module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42A0
public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.Quasithin.Vol2.GoldschmidtF431Setting

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.QuasithinUnique U42F431

@[simp] theorem A0_P1 :
    A0.P1 = P1 := rfl

@[simp] theorem A0_P2 :
    A0.P2 = P2 := rfl

theorem A0_N1 :
    A0.N1 = P1.map (MulAut.conj : Y →* MulAut Y) := by
  ext φ
  constructor
  · rintro ⟨⟨y, rfl⟩, hst⟩
    have hy : y ∈ Subgroup.normalizer (P1 : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simpa [autStab, A0_P1] using hst x
    rw [normalizer_P1] at hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, fun x => ?_⟩
    have hy' : y ∈ Subgroup.normalizer (P1 : Set Y) := Subgroup.le_normalizer hy
    simpa [A0_P1] using Subgroup.mem_normalizer_iff.1 hy' x

theorem A0_N2 :
    A0.N2 = P2.map (MulAut.conj : Y →* MulAut Y) := by
  ext φ
  constructor
  · rintro ⟨⟨y, rfl⟩, hst⟩
    have hy : y ∈ Subgroup.normalizer (P2 : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simpa [autStab, A0_P2] using hst x
    rw [normalizer_P2] at hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, fun x => ?_⟩
    have hy' : y ∈ Subgroup.normalizer (P2 : Set Y) := Subgroup.le_normalizer hy
    simpa [A0_P2] using Subgroup.mem_normalizer_iff.1 hy' x

theorem A0_K :
    A0.K = (MulAut.conj : Y →* MulAut Y).range := by
  rw [MonoidHom.range_eq_map, ← P1_sup_P2, Subgroup.map_sup, ← A0_N1, ← A0_N2]
  rfl

@[expose] noncomputable def u42Setting :
    LieSetting.{0, 0} :=
  A0.setting inferInstance (polyNumber .PSU) (three_le_polyNumber .PSU)

@[expose] def Gv
    (g : u42Setting.ι.G0) : MulAut Y := g.1.1

theorem Gv_injective :
    Function.Injective (Gv : u42Setting.ι.G0 → MulAut Y) := fun _ _ h =>
  Subtype.ext (Subtype.ext h)

theorem Gv_mem_inn
    (g : u42Setting.ι.G0) : Gv g ∈ (MulAut.conj : Y →* MulAut Y).range := by
  rw [← A0_K]
  exact g.1.2

@[expose] noncomputable def toG0 :
    Y →* u42Setting.ι.G0 :=
  ((MulAut.conj : Y →* MulAut Y).codRestrict A0.K (fun y => by
      rw [A0_K]
      exact ⟨y, rfl⟩)).codRestrict (A0.ι0.φ1.range ⊔ A0.ι0.φ2.range) (fun y => by
      rw [A0.ι0.gen]
      exact Subgroup.mem_top _)

theorem Gv_toG0 (y : Y) :
    Gv (toG0 y) = MulAut.conj y := rfl

theorem toG0_injective :
    Function.Injective (toG0 : Y →* u42Setting.ι.G0) := by
  intro a b h
  have h1 : (MulAut.conj a : MulAut Y) = MulAut.conj b := congrArg Gv h
  have hc : b⁻¹ * a ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 : (MulAut.conj (b⁻¹ * a) : MulAut Y) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := congrArg (fun φ : MulAut Y => φ y) h2
    simp only [MulAut.conj_apply, MulAut.one_apply] at h3
    calc y * (b⁻¹ * a) = (b⁻¹ * a * y * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by rw [h3]
      _ = (b⁻¹ * a) * y := by group
  rw [center_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem toG0_surjective :
    Function.Surjective (toG0 : Y →* u42Setting.ι.G0) := by
  intro g
  obtain ⟨y, hy⟩ := Gv_mem_inn g
  exact ⟨y, Gv_injective (by rw [Gv_toG0]; exact hy)⟩

@[expose] noncomputable def eG :
    Y ≃* u42Setting.ι.G0 :=
  MulEquiv.ofBijective toG0 ⟨toG0_injective, toG0_surjective⟩

theorem N_eq_top :
    u42Setting.N = ⊤ := by
  rw [eq_top_iff]
  intro g _
  exact Gv_mem_inn g

theorem mem_Mb1_iff
    (g : u42Setting.ι.G0) : g ∈ u42Setting.Mb1 ↔ Gv g ∈ A0.N1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨Gv g, h⟩, rfl⟩

theorem mem_Mb2_iff
    (g : u42Setting.ι.G0) : g ∈ u42Setting.Mb2 ↔ Gv g ∈ A0.N2 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨Gv g, h⟩, rfl⟩

theorem Mb1_eq :
    u42Setting.Mb1 = P1.map eG.toMonoidHom := by
  ext g
  rw [mem_Mb1_iff, A0_N1, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyg⟩
    exact ⟨y, hy, Gv_injective hyg⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem Mb2_eq :
    u42Setting.Mb2 = P2.map eG.toMonoidHom := by
  ext g
  rw [mem_Mb2_iff, A0_N2, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyg⟩
    exact ⟨y, hy, Gv_injective hyg⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

end CFSG.Quasithin.H13.F431.U42
