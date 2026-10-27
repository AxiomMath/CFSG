module

public import CFSG.Quasithin.Background.B1MoreIrr
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

section Generic

variable {Y : Type} [CommGroup Y]

theorem v3qb_fixed_of_comm_le {Z : Subgroup Y} {Λ : Subgroup (MulAut Y)} [Group.IsPerfect ↥Λ]
    (hZ : Z ≤ fixV Λ) {v : Y} (hv : ∀ l ∈ Λ, l v * v⁻¹ ∈ Z) : v ∈ fixV Λ := by
  let f : ↥Λ →* Y := MonoidHom.mk' (fun l => (l : MulAut Y) v * v⁻¹) (by
    intro a b
    have hb : (a : MulAut Y) ((b : MulAut Y) v * v⁻¹) = (b : MulAut Y) v * v⁻¹ :=
      hZ (hv b b.2) a a.2
    rw [map_mul, map_inv] at hb
    have e : (a : MulAut Y) ((b : MulAut Y) v) =
        ((b : MulAut Y) v * v⁻¹) * (a : MulAut Y) v := by
      rw [← hb]
      simp
    show (a : MulAut Y) ((b : MulAut Y) v) * v⁻¹ =
      ((a : MulAut Y) v * v⁻¹) * ((b : MulAut Y) v * v⁻¹)
    rw [e]
    simp [mul_comm, mul_left_comm])
  have hker : (⊤ : Subgroup ↥Λ) ≤ f.ker := by
    rw [← Group.IsPerfect.commutator_eq_top]
    show ⁅(⊤ : Subgroup ↥Λ), (⊤ : Subgroup ↥Λ)⁆ ≤ f.ker
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  intro l hl
  have h := hker (Subgroup.mem_top (⟨l, hl⟩ : ↥Λ))
  rw [MonoidHom.mem_ker] at h
  exact mul_inv_eq_one.mp h

theorem v3qb_irrPlus_map {Z V : Subgroup Y} {Λ : Subgroup (MulAut Y)} (hZ : Z ≤ fixV Λ)
    (hΛZ : Λ ≤ stabSub Z) (hV : V ∈ IrrPlus Λ (⊤ : Subgroup Y)) :
    V.map (QuotientGroup.mk' Z) ∈ IrrPlus (autQuot Λ Z) (⊤ : Subgroup (Y ⧸ Z)) := by
  rw [mem_irrPlus_top_iff] at hV ⊢
  obtain ⟨hinv, hcomm, hlt, hirr⟩ := hV
  have hinv' : ∀ x ∈ autQuot Λ Z, ∀ w ∈ V.map (QuotientGroup.mk' Z), x w ∈
      V.map (QuotientGroup.mk' Z) := by
    intro x hx w hw
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hx
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨(g : MulAut Y) v, hinv _ hg v hv, rfl⟩
  have hfix : ∀ v ∈ V ⊓ fixV Λ, QuotientGroup.mk' Z v ∈ fixV (autQuot Λ Z) := by
    intro v hv x hx
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hx
    show QuotientGroup.mk' Z ((g : MulAut Y) v) = QuotientGroup.mk' Z v
    rw [hv.2 (g : MulAut Y) hg]
  have hVZ : (∀ l ∈ Λ, ∀ w ∈ V, l w * w⁻¹ ∈ Z) → V ≤ Z := by
    intro hall
    calc V = commSub V Λ := hcomm.symm
      _ ≤ Z := by
        rw [commSub, Subgroup.closure_le]
        rintro _ ⟨l, hl, w, hw, rfl⟩
        exact hall l hl w hw
  refine ⟨hinv', ?_, ?_, ?_⟩
  · refine le_antisymm (commSub_le_of_invariant hinv') ?_
    refine Subgroup.map_le_iff_le_comap.mpr ?_
    calc V = commSub V Λ := hcomm.symm
      _ ≤ _ := by
        rw [commSub, Subgroup.closure_le]
        rintro _ ⟨l, hl, w, hw, rfl⟩
        refine Subgroup.mem_comap.mpr ?_
        rw [map_mul, map_inv]
        exact Subgroup.subset_closure ⟨quotHom Z ⟨l, hΛZ hl⟩, mem_autQuot.mpr ⟨_, hl, rfl⟩,
          QuotientGroup.mk' Z w, ⟨w, hw, rfl⟩, rfl⟩
  · refine lt_of_le_of_ne inf_le_left fun h => ?_
    have hle : V.map (QuotientGroup.mk' Z) ≤ fixV (autQuot Λ Z) := by
      rw [← h]
      exact inf_le_right
    have hVZ' : V ≤ Z := by
      refine hVZ fun l hl w hw => ?_
      have h2 := hle ⟨w, hw, rfl⟩ (quotHom Z ⟨l, hΛZ hl⟩) (mem_autQuot.mpr ⟨_, hl, rfl⟩)
      exact (mk_eq_mk_iff _ _).mp h2
    exact absurd (inf_eq_left.mpr (hVZ'.trans hZ)) (ne_of_lt hlt)
  · intro J hJinv hJ1 hJ2
    set J' : Subgroup Y := V ⊓ J.comap (QuotientGroup.mk' Z) with hJ'
    have hJ'inv : ∀ x ∈ Λ, ∀ w ∈ J', x w ∈ J' := by
      intro x hx w hw
      refine ⟨hinv x hx w hw.1, ?_⟩
      exact hJinv (quotHom Z ⟨x, hΛZ hx⟩) (mem_autQuot.mpr ⟨_, hx, rfl⟩)
        (QuotientGroup.mk' Z w) hw.2
    have hJ'1 : V ⊓ fixV Λ ≤ J' := fun v hv =>
      ⟨hv.1, hJ1 ⟨⟨v, hv.1, rfl⟩, hfix v hv⟩⟩
    rcases hirr J' hJ'inv hJ'1 inf_le_left with h | h
    · left
      refine le_antisymm (fun j hj => ?_) hJ1
      obtain ⟨v, hv, rfl⟩ := hJ2 hj
      have hvJ' : v ∈ J' := ⟨hv, hj⟩
      rw [h] at hvJ'
      exact ⟨⟨v, hv, rfl⟩, hfix v hvJ'⟩
    · right
      refine le_antisymm hJ2 ?_
      rintro _ ⟨v, hv, rfl⟩
      have hvJ' : v ∈ J' := by rw [h]; exact hv
      exact hvJ'.2

end Generic

end CFSG.Quasithin
