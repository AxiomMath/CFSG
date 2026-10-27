module

public import CFSG.Quasithin.Vol2.Ch11SecHI
public import CFSG.Quasithin.Vol2.Ch11StatementsF

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec

variable {G : Type} [Group G]

theorem mem_normalizer_inf {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro z
  simp only [Subgroup.mem_inf]
  exact and_congr (hA z) (hB z)

theorem mem_normalizer_centralizer {W : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨conj_mem_centralizer hx, fun hz => ?_⟩
  have := conj_mem_centralizer (Subgroup.inv_mem _ hx) hz
  simpa [mul_assoc] using this

theorem comm_of_conj {V : Subgroup G} (hV : IsElemAbelian 2 V) {h a b : G}
    (ha : a ∈ conjSubgroup V h) (hb : b ∈ conjSubgroup V h) : a * b = b * a := by
  have h1 := comm_of_isElemAbelian hV (mem_conjSubgroup_iff.mp ha) (mem_conjSubgroup_iff.mp hb)
  have : h * (a * b) * h⁻¹ = h * (b * a) * h⁻¹ := by
    calc h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
      _ = (h * b * h⁻¹) * (h * a * h⁻¹) := h1
      _ = h * (b * a) * h⁻¹ := by group
  simpa using this

theorem exists_mem_centralizer [Finite G] {T U : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T)
    (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    ∃ z ∈ U, z ≠ 1 ∧ z ∈ Subgroup.centralizer (T : Set G) := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy.1, fun h1 => hy1 (Subtype.ext (Subtype.ext h1)),
    ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)

theorem mem_normalizer_of_conj_le [Finite G] {S : Subgroup G} {x : G}
    (h : ∀ s ∈ S, x * s * x⁻¹ ∈ S) : x ∈ Subgroup.normalizer (S : Set G) := by
  have hle : S.map (MulAut.conj x).toMonoidHom ≤ S := by
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs
  have heq : S.map (MulAut.conj x).toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge
  have : conjSubgroup S x⁻¹ = S := by
    rw [conjSubgroup, inv_inv]
    exact heq
  exact inv_inv x ▸ Subgroup.inv_mem _ (conjSubgroup_eq_iff_mem_normalizer.mp this)

variable [Finite G]

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem fsuV_inf_centralizer_K :
    fsuV T I ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ := by
  by_contra hne
  have hUT : fsuV T I ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ≤ T :=
    inf_le_left.trans d.c.V_le_T
  have hUn : T ≤ Subgroup.normalizer ((fsuV T I ⊓ Subgroup.centralizer (oTwoUpper H : Set G) :
      Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf (SecA.T_le_normalizer_fsuV T I ht)
      (mem_normalizer_centralizer (le_normalizer_oTwoUpper H (d.c.s.T_le ht)))
  obtain ⟨z, hz, hz1, hzT⟩ := exists_mem_centralizer d.c.s.hyp.fsu.sylow.1 hUT hUn hne
  have hzZ : z ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨hUT hz, hzT⟩, (SecA.isElemAbelian_fsuV d.c.s.hyp).2 z hz.1⟩
  have : z ∈ VZ T H ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := ⟨SecC.Z_le_VZ T H hzZ, hz.2⟩
  rw [d.VHK, Subgroup.mem_bot] at this
  exact hz1 this

theorem Vh_inf_centralizer_K :
    conjSubgroup (fsuV T I) h ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : h * x * h⁻¹ ∈ fsuV T I ⊓ Subgroup.centralizer (oTwoUpper H : Set G) :=
    ⟨mem_conjSubgroup_iff.mp hx.1, conj_mem_centralizer (le_normalizer_oTwoUpper H d.c.hH) hx.2⟩
  rw [d.fsuV_inf_centralizer_K, Subgroup.mem_bot] at h1
  have : x = h⁻¹ * (h * x * h⁻¹) * h := by group
  rw [Subgroup.mem_bot, this, h1]
  group

theorem mem_centralizer_K (i : Inp32) {z : G} (hzV : z ∈ Subgroup.centralizer (fsuV T I : Set G))
    (hzVh : z ∈ Subgroup.centralizer (conjSubgroup (fsuV T I) h : Set G)) :
    z ∈ Subgroup.centralizer (oTwoUpper H : Set G) := by
  have hI : fsuV T I ⊔ conjSubgroup (fsuV T I) h ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le (fun v hv => ?_) (fun v hv => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.mp hw]
      exact (Subgroup.mem_centralizer_iff.mp hzV v hv).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.mp hw]
      exact (Subgroup.mem_centralizer_iff.mp hzVh v hv).symm
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.mem_centralizer_iff.mp (hI (d.K_le_I i hk)) z rfl).symm

theorem fsuV_inf_Vh (i : Inp32) : fsuV T I ⊓ conjSubgroup (fsuV T I) h = ⊥ := by
  have hVab := SecA.isElemAbelian_fsuV d.c.s.hyp
  rw [eq_bot_iff, ← d.fsuV_inf_centralizer_K]
  intro z hz
  refine ⟨hz.1, d.mem_centralizer_K i ?_ ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact comm_of_isElemAbelian hVab hv hz.1
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact comm_of_conj hVab hv hz.2

theorem bOf_eq (i : Inp32) : bOf T I H = fsuV T I ⊓ pCoreOf 2 H :=
  (d.c.fsuV_inf_pCoreOf i.h1135 i.h1136).symm

theorem Bh_eq (i : Inp32) :
    conjSubgroup (bOf T I H) h = conjSubgroup (fsuV T I) h ⊓ pCoreOf 2 H := by
  have hO : conjSubgroup (pCoreOf 2 H) h = pCoreOf 2 H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H d.c.hH)
  rw [d.bOf_eq i]
  calc conjSubgroup (fsuV T I ⊓ pCoreOf 2 H) h =
      conjSubgroup (fsuV T I) h ⊓ conjSubgroup (pCoreOf 2 H) h :=
        Subgroup.map_inf_eq _ _ _ (MulAut.conj h⁻¹).injective
    _ = conjSubgroup (fsuV T I) h ⊓ pCoreOf 2 H := by rw [hO]

theorem comm_B_Bh (i : Inp32) {b b' : G} (hb : b ∈ bOf T I H)
    (hb' : b' ∈ conjSubgroup (bOf T I H) h) : b * b' = b' * b := by
  rw [d.bOf_eq i] at hb
  rw [d.Bh_eq i] at hb'
  have h1 : b * b' * b⁻¹ * b'⁻¹ ∈ fsuV T I := by
    have := (Subgroup.mem_normalizer_iff.mp (d.pCoreOf_le_normalizer_V hb'.2) b⁻¹).mp
      ((fsuV T I).inv_mem hb.1)
    have h2 : b * b' * b⁻¹ * b'⁻¹ = b * (b' * b⁻¹ * b'⁻¹) := by group
    rw [h2]
    exact (fsuV T I).mul_mem hb.1 this
  have h3 : b * b' * b⁻¹ * b'⁻¹ ∈ conjSubgroup (fsuV T I) h := by
    have := (Subgroup.mem_normalizer_iff.mp (d.pCoreOf_le_normalizer_Vh hb.2) b').mp hb'.1
    exact (conjSubgroup _ h).mul_mem this ((conjSubgroup _ h).inv_mem hb'.1)
  have h4 : b * b' * b⁻¹ * b'⁻¹ ∈ fsuV T I ⊓ conjSubgroup (fsuV T I) h := ⟨h1, h3⟩
  rw [d.fsuV_inf_Vh i, Subgroup.mem_bot] at h4
  calc b * b' = (b * b' * b⁻¹ * b'⁻¹) * (b' * b) := by group
    _ = b' * b := by rw [h4, one_mul]

theorem Bh_le_normalizer_B (i : Inp32) :
    conjSubgroup (bOf T I H) h ≤ Subgroup.normalizer (bOf T I H : Set G) := fun b' hb' =>
  mem_normalizer_of_conj_le fun b hb => by
    rw [← d.comm_B_Bh i hb hb', mul_inv_cancel_right]
    exact hb

theorem mem_P_iff (i : Inp32) {x : G} : x ∈ pOf T I H h ↔
    ∃ b ∈ bOf T I H, ∃ b' ∈ conjSubgroup (bOf T I H) h, x = b * b' :=
  B19Aux.mem_sup_iff_of_le_normalizer (d.Bh_le_normalizer_B i)

theorem P_le_pCoreOf (i : Inp32) : pOf T I H h ≤ pCoreOf 2 H := by
  refine sup_le ?_ ?_
  · rw [d.bOf_eq i]
    exact inf_le_right
  · rw [d.Bh_eq i]
    exact inf_le_right

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
