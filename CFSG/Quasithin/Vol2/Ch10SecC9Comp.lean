module

public import CFSG.Quasithin.Vol2.Ch10SecC8Main4c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem pCoreOf_centralizer_ne_bot {v : G} (hv1 : v ≠ 1) (hv2 : v ^ 2 = 1) :
    pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvC : v ∈ Subgroup.centralizer ({v} : Set G) := mem_centralizer_of_mul_conj_eq (by group)
  have hC : Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hP : IsPGroup 2 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hv2 hv1, pow_one])
  have hle : Subgroup.zpowers v ≤ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) (Subgroup.zpowers_le.mpr hvC) hC
      hP
  intro h
  rw [h] at hle
  exact hv1 ((Subgroup.mem_bot).mp (hle (Subgroup.mem_zpowers v)))

theorem isSubnormal_L_fsuM (hyp : Hyp10 G T L I) : IsSubnormal L (fsuM T L) :=
  IsSubnormal.step (SecA.le_fsuL0 T L) (SecA.normal_fsuL0 hyp.fsu.maximal.1)
    (IsSubnormal.step Subgroup.le_normalizer Subgroup.normal_in_normalizer (IsSubnormal.refl _))

theorem exists_cComp_gt (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (hyp : Hyp10 G T L I)
    (h1011 : Stmt10_1_1) (h1026 : Stmt10_2_6) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {v : G}
    (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hv1 : v ≠ 1)
    (hTv : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G))
      (Subgroup.centralizer ({v} : Set G)))
    (hTvL : T ⊓ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hHM : ¬ Subgroup.centralizer ({v} : Set G) ≤ fsuM T L) :
    ∃ J ∈ cComp (Subgroup.centralizer ({v} : Set G)), L ≤ J ∧ L ≠ J ∧
      (J.subgroupOf (Subgroup.centralizer ({v} : Set G))).Normal ∧ ¬ J ≤ fsuM T L := by
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, -, hV2, -⟩ := hdec t ht htn
  have hvV : v ∈ fsuVM T L I := commutator_le_left_of_le_normalizer
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) hv
  have hH := pCoreOf_centralizer_ne_bot hv1 ((SecA.isElemAbelian_fsuVM hyp).2 v hvV)
  have hLH : L ≤ Subgroup.centralizer ({v} : Set G) := fun l hl =>
    mem_centralizer_of_mul_conj_eq (by
      rw [Subgroup.mem_centralizer_iff.mp (hV2 hv) l hl, mul_inv_cancel_right])
  have hLloc : L ∈ lFamily (T ⊓ Subgroup.centralizer ({v} : Set G)) :=
    cComp_mem_of_le hyp.fsu.maximal.1.2.1 le_sup_left (sup_le_sup_left inf_le_left _)
  obtain ⟨J, hJ, hLJ⟩ := QuasithinUnique.Vol2Native.lemma_1_2_4_exists hK h37 h39 hH hTv hLH hLloc
  have hJn := QuasithinUnique.Vol2Native.lemma_1_2_4_normal hK h37 h38 hH hTv hLloc hLJ hJ hTvL
  have hLJne : L ≠ J := by
    rintro rfl
    apply hHM
    refine le_trans (fun h hh => ?_) (h1026 G T L I hyp).2.2
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := hJn.conj_mem ⟨x, hLH hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨h, hh⟩
      exact Subgroup.mem_subgroupOf.mp this
    · intro hx
      have hx' : h * x * h⁻¹ ∈ Subgroup.centralizer ({v} : Set G) := hLH hx
      have hxH : x ∈ Subgroup.centralizer ({v} : Set G) := by
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hx') hh
        have e : h⁻¹ * (h * x * h⁻¹) * h = x := by group
        rwa [e] at this
      have := hJn.conj_mem ⟨h * x * h⁻¹, hx'⟩ (Subgroup.mem_subgroupOf.mpr hx)
        ⟨h⁻¹, Subgroup.inv_mem _ hh⟩
      have h2 := Subgroup.mem_subgroupOf.mp this
      have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
      change h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ ∈ L at h2
      rwa [e] at h2
  refine ⟨J, hJ, hLJ, hLJne, hJn, fun hJM => ?_⟩
  have hLJs : IsSubnormal L J := A3.subnormal_of_le_of_le (isSubnormal_L_fsuM hyp) hLJ hJM
  have hJs : IsSubnormal J (Subgroup.centralizer ({v} : Set G)) :=
    IsSubnormal.step (le_of_mem_cComp hJ) hJn (IsSubnormal.refl _)
  exact not_subnormal_of_mem_cComp hJ (lt_of_le_of_ne hLJ hLJne) hyp.fsu.maximal.1.2.1.1
    hyp.fsu.maximal.1.2.1.2.1 (A3.subnormal_trans hLJs hJs)

end CFSG.Quasithin.Vol2.Ch10.SecC
