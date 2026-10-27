module

public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofTools
import CFSG.RankThree.PartTwo.Sec18.Item18ResProofAlt1C

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement Pointwise

namespace SylowInner

variable {G : Type} [Group G] [Finite G]

open Item18ResProof in
theorem false_of_alt2_of_centralizer_le {X K J L : Subgroup G} (hLX : L ≤ X) (hLp : ⁅L, L⁆ = L)
    (hK : K ∈ oTwoComponentsIn X) (hJ : J ∈ oTwoComponentsIn X)
    (eL : L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) (hLXeq : ⁅L, X⁆ = K ⊔ J)
    (eK : K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    {c : G} (hcX : c ∈ X) (hcN : c ∈ Subgroup.normalizer (L : Set G)) (hc3 : c ^ 3 = 1)
    (hcL : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L)
    (hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKX : K ≤ X := le_of_mem_oTwoComponentsIn hK
  have hJX : J ≤ X := le_of_mem_oTwoComponentsIn hJ
  set QX := CFSG.Open.pCoreOf 2 X with hQX
  set QK := CFSG.Open.pCoreOf 2 K with hQK
  set QL := CFSG.Open.pCoreOf 2 L with hQL
  have hXQX : X ≤ Subgroup.normalizer (QX : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hQKX : QK ≤ QX := pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK
  have hKQK : K ≤ Subgroup.normalizer (QK : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hKp : ⁅K, K⁆ = K := commutator_eq_of_mem_oTwoComponentsIn hK
  have hLKJ : L ≤ K ⊔ J := by
    rw [← hLXeq]
    calc L = ⁅L, L⁆ := hLp.symm
      _ ≤ ⁅L, X⁆ := Subgroup.commutator_mono le_rfl hLX
  have hKJne : K ≠ J := by
    rintro rfl
    rw [sup_idem] at hLKJ
    exact false_of_le_sup_pCoreOf hK eK eL (hLKJ.trans le_sup_left)
  have hJK : J ≤ Subgroup.normalizer (K : Set G) := fun j hj =>
    mem_normalizer_of_commutator_mem hK (hJX hj) fun k hk =>
      Sec19.Step1910Proof.commutator_mem_pCoreOf hJ hK (Ne.symm hKJne) hj hk
  have hKJ : K ≤ Subgroup.normalizer (J : Set G) := fun k hk =>
    mem_normalizer_of_commutator_mem hJ (hKX hk) fun j hj =>
      Sec19.Step1910Proof.commutator_mem_pCoreOf hK hJ hKJne hk hj
  have hQXK : QX ⊓ K ≤ QK := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hXQX (hKX hx), Subgroup.le_normalizer hx⟩)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_left)
  have hJKc : ∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ * k⁻¹ ∈ QK := fun j hj k hk =>
    hQXK ⟨Sec19.Step1910Proof.commutator_mem_pCoreOf hJ hK (Ne.symm hKJne) hj hk,
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hJK hj) k).mp hk) (K.inv_mem hk)⟩
  have hcKJ : (K ⊔ J).map (MulAut.conj c).toMonoidHom = K ⊔ J := by
    rw [← hLXeq, Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer hcN,
      Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hcX)]
  have hcomp : ∀ S ∈ oTwoComponentsIn X, S ≤ K ⊔ J → S = K ∨ S = J := by
    intro S hS hSKJ
    by_contra hne
    push Not at hne
    refine false_of_le_iSup_sup_pCoreOf hS {K, J} ?_ ?_ ?_
    · rintro T (rfl | rfl)
      · exact hK
      · exact hJ
    · rintro (h1 | h1)
      · exact hne.1 h1
      · exact hne.2 h1
    · refine hSKJ.trans (le_sup_of_le_left ?_)
      exact sup_le (le_iSup₂_of_le K (Set.mem_insert _ _) le_rfl)
        (le_iSup₂_of_le J (by simp) le_rfl)
  have hKc := hcomp _ (map_conj_mem_oTwoComponentsIn hK hcX)
    (by rw [← hcKJ]; exact Subgroup.map_mono le_sup_left)
  have hJc := hcomp _ (map_conj_mem_oTwoComponentsIn hJ hcX)
    (by rw [← hcKJ]; exact Subgroup.map_mono le_sup_right)
  have hcK : c ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (map_conj_eq_of_pow_three hKJne hc3 hKc hJc)
  have hcJ : c ∈ Subgroup.normalizer (J : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (map_conj_eq_of_pow_three (Ne.symm hKJne) hc3 hJc.symm hKc.symm)
  have hLJ : ¬ L ≤ J ⊔ QK := by
    intro hLJ'
    have hLJX : L ≤ J ⊔ QX := hLJ'.trans (sup_le_sup_left hQKX J)
    set 𝓢 : Set (Subgroup G) := {S | ∃ x ∈ X, S = J.map (MulAut.conj x).toMonoidHom} with h𝓢
    have h𝓢mem : ∀ S ∈ 𝓢, S ∈ oTwoComponentsIn X := by
      rintro S ⟨x, hx, rfl⟩
      exact map_conj_mem_oTwoComponentsIn hJ hx
    have hJ𝓢 : ∀ x ∈ X, J.map (MulAut.conj x).toMonoidHom ≤ ⨆ S ∈ 𝓢, S := fun x hx =>
      le_iSup₂_of_le (J.map (MulAut.conj x).toMonoidHom) ⟨x, hx, rfl⟩ le_rfl
    have hJ1 : J ≤ ⨆ S ∈ 𝓢, S :=
      le_iSup₂_of_le J
        ⟨1, X.one_mem, (Late.map_conj_eq_of_mem_normalizer (Subgroup.one_mem _)).symm⟩ le_rfl
    have hKle : K ≤ (⨆ S ∈ 𝓢, S) ⊔ QX := by
      have h1 : ⁅L, X⁆ ≤ (⨆ S ∈ 𝓢, S) ⊔ QX := by
        rw [Subgroup.commutator_le]
        intro l hl x hx
        have hl' : l ∈ ((J : Set G) * (QX : Set G)) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right J QX (hJX.trans hXQX)]
          exact hLJX hl
        obtain ⟨j, hj, q, hq, rfl⟩ := hl'
        have hjX : j ∈ X := hJX hj
        have hq1 : q * x * q⁻¹ * x⁻¹ ∈ QX := by
          have e : q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) := by group
          rw [e]
          exact QX.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hXQX hx) _).mp (QX.inv_mem hq))
        have hq2 : j * (q * x * q⁻¹ * x⁻¹) * j⁻¹ ∈ QX :=
          (Subgroup.mem_normalizer_iff.mp (hXQX hjX) _).mp hq1
        have hj2 : x * j⁻¹ * x⁻¹ ∈ J.map (MulAut.conj x).toMonoidHom :=
          ⟨j⁻¹, J.inv_mem hj, by simp [MulAut.conj_apply]⟩
        have e : ⁅j * q, x⁆ = (j * (q * x * q⁻¹ * x⁻¹) * j⁻¹) * (j * (x * j⁻¹ * x⁻¹)) := by
          rw [commutatorElement_def]
          group
        rw [e]
        refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hq2) (Subgroup.mul_mem _ ?_ ?_)
        · exact Subgroup.mem_sup_left (hJ1 hj)
        · exact Subgroup.mem_sup_left (hJ𝓢 x hx hj2)
      exact (le_sup_left.trans hLXeq.symm.le).trans h1
    by_cases hK𝓢 : K ∈ 𝓢
    · obtain ⟨x, hx, hKx⟩ := hK𝓢
      have hLx : L.map (MulAut.conj x).toMonoidHom ≤ K ⊔ QX := by
        have h1 := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hLJX
        rwa [Subgroup.map_sup, ← hKx, Late.map_conj_eq_of_mem_normalizer (hXQX hx)] at h1
      obtain ⟨eLx⟩ := nonempty_quotient_map_conj x eL
      exact false_of_le_sup_pCoreOf hK eK eLx hLx
    · exact false_of_le_iSup_sup_pCoreOf hK 𝓢 h𝓢mem hK𝓢 hKle
  have hcc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ QK :=
    commutator_mem_pCoreOf_of_diag hJK hKJ hJKc hKp hLKJ hLp eK eL hLJ hcK hcJ hcL
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hKK₁ : K ≤ K ⊓ C ⊔ QK :=
    (le_perfectResidual_inf_centralizer_sup hKp hcK hc3 hcc).trans
      (sup_le_sup_right (Subgroup.map_subtype_le _) _)
  have hLK : L ≤ Subgroup.normalizer (K : Set G) :=
    hLKJ.trans (sup_le Subgroup.le_normalizer hJK)
  set D := K ⊓ L with hD
  have hLD : L ≤ Subgroup.normalizer (D : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hLK hl, Subgroup.le_normalizer hl⟩
  have hxl : ∀ x ∈ K ⊓ C, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ D := by
    intro x hx l hl
    refine ⟨?_, L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCL hx.2) l).mp hl) (L.inv_mem hl)⟩
    have h1 : l * x⁻¹ * l⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hLK hl) _).mp (K.inv_mem hx.1)
    have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
    rw [e]
    exact K.mul_mem hx.1 h1
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) := isSimpleGroup_projSL_three_four
  have hsimple : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := eL.isSimpleGroup
  set π : L →* L ⧸ CFSG.pCore 2 L := QuotientGroup.mk' (CFSG.pCore 2 L) with hπ
  haveI hDn : (D.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hLD
  haveI hDq : ((D.subgroupOf L).map π).Normal := hDn.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((D.subgroupOf L).map π) with hbot | htop
  ·
    have hDQ : ∀ d ∈ D, d ∈ QL := by
      intro d hd
      have h1 : π ⟨d, hd.2⟩ ∈ (D.subgroupOf L).map π := ⟨⟨d, hd.2⟩, hd, rfl⟩
      rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        mem_pCore_iff_mem_pCoreOf] at h1
      exact h1
    have hK₁ : ∀ x ∈ K ⊓ C, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ QK := fun x hx =>
      commutator_mem_pCoreOf_of_diag hJK hKJ hJKc hKp hLKJ hLp eK eL hLJ
        (Subgroup.le_normalizer hx.1) (hKJ hx.1) fun l hl => hDQ _ (hxl x hx l hl)
    have hS : ∀ t ∈ ((K ⊓ C : Subgroup G) : Set G) ∪ (QK : Set G),
        t ∈ Subgroup.normalizer (K : Set G) ∧ ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ QK := by
      rintro t (ht | ht)
      · exact ⟨Subgroup.le_normalizer ht.1, hK₁ t ht⟩
      · refine ⟨Subgroup.le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 K ht),
          fun k hk => ?_⟩
        have e : t * k * t⁻¹ * k⁻¹ = t * (k * t⁻¹ * k⁻¹) := by group
        rw [e]
        exact QK.mul_mem ht ((Subgroup.mem_normalizer_iff.mp (hKQK hk) _).mp (QK.inv_mem ht))
    have hcomm : ⁅K, K⁆ ≤ QK := by
      rw [Subgroup.commutator_le]
      intro k hk k' hk'
      have hk1 : k ∈ Subgroup.closure (((K ⊓ C : Subgroup G) : Set G) ∪ (QK : Set G)) := by
        rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
        exact hKK₁ hk
      rw [commutatorElement_def]
      exact (commutator_mem_pCoreOf_of_mem_closure hS hk1).2 k' hk'
    refine false_of_le_iSup_sup_pCoreOf hK ∅ (fun S hS => hS.elim) (Set.notMem_empty K) ?_
    rw [← hKp]
    refine hcomm.trans (hQKX.trans ?_)
    simp [hQX]
  ·
    have hLDQ : D ⊔ QL = L := by
      refine le_antisymm (sup_le inf_le_right (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
        fun l hl => ?_
      have h1 : π ⟨l, hl⟩ ∈ (D.subgroupOf L).map π := htop ▸ Subgroup.mem_top _
      obtain ⟨d, hd, hdl⟩ := h1
      have h2 : (d : G)⁻¹ * l ∈ QL := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
          mem_pCore_iff_mem_pCoreOf] at hdl
        simpa using hdl
      have e : l = (d : G) * ((d : G)⁻¹ * l) := by group
      rw [e]
      exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hd) h2
    have hQs : Group.IsSolvable QL := by
      have : Group.IsNilpotent QL := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).isNilpotent
      infer_instance
    have hs := isSolvable_quotient_of_sup_eq (U := D) (V := QL) (Y := L) inf_le_right
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hLD hLDQ hQs
    have hLle : L ≤ D :=
      (le_inSubgroup_perfectResidual hLp le_rfl).trans
        (inSubgroup_perfectResidual_le_of_isSolvable inf_le_right hs)
    exact false_of_le_sup_pCoreOf hK eK eL ((hLle.trans inf_le_left).trans le_sup_left)

end SylowInner

end CFSG.RankThree.PartTwo.Sec18
