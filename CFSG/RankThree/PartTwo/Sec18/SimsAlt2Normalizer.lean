module

public import CFSG.RankThree.PartTwo.Sec18.SimsItem186HStatement
import CFSG.RankThree.PartTwo.Sec18.Item18ResProofAlt1C

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

open Item18ResProof in
theorem false_of_alt2_of_centralizer_le_normalizer {A M : Subgroup G} (h : Sec18Std G A M)
    {H : Subgroup G} (hHs : H ∈ scriptHStar A M) {X : Subgroup G} (hHX : H ≤ X)
    {K J : Subgroup G} (hK : K ∈ oTwoComponentsIn X) (hJ : J ∈ oTwoComponentsIn X)
    (eL : inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
      projSL 3 (GaloisField 2 2))
    (hLXeq : ⁅inSubgroup perfectResidual H, X⁆ = K ⊔ J)
    (eK : K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    {c : G} (hcA : c ∈ A)
    (hcL : c ∈ sectionCentralizer A (inSubgroup perfectResidual H)
      (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H)))
    (hCN : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (inSubgroup perfectResidual H : Set G)) : False := by
  have hH : H ∈ scriptH A M := hHs.prop
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := inSubgroup perfectResidual H with hLdef
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH : A ≤ H := le_of_mem_scriptH₀ hH₀
  have hAX : A ≤ X := hAH.trans hHX
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hLX : L ≤ X := hLH.trans hHX
  have hLp : ⁅L, L⁆ = L := commutator_inSubgroup_perfectResidual H
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_inSubgroup_perfectResidual H
  have hKX : K ≤ X := le_of_mem_oTwoComponentsIn hK
  have hJX : J ≤ X := le_of_mem_oTwoComponentsIn hJ
  set QX := CFSG.Open.pCoreOf 2 X with hQX
  set QK := CFSG.Open.pCoreOf 2 K with hQK
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
  have hAKJ : ∀ a ∈ A, (K ⊔ J).map (MulAut.conj a).toMonoidHom = K ⊔ J := by
    intro a ha
    rw [← hLXeq, Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer (hHL (hAH ha)),
      Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (hAX ha))]
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
  have hAnorm : ∀ a ∈ A, a ∈ Subgroup.normalizer (K : Set G) ∧
      a ∈ Subgroup.normalizer (J : Set G) := by
    intro a ha
    have hKa := hcomp _ (map_conj_mem_oTwoComponentsIn hK (hAX ha))
      (by rw [← hAKJ a ha]; exact Subgroup.map_mono le_sup_left)
    have hJa := hcomp _ (map_conj_mem_oTwoComponentsIn hJ (hAX ha))
      (by rw [← hAKJ a ha]; exact Subgroup.map_mono le_sup_right)
    have ha3 : a ^ 3 = 1 := hA.1.2 a ha
    exact ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_eq_of_pow_three hKJne ha3 hKa hJa),
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_eq_of_pow_three (Ne.symm hKJne) ha3 hJa.symm hKa.symm)⟩
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
  have hcK : c ∈ Subgroup.normalizer (K : Set G) := (hAnorm c hcA).1
  have hcJ : c ∈ Subgroup.normalizer (J : Set G) := (hAnorm c hcA).2
  have hcLc : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L := hcL.2
  have hcc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ QK :=
    commutator_mem_pCoreOf_of_diag hJK hKJ hJKc hKp hLKJ hLp eK eL hLJ hcK hcJ hcLc
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  have hKle := le_perfectResidual_inf_centralizer_sup hKp hcK hc3 hcc
  have hQXH : QX ≤ CFSG.Open.pCoreOf 2 H :=
    le_pCoreOf_of_mem_scriptHStar h hHs (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
      (hHX.trans hXQX)
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := by
    refine hKle.trans (sup_le ?_ ?_)
    · exact (Subgroup.map_subtype_le _).trans (inf_le_right.trans hCN)
    · exact hQKX.trans (hQXH.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHL))
  have hLNK : L ≤ Subgroup.normalizer (K : Set G) := hLKJ.trans (sup_le Subgroup.le_normalizer hJK)
  have hcomm : ∀ k ∈ K, ∀ l ∈ L, k * l * k⁻¹ * l⁻¹ ∈ K ⊓ L := by
    intro k hk l hl
    refine ⟨?_, L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN hk) l).mp hl) (L.inv_mem hl)⟩
    have e : k * l * k⁻¹ * l⁻¹ = k * (l * k⁻¹ * l⁻¹) := by group
    rw [e]
    exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp (hLNK hl) _).mp (K.inv_mem hk))
  have : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) :=
    haveI := isSimpleGroup_projSL_three_four
    eL.isSimpleGroup
  set πL : L →* L ⧸ CFSG.pCore 2 L := QuotientGroup.mk' (CFSG.pCore 2 L) with hπL
  have hπL1 : ∀ x : L, πL x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 L := fun x => by
    rw [hπL, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
  set M' : Subgroup L := (K ⊓ L).subgroupOf L with hM'
  have hLKL : L ≤ Subgroup.normalizer ((K ⊓ L : Subgroup G) : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hLNK hl, Subgroup.le_normalizer hl⟩
  have hM'n : M'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hLKL
  have hM'map : (M'.map πL).Normal := hM'n.map πL (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M'.map πL) with hbot | htop
  ·
    have hKLO : K ⊓ L ≤ CFSG.Open.pCoreOf 2 L := by
      intro x hx
      have h1 : πL ⟨x, hx.2⟩ ∈ M'.map πL := ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact (hπL1 _).mp h1
    have hab : ∀ k ∈ K, ∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ QK := fun k hk =>
      commutator_mem_pCoreOf_of_diag hJK hKJ hJKc hKp hLKJ hLp eK eL hLJ
        (Subgroup.le_normalizer hk) (hKJ hk) fun l hl => hKLO (hcomm k hk l hl)
    have hKQ : K ≤ QK := by
      rw [← hKp, Subgroup.commutator_le]
      intro k hk k' hk'
      rw [commutatorElement_def]
      exact hab k hk k' hk'
    have hKcard : Nat.card K = 60480 * Nat.card QK := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 K),
        Nat.card_congr eK.toEquiv, KFacts.KS14.card_SL_three_four, card_pCoreOf_eq]
    have hQKeq : QK = K := le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hKQ
    have hpos : 0 < Nat.card K := Nat.card_pos
    rw [hQKeq] at hKcard
    omega
  ·
    have hq2 : IsPGroup 2 (L ⧸ M') := by
      intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective M' q
      have h1 : πL l ∈ M'.map πL := htop ▸ Subgroup.mem_top _
      obtain ⟨m, hm, hml⟩ := h1
      have ho : m⁻¹ * l ∈ CFSG.pCore 2 L := by
        rw [hπL, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hml
        exact QuotientGroup.eq.mp hml
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := L) ⟨_, ho⟩
      have hn' : (m⁻¹ * l) ^ (2 ^ n) = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      refine ⟨n, ?_⟩
      have hl : l = m * (m⁻¹ * l) := by group
      rw [hl, map_mul, QuotientGroup.mk'_apply M' m, (QuotientGroup.eq_one_iff m).mpr hm, one_mul,
        ← map_pow, hn', map_one]
    have hqs : Group.IsSolvable (L ⧸ M') := by
      have := hq2.isNilpotent
      infer_instance
    have hLK : L ≤ K := by
      have h1 := inSubgroup_perfectResidual_le_of_isSolvable (N := K ⊓ L) (U := L) inf_le_right hqs
      exact ((le_inSubgroup_perfectResidual hLp le_rfl).trans h1).trans inf_le_left
    exact false_of_le_sup_pCoreOf hK eK eL (hLK.trans le_sup_left)

theorem item182Alt1At_of_centralizer_le_normalizer (h4443 : Sec4.Item4_44_3) {A M : Subgroup G}
    (h : Sec18Std G A M) {H : Subgroup G} (hHs : H ∈ scriptHStar A M) {c : G} (hcA : c ∈ A)
    (hcL : c ∈ sectionCentralizer A (inSubgroup perfectResidual H)
      (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H)))
    (hCN : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (inSubgroup perfectResidual H : Set G)) :
    Item182Alt1At H := by
  intro X hHX hX
  obtain ⟨K, hK, -, hcase⟩ :=
    Rem187Bypass.exists_mem_oTwoComponentsIn_of_item4443 h4443 h hHs.prop hHX hX
  rcases hcase with hi | ⟨⟨eL⟩, J, hJ, hLXeq, ⟨eK⟩, -⟩
  · exact ⟨K, hK, hi⟩
  · exact (false_of_alt2_of_centralizer_le_normalizer h hHs hHX hK hJ eL hLXeq eK hcA hcL
      hCN).elim

end CFSG.RankThree.PartTwo.Sec18
