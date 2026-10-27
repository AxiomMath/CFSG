module

public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofU4
public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofOne
public import CFSG.RankThree.PartTwo.KFacts.KS222Sp4
import CFSG.RankThree.PartTwo.Sec21.Item228InspProofRefl
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)

@[expose] def Sp4EvenTorus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T : Subgroup G) (k : ℕ), 0 < k → Even k →
    Nonempty (X ≃* projSp 2 (GaloisField 2 k)) → T ≤ X → IsElemAbelian 3 T → Nat.card T = 3 ^ 2 →
      Nonempty (starOf T X ≃* DihedralGroup 4) ∧
      ∀ ℓ₁ ℓ₂ c₁ c₂ : Subgroup G, ℓ₁ ≤ T → ℓ₂ ≤ T → c₁ ≤ T → c₂ ≤ T →
        Nat.card ℓ₁ = 3 → Nat.card ℓ₂ = 3 → Nat.card c₁ = 3 → Nat.card c₂ = 3 → ℓ₁ ≠ ℓ₂ →
        c₁ ≤ perfCent X ℓ₁ → c₂ ≤ perfCent X ℓ₂ →
          (c₁ = ℓ₂ → c₂ = ℓ₁ ∧ ⁅perfCent X ℓ₁, perfCent X ℓ₂⁆ = ⊥) ∧
          (c₁ ≠ ℓ₂ → perfCent X ℓ₁ ⊔ perfCent X ℓ₂ = X)

namespace Item228InspProof

variable {G : Type} [Group G]

theorem isEmpty_mulEquiv_projSU_five_of_Sp4 {X : Type*} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (hme : Even m) (eX : X ≃* projSp 2 (GaloisField 2 m)) : IsEmpty (X ≃* projSU 5 2 2) := by
  refine ⟨fun f => ?_⟩
  have h := Nat.card_congr (eX.symm.trans f).toEquiv
  rw [card_projSp_two hm, ordBC_two_eq (by omega), card_projSU_five_two_two] at h
  have hodd : ∀ j : ℕ, 0 < j → Odd ((2 ^ m) ^ j - 1) := fun j hj => by
    have h1 : Even ((2 ^ m) ^ j) := by
      rw [← pow_mul]
      exact (Nat.even_pow' (by positivity)).mpr even_two
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) h1 odd_one
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat_pow_two_pow_mul_odd ((hodd 2 (by norm_num)).mul (hodd 4 (by norm_num))),
    padicValNat_two_pow_mul_odd (by decide)] at hv
  obtain ⟨r, hr⟩ := hme
  omega

theorem not_inducesOuterTheta_of_Sp4 [Finite G] {X : Subgroup G} {F : Type} [Field F] [Finite F]
    [CharP F 2] (e : X ⧸ aschbacherSolvableCore 3 X ≃* StatedProj (StatedSp 2 F)) {x : G}
    (hx3 : x ^ 3 = 1) (hfield : ¬ KFacts.InducesStdKind X x .field) :
    ¬ Sec4.InducesOuterTheta x X := by
  intro hout
  rcases KFacts.inducesKindPSp4Even_diagonal_or_field X hx3 hout e with ⟨hx, hD, hnot⟩ | hF
  · obtain ⟨B, hB⟩ := hD
    apply hnot
    rw [← hB]
    exact KFacts.conjAut_mem_inner_of_charTwo B
  · exact hfield (KFacts.InducesStdKind.psp4even F ⟨e, hF⟩)

theorem innerData_of_Sp4 [Finite G] (hNF : Item228NoFieldThree) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hA27 : Nat.card A = 3 ^ 3) {φ : MulAut A} (hφ : φ ∈ dStar A) {X : Subgroup G}
    (hX : X ∈ lStar A) (hKX : kOf A φ ≤ X) {m : ℕ} (hm : 2 ≤ m)
    (eX : X ≃* projSp 2 (GaloisField 2 m)) : InnerData A X := by
  have hG := hpair.standing.toTheoremFourHyp
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  obtain ⟨a, haA, ha1, hXa⟩ := mem_thetaComponentFamily_iff.mp hX.1
  have hAX := Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe haA ha1 X hXa
  have : IsSimpleGroup (projSp 2 (GaloisField 2 m)) := isSimpleGroup_projSp_two hm
  have : IsSimpleGroup X := eX.isSimpleGroup
  have hperf : Group.IsPerfect X := isPerfect_of_mem_thetaComponentFamily hX.1
  have hZ := Item223PrintProof.center_eq_bot_of_isSimpleGroup_of_isPerfect hperf
  have hθ := inSubgroup_theta_eq_bot_of_mulEquiv hperf eX
  have hθ' : aschbacherSolvableCore 3 X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hθ
  have eθ : X ⧸ aschbacherSolvableCore 3 X ≃* StatedProj (StatedSp 2 (GaloisField 2 m)) :=
    ((mulEquiv_lBar_of_theta_eq_bot hθ).symm.trans eX).trans
      (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSp 2 (GaloisField 2 m))).symm
  have hinner : ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X := fun x hxA =>
    not_inducesOuterTheta_of_Sp4 eθ (hAe.2 x hxA)
      (hNF G A E U c L hpair hA27 φ hφ X hX hKX x hxA).1
  exact innerData_of_inner h66 hpair hA27 hX haA ha1 hXa hAX hZ hθ' hinner

theorem insp228_of_Sp4 [Finite G] (hNF : Item228NoFieldThree) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (h222 : Item222) (hKW : KOfWellDefinedAll) (hSp : Sp4EvenTorus)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3)
    {φ ψ : MulAut A} (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (hne : ψ ≠ φ) {X : Subgroup G}
    (hX : X ∈ lStar A) (hKX : kOf A φ ≤ X) (hJX : kOf A ψ ≤ X) {m : ℕ} (hm0 : 0 < m)
    (hme : Even m) (eK : kOf A φ ≃* projSL 2 (GaloisField 2 m))
    (eX : X ≃* projSp 2 (GaloisField 2 m)) : Insp228Comm A φ ψ ∧ Insp228NonComm A φ ψ := by
  have hK := hKW G A E U c L hpair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  have hne' : φ ≠ ψ := fun h => hne h.symm
  have hm2 : 2 ≤ m := by obtain ⟨r, hr⟩ := hme; omega
  have hD := innerData_of_Sp4 hNF h45 h66 hpair hA27 hφ hX hKX hm2 eX
  set T := A ⊓ X with hTdef
  have hTe : IsElemAbelian 3 T := Sec5.isElemAbelian_of_le hAe inf_le_left
  obtain ⟨hD8, hpairs⟩ := hSp G X T m hm0 hme ⟨eX⟩ inf_le_right hTe hD.card_inf
  have hS : ∀ ℓ : Subgroup G, ℓ ≤ T → Nat.card ℓ = 3 → ∃ n : ℕ, 2 ≤ n ∧
      Nonempty (perfCent X ℓ ≃* projSL 2 (GaloisField 2 n)) := fun ℓ hℓ h3 =>
    ⟨m, hm2, ks222Sp4 G X ℓ m hm0 hme ⟨eX⟩ (hℓ.trans inf_le_right) h3⟩
  obtain ⟨hℓ₁3, hfix₁, hK₁, hc₁T, -⟩ := root_facts h222 hpair hK hD hφ hKX hS
  obtain ⟨hℓ₂3, hfix₂, hK₂, hc₂T, -⟩ := root_facts h222 hpair hK hD hψ hJX hS
  have hc₁3 : Nat.card ((commOf φ).map A.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hφ.1.2
  have hc₂3 : Nat.card ((commOf ψ).map A.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hψ.1.2
  have hℓne : T ⊓ fixedInG A φ ≠ T ⊓ fixedInG A ψ := fun h =>
    fixedSubgroupOf_ne_of_ne h222 hpair hK hφ hψ hne' (Subgroup.map_injective
      A.subtype_injective (Item223PrintProof.fixedInG_eq_of_inf_eq hD.decomp
        (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _) hfix₁ hfix₂ h))
  have hc₁S : (commOf φ).map A.subtype ≤ perfCent X (T ⊓ fixedInG A φ) :=
    hK₁ ▸ map_commOf_le_kOf h222 hpair hK hφ
  have hc₂S : (commOf ψ).map A.subtype ≤ perfCent X (T ⊓ fixedInG A ψ) :=
    hK₂ ▸ map_commOf_le_kOf h222 hpair hK hψ
  obtain ⟨hL1, hL2⟩ := hpairs _ _ _ _ inf_le_left inf_le_left hc₁T hc₂T hℓ₁3 hℓ₂3 hc₁3 hc₂3
    hℓne hc₁S hc₂S
  have hcℓ : ∀ {χ χ' : MulAut A}, (commOf χ).map A.subtype = T ⊓ fixedInG A χ' →
      commOf χ ≤ fixedSubgroupOf χ' := fun h =>
    (Subgroup.map_le_map_iff_of_injective A.subtype_injective).mp (h.le.trans inf_le_right)
  refine ⟨fun hc => ?_, fun hnc => ?_⟩
  ·
    have h₂ : commOf φ ≤ fixedSubgroupOf ψ :=
      commOf_le_fixedSubgroupOf_of_commute hAc hA3 hψ.1 hφ.1 hc.symm hne
    have hc₁ℓ₂ : (commOf φ).map A.subtype = T ⊓ fixedInG A ψ :=
      Subgroup.eq_of_le_of_card_ge (le_inf hc₁T (Subgroup.map_mono h₂)) (by rw [hℓ₂3, hc₁3])
    left
    rw [hK₁, hK₂]
    exact (hL1 hc₁ℓ₂).2
  ·
    have hc₁ne : (commOf φ).map A.subtype ≠ T ⊓ fixedInG A ψ := by
      intro h
      obtain ⟨hc₂ℓ₁, -⟩ := hL1 h
      exact hnc (commute_of_commOf_le hAc hA3 hφ.1.1 (hcℓ h) (hcℓ hc₂ℓ₁))
    have hY : kOf A φ ⊔ kOf A ψ = X := by
      rw [hK₁, hK₂]
      exact hL2 hc₁ne
    refine Or.inl ⟨by rw [hY]; exact hX, Or.inr (Or.inl ⟨hA27, m, hm0, hme, ?_, ⟨eK⟩, ?_⟩), ?_⟩
    · rw [hY]
      exact ⟨eX⟩
    · rw [hY]
      obtain ⟨e₁⟩ := nonempty_starOf_mulEquiv_inf hD
      obtain ⟨e₂⟩ := hD8
      exact ⟨e₁.trans e₂⟩
    · rw [hY]
      exact isEmpty_mulEquiv_projSU_five_of_Sp4 hm2 hme eX

end Item228InspProof

open Item228InspProof

theorem insp228Sp4_of
    (hNF : Item228NoFieldThree) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) (hSp : Sp4EvenTorus) : Insp228Sp4 := by
  intro G _ _ A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX hfam _
  obtain ⟨m, hm0, hme, ⟨eK⟩, ⟨eX⟩⟩ := hfam
  exact insp228_of_Sp4 hNF h45 h66 h222 hKW hSp hpair hA27 hφ hψ hne hX hKX hJX hm0 hme eK eX

end CFSG.RankThree.PartTwo.Sec21
