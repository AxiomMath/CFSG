module

public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofSL3
import CFSG.RankThree.PartTwo.Sec21.Item228InspProofRefl
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.RankThree.PartTwo.KFacts.KS222SL3Tools
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartOne.KF.LayerCover
public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofOne
public import CFSG.RankThree.PartTwo.Sec21.Item229Gen
public import CFSG.RankThree.PartTwo.Sec21.Item229Orders
public import CFSG.RankThree.PartTwo.Sec21.Item22Tools
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)

@[expose] def SL3E27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A : Subgroup G) (m : ℕ), 0 < m → Even m →
    Nonempty (X ≃* SL3 m) → IsElemAbelian 3 A → Nat.card A = 3 ^ 3 →
    A ≤ Subgroup.normalizer (X : Set G) → Nat.card (A ⊓ X : Subgroup G) = 3 ^ 2 →
    Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = 3 →
    (∀ a ∈ A, ¬ KFacts.InducesKindSL 3 (GaloisField 2 m) X a .field) →
      Nonempty (starOf A X ≃* Equiv.Perm (Fin 3)) ∧
      ∀ B₁ B₂ P₁ P₂ : Subgroup G, B₁ ≤ A → B₂ ≤ A → Nat.card B₁ = 3 ^ 2 →
        Nat.card B₂ = 3 ^ 2 → B₁ ≠ B₂ → P₁ ≤ X ⊓ Subgroup.centralizer (B₁ : Set G) →
        P₂ ≤ X ⊓ Subgroup.centralizer (B₂ : Set G) →
        Nonempty (P₁ ≃* projSL 2 (GaloisField 2 m)) →
        Nonempty (P₂ ≃* projSL 2 (GaloisField 2 m)) → P₁ ⊔ P₂ = X

namespace Item228InspProof

variable {G : Type} [Group G]

theorem card_inf_centralizer_eq_three [Finite G] (h66 : Sec6.Item6_6) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) {X : Subgroup G} (hX : X ∈ lStar A) {a : G}
    (haA : a ∈ A) (ha1 : a ≠ 1) (hXa : X ∈ thetaComponentsAt 3 a) :
    Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = 3 := by
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hXC := Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  have hcyc := h66 G hpair.standing A hpair.mem_S X hX
  have hle : A ⊓ Subgroup.centralizer (X : Set G) ≤ A ⊓ Sec4.thetaQuotCentralizer X := by
    rintro d ⟨hdA, hdC⟩
    refine ⟨hdA, Sec6.mem_thetaQuotCentralizer_iff.mpr
      ⟨Subgroup.centralizer_le_normalizer _ hdC, fun l hl => ?_⟩⟩
    have h1 : l * d = d * l := Subgroup.mem_centralizer_iff.mp hdC l hl
    rw [show l⁻¹ * (d * l * d⁻¹) = 1 by rw [← h1]; group]
    exact Subgroup.one_mem _
  have hle3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) ≤ 3 := by
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    have : g ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 _ g.2.1)
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one this)
  have haC : a ∈ A ⊓ Subgroup.centralizer (X : Set G) :=
    ⟨haA, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hXC hl)⟩
  have hge : 3 ≤ Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
    have h := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr haC)
    rwa [Nat.card_zpowers, orderOf_eq_prime ha3 ha1] at h
  have := (Subgroup.card_le_of_le hle).trans hle3
  omega

theorem mem_of_central_of_SL3 [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) {m : ℕ} (hm0 : 0 < m) (hme : Even m)
    (e : X ≃* SL3 m) {z : G} (hzX : z ∈ X) (hzc : ∀ x ∈ X, x * z = z * x) (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1) : z ∈ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hZ3 : Nat.card (Subgroup.center X) = 3 := by
    rw [CFSG.RankThree.PartOne.KFU.card_center_mulEquiv e]
    exact Item222Proof.card_center_SL3 hm0 hme
  set z' : X := ⟨z, hzX⟩ with hz'
  have hz'c : z' ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hord : orderOf z' = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hz3)) hz'1
  have hZ : Subgroup.center X = Subgroup.zpowers z' := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz'c) ?_
    rw [hZ3, Nat.card_zpowers, hord]
  have hcomm : ∀ b ∈ A, b * z = z * b := by
    intro b hb
    have hbN := hAX hb
    have hwX : b * z * b⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hbN z).mp hzX
    have hwc : (⟨b * z * b⁻¹, hwX⟩ : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      change (g : G) * (b * z * b⁻¹) = b * z * b⁻¹ * g
      have hgX : b⁻¹ * g * b ∈ X := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) g).mp g.2
        simpa [mul_assoc] using this
      have h1 := hzc _ hgX
      calc (g : G) * (b * z * b⁻¹) = b * ((b⁻¹ * g * b) * z) * b⁻¹ := by group
        _ = b * (z * (b⁻¹ * g * b)) * b⁻¹ := by rw [h1]
        _ = b * z * b⁻¹ * g := by group
    rw [hZ] at hwc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwc
    have hk' : z ^ (k % 3) = b * z * b⁻¹ := by
      have h1 : z' ^ (k % 3) = z' ^ k := by
        have h2 := zpow_mod_orderOf z' k
        rwa [hord, Nat.cast_ofNat] at h2
      have h3 := congrArg Subtype.val (h1.trans hk)
      simpa using h3
    have hb3 : b ^ 3 = 1 := hAe.2 b hb
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with h | h | h <;> rw [h] at hk'
    · exfalso
      apply hz1
      rw [zpow_zero] at hk'
      calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
        _ = 1 := by rw [← hk']; group
    · rw [zpow_one] at hk'
      calc b * z = b * z * b⁻¹ * b := by group
        _ = z * b := by rw [← hk']
    · exfalso
      have hw2 : b * z * b⁻¹ = z * z := by
        rw [← hk', show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq]
      have e1 : b * (z * z) * b⁻¹ = z := by
        calc b * (z * z) * b⁻¹ = (b * z * b⁻¹) * (b * z * b⁻¹) := by group
          _ = (z * z) * (z * z) := by rw [hw2]
          _ = z ^ 3 * z := by rw [pow_three]; simp only [mul_assoc]
          _ = z := by rw [hz3, one_mul]
      have hb3' : b * (b * b) = 1 := by rw [← pow_three]; exact hb3
      have e2 : z * z = z * 1 := by
        calc z * z = b * z * b⁻¹ := hw2.symm
          _ = b * (b * (z * z) * b⁻¹) * b⁻¹ := by rw [e1]
          _ = b * (b * (b * z * b⁻¹) * b⁻¹) * b⁻¹ := by rw [hw2]
          _ = (b * (b * b)) * z * (b * (b * b))⁻¹ := by group
          _ = z * 1 := by rw [hb3']; group
      exact hz1 (mul_left_cancel e2)
  by_contra hzA
  obtain ⟨hE, hcard⟩ := Sec5.isElemAbelian_sup_zpowers hAe hzA hz3 hcomm
  have hEq := hpair.mem_S.1.2.1 _ hE le_sup_left
  rw [hEq] at hcard
  have hpos : 0 < Nat.card A := Nat.card_pos
  omega

theorem card_inf_eq_nine_of_SL3 [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) (hK : KOfWellDefined A)
    {φ : MulAut A} (hφ : φ ∈ dStar A) {X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hKX : kOf A φ ≤ X) {m : ℕ} (hm0 : 0 < m)
    (hme : Even m) (e : X ≃* SL3 m) : Nat.card (A ⊓ X : Subgroup G) = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hφr := hφ.1
  have hφφ := apply_apply_of_orderOf_eq_two hφr.1
  obtain ⟨z, hz1, hz3, hzc⟩ := exists_central_SL3 hm0 hme
  set z₀ : G := ((e.symm z : X) : G) with hz₀def
  have hz₀X : z₀ ∈ X := (e.symm z).2
  have hz₀c : ∀ x ∈ X, x * z₀ = z₀ * x := by
    intro x hx
    have h := congrArg (fun g => ((e.symm g : X) : G)) (hzc (e ⟨x, hx⟩))
    simpa [map_mul] using h
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    apply hz1
    have h' : e.symm z = 1 := Subtype.ext h
    rw [← map_one e.symm] at h'
    exact e.symm.injective h'
  have hz₀3 : z₀ ^ 3 = 1 := by
    rw [hz₀def, ← Subgroup.coe_pow, ← map_pow, hz3, map_one, Subgroup.coe_one]
  have hz₀A : z₀ ∈ A := mem_of_central_of_SL3 hpair hAX hm0 hme e hz₀X hz₀c hz₀1 hz₀3
  obtain ⟨j, hjK, -, hj⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hφ
  have hfix : φ ⟨z₀, hz₀A⟩ = ⟨z₀, hz₀A⟩ := by
    rw [← hj]
    apply Subtype.ext
    rw [wConj_apply]
    change (j : G) * z₀ * (j : G)⁻¹ = z₀
    rw [hz₀c j (hKX hjK), mul_inv_cancel_right]
  have hz₀C : (⟨z₀, hz₀A⟩ : A) ∉ commOf φ := by
    intro h
    have h1 := inv_of_mem_commOf hAc hφφ h
    rw [hfix] at h1
    exact hz₀1 (congrArg Subtype.val (eq_one_of_eq_inv (fun a : A => Subtype.ext (by
      simpa using hAe.2 a a.2)) h1))
  set C : Subgroup A := commOf φ ⊔ Subgroup.zpowers ⟨z₀, hz₀A⟩ with hCdef
  have hlt : commOf φ < C := lt_of_le_of_ne le_sup_left fun h =>
    hz₀C (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hC9 : 3 ^ 2 ≤ Nat.card C := by
    have h1 := Subgroup.card_lt_of_lt hlt
    rw [hφr.2] at h1
    have hdvd : Nat.card C ∣ 3 ^ 3 := hA27 ▸ Subgroup.card_subgroup_dvd_card C
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hkeq] at h1 ⊢
    have hk2 : 2 ≤ k := by
      by_contra hk2
      interval_cases k <;> norm_num at h1
    exact Nat.pow_le_pow_right (by norm_num) hk2
  have hCX : C.map A.subtype ≤ A ⊓ X := by
    refine le_inf (Subgroup.map_subtype_le _) ?_
    rw [hCdef, Subgroup.map_sup, MonoidHom.map_zpowers]
    exact sup_le ((map_commOf_le_kOf h222 hpair hK hφ).trans hKX)
      (Subgroup.zpowers_le.mpr hz₀X)
  have hge := Subgroup.card_le_of_le hCX
  rw [Subgroup.card_map_of_injective A.subtype_injective] at hge
  have hle := card_le_nine_of_le_SL3 e (inf_le_right : A ⊓ X ≤ X)
    (fun x hx y hy => congrArg Subtype.val (hAc ⟨x, hx.1⟩ ⟨y, hy.1⟩))
    (fun x hx => hAe.2 x hx.1)
  omega

theorem mulEquiv_kOf_of_SL3 {A : Subgroup G} {ψ : MulAut A} {X : Subgroup G} {m : ℕ}
    (hm0 : 0 < m) (hme : Even m) (eX : X ≃* SL3 m) (hψX : Item228OneConcl A ψ X) :
    Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 m)) := by
  obtain ⟨m', hm'0, hm'e, eJ, h⟩ := hψX
  have hns := not_isSimpleGroup_SL3 hm0 hme
  have hsimp : ∀ {S : Type} [Group S] [IsSimpleGroup S], Nonempty (X ≃* S) → False := by
    intro S _ _ ⟨f⟩
    exact hns ((eX.symm.trans f).isSimpleGroup)
  have hm'2 : 2 ≤ m' := by obtain ⟨r, hr⟩ := hm'e; omega
  rcases h with hSL | hSp | hU | ⟨hm4, hU⟩ | ⟨-, hU⟩
  ·
    obtain ⟨f⟩ := hSL
    have hc := Nat.card_congr (eX.symm.trans f).toEquiv
    rw [SL3Lines.card_SL3_eq m hm0, SL3Lines.card_SL3_eq m' hm'0] at hc
    have ho : ∀ n : ℕ, 0 < n → Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := fun n hn =>
      (SL3Lines.odd_pow_sub_one_add_one hn (by norm_num)).1.mul
        (SL3Lines.odd_pow_sub_one_add_one hn (by norm_num)).1
    have hv := congrArg (padicValNat 2) hc
    rw [padicValNat_two_pow_mul_odd (ho m hm0), padicValNat_two_pow_mul_odd (ho m' hm'0)] at hv
    have hmm : m = m' := by omega
    rw [hmm]
    exact eJ
  · have := isSimpleGroup_projSp_two hm'2
    exact (hsimp hSp).elim
  · have := isSimpleGroup_projSU (m := 4) (n := m') le_rfl (by omega)
    exact (hsimp hU).elim
  · have := isSimpleGroup_projSU (m := 4) (n := m' / 2) le_rfl (by omega)
    exact (hsimp hU).elim
  · have := isSimpleGroup_projSU (m := 5) (n := 2) (by norm_num) (by norm_num)
    exact (hsimp hU).elim

theorem insp228_of_SL3 [Finite G] (hNF : Item228NoFieldThree) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (h222 : Item222) (hKW : KOfWellDefinedAll) (hSL : SL3E27)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3)
    {φ ψ : MulAut A} (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (hne : ψ ≠ φ) {X : Subgroup G}
    (hX : X ∈ lStar A) (hKX : kOf A φ ≤ X) (hJX : kOf A ψ ≤ X) {m : ℕ} (hm0 : 0 < m)
    (hme : Even m) (eK : kOf A φ ≃* projSL 2 (GaloisField 2 m)) (eX : X ≃* SL3 m)
    (hψX : Item228OneConcl A ψ X) : Insp228NonComm A φ ψ := by
  unfold Insp228NonComm
  intro _
  have hK := hKW G A E U c L hpair
  have hG := hpair.standing.toTheoremFourHyp
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hne' : φ ≠ ψ := fun h => hne h.symm
  obtain ⟨a, haA, ha1, hXa⟩ := mem_thetaComponentFamily_iff.mp hX.1
  have hAX := Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe haA ha1 X hXa
  have hC3 := card_inf_centralizer_eq_three h66 hpair hX haA ha1 hXa
  have hAX9 := card_inf_eq_nine_of_SL3 h222 hpair hA27 hK hφ hAX hKX hm0 hme eX
  have hfield : ∀ x ∈ A, ¬ KFacts.InducesKindSL 3 (GaloisField 2 m) X x .field :=
    fun x hx h => (hNF G A E U c L hpair hA27 φ hφ X hX hKX x hx).1
      (KFacts.InducesStdKind.sl 3 (GaloisField 2 m) le_rfl h)
  obtain ⟨hstar, hgen⟩ := hSL G X A m hm0 hme ⟨eX⟩ hAe hA27 hAX hAX9 hC3 hfield
  have hfix9 : ∀ {χ : MulAut A}, χ ∈ dStar A → Nat.card (fixedInG A χ) = 3 ^ 2 := by
    intro χ hχ
    rw [fixedInG, Subgroup.card_map_of_injective A.subtype_injective]
    have h := card_eq_three_mul_card_fixed hAc hχ.1
    rw [hA27] at h
    omega
  have hBne : fixedInG A φ ≠ fixedInG A ψ := fun h =>
    fixedSubgroupOf_ne_of_ne h222 hpair hK hφ hψ hne'
      (Subgroup.map_injective A.subtype_injective h)
  have hP : ∀ {χ : MulAut A}, χ ∈ dStar A → kOf A χ ≤ X →
      kOf A χ ≤ X ⊓ Subgroup.centralizer (fixedInG A χ : Set G) := fun hχ hχX =>
    le_inf hχX ((kOf_le_kZero hK hχ).trans (kZero_le_centralizer A _))
  have hKJ : kOf A φ ⊔ kOf A ψ = X :=
    hgen _ _ _ _ (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _) (hfix9 hφ) (hfix9 hψ)
      hBne (hP hφ hKX) (hP hψ hJX) ⟨eK⟩ (mulEquiv_kOf_of_SL3 hm0 hme eX hψX)
  have hθ := Item222Proof.inSubgroup_theta_eq_bot_of_mulEquiv_SL3 hm0 hme eX
  refine Or.inl ⟨by rw [hKJ]; exact hX, ?_, ?_⟩
  · rw [hKJ]
    exact Or.inl ⟨hA27, m, hm0, hme, ⟨(mulEquiv_lBar_of_theta_eq_bot hθ).symm.trans eX⟩, ⟨eK⟩,
      hstar⟩
  · rw [hKJ]
    refine ⟨fun f => not_isSimpleGroup_SL3 hm0 hme ?_⟩
    have := isSimpleGroup_projSU (m := 5) (n := 2) (by norm_num) (by norm_num)
    exact (eX.symm.trans f).isSimpleGroup

end Item228InspProof

open Item228InspProof

theorem insp228SL3NonComm_of
    (hNF : Item228NoFieldThree) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) (hSL : SL3E27) : Insp228SL3NonComm := by
  intro G _ _ A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX hfam hψX
  obtain ⟨m, hm0, hme, ⟨eK⟩, ⟨eX⟩⟩ := hfam
  exact insp228_of_SL3 hNF h45 h66 h222 hKW hSL hpair hA27 hφ hψ hne hX hKX hJX hm0 hme eK eX hψX


end CFSG.RankThree.PartTwo.Sec21
