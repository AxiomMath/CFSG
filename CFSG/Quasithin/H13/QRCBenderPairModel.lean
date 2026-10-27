module

public import CFSG.Quasithin.H13.QRCBenderModels
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.ShultStronglyClosedTI
  CFSG.GorensteinWalter CFSG.BenderSuzuki.MatrixGroups CFSG.Quasithin.SteinbergBS
  CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Positioning

variable {L Y : Type*} [Group L] [Group Y] [Finite L] [Finite Y]

omit [Finite L] in
theorem exists_mulEquiv_map_sylow (e : L ≃* Y) {S : Subgroup L} (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) {U₀ : Subgroup Y} (hU₀ : IsPGroup 2 U₀) (hU₀i : ¬ 2 ∣ U₀.index) :
    ∃ e' : L ≃* Y, S.map e'.toMonoidHom = U₀ ∧
      (normalizer (S : Set L)).map e'.toMonoidHom = normalizer (U₀ : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsSylowOf 2 (S.map e.toMonoidHom) ⊤ := isSylowOf_iff.2 ⟨le_top, hS.map _, by
    rw [relIndex_top_right, index_map_of_bijective e.bijective]
    exact hSi⟩
  have h2 : IsSylowOf 2 U₀ ⊤ := isSylowOf_iff.2 ⟨le_top, hU₀, by rwa [relIndex_top_right]⟩
  obtain ⟨k, -, hk⟩ := h1.exists_mem_conj h2
  have hmap : S.map (e.trans (MulAut.conj k)).toMonoidHom = U₀ := by
    ext y
    rw [hk y]
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s, hs, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, MulAut.conj_apply]
      group
    · rintro ⟨s, hs, hsy⟩
      refine ⟨s, hs, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, MulAut.conj_apply] at hsy ⊢
      rw [hsy]
      group
  exact ⟨e.trans (MulAut.conj k), hmap, by rw [map_equiv_normalizer_eq, hmap]⟩

omit [Finite L] [Finite Y] in
theorem relIndex_map_mulEquiv (e : L ≃* Y) (H K : Subgroup L) :
    (H.map e.toMonoidHom).relIndex (K.map e.toMonoidHom) = H.relIndex K := by
  rw [relIndex_map_map, show (e.toMonoidHom).ker = ⊥ from
    (MonoidHom.ker_eq_bot_iff _).2 e.injective, sup_bot_eq, sup_bot_eq]

omit [Finite L] [Finite Y] in
theorem not_comm_of_fusionBenderBorel {q k : ℕ} (hB : fusionBenderBorel Y q k) (hq : 2 ≤ q)
    (hk : 2 ≤ k) (Q : Sylow 2 Y)
    (hQ : ∀ a ∈ (Q : Subgroup Y), ∀ b ∈ (Q : Subgroup Y), a * b = b * a) : False := by
  obtain ⟨-, -, -, hZ, hQcard⟩ := hB Q
  have htop : center (Q : Subgroup Y) = ⊤ :=
    eq_top_iff.2 fun z _ => mem_center_iff.2 fun g => Subtype.ext (hQ _ g.2 _ z.2)
  rw [htop, card_top, hQcard] at hZ
  have h1 : q ^ 2 ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk
  have h2 : q < q ^ 2 := by nlinarith
  omega

end Positioning

theorem three_dvd_card_psl2 {f : ℕ} (hf : f ≠ 0) :
    3 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) := by
  rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psl2_even hf]
  refine Dvd.dvd.mul_left ?_ _
  have h4 : (2 ^ f) ^ 2 % 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, Nat.pow_mod]
    simp
  have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ Nat.one_le_two_pow
  omega

theorem three_dvd_card_psu3 {f : ℕ} (hf : 1 ≤ f) : 3 ∣ Nat.card (PSU3 2 f) := by
  have h := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd hf
  set q := 2 ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hsq : (q ^ 2 - 1) % 3 = 0 ∨ q % 3 = 0 := by
    have : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h0 | h0 | h0
    · exact Or.inr h0
    · left
      have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h0]
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
      omega
    · left
      have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h0]
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
      omega
  have hq3 : ¬ 3 ∣ q := by
    intro h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hsq' : 3 ∣ q ^ 2 - 1 := by
    rcases hsq with h0 | h0
    · exact Nat.dvd_of_mod_eq_zero h0
    · exact absurd (Nat.dvd_of_mod_eq_zero h0) hq3
  by_cases hq1' : 3 ∣ q + 1
  ·
    have hg : Nat.gcd 3 (q + 1) = 3 := Nat.gcd_eq_left hq1'
    rw [hg] at h
    have h3 : 3 ∣ q ^ 3 + 1 := by
      have : q % 3 = 2 := by omega
      have : q ^ 3 % 3 = 2 := by rw [Nat.pow_mod, this]
      omega
    have h9 : 3 * 3 ∣ Nat.card (PSU3 2 f) * 3 := by
      rw [h]
      exact Dvd.dvd.mul_left (Nat.mul_dvd_mul hsq' h3) _
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h9
  · have hg : Nat.gcd 3 (q + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hq1'
    rw [hg, mul_one] at h
    rw [h]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hsq' _) _

section Pair

variable {G : Type*} [Group G] [Finite G]

theorem dvd_of_relIndex_inf {U L : Subgroup G} {k n : ℕ} (hU : IsPGroup 2 U) (hk : 1 ≤ k)
    (hUN : U.relIndex (normalizer (U : Set G)) = 2 ^ n - 1)
    (hUL : (U ⊓ L).relIndex (L ⊓ normalizer (U : Set G)) = 2 ^ k - 1) : k ∣ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := relIndex_mul_card (U ⊓ L) (L ⊓ normalizer (U : Set G))
  have hN := relIndex_mul_card U (normalizer (U : Set G))
  rw [inf_eq_left.2 (le_inf inf_le_right (inf_le_left.trans le_normalizer)), hUL] at hP
  rw [inf_eq_left.2 le_normalizer, hUN] at hN
  have hdvd : (2 ^ k - 1) ∣ (2 ^ n - 1) * Nat.card U := by
    rw [hN]
    exact (Dvd.intro _ hP).trans (card_dvd_of_le inf_le_right)
  obtain ⟨j, hj⟩ := hU.exists_card_eq
  rw [hj] at hdvd
  have hodd : Odd (2 ^ k - 1) := by
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    exact ⟨2 ^ (k - 1) - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ k - 1) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.2 hodd)
  have h1 := hcop.dvd_of_dvd_mul_right hdvd
  have h2 := Nat.pow_sub_one_gcd_pow_sub_one 2 k n
  rw [Nat.gcd_eq_left h1] at h2
  have h3 : 2 ^ k = 2 ^ Nat.gcd k n := by
    have : 1 ≤ 2 ^ Nat.gcd k n := Nat.one_le_two_pow
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have h4 := Nat.pow_right_injective (le_refl 2) h3
  rw [h4]
  exact Nat.gcd_dvd_right k n

theorem bender_pair_linear
    {U E : Subgroup G} {n : ℕ} (hD : BenderData G U n)
    (hab : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) [IsElementaryAbelian 2 E] (hEU : E ≤ U)
    (hE4 : 4 ≤ Nat.card E) {x : G} (hx : x ∉ normalizer (U : Set G)) :
    ∃ f : ℕ, 2 ≤ f ∧ f ∣ n ∧ Nat.card E ≤ 2 ^ f ∧
      ∃ e : ↥(E ⊔ conjugate E x) ≃* PSL2MatrixGroup (GaloisField 2 f),
        (((E ⊔ conjugate E x) ⊓ normalizer (U : Set G)).subgroupOf (E ⊔ conjugate E x)).map
          e.toMonoidHom = psl2Borel (GaloisField 2 f) ∧
        ((U ⊓ (E ⊔ conjugate E x)).subgroupOf (E ⊔ conjugate E x)).map e.toMonoidHom =
          psl2UpperUnipotentSubgroup (GaloisField 2 f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := E ⊔ conjugate E x with hLdef
  set P := L ⊓ normalizer (U : Set G) with hPdef
  have hC : ∀ e ∈ E, e ≠ 1 → IsPGroup 2 (centralizer ({e} : Set G)) := fun e he he1 =>
    hD.centralizer_isPGroup e (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian e he) he1)
  obtain ⟨hB, hsyl, hnorm, -, -, -, -⟩ :=
    bender_pair_props hD.isPGroup hD.not_dvd_index hD.stronglyEmbedded hC hEU hE4 hx
  obtain ⟨Q, hQ⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hQab : ∀ a ∈ (Q : Subgroup L), ∀ b ∈ (Q : Subgroup L), a * b = b * a := by
    intro a ha b hb
    rw [hQ, mem_subgroupOf] at ha hb
    exact Subtype.ext (hab _ ha.1 _ hb.1)
  rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨b, hb, ⟨e⟩⟩
  · have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    have hM := benderData_psl2 hcardF
    obtain ⟨e', he'S, he'N⟩ := exists_mulEquiv_map_sylow e Q.isPGroup' Q.not_dvd_index
      hM.isPGroup hM.not_dvd_index
    have hrel : (U ⊓ L).relIndex P = 2 ^ f - 1 := by
      rw [← hM.relIndex, ← he'N, ← he'S, relIndex_map_mulEquiv, hQ, ← hnorm,
        relIndex_subgroupOf inf_le_left]
    have hcardQ : Nat.card ↥(U ⊓ L) = 2 ^ f := by
      have h1 : Nat.card ↥((Q : Subgroup L).map e'.toMonoidHom) = Nat.card ↥(Q : Subgroup L) :=
        card_map_of_injective (f := e'.toMonoidHom) e'.injective
      rw [he'S, psl2UpperUnipotentSubgroup_card, hcardF, hQ] at h1
      rw [← Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : U ⊓ L ≤ L)).toEquiv]
      exact h1.symm
    refine ⟨f, hf, dvd_of_relIndex_inf hD.isPGroup (by omega) hD.relIndex hrel, ?_, e', ?_, ?_⟩
    · rw [← hcardQ]
      exact card_le_of_le (le_inf hEU le_sup_left)
    · rw [hnorm, ← hQ, he'N, psl2_normalizer_rootGroup]
    · rw [← hQ, he'S]
  · exfalso
    have : Finite (PSU3 2 f) := Finite.of_injective _ e.symm.injective
    have hBB := (bender_psu3_borel_full f hf).map_mulEquiv e.symm
    refine not_comm_of_fusionBenderBorel hBB ?_ (by norm_num) Q hQab
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  · exfalso
    have : Finite (Sz b) := Finite.of_injective _ e.symm.injective
    have hBB := (bender_suzuki_borel_full b hb).map_mulEquiv e.symm
    refine not_comm_of_fusionBenderBorel hBB ?_ (le_refl 2) Q hQab
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem bender_pair_suzuki
    {U E : Subgroup G} {n : ℕ} (hD : BenderData G U n)
    (h3 : ¬ 3 ∣ Nat.card G) [IsElementaryAbelian 2 E] (hEU : E ≤ U)
    (hE4 : 4 ≤ Nat.card E) {x : G} (hx : x ∉ normalizer (U : Set G)) :
    ∃ b : ℕ, 1 ≤ b ∧ 2 * b + 1 ∣ n ∧ Nat.card E ≤ 2 ^ (2 * b + 1) ∧
      ∃ e : ↥(E ⊔ conjugate E x) ≃* suzukiGroup b (GaloisField 2 (2 * b + 1)),
        (((E ⊔ conjugate E x) ⊓ normalizer (U : Set G)).subgroupOf (E ⊔ conjugate E x)).map
          e.toMonoidHom = suzukiB b (GaloisField 2 (2 * b + 1)) ∧
        ((U ⊓ (E ⊔ conjugate E x)).subgroupOf (E ⊔ conjugate E x)).map e.toMonoidHom =
          suzukiU b (GaloisField 2 (2 * b + 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := E ⊔ conjugate E x with hLdef
  set P := L ⊓ normalizer (U : Set G) with hPdef
  have hC : ∀ e ∈ E, e ≠ 1 → IsPGroup 2 (centralizer ({e} : Set G)) := fun e he he1 =>
    hD.centralizer_isPGroup e (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian e he) he1)
  obtain ⟨hB, hsyl, hnorm, -, -, -, -⟩ :=
    bender_pair_props hD.isPGroup hD.not_dvd_index hD.stronglyEmbedded hC hEU hE4 hx
  obtain ⟨Q, hQ⟩ := hsyl.exists_sylow_eq_subgroupOf
  have h3L : ¬ 3 ∣ Nat.card L := fun h => h3 (h.trans (card_subgroup_dvd_card L))
  rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨b, hb, ⟨e₀⟩⟩
  · exact absurd ((three_dvd_card_psl2 (by omega)).trans (Nat.card_congr e.toEquiv).symm.dvd)
      h3L
  · exact absurd ((three_dvd_card_psu3 (by omega)).trans (Nat.card_congr e.toEquiv).symm.dvd)
      h3L
  · obtain ⟨σ⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup b
    set e := e₀.trans σ with hedef
    have hcardF : Nat.card (GaloisField 2 (2 * b + 1)) = 2 ^ (2 * b + 1) :=
      GaloisField.card 2 (2 * b + 1) (by omega)
    have : Finite (suzukiGroup b (GaloisField 2 (2 * b + 1))) := Finite.of_injective _
      e.symm.injective
    have hM := benderData_suzuki hb hcardF
    obtain ⟨e', he'S, he'N⟩ := exists_mulEquiv_map_sylow e Q.isPGroup' Q.not_dvd_index
      hM.isPGroup hM.not_dvd_index
    have hrel : (U ⊓ L).relIndex P = 2 ^ (2 * b + 1) - 1 := by
      rw [← hM.relIndex, ← he'N, ← he'S, relIndex_map_mulEquiv, hQ, ← hnorm,
        relIndex_subgroupOf inf_le_left]
    refine ⟨b, hb, dvd_of_relIndex_inf hD.isPGroup (by omega) hD.relIndex hrel, ?_, e', ?_, ?_⟩
    ·
      have hEZ : (E.subgroupOf L).map e'.toMonoidHom ≤ suzukiZ0 b (GaloisField 2 (2 * b + 1)) := by
        rintro _ ⟨y, hy, rfl⟩
        have hyE : (y : G) ∈ E := hy
        have hyQ : y ∈ (Q : Subgroup L) := by
          rw [hQ, mem_subgroupOf]
          exact ⟨hEU hyE, y.2⟩
        have hyU : e' y ∈ suzukiU b (GaloisField 2 (2 * b + 1)) := he'S ▸ ⟨y, hyQ, rfl⟩
        have hcen : (⟨e' y, hyU⟩ : suzukiU b (GaloisField 2 (2 * b + 1))) ∈
            center (suzukiU b (GaloisField 2 (2 * b + 1))) := by
          rw [mem_center_iff]
          rintro ⟨z, hz⟩
          apply Subtype.ext
          rw [← he'S] at hz
          obtain ⟨w, hw, rfl⟩ := hz
          have hw' : (w : G) ∈ U ⊓ L := by
            have h0 : w ∈ (Q : Subgroup L) := hw
            rw [hQ] at h0
            exact h0
          have h1 : (y : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hyE
          have h2 := hD.sq_comm (y : G) (hEU hyE) h1 (w : G) hw'.1
          change e' w * e' y = e' y * e' w
          rw [← map_mul, ← map_mul]
          exact congrArg e' (Subtype.ext h2.symm)
        rw [SuzukiRootAutomorphism.center_suzukiU hcardF hb, mem_subgroupOf] at hcen
        exact hcen
      have h1 := card_le_of_le hEZ
      rw [card_map_of_injective (f := e'.toMonoidHom) e'.injective,
        SuzukiModel.card_suzukiZ0 hcardF,
        Nat.card_congr (subgroupOfEquivOfLe le_sup_left).toEquiv] at h1
      exact h1
    · rw [hnorm, ← hQ, he'N, suzuki_normalizer_suzukiU hcardF]
    · rw [← hQ, he'S]

end Pair

end CFSG.Quasithin.H13.QRC
