module

public import CFSG.Quasithin.H13.KG14726LTools
public import CFSG.Quasithin.H13.KG14726C27C
public import CFSG.Quasithin.H13.KG14726L115
public import CFSG.Quasithin.Vol2.F134Orders

public noncomputable section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open Subgroup KG14726

namespace KG14726

section Lift

variable {L : Type*} [Group L]

theorem exists_lift_orderOf_prime (hZ : IsPGroup 2 ↥(center L)) {u : L ⧸ center L} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hu : orderOf u = p) :
    ∃ ℓ : L, (ℓ : L ⧸ center L) = u ∧ orderOf ℓ = p := by
  obtain ⟨ℓ₀, rfl⟩ := QuotientGroup.mk_surjective u
  have hc : ℓ₀ ^ p ∈ center L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hu, pow_orderOf_eq_one]
  obtain ⟨m, hm⟩ := hZ ⟨_, hc⟩
  have hm' : (ℓ₀ ^ p) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hcop : Nat.Coprime (2 ^ m) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨ℓ₀ ^ (2 ^ m * r), ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, ← pow_mod_orderOf, hu, hr, pow_one]
  · have h1 : (ℓ₀ ^ (2 ^ m * r)) ^ p = 1 := by
      rw [← pow_mul, show 2 ^ m * r * p = p * 2 ^ m * r by ring, pow_mul, pow_mul, hm', one_pow]
    have hne : ℓ₀ ^ (2 ^ m * r) ≠ 1 := by
      intro h1'
      have h2 := congrArg (fun g : L => (g : L ⧸ center L)) h1'
      simp only [QuotientGroup.mk_pow, QuotientGroup.mk_one] at h2
      rw [← pow_mod_orderOf, hu, hr, pow_one] at h2
      rw [h2, orderOf_one] at hu
      exact hp.one_lt.ne hu
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ (orderOf_dvd_of_pow_eq_one h1)) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h

theorem commute_of_mk_commute (hZ : IsPGroup 2 ↥(center L)) {ℓ l : L} (hodd : Odd (orderOf ℓ))
    (h : ((ℓ * l : L) : L ⧸ center L) = ((l * ℓ : L) : L ⧸ center L)) : ℓ * l = l * ℓ := by
  set c := ℓ * l * ℓ⁻¹ * l⁻¹ with hcdef
  have hc : c ∈ center L := by
    rw [← QuotientGroup.eq_one_iff, hcdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul]
    group
  have hcl : ℓ * l * ℓ⁻¹ = c * l := by rw [hcdef]; group
  have hpow : ∀ k : ℕ, ℓ ^ k * l * (ℓ ^ k)⁻¹ = c ^ k * l := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc' : ℓ ^ k * c = c * ℓ ^ k := mem_center_iff.mp hc (ℓ ^ k)
      calc ℓ ^ (k + 1) * l * (ℓ ^ (k + 1))⁻¹ = ℓ ^ k * (ℓ * l * ℓ⁻¹) * (ℓ ^ k)⁻¹ := by group
        _ = ℓ ^ k * (c * l) * (ℓ ^ k)⁻¹ := by rw [hcl]
        _ = (ℓ ^ k * c) * l * (ℓ ^ k)⁻¹ := by group
        _ = c * (ℓ ^ k * l * (ℓ ^ k)⁻¹) := by rw [hc']; group
        _ = c ^ (k + 1) * l := by rw [ih, pow_succ']; group
  have hco : c ^ orderOf ℓ = 1 := by
    have := hpow (orderOf ℓ)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at this
    exact (mul_eq_right.mp this.symm)
  obtain ⟨m, hm⟩ := hZ ⟨c, hc⟩
  have hm' : c ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hcop : Nat.Coprime (orderOf ℓ) (2 ^ m) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have hc1 : c = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hco
    have h2 := orderOf_dvd_of_pow_eq_one hm'
    have hd : orderOf c ∣ Nat.gcd (orderOf ℓ) (2 ^ m) := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at hd
    exact orderOf_eq_one_iff.mp hd
  calc ℓ * l = c * (l * ℓ) := by rw [hcdef]; group
    _ = l * ℓ := by rw [hc1, one_mul]

theorem autQuotCenter_conj (ℓ : L) :
    autQuotCenter (MulAut.conj ℓ) = MulAut.conj (ℓ : L ⧸ center L) := by
  ext u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
  rw [autQuotCenter_mk]
  rfl

end Lift

theorem false_of_quotient_center {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
    (hqs : CFSG.IsQuasisimple ↥L) (hZ : IsPGroup 2 ↥(center ↥L)) (hinner : InducesInner z L)
    (hX : KG115Excluded (↥L ⧸ center ↥L)) {A B : Subgroup (MulAut ↥L)}
    (hA : (MulAut.conj : ↥L →* MulAut ↥L).range ≤ A) (hBA : B ≤ A)
    (hBi : ¬ 2 ∣ (B.subgroupOf A).index) (hB : ∃ a : ℕ, Nat.card B = 2 ^ a * 27)
    (hF1 : ∃ x ∈ (MulAut.conj : ↥L →* MulAut ↥L).range, orderOf x = 3 ∧ x ∈ B ∧
      (IsPGroup 2 ↥(Subgroup.center ↥L) → ∃ N : Subgroup (MulAut ↥L),
        N ≤ (MulAut.conj : ↥L →* MulAut ↥L).range ∧ x ∈ N ∧
        B ≤ Subgroup.normalizer (N : Set (MulAut ↥L)) ∧
        ∀ a ∈ (MulAut.conj : ↥L →* MulAut ↥L).range,
          a ∈ Subgroup.normalizer (N : Set (MulAut ↥L)) → a ∈ B) ∧
      B ≤ Subgroup.normalizer ((Subgroup.zpowers x ⊔ pCoreOf 2 B : Subgroup (MulAut ↥L)) :
        Set (MulAut ↥L)))
    (hF2 : ∃ ζ ∈ B, ζ ≠ 1 ∧ (∀ ℓ : ↥L, ((ζ ℓ : ↥L) : G) = z * ℓ * z⁻¹) ∧
      ∀ b ∈ B, b * ζ = ζ * b)
    (hF2p : ∀ ℓ : ↥L, (ℓ : G) * z = z * ℓ → MulAut.conj ℓ ∈ B) : False := by
  have : Group.IsPerfect ↥L := hqs.1
  set X := ↥L ⧸ center ↥L with hXdef
  set φ : MulAut ↥L →* MulAut X := autQuotCenter with hφ
  have hφi : Function.Injective φ := autQuotCenter_injective
  obtain ⟨l, hlL, hl⟩ := hinner
  set l' : ↥L := ⟨l, hlL⟩ with hl'
  obtain ⟨ζ, hζB, hζ1, hζz, hζc⟩ := hF2
  have hζl : ζ = MulAut.conj l' := by
    ext ℓ
    rw [hζz, MulAut.conj_apply]
    have h1 := hl (l * ℓ * l⁻¹) (L.mul_mem (L.mul_mem hlL ℓ.2) (L.inv_mem hlL))
    have h2 : l⁻¹ * (l * ℓ * l⁻¹) * l = (ℓ : G) := by group
    rw [h2] at h1
    change z * ℓ * z⁻¹ = l * ℓ * l⁻¹
    calc z * ℓ * z⁻¹ = z * (z⁻¹ * (l * ℓ * l⁻¹) * z) * z⁻¹ := by rw [h1]
      _ = l * ℓ * l⁻¹ := by group
  have hcz : ∀ ℓ : ↥L, ℓ * l' = l' * ℓ → (ℓ : G) * z = z * ℓ := by
    intro ℓ hℓ
    have h1 := hl ℓ ℓ.2
    have h2 : l⁻¹ * (ℓ : G) * l = ℓ := by
      have := congrArg Subtype.val hℓ
      simp only [coe_mul] at this
      calc l⁻¹ * (ℓ : G) * l = l⁻¹ * ((ℓ : G) * l) := by group
        _ = l⁻¹ * (l * ℓ) := by rw [this]
        _ = ℓ := by group
    rw [h2] at h1
    calc (ℓ : G) * z = z * (z⁻¹ * ℓ * z) := by group
      _ = z * ℓ := by rw [h1]
  refine hX (A.map φ) (B.map φ) (l' : X) ?_ (map_mono hBA) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨u, rfl⟩
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
    exact ⟨MulAut.conj v, hA ⟨v, rfl⟩, autQuotCenter_conj v⟩
  · rwa [← relIndex, relIndex_map_map_of_injective _ _ hφi]
  · rwa [card_map_of_injective hφi]
  · obtain ⟨_, ⟨y, rfl⟩, hy3, hyB, hN, -⟩ := hF1
    obtain ⟨N, hNI, hyN, hBN, hNB⟩ := hN hZ
    have hnorm : ∀ ψ : MulAut ↥L, ψ ∈ normalizer (N : Set (MulAut ↥L)) →
        φ ψ ∈ normalizer ((N.map φ : Subgroup (MulAut X)) : Set (MulAut X)) :=
      fun ψ hψ => le_normalizer_map φ (mem_map_of_mem φ hψ)
    have hnorm' : ∀ ψ : MulAut ↥L,
        φ ψ ∈ normalizer ((N.map φ : Subgroup (MulAut X)) : Set (MulAut X)) →
        ψ ∈ normalizer (N : Set (MulAut ↥L)) := by
      intro ψ hψ
      rw [mem_normalizer_iff] at hψ ⊢
      intro n
      have h1 := hψ (φ n)
      rw [mem_map_iff_mem hφi, ← map_mul, ← map_inv, ← map_mul, mem_map_iff_mem hφi] at h1
      exact h1
    refine ⟨φ (MulAut.conj y), ⟨(y : X), (autQuotCenter_conj y).symm⟩,
      by rw [orderOf_injective φ hφi]; exact hy3, mem_map_of_mem φ hyB, N.map φ, ?_,
      mem_map_of_mem φ hyN, ?_, ?_⟩
    · rintro _ ⟨n, hn, rfl⟩
      obtain ⟨v, rfl⟩ := hNI hn
      exact ⟨(v : X), (autQuotCenter_conj v).symm⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact hnorm b (hBN hb)
    · rintro _ ⟨u, rfl⟩ hu
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
      rw [← autQuotCenter_conj] at hu ⊢
      exact mem_map_of_mem φ (hNB _ ⟨v, rfl⟩ (hnorm' _ hu))
  · rw [← autQuotCenter_conj, ← hζl]
    exact mem_map_of_mem φ hζB
  · intro h1
    apply hζ1
    rw [hζl]
    have : l' ∈ center ↥L := by rwa [← QuotientGroup.eq_one_iff]
    rw [← MonoidHom.mem_ker, ker_conj_eq_center]
    exact this
  · rintro _ ⟨b, hb, rfl⟩
    rw [← autQuotCenter_conj, ← hζl, ← map_mul, ← map_mul, hζc b hb]
  · intro u hu hp hp2
    obtain ⟨ℓ, rfl, hℓ⟩ := exists_lift_orderOf_prime hZ hp hp2 rfl
    have hodd : Odd (orderOf ℓ) := by
      rw [hℓ]
      exact hp.odd_of_ne_two hp2
    have hcomm : ℓ * l' = l' * ℓ :=
      commute_of_mk_commute hZ hodd (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hu])
    rw [← autQuotCenter_conj]
    exact mem_map_of_mem φ (hF2p ℓ (hcz ℓ hcomm))

theorem isPGroup_center_of_quotient {L : Type*} [Group L] [Finite L] (hqs : CFSG.IsQuasisimple L)
    {S : Type*} [Group S] [IsSimpleGroup S] (e : L ⧸ CFSG.pCore 2 L ≃* S) :
    IsPGroup 2 ↥(center L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Nontrivial S := IsSimpleGroup.toNontrivial
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 L))).ker = CFSG.pCore 2 L := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hle : CFSG.pCore 2 L ≤ center L := by
    rw [← hker]
    exact ker_le_center_of_surjective hqs _ (surjective_comp_mk' e)
  have hcard : Nat.card (center L) = Nat.card (CFSG.pCore 2 L) := by
    have h1 := (center L).card_mul_index
    have h2 := (CFSG.pCore 2 L).card_mul_index
    have h3 : (center L).index = (CFSG.pCore 2 L).index := by
      rw [Subgroup.index, Subgroup.index,
        Nat.card_congr (quotientCenterEquivOfQuotient hqs e).toEquiv,
        Nat.card_congr e.toEquiv]
    have hpos : 0 < (center L).index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    rw [h3] at h1
    rw [← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (by rwa [← h3]) h1
  have heq : CFSG.pCore 2 L = center L := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  rw [← heq]
  exact CFSG.pCore_isPGroup

end KG14726

open KG14726

section Certs


theorem kg14726L115C_of (hspor : KG14726L115Spor) (hL2 : KG115L2Input) (hL3 : KG115L3Input)
    (hU3 : KG115U3Input) (hSp4 : KG115Sp4Input) (hG2 : KG115G2Input) (hD4 : KG115D4Input)
    (hF4 : KG115F4Input) (hTits : KG115TitsInput) (hL33 : KG115L33Input)
    (hL2p : KG115L2pInput) (hJ4 : KG115J4Input) : KG14726L115C := by
  intro G _ _ L z hcases hqs h3 A hA B hBA hBi hB hF1 hF2 hF2p _
  have : Group.IsPerfect ↥L := hqs.1
  have hord : ∀ n : ℕ, Nat.card (MulAut (↥L ⧸ center ↥L)) ∣ n → ¬ 27 ∣ n → False :=
    fun n hn h27 => false_of_card_mulAut_dvd (card_mulAut_dvd_of_perfect.trans hn) h27 hB
  have hsimpleCase : IsSimpleGroup ↥L → InducesInner z L → KG115Excluded ↥L → False := by
    intro hs hinner hXL
    have hc : center ↥L = ⊥ := center_eq_bot_of_mulEquiv_simple hqs (MulEquiv.refl _)
    have hZ : IsPGroup 2 ↥(center ↥L) := by
      rw [hc]
      exact IsPGroup.of_bot
    exact false_of_quotient_center hqs hZ hinner
      (kg115Excluded_of_mulEquiv (quotientCenterEquivSelf hc) hXL) hA hBA hBi hB hF1 hF2 hF2p
  rcases hcases with ⟨hsimp, hlie, hinner⟩ | ⟨-, hZ, hm, hinner⟩ | ⟨φ, -, -, -, -⟩ |
    ⟨φ, -, -, -, -⟩ | ⟨hm, hinner⟩ | ⟨⟨s, hs, he₀⟩, ⟨l, hlL, hzl, -⟩⟩
  ·
    have : IsSimpleGroup ↥L := hsimp
    have hc : center ↥L = ⊥ := center_eq_bot_of_mulEquiv_simple hqs (MulEquiv.refl _)
    have eC := quotientCenterEquivSelf hc
    rcases hlie with ((⟨f, h⟩ | h) | ⟨n, hn, h⟩) | he | h
    · rcases h with ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ |
        ⟨hf, hf3, h⟩ | ⟨-, -, h⟩
      · exact hsimpleCase hsimp hinner (hL2 f _ hf h)
      · exact hsimpleCase hsimp hinner (hL3 f _ hf h)
      · exact hsimpleCase hsimp hinner (hU3 f _ hf h)
      · exact hsimpleCase hsimp hinner (hSp4 f _ hf h)
      · exact hsimpleCase hsimp hinner (hG2 f _ hf h)
      · exact hsimpleCase hsimp hinner (hD4 f _ hf h)
      · exact hsimpleCase hsimp hinner (hF4 f _ hf hf3 h)
      · exact absurd h3 (F134.not_three_dvd_card_of_suzukiModel h)
    · exact hsimpleCase hsimp hinner (hTits _ h)
    ·
      obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := h
      let e' : ↥L ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K :=
        eT.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
          (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
            n K))
      refine hord (2 * 9999360) ?_ (by decide)
      rw [card_mulAut_congr eC, card_mulAut_congr e']
      refine (card_mulAut_projectiveSL_dvd' (n := n) (f := 1) (by omega) hK).trans ?_
      rw [mul_one]
      exact Nat.mul_dvd_mul_left 2 (card_GL_dvd_of_card_two (by omega) (hK.trans (by norm_num)))
    ·
      obtain ⟨e⟩ := he
      refine hord 1440 ?_ (by decide)
      rw [card_mulAut_congr eC]
      exact card_mulAut_dvd_of_mulEquiv_alternatingGroup_six e
    ·
      exact false_of_isPSU_three_three hqs h hA hBA hBi hB
  ·
    have hZp : IsPGroup 2 ↥(center ↥L) := by
      rw [hZ]
      exact CFSG.pCore_isPGroup
    have e₁ : ↥L ⧸ center ↥L ≃* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.quotientMulEquivOfEq hZ
    rcases hm with h | h
    · exact false_of_quotient_center hqs hZp hinner
        (kg115Excluded_of_mulEquiv e₁ (hL3 2 _ (by norm_num) h)) hA hBA hBi hB hF1 hF2 hF2p
    · exact false_of_quotient_center hqs hZp hinner
        (kg115Excluded_of_mulEquiv e₁ (hG2 2 _ (by norm_num) h)) hA hBA hBi hB hF1 hF2 hF2p
  ·
    exact hord 1440 (by rw [card_mulAut_congr φ]; exact card_mulAut_alternatingGroup_six_dvd)
      (by decide)
  ·
    exact hord (7 : ℕ).factorial (by rw [card_mulAut_congr φ,
      card_mulAut_alternatingGroup (by norm_num) (by norm_num)]) (by decide)
  ·
    rcases hm with h | ⟨p, hp, h⟩
    · have : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 3 1 h).2
      exact hsimpleCase this hinner (hL33 _ h)
    · have : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 h).2
      exact hsimpleCase this hinner (hL2p p _ hp h)
  ·
    obtain ⟨e₀⟩ := he₀
    by_cases hJ : s = .J4
    · subst hJ
      have : IsSimpleGroup (NativeSporadic.Carrier .J4) := CFSG.Sporadic.J4.isSimpleGroup_J4
      exact false_of_quotient_center hqs (isPGroup_center_of_quotient hqs e₀) ⟨l, hlL, hzl⟩
        (kg115Excluded_of_mulEquiv (quotientCenterEquivOfQuotient hqs e₀) hJ4) hA hBA hBi hB
        hF1 hF2 hF2p
    · refine hspor ↥L s ?_ hqs ⟨e₀⟩ A hA B hBA hBi hB
      unfold IsLemma115SporadicName at hs
      rcases hs with h | h | h | h | h | h | h | h | h | h <;> simp_all

end Certs

end CFSG.Quasithin.H13

end
