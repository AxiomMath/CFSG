module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RTwo
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9ROne

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem normal_eq_factor {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hcen : ∀ a : S, (∀ c, a * c = c * a) → a = 1) {H : Subgroup (S × S)} [H.Normal]
    (hcard : Nat.card H = Nat.card S) (hS : 1 < Nat.card S) :
    H = (⊤ : Subgroup S).prod ⊥ ∨ H = (⊥ : Subgroup S).prod ⊤ := by
  classical
  let H₁ : Subgroup S := H.comap (MonoidHom.inl S S)
  let H₂ : Subgroup S := H.comap (MonoidHom.inr S S)
  haveI : H₁.Normal := ⟨fun n hn g => by
    have := Subgroup.Normal.conj_mem ‹H.Normal› _ hn (MonoidHom.inl S S g)
    simpa [H₁] using this⟩
  haveI : H₂.Normal := ⟨fun n hn g => by
    have := Subgroup.Normal.conj_mem ‹H.Normal› _ hn (MonoidHom.inr S S g)
    simpa [H₂] using this⟩
  have hcardprod : ∀ A B : Subgroup S, Nat.card (A.prod B) = Nat.card A * Nat.card B :=
    fun A B => by rw [Nat.card_congr (Subgroup.prodEquiv A B).toEquiv, Nat.card_prod]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H₁ with h1 | h1
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H₂ with h2 | h2
    · exfalso
      have hH : H = ⊥ := by
        rw [eq_bot_iff]
        rintro ⟨a, b⟩ hab
        have ha : a = 1 := by
          refine hcen a fun c => ?_
          have h3 : ((c, 1) * (a, b) * (c, 1)⁻¹) * (a, b)⁻¹ ∈ H :=
            H.mul_mem (Subgroup.Normal.conj_mem ‹H.Normal› _ hab _) (H.inv_mem hab)
          have h4 : (c * a * c⁻¹ * a⁻¹, (1 : S)) ∈ H := by simpa using h3
          have h5 : c * a * c⁻¹ * a⁻¹ ∈ H₁ := h4
          rw [h1, Subgroup.mem_bot] at h5
          calc a * c = (c * a * c⁻¹ * a⁻¹)⁻¹ * (c * a) * 1 := by group
            _ = c * a := by rw [inv_eq_one.mpr h5]; group
        have hb : b = 1 := by
          refine hcen b fun c => ?_
          have h3 : ((1, c) * (a, b) * (1, c)⁻¹) * (a, b)⁻¹ ∈ H :=
            H.mul_mem (Subgroup.Normal.conj_mem ‹H.Normal› _ hab _) (H.inv_mem hab)
          have h4 : ((1 : S), c * b * c⁻¹ * b⁻¹) ∈ H := by simpa using h3
          have h5 : c * b * c⁻¹ * b⁻¹ ∈ H₂ := h4
          rw [h2, Subgroup.mem_bot] at h5
          calc b * c = (c * b * c⁻¹ * b⁻¹)⁻¹ * (c * b) * 1 := by group
            _ = c * b := by rw [inv_eq_one.mpr h5]; group
        simp [ha, hb]
      rw [hH, Subgroup.card_bot] at hcard
      omega
    · right
      have hle : (⊥ : Subgroup S).prod ⊤ ≤ H := by
        rintro ⟨a, b⟩ hab'
        obtain ⟨ha, hb⟩ := Subgroup.mem_prod.mp hab'
        rw [Subgroup.mem_bot] at ha
        simp only at ha
        subst ha
        have : b ∈ H₂ := by rw [h2]; exact Subgroup.mem_top _
        exact this
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [hcardprod, Subgroup.card_bot, Subgroup.card_top, hcard]
      omega
  · left
    have hle : (⊤ : Subgroup S).prod ⊥ ≤ H := by
      rintro ⟨a, b⟩ hab'
      obtain ⟨ha, hb⟩ := Subgroup.mem_prod.mp hab'
      rw [Subgroup.mem_bot] at hb
      simp only at hb
      subst hb
      have : a ∈ H₁ := by rw [h1]; exact Subgroup.mem_top _
      exact this
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hcardprod, Subgroup.card_bot, Subgroup.card_top, hcard]
    omega

theorem exists_comm_decomp_of_hom {R Y N Q : Subgroup G} {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hcen : ∀ a : S, (∀ c, a * c = c * a) → a = 1) (ψ : ↥R →* S × S)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = N.subgroupOf R) (hYR : Y ≤ R)
    (hnorm : ∀ r ∈ R, conjSubgroup r Y = Y) (hYN : Y ⊓ N ≤ Q)
    (hcard : N.relIndex Y = Nat.card S) (hS : 1 < Nat.card S) :
    ∀ r ∈ R, ∃ y ∈ Y, ∀ y' ∈ Y, ⁅y⁻¹ * r, y'⁆ ∈ Q := by
  classical
  let H : Subgroup (S × S) := (Y.subgroupOf R).map ψ
  have hHn : H.Normal := ⟨fun h hh g => by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨r, rfl⟩ := hψ g
    refine Subgroup.mem_map.mpr ⟨r * y * r⁻¹, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have h1 : (r : G) * (y : G) * (r : G)⁻¹ ∈ conjSubgroup (r : G) Y := by
      rw [mem_conjSubgroup, show (r : G)⁻¹ * ((r : G) * (y : G) * (r : G)⁻¹) * (r : G) = y by
        group]
      exact hy
    rw [hnorm r r.2] at h1
    exact h1⟩
  have hHcard : Nat.card H = Nat.card S := by
    have h1 := Subgroup.relIndex_ker ψ (K := Y.subgroupOf R)
    rw [hker, Subgroup.relIndex_subgroupOf hYR, hcard] at h1
    exact h1.symm
  rcases normal_eq_factor hcen (H := H) hHcard hS with hH | hH
  · intro r hr
    have hmem : ψ ⟨r, hr⟩ = ((ψ ⟨r, hr⟩).1, (ψ ⟨r, hr⟩).2) := rfl
    have h1 : ((ψ ⟨r, hr⟩).1, (1 : S)) ∈ H := by
      rw [hH]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩
    obtain ⟨y, hy, hyψ⟩ := Subgroup.mem_map.mp h1
    refine ⟨(y : G), (Subgroup.mem_subgroupOf.mp hy), fun y' hy' => ?_⟩
    have hy'R : y' ∈ R := hYR hy'
    have hψy' : ψ ⟨y', hYR hy'⟩ ∈ H :=
      Subgroup.mem_map.mpr ⟨⟨y', hYR hy'⟩, Subgroup.mem_subgroupOf.mpr hy', rfl⟩
    rw [hH] at hψy'
    obtain ⟨hc1, hc2⟩ := Subgroup.mem_prod.mp hψy'
    rw [Subgroup.mem_bot] at hc2
    have hu : ψ (y⁻¹ * ⟨r, hr⟩) = (1, (ψ ⟨r, hr⟩).2) := by
      rw [map_mul, map_inv, hyψ]
      ext <;> simp
    have hcomm : ψ ⁅y⁻¹ * ⟨r, hr⟩, ⟨y', hy'R⟩⁆ = 1 := by
      rw [map_commutatorElement, hu, show ψ ⟨y', hy'R⟩ = ((ψ ⟨y', hy'R⟩).1, 1) from
        Prod.ext rfl hc2]
      ext <;> simp [commutatorElement_def]
    have hN : (⁅(y : G)⁻¹ * r, y'⁆ : G) ∈ N := by
      have : ⁅y⁻¹ * ⟨r, hr⟩, ⟨y', hy'R⟩⁆ ∈ ψ.ker := hcomm
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact this
    have hYmem : (⁅(y : G)⁻¹ * r, y'⁆ : G) ∈ Y := by
      have h2 : ((y : G)⁻¹ * r) * y' * ((y : G)⁻¹ * r)⁻¹ ∈ conjSubgroup ((y : G)⁻¹ * r) Y := by
        rw [mem_conjSubgroup, show ((y : G)⁻¹ * r)⁻¹ * (((y : G)⁻¹ * r) * y' *
          ((y : G)⁻¹ * r)⁻¹) * ((y : G)⁻¹ * r) = y' by group]
        exact hy'
      rw [hnorm _ (R.mul_mem (R.inv_mem y.2) hr)] at h2
      have e : ⁅(y : G)⁻¹ * r, y'⁆ = ((y : G)⁻¹ * r * y' * ((y : G)⁻¹ * r)⁻¹) * y'⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact Y.mul_mem h2 (Y.inv_mem hy')
    exact hYN ⟨hYmem, hN⟩
  · intro r hr
    have h1 : ((1 : S), (ψ ⟨r, hr⟩).2) ∈ H := by
      rw [hH]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩
    obtain ⟨y, hy, hyψ⟩ := Subgroup.mem_map.mp h1
    refine ⟨(y : G), (Subgroup.mem_subgroupOf.mp hy), fun y' hy' => ?_⟩
    have hy'R : y' ∈ R := hYR hy'
    have hψy' : ψ ⟨y', hYR hy'⟩ ∈ H :=
      Subgroup.mem_map.mpr ⟨⟨y', hYR hy'⟩, Subgroup.mem_subgroupOf.mpr hy', rfl⟩
    rw [hH] at hψy'
    obtain ⟨hc1, hc2⟩ := Subgroup.mem_prod.mp hψy'
    rw [Subgroup.mem_bot] at hc1
    have hu : ψ (y⁻¹ * ⟨r, hr⟩) = ((ψ ⟨r, hr⟩).1, 1) := by
      rw [map_mul, map_inv, hyψ]
      ext <;> simp
    have hcomm : ψ ⁅y⁻¹ * ⟨r, hr⟩, ⟨y', hy'R⟩⁆ = 1 := by
      rw [map_commutatorElement, hu, show ψ ⟨y', hy'R⟩ = (1, (ψ ⟨y', hy'R⟩).2) from
        Prod.ext hc1 rfl]
      ext <;> simp [commutatorElement_def]
    have hN : (⁅(y : G)⁻¹ * r, y'⁆ : G) ∈ N := by
      have : ⁅y⁻¹ * ⟨r, hr⟩, ⟨y', hy'R⟩⁆ ∈ ψ.ker := hcomm
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact this
    have hYmem : (⁅(y : G)⁻¹ * r, y'⁆ : G) ∈ Y := by
      have h2 : ((y : G)⁻¹ * r) * y' * ((y : G)⁻¹ * r)⁻¹ ∈ conjSubgroup ((y : G)⁻¹ * r) Y := by
        rw [mem_conjSubgroup, show ((y : G)⁻¹ * r)⁻¹ * (((y : G)⁻¹ * r) * y' *
          ((y : G)⁻¹ * r)⁻¹) * ((y : G)⁻¹ * r) = y' by group]
        exact hy'
      rw [hnorm _ (R.mul_mem (R.inv_mem y.2) hr)] at h2
      have e : ⁅(y : G)⁻¹ * r, y'⁆ = ((y : G)⁻¹ * r * y' * ((y : G)⁻¹ * r)⁻¹) * y'⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact Y.mul_mem h2 (Y.inv_mem hy')
    exact hYN ⟨hYmem, hN⟩

theorem center_eq_one_of_simple {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {q : ℕ}
    (h4 : 4 ≤ q) (hq : Nat.card S = q * (q ^ 2 - 1)) :
    ∀ a : S, (∀ c, a * c = c * a) → a = 1 := by
  intro a ha
  by_contra hne
  have hcent : a ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr fun c => (ha c).symm
  have hctop : Subgroup.center S = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S)).resolve_left fun h =>
      hne (by rw [h] at hcent; exact Subgroup.mem_bot.mp hcent)
  letI : CommGroup S := Group.commGroupOfCenterEqTop hctop
  have hp := IsSimpleGroup.prime_card (α := S)
  rw [hq] at hp
  have hq1 : q ≠ 1 := by omega
  have hq2' : q ^ 2 - 1 ≠ 1 := by
    have : 16 ≤ q ^ 2 := by nlinarith
    omega
  exact Nat.not_prime_mul hq1 hq2' hp

theorem exists_comm_decomp_omegaPlus (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {x : G} (hxL : x ∈ LB M Q B)
    (hxQ : x ∉ Q) {Y : Subgroup G} (hQY : Q ≤ Y) (hYR : Y ≤ Rt M (LB M Q B) x)
    (hnorm : ∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r Y = Y)
    (hYsl : QuotSat Y Q (IsSLModel 2 (Nat.card Z))) (hII : OmegaPlusNat hc x 2) :
    ∀ r ∈ Rt M (LB M Q B) x, ∃ y ∈ Y, ∀ y' ∈ Y, ⁅y⁻¹ * r, y'⁆ ∈ Q := by
  classical
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hqev : 2 ∣ Nat.card Z := by
    obtain ⟨s, hs'⟩ := hq2
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hs'
      omega
    rw [hs']
    exact dvd_pow_self 2 hs0
  have hN2 : IsPGroup 2 ↥(hc.CN x) := isPGroup_CN h34 h311a hs hxL hxQ
  have hNR : hc.CN x ≤ Rt M (LB M Q B) x := fun y hy => (Ctx.mem_CN.mp hy).1
  have hQN : Q ≤ hc.CN x := hc.Q_le_CN hxL
  obtain ⟨hYQn, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := isSLModel_two_data hq4 hq2 hYmod
  have hQYidx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  have hYN : Y ⊓ hc.CN x ≤ Q := by
    by_contra hnot
    have hK := eq_of_normal_of_ne_Q (Y := Y) (Q := Q) (K := Y ⊓ hc.CN x) hq4 hq2
      ⟨hYQn, hYmod⟩ (le_inf hQY hQN) inf_le_left (fun y hy k hk =>
        ⟨Y.mul_mem (Y.mul_mem hy hk.1) (Y.inv_mem hy), hc.CN_conj_mem hxL (hYR hy) hk.2⟩) hnot
    have hYN' : Y ≤ hc.CN x := hK ▸ inf_le_right
    obtain ⟨k, hk⟩ := relIndex_two_pow_of_isPGroup Q (hN2.to_le hYN')
    exact not_two_pow_mul_sq_sub_one hq4 hqev ⟨k, hQYidx ▸ hk⟩
  have hNYQ : hc.CN x ⊓ Y = Q := by
    refine le_antisymm (fun z hz => hYN ⟨hz.2, hz.1⟩) (le_inf hQN hQY)
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, -⟩ := hII
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hK4 : 4 ≤ Nat.card K := hK ▸ hq4
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K hK4
  haveI := isSimpleGroup_statedSL_two (statedSL_quasisimple_of_card 2 K le_rfl hK4)
  have hScard : Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
    card_statedSL_two K
  have hcen := center_eq_one_of_simple (S := ↥(StatedSL 2 K)) hK4 hScard
  have hmemΩ : ∀ r : ↥(Rt M (LB M Q B) x), φ r ∈ StatedOmega (StatedQuadPlus 2 K) := fun r => by
    rw [← hφ]
    exact MonoidHom.mem_range.mpr ⟨r, rfl⟩
  let φ' : ↥(Rt M (LB M Q B) x) →* ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    φ.codRestrict (StatedOmega (StatedQuadPlus 2 K)) hmemΩ
  let ψ : ↥(Rt M (LB M Q B) x) →* ↥(StatedSL 2 K) × ↥(StatedSL 2 K) := e.toMonoidHom.comp φ'
  have hψ : Function.Surjective ψ := by
    intro p
    have hw : ((e.symm p : ↥(StatedOmega (StatedQuadPlus 2 K))) : GL (Fin 2 ⊕ Fin 2) K) ∈
        φ.range := by
      rw [hφ]
      exact (e.symm p).2
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp hw
    refine ⟨r, ?_⟩
    have : φ' r = e.symm p := Subtype.ext hr
    show e (φ' r) = p
    rw [this, MulEquiv.apply_symm_apply]
  have hψker : ψ.ker = (hc.CN x).subgroupOf (Rt M (LB M Q B) x) := by
    ext r
    rw [← hker, MonoidHom.mem_ker, MonoidHom.mem_ker]
    show e (φ' r) = 1 ↔ φ r = 1
    rw [MulEquiv.map_eq_one_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcard : (hc.CN x).relIndex Y = Nat.card ↥(StatedSL 2 K) := by
    rw [← Subgroup.inf_relIndex_right (hc.CN x) Y, hNYQ, hQYidx, hScard, hK]
  intro r hr
  exact exists_comm_decomp_of_hom hcen ψ hψ hψker hYR hnorm hYN hcard
    (by
      rw [hScard]
      have h16 : 16 ≤ Nat.card K ^ 2 := by nlinarith
      calc 1 < 4 * 15 := by norm_num
        _ ≤ Nat.card K * (Nat.card K ^ 2 - 1) := Nat.mul_le_mul hK4 (by omega)) r hr

theorem exists_comm_decomp (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h1 : OneConcl hc X Y) {x : G} (hx : x ∈ LB M Q B ⊓ X)
    (hxQ : x ∉ Q) {r : G} (hr : r ∈ Rt M (LB M Q B) x) :
    ∃ y ∈ Y, ∀ y' ∈ Y, ⁅y⁻¹ * r, y'⁆ ∈ Q := by
  obtain ⟨hea, hnorme, hdich, -⟩ := h1 x hx hxQ
  have hsplit' := hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  rcases hdich with hI | hII
  · have hY : Y ≤ Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G) :=
      normalizer_of_commutator_le (X := LB M Q B ⊓ X) (Y := Y) (le_inf le_sup_left hQX)
        fun a ha y hy => hcXY a ha.2 y hy
    have hr' : r ∈ Y ⊔ (LB M Q B ⊓ X) := by rw [sup_comm, ← hI]; exact hr
    obtain ⟨y, hy, a, ha, hya⟩ := exists_mul_of_mem_sup_of_le_normalizer hY hr'
    refine ⟨y, hy, fun y' hy' => ?_⟩
    have : y⁻¹ * r = a := by rw [← hya]; group
    rw [this]
    exact hcXY a ha.2 y' hy'
  · exact exists_comm_decomp_omegaPlus h34 h311a hc hs hx.1 hxQ hQY (le_sup_right.trans hea)
      hnorme hYsl hII r hr

theorem three_caseA (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) (h1 : OneConcl hc X Y)
    {g : G} (hg : g ∈ M)
    (hF : ∀ f ∈ conjSubgroup g (LB M Q B ⊓ X), ∀ e ∈ LB M Q B ⊓ X,
      ⁅f, e⁆ ∈ conjSubgroup g (LB M Q B ⊓ X) ⊓ (LB M Q B ⊓ X))
    {e₁ : G} (he₁F : e₁ ∈ conjSubgroup g (LB M Q B ⊓ X)) (he₁E : e₁ ∈ LB M Q B ⊓ X)
    (he₁Q : e₁ ∉ Q) : conjSubgroup g (LB M Q B ⊓ X) = LB M Q B ⊓ X := by
  classical
  have hs5 := hs.toSec5
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hQE : Q ≤ LB M Q B ⊓ X := le_inf hQL hQX
  have hLM : LB M Q B ≤ M := hc.LB_le_M
  have hQM : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := fun m hm q hq =>
    (Subgroup.mem_normalizer_iff.mp (hQn hm) q).mp hq
  have he₀ : g⁻¹ * e₁ * g ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp he₁F
  have he₀Q : g⁻¹ * e₁ * g ∉ Q := fun h => he₁Q (by
    have := hQM g hg _ h
    simpa [mul_assoc] using this)
  have hgY : conjSubgroup g Y = Y := conj_Y_eq_of_conj_mem hc hsplit0 h1 he₀ he₀Q hg (by
    rw [show g * (g⁻¹ * e₁ * g) * g⁻¹ = e₁ by group]
    exact he₁E)
  have he₁Lg : e₁ ∈ conjSubgroup g (LB M Q B) :=
    (Subgroup.map_mono (inf_le_left : LB M Q B ⊓ X ≤ LB M Q B)) he₁F
  obtain ⟨s, hsR, hconj⟩ := exists_Rt_conj_of_mem h34 h311a hc hs hsplit0 h4 h1 he₁E he₁Q hg he₁Lg
  have hsM : s ∈ M := hc.Rt_le_M e₁ hsR
  have hhL : conjSubgroup (s⁻¹ * g) (LB M Q B) = LB M Q B := by
    rw [conjSubgroup_mul, hconj, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hhM : s⁻¹ * g ∈ M := M.mul_mem (M.inv_mem hsM) hg
  have hhY := conj_Y_eq_of_normalizes_LB h34 hc hs hsplit0 h4 h1 hhM hhL
  have hhE : ∀ z ∈ conjSubgroup (s⁻¹ * g) (LB M Q B ⊓ X), z ∈ LB M Q B ⊓ X := by
    intro z hz
    have hzL : z ∈ LB M Q B := by
      have : z ∈ conjSubgroup (s⁻¹ * g) (LB M Q B) :=
        (Subgroup.map_mono (inf_le_left : LB M Q B ⊓ X ≤ LB M Q B)) hz
      rwa [hhL] at this
    refine ⟨hzL, mem_X_of_comm_mem_Q hc hsplit0 h4 hzL fun y hy => ?_⟩
    have hy' : (s⁻¹ * g)⁻¹ * y * (s⁻¹ * g) ∈ Y := by
      have : y ∈ conjSubgroup (s⁻¹ * g) Y := by rw [hhY]; exact hy
      exact mem_conjSubgroup.mp this
    have hz' : (s⁻¹ * g)⁻¹ * z * (s⁻¹ * g) ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp hz
    have e : ⁅z, y⁆ = (s⁻¹ * g) * ⁅(s⁻¹ * g)⁻¹ * z * (s⁻¹ * g), (s⁻¹ * g)⁻¹ * y * (s⁻¹ * g)⁆ *
        (s⁻¹ * g)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hQM _ hhM _ (hcXY _ hz'.2 _ hy')
  obtain ⟨y, hy, hu⟩ := exists_comm_decomp h34 h311a hc hs hsplit0 h1 he₁E he₁Q hsR
  have hyM : y ∈ M := hc.Rt_le_M t (hYR hy)
  obtain ⟨u, hu_def⟩ : ∃ u : G, u = y⁻¹ * s := ⟨_, rfl⟩
  have huM : u ∈ M := by rw [hu_def]; exact M.mul_mem (M.inv_mem hyM) hsM
  have hu' : ∀ y' ∈ Y, ⁅u, y'⁆ ∈ Q := by rw [hu_def]; exact hu
  let C := centMod M Q Y hQn
  have hEC : ∀ e ∈ LB M Q B ⊓ X, e ∈ C := fun e he =>
    ⟨hLM he.1, fun y' hy' => hcXY e he.2 y' hy'⟩
  have huC : u ∈ C := ⟨huM, hu'⟩
  have hFC : ∀ z ∈ conjSubgroup u (LB M Q B ⊓ X), z ∈ C := by
    intro z hz
    have h0 : u⁻¹ * z * u ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp hz
    have hz' : z = u * (u⁻¹ * z * u) * u⁻¹ := by group
    rw [hz']
    exact C.mul_mem (C.mul_mem huC (hEC _ h0)) (C.inv_mem huC)
  have hQu : Q ≤ conjSubgroup u (LB M Q B ⊓ X) := by
    intro q hq
    rw [mem_conjSubgroup]
    exact hQE (by
      have := hQM u⁻¹ (M.inv_mem huM) q hq
      simpa using this)
  have hFle : conjSubgroup g (LB M Q B ⊓ X) ≤ conjSubgroup u (LB M Q B ⊓ X) := by
    intro f hf
    have hfe : g⁻¹ * f * g ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp hf
    have he' : (s⁻¹ * g) * (g⁻¹ * f * g) * (s⁻¹ * g)⁻¹ ∈ LB M Q B ⊓ X := by
      apply hhE
      rw [mem_conjSubgroup, show (s⁻¹ * g)⁻¹ * ((s⁻¹ * g) * (g⁻¹ * f * g) * (s⁻¹ * g)⁻¹) *
        (s⁻¹ * g) = g⁻¹ * f * g by group]
      exact hfe
    obtain ⟨e', he'_def⟩ : ∃ e' : G, e' = (s⁻¹ * g) * (g⁻¹ * f * g) * (s⁻¹ * g)⁻¹ := ⟨_, rfl⟩
    rw [← he'_def] at he'
    have hf_eq : f = y * (u * e' * u⁻¹) * y⁻¹ := by
      rw [he'_def, hu_def]; group
    have hw : u * e' * u⁻¹ ∈ C := C.mul_mem (C.mul_mem huC (hEC _ he')) (C.inv_mem huC)
    have hcomm : ⁅y, u * e' * u⁻¹⁆ ∈ Q := by
      have := hw.2 y hy
      rw [← commutatorElement_inv]
      exact Q.inv_mem this
    have hfe2 : f = ⁅y, u * e' * u⁻¹⁆ * (u * e' * u⁻¹) := by
      rw [hf_eq]
      simp only [commutatorElement_def]
      group
    rw [hfe2]
    refine Subgroup.mul_mem _ (hQu hcomm) (mem_conjSubgroup.mpr ?_)
    rw [show u⁻¹ * (u * e' * u⁻¹) * u = e' by group]
    exact he'
  have hFeq : conjSubgroup g (LB M Q B ⊓ X) = conjSubgroup u (LB M Q B ⊓ X) :=
    Subgroup.eq_of_le_of_card_ge hFle (by rw [card_conjSubgroup, card_conjSubgroup])
  have hnormEY : (LB M Q B ⊓ X) ≤ Subgroup.normalizer ((LB M Q B ⊓ Y : Subgroup G) : Set G) :=
    normalizer_of_commutator_le (X := LB M Q B ⊓ Y) (Y := LB M Q B ⊓ X)
      (le_inf hQL hQY) fun a ha y hy => by
        have := Q.inv_mem (hcXY y hy.2 a ha.2)
        rwa [commutatorElement_inv] at this
  have hFN : ∀ f ∈ conjSubgroup g (LB M Q B ⊓ X), f ∈ Subgroup.normalizer (LB M Q B : Set G) := by
    intro f hf
    refine Subgroup.mem_normalizer_fintype fun l hl => ?_
    have hLeq : l ∈ (LB M Q B ⊓ X) ⊔ (LB M Q B ⊓ Y) := h4.2.2 ▸ hl
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_normalizer hnormEY hLeq
    rw [← hab]
    have hfC : f ∈ C := hFC f (hFeq ▸ hf)
    have h1' : f * a * f⁻¹ ∈ LB M Q B ⊓ X := by
      have h0 := (hF f hf a ha).2
      have e : f * a * f⁻¹ = ⁅f, a⁆ * a := by simp only [commutatorElement_def]; group
      rw [e]
      exact (LB M Q B ⊓ X).mul_mem h0 ha
    have h2' : f * b * f⁻¹ ∈ LB M Q B := by
      have e : f * b * f⁻¹ = ⁅f, b⁆ * b := by simp only [commutatorElement_def]; group
      rw [e]
      exact (LB M Q B).mul_mem (hQL (hfC.2 b hb.2)) hb.1
    have e2 : f * (a * b) * f⁻¹ = (f * a * f⁻¹) * (f * b * f⁻¹) := by group
    rw [e2]
    exact (LB M Q B).mul_mem h1'.1 h2'
  have hconjN : conjSubgroup u (LB M Q B) ≤ Subgroup.normalizer (LB M Q B : Set G) := by
    intro z hz
    have hl : u⁻¹ * z * u ∈ LB M Q B := mem_conjSubgroup.mp hz
    have hLeq : u⁻¹ * z * u ∈ (LB M Q B ⊓ X) ⊔ (LB M Q B ⊓ Y) := h4.2.2 ▸ hl
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_normalizer hnormEY hLeq
    have hz_eq : z = (u * a * u⁻¹) * (u * b * u⁻¹) := by
      have h0 : z = u * (u⁻¹ * z * u) * u⁻¹ := by group
      rw [h0, ← hab]
      group
    rw [hz_eq]
    refine Subgroup.mul_mem _ ?_ ?_
    · refine hFN _ ?_
      rw [hFeq]
      exact mem_conjSubgroup.mpr (by rw [show u⁻¹ * (u * a * u⁻¹) * u = a by group]; exact ha)
    · have e : u * b * u⁻¹ = ⁅u, b⁆ * b := by simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.le_normalizer ((LB M Q B).mul_mem (hQL (hu' b hb.2)) hb.1)
  have hwc := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).1 u huM hconjN
  have hFE : conjSubgroup u (LB M Q B ⊓ X) ≤ LB M Q B ⊓ X := by
    intro z hz
    have hzL : z ∈ LB M Q B := by
      have : z ∈ conjSubgroup u (LB M Q B) :=
        (Subgroup.map_mono (inf_le_left : LB M Q B ⊓ X ≤ LB M Q B)) hz
      rwa [hwc] at this
    exact ⟨hzL, mem_X_of_comm_mem_Q hc hsplit0 h4 hzL fun y' hy' => (hFC z hz).2 y' hy'⟩
  exact Subgroup.eq_of_le_of_card_ge (hFeq ▸ hFE) (by rw [card_conjSubgroup])

end HS9

@[expose] def Sec97ThreeCaseB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y → HS9.TwoConcl M Q B X →
      ∀ g ∈ M, conjSubgroup g (LB M Q B ⊓ X) ⊓ (LB M Q B ⊓ X) ≤ Q →
        (∀ f ∈ conjSubgroup g (LB M Q B ⊓ X), ∀ e ∈ LB M Q B ⊓ X, ⁅f, e⁆ ∈ Q) → False

theorem sec97Three_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hB : Sec97ThreeCaseB) : Sec97ThreeStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 h1 h2 g hg hF
  by_cases hA : conjSubgroup g (LB M Q B ⊓ X) ⊓ (LB M Q B ⊓ X) ≤ Q
  · exact (hB G M Q Z B hc n t hs X Y hsplit h4 h1 h2 g hg hA fun f hf e he =>
      hA (hF f hf e he)).elim
  · obtain ⟨e₁, he₁, he₁Q⟩ :
        ∃ e₁ ∈ conjSubgroup g (LB M Q B ⊓ X) ⊓ (LB M Q B ⊓ X), e₁ ∉ Q := by
      by_contra hno
      push Not at hno
      exact hA fun x hx => hno x hx
    exact HS9.three_caseA h34 h311a hc hs hsplit h4 h1 hg hF he₁.1 he₁.2 he₁Q

end CFSG.RankThree.GF2n.Stroth80
