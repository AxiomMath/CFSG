module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Coord
public import CFSG.Quasithin.Vol2.Ch11G2Q8TwelveDefs
public import CFSG.Quasithin.Vol2.Ch11G2Q8OffReal
public import CFSG.Quasithin.Vol2.Ch11G2Q8OffCore
public import CFSG.Quasithin.Vol2.Ch11SecA14Delta

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (pCoreOf_map_of_injective)
open scoped IsMulCommutative

variable {K : Type} [Field K] [CharP K 2]

theorem autOn_pCoreOf_le_G2 {G : Type} [Group G] [Finite G] (X V : Subgroup G) :
    autOn (pCoreOf 2 X) V ≤ pCoreOf 2 (autOn X V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (A4.autOn_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 X)) ?_
    (B6.isPGroup_autOn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) V)
  have key : ∀ b ∈ autOn X V, ∀ c ∈ autOn (pCoreOf 2 X) V,
      b * c * b⁻¹ ∈ autOn (pCoreOf 2 X) V := by
    intro b hb c hc
    obtain ⟨y, hy, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hb
    obtain ⟨z, hz, hzV, rfl⟩ := SecA.mem_autOn_iff.mp hc
    rw [SecA.conjV_conj]
    exact SecA.conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hy) z).mp hz) _
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact key a ha c
  · intro hc
    have h1 := key a⁻¹ ((autOn X V).inv_mem ha) _ hc
    rwa [show a⁻¹ * (a * c * a⁻¹) * a⁻¹⁻¹ = c by group] at h1

theorem qr_Z1 {z : ↥(cayleyGroup K)} (hz : z ∈ Z1 K) (x : Ix3 → K) : qr z x = 0 := by
  obtain ⟨v, rfl⟩ := hz
  conv_lhs => rw [q6_eta x]
  simp only [qr, g2Act_g2A_uSL, polarQ, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2,
    q6_apply_inr0, q6_apply_inr1, q6_apply_inr2]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (x (.inl 0) * x (.inr 0) + x (.inl 1) * x (.inr 1) + x (.inl 2) * x (.inr 2) +
    v.1 * x (.inl 1) * x (.inr 0) + v.2 * x (.inl 2) * x (.inr 0)) * h2

theorem factG2TwelveCent_holds : FactG2TwelveCent := by
  intro G _ _ L V X T V₁ V₃ n hV hn hLV hVL hnat hkind hCV hLX hXN hTS hTV hTL hCV₁ h13 h3V
    hst₁ hst₃ hidx₁ hidx₃ hTV₁ hTV₃ A hAR hA
  obtain ⟨_, K, _, _, _, hK, π, f, hf, c₀, hc0, hc1, g, -, hflag⟩ :=
    exists_coord_G2 hV hn hLV hnat hkind hTS hTL
  have hV₁ := hflag (i := 1) (h13.trans h3V) hCV₁ hst₁ (by rw [hidx₁, mul_one]) hTV₁
  have hV₃ := hflag (i := 3) h3V (hCV₁.trans h13) hst₃ hidx₃ hTV₃
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_cayleyGroup (F := K)
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have h4 := four_le_card hn hK
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : ((a * b⁻¹ : ↥V) : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨(a * b⁻¹).2, (hf.eq_iff a b).mp hab⟩
    rw [hCV, Subgroup.mem_bot] at h1
    exact mul_inv_eq_one.mp (Subtype.ext h1)
  have hsurj : Function.Surjective f := hf.surj
  have hL1T : LOf L V₁ ⊔ T ≤ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.normalizer (V₁ : Set G) := by
    refine sup_le (le_inf ?_ ?_) (le_inf hTV hTV₁)
    · exact ((perfectCore_le _).trans inf_le_left).trans hLV
    · exact (perfectCore_le _).trans inf_le_right
  have hRL : pCoreOf 2 (LOf L V₁ ⊔ T) ≤ LOf L V₁ ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAR.trans (hRL.trans (hL1T.trans inf_le_left))
  obtain ⟨hĀX, hĀne, ⟨hĀc, hĀ2⟩, hĀP⟩ := hA
  have hĀX' : autOn A V ≤ autOn X V := hĀX
  have hĀ1 : ∀ φ ∈ autOn A V, φ * φ = 1 := fun φ hφ => by
    rw [← sq]
    exact hĀ2 φ hφ
  have hk1 : Nat.card K < 2 ^ (2 * n - 1) := by
    rw [hK]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hk2 : Nat.card K ^ 2 ≤ 2 * 2 ^ (2 * n - 1) := by
    rw [hK, ← pow_mul, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hPĀ : ∀ B ≤ autOn A V, Nat.card ↥(autOn A V) < 2 ^ (2 * n - 1) * Nat.card ↥B →
      ∀ v : ↥V, (∀ b ∈ B, b v = v) → ∀ φ ∈ autOn A V, φ v = v := by
    intro B hB hcard v hv φ hφ
    have h1 := Subgroup.relIndex_mul_card (H := B) (K := autOn A V)
    rw [inf_of_le_left hB] at h1
    have hidx : B.relIndex (autOn A V) < 2 ^ (2 * n - 1) := by
      by_contra hge
      have h3 := Nat.mul_le_mul_right (Nat.card ↥B) (not_lt.mp hge)
      rw [h1] at h3
      omega
    have hm : E3.mQuot (autOn A V) B < 2 * n - 1 := by
      have h0 : B.relIndex (autOn A V) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h1
        exact Nat.card_pos.ne' h1.symm
      exact (padicValNat_le_nat_log _).trans_lt (Nat.log_lt_of_lt_pow h0 hidx)
    have h4 := hĀP B hB hm
    have h3 : v ∈ fixV (V := IntMod V hV) B := fun b hb => hv b hb
    rw [h4] at h3
    exact h3 φ hφ
  obtain ⟨Φ, hΦinj, hΦ⟩ := exists_g2Hom_of_fixStable hf hfinj hsq hc0 hc1 hK hn hXN hĀX' hĀ1
    hk1 hPĀ
  have hΓ1 : ∀ γ ∈ Φ.range, γ * γ = 1 := by
    rintro _ ⟨φ, rfl⟩
    rw [← map_mul, show φ * φ = 1 from Subtype.ext (hĀ1 φ φ.2), map_one]
  have hΓc : ∀ γ ∈ Φ.range, ∀ δ ∈ Φ.range, γ * δ = δ * γ := by
    rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩
    rw [← map_mul, ← map_mul, show φ * ψ = ψ * φ from
      Subtype.ext (hĀc (φ : MulAut ↥V) φ.2 (ψ : MulAut ↥V) ψ.2)]
  have hΓne : Φ.range ≠ ⊥ := by
    intro h
    apply hĀne
    rw [eq_bot_iff]
    intro φ hφ
    have h1 : Φ ⟨φ, hφ⟩ ∈ Φ.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one Φ] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hΦinj h1))
  have hPΓ : FixStable (2 ^ (2 * n - 1)) Φ.range := by
    intro B hB hcard w hw γ hγ
    have hcB : Nat.card ↥((B.comap Φ).map (autOn A V).subtype) = Nat.card ↥B := by
      rw [Subgroup.card_map_of_injective Subtype.val_injective]
      have hmap : (B.comap Φ).map Φ = B := Subgroup.map_comap_eq_self (hB.trans le_rfl)
      rw [← hmap, Subgroup.card_map_of_injective hΦinj, hmap]
    have hcΓ : Nat.card ↥Φ.range = Nat.card ↥(autOn A V) := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hΦinj, Subgroup.card_top]
    obtain ⟨v, rfl⟩ := hsurj w
    have h1 := hPĀ _ (Subgroup.map_subtype_le _) (by rw [hcB, ← hcΓ]; exact hcard) v (by
      rintro _ ⟨φ, hφ, rfl⟩
      apply hfinj
      rw [Subgroup.coe_subtype, hΦ, hw _ hφ])
    obtain ⟨φ, rfl⟩ := hγ
    rw [← hΦ, h1 φ φ.2]
  obtain ⟨x, hxle, -⟩ := exists_conj_le_A1 hK (by omega) hk1 hk2 hΓ1 hΓc hΓne hPΓ
  have hL1 : autOn (LOf L V₁) V = (stabV0 K).map (psiG hc0 hc1 π g) := by
    rw [SecA.autOn_lOf hLV (h13.trans h3V), hV₁]
    exact gammaW_one_eqG h4 hf hc0 hc1 g
  have hψ := psiG_injective hf hc0 hc1 g
  have hpsi : ∀ γ : ↥(cayleyGroup K), ∀ w : ↥V,
      f ((psiG hc0 hc1 π g γ : MulAut ↥V) w) = g2Act (g * γ * g⁻¹) (f w) := fun γ w => by
    rw [psiG_apply, IsCoord.actG hf hc0 hc1]
  have hconjR : ∀ φ : ↥(autOn A V), g⁻¹ * Φ φ * g ∈ pCoreOf 2 (stabV0 K) := by
    intro φ
    have hψφ : psiG hc0 hc1 π g (g⁻¹ * Φ φ * g) = (φ : MulAut ↥V) := by
      refine MulEquiv.ext fun w => hfinj ?_
      rw [hpsi, hΦ, show g * (g⁻¹ * Φ φ * g) * g⁻¹ = Φ φ by group]
    have hφR : (φ : MulAut ↥V) ∈ autOn (LOf L V₁ ⊔ T) V :=
      A4.autOn_mono hRL (A4.autOn_mono hAR φ.2)
    have hφV₁ : (φ : MulAut ↥V) ∈ SecA.stabW (V₁.subgroupOf V) := by
      obtain ⟨y, hy, hyV, hφy⟩ := SecA.mem_autOn_iff.mp hφR
      rw [hφy]
      exact (SecA.conjV_mem_stabW_iff (h13.trans h3V) hyV).mpr (hL1T hy).2
    have hS : g⁻¹ * Φ φ * g ∈ stabV0 K := by
      obtain ⟨v₀, hv₀⟩ := hsurj (g2Act g (eu 0 1))
      have hv₀V : v₀ ∈ V₁.subgroupOf V := by
        rw [hV₁]
        exact mem_gmapG_stdF_one_iff.mpr ⟨1, by rw [hv₀, one_smul]⟩
      have h1 := (SecA.mem_stabW.mp hφV₁ v₀).mp hv₀V
      rw [hV₁] at h1
      change f ((φ : MulAut ↥V) v₀) ∈ gmapG g (stdF K 1) at h1
      obtain ⟨t, ht⟩ := mem_gmapG_stdF_one_iff.mp h1
      rw [hΦ, hv₀] at ht
      have h2 : g2Act (Φ φ) (g2Act (Φ φ) (g2Act g (eu 0 1))) = g2Act g (eu 0 1) := by
        rw [← g2Act_mul_apply, ← map_mul, show φ * φ = 1 from Subtype.ext (hĀ1 φ φ.2),
          map_one, map_one]
        rfl
      rw [ht, g2Act_smul, ht, smul_smul] at h2
      have h3 : t * t = 1 := by
        have h5 := congrFun (congrArg (g2Act g⁻¹) h2) (.inl 0)
        rw [g2Act_smul, g2Act_inv_apply] at h5
        simpa using h5
      have ht1 : t = 1 := eq_of_mul_self_eq_charTwo (by rw [h3, one_mul])
      rw [ht1, one_smul] at ht
      show g2Act (g⁻¹ * Φ φ * g) (eu 0 1) = eu 0 1
      rw [g2Act_mul_apply, g2Act_mul_apply, ht, g2Act_inv_apply]
    have hφL1 : (φ : MulAut ↥V) ∈ autOn (LOf L V₁) V := by
      rw [hL1, ← hψφ]
      exact ⟨_, hS, rfl⟩
    have hmem : (φ : MulAut ↥V) ∈ pCoreOf 2 (autOn (LOf L V₁) V) :=
      F7.pCoreOf_inf_le (A4.autOn_mono le_sup_left)
        ⟨autOn_pCoreOf_le_G2 _ V (A4.autOn_mono hAR φ.2), hφL1⟩
    rw [hL1, pCoreOf_map_of_injective _ hψ] at hmem
    obtain ⟨γ, hγ, hγeq⟩ := hmem
    rwa [← hψ (hγeq.trans hψφ.symm)]
  have hfixF3 : ∀ φ : ↥(autOn A V), ∀ w ∈ stdF K 3, g2Act (Φ φ) (g2Act g w) = g2Act g w := by
    have hlong : ∀ φ' : ↥(autOn A V), x⁻¹ * Φ φ' * x ∈ Z1 K → ∀ w ∈ stdF K 3,
        g2Act (Φ φ') (g2Act g w) = g2Act g w := by
      intro φ' hZ w hw
      have hq0 : ∀ t, qr (g⁻¹ * Φ φ' * g) t = 0 := by
        intro t
        have h1 := qr_conj (g⁻¹ * x) (x⁻¹ * Φ φ' * x) (g2Act (g⁻¹ * x)⁻¹ t)
        rw [g2Act_apply_inv, qr_Z1 hZ,
          show g⁻¹ * x * (x⁻¹ * Φ φ' * x) * (g⁻¹ * x)⁻¹ = g⁻¹ * Φ φ' * g by group] at h1
        exact h1
      obtain ⟨hcS, hcM⟩ := mem_pCoreOf_stabV0_iff.mp (hconjR φ')
      obtain ⟨α, β, γ, p, q', hceq⟩ := eq_of_levi1Mat_eq_one hcS hcM
      rw [hceq] at hq0
      obtain ⟨rfl, rfl, rfl⟩ := kerElt_eq_of_qr_zero hq0
      have h1 := kerElt_mem_A1 (0 : K) p q' w hw
      rw [← hceq, g2Act_mul_apply, g2Act_mul_apply] at h1
      have h3 := congrArg (g2Act g) h1
      rwa [g2Act_apply_inv] at h3
    have hPΔ := fixStable_map_conj hPΓ x⁻¹
    have hcardΔ := card_le_mul_card_inf_Z1 hxle
    have hlt : Nat.card ↥(Φ.range.map (MulAut.conj x⁻¹).toMonoidHom) <
        2 ^ (2 * n - 1) * Nat.card ↥(Φ.range.map (MulAut.conj x⁻¹).toMonoidHom ⊓ Z1 K) := by
      calc _ ≤ _ := hcardΔ
        _ < _ := by
          rw [mul_comm]
          exact Nat.mul_lt_mul_of_pos_right hk1 Nat.card_pos
    intro φ w hw
    have h1 := hPΔ _ inf_le_left hlt (g2Act x⁻¹ (g2Act g w)) (by
      rintro b ⟨⟨_, ⟨φ', rfl⟩, rfl⟩, hbZ⟩
      change g2Act (x⁻¹ * Φ φ' * x⁻¹⁻¹) (g2Act x⁻¹ (g2Act g w)) = g2Act x⁻¹ (g2Act g w)
      change x⁻¹ * Φ φ' * x⁻¹⁻¹ ∈ Z1 K at hbZ
      rw [inv_inv] at hbZ ⊢
      rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_apply_inv, hlong φ' hbZ w hw])
      (x⁻¹ * Φ φ * x⁻¹⁻¹) ⟨Φ φ, ⟨φ, rfl⟩, rfl⟩
    rw [inv_inv, g2Act_mul_apply, g2Act_mul_apply, g2Act_apply_inv] at h1
    have h3 := congrArg (g2Act x) h1
    rwa [g2Act_apply_inv, g2Act_apply_inv] at h3
  intro a haA
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvV : v ∈ V := h3V hv
  have hv3 : (⟨v, hvV⟩ : ↥V) ∈ V₃.subgroupOf V := hv
  rw [hV₃] at hv3
  change f ⟨v, hvV⟩ ∈ gmapG g (stdF K 3) at hv3
  rw [mem_gmapG] at hv3
  let φ : ↥(autOn A V) := ⟨SecA.conjV V a (hAN haA), SecA.conjV_mem_autOn haA _⟩
  have h1 := hfixF3 φ _ hv3
  rw [g2Act_apply_inv, ← hΦ] at h1
  have h3 := congrArg Subtype.val (hfinj h1)
  change ((SecA.conjV V a (hAN haA) ⟨v, hvV⟩ : ↥V) : G) = v at h3
  rw [SecA.conjV_apply_coe] at h3
  calc v * a = a * v * a⁻¹ * a := by rw [h3]
    _ = a * v := by group

end CFSG.Quasithin.Vol2.Ch11.G2Q8
