module

public import CFSG.Quasithin.H13.U3S1348J
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.Quasithin.Vol2.Ch11SecD556G

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

theorem block_conj_eq_inv {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {J : Subgroup (MulAut W)} {𝓗 : Finset (Subgroup (MulAut W))} (hb : IsTransvectionBlocks J 𝓗)
    {K : Subgroup (MulAut W)} (hK : K ∈ 𝓗) {c τ : MulAut W} (hc : c ∈ K) (hc3 : orderOf c = 3)
    (hτ : τ ∈ K) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1) : τ * c * τ⁻¹ = c⁻¹ := by
  have h6 := hb.card_eq K hK
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc3
    omega
  have he3 : (τ * c * τ⁻¹) ^ 3 = 1 := by rw [conj_pow, hc3', mul_one, mul_inv_cancel]
  have heK : τ * c * τ⁻¹ ∈ K := mul_mem (mul_mem hτ hc) (inv_mem hτ)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (mem_zpowers_of_pow_three h6 hc hc3 heK he3)
  have hk' : τ * c * τ⁻¹ = c ^ (k % 3).toNat := by
    rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num)),
      ← zpow_mod_orderOf, hc3]
    norm_num
  have hlt : (k % 3).toNat < 3 := by omega
  interval_cases h : (k % 3).toNat
  · exfalso
    rw [pow_zero] at hk'
    apply hc1
    calc c = τ⁻¹ * (τ * c * τ⁻¹) * τ := by group
      _ = 1 := by rw [hk']; group
  · exfalso
    rw [pow_one] at hk'
    have hcomm : c * τ = τ * c := by
      calc c * τ = (τ * c * τ⁻¹) * τ := by rw [hk']
        _ = τ * c := by group
    exact hc1 (block_eq_one_of_commute hW hb hK hc hτ hτ2 hτ1 hcomm ⟨3, by decide, hc3'⟩)
  · rw [hk']
    calc c ^ 2 = c ^ 3 * c⁻¹ := by group
      _ = c⁻¹ := by rw [hc3', one_mul]

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_card_blocks_eq_one_of_sylow (S : A6.Setting134 G T L V) {Lp : Subgroup G}
    (P : S134Plus S Lp) {z : G}
    {H VH : Subgroup G} (hHz : InHz T L V z H) (hsolv : Group.IsSolvable ↥H)
    (hred : IsTwoReducedIn H VH) (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hJ : ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G))
    (hL1eq : Lp = oTwoRes (H ⊓ centralizer (VH : Set G)))
    (hHL1 : H ≤ normalizer (Lp : Set G))
    (hR₁ : IsSylowTwoOf (r1Of T L V) (centralizerMod (pCoreOf 2 Lp) H Lp))
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))}
    (B : BlocksR (hV := hred.2.2.1) H (r1Of T L V) 𝓗 𝓘) (hne : 𝓘.Nonempty)
    (hcard : 𝓘.card ≤ 2) : 𝓘.card = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : 1 ≤ 𝓘.card := Finset.card_pos.2 hne
  by_contra hne1
  have h2 : 𝓘.card = 2 := by omega
  obtain ⟨K₁, K₂, hK12, hI⟩ := Finset.card_eq_two.1 h2
  have hK₁ : K₁ ∈ 𝓘 := hI ▸ Finset.mem_insert_self _ _
  have hK₂ : K₂ ∈ 𝓘 := hI ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  set O₁ := pCoreOf 2 Lp with hO₁
  set H₁ := centralizerMod O₁ H Lp with hH₁
  have hW : ∀ w : IntMod VH hred.2.2.1, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  obtain ⟨hTsyl, hL1TH, -, hO2H, -⟩ := s134_inHz_facts S hHz
  have hTH : T ≤ H := hTsyl.1
  have hL1H : Lp ≤ H := P.le_L1.trans (le_sup_left.trans hL1TH)
  have hHN : H ≤ normalizer (VH : Set G) := hred.2.1
  have hH₁H : H₁ ≤ H := fun x hx => hx.1
  have hOn : H ≤ normalizer (O₁ : Set G) := hHL1.trans (normalizer_le_normalizer_pCoreOf 2 Lp)
  have hH₁n : H ≤ normalizer (H₁ : Set G) := le_normalizer_centralizerMod hOn le_normalizer hHL1
  have hRH₁ : r1Of T L V ≤ H₁ := hR₁.1
  have hJR : thompsonJ (r1Of T L V) ≤ r1Of T L V := iSup₂_le fun _ hA => hA.1
  have hIH₁ : conjClosure (thompsonJ (r1Of T L V)) H ≤ H₁ := conjClosure_le fun h hh j hj =>
    (mem_normalizer_iff.mp (hH₁n hh) j).mp (hRH₁ (hJR hj))
  have hO₁O : O₁ ≤ pCoreOf 2 H := by
    have hO₁H : O₁ ≤ H := (pCoreOf_le 2 Lp).trans hL1H
    exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hO₁H
      ((normal_subgroupOf_iff_le_normalizer hO₁H).2 hOn) (pCoreOf_isPGroup 2 Lp)
  have hCH : H ⊓ centralizer (VH : Set G) ≤ H := inf_le_left
  have hL1C : Lp ≤ centralizer (VH : Set G) :=
    hL1eq.le.trans ((oTwoRes_le _).trans inf_le_right)
  have hP1 := P
  obtain ⟨ℓ, hℓL, hℓ3, hℓNV, hℓρ⟩ := P.exists_cube
    (inA4_cube_mem_C3 c012 c012_props.2.2 c012_props.2.1)
  have hℓH : ℓ ∈ H := hL1H hℓL
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hπ1 : ∀ (x : G) (hx : x ∈ H), x ∈ pCoreOf 2 H → π ⟨x, hx⟩ = 1 := by
    intro x hx hxO
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, AppC.mem_pCore_iff_mem_blockQ]
    exact hxO
  have hπ1' : ∀ (x : G) (hx : x ∈ H), π ⟨x, hx⟩ = 1 → x ∈ pCoreOf 2 H := by
    intro x hx h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      AppC.mem_pCore_iff_mem_blockQ] at h
    exact h
  have hker : CFSG.pCore 2 ↥H ≤ (convHom hred.2.2.1 H hHN).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, convHom_apply, convI_eq_one_iff]
    exact pCoreOf_le_centralizer_of_reduced' hred ((AppC.mem_pCore_iff_mem_blockQ x).1 hx)
  set ψ := QuotientGroup.lift (CFSG.pCore 2 ↥H) (convHom hred.2.2.1 H hHN) hker with hψ
  have hψπ : ∀ (x : G) (hx : x ∈ H), ψ (π ⟨x, hx⟩) = convI hred.2.2.1 ⟨x, hHN hx⟩ := fun x hx => rfl
  set w := π ⟨ℓ, hℓH⟩ with hw
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← map_pow]
    have : (⟨ℓ, hℓH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hℓ3)
    rw [this, map_one]
  have hw1 : w ≠ 1 := by
    intro h
    have hℓO := hπ1' ℓ hℓH h
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨ℓ, hℓO⟩
    have hk' : ℓ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hg : ℓ ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.2 ⟨hℓ3, hk'⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at hg
    have h1 : (⟨ℓ, hℓNV⟩ : ↥(normalizer (V : Set G))) = 1 := Subtype.ext hg
    rw [h1, map_one] at hℓρ
    exact absurd hℓρ.symm (by decide)
  have hψw : ψ w = 1 := by
    rw [hw, hψπ, convI_eq_one_iff]
    exact hL1C hℓL
  have hcommw : ∀ (x : G) (hx : x ∈ H), x ∈ H₁ → Commute (π ⟨x, hx⟩) w := by
    intro x hx hxH₁
    have h1 : x * ℓ * x⁻¹ * ℓ⁻¹ ∈ pCoreOf 2 H := hO₁O (hxH₁.2.2 ℓ hℓL)
    have h2 := hπ1 _ (mul_mem (mul_mem (mul_mem hx hℓH) (inv_mem hx)) (inv_mem hℓH)) h1
    have e : (⟨x * ℓ * x⁻¹ * ℓ⁻¹, mul_mem (mul_mem (mul_mem hx hℓH) (inv_mem hx))
        (inv_mem hℓH)⟩ : ↥H) = ⟨x, hx⟩ * ⟨ℓ, hℓH⟩ * ⟨x, hx⟩⁻¹ * ⟨ℓ, hℓH⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    have h3 : π ⟨x, hx⟩ * w = w * π ⟨x, hx⟩ := by
      calc π ⟨x, hx⟩ * w = (π ⟨x, hx⟩ * w * (π ⟨x, hx⟩)⁻¹ * w⁻¹) * (w * π ⟨x, hx⟩) := by group
        _ = w * π ⟨x, hx⟩ := by rw [h2, one_mul]
    exact h3
  have hL1bar : ∀ (x : G) (hx : x ∈ Lp), ∃ k : ℕ, π ⟨x, hL1H hx⟩ = w ^ k := by
    intro x hx
    have hxN : x ∈ normalizer (V : Set G) := P.le_NV hx
    have hA4 := P.rho (x := ⟨x, hxN⟩) hx
    have hK : ∀ (e : G) (he : e ∈ Lp) (heN : e ∈ normalizer (V : Set G)),
        S.frame.ρ ⟨e, heN⟩ ∈ K4List → π ⟨e, hL1H he⟩ = 1 := fun e he heN hρ =>
      hπ1 e _ (hO₁O (hP1.mem_pCoreOf_of_K4 (x := ⟨e, heN⟩) he hρ))
    rcases A4_dec _ hA4 with h | h | h
    · exact ⟨0, by rw [pow_zero]; exact hK x hx hxN h⟩
    ·
      have hmem : x * ℓ⁻¹ ∈ Lp := mul_mem hx (inv_mem hℓL)
      have hmemN : x * ℓ⁻¹ ∈ normalizer (V : Set G) := mul_mem hxN (inv_mem hℓNV)
      have hρe : S.frame.ρ ⟨x * ℓ⁻¹, hmemN⟩ ∈ K4List := by
        rw [show (⟨x * ℓ⁻¹, hmemN⟩ : ↥(normalizer (V : Set G))) = ⟨x, hxN⟩ * ⟨ℓ, hℓNV⟩⁻¹ from rfl,
          map_mul, map_inv, hℓρ]
        exact h
      have h1 := hK _ hmem hmemN hρe
      refine ⟨1, ?_⟩
      rw [pow_one]
      have e : (⟨x * ℓ⁻¹, hL1H hmem⟩ : ↥H) = ⟨x, hL1H hx⟩ * (⟨ℓ, hℓH⟩)⁻¹ := rfl
      rw [e, map_mul, map_inv] at h1
      calc π ⟨x, hL1H hx⟩ = (π ⟨x, hL1H hx⟩ * w⁻¹) * w := by group
        _ = w := by rw [h1, one_mul]
    ·
      have hmem : x * ℓ ∈ Lp := mul_mem hx hℓL
      have hmemN : x * ℓ ∈ normalizer (V : Set G) := mul_mem hxN hℓNV
      have hρe : S.frame.ρ ⟨x * ℓ, hmemN⟩ ∈ K4List := by
        rw [show (⟨x * ℓ, hmemN⟩ : ↥(normalizer (V : Set G))) = ⟨x, hxN⟩ * ⟨ℓ, hℓNV⟩ from rfl,
          map_mul, hℓρ]
        exact h
      have h1 := hK _ hmem hmemN hρe
      refine ⟨2, ?_⟩
      have e : (⟨x * ℓ, hL1H hmem⟩ : ↥H) = ⟨x, hL1H hx⟩ * ⟨ℓ, hℓH⟩ := rfl
      rw [e, map_mul] at h1
      have hw2 : w ^ 2 = w⁻¹ := by
        calc w ^ 2 = w ^ 3 * w⁻¹ := by group
          _ = w⁻¹ := by rw [hw3, one_mul]
      calc π ⟨x, hL1H hx⟩ = (π ⟨x, hL1H hx⟩ * w) * w⁻¹ := by group
        _ = w ^ 2 := by rw [h1, one_mul, hw2]
  have hCn : H ≤ normalizer ((H ⊓ centralizer (VH : Set G) : Subgroup G) : Set G) :=
    fun h hh => mem_normalizer_inf_of (le_normalizer hh)
      (mem_normalizer_centralizer_of_mem (hHN hh))
  have hRH : r1Of T L V ≤ H := (r1Of_le_T T L V).trans hTH
  have hsylC : IsSylowTwoOf (pCoreOf 2 H) ((H ⊓ centralizer (VH : Set G)) ⊓ H₁) := by
    have h := A4.isSylowTwoOf_inf_normal hR₁
      (inf_le_right : (H ⊓ centralizer (VH : Set G)) ⊓ H₁ ≤ H₁)
      (fun x hx => mem_normalizer_inf_of (hCn (hH₁H hx)) (le_normalizer hx))
    have e : r1Of T L V ⊓ ((H ⊓ centralizer (VH : Set G)) ⊓ H₁) = pCoreOf 2 H := by
      rw [inf_comm (H ⊓ centralizer (VH : Set G)) H₁, ← inf_assoc, inf_eq_left.2 hRH₁,
        ← inf_assoc, inf_eq_left.2 hRH, hcR]
    rwa [e] at h
  have hQ1 : ∀ (x : G) (hx : x ∈ H), x ∈ centralizer (VH : Set G) → x ∈ H₁ →
      ∃ k : ℕ, π ⟨x, hx⟩ = w ^ k := by
    intro x hx hxC hxH₁
    obtain ⟨y, hy, z', hz', hxyz, ⟨k, hyk⟩, m, hm, hzm⟩ := exists_two_odd_decomp x
    have hzpow : ∀ {X : Subgroup G}, x ∈ X → zpowers x ≤ X := fun hX => zpowers_le.2 hX
    have hyH := hzpow hx hy
    have hzH := hzpow hx hz'
    have hyC := hzpow hxC hy
    have hzC := hzpow hxC hz'
    have hyH₁ := hzpow hxH₁ hy
    have hyO : y ∈ pCoreOf 2 H :=
      Unc25G2.mem_of_isSylowTwoOf_of_normalizes hsylC
        (fun g hg => le_normalizer_pCoreOf 2 H hg.1.1) ⟨⟨hyH, hyC⟩, hyH₁⟩ ⟨k, hyk⟩
    have hzL : z' ∈ Lp := hL1eq.ge (mem_oTwoRes_of_odd (mem_inf.2 ⟨hzH, hzC⟩) hm hzm)
    obtain ⟨j, hj⟩ := hL1bar z' hzL
    refine ⟨j, ?_⟩
    have e : (⟨x, hx⟩ : ↥H) = ⟨y, hyH⟩ * ⟨z', hL1H hzL⟩ := Subtype.ext hxyz
    rw [e, map_mul, hπ1 y hyH hyO, one_mul, hj]
  set H₁b := (H₁.subgroupOf H).map π with hH₁b
  have hQ1' : ∀ q ∈ H₁b, ψ q = 1 → ∃ k : ℕ, q = w ^ k := by
    rintro q ⟨x, hx, rfl⟩ h1
    have hxC : (x : G) ∈ centralizer (VH : Set G) :=
      (convI_eq_one_iff hred.2.2.1 _).1 h1
    exact hQ1 x x.2 hxC (mem_subgroupOf.1 hx)
  have hcommw' : ∀ q ∈ H₁b, Commute q w := by
    rintro q ⟨x, hx, rfl⟩
    exact hcommw x x.2 (mem_subgroupOf.1 hx)
  have hmemb : ∀ (x : G) (hx : x ∈ H), x ∈ H₁ → π ⟨x, hx⟩ ∈ H₁b := fun x hx hxH₁ =>
    ⟨⟨x, hx⟩, mem_subgroupOf.2 hxH₁, rfl⟩
  have hIH : conjClosure (thompsonJ (r1Of T L V)) H ≤ H := hIH₁.trans hH₁H
  have hlift : ∀ {X : Subgroup G}, X ≤ H₁ → ∀ c ∈ autI hred.2.2.1 X,
      ∃ q ∈ H₁b, ψ q = c := by
    intro X hXH c hc
    obtain ⟨g, hgX, rfl⟩ := (mem_autI hred.2.2.1).1 hc
    exact ⟨π ⟨g, hH₁H (hXH hgX)⟩, hmemb _ _ (hXH hgX), rfl⟩
  have hKI : ∀ K ∈ 𝓘, K ≤ autI hred.2.2.1 (conjClosure (thompsonJ (r1Of T L V)) H) := by
    intro K hK
    rw [B.eq]
    exact le_iSup₂_of_le (f := fun (K' : Subgroup (MulAut (IntMod VH hred.2.2.1)))
      (_ : K' ∈ 𝓘) => K') K hK le_rfl
  have hVR : VH ≤ r1Of T L V :=
    (s134_VH_le_r1Of hred hcR).1.trans (s134_VH_le_r1Of hred hcR).2
  have hTR : T ≤ normalizer (r1Of T L V : Set G) := by
    rw [← hP1.pCoreOf_eq_r1Of]
    exact le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  have hτ : ∀ K ∈ 𝓘, ∃ τ ∈ autI hred.2.2.1 (thompsonJ (r1Of T L V)), τ ∈ K ∧ τ ≠ 1 ∧
      τ ^ 2 = 1 := by
    intro K hK
    obtain ⟨⟨τ, hτm⟩, hτ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
      (B.inf_ne_bot hred hsolv hVR hRH hJ hTsyl hTR hcard hK)
    have hτ1' : τ ≠ 1 := fun h => hτ1 (Subtype.ext h)
    obtain ⟨hτJ, hτK⟩ := mem_inf.1 hτm
    refine ⟨τ, hτJ, hτK, hτ1', ?_⟩
    obtain ⟨g, hgJ, rfl⟩ := (mem_autI hred.2.2.1).1 hτJ
    obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨g, (r1Of_le_T T L V) (hJR hgJ)⟩
    have hk' : (convI hred.2.2.1 g) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    have h6 : (convI hred.2.2.1 g) ^ 6 = 1 := by
      have h1 : orderOf (⟨_, hτK⟩ : ↥K) ∣ 6 :=
        B.hb.card_eq K (B.sub hK) ▸ orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact orderOf_dvd_iff_pow_eq_one.1 h1
    have hg := pow_gcd_eq_one.2 ⟨h6, hk'⟩
    have hd : Nat.gcd 6 (2 ^ k) ∣ 2 := by
      rw [show (6 : ℕ) = 3 * 2 from rfl,
        Nat.Coprime.gcd_mul_left_cancel 2 (Nat.Coprime.pow_right k (by norm_num))]
      exact Nat.gcd_dvd_left 2 (2 ^ k)
    exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one hg).trans hd)
  obtain ⟨c₁, hc₁K, hc₁⟩ := exists_orderOf_three_of_card_six (B.hb.card_eq K₁ (B.sub hK₁))
  obtain ⟨c₂, hc₂K, hc₂⟩ := exists_orderOf_three_of_card_six (B.hb.card_eq K₂ (B.sub hK₂))
  obtain ⟨τ₁, hτ₁J, hτ₁K, hτ₁1, hτ₁2⟩ := hτ K₁ hK₁
  obtain ⟨τ₂, hτ₂J, hτ₂K, hτ₂1, hτ₂2⟩ := hτ K₂ hK₂
  obtain ⟨Y₁, hY₁, hψY₁⟩ := hlift hIH₁ c₁ (hKI K₁ hK₁ hc₁K)
  obtain ⟨Y₂, hY₂, hψY₂⟩ := hlift hIH₁ c₂ (hKI K₂ hK₂ hc₂K)
  obtain ⟨U₁, hU₁, hψU₁⟩ := hlift (hJR.trans hRH₁) τ₁ hτ₁J
  obtain ⟨U₂, hU₂, hψU₂⟩ := hlift (hJR.trans hRH₁) τ₂ hτ₂J
  have hc₁3 : c₁ ^ 3 = 1 := by rw [← hc₁]; exact pow_orderOf_eq_one c₁
  have hc₂3 : c₂ ^ 3 = 1 := by rw [← hc₂]; exact pow_orderOf_eq_one c₂
  have hinv₁ := block_conj_eq_inv hW B.hb (B.sub hK₁) hc₁K hc₁ hτ₁K hτ₁2 hτ₁1
  have hinv₂ := block_conj_eq_inv hW B.hb (B.sub hK₂) hc₂K hc₂ hτ₂K hτ₂2 hτ₂1
  have h12 : c₁ * c₂ = c₂ * c₁ := B.hb.comm K₁ (B.sub hK₁) K₂ (B.sub hK₂) hK12 c₁ hc₁K c₂ hc₂K
  have hτc : τ₁ * c₂ = c₂ * τ₁ := B.hb.comm K₁ (B.sub hK₁) K₂ (B.sub hK₂) hK12 τ₁ hτ₁K c₂ hc₂K
  have hψ₀ : ψ (Y₁ * Y₂ * Y₁⁻¹ * Y₂⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hψY₁, hψY₂, h12]
    group
  obtain ⟨e₀, he₀⟩ := hQ1' _ (H₁b.mul_mem (H₁b.mul_mem (H₁b.mul_mem hY₁ hY₂)
    (H₁b.inv_mem hY₁)) (H₁b.inv_mem hY₂)) hψ₀
  have hcomm₀ : ⁅Y₁, Y₂⁆ = w ^ e₀ := by rw [commutatorElement_def]; exact he₀
  have hψf₁ : ψ (Y₁ ^ 3) = 1 := by rw [map_pow, hψY₁, hc₁3]
  have hψf₂ : ψ (Y₂ ^ 3) = 1 := by rw [map_pow, hψY₂, hc₂3]
  obtain ⟨f₁, hf₁⟩ := hQ1' _ (H₁b.pow_mem hY₁ 3) hψf₁
  obtain ⟨f₂, hf₂⟩ := hQ1' _ (H₁b.pow_mem hY₂ 3) hψf₂
  have hψa₁ : ψ (U₁ * Y₁ * U₁⁻¹ * Y₁) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hψU₁, hψY₁, hinv₁, inv_mul_cancel]
  have hψa₂ : ψ (U₂ * Y₂ * U₂⁻¹ * Y₂) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hψU₂, hψY₂, hinv₂, inv_mul_cancel]
  have hψb₁ : ψ (U₁ * Y₂ * U₁⁻¹ * Y₂⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hψU₁, hψY₂, hτc]
    group
  obtain ⟨a₁, ha₁⟩ := hQ1' _ (H₁b.mul_mem (H₁b.mul_mem (H₁b.mul_mem hU₁ hY₁)
    (H₁b.inv_mem hU₁)) hY₁) hψa₁
  obtain ⟨a₂, ha₂⟩ := hQ1' _ (H₁b.mul_mem (H₁b.mul_mem (H₁b.mul_mem hU₂ hY₂)
    (H₁b.inv_mem hU₂)) hY₂) hψa₂
  obtain ⟨b₁, hb₁⟩ := hQ1' _ (H₁b.mul_mem (H₁b.mul_mem (H₁b.mul_mem hU₁ hY₂)
    (H₁b.inv_mem hU₁)) (H₁b.inv_mem hY₂)) hψb₁
  have hY₁w := hcommw' Y₁ hY₁
  have hY₂w := hcommw' Y₂ hY₂
  have hU₁w := hcommw' U₁ hU₁
  have hU₂w := hcommw' U₂ hU₂
  have htu₁ : U₁ * Y₁ * U₁⁻¹ = w ^ a₁ * Y₁⁻¹ := by
    rw [← ha₁]
    group
  have htu₂ : U₂ * Y₂ * U₂⁻¹ = w ^ a₂ * Y₂⁻¹ := by
    rw [← ha₂]
    group
  have htv₁ : U₁ * Y₂ * U₁⁻¹ = w ^ b₁ * Y₂ := by
    rw [← hb₁]
    group
  have hY12 : ⁅Y₁, Y₂⁆ = 1 :=
    commutatorElement_eq_one_of_central hw3 hY₁w hY₂w hU₁w htu₁ htv₁ hcomm₀
  have hY₁3 : Y₁ ^ 3 = 1 := pow_three_eq_one_of_central hw3 hY₁w hU₁w htu₁ hf₁
  have hY₂3 : Y₂ ^ 3 = 1 := pow_three_eq_one_of_central hw3 hY₂w hU₂w htu₂ hf₂
  have hY12c : Y₁ * Y₂ = Y₂ * Y₁ := by
    rw [commutatorElement_def] at hY12
    calc Y₁ * Y₂ = (Y₁ * Y₂ * Y₁⁻¹ * Y₂⁻¹) * (Y₂ * Y₁) := by group
      _ = Y₂ * Y₁ := by rw [hY12, one_mul]
  have hbot : IsElemAbelian 3 (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [(mem_bot).1 hx, one_pow]⟩
  obtain ⟨hA₁, hA₁c⟩ := elemAbelian_sup_zpowers hbot (fun h => hw1 ((mem_bot).1 h)) hw3
    (fun a ha => by rw [(mem_bot).1 ha, one_mul, mul_one])
  set A₁ := (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ⊔ zpowers w with hA₁def
  have hA₁ψ : A₁ ≤ ψ.ker := sup_le bot_le (zpowers_le.2 (MonoidHom.mem_ker.2 hψw))
  have hc₁1 : c₁ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc₁
    omega
  have hc₂1 : c₂ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc₂
    omega
  have hY₁A : Y₁ ∉ A₁ := fun h => hc₁1 (hψY₁ ▸ MonoidHom.mem_ker.1 (hA₁ψ h))
  obtain ⟨hA₂, hA₂c⟩ := elemAbelian_sup_zpowers hA₁ hY₁A hY₁3 (by
    have hle : A₁ ≤ centralizer ({Y₁} : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      sup_le bot_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hY₁w.eq.symm))
    exact fun a ha => mem_centralizer_singleton_iff.1 (hle ha))
  set A₂ := A₁ ⊔ zpowers Y₁ with hA₂def
  have hA₂ψ : A₂ ≤ K₁.comap ψ := by
    refine sup_le (hA₁ψ.trans fun x hx => ?_) (zpowers_le.2 (mem_comap.2 (hψY₁ ▸ hc₁K)))
    rw [mem_comap, MonoidHom.mem_ker.1 hx]
    exact one_mem _
  have hY₂A : Y₂ ∉ A₂ := by
    intro h
    have h1 : c₂ ∈ K₁ ⊓ K₂ := ⟨hψY₂ ▸ mem_comap.1 (hA₂ψ h), hc₂K⟩
    rw [B.inf_eq_bot hK₁ hK₂ hK12, mem_bot] at h1
    exact hc₂1 h1
  obtain ⟨hA₃, hA₃c⟩ := elemAbelian_sup_zpowers hA₂ hY₂A hY₂3 (by
    have hle : A₂ ≤ centralizer ({Y₂} : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      refine sup_le (sup_le bot_le (zpowers_le.2 ?_)) (zpowers_le.2 ?_)
      · exact mem_centralizer_singleton_iff.2 hY₂w.eq.symm
      · exact mem_centralizer_singleton_iff.2 hY12c
    exact fun a ha => mem_centralizer_singleton_iff.1 (hle ha))
  have hcard3 : Nat.card ↥(A₂ ⊔ zpowers Y₂) = 3 ^ 3 := by
    rw [hA₃c, hA₂c, hA₁c, card_bot]
    norm_num
  have hrank : ∀ E : Subgroup G, E ≤ H → IsElemAbelian 3 E → ∀ r, Nat.card E = 3 ^ r →
      r ≤ 2 := fun E hE hEab r hr =>
    Vol2.Ch11.SecD.le_two_of_elemAbelian S.fsu.qtke.2.2 hO2H (pCoreOf_isPGroup 2 H)
      Nat.prime_three (by norm_num) (hE.trans (le_normalizer_pCoreOf 2 H)) hEab hr
  have := Vol2.Ch11.SecD.le_two_of_elemAbelian_quotient (G₁ := H) Nat.prime_three
    (by norm_num) hrank hA₃ hcard3
  omega

end CFSG.Quasithin.H13.U3
