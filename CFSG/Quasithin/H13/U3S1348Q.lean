module

public import CFSG.Quasithin.H13.U3S1348P
public import CFSG.Quasithin.H13.U3S1349S

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_quot_I_of {H VH R : Subgroup G} (hred : IsTwoReducedIn H VH)
    (hTsyl : IsSylowTwoOf T H) (hRT : R ≤ T)
    (hJ : ¬ thompsonJ R ≤ centralizer (VH : Set G))
    {K : Subgroup (MulAut (IntMod VH hred.2.2.1))} (hK6 : Nat.card K = 6)
    (hIK : autI hred.2.2.1 (conjClosure (thompsonJ R) H) = K)
    (hIC : conjClosure (thompsonJ R) H ⊓ centralizer (VH : Set G) ≤ pCoreOf 2 H) :
    quasithinO2QuotientIso (conjClosure (thompsonJ R) H) (Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := conjClosure (thompsonJ R) H with hIdef
  have hJT : thompsonJ R ≤ T := (iSup₂_le fun _ hA => hA.1 : thompsonJ R ≤ R).trans hRT
  have hIH : I ≤ H := conjClosure_le fun h hh j hj =>
    mul_mem (mul_mem hh (hTsyl.1 (hJT hj))) (inv_mem hh)
  have hHI : H ≤ normalizer (I : Set G) := le_normalizer_conjClosure _ _
  have hsyl : IsSylowTwoOf (T ⊓ I) I := A4.isSylowTwoOf_inf_normal hTsyl hIH hHI
  have hIN : I ≤ normalizer (VH : Set G) := hIH.trans hred.2.1
  have hcI := card_autI_mul_card_inf hred.2.2.1 hIN
  have hcT := card_autI_mul_card_inf hred.2.2.1 (inf_le_right.trans hIN : T ⊓ I ≤ _)
  have hTIC : (T ⊓ I) ⊓ centralizer (VH : Set G) = I ⊓ centralizer (VH : Set G) := by
    refine le_antisymm (inf_le_inf_right _ inf_le_right) (le_inf (le_inf ?_ inf_le_left)
      inf_le_right)
    exact hIC.trans (pCoreOf_two_le_of_isSylowTwoOf hTsyl)
  have hJI : thompsonJ R ≤ T ⊓ I := le_inf hJT (le_conjClosure _ _)
  have hc2 : Nat.card ↥(autI hred.2.2.1 (T ⊓ I)) = 2 := by
    have hle : autI hred.2.2.1 (T ⊓ I) ≤ K := hIK ▸ autI_mono _ inf_le_right
    have hdvd : Nat.card ↥(autI hred.2.2.1 (T ⊓ I)) ∣ 6 := hK6 ▸ card_dvd_of_le hle
    have hp : IsPGroup 2 ↥(autI hred.2.2.1 (T ⊓ I)) := by
      rintro ⟨φ, hφ⟩
      obtain ⟨g, hgT, rfl⟩ := (mem_autI hred.2.2.1).1 hφ
      obtain ⟨k, hk⟩ := hTsyl.2.1 ⟨g, hgT.1⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, h1, map_one]
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hne : autI hred.2.2.1 (T ⊓ I) ≠ ⊥ := by
      intro h
      have h1 : autI hred.2.2.1 (thompsonJ R) = ⊥ :=
        le_bot_iff.1 (h ▸ autI_mono hred.2.2.1 hJI)
      exact hJ ((autI_eq_bot_iff hred.2.2.1 ((hJI.trans inf_le_right).trans hIN)).1 h1)
    have hn1 : n ≠ 0 := by
      rintro rfl
      exact hne (card_eq_one.1 (by rw [hn, pow_zero]))
    have hn2 : n < 2 := by
      by_contra h
      have h4 : 4 ∣ 2 ^ n := pow_dvd_pow 2 (by omega : 2 ≤ n)
      rw [← hn] at h4
      exact absurd (h4.trans hdvd) (by norm_num)
    have hn' : n = 1 := by omega
    rw [hn, hn', pow_one]
  have h3 : (T ⊓ I).relIndex I = 3 := by
    have h1 := relIndex_mul_card (T ⊓ I) I
    rw [inf_eq_left.2 (inf_le_right : T ⊓ I ≤ I)] at h1
    rw [← hcT, ← hcI, hTIC, hc2, hIK, hK6] at h1
    have hpos : 0 < Nat.card ↥(I ⊓ centralizer (VH : Set G)) := Nat.card_pos
    have h2 : (T ⊓ I).relIndex I * 2 = 6 := by
      have := h1
      rw [← mul_assoc] at this
      exact Nat.eq_of_mul_eq_mul_right hpos this
    omega
  refine quot_S3_of_index_three hsyl h3 fun hN => ?_
  have hTO : T ⊓ I ≤ pCoreOf 2 I := by
    refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
      inf_le_right ?_ (hTsyl.2.1.to_le inf_le_left)
    exact (normal_subgroupOf_iff_le_normalizer inf_le_right).2 hN
  exact hJ ((hJI.trans hTO).trans ((pCoreOf_le_pCoreOf hIH hHI).trans
    (pCoreOf_le_centralizer_of_reduced' hred)))

theorem s134_I_inf_C_of_sylow (S : A6.Setting134 G T L V) {Lp : Subgroup G}
    (P : S134Plus S Lp) {z : G} {H VH : Subgroup G} (hHz : InHz T L V z H)
    (hsolv : Group.IsSolvable ↥H) (hred : IsTwoReducedIn H VH)
    (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hJ : ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G))
    (hL1eq : Lp = oTwoRes (H ⊓ centralizer (VH : Set G)))
    (hHL1 : H ≤ normalizer (Lp : Set G))
    (hR₁ : IsSylowTwoOf (r1Of T L V) (centralizerMod (pCoreOf 2 Lp) H Lp))
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))}
    (B : BlocksR (hV := hred.2.2.1) H (r1Of T L V) 𝓗 𝓘) (hne : 𝓘.Nonempty)
    (hcard : 𝓘.card ≤ 2) :
    conjClosure (thompsonJ (r1Of T L V)) H ⊓ centralizer (VH : Set G) ≤ pCoreOf 2 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I := conjClosure (thompsonJ (r1Of T L V)) H with hIdef
  set H₁ := centralizerMod (pCoreOf 2 Lp) H Lp with hH₁
  have h1 := s134_card_blocks_eq_one_of_sylow S P hHz hsolv hred hcR hJ hL1eq hHL1 hR₁ B hne
    hcard
  obtain ⟨K, hK𝓘, hIK, -⟩ := s134_single_block B h1
  have hK : K ∈ 𝓗 := B.sub hK𝓘
  have hW : ∀ w : IntMod VH hred.2.2.1, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hHN : H ≤ normalizer (VH : Set G) := hred.2.1
  obtain ⟨ℓ, -, hℓ3, hℓO, hℓC, hℓcomm, hℓmod, hℓH₁⟩ :=
    s134_bar_ctx S P hHz hred hcR hL1eq hHL1 hR₁
  have hH₁H : H₁ ≤ H := fun x hx => hx.1
  have hℓH : ℓ ∈ H := hH₁H hℓH₁
  have hOn : H ≤ normalizer (pCoreOf 2 Lp : Set G) :=
    hHL1.trans (normalizer_le_normalizer_pCoreOf 2 Lp)
  have hH₁n : H ≤ normalizer (H₁ : Set G) := le_normalizer_centralizerMod hOn le_normalizer hHL1
  have hJR : thompsonJ (r1Of T L V) ≤ r1Of T L V := iSup₂_le fun _ hA => hA.1
  have hIH₁ : I ≤ H₁ := conjClosure_le fun h hh j hj =>
    (mem_normalizer_iff.mp (hH₁n hh) j).mp (hR₁.1 (hJR hj))
  obtain ⟨y, hyK, hy3⟩ := exists_orderOf_three_of_card_six (B.hb.card_eq K hK)
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  obtain ⟨τ, hτJ, hτK, hτ1, hτ2⟩ := s134_exists_tau S P hHz hsolv hred hcR hJ B hcard hK𝓘
  have hinvτ := block_conj_eq_inv hW B.hb hK hyK hy3 hτK hτ2 hτ1
  have hτz : τ ∉ zpowers y := by
    intro h
    have h3 : τ ^ 3 = 1 := by
      have := orderOf_dvd_natCard (⟨τ, h⟩ : ↥(zpowers y))
      rw [Subgroup.orderOf_mk, Nat.card_zpowers, hy3] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    apply hτ1
    calc τ = τ ^ 3 * (τ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, hτ2]; group
  have hyI := hyK
  rw [← hIK] at hyI
  obtain ⟨⟨i, hiN⟩, hiI, hiy⟩ := (mem_autI hred.2.2.1).1 hyI
  obtain ⟨⟨t, htN⟩, htJ, htτ⟩ := (mem_autI hred.2.2.1).1 hτJ
  have hiH₁ : i ∈ H₁ := hIH₁ hiI
  have htH₁ : t ∈ H₁ := hR₁.1 (hJR htJ)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hker : CFSG.pCore 2 ↥H ≤ (convHom hred.2.2.1 H hHN).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, convHom_apply, convI_eq_one_iff]
    exact pCoreOf_le_centralizer_of_reduced' hred ((AppC.mem_pCore_iff_mem_blockQ x).1 hx)
  set ψ := QuotientGroup.lift (CFSG.pCore 2 ↥H) (convHom hred.2.2.1 H hHN) hker with hψ
  have hψπ : ∀ x : ↥H, ψ (π x) = convI hred.2.2.1 ⟨x, hHN x.2⟩ := fun _ => rfl
  have hπ1 : ∀ x : ↥H, π x = 1 ↔ (x : G) ∈ pCoreOf 2 H := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, AppC.mem_pCore_iff_mem_blockQ]
    exact Iff.rfl
  obtain ⟨w, hw⟩ : ∃ q, q = π ⟨ℓ, hℓH⟩ := ⟨_, rfl⟩
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← map_pow]
    exact (hπ1 _).2 (by simp [hℓ3])
  have hψw : ψ w = 1 := by
    rw [hw, hψπ, convI_eq_one_iff]
    exact hℓC
  obtain ⟨Hb, hHb⟩ : ∃ X : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), X = (H₁.subgroupOf H).map π :=
    ⟨_, rfl⟩
  have hmemHb : ∀ x : ↥H, (x : G) ∈ H₁ → π x ∈ Hb := fun x hx =>
    hHb ▸ ⟨x, mem_subgroupOf.2 hx, rfl⟩
  have hcommHb : ∀ q ∈ Hb, Commute q w := by
    intro q hq
    rw [hHb] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    have h1 : π (x * ⟨ℓ, hℓH⟩ * x⁻¹ * (⟨ℓ, hℓH⟩)⁻¹) = 1 :=
      (hπ1 _).2 (hℓcomm x (mem_subgroupOf.1 hx))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hw] at h1
    show π x * w = w * π x
    calc π x * w = (π x * w * (π x)⁻¹ * w⁻¹) * (w * π x) := by group
      _ = w * π x := by rw [h1, one_mul]
  have hQHb : ∀ q ∈ Hb, ψ q = 1 → ∃ k : ℕ, q = w ^ k := by
    intro q hq h
    rw [hHb] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    have hxC : (x : G) ∈ centralizer (VH : Set G) := by
      rw [hψπ, convI_eq_one_iff] at h
      exact h
    obtain ⟨k, hk⟩ := hℓmod x (mem_subgroupOf.1 hx) hxC
    refine ⟨k, ?_⟩
    have h1 : π (x * (⟨ℓ, hℓH⟩ ^ k)⁻¹) = 1 := (hπ1 _).2 (by simpa using hk)
    rw [map_mul, map_inv, map_pow, ← hw] at h1
    calc π x = (π x * (w ^ k)⁻¹) * w ^ k := by group
      _ = w ^ k := by rw [h1, one_mul]
  have hwHb : w ∈ Hb := hw ▸ hmemHb _ hℓH₁
  have hiH : i ∈ H := hH₁H hiH₁
  have htH : t ∈ H := hH₁H htH₁
  obtain ⟨Y, hY⟩ : ∃ q, q = π ⟨i, hiH⟩ := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ q, q = π ⟨t, htH⟩ := ⟨_, rfl⟩
  have hYHb : Y ∈ Hb := hY ▸ hmemHb _ hiH₁
  have hUHb : U ∈ Hb := hU ▸ hmemHb _ htH₁
  have hψY : ψ Y = y := by rw [hY, hψπ, ← hiy]
  have hψU : ψ U = τ := by rw [hU, hψπ, ← htτ]
  obtain ⟨a, ha⟩ := hQHb _ (Hb.mul_mem (Hb.mul_mem (Hb.mul_mem hUHb hYHb) (Hb.inv_mem hUHb))
    hYHb) (by rw [map_mul, map_mul, map_mul, map_inv, hψY, hψU, hinvτ, inv_mul_cancel])
  have htu : U * Y * U⁻¹ = w ^ a * Y⁻¹ := by
    rw [← ha]
    group
  obtain ⟨f, hf⟩ := hQHb _ (Hb.pow_mem hYHb 3) (by rw [map_pow, hψY, hy3'])
  have hY3 : Y ^ 3 = 1 :=
    pow_three_eq_one_of_central hw3 (hcommHb _ hYHb) (hcommHb _ hUHb) htu hf
  obtain ⟨g, hg⟩ := hQHb _ (Hb.pow_mem hUHb 2) (by rw [map_pow, hψU, hτ2])
  have hU2 : U ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨t, (r1Of_le_T T L V) (hJR htJ)⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hUk : U ^ 2 ^ k = 1 := by
      rw [hU, ← map_pow]
      exact (hπ1 _).2 (by simp [hk'])
    have hg1 : (w ^ g) ^ 2 ^ k = 1 := by
      rw [← hg, ← pow_mul, mul_comm, pow_mul, hUk, one_pow]
    have hg3 : (w ^ g) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hw3, one_pow]
    have hgcd := pow_gcd_eq_one.2 ⟨hg3, hg1⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at hgcd
    rw [hg, hgcd]
  have hYw := hcommHb _ hYHb
  have hUw := hcommHb _ hUHb
  obtain ⟨Yp, hYp⟩ : ∃ q, q = w ^ a * Y := ⟨_, rfl⟩
  have hYpHb : Yp ∈ Hb := hYp ▸ Hb.mul_mem (Hb.pow_mem hwHb a) hYHb
  have hψYp : ψ Yp = y := by rw [hYp, map_mul, map_pow, hψw, one_pow, one_mul, hψY]
  have hwa3 : (w ^ a) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hw3, one_pow]
  have hYpinv : U * Yp * U⁻¹ = Yp⁻¹ := by
    have hUwa : Commute U (w ^ a) := hUw.pow_right a
    have hYwa : Commute Y (w ^ a) := hYw.pow_right a
    calc U * Yp * U⁻¹ = (U * w ^ a * U⁻¹) * (U * Y * U⁻¹) := by rw [hYp]; group
      _ = w ^ a * (w ^ a * Y⁻¹) := by rw [htu, hUwa.eq]; group
      _ = ((w ^ a) ^ 3 * (w ^ a)⁻¹) * Y⁻¹ := by group
      _ = (w ^ a)⁻¹ * Y⁻¹ := by rw [hwa3, one_mul]
      _ = Y⁻¹ * (w ^ a)⁻¹ := (hYwa.inv_left.inv_right).eq.symm
      _ = Yp⁻¹ := by rw [hYp, mul_inv_rev]
  have hYp3 : Yp ^ 3 = 1 := by
    rw [hYp, ((hYw.pow_right a).symm).mul_pow, hwa3, hY3, one_mul]
  have hpow2 : ∀ x : ↥H ⧸ CFSG.pCore 2 ↥H, x ^ 2 = 1 → ∀ n : ℤ, x ^ n = 1 ∨ x ^ n = x := by
    intro x hx n
    obtain ⟨q, r, hr, hn⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1) ∧ n = 2 * q + r :=
      ⟨n / 2, n % 2, by omega, by omega⟩
    have hx2 : x ^ (2 : ℤ) = 1 := by simpa using hx
    rw [hn, zpow_add, zpow_mul, hx2, one_zpow, one_mul]
    rcases hr with rfl | rfl
    · left; simp
    · right; simp
  have hUN : zpowers U ≤
      normalizer ((zpowers Yp : Subgroup _) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine A5.le_normalizer_of_forall_conj_mem fun l hl x hx => ?_
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hl
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
    rcases hpow2 U hU2 n with h | h
    · rw [h, one_mul, inv_one, mul_one]
      exact zpow_mem_zpowers _ _
    · rw [h, ← conj_zpow, hYpinv, inv_zpow']
      exact zpow_mem_zpowers _ _
  obtain ⟨D, hD⟩ : ∃ X : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), X = zpowers Yp ⊔ zpowers U :=
    ⟨_, rfl⟩
  have hDdec : ∀ d ∈ D, ∃ m n : ℤ, d = Yp ^ m * U ^ n := by
    intro d hd
    have hd' : d ∈ ((zpowers Yp ⊔ zpowers U : Subgroup _) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [← hD]
      exact hd
    rw [coe_mul_of_right_le_normalizer_left _ _ hUN] at hd'
    obtain ⟨a', ha', b', hb', rfl⟩ := hd'
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb'
    exact ⟨m, n, rfl⟩
  have hDHb : D ≤ Hb := hD ▸ sup_le (zpowers_le.2 hYpHb) (zpowers_le.2 hUHb)
  have hDker : ∀ d ∈ D, ψ d = 1 → d = 1 := by
    intro d hd h
    obtain ⟨m, n, rfl⟩ := hDdec d hd
    rw [map_mul, map_zpow, map_zpow, hψYp, hψU] at h
    rcases hpow2 U hU2 n with hn | hn
    · have hτn : τ ^ n = 1 := by
        have := congrArg ψ hn
        rwa [map_zpow, hψU, map_one] at this
      rw [hτn, mul_one] at h
      have h3m : (3 : ℤ) ∣ m := by
        have h3 : ((orderOf y : ℕ) : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.2 h
        rw [hy3] at h3
        exact_mod_cast h3
      obtain ⟨q, rfl⟩ := h3m
      rw [hn, mul_one, zpow_mul, show Yp ^ (3 : ℤ) = 1 by simpa using hYp3, one_zpow]
    · exfalso
      have hτn : τ ^ n = τ := by
        have := congrArg ψ hn
        rwa [map_zpow, hψU] at this
      rw [hτn] at h
      apply hτz
      have : τ = (y ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this, ← zpow_neg]
      exact zpow_mem_zpowers y _
  have hKD : ∀ k ∈ K, ∃ d ∈ D, ψ d = k := by
    have hM : zpowers y ⊔ zpowers τ = K := by
      have hle : zpowers y ⊔ zpowers τ ≤ K := sup_le (zpowers_le.2 hyK) (zpowers_le.2 hτK)
      refine eq_of_le_of_card_ge hle ?_
      have h6 := B.hb.card_eq K hK
      have h3 : 3 ∣ Nat.card ↥(zpowers y ⊔ zpowers τ) := by
        have := card_dvd_of_le (le_sup_left : zpowers y ≤ zpowers y ⊔ zpowers τ)
        rwa [Nat.card_zpowers, hy3] at this
      have h2 : 2 ∣ Nat.card ↥(zpowers y ⊔ zpowers τ) := by
        have := card_dvd_of_le (le_sup_right : zpowers τ ≤ zpowers y ⊔ zpowers τ)
        rwa [Nat.card_zpowers, orderOf_eq_prime hτ2 hτ1] at this
      have h6' : 6 ∣ Nat.card ↥(zpowers y ⊔ zpowers τ) :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
      rw [h6]
      exact Nat.le_of_dvd Nat.card_pos h6'
    have hle : K ≤ D.map ψ := by
      rw [← hM]
      refine sup_le (zpowers_le.2 ⟨Yp, ?_, hψYp⟩) (zpowers_le.2 ⟨U, ?_, hψU⟩)
      · exact hD ▸ mem_sup_left (mem_zpowers Yp)
      · exact hD ▸ mem_sup_right (mem_zpowers U)
    intro k hk
    obtain ⟨d, hd, hdk⟩ := hle hk
    exact ⟨d, hd, hdk⟩
  have h2el : ∀ q ∈ Hb, (∃ k : ℕ, q ^ 2 ^ k = 1) → ψ q ∈ K → q ∈ D := by
    intro q hq ⟨k, hk⟩ hqK
    obtain ⟨d, hd, hdq⟩ := hKD _ hqK
    have hdq' : ψ (d⁻¹ * q) = 1 := by rw [map_mul, map_inv, hdq, inv_mul_cancel]
    obtain ⟨m, hm⟩ := hQHb _ (Hb.mul_mem (Hb.inv_mem (hDHb hd)) hq) hdq'
    have hq' : q = d * w ^ m := by
      calc q = d * (d⁻¹ * q) := by group
        _ = d * w ^ m := by rw [hm]
    have hdw : Commute d (w ^ m) := (hcommHb _ (hDHb hd)).pow_right m
    have h1 : d ^ 2 ^ k * (w ^ m) ^ 2 ^ k = 1 := by
      rw [← hdw.mul_pow, ← hq', hk]
    have hd1 : d ^ 2 ^ k = 1 := by
      refine hDker _ (D.pow_mem hd _) ?_
      have h2 : d ^ 2 ^ k = ((w ^ m) ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [h2, map_inv, map_pow, map_pow, hψw, one_pow, one_pow, inv_one]
    rw [hd1, one_mul] at h1
    have hm3 : (w ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hw3, one_pow]
    have hgcd := pow_gcd_eq_one.2 ⟨hm3, h1⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at hgcd
    rw [hq', hgcd, mul_one]
    exact hd
  have hID : I ≤ (D.comap π).map H.subtype := by
    rw [hIdef, conjClosure, closure_le]
    rintro x ⟨h, hh, j, hj, rfl⟩
    have hjT : j ∈ T := (r1Of_le_T T L V) (hJR hj)
    have hgH : h * j * h⁻¹ ∈ H :=
      mul_mem (mul_mem hh ((s134_inHz_facts S hHz).1.1 hjT)) (inv_mem hh)
    have hgI : h * j * h⁻¹ ∈ I := mem_conjClosure hh hj
    refine ⟨⟨h * j * h⁻¹, hgH⟩, ?_, rfl⟩
    show π ⟨h * j * h⁻¹, hgH⟩ ∈ D
    refine h2el _ (hmemHb _ (hIH₁ hgI)) ?_ ?_
    · obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨j, hjT⟩
      have hk' : j ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine ⟨k, ?_⟩
      rw [← map_pow]
      refine (hπ1 _).2 ?_
      have e : ((⟨h * j * h⁻¹, hgH⟩ ^ 2 ^ k : ↥H) : G) = h * j ^ 2 ^ k * h⁻¹ := by
        simp [conj_pow]
      rw [e, hk', mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [hψπ, ← hIK]
      exact convI_mem_autI _ hgI _
  rintro x ⟨hxI, hxC⟩
  have hxH : x ∈ H := hH₁H (hIH₁ hxI)
  obtain ⟨x', hx', hxx'⟩ := hID hxI
  have hx'eq : x' = ⟨x, hxH⟩ := Subtype.ext hxx'
  rw [hx'eq] at hx'
  have hx'' : π ⟨x, hxH⟩ ∈ D := hx'
  have hψx : ψ (π ⟨x, hxH⟩) = 1 := by
    rw [hψπ, convI_eq_one_iff]
    exact hxC
  exact (hπ1 _).1 (hDker _ hx'' hψx)

end CFSG.Quasithin.H13.U3
