module

public import CFSG.Quasithin.Vol2.KGFactC31RuScan
public import CFSG.Quasithin.Vol2.KGFactC31RuTypeE
public import CFSG.Quasithin.Vol2.KGFactC31RuType64
public import CFSG.Quasithin.Vol2.KGFactC31RuType32

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.LieType.BorelTits CFSG.Sporadic.RuSchreier
  CFSG.Quasithin.KGC31

theorem pow_eq_one_of_not_dvd {G : Type*} [Group G] [Finite G] {y : G} {p k m : ℕ}
    (hp : p.Prime) (hy : y ^ p ^ k = 1) (hm : ¬ p ^ (m + 1) ∣ Nat.card G) : y ^ p ^ m = 1 := by
  have h1 : orderOf y ∣ p ^ k := orderOf_dvd_of_pow_eq_one hy
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow hp).mp h1
  have h2 : p ^ j ∣ Nat.card G := hjo ▸ orderOf_dvd_natCard y
  have hjm : j ≤ m := by
    by_contra hlt
    exact hm ((Nat.pow_dvd_pow p (by omega)).trans h2)
  rw [← orderOf_dvd_iff_pow_eq_one, hjo]
  exact Nat.pow_dvd_pow p hjm

theorem prime_dvd_ru {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 145926144000) :
    p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 29 := by
  have h' : p ∣ 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
        · rcases (Nat.Prime.dvd_mul hp).mp h4 with h5 | h5
          · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h5); omega
          · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h5); omega
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h4))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1)))

variable {A : Type} [Group A]

theorem img_orbSub (e : G₀ ≃* A) (y t : G₀) :
    img e (orbSub (y : Equiv.Perm (Fin 4060)) t) = orbSub (e y) (e t) := by
  have h1 : orbSub (y : Equiv.Perm (Fin 4060)) t = (orbSub y t).map ruP.subtype :=
    (orbSub_map ruP.subtype y t).symm
  rw [img, h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
    ruP.subtype_injective, orbSub_map]
  rfl

theorem card_G₀ :
    Nat.card G₀ = 145926144000 := card_ruP'

section Reduction

variable [Finite A]

theorem exists_ref {M₀ R M V : Subgroup A} (h : RuHyp M₀ R M V) (e : G₀ ≃* A) :
    ∃ e' : G₀ ≃* A, ∃ τ' < 5, ∃ y' : G₀, img e' (refU τ') ≤ V ∧ e' y' ∈ M₀ ∧
      (y' : Equiv.Perm (Fin 4060)) ∈
        Subgroup.normalizer (refU τ' : Set (Equiv.Perm (Fin 4060))) ∧ y' ≠ 1 ∧
      ((refPrime τ' = 5 ∧ y' ^ 5 ^ 3 = 1) ∨ (refPrime τ' = 7 ∧ y' ^ 7 ^ 1 = 1)) := by
  have hne : ⁅V, M₀⁆ ≠ ⊥ := by rw [h.comm]; exact h.Vne
  obtain ⟨p, hp, hp5, y, hy, ⟨k, hyk⟩, t, ht, hyt⟩ := exists_pElement_not_comm h.per h.M₀V hne
  set y₀ := e.symm y with hy₀
  set t₀ := e.symm t with ht₀
  have hey : e y₀ = y := by simp [hy₀]
  have het : e t₀ = t := by simp [ht₀]
  have ht2 : orderOf (t₀ : Equiv.Perm (Fin 4060)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ fun h1 => hyt ?_
    · have h2 := h.V_sq t ht
      rw [← het, ← map_mul, ← map_one e] at h2
      rw [sq]
      exact congrArg Subtype.val (e.injective h2)
    · have : t₀ = 1 := Subtype.ext h1
      rw [← het, this, map_one, mul_one, mul_inv_cancel]
  have hinv : (t₀ : Equiv.Perm (Fin 4060)) ∈ ruZP ∪ ruAP := by
    rw [← ruInvolutions_eq]
    exact ⟨t₀.2, ht2⟩
  obtain ⟨τ, hτ, g, hg, hgt⟩ : ∃ τ, (τ = ruZ ∨ τ = ruA0) ∧ ∃ g ∈ ruP,
      g * τ * g⁻¹ = (t₀ : Equiv.Perm (Fin 4060)) := by
    rcases hinv with ⟨g, hg, hgt⟩ | ⟨g, hg, hgt⟩
    · exact ⟨ruZ, Or.inl rfl, g, hg, hgt⟩
    · exact ⟨ruA0, Or.inr rfl, g, hg, hgt⟩
  have hτP : τ ∈ ruP := by rcases hτ with rfl | rfl; exacts [ruZ_mem, ruA0_mem]
  set e₁ := conjE e ⟨g, hg⟩ with he₁
  set τ₀ : G₀ := ⟨τ, hτP⟩
  set y₁ : G₀ := (⟨g, hg⟩ : G₀)⁻¹ * y₀ * ⟨g, hg⟩ with hy₁
  have he₁τ : e₁ τ₀ = t := by
    rw [he₁, conjE_apply, ← het]
    congr 1
    exact Subtype.ext hgt
  have he₁y : e₁ y₁ = y := by
    rw [he₁, conjE_apply, hy₁, ← hey]
    congr 1
    group
  set Y : Equiv.Perm (Fin 4060) := (y₁ : Equiv.Perm (Fin 4060)) with hY
  have hYP : Y ∈ ruP := y₁.2
  have hmove : Y * τ * Y⁻¹ ≠ τ := by
    intro hm
    apply hyt
    have : y₁ * τ₀ * y₁⁻¹ = τ₀ := Subtype.ext hm
    rw [← he₁y, ← he₁τ, ← map_inv, ← map_mul, ← map_mul, this]
  have hV₁ : ∀ a ∈ pb e₁ V, ∀ b ∈ pb e₁ V, a * b = b * a := by
    intro a ha b hb
    obtain ⟨haP, haV⟩ := (mem_pb e₁).mp ha
    obtain ⟨hbP, hbV⟩ := (mem_pb e₁).mp hb
    have := h.V_comm _ haV _ hbV
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (e₁.injective this)
  have hτV : τ ∈ pb e₁ V := (apply_mem_iff_mem_pb e₁ (g := τ₀)).mp (he₁τ ▸ ht)
  have hYN : Y ∈ Subgroup.normalizer (pb e₁ V : Set (Equiv.Perm (Fin 4060))) :=
    pb_le_normalizer e₁ h.M₀V ((apply_mem_iff_mem_pb e₁ (g := y₁)).mp (he₁y ▸ hy))
  have hcomm : ∀ j : ℕ, τ * (Y ^ j * τ * (Y ^ j)⁻¹) = Y ^ j * τ * (Y ^ j)⁻¹ * τ := by
    intro j
    have hc : Y ^ j * τ * (Y ^ j)⁻¹ ∈ pb e₁ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hYN j) τ).mp hτV
    exact hV₁ τ hτV _ hc
  have hY1 : y₁ ≠ 1 := by
    intro h1
    apply hmove
    rw [hY, h1]
    simp
  have hYk : y₁ ^ p ^ k = 1 := by
    apply e₁.injective
    rw [map_pow, he₁y, hyk, map_one]
  have hpd : p ∣ 145926144000 := by
    by_contra hpd
    have h1 := pow_eq_one_of_not_dvd hp hYk (m := 0) (by rw [card_G₀, zero_add, pow_one]; exact hpd)
    rw [pow_zero, pow_one] at h1
    exact hY1 h1
  have hZA := hτ
  obtain ⟨hs5, hs7, hs13⟩ :
      ([125], 5) ∈ ruGroups ∧ ([7], 7) ∈ ruGroups ∧ ([13, 29], 0) ∈ ruGroups := by
    simp [ruGroups]
  have hbad : ∀ {es : List ℕ} {q : ℕ}, (es, q) ∈ ruGroups →
      (∃ e ∈ es, Y ^ e = 1) → BadConcl Y τ q := by
    intro es q hs he
    rcases hZA with rfl | rfl
    · exact classifyZ hYP hmove hs he hcomm
    · exact classifyA hYP hmove hs he hcomm
  have key : ∀ {q : ℕ}, BadConcl Y τ q → ∃ e' : G₀ ≃* A, ∃ τ' < 5, ∃ y' : G₀,
      refPrime τ' = q ∧ img e' (refU τ') ≤ V ∧ e' y' ∈ M₀ ∧
      (y' : Equiv.Perm (Fin 4060)) ∈
        Subgroup.normalizer (refU τ' : Set (Equiv.Perm (Fin 4060))) ∧ y' ≠ 1 ∧
      ∀ m : ℕ, y₁ ^ m = 1 → y' ^ m = 1 := by
    intro q hb
    obtain ⟨g', hg', c, hc, hq, hle, hn⟩ := hb
    refine ⟨conjE e₁ ⟨g', hg'⟩, c.1, candData_lt c hc, (⟨g', hg'⟩ : G₀)⁻¹ * y₁ * ⟨g', hg'⟩, hq,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [img_conjE]
      refine (img_mono e₁ hle).trans ?_
      rw [show Y = ((y₁ : G₀) : Equiv.Perm (Fin 4060)) from rfl,
        show τ = ((τ₀ : G₀) : Equiv.Perm (Fin 4060)) from rfl, img_orbSub, he₁y, he₁τ]
      exact orbSub_le (h.M₀V hy) ht
    · rw [conjE_apply, show (⟨g', hg'⟩ : G₀) * ((⟨g', hg'⟩ : G₀)⁻¹ * y₁ * ⟨g', hg'⟩) *
        (⟨g', hg'⟩ : G₀)⁻¹ = y₁ by group, he₁y]
      exact hy
    · simpa using hn
    · intro h1
      apply hY1
      have : y₁ = ⟨g', hg'⟩ * ((⟨g', hg'⟩ : G₀)⁻¹ * y₁ * ⟨g', hg'⟩) * (⟨g', hg'⟩ : G₀)⁻¹ := by
        group
      rw [this, h1]
      group
    · intro m hm
      have e1 : (⟨g', hg'⟩ : G₀)⁻¹ * y₁ * ⟨g', hg'⟩ =
          (⟨g', hg'⟩ : G₀)⁻¹ * y₁ * ((⟨g', hg'⟩ : G₀)⁻¹)⁻¹ := by rw [inv_inv]
      rw [e1, conj_pow, hm]
      group
  rcases prime_dvd_ru hp hp5 hpd with rfl | rfl | rfl | rfl
  ·
    have h5 : y₁ ^ 5 ^ 3 = 1 := pow_eq_one_of_not_dvd hp hYk (m := 3)
      (by rw [card_G₀]; norm_num)
    obtain ⟨e', τ', hτ', y', hq, hUV, hyM, hyN, hy1, hpow⟩ :=
      key (hbad hs5 ⟨125, List.mem_singleton_self _, by simpa using congrArg Subtype.val h5⟩)
    exact ⟨e', τ', hτ', y', hUV, hyM, hyN, hy1, Or.inl ⟨hq, hpow _ h5⟩⟩
  ·
    have h7 : y₁ ^ 7 ^ 1 = 1 := pow_eq_one_of_not_dvd hp hYk (m := 1)
      (by rw [card_G₀]; norm_num)
    obtain ⟨e', τ', hτ', y', hq, hUV, hyM, hyN, hy1, hpow⟩ :=
      key (hbad hs7 ⟨7, List.mem_singleton_self _, by simpa using congrArg Subtype.val h7⟩)
    exact ⟨e', τ', hτ', y', hUV, hyM, hyN, hy1, Or.inr ⟨hq, hpow _ h7⟩⟩
  ·
    have h13 : y₁ ^ 13 ^ 1 = 1 := pow_eq_one_of_not_dvd hp hYk (m := 1)
      (by rw [card_G₀]; norm_num)
    obtain ⟨e', τ', hτ', y', hq, -⟩ :=
      key (hbad hs13 ⟨13, by simp, by simpa using congrArg Subtype.val h13⟩)
    exfalso
    unfold refPrime at hq
    split_ifs at hq
  ·
    have h29 : y₁ ^ 29 ^ 1 = 1 := pow_eq_one_of_not_dvd hp hYk (m := 1)
      (by rw [card_G₀]; norm_num)
    obtain ⟨e', τ', hτ', y', hq, -⟩ :=
      key (hbad hs13 ⟨29, by simp, by simpa using congrArg Subtype.val h29⟩)
    exfalso
    unfold refPrime at hq
    split_ifs at hq

end Reduction

section Main


theorem exists_equiv [Finite A] {S : Subgroup A} (hSn : S.Normal) (hSs : IsSporadic .Ru ↥S)
    (hCS : Subgroup.centralizer (S : Set A) = ⊥) :
    Nonempty (G₀ ≃* A) ∧ S = ⊤ ∧ Subgroup.center ↥S = ⊥ := by
  obtain ⟨e₀⟩ := id hSs
  let eS : ↥S ≃* G₀ := e₀.trans ruEquivP
  have hA : Nat.card A ≤ Nat.card S :=
    calc Nat.card A ≤ Nat.card (MulAut ↥S) := card_le_card_mulAut hSn hCS
      _ = Nat.card (MulAut G₀) := Nat.card_congr (MulAut.congr eS).toEquiv
      _ = Nat.card G₀ := (Nat.card_congr (Equiv.ofBijective _ conj_bijective)).symm
      _ = Nat.card S := Nat.card_congr eS.toEquiv.symm
  have hStop : S = ⊤ :=
    Subgroup.eq_top_of_card_eq S (le_antisymm (Subgroup.card_le_card_group S) hA)
  refine ⟨⟨eS.symm.trans ((MulEquiv.subgroupCongr hStop).trans Subgroup.topEquiv)⟩, hStop, ?_⟩
  have hZ : (Subgroup.center ↥S).map eS.toMonoidHom = Subgroup.center G₀ :=
    Subgroup.map_center_eq eS
  rw [center_ruP] at hZ
  exact (Subgroup.map_eq_bot_iff_of_injective _ eS.injective).mp hZ

theorem config_ru {A : Type} [Group A] [Finite A] (S M₀ R M V : Subgroup A) (hSn : S.Normal)
    (hSs : IsSporadic .Ru ↥S) (hCS : Subgroup.centralizer (S : Set A) = ⊥) (h : RuHyp M₀ R M V) :
    ∃ e : G₀ ≃* A, (V = img e ruESub ∧ M₀ = img e ruN ∧ R = img e ruK) ∨
      (V = img e u64 ∧ M₀ = img e M64 ∧ R = V) := by
  obtain ⟨⟨e⟩, -, -⟩ := exists_equiv hSn hSs hCS
  obtain ⟨e', τ', hτ', y', hUV, hyM, hyN, hy1, hp⟩ := exists_ref h e
  interval_cases τ'
  · rcases hp with ⟨hp, -⟩ | ⟨-, hy7⟩
    · simp [refPrime] at hp
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hyN' : (y' : Equiv.Perm (Fin 4060)) ∈ ruN := by
      rw [← ruN_eq_normalizer_E, ← uE_eq]
      exact ⟨y'.2, hyN⟩
    obtain ⟨n, hnN, hxM⟩ := exists_conj_std e' ruN_le xE_memN orderOf_xE
      (by rw [card_ruN]; norm_num) hyN' ⟨1, hy7⟩ hy1 hyM
    have hnE : ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060)) ∈
        Subgroup.normalizer (uE : Set (Equiv.Perm (Fin 4060))) := by
      have h1 : ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060)) ∈ ruN := by simpa using ruN.inv_mem hnN
      rw [← ruN_eq_normalizer_E, ← uE_eq] at h1
      exact h1.2
    have hEV : img (conjE e' n⁻¹) uE ≤ V := by
      have e1 : uE.map (MulAut.conj ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060))).toMonoidHom = uE :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hnE
      rw [img_conjE, e1]
      exact hUV
    obtain ⟨hV, -, hM, hR⟩ := config_E h (conjE e' n⁻¹) hEV hxM
    refine ⟨conjE e' n⁻¹, Or.inl ⟨by rw [hV, uE_eq], hM, ?_⟩⟩
    have hK : ruP ⊓ Subgroup.centralizer (uE : Set (Equiv.Perm (Fin 4060))) = ruK := by
      rw [uE_eq]
      exact ruP_centralizer_E
    rw [hR, centralizer_img _ (refSub_le_ruP _)]
    exact congrArg (img _) hK
  · obtain ⟨hV, -, hM, hR, -⟩ := config_64 h e' (refSub_le_ruP _) hUV centralizer64_le
    exact ⟨e', Or.inr ⟨hV, hM, hR.trans hV.symm⟩⟩
  · obtain ⟨hV, -, hM, hR, -⟩ := config_64 h e' (refSub_le_ruP _) hUV centralizer3_le
    exact ⟨e', Or.inr ⟨hV, hM, hR.trans hV.symm⟩⟩
  · rcases hp with ⟨-, hy5⟩ | ⟨hp, -⟩
    · exact (false_u16 h e' hUV hyM hyN ⟨3, hy5⟩ hy1).elim
    · simp [refPrime] at hp
  · rcases hp with ⟨-, hy5⟩ | ⟨hp, -⟩
    · exact (false_u32 h e' hUV hyM hyN ⟨3, hy5⟩ hy1).elim
    · simp [refPrime] at hp

theorem config_ru_insp {A : Type} [Group A] [Finite A] (S M₀ R M V : Subgroup A)
    (hSn : S.Normal) (hSs : IsSporadic .Ru ↥S) (hCS : Subgroup.centralizer (S : Set A) = ⊥)
    (_hM₀S : M₀ ≤ S) (hper : ⁅M₀, M₀⁆ = M₀) (_hM₀ne : M₀ ≠ ⊥)
    (_hL : ∃ L ∈ cComp M, M₀ = conjClosure L M) (hR2 : IsPGroup 2 ↥R) (hRM : R ≤ M)
    (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A))
    (hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀)))
    (hVM₀ : V ≤ M₀) (hVne : V ≠ ⊥) (hV : IsElemAbelian 2 V) (hcomm : ⁅V, M₀⁆ = V)
    (hVc : V ≤ CFSG.Quasithin.centerOf (pCoreOf 2 (M₀ ⊔ R)))
    (_hNVM : Subgroup.normalizer (V : Set A) ⊓ Subgroup.normalizer (M₀ : Set A) ≤ M)
    (hNR : Subgroup.normalizer (R : Set A) ≤ M) (_hSM : ¬ S ≤ M) :
    ∃ e : G₀ ≃* A, (V = img e ruESub ∧ M₀ = img e ruN ∧ R = img e ruK) ∨
      (V = img e u64 ∧ M₀ = img e M64 ∧ R = V) :=
  config_ru S M₀ R M V hSn hSs hCS
    ⟨hper, hR2, hRM, hMN, hM₀R, hsyl, hVM₀, hVne, hV, hcomm, hVc, hNR⟩

theorem inspC31SporadicAt_ru : CFSG.Quasithin.InspC31SporadicAt .Ru := by
  intro A _ _ S M₀ R M V hSn hSs hCS hM₀S hper _ _ hR2 hRM hMN hM₀R hsyl hVM₀ hVne hV hcomm hVc
    _ hNR _
  obtain ⟨⟨e⟩, -, hcS⟩ := exists_equiv hSn hSs hCS
  have h : RuHyp M₀ R M V := ⟨hper, hR2, hRM, hMN, hM₀R, hsyl, hVM₀, hVne, hV, hcomm, hVc, hNR⟩
  obtain ⟨e', τ', hτ', y', hUV, hyM, hyN, hy1, hp⟩ := exists_ref h e
  interval_cases τ'
  · rcases hp with ⟨hp, -⟩ | ⟨-, hy7⟩
    · simp [refPrime] at hp
    · exact concl_E hSs hcS hM₀S h e' hUV hyM hyN ⟨1, hy7⟩ hy1
  · exact concl_64 hSs hcS hM₀S h e' (refSub_le_ruP _) hUV centralizer64_le
  · exact concl_64 hSs hcS hM₀S h e' (refSub_le_ruP _) hUV centralizer3_le
  · rcases hp with ⟨-, hy5⟩ | ⟨hp, -⟩
    · exact (false_u16 h e' hUV hyM hyN ⟨3, hy5⟩ hy1).elim
    · simp [refPrime] at hp
  · rcases hp with ⟨-, hy5⟩ | ⟨hp, -⟩
    · exact (false_u32 h e' hUV hyM hyN ⟨3, hy5⟩ hy1).elim
    · simp [refPrime] at hp

end Main

end CFSG.Quasithin.KGC31.Ru

end
