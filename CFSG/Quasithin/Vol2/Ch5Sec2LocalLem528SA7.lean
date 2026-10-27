module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528Blocks
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SKG

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Blueprint
open CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Quasithin.Ch1Four

theorem three_le_pRank_of_indep {Y : Type} [Group Y] [Finite Y] {a b c : Y}
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (hind : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 → a ^ i * b ^ j * c ^ k = 1 →
      i = 0 ∧ j = 0 ∧ k = 0) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  classical
  have ho : ∀ {y : Y}, y ^ 3 = 1 → y ≠ 1 → orderOf y = 3 := fun h1 h2 =>
    orderOf_eq_prime h1 h2
  have ha1 : a ≠ 1 := fun h => by
    have := (hind 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by simp [h])).1
    omega
  have hb1 : b ≠ 1 := fun h => by
    have := (hind 0 1 0 (by norm_num) (by norm_num) (by norm_num) (by simp [h])).2.1
    omega
  have hc1 : c ≠ 1 := fun h => by
    have := (hind 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by simp [h])).2.2
    omega
  have hoa := ho ha ha1
  have hob := ho hb hb1
  have hoc := ho hc hc1
  have hmem : ∀ {y : Y}, orderOf y = 3 → ∀ m : ↥(Subgroup.zpowers y),
      ∃ i : ℕ, i < 3 ∧ (m : Y) = y ^ i := by
    intro y hy m
    obtain ⟨i, hi, hm⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp m.2)
    rw [hy, Finset.mem_range] at hi
    exact ⟨i, hi, hm.symm⟩
  have hcomm' : ∀ {y z : Y}, Commute y z → ∀ (m : ↥(Subgroup.zpowers y))
      (n : ↥(Subgroup.zpowers z)), Commute (m : Y) (n : Y) := by
    intro y z hyz m n
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp m.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp n.2
    rw [← hi, ← hj]
    exact hyz.zpow_zpow i j
  let fab := (Subgroup.zpowers a).subtype.noncommCoprod (Subgroup.zpowers b).subtype
    (fun m n => hcomm' hab m n)
  have hfab : ∀ mn p, Commute (fab mn) ((Subgroup.zpowers c).subtype p) := by
    intro mn p
    simp only [fab, Subgroup.coe_subtype]
    exact (hcomm' hac mn.1 p).mul_left (hcomm' hbc mn.2 p)
  let f := fab.noncommCoprod (Subgroup.zpowers c).subtype hfab
  have hf : ∀ m n p, f ((m, n), p) = (m : Y) * n * p := fun m n p => rfl
  have hcz : ∀ {y : Y} (m n : ↥(Subgroup.zpowers y)), m * n = n * m := fun m n =>
    Subtype.ext (hcomm' (Commute.refl _) m n).eq
  have hpz : ∀ {y : Y}, y ^ 3 = 1 → ∀ m : ↥(Subgroup.zpowers y), m ^ 3 = 1 := by
    intro y hy m
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp m.2
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  refine CFSG.SectionRank.le_pRank_of_injective (A := (↥(Subgroup.zpowers a) ×
      ↥(Subgroup.zpowers b)) × ↥(Subgroup.zpowers c)) (by norm_num) ?_ ?_ ?_ f ?_ le_top
  · rintro ⟨⟨m₁, n₁⟩, p₁⟩ ⟨⟨m₂, n₂⟩, p₂⟩
    exact Prod.ext (Prod.ext (hcz m₁ m₂) (hcz n₁ n₂)) (hcz p₁ p₂)
  · rintro ⟨⟨m, n⟩, p⟩
    exact Prod.ext (Prod.ext (hpz ha m) (hpz hb n)) (hpz hc p)
  · rw [Nat.card_prod, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, Nat.card_zpowers,
      hoa, hob, hoc]
    norm_num
  · rw [injective_iff_map_eq_one]
    rintro ⟨⟨m, n⟩, p⟩ h1
    rw [hf] at h1
    obtain ⟨i, hi, hm⟩ := hmem hoa m
    obtain ⟨j, hj, hn⟩ := hmem hob n
    obtain ⟨k, hk, hp⟩ := hmem hoc p
    rw [hm, hn, hp] at h1
    obtain ⟨rfl, rfl, rfl⟩ := hind i j k hi hj hk h1
    have hm1 : m = 1 := Subtype.ext (by rw [hm, pow_zero]; rfl)
    have hn1 : n = 1 := Subtype.ext (by rw [hn, pow_zero]; rfl)
    have hp1 : p = 1 := Subtype.ext (by rw [hp, pow_zero]; rfl)
    rw [hm1, hn1, hp1]
    rfl

theorem not_a38Types_of_card
    {X : Type} [Group X] (hX : Nat.card X = 2520) : ¬ A38Types X := by
  rintro (⟨n, hn⟩ | ⟨n, hn⟩ | hn | ⟨p, hp, hp3, hn⟩)
  · obtain ⟨hn1, hc⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two hn
    rw [hX, show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num] at hc
    obtain ⟨rfl, h2⟩ := two_pow_mul_odd_inj (by decide) (odd_oSL2 hn1) hc
    exact absurd h2 (by decide)
  · exact not_three_dvd_card_of_isSz hn (by rw [hX]; decide)
  · have hsp : ∀ {s : TauCeti.SporadicName} {N : ℕ}, Nat.card (NativeSporadic.Carrier s) = N →
        IsSporadic s X → Nat.card X = N := fun hN ⟨e⟩ => (Nat.card_congr e.toEquiv).trans hN
    have := hsp (s := .J1) (N := 175560) CFSG.Sporadic.J1.card_J1 hn
    rw [hX] at this
    norm_num at this
  · have h2 := two_mul_card_of_isPSL_two hp (by omega) hn
    rw [hX] at h2
    have hp20 : p < 20 := by
      by_contra h20
      have : 20 * 399 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul (by omega) (by
        have : 400 ≤ p ^ 2 := by nlinarith
        omega)
      omega
    interval_cases p <;> norm_num at h2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_forall_commute_a7 {σ : alternatingGroup (Fin 7)}
    (h : ∀ τ : alternatingGroup (Fin 7), σ * τ = τ * σ) : σ = 1 := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
  have hσ : σ ∈ Subgroup.center (alternatingGroup (Fin 7)) :=
    Subgroup.mem_center_iff.mpr fun τ => (h τ).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 7)))
    with hb | ht
  · rw [hb] at hσ
    exact Subgroup.mem_bot.mp hσ
  · exfalso
    set u : alternatingGroup (Fin 7) :=
      ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    set v : alternatingGroup (Fin 7) :=
      ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    have huv := Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top u) v
    have := congrArg Subtype.val huv
    revert this
    decide

omit [Finite G] in
theorem exists_induced_aut {Kh : Subgroup G} (α : ↥Kh →* alternatingGroup (Fin 7))
    (hαs : Function.Surjective α) (hαk : α.ker = (pCoreOf 2 Kh).subgroupOf Kh) {x : G}
    (hx : x ∈ Subgroup.normalizer (Kh : Set G)) :
    ∃ φ : MulAut (alternatingGroup (Fin 7)), ∀ k : ↥Kh,
      φ (α k) = α ⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx k).mp k.2⟩ := by
  set cx : MulAut ↥Kh := Kh.normalizerMonoidHom ⟨x, hx⟩ with hcx
  have hcxk : ∀ k : ↥Kh, cx k = ⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx k).mp k.2⟩ :=
    fun k => Subtype.ext (by simp [hcx])
  have hxR : x ∈ Subgroup.normalizer (pCoreOf 2 Kh : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 Kh hx
  have hmap : α.ker.map cx.toMonoidHom = α.ker := by
    rw [hαk]
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk
      rw [Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, hcxk]
      exact (Subgroup.mem_normalizer_iff.mp hxR k).mp hk
    · intro k hk
      have hx' : x⁻¹ ∈ Subgroup.normalizer (Kh : Set G) := inv_mem hx
      refine ⟨⟨x⁻¹ * k * x⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp hx' k).mp k.2⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hk
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_normalizer_iff.mp (inv_mem hxR) k).mp hk
      · rw [MulEquiv.coe_toMonoidHom, hcxk]
        apply Subtype.ext
        simp only
        group
  let eA := QuotientGroup.quotientKerEquivOfSurjective α hαs
  let cq : (↥Kh ⧸ α.ker) ≃* (↥Kh ⧸ α.ker) := QuotientGroup.congr α.ker α.ker cx hmap
  refine ⟨eA.symm.trans (cq.trans eA), fun k => ?_⟩
  have h1 : eA.symm (α k) = (k : ↥Kh ⧸ α.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h2 : cq (k : ↥Kh ⧸ α.ker) = ((cx k : ↥Kh) : ↥Kh ⧸ α.ker) :=
    QuotientGroup.congr_mk _ _ _ _ k
  change eA (cq (eA.symm (α k))) = _
  rw [h1, h2, hcxk]
  rfl

theorem false_of_a7_of
    (hqtke : quasithinIsQTKECat G) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hAut : AutA7Fact)
    {T K Kh : Subgroup G} (e : Emb528 T K Kh) (hKh : quasithinIsMaximalLocal T Kh)
    (hQR : pCoreOf 2 K ≤ pCoreOf 2 Kh)
    (hcardK : Nat.card K = 60 * Nat.card (pCoreOf 2 K))
    (hA : Nonempty (ModO2 Kh ≃* alternatingGroup (Fin 7)))
    {x : G} (hx3 : orderOf x = 3) (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K)
    (P₀ : Subgroup G) (hP₀2 : IsPGroup 2 P₀) (hP₀1 : P₀ ≠ ⊥)
    (hKhP : Kh ≤ Subgroup.normalizer (P₀ : Set G)) (hTP : T ≤ Subgroup.normalizer (P₀ : Set G))
    (hxP : x ∈ Subgroup.normalizer (P₀ : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := pCoreOf 2 K with hQdef
  set R := pCoreOf 2 Kh with hRdef
  obtain ⟨eA⟩ := hA
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 Kh
  have hxx : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hpR : CFSG.pCore 2 ↥Kh = R.subgroupOf Kh := pCore_eq_subgroupOf rfl
  set α : ↥Kh →* alternatingGroup (Fin 7) :=
    eA.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Kh)) with hα
  have hαs : Function.Surjective α := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hαk : α.ker = R.subgroupOf Kh := by
    rw [← hpR]
    ext k
    rw [MonoidHom.mem_ker, hα, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ eA.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hαR : ∀ k : ↥Kh, α k = 1 ↔ (k : G) ∈ R := fun k => by
    rw [← MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]
  set N₀ := Subgroup.normalizer (P₀ : Set G) with hN₀
  have hPN₀ : P₀ ≤ pCoreOf 2 N₀ :=
    le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hP₀2
  have hInH : InH (Kh ⊔ T) N₀ := ⟨sup_le hKhP hTP, fun h => hP₀1 (le_bot_iff.mp (h ▸ hPN₀))⟩
  have hKhC : Kh ∈ cComp N₀ := lemma_1_2_7_one hqtke hs hnab h37 h39 e.sylow hKh hInH
  have hcardA : Nat.card (ModO2 Kh) = 2520 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hxKh : x ∈ Subgroup.normalizer (Kh : Set G) := by
    rcases CFSG.Quasithin.lemma_1_2_1_three hqtke hs hnab h37 h38 hInH.2 hKhC with hn | ⟨-, ht⟩
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hInH.1)).mp hn hxP
    · exact (not_a38Types_of_card hcardA ht).elim
  obtain ⟨φ, hφ⟩ := exists_induced_aut α hαs hαk hxKh
  have hφ3 : φ ^ 3 = 1 := by
    refine MulEquiv.ext fun σ => ?_
    obtain ⟨k, rfl⟩ := hαs σ
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, hφ, hφ, hφ, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    change x * (x * (x * (k : G) * x⁻¹) * x⁻¹) * x⁻¹ = k
    have hxx' : x * (x * x) = 1 := by rw [← pow_three]; exact hxx
    calc x * (x * (x * (k : G) * x⁻¹) * x⁻¹) * x⁻¹ = (x * (x * x)) * k * (x * (x * x))⁻¹ := by
          group
      _ = k := by rw [hxx']; group
  have hKR : K ⊓ R = Q := by
    refine le_antisymm ?_ (le_inf (pCoreOf_le 2 K) hQR)
    exact (inf_le_inf_left K (e.pCoreOf_le_sup h37)).trans e.inf_le_blockQ
  set H : Subgroup (alternatingGroup (Fin 7)) := (K.subgroupOf Kh).map α with hH
  have hHcard : Nat.card H = 60 := by
    have h1 := card_modO2Image_mul (H := Kh) e.le
    rw [hKR, hcardK] at h1
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have h2 : Nat.card ↥(modO2Image Kh K) = 60 := Nat.eq_of_mul_eq_mul_right hpos h1
    have h3 : H = (modO2Image Kh K).map eA.toMonoidHom := by
      rw [hH, hα, ← Subgroup.map_map]
      rfl
    rw [h3, Subgroup.card_map_of_injective eA.injective, h2]
  have hφH : ∀ h ∈ H, φ h = h := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hφ]
    have hk' : (k : G) ∈ K := hk
    have hc : x * k * x⁻¹ * (k : G)⁻¹ ∈ R := hQR (hxK k hk')
    have e1 : (⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxKh k).mp k.2⟩ : ↥Kh) =
        ⟨x * k * x⁻¹ * (k : G)⁻¹, (pCoreOf_le 2 Kh) hc⟩ * k :=
      Subtype.ext (by simp)
    rw [e1, map_mul, (hαR _).mpr hc, one_mul]
  have hφ1 : φ = 1 := hAut φ hφ3 H hHcard hφH
  have hxc : ∀ k : ↥Kh, x * k * x⁻¹ * (k : G)⁻¹ ∈ R := by
    intro k
    have h1 := hφ k
    rw [hφ1, MulAut.one_apply] at h1
    have h2 := (MonoidHom.eq_iff α).mp h1.symm
    rw [hαk, Subgroup.mem_subgroupOf] at h2
    have h2' : (k : G)⁻¹ * (x * k * x⁻¹) ∈ R := by simpa using h2
    have e1 : x * k * x⁻¹ * (k : G)⁻¹ = (k : G) * ((k : G)⁻¹ * (x * k * x⁻¹)) * (k : G)⁻¹ := by
      group
    rw [e1]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Kh k.2) _).mp h2'
  have hxnKh : x ∉ Kh := by
    intro hx
    have hcent : ∀ τ : alternatingGroup (Fin 7), α ⟨x, hx⟩ * τ = τ * α ⟨x, hx⟩ := by
      intro τ
      obtain ⟨k, rfl⟩ := hαs τ
      have h1 := hφ k
      rw [hφ1, MulAut.one_apply] at h1
      have e1 : (⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxKh k).mp k.2⟩ : ↥Kh) =
          ⟨x, hx⟩ * k * ⟨x, hx⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv] at h1
      calc α ⟨x, hx⟩ * α k = (α ⟨x, hx⟩ * α k * (α ⟨x, hx⟩)⁻¹) * α ⟨x, hx⟩ := by group
        _ = α k * α ⟨x, hx⟩ := by rw [← h1]
    have h1 := eq_one_of_forall_commute_a7 hcent
    have hxR : x ∈ R := (hαR ⟨x, hx⟩).mp h1
    obtain ⟨t, ht⟩ := hR2 ⟨x, hxR⟩
    have ht' : x ^ 2 ^ t = 1 := congrArg Subtype.val ht
    have hd := orderOf_dvd_of_pow_eq_one ht'
    rw [hx3] at hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  set J := Kh ⊔ Subgroup.zpowers x with hJ
  have hxR' : x ∈ Subgroup.normalizer (R : Set G) := normalizer_le_normalizer_pCoreOf 2 Kh hxKh
  have hJR : J ≤ Subgroup.normalizer (R : Set G) :=
    sup_le (le_normalizer_pCoreOf 2 Kh) ((Subgroup.zpowers_le).mpr hxR')
  have hRJ : R ≤ J := (pCoreOf_le 2 Kh).trans le_sup_left
  have hKhJ : Kh ≤ J := le_sup_left
  have hxJ : x ∈ J := (le_sup_right : Subgroup.zpowers x ≤ J) (Subgroup.mem_zpowers x)
  have hJN₀ : J ≤ N₀ := sup_le hKhP ((Subgroup.zpowers_le).mpr hxP)
  set R' := R.subgroupOf J with hR'
  have : R'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRJ).mpr hJR
  let π := QuotientGroup.mk' R'
  have hπ : ∀ g : ↥J, π g = 1 ↔ (g : G) ∈ R := fun g => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hR', Subgroup.mem_subgroupOf]
  set σ₁ : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ with hσ₁
  set σ₂ : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ with hσ₂
  obtain ⟨a, ha⟩ := hαs σ₁
  obtain ⟨b, hb⟩ := hαs σ₂
  set a' : ↥J := ⟨a, hKhJ a.2⟩ with ha'
  set b' : ↥J := ⟨b, hKhJ b.2⟩ with hb'
  set x' : ↥J := ⟨x, hxJ⟩ with hx'
  have hRmem : ∀ k : ↥Kh, α k = 1 → (k : G) ∈ R := fun k h => (hαR k).mp h
  have hab : Commute (π a') (π b') := by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, hπ]
    have : α (a * b * (b * a)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, ha, hb]
      apply Subtype.ext
      decide
    exact hRmem _ this
  have hcx : ∀ k : ↥Kh, Commute (π ⟨k, hKhJ k.2⟩) (π x') := by
    intro k
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, hπ]
    have h1 := hxc k
    have e1 : ((⟨k, hKhJ k.2⟩ * x' * (x' * ⟨k, hKhJ k.2⟩)⁻¹ : ↥J) : G) =
        (x * k * x⁻¹ * (k : G)⁻¹)⁻¹ := by
      simp only [hx', Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1]
    exact inv_mem h1
  have hcub : ∀ k : ↥Kh, α k ^ 3 = 1 → π ⟨k, hKhJ k.2⟩ ^ 3 = 1 := by
    intro k hk
    rw [← map_pow, hπ]
    have : α (k ^ 3) = 1 := by rw [map_pow, hk]
    have h1 := hRmem _ this
    simpa using h1
  have ha3 : π a' ^ 3 = 1 := hcub a (by rw [ha]; apply Subtype.ext; decide)
  have hb3 : π b' ^ 3 = 1 := hcub b (by rw [hb]; apply Subtype.ext; decide)
  have hx3' : π x' ^ 3 = 1 := by
    rw [← map_pow]
    have : x' ^ 3 = 1 := Subtype.ext (by simp [hx', hxx])
    rw [this, map_one]
  have hind : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 → π a' ^ i * π b' ^ j * π x' ^ k = 1 →
      i = 0 ∧ j = 0 ∧ k = 0 := by
    intro i j k hi hj hk h1
    rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul, hπ] at h1
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow, ha', hb', hx'] at h1
    have hxk : x ^ k ∈ Kh := by
      have : x ^ k = ((a : G) ^ i * (b : G) ^ j)⁻¹ * ((a : G) ^ i * (b : G) ^ j * x ^ k) := by
        group
      rw [this]
      exact Kh.mul_mem (Kh.inv_mem (Kh.mul_mem (Kh.pow_mem a.2 i) (Kh.pow_mem b.2 j)))
        ((pCoreOf_le 2 Kh) h1)
    have hk0 : k = 0 := by
      interval_cases k
      · rfl
      · exact (hxnKh (by simpa using hxk)).elim
      · exfalso
        apply hxnKh
        have : x = (x ^ 2) ^ 2 := by
          calc x = x ^ 3 * x := by rw [hxx, one_mul]
            _ = (x ^ 2) ^ 2 := by group
        rw [this]
        exact Kh.pow_mem hxk 2
    subst hk0
    simp only [pow_zero, mul_one] at h1
    have h2 : α (a ^ i * b ^ j) = 1 := (hαR _).mpr (by simpa using h1)
    rw [map_mul, map_pow, map_pow, ha, hb] at h2
    refine ⟨?_, ?_, rfl⟩ <;>
    · interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; revert h2; decide)
  have h3 := three_le_pRank_of_indep hab (hcx a) (hcx b) ha3 hb3 hx3' hind
  have hR'3 : ¬ 3 ∣ Nat.card R' := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRJ).toEquiv]
    obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp hR2
    rw [ht]
    intro h
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)) (by norm_num)
  have h4 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥J ⧸ R')) = CFSG.Open.pRank 3 J := by
    rw [CFSG.SectionRank.pRank_quotient_eq R' hR'3]
    exact pRank_top_subtype J
  have h5 : CFSG.Open.pRank 3 J ≤ CFSG.Open.pRank 3 N₀ :=
    CFSG.SectionRank.pRank_mono (by norm_num) hJN₀
  have hloc : CFSG.Open.IsTwoLocal N₀ := ⟨P₀, hP₀1, hP₀2, rfl⟩
  have h6 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) N₀ hloc
  have h7 : CFSG.Open.evenRank G ≤ 2 := hqtke.2.2
  omega

end CFSG.Quasithin.H13
