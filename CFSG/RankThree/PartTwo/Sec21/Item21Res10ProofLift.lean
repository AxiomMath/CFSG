module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res10ProofCore
public import CFSG.RankThree.PartTwo.Sec21.Implications
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof

open CFSG CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Subgroup
open scoped Pointwise

section General

variable {G : Type*} [Group G] [Finite G]

theorem card_comap_mk_theta {H : Type*} [Group H] [Finite H]
    (K : Subgroup (H ⧸ aschbacherSolvableCore 3 H)) :
    Nat.card (K.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) =
      Nat.card K * Nat.card (aschbacherSolvableCore 3 H) := by
  set θ := aschbacherSolvableCore 3 H
  have h1 := Subgroup.card_mul_index (K.comap (QuotientGroup.mk' θ))
  have h2 : (K.comap (QuotientGroup.mk' θ)).index = K.index :=
    Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective θ)
  have h3 := Subgroup.card_mul_index K
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  rw [h2] at h1
  rw [← h3] at h4
  have : Nat.card (K.comap (QuotientGroup.mk' θ)) * K.index =
      Nat.card K * Nat.card θ * K.index := by rw [h1, h4]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem card_map_eq_of_injOn' {M M' : Type*} [Group M] [Group M'] (f : M →* M')
    {S : Subgroup M} (h : Set.InjOn f S) : Nat.card (S.map f) = Nat.card S := by
  have := Nat.card_image_of_injOn h
  rw [← Subgroup.coe_map] at this
  exact this

theorem exists_sylow_two_normalized {Γ B : Subgroup G} (hN : B ≤ normalizer (Γ : Set G))
    (hB : IsPGroup 3 B) (h3 : ¬ 3 ∣ Nat.card Γ) :
    ∃ P : Sylow 2 Γ, ∀ a ∈ B, ∀ x : Γ, x ∈ P → ∃ y : Γ, y ∈ P ∧ (y : G) = a * x * a⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : MulDistribMulAction B Γ := MulDistribMulAction.compHom Γ (Subgroup.inclusion hN)
  obtain ⟨sample⟩ := Sylow.nonempty (p := 2) (G := Γ)
  have hnd : ¬ 3 ∣ Nat.card (Sylow 2 Γ) := fun h =>
    h3 (h.trans (sample.card_dvd_index.trans (sample : Subgroup Γ).index_dvd_card))
  obtain ⟨P, hP⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 Γ) hnd
  refine ⟨P, fun a ha x hx => ?_⟩
  have hfix : (⟨a, ha⟩ : B) • P = P := hP ⟨a, ha⟩
  have hmem : (⟨a, ha⟩ : B) • x ∈ (⟨a, ha⟩ : B) • (P : Subgroup Γ) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hx
  have hsub : ((⟨a, ha⟩ : B) • P : Sylow 2 Γ).toSubgroup = (⟨a, ha⟩ : B) • (P : Subgroup Γ) :=
    Sylow.pointwise_smul_def
  have hP' : (⟨a, ha⟩ : B) • (P : Subgroup Γ) = (P : Subgroup Γ) := by
    rw [← hsub, hfix]
  rw [hP'] at hmem
  exact ⟨(⟨a, ha⟩ : B) • x, hmem, rfl⟩

theorem eq_one_of_two_pow_of_odd {Q : Type*} [Group Q] {N : Subgroup Q}
    (hN : Odd (Nat.card N)) {x : Q} (hx : x ∈ N) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

end General

section Bar

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev barMap (L : Subgroup G) : ↥L →* lBar L :=
  QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)

theorem bar_data {L B : Subgroup G} (hBL : B ≤ L) (hB3 : IsPGroup 3 B) (hB9 : Nat.card B = 9)
    {d : G} (hdB : d ∈ B) (hd1 : d ≠ 1)
    (h27 : 27 ∣ Nat.card (L ⊓ centralizer ({d} : Set G) : Subgroup G)) {a : G} (haB : a ∈ B)
    (had : a ∉ zpowers d) :
    Nat.card ((B.subgroupOf L).map (barMap L)) = 9 ∧
      barMap L ⟨d, hBL hdB⟩ ∈ (B.subgroupOf L).map (barMap L) ∧ barMap L ⟨d, hBL hdB⟩ ≠ 1 ∧
      27 ∣ Nat.card (centralizer ({barMap L ⟨d, hBL hdB⟩} : Set (lBar L))) ∧
      barMap L ⟨a, hBL haB⟩ ∈ (B.subgroupOf L).map (barMap L) ∧
      barMap L ⟨a, hBL haB⟩ ∉ zpowers (barMap L ⟨d, hBL hdB⟩) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := barMap L with hπ
  set B' := B.subgroupOf L with hB'
  have hB'3 : IsPGroup 3 B' := hB3.comap_subtype
  have hinj : Set.InjOn π (B' : Set ↥L) := injOn_mk_of_isPGroup Nat.prime_three hB'3
  set d' : ↥L := ⟨d, hBL hdB⟩ with hd'
  set a' : ↥L := ⟨a, hBL haB⟩ with ha'
  have hd'B : d' ∈ B' := mem_subgroupOf.mpr hdB
  have ha'B : a' ∈ B' := mem_subgroupOf.mpr haB
  refine ⟨?_, ⟨d', hd'B, rfl⟩, ?_, ?_, ⟨a', ha'B, rfl⟩, ?_⟩
  · rw [card_map_eq_of_injOn' π hinj, hB', Nat.card_congr (subgroupOfEquivOfLe hBL).toEquiv,
      hB9]
  · intro h
    have h1 : π d' = π 1 := by rw [h, map_one]
    have := hinj hd'B (one_mem _) h1
    exact hd1 (congrArg Subtype.val this)
  ·
    obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(L ⊓ centralizer ({d} : Set G)))
      3 (n := 3) (by norm_num; exact h27)
    set K : Subgroup G := K₀.map (L ⊓ centralizer ({d} : Set G)).subtype with hK
    have hK27 : Nat.card K = 27 := by
      rw [hK, card_map_of_injective (subtype_injective _), hK₀]
      norm_num
    have hKL : K ≤ L := (map_subtype_le _).trans inf_le_left
    have hKC : K ≤ centralizer ({d} : Set G) := (map_subtype_le _).trans inf_le_right
    have hK3 : IsPGroup 3 K := IsPGroup.of_card (n := 3) (by rw [hK27]; norm_num)
    set K' := K.subgroupOf L with hK'
    have hK'3 : IsPGroup 3 K' := hK3.comap_subtype
    have hinjK : Set.InjOn π (K' : Set ↥L) := injOn_mk_of_isPGroup Nat.prime_three hK'3
    have hcard : Nat.card (K'.map π) = 27 := by
      rw [card_map_eq_of_injOn' π hinjK, hK', Nat.card_congr (subgroupOfEquivOfLe hKL).toEquiv,
        hK27]
    have hle : K'.map π ≤ centralizer ({π d'} : Set (lBar L)) := by
      rintro _ ⟨k, hk, rfl⟩
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hKC (mem_subgroupOf.mp hk)))
    exact hcard ▸ card_dvd_of_le hle
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    have h1 : π (d' ^ k) = π a' := by rw [map_zpow, hk]
    have := hinj (zpow_mem hd'B k) ha'B h1
    apply had
    have h2 : ((d' ^ k : ↥L) : G) = a := congrArg Subtype.val this
    rw [← h2, coe_zpow]
    exact zpow_mem_zpowers d k

theorem exists_four_lift (h415 : Sec4.Item4_15) {L B : Subgroup G}
    (hθ : Odd (Nat.card (aschbacherSolvableCore 3 ↥L)))
    (hJ2 : Nonempty (lBar L ≃* NativeSporadic.J2)) (hBL : B ≤ L) (hB3 : IsPGroup 3 B)
    (hB9 : Nat.card B = 9) {d : G} (hdB : d ∈ B) (hd1 : d ≠ 1)
    (h27 : 27 ∣ Nat.card (L ⊓ centralizer ({d} : Set G) : Subgroup G)) {a : G} (haB : a ∈ B)
    (had : a ∉ zpowers d) :
    ∃ Y : Subgroup G, Y ≤ L ∧ CFSG.Assembly.IsElemAbelian 2 Y ∧ Nat.card Y = 4 ∧
      B ≤ normalizer (Y : Set G) ∧ a ∈ centralizer (Y : Set G) ∧
      ∀ y ∈ Y, d * y * d⁻¹ = y → y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hB9', hdB', hd1', h27', haB', had'⟩ :=
    bar_data hBL hB3 hB9 hdB hd1 h27 haB had
  set π := barMap L with hπ
  set N₀ := aschbacherSolvableCore 3 ↥L with hN₀
  set B' := B.subgroupOf L with hB'
  set d' : ↥L := ⟨d, hBL hdB⟩ with hd'
  set a' : ↥L := ⟨a, hBL haB⟩ with ha'
  obtain ⟨hWab, hW4, hWa, hBW, hfpf⟩ := j2_exists_four h415 hJ2 hB9' hdB' hd1' h27' haB' had'
  set W := oTwoN (π a') with hW
  set P : Subgroup ↥L := W.comap π with hP
  have hB'P : B' ≤ normalizer (P : Set ↥L) := by
    intro b hb
    refine mem_normalizer_fintype fun x hx => ?_
    change π (b * x * b⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hBW ⟨b, hb, rfl⟩) (π x)).mp hx
  have hB'3 : IsPGroup 3 B' := hB3.comap_subtype
  have hN₀odd : Odd (Nat.card N₀) := hθ
  have hPcard : Nat.card P = 4 * Nat.card N₀ := by rw [hP, card_comap_mk_theta, hW4]
  have hP3 : ¬ 3 ∣ Nat.card P := by
    rw [hPcard]
    intro h
    have h3 := (Nat.Prime.dvd_mul Nat.prime_three).mp h
    rcases h3 with h3 | h3
    · norm_num at h3
    · exact three_not_dvd_card_aschbacherSolvableCore h3
  obtain ⟨S, hS⟩ := exists_sylow_two_normalized hB'P hB'3 hP3
  have hS4 : Nat.card S = 4 := by
    have h4dvd : 2 ^ 2 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (by
      rw [hPcard]; exact Dvd.intro _ rfl)
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    have hdvdP : Nat.card S ∣ Nat.card P := (S : Subgroup P).card_subgroup_dvd_card
    rw [hk, hPcard] at hdvdP
    rw [hk] at h4dvd
    have hcop : Nat.Coprime (2 ^ k) (Nat.card N₀) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN₀odd)
    have h4' : 2 ^ k ∣ 4 := hcop.dvd_of_dvd_mul_right hdvdP
    have hk2 : k ≤ 2 := by
      by_contra h
      have : 2 ^ 3 ∣ 4 := (pow_dvd_pow 2 (by omega)).trans h4'
      norm_num at this
    have hk2' : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h4dvd
    rw [hk, show k = 2 by omega]
    norm_num
  have hSθ : ∀ s : P, s ∈ S → ((s : ↥L) ∈ N₀) → s = 1 := by
    intro s hs hsN
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    have hk' : (s : ↥L) ^ 2 ^ k = 1 := by
      have := congrArg (fun t : S => ((t : P) : ↥L)) hk
      simpa using this
    have := eq_one_of_two_pow_of_odd hN₀odd hsN hk'
    exact Subtype.ext this
  set Y : Subgroup G := ((S : Subgroup P).map P.subtype).map L.subtype with hYdef
  have hYmem : ∀ y ∈ Y, ∃ s : P, s ∈ S ∧ ((s : ↥L) : G) = y := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  have hπS : ∀ s : P, π s ∈ W := fun s => s.2
  refine ⟨Y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact map_subtype_le _
  ·
    refine isElemAbelian_two_of_sq fun y hy => ?_
    obtain ⟨s, hs, rfl⟩ := hYmem y hy
    have h1 : π ((s : ↥L) ^ 2) = 1 := by rw [map_pow]; exact hWab.2 _ (hπS s)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : s ^ 2 ∈ S := pow_mem hs 2
    have := hSθ (s ^ 2) h2 (by simpa using h1)
    rw [← coe_pow, ← coe_pow, this]
    rfl
  · rw [hYdef, card_map_of_injective (subtype_injective _),
      card_map_of_injective (subtype_injective _), hS4]
  ·
    intro b hb
    refine mem_normalizer_fintype fun y hy => ?_
    obtain ⟨s, hs, rfl⟩ := hYmem y hy
    have hbB' : (⟨b, hBL hb⟩ : ↥L) ∈ B' := mem_subgroupOf.mpr hb
    obtain ⟨t, ht, hts⟩ := hS _ hbB' s hs
    refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
    change ((t : ↥L) : G) = b * ((s : ↥L) : G) * b⁻¹
    rw [hts]
    rfl
  ·
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨s, hs, rfl⟩ := hYmem y hy
    have ha'B' : a' ∈ B' := mem_subgroupOf.mpr haB
    obtain ⟨t, ht, hts⟩ := hS _ ha'B' s hs
    have hπt : π (t : ↥L) = π (s : ↥L) := by
      have e1 : (t : ↥L) = a' * (s : ↥L) * a'⁻¹ := hts
      rw [e1, map_mul, map_mul, map_inv]
      have hc := mem_centralizer_singleton_iff.mp (hWa (hπS s))
      rw [← hc, mul_inv_cancel_right]
    have hmem : t * s⁻¹ ∈ S := mul_mem ht (inv_mem hs)
    have hN : ((t * s⁻¹ : P) : ↥L) ∈ N₀ := by
      have : π ((t * s⁻¹ : P) : ↥L) = 1 := by
        simp only [coe_mul, coe_inv, map_mul, map_inv, hπt, mul_inv_cancel]
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have hts1 := hSθ _ hmem hN
    have hteq : t = s := by
      calc t = t * s⁻¹ * s := by group
        _ = s := by rw [hts1, one_mul]
    have e2 : ((t : ↥L) : G) = a * ((s : ↥L) : G) * a⁻¹ := by
      have := congrArg Subtype.val hts
      simpa using this
    rw [hteq] at e2
    calc ((s : ↥L) : G) * a = a * ((s : ↥L) : G) * a⁻¹ * a := by rw [← e2]
      _ = a * ((s : ↥L) : G) := by group
  ·
    intro y hy hdy
    obtain ⟨s, hs, rfl⟩ := hYmem y hy
    have hπ1 : π d' * π (s : ↥L) * (π d')⁻¹ = π (s : ↥L) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hdy
    have h1 := hfpf _ (hπS s) hπ1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have := hSθ s hs h1
    rw [this]
    rfl

theorem commutator_mem_theta_lift (h415 : Sec4.Item4_15) {L B : Subgroup G}
    (hθ : Odd (Nat.card (aschbacherSolvableCore 3 ↥L)))
    (hJ2 : Nonempty (lBar L ≃* NativeSporadic.J2)) (hBL : B ≤ L) (hB3 : IsPGroup 3 B)
    (hB9 : Nat.card B = 9) {d : G} (hdB : d ∈ B) (hd1 : d ≠ 1)
    (h27 : 27 ∣ Nat.card (L ⊓ centralizer ({d} : Set G) : Subgroup G)) {Y : Subgroup G}
    (hYL : Y ≤ L) (hY4 : Nat.card Y = 4)
    (hBY : B ≤ normalizer (Y : Set G)) {e : G} (heB : e ∈ B)
    (heY : e ∈ centralizer (Y : Set G)) (hed : e ∉ zpowers d) :
    ∀ q ∈ inSubgroup (CFSG.pCore 2) (centralizer (Y : Set G)) ⊓ L,
      ∀ x ∈ B ⊓ centralizer (Y : Set G),
        q * x * q⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hB9', hdB', hd1', h27', heB', hed'⟩ :=
    bar_data hBL hB3 hB9 hdB hd1 h27 heB hed
  set π := barMap L with hπ
  set N₀ := aschbacherSolvableCore 3 ↥L with hN₀
  have hN₀odd : Odd (Nat.card N₀) := hθ
  set e' : ↥L := ⟨e, hBL heB⟩ with he'
  set Y' := Y.subgroupOf L with hY'
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card (n := 2) (by rw [hY4]; norm_num)
  have hY'2 : IsPGroup 2 Y' := hY2.comap_subtype
  have hinjY : Set.InjOn π (Y' : Set ↥L) := by
    intro u hu v hv huv
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at huv
    obtain ⟨k, hk⟩ := hY'2 ⟨u⁻¹ * v, mul_mem (inv_mem hu) hv⟩
    have hk' : (u⁻¹ * v) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have := eq_one_of_two_pow_of_odd hN₀odd huv hk'
    exact eq_of_inv_mul_eq_one this
  set Ybar := Y'.map π with hYbar
  have hYbar4 : Nat.card Ybar = 4 := by
    rw [hYbar, card_map_eq_of_injOn' π hinjY, hY', Nat.card_congr (subgroupOfEquivOfLe hYL).toEquiv,
      hY4]
  have hYbar2 : IsPGroup 2 Ybar := hY'2.map π
  have hYbare : Ybar ≤ centralizer ({π e'} : Set (lBar L)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((mem_centralizer_iff.mp heY) y (mem_subgroupOf.mp hy))
  have hBYbar : (B.subgroupOf L).map π ≤ normalizer (Ybar : Set (lBar L)) := by
    rintro _ ⟨b, hb, rfl⟩
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨b * y * b⁻¹, mem_subgroupOf.mpr ?_, by simp⟩
    exact (mem_normalizer_iff.mp (hBY (mem_subgroupOf.mp hb)) y).mp (mem_subgroupOf.mp hy)
  have hcore := j2_pCore_centralizer_le h415 hJ2 hB9' hdB' hd1' h27' heB' hed' hYbar2 hYbar4
    hYbare hBYbar
  set Q := inSubgroup (CFSG.pCore 2) (centralizer (Y : Set G)) ⊓ L with hQ
  set Q' := Q.subgroupOf L with hQ'
  have hQ2 : IsPGroup 2 Q :=
    ((CFSG.pCore_isPGroup (p := 2) (G := ↥(centralizer (Y : Set G)))).map _).to_le inf_le_left
  have hQbar2 : IsPGroup 2 (Q'.map π) := hQ2.comap_subtype.map π
  have hQC : Q ≤ centralizer (Y : Set G) := inf_le_left.trans (map_subtype_le _)
  have hQbarC : Q'.map π ≤ centralizer (Ybar : Set (lBar L)) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((mem_centralizer_iff.mp (hQC (mem_subgroupOf.mp hq))) y
      (mem_subgroupOf.mp hy))
  let α : Y' →* MulAut ↥L := MulAut.conj.comp Y'.subtype
  have hαN : ∀ a : Y', ∀ n ∈ N₀, α a n ∈ N₀ := fun a n hn =>
    (aschbacherSolvableCore_normal 3 ↥L).conj_mem n hn _
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hY'2 α N₀ hαN
    (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hN₀odd)
  have hnorm : centralizer (Ybar : Set (lBar L)) ≤ normalizer ((Q'.map π : Subgroup (lBar L)) :
      Set (lBar L)) := by
    intro z hz
    have hzfix : z ∈ {q : lBar L | ∀ a : Y',
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N₀ hαN a q = q} := by
      intro a
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N₀ z
      change π (α a x) = π x
      have h1 : α a x = (a : ↥L) * x * (a : ↥L)⁻¹ := rfl
      rw [h1, map_mul, map_mul, map_inv]
      have hc : π (a : ↥L) * π x = π x * π (a : ↥L) :=
        (mem_centralizer_iff.mp hz) (π a) ⟨a, a.2, rfl⟩
      rw [hc, mul_inv_cancel_right]
    rw [hlift] at hzfix
    obtain ⟨c, hc, rfl⟩ := hzfix
    have hcY : (c : G) ∈ centralizer (Y : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := hc ⟨⟨y, hYL hy⟩, mem_subgroupOf.mpr hy⟩
      have h2 : (⟨y, hYL hy⟩ : ↥L) * c * (⟨y, hYL hy⟩ : ↥L)⁻¹ = c := h1
      have h3 := congrArg Subtype.val h2
      simp only [coe_mul, coe_inv] at h3
      calc y * (c : G) = y * c * y⁻¹ * y := by group
        _ = c * y := by rw [h3]
    have hcN : (c : G) ∈ normalizer (Q : Set G) := by
      have h1 : (c : G) ∈ normalizer
          (inSubgroup (CFSG.pCore 2) (centralizer (Y : Set G)) : Set G) :=
        CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map _ _
          inferInstance (le_normalizer hcY)
      have h2 : (c : G) ∈ normalizer (L : Set G) := le_normalizer c.2
      refine mem_normalizer_fintype fun x hx => ⟨?_, ?_⟩
      · exact (mem_normalizer_iff.mp h1 x).mp hx.1
      · exact (mem_normalizer_iff.mp h2 x).mp hx.2
    refine mem_normalizer_fintype fun w hw => ?_
    obtain ⟨q, hq, rfl⟩ := hw
    refine ⟨c * q * c⁻¹, mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (mem_normalizer_iff.mp hcN q).mp (mem_subgroupOf.mp hq)
  have hQbarY : Q'.map π ≤ Ybar :=
    (le_inSubgroup_pCore hQbarC hQbar2 hnorm).trans hcore
  intro q hq x hx
  have hqL : q ∈ L := hq.2
  have hxL : x ∈ L := hBL hx.1
  have hπq : π ⟨q, hqL⟩ ∈ Ybar := hQbarY ⟨⟨q, hqL⟩, mem_subgroupOf.mpr hq, rfl⟩
  obtain ⟨y, hy, hyq⟩ := hπq
  have hcomm : π ⟨q, hqL⟩ * π ⟨x, hxL⟩ = π ⟨x, hxL⟩ * π ⟨q, hqL⟩ := by
    rw [← hyq, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((mem_centralizer_iff.mp hx.2) y (mem_subgroupOf.mp hy))
  have h1 : π (⟨q, hqL⟩ * ⟨x, hxL⟩ * ⟨q, hqL⟩⁻¹ * ⟨x, hxL⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

end Bar

end CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof
