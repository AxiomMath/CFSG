module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeBasic
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeComponent
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52Bridge
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeStepTwo
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.Assembly.Subnormal
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Defs

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType

theorem rawDatumLegacy_exists {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatumLegacy lab Q) : ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)),
      Q R I F := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> dsimp only [LargeEvenRawDatumLegacy] at h <;> (try split_ifs at h) <;>
    (repeat' (obtain ⟨_, h⟩ := h)) <;> exact ⟨_, _, _, _, h⟩

theorem ggThmIHyp_unpack {G : Type} [Group G] [Finite G]
    {p : ℕ} {B L : Subgroup G} {x : G} (hG : GGThmIHyp p B x L) :
    IsElemAbelian p B ∧ x ∈ B ∧ x ≠ 1 ∧
      CFSG.Open.IsComponentOf L (centralizer ({x} : Set G)) ∧
      (∀ S : Subgroup G, S ≤ centralizer (L : Set G) → IsPGroup p S → IsCyclic S) ∧
      commutator L = ⊤ ∧ B ≤ normalizer (L : Set G) ∧
      ∃ T : Subgroup G, T ≤ centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
        B ≤ normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥ := by
  obtain ⟨-, -, -, -, -, -, hSS, hST⟩ := hG
  obtain ⟨⟨hBab, -, -⟩, hxB, hx1, hLc, hcyc⟩ := hSS
  obtain ⟨⟨hperf, lab, -, hraw⟩, hT, -, -⟩ := hST
  obtain ⟨R, _, I, F, -, -, θ, -, hBL, -⟩ := rawDatumLegacy_exists hraw
  exact ⟨hBab, hxB, hx1, isComponentOf_iff_open.1 hLc, hcyc, hperf, hBL, hT⟩

theorem ggThmIHyp_clause_six {G : Type} [Group G] [Finite G]
    {p : ℕ} {B L : Subgroup G} {x : G} (hG : GGThmIHyp p B x L)
    {D K : Subgroup G} (hDK : LargeEvenStdSub p B x L D K) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    Odd (Nat.card (⁅K, LargeEvenPPrimeCoreOf p (centralizer ({d} : Set G))⁆ : Subgroup G)) :=
  ((hG.2.2.2.2.2.2.2.2.2.2 D K hDK).2 d hd hd1)

structure O1ppData {G : Type} [Group G] [Finite G]
    (B : Subgroup G) (x zn : G) (L X Xk Tk : Subgroup G) : Prop where
  hyp : GGThmIHyp 3 B x L
  bstar : GGBstar 3 B B
  rank_six : twoLocalPrimeRank 3 G = 6
  zn_mem : zn ∈ B
  zn_not_mem : zn ∉ zpowers x
  stdSub : LargeEvenStdSub 3 B x L (closure {x, zn}) X
  X_model : LieModel X .PSU 5 2 1
  X_le : X ≤ centralizer ({x * zn⁻¹} : Set G)
  X_normal : centralizer ({x} : Set G) ⊓ centralizer ({x * zn⁻¹} : Set G) ≤ normalizer (X : Set G)
  Xk_le : Xk ≤ X
  Xk_model : LieModel Xk .PSU 4 2 1
  Tk_two : IsPGroup 2 Tk
  Tk_card : Nat.card Tk = 4
  Tk_le : Tk ≤ centralizer ({x * zn⁻¹} : Set G)
  B_norm_Tk : B ≤ normalizer (Tk : Set G)
  Tk_cent_Xk : Tk ≤ centralizer (Xk : Set G)
  E_moves : ∃ b ∈ B ⊓ X, ∃ t ∈ Tk, b * t * b⁻¹ ≠ t
  x_moves : ∃ t ∈ Tk, x * t * x⁻¹ ≠ t
  F14 : ∀ α : MulAut X, (∀ y : X, (y : G) ∈ Xk → α y = y) → α ^ 3 = 1

abbrev O1ppCore {G : Type} [Group G] (x zn : G) : Subgroup G :=
  LargeEvenPPrimeCoreOf 3 (centralizer ({x * zn⁻¹} : Set G))

theorem prop_10_10_step1 {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (h : O1ppData B x zn L X Xk Tk) :
    Odd (Nat.card (⁅X, O1ppCore x zn⁆ : Subgroup G)) := by
  refine ggThmIHyp_clause_six h.hyp h.stdSub ?_ ?_
  · exact mul_mem (subset_closure (by simp)) (inv_mem (subset_closure (by simp)))
  · intro h1
    apply h.zn_not_mem
    rw [mul_inv_eq_one] at h1
    exact h1 ▸ mem_zpowers zn

@[expose] def U52SimpleSix : Prop :=
  ∀ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ 1) ^ 2 →
    IsSimpleGroup (StatedProj (StatedSU 5 (2 ^ 1) K)) ∧
      6 ∣ Nat.card (StatedProj (StatedSU 5 (2 ^ 1) K))

theorem o1pp_core_facts {G : Type} [Group G] [Finite G] (x zn : G) :
    centralizer ({x * zn⁻¹} : Set G) ≤ normalizer ((O1ppCore x zn : Subgroup G) : Set G) ∧
      Nat.Coprime 3 (Nat.card (O1ppCore x zn)) := by
  set H := centralizer ({x * zn⁻¹} : Set G) with hH
  refine ⟨fun g hg => ?_, ?_⟩
  · have hn : (⟨g, hg⟩ : H) ∈ normalizer ((LargeEvenPPrimeCore 3 H : Subgroup H) : Set H) := by
      rw [normalizer_eq_top (LargeEvenPPrimeCore 3 H)]; trivial
    exact le_normalizer_map H.subtype (mem_map_of_mem _ hn)
  · have : Nat.card (O1ppCore x zn) = Nat.card (LargeEvenPPrimeCore 3 H) :=
      card_map_of_injective H.subtype_injective
    rw [this]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact CFSG.pPrimeCore_coprime_card

theorem o1pp_X_facts {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (hU : U52SimpleSix) (h : O1ppData B x zn L X Xk Tk) :
    IsSimpleGroup X ∧ 2 ∣ Nat.card X ∧ 3 ∣ Nat.card X := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := lieModel_PSU_five h.X_model
  obtain ⟨hs, h6⟩ := hU K hF hfin hK
  have hcX : Nat.card X = Nat.card (StatedProj (StatedSU 5 (2 ^ 1) K)) := Nat.card_congr e.toEquiv
  exact ⟨(MulEquiv.isSimpleGroup_congr e).2 hs, hcX ▸ (dvd_trans (by norm_num) h6),
    hcX ▸ (dvd_trans (by norm_num) h6)⟩

theorem prop_10_10_step3 {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (hU : U52SimpleSix) (h : O1ppData B x zn L X Xk Tk)
    (hT : Tk ≤ normalizer ((X ⊔ O1ppCore x zn : Subgroup G) : Set G)) :
    ∀ t ∈ Tk, ∀ y ∈ X, t * y * t⁻¹ * y⁻¹ ∈ (⁅X, O1ppCore x zn⁆ : Subgroup G) := by
  intro t ht
  obtain ⟨hHO, hO3⟩ := o1pp_core_facts x zn
  obtain ⟨hXs, h2, h3⟩ := o1pp_X_facts hU h
  obtain ⟨hint, htV, htN⟩ := step_two (le_trans h.X_le hHO) hXs h2 h3 hO3 (prop_10_10_step1 h)
    (hHO (h.Tk_le ht)) (hT ht)
  obtain ⟨k, hk⟩ := h.Tk_two ⟨t, ht⟩
  have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  refine comm_mem_of_two_elem (normalizer_commutator_ge_left X _) hint h.F14 htV htN hk' ?_
  intro y hy
  have := mem_centralizer_iff.1 (h.Tk_cent_Xk ht) y hy
  rw [← this]
  group

theorem prop_10_10 {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (hU : U52SimpleSix) (h : O1ppData B x zn L X Xk Tk) :
    ¬ Tk ≤ normalizer ((X ⊔ O1ppCore x zn : Subgroup G) : Set G) := by
  intro hT
  have hc := commute_of_comm_mem_odd (E := B ⊓ X) h.Tk_two (prop_10_10_step1 h)
    (inf_le_left.trans h.B_norm_Tk)
    (fun t ht e he => prop_10_10_step3 hU h hT t ht e (mem_inf.1 he).2)
  obtain ⟨b, hb, t, ht, hne⟩ := h.E_moves
  apply hne
  rw [← hc t ht b hb]
  group

abbrev O1ppBar {G : Type} [Group G] (x zn : G) : Type :=
  ↥(centralizer ({x * zn⁻¹} : Set G)) ⧸ LargeEvenPPrimeCore 3 ↥(centralizer ({x * zn⁻¹} : Set G))

abbrev O1ppXBar {G : Type} [Group G]
    (x zn : G) (X : Subgroup G) : Subgroup (O1ppBar x zn) :=
  (X.subgroupOf (centralizer ({x * zn⁻¹} : Set G))).map (QuotientGroup.mk' _)

@[expose] def U42Nonabelian : Prop :=
  ∀ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ 1) ^ 2 →
    ∃ a b : StatedProj (StatedSU 4 (2 ^ 1) K), a * b ≠ b * a

theorem lieModel_PSU_four {R : Type} [Group R] (h : LieModel R .PSU 4 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ 1) ^ 2 ∧
      Nonempty (R ≃* StatedProj (StatedSU 4 (2 ^ 1) K)) := by
  rcases h.2 with h | ⟨h, -⟩
  · exact h.2
  · exact absurd h (by norm_num)

theorem prop_10_10_not_component {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G}
    {x zn : G} (hU : U52SimpleSix) (hU4 : U42Nonabelian)
    (h : O1ppData B x zn L X Xk Tk) : ¬ CFSG.Open.IsComponentOf (O1ppXBar x zn X) ⊤ := by
  intro hc
  apply prop_10_10 hU h
  set H := centralizer ({x * zn⁻¹} : Set G) with hH
  set O := O1ppCore x zn with hOdef
  set π := QuotientGroup.mk' (LargeEvenPPrimeCore 3 ↥H) with hπdef
  obtain ⟨hHO, hO3⟩ := o1pp_core_facts x zn
  obtain ⟨hXs, -, h3⟩ := o1pp_X_facts hU h
  have hXO : X ≤ normalizer (O : Set G) := le_trans h.X_le hHO
  have hXObot : X ⊓ O = ⊥ := by
    haveI := hXs
    haveI := normal_subgroupOf_of_le_normalizer hXO
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.subgroupOf X) with h' | h'
    · rw [subgroupOf_eq_bot] at h'
      exact disjoint_iff.1 h'.symm
    · rw [subgroupOf_eq_top] at h'
      have := Nat.Coprime.eq_one_of_dvd hO3 (h3.trans (card_dvd_of_le h'))
      omega
  have hπ : ∀ a b : H, π a = π b ↔ ((a⁻¹ * b : H) : G) ∈ O := by
    intro a b
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    constructor
    · intro hm; exact mem_map_of_mem _ hm
    · rintro ⟨c, hc', hce⟩
      have : c = a⁻¹ * b := Subtype.ext hce
      rwa [← this]
  have hmemX : ∀ (a : G) (ha : a ∈ X), π ⟨a, h.X_le ha⟩ ∈ O1ppXBar x zn X :=
    fun a ha => mem_map_of_mem _ (mem_subgroupOf.2 ha)
  intro t ht
  have htH := h.Tk_le ht
  set τ : O1ppBar x zn := π ⟨t, htH⟩ with hτ
  have hconj : ∀ (a : G) (ha : a ∈ H),
      (MulAut.conj τ) (π ⟨a, ha⟩) = π ⟨t * a * t⁻¹, mul_mem (mul_mem htH ha) (inv_mem htH)⟩ := by
    intro a ha
    rw [MulAut.conj_apply, hτ, ← map_mul, ← map_inv, ← map_mul]
    rfl
  have hfix : (O1ppXBar x zn X).map (MulAut.conj τ).toMonoidHom = O1ppXBar x zn X := by
    by_contra hne
    have hc' := CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hc (mem_top τ)
    obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := lieModel_PSU_four h.Xk_model
    obtain ⟨a, b, hab⟩ := hU4 K hF hfin hK
    apply hab
    set a' : G := ((e.symm a : Xk) : G) with ha'
    set b' : G := ((e.symm b : Xk) : G) with hb'
    have haX : a' ∈ X := h.Xk_le (e.symm a).2
    have hbX : b' ∈ X := h.Xk_le (e.symm b).2
    have hbτ : π ⟨b', h.X_le hbX⟩ ∈ (O1ppXBar x zn X).map (MulAut.conj τ).toMonoidHom := by
      refine ⟨π ⟨b', h.X_le hbX⟩, hmemX b' hbX, ?_⟩
      show (MulAut.conj τ) (π ⟨b', h.X_le hbX⟩) = _
      rw [hconj]
      congr 2
      have := mem_centralizer_iff.1 (h.Tk_cent_Xk ht) b' (e.symm b).2
      rw [← this]; group
    have key := CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hc hc' (Ne.symm hne)
      (hmemX a' haX) hbτ
    rw [← map_mul, ← map_mul, hπ] at key
    have hmem : (((((⟨a', h.X_le haX⟩ : H) * ⟨b', h.X_le hbX⟩)⁻¹ *
        ((⟨b', h.X_le hbX⟩ : H) * ⟨a', h.X_le haX⟩)) : H) : G) ∈ X ⊓ O := by
      refine mem_inf.2 ⟨?_, key⟩
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      exact mul_mem (inv_mem (mul_mem haX hbX)) (mul_mem hbX haX)
    rw [hXObot, mem_bot] at hmem
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at hmem
    have hab' : a' * b' = b' * a' := by
      calc a' * b' = a' * b' * ((a' * b')⁻¹ * (b' * a')) := by rw [hmem, mul_one]
        _ = b' * a' := by group
    apply e.symm.injective
    apply Subtype.ext
    simpa [map_mul, ha', hb'] using hab'
  apply mem_normalizer_of_conj_mem
  intro g hg
  obtain ⟨a, ha, o, ho, rfl⟩ := exists_mul_of_mem_sup hXO hg
  have hto : t * o * t⁻¹ ∈ O := (mem_normalizer_iff.1 (hHO htH) o).1 ho
  have hta : π ⟨t * a * t⁻¹, mul_mem (mul_mem htH (h.X_le ha)) (inv_mem htH)⟩ ∈
      O1ppXBar x zn X := by
    rw [← hfix, ← hconj a (h.X_le ha)]
    exact mem_map_of_mem _ (hmemX a ha)
  obtain ⟨a₂, ha₂, he⟩ := mem_map.1 hta
  have ha₂X : (a₂ : G) ∈ X := mem_subgroupOf.1 ha₂
  have hk := (hπ a₂ _).1 he
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at hk
  have : t * (a * o) * t⁻¹ = a₂ * ((a₂ : G)⁻¹ * (t * a * t⁻¹)) * (t * o * t⁻¹) := by group
  rw [this]
  exact mul_mem (mul_mem (mem_sup_left ha₂X) (mem_sup_right hk)) (mem_sup_right hto)

end CFSG.GGQ2Prime
