module

public import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofU
public import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofQ0
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec15.NoModNine

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

@[expose] def KS165L : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (n : ℕ), 2 ^ n % 3 = 1 → 2 ^ n % 9 ≠ 1 → n ≠ 2 →
    CFSG.IsQuasisimple Q → ¬ 3 ∣ Nat.card (Subgroup.center Q) →
    Nonempty (Q ⧸ Subgroup.center Q ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) →
    ∀ B : Subgroup Q, CFSG.Assembly.IsElemAbelian 3 B → Nat.card B = 9 →
    ∀ T : Subgroup (MulAut Q), IsPGroup 2 T → T ≠ ⊥ →
      (∀ b ∈ B, ∀ t ∈ T, MulAut.conj b * t * (MulAut.conj b)⁻¹ ∈ T) →
      ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ E : Subgroup Q, IsPGroup p E ∧ E ≠ ⊥ ∧
        (∀ t ∈ T, ∀ e ∈ E, t e ∈ E) ∧
        ∀ e ∈ E, e ≠ 1 → Subgroup.closure ({x : Q | ∀ t ∈ T, t x = x} ∪ {e}) = ⊤

namespace Steps165

variable {G : Type} [Group G] [Finite G]

theorem card_comap_of_surjective' {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    (hf : Function.Surjective f) (K : Subgroup Y) :
    Nat.card (K.comap f) = Nat.card K * Nat.card f.ker := by
  have : Finite Y := Finite.of_surjective f hf
  have e1 : Nat.card (K.comap f) * (K.comap f).index = Nat.card X := Subgroup.card_mul_index _
  have e2 : Nat.card K * K.index = Nat.card Y := Subgroup.card_mul_index K
  have e3 : Nat.card X = Nat.card (X ⧸ f.ker) * Nat.card f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have e5 : Nat.card (X ⧸ f.ker) = Nat.card Y :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have e4 : (K.comap f).index = K.index := Subgroup.index_comap_of_surjective K hf
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [e4] at e1
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card (K.comap f) * K.index = Nat.card X := e1
    _ = Nat.card Y * Nat.card f.ker := by rw [e3, e5]
    _ = (Nat.card K * K.index) * Nat.card f.ker := by rw [e2]
    _ = (Nat.card K * Nat.card f.ker) * K.index := by ring

theorem mem_normalizer_of_forall_conj_mem {S : Subgroup G} {g : G}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ S) : g ∈ Subgroup.normalizer (S : Set G) := by
  have hle : S.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs
  refine mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit [Finite G] in
theorem actQuotPCore_mk {Y : Subgroup G} {m : G} (hm : m ∈ Subgroup.normalizer (Y : Set G))
    (y : G) (hy : y ∈ Y) :
    ((actQuotPCore Y ⟨m, hm⟩ (((⟨y, hy⟩ : ↥Y)) : ↥Y ⧸ CFSG.pCore 2 ↥Y) :
        ↥Y ⧸ CFSG.pCore 2 ↥Y)) =
      (((⟨m * y * m⁻¹, (Subgroup.mem_normalizer_iff.mp hm y).mp hy⟩ : ↥Y)) :
        ↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  change Crit167.quotPCoreAut ↥Y (Y.normalizerMonoidHom ⟨m, hm⟩) _ = _
  rw [Crit167.quotPCoreAut_apply_mk]
  congr 1

theorem mem_normalizer_of_fixed {Y₀ S : Subgroup G} (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G))
    (hOS : CFSG.Open.pCoreOf 2 Y₀ ≤ S) {y : G} (hy : y ∈ Y₀)
    (hfix : ∀ s (hs : s ∈ S), actQuotPCore Y₀ ⟨s, hSM hs⟩
      (((⟨y, hy⟩ : ↥Y₀)) : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = (((⟨y, hy⟩ : ↥Y₀)) : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) :
    y ∈ Subgroup.normalizer (S : Set G) := by
  have key : ∀ s ∈ S, s * y⁻¹ * s⁻¹ * y ∈ S := by
    intro s hs
    have h1 := hfix s hs
    rw [actQuotPCore_mk, QuotientGroup.eq] at h1
    have h2 : (((⟨s * y * s⁻¹, (Subgroup.mem_normalizer_iff.mp (hSM hs) y).mp hy⟩ : ↥Y₀)⁻¹ *
        ⟨y, hy⟩ : ↥Y₀) : G) ∈ CFSG.Open.pCoreOf 2 Y₀ := by
      rw [CFSG.Open.pCoreOf]
      exact ⟨_, h1, rfl⟩
    have e : (((⟨s * y * s⁻¹, (Subgroup.mem_normalizer_iff.mp (hSM hs) y).mp hy⟩ : ↥Y₀)⁻¹ *
        ⟨y, hy⟩ : ↥Y₀) : G) = s * y⁻¹ * s⁻¹ * y := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e] at h2
    exact hOS h2
  have hinv : y⁻¹ ∈ Subgroup.normalizer (S : Set G) := by
    refine mem_normalizer_of_forall_conj_mem fun s hs => ?_
    have h3 := key s⁻¹ (S.inv_mem hs)
    have e : y⁻¹ * s * y⁻¹⁻¹ = s * (s⁻¹ * y⁻¹ * s⁻¹⁻¹ * y) := by group
    rw [e]
    exact S.mul_mem hs h3
  simpa using Subgroup.inv_mem _ hinv

theorem isSimpleGroup_thetaQuot_of_projSL {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) {n : ℕ} (hn : 1 ≤ n) (hq : 2 ^ n % 3 = 1)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) :
    IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  have hQ := Sec6.isQuasisimple_of_mem_thetaComponentsAt hL
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
    center_eq_bot_of_mulEquiv φ (isPerfect_center_projSL 2 n hn hq).2
  have : IsSimpleGroup ((↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸
      Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := hQ.2.1
  have e : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸
      Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃*
        ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

end Steps165

theorem tor165L_of (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h138 : Item138N)
    (hK : KS165L) : Tor165L := by
  intro G _ _ A c L Y₀ h hLn S hS hS1 hYS hOS
  obtain ⟨n, hn, hq, ⟨φ⟩⟩ := hLn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : n ≠ 2 := by
    rintro rfl
    exact h.not_l34.false φ
  obtain ⟨hY, hprod⟩ := Steps165.cover_prod_of_std h h1514 hMeets
    (Steps165.isEmpty_alt7_of_projSL hn hq φ)
  have hmod := not_modNine_of_inner h.toSec15R h138 KFacts.kSL3PiOrder3TypeC hn
    (Or.inl ⟨hq, ⟨φ⟩⟩) hprod
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    card_inf_eq_nine h.toSec13Data (isPerfect_lBar h.toSec13Data) hprod.some
  have hQq : CFSG.IsQuasisimple (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := h.mem_y0Star.prop.1.2.2.2
  obtain ⟨⟨e⟩, hZ3⟩ := Steps165.quotCenter_facts h.le_y0 hY hQq
    (Steps165.isSimpleGroup_thetaQuot_of_projSL h.mem_lA.1 hn hq φ)
  obtain ⟨B, hBe, hB9, hBA⟩ := Steps165.exists_image_inf h h9
  have hSM : S ≤ Subgroup.normalizer (Y₀ : Set G) := h.qStar_le S hS
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  set T := (S.subgroupOf (Subgroup.normalizer (Y₀ : Set G))).map (actQuotPCore Y₀) with hT
  have hT2 : IsPGroup 2 T := hS2.comap_subtype.map _
  have hTmem : ∀ s (hs : s ∈ S), actQuotPCore Y₀ ⟨s, hSM hs⟩ ∈ T := fun s hs =>
    ⟨⟨s, hSM hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  have hTn : ∀ b ∈ B, ∀ t ∈ T, MulAut.conj b * t * (MulAut.conj b)⁻¹ ∈ T := by
    intro b hb t ht
    obtain ⟨a, ha, haA, rfl⟩ := hBA b hb
    obtain ⟨⟨s, hsN⟩, hsS, rfl⟩ := ht
    have haN : a ∈ Subgroup.normalizer (Y₀ : Set G) := Subgroup.le_normalizer ha
    have has : a * s * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hAS haA) s).mp hsS
    refine ⟨⟨a, haN⟩ * ⟨s, hsN⟩ * ⟨a, haN⟩⁻¹, Subgroup.mem_subgroupOf.mpr has, ?_⟩
    rw [map_mul, map_mul, map_inv, Steps165.actQuotPCore_of_mem ha haN]
  have hT1 : T ≠ ⊥ := by
    intro hT0
    apply hYS
    refine Steps165.le_normalizer_of_commutator_le ?_ hOS
    rw [Subgroup.commutator_le]
    intro y hy s hs
    have hs1 : actQuotPCore Y₀ ⟨s, hSM hs⟩ = 1 := by
      have hmem := hTmem s hs
      rw [hT0] at hmem
      exact hmem
    have hsc := (mem_sectionCentralizer_of_actQuotPCore_eq_one (hSM hs) hs1).2 y hy
    have e' : ⁅y, s⁆ = (s * y * s⁻¹ * y⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e']
    exact Subgroup.inv_mem _ hsc
  obtain ⟨p, hp, hp3, Ē, hĒp, hĒ1, hĒT, hgen⟩ := hK _ n hq (fun h1 => hmod (Or.inl h1)) hn2
    hQq hZ3 ⟨e.trans φ⟩ B hBe hB9 T hT2 hT1 hTn
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) with hπ
  set P := (Ē.comap π).map Y₀.subtype with hP
  have hO : CFSG.Open.pCoreOf 2 Y₀ = (CFSG.pCore 2 ↥Y₀).map Y₀.subtype := by
    rw [CFSG.Open.pCoreOf]
  have hkerπ : π.ker = CFSG.pCore 2 ↥Y₀ := QuotientGroup.ker_mk' _
  have hmemP : ∀ y (hy : y ∈ Y₀), y ∈ P ↔ π ⟨y, hy⟩ ∈ Ē := by
    intro y hy
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = ⟨y, hy⟩ := Subtype.ext hzy
      rw [← this]
      exact hz
    · intro hy'
      exact ⟨⟨y, hy⟩, hy', rfl⟩
  refine ⟨p, hp, hp3, P, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  ·
    rw [hO]
    refine Subgroup.map_mono fun z hz => ?_
    change π z ∈ Ē
    rw [show π z = 1 from (MonoidHom.mem_ker).mp (hkerπ.symm ▸ hz)]
    exact Ē.one_mem
  ·
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hconj : ∀ (g : G) (hg : g ∈ S) (z : G), z ∈ P → g * z * g⁻¹ ∈ P := by
      intro g hg z hz
      obtain ⟨⟨z', hzY⟩, hz', rfl⟩ := hz
      have hgz : g * z' * g⁻¹ ∈ Y₀ := (Subgroup.mem_normalizer_iff.mp (hSM hg) z').mp hzY
      refine (hmemP _ hgz).mpr ?_
      have h1 := hĒT _ (hTmem g hg) _ hz'
      rw [hπ, QuotientGroup.mk'_apply, Steps165.actQuotPCore_mk (hSM hg) z' hzY] at h1
      exact h1
    constructor
    · exact hconj s hs x
    · intro hx
      have := hconj s⁻¹ (S.inv_mem hs) _ hx
      simpa [mul_assoc] using this
  ·
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hĒp
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      rw [hk0', pow_zero] at hk
      exact hĒ1 (Subgroup.eq_bot_of_card_eq Ē hk)
    refine ⟨k, hk1, ?_⟩
    rw [hP, Subgroup.card_map_of_injective Y₀.subtype_injective,
      Steps165.card_comap_of_surjective' π (QuotientGroup.mk'_surjective _), hk, hkerπ, hO,
      Subgroup.card_map_of_injective Y₀.subtype_injective]
  ·
    intro x hxP hxO
    obtain ⟨⟨y, hy⟩, hyĒ, rfl⟩ := hxP
    have hy1 : π ⟨y, hy⟩ ≠ 1 := by
      intro h1
      apply hxO
      rw [hO]
      exact ⟨⟨y, hy⟩, hkerπ ▸ (MonoidHom.mem_ker).mpr h1, rfl⟩
    have hcl := hgen _ hyĒ hy1
    set J := ((Y₀ ⊓ Subgroup.normalizer (S : Set G)) ⊔ Subgroup.zpowers y).subgroupOf Y₀
      with hJ
    have hkerJ : π.ker ≤ J := by
      rw [hkerπ]
      intro z hz
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left ⟨z.2, ?_⟩)
      have hzO : (z : G) ∈ CFSG.Open.pCoreOf 2 Y₀ := by
        rw [hO]
        exact ⟨z, hz, rfl⟩
      exact Subgroup.le_normalizer (hOS hzO)
    have hmap : (⊤ : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) ≤ J.map π := by
      rw [← hcl, Subgroup.closure_le]
      rintro q (hq | hq)
      · obtain ⟨⟨y', hy'⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y₀) q
        refine ⟨⟨y', hy'⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left ⟨hy', ?_⟩), rfl⟩
        exact Steps165.mem_normalizer_of_fixed hSM hOS hy' fun s hs => hq _ (hTmem s hs)
      · rw [Set.mem_singleton_iff] at hq
        rw [hq]
        exact ⟨⟨y, hy⟩, Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)), rfl⟩
    intro z hz
    have hzJ : (⟨z, hz⟩ : ↥Y₀) ∈ J := by
      have h1 : π ⟨z, hz⟩ ∈ J.map π := hmap (Subgroup.mem_top _)
      have h2 : (⟨z, hz⟩ : ↥Y₀) ∈ (J.map π).comap π := h1
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerJ] at h2
      exact h2
    exact Subgroup.mem_subgroupOf.mp hzJ

theorem step165E_of_kfacts (h153 : Item153MainR) (hQ : Step171CommQ) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (h138 : Item138N) (hKU : KS165U) (hKL : KS165L) : Step165E :=
  step165E_of_commQ hQ h153 (centU165_of h1514 hMeets h138 hKU)
    (tor165L_of h1514 hMeets h138 hKL)

end CFSG.RankThree.PartTwo.Sec16
