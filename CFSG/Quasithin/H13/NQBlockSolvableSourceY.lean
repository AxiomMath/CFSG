module

public import CFSG.Quasithin.H13.NQBlockStrictCore
public import CFSG.Quasithin.H13.NQTermContainedCritical
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.LocalAnalysis.SteinbergCEFaithfulPerfectInclusion

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

abbrev nqOddPart (E : Subgroup G) : Subgroup G :=
  closure {y | y ∈ E ∧ Odd (orderOf y)}

abbrev nqCoreQuotPreimage (H : Subgroup G) {r : ℕ}
    (D : Subgroup (CFSG.pCore r (↥H ⧸ CFSG.pCore 2 ↥H))) : Subgroup G :=
  ((D.map (CFSG.pCore r (↥H ⧸ CFSG.pCore 2 ↥H)).subtype).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype

theorem nqOddPart_le (E : Subgroup G) : nqOddPart E ≤ E :=
  (closure_le _).mpr fun _ hy => hy.1

theorem normalizer_le_normalizer_nqOddPart (E : Subgroup G) :
    normalizer (E : Set G) ≤ normalizer (nqOddPart E : Set G) := by
  have key : ∀ g ∈ normalizer (E : Set G), ∀ y ∈ nqOddPart E, g * y * g⁻¹ ∈ nqOddPart E := by
    intro g hg y hy
    have hle : nqOddPart E ≤ (nqOddPart E).comap (MulAut.conj g).toMonoidHom := by
      refine (closure_le _).mpr ?_
      rintro x ⟨hxE, hxo⟩
      change g * x * g⁻¹ ∈ nqOddPart E
      refine subset_closure ⟨(mem_normalizer_iff.mp hg x).mp hxE, ?_⟩
      have h1 : orderOf (g * x * g⁻¹) = orderOf x :=
        orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
      rw [h1]
      exact hxo
    exact hle hy
  intro g hg
  exact mem_normalizer_of_conj_mem (key g hg) fun y hy => by
    have := key g⁻¹ (inv_mem hg) y hy
    rwa [inv_inv] at this

theorem noPQuotient_two_nqOddPart (E : Subgroup G) :
    QuasithinUnique.Setup.Campbell.NoPQuotient 2 ↥(nqOddPart E) := by
  intro N _ hq
  rw [eq_top_iff]
  intro y _
  have hle : nqOddPart E ≤ N.map (nqOddPart E).subtype := by
    refine (closure_le _).mpr ?_
    rintro x ⟨hxE, hxo⟩
    have hxY : x ∈ nqOddPart E := subset_closure ⟨hxE, hxo⟩
    refine ⟨⟨x, hxY⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff]
    obtain ⟨n, hn⟩ := hq (QuotientGroup.mk (⟨x, hxY⟩ : ↥(nqOddPart E)))
    have h1 : (QuotientGroup.mk (⟨x, hxY⟩ : ↥(nqOddPart E)) : ↥(nqOddPart E) ⧸ N) ^
        orderOf x = 1 := by
      rw [← QuotientGroup.mk_pow]
      have h2 : (⟨x, hxY⟩ : ↥(nqOddPart E)) ^ orderOf x = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, pow_orderOf_eq_one])
      rw [h2, QuotientGroup.mk_one]
    have hcop : Nat.Coprime (2 ^ n) (orderOf x) :=
      Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hxo)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one h1))
  obtain ⟨y', hy', hyy'⟩ := hle y.2
  rwa [show y = y' from Subtype.ext hyy'.symm]

@[expose] def AllComponentsContainedSolvableSourceY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → T ≤ H → H ≠ M → (∀ C ∈ cComp H, C ≤ M) →
      ∃ (r : ℕ) (D : Subgroup (CFSG.pCore r (↥H ⧸ CFSG.pCore 2 ↥H))) (Y : Subgroup G),
        r.Prime ∧ r ≠ 2 ∧ NQTerm.IsOddCriticalDetector r D ∧ Monoid.exponent ↥D = r ∧
        Subgroup.upperCentralSeries ↥D 2 = ⊤ ∧ ¬ nqCoreQuotPreimage H D ≤ M ∧
        Y = nqOddPart (nqCoreQuotPreimage H D) ∧
        (nqCoreQuotPreimage H D : Set G) = (pCoreOf 2 H : Set G) * (Y : Set G) ∧
        Y ≤ H ∧ (Y.subgroupOf H).Normal ∧ Y ≤ (CFSG.solvableRadical ↥H).map H.subtype ∧
        ¬ Y ≤ M ∧ ⁅quasithinOmegaOneCenter T, Y⁆ ≠ ⊥ ∧
        QuasithinUnique.Setup.Campbell.NoPQuotient 2 ↥Y ∧ pCoreOf 2 Y ≠ ⊥ ∧
        pCoreOf 2 Y = Y ⊓ pCoreOf 2 H ∧
        (Y.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) =
          D.map (CFSG.pCore r (↥H ⧸ CFSG.pCore 2 ↥H)).subtype ∧
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥D) ∧ Group.IsSolvable ↥Y ∧
        (∀ q : ℕ, q.Prime → q ∣ Nat.card ↥Y → q = 2 ∨ q = r) ∧
        Monoid.exponent (↥Y ⧸ CFSG.pCore 2 ↥Y) = r ∧
        Subgroup.upperCentralSeries (↥Y ⧸ CFSG.pCore 2 ↥Y) 2 = ⊤ ∧
        CFSG.pRank r (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ 2 ∧ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ r ^ 3

variable [Finite G]

omit [Finite G] in
theorem odd_decomposition_of_mem_preimage {H : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {D : Subgroup (CFSG.pCore r (↥H ⧸ CFSG.pCore 2 ↥H))} (hDr : ∀ x ∈ D, x ^ r = 1) {e : ↥H}
    (he : e ∈ (D.map (CFSG.pCore r (↥H ⧸ CFSG.pCore 2 ↥H)).subtype).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) :
    ∃ p ∈ CFSG.pCore 2 ↥H, ∃ y ∈ (D.map (CFSG.pCore r (↥H ⧸ CFSG.pCore 2 ↥H)).subtype).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)), Odd (orderOf y) ∧ e = p * y := by
  classical
  have her : e ^ r ∈ CFSG.pCore 2 ↥H := by
    obtain ⟨x, hx, hxe⟩ := mem_comap.mp he
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥H), MonoidHom.mem_ker, map_pow, ← hxe]
    change ((x : ↥H ⧸ CFSG.pCore 2 ↥H)) ^ r = 1
    rw [← Subgroup.coe_pow, hDr x hx, Subgroup.coe_one]
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (⟨e ^ r, her⟩ : ↥(CFSG.pCore 2 ↥H))
  have h1 : e ^ (r * 2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    rw [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [pow_mul]
    exact this
  have hcop : Nat.Coprime r (2 ^ k) :=
    ((Nat.coprime_primes hr Nat.prime_two).mpr hr2).pow_right k
  obtain ⟨a, b, hab⟩ := Nat.Coprime.isCoprime hcop
  refine ⟨e ^ ((r : ℤ) * a), ?_, e ^ (((2 ^ k : ℕ) : ℤ) * b), zpow_mem he _, ?_, ?_⟩
  · rw [zpow_mul, zpow_natCast]
    exact zpow_mem her a
  · have hy : (e ^ (((2 ^ k : ℕ) : ℤ) * b)) ^ r = 1 := by
      rw [← zpow_natCast, ← zpow_mul,
        show ((2 ^ k : ℕ) : ℤ) * b * (r : ℤ) = ((r * 2 ^ k : ℕ) : ℤ) * b by push_cast; ring,
        zpow_mul, zpow_natCast, h1, one_zpow]
    rcases (Nat.dvd_prime hr).mp (orderOf_dvd_of_pow_eq_one hy) with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact hr.odd_of_ne_two hr2
  · rw [← zpow_add]
    conv_lhs => rw [← zpow_one e]
    congr 1
    linarith [hab]

omit [Finite G] in
theorem nqCoreQuotPreimage_facts {H : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {D : Subgroup (CFSG.pCore r (↥H ⧸ CFSG.pCore 2 ↥H))} (hDr : ∀ x ∈ D, x ^ r = 1) :
    (nqCoreQuotPreimage H D : Set G) =
        (pCoreOf 2 H : Set G) * (nqOddPart (nqCoreQuotPreimage H D) : Set G) ∧
      ((nqOddPart (nqCoreQuotPreimage H D)).subgroupOf H).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) =
        D.map (CFSG.pCore r (↥H ⧸ CFSG.pCore 2 ↥H)).subtype := by
  classical
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπdef
  set D' := D.map (CFSG.pCore r (↥H ⧸ CFSG.pCore 2 ↥H)).subtype with hD'def
  set E' := D'.comap π with hE'def
  set E := nqCoreQuotPreimage H D with hEdef
  set Y := nqOddPart E with hYdef
  have hQ : (CFSG.pCore 2 ↥H).map H.subtype = pCoreOf 2 H := by
    unfold pCoreOf
    try with_reducible rfl
  have hPE' : CFSG.pCore 2 ↥H ≤ E' := by
    intro x hx
    rw [hE'def, mem_comap]
    have : π x = 1 := by
      rw [← MonoidHom.mem_ker, hπdef, QuotientGroup.ker_mk']
      exact hx
    rw [this]
    exact one_mem _
  have hYodd : ∀ y ∈ E', Odd (orderOf y) → (y : G) ∈ Y := fun y hy hyo =>
    subset_closure ⟨⟨y, hy, rfl⟩, by rw [Subgroup.orderOf_coe]; exact hyo⟩
  have hYE : Y ≤ E := nqOddPart_le E
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · ext g
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨p, hp, y, hy, hyo, rfl⟩ := odd_decomposition_of_mem_preimage hr hr2 hDr he
      exact ⟨p, hQ ▸ mem_map_of_mem _ hp, y, hYodd y hy hyo, rfl⟩
    · rintro ⟨p, hp, y, hy, rfl⟩
      refine mul_mem ?_ (hYE hy)
      rw [← hQ] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      exact mem_map_of_mem _ (hPE' hp')
  · rw [map_le_iff_le_comap]
    intro y hy
    obtain ⟨e, he, hee⟩ := hYE (mem_subgroupOf.mp hy)
    have : e = y := Subtype.ext hee
    rw [← this]
    exact he
  · intro d hd
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) d
    have he : e ∈ E' := hd
    obtain ⟨p, hp, y, hy, hyo, rfl⟩ := odd_decomposition_of_mem_preimage hr hr2 hDr he
    refine ⟨y, mem_subgroupOf.mpr (hYodd y hy hyo), ?_⟩
    have hp1 : π p = 1 := by
      rw [← MonoidHom.mem_ker, hπdef, QuotientGroup.ker_mk']
      exact hp
    change π y = π (p * y)
    rw [map_mul, hp1, one_mul]

theorem upperCentralSeries_two_eq_top {Q : Type*} [Group Q]
    (h : ∀ a b c : Q, ⁅a, b⁆ * c = c * ⁅a, b⁆) : Subgroup.upperCentralSeries Q 2 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
  intro z
  exact (h x y z).symm

theorem exists_escaping_detector {T L M H : Subgroup G} (h : QTNQ T L M) (hTH : T ≤ H)
    (hall : ∀ C ∈ cComp H, C ≤ M) (hstrict : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) :
    ∃ r ∈ NQTerm.oddPrimeCoreSupport (↥H ⧸ CFSG.pCore 2 ↥H),
      ∃ D : Subgroup (CFSG.pCore r (↥H ⧸ CFSG.pCore 2 ↥H)),
        NQTerm.IsOddCriticalDetector r D ∧ ¬ nqCoreQuotPreimage H D ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Γ := ↥H ⧸ CFSG.pCore 2 ↥H with hΓdef
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπdef
  have hO2 : CFSG.pCore 2 Γ = ⊥ := CFSG.RankThree.PartTwo.Sec18.pCore_quotient_pCore_eq_bot 2
  obtain ⟨hex, -⟩ := NQTerm.odd_critical_fitting_layer_detects_every_two_subgroup Γ hO2
  by_contra hall'
  simp only [not_exists, not_and, not_not] at hall'
  set D : (r : ℕ) → Subgroup (CFSG.pCore r Γ) := fun r =>
    if hr : r ∈ NQTerm.oddPrimeCoreSupport Γ then Classical.choose (hex r hr) else ⊥ with hDdef
  have hD : ∀ r ∈ NQTerm.oddPrimeCoreSupport Γ, NQTerm.IsOddCriticalDetector r (D r) := by
    intro r hr
    simp only [hDdef, hr, ↓reduceDIte]
    exact Classical.choose_spec (hex r hr)
  set W := (M.subgroupOf H).map π with hWdef
  have hPT : pCoreOf 2 H ≤ T := QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
    (NQCore.isSylowIn_of_quasithin h.sylow hTH)
  have hQ : (CFSG.pCore 2 ↥H).map H.subtype = pCoreOf 2 H := by
    unfold pCoreOf
    try with_reducible rfl
  have hPM : CFSG.pCore 2 ↥H ≤ M.subgroupOf H := fun x hx =>
    mem_subgroupOf.mpr (h.t_le (hPT (hQ ▸ mem_map_of_mem _ hx)))
  have hWc : W.comap π = M.subgroupOf H := by
    rw [hWdef, comap_map_eq, hπdef, QuotientGroup.ker_mk', sup_eq_left.mpr hPM]
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hN : Group.IsSolvable ↥(CFSG.pCore 2 ↥H) := by
    have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥H) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
    infer_instance
  have hlayer : CFSG.layer Γ ≤ W := by
    refine sSup_le fun J hJ => ?_
    obtain ⟨hC, hCJ⟩ := (Ccomponent_solvable_quotient_bijection (CFSG.pCore 2 ↥H) hN).2 J
      (isCComponent_of_isComponent hJ)
    have hCH := map_subtype_mem_cComp (mem_cComp_top_iff_isCComponent.mpr hC)
    have hCM := map_le_iff_le_comap.mp (hall _ hCH)
    rw [← hCJ]
    exact map_mono hCM
  have hDW : ∀ r ∈ NQTerm.oddPrimeCoreSupport Γ,
      (D r).map (CFSG.pCore r Γ).subtype ≤ W := by
    intro r hr
    have h2 := map_le_iff_le_comap.mp (hall' r hr (D r) (hD r hr))
    calc (D r).map (CFSG.pCore r Γ).subtype =
          (((D r).map (CFSG.pCore r Γ).subtype).comap π).map π :=
          (map_comap_eq_self_of_surjective hsurj _).symm
      _ ≤ W := map_mono h2
  have hΘ : NQTerm.oddCriticalLayer Γ D ≤ W := sup_le hlayer (iSup₂_le hDW)
  have hM : ((NQTerm.oddCriticalLayer Γ D).comap π).map H.subtype ≤ M := by
    rw [map_le_iff_le_comap]
    exact (comap_mono hΘ).trans hWc.le
  have heq := NQTerm.contained_critical_fitting_layer_inter_two_core H M D hD hM
  rw [← CFSG.LocalAnalysis.FaithfulPerfectInclusion.pCoreOf_eq_inSubgroup,
    ← CFSG.LocalAnalysis.FaithfulPerfectInclusion.pCoreOf_eq_inSubgroup] at heq
  exact hstrict heq

theorem allComponentsContainedSolvableSourceY_of (hsc : DifferentMaxTwoLocalStrictCore) :
    AllComponentsContainedSolvableSourceY := by
  intro G _ _ T L M h H hH hTH hHM hall
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP1, -, -, hstrict⟩ := hsc G T L M h H hH hTH hHM
  obtain ⟨r, ⟨hr, hr2, -⟩, D, hD, hEM⟩ := exists_escaping_detector h hTH hall hstrict
  have : Fact r.Prime := ⟨hr⟩
  have hD' := hD
  obtain ⟨hD1, hDc, hDr, hDcomm, -⟩ := hD'
  obtain ⟨hEPY, hπY⟩ := nqCoreQuotPreimage_facts hr hr2 hDr
  set Γ := ↥H ⧸ CFSG.pCore 2 ↥H with hΓdef
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπdef
  set D' := D.map (CFSG.pCore r Γ).subtype with hD'def
  set E := nqCoreQuotPreimage H D with hEdef
  set Y := nqOddPart E with hYdef
  have hEH : E ≤ H := map_subtype_le _
  have hYE : Y ≤ E := nqOddPart_le E
  have hYH : Y ≤ H := hYE.trans hEH
  have hD'n : D'.Normal := by
    have := hDc
    have : D'.Characteristic := characteristic_of_characteristic_of_characteristic
    infer_instance
  have hHE : H ≤ normalizer (E : Set G) := le_normalizer_map_of_normal (hD'n.comap π)
  have hHY : H ≤ normalizer (Y : Set G) := hHE.trans (normalizer_le_normalizer_nqOddPart E)
  have hYn : (Y.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hYH).mpr hHY
  have hPT : pCoreOf 2 H ≤ T := QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
    (NQCore.isSylowIn_of_quasithin h.sylow hTH)
  have hYM : ¬ Y ≤ M := by
    intro hY
    apply hEM
    intro e he
    have he' : e ∈ (E : Set G) := he
    rw [hEPY] at he'
    obtain ⟨p, hp, y, hy, rfl⟩ := he'
    exact mul_mem (h.t_le (hPT hp)) (hY hy)
  have hH2 : QuasithinUnique.CharTwo H :=
    QuasithinUnique.charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot h.qtke.2.1
      ⟨le_top, h.sylow.1, by
        change ¬ 2 ∣ T.relIndex ⊤
        rw [relIndex_top_right]
        exact h.sylow.2⟩ hTH hP1
  have hY2 : QuasithinUnique.CharTwo Y := QuasithinUnique.CharTwo.of_normal hH2 hYH hYn
  have hqY : pCoreOf 2 Y ≠ ⊥ := by
    intro h0
    apply hYM
    intro y hy
    have hy' : y ∈ pCoreOf 2 Y := hY2 (mem_inf.mpr ⟨hy, by
      rw [h0]
      exact mem_centralizer_iff.mpr fun z hz => by
        rw [(mem_bot.mp hz : z = 1), one_mul, mul_one]⟩)
    rw [h0, mem_bot] at hy'
    rw [hy']
    exact one_mem M
  have hqYeq : pCoreOf 2 Y = Y ⊓ pCoreOf 2 H := by
    apply le_antisymm
    · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
        (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYH)
          (hHY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y))
    · refine le_pCoreOf_of_subgroupOf_normal inf_le_left ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
      rw [normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro y hy
      exact mem_normalizer_inf (le_normalizer hy)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hYH hy))
  have hZY : ⁅quasithinOmegaOneCenter T, Y⁆ ≠ ⊥ := by
    intro h0
    apply hYM
    rw [commutator_eq_bot_iff_le_centralizer] at h0
    exact (le_centralizer_iff.mp h0).trans h.centralizer_le
  set ψ₀ : ↥Y →* Γ := π.comp (Subgroup.inclusion hYH) with hψ₀def
  have hψ₀D : ∀ y : ↥Y, ψ₀ y ∈ D' := fun y => by
    rw [← hπY]
    exact ⟨Subgroup.inclusion hYH y, mem_subgroupOf.mpr y.2, rfl⟩
  set ψ : ↥Y →* ↥D' := ψ₀.codRestrict D' hψ₀D with hψdef
  have hψs : Function.Surjective ψ := by
    rintro ⟨d, hd⟩
    rw [← hπY] at hd
    obtain ⟨y, hy, rfl⟩ := hd
    exact ⟨⟨y, mem_subgroupOf.mp hy⟩, Subtype.ext rfl⟩
  have hker : ψ.ker = CFSG.pCore 2 ↥Y := by
    ext y
    rw [MonoidHom.mem_ker, mem_pCore_iff_mem_pCoreOf, hqYeq]
    constructor
    · intro hy
      have h1 : ψ₀ y = 1 := congrArg Subtype.val hy
      rw [hψ₀def, MonoidHom.comp_apply, hπdef, ← MonoidHom.mem_ker, QuotientGroup.ker_mk',
        mem_pCore_iff_mem_pCoreOf] at h1
      exact mem_inf.mpr ⟨y.2, h1⟩
    · intro hy
      apply Subtype.ext
      change ψ₀ y = 1
      rw [hψ₀def, MonoidHom.comp_apply, hπdef, ← MonoidHom.mem_ker, QuotientGroup.ker_mk',
        mem_pCore_iff_mem_pCoreOf]
      exact (mem_inf.mp hy).2
  have eD : ↥D ≃* ↥D' := D.equivMapOfInjective _ (CFSG.pCore r Γ).subtype_injective
  have e : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥D :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)).trans eD.symm
  have hD2 : IsPGroup r ↥D := (CFSG.pCore_isPGroup (p := r) (G := Γ)).to_subgroup D
  have hDexp : ∀ g : ↥D, g ^ r = 1 := fun g => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hDr g g.2)
  have hDexpr : Monoid.exponent ↥D = r := by
    rcases (Nat.dvd_prime hr).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hDexp) with h1 | h1
    · exfalso
      apply hD1
      have : Subsingleton ↥D := Monoid.exp_eq_one_iff.mp h1
      rw [eq_bot_iff]
      intro x hx
      rw [mem_bot]
      exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥D) 1)
    · exact h1
  have hDcls : ∀ a b c : ↥D, ⁅a, b⁆ * c = c * ⁅a, b⁆ := by
    intro a b c
    apply Subtype.ext
    have hab : ⁅(a : ↥(CFSG.pCore r Γ)), (b : ↥(CFSG.pCore r Γ))⁆ ∈
        D ⊓ centralizer (D : Set ↥(CFSG.pCore r Γ)) :=
      hDcomm (commutator_mem_commutator a.2 (mem_top _))
    have h1 := (mem_centralizer_iff.mp (mem_inf.mp hab).2) c c.2
    have hc : ((⁅a, b⁆ : ↥D) : ↥(CFSG.pCore r Γ)) =
        ⁅(a : ↥(CFSG.pCore r Γ)), (b : ↥(CFSG.pCore r Γ))⁆ :=
      map_commutatorElement D.subtype a b
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact h1.symm
  have hDucs : Subgroup.upperCentralSeries ↥D 2 = ⊤ := upperCentralSeries_two_eq_top hDcls
  have hQ2 : IsPGroup r (↥Y ⧸ CFSG.pCore 2 ↥Y) := hD2.of_equiv e.symm
  have hQexp : ∀ x : ↥Y ⧸ CFSG.pCore 2 ↥Y, x ^ r = 1 := fun x => by
    apply e.injective
    rw [map_pow, hDexp, map_one]
  have hQexpr : Monoid.exponent (↥Y ⧸ CFSG.pCore 2 ↥Y) = r := by
    rw [Monoid.exponent_eq_of_mulEquiv e, hDexpr]
  have hQcls : Subgroup.upperCentralSeries (↥Y ⧸ CFSG.pCore 2 ↥Y) 2 = ⊤ :=
    upperCentralSeries_two_eq_top fun a b c => by
      apply e.injective
      rw [map_mul, map_mul, map_commutatorElement]
      exact hDcls _ _ _
  have hq2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥Y) := CFSG.pCore_isPGroup
  have : Group.IsSolvable ↥(CFSG.pCore 2 ↥Y) := by
    have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥Y) := hq2.isNilpotent
    infer_instance
  have : Group.IsSolvable (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    have : Group.IsNilpotent (↥Y ⧸ CFSG.pCore 2 ↥Y) := hQ2.isNilpotent
    infer_instance
  have hYs : Group.IsSolvable ↥Y :=
    Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥Y).subtype
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) (by rw [QuotientGroup.ker_mk', range_subtype])
  have hYR : Y ≤ (CFSG.solvableRadical ↥H).map H.subtype := by
    obtain ⟨-, -, hmax, -⟩ :=
      CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization ↥H
    have hYs' : Group.IsSolvable ↥(Y.subgroupOf H) :=
      Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hYH).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have h2 := map_mono (f := H.subtype) (hmax _ hYn hYs')
    rwa [map_subgroupOf_eq_of_le hYH] at h2
  obtain ⟨a, ha⟩ := hq2.exists_card_eq
  have hprimes : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥Y → q = 2 ∨ q = r := by
    intro q hq hqY
    obtain ⟨b, hb⟩ := hQ2.exists_card_eq
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Y), hb, ha] at hqY
    rcases (Nat.Prime.dvd_mul hq).mp hqY with h1 | h1
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow h1))
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h1))
  have hcop : ¬ r ∣ Nat.card ↥(CFSG.pCore 2 ↥Y) := by
    rw [ha]
    intro hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
  have hrank : CFSG.pRank r (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ 2 := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr
      (CFSG.pCore 2 ↥Y) hcop]
    calc CFSG.pRank r ↥Y = CFSG.Open.pRank r (⊤ : Subgroup ↥Y) :=
          CFSG.SectionRank.pRank_eq_open_pRank_top r ↥Y
      _ ≤ CFSG.Open.pRank r ((⊤ : Subgroup ↥Y).map Y.subtype) :=
          CFSG.SectionRank.pRank_le_map hr.one_lt Y.subtype Y.subtype_injective ⊤
      _ ≤ CFSG.Open.pRank r H := CFSG.SectionRank.pRank_mono hr.one_lt (by
          rintro _ ⟨y, -, rfl⟩
          exact hYH y.2)
      _ ≤ CFSG.Open.evenRank G :=
          CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr hr2 H hH.1
      _ = CFSG.Assembly.evenRank G := rfl
      _ ≤ 2 := h.qtke.2.2
  have hcard : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ r ^ 3 :=
    (CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound hQ2 hQexp (by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact hrank)).1
  exact ⟨r, D, Y, hr, hr2, hD, hDexpr, hDucs, hEM, rfl, hEPY, hYH, hYn, hYR, hYM, hZY,
    noPQuotient_two_nqOddPart E, hqY, hqYeq, hπY, ⟨e⟩, hYs, hprimes, hQexpr, hQcls, hrank, hcard⟩

theorem allComponentsContainedSolvableSourceY_holds :
    AllComponentsContainedSolvableSourceY :=
  allComponentsContainedSolvableSourceY_of differentMaxTwoLocalStrictCore_holds

end CFSG.Quasithin.H13.NQBlock
