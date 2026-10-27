module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.GroupTheory.CentralizeSolvableOfPCores
public import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
public import CFSG.GroupTheory.CoprimeCosetFixed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (PPrimeCoreIn)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

open scoped commutatorElement

private theorem k89ch_pCoreOf_normal {Q : Type} [Group Q] (p : ℕ) {M : Subgroup Q}
    (hM : M.Normal) : (CFSG.Open.pCoreOf p M).Normal := by
  have hinst_ := CFSG.LieType.BorelTits.pCore_characteristic p (G := ↥M)
  refine ⟨fun x hx g => ?_⟩
  have hg : g ∈ Subgroup.normalizer ((M : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hM.conj_mem h hh g, fun hh => ?_⟩
    have := hM.conj_mem _ hh g⁻¹
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at this
  have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (CFSG.Open.pCore p ↥M) hg
  exact (Subgroup.mem_normalizer_iff.mp this x).mp hx

private theorem k89ch_pCore_quotient_map_bot {X : Type} [Group X] [Finite X]
    (p : ℕ) [Fact p.Prime] {H : Subgroup X} (_hH : H.Normal)
    {N : Subgroup X} [N.Normal] (hN : N = (CFSG.pCore p ↥H).map H.subtype) :
    CFSG.Open.pCoreOf p (H.map (QuotientGroup.mk' N)) = ⊥ := by
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  let φ : ↥H →* X ⧸ N := π.comp H.subtype
  have hker : φ.ker = CFSG.pCore p ↥H := by
    rw [show φ.ker = (MonoidHom.ker π).comap H.subtype from
        (MonoidHom.comap_ker π H.subtype).symm,
      QuotientGroup.ker_mk', hN, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hrange : φ.range = H.map π := by
    rw [show φ = π.comp H.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
  let M : Subgroup (X ⧸ N) := H.map π
  let ψ : ↥H →* ↥M :=
    (MulEquiv.subgroupCongr (show φ.range = M from hrange)).toMonoidHom.comp φ.rangeRestrict
  have hψker : ψ.ker = CFSG.pCore p ↥H := by
    have h1 : ψ.ker = φ.ker := by
      ext x
      simp only [MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      constructor
      · intro h; exact congrArg Subtype.val h
      · intro h; exact Subtype.ext h
    rw [h1, hker]
  have hQnorm : ((CFSG.pCore p ↥M).comap ψ).Normal :=
    Subgroup.Normal.comap (CFSG.pCore_normal (p := p) (G := ↥M)) ψ
  have hQp : IsPGroup p ((CFSG.pCore p ↥M).comap ψ) :=
    IsPGroup.comap_of_ker_isPGroup (CFSG.pCore_isPGroup (G := ↥M) (p := p)) ψ (by
      rw [hψker]; exact CFSG.pCore_isPGroup (G := ↥H) (p := p))
  have hQle : (CFSG.pCore p ↥M).comap ψ ≤ CFSG.pCore p ↥H :=
    CFSG.LieType.BorelTits.le_pCore (r := p) hQnorm hQp
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨⟨x, hx.1⟩, Subtype.ext hx.2⟩
  have hbot : CFSG.pCore p ↥M = ⊥ := by
    have hmapQ : Subgroup.map ψ ((CFSG.pCore p ↥M).comap ψ) = CFSG.pCore p ↥M :=
      Subgroup.map_comap_eq_self (f := ψ) (H := CFSG.pCore p ↥M) (by
        rw [MonoidHom.range_eq_top.mpr hsurj]; exact le_top)
    have hle : Subgroup.map ψ ((CFSG.pCore p ↥M).comap ψ) ≤ (⊥ : Subgroup ↥M) := by
      calc Subgroup.map ψ ((CFSG.pCore p ↥M).comap ψ)
          ≤ Subgroup.map ψ (CFSG.pCore p ↥H) := Subgroup.map_mono hQle
        _ = (⊥ : Subgroup ↥M) := by
            rw [← hψker]
            refine le_bot_iff.mp ?_
            intro y hy
            obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
            simpa using hx
    rw [hmapQ] at hle
    exact le_bot_iff.mp hle
  rw [CFSG.Open.pCoreOf, hbot, Subgroup.map_bot]

private theorem k89ch_pCoreOf_eq_bot_of_not_dvd {G : Type} [Group G] [Finite G] {q : ℕ}
    (hq : q.Prime) {H : Subgroup G} (h : ¬ q ∣ Nat.card H) :
    CFSG.Open.pCoreOf q H = ⊥ := by
  have hinst_ : Fact q.Prime := ⟨hq⟩
  have hbot : CFSG.pCore q ↥H = ⊥ := by
    rw [← Subgroup.card_le_one_iff_eq_bot]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (G := ↥H) (p := q))
    have hdvd : q ^ k ∣ Nat.card H := by
      rw [← hk]
      exact Subgroup.card_subgroup_dvd_card _
    have hk0 : k = 0 := by
      by_contra hkne
      exact h ((dvd_pow_self q hkne).trans hdvd)
    rw [hk, hk0, pow_zero]
  rw [CFSG.Open.pCoreOf, hbot, Subgroup.map_bot]

private theorem k89ch_card_of_isA6Z3 {Y : Type} [Group Y] (h : IsA6Z3 Y) :
    Nat.card Y = 1080 := by
  obtain ⟨-, hz, e⟩ := h
  have hq : Nat.card (Y ⧸ Subgroup.center Y) = 360 := by
    obtain ⟨e⟩ := e
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
  rw [hq, hz] at hcard
  omega

private theorem k89ch_not_dvd_card_of_isA6Z3 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (halt6 : IsA6Z3 (Bar2 K)) {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q) :
    ¬ q ∣ Nat.card K := by
  have hinst_ : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (Bar2 K) = 1080 := k89ch_card_of_isA6Z3 halt6
  have hdecomp := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (G := ↥K) (p := 2))
  have hK : Nat.card K = 1080 * 2 ^ k := by
    rw [hdecomp, hcard, hk]
  rw [hK]
  intro hdvd
  rcases hq.dvd_mul.mp hdvd with h1 | h2
  · have hle : q ≤ 1080 := Nat.le_of_dvd (by norm_num) h1
    interval_cases q <;> norm_num at hq <;> norm_num at h1
  · have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h2)
    have h2le : 2 ≤ q := hq.two_le
    omega

private theorem k89ch_perfect {G : Type} [Group G] {K : Subgroup G}
    (hperf : ⁅K, K⁆ = K) : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator]
  simp only [Subgroup.map_top, Subgroup.range_subtype]
  rw [hperf]

private theorem k89ch_commutator_subgroupOf {Y : Type} [Group Y] (D : Subgroup Y) :
    _root_.commutator ↥D = ⁅D, D⁆.subgroupOf D := by
  apply Subgroup.map_injective D.subtype_injective
  show Subgroup.map D.subtype (⁅(⊤ : Subgroup ↥D), ⊤⁆) = _
  rw [Subgroup.map_commutator]
  simp only [Subgroup.map_top, Subgroup.range_subtype]
  rw [Subgroup.subgroupOf_map_subtype]
  exact le_antisymm (le_inf le_rfl (Subgroup.commutator_le_of_le le_rfl le_rfl)) inf_le_left

private theorem k89ch_triv_quot_commutator {Y : Type} [Group Y] {A D : Subgroup Y}
    (conjA : ↥A →* MulAut ↥D)
    (hconjA : ∀ (a : ↥A) (d : ↥D), ((conjA a d : ↥D) : Y) = (a : Y) * (d : Y) * (a : Y)⁻¹)
    (htriv : ∀ a : ↥A,
      CFSG.OrderReductions.FrattiniAutomorphisms.quotientAction (frattini ↥D) conjA a = 1) :
    ⁅D, A⁆ ≤ (frattini ↥D).map D.subtype := by
  rw [Subgroup.commutator_le]
  intro d hd a ha
  have h1 : CFSG.OrderReductions.FrattiniAutomorphisms.quotientAction (frattini ↥D) conjA
      (⟨a, ha⟩ : ↥A) ((QuotientGroup.mk' (frattini ↥D)) (⟨d, hd⟩ : ↥D)) = (⟨d, hd⟩ : ↥D) := by
    have := congrArg (fun e : MulAut (↥D ⧸ frattini ↥D) =>
      e ((QuotientGroup.mk' (frattini ↥D)) (⟨d, hd⟩ : ↥D))) (htriv (⟨a, ha⟩ : ↥A))
    exact this
  rw [CFSG.OrderReductions.FrattiniAutomorphisms.quotientAction_apply] at h1
  have hmem : conjA (⟨a, ha⟩ : ↥A) (⟨d, hd⟩ : ↥D) * (⟨d, hd⟩ : ↥D)⁻¹ ∈ frattini ↥D := by
    have := (QuotientGroup.eq_iff_div_mem).mp h1
    rwa [div_eq_mul_inv] at this
  have hcoe : (((conjA (⟨a, ha⟩ : ↥A) (⟨d, hd⟩ : ↥D) *
      (⟨d, hd⟩ : ↥D)⁻¹)⁻¹ : ↥D) : Y) = ⁅d, a⁆ := by
    push_cast
    rw [hconjA]
    rw [commutatorElement_def]; group
  exact Subgroup.mem_map.mpr ⟨_, (frattini ↥D).inv_mem hmem, hcoe⟩

private theorem k89ch_q_component
    {Y : Type} [Group Y] [Finite Y] (q : ℕ) (hq : q.Prime) (hq7 : 7 ≤ q)
    {A D₀ : Subgroup Y} (hAD₀ : A ≤ Subgroup.normalizer (D₀ : Set Y))
    (hD₀q : IsPGroup q D₀) (hne : ⁅D₀, A⁆ ≠ ⊥)
    (hD₀rank : CFSG.Open.pRank q D₀ ≤ 2) (hAq : ¬ q ∣ Nat.card A)
    {K : Type} [Group K] [Finite K] (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (halt6 : IsA6Z3 (K ⧸ CFSG.pCore 2 K))
    (surj : K →* A) (hsurj : Function.Surjective surj)
    (hQMin : S889QMin) (hQRank : S889QRank) (hDick : S889Dickson) :
    False := by
  have hinst_ : Fact q.Prime := ⟨hq⟩
  obtain ⟨D, hDD₀, hAD, hDexp, hDcl, hne', -⟩ :=
    hQMin Y q hq (by omega) A D₀ hD₀q hAq hAD₀ hne
  have hDq : IsPGroup q D := hD₀q.to_le hDD₀
  have hDrank : CFSG.Open.pRank q D ≤ 2 :=
    (CFSG.SectionRank.pRank_mono hq.one_lt hDD₀).trans hD₀rank
  have hDqFact : Fact (IsPGroup q ↥D) := ⟨hDq⟩
  have hcomm_le_frat : ⁅D, D⁆.subgroupOf D ≤ frattini ↥D := by
    rw [← k89ch_commutator_subgroupOf (Y := Y) D]
    exact CFSG.commutator_le_frattini_of_isPGroup (R := ↥D) (p := q)
  have hDindex : (frattini ↥D).index ≤ q ^ 2 :=
    (Subgroup.index_antitone hcomm_le_frat).trans
      (hQRank Y q hq (by omega) D hDexp hDcl hDrank)
  let conjA : ↥A →* MulAut ↥D :=
    D.normalizerMonoidHom.comp (Subgroup.inclusion hAD)
  have hconjA : ∀ (a : ↥A) (d : ↥D), ((conjA a d : ↥D) : Y) = (a : Y) * (d : Y) * (a : Y)⁻¹ :=
    fun a d => Subgroup.normalizerMonoidHom_apply_apply_coe D _ d
  let action : K →* MulAut (↥D ⧸ frattini ↥D) :=
    (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAction (frattini ↥D) conjA).comp surj
  let _instComm : CommGroup (↥D ⧸ frattini ↥D) :=
    CFSG.OrderReductions.ElementaryRepresentation.frattiniQuotientCommGroup q hDq
  let _instMod : Module (ZMod q) (Additive (↥D ⧸ frattini ↥D)) :=
    CFSG.OrderReductions.ElementaryRepresentation.frattiniQuotientModule q hDq
  let V := Additive (↥D ⧸ frattini ↥D)
  have hfrat_le_comm : frattini ↥D ≤ ⁅D, D⁆.subgroupOf D := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (R := ↥D) (p := q)]
    refine (Subgroup.closure_le (K := ⁅D, D⁆.subgroupOf D)).mpr ?_
    intro x hx
    rcases hx with hx | ⟨y, rfl⟩
    · rwa [← k89ch_commutator_subgroupOf (Y := Y) D]
    · change (y : ↥D) ^ q ∈ _
      rw [show (y : ↥D) ^ q = 1 from Subtype.ext (by simpa using hDexp (y : Y) y.2)]
      exact Subgroup.one_mem _
  have hcardΦ : Nat.card (↥D ⧸ frattini ↥D) ≤ q ^ 2 := by
    have h1 : Nat.card (↥D ⧸ frattini ↥D) = (frattini ↥D).index := Subgroup.index_eq_card _
    rw [h1]
    exact hDindex
  let _instFintype : Fintype V := Fintype.ofFinite V
  have hcardfin : q ^ Module.finrank (ZMod q) V = Nat.card V := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod q) (V := V), ZMod.card]
  have hdim : Module.finrank (ZMod q) V ≤ 2 := by
    have hpow : q ^ Module.finrank (ZMod q) V ≤ q ^ 2 := by
      rw [hcardfin]
      exact hcardΦ
    exact (Nat.pow_le_pow_iff_right hq.one_lt).mp hpow
  have hdick := hDick q hq hq7 K hperf halt6 V hdim
    (CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation q action)
  have htriv : ∀ a : ↥A,
      CFSG.OrderReductions.FrattiniAutomorphisms.quotientAction (frattini ↥D) conjA a = 1 := by
    intro a
    obtain ⟨k, hk⟩ := hsurj a
    have h1 : action k = 1 := by
      have hk1 : (CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation q action) k = 1 :=
        hdick k
      ext v
      have hv := congrArg (fun e : Module.End (ZMod q) V => e (Additive.ofMul v)) hk1
      rw [CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation_apply] at hv
      exact Additive.ofMul.injective (by simpa using hv)
    have h2 : CFSG.OrderReductions.FrattiniAutomorphisms.quotientAction (frattini ↥D) conjA
        (surj k) = 1 := h1
    rwa [← hk]
  have hcomm_le_Φ : ⁅D, A⁆ ≤ (frattini ↥D).map D.subtype :=
    k89ch_triv_quot_commutator conjA hconjA htriv
  have hΦle_map : (frattini ↥D).map D.subtype ≤ ⁅D, D⁆ := by
    have h := Subgroup.map_mono (f := D.subtype) hfrat_le_comm
    have heq : (⁅D, D⁆.subgroupOf D).map D.subtype = ⁅D, D⁆ := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact le_antisymm inf_le_left (le_inf le_rfl (Subgroup.commutator_le_of_le le_rfl le_rfl))
    rwa [heq] at h
  exact hne' (hcomm_le_Φ.trans hΦle_map)

private theorem k89ch_exists_generator_Z {G : Type} [Group G] [Finite G] {K Z P : Subgroup G}
    (hZK : Z ≤ K) (hZP : Z ≤ P) (hP3 : IsPGroup 3 P)
    (hcenter : (Z.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) =
      Subgroup.center (Bar2 K))
    (hcenter3 : Nat.card (Subgroup.center (Bar2 K)) = 3) :
    ∃ z ∈ Z, Z = Subgroup.zpowers z := by
  have hinst_ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinst_ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ3 : IsPGroup 3 Z := hP3.to_le hZP
  have hZsub3 : IsPGroup 3 (Z.subgroupOf K) := hZ3.comap_subtype
  have hO2 : IsPGroup 2 (CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup
  have hdisj : Disjoint (Z.subgroupOf K) (CFSG.pCore 2 ↥K) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hZsub3 hO2
  let f : ↥(Z.subgroupOf K) →* Bar2 K :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Z.subgroupOf K).subtype
  have hfker : f.ker = ⊥ := by
    ext y
    rw [Subgroup.mem_bot, MonoidHom.mem_ker]
    constructor
    · intro hy
      have h1 : (y : ↥K) ∈ CFSG.pCore 2 ↥K :=
        (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K) (x := (y : ↥K))).mp hy
      have h2 : (y : ↥K) ∈ Z.subgroupOf K ⊓ CFSG.pCore 2 ↥K := ⟨y.2, h1⟩
      rw [hdisj.eq_bot] at h2
      exact Subtype.ext (by simpa using h2)
    · intro hy
      rw [hy]
      simp
  have hfrange : f.range = Subgroup.center (Bar2 K) := by
    rw [show f = (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Z.subgroupOf K).subtype from rfl,
      MonoidHom.range_comp, Subgroup.range_subtype]
    exact hcenter
  have hcenter_ne : Subgroup.center (Bar2 K) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcenter3
    omega
  obtain ⟨c, hcne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter_ne
  let c' : Bar2 K := (c : Bar2 K)
  have hc'mem : c' ∈ Subgroup.center (Bar2 K) := c.2
  have hc'ne : c' ≠ 1 := fun h => hcne (Subtype.ext h)
  have hcfrange : c' ∈ f.range := by rw [hfrange]; exact hc'mem
  obtain ⟨z0, hz0⟩ := hcfrange
  have hfc : f z0 = c' := hz0
  have hz0mem : (z0 : ↥K) ∈ Z.subgroupOf K := z0.2
  have hfkerall : ∀ y : ↥(Z.subgroupOf K), f y = 1 → y = 1 := by
    intro y hy
    have : y ∈ f.ker := hy
    rwa [hfker] at this
  have hc'order : orderOf c' = 3 := by
    have hdvd : orderOf c' ∣ Nat.card (Subgroup.center (Bar2 K)) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center (Bar2 K)) hc'mem
    rw [hcenter3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc'ne
    · exact h
  have hcenter_eq : Subgroup.zpowers c' = Subgroup.center (Bar2 K) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hc'mem) ?_
    rw [Nat.card_zpowers, hc'order, hcenter3]
  have hZsub_eq : Z.subgroupOf K = Subgroup.zpowers (z0 : ↥K) := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.2 hz0mem)
    intro y hy
    have hyc : f ⟨y, hy⟩ ∈ Subgroup.zpowers c' := by
      rw [hcenter_eq, ← hfrange]
      exact MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩
    rw [Subgroup.mem_zpowers_iff] at hyc
    obtain ⟨i, hi⟩ := hyc
    have h1 : f (⟨y, hy⟩ * z0 ^ (-i)) = 1 := by
      rw [map_mul, map_zpow, hfc, ← hi, zpow_neg, mul_inv_cancel]
    have h2 := hfkerall _ h1
    have h3 : (⟨y, hy⟩ : ↥(Z.subgroupOf K)) = z0 ^ i := by
      have := congrArg (fun t => t * z0 ^ i) h2
      simpa [mul_assoc] using this
    have h4 : y = (z0 : ↥K) ^ i := by
      have := congrArg (fun t : ↥(Z.subgroupOf K) => (t : ↥K)) h3
      simpa using this
    rw [h4]
    exact Subgroup.zpow_mem_zpowers (z0 : ↥K) i
  refine ⟨((z0 : ↥K) : G), ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp hz0mem
  · apply le_antisymm
    · intro x hx
      have hxK : x ∈ K := hZK hx
      have hxsub : (⟨x, hxK⟩ : ↥K) ∈ Z.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
      have hmem : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.zpowers (z0 : ↥K) := by
        rw [← hZsub_eq]; exact hxsub
      rw [Subgroup.mem_zpowers_iff] at hmem
      obtain ⟨i, hi⟩ := hmem
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨i, ?_⟩
      have h5 := congrArg (fun t : ↥K => (t : G)) hi
      simpa using h5
    · intro x hx
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← hi]
      have hzZ : ((z0 : ↥K) : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz0mem
      exact zpow_mem hzZ i

private theorem k89ch_pCoreOf_map {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (I : Subgroup ↥X) :
    (CFSG.Open.pCoreOf 2 I).map X.subtype = CFSG.Open.pCoreOf 2 (I.map X.subtype) := by
  let φ : ↥I →* ↥(I.map X.subtype) :=
    { toFun := fun x => ⟨X.subtype (x : ↥X), Subgroup.mem_map_of_mem X.subtype x.2⟩
      map_one' := Subtype.ext (map_one X.subtype)
      map_mul' := fun a b => Subtype.ext (map_mul X.subtype (a : ↥X) (b : ↥X)) }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    simpa [φ] using X.subtype_injective this
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : ↥I ≃* ↥(I.map X.subtype) := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hcoe : (Subgroup.subtype (I.map X.subtype)).comp e.toMonoidHom =
      X.subtype.comp I.subtype := by
    ext x; rfl
  have hpci := CFSG.pCore_map_iso (G := ↥I) (G' := ↥(I.map X.subtype)) 2 e
  rw [CFSG.Open.pCoreOf, CFSG.Open.pCoreOf]
  rw [← hpci]
  rw [Subgroup.map_map, Subgroup.map_map]
  exact congrArg (fun f => (CFSG.pCore 2 ↥I).map f) hcoe

private theorem k89ch_isSolvable_of_map {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {I : Subgroup ↥X} (h : Group.IsSolvable ↥(I.map X.subtype)) : Group.IsSolvable ↥I := by
  let φ : ↥I →* ↥(I.map X.subtype) :=
    { toFun := fun x => ⟨X.subtype (x : ↥X), Subgroup.mem_map_of_mem X.subtype x.2⟩
      map_one' := Subtype.ext (map_one X.subtype)
      map_mul' := fun a b => Subtype.ext (map_mul X.subtype (a : ↥X) (b : ↥X)) }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    simpa [φ] using X.subtype_injective this
  exact Group.isSolvable_of_isSolvable_injective (f := φ) hφinj

private theorem k89ch_pCoreOf_le_pCoreOf {G : Type} [Group G] [Finite G] {I X : Subgroup G}
    (hIX : I ≤ X) (hI_norm : (I.subgroupOf X).Normal) :
    CFSG.Open.pCoreOf 2 I ≤ CFSG.Open.pCoreOf 2 X :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 I).trans hIX)
    (((Subgroup.normal_subgroupOf_iff_le_normalizer hIX).mp hI_norm).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 I))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I)

private theorem k89ch_commutator_le_of_quotient_bot {G : Type} [Group G] [Finite G]
    {X : Subgroup G} {K I : Subgroup ↥X} {N : Subgroup ↥X} [N.Normal]
    (hN : N = CFSG.Open.pCoreOf 2 I)
    (hcomm : ⁅K.map (QuotientGroup.mk' N), I.map (QuotientGroup.mk' N)⁆ = ⊥) :
    ⁅K.map X.subtype, I.map X.subtype⁆ ≤ CFSG.Open.pCoreOf 2 (I.map X.subtype) := by
  have h1 : (⁅K, I⁆).map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.map_commutator, hcomm]
  have h2 : ⁅K, I⁆ ≤ N := by
    rw [← QuotientGroup.ker_mk' N]
    exact (Subgroup.map_eq_bot_iff ⁅K, I⁆).mp h1
  have h3 := Subgroup.map_mono (f := X.subtype) h2
  rw [hN, k89ch_pCoreOf_map I] at h3
  rwa [Subgroup.map_commutator] at h3

private theorem k89ch_pRank_pCoreOf_quotient_le {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] {I : Subgroup X} {q : ℕ} (hq : q.Prime)
    (hker : ¬ q ∣ Nat.card ↥(MonoidHom.ker (QuotientGroup.mk' N)))
    (hrank : CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 2) :
    CFSG.Open.pRank q (CFSG.Open.pCoreOf q (I.map (QuotientGroup.mk' N))) ≤ 2 := by
  have h1 : CFSG.Open.pRank q (CFSG.Open.pCoreOf q (I.map (QuotientGroup.mk' N))) ≤
      CFSG.Open.pRank q (⊤ : Subgroup (X ⧸ N)) :=
    (CFSG.SectionRank.pRank_mono hq.one_lt
      (CFSG.LieType.BorelTits.pCoreOf_le q (I.map (QuotientGroup.mk' N)))).trans
      (CFSG.SectionRank.pRank_mono hq.one_lt le_top)
  have hmap : (⊤ : Subgroup X).map (QuotientGroup.mk' N) = (⊤ : Subgroup (X ⧸ N)) := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
  have h2 : CFSG.Open.pRank q (⊤ : Subgroup (X ⧸ N)) =
      CFSG.Open.pRank q (⊤ : Subgroup X) := by
    rw [← hmap]
    exact CFSG.pRank_map_eq_of_not_dvd_card_ker (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) hq hker (⊤ : Subgroup X)
  omega

private theorem k89ch_coprime_orderOf_card {G : Type} [Group G] [Finite G] {z : G}
    {I1 : Subgroup G} (hz3 : IsPGroup 3 (Subgroup.zpowers z)) (hI1 : IsPGroup 2 I1) :
    Nat.Coprime (orderOf z) (Nat.card I1) := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hz3
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hI1
  rw [Nat.card_zpowers] at ha
  rw [ha, hb]
  exact ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num)).pow a b

private theorem k89ch_mem_normalizer_zpowers {K : Type} [Group K] {g y : K}
    (hg : g * y = y * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup K) : Set K) := by
  have hc : Commute g y := hg
  have hfix : ∀ s ∈ Subgroup.zpowers y, g * s * g⁻¹ = s := by
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    exact (hc.zpow_right k).mul_inv_cancel
  have hfix' : ∀ s ∈ Subgroup.zpowers y, g⁻¹ * s * g = s := by
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    exact (hc.zpow_right k).inv_mul_cancel
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hfix h hh]; exact hh
  · intro hh
    have h2 : h = g * h * g⁻¹ := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = g * h * g⁻¹ := hfix' _ hh
    rw [h2]; exact hh

private theorem k89ch_le_sup_centralizer {G : Type} [Group G] [Finite G]
    {I I1 : Subgroup G} {z : G} (hI1_le : I1 ≤ I)
    (hzN : ∀ n ∈ I1, z * n * z⁻¹ ∈ I1)
    (hcop : Nat.Coprime (orderOf z) (Nat.card I1))
    (hcomm : ∀ g ∈ I, g⁻¹ * (z * g * z⁻¹) ∈ I1) :
    I ≤ I1 ⊔ (I ⊓ Subgroup.centralizer ({z} : Set G)) := by
  intro g hg
  obtain ⟨n, hn, hfix⟩ :=
    CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime I1 hzN (hcomm g hg) hcop
  have hgnI : g * n ∈ I := I.mul_mem hg (hI1_le hn)
  have hgnC : g * n ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc z * (g * n) = z * (g * n) * z⁻¹ * z := by group
      _ = (g * n) * z := by rw [hfix]
  have hg_eq : g = (g * n) * n⁻¹ := by group
  rw [hg_eq, sup_comm]
  exact Subgroup.mul_mem_sup ⟨hgnI, hgnC⟩ (I1.inv_mem hn)

private theorem k89ch_twoLocal_ne_top {G : Type} [Group G] [Finite G] (D : Data G)
    {X : Subgroup G} (hX : IsTwoLocal X) : X ≠ ⊤ := by
  have hinst_ : IsSimpleGroup G := D.standing.simple
  exact CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top D.standing.nonab X hX

private theorem k89ch_not_le_M {G : Type} [Group G] [Finite G] (D : Data G)
    {X : Subgroup G} (hX : rankThreeIsMaxTwoLocal X) (hXM : X ≠ D.M) : ¬ X ≤ D.M := by
  intro hle
  exact hXM (hX.2 D.M D.maxLocal.1 hle).symm

private theorem k89ch_descent {G : Type} [Group G] [Finite G] (D : Data G)
    (hFacts : AllFacts889 D) (hOdd : S889OddCore D) (hrank : Rank889 D)
    (hQMin : S889QMin) (hQRank : S889QRank) (hDick : S889Dickson)
    {L P : Subgroup G} {ω : G} (hSet : Set889 D L P ω) {X : Subgroup G}
    (hX2 : IsTwoLocal X) (hKX : K889 L ω ≤ X) (hXM' : ¬ X ≤ D.M) :
    ⁅K889 L ω, PPrimeCoreIn 3 X⁆ ≤ CFSG.Open.pCoreOf 2 (PPrimeCoreIn 3 X) := by
  have hinst_ : IsSimpleGroup G := D.standing.simple
  have hFacts' := hFacts L P ω hSet
  obtain ⟨h5, hIsolv⟩ := hOdd L P ω hSet X (k89ch_twoLocal_ne_top D hX2) hKX hXM'
  let I0 : Subgroup ↥X := CFSG.pPrimeCore 3 ↥X
  have hI0_normal : I0.Normal := CFSG.pPrimeCore_normal
  have hI0_solv : Group.IsSolvable ↥I0 :=
    k89ch_isSolvable_of_map (I := I0) (by
      change Group.IsSolvable ↥(PPrimeCoreIn 3 X)
      exact hIsolv)
  let N : Subgroup ↥X := CFSG.Open.pCoreOf 2 I0
  have hN_normal : N.Normal := k89ch_pCoreOf_normal 2 hI0_normal
  let π : ↥X →* ↥X ⧸ N := QuotientGroup.mk' N
  let Ibar : Subgroup (↥X ⧸ N) := I0.map π
  have hIbar_normal : Ibar.Normal := hI0_normal.map π (QuotientGroup.mk'_surjective N)
  let K' : Subgroup ↥X := (K889 L ω).subgroupOf X
  let Kbar : Subgroup (↥X ⧸ N) := K'.map π
  have hsurjπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hIbar_solv : Group.IsSolvable ↥Ibar := by
    have := hI0_solv
    let f : ↥I0 →* ↥Ibar :=
      (π.comp I0.subtype).codRestrict Ibar (fun x => Subgroup.mem_map_of_mem π x.2)
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact Group.isSolvable_of_surjective (f := f) hf
  have hK'map : K'.map X.subtype = K889 L ω := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact le_antisymm inf_le_left (le_inf le_rfl hKX)
  have hKbar_perf : ⁅Kbar, Kbar⁆ = Kbar := by
    have hK'perf : ⁅K', K'⁆ = K' := by
      apply Subgroup.map_injective X.subtype_injective
      rw [Subgroup.map_commutator]
      rw [hK'map, hFacts'.perfect]
    have h2 : ⁅Kbar, Kbar⁆ = ⁅K', K'⁆.map π := by
      rw [Subgroup.map_commutator]
    rw [h2, hK'perf]
  have hKbar_le_norm : Kbar ≤ Subgroup.normalizer (Ibar : Set (↥X ⧸ N)) := by
    have htop : Subgroup.normalizer (Ibar : Set (↥X ⧸ N)) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hIbar_normal
    rw [htop]
    exact le_top
  have hq_bot : ∀ q : ℕ, q.Prime → ⁅Kbar, CFSG.Open.pCoreOf q Ibar⁆ = ⊥ := by
    intro q hq
    have hinst_ : Fact q.Prime := ⟨hq⟩
    rcases eq_or_ne q 2 with rfl | hq2
    · have hbot : CFSG.Open.pCoreOf 2 Ibar = ⊥ :=
        k89ch_pCore_quotient_map_bot (X := ↥X) 2 hI0_normal (N := N) rfl
      rw [hbot, commutator_bot_right]
    rcases eq_or_ne q 3 with rfl | hq3
    · have h3I0 : ¬ 3 ∣ Nat.card ↥I0 :=
        (Nat.prime_three.coprime_iff_not_dvd).mp (by
          simpa [I0] using CFSG.pPrimeCore_coprime_card (G := ↥X) (p := 3))
      have hnot : ¬ 3 ∣ Nat.card ↥Ibar := fun h =>
        h3I0 (h.trans (by simpa [Ibar] using Subgroup.card_map_dvd I0 π))
      have hbot : CFSG.Open.pCoreOf 3 Ibar = ⊥ :=
        k89ch_pCoreOf_eq_bot_of_not_dvd Nat.prime_three hnot
      rw [hbot, commutator_bot_right]
    rcases eq_or_ne q 5 with rfl | hq5
    · have hcard : Nat.card ↥I0 = Nat.card ↥(PPrimeCoreIn 3 X) := by
        rw [show PPrimeCoreIn 3 X = I0.map X.subtype from rfl]
        exact (Subgroup.card_map_of_injective X.subtype_injective).symm
      have h5I0 : ¬ 5 ∣ Nat.card ↥I0 := fun h => h5 (hcard ▸ h)
      have hnot : ¬ 5 ∣ Nat.card ↥Ibar := fun h =>
        h5I0 (h.trans (by simpa [Ibar] using Subgroup.card_map_dvd I0 π))
      have hbot : CFSG.Open.pCoreOf 5 Ibar = ⊥ :=
        k89ch_pCoreOf_eq_bot_of_not_dvd Nat.prime_five hnot
      rw [hbot, commutator_bot_right]
    · have hq7 : 7 ≤ q := by
        by_contra h
        have hlt : q < 7 := by omega
        interval_cases q
        · norm_num at hq
        · norm_num at hq
        · omega
        · omega
        · norm_num at hq
        · omega
        · norm_num at hq
      have hrankX : CFSG.Open.pRank q (⊤ : Subgroup ↥X) ≤ 2 := by
        have h := (hrank L P hSet.set880 X hX2).2 q hq hq7
        rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup X] at h
      have hker : ¬ q ∣ Nat.card ↥(MonoidHom.ker (QuotientGroup.mk' N)) := by
        rw [QuotientGroup.ker_mk']
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I0)
        rw [hk]
        intro hdiv
        have h2 : q ∣ 2 := hq.dvd_of_dvd_pow hdiv
        have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) h2
        omega
      have hD0rank : CFSG.Open.pRank q (CFSG.Open.pCoreOf q Ibar) ≤ 2 :=
        k89ch_pRank_pCoreOf_quotient_le (X := ↥X) (N := N) (I := I0) hq hker hrankX
      have hAq : ¬ q ∣ Nat.card ↥Kbar := by
        have hK'dvd : Nat.card ↥Kbar ∣ Nat.card ↥K' := by
          simpa [Kbar] using Subgroup.card_map_dvd K' π
        have hK'card : Nat.card ↥K' = Nat.card (K889 L ω) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
        intro h
        have h1 : q ∣ Nat.card (K889 L ω) := by
          rw [← hK'card]
          exact h.trans hK'dvd
        exact k89ch_not_dvd_card_of_isA6Z3 hFacts'.alt6 hq hq7 h1
      by_contra hne
      have hne' : ⁅CFSG.Open.pCoreOf q Ibar, Kbar⁆ ≠ ⊥ := by
        rwa [Subgroup.commutator_comm]
      let base : ↥K' →* ↥Kbar :=
        (π.comp K'.subtype).codRestrict Kbar (fun x => Subgroup.mem_map_of_mem π x.2)
      have hbase : Function.Surjective base := by
        intro y
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
      let surj : ↥(K889 L ω) →* ↥Kbar :=
        base.comp (Subgroup.subgroupOfEquivOfLe hKX).symm.toMonoidHom
      have hsurj : Function.Surjective surj :=
        hbase.comp (Subgroup.subgroupOfEquivOfLe hKX).symm.surjective
      have hnorm : Kbar ≤ Subgroup.normalizer (CFSG.Open.pCoreOf q Ibar : Set (↥X ⧸ N)) :=
        hKbar_le_norm.trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf q Ibar)
      exact k89ch_q_component q hq hq7 hnorm
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup q Ibar) hne' hD0rank hAq
        (k89ch_perfect hFacts'.perfect) hFacts'.alt6 surj hsurj
        hQMin hQRank hDick
  have hcomm : ⁅Kbar, Ibar⁆ = ⊥ :=
    CFSG.GroupTheory.commutator_eq_bot_of_forall_pCoreOf hIbar_solv hKbar_perf hKbar_le_norm hq_bot
  have hfin : ⁅K'.map X.subtype, I0.map X.subtype⁆ ≤
      CFSG.Open.pCoreOf 2 (I0.map X.subtype) :=
    k89ch_commutator_le_of_quotient_bot (K := K') (I := I0) (N := N) rfl hcomm
  rwa [hK'map] at hfin

theorem s889_chief_of_parts {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (h885 : R885 D) (h887 : R887 D) (hrank : Rank889 D) (hFacts : AllFacts889 D)
    (hSplit : S889Split D) (hOdd : S889OddCore D) (hQMin : S889QMin) (hQRank : S889QRank)
    (hDick : S889Dickson) : S889Chief D := by
  intro L P ω hSet X hX hXM
  have _hSg := hSg
  have _h885 := h885
  have hinst_ : IsSimpleGroup G := D.standing.simple
  have hX2 : IsTwoLocal X := hX.1.1
  have hXtop : X ≠ ⊤ := k89ch_twoLocal_ne_top D hX2
  have hXM' : ¬ X ≤ D.M := k89ch_not_le_M D hX.1 hXM
  obtain ⟨h5, hIsolv⟩ := hOdd L P ω hSet X hXtop hX.2 hXM'
  have hSplit' := hSplit L P ω hSet X hXtop hX.2 hXM'
  have hFacts' := hFacts L P ω hSet
  have hdesc := k89ch_descent D hFacts hOdd hrank hQMin hQRank hDick hSet hX2 hX.2 hXM'
  have hIX : PPrimeCoreIn 3 X ≤ X := Subgroup.map_subtype_le _
  have hI_norm : ((PPrimeCoreIn 3 X).subgroupOf X).Normal := by
    have h : (PPrimeCoreIn 3 X).subgroupOf X = CFSG.pPrimeCore 3 ↥X := by
      change ((CFSG.pPrimeCore 3 ↥X).map X.subtype).subgroupOf X = CFSG.pPrimeCore 3 ↥X
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    rw [h]
    exact CFSG.pPrimeCore_normal
  have hZK : ZOf (P ⊓ L) ≤ K889 L ω :=
    (show ZOf (P ⊓ L) ≤ P ⊓ L from inf_le_left).trans hFacts'.qLe
  have hZP : ZOf (P ⊓ L) ≤ P :=
    (show ZOf (P ⊓ L) ≤ P ⊓ L from inf_le_left).trans inf_le_left
  obtain ⟨z, hzZ, hzZeq⟩ :=
    k89ch_exists_generator_Z (K := K889 L ω) (Z := ZOf (P ⊓ L)) (P := P)
      hZK hZP hSet.sylow3.isPGroup hFacts'.centerEq hFacts'.alt6.2.1
  have hzK : z ∈ K889 L ω := hZK hzZ
  have hzX : z ∈ X := hX.2 hzK
  have hcomm : ∀ g ∈ PPrimeCoreIn 3 X,
      g⁻¹ * (z * g * z⁻¹) ∈ CFSG.Open.pCoreOf 2 (PPrimeCoreIn 3 X) := by
    intro g hg
    have hmem : ⁅g⁻¹, z⁆ ∈ ⁅K889 L ω, PPrimeCoreIn 3 X⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator ((PPrimeCoreIn 3 X).inv_mem hg) hzK
    have h1 := hdesc hmem
    simpa [commutatorElement_def, mul_assoc] using h1
  have hX_norm_I : X ≤ Subgroup.normalizer (PPrimeCoreIn 3 X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIX).mp hI_norm
  have hX_norm_I1 : X ≤ Subgroup.normalizer
      (CFSG.Open.pCoreOf 2 (PPrimeCoreIn 3 X) : Set G) :=
    hX_norm_I.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (PPrimeCoreIn 3 X))
  have hzN : ∀ n ∈ CFSG.Open.pCoreOf 2 (PPrimeCoreIn 3 X),
      z * n * z⁻¹ ∈ CFSG.Open.pCoreOf 2 (PPrimeCoreIn 3 X) :=
    fun n hn => (Subgroup.mem_normalizer_iff.mp (hX_norm_I1 hzX) n).mp hn
  have hz3 : IsPGroup 3 (Subgroup.zpowers z) := by
    rw [← hzZeq]
    exact hSet.sylow3.isPGroup.to_le hZP
  have hI1_2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (PPrimeCoreIn 3 X)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (PPrimeCoreIn 3 X)
  have hcop : Nat.Coprime (orderOf z)
      (Nat.card ↥(CFSG.Open.pCoreOf 2 (PPrimeCoreIn 3 X))) :=
    k89ch_coprime_orderOf_card hz3 hI1_2
  have hI_le : PPrimeCoreIn 3 X ≤
      CFSG.Open.pCoreOf 2 (PPrimeCoreIn 3 X) ⊔
        (PPrimeCoreIn 3 X ⊓ Subgroup.centralizer ({z} : Set G)) :=
    k89ch_le_sup_centralizer
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (PPrimeCoreIn 3 X)) hzN hcop hcomm
  have hCI_le_M : PPrimeCoreIn 3 X ⊓ Subgroup.centralizer ({z} : Set G) ≤ D.M := by
    intro x hx
    obtain ⟨hxI, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxz : x * z = z * x := ((Subgroup.mem_centralizer_iff.mp hxC) z rfl).symm
    have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
      k89ch_mem_normalizer_zpowers hxz
    have hxZ : x ∈ Subgroup.normalizer (ZOf (P ⊓ L) : Set G) := by
      rw [← hzZeq] at hxN
      exact hxN
    exact h887 L P hSet.set880 hxZ
  have hI_le_final : PPrimeCoreIn 3 X ≤ CFSG.Open.pCoreOf 2 X ⊔ (X ⊓ D.M) := by
    refine hI_le.trans (sup_le ?_ ?_)
    · exact (k89ch_pCoreOf_le_pCoreOf hIX hI_norm).trans le_sup_left
    · exact (le_inf (inf_le_left.trans hIX) hCI_le_M).trans le_sup_right
  exact hSplit'.trans (sup_le hI_le_final le_sup_right)


end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
