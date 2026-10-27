module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.UC1K31
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.GL83PartI.I713.Extension
import CFSG.RankThree.PartOne.S12.Sec15Frattini
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76 StronglyEmbeddedFive)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL_mk_coe)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p218s_exists_sylow_le_normalizer {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {W A : Subgroup G}
    (hA : IsPGroup p A) (hAW : A ≤ normalizer (W : Set G)) (hcard : ¬ p ∣ Nat.card (Sylow q W)) :
    ∃ S : Sylow q W, A ≤ normalizer (((S : Subgroup W).map W.subtype : Subgroup G) : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  letI : MulDistribMulAction ↥A ↥W := Subgroup.conjMulDistribMulActionOfLeNormalizer A W hAW
  letI : MulAction ↥A (Sylow q W) := Sylow.pointwiseMulAction
  obtain ⟨S, hS⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q W) hcard
  refine ⟨S, fun a ha => ?_⟩
  have hfix : (⟨a, ha⟩ : ↥A) • (S : Subgroup ↥W) = S := by
    rw [← Sylow.pointwise_smul_def]
    exact congrArg Sylow.toSubgroup (hS ⟨a, ha⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : (⟨a, ha⟩ : ↥A) • s ∈ (S : Subgroup ↥W) :=
      hfix ▸ Subgroup.smul_mem_pointwise_smul s (⟨a, ha⟩ : ↥A) (S : Subgroup ↥W) hs
    exact ⟨(⟨a, ha⟩ : ↥A) • s, hs', rfl⟩
  · rintro ⟨s', hs', hs'x⟩
    rw [← hfix] at hs'
    obtain ⟨s, hs, rfl⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists s' (⟨a, ha⟩ : ↥A) (S : Subgroup ↥W)).1 hs'
    refine ⟨s, hs, ?_⟩
    have h1 : a * (s : G) * a⁻¹ = a * x * a⁻¹ := hs'x
    simpa using h1

theorem uc22p218s_conj_eq_self_of_pow {r : ℕ} [Fact r.Prime] {E : Subgroup G} (hE : ∀ e ∈ E, e ^ r = 1) {x : G}
    {k : ℕ} (hxE : ∀ e ∈ E, x * e * x⁻¹ = e ^ k) {a : ℕ} (hx : x ^ r ^ a = 1) : ∀ e ∈ E, x * e * x⁻¹ = e := by
  intro e he
  have hj : ∀ j : ℕ, x ^ j * e * (x ^ j)⁻¹ = e ^ k ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc x ^ (j + 1) * e * (x ^ (j + 1))⁻¹ = x * (x ^ j * e * (x ^ j)⁻¹) * x⁻¹ := by
            rw [pow_succ' x j]
            group
        _ = (x * e * x⁻¹) ^ k ^ j := by rw [ih, conj_pow]
        _ = e ^ k ^ (j + 1) := by rw [hxE e he, ← pow_mul, pow_succ' k j]
  have h1 := hj (r ^ a)
  rw [hx, one_mul, inv_one, mul_one] at h1
  have hmod : k ^ r ^ a ≡ k [MOD r] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).1 (by rw [Nat.cast_pow, ZMod.pow_card_pow])
  have h2 : e ^ k ^ r ^ a = e ^ k :=
    pow_eq_pow_iff_modEq.2 (hmod.of_dvd (orderOf_dvd_of_pow_eq_one (hE e he)))
  exact (hxE e he).trans (h2.symm.trans h1.symm)

theorem uc22p218s_exists_mem_centralizer {p r : ℕ} (hp : p.Prime) (hr : r.Prime) {Q E : Subgroup G}
    (hQ : IsElemAbelian p Q) (hQc : Nat.card Q = p ^ 2) (hE : IsElemAbelian r E) (hE1 : E ≠ ⊥)
    (hpow : ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k) :
    ∃ x ∈ Q, x ≠ 1 ∧ x ∈ centralizer (E : Set G) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨e₀, he₀E, he₀1⟩ := (bot_or_exists_ne_one E).resolve_left hE1
  have he₀o : orderOf e₀ = r := orderOf_eq_prime (hE.2 e₀ he₀E) he₀1
  haveI : Fact (Nat.card ↥(zpowers e₀)).Prime := ⟨by rw [Nat.card_zpowers, he₀o]; exact hr⟩
  have hQN : Q ≤ normalizer ((zpowers e₀ : Subgroup G) : Set G) := by
    rw [le_normalizer_iff]
    intro x hx g hg
    obtain ⟨k, hk⟩ := hpow x hx
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
    rw [← conj_zpow, hk e₀ he₀E]
    exact zpow_mem (pow_mem (mem_zpowers e₀) k) m
  let φ : ↥Q →* MulAut ↥(zpowers e₀) := (normalizerMonoidHom (zpowers e₀)).comp (inclusion hQN)
  let ψ : ↥Q →* ZMod (Nat.card ↥(zpowers e₀)) :=
    (Units.coeHom _).comp ((IsCyclic.mulAutMulEquiv ↥(zpowers e₀)).toMonoidHom.comp φ)
  by_contra hcon
  have hψ : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).2 fun x hx => ?_
    have h0 : ((IsCyclic.mulAutMulEquiv ↥(zpowers e₀) (φ x) : (ZMod (Nat.card ↥(zpowers e₀)))ˣ) :
        ZMod (Nat.card ↥(zpowers e₀))) = 1 := hx
    have h1 : φ x = 1 := (MulEquiv.map_eq_one_iff _).1 (Units.val_eq_one.1 h0)
    have h2 : ((normalizerMonoidHom (zpowers e₀) (inclusion hQN x) ⟨e₀, mem_zpowers e₀⟩ : ↥(zpowers e₀)) : G) =
        e₀ := by
      rw [show normalizerMonoidHom (zpowers e₀) (inclusion hQN x) = φ x from rfl, h1]
      rfl
    rw [rhoL_mk_coe] at h2
    obtain ⟨k, hk⟩ := hpow x x.2
    have h4 : e₀ ^ k = e₀ ^ 1 := by
      rw [← hk e₀ he₀E, pow_one]
      exact h2
    have hk1 : k ≡ 1 [MOD r] := by
      have h5 := pow_eq_pow_iff_modEq.1 h4
      rwa [he₀o] at h5
    have hxC : (x : G) ∈ centralizer (E : Set G) := by
      rw [mem_centralizer_iff]
      intro e he
      have h5 : e ^ k = e ^ 1 :=
        pow_eq_pow_iff_modEq.2 (hk1.of_dvd (orderOf_dvd_of_pow_eq_one (hE.2 e he)))
      have h6 := hk e he
      rw [h5, pow_one] at h6
      calc e * (x : G) = (x : G) * e * (x : G)⁻¹ * x := by rw [h6]
        _ = x * e := by group
    by_contra hx1
    exact hcon ⟨x, x.2, fun h => hx1 (Subtype.ext h), hxC⟩
  haveI := isCyclic_of_injective_ringHom ψ hψ
  have hexp : Monoid.exponent ↥Q ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hQ.2 x x.2)
  rw [IsCyclic.exponent_eq_card, hQc] at hexp
  have h7 : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  exact absurd (Nat.le_of_dvd hp.pos hexp) (not_le.2 h7)

theorem uc22p218s_pRank_top_le_add {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (N C : Subgroup K)
    [N.Normal] (hNC : ∀ k : K, ∃ c ∈ C, c * k⁻¹ ∈ N) (hcop : ∀ c ∈ C, c ∈ N → c ^ p = 1 → c = 1) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p N + CFSG.Open.pRank p C := by
  haveI : Fact p.Prime := ⟨hp⟩
  let π : ↥C →* K ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨c, hc, hck⟩ := hNC k
    refine ⟨⟨c, hc⟩, ?_⟩
    have h1 : QuotientGroup.mk' N (c * k⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hck
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hker : ¬ p ∣ Nat.card π.ker := by
    intro hdvd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have h1 : ((y : ↥C) : K) ∈ N := by
      have h2 : QuotientGroup.mk' N ((y : ↥C) : K) = 1 := y.2
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h2
    have h3 : ((y : ↥C) : K) ^ p = 1 := by
      have h4 := pow_orderOf_eq_one y
      rw [hy] at h4
      simpa using congrArg (fun z : ↥π.ker => ((z : ↥C) : K)) h4
    have h5 : y = 1 := Subtype.ext (Subtype.ext (hcop _ (y : ↥C).2 h1 h3))
    rw [h5, orderOf_one] at hy
    exact hp.one_lt.ne hy
  have h1 := GL83.I713.pRank_top_le_add_pRank_quotient hp N
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (QuotientGroup.quotientKerEquivOfSurjective π hπ),
    CFSG.SectionRank.pRank_quotient_eq π.ker hker, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup C] at h1
  exact h1

theorem uc22p218s_two_le_pRank_inf_normalizer {p q : ℕ} (hp : p.Prime) [Fact q.Prime] {L M S : Subgroup G}
    (hLM : L ≤ M) [(L.subgroupOf M).Normal] (hS : IsSylowOf q S L)
    (hcop : ∀ h ∈ L, h ∈ normalizer (S : Set G) → h ^ p = 1 → h = 1)
    (hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p M) : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (S : Set G)) := by
  have hML : M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  have h1 := uc22p218s_pRank_top_le_add hp (L.subgroupOf M) ((M ⊓ normalizer (S : Set G)).subgroupOf M)
    (fun m => by
      obtain ⟨l, hlL, hl⟩ :=
        CFSG.RankThree.PartOne.Sec15Frattini.exists_mem_normalizer_of_isSylowOf hS (hML m.2)
      refine ⟨⟨l, hLM hlL⟩⁻¹ * m, mem_subgroupOf.2 ⟨M.mul_mem (M.inv_mem (hLM hlL)) m.2, hl⟩, ?_⟩
      rw [mul_inv_cancel_right, mem_subgroupOf]
      exact L.inv_mem hlL)
    (fun c hcC hcN hcp => Subtype.ext (hcop _ (mem_subgroupOf.1 hcN) (mem_inf.1 (mem_subgroupOf.1 hcC)).2
      (by simpa using congrArg Subtype.val hcp)))
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup M, UCK.K31.pRank_subgroupOf_eq hp.one_lt hLM,
    UCK.K31.pRank_subgroupOf_eq hp.one_lt (inf_le_left : M ⊓ normalizer (S : Set G) ≤ M)] at h1
  omega

theorem uc22p218s_exists_pow_torus {L M : Subgroup G} {n p r : ℕ} (hLM : L ≤ M) [(L.subgroupOf M).Normal]
    (hX : IsSp4 (Bar2 L) n) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ 2 ^ n - 1) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : r ∣ 2 ^ n - 1) (hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p M) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ M ∧ IsElemAbelian p Q ∧
      Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hML : M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  have hpr : p ≠ r := by
    rintro rfl
    exact hpn hrn
  obtain ⟨E₀, hE₀L, hE₀el, hE₀c⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hr (uc22p218c_pRank_eq_two_of_bar2 hX hr hrn).ge
  obtain ⟨S', hS'⟩ := uc22p218s_exists_sylow_le_normalizer hr Nat.prime_two hE₀el.isPGroup
    (hE₀L.trans le_normalizer) (uc22p218d_not_dvd_card_sylow_of_bar2 hX hr hrn)
  obtain ⟨S, hS, hE₀S⟩ : ∃ S : Subgroup G, IsSylowOf 2 S L ∧ E₀ ≤ normalizer (S : Set G) := ⟨_, ⟨S', rfl⟩, hS'⟩
  obtain ⟨Q, hQ, hQel, hQc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp
    (uc22p218s_two_le_pRank_inf_normalizer hp hLM hS
      (fun h hhL hhS hhp => uc22p218d_eq_one_of_pow_eq_one hS hX hp hp2 hpn hhL hhS hhp) hrank)
  have hQM : Q ≤ M := hQ.trans inf_le_left
  have hQS : Q ≤ normalizer (S : Set G) := hQ.trans inf_le_right
  have hpow : ∀ x ∈ Q, ∃ k : ℕ, ∀ h ∈ L, h ∈ normalizer (S : Set G) → x * h * x⁻¹ * (h ^ k)⁻¹ ∈ S :=
    fun x hx => uc22p218d_exists_pow_conj_mem_sp4 hS hX (hML (hQM hx)) (hQS hx) (hp.odd_of_ne_two hp2)
      (hQel.2 x hx)
  have hWL : S ⊔ E₀ ≤ L := sup_le hS.le hE₀L
  have hWN : S ⊔ E₀ ≤ normalizer (S : Set G) := sup_le le_normalizer hE₀S
  have hQW : Q ≤ normalizer ((S ⊔ E₀ : Subgroup G) : Set G) := by
    have hW : S ⊔ E₀ = closure ((S : Set G) ∪ E₀) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    rw [hW, le_normalizer_closure_iff]
    intro x hx g hg
    rw [← hW]
    rcases hg with hg | hg
    · exact mem_sup_left ((mem_normalizer_iff.1 (hQS hx) g).1 hg)
    · obtain ⟨k, hk⟩ := hpow x hx
      have h1 := hk g (hE₀L hg) (hE₀S hg)
      have h2 : x * g * x⁻¹ = (x * g * x⁻¹ * (g ^ k)⁻¹) * g ^ k := by group
      rw [h2]
      exact mul_mem (mem_sup_left h1) (mem_sup_right (pow_mem hg k))
  obtain ⟨a, ha⟩ := hS.isPGroup.exists_card_eq
  have hWc : Nat.card (S ⊔ E₀ : Subgroup G) = 2 ^ a * r ^ 2 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer S E₀ hE₀S
      (IsPGroup.disjoint_of_ne 2 r hr2.symm S E₀ hS.isPGroup hE₀el.isPGroup), ha, hE₀c]
  have hpW : ¬ p ∣ Nat.card (S ⊔ E₀ : Subgroup G) := by
    rw [hWc]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨P, hP⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hp hr hQel.isPGroup hQW hpW
  obtain ⟨E, hE, hQE⟩ : ∃ E : Subgroup G, IsSylowOf r E (S ⊔ E₀) ∧ Q ≤ normalizer (E : Set G) :=
    ⟨_, ⟨P, rfl⟩, hP⟩
  have hE₀ : IsSylowOf r E₀ (S ⊔ E₀) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_right, hE₀el.isPGroup, fun h => ?_⟩
    have h1 := relIndex_mul_card E₀ (S ⊔ E₀)
    rw [inf_eq_left.2 (le_sup_right : E₀ ≤ S ⊔ E₀), hWc, hE₀c] at h1
    have h2 : E₀.relIndex (S ⊔ E₀) = 2 ^ a := Nat.eq_of_mul_eq_mul_right (pow_pos hr.pos 2) h1
    rw [h2] at h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  obtain ⟨w, -, hw⟩ := hE₀.exists_mem_conj hE
  have hEeq : E = E₀.map (MulAut.conj w).toMonoidHom := by
    ext x
    rw [mem_map_equiv, MulAut.conj_symm_apply]
    exact hw x
  have hEel : IsElemAbelian r E := by
    rw [hEeq]
    exact hE₀el.map _
  have hEc : Nat.card E = r ^ 2 := by
    rw [hEeq, card_map_of_injective (f := (MulAut.conj w).toMonoidHom) (MulAut.conj w).injective, hE₀c]
  have hEW : E ≤ S ⊔ E₀ := hE.le
  have hdisj : Disjoint E S := IsPGroup.disjoint_of_ne r 2 hr2 E S hE.isPGroup hS.isPGroup
  refine ⟨E, Q, hEW.trans hWL, hEel, hEc, hQM, hQel, hQc, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hpow x hx
  refine ⟨k, fun e he => ?_⟩
  have h1 := hk e (hWL (hEW he)) (hWN (hEW he))
  have h2 : x * e * x⁻¹ * (e ^ k)⁻¹ ∈ E :=
    mul_mem ((mem_normalizer_iff.1 (hQE hx) e).1 he) (inv_mem (pow_mem he k))
  exact mul_inv_eq_one.1 (disjoint_def.1 hdisj h2 h1)

theorem uc22p218s_le_centralizer {L M R E : Subgroup G} {n r : ℕ} (hX : IsSp4 (Bar2 L) n) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1) (hML : M ≤ normalizer (L : Set G)) (hR : IsSylowOf r R M) (hER : E ≤ R)
    (hEL : E ≤ L) (hEr : ∀ e ∈ E, e ^ r = 1) : E ≤ centralizer (R : Set G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRp : IsPGroup r R := hR.isPGroup
  obtain ⟨S', hS'⟩ := uc22p218s_exists_sylow_le_normalizer hr Nat.prime_two hRp (hR.le.trans hML)
    (uc22p218d_not_dvd_card_sylow_of_bar2 hX hr hrn)
  obtain ⟨S, hS, hRS⟩ : ∃ S : Subgroup G, IsSylowOf 2 S L ∧ R ≤ normalizer (S : Set G) := ⟨_, ⟨S', rfl⟩, hS'⟩
  have hdisj : Disjoint R S := IsPGroup.disjoint_of_ne r 2 hr2 R S hRp hS.isPGroup
  intro e he
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨a, ha⟩ := hRp ⟨x, hx⟩
  have hxa : x ^ r ^ a = 1 := congrArg Subtype.val ha
  obtain ⟨k, hk⟩ := uc22p218d_exists_pow_conj_mem_sp4 hS hX (hML (hR.le hx)) (hRS hx)
    (hr.odd_of_ne_two hr2).pow hxa
  have hxE : ∀ f ∈ E, x * f * x⁻¹ = f ^ k := by
    intro f hf
    have h1 := hk f (hEL hf) (hRS (hER hf))
    have h2 : x * f * x⁻¹ * (f ^ k)⁻¹ ∈ R :=
      mul_mem (mul_mem (mul_mem hx (hER hf)) (inv_mem hx)) (inv_mem (pow_mem (hER hf) k))
    exact mul_inv_eq_one.1 (disjoint_def.1 hdisj h2 h1)
  have h3 := uc22p218s_conj_eq_self_of_pow hEr hxE hxa e he
  calc x * e = x * e * x⁻¹ * x := by group
    _ = e * x := by rw [h3]

theorem uc22p218s_isSp4_barInf {M L : Subgroup G} {n : ℕ} (hL : L ∈ calC M) (hX : IsSp4 (Bar2 L) n) :
    IsSp4 (BarInf L) n := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 (uc22p218d_center_eq_bot_sp4 hX)
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hX

theorem uc22p218s_false_of_le_normalizer (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch) (hH : H1930 D)
    (c : Ctx21 D Ch) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {y : G} (hy : orderOf y = r)
    (hyU : zpowers y ∈ uniqueSet D.M) (hyT : zpowers y ≤ normalizer (D.T : Set G)) : False := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  obtain ⟨a, ha⟩ := hT2.exists_card_eq
  have hyc : Nat.card (zpowers y) = r := by rw [Nat.card_zpowers, hy]
  have hyp : IsPGroup r (zpowers y) := IsPGroup.of_card (n := 1) (by rw [hyc, pow_one])
  have hcard : Nat.card ↥(zpowers y ⊔ D.T) = 2 ^ a * r := by
    rw [sup_comm, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer D.T (zpowers y) hyT
      (IsPGroup.disjoint_of_ne 2 r hr2.symm _ _ hT2 hyp), ha, hyc]
  have hsol : IsSolvable ↥(zpowers y ⊔ D.T) := by
    haveI := Fintype.ofFinite ↥(zpowers y ⊔ D.T)
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := a) (b := 1)
      Nat.prime_two hr (Ne.symm hr2) (by rw [← Nat.card_eq_fintype_card, hcard, pow_one])
  have hhall : IsHallOddIn (zpowers y) (zpowers y ⊔ D.T) := by
    refine ⟨le_sup_left, by rw [hyc]; exact hr.odd_of_ne_two hr2, a, ?_⟩
    have h1 := relIndex_mul_card (zpowers y) (zpowers y ⊔ D.T)
    rw [inf_eq_left.2 (le_sup_left : zpowers y ≤ zpowers y ⊔ D.T), hcard, hyc] at h1
    exact Nat.eq_of_mul_eq_mul_right hr.pos h1
  have hrank : ∀ q ∈ piSet (zpowers y ⊔ D.T), q ≠ 2 → CFSG.Open.pRank q (zpowers y ⊔ D.T) ≤ 2 := by
    intro q hq hq2
    obtain ⟨hqp, hqd⟩ := hq
    rw [hcard] at hqd
    have hqr : q = r := by
      rcases (Nat.Prime.dvd_mul hqp).1 hqd with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1 (hqp.dvd_of_dvd_pow h)) hq2
      · exact (Nat.prime_dvd_prime_iff_eq hqp hr).1 h
    rw [hqr]
    refine CFSG.SectionRank.pRank_le hr.one_lt fun F hF hFel => ?_
    obtain ⟨j, hj⟩ := hFel.isPGroup.exists_card_eq
    have h1 : Nat.card F ∣ 2 ^ a * r := by
      rw [← hcard]
      exact card_dvd_of_le hF
    have h2 : Nat.Coprime (Nat.card F) (2 ^ a) := by
      rw [hj]
      exact Nat.Coprime.pow j a ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
    exact (Nat.le_of_dvd hr.pos (h2.dvd_of_dvd_mul_left h1)).trans (Nat.le_self_pow (by norm_num) r)
  exact (h211 hH c (zpowers y) (by rw [hyc]; exact hr) (by rw [hyc]; exact hr2) hsol
    ⟨zpowers y, hhall, inferInstance⟩ hrank hyU).2 hyT

theorem uc22p218s_not_stronglyEmbedded (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hLM : L ≤ D.M) (hML : D.M ≤ normalizer (L : Set G)) {n r : ℕ}
    (hX : IsSp4 (Bar2 L) n) (hn : Odd n) (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1) :
    ¬ IsStronglyPEmbedded r D.M := by
  intro hsp
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyL, hy, hyT⟩ := uc22p218c_exists_orderOf_eq_mem_normalizer_sp4 D.sylowM.isPGroup
    (D.sylowM.le.trans hML) (D.sylowM.inf_of_le_normalizer hLM hML) hX hn dvd_rfl hrn
  have hyp : IsPGroup r (zpowers y) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hy1 : zpowers y ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot.1 h, orderOf_one] at hy
    exact hr.one_lt.ne hy
  exact uc22p218s_false_of_le_normalizer D Ch h211 hH c hr hr2 hy
    (uc22p22r_mem_uniqueSet_of_sp D hr hsp ((zpowers_le.2 hyL).trans hLM) hyp hy1) hyT

theorem s21_8E_of_conclusion76 (D : Data G) (Ch : Choice2011 G) (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (h211 : S21_1 D Ch)
    (hN : H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, Odd n → IsSp4 (Bar2 L) n →
      (L.subgroupOf D.M).Normal)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) : S21_8E D Ch := by
  intro hH c L hL n hn hX p hp
  by_contra h4
  have hns := UC6S846.not_solvable_of_mem_calC hL
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hsp := UC6S846.sp_of_mem_sig hSg hns hp
  have hLM : L ≤ D.M := hL.1.le
  haveI : (L.subgroupOf D.M).Normal := hN hH c L hL n hn hX
  have hML : D.M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  have hCL : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n - 1 → ¬ IsStronglyPEmbedded r D.M := fun r hr hr2 hrn =>
    uc22p218s_not_stronglyEmbedded D Ch h211 hH c hLM hML hX hn hr hr2 hrn
  by_cases hpn : p ∣ 2 ^ n - 1
  · exact hCL p hpp hp2 hpn hsp
  have hn3 : 3 ≤ n := uc22p218d_three_le_of_odd hX hn
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd (by omega) hrn
  by_cases hrσ : r ∈ D.sig
  · exact hCL r hr hr2 hrn (UC6S846.sp_of_mem_sig hSg hns hrσ)
  have hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p D.M := by
    have := uc22p218d_pRank_le_two_of_bar2 hX hpp hp2
    omega
  obtain ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hpow⟩ :=
    uc22p218s_exists_pow_torus hLM hX hpp hp2 hpn hr hr2 hrn hrank
  have hEM : E ≤ D.M := hEL.trans hLM
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [card_bot] at hEc
    exact (Nat.one_lt_pow two_ne_zero hr.one_lt).ne hEc
  obtain ⟨x, hxQ, hx1, hxC⟩ := uc22p218s_exists_mem_centralizer hpp hr hQel hQc hEel hE1 hpow
  have hxle : zpowers x ≤ D.M ⊓ centralizer (E : Set G) := zpowers_le.2 ⟨hQM hxQ, hxC⟩
  have hpos : 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) := UC6S846.le_pRank' hpp hxle
    (isElemAbelian_zpowers (hQel.2 x hxQ)) (by rw [Nat.card_zpowers, orderOf_eq_prime (hQel.2 x hxQ) hx1, pow_one])
  have hXN : ∀ X : Subgroup G, X ≤ E → Nat.card X = r → 1 < CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) := by
    intro X hXE _
    have hQX : Q ≤ normalizer (X : Set G) := le_normalizer_iff.2 fun x hx y hy => by
      obtain ⟨k, hk⟩ := hpow x hx
      rw [hk y (hXE hy)]
      exact pow_mem hy k
    have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) := UC6S846.le_pRank' hpp (le_inf hQM hQX) hQel hQc
    omega
  obtain ⟨R, hR, hER⟩ := UC6.exists_isSylowOf_ge hEM hEel.isPGroup
  have hEC : E ≤ centralizer (R : Set G) := uc22p218s_le_centralizer hX hr hr2 hrn hML hR hER hEL hEel.2
  have hΓ := h76 p hp hsp r hr E hEM hEel hEc hpos hXN
  exact hCL r hr hr2 hrn
    (h614 (UC6S846.sig_subset_sig1 hSg hns) r hr hr2 hrσ R hR E (le_inf hER hEC) hEel hEc hΓ)

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4) in
theorem s21_8E_setup4 (hSE : StronglyEmbeddedFive) (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (Ch : Choice2011 G) (h614 : UC6.R6_14 (UC6.dataOfSetup4 hS hU S))
    (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch)
    (hN : H1930 (UC6.dataOfSetup4 hS hU S) → ∀ _ : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch,
      ∀ L ∈ calC (UC6.dataOfSetup4 hS hU S).M, ∀ n : ℕ, Odd n → IsSp4 (Bar2 L) n →
        (L.subgroupOf (UC6.dataOfSetup4 hS hU S).M).Normal)
    (h3 : 3 ∈ uniqueFourBeta G → ∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig,
      IsStronglyPEmbedded p (UC6.dataOfSetup4 hS hU S).M → Conclusion76 (UC6.dataOfSetup4 hS hU S).M p) :
    S21_8E (UC6.dataOfSetup4 hS hU S) Ch :=
  s21_8E_of_conclusion76 _ Ch (UC6S846.sigmaStd_dataOfSetup4 hS hU S) h614 h211 hN fun p hp hsp => by
    by_cases h : 3 ∈ uniqueFourBeta G
    · exact h3 h p hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h hp hsp

end CFSG.LocalAnalysis.UniquenessCase.UC22
