module

public import CFSG.Timmesfeld.Bridge.RootClosureL2Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux1
public import CFSG.Timmesfeld.Bridge.Asc72Central
public import CFSG.Timmesfeld.Bridge.RootClosureRankOne

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.BenderSuzuki
open scoped commutatorElement

section General

variable {H : Type*} [Group H]

theorem orderOf_conj_eq' (g x : H) : orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

@[expose] def quotSetN (F : Set H) (M : Subgroup H) : Set (H ⧸ M) :=
  (fun c : H => (c : H ⧸ M)) '' {c | c ∈ F ∧ c ∉ M}

variable {F : Set H}

theorem isRootInvolutionSet_quotSetN (hF : IsRootInvolutionSet F) (M : Subgroup H)
    [M.Normal] : IsRootInvolutionSet (quotSetN F M) := by
  have hdvd : ∀ g : H, orderOf (g : H ⧸ M) ∣ orderOf g := fun g =>
    orderOf_map_dvd (QuotientGroup.mk' M) g
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨c, ⟨hc, hcM⟩, rfl⟩
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ← hF.1 c hc, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h1
      exact hcM ((QuotientGroup.eq_one_iff c).1 h1)
  · rintro _ ⟨c, ⟨hc, -⟩, rfl⟩ _ ⟨c', ⟨hc', -⟩, rfl⟩
    rw [← QuotientGroup.mk_mul]
    rcases hF.2.1 c hc c' hc' with h2 | h4 | ho
    · have h := hdvd (c * c')
      rw [h2] at h
      rcases (Nat.dvd_prime Nat.prime_two).1 h with h | h
      · right; right
        rw [h]
        exact odd_one
      · left
        exact h
    · have h := hdvd (c * c')
      rw [h4] at h
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show _ ∣ 2 ^ 2 from h)
      interval_cases i
      · right; right
        rw [hi', pow_zero]
        exact odd_one
      · left
        simpa using hi'
      · right; left
        simpa using hi'
    · right; right
      exact ho.of_dvd_nat (hdvd _)
  · rintro _ ⟨c, ⟨hc, -⟩, rfl⟩ _ ⟨c', ⟨hc', -⟩, rfl⟩ h4
    rw [← QuotientGroup.mk_mul] at h4 ⊢
    have h4' : orderOf (c * c') = 4 := by
      rcases hF.2.1 c hc c' hc' with h2 | h4' | ho
      · have h := hdvd (c * c')
        rw [h2, h4] at h
        exact absurd h (by norm_num)
      · exact h4'
      · have h := ho.of_dvd_nat (hdvd (c * c'))
        rw [h4] at h
        exact absurd h (by decide)
    refine ⟨(c * c') ^ 2, ⟨hF.2.2 c hc c' hc' h4', ?_⟩, QuotientGroup.mk_pow _ _ _⟩
    intro hM
    have h1 : ((c * c' : H) : H ⧸ M) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).2 hM
    have h := orderOf_dvd_of_pow_eq_one h1
    rw [h4] at h
    exact absurd h (by norm_num)

theorem conj_mem_quotSetN (hFn : ∀ g : H, ∀ f ∈ F, g * f * g⁻¹ ∈ F) (M : Subgroup H)
    [M.Normal] (k : H ⧸ M) {f : H ⧸ M} (hf : f ∈ quotSetN F M) :
    k * f * k⁻¹ ∈ quotSetN F M := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
  obtain ⟨c, ⟨hc, hcM⟩, rfl⟩ := hf
  refine ⟨g * c * g⁻¹, ⟨hFn g c hc, fun h => hcM ?_⟩, by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
  have h1 := (inferInstance : M.Normal).conj_mem _ h g⁻¹
  convert h1 using 1
  group

theorem conj_mem_rootSet_of_normal (hFn : ∀ g : H, ∀ f ∈ F, g * f * g⁻¹ ∈ F) (g : H)
    {d e : H} (he : e ∈ rootSet F d) : g * e * g⁻¹ ∈ rootSet F (g * d * g⁻¹) := by
  refine ⟨hFn g e he.1, fun f hf => ?_⟩
  have key : ∀ u : H, Commute (g * u * g⁻¹) f ↔ Commute u (g⁻¹ * f * g) := by
    intro u
    constructor
    · intro hc
      have h1 := hc.map (MulAut.conj g⁻¹).toMonoidHom
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
      convert h1 using 1
      group
    · intro hc
      have h1 := hc.map (MulAut.conj g).toMonoidHom
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      convert h1 using 1
      group
  rw [key, key]
  have hf' : g⁻¹ * f * g ∈ F := by simpa using hFn g⁻¹ f hf
  exact he.2 _ hf'

theorem mul_self_eq_one_of_pow_four [Finite H] {n : ℕ} (hn : 2 ≤ n) (e : H ≃* PSL2Model n)
    {g : H} (hg : g ^ 2 ^ 2 = 1) : g * g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers g) := isPGroup_iff_orderOf_dvd_pow.2 fun k => ⟨2, by
    rw [← Subgroup.orderOf_coe]
    exact (orderOf_dvd_of_mem_zpowers k.2).trans (orderOf_dvd_of_pow_eq_one hg)⟩
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hgQ : g ∈ Q := hQ (Subgroup.mem_zpowers g)
  exact Asc72.IsBenderGroup.mul_self_eq_one_of_commute (.isPSL2 n hn e) Q hgQ
    (fun q hq => Asc72.IsBenderGroup.commute_of_psl2 hn e Q _ hgQ _ hq)

theorem commute_of_minimal [Finite H] {V : Subgroup H} [hVn : V.Normal] (hV2 : IsPGroup 2 V)
    (hne : V ≠ ⊥) (hmin : ∀ W : Subgroup H, W.Normal → W ≤ V → W = ⊥ ∨ W = V) :
    ∀ v ∈ V, ∀ w ∈ V, Commute v w := by
  set Z := V ⊓ Subgroup.centralizer (V : Set H) with hZ
  have hZn : Z.Normal := by
    refine ⟨fun z hz k => Subgroup.mem_inf.2 ⟨hVn.conj_mem z (Subgroup.mem_inf.1 hz).1 k, ?_⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : k⁻¹ * w * k ∈ V := by simpa using hVn.conj_mem w hw k⁻¹
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 _ hw'
    calc w * (k * z * k⁻¹) = k * ((k⁻¹ * w * k) * z) * k⁻¹ := by group
      _ = k * (z * (k⁻¹ * w * k)) * k⁻¹ := by rw [h1]
      _ = k * z * k⁻¹ * w := by group
  have hZne : Z ≠ ⊥ := by
    have : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).2 hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := hV2.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center V)
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨((c : V) : H), (c : V).2, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩, ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 ⟨w, hw⟩)
    · intro h1
      apply hc1
      have h2 : ((c : V) : H) = 1 := congrArg Subtype.val h1
      exact Subtype.ext (Subtype.ext h2)
  rcases hmin Z hZn inf_le_left with h | h
  · exact absurd h hZne
  · intro v hv w hw
    have hvZ : v ∈ Z := h ▸ hv
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hvZ).2 w hw).symm

end General

section Chief

variable {K : Type} [Group K]

structure L2Chief (D : Set K) (V : Subgroup K) [V.Normal] (x a b h : K) (E : Set K) (n : ℕ) :
    Prop where
  root : IsRootInvolutionSet D
  normal : ∀ g : K, ∀ f ∈ D, g * f * g⁻¹ ∈ D
  x_mem : x ∈ D
  a_mem : a ∈ D
  b_mem : b ∈ D
  ab_mem : a * b ∈ D
  order : orderOf (a * x) = 3
  conj_b : IsConj a b
  conj_ab : IsConj a (a * b)
  gen : Subgroup.closure {x, a, b} = ⊤
  two : IsPGroup 2 V
  ne_bot : V ≠ ⊥
  min : ∀ W : Subgroup K, W.Normal → W ≤ V → W = ⊥ ∨ W = V
  two_le : 2 ≤ n
  iso : Nonempty (K ⧸ V ≃* PSL2Model n)
  sub : E ⊆ D
  a_E : a ∈ E
  b_E : b ∈ E
  comm : ∀ f ∈ E, ∀ g ∈ E, Commute f g
  conj_h : h * a * h⁻¹ = b
  h_E : ∀ f ∈ E, h * f * h⁻¹ ∈ E
  weak : ∀ f ∈ E, ∀ g ∈ E, ∀ e ∈ D, e ∈ V → Commute ⁅f, e⁆ g

namespace L2Chief

variable [Finite K] {D : Set K} {V : Subgroup K} [hVn : V.Normal] {x a b h : K} {E : Set K}
  {n : ℕ} (c : L2Chief D V x a b h E n)
include c

omit [Finite K] in
theorem conj_x : IsConj a x := by
  obtain ⟨g, -, hg⟩ := exists_conj_of_odd_orderOf_mul (c.root.mul_self_eq_one c.a_mem)
    (c.root.mul_self_eq_one c.x_mem) (by rw [c.order]; decide)
  exact isConj_iff.2 ⟨g, hg⟩

omit [Finite K] in
theorem isBender : IsBenderGroup (K ⧸ V) := by
  obtain ⟨e⟩ := c.iso
  exact .isPSL2 n c.two_le e

theorem a_not_mem : a ∉ V := by
  intro haV
  have hconjV : ∀ g, IsConj a g → g ∈ V := fun g hg => by
    obtain ⟨k, rfl⟩ := isConj_iff.1 hg
    exact hVn.conj_mem a haV k
  have htop : V = ⊤ := by
    rw [eq_top_iff, ← c.gen, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact hconjV _ c.conj_x
    · exact haV
    · exact hconjV _ c.conj_b
  obtain ⟨u, w, huw⟩ := Asc72.IsBenderGroup.exists_not_commute c.isBender
  apply huw
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  have hu : (u : K ⧸ V) = 1 := (QuotientGroup.eq_one_iff u).2 (htop ▸ Subgroup.mem_top u)
  rw [hu]
  exact Commute.one_left _

theorem not_mem_of_conj {g : K} (hg : IsConj a g) : g ∉ V := by
  intro hgV
  obtain ⟨k, rfl⟩ := isConj_iff.1 hg
  apply c.a_not_mem
  have h1 := hVn.conj_mem _ hgV k⁻¹
  convert h1 using 1
  group

theorem false_of_le_center (hVc : V ≤ Subgroup.center K) : False := by
  have hD := c.root
  obtain ⟨e⟩ := c.iso
  have hS : Asc72.Setup K {g | IsConj a g} := by
    refine ⟨⟨a, rfl⟩, ⟨fun f hf => ?_, fun f hf g hg => ?_⟩, ?_⟩
    · obtain ⟨k, rfl⟩ := isConj_iff.1 hf
      rw [orderOf_conj_eq']
      exact hD.1 a c.a_mem
    · have hfD : f ∈ D := by
        obtain ⟨k, rfl⟩ := isConj_iff.1 hf
        exact c.normal k a c.a_mem
      have hgD : g ∈ D := by
        obtain ⟨k, rfl⟩ := isConj_iff.1 hg
        exact c.normal k a c.a_mem
      rcases hD.2.1 f hfD g hgD with h2 | h4 | ho
      · left
        rw [h2]
      · exfalso
        have hw : (QuotientGroup.mk' V (f * g)) ^ 2 ^ 2 = 1 := by
          rw [← map_pow, orderOf_dvd_iff_pow_eq_one.1 (by rw [h4]; norm_num), map_one]
        have hw2 := mul_self_eq_one_of_pow_four c.two_le e hw
        have hmem : f * g * (f * g) ∈ V := by
          rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul]
          exact hw2
        have hzc := Subgroup.mem_center_iff.1 (hVc hmem)
        have hzD : f * g * (f * g) ∈ D := by
          rw [← sq]
          exact hD.2.2 f hfD g hgD h4
        have hf2 := hD.mul_self_eq_one hfD
        have hfzD : f * (f * g * (f * g)) ∈ D := by
          have h' := c.normal g f hfD
          rwa [show g * f * g⁻¹ = f * (f * g * (f * g)) by
            rw [hD.inv_eq hgD, show f * (f * g * (f * g)) = f * f * (g * f * g) by group, hf2,
              one_mul]] at h'
        obtain ⟨k, rfl⟩ := isConj_iff.1 hf
        have hhD : k * x * k⁻¹ ∈ D := c.normal k x c.x_mem
        have hho : orderOf (k * x * k⁻¹ * (k * a * k⁻¹)) = 3 := by
          rw [show k * x * k⁻¹ * (k * a * k⁻¹) = k * (x * a) * k⁻¹ by group, orderOf_conj_eq',
            orderOf_mul_comm_eq, c.order]
        have h' := Moufang.eq_of_collinear_of_odd hD hzD (hzc _) hfzD hhD (hzc _)
          (by rw [hho]; decide)
        rw [h', orderOf_one] at hho
        exact absurd hho (by norm_num)
      · right
        exact ho
    · rw [eq_top_iff, ← c.gen]
      refine Subgroup.closure_mono ?_
      rintro g (rfl | rfl | rfl)
      · exact c.conj_x
      · exact IsConj.refl _
      · exact c.conj_b
  have hinf := Asc72.inf_commutator_eq_bot_of_isBenderGroup hS hVc c.two c.isBender
  have hperf : commutator K = ⊤ := by
    have hab : ∀ g, IsConj a g → Abelianization.of g = Abelianization.of a := fun g hg =>
      (isConj_iff_eq.1 ((Abelianization.of (G := K)).map_isConj hg)).symm
    have hb1 : Abelianization.of b = 1 := by
      have h1 := hab _ c.conj_ab
      rw [map_mul] at h1
      exact mul_eq_left.1 h1
    have ha1 : Abelianization.of a = 1 := (hab _ c.conj_b).symm.trans hb1
    have hker : ∀ g, Abelianization.of g = 1 → g ∈ commutator K := fun g hg => by
      rw [← Abelianization.ker_of]
      exact hg
    rw [eq_top_iff, ← c.gen, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact hker _ ((hab _ c.conj_x).trans ha1)
    · exact hker _ ha1
    · exact hker _ hb1
  rw [hperf, inf_top_eq] at hinf
  exact c.ne_bot hinf

theorem exists_sylow (h1 : PSL2SylowCoordStmt) (h2 : L2TorusIrredStmt) :
    ∃ (P : Sylow 2 (K ⧸ V))
      (φ : (K ⧸ V) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)),
      (P : Subgroup (K ⧸ V)).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
        (Subgroup.closure E).map (QuotientGroup.mk' V) = P := by
  have hD := c.root
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' V with hπ
  have hE2 : ∀ g ∈ Subgroup.closure E, g * g = 1 := fun g hg =>
    mul_self_eq_one_of_mem_closure (fun f hf g hg _ => c.comm f hf g hg)
      (fun f hf => hD.mul_self_eq_one (c.sub hf)) hg
  have hEp : IsPGroup 2 ((Subgroup.closure E).map π) := by
    rintro ⟨y, ⟨g, hg, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    show π g ^ 2 ^ 1 = 1
    rw [pow_one, sq, ← map_mul, hE2 g hg, map_one]
  obtain ⟨P, hP⟩ := hEp.exists_le_sylow
  obtain ⟨φ, hφ⟩ := h1 n c.two_le (K ⧸ V) c.iso P
  refine ⟨P, φ, hφ, le_antisymm hP ?_⟩
  set F := GaloisField 2 n with hF
  have : Fintype F := Fintype.ofFinite F
  have hcard : 4 ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF, GaloisField.card 2 n (by have := c.two_le; omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) c.two_le
  have hmemW : ∀ g ∈ Subgroup.closure E, π g ∈ (Subgroup.closure E).map π :=
    fun g hg => ⟨g, hg, rfl⟩
  have hupper : ∀ q ∈ (Subgroup.closure E).map π, φ q ∈ upperUnipotent F := fun q hq => by
    rw [← hφ]
    exact ⟨q, hP hq, rfl⟩
  have hne1 : ∀ g : K, g ∉ V → φ (π g) ≠ 1 := fun g hg h1' => by
    apply hg
    have : π g = 1 := φ.injective (h1'.trans (map_one φ).symm)
    exact (QuotientGroup.eq_one_iff g).1 this
  have hab' : φ (π a) ≠ φ (π b) := by
    intro h'
    apply c.not_mem_of_conj c.conj_ab
    have h'' : π a = π b := φ.injective h'
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, ← hπ, h'', ← map_mul,
      hD.mul_self_eq_one c.b_mem, map_one]
  have hx2 : φ (π x) * φ (π x) = 1 := by
    rw [← map_mul, ← map_mul, hD.mul_self_eq_one c.x_mem, map_one, map_one]
  have hord : orderOf (φ (π a) * φ (π x)) = 3 := by
    rw [← map_mul, ← map_mul, MulEquiv.orderOf_eq,
      orderOf_mk_eq_of_odd c.two (by rw [c.order]; decide), c.order]
  have hgen : Subgroup.closure {φ (π x), φ (π a), φ (π b)} = ⊤ := by
    have h' := congrArg (Subgroup.map (φ.toMonoidHom.comp π)) c.gen
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _
      (φ.surjective.comp (QuotientGroup.mk'_surjective V))] at h'
    rw [← h']
    simp only [Set.image_insert_eq, Set.image_singleton, MonoidHom.coe_comp,
      Function.comp_apply, MulEquiv.coe_toMonoidHom]
  have hconj : φ (π h) * φ (π a) * (φ (π h))⁻¹ = φ (π b) := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, c.conj_h]
  have hEh : ∀ g ∈ Subgroup.closure E, h * g * h⁻¹ ∈ Subgroup.closure E := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem f hf => exact Subgroup.subset_closure (c.h_E f hf)
    | one => simp
    | mul u w _ _ ihu ihw =>
      rw [show h * (u * w) * h⁻¹ = h * u * h⁻¹ * (h * w * h⁻¹) by group]
      exact Subgroup.mul_mem _ ihu ihw
    | inv u _ ihu =>
      rw [show h * u⁻¹ * h⁻¹ = (h * u * h⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ihu
  set W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ((Subgroup.closure E).map π).map φ.toMonoidHom with hW
  have hWU : W ≤ upperUnipotent F := by
    rintro _ ⟨q, hq, rfl⟩
    exact hupper q hq
  have haW : φ (π a) ∈ W := ⟨π a, hmemW a (Subgroup.subset_closure c.a_E), rfl⟩
  have hWh : ∀ w ∈ W, φ (π h) * w * (φ (π h))⁻¹ ∈ W := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨π (h * g * h⁻¹), hmemW _ (hEh g hg), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  have hWeq := h2 F hcard (φ (π x)) (φ (π a)) (φ (π b)) (φ (π h))
    (hupper _ (hmemW a (Subgroup.subset_closure c.a_E)))
    (hupper _ (hmemW b (Subgroup.subset_closure c.b_E))) (hne1 a c.a_not_mem)
    (hne1 b (c.not_mem_of_conj c.conj_b)) hab' hx2 hord hgen hconj W hWU haW hWh
  intro p hp
  have hφp : φ p ∈ W := by
    rw [hWeq, ← hφ]
    exact ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hqp⟩ := hφp
  have hqp' : q = p := φ.injective hqp
  rw [← hqp']
  exact hq

omit [Finite K] in
theorem quadratic (hVcomm : ∀ v ∈ V, ∀ w ∈ V, Commute v w) {S : Subgroup K}
    (hS : S = Subgroup.closure E ⊔ V) : ∀ s ∈ S, ∀ s' ∈ S, ∀ v ∈ V, Commute s' ⁅s, v⁆ := by
  have hD := c.root
  have hcV : ∀ s : K, ∀ v ∈ V, ⁅s, v⁆ ∈ V := fun s v hv => by
    rw [commutatorElement_def]
    exact V.mul_mem (hVn.conj_mem v hv s) (V.inv_mem hv)
  have hmul : ∀ f : K, ∀ u ∈ V, ∀ w ∈ V, ⁅f, u * w⁆ = ⁅f, u⁆ * ⁅f, w⁆ := by
    intro f u hu w hw
    have hc : Commute u⁻¹ ⁅f, w⁆ := hVcomm _ (V.inv_mem hu) _ (hcV f w hw)
    rw [commutatorElement_def] at hc
    simp only [commutatorElement_def]
    calc f * (u * w) * f⁻¹ * (u * w)⁻¹ = f * u * f⁻¹ * ((f * w * f⁻¹ * w⁻¹) * u⁻¹) := by group
      _ = f * u * f⁻¹ * (u⁻¹ * (f * w * f⁻¹ * w⁻¹)) := by rw [← hc.eq]
      _ = f * u * f⁻¹ * u⁻¹ * (f * w * f⁻¹ * w⁻¹) := by group
  have hinv : ∀ f : K, ∀ u ∈ V, ⁅f, u⁻¹⁆ = ⁅f, u⁆⁻¹ := by
    intro f u hu
    have hc : Commute u (f * u * f⁻¹)⁻¹ := hVcomm _ hu _ (V.inv_mem (hVn.conj_mem u hu f))
    simp only [commutatorElement_def]
    calc f * u⁻¹ * f⁻¹ * u⁻¹⁻¹ = (f * u * f⁻¹)⁻¹ * u := by group
      _ = u * (f * u * f⁻¹)⁻¹ := hc.eq.symm
      _ = (f * u * f⁻¹ * u⁻¹)⁻¹ := by group
  have hQ0 : ∀ f ∈ E, ∀ g ∈ E, ∀ v ∈ V, Commute g ⁅f, v⁆ := by
    by_cases hDV : ∃ e ∈ D, e ∈ V
    · obtain ⟨e₀, he₀D, he₀V⟩ := hDV
      set Y : Set K := {e | e ∈ D ∧ e ∈ V} with hY
      have hYn : (Subgroup.closure Y).Normal := by
        refine ⟨fun g hg k => ?_⟩
        induction hg using Subgroup.closure_induction with
        | mem y hy => exact Subgroup.subset_closure ⟨c.normal k y hy.1, hVn.conj_mem y hy.2 k⟩
        | one => simp
        | mul u w _ _ ihu ihw =>
          rw [show k * (u * w) * k⁻¹ = k * u * k⁻¹ * (k * w * k⁻¹) by group]
          exact Subgroup.mul_mem _ ihu ihw
        | inv u _ ihu =>
          rw [show k * u⁻¹ * k⁻¹ = (k * u * k⁻¹)⁻¹ by group]
          exact Subgroup.inv_mem _ ihu
      have hYV : Subgroup.closure Y ≤ V := by
        rw [Subgroup.closure_le]
        exact fun y hy => hy.2
      have hYne : Subgroup.closure Y ≠ ⊥ := by
        intro h0
        have h1 : e₀ ∈ Subgroup.closure Y := Subgroup.subset_closure ⟨he₀D, he₀V⟩
        rw [h0, Subgroup.mem_bot] at h1
        exact hD.ne_one he₀D h1
      have hYeq : Subgroup.closure Y = V := (c.min _ hYn hYV).resolve_left hYne
      intro f hf g hg v hv
      rw [← hYeq] at hv
      induction hv using Subgroup.closure_induction with
      | mem y hy => exact (c.weak f hf g hg y hy.1 hy.2).symm
      | one => simp
      | mul u w hu hw ihu ihw =>
        rw [hmul f u (hYV hu) w (hYV hw)]
        exact ihu.mul_right ihw
      | inv u hu ihu =>
        rw [hinv f u (hYV hu)]
        exact ihu.inv_right
    · push Not at hDV
      intro f hf g hg v hv
      have hfD := c.sub hf
      have hgD := c.sub hg
      have hfg2 : f * g * (f * g) = 1 := by
        rw [show f * g * (f * g) = f * (g * f) * g by group, ← (c.comm f hf g hg).eq,
          show f * (f * g) * g = f * f * (g * g) by group, hD.mul_self_eq_one hfD,
          hD.mul_self_eq_one hgD, one_mul]
      set u := v * f * v⁻¹ * f⁻¹ with hu
      have huV : u ∈ V := by
        rw [hu, show v * f * v⁻¹ * f⁻¹ = v * (f * v⁻¹ * f⁻¹) by group]
        exact V.mul_mem hv (hVn.conj_mem _ (V.inv_mem hv) f)
      have hf'D : v * f * v⁻¹ ∈ D := c.normal v f hfD
      have hsqV : v * f * v⁻¹ * g * (v * f * v⁻¹ * g) ∈ V := by
        have e1 : v * f * v⁻¹ * g * (v * f * v⁻¹ * g) =
            u * ((f * g) * u * (f * g)⁻¹) * (f * g * (f * g)) := by
          rw [hu]
          group
        rw [e1, hfg2, mul_one]
        exact V.mul_mem huV (hVn.conj_mem u huV (f * g))
      obtain ⟨k, hk⟩ := c.two ⟨_, hsqV⟩
      have hpow : (v * f * v⁻¹ * g) ^ 2 ^ (k + 1) = 1 := by
        have h1 := congrArg Subtype.val hk
        simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h1
        rw [pow_succ', pow_mul, sq]
        exact h1
      have hcomm : Commute (v * f * v⁻¹) g := by
        rcases hD.2.1 _ hf'D g hgD with h2 | h4 | ho
        · exact (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hf'D)
            (hD.mul_self_eq_one hgD)).2 (by rw [← h2]; exact pow_orderOf_eq_one _)
        · exfalso
          have h4' : (v * f * v⁻¹ * g) ^ 2 ∈ D := hD.2.2 _ hf'D g hgD h4
          rw [sq] at h4'
          exact hDV _ h4' hsqV
        · have h1 : orderOf (v * f * v⁻¹ * g) = 1 :=
            Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ho))
              (orderOf_dvd_of_pow_eq_one hpow)
          rw [orderOf_eq_one_iff] at h1
          rw [eq_inv_of_mul_eq_one_left h1]
          exact (Commute.refl g).inv_left
      have h' : ⁅f, v⁆ = f * (v * f * v⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [h']
      exact (c.comm f hf g hg).symm.mul_right hcomm.symm.inv_right
  have hQ1 : ∀ s ∈ Subgroup.closure E, ∀ g ∈ E, ∀ v ∈ V, Commute g ⁅s, v⁆ := by
    intro s hs g hg v hv
    have hgE : ∀ t ∈ Subgroup.closure E, Commute g t := fun t ht =>
      commute_of_mem_closure (fun f hf f' hf' => c.comm f hf f' hf')
        (Subgroup.subset_closure hg) ht
    induction hs using Subgroup.closure_induction with
    | mem f hf => exact hQ0 f hf g hg v hv
    | one => simp
    | mul s₁ s₂ hs₁ _ ih₁ ih₂ =>
      rw [show ⁅s₁ * s₂, v⁆ = s₁ * ⁅s₂, v⁆ * s₁⁻¹ * ⁅s₁, v⁆ by
        simp only [commutatorElement_def]; group]
      exact (((hgE s₁ hs₁).mul_right ih₂).mul_right (hgE s₁ hs₁).inv_right).mul_right ih₁
    | inv s hs' ih =>
      rw [show ⁅s⁻¹, v⁆ = s⁻¹ * ⁅s, v⁆⁻¹ * s by simp only [commutatorElement_def]; group]
      exact (((hgE s hs').inv_right).mul_right ih.inv_right).mul_right (hgE s hs')
  intro s hs s' hs' v hv
  rw [hS] at hs hs'
  obtain ⟨s₀, hs₀, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hs
  have e1 : ⁅s₀ * w, v⁆ = ⁅s₀, v⁆ := by
    have hwv : Commute w v := hVcomm w hw v hv
    simp only [commutatorElement_def]
    calc s₀ * w * v * (s₀ * w)⁻¹ * v⁻¹ = s₀ * (w * v * w⁻¹) * s₀⁻¹ * v⁻¹ := by group
      _ = s₀ * v * s₀⁻¹ * v⁻¹ := by rw [hwv.eq, mul_inv_cancel_right]
  rw [e1]
  obtain ⟨s₀', hs₀', w', hw', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hs'
  clear hs'
  have h1 : Commute s₀' ⁅s₀, v⁆ := by
    induction hs₀' using Subgroup.closure_induction with
    | mem g hg => exact hQ1 s₀ hs₀ g hg v hv
    | one => exact Commute.one_left _
    | mul _ _ _ _ ih₁ ih₂ => exact ih₁.mul_left ih₂
    | inv _ _ ih => exact ih.inv_left
  exact h1.mul_left (hVcomm w' hw' _ (hcV s₀ v hv))

theorem exists_complement (hVcomm : ∀ v ∈ V, ∀ w ∈ V, Commute v w) (S : Sylow 2 K)
    (hS : (S : Subgroup K) = Subgroup.closure E ⊔ V) :
    ∃ R : Subgroup K, V ⊓ R = ⊥ ∧ V ⊔ R = ⊤ := by
  have hD := c.root
  have hcomm : ∀ u ∈ Subgroup.closure E, ∀ w ∈ Subgroup.closure E, Commute u w :=
    fun u hu w hw => commute_of_mem_closure (fun f hf g hg => c.comm f hf g hg) hu hw
  have hEl : CFSG.Open.IsElemAbelian 2 (Subgroup.closure E) := by
    refine ⟨⟨⟨fun u w => Subtype.ext (hcomm u u.2 w w.2).eq⟩⟩, fun g hg => ?_⟩
    rw [sq]
    exact mul_self_eq_one_of_mem_closure (fun f hf g hg _ => c.comm f hf g hg)
      (fun f hf => hD.mul_self_eq_one (c.sub hf)) hg
  obtain ⟨C, hCE, hC1, hC2⟩ :=
    SignalizerFunctorTheorem.McBride.Near.Lemma27.exists_isCompl_of_le Nat.prime_two hEl
      (inf_le_left : Subgroup.closure E ⊓ V ≤ Subgroup.closure E) le_rfl
  have : IsMulCommutative V := ⟨⟨fun u w => Subtype.ext (hVcomm u u.2 w w.2).eq⟩⟩
  have hVC : V ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [← hC1]
    exact ⟨⟨hCE hg.2, hg.1⟩, hg.2⟩
  have hVCS : V ⊔ C = S := by
    rw [hS]
    apply le_antisymm
    · exact sup_le le_sup_right (hCE.trans le_sup_left)
    · refine sup_le ?_ le_sup_left
      rw [← hC2]
      exact sup_le (inf_le_right.trans le_sup_left) le_sup_right
  exact SignalizerFunctorTheorem.McBride.exists_complement_of_sylow_complement Nat.prime_two
    c.two S (hS ▸ le_sup_right) hVC hVCS

theorem false (h1 : PSL2SylowCoordStmt) (h2 : L2TorusIrredStmt) (h3 : NaturalComplementStmt) :
    False := by
  have hD := c.root
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hVc : V ≤ Subgroup.center K
  · exact c.false_of_le_center hVc
  have hVcomm := commute_of_minimal c.two c.ne_bot c.min
  have hfix : ∀ v ∈ V, (∀ k : K, Commute k v) → v = 1 := by
    intro v hv hcomm
    have hZn : (V ⊓ Subgroup.center K).Normal := inferInstance
    rcases c.min _ hZn inf_le_left with h0 | h0
    · have hvZ : v ∈ V ⊓ Subgroup.center K :=
        ⟨hv, Subgroup.mem_center_iff.2 fun k => hcomm k⟩
      rw [h0, Subgroup.mem_bot] at hvZ
      exact hvZ
    · exact absurd (h0 ▸ (inf_le_right : V ⊓ Subgroup.center K ≤ Subgroup.center K)) hVc
  obtain ⟨P, φ, hφ, hEP⟩ := c.exists_sylow h1 h2
  set π := QuotientGroup.mk' V with hπ
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact c.two
  set S : Sylow 2 K := P.comapOfKerIsPGroup π hker (by
    rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective V)]
    exact le_top) with hSdef
  have hS : (S : Subgroup K) = Subgroup.closure E ⊔ V := by
    rw [hSdef, Sylow.coe_comapOfKerIsPGroup, ← hEP, Subgroup.comap_map_eq, hπ,
      QuotientGroup.ker_mk']
  obtain ⟨R, hVR, hVR'⟩ := c.exists_complement hVcomm S hS
  have hdecomp : ∀ k : K, ∃ v ∈ V, ∃ r ∈ R, v * r = k := fun k =>
    Subgroup.mem_sup_of_normal_left.1 (hVR' ▸ Subgroup.mem_top k)
  have hπR : Function.Bijective (π.comp R.subtype) := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro r hr
      have hrV : (r : K) ∈ V := (QuotientGroup.eq_one_iff _).1 hr
      have hrVR : (r : K) ∈ V ⊓ R := ⟨hrV, r.2⟩
      rw [hVR, Subgroup.mem_bot] at hrVR
      exact Subtype.ext hrVR
    · intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective V q
      obtain ⟨v, hv, r, hr, rfl⟩ := hdecomp k
      refine ⟨⟨r, hr⟩, ?_⟩
      show π r = π (v * r)
      rw [map_mul, show π v = 1 from (QuotientGroup.eq_one_iff v).2 hv, one_mul]
  set ψ : ↥R ≃* K ⧸ V := MulEquiv.ofBijective (π.comp R.subtype) hπR with hψ
  set F := GaloisField 2 n with hF
  set φR : ↥R ≃* Matrix.SpecialLinearGroup (Fin 2) F := ψ.trans φ with hφR
  set A : Subgroup K := (S : Subgroup K) ⊓ R with hA
  have hAmap : (A.subgroupOf R).map φR.toMonoidHom = upperUnipotent F := by
    have hψA : (A.subgroupOf R).map ψ.toMonoidHom = P := by
      ext q
      constructor
      · rintro ⟨r, hr, rfl⟩
        have hrS : (r : K) ∈ (S : Subgroup K) :=
          (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hr)).1
        rw [hSdef, Sylow.coe_comapOfKerIsPGroup] at hrS
        exact hrS
      · intro hq
        obtain ⟨r, hr⟩ := hπR.2 q
        refine ⟨r, Subgroup.mem_subgroupOf.2 ⟨?_, r.2⟩, hr⟩
        rw [hSdef, Sylow.coe_comapOfKerIsPGroup]
        show π r ∈ P
        rw [← hr] at hq
        exact hq
    rw [← hφ, ← hψA, Subgroup.map_map]
    exact congrArg (fun f => (A.subgroupOf R).map f) (MonoidHom.ext fun _ => rfl)
  have hVS : V ≤ (S : Subgroup K) := hS ▸ le_sup_right
  have : Group.IsNilpotent ↥(S : Subgroup K) := S.isPGroup'.isNilpotent
  have : (V.subgroupOf (S : Subgroup K)).Normal := hVn.subgroupOf _
  have hne' : V.subgroupOf (S : Subgroup K) ≠ ⊥ := by
    intro h0
    apply c.ne_bot
    rw [← Subgroup.map_subgroupOf_eq_of_le hVS, h0, Subgroup.map_bot]
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  have hwV : ((y : (S : Subgroup K)) : K) ∈ V := (Subgroup.mem_inf.1 y.2).1
  have hwA : ∀ s ∈ A, Commute s ((y : (S : Subgroup K)) : K) := fun s hs =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 y.2).2
      ⟨s, (Subgroup.mem_inf.1 hs).1⟩)
  have hw1 : ((y : (S : Subgroup K)) : K) ≠ 1 := fun h1' => hy1 (Subtype.ext (Subtype.ext h1'))
  obtain ⟨θ, hθ, hθrange, -⟩ := ARS.exists_natural_of_quadratic_conj (N := V) φR hAmap
    hVcomm (fun r _ v hv => hVn.conj_mem v hv r)
    (fun v hv hcomm => hfix v hv fun k => by
      obtain ⟨v', hv', r, hr, rfl⟩ := hdecomp k
      exact (hVcomm v' hv' v hv).mul_left (hcomm r hr))
    (fun v hv s hs s' hs' => c.quadratic hVcomm hS s (Subgroup.mem_inf.1 hs).1 s'
      (Subgroup.mem_inf.1 hs').1 v hv) hwV hwA hw1
  set W₁ := Subgroup.closure
    (Set.range fun r : ↥R => (r : K) * ((y : (S : Subgroup K)) : K) * (r : K)⁻¹) with hW₁
  have hW₁V : W₁ ≤ V := by
    rw [hW₁, Subgroup.closure_le]
    rintro _ ⟨r, rfl⟩
    exact hVn.conj_mem _ hwV r
  have hW₁n : W₁.Normal := by
    refine ⟨fun g hg k => ?_⟩
    obtain ⟨v', hv', r, hr, rfl⟩ := hdecomp k
    have hrg : r * g * r⁻¹ ∈ W₁ := by
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨r', rfl⟩ := hg
        exact Subgroup.subset_closure ⟨⟨r, hr⟩ * r', by
          simp only [Subgroup.coe_mul, mul_inv_rev]
          group⟩
      | one => simp
      | mul u u' _ _ ihu ihu' =>
        rw [show r * (u * u') * r⁻¹ = r * u * r⁻¹ * (r * u' * r⁻¹) by group]
        exact Subgroup.mul_mem _ ihu ihu'
      | inv u _ ihu =>
        rw [show r * u⁻¹ * r⁻¹ = (r * u * r⁻¹)⁻¹ by group]
        exact Subgroup.inv_mem _ ihu
    have hcomm : Commute v' (r * g * r⁻¹) := hVcomm v' hv' _ (hW₁V hrg)
    rw [show v' * r * g * (v' * r)⁻¹ = v' * (r * g * r⁻¹) * v'⁻¹ by group, hcomm.eq,
      mul_inv_cancel_right]
    exact hrg
  have hW₁ne : W₁ ≠ ⊥ := by
    intro h0
    apply hw1
    have h' : ((y : (S : Subgroup K)) : K) ∈ W₁ := Subgroup.subset_closure ⟨1, by simp⟩
    rw [h0, Subgroup.mem_bot] at h'
    exact h'
  have hW₁eq : W₁ = V := (c.min W₁ hW₁n hW₁V).resolve_left hW₁ne
  have hθV : ∀ v, θ v ∈ V := fun v => by
    have h' : θ v ∈ Set.range θ := ⟨v, rfl⟩
    rw [hθrange, hW₁eq] at h'
    exact h'
  have : Fintype F := Fintype.ofFinite F
  have hcard : 4 ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF, GaloisField.card 2 n (by have := c.two_le; omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) c.two_le
  have hθ0 : θ 0 = 1 := hθ.map_zero
  have hθR : ∀ v, θ v ∈ R → v = 0 := fun v hv => by
    have h' : θ v ∈ V ⊓ R := ⟨hθV v, hv⟩
    rw [hVR, Subgroup.mem_bot] at h'
    exact hθ.injective (h'.trans hθ0.symm)
  have hθdec : ∀ k : K, ∃ v, ∃ r ∈ R, k = θ v * r := fun k => by
    obtain ⟨v', hv', r, hr, rfl⟩ := hdecomp k
    have h' : v' ∈ Set.range θ := by
      rw [hθrange, hW₁eq]
      exact hv'
    obtain ⟨v, rfl⟩ := h'
    exact ⟨v, r, hr, rfl⟩
  have hmem : ∀ g : K, g ∈ Subgroup.closure {x, a, b} := fun g => c.gen ▸ Subgroup.mem_top g
  have key := h3 K F hcard R φR θ hθ hθR hθdec x a b (hD.mul_self_eq_one c.x_mem)
    (hD.mul_self_eq_one c.a_mem) (hD.mul_self_eq_one c.b_mem)
    (fun v hv => c.not_mem_of_conj c.conj_x (hv ▸ hθV v)) (fun v hv => c.a_not_mem (hv ▸ hθV v))
    (fun v hv => c.not_mem_of_conj c.conj_b (hv ▸ hθV v))
    (fun g => ⟨0, g, hmem g, by rw [hθ0, one_mul]⟩) ![1, 0] (hmem _)
  have h10 := congrFun key 0
  simp at h10

end L2Chief

end Chief

end CFSG.Timmesfeld.Bridge.RootClosure
