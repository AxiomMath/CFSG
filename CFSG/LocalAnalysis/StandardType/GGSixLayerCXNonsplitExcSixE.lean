module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcTags
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyCenter
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny LayerFacts LayerSixE
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace ExcNonsplit

section Group

theorem mem_inner_of_pow_eq_one {C : Type*} [Group C] {D : Subgroup (MulAut C)}
    (hD : ∀ d ∈ D, d ^ 3 ∈ inner C) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {α : MulAut C}
    (hα : α ∈ inner C ⊔ D) (hαp : α ^ p = 1) : α ∈ inner C := by
  have h1 : QuotientGroup.mk' (inner C) α ∈ D.map (QuotientGroup.mk' (inner C)) := by
    have h := Subgroup.mem_map_of_mem (QuotientGroup.mk' (inner C)) hα
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h
  obtain ⟨d, hd, hdα⟩ := h1
  have h3 : QuotientGroup.mk' (inner C) α ^ 3 = 1 := by
    rw [← hdα, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hD d hd
  have hp' : QuotientGroup.mk' (inner C) α ^ p = 1 := by rw [← map_pow, hαp, map_one]
  have hord : orderOf (QuotientGroup.mk' (inner C) α) ∣ Nat.gcd 3 p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hp')
  have hg : Nat.gcd 3 p = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hord
  exact hord

theorem conj_mul_aux {G : Type*} [Group G] {w g h : G}
    (hc : g⁻¹ * (w * g * w⁻¹) * h = h * (g⁻¹ * (w * g * w⁻¹))) :
    (g * h)⁻¹ * (w * (g * h) * w⁻¹) = g⁻¹ * (w * g * w⁻¹) * (h⁻¹ * (w * h * w⁻¹)) := by
  have hc' : g⁻¹ * (w * g * w⁻¹) * h⁻¹ = h⁻¹ * (g⁻¹ * (w * g * w⁻¹)) := by
    calc g⁻¹ * (w * g * w⁻¹) * h⁻¹ = h⁻¹ * (h * (g⁻¹ * (w * g * w⁻¹)) * h⁻¹) := by group
      _ = h⁻¹ * (g⁻¹ * (w * g * w⁻¹) * h * h⁻¹) := by rw [hc]
      _ = h⁻¹ * (g⁻¹ * (w * g * w⁻¹)) := by group
  calc (g * h)⁻¹ * (w * (g * h) * w⁻¹) = h⁻¹ * (g⁻¹ * (w * g * w⁻¹)) * (w * h * w⁻¹) := by group
    _ = g⁻¹ * (w * g * w⁻¹) * h⁻¹ * (w * h * w⁻¹) := by rw [hc']
    _ = g⁻¹ * (w * g * w⁻¹) * (h⁻¹ * (w * h * w⁻¹)) := by group

theorem mem_centralizer_of_induces_one {L C G : Type*} [Group L] [Group C] [Group G]
    {π : L →* C} {ψ : L →* G} (hπker : π.ker ≤ Subgroup.center L)
    (hperf : commutator ↥ψ.range = ⊤) {w : G}
    (hwN : w ∈ Subgroup.normalizer (ψ.range : Set G)) (hw : GGInduces π ψ w 1) :
    w ∈ Subgroup.centralizer (ψ.range : Set G) := by
  have hcen : ∀ g ∈ ψ.range, g⁻¹ * (w * g * w⁻¹) ∈ (Subgroup.center L).map ψ := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := exists_conj_eq hwN y
    have h1 : π y' = π y := by
      have := hw y y' hy'
      rwa [MulAut.one_apply] at this
    refine ⟨y⁻¹ * y', hπker ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    · rw [map_mul, map_inv, hy']
  have hcomm : ∀ z ∈ (Subgroup.center L).map ψ, ∀ g ∈ ψ.range, z * g = g * z := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨u, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz u).symm]
  let Φ : ↥ψ.range →* G :=
    { toFun := fun g => (g : G)⁻¹ * (w * g * w⁻¹)
      map_one' := by simp
      map_mul' := fun g h => by
        simp only [Subgroup.coe_mul]
        exact conj_mul_aux (hcomm _ (hcen g g.2) h h.2) }
  have hΦ : ∀ g : ↥ψ.range, Φ g = (g : G)⁻¹ * (w * g * w⁻¹) := fun _ => rfl
  have hker : (⊤ : Subgroup ↥ψ.range) ≤ Φ.ker := by
    rw [← hperf, commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ (hcen g g.2) _
      ((Subgroup.map_le_range ψ _) (by rw [hΦ]; exact hcen h h.2))
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h1 : Φ ⟨g, hg⟩ = 1 := hker (Subgroup.mem_top _)
  rw [hΦ] at h1
  have h2 : w * g * w⁻¹ = g := by
    calc w * g * w⁻¹ = g * (g⁻¹ * (w * g * w⁻¹)) := by group
      _ = g := by rw [h1, mul_one]
  calc g * w = w * g * w⁻¹ * w := by rw [h2]
    _ = w * g := by group

theorem mul_comm_of_commutator_mem_center {L : Type*} [Group L] {s t : L} {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hsp : s ^ p = 1)
    (hz : s * t * s⁻¹ * t⁻¹ ∈ Subgroup.center L) (hz3 : (s * t * s⁻¹ * t⁻¹) ^ 3 = 1) :
    s * t = t * s := by
  set z := s * t * s⁻¹ * t⁻¹ with hzdef
  have hzt : s * t * s⁻¹ = z * t := by rw [hzdef]; group
  have hn : ∀ n : ℕ, s ^ n * t * (s ^ n)⁻¹ = z ^ n * t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : ∀ g : L, z ^ n * g = g * z ^ n := fun g =>
        (Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz n) g).symm
      calc s ^ (n + 1) * t * (s ^ (n + 1))⁻¹ = s * (s ^ n * t * (s ^ n)⁻¹) * s⁻¹ := by
            rw [pow_succ']; group
        _ = s * (z ^ n * t) * s⁻¹ := by rw [ih]
        _ = s * z ^ n * t * s⁻¹ := by group
        _ = z ^ n * s * t * s⁻¹ := by rw [← hc s]
        _ = z ^ n * (s * t * s⁻¹) := by group
        _ = z ^ n * (z * t) := by rw [hzt]
        _ = z ^ (n + 1) * t := by rw [pow_succ]; group
  have hzp : z ^ p = 1 := by
    have h := hn p
    rw [hsp, one_mul, inv_one, mul_one] at h
    calc z ^ p = z ^ p * t * t⁻¹ := by group
      _ = 1 := by rw [← h, mul_inv_cancel]
  have hord : orderOf z ∣ Nat.gcd 3 p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz3) (orderOf_dvd_of_pow_eq_one hzp)
  have hg : Nat.gcd 3 p = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hord
  have h1 : s * t * s⁻¹ = t := by rw [hzt, hord, one_mul]
  calc s * t = s * t * s⁻¹ * s := by group
    _ = t * s := by rw [h1]

end Group

end ExcNonsplit


namespace ExcNonsplit

theorem rootDiagAutHom_pow_three_mem_inner_E6
    {K : Type} [Field K] [Finite K] (a : Fin Tag.E6.rank → Kˣ) :
    rootDiagAutHom .E6 K a ^ 3 ∈ inner ↥(adjointGroup .E6 K) := by
  rw [← map_pow]
  set R := (CFSG.LocalAnalysis.ComponentInitial.monomialHom (G := Kˣ)
    Tag.E6.cartan.transpose).range with hR
  have hidx : R.index ∣ 3 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.index_range_monomialHom_dvd K
      Tag.E6.cartan.transpose).2
    rw [Matrix.det_transpose, det_cartan_E6] at h
    exact h
  obtain ⟨m, hm⟩ := hidx
  have h3 : a ^ 3 ∈ R := by
    rw [hm, pow_mul]
    exact R.pow_mem (Subgroup.pow_index_mem R a) m
  obtain ⟨t, ht⟩ := h3
  change rootDiagAut .E6 K (a ^ 3) ∈ inner ↥(adjointGroup .E6 K)
  rw [← ht, monomialHom_transpose_cartan]
  exact rootDiagAut_cartanChar_mem_inner t

theorem ker_eq_bot_or_center_E6
    {k : Type} [Field k] [Finite k]
    {G : Type*} [Group G] {ψ : ↥(e6Data_valid.minGroup k) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k)) :
    ψ.ker = ⊥ ∨ ψ.ker = Subgroup.center ↥(e6Data_valid.minGroup k) := by
  have : Finite ↥(e6Data_valid.minGroup k) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e6Data_valid
  obtain ⟨hcard, -⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 (k := k)
  have hZ3 : Nat.card (Subgroup.center ↥(e6Data_valid.minGroup k)) ∣ 3 := by
    rw [hcard]
    exact Nat.gcd_dvd_left _ _
  have hdvd : Nat.card ψ.ker ∣ 3 := (Subgroup.card_dvd_of_le hker).trans hZ3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h1)
  · right
    apply Subgroup.eq_of_le_of_card_ge hker
    rw [h3]
    exact Nat.le_of_dvd (by norm_num) hZ3

section Isogeny

theorem exists_factor_e6Isogeny {k : Type} [Field k] [Finite k] {G : Type*} [Group G]
    {ψ : ↥(e6Data_valid.minGroup k) →* G}
    (hker : ψ.ker = Subgroup.center ↥(e6Data_valid.minGroup k)) :
    ∃ ψb : ↥(adjointGroup .E6 k) →* G, Function.Injective ψb ∧
      ∀ y, ψb (e6Isogeny k y) = ψ y := by
  have hkπ : (e6Isogeny k).ker = ψ.ker := by
    rw [hker]
    exact CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center
  let e := QuotientGroup.quotientKerEquivOfSurjective (e6Isogeny k) (e6Isogeny_surjective k)
  let ψb : ↥(adjointGroup .E6 k) →* G :=
    (QuotientGroup.lift (e6Isogeny k).ker ψ hkπ.le).comp e.symm.toMonoidHom
  have hval : ∀ y, ψb (e6Isogeny k y) = ψ y := by
    intro y
    have he : e.symm (e6Isogeny k y) = QuotientGroup.mk y := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift (e6Isogeny k).ker ψ hkπ.le (e.symm (e6Isogeny k y)) = ψ y
    rw [he, QuotientGroup.lift_mk]
  refine ⟨ψb, ?_, hval⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  obtain ⟨y, rfl⟩ := e6Isogeny_surjective k c
  rw [MonoidHom.mem_ker, hval] at hc
  have hy : y ∈ (e6Isogeny k).ker := by
    rw [hkπ]
    exact MonoidHom.mem_ker.mpr hc
  rw [Subgroup.mem_bot]
  exact MonoidHom.mem_ker.mp hy

theorem exists_lift_pow_eq_one_E6 {k : Type} [Field k] [Finite k]
    {a : ↥(adjointGroup .E6 k)} {p : ℕ} (ha : a ^ p = 1) (hp : p.Prime) (hp3 : p ≠ 3) :
    ∃ s : ↥(e6Data_valid.minGroup k), s ^ p = 1 ∧ e6Isogeny k s = a := by
  obtain ⟨s₀, hs₀⟩ := e6Isogeny_surjective k a
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨s₀ ^ (3 * m), ?_, ?_⟩
  · have hz : s₀ ^ p ∈ Subgroup.center ↥(e6Data_valid.minGroup k) := by
      rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center, MonoidHom.mem_ker,
        map_pow, hs₀, ha]
    have h3 := CFSG.ClassicalInvolution.ModelFacts.A2Isogeny.center_pow_three_e6 k hz
    rw [← pow_mul, mul_comm (3 * m) p, pow_mul, pow_mul, h3, one_pow]
  · rw [map_pow, hs₀, ← Nat.div_add_mod (3 * m) p, pow_add, pow_mul, ha, one_pow, one_mul, hm,
      pow_one]

end Isogeny

end ExcNonsplit

namespace ExcNonsplit

section Pairs

variable {L C G : Type*} [Group L] [Group C] [Group G]

theorem mem_ggConjPairs_of_induces {π : L →* C} (hπ : Function.Surjective π) {ψ : L →* G}
    {ψb : C →* G} (hval : ∀ y, ψb (π y) = ψ y) {x : G}
    (hxN : x ∈ Subgroup.normalizer (ψ.range : Set G)) {a : C}
    (hx : GGInduces π ψ x (MulAut.conj a)) : (x, a) ∈ ggConjPairs ψb := by
  rw [mem_ggConjPairs]
  intro u
  obtain ⟨y, rfl⟩ := hπ u
  obtain ⟨y', hy'⟩ := exists_conj_eq hxN y
  have h1 := hx y y' hy'
  rw [MulAut.conj_apply] at h1
  rw [← h1, hval, hval, hy']

theorem mem_ggConjPairs_of_induces_conj {π : L →* C} (hπker : π.ker ≤ Subgroup.center L)
    {ψ : L →* G} (hkψ : ψ.ker ≤ π.ker) (hperf : commutator ↥ψ.range = ⊤) {x : G}
    (hxN : x ∈ Subgroup.normalizer (ψ.range : Set G)) {s : L}
    (hx : GGInduces π ψ x (MulAut.conj (π s))) : (x, s) ∈ ggConjPairs ψ := by
  have hsN : (ψ s)⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) :=
    inv_mem (Subgroup.le_normalizer ⟨s, rfl⟩)
  have hw : GGInduces π ψ (x * (ψ s)⁻¹) 1 := by
    have h := hx.mul hsN (GGInduces.psi hkψ s).inv
    rwa [mul_inv_cancel] at h
  have hwC := mem_centralizer_of_induces_one hπker hperf (mul_mem hxN hsN) hw
  rw [mem_ggConjPairs]
  intro u
  have h := Subgroup.mem_centralizer_iff.mp hwC (ψ (s * u * s⁻¹)) ⟨_, rfl⟩
  calc ψ (s * u * s⁻¹) = ψ (s * u * s⁻¹) * (x * (ψ s)⁻¹) * (x * (ψ s)⁻¹)⁻¹ := by group
    _ = x * (ψ s)⁻¹ * ψ (s * u * s⁻¹) * (x * (ψ s)⁻¹)⁻¹ := by rw [h]
    _ = x * ψ u * x⁻¹ := by rw [map_mul, map_mul, map_inv]; group

theorem commutator_mem_center_of_pairs {ψ : L →* G} (hinj : Function.Injective ψ) {x y : G}
    {s t : L} (hxy : x * y = y * x) (hs : (x, s) ∈ ggConjPairs ψ)
    (ht : (y, t) ∈ ggConjPairs ψ) : s * t * s⁻¹ * t⁻¹ ∈ Subgroup.center L := by
  have h := (ggConjPairs ψ).mul_mem ((ggConjPairs ψ).mul_mem ((ggConjPairs ψ).mul_mem hs ht)
    ((ggConjPairs ψ).inv_mem hs)) ((ggConjPairs ψ).inv_mem ht)
  have e : (x, s) * (y, t) * (x, s)⁻¹ * (y, t)⁻¹ = ((1 : G), s * t * s⁻¹ * t⁻¹) := by
    refine Prod.ext ?_ rfl
    change x * y * x⁻¹ * y⁻¹ = 1
    rw [hxy]
    group
  rw [e] at h
  exact mem_center_of_mem_ggConjPairs_one hinj h

end Pairs

end ExcNonsplit

section Tags

theorem ExcNonsplit.exists_conj_of_innerDiag_E6 {k : Type} [Field k] [Finite k] [CharP k 2]
    {G : Type*} [Group G] (ψ : ↥(e6Data_valid.minGroup k) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k)) {c : G}
    (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G)) (hc : GGPsiInnerDiag (e6Datum k) ψ c)
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hcp : c ^ p = 1) :
    ∃ a : ↥(adjointGroup .E6 k), a ^ p = 1 ∧ GGInduces (e6Isogeny k) ψ c (MulAut.conj a) := by
  obtain ⟨α, hαD, hα⟩ := exists_induces_E6 ψ hker hcN hc
  have hkπ := ker_le_ker_e6Isogeny hker
  have hαp : α ^ p = 1 := by
    have h1 := hα.pow hkπ hcN p
    rw [hcp] at h1
    exact GGInduces.unique (e6Isogeny_surjective k) (Subgroup.one_mem _) h1 (GGInduces.one hkπ)
  obtain ⟨a, rfl⟩ : α ∈ inner ↥(adjointGroup .E6 k) :=
    ExcNonsplit.mem_inner_of_pow_eq_one (D := (rootDiagAutHom .E6 k).range)
      (by rintro _ ⟨a, rfl⟩; exact ExcNonsplit.rootDiagAutHom_pow_three_mem_inner_E6 a) hp hp3
      hαD hαp
  refine ⟨a, ?_, hα⟩
  have hZ : a ^ p ∈ Subgroup.center ↥(adjointGroup .E6 k) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 : MulAut.conj (a ^ p) g = g := by rw [map_pow, hαp, MulAut.one_apply]
    rw [MulAut.conj_apply] at h2
    calc g * a ^ p = a ^ p * g * (a ^ p)⁻¹ * a ^ p := by rw [h2]
      _ = a ^ p * g := by group
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hZ
  exact hZ

@[expose] def GGE6NonsplitCoreInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card K - 1 → ¬ p ∣ Nat.card K + 1 →
      ExcNonsplit.GGNonsplitCoreAt ↥(e6Data_valid.minGroup K) p ∧
        ExcNonsplit.GGNonsplitCoreAt ↥(adjointGroup .E6 K) p

theorem ExcNonsplit.exists_component_E6_of {k : Type} [Field k] [Finite k] [CharP k 2] {p : ℕ}
    (hcL : ExcNonsplit.GGNonsplitCoreAt ↥(e6Data_valid.minGroup k) p)
    (hcC : ExcNonsplit.GGNonsplitCoreAt ↥(adjointGroup .E6 k) p) {G : Type} [Group G]
    {ψ : ↥(e6Data_valid.minGroup k) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k))
    (hperf : commutator ↥ψ.range = ⊤) (hp : p.Prime) (hp3 : p ≠ 3) {x y : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x)
    (hxN : x ∈ Subgroup.normalizer (ψ.range : Set G))
    (hyN : y ∈ Subgroup.normalizer (ψ.range : Set G)) (hxD : GGPsiInnerDiag (e6Datum k) ψ x)
    (hyD : GGPsiInnerDiag (e6Datum k) ψ y) {K : Subgroup G}
    (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {x})) (hpK : ¬ p ∣ Nat.card K) :
    ∃ K' : Subgroup G, IsComponentOf K' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ K ≤ K' ∧
      ¬ GGNbrClauseFiveMarking p x K' := by
  obtain ⟨a, hap, hxa⟩ := ExcNonsplit.exists_conj_of_innerDiag_E6 ψ hker hxN hxD hp hp3 hx
  obtain ⟨b, hbp, hyb⟩ := ExcNonsplit.exists_conj_of_innerDiag_E6 ψ hker hyN hyD hp hp3 hy
  rcases ExcNonsplit.ker_eq_bot_or_center_E6 hker with hk1 | hkZ
  ·
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hk1
    have hπker := (CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center
      (K := k)).le
    have hkψ : ψ.ker ≤ (e6Isogeny k).ker := by
      rw [hk1]
      exact bot_le
    obtain ⟨s, hsp, hsa⟩ := ExcNonsplit.exists_lift_pow_eq_one_E6 hap hp hp3
    obtain ⟨t, htp, htb⟩ := ExcNonsplit.exists_lift_pow_eq_one_E6 hbp hp hp3
    have hs : (x, s) ∈ ggConjPairs ψ :=
      ExcNonsplit.mem_ggConjPairs_of_induces_conj hπker hkψ hperf hxN (by rw [hsa]; exact hxa)
    have ht : (y, t) ∈ ggConjPairs ψ :=
      ExcNonsplit.mem_ggConjPairs_of_induces_conj hπker hkψ hperf hyN (by rw [htb]; exact hyb)
    have hz := ExcNonsplit.commutator_mem_center_of_pairs hinj hxy hs ht
    have hst : s * t = t * s := ExcNonsplit.mul_comm_of_commutator_mem_center hp hp3 hsp hz
      (CFSG.ClassicalInvolution.ModelFacts.A2Isogeny.center_pow_three_e6 k hz)
    exact ExcNonsplit.exists_component_of_pairs hinj hcL hsp htp hst hs ht hK hpK
  ·
    obtain ⟨ψb, hinj, hval⟩ := ExcNonsplit.exists_factor_e6Isogeny hkZ
    have hrange : ψb.range = ψ.range := by
      ext g
      constructor
      · rintro ⟨c, rfl⟩
        obtain ⟨u, rfl⟩ := e6Isogeny_surjective k c
        exact ⟨u, (hval u).symm⟩
      · rintro ⟨u, rfl⟩
        exact ⟨_, hval u⟩
    have hs := ExcNonsplit.mem_ggConjPairs_of_induces (e6Isogeny_surjective k) hval hxN hxa
    have ht := ExcNonsplit.mem_ggConjPairs_of_induces (e6Isogeny_surjective k) hval hyN hyb
    rw [← hrange] at hK ⊢
    exact ExcNonsplit.exists_component_of_core center_adjointGroup_eq_bot hinj hcC hx hy hxy hs ht
      hK hpK

theorem ggNonsplitTag_E6_of_core (h : GGE6NonsplitCoreInput) : GGNonsplitTag .E6 := by
  refine ⟨fun G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy hxN hyN hxD hyD K hK hpK => ?_,
    fun G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy hxN hyN hxD hyD K K' hK hpK hK' hKK'
      _ => ?_⟩
  all_goals
    obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, hperf, -⟩ := hpres
    subst hrange
    have hF : Nat.card (GaloisField 2 f) = 2 ^ f :=
      GaloisField.card 2 f (by have := hadm.2.1; omega)
    have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
    obtain ⟨hcL, hcC⟩ := h (GaloisField 2 f) p hp hp2 (by rwa [hF]) (by rwa [hF])
    obtain ⟨K'', hK'', hKK'', hm⟩ := ExcNonsplit.exists_component_E6_of (k := GaloisField 2 f)
      hcL hcC hker hperf hp hp3 hx hy hxy hxN hyN hxD hyD hK hpK
  · exact ⟨K'', hK'', hKK''⟩
  · obtain rfl := OmNonsplit.eq_of_isComponentOf_of_le hK' hK''
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).mp hK.2.2)
      hKK' hKK''
    exact hm

end Tags

section Assembly


theorem ggNonsplitRound8_of_excCoreSix (hF4 : GGExcNonsplitCoreInput .F4)
    (hE6 : GGE6NonsplitCoreInput) (hE7 : GGExcNonsplitCoreInput .E7)
    (hE8 : GGExcNonsplitCoreInput .E8) (hTwE6 : GGNonsplitTag .twistedE6) :
    GGNonsplitCompLiftRound8 ∧ GGNonsplitNbrMarkingRound8 :=
  ggNonsplitRound8_of_excCore hF4 hE7 hE8 (ggNonsplitTag_E6_of_core hE6) hTwE6

theorem ggSixLayerCXNonsplitInput_of_excCoreSix (hF4 : GGExcNonsplitCoreInput .F4)
    (hE6 : GGE6NonsplitCoreInput) (hE7 : GGExcNonsplitCoreInput .E7)
    (hE8 : GGExcNonsplitCoreInput .E8) (hTwE6 : GGNonsplitTag .twistedE6) :
    GGSixLayerCXNonsplitInput :=
  ggSixLayerCXNonsplitInput_of_excCore hF4 hE7 hE8 (ggNonsplitTag_E6_of_core hE6) hTwE6

end Assembly

end CFSG.StandardType
