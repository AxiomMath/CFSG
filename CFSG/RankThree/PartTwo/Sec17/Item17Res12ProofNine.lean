module

public import CFSG.RankThree.PartTwo.Sec3.AlternatingSLTwoLocalRank
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res12

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec3
open scoped IsMulCommutative commutatorElement

theorem exists_three_le_pRank_of_class_two {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) (hexp : ∀ x : P, x ^ p = 1)
    (hclass : commutator P ≤ Subgroup.center P)
    {E : Type*} [CommGroup E] [Finite E] (hE2 : ∀ a : E, a ^ 2 = 1) (hE8 : Nat.card E = 8)
    (ρ : E →* MulAut P) (hρ : Function.Injective ρ) {e₁ e₂ ez : E} (he₁ : e₁ ≠ 1)
    (hez : ez ≠ 1) {τ β₁ β₂ : MulAut P}
    (hτ₁ : ρ e₁ * τ = τ * ρ e₂) (hτ₂ : ρ e₂ * τ = τ * (ρ e₁ * ρ e₂))
    (hβ₁₁ : β₁ * ρ e₁ = ρ e₁ * β₁) (hβ₁₂ : β₁ * ρ e₂ = ρ e₂ * β₁)
    (hβ₂₁ : β₂ * ρ e₁ = ρ e₁ * β₂) (hβ₂₂ : β₂ * ρ e₂ = ρ e₂ * β₂)
    (hζ : β₁ * β₂ = ρ ez * β₂ * β₁) :
    ∃ g : E, g ≠ 1 ∧ 3 ≤ CFSG.pRank p (fixedSubgroupOf (ρ g)) := by
  classical
  by_contra hcon
  push Not at hcon
  have hp' : p.Prime := hp.out
  obtain ⟨hchar, hVcomm, hVexp, hVelem, d, hVcard, -⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient hP
  have : Finite (Additive (P ⧸ frattini P)) := inferInstanceAs (Finite (P ⧸ frattini P))
  have : FiniteDimensional (ZMod p) (Additive (P ⧸ frattini P)) := Module.Finite.of_finite
  let Elin : MulAut (P ⧸ frattini P) →* Module.End (ZMod p) (Additive (P ⧸ frattini P)) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap p
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hE : ∀ (σ : MulAut (P ⧸ frattini P)) (q : P ⧸ frattini P),
      Elin σ (Additive.ofMul q) = Additive.ofMul (σ q) := fun _ _ => rfl
  let q := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini P)
  have hq : ∀ (σ : MulAut P) (x : P), q σ (x : P ⧸ frattini P) = ((σ x : P) : P ⧸ frattini P) :=
    fun σ x => CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply _ σ x
  let ρW : MulAut P →* Module.End (ZMod p) (Additive (P ⧸ frattini P)) := Elin.comp q
  have hρW : ∀ (σ : MulAut P) (x : P), ρW σ (Additive.ofMul (x : P ⧸ frattini P)) =
      Additive.ofMul ((σ x : P) : P ⧸ frattini P) := fun σ x => by
    change Elin (q σ) _ = _
    rw [hE, hq]
  have hinv : ∀ σ (v : Additive (P ⧸ frattini P)), ρW σ⁻¹ (ρW σ v) = v := fun σ v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinj : ∀ σ, Function.Injective (ρW σ) := fun σ x y h => by
    rw [← hinv σ x, h, hinv σ y]
  have hdim : Module.finrank (ZMod p) (Additive (P ⧸ frattini P)) ≤ 4 := by
    have h8 := (class_two_eight_action_inverting_quotient hp2 hP hexp hclass hE2 hE8 ρ hρ
      (fun a ha => Nat.le_of_lt_succ (hcon a ha))).1
    have : Fintype (Additive (P ⧸ frattini P)) := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod p) (V := Additive (P ⧸ frattini P))
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
    have hrank := pRank_eq_of_isMulCommutative hp' hVexp hVcomm
      (k := Module.finrank (ZMod p) (Additive (P ⧸ frattini P))) hpow
    rw [← hrank]
    rcases h8 with h | h <;> omega
  have hσ₁ : ρW (ρ e₁) ≠ 1 := by
    intro h1
    have hρd : ρ e₁ ≠ 1 := fun h => he₁ (hρ (h.trans (map_one ρ).symm))
    have hord : orderOf (ρ e₁) = 2 := orderOf_eq_prime (by rw [← map_pow, hE2, map_one]) hρd
    apply hρd
    refine CFSG.OrderReductions.FrattiniAutomorphisms.prime_order_frattini_kernel_trivial 2
      (ρ e₁) hord (not_two_dvd_card_of_odd hp2 hP) ?_
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro x
    have h := congrArg (fun f : Module.End (ZMod p) (Additive (P ⧸ frattini P)) =>
      f (Additive.ofMul (x : P ⧸ frattini P))) h1
    simp only [hρW, Module.End.one_apply] at h
    exact congrArg Additive.toMul h
  have hsq : ∀ a : E, ρW (ρ a) * ρW (ρ a) = 1 := fun a => by
    rw [← map_mul, ← map_mul, ← pow_two, hE2, map_one, map_one]
  have h3 := three_le_finrank_eigenspace (σ₁ := ρW (ρ e₁)) (σ₂ := ρW (ρ e₂)) (τ := ρW τ)
    (β₁ := ρW β₁) (β₂ := ρW β₂) (ζ := ρW (ρ ez)) (two_ne_zero_zmod hp' hp2)
    (hsq e₁) (hsq e₂)
    (by rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm e₁ e₂])
    (by simpa only [map_mul] using congrArg ρW hτ₁)
    (by simpa only [map_mul] using congrArg ρW hτ₂) (hinj τ)
    (by simpa only [map_mul] using congrArg ρW hβ₁₁)
    (by simpa only [map_mul] using congrArg ρW hβ₁₂)
    (by simpa only [map_mul] using congrArg ρW hβ₂₁)
    (by simpa only [map_mul] using congrArg ρW hβ₂₂) (hinj β₁) (hinj β₂)
    (by simpa only [map_mul] using congrArg ρW hζ) hσ₁ hdim
  have h2 := finrank_eigenspace_le_two_of_pRank_le_two hp2 hP hexp hclass
    (σ := ρ ez) (by rw [← map_pow, hE2, map_one])
    (Nat.le_of_lt_succ (hcon ez hez)) (ρW (ρ ez)) (hρW (ρ ez))
  omega

theorem exists_three_le_pRank {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    {E : Type*} [CommGroup E] [Finite E] (hE2 : ∀ a : E, a ^ 2 = 1) (hE8 : Nat.card E = 8)
    (ρ : E →* MulAut P) (hρ : Function.Injective ρ) {e₁ e₂ ez : E} (he₁ : e₁ ≠ 1)
    (hez : ez ≠ 1) {τ β₁ β₂ : MulAut P}
    (hτ₁ : ρ e₁ * τ = τ * ρ e₂) (hτ₂ : ρ e₂ * τ = τ * (ρ e₁ * ρ e₂))
    (hβ₁₁ : β₁ * ρ e₁ = ρ e₁ * β₁) (hβ₁₂ : β₁ * ρ e₂ = ρ e₂ * β₁)
    (hβ₂₁ : β₂ * ρ e₁ = ρ e₁ * β₂) (hβ₂₂ : β₂ * ρ e₂ = ρ e₂ * β₂)
    (hζ : β₁ * β₂ = ρ ez * β₂ * β₁) :
    ∃ g : E, g ≠ 1 ∧ 3 ≤ CFSG.pRank p (fixedSubgroupOf (ρ g)) := by
  have hp' : p.Prime := hp.out
  have hp2 : p ≠ 2 := by omega
  have hnt : Nontrivial P := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton (MulAut P) := ⟨fun σ τ => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    exact he₁ (hρ (Subsingleton.elim _ _))
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hP
  set r := restrictCharacteristic D with hr
  let ρD := r.comp ρ
  have hρD : Function.Injective ρD := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hfixg : ρ g ∈ fixingSubgroup (MulAut P) (D : Set P) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      have h := congrArg (fun σ : MulAut D => ((σ ⟨y, hy⟩ : D) : P)) hg
      exact h
    obtain ⟨k, hk⟩ := hDfix ⟨ρ g, hfixg⟩
    have hk' : (ρ g) ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have h1 : orderOf (ρ g) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf (ρ g) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hE2, map_one])
    have hcop : Nat.Coprime (p ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes hp' Nat.prime_two).mpr hp2)
    have h1' := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact hρ ((orderOf_eq_one_iff.mp h1').trans (map_one ρ).symm)
  have hDp : IsPGroup p D := hP.to_subgroup D
  have hDexp' : ∀ x : D, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hDclass : commutator D ≤ Subgroup.center D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hxy : ⁅(x : P), (y : P)⁆ ∈ D ⊓ Subgroup.centralizer (D : Set P) :=
      hDcomm (Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _))
    have hcoe : ((⁅x, y⁆ : D) : P) = ⁅(x : P), (y : P)⁆ := by simp [commutatorElement_def]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]
    exact Subgroup.mem_centralizer_iff.mp hxy.2 w w.2
  have hmap : ∀ {σ₁ σ₂ σ₃ σ₄ : MulAut P}, σ₁ * σ₂ = σ₃ * σ₄ → r σ₁ * r σ₂ = r σ₃ * r σ₄ :=
    fun h => by rw [← map_mul, ← map_mul, h]
  have hmap₃ : ∀ {σ₁ σ₂ σ₃ σ₄ σ₅ : MulAut P}, σ₁ * σ₂ = σ₃ * (σ₄ * σ₅) →
      r σ₁ * r σ₂ = r σ₃ * (r σ₄ * r σ₅) :=
    fun h => by rw [← map_mul, ← map_mul, ← map_mul, h]
  have hmap₃' : ∀ {σ₁ σ₂ σ₃ σ₄ σ₅ : MulAut P}, σ₁ * σ₂ = σ₃ * σ₄ * σ₅ →
      r σ₁ * r σ₂ = r σ₃ * r σ₄ * r σ₅ :=
    fun h => by rw [← map_mul, ← map_mul, ← map_mul, h]
  obtain ⟨g, hg1, hgr⟩ := exists_three_le_pRank_of_class_two hp2 hDp hDexp' hDclass hE2 hE8 ρD
    hρD he₁ hez (τ := r τ) (β₁ := r β₁) (β₂ := r β₂) (hmap hτ₁) (hmap₃ hτ₂) (hmap hβ₁₁)
    (hmap hβ₁₂) (hmap hβ₂₁) (hmap hβ₂₂) (hmap₃' hζ)
  refine ⟨g, hg1, hgr.trans ?_⟩
  let f : fixedSubgroupOf (ρD g) →* fixedSubgroupOf (ρ g) :=
    (D.subtype.comp (fixedSubgroupOf (ρD g)).subtype).codRestrict _ fun x => by
      have hx := x.2
      rw [mem_fixedSubgroupOf] at hx ⊢
      exact congrArg Subtype.val hx
  have hf : Function.Injective f := fun x y h => by
    have h' : ((x : D) : P) = ((y : D) : P) :=
      congrArg (fun z : fixedSubgroupOf (ρ g) => (z : P)) h
    exact Subtype.ext (Subtype.ext h')
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_le_of_injective hp'.one_lt f hf

theorem three_le_localRank_of_elems {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {P : Subgroup G} (hP : IsPGroup p P)
    {E : Type*} [CommGroup E] [Finite E] (hE2 : ∀ a : E, a ^ 2 = 1) (hE8 : Nat.card E = 8)
    (φ : E →* Subgroup.normalizer (P : Set G))
    (hφ : ∀ e, (φ e : G) ∈ Subgroup.centralizer (P : Set G) → e = 1)
    {e₁ e₂ ez : E} (he₁ : e₁ ≠ 1) (hez : ez ≠ 1) {w b₁ b₂ : Subgroup.normalizer (P : Set G)}
    (hτ₁ : φ e₁ * w = w * φ e₂) (hτ₂ : φ e₂ * w = w * (φ e₁ * φ e₂))
    (hβ₁₁ : b₁ * φ e₁ = φ e₁ * b₁) (hβ₁₂ : b₁ * φ e₂ = φ e₂ * b₁)
    (hβ₂₁ : b₂ * φ e₁ = φ e₁ * b₂) (hβ₂₂ : b₂ * φ e₂ = φ e₂ * b₂)
    (hζ : b₁ * b₂ = φ ez * b₂ * b₁) :
    3 ≤ CFSG.Assembly.RankThreeEven.localRank p G := by
  have : Fact p.Prime := ⟨hp⟩
  set cn := P.normalizerMonoidHom with hcn
  let ρ : E →* MulAut P := cn.comp φ
  have hρapp : ∀ e (y : P), ((ρ e y : P) : G) = (φ e : G) * y * (φ e : G)⁻¹ := fun e y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro e he
    apply hφ e
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have h := congrArg (fun σ : MulAut P => ((σ ⟨y, hy⟩ : P) : G)) he
    simp only [hρapp, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hmap : ∀ {x₁ x₂ x₃ x₄ : Subgroup.normalizer (P : Set G)}, x₁ * x₂ = x₃ * x₄ →
      cn x₁ * cn x₂ = cn x₃ * cn x₄ := fun h => by rw [← map_mul, ← map_mul, h]
  have hmap₃ : ∀ {x₁ x₂ x₃ x₄ x₅ : Subgroup.normalizer (P : Set G)}, x₁ * x₂ = x₃ * (x₄ * x₅) →
      cn x₁ * cn x₂ = cn x₃ * (cn x₄ * cn x₅) :=
    fun h => by rw [← map_mul, ← map_mul, ← map_mul, h]
  have hmap₃' : ∀ {x₁ x₂ x₃ x₄ x₅ : Subgroup.normalizer (P : Set G)}, x₁ * x₂ = x₃ * x₄ * x₅ →
      cn x₁ * cn x₂ = cn x₃ * cn x₄ * cn x₅ :=
    fun h => by rw [← map_mul, ← map_mul, ← map_mul, h]
  obtain ⟨g, hg1, hgr⟩ := exists_three_le_pRank hp3 hP hE2 hE8 ρ hρ he₁ hez (τ := cn w)
    (β₁ := cn b₁) (β₂ := cn b₂) (hmap hτ₁) (hmap₃ hτ₂) (hmap hβ₁₁) (hmap hβ₁₂) (hmap hβ₂₁)
    (hmap hβ₂₂) (hmap₃' hζ)
  have hx1 : (φ g : G) ≠ 1 := fun h => hg1 (hφ g (by rw [h]; exact Subgroup.one_mem _))
  have hx2 : (φ g : G) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hE2, map_one, Subgroup.coe_one]
  let f : fixedSubgroupOf (ρ g) →* G := P.subtype.comp (fixedSubgroupOf (ρ g)).subtype
  have hf : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext h)
  have hfmap : (⊤ : Subgroup (fixedSubgroupOf (ρ g))).map f ≤
      P ⊓ Subgroup.centralizer ({(φ g : G)} : Set G) := by
    rintro _ ⟨y, -, rfl⟩
    have hy := y.2
    rw [mem_fixedSubgroupOf] at hy
    have h := congrArg Subtype.val hy
    rw [hρapp, mul_inv_eq_iff_eq_mul] at h
    exact Subgroup.mem_inf.mpr ⟨((y : P)).2,
      Subgroup.mem_centralizer_singleton_iff.mpr h.symm⟩
  have hle : 3 ≤ CFSG.Open.pRank p (P ⊓ Subgroup.centralizer ({(φ g : G)} : Set G)) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hgr
    exact hgr.trans ((CFSG.SectionRank.pRank_le_map hp.one_lt f hf ⊤).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt hfmap))
  obtain ⟨E', hE'H, hE', hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (P ⊓ Subgroup.centralizer ({(φ g : G)} : Set G))
  exact hle.trans (le_localRank_of_commute_involution hp.one_lt hx1 hx2 hE'.1 hE'.2
    (hE'H.trans inf_le_right) hcard)

section Four

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_mem_four {Z : Subgroup G} (hZ4 : Nat.card Z = 4) (hZ2 : ∀ u ∈ Z, u ^ 2 = 1)
    {x y : G} (hx : x ∈ Z) (hy : y ∈ Z) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) {u : G}
    (hu : u ∈ Z) : u = 1 ∨ u = x ∨ u = y ∨ u = x * y := by
  classical
  have : Fintype Z := Fintype.ofFinite _
  set x' : Z := ⟨x, hx⟩ with hx'
  set y' : Z := ⟨y, hy⟩ with hy'
  have hxy1 : x * y ≠ 1 := by
    intro h
    apply hxy
    have hx2 : x * x = 1 := by rw [← pow_two]; exact hZ2 x hx
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hx2]
  have hT : ({1, x', y', x' * y'} : Finset Z).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      apply hx1
      have h' : y = x * y := congrArg Subtype.val h
      calc x = x * y * y⁻¹ := by group
        _ = 1 := by rw [← h', mul_inv_cancel]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => hxy (congrArg Subtype.val h), fun h => hy1 ?_⟩
      have h' : x = x * y := congrArg Subtype.val h
      calc y = x⁻¹ * (x * y) := by group
        _ = 1 := by rw [← h', inv_mul_cancel]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hx1 (congrArg Subtype.val h).symm,
        fun h => hy1 (congrArg Subtype.val h).symm,
        fun h => hxy1 (congrArg Subtype.val h).symm⟩
  have huniv := Finset.eq_univ_of_card _ (hT.trans (by rw [← Nat.card_eq_fintype_card, hZ4]))
  have hu' : (⟨u, hu⟩ : Z) ∈ ({1, x', y', x' * y'} : Finset Z) := huniv ▸ Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu'
  rcases hu' with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

theorem eq_one_of_conj_eq {Z : Subgroup G} (hZ4 : Nat.card Z = 4) (hZ2 : ∀ u ∈ Z, u ^ 2 = 1)
    {w : G}
    (hwZ : w ∈ Subgroup.normalizer (Z : Set G)) (hw3 : w ^ 3 = 1) {d : G} (hd : d ∈ Z)
    (hwd : w * d * w⁻¹ ≠ d) {u : G} (hu : u ∈ Z) (hwu : w * u * w⁻¹ = u) : u = 1 := by
  by_contra hu1
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hwd (by group)
  have hdu : u ≠ d := fun h => hwd (h ▸ hwu)
  have hwdZ : w * d * w⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hwZ d).mp hd
  have hwd1 : w * d * w⁻¹ ≠ 1 := fun h => hd1 (by
    calc d = w⁻¹ * (w * d * w⁻¹) * w := by group
      _ = 1 := by rw [h]; group)
  have hwdu : w * d * w⁻¹ ≠ u := fun h => hdu (by
    calc u = w⁻¹ * u * w := by
          calc u = w⁻¹ * (w * u * w⁻¹) * w := by group
            _ = w⁻¹ * u * w := by rw [hwu]
      _ = w⁻¹ * (w * d * w⁻¹) * w := by rw [h]
      _ = d := by group)
  have hwd' : w * d * w⁻¹ = u * d := by
    rcases eq_of_mem_four hZ4 hZ2 hu hd hu1 hd1 hdu hwdZ with h | h | h | h
    · exact absurd h hwd1
    · exact absurd h hwdu
    · exact absurd h hwd
    · exact h
  have hu2 : u * u = 1 := by rw [← pow_two]; exact hZ2 u hu
  have hw1 : w * (u * d) * w⁻¹ = d := by
    calc w * (u * d) * w⁻¹ = (w * u * w⁻¹) * (w * d * w⁻¹) := by group
      _ = d := by rw [hwu, hwd', ← mul_assoc, hu2, one_mul]
  have hw3' : w * w * w = 1 := by rw [← pow_three', hw3]
  have : d = u * d := by
    calc d = (w * w * w) * d * (w * w * w)⁻¹ := by rw [hw3']; group
      _ = w * (w * (w * d * w⁻¹) * w⁻¹) * w⁻¹ := by group
      _ = u * d := by rw [hwd', hw1, hwd']
  exact hu1 (by
    calc u = u * d * d⁻¹ := by group
      _ = 1 := by rw [← this, mul_inv_cancel])

omit [Finite G] in
theorem conj_mem_centralizer {P : Subgroup G} {w g : G}
    (hw : w ∈ Subgroup.normalizer (P : Set G)) (hg : g ∈ Subgroup.centralizer (P : Set G)) :
    w * g * w⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro y hy
  have hy' : w⁻¹ * y * w ∈ P := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hw) y).mp hy
    simpa using this
  have h := hg _ hy'
  calc y * (w * g * w⁻¹) = w * ((w⁻¹ * y * w) * g) * w⁻¹ := by group
    _ = w * (g * (w⁻¹ * y * w)) * w⁻¹ := by rw [h]
    _ = w * g * w⁻¹ * y := by group

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {z y : G} (hz2 : z ^ 2 = 1) (hy : y ∈ Subgroup.zpowers z) :
    y = 1 ∨ y = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_ofNat, hz2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, hz2, one_zpow, one_mul, zpow_one]

end Four

theorem le_centralizer_or_mem_centralizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3)
    {P Z : Subgroup G} (hP : IsPGroup p P) (hZ4 : Nat.card Z = 4) (hZ2 : ∀ u ∈ Z, u ^ 2 = 1)
    (hZc : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u) (hZP : Z ≤ Subgroup.normalizer (P : Set G))
    {w z b₁ b₂ : G} (hwP : w ∈ Subgroup.normalizer (P : Set G))
    (hzP : z ∈ Subgroup.normalizer (P : Set G)) (hb₁P : b₁ ∈ Subgroup.normalizer (P : Set G))
    (hb₂P : b₂ ∈ Subgroup.normalizer (P : Set G)) (hwZ : w ∈ Subgroup.normalizer (Z : Set G))
    (hw3 : w ^ 3 = 1) {d : G} (hd : d ∈ Z) (hwd : w * d * w⁻¹ ≠ d) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hzZ : ∀ u ∈ Z, z * u = u * z) (hwz : w * z = z * w)
    (hb₁Z : ∀ u ∈ Z, b₁ * u = u * b₁) (hb₂Z : ∀ u ∈ Z, b₂ * u = u * b₂)
    (hb : b₁ * b₂ = z * b₂ * b₁) :
    Z ≤ Subgroup.centralizer (P : Set G) ∨ z ∈ Subgroup.centralizer (P : Set G) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hZC, hzC⟩ := hcon
  have hfix : ∀ u ∈ Z, w * u * w⁻¹ = u → u = 1 := fun u hu hwu =>
    eq_one_of_conj_eq hZ4 hZ2 hwZ hw3 hd hwd hu hwu
  have hwz' : w * z * w⁻¹ = z := by rw [hwz, mul_inv_cancel_right]
  have hZC' : ∀ x ∈ Z, x ≠ 1 → x ∉ Subgroup.centralizer (P : Set G) := by
    intro x hx hx1 hxC
    apply hZC
    have hwx : w * x * w⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hwZ x).mp hx
    have hwxC : w * x * w⁻¹ ∈ Subgroup.centralizer (P : Set G) := conj_mem_centralizer hwP hxC
    have hwx1 : w * x * w⁻¹ ≠ 1 := fun h => hx1 (by
      calc x = w⁻¹ * (w * x * w⁻¹) * w := by group
        _ = 1 := by rw [h]; group)
    have hwxx : x ≠ w * x * w⁻¹ := fun h => hx1 (hfix x hx h.symm)
    intro u hu
    rcases eq_of_mem_four hZ4 hZ2 hx hwx hx1 hwx1 hwxx hu with h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact hxC
    · rw [h]; exact hwxC
    · rw [h]; exact Subgroup.mul_mem _ hxC hwxC
  set Zz := Subgroup.zpowers z with hZz
  have : IsMulCommutative Z := ⟨⟨fun a b => Subtype.ext (hZc a a.2 b b.2)⟩⟩
  let : CommGroup Z := IsMulCommutative.instCommGroup
  let : CommGroup Zz := IsMulCommutative.instCommGroup
  have hcomm : ∀ (m : Z) (n : Zz), Commute (Z.subtype m) (Zz.subtype n) := by
    rintro ⟨m, hm⟩ ⟨n, hn⟩
    rcases eq_one_or_eq_of_mem_zpowers hz2 hn with rfl | rfl
    · exact Commute.one_right _
    · exact (hzZ m hm).symm
  set f : Z × Zz →* G := MonoidHom.noncommCoprod Z.subtype Zz.subtype hcomm with hfdef
  have hfapp : ∀ e : Z × Zz, f e = (e.1 : G) * (e.2 : G) := fun e => rfl
  have hfN : ∀ e, f e ∈ Subgroup.normalizer (P : Set G) := fun e => by
    rw [hfapp]
    refine Subgroup.mul_mem _ (hZP e.1.2) ?_
    rcases eq_one_or_eq_of_mem_zpowers hz2 e.2.2 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact hzP
  set φ : Z × Zz →* Subgroup.normalizer (P : Set G) := f.codRestrict _ hfN with hφdef
  have hφapp : ∀ e, (φ e : G) = (e.1 : G) * (e.2 : G) := fun e => rfl
  have hz : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hE8 : Nat.card (Z × Zz) = 8 := by
    rw [Nat.card_prod, hZ4, hZz, Nat.card_zpowers, hz]
  have hE2 : ∀ e : Z × Zz, e ^ 2 = 1 := by
    rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa using hZ2 m hm
    · rcases eq_one_or_eq_of_mem_zpowers hz2 hn with rfl | rfl
      · simp
      · simpa using hz2
  have hφ : ∀ e, (φ e : G) ∈ Subgroup.centralizer (P : Set G) → e = 1 := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ he
    rw [hφapp] at he
    simp only at he
    rcases eq_one_or_eq_of_mem_zpowers hz2 hy with rfl | rfl
    · rw [mul_one] at he
      have hx1 : x = 1 := by
        by_contra hx1
        exact hZC' x hx hx1 he
      subst hx1
      rfl
    · by_cases hx1 : x = 1
      · subst hx1
        rw [one_mul] at he
        exact absurd he hzC
      · exfalso
        have hwe := conj_mem_centralizer hwP he
        have hdiv := Subgroup.mul_mem _ (Subgroup.inv_mem _ he) hwe
        have hmem : x⁻¹ * (w * x * w⁻¹) ∈ Z :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) ((Subgroup.mem_normalizer_iff.mp hwZ x).mp hx)
        have heq : (x * y)⁻¹ * (w * (x * y) * w⁻¹) = x⁻¹ * (w * x * w⁻¹) := by
          have h1 : w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by group
          rw [h1, hwz', mul_inv_rev]
          calc y⁻¹ * x⁻¹ * (w * x * w⁻¹ * y) = y⁻¹ * ((x⁻¹ * (w * x * w⁻¹)) * y) := by group
            _ = y⁻¹ * (y * (x⁻¹ * (w * x * w⁻¹))) := by rw [← hzZ _ hmem]
            _ = x⁻¹ * (w * x * w⁻¹) := by group
        rw [heq] at hdiv
        have hne : x⁻¹ * (w * x * w⁻¹) ≠ 1 := fun h => hx1 (hfix x hx (by
          calc w * x * w⁻¹ = x * (x⁻¹ * (w * x * w⁻¹)) := by group
            _ = x := by rw [h, mul_one]))
        exact hZC' _ hmem hne hdiv
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hwd (by group)
  have hw3' : w * w * w = 1 := by rw [← pow_three', hw3]
  set d₂ := w⁻¹ * d * w with hd₂
  have hd₂Z : d₂ ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hwZ) d).mp hd
    simpa [hd₂] using this
  have hd₂1 : d₂ ≠ 1 := fun h => hd1 (by
    calc d = w * d₂ * w⁻¹ := by rw [hd₂]; group
      _ = 1 := by rw [h]; group)
  have hdd₂ : d ≠ d₂ := fun h => hwd (by
    calc w * d * w⁻¹ = w * d₂ * w⁻¹ := by rw [← h]
      _ = d := by rw [hd₂]; group)
  have hd₃ : w⁻¹ * d₂ * w = d * d₂ := by
    have hd₃Z : w⁻¹ * d₂ * w ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hwZ) d₂).mp hd₂Z
      simpa using this
    rcases eq_of_mem_four hZ4 hZ2 hd hd₂Z hd1 hd₂1 hdd₂ hd₃Z with h | h | h | h
    · exact absurd (by
        calc d₂ = w * (w⁻¹ * d₂ * w) * w⁻¹ := by group
          _ = 1 := by rw [h]; group) hd₂1
    · exfalso
      apply hwd
      calc w * d * w⁻¹ = w * (w⁻¹ * d₂ * w) * w⁻¹ := by rw [h]
        _ = d₂ := by group
        _ = w⁻¹ * (w⁻¹ * d₂ * w) * w := by rw [h]
        _ = w⁻¹ * (w⁻¹ * (w⁻¹ * d * w) * w) * w := by rw [hd₂]
        _ = (w * w * w)⁻¹ * d * (w * w * w) := by group
        _ = d := by rw [hw3']; group
    · exfalso
      apply hd₂1
      refine hfix d₂ hd₂Z ?_
      calc w * d₂ * w⁻¹ = w * (w⁻¹ * d₂ * w) * w⁻¹ := by rw [h]
        _ = d₂ := by group
    · exact h
  set e₁ : Z × Zz := (⟨d, hd⟩, 1) with he₁def
  set e₂ : Z × Zz := (⟨d₂, hd₂Z⟩, 1) with he₂def
  set ez : Z × Zz := (1, ⟨z, Subgroup.mem_zpowers z⟩) with hezdef
  have he₁ : e₁ ≠ 1 := fun h => hd1 (congrArg (fun e : Z × Zz => (e.1 : G)) h)
  have hez : ez ≠ 1 := fun h => hz1 (congrArg (fun e : Z × Zz => (e.2 : G)) h)
  have hφ₁ : (φ e₁ : G) = d := by rw [hφapp]; simp [he₁def]
  have hφ₂ : (φ e₂ : G) = d₂ := by rw [hφapp]; simp [he₂def]
  have hφz : (φ ez : G) = z := by rw [hφapp]; simp [hezdef]
  refine (not_le.mpr hloc) (three_le_localRank_of_elems hp hp3 hP hE2 hE8 φ hφ he₁ hez
    (e₂ := e₂) (w := ⟨w, hwP⟩) (b₁ := ⟨b₁, hb₁P⟩) (b₂ := ⟨b₂, hb₂P⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hφ₁, hφ₂]
    rw [hd₂]
    group
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hφ₁, hφ₂]
    rw [← hd₃]
    group
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hφ₁]
    exact hb₁Z d hd
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hφ₂]
    exact hb₁Z d₂ hd₂Z
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hφ₁]
    exact hb₂Z d hd
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hφ₂]
    exact hb₂Z d₂ hd₂Z
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hφz]
    exact hb

end CFSG.RankThree.PartTwo.Sec17.Proof17Res12
