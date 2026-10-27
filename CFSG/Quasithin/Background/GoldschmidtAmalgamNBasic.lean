module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS4
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Transfer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

universe u

namespace CFSG.Quasithin.F6.GoldAmN

open Subgroup

theorem card_modEq_card_inf_centralizer {D : Type*} [Group D] (Q : Subgroup D) [Finite Q]
    {x : D} (hx : x ^ 3 = 1) (hnorm : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) :
    Nat.card Q ≡ Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set D)) [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype Q := Fintype.ofFinite Q
  let f : Function.End Q := fun q => ⟨x * q * x⁻¹, hnorm q q.2⟩
  have hpow : ∀ (n : ℕ) (q : Q), ((f ^ n : Function.End Q) q : D) = x ^ n * q * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro q
      show (q : D) = x ^ 0 * q * (x ^ 0)⁻¹
      simp
    | succ n ih =>
      intro q
      rw [pow_succ]
      show (((f ^ n) (f q) : Q) : D) = _
      rw [ih]
      show x ^ n * (x * (q : D) * x⁻¹) * (x ^ n)⁻¹ = _
      group
  have hf : f ^ 3 ^ 1 = 1 := by
    funext q
    apply Subtype.ext
    rw [hpow]
    show x ^ 3 ^ 1 * (q : D) * (x ^ 3 ^ 1)⁻¹ = (q : D)
    simp [hx]
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf
  have : Finite ↥(Q ⊓ Subgroup.centralizer ({x} : Set D)) :=
    Finite.of_injective
      (Subgroup.inclusion (inf_le_left : Q ⊓ Subgroup.centralizer ({x} : Set D) ≤ Q))
      (Subgroup.inclusion_injective _)
  have : Fintype ↥(Q ⊓ Subgroup.centralizer ({x} : Set D)) := Fintype.ofFinite _
  have hcard : Fintype.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set D)) =
      Fintype.card ↑(Function.fixedPoints f) := by
    refine Fintype.card_congr
      { toFun := fun q => ⟨⟨q.1, q.2.1⟩, ?_⟩
        invFun := fun q => ⟨q.1.1, q.1.2, ?_⟩
        left_inv := fun q => rfl
        right_inv := fun q => rfl }
    · apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp q.2.2 x (Set.mem_singleton x)
      show x * (q : D) * x⁻¹ = q
      rw [this]
      group
    · have := q.2
      have h2 : x * (q.1 : D) * x⁻¹ = q.1 := congrArg Subtype.val this
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      calc g * (q.1 : D) = g * q.1 * g⁻¹ * g := by group
        _ = q.1 * g := by rw [h2]
  rw [Nat.card_eq_fintype_card (α := Q)]
  rw [Nat.card_eq_fintype_card (α := ↥(Q ⊓ Subgroup.centralizer ({x} : Set D)))]
  rw [hcard]
  exact h

theorem nonempty_mulEquiv_perm_of_normalCore_eq_bot {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) {n : ℕ} (hn : H.index = n) (hcore : H.normalCore = ⊥)
    (hcard : Nat.card G = n.factorial) : Nonempty (G ≃* Equiv.Perm (Fin n)) := by
  classical
  have hq : Nat.card (G ⧸ H) = n := by rw [← hn]; rfl
  let e : G ⧸ H ≃ Fin n := Finite.equivFinOfCardEq hq
  let ψ : G →* Equiv.Perm (Fin n) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr ?_
    intro g hg
    have h1 : MulAction.toPermHom G (G ⧸ H) g = 1 := by
      apply (Equiv.permCongrHom e).injective
      rw [map_one]
      exact hg
    have : g ∈ (MulAction.toPermHom G (G ⧸ H)).ker := h1
    rw [← Subgroup.normalCore_eq_ker, hcore] at this
    exact this
  have hcard' : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  exact ⟨MulEquiv.ofBijective ψ (hinj.bijective_of_nat_card_le (by rw [hcard, hcard']))⟩

theorem isKleinFour_of_card_eq_four {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem nonempty_mulEquiv_klein {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) :
    Nonempty (H ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have : IsKleinFour H := isKleinFour_of_card_eq_four h4 hsq
  have : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    isKleinFour_of_card_eq_four (by simp) (by
      intro x
      obtain ⟨a, b⟩ := x
      have ha : ∀ a : Multiplicative (ZMod 2), a ^ 2 = 1 := by decide
      exact Prod.ext (ha a) (ha b))
  exact IsKleinFour.nonempty_mulEquiv

theorem nonempty_mulEquiv_klein_subgroup {D : Type*} [Group D] (V : Subgroup D)
    (h4 : Nat.card V = 4) (hsq : ∀ v ∈ V, v ^ 2 = 1) :
    Nonempty (↥V ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  nonempty_mulEquiv_klein h4 (fun x => Subtype.ext (hsq x x.2))

theorem eq_one_of_mem_centralizer_of_card_four {G : Type*} [Group G] [Finite G] (V : Subgroup G)
    [V.Normal] (hV : Nat.card V = 4) {x : G} (hx : orderOf x = 3)
    (hnc : ¬ ∀ v ∈ V, x * v = v * x) {v : G} (hv : v ∈ V) (hxv : x * v = v * x) : v = 1 := by
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := card_modEq_card_inf_centralizer V hx3 (fun q hq => by
    simpa using (inferInstance : V.Normal).conj_mem q hq x)
  set F := V ⊓ Subgroup.centralizer ({x} : Set G) with hF
  have hFle : F ≤ V := inf_le_left
  have hdvd : Nat.card F ∣ 4 := hV ▸ Subgroup.card_dvd_of_le hFle
  have hFcard : Nat.card F = 1 := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4] at hdvd
    obtain ⟨i, hi, hFi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hV, hFi] at hmod
    interval_cases i
    · simpa using hFi
    · exfalso; revert hmod; decide
    · exfalso
      have hFV : F = V := Subgroup.eq_of_le_of_card_ge hFle (by rw [hV, hFi]; norm_num)
      apply hnc
      intro w hw
      have : w ∈ F := by rw [hFV]; exact hw
      exact (Subgroup.mem_centralizer_iff.mp this.2) x (Set.mem_singleton x)
  have hFbot : F = ⊥ := Subgroup.eq_bot_of_card_eq F hFcard
  have hvF : v ∈ F := ⟨hv, Subgroup.mem_centralizer_iff.mpr (by
    intro g hg; rw [Set.mem_singleton_iff] at hg; subst hg; exact hxv)⟩
  rw [hFbot] at hvF
  exact hvF

theorem nonempty_mulEquiv_perm_four_of_normal {G : Type*} [Group G] [Finite G] (V : Subgroup G)
    [V.Normal] (hV : Nat.card V = 4) (hsq : ∀ v ∈ V, v ^ 2 = 1)
    (hC : ∀ g : G, (∀ v ∈ V, g * v = v * g) → g ∈ V) (hG : Nat.card G = 24) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hG]; norm_num)
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hnc : ¬ ∀ v ∈ V, x * v = v * x := by
    intro h
    have hxV : x ∈ V := hC x h
    have := orderOf_dvd_natCard (⟨x, hxV⟩ : V)
    rw [Subgroup.orderOf_mk, hx, hV] at this
    omega
  have hfpf : ∀ v ∈ V, x * v = v * x → v = 1 := fun v hv hxv =>
    eq_one_of_mem_centralizer_of_card_four V hV hx hnc hv hxv
  have hPV : ∀ z ∈ Subgroup.zpowers x, z ∈ V → z = 1 := by
    intro z hz hzV
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h3 : (x ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [hx3]
    have h2 := hsq _ hzV
    calc x ^ k = (x ^ k) ^ 3 * ((x ^ k) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  have hNV : ∀ v ∈ V, v ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) → v = 1 := by
    intro v hv hvN
    have hxP : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    have hvx : v * x * v⁻¹ ∈ Subgroup.zpowers x :=
      (Subgroup.mem_normalizer_iff.mp hvN x).mp hxP
    have hc1 : v * x * v⁻¹ * x⁻¹ ∈ Subgroup.zpowers x :=
      Subgroup.mul_mem _ hvx (Subgroup.inv_mem _ hxP)
    have hc2 : v * x * v⁻¹ * x⁻¹ ∈ V := by
      have : v * (x * v⁻¹ * x⁻¹) ∈ V :=
        V.mul_mem hv ((inferInstance : V.Normal).conj_mem _ (V.inv_mem hv) x)
      simpa [mul_assoc] using this
    have hc := hPV _ hc1 hc2
    apply hfpf v hv
    have : v * x * v⁻¹ = x := by
      have := congrArg (· * x) hc
      simpa [mul_assoc] using this
    calc x * v = (v * x * v⁻¹) * v := by rw [this]
      _ = v * x := by group
  have hPcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hPi : (Subgroup.zpowers x).index = 8 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hPcard, hG] at this
    omega
  have hPidx : ¬ 3 ∣ (Subgroup.zpowers x).index := by rw [hPi]; omega
  let P : Sylow 3 G :=
    (IsPGroup.of_card (p := 3) (n := 1) (by rw [hPcard, pow_one])).toSylow hPidx
  have hn3 : Subgroup.index (Subgroup.normalizer (Subgroup.zpowers x : Set G)) = 4 := by
    have h0 : Nat.card (Sylow 3 G) =
        (Subgroup.normalizer (Subgroup.zpowers x : Set G)).index :=
      Sylow.card_eq_index_normalizer P
    rw [← h0]
    have h1 := card_sylow_modEq_one 3 G
    have h2 : Nat.card (Sylow 3 G) ∣ (Subgroup.zpowers x).index := Sylow.card_dvd_index P
    rw [hPi] at h2
    have hle : Nat.card (Sylow 3 G) ≤ 8 := Nat.le_of_dvd (by norm_num) h2
    have hne : Nat.card (Sylow 3 G) ≠ 1 := by
      intro h1'
      have hid : Subgroup.index (Subgroup.normalizer (Subgroup.zpowers x : Set G)) = 1 := by
        rw [← h0]; exact h1'
      have htop := Subgroup.index_eq_one.mp hid
      have hVbot : V = ⊥ := by
        rw [eq_bot_iff]
        intro v hv
        rw [Subgroup.mem_bot]
        exact hNV v hv (by rw [htop]; exact Subgroup.mem_top v)
      rw [hVbot] at hV
      simp at hV
    interval_cases h : Nat.card (Sylow 3 G)
    · exact absurd h1 (by decide)
    · exact absurd rfl hne
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide)
    · rfl
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)
    · exact absurd h1 (by decide)
  refine nonempty_mulEquiv_perm_of_normalCore_eq_bot
    (Subgroup.normalizer (Subgroup.zpowers x : Set G)) hn3 ?_ (by rw [hG]; decide)
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  have hKbot : ∀ w ∈ (Subgroup.normalizer (Subgroup.zpowers x : Set G)).normalCore, w ∈ V →
      w = 1 := fun w hw hwV => hNV w hwV (Subgroup.normalCore_le _ hw)
  have hkV : k ∈ V := by
    apply hC
    intro v hv
    have hcK : k * v * k⁻¹ * v⁻¹ ∈
        (Subgroup.normalizer (Subgroup.zpowers x : Set G)).normalCore := by
      have : k * (v * k⁻¹ * v⁻¹) ∈
          (Subgroup.normalizer (Subgroup.zpowers x : Set G)).normalCore :=
        Subgroup.mul_mem _ hk
          ((Subgroup.normalCore_normal _).conj_mem _ (Subgroup.inv_mem _ hk) v)
      simpa [mul_assoc] using this
    have hcV : k * v * k⁻¹ * v⁻¹ ∈ V := by
      have : (k * v * k⁻¹) * v⁻¹ ∈ V :=
        V.mul_mem ((inferInstance : V.Normal).conj_mem v hv k) (V.inv_mem hv)
      exact this
    have := hKbot _ hcK hcV
    calc k * v = (k * v * k⁻¹ * v⁻¹) * v * k := by group
      _ = v * k := by rw [this]; simp
  exact hKbot k hk hkV

theorem nonempty_mulEquiv_perm_four {D : Type*} [Group D] (K V : Subgroup D) [Finite K]
    (hVK : V ≤ K) (hnorm : K ≤ Subgroup.normalizer (V : Set D)) (hV : Nat.card V = 4)
    (hsq : ∀ v ∈ V, v ^ 2 = 1) (hC : ∀ g ∈ K, (∀ v ∈ V, g * v = v * g) → g ∈ V)
    (hK : Nat.card K = 24) : Nonempty (↥K ≃* Equiv.Perm (Fin 4)) := by
  have hN : (V.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).mpr hnorm
  refine nonempty_mulEquiv_perm_four_of_normal (V.subgroupOf K) ?_ ?_ ?_ hK
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hV]
  · intro v hv
    exact Subtype.ext (hsq v hv)
  · intro g hg
    have := hC g g.2 (fun v hv => by
      have := hg ⟨v, hVK hv⟩ hv
      exact congrArg Subtype.val this)
    exact this

theorem nonempty_mulEquiv_dihedral_four {D : Type*} [Group D] (K A : Subgroup D) (hAK : A ≤ K)
    (e : ↥K ≃* Equiv.Perm (Fin 4)) (hA : Nat.card A = 8) :
    Nonempty (↥A ≃* DihedralGroup 4) := by
  let A' : Subgroup ↥K := A.subgroupOf K
  let P : Subgroup (Equiv.Perm (Fin 4)) := A'.map e.toMonoidHom
  have hA' : Nat.card A' = 8 := by
    rw [← hA]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hP : Nat.card P = 8 := by
    rw [← hA']
    exact Nat.card_congr (A'.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm
  obtain ⟨f⟩ := CFSG.QuasithinUnique.AppC.exists_mulEquiv_dihedral hP
  exact ⟨((Subgroup.subgroupOfEquivOfLe hAK).symm.trans
    (A'.equivMapOfInjective e.toMonoidHom e.injective)).trans f.symm⟩

theorem nonempty_mulEquiv_dihedral_of_card {G : Type*} [Group G] [Finite G] {ρ σ : G} {n : ℕ}
    (hρ : orderOf ρ = n) (hσ : σ ^ 2 = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹)
    (hnot : σ ∉ Subgroup.zpowers ρ) (hcard : Nat.card G = 2 * n) :
    Nonempty (G ≃* DihedralGroup n) := by
  have hn : 0 < n := by rw [← hρ]; exact orderOf_pos ρ
  have hA : Nat.card (Subgroup.zpowers ρ) = n := by rw [Nat.card_zpowers, hρ]
  have hAi : (Subgroup.zpowers ρ).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers ρ)
    rw [hA, hcard] at this
    exact Nat.eq_of_mul_eq_mul_left hn (by rw [this]; ring)
  have hKtop : Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ = ⊤ := by
    have hdvd : (Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ).index ∣ 2 :=
      hAi ▸ Subgroup.index_dvd_of_le le_sup_left
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      have hmul := Subgroup.relIndex_mul_index
        (le_sup_left : Subgroup.zpowers ρ ≤ Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ)
      rw [hAi, h2] at hmul
      have hrel1 : (Subgroup.zpowers ρ).relIndex
          (Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) = 1 := by omega
      have hle := Subgroup.relIndex_eq_one.mp hrel1
      exact hnot (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)))
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hKtop.symm hσ hrel hnot
  rw [hρ] at e
  exact ⟨e⟩

theorem nonempty_mulEquiv_dihedral_of_mem {D : Type*} [Group D] (H : Subgroup D) [Finite H]
    {ρ σ : D} {n : ℕ} (hρH : ρ ∈ H) (hσH : σ ∈ H) (hρ : orderOf ρ = n) (hσ : σ ^ 2 = 1)
    (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (hnot : σ ∉ Subgroup.zpowers ρ) (hcard : Nat.card H = 2 * n) :
    Nonempty (↥H ≃* DihedralGroup n) := by
  refine nonempty_mulEquiv_dihedral_of_card (ρ := (⟨ρ, hρH⟩ : H)) (σ := (⟨σ, hσH⟩ : H)) ?_ ?_ ?_
    ?_ hcard
  · rw [Subgroup.orderOf_mk, hρ]
  · exact Subtype.ext hσ
  · exact Subtype.ext (by simpa using hrel)
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hnot
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this

theorem nonempty_mulEquiv_perm_three {G : Type*} [Group G] [Finite G] {x σ : G}
    (hx : orderOf x = 3) (hσ : σ ^ 2 = 1) (hrel : σ * x * σ⁻¹ = x⁻¹)
    (hcard : Nat.card G = 6) : Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxne : x ≠ x⁻¹ := by
    intro h
    have h2 : x ^ 2 = 1 := by
      have : x * x = 1 := by
        calc x * x = x * x⁻¹ := by rw [← h]
          _ = 1 := by simp
      simpa [pow_two] using this
    have : x = 1 := by
      calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
        _ = 1 := by rw [hx3, h2]; simp
    rw [this] at hx
    simp at hx
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h] at hrel
    apply hxne
    simpa using hrel
  have hσo : orderOf σ = 2 := by
    have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one hσ
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσ1
    · exact h
  have hHcard : Nat.card (Subgroup.zpowers σ) = 2 := by rw [Nat.card_zpowers, hσo]
  have hHi : (Subgroup.zpowers σ).index = 3 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers σ)
    rw [hHcard, hcard] at this
    omega
  have hz : ∀ z ∈ Subgroup.zpowers σ, z = 1 ∨ z = σ := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h2 : σ ^ k = σ ^ (k % 2) := by
      rw [← zpow_mod_orderOf, hσo]
      rfl
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [h2, h]; simp
    · right; rw [h2, h]; simp
  refine nonempty_mulEquiv_perm_of_normalCore_eq_bot (Subgroup.zpowers σ) hHi ?_
    (by rw [hcard]; decide)
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  have hcH : c ∈ Subgroup.zpowers σ := Subgroup.normalCore_le _ hc
  rcases hz c hcH with h | h
  · exact h
  · exfalso
    rw [h] at hc
    have hc' : x * σ * x⁻¹ ∈ (Subgroup.zpowers σ).normalCore :=
      (Subgroup.normalCore_normal _).conj_mem _ hc x
    rcases hz _ (Subgroup.normalCore_le _ hc') with h1 | h1
    · apply hσ1
      have := congrArg (fun y => x⁻¹ * y * x) h1
      simpa [mul_assoc] using this
    · apply hxne
      have h3 : x * σ = σ * x := by
        calc x * σ = x * σ * x⁻¹ * x := by group
          _ = σ * x := by rw [h1]
      have h4 : σ * x * σ⁻¹ = x := by
        calc σ * x * σ⁻¹ = x * σ * σ⁻¹ := by rw [← h3]
          _ = x := by group
      exact h4.symm.trans hrel

theorem nonempty_mulEquiv_quotient_of_complement {G : Type*} [Group G] [Finite G]
    (N C : Subgroup G) [N.Normal] (hdisj : C ⊓ N = ⊥)
    (hcard : Nat.card G = Nat.card C * Nat.card N) : Nonempty (↥C ≃* G ⧸ N) := by
  let φ : ↥C →* G ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).mpr ?_
    intro c hc
    have h1 : (c : G) ∈ N := (QuotientGroup.eq_one_iff (c : G)).mp hc
    have h2 : (c : G) ∈ C ⊓ N := ⟨c.2, h1⟩
    rw [hdisj, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hpos : 0 < Nat.card N := Nat.card_pos
  have h2 : Nat.card (G ⧸ N) = Nat.card C := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← h1, hcard]
  exact ⟨MulEquiv.ofBijective φ (hinj.bijective_of_nat_card_le (by rw [h2]))⟩

theorem nonempty_mulEquiv_of_complements {D : Type*} [Group D] (T N C₁ C₂ : Subgroup D)
    [Finite T] (hN : N ≤ T) (hC₁ : C₁ ≤ T) (hC₂ : C₂ ≤ T)
    (hnorm : T ≤ Subgroup.normalizer (N : Set D)) (hd₁ : C₁ ⊓ N = ⊥) (hd₂ : C₂ ⊓ N = ⊥)
    (h₁ : Nat.card T = Nat.card C₁ * Nat.card N) (h₂ : Nat.card T = Nat.card C₂ * Nat.card N) :
    Nonempty (↥C₁ ≃* ↥C₂) := by
  have hNn : (N.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hnorm
  have hcardN : Nat.card (N.subgroupOf T) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
  have key : ∀ C : Subgroup D, C ≤ T → C ⊓ N = ⊥ → Nat.card T = Nat.card C * Nat.card N →
      Nonempty (↥C ≃* ↥T ⧸ N.subgroupOf T) := by
    intro C hC hd h
    have hcardC : Nat.card (C.subgroupOf T) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv
    have hd' : C.subgroupOf T ⊓ N.subgroupOf T = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxC, hxN⟩
      have : (x : D) ∈ C ⊓ N := ⟨hxC, hxN⟩
      rw [hd, Subgroup.mem_bot] at this
      exact Subtype.ext this
    obtain ⟨e⟩ := nonempty_mulEquiv_quotient_of_complement (N.subgroupOf T) (C.subgroupOf T) hd'
      (by rw [hcardC, hcardN]; exact h)
    exact ⟨(Subgroup.subgroupOfEquivOfLe hC).symm.trans e⟩
  obtain ⟨e₁⟩ := key C₁ hC₁ hd₁ h₁
  obtain ⟨e₂⟩ := key C₂ hC₂ hd₂ h₂
  exact ⟨e₁.trans e₂.symm⟩

theorem nonempty_mulEquiv_prod_of_sup_eq {D : Type*} [Group D] (H A B : Subgroup D)
    (hA : A ≤ H) (hB : B ≤ H) (hsup : A ⊔ B = H) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisj : A ⊓ B = ⊥) : Nonempty (↥H ≃* ↥A × ↥B) := by
  let φ : ↥A × ↥B →* ↥H := (Subgroup.inclusion hA).noncommCoprod (Subgroup.inclusion hB)
    (fun a b => Subtype.ext (hcomm a a.2 b b.2))
  have hφ : ∀ p : ↥A × ↥B, (φ p : D) = (p.1 : D) * (p.2 : D) := fun p => rfl
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).mpr ?_
    rintro ⟨a, b⟩ h
    have h1 : (a : D) * (b : D) = 1 := (hφ (a, b)).symm.trans (congrArg Subtype.val h)
    have h2 : (a : D) = (b : D)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (a : D) ∈ A ⊓ B := ⟨a.2, by rw [h2]; exact B.inv_mem b.2⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    have h4 : (b : D) = 1 := by
      rw [h3] at h1
      simpa using h1
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  have hsurj : Function.Surjective φ := by
    have hRA : A ≤ (φ.range).map H.subtype := fun a ha =>
      ⟨⟨a, hA ha⟩, ⟨(⟨a, ha⟩, 1), Subtype.ext (by simp [hφ])⟩, rfl⟩
    have hRB : B ≤ (φ.range).map H.subtype := fun b hb =>
      ⟨⟨b, hB hb⟩, ⟨(1, ⟨b, hb⟩), Subtype.ext (by simp [hφ])⟩, rfl⟩
    intro h
    have hmem : (h : D) ∈ (φ.range).map H.subtype := by
      have := sup_le hRA hRB
      rw [hsup] at this
      exact this h.2
    obtain ⟨r, ⟨p, hp⟩, hr⟩ := hmem
    exact ⟨p, hp.trans (Subtype.ext hr)⟩
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

theorem sup_zpowers_eq_of_relIndex_two {D : Type*} [Group D] {H T : Subgroup D} {z : D}
    (hHT : H ≤ T) (h2 : H.relIndex T = 2) (hzT : z ∈ T) (hzH : z ∉ H) :
    H ⊔ Subgroup.zpowers z = T := by
  have hS : H ⊔ Subgroup.zpowers z ≤ T := sup_le hHT ((Subgroup.zpowers_le).mpr hzT)
  have hmul := Subgroup.relIndex_mul_relIndex H (H ⊔ Subgroup.zpowers z) T le_sup_left hS
  rw [h2] at hmul
  have hne : H.relIndex (H ⊔ Subgroup.zpowers z) ≠ 1 := by
    intro h1
    exact hzH ((Subgroup.relIndex_eq_one.mp h1) (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)))
  have hdvd' : H.relIndex (H ⊔ Subgroup.zpowers z) ∣ 2 := Dvd.intro _ hmul
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd' with h | h
  · exact absurd h hne
  · have hT1 : (H ⊔ Subgroup.zpowers z).relIndex T = 1 := by
      rw [h] at hmul; omega
    exact le_antisymm hS (Subgroup.relIndex_eq_one.mp hT1)

theorem card_sup_le_of_le_normalizer {D : Type*} [Group D] (H N : Subgroup D) [Finite H] [Finite N]
    (hLE : H ≤ Subgroup.normalizer (N : Set D)) :
    Nat.card ↥(H ⊔ N) ≤ Nat.card H * Nat.card N := by
  open scoped Pointwise in
  have hset : (↑(H ⊔ N) : Set D) = (H : Set D) * (N : Set D) :=
    Subgroup.coe_mul_of_left_le_normalizer_right H N hLE
  let f : H × N → ↥(H ⊔ N) := fun p => ⟨p.1 * p.2, by
    have : (p.1 : D) * p.2 ∈ (↑(H ⊔ N) : Set D) := by
      rw [hset]; exact Set.mul_mem_mul p.1.2 p.2.2
    exact this⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    have hg' : g ∈ (↑(H ⊔ N) : Set D) := hg
    rw [hset] at hg'
    obtain ⟨a, ha, b, hb, rfl⟩ := hg'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod] at this

theorem mul_comm_of_sq_eq_one {D : Type*} [Group D] {a b : D} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : (a * b) ^ 2 = 1) : a * b = b * a := by
  have hinv : ∀ z : D, z ^ 2 = 1 → z⁻¹ = z := fun z hz =>
    inv_eq_of_mul_eq_one_right (by simpa [sq] using hz)
  calc a * b = (a * b)⁻¹ := (hinv _ hab).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv b hb, hinv a ha]

theorem eq_one_of_mem_of_pow_three {D : Type*} [Group D] {P : Subgroup D} (hP : IsPGroup 2 P)
    {q : D} (hq : q ∈ P) (h3 : q ^ 3 = 1) : q = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨q, hq⟩
  have hk' : q ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h3' : orderOf q ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h2 h1
  rw [hcop.gcd_eq_one] at h3'
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3')

theorem eq_one_or_eq_of_card_two {D : Type*} [Group D] {Q : Subgroup D} (hQ : Nat.card Q = 2)
    {a x : D} (ha : a ∈ Q) (ha1 : a ≠ 1) (hx : x ∈ Q) : x = 1 ∨ x = a := by
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · right
    obtain ⟨y, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQ
    have h1 : (⟨a, ha⟩ : Q) = y := huniq _ (fun h => ha1 (congrArg Subtype.val h))
    have h2 : (⟨x, hx⟩ : Q) = y := huniq _ (fun h => hx1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (h2.trans h1.symm)

theorem exists_ne_one_of_card_two {D : Type*} [Group D] {Q : Subgroup D} (hQ : Nat.card Q = 2) :
    ∃ a ∈ Q, a ≠ 1 := by
  have h1 : 1 < Nat.card Q := by rw [hQ]; norm_num
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨a, ha⟩ := exists_ne (1 : Q)
  exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩

theorem exists_mem_not_mem_of_card_lt {D : Type*} [Group D] [Finite D] {Q T : Subgroup D}
    (h : Nat.card Q < Nat.card T) : ∃ t ∈ T, t ∉ Q := by
  by_contra hcon
  push Not at hcon
  have hle : T ≤ Q := hcon
  exact absurd (Subgroup.card_le_of_le hle) (not_le.mpr h)

theorem exists_mem_not_mem_of_ne_of_card_eq {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (hne : A ≠ B) (hcard : Nat.card A = Nat.card B) : ∃ a ∈ A, a ∉ B := by
  by_contra hcon
  push Not at hcon
  have hle : A ≤ B := hcon
  exact hne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm))

theorem eq_or_eq_inv_of_orderOf_four {G : Type*} [Group G] {y z : G} (hy : orderOf y = 4)
    (hz : z ∈ Subgroup.zpowers y) (hz4 : orderOf z = 4) : z = y ∨ z = y⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h4 : y ^ 4 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hk : y ^ k = y ^ (k % 4) := by
    rw [← zpow_mod_orderOf, hy]
    rfl
  have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  · exfalso
    rw [hk, h] at hz4
    simp at hz4
  · left
    rw [hk, h]
    simp
  · exfalso
    rw [hk, h] at hz4
    have hsq : (y ^ (2 : ℤ)) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : y ^ (4 : ℤ) = 1 := by exact_mod_cast h4
      exact_mod_cast this
    have hdvd : orderOf (y ^ (2 : ℤ)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rw [hz4] at hdvd
    omega
  · right
    rw [hk, h]
    have : y ^ (3 : ℤ) * y = 1 := by
      rw [← zpow_add_one]
      exact_mod_cast h4
    exact eq_inv_of_mul_eq_one_left this

theorem card_inf_centralizer_eq_two {D : Type*} [Group D] (Q : Subgroup D) [Finite Q]
    (hQ : Nat.card Q = 8) {x : D} (hx3 : orderOf x = 3) (hnorm : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hnc : ¬ ∀ v ∈ Q, x * v = v * x) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set D)) = 2 := by
  have hx : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hmod := card_modEq_card_inf_centralizer Q hx hnorm
  set F := Q ⊓ Subgroup.centralizer ({x} : Set D) with hF
  have hFle : F ≤ Q := inf_le_left
  have hdvd : Nat.card F ∣ 8 := hQ ▸ Subgroup.card_dvd_of_le hFle
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h8] at hdvd
  obtain ⟨i, hi, hFi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hQ, hFi] at hmod
  rw [hFi]
  interval_cases i
  · exfalso; revert hmod; decide
  · rfl
  · exfalso; revert hmod; decide
  · exfalso
    have hFQ : F = Q := Subgroup.eq_of_le_of_card_ge hFle (by rw [hQ, hFi]; norm_num)
    apply hnc
    intro w hw
    have : w ∈ F := by rw [hFQ]; exact hw
    exact (Subgroup.mem_centralizer_iff.mp this.2) x (Set.mem_singleton x)

theorem eq_one_or_eq_of_mem_zpowers_of_sq_eq_one {D : Type*} [Group D] {ε z : D} (hε : ε ^ 2 = 1)
    (hz : z ∈ Subgroup.zpowers ε) : z = 1 ∨ z = ε := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hk : ε ^ k = ε ^ (k % 2) := by
    have hord : orderOf ε ∣ 2 := orderOf_dvd_of_pow_eq_one hε
    have h2 : ε ^ (2 : ℤ) = 1 := by exact_mod_cast hε
    calc ε ^ k = ε ^ (2 * (k / 2) + k % 2) := by rw [Int.mul_ediv_add_emod]
      _ = (ε ^ (2 : ℤ)) ^ (k / 2) * ε ^ (k % 2) := by rw [zpow_add, zpow_mul]
      _ = ε ^ (k % 2) := by rw [h2]; simp
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hk, h]; simp
  · right; rw [hk, h]; simp

theorem exists_hom_of_relIndex_two {D : Type*} [Group D] (G M : Subgroup D)
    (h2 : M.relIndex G = 2) :
    ∃ φ : ↥G →* Multiplicative (ZMod 2), Function.Surjective φ ∧
      ∀ g : ↥G, φ g = 1 ↔ (g : D) ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M' : Subgroup ↥G := M.subgroupOf G
  have hM' : M'.index = 2 := h2
  have hnormal : M'.Normal := Subgroup.normal_of_index_eq_two hM'
  have hcard : Nat.card (↥G ⧸ M') = 2 := by rw [← hM']; rfl
  let e₂ : ↥G ⧸ M' ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hcard (by simp)
  refine ⟨e₂.toMonoidHom.comp (QuotientGroup.mk' M'),
    e₂.surjective.comp (QuotientGroup.mk'_surjective M'), fun g => ?_⟩
  rw [MonoidHom.coe_comp, Function.comp_apply,
    show (e₂.toMonoidHom (QuotientGroup.mk' M' g)) = e₂ (QuotientGroup.mk g) from rfl,
    MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  exact Iff.rfl

theorem nonempty_mulEquiv_perm_three_of_mem {D : Type*} [Group D] (A : Subgroup D) [Finite A]
    {x ε : D} (hxA : x ∈ A) (hεA : ε ∈ A) (hx3 : orderOf x = 3) (hε2 : ε ^ 2 = 1)
    (hrel : ε * x * ε⁻¹ = x⁻¹) (hcard : Nat.card A = 6) :
    Nonempty (↥A ≃* Equiv.Perm (Fin 3)) := by
  refine nonempty_mulEquiv_perm_three (x := (⟨x, hxA⟩ : A)) (σ := (⟨ε, hεA⟩ : A)) ?_ ?_ ?_ hcard
  · rw [Subgroup.orderOf_mk, hx3]
  · exact Subtype.ext hε2
  · exact Subtype.ext (by simpa using hrel)

theorem not_mem_of_isPGroup_two {D : Type*} [Group D] {P : Subgroup D} (hP : IsPGroup 2 P) {x : D}
    (hx : orderOf x = 3) : x ∉ P := by
  intro hxP
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  rw [hx] at h1
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
  omega

theorem exists_normal_index_two_not_mem {D : Type*} [Group D] [Finite D] (G H M : Subgroup D)
    (hHG : H ≤ G) (hodd : Odd (H.relIndex G)) (h2 : M.relIndex H = 2)
    {ε : D} (hεH : ε ∈ H) (hεM : ε ∉ M) (hεc : ∀ g ∈ G, g * ε = ε * g) (hε2 : ε ^ 2 = 1) :
    ∃ K : Subgroup D, K ≤ G ∧ G ≤ Subgroup.normalizer (K : Set D) ∧ ε ∉ K ∧
      K.relIndex G = 2 ∧ ∀ q ∈ G, q ∉ K → ε * q ∈ K := by
  obtain ⟨ϕ, -, hϕ⟩ := exists_hom_of_relIndex_two H M h2
  have hεG : ε ∈ G := hHG hεH
  let H' : Subgroup ↥G := H.subgroupOf G
  let ϕ' : ↥H' →* Multiplicative (ZMod 2) :=
    ϕ.comp (Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom
  let ε' : ↥G := ⟨ε, hεG⟩
  have hε'2 : ε' ^ 2 = 1 := Subtype.ext hε2
  have hε'H : ε' ∈ H' := hεH
  have hkey : ∀ (k : ℕ) (g₀ : ↥G), g₀⁻¹ * ε' ^ k * g₀ ∈ H' → g₀⁻¹ * ε' ^ k * g₀ = ε' ^ k := by
    intro k g₀ _
    have hc : ∀ g : ↥G, g * ε' = ε' * g := fun g => Subtype.ext (hεc g g.2)
    have : g₀⁻¹ * ε' ^ k * g₀ = ε' ^ k := by
      have hck : Commute g₀ ε' := hc g₀
      calc g₀⁻¹ * ε' ^ k * g₀ = ε' ^ k * g₀⁻¹ * g₀ := by
            rw [((hck.symm.pow_left k).inv_right).eq]
        _ = ε' ^ k := by group
    exact this
  let ψ : ↥G →* Multiplicative (ZMod 2) := ϕ'.transfer
  have hψ := MonoidHom.transfer_eq_pow ϕ' ε' hkey
  have hpow : ε' ^ H'.index = ε' := by
    have hidx : H'.index = H.relIndex G := rfl
    rw [hidx]
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_succ, pow_mul, hε'2, one_pow, one_mul]
  have heq : (⟨ε' ^ H'.index, MonoidHom.transfer_eq_pow_aux ε' hkey⟩ : ↥H') = ⟨ε', hε'H⟩ :=
    Subtype.ext hpow
  rw [heq] at hψ
  have hψε : ψ ε' ≠ 1 := by
    have : ψ ε' = ϕ ⟨ε, hεH⟩ := hψ
    rw [this]
    intro h1
    exact hεM ((hϕ ⟨ε, hεH⟩).mp h1)
  have hZ2 : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a * b = 1 := by decide
  have hZ2' : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by decide
  let K : Subgroup D := (ψ.ker).map G.subtype
  have hKmem : ∀ g : D, g ∈ K ↔ ∃ hg : g ∈ G, ψ ⟨g, hg⟩ = 1 := by
    intro g
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨hg, hψg⟩
      exact ⟨⟨g, hg⟩, hψg, rfl⟩
  have hkey' : ∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    obtain ⟨hkG, hψk⟩ := (hKmem k).mp hk
    rw [hKmem]
    refine ⟨G.mul_mem (G.mul_mem hg hkG) (G.inv_mem hg), ?_⟩
    show ψ (⟨g, hg⟩ * ⟨k, hkG⟩ * ⟨g, hg⟩⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hψk, mul_one]
    exact mul_inv_cancel _
  refine ⟨K, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro k
    exact ⟨hkey' g hg k, fun hk => by simpa [mul_assoc] using hkey' g⁻¹ (G.inv_mem hg) _ hk⟩
  · intro hεK
    obtain ⟨_, hψg⟩ := (hKmem ε).mp hεK
    exact hψε hψg
  · have hKsub : K.subgroupOf G = ψ.ker :=
      Subgroup.comap_map_eq_self_of_injective G.subtype_injective ψ.ker
    have hsurj : Function.Surjective ψ := by
      intro w
      by_cases hw : w = 1
      · exact ⟨1, by rw [map_one, hw]⟩
      · exact ⟨ε', hZ2' _ _ hψε hw⟩
    show (K.subgroupOf G).index = 2
    rw [hKsub, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    simp
  · intro q hq hqK
    rw [hKmem]
    refine ⟨G.mul_mem hεG hq, ?_⟩
    have hqψ : ψ ⟨q, hq⟩ ≠ 1 := fun h1 => hqK ((hKmem q).mpr ⟨hq, h1⟩)
    show ψ (ε' * ⟨q, hq⟩) = 1
    rw [map_mul]
    exact hZ2 _ _ hψε hqψ

theorem le_normalizer_zpowers_of_central {D : Type*} [Group D] (G : Subgroup D) {ε : D}
    (hεc : ∀ g ∈ G, g * ε = ε * g) : G ≤ Subgroup.normalizer (Subgroup.zpowers ε : Set D) := by
  have hfix : ∀ g ∈ G, ∀ z ∈ Subgroup.zpowers ε, g * z * g⁻¹ = z := by
    intro g hg z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have : g * ε * g⁻¹ = ε := by
      calc g * ε * g⁻¹ = ε * g * g⁻¹ := by rw [hεc g hg]
        _ = ε := by group
    rw [← conj_zpow, this]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz; rw [hfix g hg z hz]; exact hz
  · intro hz
    have hz' : g * z * g⁻¹ ∈ Subgroup.zpowers ε := hz
    have h4 := hfix g⁻¹ (G.inv_mem hg) _ hz'
    rw [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h4
    rw [← h4] at hz'
    exact hz'

theorem mem_normalizer_zpowers_of_conj_inv {D : Type*} [Group D] {t x : D}
    (h : t * x * t⁻¹ = x⁻¹) (ht2 : t ^ 2 = 1) :
    t ∈ Subgroup.normalizer (Subgroup.zpowers x : Set D) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa [sq] using ht2)
  have key : ∀ z ∈ Subgroup.zpowers x, t * z * t⁻¹ ∈ Subgroup.zpowers x := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, h]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) k
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact key z
  · intro hz
    have := key _ hz
    rw [hti] at this
    rwa [show t * (t * z * t) * t = z by
      calc t * (t * z * t) * t = (t * t) * z * (t * t) := by group
        _ = z := by rw [← pow_two, ht2]; simp] at this

end CFSG.Quasithin.F6.GoldAmN
