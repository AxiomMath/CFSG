module

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
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch59

open Equiv MulAction

theorem exists_involution_quotient {G : Type*} [Group G] {H : Subgroup G} {k : G}
    (hnorm : ∀ h ∈ H, k⁻¹ * h * k ∈ H) (hk2 : k * k ∈ H) (hk : k ∉ H) :
    ∃ f : G ⧸ H → G ⧸ H,
      Function.Involutive f ∧ (∀ q, f q ≠ q) ∧
        ∀ (g : G) (q : G ⧸ H), f (g • q) = g • f q := by
  classical
  let f : G ⧸ H → G ⧸ H :=
    Quotient.map (fun g : G => g * k) (by
      intro a b hab
      show QuotientGroup.leftRel H (a * k) (b * k)
      rw [QuotientGroup.leftRel_apply]
      have habH : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
      have hconj : k⁻¹ * (a⁻¹ * b) * k ∈ H := hnorm _ habH
      have hk' : (a * k)⁻¹ * (b * k) = k⁻¹ * (a⁻¹ * b) * k := by group
      rw [hk']
      exact hconj)
  have hf_mk (g : G) : f (QuotientGroup.mk g) = QuotientGroup.mk (g * k) := by
    simp [f]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [hf_mk, hf_mk, QuotientGroup.eq]
      have h2 : (g * k * k)⁻¹ * g = (k * k)⁻¹ := by group
      rw [h2]
      exact H.inv_mem hk2
  · intro q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [hf_mk]
      intro hq
      have hmem : (g * k)⁻¹ * g ∈ H := QuotientGroup.eq.mp hq
      have hkinv : k⁻¹ ∈ H := by
        rwa [show (g * k)⁻¹ * g = k⁻¹ by group] at hmem
      exact hk (by simpa using H.inv_mem hkinv)
  · intro g q
    induction q using Quotient.inductionOn with
    | h h =>
      rw [MulAction.Quotient.smul_mk, hf_mk, hf_mk, MulAction.Quotient.smul_mk]
      simp only [smul_eq_mul, mul_assoc]

theorem exists_perm_orbit_involution {T Ω : Type*} [Group T] [Finite T] [MulAction T Ω]
    (hT : IsPGroup 2 T) {x : Ω} (hx : ∃ g : T, g • x ≠ x) :
    ∃ σ : Perm (MulAction.orbit T x),
      (∀ y, σ (σ y) = y) ∧ (∀ y, σ y ≠ y) ∧
        ∀ (g : T) (y : MulAction.orbit T x), σ (g • y) = g • σ y := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup T := MulAction.stabilizer T x
  have hHproper : H ≠ ⊤ := by
    intro htop
    obtain ⟨g, hg⟩ := hx
    exact hg (by
      have hgH : g ∈ H := by rw [htop]; exact Subgroup.mem_top g
      exact MulAction.mem_stabilizer_iff.mp hgH)
  have hHp : IsPGroup 2 H := hT.to_subgroup H
  obtain ⟨a, ha⟩ := hHp.exists_card_eq
  obtain ⟨n, hn⟩ := hT.index H
  have hn0 : n ≠ 0 := by
    intro h0
    apply hHproper
    rw [← Subgroup.index_eq_one, hn, h0]
    simp
  have hcard : Nat.card H * H.index = Nat.card T := H.card_mul_index
  have hdvd : 2 ^ (a + 1) ∣ Nat.card T := by
    rw [← hcard, ha, hn, ← pow_add]
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨K, hKcard, hHK, -⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (p := 2) Nat.prime_two (n := a + 1)
      (H := H) (L := ⊤)
      (by rw [ha]; exact pow_dvd_pow 2 (by omega))
      (by simpa using hdvd) le_top
  have hidxK : (H.subgroupOf K).index = 2 := by
    have h := (H.subgroupOf K).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, ha, hKcard,
      pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) a) h
  have hnormK : (H.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two hidxK
  have hKneH : K ≠ H := by
    intro hKH
    have hlt : 2 ^ a < 2 ^ (a + 1) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [hKH, ha] at hKcard
    omega
  obtain ⟨k, hkK, hkH⟩ : ∃ k : T, k ∈ K ∧ k ∉ H := by
    by_contra h
    push Not at h
    exact hKneH (le_antisymm (fun x hx => h x hx) hHK)
  have hk2 : k * k ∈ H := by
    have h := Subgroup.mul_self_mem_of_index_two hidxK (⟨k, hkK⟩ : K)
    exact Subgroup.mem_subgroupOf.mp h
  have hnorm : ∀ h ∈ H, k⁻¹ * h * k ∈ H := by
    intro h hh
    have hmem : (⟨h, hHK hh⟩ : K) ∈ H.subgroupOf K := Subgroup.mem_subgroupOf.mpr hh
    have hconj := hnormK.conj_mem' ⟨h, hHK hh⟩ hmem ⟨k, hkK⟩
    simpa using Subgroup.mem_subgroupOf.mp hconj
  obtain ⟨f, hfinv, hffree, hfsmul⟩ :=
    exists_involution_quotient (H := H) (k := k) hnorm hk2 hkH
  let e := MulAction.orbitEquivQuotientStabilizer T x
  have hsymm_smul : ∀ (g : T) (q : T ⧸ H), e.symm (g • q) = g • e.symm q := by
    intro g q
    induction q using Quotient.inductionOn with
    | h h =>
      apply Subtype.ext
      rw [MulAction.Quotient.smul_mk]
      change ((e.symm (QuotientGroup.mk (g • h)) : MulAction.orbit T x) : Ω) =
        g • ((e.symm (QuotientGroup.mk h) : MulAction.orbit T x) : Ω)
      rw [MulAction.orbitEquivQuotientStabilizer_symm_apply,
        MulAction.orbitEquivQuotientStabilizer_symm_apply]
      rw [smul_eq_mul, mul_smul]
  have he_smul : ∀ (g : T) (y : MulAction.orbit T x), e (g • y) = g • e y := by
    intro g y
    apply e.symm.injective
    rw [e.symm_apply_apply, hsymm_smul, e.symm_apply_apply]
  let σfun : MulAction.orbit T x → MulAction.orbit T x := fun y => e.symm (f (e y))
  have hσfun_inv : Function.Involutive σfun := by
    intro y
    change e.symm (f (e (e.symm (f (e y))))) = y
    rw [e.apply_symm_apply, hfinv, e.symm_apply_apply]
  have hσfun_free : ∀ y, σfun y ≠ y := by
    intro y hy
    apply hffree (e y)
    simpa [σfun] using congrArg e hy
  have hσfun_smul : ∀ (g : T) (y : MulAction.orbit T x), σfun (g • y) = g • σfun y := by
    intro g y
    change e.symm (f (e (g • y))) = g • e.symm (f (e y))
    rw [he_smul, hfsmul, hsymm_smul]
  let σ : Perm (MulAction.orbit T x) := hσfun_inv.toPerm σfun
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro y
    simpa [σ, Function.Involutive.coe_toPerm] using hσfun_inv y
  · intro y hy
    apply hσfun_free y
    simpa [σ, Function.Involutive.coe_toPerm] using hy
  · intro g y
    simpa [σ, Function.Involutive.coe_toPerm] using hσfun_smul g y

theorem perm_mul_involutive_of_commute {Ω : Type*} {σ τ : Perm Ω}
    (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    (hcomm : ∀ x, σ (τ x) = τ (σ x)) : ∀ x, (σ * τ) ((σ * τ) x) = x := by
  intro x
  calc (σ * τ) ((σ * τ) x) = σ (τ (σ (τ x))) := rfl
    _ = σ (σ (τ (τ x))) := by rw [← hcomm (τ x)]
    _ = x := by rw [hτ x, hσ x]

theorem exists_involution_commute {T Ω : Type*} [Group T] [Finite T] [MulAction T Ω] [Finite Ω]
    (hT : IsPGroup 2 T) :
    ∃ σ : Perm Ω, (∀ x, σ (σ x) = x) ∧ (∀ x y, σ x = x → σ y = y → x = y) ∧
      ∀ (g : T) (x : Ω), σ (g • x) = g • σ x := by
  classical
  let : Fintype Ω := Fintype.ofFinite Ω
  let : DecidableEq Ω := Classical.decEq Ω
  have main : ∀ s : Finset Ω, (∀ x ∈ s, ∀ g : T, g • x ∈ s) →
      ∃ σ : Perm Ω, (∀ x, σ (σ x) = x) ∧ (∀ x, x ∉ s → σ x = x) ∧
        (∀ x ∈ s, ∀ y ∈ s, σ x = x → σ y = y → x = y) ∧
        ∀ (g : T) (x : Ω), σ (g • x) = g • σ x := by
    intro s
    refine Finset.strongInduction (p := fun s => (∀ x ∈ s, ∀ g : T, g • x ∈ s) →
      ∃ σ : Perm Ω, (∀ x, σ (σ x) = x) ∧ (∀ x, x ∉ s → σ x = x) ∧
        (∀ x ∈ s, ∀ y ∈ s, σ x = x → σ y = y → x = y) ∧
        ∀ (g : T) (x : Ω), σ (g • x) = g • σ x) ?_ s
    intro s ih hsinv
    by_cases hex : ∃ x ∈ s, ∃ g : T, g • x ≠ x
    ·
      obtain ⟨x, hx, g0, hg0⟩ := hex
      let O : Set Ω := MulAction.orbit T x
      let Of : Finset Ω := Finset.univ.filter (fun y => y ∈ O)
      have hxO : x ∈ O := MulAction.mem_orbit_self x
      have hxOf : x ∈ Of := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxO⟩
      have hOf_sub : Of ⊆ s := by
        intro y hy
        rw [Finset.mem_filter] at hy
        obtain ⟨-, hyO⟩ := hy
        obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hyO
        exact hsinv x hx h
      have hOf_inv : ∀ y ∈ Of, ∀ g : T, g • y ∈ Of := by
        intro y hy g
        rw [Finset.mem_filter] at hy ⊢
        obtain ⟨-, hyO⟩ := hy
        obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hyO
        exact ⟨Finset.mem_univ _, by simpa [mul_smul] using MulAction.mem_orbit x (g * h)⟩
      have ht_sub : s \ Of ⊂ s := Finset.sdiff_ssubset hOf_sub ⟨x, hxOf⟩
      have ht_inv : ∀ y ∈ s \ Of, ∀ g : T, g • y ∈ s \ Of := by
        intro y hy g
        rw [Finset.mem_sdiff] at hy ⊢
        refine ⟨hsinv y hy.1 g, ?_⟩
        intro hgy
        exact hy.2 (by simpa using hOf_inv (g • y) hgy g⁻¹)
      obtain ⟨τ, hτ_inv, hτ_out, hτ_atmost, hτ_smul⟩ := ih (s \ Of) ht_sub ht_inv
      obtain ⟨σO, hσO_inv, hσO_free, hσO_smul⟩ :=
        exists_perm_orbit_involution hT (x := x) ⟨g0, hg0⟩
      let σ : Perm Ω := Equiv.Perm.ofSubtype σO
      have hσ_inv : ∀ y, σ (σ y) = y := by
        intro y
        by_cases hy : y ∈ O
        · have h1 : σ y = σO ⟨y, hy⟩ := Equiv.Perm.ofSubtype_apply_coe σO ⟨y, hy⟩
          have h2 : σ (σO ⟨y, hy⟩) = σO (σO ⟨y, hy⟩) :=
            Equiv.Perm.ofSubtype_apply_coe σO (σO ⟨y, hy⟩)
          calc σ (σ y) = σ (σO ⟨y, hy⟩) := by rw [h1]
            _ = σO (σO ⟨y, hy⟩) := h2
            _ = (⟨y, hy⟩ : MulAction.orbit T x) :=
              congrArg Subtype.val (hσO_inv ⟨y, hy⟩)
        · rw [Equiv.Perm.ofSubtype_apply_of_not_mem σO hy,
              Equiv.Perm.ofSubtype_apply_of_not_mem σO hy]
      have hσ_out : ∀ y, y ∉ O → σ y = y := by
        intro y hy
        exact Equiv.Perm.ofSubtype_apply_of_not_mem σO hy
      have hσ_free : ∀ y, y ∈ O → σ y ≠ y := by
        intro y hy h
        apply hσO_free ⟨y, hy⟩
        exact Subtype.ext (by
          have h1 : σ y = σO ⟨y, hy⟩ := Equiv.Perm.ofSubtype_apply_coe σO ⟨y, hy⟩
          rw [← h1]
          exact h)
      have hσ_smul : ∀ (g : T) (y : Ω), σ (g • y) = g • σ y := by
        intro g y
        by_cases hy : y ∈ O
        · obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hy
          have hmem : (g * h) • x ∈ O := by
            simpa [mul_smul] using MulAction.mem_orbit x (g * h)
          have hmemh : h • x ∈ O := MulAction.mem_orbit x h
          have h1 : σ ((g * h) • x) = σO ⟨(g * h) • x, hmem⟩ :=
            Equiv.Perm.ofSubtype_apply_coe σO ⟨(g * h) • x, hmem⟩
          have h2 : σ (h • x) = σO ⟨h • x, hmemh⟩ :=
            Equiv.Perm.ofSubtype_apply_coe σO ⟨h • x, hmemh⟩
          have harg : (g • (⟨h • x, hmemh⟩ : MulAction.orbit T x)) =
              ⟨(g * h) • x, hmem⟩ := by
            ext
            simp [mul_smul]
          have h3 : ((σO (g • (⟨h • x, hmemh⟩ : MulAction.orbit T x)) :
              MulAction.orbit T x) : Ω) =
              g • ((σO ⟨h • x, hmemh⟩ : MulAction.orbit T x) : Ω) := by
            simpa using congrArg Subtype.val (hσO_smul g ⟨h • x, hmemh⟩)
          rw [harg] at h3
          rw [← mul_smul g h x, h1, h2]
          exact h3
        · have hgy : g • y ∉ O := by
            intro hgO
            obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hgO
            apply hy
            have hy' : y = (g⁻¹ * h) • x := by
              calc y = g⁻¹ • (g • y) := (inv_smul_smul g y).symm
                _ = g⁻¹ • (h • x) := by rw [← hh]
                _ = (g⁻¹ * h) • x := by rw [mul_smul]
            rw [hy']
            exact MulAction.mem_orbit x (g⁻¹ * h)
          rw [hσ_out (g • y) hgy]
          rw [hσ_out y hy]
      have hdisj : Equiv.Perm.Disjoint σ τ := by
        rw [Equiv.Perm.disjoint_iff_eq_or_eq]
        intro y
        by_cases hy : y ∈ O
        · right
          apply hτ_out
          intro hyt
          rw [Finset.mem_sdiff] at hyt
          exact hyt.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)
        · left
          exact hσ_out y hy
      have hcomm : ∀ y, σ (τ y) = τ (σ y) := fun y =>
        congrArg (fun e : Perm Ω => e y) hdisj.commute.eq
      refine ⟨σ * τ, perm_mul_involutive_of_commute hσ_inv hτ_inv hcomm, ?_, ?_, ?_⟩
      · intro y hy
        have hyO : y ∉ O := fun hO => hy (hOf_sub (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hO⟩))
        have hyt : y ∉ s \ Of := fun h => hy (Finset.mem_sdiff.mp h).1
        rw [Equiv.Perm.mul_apply, hτ_out y hyt, hσ_out y hyO]
      · intro y hy z hz hfy hfz
        by_cases hyO : y ∈ O
        · have hyt : y ∉ s \ Of :=
            fun h => (Finset.mem_sdiff.mp h).2
              (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hyO⟩)
          have hτy : τ y = y := hτ_out y hyt
          rw [Equiv.Perm.mul_apply, hτy] at hfy
          exact absurd hfy (hσ_free y hyO)
        · have hyOf : y ∉ Of := fun h => hyO (Finset.mem_filter.mp h).2
          have hyt : y ∈ s \ Of := Finset.mem_sdiff.mpr ⟨hy, hyOf⟩
          have hσy : σ y = y := hσ_out y hyO
          have hτy : τ y = y := by
            have h := congrArg σ hfy
            rw [Equiv.Perm.mul_apply, hσ_inv, hσy] at h
            exact h
          by_cases hzO : z ∈ O
          · have hzt : z ∉ s \ Of :=
              fun h => (Finset.mem_sdiff.mp h).2
                (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hzO⟩)
            have hτz : τ z = z := hτ_out z hzt
            rw [Equiv.Perm.mul_apply, hτz] at hfz
            exact absurd hfz (hσ_free z hzO)
          · have hzOf : z ∉ Of := fun h => hzO (Finset.mem_filter.mp h).2
            have hzt : z ∈ s \ Of := Finset.mem_sdiff.mpr ⟨hz, hzOf⟩
            have hσz : σ z = z := hσ_out z hzO
            have hτz : τ z = z := by
              have h := congrArg σ hfz
              rw [Equiv.Perm.mul_apply, hσ_inv, hσz] at h
              exact h
            exact hτ_atmost y hyt z hzt hτy hτz
      · intro g y
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ_smul, hσ_smul]
    ·
      push Not at hex
      have hfixed : ∀ y ∈ s, ∀ g : T, g • y = y := hex
      by_cases hcard : s.card ≤ 1
      · refine ⟨1, ?_, ?_, ?_, ?_⟩
        · intro y; rfl
        · intro y _; rfl
        · intro y hy z hz _ _; exact Finset.card_le_one.mp hcard y hy z hz
        · intro g y; rfl
      · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
        have ht_sub : s \ {x, y} ⊂ s := by
          refine Finset.sdiff_ssubset ?_ ⟨x, by simp⟩
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have ht_inv : ∀ z ∈ s \ {x, y}, ∀ g : T, g • z ∈ s \ {x, y} := by
          intro z hz g
          rw [Finset.mem_sdiff] at hz ⊢
          refine ⟨hsinv z hz.1 g, ?_⟩
          rw [hfixed z hz.1 g]
          exact hz.2
        obtain ⟨τ, hτ_inv, hτ_out, hτ_atmost, hτ_smul⟩ := ih (s \ {x, y}) ht_sub ht_inv
        let σ : Perm Ω := Equiv.swap x y
        have hσ_inv : ∀ z, σ (σ z) = z := by
          intro z
          simp [σ]
        have hσ_out : ∀ z, z ≠ x → z ≠ y → σ z = z := by
          intro z hzx hzy
          simpa [σ] using Equiv.swap_apply_of_ne_of_ne hzx hzy
        have hσ_smul : ∀ (g : T) (z : Ω), σ (g • z) = g • σ z := by
          intro g z
          by_cases hzx : z = x
          · rw [hzx]
            rw [hfixed x hx g]
            simp only [σ, Equiv.swap_apply_left]
            rw [hfixed y hy g]
          · by_cases hzy : z = y
            · rw [hzy]
              rw [hfixed y hy g]
              simp only [σ, Equiv.swap_apply_right]
              rw [hfixed x hx g]
            · have hgzx : g • z ≠ x := by
                intro h
                have hz' : z = g⁻¹ • x := by
                  rw [← h, inv_smul_smul]
                have : z ∈ s := by
                  rw [hz']
                  simpa using hsinv x hx g⁻¹
                have hgz : g • z = z := hfixed z this g
                exact hzx (hgz.symm.trans h)
              have hgzy : g • z ≠ y := by
                intro h
                have hz' : z = g⁻¹ • y := by
                  rw [← h, inv_smul_smul]
                have : z ∈ s := by
                  rw [hz']
                  simpa using hsinv y hy g⁻¹
                have hgz : g • z = z := hfixed z this g
                exact hzy (hgz.symm.trans h)
              rw [hσ_out (g • z) hgzx hgzy, hσ_out z hzx hzy]
        have hdisj : Equiv.Perm.Disjoint σ τ := by
          rw [Equiv.Perm.disjoint_iff_eq_or_eq]
          intro z
          by_cases hzx : z = x
          · right
            exact hτ_out z fun hmem =>
              (Finset.mem_sdiff.mp hmem).2 (by simp [hzx])
          · by_cases hzy : z = y
            · right
              exact hτ_out z fun hmem =>
                (Finset.mem_sdiff.mp hmem).2 (by simp [hzy])
            · left
              exact hσ_out z hzx hzy
        have hcomm : ∀ z, σ (τ z) = τ (σ z) := fun z =>
          congrArg (fun e : Perm Ω => e z) hdisj.commute.eq
        refine ⟨σ * τ, perm_mul_involutive_of_commute hσ_inv hτ_inv hcomm, ?_, ?_, ?_⟩
        · intro z hz
          have hzt : z ∉ s \ {x, y} := fun h => hz (Finset.mem_sdiff.mp h).1
          have hzx : z ≠ x := by
            intro h; rw [h] at hz; exact hz hx
          have hzy : z ≠ y := by
            intro h; rw [h] at hz; exact hz hy
          rw [Equiv.Perm.mul_apply, hτ_out z hzt, hσ_out z hzx hzy]
        · intro z hz w hw hfz hfw
          have hz_not_x : z ≠ x := by
            intro h
            rw [h] at hfz
            have hxmove : (σ * τ) x = y := by
              rw [Equiv.Perm.mul_apply, hτ_out x (by simp)]
              simp [σ]
            rw [hxmove] at hfz
            exact hxy hfz.symm
          have hz_not_y : z ≠ y := by
            intro h
            rw [h] at hfz
            have hymove : (σ * τ) y = x := by
              rw [Equiv.Perm.mul_apply, hτ_out y (by simp)]
              simp [σ]
            rw [hymove] at hfz
            exact hxy hfz
          have hw_not_x : w ≠ x := by
            intro h
            rw [h] at hfw
            have hxmove : (σ * τ) x = y := by
              rw [Equiv.Perm.mul_apply, hτ_out x (by simp)]
              simp [σ]
            rw [hxmove] at hfw
            exact hxy hfw.symm
          have hw_not_y : w ≠ y := by
            intro h
            rw [h] at hfw
            have hymove : (σ * τ) y = x := by
              rw [Equiv.Perm.mul_apply, hτ_out y (by simp)]
              simp [σ]
            rw [hymove] at hfw
            exact hxy hfw
          have hzt : z ∈ s \ {x, y} :=
            Finset.mem_sdiff.mpr ⟨hz, by simp [hz_not_x, hz_not_y]⟩
          have hwt : w ∈ s \ {x, y} :=
            Finset.mem_sdiff.mpr ⟨hw, by simp [hw_not_x, hw_not_y]⟩
          have hσz : σ z = z := hσ_out z hz_not_x hz_not_y
          have hσw : σ w = w := hσ_out w hw_not_x hw_not_y
          have hτz : τ z = z := by
            have h := congrArg σ hfz
            rw [Equiv.Perm.mul_apply, hσ_inv, hσz] at h
            exact h
          have hτw : τ w = w := by
            have h := congrArg σ hfw
            rw [Equiv.Perm.mul_apply, hσ_inv, hσw] at h
            exact h
          exact hτ_atmost z hzt w hwt hτz hτw
        · intro g z
          rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ_smul, hσ_smul]
  have huniv : ∀ x ∈ (Finset.univ : Finset Ω), ∀ g : T, g • x ∈ Finset.univ := by
    intro x _ g
    exact Finset.mem_univ _
  obtain ⟨σ, hσ_inv, -, hσ_atmost, hσ_smul⟩ := main Finset.univ huniv
  refine ⟨σ, hσ_inv, ?_, hσ_smul⟩
  intro x y hx hy
  exact hσ_atmost x (Finset.mem_univ x) y (Finset.mem_univ y) hx hy

theorem card_image_nonfixed_of_involution {α β : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq β]
    (τ : Perm α) (hτ : ∀ x, τ (τ x) = x) (f : α → β) (hf : ∀ x, f (τ x) = f x)
    (hfib : ∀ x y, τ x ≠ x → f x = f y → y = x ∨ y = τ x) :
    ((Finset.univ.filter (fun x => τ x ≠ x)).image f).card * 2 =
      (Finset.univ.filter (fun x => τ x ≠ x)).card := by
  classical
  let s : Finset α := Finset.univ.filter (fun x => τ x ≠ x)
  have hsτ : ∀ x ∈ s, τ x ∈ s := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro h
    rw [hτ x] at h
    exact hx.2 h.symm
  have hfiber : ∀ b ∈ s.image f, ({a ∈ s | f a = b} : Finset α).card = 2 := by
    intro b hb
    obtain ⟨x, hxs, rfl⟩ := Finset.mem_image.mp hb
    have hxτ : τ x ∈ s := hsτ x hxs
    have hxne : τ x ≠ x := (Finset.mem_filter.mp hxs).2
    have hset : ({a ∈ s | f a = f x} : Finset α) = {x, τ x} := by
      ext a
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨has, hfa⟩
        rcases hfib x a hxne hfa.symm with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact ⟨hxs, rfl⟩
        · exact ⟨hxτ, hf x⟩
    rw [hset, Finset.card_pair (Ne.symm hxne)]
  have hsum : s.card = 2 * (s.image f).card := by
    calc s.card = ∑ b ∈ s.image f, ({a ∈ s | f a = b} : Finset α).card :=
          Finset.card_eq_sum_card_image f s
      _ = ∑ b ∈ s.image f, 2 := Finset.sum_congr rfl hfiber
      _ = 2 * (s.image f).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hsum]
  exact mul_comm _ _

theorem exists_blocks_four {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {T : Subgroup (Perm Ω)}
    (hT : IsPGroup 2 T) :
    ∃ (σ : Perm Ω) (ℬ : Finset (Finset Ω)),
      (∀ x, σ (σ x) = x) ∧ (∀ x y, σ x = x → σ y = y → x = y) ∧
      T ≤ Subgroup.centralizer {σ} ∧ ℬ.card = Fintype.card Ω / 4 ∧
      (ℬ : Set (Finset Ω)).PairwiseDisjoint id ∧ (∀ B ∈ ℬ, B.card = 4 ∧ ∀ x ∈ B, σ x ∈ B) ∧
      ∀ g ∈ T, ∀ B ∈ ℬ, B.image g ∈ ℬ := by
  classical
  obtain ⟨σ, hσ_inv, hσ_fix, hσ_comm⟩ :=
    exists_involution_commute (T := ↥T) (Ω := Ω) hT
  have hσ_comm' : ∀ (g : Perm Ω), g ∈ T → ∀ x : Ω, σ (g x) = g (σ x) := by
    intro g hg x
    simpa [Subgroup.smul_def] using hσ_comm ⟨g, hg⟩ x
  have hTcent : T ≤ Subgroup.centralizer ({σ} : Set (Perm Ω)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    ext x
    exact (hσ_comm' g hg x).symm
  let fixσ : Finset Ω := Finset.univ.filter (fun x => σ x = x)
  let D : Finset Ω := Finset.univ.filter (fun x => σ x ≠ x)
  let pairOf : Ω → Finset Ω := fun x => {x, σ x}
  let P : Finset (Finset Ω) := D.image pairOf
  have hPcard : P.card * 2 = D.card := by
    have h := card_image_nonfixed_of_involution σ hσ_inv pairOf ?_ ?_
    · simpa [P, D] using h
    · intro x
      simp [pairOf, hσ_inv, Finset.pair_comm]
    · intro x y hx hxy
      have hy : y ∈ pairOf x := by
        rw [hxy]
        simp [pairOf]
      simpa [pairOf, Finset.mem_insert, Finset.mem_singleton] using hy
  have hDcard : D.card + fixσ.card = Fintype.card Ω := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω))
      (p := fun x => σ x = x)
    simpa [D, fixσ, Finset.card_univ, add_comm] using h
  have hfixσ_le : fixσ.card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro x hx y hy
    exact hσ_fix x y (by simpa [fixσ] using hx) (by simpa [fixσ] using hy)
  have hP_mem : ∀ {p : Finset Ω}, p ∈ P ↔ ∃ x : Ω, σ x ≠ x ∧ p = pairOf x := by
    intro p
    change p ∈ D.image pairOf ↔ ∃ x : Ω, σ x ≠ x ∧ p = pairOf x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (Finset.mem_filter.mp hx).2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩, rfl⟩
  have hP_card2 : ∀ p ∈ P, p.card = 2 := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := hP_mem.mp hp
    exact Finset.card_pair (Ne.symm hx)
  have hP_sigma : ∀ p ∈ P, p.image σ = p := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := hP_mem.mp hp
    simp [pairOf, hσ_inv, Finset.pair_comm]
  have hP_mem_ne : ∀ p ∈ P, ∀ x ∈ p, σ x ≠ x := by
    intro p hp x hx
    obtain ⟨y, hy, hpy⟩ := hP_mem.mp hp
    rw [hpy] at hx
    have hxmem : x ∈ ({y, σ y} : Finset Ω) := hx
    rcases Finset.mem_insert.mp hxmem with hxy | hxσy
    · rw [hxy]
      exact hy
    · have hxeq : x = σ y := Finset.mem_singleton.mp hxσy
      rw [hxeq, hσ_inv]
      exact fun h => hy h.symm
  have hP_eq_pair : ∀ {p : Finset Ω} {x : Ω}, p ∈ P → x ∈ p → p = pairOf x := by
    intro p x hp hx
    obtain ⟨y, hy, rfl⟩ := hP_mem.mp hp
    have hxmem : x ∈ ({y, σ y} : Finset Ω) := hx
    rcases Finset.mem_insert.mp hxmem with hxy | hxσy
    · rw [← hxy]
    · have hxeq : x = σ y := Finset.mem_singleton.mp hxσy
      have hyx : y = σ x := by rw [hxeq, hσ_inv]
      rw [hyx]
      change ({σ x, σ (σ x)} : Finset Ω) = {x, σ x}
      rw [hσ_inv, Finset.pair_comm]
  have hP_disjoint : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p q := by
    intro p hp q hq hpq
    rw [Finset.disjoint_left]
    intro x hxp hxq
    exact hpq ((hP_eq_pair hp hxp).trans (hP_eq_pair hq hxq).symm)
  have hsmul_mem : ∀ (g : ↥T) (p : Finset Ω), p ∈ P → p.image (g : Perm Ω) ∈ P := by
    intro g p hp
    obtain ⟨x, hx, rfl⟩ := hP_mem.mp hp
    refine hP_mem.mpr ⟨(g : Perm Ω) x, ?_, ?_⟩
    · intro h
      apply hx
      apply (g : Perm Ω).injective
      calc (g : Perm Ω) (σ x) = σ ((g : Perm Ω) x) :=
            (hσ_comm' (g : Perm Ω) g.2 x).symm
        _ = (g : Perm Ω) x := h
    · simp [pairOf, hσ_comm' (g : Perm Ω) g.2 x]
  let actP : MulAction ↥T ↥P :=
    { smul := fun g p => ⟨p.1.image (g : Perm Ω), hsmul_mem g p.1 p.2⟩
      one_smul := by
        intro p
        apply Subtype.ext
        show p.1.image ((1 : ↥T) : Perm Ω) = p.1
        simp
      mul_smul := by
        intro g h p
        apply Subtype.ext
        apply Finset.ext
        intro x
        change x ∈ p.1.image (((g * h : ↥T) : Perm Ω)) ↔
          x ∈ (p.1.image (h : Perm Ω)).image (g : Perm Ω)
        constructor
        · intro hx
          rw [Finset.mem_image] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          rw [Finset.mem_image]
          refine ⟨(h : Perm Ω) y, ?_, ?_⟩
          · exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
          · simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]
        · intro hx
          rw [Finset.mem_image] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          rw [Finset.mem_image] at hy
          obtain ⟨z, hz, rfl⟩ := hy
          rw [Finset.mem_image]
          exact ⟨z, hz, by
            simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]⟩ }
  let : MulAction ↥T ↥P := actP
  obtain ⟨ρ, hρ_inv, hρ_fix, hρ_comm⟩ :=
    exists_involution_commute (T := ↥T) (Ω := ↥P) hT
  let Q : Finset ↥P := Finset.univ.filter (fun q => ρ q ≠ q)
  let fixρ : Finset ↥P := Finset.univ.filter (fun q => ρ q = q)
  let block : ↥P → Finset Ω := fun q => q.1 ∪ (ρ q).1
  let ℬ : Finset (Finset Ω) := Q.image block
  have hblock_rho : ∀ q : ↥P, block (ρ q) = block q := by
    intro q
    simp [block, hρ_inv q, Finset.union_comm]
  have hP_card_of_subtype : Fintype.card ↥P = P.card :=
    Fintype.card_of_subtype P (fun x => Iff.rfl)
  have hQcard : Q.card + fixρ.card = P.card := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ↥P))
      (p := fun q : ↥P => ρ q = q)
    have h' : fixρ.card + Q.card = P.card := by
      simpa [fixρ, Q, Finset.card_univ, hP_card_of_subtype] using h
    omega
  have hfixρ_le : fixρ.card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro q hq q' hq'
    exact hρ_fix q q' (by simpa [fixρ] using hq) (by simpa [fixρ] using hq')
  have horbit_eq_of_common : ∀ {q q' : ↥P} (x : Ω), x ∈ block q → x ∈ block q' →
      q = q' ∨ q = ρ q' ∨ ρ q = q' ∨ ρ q = ρ q' := by
    intro q q' x hx hx'
    have hxq : x ∈ q.1 ∪ (ρ q).1 := by simpa [block] using hx
    have hxq' : x ∈ q'.1 ∪ (ρ q').1 := by simpa [block] using hx'
    rcases Finset.mem_union.mp hxq with hxq | hxρq
    · rcases Finset.mem_union.mp hxq' with hxq' | hxρq'
      · exact Or.inl (Subtype.ext
          ((hP_eq_pair q.2 hxq).trans (hP_eq_pair q'.2 hxq').symm))
      · exact Or.inr (Or.inl (Subtype.ext
          ((hP_eq_pair q.2 hxq).trans
            (hP_eq_pair (ρ q').2 hxρq').symm)))
    · rcases Finset.mem_union.mp hxq' with hxq' | hxρq'
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext
          ((hP_eq_pair (ρ q).2 hxρq).trans (hP_eq_pair q'.2 hxq').symm))))
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext
          ((hP_eq_pair (ρ q).2 hxρq).trans
            (hP_eq_pair (ρ q').2 hxρq').symm))))
  have hcommon_eq : ∀ {q q' : ↥P} (x : Ω), x ∈ block q → x ∈ block q' →
      block q = block q' := by
    intro q q' x hx hx'
    rcases horbit_eq_of_common x hx hx' with h | h | h | h
    · rw [h]
    · rw [h, hblock_rho]
    · rw [← h]
      exact (hblock_rho q).symm
    · have hqq' : q = q' := by
        have := congrArg ρ h
        simpa [hρ_inv] using this
      rw [hqq']
  have hBcard : ℬ.card * 2 = Q.card := by
    have h := card_image_nonfixed_of_involution ρ hρ_inv block hblock_rho ?_
    · simpa [ℬ, Q, block] using h
    · intro q q' hq hblockeq
      obtain ⟨y, hy, hqy⟩ := hP_mem.mp q.2
      have hyq : y ∈ q.1 := by rw [hqy]; simp [pairOf]
      have hyblock : y ∈ block q := by
        change y ∈ q.1 ∪ (ρ q).1
        exact Finset.mem_union_left _ hyq
      have hyblock' : y ∈ block q' := by
        rw [← hblockeq]
        exact hyblock
      rcases horbit_eq_of_common y hyblock hyblock' with h | h | h | h
      · exact Or.inl h.symm
      · have h' : q' = ρ q := by
          have := congrArg ρ h
          simpa [hρ_inv] using this.symm
        exact Or.inr h'
      · exact Or.inr h.symm
      · have hqq' : q = q' := by
          have := congrArg ρ h
          simpa [hρ_inv] using this
        exact Or.inl hqq'.symm
  have htotal : Fintype.card Ω = 4 * ℬ.card + fixσ.card + 2 * fixρ.card := by
    omega
  have hBcard_final : ℬ.card = Fintype.card Ω / 4 := by
    have hr : fixσ.card + 2 * fixρ.card < 4 := by omega
    rw [htotal]
    rw [show 4 * ℬ.card + fixσ.card + 2 * fixρ.card =
      4 * ℬ.card + (fixσ.card + 2 * fixρ.card) by omega]
    rw [Nat.mul_add_div (by norm_num : 0 < 4), Nat.div_eq_of_lt hr, Nat.add_zero]
  have hblock_card4 : ∀ q ∈ Q, (block q).card = 4 := by
    intro q hq
    have hqne : ρ q ≠ q := (Finset.mem_filter.mp hq).2
    have hneq : q.1 ≠ (ρ q).1 := by
      intro h
      exact hqne (Subtype.ext h.symm)
    have hdisj : Disjoint q.1 (ρ q).1 := hP_disjoint q.1 q.2 (ρ q).1 (ρ q).2 hneq
    change (q.1 ∪ (ρ q).1).card = 4
    rw [Finset.card_union_of_disjoint hdisj, hP_card2 q.1 q.2,
      hP_card2 (ρ q).1 (ρ q).2]
  have hblock_sigma : ∀ q : ↥P, (block q).image σ = block q := by
    intro q
    change (q.1 ∪ (ρ q).1).image σ = q.1 ∪ (ρ q).1
    rw [Finset.image_union, hP_sigma q.1 q.2, hP_sigma (ρ q).1 (ρ q).2]
  have hB_card : ∀ B ∈ ℬ, B.card = 4 := by
    intro B hB
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    exact hblock_card4 q hq
  have hB_sigma : ∀ B ∈ ℬ, ∀ x ∈ B, σ x ∈ B := by
    intro B hB x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    rw [← hblock_sigma q]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hB_pairwise : (ℬ : Set (Finset Ω)).PairwiseDisjoint id := by
    rw [show (ℬ : Set (Finset Ω)).PairwiseDisjoint id =
        (ℬ : Set (Finset Ω)).Pairwise (fun B₁ B₂ => Disjoint B₁ B₂) from rfl]
    intro B₁ hB₁ B₂ hB₂ hne
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    apply hne
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB₁
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hB₂
    exact hcommon_eq x hx₁ hx₂
  have hB_T : ∀ g ∈ T, ∀ B ∈ ℬ, B.image g ∈ ℬ := by
    intro g hg B hB
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    have hqQ : (⟨g, hg⟩ : ↥T) • q ∈ Q := by
      change (⟨g, hg⟩ : ↥T) • q ∈ Finset.univ.filter (fun r : ↥P => ρ r ≠ r)
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro h
      apply (Finset.mem_filter.mp hq).2
      have h1 : (⟨g, hg⟩ : ↥T)⁻¹ • ρ ((⟨g, hg⟩ : ↥T) • q) = ρ q := by
        rw [hρ_comm (⟨g, hg⟩) q]
        simp
      have := congrArg (fun r : ↥P => (⟨g, hg⟩ : ↥T)⁻¹ • r) h
      rw [h1] at this
      simpa using this
    refine Finset.mem_image.mpr ⟨(⟨g, hg⟩ : ↥T) • q, hqQ, ?_⟩
    change (q.1.image (g : Perm Ω) ∪
      (ρ ((⟨g, hg⟩ : ↥T) • q)).1) =
      (q.1 ∪ (ρ q).1).image (g : Perm Ω)
    rw [hρ_comm, Finset.image_union]
    rfl
  refine ⟨σ, ℬ, hσ_inv, hσ_fix, hTcent, hBcard_final, hB_pairwise,
    fun B hB => ⟨hB_card B hB, hB_sigma B hB⟩, hB_T⟩


end CFSG.LocalAnalysis.WeakClosure81.Asch59
