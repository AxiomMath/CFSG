module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmOrbit
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentTypeSum
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.TwistedConfig
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDickson
import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary
import CFSG.RankThree.PartOne.S11d.OrthCaseH
import CFSG.RankThree.PartOne.S11d.OrthCaseN
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
open CFSG.GroupTheory.WeirSylow

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem tbjOmBlkZ_commute_of_isCompl {U R : Submodule K V} (hc : IsCompl U R)
    {a b : V ≃ₗ[K] V} (haU : ∀ u ∈ U, a u = u) (haR : ∀ s ∈ R, a s ∈ R)
    (hbU : ∀ u ∈ U, b u ∈ U) (hbR : ∀ s ∈ R, b s = s) : a * b = b * a := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, hu, s, hs, rfl⟩ := exists_add_of_isCompl hc v
  simp only [LinearEquiv.mul_apply, map_add, hbR s hs, haU u hu, haU _ (hbU u hu),
    hbR _ (haR s hs)]

omit [Finite K] [CharP K 2] in
private theorem tbjOmBlkZ_finrank_sup_sup_span {U₁ U₂ : Submodule K V} {v : V}
    (hnd₁ : ∀ u ∈ U₁, (∀ w ∈ U₁, QuadraticMap.polar Q w u = 0) → u = 0)
    (hnd₂ : ∀ u ∈ U₂, (∀ w ∈ U₂, QuadraticMap.polar Q w u = 0) → u = 0)
    (h₁₂ : ∀ u ∈ U₁, ∀ w ∈ U₂, QuadraticMap.polar Q u w = 0) (hv : v ≠ 0)
    (hv₁ : ∀ u ∈ U₁, QuadraticMap.polar Q u v = 0)
    (hv₂ : ∀ u ∈ U₂, QuadraticMap.polar Q u v = 0) :
    finrank K ↥(U₁ ⊔ U₂ ⊔ K ∙ v) = finrank K U₁ + finrank K U₂ + 1 := by
  have hd : Disjoint U₁ U₂ := Submodule.disjoint_def.mpr fun u hu₁ hu₂ =>
    hnd₁ u hu₁ fun w hw => h₁₂ w hw u hu₂
  have h12 : finrank K ↥(U₁ ⊔ U₂) = finrank K U₁ + finrank K U₂ := by
    have := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
    rwa [disjoint_iff.mp hd, finrank_bot, add_zero] at this
  have hv' : v ∉ U₁ ⊔ U₂ := by
    intro hmem
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    have ha0 : a = 0 := hnd₁ a ha fun w hw => by
      have h1 := hv₁ w hw
      rwa [← hab, QuadraticMap.polar_add_right, h₁₂ w hw b hb, add_zero] at h1
    have hb0 : b = 0 := hnd₂ b hb fun w hw => by
      have h1 := hv₂ w hw
      rwa [← hab, QuadraticMap.polar_add_right, QuadraticMap.polar_comm Q w a, h₁₂ a ha w hw,
        zero_add] at h1
    exact hv (by rw [← hab, ha0, hb0, add_zero])
  have hd2 : Disjoint (U₁ ⊔ U₂) (K ∙ v) := (Submodule.disjoint_span_singleton' hv).mpr hv'
  have := Submodule.finrank_sup_add_finrank_inf_eq (U₁ ⊔ U₂) (K ∙ v)
  rwa [disjoint_iff.mp hd2, finrank_bot, add_zero, h12, finrank_span_singleton hv] at this

private theorem tbjOmBlkZ_exists_pair_ne {ι : Type*} {P : ι → Prop}
    (h : 2 ≤ Nat.card {i // P i}) : ∃ i k, i ≠ k ∧ P i ∧ P k := by
  have : Finite {i // P i} := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨a, b, hab⟩ :=
    ((Finite.one_lt_card_iff_nontrivial (α := {i // P i})).mp (by omega)).exists_pair_ne
  exact ⟨a.1, b.1, fun h => hab (Subtype.ext h), a.2, b.2⟩

private theorem tbjOmBlkZ_exists_third {P : Fin r → Prop} (h : 3 ≤ Nat.card {i // P i})
    (i k : Fin r) : ∃ l, l ≠ i ∧ l ≠ k ∧ P l := by
  classical
  have hcard : Nat.card {i // P i} = (Finset.univ.filter P).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hpos : 0 < (((Finset.univ.filter P).erase i).erase k).card := by
    have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.filter P) (a := i)
    have h2 := Finset.pred_card_le_card_erase (s := (Finset.univ.filter P).erase i) (a := k)
    omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_filter] at hl
  exact ⟨l, hl.2.1, hl.1, hl.2.2.2⟩

private theorem tbjOmBlkZ_permAut_swap_apply {n : ℕ} {i k : Fin n}
    {f : Fin n → Multiplicative (ZMod p)} (h : f i = f k) : permAut (Equiv.swap i k) f = f := by
  funext j
  rw [permAut_apply, Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, h]
  · rw [h2, h]
  · rfl

private theorem tbjOmBlkZ_sgnAut_apply {n : ℕ} {i : Fin n} {f : Fin n → Multiplicative (ZMod p)}
    (h : f i = 1) : sgnAut i f = f := by
  rw [sgnAut_apply, h, inv_one, ← h, Function.update_eq_self]

private theorem tbjOmBlkZ_dinv_apply {n : ℕ} {i k : Fin n} (hik : i ≠ k)
    {f : Fin n → Multiplicative (ZMod p)} (hi : f i = 1) (hk : f k = 1) :
    dinv i k f = f := by
  funext j
  unfold dinv
  have h1 : Function.update f k (f k)⁻¹ = f := by
    rw [hk, inv_one, ← hk]
    exact Function.update_eq_self k f
  rw [h1, hi, inv_one, ← hi]
  exact congrFun (Function.update_eq_self i f) j

private theorem tbjOmBlkZ_dicksonDerived {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (R : QuadraticForm K W) (hR : (polarBilin R).Nondegenerate)
    (h5 : 5 ≤ finrank K W) : CFSG.RankThree.PartOne.DicksonDerived R hR := by
  have heven : Even (finrank K W) :=
    LinearMap.BilinForm.IsAlt.even_finrank (B := polarBilin R) (fun w => by
      rw [polarBilin_apply_apply, polar_self, two_smul, CharTwo.add_self_eq_zero]) hR
  obtain ⟨m, hm⟩ := heven
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · have h6 : finrank K W = 6 := by omega
    by_cases hT : ∃ U : Submodule K W, finrank K U = 3 ∧ ∀ u ∈ U, R u = 0
    · exact CFSG.RankThree.PartOne.dicksonDerived_of_threeSingular R hR hT
    · refine (CFSG.RankThree.PartOne.nonsplit_quasisimple_dicksonDerived R hR (Or.inr h6)
        fun U hU => ?_).2
      by_contra hall
      push Not at hall
      exact hT ⟨U, by omega, hall⟩
  · exact CFSG.RankThree.PartOne.dicksonDerived_of_threeSingular R hR
      (CFSG.RankThree.PartOne.exists_threeSingular_of_dim R hR hm4 (by omega))

omit [Finite K] [CharP K 2] in
private theorem tbjOmBlkZ_X_sub_one_mem_primaryFactors {x : V ≃ₗ[K] V}
    (h : 0 < finrank K (fixedSpace x)) : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
  by_contra hnot
  rw [fixedSpace_eq_bot_of_not_mem hnot, finrank_bot] at h
  exact lt_irrefl 0 h

omit [Finite K] [CharP K 2] in
theorem mem_supportedBlock_of_fixes {x g : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgx : g * x = x * g)
    (hgR : ∀ v, (∀ w ∈ fixedSpace x, QuadraticMap.polar Q w v = 0) → g v = v) :
    g ∈ supportedBlock Q x (X - 1) := by
  refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr
    ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO, fun v => ?_⟩,
    fun s hs => hgR s fun w hw => hx.fixed_others.2 w hw s hs⟩
  exact congrArg (fun f : V ≃ₗ[K] V => f v) hgx

omit [CharP K 2] in
private theorem tbjOmBlkZ_mem_supportedFixedDerived_of_dicksonDerived {x g : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hp : Odd p) (hQ : (polarBilin Q).Nondegenerate)
    (hD : CFSG.RankThree.PartOne.DicksonDerived (Q.comp (fixedSpace x).subtype)
      hx.polarBilin_fixed_nondegenerate)
    (hX : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap) (hg : g ∈ orthDerived Q)
    (hgB : g ∈ supportedBlock Q x (X - 1)) : g ∈ supportedFixedDerived Q x := by
  have hdick : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ
      ⟨g, orthDerived_le_orthogonalGroup_of_commutator Q hg⟩ = 1 :=
    dicksonHom_apply_orthDerived_eq_one hQ hg
  have hdickW : CFSG.RankThree.OrthogonalInvolutions.dicksonHom (Q.comp (fixedSpace x).subtype)
      hx.polarBilin_fixed_nondegenerate
      ⟨isometryRestrictFixed Q x ⟨g, supportedBlock_le_isometryCentralizer (X - 1) hgB⟩,
        isometryRestrictFixed_mem_orthogonalGroup _⟩ = 1 := by
    rw [← hx.dicksonHom_eq_restrict_of_mem_supportedBlock hp hQ hX hgB]
    exact hdick
  refine mem_supportedFixedDerived.mpr ⟨hgB, ?_⟩
  rw [← isometryRestrictFixed_restrictFixed (Q := Q) (x := x) ⟨g, hgB⟩]
  exact hD _ hdickW

private theorem tbjOmBlkZ_mem_supportedFixedDerived {x g : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hp : Odd p) (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ finrank K (fixedSpace x)) (hg : g ∈ orthDerived Q) (hgx : g * x = x * g)
    (hgR : ∀ v, (∀ w ∈ fixedSpace x, QuadraticMap.polar Q w v = 0) → g v = v) :
    g ∈ supportedFixedDerived Q x :=
  tbjOmBlkZ_mem_supportedFixedDerived_of_dicksonDerived hx hp hQ
    (tbjOmBlkZ_dicksonDerived _ hx.polarBilin_fixed_nondegenerate h5)
    (tbjOmBlkZ_X_sub_one_mem_primaryFactors (by omega)) hg
    (mem_supportedBlock_of_fixes hx (orthDerived_le_orthogonalGroup hg) hgx hgR)

theorem TBJOmData.piece_le_fixedSpace (Δ : TBJOmData Q p A r)
    (f₀ : Fin r → Multiplicative (ZMod p)) {i : Fin r} (hi : toAdd (f₀ i) = 0) :
    Δ.F.U i ≤ fixedSpace (Δ.τ f₀) := by
  intro u hu
  rw [Δ.mem_fixedSpace_iff]
  intro j hj u' hu'
  exact Δ.F.orth j i (fun h => hj (h ▸ hi)) u' hu' u hu

private theorem tbjOmBlkZ_polar_piece_eq_zero [Fact p.Prime] (Δ : TBJOmData Q p A r) {v : V}
    (hv : ∀ a ∈ A, a v = v) (j : Fin r) {u : V} (hu : u ∈ Δ.F.U j) :
    QuadraticMap.polar Q u v = 0 := by
  have hτ : Δ.τ (fun _ => ofAdd (1 : ZMod p)) ∈ A := Δ.τ_range.le ⟨_, rfl⟩
  have h := (Δ.mem_fixedSpace_iff (fun _ => ofAdd (1 : ZMod p)) v).mp
    (mem_fixedSpace.mpr (hv _ hτ))
  exact h j (by simp) u hu

omit [Finite K] [FiniteDimensional K V] in
theorem TBJOmData.finrank_piece (Δ : TBJOmData Q p A r) (j : Fin r) :
    finrank K (Δ.F.U j) = 2 := by
  rw [← Δ.θ_range j, LinearMap.finrank_range_of_inj (Δ.θ_inj j), Δ.finrank_D]

theorem TBJOmData.fixedSpace_eq_polarPerp (Δ : TBJOmData Q p A r)
    (f₀ : Fin r → Multiplicative (ZMod p)) :
    fixedSpace (Δ.τ f₀) =
      polarPerp Q (⨆ j ∈ Finset.univ.filter (fun j => toAdd (f₀ j) ≠ 0), Δ.F.U j) := by
  ext v
  rw [Δ.mem_fixedSpace_iff f₀ v, mem_polarPerp_iff]
  constructor
  · intro h y hy
    rw [iSup_subtype'] at hy
    refine Submodule.iSup_induction
      (p := fun j : {j : Fin r // j ∈ Finset.univ.filter (fun j => toAdd (f₀ j) ≠ 0)} =>
        Δ.F.U j.1) (motive := fun y => QuadraticMap.polar Q y v = 0) hy ?_ ?_ ?_
    · rintro ⟨j, hj⟩ x hx
      exact h j (Finset.mem_filter.mp hj).2 x hx
    · simp
    · intro x y hx hy
      rw [QuadraticMap.polar_add_left, hx, hy, add_zero]
  · intro h j hj u hu
    exact h u (le_iSup₂_of_le
      (f := fun j (_ : j ∈ Finset.univ.filter (fun j => toAdd (f₀ j) ≠ 0)) => Δ.F.U j)
      j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) le_rfl hu)

theorem TBJOmData.fixedSpace_eq_polarPerp_one_active (Δ : TBJOmData Q p A r)
    {f0 : Fin r → Multiplicative (ZMod p)} {j : Fin r}
    (hj : f0 j ≠ 1) (hf : ∀ i, i ≠ j → f0 i = 1) :
    fixedSpace (Δ.τ f0) = polarPerp Q (Δ.F.U j) := by
  rw [Δ.fixedSpace_eq_polarPerp]
  have hfilter : Finset.univ.filter (fun i : Fin r => toAdd (f0 i) ≠ 0) = {j} := by
    apply Finset.ext
    intro i
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hne⟩
      by_contra hij
      exact hne (by rw [hf i hij, toAdd_one])
    · intro hmem
      refine ⟨Finset.mem_univ i, ?_⟩
      rw [hmem]
      intro h0
      exact hj (toAdd.injective (h0.trans toAdd_one.symm))
  rw [hfilter, Finset.iSup_singleton]

theorem TBJOmData.finrank_fixedSpace_one_active (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate)
    {f0 : Fin r → Multiplicative (ZMod p)} {j : Fin r}
    (hj : f0 j ≠ 1) (hf : ∀ i, i ≠ j → f0 i = 1) :
    finrank K (fixedSpace (Δ.τ f0)) = finrank K V - 2 := by
  rw [Δ.fixedSpace_eq_polarPerp_one_active hj hf, finrank_polarPerp hQ, Δ.finrank_piece]

omit [Finite K] [FiniteDimensional K V] in
theorem TBJOmData.polarPerp_iSup_le_commonFixed (Δ : TBJOmData Q p A r) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, Δ.F.U j)) : ∀ a ∈ A, a v = v := by
  intro a ha
  rw [← Δ.τ_range] at ha
  obtain ⟨f, rfl⟩ := ha
  rw [Δ.τ_eq, Δ.F.fix]
  intro j _ u hu
  exact mem_polarPerp_iff.mp hv u (Submodule.mem_iSup_of_mem j hu)

theorem TBJOmData.isPlusType_piece_iff_dvd_card_sub_one [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q) (i : Fin r) :
    IsPlusType (Q.comp (Δ.F.U i).subtype) ↔ p ∣ Nat.card K - 1 := by
  classical
  let f : Fin r → Multiplicative (ZMod p) := fun j => if j = i then ofAdd 1 else 1
  have hfi : toAdd (f i) = 1 := by simp [f]
  have hfi0 : toAdd (f i) ≠ 0 := by rw [hfi]; exact one_ne_zero
  have hpi0 : toAdd (piMul r p f) i ≠ 0 := by
    rw [piMul_apply, toAdd_ofAdd]
    exact hfi0
  have hmap : ∀ u ∈ Δ.F.U i, Δ.τ f u ∈ Δ.F.U i := by
    intro u hu
    rw [Δ.τ_eq]
    exact Δ.F.mapsTo (piMul r p f) i u hu
  have hinv : ∀ u ∈ Δ.F.U i, (Δ.τ f).symm u ∈ Δ.F.U i := by
    intro u hu
    rw [show (Δ.τ f).symm = (Δ.τ f)⁻¹ from rfl, ← map_inv (Δ.τ) f, Δ.τ_eq]
    exact Δ.F.mapsTo (piMul r p f⁻¹) i u hu
  let g : Δ.F.U i ≃ₗ[K] Δ.F.U i := restrictEquiv (Δ.F.U i) (Δ.τ f) hmap hinv
  have hgcoe : ∀ u : Δ.F.U i, (g u : V) = Δ.τ f u := fun u =>
    coe_restrictEquiv (Δ.F.U i) (Δ.τ f) hmap hinv u
  have hgp : g ^ p = 1 := by
    have hcoepow : ∀ (n : ℕ) (u : Δ.F.U i),
        (((g ^ n) u : Δ.F.U i) : V) = ((Δ.τ f) ^ n) u := by
      intro n
      induction n with
      | zero => intro u; simp
      | succ n ih =>
        intro u
        rw [pow_succ, LinearEquiv.mul_apply, ih (g u), hgcoe]
        rfl
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    rw [hcoepow p u, Δ.τ_eq, Δ.F.pow_p]
    rfl
  have hg1 : g ≠ 1 := by
    intro hg
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Δ.F.ne_bot i)
    have hgu : g ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [hg]; rfl
    have hL : Δ.τ f u = u := by
      rw [← hgcoe ⟨u, hu⟩]
      exact congrArg Subtype.val hgu
    exact hu0 (Δ.F.fpf (piMul r p f) i hpi0 u hu (by simpa [Δ.τ_eq] using hL))
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Δ.F.U i).subtype) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro u
    change Q ((g u : Δ.F.U i) : V) = Q (u : V)
    rw [hgcoe]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup (hA (Δ.τ_range.le ⟨f, rfl⟩))) (u : V)
  have hQU : (polarBilin (Q.comp (Δ.F.U i).subtype)).Nondegenerate :=
    CFSG.ComponentClassification.UnbalancedCatalog.nondegenerate_polarBilin_comp_subtype
      (S := Δ.F.U i) fun u hu hperp => Δ.F.nondeg i u hu fun v hv => by
        rw [QuadraticMap.polar_comm]
        exact hperp v hv
  have hplane := CFSG.LocalAnalysis.GLTheoremA.H81Orth.int_dvd_of_plane hQU
    (Δ.finrank_piece i) (Fact.out : p.Prime) hp2 hgO hgp hg1
  have hboth : ¬ ((p : ℤ) ∣ (Nat.card K : ℤ) - 1 ∧
      (p : ℤ) ∣ (Nat.card K : ℤ) + 1) := by
    rintro ⟨h1, h2⟩
    have h3 : (p : ℤ) ∣ 2 := by
      have := dvd_sub h2 h1
      rwa [show (Nat.card K : ℤ) + 1 - ((Nat.card K : ℤ) - 1) = 2 by ring] at this
    have hnat : p ∣ 2 := Int.natCast_dvd_natCast.mp h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hnat)
  constructor
  · intro hplus
    have hq : 1 ≤ Nat.card K := by
      have hpos : 0 < Nat.card K := Nat.card_pos
      omega
    have hZ' : (p : ℤ) ∣ ((Nat.card K - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hq, Nat.cast_one]
      exact hplane.1 hplus
    exact Int.natCast_dvd_natCast.mp hZ'
  · intro hdvd
    by_contra hnot
    refine hboth ⟨?_, hplane.2 hnot⟩
    have hq : 1 ≤ Nat.card K := by
      have hpos : 0 < Nat.card K := Nat.card_pos
      omega
    have h := Int.natCast_dvd_natCast.mpr hdvd
    rwa [Nat.cast_sub hq, Nat.cast_one] at h

private theorem tbjOmBlkZ_tau_apply_of_mem_fixedSpace (Δ : TBJOmData Q p A r)
    {f₀ f : Fin r → Multiplicative (ZMod p)} (hf : ∀ i, toAdd (f₀ i) = 0 → f i = 1) {v : V}
    (hv : v ∈ fixedSpace (Δ.τ f₀)) : Δ.τ f v = v := by
  rw [Δ.mem_fixedSpace_iff] at hv
  refine mem_fixedSpace.mp ((Δ.mem_fixedSpace_iff f v).mpr fun j hj u hu =>
    hv j (fun h0 => hj ?_) u hu)
  rw [hf j h0, toAdd_one]

private theorem tbjOmBlkZ_five_le_finrank [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v) (f₀ : Fin r → Multiplicative (ZMod p))
    {i k : Fin r} (hik : i ≠ k) (hi : toAdd (f₀ i) = 0) (hk : toAdd (f₀ k) = 0) :
    5 ≤ finrank K (fixedSpace (Δ.τ f₀)) := by
  obtain ⟨v, hv0, hv⟩ := hW
  have hτ : Δ.τ f₀ ∈ A := Δ.τ_range.le ⟨f₀, rfl⟩
  have hle : Δ.F.U i ⊔ Δ.F.U k ⊔ K ∙ v ≤ fixedSpace (Δ.τ f₀) :=
    sup_le (sup_le (TBJOmData.piece_le_fixedSpace Δ f₀ hi) (TBJOmData.piece_le_fixedSpace Δ f₀ hk))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr (mem_fixedSpace.mpr (hv _ hτ)))
  have heq := tbjOmBlkZ_finrank_sup_sup_span (Δ.F.nondeg i) (Δ.F.nondeg k) (Δ.F.orth i k hik)
    hv0 (fun u hu => tbjOmBlkZ_polar_piece_eq_zero Δ hv i hu)
    (fun u hu => tbjOmBlkZ_polar_piece_eq_zero Δ hv k hu)
  rw [TBJOmData.finrank_piece, TBJOmData.finrank_piece] at heq
  have := Submodule.finrank_mono hle
  omega

private theorem tbjOmBlkZ_five_le_finrank_of_three (Δ : TBJOmData Q p A r)
    (f₀ : Fin r → Multiplicative (ZMod p)) {i k l : Fin r} (hik : i ≠ k) (hli : l ≠ i)
    (hlk : l ≠ k) (hi : toAdd (f₀ i) = 0) (hk : toAdd (f₀ k) = 0) (hl : toAdd (f₀ l) = 0) :
    5 ≤ finrank K (fixedSpace (Δ.τ f₀)) := by
  obtain ⟨v, hvl, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Δ.F.ne_bot l)
  have hle : Δ.F.U i ⊔ Δ.F.U k ⊔ K ∙ v ≤ fixedSpace (Δ.τ f₀) :=
    sup_le (sup_le (TBJOmData.piece_le_fixedSpace Δ f₀ hi) (TBJOmData.piece_le_fixedSpace Δ f₀ hk))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr (TBJOmData.piece_le_fixedSpace Δ f₀ hl hvl))
  have heq := tbjOmBlkZ_finrank_sup_sup_span (Δ.F.nondeg i) (Δ.F.nondeg k) (Δ.F.orth i k hik)
    hv0 (fun u hu => Δ.F.orth i l (Ne.symm hli) u hu v hvl)
    (fun u hu => Δ.F.orth k l (Ne.symm hlk) u hu v hvl)
  rw [TBJOmData.finrank_piece, TBJOmData.finrank_piece] at heq
  have := Submodule.finrank_mono hle
  omega

private theorem tbjOmBlkZ_swap [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) (h5 : 5 ≤ finrank K (fixedSpace (Δ.τ f₀)))
    {i k : Fin r} (hik : i ≠ k) (hi : toAdd (f₀ i) = 0) (hk : toAdd (f₀ k) = 0) :
    ∃ n ∈ supportedFixedDerived Q (Δ.τ f₀),
      ∀ f, n * Δ.τ f * n⁻¹ = Δ.τ (permAut (Equiv.swap i k) f) := by
  have hx := Δ.oddOrderIsometry hp2 hQ hA f₀
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨w, hwΩ, hwfix, hwconj⟩ := Δ.swapMove i k hik
  have hwx : w * Δ.τ f₀ = Δ.τ f₀ * w := by
    have h := hwconj f₀
    rw [tbjOmBlkZ_permAut_swap_apply (toAdd.injective (hi.trans hk.symm))] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  refine ⟨w, tbjOmBlkZ_mem_supportedFixedDerived hx hp hQ h5 hwΩ hwx fun v hv => ?_, hwconj⟩
  exact hwfix v (fun u hu => hv u (TBJOmData.piece_le_fixedSpace Δ f₀ hi hu))
    (fun u hu => hv u (TBJOmData.piece_le_fixedSpace Δ f₀ hk hu))

theorem TBJOmData.blockZ_comm [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ f : Fin r → Multiplicative (ZMod p)) (hf : ∀ i, toAdd (f₀ i) = 0 → f i = 1) :
    ∀ j ∈ supportedFixedDerived Q (Δ.τ f₀), Δ.τ f * j = j * Δ.τ f := by
  intro j hj
  have hx := Δ.oddOrderIsometry hp2 hQ hA f₀
  obtain ⟨hjM, hjR⟩ := mem_supportedBlock.mp (supportedFixedDerived_le_supportedBlock hj)
  have hjc : j ∈ Subgroup.centralizer ({Δ.τ f₀} : Set (V ≃ₗ[K] V)) :=
    (Subgroup.mem_inf.mp hjM).2
  have hτc : Δ.τ f ∈ Subgroup.centralizer ({Δ.τ f₀} : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mul_comm]
  exact tbjOmBlkZ_commute_of_isCompl hx.fixed_others.1
    (fun u hu => tbjOmBlkZ_tau_apply_of_mem_fixedSpace Δ hf hu)
    (fun s hs => mem_othersSpace_of_apply hτc hs) (fun u hu => mem_fixedSpace_of_apply hjc hu)
    hjR

theorem TBJOmData.blockZ [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v) (f₀ : Fin r → Multiplicative (ZMod p)) :
    (∀ i k : Fin r, i ≠ k → toAdd (f₀ i) = 0 → toAdd (f₀ k) = 0 →
      ∃ n ∈ supportedFixedDerived Q (Δ.τ f₀),
        ∀ f, n * Δ.τ f * n⁻¹ = Δ.τ (permAut (Equiv.swap i k) f)) ∧
    (2 ≤ Nat.card {i : Fin r // toAdd (f₀ i) = 0} → ∀ i : Fin r, toAdd (f₀ i) = 0 →
      ∃ n ∈ supportedFixedDerived Q (Δ.τ f₀), ∀ f, n * Δ.τ f * n⁻¹ = Δ.τ (sgnAut i f)) ∧
    (∀ f : Fin r → Multiplicative (ZMod p), (∀ i, toAdd (f₀ i) = 0 → f i = 1) →
      ∀ j ∈ supportedFixedDerived Q (Δ.τ f₀), Δ.τ f * j = j * Δ.τ f) ∧
    (2 ≤ Nat.card {i : Fin r // toAdd (f₀ i) = 0} → 4 < finrank K (fixedSpace (Δ.τ f₀))) := by
  have hx := Δ.oddOrderIsometry hp2 hQ hA f₀
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hτA : Δ.τ f₀ ∈ A := Δ.τ_range.le ⟨f₀, rfl⟩
  refine ⟨fun i k hik hi hk => tbjOmBlkZ_swap hp2 Δ hQ hA f₀
    (tbjOmBlkZ_five_le_finrank Δ hW f₀ hik hi hk) hik hi hk, fun h2 i hi => ?_,
    fun f hf => Δ.blockZ_comm hp2 hQ hA f₀ f hf, fun h2 => ?_⟩
  ·
    obtain ⟨i₁, i₂, h12, hi₁, hi₂⟩ := tbjOmBlkZ_exists_pair_ne h2
    obtain ⟨w, hwΩ, hwfix, hwconj⟩ := Δ.signMove hW i
    have hwx : w * Δ.τ f₀ = Δ.τ f₀ * w := by
      have h := hwconj f₀
      rw [tbjOmBlkZ_sgnAut_apply (toAdd.injective (hi.trans toAdd_one.symm))] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    refine ⟨w, tbjOmBlkZ_mem_supportedFixedDerived hx hp hQ
      (tbjOmBlkZ_five_le_finrank Δ hW f₀ h12 hi₁ hi₂) hwΩ hwx fun v hv => ?_, hwconj⟩
    exact hwfix v (fun u hu => hv u (TBJOmData.piece_le_fixedSpace Δ f₀ hi hu))
      (fun u hu => hv u (mem_fixedSpace.mpr (hu _ hτA)))
  ·
    obtain ⟨i₁, i₂, h12, hi₁, hi₂⟩ := tbjOmBlkZ_exists_pair_ne h2
    have := tbjOmBlkZ_five_le_finrank Δ hW f₀ h12 hi₁ hi₂
    omega

theorem TBJOmData.blockZ_nf [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) (h3 : 3 ≤ Nat.card {i : Fin r // toAdd (f₀ i) = 0}) :
    (∀ i k : Fin r, i ≠ k → toAdd (f₀ i) = 0 → toAdd (f₀ k) = 0 →
      ∃ n ∈ supportedFixedDerived Q (Δ.τ f₀),
        ∀ f, n * Δ.τ f * n⁻¹ = Δ.τ (permAut (Equiv.swap i k) f)) ∧
    (∀ f : Fin r → Multiplicative (ZMod p), (∀ i, toAdd (f₀ i) = 0 → f i = 1) →
      ∀ j ∈ supportedFixedDerived Q (Δ.τ f₀), Δ.τ f * j = j * Δ.τ f) ∧
    4 < finrank K (fixedSpace (Δ.τ f₀)) := by
  refine ⟨fun i k hik hi hk => ?_, fun f hf => Δ.blockZ_comm hp2 hQ hA f₀ f hf, ?_⟩
  · obtain ⟨l, hli, hlk, hl⟩ := tbjOmBlkZ_exists_third h3 i k
    exact tbjOmBlkZ_swap hp2 Δ hQ hA f₀
      (tbjOmBlkZ_five_le_finrank_of_three Δ f₀ hik hli hlk hi hk hl) hik hi hk
  · obtain ⟨i₁, i₂, h12, hi₁, hi₂⟩ :=
      tbjOmBlkZ_exists_pair_ne (P := fun i : Fin r => toAdd (f₀ i) = 0) (by omega)
    obtain ⟨l, hl1, hl2, hl⟩ := tbjOmBlkZ_exists_third h3 i₁ i₂
    have := tbjOmBlkZ_five_le_finrank_of_three Δ f₀ h12 hl1 hl2 hi₁ hi₂ hl
    omega

theorem TBJOmData.blockZ_dinv [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) (h5 : 5 ≤ finrank K (fixedSpace (Δ.τ f₀)))
    {i k : Fin r} (hik : i ≠ k) (hi : toAdd (f₀ i) = 0) (hk : toAdd (f₀ k) = 0) :
    ∃ n ∈ supportedFixedDerived Q (Δ.τ f₀),
      ∀ f, n * Δ.τ f * n⁻¹ = Δ.τ (dinv i k f) := by
  have hx := Δ.oddOrderIsometry hp2 hQ hA f₀
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨w, hwΩ, hwfix, hwconj⟩ := Δ.dinvMove i k hik
  have hwx : w * Δ.τ f₀ = Δ.τ f₀ * w := by
    have h := hwconj f₀
    rw [tbjOmBlkZ_dinv_apply hik (toAdd.injective (hi.trans toAdd_one.symm))
      (toAdd.injective (hk.trans toAdd_one.symm))] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  exact ⟨w, tbjOmBlkZ_mem_supportedFixedDerived hx hp hQ h5 hwΩ hwx fun v hv =>
    hwfix v (fun u hu => hv u (TBJOmData.piece_le_fixedSpace Δ f₀ hi hu))
      (fun u hu => hv u (TBJOmData.piece_le_fixedSpace Δ f₀ hk hu)), hwconj⟩

theorem TBJOmData.blockZ_sign [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p))
    (h4 : finrank K (fixedSpace (Δ.τ f₀)) = 4)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v)
    (hnonsplit : ∀ S : Submodule K (fixedSpace (Δ.τ f₀)), finrank K S = 2 →
      ∃ x ∈ S, (Q.comp (fixedSpace (Δ.τ f₀)).subtype) x ≠ 0)
    {i : Fin r} (hi : toAdd (f₀ i) = 0) :
    ∃ n ∈ supportedFixedDerived Q (Δ.τ f₀),
      ∀ f, n * Δ.τ f * n⁻¹ = Δ.τ (sgnAut i f) := by
  have hx := Δ.oddOrderIsometry hp2 hQ hA f₀
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨w, hwΩ, hwfix, hwconj⟩ := Δ.signMove hW i
  have hwx : w * Δ.τ f₀ = Δ.τ f₀ * w := by
    have h := hwconj f₀
    rw [tbjOmBlkZ_sgnAut_apply (toAdd.injective (hi.trans toAdd_one.symm))] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hD : CFSG.RankThree.PartOne.DicksonDerived (Q.comp (fixedSpace (Δ.τ f₀)).subtype)
      hx.polarBilin_fixed_nondegenerate := by
    have hts : ∀ U : Submodule K (fixedSpace (Δ.τ f₀)),
        finrank K U = finrank K (fixedSpace (Δ.τ f₀)) / 2 →
          ∃ u ∈ U, (Q.comp (fixedSpace (Δ.τ f₀)).subtype) u ≠ 0 := by
      intro U hU
      rw [h4] at hU
      norm_num at hU
      exact hnonsplit U hU
    exact (CFSG.RankThree.PartOne.nonsplit_quasisimple_dicksonDerived _
      hx.polarBilin_fixed_nondegenerate (Or.inl h4) hts).2
  refine ⟨w, tbjOmBlkZ_mem_supportedFixedDerived_of_dicksonDerived hx hp hQ hD
    (tbjOmBlkZ_X_sub_one_mem_primaryFactors (by omega)) hwΩ ?_, hwconj⟩
  refine mem_supportedBlock_of_fixes hx (orthDerived_le_orthogonalGroup hwΩ) hwx ?_
  intro v hv
  refine hwfix v (fun u hu => hv u (TBJOmData.piece_le_fixedSpace Δ f₀ hi hu)) ?_
  intro u hu
  exact hv u (mem_fixedSpace.mpr (hu _ (Δ.τ_range.le ⟨f₀, rfl⟩)))

theorem TBJOmData.inactive_plane_of_minus [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (hr : 1 ≤ r) (hdim : finrank K V = 2 * (r + 1)) (hminus : ¬ IsPlusType Q)
    (hrow : p ∣ Nat.card K - 1 ∨ Odd r ∧ p ∣ Nat.card K + 1) :
    let S := ⨆ i, Δ.F.U i
    let W := polarPerp Q S
    (∀ v, v ∈ W ↔ ∀ a ∈ A, a v = v) ∧ finrank K W = 2 ∧
      (polarBilin (Q.comp W.subtype)).Nondegenerate ∧ IsCompl W S ∧
      ∀ i, IsPlusType (Q.comp W.subtype) ↔ ¬ IsPlusType (Q.comp (Δ.F.U i).subtype) := by
  classical
  dsimp only
  set S : Submodule K V := ⨆ i, Δ.F.U i with hSdef
  set W : Submodule K V := polarPerp Q S with hWdef
  have hIndep : iSupIndep Δ.F.U := Δ.F.iSupIndep_pieces
  have hSdim : finrank K S = 2 * r := by
    rw [hSdef, TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep hIndep]
    rw [Finset.sum_congr rfl (fun i _ => Δ.finrank_piece i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hWdim : finrank K W = 2 := by
    rw [hWdef, finrank_polarPerp hQ S, hSdim, hdim]
    omega
  have hfix : fixedSpace (Δ.τ (fun _ => ofAdd (1 : ZMod p))) = W := by
    rw [Δ.fixedSpace_eq_polarPerp]
    rw [hWdef, hSdef]
    congr 1
    ext v
    simp
  have hx := Δ.oddOrderIsometry hp2 hQ hA (fun _ => ofAdd (1 : ZMod p))
  have hWnd : (polarBilin (Q.comp W.subtype)).Nondegenerate := by
    rw [← hfix]
    exact hx.polarBilin_fixed_nondegenerate
  have hWperp : polarPerp Q W = S := by
    rw [hWdef]
    simpa [polarPerp] using
      (LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin Q) S)
  have hcompl : IsCompl W S := by
    have h := isCompl_polarPerp (Q := Q) (W := W) hWnd
    rwa [hWperp] at h
  have hSnd : (polarBilin (Q.comp S.subtype)).Nondegenerate := by
    have hdisjS : Disjoint S (LinearMap.BilinForm.orthogonal (polarBilin Q) S) := by
      rw [Submodule.disjoint_def]
      intro x hxS hxperp
      have hxV : ∀ y, QuadraticMap.polar Q y x = 0 := by
        intro y
        have hy : y ∈ W ⊔ S := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
        obtain ⟨w, hw, s, hs, rfl⟩ := Submodule.mem_sup.mp hy
        rw [QuadraticMap.polar_add_left]
        have h1 : QuadraticMap.polar Q w x = 0 := by
          rw [QuadraticMap.polar_comm]
          rw [hWdef] at hw
          exact mem_polarPerp_iff.mp hw x hxS
        have h2 : QuadraticMap.polar Q s x = 0 := by
          exact mem_polarPerp_iff.mp hxperp s hs
        rw [h1, h2, add_zero]
      refine hQ.1 x fun y => ?_
      simpa [polarBilin_apply_apply, QuadraticMap.polar_comm] using hxV y
    rw [polarBilin_comp_subtype_cent]
    exact LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal _
      (isRefl_polarBilin Q) hdisjS
  have horth : ∀ a ∈ W, ∀ b ∈ S, QuadraticMap.polar Q a b = 0 := by
    intro a ha b hb
    rw [hWdef] at ha
    rw [QuadraticMap.polar_comm]
    exact mem_polarPerp_iff.mp ha b hb
  have hiso := CFSG.RankThree.PartOne.K159.isometryEquivSup Q W S hcompl.disjoint horth
  have htotal : IsPlusType Q ↔
      (IsPlusType (Q.comp W.subtype) ↔ IsPlusType (Q.comp S.subtype)) := by
    rw [← isPlusType_comp_top_iff (Q := Q), ← hcompl.sup_eq_top]
    exact (isPlusType_congr hiso).trans
      (CFSG.RankThree.PartOne.K159.isPlusType_prod_iff hWnd hSnd
        (d₁ := 1) (d₂ := r) le_rfl hr hWdim hSdim)
  have hcommon : ∀ v, v ∈ W ↔ ∀ a ∈ A, a v = v := by
    intro v
    constructor
    · intro hv
      rw [hWdef] at hv
      rw [hSdef] at hv
      exact Δ.polarPerp_iSup_le_commonFixed hv
    · intro hv
      rw [← hfix]
      exact mem_fixedSpace.mpr (hv _ (Δ.τ_range.le ⟨fun _ => ofAdd 1, rfl⟩))
  refine ⟨hcommon, hWdim, hWnd, hcompl, ?_⟩
  by_cases hq1 : p ∣ Nat.card K - 1
  · have hpiecePlus : ∀ i, IsPlusType (Q.comp (Δ.F.U i).subtype) := fun i =>
      (Δ.isPlusType_piece_iff_dvd_card_sub_one hp2 hA i).mpr hq1
    have hSplus : IsPlusType (Q.comp S.subtype) := by
      choose v hv0 hvQ using fun i =>
        CFSG.LocalAnalysis.GLTheoremA.H81Orth.exists_singular_of_isPlusType
          (Δ.finrank_piece i) (hpiecePlus i)
      let w : Fin r → V := fun i => (v i : V)
      have hw0 : ∀ i, w i ≠ 0 := fun i h => hv0 i (Subtype.ext h)
      have hwQ : ∀ i, Q (w i) = 0 := fun i => hvQ i
      have hli : LinearIndependent K w :=
        iSupIndep.linearIndependent (p := Δ.F.U) hIndep (v := w)
          (fun i => by simpa [w] using (v i).2) hw0
      let T : Submodule K V := Submodule.span K (Set.range w)
      have hTsing : ∀ x ∈ T, Q x = 0 := by
        intro x hx
        have hx' : x ∈ Submodule.span K (Set.range w) := by simpa [T] using hx
        refine CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span
          (S := Set.range w) ?_ ?_ hx'
        · rintro _ ⟨i, rfl⟩
          exact hwQ i
        · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
          by_cases hij : i = j
          · subst hij
            rw [QuadraticMap.polar_self, hwQ i, smul_zero]
          · exact Δ.F.orth i j hij (v i : V) (v i).2 (v j : V) (v j).2
      have hTdim : finrank K T = r := by
        rw [show T = Submodule.span K (Set.range w) from rfl, finrank_span_eq_card hli,
          Fintype.card_fin]
      have hTS : T ≤ S := by
        rw [show T = Submodule.span K (Set.range w) from rfl]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        rw [hSdef]
        simpa [w] using Submodule.mem_iSup_of_mem i (v i).2
      let T' : Submodule K ↥S := T.comap S.subtype
      refine ⟨T', ?_, ?_⟩
      · rw [show T' = T.comap S.subtype from rfl,
          (Submodule.comapSubtypeEquivOfLe hTS).finrank_eq, hTdim, hSdim]
      · intro x hx
        exact hTsing (x : V) hx
    have hWnot : ¬ IsPlusType (Q.comp W.subtype) := by
      intro hWplus
      exact hminus (htotal.mpr ⟨fun _ => hSplus, fun _ => hWplus⟩)
    intro i
    exact ⟨fun hW _ => hWnot hW, fun hnot => absurd (hpiecePlus i) hnot⟩
  · have hodd : Odd r := by
      rcases hrow with h | ⟨h, -⟩
      · exact absurd h hq1
      · exact h
    have hpieceNot : ∀ i, ¬ IsPlusType (Q.comp (Δ.F.U i).subtype) := by
      intro i hplus
      exact hq1 ((Δ.isPlusType_piece_iff_dvd_card_sub_one hp2 hA i).mp hplus)
    have hps : IsPlaneSystem Q Δ.F.U := by
      refine ⟨Δ.finrank_piece, ?_, hpieceNot, Δ.F.orth⟩
      intro j
      exact CFSG.ComponentClassification.UnbalancedCatalog.nondegenerate_polarBilin_comp_subtype
        (S := Δ.F.U j) fun u hu hperp => Δ.F.nondeg j u hu fun v hv => by
          rw [QuadraticMap.polar_comm]
          exact hperp v hv
    have hSnot : ¬ IsPlusType (Q.comp S.subtype) := by
      intro hSplus
      have hEven : Even r := by
        have h' : IsPlusType
            (Q.comp (⨆ j ∈ (Finset.univ : Finset (Fin r)), Δ.F.U j).subtype) := by
          have hEq : (⨆ j ∈ (Finset.univ : Finset (Fin r)), Δ.F.U j) = ⨆ j, Δ.F.U j := by
            ext v
            simp
          rw [hEq, ← hSdef]
          exact hSplus
        have := (hps.isPlusType_biSup_iff Finset.univ).mp h'
        simpa using this
      exact (Nat.not_even_iff_odd.mpr hodd) hEven
    have hWplus : IsPlusType (Q.comp W.subtype) := by
      by_contra hW
      exact hminus (htotal.mpr ⟨fun h => absurd h hW, fun h => absurd h hSnot⟩)
    intro i
    exact ⟨fun _ => hpieceNot i, fun _ => hWplus⟩

end OrthTorus

end CFSG.StandardType

end
