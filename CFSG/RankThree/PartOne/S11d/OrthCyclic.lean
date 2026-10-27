module

public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.RankThree.PartOne.S11d.PSLRank
public import CFSG.RankThree.CentralCover.SteinbergBNOrthogonalRepeatedSummands
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.RankThree.PartOne.S11d.LieCentralizerGL
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.CentralCover
  CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.FieldFix

section Coord

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {m : ℕ} {R W : Type*} [AddCommGroup R] [Module K R] [AddCommGroup W] [Module K W]
  (ψ : V ≃ₗ[K] R × (Fin m → W))

theorem coordPi_single (gs : Fin m → (W ≃ₗ[K] W)) (i : Fin m) (w : W) :
    coordAut ψ (piAut K W m gs) (ψ.symm (0, Pi.single i w)) =
      ψ.symm (0, Pi.single i (gs i w)) := by
  rw [coordAut_symm_apply]
  congr 2
  funext j
  by_cases hj : j = i
  · subst hj
    simp [piAut_apply]
  · simp [piAut_apply, hj]

end Coord

section Rank

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] in
theorem mem_omegaGroup_of_pow_eq_one (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hodd : Odd p) {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgp : g ^ p = 1) : g ∈ omegaGroup Q hQ := by
  refine mem_omegaGroup.mpr ⟨hg, ?_⟩
  have h2 : ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 := by decide
  have hz : dicksonHom Q hQ ⟨g, hg⟩ = 1 := by
    have hzp : (dicksonHom Q hQ ⟨g, hg⟩) ^ p = 1 := by
      rw [← map_pow]
      have : (⟨g, hg⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) ^ p = 1 := Subtype.ext hgp
      rw [this, map_one]
    obtain ⟨k, hk⟩ := hodd
    have : (dicksonHom Q hQ ⟨g, hg⟩) ^ (2 * k + 1) = dicksonHom Q hQ ⟨g, hg⟩ := by
      rw [pow_succ, pow_mul, h2, one_pow, one_mul]
    rw [← this, ← hk]
    exact hzp
  rw [dicksonHom_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff,
    ZMod.natCast_eq_zero_iff_even] at hz
  exact hz

theorem mem_orthDerived_of_pow_eq_one (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hodd : Odd p)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgp : g ^ p = 1) :
    g ∈ orthDerived Q :=
  omegaGroup_le_orthDerived hQ hT (mem_omegaGroup_of_pow_eq_one hQ hodd hg hgp)

omit [Finite K] [CharP K 2] in
theorem nontrivial_of_threeSingular (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Nontrivial V := by
  obtain ⟨U, hU3, -⟩ := hT
  exact Module.nontrivial_of_finrank_pos (R := K)
    (lt_of_lt_of_le (by norm_num : 0 < 3) (hU3 ▸ Submodule.finrank_le U))

theorem two_le_pRank_of_repeated (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : V ≃ₗ[K] V} {h : K[X]} (hRS : RepeatedSummands Q x p h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    2 ≤ CFSG.pRank p (ProjOrthDerived Q) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set m := primaryMultiplicity x.toLinearMap h with hmdef
  obtain ⟨R, W, _, _, _, _, QR, QW, ψ, hψ, hQW, hnt, ⟨h₀, hh₀, ho, hx₀⟩, -, -⟩ := hRS
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : NeZero p := ⟨hp.ne_zero⟩
  have hh₀p : h₀ ^ p = 1 := by rw [← ho, pow_orderOf_eq_one]
  have : Nontrivial V := nontrivial_of_threeSingular hT
  obtain ⟨v₀, hv₀⟩ := exists_map_ne_zero hQ
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  let F : (Fin m → (W ≃ₗ[K] W)) →* (V ≃ₗ[K] V) := (coordAut ψ).comp (piAut K W m)
  have hFO : ∀ gs : Fin m → (W ≃ₗ[K] W),
      (∀ i, gs i ∈ TauCeti.QuadraticMap.orthogonalGroup QW) → F gs ∈ O :=
    fun gs hgs => coordAut_piAut_mem hψ hgs
  have hgsO : ∀ j : Fin m, ∀ i, (Pi.mulSingle j h₀ : Fin m → (W ≃ₗ[K] W)) i ∈
      TauCeti.QuadraticMap.orthogonalGroup QW := by
    intro j i
    by_cases hij : i = j
    · subst hij
      simpa using hh₀
    · rw [Pi.mulSingle_eq_of_ne hij]
      exact one_mem _
  have hgO : ∀ j, F (Pi.mulSingle j h₀) ∈ O := fun j => hFO _ (hgsO j)
  have hgp : ∀ j, F (Pi.mulSingle j h₀) ^ p = 1 := by
    intro j
    rw [← map_pow, ← Pi.mulSingle_pow, hh₀p, Pi.mulSingle_one, map_one]
  have hgΩ : ∀ j, F (Pi.mulSingle j h₀) ∈ orthDerived Q := fun j =>
    mem_orthDerived_of_pow_eq_one hQ hT hodd (hgO j) (hgp j)
  let ρ : orthDerived Q →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  have hcomm' : Commute (Pi.mulSingle i₀ h₀ : Fin m → (W ≃ₗ[K] W)) (Pi.mulSingle i₁ h₀) :=
    Pi.mulSingle_commute (f := fun _ : Fin m => W ≃ₗ[K] W) h01 h₀ h₀
  have hcomm : Commute (F (Pi.mulSingle i₀ h₀)) (F (Pi.mulSingle i₁ h₀)) := hcomm'.map F
  refine two_le_pRank_of_two_elements hp (e₁ := ρ ⟨F (Pi.mulSingle i₀ h₀), hgΩ i₀⟩)
    (e₂ := ρ ⟨F (Pi.mulSingle i₁ h₀), hgΩ i₁⟩) ?_ ?_ ?_ ?_
  · exact Commute.map (Subtype.ext hcomm.eq : Commute
      (⟨F (Pi.mulSingle i₀ h₀), hgΩ i₀⟩ : orthDerived Q) ⟨F (Pi.mulSingle i₁ h₀), hgΩ i₁⟩) ρ
  · rw [← map_pow]
    have : (⟨F (Pi.mulSingle i₀ h₀), hgΩ i₀⟩ : orthDerived Q) ^ p = 1 := Subtype.ext (hgp i₀)
    rw [this, map_one]
  · rw [← map_pow]
    have : (⟨F (Pi.mulSingle i₁ h₀), hgΩ i₁⟩ : orthDerived Q) ^ p = 1 := Subtype.ext (hgp i₁)
    rw [this, map_one]
  · intro a b hab
    have hab' : ρ ((⟨F (Pi.mulSingle i₀ h₀), hgΩ i₀⟩ : orthDerived Q) ^ a *
        (⟨F (Pi.mulSingle i₁ h₀), hgΩ i₁⟩ : orthDerived Q) ^ b) = 1 := by
      rw [map_mul, map_zpow, map_zpow]
      exact hab
    have hsc : F (Pi.mulSingle i₀ h₀) ^ a * F (Pi.mulSingle i₁ h₀) ^ b ∈ scalars K V :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hab')
    have hcO : F (Pi.mulSingle i₀ h₀) ^ a * F (Pi.mulSingle i₁ h₀) ^ b ∈ O :=
      mul_mem (zpow_mem (hgO i₀) a) (zpow_mem (hgO i₁) b)
    have hcp : (F (Pi.mulSingle i₀ h₀) ^ a * F (Pi.mulSingle i₁ h₀) ^ b) ^ p = 1 := by
      rw [(hcomm.zpow_zpow a b).mul_pow, ← zpow_natCast (F (Pi.mulSingle i₀ h₀) ^ a),
        ← zpow_natCast (F (Pi.mulSingle i₁ h₀) ^ b), ← zpow_mul, ← zpow_mul, mul_comm a,
        mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hgp, hgp, one_zpow, one_zpow,
        one_mul]
    have hc1 : F (Pi.mulSingle i₀ h₀) ^ a * F (Pi.mulSingle i₁ h₀) ^ b = 1 :=
      eq_one_of_mem_scalars_of_pow hsc hcO hv₀ hodd hcp
    have hFpow : ∀ (j : Fin m) (n : ℤ),
        F (Pi.mulSingle j h₀) ^ n = F (Pi.mulSingle j (h₀ ^ n)) := fun j n => by
      rw [← map_zpow, ← Pi.mulSingle_zpow]
    have hcoord : ∀ (j : Fin m) (n : ℤ) (w : W),
        (F (Pi.mulSingle j h₀) ^ n) (ψ.symm (0, Pi.single j w)) =
          ψ.symm (0, Pi.single j ((h₀ ^ n) w)) := by
      intro j n w
      rw [hFpow]
      change coordAut ψ (piAut K W m (Pi.mulSingle j (h₀ ^ n))) _ = _
      rw [coordPi_single]
      simp
    have hother : ∀ (j j' : Fin m) (n : ℤ) (w : W), j ≠ j' →
        (F (Pi.mulSingle j' h₀) ^ n) (ψ.symm (0, Pi.single j w)) = ψ.symm (0, Pi.single j w) := by
      intro j j' n w hjj
      rw [hFpow]
      change coordAut ψ (piAut K W m (Pi.mulSingle j' (h₀ ^ n))) _ = _
      rw [coordPi_single, Pi.mulSingle_eq_of_ne hjj]
      rfl
    have hext : ∀ n : ℤ, (∀ w : W, (h₀ ^ n) w = w) → (p : ℤ) ∣ n := by
      intro n hn
      rw [← ho]
      exact orderOf_dvd_iff_zpow_eq_one.mpr (LinearEquiv.ext hn)
    refine ⟨hext a fun w => ?_, hext b fun w => ?_⟩
    · have h1 := congrArg (fun f : V ≃ₗ[K] V => f (ψ.symm (0, Pi.single i₀ w))) hc1
      simp only [LinearEquiv.mul_apply] at h1
      rw [hother i₀ i₁ b w h01, hcoord] at h1
      have h2 := congrArg (fun v => (ψ v).2 i₀) h1
      simpa using h2
    · have h1 := congrArg (fun f : V ≃ₗ[K] V => f (ψ.symm (0, Pi.single i₁ w))) hc1
      simp only [LinearEquiv.mul_apply] at h1
      rw [hcoord, hother i₁ i₀ a _ h01.symm] at h1
      have h2 := congrArg (fun v => (ψ v).2 i₁) h1
      simpa using h2

omit [Finite K] in
theorem multiplicity_le_one_of_pRank [Finite K] (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hrank : CFSG.pRank p (ProjOrthDerived Q) ≤ 1) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    primaryMultiplicity x.toLinearMap h ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hRS : RepeatedSummands Q x p h := by
    by_cases hself : h = reciprocalPolynomial h
    · exact hx.repeatedSummands_selfDual hp hp2 hh hne1 hself
    · exact hx.repeatedSummands_paired hp hh hne1 hself
  have := two_le_pRank_of_repeated hQ hT hp hp2 hRS (by omega)
  omega

end Rank

section LinGp

theorem eq_one_of_two_pow_eq_one_of_finrank_lt_two {E W : Type*} [Field E] [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] (h2 : (2 : E) = 0) (hW : Module.finrank E W < 2)
    (u : LinearMap.GeneralLinearGroup E W) {k : ℕ} (hu : u ^ (2 ^ k) = 1) : u = 1 := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
    refine ih (eq_one_of_sq_eq_one_of_finrank_lt_two h2 hW _ ?_)
    rw [← pow_mul, ← pow_succ]
    exact hu

theorem commute_of_finrank_le_one {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (hW : Module.finrank E W ≤ 1) (u u' : LinearMap.GeneralLinearGroup E W) :
    Commute u u' := by
  rcases Nat.lt_or_ge (Module.finrank E W) 1 with h0 | h1
  · have : Subsingleton W := (Module.finrank_zero_iff (R := E)).mp (by omega)
    exact Units.ext (LinearMap.ext fun w => Subsingleton.elim _ _)
  · have hfr : Module.finrank E W = 1 := by omega
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hfr
    obtain ⟨a, ha⟩ := hv ((u : Module.End E W) v)
    obtain ⟨b, hb⟩ := hv ((u' : Module.End E W) v)
    have hu : ∀ t : E, (u : Module.End E W) (t • v) = (t * a) • v := fun t => by
      rw [map_smul, ← ha, smul_smul]
    have hu' : ∀ t : E, (u' : Module.End E W) (t • v) = (t * b) • v := fun t => by
      rw [map_smul, ← hb, smul_smul]
    refine Units.ext (LinearMap.ext fun w => ?_)
    obtain ⟨c, rfl⟩ := hv w
    change (u : Module.End E W) ((u' : Module.End E W) (c • v)) =
      (u' : Module.End E W) ((u : Module.End E W) (c • v))
    rw [hu', hu, hu, hu']
    congr 1
    ring

end LinGp

section Centralizer

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem KCOrthogonal.OddOrderIsometry.apply_eq_of_two_pow (hx : OddOrderIsometry Q p x)
    (hmult : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity x.toLinearMap h ≤ 1)
    {g : V ≃ₗ[K] V} (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) {k : ℕ}
    (hgk : g ^ (2 ^ k) = 1) :
    ∀ r ∈ othersSpace x.toLinearMap (X - 1), g r = r := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hsq := hx.squarefree_minpoly
  refine (fixes_othersSpace_iff (x := x) (h := X - 1) (g := g)).mpr fun b hb hb1 _ v hv => ?_
  let bb : primaryFactors x.toLinearMap := ⟨b, hb⟩
  have : Fact (Irreducible (bb : K[X])) := ⟨irreducible_of_mem_primaryFactors hb⟩
  set w := theta x hsq ⟨g, hg⟩ with hw
  have hwk : w ^ (2 ^ k) = 1 := by
    rw [hw, ← map_pow]
    have : (⟨g, hg⟩ : ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))) ^ (2 ^ k) = 1 :=
      Subtype.ext hgk
    rw [this, map_one]
  have h2b : (2 : AdjoinRoot (bb : K[X])) = 0 := by
    rw [← map_ofNat (algebraMap K (AdjoinRoot (bb : K[X]))) 2, h2, map_zero]
  have hwb : w bb = 1 :=
    eq_one_of_two_pow_eq_one_of_finrank_lt_two h2b
      (lt_of_le_of_lt (hmult b hb hb1) one_lt_two) _ (congrFun hwk bb)
  have := coe_theta_apply x hsq ⟨g, hg⟩ bb ⟨v, hv⟩
  rw [← hw, hwb] at this
  exact this.symm

omit [Finite K] [CharP K 2] in
theorem KCOrthogonal.OddOrderIsometry.commute_of_fixes_fixedSpace (hx : OddOrderIsometry Q p x)
    (hmult : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity x.toLinearMap h ≤ 1)
    {g g' : V ≃ₗ[K] V} (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))
    (hg' : g' ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))
    (hgf : ∀ w ∈ fixedSpace x, g w = w) (hgf' : ∀ w ∈ fixedSpace x, g' w = w) :
    g * g' = g' * g := by
  have hsq := hx.squarefree_minpoly
  have hcomm : (⟨g, hg⟩ : ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))) * ⟨g', hg'⟩ =
      ⟨g', hg'⟩ * ⟨g, hg⟩ := by
    apply (theta x hsq).injective
    rw [map_mul, map_mul]
    funext b
    rw [Pi.mul_apply, Pi.mul_apply]
    by_cases hb1 : (b : K[X]) = X - 1
    · have hone : ∀ (u : V ≃ₗ[K] V) (hu : u ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))),
          (∀ w ∈ fixedSpace x, u w = w) → theta x hsq ⟨u, hu⟩ b = 1 := by
        intro u hu hfu
        refine Units.ext (LinearMap.ext fun v => Subtype.ext ?_)
        have := coe_theta_apply x hsq ⟨u, hu⟩ b v
        rw [Units.val_one, Module.End.one_apply] at *
        refine this.trans ?_
        apply hfu
        rw [fixedSpace_eq_primaryComponent, ← hb1]
        exact v.2
      rw [hone g hg hgf, hone g' hg' hgf']
    · exact commute_of_finrank_le_one (hmult b b.2 hb1) _ _
  exact congrArg Subtype.val hcomm

end Centralizer

end CFSG.RankThree.PartOne
