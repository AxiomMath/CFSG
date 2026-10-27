module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Share
import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedComponentPrimes
import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
import CFSG.LocalAnalysis.SteinbergBMOddResidualE7Lift
import CFSG.LocalAnalysis.SteinbergCAOddResidualOrderFacts
import CFSG.LocalAnalysis.SteinbergCEOddResidualTwistedE6Inner
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeReturn
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergCA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

section Parity

theorem even_iform_self_E67 {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7) (y : Fin τ.rank → ℤ) :
    Even (iform y y) := by
  have h : ∀ z : Fin τ.rank → ZMod 2,
      ∑ i, ∑ j, z i * ((τ.symmetrizedCartan i j : ℤ) : ZMod 2) * z j = 0 := by
    rcases hτ with rfl | rfl <;> decide +kernel
  have h2 := h fun i => (y i : ZMod 2)
  rw [even_iff_two_dvd]
  have h3 : ((iform y y : ℤ) : ZMod 2) = 0 := by
    simp only [iform]
    push_cast
    exact h2
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (iform y y) 2).1 h3

theorem iform_self_emod_eight_of_bool {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7) :
    ∀ b : Fin τ.rank → Bool,
      (∀ i, iform (fun j => if b j then (1 : ℤ) else 0) (Pi.single i 1) % 2 = 0) →
        iform (fun j => if b j then (1 : ℤ) else 0) (fun j => if b j then (1 : ℤ) else 0) % 8 = 0 ∨
          iform (fun j => if b j then (1 : ℤ) else 0) (fun j => if b j then (1 : ℤ) else 0) %
            8 = 6 := by
  rcases hτ with rfl | rfl <;> decide +kernel

theorem iform_self_emod_eight_of_even
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7) {x : Fin τ.rank → ℤ}
    (hx : ∀ i, Even (iform x (Pi.single i 1))) : iform x x % 8 = 0 ∨ iform x x % 8 = 6 := by
  set b : Fin τ.rank → Bool := fun j => decide (x j % 2 = 1) with hb
  set z : Fin τ.rank → ℤ := fun j => if b j then (1 : ℤ) else 0 with hz
  set y : Fin τ.rank → ℤ := fun j => x j / 2 with hy
  have hzx : ∀ j, z j = x j % 2 := by
    intro j
    rcases Int.emod_two_eq_zero_or_one (x j) with h | h <;> simp [hz, hb, h]
  have hxzy : x = z + (2 : ℤ) • y := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzx, hy]
    have := Int.mul_ediv_add_emod (x j) 2
    omega
  have hzev : ∀ i, iform z (Pi.single i 1) % 2 = 0 := by
    intro i
    obtain ⟨m, hm⟩ := hx i
    rw [hxzy, iform_add_left, iform_smul_left] at hm
    omega
  have hkey : iform z z % 8 = 0 ∨ iform z z % 8 = 6 := iform_self_emod_eight_of_bool hτ b hzev
  have hzy : Even (iform z y) := by
    rw [iform_comm, iform_eq_sum_single]
    refine Finset.even_sum _ fun j _ => (Even.mul_left ?_ _)
    rw [iform_comm]
    exact Int.even_iff.2 (hzev j)
  obtain ⟨a, ha⟩ := hzy
  obtain ⟨c, hc⟩ := even_iform_self_E67 hτ y
  have hxx : iform x x = iform z z + 4 * iform z y + 4 * iform y y := by
    rw [hxzy]
    simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right]
    rw [iform_comm y z]
    ring
  rw [hxx]
  omega

theorem corootPair_eq_iform_E67
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (v : Fin τ.rank → ℤ) : corootPair γ v = iform γ v := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  have h1 : τ.symmetrizer j j = 1 := by rcases hτ with rfl | rfl <;> fin_cases j <;> rfl
  rw [corootPair, hj, h1, mul_one]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

theorem even_of_neg_one_zpow_eq_one {k : Type*} [Field k] (hk : ringChar k ≠ 2) {n : ℤ}
    (h : (-1 : kˣ) ^ n = 1) : Even n := by
  rcases Int.even_or_odd n with hn | hn
  · exact hn
  · exfalso
    rw [hn.neg_one_zpow] at h
    have h1 : (-1 : k) = 1 := congrArg Units.val h
    have h2 : (2 : k) = 0 := by linear_combination -h1
    exact Ring.two_ne_zero hk h2

end Parity

section OrbitMap

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem orbitMap_neg_one_ne_one
    {τ : Tag} (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hτ : τ = .E6 ∨ τ = .E7) {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hO2 : orbitCard O ≤ 2) : D.orbitMap O (-1) ≠ 1 := by
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact D.odd
  have hpos := D.orbitCard_pos hO
  have hf : ∀ j, D.orbitFactor O j (-1) = rootDiagUnit τ
      (fun i => (-1 : kˣ) ^ corootPair (D.orbitVec O j) (Pi.single i 1)) := by
    intro j
    rw [D.orbitFactor_apply, map_neg_one_sl2, map_neg_one_sl2, ← HSL_neg_one_eq]
    exact rootSL2_neg_one_eq_rootDiagUnit (D.isRoot_orbitVec hO j) fun i => rfl
  have hcp : ∀ j (i : Fin τ.rank), corootPair (D.orbitVec O j) (Pi.single i 1) =
      iform (D.orbitVec O j) (Pi.single i 1) := fun j i =>
    corootPair_eq_iform_E67 hτ (D.isRoot_orbitVec hO j) _
  have hself : ∀ j, iform (D.orbitVec O j) (D.orbitVec O j) = 2 := by
    intro j
    obtain ⟨i, hi⟩ := iform_self_of_isRoot (D.isRoot_orbitVec hO j)
    have h1 : τ.symmetrizer i i = 1 := by rcases hτ with rfl | rfl <;> fin_cases i <;> rfl
    rw [hi, h1, mul_one]
  intro h
  rw [D.orbitMap_eq_prod] at h
  interval_cases hd : orbitCard O
  ·
    simp only [List.range_one, List.map_singleton, List.prod_singleton, hf] at h
    rw [← rootDiagUnit_one] at h
    have hb := rootDiagUnit_injective h
    have hev : ∀ i, Even (iform (D.orbitVec O 0) (Pi.single i 1)) := fun i => by
      rw [← hcp]
      exact even_of_neg_one_zpow_eq_one hk2 (congrFun hb i)
    have := iform_self_emod_eight_of_even hτ hev
    rw [hself] at this
    omega
  ·
    simp only [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, hf] at h
    rw [← rootDiagUnit_mul, ← rootDiagUnit_one] at h
    have hb := rootDiagUnit_injective h
    have hne : D.orbitVec O 0 ≠ D.orbitVec O 1 := fun h01 => by
      have := D.orbitVec_injOn hO (by omega) (by omega) h01
      omega
    have horth : iform (D.orbitVec O 0) (D.orbitVec O 1) = 0 := by
      have hO' := D.eq_thetaOrbit_orbitRoot hO
      refine D.orbit_orthogonal _ (D.orbitRoot_mem_kernelRoots hO) _ ?_ _ ?_ hne
      · rw [← hO']
        exact D.orbitVec_mem hO 0
      · rw [← hO']
        exact D.orbitVec_mem hO 1
    have hev : ∀ i, Even (iform (D.orbitVec O 0 + D.orbitVec O 1) (Pi.single i 1)) := by
      intro i
      have h1 := congrFun hb i
      simp only [Pi.mul_apply, Pi.one_apply, ← zpow_add] at h1
      rw [iform_add_left, ← hcp, ← hcp]
      exact even_of_neg_one_zpow_eq_one hk2 h1
    have := iform_self_emod_eight_of_even hτ hev
    have hvv : iform (D.orbitVec O 0 + D.orbitVec O 1) (D.orbitVec O 0 + D.orbitVec O 1) =
        4 := by
      rw [iform_add_left, iform_add_right, iform_add_right, hself, hself, horth,
        iform_comm (D.orbitVec O 1), horth]
      norm_num
    rw [hvv] at this
    omega

end OrbitMap

section Obstruction

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem false_of_isPComponent_totalFixedGroup
    {τ : Tag}
    (D : OrthogonalSemilinearFixedRootDatum τ p k) (hτ : τ = .E6 ∨ τ = .E7)
    (horb : ∀ (J' : Set.range D.classOrbit) (O : Set (Fin τ.rank → ℤ)),
      O ∈ (D.withOrbit J').orbits → orbitCard O ≤ 2)
    (hX : Finite D.totalFixedGroup) {J₀ : Subgroup (adjointGroup τ k)}
    (hJ₀X : J₀ ≤ D.totalFixedGroup) (hJ₀c : CFSG.IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup))
    (hJ₀s : IsSimpleGroup J₀) (hJ₀nab : ∃ a b : J₀, a * b ≠ b * a) {K : Type*} [Field K]
    [CharP K 2] (eJ : J₀ ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  have hcomp : CFSG.IsComponent (J₀.subgroupOf D.totalFixedGroup) := by
    obtain ⟨-, -, hsub, -, -⟩ := hJ₀c
    refine ⟨?_, hsub⟩
    have : IsSimpleGroup (J₀.subgroupOf D.totalFixedGroup) :=
      (Subgroup.subgroupOfEquivOfLe hJ₀X).isSimpleGroup
    exact isQuasisimple_of_isSimpleGroup (by
      obtain ⟨a, b, hab⟩ := hJ₀nab
      refine ⟨(Subgroup.subgroupOfEquivOfLe hJ₀X).symm a,
        (Subgroup.subgroupOfEquivOfLe hJ₀X).symm b, fun h' => hab ?_⟩
      apply (Subgroup.subgroupOfEquivOfLe hJ₀X).symm.injective
      exact (MulEquiv.map_mul _ a b).trans (h'.trans (MulEquiv.map_mul _ b a).symm))
  obtain ⟨J', ⟨O, hO⟩, hJ₀eq⟩ := D.exists_eq_orbitGroupC_of_isComponent hX hJ₀X hcomp
  have : CharP ((D.withOrbit J').orbitField O) p :=
    CharP.subring k p ((D.withOrbit J').orbitField O).toSubring
  let φ : Matrix.SpecialLinearGroup (Fin 2) ((D.withOrbit J').orbitField O) →*
      adjointGroup τ k :=
    ((D.withOrbit J').orbitMapHom hO).codRestrict _
      (fun A => (D.withOrbit J').orbitMap_mem_adjointGroup O A)
  have hφ : ∀ A, ((φ A : adjointGroup τ k) : ModGL τ k) = (D.withOrbit J').orbitMap O A :=
    fun A => rfl
  have hφJ : ∀ A, φ A ∈ J₀ := fun A => by
    rw [hJ₀eq]
    exact (D.withOrbit J').mk_mem_orbitGroupC ((D.withOrbit J').orbitMap_mem_orbitGroup hO A)
  have hneg : φ (-1) ≠ 1 := fun h => by
    apply orbitMap_neg_one_ne_one (D.withOrbit J') hτ hO (horb J' O hO)
    rw [← hφ, h]
    rfl
  have hu : φ (uSL 1) ≠ 1 := fun h => by
    have h1 : (D.withOrbit J').orbitX O 1 = 1 := by
      change (D.withOrbit J').orbitMap O (uSL 1) = 1
      rw [← hφ, h]
      rfl
    have h2 := (D.withOrbit J').orderOf_orbitX_one hO
    rw [h1, orderOf_one] at h2
    exact (Fact.out : p.Prime).one_lt.ne h2
  exact false_of_mulEquiv_SL2_of_hom eJ D.odd φ hφJ hneg hu

end Obstruction

section Reduction

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_datum_isPComponent_of_twistReduction
    (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j) {r₀ : ℕ}
    {reps : List (SignRep τ)}
    (htheta : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      ThetaProperties ρ r₀ (signMaskChar τ m.mask) (ToralSign.wordElt τ l))
    {D : ModGL τ k}
    (hDX : ∀ (l : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      (wordWeylMatrix τ k l * D) * pinnedX τ k γ c * (wordWeylMatrix τ k l * D)⁻¹ =
        pinnedX τ k (thetaMap (ToralSign.wordElt τ l) ρ γ) (μ * c))
    (hDT : D ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hDG : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (hpin : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization τ k p e (signMaskChar τ m.mask)
        (thetaMap (ToralSign.wordElt τ l) ρ) (wordWeylMatrix τ k l * D))
    {x : ModGL τ k} (hred : IsFiniteToralTwistReduction τ k p e D reps x)
    (L : Subgroup (ModGL τ k))
    (hL : L ≤ ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x})
    (hLc : CFSG.IsPComponent 2 (L.subgroupOf (⁅fixedPointsIn (adjointGroup τ k)
      (frobTwistGL τ k p e D), fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
        Subgroup.centralizer {x}))) :
    ∃ (Dd : OrthogonalSemilinearFixedRootDatum τ p k) (J₀ : Subgroup (adjointGroup τ k)),
      (∃ m ∈ reps, ∃ l ∈ m.omegaWords, Dd.χ = signMaskChar τ m.mask ∧
        ∀ γ, Dd.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt τ l) ρ γ)) ∧
      Finite Dd.totalFixedGroup ∧ J₀ ≤ Dd.totalFixedGroup ∧
      CFSG.IsPComponent 2 (J₀.subgroupOf Dd.totalFixedGroup) ∧ Nonempty (L ≃* J₀) := by
  classical
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨r, hr, l, hl, -, hQfin, g₁, -, hcomp⟩ := hred
  obtain ⟨hJle, hJc⟩ := ((hcomp 2 Nat.prime_two).1 L).1 ⟨hL, hLc⟩
  set χ := signMaskChar τ r.mask with hχ
  set Q₀ := wordWeylMatrix τ k l * D with hQ₀_def
  set M := torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) with hM_def
  set J := L.map (MulAut.conj g₁).toMonoidHom with hJ_def
  have hMG : M ≤ adjointGroup τ k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  by_cases hne : (kernelRoots χ).Nonempty
  swap
  · exfalso
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact not_isPComponent_of_kernelRoots_eq_empty hne
      (inf_le_left : fixedPointsIn M (frobTwistGL τ k p e Q₀) ≤ M) _ hJc
  have hθ := htheta r hr l hl
  have hQ₀T : Q₀ ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)) :=
    mul_mem (wordWeylMatrix_mem_normalizer l) hDT
  obtain ⟨Dd, h, hhT, hDχ, -, hDθ, -, hX⟩ := exists_pinned_datum p hp hk he hτ hA hB hθ
    (hDX l) hQ₀T (map_conj_wordWeylMatrix_mul l hDG) (hpin r hr l hl) hne
  have hker := rootCharKernel_signCharTuple (k := k) hk2 χ
  obtain ⟨-, ⟨hMc, -, hMsm, -, -⟩, -⟩ := exceptional_toral_centralizer_identity_component τ k hk2
    (signCharTuple χ) (signCharTuple_sign χ)
  rw [toralRootPointSubgroup, toralRootGroup, hker] at hMc hMsm
  have hF₀M : ∀ g ∈ M, frobTwistGL τ k p e Q₀ g ∈ M := by
    intro g hg
    have hS : (rootSpan τ k (kernelRoots χ)).map (frobTwistGL τ k p e Q₀) =
        rootSpan τ k (kernelRoots χ) := by
      rw [map_frobTwistGL_rootSpan_of_conj p e (hDX l) fun _ hα => hα.1, hθ.image_kernelRoots]
    have hM₀ : M.map (frobTwistGL τ k p e Q₀) = M := by
      rw [hM_def, Subgroup.map_sup, map_frobTwistGL_torusGroup p e hQ₀T, hS]
    rw [← hM₀]
    exact ⟨g, hg, rfl⟩
  obtain ⟨z, hzM, hz⟩ := exists_eq_inv_mul_frobTwistGL p he Q₀ hMc hMsm hF₀M
    (Subgroup.mem_sup_left hhT)
  have hFu : frobTwistGL τ k p e Q₀ z⁻¹ = h⁻¹ * z⁻¹ := by
    rw [map_inv, hz]
    group
  have hFh : ∀ y, frobTwistGL τ k p e (h * Q₀) y = h * frobTwistGL τ k p e Q₀ y * h⁻¹ :=
    fun y => frobTwistGL_mul_left_apply p e h _ y
  have hconj : (fixedPointsIn M (frobTwistGL τ k p e Q₀)).map (MulAut.conj z⁻¹).toMonoidHom =
      fixedPointsIn M (frobTwistGL τ k p e (h * Q₀)) :=
    map_conj_fixedPointsIn_eq M _ _ (inv_mem hzM) hFh hFu
  have hQfin' : Finite (fixedPointsIn M (frobTwistGL τ k p e Q₀)) := hQfin
  obtain ⟨hJDle, hJDc⟩ := (isPComponent_subgroupOf_map_conj_iff z⁻¹ hconj 2 Nat.prime_two J).1
    ⟨hJle, hJc⟩
  set Mh := fixedPointsIn M (frobTwistGL τ k p e (h * Q₀)) with hMh_def
  set X := Dd.totalFixedGroup with hX_def
  set JD := J.map (MulAut.conj z⁻¹).toMonoidHom with hJD_def
  have hJDG : JD ≤ adjointGroup τ k := hJDle.trans ((inf_le_left : Mh ≤ M).trans hMG)
  set J₀ := JD.subgroupOf (adjointGroup τ k) with hJ₀_def
  have hJ₀X : J₀ ≤ X := by
    intro y hy
    have hy' : (y : ModGL τ k) ∈ JD := hy
    have hmem : (y : ModGL τ k) ∈ X.map (adjointGroup τ k).subtype := by
      rw [hX]
      exact hJDle hy'
    obtain ⟨w, hw, hwy⟩ := hmem
    have : w = y := Subtype.ext hwy
    exact this ▸ hw
  let eX : X ≃* Mh :=
    (X.equivMapOfInjective (adjointGroup τ k).subtype
      (adjointGroup τ k).subtype_injective).trans (MulEquiv.subgroupCongr hX)
  have heX : ∀ y : X, ((eX y : Mh) : ModGL τ k) =
      (((y : adjointGroup τ k)) : ModGL τ k) := fun y => rfl
  have hMhfin : Finite Mh := by
    rw [← hconj]
    exact Finite.of_equiv _ ((MulAut.conj z⁻¹).subgroupMap
      (fixedPointsIn M (frobTwistGL τ k p e Q₀))).toEquiv
  have hXfin : Finite X := Finite.of_equiv _ eX.symm.toEquiv
  have hJ₀comp : CFSG.IsPComponent 2 (J₀.subgroupOf X) := by
    have h1 := isPComponent_map_of_isPComponent 2 eX.symm hJDc
    have h2 : (JD.subgroupOf Mh).map eX.symm.toMonoidHom = J₀.subgroupOf X := by
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have : (((eX.symm w : X) : adjointGroup τ k) : ModGL τ k) = (w : ModGL τ k) := by
          have := heX (eX.symm w)
          rw [MulEquiv.apply_symm_apply] at this
          exact this.symm
        change (((eX.symm w : X) : adjointGroup τ k) : ModGL τ k) ∈ JD
        rw [this]
        exact hw
      · intro hy
        refine ⟨eX y, ?_, MulEquiv.symm_apply_apply eX y⟩
        change ((eX y : Mh) : ModGL τ k) ∈ JD
        rw [heX]
        exact hy
    rwa [h2] at h1
  refine ⟨Dd, J₀, ⟨r, hr, l, hl, hDχ, hDθ⟩, hXfin, hJ₀X, hJ₀comp,
    ⟨(L.equivMapOfInjective _ (MulAut.conj g₁).injective).trans
      ((J.equivMapOfInjective _ (MulAut.conj z⁻¹).injective).trans
        (Subgroup.subgroupOfEquivOfLe hJDG).symm)⟩⟩

end Reduction

section Inner

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem false_of_mulEquiv_inner_centralizer
    (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j)
    {reps : List (SignRep τ)}
    (htheta : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      ThetaProperties ρ 2 (signMaskChar τ m.mask) (ToralSign.wordElt τ l))
    {D : ModGL τ k}
    (hDX : ∀ (l : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      (wordWeylMatrix τ k l * D) * pinnedX τ k γ c * (wordWeylMatrix τ k l * D)⁻¹ =
        pinnedX τ k (thetaMap (ToralSign.wordElt τ l) ρ γ) (μ * c))
    (hDT : D ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hDG : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (hpin : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization τ k p e (signMaskChar τ m.mask)
        (thetaMap (ToralSign.wordElt τ l) ρ) (wordWeylMatrix τ k l * D))
    (hRfin : Finite (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)))
    {x : ModGL τ k} (hred : IsFiniteToralTwistReduction τ k p e D reps x)
    {A : Type*} [Group A] (eA : A ≃* ↥(⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x}))
    (S : Subgroup A) (hSn : S.Normal) (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a) {K : Type*} [Field K] [CharP K 2]
    (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 := Or.inr hτ
  let N : Subgroup (ModGL τ k) :=
    ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x}
  have hNfin : Finite N := by
    have hNR : N ≤ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D) :=
      inf_le_left.trans (Subgroup.commutator_le.2 fun a ha b hb => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))
    exact Finite.of_injective _ (Subgroup.inclusion_injective hNR)
  let S' : Subgroup N := S.map eA.toMonoidHom
  let e' : S ≃* S' := S.equivMapOfInjective _ eA.injective
  have := hSs
  have hS'n : S'.Normal := hSn.map _ eA.surjective
  have hS's : IsSimpleGroup S' := e'.symm.isSimpleGroup
  have hS'nab : ∃ a b : S', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnab
    exact ⟨e' a, e' b, fun h' => hab (e'.injective
      ((MulEquiv.map_mul e' a b).trans (h'.trans (MulEquiv.map_mul e' b a).symm)))⟩
  have hS'c : CFSG.IsPComponent 2 S' :=
    isPComponent_two_of_mulEquiv_SL2 S' hS'n hS's hS'nab (e'.symm.trans eS)
  have hLsub : (S'.map N.subtype).subgroupOf N = S' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective S'
  obtain ⟨Dd, J₀, ⟨m, hm, l, hl, hDχ, hDθ⟩, hXfin, hJ₀X, hJ₀c, ⟨eL⟩⟩ :=
    exists_datum_isPComponent_of_twistReduction p hp hk he hτ' hA hB htheta hDX hDT hDG hpin
      hred (S'.map N.subtype) (Subgroup.map_subtype_le S') (by rw [hLsub]; exact hS'c)
  have hθ : ThetaProperties ρ 2 Dd.χ (ToralSign.wordElt τ l) := by
    rw [hDχ]
    exact htheta m hm l hl
  have horb : ∀ (J' : Set.range Dd.classOrbit) (O : Set (Fin τ.rank → ℤ)),
      O ∈ (Dd.withOrbit J').orbits → orbitCard O ≤ 2 := by
    intro J' O hO
    rcases orbitCard_eq_of_thetaProperties (Dd.withOrbit J') hθ hDθ hO with h | h <;> omega
  let eJ : J₀ ≃* S := (eL.symm.trans (S'.equivMapOfInjective _ N.subtype_injective).symm).trans
    e'.symm
  have hJ₀s : IsSimpleGroup J₀ := eJ.isSimpleGroup
  have hJ₀nab : ∃ a b : J₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnab
    exact ⟨eJ.symm a, eJ.symm b, fun h' => hab (eJ.symm.injective
      ((MulEquiv.map_mul eJ.symm a b).trans (h'.trans (MulEquiv.map_mul eJ.symm b a).symm)))⟩
  exact false_of_isPComponent_totalFixedGroup Dd hτ horb hXfin hJ₀X hJ₀c hJ₀s hJ₀nab
    (eJ.trans eS)

end Inner

section Main

theorem odd_E7_inner_diagonal_fixed_no_normal_even_SL2
    {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {α : MulAut (adjointGroup .E7 F)} {g : adjointGroup .E7 F}
    {a : Fin Tag.E7.rank → Fˣ}
    (hαg : ∀ h : adjointGroup .E7 F, (α h : ModGL .E7 F) =
      (g : ModGL .E7 F) * rootDiagUnit .E7 a * h * (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 F)⁻¹)
    (hα : α ^ 2 = 1)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 F)))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (K : Type) [Field K] [CharP K 2] (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  obtain ⟨p, n, hp, hp2, hn, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hF
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := hchar ▸ ringChar.charP F
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.exists_mulEquiv_E7_inner_diagonal_fixed hp2 hn hcard hαg hα
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨n7, -, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure F) p hp2 n hn
  obtain ⟨r7, -, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure F) hp2 n hn
  exact false_of_mulEquiv_inner_centralizer p hp2 hk hn (Or.inr rfl) (ρ := 1) (fun _ _ => rfl)
    (fun _ _ => rfl) h7.theta (fun l _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ)
    (one_mem _) (map_conj_one_adjointGroup _ _) n7
    (finite_fixedPointsIn_frobTwistGL p hn le_rfl (map_one _) (one_pow 1)) (r7 x hxR hx2) eA S
    hSn hSs hSnab eS

theorem odd_twisted_E6_inner_fixed_no_normal_even_SL2
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (F : Type) [Field F] [Finite F] (hF : Nat.card F = (p ^ f) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (α : MulAut (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))
    (hα : α ^ 2 = 1) (hαi : α ∈ twistedE6Inn F σ)
    (S : Subgroup (α.toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (K : Type) [Field K] [CharP K 2] (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := finite_field_prime_power_characteristic hp (by omega : 1 ≤ 2 * f)
    (by rw [hF, ← pow_mul, mul_comm])
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    CFSG.LocalAnalysis.SteinbergCE.exists_mulEquiv_twisted_E6_inner_fixed hp2 hf hF σ hσ hα hαi
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure F) p hp2 f hf
  obtain ⟨-, r6, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure F) hp2 f hf
  exact false_of_mulEquiv_inner_centralizer p hp2 hk hf (Or.inl rfl) TwistTag.E6.cartan_perm
    symmetrizedCartan_perm_E6 h6.theta
    (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.E6 l hγ)
    (diagramMap_mem_normalizer TwistTag.E6) (map_conj_diagramMap TwistTag.E6 _ (Or.inl rfl)) n6
    (finite_fixedPointsIn_frobTwistGL p hf (by decide)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.E6)
        (iterateFrobenius (AlgebraicClosure F) p f))
      (diagramMap_pow_order TwistTag.E6 (AlgebraicClosure F)))
    (r6 x hxR hx2) eA S hSn hSs hSnab eS

end Main

end CFSG.LocalAnalysis.SteinbergCA
