module

public import CFSG.LocalAnalysis.StandardType.GGTwE6HyperplaneFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6FixedA2SL3
public import CFSG.LocalAnalysis.StandardType.GGE6NonToralCentralizerTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6FixedA2Type
public import CFSG.LieType.AlgebraicGroups.MonomialCentralizerCoroot
public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial

public noncomputable section
namespace CFSG.StandardType.TwE6E4bTorus

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.Three
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6NonToralThree
  CFSG.StandardType.E6ThreeEnd CFSG.StandardType.TwE6HyperplaneTypes
  CFSG.StandardType.TwE6FixedA2Type CFSG.StandardType.TwE6FixedA2SL3

local instance : NeZero Tag.E6.rank := ⟨by decide⟩

theorem orthRoots_rotation_0 :
    ((fun j : Fin Tag.E6.rank => ![0, 0, 1, 1, 1, 1] j) + cAct (fun j : Fin Tag.E6.rank => ![0, 0, 1, 1, 1, 1] j) +
      cAct (cAct (fun j : Fin Tag.E6.rank => ![0, 0, 1, 1, 1, 1] j))) = 0 := by
  decide +kernel

theorem orthRoots_rotation_1 :
    ((fun j : Fin Tag.E6.rank => ![0, 1, 0, 1, 1, 1] j) + cAct (fun j : Fin Tag.E6.rank => ![0, 1, 0, 1, 1, 1] j) +
      cAct (cAct (fun j : Fin Tag.E6.rank => ![0, 1, 0, 1, 1, 1] j))) = 0 := by
  decide +kernel

theorem orthRoots_rotation_2 :
    ((fun j : Fin Tag.E6.rank => ![1, 0, 1, 1, 1, 0] j) + cAct (fun j : Fin Tag.E6.rank => ![1, 0, 1, 1, 1, 0] j) +
      cAct (cAct (fun j : Fin Tag.E6.rank => ![1, 0, 1, 1, 1, 0] j))) = 0 := by
  decide +kernel

theorem orthRoots_rotation_3 :
    ((fun j : Fin Tag.E6.rank => ![1, 1, 1, 1, 0, 0] j) + cAct (fun j : Fin Tag.E6.rank => ![1, 1, 1, 1, 0, 0] j) +
      cAct (cAct (fun j : Fin Tag.E6.rank => ![1, 1, 1, 1, 0, 0] j))) = 0 := by
  decide +kernel

theorem orthRoots_rotation (α : Fin Tag.E6.rank → ℤ) (hα : α ∈ orthRoots) :
    α + cAct α + cAct (cAct α) = 0 := by
  rcases List.mem_cons.mp hα with h0 | hrest
  · rw [h0]; exact orthRoots_rotation_0
  rcases List.mem_cons.mp hrest with h1 | hrest
  · rw [h1]; exact orthRoots_rotation_1
  rcases List.mem_cons.mp hrest with h2 | hrest
  · rw [h2]; exact orthRoots_rotation_2
  have h3 := List.mem_singleton.mp hrest
  rw [h3]
  exact orthRoots_rotation_3

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

set_option maxRecDepth 1000000 in
theorem rootChar_eq_one_of_mem_connected_centralizer_orthRoots
    (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {x : ModGL .E6 L} (hxE : x ∈ E)
    (hxc : weylQuotientHom .E6 L ⟨x, hEM hxE⟩ = cE6)
    {t : ModGL .E6 L} (ht : t ∈ closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))))
    {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ orthRoots) :
    ∃ b, t = rootDiagUnit .E6 b ∧ rootChar b α = 1 := by
  refine CFSG.StandardType.TwE6HyperplaneFrame.rootChar_eq_one_of_mem_connected_centralizer
    hL hEM hE hcard hET hAS hAg hxE (isRoot_orthRoots α hα) ?_ ht
  rw [hxc]
  simpa only [cE6_smul] using orthRoots_rotation α hα

def fixedA2ActionVec : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![0, 1, 0, 1, 1, 0], ![0, 0, 1, 1, 1, 0], ![-1, -1, -1, -2, -1, 0],
    ![1, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 1]]

set_option maxRecDepth 1000000 in
theorem fixedA2V_inv_smul_single (j : Fin Tag.E6.rank) :
    fixedA2V⁻¹ • (Pi.single j (1 : ℤ) : Fin Tag.E6.rank → ℤ) = fixedA2ActionVec j := by
  rw [fixedA2V, ← CoxeterSystem.wordProd_reverse, CFSG.LieType.Chevalley.wordProd_smul]
  revert j
  decide +kernel

set_option maxRecDepth 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem diagTuple_explicit {L : Type} [Field L] (s u : Lˣ) :
    diagTuple s u = ![u⁻¹, s⁻¹ * u, s⁻¹ * u, s ^ 2 * u⁻¹, s⁻¹ * u, u⁻¹] := by
  classical
  change (fun j : Fin 6 => diagTuple s u j) =
    (![u⁻¹, s⁻¹ * u, s⁻¹ * u, s ^ 2 * u⁻¹, s⁻¹ * u, u⁻¹] : Fin 6 → Lˣ)
  funext j
  rw [diagTuple, weylTuple, fixedA2V_inv_smul_single]
  change (∏ i : Fin 6, (s ^ Tag.E6.cartan 0 i * u ^ Tag.E6.cartan 2 i) ^
    fixedA2ActionVec j i) = _
  simp only [Fin.prod_univ_succ]
  fin_cases j <;> norm_num [Tag.cartan, Tag.cartanE, fixedA2ActionVec]
  all_goals ext <;> simp <;> field_simp <;> ring

set_option maxRecDepth 1000000 in
theorem corootPair_gamma1_single (j : Fin Tag.E6.rank) :
    corootPair gamma1 (Pi.single j 1) = ![0, -1, -1, 2, -1, 0] j := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 1000000 in
theorem corootPair_gamma2_single (j : Fin Tag.E6.rank) :
    corootPair gamma2 (Pi.single j 1) = ![-1, 1, 1, -1, 1, -1] j := by
  fin_cases j <;> decide +kernel

set_option backward.isDefEq.respectTransparency false in
theorem corootCurve_explicit {L : Type} [Field L] (s u : Lˣ) :
    (fun j : Fin Tag.E6.rank =>
      s ^ corootPair gamma1 (Pi.single j 1) * u ^ corootPair gamma2 (Pi.single j 1)) =
      ![u⁻¹, s⁻¹ * u, s⁻¹ * u, s ^ 2 * u⁻¹, s⁻¹ * u, u⁻¹] := by
  classical
  change (fun j : Fin 6 =>
    s ^ corootPair gamma1 (Pi.single j 1) * u ^ corootPair gamma2 (Pi.single j 1)) =
      (![u⁻¹, s⁻¹ * u, s⁻¹ * u, s ^ 2 * u⁻¹, s⁻¹ * u, u⁻¹] : Fin 6 → Lˣ)
  funext j
  rw [corootPair_gamma1_single, corootPair_gamma2_single]
  fin_cases j <;> simp

@[expose] def fixedA2Torus (L : Type) [Field L] : Set (ModGL .E6 L) :=
  Set.range (fun p : Lˣ × Lˣ => fixedA2Rho L (diagSL3 p.1 p.2))

set_option backward.isDefEq.respectTransparency false in
theorem mem_fixedA2Torus_of_orthRoots {b : Fin Tag.E6.rank → Lˣ}
    (h : ∀ α ∈ orthRoots, rootChar b α = 1) :
    ∃ s u : Lˣ, b = diagTuple s u := by
  classical
  have hprod (v : Fin 6 → ℤ) : rootChar b v =
      b 0 ^ v 0 * (b 1 ^ v 1 * (b 2 ^ v 2 * (b 3 ^ v 3 * (b 4 ^ v 4 * b 5 ^ v 5)))) := by
    change (∏ i : Fin 6, b i ^ v i) = _
    simp [Fin.prod_univ_succ]
  have h0 : b 2 * b 3 * b 4 * b 5 = 1 := by
    simpa [hprod, mul_assoc] using h ![0, 0, 1, 1, 1, 1] (by simp [orthRoots])
  have h1 : b 1 * b 3 * b 4 * b 5 = 1 := by
    simpa [hprod, mul_assoc] using h ![0, 1, 0, 1, 1, 1] (by simp [orthRoots])
  have h2 : b 0 * b 2 * b 3 * b 4 = 1 := by
    simpa [hprod, mul_assoc] using h ![1, 0, 1, 1, 1, 0] (by simp [orthRoots])
  have h3 : b 0 * b 1 * b 2 * b 3 = 1 := by
    simpa [hprod, mul_assoc] using h ![1, 1, 1, 1, 0, 0] (by simp [orthRoots])
  have h12 : b 1 = b 2 := by
    have he : b 1 * (b 3 * b 4 * b 5) = b 2 * (b 3 * b 4 * b 5) := by
      simpa [mul_assoc] using h1.trans h0.symm
    exact mul_right_cancel he
  have h14 : b 4 = b 1 := by
    have he : b 4 * (b 0 * b 2 * b 3) = b 1 * (b 0 * b 2 * b 3) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using h2.trans h3.symm
    exact mul_right_cancel he
  have h05 : b 0 = b 5 := by
    have he : b 0 * (b 2 * b 3 * b 4) = b 5 * (b 2 * b 3 * b 4) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using h2.trans h0.symm
    exact mul_right_cancel he
  have hb3 : b 3 = (b 0)⁻¹ * (b 1)⁻¹ ^ 2 := by
    have he : (b 0 * b 1 ^ 2) * b 3 = 1 := by
      simpa [pow_two, mul_assoc, ← h12] using h3
    calc
      b 3 = (b 0 * b 1 ^ 2)⁻¹ * ((b 0 * b 1 ^ 2) * b 3) := by group
      _ = (b 0 * b 1 ^ 2)⁻¹ := by rw [he, mul_one]
      _ = (b 0)⁻¹ * (b 1)⁻¹ ^ 2 := by simp [mul_comm]
  refine ⟨(b 0)⁻¹ * (b 1)⁻¹, (b 0)⁻¹, ?_⟩
  rw [diagTuple_explicit]
  change (fun j : Fin 6 => b j) = _
  funext j
  fin_cases j <;> simp [h12, h14, h05, hb3, mul_pow, pow_two,
    mul_assoc, mul_comm, mul_left_comm]

set_option backward.isDefEq.respectTransparency false in
theorem fixedA2Torus_le_connectedCentralizer
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEM : E ≤ monomialSubgroup .E6 L)
    (hWeyl : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ Subgroup.zpowers cE6) :
    fixedA2Torus L ≤ closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) := by
  intro t ht
  obtain ⟨p, rfl⟩ := ht
  change fixedA2Rho L (diagSL3 p.1 p.2) ∈
    closedIdentityComponent (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)))
  rw [fixedA2Rho_diagSL3]
  have hc1 : cE6 • gamma1 = gamma1 := by
    rw [cE6_smul]
    exact cAct_fixedA2E6 gamma1 (mem_fixedA2E6.mpr (Or.inl rfl))
  have hc2 : cE6 • gamma2 = gamma2 := by
    rw [cE6_smul]
    exact cAct_fixedA2E6 gamma2 (mem_fixedA2E6.mpr (Or.inr (Or.inl rfl)))
  have hz1 : ∀ k : ℤ, cE6 ^ k • gamma1 = gamma1 :=
    fun k => MulAction.mem_fixedBy_zpow hc1 k
  have hz2 : ∀ k : ℤ, cE6 ^ k • gamma2 = gamma2 :=
    fun k => MulAction.mem_fixedBy_zpow hc2 k
  have hfix1 : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ • gamma1 = gamma1 := by
    intro e he
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hWeyl e he)
    rw [← hk]
    exact hz1 k
  have hfix2 : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ • gamma2 = gamma2 := by
    intro e he
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hWeyl e he)
    rw [← hk]
    exact hz2 k
  have h1 : rootDiagUnit .E6 (fun j => p.1 ^ corootPair gamma1 (Pi.single j 1)) ∈
      closedIdentityComponent (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) :=
    corootCurve_mem_connectedCentralizer_of_all_weyl_fixed (τ := Tag.E6) (k := L) isRoot_gamma1 E hEM hfix1 p.1
  have h2 : rootDiagUnit .E6 (fun j => p.2 ^ corootPair gamma2 (Pi.single j 1)) ∈
      closedIdentityComponent (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) :=
    corootCurve_mem_connectedCentralizer_of_all_weyl_fixed (τ := Tag.E6) (k := L) isRoot_gamma2 E hEM hfix2 p.2
  have hmul : rootDiagUnit .E6 (fun j =>
      p.1 ^ corootPair gamma1 (Pi.single j 1) * p.2 ^ corootPair gamma2 (Pi.single j 1)) ∈
      closedIdentityComponent (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) := by
    have hm := Subgroup.mul_mem _ h1 h2
    rw [← rootDiagUnit_mul] at hm
    exact hm
  convert hmul using 2
  rw [diagTuple_explicit, corootCurve_explicit]

set_option backward.isDefEq.respectTransparency false in
theorem connectedCentralizer_le_fixedA2Torus
    (hchar : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {x : ModGL .E6 L} (hxE : x ∈ E)
    (hxc : weylQuotientHom .E6 L ⟨x, hEM hxE⟩ = cE6) :
    closedIdentityComponent (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)))
      ≤ fixedA2Torus L := by
  intro t ht
  have hST := connected_centralizer_le_torus_of_regular hchar hEM hE hcard hET hAS hAg
  have htT : t ∈ torusGroup .E6 L := hST ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT
  have horth : ∀ α ∈ orthRoots, rootChar b α = 1 := by
    intro α hα
    obtain ⟨b', hb', hchar'⟩ := rootChar_eq_one_of_mem_connected_centralizer_orthRoots
      hchar hEM hE hcard hET hAS hAg hxE hxc ht hα
    rw [← rootDiagUnit_injective hb'] at hchar'
    exact hchar'
  obtain ⟨s, u, hsu⟩ := mem_fixedA2Torus_of_orthRoots horth
  rw [hsu, ← fixedA2Rho_diagSL3]
  exact ⟨(s, u), rfl⟩

theorem connectedCentralizer_eq_fixedA2Torus
    (hchar : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    (hWeyl : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ Subgroup.zpowers cE6)
    {x : ModGL .E6 L} (hxE : x ∈ E)
    (hxc : weylQuotientHom .E6 L ⟨x, hEM hxE⟩ = cE6) :
    closedIdentityComponent (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)))
      = fixedA2Torus L :=
  le_antisymm (connectedCentralizer_le_fixedA2Torus hchar hEM hE hcard hET hAS hAg hxE hxc)
    (fixedA2Torus_le_connectedCentralizer hEM hWeyl)

theorem exists_conj_connectedCentralizer_eq_fixedA2Torus
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ SCFourCover.E6AdToral E)
    {e : ModGL .E6 L} (he1 : e ≠ 1)
    (heS : e ∈ closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)))) :
    ∃ y₀ ∈ adjointGroup .E6 L,
      let E' := E.map (MulAut.conj y₀).toMonoidHom
      ∃ hEM : E' ≤ monomialSubgroup .E6 L,
        (∀ a (ha : a ∈ E'), weylQuotientHom .E6 L ⟨a, hEM ha⟩ ∈ Subgroup.zpowers cE6) ∧
        ∃ x, ∃ hx : x ∈ E', weylQuotientHom .E6 L ⟨x, hEM hx⟩ = cE6 ∧
          (closedIdentityComponent (adjointGroup .E6 L ⊓
            Subgroup.centralizer (E' : Set (ModGL .E6 L))) : Set (ModGL .E6 L)) =
              fixedA2Torus L := by
  obtain ⟨y₀, hy₀, hEM, hw, x, hx, hxc⟩ :=
    TwE6HyperplaneFrame.exists_conj_weylImage_zpowers_c halg hEG hE hcard hnt he1 heS
  let E' := E.map (MulAut.conj y₀).toMonoidHom
  haveI : Finite E' := Finite.of_surjective _
    ((MulAut.conj y₀).toMonoidHom.subgroupMap_surjective E)
  have hE' : IsElemAbelian 3 E' := hE.map _
  have hcard' : Nat.card E' = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj y₀).injective]
    exact hcard
  have hET : ¬ E' ≤ torusGroup .E6 L := by
    intro h
    apply hnt
    apply (SCFourCover.e6AdToral_map_conj hy₀ E).mp
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    intro a ha
    simpa using h ha
  have hcR : cE6 ∈ modelHomE6.range :=
    ⟨⟨1, Multiplicative.ofAdd 1⟩, modelHomE6_c⟩
  have hAS : ∀ a (ha : a ∈ E'), weylQuotientHom .E6 L ⟨a, hEM ha⟩ ∈ modelHomE6.range :=
    fun a ha => (Subgroup.zpowers_le.mpr hcR) (hw a ha)
  have hAg : ∀ a (ha : a ∈ E') i, weylQuotientHom .E6 L ⟨a, hEM ha⟩ ≠ gE6 i := by
    intro a ha i h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hw a ha)
    exact cE6_zpow_ne_gE6 m i (hm.trans h)
  have hchar : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; decide
  refine ⟨y₀, hy₀, hEM, hw, x, hx, hxc, ?_⟩
  exact connectedCentralizer_eq_fixedA2Torus hchar hEM hE' hcard' hET hAS hAg hw hx hxc

theorem weylMatList_parameter_iterate_six {F : Type} [Field F]
    {μ ν : ℤ × ℤ} (h : (μ, ν) ∈ weylMatList) (p : Fˣ × Fˣ) :
    (fun q : Fˣ × Fˣ => (q.1 ^ μ.1 * q.2 ^ μ.2, q.1 ^ ν.1 * q.2 ^ ν.2))^[6] p = p := by
  simp only [weylMatList, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp [Function.iterate_succ_apply', Function.iterate_zero,
    mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

theorem normalizer_fixedA2Torus_pow_six
    (R : ModGL .E6 L) (hR : R ∈ Subgroup.normalizer (fixedA2Torus L))
    {t : ModGL .E6 L} (ht : t ∈ fixedA2Torus L) :
    R ^ 6 * t * (R ^ 6)⁻¹ = t := by
  classical
  obtain ⟨p, rfl⟩ := ht
  have hmem : ∀ s u : Lˣ, ∃ a b : Lˣ,
      fixedA2Rho L (diagSL3 a b) = R * fixedA2Rho L (diagSL3 s u) * R⁻¹ := by
    intro s u
    obtain ⟨q, hq⟩ := ((Subgroup.mem_set_normalizer_iff.mp hR)
      (fixedA2Rho L (diagSL3 s u))).mp ⟨(s, u), rfl⟩
    exact ⟨q.1, q.2, hq⟩
  choose θ₁ θ₂ hθ using hmem
  have hθ' : ∀ s u : Lˣ, R * rootDiagUnit .E6 (diagTuple s u) * R⁻¹ =
      rootDiagUnit .E6 (diagTuple (θ₁ s u) (θ₂ s u)) := by
    intro s u
    rw [← fixedA2Rho_diagSL3 L s u, ← fixedA2Rho_diagSL3 L (θ₁ s u) (θ₂ s u)]
    exact (hθ s u).symm
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_diagWt_eq (μ := (1, 0)) (by decide)
  obtain ⟨ℓ₂, hℓ₂⟩ := exists_diagWt_eq (μ := (0, 1)) (by decide)
  obtain ⟨b₁, b₂, hθform, hrows, hcols⟩ :=
    exists_weightMatrix_of_conj_rootDiagUnit (Ω := L) diagTuple (diagWt 0) (diagWt 2)
      rootChar_diagTuple R θ₁ θ₂ hθ' (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
      ⟨congrArg Prod.fst hℓ₁, congrArg Prod.snd hℓ₁⟩
      ⟨congrArg Prod.fst hℓ₂, congrArg Prod.snd hℓ₂⟩
  have hμν : (((diagWt 0 b₁, diagWt 2 b₁), (diagWt 0 b₂, diagWt 2 b₂)) ∈
      weylMatList) := by
    refine weightMatrix_mem_weylMatList _ (diagWt_mem_diagWtList b₁) _
      (diagWt_mem_diagWtList b₂) ?_ ?_
    · intro α hα
      obtain ⟨a, rfl⟩ := exists_diagWt_eq hα
      obtain ⟨b, hb1, hb2⟩ := hrows a
      rw [← hb1, ← hb2]
      exact diagWt_mem_diagWtList b
    · intro β hβ
      obtain ⟨b, rfl⟩ := exists_diagWt_eq hβ
      obtain ⟨a, ha1, ha2⟩ := hcols b
      exact ⟨(diagWt 0 a, diagWt 2 a), diagWt_mem_diagWtList a,
        by rw [ha1, ha2]⟩
  let f : Lˣ × Lˣ → Lˣ × Lˣ := fun q =>
    (q.1 ^ (diagWt 0 b₁) * q.2 ^ (diagWt 2 b₁),
      q.1 ^ (diagWt 0 b₂) * q.2 ^ (diagWt 2 b₂))
  have hRaction : ∀ p : Lˣ × Lˣ,
      R * rootDiagUnit .E6 (diagTuple p.1 p.2) * R⁻¹ =
        rootDiagUnit .E6 (diagTuple (f p).1 (f p).2) := by
    intro p
    rw [hθ' p.1 p.2]
    simp only [f]
    rw [(hθform p.1 p.2).1, (hθform p.1 p.2).2]
  have hiter : ∀ (m : ℕ) (p : Lˣ × Lˣ),
      R ^ m * rootDiagUnit .E6 (diagTuple p.1 p.2) * (R ^ m)⁻¹ =
        rootDiagUnit .E6 (diagTuple (f^[m] p).1 (f^[m] p).2) := by
    intro m
    induction m with
    | zero =>
        intro p
        simp [Function.iterate_zero]
    | succ m ih =>
        intro p
        calc
          R ^ (m + 1) * rootDiagUnit .E6 (diagTuple p.1 p.2) * (R ^ (m + 1))⁻¹
              = R ^ m * (R * rootDiagUnit .E6 (diagTuple p.1 p.2) * R⁻¹) *
                  (R ^ m)⁻¹ := by
                rw [pow_succ, mul_inv_rev]
                group
          _ = R ^ m * rootDiagUnit .E6 (diagTuple (f p).1 (f p).2) * (R ^ m)⁻¹ := by
                rw [hRaction p]
          _ = rootDiagUnit .E6 (diagTuple (f^[m] (f p)).1 (f^[m] (f p)).2) := ih (f p)
          _ = rootDiagUnit .E6 (diagTuple (f^[m+1] p).1 (f^[m+1] p).2) := by
                rw [Function.iterate_succ_apply]
  have hsix := hiter 6 p
  rw [weylMatList_parameter_iterate_six hμν p] at hsix
  change R ^ 6 * fixedA2Rho L (diagSL3 p.1 p.2) * (R ^ 6)⁻¹ =
    fixedA2Rho L (diagSL3 p.1 p.2)
  rw [fixedA2Rho_diagSL3 L p.1 p.2]
  exact hsix

theorem normalizer_pow_six_centralizes_connectedCentralizer
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hnt : ¬ SCFourCover.E6AdToral E)
    {e : ModGL .E6 L} (he1 : e ≠ 1)
    (heS : e ∈ closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))))
    {g : ModGL .E6 L} (hg : g ∈ adjointGroup .E6 L)
    (hgE : g ∈ Subgroup.normalizer (E : Set (ModGL .E6 L)))
    {t : ModGL .E6 L}
    (ht : t ∈ closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)))) :
    g ^ 6 * t * (g ^ 6)⁻¹ = t := by
  classical
  obtain ⟨y₀, hy₀, hEM, hw, x, hx, hxc, hS0⟩ :=
    exists_conj_connectedCentralizer_eq_fixedA2Torus halg hEG hE hcard hnt he1 heS
  let E' := E.map (MulAut.conj y₀).toMonoidHom
  have hS' : (closedIdentityComponent (adjointGroup .E6 L ⊓
      Subgroup.centralizer (E' : Set (ModGL .E6 L))) : Set (ModGL .E6 L)) =
      fixedA2Torus L := by
    simpa only [E'] using hS0
  have hZmap : (adjointGroup .E6 L ⊓
      Subgroup.centralizer (E : Set (ModGL .E6 L))).map
        (MulAut.conj y₀).toMonoidHom =
      adjointGroup .E6 L ⊓ Subgroup.centralizer (E' : Set (ModGL .E6 L)) := by
    simpa only [E'] using map_adjoint_centralizer_conj E hy₀
  have hSmap : (closedIdentityComponent (adjointGroup .E6 L ⊓
      Subgroup.centralizer (E : Set (ModGL .E6 L)))).map (MulAut.conj y₀).toMonoidHom =
      closedIdentityComponent (adjointGroup .E6 L ⊓
        Subgroup.centralizer (E' : Set (ModGL .E6 L))) := by
    rw [← closedIdentityComponent_map_conj
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) y₀, hZmap]
  have hSfixed : ((closedIdentityComponent (adjointGroup .E6 L ⊓
      Subgroup.centralizer (E : Set (ModGL .E6 L)))).map
        (MulAut.conj y₀).toMonoidHom : Set (ModGL .E6 L)) = fixedA2Torus L := by
    rw [hSmap]
    exact hS'
  have hgS : g ∈ Subgroup.normalizer (closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) :
        Set (ModGL .E6 L)) :=
    mem_normalizer_connected_adjoint_centralizer E hg hgE
  let R : ModGL .E6 L := y₀ * g * y₀⁻¹
  have hR : R ∈ Subgroup.normalizer (fixedA2Torus L) := by
    refine Subgroup.mem_set_normalizer_iff.mpr fun z => ?_
    constructor
    · intro hz
      rw [← hSfixed] at hz ⊢
      obtain ⟨s, hs, rfl⟩ := hz
      refine ⟨g * s * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgS s).mp hs, ?_⟩
      simp only [R, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · intro hz
      rw [← hSfixed] at hz ⊢
      obtain ⟨s, hs, hsz⟩ := hz
      refine ⟨g⁻¹ * s * g, (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ hgS) s).mp hs, ?_⟩
      simp only [R, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hsz ⊢
      calc
        y₀ * (g⁻¹ * s * g) * y₀⁻¹ =
            (y₀ * g * y₀⁻¹)⁻¹ * (y₀ * s * y₀⁻¹) * (y₀ * g * y₀⁻¹) := by group
        _ = z := by
          rw [hsz]
          group
  have ht' : y₀ * t * y₀⁻¹ ∈ fixedA2Torus L := by
    rw [← hSfixed]
    exact ⟨t, ht, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hA := normalizer_fixedA2Torus_pow_six R hR ht'
  have hR6 : R ^ 6 = y₀ * g ^ 6 * y₀⁻¹ := by
    change ((MulAut.conj y₀) g) ^ 6 = y₀ * g ^ 6 * y₀⁻¹
    rw [← map_pow (MulAut.conj y₀) g 6]
    simp only [MulAut.conj_apply]
  calc
    g ^ 6 * t * (g ^ 6)⁻¹ =
        y₀⁻¹ * (R ^ 6 * (y₀ * t * y₀⁻¹) * (R ^ 6)⁻¹) * y₀ := by
      rw [hR6]
      group
    _ = y₀⁻¹ * (y₀ * t * y₀⁻¹) * y₀ := by rw [hA]
    _ = t := by group

end CFSG.StandardType.TwE6E4bTorus
