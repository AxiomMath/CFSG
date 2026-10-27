module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27CommutatorLePiCompl
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27FixedInversion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralKleinFourContainingInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PiCoreCharacteristic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed-point ingredient for the final `[S,U] ≰ F(U)` conjunct

Lemma 2.7 has proved `[M, ⟨t⟩] ≤ F_{πᶜ}(M)`.  Since `M ⊈ Ĥ`, the
commutator subgroup is nontrivial, so `F_{πᶜ}(M) ≠ 1`.  It is an odd normal
subgroup of `M` inverted by `t`, and `t` lies in a Klein-four subgroup of a
Sylow `2`-subgroup of `M`; the Klein-four fixed-point lemma then supplies an
involution `t' ∈ C_M(t)` with a nontrivial fixed part on `F_{πᶜ}(M)`.
-/

noncomputable section

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Conjugating by `g` maps the centralizer of `x` onto the centralizer of
`g * x * g⁻¹`. -/
private theorem map_centralizer_singleton_conj
    {G : Type u} [Group G] (g x : G) :
    Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.centralizer ({x} : Set G)) =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  let e : G ≃* G := MulAut.conj g
  apply le_antisymm
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hyz⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    have hzx : z * x = x * z :=
      (Subgroup.mem_centralizer_iff.mp hz x (by simp)).symm
    have hmap' : e z * e x = e x * e z := by
      simpa [map_mul] using congrArg e.toMonoidHom hzx
    change e z = y at hyz
    rw [hyz] at hmap'
    simpa [e, MulAut.conj_apply] using hmap'.symm
  · intro y hy
    let z : G := e.symm y
    have he_x : e x = g * x * g⁻¹ := by simp [e]
    have hzC : z ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.mp hw]
      have heq : y * e x = e x * y :=
        (Subgroup.mem_centralizer_iff.mp hy (e x) (by simpa using he_x)).symm
      have hmap' : e.symm y * e.symm (e x) = e.symm (e x) * e.symm y := by
        simpa [map_mul] using congrArg e.symm.toMonoidHom heq
      simp [e, he_x] at hmap'
      group at hmap'
      simpa [z, e, he_x, mul_assoc] using hmap'.symm
    refine Subgroup.mem_map.mpr ⟨z, hzC, ?_⟩
    change e (e.symm y) = y
    exact e.apply_symm_apply y

/-- `O(H)` is normal in `H`. -/
private theorem oddCoreOf_isNormalIn {G : Type u} [Group G]
    (H : Subgroup G) : IsNormalIn (oddCoreOf H) H := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
    exact y.2
  · intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥H) * y * (⟨h, hh⟩ : ↥H)⁻¹, ?_, by simp⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥H)).conj_mem y hy (⟨h, hh⟩ : ↥H)

/-- `F(U)` is normal in `H = C_G(t)`. -/
private theorem FU_isNormalIn_H {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : IsNormalIn c.FU c.H := by
  change IsNormalIn ((fittingSubgroup (↥c.U)).map c.U.subtype) c.H
  exact map_characteristic_isNormalIn_of_isNormalIn
    (K := fittingSubgroup (↥c.U))
    (hKchar := by infer_instance)
    (hHnormal := by
      change IsNormalIn (oddCoreOf c.H) c.H
      exact oddCoreOf_isNormalIn c.H)

/-- `2 ∈ π(F(Ĥ))`, because `t ∈ O₂(Ĥ) ≤ F(Ĥ)` has order two. -/
private theorem two_mem_primesOfOrder_fitting_Hhat
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (h26 : CentralizerStructure c) :
    2 ∈ primesOfOrder (fittingSubgroupOf c.Hhat) := by
  have ht2 : c.t ∈ twoCoreOf c.Hhat := centralizerStructure_t_mem_twoCore c h26
  have hq2 : twoCoreOf c.Hhat = qCoreOf c.Hhat 2 := by
    rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton c.Hhat 2 Nat.prime_two]
  have hxt : c.t ∈ qCoreOf c.Hhat 2 := by simpa [hq2] using ht2
  have hxF : c.t ∈ fittingSubgroupOf c.Hhat :=
    qCoreOf_le_fittingSubgroupOf c.Hhat 2 Nat.prime_two hxt
  have hord : orderOf c.t = 2 :=
    orderOf_eq_prime c.t_involution.2 c.t_involution.1
  have h2dvd : 2 ∣ Nat.card (↥(fittingSubgroupOf c.Hhat)) := by
    have hdvd : orderOf c.t ∣ Nat.card (↥(fittingSubgroupOf c.Hhat)) := by
      let : Fintype (↥(fittingSubgroupOf c.Hhat)) := Fintype.ofFinite _
      have h := orderOf_dvd_card (x := (⟨c.t, hxF⟩ : fittingSubgroupOf c.Hhat))
      simpa [Nat.card_eq_fintype_card, Subgroup.orderOf_mk] using h
    rwa [hord] at hdvd
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, Nat.card_pos.ne'⟩

/-- `[M,⟨t⟩] ≠ 1`: otherwise `M` centralizes `t`, so `M ≤ Ĥ`. -/
private theorem commutator_piCore_ne_bot_of_Lemma27Hypothesis
    {G : Type u} [Group G] [Finite G]
    (_hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) :
    ⁅M, Subgroup.zpowers c.t⁆ ≠ ⊥ := by
  classical
  rcases hM with ⟨hMproper, _hControl, hMnotle, _hEt, _hSylow, _hBranch⟩
  intro hbot
  apply hMnotle
  intro m hm
  have hMleCz : M ≤ Subgroup.centralizer
      ((Subgroup.zpowers c.t : Subgroup G) : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := M) (H₂ := Subgroup.zpowers c.t)).1 hbot
  have hmCz : m ∈ Subgroup.centralizer
      ((Subgroup.zpowers c.t : Subgroup G) : Set G) := hMleCz hm
  have hmC : m ∈ Subgroup.centralizer ({c.t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyt : y = c.t := by simpa using hy
    rw [hyt]
    exact Subgroup.mem_centralizer_iff.mp hmCz c.t
      (Subgroup.mem_zpowers c.t)
  have hmH : m ∈ c.H := by
    rw [c.H_eq_centralizer]
    exact hmC
  exact c.H_le_Hhat hmH

/-- `F_{πᶜ}(M) ≠ 1` under the Lemma 2.7 hypotheses. -/
public theorem piCore_compl_fitting_ne_bot_of_Lemma27Hypothesis
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) :
    let π := primesOfOrder (fittingSubgroupOf c.Hhat)
    piCoreOf (fittingSubgroupOf M) πᶜ ≠ ⊥ := by
  classical
  intro π
  have hComm : ⁅M, Subgroup.zpowers c.t⁆ ≤
      piCoreOf (fittingSubgroupOf M) πᶜ :=
    lemma_2_7_commutator_le_piCore_compl hmin c M hM
  have hCommNe : ⁅M, Subgroup.zpowers c.t⁆ ≠ ⊥ :=
    commutator_piCore_ne_bot_of_Lemma27Hypothesis hmin c M hM
  intro hbot
  apply hCommNe
  exact le_bot_iff.mp (hComm.trans (le_of_eq hbot))

/-- `F_{πᶜ}(M)` is odd under the Lemma 2.7 hypotheses. -/
public theorem piCore_compl_odd_card_of_Lemma27Hypothesis
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) :
    let π := primesOfOrder (fittingSubgroupOf c.Hhat)
    let A := piCoreOf (fittingSubgroupOf M) πᶜ
    Nat.Coprime 2 (Nat.card (↥A)) := by
  classical
  intro π A
  have h26 : CentralizerStructure c := theorem_2_6 hmin c
  have h2π : 2 ∈ primesOfOrder (fittingSubgroupOf c.Hhat) :=
    two_mem_primesOfOrder_fitting_Hhat c h26
  have hAodd' : Odd (Nat.card (↥A)) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have h2dvd : 2 ∣ Nat.card (↥A) := even_iff_two_dvd.mp heven
    have h2pf : 2 ∈ (Nat.card (↥A)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, Nat.card_pos.ne'⟩
    have hAeq : A = piCoreOf (fittingSubgroupOf M) {q : ℕ | q ∉ π} := by
      rfl
    have h2pf' : 2 ∈ (Nat.card ↥(piCoreOf (fittingSubgroupOf M)
        {q : ℕ | q ∉ π})).primeFactors := by
      simpa [hAeq] using h2pf
    have h2c : 2 ∉ π := by
      simpa using (piCoreOf_primeDivisors (fittingSubgroupOf M)
        {q : ℕ | q ∉ π} 2 h2pf')
    exact h2c (by simpa [π] using h2π)
  exact Nat.coprime_two_left.mpr hAodd'

/-- An involution in `C_M(t)` with nontrivial fixed part on `F_{πᶜ}(M)`. -/
public theorem exists_fixed_involution_of_Lemma27Hypothesis
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) :
    let π := primesOfOrder (fittingSubgroupOf c.Hhat)
    let A := piCoreOf (fittingSubgroupOf M) πᶜ
    ∃ t' : G,
      t' ∈ M ∧ t' ∈ Subgroup.centralizer ({c.t} : Set G) ∧
        t' ≠ 1 ∧ t' ≠ c.t ∧ t' * t' = 1 ∧
          A ⊓ Subgroup.centralizer ({t'} : Set G) ≠ ⊥ := by
  classical
  intro π A
  rcases hM with ⟨hMproper, hControl, hMnotle, hEt, hSylow, hBranch⟩
  let hM' : Lemma27Hypothesis c M :=
    ⟨hMproper, hControl, hMnotle, hEt, hSylow, hBranch⟩
  have h26 : CentralizerStructure c := theorem_2_6 hmin c
  have htM : c.t ∈ M := t_mem_M_of_centralizerStructure c M hM' h26
  have hAne : A ≠ ⊥ :=
    piCore_compl_fitting_ne_bot_of_Lemma27Hypothesis hmin c M hM'
  have hAodd : Nat.Coprime 2 (Nat.card (↥A)) :=
    piCore_compl_odd_card_of_Lemma27Hypothesis hmin c M hM'
  have hAnorm : IsNormalIn A M := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := M) (F := fittingSubgroupOf M)
      (K := piCore πᶜ (↥(fittingSubgroupOf M)))
      (piCore_characteristic πᶜ)
      (by simpa [fittingSubgroupOf] using fittingSubgroupOf_isNormalIn M)
    simpa [A, piCoreOf] using h
  rcases lemma_2_7_piCore_disjoint_and_inverted hmin c M hM'.2.1 with
    ⟨_hDdisj, hInv⟩
  have hAinvt : ∀ x : G, x ∈ (A : Set G) → c.t * x * c.t⁻¹ = x⁻¹ :=
    hInv htM
  -- Put `t` in a Klein-four subgroup `V` of `M`.
  have hDM : IsDGroup (↥M) := properSubgroups_areDGroups hmin M hMproper
  have hSylowM : HasCyclicOrDihedralSylowTwo (↥M) := by
    rcases hDM with ⟨hS, _⟩ | ⟨hS, _⟩ | ⟨hS, _K, _hKp, _L, _hL, _hLidx, _hLmodel⟩
    · exact hS
    · exact hS
    · exact hS
  let tM : ↥M := ⟨c.t, htM⟩
  have htMInv : IsInvolution tM := by
    constructor
    · intro h
      apply c.t_involution.1
      exact congrArg Subtype.val h
    · apply Subtype.ext
      exact c.t_involution.2
  have htzp : IsPGroup 2 (Subgroup.zpowers tM) := by
    apply IsPGroup.of_card (n := 1)
    have hord : orderOf tM = 2 := orderOf_eq_prime
      (by apply Subtype.ext; exact c.t_involution.2)
      (by
        intro h
        apply c.t_involution.1
        exact congrArg Subtype.val h)
    simp [Nat.card_zpowers, hord]
  obtain ⟨P, htP⟩ := IsPGroup.exists_le_sylow (G := ↥M) (p := 2) htzp
  rcases hSylowM P with hPcyc | ⟨mP, hmP, eP⟩
  · exact False.elim (hSylow P hPcyc)
  · have htP' : tM ∈ (P : Subgroup (↥M)) :=
      htP (Subgroup.mem_zpowers tM)
    obtain ⟨V', hV'P, hV', htV'⟩ :=
      exists_kleinFour_of_dihedral_mulEquiv_containing_involution
        (P : Subgroup (↥M)) hmP eP.some htP' htMInv
    let V : Subgroup G := V'.map M.subtype
    have hVleM : V ≤ M := Subgroup.map_subtype_le (H := M) V'
    have hVK4 : IsKleinFour V := by
      let e : V' ≃* V :=
        V'.equivMapOfInjective M.subtype M.subtype_injective
      exact {
        card_four := (Nat.card_congr e.toEquiv).symm.trans hV'.card_four
        exponent_two :=
          (Monoid.exponent_eq_of_mulEquiv e).symm.trans hV'.exponent_two
      }
    have htV : c.t ∈ V := by
      refine Subgroup.mem_map.mpr ⟨tM, htV', ?_⟩
      rfl
    obtain ⟨t', ht'M, ht'C, ht'V, ht'ne, ht'ne_t, ht'fix⟩ :=
      exists_fixed_involution_centralizer_of_kleinFour_inverted
        M A V c.t hVK4 hVleM htV hAne hAodd hAnorm hAinvt
    have ht'2 : t' * t' = 1 := by
      let : IsKleinFour (↥V) := hVK4
      let t'V : ↥V := ⟨t', ht'V⟩
      exact congrArg Subtype.val (IsKleinFour.mul_self t'V)
    exact ⟨t', ht'M, ht'C, ht'ne, ht'ne_t, ht'2, ht'fix⟩

/-- The third-involution transfer closing `¬ [S,U] ≤ F(U)` in Lemma 2.7.

Assuming `[S,U] ≤ F(U)`, conjugate the fixed-point involution `t'` to the
distinguished involution `t`.  The odd fixed part `x ∈ C_A(t')` lies in the
odd core `U'` of the conjugate centralizer, and `r = t t'` is a `2`-element
of `H' = C_G(t')`.  Conjugating `r` into a Sylow `2`-subgroup of `H'`
expresses `[t,x] = [r,x]` as a commutator of `[S',U']`, hence in `F(U')`.
But `[t,x]` is a nontrivial element of the `π'`-group `A`, while `F(U')` is
a `π`-group. -/
public theorem lemma_2_7_commutator_S_U_not_le_FU
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) :
    ¬ ⁅(c.S : Subgroup G), c.U⁆ ≤ c.FU := by
  classical
  let π := primesOfOrder (fittingSubgroupOf c.Hhat)
  let A := piCoreOf (fittingSubgroupOf M) πᶜ
  intro hle
  obtain ⟨t', ht'M, ht'C, ht'ne, ht'ne_t, ht'2, ht'fix⟩ :=
    exists_fixed_involution_of_Lemma27Hypothesis hmin c M hM
  obtain ⟨xS, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp ht'fix
  let x : G := xS
  have hxA : x ∈ A := xS.2.1
  have hxCt' : x ∈ Subgroup.centralizer ({t'} : Set G) := xS.2.2
  have hAodd : Nat.Coprime 2 (Nat.card (↥A)) :=
    piCore_compl_odd_card_of_Lemma27Hypothesis hmin c M hM
  have hxodd : Nat.Coprime 2 (orderOf x) := by
    have hdvd : orderOf x ∣ Nat.card (↥A) := by
      let : Fintype (↥A) := Fintype.ofFinite _
      have h := orderOf_dvd_card (x := (⟨x, hxA⟩ : A))
      simpa [Nat.card_eq_fintype_card, Subgroup.orderOf_mk] using h
    exact Nat.Coprime.of_dvd_right hdvd hAodd
  have h26 : CentralizerStructure c := theorem_2_6 hmin c
  have htM : c.t ∈ M := t_mem_M_of_centralizerStructure c M hM h26
  rcases lemma_2_7_piCore_disjoint_and_inverted hmin c M hM.2.1 with
    ⟨_hDdisj, hInv⟩
  have hAinvt : ∀ y : G, y ∈ A → c.t * y * c.t⁻¹ = y⁻¹ := hInv htM
  obtain ⟨g, hg⟩ :=
    fact_2_preamble_involutions_conjugate_proved hmin c.t t'
      c.t_involution ⟨ht'ne, by simpa [pow_two] using ht'2⟩
  let e : G ≃* G := MulAut.conj g
  have ht'e : e c.t = t' := by
    simpa [e, MulAut.conj_apply] using hg
  let H' : Subgroup G := c.H.map e.toMonoidHom
  let U' : Subgroup G := c.U.map e.toMonoidHom
  let F' : Subgroup G := c.FU.map e.toMonoidHom
  let S' : Subgroup G := (c.S : Subgroup G).map e.toMonoidHom
  have hH'eq : H' = Subgroup.centralizer ({t'} : Set G) := by
    calc
      H' = (Subgroup.centralizer ({c.t} : Set G)).map e.toMonoidHom := by
        rw [← c.H_eq_centralizer]
      _ = Subgroup.centralizer ({g * c.t * g⁻¹} : Set G) :=
        map_centralizer_singleton_conj g c.t
      _ = Subgroup.centralizer ({t'} : Set G) := by
        have hg' : g * c.t * g⁻¹ = t' := by
          simpa [e, MulAut.conj_apply] using ht'e
        rw [hg']
  have hCmap : (Subgroup.centralizer ({c.t} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({t'} : Set G) := by
    have hg' : g * c.t * g⁻¹ = t' := by
      simpa [e, MulAut.conj_apply] using ht'e
    rw [← hg']
    exact map_centralizer_singleton_conj g c.t
  have hxH' : x ∈ H' := by
    rw [hH'eq, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact Subgroup.mem_centralizer_iff.mp hxCt' t' (by simp)
  have hxpre : e.symm x ∈ Subgroup.centralizer ({c.t} : Set G) := by
    have hxmem : x ∈ (Subgroup.centralizer ({c.t} : Set G)).map e.toMonoidHom := by
      rw [hCmap]
      rw [← hH'eq]
      exact hxH'
    rcases Subgroup.mem_map.mp hxmem with ⟨w, hw, hw_eq⟩
    have hw_eq' : w = e.symm x := by
      apply e.injective
      change e w = e (e.symm x)
      rw [e.apply_symm_apply x]
      exact hw_eq
    simpa [hw_eq'] using hw
  have hXodd : Nat.Coprime 2
      (Nat.card (↥(Subgroup.zpowers (e.symm x)))) := by
    have hord : orderOf (e.symm x) = orderOf x := by
      simpa using (orderOf_injective e.symm.toMonoidHom e.symm.injective x)
    rw [Nat.card_zpowers, hord]
    exact hxodd
  have hXH : Subgroup.zpowers (e.symm x) ≤ c.H := by
    have hle : Subgroup.zpowers (e.symm x) ≤
        Subgroup.centralizer ({c.t} : Set G) :=
      Subgroup.zpowers_le.2 hxpre
    rw [c.H_eq_centralizer]
    exact hle
  have hXU : Subgroup.zpowers (e.symm x) ≤ c.U :=
    odd_order_subgroup_le_U_of_H_eq_SU hmin c hXH hXodd
  have hxU' : x ∈ U' := by
    refine Subgroup.mem_map.mpr ⟨e.symm x, hXU (Subgroup.mem_zpowers (e.symm x)), ?_⟩
    change e (e.symm x) = x
    exact e.apply_symm_apply x
  have htH' : c.t ∈ H' := by
    rw [hH'eq, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact (Subgroup.mem_centralizer_iff.mp ht'C c.t (by simp)).symm
  have ht'H' : t' ∈ H' := by
    rw [hH'eq, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
  let r : G := c.t * t'
  have hrH' : r ∈ H' := H'.mul_mem htH' ht'H'
  have hcomm_tt' : c.t * t' = t' * c.t :=
    Subgroup.mem_centralizer_iff.mp ht'C c.t (by simp)
  have hr2 : r * r = 1 := by
    dsimp [r]
    calc
      (c.t * t') * (c.t * t') = (c.t * c.t) * (t' * t') := by
        calc
          (c.t * t') * (c.t * t') = c.t * (t' * c.t) * t' := by group
          _ = c.t * (c.t * t') * t' := by rw [hcomm_tt']
          _ = (c.t * c.t) * (t' * t') := by group
      _ = 1 := by
        have ht2' : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
        rw [ht2', ht'2]
        simp
  have hS'H' : S' ≤ H' := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨s, hs, rfl⟩
    exact Subgroup.mem_map.mpr ⟨s, centralizerSetup_S_le_H c hs, by
      simp [S', H', e, MulAut.conj_apply]⟩
  have hS'Hp : IsPGroup 2 (S'.subgroupOf H') := by
    have hS'p : IsPGroup 2 S' := by
      exact c.S.isPGroup'.of_equiv
        (Subgroup.equivMapOfInjective (c.S : Subgroup G) e.toMonoidHom e.injective)
    exact hS'p.of_equiv (Subgroup.subgroupOfEquivOfLe hS'H').symm
  obtain ⟨P, hS'P⟩ := IsPGroup.exists_le_sylow (G := H') hS'Hp
  let Pmap : Subgroup G := (P : Subgroup H').map H'.subtype
  have hPmap_p : IsPGroup 2 Pmap := (P.isPGroup').map H'.subtype
  have hSlePmap : S' ≤ Pmap := by
    intro y hy
    have hyH' : y ∈ H' := hS'H' hy
    have hySH : (⟨y, hyH'⟩ : H') ∈ S'.subgroupOf H' := by
      change y ∈ S'
      exact hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hyH'⟩, hS'P hySH, rfl⟩
  let Pmap0 : Subgroup G := Pmap.map e.symm.toMonoidHom
  have hPmap0_p : IsPGroup 2 Pmap0 := hPmap_p.map e.symm.toMonoidHom
  have hSlePmap0 : (c.S : Subgroup G) ≤ Pmap0 := by
    intro y hy
    refine Subgroup.mem_map.mpr ⟨e y, ?_, ?_⟩
    · exact hSlePmap (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
    · change e.symm (e y) = y
      exact e.symm_apply_apply y
  have hPmap0_eq : Pmap0 = c.S := c.S.is_maximal' hPmap0_p hSlePmap0
  have hPmap_eq : Pmap = S' := by
    have heq := congrArg (Subgroup.map e.toMonoidHom) hPmap0_eq
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
      ext z
      simp [e]
    have hleft : Pmap0.map e.toMonoidHom = Pmap := by
      change (Pmap.map e.symm.toMonoidHom).map e.toMonoidHom = Pmap
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    have hright : (c.S : Subgroup G).map e.toMonoidHom = S' := rfl
    rw [hleft] at heq
    rw [hright] at heq
    exact heq
  let rH : ↥H' := ⟨r, hrH'⟩
  have hrHp : IsPGroup 2 (Subgroup.zpowers rH) := by
    by_cases hr1 : rH = 1
    · rw [hr1]
      apply IsPGroup.of_card (n := 0)
      simp [Nat.card_zpowers]
    · apply IsPGroup.of_card (n := 1)
      have hpow : rH * rH = 1 := by
        apply Subtype.ext
        simpa [rH, r] using hr2
      have hpow2 : rH ^ 2 = 1 := by simpa [pow_two] using hpow
      have hord : orderOf rH = 2 := orderOf_eq_prime hpow2 hr1
      simp [Nat.card_zpowers, hord]
  obtain ⟨Q, hrQ⟩ := IsPGroup.exists_le_sylow (G := H') hrHp
  obtain ⟨h, hh⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq H' (Sylow 2 H')
      inferInstance inferInstance P Q
  have hh2 : (h : H')⁻¹ • Q = P := by
    have hh' := congrArg (fun S : Sylow 2 H' => (h : H')⁻¹ • S) hh
    simpa [smul_smul] using hh'.symm
  have hconjP : (h : H')⁻¹ * rH * (h : H') ∈
      (P : Subgroup H') := by
    have hmem : (h : H')⁻¹ * rH * ((h : H')⁻¹)⁻¹ ∈
        (((h : H')⁻¹ : H') • Q : Sylow 2 H') := by
      change (MulAut.conj (h : H')⁻¹) rH ∈
        (Q : Subgroup H').map (MulAut.conj (h : H')⁻¹).toMonoidHom
      exact Subgroup.mem_map.mpr ⟨rH, hrQ (Subgroup.mem_zpowers rH), rfl⟩
    rw [hh2] at hmem
    simp only [inv_inv] at hmem
    change (h : H')⁻¹ * rH * (h : H') ∈ (P : Subgroup H')
    exact hmem
  let rh : G := (h : G)⁻¹ * r * (h : G)
  have hrS' : rh ∈ S' := by
    have hmem : (((h : H')⁻¹ * rH * (h : H')) : G) ∈
        (P : Subgroup H').map H'.subtype := by
      exact Subgroup.mem_map.mpr
        ⟨(h : H')⁻¹ * rH * (h : H'), hconjP, rfl⟩
    rw [← hPmap_eq]
    change (((h : H')⁻¹ * rH * (h : H')) : G) ∈ Pmap
    exact hmem
  have hUnormH : IsNormalIn c.U c.H := by
    change IsNormalIn (oddCoreOf c.H) c.H
    exact oddCoreOf_isNormalIn c.H
  have hFUnormH : IsNormalIn c.FU c.H := FU_isNormalIn_H c
  have hUnormH' : IsNormalIn U' H' := by
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨u, hu, rfl⟩
      exact Subgroup.mem_map.mpr ⟨u, hUnormH.1 hu, by simp [U', H', e, MulAut.conj_apply]⟩
    · intro n hn u hu
      rcases Subgroup.mem_map.mp hn with ⟨n0, hn0, rfl⟩
      rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
      refine Subgroup.mem_map.mpr ⟨n0 * u0 * n0⁻¹, hUnormH.2 n0 hn0 u0 hu0, ?_⟩
      simp [U', e, MulAut.conj_apply]
      group
  have hF'normH' : IsNormalIn F' H' := by
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨f, hf, rfl⟩
      exact Subgroup.mem_map.mpr ⟨f, hFUnormH.1 hf, by simp [F', H', e, MulAut.conj_apply]⟩
    · intro n hn f hf
      rcases Subgroup.mem_map.mp hn with ⟨n0, hn0, rfl⟩
      rcases Subgroup.mem_map.mp hf with ⟨f0, hf0, rfl⟩
      refine Subgroup.mem_map.mpr ⟨n0 * f0 * n0⁻¹, hFUnormH.2 n0 hn0 f0 hf0, ?_⟩
      simp [F', e, MulAut.conj_apply]
      group
  have huU' : (h : G)⁻¹ * x * (h : G) ∈ U' := by
    rcases Subgroup.mem_map.mp hxU' with ⟨x0, hx0, hx0_eq⟩
    rcases Subgroup.mem_map.mp (show (h : G) ∈ H' from h.2)
      with ⟨h0, hh0, hh0_eq⟩
    have hnx : h0⁻¹ * x0 * h0 ∈ c.U := by
      simpa using hUnormH.2 (h0⁻¹) (c.H.inv_mem hh0) x0 hx0
    refine Subgroup.mem_map.mpr ⟨h0⁻¹ * x0 * h0, hnx, ?_⟩
    rw [← hh0_eq, ← hx0_eq]
    simp [U', e, hx0_eq, hh0_eq, MulAut.conj_apply]
    group
  have hS'U' : ⁅S', U'⁆ ≤ F' := by
    have hmap : (⁅(c.S : Subgroup G), c.U⁆).map e.toMonoidHom ≤
        c.FU.map e.toMonoidHom := Subgroup.map_mono hle
    simpa [S', U', F', Subgroup.map_commutator] using hmap
  have hcommF' : ⁅rh, (h : G)⁻¹ * x * (h : G)⁆ ∈ F' :=
    (Subgroup.commutator_le.mp hS'U' rh hrS' ((h : G)⁻¹ * x * (h : G))) huU'
  have hcommconj : (h : G) * ⁅rh, (h : G)⁻¹ * x * (h : G)⁆ * (h : G)⁻¹ ∈ F' :=
    hF'normH'.2 (h : G) h.2 ⁅rh, (h : G)⁻¹ * x * (h : G)⁆ hcommF'
  have hcomm_eq : (h : G) * ⁅rh, (h : G)⁻¹ * x * (h : G)⁆ * (h : G)⁻¹ =
      ⁅r, x⁆ := by
    dsimp [rh]
    rw [commutatorElement_def]
    group
  have hcommsF' : ⁅r, x⁆ ∈ F' := by
    simpa [hcomm_eq] using hcommconj
  have ht'x_comm : t' * x = x * t' :=
    Subgroup.mem_centralizer_iff.mp hxCt' t' (by simp)
  have hrtx : ⁅r, x⁆ = ⁅c.t, x⁆ := by
    dsimp [r]
    rw [commutatorElement_mul_left_eq_conj_mul c.t t' x]
    have ht'x1 : ⁅t', x⁆ = 1 := (commutatorElement_eq_one_iff_mul_comm).mpr ht'x_comm
    rw [ht'x1]
    simp
  have htx_eq : ⁅c.t, x⁆ = (x * x)⁻¹ := by
    rw [commutatorElement_def, hAinvt x hxA]
    group
  have htxA : ⁅c.t, x⁆ ∈ A := by
    rw [htx_eq]
    exact A.inv_mem (A.mul_mem hxA hxA)
  have htx_ne : ⁅c.t, x⁆ ≠ 1 := by
    intro h1
    have hxx1 : x * x = 1 := by
      have h' : (x * x)⁻¹ = 1 := by
        simpa [htx_eq] using h1
      exact inv_eq_one.mp h'
    have hx1 : (⟨x, hxA⟩ : ↥A) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hxx1
    have hxG : (x : G) = 1 :=
      congrArg Subtype.val (eq_one_of_sq_eq_one_of_coprime_two (G := ↥A) hAodd hx1)
    exact hxne (Subtype.ext hxG)
  have htxF' : ⁅c.t, x⁆ ∈ F' := by
    simpa [hrtx] using hcommsF'
  have htxF'_map : ∃ f : G, f ∈ c.FU ∧ e f = ⁅c.t, x⁆ := by
    exact Subgroup.mem_map.mp htxF'
  rcases htxF'_map with ⟨f, hfFU, hf_eq⟩
  have hord_f : orderOf f = orderOf ⁅c.t, x⁆ := by
    rw [← hf_eq]
    exact (orderOf_injective e.toMonoidHom e.injective f).symm
  have hFU_le_F : c.FU ≤ fittingSubgroupOf c.Hhat := by
    have hUeq : c.U = oddCoreOf c.Hhat := h26.1
    have hFUeq : c.FU = piCoreOf (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q} := by
      calc
        c.FU = fittingSubgroupOf c.U := rfl
        _ = fittingSubgroupOf (oddCoreOf c.Hhat) := by rw [hUeq]
        _ = piCoreOf (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q} :=
          fittingSubgroupOf_oddCore_eq_oddPart_fittingSubgroupOf c.Hhat
    rw [hFUeq]
    exact piCoreOf_le (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q}
  have hFU_pi : ∀ p : ℕ, p ∈ (Nat.card (↥c.FU)).primeFactors → p ∈ π := by
    intro p hp
    have hpF : p ∣ Nat.card (↥(fittingSubgroupOf c.Hhat)) :=
      (Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_dvd_of_le hFU_le_F)
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpF, Nat.card_pos.ne'⟩
  have hord_ne : orderOf ⁅c.t, x⁆ ≠ 1 := by
    intro h
    exact htx_ne (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hpprime, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (by exact hord_ne)
  have hpdvd_f : p ∣ orderOf f := by
    simpa [hord_f] using hpdvd
  have hpdvd_FU : p ∣ Nat.card (↥c.FU) := by
    let : Fintype (↥c.FU) := Fintype.ofFinite _
    have h := orderOf_dvd_card (x := (⟨f, hfFU⟩ : c.FU))
    exact hpdvd_f.trans (by simpa [Nat.card_eq_fintype_card, Subgroup.orderOf_mk] using h)
  have hpFU : p ∈ (Nat.card (↥c.FU)).primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨hpprime, hpdvd_FU, Nat.card_pos.ne'⟩
  have hpπ : p ∈ π := hFU_pi p hpFU
  have hpdvd_A : p ∣ Nat.card (↥A) := by
    let : Fintype (↥A) := Fintype.ofFinite _
    have h := orderOf_dvd_card (x := (⟨⁅c.t, x⁆, htxA⟩ : A))
    exact hpdvd.trans (by simpa [Nat.card_eq_fintype_card, Subgroup.orderOf_mk] using h)
  have hpA : p ∈ (Nat.card (↥A)).primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨hpprime, hpdvd_A, Nat.card_pos.ne'⟩
  have hpπ' : p ∈ πᶜ := by
    simpa [A] using piCoreOf_primeDivisors (fittingSubgroupOf M) πᶜ p hpA
  exact hpπ' hpπ

end CFSG.GorensteinWalter
