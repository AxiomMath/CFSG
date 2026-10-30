module

public import CFSG.Permutation.FiveTransitive.OddFourCentralizer

public section

namespace CFSG

namespace FiveTransitive.Research.OddFourInvolutionGeometry

open MulAction
open Research.SharpFourDegreeCompletion
open Research.OddFourCentralizer

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem involution_fixedBy_ncard_le_three
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (g : G) (hgTwo : g ^ 2 = 1) (hgNe : g ≠ 1) :
    (MulAction.fixedBy X g).ncard ≤ 3 := by
  classical
  by_contra hnot
  have hfour : 4 ≤ (MulAction.fixedBy X g).ncard := by omega
  letI : Fintype (MulAction.fixedBy X g) := Fintype.ofFinite _
  let f : Fin 4 ↪ MulAction.fixedBy X g := Classical.choice
    (Function.Embedding.nonempty_iff_card_le.mpr (by
      simpa using hfour))
  let ef : Fin 4 ↪ X := f.trans (Function.Embedding.subtype _)
  obtain ⟨q, hq⟩ :=
    Research.SharpFourBound.exists_maps_embedding h4 e ef
  let x : G := q⁻¹ * g * q
  have hxTwo : x ^ 2 = 1 := by
    calc
      x ^ 2 = q⁻¹ * (g ^ 2) * q := by
        dsimp only [x]
        rw [pow_two, pow_two]
        group
      _ = 1 := by rw [hgTwo]; simp
  have hxNe : x ≠ 1 := by
    intro hx
    apply hgNe
    have : q * x * q⁻¹ = g := by
      dsimp only [x]
      group
    rw [hx] at this
    simpa using this.symm
  have hxfix : ∀ i, x • e i = e i := by
    intro i
    calc
      x • e i = q⁻¹ • (g • (q • e i)) := by
        simp only [x, mul_smul]
      _ = q⁻¹ • (g • (ef i : X)) := by rw [hq]
      _ = q⁻¹ • (ef i : X) := by
        congr 1
        exact (f i).property
      _ = q⁻¹ • (q • e i) := by rw [hq]
      _ = e i := inv_smul_smul q _
  have hxmem : x ∈ MulAction.stabilizer G e := by
    rw [MulAction.mem_stabilizer_iff]
    apply Function.Embedding.ext
    exact hxfix
  have hxOrder : orderOf x = 2 := orderOf_eq_prime hxTwo hxNe
  have hdvd := (MulAction.stabilizer G e).orderOf_dvd_natCard hxmem
  rw [hxOrder] at hdvd
  exact hodd.not_two_dvd_nat hdvd

private theorem exists_two_disjoint_involution_pairs_of_fixed_le_three
    (hX : 8 ≤ Fintype.card X)
    (g : G) (hgTwo : g ^ 2 = 1)
    (hfixed : (MulAction.fixedBy X g).ncard ≤ 3) :
    ∃ x z : X,
      g • x ≠ x ∧ g • z ≠ z ∧
      z ≠ x ∧ z ≠ g • x ∧ g • z ≠ x ∧ g • z ≠ g • x := by
  classical
  let M : Set X := (MulAction.fixedBy X g)ᶜ
  have hsum := Set.ncard_add_ncard_compl (MulAction.fixedBy X g)
  rw [Nat.card_eq_fintype_card] at hsum
  have hMcard : 5 ≤ M.ncard := by
    dsimp only [M]
    omega
  have hMnonempty : M.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨x, hxM⟩ := hMnonempty
  have hx : g • x ≠ x := by simpa [M] using hxM
  have hinvol : ∀ y : X, g • (g • y) = y := by
    intro y
    rw [← mul_smul, ← pow_two, hgTwo, one_smul]
  have hzExists : ∃ z ∈ M, z ≠ x ∧ z ≠ g • x := by
    by_contra hnone
    push Not at hnone
    have hsub : M ⊆ ({x, g • x} : Set X) := by
      intro y hy
      by_cases hyx : y = x
      · simp [hyx]
      · right
        exact hnone y hy hyx
    have hle := Set.ncard_le_ncard hsub
    have hpair : ({x, g • x} : Set X).ncard = 2 := by
      simp [Ne.symm hx]
    rw [hpair] at hle
    omega
  obtain ⟨z, hzM, hzx, hzgx⟩ := hzExists
  have hz : g • z ≠ z := by simpa [M] using hzM
  have hgzx : g • z ≠ x := by
    intro heq
    have hzx' : z = g • x := by
      calc
        z = g • (g • z) := (hinvol z).symm
        _ = g • x := congrArg (fun y : X => g • y) heq
    exact hzgx hzx'
  have hgzgx : g • z ≠ g • x := by
    intro heq
    exact hzx ((MulAction.injective g) heq)
  exact ⟨x, z, hx, hz, hzx, hzgx, hgzx, hgzgx⟩

theorem involution_conjugate_doubleSwapLift
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (hlocal : SameBaseInvolutionConjugacy (G := G) e)
    (g d : G)
    (hgTwo : g ^ 2 = 1) (hdTwo : d ^ 2 = 1)
    (hgNe : g ≠ 1)
    (hdbase : ∀ i,
      d • e i = e (Research.SharpFourBound.baseDoubleSwap i)) :
    ∃ q : G, q * g * q⁻¹ = d := by
  classical
  have hfixed := involution_fixedBy_ncard_le_three
    h4 e hodd g hgTwo hgNe
  obtain ⟨x, z, hx, hz, hzx, hzgx, hgzx, hgzgx⟩ :=
    exists_two_disjoint_involution_pairs_of_fixed_le_three
      hX g hgTwo hfixed
  have hinvol : ∀ y : X, g • (g • y) = y := by
    intro y
    rw [← mul_smul, ← pow_two, hgTwo, one_smul]
  let f : Fin 4 → X := ![x, g • x, z, g • z]
  have hf : Function.Injective f := by
    have hx' : x ≠ g • x := hx.symm
    have hz' : z ≠ g • z := hz.symm
    have hxz : x ≠ z := hzx.symm
    have hxgz : x ≠ g • z := hgzx.symm
    have hgxz : g • x ≠ z := hzgx.symm
    have hgxgz : g • x ≠ g • z := hgzgx.symm
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all [f]
  let ef : Fin 4 ↪ X := ⟨f, hf⟩
  obtain ⟨q, hq⟩ :=
    Research.SharpFourBound.exists_maps_embedding h4 ef e
  have hqinv : ∀ i : Fin 4, q⁻¹ • e i = ef i := by
    intro i
    rw [← hq]
    simp
  have hq0 : q • x = e 0 := by simpa [ef, f] using hq 0
  have hq1 : q • (g • x) = e 1 := by simpa [ef, f] using hq 1
  have hq2 : q • z = e 2 := by simpa [ef, f] using hq 2
  have hq3 : q • (g • z) = e 3 := by simpa [ef, f] using hq 3
  let w : G := q * g * q⁻¹
  have hwTwo : w ^ 2 = 1 := by
    calc
      w ^ 2 = q * (g ^ 2) * q⁻¹ := by
        dsimp only [w]
        rw [pow_two, pow_two]
        group
      _ = 1 := by rw [hgTwo]; simp
  have hwSame : ∀ i, w • e i = d • e i := by
    intro i
    rw [hdbase]
    dsimp only [w]
    rw [mul_smul, mul_smul, hqinv]
    fin_cases i
    · change q • (g • x) =
        e (Research.SharpFourBound.baseDoubleSwap 0)
      rw [hq1, show Research.SharpFourBound.baseDoubleSwap 0 = 1 by decide]
    · change q • (g • (g • x)) =
        e (Research.SharpFourBound.baseDoubleSwap 1)
      rw [hinvol, hq0,
        show Research.SharpFourBound.baseDoubleSwap 1 = 0 by decide]
    · change q • (g • z) =
        e (Research.SharpFourBound.baseDoubleSwap 2)
      rw [hq3, show Research.SharpFourBound.baseDoubleSwap 2 = 3 by decide]
    · change q • (g • (g • z)) =
        e (Research.SharpFourBound.baseDoubleSwap 3)
      rw [hinvol, hq2,
        show Research.SharpFourBound.baseDoubleSwap 3 = 2 by decide]
  obtain ⟨h, _, hhw⟩ := hlocal w d hwTwo hdTwo hwSame
  refine ⟨h * q, ?_⟩
  calc
    (h * q) * g * (h * q)⁻¹ = h * w * h⁻¹ := by
      dsimp only [w]
      group
    _ = d := hhw

theorem single_double_centralizer_equation
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (hlocal : SameBaseInvolutionConjugacy (G := G) e)
    (s d : G)
    (hsTwo : s ^ 2 = 1) (hdTwo : d ^ 2 = 1)
    (hsNe : s ≠ 1)
    (hsbase : ∀ i,
      s • e i = e (Research.SharpFourBound.baseSingleSwap i))
    (hdbase : ∀ i,
      d • e i = e (Research.SharpFourBound.baseDoubleSwap i)) :
    ((MulAction.fixedBy X s).ncard.descFactorial 2 *
        (Fintype.card X - (MulAction.fixedBy X s).ncard)) *
        Nat.card (centralizingBaseStabilizer e s) =
      ((Fintype.card X - (MulAction.fixedBy X s).ncard) *
        (Fintype.card X - (MulAction.fixedBy X s).ncard - 2)) *
        Nat.card (centralizingBaseStabilizer e d) := by
  have hcorrectS := centralizerCorrection_of_sameBaseInvolutionConjugacy
    h4 e s Research.SharpFourBound.baseSingleSwap hsTwo hsbase hlocal
  have hcorrectD := centralizerCorrection_of_sameBaseInvolutionConjugacy
    h4 e d Research.SharpFourBound.baseDoubleSwap hdTwo hdbase hlocal
  obtain ⟨q, hq⟩ := involution_conjugate_doubleSwapLift
    h4 hX e hodd hlocal s d hsTwo hdTwo hsNe hdbase
  have hfix : (MulAction.fixedBy X s).ncard =
      (MulAction.fixedBy X d).ncard :=
    fixedBy_ncard_eq_of_conjugate s d q hq
  calc
    ((MulAction.fixedBy X s).ncard.descFactorial 2 *
        (Fintype.card X - (MulAction.fixedBy X s).ncard)) *
        Nat.card (centralizingBaseStabilizer e s) =
        Nat.card (Subgroup.centralizer ({s} : Set G)) :=
      (singleSwap_centralizer_card e s hsTwo hsbase hcorrectS).symm
    _ = Nat.card (Subgroup.centralizer ({d} : Set G)) :=
      centralizer_ncard_eq_of_conjugate s d q hq
    _ = ((Fintype.card X - (MulAction.fixedBy X d).ncard) *
        (Fintype.card X - (MulAction.fixedBy X d).ncard - 2)) *
        Nat.card (centralizingBaseStabilizer e d) :=
      doubleSwap_centralizer_card e d hdTwo hdbase hcorrectD
    _ = ((Fintype.card X - (MulAction.fixedBy X s).ncard) *
        (Fintype.card X - (MulAction.fixedBy X s).ncard - 2)) *
        Nat.card (centralizingBaseStabilizer e d) := by rw [hfix]

end FiveTransitive.Research.OddFourInvolutionGeometry

end CFSG
