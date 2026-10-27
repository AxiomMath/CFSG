module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrameLemmas
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdx

public section

namespace CFSG.HardMathSupport.C14Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.C14Idx



theorem mem_familyGroup_iff
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {ι : Type} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5) [Finite ι]
    (a : ι → Fin τ.rank → Lˣ) (ha : ∀ i j, a i j ^ p = 1) {y : ModGL τ L}
    (hy : y ∈ adjointGroup τ L) :
    y ∈ familyGroup a ↔ ∀ i, rootDiagUnit τ (a i) * y * (rootDiagUnit τ (a i))⁻¹ = y := by
  constructor
  · intro hyM
    exact (mem_familyCentralizer.1 (familyGroup_le_familyCentralizer (K := L) a hyM)).2
  · intro hcomm
    have hc : y ∈ familyCentralizer τ L a := mem_familyCentralizer.2 ⟨hy, hcomm⟩
    rwa [CFSG.HardMathSupport.C14Lattice.familyCentralizer_eq_familyGroup_of_nonTorsion
      hp hp2 h3 h5 a ha] at hc

theorem famZ_le_diagKer
                                      {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type} (a : ι → Fin τ.rank → Lˣ) :
    famZ a ≤ diagKer τ L (familyKernel a) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨lam, c, hlam, rfl⟩
  refine ⟨cochar lam c, rfl, fun α hα => ?_⟩
  have hsum : (∑ i, lam i * α i) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => mul_comm (lam i) (α i)), hlam α hα]
  calc FourGroupChevalley.rootChar (cochar lam c) α
      = ∏ i, (c ^ lam i) ^ α i := rfl
    _ = ∏ i, c ^ (lam i * α i) :=
        Finset.prod_congr rfl fun i _ => (zpow_mul c (lam i) (α i)).symm
    _ = c ^ (∑ i, lam i * α i) :=
        CFSG.LieType.Chevalley.prod_zpow_eq_zpow_sum Finset.univ (fun i => lam i * α i) c
    _ = 1 := by rw [hsum, zpow_zero]

theorem frobTwistGL_mem_adjointGroup
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {e : ℕ} {Q' : ModGL τ L}
    (hQτ : Q' ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q' = (h ▸ diagramMap t L ^ j) * n)
    {g : ModGL τ L} (hg : g ∈ adjointGroup τ L) :
    frobTwistGL τ L 2 e Q' g ∈ adjointGroup τ L := by
  rcases hQτ with hQ | ⟨t, j, htag, n, hn, hQeq⟩
  · rw [frobTwistGL_apply]
    exact (adjointGroup τ L).mul_mem
      ((adjointGroup τ L).mul_mem hQ (entrywiseFrobGL_mem 2 e hg))
      ((adjointGroup τ L).inv_mem hQ)
  · rw [hQeq]
    cases htag
    rw [frobTwistGL_apply]
    have hmid : n * entrywiseFrobGL t.tag L 2 e g * n⁻¹ ∈ adjointGroup t.tag L :=
      (adjointGroup t.tag L).mul_mem
        ((adjointGroup t.tag L).mul_mem hn (entrywiseFrobGL_mem 2 e hg))
        ((adjointGroup t.tag L).inv_mem hn)
    have hconj := conj_mem_adjointGroup_of_map_eq
      (Q := diagramMap t L ^ j) (map_conj_diagramMap_zpow (L := L) (t := t) (j := j))
      (n * entrywiseFrobGL t.tag L 2 e g * n⁻¹) hmid
    have hEq : (diagramMap t L ^ j * n) * entrywiseFrobGL t.tag L 2 e g *
          (diagramMap t L ^ j * n)⁻¹ =
        diagramMap t L ^ j * (n * entrywiseFrobGL t.tag L 2 e g * n⁻¹) *
          (diagramMap t L ^ j)⁻¹ := by
      group
    rwa [hEq]

@[expose] noncomputable def frameEndo
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (e : ℕ) {Q' : ModGL τ L}
    (hQτ : Q' ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q' = (h ▸ diagramMap t L ^ j) * n) :
    adjointGroup τ L →* adjointGroup τ L :=
  MonoidHom.codRestrict ((frobTwistGL τ L 2 e Q').comp (adjointGroup τ L).subtype) (adjointGroup τ L)
    fun g => frobTwistGL_mem_adjointGroup hQτ g.2

theorem frameEndo_apply
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (e : ℕ) {Q' : ModGL τ L}
    (hQτ : Q' ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q' = (h ▸ diagramMap t L ^ j) * n)
    (g : adjointGroup τ L) :
    ((frameEndo e hQτ g : adjointGroup τ L) : ModGL τ L) = frobTwistGL τ L 2 e Q' g :=
  rfl

theorem frobTwistGL_mem_familyGroup
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {ι : Type} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5) [Finite ι]
    (a : ι → Fin τ.rank → Lˣ) (ha : ∀ i j, a i j ^ p = 1) {e : ℕ} {Q' : ModGL τ L}
    (hQτ : Q' ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q' = (h ▸ diagramMap t L ^ j) * n)
    (hfix : ∀ i, frobTwistGL τ L 2 e Q' (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i))
    {g : ModGL τ L} (hg : g ∈ adjointGroup τ L ⊓ familyGroup a) :
    frobTwistGL τ L 2 e Q' g ∈ adjointGroup τ L ⊓ familyGroup a := by
  rw [Subgroup.mem_inf] at hg ⊢
  obtain ⟨hgG, hgM⟩ := hg
  have hFG : frobTwistGL τ L 2 e Q' g ∈ adjointGroup τ L :=
    frobTwistGL_mem_adjointGroup hQτ hgG
  refine ⟨hFG, ?_⟩
  rw [mem_familyGroup_iff hp hp2 h3 h5 a ha hFG]
  intro i
  have hcomm : rootDiagUnit τ (a i) * g * (rootDiagUnit τ (a i))⁻¹ = g :=
    (mem_familyGroup_iff hp hp2 h3 h5 a ha hgG).1 hgM i
  have h := congrArg (frobTwistGL τ L 2 e Q') hcomm
  rw [map_mul, map_mul, map_inv, hfix i] at h
  exact h

private theorem eZ4_sum_mul_transpose
                                      {τ : Tag} (B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (α lam : Fin τ.rank → ℤ) :
    ∑ i, α i * Matrix.mulVec (Matrix.transpose B) lam i
      = ∑ j, Matrix.mulVec B α j * lam j := by
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem frobTwistGL_mem_famZ
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {ι : Type} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ι → Fin τ.rank → Lˣ)
    (ha : ∀ i j, a i j ^ p = 1) {e : ℕ} {Q' : ModGL τ L}
    (hQT : ∀ t, ∃ t', Q' * rootDiagUnit τ t * Q'⁻¹ = rootDiagUnit τ t')
    (hfix : ∀ i, frobTwistGL τ L 2 e Q' (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i))
    {g : ModGL τ L} (hg : g ∈ famZ a) : frobTwistGL τ L 2 e Q' g ∈ famZ a := by
  classical
  obtain ⟨A, hA, hAroot, N, hN0, hAN⟩ := CFSG.HardMathSupport.C14W1.exists_lattice_map Q' hQT
  set q : ℕ := 2 ^ e with hq
  set B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ := (q : ℤ) • A with hB
  have hFr : ∀ t : Fin τ.rank → Lˣ,
      (fun i => Units.map (iterateFrobenius L 2 e).toMonoidHom (t i)) = t ^ q := by
    intro t; funext i; apply Units.ext; simp [iterateFrobenius_def, q]
  have hFd : ∀ t, frobTwistGL τ L 2 e Q' (rootDiagUnit τ t) =
      rootDiagUnit τ (C14Torus.tmap B t) := by
    intro t
    rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_eq_map, hFr, hA]
    congr 1
    rw [← zpow_natCast, ← C14Torus.tmap_smul_one, C14Torus.tmap_tmap, smul_mul_assoc, one_mul]
  have hinj := CFSG.HardMathSupport.C14W1.rootDiagUnit_injective' (τ := τ) (K := L)
  have hBfix : ∀ i, C14Torus.tmap B (a i) = a i := fun i => hinj (by rw [← hFd]; exact hfix i)
  have hap : ∀ i, a i ^ p = 1 := fun i => funext fun j => ha i j
  have hcopq : Nat.Coprime q p :=
    Nat.Coprime.pow_left e ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hAΨ : ∀ α ∈ familyKernel a, Matrix.mulVec A α ∈ familyKernel a := by
    rintro α ⟨hα, hαa⟩
    refine ⟨hAroot α hα, fun i => ?_⟩
    have h1 : rootChar (a i) (Matrix.mulVec A α) ^ q = 1 := by
      have := congrArg (fun t => rootChar t α) (hBfix i)
      rw [C14Torus.rootChar_tmap, hαa i, hB, Matrix.smul_mulVec,
        C14Torus.rootChar_zsmul, zpow_natCast] at this
      exact this
    have h2 : rootChar (a i) (Matrix.mulVec A α) ^ p = 1 := by
      rw [← C14Torus.rootChar_pow_left, hap i, C14Torus.rootChar_one_left]
    have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rwa [hcopq, pow_one] at h3
  have htmap : ∀ (lam : Fin τ.rank → ℤ) (c : Lˣ),
      C14Torus.tmap B (cochar lam c) = cochar (Matrix.mulVec (Matrix.transpose B) lam) c := by
    intro lam c
    funext i
    change rootChar (cochar lam c) (fun j => B j i)
      = c ^ Matrix.mulVec (Matrix.transpose B) lam i
    rw [rootChar]
    trans ∏ j, c ^ (lam j * B j i)
    · exact Finset.prod_congr rfl fun j _ => by rw [cochar, ← zpow_mul]
    · rw [Finset.prod_zpow_eq_zpow_sum]
      congr 1
      simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine Subgroup.closure_induction (p := fun g _ => frobTwistGL τ L 2 e Q' g ∈ famZ a)
    ?_ ?_ ?_ ?_ hg
  · rintro g ⟨lam, c, hlam, rfl⟩
    have horth : ∀ α ∈ familyKernel a,
        ∑ i, α i * Matrix.mulVec (Matrix.transpose B) lam i = 0 := by
      intro α hα
      have hAα : Matrix.mulVec A α ∈ familyKernel a := hAΨ α hα
      have h0 : ∑ j, Matrix.mulVec A α j * lam j = 0 := hlam (Matrix.mulVec A α) hAα
      rw [eZ4_sum_mul_transpose B α lam, hB, Matrix.smul_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul]
      have hf : (∑ j, ((q : ℤ) * Matrix.mulVec A α j) * lam j)
          = (q : ℤ) * ∑ j, Matrix.mulVec A α j * lam j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hf, h0, mul_zero]
    rw [hFd (cochar lam c), htmap lam c]
    exact Subgroup.subset_closure ⟨Matrix.mulVec (Matrix.transpose B) lam, c, horth, rfl⟩
  · rw [map_one]; exact one_mem _
  · intro x y hx hy hpx hpy
    rw [map_mul]; exact mul_mem hpx hpy
  · intro x hx hpx
    rw [map_inv]; exact inv_mem hpx

theorem commutator_stable
                                      {Γ : Type*} [Group Γ] (F : Γ →* Γ) (M : Subgroup Γ)
    (hM : ∀ g ∈ M, F g ∈ M) : ∀ g ∈ ⁅M, M⁆, F g ∈ ⁅M, M⁆ := by
  intro g hg
  have hmapM : M.map F ≤ M := by
    rintro x ⟨y, hy, rfl⟩
    exact hM y hy
  have hle : (⁅M, M⁆).map F ≤ ⁅M, M⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmapM hmapM
  exact hle ⟨g, hg, rfl⟩

end CFSG.HardMathSupport.C14Exc
