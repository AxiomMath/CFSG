
module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408SchreierBase

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Inputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census

attribute [local instance] wLeftAction

namespace UsigIdxAct

variable {N : ℕ} (A : UsigIdxAct N)

end UsigIdxAct

@[expose] def tauWord
    (i : ℕ) : Usig := CFSG.Perm.treeWord tauPar tauLab genUL i

theorem tauWord_zero :
    tauWord 0 = 1 := CFSG.Perm.treeWord_zero _ _ _

theorem genUL_inv
    {k : ℕ} (hk : k < 17) : (genUL k)⁻¹ = genU ⟨k, hk⟩ := by
  rw [genUL, dite_eq_left hk, inv_inv]

theorem tauWord_of_pos
    {i : ℕ} (h0 : 0 < i) (hi : i < 1408) :
    tauWord i = genUL (tauLab i) * tauWord (tauPar i) :=
  CFSG.Perm.treeWord_of_pos tauLab genUL h0 (tauPar_lt i h0 hi)

theorem tauWord_inv_of_pos
    {i : ℕ} (h0 : 0 < i) (hi : i < 1408) :
    (tauWord i)⁻¹ = (tauWord (tauPar i))⁻¹ * genU ⟨tauLab i, tauLab_lt i h0 hi⟩ := by
  rw [tauWord_of_pos h0 hi, mul_inv_rev, genUL_inv (tauLab_lt i h0 hi)]

theorem tauWord_smul
    {i : ℕ} (hi : i < 1408) : tauWord i • tauW = tauP i := by
  rw [← tauP_zero]
  exact CFSG.Perm.treeWord_smul tauPar_lt tauP_tree hi

theorem tauEdge_spec
    {i k : ℕ} (hi : i < 1408) (hk : k < 17) :
    tauEdge i k < 1408 ∧ tauP (tauEdge i k) = genUL k • tauP i := by
  rw [← tauCert_size] at hi ⊢
  obtain ⟨hj, e⟩ := natCertOK_edge tauCert_ok hi hk
  exact ⟨hj, by rw [tauP, e, genUL_act k hk _ (natCertOK_valid tauCert_ok hi)]⟩

@[expose] def schreierElt
    (i k : ℕ) : Usig := (tauWord i)⁻¹ * (genUL k)⁻¹ * tauWord (tauEdge i k)

theorem schreierElt_mem
    {i k : ℕ} (hi : i < 1408) (hk : k < 17) : schreierElt i k ∈ Atau := by
  rw [← stabilizer_tauW]
  obtain ⟨hj, e⟩ := tauEdge_spec hi hk
  have h : (schreierElt i k)⁻¹ ∈ MulAction.stabilizer Usig tauW := by
    rw [MulAction.mem_stabilizer_iff, schreierElt, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv,
      mul_smul, mul_smul, tauWord_smul hi, ← e, ← tauWord_smul hj, inv_smul_smul]
  simpa using (MulAction.stabilizer Usig tauW).inv_mem h

section Tree

variable {N : ℕ} {gen T I : Array (Array ℕ)}

variable (A : UsigIdxAct N)
  (hgen : ∀ k (hk : k < 17) (x : Fin N), (A.f (genU ⟨k, hk⟩) x : ℕ) = (gen[k]!)[(x : ℕ)]!)

include hgen in
theorem f_tauWord_inv (htree : treeOK gen T I N = true) :
    ∀ i < 1408, ∀ x : Fin N, (A.f (tauWord i)⁻¹ x : ℕ) = (T[i]!)[(x : ℕ)]! := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi x
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · rw [tauWord_zero, inv_one, A.one, treeOK_zero htree x.2]
    · have hp := tauPar_lt i h0 hi
      rw [tauWord_inv_of_pos h0 hi, A.mul, hgen, ih _ hp (hp.trans hi),
        (treeOK_spec htree hi x.2).2.2.2 h0]

include hgen in
theorem f_tauWord
    (htree : treeOK gen T I N = true) {i : ℕ} (hi : i < 1408) (y : Fin N) :
    (A.f (tauWord i) y : ℕ) = (I[i]!)[(y : ℕ)]! := by
  obtain ⟨-, hz, hTI, -⟩ := treeOK_spec htree hi y.2
  have e : A.f (tauWord i)⁻¹ ⟨_, hz⟩ = y :=
    Fin.ext (by rw [f_tauWord_inv A hgen htree i hi]; exact hTI)
  have e2 : A.f (tauWord i) y = ⟨_, hz⟩ := by
    conv_lhs => rw [← e]
    exact A.f_inv _ _
  rw [e2]

include hgen in
theorem f_schreierElt
    (htree : treeOK gen T I N = true) {i k : ℕ} (hi : i < 1408) (hk : k < 17)
    (x : Fin N) :
    (A.f (schreierElt i k) x : ℕ) = (I[tauEdge i k]!)[(gen[k]!)[(T[i]!)[(x : ℕ)]!]!]! := by
  rw [schreierElt, A.mul, A.mul, genUL_inv hk, f_tauWord A hgen htree (tauEdge_spec hi hk).1,
    hgen, f_tauWord_inv A hgen htree i hi]

include hgen in
theorem part_invariant
    (htree : treeOK gen T I N = true) {part : Array ℕ}
    (hs : schreierOK gen T I part N = true) :
    ∀ a ∈ Atau, ∀ x : Fin N, part[(A.f a x : ℕ)]! = part[(x : ℕ)]! := by
  simp only [schreierOK, List.all_eq_true, List.mem_range, beq_iff_eq] at hs
  have hK : ∀ i < 1408, ∀ s ∈ genUL '' {k | k < 17}, ∀ j < 1408, tauP j = s • tauP i →
      (tauWord j)⁻¹ * s * tauWord i ∈ A.partStab part := by
    rintro i hi _ ⟨k, hk, rfl⟩ j hj e
    obtain ⟨hj', e'⟩ := tauEdge_spec hi hk
    have hji : j = tauEdge i k := tauP_inj j hj _ hj' (e.trans e'.symm)
    subst hji
    have h : schreierElt i k ∈ A.partStab part := by
      intro x
      rw [f_schreierElt A hgen htree hi hk]
      exact hs i hi k hk x x.2
    have e2 : (tauWord (tauEdge i k))⁻¹ * genUL k * tauWord i = (schreierElt i k)⁻¹ := by
      rw [schreierElt, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, mul_assoc]
    rw [e2]
    exact (A.partStab part).inv_mem h
  have h := (CFSG.Perm.orbitTree_schreier (genUL '' {k | k < 17}) closure_genUL 1408
    (by norm_num) tauP tauP_inj tauP_closed tauPar tauLab genUL tauPar_lt tauP_tree
    (A.partStab part) hK).1
  rw [tauP_zero, stabilizer_tauW] at h
  exact fun a ha => h ha

include hgen in
theorem exists_Atau_of_cert
    (htree : treeOK gen T I N = true) {sel : Array (ℕ × ℕ)}
    (hsel : ∀ r < sel.size, sel[r]!.1 < 1408 ∧ sel[r]!.2 < 17) {root : ℕ} {c : NatCert}
    (hc : natCertOK (selAct gen T I sel) sel.size (fun x => decide (x < N)) root c = true)
    (hroot : root < N) :
    ∀ m < c.pts.size, ∃ a ∈ Atau, (A.f a ⟨root, hroot⟩ : ℕ) = c.pts[m]! := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · exact ⟨1, Atau.one_mem, by rw [A.one, natCertOK_root hc]⟩
    · obtain ⟨hp, hl, e⟩ := natCertOK_tree hc h0 hm
      obtain ⟨a, ha, hfa⟩ := ih _ hp (hp.trans hm)
      obtain ⟨hi, hk⟩ := hsel _ hl
      refine ⟨a * schreierElt sel[c.lab[m]!]!.1 sel[c.lab[m]!]!.2,
        Atau.mul_mem ha (schreierElt_mem hi hk), ?_⟩
      rw [A.mul, f_schreierElt A hgen htree hi hk, hfa, e]
      rfl

include hgen in
theorem idxOrbit_eq
    (htree : treeOK gen T I N = true) {part : Array ℕ}
    (hs : schreierOK gen T I part N = true) {sel : Array (ℕ × ℕ)}
    (hsel : ∀ r < sel.size, sel[r]!.1 < 1408 ∧ sel[r]!.2 < 17) {root₀ root₁ : ℕ}
    {c₀ c₁ : NatCert}
    (hc₀ : natCertOK (selAct gen T I sel) sel.size (fun x => decide (x < N)) root₀ c₀ = true)
    (hc₁ : natCertOK (selAct gen T I sel) sel.size (fun x => decide (x < N)) root₁ c₁ = true)
    (hcov : ∀ y < N, (part[y]! = 0 ∧ c₀.pts.contains y = true) ∨
      (part[y]! = 1 ∧ c₁.pts.contains y = true)) (x : Fin N) :
    {y | ∃ a ∈ Atau, A.f a x = y} = {y : Fin N | part[(y : ℕ)]! = part[(x : ℕ)]!} := by
  have hr₀ : root₀ < N := by
    have := natCertOK_valid hc₀ (natCertOK_pos hc₀)
    rwa [natCertOK_root hc₀, decide_eq_true_eq] at this
  have hr₁ : root₁ < N := by
    have := natCertOK_valid hc₁ (natCertOK_pos hc₁)
    rwa [natCertOK_root hc₁, decide_eq_true_eq] at this
  have reach : ∀ z : Fin N, (part[(z : ℕ)]! = 0 ∧ ∃ a ∈ Atau, A.f a ⟨root₀, hr₀⟩ = z) ∨
      (part[(z : ℕ)]! = 1 ∧ ∃ a ∈ Atau, A.f a ⟨root₁, hr₁⟩ = z) := by
    intro z
    rcases hcov z z.2 with ⟨hz, hm⟩ | ⟨hz, hm⟩
    · obtain ⟨m, hm', e⟩ := Array.mem_iff_getElem.1 (Array.contains_iff_mem.1 hm)
      obtain ⟨a, ha, hfa⟩ := exists_Atau_of_cert A hgen htree hsel hc₀ hr₀ m hm'
      refine .inl ⟨hz, a, ha, Fin.ext ?_⟩
      rw [hfa, getElem!_pos c₀.pts m hm', e]
    · obtain ⟨m, hm', e⟩ := Array.mem_iff_getElem.1 (Array.contains_iff_mem.1 hm)
      obtain ⟨a, ha, hfa⟩ := exists_Atau_of_cert A hgen htree hsel hc₁ hr₁ m hm'
      refine .inr ⟨hz, a, ha, Fin.ext ?_⟩
      rw [hfa, getElem!_pos c₁.pts m hm', e]
  have hinv := part_invariant A hgen htree hs
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact hinv a ha x
  · intro hy
    have key : ∀ (r : Fin N) (a b : Usig), a ∈ Atau → b ∈ Atau → A.f a r = x → A.f b r = y →
        ∃ g ∈ Atau, A.f g x = y := by
      intro r a b ha hb hax hby
      refine ⟨a⁻¹ * b, Atau.mul_mem (Atau.inv_mem ha) hb, ?_⟩
      rw [A.mul, ← hax, A.inv_f, hby]
    rcases reach x with ⟨hx, a, ha, hax⟩ | ⟨hx, a, ha, hax⟩ <;>
      rcases reach y with ⟨hy', b, hb, hby⟩ | ⟨hy', b, hb, hby⟩
    · exact key _ a b ha hb hax hby
    · exact absurd (hy.symm.trans hy') (by rw [hx]; decide)
    · exact absurd (hy.symm.trans hy') (by rw [hx]; decide)
    · exact key _ a b ha hb hax hby

end Tree

end CFSG.Monster.B.TwoA.Unitary
