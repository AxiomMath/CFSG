module

public import CFSG.LocalAnalysis.StandardType.GGK0NormalForm
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcoveClasses

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

namespace K0Normal

variable {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)

private theorem rootChar_zsmul_aux {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (k : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar a (k • v) = rootChar a v ^ k := by
  simp only [rootChar, Pi.smul_apply, smul_eq_mul, ← Finset.prod_zpow, ← zpow_mul]
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

private theorem p_odd_aux (A : K0LangMark Omega lab p R I phi) (hp : 0 < p) : Odd p := by
  rcases Nat.even_or_odd p with heven | hodd
  · exfalso
    obtain ⟨m, hm⟩ := heven
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · rw [hm] at hp; simp at hp
      · exact h
    let u : Omegaˣ := A.zeta ^ m
    have hu2 : u ^ 2 = 1 := by
      dsimp [u]
      rw [← pow_mul, show m * 2 = p by omega]
      have h : A.zeta ^ orderOf A.zeta = 1 := pow_orderOf_eq_one A.zeta
      rwa [A.zeta_order] at h
    have hu1 : u = 1 := by
      apply Units.ext
      have hu2' : ((u : Omega)) ^ 2 = 1 := by
        have := congrArg (fun x : Omegaˣ => (x : Omega)) hu2
        simpa [Units.val_pow_eq_pow_val] using this
      have hsq : ((u : Omega) - 1) ^ 2 = 0 := by
        have h := sub_pow_char (u : Omega) (1 : Omega) (p := 2)
        rw [h, hu2']
        norm_num
      have h : (u : Omega) - 1 = 0 := sq_eq_zero_iff.mp hsq
      exact sub_eq_zero.mp h
    have hdvd : p ∣ m := by
      dsimp [u] at hu1
      rw [← A.zeta_order, orderOf_dvd_iff_pow_eq_one]
      exact hu1
    have : p ≤ m := Nat.le_of_dvd hm_pos hdvd
    omega
  · exact hodd

private theorem hcop_aux (A : K0LangMark Omega lab p R I phi) (hp : 0 < p) :
    Nat.Coprime p A.setup.D.q := by
  rw [A.q_eq]
  exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (p_odd_aux A hp))

include N in
theorem s_nodePerm_eq_zero_iff (i : Fin A.row.diagram.marks.length) :
    A.row.s.getD (A.row.nodePerm i).val 0 = 0 ↔ A.row.s.getD i.val 0 = 0 := by
  let s_i : ℕ := A.row.s.getD i.val 0
  let s_pi : ℕ := A.row.s.getD (A.row.nodePerm i).val 0
  let q : ℕ := A.setup.D.q
  let ε : ℤ := A.epsilon
  change s_pi = 0 ↔ s_i = 0
  let γ_i : Fin A.tau.rank → ℤ := A.nodeMap (Pi.single i 1)
  let γ_pi : Fin A.tau.rank → ℤ := A.nodeMap (Pi.single (A.row.nodePerm i) 1)
  have hγ_i : IsRoot A.tau γ_i := A.node_isRoot i
  have hρ : A.setup.ρ γ_i = A.epsilon • γ_pi := by
    rw [← A.frob_roots γ_i hγ_i]
    exact A.frob_nodes i
  have hchar := A.setup.frob.rootChar_eq A.a A.a_torus γ_i hγ_i
  rw [hρ, rootChar_zsmul_aux] at hchar
  rw [A.node_eval i, A.node_eval (A.row.nodePerm i)] at hchar
  have hchar_int : A.zeta ^ ((s_pi : ℤ) * ε) = A.zeta ^ ((s_i : ℤ) * q) := by
    dsimp only [s_i, s_pi, q, ε]
    simpa [zpow_natCast, zpow_mul] using hchar
  have hdvd : (p : ℤ) ∣ (s_i : ℤ) * q - (s_pi : ℤ) * ε := by
    have hz : A.zeta ^ ((s_i : ℤ) * q - (s_pi : ℤ) * ε) = 1 := by
      rw [zpow_sub, hchar_int, mul_inv_cancel]
    have hdvd_order : (orderOf A.zeta : ℤ) ∣ (s_i : ℤ) * q - (s_pi : ℤ) * ε :=
      (orderOf_dvd_iff_zpow_eq_one).mpr hz
    have h_eq : (orderOf A.zeta : ℤ) = (p : ℤ) := by exact_mod_cast A.zeta_order
    rwa [h_eq] at hdvd_order
  have hcop : Nat.Coprime p q := by
    dsimp only [q]
    exact hcop_aux A N.zero_lt
  have hs_i_lt : (s_i : ℤ) < p := by
    dsimp only [s_i]
    exact_mod_cast N.s_lt i.val
  have hs_pi_lt : (s_pi : ℤ) < p := by
    dsimp only [s_pi]
    exact_mod_cast N.s_lt (A.row.nodePerm i).val
  constructor
  · intro h
    have h' : (s_pi : ℤ) = 0 := by exact_mod_cast h
    have hdvd' : (p : ℤ) ∣ (s_i : ℤ) * q := by
      simpa only [h', zero_mul, sub_zero] using hdvd
    have hdvd'' : p ∣ s_i * q := by
      rw [← Int.natCast_dvd_natCast]
      exact hdvd'
    have h' : p ∣ q * s_i := by
      rwa [Nat.mul_comm]
    have hdvd''' : p ∣ s_i := hcop.dvd_of_dvd_mul_left h'
    have hzero : (s_i : ℤ) = 0 :=
      Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.natCast_dvd_natCast.mpr hdvd''')
        (by simpa using hs_i_lt)
    exact Nat.cast_eq_zero.mp hzero
  · intro h
    have h' : (s_i : ℤ) = 0 := by exact_mod_cast h
    have hdvd' : (p : ℤ) ∣ - ((s_pi : ℤ) * ε) := by
      simpa only [h', zero_mul, zero_sub] using hdvd
    have hdvd'' : (p : ℤ) ∣ (s_pi : ℤ) * ε := by
      exact dvd_neg.mp hdvd'
    have hε : ε = 1 ∨ ε = -1 := by
      dsimp only [ε]
      rw [A.epsilon_eq]
      split_ifs <;> simp
    rcases hε with h1 | h1
    · have hdvd''' : (p : ℤ) ∣ (s_pi : ℤ) := by
        simpa [h1] using hdvd''
      have hdvd4 : p ∣ s_pi := by
        rw [← Int.natCast_dvd_natCast]
        exact hdvd'''
      have hzero : (s_pi : ℤ) = 0 :=
        Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.natCast_dvd_natCast.mpr hdvd4)
          (by simpa using hs_pi_lt)
      exact Nat.cast_eq_zero.mp hzero
    · have hdvd''' : (p : ℤ) ∣ (s_pi : ℤ) := by
        have h2 : (p : ℤ) ∣ - (s_pi : ℤ) := by
          simpa [h1] using hdvd''
        exact dvd_neg.mp h2
      have hdvd4 : p ∣ s_pi := by
        rw [← Int.natCast_dvd_natCast]
        exact hdvd'''
      have hzero : (s_pi : ℤ) = 0 :=
        Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.natCast_dvd_natCast.mpr hdvd4)
          (by simpa using hs_pi_lt)
      exact Nat.cast_eq_zero.mp hzero

omit [CharP Omega 2] in
include N in
theorem adj_nodePerm (i j : Fin A.row.diagram.marks.length) :
    0 < A.row.diagram.adj (A.row.nodePerm i).val (A.row.nodePerm j).val ↔
      0 < A.row.diagram.adj i.val j.val := by
  have hi : (A.row.nodePerm i).val < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact (A.row.nodePerm i).isLt
  have hj : (A.row.nodePerm j).val < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact (A.row.nodePerm j).isLt
  have hi' : i.val < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact i.isLt
  have hj' : j.val < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact j.isLt
  rw [← N.adj_iff (A.row.nodePerm i).val (A.row.nodePerm j).val hi hj]
  rw [← N.adj_iff i.val j.val hi' hj']
  unfold KacData.Adj
  have hγi : IsRoot A.tau (A.nodeMap (Pi.single i 1)) := A.node_isRoot i
  have hγj : IsRoot A.tau (A.nodeMap (Pi.single j 1)) := A.node_isRoot j
  have hρi : A.setup.ρ (A.nodeMap (Pi.single i 1)) =
      A.epsilon • A.nodeMap (Pi.single (A.row.nodePerm i) 1) := by
    rw [← A.frob_roots _ hγi]; exact A.frob_nodes i
  have hρj : A.setup.ρ (A.nodeMap (Pi.single j 1)) =
      A.epsilon • A.nodeMap (Pi.single (A.row.nodePerm j) 1) := by
    rw [← A.frob_roots _ hγj]; exact A.frob_nodes j
  have hiform : CFSG.LieType.Steinberg.Adjoint.iform
      (A.nodeMap (Pi.single (A.row.nodePerm i) 1))
      (A.nodeMap (Pi.single (A.row.nodePerm j) 1)) =
      CFSG.LieType.Steinberg.Adjoint.iform (A.nodeMap (Pi.single i 1))
        (A.nodeMap (Pi.single j 1)) := by
    have h := A.setup.frob.iform_eq (A.nodeMap (Pi.single i 1)) (A.nodeMap (Pi.single j 1))
    rw [hρi, hρj] at h
    rw [CFSG.LieType.Steinberg.Adjoint.iform_smul_left,
      CFSG.LieType.Steinberg.Adjoint.iform_smul_right] at h
    have hε2 : A.epsilon * A.epsilon = 1 := by
      rw [A.epsilon_eq]; split_ifs <;> norm_num
    rw [← mul_assoc, hε2, one_mul] at h
    exact h
  have h_inj : ∀ a b : ℕ, a < A.tau.rank + 1 → b < A.tau.rank + 1 →
      idxNode (r := A.tau.rank) a = idxNode (r := A.tau.rank) b → a = b := by
    intro a b ha hb h
    have := congrArg (nodeIdx (r := A.tau.rank)) h
    rwa [nodeIdx_idxNode ha, nodeIdx_idxNode hb] at this
  rw [← N.nodeMap_eq i, ← N.nodeMap_eq j, ← N.nodeMap_eq (A.row.nodePerm i),
    ← N.nodeMap_eq (A.row.nodePerm j)]
  rw [hiform]
  constructor
  · rintro ⟨hne, hif⟩
    refine ⟨?_, hif⟩
    intro h_eq
    apply hne
    have h_eq' : i.val = j.val := h_inj i.val j.val hi' hj' h_eq
    have h_eq'' : i = j := Fin.ext h_eq'
    rw [h_eq'']
  · rintro ⟨hne, hif⟩
    refine ⟨?_, hif⟩
    intro h_eq
    apply hne
    have h_eq' : (A.row.nodePerm i).val = (A.row.nodePerm j).val := h_inj _ _ hi hj h_eq
    have h_eq'' : A.row.nodePerm i = A.row.nodePerm j := Fin.ext h_eq'
    have h_eq''' : i = j := A.row.nodePerm.injective h_eq''
    rw [h_eq''']

omit [CharP Omega 2] in
private theorem nodeEquiv_aux (h : A.row.diagram.marks.length = A.tau.rank + 1) :
    ∃ e : Fin A.row.diagram.marks.length ≃ Option (Fin A.tau.rank),
      ∀ k, e k = idxNode k.val := by
  refine ⟨Equiv.ofBijective
    (fun i : Fin A.row.diagram.marks.length => idxNode (r := A.tau.rank) i.val) ?_, fun _ => rfl⟩
  constructor
  · intro i j hij
    have hi : i.val < A.tau.rank + 1 := by rw [← h]; exact i.isLt
    have hj : j.val < A.tau.rank + 1 := by rw [← h]; exact j.isLt
    have h' : i.val = j.val := by
      have hc := congrArg (nodeIdx (r := A.tau.rank)) hij
      rwa [nodeIdx_idxNode hi, nodeIdx_idxNode hj] at hc
    exact Fin.ext h'
  · intro x
    exact ⟨⟨nodeIdx x, by rw [h]; exact nodeIdx_lt x⟩, idxNode_nodeIdx x⟩

private theorem sigma_isZ_aux
    (e : Fin A.row.diagram.marks.length ≃ Option (Fin A.tau.rank))
    (he : ∀ k, e k = idxNode k.val)
    (σ : Equiv.Perm (Option (Fin A.tau.rank)))
    (hσ : ∀ k, σ (idxNode k.val) = idxNode (A.row.nodePerm k).val)
    (x : Option (Fin A.tau.rank)) :
    N.K.IsZ p A.kacMu (σ x) ↔ N.K.IsZ p A.kacMu x := by
  have hx : x = e (e.symm x) := (e.apply_symm_apply x).symm
  have hσx : σ (e (e.symm x)) = idxNode (A.row.nodePerm (e.symm x)).val := by
    rw [he (e.symm x)]
    exact hσ (e.symm x)
  rw [hx, hσx, he (e.symm x)]
  have h1 : (e.symm x).val < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact (e.symm x).isLt
  have h2 : (A.row.nodePerm (e.symm x)).val < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact (A.row.nodePerm (e.symm x)).isLt
  rw [N.isZ_iff h2, N.isZ_iff h1]
  exact s_nodePerm_eq_zero_iff N (e.symm x)

omit [CharP Omega 2] in
private theorem sigma_adj_aux
    (e : Fin A.row.diagram.marks.length ≃ Option (Fin A.tau.rank))
    (he : ∀ k, e k = idxNode k.val)
    (σ : Equiv.Perm (Option (Fin A.tau.rank)))
    (hσ : ∀ k, σ (idxNode k.val) = idxNode (A.row.nodePerm k).val)
    (x y : Option (Fin A.tau.rank)) :
    N.K.Adj (σ x) (σ y) ↔ N.K.Adj x y := by
  have hx : x = e (e.symm x) := (e.apply_symm_apply x).symm
  have hy : y = e (e.symm y) := (e.apply_symm_apply y).symm
  have hσx : σ (e (e.symm x)) = idxNode (A.row.nodePerm (e.symm x)).val := by
    rw [he (e.symm x)]
    exact hσ (e.symm x)
  have hσy : σ (e (e.symm y)) = idxNode (A.row.nodePerm (e.symm y)).val := by
    rw [he (e.symm y)]
    exact hσ (e.symm y)
  rw [hx, hy, hσx, hσy, he (e.symm x), he (e.symm y)]
  have h1 : (e.symm x).val < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact (e.symm x).isLt
  have h2 : (e.symm y).val < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact (e.symm y).isLt
  have h3 : (A.row.nodePerm (e.symm x)).val < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact (A.row.nodePerm (e.symm x)).isLt
  have h4 : (A.row.nodePerm (e.symm y)).val < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact (A.row.nodePerm (e.symm y)).isLt
  rw [N.adj_iff _ _ h3 h4, N.adj_iff _ _ h1 h2]
  exact adj_nodePerm N (e.symm x) (e.symm y)

omit [CharP Omega 2] in
private theorem frobLinear_extRoot_aux
    (e : Fin A.row.diagram.marks.length ≃ Option (Fin A.tau.rank))
    (he : ∀ k, e k = idxNode k.val)
    (σ : Equiv.Perm (Option (Fin A.tau.rank)))
    (hσ : ∀ k, σ (idxNode k.val) = idxNode (A.row.nodePerm k).val)
    (z : Option (Fin A.tau.rank)) :
    A.frobLinear (N.K.extRoot z) = A.epsilon • N.K.extRoot (σ z) := by
  have hz : z = e (e.symm z) := (e.apply_symm_apply z).symm
  rw [hz, he (e.symm z), ← N.nodeMap_eq (e.symm z), A.frob_nodes (e.symm z),
    N.nodeMap_eq (A.row.nodePerm (e.symm z)), hσ (e.symm z)]

private theorem frobLinear_span_image_aux
    (e : Fin A.row.diagram.marks.length ≃ Option (Fin A.tau.rank))
    (he : ∀ k, e k = idxNode k.val)
    (σ : Equiv.Perm (Option (Fin A.tau.rank)))
    (hσ : ∀ k, σ (idxNode k.val) = idxNode (A.row.nodePerm k).val)
    (x : Option (Fin A.tau.rank)) :
    Submodule.map (A.frobLinear : (Fin A.tau.rank → ℤ) →ₗ[ℤ] (Fin A.tau.rank → ℤ))
        (Submodule.span ℤ (N.K.extRoot '' N.K.comp p A.kacMu x)) =
      Submodule.span ℤ (N.K.extRoot '' N.K.comp p A.kacMu (σ x)) := by
  have hfrob := frobLinear_extRoot_aux (N := N) e he σ hσ
  have hcomp : σ '' N.K.comp p A.kacMu x = N.K.comp p A.kacMu (σ x) :=
    N.K.image_comp σ (sigma_isZ_aux (N := N) e he σ hσ)
      (sigma_adj_aux (N := N) e he σ hσ) x
  have hε2 : A.epsilon * A.epsilon = 1 := by
    rw [A.epsilon_eq]; split_ifs <;> norm_num
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro v ⟨z, hz, rfl⟩
    have hz' : σ z ∈ N.K.comp p A.kacMu (σ x) := by
      rw [← hcomp]; exact ⟨z, hz, rfl⟩
    have hgen : N.K.extRoot (σ z) ∈ Submodule.span ℤ (N.K.extRoot '' N.K.comp p A.kacMu (σ x)) :=
      Submodule.subset_span ⟨σ z, hz', rfl⟩
    change A.frobLinear (N.K.extRoot z) ∈
      Submodule.span ℤ (N.K.extRoot '' N.K.comp p A.kacMu (σ x))
    rw [hfrob z]
    exact Submodule.smul_mem _ _ hgen
  · rw [Submodule.span_le]
    rintro v ⟨z', hz', rfl⟩
    have hz'' : z' ∈ σ '' N.K.comp p A.kacMu x := by rw [hcomp]; exact hz'
    obtain ⟨z, hz, hzz'⟩ := hz''
    rw [← hzz']
    have hz'eq : N.K.extRoot (σ z) = A.epsilon • A.frobLinear (N.K.extRoot z) := by
      rw [hfrob z, smul_smul, hε2, one_smul]
    rw [hz'eq]
    exact Submodule.smul_mem _ _ (Submodule.mem_map.mpr
      ⟨N.K.extRoot z, Submodule.subset_span ⟨z, hz, rfl⟩, rfl⟩)

private theorem rho_image_rootsOf_aux
    (e : Fin A.row.diagram.marks.length ≃ Option (Fin A.tau.rank))
    (he : ∀ k, e k = idxNode k.val)
    (σ : Equiv.Perm (Option (Fin A.tau.rank)))
    (hσ : ∀ k, σ (idxNode k.val) = idxNode (A.row.nodePerm k).val)
    (x : Option (Fin A.tau.rank)) :
    (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ)) ''
        N.K.rootsOf (N.K.comp p A.kacMu x) =
      N.K.rootsOf (N.K.comp p A.kacMu (σ x)) := by
  rw [N.K.rootsOf_comp_eq_span N.facts N.zero_lt N.isNormal,
    N.K.rootsOf_comp_eq_span N.facts N.zero_lt N.isNormal]
  have hspan := frobLinear_span_image_aux (N := N) e he σ hσ x
  ext w
  constructor
  · rintro ⟨v, ⟨hv, hmem⟩, rfl⟩
    refine ⟨(A.setup.frob.isRoot_iff v).mpr hv, ?_⟩
    rw [show A.setup.ρ v = A.frobLinear v from (A.frob_roots v hv).symm]
    have hmap : A.frobLinear v ∈ Submodule.map
        (A.frobLinear : (Fin A.tau.rank → ℤ) →ₗ[ℤ] (Fin A.tau.rank → ℤ))
        (Submodule.span ℤ (N.K.extRoot '' N.K.comp p A.kacMu x)) :=
      Submodule.mem_map.mpr ⟨v, hmem, rfl⟩
    rwa [hspan] at hmap
  · rintro ⟨hw, hmem⟩
    have hroot : IsRoot A.tau (A.setup.ρ.symm w) := by
      refine (A.setup.frob.isRoot_iff (A.setup.ρ.symm w)).mp ?_
      rwa [Equiv.apply_symm_apply]
    have hfrobw : A.frobLinear (A.setup.ρ.symm w) = w := by
      rw [A.frob_roots _ hroot, Equiv.apply_symm_apply]
    have hmap : w ∈ Submodule.map
        (A.frobLinear : (Fin A.tau.rank → ℤ) →ₗ[ℤ] (Fin A.tau.rank → ℤ))
        (Submodule.span ℤ (N.K.extRoot '' N.K.comp p A.kacMu x)) := by
      rw [hspan]
      exact hmem
    obtain ⟨v', hv', hfv'⟩ := Submodule.mem_map.mp hmap
    have hfv'' : (A.frobLinear : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ)) v' = w := hfv'
    have hv'eq : v' = A.setup.ρ.symm w :=
      A.frobLinear.injective (by rw [hfv'', hfrobw])
    exact ⟨A.setup.ρ.symm w, ⟨hroot, by rwa [← hv'eq]⟩, Equiv.apply_symm_apply _ _⟩

theorem rho_image_rootsOf_comp (i : Fin A.row.diagram.marks.length) :
    (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ)) ''
        N.K.rootsOf (N.K.comp p A.kacMu (idxNode i.val)) =
      N.K.rootsOf (N.K.comp p A.kacMu (idxNode (A.row.nodePerm i).val)) := by
  obtain ⟨e, he⟩ := nodeEquiv_aux N.length_eq
  let σ : Equiv.Perm (Option (Fin A.tau.rank)) := e.symm.trans (A.row.nodePerm.trans e)
  have hσ : ∀ k, σ (idxNode k.val) = idxNode (A.row.nodePerm k).val := by
    intro k
    have h1 : e.symm (idxNode k.val) = k := by
      rw [← he k]
      exact e.symm_apply_apply k
    dsimp [σ]
    rw [h1, he (A.row.nodePerm k)]
  have hσi : σ (idxNode i.val) = idxNode (A.row.nodePerm i).val := hσ i
  rw [← hσi]
  exact rho_image_rootsOf_aux (N := N) e he σ hσ (idxNode i.val)

end K0Normal

end CFSG.StandardType.GGK0MarkedKacIface1587

end
