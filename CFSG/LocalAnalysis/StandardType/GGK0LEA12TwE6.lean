module

public import CFSG.LocalAnalysis.StandardType.GGK0LEA12
public import CFSG.LocalAnalysis.StandardType.GGK0LQ1
public import CFSG.LocalAnalysis.StandardType.GGK0LQ3
public import CFSG.LocalAnalysis.StandardType.GGK0LQAlgSetup
public import CFSG.LocalAnalysis.StandardType.GGK0LETwE6Normal
public import CFSG.LocalAnalysis.StandardType.GGK0LETwE6Chiral
public import CFSG.LocalAnalysis.StandardType.GGKacTwE6A12Class
public import CFSG.LieType.Chevalley.E6DiagramRootChar
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.Sporadic.ThSchreier.GlobalData

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma lea12e_twE6_kacRow_type_of_tag {lab : LargeEvenLabel} {p : ℕ}
    (row : KacRow lab p) (htag : lab.tag = .twE6) : row.T = .E6 ∧ row.tw = true := by
  have h := row.type_eq
  unfold ggKacTypeOfLabel at h
  rw [htag] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

private lemma lea12e_twE6_marks_length (T : GGKacType) :
    (k0DiagOf T).marks.length = (absTag T).rank + 1 := by
  cases T <;> rfl

private lemma lea12e_twE6_a_eq {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) (tau_eq : absTag row.T = Tag.E6)
    (a : Fin Tag.E6.rank → Omegaˣ) (zeta : Omegaˣ)
    (nodeMap : (Fin row.diagram.marks.length → ℤ) →ₗ[ℤ] (Fin Tag.E6.rank → ℤ))
    (node_eval : ∀ i : Fin row.diagram.marks.length,
      rootChar a (nodeMap (Pi.single i 1)) = zeta ^ (row.s.getD i.val 0))
    (node_std : ∀ (i : Fin row.diagram.marks.length) (j : Fin Tag.E6.rank),
      i.val = j.val + 1 → nodeMap (Pi.single i 1) = Pi.single j 1)
    (i : Fin Tag.E6.rank) :
    a i = zeta ^ (row.s.getD (i.val + 1) 0) := by
  have hmark : row.diagram.marks.length = Tag.E6.rank + 1 := by
    show (k0DiagOf row.T).marks.length = 6 + 1
    rw [lea12e_twE6_marks_length row.T, tau_eq]
    rfl
  have hlt : i.val + 1 < row.diagram.marks.length := by
    rw [hmark]
    exact Nat.succ_lt_succ i.isLt
  have h1 := node_eval ⟨i.val + 1, hlt⟩
  have hstd := node_std ⟨i.val + 1, hlt⟩ i rfl
  rw [hstd] at h1
  have h2 : rootChar a (Pi.single i 1) = a i := by
    simpa using rootChar_nsmul_single a i 1
  rw [h2] at h1
  simpa using h1

private lemma lea12e_twE6_Phi_eq {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (setup : LangSetup Tag.E6 Omega 5) (fr : Omega →+* Omega)
    (h : ∃ ht : TwistTag.E6.tag = Tag.E6, ∀ g : ModGL Tag.E6 Omega,
      setup.D.Φ g = diagramAt Tag.E6 Omega TwistTag.E6 ht * Units.map (entrywiseHom fr) g *
        (diagramAt Tag.E6 Omega TwistTag.E6 ht)⁻¹) :
    setup.D.Φ = twistHom TwistTag.E6 Omega fr := by
  obtain ⟨ht, hΦtw⟩ := h
  have hdiag : diagramAt Tag.E6 Omega TwistTag.E6 ht =
      (diagramMap TwistTag.E6 Omega : ModGL Tag.E6 Omega) := by
    cases ht
    rfl
  refine MonoidHom.ext fun g => ?_
  rw [hΦtw g, hdiag]
  rfl

private theorem lea12e_twE6_a_ne {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} (row : KacRow lab 3) (tau_eq : absTag row.T = Tag.E6)
    (htag : lab.tag = .twE6) (hn : lab.n = 1)
    (j : Fin row.D.orbits.length) (hj : row.D.orbits[j].lab = ⟨.A, 1, 1⟩)
    (hjqs : row.D.orbits[j].qs = false)
    (a : Fin Tag.E6.rank → Omegaˣ) (zeta : Omegaˣ) (zeta_order : orderOf zeta = 3)
    (nodeMap : (Fin row.diagram.marks.length → ℤ) →ₗ[ℤ] (Fin Tag.E6.rank → ℤ))
    (node_eval : ∀ i : Fin row.diagram.marks.length,
      rootChar a (nodeMap (Pi.single i 1)) = zeta ^ (row.s.getD i.val 0))
    (node_std : ∀ (i : Fin row.diagram.marks.length) (j : Fin Tag.E6.rank),
      i.val = j.val + 1 → nodeMap (Pi.single i 1) = Pi.single j 1) :
    a ⟨0, by decide⟩ * a ⟨4, by decide⟩ ≠ a ⟨2, by decide⟩ * a ⟨5, by decide⟩ := by
  intro heq
  have h0 := lea12e_twE6_a_eq row tau_eq a zeta nodeMap node_eval node_std ⟨0, by decide⟩
  have h2 := lea12e_twE6_a_eq row tau_eq a zeta nodeMap node_eval node_std ⟨2, by decide⟩
  have h4 := lea12e_twE6_a_eq row tau_eq a zeta nodeMap node_eval node_std ⟨4, by decide⟩
  have h5 := lea12e_twE6_a_eq row tau_eq a zeta nodeMap node_eval node_std ⟨5, by decide⟩
  rw [h0, h2, h4, h5] at heq
  rw [← pow_add, ← pow_add] at heq
  have hmod : row.s.getD 1 0 + row.s.getD 5 0 ≡ row.s.getD 3 0 + row.s.getD 6 0 [MOD 3] := by
    have h := pow_eq_pow_iff_modEq.mp heq
    rwa [zeta_order] at h
  exact kacRow_twE6_a12_kac_mod_three row htag hn rfl j hj hjqs hmod

theorem k0_exists_modelAction_eq_twE6
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hAlg : ∀ c : Omega, ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c)
    (A : K0LangMark Omega lab p R I phi) (htag : lab.tag = .twE6) (hn : lab.n = 1) (hp : p = 3)
    (j : Fin A.row.D.orbits.length) (hj : A.row.D.orbits[j].lab = ⟨.A, 1, 1⟩)
    (hjqs : A.row.D.orbits[j].qs = false) (u : MulAut R) (hu : Commute u phi) :
    ∃ g : A.setup.D.model, A.modelAction g = u := by
  subst hp
  have hAlgS : A.setup.IsAlgebraic := CFSG.StandardType.GGK0LQ.lq_setup_isAlgebraic hAlg A
  rcases A with ⟨row, tau, tau_eq, setup, q_eq, fr, fr_eq, phi_split, phi_twisted, iota, iota_inj,
    iota_range, modelAction, modelAction_inj, modelAction_range, modelAction_compat, a, a_pow,
    a_torus, a_model, a_ne, action_eq, zeta, zeta_order, nodeMap, nodeMap_surj, nodeMap_ker,
    node_isRoot, node_eval, kernel_span_eq, epsilon, epsilon_eq, frobLinear, frob_roots,
    frob_nodes, node_std⟩
  have hT : row.T = .E6 := (lea12e_twE6_kacRow_type_of_tag row htag).1
  have htw : row.tw = true := (lea12e_twE6_kacRow_type_of_tag row htag).2
  have htau : tau = Tag.E6 := by
    rw [← tau_eq, hT]
    rfl
  subst htau
  have hΦ : setup.D.Φ = twistHom TwistTag.E6 Omega fr :=
    lea12e_twE6_Phi_eq setup fr (phi_twisted htw)
  have hq : setup.D.q = 2 := by
    rw [q_eq, hn]
    norm_num
  have hFr : ∀ c, fr c = c ^ setup.D.q := by
    intro c
    rw [fr_eq c, q_eq]
  rcases CFSG.StandardType.LangRat.exists_modelAction_eq_or_diagram_twE6 (L := Omega)
    setup hq hAlgS hFr hΦ iota_inj
    iota_range modelAction_compat u with ⟨g, hg⟩ | ⟨Z, hZ, hN⟩
  · exact ⟨g, hg⟩
  · have hcomm : Commute u (modelAction ⟨rootDiagUnit Tag.E6 a, a_model⟩) := by
      simpa [← action_eq] using hu
    obtain ⟨X, hX, hconj⟩ :=
      CFSG.StandardType.LangRat.exists_conj_rootDiagUnit_perm_of_commute_twE6
        (L := Omega) setup.D hΦ iota_inj
        modelAction_inj modelAction_compat a_model hZ hN hcomm
    have ha : ∀ i : Fin TwistTag.E6.tag.rank, a i ^ 3 = 1 := a_pow
    have hc : a ⟨0, by decide⟩ * a ⟨4, by decide⟩ ≠
        a ⟨2, by decide⟩ * a ⟨5, by decide⟩ :=
      lea12e_twE6_a_ne row tau_eq htag hn j hj hjqs a zeta zeta_order nodeMap node_eval node_std
    have hweyl : ∃ w : WeylGroup TwistTag.E6.tag, ∀ v : Fin TwistTag.E6.tag.rank → ℤ,
        rootChar a (w • v) = rootChar (fun i => a (TwistTag.E6.perm.symm i)) v :=
      (exceptional_root_diagonal_conjugacy_Weyl_transporter TwistTag.E6.tag Omega a
        (fun i => a (TwistTag.E6.perm.symm i))).1.1 ⟨X, hX, hconj⟩
    obtain ⟨w, hw⟩ := hweyl
    exact absurd ⟨w, hw⟩ (not_exists_weyl_rootChar_eq_perm_E6 ha hc)

theorem k0_fullFactor_a12_twE6
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hAlg : ∀ c : Omega, ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (hqs : ∀ j, A.row.D.orbits[j].qs = true →
      CFSG.IsQuasisimple (rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)))
    (hsolv : ∀ j, A.row.D.orbits[j].qs = false →
      Group.IsSolvable (rationalSpan A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)))
    (hn : 1 ≤ lab.n) (hp : p.Prime) (hd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)
    (j : Fin A.row.D.orbits.length) (hj : A.row.D.orbits[j].lab = ⟨.A, 1, 1⟩)
    (hjqs : A.row.D.orbits[j].qs = false) (htag : lab.tag = .twE6)
    (u : MulAut R) (hu : Commute u phi) :
    (fullFactor A.setup A.iota A.a (P.repr j)).map u.toMonoidHom =
      fullFactor A.setup A.iota A.a (P.repr j) := by
  obtain ⟨hn1, hp3, -⟩ := ggKacValid_a12_tag hn hp hd A.row.valid j ⟨hj, hjqs⟩
  obtain ⟨g, rfl⟩ := k0_exists_modelAction_eq_twE6 hAlg A htag hn1 hp3 j hj hjqs u hu
  exact k0_fullFactor_a12_map_modelAction A P hqs hsolv hn hp hd j hj hjqs g hu

theorem k0_fullFactor_a12_invariant
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hlab : LargeEvenInLambda2 lab)
    (hpair : GGKacExcPair lab p) (hAlg : ∀ c : Omega, ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (hn : 1 ≤ lab.n) (hp : p.Prime) (hd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)
    (j : Fin A.row.D.orbits.length) (hj : A.row.D.orbits[j].lab = ⟨.A, 1, 1⟩)
    (hqs : A.row.D.orbits[j].qs = false) (u : MulAut R) (hu : Commute u phi) :
    (fullFactor A.setup A.iota A.a (P.repr j)).map u.toMonoidHom =
      fullFactor A.setup A.iota A.a (P.repr j) :=
  k0_fullFactor_a12_invariant_of_twE6 hAlg A P
    (fun k hk => k0_rationalComponent_quasisimple hlab hpair A P k hk)
    (fun k hk => k0_rationalSpan_solvable hlab hpair A P k hk) hn hp hd j hj hqs
    (fun htag v hv => k0_fullFactor_a12_twE6 hAlg A P
      (fun k hk => k0_rationalComponent_quasisimple hlab hpair A P k hk)
      (fun k hk => k0_rationalSpan_solvable hlab hpair A P k hk) hn hp hd j hj hqs htag v hv)
    u hu

end CFSG.StandardType.GGK0MarkedKacIface1587
