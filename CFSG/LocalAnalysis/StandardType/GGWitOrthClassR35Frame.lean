module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR35Aux2
public import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ1
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTransitive

public section

namespace CFSG.StandardType.ZS

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem owR35g_e6_conj {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (W : Fin 5 → ZMod p)
    (roots : Fin 6 → Fin 5 → ZMod p) (ord : Fin 72 → Fin 5 → ZMod p) (par : Fin 72 → Fin 72)
    (gen : Fin 72 → Fin 6)
    (hnorm : ∀ i, ∑ k, W k * (roots i k * roots i k) = 1)
    (hfirst : ∀ i : Fin 6, ord (Fin.castLE (by norm_num) i) = roots i)
    (hstep : ∀ j : Fin 72, 6 ≤ j.val → ord j = owR35g_formP p W (roots (gen j)) (ord (par j)))
    (hlt : ∀ j : Fin 72, 6 ≤ j.val → (par j).val < j.val)
    (hcov : ∀ a : Fin 5 → ZMod p, (∑ k, W k * (a k * a k)) = 1 → ∃ j, a = ord j)
    (s : Fin 6 → (Fin 5 → ZMod p) ≃ₗ[ZMod p] (Fin 5 → ZMod p))
    (hs : ∀ i v, s i v = v - owR35g_alphaLinP p W (roots i) v • roots i) :
    closure (ClassRefl p (QuadraticMap.weightedSumSquares (ZMod p) W) 1) =
        closure (Set.range s) ∧
      ∀ t ∈ ClassRefl p (QuadraticMap.weightedSumSquares (ZMod p) W) 1,
        ∃ g ∈ closure (Set.range s), ∃ i, t = g * s i * g⁻¹ := by
  classical
  have hone : (1 : ZMod p) ≠ 0 := by
    intro h
    exact hp.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h))
  let H : Subgroup ((Fin 5 → ZMod p) ≃ₗ[ZMod p] (Fin 5 → ZMod p)) := closure (Set.range s)
  have hsH : ∀ i, s i ∈ H := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hs_eq : ∀ i, s i = Module.reflection (f := owR35g_alphaLinP p W (roots i)) (x := roots i)
      (owR35g_alpha_self W (roots i) (hnorm i)) := by
    intro i
    apply LinearEquiv.ext
    intro v
    rw [hs i v, Module.reflection_apply]
  have hord : ∀ n : ℕ, ∀ j : Fin 72, j.val = n →
      ∃ hn : (∑ k, W k * (ord j k * ord j k)) = 1,
        ∃ g ∈ closure (Set.range s), ∃ i,
          Module.reflection (f := owR35g_alphaLinP p W (ord j)) (x := ord j)
            (owR35g_alpha_self W (ord j) hn) = g * s i * g⁻¹ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro j hjn
      by_cases hj6 : j.val < 6
      · have hjroot : ord j = roots ⟨j.val, hj6⟩ := by
          rw [← hfirst ⟨j.val, hj6⟩]
          rfl
        have hn : (∑ k, W k * (ord j k * ord j k)) = 1 := by
          rw [hjroot]; exact hnorm _
        refine ⟨hn, 1, H.one_mem, ⟨j.val, hj6⟩, ?_⟩
        rw [owR35g_r_congr W (ord j) (roots ⟨j.val, hj6⟩) hn (hnorm _) hjroot]
        simp only [one_mul, inv_one, mul_one]
        exact (hs_eq ⟨j.val, hj6⟩).symm
      · have hj6' : 6 ≤ j.val := not_lt.mp hj6
        have hpar := hlt j hj6'
        obtain ⟨hnp, g, hg, i, hmi⟩ := ih (par j).val (by omega) (par j) rfl
        have hbn := hnorm (gen j)
        have hn : (∑ k, W k * (ord j k * ord j k)) = 1 := by
          rw [hstep j hj6']
          exact owR35g_formP_norm W (roots (gen j)) (ord (par j)) hbn hnp
        refine ⟨hn, s (gen j) * g, H.mul_mem (hsH (gen j)) hg, i, ?_⟩
        rw [owR35g_r_congr W (ord j) (owR35g_formP p W (roots (gen j)) (ord (par j))) hn
            (owR35g_formP_norm W _ _ hbn hnp) (hstep j hj6'),
          ← owR35g_reflP_conj W (roots (gen j)) (ord (par j)) hbn hnp, hmi]
        rw [← hs_eq (gen j)]
        simp only [mul_assoc, mul_inv_rev]
  have hclass : ∀ t ∈ ClassRefl p (QuadraticMap.weightedSumSquares (ZMod p) W) 1,
      ∃ g ∈ closure (Set.range s), ∃ i, t = g * s i * g⁻¹ := by
    intro t ht
    rw [wit_coord_classRefl_iff hp hp2 W 1 hone] at ht
    obtain ⟨a, ha, hta⟩ := ht
    have hra : t = Module.reflection (f := owR35g_alphaLinP p W a) (x := a)
        (owR35g_alpha_self W a ha) := by
      ext v
      rw [hta v, Module.reflection_apply]
      simp only [owR35g_alphaLinP, LinearMap.coe_mk, AddHom.coe_mk, ZMod.inv_one, mul_one]
    obtain ⟨j, hj⟩ := hcov a ha
    obtain ⟨hn, g, hg, i, hmi⟩ := hord j.val j rfl
    refine ⟨g, hg, i, ?_⟩
    rw [hra, owR35g_r_congr W a (ord j) ha hn hj]
    exact hmi
  have hgen : closure (ClassRefl p (QuadraticMap.weightedSumSquares (ZMod p) W) 1) =
      closure (Set.range s) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro t ht
      obtain ⟨g, hg, i, hti⟩ := hclass t ht
      rw [hti]
      exact H.mul_mem (H.mul_mem hg (hsH i)) (H.inv_mem hg)
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      apply Subgroup.subset_closure
      rw [hs_eq i]
      rw [wit_coord_classRefl_iff hp hp2 W 1 hone]
      refine ⟨roots i, hnorm i, fun v => ?_⟩
      rw [Module.reflection_apply]
      simp only [owR35g_alphaLinP, LinearMap.coe_mk, AddHom.coe_mk, ZMod.inv_one, mul_one]
  exact ⟨hgen, hclass⟩

open CFSG.QuasithinUnique.Setup.Layer in
private lemma owR35g_conj_mem_classRefl {p : ℕ} (hp : p.Prime) {U V : Type} [AddCommGroup U]
    [Module (ZMod p) U] [AddCommGroup V] [Module (ZMod p) V] {Q : QuadraticForm (ZMod p) U}
    {Q' : QuadraticForm (ZMod p) V} (e : U ≃ₗ[ZMod p] V) (he : ∀ v, Q' (e v) = Q v)
    {c : ZMod p} {t : U ≃ₗ[ZMod p] U} (ht : t ∈ ClassRefl p Q c) :
    e.symm.trans (t.trans e) ∈ ClassRefl p Q' c := by
  haveI : Fact p.Prime := ⟨hp⟩
  change autConj e t ∈ ClassRefl p Q' c
  rcases ht with ⟨hr, hiso, a, hQa, hta⟩
  refine ⟨⟨?_, ?_⟩, ?_, e a, ?_, ?_⟩
  · rw [← map_mul, hr.1, map_one]
  · have hrange : LinearMap.range
        (((autConj e t : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) - LinearMap.id) =
        Submodule.map ((e : U ≃ₗ[ZMod p] V) : U →ₗ[ZMod p] V)
          (LinearMap.range (((t : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - LinearMap.id)) := by
      ext y
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨t (e.symm x) - e.symm x, ⟨e.symm x, rfl⟩, ?_⟩
        rw [← hx]
        simp [autConj_apply, sub_eq_add_neg]
      · rintro ⟨w, ⟨u, hu⟩, hw⟩
        refine ⟨e u, ?_⟩
        rw [← hw, ← hu]
        simp [autConj_apply, sub_eq_add_neg]
    rw [hrange, LinearEquiv.finrank_map_eq, hr.2]
  · intro v
    calc Q' (autConj e t v) = Q (t (e.symm v)) := by rw [autConj_apply, he]
      _ = Q (e.symm v) := hiso _
      _ = Q' v := by rw [← he (e.symm v), e.apply_symm_apply]
  · rw [he, hQa]
  · rw [autConj_apply, e.symm_apply_apply, hta, map_neg]

open CFSG.QuasithinUnique.Setup.Layer in
theorem owR35g_e6_frame {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (Q : QuadraticForm (ZMod p) U) (e : U ≃ₗ[ZMod p] (Fin 5 → ZMod p))
    (W : Fin 5 → ZMod p) (he : ∀ v, Q v = ∑ i, W i * (e v i) ^ 2)
    (roots : Fin 6 → Fin 5 → ZMod p) (ord : Fin 72 → Fin 5 → ZMod p) (par : Fin 72 → Fin 72)
    (gen : Fin 72 → Fin 6)
    (hnorm : ∀ i, ∑ k, W k * (roots i k * roots i k) = 1)
    (hP : ∀ i j, owR35g_alphaLinP p W (roots i) (roots j) = (CartanMatrix.E 6 i j : ZMod p))
    (hfirst : ∀ i : Fin 6, ord (Fin.castLE (by norm_num) i) = roots i)
    (hstep : ∀ j : Fin 72, 6 ≤ j.val → ord j = owR35g_formP p W (roots (gen j)) (ord (par j)))
    (hlt : ∀ j : Fin 72, 6 ≤ j.val → (par j).val < j.val)
    (hcov : ∀ a : Fin 5 → ZMod p, (∑ k, W k * (a k * a k)) = 1 → ∃ j, a = ord j) :
    ∃ (u : Fin 6 → U) (φ : Fin 6 → Module.Dual (ZMod p) U) (hφ : ∀ i, φ i (u i) = 2),
      (∀ i j, φ i (u j) = (CartanMatrix.E 6 i j : ZMod p)) ∧
      closure (ClassRefl p Q 1) = closure (Set.range fun i => Module.reflection (hφ i)) ∧
      ∀ t ∈ ClassRefl p Q 1, ∃ g ∈ closure (Set.range fun i => Module.reflection (hφ i)), ∃ i,
        t = g * Module.reflection (hφ i) * g⁻¹ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let Q' : QuadraticForm (ZMod p) (Fin 5 → ZMod p) := QuadraticMap.weightedSumSquares (ZMod p) W
  have he' : ∀ v, Q' (e v) = Q v := by
    intro v
    rw [he v]
    simp only [Q', QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two]
  let u : Fin 6 → U := fun i => e.symm (roots i)
  let φ : Fin 6 → Module.Dual (ZMod p) U :=
    fun i => (owR35g_alphaLinP p W (roots i)).comp e.toLinearMap
  have hφ : ∀ i, φ i (u i) = 2 := by
    intro i
    change owR35g_alphaLinP p W (roots i) (e (e.symm (roots i))) = 2
    rw [e.apply_symm_apply]
    exact owR35g_alpha_self W (roots i) (hnorm i)
  have hφcart : ∀ i j, φ i (u j) = (CartanMatrix.E 6 i j : ZMod p) := by
    intro i j
    change owR35g_alphaLinP p W (roots i) (e (e.symm (roots j))) = _
    rw [e.apply_symm_apply]
    exact hP i j
  let s : Fin 6 → (Fin 5 → ZMod p) ≃ₗ[ZMod p] (Fin 5 → ZMod p) :=
    fun i => Module.reflection (owR35g_alpha_self W (roots i) (hnorm i))
  have hs : ∀ i v, s i v = v - owR35g_alphaLinP p W (roots i) v • roots i := by
    intro i v
    change Module.reflection (owR35g_alpha_self W (roots i) (hnorm i)) v = _
    rw [Module.reflection_apply]
  obtain ⟨hgen, hconj⟩ :=
    owR35g_e6_conj hp hp2 W roots ord par gen hnorm hfirst hstep hlt hcov s hs
  have hgen' : closure (ClassRefl p Q' 1) = closure (Set.range s) := hgen
  have hconj' : ∀ t ∈ ClassRefl p Q' 1, ∃ g ∈ closure (Set.range s), ∃ i,
      t = g * s i * g⁻¹ := hconj
  have href : ∀ i, Module.reflection (hφ i) = autConj e.symm (s i) := by
    intro i
    ext v
    rw [Module.reflection_apply, autConj_apply]
    change v - owR35g_alphaLinP p W (roots i) (e v) • e.symm (roots i)
        = e.symm (s i (e v))
    rw [hs i (e v)]
    simp only [map_sub, map_smul]
    simp
  have he'' : ∀ w : Fin 5 → ZMod p, Q (e.symm w) = Q' w := by
    intro w
    rw [← he' (e.symm w), e.apply_symm_apply]
  have himg : (⇑(autConj e.symm).toMonoidHom) '' ClassRefl p Q' 1 = ClassRefl p Q 1 := by
    ext t
    constructor
    · rintro ⟨s0, hs0, rfl⟩
      exact owR35g_conj_mem_classRefl hp e.symm he'' hs0
    · intro ht
      refine ⟨autConj e t, owR35g_conj_mem_classRefl hp e he' ht, ?_⟩
      ext x
      simp [autConj_apply]
  have hrange : (⇑(autConj e.symm).toMonoidHom) '' Set.range s =
      Set.range (fun i => Module.reflection (hφ i)) := by
    ext t
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, href i⟩
    · rintro ⟨i, rfl⟩
      exact ⟨s i, ⟨i, rfl⟩, (href i).symm⟩
  have hgen'' : closure (ClassRefl p Q 1) =
      closure (Set.range fun i => Module.reflection (hφ i)) := by
    have hmap := congrArg (Subgroup.map (autConj e.symm).toMonoidHom) hgen'
    rw [MonoidHom.map_closure, MonoidHom.map_closure, himg] at hmap
    rw [hrange] at hmap
    exact hmap
  refine ⟨u, φ, hφ, hφcart, hgen'', ?_⟩
  intro t ht
  have ht' : t ∈ (⇑(autConj e.symm).toMonoidHom) '' ClassRefl p Q' 1 := by
    rw [himg]; exact ht
  rcases ht' with ⟨t0, ht0, rfl⟩
  obtain ⟨g, hg, i, hgi⟩ := hconj' t0 ht0
  refine ⟨autConj e.symm g, ?_, i, ?_⟩
  · have hg' : autConj e.symm g ∈
        Subgroup.map (autConj e.symm).toMonoidHom (closure (Set.range s)) :=
      Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    rwa [MonoidHom.map_closure, hrange] at hg'
  · rw [hgi]
    change autConj e.symm (g * s i * g⁻¹) =
      autConj e.symm g * Module.reflection (hφ i) * (autConj e.symm g)⁻¹
    rw [map_mul, map_mul, map_inv, ← href i]

theorem owR35_e6_frame_odd {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (Q : QuadraticForm (ZMod 3) U) (e : U ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) (k : Fin 6)
    (hk : k = 1 ∨ k = 3 ∨ k = 5) (he : ∀ v, Q v = ∑ i, owR35_wcan k i * (e v i) ^ 2) :
    ∃ (u : Fin 6 → U) (φ : Fin 6 → Module.Dual (ZMod 3) U) (hφ : ∀ i, φ i (u i) = 2),
      (∀ i j, φ i (u j) = (CartanMatrix.E 6 i j : ZMod 3)) ∧
      closure (ClassRefl 3 Q 1) = closure (Set.range fun i => Module.reflection (hφ i)) ∧
      ∀ t ∈ ClassRefl 3 Q 1, ∃ g ∈ closure (Set.range fun i => Module.reflection (hφ i)), ∃ i,
        t = g * Module.reflection (hφ i) * g⁻¹ := by
  rcases hk with rfl | rfl | rfl
  ·
    have hnorm : ∀ i, ∑ k, (owR35_wcan 1) k * (owR35_roots1 i k * owR35_roots1 i k) = 1 :=
      fun i => by simpa only [pow_two] using owR35_hQ1 i
    exact owR35g_e6_frame (p := 3) (by norm_num) (by norm_num) Q e (owR35_wcan 1) he
      owR35_roots1 owR35_ord1 owR35_par1 owR35_gen1 hnorm
      (fun i j => by rw [owR35_alpha_eq]; exact owR35_hP1 i j)
      owR35_hfirst1
      (fun j hj => by
        rw [← owR35_reflFun_eq (owR35_wcan 1) _ _ (hnorm (owR35_gen1 j))]
        exact (owR35_hstep1 j hj).symm)
      owR35_hlt1
      (fun a ha => owR35_hcov1 a (by simpa only [pow_two] using ha))
  ·
    have hnorm : ∀ i, ∑ k, (owR35_wcan 3) k * (owR35_roots3 i k * owR35_roots3 i k) = 1 :=
      fun i => by simpa only [pow_two] using owR35_hQ3 i
    exact owR35g_e6_frame (p := 3) (by norm_num) (by norm_num) Q e (owR35_wcan 3) he
      owR35_roots3 owR35_ord3 owR35_par3 owR35_gen3 hnorm
      (fun i j => by rw [owR35_alpha_eq]; exact owR35_hP3 i j)
      owR35_hfirst3
      (fun j hj => by
        rw [← owR35_reflFun_eq (owR35_wcan 3) _ _ (hnorm (owR35_gen3 j))]
        exact (owR35_hstep3 j hj).symm)
      owR35_hlt3
      (fun a ha => owR35_hcov3 a (by simpa only [pow_two] using ha))
  ·
    have hnorm : ∀ i, ∑ k, (owR35_wcan 5) k * (owR35_roots5 i k * owR35_roots5 i k) = 1 :=
      fun i => by simpa only [pow_two] using owR35_hQ5 i
    exact owR35g_e6_frame (p := 3) (by norm_num) (by norm_num) Q e (owR35_wcan 5) he
      owR35_roots5 owR35_ord5 owR35_par5 owR35_gen5 hnorm
      (fun i j => by rw [owR35_alpha_eq]; exact owR35_hP5 i j)
      owR35_hfirst5
      (fun j hj => by
        rw [← owR35_reflFun_eq (owR35_wcan 5) _ _ (hnorm (owR35_gen5 j))]
        exact (owR35_hstep5 j hj).symm)
      owR35_hlt5
      (fun a ha => owR35_hcov5 a (by simpa only [pow_two] using ha))

theorem owR35_neg_mem_even {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    [Module.Finite (ZMod 3) U] (Q : QuadraticForm (ZMod 3) U)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (e : U ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (k : Fin 6) (hk : k = 0 ∨ k = 2 ∨ k = 4)
    (he : ∀ v, Q v = ∑ i, owR35_wcan k i * (e v i) ^ 2) :
    (LinearEquiv.neg (ZMod 3) : U ≃ₗ[ZMod 3] U) ∈ closure (ClassRefl 3 Q 1) := by
  rcases hk with rfl | rfl | rfl
  ·
    let B : Fin 5 → Fin 5 → ZMod 3 := fun i => Pi.single i 1
    have hB : Submodule.span (ZMod 3) (Set.range B) = ⊤ := by
      have hbasis : Set.range B = Set.range (Pi.basisFun (ZMod 3) (Fin 5)) := by
        ext x
        simp [B, Pi.basisFun_apply]
      rw [hbasis]
      exact (Pi.basisFun (ZMod 3) (Fin 5)).span_eq
    have hspan : ⊤ ≤ Submodule.span (ZMod 3) (Set.range fun i => e.symm (B i)) := by
      rw [Set.range_comp' e.symm B]
      change ⊤ ≤ Submodule.span (ZMod 3) (⇑(e.symm.toLinearMap) '' Set.range B)
      rw [← Submodule.map_span e.symm.toLinearMap (Set.range B), hB, Submodule.map_top,
        LinearMap.range_eq_top.mpr e.symm.surjective]
    have hb : ∀ i, Q (e.symm (B i)) = 1 := by
      intro i
      rw [he, LinearEquiv.apply_symm_apply]
      simp only [B, owR35_wcan, Pi.single_apply]
      rw [Fin.sum_univ_five]
      decide +kernel +revert
    have horth : ∀ i j : Fin 5, i ≠ j → QuadraticMap.polar Q (e.symm (B i)) (e.symm (B j)) = 0 := by
      intro i j hij
      rw [QuadraticMap.polar]
      have h_add : e.symm (B i) + e.symm (B j) = e.symm (B i + B j) := by
        rw [← LinearEquiv.map_add]
      rw [h_add]
      simp only [he, LinearEquiv.apply_symm_apply]
      rw [Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five]
      simp only [B, owR35_wcan, Pi.single_apply]
      fin_cases i <;> fin_cases j <;> simp_all <;> decide +kernel
    exact neg_mem_closure_classRefl_of_orthogonal (by norm_num) hQ one_ne_zero
      (fun i => e.symm (B i)) horth hb hspan
  ·
    let B : Fin 5 → Fin 5 → ZMod 3 :=
      ![![1,1,0,0,0], ![1,2,0,0,0], ![0,0,1,0,0], ![0,0,0,1,0], ![0,0,0,0,1]]
    have hB : Submodule.span (ZMod 3) (Set.range B) = ⊤ := by
      apply LinearIndependent.span_eq_top_of_card_eq_finrank
      · change LinearIndependent (ZMod 3) (Matrix.of B).row
        rw [Matrix.linearIndependent_rows_iff_isUnit]
        rw [Matrix.isUnit_iff_isUnit_det]
        rw [isUnit_iff_ne_zero]
        decide +kernel +revert
      · simp [Fintype.card_fin, Module.finrank_fintype_fun_eq_card]
    have hspan : ⊤ ≤ Submodule.span (ZMod 3) (Set.range fun i => e.symm (B i)) := by
      rw [Set.range_comp' e.symm B]
      change ⊤ ≤ Submodule.span (ZMod 3) (⇑(e.symm.toLinearMap) '' Set.range B)
      rw [← Submodule.map_span e.symm.toLinearMap (Set.range B), hB, Submodule.map_top,
        LinearMap.range_eq_top.mpr e.symm.surjective]
    have hb : ∀ i, Q (e.symm (B i)) = 1 := by
      intro i
      fin_cases i <;> rw [he, LinearEquiv.apply_symm_apply] <;> simp only [B, owR35_wcan] <;>
        rw [Fin.sum_univ_five] <;> decide +kernel +revert
    have horth : ∀ i j : Fin 5, i ≠ j → QuadraticMap.polar Q (e.symm (B i)) (e.symm (B j)) = 0 := by
      intro i j hij
      rw [QuadraticMap.polar]
      have h_add : e.symm (B i) + e.symm (B j) = e.symm (B i + B j) := by
        rw [← LinearEquiv.map_add]
      rw [h_add]
      simp only [he, LinearEquiv.apply_symm_apply]
      rw [Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five]
      simp only [B, owR35_wcan]
      fin_cases i <;> fin_cases j <;> simp_all <;> decide +kernel +revert
    exact neg_mem_closure_classRefl_of_orthogonal (by norm_num) hQ one_ne_zero
      (fun i => e.symm (B i)) horth hb hspan
  ·
    let B : Fin 5 → Fin 5 → ZMod 3 :=
      ![![1,1,0,0,0], ![1,2,0,0,0], ![0,0,1,1,0], ![0,0,1,2,0], ![0,0,0,0,1]]
    have hB : Submodule.span (ZMod 3) (Set.range B) = ⊤ := by
      apply LinearIndependent.span_eq_top_of_card_eq_finrank
      · change LinearIndependent (ZMod 3) (Matrix.of B).row
        rw [Matrix.linearIndependent_rows_iff_isUnit]
        rw [Matrix.isUnit_iff_isUnit_det]
        rw [isUnit_iff_ne_zero]
        decide +kernel +revert
      · simp [Fintype.card_fin, Module.finrank_fintype_fun_eq_card]
    have hspan : ⊤ ≤ Submodule.span (ZMod 3) (Set.range fun i => e.symm (B i)) := by
      rw [Set.range_comp' e.symm B]
      change ⊤ ≤ Submodule.span (ZMod 3) (⇑(e.symm.toLinearMap) '' Set.range B)
      rw [← Submodule.map_span e.symm.toLinearMap (Set.range B), hB, Submodule.map_top,
        LinearMap.range_eq_top.mpr e.symm.surjective]
    have hb : ∀ i, Q (e.symm (B i)) = 1 := by
      intro i
      fin_cases i <;> rw [he, LinearEquiv.apply_symm_apply] <;> simp only [B, owR35_wcan] <;>
        rw [Fin.sum_univ_five] <;> decide +kernel +revert
    have horth : ∀ i j : Fin 5, i ≠ j → QuadraticMap.polar Q (e.symm (B i)) (e.symm (B j)) = 0 := by
      intro i j hij
      rw [QuadraticMap.polar]
      have h_add : e.symm (B i) + e.symm (B j) = e.symm (B i + B j) := by
        rw [← LinearEquiv.map_add]
      rw [h_add]
      simp only [he, LinearEquiv.apply_symm_apply]
      rw [Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five]
      simp only [B, owR35_wcan]
      fin_cases i <;> fin_cases j <;> simp_all <;> decide +kernel +revert
    exact neg_mem_closure_classRefl_of_orthogonal (by norm_num) hQ one_ne_zero
      (fun i => e.symm (B i)) horth hb hspan

theorem owR35_e6Frame {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [Module.Finite (ZMod 3) U]
    (Q : QuadraticForm (ZMod 3) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) U = 5) (c : ZMod 3) (hc : c ≠ 0)
    (hneg : (LinearEquiv.neg (ZMod 3) : U ≃ₗ[ZMod 3] U) ∉ closure (ClassRefl 3 Q c)) :
    ∃ (u : Fin 6 → U) (φ : Fin 6 → Module.Dual (ZMod 3) U) (hφ : ∀ i, φ i (u i) = 2),
      (∀ i j, φ i (u j) = (CartanMatrix.E 6 i j : ZMod 3)) ∧
      closure (ClassRefl 3 Q c) = closure (Set.range fun i => Module.reflection (hφ i)) ∧
      ∀ t ∈ ClassRefl 3 Q c, ∃ g ∈ closure (Set.range fun i => Module.reflection (hφ i)), ∃ i,
        t = g * Module.reflection (hφ i) * g⁻¹ := by
  obtain ⟨e, w, hw, he⟩ := wit_orth_normal (p := 3) (by norm_num) (by norm_num) Q hQ
  generalize hdU : Module.finrank (ZMod 3) U = d at e w he
  have hd5 : d = 5 := by rw [← hdU]; exact hd
  subst hd5
  have hcinv : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  have hu : c⁻¹ ≠ 0 := inv_ne_zero hc
  have hcl : ClassRefl 3 Q c = ClassRefl 3 (c⁻¹ • Q) 1 := by
    rw [owR35_classRefl_smul_form Q c c⁻¹ hu, hcinv]
  rw [hcl] at hneg ⊢
  have hQ1 : (QuadraticMap.polarBilin (c⁻¹ • Q)).Nondegenerate := owR35_nondeg_smul Q hQ hu
  have hw1 : ∀ i, c⁻¹ * w i = 1 ∨ c⁻¹ * w i = 2 := by
    intro i
    have h0 : c⁻¹ * w i ≠ 0 := mul_ne_zero hu (hw i)
    have hcases : ∀ m : ZMod 3, m ≠ 0 → m = 1 ∨ m = 2 := by decide
    exact hcases _ h0
  have he1 : ∀ v, (c⁻¹ • Q) v = ∑ i, (c⁻¹ * w i) * (e v i) ^ 2 := by
    intro v
    rw [QuadraticMap.smul_apply, he v, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨π, hπ⟩ := owR35_perm_exists (fun i => c⁻¹ * w i) hw1
  let e' : U ≃ₗ[ZMod 3] (Fin 5 → ZMod 3) := e.trans (owR35_permIso π)
  have he' : ∀ v, (c⁻¹ • Q) v =
      ∑ i, owR35_wcan (owR35_kOf (fun i => c⁻¹ * w i)) i * (e' v i) ^ 2 := by
    intro v
    have h := owR35_permIso_form π (fun i => c⁻¹ * w i) (owR35_kOf (fun i => c⁻¹ * w i)) hπ (e v)
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul] at h
    rw [he1 v]
    simp only [pow_two]
    exact h.symm
  generalize owR35_kOf (fun i => c⁻¹ * w i) = k at he'
  fin_cases k
  · exact absurd (owR35_neg_mem_even (c⁻¹ • Q) hQ1 e' 0 (by decide) he') hneg
  · exact owR35_e6_frame_odd (c⁻¹ • Q) e' 1 (by decide) he'
  · exact absurd (owR35_neg_mem_even (c⁻¹ • Q) hQ1 e' 2 (by decide) he') hneg
  · exact owR35_e6_frame_odd (c⁻¹ • Q) e' 3 (by decide) he'
  · exact absurd (owR35_neg_mem_even (c⁻¹ • Q) hQ1 e' 4 (by decide) he') hneg
  · exact owR35_e6_frame_odd (c⁻¹ • Q) e' 5 (by decide) he'

end CFSG.StandardType.ZS

end
