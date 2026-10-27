module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OParA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OParW
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutC
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutR
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OTrans
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmMinus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap Matrix
open CFSG.LieType.Universal.Spin (quadMinus)

@[expose] def radStdPlane (F : Type) [Field F] : Submodule F (OW F) :=
  Submodule.span F {eV F idx0, eV F idx1}

theorem exists_conj_le_radGrp_of_fixes_singular_plane_std
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)}
    (hEΩ : E ≤ StatedOmega (StatedQuadMinus 3 F b c))
    (hE2 : ∀ g ∈ E, g * g = 1)
    {U : Submodule F (OW F)} (hU2 : Module.finrank F U = 2)
    (hUs : ∀ u ∈ U, StatedQuadMinus 3 F b c u = 0)
    (hfix : ∀ g ∈ E, ∀ u ∈ U, gv g u = u) :
    ∃ x : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F,
      (∀ v : OW F, StatedQuadMinus 3 F b c (gv x v) = StatedQuadMinus 3 F b c v) ∧
      (∀ u ∈ U, gv x u ∈ radStdPlane F) ∧
      ∀ g ∈ E, x * g * x⁻¹ ∈ RadGrp b c := by
  classical
  let bU : Module.Basis (Fin 2) F U := Module.finBasisOfFinrankEq F U hU2
  let w : OW F := (bU 0 : U)
  let u : OW F := (bU 1 : U)
  have hwU : w ∈ U := (bU 0).2
  have huU : u ∈ U := (bU 1).2
  have hli : LinearIndependent F ![w, u] := by
    have hb : LinearIndependent F (fun i : Fin 2 => (bU i : OW F)) :=
      bU.linearIndependent.map' U.subtype (by simp)
    have hfun : (![w, u] : Fin 2 → OW F) = fun i => (bU i : OW F) := by
      funext i
      fin_cases i <;> rfl
    rw [hfun]
    exact hb
  have hw : quadMinus 3 F b c w = 0 := by
    rw [quadMinus_eq_stated]
    exact hUs w hwU
  have hu : quadMinus 3 F b c u = 0 := by
    rw [quadMinus_eq_stated]
    exact hUs u huU
  have hwu : polar (quadMinus 3 F b c) w u = 0 := by
    have h1 : quadMinus 3 F b c (w + u) = 0 := by
      rw [quadMinus_eq_stated]
      exact hUs _ (U.add_mem hwU huU)
    simp [QuadraticMap.polar, h1, hw, hu]
  obtain ⟨G, hGiso, hGe0, hGe1⟩ := exists_gl_isometry_pair hirr hli hw hu hwu
  have hGinv : ∀ v : OW F, quadMinus 3 F b c (gv G⁻¹ v) = quadMinus 3 F b c v := by
    intro v
    have h := map_of_mem hGiso (gv G⁻¹ v)
    change quadMinus 3 F b c (gv G (gv G⁻¹ v)) = quadMinus 3 F b c (gv G⁻¹ v) at h
    rw [gv_gv_inv] at h
    exact h.symm
  refine ⟨G⁻¹, ?_, ?_, ?_⟩
  · intro v
    simpa only [← quadMinus_eq_stated] using hGinv v
  · intro z hz
    have hz' : z = bU.repr ⟨z, hz⟩ 0 • w + bU.repr ⟨z, hz⟩ 1 • u := by
      have h := bU.sum_repr ⟨z, hz⟩
      rw [Fin.sum_univ_two] at h
      simpa [w, u] using (congrArg Subtype.val h).symm
    rw [hz', gv_add, gv_smul, gv_smul]
    have hw' : gv G⁻¹ w = eV F idx0 := by
      rw [← hGe0, gv_inv_gv]
    have hu' : gv G⁻¹ u = eV F idx1 := by
      rw [← hGe1, gv_inv_gv]
    rw [hw', hu']
    have hmem0 : eV F idx0 ∈ radStdPlane F :=
      Submodule.subset_span (Set.mem_insert (eV F idx0) {eV F idx1})
    have hmem1 : eV F idx1 ∈ radStdPlane F :=
      Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton (eV F idx1)))
    exact (radStdPlane F).add_mem ((radStdPlane F).smul_mem _ hmem0)
      ((radStdPlane F).smul_mem _ hmem1)
  · intro g hg
    have hΩ : g ∈ StatedOmega (StatedQuadMinus 3 F b c) := hEΩ hg
    have hΩ' : G⁻¹ * g * (G⁻¹)⁻¹ ∈ StatedOmega (StatedQuadMinus 3 F b c) :=
      OutLin.outIsoConj_mem_omega hGinv hΩ
    have hfix' : ∀ i : Fin (3 - 1), gv (G⁻¹ * g * (G⁻¹)⁻¹) (eV F i) = eV F i := by
      intro i
      fin_cases i
      · rw [inv_inv, gv_mul, gv_mul, hGe0, hfix g hg w hwU, ← hGe0, gv_inv_gv]
      · rw [inv_inv, gv_mul, gv_mul, hGe1, hfix g hg u huU, ← hGe1, gv_inv_gv]
    have hsq : (G⁻¹ * g * (G⁻¹)⁻¹) * (G⁻¹ * g * (G⁻¹)⁻¹) = 1 := by
      rw [inv_inv]
      calc (G⁻¹ * g * G) * (G⁻¹ * g * G) = G⁻¹ * (g * g) * G := by group
        _ = 1 := by rw [hE2 g hg]; group
    exact mem_RadGrp.mpr (rad_of_involution hirr hΩ' hsq hfix')

theorem exists_conj_le_radGrp_of_fixes_singular_plane
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)}
    (hEΩ : E ≤ StatedOmega (StatedQuadMinus 3 F b c))
    (hE2 : ∀ g ∈ E, g * g = 1)
    {U : Submodule F (OW F)} (hU2 : Module.finrank F U = 2)
    (hUs : ∀ u ∈ U, StatedQuadMinus 3 F b c u = 0)
    (hfix : ∀ g ∈ E, ∀ u ∈ U, gv g u = u) :
    ∃ x : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F,
      (∀ v : OW F, StatedQuadMinus 3 F b c (gv x v) = StatedQuadMinus 3 F b c v) ∧
      ∀ g ∈ E, x * g * x⁻¹ ∈ RadGrp b c := by
  obtain ⟨x, hx, -, hconj⟩ :=
    exists_conj_le_radGrp_of_fixes_singular_plane_std hirr hEΩ hE2 hU2 hUs hfix
  exact ⟨x, hx, hconj⟩

theorem rk_le_of_singComm
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F} {n : ℕ}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)}
    (hEΩ : E ≤ StatedOmega (StatedQuadMinus 3 F b c))
    (hE2 : ∀ g ∈ E, g * g = 1)
    {T : Set (OW F)}
    (hTQ : ∀ v ∈ T, StatedQuadMinus 3 F b c v = 0)
    (hTadd : ∀ u ∈ T, ∀ v ∈ T, u + v ∈ T)
    (hTcomm : ∀ g ∈ E, ∀ v : OW F, gv g v - v ∈ T) :
    rk ↥E ≤ n := by
  classical
  let U : Submodule F (OW F) := Submodule.span F T
  have hTsub : T ⊆ U := Submodule.subset_span
  have hTQ' : ∀ v ∈ T, quadMinus 3 F b c v = 0 := by
    intro v hv
    rw [quadMinus_eq_stated]
    exact hTQ v hv
  have hTpol : ∀ u ∈ T, ∀ v ∈ T, polar (quadMinus 3 F b c) u v = 0 := by
    intro u hu v hv
    have h1 : quadMinus 3 F b c (u + v) = 0 := hTQ' _ (hTadd u hu v hv)
    have h2 : quadMinus 3 F b c u = 0 := hTQ' u hu
    have h3 : quadMinus 3 F b c v = 0 := hTQ' v hv
    rw [QuadraticMap.polar, h1, h2, h3]
    ring
  have hUQ : ∀ u ∈ U, quadMinus 3 F b c u = 0 :=
    fun u hu => map_eq_zero_of_mem_span hTQ' hTpol hu
  have hUs : ∀ u ∈ U, StatedQuadMinus 3 F b c u = 0 := by
    intro u hu
    rw [← quadMinus_eq_stated]
    exact hUQ u hu
  have hUorth : U ≤ LinearMap.BilinForm.orthogonal (quadMinus 3 F b c).polarBilin U := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    rw [polarBilin_apply_apply]
    have h1 : quadMinus 3 F b c (v + u) = 0 := by
      rw [add_comm]
      exact hUQ _ (U.add_mem hu hv)
    have h2 : quadMinus 3 F b c u = 0 := hUQ u hu
    have h3 : quadMinus 3 F b c v = 0 := hUQ v hv
    rw [QuadraticMap.polar, h1, h3, h2]
    ring
  have hcommU : ∀ g ∈ E,
      CFSG.RankThree.OrthogonalInvolutions.commSpace
        (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F g) ≤ U := by
    intro g hg
    rintro _ ⟨v, rfl⟩
    exact hTsub (hTcomm g hg v)
  have hfixU : ∀ g ∈ E, ∀ u ∈ U, gv g u = u := by
    intro g hg u hu
    have hO : toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F g ∈
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 F b c) :=
      commutator_le_orthogonalGroup_self (quadMinus 3 F b c) ((mem_statedOmega_iff g).mp (hEΩ hg))
    have htt : toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F g *
        toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F g = 1 := by
      rw [← map_mul, hE2 g hg, map_one]
    have hfixeq := CFSG.RankThree.OrthogonalInvolutions.fixSpace_eq_orthogonal_commSpace
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr) hO htt
    have hanti : LinearMap.BilinForm.orthogonal (quadMinus 3 F b c).polarBilin U ≤
        LinearMap.BilinForm.orthogonal (quadMinus 3 F b c).polarBilin
          (CFSG.RankThree.OrthogonalInvolutions.commSpace
            (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F g)) :=
      LinearMap.BilinForm.orthogonal_le (hcommU g hg)
    have hu' : u ∈ CFSG.RankThree.OrthogonalInvolutions.fixSpace
        (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F g) := by
      rw [hfixeq]
      exact hanti (hUorth hu)
    exact CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mp hu'
  have hdim : Module.finrank F U ≤ 2 := by
    have h := CFSG.StandardType.OrdPOm.finrank_le_of_singular_quadMinus (n := 3) hirr
      (by omega) U hUQ
    simpa using h
  have hEp : IsPGroup 2 ↥E := isPGroup_two_of_sq_eq_one (fun g => by
    apply Subtype.ext
    show (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) ^ 2 = 1
    simpa [pow_two] using hE2 g g.2)
  have hcardE : Nat.card ↥E = 2 ^ rk ↥E := card_eq_two_pow_of_isPGroup hEp
  rcases Nat.eq_zero_or_pos (Module.finrank F U) with h0 | hpos
  · have hUbot : U = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hEbot : E = ⊥ := by
      ext g
      constructor
      · intro hg
        have hg1 : g = 1 := by
          apply gl_ext
          intro v
          rw [gv_one]
          have h : gv g v - v ∈ U := hTsub (hTcomm g hg v)
          rw [hUbot, Submodule.mem_bot] at h
          exact sub_eq_zero.mp h
        rw [hg1]
        exact Subgroup.one_mem ⊥
      · intro hg
        rw [Subgroup.mem_bot] at hg
        rw [hg]
        exact Subgroup.one_mem E
    have hcard1 : Nat.card ↥E = 1 := by rw [hEbot]; simp
    rw [hcardE] at hcard1
    have hz : rk ↥E = 0 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) (by simpa using hcard1)
    omega
  · have h12 : Module.finrank F U = 1 ∨ Module.finrank F U = 2 := by omega
    rcases h12 with h1 | h2
    · obtain ⟨w, hwU, hw0⟩ : ∃ w ∈ U, w ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have hUbot : U = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro x hx
          exact hcon x hx
        rw [hUbot] at h1
        simp at h1
      have hUw : U = Submodule.span F {w} :=
        eq_span_singleton_of_mem_of_finrank_eq_one h1 hwU hw0
      have hEbot : E = ⊥ := by
        ext g
        constructor
        · intro hg
          have hg1 : g = 1 := by
            apply gl_ext
            intro v
            rw [gv_one]
            by_contra hne
            have hmem : gv g v - v ∈ Submodule.span F {w} := by
              rw [← hUw]
              exact hTsub (hTcomm g hg v)
            obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
            have hiso : ∀ x : OW F,
                StatedQuadMinus 3 F b c
                  ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
                    (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
                StatedQuadMinus 3 F b c x := by
              intro x
              simpa only [← quadMinus_eq_stated] using
                quadMinus_mulVec_of_mem_statedOmega (hEΩ hg) x
            have hu : ∀ x : OW F, ∃ r : F,
                ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
                  (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) - 1) *ᵥ x = r • w := by
              intro x
              have hx : gv g x - x ∈ Submodule.span F {w} := by
                rw [← hUw]
                exact hTsub (hTcomm g hg x)
              obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
              exact ⟨r, by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; exact hr.symm⟩
            have htrans := transvection_quad hirr
              (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
                (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) hiso w hu
            have hx0 : ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
                (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) - 1) *ᵥ v ≠ 0 := by
              rw [Matrix.sub_mulVec, Matrix.one_mulVec]
              exact sub_ne_zero.mpr hne
            have hQne := htrans v hx0
            have hQ0 : quadMinus 3 F b c (gv g v - v) = 0 :=
              hUQ _ (hTsub (hTcomm g hg v))
            rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← quadMinus_eq_stated] at hQne
            exact hQne hQ0
          rw [hg1]
          exact Subgroup.one_mem ⊥
        · intro hg
          rw [Subgroup.mem_bot] at hg
          rw [hg]
          exact Subgroup.one_mem E
      have hcard1 : Nat.card ↥E = 1 := by rw [hEbot]; simp
      rw [hcardE] at hcard1
      have hz : rk ↥E = 0 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) (by simpa using hcard1)
      omega
    · obtain ⟨x, hxiso, hxU, hconj⟩ :=
        exists_conj_le_radGrp_of_fixes_singular_plane_std hirr hEΩ hE2 h2 hUs hfixU
      have hnstd : ∀ (k : Fin 2) (v : OW F), v ∈ radStdPlane F → v (Sum.inr (Sum.inr k)) = 0 := by
        intro k v hv
        induction hv using Submodule.span_induction with
        | mem v hv =>
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
            rcases hv with rfl | rfl <;> simp [eV]
        | zero => simp
        | add a b _ _ ha hb => simp [Pi.add_apply, ha, hb]
        | smul c a _ ha => simp [Pi.smul_apply, ha]
      have hdiff : ∀ (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) (i : Fin (3 - 1)),
          g ∈ E → gv (x * g * x⁻¹) (fV F i) - fV F i ∈ radStdPlane F := by
        intro g i hg
        have hw : gv g (gv x⁻¹ (fV F i)) - gv x⁻¹ (fV F i) ∈ U :=
          hTsub (hTcomm g hg (gv x⁻¹ (fV F i)))
        have hxw := hxU _ hw
        have e : gv (x * g * x⁻¹) (fV F i) - fV F i =
            gv x (gv g (gv x⁻¹ (fV F i)) - gv x⁻¹ (fV F i)) := by
          rw [gv_mul, gv_mul, gv_sub, gv_gv_inv]
        rw [e]
        exact hxw
      have hinj : Function.Injective (fun g : ↥E =>
          gv (x * (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) * x⁻¹)
            (fV F idx0) (Sum.inl idx1)) := by
        intro g1 g2 hs
        apply Subtype.ext
        have hrad1 : RadHyp b c
            (x * (g1 : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) * x⁻¹) :=
          mem_RadGrp.mp (hconj g1 g1.2)
        have hrad2 : RadHyp b c
            (x * (g2 : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) * x⁻¹) :=
          mem_RadGrp.mp (hconj g2 g2.2)
        have hm : ∀ (i : Fin (3 - 1)) (k : Fin 2),
            gv (x * (g1 : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) * x⁻¹)
              (fV F i) (Sum.inr (Sum.inr k)) =
            gv (x * (g2 : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) * x⁻¹)
              (fV F i) (Sum.inr (Sum.inr k)) := by
          intro i k
          have h1 := hnstd k _ (hdiff g1 i g1.2)
          have h2 := hnstd k _ (hdiff g2 i g2.2)
          have hf : fV F i (Sum.inr (Sum.inr k)) = 0 := by simp [fV]
          simp only [Pi.sub_apply, hf, sub_zero] at h1 h2
          rw [h1, h2]
        have heq := OutLin.RadHyp.ext_params (F := F) (b := b) (c := c)
          (g := x * (g1 : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) * x⁻¹)
          (g' := x * (g2 : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) * x⁻¹)
          hrad1 hrad2 hm hs
        exact mul_left_cancel (mul_right_cancel heq)
      have hcardle : Nat.card ↥E ≤ Nat.card F := Nat.card_le_card_of_injective _ hinj
      have hpow : 2 ^ rk ↥E ≤ 2 ^ n := by
        rw [← hcardE, ← hF]
        exact hcardle
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow

theorem k_Omega6Minus_singComm_rank :
    ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ) (F : Type) [Field F]
      [Finite F] (b c : F), 2 ≤ n → Nat.card F = 2 ^ n → (∀ s : F, s ^ 2 + b * s + c ≠ 0) →
      ∀ (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
        (ψ : ↥(⊤ : Subgroup W) ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
        NatCoordsOmegaMinusOn H ⊤ (fun _ _ s _ => Subgroup.mem_top s) F b c ε ψ →
        ∀ E : Subgroup (MulAut W), E ≤ H → IsElemAbelian2 E →
          (∀ w ∈ commSub ⊤ E,
            StatedQuadMinus 3 F b c (Multiplicative.toAdd (ψ ⟨w, Subgroup.mem_top w⟩)) = 0) →
            rk ↥E ≤ n := by
  intro W _ _ H n F _ _ b c hn hF hbc ε ψ hψ E hEH hE hcomm
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  let φ : ↥H →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F :=
    (StatedOmega (StatedQuadMinus 3 F b c)).subtype.comp ε.toMonoidHom
  let E₁ : Subgroup ↥H := (⊤ : Subgroup ↥E).map (Subgroup.inclusion hEH)
  let E' : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) := E₁.map φ
  have hE'Ω : E' ≤ StatedOmega (StatedQuadMinus 3 F b c) := by
    rintro _ ⟨l, -, rfl⟩
    exact (ε l).2
  have hE'2 : ∀ g ∈ E', g * g = 1 := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hl
    rw [← map_mul, ← map_one φ]
    congr 1
    rw [← map_mul, ← map_one (Subgroup.inclusion hEH)]
    congr 1
    apply Subtype.ext
    simpa [pow_two] using hE.2 e e.2
  let T : Set (OW F) :=
    (fun w : W => Multiplicative.toAdd (ψ ⟨w, Subgroup.mem_top w⟩)) ''
      (commSub ⊤ E : Set W)
  have hTQ : ∀ v ∈ T, StatedQuadMinus 3 F b c v = 0 := by
    rintro v ⟨w, hw, rfl⟩
    exact hcomm w hw
  have hTadd : ∀ u ∈ T, ∀ v ∈ T, u + v ∈ T := by
    rintro u ⟨a, ha, rfl⟩ v ⟨b, hb, rfl⟩
    refine ⟨a * b, (commSub ⊤ E).mul_mem ha hb, ?_⟩
    change Multiplicative.toAdd (ψ ⟨a * b, Subgroup.mem_top _⟩) =
      Multiplicative.toAdd (ψ ⟨a, Subgroup.mem_top _⟩) +
        Multiplicative.toAdd (ψ ⟨b, Subgroup.mem_top _⟩)
    rw [show (⟨a * b, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
        ⟨a, Subgroup.mem_top _⟩ * ⟨b, Subgroup.mem_top _⟩ from rfl,
      map_mul, toAdd_mul]
  have hTcomm : ∀ g ∈ E', ∀ v : OW F, gv g v - v ∈ T := by
    rintro _ ⟨l, hl, rfl⟩ v
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hl
    let w : ↥(⊤ : Subgroup W) := ψ.symm (Multiplicative.ofAdd v)
    have hwv : Multiplicative.toAdd (ψ w) = v := by simp [w]
    have hψe : ψ ⟨(e : MulAut W) w.1, Subgroup.mem_top _⟩ =
        Multiplicative.ofAdd (gv (φ (Subgroup.inclusion hEH e)) v) := by
      have h := hψ ⟨e, hEH e.2⟩ w
      rw [hwv] at h
      exact h
    refine ⟨(e : MulAut W) w.1 * w.1⁻¹,
      Subgroup.subset_closure ⟨e, e.2, w.1, Subgroup.mem_top _, rfl⟩, ?_⟩
    change Multiplicative.toAdd (ψ ⟨(e : MulAut W) w.1 * w.1⁻¹, Subgroup.mem_top _⟩) =
      gv (φ (Subgroup.inclusion hEH e)) v - v
    rw [show (⟨(e : MulAut W) w.1 * w.1⁻¹, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
        ⟨(e : MulAut W) w.1, Subgroup.mem_top _⟩ * ⟨w.1, Subgroup.mem_top _⟩⁻¹ from rfl,
      map_mul, map_inv, toAdd_mul, toAdd_inv, hψe]
    rw [sub_eq_add_neg]
    change Multiplicative.toAdd (Multiplicative.ofAdd (gv (φ (Subgroup.inclusion hEH e)) v)) +
      -Multiplicative.toAdd (ψ w) = gv (φ (Subgroup.inclusion hEH e)) v + -v
    rw [toAdd_ofAdd, hwv]
  have hφinj : Function.Injective φ := by
    intro a b h
    exact ε.injective (Subtype.ext h)
  have hcardE' : Nat.card ↥E' = Nat.card ↥E := by
    rw [Subgroup.card_map_of_injective hφinj]
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hEH)]
    simp
  have hrk : rk ↥E' = rk ↥E := by
    unfold CFSG.Quasithin.rk
    rw [hcardE']
  rw [← hrk]
  exact rk_le_of_singComm hbc hn hF hE'Ω hE'2 hTQ hTadd hTcomm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
