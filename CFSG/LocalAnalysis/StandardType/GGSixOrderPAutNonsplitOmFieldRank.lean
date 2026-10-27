module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmFieldFrame

public section

namespace CFSG.StandardType

namespace OrdPFieldNsOm

open QuadraticMap Module OrdPNsOm SUTB NoOffOm OrdPNsGen
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Compare

variable {K K₀ : Type} [Field K] [Finite K] [CharP K 2] [Field K₀] [Finite K₀] [CharP K₀ 2]
  {n : ℕ} {Q : QuadraticForm K (Fin (2 * n) → K)} {Q₀ : QuadraticForm K₀ (Fin (2 * n) → K₀)}
  {p : ℕ}

theorem card_le_card_of_genMax_field (ι : K₀ →+* K) (κ : (Fin (2 * n) → K₀) →+ (Fin (2 * n) → K))
    (hκ : ∀ v, Q (κ v) = ι (Q₀ v))
    (hT₀ : ∃ T : Submodule K₀ (Fin (2 * n) → K₀), finrank K₀ T = 3 ∧ ∀ x ∈ T, Q₀ x = 0)
    (hwp : ∀ c : K₀, c ∉ (wp K₀).range → ι c ∉ (wp K).range)
    (hq : (Nat.card K : ℤ) ≡ Nat.card K₀ [ZMOD p]) (hord : OrdPNS.ordQ K₀ p = OrdPNS.ordQ K p)
    {A : Subgroup (GL (Fin (2 * n)) K)} (hA : GenMax (polB Q) (matrixDerived Q) p A)
    {E : Subgroup (GL (Fin (2 * n)) K₀)} (hE : GenMax (polB Q₀) (matrixDerived Q₀) p E)
    (hE1 : ∃ x ∈ E, x ≠ 1) : Nat.card A ≤ Nat.card E := by
  classical
  have hp := hA.prime
  have hp2 := hA.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hnd := nondegenerate_of_genMax hA
  have hnd₀ := nondegenerate_of_genMax hE
  obtain ⟨SA, hSA, htA⟩ := exists_terminal_genPieceSet hA
  obtain ⟨SE, hSE, htE⟩ := exists_terminal_genPieceSet hE
  rw [card_eq_pow_of_terminal hA hSA htA, card_eq_pow_of_terminal hE hSE htE]
  refine Nat.pow_le_pow_right hp.pos ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨m, hm⟩ := exists_lcm_eq (K := K) hp hA.natCast_ne_zero
  have hm₀ : Nat.lcm 2 (OrdPNS.ordQ K₀ p) = 2 * m + 2 := by rw [hord, hm]
  set yA : Fin SA.card → GL (Fin (2 * n)) K := fun j => (SA.equivFin.symm j : GL (Fin (2 * n)) K)
    with hyA
  set yE : Fin SE.card → GL (Fin (2 * n)) K₀ :=
    fun j => (SE.equivFin.symm j : GL (Fin (2 * n)) K₀) with hyE
  have hyAS : ∀ j, yA j ∈ SA := fun j => (SA.equivFin.symm j).2
  have hyES : ∀ j, yE j ∈ SE := fun j => (SE.equivFin.symm j).2
  have hyAinj : Function.Injective yA := fun i j h =>
    SA.equivFin.symm.injective (Subtype.ext h)
  have hyEinj : Function.Injective yE := fun i j h =>
    SE.equivFin.symm.injective (Subtype.ext h)
  have hyAA : ∀ j, yA j ∈ A := fun j => hSA.mem _ (hyAS j)
  have hyEE : ∀ j, yE j ∈ E := fun j => hSE.mem _ (hyES j)
  have hdimA : ∀ j, finrank K (grng (yA j)) = 2 * m + 2 := fun j => by
    rw [finrank_grng_eq_lcm polB_self hA hSA (hyAS j), hm]
  have hdimE : ∀ j, finrank K₀ (grng (yE j)) = 2 * m + 2 := fun j => by
    rw [finrank_grng_eq_lcm polB_self hE hSE (hyES j), hm₀]
  have hSE0 : 0 < SE.card := by
    rw [Finset.card_pos]
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    obtain ⟨x, hx, hx1⟩ := hE1
    refine hx1 (htE x hx fun v hv => ?_)
    have h1 : genPieceSpan SE = ⊥ := by rw [h0]; simp
    rw [h1, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  set i₀ : Fin SE.card := ⟨0, hSE0⟩ with hi₀
  obtain ⟨c₀, hc₀⟩ := exists_not_mem_range_wp (K := K₀)
  have hc₀' := hwp c₀ hc₀
  obtain ⟨τ, -, -, -, -, -, -, hS₀⟩ := exists_frame (Q := Q₀) hc₀ m (grng (yE i₀))
    (nondegOn_grng hE (hyEE i₀)) (hdimE i₀)
  have hτ₀ : (Nat.card K₀ : ℤ) ^ m * tailSum K₀ τ ≡ 1 [ZMOD p] :=
    hS₀ ▸ charSum_grng_modEq hE (hyEE i₀)
  have hτ : (Nat.card K : ℤ) ^ m * tailSum K τ ≡ 1 [ZMOD p] := by
    refine Int.ModEq.trans ?_ hτ₀
    cases τ
    · simp only [tailSum, Bool.false_eq_true, ite_false]
      exact (hq.pow m).mul hq
    · simp only [tailSum, ite_true]
      exact (hq.pow m).mul hq.neg
  have hfrA : ∀ j, ∃ (e f : Fin m → Fin (2 * n) → K) (a b : Fin (2 * n) → K),
      (∀ x, fvec e f a b x ∈ grng (yA j)) ∧ IsFrame Q (ι c₀) τ e f a b := fun j =>
    exists_frame_of_modEq hc₀' hp hp2 hτ (nondegOn_grng hA (hyAA j)) (hdimA j)
      (charSum_grng_modEq hA (hyAA j))
  have hfrE : ∀ j, ∃ (e f : Fin m → Fin (2 * n) → K₀) (a b : Fin (2 * n) → K₀),
      (∀ x, fvec e f a b x ∈ grng (yE j)) ∧ IsFrame Q₀ c₀ τ e f a b := fun j =>
    exists_frame_of_modEq hc₀ hp hp2 hτ₀ (nondegOn_grng hE (hyEE j)) (hdimE j)
      (charSum_grng_modEq hE (hyEE j))
  choose eA fA aA bA hmA hFA using hfrA
  choose eE fE aE bE hmE hFE using hfrE
  have horthA : ∀ j j', j ≠ j' → ∀ u ∈ grng (yA j), ∀ v ∈ grng (yA j'), polar Q u v = 0 :=
    fun j j' hjj' => hSA.orth _ (hyAS j) _ (hyAS j') fun h => hjj' (hyAinj h)
  have horthE : ∀ j j', j ≠ j' → ∀ u ∈ grng (yE j), ∀ v ∈ grng (yE j'), polar Q₀ u v = 0 :=
    fun j j' hjj' => hSE.orth _ (hyES j) _ (hyES j') fun h => hjj' (hyEinj h)
  have hspanA : ∀ j, Submodule.span K (Set.range (fvec (eA j) (fA j) (aA j) (bA j))) =
      grng (yA j) := fun j => (hFA j).span_eq (hmA j) (hdimA j)
  have hspanE : ∀ j, Submodule.span K₀ (Set.range (fvec (eE j) (fE j) (aE j) (bE j))) =
      grng (yE j) := fun j => (hFE j).span_eq (hmE j) (hdimE j)
  set ιc : Fin SE.card → Fin SA.card := Fin.castLE hlt.le with hιc
  obtain ⟨g, hg, hgF⟩ := exists_orth_frames (Q := Q) hnd
    (e := fun j => κ ∘ eE j) (f := fun j => κ ∘ fE j) (a := fun j => κ (aE j))
    (b := fun j => κ (bE j)) (e' := fun j => eA (ιc j)) (f' := fun j => fA (ιc j))
    (a' := fun j => aA (ιc j)) (b' := fun j => bA (ιc j))
    (fun j => isFrame_map ι κ hκ (hFE j)) (fun j => hFA (ιc j))
    (fun j j' hjj' x y => by
      rw [fvec_map, fvec_map, polar_map ι κ hκ, horthE j j' hjj' _ (hmE j x) _ (hmE j' y),
        map_zero])
    (fun j j' hjj' x y => horthA (ιc j) (ιc j') (fun h => hjj' (Fin.castLE_injective _ h)) _
      (hmA _ x) _ (hmA _ y))
  have hgQ : ∀ v, Q (g v) = Q v := fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg v
  have hgpol : ∀ u v, polar Q (g u) (g v) = polar Q u v := fun u v => by
    change Q (g u + g v) - Q (g u) - Q (g v) = Q (u + v) - Q u - Q v
    rw [← map_add, hgQ, hgQ, hgQ]
  have hgκ : ∀ j x, g (κ (fvec (eE j) (fE j) (aE j) (bE j) x)) =
      fvec (eA (ιc j)) (fA (ιc j)) (aA (ιc j)) (bA (ιc j)) x := fun j x => by
    rw [← fvec_map]
    exact hgF j x
  set X₀ := genPieceSpan SE with hX₀
  have hX₀nd : NondegOn (polB Q₀) X₀ := (hSE.nondegOn_card hE).1
  set W₀ := X₀.orthogonalBilin (polB Q₀) with hW₀
  have hW₀nd : NondegOn (polB Q₀) W₀ := nondegOn_orth' hE.symm hE.sep hX₀nd
  have hfrX₀ : finrank K₀ X₀ = SE.card * (2 * m + 2) :=
    finrank_genPieceSpan hE hSE fun y hy => by rw [finrank_grng_eq_lcm polB_self hE hSE hy, hm₀]
  have hfrW₀ : finrank K₀ X₀ + finrank K₀ W₀ = 2 * n := finrank_add_finrank_orth hX₀nd
  have hfrXA : finrank K (genPieceSpan SA) = SA.card * (2 * m + 2) :=
    finrank_genPieceSpan hA hSA fun y hy => by rw [finrank_grng_eq_lcm polB_self hA hSA hy, hm]
  have hdA : SA.card * (2 * m + 2) ≤ 2 * n := by
    rw [← hfrXA]
    exact (Submodule.finrank_le _).trans (Module.finrank_fin_fun K).le
  have hkey : SE.card * (m + 1) + (m + 1) ≤ SA.card * (m + 1) := by
    have h1 := Nat.mul_le_mul_right (m + 1) (Nat.succ_le_of_lt hlt)
    rwa [Nat.succ_mul] at h1
  have hX₀' : finrank K₀ X₀ = 2 * (SE.card * (m + 1)) := by rw [hfrX₀]; ring
  have hdA' : 2 * (SA.card * (m + 1)) ≤ 2 * n := by
    rw [show 2 * (SA.card * (m + 1)) = SA.card * (2 * m + 2) by ring]
    exact hdA
  have hXA' : finrank K (genPieceSpan SA) = 2 * (SA.card * (m + 1)) := by rw [hfrXA]; ring
  obtain ⟨m', hm', hmm'⟩ : ∃ m', finrank K₀ W₀ = 2 * m' + 2 ∧ m ≤ m' :=
    ⟨n - SE.card * (m + 1) - 1, by omega, by omega⟩
  have hW₀frame : ∃ (e' f' : Fin m → Fin (2 * n) → K₀) (a' b' : Fin (2 * n) → K₀),
      (∀ x, fvec e' f' a' b' x ∈ W₀) ∧ IsFrame Q₀ c₀ τ e' f' a' b' := by
    rcases Nat.eq_or_lt_of_le hmm' with hmeq | hmlt
    ·
      rw [← hmeq] at hm'
      obtain ⟨τW, eW, fW, aW, bW, hmW, hFW, -⟩ := exists_frame (Q := Q₀) hc₀ m W₀ hW₀nd hm'
      suffices hτW : τW = τ by
        subst hτW
        exact ⟨eW, fW, aW, bW, hmW, hFW⟩
      have hSAc : SA.card * (m + 1) = SE.card * (m + 1) + (m + 1) := by omega
      have hXA : genPieceSpan SA = ⊤ := Submodule.eq_top_of_finrank_eq (by
        rw [hXA', Module.finrank_fin_fun]
        omega)
      have hcard : SA.card = SE.card + 1 := by
        have h1 : SA.card * (m + 1) = (SE.card + 1) * (m + 1) := by rw [hSAc]; ring
        exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) h1
      set j₀ : Fin SA.card := ⟨SE.card, hlt⟩ with hj₀
      set y₀ := yA j₀ with hy₀
      have hy₀S : y₀ ∈ SA := hyAS j₀
      set P := grng y₀ with hP
      have hPnd : NondegOn (polB Q) P := nondegOn_grng hA (hyAA j₀)
      have hother : ∀ y ∈ SA.erase y₀, ∃ i, yA (ιc i) = y := by
        intro y hy
        obtain ⟨hyy₀, hyS⟩ := Finset.mem_erase.mp hy
        set j := SA.equivFin ⟨y, hyS⟩ with hj
        have hjy : yA j = y := by simp [hyA, hj]
        have hjne : j.val ≠ SE.card := fun h => hyy₀ (by rw [← hjy, hy₀]; congr 1; exact Fin.ext h)
        have hjlt : j.val < SE.card := by have := j.2; omega
        exact ⟨⟨j.val, hjlt⟩, by rw [← hjy]; congr 1⟩
      have hv : ∀ x, ∀ u ∈ genPieceSpan (SA.erase y₀),
          polar Q (g (κ (fvec eW fW aW bW x))) u = 0 := by
        intro x u hu
        have hle : genPieceSpan (SA.erase y₀) ≤
            LinearMap.ker (polarBilin Q (g (κ (fvec eW fW aW bW x)))) := by
          refine iSup₂_le fun y hy => ?_
          obtain ⟨i, rfl⟩ := hother y hy
          rw [← hspanA (ιc i), Submodule.span_le]
          rintro _ ⟨z, rfl⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply, ← hgκ i z, hgpol,
            polar_map ι κ hκ]
          have h1 : fvec (eE i) (fE i) (aE i) (bE i) z ∈ X₀ :=
            (le_iSup₂ (f := fun y (_ : y ∈ SE) => grng y) _ (hyES i)) (hmE i z)
          have h2 := (Submodule.mem_orthogonalBilin.mp (hmW x)) _ h1
          rw [polar_comm]
          change ι (polB Q₀ _ _) = 0
          rw [show polB Q₀ (fvec (eE i) (fE i) (aE i) (bE i) z) (fvec eW fW aW bW x) = 0 from h2,
            map_zero]
        exact hle hu
      have hsplit : genPieceSpan SA = genPieceSpan (SA.erase y₀) ⊔ P := by
        conv_lhs => rw [← Finset.insert_erase hy₀S]
        rw [genPieceSpan, Finset.iSup_insert, sup_comm]
      have horthP := orth_genPieceSpan hA.symm (S := SA.erase y₀) (y := y₀)
        (by rw [Finset.insert_erase hy₀S]; exact hSA) (Finset.notMem_erase _ _)
      have hPperp : P.orthogonalBilin (polB Q) ≤ genPieceSpan (SA.erase y₀) := by
        intro z hz
        have hz' : z ∈ genPieceSpan (SA.erase y₀) ⊔ P := by rw [← hsplit, hXA]; trivial
        obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hz'
        have hw0 : w = 0 := hPnd w hw fun n hn => by
          have h1 : polB Q n (u + w) = 0 := (Submodule.mem_orthogonalBilin.mp hz) n hn
          have h2 : polB Q n u = 0 := (horthP n hn u hu).1
          rw [map_add, h2, zero_add] at h1
          exact h1
        rw [hw0, add_zero]
        exact hu
      have hvP : ∀ x, g (κ (fvec eW fW aW bW x)) ∈ P := by
        intro x
        obtain ⟨mm, hmm, zz, hzz, hmz⟩ := exists_add_orth hPnd (g (κ (fvec eW fW aW bW x)))
        have hzz0 : zz = 0 := by
          refine nondegOn_orth' hA.symm hA.sep hPnd zz hzz fun n hn => ?_
          have h1 : polB Q n (g (κ (fvec eW fW aW bW x))) = 0 := by
            rw [polB_apply, polar_comm]
            exact hv x n (hPperp hn)
          have h2 : polB Q n mm = 0 := by
            have h3 : polB Q mm n = 0 := (Submodule.mem_orthogonalBilin.mp hn) mm hmm
            rw [polB_apply, polar_comm, ← polB_apply]
            exact h3
          have h4 : zz = g (κ (fvec eW fW aW bW x)) - mm := by rw [← hmz]; abel
          rw [h4, map_sub, h1, h2, sub_zero]
        rw [← hmz, hzz0, add_zero]
        exact hmm
      have hFP : IsFrame Q (ι c₀) τW (g ∘ (κ ∘ eW)) (g ∘ (κ ∘ fW)) (g (κ aW)) (g (κ bW)) :=
        isFrame_map (RingHom.id K) g.toLinearMap.toAddMonoidHom (fun v => hgQ v)
          (isFrame_map ι κ hκ hFW)
      have hmP : ∀ x, fvec (g ∘ (κ ∘ eW)) (g ∘ (κ ∘ fW)) (g (κ aW)) (g (κ bW)) x ∈ P := by
        intro x
        rw [show fvec (g ∘ (κ ∘ eW)) (g ∘ (κ ∘ fW)) (g (κ aW)) (g (κ bW)) x =
          g (κ (fvec eW fW aW bW x)) from by rcases x with i | i | j <;> [rfl; rfl; fin_cases j <;> rfl]]
        exact hvP x
      have hcs := charSum_span_frame hc₀' hFP
      rw [hFP.span_eq hmP (hdimA j₀)] at hcs
      have hmod := charSum_grng_modEq hA (hyAA j₀)
      rw [← hP, hcs] at hmod
      exact tau_eq_of_modEq hp hp2 hmod hτ
    ·
      obtain ⟨τW, eW, fW, aW, bW, hmW, hFW, -⟩ := exists_frame (Q := Q₀) hc₀ m' W₀ hW₀nd hm'
      have hle : m + 1 ≤ m' := hmlt
      obtain ⟨a', b', ha', hb', hF'⟩ := exists_frame_castSucc (isFrame_castLE hFW hle) τ
        (U := W₀) (fvec_comp_mem _ hmW)
      refine ⟨_, _, a', b', fun x => ?_, hF'⟩
      rcases x with i | i | j
      · exact hmW (.inl _)
      · exact hmW (.inr (.inl _))
      · fin_cases j
        · exact ha'
        · exact hb'
  obtain ⟨e', f', a', b', hm'W, hF'⟩ := hW₀frame
  obtain ⟨h, hh, hhF⟩ := exists_orth_frames (Q := Q₀) hnd₀ (k := 1)
    (e := fun _ => eE i₀) (f := fun _ => fE i₀) (a := fun _ => aE i₀) (b := fun _ => bE i₀)
    (e' := fun _ => e') (f' := fun _ => f') (a' := fun _ => a') (b' := fun _ => b')
    (fun _ => hFE i₀) (fun _ => hF') (fun j j' hjj' => absurd (Subsingleton.elim j j') hjj')
    (fun j j' hjj' => absurd (Subsingleton.elim j j') hjj')
  set H : GL (Fin (2 * n)) K₀ := matrixLinearIso.symm h with hH
  have hHh : matrixLinearIso H = h := MulEquiv.apply_symm_apply _ _
  have hHv : ∀ v, glin H v = h v := fun v => by
    rw [glin_apply, ← hHh]
    rfl
  have hHiso : H ∈ matrixIsometries Q₀ := by
    change matrixLinearIso.toMonoidHom H ∈ TauCeti.QuadraticMap.orthogonalGroup Q₀
    rw [MulEquiv.coe_toMonoidHom, hHh]
    exact hh
  have hUW : ∀ u ∈ grng (yE i₀), h u ∈ W₀ := by
    intro u hu
    rw [← hspanE i₀] at hu
    have hle : Submodule.span K₀ (Set.range (fvec (eE i₀) (fE i₀) (aE i₀) (bE i₀))) ≤
        W₀.comap h.toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      change h _ ∈ W₀
      rw [hhF 0 x]
      exact hm'W x
    exact hle hu
  have hy₁ := hyEE i₀
  obtain ⟨b₁, hb₁E, hb₁on, hb₁off⟩ := hE.exists_mem_restrict (nondegOn_grng hE hy₁)
    (fun a ha => grng_inv hE hy₁ ha) hy₁
  have hb₁1 : b₁ ≠ 1 := by
    intro hb
    obtain ⟨u, hu, hu0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (grng_ne_bot (hSE.ne_one _ (hyES i₀)))
    have h1 := hb₁on u hu
    rw [hb, glin_one, Module.End.one_apply] at h1
    exact hu0 (eq_zero_of_mem_grng hE hy₁ hu h1.symm)
  set z : GL (Fin (2 * n)) K₀ := H * b₁ * H⁻¹ with hz
  have hzlin : ∀ v, glin z v = glin H (glin b₁ (glin H⁻¹ v)) := fun v => by
    rw [hz, glin_mul, glin_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hb₁iso : b₁ ∈ matrixIsometries Q₀ := matrixDerived_le_isometries Q₀ (hE.le hb₁E)
  have hziso : z ∈ matrixIsometries Q₀ :=
    (matrixIsometries Q₀).mul_mem ((matrixIsometries Q₀).mul_mem hHiso hb₁iso)
      ((matrixIsometries Q₀).inv_mem hHiso)
  have hzp : z ^ p = 1 := by
    rw [hz, conj_pow, hE.pow b₁ hb₁E, mul_one, mul_inv_cancel]
  have hz1 : z ≠ 1 := by
    intro h1
    apply hb₁1
    have h2 : b₁ = H⁻¹ * z * H := by rw [hz]; group
    rw [h2, h1, mul_one, inv_mul_cancel]
  have hzodd : Odd (orderOf z) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hzp)
  have hzΓ : z ∈ matrixDerived Q₀ :=
    CFSG.ComponentClassification.HarrisLit.T1.P58b3D4.mem_matrixDerived_of_odd hnd₀ hT₀ hziso
      hzodd
  have hzX : ∀ v ∈ X₀, glin z v = v := by
    intro v hv
    have e1 : glin H (glin H⁻¹ v) = v := by
      have h2 := glin_inv_apply H⁻¹ v
      rwa [inv_inv] at h2
    have h1 : glin H⁻¹ v ∈ (grng (yE i₀)).orthogonalBilin (polB Q₀) := by
      refine Submodule.mem_orthogonalBilin.mpr fun u hu => ?_
      change polB Q₀ u (glin H⁻¹ v) = 0
      calc polB Q₀ u (glin H⁻¹ v) = polB Q₀ (glin H u) (glin H (glin H⁻¹ v)) :=
            (polB_glin_of_mem_isometries hHiso u _).symm
        _ = polB Q₀ (h u) v := by rw [e1, hHv]
        _ = 0 := by
          have h2 : polB Q₀ v (h u) = 0 := (Submodule.mem_orthogonalBilin.mp (hUW u hu)) v hv
          rw [polB_apply, polar_comm, ← polB_apply]
          exact h2
    rw [hzlin, hb₁off _ h1, e1]
  have hXE : ∀ c ∈ E, ∀ v ∈ X₀, glin c v ∈ X₀ := by
    intro c hc v hv
    have hle' : X₀ ≤ X₀.comap (glin c) := by
      refine iSup₂_le fun y hy u hu => ?_
      exact (le_iSup₂ (f := fun y (_ : y ∈ SE) => grng y) y hy)
        (grng_inv hE (hSE.mem y hy) hc u hu)
    exact hle' hv
  have hcomm : ∀ c ∈ E, z * c = c * z := by
    intro c hc
    apply glin_injective
    rw [glin_mul z c, glin_mul c z]
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, hx, w, hw, rfl⟩ := exists_add_orth hX₀nd v
    have hcw : glin c w = w := triv_orth_genPieceSpan hE hSE htE hc w hw
    have hzw : glin z w ∈ W₀ := by
      refine Submodule.mem_orthogonalBilin.mpr fun n hn => ?_
      change polB Q₀ n (glin z w) = 0
      rw [← hzX n hn, polB_glin_of_mem_isometries hziso]
      exact (Submodule.mem_orthogonalBilin.mp hw) n hn
    have hczw : glin c (glin z w) = glin z w := triv_orth_genPieceSpan hE hSE htE hc _ hzw
    simp only [Module.End.mul_apply, map_add]
    rw [hcw, hzX _ (hXE c hc x hx), hzX x hx, hczw]
  exact hz1 (htE z (hE.max z hzΓ hzp hcomm) hzX)

end Compare

end OrdPFieldNsOm

end CFSG.StandardType
