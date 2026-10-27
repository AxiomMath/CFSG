module

public import CFSG.LocalAnalysis.StandardType.GGD5Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private lemma lup10ab_tw_C_cast (i j : Fin 5) :
    (Int.cast (CartanMatrix.D 5 (lup10ab_tau i) (lup10ab_tau j)) : ZMod 3) = lup10fa_C i j := by
  fin_cases i <;> fin_cases j <;> rfl

private lemma lup10ab_tw_C_zero_or_two :
    ∀ a b : Fin 4, a ≠ b →
      lup10fa_C a.castSucc b.castSucc = 0 ∨ lup10fa_C a.castSucc b.castSucc = 2 := by
  decide

private lemma lup10ab_tw_C_center :
    ∀ a : Fin 4, (∀ b : Fin 4, b ≠ a → lup10fa_C a.castSucc b.castSucc ≠ 0) → a = 1 := by
  decide

private lemma lup10ab_tw_C_10 : lup10fa_C (1 : Fin 4).castSucc (0 : Fin 4).castSucc = 2 := by
  decide

private lemma lup10ab_tw_C_12 : lup10fa_C (1 : Fin 4).castSucc (2 : Fin 4).castSucc = 2 := by
  decide

private lemma lup10ab_tw_C_13 : lup10fa_C (1 : Fin 4).castSucc (3 : Fin 4).castSucc = 2 := by
  decide

private lemma lup10ab_tw_x_castSucc (j : Fin 4) :
    lup10fa_x j.castSucc = (![1, 2, 1, 2] : Fin 4 → ZMod 3) j := by
  fin_cases j <;> rfl

private lemma lup10ab_tw_single (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3) (j : Fin 4) :
    (lup10fa_twist γ lam c).mulVec (Pi.single j.castSucc (1 : ZMod 3)) =
      c • Pi.single (γ j).castSucc 1 := by
  funext r
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j.castSucc]
  · rw [Pi.single_eq_same, mul_one, Pi.smul_apply]
    by_cases h : (γ j).castSucc = r
    · subst h
      simp [lup10fa_twist]
    · have h' : (γ j).val ≠ r.val := fun hv => h (Fin.ext hv)
      rw [Pi.single_apply, if_neg (Ne.symm h)]
      simp [lup10fa_twist, j.isLt, h']
  · intro k _ hk
    rw [Pi.single_apply, if_neg hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma lup10ab_tw_sum_col (γ : Equiv.Perm (Fin 4)) (c : ZMod 3) (r : Fin 4) :
    (∑ k : Fin 4,
        (if (γ k).val = r.val then c else 0) *
          (![1, 2, 1, 2] : Fin 4 → ZMod 3) k) =
      c * (![1, 2, 1, 2] : Fin 4 → ZMod 3) (γ.symm r) := by
  rw [Finset.sum_eq_single (γ.symm r)]
  · rw [Equiv.apply_symm_apply]
    simp
  · intro k _ hk
    have hne : (γ k).val ≠ r.val := by
      intro h
      exact hk (γ.injective (by rw [Equiv.apply_symm_apply]; exact Fin.ext h))
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma lup10ab_tw_row (lam c u w : ZMod 3) :
    c * w + (2 * lam * u - 2 * c * w) * 2 = lam * u := by
  have h4 : (4 : ZMod 3) = 1 := by decide
  calc c * w + (2 * lam * u - 2 * c * w) * 2
      = c * w + (2 * lam * u) * 2 - (2 * c * w) * 2 := by ring
    _ = c * w + lam * u * 4 - c * w * 4 := by ring
    _ = lam * u := by rw [h4]; ring

private lemma lup10ab_tw_row_last (lam : ZMod 3) :
    (2 * lam * (2 : ZMod 3)) * 2 = lam * 2 := by
  have h8 : (8 : ZMod 3) = 2 := by decide
  calc (2 * lam * (2 : ZMod 3)) * 2 = lam * 8 := by ring
    _ = lam * 2 := by rw [h8]

private lemma lup10ab_tw_twist_x (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3) :
    (lup10fa_twist γ lam c).mulVec lup10fa_x = lam • lup10fa_x := by
  funext r
  rcases Fin.eq_castSucc_or_eq_last r with ⟨r', rfl⟩ | rfl
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
    have hcol : ∀ j : Fin 4,
        lup10fa_twist γ lam c (Fin.castSucc r') (Fin.castSucc j) =
          if (γ j).val = r'.val then c else 0 := by
      intro j
      simp [lup10fa_twist, j.isLt]
    have hlast : lup10fa_twist γ lam c (Fin.castSucc r') (Fin.last 4) =
        2 * lam * lup10fa_x (Fin.castSucc r') - 2 * c * ![1, 2, 1, 2] (γ.symm r') := by
      simp [lup10fa_twist, r'.isLt]
    have hsum : (∑ j : Fin 4,
        lup10fa_twist γ lam c (Fin.castSucc r') (Fin.castSucc j) *
          lup10fa_x (Fin.castSucc j)) = c * ![1, 2, 1, 2] (γ.symm r') := by
      rw [Finset.sum_congr rfl (fun j _ => by rw [hcol j])]
      exact lup10ab_tw_sum_col γ c r'
    rw [hsum, hlast, show lup10fa_x (Fin.last 4) = 2 from rfl]
    rw [Pi.smul_apply, lup10ab_tw_x_castSucc r']
    exact lup10ab_tw_row lam c _ _
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
    have hcol0 : ∀ j : Fin 4,
        lup10fa_twist γ lam c (Fin.last 4) (Fin.castSucc j) = 0 := by
      intro j
      have hj4 : (γ j).val ≠ 4 := by omega
      simp [lup10fa_twist, j.isLt, hj4]
    have hlast : lup10fa_twist γ lam c (Fin.last 4) (Fin.last 4) =
        2 * lam * lup10fa_x (Fin.last 4) := by
      simp [lup10fa_twist]
    have hsum0 : (∑ j : Fin 4,
        lup10fa_twist γ lam c (Fin.last 4) (Fin.castSucc j) * lup10fa_x (Fin.castSucc j)) = 0 := by
      exact Finset.sum_eq_zero fun j _ => by rw [hcol0 j, zero_mul]
    rw [hsum0, zero_add, hlast, show lup10fa_x (Fin.last 4) = 2 from rfl]
    rw [Pi.smul_apply, show lup10fa_x (Fin.last 4) = 2 from rfl]
    exact lup10ab_tw_row_last lam

private theorem lup10ab_tw_frame {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (he0 : M.a = e 0) :
    ∃ f : Fin 4 ≃ {k : M.ι // k ≠ M.a},
      ∀ j : Fin 4, (f j : M.ι) = e (lup10ab_tau j.castSucc) := by
  classical
  have htau : Function.Injective lup10ab_tau := by decide
  have hsurj : ∀ t : Fin 5, t ≠ 0 → ∃ j : Fin 4, lup10ab_tau j.castSucc = t := by decide
  let g : Fin 4 → {k : M.ι // k ≠ M.a} := fun j =>
    ⟨e (lup10ab_tau j.castSucc), by
      intro h
      have h0 : lup10ab_tau j.castSucc = 0 := e.injective (h.trans he0)
      revert h0
      fin_cases j <;> decide⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j hij
      have h1 : lup10ab_tau i.castSucc = lup10ab_tau j.castSucc :=
        e.injective (Subtype.ext_iff.mp hij)
      exact Fin.castSucc_injective 4 (htau h1)
    · intro k
      obtain ⟨t, ht⟩ := e.surjective (k : M.ι)
      have ht0 : t ≠ 0 := fun h => k.2 (by rw [← ht, h, he0])
      obtain ⟨j, hj⟩ := hsurj t ht0
      refine ⟨j, Subtype.ext ?_⟩
      show e (lup10ab_tau j.castSucc) = (k : M.ι)
      rw [hj, ht]
  exact ⟨Equiv.ofBijective g hg, fun j => rfl⟩

theorem lup10ab_twist_form {G : Type} [Group G] {Bs : Subgroup G} {x y : G} {L H : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hV : Submodule.span (ZMod 3)
      (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤)
    (hbas : M.toLin.Basis) (hx1 : x ≠ 1)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκ1 : ∀ i : Fin 5, κ (M.coroot (e (lup10ab_tau i))) = Pi.single i 1)
    (hκx : ∃ ν : ZMod 3, ν ≠ 0 ∧ κ M.xV = ν • lup10fa_x)
    {φ : MulAut ↥Bs}
    (hφx : ggLin (p := 3) M.model φ M.xV ∈ Submodule.span (ZMod 3) {M.xV})
    (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod 3) (c : ZMod 3)
    (w : M.V ≃ₗ[ZMod 3] M.V) (hSc : M.toLin.ScaledAut M.a π μ)
    (hw : w ∈ M.toLin.parab {k | k ≠ M.a})
    (hT : ∀ i : {k // k ≠ M.a},
      ggLin (p := 3) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i)))
    (hπb : π ⟨M.b, M.a_ne_b.symm⟩ ≠ ⟨M.b, M.a_ne_b.symm⟩)
    (hπ1 : ∀ i : {k // k ≠ M.a}, (i : M.ι) = e 1 → ((π i : {k // k ≠ M.a}) : M.ι) ≠ e 1) :
    ∃ w' : MulAut ↥Bs, w' ∈ ggAutomizer L Bs ∧
      ∃ (b : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c' : ZMod 3), lup10fa_Adm b γ lam c' ∧
        e (lup10ab_tau b.castSucc) = M.b ∧
        ∀ v : M.V, κ (ggLin (p := 3) M.model (w'⁻¹ * φ) v) =
          (lup10fa_twist γ lam c').mulVec (κ v) := by
  classical
  have _ : M.toLin.Basis := hbas
  have _ : x ≠ 1 := hx1
  obtain ⟨f, hf⟩ := lup10ab_tw_frame M e he0
  let γ : Equiv.Perm (Fin 4) := (f.trans π).trans f.symm
  let μ' : Fin 4 → ZMod 3 := fun j => μ (f j)
  have hπf : ∀ i : Fin 4, π (f i) = f (γ i) := by
    intro i
    change π (f i) = f (f.symm (π (f i)))
    rw [Equiv.apply_symm_apply]
  have hμ' : ∀ i : Fin 4, μ' i ≠ 0 := fun i => hSc.1 (f i)
  have hC : ∀ i j : Fin 4,
      ((M.cartan (f i) (f j) : ℤ) : ZMod 3) = lup10fa_C i.castSucc j.castSucc := by
    intro i j
    rw [hf i, hf j, hecart]
    exact lup10ab_tw_C_cast i.castSucc j.castSucc
  have hrel : ∀ i j : Fin 4,
      μ' i * lup10fa_C i.castSucc j.castSucc =
        μ' j * lup10fa_C (γ i).castSucc (γ j).castSucc := by
    intro i j
    have hc := hSc.2 (f i) (f j)
    change μ (f i) * ((M.cartan (f i) (f j) : ℤ) : ZMod 3) =
      μ (f j) * ((M.cartan (π (f i)) (π (f j)) : ℤ) : ZMod 3) at hc
    rw [hπf i, hπf j, hC i j, hC (γ i) (γ j)] at hc
    exact hc
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hmu1 : μ' (1 : Fin 4) ≠ 0 := hμ' 1
  have hprod : μ' (1 : Fin 4) * (2 : ZMod 3) ≠ 0 := mul_ne_zero hmu1 h2
  have hC1j : ∀ j : Fin 4, j ≠ 1 → lup10fa_C (1 : Fin 4).castSucc j.castSucc = 2 := by
    intro j hj
    fin_cases j
    · exact lup10ab_tw_C_10
    · exact absurd rfl hj
    · exact lup10ab_tw_C_12
    · exact lup10ab_tw_C_13
  have hμc : ∀ j : Fin 4, μ' j = μ' 1 := by
    intro j
    by_cases hj : j = 1
    · rw [hj]
    · have hCγ : lup10fa_C (γ 1).castSucc (γ j).castSucc = 0 ∨
          lup10fa_C (γ 1).castSucc (γ j).castSucc = 2 :=
        lup10ab_tw_C_zero_or_two (γ 1) (γ j) (fun h => hj (γ.injective h).symm)
      have hCγ2 : lup10fa_C (γ 1).castSucc (γ j).castSucc = 2 := by
        rcases hCγ with h | h
        · exfalso
          have hh := hrel 1 j
          rw [hC1j j hj, h] at hh
          exact hprod (by simpa using hh)
        · exact h
      have hh := hrel 1 j
      rw [hC1j j hj, hCγ2] at hh
      exact (mul_right_cancel₀ h2 hh).symm
  have hγ1 : γ 1 = 1 := by
    refine lup10ab_tw_C_center (γ 1) ?_
    intro b hb
    obtain ⟨j, rfl⟩ := γ.surjective b
    have hj : j ≠ 1 := fun h => hb (by rw [h])
    have hh := hrel 1 j
    rw [hC1j j hj] at hh
    intro h0
    rw [h0] at hh
    exact hprod (by simpa using hh)
  have hf3 : (f 3 : M.ι) = e 1 := by
    rw [hf 3]
    congr 1
  have hγ3 : γ 3 ≠ 3 := by
    intro h3
    have hπ3 : ((π (f 3) : {k // k ≠ M.a}) : M.ι) ≠ e 1 := hπ1 (f 3) hf3
    apply hπ3
    rw [hπf 3, h3]
    exact hf3
  let b0 : Fin 4 := f.symm ⟨M.b, M.a_ne_b.symm⟩
  have hb0 : e (lup10ab_tau b0.castSucc) = M.b := by
    rw [← hf b0]
    show (f b0 : M.ι) = M.b
    simp [b0]
  have hγb : γ b0 ≠ b0 := by
    intro h
    apply hπb
    have h1 : π (f b0) = f b0 := by rw [hπf b0, h]
    have hfb : f b0 = ⟨M.b, M.a_ne_b.symm⟩ := by simp [b0]
    rw [hfb] at h1
    exact h1
  have hwmap : w ∈ M.parabL {k | k ≠ M.a} := hw
  rw [M.parabL_L] at hwmap
  obtain ⟨w', hw'mem, hw'eq⟩ := Subgroup.mem_map.mp hwmap
  have hfix : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [M.fixed_x]
    exact Submodule.mem_span_singleton_self _
  have hwx : w M.xV = M.xV := by
    have h := mem_ggFixedSubmodule_iff.mp hfix w' hw'mem
    rwa [hw'eq] at h
  have hwxinv : w.symm M.xV = M.xV := by
    have h := congrArg w.symm hwx
    rw [LinearEquiv.symm_apply_apply] at h
    exact h.symm
  obtain ⟨ν, hν0, hκx⟩ := hκx
  have hx0 : M.xV ≠ 0 := by
    intro h
    have h1 : ν • lup10fa_x = 0 := by rw [← hκx, h, map_zero]
    have h2 : lup10fa_x = 0 := (smul_eq_zero.mp h1).resolve_left hν0
    have h3 : (1 : ZMod 3) = 0 := by simpa [lup10fa_x] using congrFun h2 0
    exact (by decide : (1 : ZMod 3) ≠ 0) h3
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hφx
  have hlam0 : lam ≠ 0 := by
    intro h
    have h1 : ggLin (p := 3) M.model φ M.xV = 0 := by rw [← hlam, h, zero_smul]
    have h2 : M.xV = 0 := (ggLin (p := 3) M.model φ).map_eq_zero_iff.mp h1
    exact hx0 h2
  have hc0 : c ≠ 0 := by
    intro h
    have h1 := hT (f 0)
    rw [h] at h1
    simp only [zero_smul] at h1
    have h2 : M.coroot (f 0) = 0 := (ggLin (p := 3) M.model φ).map_eq_zero_iff.mp h1
    have hκf0 : κ (M.coroot (f 0)) = Pi.single (0 : Fin 5) 1 := by
      rw [hf 0]
      exact hκ1 0
    rw [h2, map_zero] at hκf0
    have h3 : (0 : ZMod 3) = 1 := by simpa using congrFun hκf0 0
    exact (by decide : (0 : ZMod 3) ≠ 1) h3
  let c' : ZMod 3 := c * μ' 1
  have hc'0 : c' ≠ 0 := mul_ne_zero hc0 hmu1
  let Φ : M.V ≃ₗ[ZMod 3] M.V := ggLin (p := 3) M.model φ
  have hg_apply : ∀ v : M.V, ggLin (p := 3) M.model (w'⁻¹ * φ) v = w.symm (Φ v) := by
    intro v
    rw [map_mul, map_inv, hw'eq, LinearEquiv.mul_apply]
    rfl
  have hgcor : ∀ j : Fin 4,
      ggLin (p := 3) M.model (w'⁻¹ * φ) (M.coroot (f j)) = c' • M.coroot (f (γ j)) := by
    intro j
    rw [hg_apply]
    have h1 := hT (f j)
    rw [hπf j] at h1
    rw [h1, map_smul, map_smul, LinearEquiv.symm_apply_apply]
    have hμj : μ (f j) = μ (f 1) := hμc j
    rw [hμj, show c' = c * μ (f 1) from rfl, ← smul_smul]
  have hκf : ∀ j : Fin 4, κ (M.coroot (f j)) = Pi.single j.castSucc 1 := by
    intro j
    rw [hf j]
    exact hκ1 j.castSucc
  have hmat : ∀ v : M.V, κ (ggLin (p := 3) M.model (w'⁻¹ * φ) v) =
      (lup10fa_twist γ lam c').mulVec (κ v) := by
    have hlin : (κ.toLinearMap ∘ₗ (ggLin (p := 3) M.model (w'⁻¹ * φ)).toLinearMap) =
        ((lup10fa_twist γ lam c').mulVecLin ∘ₗ κ.toLinearMap) := by
      apply LinearMap.ext_on hV
      intro v hv
      rcases Set.mem_insert_iff.mp hv with rfl | hv
      · have hgx : ggLin (p := 3) M.model (w'⁻¹ * φ) M.xV = lam • M.xV := by
          rw [hg_apply, ← hlam, map_smul, hwxinv]
        have h1 : κ (ggLin (p := 3) M.model (w'⁻¹ * φ) M.xV) = lam • κ M.xV := by
          rw [hgx, map_smul]
        have h2 : (lup10fa_twist γ lam c').mulVec (κ M.xV) = lam • κ M.xV := by
          rw [hκx, Matrix.mulVec_smul, lup10ab_tw_twist_x]
          exact smul_comm _ _ _
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Matrix.mulVecLin_apply]
          using h1.trans h2.symm
      · obtain ⟨i, hi⟩ := Set.mem_range.mp hv
        rw [← hi]
        obtain ⟨j, rfl⟩ := f.surjective i
        have hg1 : κ (ggLin (p := 3) M.model (w'⁻¹ * φ) (M.coroot (f j))) =
            c' • Pi.single (γ j).castSucc 1 := by
          rw [hgcor j, map_smul, hκf (γ j)]
        have hg2 : (lup10fa_twist γ lam c').mulVec (κ (M.coroot (f j))) =
            c' • Pi.single (γ j).castSucc 1 := by
          rw [hκf j]
          exact lup10ab_tw_single γ lam c' j
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Matrix.mulVecLin_apply]
          using hg1.trans hg2.symm
    intro v
    have h := LinearMap.congr_fun hlin v
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Matrix.mulVecLin_apply]
      using h
  exact ⟨w', hw'mem, b0, γ, lam, c', ⟨hγ1, hγ3, hγb, hlam0, hc'0⟩, hb0, hmat⟩

end CFSG.StandardType

end
