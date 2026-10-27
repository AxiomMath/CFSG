module

public import CFSG.LocalAnalysis.StandardType.GGReflNineSound
public import CFSG.LocalAnalysis.StandardType.GGReflDepWeylE6
public import CFSG.LocalAnalysis.StandardType.GGReflExtFinal

public section

namespace CFSG.DepFrame

open CFSG.TwoNodeSmall CFSG.ReflExt CFSG.StandardType CFSG.NineAll

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem verifyAllD_elim {P0 : Pt} {Bstab : ℕ} {T : NTables} (h : verifyAllD P0 Bstab T = true) :
    NCore P0 Bstab T ∧ T.reps.all (verifyRepD P0 (candOfN P0 T)) = true ∧
      T.orb1.all (centEntryOK P0 T) = true := by
  unfold verifyAllD at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨⟨⟨⟨⟨h4, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, h9, h10⟩

variable {P0 : Pt} [Fact P0.p.Prime] {Bstab : ℕ} {T : NTables}
  {A : Subgroup (P0.V ≃ₗ[ZMod P0.p] P0.V)}

theorem classificationD
    (C : CtxN P0 Bstab T A) (hreps : T.reps.all (verifyRepD P0 (candOfN P0 T)) = true)
    (hcent : T.orb1.all (centEntryOK P0 T) = true) :
    ZS.LinWeyl P0.p A ∨
      ∀ s ∈ A, GGLinRefl s → s (P0.vec P0.x) ≠ P0.vec P0.x →
        ∀ r ∈ P0.gens, ∀ e : P0.V ≃ₗ[ZMod P0.p] P0.V,
          (∀ w, e w = w - P0.dot (P0.vec r.f) w • P0.vec r.h) → s * e = e * s := by
  by_cases hW : ZS.LinWeyl P0.p A
  · exact Or.inl hW
  · right
    intro s hsA hsr hsm r hr e he
    obtain ⟨en, hen, hform, rp, hrp, hArep⟩ := C.toM.entry_of_moving hsA hsr hsm
    have hmem : rp ∈ T.reps := List.mem_of_getElem? hrp
    have hv := List.all_eq_true.mp hreps rp hmem
    unfold verifyRepD at hv
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hv
    obtain ⟨⟨hwr, hmv⟩, hk⟩ := hv
    cases hkind : rp.kind with
    | w w =>
      simp only [hkind] at hk
      cases w with
      | kernel v => simp at hk
      | transv t0 =>
        dsimp only at hk
        exact (C.toM.not_bad1 hk rfl hArep).elim
      | order o =>
        dsimp only at hk
        exact (C.toM.not_bad1 hk rfl hArep).elim
      | weyl cw =>
        dsimp only at hk
        simp only [Bool.and_eq_true] at hk
        obtain ⟨⟨hvwf, hvwe6⟩, hS2⟩ := hk
        exfalso
        have hleG : (withExtra P0 [rp.r]).group ≤ A := by
          apply C.toM.group_le
          intro r' hr'
          rw [List.mem_singleton] at hr'
          rw [hr']
          exact hArep
        have hAeq : A = (withExtra P0 [rp.r]).group := by
          apply le_antisymm
          · conv_lhs => rw [C.rgen]
            rw [Subgroup.closure_le]
            rintro s' ⟨hsA', hsr'⟩
            exact (C.stage2 hwr hS2 hArep hsA' hsr').1
          · exact hleG
        haveI : Fact (withExtra P0 [rp.r]).p.Prime := ‹Fact P0.p.Prime›
        have hWE : ZS.LinWeyl P0.p (withExtra P0 [rp.r]).group :=
          verifyWE6_sound (wfCheck_sound hvwf) hvwe6
        exact hW (by rw [hAeq]; exact hWE)
    | cent =>
      simp only [hkind] at hk
      have hce := List.all_eq_true.mp hcent en hen
      simp only [centEntryOK, hrp, hkind, Bool.or_eq_true] at hce
      have hform' : ∀ w, s w = w - P0.dot (P0.vec rp.r.f) w • P0.vec rp.r.h := by
        rcases hce with h1 | h2
        · intro w
          rw [hform w, reqb_eq h1]
        · intro w
          rw [hform w, reqb_eq h2]
          obtain ⟨hf, hh⟩ := vec_negR P0 rp.r
          rw [hf, hh]
          have hd : P0.dot (-P0.vec rp.r.f) w = - P0.dot (P0.vec rp.r.f) w := by
            show (pww2_dotLM P0 (-P0.vec rp.r.f)) w = - (pww2_dotLM P0 (P0.vec rp.r.f)) w
            simp [pww2_dotLM, Pt.dot, Finset.sum_neg_distrib]
          rw [hd, neg_smul, smul_neg, neg_neg]
      have hev_s : ∀ u, s (P0.vec u) = P0.vec (P0.applyRefl rp.r u) := fun u => by
        rw [Pt.vec_applyRefl, hform']
      have hev_e : ∀ u, e (P0.vec u) = P0.vec (P0.applyRefl r u) := fun u => by
        rw [Pt.vec_applyRefl, he]
      apply pww2_le_ext_unit P0
      intro j
      show s (e (P0.vec (P0.unit j))) = e (s (P0.vec (P0.unit j)))
      rw [hev_e, hev_s, hev_s, hev_e]
      have hcent' : P0.gens.all (fun g => (List.range P0.D).all fun m =>
          P0.vecEq (P0.applyRefl g (P0.applyRefl rp.r (P0.unit m)))
            (P0.applyRefl rp.r (P0.applyRefl g (P0.unit m)))) = true := hk
      have hcj := List.all_eq_true.mp (List.all_eq_true.mp hcent' r hr) j.val
        (List.mem_range.mpr j.isLt)
      exact (pww2_vec_of_vecEq P0 _ _ hcj).symm

theorem depFrame_core
    (P0 : Pt) [Fact P0.p.Prime] {Bstab : ℕ} {T : NTables} (hp2 : P0.p ≠ 2)
    (hok : verifyAllD P0 Bstab T = true) {n : ℕ} (G : ℕ → Refl)
    (hgens : P0.gens = (List.range n).map G)
    {V : Type} [AddCommGroup V] [Module (ZMod P0.p) V] (ε : V ≃ₗ[ZMod P0.p] P0.V)
    (h : Fin n → V) (α : Fin n → Module.Dual (ZMod P0.p) V) (x : V)
    (r : Fin n → (V ≃ₗ[ZMod P0.p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (A : Subgroup (V ≃ₗ[ZMod P0.p] V)) (hrA : ∀ i, r i ∈ A)
    (hεh : ∀ i : Fin n, ε (h i) = P0.vec (G i).h)
    (hεα : ∀ (i : Fin n) w, α i w = P0.dot (P0.vec (G i).f) (ε w)) (hεx : ε x = P0.vec P0.x)
    (hrg : A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s}) (hnt : ∀ g ∈ A, ¬ IsTransv g)
    (hcard : Nat.card A ≤ P0.bound)
    (hstab : Nat.card ↥(A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod P0.p] V) x) ≤ Bstab) :
    ZS.LinWeyl P0.p A ∨ ∀ s ∈ A, GGLinRefl s → s x ≠ x → ∀ i, s * r i = r i * s := by
  have hfr : ∀ r' ∈ P0.gens, ∃ g ∈ A,
      ∀ w : P0.V, ε (g (ε.symm w)) = w - P0.dot (P0.vec r'.f) w • P0.vec r'.h := by
    intro r' hr'
    rw [hgens] at hr'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr'
    have hi' : i < n := List.mem_range.mp hi
    refine ⟨r ⟨i, hi'⟩, hrA _, fun w => ?_⟩
    rw [hr, map_sub, map_smul, LinearEquiv.apply_symm_apply, hεh ⟨i, hi'⟩,
      hεα ⟨i, hi'⟩ (ε.symm w), LinearEquiv.apply_symm_apply]
  have hctx := ctxN_of_conj (T := T) hp2 (verifyAllD_elim hok).1 ε x hεx A hfr hrg hnt hcard hstab
  rcases classificationD hctx (verifyAllD_elim hok).2.1 (verifyAllD_elim hok).2.2 with hw | hcomm
  · exact Or.inl (linWeyl_of_conj ε A hw)
  · right
    intro s hsA hsr hsm i
    have hmem' : rxConj ε s ∈ A.map (rxConj ε).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨s, hsA, rfl⟩
    have hrefl' : GGLinRefl (rxConj ε s) := (rxConj_isRefl ε s).mpr hsr
    have hmov' : rxConj ε s (P0.vec P0.x) ≠ P0.vec P0.x :=
      moving_conj ε x (P0.vec P0.x) 1 one_ne_zero (by rw [one_smul]; exact hεx) s hsm
    have hGi : G i ∈ P0.gens := by
      rw [hgens]
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr i.isLt, rfl⟩
    have hform : ∀ w, rxConj ε (r i) w = w - P0.dot (P0.vec (G i).f) w • P0.vec (G i).h :=
      fun w => by
        rw [rxConj_apply, hr, map_sub, map_smul, LinearEquiv.apply_symm_apply, hεh i,
          hεα i (ε.symm w), LinearEquiv.apply_symm_apply]
    have hcomm' := hcomm (rxConj ε s) hmem' hrefl' hmov' (G i) hGi (rxConj ε (r i)) hform
    apply (rxConj ε).injective
    rw [map_mul, map_mul]
    exact hcomm'

end CFSG.DepFrame

end
