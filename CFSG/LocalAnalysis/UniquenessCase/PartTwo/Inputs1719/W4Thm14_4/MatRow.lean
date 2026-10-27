module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.MatRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.A5Irr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB
public import TauCeti.FieldTheory.Finite.Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

theorem matModel_row_cases {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {D X : Subgroup (MulAut V)} {F : Type} [Field F] [Finite F] {d r : ℕ}
    {β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)}
    {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F} {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F}
    (hM : IsMatModel D X β ρ σ) (hX : IsAlt ↥X 5) :
    (Nat.card F = 2 → r = 4) ∧ (Nat.card F = 4 → r = 2 ∨ r = 4) := by
  classical
  have hXalt : IsAlt ↥X 5 := hX
  have hXne : X ≠ ⊥ := ne_bot_of_isAlt_five hX
  have hd : 0 < d := by
    rw [Nat.pos_iff_ne_zero]
    intro hd0
    have hcardV : Nat.card V = 1 := by
      rw [card_eq_card_pow_of_matEquiv (F := F) β, hd0]
      simp
    have hsingleV : Subsingleton V := (Nat.card_eq_one_iff_unique.mp hcardV).1
    have hXbot : X = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x _
      exact MulEquiv.ext fun v => hsingleV.elim (x v) v
    exact hXne hXbot
  let a : Fin d := ⟨0, hd⟩
  have hr : 0 < r := by
    rw [Nat.pos_iff_ne_zero]
    intro hr0
    have hcard1 : Nat.card ↥(matRowSub β a) = 1 := by
      rw [card_matRowSub, hr0]
      simp
    have hsingle : Subsingleton ↥(matRowSub β a) :=
      (Nat.card_eq_one_iff_unique.mp hcard1).1
    obtain ⟨x, hx, u, hu, hxu⟩ := exists_moves_matRowSub hM hXne a
    have hu1 : u = 1 := by
      have h : (⟨u, hu⟩ : ↥(matRowSub β a)) = 1 := hsingle.elim _ 1
      simpa using congrArg Subtype.val h
    exact hxu (by rw [hu1, map_one])
  have hRne : matRowSub β a ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx, u, hu, hxu⟩ := exists_moves_matRowSub hM hXne a
    rw [hbot, Subgroup.mem_bot] at hu
    exact hxu (by rw [hu, map_one])
  have hScalR : ∀ (c : F) (hc : c ≠ 0) (v : V) (hv : v ∈ matRowSub β a),
      matScal β c hc v ∈ matRowSub β a := by
    intro c hc v hv b k hb
    rw [matScal_apply]
    show c * Multiplicative.toAdd (β v) b k = 0
    rw [hv b k hb, mul_zero]
  have hrow_mul : ∀ (u v : V) (hu : u ∈ matRowSub β a) (hv : v ∈ matRowSub β a)
      (huv : u * v ∈ matRowSub β a),
      Multiplicative.toAdd (matRowEquiv β a ⟨u * v, huv⟩) =
        Multiplicative.toAdd (matRowEquiv β a ⟨u, hu⟩) +
          Multiplicative.toAdd (matRowEquiv β a ⟨v, hv⟩) := by
    intro u v hu hv huv
    ext k
    rw [matRowEquiv_apply, Pi.add_apply, matRowEquiv_apply, matRowEquiv_apply, map_mul,
      toAdd_mul, Matrix.add_apply]
  have hrow_smul : ∀ (c : F) (hc : c ≠ 0) (u : V) (hu : u ∈ matRowSub β a)
      (hcu : matScal β c hc u ∈ matRowSub β a),
      Multiplicative.toAdd (matRowEquiv β a ⟨matScal β c hc u, hcu⟩) =
        c • Multiplicative.toAdd (matRowEquiv β a ⟨u, hu⟩) := by
    intro c hc u hu hcu
    ext k
    rw [matRowEquiv_apply, matScal_apply, Matrix.smul_apply, Pi.smul_apply,
      matRowEquiv_apply, smul_eq_mul]
  constructor
  ·
    intro hF2
    have hscal2 : ∀ c : F, c = 0 ∨ c = 1 :=
      CFSG.Quasithin.G64.eq_zero_or_eq_one_of_card_two hF2
    have hmvR : ∃ x ∈ X, ∃ u ∈ matRowSub β a, x u ≠ u :=
      exists_moves_matRowSub hM hXne a
    have hirrR : IsIrrOn X (matRowSub β a) ⊥ := by
      refine ⟨bot_lt_iff_ne_bot.mpr hRne, stableUnder_matRowSub hM a, ?_, ?_⟩
      · intro x hx u hu
        rw [Subgroup.mem_bot] at hu ⊢
        rw [hu, map_one]
      · intro J hJstab hJbot hJle
        by_cases hJne : J = ⊥
        · exact Or.inl hJne
        · right
          let A : Set (Fin r → F) :=
            {w | ∃ u : ↥J, Multiplicative.toAdd (matRowEquiv β a ⟨u, hJle u.2⟩) = w}
          let W : Submodule F (Fin r → F) := Submodule.span F A
          have hWinv : ∀ x : ↥X, ∀ w ∈ W,
              (((σ x : Matrix.GeneralLinearGroup (Fin r) F) :
                Matrix (Fin r) (Fin r) F).mulVec w) ∈ W := by
            intro x w hw
            let M : Matrix (Fin r) (Fin r) F :=
              (σ x : Matrix.GeneralLinearGroup (Fin r) F)
            refine Submodule.span_induction (p := fun y _ => M.mulVec y ∈ W) ?_ ?_ ?_ ?_ hw
            · rintro y ⟨u, rfl⟩
              have hmem : (x : MulAut V) (u : V) ∈ J := hJstab x x.2 (u : V) u.2
              have hact := matRowEquiv_act hM a x ⟨(u : V), hJle u.2⟩
                ⟨(x : MulAut V) (u : V), hJle hmem⟩ rfl
              rw [← hact]
              exact Submodule.subset_span ⟨⟨(x : MulAut V) (u : V), hmem⟩, rfl⟩
            · simpa using Submodule.zero_mem W
            · intro y z _ _ ihy ihz
              rw [Matrix.mulVec_add]
              exact Submodule.add_mem W ihy ihz
            · intro c y _ ihy
              rw [Matrix.mulVec_smul]
              exact Submodule.smul_mem W c ihy
          rcases hM.U_irr W hWinv with hWbot | hWtop
          · exfalso
            apply hJne
            rw [Subgroup.eq_bot_iff_forall]
            intro v hv
            have hmemA : Multiplicative.toAdd (matRowEquiv β a ⟨v, hJle hv⟩) ∈ A :=
              ⟨⟨v, hv⟩, rfl⟩
            have hmemW : Multiplicative.toAdd (matRowEquiv β a ⟨v, hJle hv⟩) ∈ W :=
              Submodule.subset_span (R := F) hmemA
            rw [hWbot, Submodule.mem_bot] at hmemW
            have hv1 : (⟨v, hJle hv⟩ : ↥(matRowSub β a)) = 1 := by
              apply (matRowEquiv β a).injective
              apply Multiplicative.toAdd.injective
              simpa using hmemW
            simpa using congrArg Subtype.val hv1
          · refine le_antisymm hJle ?_
            intro v hv
            have hAle : W ≤ A := by
              intro w hw
              refine Submodule.span_induction (p := fun y _ => y ∈ A) ?_ ?_ ?_ ?_ hw
              · intro y hy
                exact hy
              · exact ⟨⟨1, J.one_mem⟩, by simp⟩
              · rintro y z _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
                exact ⟨⟨u * v, J.mul_mem u.2 v.2⟩,
                  hrow_mul (u : V) (v : V) (hJle u.2) (hJle v.2)
                    (hJle (J.mul_mem u.2 v.2))⟩
              · rintro c y _ ⟨u, rfl⟩
                rcases hscal2 c with rfl | rfl
                · rw [zero_smul]
                  exact ⟨⟨1, J.one_mem⟩, by simp⟩
                · rw [one_smul]
                  exact ⟨u, rfl⟩
            have hmemA : Multiplicative.toAdd (matRowEquiv β a ⟨v, hv⟩) ∈ A := by
              apply hAle
              rw [hWtop]
              exact Submodule.mem_top
            obtain ⟨u, heq⟩ := hmemA
            have hvu : (u : V) = v := by
              have h1 : matRowEquiv β a ⟨(u : V), hJle u.2⟩ =
                  matRowEquiv β a ⟨v, hv⟩ := by
                apply Multiplicative.toAdd.injective
                exact heq
              exact congrArg Subtype.val ((matRowEquiv β a).injective h1)
            rw [← hvu]
            exact u.2
    obtain ⟨hR16, -⟩ := a5_irr_classification hV hXalt hirrR hmvR
    have hpow : Nat.card F ^ r = 16 := by
      rw [← card_matRowSub β a, hR16]
    rw [hF2] at hpow
    have h16 : (2 : ℕ) ^ r = 2 ^ 4 := by
      rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
      exact hpow
    exact Nat.pow_right_injective (le_refl 2) h16
  ·
    intro hF4
    letI : Fintype F := Fintype.ofFinite F
    have h2 : (2 : F) = 0 := by
      let E : Matrix (Fin d) (Fin r) F :=
        Matrix.of fun i j => if i = ⟨0, hd⟩ ∧ j = ⟨0, hr⟩ then 1 else 0
      have hv : (β.symm (Multiplicative.ofAdd E)) ^ 2 = 1 := hV _
      have h := congrArg (fun v : V => Multiplicative.toAdd (β v)) hv
      have h' : E + E = 0 := by
        simpa [pow_two, toAdd_mul] using h
      have h00 := congrFun (congrFun h' ⟨0, hd⟩) ⟨0, hr⟩
      simp [E, Matrix.add_apply] at h00
      have htwo : (2 : F) = 1 + 1 := by norm_num
      rw [htwo]
      exact h00
    obtain ⟨ω, hωsq⟩ := TauCeti.exists_sq_add_self_add_one_eq_zero_of_card_eq_four hF4
    have hω0 : ω ≠ 0 := by
      intro h0
      rw [h0] at hωsq
      simpa using hωsq
    have hω1 : ω ≠ 1 := by
      intro h1
      rw [h1] at hωsq
      have h3 : (1 : F) + 1 + 1 = 0 := by simpa using hωsq
      have hone : (1 : F) + 1 + 1 = 1 := by
        rw [show (1 : F) + 1 + 1 = 2 + 1 by norm_num, h2, zero_add]
      rw [hone] at h3
      exact one_ne_zero h3
    have huniv : (Finset.univ : Finset F) = {0, 1, ω, ω ^ 2} :=
      TauCeti.univ_eq_zero_one_root_sq hF4 hωsq
    have hcases : ∀ c : F, c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω ^ 2 := by
      intro c
      have hc : c ∈ ({0, 1, ω, ω ^ 2} : Finset F) := by
        rw [← huniv]
        exact Finset.mem_univ c
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
    have hωadd : ω ^ 2 = ω + 1 := by
      have h3 : (ω + 1) + (ω + 1) = 0 := by
        have h : (2 : F) * (ω + 1) = 0 := by rw [h2, zero_mul]
        rwa [two_mul] at h
      have hsq' : ω ^ 2 + (ω + 1) = 0 := by
        rw [← add_assoc]
        exact hωsq
      exact add_right_cancel (hsq'.trans h3.symm)
    obtain ⟨U, hUle, hUirr⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.s15_Three_exists_irr_le
        (A := X) (X := matRowSub β a) (stableUnder_matRowSub hM a) hRne
    have hUstab : StableUnder X U := hUirr.2.1
    have hUne : U ≠ ⊥ := bot_lt_iff_ne_bot.mp hUirr.1
    let ωU : Subgroup V := U.map (matScal β ω hω0).toMonoidHom
    let S : Subgroup V := U ⊔ ωU
    have hωUstab : StableUnder X ωU := by
      intro x hx v hv
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
      refine Subgroup.mem_map.mpr ⟨x u, hUstab x hx u hu, ?_⟩
      have hcomm := (matScal_commute hM ω hω0).2 x hx
      have h1 := congrArg (fun f : MulAut V => f u) hcomm
      rw [MulAut.mul_apply, MulAut.mul_apply] at h1
      exact h1
    have hωUcard : Nat.card ↥ωU = Nat.card ↥U :=
      Subgroup.card_map_of_injective (MulEquiv.injective (matScal β ω hω0))
    have hSle : S ≤ matRowSub β a := by
      intro v hv
      rw [Subgroup.mem_sup] at hv
      obtain ⟨u, hu, w, hw, rfl⟩ := hv
      refine (matRowSub β a).mul_mem (hUle hu) ?_
      obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hw
      exact hScalR ω hω0 u' (hUle hu')
    let A : Set (Fin r → F) :=
      {w | ∃ u : ↥U, Multiplicative.toAdd (matRowEquiv β a ⟨u, hUle u.2⟩) = w}
    let T : Set (Fin r → F) :=
      {w | ∃ s : ↥S, Multiplicative.toAdd (matRowEquiv β a ⟨s, hSle s.2⟩) = w}
    have hT_desc : ∀ w : Fin r → F, w ∈ T ↔
        ∃ x ∈ A, ∃ y ∈ A, x + ω • y = w := by
      intro w
      constructor
      · rintro ⟨s, rfl⟩
        have hs : (s : V) ∈ U ⊔ ωU := s.2
        obtain ⟨u, hu, v, hv, hsv⟩ := Subgroup.mem_sup.mp hs
        obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hv
        have hsv' : s = (⟨u * matScal β ω hω0 u',
            Subgroup.mul_mem_sup hu (Subgroup.mem_map_of_mem _ hu')⟩ : ↥S) := by
          refine Subtype.ext ?_
          exact hsv.symm
        rw [hsv']
        refine ⟨Multiplicative.toAdd (matRowEquiv β a ⟨u, hUle hu⟩), ⟨⟨u, hu⟩, rfl⟩,
          Multiplicative.toAdd (matRowEquiv β a ⟨u', hUle hu'⟩), ⟨⟨u', hu'⟩, rfl⟩, ?_⟩
        rw [hrow_mul u (matScal β ω hω0 u') (hUle hu)
          (hScalR ω hω0 u' (hUle hu')),
          hrow_smul ω hω0 u' (hUle hu') (hScalR ω hω0 u' (hUle hu'))]
      · rintro ⟨x, ⟨u, rfl⟩, y, ⟨u', rfl⟩, rfl⟩
        refine ⟨⟨u * matScal β ω hω0 u',
          Subgroup.mul_mem_sup u.2 (Subgroup.mem_map_of_mem _ u'.2)⟩, ?_⟩
        rw [hrow_mul (u : V) (matScal β ω hω0 (u' : V)) (hUle u.2)
          (hScalR ω hω0 (u' : V) (hUle u'.2)),
          hrow_smul ω hω0 (u' : V) (hUle u'.2) (hScalR ω hω0 (u' : V) (hUle u'.2))]
    have hT0 : (0 : Fin r → F) ∈ T := ⟨1, by simp⟩
    have hAadd : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A := by
      rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
      exact ⟨⟨u * v, U.mul_mem u.2 v.2⟩,
        hrow_mul (u : V) (v : V) (hUle u.2) (hUle v.2) (hUle (U.mul_mem u.2 v.2))⟩
    have hTadd : ∀ x ∈ T, ∀ y ∈ T, x + y ∈ T := by
      intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := (hT_desc x).mp hx
      obtain ⟨c, hc, d, hd, rfl⟩ := (hT_desc y).mp hy
      refine (hT_desc _).mpr ⟨_, hAadd a ha c hc, _, hAadd b hb d hd, ?_⟩
      rw [smul_add]
      abel
    have hTsmulω : ∀ x ∈ T, ω • x ∈ T := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (hT_desc x).mp hx
      refine (hT_desc _).mpr ⟨b, hb, _, hAadd a ha b hb, ?_⟩
      simp only [smul_add, smul_smul, ← pow_two, hωadd, add_smul, one_smul]
      abel
    have hTsmul : ∀ c : F, ∀ x ∈ T, c • x ∈ T := by
      intro c x hx
      rcases hcases c with rfl | rfl | rfl | rfl
      · rw [zero_smul]
        exact hT0
      · rwa [one_smul]
      · exact hTsmulω x hx
      · rw [hωadd, add_smul, one_smul]
        exact hTadd _ (hTsmulω x hx) _ hx
    have hAT : ∀ x ∈ A, x ∈ T := by
      rintro x ⟨u, rfl⟩
      exact ⟨⟨u, Subgroup.mem_sup_left u.2⟩, rfl⟩
    let W : Submodule F (Fin r → F) := Submodule.span F A
    have hWinv : ∀ x : ↥X, ∀ w ∈ W,
        (((σ x : Matrix.GeneralLinearGroup (Fin r) F) :
          Matrix (Fin r) (Fin r) F).mulVec w) ∈ W := by
      intro x w hw
      let M : Matrix (Fin r) (Fin r) F := (σ x : Matrix.GeneralLinearGroup (Fin r) F)
      refine Submodule.span_induction (p := fun y _ => M.mulVec y ∈ W) ?_ ?_ ?_ ?_ hw
      · rintro y ⟨u, rfl⟩
        have hmem : (x : MulAut V) (u : V) ∈ U := hUstab x x.2 (u : V) u.2
        have hact := matRowEquiv_act hM a x ⟨(u : V), hUle u.2⟩
          ⟨(x : MulAut V) (u : V), hUle hmem⟩ rfl
        rw [← hact]
        exact Submodule.subset_span ⟨⟨(x : MulAut V) (u : V), hmem⟩, rfl⟩
      · simpa using Submodule.zero_mem W
      · intro y z _ _ ihy ihz
        rw [Matrix.mulVec_add]
        exact Submodule.add_mem W ihy ihz
      · intro c y _ ihy
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem W c ihy
    have hWne : W ≠ ⊥ := by
      haveI : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).mpr hUne
      obtain ⟨u, hu1⟩ := exists_ne (1 : ↥U)
      intro hbot
      have hrowne : Multiplicative.toAdd (matRowEquiv β a ⟨(u : V), hUle u.2⟩) ≠ 0 := by
        intro h0
        apply hu1
        have hq : matRowEquiv β a ⟨(u : V), hUle u.2⟩ = 1 := by
          apply Multiplicative.toAdd.injective
          simpa using h0
        have hsub : (⟨(u : V), hUle u.2⟩ : ↥(matRowSub β a)) = 1 :=
          (matRowEquiv β a).injective (by simpa using hq)
        exact Subtype.ext (by simpa using congrArg Subtype.val hsub)
      have hmemW : Multiplicative.toAdd (matRowEquiv β a ⟨(u : V), hUle u.2⟩) ∈ W :=
        Submodule.subset_span ⟨u, rfl⟩
      rw [hbot, Submodule.mem_bot] at hmemW
      exact hrowne hmemW
    have hWtop : W = ⊤ := by
      rcases hM.U_irr W hWinv with h | h
      · exact absurd h hWne
      · exact h
    have hWleT : W ≤ T := by
      intro w hw
      refine Submodule.span_induction (p := fun y _ => y ∈ T) ?_ ?_ ?_ ?_ hw
      · intro y hy
        exact hAT y hy
      · exact hT0
      · intro y z _ _ ihy ihz
        exact hTadd y ihy z ihz
      · intro c y _ ihy
        exact hTsmul c y ihy
    have hTuniv : T = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro w
      exact hWleT (by rw [hWtop]; exact Submodule.mem_top)
    have hSR : S = matRowSub β a := by
      refine le_antisymm hSle ?_
      intro v hv
      have hmemT : Multiplicative.toAdd (matRowEquiv β a ⟨v, hv⟩) ∈ T := by
        rw [hTuniv]
        exact Set.mem_univ _
      obtain ⟨s, heq⟩ := hmemT
      have hsv : (s : V) = v := by
        have h1 : matRowEquiv β a ⟨s, hSle s.2⟩ = matRowEquiv β a ⟨v, hv⟩ := by
          apply Multiplicative.toAdd.injective
          exact heq
        exact congrArg Subtype.val ((matRowEquiv β a).injective h1)
      rw [← hsv]
      exact s.2
    have hcardS : Nat.card ↥S = Nat.card F ^ r := by
      have hbij : Function.Bijective
          (fun s : ↥S => Multiplicative.toAdd (matRowEquiv β a ⟨s, hSle s.2⟩)) := by
        refine ⟨?_, ?_⟩
        · intro s1 s2 h
          have h1 : matRowEquiv β a ⟨s1, hSle s1.2⟩ = matRowEquiv β a ⟨s2, hSle s2.2⟩ :=
            Multiplicative.toAdd.injective h
          exact Subtype.ext (congrArg (fun x : ↥(matRowSub β a) => (x : V))
            ((matRowEquiv β a).injective h1))
        · intro w
          have hmemT : w ∈ T := by
            rw [hTuniv]
            exact Set.mem_univ w
          obtain ⟨s, heq⟩ := hmemT
          exact ⟨s, heq⟩
      calc Nat.card ↥S = Nat.card (Fin r → F) :=
            Nat.card_congr (Equiv.ofBijective _ hbij)
        _ = Nat.card F ^ r := by rw [Nat.card_fun, Nat.card_fin]
    have hmvU : ∃ x ∈ X, ∃ u ∈ U, x u ≠ u := by
      by_contra h
      push Not at h
      have htrivS : ∀ x ∈ X, ∀ s ∈ S, x s = s := by
        intro x hx s hs
        rw [Subgroup.mem_sup] at hs
        obtain ⟨u, hu, v, hv, rfl⟩ := hs
        obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hv
        rw [map_mul, h x hx u hu]
        congr 1
        have hcomm := (matScal_commute hM ω hω0).2 x hx
        have h1 := congrArg (fun f : MulAut V => f u') hcomm
        rw [MulAut.mul_apply, MulAut.mul_apply, h x hx u' hu'] at h1
        exact h1.symm
      obtain ⟨x, hx, u, hu, hxu⟩ := exists_moves_matRowSub hM hXne a
      exact hxu (htrivS x hx u (hSR.symm ▸ hu))
    obtain ⟨hU16, -⟩ := a5_irr_classification hV hXalt hUirr hmvU
    have hIstab : StableUnder X (U ⊓ ωU) := by
      intro x hx v hv
      rw [Subgroup.mem_inf] at hv ⊢
      exact ⟨hUstab x hx v hv.1, hωUstab x hx v hv.2⟩
    have hcore : Nat.card F ^ r = 256 ∨ Nat.card F ^ r = 16 := by
      rcases hUirr.2.2.2 (U ⊓ ωU) hIstab bot_le inf_le_left with hIbot | hItop
      · left
        have hdisj : Disjoint U ωU := by
          rw [disjoint_iff_inf_le, hIbot]
        have hbij : Function.Bijective
            (fun p : ↥U × ↥ωU => (⟨(p.1 : V) * (p.2 : V),
              Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥S)) := by
          refine ⟨?_, ?_⟩
          · intro p q hpq
            have h1 : (p.1 : V) * (p.2 : V) = (q.1 : V) * (q.2 : V) :=
              congrArg Subtype.val hpq
            exact Subgroup.mul_injective_of_disjoint hdisj h1
          · rintro ⟨s, hs⟩
            rw [Subgroup.mem_sup] at hs
            obtain ⟨u, hu, v, hv, rfl⟩ := hs
            exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
        have h256 : Nat.card ↥S = 256 := by
          calc Nat.card ↥S = Nat.card (↥U × ↥ωU) :=
                Nat.card_congr (Equiv.ofBijective
                  (fun p : ↥U × ↥ωU => (⟨(p.1 : V) * (p.2 : V),
                    Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥S)) hbij).symm
            _ = Nat.card ↥U * Nat.card ↥ωU := Nat.card_prod _ _
            _ = 256 := by norm_num [hU16, hωUcard]
        exact hcardS.symm.trans h256
      · right
        have hUω : U = ωU :=
          Subgroup.eq_of_le_of_card_ge (hItop ▸ inf_le_right) (le_of_eq hωUcard)
        have h16 : Nat.card ↥S = 16 := by
          rw [show S = U by rw [show S = U ⊔ ωU from rfl, hUω, sup_idem], hU16]
        exact hcardS.symm.trans h16
    rcases hcore with hcore | hcore <;> rw [hF4] at hcore
    · right
      have h256 : (4 : ℕ) ^ r = 4 ^ 4 := by
        rw [show (4 : ℕ) ^ 4 = 256 by norm_num]
        exact hcore
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h256
    · left
      have h16 : (4 : ℕ) ^ r = 4 ^ 2 := by
        rw [show (4 : ℕ) ^ 2 = 16 by norm_num]
        exact hcore
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h16

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
