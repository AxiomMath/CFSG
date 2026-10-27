module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.M3a
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.GenPi

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T614

theorem nonempty_mulEquiv_of_subsingleton {M N : Type*} [Group M] [Group N] [Subsingleton M]
    [Subsingleton N] : Nonempty (M ≃* N) :=
  ⟨{ toFun := fun _ => 1
     invFun := fun _ => 1
     left_inv := fun _ => Subsingleton.elim _ _
     right_inv := fun _ => Subsingleton.elim _ _
     map_mul' := fun _ _ => (mul_one 1).symm }⟩

end T614

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E : Subgroup G}

theorem nonempty_pi_mulEquiv_thetaTilde
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) :
    Nonempty ((Fin p → ↥(thetaOf (thetaTilde θ E) B)) ≃* ↥(thetaTilde θ E b)) := by
  classical
  have hbA : b ∈ A := hB.1 hb
  have hbE : b ∉ E := not_mem_of_mem_complement hEB hb hb1
  have hline := h.zpowers_mem_E1 hbA hb1
  have hline0 := h.ne_bot_of_mem_E1 hline
  have hsol : sol (θ b) = ⊥ := h.sol_apply hbA hb1
  have hK : IsDirectProduct (lcal (θ b)) (kOf (θ b)) := isDirectProduct_lcal_kOf hsol
  have hAN : A ≤ Subgroup.normalizer (θ b : Set G) := h.isFunctor.normalized b hbA hb1
  have hthb : thetaOf θ (Subgroup.zpowers b) = θ b := h.isFunctor.thetaOf_zpowers hbA hb1
  have hcard : Nat.card (lcal (θ b)) = p := by
    rw [← hthb]
    exact S.card_F _ hline fun hz => hbE (hz ▸ Subgroup.mem_zpowers b)
  have hNL : ∀ L ∈ lcal (θ b), A ⊓ Subgroup.normalizer (L : Set G) =
      Subgroup.zpowers b ⊔ E := fun L hL => by
    rw [← S.bN_eq _ hline]
    exact (h.lemma_6_9_b hline.1 hline0 L (hthb ▸ hL)).symm
  have hEN : ∀ L ∈ lcal (θ b), E ≤ Subgroup.normalizer (L : Set G) := fun L hL e he => by
    have : e ∈ A ⊓ Subgroup.normalizer (L : Set G) := by
      rw [hNL L hL]
      exact Subgroup.mem_sup_right he
    exact this.2
  have hX := T614.isDirectProduct_inf_centralizer hK hEN
  set SX : Set (Subgroup G) := {Y | ∃ J ∈ lcal (θ b), Y = J ⊓ Subgroup.centralizer (E : Set G)}
    with hSX
  have hXeq : thetaTilde θ E b = kOf (θ b) ⊓ Subgroup.centralizer (E : Set G) :=
    h.thetaTilde_eq_inf_centralizer S.mem.1 hbA hb1
  have hBC : ∀ c ∈ B, (Subgroup.centralizer (E : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer (E : Set G) := by
    intro c hc
    refine L69.map_conj_eq_self_iff.mpr (Subgroup.le_normalizer ?_)
    exact Subgroup.mem_centralizer_iff.mpr fun e he => (h.comm_of_mem_A (S.mem.1 he) (hB.1 hc))
  have hmapinf : ∀ c ∈ B, ∀ L : Subgroup G,
      (L ⊓ Subgroup.centralizer (E : Set G)).map (MulAut.conj c).toMonoidHom =
        L.map (MulAut.conj c).toMonoidHom ⊓ Subgroup.centralizer (E : Set G) := by
    intro c hc L
    rw [Subgroup.map_inf _ _ _ (MulAut.conj c).injective, hBC c hc]
  have hperm : ∀ c ∈ B, ∀ J ∈ SX, J.map (MulAut.conj c).toMonoidHom ∈ SX := by
    rintro c hc _ ⟨L, hL, rfl⟩
    exact ⟨L.map (MulAut.conj c).toMonoidHom, map_conj_mem_lcal hL (hAN (hB.1 hc)), hmapinf c hc L⟩
  have htransL : ∀ L ∈ lcal (θ b), ∀ L' ∈ lcal (θ b),
      ∃ c ∈ B, L' = L.map (MulAut.conj c).toMonoidHom := by
    intro L hL L' hL'
    obtain ⟨a, haA, rfl⟩ := h.exists_conj_eq_of_mem_lcal hline.1 hline0 (hthb ▸ hL) (hthb ▸ hL')
    have haEB : a ∈ E ⊔ B := (S.sup_eq h hB hEB).symm ▸ haA
    have hcomm : ∀ e ∈ E, ∀ β ∈ B, Commute e β := fun e he β hβ =>
      h.comm_of_mem_A (S.mem.1 he) (hB.1 hβ)
    obtain ⟨e, he, β, hβ, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp haEB
    refine ⟨β, hβ, ?_⟩
    have hLβ : L.map (MulAut.conj β).toMonoidHom ∈ lcal (θ b) :=
      map_conj_mem_lcal hL (hAN (hB.1 hβ))
    rw [← T517.map_conj_map_conj]
    exact L69.map_conj_eq_self_iff.mpr (hEN _ hLβ he)
  have htrans : ∀ J ∈ SX, ∀ K ∈ SX, ∃ c ∈ B, K = J.map (MulAut.conj c).toMonoidHom := by
    rintro _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩
    obtain ⟨c, hc, rfl⟩ := htransL L hL L' hL'
    exact ⟨c, hc, (hmapinf c hc L).symm⟩
  have hker : ∀ J ∈ SX, B ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.centralizer (J : Set G) := by
    rintro _ ⟨L, hL, rfl⟩ c ⟨hcB, hcN⟩
    by_cases hLc : L.map (MulAut.conj c).toMonoidHom = L
    · have h1 : c ∈ A ⊓ Subgroup.normalizer (L : Set G) :=
        ⟨hB.1 hcB, L69.map_conj_eq_self_iff.mp hLc⟩
      rw [hNL L hL] at h1
      have h2 : c ∈ B ⊓ (Subgroup.zpowers b ⊔ E) := ⟨hcB, h1⟩
      rw [h.inf_sup_eq_of_le S.mem.1 hB.1 hEB (Subgroup.zpowers_le.mpr hb)] at h2
      have hLc' : L ⊓ Subgroup.centralizer (E : Set G) ≤
          Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
        rw [centralizer_zpowers_eq_singleton]
        exact inf_le_left.trans ((lcal_le hL).trans (h.isFunctor.le_centralizer b hbA hb1))
      exact Subgroup.le_centralizer_iff.mp hLc' h2
    · have hLc2 : L.map (MulAut.conj c).toMonoidHom ∈ lcal (θ b) :=
        map_conj_mem_lcal hL (hAN (hB.1 hcB))
      have hmemd : L.map (MulAut.conj c).toMonoidHom ∈ lcal (θ b) \ {L} := ⟨hLc2, hLc⟩
      have hbot : L ⊓ L.map (MulAut.conj c).toMonoidHom = ⊥ := by
        have hdis := hK.indep hL
        rw [← disjoint_iff]
        exact hdis.mono_right (le_sSup hmemd)
      have hJ : L ⊓ Subgroup.centralizer (E : Set G) = ⊥ := by
        have h1 := L69.map_conj_eq_self_iff.mpr hcN
        rw [hmapinf c hcB L] at h1
        refine eq_bot_iff.mpr ?_
        intro x hx
        have hx' : x ∈ L.map (MulAut.conj c).toMonoidHom ⊓ Subgroup.centralizer (E : Set G) := by
          rw [h1]
          exact hx
        have : x ∈ L ⊓ L.map (MulAut.conj c).toMonoidHom := ⟨hx.1, hx'.1⟩
        rw [hbot] at this
        exact this
      rw [hJ]
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have hx1 : x = 1 := by simpa using hx
      rw [hx1, one_mul, mul_one]
  obtain ⟨e⟩ := T614.nonempty_pi_mulEquiv hX hperm htrans hker
  have hZ : thetaTilde θ E b ⊓ Subgroup.centralizer (B : Set G) =
      thetaOf (thetaTilde θ E) B := by
    have := (h.isFunctor_thetaTilde S hB hEB).inf_centralizer_eq_thetaOf hb hb1 (le_refl B)
    rwa [sup_eq_right.mpr (Subgroup.zpowers_le.mpr hb)] at this
  rw [← hXeq] at hX
  rw [← hXeq, hZ] at e
  by_cases hX0 : thetaTilde θ E b = ⊥
  · have hZ0 : thetaOf (thetaTilde θ E) B = ⊥ := le_bot_iff.mp (hX0 ▸ thetaOf_le_apply hb hb1)
    have h1 : Subsingleton ↥(thetaTilde θ E b) := by rw [hX0]; infer_instance
    have h2 : Subsingleton ↥(thetaOf (thetaTilde θ E) B) := by rw [hZ0]; infer_instance
    exact T614.nonempty_mulEquiv_of_subsingleton
  · have hne : ∀ L ∈ lcal (θ b), L ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨L₁, hL₁, hL₁bot⟩ := hcon
      have hall : ∀ L ∈ lcal (θ b), L ⊓ Subgroup.centralizer (E : Set G) = ⊥ := by
        intro L hL
        obtain ⟨c, hc, rfl⟩ := htransL L₁ hL₁ L hL
        rw [← hmapinf c hc L₁, hL₁bot, Subgroup.map_bot]
      have hbot : sSup SX = ⊥ := by
        refine le_bot_iff.mp (sSup_le ?_)
        rintro _ ⟨L, hL, rfl⟩
        rw [hall L hL]
      exact hX0 (hX.sSup_eq.symm.trans hbot)
    have hinj : Set.InjOn (fun L : Subgroup G => L ⊓ Subgroup.centralizer (E : Set G))
        (lcal (θ b)) := by
      intro L hL L' hL' hEq
      by_contra hne'
      have hmemd : L' ∈ lcal (θ b) \ {L} := ⟨hL', Ne.symm hne'⟩
      have hdis : Disjoint L L' := (hK.indep hL).mono_right (le_sSup hmemd)
      apply hne L hL
      refine eq_bot_iff.mpr fun x hx => ?_
      have hEq' : L ⊓ Subgroup.centralizer (E : Set G) = L' ⊓ Subgroup.centralizer (E : Set G) :=
        hEq
      have hx' : x ∈ L' ⊓ Subgroup.centralizer (E : Set G) := by
        rw [← hEq']
        exact hx
      have hxx : x ∈ L ⊓ L' := ⟨hx.1, hx'.1⟩
      rw [disjoint_iff.mp hdis] at hxx
      exact hxx
    have hSXcard : Nat.card SX = p := by
      have himg : SX = (fun L : Subgroup G => L ⊓ Subgroup.centralizer (E : Set G)) ''
          lcal (θ b) := by
        ext Y
        constructor
        · rintro ⟨J, hJ, hY⟩
          exact ⟨J, hJ, hY.symm⟩
        · rintro ⟨J, hJ, hY⟩
          exact ⟨J, hJ, hY.symm⟩
      rw [himg, Nat.card_image_of_injOn hinj, hcard]
    rw [hSXcard] at e
    exact ⟨e⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
