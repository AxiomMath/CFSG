module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin

namespace B69

@[expose] def kleinStd : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {σ | σ = 1 ∨ σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨
    σ = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ σ = Equiv.swap 0 3 * Equiv.swap 1 2}
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide

theorem mem_kleinStd {σ : Equiv.Perm (Fin 5)} : σ ∈ kleinStd ↔
    σ = 1 ∨ σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ σ = Equiv.swap 0 2 * Equiv.swap 1 3 ∨
      σ = Equiv.swap 0 3 * Equiv.swap 1 2 := Iff.rfl

theorem kleinStd_le_alternatingGroup : kleinStd ≤ alternatingGroup (Fin 5) := by
  intro σ hσ
  rw [Equiv.Perm.mem_alternatingGroup]
  rcases mem_kleinStd.1 hσ with rfl | rfl | rfl | rfl <;>
    simp [Equiv.Perm.sign_mul]

theorem card_kleinStd : Nat.card kleinStd = 4 := by
  have h : (kleinStd : Set (Equiv.Perm (Fin 5))) =
      ↑({1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
        Equiv.swap 0 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 5))) := by
    ext σ
    simp [mem_kleinStd, SetLike.mem_coe]
  have h2 : Nat.card kleinStd = (kleinStd : Set (Equiv.Perm (Fin 5))).ncard :=
    Nat.card_coe_set_eq _
  rw [h2, h, Set.ncard_coe_finset]
  decide

theorem kleinStd_apply_four {σ : Equiv.Perm (Fin 5)} (h : σ ∈ kleinStd) : σ 4 = 4 := by
  rcases mem_kleinStd.1 h with rfl | rfl | rfl | rfl <;> decide

private theorem act_inv_act {Γ X : Type*} [Group Γ] [CommGroup X] (a : Γ →* MulAut X) (g : Γ)
    (x : X) : a g⁻¹ (a g x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

private theorem act_act_inv {Γ X : Type*} [Group Γ] [CommGroup X] (a : Γ →* MulAut X) (g : Γ)
    (x : X) : a g (a g⁻¹ x) = x := by
  simp

theorem avg_section {Γ : Type*} [Group Γ] [Finite Γ] {W S : Type*} [CommGroup W] [CommGroup S]
    (actW : Γ →* MulAut W) (actS : Γ →* MulAut S) (Φ : W →* S)
    (hΦ : ∀ (g : Γ) (w : W), Φ (actW g w) = actS g (Φ w))
    (hS2 : ∀ s : S, s ^ 2 = 1) (Q : Subgroup Γ) (hQ : ¬ 2 ∣ Q.index)
    (σ : S →* W) (hσ : ∀ s, Φ (σ s) = s)
    (hσQ : ∀ q ∈ Q, ∀ s, σ (actS q s) = actW q (σ s)) :
    ∃ σ' : S →* W, (∀ s, Φ (σ' s) = s) ∧ ∀ (g : Γ) (s : S), σ' (actS g s) = actW g (σ' s) := by
  classical
  have : Fintype (Γ ⧸ Q) := Fintype.ofFinite _
  let f : Γ → S →* W := fun g =>
    { toFun := fun s => actW g (σ (actS g⁻¹ s))
      map_one' := by simp
      map_mul' := fun x y => by simp }
  have hf : ∀ g s, f g s = actW g (σ (actS g⁻¹ s)) := fun g s => rfl
  have hfQ : ∀ g, ∀ q ∈ Q, ∀ s, f (g * q) s = f g s := by
    intro g q hq s
    rw [hf, hf, mul_inv_rev, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, ← hσQ q hq,
      act_act_inv actS q]
  have hfg : ∀ g h s, actW g (f h s) = f (g * h) (actS g s) := by
    intro g h s
    rw [hf, hf, mul_inv_rev, map_mul actW, map_mul actS, MulAut.mul_apply, MulAut.mul_apply,
      act_inv_act actS g]
  refine ⟨∏ c : Γ ⧸ Q, f c.out, ?_, ?_⟩
  · intro s
    rw [MonoidHom.finsetProd_apply, map_prod]
    have h1 : ∀ c : Γ ⧸ Q, Φ (f c.out s) = s := by
      intro c
      rw [hf, hΦ, hσ, act_act_inv actS]
    rw [Finset.prod_congr rfl (fun c _ => h1 c), Finset.prod_const, Finset.card_univ]
    have hcard : Fintype.card (Γ ⧸ Q) = Q.index := by
      rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    rw [hcard]
    obtain ⟨k, hk⟩ : ∃ k, Q.index = 2 * k + 1 := by
      rcases Nat.even_or_odd' Q.index with ⟨k, hk | hk⟩
      · exact absurd ⟨k, hk⟩ hQ
      · exact ⟨k, hk⟩
    rw [hk, pow_succ, pow_mul, hS2, one_pow, one_mul]
  · intro g s
    rw [MonoidHom.finsetProd_apply, MonoidHom.finsetProd_apply, map_prod]
    have h2 : ∀ c : Γ ⧸ Q, actW g (f c.out s) = f (g • c).out (actS g s) := by
      intro c
      have hq : (g * c.out)⁻¹ * (g • c).out ∈ Q := by
        rw [← QuotientGroup.eq]
        have h3 : (QuotientGroup.mk (g • c.out) : Γ ⧸ Q) = g • c :=
          MulAction.Quotient.mk_smul_out Q g c
        rw [smul_eq_mul] at h3
        rw [h3, QuotientGroup.out_eq']
      have h4 : (g • c).out = g * c.out * ((g * c.out)⁻¹ * (g • c).out) := by group
      rw [h4, hfQ _ _ hq, hfg]
    rw [Finset.prod_congr rfl (fun c _ => h2 c)]
    exact (Equiv.prod_comp (MulAction.toPerm g) (fun c : Γ ⧸ Q => f c.out (actS g s))).symm

private def bvec (i : Fin 5) : G6.PermMod 5 :=
  Multiplicative.ofAdd (Pi.single i 1 + Pi.single 4 1)

private theorem bvec_mem (i : Fin 5) : bvec i ∈ G6.coreMod 5 := by
  rw [G6.mem_coreMod]
  revert i
  decide

private def bas (i : Fin 5) : G6.coreMod 5 := ⟨bvec i, bvec_mem i⟩

private theorem bas_four : bas 4 = 1 := by
  apply Subtype.ext
  show bvec 4 = 1
  decide

private theorem coreAct_bas {κ : Equiv.Perm (Fin 5)} (hκ : κ 4 = 4) (j : Fin 5) :
    G6.coreAct 5 κ (bas j) = bas (κ j) := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext k
  simp [G6.coreAct_coe, G6.permAct_apply, bas, bvec, Pi.single_apply, Equiv.symm_apply_eq, hκ]

private theorem toAdd_pow_val (x : G6.PermMod 5) (n : ZMod 2) (k : Fin 5) :
    Multiplicative.toAdd (x ^ n.val) k = n * Multiplicative.toAdd x k := by
  rw [toAdd_pow, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]

private theorem sum_decomp (x : Fin 5 → ZMod 2) (hx : ∑ i, x i = 0) (k : Fin 5) :
    ∑ i : Fin 5, x i * ((Pi.single i 1 + Pi.single 4 1 : Fin 5 → ZMod 2) k) = x k := by
  rw [Fin.sum_univ_five] at hx ⊢
  fin_cases k <;> simp
  linear_combination hx

private theorem prod_bas (t : G6.coreMod 5) :
    ∏ i : Fin 5, bas i ^ (Multiplicative.toAdd (t : G6.PermMod 5) i).val = t := by
  have ht := G6.mem_coreMod.1 t.2
  apply Subtype.ext
  have h := map_prod (G6.coreMod 5).subtype
    (fun i : Fin 5 => bas i ^ (Multiplicative.toAdd (t : G6.PermMod 5) i).val) Finset.univ
  simp only [Subgroup.coe_subtype] at h
  rw [h]
  apply Multiplicative.toAdd.injective
  funext k
  rw [toAdd_prod, Finset.sum_apply]
  simp only [Subgroup.coe_pow, toAdd_pow_val]
  exact sum_decomp _ ht k

private theorem pow_val_add {W : Type*} [CommGroup W] (w : W) (hw : w ^ 2 = 1) (a b : ZMod 2) :
    w ^ (a + b).val = w ^ a.val * w ^ b.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hw]

private def coordPow {W : Type*} [CommGroup W] (w : W) (hw : w ^ 2 = 1) (i : Fin 5) :
    G6.coreMod 5 →* W :=
  MonoidHom.mk' (fun t => w ^ (Multiplicative.toAdd (t : G6.PermMod 5) i).val) (fun a b => by
    rw [← pow_val_add w hw]
    rfl)

private def kseq : Fin 5 → Equiv.Perm (Fin 5) :=
  ![1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2, 1]

private theorem kseq_mem (i : Fin 5) : kseq i ∈ kleinStd := by
  rw [mem_kleinStd]
  revert i
  decide

private theorem kseq_zero (i : Fin 5) (hi : i ≠ 4) : kseq i 0 = i := by
  revert i
  decide

private theorem kseq_mul {κ : Equiv.Perm (Fin 5)} (hκ : κ ∈ kleinStd) (i : Fin 5) (hi : i ≠ 4) :
    κ * kseq i = kseq (κ i) := by
  rcases mem_kleinStd.1 hκ with rfl | rfl | rfl | rfl <;> revert i <;> decide

theorem exists_sec_klein {Γ : Type*} [Group Γ] {W S : Type*} [CommGroup W] [CommGroup S]
    (actW : Γ →* MulAut W) (actS : Γ →* MulAut S) (Φ : W →* S) (hΦs : Function.Surjective Φ)
    (hΦ : ∀ (g : Γ) (w : W), Φ (actW g w) = actS g (Φ w)) (hW2 : ∀ w : W, w ^ 2 = 1)
    (e : S ≃* ↥(G6.coreMod 5)) (ρ : Γ →* Equiv.Perm (Fin 5))
    (hρe : ∀ (g : Γ) (s : S), e (actS g s) = G6.coreAct 5 (ρ g) (e s))
    (hρs : ∀ σ ∈ kleinStd, ∃ g : Γ, ρ g = σ)
    (htriv : ∀ (g : Γ), ρ g = 1 → ∀ w : W, actW g w = w) :
    ∃ σ : S →* W, (∀ s, Φ (σ s) = s) ∧
      ∀ (g : Γ), ρ g ∈ kleinStd → ∀ s : S, σ (actS g s) = actW g (σ s) := by
  classical
  have hact : ∀ g g' : Γ, ρ g = ρ g' → ∀ w : W, actW g w = actW g' w := by
    intro g g' h w
    have h1 : ρ (g'⁻¹ * g) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    calc actW g w = actW g' (actW (g'⁻¹ * g) w) := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = actW g' w := by rw [htriv _ h1]
  have hsymm : ∀ (g : Γ) (y : G6.coreMod 5),
      actS g (e.symm y) = e.symm (G6.coreAct 5 (ρ g) y) := by
    intro g y
    apply e.injective
    rw [hρe, e.apply_symm_apply, e.apply_symm_apply]
  choose g0 hg0 using fun i : Fin 5 => hρs (kseq i) (kseq_mem i)
  obtain ⟨w0, hw0⟩ := hΦs (e.symm (bas 0))
  let ω : Fin 5 → W := fun i => if i = 4 then 1 else actW (g0 i) w0
  have hω4 : ω 4 = 1 := by simp [ω]
  have hω : ∀ i, i ≠ 4 → ω i = actW (g0 i) w0 := fun i hi => by simp [ω, hi]
  have hωg : ∀ g : Γ, ρ g ∈ kleinStd → ∀ i, actW g (ω i) = ω (ρ g i) := by
    intro g hg i
    by_cases hi : i = 4
    · subst hi
      rw [kleinStd_apply_four hg, hω4, map_one]
    · have hi' : ρ g i ≠ 4 := by
        intro h4
        exact hi ((ρ g).injective (h4.trans (kleinStd_apply_four hg).symm))
      rw [hω i hi, hω _ hi', ← MulAut.mul_apply, ← map_mul]
      exact hact _ _ (by rw [map_mul, hg0, hg0]; exact kseq_mul hg i hi) w0
  have hΦω : ∀ i, Φ (ω i) = e.symm (bas i) := by
    intro i
    by_cases hi : i = 4
    · subst hi
      rw [hω4, map_one, bas_four, map_one]
    · rw [hω i hi, hΦ, hw0, hsymm, hg0, coreAct_bas (kleinStd_apply_four (kseq_mem i)),
        kseq_zero i hi]
  let hom : Fin 5 → G6.coreMod 5 →* W := fun i => coordPow (ω i) (hW2 _) i
  have hσ : ∀ s : S, ((∏ i, hom i).comp e.toMonoidHom) s =
      ∏ i : Fin 5, ω i ^ (Multiplicative.toAdd ((e s : G6.coreMod 5) : G6.PermMod 5) i).val := by
    intro s
    rw [MonoidHom.comp_apply, MonoidHom.finsetProd_apply]
    rfl
  refine ⟨(∏ i, hom i).comp e.toMonoidHom, ?_, ?_⟩
  · intro s
    rw [hσ, map_prod]
    have h1 : ∀ i : Fin 5,
        Φ (ω i ^ (Multiplicative.toAdd ((e s : G6.coreMod 5) : G6.PermMod 5) i).val) =
          e.symm (bas i ^ (Multiplicative.toAdd ((e s : G6.coreMod 5) : G6.PermMod 5) i).val) := by
      intro i
      rw [map_pow, hΦω, map_pow]
    rw [Finset.prod_congr rfl (fun i _ => h1 i), ← map_prod, prod_bas, e.symm_apply_apply]
  · intro g hg s
    rw [hσ, hσ, map_prod]
    have hcoord : ∀ i : Fin 5,
        Multiplicative.toAdd ((e (actS g s) : G6.coreMod 5) : G6.PermMod 5) i =
          Multiplicative.toAdd ((e s : G6.coreMod 5) : G6.PermMod 5) ((ρ g)⁻¹ i) := by
      intro i
      rw [hρe]
      rfl
    simp only [hcoord, map_pow, hωg g hg]
    rw [← Equiv.prod_comp (ρ g) (fun j => ω j ^
      (Multiplicative.toAdd ((e s : G6.coreMod 5) : G6.PermMod 5) ((ρ g)⁻¹ j)).val)]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]

end B69

end CFSG.Quasithin
