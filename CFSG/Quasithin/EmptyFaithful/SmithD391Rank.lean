module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S153ZE
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391

variable {X : Type*} [CommGroup X]

theorem exists_gen_mod [Finite X] (hX : ∀ x : X, x ^ 2 = 1) {U : Subgroup X} :
    ∀ (k : ℕ) (C : Subgroup X), C ≤ U → rk ↥U = rk ↥C + k →
      ∃ x : Fin k → X, (∀ i, x i ∈ U) ∧ C ⊔ Subgroup.closure (Set.range x) = U
  | 0, C, hCU, hrk => by
    refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
    rw [Set.range_eq_empty, Subgroup.closure_empty, sup_bot_eq]
    exact eq_of_le_of_rk_le hX hCU (by omega)
  | k + 1, C, hCU, hrk => by
    have hne : C ≠ U := by
      intro h
      subst h
      omega
    obtain ⟨s, hsU, hsC⟩ : ∃ s ∈ U, s ∉ C := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm hCU hcon)
    set C' := C ⊔ Subgroup.zpowers s with hC'
    have hC'U : C' ≤ U := sup_le hCU (Subgroup.zpowers_le.2 hsU)
    have hs1 : s ≠ 1 := fun h => hsC (h ▸ C.one_mem)
    have hord : orderOf s = 2 := orderOf_eq_prime (hX s) hs1
    have hrks : rk ↥(Subgroup.zpowers s) = 1 := by
      unfold rk
      rw [Nat.card_zpowers, hord]
      simp
    have hinf : rk ↥(C ⊓ Subgroup.zpowers s) = 0 := by
      by_contra h0
      have h1 : rk ↥(C ⊓ Subgroup.zpowers s) ≤ 1 := hrks ▸ rk_mono inf_le_right
      have h2 : C ⊓ Subgroup.zpowers s = Subgroup.zpowers s :=
        eq_of_le_of_rk_le hX inf_le_right (by omega)
      apply hsC
      have : s ∈ C ⊓ Subgroup.zpowers s := by rw [h2]; exact Subgroup.mem_zpowers s
      exact this.1
    have hrkC' : rk ↥C' = rk ↥C + 1 := by
      have h := rk_sup_add_rk_inf C (Subgroup.zpowers s)
      rw [← hC'] at h
      omega
    obtain ⟨x', hx'U, hx'⟩ := exists_gen_mod hX k C' hC'U (by omega)
    refine ⟨Fin.cons s x', fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact hsU
      · exact hx'U j
    · refine le_antisymm (sup_le hCU ?_) ?_
      · rw [Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hsU
        · exact hx'U j
      · rw [← hx', hC']
        refine sup_le (sup_le le_sup_left ?_) ?_
        · refine le_sup_of_le_right (Subgroup.zpowers_le.2 (Subgroup.subset_closure ⟨0, rfl⟩))
        · refine le_sup_of_le_right (Subgroup.closure_mono ?_)
          rintro _ ⟨j, rfl⟩
          exact ⟨j.succ, rfl⟩

theorem rk_le_mul_of_faithful [Finite X] (hX : ∀ x : X, x ^ 2 = 1) {F : Subgroup (MulAut X)}
    {U : Subgroup X} (hfaith : ∀ f ∈ F, (∀ u ∈ U, f u = u) → f = 1) :
    rk ↥F ≤ (rk ↥U - rk ↥(U ⊓ fixV F)) * rk ↥(commSub U F) := by
  classical
  set C := U ⊓ fixV F with hCdef
  set α := rk ↥U - rk ↥C with hα
  have hrk : rk ↥U = rk ↥C + α := by
    have h1 : rk ↥C ≤ rk ↥U := rk_mono inf_le_left
    omega
  obtain ⟨x, hxU, hgen⟩ := exists_gen_mod hX α C inf_le_left hrk
  let Φ : ↥F → (Fin α → ↥(commSub U F)) := fun f i =>
    ⟨(f : MulAut X) (x i) * (x i)⁻¹, Subgroup.subset_closure ⟨f, f.2, x i, hxU i, rfl⟩⟩
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    have hi : ∀ i, (f : MulAut X) (x i) = (g : MulAut X) (x i) := by
      intro i
      have h1 := congrArg Subtype.val (congrFun hfg i)
      exact mul_right_cancel h1
    set φ : MulAut X := (g : MulAut X)⁻¹ * f with hφ
    have hle : U ≤ MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id X) := by
      rw [← hgen]
      refine sup_le (fun c hc => ?_) ?_
      · show φ c = c
        have hfc : (f : MulAut X) c = c := (mem_fixV.1 hc.2) f f.2
        have hgc : (g : MulAut X) c = c := (mem_fixV.1 hc.2) g g.2
        have hgc' : (g : MulAut X)⁻¹ c = c := by
          nth_rewrite 1 [← hgc]
          exact MulAut.inv_apply_self _ _ _
        rw [hφ, MulAut.mul_apply, hfc, hgc']
      · rw [Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        show φ (x i) = x i
        rw [hφ, MulAut.mul_apply, hi i, MulAut.inv_apply_self]
    have h1 : φ = 1 := hfaith φ (F.mul_mem (F.inv_mem g.2) f.2) fun u hu => hle hu
    apply Subtype.ext
    rw [hφ, inv_mul_eq_one] at h1
    exact h1.symm
  have hcard := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin α), Fintype.card_fin,
    card_eq_two_pow hX (commSub U F), ← pow_mul] at hcard
  have h3 : 2 ^ rk ↥F ≤ Nat.card ↥F := Nat.le_of_dvd Nat.card_pos pow_padicValNat_dvd
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (h3.trans hcard)
  rw [mul_comm] at h4
  exact h4

theorem rk_le_mul_of_quadratic [Finite X] (hX : ∀ x : X, x ^ 2 = 1) {F : Subgroup (MulAut X)}
    {U : Subgroup X} (hFU : ∀ f ∈ F, ∀ u ∈ U, f u ∈ U) (hq : commSub U F ≤ fixV F)
    (hfaith : ∀ f ∈ F, (∀ u ∈ U, f u = u) → f = 1) :
    rk ↥F ≤ (rk ↥U - rk ↥(U ⊓ fixV F)) * (rk ↥U - (rk ↥U - rk ↥(U ⊓ fixV F))) := by
  have h1 := rk_le_mul_of_faithful hX hfaith
  have hcU : commSub U F ≤ U := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨f, hf, u, hu, rfl⟩
    exact U.mul_mem (hFU f hf u hu) (U.inv_mem hu)
  have h2 : rk ↥(commSub U F) ≤ rk ↥(U ⊓ fixV F) := rk_mono (le_inf hcU hq)
  have h3 : rk ↥(U ⊓ fixV F) ≤ rk ↥U := rk_mono inf_le_left
  have h4 : rk ↥U - (rk ↥U - rk ↥(U ⊓ fixV F)) = rk ↥(U ⊓ fixV F) := by omega
  rw [h4]
  exact h1.trans (Nat.mul_le_mul_left _ h2)

end CFSG.Quasithin.SmithD391
