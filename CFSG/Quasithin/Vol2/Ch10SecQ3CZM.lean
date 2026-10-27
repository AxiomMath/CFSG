module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZL
public import CFSG.Quasithin.Vol2.Ch10SecQ3CZK

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}
  {c : Ctx T L I H K n k b hel I' K₀} {t : G} {L₁ : Subgroup G}

omit [Finite G] in
theorem mem_map_conj_iff {X : Subgroup G} {g x : G} :
    x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ X := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

omit [Finite G] in
theorem mem_normalizer_map_conj {X : Subgroup G} {g y : G}
    (hy : g⁻¹ * y * g ∈ Subgroup.normalizer (X : Set G)) :
    y ∈ Subgroup.normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have e : g⁻¹ * (y * x * y⁻¹) * g = (g⁻¹ * y * g) * (g⁻¹ * x * g) * (g⁻¹ * y * g)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hy _

omit [Finite G] in
theorem odd_orderOf_conj {t b : G} (hb : Odd (orderOf b)) : Odd (orderOf (t * b * t⁻¹)) := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  exact hb

theorem Ctx.hKF_n (c : Ctx T L I H K n k b hel I' K₀) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  have h := c.hKF
  rwa [c.s7.1] at h

namespace Ctx9

variable (d : Ctx9 c t L₁)
include d

omit [Finite G] d in
theorem T_le_L0T : T ≤ fsuL0 T L ⊔ T := le_sup_right

theorem L₁_mem_cComp : L₁ ∈ cComp (fsuL0 T L ⊔ T) := by
  rcases d.hL₁ with rfl | rfl
  · exact SecE.mem_cComp_L0T c.hyp
  · exact H13.LocDbl.map_conj_mem_cComp (SecE.mem_cComp_L0T c.hyp)
      (Subgroup.le_normalizer (T_le_L0T (T.inv_mem d.ht)))

theorem L₂_mem_cComp : L₁.map (MulAut.conj t).toMonoidHom ∈ cComp (fsuL0 T L ⊔ T) :=
  H13.LocDbl.map_conj_mem_cComp d.L₁_mem_cComp (Subgroup.le_normalizer (T_le_L0T d.ht))

theorem t_not_mem_normalizer_L₁ : t ∉ Subgroup.normalizer (L₁ : Set G) := by
  rcases d.hL₁ with rfl | rfl
  · exact d.htn
  · intro h
    apply d.htn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp h (t⁻¹ * x * t)
    rw [SecA.mem_conjugate_iff, SecA.mem_conjugate_iff] at h1
    simpa [mul_assoc] using h1

theorem L₂_ne : L₁.map (MulAut.conj t).toMonoidHom ≠ L₁ := fun h =>
  d.t_not_mem_normalizer_L₁ (A38.map_conj_eq_iff.mp h)

theorem L₂_short : IsShort2 (L₁.map (MulAut.conj t).toMonoidHom) :=
  (Lin2.isShort2_map_equiv_iff (MulAut.conj t) L₁).mpr d.hL₁blk.1

theorem L₁_quasisimple :
    CFSG.IsQuasisimple (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) := by
  refine d.hL₁blk.1.2.2.2.1.resolve_right fun h3 => ?_
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := d.hL₁blk.2.1
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hαk).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  rw [Nat.card_congr e.toEquiv, SecA.card_SL_two_pow hF'] at h3
  have hn := c.h1.1
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h5 : 16 ≤ 4 ^ n := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h6 : 4 * 15 ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h4 (by omega)
  omega

theorem commutator_L :
    ⁅L₁, L₁.map (MulAut.conj t).toMonoidHom⁆ = ⊥ :=
  SecF.C10P4F.commutator_eq_bot_of_mem_cComp d.L₁_mem_cComp d.L₂_mem_cComp d.hL₁blk.1
    d.L₂_short d.L₁_quasisimple d.L₂_ne.symm

theorem comm_L {x y : G} (hx : x ∈ L₁)
    (hy : y ∈ L₁.map (MulAut.conj t).toMonoidHom) : y * x * y⁻¹ = x := by
  have h := Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp d.commutator_L hx) y hy
  rw [h, mul_inv_cancel_right]

theorem b₂_mem_L₂ : t * b * t⁻¹ ∈ L₁.map (MulAut.conj t).toMonoidHom :=
  ⟨b, d.hbL₁, rfl⟩

theorem K₂_mem_cComp : K.map (MulAut.conj t).toMonoidHom ∈ cComp H :=
  H13.LocDbl.map_conj_mem_cComp c.hKc (Subgroup.le_normalizer (c.T_le_H d.ht))

theorem b_centralizes_K₂ :
    ∀ x ∈ K.map (MulAut.conj t).toMonoidHom, b * x * b⁻¹ = x := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := c.hKF_n
  have hbN : b ∈ Subgroup.normalizer
      ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    H13.LocDbl.le_normalizer_of_mem_cComp d.K₂_mem_cComp c.hKc c.hbK
  refine centralizes_of_sylow hF ⟨(C10P34.conjQuot K _ t rfl).symm.trans e⟩
    (isSylowTwoOf_map_conj d.hS₁K t) hbN c.hbo fun s hs => ?_
  obtain ⟨s₀, hs₀, rfl⟩ := hs
  have h := d.comm_L d.hbL₁ (⟨s₀, d.hS₁L₁.1 hs₀, rfl⟩ :
    (MulAut.conj t).toMonoidHom s₀ ∈ L₁.map (MulAut.conj t).toMonoidHom)
  have h' := mul_inv_eq_iff_eq_mul.mp h
  rw [← h', mul_inv_cancel_right]

theorem K₂_ne : K.map (MulAut.conj t).toMonoidHom ≠ K := by
  intro h
  obtain ⟨F, _, _, hF, he⟩ := c.hKF_n
  have hb1 := eq_one_of_centralizes hF he c.hbK c.hbo
    (fun x hx => d.b_centralizes_K₂ x (by rw [h]; exact hx))
  have ho := c.orderOf_b
  rw [hb1, orderOf_one] at ho
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) c.h1.1
  omega

theorem commutator_K :
    ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
    refine d.hKblk.1.2.2.2.1.resolve_right fun h3 => ?_
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := c.hKF_n
    rw [Nat.card_congr e.toEquiv, SecA.card_SL_two_pow hF] at h3
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) c.h1.1
    have h5 : 2 ≤ 4 ^ n - 1 := by
      have : 4 ≤ 4 ^ n := Nat.le_self_pow (by have := c.h1.1; omega) 4
      omega
    have h6 : 4 * 2 ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h4 h5
    omega
  exact SecF.C10P4F.commutator_eq_bot_of_mem_cComp c.hKc d.K₂_mem_cComp d.hKblk.1
    ((Lin2.isShort2_map_equiv_iff (MulAut.conj t) K).mpr d.hKblk.1) hq d.K₂_ne.symm

end Ctx9

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
