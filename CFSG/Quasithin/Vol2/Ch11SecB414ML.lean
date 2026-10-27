module

public import CFSG.Quasithin.Vol2.Ch11SecB414MK
public import CFSG.Quasithin.Vol2.Ch11SecB414MD
public import CFSG.Quasithin.Vol2.Ch11SecB414ME

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix

variable {F : Type} [Field F] {G : Type} [Group G] {Γ V Z L X : Subgroup G} {k : ℕ}
  {α : ↥Γ →* PGL3 F} (m : Model Γ V Z F k α)

@[expose] def Model.coord (W : AddSubgroup (Matrix (Fin 3) (Fin 3) F))
    (κ : Matrix (Fin 3) (Fin 3) F →+ (Fin 2 → F)) : ↥(m.pre W) →* Multiplicative (Fin 2 → F) where
  toFun s := Multiplicative.ofAdd (κ (Multiplicative.toAdd (m.β ⟨s, s.2.1⟩)))
  map_one' := by
    have : m.β (⟨((1 : ↥(m.pre W)) : G), (1 : ↥(m.pre W)).2.1⟩ : ↥V) = 1 := map_one m.β
    simp only [this, toAdd_one, map_zero, ofAdd_zero]
  map_mul' s t := by
    have : m.β (⟨((s * t : ↥(m.pre W)) : G), (s * t).2.1⟩ : ↥V) =
        m.β ⟨s, s.2.1⟩ * m.β ⟨t, t.2.1⟩ := map_mul m.β ⟨s, s.2.1⟩ ⟨t, t.2.1⟩
    simp only [this, toAdd_mul, map_add, ofAdd_add]

theorem Model.toAdd_coord (W : AddSubgroup (Matrix (Fin 3) (Fin 3) F))
    (κ : Matrix (Fin 3) (Fin 3) F →+ (Fin 2 → F)) (s : ↥(m.pre W)) :
    Multiplicative.toAdd (m.coord W κ s) = κ (Multiplicative.toAdd (m.β ⟨s, s.2.1⟩)) := rfl

variable [Finite F] [CharP F 2]

theorem Model.isNatEigSection_layer (hF : Nat.card F = 4) (hLΓ : L ≤ Γ)
    (hL : (L.subgroupOf Γ).map α = Ptheta F 0) {W W' : AddSubgroup (Matrix (Fin 3) (Fin 3) F)}
    (κ : Matrix (Fin 3) (Fin 3) F →+ (Fin 2 → F))
    (hsurj : ∀ v : Fin 2 → F, ∃ M ∈ W', M.trace = 0 ∧ κ M = v)
    (hker : ∀ M ∈ W', κ M = 0 ↔ M ∈ W)
    (hcnj : ∀ A : Matrix (Fin 3) (Fin 3) F, A 1 0 = 0 → A 2 0 = 0 → A.det = 1 →
      ∀ M ∈ W', κ (cnj A M) = rhoA A *ᵥ κ M)
    (α₀' : ↥(Ptheta F 0) →* ↥(StatedSL 2 F)) (α₀ : ↥L →* ↥(StatedSL 2 F))
    (hcomp : ∀ (l : ↥L) (γ : ↥Γ) (p : ↥(Ptheta F 0)), (γ : G) = l →
      (p : PGL3 F) = α γ → α₀ l = α₀' p)
    (T : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hT : ∀ (p : ↥(Ptheta F 0)) (v : Fin 2 → F),
      T (((rhoRef hF p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (((α₀' p : StatedSL 2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ T v)
    {γx : ↥Γ} {c : Fˣ} (hγx : α γx = ProjGenLinGroup.mk (dgHom c)) {a μ : F}
    (hdg : ∀ M ∈ W', κ (twAdj k (dgHom c) M) = a • κ M)
    (hμ : ∀ w : Fin 2 → F, T (a • w) = μ • T w) :
    IsNatEigSection L (γx : G) α₀ (m.pre W) (m.pre W') μ := by
  have hP : ∀ l : ↥L, α ⟨l, hLΓ l.2⟩ ∈ Ptheta F 0 := fun l => by
    rw [← hL]
    exact ⟨⟨l, hLΓ l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  refine isNatEigSection_of_coords α₀ (m.coord W' κ) ?_ ?_
    (fun l => ((rhoRef hF ⟨_, hP l⟩ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    ?_ T (fun l v => by rw [hT, hcomp l ⟨l, hLΓ l.2⟩ ⟨_, hP l⟩ rfl rfl]) ?_ hμ
  · intro w
    obtain ⟨M, hM, hMt, hκ⟩ := hsurj (Multiplicative.toAdd w)
    obtain ⟨v, hv⟩ := m.onto M hMt
    refine ⟨⟨v, v.2, hv ▸ hM⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [Model.toAdd_coord]
    show κ (Multiplicative.toAdd (m.β v)) = _
    rw [hv, hκ]
  · intro s
    rw [show m.coord W' κ s = 1 ↔ κ (Multiplicative.toAdd (m.β ⟨s, s.2.1⟩)) = 0 from
      ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩,
      hker _ s.2.2]
    exact ⟨fun h => ⟨s.2.1, h⟩, fun ⟨_, h⟩ => h⟩
  · intro l s s' hs'
    obtain ⟨A, h10, h20, hA⟩ := exists_rep_of_mem_L hLΓ hL l.2
    rw [Model.toAdd_coord, Model.toAdd_coord,
      m.act ⟨l, hLΓ l.2⟩ ⟨s, s.2.1⟩ ⟨s', s'.2.1⟩ hs' _ hA, twAdj_toGL,
      hcnj _ h10 h20 A.prop _ s.2.2, rhoRef_eq hF _ hA, rhoMatG_toGL]
  · intro s s' hs'
    rw [Model.toAdd_coord, Model.toAdd_coord, m.act γx ⟨s, s.2.1⟩ ⟨s', s'.2.1⟩ hs' _ hγx.symm,
      hdg _ s.2.2]

omit [Finite F] [CharP F 2] in
theorem pow_four_eq (hF : Nat.card F = 4) (x : F) : x ^ 4 = x := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [pow_succ, pow_three_eq_one hF hx, one_mul]

omit [Finite F] [CharP F 2] in
@[expose] def kpHom : Matrix (Fin 3) (Fin 3) F →+ (Fin 2 → F) where
  toFun := kp
  map_zero' := by funext i; fin_cases i <;> rfl
  map_add' M N := by funext i; fin_cases i <;> rfl

omit [Finite F] [CharP F 2] in
@[expose] def kmHom : Matrix (Fin 3) (Fin 3) F →+ (Fin 2 → F) where
  toFun := km
  map_zero' := by funext i; fin_cases i <;> rfl
  map_add' M N := by funext i; fin_cases i <;> rfl

omit [Finite F] in
@[expose] def k2Hom : Matrix (Fin 3) (Fin 3) F →+ (Fin 2 → F) where
  toFun := k2
  map_zero' := by funext i; fin_cases i <;> simp [k2]
  map_add' M N := by
    funext i
    fin_cases i <;> simp [k2, add_sq, CharTwo.two_eq_zero]

omit [Finite F] [CharP F 2] in
theorem kpHom_apply (M : Matrix (Fin 3) (Fin 3) F) : kpHom M = kp M := rfl

omit [Finite F] [CharP F 2] in
theorem kmHom_apply (M : Matrix (Fin 3) (Fin 3) F) : kmHom M = km M := rfl

omit [Finite F] in
theorem k2Hom_apply (M : Matrix (Fin 3) (Fin 3) F) : k2Hom M = k2 M := rfl

omit [Finite F] [CharP F 2] in
theorem delta_eq (hF : Nat.card F = 4) {A : Matrix (Fin 3) (Fin 3) F} (h10 : A 1 0 = 0)
    (h20 : A 2 0 = 0) (hdet : A.det = 1) : A 1 1 * A 2 2 - A 1 2 * A 2 1 = A 0 0 ^ 2 := by
  rw [det_of_par h10 h20] at hdet
  have h0 : A 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have h3 := pow_three_eq_one hF h0
  linear_combination A 0 0 ^ 2 * hdet - (A 1 1 * A 2 2 - A 1 2 * A 2 1) * h3

omit [Finite F] [CharP F 2] in
theorem twAdj_add (k : ℕ) (g : GL (Fin 3) F) (M N : Matrix (Fin 3) (Fin 3) F) :
    twAdj k g (M + N) = twAdj k g M + twAdj k g N := by
  simp only [twAdj, Matrix.mul_add, Matrix.add_mul, smul_add]

omit [Finite F] [CharP F 2] in
theorem twAdj_smul (k : ℕ) (g : GL (Fin 3) F) (t : F) (M : Matrix (Fin 3) (Fin 3) F) :
    twAdj k g (t • M) = t • twAdj k g M := by
  simp only [twAdj, Matrix.mul_smul, Matrix.smul_mul, smul_comm t]

omit [Finite F] [CharP F 2] in
theorem twAdj_sub (k : ℕ) (g : GL (Fin 3) F) (M N : Matrix (Fin 3) (Fin 3) F) :
    twAdj k g (M - N) = twAdj k g M - twAdj k g N := by
  simp only [twAdj, Matrix.mul_sub, Matrix.sub_mul, smul_sub]

end CFSG.Quasithin.H13.Ch4.B414.M
