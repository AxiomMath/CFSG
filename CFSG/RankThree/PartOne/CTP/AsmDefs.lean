module

public import CFSG.RankThree.PartOne.CTP.LStd
public import CFSG.RankThree.PartOne.CTP.AsmConj

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.RankThree.PartOne CFSG.RankThree
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

theorem conjBy_conjBy (a b : G) (X : Subgroup G) :
    conjBy a (conjBy b X) = conjBy (a * b) X := by
  unfold conjBy
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem conjBy_inf (w : G) (X Y : Subgroup G) :
    conjBy w (X ⊓ Y) = conjBy w X ⊓ conjBy w Y := by
  unfold conjBy
  exact Subgroup.map_inf _ _ _ (MulAut.conj w).injective

theorem conjBy_sup (w : G) (X Y : Subgroup G) :
    conjBy w (X ⊔ Y) = conjBy w X ⊔ conjBy w Y := by
  unfold conjBy
  exact Subgroup.map_sup _ _ _

theorem conjBy_zpowers (w a : G) :
    conjBy w (Subgroup.zpowers a) = Subgroup.zpowers (w * a * w⁻¹) := by
  unfold conjBy
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

theorem conjBy_centralizer (w : G) (X : Subgroup G) :
    conjBy w (Subgroup.centralizer (X : Set G)) = Subgroup.centralizer (conjBy w X : Set G) :=
  (Equivariance.centralizer_conjBy w X).symm

theorem card_conjBy (w : G) (X : Subgroup G) : Nat.card ↥(conjBy w X) = Nat.card ↥X :=
  (Nat.card_congr (X.equivMapOfInjective (MulAut.conj w).toMonoidHom
    (MulAut.conj w).injective).toEquiv).symm

theorem centralizer_sup (X Y : Subgroup G) :
    Subgroup.centralizer ((X ⊔ Y : Subgroup G) : Set G) =
      Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (Y : Set G) := by
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun y hy => h y (Subgroup.mem_sup_left hy), fun y hy => h y (Subgroup.mem_sup_right hy)⟩
  · rintro ⟨h1, h2⟩ y hy
    have hle : X ⊔ Y ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact h1 x hx
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact h2 x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

section Family

variable {L B K : Subgroup G} {f₀ : ℕ} {b : G} (F : LFam L B f₀ b K) (I : Subgroup G)

@[expose] def Isg (σ : Equiv.Perm (Fin 5)) : Subgroup G := conjBy (F.W σ) I

@[expose] def Ksg (σ : Equiv.Perm (Fin 5)) : Subgroup G := conjBy (F.W σ) K

@[expose] def BKsg (σ : Equiv.Perm (Fin 5)) : Subgroup G := conjBy (F.W σ) (B ⊓ K)

@[expose] def Jsg (σ : Equiv.Perm (Fin 5)) (x y : Fin 3) : Subgroup G :=
  conjBy (F.W σ) (F.J (e3 x) (e3 y))

@[expose] def bsg (σ : Equiv.Perm (Fin 5)) : G := F.W σ * b * (F.W σ)⁻¹

@[expose] def Msg (σ : Equiv.Perm (Fin 5)) (x y : Fin 3) : Subgroup G :=
  pairLayer (Isg F I σ) (BKsg F σ) (Jsg F σ x y)

theorem Jsg_eq (σ : Equiv.Perm (Fin 5)) (x y : Fin 3) :
    Jsg F σ x y = F.J (σ (e3 x)) (σ (e3 y)) := (F.J_equiv σ _ _).symm

theorem conjBy_J (ρ : Equiv.Perm (Fin 5)) (a b : Fin 5) :
    conjBy (F.W ρ) (F.J a b) = F.J (ρ a) (ρ b) := (F.J_equiv ρ a b).symm

theorem conj_Isg (τ σ : Equiv.Perm (Fin 5)) : conjBy (F.W τ) (Isg F I σ) = Isg F I (τ * σ) := by
  unfold Isg
  rw [conjBy_conjBy, ← map_mul]

theorem conj_BKsg (τ σ : Equiv.Perm (Fin 5)) :
    conjBy (F.W τ) (BKsg F σ) = BKsg F (τ * σ) := by
  unfold BKsg
  rw [conjBy_conjBy, ← map_mul]

theorem conj_Jsg (τ σ : Equiv.Perm (Fin 5)) (x y : Fin 3) :
    conjBy (F.W τ) (Jsg F σ x y) = Jsg F (τ * σ) x y := by
  unfold Jsg
  rw [conjBy_conjBy, ← map_mul]

theorem conjBy_B_inf_J (ρ : Equiv.Perm (Fin 5)) (a b : Fin 5) :
    conjBy (F.W ρ) (B ⊓ F.J a b) = B ⊓ F.J (ρ a) (ρ b) := by
  rw [conjBy_inf, Equivariance.conjBy_eq_of_mem_normalizer (F.W_B ρ), conjBy_J]

theorem conjBy_B_inf_centralizer_J (ρ : Equiv.Perm (Fin 5)) (a b : Fin 5) :
    conjBy (F.W ρ) (B ⊓ Subgroup.centralizer (F.J a b : Set G)) =
      B ⊓ Subgroup.centralizer (F.J (ρ a) (ρ b) : Set G) := by
  rw [conjBy_inf, Equivariance.conjBy_eq_of_mem_normalizer (F.W_B ρ), conjBy_centralizer,
    conjBy_J]

theorem B_inf_J_34 : B ⊓ F.J 3 4 = Subgroup.zpowers b := by
  have := F.B_elem
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hb5 : b ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := B) b (F.b_mem.1)
  have hord : orderOf b = 5 := orderOf_eq_prime hb5 F.b_ne
  have hfin : Finite ↥(B ⊓ F.J 3 4) :=
    Nat.finite_of_card_ne_zero (by rw [F.line_card 3 4 (by decide)]; norm_num)
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr F.b_mem) ?_).symm
  rw [Nat.card_zpowers, hord, F.line_card 3 4 (by decide)]

theorem B_inf_J_sg (σ : Equiv.Perm (Fin 5)) :
    B ⊓ F.J (σ 3) (σ 4) = Subgroup.zpowers (bsg F σ) := by
  rw [← conjBy_B_inf_J, B_inf_J_34, conjBy_zpowers]
  rfl

theorem bsg_mem (σ : Equiv.Perm (Fin 5)) : bsg F σ ∈ B ⊓ F.J (σ 3) (σ 4) := by
  rw [B_inf_J_sg]
  exact Subgroup.mem_zpowers _

end Family

section FamilyFinite

variable [Finite G] {L B K : Subgroup G} {f₀ : ℕ} {b : G} (F : LFam L B f₀ b K) (I : Subgroup G)

theorem conj_Msg (τ σ : Equiv.Perm (Fin 5)) (x y : Fin 3) :
    conjBy (F.W τ) (Msg F I σ x y) = Msg F I (τ * σ) x y := by
  unfold Msg
  rw [pairLayer_conjBy, conj_Isg, conj_BKsg, conj_Jsg]

theorem Isg_mem_theta (hI : I ∈ thetaComponentsAt 5 b) (σ : Equiv.Perm (Fin 5)) :
    Isg F I σ ∈ thetaComponentsAt 5 (bsg F σ) :=
  conjBy_mem_thetaComponentsAt (by norm_num) (F.W σ) b hI

end FamilyFinite

end CFSG.RankThree.PartOne.CTP
