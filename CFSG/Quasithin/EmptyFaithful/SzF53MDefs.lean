module

public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

structure Model (n : ℕ) where
  W : Type
  [grp : CommGroup W]
  [fin : Finite W]
  act : Equiv.Perm (Fin n) →* MulAut W
  sq : ∀ w : W, w * w = 1

attribute [instance] Model.grp Model.fin

theorem coreMod_sq (n : ℕ) : ∀ w : ↥(G6.coreMod n), w * w = 1 := by
  intro w
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  show Multiplicative.toAdd (w : G6.PermMod n) i + Multiplicative.toAdd (w : G6.PermMod n) i = 0
  exact h2 _

@[expose] def deltaModel (n : ℕ) : Model n where
  W := ↥(G6.coreMod n)
  grp := Subgroup.toCommGroup (G6.coreMod n)
  act := G6.coreAct n
  sq := coreMod_sq n

abbrev orth : Model 5 := deltaModel 5

abbrev nat3 : Model 3 := deltaModel 3

@[expose] def edgeEnd : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

@[expose] def edgeIdx : Fin 5 → Fin 5 → Fin 10 :=
  ![![0, 0, 1, 2, 3], ![0, 0, 4, 5, 6], ![1, 4, 0, 7, 8], ![2, 5, 7, 0, 9], ![3, 6, 8, 9, 0]]

@[expose] def edgePerm (σ : Perm (Fin 5)) (k : Fin 10) : Fin 10 :=
  edgeIdx (σ (edgeEnd k).1) (σ (edgeEnd k).2)

@[expose] def embed (c : Fin 4 → ZMod 2) (k : Fin 10) : ZMod 2 :=
  c 0 * (if k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 5 then 1 else 0) +
  c 1 * (if k = 1 ∨ k = 3 ∨ k = 4 ∨ k = 6 then 1 else 0) +
  c 2 * (if k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 7 then 1 else 0) +
  c 3 * (if k = 0 ∨ k = 3 ∨ k = 4 ∨ k = 8 then 1 else 0)

@[expose] def edgeAct (σ : Perm (Fin 5)) (z : Fin 10 → ZMod 2) : Fin 10 → ZMod 2 :=
  fun k => z (edgePerm σ⁻¹ k)

@[expose] def natAct (σ : Perm (Fin 5)) (c : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  fun i =>
    let y : Fin 10 → ZMod 2 := fun k => embed c (edgePerm σ⁻¹ k)
    y (![5, 6, 7, 8] i) + y 9

private theorem chart_compat : ∀ (σ : Perm (Fin 5)) (c : Fin 4 → ZMod 2),
    edgeAct σ (embed c) = (fun k => embed (natAct σ c) k) ∨
    edgeAct σ (embed c) = (fun k => embed (natAct σ c) k + 1) := by
  decide +kernel

private theorem edgeEnd_ne : ∀ k : Fin 10, (edgeEnd k).1 ≠ (edgeEnd k).2 := by decide +kernel

private theorem edgeIdx_comm : ∀ a b : Fin 5, edgeIdx a b = edgeIdx b a ∨ a = b := by
  decide +kernel

private theorem edgeEnd_edgeIdx : ∀ a b : Fin 5, a ≠ b →
    edgeEnd (edgeIdx a b) = (a, b) ∨ edgeEnd (edgeIdx a b) = (b, a) := by decide +kernel

theorem edgePerm_mul (ρ π : Perm (Fin 5)) (k : Fin 10) :
    edgePerm (ρ * π) k = edgePerm ρ (edgePerm π k) := by
  have hne := edgeEnd_ne k
  have hπ : π (edgeEnd k).1 ≠ π (edgeEnd k).2 := fun h => hne (π.injective h)
  unfold edgePerm
  rcases edgeEnd_edgeIdx _ _ hπ with h | h
  · rw [h]; rfl
  · rw [h]
    simp only [Perm.mul_apply]
    rcases edgeIdx_comm (ρ (π (edgeEnd k).1)) (ρ (π (edgeEnd k).2)) with h' | h'
    · exact h'
    · exact absurd (ρ.injective h' ▸ rfl : π (edgeEnd k).1 = π (edgeEnd k).2) hπ

theorem edgeAct_mul (σ τ : Perm (Fin 5)) (z : Fin 10 → ZMod 2) :
    edgeAct (σ * τ) z = edgeAct σ (edgeAct τ z) := by
  funext k
  simp only [edgeAct, mul_inv_rev, edgePerm_mul]

@[expose] def canon (y : Fin 10 → ZMod 2) : Fin 10 → ZMod 2 := fun k => y k + y 9

private theorem two_eq_zero_zmod2 : (2 : ZMod 2) = 0 := by decide

theorem canon_add_smul_J (y : Fin 10 → ZMod 2) (l : ZMod 2) :
    canon (fun k => y k + l) = canon y := by
  funext k
  simp only [canon]
  linear_combination l * two_eq_zero_zmod2

private theorem embed_nine : ∀ c : Fin 4 → ZMod 2, embed c 9 = 0 := by decide +kernel

theorem embed_injective : ∀ c c' : Fin 4 → ZMod 2, embed c = embed c' → c = c' := by
  decide +kernel

theorem embed_add : ∀ c c' : Fin 4 → ZMod 2, embed (c + c') = embed c + embed c' := by
  decide +kernel

theorem embed_natAct (σ : Perm (Fin 5)) (c : Fin 4 → ZMod 2) :
    embed (natAct σ c) = canon (edgeAct σ (embed c)) := by
  rcases chart_compat σ c with h | h
  · have h9 : edgeAct σ (embed c) 9 = 0 := by rw [h]; exact embed_nine _
    funext k
    simp only [canon, h9, add_zero]
    exact (congrFun h k).symm
  · have h9 : edgeAct σ (embed c) 9 = 1 := by
      rw [h]; simp only [embed_nine, zero_add]
    funext k
    simp only [canon, h9]
    have := congrFun h k
    rw [this]
    generalize embed (natAct σ c) k = a
    revert a; decide

theorem natAct_mul (σ τ : Perm (Fin 5)) (c : Fin 4 → ZMod 2) :
    natAct (σ * τ) c = natAct σ (natAct τ c) := by
  apply embed_injective
  have h1 := embed_natAct (σ * τ) c
  have h2 := embed_natAct σ (natAct τ c)
  have h3 := embed_natAct τ c
  rw [h1, h2, h3, edgeAct_mul]
  have : edgeAct σ (canon (edgeAct τ (embed c))) =
      fun k => edgeAct σ (edgeAct τ (embed c)) k + edgeAct τ (embed c) 9 := rfl
  rw [this, canon_add_smul_J]

theorem natAct_one (c : Fin 4 → ZMod 2) : natAct 1 c = c := by
  revert c; decide +kernel

private theorem canon_add (y y' : Fin 10 → ZMod 2) : canon (y + y') = canon y + canon y' := by
  funext k
  simp only [canon, Pi.add_apply]
  ring

theorem natAct_add (σ : Perm (Fin 5)) (c c' : Fin 4 → ZMod 2) :
    natAct σ (c + c') = natAct σ c + natAct σ c' := by
  apply embed_injective
  rw [embed_natAct, embed_add, embed_add, embed_natAct, embed_natAct]
  have : edgeAct σ (embed c + embed c') = edgeAct σ (embed c) + edgeAct σ (embed c') := rfl
  rw [this, canon_add]

@[expose] def nat : Model 5 where
  W := Multiplicative (Fin 4 → ZMod 2)
  act :=
    { toFun := fun σ =>
        { toFun := fun x => Multiplicative.ofAdd (natAct σ (Multiplicative.toAdd x))
          invFun := fun x => Multiplicative.ofAdd (natAct σ⁻¹ (Multiplicative.toAdd x))
          left_inv := fun x => by
            apply Multiplicative.toAdd.injective
            show natAct σ⁻¹ (natAct σ (Multiplicative.toAdd x)) = _
            rw [← natAct_mul, inv_mul_cancel, natAct_one]
          right_inv := fun x => by
            apply Multiplicative.toAdd.injective
            show natAct σ (natAct σ⁻¹ (Multiplicative.toAdd x)) = _
            rw [← natAct_mul, mul_inv_cancel, natAct_one]
          map_mul' := fun x y => by
            apply Multiplicative.toAdd.injective
            exact natAct_add σ _ _ }
      map_one' := MulEquiv.ext fun x => Multiplicative.toAdd.injective (natAct_one _)
      map_mul' := fun σ τ => MulEquiv.ext fun x =>
        Multiplicative.toAdd.injective (natAct_mul σ τ _) }
  sq := by intro w; revert w; decide +kernel

@[expose] def fixW {n : ℕ} (M : Model n) (B : Subgroup (Equiv.Perm (Fin n))) : Subgroup M.W where
  carrier := {w | ∀ b ∈ B, M.act b w = w}
  one_mem' := fun b _ => map_one _
  mul_mem' := fun {x y} hx hy b hb => by rw [map_mul, hx b hb, hy b hb]
  inv_mem' := fun {x} hx b hb => by rw [map_inv, hx b hb]

@[expose] def commW {n : ℕ} (M : Model n) (B : Subgroup (Equiv.Perm (Fin n)))
    (U : Subgroup M.W) : Subgroup M.W :=
  Subgroup.closure {w | ∃ b ∈ B, ∃ u ∈ U, w = M.act b u * u⁻¹}

@[expose] noncomputable def idx {n : ℕ} (M : Model n) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (fixW M (Subgroup.zpowers σ)).index

theorem mem_fixW {n : ℕ} {M : Model n} {B : Subgroup (Equiv.Perm (Fin n))} {w : M.W} :
    w ∈ fixW M B ↔ ∀ b ∈ B, M.act b w = w := Iff.rfl

variable {G : Type} [Group G]

structure IsSec (X L N : Subgroup G) : Prop where
  le : L ≤ N
  normN : X ≤ Subgroup.normalizer (N : Set G)
  normL : X ≤ Subgroup.normalizer (L : Set G)
  comm : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ ∈ L
  sq : ∀ x ∈ N, x ^ 2 ∈ L

@[expose] noncomputable def secIdx (A L N : Subgroup G) : ℕ := (fixSecIn A L N).relIndex N

@[expose] def commSec (A L N : Subgroup G) : Subgroup G := ⁅N, A⁆ ⊔ L

@[expose] noncomputable def IsTransvec (k : ℕ) (a : G) (L N : Subgroup G) : Prop :=
  1 < secIdx (Subgroup.zpowers a) L N ∧ secIdx (Subgroup.zpowers a) L N ≤ 2 ^ k

structure SecData {n : ℕ} (M : Model n) (K L X : Subgroup G) [(L.subgroupOf X).Normal]
    (Ψ : ↥K →* Equiv.Perm (Fin n)) (β : M.W →* ↥X ⧸ L.subgroupOf X) : Prop where
  surj : Function.Surjective β
  inj : Function.Injective β
  equiv : ∀ (k : ↥K) (u : M.W) (x : ↥X), β u = QuotientGroup.mk x →
    ∃ hkx : (k : G) * (x : G) * (k : G)⁻¹ ∈ X,
      β (M.act (Ψ k) u) = QuotientGroup.mk ⟨(k : G) * (x : G) * (k : G)⁻¹, hkx⟩

@[expose] def IsModelSec {n : ℕ} (M : Model n) (F L X : Subgroup G) : Prop :=
  ∃ _ : (L.subgroupOf X).Normal, ∃ (θ : ↥F →* Equiv.Perm (Fin n))
    (β : M.W →* ↥X ⧸ L.subgroupOf X),
    Function.Surjective θ ∧ θ.ker = (cSecIn F L X).subgroupOf F ∧ SecData M F L X θ β

@[expose] def IsOrthSec (F L N : Subgroup G) : Prop := IsModelSec orth F L N

@[expose] def IsNatSec (F L N : Subgroup G) : Prop := IsModelSec nat F L N

@[expose] def IsNat3Sec (F L N : Subgroup G) : Prop := IsModelSec nat3 F L N

theorem naturalSn_iff_isModelSec {n : ℕ} (hn : n = 3 ∨ n = 5) {F L X : Subgroup G}
    [h : (L.subgroupOf X).Normal] :
    NaturalSn n F L X ↔ IsModelSec (deltaModel n) F L X := by
  have hk : G6.natKer n = ⊥ := X1512.natKer_eq_bot hn
  constructor
  · rintro ⟨θ, β, hθs, hθk, hβs, hβk, hequiv⟩
    exact ⟨h, θ, β, hθs, hθk, ⟨hβs, (MonoidHom.ker_eq_bot_iff β).mp (hβk.trans hk), hequiv⟩⟩
  · rintro ⟨_, θ, β, hθs, hθk, hsd⟩
    exact ⟨θ, β, hθs, hθk, hsd.surj, ((MonoidHom.ker_eq_bot_iff β).mpr hsd.inj).trans hk.symm,
      hsd.equiv⟩

theorem naturalSn_five_iff {F L X : Subgroup G} [(L.subgroupOf X).Normal] :
    NaturalSn 5 F L X ↔ IsOrthSec F L X :=
  naturalSn_iff_isModelSec (Or.inr rfl)

end CFSG.Quasithin.F53Mod
