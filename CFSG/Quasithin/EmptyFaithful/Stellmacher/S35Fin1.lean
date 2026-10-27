module

public import CFSG.Quasithin.EmptyFaithful.SzF53MUni

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

@[expose] def IsFixPt (D : Subgroup (Perm (Fin 5))) (p : Fin 5) : Prop := ∀ d ∈ D, d p = p

@[expose] def IsCentInv (D : Subgroup (Perm (Fin 5))) (z : Perm (Fin 5)) : Prop :=
  z ∈ D ∧ z ≠ 1 ∧ ∀ d ∈ D, d * z = z * d

@[expose] def Tsub (D : Subgroup (Perm (Fin 5))) : Subgroup (Perm (Fin 5)) :=
  D ⊓ alternatingGroup (Fin 5)

@[expose] def That (D : Subgroup (Perm (Fin 5))) : Subgroup (Perm (Fin 5)) :=
  Subgroup.closure {g | g ∈ D ∧ g.IsSwap}

@[expose] def Cfour (D : Subgroup (Perm (Fin 5))) : Subgroup (Perm (Fin 5)) :=
  Subgroup.closure {g | g ∈ D ∧ g ^ 2 ≠ 1}

@[expose] def ptStab (p : Fin 5) : Subgroup (Perm (Fin 5)) :=
  MulAction.stabilizer (Perm (Fin 5)) p

theorem mem_ptStab {p : Fin 5} {σ : Perm (Fin 5)} : σ ∈ ptStab p ↔ σ p = p :=
  MulAction.mem_stabilizer_iff

theorem vp_mem (p : Fin 5) :
    (Multiplicative.ofAdd (fun i : Fin 5 => if i = p then (0 : ZMod 2) else 1) : G6.PermMod 5) ∈
      G6.coreMod 5 := by
  rw [G6.mem_coreMod]; revert p; decide +kernel

theorem ep_mem (a b : Fin 5) :
    (Multiplicative.ofAdd (fun i : Fin 5 => (if i = a then (1 : ZMod 2) else 0) +
      (if i = b then 1 else 0)) : G6.PermMod 5) ∈ G6.coreMod 5 := by
  rw [G6.mem_coreMod]; revert a b; decide +kernel

@[expose] def vp (p : Fin 5) : orth.W :=
  ⟨Multiplicative.ofAdd (fun i : Fin 5 => if i = p then (0 : ZMod 2) else 1), vp_mem p⟩

@[expose] def ep (a b : Fin 5) : orth.W :=
  ⟨Multiplicative.ofAdd (fun i : Fin 5 => (if i = a then (1 : ZMod 2) else 0) +
    (if i = b then 1 else 0)), ep_mem a b⟩

@[expose] def cenW (U : Subgroup orth.W) : Subgroup (Perm (Fin 5)) where
  carrier := {g | ∀ w ∈ U, orth.act g w = w}
  one_mem' := fun w _ => by rw [map_one]; rfl
  mul_mem' := fun {a b} ha hb w hw => by
    rw [act_mul_apply, hb w hw, ha w hw]
  inv_mem' := fun {a} ha w hw => by
    have h := ha w hw
    calc orth.act a⁻¹ w = orth.act a⁻¹ (orth.act a w) := by rw [h]
      _ = w := act_inv_act orth a w

theorem mem_cenW {U : Subgroup orth.W} {g : Perm (Fin 5)} :
    g ∈ cenW U ↔ ∀ w ∈ U, orth.act g w = w := Iff.rfl

@[expose] def IsQuad (A : Subgroup (Perm (Fin 5))) : Prop :=
  ∀ a ∈ A, ∀ w ∈ commW orth A ⊤, orth.act a w = w

abbrev cj (g : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) : Subgroup (Perm (Fin 5)) :=
  B.map (MulAut.conj g).toMonoidHom

abbrev mp (g : Perm (Fin 5)) (U : Subgroup orth.W) : Subgroup orth.W :=
  U.map (orth.act g).toMonoidHom

theorem mem_cj {g σ : Perm (Fin 5)} {B : Subgroup (Perm (Fin 5))} :
    σ ∈ cj g B ↔ g⁻¹ * σ * g ∈ B := mem_map_conj B g σ

theorem mem_mp {g : Perm (Fin 5)} {U : Subgroup orth.W} {w : orth.W} :
    w ∈ mp g U ↔ orth.act g⁻¹ w ∈ U := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    show orth.act g⁻¹ (orth.act g u) ∈ U
    rw [act_inv_act]; exact hu
  · intro h
    exact ⟨_, h, act_act_inv orth g w⟩

theorem commW_cj_top (g : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) :
    commW orth (cj g B) ⊤ = mp g (commW orth B ⊤) := by
  have h := map_commW_conj orth g B ⊤
  rw [map_act_top] at h
  exact h.symm

theorem commW_cj (g : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) (U : Subgroup orth.W) :
    commW orth (cj g B) (mp g U) = mp g (commW orth B U) :=
  (map_commW_conj orth g B U).symm

theorem fixW_cj (g : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) :
    fixW orth (cj g B) = mp g (fixW orth B) := by
  ext w
  rw [mem_fixW_map_conj, mem_mp]

theorem card_mp (g : Perm (Fin 5)) (U : Subgroup orth.W) : Nat.card (mp g U) = Nat.card U :=
  card_map_act orth g U

theorem cenW_mp (g : Perm (Fin 5)) (U : Subgroup orth.W) : cenW (mp g U) = cj g (cenW U) := by
  ext σ
  rw [mem_cj, mem_cenW, mem_cenW]
  constructor
  · intro h w hw
    have h1 := h (orth.act g w) ⟨w, hw, rfl⟩
    calc orth.act (g⁻¹ * σ * g) w = orth.act g⁻¹ (orth.act σ (orth.act g w)) := by
          rw [act_mul_apply, act_mul_apply]
      _ = w := by rw [h1, act_inv_act]
  · intro h w hw
    rw [mem_mp] at hw
    have h1 := h _ hw
    have h2 : orth.act σ w = orth.act g (orth.act (g⁻¹ * σ * g) (orth.act g⁻¹ w)) := by
      rw [← act_mul_apply, ← act_mul_apply]; congr 1; group
    rw [h2, h1, act_act_inv]

theorem cj_inf (g : Perm (Fin 5)) (A B : Subgroup (Perm (Fin 5))) :
    cj g (A ⊓ B) = cj g A ⊓ cj g B :=
  Subgroup.map_inf A B _ (MulEquiv.injective _)

theorem cj_zpowers (g x : Perm (Fin 5)) :
    cj g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) := by
  exact MonoidHom.map_zpowers _ x

theorem mem_cj_conj {g σ : Perm (Fin 5)} {B : Subgroup (Perm (Fin 5))} :
    g * σ * g⁻¹ ∈ cj g B ↔ σ ∈ B := by
  rw [mem_cj]; simp [mul_assoc]

theorem card_cj (g : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) : Nat.card (cj g B) = Nat.card B :=
  Subgroup.card_map_of_injective (MulEquiv.injective _)

theorem exists_cj {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    ∃ g : Perm (Fin 5), D = cj g S5Syl := exists_conj_S5Syl hD

theorem card_cj_S5Syl (g : Perm (Fin 5)) : Nat.card (cj g S5Syl) = 8 := by
  rw [card_cj]; exact card_S5Syl

end CFSG.Quasithin.F53.Stellmacher.S35.Fin
