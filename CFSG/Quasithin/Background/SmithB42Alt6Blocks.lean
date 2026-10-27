module

public import CFSG.Quasithin.EmptyFaithful.S143A6Nat
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3ECheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3EGroup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

namespace B42Alt6

open Equiv Equiv.Perm CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.S143

@[expose] def qFun (q : Fin 4 → Fin 6 → ZMod 2) (s : Vec 4) : Fin 6 → ZMod 2 :=
  fun j => ∑ k, s k * q k j

theorem qFun_add (q : Fin 4 → Fin 6 → ZMod 2) (s t : Vec 4) :
    qFun q (s + t) = qFun q s + qFun q t := by
  funext j
  simp only [qFun, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem qFun_zero (q : Fin 4 → Fin 6 → ZMod 2) : qFun q 0 = 0 := by
  funext j
  simp [qFun]

@[expose] def qTab : ℕ → Fin 4 → Fin 6 → ZMod 2
  | 0 => ![![0, 0, 1, 1, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 0], ![1, 1, 1, 0, 1, 0]]
  | 2 => ![![1, 1, 0, 1, 1, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 1, 1, 1, 0]]
  | 5 => ![![0, 1, 1, 0, 0, 0], ![1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0], ![0, 1, 0, 0, 1, 0]]
  | 6 => ![![0, 0, 0, 1, 1, 0], ![1, 1, 1, 0, 1, 0], ![1, 1, 0, 1, 1, 0], ![0, 1, 0, 0, 1, 0]]
  | 8 => ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 1, 1, 1, 0]]
  | 10 => ![![1, 1, 1, 0, 1, 0], ![0, 0, 0, 1, 1, 0], ![0, 1, 1, 0, 0, 0], ![1, 0, 1, 0, 0, 0]]
  | _ => 0

@[expose] def tw1 : Perm (Fin 6) := c[0, 1, 2] * c[3, 4, 5]

@[expose] def tw2 : Perm (Fin 6) := c[1, 3, 2, 4, 5]

@[expose] def gImg (i : ℕ) (b : Bool) : Perm (Fin 6) :=
  if i = 2 ∨ i = 6 ∨ i = 10 then (if b then tw2 else tw1) else (gen b : Perm (Fin 6))

@[expose] def BlockOK (i : ℕ) : Prop :=
  (∀ s : Vec 4, ∑ j, qFun (qTab i) s j = 0 ∧ qFun (qTab i) s 5 = 0) ∧
  (∀ s t : Vec 4, qFun (qTab i) s = qFun (qTab i) t → s = t) ∧
  ∀ b : Bool, ∀ s : Vec 4,
    qFun (qTab i) (∑ j : Fin 4, s j • toVec 4 ((blkOf i b).getD j.val 0)) =
      n6Norm (gImg i b) (qFun (qTab i) s)

theorem blockOK_0 : BlockOK 0 := by unfold BlockOK; decide
theorem blockOK_2 : BlockOK 2 := by unfold BlockOK; decide
theorem blockOK_5 : BlockOK 5 := by unfold BlockOK; decide
theorem blockOK_6 : BlockOK 6 := by unfold BlockOK; decide
theorem blockOK_8 : BlockOK 8 := by unfold BlockOK; decide
theorem blockOK_10 : BlockOK 10 := by unfold BlockOK; decide

@[expose] noncomputable def qEquiv {i : ℕ} (h : BlockOK i) : Multiplicative (Vec 4) ≃* N6 :=
  MulEquiv.ofBijective
    ({ toFun := fun s => ⟨Multiplicative.ofAdd (qFun (qTab i) (Multiplicative.toAdd s)),
          mem_n6Sub_iff.2 (h.1 _)⟩
       map_one' := by
         apply Subtype.ext
         show Multiplicative.ofAdd (qFun (qTab i) 0) = 1
         rw [qFun_zero]
         rfl
       map_mul' := fun s t => by
         apply Subtype.ext
         show Multiplicative.ofAdd (qFun (qTab i) (Multiplicative.toAdd s + Multiplicative.toAdd t))
           = Multiplicative.ofAdd (qFun (qTab i) (Multiplicative.toAdd s)) *
             Multiplicative.ofAdd (qFun (qTab i) (Multiplicative.toAdd t))
         rw [qFun_add]
         rfl } : Multiplicative (Vec 4) →* N6)
    (by
      have hinj : Function.Injective fun s : Multiplicative (Vec 4) =>
          (⟨Multiplicative.ofAdd (qFun (qTab i) (Multiplicative.toAdd s)),
            mem_n6Sub_iff.2 (h.1 _)⟩ : N6) := by
        intro s t hst
        have h1 := congrArg (fun a : N6 => Multiplicative.toAdd a.1) hst
        exact Multiplicative.toAdd.injective (h.2.1 _ _ h1)
      refine ⟨hinj, ?_⟩
      have hc : Nat.card (Multiplicative (Vec 4)) = Nat.card N6 := by
        rw [n6_card, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
          Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num
      exact (Function.Injective.bijective_of_nat_card_le hinj hc.ge).2)

theorem coe_qEquiv {i : ℕ} (h : BlockOK i) (s : Vec 4) :
    Multiplicative.toAdd (qEquiv h (Multiplicative.ofAdd s)).1 = qFun (qTab i) s := rfl

theorem qEquiv_lin {i : ℕ} (h : BlockOK i) (b : Bool) (s : Vec 4) :
    qEquiv h (Multiplicative.ofAdd (lin 4 (blkOf i b) s)) =
      n6Act (gImg i b) (qEquiv h (Multiplicative.ofAdd s)) := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext j
  rw [coe_qEquiv, n6Act_val, coe_qEquiv, lin_apply, h.2.2 b s]
  rfl

theorem alt_le_closure_gen :
    alternatingGroup (Fin 6) ≤
      Subgroup.closure ({(gx : Perm (Fin 6)), (gy : Perm (Fin 6))} : Set (Perm (Fin 6))) := by
  intro σ hσ
  have h1 : (⟨σ, hσ⟩ : S6) ∈ Subgroup.closure ({gx, gy} : Set S6) := by
    rw [closure_xy]; trivial
  have h2 := Subgroup.mem_map_of_mem (alternatingGroup (Fin 6)).subtype h1
  rw [MonoidHom.map_closure, Set.image_pair] at h2
  exact h2

theorem gx_eq_word : (gx : Perm (Fin 6)) =
    tw2 * tw2 * tw1 * tw2 * tw2 * tw2 * tw1 * tw1 * tw2 * tw1 * tw2 * tw1 := by decide +kernel

theorem gy_eq_word : (gy : Perm (Fin 6)) = tw2 * tw1 * tw2 * tw2 * tw1 := by decide +kernel

theorem alt_le_closure_tw :
    alternatingGroup (Fin 6) ≤ Subgroup.closure ({tw1, tw2} : Set (Perm (Fin 6))) := by
  refine alt_le_closure_gen.trans ?_
  rw [Subgroup.closure_le]
  have h1 : tw1 ∈ Subgroup.closure ({tw1, tw2} : Set (Perm (Fin 6))) :=
    Subgroup.subset_closure (by simp)
  have h2 : tw2 ∈ Subgroup.closure ({tw1, tw2} : Set (Perm (Fin 6))) :=
    Subgroup.subset_closure (by simp)
  rintro x (rfl | rfl)
  · rw [SetLike.mem_coe, gx_eq_word]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 h2) h1) h2) h2) h2) h1)
      h1) h2) h1) h2) h1
  · rw [SetLike.mem_coe, gy_eq_word]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 h1)
      h2) h2) h1

theorem alt_le_closure_gImg (i : ℕ) :
    alternatingGroup (Fin 6) ≤
      Subgroup.closure ({gImg i false, gImg i true} : Set (Perm (Fin 6))) := by
  by_cases h : i = 2 ∨ i = 6 ∨ i = 10
  · have e1 : gImg i false = tw1 := by simp [gImg, h]
    have e2 : gImg i true = tw2 := by simp [gImg, h]
    rw [e1, e2]
    exact alt_le_closure_tw
  · have e1 : gImg i false = gx := by simp [gImg, h, gen]
    have e2 : gImg i true = gy := by simp [gImg, h, gen]
    rw [e1, e2]
    exact alt_le_closure_gen

end B42Alt6

end CFSG.Quasithin
