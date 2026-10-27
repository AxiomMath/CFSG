
module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.Sporadic.Schreier.J4SAutBase

public import CFSG.Sporadic.Schreier.J4SProfileNodeBase1
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SProfile
public meta import CFSG.Sporadic.Schreier.J4SProfile
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.SmallF2
open CFSG.OrderReductions.FrattiniAutomorphisms

section Generic

variable {P : Type*} [Group P] {f : P →* Multiplicative (Fin 5 → ZMod 2)}

@[expose] def fiberCount (f : P →* Multiplicative (Fin 5 → ZMod 2))
    (a : Multiplicative (Fin 5 → ZMod 2)) (d : ℕ) : ℕ :=
  Nat.card {s : P // f s = a ∧ orderOf s = d}

theorem mem_frattini_aut (σ : MulAut P) (s : P) : σ s ∈ frattini P ↔ s ∈ frattini P := by
  have hc := Subgroup.characteristic_iff_comap_eq.1 (frattini_characteristic (G := P)) σ
  conv_rhs => rw [← hc]
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]

theorem ker_comp_aut (hker : f.ker = frattini P) (σ : MulAut P) :
    (f.comp (MulEquiv.toMonoidHom σ)).ker = f.ker := by
  ext s
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker,
    hker, mem_frattini_aut]

@[expose] def thetaOf (hf : Function.Surjective f) (hker : f.ker = frattini P) (σ : MulAut P) :
    Multiplicative (Fin 5 → ZMod 2) →* Multiplicative (Fin 5 → ZMod 2) :=
  (QuotientGroup.lift f.ker (f.comp (MulEquiv.toMonoidHom σ)) (ker_comp_aut hker σ).ge).comp
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom

variable (hf : Function.Surjective f) (hker : f.ker = frattini P)
include hf hker

theorem thetaOf_apply (σ : MulAut P) (s : P) : thetaOf hf hker σ (f s) = f (σ s) := by
  have e : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f s) = (s : P ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [thetaOf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, QuotientGroup.lift_mk,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

theorem thetaOf_injective (σ : MulAut P) : Function.Injective (thetaOf hf hker σ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  obtain ⟨s, rfl⟩ := hf a
  rw [MonoidHom.mem_ker, thetaOf_apply hf hker, ← MonoidHom.mem_ker, hker, mem_frattini_aut,
    ← hker, MonoidHom.mem_ker] at ha
  rw [Subgroup.mem_bot]
  exact ha

theorem fiber_iff (σ : MulAut P) (s : P) (a : Multiplicative (Fin 5 → ZMod 2)) :
    f (σ s) = thetaOf hf hker σ a ↔ f s = a := by
  rw [← thetaOf_apply hf hker]
  exact (thetaOf_injective hf hker σ).eq_iff

theorem fiberCount_theta (σ : MulAut P) (a : Multiplicative (Fin 5 → ZMod 2)) (d : ℕ) :
    fiberCount f (thetaOf hf hker σ a) d = fiberCount f a d := by
  rw [fiberCount, fiberCount]
  refine Nat.card_congr
    { toFun := fun s => ⟨σ.symm s, ?_, ?_⟩
      invFun := fun s => ⟨σ s, (fiber_iff hf hker σ s a).2 s.2.1, by
        rw [MulEquiv.orderOf_eq]; exact s.2.2⟩
      left_inv := fun s => Subtype.ext (MulEquiv.apply_symm_apply σ s)
      right_inv := fun s => Subtype.ext (MulEquiv.symm_apply_apply σ s) }
  · rw [← fiber_iff hf hker σ, MulEquiv.apply_symm_apply]
    exact s.2.1
  · rw [MulEquiv.orderOf_eq]
    exact s.2.2

theorem thetaOf_eq_self
    (huniq : ∀ a ∈ ({5, 6, 7, 8, 17} : Set ℕ), ∀ w : Fin 5 → ZMod 2,
      (∀ j : Fin 5, fiberCount f (Multiplicative.ofAdd w) (2 ^ j.val) =
        fiberCount f (Multiplicative.ofAdd (toVecD 5 a)) (2 ^ j.val)) → w = toVecD 5 a)
    (σ : MulAut P) (a : Multiplicative (Fin 5 → ZMod 2)) : thetaOf hf hker σ a = a := by
  have hbasis : ∀ b ∈ ({5, 6, 7, 8, 17} : Set ℕ),
      thetaOf hf hker σ (Multiplicative.ofAdd (toVecD 5 b)) =
        Multiplicative.ofAdd (toVecD 5 b) := by
    intro b hb
    have h := huniq b hb
      (Multiplicative.toAdd (thetaOf hf hker σ (Multiplicative.ofAdd (toVecD 5 b)))) fun j => by
        rw [ofAdd_toAdd, fiberCount_theta]
    exact (ofAdd_toAdd _).symm.trans (congrArg Multiplicative.ofAdd h)
  have hθ' : ∀ v, AddMonoidHom.toMultiplicative.symm (thetaOf hf hker σ) v =
      Multiplicative.toAdd (thetaOf hf hker σ (Multiplicative.ofAdd v)) := fun v => rfl
  have hfix : ∀ i : Fin 5, AddMonoidHom.toMultiplicative.symm (thetaOf hf hker σ)
      (toVecD 5 (![5, 6, 7, 8, 17] i)) = toVecD 5 (![5, 6, 7, 8, 17] i) := by
    intro i
    rw [hθ', hbasis _ (by fin_cases i <;> simp), toAdd_ofAdd]
  have hsmul : ∀ (c : ZMod 2) (v : Fin 5 → ZMod 2),
      AddMonoidHom.toMultiplicative.symm (thetaOf hf hker σ) (c • v) =
        c • AddMonoidHom.toMultiplicative.symm (thetaOf hf hker σ) v := by
    intro c v
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul, zero_smul, map_zero]
    · rw [one_smul, one_smul]
  obtain ⟨c, hc⟩ := basis_five_span (Multiplicative.toAdd a)
  have h : AddMonoidHom.toMultiplicative.symm (thetaOf hf hker σ) (Multiplicative.toAdd a) =
      Multiplicative.toAdd a := by
    rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul, hfix]
  rw [hθ', ofAdd_toAdd] at h
  exact Multiplicative.toAdd.injective h

theorem aut_trivial_of_profiles
    (huniq : ∀ a ∈ ({5, 6, 7, 8, 17} : Set ℕ), ∀ w : Fin 5 → ZMod 2,
      (∀ j : Fin 5, fiberCount f (Multiplicative.ofAdd w) (2 ^ j.val) =
        fiberCount f (Multiplicative.ofAdd (toVecD 5 a)) (2 ^ j.val)) → w = toVecD 5 a)
    (σ : MulAut P) (s : P) :
    QuotientGroup.mk' (frattini P) (σ s) = QuotientGroup.mk' (frattini P) s := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← hker,
    MonoidHom.mem_ker, map_mul, map_inv, ← thetaOf_apply hf hker,
    thetaOf_eq_self hf hker huniq]
  exact inv_mul_cancel _

theorem isPGroup_aut_of_profiles [Finite P] (hP : IsPGroup 2 P)
    (huniq : ∀ a ∈ ({5, 6, 7, 8, 17} : Set ℕ), ∀ w : Fin 5 → ZMod 2,
      (∀ j : Fin 5, fiberCount f (Multiplicative.ofAdd w) (2 ^ j.val) =
        fiberCount f (Multiplicative.ofAdd (toVecD 5 a)) (2 ^ j.val)) → w = toVecD 5 a) :
    IsPGroup 2 (MulAut P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk := (CFSG.GroupTheory.frattini_automorphism_kernel hP).2
  intro σ
  have hσ : σ ∈ (quotientAutomorphism (frattini P)).ker :=
    (mem_quotientAutomorphism_kernel _ σ).2 (aut_trivial_of_profiles hf hker huniq σ)
  obtain ⟨k, hk'⟩ := hk ⟨σ, hσ⟩
  refine ⟨k, ?_⟩
  have := congrArg Subtype.val hk'
  rwa [Subgroup.coe_pow, Subgroup.coe_one] at this

omit hf hker

theorem aut_trivial_of_equiv {Q : Type*} [Group Q] (e : P ≃* Q)
    (h : ∀ (σ : MulAut P) (s : P),
      QuotientGroup.mk' (frattini P) (σ s) = QuotientGroup.mk' (frattini P) s)
    (σ : MulAut Q) (s : Q) :
    QuotientGroup.mk' (frattini Q) (σ s) = QuotientGroup.mk' (frattini Q) s := by
  have h1 := h ((e.trans σ).trans e.symm) (e.symm s)
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1 ⊢
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, ← map_inv,
    ← map_mul] at h1
  have h2 := frattini_le_comap_frattini_of_surjective (φ := MulEquiv.toMonoidHom e)
    e.surjective h1
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h2

theorem isPGroup_aut_of_equiv {Q : Type*} [Group Q] (e : P ≃* Q) (h : IsPGroup 2 (MulAut P)) :
    IsPGroup 2 (MulAut Q) :=
  h.of_equiv (MulAut.congr e)

end Generic

end CFSG.Sporadic.J4Schreier
