module

public import CFSG.Quasithin.MS93.S6Bridge
public import CFSG.Quasithin.EmptyFaithful.S143A6Nat
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.AppendixH.H15.Vocab

public section

namespace CFSG.ASVolI.H16

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Quasithin.MS93
  CFSG.ASVolI.ChH Matrix
open CFSG.Quasithin.H (StdMod)

@[expose] def n6Even (a : S143.N6) : ↥(evenWeight 6) :=
  ⟨Multiplicative.toAdd (a : Multiplicative (Fin 6 → ZMod 2)),
    S6B.mem_of_sum_eq_zero (S143.mem_n6Sub_iff.1 a.2).1⟩

private def n6Ones : ↥(evenWeight 6) :=
  ⟨fun _ => 1, S6B.mem_of_sum_eq_zero (by decide)⟩

private theorem n6Ones_sum : ∑ i, (n6Ones : Fin 6 → ZMod 2) i = 0 :=
  S6B.sum_eq_zero_of_mem n6Ones.2

private theorem n6Ones_apply (i : Fin 6) : (n6Ones : Fin 6 → ZMod 2) i = 1 := rfl

private theorem n6Even_mul (a b : S143.N6) : n6Even (a * b) = n6Even a + n6Even b := by
  apply Subtype.ext
  change Multiplicative.toAdd (a.1 * b.1) = Multiplicative.toAdd a.1 + Multiplicative.toAdd b.1
  rw [toAdd_mul]

private theorem n6Even_one : n6Even (1 : S143.N6) = 0 := by
  apply Subtype.ext
  show Multiplicative.toAdd (1 : Multiplicative (Fin 6 → ZMod 2)) = 0
  simp

private theorem zmod_two_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  revert h
  revert c
  decide

private theorem n6Even_act_class (σ : Equiv.Perm (Fin 6)) (a : S143.N6) :
    (QuotientAddGroup.mk (n6Even (S143.n6Act σ a)) : AltHeart 6) =
      (QuotientAddGroup.mk (permWeight 6 σ (n6Even a)) : AltHeart 6) := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  intro i j
  show (n6Even (S143.n6Act σ a) : Fin 6 → ZMod 2) i -
      (permWeight 6 σ (n6Even a) : Fin 6 → ZMod 2) i =
    (n6Even (S143.n6Act σ a) : Fin 6 → ZMod 2) j -
      (permWeight 6 σ (n6Even a) : Fin 6 → ZMod 2) j
  rw [show (n6Even (S143.n6Act σ a) : Fin 6 → ZMod 2) i =
        (n6Even a : Fin 6 → ZMod 2) (σ⁻¹ i) + (n6Even a : Fin 6 → ZMod 2) (σ⁻¹ 5) from
      S143.n6Act_val σ a i,
    show (n6Even (S143.n6Act σ a) : Fin 6 → ZMod 2) j =
        (n6Even a : Fin 6 → ZMod 2) (σ⁻¹ j) + (n6Even a : Fin 6 → ZMod 2) (σ⁻¹ 5) from
      S143.n6Act_val σ a j,
    show (permWeight 6 σ (n6Even a) : Fin 6 → ZMod 2) i =
        (n6Even a : Fin 6 → ZMod 2) (σ⁻¹ i) from rfl,
    show (permWeight 6 σ (n6Even a) : Fin 6 → ZMod 2) j =
        (n6Even a : Fin 6 → ZMod 2) (σ⁻¹ j) from rfl]
  ring

private theorem n6Even_eq_of_sub_const {u v : ↥(evenWeight 6)}
    (h : u - v ∈ constWeight 6) (hu : (u : Fin 6 → ZMod 2) 5 = 0)
    (hv : (v : Fin 6 → ZMod 2) 5 = 0) : u = v := by
  have h' : ∀ i j, (u : Fin 6 → ZMod 2) i - (v : Fin 6 → ZMod 2) i =
      (u : Fin 6 → ZMod 2) j - (v : Fin 6 → ZMod 2) j := h
  apply Subtype.ext
  funext i
  have hi := h' i 5
  rw [hu, hv] at hi
  exact sub_eq_zero.mp (by simpa using hi)

private theorem n6Even_injective : Function.Injective n6Even := by
  intro a b h
  apply Subtype.ext
  exact Multiplicative.toAdd.injective
    (congrArg (fun x : ↥(evenWeight 6) => (x : Fin 6 → ZMod 2)) h)

@[expose] noncomputable def n6Heart : S143.N6 →* Multiplicative (AltHeart 6) where
  toFun a := Multiplicative.ofAdd (QuotientAddGroup.mk (n6Even a))
  map_one' := by
    show Multiplicative.ofAdd (QuotientAddGroup.mk (n6Even 1)) = 1
    rw [n6Even_one]
    simp
  map_mul' a b := by
    show Multiplicative.ofAdd (QuotientAddGroup.mk (n6Even (a * b))) =
      Multiplicative.ofAdd (QuotientAddGroup.mk (n6Even a)) *
        Multiplicative.ofAdd (QuotientAddGroup.mk (n6Even b))
    rw [n6Even_mul a b, QuotientAddGroup.mk_add, ofAdd_add]

theorem n6Heart_bijective : Function.Bijective n6Heart := by
  refine ⟨fun a b h => ?_, fun y => ?_⟩
  · have h' : QuotientAddGroup.mk (n6Even a) = QuotientAddGroup.mk (n6Even b) :=
      congrArg Multiplicative.toAdd h
    exact n6Even_injective
      (n6Even_eq_of_sub_const (QuotientAddGroup.eq_iff_sub_mem.mp h')
        (S143.mem_n6Sub_iff.1 a.2).2 (S143.mem_n6Sub_iff.1 b.2).2)
  · obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd y)
    by_cases hx5 : (x : Fin 6 → ZMod 2) 5 = 0
    · let w : S143.N6 := ⟨Multiplicative.ofAdd x,
        S143.mem_n6Sub_iff.2 ⟨by rw [toAdd_ofAdd]; exact S6B.sum_eq_zero_of_mem x.2,
          by rw [toAdd_ofAdd]; exact hx5⟩⟩
      refine ⟨w, ?_⟩
      have hwe : n6Even w = x := Subtype.ext (by simp [n6Even, w])
      rw [show n6Heart w = Multiplicative.ofAdd (QuotientAddGroup.mk (n6Even w)) from rfl,
        hwe, hx, ofAdd_toAdd]
    · have hx5' : (x : Fin 6 → ZMod 2) 5 = 1 := zmod_two_eq_one_of_ne_zero hx5
      have ha5 : ((x + n6Ones : ↥(evenWeight 6)) : Fin 6 → ZMod 2) 5 = 0 := by
        show (x : Fin 6 → ZMod 2) 5 + (n6Ones : Fin 6 → ZMod 2) 5 = 0
        rw [n6Ones_apply, hx5']
        decide
      have haeven : ∑ i, ((x + n6Ones : ↥(evenWeight 6)) : Fin 6 → ZMod 2) i = 0 := by
        simp only [AddSubgroup.coe_add, Pi.add_apply]
        rw [Finset.sum_add_distrib, S6B.sum_eq_zero_of_mem x.2, n6Ones_sum, add_zero]
      let w : S143.N6 := ⟨Multiplicative.ofAdd (x + n6Ones),
        S143.mem_n6Sub_iff.2 ⟨by rw [toAdd_ofAdd]; exact haeven,
          by rw [toAdd_ofAdd]; exact ha5⟩⟩
      have hconst : n6Ones ∈ constWeight 6 := by intro i j; rfl
      refine ⟨w, ?_⟩
      have hwe : n6Even w = x + n6Ones := Subtype.ext (by simp [n6Even, w])
      rw [show n6Heart w = Multiplicative.ofAdd (QuotientAddGroup.mk (n6Even w)) from rfl,
        hwe, QuotientAddGroup.mk_add,
        (QuotientAddGroup.eq_zero_iff (N := constWeight 6) n6Ones).mpr hconst, add_zero, hx,
        ofAdd_toAdd]

@[expose] noncomputable def n6Crd : S143.N6 →* StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  S6B.crdHom.comp n6Heart

theorem n6Crd_bijective : Function.Bijective n6Crd :=
  S6B.crdHom_bijective.comp n6Heart_bijective

theorem n6Crd_act (σ : Equiv.Perm (Fin 6)) (a : S143.N6) :
    Multiplicative.toAdd (n6Crd (S143.n6Act σ a)) =
      (((S6B.thetaTwo σ : ↥(StatedSp 2 (ZMod 2))) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ Multiplicative.toAdd (n6Crd a) := by
  change S6B.heartCrd (QuotientAddGroup.mk (n6Even (S143.n6Act σ a))) =
    (((S6B.thetaTwo σ : ↥(StatedSp 2 (ZMod 2))) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ
      S6B.heartCrd (QuotientAddGroup.mk (n6Even a))
  rw [← S6B.heartCrd_perm σ (n6Even a), n6Even_act_class]

theorem n6Crd_act_natHomI (σ : Equiv.Perm (Fin 6)) (a : S143.N6) :
    n6Crd (S143.n6Act σ a) =
      natHomI (Fin 2 ⊕ Fin 2) (ZMod 2)
        ((S6B.thetaTwo σ : ↥(StatedSp 2 (ZMod 2))) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (n6Crd a) := by
  apply Multiplicative.toAdd.injective
  rw [n6Crd_act]
  rfl

theorem mem_natSubI_iff (γ : MulAut (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod 2))) :
    γ ∈ natSubI (Fin 2 ⊕ Fin 2) (ZMod 2) (StatedSp 2 (ZMod 2)) ↔
      ∃ σ : Equiv.Perm (Fin 6), γ = natHomI (Fin 2 ⊕ Fin 2) (ZMod 2)
        ((S6B.thetaTwo σ : ↥(StatedSp 2 (ZMod 2))) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
  rw [natSubI, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨σ, hσ⟩ := S6B.thetaTwo.surjective ⟨g, hg⟩
    exact ⟨σ, by rw [hσ]⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨((S6B.thetaTwo σ : ↥(StatedSp 2 (ZMod 2))) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)),
      (S6B.thetaTwo σ).2, rfl⟩

end CFSG.ASVolI.H16
