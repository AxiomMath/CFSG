module

public import CFSG.Quasithin.Vol2.Ch10SecECase2
public import CFSG.Quasithin.Vol2.Ch10SecES5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] {T L I : Subgroup G}

theorem mem_alternatingGroup_of_pow_three {σ : Equiv.Perm (Fin 5)} (h3 : σ ^ 3 = 1) :
    σ ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h := congrArg Equiv.Perm.sign h3
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

theorem vThree_eq : vThree = (Pi.single 3 1 + Pi.single 4 1 : Fin 5 → ZMod 2) := by
  decide

theorem case2_elements (h2 : Ch10.Case10_1_1Two T L I) :
    ∃ x ∈ L, ∃ y ∈ L, ∃ w ∈ fsuUL T L I, x * w * x⁻¹ = w ∧ y * w * y⁻¹ ≠ w ∧
      w ∈ ⁅fsuUL T L I, L⁆ ∧ ∃ v ∈ fsuUL T L I, x * x * v * (x * x)⁻¹ ≠ v := by
  obtain ⟨-, hcU, π, hπ⟩ := h2
  obtain ⟨β, hβs, hβk, hβe⟩ := RealizesVia.coordSec altDn_five_ker hπ
  have hβinj : ∀ u u' : ↥(⊤ : Subgroup ↥(fsuUL T L I)), β u = β u' → u = u' := by
    intro u u' h
    have h1 : β (u⁻¹ * u') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h3 := (hβk _).mp h1
    rw [Subgroup.mem_bot] at h3
    have h4 : u⁻¹ * u' = 1 := Subtype.ext h3
    rw [← mul_left_cancel_iff (a := u⁻¹), h4, inv_mul_cancel]
  have hcoord : ∀ (γ : ↥(alternatingGroup (Fin 5))) (u : ↥(⊤ : Subgroup ↥(fsuUL T L I)))
      (e : Fin 5 → ZMod 2) (_ : isEven e),
      β u = ⟨Multiplicative.ofAdd e, ‹_›⟩ →
      ((β ⟨((π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) (u : ↥(fsuUL T L I)),
        Subgroup.mem_top _⟩ : ↥(FFModel.altDn 5).sec) : (FFModel.altDn 5).Amb) =
        Multiplicative.ofAdd (pact (γ : Equiv.Perm (Fin 5)) e) := by
    intro γ u e _ hu
    rw [hβe γ u (Subgroup.mem_top _), hu]
    rfl
  have hconj : ∀ γ : ↥(alternatingGroup (Fin 5)), ∃ g ∈ L,
      ∀ u : ↥(fsuUL T L I), (((π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) u :
        G) = g * u * g⁻¹ := by
    intro γ
    obtain ⟨g, hgL, hg⟩ := SecA.mem_autOn_iff'.mp (π γ).2
    exact ⟨g, hgL, fun u => by rw [← hg, SecA.coe_conjAct_apply']⟩
  obtain ⟨x, hxL, hx⟩ := hconj ⟨cThree, cThree_mem_alt⟩
  obtain ⟨y, hyL, hy⟩ := hconj ⟨cThree', cThree'_mem_alt⟩
  obtain ⟨w, hw⟩ := hβs ⟨Multiplicative.ofAdd vThree, isEven_vThree⟩
  have hfixw : ∀ γ : ↥(alternatingGroup (Fin 5)),
      pact (γ : Equiv.Perm (Fin 5)) vThree = vThree →
      ((π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) (w : ↥(fsuUL T L I)) = w := by
    intro γ hγ
    have h1 := hcoord γ w vThree isEven_vThree hw
    rw [hγ] at h1
    have h3 := hβinj _ w (Subtype.ext (h1.trans (congrArg Subtype.val hw).symm))
    exact congrArg Subtype.val h3
  have hxw : x * ((w : ↥(fsuUL T L I)) : G) * x⁻¹ = ((w : ↥(fsuUL T L I)) : G) := by
    rw [← hx]
    exact congrArg Subtype.val (hfixw ⟨cThree, cThree_mem_alt⟩ pact_cThree_vThree)
  have hyw : y * ((w : ↥(fsuUL T L I)) : G) * y⁻¹ ≠ ((w : ↥(fsuUL T L I)) : G) := by
    intro h5
    apply pact_cThree'_vThree
    have h1 := hcoord ⟨cThree', cThree'_mem_alt⟩ w vThree isEven_vThree hw
    have e : (⟨((π ⟨cThree', cThree'_mem_alt⟩ : ↥(autOn L (fsuUL T L I))) :
        MulAut ↥(fsuUL T L I)) (w : ↥(fsuUL T L I)), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup ↥(fsuUL T L I))) = w := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hy]
      exact h5
    rw [e, hw] at h1
    exact (Multiplicative.ofAdd.injective h1).symm
  refine ⟨x, hxL, y, hyL, _, (w : ↥(fsuUL T L I)).2, hxw, hyw, ?_, ?_⟩
  ·
    obtain ⟨σ, hσ3, -, z₀, hz₀, he⟩ := exists_comm_pair 3 4 (by decide)
    obtain ⟨z, hzL, hz⟩ := hconj ⟨σ, mem_alternatingGroup_of_pow_three hσ3⟩
    obtain ⟨u, hu⟩ := hβs ⟨Multiplicative.ofAdd z₀, hz₀⟩
    set u₁ : ↥(⊤ : Subgroup ↥(fsuUL T L I)) :=
      ⟨((π ⟨σ, mem_alternatingGroup_of_pow_three hσ3⟩ : ↥(autOn L (fsuUL T L I))) :
        MulAut ↥(fsuUL T L I)) (u : ↥(fsuUL T L I)), Subgroup.mem_top _⟩ with hu₁
    have h1 := hcoord ⟨σ, mem_alternatingGroup_of_pow_three hσ3⟩ u z₀ hz₀ hu
    have hwu : u₁ * u⁻¹ = w := by
      apply hβinj
      apply Subtype.ext
      rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, h1, hu, hw]
      show Multiplicative.ofAdd (pact σ z₀) * (Multiplicative.ofAdd z₀)⁻¹ =
        Multiplicative.ofAdd vThree
      rw [← ofAdd_neg, ← ofAdd_add, vThree_eq, ← he,
        show -z₀ = z₀ from funext fun i => ZMod.neg_eq_self_mod_two (z₀ i)]
    have hw' : ((w : ↥(fsuUL T L I)) : G) =
        z * ((u : ↥(fsuUL T L I)) : G) * z⁻¹ * ((u : ↥(fsuUL T L I)) : G)⁻¹ := by
      rw [← hwu]
      show ((u₁ : ↥(fsuUL T L I)) : G) * ((u : ↥(fsuUL T L I)) : G)⁻¹ = _
      rw [hu₁, hz]
    rw [hw', Subgroup.commutator_comm, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hzL (u : ↥(fsuUL T L I)).2
  ·
    obtain ⟨v, hv⟩ := hβs ⟨Multiplicative.ofAdd vTwo, isEven_vTwo⟩
    refine ⟨_, (v : ↥(fsuUL T L I)).2, fun h => pact_cThree_sq_vTwo ?_⟩
    set v₁ : ↥(⊤ : Subgroup ↥(fsuUL T L I)) :=
      ⟨((π ⟨cThree, cThree_mem_alt⟩ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))
        (v : ↥(fsuUL T L I)), Subgroup.mem_top _⟩ with hv₁
    have hev : isEven (pact cThree vTwo) := by decide
    have h1 := hcoord ⟨cThree, cThree_mem_alt⟩ v vTwo isEven_vTwo hv
    have h1' : β v₁ = ⟨Multiplicative.ofAdd (pact cThree vTwo), hev⟩ := Subtype.ext h1
    have h3 := hcoord ⟨cThree, cThree_mem_alt⟩ v₁ _ hev h1'
    have e : (⟨((π ⟨cThree, cThree_mem_alt⟩ : ↥(autOn L (fsuUL T L I))) :
        MulAut ↥(fsuUL T L I)) (v₁ : ↥(fsuUL T L I)), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup ↥(fsuUL T L I))) = v := by
      apply Subtype.ext
      apply Subtype.ext
      have e1 : (((v₁ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) : ↥(fsuUL T L I)) : G) =
          x * ((v : ↥(fsuUL T L I)) : G) * x⁻¹ := hx _
      show ((((π ⟨cThree, cThree_mem_alt⟩ : ↥(autOn L (fsuUL T L I))) :
        MulAut ↥(fsuUL T L I)) (v₁ : ↥(fsuUL T L I)) : ↥(fsuUL T L I)) : G) = _
      rw [hx, e1]
      calc x * (x * ((v : ↥(fsuUL T L I)) : G) * x⁻¹) * x⁻¹ =
          x * x * ((v : ↥(fsuUL T L I)) : G) * (x * x)⁻¹ := by group
        _ = _ := h
    rw [e, hv] at h3
    rw [CFSG.QuasithinUnique.A5.Delta5.pact_mul]
    exact (Multiplicative.ofAdd.injective h3).symm

end CFSG.Quasithin.Vol2.Ch10.SecE
