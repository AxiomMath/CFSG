module

public import CFSG.Quasithin.MS93.S37Tor
public import CFSG.Quasithin.MS93.S37Type

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem exists_of_comm_transv {x : G} (hx : x ∈ pCoreOf 2 M)
    (h : ∀ c : F, ∃ (t : G) (ht : t ∈ L ⊔ pCoreOf 2 M),
      C.rho ⟨t, ht⟩ = transv (e₁ F) c ∧ ⁅t, x⁆ ∈ Dq M L) :
    ∃ u ∈ C.Usub (perp (pt₀ F)), u⁻¹ * x ∈ Dq M L := by
  have key : ∀ (t : G) (ht : t ∈ L ⊔ pCoreOf 2 M), C.rho ⟨t, ht⟩ ∈ X₂ F → ⁅t, x⁆ ∈ Dq M L := by
    intro t ht htX
    obtain ⟨c, hc⟩ := mem_X₂_iff.1 htX
    obtain ⟨t₀, ht₀, hρ, hD⟩ := h c
    set y := t₀⁻¹ * t with hy
    have hyK : y ∈ L ⊔ pCoreOf 2 M := (L ⊔ pCoreOf 2 M).mul_mem
      ((L ⊔ pCoreOf 2 M).inv_mem ht₀) ht
    have hyQ : y ∈ pCoreOf 2 M := by
      refine (C.rho_eq_one_iff ⟨y, hyK⟩).1 ?_
      have e : (⟨y, hyK⟩ : ↥(L ⊔ pCoreOf 2 M)) = (⟨t₀, ht₀⟩)⁻¹ * ⟨t, ht⟩ := rfl
      rw [e, map_mul, map_inv, hρ, hc, inv_mul_cancel]
    have hyx : ⁅y, x⁆ ∈ Dq M L :=
      commutator_pCore_le_Dq C.h C.hVU (Subgroup.commutator_mem_commutator hyQ hx)
    have ht₀M : t₀ ∈ M := C.sup_le_M ht₀
    have hconj : t₀ * ⁅y, x⁆ * t₀⁻¹ ∈ Dq M L :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_Dq C.h.le_normalizer ht₀M) _).1 hyx
    have e : ⁅t, x⁆ = t₀ * ⁅y, x⁆ * t₀⁻¹ * ⁅t₀, x⁆ := by
      rw [hy]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Dq M L).mul_mem hconj hD
  obtain ⟨u, hu, hco, hd⟩ := C.mem_of_comm_X₂ hx key
  exact ⟨u, (C.mem_Usub).2 ⟨hu, hco⟩, hd⟩

theorem inf_Qt_of_rhoIm (θ : MulAut ↥(T1 M T L)) (hE : C.rhoIm (Ut M T L θ) = X₂ F) :
    ∀ x ∈ pCoreOf 2 M ⊓ Qt M θ, ∃ u ∈ C.Usub (perp (pt₀ F)), u⁻¹ * x ∈ Dq M L := by
  intro x hx
  refine C.exists_of_comm_transv hx.1 fun c => ?_
  have hm : transv (e₁ F) c ∈ C.rhoIm (Ut M T L θ) := by
    rw [hE]
    exact transv_mem_X₂ c
  obtain ⟨t, htK, ht, hρ⟩ := (C.mem_rhoIm).1 hm
  refine ⟨t, htK, hρ, ?_⟩
  have hxc := hx.2
  rw [C.Qt_eq C.pCore_le_T1 T1_le_T] at hxc
  have hc : t * x = x * t := Subgroup.mem_centralizer_iff.1 hxc.2 t ht
  rw [commutatorElement_def, hc, mul_inv_cancel_right, mul_inv_cancel]
  exact (Dq M L).one_mem

theorem relIndex_Usub_perp : (C.Usub (perp (pt₀ F))).relIndex (Uq M T L) = Nat.card F := by
  let f : ↥(Uq M T L) →* Multiplicative F :=
    { toFun := fun u => Multiplicative.ofAdd (C.N.co u (.inr 0))
      map_one' := by simp [C.N.co_one]
      map_mul' := fun u v => by simp [C.N.co_mul] }
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨u, hu⟩ := C.N.co_surj (Multiplicative.toAdd c • f₁ F)
    refine ⟨u, ?_⟩
    show Multiplicative.ofAdd (C.N.co u (.inr 0)) = c
    rw [hu]
    simp [f₁]
  have hker : f.ker = (C.Usub (perp (pt₀ F))).subgroupOf (Uq M T L) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, C.mem_Usub]
    constructor
    · intro h
      refine ⟨u.2, mem_perp_pt₀.2 ?_⟩
      have h1 : Multiplicative.ofAdd (C.N.co u (.inr 0)) = 1 := h
      simpa using h1
    · rintro ⟨hu, hp⟩
      show Multiplicative.ofAdd (C.N.co u (.inr 0)) = 1
      rw [mem_perp_pt₀.1 hp]
      rfl
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hf,
    Subgroup.card_top]
  rfl

theorem Usub_sup_inf_Uq :
    (C.Usub (perp (pt₀ F)) ⊔ Dq M L) ⊓ Uq M T L = C.Usub (perp (pt₀ F)) := by
  refine le_antisymm ?_ (le_inf le_sup_left (C.Usub_le _))
  rintro x ⟨hxP, hxU⟩
  have hn : C.Usub (perp (pt₀ F)) ≤ Subgroup.normalizer (Dq M L : Set G) :=
    ((C.Usub_le _).trans (Uq_le C.h.L_le)).trans (le_normalizer_Dq C.h.le_normalizer)
  have hxP' : x ∈ ((C.Usub (perp (pt₀ F)) ⊔ Dq M L : Subgroup G) : Set G) := hxP
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hxP'
  obtain ⟨u, hu, d, hd, rfl⟩ := hxP'
  obtain ⟨huU, hco⟩ := (C.mem_Usub).1 hu
  have hdU : d ∈ Uq M T L := by
    have e : d = u⁻¹ * (u * d) := by group
    rw [e]
    exact (Uq M T L).mul_mem ((Uq M T L).inv_mem huU) hxU
  refine (C.mem_Usub).2 ⟨hxU, ?_⟩
  have e : (⟨u * d, hxU⟩ : ↥(Uq M T L)) = ⟨u, huU⟩ * ⟨d, hdU⟩ := rfl
  rw [e, C.N.co_mul, (C.N.co_eq_zero_iff ⟨d, hdU⟩).2 ⟨hdU, hd.2⟩, add_zero]
  exact hco

theorem pCore_eq_of_rhoIm (θ : MulAut ↥(T1 M T L)) (hE : C.rhoIm (Ut M T L θ) = X₂ F)
    (hN : C.rhoIm (Qt M θ) = X₂ F) :
    Uq M T L ⊔ Dq M L = pCoreOf 2 M ∧
      pCoreOf 2 M ⊓ Qt M θ = C.Usub (perp (pt₀ F)) ⊔ Dq M L := by
  set P := C.Usub (perp (pt₀ F)) ⊔ Dq M L with hP
  set UD := Uq M T L ⊔ Dq M L with hUD
  have hUQ : Uq M T L ≤ pCoreOf 2 M := C.Uq_le_pCore
  have hDQ : Dq M L ≤ pCoreOf 2 M := inf_le_left
  have hUDQ : UD ≤ pCoreOf 2 M := sup_le hUQ hDQ
  have hPUD : P ≤ UD := sup_le_sup_right (C.Usub_le _) _
  have h1 : pCoreOf 2 M ⊓ Qt M θ ≤ P := by
    intro x hx
    obtain ⟨u, hu, hd⟩ := C.inf_Qt_of_rhoIm θ hE x hx
    have e : x = u * (u⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hu hd
  have h2 : Nat.card F * Nat.card ↥(pCoreOf 2 M ⊓ Qt M θ) = Nat.card ↥(pCoreOf 2 M) := by
    have c1 := C.card_rhoIm (Qt_le_sup θ)
    rw [hN, card_X₂] at c1
    have c2 := Subgroup.relIndex_mul_card (pCoreOf 2 M) (Qt M θ)
    rw [← c1, card_tImage θ C.pCore_le_T1] at c2
    exact c2
  have h3 : Nat.card ↥UD = Nat.card F * Nat.card ↥P := by
    have hn : UD ≤ Subgroup.normalizer (Uq M T L : Set G) := hUDQ.trans
      ((pCoreOf_le' M).trans C.hMU)
    have hsup : Uq M T L ⊔ P = UD := by
      refine le_antisymm (sup_le le_sup_left hPUD) (sup_le le_sup_left ?_)
      exact le_sup_right.trans le_sup_right
    have e1 := relIndex_eq_of_sup le_sup_left hPUD hn hsup
    rw [← Subgroup.inf_relIndex_right, C.Usub_sup_inf_Uq, C.relIndex_Usub_perp] at e1
    have c := Subgroup.relIndex_mul_card P UD
    rw [inf_eq_left.2 hPUD, ← e1] at c
    exact c.symm
  have h4 : Nat.card ↥(pCoreOf 2 M ⊓ Qt M θ) ≤ Nat.card ↥P := Subgroup.card_le_of_le h1
  have h5 : Nat.card ↥UD ≤ Nat.card ↥(pCoreOf 2 M) := Subgroup.card_le_of_le hUDQ
  have hq : 0 < Nat.card F := Nat.card_pos
  have h6 : Nat.card ↥UD = Nat.card ↥(pCoreOf 2 M) := by
    refine le_antisymm h5 ?_
    rw [← h2, h3]
    exact Nat.mul_le_mul_left _ h4
  have h7 : Nat.card ↥(pCoreOf 2 M ⊓ Qt M θ) = Nat.card ↥P := by
    refine le_antisymm h4 ?_
    have := h6
    rw [h3, ← h2] at this
    exact (Nat.eq_of_mul_eq_mul_left hq this).le
  exact ⟨Subgroup.eq_of_le_of_card_ge hUDQ h6.ge, Subgroup.eq_of_le_of_card_ge h1 h7.ge⟩

theorem exists_of_sup_eq (h : Uq M T L ⊔ Dq M L = pCoreOf 2 M) :
    ∀ x ∈ pCoreOf 2 M, ∃ u ∈ Uq M T L, u⁻¹ * x ∈ Dq M L := by
  intro x hx
  have hn : Uq M T L ≤ Subgroup.normalizer (Dq M L : Set G) :=
    (Uq_le C.h.L_le).trans (le_normalizer_Dq C.h.le_normalizer)
  have hx' : x ∈ ((Uq M T L ⊔ Dq M L : Subgroup G) : Set G) := by
    rw [h]
    exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hx'
  obtain ⟨u, hu, d, hd, rfl⟩ := hx'
  exact ⟨u, hu, by rwa [inv_mul_cancel_left]⟩

theorem isGood_of_rhoIm (θ : MulAut ↥(T1 M T L)) (hE : C.rhoIm (Ut M T L θ) = X₂ F)
    (hN : C.rhoIm (Qt M θ) = X₂ F) (hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F)
    (hN' : C.rhoIm (Qt M θ⁻¹) = X₂ F) : C.IsGood θ := by
  obtain ⟨-, h2⟩ := C.pCore_eq_of_rhoIm θ hE hN
  obtain ⟨-, h2'⟩ := C.pCore_eq_of_rhoIm θ⁻¹ hE' hN'
  have hD : Dq M L ≤ Qt M θ := fun d hd =>
    (h2 ▸ (le_sup_right : Dq M L ≤ C.Usub (perp (pt₀ F)) ⊔ Dq M L) hd :
      d ∈ pCoreOf 2 M ⊓ Qt M θ).2
  have hD' : Dq M L ≤ Qt M θ⁻¹ := fun d hd =>
    (h2' ▸ (le_sup_right : Dq M L ≤ C.Usub (perp (pt₀ F)) ⊔ Dq M L) hd :
      d ∈ pCoreOf 2 M ⊓ Qt M θ⁻¹).2
  refine ⟨hE, hN, C.inf_Qt_of_rhoIm θ hE, ?_, hD⟩
  have h := tImage_mono' θ hD'
  rwa [tImage_tImage_inv' θ C.pCore_le_T1] at h

end Cfg

end CFSG.Quasithin.MS93.S37
