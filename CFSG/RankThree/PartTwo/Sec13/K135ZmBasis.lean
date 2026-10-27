module

public import CFSG.RankThree.PartTwo.Sec13.F135LastDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open Subgroup

section Basis

open scoped IsMulCommutative

@[expose] noncomputable def fcPowHom {C : Type*} [CommGroup C] {n : ℕ} (v : Fin n → C)
    (hv : ∀ i, v i ^ 4 = 1) : Multiplicative (Fin n → ZMod 4) →* C where
  toFun a := ∏ i, v i ^ (Multiplicative.toAdd a i).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

variable {L : Type*} [Group L] {n : ℕ} (x : Fin n → L)

@[expose] def fcBasisProd (a : Fin n → ZMod 4) : L := (List.ofFn fun i => x i ^ (a i).val).prod

variable {x} (hx : ∀ i, x i ^ 4 = 1) (hc : ∀ i j, Commute (x i) (x j))
include hx hc

@[expose] noncomputable def fcBasisHom :
    Multiplicative (Fin n → ZMod 4) →* closure (Set.range x) :=
  haveI : IsMulCommutative (closure (Set.range x)) :=
    isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
  fcPowHom (fun i => ⟨x i, subset_closure ⟨i, rfl⟩⟩) (fun i => Subtype.ext (by simpa using hx i))

theorem coe_fcBasisHom (a : Multiplicative (Fin n → ZMod 4)) :
    (fcBasisHom hx hc a : L) = fcBasisProd x (Multiplicative.toAdd a) := by
  have : IsMulCommutative (closure (Set.range x)) :=
    isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
  rw [fcBasisProd]
  change ((∏ i, (⟨x i, subset_closure ⟨i, rfl⟩⟩ : closure (Set.range x)) ^
    (Multiplicative.toAdd a i).val : closure (Set.range x)) : L) = _
  rw [← Fin.prod_ofFn, ← (closure (Set.range x)).coe_subtype, map_list_prod, List.map_ofFn]
  rfl

theorem fcBasisHom_single (i : Fin n) :
    fcBasisHom hx hc (Multiplicative.ofAdd (Pi.single i 1)) = ⟨x i, subset_closure ⟨i, rfl⟩⟩ := by
  have : IsMulCommutative (closure (Set.range x)) :=
    isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
  change ∏ j, (⟨x j, subset_closure ⟨j, rfl⟩⟩ : closure (Set.range x)) ^
    ((Pi.single i (1 : ZMod 4) : Fin n → ZMod 4) j).val = _
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp [show (1 : ZMod 4).val = 1 from rfl]

theorem fcBasisHom_surjective : Function.Surjective (fcBasisHom hx hc) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← map_subtype_le_map_subtype, ← MonoidHom.range_eq_map,
    range_subtype, closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨_, ⟨_, fcBasisHom_single hx hc i⟩, rfl⟩

theorem fcBasisProd_mem (f : Fin n → ZMod 4) : fcBasisProd x f ∈ closure (Set.range x) := by
  have := coe_fcBasisHom hx hc (Multiplicative.ofAdd f)
  rw [toAdd_ofAdd] at this
  rw [← this]
  exact Subtype.mem _

theorem fcBasisProd_add (f g : Fin n → ZMod 4) :
    fcBasisProd x (f + g) = fcBasisProd x f * fcBasisProd x g := by
  have h1 := coe_fcBasisHom hx hc (Multiplicative.ofAdd (f + g))
  have h2 := coe_fcBasisHom hx hc (Multiplicative.ofAdd f)
  have h3 := coe_fcBasisHom hx hc (Multiplicative.ofAdd g)
  rw [toAdd_ofAdd] at h1 h2 h3
  rw [← h1, ← h2, ← h3, ofAdd_add, map_mul]
  rfl

theorem fcBasisProd_zero : fcBasisProd x (0 : Fin n → ZMod 4) = 1 := by
  have h1 := coe_fcBasisHom hx hc (Multiplicative.ofAdd (0 : Fin n → ZMod 4))
  rw [toAdd_ofAdd] at h1
  rw [← h1, ofAdd_zero, map_one]
  rfl

theorem exists_fcBasisProd {g : L} (hg : g ∈ closure (Set.range x)) : ∃ f, g = fcBasisProd x f := by
  obtain ⟨b, hb⟩ := fcBasisHom_surjective hx hc ⟨g, hg⟩
  exact ⟨Multiplicative.toAdd b, by rw [← coe_fcBasisHom hx hc, hb]⟩

variable (hinj : Function.Injective (fcBasisProd x))
include hinj

theorem fcBasisHom_injective : Function.Injective (fcBasisHom hx hc) := by
  intro a b hab
  have := congrArg Subtype.val hab
  rw [coe_fcBasisHom, coe_fcBasisHom] at this
  exact Multiplicative.toAdd.injective (hinj this)

@[expose] noncomputable def fcBasisEquiv :
    Multiplicative (Fin n → ZMod 4) ≃* closure (Set.range x) :=
  MulEquiv.ofBijective (fcBasisHom hx hc) ⟨fcBasisHom_injective hx hc hinj, fcBasisHom_surjective hx hc⟩

theorem card_closure_fcBasis : Nat.card (closure (Set.range x)) = 4 ^ n := by
  rw [← Nat.card_congr (fcBasisEquiv hx hc hinj).toEquiv]
  simp [Nat.card_eq_fintype_card]

end Basis

section Abstract

open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem mem_normalizer_closure_of_conj_mem_fin {S : Set G} {s : G} [Finite (closure S)]
    (h : ∀ y ∈ S, s * y * s⁻¹ ∈ closure S) : s ∈ normalizer (closure S : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (closure S).map (MulAut.conj s).toMonoidHom ≤ closure S := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro y hy
    exact h y hy
  exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective (MulAut.conj s).injective).ge

theorem fourCubeSeven_of_basis {a : Fin 3 → G} (ha : ∀ i, a i ^ 4 = 1)
    (hc : ∀ i j, Commute (a i) (a j)) (hinj : Function.Injective (fcBasisProd a))
    {x : G} (hx : orderOf x = 7) (M : Fin 3 → Fin 3 → ZMod 4)
    (hconj : ∀ j, x * a j * x⁻¹ = fcBasisProd a fun i => M i j)
    (hfpf : ∀ f : Fin 3 → ZMod 4, f + f = 0 → f ≠ 0 →
      x * fcBasisProd a f * x⁻¹ ≠ fcBasisProd a f) :
    FourCubeSeven (closure (Set.range a)) x := by
  have hcomm : IsMulCommutative (closure (Set.range a)) :=
    isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
  have hab : ∀ g ∈ closure (Set.range a), ∀ h ∈ closure (Set.range a), g * h = h * g :=
    fun g hg h hh =>
      congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : closure (Set.range a)) ⟨h, hh⟩)
  have hcard : Nat.card (closure (Set.range a)) = 4 ^ 3 := card_closure_fcBasis ha hc hinj
  haveI hfin : Finite (closure (Set.range a)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hexp : ∀ g ∈ closure (Set.range a), g ^ 4 = 1 := by
    intro g hg
    induction hg using closure_induction with
    | mem _ h =>
      obtain ⟨i, rfl⟩ := h
      exact ha i
    | one => exact one_pow 4
    | mul g h hg hh h₁ h₂ => rw [(show Commute g h from hab g hg h hh).mul_pow, h₁, h₂, one_mul]
    | inv g _ h => rw [inv_pow, h, inv_one]
  refine ⟨hab, hcard, hexp, ?_, hx, ?_, ?_⟩
  ·
    let e := fcBasisEquiv ha hc hinj
    have hcongr : Nat.card {g : closure (Set.range a) | g ^ 2 = 1} =
        Nat.card {f : Multiplicative (Fin 3 → ZMod 4) | f ^ 2 = 1} := by
      refine Nat.card_congr (e.toEquiv.subtypeEquiv fun f => ?_).symm
      change f ^ 2 = 1 ↔ (e f) ^ 2 = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff]
    rw [hcongr]
    have h8 : Nat.card {f : Multiplicative (Fin 3 → ZMod 4) | f ^ 2 = 1} = 8 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [h8]
    norm_num
  ·
    refine mem_normalizer_closure_of_conj_mem_fin ?_
    rintro _ ⟨j, rfl⟩
    rw [hconj j]
    exact fcBasisProd_mem ha hc _
  ·
    intro g hg hg2 hgx
    obtain ⟨f, rfl⟩ := exists_fcBasisProd ha hc hg
    have hff : f + f = 0 := by
      apply hinj
      rw [fcBasisProd_add ha hc, fcBasisProd_zero ha hc, ← sq]
      exact hg2
    by_cases hf0 : f = 0
    · rw [hf0, fcBasisProd_zero ha hc]
    · exact absurd hgx (hfpf f hff hf0)

end Abstract

end CFSG.RankThree.PartTwo.Sec13.F135Last
