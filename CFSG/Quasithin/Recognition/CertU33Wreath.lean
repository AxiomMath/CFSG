module

public import CFSG.Quasithin.Recognition.CertU33DcPG
public import Certificates.Certificate8082

public section

namespace CFSG.Quasithin

open CFSG.CosetTable CFSG.Sporadic.Bridge CFSG.Open

theorem u33C_check :
    Finite (PG 3 u33CRels) ∧ Nat.card (PG 3 u33CRels) ≤ 32 :=
  Certificates.certificate8082

theorem u33C_card_le :
    Finite (PG 3 u33CRels) ∧ Nat.card (PG 3 u33CRels) ≤ 32 :=
  u33C_check

theorem lift_mk' {G : Type*} [Group G] {m : ℕ} (img : ℕ → G) (w : List (Fin m × Bool)) :
    FreeGroup.lift (fun i : Fin m => img i.val) (FreeGroup.mk w) =
      wordProd img (w.map fun l => (l.1.val, l.2)) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [show FreeGroup.mk (x :: w) = FreeGroup.mk [x] * FreeGroup.mk w from rfl, map_mul, ih]
    obtain ⟨i, b⟩ := x
    cases b with
    | true =>
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, ↓reduceIte]
    | false =>
      rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, Bool.false_eq_true, ↓reduceIte]

theorem u33CRels_perm : ∀ w ∈ u33CRels, wordProd u33GenP (w.map fun l => (l.1.val, l.2)) = 1 := by
  decide +kernel

noncomputable def u33CHom :
    PG 3 u33CRels →* U33G :=
  PresentedGroup.toGroup (f := fun i : Fin 3 => u33GenPG i.val) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [lift_mk']
    apply u33PresHom_injective
    rw [map_one, u33PresHom_wordProd']
    exact u33CRels_perm w hw)

theorem u33CHom_of
    (i : Fin 3) : u33CHom (PresentedGroup.of i) = u33GenPG i.val := by
  rw [u33CHom, PresentedGroup.toGroup.of]

theorem range_u33CHom :
    u33CHom.range = u33Data.T := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    {r : FreeGroup (Fin 3) | r ∈ u33CRels.map FreeGroup.mk}, MonoidHom.map_closure]
  unfold OvergroupData.T
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rw [u33CHom_of]
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, u33CHom_of 0⟩
    · exact ⟨1, u33CHom_of 1⟩
    · exact ⟨2, u33CHom_of 2⟩

theorem u33C_mulEquiv_T :
    Nonempty (PG 3 u33CRels ≃* u33Data.T) := by
  obtain ⟨hfin, hle⟩ := u33C_card_le
  have hbij : Function.Bijective u33CHom.rangeRestrict :=
    u33CHom.rangeRestrict_surjective.bijective_of_nat_card_le (by
      rw [range_u33CHom, u33_card_T]; exact hle)
  exact ⟨(MulEquiv.ofBijective u33CHom.rangeRestrict hbij).trans
    (MulEquiv.subgroupCongr range_u33CHom)⟩

private instance : DecidableEq (WreathedTwoGroup 2) := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

@[expose] def wrImg : Fin 3 → WreathedTwoGroup 2
  | 0 => ⟨fun q => if q = 1 then Multiplicative.ofAdd (1 : ZMod (2 ^ 2)) else 1, 1⟩
  | 1 => ⟨fun q => if q = 1 then 1 else Multiplicative.ofAdd (1 : ZMod (2 ^ 2)), 1⟩
  | 2 => ⟨fun _ => 1, Multiplicative.ofAdd (1 : ZMod 2)⟩

@[expose] def wrGen (i : ℕ) : WreathedTwoGroup 2 := if h : i < 3 then wrImg ⟨i, h⟩ else 1

theorem wrGen_relators : ∀ w ∈ u33CRels, wordProd wrGen (w.map fun l => (l.1.val, l.2)) = 1 := by
  decide +kernel

noncomputable def wrHom : PG 3 u33CRels →* WreathedTwoGroup 2 :=
  PresentedGroup.toGroup (f := fun i : Fin 3 => wrGen i.val) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [lift_mk']
    exact wrGen_relators w hw)

theorem wrHom_of (i : Fin 3) : wrHom (PresentedGroup.of i) = wrGen i.val := by
  rw [wrHom, PresentedGroup.toGroup.of]

theorem wr_inj : ∀ i j : Fin 32, wordProd wrGen (u33TelW i) = wordProd wrGen (u33TelW j) →
    i = j := by
  decide +kernel

theorem card_wreathed_two : Nat.card (WreathedTwoGroup 2) = 32 := by
  have h := RegularWreathProduct.card (D := Multiplicative (ZMod (2 ^ 2)))
    (Q := Multiplicative (ZMod 2))
  have h1 : Nat.card (Multiplicative (ZMod (2 ^ 2))) = 4 := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod (2 ^ 2))), Nat.card_zmod]; norm_num
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod 2)), Nat.card_zmod]
  change Nat.card (Multiplicative (ZMod (2 ^ 2)) ≀ᵣ Multiplicative (ZMod 2)) = 32
  rw [h, h1, h2]
  norm_num

theorem wrHom_surjective : Function.Surjective wrHom := by
  let genC : ℕ → PG 3 u33CRels := fun i => if h : i < 3 then PresentedGroup.of ⟨i, h⟩ else 1
  have hgen : ∀ i, wrHom (genC i) = wrGen i := by
    intro i
    unfold genC
    split_ifs with h
    · exact wrHom_of ⟨i, h⟩
    · have : wrGen i = 1 := by unfold wrGen; rw [dite_eq_right h]
      rw [this, map_one]
  have hmem : ∀ i : Fin 32, wordProd wrGen (u33TelW i) ∈ wrHom.range := fun i => by
    refine ⟨wordProd genC (u33TelW i), ?_⟩
    rw [map_wordProd]
    exact congrArg (fun f => wordProd f (u33TelW i)) (funext hgen)
  have hinj : Function.Injective fun i : Fin 32 => (⟨wordProd wrGen (u33TelW i), hmem i⟩ :
      wrHom.range) := fun i j h => wr_inj i j (congrArg Subtype.val h)
  have hcard : 32 ≤ Nat.card wrHom.range := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hle : Nat.card wrHom.range ≤ Nat.card (WreathedTwoGroup 2) :=
    Nat.card_le_card_of_injective (Subtype.val : wrHom.range → WreathedTwoGroup 2)
      Subtype.val_injective
  have htop : wrHom.range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [card_wreathed_two] at hle ⊢; omega)
  exact MonoidHom.range_eq_top.1 htop

theorem u33C_mulEquiv_wreathed :
    Nonempty (PG 3 u33CRels ≃* WreathedTwoGroup 2) := by
  obtain ⟨hfin, hle⟩ := u33C_card_le
  exact ⟨MulEquiv.ofBijective wrHom (wrHom_surjective.bijective_of_nat_card_le (by
    rw [card_wreathed_two]; exact hle))⟩

theorem u33_T_mulEquiv_wreathed :
    Nonempty (u33Data.T ≃* WreathedTwoGroup 2) := by
  obtain ⟨e1⟩ := u33C_mulEquiv_T
  obtain ⟨e2⟩ := u33C_mulEquiv_wreathed
  exact ⟨e1.symm.trans e2⟩

end CFSG.Quasithin
