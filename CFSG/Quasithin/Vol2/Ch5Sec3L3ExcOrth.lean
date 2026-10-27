module

public import Certificates.Certificate7151
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.OPlusFourTwo Matrix

@[expose] def orthQ0 : Subgroup (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ where
  carrier := {u | PreservesQ0 (u : Matrix (Fin 4) (Fin 4) (ZMod 2))}
  one_mem' := fun v => by simp
  mul_mem' := fun {a b} ha hb v => by
    show q0 (((a * b : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) =
      q0 v
    rw [Units.val_mul, ← mulVec_mulVec, ha, hb]
  inv_mem' := fun {a} ha v => by
    have h := ha (((a⁻¹ : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v)
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec] at h
    exact h.symm

theorem mem_orthQ0 {u : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ} :
    u ∈ orthQ0 ↔ PreservesQ0 (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) := Iff.rfl

theorem mem_o4List_of_preserves
    {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hM : PreservesQ0 M) : M ∈ o4List :=
  Certificates.certificate7151.1 M hM

theorem pow_twelve_of_mem {M : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hM : M ∈ o4List) : M ^ 12 = 1 :=
  Certificates.certificate7151.2.2.2.1 M hM

@[expose] noncomputable def unitOfMem
    (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hM : M ∈ o4List) : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ where
  val := M
  inv := M ^ 11
  val_inv := by rw [← pow_succ', pow_twelve_of_mem hM]
  inv_val := by rw [← pow_succ, pow_twelve_of_mem hM]

theorem natCard_subtype_mem_of_nodup {α : Type*} [DecidableEq α] {l : List α} (h : l.Nodup) :
    Nat.card {x // x ∈ l} = l.length := by
  rw [← List.toFinset_card_of_nodup h, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => List.mem_toFinset.symm)

theorem length_o4List : o4List.length = 72 := rfl

theorem card_orthQ0 : Nat.card orthQ0 = 72 := by
  classical
  have hsound := Certificates.certificate7151.2.1
  have hnodup := Certificates.certificate7151.2.2.1
  let e : orthQ0 ≃ {M // M ∈ o4List} :=
    { toFun := fun u => ⟨((u : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ) : Matrix (Fin 4) (Fin 4) (ZMod 2)),
        mem_o4List_of_preserves u.2⟩
      invFun := fun M => ⟨unitOfMem M.1 M.2, hsound M.1 M.2⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        rfl
      right_inv := fun M => rfl }
  rw [Nat.card_congr e, natCard_subtype_mem_of_nodup hnodup, length_o4List]

theorem pow_three_of_pow_nine {u : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ}
    (hu : u ∈ orthQ0) (h9 : u ^ 9 = 1) : u ^ 3 = 1 := by
  have hM := mem_o4List_of_preserves hu
  have h := Certificates.certificate7151.2.2.2.2.2 _ hM (by
    rw [← Units.val_pow_eq_pow_val, h9, Units.val_one])
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])

theorem card_three :
    Nat.card {u : orthQ0 // u ^ 3 = 1} = 9 := by
  classical
  have hsound := Certificates.certificate7151.2.1
  have hnodup := Certificates.certificate7151.2.2.1
  have h9 := Certificates.certificate7151.2.2.2.2.1
  let e : {u : orthQ0 // u ^ 3 = 1} ≃ {M // M ∈ o4List.filter (fun M => M ^ 3 = 1)} :=
    { toFun := fun u => ⟨(((u : orthQ0) : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)), by
        rw [List.mem_filter]
        refine ⟨mem_o4List_of_preserves u.1.2, ?_⟩
        rw [decide_eq_true_eq, ← Units.val_pow_eq_pow_val]
        have := congrArg (fun w : orthQ0 => ((w : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ) :
          Matrix (Fin 4) (Fin 4) (ZMod 2))) u.2
        simpa using this⟩
      invFun := fun M => ⟨⟨unitOfMem M.1 (List.mem_filter.mp M.2).1,
          hsound M.1 (List.mem_filter.mp M.2).1⟩, by
        apply Subtype.ext
        apply Units.ext
        have := (List.mem_filter.mp M.2).2
        rw [decide_eq_true_eq] at this
        simpa [unitOfMem] using this⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Subtype.ext
        apply Units.ext
        rfl
      right_inv := fun M => rfl }
  rw [Nat.card_congr e, natCard_subtype_mem_of_nodup (hnodup.filter _), h9]

@[expose] def g3 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0]

theorem preservesQ0_g3 : PreservesQ0 g3 := by decide +kernel

theorem g3_pow_three : g3 ^ 3 = 1 := by decide +kernel

theorem g3_ne_one : g3 ≠ 1 := by decide +kernel

theorem g3_mulVec_mem : ∀ v : Fin 4 → ZMod 2, v 1 = 0 → v 3 = 0 →
    (g3 *ᵥ v) 1 = 0 ∧ (g3 *ᵥ v) 3 = 0 := by decide +kernel

@[expose] def g3Unit : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ where
  val := g3
  inv := g3 ^ 2
  val_inv := by rw [← pow_succ', g3_pow_three]
  inv_val := by rw [← pow_succ, g3_pow_three]

theorem g3Unit_mem : g3Unit ∈ orthQ0 := preservesQ0_g3

theorem g3_mem_of_dvd {H : Subgroup orthQ0}
    (h9 : 9 ∣ Nat.card H) : (⟨g3Unit, g3Unit_mem⟩ : orthQ0) ∈ H := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥H) 3 (n := 2) (by simpa using h9)
  have hP3 : ∀ p : ↥P, ((p : ↥H) : orthQ0) ^ 3 = 1 := by
    intro p
    have h1 : (p : ↥P) ^ 9 = 1 := by
      have := pow_card_eq_one (G := ↥P) (x := p)
      rwa [Nat.card_eq_fintype_card.symm.trans hP] at this
    have h2 : ((p : ↥H) : orthQ0) ^ 9 = 1 := by
      have := congrArg (fun w : ↥P => ((w : ↥H) : orthQ0)) h1
      simpa using this
    have h3 := pow_three_of_pow_nine ((p : ↥H) : orthQ0).2 (by
      have := congrArg Subtype.val h2
      simpa using this)
    exact Subtype.ext (by simpa using h3)
  let f : ↥P → {u : orthQ0 // u ^ 3 = 1} := fun p => ⟨((p : ↥H) : orthQ0), hP3 p⟩
  have hf : Function.Injective f := fun p q h => by
    have := congrArg (fun w : {u : orthQ0 // u ^ 3 = 1} => (w : orthQ0)) h
    exact Subtype.ext (Subtype.ext this)
  have hcard : Nat.card ↥P = Nat.card {u : orthQ0 // u ^ 3 = 1} := by
    rw [card_three, hP]
    norm_num
  have hbij : Function.Bijective f :=
    (Function.Injective.bijective_of_nat_card_le hf hcard.ge)
  obtain ⟨p, hp⟩ := hbij.2 ⟨⟨g3Unit, g3Unit_mem⟩, Subtype.ext (Units.ext (by
    show (g3Unit ^ 3 : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ).val = 1
    rw [Units.val_pow_eq_pow_val]
    exact g3_pow_three))⟩
  have := congrArg (fun w : {u : orthQ0 // u ^ 3 = 1} => (w : orthQ0)) hp
  simp only [f] at this
  rw [← this]
  exact (p : ↥H).2

end CFSG.Quasithin.H13.Sec53L3
