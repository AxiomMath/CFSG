
module

public import CFSG.Sporadic.Schreier.J4SBinaryBase

public import CFSG.Sporadic.Schreier.J4SCheck
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SNative

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.SectionRank CFSG.SectionRank.Native
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem u_facts : (∀ j, u j ^ 2 = 1) ∧ (∀ i j, Commute (u i) (u j)) ∧
    ∀ a : Fin 11 → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1 :=
  OpsSpecFacts.elem2_of_ok Sp φ φ_injective u (fun j => (Un j).1)
    (fun j => ⟨(rep_u matFacts j).1, (rep_u matFacts j).2.2.1⟩) elemCheck_eq

theorem u_sq (j : Fin 11) : u j ^ 2 = 1 := u_facts.1 j

theorem u_comm
    (i j : Fin 11) : Commute (u i) (u j) := u_facts.2.1 i j

theorem u_ne_one
    (j : Fin 11) : u j ≠ 1 := ne_one_of_ker u u_facts.2.2 j

theorem exists_etaHom :
    ∃ η : Multiplicative (Fin 11 → ZMod 2) →* J,
      (∀ a, η a = (List.ofFn fun i => u i ^ (Multiplicative.toAdd a i).val).prod) ∧
      Function.Injective η ∧ η.range = Subgroup.closure (Set.range u) ∧
      CFSG.IsElementaryAbelian 2 (Subgroup.closure (Set.range u)) ∧
      Nat.card (Subgroup.closure (Set.range u)) = 2 ^ 11 :=
  exists_elemAbelian_two u u_facts.1 u_facts.2.1 u_facts.2.2

@[expose] def etaHom :
    Multiplicative (Fin 11 → ZMod 2) →* J := Classical.choose exists_etaHom

theorem etaHom_apply (a : Multiplicative (Fin 11 → ZMod 2)) :
    etaHom a = (List.ofFn fun i => u i ^ (Multiplicative.toAdd a i).val).prod :=
  (Classical.choose_spec exists_etaHom).1 a

theorem etaHom_injective :
    Function.Injective etaHom := (Classical.choose_spec exists_etaHom).2.1

theorem etaHom_range :
    etaHom.range = N := (Classical.choose_spec exists_etaHom).2.2.1

theorem N_isElementaryAbelian : CFSG.IsElementaryAbelian 2 N :=
  (Classical.choose_spec exists_etaHom).2.2.2.1

theorem card_N :
    Nat.card N = 2 ^ 11 := (Classical.choose_spec exists_etaHom).2.2.2.2

theorem η_eq
    (i : ℕ) : η i = etaHom (Multiplicative.ofAdd (toVecD 11 i)) := by
  rw [etaHom_apply, η]
  refine congrArg List.prod (List.ofFn_inj.2 (funext fun j => ?_))
  simp only [toAdd_ofAdd, toVecD_apply]
  split_ifs
  · rw [ZMod.val_one, pow_one]
  · rw [ZMod.val_zero, pow_zero]

theorem η_xor (i k : ℕ) : η (i ^^^ k) = η i * η k := by
  rw [η_eq, η_eq, η_eq, toVecD_xor, ofAdd_add, map_mul]

theorem η_zero : η 0 = 1 := by
  rw [η_eq, toVecD_zero, ofAdd_zero, map_one]

theorem η_injOn
    {i k : ℕ} (hi : i < 2 ^ 11) (hk : k < 2 ^ 11) (h : η i = η k) : i = k := by
  rw [η_eq, η_eq] at h
  exact toVecD_injective hi hk (Multiplicative.ofAdd.injective (etaHom_injective h))

theorem η_binOf
    (a : Fin 11 → ZMod 2) : η (binOf a) = etaHom (Multiplicative.ofAdd a) := by
  rw [η_eq, toVecD_binOf]

theorem exists_η_eq
    {n : J} (hn : n ∈ N) : ∃ i < 2 ^ 11, η i = n := by
  rw [← etaHom_range] at hn
  obtain ⟨a, rfl⟩ := hn
  exact ⟨binOf (Multiplicative.toAdd a), binOf_lt _, by rw [η_binOf]; rfl⟩

theorem image_η : η '' Set.Iio (2 ^ 11) = N := by
  ext n
  constructor
  · rintro ⟨i, -, rfl⟩
    exact η_mem_N i
  · intro hn
    obtain ⟨i, hi, rfl⟩ := exists_η_eq hn
    exact ⟨i, hi, rfl⟩

theorem x_conj_u
    (j : Fin 11) : x * u j * x⁻¹ = η xColumns[j.val]! := by
  have h := colsCheck_eq
  unfold colsCheck at h
  rw [List.all_eq_true] at h
  have hj := h j (List.mem_finRange j)
  rw [Bool.and_eq_true] at hj
  exact eq_of_rep (rep_mulP (rep_mulP (rep_x matFacts) (rep_u matFacts j))
    (rep_invP (rep_x matFacts))) (rep_etaP matFacts _) hj.1

theorem y_conj_u
    (j : Fin 11) : y * u j * y⁻¹ = η yColumns[j.val]! := by
  have h := colsCheck_eq
  unfold colsCheck at h
  rw [List.all_eq_true] at h
  have hj := h j (List.mem_finRange j)
  rw [Bool.and_eq_true] at hj
  exact eq_of_rep (rep_mulP (rep_mulP (rep_y matFacts) (rep_u matFacts j))
    (rep_invP (rep_y matFacts))) (rep_etaP matFacts _) hj.2

theorem conj_η_of_cols
    {g : J} {C : Array ℕ} (hg : ∀ j : Fin 11, g * u j * g⁻¹ = η C[j.val]!)
    (a : ℕ) : g * η a * g⁻¹ = η (app11 C a) := by
  have h := map_list_prod (MulAut.conj g)
    (List.ofFn fun j : Fin 11 => if a.testBit j then u j else 1)
  rw [MulAut.conj_apply, List.map_ofFn] at h
  have e : (List.ofFn ((MulAut.conj g) ∘ fun j : Fin 11 => if a.testBit j then u j else 1)) =
      List.ofFn fun j : Fin 11 => if a.testBit j then η C[j.val]! else 1 := by
    refine List.ofFn_inj.2 (funext fun j => ?_)
    simp only [Function.comp_apply]
    split_ifs
    · rw [MulAut.conj_apply]
      exact hg j
    · exact map_one _
  rw [show η a = (List.ofFn fun j : Fin 11 => if a.testBit j then u j else 1).prod from rfl, h, e]
  exact prod_bits_eq η η_xor C a

theorem x_conj_η
    (a : ℕ) : x * η a * x⁻¹ = η (app11 xColumns a) := conj_η_of_cols x_conj_u a

theorem y_conj_η
    (a : ℕ) : y * η a * y⁻¹ = η (app11 yColumns a) := conj_η_of_cols y_conj_u a

end CFSG.Sporadic.J4Schreier
