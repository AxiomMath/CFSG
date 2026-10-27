module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod
import CFSG.LocalAnalysis.StandardType.GGTBRowPermFrameAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

private def qTwoLMA_evalHom {m : ℕ} (k : Fin m) :
    ↥(sumZero m 3) →* Multiplicative (ZMod 3) where
  toFun f := (f : Fin m → Multiplicative (ZMod 3)) k
  map_one' := rfl
  map_mul' _ _ := rfl

private def qTwoLMA_invHom {m : ℕ} (b : Fin m) :
    ↥(sumZero m 3) →* Multiplicative (ZMod 3) where
  toFun f := ((f : Fin m → Multiplicative (ZMod 3)) b)⁻¹
  map_one' := by exact inv_one
  map_mul' x y := by
    change (((x : Fin m → Multiplicative (ZMod 3)) b) *
      ((y : Fin m → Multiplicative (ZMod 3)) b))⁻¹ =
      ((x : Fin m → Multiplicative (ZMod 3)) b)⁻¹ *
        ((y : Fin m → Multiplicative (ZMod 3)) b)⁻¹
    exact mul_inv _ _

private def qTwoLMA_diffHom {m : ℕ} (a b : Fin m) :
    ↥(sumZero m 3) →* Multiplicative (ZMod 3) :=
  qTwoLMA_evalHom a * qTwoLMA_invHom b

private theorem qTwoLMA_toAdd_diffHom {m : ℕ} (a b : Fin m) (f : ↥(sumZero m 3)) :
    Multiplicative.toAdd (qTwoLMA_diffHom a b f) = crd f a - crd f b := by
  show Multiplicative.toAdd ((f : Fin m → Multiplicative (ZMod 3)) a *
    ((f : Fin m → Multiplicative (ZMod 3)) b)⁻¹) = crd f a - crd f b
  rw [toAdd_mul, toAdd_inv, sub_eq_add_neg]
  rfl

private theorem qTwoLMA_crd_prod {ι : Type*} {m : ℕ} (s : Finset ι)
    (g : ι → ↥(sumZero m 3)) (k : Fin m) :
    crd (∏ i ∈ s, g i) k = ∑ i ∈ s, crd (g i) k := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, crd_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, crd_mul, ih]

private theorem qTwoLMA_rootV_inv {m : ℕ} (i j : Fin m) :
    (rootV i j : ↥(sumZero m 3))⁻¹ = rootV j i := by
  apply ext_crd
  intro k
  simp only [crd_inv, crd_rootV]
  ring

private theorem qTwoLMA_swap_rootV {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    permAutV (Equiv.swap i j) (rootV i j : ↥(sumZero m 3)) *
      (rootV i j : ↥(sumZero m 3))⁻¹ = (rootV i j : ↥(sumZero m 3)) := by
  rw [permAutV_rootV, Equiv.swap_apply_left, Equiv.swap_apply_right, ← qTwoLMA_rootV_inv i j]
  set x := (rootV i j : ↥(sumZero m 3)) with _hx
  have hx3 : x ^ 3 = 1 := pow_p_eq_one x
  have hx2 : x ^ 2 = x⁻¹ := by
    have h : x * x ^ 2 = 1 := by rw [← pow_succ', hx3]
    exact eq_inv_of_mul_eq_one_right h
  rw [← pow_two, inv_pow, hx2, inv_inv]

private theorem qTwoLMA_prod_rootV_eq {m : ℕ} (f : ↥(sumZero m 3)) (j0 : Fin m) :
    (∏ i ∈ Finset.univ.erase j0, (rootV i j0) ^ (crd f i).val) = f := by
  apply ext_crd
  intro k
  rw [qTwoLMA_crd_prod]
  have hterm : ∀ i ∈ Finset.univ.erase j0,
      crd ((rootV i j0) ^ (crd f i).val) k = (crd f i) * crd (rootV i j0) k := by
    intro i _
    rw [crd_pow, ZMod.natCast_zmod_val]
  rw [Finset.sum_congr rfl hterm]
  by_cases hk : k = j0
  · rw [← hk]
    have hsum0 : ∑ i ∈ Finset.univ.erase k, crd f i = - crd f k := by
      have h : crd f k + ∑ i ∈ Finset.univ.erase k, crd f i = 0 := by
        rw [Finset.add_sum_erase _ _ (Finset.mem_univ k)]
        exact sum_crd f
      exact eq_neg_of_add_eq_zero_right h
    calc ∑ i ∈ Finset.univ.erase k, crd f i * crd (rootV i k) k
        = ∑ i ∈ Finset.univ.erase k, -crd f i :=
          Finset.sum_congr rfl (fun i hi => by
            rw [crd_rootV_right (Finset.mem_erase.mp hi).1]
            exact mul_neg_one _)
      _ = -∑ i ∈ Finset.univ.erase k, crd f i := Finset.sum_neg_distrib (fun i => crd f i)
      _ = -(-crd f k) := by rw [hsum0]
      _ = crd f k := neg_neg _
  · have hk_mem : k ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩
    rw [Finset.sum_eq_single k]
    · rw [crd_rootV_left hk]
      exact mul_one _
    · intro i _ hik
      rw [crd_rootV_other (Ne.symm hik) hk]
      exact mul_zero _
    · intro hknot
      exact absurd hk_mem hknot

theorem qTwoLMA_closure_rootV (m : ℕ) :
    Subgroup.closure {x : ↥(sumZero m 3) | ∃ i j, i ≠ j ∧ x = rootV i j} = ⊤ := by
  rcases m with _ | n
  · rw [eq_top_iff]
    intro f _
    haveI : Subsingleton ↥(sumZero 0 3) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    rw [Subsingleton.elim f 1]
    exact one_mem _
  · rw [eq_top_iff]
    intro f _
    let H : Subgroup ↥(sumZero (n + 1) 3) :=
      Subgroup.closure {x : ↥(sumZero (n + 1) 3) | ∃ i j, i ≠ j ∧ x = rootV i j}
    have hprod : ∀ s : Finset (Fin (n + 1)), (∀ i ∈ s, i ≠ 0) →
        (∏ i ∈ s, (rootV i (0 : Fin (n + 1))) ^ (crd f i).val) ∈ H := by
      intro s
      induction s using Finset.induction with
      | empty => intro _; simpa using one_mem H
      | insert a s ha ih =>
          intro hs
          rw [Finset.prod_insert ha]
          have ha0 : a ≠ 0 := hs a (Finset.mem_insert_self a s)
          have hroot : (rootV a (0 : Fin (n + 1)) : ↥(sumZero (n + 1) 3)) ∈ H :=
            Subgroup.subset_closure ⟨a, 0, ha0, rfl⟩
          exact mul_mem (Subgroup.pow_mem H hroot _)
            (ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)))
    have hmem := hprod (Finset.univ.erase (0 : Fin (n + 1)))
      (fun i hi => (Finset.mem_erase.mp hi).1)
    rw [← qTwoLMA_prod_rootV_eq f (0 : Fin (n + 1))]
    exact hmem

private theorem qTwoLMA_closure_sumZero (m : ℕ) :
    Subgroup.closure {w : ↥(sumZero m 3) | ∃ σ v, w = permAutV σ v * v⁻¹} = ⊤ := by
  apply le_antisymm le_top
  rw [← qTwoLMA_closure_rootV m]
  refine (Subgroup.closure_le _).mpr (fun x hx => ?_)
  obtain ⟨i, j, hij, rfl⟩ := hx
  have h : (rootV i j : ↥(sumZero m 3)) ∈
      {w : ↥(sumZero m 3) | ∃ σ v, w = permAutV σ v * v⁻¹} :=
    ⟨Equiv.swap i j, rootV i j, (qTwoLMA_swap_rootV hij).symm⟩
  exact Subgroup.subset_closure h

private theorem qTwoLMA_fixed_eq_one {m : ℕ} (h3 : ¬ 3 ∣ m) (hm : 1 ≤ m)
    {f : ↥(sumZero m 3)} (hf : ∀ σ : Equiv.Perm (Fin m), permAutV σ f = f) : f = 1 := by
  let j0 : Fin m := ⟨0, by omega⟩
  have hconst : ∀ k : Fin m, crd f k = crd f j0 := by
    intro k
    by_cases hk : k = j0
    · rw [hk]
    · have h1 := crd_apply_eq_of_fix (σ := Equiv.swap j0 k) (hf (Equiv.swap j0 k)) j0
      rw [Equiv.swap_apply_left] at h1
      exact h1
  have hsum : (m : ZMod 3) * crd f j0 = 0 := by
    calc (m : ZMod 3) * crd f j0 = ∑ _ : Fin m, crd f j0 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∑ k, crd f k := by
          apply Finset.sum_congr rfl
          intro k _
          exact (hconst k).symm
      _ = 0 := sum_crd f
  have hm0 : (m : ZMod 3) ≠ 0 := fun h =>
    h3 ((CharP.cast_eq_zero_iff (ZMod 3) 3 m).mp h)
  have hcj : crd f j0 = 0 := (mul_eq_zero.mp hsum).resolve_left hm0
  apply ext_crd
  intro k
  rw [hconst k, hcj, crd_one]

private theorem qTwoLMA_fix_swap_iff {m : ℕ} {a b : Fin m} (hab : a ≠ b)
    (f : ↥(sumZero m 3)) :
    permAutV (Equiv.swap a b) f = f ↔
      (f : Fin m → Multiplicative (ZMod 3)) a = (f : Fin m → Multiplicative (ZMod 3)) b := by
  constructor
  · intro h
    have h1 := crd_apply_eq_of_fix (σ := Equiv.swap a b) h a
    rw [Equiv.swap_apply_left] at h1
    exact Multiplicative.toAdd.injective h1.symm
  · intro h
    apply ext_crd
    intro k
    rw [crd_permAutV, Equiv.swap_inv]
    by_cases hka : k = a
    · subst hka
      rw [Equiv.swap_apply_left]
      exact (congrArg Multiplicative.toAdd h).symm
    · by_cases hkb : k = b
      · subst hkb
        rw [Equiv.swap_apply_right]
        exact congrArg Multiplicative.toAdd h
      · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]

private theorem qTwoLMA_card_fix_swap {m : ℕ} {a b : Fin m} (hab : a ≠ b) :
    Nat.card {f : ↥(sumZero m 3) // permAutV (Equiv.swap a b) f = f} * 3 =
      Nat.card ↥(sumZero m 3) := by
  have hker : Nat.card {f : ↥(sumZero m 3) // permAutV (Equiv.swap a b) f = f} =
      Nat.card (qTwoLMA_diffHom a b).ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun f => by
      rw [MonoidHom.mem_ker, qTwoLMA_fix_swap_iff hab f]
      show (f : Fin m → Multiplicative (ZMod 3)) a =
          (f : Fin m → Multiplicative (ZMod 3)) b ↔
            qTwoLMA_evalHom a f * (qTwoLMA_evalHom b f)⁻¹ = 1
      exact mul_inv_eq_one.symm))
  have hsurj : Function.Surjective (qTwoLMA_diffHom a b) := by
    intro y
    refine ⟨(rootV a b) ^ ((2 * Multiplicative.toAdd y).val), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [qTwoLMA_toAdd_diffHom]
    rw [crd_pow, crd_pow, crd_rootV_left hab, crd_rootV_right hab, ZMod.natCast_zmod_val]
    ring_nf
    have h4 : (4 : ZMod 3) = 1 := by decide
    simp only [h4, mul_one, one_mul]
  have hrange : Nat.card (qTwoLMA_diffHom a b).range = 3 := by
    rw [MonoidHom.range_eq_top.mpr hsurj]
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
    simpa using (Nat.card_zmod 3 : Nat.card (ZMod 3) = 3)
  have hcard := (qTwoLMA_diffHom a b).ker.card_mul_index
  rw [Subgroup.index_ker, hrange] at hcard
  rw [hker]
  exact hcard

theorem qTwoLMSkel_isAugModel_card {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsAugModel m V ρ) :
    Nat.card V = 3 ^ (m - 1) := by
  obtain ⟨e, _⟩ := h.ex
  rw [← Nat.card_congr e.toEquiv]
  exact ggTBRowPerm_card_sumZero' m 3

theorem qTwoLMSkel_isAugModel_fixed {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsAugModel m V ρ) (h3 : ¬ 3 ∣ m) (hm : 5 ≤ m) :
    ∀ v : V, (∀ σ, ρ σ v = v) → v = 1 := by
  obtain ⟨e, he⟩ := h.ex
  intro v hv
  have hw : e.symm v = 1 := by
    apply qTwoLMA_fixed_eq_one h3 (by omega)
    intro σ
    apply e.injective
    calc e (permAutV σ (e.symm v)) = ρ σ (e (e.symm v)) := he σ (e.symm v)
      _ = ρ σ v := by rw [e.apply_symm_apply]
      _ = v := hv σ
      _ = e (e.symm v) := (e.apply_symm_apply v).symm
  rw [← e.apply_symm_apply v, hw, map_one]

theorem qTwoLMSkel_isAugModel_comm {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsAugModel m V ρ) :
    Subgroup.closure {w : V | ∃ σ v, w = ρ σ v * v⁻¹} = ⊤ := by
  obtain ⟨e, he⟩ := h.ex
  have hsum : Subgroup.closure {w : ↥(sumZero m 3) | ∃ σ v, w = permAutV σ v * v⁻¹} = ⊤ :=
    qTwoLMA_closure_sumZero m
  have hmap : Subgroup.map e.toMonoidHom
      (Subgroup.closure {w : ↥(sumZero m 3) | ∃ σ v, w = permAutV σ v * v⁻¹}) =
      Subgroup.closure {w : V | ∃ σ v, w = ρ σ v * v⁻¹} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨σ, v, rfl⟩ := hx
      exact ⟨σ, e v, by
        show e (permAutV σ v * v⁻¹) = ρ σ (e v) * (e v)⁻¹
        rw [map_mul, map_inv, he]⟩
    · rintro ⟨σ, v, rfl⟩
      refine ⟨permAutV σ (e.symm v) * (e.symm v)⁻¹, ⟨σ, e.symm v, rfl⟩, ?_⟩
      show e (permAutV σ (e.symm v) * (e.symm v)⁻¹) = ρ σ v * v⁻¹
      rw [map_mul, map_inv, he, e.apply_symm_apply]
  rw [hsum] at hmap
  rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hmap
  exact hmap.symm

theorem qTwoLMSkel_isAugModel_faithful {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsAugModel m V ρ) (hm : 5 ≤ m) :
    ∀ σ, (∀ v, ρ σ v = v) → σ = 1 := by
  obtain ⟨e, he⟩ := h.ex
  intro σ hσ
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h'
    push Not at h'
    exact hne (Equiv.ext h')
  obtain ⟨c, hca, hcs⟩ : ∃ c : Fin m, c ≠ a ∧ c ≠ σ a := by
    obtain ⟨c, h1, h2, _⟩ := TypeA.exists_fin_avoid_three (d := m) (by omega) a (σ a) a
    exact ⟨c, h1, h2⟩
  have hw : permAutV σ (rootV a c : ↥(sumZero m 3)) ≠ (rootV a c : ↥(sumZero m 3)) := by
    intro hfix
    have h1 := congrArg (fun f => crd f (σ a)) hfix
    have h2 : (σ⁻¹ : Equiv.Perm (Fin m)) (σ a) = a := σ.symm_apply_apply a
    rw [crd_permAutV, h2, crd_rootV_left (Ne.symm hca),
      crd_rootV_other ha (Ne.symm hcs)] at h1
    exact one_ne_zero h1
  have hv := hσ (e (rootV a c))
  rw [← he σ (rootV a c)] at hv
  exact hw (e.injective hv)

theorem qTwoLMSkel_isAugModel_transposition {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsAugModel m V ρ) (a b : Fin m) (hab : a ≠ b) :
    ρ (Equiv.swap a b) ^ 2 = 1 ∧ Nat.card {v : V // ρ (Equiv.swap a b) v = v} * 3 = Nat.card V := by
  obtain ⟨e, he⟩ := h.ex
  refine ⟨?_, ?_⟩
  · rw [← map_pow, pow_two, Equiv.swap_mul_self, map_one]
  · have hcard : Nat.card {v : V // ρ (Equiv.swap a b) v = v} =
        Nat.card {f : ↥(sumZero m 3) // permAutV (Equiv.swap a b) f = f} :=
      (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun f => by
        show (permAutV (Equiv.swap a b) f = f) ↔ (ρ (Equiv.swap a b) (e f) = e f)
        rw [← he (Equiv.swap a b) f]
        exact (e.injective.eq_iff).symm))).symm
    rw [hcard, qTwoLMA_card_fix_swap hab]
    exact Nat.card_congr e.toEquiv

end CFSG.StandardType.QTwo

end
