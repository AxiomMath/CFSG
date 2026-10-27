module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMModHmAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMModAug

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord CFSG.StandardType.SpCoord
open Multiplicative
open Subgroup
open scoped BigOperators

theorem qTwoLMH_closure_rootV {m : ℕ} (_hm : 1 ≤ m) :
    Subgroup.closure (Set.range (fun p : Fin m × Fin m => rootV (p := 3) p.1 p.2)) = ⊤ := by
  rw [eq_top_iff, ← qTwoLMA_closure_rootV m]
  refine Subgroup.closure_mono ?_
  rintro x ⟨i, j, _, rfl⟩
  exact ⟨(i, j), rfl⟩

theorem qTwoLMH_swap_rootV {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    permAutV (Equiv.swap i j) (rootV (p := 3) j i) * (rootV (p := 3) j i)⁻¹ =
      (rootV (p := 3) i j)⁻¹ := by
  have h := mul_inv_permAutV_swap (p := 3) hij (rootV (p := 3) j i)
  have hval : (crd (rootV (p := 3) j i) i - crd (rootV (p := 3) j i) j).val = 1 := by
    rw [crd_rootV_right (Ne.symm hij), crd_rootV_left (Ne.symm hij)]
    decide
  rw [hval, pow_one] at h
  rw [← h, mul_inv_rev, inv_inv]

theorem qTwoLMH_card_of_model {m : ℕ} (h3 : 3 ∣ m) {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsHmModel m h3 V ρ) :
    Nat.card V = 3 ^ (m - 2) := by
  obtain ⟨π, hsurj, hker, -⟩ := h.ex
  by_cases hm : m = 0
  · subst hm
    haveI : Subsingleton V := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hsurj a
      obtain ⟨y, rfl⟩ := hsurj b
      rw [Subsingleton.elim x y]⟩
    rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩]
    norm_num
  · have hm' : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    haveI : Fintype ↥(sumZero m 3) := Fintype.ofFinite _
    have hcardV : Nat.card V * 3 = Nat.card ↥(sumZero m 3) := by
      have h := qTwoLMH_card_of_surjective_ker (qTwoOneVec m h3) π hsurj hker
      rwa [qTwoLMH_card_zpowers_oneVec h3 hm'] at h
    have hpow : 3 ^ (m - 1) = 3 ^ (m - 2) * 3 := by
      rw [← pow_succ]
      congr 1
      omega
    have hEq : Nat.card V * 3 = 3 ^ (m - 2) * 3 := by
      rw [hcardV, qTwoLMH_card_sumZero hm', hpow]
    exact Nat.mul_right_cancel (by norm_num : 0 < 3) hEq

theorem qTwoLMH_fixed {m : ℕ} (h3 : 3 ∣ m) {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsHmModel m h3 V ρ) (hm : 5 ≤ m) :
    ∀ v : V, (∀ σ, ρ σ v = v) → v = 1 := by
  obtain ⟨π, hsurj, hker, heq⟩ := h.ex
  have hm1 : 1 ≤ m := by omega
  intro v hv
  obtain ⟨w, rfl⟩ := hsurj v
  rw [hker w, qTwoLMH_mem_zpowers_oneVec h3 hm1 w]
  intro i j
  by_cases hij : i = j
  · rw [hij]
  · have hx : permAutV (Equiv.swap i j) w * w⁻¹ ∈ Subgroup.zpowers (qTwoOneVec m h3) := by
      rw [← hker, map_mul, map_inv, heq, hv (Equiv.swap i j), mul_inv_cancel]
    have hconst := (qTwoLMH_mem_zpowers_oneVec h3 hm1 _).mp hx
    have h1 : crd (permAutV (Equiv.swap i j) w * w⁻¹) i = crd w j - crd w i := by
      rw [crd_mul, crd_inv, crd_permAutV, Equiv.swap_inv, Equiv.swap_apply_left]
      ring
    have h2 : crd (permAutV (Equiv.swap i j) w * w⁻¹) j = crd w i - crd w j := by
      rw [crd_mul, crd_inv, crd_permAutV, Equiv.swap_inv, Equiv.swap_apply_right]
      ring
    have h3 : crd w j - crd w i = -(crd w j - crd w i) := by
      calc crd w j - crd w i
          = crd (permAutV (Equiv.swap i j) w * w⁻¹) i := h1.symm
        _ = crd (permAutV (Equiv.swap i j) w * w⁻¹) j := hconst i j
        _ = crd w i - crd w j := h2
        _ = -(crd w j - crd w i) := by abel
    have h4 : crd w j - crd w i = 0 :=
      coord_eq_zero_of_eq_neg (p := 3) (by norm_num) (by norm_num) h3
    exact (sub_eq_zero.mp h4).symm

theorem qTwoLMH_faithful {m : ℕ} (h3 : 3 ∣ m) {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsHmModel m h3 V ρ) (hm : 5 ≤ m) :
    ∀ σ, (∀ v, ρ σ v = v) → σ = 1 := by
  obtain ⟨π, hsurj, hker, heq⟩ := h.ex
  have hm1 : 1 ≤ m := by omega
  intro σ hσ
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra hcon
    push_neg at hcon
    exact hne (Equiv.ext hcon)
  obtain ⟨c, hca, hcσa, hcσia⟩ := qTwoLMH_exists_ne_three (by omega : 4 ≤ m) a (σ a) (σ⁻¹ a)
  have hσia : σ⁻¹ a ≠ a := by
    intro hcon
    exact ha (by
      calc σ a = σ (σ⁻¹ a) := by rw [hcon]
        _ = a := Equiv.apply_symm_apply σ a)
  have hx : permAutV σ (rootV a c) * (rootV a c)⁻¹ ∈ Subgroup.zpowers (qTwoOneVec m h3) := by
    rw [← hker, map_mul, map_inv, heq, hσ (π (rootV a c)), mul_inv_cancel]
  have hconst := (qTwoLMH_mem_zpowers_oneVec h3 hm1 _).mp hx
  have hσa : (σ⁻¹ : Equiv.Perm (Fin m)) (σ a) = a := σ.symm_apply_apply a
  have h1 : crd (permAutV (p := 3) σ (rootV (p := 3) a c) * (rootV (p := 3) a c)⁻¹)
      (σ a) = 1 := by
    rw [crd_mul, crd_inv, crd_permAutV, hσa]
    rw [crd_rootV_left hca.symm, crd_rootV_other ha hcσa.symm]
    abel
  have h2 : crd (permAutV (p := 3) σ (rootV (p := 3) a c) * (rootV (p := 3) a c)⁻¹) a = -1 := by
    rw [crd_mul, crd_inv, crd_permAutV]
    rw [crd_rootV_other hσia hcσia.symm, crd_rootV_left hca.symm]
    abel
  have h3 := hconst (σ a) a
  rw [h1, h2] at h3
  exact (by decide : ¬ (1 : ZMod 3) = -1) h3

theorem qTwoLMH_comm {m : ℕ} (h3 : 3 ∣ m) {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsHmModel m h3 V ρ) :
    Subgroup.closure {w : V | ∃ σ v, w = ρ σ v * v⁻¹} = ⊤ := by
  obtain ⟨π, hsurj, hker, heq⟩ := h.ex
  by_cases hm : m = 0
  · subst hm
    haveI : Subsingleton V := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hsurj a
      obtain ⟨y, rfl⟩ := hsurj b
      rw [Subsingleton.elim x y]⟩
    rw [Subgroup.eq_top_iff']
    intro v
    rw [Subsingleton.elim v 1]
    exact Subgroup.one_mem _
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hroot' : ∀ i j, π (rootV i j) ∈
        Subgroup.closure {w : V | ∃ σ v, w = ρ σ v * v⁻¹} := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rw [show rootV i i = 1 from ?_, map_one]
        · exact Subgroup.one_mem _
        · apply ext_crd; intro k; rw [crd_rootV, crd_one]; simp
      · have hmem : ρ (Equiv.swap i j) (π (rootV j i)) * (π (rootV j i))⁻¹ ∈
            Subgroup.closure {w : V | ∃ σ v, w = ρ σ v * v⁻¹} :=
          Subgroup.subset_closure ⟨Equiv.swap i j, π (rootV j i), rfl⟩
        have heq' : ρ (Equiv.swap i j) (π (rootV j i)) * (π (rootV j i))⁻¹ =
            (π (rootV i j))⁻¹ := by
          rw [← heq, ← map_inv, ← map_mul, qTwoLMH_swap_rootV hij, map_inv]
        rw [heq'] at hmem
        exact inv_inv (π (rootV i j)) ▸ Subgroup.inv_mem _ hmem
    have hle : (⊤ : Subgroup ↥(sumZero m 3)).map π ≤
        Subgroup.closure {w : V | ∃ σ v, w = ρ σ v * v⁻¹} := by
      rw [Subgroup.map_le_iff_le_comap, ← qTwoLMH_closure_rootV hm1]
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨p, rfl⟩
      exact hroot' p.1 p.2
    have htop : (⊤ : Subgroup ↥(sumZero m 3)).map π = ⊤ :=
      Subgroup.map_top_of_surjective π hsurj
    rw [htop] at hle
    exact top_le_iff.mp hle

theorem qTwoLMH_fix_swap_card {m : ℕ} (h3 : 3 ∣ m) {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsHmModel m h3 V ρ)
    (a b : Fin m) (hab : a ≠ b) :
    Nat.card {v : V // ρ (Equiv.swap a b) v = v} * 3 = Nat.card V := by
  obtain ⟨π, hsurj, hker, heq⟩ := h.ex
  haveI : Fintype ↥(sumZero m 3) := Fintype.ofFinite _
  have hm1 : 1 ≤ m := by have := a.2; omega
  let ψ : ↥(sumZero m 3) →* Multiplicative (ZMod 3) :=
    { toFun := fun w => ofAdd (crd w a - crd w b)
      map_one' := by simp [crd_one]
      map_mul' := by
        intro f g
        simp only [crd_mul]
        rw [← ofAdd_add]
        congr 1
        ring }
  have hψsurj : Function.Surjective ψ := by
    have hgen : Subgroup.zpowers (ofAdd (1 : ZMod 3)) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro y
      obtain ⟨c, rfl⟩ : ∃ c, ofAdd c = y := ⟨toAdd y, rfl⟩
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨(c.val : ℤ), by rw [zpow_natCast, qTwoLMH_ofAdd_one_pow, ZMod.natCast_zmod_val]⟩
    have hmem : ofAdd (1 : ZMod 3) ∈ ψ.range := by
      refine ⟨rootV (p := 3) b a, ?_⟩
      show ofAdd (crd (rootV (p := 3) b a) a - crd (rootV (p := 3) b a) b) = ofAdd 1
      have h2 : crd (rootV (p := 3) b a) a - crd (rootV (p := 3) b a) b = 1 := by
        rw [crd_rootV_right (Ne.symm hab), crd_rootV_left (Ne.symm hab)]
        decide
      rw [h2]
    have hle : (⊤ : Subgroup (Multiplicative (ZMod 3))) ≤ ψ.range := by
      rw [← hgen]
      exact Subgroup.zpowers_le.mpr hmem
    exact MonoidHom.range_eq_top.mp (le_antisymm le_top hle)
  have hBidx : Nat.card ψ.ker * 3 = Nat.card ↥(sumZero m 3) :=
    qTwoLMH_card_ker_of_surjective_zmod3 ψ hψsurj
  have hBk : Subgroup.zpowers (qTwoOneVec m h3) ≤ ψ.ker := by
    intro w hw
    rw [MonoidHom.mem_ker]
    have hconst := (qTwoLMH_mem_zpowers_oneVec h3 hm1 w).mp hw
    show ofAdd (crd w a - crd w b) = 1
    rw [hconst a b, sub_self]
    rfl
  have hBfix : ∀ w, w ∈ ψ.ker ↔ ρ (Equiv.swap a b) (π w) = π w := by
    intro w
    rw [MonoidHom.mem_ker]
    constructor
    · intro hw
      have hw' : crd w a - crd w b = 0 := by
        have h : toAdd (ψ w) = 0 := by rw [congrArg toAdd hw, toAdd_one]
        rwa [show ψ w = ofAdd (crd w a - crd w b) from rfl, toAdd_ofAdd] at h
      have hab' : crd w a = crd w b := sub_eq_zero.mp hw'
      have hx : permAutV (Equiv.swap a b) w = w := by
        apply ext_crd
        intro k
        rw [crd_permAutV, Equiv.swap_inv]
        by_cases hka : k = a
        · rw [hka, Equiv.swap_apply_left, hab']
        · by_cases hkb : k = b
          · rw [hkb, Equiv.swap_apply_right, hab']
          · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]
      rw [← heq, hx]
    · intro hfix
      have hx : permAutV (Equiv.swap a b) w * w⁻¹ ∈ Subgroup.zpowers (qTwoOneVec m h3) := by
        rw [← hker, map_mul, map_inv, heq, hfix, mul_inv_cancel]
      have hconst := (qTwoLMH_mem_zpowers_oneVec h3 hm1 _).mp hx
      have h1 : crd (permAutV (Equiv.swap a b) w * w⁻¹) a = crd w b - crd w a := by
        rw [crd_mul, crd_inv, crd_permAutV, Equiv.swap_inv, Equiv.swap_apply_left]
        ring
      have h2 : crd (permAutV (Equiv.swap a b) w * w⁻¹) b = crd w a - crd w b := by
        rw [crd_mul, crd_inv, crd_permAutV, Equiv.swap_inv, Equiv.swap_apply_right]
        ring
      have h3 : crd w b - crd w a = -(crd w b - crd w a) := by
        calc crd w b - crd w a
            = crd (permAutV (Equiv.swap a b) w * w⁻¹) a := h1.symm
          _ = crd (permAutV (Equiv.swap a b) w * w⁻¹) b := hconst a b
          _ = crd w a - crd w b := h2
          _ = -(crd w b - crd w a) := by abel
      have h4 : crd w b - crd w a = 0 :=
        coord_eq_zero_of_eq_neg (p := 3) (by norm_num) (by norm_num) h3
      have hab' : crd w a = crd w b := (sub_eq_zero.mp h4).symm
      show ofAdd (crd w a - crd w b) = 1
      rw [hab', sub_self]
      rfl
  exact qTwoLMH_card_fix_of_index_three π hsurj hker (Equiv.swap a b) ρ ψ.ker hBk hBidx hBfix


end CFSG.StandardType.QTwo

end
