module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.HeisCoord
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open CFSG.HardMathSupport.Solomon.Coordinator.B3B

@[expose] def heisSub {G : Type*} [Group G] (x y : Fin 4 → G) (z : G) : Subgroup G :=
  Subgroup.closure (insert z (insert (y 0) (Set.range x)))

variable {G : Type*} [Group G] {x y : Fin 4 → G} {z : G}

private def m4A : Subgroup G := Subgroup.closure (insert z (Set.range x))

private def m4suppA (v : Fin 4 → ZMod 3) : Fin (4 + 4) → ZMod 3 :=
  fun k => if h : k.val < 4 then v ⟨k.val, h⟩ else 0

private theorem m4suppA_castAdd (v : Fin 4 → ZMod 3) (i : Fin 4) :
    m4suppA v (Fin.castAdd 4 i) = v i := by
  simp only [m4suppA, Fin.val_castAdd]
  rw [dif_pos i.isLt]

private theorem m4suppA_natAdd (v : Fin 4 → ZMod 3) (j : Fin 4) :
    m4suppA v (Fin.natAdd 4 j) = 0 := by
  simp only [m4suppA, Fin.val_natAdd]
  rw [dif_neg (by omega : ¬ 4 + j.val < 4)]

private theorem m4suppA_zero : m4suppA (0 : Fin 4 → ZMod 3) = 0 := by
  funext k
  by_cases h : k.val < 4 <;> simp [m4suppA, h]

private theorem m4suppA_add (v v' : Fin 4 → ZMod 3) :
    m4suppA (v + v') = m4suppA v + m4suppA v' := by
  funext k
  by_cases h : k.val < 4 <;> simp [m4suppA, h, Pi.add_apply]

private noncomputable def m4psiA (h : HeisCfg 3 4 x y z) (hy : ∀ i, y i ^ 3 = 1) :
    Multiplicative (Fin 4 → ZMod 3) × Multiplicative (ZMod 3) →* G where
  toFun p := heisNF x y z (m4suppA (Multiplicative.toAdd p.1)) (Multiplicative.toAdd p.2)
  map_one' := by
    change heisNF x y z (m4suppA 0) 0 = 1
    rw [m4suppA_zero]
    simp [heisNF]
  map_mul' p q := by
    have hβ : heisCocycle (m4suppA (Multiplicative.toAdd p.1))
        (m4suppA (Multiplicative.toAdd q.1)) = 0 := by
      have hsum : (∑ j : Fin 4, m4suppA (Multiplicative.toAdd p.1) (Fin.natAdd 4 j) *
          m4suppA (Multiplicative.toAdd q.1) (Fin.castAdd 4 j)) = 0 :=
        Finset.sum_eq_zero (fun j _ => by rw [m4suppA_natAdd, zero_mul])
      unfold heisCocycle
      rw [hsum, mul_zero]
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, Pi.add_apply]
    rw [heisNF_mul h hy, m4suppA_add, hβ, add_zero]

private theorem m4psiA_mem_A (h : HeisCfg 3 4 x y z) (hy : ∀ i, y i ^ 3 = 1)
    (p : Multiplicative (Fin 4 → ZMod 3) × Multiplicative (ZMod 3)) :
    m4psiA h hy p ∈ m4A (x := x) (z := z) := by
  change heisNF x y z (m4suppA (Multiplicative.toAdd p.1)) (Multiplicative.toAdd p.2) ∈ m4A
  rw [m4A, heisNF]
  have hy1 : (List.ofFn fun j : Fin 4 =>
      y j ^ (m4suppA (Multiplicative.toAdd p.1) (Fin.natAdd 4 j)).val).prod = 1 := by
    refine List.prod_eq_one (fun a ha => ?_)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    rw [m4suppA_natAdd, ZMod.val_zero, pow_zero]
  rw [hy1, mul_one]
  refine mul_mem (Subgroup.list_prod_mem _ (fun a ha => ?_))
    (pow_mem (Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))) _)
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    rw [m4suppA_castAdd]
    exact pow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self i))) _

private theorem m4suppA_single (i : Fin 4) (a : ZMod 3) :
    m4suppA (Pi.single i a) = Pi.single (Fin.castAdd 4 i) a := by
  funext k
  by_cases hk : k.val < 4
  · rw [m4suppA, dif_pos hk]
    by_cases hik : k.val = i.val
    · have h1 : (⟨k.val, hk⟩ : Fin 4) = i := Fin.ext hik
      have h2 : k = (Fin.castAdd 4 i : Fin (4 + 4)) :=
        Fin.ext (by rw [Fin.val_castAdd]; exact congrArg Fin.val h1)
      rw [h1, h2, Pi.single_eq_same, Pi.single_eq_same]
    · have h1 : (⟨k.val, hk⟩ : Fin 4) ≠ i := fun e => hik (congrArg Fin.val e)
      have h2 : k ≠ (Fin.castAdd 4 i : Fin (4 + 4)) := fun e => hik (by rw [e]; rfl)
      rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
  · rw [m4suppA, dif_neg hk]
    have h2 : k ≠ (Fin.castAdd 4 i : Fin (4 + 4)) := fun e => hk (by rw [e]; exact i.isLt)
    rw [Pi.single_eq_of_ne h2]

private theorem m4psiA_injective (h : HeisCfg 3 4 x y z) (hy : ∀ i, y i ^ 3 = 1) :
    Function.Injective (m4psiA h hy) := by
  intro p q hpq
  have hsub : heisNF x y z (m4suppA (Multiplicative.toAdd p.1)) (Multiplicative.toAdd p.2) =
      heisNF x y z (m4suppA (Multiplicative.toAdd q.1)) (Multiplicative.toAdd q.2) := hpq
  obtain ⟨hv, hc⟩ := heisNF_inj h hy hsub
  refine Prod.ext ?_ ?_
  · apply Multiplicative.toAdd.injective
    funext i
    have := congrFun hv (Fin.castAdd 4 i)
    simpa [m4suppA_castAdd] using this
  · exact Multiplicative.toAdd.injective hc

private theorem m4psiA_range (h : HeisCfg 3 4 x y z) (hy : ∀ i, y i ^ 3 = 1) :
    (m4psiA h hy).range = m4A (x := x) (z := z) := by
  apply le_antisymm
  · intro g hg
    rw [MonoidHom.mem_range] at hg
    obtain ⟨p, rfl⟩ := hg
    exact m4psiA_mem_A h hy p
  · rw [m4A, Subgroup.closure_le]
    intro g hg
    rw [Set.mem_insert_iff, Set.mem_range] at hg
    rcases hg with hg | ⟨i, hg⟩
    · rw [hg]
      change ∃ p, m4psiA h hy p = z
      refine ⟨(1, Multiplicative.ofAdd 1), ?_⟩
      change heisNF x y z (m4suppA 0) 1 = z
      rw [m4suppA_zero, heisNF_zero_left, zmod3_val_one, pow_one]
    · rw [← hg]
      change ∃ p, m4psiA h hy p = x i
      refine ⟨(Multiplicative.ofAdd (Pi.single i 1), 1), ?_⟩
      change heisNF x y z (m4suppA (Pi.single i 1)) 0 = x i
      rw [m4suppA_single, heisNF_single_x]

private theorem m4A_card (h : HeisCfg 3 4 x y z) (hy : ∀ i, y i ^ 3 = 1) :
    Nat.card (m4A (x := x) (z := z)) = 3 ^ 5 := by
  have hker : (m4psiA h hy).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).mpr (m4psiA_injective h hy)
  have h1 := Subgroup.card_ker_mul_card_range (m4psiA h hy)
  rw [hker, m4psiA_range h hy, Subgroup.card_bot, one_mul] at h1
  rw [h1, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

private theorem m4y0_mem_normalizer (h : HeisCfg 3 4 x y z) :
    y 0 ∈ Subgroup.normalizer (m4A (x := x) (z := z) : Set G) := by
  have hconj_z : y 0 * z * (y 0)⁻¹ = z := by rw [h.zy 0]; group
  have hconj_x0 : y 0 * x 0 * (y 0)⁻¹ = x 0 * z⁻¹ := by
    have h2 := h.yx 0
    have h3 : MulAut.conj (y 0) (x 0 * z) = x 0 := by
      rw [← h2, MulAut.conj_apply]
      group
    simp only [map_mul, MulAut.conj_apply, hconj_z] at h3
    have h4 : MulAut.conj (y 0) (x 0) = x 0 * z⁻¹ := eq_mul_inv_of_mul_eq h3
    rwa [MulAut.conj_apply] at h4
  have hconj_xi : ∀ i : Fin 4, i ≠ 0 → y 0 * x i * (y 0)⁻¹ = x i := by
    intro i hi
    rw [← h.xy i 0 hi]; group
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, m4A, Subgroup.closure_le]
    intro a ha
    rw [Set.mem_insert_iff, Set.mem_range] at ha
    change MulAut.conj (y 0) a ∈ Subgroup.closure (insert z (Set.range x))
    rcases ha with rfl | ⟨i, rfl⟩
    · rw [MulAut.conj_apply, hconj_z]
      exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
    · rw [MulAut.conj_apply]
      by_cases hi : i = 0
      · subst hi; rw [hconj_x0]
        exact mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self 0)))
          (inv_mem (Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))))
      · rw [hconj_xi i hi]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self i))
  · rw [m4A, Subgroup.closure_le]
    intro a ha
    rw [Set.mem_insert_iff, Set.mem_range] at ha
    rcases ha with hz | ⟨i, hi⟩
    · rw [hz]
      change ∃ b ∈ Subgroup.closure (insert z (Set.range x)), MulAut.conj (y 0) b = z
      exact ⟨z, Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl)),
        by rw [MulAut.conj_apply, hconj_z]⟩
    · rw [← hi]
      change ∃ b ∈ Subgroup.closure (insert z (Set.range x)), MulAut.conj (y 0) b = x i
      by_cases hi : i = 0
      · subst hi
        refine ⟨x 0 * z, mul_mem
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self 0)))
          (Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))), ?_⟩
        rw [map_mul, MulAut.conj_apply, hconj_x0, MulAut.conj_apply, hconj_z]
        group
      · exact ⟨x i, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self i)),
          by rw [MulAut.conj_apply, hconj_xi i hi]⟩

private theorem m4A_le_normalizer (h : HeisCfg 3 4 x y z) :
    Subgroup.zpowers (y 0) ≤ Subgroup.normalizer (m4A (x := x) (z := z) : Set G) :=
  Subgroup.zpowers_le.mpr (m4y0_mem_normalizer h)

private theorem m4_closure_commute {s : Set G}
    (hs : ∀ a ∈ s, ∀ b ∈ s, Commute a b) :
    ∀ a ∈ Subgroup.closure s, ∀ b ∈ Subgroup.closure s, Commute a b := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    intro b hb
    induction hb using Subgroup.closure_induction with
    | mem b hb => exact hs a ha b hb
    | one => exact Commute.one_right a
    | mul b c _ _ ihb ihc => exact ihb.mul_right ihc
    | inv b _ ihb => exact ihb.inv_right
  | one => intro b _; exact Commute.one_left b
  | mul a b _ _ iha ihb => intro c hc; exact (iha c hc).mul_left (ihb c hc)
  | inv a _ iha => intro c hc; exact (iha c hc).inv_left

private theorem m4A_commute (h : HeisCfg 3 4 x y z) :
    ∀ a ∈ m4A (x := x) (z := z), ∀ b ∈ m4A (x := x) (z := z), Commute a b := by
  apply m4_closure_commute
  intro a ha b hb
  rw [Set.mem_insert_iff, Set.mem_range] at ha hb
  rcases ha with hz | ⟨i, hi⟩ <;> rcases hb with hz' | ⟨j, hj⟩
  · rw [hz, hz']
  · rw [hz, ← hj]; exact (h.zx j).symm
  · rw [← hi, hz']; exact h.zx i
  · rw [← hi, ← hj]; exact h.xx i j

private theorem m4y0_not_mem_A (h : HeisCfg 3 4 x y z) :
    y 0 ∉ m4A (x := x) (z := z) := by
  intro hy0A
  have hcomm : Commute (y 0) (x 0) :=
    m4A_commute h (y 0) hy0A (x 0)
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self 0)))
  have hxy := heisCfg_xy_same h 0
  rw [hcomm.eq] at hxy
  have h2 : (x 0 * y 0) * 1 = (x 0 * y 0) * z := by rw [mul_one]; exact hxy
  have h3 : (1 : G) = z := mul_left_cancel h2
  exact h.z1 h3.symm

private theorem m4A_disjoint_zpowers (h : HeisCfg 3 4 x y z) (hy : ∀ i, y i ^ 3 = 1) :
    Disjoint (m4A (x := x) (z := z)) (Subgroup.zpowers (y 0)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hy1 : y 0 ≠ 1 := by
    intro h1
    have h2 := h.yx 0
    rw [h1, inv_one, one_mul, mul_one] at h2
    have h3 : (x 0) * 1 = (x 0) * z := by rw [mul_one]; exact h2
    have h4 : (1 : G) = z := mul_left_cancel h3
    exact h.z1 h4.symm
  have horder : orderOf (y 0) = 3 := orderOf_eq_prime (hy 0) hy1
  have hcard : Nat.card (Subgroup.zpowers (y 0)) = 3 := by rw [Nat.card_zpowers, horder]
  haveI : Finite ↥(Subgroup.zpowers (y 0)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rw [disjoint_iff_inf_le]
  intro g hg
  rw [Subgroup.mem_bot]
  have hdvd : Nat.card ↥((m4A (x := x) (z := z) : Subgroup G) ⊓
      (Subgroup.zpowers (y 0) : Subgroup G)) ∣ 3 := by
    have h := Subgroup.card_dvd_of_le
      (H := (m4A (x := x) (z := z) : Subgroup G) ⊓ (Subgroup.zpowers (y 0) : Subgroup G))
      (K := Subgroup.zpowers (y 0)) inf_le_right
    rwa [hcard] at h
  have hcases : Nat.card ↥((m4A (x := x) (z := z) : Subgroup G) ⊓
      (Subgroup.zpowers (y 0) : Subgroup G)) = 1 ∨
      Nat.card ↥((m4A (x := x) (z := z) : Subgroup G) ⊓
        (Subgroup.zpowers (y 0) : Subgroup G)) = 3 :=
    (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd
  rcases hcases with h1 | h3
  · have hbot : (m4A (x := x) (z := z)) ⊓ Subgroup.zpowers (y 0) = ⊥ :=
      Subgroup.card_eq_one.mp h1
    rw [hbot, Subgroup.mem_bot] at hg
    exact hg
  · exfalso
    have heq : (m4A (x := x) (z := z)) ⊓ Subgroup.zpowers (y 0) = Subgroup.zpowers (y 0) :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hcard])
    have : y 0 ∈ m4A (x := x) (z := z) := by
      have hmem : y 0 ∈ Subgroup.zpowers (y 0) := Subgroup.mem_zpowers (y 0)
      rw [← heq] at hmem
      exact hmem.1
    exact m4y0_not_mem_A h this

private theorem m4y0_ne_one (h : HeisCfg 3 4 x y z) : y 0 ≠ 1 := by
  intro h1
  have h2 := h.yx 0
  rw [h1, inv_one, one_mul, mul_one] at h2
  have h3 : (x 0) * 1 = (x 0) * z := by rw [mul_one]; exact h2
  have h4 : (1 : G) = z := mul_left_cancel h3
  exact h.z1 h4.symm

private theorem m4heisSub_eq_sup (x y : Fin 4 → G) (z : G) :
    heisSub x y z = m4A (x := x) (z := z) ⊔ Subgroup.zpowers (y 0) := by
  rw [heisSub, m4A, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
  tauto

private theorem m4card (h : HeisCfg 3 4 x y z) (hy : ∀ i, y i ^ 3 = 1) :
    Nat.card (heisSub x y z) = 3 ^ 6 := by
  rw [m4heisSub_eq_sup]
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (m4A (x := x) (z := z)) (Subgroup.zpowers (y 0))
    (m4A_le_normalizer h) (m4A_disjoint_zpowers h hy)
  rw [hcard, m4A_card h hy]
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have horder : orderOf (y 0) = 3 := orderOf_eq_prime (hy 0) (m4y0_ne_one h)
  rw [Nat.card_zpowers, horder]
  norm_num

private theorem m4_le_Q (h : HeisCfg 3 4 x y z) :
    heisSub x y z ≤ CFSG.HardMathSupport.Solomon.Coordinator.B3B.heisSub x y := by
  rw [heisSub, Subgroup.closure_le]
  intro g hg
  rw [Set.mem_insert_iff] at hg
  rcases hg with hg | hg
  · rw [hg]; exact z_mem h (by norm_num)
  · rw [Set.mem_insert_iff, Set.mem_range] at hg
    rcases hg with hg | ⟨i, hg⟩
    · rw [hg]; exact y_mem_heisSub 0
    · rw [← hg]; exact x_mem_heisSub i

private theorem m4_pow_three_of_mem_Q (h : HeisCfg 3 4 x y z) (hy : ∀ i, y i ^ 3 = 1) :
    ∀ q ∈ CFSG.HardMathSupport.Solomon.Coordinator.B3B.heisSub x y, q ^ 3 = 1 := by
  intro q hq
  obtain ⟨v, c, rfl⟩ := exists_heisNF h hy (by norm_num : 0 < 4) q hq
  have h1 := heisNF_mul h hy v v c c
  have h2 := heisNF_mul h hy (v + v) v (c + c + heisCocycle v v) c
  have hv : v + v + v = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize v i = a
    revert a
    decide
  have hcocy : heisCocycle (v + v) v = heisCocycle v v + heisCocycle v v := by
    unfold heisCocycle
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  have hc : c + c + heisCocycle v v + c + heisCocycle (v + v) v = 0 := by
    rw [hcocy]
    generalize heisCocycle v v = b
    generalize c = a
    revert a b
    decide
  rw [pow_three, ← mul_assoc, h1, h2, hv, hc, heisNF_zero_left, ZMod.val_zero, pow_zero]

private theorem m4_pow_three (h : HeisCfg 3 4 x y z) (hy : ∀ i, y i ^ 3 = 1) {g : G}
    (hg : g ∈ heisSub x y z) : g ^ 3 = 1 :=
  m4_pow_three_of_mem_Q h hy g (m4_le_Q h hg)

private theorem m4_closure_mono (x y : Fin 4 → G) (z : G) :
    heisSub x y z ≤ Subgroup.closure (Set.range x ∪ Set.range y ∪ {z}) := by
  rw [heisSub]
  apply Subgroup.closure_mono
  rintro g (rfl | rfl | ⟨i, rfl⟩)
  · exact Or.inr rfl
  · exact Or.inl (Or.inr ⟨0, rfl⟩)
  · exact Or.inl (Or.inl ⟨i, rfl⟩)

theorem card_heisSub {G : Type*} [Group G] {x y : Fin 4 → G} {z : G} (h : HeisCfg 3 4 x y z)
    (hy : ∀ i, y i ^ 3 = 1) : Nat.card (heisSub x y z) = 3 ^ 6 :=
  m4card h hy

theorem pow_three_eq_one_of_mem_heisSub {G : Type*} [Group G] {x y : Fin 4 → G} {z : G}
    (h : HeisCfg 3 4 x y z) (hy : ∀ i, y i ^ 3 = 1) {g : G} (hg : g ∈ heisSub x y z) :
    g ^ 3 = 1 :=
  m4_pow_three h hy hg

theorem heisSub_le_closure {G : Type*} [Group G] (x y : Fin 4 → G) (z : G) :
    heisSub x y z ≤ Subgroup.closure (Set.range x ∪ Set.range y ∪ {z}) :=
  m4_closure_mono x y z

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
