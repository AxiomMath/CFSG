module

import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen2
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSNorm

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

namespace SixSOne

@[expose] def sumOn (J : Finset (Fin 6)) : (Fin 6 → ZMod 2) →+ ZMod 2 where
  toFun y := ∑ k ∈ J, y k
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

@[expose] noncomputable def lamJ (J : Finset (Fin 6)) (hJ : Even J.card) : permBar 6 →+ ZMod 2 :=
  QuotientAddGroup.lift _ (sumOn J) (fun z hz => by
    rw [AddMonoidHom.mem_ker]
    rcases (mem_zmultiples_allOnes_iff z).1 hz with rfl | rfl
    · exact map_zero _
    · show ∑ k ∈ J, allOnes 6 k = 0
      simp only [allOnes, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact (ZMod.natCast_eq_zero_iff_even).2 hJ)

theorem lamJ_mk (J : Finset (Fin 6)) (hJ : Even J.card) (y : Fin 6 → ZMod 2) :
    lamJ J hJ (y : permBar 6) = ∑ k ∈ J, y k := rfl

theorem lamJ_single (J : Finset (Fin 6)) (hJ : Even J.card) (a : Fin 6) :
    lamJ J hJ ((Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) : permBar 6) =
      if a ∈ J then 1 else 0 := by
  rw [lamJ_mk, Finset.sum_pi_single']

theorem lamJ_uvec (J : Finset (Fin 6)) (hJ : Even J.card) (a b : Fin 6) :
    lamJ J hJ (uvec a b) = (if a ∈ J then 1 else 0) + (if b ∈ J then 1 else 0) := by
  unfold uvec
  rw [lamJ_mk]
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']

theorem mk_mem_of_sum_eq_zero {J : Finset (Fin 6)} {a₀ : Fin 6}
    (A : AddSubgroup (permBar 6)) (hA : ∀ a ∈ J, uvec a a₀ ∈ A) {z : Fin 6 → ZMod 2}
    (hz : ∀ k, k ∉ J → z k = 0) (hs : ∑ k ∈ J, z k = 0) : (z : permBar 6) ∈ A := by
  classical
  have key : z = ∑ a ∈ J, z a •
      (Pi.single a (1 : ZMod 2) + Pi.single a₀ (1 : ZMod 2) : Fin 6 → ZMod 2) := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hs, zero_mul, add_zero]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · exact hz k hk
  rw [key, QuotientAddGroup.mk_sum]
  refine AddSubgroup.sum_mem _ fun a ha => ?_
  rcases zmod_two_cases' (z a) with h | h
  · rw [h, zero_smul]
    exact A.zero_mem
  · rw [h, one_smul]
    exact hA a ha


theorem even_card_compl {i j : Fin 6} (hij : i ≠ j) : Even ({i, j}ᶜ : Finset (Fin 6)).card := by
  rw [SixS.card_compl_pair hij]
  decide

theorem klein4_props {J : Finset (Fin 6)} (hJ : J.card = 4) {u : Perm (Fin 6)}
    (hu : u ∈ klein4 J) :
    (∀ k, k ∉ J → u k = k) ∧ (∀ k, u (u k) = k) ∧ (∀ k ∈ J, u k ∈ J) ∧
      (u = 1 ∨ ∀ k ∈ J, u k ≠ k) := by
  obtain ⟨hA, hsq⟩ := (mem_klein4_iff hJ).1 hu
  refine ⟨(mem_altOn.1 hA).1, fun k => ?_, fun k hk => ?_, ?_⟩
  · have := congrArg (fun f : Perm (Fin 6) => f k) hsq
    simpa [Perm.mul_apply] using this
  · exact (mem_setStab.1 ((klein4_fourGroup hJ).stab hu) k).2 hk
  · by_cases h1 : u = 1
    · exact Or.inl h1
    · exact Or.inr ((klein4_fourGroup hJ).free hJ hu h1)

theorem vecPerm_sub_cases {J : Finset (Fin 6)} (hJ : J.card = 4) {u : Perm (Fin 6)}
    (hu : u ∈ klein4 J) {y : Fin 6 → ZMod 2} (hy : ∑ k ∈ J, y k = 0) :
    vecPerm u y - y = 0 ∨ vecPerm u y - y = indVec J := by
  classical
  obtain ⟨hF1, hF2, hF3, hF4⟩ := klein4_props hJ hu
  have hinv : ∀ k, u⁻¹ k = u k := fun k => by
    rw [Perm.inv_eq_iff_eq]
    exact (hF2 k).symm
  have hval : ∀ k, (vecPerm u y - y) k = y (u k) + y k := fun k => by
    rw [Pi.sub_apply, vecPerm_apply, hinv, H2.zmod_two_sub_eq_add]
  rcases hF4 with rfl | hfree
  · left
    funext k
    simp [vecPerm_apply]
  · obtain ⟨k₀, hk₀⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
    have hconst : ∀ k ∈ J, ∀ k' ∈ J, y (u k) + y k = y (u k') + y k' := by
      intro k hk k' hk'
      by_cases h1 : k' = k
      · rw [h1]
      by_cases h2 : k' = u k
      · rw [h2, hF2 k, add_comm]
      have d1 : k ≠ u k := (hfree k hk).symm
      have d3 : k ≠ u k' := fun h => h2 (by rw [h, hF2 k'])
      have d4 : u k ≠ k' := fun h => h2 h.symm
      have d5 : u k ≠ u k' := fun h => h1 (u.injective h).symm
      have d6 : k' ≠ u k' := (hfree k' hk').symm
      have hJeq : J = {k, u k, k', u k'} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl | rfl
          · exact hk
          · exact hF3 _ hk
          · exact hk'
          · exact hF3 _ hk'
        · rw [hJ]
          have : ({k, u k, k', u k'} : Finset (Fin 6)).card = 4 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair d6]
            · simp [d4, d5]
            · simp [d1, Ne.symm h1, d3]
          omega
      have hsum : y k + (y (u k) + (y k' + y (u k'))) = 0 := by
        have := hy
        rw [hJeq, Finset.sum_insert (by simp [d1, Ne.symm h1, d3]),
          Finset.sum_insert (by simp [d4, d5]), Finset.sum_pair d6] at this
        exact this
      have hz2 : ∀ a b c d : ZMod 2, a + (b + (c + d)) = 0 → b + a = d + c := by decide
      exact hz2 _ _ _ _ hsum
    set c := y (u k₀) + y k₀ with hc
    have hz : ∀ k, (vecPerm u y - y) k = if k ∈ J then c else 0 := by
      intro k
      rw [hval]
      by_cases hk : k ∈ J
      · rw [if_pos hk]
        exact hconst k hk k₀ hk₀
      · rw [if_neg hk, hF1 k hk]
        exact (show ∀ a : ZMod 2, a + a = 0 by decide) _
    rcases zmod_two_cases' c with h0 | h1
    · left
      funext k
      rw [hz k, h0]
      split_ifs <;> rfl
    · right
      funext k
      rw [hz k, h1]
      rfl


theorem uvec_self (a : Fin 6) : uvec a a = 0 := by
  unfold uvec
  have : (Pi.single a (1 : ZMod 2) + Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) = 0 := by
    funext k
    simp only [Pi.add_apply, Pi.zero_apply]
    exact (show ∀ c : ZMod 2, c + c = 0 by decide) _
  rw [this]
  rfl

@[expose] noncomputable def lam {i j : Fin 6} (hij : i ≠ j) : permBar 6 →+ ZMod 2 :=
  lamJ ({i, j}ᶜ : Finset (Fin 6)) (even_card_compl hij)

theorem lam_mk {i j : Fin 6} (hij : i ≠ j) (y : Fin 6 → ZMod 2) :
    lam hij (y : permBar 6) = ∑ k ∈ ({i, j}ᶜ : Finset (Fin 6)), y k := rfl

theorem barAct_sub_klein4 {i j : Fin 6} (hij : i ≠ j) {u : Perm (Fin 6)}
    (hu : u ∈ klein4 ({i, j}ᶜ : Finset (Fin 6))) {v : permBar 6} (hv : lam hij v = 0) :
    barAct u v - v = 0 ∨ barAct u v - v = barInd ({i, j} : Finset (Fin 6)) := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [lam_mk] at hv
  rw [barAct_mk, ← QuotientAddGroup.mk_sub]
  rcases vecPerm_sub_cases (SixS.card_compl_pair hij) hu hv with h | h
  · left
    rw [h]
    rfl
  · right
    rw [h]
    exact barInd_compl ({i, j} : Finset (Fin 6))

theorem lam_barAct_swap {i j : Fin 6} (hij : i ≠ j) (v : permBar 6) :
    lam hij (barAct (swap i j) v) = lam hij v := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [barAct_mk, lam_mk, lam_mk]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ∉ ({i, j} : Finset (Fin 6)) := Finset.mem_compl.1 hk
  have hki : k ≠ i := fun h => hk' (by simp [h])
  have hkj : k ≠ j := fun h => hk' (by simp [h])
  rw [vecPerm_apply, Equiv.swap_inv, swap_apply_of_ne_of_ne hki hkj]

theorem barAct_sub_sup {i j : Fin 6} (hij : i ≠ j) {σ : Perm (Fin 6)}
    (hσ : σ ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)))
    {v : permBar 6} (hv : lam hij v = 0) :
    barAct σ v - v = 0 ∨ barAct σ v - v = barInd ({i, j} : Finset (Fin 6)) := by
  rcases (SixS.mem_sup_iff hij).1 hσ with h | h
  · exact barAct_sub_klein4 hij h hv
  · have hσu : σ = (σ * swap i j) * swap i j := by
      rw [mul_assoc, Equiv.swap_mul_self, mul_one]
    have h1 := barAct_sub_klein4 hij h
      (show lam hij (barAct (swap i j) v) = 0 by rw [lam_barAct_swap, hv])
    have h2 := H2.barAct_swap_sub (i := i) (j := j) v
    have e : barAct σ v - v = (barAct (σ * swap i j) (barAct (swap i j) v) -
        barAct (swap i j) v) + (barAct (swap i j) v - v) := by
      conv_lhs => rw [hσu, barAct_mul]
      abel
    rw [e]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2]
    · left
      simp
    · right
      simp
    · right
      simp
    · left
      exact permBar_add_self _

theorem barAct_sub_klein4_mem {J : Finset (Fin 6)} (hJ : J.card = 4) {u : Perm (Fin 6)}
    (hu : u ∈ klein4 J) (A : AddSubgroup (permBar 6))
    (hA : ∀ a ∈ J, ∀ b ∈ J, uvec a b ∈ A) (v : permBar 6) : barAct u v - v ∈ A := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [barAct_mk, ← QuotientAddGroup.mk_sub]
  obtain ⟨hF1, hF2, hF3, -⟩ := klein4_props hJ hu
  obtain ⟨a₀, ha₀⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
  refine mk_mem_of_sum_eq_zero A (a₀ := a₀) (fun a ha => hA a ha a₀ ha₀) (fun k hk => ?_) ?_
  · rw [Pi.sub_apply, vecPerm_apply]
    have : u⁻¹ k = k := by
      rw [Perm.inv_eq_iff_eq]
      exact (hF1 k hk).symm
    rw [this]
    exact sub_self _
  · have hsub : {a | u⁻¹ a ≠ a} ⊆ (J : Set (Fin 6)) := by
      intro a ha
      by_contra hcon
      apply ha
      have h1 : u a = a := hF1 a (by simpa using hcon)
      rw [Perm.inv_eq_iff_eq]
      exact h1.symm
    simp only [Pi.sub_apply, vecPerm_apply, Finset.sum_sub_distrib]
    rw [Perm.sum_comp u⁻¹ J y hsub, sub_self]

theorem barAct_sub_mem {i j : Fin 6} (hij : i ≠ j) {σ : Perm (Fin 6)}
    (hσ : σ ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)))
    (A : AddSubgroup (permBar 6))
    (hA : ∀ a ∈ ({i, j}ᶜ : Finset (Fin 6)), ∀ b ∈ ({i, j}ᶜ : Finset (Fin 6)), uvec a b ∈ A)
    (v : permBar 6) : barAct σ v - v ∈ A := by
  have hJ := SixS.card_compl_pair hij
  rcases (SixS.mem_sup_iff hij).1 hσ with h | h
  · exact barAct_sub_klein4_mem hJ h A hA v
  · have hσu : σ = (σ * swap i j) * swap i j := by
      rw [mul_assoc, Equiv.swap_mul_self, mul_one]
    have h1 := barAct_sub_klein4_mem hJ h A hA (barAct (swap i j) v)
    have h2 := H2.barAct_swap_sub (i := i) (j := j) v
    have e : barAct σ v - v = (barAct (σ * swap i j) (barAct (swap i j) v) -
        barAct (swap i j) v) + (barAct (swap i j) v - v) := by
      conv_lhs => rw [hσu, barAct_mul]
      abel
    rw [e]
    refine A.add_mem h1 ?_
    rcases h2 with h2 | h2
    · rw [h2]
      exact A.zero_mem
    · rw [h2, ← barInd_compl ({i, j} : Finset (Fin 6))]
      obtain ⟨a₀, ha₀⟩ : ({i, j}ᶜ : Finset (Fin 6)).Nonempty := Finset.card_pos.1 (by omega)
      refine mk_mem_of_sum_eq_zero A (a₀ := a₀) (fun a ha => hA a ha a₀ ha₀) (fun k hk => ?_) ?_
      · exact if_neg hk
      · calc ∑ k ∈ ({i, j}ᶜ : Finset (Fin 6)), indVec ({i, j}ᶜ : Finset (Fin 6)) k
            = ∑ k ∈ ({i, j}ᶜ : Finset (Fin 6)), (1 : ZMod 2) :=
              Finset.sum_congr rfl fun k hk => if_pos hk
          _ = 0 := by
            rw [Finset.sum_const, hJ]
            decide


theorem mem_setStab_pair_of_fix {i j : Fin 6} {σ : Perm (Fin 6)} (hi : σ i = i) (hj : σ j = j) :
    σ ∈ setStab ({i, j} : Finset (Fin 6)) := by
  rw [mem_setStab]
  intro x
  constructor
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h
    · left
      exact σ.injective (h.trans hi.symm)
    · right
      exact σ.injective (h.trans hj.symm)
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with rfl | rfl
    · left
      exact hi
    · right
      exact hj

theorem exists_perm_pair {a b a' b' : Fin 6} (hab : a ≠ b) (hab' : a' ≠ b') {S : Finset (Fin 6)}
    (ha : a ∈ S) (hb : b ∈ S) (ha' : a' ∈ S) (hb' : b' ∈ S) :
    ∃ σ : Perm (Fin 6), (∀ k, k ∉ S → σ k = k) ∧ σ a = a' ∧ σ b = b' := by
  set σ₁ : Perm (Fin 6) := swap a a' with hσ₁
  set b₁ : Fin 6 := σ₁ b with hb₁
  have hb₁S : b₁ ∈ S := by
    rw [hb₁, hσ₁, swap_apply_def]
    split_ifs <;> assumption
  have ha'b₁ : a' ≠ b₁ := fun h => hab (σ₁.injective (by rw [hσ₁, swap_apply_left]; exact h))
  refine ⟨swap b₁ b' * σ₁, fun k hk => ?_, ?_, ?_⟩
  · have hka : k ≠ a := fun h => hk (h ▸ ha)
    have hka' : k ≠ a' := fun h => hk (h ▸ ha')
    have hkb₁ : k ≠ b₁ := fun h => hk (h ▸ hb₁S)
    have hkb' : k ≠ b' := fun h => hk (h ▸ hb')
    rw [Perm.mul_apply, hσ₁, swap_apply_of_ne_of_ne hka hka', swap_apply_of_ne_of_ne hkb₁ hkb']
  · rw [Perm.mul_apply, hσ₁, swap_apply_left, swap_apply_of_ne_of_ne ha'b₁ hab']
  · rw [Perm.mul_apply, ← hb₁, swap_apply_left]

theorem eq_one_of_barAct_fix {i j : Fin 6} (hij : i ≠ j) {σ : Perm (Fin 6)}
    (hσ : σ ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)))
    (hfix : ∀ v : permBar 6, lam hij v = 0 → barAct σ v = v) : σ = 1 := by
  have hJ := SixS.card_compl_pair hij
  have hsingle : ∀ a : Fin 6, a ∉ ({i, j}ᶜ : Finset (Fin 6)) → σ a = a := by
    intro a ha
    have hl : lam hij (barInd ({a} : Finset (Fin 6))) = 0 := by
      have : barInd ({a} : Finset (Fin 6)) =
          ((Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) : permBar 6) := by
        unfold barInd
        congr 1
        funext k
        simp [indVec, Pi.single_apply]
      rw [this]
      exact (lamJ_single _ _ a).trans (if_neg ha)
    have h1 := (barAct_barInd_eq_self_iff (I := ({a} : Finset (Fin 6))) (by simp) σ).1
      (hfix _ hl)
    exact Finset.mem_singleton.1 ((mem_setStab.1 h1 a).2 (Finset.mem_singleton_self a))
  have hσi : σ i = i := hsingle i (by simp)
  have hσj : σ j = j := hsingle j (by simp)
  have hσV : σ ∈ klein4 ({i, j}ᶜ : Finset (Fin 6)) := by
    rcases (SixS.mem_sup_iff hij).1 hσ with h | h
    · exact h
    · exfalso
      have hi := (SixS.klein4_fix hij h).1
      rw [Perm.mul_apply, swap_apply_left, hσj] at hi
      exact hij hi.symm
  by_contra hne
  obtain ⟨-, -, -, hfree⟩ := klein4_props hJ hσV
  have hfree' := hfree.resolve_left hne
  obtain ⟨a, ha⟩ : ({i, j}ᶜ : Finset (Fin 6)).Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨b, hbJ, hbs⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, σ a} : Finset (Fin 6))) (t := ({i, j}ᶜ : Finset (Fin 6)))
    (by have := Finset.card_le_two (a := a) (b := σ a); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbs
  obtain ⟨hba, hbσ⟩ := hbs
  have hl : lam hij (uvec a b) = 0 := by
    rw [lam, lamJ_uvec, if_pos ha, if_pos hbJ]
    decide
  have h1 := hfix _ hl
  rw [barAct_uvec] at h1
  have hab : a ≠ b := fun h => hba h.symm
  have hσab : σ a ≠ σ b := fun h => hab (σ.injective h)
  rw [H4b.uvec_eq_barInd hσab, H4b.uvec_eq_barInd hab] at h1
  have h2 : ({σ a, σ b} : Finset (Fin 6)) = {a, b} :=
    eq_of_barInd_eq (I := {σ a, σ b}) (J := {a, b}) (by rw [Finset.card_pair hσab]; norm_num)
      (by rw [Finset.card_pair hσab, Finset.card_pair hab]) h1
  have h3 : σ a ∈ ({a, b} : Finset (Fin 6)) := h2 ▸ Finset.mem_insert_self _ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at h3
  rcases h3 with h3 | h3
  · exact hfree' a ha h3
  · exact hbσ h3.symm


theorem commute_of_mem_sup {i j : Fin 6} (hij : i ≠ j) {σ₁ σ₂ : Perm (Fin 6)}
    (h₁ : σ₁ ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)))
    (h₂ : σ₂ ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6))) :
    σ₁ * σ₂ = σ₂ * σ₁ := by
  have hJ := SixS.card_compl_pair hij
  have hV : ∀ u₁ ∈ klein4 ({i, j}ᶜ : Finset (Fin 6)), ∀ u₂ ∈ klein4 ({i, j}ᶜ : Finset (Fin 6)),
      Commute u₁ u₂ := by
    intro u₁ hu₁ u₂ hu₂
    have hs1 := ((mem_klein4_iff hJ).1 hu₁).2
    have hs2 := ((mem_klein4_iff hJ).1 hu₂).2
    have hs12 := ((mem_klein4_iff hJ).1 (Subgroup.mul_mem _ hu₁ hu₂)).2
    have e1 : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right hs1
    have e2 : u₂⁻¹ = u₂ := inv_eq_of_mul_eq_one_right hs2
    have e12 : (u₁ * u₂)⁻¹ = u₁ * u₂ := inv_eq_of_mul_eq_one_right hs12
    show u₁ * u₂ = u₂ * u₁
    calc u₁ * u₂ = (u₁ * u₂)⁻¹ := e12.symm
      _ = u₂⁻¹ * u₁⁻¹ := mul_inv_rev _ _
      _ = u₂ * u₁ := by rw [e1, e2]
  have hT : ∀ u ∈ klein4 ({i, j}ᶜ : Finset (Fin 6)), Commute u (swap i j) := fun u hu =>
    SixS.commute_swap_of_fix (SixS.klein4_fix hij hu).1 (SixS.klein4_fix hij hu).2
  have hσ : ∀ σ ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)),
      ∃ u ∈ klein4 ({i, j}ᶜ : Finset (Fin 6)), ∃ a : Perm (Fin 6),
        (a = 1 ∨ a = swap i j) ∧ σ = u * a := by
    intro σ hσ
    rcases (SixS.mem_sup_iff hij).1 hσ with h | h
    · exact ⟨σ, h, 1, Or.inl rfl, (mul_one σ).symm⟩
    · exact ⟨σ * swap i j, h, swap i j, Or.inr rfl, by
        rw [mul_assoc, Equiv.swap_mul_self, mul_one]⟩
  obtain ⟨u₁, hu₁, a₁, ha₁, rfl⟩ := hσ σ₁ h₁
  obtain ⟨u₂, hu₂, a₂, ha₂, rfl⟩ := hσ σ₂ h₂
  have hac : ∀ u ∈ klein4 ({i, j}ᶜ : Finset (Fin 6)), ∀ a : Perm (Fin 6),
      (a = 1 ∨ a = swap i j) → Commute u a := fun u hu a ha => by
    rcases ha with rfl | rfl
    · exact Commute.one_right u
    · exact hT u hu
  have haa : Commute a₁ a₂ := by
    rcases ha₁ with rfl | rfl <;> rcases ha₂ with rfl | rfl
    · exact Commute.one_left _
    · exact Commute.one_left _
    · exact Commute.one_right _
    · exact Commute.refl _
  exact ((Commute.mul_left (hV u₁ hu₁ u₂ hu₂) (hac u₂ hu₂ a₁ ha₁).symm).mul_right
    (Commute.mul_left (hac u₁ hu₁ a₂ ha₂) haa)).eq

theorem card_sup {i j : Fin 6} (hij : i ≠ j) :
    Nat.card ↥(Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6))) = 8 := by
  have hJ := SixS.card_compl_pair hij
  set S := Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)) with hS
  have hVS : klein4 ({i, j}ᶜ : Finset (Fin 6)) ≤ S := le_sup_right
  have hτS : swap i j ∈ S := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hτV : swap i j ∉ klein4 ({i, j}ᶜ : Finset (Fin 6)) := fun h => by
    have := (SixS.klein4_fix hij h).1
    rw [swap_apply_left] at this
    exact hij this.symm
  have hidx : ((klein4 ({i, j}ᶜ : Finset (Fin 6))).subgroupOf S).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨swap i j, hτS⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases (SixS.mem_sup_iff hij).1 b.2 with hb | hb
    · refine Or.inr ⟨hb, fun h => hτV ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) h
      simpa using this
    · refine Or.inl ⟨hb, fun h => hτV ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h) hb
      simpa using this
  have h1 := Subgroup.card_mul_index ((klein4 ({i, j}ᶜ : Finset (Fin 6))).subgroupOf S)
  rw [hidx] at h1
  have h2 : Nat.card ↥((klein4 ({i, j}ᶜ : Finset (Fin 6))).subgroupOf S) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv, card_klein4 hJ]
  rw [h2] at h1
  omega


structure Setup {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6}
    (D : C.PiData) (x : G) (i j : Fin 6) : Prop where
  hR : Nat.card ↥(Rc X) ≤ 2
  hsurj : Function.Surjective C.θ
  hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16
  hRb : Rc X = ⊥
  hx : x ∈ CFSG.Open.pCoreOf 2 M
  hij : i ≠ j
  hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}

section Grp

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6}

theorem toAdd_piQ_comm (D : C.PiData) (m : ↥M) (q : ↥(CFSG.Open.pCoreOf 2 M))
    (hc : (m : G) * q * (m : G)⁻¹ * (q : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    Multiplicative.toAdd (D.piQ ⟨(m : G) * q * (m : G)⁻¹ * (q : G)⁻¹, hc⟩) =
      barAct (C.θ m) (Multiplicative.toAdd (D.piQ q)) - Multiplicative.toAdd (D.piQ q) := by
  have hq' : (m : G) * q * (m : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M m.2 q.2
  have h := D.piQ_conj m q ⟨(m : G) * q * (m : G)⁻¹, hq'⟩ rfl
  have e : (⟨(m : G) * q * (m : G)⁻¹ * (q : G)⁻¹, hc⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
      ⟨(m : G) * q * (m : G)⁻¹, hq'⟩ * q⁻¹ := rfl
  rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, h, sub_eq_add_neg]

end Grp

section Grp


variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} {D : C.PiData}
  {x : G} {i j : Fin 6}

namespace Setup

theorem bij (S : Setup D x i j) : Function.Bijective D.piQ :=
  D.piQ_bijective_of_bot S.hRb S.hQ16

theorem card_Q (S : Setup D x i j) : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 32 := by
  rw [Nat.card_congr (Equiv.ofBijective _ S.bij), Nat.card_congr Multiplicative.toAdd,
    Comb.card_permBar (by norm_num)]
  norm_num

theorem x_ne_one (S : Setup D x i j) : x ≠ 1 :=
  D.ne_one_of_len_two S.hx (Finset.card_pair S.hij) S.hπ

theorem x_sq (S : Setup D x i j) : x * x = 1 := by
  have h1 : D.piQ (⟨x, S.hx⟩ * ⟨x, S.hx⟩) = 1 := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, toAdd_mul, toAdd_one, permBar_add_self]
  have h2 : (⟨x, S.hx⟩ * ⟨x, S.hx⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = 1 := S.bij.1 (h1.trans (map_one _).symm)
  exact congrArg Subtype.val h2

theorem orderOf_x (S : Setup D x i j) : orderOf x = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact S.x_sq) S.x_ne_one

theorem lam_x (S : Setup D x i j) : lam S.hij (Multiplicative.toAdd (D.piQ ⟨x, S.hx⟩)) = 0 := by
  rw [S.hπ, ← H4b.uvec_eq_barInd S.hij, lam, lamJ_uvec]
  have h1 : i ∉ ({i, j}ᶜ : Finset (Fin 6)) := by simp
  have h2 : j ∉ ({i, j}ᶜ : Finset (Fin 6)) := by simp
  rw [if_neg h1, if_neg h2]
  simp


@[expose] noncomputable def lamQ (S : Setup D x i j) :
    ↥(CFSG.Open.pCoreOf 2 M) →* Multiplicative (ZMod 2) :=
  (AddMonoidHom.toMultiplicative (lam S.hij)).comp D.piQ

@[expose] noncomputable def Hsub (S : Setup D x i j) : Subgroup G :=
  S.lamQ.ker.map (CFSG.Open.pCoreOf 2 M).subtype

theorem mem_Hsub (S : Setup D x i j) {g : G} :
    g ∈ S.Hsub ↔ ∃ hg : g ∈ CFSG.Open.pCoreOf 2 M,
      lam S.hij (Multiplicative.toAdd (D.piQ ⟨g, hg⟩)) = 0 := by
  unfold Hsub
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.2, ?_⟩
    have h2 : Multiplicative.ofAdd (lam S.hij (Multiplicative.toAdd (D.piQ q))) = 1 :=
      MonoidHom.mem_ker.1 hq
    exact congrArg Multiplicative.toAdd h2
  · rintro ⟨hg, h⟩
    refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    show Multiplicative.ofAdd (lam S.hij (Multiplicative.toAdd (D.piQ ⟨g, hg⟩))) = 1
    rw [h]
    rfl

theorem Hsub_le_Q (S : Setup D x i j) : S.Hsub ≤ CFSG.Open.pCoreOf 2 M := fun _ hg =>
  ((S.mem_Hsub).1 hg).1

theorem x_mem_Hsub (S : Setup D x i j) : x ∈ S.Hsub := (S.mem_Hsub).2 ⟨S.hx, S.lam_x⟩

theorem lamQ_surjective (S : Setup D x i j) : Function.Surjective S.lamQ := by
  intro w
  obtain ⟨a, ha⟩ : ({i, j}ᶜ : Finset (Fin 6)).Nonempty :=
    Finset.card_pos.1 (by rw [SixS.card_compl_pair S.hij]; norm_num)
  obtain ⟨q, hq⟩ := S.bij.2 (Multiplicative.ofAdd
    ((Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) : permBar 6))
  have h1 : S.lamQ q = Multiplicative.ofAdd (1 : ZMod 2) := by
    show Multiplicative.ofAdd (lam S.hij (Multiplicative.toAdd (D.piQ q))) = _
    rw [hq, toAdd_ofAdd, lam, lamJ_single, if_pos ha]
  rcases zmod_two_cases' (Multiplicative.toAdd w) with h0 | h0
  · refine ⟨1, ?_⟩
    rw [map_one]
    apply Multiplicative.toAdd.injective
    rw [h0]
    rfl
  · refine ⟨q, ?_⟩
    rw [h1]
    apply Multiplicative.toAdd.injective
    rw [h0]
    rfl

theorem card_Hsub (S : Setup D x i j) : Nat.card ↥S.Hsub = 16 := by
  have h1 := Subgroup.card_ker_mul_card_range S.lamQ
  have hr : S.lamQ.range = ⊤ := MonoidHom.range_eq_top.2 S.lamQ_surjective
  have h2 : Nat.card ↥S.lamQ.range = 2 := by
    rw [hr, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd]
    exact Nat.card_zmod 2
  rw [h2, S.card_Q] at h1
  have h3 : Nat.card ↥S.Hsub = Nat.card ↥S.lamQ.ker :=
    Subgroup.card_map_of_injective (CFSG.Open.pCoreOf 2 M).subtype_injective
  omega

theorem theta_mem_sup (S : Setup D x i j) {t : G} (ht : t ∈ TOf M x) (htM : t ∈ M) :
    C.θ ⟨t, htM⟩ ∈ Subgroup.zpowers (swap i j) ⊔ klein4 ({i, j}ᶜ : Finset (Fin 6)) := by
  rw [← D.thetaN_eq_sym S.hR S.hsurj S.hx S.hij S.hπ]
  exact C.mem_thetaN.2 ⟨⟨t, htM⟩, ht, rfl⟩

theorem mem_zpowers_of_toAdd (S : Setup D x i j) {c : G} (hc : c ∈ CFSG.Open.pCoreOf 2 M)
    (h : Multiplicative.toAdd (D.piQ ⟨c, hc⟩) = 0 ∨
      Multiplicative.toAdd (D.piQ ⟨c, hc⟩) = barInd ({i, j} : Finset (Fin 6))) :
    c ∈ Subgroup.zpowers x := by
  rcases h with h | h
  · have h3 : (⟨c, hc⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = 1 :=
      S.bij.1 (Multiplicative.toAdd.injective (by rw [h, map_one]; rfl))
    have h4 : c = 1 := congrArg Subtype.val h3
    rw [h4]
    exact Subgroup.one_mem _
  · have h3 : (⟨c, hc⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = ⟨x, S.hx⟩ :=
      S.bij.1 (Multiplicative.toAdd.injective (by rw [h, S.hπ]))
    have h4 : c = x := congrArg Subtype.val h3
    rw [h4]
    exact Subgroup.mem_zpowers x

theorem comm_mem_zpowers (S : Setup D x i j) {q : G} (hq : q ∈ S.Hsub) {t : G}
    (ht : t ∈ TOf M x) : t * q * t⁻¹ * q⁻¹ ∈ Subgroup.zpowers x := by
  obtain ⟨hqQ, hlam⟩ := (S.mem_Hsub).1 hq
  have htM : t ∈ M := TOf_le_M M x ht
  have hc : t * q * t⁻¹ * q⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    (CFSG.Open.pCoreOf 2 M).mul_mem (pCoreOf_normalized M htM hqQ)
      ((CFSG.Open.pCoreOf 2 M).inv_mem hqQ)
  refine S.mem_zpowers_of_toAdd hc ?_
  rw [toAdd_piQ_comm D ⟨t, htM⟩ ⟨q, hqQ⟩ hc]
  exact barAct_sub_sup S.hij (S.theta_mem_sup ht htM) hlam

theorem cons_P (S : Setup D x i j) {k : G} (hk : k ∈ CGOf x)
    (hkc : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * k = k * p) :
    k ∈ CFSG.Open.pCoreOf 2 (CGOf x) :=
  H4b.twoConstrained_P C S.hR S.hx S.x_ne_one
    (Subgroup.mem_inf.2 ⟨hk, Subgroup.mem_centralizer_iff.2 hkc⟩)

theorem stab_mem_P (S : Setup D x i j) {a : G} (haK : a ∈ CGOf x)
    (ha : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), a * p * a⁻¹ * p⁻¹ ∈ Subgroup.zpowers x) :
    a ∈ CFSG.Open.pCoreOf 2 (CGOf x) :=
  H2.stabSub_le_pCoreOf (fun k hk => mem_centralizer_zpowers_iff.1 hk)
    (exists_two_pow_of_mem_pCoreOf M S.hx) (fun k hk hkc => S.cons_P hk hkc) ⟨haK, ha⟩

theorem Hsub_le_P (S : Setup D x i j)
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x) :
    S.Hsub ≤ CFSG.Open.pCoreOf 2 (CGOf x) := by
  intro q hq
  obtain ⟨hqQ, -⟩ := (S.mem_Hsub).1 hq
  refine S.stab_mem_P (H4b.Q_le_CGOf C S.hR S.hx hqQ) fun p hp => ?_
  have hpT : p ∈ TOf M x := h.le (Subgroup.mem_sup_left hp)
  have e : q * p * q⁻¹ * p⁻¹ = (p * q * p⁻¹ * q⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.inv_mem _ (S.comm_mem_zpowers hq hpT)

theorem not_Q_le_P (S : Setup D x i j) (hK : ¬ CGOf x ≤ M)
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x) :
    ¬ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 (CGOf x) := by
  intro hQP
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) = TOf M x := (sup_eq_left.2 hQP).symm.trans h
  apply hK
  intro k hk
  apply D.normalizer_TOf_le S.hR S.hsurj S.hQ16 S.hx S.hij S.hπ
  rw [Subgroup.mem_normalizer_iff]
  intro t
  rw [← hPT]
  refine ⟨fun ht => pCoreOf_normalized _ hk ht, fun ht => ?_⟩
  have := pCoreOf_normalized _ ((CGOf x).inv_mem hk) ht
  simpa [mul_assoc] using this

theorem inf_le_Hsub (S : Setup D x i j) (hK : ¬ CGOf x ≤ M)
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x) :
    CFSG.Open.pCoreOf 2 (CGOf x) ⊓ CFSG.Open.pCoreOf 2 M ≤ S.Hsub := by
  intro q hq
  obtain ⟨hqP, hqQ⟩ := Subgroup.mem_inf.1 hq
  rw [S.mem_Hsub]
  refine ⟨hqQ, ?_⟩
  by_contra hne
  apply S.not_Q_le_P hK h
  intro q' hq'Q
  by_cases hq'0 : lam S.hij (Multiplicative.toAdd (D.piQ ⟨q', hq'Q⟩)) = 0
  · exact S.Hsub_le_P h ((S.mem_Hsub).2 ⟨hq'Q, hq'0⟩)
  · have hqq : q' * q⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      (CFSG.Open.pCoreOf 2 M).mul_mem hq'Q ((CFSG.Open.pCoreOf 2 M).inv_mem hqQ)
    have hlam : lam S.hij (Multiplicative.toAdd (D.piQ ⟨q' * q⁻¹, hqq⟩)) = 0 := by
      have e : (⟨q' * q⁻¹, hqq⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = ⟨q', hq'Q⟩ * ⟨q, hqQ⟩⁻¹ := rfl
      rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, map_add, map_neg]
      have hz : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a + -b = 0 := by decide
      exact hz _ _ hq'0 hne
    have hH : q' * q⁻¹ ∈ S.Hsub := (S.mem_Hsub).2 ⟨hqq, hlam⟩
    have e : q' = (q' * q⁻¹) * q := by group
    rw [e]
    exact (CFSG.Open.pCoreOf 2 (CGOf x)).mul_mem (S.Hsub_le_P h hH) hqP


theorem map_theta_P (S : Setup D x i j)
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x) :
    ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ = C.thetaN x := by
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) ≤ TOf M x := h ▸ le_sup_left
  have hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M := hPT.trans (TOf_le_M M x)
  have hQM : CFSG.Open.pCoreOf 2 M ≤ M := pCoreOf_le_self M
  have e : C.thetaN x = (((CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M).subgroupOf M).map
      C.θ) := by
    show ((TOf M x).subgroupOf M).map C.θ = _
    rw [h]
  rw [e, Subgroup.subgroupOf_sup hPM hQM, Subgroup.map_sup]
  have hQ0 : ((CFSG.Open.pCoreOf 2 M).subgroupOf M).map C.θ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, C.theta_ker_eq S.hR]
  rw [hQ0, sup_bot_eq]

theorem card_P (S : Setup D x i j) (hK : ¬ CGOf x ≤ M)
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 (CGOf x)) = 2 ^ (1 + 2 * 3) := by
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) ≤ TOf M x := h ▸ le_sup_left
  have hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M := hPT.trans (TOf_le_M M x)
  have h1 := C.card_eq_card_inf_mul S.hR hPM
  have hPQ : CFSG.Open.pCoreOf 2 (CGOf x) ⊓ CFSG.Open.pCoreOf 2 M = S.Hsub :=
    le_antisymm (S.inf_le_Hsub hK h) (le_inf (S.Hsub_le_P h) S.Hsub_le_Q)
  rw [hPQ, S.map_theta_P h, D.thetaN_eq_sym S.hR S.hsurj S.hx S.hij S.hπ, S.card_Hsub,
    card_sup S.hij] at h1
  rw [h1]
  norm_num

theorem centerP_le_Q (S : Setup D x i j) (hK : ¬ CGOf x ≤ M)
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x) :
    H4b.centerP x ≤ CFSG.Open.pCoreOf 2 M := by
  intro z hz
  obtain ⟨hzP, hzc⟩ := Subgroup.mem_inf.1 hz
  have hzT : z ∈ TOf M x := h.le (Subgroup.mem_sup_left hzP)
  have hzM : z ∈ M := TOf_le_M M x hzT
  have hσ := S.theta_mem_sup hzT hzM
  have h1 : C.θ ⟨z, hzM⟩ = 1 := by
    refine eq_one_of_barAct_fix S.hij hσ fun v hv => ?_
    obtain ⟨q, hq⟩ := S.bij.2 (Multiplicative.ofAdd v)
    have hqv : Multiplicative.toAdd (D.piQ q) = v := by rw [hq]; rfl
    have hqH : (q : G) ∈ S.Hsub := (S.mem_Hsub).2 ⟨q.2, by
      show lam S.hij (Multiplicative.toAdd (D.piQ q)) = 0
      rw [hqv]
      exact hv⟩
    have hqP := S.Hsub_le_P h hqH
    have hcomm : (q : G) = z * q * z⁻¹ := by
      have h2 := Subgroup.mem_centralizer_iff.1 hzc q hqP
      calc (q : G) = (q * z) * z⁻¹ := by group
        _ = (z * q) * z⁻¹ := by rw [h2]
    have := D.piQ_conj ⟨z, hzM⟩ q q hcomm
    rw [hqv] at this
    exact this.symm
  have hK' : z ∈ C.K := C.mem_K.2 ⟨hzM, h1⟩
  rwa [C.K_eq_Q S.hR] at hK'

end Setup

@[expose] def piSub (D : C.PiData) (Q₂ : Subgroup G) : AddSubgroup (permBar 6) where
  carrier := {v | ∃ q : ↥(CFSG.Open.pCoreOf 2 M),
    (q : G) ∈ Q₂ ∧ Multiplicative.toAdd (D.piQ q) = v}
  zero_mem' := ⟨1, Q₂.one_mem, by rw [map_one]; rfl⟩
  add_mem' := by
    rintro _ _ ⟨q₁, h₁, rfl⟩ ⟨q₂, h₂, rfl⟩
    exact ⟨q₁ * q₂, Q₂.mul_mem h₁ h₂, by rw [map_mul]; rfl⟩
  neg_mem' := by
    rintro _ ⟨q₁, h₁, rfl⟩
    exact ⟨q₁⁻¹, Q₂.inv_mem h₁, by rw [map_inv]; rfl⟩

namespace Setup

theorem le_zpowers_of_invariant (S : Setup D x i j) (hK : ¬ CGOf x ≤ M) {Q₂ : Subgroup G}
    (hQ₂H : Q₂ ≤ S.Hsub) (hQ₂K : ∀ k ∈ CGOf x, ∀ u ∈ Q₂, k * u * k⁻¹ ∈ Q₂) :
    Q₂ ≤ Subgroup.zpowers x := by
  classical
  intro q hq
  have hqH := hQ₂H hq
  obtain ⟨hqQ, hlam⟩ := (S.mem_Hsub).1 hqH
  by_cases hq1 : q = 1
  · rw [hq1]
    exact Subgroup.one_mem _
  have hlen : barLen (Multiplicative.toAdd (D.piQ ⟨q, hqQ⟩)) = 2 := by
    by_contra hl
    apply hK
    intro k hk
    exact D.mem_M_of_conj_len_ne_two S.hR S.hsurj hqQ hq1 hl
      (S.Hsub_le_Q (hQ₂H (hQ₂K k hk q hq)))
  obtain ⟨I, hIc, hI⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨q, hqQ⟩))
  rw [hlen] at hIc
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hIc
  have hπq : Multiplicative.toAdd (D.piQ ⟨q, hqQ⟩) = uvec a b := by
    rw [hI, H4b.uvec_eq_barInd hab]
  rw [hπq, lam, lamJ_uvec] at hlam
  by_cases haJ : a ∈ ({i, j}ᶜ : Finset (Fin 6)) <;>
    by_cases hbJ : b ∈ ({i, j}ᶜ : Finset (Fin 6))
  · exfalso
    have hA : ∀ a' ∈ ({i, j}ᶜ : Finset (Fin 6)), ∀ b' ∈ ({i, j}ᶜ : Finset (Fin 6)),
        uvec a' b' ∈ piSub D Q₂ := by
      intro a' ha' b' hb'
      by_cases hab' : a' = b'
      · subst hab'
        rw [uvec_self]
        exact (piSub D Q₂).zero_mem
      obtain ⟨σ, hσfix, hσa, hσb⟩ := exists_perm_pair hab hab' haJ hbJ ha' hb'
      obtain ⟨m, hm⟩ := S.hsurj σ
      have hσi : σ i = i := hσfix i (by simp)
      have hσj : σ j = j := hσfix j (by simp)
      have hmC : (m : G) ∈ CGOf x := by
        have : (m : G) ∈ CMOf M x := by
          rw [D.CMOf_eq_thetaPre S.hR S.hsurj S.hx S.hij S.hπ, C.mem_thetaPre]
          exact ⟨m.2, by
            rw [show (⟨(m : G), m.2⟩ : ↥M) = m from rfl, hm]
            exact mem_setStab_pair_of_fix hσi hσj⟩
        exact (Subgroup.mem_inf.1 this).2
      have hq' : (m : G) * q * (m : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
        pCoreOf_normalized M m.2 hqQ
      refine ⟨⟨(m : G) * q * (m : G)⁻¹, hq'⟩, hQ₂K _ hmC _ hq, ?_⟩
      rw [D.piQ_conj m ⟨q, hqQ⟩ _ rfl, hm, hπq, barAct_uvec, hσa, hσb]
    have hcomm : ⁅CFSG.Open.pCoreOf 2 M, TOf M x⁆ ≤ Q₂ := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      have hg₂M : g₂ ∈ M := TOf_le_M M x hg₂
      have hc : g₂ * g₁ * g₂⁻¹ * g₁⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
        (CFSG.Open.pCoreOf 2 M).mul_mem (pCoreOf_normalized M hg₂M hg₁)
          ((CFSG.Open.pCoreOf 2 M).inv_mem hg₁)
      have h1 := toAdd_piQ_comm D ⟨g₂, hg₂M⟩ ⟨g₁, hg₁⟩ hc
      have h2 := barAct_sub_mem S.hij (S.theta_mem_sup hg₂ hg₂M) (piSub D Q₂) hA
        (Multiplicative.toAdd (D.piQ ⟨g₁, hg₁⟩))
      rw [← h1] at h2
      obtain ⟨q'', hq''Q₂, hq''⟩ := h2
      have h3 : q'' = ⟨_, hc⟩ := S.bij.1 (Multiplicative.toAdd.injective hq'')
      have hcQ₂ : g₂ * g₁ * g₂⁻¹ * g₁⁻¹ ∈ Q₂ := by
        rw [h3] at hq''Q₂
        exact hq''Q₂
      have e : ⁅g₁, g₂⁆ = (g₂ * g₁ * g₂⁻¹ * g₁⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Q₂.inv_mem hcQ₂
    have hN := D.normalizer_le_of_commutator_le S.hR S.hsurj S.hQ16 S.hx S.hij S.hπ hcomm
      (hQ₂H.trans S.Hsub_le_Q)
    apply hK
    intro k hk
    apply hN
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => hQ₂K k hk u hu, fun hu => ?_⟩
    have := hQ₂K k⁻¹ ((CGOf x).inv_mem hk) _ hu
    simpa [mul_assoc] using this
  · exfalso
    rw [if_pos haJ, if_neg hbJ] at hlam
    exact absurd hlam (by decide)
  · exfalso
    rw [if_neg haJ, if_pos hbJ] at hlam
    exact absurd hlam (by decide)
  · have ha : a ∈ ({i, j} : Finset (Fin 6)) := by
      by_contra h'
      exact haJ (Finset.mem_compl.2 h')
    have hb : b ∈ ({i, j} : Finset (Fin 6)) := by
      by_contra h'
      exact hbJ (Finset.mem_compl.2 h')
    have hset : ({a, b} : Finset (Fin 6)) = {i, j} := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> assumption
      · rw [Finset.card_pair S.hij, Finset.card_pair hab]
    have h3 : (⟨q, hqQ⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = ⟨x, S.hx⟩ :=
      S.bij.1 (Multiplicative.toAdd.injective (by rw [hπq, H4b.uvec_eq_barInd hab, hset, S.hπ]))
    have h4 : q = x := congrArg Subtype.val h3
    rw [h4]
    exact Subgroup.mem_zpowers x


theorem commutator_P_le_Q (S : Setup D x i j)
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x) :
    ⁅CFSG.Open.pCoreOf 2 (CGOf x), CFSG.Open.pCoreOf 2 (CGOf x)⁆ ≤ CFSG.Open.pCoreOf 2 M := by
  rw [Subgroup.commutator_le]
  intro p hp p' hp'
  have hpT : p ∈ TOf M x := h.le (Subgroup.mem_sup_left hp)
  have hp'T : p' ∈ TOf M x := h.le (Subgroup.mem_sup_left hp')
  have hpM : p ∈ M := TOf_le_M M x hpT
  have hp'M : p' ∈ M := TOf_le_M M x hp'T
  have hcM : ⁅p, p'⁆ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hpM hp'M) (M.inv_mem hpM)) (M.inv_mem hp'M)
  have hθ : C.θ ⟨⁅p, p'⁆, hcM⟩ = 1 := by
    have e : (⟨⁅p, p'⁆, hcM⟩ : ↥M) =
        ⟨p, hpM⟩ * ⟨p', hp'M⟩ * ⟨p, hpM⟩⁻¹ * ⟨p', hp'M⟩⁻¹ := rfl
    have hcomm := commute_of_mem_sup S.hij (S.theta_mem_sup hpT hpM) (S.theta_mem_sup hp'T hp'M)
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hK' : ⁅p, p'⁆ ∈ C.K := C.mem_K.2 ⟨hcM, hθ⟩
  rwa [C.K_eq_Q S.hR] at hK'

end Setup

end Grp

section Extraspecial

variable {G : Type} [Group G] [Finite G]

theorem eq_one_or_eq_of_mem_zpowers {x c : G} (hx2 : x * x = 1) (hc : c ∈ Subgroup.zpowers x) :
    c = 1 ∨ c = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hx2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hx2, one_zpow, one_mul, zpow_one]

theorem isExtraspecial_of_zpowers {P : Subgroup G} (hP2 : IsPGroup 2 ↥P) {x : G} (hxP : x ∈ P)
    (hx1 : x ≠ 1) (hx2 : x * x = 1) (hxZ : ∀ p ∈ P, p * x = x * p)
    (hZ : ∀ z ∈ P, (∀ p ∈ P, p * z = z * p) → z ∈ Subgroup.zpowers x)
    (hC : ⁅P, P⁆ = Subgroup.zpowers x) : IsExtraspecialPGroup 2 ↥P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hP2⟩
  have hxP' : (⟨x, hxP⟩ : ↥P) ∈ Subgroup.center ↥P :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hxZ g g.2)
  have hcenter : (Subgroup.center ↥P).map P.subtype = Subgroup.zpowers x := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hZ z z.2 fun p hp => congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨p, hp⟩)
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨x, hxP⟩, hxP', rfl⟩
  have hcomm : (commutator ↥P).map P.subtype = Subgroup.zpowers x := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact hC
  have hCZ : commutator ↥P = Subgroup.center ↥P :=
    Subgroup.map_injective P.subtype_injective (hcomm.trans hcenter.symm)
  have hcardZ : Nat.card ↥(Subgroup.center ↥P) = 2 := by
    rw [← Subgroup.card_map_of_injective P.subtype_injective, hcenter, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hsq : ∀ a : ↥P, a ^ 2 ∈ Subgroup.center ↥P := by
    intro a
    refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
    have hc : (g * a * g⁻¹ * a⁻¹ : ↥P) ∈ commutator ↥P := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top g) (Subgroup.mem_top a)
    have hc' : ((g * a * g⁻¹ * a⁻¹ : ↥P) : G) ∈ Subgroup.zpowers x := by
      rw [← hcomm]
      exact ⟨_, hc, rfl⟩
    have hca : ∀ c ∈ Subgroup.zpowers x, (c : G) * a = a * c := by
      intro c hc
      rcases eq_one_or_eq_of_mem_zpowers hx2 hc with rfl | rfl
      · simp
      · exact (hxZ a a.2).symm
    set c : G := ((g * a * g⁻¹ * a⁻¹ : ↥P) : G) with hcdef
    have hga : (g : G) * a * (g : G)⁻¹ = c * a := by
      rw [hcdef]; simp [mul_assoc]
    have hc2 : c * c = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers hx2 hc' with h | h
      · rw [h, one_mul]
      · rw [h]; exact hx2
    have hga2 : (g : G) * ((a : G) * a) * (g : G)⁻¹ = (a : G) * a := by
      calc (g : G) * ((a : G) * a) * (g : G)⁻¹
          = ((g : G) * a * (g : G)⁻¹) * ((g : G) * a * (g : G)⁻¹) := by group
        _ = (c * a) * (c * a) := by rw [hga]
        _ = c * (a * c) * a := by group
        _ = c * (c * a) * a := by rw [← hca c hc']
        _ = (c * c) * (a * a) := by group
        _ = (a : G) * a := by rw [hc2, one_mul]
    rw [pow_two]
    show (g : G) * ((a : G) * a) = ((a : G) * a) * g
    calc (g : G) * ((a : G) * a) = ((g : G) * ((a : G) * a) * (g : G)⁻¹) * g := by group
      _ = ((a : G) * a) * g := by rw [hga2]
  refine ⟨hP2, hCZ, ?_, hcardZ⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (R := ↥P) (p := 2)]
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro g (hg | ⟨a, rfl⟩)
    · exact hCZ ▸ hg
    · exact hsq a
  · rw [← hCZ]
    exact CFSG.commutator_le_frattini_of_isPGroup (R := ↥P) (p := 2) |>.trans
      (le_of_eq (CFSG.frattini_eq_closure_commutator_union_powers (R := ↥P) (p := 2)))

end Extraspecial

end SixSOne

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)
  (hR : Nat.card ↥(Rc X) ≤ 2) (hsurj : Function.Surjective C.θ)
  (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) (hRb : Rc X = ⊥) {x : G}
  (hx : x ∈ CFSG.Open.pCoreOf 2 M) {i j : Fin 6} (hij : i ≠ j)
  (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j}) (hK : ¬ CGOf x ≤ M)
include hR hsurj hQ16 hRb hij hπ hK

theorem false_of_sup_eq_T2_of_bot
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = C.T2 i j) : False := by
  have S : SixSOne.Setup D x i j := ⟨hR, hsurj, hQ16, hRb, hx, hij, hπ⟩
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) ≤ C.T2 i j := le_sup_left.trans h.le
  have hcomm : ∀ t ∈ C.T2 i j, ∀ q ∈ CFSG.Open.pCoreOf 2 M,
      t * q * t⁻¹ * q⁻¹ ∈ Subgroup.zpowers x := by
    intro t ht q hq
    obtain ⟨htM, hθt⟩ := C.mem_thetaPre.1 ht
    have hc : t * q * t⁻¹ * q⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      (CFSG.Open.pCoreOf 2 M).mul_mem (pCoreOf_normalized M htM hq)
        ((CFSG.Open.pCoreOf 2 M).inv_mem hq)
    refine S.mem_zpowers_of_toAdd hc ?_
    rw [SixSOne.toAdd_piQ_comm D ⟨t, htM⟩ ⟨q, hq⟩ hc]
    rcases SixS.mem_zpowers_swap hθt with h2 | h2
    · left
      show barAct (C.θ ⟨t, htM⟩) _ - _ = 0
      rw [h2, barAct_one, sub_self]
    · exact H2.barAct_swap_sub _ |>.imp_right (fun h3 => by
        show barAct (C.θ ⟨t, htM⟩) _ - _ = _
        rw [h2]
        exact h3) |>.imp_left (fun h3 => by
        show barAct (C.θ ⟨t, htM⟩) _ - _ = _
        rw [h2]
        exact h3)
  have hQP : CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 (CGOf x) := by
    intro q hq
    refine S.stab_mem_P (H4b.Q_le_CGOf C hR hx hq) fun p hp => ?_
    have e : q * p * q⁻¹ * p⁻¹ = (p * q * p⁻¹ * q⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ (hcomm p (hPT hp) q hq)
  have hPeq : CFSG.Open.pCoreOf 2 (CGOf x) = C.T2 i j := (sup_eq_left.2 hQP).symm.trans h
  apply hK
  intro k hk
  apply normalizer_T2_le hR hsurj hQ16 hij
  rw [Subgroup.mem_normalizer_iff]
  intro t
  rw [← hPeq]
  refine ⟨fun ht => pCoreOf_normalized _ hk ht, fun ht => ?_⟩
  have := pCoreOf_normalized _ ((CGOf x).inv_mem hk) ht
  simpa [mul_assoc] using this

theorem extraspecial_of_sup_eq_TOf_of_bot
    (h : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x) :
    IsExtraspecialPGroup 2 ↥(CFSG.Open.pCoreOf 2 (CGOf x)) ∧
      Nat.card ↥(CFSG.Open.pCoreOf 2 (CGOf x)) = 2 ^ (1 + 2 * 3) := by
  have S : SixSOne.Setup D x i j := ⟨hR, hsurj, hQ16, hRb, hx, hij, hπ⟩
  refine ⟨?_, S.card_P hK h⟩
  have hxP : x ∈ CFSG.Open.pCoreOf 2 (CGOf x) := S.Hsub_le_P h S.x_mem_Hsub
  have hxK : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * x = x * p := fun p hp => by
    have h1 := mem_centralizer_zpowers_iff.1 (pCoreOf_le_self _ hp)
    calc p * x = (p * x * p⁻¹) * p := by group
      _ = x * p := by rw [h1]
  have hZle : H4b.centerP x ≤ Subgroup.zpowers x :=
    S.le_zpowers_of_invariant hK
      (fun w hw => S.inf_le_Hsub hK h (Subgroup.mem_inf.2 ⟨hw.1, S.centerP_le_Q hK h hw⟩))
      (fun k hk u hu => center_conj_mem (fun k hk p hp => pCoreOf_normalized _ hk hp) hk hu)
  have hZ : ∀ z ∈ CFSG.Open.pCoreOf 2 (CGOf x),
      (∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * z = z * p) → z ∈ Subgroup.zpowers x :=
    fun z hzP hzc => hZle (Subgroup.mem_inf.2 ⟨hzP, Subgroup.mem_centralizer_iff.2 hzc⟩)
  have hCle : ⁅CFSG.Open.pCoreOf 2 (CGOf x), CFSG.Open.pCoreOf 2 (CGOf x)⁆ ≤
      Subgroup.zpowers x := by
    refine S.le_zpowers_of_invariant hK (fun w hw => ?_) (fun k hk u hu => ?_)
    · exact S.inf_le_Hsub hK h (Subgroup.mem_inf.2 ⟨Subgroup.commutator_le.2 (fun g₁ hg₁ g₂ hg₂ =>
        (CFSG.Open.pCoreOf 2 (CGOf x)).mul_mem ((CFSG.Open.pCoreOf 2 (CGOf x)).mul_mem
          ((CFSG.Open.pCoreOf 2 (CGOf x)).mul_mem hg₁ hg₂)
            ((CFSG.Open.pCoreOf 2 (CGOf x)).inv_mem hg₁))
          ((CFSG.Open.pCoreOf 2 (CGOf x)).inv_mem hg₂)) hw, S.commutator_P_le_Q h hw⟩)
    · have hle : (⁅CFSG.Open.pCoreOf 2 (CGOf x), CFSG.Open.pCoreOf 2 (CGOf x)⁆).map
          (MulAut.conj k).toMonoidHom ≤
          ⁅CFSG.Open.pCoreOf 2 (CGOf x), CFSG.Open.pCoreOf 2 (CGOf x)⁆ := by
        rw [Subgroup.map_commutator]
        refine Subgroup.commutator_mono ?_ ?_ <;> rintro _ ⟨p, hp, rfl⟩ <;>
          exact pCoreOf_normalized _ hk hp
      exact hle ⟨u, hu, rfl⟩
  have hne : ⁅CFSG.Open.pCoreOf 2 (CGOf x), CFSG.Open.pCoreOf 2 (CGOf x)⁆ ≠ ⊥ := by
    intro hbot
    have hPle : CFSG.Open.pCoreOf 2 (CGOf x) ≤ Subgroup.zpowers x := by
      intro p hp
      refine hZ p hp fun p' hp' => ?_
      have h1 : ⁅p', p⁆ ∈ ⁅CFSG.Open.pCoreOf 2 (CGOf x), CFSG.Open.pCoreOf 2 (CGOf x)⁆ :=
        Subgroup.commutator_mem_commutator hp' hp
      rw [hbot, Subgroup.mem_bot, commutatorElement_def] at h1
      have h2 : p' * p * p'⁻¹ = p := mul_inv_eq_one.1 h1
      calc p' * p = (p' * p * p'⁻¹) * p' := by group
        _ = p * p' := by rw [h2]
    have h1 := Subgroup.card_le_of_le hPle
    rw [S.card_P hK h, Nat.card_zpowers, S.orderOf_x] at h1
    norm_num at h1
  have hCeq : ⁅CFSG.Open.pCoreOf 2 (CGOf x), CFSG.Open.pCoreOf 2 (CGOf x)⁆ =
      Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge hCle ?_
    rw [Nat.card_zpowers, S.orderOf_x]
    exact Nat.succ_le_of_lt ((Subgroup.one_lt_card_iff_ne_bot _).2 hne)
  exact SixSOne.isExtraspecial_of_zpowers (isPGroup_pCoreOf' _) hxP S.x_ne_one S.x_sq hxK hZ hCeq

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
