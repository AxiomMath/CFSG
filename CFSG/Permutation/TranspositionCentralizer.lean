module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Permutation.TranspositionCentralizer

open Equiv
open scoped Pointwise

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem alternatingGroup_sup_zpowers_swap {i j : α} (hij : i ≠ j) :
    alternatingGroup α ⊔ Subgroup.zpowers (Equiv.swap i j) = ⊤ := by
  refine eq_top_iff.mpr ?_
  intro σ _
  by_cases hs : Equiv.Perm.sign σ = 1
  · exact Subgroup.mem_sup_left (Equiv.Perm.mem_alternatingGroup.mpr hs)
  · have hs' : Equiv.Perm.sign σ = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · exact absurd h hs
      · exact h
    have hmem : σ * Equiv.swap i j ∈ alternatingGroup α := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, hs', Equiv.Perm.sign_swap hij]
      norm_num
    have heq : σ = (σ * Equiv.swap i j) * Equiv.swap i j := by
      rw [mul_assoc, Equiv.swap_mul_self, mul_one]
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem centralizer_swap_ne_top {i j : α} (hij : i ≠ j) (h3 : 3 ≤ Fintype.card α) :
    Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm α)) ≠ ⊤ := by
  intro htop
  have hlt : ({i, j} : Finset α).card < (Finset.univ : Finset α).card := by
    rw [Finset.card_univ, Finset.card_insert_of_notMem (by simp [hij])]
    simp [hij]
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hki : k ≠ i := fun h => hk (by simp [h])
  have hkj : k ≠ j := fun h => hk (by simp [h])
  have hmem : Equiv.swap i k ∈ Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm α)) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hcomm : Equiv.swap i k * Equiv.swap i j = Equiv.swap i j * Equiv.swap i k :=
    Subgroup.mem_centralizer_singleton_iff.mp hmem
  have happ := congrArg (fun e : Equiv.Perm α => e i) hcomm
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at happ
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hij.symm hkj.symm,
    Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hki hkj] at happ
  exact hkj happ.symm

theorem le_zpowers_swap_of_isPGroup {i j : α} (hij : i ≠ j) (h7 : 7 ≤ Fintype.card α)
    {N : Subgroup (Equiv.Perm α)} (hN2 : IsPGroup 2 N)
    (hNC : N ≤ Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm α)))
    (hCN : Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm α)) ≤
      Subgroup.normalizer (N : Set (Equiv.Perm α))) :
    N ≤ Subgroup.zpowers (Equiv.swap i j) := by
  classical
  let g : Equiv.Perm α := Equiv.swap i j
  let C : Subgroup (Equiv.Perm α) := Subgroup.centralizer ({g} : Set (Equiv.Perm α))
  let s : Set α := ({i, j} : Set α)ᶜ
  have hfix_of_mem_s : ∀ x : α, x ∈ s → g x = x := by
    intro x hx
    have hx' : x ≠ i ∧ x ≠ j := by simpa [s] using hx
    change Equiv.swap i j x = x
    exact Equiv.swap_apply_of_ne_of_ne hx'.1 hx'.2
  have hcompl_of_not_mem_s : ∀ x : α, x ∉ s → x = i ∨ x = j := by
    intro x hx
    have hx' : x ≠ i → x = j := by simpa [s] using hx
    by_cases h : x = i
    · exact Or.inl h
    · exact Or.inr (hx' h)
  have hCs : C ≤ MulAction.stabilizer (Equiv.Perm α) s := by
    rw [MulAction.le_stabilizer_iff_smul_le]
    intro c hc x hx
    rw [Set.mem_smul_set] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hcomm : c * g = g * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcy : g (c y) = c y := by
      rw [← Equiv.Perm.mul_apply, ← hcomm, Equiv.Perm.mul_apply, hfix_of_mem_s y hy]
    show c y ∈ s
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      rw [h] at hcy
      change Equiv.swap i j i = i at hcy
      rw [Equiv.swap_apply_left] at hcy
      exact hij hcy.symm
    · intro h
      rw [h] at hcy
      change Equiv.swap i j j = j at hcy
      rw [Equiv.swap_apply_right] at hcy
      exact hij hcy
  let ρC : C →* Equiv.Perm s :=
    (MulAction.toPermHom (MulAction.stabilizer (Equiv.Perm α) s) s).comp (Subgroup.inclusion hCs)
  have hρC_surj : Function.Surjective ρC := by
    intro u
    refine ⟨⟨Equiv.Perm.ofSubtype u, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      ext x
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      change (Equiv.Perm.ofSubtype u) (g x) = g ((Equiv.Perm.ofSubtype u) x)
      by_cases hx : x ∈ s
      · have hgx : g x = x := hfix_of_mem_s x hx
        rw [hgx]
        have hux : (Equiv.Perm.ofSubtype u) x ∈ s := by
          rw [Equiv.Perm.ofSubtype_apply_of_mem u hx]
          simpa [s] using (u ⟨x, hx⟩).2
        exact (hfix_of_mem_s _ hux).symm
      · rcases hcompl_of_not_mem_s x hx with hxi | hxj
        · subst x
          rw [Equiv.swap_apply_left,
            Equiv.Perm.ofSubtype_apply_of_not_mem u (by simp [s] : j ∉ s),
            Equiv.Perm.ofSubtype_apply_of_not_mem u (by simp [s] : i ∉ s)]
          exact (Equiv.swap_apply_left i j).symm
        · subst x
          rw [Equiv.swap_apply_right,
            Equiv.Perm.ofSubtype_apply_of_not_mem u (by simp [s] : i ∉ s),
            Equiv.Perm.ofSubtype_apply_of_not_mem u (by simp [s] : j ∉ s)]
          exact (Equiv.swap_apply_right i j).symm
    · apply Equiv.Perm.ext
      intro x
      apply Subtype.ext
      change (Equiv.Perm.ofSubtype u) (x : α) = u x
      rw [Equiv.Perm.ofSubtype_apply_of_mem u x.2]
  let Nc : Subgroup C := N.subgroupOf C
  have hNc_normal : Nc.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNC]
    intro h k hh hk
    exact (Subgroup.le_normalizer_iff.mp hCN) k hk h hh
  have hNc2 : IsPGroup 2 Nc :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNC).symm
  have hρC_image2 : IsPGroup 2 (Nc.map ρC) := hNc2.map ρC
  have hρC_image_normal : (Nc.map ρC).Normal := hNc_normal.map ρC hρC_surj
  have hcard_s : 5 ≤ Nat.card s := by
    rw [Nat.card_coe_set_eq]
    have hpair : ({i, j} : Set α).ncard = 2 := Set.ncard_pair hij
    rw [show s = ({i, j} : Set α)ᶜ from rfl, Set.ncard_compl, hpair,
      Nat.card_eq_fintype_card]
    omega
  intro n hnN
  by_contra hnz
  have hnc : (⟨n, hNC hnN⟩ : C) ∈ Nc := hnN
  have hρn_ne : ρC ⟨n, hNC hnN⟩ ≠ 1 := by
    intro hρn
    have hnfix : ∀ x : α, x ∈ s → n x = x := by
      intro x hx
      have h' : (ρC ⟨n, hNC hnN⟩) ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hρn]; rfl
      have := congrArg Subtype.val h'
      change ((⟨n, hNC hnN⟩ : C) : Equiv.Perm α) x = x at this
      simpa using this
    have himage : n '' s = s := by
      apply Set.Subset.antisymm
      · rintro _ ⟨y, hy, rfl⟩
        rw [hnfix y hy]
        exact hy
      · intro y hy
        exact ⟨y, hy, hnfix y hy⟩
    have hmaps : n '' ({i, j} : Set α) = ({i, j} : Set α) := by
      have hcompl : n '' sᶜ = sᶜ := by
        rw [Set.image_compl_eq n.bijective, himage]
      have hs : sᶜ = ({i, j} : Set α) := by simp [s]
      rwa [hs] at hcompl
    have hni : n i = i ∨ n i = j := by
      have h : n i ∈ n '' ({i, j} : Set α) := ⟨i, by simp, rfl⟩
      rw [hmaps] at h
      simpa using h
    have hnj_of_ne : n j ≠ j → n j = i := by
      intro hne
      have h : n j ∈ n '' ({i, j} : Set α) := ⟨j, by simp, rfl⟩
      rw [hmaps] at h
      have h' : n j = i ∨ n j = j := by simpa using h
      exact h'.resolve_right hne
    rcases hni with hni | hni
    · have hn1 : n = 1 := by
        ext x
        by_cases hx : x ∈ s
        · exact hnfix x hx
        · rcases hcompl_of_not_mem_s x hx with hxi | hxj
          · subst x
            exact hni
          · subst x
            have hnj : n j = j := by
              by_contra hne
              have h := hnj_of_ne hne
              exact hij (n.injective (h.trans hni.symm)).symm
            exact hnj
      rw [hn1] at hnz
      exact hnz (Subgroup.one_mem _)
    · have hng : n = g := by
        ext x
        by_cases hx : x ∈ s
        · exact (hnfix x hx).trans (hfix_of_mem_s x hx).symm
        · rcases hcompl_of_not_mem_s x hx with hxi | hxj
          · subst x
            rw [hni]
            exact (Equiv.swap_apply_left i j).symm
          · subst x
            have hnj : n j = i := by
              by_contra hne
              have h : n j = j := by
                by_contra hne'
                exact hne (hnj_of_ne hne')
              exact hij (n.injective (h.trans hni.symm)).symm
            rw [hnj]
            exact (Equiv.swap_apply_right i j).symm
      rw [hng] at hnz
      exact hnz (Subgroup.mem_zpowers _)
  have hmap_ne_bot : Nc.map ρC ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff] at hbot
    exact hρn_ne (MonoidHom.mem_ker.mp (hbot hnc))
  have hnt : Nontrivial (Nc.map ρC) :=
    (Subgroup.nontrivial_iff_ne_bot (Nc.map ρC)).mpr hmap_ne_bot
  have hAlt : alternatingGroup s ≤ Nc.map ρC := by
    haveI : (Nc.map ρC).Normal := hρC_image_normal
    exact Equiv.Perm.alternatingGroup_le_of_normal hcard_s hnt
  have h2lt : 2 < Fintype.card s := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h2lt
  let τ : Equiv.Perm s := Equiv.swap a b * Equiv.swap a c
  have hτ3 : τ.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hτmem : τ ∈ Nc.map ρC := hAlt hτ3.mem_alternatingGroup
  obtain ⟨k, hk⟩ := hρC_image2.exists_orderOf_eq_pow ⟨τ, hτmem⟩
  have horder : orderOf (⟨τ, hτmem⟩ : Nc.map ρC) = 3 := by
    rw [Subgroup.orderOf_mk, hτ3.orderOf]
  rw [horder] at hk
  have h2dvd : 2 ∣ 2 ^ k := by
    cases k with
    | zero => simp at hk
    | succ k => exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  rw [← hk] at h2dvd
  norm_num at h2dvd

theorem fixingSubgroup_compl_eq_range_ofSubtype (s : Set α) [DecidablePred (· ∈ s)] :
    fixingSubgroup (Equiv.Perm α) sᶜ = (Equiv.Perm.ofSubtype (p := (· ∈ s))).range := by
  ext g
  rw [mem_fixingSubgroup_iff, Equiv.Perm.mem_range_ofSubtype_iff]
  constructor
  · intro h x hx
    by_contra hxs
    exact (Equiv.Perm.mem_support.mp hx) (h x hxs)
  · intro h y hy
    by_contra hne
    exact hy (h (Equiv.Perm.mem_support.mpr hne))

theorem centralizer_swap_sup_fixingSubgroup_eq_top {i j k : α} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm α)) ⊔
      fixingSubgroup (Equiv.Perm α) ({i, j, k}ᶜ : Set α) = ⊤ := by
  classical
  set C : Subgroup (Equiv.Perm α) :=
    Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm α))
  set S : Subgroup (Equiv.Perm α) :=
    fixingSubgroup (Equiv.Perm α) ({i, j, k}ᶜ : Set α)
  have hpair : ∀ {a b : α}, a ∉ ({i, j} : Set α) → b ∉ ({i, j} : Set α) → a ≠ b →
      Equiv.swap a b ∈ C := by
    intro a b ha hb hab
    have ha' : a ≠ i ∧ a ≠ j := by simpa using ha
    have hb' : b ≠ i ∧ b ≠ j := by simpa using hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Equiv.Perm.Disjoint.commute
    intro x
    by_cases hx : x = i ∨ x = j
    · left
      rcases hx with rfl | rfl
      · exact Equiv.swap_apply_of_ne_of_ne ha'.1.symm hb'.1.symm
      · exact Equiv.swap_apply_of_ne_of_ne ha'.2.symm hb'.2.symm
    · right
      push Not at hx
      exact Equiv.swap_apply_of_ne_of_ne hx.1 hx.2
  have htriple : ∀ {a b : α}, a ∈ ({i, j, k} : Set α) → b ∈ ({i, j, k} : Set α) →
      Equiv.swap a b ∈ S := by
    intro a b ha hb
    rw [mem_fixingSubgroup_iff]
    intro x hx
    have hxa : x ≠ a := fun h => hx (h ▸ ha)
    have hxb : x ≠ b := fun h => hx (h ▸ hb)
    exact Equiv.swap_apply_of_ne_of_ne hxa hxb
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap]
  rw [Subgroup.closure_le]
  rintro σ ⟨a, b, hab, rfl⟩
  by_cases hboth : a ∈ ({i, j, k} : Set α) ∧ b ∈ ({i, j, k} : Set α)
  · exact Subgroup.mem_sup_right (htriple hboth.1 hboth.2)
  · by_cases hC : a ∉ ({i, j} : Set α) ∧ b ∉ ({i, j} : Set α)
    · exact Subgroup.mem_sup_left (hpair hC.1 hC.2 hab)
    · have hmem : a ∈ ({i, j} : Set α) ∨ b ∈ ({i, j} : Set α) := by
        by_contra h
        push Not at h
        exact hC h
      have hnotboth : a ∉ ({i, j, k} : Set α) ∨ b ∉ ({i, j, k} : Set α) := by
        by_contra h
        push Not at h
        exact hboth h
      have hstep : ∀ {x y : α}, x ∈ ({i, j} : Set α) →
          y ∉ ({i, j, k} : Set α) → x ≠ y → Equiv.swap x y ∈ C ⊔ S := by
        intro x y hx hy hxy
        have hy' : y ≠ i ∧ y ≠ j ∧ y ≠ k := by simpa using hy
        have hkij : k ∉ ({i, j} : Set α) := by simp [hik.symm, hjk.symm]
        have hyij : y ∉ ({i, j} : Set α) := by simp [hy'.1, hy'.2.1]
        rcases hx with hxi | hxj
        · subst x
          have hconj : Equiv.swap i y =
              Equiv.swap i k * Equiv.swap k y * Equiv.swap i k := by
            rw [Equiv.swap_comm i k, Equiv.swap_comm k y]
            exact (Equiv.swap_mul_swap_mul_swap (x := y) (y := k) (z := i)
              hy'.2.2 hy'.1).symm
          rw [hconj]
          exact Subgroup.mul_mem _
            (Subgroup.mul_mem _ (Subgroup.mem_sup_right (htriple (by simp) (by simp)))
              (Subgroup.mem_sup_left (hpair hkij hyij hy'.2.2.symm)))
            (Subgroup.mem_sup_right (htriple (by simp) (by simp)))
        · subst x
          have hconj : Equiv.swap j y =
              Equiv.swap j k * Equiv.swap k y * Equiv.swap j k := by
            rw [Equiv.swap_comm j k, Equiv.swap_comm k y]
            exact (Equiv.swap_mul_swap_mul_swap (x := y) (y := k) (z := j)
              hy'.2.2 hy'.2.1).symm
          rw [hconj]
          exact Subgroup.mul_mem _
            (Subgroup.mul_mem _ (Subgroup.mem_sup_right (htriple (by simp) (by simp)))
              (Subgroup.mem_sup_left (hpair hkij hyij hy'.2.2.symm)))
            (Subgroup.mem_sup_right (htriple (by simp) (by simp)))
      rcases hmem with ha | hb
      · have hb_out : b ∉ ({i, j, k} : Set α) := by
          rcases hnotboth with ha_out | hb_out
          · exfalso
            apply ha_out
            rcases ha with hai | haj
            · subst a; simp
            · subst a; simp
          · exact hb_out
        exact hstep ha hb_out hab
      · have ha_out : a ∉ ({i, j, k} : Set α) := by
          rcases hnotboth with ha_out | hb_out
          · exact ha_out
          · exfalso
            apply hb_out
            rcases hb with hbi | hbj
            · subst b; simp
            · subst b; simp
        rw [Equiv.swap_comm]
        exact hstep hb ha_out hab.symm

theorem swap_mem_fixingSubgroup (i j k : α) :
    Equiv.swap i j ∈ fixingSubgroup (Equiv.Perm α) ({i, j, k}ᶜ : Set α) := by
  rw [mem_fixingSubgroup_iff]
  intro x hx
  have hx' : x ≠ i ∧ x ≠ j ∧ x ≠ k := by
    simpa using hx
  exact Equiv.swap_apply_of_ne_of_ne hx'.1 hx'.2.1

theorem card_fixingSubgroup_compl_triple {i j k : α} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card (fixingSubgroup (Equiv.Perm α) ({i, j, k}ᶜ : Set α)) = 6 := by
  classical
  rw [fixingSubgroup_compl_eq_range_ofSubtype]
  have hcard_range :
      Nat.card (Equiv.Perm.ofSubtype (p := fun x => x ∈ ({i, j, k} : Set α))).range =
        Nat.card (Equiv.Perm ({i, j, k} : Set α)) := by
    rw [MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective
        (Equiv.Perm.ofSubtype_injective (p := fun x => x ∈ ({i, j, k} : Set α)))]
    exact Subgroup.card_top
  rw [hcard_range, Nat.card_perm]
  have hcard_s : Nat.card ({i, j, k} : Set α) = 3 := by
    rw [Nat.card_coe_set_eq]
    simp [hij, hik, hjk]
  rw [hcard_s]
  norm_num [Nat.factorial]

theorem relIndex_zpowers_swap_fixingSubgroup {i j k : α} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    (Subgroup.zpowers (Equiv.swap i j)).relIndex
      (fixingSubgroup (Equiv.Perm α) ({i, j, k}ᶜ : Set α)) = 3 := by
  have hle : Subgroup.zpowers (Equiv.swap i j) ≤
      fixingSubgroup (Equiv.Perm α) ({i, j, k}ᶜ : Set α) :=
    Subgroup.zpowers_le.mpr (swap_mem_fixingSubgroup i j k)
  have hH : Nat.card (Subgroup.zpowers (Equiv.swap i j)) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_zpowers,
      Equiv.Perm.IsSwap.orderOf ((Equiv.Perm.swap_isSwap_iff.mpr hij))]
  have hK : Nat.card (fixingSubgroup (Equiv.Perm α) ({i, j, k}ᶜ : Set α)) = 6 :=
    card_fixingSubgroup_compl_triple hij hik hjk
  have h := Subgroup.relIndex_mul_card
    (H := Subgroup.zpowers (Equiv.swap i j))
    (K := fixingSubgroup (Equiv.Perm α) ({i, j, k}ᶜ : Set α))
  rw [inf_of_le_left hle, hH, hK] at h
  omega

theorem fixingSubgroup_not_le_normalizer_zpowers_swap {i j k : α} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ¬ fixingSubgroup (Equiv.Perm α) ({i, j, k}ᶜ : Set α) ≤
      Subgroup.normalizer ((Subgroup.zpowers (Equiv.swap i j) : Subgroup (Equiv.Perm α)) :
        Set (Equiv.Perm α)) := by
  intro hle
  have hmem : Equiv.swap i k ∈
      Subgroup.normalizer ((Subgroup.zpowers (Equiv.swap i j) : Subgroup (Equiv.Perm α)) :
        Set (Equiv.Perm α)) := by
    refine hle ?_
    rw [mem_fixingSubgroup_iff]
    intro x hx
    have hx' : x ≠ i ∧ x ≠ j ∧ x ≠ k := by simpa using hx
    exact Equiv.swap_apply_of_ne_of_ne hx'.1 hx'.2.2
  have hconj := (Subgroup.mem_normalizer_iff.mp hmem) (Equiv.swap i j)
  have hconjmem : Equiv.swap i k * Equiv.swap i j * (Equiv.swap i k)⁻¹ ∈
      Subgroup.zpowers (Equiv.swap i j) := hconj.mp (Subgroup.mem_zpowers _)
  have hconj_eq : Equiv.swap i k * Equiv.swap i j * (Equiv.swap i k)⁻¹ =
      Equiv.swap k j := by
    rw [Equiv.swap_inv, show Equiv.swap i j = Equiv.swap j i from Equiv.swap_comm i j]
    exact Equiv.swap_mul_swap_mul_swap (x := j) (y := i) (z := k) hij.symm hjk
  rw [hconj_eq] at hconjmem
  have hnot : Equiv.swap k j ∉ Subgroup.zpowers (Equiv.swap i j) := by
    intro hmem'
    rw [Subgroup.mem_zpowers_iff] at hmem'
    obtain ⟨n, hn⟩ := hmem'
    have hfix : Equiv.swap i j k = k := Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm
    have hk := congrArg (fun e : Equiv.Perm α => e k) hn
    rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix, Equiv.swap_apply_left] at hk
    exact hjk hk.symm
  exact hnot hconjmem

theorem isSolvable_fixingSubgroup_compl_triple (i j k : α) :
    IsSolvable (fixingSubgroup (Equiv.Perm α) ({i, j, k}ᶜ : Set α)) := by
  classical
  have hcard_s : Nat.card ({i, j, k} : Set α) ≤ 4 := by
    rw [Nat.card_coe_set_eq]
    have h1 := Set.ncard_insert_le j ({k} : Set α)
    have h2 := Set.ncard_insert_le i (insert j ({k} : Set α))
    have hk : ({k} : Set α).ncard ≤ 1 := by simp
    omega
  let e : Equiv.Perm ({i, j, k} : Set α) ≃*
      fixingSubgroup (Equiv.Perm α) ({i, j, k}ᶜ : Set α) :=
    (MonoidHom.ofInjective
      (Equiv.Perm.ofSubtype_injective (p := fun x => x ∈ ({i, j, k} : Set α)))).trans
      (MulEquiv.subgroupCongr (fixingSubgroup_compl_eq_range_ofSubtype _).symm)
  haveI : Group.IsSolvable (Equiv.Perm ({i, j, k} : Set α)) :=
    Equiv.Perm.isSolvable (by omega)
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom)
    (MulEquiv.injective e.symm)

end CFSG.Permutation.TranspositionCentralizer
