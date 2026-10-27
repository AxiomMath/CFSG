module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorusComp

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type} [Group G]

open CosetGeom (graph stab ballStab nbrs vtype)

variable {G₀ G₁ G₂ : Subgroup G} {X : Subgroup G} {δ : CosetGeom G₀ G₁ G₂}

theorem torusComp_trans_of_swap (hδ : X ≤ stab δ)
    (hswap : ∀ e ∈ torusComp X δ, vtype e = false → ∀ u ∈ nbrs e, ∀ w ∈ nbrs e, u ≠ w →
      X ≤ stab u → X ≤ stab w →
      ∃ n : ↥G₀, (n : G) ∈ Subgroup.normalizer (X : Set G) ∧ n • u = w)
    {y y' : CosetGeom G₀ G₁ G₂} (hy : y ∈ torusComp X δ) (hyt : vtype y = true)
    (hy' : y' ∈ torusComp X δ) (hy't : vtype y' = true) :
    ∃ n : ↥G₀, (n : G) ∈ Subgroup.normalizer (X : Set G) ∧ n • y = y' := by
  have key : ∀ {v : CosetGeom G₀ G₁ G₂},
      Relation.ReflTransGen
        (fun a b => a ∈ torusComp X δ ∧ b ∈ torusComp X δ ∧ (graph G₀ G₁ G₂).Adj a b) y v →
      (vtype v = true →
        ∃ n : ↥G₀, (n : G) ∈ Subgroup.normalizer (X : Set G) ∧ n • y = v) ∧
      (vtype v = false → ∀ w ∈ nbrs v, X ≤ stab w →
        ∃ n : ↥G₀, (n : G) ∈ Subgroup.normalizer (X : Set G) ∧ n • y = w) := by
    intro v h
    induction h with
    | refl =>
      refine ⟨?_, ?_⟩
      · intro _
        exact ⟨1, Subgroup.one_mem _, by simp⟩
      · intro hfalse
        exfalso
        rw [hfalse] at hyt
        exact Bool.false_ne_true hyt
    | tail hab hbc ih =>
      rename_i u v
      obtain ⟨hu, hv, hadj⟩ := hbc
      have hne : vtype u ≠ vtype v := CosetGeom.vtype_ne_of_adj hadj
      have hXu : X ≤ stab u := le_stab_of_mem_torusComp hδ hu
      by_cases hut : vtype u = true
      · have hvf : vtype v = false := by
          cases hvv : vtype v with
          | false => rfl
          | true => exact absurd (hut.trans hvv.symm) hne
        refine ⟨?_, ?_⟩
        · intro hvt
          exfalso
          exact Bool.false_ne_true (hvf.symm.trans hvt)
        · intro _ w hw hwstab
          obtain ⟨n, hn, hny⟩ := ih.1 hut
          by_cases hwu : w = u
          · exact ⟨n, hn, hny.trans hwu.symm⟩
          · have huw : u ≠ w := Ne.symm hwu
            obtain ⟨m, hm, hmu⟩ := hswap v hv hvf u hadj.symm w hw huw hXu hwstab
            exact ⟨m * n, (Subgroup.normalizer (X : Set G)).mul_mem hm hn, by
              rw [mul_smul, hny, hmu]⟩
      · have huf : vtype u = false := by
          cases hvu : vtype u with
          | false => rfl
          | true => exact absurd hvu hut
        have hvt : vtype v = true := by
          cases hvv : vtype v with
          | false => exact absurd (huf.trans hvv.symm) hne
          | true => rfl
        refine ⟨?_, ?_⟩
        · intro _
          exact ih.2 huf v hadj (le_stab_of_mem_torusComp hδ hv)
        · intro hvf
          exfalso
          exact Bool.false_ne_true (hvf.symm.trans hvt)
  exact (key (torusComp_reflTransGen hy hy')).1 hy't

theorem torusComp_simple_of_loc (hδ : X ≤ stab δ)
    (h3 : ∀ y : CosetGeom G₀ G₁ G₂, vtype y = true → (nbrs y).ncard = 3)
    (htwin : ∀ y y' : CosetGeom G₀ G₁ G₂, vtype y = true → vtype y' = true →
      nbrs y = nbrs y' → y = y')
    (hnbr : ∀ y ∈ torusComp X δ, vtype y = true → ∀ e ∈ nbrs y, X ≤ stab e)
    (htwo : ∀ e ∈ torusComp X δ, vtype e = false → ∀ u ∈ nbrs e, ∀ w ∈ nbrs e, ∀ w' ∈ nbrs e,
      X ≤ stab u → X ≤ stab w → X ≤ stab w' → u = w ∨ u = w' ∨ w = w')
    (hloc : ∀ y ∈ torusComp X δ, vtype y = true → ∀ e ∈ nbrs y, ∀ e' ∈ nbrs y,
      ∃ n : ↥G₀, (n : G) ∈ Subgroup.normalizer (X : Set G) ∧ n • y = y ∧ n • e = e')
    {y : CosetGeom G₀ G₁ G₂} (hy : y ∈ torusComp X δ) (hyt : vtype y = true)
    {e₁ e₂ y' : CosetGeom G₀ G₁ G₂} (h₁ : (graph G₀ G₁ G₂).Adj y e₁)
    (h₂ : (graph G₀ G₁ G₂).Adj y e₂) (hy' : y' ∈ torusComp X δ) (hne : y' ≠ y)
    (h₁' : (graph G₀ G₁ G₂).Adj e₁ y') (h₂' : (graph G₀ G₁ G₂).Adj e₂ y') : e₁ = e₂ := by
  by_contra h12
  have hy3 : (nbrs y).ncard = 3 := h3 y hyt
  have he1 : X ≤ stab e₁ := hnbr y hy hyt e₁ h₁
  have he2 : X ≤ stab e₂ := hnbr y hy hyt e₂ h₂
  have hy'stab : X ≤ stab y' := le_stab_of_mem_torusComp hδ hy'
  have ht1 : vtype e₁ = false := by
    cases hve : vtype e₁ with
    | false => rfl
    | true => exact absurd (hyt.trans hve.symm) (CosetGeom.vtype_ne_of_adj h₁)
  have ht2 : vtype e₂ = false := by
    cases hve : vtype e₂ with
    | false => rfl
    | true => exact absurd (hyt.trans hve.symm) (CosetGeom.vtype_ne_of_adj h₂)
  have hty' : vtype y' = true := by
    cases hvy : vtype y' with
    | false => exact absurd (ht1.trans hvy.symm) (CosetGeom.vtype_ne_of_adj h₁')
    | true => rfl
  have hex : ∃ e₃ ∈ nbrs y, e₃ ≠ e₁ ∧ e₃ ≠ e₂ := by
    by_contra h
    have hsub : nbrs y ⊆ ({e₁, e₂} : Set (CosetGeom G₀ G₁ G₂)) := by
      intro z hz
      by_cases hz1 : z = e₁
      · simp [hz1]
      · by_cases hz2 : z = e₂
        · simp [hz2]
        · exact absurd ⟨z, hz, hz1, hz2⟩ h
    have hle : (nbrs y).ncard ≤ ({e₁, e₂} : Set (CosetGeom G₀ G₁ G₂)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair h12, hy3] at hle
    omega
  obtain ⟨e₃, he₃mem, he₃ne1, he₃ne2⟩ := hex
  have hset3 : nbrs y = {e₁, e₂, e₃} := by
    have hsub : ({e₁, e₂, e₃} : Set (CosetGeom G₀ G₁ G₂)) ⊆ nbrs y := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · exact he₃mem
    have hs : ({e₁, e₂, e₃} : Set (CosetGeom G₀ G₁ G₂)).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨e₁, e₂, e₃, h12, Ne.symm he₃ne1, Ne.symm he₃ne2, rfl⟩
    have hfin : (nbrs y).Finite := Set.finite_of_ncard_ne_zero (by rw [hy3]; norm_num)
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hy3, hs]) hfin).symm
  obtain ⟨n, hn, hny, hn1⟩ := hloc y hy hyt e₁ h₁ e₃ he₃mem
  set z : CosetGeom G₀ G₁ G₂ := n • y' with hz
  have hzstab : X ≤ stab z := by
    rw [hz]
    exact le_stab_smul_of_mem_normalizer hn hy'stab
  have hzy : z ≠ y := by
    intro h
    apply hne
    have h' : n • y' = n • y := by rw [← hz, h, hny]
    exact MulAction.injective n h'
  set f : CosetGeom G₀ G₁ G₂ := n • e₂ with hf
  have hf_false : vtype f = false := by
    rw [hf, CosetGeom.vtype_smul, ht2]
  have hfstab : X ≤ stab f := by
    rw [hf]
    exact le_stab_smul_of_mem_normalizer hn he2
  have hfy : (graph G₀ G₁ G₂).Adj y f := by
    rw [hf, ← hny]
    exact (CosetGeom.smul_adj n).mpr h₂
  have hfΔ : f ∈ torusComp X δ := mem_torusComp_of_adj hδ hy hfy hfstab
  have hfne3 : f ≠ e₃ := by
    intro h
    have h' : n • e₂ = n • e₁ := by rw [← hf, h, hn1]
    exact h12 (MulAction.injective n h').symm
  have hf12 : f = e₁ ∨ f = e₂ := by
    have hmem : f ∈ nbrs y := hfy
    rw [hset3] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hfne3
  have hfy' : y' ∈ nbrs f := by
    rcases hf12 with h | h
    · rw [h]
      exact h₁'
    · rw [h]
      exact h₂'
  have hyf : y ∈ nbrs f := hfy.symm
  have hfz : z ∈ nbrs f := by
    rw [hf, hz]
    exact (CosetGeom.smul_adj n).mpr h₂'
  have hy'z : y' = z := by
    have h := htwo f hfΔ hf_false y hyf y' hfy' z hfz
      (le_stab_of_mem_torusComp hδ hy) hy'stab hzstab
    rcases h with h | h | h
    · exact absurd h.symm hne
    · exact absurd h.symm hzy
    · exact h
  have hze3 : z ∈ nbrs e₃ := by
    rw [hz, ← hn1]
    exact (CosetGeom.smul_adj n).mpr h₁'
  have he3y' : (graph G₀ G₁ G₂).Adj y' e₃ := by
    rw [hy'z]
    exact hze3.symm
  have hsub : nbrs y ⊆ nbrs y' := by
    intro w hw
    rw [hset3] at hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact h₁'.symm
    · exact h₂'.symm
    · exact he3y'
  have hfin' : (nbrs y').Finite :=
    Set.finite_of_ncard_ne_zero (by rw [h3 y' hty']; norm_num)
  have heq : nbrs y = nbrs y' :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [h3 y' hty', hy3]) hfin'
  exact hne (htwin y y' hyt hty' heq).symm

end CFSG.Quasithin.F112Crit

end
