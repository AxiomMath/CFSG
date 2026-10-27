module

public import CFSG.Quasithin.EmptyFaithful.S153Q3Ba
public import CFSG.Quasithin.EmptyFaithful.S153QDef

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q3B

section Points

variable {W : Type} [CommGroup W] {z : MulAut W} {o : Subgroup W}

theorem pt_card (h : IsPt z o) : Nat.card ↥o = 4 := And.left h

theorem pt_mem (h : IsPt z o) {w : W} (hw : w ∈ o) : z w ∈ o := And.right h w hw

end Points

section Counting

variable {W : Type} [CommGroup W] [Finite W]

theorem eq_of_mem_of_ne_one {z : MulAut W} (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1)
    {o₁ o₂ : Subgroup W} (h₁ : IsPt z o₁) (h₂ : IsPt z o₂) {w : W} (hw₁ : w ∈ o₁) (hw₂ : w ∈ o₂)
    (hw : w ≠ 1) : o₁ = o₂ := by
  classical
  have hz3w : z (z (z w)) = w := by
    have := congrArg (fun f : MulAut W => f w) hz3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hne : ∀ x : W, x ≠ 1 → z x ≠ 1 := fun x hx h => hx (z.injective (h.trans (map_one z).symm))
  have h1 : z w ≠ w := fun h => hw (hfpf w h)
  have h2 : z (z w) ≠ z w := fun h => h1 (z.injective h)
  have h3 : z (z w) ≠ w := fun h => h1 ((congrArg z h).symm.trans hz3w)
  let S : Finset W := {1, w, z w, z (z w)}
  have hS : S.card = 4 := by
    have a1 : (1 : W) ∉ ({w, z w, z (z w)} : Finset W) := by
      simp [hw.symm, (hne w hw).symm, (hne (z w) (hne w hw)).symm]
    have a2 : w ∉ ({z w, z (z w)} : Finset W) := by simp [h1.symm, h3.symm]
    have a3 : z w ∉ ({z (z w)} : Finset W) := by simp [h2.symm]
    simp only [S]
    rw [Finset.card_insert_of_notMem a1, Finset.card_insert_of_notMem a2,
      Finset.card_insert_of_notMem a3, Finset.card_singleton]
  have hsub : ∀ o : Subgroup W, IsPt z o → w ∈ o → (S : Set W) ⊆ (o : Set W) := by
    intro o ho hwo x hx
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact o.one_mem
    · exact hwo
    · exact pt_mem ho hwo
    · exact pt_mem ho (pt_mem ho hwo)
  have heq : ∀ o : Subgroup W, IsPt z o → w ∈ o → (o : Set W) = S := by
    intro o ho hwo
    have hc : (o : Set W).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact pt_card ho
    have hc' : (S : Set W).ncard = 4 := by
      rw [Set.ncard_coe_finset]
      exact hS
    exact (Set.eq_of_subset_of_ncard_le (hsub o ho hwo) (le_of_eq (hc.trans hc'.symm))
      (Set.toFinite _)).symm
  exact SetLike.coe_injective ((heq o₁ h₁ hw₁).trans (heq o₂ h₂ hw₂).symm)

theorem card_sup_le (A B : Subgroup W) : Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  have hsurj : Function.Surjective (fun p : ↥A × ↥B =>
      (⟨(p.1 : W) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B))) := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, y', hy', rfl⟩ := Subgroup.mem_sup.mp hx
    exact ⟨(⟨y, hy⟩, ⟨y', hy'⟩), rfl⟩
  simpa [Nat.card_prod] using Nat.card_le_card_of_surjective _ hsurj

theorem six_not_in_subgroup (L : Fin 6 → Subgroup W) (ℓ : Subgroup W) (hle : ∀ k, L k ≤ ℓ)
    (hcard : ∀ k, Nat.card ↥(L k) = 4) (hℓ : Nat.card ↥ℓ ≤ 16)
    (hdisj : ∀ i j : Fin 6, i ≠ j → ∀ w, w ∈ L i → w ∈ L j → w = 1) : False := by
  classical
  have : Fintype W := Fintype.ofFinite W
  have hpunct : ∀ H : Subgroup W,
      (Finset.univ.filter (fun w => w ∈ H ∧ w ≠ 1)).card = Nat.card ↥H - 1 := by
    intro H
    have h1 : (Finset.univ.filter (fun w => w ∈ H)).card = Nat.card ↥H := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h2 : Finset.univ.filter (fun w => w ∈ H ∧ w ≠ 1) =
        (Finset.univ.filter (fun w => w ∈ H)).erase 1 := by
      ext w
      simp [and_comm]
    rw [h2, Finset.card_erase_of_mem (by simp), h1]
  let P : Fin 6 → Finset W := fun k => Finset.univ.filter (fun w => w ∈ L k ∧ w ≠ 1)
  have hPcard : ∀ k, (P k).card = 3 := fun k => by
    simp only [P]
    rw [hpunct, hcard]
  have hPdisj : ∀ i ∈ (Finset.univ : Finset (Fin 6)), ∀ j ∈ (Finset.univ : Finset (Fin 6)),
      i ≠ j → Disjoint (P i) (P j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro w hwi hwj
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hwi hwj
    exact hwi.2 (hdisj i j hij w hwi.1 hwj.1)
  have hU : (Finset.univ.biUnion P).card = 18 := by
    rw [Finset.card_biUnion hPdisj]
    simp [hPcard]
  have hsub : Finset.univ.biUnion P ⊆ Finset.univ.filter (fun w => w ∈ ℓ ∧ w ≠ 1) := by
    intro w hw
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, P, Finset.mem_filter] at hw ⊢
    obtain ⟨k, hk, hw1⟩ := hw
    exact ⟨hle k hk, hw1⟩
  have := Finset.card_le_card hsub
  rw [hU, hpunct] at this
  omega

theorem collinear_transport {Ah : Subgroup (MulAut W)} {z : MulAut W} {lab : Fin 6 → Subgroup W}
    (hO : OvalData0 Ah z lab) {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ alternatingGroup (Fin 6))
    {a b c : Fin 6} (h : lab c ≤ lab a ⊔ lab b) : lab (σ c) ≤ lab (σ a) ⊔ lab (σ b) := by
  obtain ⟨g, -, hg⟩ := hO.surj σ hσ
  have hbij : Function.Bijective
      (fun w : ↥(lab c) => (⟨g w, hg c w w.2⟩ : ↥(lab (σ c)))) := by
    refine Function.Injective.bijective_of_nat_card_le ?_ ?_
    · intro x y hxy
      exact Subtype.ext (g.injective (congrArg Subtype.val hxy))
    · rw [pt_card (hO.pt c), pt_card (hO.pt (σ c))]
  intro u hu
  obtain ⟨⟨w, hwc⟩, hw⟩ := hbij.2 ⟨u, hu⟩
  have hgw : g w = u := congrArg Subtype.val hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp (h hwc)
  rw [← hgw, map_mul]
  exact Subgroup.mul_mem_sup (hg a x hx) (hg b y hy)

end Counting

end Q3B

theorem OvalData0.arc' {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w * w = 1)
    {Ah : Subgroup (MulAut W)} {z : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) {lab : Fin 6 → Subgroup W} (hO : OvalData0 Ah z lab) :
    ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → ¬ (lab c ≤ lab a ⊔ lab b) := by
  have _ := hW2
  intro a b c hab hac hbc hcol
  have hline : ∀ k : Fin 6, lab k ≤ lab 0 ⊔ lab 1 := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      exact le_sup_left
    by_cases hk1 : k = 1
    · subst hk1
      exact le_sup_right
    obtain ⟨σ, hσ, ha, hb, hc⟩ := Q3B.alt_three_trans a b c 0 1 k hab hac hbc (by decide)
      (Ne.symm hk0) (Ne.symm hk1)
    have := Q3B.collinear_transport hO hσ hcol
    rwa [ha, hb, hc] at this
  refine Q3B.six_not_in_subgroup lab (lab 0 ⊔ lab 1) hline (fun k => Q3B.pt_card (hO.pt k)) ?_ ?_
  · calc Nat.card ↥(lab 0 ⊔ lab 1) ≤ Nat.card ↥(lab 0) * Nat.card ↥(lab 1) :=
          Q3B.card_sup_le _ _
      _ = 16 := by rw [Q3B.pt_card (hO.pt 0), Q3B.pt_card (hO.pt 1)]
  · intro i j hij w hwi hwj
    by_contra hw
    exact hij (hO.inj (Q3B.eq_of_mem_of_ne_one hz3 hfpf (hO.pt i) (hO.pt j) hwi hwj hw))

theorem OvalData.ofOvalData0 {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w * w = 1)
    {Ah : Subgroup (MulAut W)} {z : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) {lab : Fin 6 → Subgroup W} (hO : OvalData0 Ah z lab) :
    OvalData Ah z lab := ⟨hO, OvalData0.arc' hW2 hz3 hfpf hO⟩

theorem OvalData.relabel {W : Type} [CommGroup W] {Ah : Subgroup (MulAut W)} {z : MulAut W}
    {lab : Fin 6 → Subgroup W} (hO : OvalData Ah z lab) {ρ : Equiv.Perm (Fin 6)}
    (hρ : ρ ∈ alternatingGroup (Fin 6)) : OvalData Ah z (fun k => lab (ρ.symm k)) where
  pt k := hO.pt (ρ.symm k)
  inj := hO.inj.comp ρ.symm.injective
  equiv g hg := by
    obtain ⟨σ, hσ, h⟩ := hO.equiv g hg
    refine ⟨ρ * σ * ρ⁻¹, mul_mem (mul_mem hρ hσ) (inv_mem hρ), fun k w hw => ?_⟩
    simpa [Equiv.Perm.mul_apply, Equiv.Perm.inv_def] using h (ρ.symm k) w hw
  surj σ hσ := by
    obtain ⟨g, hg, h⟩ := hO.surj (ρ⁻¹ * σ * ρ) (mul_mem (mul_mem (inv_mem hρ) hσ) hρ)
    refine ⟨g, hg, fun k w hw => ?_⟩
    simpa [Equiv.Perm.mul_apply, Equiv.Perm.inv_def] using h (ρ.symm k) w hw
  ker g hg h := hO.ker g hg fun k w hw => by simpa using h (ρ k) w (by simpa using hw)
  arc a b c hab hac hbc :=
    hO.arc _ _ _ (ρ.symm.injective.ne hab) (ρ.symm.injective.ne hac) (ρ.symm.injective.ne hbc)

end S153Q

end CFSG.Quasithin
