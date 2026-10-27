module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs

public section

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

private theorem a11b8_fPow_add {G : Type} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, orderOf (f i) = 7)
    (v w : Fin 4 → ZMod 7) : fPow f (v + w) = fPow f v * fPow f w := by
  let H : Subgroup G := Subgroup.closure (Set.range f)
  have hpair : (Set.range f).Pairwise Commute := by
    intro a ha b hb _
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact hcomm i j
  letI : CommGroup H := Subgroup.closureCommGroupOfComm hpair
  let fH : Fin 4 → H := fun i => ⟨f i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hordH : ∀ i, orderOf (fH i) = 7 := by
    intro i
    have h := Subgroup.orderOf_mk (H := H) (f i) (Subgroup.subset_closure ⟨i, rfl⟩)
    simpa [fH, hord i] using h
  have hper : ∀ i, fH i ^ ((v + w) i).val = fH i ^ (v i).val * fH i ^ (w i).val := by
    intro i
    have hval := ZMod.val_add (v i) (w i)
    have hmod : fH i ^ (v i + w i).val = fH i ^ ((v i).val + (w i).val) := by
      have h := pow_mod_orderOf (fH i) ((v i).val + (w i).val)
      rw [hordH i] at h
      rwa [← hval] at h
    change fH i ^ (v i + w i).val = fH i ^ (v i).val * fH i ^ (w i).val
    rw [hmod, pow_add]
  have keyprod : (∏ i, fH i ^ ((v + w) i).val) =
      (∏ i, fH i ^ (v i).val) * (∏ i, fH i ^ (w i).val) := by
    calc (∏ i, fH i ^ ((v + w) i).val)
        = ∏ i, (fH i ^ (v i).val * fH i ^ (w i).val) :=
          Finset.prod_congr rfl (fun i _ => hper i)
      _ = (∏ i, fH i ^ (v i).val) * (∏ i, fH i ^ (w i).val) := Finset.prod_mul_distrib
  have key : fPow fH (v + w) = fPow fH v * fPow fH w := by
    simpa only [fPow, Fin.prod_univ_four] using keyprod
  simpa [fPow, fH] using congrArg Subtype.val key

private theorem a11b8_fPow_zero {G : Type} [Group G] (f : Fin 4 → G) :
    fPow f (0 : Fin 4 → ZMod 7) = 1 := by
  simp [fPow]

private theorem a11b8_val_one : (1 : ZMod 7).val = 1 := by decide

private theorem a11b8_fPow_single {G : Type} [Group G] (f : Fin 4 → G) (i : Fin 4) :
    fPow f (Pi.single i (1 : ZMod 7)) = f i := by
  fin_cases i <;> simp [fPow, Pi.single_eq_same, Pi.single_eq_of_ne, a11b8_val_one]

private theorem a11b8_fPow_neg {G : Type} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, orderOf (f i) = 7)
    (v : Fin 4 → ZMod 7) : fPow f (-v) = (fPow f v)⁻¹ := by
  have h1 : fPow f (-v) * fPow f v = 1 := by
    rw [← a11b8_fPow_add f hcomm hord (-v) v]
    rw [_root_.neg_add_cancel]
    exact a11b8_fPow_zero f
  exact eq_inv_of_mul_eq_one_left h1

private theorem a11b8_fPow_mem {G : Type} [Group G] (f : Fin 4 → G)
    (v : Fin 4 → ZMod 7) : fPow f v ∈ Subgroup.closure (Set.range f) := by
  have h0 : f 0 ∈ Subgroup.closure (Set.range f) := Subgroup.subset_closure ⟨0, rfl⟩
  have h1 : f 1 ∈ Subgroup.closure (Set.range f) := Subgroup.subset_closure ⟨1, rfl⟩
  have h2 : f 2 ∈ Subgroup.closure (Set.range f) := Subgroup.subset_closure ⟨2, rfl⟩
  have h3 : f 3 ∈ Subgroup.closure (Set.range f) := Subgroup.subset_closure ⟨3, rfl⟩
  have p0 := Subgroup.pow_mem (Subgroup.closure (Set.range f)) h0 (v 0).val
  have p1 := Subgroup.pow_mem (Subgroup.closure (Set.range f)) h1 (v 1).val
  have p2 := Subgroup.pow_mem (Subgroup.closure (Set.range f)) h2 (v 2).val
  have p3 := Subgroup.pow_mem (Subgroup.closure (Set.range f)) h3 (v 3).val
  simp only [fPow, Fin.prod_univ_four]
  exact Subgroup.mul_mem (Subgroup.closure (Set.range f))
    (Subgroup.mul_mem (Subgroup.closure (Set.range f))
      (Subgroup.mul_mem (Subgroup.closure (Set.range f)) p0 p1) p2) p3

private theorem a11b8_fPow_range {G : Type} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, orderOf (f i) = 7) :
    Set.range (fPow f) = (Subgroup.closure (Set.range f) : Set G) := by
  let R : Subgroup G :=
    { carrier := Set.range (fPow f)
      one_mem' := ⟨0, a11b8_fPow_zero f⟩
      mul_mem' := by rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩; exact ⟨v + w, a11b8_fPow_add f hcomm hord v w⟩
      inv_mem' := by rintro _ ⟨v, rfl⟩; exact ⟨-v, a11b8_fPow_neg f hcomm hord v⟩ }
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    exact a11b8_fPow_mem f v
  · intro x hx
    exact (Subgroup.closure_le R).2 (fun y hy => by
      obtain ⟨i, rfl⟩ := hy
      exact ⟨Pi.single i (1 : ZMod 7), a11b8_fPow_single f i⟩) hx

private theorem a11b8_fPow_injective {G : Type} [Group G] [Finite G] (f : Fin 4 → G)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, orderOf (f i) = 7)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4) :
    Function.Injective (fPow f) := by
  classical
  let C : Subgroup G := Subgroup.closure (Set.range f)
  have hrange : Set.range (fPow f) = (C : Set G) := a11b8_fPow_range f hcomm hord
  let g : (Fin 4 → ZMod 7) → C := fun v => ⟨fPow f v, by
    have hv : fPow f v ∈ Set.range (fPow f) := ⟨v, rfl⟩
    rwa [hrange] at hv⟩
  have hsurj : Function.Surjective g := by
    intro x
    have hx : (x : G) ∈ Set.range (fPow f) := by
      rw [hrange]; exact x.2
    obtain ⟨v, hv⟩ := hx
    exact ⟨v, Subtype.ext hv⟩
  haveI : Fintype C := Fintype.ofFinite C
  have hcardC : Fintype.card C = 7 ^ 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hcardD : Fintype.card (Fin 4 → ZMod 7) = 7 ^ 4 := by
    rw [Fintype.card_pi_const, ZMod.card]
  intro v w hvw
  by_contra hne
  have hnotinj : ¬ Function.Injective g := by
    intro hinj
    exact hne (hinj (Subtype.ext hvw))
  have hlt := Fintype.card_lt_of_surjective_not_injective g hsurj hnotinj
  rw [hcardC, hcardD] at hlt
  exact (lt_irrefl (7 ^ 4)) hlt

private lemma a11b8_P01_cube :
    (!![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1] : Certificates.A8Nbr476.M4) ^ 3 =
      !![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1] := by decide

private lemma a11b8_P01_ne_one :
    (!![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1] : Certificates.A8Nbr476.M4) ≠ 1 := by decide

private lemma a11b8_P02_cube :
    (!![0,0,1,0; 0,1,0,0; 1,0,0,0; 0,0,0,1] : Certificates.A8Nbr476.M4) ^ 3 =
      !![0,0,1,0; 0,1,0,0; 1,0,0,0; 0,0,0,1] := by decide

private lemma a11b8_P02_ne_one :
    (!![0,0,1,0; 0,1,0,0; 1,0,0,0; 0,0,0,1] : Certificates.A8Nbr476.M4) ≠ 1 := by decide

private lemma a11b8_P12_cube :
    (!![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1] : Certificates.A8Nbr476.M4) ^ 3 =
      !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1] := by decide

private lemma a11b8_P12_ne_one :
    (!![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1] : Certificates.A8Nbr476.M4) ≠ 1 := by decide

private lemma a11b8_cube_contra {P : Certificates.A8Nbr476.M4} (hcube : P ^ 3 = P) (hne : P ≠ 1)
    (h3 : P ^ 3 = 1) : False :=
  hne (by rwa [hcube] at h3)

theorem a11NbrBadA8Input_holds
    : A11NbrBadA8Input := by
  intro hMp hLB hAM hH hLR hBF G _ _ B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb hmodel c hc hline
  have hGlue : A11GlueHyp φ₃ f n := hctx.2.2.1.1
  obtain ⟨hφinj, hfT9, hfcomm, hford, hfcard, hn3, hnswap, hcomp⟩ := hGlue
  obtain ⟨A, hA_N, hA_M, hA_gen, hA_inv, hA_nt, hA_good⟩ :=
    hAM G B Bs x L D J y K φ₃ f n Φ ρ hctx
  have hfinj := a11b8_fPow_injective f hfcomm hford hfcard
  obtain ⟨M, hMinj, hMprop⟩ :=
    hH hMp hLB G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb hmodel c hline
  have hMA : ∀ i, M i ∈ A := by
    intro i
    obtain ⟨⟨h, hhK, hhnorm, hhconj⟩, -, -, -⟩ := hMprop i
    obtain ⟨M', hM'A, hM'conj⟩ := hA_N h hhnorm
    have hrow : ∀ r : Fin 4, Matrix.vecMul (ev r) M' = Matrix.vecMul (ev r) (M i) := by
      intro r
      apply hfinj
      rw [← hM'conj (ev r), ← hhconj (ev r)]
    have hMeq : M' = M i := by
      ext r s
      have hr := hrow r
      have hr' : M'.row r = (M i).row r := by simpa [ev] using hr
      simpa using congrFun hr' s
    exact hMeq ▸ hM'A
  have hΓ : ∀ i, M i ∈ Submonoid.closure G314gens := fun i =>
    hLR A hA_gen hA_inv hA_nt hA_good (M i) (hMA i) (hMprop i).2.1
  have hlast : ∀ i, c = 0 ∧
      (M i = (!![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,2] : Certificates.A8Nbr476.M4) ∨
       M i = (!![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,4] : Certificates.A8Nbr476.M4)) := by
    intro i
    have hcube_i : M i ^ 3 = 1 := (hMprop i).2.2.1
    rcases hBF c hc (M i) (hΓ i) (hMprop i).2.1 (hMprop i).2.2.2 with h | h | h | h
    · exact ((a11b8_cube_contra a11b8_P01_cube a11b8_P01_ne_one
        (by simpa [h] using hcube_i)).elim)
    · exact ((a11b8_cube_contra a11b8_P02_cube a11b8_P02_ne_one
        (by simpa [h] using hcube_i)).elim)
    · exact ((a11b8_cube_contra a11b8_P12_cube a11b8_P12_ne_one
        (by simpa [h] using hcube_i)).elim)
    · exact h
  rcases hc with hc0 | hc3 | hc5 | hc6
  · have h2 : ∀ i, M i = (!![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,2] : Certificates.A8Nbr476.M4) ∨
        M i = (!![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,4] : Certificates.A8Nbr476.M4) :=
      fun i => (hlast i).2
    have h01 : M 0 = M 1 ∨ M 0 = M 2 ∨ M 1 = M 2 := by
      rcases h2 0 with h0 | h0 <;> rcases h2 1 with h1 | h1
      · exact Or.inl (h0.trans h1.symm)
      · rcases h2 2 with h2' | h2'
        · exact Or.inr (Or.inl (h0.trans h2'.symm))
        · exact Or.inr (Or.inr (h1.trans h2'.symm))
      · rcases h2 2 with h2' | h2'
        · exact Or.inr (Or.inr (h1.trans h2'.symm))
        · exact Or.inr (Or.inl (h0.trans h2'.symm))
      · exact Or.inl (h0.trans h1.symm)
    rcases h01 with hh | hh | hh
    · exact (by decide : (0 : Fin 3) ≠ 1) (hMinj hh)
    · exact (by decide : (0 : Fin 3) ≠ 2) (hMinj hh)
    · exact (by decide : (1 : Fin 3) ≠ 2) (hMinj hh)
  · exact (by decide : (3 : ZMod 7) ≠ 0) (hc3.symm.trans (hlast 0).1)
  · exact (by decide : (5 : ZMod 7) ≠ 0) (hc5.symm.trans (hlast 0).1)
  · exact (by decide : (6 : ZMod 7) ≠ 0) (hc6.symm.trans (hlast 0).1)

end CFSG.StandardType.A11

end
