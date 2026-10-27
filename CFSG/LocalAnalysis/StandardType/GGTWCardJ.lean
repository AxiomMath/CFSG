module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGTWDFalse
public import CFSG.LocalAnalysis.StandardType.GGTWDCells36Orb
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
public import CFSG.LocalAnalysis.StandardType.GGTWCoreDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nCJ_intCartan_three {ι : Type} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {a b : ι} (hab : a ≠ b) (hm : M a b = 3) :
    C a b = -1 ∧ C b a = -1 := by
  rcases hC.2 a b hab with ⟨h2, -⟩ | ⟨-, h1, h2⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · exact absurd h2 (by omega)
  · exact ⟨h1, h2⟩
  · exact absurd h4 (by omega)
  · exact absurd h6 (by omega)

private theorem l05nCJ_intCartan_two {ι : Type} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {a b : ι} (hab : a ≠ b) (hm : M a b = 2) :
    C a b = 0 ∧ C b a = 0 := by
  rcases hC.2 a b hab with ⟨-, h1, h2⟩ | ⟨h3, -, -⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · exact ⟨h1, h2⟩
  · exact absurd h3 (by omega)
  · exact absurd h4 (by omega)
  · exact absurd h6 (by omega)

private theorem l05nCJ_coxeterA_entry (m : ℕ) (i j : Fin m) :
    (CoxeterMatrix.A m) i j =
      if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 :=
  rfl

private theorem l05nCJ_cartanA_entry (m : ℕ) (i j : Fin m) :
    CartanMatrix.A m i j =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 :=
  rfl

private theorem l05nCJ_cartan_of_reindex {m : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (eA : Fin m ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = (CoxeterMatrix.A m).reindex eA) :
    ∀ i j : Fin m, CL (eA i) (eA j) = CartanMatrix.A m i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hCL.1, l05nCJ_cartanA_entry]
    simp
  · have hentryM : ML (eA i) (eA j) = (CoxeterMatrix.A m) i j := by
      rw [hML, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have hne : eA i ≠ eA j := fun h => hij (eA.injective h)
    by_cases h3 : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
    · have hM3 : ML (eA i) (eA j) = 3 := by
        rw [hentryM, l05nCJ_coxeterA_entry, if_neg hij]
        rw [if_pos (h3.elim (fun h => Or.inr h) (fun h => Or.inl h))]
      have hthree := l05nCJ_intCartan_three hCL hne hM3
      rw [hthree.1, l05nCJ_cartanA_entry, if_neg hij, if_pos h3]
    · have hM2 : ML (eA i) (eA j) = 2 := by
        rw [hentryM, l05nCJ_coxeterA_entry, if_neg hij]
        rw [if_neg (fun h => h3 (h.elim (fun h => Or.inr h) (fun h => Or.inl h)))]
      have htwo := l05nCJ_intCartan_two hCL hne hM2
      rw [htwo.1, l05nCJ_cartanA_entry, if_neg hij, if_neg h3]

private def l05nCJ_Padj (N : ℕ) (hN : 5 ≤ N) :
    Fin (N - 3) ≃ {i : Fin (N - 1) // ggTWInJ N GGTWPos.adj i.val} where
  toFun k := ⟨⟨k.val, by omega⟩, by simp only [ggTWInJ]; omega⟩
  invFun i := ⟨i.1.val, by have := i.2; simp only [ggTWInJ] at this; omega⟩
  left_inv k := by apply Fin.ext; rfl
  right_inv i := by apply Subtype.ext; apply Fin.ext; rfl

private def l05nCJ_Pends (N : ℕ) (hN : 5 ≤ N) :
    Fin (N - 3) ≃ {i : Fin (N - 1) // ggTWInJ N GGTWPos.ends i.val} where
  toFun k := ⟨⟨k.val + 1, by omega⟩, by simp only [ggTWInJ]; omega⟩
  invFun i := ⟨i.1.val - 1, by have := i.2; simp only [ggTWInJ] at this; omega⟩
  left_inv k := by apply Fin.ext; exact Nat.add_sub_cancel k.val 1
  right_inv i := by
    apply Subtype.ext
    exact Fin.ext (Nat.sub_add_cancel i.2.1)

private theorem l05nCJ_A_adj (N : ℕ) (hN : 5 ≤ N) (a b : Fin (N - 3)) :
    (CartanMatrix.A (N - 1)) (l05nCJ_Padj N hN a).1 (l05nCJ_Padj N hN b).1 =
      (CartanMatrix.A (N - 3)) a b := by
  have ha : (l05nCJ_Padj N hN a).1 = ⟨a.val, by omega⟩ := Fin.ext rfl
  have hb : (l05nCJ_Padj N hN b).1 = ⟨b.val, by omega⟩ := Fin.ext rfl
  rw [ha, hb]
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.mk.injEq]
  split_ifs <;> omega

private theorem l05nCJ_A_ends (N : ℕ) (hN : 5 ≤ N) (a b : Fin (N - 3)) :
    (CartanMatrix.A (N - 1)) (l05nCJ_Pends N hN a).1 (l05nCJ_Pends N hN b).1 =
      (CartanMatrix.A (N - 3)) a b := by
  have ha : (l05nCJ_Pends N hN a).1 = ⟨a.val + 1, by omega⟩ := Fin.ext rfl
  have hb : (l05nCJ_Pends N hN b).1 = ⟨b.val + 1, by omega⟩ := Fin.ext rfl
  rw [ha, hb]
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.mk.injEq]
  split_ifs <;> omega

private theorem l05nCJ_bulk {G : Type} [Group G] [Finite G] {p N : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (hpN : p ∣ N) (hN5 : 5 ≤ N) {Bs J : Subgroup G}
    (hNJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hcomm : ∀ a b : ↥Bs, a * b = b * a) {S : Type} (eS : Fin (N - 3) ≃ S)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φJ : S → MulAut ↥Bs} {hJ : S → V} {αJ : S → Module.Dual (ZMod p) V}
    (hlin : ∀ j w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j)
    (hpair : ∀ a b : Fin (N - 3), αJ (eS a) (hJ (eS b)) =
      ((CartanMatrix.A (N - 3)) a b : ZMod p))
    (hAJ : ggAutomizer J Bs = Subgroup.closure (Set.range φJ)) :
    p ^ (N - 3) ≤ Nat.card ↥(Bs ⊓ J) := by
  classical
  letI : CommMonoid ↥Bs := { (inferInstance : Monoid ↥Bs) with mul_comm := hcomm }
  letI : CommMonoid ↥(Bs ⊓ J) :=
    { (inferInstance : Monoid ↥(Bs ⊓ J)) with
      mul_comm := fun a b => Subtype.ext (by
        show a.1 * b.1 = b.1 * a.1
        exact congrArg Subtype.val (hcomm ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩)) }
  have hp2 : p ≠ 2 := by omega
  have hneg2 : (-2 : ZMod p) ≠ 0 := neg_ne_zero.mpr (zmod_two_ne_zero hp2)
  have hdet : ((CartanMatrix.A (N - 3)).map (fun x : ℤ => (x : ZMod p))).det ≠ 0 := by
    rw [← Int.cast_det, CartanMatrix.A_det]
    intro hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    have hpZ : (p : ℤ) ∣ (N : ℤ) := by exact_mod_cast hpN
    have h2 : (p : ℤ) ∣ (2 : ℤ) := by
      have hsub := dvd_sub hpZ hz
      have heq : (N : ℤ) - (((N - 3 : ℕ) : ℤ) + 1) = 2 := by omega
      rwa [heq] at hsub
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      (Int.natCast_dvd_natCast.1 h2))
  have hLI : LinearIndependent (ZMod p) (fun a : Fin (N - 3) => hJ (eS a)) := by
    apply linearIndependent_of_det_ne_zero
      (h := fun a : Fin (N - 3) => hJ (eS a))
      (α := fun a : Fin (N - 3) => αJ (eS a))
    have hmat : (Matrix.of fun a b : Fin (N - 3) => αJ (eS a) (hJ (eS b))) =
        (CartanMatrix.A (N - 3)).map (fun x : ℤ => (x : ZMod p)) := by
      ext a b
      rw [Matrix.of_apply, Matrix.map_apply, hpair a b]
    rw [hmat]
    exact hdet
  have hdiag : ∀ a : Fin (N - 3), αJ (eS a) (hJ (eS a)) = 2 := by
    intro a
    rw [hpair a a]
    simp [CartanMatrix.A]
  choose n hnJ hnN hnconj using fun a : Fin (N - 3) => mem_ggAutomizer_iff.mp (by
    rw [hAJ]; exact Subgroup.subset_closure ⟨eS a, rfl⟩)
  let aV : Fin (N - 3) → ↥Bs := fun a => Additive.toMul (ι.symm (hJ (eS a)))
  have hιa : ∀ a : Fin (N - 3), ι (Additive.ofMul (aV a)) = hJ (eS a) := by
    intro a; simp [aV]
  have hφa : ∀ a : Fin (N - 3), φJ (eS a) (aV a) = (aV a)⁻¹ := by
    intro a
    refine (ggLin_inv_iff (p := p) ι (φJ (eS a)) (aV a)).mpr ?_
    rw [hιa a, hlin (eS a) (hJ (eS a)), hdiag a]
    module
  have hconj : ∀ a : Fin (N - 3),
      n a * (aV a : G) * (n a)⁻¹ = (((aV a)⁻¹ : ↥Bs) : G) := by
    intro a
    exact (hnconj a (aV a)).symm.trans (congrArg Subtype.val (hφa a))
  let d : Fin (N - 3) → ↥Bs := fun a =>
    ⟨n a * (aV a : G) * (n a)⁻¹, by rw [hconj a]; exact (aV a)⁻¹ |>.2⟩
  have hd : ∀ a : Fin (N - 3), d a = (aV a)⁻¹ := fun a => Subtype.ext (hconj a)
  let c : Fin (N - 3) → ↥Bs := fun a => d a * (aV a)⁻¹
  have hcJ : ∀ a : Fin (N - 3), (c a : G) ∈ J := by
    intro a
    have h2 : (aV a : G) * (n a)⁻¹ * (aV a : G)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hNJ (aV a).2) (n a)⁻¹).mp (J.inv_mem (hnJ a))
    have h1 : n a * ((aV a : G) * (n a)⁻¹ * (aV a : G)⁻¹) ∈ J := J.mul_mem (hnJ a) h2
    have hceq : (c a : G) = n a * ((aV a : G) * (n a)⁻¹ * (aV a : G)⁻¹) := by
      have hcval : (c a : G) = (d a : G) * (aV a : G)⁻¹ := rfl
      have hdval : (d a : G) = n a * (aV a : G) * (n a)⁻¹ := rfl
      rw [hcval, hdval]; group
    rw [hceq]; exact h1
  have hιc : ∀ a : Fin (N - 3),
      ι (Additive.ofMul (c a)) = (-2 : ZMod p) • hJ (eS a) := by
    intro a
    have hd' : ι (Additive.ofMul (d a)) = - hJ (eS a) := by
      rw [hd a, ofMul_inv, map_neg, hιa a]
    have ha' : ι (Additive.ofMul ((aV a)⁻¹)) = - hJ (eS a) := by
      rw [ofMul_inv, map_neg, hιa a]
    have hof : Additive.ofMul (c a) = Additive.ofMul (d a) + Additive.ofMul ((aV a)⁻¹) := by
      dsimp only [c]; rw [ofMul_mul]
    rw [hof, map_add, hd', ha']
    module
  let cc : Fin (N - 3) → ↥(Bs ⊓ J) := fun a =>
    ⟨(c a : G), Subgroup.mem_inf.mpr ⟨(c a).2, hcJ a⟩⟩
  let f : (Fin (N - 3) → ZMod p) → ↥(Bs ⊓ J) := fun k => ∏ a, (cc a) ^ (k a).val
  have hformula : ∀ k : Fin (N - 3) → ZMod p,
      ι (Additive.ofMul (Subgroup.inclusion (show Bs ⊓ J ≤ Bs from inf_le_left) (f k))) =
        ∑ a : Fin (N - 3), (k a) • ((-2 : ZMod p) • hJ (eS a)) := by
    intro k
    have hincl : Subgroup.inclusion (show Bs ⊓ J ≤ Bs from inf_le_left) (f k) =
        ∏ a : Fin (N - 3), (c a) ^ (k a).val := by
      dsimp only [f, cc]
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro a _
      rw [map_pow]
      rfl
    rw [hincl, ofMul_prod, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [ofMul_pow, map_nsmul, hιc a]
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) (k a).val ((-2 : ZMod p) • hJ (eS a)),
      ZMod.natCast_zmod_val]
  have hf_inj : Function.Injective f := by
    intro k l hkl
    have h1 : (∑ a : Fin (N - 3), (k a) • ((-2 : ZMod p) • hJ (eS a))) =
        ∑ a : Fin (N - 3), (l a) • ((-2 : ZMod p) • hJ (eS a)) := by
      have hcongr := congrArg (fun b : ↥Bs => ι (Additive.ofMul b))
        (congrArg (Subgroup.inclusion (show Bs ⊓ J ≤ Bs from inf_le_left)) hkl)
      rwa [hformula k, hformula l] at hcongr
    have h1k : (∑ a : Fin (N - 3), (k a) • ((-2 : ZMod p) • hJ (eS a))) =
        (-2 : ZMod p) • ∑ a : Fin (N - 3), (k a) • hJ (eS a) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun a _ => by rw [smul_smul, smul_smul, mul_comm])
    have h1l : (∑ a : Fin (N - 3), (l a) • ((-2 : ZMod p) • hJ (eS a))) =
        (-2 : ZMod p) • ∑ a : Fin (N - 3), (l a) • hJ (eS a) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun a _ => by rw [smul_smul, smul_smul, mul_comm])
    have heq : (-2 : ZMod p) • (∑ a : Fin (N - 3), (k a) • hJ (eS a)) =
        (-2 : ZMod p) • ∑ a : Fin (N - 3), (l a) • hJ (eS a) := by
      rw [← h1k, h1, h1l]
    have h1' : (∑ a : Fin (N - 3), (k a) • hJ (eS a)) =
        ∑ a : Fin (N - 3), (l a) • hJ (eS a) := by
      have hcancel := congrArg (fun x : V => (-2 : ZMod p)⁻¹ • x) heq
      simpa only [smul_smul, inv_mul_cancel₀ hneg2, one_smul] using hcancel
    have h2 : (∑ a : Fin (N - 3), ((k a) - (l a)) • hJ (eS a)) = 0 := by
      rw [show (∑ a : Fin (N - 3), ((k a) - (l a)) • hJ (eS a)) =
          (∑ a : Fin (N - 3), (k a) • hJ (eS a)) -
          (∑ a : Fin (N - 3), (l a) • hJ (eS a)) by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun a _ => sub_smul _ _ _)]
      rw [h1', sub_self]
    funext a
    exact sub_eq_zero.mp
      (Fintype.linearIndependent_iff.mp hLI (fun a => (k a) - (l a)) h2 a)
  have hle := Nat.card_le_card_of_injective f hf_inj
  have hdom : Nat.card (Fin (N - 3) → ZMod p) = p ^ (N - 3) := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rwa [hdom] at hle

private theorem l05nCJ_datum {G : Type} [Group G] [Finite G] {p N k : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (hpN : p ∣ N)
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10)
    {Bs X J Y : Subgroup G} (hNJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hcomm : ∀ a b : ↥Bs, a * b = b * a)
    (hA : GGTWAligned p N k Bs X J Y) :
    p ^ (N - 3) ≤ Nat.card ↥(Bs ⊓ J) := by
  classical
  obtain ⟨pos, Λ, hΛF, hΛD, b₁, b₂, Λa, hΛaF, hΛaD, ML, CL, MK, CK, V, hVadd, hVmod, ι, φ,
    h, α, e, hb, hΛa, hiff, hML, hWM, hCL, hWMK, hCK, hk2, hlin, hrefl, hpairL, hpairK, hAL,
    hAK, hAJ⟩ := hA
  haveI : Fintype Λ := hΛF
  haveI : DecidableEq Λ := hΛD
  have hN5 : 5 ≤ N := by rcases hN with h | h | h | h | h <;> omega
  have hcartan : ∀ i j : Fin (N - 1), CL (e i) (e j) = CartanMatrix.A (N - 1) i j :=
    l05nCJ_cartan_of_reindex (m := N - 1) e hCL hML
  cases pos with
  | adj =>
      let eS : Fin (N - 3) ≃ {j : Λ // j ≠ b₁ ∧ j ≠ b₂} :=
        (l05nCJ_Padj N hN5).trans (Equiv.subtypeEquiv e hiff)
      have hpair' : ∀ a b : Fin (N - 3),
          α (Sum.inl (eS a).1) (h (Sum.inl (eS b).1)) =
            ((CartanMatrix.A (N - 3)) a b : ZMod p) := by
        intro a b
        have hsa : (eS a).1 = e ((l05nCJ_Padj N hN5 a).1) := by
          simp only [eS, Equiv.trans_apply, Equiv.subtypeEquiv_apply]
        have hsb : (eS b).1 = e ((l05nCJ_Padj N hN5 b).1) := by
          simp only [eS, Equiv.trans_apply, Equiv.subtypeEquiv_apply]
        rw [hsa, hsb, hpairL, hcartan, l05nCJ_A_adj N hN5 a b]
      exact l05nCJ_bulk (p := p) (N := N) hp hpN hN5 hNJ hcomm eS
        (fun j w => hlin (Sum.inl j.1) w) hpair' hAJ
  | ends =>
      let eS : Fin (N - 3) ≃ {j : Λ // j ≠ b₁ ∧ j ≠ b₂} :=
        (l05nCJ_Pends N hN5).trans (Equiv.subtypeEquiv e hiff)
      have hpair' : ∀ a b : Fin (N - 3),
          α (Sum.inl (eS a).1) (h (Sum.inl (eS b).1)) =
            ((CartanMatrix.A (N - 3)) a b : ZMod p) := by
        intro a b
        have hsa : (eS a).1 = e ((l05nCJ_Pends N hN5 a).1) := by
          simp only [eS, Equiv.trans_apply, Equiv.subtypeEquiv_apply]
        have hsb : (eS b).1 = e ((l05nCJ_Pends N hN5 b).1) := by
          simp only [eS, Equiv.trans_apply, Equiv.subtypeEquiv_apply]
        rw [hsa, hsb, hpairL, hcartan, l05nCJ_A_ends N hN5 a b]
      exact l05nCJ_bulk (p := p) (N := N) hp hpN hN5 hNJ hcomm eS
        (fun j w => hlin (Sum.inl j.1) w) hpair' hAJ

theorem ggTW_inf_J_ge {G : Type} [Group G] [Finite G] {p N k : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (hpN : p ∣ N) (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) {B Bs : Subgroup G} {x y : G}
    {L D J K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hk : k = 1 ∨ k = 2)
    (hA : GGTWAligned p N k Bs L J K ∨ GGTWAligned p N k Bs K J L) :
    p ^ (N - 3) ≤ Nat.card ↥(Bs ⊓ J) := by
  obtain ⟨⟨hI, hBsB, hDJ⟩, hOp, hInnAll, hNoT, hNbr, hRG, hSW⟩ := hH
  have hInn : GGInnerDiagOn Bs L := hInnAll.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsB.2.1.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) (⟨b, hb⟩ : ↥Bs))
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hInn
  have hNJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBsB.1 hDJ.1 hBsL
  have hcomm' : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
    Subtype.ext (hcomm a.1 a.2 b.1 b.2)
  rcases hA with hA | hA
  · exact l05nCJ_datum hp hpN hN hNJ hcomm' hA
  · exact l05nCJ_datum hp hpN hN hNJ hcomm' hA

end CFSG.StandardType

end
