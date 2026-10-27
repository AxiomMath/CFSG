module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTBFrame
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompBasic

public section

namespace CFSG.StandardType.LinTwoGen

open Polynomial CFSG CFSG.Assembly TableB Matrix CoordSL

theorem exists_frame_of_maxRank {d : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (hd : 6 ≤ d)
    {E : Subgroup (SpecialLinearGroup (Fin d) K)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ (d / 2) ≤ Nat.card E) :
    ∃ (g : K[X]) (_ : Fact (Irreducible g)) (_ : g ∣ cyclotomic 3 K) (s r : ℕ)
      (ε : Fin d ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (A₀ : SpecialLinearGroup (Fin d) K)
      (hC : (rootMat g).det = 1) (hCp : rootMat g ^ 3 = 1),
      (frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp).range = E ∧
        (rootPB g).dim = 2 ∧ s = d / 2 ∧ r = d - 2 * s := by
  classical
  have hchar : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
  have hp3 : ((3 : ℕ) : K) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  obtain ⟨g, hg, hgd⟩ := LineL2.exists_irreducible_factor_cyclotomic_three K
  have : Fact (Irreducible g) := ⟨hg⟩
  have hnsplit : ¬ 3 ∣ Nat.card K - 1 := by rw [hK]; decide
  have hC : (rootMat g).det = 1 := det_rootMat Nat.prime_three hnsplit hp3 hgd
  have hCp : rootMat g ^ 3 = 1 := rootMat_pow_eq_one Nat.prime_three hp3 hgd
  have hζ : AdjoinRoot.root g ^ 3 = 1 :=
    (root_isPrimitiveRoot Nat.prime_three hp3 hgd).pow_eq_one
  have hunit : ∀ j : ℕ, ¬ 3 ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1) := fun j hj c =>
    isUnit_rootMat_pow_sub Nat.prime_three hnsplit hp3 hgd j hj c
  have he2 : 2 ≤ (rootPB g).dim := LinTwoTv.two_le_rootPB_dim (fun c => hunit 1 (by decide) c)
  obtain ⟨s, r, ε, A₀, hframe⟩ := exists_frame g Nat.prime_three hp3 hgd
    (Set.range fun x : E => ((x : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      have h := TableB.IsElemAbelian.comm hE x.2 y.2
      simpa [Commute, SemiconjBy, Matrix.SpecialLinearGroup.coe_mul] using
        congrArg (fun z : SpecialLinearGroup (Fin d) K => (z : Matrix (Fin d) (Fin d) K)) h)
    (by
      rintro _ ⟨x, rfl⟩
      have h1 := hE.2 x x.2
      rw [← Matrix.SpecialLinearGroup.coe_pow, h1, Matrix.SpecialLinearGroup.coe_one])
  set ι := frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp with hι
  have hιinj : Function.Injective ι := by
    refine frameHom_injective (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp ?_
      (rootPB_dim_pos g) hunit
    intro x hx
    have hx1 : x = 1 := by simpa using (MonoidHom.mem_ker.mp hx)
    rw [hx1]
    exact Subgroup.one_mem _
  have hEle : E ≤ ι.range := by
    intro b hb
    obtain ⟨k, hk⟩ := hframe _ ⟨⟨b, hb⟩, rfl⟩
    refine ⟨Multiplicative.ofAdd fun i => (k i : ZMod 3), ?_⟩
    rw [hι, frameHom_natCast, SLRep.ggFrame_apply]
    apply Subtype.ext
    have h2 : (A₀ : Matrix (Fin d) (Fin d) K) *
        ((A₀⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    change (A₀ : Matrix (Fin d) (Fin d) K) * SLNS.nsMat ε (rootMat g) k *
      ((A₀⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (b : Matrix (Fin d) (Fin d) K)
    have hk' : (b : Matrix (Fin d) (Fin d) K) * (A₀ : Matrix (Fin d) (Fin d) K) =
        (A₀ : Matrix (Fin d) (Fin d) K) * SLNS.nsMat ε (rootMat g) k := hk
    rw [← hk', Matrix.mul_assoc, h2, Matrix.mul_one]
  have hcardι : Nat.card ι.range = 3 ^ s := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi, ZMod.card]
  have hsd : s ≤ d / 2 := by
    have hcd : Fintype.card (Fin d) = Fintype.card ((Fin (rootPB g).dim × Fin s) ⊕ Fin r) :=
      Fintype.card_congr ε
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod] at hcd
    have : 2 * s ≤ d := by nlinarith
    omega
  have hEeq : E = ι.range := by
    apply Subgroup.eq_of_le_of_card_ge hEle
    rw [hcardι]
    exact (Nat.pow_le_pow_right (by norm_num) hsd).trans hcard
  have hcd : (rootPB g).dim * s + r = d := by
    have hcd' : Fintype.card (Fin d) = Fintype.card ((Fin (rootPB g).dim × Fin s) ⊕ Fin r) :=
      Fintype.card_congr ε
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod] at hcd'
    omega
  have hs : s = d / 2 := by
    refine le_antisymm hsd ?_
    have h1 : 3 ^ (d / 2) ≤ 3 ^ s := by
      rw [← hcardι, ← hEeq]
      exact hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hdim : (rootPB g).dim = 2 := by
    by_contra hne
    have h3 : 3 ≤ (rootPB g).dim := by omega
    have h2 : 3 * s ≤ (rootPB g).dim * s := Nat.mul_le_mul_right s h3
    have hcd' : (rootPB g).dim * s + r = d := hcd
    rw [hs] at hcd' h2
    have hlt : d < 3 * (d / 2) := by omega
    omega
  have hr : r = d - 2 * s := by
    rw [hdim] at hcd
    omega
  exact ⟨g, ⟨hg⟩, hgd, s, r, ε, A₀, hC, hCp, hEeq.symm, hdim, hs, hr⟩

private theorem exists_torusAct_of_comm {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {g : K[X]} [Fact (Irreducible g)] (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3) (hdim : (rootPB g).dim = 2)
    {s r : ℕ} (hr : r ≤ 1)
    {φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K))}
    (hφcomm : ∀ k : Fin s → ℕ, ∀ x, φ (torusAct g k x) = torusAct g k (φ x))
    (hφinj : Function.Injective φ) :
    ∃ k : Fin s → ℕ, ∀ x, φ x = torusAct g k x := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  have : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hK2 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    have hcard2 : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
    have huniv : ({0, 1} : Finset K) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_insert_of_notMem, Finset.card_singleton, hcard2]
      simp [zero_ne_one]
    have : c ∈ ({0, 1} : Finset K) := by rw [huniv]; exact Finset.mem_univ c
    simpa using this
  have hK2' : ∀ c : K, c ≠ 0 → c = 1 := by
    intro c hc
    rcases hK2 c with h | h
    · exact absurd h hc
    · exact h
  have hpow3 : ∀ a : AdjoinRoot g, a ≠ 0 → a ^ 3 = 1 := by
    intro a ha
    have h1 := FiniteField.pow_card_sub_one_eq_one a ha
    have hcard : Fintype.card (AdjoinRoot g) = 4 := by
      rw [← Nat.card_eq_fintype_card,
        Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot g), (rootPB g).finrank, hdim,
        hK]
      norm_num
    rw [hcard] at h1
    simpa using h1
  set lam : Fin s → AdjoinRoot g := fun j => (φ (Pi.single j (1 : AdjoinRoot g), 0)).1 j with hlam
  have hβk : ∀ j : Fin s,
      (fun i : Fin s => ((Pi.single j (1 : ZMod 3) : Fin s → ZMod 3) i).val) =
        Pi.single j (1 : ℕ) := by
    intro j
    funext i
    by_cases hi : i = j
    · subst hi
      rw [Pi.single_eq_same, ZMod.val_one, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hi 1, Pi.single_eq_of_ne hi 1]
      rfl
  have hal : ∀ j : Fin s, Aligned hζ (Pi.single j (1 : ZMod 3)) := by
    intro j i j' hj' u hu h
    have hj'j : j' = j := by
      by_contra hne
      have h0 : ((Pi.single j (1 : ZMod 3) : Fin s → ZMod 3)) j' = 0 :=
        Pi.single_eq_of_ne hne 1
      exact hj' h0
    rw [hj'j] at h ⊢
    have hi : i = j := by
      by_contra hne
      have h0 : ((Pi.single j (1 : ZMod 3) : Fin s → ZMod 3)) i = 0 :=
        Pi.single_eq_of_ne hne 1
      rw [h, Pi.single_eq_same, mul_one] at h0
      exact (Units.ne_zero u) h0
    rw [hi]
  have hsingle : ∀ (j : Fin s) (x : AdjoinRoot g),
      φ (Pi.single j x, 0) = (Pi.single j (x * lam j), 0) := by
    intro j x
    have hj : (Pi.single j (1 : ZMod 3) : Fin s → ZMod 3) j ≠ 0 := by simp
    have hcommj : ∀ y, φ (torusAct g (fun i : Fin s =>
        ((Pi.single j (1 : ZMod 3) : Fin s → ZMod 3) i).val) y) =
        torusAct g (fun i : Fin s =>
          ((Pi.single j (1 : ZMod 3) : Fin s → ZMod 3) i).val) (φ y) := by
      intro y
      rw [hβk j]
      exact hφcomm (Pi.single j 1) y
    have h := apply_single_of_comm hprim (hal j) hcommj hj x
    rw [h]
    congr 1
    funext i
    by_cases hi : i = j
    · subst hi
      simp only [Pi.single_eq_same, if_true, hlam]
    · have hne : (Pi.single j (1 : ZMod 3) : Fin s → ZMod 3) i ≠
          (Pi.single j (1 : ZMod 3) : Fin s → ZMod 3) j := by
        rw [Pi.single_eq_of_ne hi 1, Pi.single_eq_same]
        exact zero_ne_one
      rw [if_neg hne, Pi.single_eq_of_ne hi]
  have hlam_ne : ∀ j : Fin s, lam j ≠ 0 := by
    intro j hj0
    have h1 : φ (Pi.single j (1 : AdjoinRoot g), (0 : Fin r → K)) = φ (0, 0) := by
      rw [hsingle j 1, hj0, mul_zero, Pi.single_zero]
      change (0 : (Fin s → AdjoinRoot g) × (Fin r → K)) = φ 0
      rw [map_zero]
    have h2 := hφinj h1
    have h3 : (Pi.single j (1 : AdjoinRoot g) : Fin s → AdjoinRoot g) = 0 := by
      simpa using congrArg Prod.fst h2
    have := congrFun h3 j
    simp at this
  have hk : ∀ j : Fin s, ∃ k : ℕ, AdjoinRoot.root g ^ k = lam j := by
    intro j
    obtain ⟨i, -, hi⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hprim (hpow3 (lam j) (hlam_ne j))
    exact ⟨i, hi⟩
  choose k hk using hk
  have hKr_fst : ∀ w : Fin r → K, (φ (0, w)).1 = 0 := by
    intro w
    funext i
    have hz : torusAct g (Pi.single i (1 : ℕ)) (0, w) = (0, w) := by
      refine Prod.ext ?_ ?_
      · funext i'
        simp [torusAct]
      · simp [torusAct]
    have hfix : torusAct g (fun i' : Fin s =>
        ((Pi.single i (1 : ZMod 3) : Fin s → ZMod 3) i').val) (φ (0, w)) =
        φ (0, w) := by
      rw [hβk i, ← hφcomm (Pi.single i 1) (0, w), hz]
    have h1 := (torusAct_eq_self_iff hprim (β := Pi.single i (1 : ZMod 3))
      (x := φ (0, w))).mp hfix
    exact h1 i (by simp)
  have hKr : ∀ w : Fin r → K, φ (0, w) = (0, w) := by
    intro w
    refine Prod.ext (hKr_fst w) ?_
    rcases (by omega : r = 0 ∨ r = 1) with hr0 | hr1
    · subst hr0
      funext t
      exact t.elim0
    · subst hr1
      set ψ : (Fin 1 → K) →ₗ[K] (Fin 1 → K) :=
        (LinearMap.snd K (Fin s → AdjoinRoot g) (Fin 1 → K)).comp
          (φ.comp (LinearMap.inr K (Fin s → AdjoinRoot g) (Fin 1 → K))) with hψ
      have hψw : ∀ w, ψ w = (φ (0, w)).2 := fun w => rfl
      have hψinj : Function.Injective ψ := by
        intro a b hab
        have h2 : φ (0, a) = φ (0, b) := by
          refine Prod.ext ?_ ?_
          · rw [hKr_fst a, hKr_fst b]
          · exact hab
        have h3 := hφinj h2
        have := congrArg (fun z : (Fin s → AdjoinRoot g) × (Fin 1 → K) => z.2) h3
        simpa using this
      have hψid : ∀ w, ψ w = w := by
        intro w
        have hw : w = w 0 • (fun _ : Fin 1 => (1 : K)) := by
          funext t; fin_cases t; simp
        have hcne : ψ (fun _ : Fin 1 => (1 : K)) ≠ 0 := by
          intro h0
          have h1 : ψ (fun _ : Fin 1 => (1 : K)) = ψ 0 := by rw [h0, map_zero]
          have h2 := hψinj h1
          have h3 := congrFun h2 0
          exact one_ne_zero h3
        have hc0 : ψ (fun _ : Fin 1 => (1 : K)) 0 ≠ 0 := by
          intro h0
          exact hcne (funext fun t => by fin_cases t; simpa using h0)
        have hc1 : ψ (fun _ : Fin 1 => (1 : K)) 0 = 1 := hK2' _ hc0
        rw [hw, map_smul]
        have hc_eq : ψ (fun _ : Fin 1 => (1 : K)) = fun _ : Fin 1 => (1 : K) := by
          funext t; fin_cases t; exact hc1
        rw [hc_eq]
      rw [← hψw w, hψid w]
  have hsum : ∀ x₁ : Fin s → AdjoinRoot g,
      φ (x₁, (0 : Fin r → K)) = (fun i => lam i * x₁ i, 0) := by
    intro x₁
    have hx0 : (x₁, (0 : Fin r → K)) =
        ∑ j, ((Pi.single j (x₁ j), (0 : Fin r → K)) :
          (Fin s → AdjoinRoot g) × (Fin r → K)) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum]; exact (Finset.univ_sum_single x₁).symm
      · rw [Prod.snd_sum]; simp
    rw [hx0, map_sum]
    have hR : (fun i => lam i * x₁ i, (0 : Fin r → K)) =
        ∑ j, ((Pi.single j (x₁ j * lam j), (0 : Fin r → K)) :
          (Fin s → AdjoinRoot g) × (Fin r → K)) := by
      have hfst : (fun i => lam i * x₁ i) =
          (∑ j, ((Pi.single j (x₁ j * lam j), (0 : Fin r → K)) :
            (Fin s → AdjoinRoot g) × (Fin r → K))).1 := by
        rw [Prod.fst_sum]
        funext i
        rw [Finset.sum_apply]
        change lam i * x₁ i =
          ∑ j, (Pi.single j (x₁ j * lam j) : Fin s → AdjoinRoot g) i
        rw [Finset.sum_eq_single i]
        · rw [Pi.single_eq_same]; ring
        · intro j _ hji
          exact Pi.single_eq_of_ne (M := fun _ => AdjoinRoot g) (Ne.symm hji) (x₁ j * lam j)
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      have hsnd : (0 : Fin r → K) =
          (∑ j, ((Pi.single j (x₁ j * lam j), (0 : Fin r → K)) :
            (Fin s → AdjoinRoot g) × (Fin r → K))).2 := by
        rw [Prod.snd_sum]; simp
      exact Prod.ext hfst hsnd
    rw [hR]
    exact Finset.sum_congr rfl fun j _ => hsingle j (x₁ j)
  refine ⟨k, fun x => ?_⟩
  obtain ⟨x₁, x₂⟩ := x
  have hx : (x₁, x₂) = (x₁, (0 : Fin r → K)) + (0, x₂) := by simp
  calc φ (x₁, x₂) = φ ((x₁, (0 : Fin r → K)) + (0, x₂)) := by rw [hx]
    _ = φ (x₁, (0 : Fin r → K)) + φ (0, x₂) := by rw [map_add]
    _ = (fun i => lam i * x₁ i, 0) + (0, x₂) := by rw [hsum x₁, hKr x₂]
    _ = (fun i => AdjoinRoot.root g ^ k i * x₁ i, x₂) := by
        have ha : (fun i => lam i * x₁ i) =
            (fun i => AdjoinRoot.root g ^ k i * x₁ i) := by
          funext i; rw [hk i]
        rw [← ha]
        refine Prod.ext ?_ ?_
        · funext i; simp
        · simp

theorem cent_le_of_maxRank {d : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (hd : 6 ≤ d)
    {E : Subgroup (SpecialLinearGroup (Fin d) K)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ (d / 2) ≤ Nat.card E) :
    ∀ c : SpecialLinearGroup (Fin d) K, (∀ e ∈ E, c * e = e * c) → c ∈ E := by
  classical
  obtain ⟨g, hg, hgd, s, r, ε, A₀, hC, hCp, hEeq, hdim, hs, hr⟩ :=
    exists_frame_of_maxRank hK hd hE hcard
  have : Fact (Irreducible g) := hg
  have hchar : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
  have hp3 : ((3 : ℕ) : K) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  have hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3 :=
    root_isPrimitiveRoot Nat.prime_three hp3 hgd
  have hζ : AdjoinRoot.root g ^ 3 = 1 := hprim.pow_eq_one
  set ι := frameHom (MonoidHom.id (SpecialLinearGroup (Fin d) K)) A₀ ε hC hCp with hι
  have hr1 : r ≤ 1 := by omega
  intro c hc
  rw [← hEeq]
  set u : SpecialLinearGroup (Fin d) K := A₀⁻¹ * c * A₀ with hu_def
  have hιk : ∀ k : Fin s → ℕ, ι (Multiplicative.ofAdd fun i => (k i : ZMod 3)) =
      A₀ * SLNS.nsSL ε hC k * A₀⁻¹ := by
    intro k
    rw [hι, frameHom_natCast, SLRep.ggFrame_apply]
    rfl
  have hu : ∀ k : Fin s → ℕ, u * SLNS.nsSL ε hC k = SLNS.nsSL ε hC k * u := by
    intro k
    have hmem : ι (Multiplicative.ofAdd fun i => (k i : ZMod 3)) ∈ E := by
      rw [← hEeq]; exact ⟨_, rfl⟩
    have h1 := hc _ hmem
    rw [hιk k] at h1
    rw [hu_def]
    calc (A₀⁻¹ * c * A₀) * SLNS.nsSL ε hC k
        = A₀⁻¹ * (c * (A₀ * SLNS.nsSL ε hC k * A₀⁻¹)) * A₀ := by group
      _ = A₀⁻¹ * ((A₀ * SLNS.nsSL ε hC k * A₀⁻¹) * c) * A₀ := by rw [h1]
      _ = SLNS.nsSL ε hC k * (A₀⁻¹ * c * A₀) := by group
  have hu_mat : ∀ k : Fin s → ℕ,
      (u : Matrix (Fin d) (Fin d) K) * SLNS.nsMat ε (rootMat g) k =
        SLNS.nsMat ε (rootMat g) k * (u : Matrix (Fin d) (Fin d) K) := by
    intro k
    calc (u : Matrix (Fin d) (Fin d) K) * SLNS.nsMat ε (rootMat g) k
        = ((u * SLNS.nsSL ε hC k : SpecialLinearGroup (Fin d) K) :
            Matrix (Fin d) (Fin d) K) := by
          rw [Matrix.SpecialLinearGroup.coe_mul]; rfl
      _ = ((SLNS.nsSL ε hC k * u : SpecialLinearGroup (Fin d) K) :
            Matrix (Fin d) (Fin d) K) := by rw [hu k]
      _ = SLNS.nsMat ε (rootMat g) k * (u : Matrix (Fin d) (Fin d) K) := by
          rw [Matrix.SpecialLinearGroup.coe_mul]; rfl
  set φ := frameForm g ε (u : Matrix (Fin d) (Fin d) K) with hφ
  have hφcomm : ∀ k : Fin s → ℕ, ∀ x, φ (torusAct g k x) = torusAct g k (φ x) := by
    intro k x
    rw [hφ]
    exact frameForm_torusAct_comm g ε (hu_mat k) x
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hfc : frameCoords g ε (φ x) = frameCoords g ε (φ y) := congrArg (frameCoords g ε) hxy
    rw [hφ, frameCoords_frameForm, frameCoords_frameForm] at hfc
    set ui : Matrix (Fin d) (Fin d) K :=
      ((u⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) with hui
    have hunit : ui * (u : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [hui, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h2 : frameCoords g ε x = frameCoords g ε y := by
      have h3 : ui *ᵥ ((u : Matrix (Fin d) (Fin d) K) *ᵥ frameCoords g ε x) =
          ui *ᵥ ((u : Matrix (Fin d) (Fin d) K) *ᵥ frameCoords g ε y) :=
        congrArg (fun v => ui *ᵥ v) hfc
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hunit] at h3
      simpa only [Matrix.one_mulVec] using h3
    exact (frameCoords g ε).injective h2
  obtain ⟨k, hk⟩ := exists_torusAct_of_comm (s := s) (r := r) hK hζ hprim hdim hr1 hφcomm hφinj
  have hu_nsSL : u = SLNS.nsSL ε hC k := by
    apply Subtype.ext
    apply frameForm_injective g ε
    refine LinearMap.ext fun x => ?_
    rw [← hφ, hk x]
    exact (frameForm_nsMat g ε k x).symm
  refine ⟨Multiplicative.ofAdd fun i => (k i : ZMod 3), ?_⟩
  rw [hιk k, ← hu_nsSL, hu_def]
  group

end CFSG.StandardType.LinTwoGen
