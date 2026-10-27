module

public import CFSG.Milestones.ASVolI.F48.D43.Lin
public import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4


section Gen

variable {K : Type} [Field K] (σ : K →+* K) (ω : K)

@[expose] def burnsideF48d_par (k : ℕ) : ℕ :=
  if k = 2 ∨ k = 5 then 1 else if k = 3 ∨ k = 6 then 3 else 9

@[expose] noncomputable def burnsideF48d_g (k : ℕ) : adjointGroup d4 K :=
  if k = 0 then xPar (rootOperatorFamily d4) ((1 : ℤ) • Pi.single (nd 2) 1) 1
  else if k = 1 then xPar (rootOperatorFamily d4) ((-1 : ℤ) • Pi.single (nd 2) 1) 1
  else xOuter (if 5 ≤ k then -1 else 1) (burnsideF48d_φ ω (burnsideF48d_par k))
    (σ (burnsideF48d_φ ω (burnsideF48d_par k))) (σ (σ (burnsideF48d_φ ω (burnsideF48d_par k))))

theorem burnsideF48d_sign (k : ℕ) : ((if 5 ≤ k then -1 else 1 : ℤ)) = 1 ∨
    ((if 5 ≤ k then -1 else 1 : ℤ)) = -1 := by
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem burnsideF48d_g_mem (hσ3 : ∀ c, σ (σ (σ c)) = c) (k : ℕ) :
    burnsideF48d_g σ ω k ∈ twistedGroup σ := by
  have hp : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hn : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  unfold burnsideF48d_g
  by_cases h0 : k = 0
  · rw [if_pos h0]
    exact twistedRootSubgroupD4_le_twistedGroup σ (isRoot_smul_single_G2 hp (ng 0))
      (xPar_two_mem σ hp (map_one σ))
  rw [if_neg h0]
  by_cases h1 : k = 1
  · rw [if_pos h1]
    exact twistedRootSubgroupD4_le_twistedGroup σ (isRoot_smul_single_G2 hn (ng 0))
      (xPar_two_mem σ hn (map_one σ))
  rw [if_neg h1]
  · exact twistedRootSubgroupD4_le_twistedGroup σ
      (isRoot_smul_single_G2 (burnsideF48d_sign k) (ng 1))
      (xOuter_mem σ (burnsideF48d_sign k) (hσ3 _))

@[expose] noncomputable def burnsideF48d_G8 : Subgroup (adjointGroup d4 K) :=
  Subgroup.closure (Set.range fun k : Fin 8 => burnsideF48d_g σ ω k)

theorem burnsideF48d_g_mem_G8 (k : Fin 8) : burnsideF48d_g σ ω k ∈ burnsideF48d_G8 σ ω :=
  Subgroup.subset_closure ⟨k, rfl⟩

theorem burnsideF48d_xOuter_add {s : ℤ} (hs : s = 1 ∨ s = -1) (c d : K) :
    xOuter s (c + d) (σ (c + d)) (σ (σ (c + d))) =
      xOuter s c (σ c) (σ (σ c)) * xOuter s d (σ d) (σ (σ d)) := by
  simp only [xOuter, map_add, xPar_add]
  have h01 := commute_xPar_outer (K := K) (a := nd 0) (b := nd 1) (by decide) (by decide)
    (by decide) hs hs
  have h03 := commute_xPar_outer (K := K) (a := nd 0) (b := nd 3) (by decide) (by decide)
    (by decide) hs hs
  have h13 := commute_xPar_outer (K := K) (a := nd 1) (b := nd 3) (by decide) (by decide)
    (by decide) hs hs
  set A := xPar (rootOperatorFamily d4) (s • Pi.single (nd 0) 1) c
  set A' := xPar (rootOperatorFamily d4) (s • Pi.single (nd 0) 1) d
  set B := xPar (rootOperatorFamily d4) (s • Pi.single (nd 1) 1) (σ c)
  set B' := xPar (rootOperatorFamily d4) (s • Pi.single (nd 1) 1) (σ d)
  set C := xPar (rootOperatorFamily d4) (s • Pi.single (nd 3) 1) (σ (σ c))
  set C' := xPar (rootOperatorFamily d4) (s • Pi.single (nd 3) 1) (σ (σ d))
  have hA'B : Commute A' B := (h01 d (σ c))
  have hA'C : Commute A' C := (h03 d (σ (σ c)))
  have hB'C : Commute B' C := (h13 (σ d) (σ (σ c)))
  calc A * A' * (B * B') * (C * C') = A * (A' * B) * B' * C * C' := by group
    _ = A * (B * A') * B' * C * C' := by rw [hA'B.eq]
    _ = A * B * (A' * (B' * C)) * C' := by group
    _ = A * B * (A' * (C * B')) * C' := by rw [hB'C.eq]
    _ = A * B * ((A' * C) * B') * C' := by group
    _ = A * B * ((C * A') * B') * C' := by rw [hA'C.eq]
    _ = A * B * C * (A' * B' * C') := by group

theorem burnsideF48d_xOuter_zero (s : ℤ) :
    xOuter s (0 : K) (σ 0) (σ (σ 0)) = 1 := by
  simp only [xOuter, map_zero, xPar_zero, mul_one]

theorem burnsideF48d_xOuter_nsmul {s : ℤ} (hs : s = 1 ∨ s = -1) (c : K) (n : ℕ) :
    xOuter s ((n : K) * c) (σ ((n : K) * c)) (σ (σ ((n : K) * c))) =
      xOuter s c (σ c) (σ (σ c)) ^ n := by
  induction n with
  | zero => simp only [Nat.cast_zero, zero_mul, pow_zero, burnsideF48d_xOuter_zero]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, burnsideF48d_xOuter_add σ hs, ih, pow_succ]

variable (hK : Nat.card K = 27) (hσ : ∀ c, σ c = c ^ 3) (hω : ω ^ 3 = ω + 1)

include hK hσ in
theorem burnsideF48d_sigma3 (c : K) : σ (σ (σ c)) = c := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  exact sigma_three_of_card (q := 3) (by rw [hK]; norm_num) hσ c

include hK in
theorem burnsideF48d_charP : CharP K 3 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact charP_of_card_eq_prime_pow (f := 3) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)

include hK hω in
theorem burnsideF48d_φ_surj (c : K) : ∃ n < 27, burnsideF48d_φ ω n = c := by
  classical
  haveI := burnsideF48d_charP hK
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Fintype K := Fintype.ofFinite K
  have hinj : Set.InjOn (burnsideF48d_φ ω) (Finset.range 27 : Set ℕ) := fun a ha b hb h =>
    burnsideF48d_φ_injOn ω hω (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h
  have hcard : ((Finset.range 27).image (burnsideF48d_φ ω)).card = Fintype.card K := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← Nat.card_eq_fintype_card, hK]
  have hall : (Finset.range 27).image (burnsideF48d_φ ω) = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  have hc : c ∈ (Finset.range 27).image (burnsideF48d_φ ω) := by rw [hall]; exact Finset.mem_univ c
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hc
  exact ⟨n, Finset.mem_range.1 hn, rfl⟩

include hK hσ hω in
theorem burnsideF48d_twistedGroup_le : twistedGroup σ ≤ burnsideF48d_G8 σ ω := by
  haveI := burnsideF48d_charP hK
  have hσ3 := burnsideF48d_sigma3 σ hK hσ
  set R : Subgroup (adjointGroup d4 K) := burnsideF48d_G8 σ ω with hR
  have hφ1 : burnsideF48d_φ ω 1 = 1 := burnsideF48d_φ_one ω
  have base_long : ∀ {s : ℤ}, (s = 1 ∨ s = -1) →
      twistedRootSubgroupD4 σ (s • Pi.single (ng 0) 1) ≤ R := by
    intro s hs g hg
    have hα₀ : IsRoot d4 (s • Pi.single (nd 2) 1) := isRoot_smul_single hs (nd 2)
    have hp : proj (s • Pi.single (nd 2) 1) = s • Pi.single (ng 0) 1 := by
      rw [proj_smul_single hs]
      rfl
    have hfix : rho (s • Pi.single (nd 2) 1) = s • Pi.single (nd 2) 1 := by
      rw [rho_smul_single, rhoPerm_two]
    obtain ⟨c, hc, rfl⟩ :=
      (mem_twistedRootSubgroupD4_iff_of_fixed (σ := σ) hσ3 hα₀ hp hfix g).1 hg
    have h3 : c ^ 3 = c := (hσ c).symm.trans hc
    have h33 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
    have hc3 : c = 0 ∨ c = 1 ∨ c = -1 := by
      have : c * (c - 1) * (c + 1) = 0 := by linear_combination h3
      rcases mul_eq_zero.1 this with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (sub_eq_zero.1 h))
      · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))
    have hgen : xPar (rootOperatorFamily d4) (s • Pi.single (nd 2) 1) 1 ∈ R := by
      rcases hs with rfl | rfl
      · have := burnsideF48d_g_mem_G8 σ ω ⟨0, by decide⟩
        simpa [burnsideF48d_g] using this
      · have := burnsideF48d_g_mem_G8 σ ω ⟨1, by decide⟩
        simpa [burnsideF48d_g] using this
    rcases hc3 with rfl | rfl | rfl
    · rw [xPar_zero]; exact R.one_mem
    · exact hgen
    · rw [← xPar_neg]; exact R.inv_mem hgen
  have base_short : ∀ {s : ℤ}, (s = 1 ∨ s = -1) →
      twistedRootSubgroupD4 σ (s • Pi.single (ng 1) 1) ≤ R := by
    intro s hs g hg
    have hα₀ : IsRoot d4 (s • Pi.single (nd 0) 1) := isRoot_smul_single hs (nd 0)
    have hp : proj (s • Pi.single (nd 0) 1) = s • Pi.single (ng 1) 1 := by
      rw [proj_smul_single hs]
      rfl
    have hne : rho (s • Pi.single (nd 0) 1) ≠ s • Pi.single (nd 0) 1 :=
      rho_smul_single_ne hs (by decide)
    obtain ⟨c, rfl⟩ :=
      (mem_twistedRootSubgroupD4_iff_of_orbit (σ := σ) hσ3 hα₀ hp hne g).1 hg
    rw [xOrbit_smul_single σ hs]
    have hgen : ∀ j < 3, xOuter s (burnsideF48d_φ ω (3 ^ j)) (σ (burnsideF48d_φ ω (3 ^ j)))
        (σ (σ (burnsideF48d_φ ω (3 ^ j)))) ∈ R := by
      intro j hj
      have hk : (if 5 ≤ (if s = 1 then 2 + j else 5 + j) then (-1 : ℤ) else 1) = s := by
        rcases hs with rfl | rfl
        · rw [if_pos rfl, if_neg (by omega)]
        · rw [if_neg (show ¬((-1 : ℤ) = 1) by decide), if_pos (by omega)]
      have hpar : burnsideF48d_par (if s = 1 then 2 + j else 5 + j) = 3 ^ j := by
        unfold burnsideF48d_par
        interval_cases j <;> rcases hs with rfl | rfl <;> simp
      have := burnsideF48d_g_mem_G8 σ ω ⟨if s = 1 then 2 + j else 5 + j, by split_ifs <;> omega⟩
      have e : burnsideF48d_g σ ω (if s = 1 then 2 + j else 5 + j) =
          xOuter s (burnsideF48d_φ ω (3 ^ j)) (σ (burnsideF48d_φ ω (3 ^ j)))
            (σ (σ (burnsideF48d_φ ω (3 ^ j)))) := by
        unfold burnsideF48d_g
        rw [if_neg (by split_ifs <;> omega), if_neg (by split_ifs <;> omega), hk, hpar]
      rw [← e]
      exact this
    obtain ⟨n, -, rfl⟩ := burnsideF48d_φ_surj ω hK hω c
    have hn : burnsideF48d_φ ω n = ((n % 3 : ℕ) : K) * burnsideF48d_φ ω (3 ^ 0) +
        ((n / 3 % 3 : ℕ) : K) * burnsideF48d_φ ω (3 ^ 1) +
        ((n / 9 % 3 : ℕ) : K) * burnsideF48d_φ ω (3 ^ 2) := by
      rw [pow_zero, pow_one, burnsideF48d_φ_one, burnsideF48d_φ_three,
        show (3 : ℕ) ^ 2 = 9 by norm_num]
      simp only [burnsideF48d_φ]
      norm_num
    rw [hn, burnsideF48d_xOuter_add σ hs, burnsideF48d_xOuter_add σ hs,
      burnsideF48d_xOuter_nsmul σ hs, burnsideF48d_xOuter_nsmul σ hs,
      burnsideF48d_xOuter_nsmul σ hs]
    exact R.mul_mem (R.mul_mem (R.pow_mem (hgen 0 (by norm_num)) _)
      (R.pow_mem (hgen 1 (by norm_num)) _)) (R.pow_mem (hgen 2 (by norm_num)) _)
  have base₁ : ∀ j : Fin (Tag.rank .G2), twistedRootSubgroupD4 σ (Pi.single j 1) ≤ R := by
    intro j
    match j with
    | ⟨0, _⟩ => have := base_long (s := 1) (Or.inl rfl); rwa [one_smul] at this
    | ⟨1, _⟩ => have := base_short (s := 1) (Or.inl rfl); rwa [one_smul] at this
  have base₂ : ∀ j : Fin (Tag.rank .G2), twistedRootSubgroupD4 σ (-Pi.single j 1) ≤ R := by
    intro j
    match j with
    | ⟨0, _⟩ => have := base_long (s := -1) (Or.inr rfl); rwa [neg_one_smul] at this
    | ⟨1, _⟩ => have := base_short (s := -1) (Or.inr rfl); rwa [neg_one_smul] at this
  have hn : ∀ i : Fin (Tag.rank .G2), ((nHat σ i : twistedGroup σ) : adjointGroup d4 K) ∈ R := by
    intro i
    have hle : CFSG.LieType.CurtisTits.rankOne (twistedRootGroup σ) i ≤
        R.subgroupOf (twistedGroup σ) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact base₁ i ((mem_twistedRootGroup σ).1 hx)
      · exact base₂ i ((mem_twistedRootGroup σ).1 hx)
    exact hle (nHat_mem_rankOne σ i)
  have key : ∀ β, IsRoot .G2 β → twistedRootSubgroupD4 σ β ≤ R := by
    intro β hβ
    induction hβ with
    | basis j => exact base₁ j
    | reflect i hβ' ih =>
      intro g hg
      have hgΓ : g ∈ twistedGroup σ := twistedRootSubgroupD4_le_twistedGroup σ (hβ'.reflect i) hg
      have hx : (⟨g, hgΓ⟩ : twistedGroup σ) ∈ twistedRootGroup σ (reflect .G2 i _) :=
        (mem_twistedRootGroup σ).2 hg
      have h1 := nHat_conj_mem σ i (hβ'.reflect i) hx
      rw [reflect_reflect] at h1
      have h2 := ih ((mem_twistedRootGroup σ).1 h1)
      have h3 : (g : adjointGroup d4 K) =
          ((nHat σ i : twistedGroup σ) : adjointGroup d4 K)⁻¹ *
            (((nHat σ i : twistedGroup σ) : adjointGroup d4 K) * g *
              ((nHat σ i : twistedGroup σ) : adjointGroup d4 K)⁻¹) *
            ((nHat σ i : twistedGroup σ) : adjointGroup d4 K) := by group
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hn i)) h2) (hn i)
  exact iSup₂_le fun β hβ => key β hβ

include hK hσ hω in
theorem burnsideF48d_twistedGroup_eq : twistedGroup σ = burnsideF48d_G8 σ ω := by
  refine le_antisymm (burnsideF48d_twistedGroup_le σ ω hK hσ hω) ?_
  rw [burnsideF48d_G8, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact burnsideF48d_g_mem σ ω (burnsideF48d_sigma3 σ hK hσ) k

include hK hσ hω in
theorem burnsideF48d_C0_eq :
    graphFixedRootGroup TwistTag.D4 K σ =
    Subgroup.closure (Set.range fun k : Fin 8 =>
      ((burnsideF48d_g σ ω k : adjointGroup d4 K) : ModGL d4 K)) := by
  haveI := burnsideF48d_charP hK
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  rw [← CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup
    hK2 (q := 3) (by norm_num) (by rw [hK]; norm_num) hσ,
    burnsideF48d_twistedGroup_eq σ ω hK hσ hω, burnsideF48d_G8, MonoidHom.map_closure,
    ← Set.range_comp]
  rfl

end Gen

section Val

variable {K : Type} [Field K] (σ : K →+* K) (ω : K)

theorem burnsideF48d_xPar_pos_val (i : Fin d4.rank) (c : K) :
    (((xPar (rootOperatorFamily d4) ((1 : ℤ) • Pi.single i 1) c : adjointGroup d4 K) :
      ModGL d4 K) : Module.End K (RootModule d4 K)) = xOp d4 K i c := by
  rw [one_smul, xPar_simple, eltElement_simpleRoot]
  rfl

theorem burnsideF48d_xPar_neg_val (i : Fin d4.rank) (c : K) :
    (((xPar (rootOperatorFamily d4) ((-1 : ℤ) • Pi.single i 1) c : adjointGroup d4 K) :
      ModGL d4 K) : Module.End K (RootModule d4 K)) = yOp d4 K i c := by
  have e : xPar (rootOperatorFamily d4) (-Pi.single i 1) c = yElement i c :=
    (xPar_neg_simple i c).trans (Subtype.ext ((rootOperatorFamily d4).eltUnit_neg_simple i c))
  rw [neg_one_smul, e]
  rfl

theorem burnsideF48d_xPar_val (k : ℕ) (i : Fin d4.rank) (c : K) :
    (((xPar (rootOperatorFamily d4) ((if 5 ≤ k then -1 else 1 : ℤ) • Pi.single i 1) c :
      adjointGroup d4 K) : ModGL d4 K) : Module.End K (RootModule d4 K)) =
      burnsideF48d_op K (decide (5 ≤ k)) i c := by
  by_cases h : 5 ≤ k
  · rw [if_pos h, burnsideF48d_xPar_neg_val, burnsideF48d_op,
      dif_pos (show (i : ℕ) < 4 from i.2), decide_eq_true h, if_pos rfl]
    rfl
  · rw [if_neg h, burnsideF48d_xPar_pos_val, burnsideF48d_op,
      dif_pos (show (i : ℕ) < 4 from i.2), decide_eq_false h]
    rfl

variable [CharP K 3] (hσ : ∀ c, σ c = c ^ 3) (hω : ω ^ 3 = ω + 1)

include hσ hω in
theorem burnsideF48d_g_val (k : ℕ) :
    (((burnsideF48d_g σ ω k : adjointGroup d4 K) : ModGL d4 K) :
      Module.End K (RootModule d4 K)) = burnsideF48d_genEnd ω k := by
  unfold burnsideF48d_g burnsideF48d_genEnd
  by_cases h0 : k = 0
  · subst h0
    rw [if_pos rfl, burnsideF48d_xPar_pos_val]
    simp only [burnsideF48d_genSpec, if_true, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, burnsideF48d_opEnd, burnsideF48d_φ_one]
    rw [burnsideF48d_op, dif_pos (by norm_num)]
    rfl
  by_cases h1 : k = 1
  · subst h1
    rw [if_neg (by norm_num), if_pos rfl, burnsideF48d_xPar_neg_val]
    simp only [burnsideF48d_genSpec, one_ne_zero, if_false, if_true, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, burnsideF48d_opEnd, burnsideF48d_φ_one]
    rw [burnsideF48d_op, dif_pos (by norm_num)]
    rfl
  rw [if_neg h0, if_neg h1]
  have hfrob : ∀ a, burnsideF48d_φ ω (burnsideF48d_frobC a) = σ (burnsideF48d_φ ω a) := by
    intro a
    rw [burnsideF48d_φ_frob ω hω, hσ]
  simp only [burnsideF48d_genSpec, h0, h1, if_false, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, burnsideF48d_opEnd, hfrob]
  simp only [xOuter, Subgroup.coe_mul, Units.val_mul, burnsideF48d_xPar_val]
  exact mul_assoc _ _ _

end Val

end CFSG.ASVolI
