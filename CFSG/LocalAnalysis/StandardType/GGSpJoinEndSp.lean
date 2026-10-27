module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinCentralizerLam
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.Symplectic CFSG.Open CFSG.StandardType.SpJoin
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix
open CFSG.LieType.Universal.Symplectic.SpExtras TauCeti.GLSymplecticFin

variable {F : Type} [Field F] [CharP F 2]

theorem spEnd_eq_one_of_mul_self_of_commute {g t : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) (hc : t * g = g * t) (ht : t * t = 1) :
    t = 1 := by
  let T : Matrix (Fin 2) (Fin 2) F := (t : Matrix (Fin 2) (Fin 2) F)
  let G : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F)
  have htrG : G 0 0 + G 1 1 ≠ 0 := by
    rw [Matrix.trace_fin_two] at htr
    simpa only [G] using htr
  have htM : T * T = 1 := by
    have := congrArg (fun x : SpecialLinearGroup (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) ht
    simpa only [T, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using this
  have hcM : T * G = G * T := by
    have := congrArg (fun x : SpecialLinearGroup (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) hc
    simpa only [T, G, Matrix.SpecialLinearGroup.coe_mul] using this
  have h00 : T 0 0 * T 0 0 + T 0 1 * T 1 0 = 1 := by
    have := congrFun (congrFun htM 0) 0
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] using this
  have h11 : T 1 0 * T 0 1 + T 1 1 * T 1 1 = 1 := by
    have := congrFun (congrFun htM 1) 1
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] using this
  have hsq : T 0 0 ^ 2 = T 1 1 ^ 2 := by
    linear_combination h00 - h11
  have hsum : T 0 0 + T 1 1 = 0 := by
    have h : (T 0 0 + T 1 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, hsq]
      exact CharTwo.add_self_eq_zero (T 1 1 ^ 2)
    rw [pow_two] at h
    exact mul_self_eq_zero.mp h
  have hp_eq_s : T 0 0 = T 1 1 := by
    have h := add_eq_zero_iff_eq_neg.mp hsum
    simpa only [CharTwo.neg_eq] using h
  have hc01 : T 0 0 * G 0 1 + T 0 1 * G 1 1 = G 0 0 * T 0 1 + G 0 1 * T 1 1 := by
    have := congrFun (congrFun hcM 0) 1
    simpa only [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hqG : T 0 1 * G 1 1 = G 0 0 * T 0 1 := by
    linear_combination hc01 - G 0 1 * hp_eq_s
  have hq0 : T 0 1 * (G 0 0 + G 1 1) = 0 := by
    have h : T 0 1 * G 1 1 - G 0 0 * T 0 1 = 0 := sub_eq_zero.mpr hqG
    rw [CharTwo.sub_eq_add, mul_comm (G 0 0) (T 0 1), ← mul_add,
      add_comm (G 1 1) (G 0 0)] at h
    exact h
  have hq : T 0 1 = 0 := by
    rcases mul_eq_zero.mp hq0 with h | h
    · exact h
    · exact absurd h htrG
  have hc10 : T 1 0 * G 0 0 + T 1 1 * G 1 0 = G 1 0 * T 0 0 + G 1 1 * T 1 0 := by
    have := congrFun (congrFun hcM 1) 0
    simpa only [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hrG : T 1 0 * G 0 0 = G 1 1 * T 1 0 := by
    linear_combination hc10 + G 1 0 * hp_eq_s
  have hr0 : T 1 0 * (G 0 0 + G 1 1) = 0 := by
    have h : T 1 0 * G 0 0 - G 1 1 * T 1 0 = 0 := sub_eq_zero.mpr hrG
    rw [CharTwo.sub_eq_add, mul_comm (G 1 1) (T 1 0), ← mul_add] at h
    exact h
  have hr : T 1 0 = 0 := by
    rcases mul_eq_zero.mp hr0 with h | h
    · exact h
    · exact absurd h htrG
  have hp2 : T 0 0 * T 0 0 = 1 := by
    have h := h00
    rw [hq, hr, mul_zero, add_zero] at h
    exact h
  have hp : T 0 0 = 1 := by
    have h : (T 0 0 + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq]
      simp only [pow_two, hp2, one_pow, one_mul]
      exact CharTwo.add_self_eq_zero 1
    rw [pow_two] at h
    have h' : T 0 0 + 1 = 0 := mul_self_eq_zero.mp h
    have h'' := add_eq_zero_iff_eq_neg.mp h'
    simpa only [CharTwo.neg_eq] using h''
  have hps : T 1 1 = 1 := by rw [← hp_eq_s]; exact hp
  exact Matrix.SpecialLinearGroup.ext t 1 (fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp [T, hp, hps, hq, hr, Matrix.SpecialLinearGroup.coe_one])

theorem spEnd_exists_lam_zero_of_commute_levi {m : ℕ} (hm : 1 ≤ m) {u : StatedSp (m + 1) F}
    (hu : ∀ h : StatedSp m F, u * spLeviBlock m F h = spLeviBlock m F h * u) :
    ∃ g : SpecialLinearGroup (Fin 2) F, u = lam (0 : Fin (m + 1)) g := by
  have hmem : u ∈ Subgroup.normalizer (CFSG.StandardType.spLeviBlock m F).range := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨h, ?_⟩
      rw [hu h]
      group
    · rintro ⟨h, hx⟩
      refine ⟨h, ?_⟩
      calc CFSG.StandardType.spLeviBlock m F h
          = u⁻¹ * (u * CFSG.StandardType.spLeviBlock m F h) := by group
        _ = u⁻¹ * (CFSG.StandardType.spLeviBlock m F h * u) := by rw [hu h]
        _ = u⁻¹ * CFSG.StandardType.spLeviBlock m F h * u := by group
        _ = x := by rw [hx]; group
  obtain ⟨g, h, hu_eq⟩ :=
    CFSG.StandardType.SpJoin.exists_lam_mul_levi_of_mem_normalizer hmem
  have hcenter : h ∈ Subgroup.center (StatedSp m F) := by
    rw [Subgroup.mem_center_iff]
    intro h'
    apply CFSG.StandardType.spLeviBlock_injective (n := m) (F := F)
    rw [map_mul, map_mul]
    have hβ : CFSG.StandardType.spLeviBlock m F h =
        (lam (0 : Fin (m + 1)) g)⁻¹ * u := by
      rw [hu_eq]
      group
    rw [hβ]
    have hc : Commute ((lam (0 : Fin (m + 1)) g)⁻¹)
        (CFSG.StandardType.spLeviBlock m F h') :=
      (CFSG.StandardType.SpJoin.lam_zero_commute_spLeviBlock (m := m) g h').inv_left
    calc CFSG.StandardType.spLeviBlock m F h' * ((lam (0 : Fin (m + 1)) g)⁻¹ * u)
        = (CFSG.StandardType.spLeviBlock m F h' * (lam (0 : Fin (m + 1)) g)⁻¹) * u := by
          rw [mul_assoc]
      _ = ((lam (0 : Fin (m + 1)) g)⁻¹ * CFSG.StandardType.spLeviBlock m F h') * u := by
          rw [← hc.eq]
      _ = (lam (0 : Fin (m + 1)) g)⁻¹ * (CFSG.StandardType.spLeviBlock m F h' * u) := by
          rw [mul_assoc]
      _ = (lam (0 : Fin (m + 1)) g)⁻¹ * (u * CFSG.StandardType.spLeviBlock m F h') := by
          rw [hu h']
      _ = ((lam (0 : Fin (m + 1)) g)⁻¹ * u) * CFSG.StandardType.spLeviBlock m F h' := by
          rw [mul_assoc]
  have hbot : Subgroup.center (StatedSp m F) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  have h1 : h = 1 := by
    rw [hbot, Subgroup.mem_bot] at hcenter
    exact hcenter
  exact ⟨g, by rw [hu_eq, h1, map_one, mul_one]⟩

theorem spEnd_exists_lam_lam_of_commute {k : ℕ} (hk : 1 ≤ k) {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {B : StatedSp (k + 2 + 1) F}
    (hg : B * lam (0 : Fin (k + 2 + 1)) g = lam (0 : Fin (k + 2 + 1)) g * B)
    (hM : ∀ h : StatedSp (k + 1) F,
      B * spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) =
        spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) * B) :
    ∃ s t : SpecialLinearGroup (Fin 2) F, s * g = g * s ∧
      B = lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t := by
  obtain ⟨s₀, B', hB, hsg⟩ :=
    CFSG.StandardType.SpJoin.exists_lam_zero_mul_levi_of_commute (m := k + 2) htr hg
  have hB' : ∀ h : StatedSp (k + 1) F,
      B' * spLeviBlock (k + 1) F h = spLeviBlock (k + 1) F h * B' := by
    intro h
    apply CFSG.StandardType.spLeviBlock_injective (n := k + 2) (F := F)
    rw [map_mul, map_mul]
    have hβB' : CFSG.StandardType.spLeviBlock (k + 2) F B' =
        (lam (0 : Fin (k + 2 + 1)) s₀)⁻¹ * B := by
      rw [hB]
      group
    rw [hβB']
    have hc : Commute ((lam (0 : Fin (k + 2 + 1)) s₀)⁻¹)
        (CFSG.StandardType.spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h)) :=
      (CFSG.StandardType.SpJoin.lam_zero_commute_spLeviBlock (m := k + 2) s₀
        (spLeviBlock (k + 1) F h)).inv_left
    calc ((lam (0 : Fin (k + 2 + 1)) s₀)⁻¹ * B) *
            CFSG.StandardType.spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h)
        = (lam (0 : Fin (k + 2 + 1)) s₀)⁻¹ *
            (B * CFSG.StandardType.spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h)) := by
          rw [mul_assoc]
      _ = (lam (0 : Fin (k + 2 + 1)) s₀)⁻¹ *
            (CFSG.StandardType.spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) * B) := by
          rw [hM h]
      _ = ((lam (0 : Fin (k + 2 + 1)) s₀)⁻¹ *
            CFSG.StandardType.spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h)) * B := by
          rw [mul_assoc]
      _ = (CFSG.StandardType.spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) *
            (lam (0 : Fin (k + 2 + 1)) s₀)⁻¹) * B := by
          rw [hc.eq]
      _ = CFSG.StandardType.spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) *
            ((lam (0 : Fin (k + 2 + 1)) s₀)⁻¹ * B) := by
          rw [mul_assoc]
  obtain ⟨t, ht⟩ :=
    spEnd_exists_lam_zero_of_commute_levi (m := k + 1) (by omega) (u := B') hB'
  refine ⟨s₀, t, hsg, ?_⟩
  rw [hB, ht, CFSG.StandardType.SpJoin.spLeviBlock_lam (m := k + 2) (i := (0 : Fin (k + 2))) t,
    Fin.succ_zero_eq_one]

private theorem spEnd_isSupp_iff_basic {n : ℕ} {A : Set (Fin n ⊕ Fin n)}
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp A M ↔
      CFSG.ClassicalInvolution.Models.SymplecticPairs.IsSupp A M := by
  constructor
  · intro h x y hxy
    exact h x y (not_and_or.mp hxy)
  · intro h x y hxy
    exact h x y (not_and_or.mpr hxy)

private theorem spEnd_isSupp_mat_elt {n : ℕ} {P : Set (Fin n ⊕ Fin n)}
    (r : RootSubgroupIndex n)
    (h1 : (pos1 r).1 ∈ P ∧ (pos1 r).2 ∈ P) (h2 : (pos2 r).1 ∈ P ∧ (pos2 r).2 ∈ P) (c : F) :
    CFSG.ClassicalInvolution.Models.SymplecticPairs.IsSupp P (mat n F (elt r c)) := by
  intro a b hab
  rw [mat_elt, Matrix.add_apply, Matrix.smul_apply]
  have hE : E F r a b = 0 := by
    by_contra h
    rcases eq_pos_of_E_ne_zero r a b h with h' | h'
    · apply hab
      rw [show a = (pos1 r).1 from congrArg Prod.fst h',
        show b = (pos1 r).2 from congrArg Prod.snd h']
      exact h1
    · apply hab
      rw [show a = (pos2 r).1 from congrArg Prod.fst h',
        show b = (pos2 r).2 from congrArg Prod.snd h']
      exact h2
  rw [hE, smul_zero, add_zero]

private theorem spEnd_isSupp_spEmbedMat {m n : ℕ} {σ : Fin m → Fin n}
    (hσ : Function.Injective σ)
    {M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F} {B : Set (Fin m ⊕ Fin m)}
    (hM : CFSG.ClassicalInvolution.Models.SymplecticPairs.IsSupp B M) :
    CFSG.ClassicalInvolution.Models.SymplecticPairs.IsSupp (Sum.map σ σ '' B)
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.spEmbedMat σ M) := by
  intro a b hab
  by_cases h : a ∈ Set.range (Sum.map σ σ) ∧ b ∈ Set.range (Sum.map σ σ)
  · obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := h
    rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.spEmbedMat_apply_image hσ]
    have hnot : ¬(a' ∈ B ∧ b' ∈ B) := by
      rintro ⟨ha, hb⟩
      exact hab ⟨⟨a', ha, rfl⟩, ⟨b', hb, rfl⟩⟩
    rw [hM a' b' hnot]
    simp only [Matrix.one_apply]
    by_cases h' : a' = b'
    · subst h'; simp
    · have hne : ¬(Sum.map σ σ a' = Sum.map σ σ b') :=
        fun h => h' ((Sum.map_injective.2 ⟨hσ, hσ⟩) h)
      simp [h', hne]
  · exact CFSG.ClassicalInvolution.Models.SymplecticPairs.spEmbedMat_apply_of_not_mem M h

private theorem spEnd_isSupp_spLeviBlock_two {k : ℕ} (h : StatedSp (k + 1) F) :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp
      (Set.range (Sum.map (fun i : Fin (k + 1) => i.succ.succ)
        (fun i : Fin (k + 1) => i.succ.succ) :
        Fin (k + 1) ⊕ Fin (k + 1) → Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1)))
      (mat (k + 2 + 1) F (spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h))) := by
  rw [spEnd_isSupp_iff_basic]
  have h1 : CFSG.ClassicalInvolution.Models.SymplecticPairs.IsSupp
      (Set.range (Sum.map Fin.succ Fin.succ : Fin (k + 1) ⊕ Fin (k + 1) → Fin (k + 2) ⊕ Fin (k + 2)))
      (mat (k + 2) F (spLeviBlock (k + 1) F h)) :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.isSupp_spEmbed (K := F)
      (Fin.succ_injective (k + 1)) h
  have h2 := spEnd_isSupp_spEmbedMat (σ := (Fin.succ : Fin (k + 2) → Fin (k + 2 + 1)))
    (Fin.succ_injective (k + 2)) h1
  have hrange : (Sum.map (Fin.succ : Fin (k + 2) → Fin (k + 2 + 1)) Fin.succ '' Set.range
      (Sum.map (Fin.succ : Fin (k + 1) → Fin (k + 2)) Fin.succ)) =
      Set.range (Sum.map (fun i : Fin (k + 1) => i.succ.succ)
        (fun i : Fin (k + 1) => i.succ.succ)) := by
    rw [← Set.range_comp]
    congr 1
    funext x
    rcases x with i | i <;> rfl
  rw [← hrange]
  exact h2

private theorem spEnd_disjoint_weyl_support (k : ℕ)
    (hk : (0 : Fin (k + 2 + 1)).val + 1 < k + 2 + 1) :
    Disjoint (Set.range (Sum.map (fun i : Fin (k + 1) => i.succ.succ)
        (fun i : Fin (k + 1) => i.succ.succ) :
        Fin (k + 1) ⊕ Fin (k + 1) → Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1)))
      ({Sum.inl (0 : Fin (k + 2 + 1)),
        Sum.inl ⟨(0 : Fin (k + 2 + 1)).val + 1, hk⟩,
        Sum.inr (0 : Fin (k + 2 + 1)),
        Sum.inr ⟨(0 : Fin (k + 2 + 1)).val + 1, hk⟩} :
        Set (Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1))) := by
  rw [Set.disjoint_left]
  rintro x ⟨y, rfl⟩ hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases y with i | i
  · rcases hx with h | h | h | h
    · exact Fin.succ_ne_zero i.succ (Sum.inl_injective h)
    · have hv : (i.succ.succ).val =
          (⟨(0 : Fin (k + 2 + 1)).val + 1, hk⟩ : Fin (k + 2 + 1)).val :=
        Fin.ext_iff.mp (Sum.inl_injective h)
      simp only [Fin.val_succ, Fin.val_zero] at hv
      omega
    · exact Sum.inl_ne_inr h
    · exact Sum.inl_ne_inr h
  · rcases hx with h | h | h | h
    · exact Sum.inr_ne_inl h
    · exact Sum.inr_ne_inl h
    · exact Fin.succ_ne_zero i.succ (Sum.inr_injective h)
    · have hv : (i.succ.succ).val =
          (⟨(0 : Fin (k + 2 + 1)).val + 1, hk⟩ : Fin (k + 2 + 1)).val :=
        Fin.ext_iff.mp (Sum.inr_injective h)
      simp only [Fin.val_succ, Fin.val_zero] at hv
      omega

theorem spEnd_commute_weylRep_zero_levi_two {k : ℕ} (h : StatedSp (k + 1) F) :
    weylRep (k + 2 + 1) F 0 * spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) =
      spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) * weylRep (k + 2 + 1) F 0 := by
  apply statedSp_commute
  have hk : (0 : Fin (k + 2 + 1)).val + 1 < k + 2 + 1 := by
    simp only [Fin.val_zero]; omega
  have hweyl : CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp
      ({Sum.inl (0 : Fin (k + 2 + 1)),
        Sum.inl ⟨(0 : Fin (k + 2 + 1)).val + 1, hk⟩,
        Sum.inr (0 : Fin (k + 2 + 1)),
        Sum.inr ⟨(0 : Fin (k + 2 + 1)).val + 1, hk⟩} :
        Set (Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1)))
      (mat (k + 2 + 1) F (weylRep (k + 2 + 1) F 0)) := by
    rw [spEnd_isSupp_iff_basic]
    rw [CFSG.StandardType.weylRep_eq_elt_of_lt (k := (0 : Fin (k + 2 + 1))) hk]
    rw [map_mul, map_mul]
    refine ((spEnd_isSupp_mat_elt _ ⟨?_, ?_⟩ ⟨?_, ?_⟩ (1 : F)).mul
      (spEnd_isSupp_mat_elt _ ⟨?_, ?_⟩ ⟨?_, ?_⟩ (-1 : F))).mul
      (spEnd_isSupp_mat_elt _ ⟨?_, ?_⟩ ⟨?_, ?_⟩ (1 : F))
    all_goals simp [pos1, pos2]
  have hlevi : CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp
      (Set.range (Sum.map (fun i : Fin (k + 1) => i.succ.succ)
        (fun i : Fin (k + 1) => i.succ.succ) :
        Fin (k + 1) ⊕ Fin (k + 1) → Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1)))
      (mat (k + 2 + 1) F (spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h))) :=
    spEnd_isSupp_spLeviBlock_two h
  have hdisj : Disjoint (Set.range (Sum.map (fun i : Fin (k + 1) => i.succ.succ)
        (fun i : Fin (k + 1) => i.succ.succ) :
        Fin (k + 1) ⊕ Fin (k + 1) → Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1)))
      ({Sum.inl (0 : Fin (k + 2 + 1)),
        Sum.inl ⟨(0 : Fin (k + 2 + 1)).val + 1, hk⟩,
        Sum.inr (0 : Fin (k + 2 + 1)),
        Sum.inr ⟨(0 : Fin (k + 2 + 1)).val + 1, hk⟩} :
        Set (Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1))) :=
    spEnd_disjoint_weyl_support k hk
  exact hweyl.commute hlevi hdisj.symm

end CFSG.StandardType
