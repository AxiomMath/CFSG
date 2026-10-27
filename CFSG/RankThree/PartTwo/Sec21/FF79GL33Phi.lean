module

public import CFSG.RankThree.PartTwo.Sec21.FF79GL33Dict
public import CFSG.RankThree.PartTwo.Sec21.FF79GL33Lat
public import CFSG.RankThree.PartTwo.Sec21.FF79KFacts13

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.GL33

@[expose] def GL33At (X : Subgroup (GL (Fin 3) (ZMod 3))) (v w₁ w₂ : Fin 3 → ZMod 3) : Prop :=
  (∃ τ ∈ X, act33 τ v = v ∧ act33 τ w₁ = -w₁ ∧ act33 τ w₂ = -w₂) →
    Nat.card {g : GL (Fin 3) (ZMod 3) // g ∈ X ∧ act33 g v = v} = 8 →
    (∃ g ∈ X, ∃ h ∈ X, act33 g v = v ∧ act33 h v = v ∧ g * h ≠ h * g) →
    (∀ g ∈ X, (act33 g v = v ∨ act33 g v = -v) →
      (∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂}, act33 g w ∈ Submodule.span (ZMod 3) {w₁, w₂}) ∧
      ∃ d ∈ X, act33 d v = v ∧
        ((∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂}, act33 g w = act33 d w) ∨
          ∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂}, act33 g w = -act33 d w)) →
    (∃ g ∈ X, act33 g v ≠ v ∧ act33 g v ≠ -v) →
    ((∀ g ∈ X, ∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂},
        act33 g w ∈ Submodule.span (ZMod 3) {w₁, w₂}) ∧
      ∀ u : Fin 3 → ZMod 3, u ∉ Submodule.span (ZMod 3) {w₁, w₂} →
        ∃ g ∈ X, act33 g v = u ∨ act33 g v = -u) ∨
    (∃ u₁ ∈ Submodule.span (ZMod 3) {w₁, w₂}, ∃ u₂ ∈ Submodule.span (ZMod 3) {w₁, w₂},
      LinearIndependent (ZMod 3) ![v, u₁, u₂] ∧
      (∀ g ∈ X, ∀ x ∈ ({v, -v, u₁, -u₁, u₂, -u₂} : Set (Fin 3 → ZMod 3)),
        act33 g x ∈ ({v, -v, u₁, -u₁, u₂, -u₂} : Set (Fin 3 → ZMod 3))) ∧
      (∃ g ∈ X, act33 g v = -v ∧ act33 g u₁ = u₁ ∧ act33 g u₂ = u₂) ∧
      (∃ g ∈ X, act33 g v = u₁ ∧ act33 g u₁ = v ∧ act33 g u₂ = u₂) ∧
      (∃ g ∈ X, act33 g v = u₁ ∧ act33 g u₁ = u₂ ∧ act33 g u₂ = v))

theorem FF79KGL33_iff : FF79KGL33 ↔
    ∀ (X : Subgroup (GL (Fin 3) (ZMod 3))) (v w₁ w₂ : Fin 3 → ZMod 3),
    LinearIndependent (ZMod 3) ![v, w₁, w₂] → GL33At X v w₁ w₂ := Iff.rfl

structure TabSpec (T : Array ℕ) : Prop where
  lt : TabLt T
  act_spec : ∀ r c, r < 27 → c < N → decV (act T c r) = Matrix.vecMul (decV r) (dec c)
  mul_spec : ∀ a b, b < N → dec (mulc T a b) = dec a * dec b

theorem tabSpec_vmTab : TabSpec (vmTab ()) :=
  ⟨tabLt_vmTab, fun _ _ hr hc => decV_act hr hc, fun _ _ hb => dec_mulc hb⟩

theorem TabSpec.act_lt {T : Array ℕ} (hT : TabSpec T) (r c : ℕ) : act T c r < 27 :=
  hT.lt _

section Spec

variable {T : Array ℕ} (hT : TabSpec T) {X : Subgroup (GL (Fin 3) (ZMod 3))} {S : Array ℕ}

include hT in
theorem actG {g : GL (Fin 3) (ZMod 3)} {c r : ℕ} (hc : c < N) (hg : dec c = (g : Mat))
    (hr : r < 27) : act33 g (decV r) = decV (act T c r) := by
  rw [hT.act_spec r c hr hc, hg]

include hT in
theorem actG_iff {g : GL (Fin 3) (ZMod 3)} {c r r' : ℕ} (hc : c < N) (hg : dec c = (g : Mat))
    (hr : r < 27) (hr' : r' < 27) : act33 g (decV r) = decV r' ↔ act T c r = r' := by
  rw [actG hT hc hg hr]
  constructor
  · intro h; exact decV_inj (hT.act_lt r c) hr' h
  · intro h; rw [h]

theorem code_enc (g : GL (Fin 3) (ZMod 3)) : enc (g : Mat) < N ∧ dec (enc (g : Mat)) = (g : Mat) :=
  ⟨enc_lt _, dec_enc _⟩

theorem mem_stabArr {c : ℕ} : c ∈ stabArr T S ↔ c ∈ S ∧ act T c 1 = 1 := by
  unfold stabArr
  rw [Array.mem_filter]
  simp

include hT in
theorem card_stab (hS1 : ∀ c ∈ S, c < N ∧ ∃ g ∈ X, dec c = (g : Mat))
    (hS2 : ∀ g ∈ X, enc (g : Mat) ∈ S) (hS3 : S.toList.Nodup) :
    Nat.card {g : GL (Fin 3) (ZMod 3) // g ∈ X ∧ act33 g e0 = e0} = (stabArr T S).size := by
  let f : {g : GL (Fin 3) (ZMod 3) // g ∈ X ∧ act33 g e0 = e0} → ℕ := fun g => enc (g.1 : Mat)
  have hf : Function.Injective f := by
    intro g h hgh
    apply Subtype.ext
    apply Units.ext
    have := congrArg dec hgh
    simpa [f, dec_enc] using this
  have hrange : Set.range f = ((stabArr T S).toList.toFinset : Set ℕ) := by
    ext c
    simp only [Set.mem_range, Finset.mem_coe, List.mem_toFinset, Array.mem_toList_iff,
      mem_stabArr]
    constructor
    · rintro ⟨⟨g, hgX, hge⟩, rfl⟩
      have ⟨hc, hg⟩ := code_enc g
      refine ⟨hS2 g hgX, ?_⟩
      rw [← decV_one] at hge
      exact (actG_iff hT hc hg (by norm_num) (by norm_num)).mp (by simpa [decV_one] using hge)
    · rintro ⟨hcS, hc1⟩
      obtain ⟨hc, g, hgX, hg⟩ := hS1 c hcS
      refine ⟨⟨g, hgX, ?_⟩, ?_⟩
      · have := (actG_iff hT hc hg (by norm_num : 1 < 27) (by norm_num : 1 < 27)).mpr hc1
        simpa [decV_one] using this
      · simp only [f]; rw [← hg]; exact enc_dec hc
  have h1 : Nat.card {g : GL (Fin 3) (ZMod 3) // g ∈ X ∧ act33 g e0 = e0} =
      Nat.card (Set.range f) := (Nat.card_range_of_injective hf).symm
  rw [h1, hrange, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [List.toFinset_card_of_nodup]
  · simp
  · exact (List.Nodup.filter _ hS3 : _) |> fun h => by
      unfold stabArr
      rw [Array.toList_filter]
      exact h

include hT in
theorem act_fix_iff {g : GL (Fin 3) (ZMod 3)} {c : ℕ} (hc : c < N) (hg : dec c = (g : Mat)) :
    act33 g e0 = e0 ↔ act T c 1 = 1 := by
  rw [← decV_one]; exact actG_iff hT hc hg (by norm_num) (by norm_num)

include hT in
theorem act_neg_iff {g : GL (Fin 3) (ZMod 3)} {c : ℕ} (hc : c < N) (hg : dec c = (g : Mat)) :
    act33 g e0 = -e0 ↔ act T c 1 = 2 := by
  rw [← decV_two, ← decV_one]; exact actG_iff hT hc hg (by norm_num) (by norm_num)

include hT in
theorem act_e1 {g : GL (Fin 3) (ZMod 3)} {c : ℕ} (hc : c < N) (hg : dec c = (g : Mat)) :
    act33 g e1 = decV (act T c 3) := by
  have := actG hT hc hg (r := 3) (by norm_num)
  rwa [decV_three] at this

include hT in
theorem act_e2 {g : GL (Fin 3) (ZMod 3)} {c : ℕ} (hc : c < N) (hg : dec c = (g : Mat)) :
    act33 g e2 = decV (act T c 9) := by
  have := actG hT hc hg (r := 9) (by norm_num)
  rwa [decV_nine] at this

include hT in
theorem phiHyp_of (hS1 : ∀ c ∈ S, c < N ∧ ∃ g ∈ X, dec c = (g : Mat))
    (hS2 : ∀ g ∈ X, enc (g : Mat) ∈ S) (hS3 : S.toList.Nodup)
    (hcard : Nat.card {g : GL (Fin 3) (ZMod 3) // g ∈ X ∧ act33 g e0 = e0} = 8)
    (hnon : ∃ g ∈ X, ∃ h ∈ X, act33 g e0 = e0 ∧ act33 h e0 = e0 ∧ g * h ≠ h * g)
    (hD : ∀ g ∈ X, (act33 g e0 = e0 ∨ act33 g e0 = -e0) →
      (∀ w ∈ Submodule.span (ZMod 3) {e1, e2}, act33 g w ∈ Submodule.span (ZMod 3) {e1, e2}) ∧
      ∃ d ∈ X, act33 d e0 = e0 ∧
        ((∀ w ∈ Submodule.span (ZMod 3) {e1, e2}, act33 g w = act33 d w) ∨
          ∀ w ∈ Submodule.span (ZMod 3) {e1, e2}, act33 g w = -act33 d w))
    (hE : ∃ g ∈ X, act33 g e0 ≠ e0 ∧ act33 g e0 ≠ -e0) : phiHyp T S = true := by
  have e1mem : e1 ∈ Submodule.span (ZMod 3) {e1, e2} := Submodule.subset_span (by simp)
  have e2mem : e2 ∈ Submodule.span (ZMod 3) {e1, e2} := Submodule.subset_span (by simp)
  unfold phiHyp hypB hypC hypD hypE
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [card_stab hT hS1 hS2 hS3] at hcard
    exact beq_iff_eq.mpr hcard
  · obtain ⟨g, hgX, h, hhX, hg0, hh0, hgh⟩ := hnon
    obtain ⟨hcg, hdg⟩ := code_enc g
    obtain ⟨hch, hdh⟩ := code_enc h
    rw [Array.any_eq_true']
    refine ⟨enc (g : Mat), mem_stabArr.mpr ⟨hS2 g hgX, (act_fix_iff hT hcg hdg).mp hg0⟩, ?_⟩
    rw [Array.any_eq_true']
    refine ⟨enc (h : Mat), mem_stabArr.mpr ⟨hS2 h hhX, (act_fix_iff hT hch hdh).mp hh0⟩, ?_⟩
    rw [bne_iff_ne]
    intro heq
    apply hgh
    apply Units.ext
    have := congrArg dec heq
    rw [hT.mul_spec _ _ hch, hT.mul_spec _ _ hcg, hdg, hdh] at this
    simpa using this
  · rw [Array.all_eq_true_iff_forall_mem]
    intro c hcS
    obtain ⟨hc, g, hgX, hg⟩ := hS1 c hcS
    by_cases hcase : act T c 1 = 1 ∨ act T c 1 = 2
    · have hcase' : act33 g e0 = e0 ∨ act33 g e0 = -e0 := by
        rcases hcase with h | h
        · exact Or.inl ((act_fix_iff hT hc hg).mpr h)
        · exact Or.inr ((act_neg_iff hT hc hg).mpr h)
      obtain ⟨hW, d, hdX, hd0, hrows⟩ := hD g hgX hcase'
      have hW1 := hW e1 e1mem
      have hW2 := hW e2 e2mem
      rw [act_e1 hT hc hg, mem_span_e12, decV_coord0_eq_zero] at hW1
      rw [act_e2 hT hc hg, mem_span_e12, decV_coord0_eq_zero] at hW2
      obtain ⟨hcd, hdd⟩ := code_enc d
      have hdS : enc (d : Mat) ∈ stabArr T S :=
        mem_stabArr.mpr ⟨hS2 d hdX, (act_fix_iff hT hcd hdd).mp hd0⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq]
      right
      refine ⟨⟨hW1, hW2⟩, ?_⟩
      rw [Array.any_eq_true']
      refine ⟨enc (d : Mat), hdS, ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      rcases hrows with hr | hr
      · left
        have h1 := hr e1 e1mem
        have h2 := hr e2 e2mem
        rw [act_e1 hT hc hg, act_e1 hT hcd hdd] at h1
        rw [act_e2 hT hc hg, act_e2 hT hcd hdd] at h2
        exact ⟨decV_inj (hT.act_lt _ _) (hT.act_lt _ _) h1,
          decV_inj (hT.act_lt _ _) (hT.act_lt _ _) h2⟩
      · right
        have h1 := hr e1 e1mem
        have h2 := hr e2 e2mem
        rw [act_e1 hT hc hg, act_e1 hT hcd hdd, ← decV_negV] at h1
        rw [act_e2 hT hc hg, act_e2 hT hcd hdd, ← decV_negV] at h2
        exact ⟨decV_inj (hT.act_lt _ _) (negV_lt _) h1, decV_inj (hT.act_lt _ _) (negV_lt _) h2⟩
    · simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq]
      left
      simpa [Bool.or_eq_true, beq_iff_eq] using hcase
  · obtain ⟨g, hgX, h1, h2⟩ := hE
    obtain ⟨hcg, hdg⟩ := code_enc g
    rw [Array.any_eq_true']
    refine ⟨enc (g : Mat), hS2 g hgX, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne]
    exact ⟨fun h => h1 ((act_fix_iff hT hcg hdg).mpr h),
      fun h => h2 ((act_neg_iff hT hcg hdg).mpr h)⟩

theorem vecMul_coord0 (M : Mat) (w : Vec) :
    Matrix.vecMul w M 0 = w 0 * M 0 0 + w 1 * M 1 0 + w 2 * M 2 0 := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem vecMul_e1 (M : Mat) (j : Fin 3) : Matrix.vecMul e1 M j = M 1 j := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, e1]

theorem vecMul_e2 (M : Mat) (j : Fin 3) : Matrix.vecMul e2 M j = M 2 j := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, e2]

include hT in
theorem concl1_of (hS1 : ∀ c ∈ S, c < N ∧ ∃ g ∈ X, dec c = (g : Mat))
    (hS2 : ∀ g ∈ X, enc (g : Mat) ∈ S) (h : phiC1 T S = true) :
    (∀ g ∈ X, ∀ w ∈ Submodule.span (ZMod 3) {e1, e2},
        act33 g w ∈ Submodule.span (ZMod 3) {e1, e2}) ∧
      ∀ u : Fin 3 → ZMod 3, u ∉ Submodule.span (ZMod 3) {e1, e2} →
        ∃ g ∈ X, act33 g e0 = u ∨ act33 g e0 = -u := by
  unfold phiC1 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro g hgX w hw
    obtain ⟨hc, hg⟩ := code_enc g
    rw [Array.all_eq_true_iff_forall_mem] at h1
    have h1' := h1 _ (hS2 g hgX)
    simp only [Bool.and_eq_true, beq_iff_eq] at h1'
    have e1z := act_e1 hT hc hg
    have e2z := act_e2 hT hc hg
    rw [mem_span_e12] at hw ⊢
    have c1 : (g : Mat) 1 0 = 0 := by
      have := vecMul_e1 (g : Mat) 0
      rw [← this]
      change act33 g e1 0 = 0
      rw [e1z, decV_coord0_eq_zero]; exact h1'.1
    have c2 : (g : Mat) 2 0 = 0 := by
      have := vecMul_e2 (g : Mat) 0
      rw [← this]
      change act33 g e2 0 = 0
      rw [e2z, decV_coord0_eq_zero]; exact h1'.2
    change Matrix.vecMul w (g : Mat) 0 = 0
    rw [vecMul_coord0, hw, c1, c2]; ring
  · intro u hu
    rw [mem_span_e12] at hu
    have hr : encV u < 27 := encV_lt u
    have hdu : decV (encV u) = u := decV_encV u
    have hmod : encV u % 3 ≠ 0 := by
      intro h0
      apply hu
      rw [← hdu]
      exact decV_coord0_eq_zero.mpr h0
    rw [List.all_eq_true] at h2
    have h2' := h2 (encV u) (List.mem_range.mpr hr)
    simp only [Bool.or_eq_true, beq_iff_eq] at h2'
    rcases h2' with h2' | h2'
    · exact absurd h2' hmod
    · rw [Array.any_eq_true'] at h2'
      obtain ⟨c, hcS, hc⟩ := h2'
      obtain ⟨hcN, g, hgX, hg⟩ := hS1 c hcS
      refine ⟨g, hgX, ?_⟩
      have key := actG hT hcN hg (r := 1) (by norm_num)
      rw [decV_one] at key
      simp only [Bool.or_eq_true, beq_iff_eq] at hc
      rcases hc with hc | hc
      · left; rw [key, hc, hdu]
      · right; rw [key, hc, decV_negV, hdu]

theorem li_of_raw {r₁ r₂ : ℕ} (h₁ : r₁ % 3 = 0) (h₂ : r₂ % 3 = 0)
    (h : ((r₁ / 3) % 3 * ((r₂ / 9) % 3) + 2 * ((r₁ / 9) % 3 * ((r₂ / 3) % 3))) % 3 ≠ 0) :
    LinearIndependent (ZMod 3) ![e0, decV r₁, decV r₂] := by
  have hdet : (Matrix.of ![e0, decV r₁, decV r₂]).det =
      (((r₁ / 3) % 3 * ((r₂ / 9) % 3) + 2 * ((r₁ / 9) % 3 * ((r₂ / 3) % 3)) : ℕ) : ZMod 3) := by
    rw [Matrix.det_fin_three]
    simp [decV, e0, h₁, h₂]
    have h2 : (2 : ZMod 3) = -1 := by decide
    rw [h2]
    generalize ((r₁ / 3 : ℕ) : ZMod 3) = a
    generalize ((r₂ / 9 : ℕ) : ZMod 3) = b
    generalize ((r₁ / 9 : ℕ) : ZMod 3) = c
    generalize ((r₂ / 3 : ℕ) : ZMod 3) = d
    revert a b c d
    decide
  have hne : (Matrix.of ![e0, decV r₁, decV r₂]).det ≠ 0 := by
    rw [hdet]
    intro h0
    have := congrArg ZMod.val h0
    rw [ZMod.val_natCast, ZMod.val_zero] at this
    exact h this
  exact Matrix.linearIndependent_rows_of_det_ne_zero hne

include hT in
theorem concl2_of (hS1 : ∀ c ∈ S, c < N ∧ ∃ g ∈ X, dec c = (g : Mat))
    (hS2 : ∀ g ∈ X, enc (g : Mat) ∈ S) (h : phiC2 T S = true) :
    ∃ u₁ ∈ Submodule.span (ZMod 3) {e1, e2}, ∃ u₂ ∈ Submodule.span (ZMod 3) {e1, e2},
      LinearIndependent (ZMod 3) ![e0, u₁, u₂] ∧
      (∀ g ∈ X, ∀ x ∈ ({e0, -e0, u₁, -u₁, u₂, -u₂} : Set (Fin 3 → ZMod 3)),
        act33 g x ∈ ({e0, -e0, u₁, -u₁, u₂, -u₂} : Set (Fin 3 → ZMod 3))) ∧
      (∃ g ∈ X, act33 g e0 = -e0 ∧ act33 g u₁ = u₁ ∧ act33 g u₂ = u₂) ∧
      (∃ g ∈ X, act33 g e0 = u₁ ∧ act33 g u₁ = e0 ∧ act33 g u₂ = u₂) ∧
      (∃ g ∈ X, act33 g e0 = u₁ ∧ act33 g u₁ = u₂ ∧ act33 g u₂ = e0) := by
  unfold phiC2 at h
  obtain ⟨u1, hu1r, hu1⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hu1
  obtain ⟨hu1m, hany2⟩ := hu1
  obtain ⟨u2, hu2r, hu2⟩ := List.any_eq_true.mp hany2
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hu2
  obtain ⟨⟨⟨⟨⟨hu2m, hli⟩, hcl⟩, hex1⟩, hex2⟩, hex3⟩ := hu2
  have hu1l : u1 < 27 := List.mem_range.mp hu1r
  have hu2l : u2 < 27 := List.mem_range.mp hu2r
  refine ⟨decV u1, mem_span_e12.mpr (decV_coord0_eq_zero.mpr hu1m), decV u2,
    mem_span_e12.mpr (decV_coord0_eq_zero.mpr hu2m), li_of_raw hu1m hu2m hli, ?_, ?_, ?_, ?_⟩
  · intro g hgX x hx
    obtain ⟨hc, hg⟩ := code_enc g
    rw [Array.all_eq_true_iff_forall_mem] at hcl
    have hcl' := hcl _ (hS2 g hgX)
    have key : ∀ x' : ℕ, x' < 27 → x' ∈ [1, 2, u1, negV u1, u2, negV u2] →
        act33 g (decV x') ∈ ({e0, -e0, decV u1, -decV u1, decV u2, -decV u2} :
          Set (Fin 3 → ZMod 3)) := by
      intro x' hx' hmem
      rw [actG hT hc hg hx']
      have := (List.all_eq_true.mp hcl') x' hmem
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases this with ((((h | h) | h) | h) | h) | h
      · left; rw [h, decV_one]
      · right; left; rw [h, decV_two]
      · right; right; left; rw [h]
      · right; right; right; left; rw [h, decV_negV]
      · right; right; right; right; left; rw [h]
      · right; right; right; right; right; rw [h, decV_negV]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx | hx | hx
    · subst hx
      have := key 1 (by norm_num) (by simp)
      rwa [decV_one] at this
    · subst hx
      have := key 2 (by norm_num) (by simp)
      rwa [decV_two] at this
    · subst hx; exact key u1 hu1l (by simp)
    · subst hx
      have := key (negV u1) (negV_lt _) (by simp)
      rwa [decV_negV] at this
    · subst hx; exact key u2 hu2l (by simp)
    · subst hx
      have := key (negV u2) (negV_lt _) (by simp)
      rwa [decV_negV] at this
  · rw [Array.any_eq_true'] at hex1
    obtain ⟨c, hcS, hc⟩ := hex1
    obtain ⟨hcN, g, hgX, hg⟩ := hS1 c hcS
    refine ⟨g, hgX, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have k0 := actG hT hcN hg (r := 1) (by norm_num)
    rw [decV_one] at k0
    refine ⟨?_, ?_, ?_⟩
    · rw [k0, h1, decV_two]
    · rw [actG hT hcN hg hu1l, h2]
    · rw [actG hT hcN hg hu2l, h3]
  · rw [Array.any_eq_true'] at hex2
    obtain ⟨c, hcS, hc⟩ := hex2
    obtain ⟨hcN, g, hgX, hg⟩ := hS1 c hcS
    refine ⟨g, hgX, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have k0 := actG hT hcN hg (r := 1) (by norm_num)
    rw [decV_one] at k0
    refine ⟨?_, ?_, ?_⟩
    · rw [k0, h1]
    · rw [actG hT hcN hg hu1l, h2, decV_one]
    · rw [actG hT hcN hg hu2l, h3]
  · rw [Array.any_eq_true'] at hex3
    obtain ⟨c, hcS, hc⟩ := hex3
    obtain ⟨hcN, g, hgX, hg⟩ := hS1 c hcS
    refine ⟨g, hgX, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have k0 := actG hT hcN hg (r := 1) (by norm_num)
    rw [decV_one] at k0
    refine ⟨?_, ?_, ?_⟩
    · rw [k0, h1]
    · rw [actG hT hcN hg hu1l, h2]
    · rw [actG hT hcN hg hu2l, h3, decV_one]

include hT in
theorem phi_spec (hS1 : ∀ c ∈ S, c < N ∧ ∃ g ∈ X, dec c = (g : Mat))
    (hS2 : ∀ g ∈ X, enc (g : Mat) ∈ S) (hS3 : S.toList.Nodup) (h : phi T S = true) :
    GL33At X e0 e1 e2 := by
  intro _ hcard hnon hD hE
  unfold phi at h
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with (h | h) | h
  · exfalso
    have := phiHyp_of hT hS1 hS2 hS3 hcard hnon hD hE
    rw [this] at h
    exact absurd h (by simp)
  · exact Or.inl (concl1_of hT hS1 hS2 h)
  · exact Or.inr (concl2_of hT hS1 hS2 h)

end Spec

end CFSG.RankThree.PartTwo.Sec21.FF79.GL33

end
