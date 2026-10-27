module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QOrbit
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QCount
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QCanon
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QA2
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7TorusSwap
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaProjection
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameD6Word
public import CFSG.LocalAnalysis.StandardType.FS81.WeakClosureFusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup TwD7Q
open scoped Matrix

theorem isD6Root_neg {f : Coords 7} (h : IsD6Root f) : IsD6Root (-f) := by
  have hprod : ∏ i : Fin 6, (-f) i.succ = ∏ i : Fin 6, f i.succ := by
    simp only [Pi.neg_apply, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
    norm_num
  unfold IsD6Root at h ⊢
  rw [wt_neg, hprod]
  simpa only [Pi.neg_apply, ne_eq, neg_eq_zero] using h

private def tSign : Fin 7 → ZMod 3 := fun i => if i = 0 then -1 else 1

private theorem spMat_tSign_mul_self : spMat 1 tSign * spMat 1 tSign = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  have hs : tSign j * tSign j = 1 := by
    unfold tSign
    split_ifs <;> decide
  rw [← Matrix.mulVec_mulVec, spMat_mulVec_single, spMat_mulVec_single, Matrix.one_mulVec,
    Equiv.Perm.one_apply, Equiv.Perm.one_apply, mul_one, hs]

open TwD7Q in
theorem card_realized_normalizer_twD7Quot_lt {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    Nat.card ↥(B.twD7Quot.realized
        (normalizer (zpowers (B.twD7Quot.b 0) : Set (Q (B.b 0 * B.b 1))))) <
      Nat.card ↥(ggAutomizer ⊤ B.twD7Quot.span) := by
  classical
  rw [card_ggAutomizer_twD7Quot hstd hB hrec]
  obtain ⟨τ, -, hτβ, hτb⟩ := exists_tau_swap_of_std_twD7 hstd B hB hrec
  have hτβ' : τ ∈ cen (B.b 0 * B.b 1) := by rw [hB.2.1]; exact hτβ
  have hconj : ∀ i : Fin 8, pr _ ⟨τ, hτβ'⟩ * pr _ ⟨B.b i, B.b_mem_cen_twD7 i⟩ *
      (pr _ ⟨τ, hτβ'⟩)⁻¹ = pr _ ⟨B.b (Equiv.swap 0 1 i), B.b_mem_cen_twD7 _⟩ := by
    intro i
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hτb i)
  have hT : B.twD7Quot.Acts (pr _ ⟨τ, hτβ'⟩) (spMat 1 tSign) := by
    rw [B.twD7Quot.acts_spMat_iff]
    intro j
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ j
    · have h := hconj 0
      rw [Equiv.swap_apply_left, B.pr_b_zero_twD7Quot, B.pr_b_one_twD7Quot] at h
      have hs : (tSign 0).val = 2 := by decide
      have h3 : B.twD7Quot.b 0 ^ 3 = 1 := by
        rw [← B.twD7Quot.ord 0]
        exact pow_orderOf_eq_one _
      rw [h, Equiv.Perm.one_apply, hs]
      calc (B.twD7Quot.b 0)⁻¹ = (B.twD7Quot.b 0)⁻¹ * B.twD7Quot.b 0 ^ 3 := by
            rw [h3, mul_one]
        _ = B.twD7Quot.b 0 ^ 2 := by group
    · have h := hconj k.succ.succ
      rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one k),
        B.pr_b_succ_succ_twD7Quot] at h
      have hs : (tSign k.succ).val = 1 := by
        rw [show tSign k.succ = 1 from if_neg (Fin.succ_ne_zero k)]
        rfl
      rw [h, Equiv.Perm.one_apply, hs, pow_one]
  have hsub : B.twD7Quot.realized
      (normalizer (zpowers (B.twD7Quot.b 0) : Set (Q (B.b 0 * B.b 1)))) ⊆
      evenFix0 6 ∪ (fun X => spMat 1 tSign * X) '' evenFix0 6 := by
    rintro A ⟨q, hq, hqA⟩
    have hcol0 : q * B.twD7Quot.b 0 * q⁻¹ = B.twD7Quot.vec (A *ᵥ Pi.single 0 1) := by
      rw [← B.twD7Quot.vec_single 0, B.twD7Quot.acts_vec hqA]
    have hmem : B.twD7Quot.vec (A *ᵥ Pi.single 0 1) ∈
        zpowers (B.twD7Quot.vec (Pi.single 0 1)) := by
      rw [← hcol0, B.twD7Quot.vec_single]
      exact (mem_normalizer_iff.mp hq _).mp (mem_zpowers _)
    have hne : A *ᵥ Pi.single 0 1 ≠ 0 := by
      intro h0
      rw [h0, B.twD7Quot.vec_zero] at hcol0
      have h1 : B.twD7Quot.b 0 = 1 := by
        calc B.twD7Quot.b 0 = q⁻¹ * (q * B.twD7Quot.b 0 * q⁻¹) * q := by group
          _ = 1 := by rw [hcol0]; group
      have ho := B.twD7Quot.ord 0
      rw [h1, orderOf_one] at ho
      exact absurd ho (by norm_num)
    rcases B.twD7Quot.eq_or_eq_neg_of_vec_mem_zpowers hne hmem with h | h
    · exact Or.inl (mem_evenFix0_six_of_acts_twD7Quot hstd hB hrec hqA h)
    · refine Or.inr ⟨spMat 1 tSign * A, mem_evenFix0_six_of_acts_twD7Quot hstd hB hrec
        (B.twD7Quot.acts_mul hT hqA) ?_, ?_⟩
      · rw [← Matrix.mulVec_mulVec, h, ← Pi.single_neg, spMat_mulVec_single,
          Equiv.Perm.one_apply]
        congr 1
      · show spMat 1 tSign * (spMat 1 tSign * A) = A
        rw [← Matrix.mul_assoc, spMat_tSign_mul_self, Matrix.one_mul]
  have hfin : (evenFix0 6).Finite := Set.toFinite _
  calc Nat.card ↥(B.twD7Quot.realized
        (normalizer (zpowers (B.twD7Quot.b 0) : Set (Q (B.b 0 * B.b 1)))))
      ≤ Nat.card ↥(evenFix0 6 ∪ (fun X => spMat 1 tSign * X) '' evenFix0 6) :=
        Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card ↥(evenFix0 6) + Nat.card ↥((fun X => spMat 1 tSign * X) '' evenFix0 6) := by
        simp only [Nat.card_coe_set_eq]
        exact Set.ncard_union_le _ _
    _ ≤ Nat.card ↥(evenFix0 6) + Nat.card ↥(evenFix0 6) := by
        refine Nat.add_le_add_left ?_ _
        simp only [Nat.card_coe_set_eq]
        exact Set.ncard_image_le hfin
    _ ≤ 23040 + 23040 := Nat.add_le_add card_evenFix0_le card_evenFix0_le
    _ < 2903040 := by norm_num

open TwD7Q in
theorem nonempty_mulEquiv_om12_img_m0_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    Nonempty (↥(img (B.b 0 * B.b 1) (twD7M0 K B)) ≃* ↥D6M.Om12) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_img_m0_twD7 hstd hB hrec
  obtain ⟨e'⟩ := nonempty_mulEquiv_om12_m0_twD7 hstd hB hrec
  exact ⟨e.trans e'⟩

open TwD7Q in
theorem adapted_twD7Quot {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD7 B b₀) :
    Adapted B.twD7Quot (B.twD7Quot.b 0) (img (B.b 0 * B.b 1) (twD7M0 K B))
      B.twD7Quot.span := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
  exact twD7Quot_b_succ_mem_img_m0 hstd hB hrec j

open TwD7Q in
theorem stdLoc_twD7Quot {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD7 B b₀) :
    StdLoc (B.twD7Quot.b 0) (img (B.b 0 * B.b 1) (twD7M0 K B)) B.twD7Quot.span Row.D6 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_om12_img_m0_twD7 hstd hB hrec
  obtain ⟨-, hmark, hz, -⟩ := isRow_D6_of_mulEquiv_om12 e
  obtain ⟨hKC, hKn⟩ := img_m0_le_centralizer_twD7Quot hstd hB hrec
  refine ⟨trivial, ⟨⟨B.twD7Quot.ord 0, hKC, hKn, hz, hmark,
      isCyclic_of_le_centralizer_img_m0_twD7 hstd hB hrec, trivial, trivial⟩,
    isMaxElemAb3_twD7Quot hstd hB hrec, B.twD7Quot.b_mem_span 0, B.twD7Quot.card_span,
    le_rfl, ?_⟩, canonPosition_twD7Quot hstd hB hrec⟩
  rw [card_ggAutomizer_twD7Quot hstd hB hrec]
  show 2 ^ 7 * Nat.factorial 7 < 2903040
  norm_num [Nat.factorial]

section Certified


open TwD7Q in
theorem fus42_twD7Quot {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD7 B b₀) : Fus42 B.twD7Quot (B.twD7Quot.b 0) := by
  obtain ⟨-, ⟨hA, hEmax, -, hEcard, -, -⟩, hrow, -, hsup, hEKmax, hEKcard, -⟩ :=
    stdLoc_twD7Quot hstd hB hrec
  obtain ⟨hb₀, hKC, hKn, hKz, hKmark, hA2, -, -⟩ := hA
  have hOut := fs81_row_out_not_dvd_three hKmark hKz
  obtain ⟨hrank, hconj⟩ := rowElemAb3_D6 hrow hKz inf_le_right hEKmax.2.1 hEKcard
  exact fus42_of_facts hb₀ hKC hKn hKz hOut hA2 hEmax hEcard hsup hrank hconj rfl
    (card_realized_normalizer_twD7Quot_lt hstd hB hrec)

open TwD7Q in
theorem recOutD6_twD7Quot {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD7 B b₀) : RecOutD6 B.twD7Quot (B.twD7Quot.b 0) := by
  have hcard := card_ggAutomizer_twD7Quot hstd hB hrec
  have hfus := fus42_twD7Quot hstd hB hrec
  have h0 : ¬ IsD6Root 0 := by decide
  refine ⟨hcard, fun e _ => ⟨fun ⟨g, hg⟩ => ?_, fun hroot => ?_⟩⟩
  · have hgl : g * B.twD7Quot.b 0 * g⁻¹ ∈ B.twD7Quot.line e := by
      rw [← hg]
      exact mem_zpowers _
    have hgE : g * B.twD7Quot.b 0 * g⁻¹ ∈ B.twD7Quot.span :=
      zpowers_le.mpr (B.twD7Quot.vec_mem_span e) hgl
    obtain ⟨x, hxN, hx⟩ := hfus.2 g hgE
    obtain ⟨f, hf⟩ := B.twD7Quot.exists_vec_eq (hx ▸ hgE)
    have hroot : IsD6Root f :=
      (exists_normalizer_conj_twD7Quot_iff hstd hB hrec hcard f).mp ⟨x, hxN, hf.symm⟩
    have hf0 : f ≠ 0 := fun h => h0 (h ▸ hroot)
    have hfe : B.twD7Quot.vec f ∈ zpowers (B.twD7Quot.vec e) := by
      rw [hf, ← hx]
      exact hgl
    have he : IsD6Root e := by
      rcases B.twD7Quot.eq_or_eq_neg_of_vec_mem_zpowers hf0 hfe with h | h
      · exact h ▸ hroot
      · have h' : e = -f := by rw [h, neg_neg]
        exact h' ▸ isD6Root_neg hroot
    exact he
  · obtain ⟨n, -, hn⟩ := (exists_normalizer_conj_twD7Quot_iff hstd hB hrec hcard e).mpr hroot
    exact ⟨n, by rw [hn]; rfl⟩

open TwD7Q CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley E7Frame in
theorem exists_twD7BetaHost_projection_of_std {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    ∃ π : twD7BetaHost b₀ K E B →* adjointGroup .E7 (ZMod 2),
      Function.Surjective π ∧
      (∃ R₁ : Subgroup G, R₁ ≤ centralizer ({b₀} : Set G) ∧
        (R₁.subgroupOf (centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R₁ ∧
        π.ker ≤ R₁.subgroupOf (twD7BetaHost b₀ K E B) ⊔
          (zpowers (b₀ * B.b 1)).subgroupOf (twD7BetaHost b₀ K E B)) ∧
      (∀ ha : b₀⁻¹ * B.b 1 ∈ twD7BetaHost b₀ K E B,
        ((π ⟨b₀⁻¹ * B.b 1, ha⟩ : adjointGroup .E7 (ZMod 2)) : ModGL .E7 (ZMod 2)) ∈ Jn 0) :=
  exists_twD7BetaHost_projection_of_quot hstd hB hrec (stdLoc_twD7Quot hstd hB hrec)
    (adapted_twD7Quot hstd hB hrec) (recOutD6_twD7Quot hstd hB hrec)
    (fun n hn e h => (exists_normalizer_conj_twD7Quot_iff hstd hB hrec
      (card_ggAutomizer_twD7Quot hstd hB hrec) e).mp ⟨n, hn, h⟩)
    (fun hx h1 h2 h5 h6 => exists_conj_mem_jn_zero_of_commute hx h1 h2 h5 h6)

end Certified

end CFSG.StandardType.FrameRoute.FS81

end
