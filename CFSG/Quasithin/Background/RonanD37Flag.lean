module

public import CFSG.Quasithin.Background.RonanD37Rank8
public import CFSG.Quasithin.Background.SmithD37Flag

public section

namespace CFSG.Quasithin.RonanD37

open CFSG.Quasithin CFSG.Quasithin.SmithD37
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.Layer
open scoped Matrix

section Rank

theorem card_le_of_normalizer_psl {Q : Type} [CommGroup Q] [Finite Q] (hQ : ∀ q : Q, q * q = 1)
    {L : Subgroup (MulAut Q)} (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup Q) ⊤) {n : ℕ}
    (hL : IsPSL 2 2 n ↥L) {E : Subgroup (MulAut Q)}
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut Q))) (hE : IsElemAbelian2 E) :
    Nat.card E ≤ 2 ^ n := by
  classical
  obtain ⟨F', _, _, hn2, hF', ⟨θL⟩⟩ := exists_sl2_of_isPSL hL
  have : CharP F' 2 := charP_two_of_card_eq hF'
  have hF'' : Nat.card F' = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF']
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := Actor.exists_binModel_of_binary hQ
  by_cases hEL : E ≤ L
  · exact (card_le_of_le θL hEL hE).trans hF''.le
  · obtain ⟨s, hs, hns, hle⟩ := card_le_of_not_le hirr (by omega) hF'' θL θ hEN hE hEL
    exact hle.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

end Rank

section Flag

variable {U : Type} [CommGroup U] [Finite U] {L₁ L₂ : Subgroup (MulAut U)}
  {F : Type} [Field F] [Fintype F] [CharP F 2] {d : ℕ}

omit [Fintype F] [CharP F 2] in
private theorem top_ne_bot_d (hd : 0 < d) : (⊤ : Submodule F (Fin d → F)) ≠ ⊥ := by
  intro h
  have h1 := congrArg (fun S : Submodule F (Fin d → F) => Module.finrank F S) h
  simp only [finrank_top, finrank_bot, Module.finrank_fin_fun] at h1
  omega

theorem card_fixV_flag_mul (Mm : MatModel L₁ L₂ F d) {P : Subgroup (MulAut U)}
    (hP2 : IsPGroup 2 ↥P) (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁) (m M : ℕ)
    (hc : ∀ (Y' Y : Submodule F (Fin d → F)) (D : FacStep Y' Y)
      (hP : P ≤ stabSub (rowSub Mm Y)) (hP' : P ≤ stabSub (rowSub Mm Y')),
      Nat.card ↥(fixV (facAct Mm D hP hP').range) * m ≤ M) :
    ∀ (k : ℕ) (Y : Submodule F (Fin d → F)), Module.finrank F Y = k →
      IsInvBy P (rowSub Mm Y) → Nat.card ↥(rowSub Mm Y ⊓ fixV P) * m ^ k ≤ M ^ k := by
  intro k
  induction k with
  | zero =>
    intro Y hY _
    rw [Submodule.finrank_eq_zero.mp hY, rowSub_bot, bot_inf_eq, Subgroup.card_bot]
    simp
  | succ k ih =>
    intro Y hY hinv
    have hY0 : Y ≠ ⊥ := fun h => by
      rw [h, finrank_bot] at hY
      omega
    obtain ⟨Y', hY'le, hrank, hinv'⟩ := exists_hyperplane_inv Mm hP2 hPN hinv hY0
    obtain ⟨D⟩ := exists_facStep hY'le hrank
    have hP := le_stabSub_of_isInvBy hinv
    have hP' := le_stabSub_of_isInvBy hinv'
    have h1 := card_fixV_le_facAct Mm D hP hP'
    have h2 := hc Y' Y D hP hP'
    have h4 := ih Y' (by omega) hinv'
    calc Nat.card ↥(rowSub Mm Y ⊓ fixV P) * m ^ (k + 1)
        ≤ (Nat.card ↥(rowSub Mm Y' ⊓ fixV P) *
            Nat.card ↥(fixV (facAct Mm D hP hP').range)) * m ^ (k + 1) :=
          Nat.mul_le_mul_right _ h1
      _ = (Nat.card ↥(rowSub Mm Y' ⊓ fixV P) * m ^ k) *
            (Nat.card ↥(fixV (facAct Mm D hP hP').range) * m) := by ring
      _ ≤ M ^ k * M := Nat.mul_le_mul h4 h2
      _ = M ^ (k + 1) := by ring

theorem card_fixV_range_mul_two_le (Mm : MatModel L₁ L₂ F d) {Y' Y : Submodule F (Fin d → F)}
    (D : FacStep Y' Y) {P : Subgroup (MulAut U)} (hP : P ≤ stabSub (rowSub Mm Y))
    (hP' : P ≤ stabSub (rowSub Mm Y')) (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁)
    (h2 : IsPGroup 2 ↥P) (hnc : ∃ a ∈ P, ∃ l ∈ L₁, a * l ≠ l * a) :
    Nat.card ↥(fixV (facAct Mm D hP hP').range) * 2 ≤ Nat.card F ^ d := by
  obtain ⟨a, ha, l, hl, hal⟩ := hnc
  have hne : facAct Mm D hP hP' ⟨a, ha⟩ ≠ 1 := fun h =>
    hal ((facAct_eq_one_iff Mm D hP hP' hPN h2 ⟨a, ha⟩).mp h l hl)
  have hfix : fixV (facAct Mm D hP hP').range ≠ ⊤ := by
    intro htop
    apply hne
    refine MulEquiv.ext fun x => ?_
    have hx : x ∈ fixV (facAct Mm D hP hP').range := htop ▸ Subgroup.mem_top x
    exact hx _ ⟨⟨a, ha⟩, rfl⟩
  have hidx : (fixV (facAct Mm D hP hP').range).index ≠ 1 := fun h =>
    hfix (Subgroup.index_eq_one.mp h)
  have hpos : (fixV (facAct Mm D hP hP').range).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul := (fixV (facAct Mm D hP hP').range).card_mul_index
  rw [natCard_natMod] at hmul
  calc Nat.card ↥(fixV (facAct Mm D hP hP').range) * 2
      ≤ Nat.card ↥(fixV (facAct Mm D hP hP').range) *
          (fixV (facAct Mm D hP hP').range).index :=
        Nat.mul_le_mul_left _ (by omega)
    _ = Nat.card F ^ d := hmul

theorem exists_fixV_eq_rowSub (Mm : MatModel L₁ L₂ F d) {K : Subgroup (MulAut U)}
    (hK : ∀ c ∈ K, ∀ l ∈ L₁, c * l = l * c) : ∃ Y₀, fixV K = rowSub Mm Y₀ := by
  refine exists_eq_rowSub Mm ?_
  intro l hl u hu c hc
  have h : c (l u) = l (c u) := by
    rw [← MulAut.mul_apply, hK c hc l hl, MulAut.mul_apply]
  rw [h, hu c hc]

theorem finrank_lt_of_ne_bot (Mm : MatModel L₁ L₂ F d) {K : Subgroup (MulAut U)} (hK : K ≠ ⊥)
    {Y₀ : Submodule F (Fin d → F)} (hY : fixV K = rowSub Mm Y₀) : Module.finrank F Y₀ < d := by
  have hle : Module.finrank F Y₀ ≤ d := by
    have := Submodule.finrank_le Y₀
    rwa [Module.finrank_fin_fun] at this
  refine lt_of_le_of_ne hle fun heq => hK ?_
  have htop : Y₀ = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [heq, Module.finrank_fin_fun])
  rw [htop, rowSub_top] at hY
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun u => ?_
  have hu : u ∈ fixV K := hY ▸ Subgroup.mem_top u
  exact hu c hc

theorem isInvBy_fixV_of_comm {B K : Subgroup (MulAut U)}
    (hcomm : ∀ b ∈ B, ∀ c ∈ K, b * c = c * b) : IsInvBy B (fixV K) := by
  intro b hb u hu c hc
  have h : c (b u) = b (c u) := by
    rw [← MulAut.mul_apply, ← hcomm b hb c hc, MulAut.mul_apply]
  rw [h, hu c hc]

theorem card_le_mul_cent_psl (Mm : MatModel L₁ L₂ F d) (hd : 0 < d) (hs : IsSimpleGroup ↥L₁)
    (hnc : ∃ a b : ↥L₁, a * b ≠ b * a) (hSQ : SQTKGroup ↥L₁) {n : ℕ} (hL : IsPSL 2 2 n ↥L₁)
    {P : Subgroup (MulAut U)} (hE : IsElemAbelian2 P)
    (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁) :
    Nat.card P ≤ 2 ^ n * Nat.card ↥(P ⊓ Subgroup.centralizer (L₁ : Set (MulAut U))) := by
  obtain ⟨y, -, hy, hinv⟩ := exists_line_inv Mm hE.isPGroup hPN
    (Y := ⊤) (by rw [rowSub_top]; exact fun _ _ _ _ => Subgroup.mem_top _)
    (top_ne_bot_d hd)
  have hP := le_stabSub_of_isInvBy hinv
  have hP' := le_stabSub_rowSub_bot Mm P
  have hmul := card_range_facAct_mul Mm (facStepLine hy) hP hP' hPN hE.isPGroup
  have hB2 := isPGroup_range_facAct Mm (facStepLine hy) hP hP' hE.isPGroup
  have hBN := conj_mem_natSub_of_mem_range Mm (facStepLine hy) hP hP' hPN
  have hirr := (b4Hyp_natSub Mm hd hs hnc hSQ hB2 hBN).2.2.2
  have hQ : ∀ q : natMod F d, q * q = 1 := fun q => by rw [← pow_two]; exact natMod_sq q
  have hle := card_le_of_normalizer_psl hQ hirr (isPSL_transfer (natSubEquiv Mm).symm hL)
    (range_facAct_le_normalizer Mm (facStepLine hy) hP hP' hPN)
    (isElemAbelian2_range_facAct Mm (facStepLine hy) hP hP' hE)
  rw [← hmul]
  exact Nat.mul_le_mul_right _ hle

theorem card_le_mul_cent_eight (Mm : MatModel L₁ L₂ F d) (hd : 0 < d)
    (h8 : Nat.card F ^ d = 8) {P : Subgroup (MulAut U)} (hE : IsElemAbelian2 P)
    (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁) :
    Nat.card P ≤ 4 * Nat.card ↥(P ⊓ Subgroup.centralizer (L₁ : Set (MulAut U))) := by
  obtain ⟨y, -, hy, hinv⟩ := exists_line_inv Mm hE.isPGroup hPN
    (Y := ⊤) (by rw [rowSub_top]; exact fun _ _ _ _ => Subgroup.mem_top _)
    (top_ne_bot_d hd)
  have hP := le_stabSub_of_isInvBy hinv
  have hP' := le_stabSub_rowSub_bot Mm P
  have hmul := card_range_facAct_mul Mm (facStepLine hy) hP hP' hPN hE.isPGroup
  have hle := card_le_four_of_card_eight natMod_sq (by rw [natCard_natMod, h8])
    (isElemAbelian2_range_facAct Mm (facStepLine hy) hP hP' hE)
  rw [← hmul]
  exact Nat.mul_le_mul_right _ hle

end Flag

end CFSG.Quasithin.RonanD37
