module

public import CFSG.Quasithin.EmptyFaithful.SBd4Five
public import CFSG.Quasithin.EmptyFaithful.S153D35
public import CFSG.Quasithin.EmptyFaithful.A38c7Rank
public import CFSG.Quasithin.EmptyFaithful.A38c7Quot
public import CFSG.Quasithin.EmptyFaithful.A38c7Phi

public section

namespace CFSG.Quasithin.A38c7

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417

theorem card_autOn_dvd {G : Type} [Group G] [Finite G] (L V : Subgroup G) :
    Nat.card ↥(autOn L V) ∣ Nat.card ↥L :=
  CFSG.Quasithin.AutOn.card_autOn_dvd _ _

theorem conj_mem_thetaOf {G : Type} [Group G] {I : Subgroup G} {g : G} (hg : g ∈ I) {x : G}
    (hx : x ∈ thetaOf I) : g * x * g⁻¹ ∈ thetaOf I := by
  unfold thetaOf at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine Subgroup.subset_closure ⟨I.mul_mem (I.mul_mem hg hy.1) (I.inv_mem hg), ?_⟩
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    rw [← hy.2]
    exact this
  | one => simp
  | mul a b _ _ ha hb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem concl15317_two {G : Type} [Group G] [Finite G] {T V₁ Yp I L : Subgroup G}
    (c17 : Concl15317 T V₁ Yp I L) (hq : IsLnTwoQuot L 5) : Yp ≤ thetaOf I ∧ thetaOf I = L := by
  rcases c17 with ⟨h1, -⟩ | ⟨-, hY, hθ⟩ | ⟨-, n, F, hF, hFin, hn, hcard, ⟨e⟩⟩
  · have := two_le_pRank_of_quot5 hq
    omega
  · exact ⟨hY, hθ⟩
  · exfalso
    apply not_dvd_27_card_of_quot5 hq
    have h27 : 27 ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
      dvd_27_card_statedSL_three hn (by rw [Nat.card_eq_fintype_card]; exact hcard)
    rw [← Nat.card_congr e.toEquiv] at h27
    exact h27.trans (card_autOn_dvd L _)

theorem l5Parabolics_holds (h36 : Input15336One) : L5Parabolics := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c c17 hq
  obtain ⟨hYθ, hθ⟩ := concl15317_two c17 hq
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hF : Facts15311 T M V₁ Yp I := c.facts
  have hS : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  obtain ⟨hLc, -, -, -, -, -⟩ := c.conc
  have hLI : L ≤ I := le_of_mem_cComp (S153D.mem_cComp_of_mem_cComp_thompsonJ hLc)
  have hYL : Yp ≤ L := hθ ▸ hYθ
  have hIL : ∀ g ∈ I, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    rw [← hθ] at hl ⊢
    exact conj_mem_thetaOf hg hl
  have hIN : I ≤ Subgroup.normalizer (L : Set G) := FLc.le_normalizer_of_conj_mem hIL
  have hSL : ∀ s ∈ Sgp153 T V₁, ∀ l ∈ L, s * l * s⁻¹ ∈ L := fun s hs l hl => hIL s (hS.1 hs) l hl
  have hB : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L := A4.isSylowTwoOf_inf_normal hS hLI hIN
  have hSM : Sgp153 T V₁ ≤ M := (inf_le_left : Sgp153 T V₁ ≤ T).trans hh.hyp.T_le
  have hSN : ∀ s ∈ Sgp153 T V₁, ∀ y ∈ Yp, s * y * s⁻¹ ∈ Yp := by
    intro s hs y hy
    have hs' : s ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by
      rw [hF.norm_eq]
      exact ⟨hSM hs, hS.1 hs⟩
    exact (Subgroup.mem_normalizer_iff.1 hs'.2 y).1 hy
  have hE : IsElemAbelianOfRank 3 2 (OTwoQuot Yp) := by
    rcases hF.struct_Yp with h | h
    · exact h
    · exfalso
      have h27 : Nat.card (OTwoQuot Yp) = 3 ^ 3 := h.2.1
      apply not_dvd_27_card_of_quot5 hq
      have h1 : Nat.card (OTwoQuot Yp) ∣ Nat.card Yp := Subgroup.card_quotient_dvd_card _
      have h2 : Nat.card Yp ∣ Nat.card L := Subgroup.card_dvd_of_le hYL
      rw [h27] at h1
      exact (by norm_num : (27 : ℕ) = 3 ^ 3) ▸ h1.trans h2
  obtain ⟨φ, hφ, hker⟩ := h36 G T Mc M V₁ V₂ Yp t hh c.ctx.rank I c.ctx.inH
  obtain ⟨Y₁, Y₂, hY₁Y, hY₂Y, hYY, hY₁S, hY₂S, hY₁c, hY₂c⟩ :=
    exists_two_factors hS.2.1 hSN hE φ hφ hker
  obtain ⟨P₁, P₂, ⟨hB₁, hP₁L, hP₁ne, hY₁P₁, hY₂P₁, hP₁S⟩, ⟨hB₂, hP₂L, hP₂ne, hY₁P₂, hY₂P₂, hP₂S⟩,
      hP⟩ := transfer5 hSL hB hq (hY₁Y.trans hYL) hY₁S hY₁c (hY₂Y.trans hYL) hY₂S hY₂c
  have fin : ∀ P : Subgroup G, Sgp153 T V₁ ⊓ L ≤ P → P ≤ L → P ≠ L → Yp ≤ P →
      (∀ s ∈ Sgp153 T V₁, ∀ p ∈ P, s * p * s⁻¹ ∈ P) →
      Yp ⊔ Sgp153 T V₁ ≤ P ⊔ Sgp153 T V₁ ∧ P ⊔ Sgp153 T V₁ ≤ I ∧ P ⊔ Sgp153 T V₁ ≠ I := by
    intro P hBP hPL hPne hYP hPS
    refine ⟨sup_le_sup_right hYP _, sup_le (hPL.trans hLI) hS.1,
      fun heq => hPne (le_antisymm hPL ?_)⟩
    intro l hl
    have hl' : l ∈ P ⊔ Sgp153 T V₁ := heq ▸ hLI hl
    obtain ⟨p, hp, s, hs, rfl⟩ := FLc.mem_sup_prod_of_conj hPS l hl'
    have hsL : s ∈ L := by
      have := L.mul_mem (L.inv_mem (hPL hp)) hl
      simpa [mul_assoc] using this
    exact P.mul_mem hp (hBP ⟨hs, hsL⟩)
  obtain ⟨a₁, b₁, c₁⟩ := fin P₁ hB₁ hP₁L hP₁ne (hYY.trans (sup_le hY₁P₁ hY₂P₁)) hP₁S
  obtain ⟨a₂, b₂, c₂⟩ := fin P₂ hB₂ hP₂L hP₂ne (hYY.trans (sup_le hY₁P₂ hY₂P₂)) hP₂S
  refine ⟨P₁ ⊔ Sgp153 T V₁, P₂ ⊔ Sgp153 T V₁, a₁, a₂, b₁, b₂, c₁, c₂, ?_⟩
  rw [← hP]
  exact sup_le_sup le_sup_left le_sup_left

end CFSG.Quasithin.A38c7
