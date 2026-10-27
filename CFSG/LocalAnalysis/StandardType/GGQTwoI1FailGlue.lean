module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflCentre
public import CFSG.LocalAnalysis.StandardType.GGQTwoTBDerive
public import CFSG.LocalAnalysis.StandardType.GGQTwoProp898

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2cv_cent_eq {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (M : GGQ2LDatum p Bs L x) :
    (Subgroup.centralizer (L : Set G)).subgroupOf Bs = Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := by
  classical
  obtain ⟨hcfg, -, -⟩ := hS
  obtain ⟨hconfig, -, -⟩ := hcfg
  obtain ⟨hI, hBstar, -⟩ := hconfig
  have hSst : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hLle : L ≤ Subgroup.centralizer ({x} : Set G) := hSst.2.2.2.1.1
  have hxcen : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLle hl)
  apply le_antisymm
  · intro b hb
    rw [Subgroup.mem_subgroupOf] at hb
    have hbc : ∀ l ∈ L, l * (b : G) = (b : G) * l := Subgroup.mem_centralizer_iff.mp hb
    have hfix : M.model (Additive.ofMul b) ∈
        ggFixedSubmodule (p := p) M.model (ggAutomizer L Bs) := by
      rw [mem_ggFixedSubmodule_iff]
      intro φ hφ
      refine Subgroup.closure_induction (k := ggInduced L Bs)
        (p := fun φ _ => ggLin (p := p) M.model φ (M.model (Additive.ofMul b)) =
          M.model (Additive.ofMul b)) ?_ ?_ ?_ ?_ hφ
      · rintro φ ⟨g, hgL, hgnorm, hφg⟩
        apply (ggLin_fix_iff (p := p) M.model φ b).mp
        apply Subtype.ext
        rw [hφg b]
        have hcomm : g * (b : G) = (b : G) * g := hbc g hgL
        rw [hcomm]
        group
      · simp
      · intro a c ha hc iha ihc
        rw [map_mul, LinearEquiv.mul_apply, ihc, iha]
      · intro a ha iha
        rw [map_inv]
        change (ggLin (p := p) M.model a).symm (M.model (Additive.ofMul b)) =
          M.model (Additive.ofMul b)
        apply LinearEquiv.injective (ggLin (p := p) M.model a)
        rw [LinearEquiv.apply_symm_apply, iha]
    rw [M.fixed_x] at hfix
    rw [Submodule.mem_span_singleton] at hfix
    obtain ⟨c, hc⟩ := hfix
    have hβ : Additive.ofMul b = c.val • Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) := by
      apply M.model.injective
      calc M.model (Additive.ofMul b)
          = c • M.model (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) := hc.symm
        _ = (c.val : ZMod p) • M.model (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) := by
              rw [ZMod.natCast_zmod_val]
        _ = c.val • M.model (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) :=
              Nat.cast_smul_eq_nsmul (ZMod p) c.val _
        _ = M.model (c.val • Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) :=
              (map_nsmul M.model.toAddMonoidHom c.val _).symm
    rw [← ofMul_pow] at hβ
    have hb_eq : b = (⟨x, M.hx⟩ : ↥Bs) ^ c.val := Additive.ofMul.injective hβ
    refine Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), ?_⟩
    rw [zpow_natCast]
    exact hb_eq.symm
  · rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
    exact hxcen

private theorem ggQ2cv_card_x {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (M : GGQ2LDatum p Bs L x) : Nat.card (Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs)) = p := by
  obtain ⟨hcfg, -, -⟩ := hS
  obtain ⟨hconfig, -, -⟩ := hcfg
  obtain ⟨hI, hBstar, -⟩ := hconfig
  have hSst : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxne : x ≠ 1 := hSst.2.2.1
  have hBs : IsElemAbelian p Bs := hBstar.2.1
  have hpow : (⟨x, M.hx⟩ : ↥Bs) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hBs.2 x M.hx, Subgroup.coe_one]
  have hne : (⟨x, M.hx⟩ : ↥Bs) ≠ 1 := by
    intro h
    exact hxne (by simpa using congrArg Subtype.val h)
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hpow hne

private theorem ggQ2cv_card_Bs {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) :
    Nat.card ↥Bs = p ^ Module.finrank (ZMod p) M.V := by
  haveI hE : Finite (Additive ↥Bs) :=
    Finite.of_injective (Additive.ofMul.symm : Additive ↥Bs → ↥Bs)
      Additive.ofMul.symm.injective
  haveI : Finite M.V :=
    Finite.of_injective (M.model.toEquiv.symm : M.V → Additive ↥Bs)
      M.model.toEquiv.symm.injective
  haveI : Fintype M.V := Fintype.ofFinite M.V
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcard : Nat.card ↥Bs = Nat.card M.V :=
    Nat.card_congr (Additive.ofMul.trans M.model.toEquiv)
  rw [hcard, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

private theorem ggQ2cv_index {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (M : GGQ2LDatum p Bs L x) :
    ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index =
      p ^ (Module.finrank (ZMod p) M.V - 1) := by
  classical
  have hCcard : Nat.card ↥((Subgroup.centralizer (L : Set G)).subgroupOf Bs) = p := by
    rw [ggQ2cv_cent_eq hS M]
    exact ggQ2cv_card_x hS M
  have hcard := Subgroup.card_mul_index ((Subgroup.centralizer (L : Set G)).subgroupOf Bs)
  rw [hCcard, ggQ2cv_card_Bs M] at hcard
  have hD : 0 < Module.finrank (ZMod p) M.V := by
    by_contra hD
    rw [Nat.eq_zero_of_not_pos hD, pow_zero] at hcard
    exact (Fact.out : p.Prime).not_dvd_one ⟨_, hcard.symm⟩
  have hD' : Module.finrank (ZMod p) M.V = (Module.finrank (ZMod p) M.V - 1) + 1 :=
    (Nat.succ_pred_eq_of_pos hD).symm
  rw [hD', pow_succ, Nat.mul_comm (p ^ (Module.finrank (ZMod p) M.V - 1)) p] at hcard
  exact Nat.mul_left_cancel (Fact.out : p.Prime).pos hcard

private theorem ggQ2cv_finrank_sup {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x)
    (hx : M.xV ∉ M.coSpan)
    (hsup : M.coSpan ⊔ Submodule.span (ZMod p) {M.xV} = ⊤) :
    Module.finrank (ZMod p) M.V = Module.finrank (ZMod p) M.coSpan + 1 := by
  haveI hfdH : FiniteDimensional (ZMod p) M.coSpan := by
    rw [GGQ2LDatum.coSpan]
    exact Module.Finite.span_of_finite (ZMod p) (Set.finite_range M.coroot)
  haveI hfdS : FiniteDimensional (ZMod p) (Submodule.span (ZMod p) {M.xV}) :=
    Module.Finite.span_of_finite (ZMod p) (Set.finite_singleton M.xV)
  have hx0 : M.xV ≠ 0 := fun h => hx (h ▸ M.coSpan.zero_mem)
  have hdisj : M.coSpan ⊓ Submodule.span (ZMod p) {M.xV} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hvH, hvS⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hvS
    rw [← hc] at hvH
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul] at hc
      exact hc.symm
    · exact absurd (by
        have hxx : M.xV = c⁻¹ • (c • M.xV) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hxx]
        exact Submodule.smul_mem _ _ hvH) hx
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq M.coSpan
    (Submodule.span (ZMod p) {M.xV})
  have hspan : Module.finrank (ZMod p) (Submodule.span (ZMod p) {M.xV}) = 1 :=
    finrank_span_singleton hx0
  rw [hsup, hdisj, finrank_top, finrank_bot, hspan, add_zero] at hfin
  exact hfin

private theorem ggQ2cv_dim_nonheart {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x)
    (h : M.ShapeFull ∨ M.ShapeA ∨ M.ShapeC) :
    Module.finrank (ZMod p) M.V = Fintype.card M.Λ + 1 := by
  rcases h with hFull | hA | hC
  · obtain ⟨-, hLI, hxVn, hsup⟩ := hFull
    have hco : Module.finrank (ZMod p) M.coSpan = Fintype.card M.Λ :=
      finrank_span_eq_card hLI
    rw [ggQ2cv_finrank_sup M hxVn hsup, hco]
  · exact hA.2.2.2.1
  · exact hC.2.2.2.1

private theorem ggQ2cv_dim_heart {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) (h : M.HeartShape) :
    Module.finrank (ZMod p) M.V = Fintype.card M.Λ := by
  rcases h with hB | hD
  · obtain ⟨-, hco1, hxVn, hsup⟩ := hB
    rw [ggQ2cv_finrank_sup M hxVn hsup]
    exact hco1
  · obtain ⟨-, hLI, htop⟩ := hD
    rw [← finrank_top (ZMod p) M.V, ← htop]
    exact finrank_span_eq_card hLI

private theorem ggQ2cv_card_lie {lab : LargeEvenLabel} {ι : Type} [Fintype ι]
    {M : CoxeterMatrix ι} (h : GGQ2LabelWeyl lab M) (hlab : GGQ2TBLabel lab) :
    Fintype.card ι = GGQ2LieRank lab := by
  unfold GGQ2TBLabel at hlab
  rcases hlab with hA | hBC | hD | htwD | hF4 | htwE6 | hE7 | hE8
  · obtain ⟨htag, -⟩ := hA
    simp only [GGQ2LabelWeyl, htag] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, htag]
  · obtain ⟨htag | htag, -⟩ := hBC
    · simp only [GGQ2LabelWeyl, htag] at h
      obtain ⟨e, -⟩ := h
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
      simp [GGQ2LieRank, htag]
    · simp only [GGQ2LabelWeyl, htag] at h
      obtain ⟨e, -⟩ := h
      rw [Fintype.card_congr e.symm, Fintype.card_fin]
      simp [GGQ2LieRank, htag]
  · obtain ⟨htag, -⟩ := hD
    simp only [GGQ2LabelWeyl, htag] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, htag]
  · obtain ⟨htag, -⟩ := htwD
    simp only [GGQ2LabelWeyl, htag] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, htag]
  · simp only [GGQ2LabelWeyl, hF4] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, hF4]
  · simp only [GGQ2LabelWeyl, htwE6] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, htwE6]
  · simp only [GGQ2LabelWeyl, hE7] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, hE7]
  · simp only [GGQ2LabelWeyl, hE8] at h
    obtain ⟨e, -⟩ := h
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
    simp [GGQ2LieRank, hE8]

theorem ggQ2_cav_of_tableB (hF : GGQ2CavOfTBFull) (hH : GGQ2CavOfTBHeart)
    (hT : GGQ2TableBI1Fail) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hI1 : ¬ GGQTwoI1 Bs D J) : 4 ∣ Nat.card (ggAutomizer J Bs) := by
  haveI : Fact p.Prime := ⟨by rw [hp]; exact Nat.prime_three⟩
  obtain ⟨labL, hlab, hTB, hmark, M, hweyl, hshape, hlast⟩ := hT hS hp hI1
  rcases hshape with hFull | hA | hB | hC | hD
  · exact hF hS hp ⟨labL, hlab, hmark, by
      rw [ggQ2cv_index hS M, ggQ2cv_dim_nonheart M (Or.inl hFull),
        Nat.add_sub_cancel, ggQ2cv_card_lie hweyl hTB]⟩
  · exact hF hS hp ⟨labL, hlab, hmark, by
      rw [ggQ2cv_index hS M, ggQ2cv_dim_nonheart M (Or.inr (Or.inl hA)),
        Nat.add_sub_cancel, ggQ2cv_card_lie hweyl hTB]⟩
  · refine hH hS hp hI1 ⟨labL, hlab, hmark, ?_, ?_⟩ M (Or.inl hB)
    · exact hlast (le_of_eq (ggQ2cv_dim_heart M (Or.inl hB)))
    · rw [ggQ2cv_index hS M, ggQ2cv_dim_heart M (Or.inl hB), ggQ2cv_card_lie hweyl hTB]
  · exact hF hS hp ⟨labL, hlab, hmark, by
      rw [ggQ2cv_index hS M, ggQ2cv_dim_nonheart M (Or.inr (Or.inr hC)),
        Nat.add_sub_cancel, ggQ2cv_card_lie hweyl hTB]⟩
  · refine hH hS hp hI1 ⟨labL, hlab, hmark, ?_, ?_⟩ M (Or.inr hD)
    · exact hlast (le_of_eq (ggQ2cv_dim_heart M (Or.inr hD)))
    · rw [ggQ2cv_index hS M, ggQ2cv_dim_heart M (Or.inr hD), ggQ2cv_card_lie hweyl hTB]

@[expose] def GGQ2GammaXOffI1Input : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
      4 ∣ Nat.card (ggAutomizer J Bs) → GGQ2GammaX p B Bs x L D J

@[expose] def GGQ2P3OffI1Input : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J → ∀ [Fact p.Prime],
      4 ∣ Nat.card (ggAutomizer J Bs) → ¬ GGQ2ReflAbsIrred p Bs → GGQ2P3 p Bs x

@[expose] def GGQ2ReflRestOutInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
    4 ∣ Nat.card (ggAutomizer J Bs) →
    ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection p φ → GGQ2MovesX Bs x φ →
      GGQ2CentreNotIn Bs D φ →
      (¬ GGQ2EForm Bs J φ ∧ ¬ ∃ (y : G) (K : Subgroup G),
        GGNbr p B x D J y K ∧ (∀ c : ↥Bs, (c : G) = y → φ c = c) ∧ (¬ ∃ k ∈ K, GGQ2Ind Bs k φ) ∧
        ¬ ∃ k ∈ K, k ∈ Subgroup.normalizer (Bs : Set G) ∧ k * x * k⁻¹ = g * x * g⁻¹) →
        g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem ggQ2ReflRestInput_of_out (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h : GGQ2ReflRestOutInput) : GGQ2ReflRestInput := by
  intro G _ _ p B Bs x L D J hS hp hI1 hCav g φ hInd hR hM hcase
  by_cases hC : GGQ2CentreNotIn Bs D φ
  · rcases hcase with hc | hc
    · exact absurd hC hc
    · exact h hS hp hI1 hCav g φ hInd hR hM hC hc
  · exact ggQ2n_reflCentre hLB hP hS.1 hp hCav g φ hInd hC

theorem ggQ2_i1FailInput_of_pieces (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hF : GGQ2CavOfTBFull) (hH : GGQ2CavOfTBHeart) (hT : GGQ2TableBI1Fail)
    (hΓ : GGQ2GammaXOffI1Input) (h898 : GGQ2Prop898) (hP3 : GGQ2P3OffI1Input)
    (hE : GGQ2ReflEInput) (hK : GGQ2ReflKInput) (hR : GGQ2ReflRestOutInput) :
    GGQ2I1FailInput := by
  intro G _ _ p B Bs x L D J hS hp hI1
  haveI : Fact p.Prime := ⟨by rw [hp]; exact Nat.prime_three⟩
  have hCav := ggQ2_cav_of_tableB hF hH hT hS hp hI1
  have hx := ggQ2_x_mem_Bs hS
  have hmove : GGQ2ReflMoveX p B Bs x L D J :=
    ggQ2ReflMoveX_of_split hE hK (ggQ2ReflRestInput_of_out hLB hP hR) hS hp hI1 hCav
  have hInM : GGQ2ReflInM p B Bs x L D J := by
    intro g φ hInd hRefl
    by_cases hm : GGQ2MovesX Bs x φ
    · exact hmove g φ hInd hRefl hm
    · apply hΓ hS hp hI1 hCav g hInd.1
      have hfix : φ ⟨x, hx⟩ = ⟨x, hx⟩ := by
        by_contra hne
        exact hm ⟨⟨x, hx⟩, rfl, hne⟩
      have h2 := hInd.2 ⟨x, hx⟩
      rw [hfix] at h2
      rw [← h2]
      exact Subgroup.mem_zpowers x
  have hP3' : GGQ2P3 p Bs x := by
    by_cases hAI : GGQ2ReflAbsIrred p Bs
    · exact h898 hS hp hI1 hAI hInM
    · exact hP3 hS hp hI1 hCav hAI
  exact ggQ2_normalizer_le_of_refl hx (hΓ hS hp hI1 hCav) hP3' hmove

end CFSG.StandardType

end
