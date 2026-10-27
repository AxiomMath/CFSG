module

public import CFSG.RankThree.GF2n.Smith81.Lin3Leaves
public import CFSG.RankThree.GF2n.Smith81.Lin31TwoPGL
public import CFSG.RankThree.GF2n.Smith81.Lin31TwoSetup
public import CFSG.RankThree.GF2n.Smith81.Lin31TwoTorus

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem lin31Back_two {n : ℕ} {V₁ V₂ : Subgroup G} (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn2 : 2 ≤ n) (hBV : B ≤ V₁) {v : G} (hv1 : v ≠ 1)
    (hv : v ∈ V₁ ∨ v ∈ V₂) : InZClass Z v := by
  have H := hc.hyp
  obtain ⟨K, hK, hfin, hcard, φ, hrange, hker, hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup,
    hs₁, hs₂, ⟨x₀, hx₀M, hx₀V⟩, hcent⟩ := hS
  obtain ⟨hN₁, hn₁, ψ, hψ⟩ := hs₁
  have hBne : B ≠ ⊥ := by
    intro h
    have h1 : Nat.card B = Nat.card Z := by
      obtain ⟨g, hg⟩ := hc.conj
      rw [hg, card_conjSubgroup]
    rw [h, Subgroup.card_bot] at h1
    have := H.q4
    omega
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbV : b ∈ V₁ := hBV hb
  have hbZ : b ∉ Z := by
    intro hbz
    have : b ∈ Z ⊓ B := ⟨hbz, hb⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot] at this
    exact hb1' this
  have hbcl : InZClass Z b := inZClass_of_mem_root hc.conj hb hb1'
  have key : ∀ v ∈ V₁, v ≠ 1 → InZClass Z v := by
    intro v hv hv1
    by_cases hvZ : v ∈ Z
    · exact ⟨1, v, hvZ, hv1, by group⟩
    have hcoord : ∀ (u : G) (hu : u ∈ V₁), u ∉ Z →
        Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨u, hu⟩)) ≠ 0 := by
      intro u hu huZ h0
      have h1 : ψ (QuotientGroup.mk ⟨u, hu⟩) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [h0]; rfl
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact huZ h1
    obtain ⟨A, hA, hAw⟩ := CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq hn2
      (hcoord b hbV hbZ) (hcoord v hv hvZ)
    obtain ⟨l, hl⟩ : A ∈ φ.range := hrange ▸ hA
    have hlb : (l : G) * b * (l : G)⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hN₁ l.2) b).mp hbV
    have hmk := hψ l ⟨b, hbV⟩ ⟨(l : G) * b * (l : G)⁻¹, hlb⟩ rfl
    have hvec : Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨(l : G) * b * (l : G)⁻¹, hlb⟩)) =
        Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨v, hv⟩)) := by
      rw [hmk, ← hAw, ← hl]
    have hz₁ : v⁻¹ * ((l : G) * b * (l : G)⁻¹) ∈ Z := by
      have h2 := ψ.injective (Multiplicative.toAdd.injective hvec)
      have h3 := (QuotientGroup.eq.mp h2.symm)
      rw [Subgroup.mem_subgroupOf] at h3
      simpa using h3
    set z₁ : G := v⁻¹ * ((l : G) * b * (l : G)⁻¹) with hz₁def
    have hlbcl : InZClass Z ((l : G) * b * (l : G)⁻¹) := hbcl.conj l
    obtain ⟨w, hwQ, hw⟩ := exists_comm_eq H (hV₁Q hv) hvZ hz₁
    have hz2 : z₁ * z₁ = 1 := by rw [← pow_two]; exact Z_sq H hz₁
    have hcomm1 : (l : G) * b * (l : G)⁻¹ = v * z₁ := by rw [hz₁def]; group
    have hwz : w * z₁ * w⁻¹ = z₁ := by
      have := Z_central H hz₁ hwQ
      rw [← this]; group
    have hvz : v * z₁ = z₁ * v := Z_central H hz₁ (hV₁Q hv) |>.symm
    have hconj : w * ((l : G) * b * (l : G)⁻¹) * w⁻¹ = v := by
      rw [hcomm1]
      have e : w * (v * z₁) * w⁻¹ = (w * v * w⁻¹ * v⁻¹) * (v * (w * z₁ * w⁻¹)) := by group
      have hw' : w * v * w⁻¹ * v⁻¹ = z₁ := by rw [← commutatorElement_def]; exact hw
      rw [e, hw', hwz]
      calc z₁ * (v * z₁) = z₁ * (z₁ * v) := by rw [hvz]
        _ = (z₁ * z₁) * v := by group
        _ = v := by rw [hz2, one_mul]
    have := hlbcl.conj w
    rwa [hconj] at this
  rcases hv with hv | hv
  · exact key v hv hv1
  · have hv' : x₀⁻¹ * v * x₀ ∈ V₁ := by
      have : v ∈ conjSubgroup x₀ V₁ := by rw [hx₀V]; exact hv
      exact mem_conjSubgroup.mp this
    have hne : x₀⁻¹ * v * x₀ ≠ 1 := by
      intro h
      apply hv1
      have : v = x₀ * (x₀⁻¹ * v * x₀) * x₀⁻¹ := by group
      rw [this, h]; group
    have := key _ hv' hne
    have h2 := (inZClass_conj_iff (Z := Z) (v := v) x₀⁻¹).mp (by simpa using this)
    exact h2

theorem LinSetup.centDvdN {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (hS : LinSetup M Q Z B n V₁ V₂) : CentDvdN 2 M Q Z (Lgen M (LB M Q B)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcent⟩ := hS
  exact hcent

open TensorModel in
theorem exists_two_planes_of_model (hc : Ctx M Q Z B) (TM : TensorModel M Q Z B)
    (hw : Width Q Z 2) (hCD : CentDvdN 2 M Q Z (Lgen M (LB M Q B))) :
    ∃ W₁ W₂ : Subgroup G, LinSetup M Q Z B 2 W₁ W₂ ∧ B ≤ W₁ ∧
      ∀ v ∈ Q, v ≠ 1 → InZClass Z v → v ∈ W₁ ∨ v ∈ W₂ := by
  obtain ⟨u₁, hu₁, hBu₁⟩ := exists_plane_of_ctx (TM := TM) hc
  obtain ⟨H, μ₁, hHΓ, hHodd, hHns, hHeig⟩ := torus_lemma (TM := TM) hc hw hc hu₁ hBu₁
  obtain ⟨u₂, μ₂, hu₂, hH₂, hμ, hall⟩ := exists_second_eigen hHodd hHns hu₁ hHeig
  have hne : ∀ c : TM.F, u₂ ≠ c • u₁ := by
    intro c hc2
    apply hμ
    have h1 : Matrix.vecMul u₂ (H : Matrix (Fin 2) (Fin 2) TM.F) = μ₁ • u₂ := by
      rw [hc2, Matrix.smul_vecMul, hHeig, smul_comm]
    exact (smul_left_injective TM.F hu₂ (hH₂.symm.trans h1)).symm
  have key : ∀ C : Subgroup G, Ctx M Q Z C → C ≤ TM.plane u₁ ∨ C ≤ TM.plane u₂ := by
    intro C hC
    obtain ⟨u, hu, hCu⟩ := exists_plane_of_ctx (TM := TM) hC
    obtain ⟨H', μ', hH'Γ, hH'odd, hH'ns, hH'eig⟩ := torus_lemma (TM := TM) hc hw hC hu hCu
    obtain ⟨μ'', hμ''⟩ := odd_eigen_common TM.Gamma (card_Gamma_inf_SL (TM := TM) hc hCD) hHΓ
      hH'Γ hHodd hH'odd hHns hH'ns hu hH'eig
    obtain ⟨c, hc0, h | h⟩ := hall u μ'' hu hμ''
    · left
      rw [h, plane_smul hc0] at hCu
      exact hCu
    · right
      rw [h, plane_smul hc0] at hCu
      exact hCu
  have hperm : ∀ m ∈ M, conjSubgroup m (TM.plane u₁) = TM.plane u₁ ∨
      conjSubgroup m (TM.plane u₁) = TM.plane u₂ := by
    intro m hm
    obtain ⟨u', hu', hconj⟩ := conj_plane (TM := TM) hc hu₁ hm
    obtain ⟨g, hg⟩ := hc.conj
    have hB' : Ctx M Q Z (conjSubgroup m B) :=
      { hyp := hc.hyp
        conj := ⟨m * g, by rw [hg, CFSG.RankThree.GF2n.conjSubgroup_mul]⟩
        le := by
          rw [← hc.conj_Q_eq hm]
          exact Subgroup.map_mono hc.le
        ne := by
          intro h
          apply hc.ne
          rw [← hc.conj_Z_eq hm] at h
          exact Subgroup.map_injective (MulAut.conj m).injective h }
    have hnZ : ¬ conjSubgroup m B ≤ Z := by
      intro hle
      apply hB'.ne
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [card_conjSubgroup]
      obtain ⟨g₀, hg₀⟩ := hc.conj
      rw [hg₀, card_conjSubgroup]
    have hle : conjSubgroup m B ≤ TM.plane u' := by
      rw [← hconj]
      exact Subgroup.map_mono hBu₁
    have share : ∀ u'' : Fin 2 → TM.F, u'' ≠ 0 → conjSubgroup m B ≤ TM.plane u'' →
        TM.plane u'' = TM.plane u' := by
      intro u'' hu'' hle''
      by_cases h : ∃ c : TM.F, u'' = c • u'
      · obtain ⟨c, rfl⟩ := h
        have hc0 : c ≠ 0 := fun h0 => hu'' (by rw [h0, zero_smul])
        exact plane_smul hc0
      · exfalso
        push Not at h
        have := plane_inf_plane (TM := TM) hu' hu'' h
        exact hnZ (this ▸ le_inf hle hle'')
    rcases key _ hB' with h | h
    · left
      rw [hconj]
      exact (share u₁ hu₁ h).symm
    · right
      rw [hconj]
      exact (share u₂ hu₂ h).symm
  have hLS := linSetup_planes (TM := TM) hc hCD hu₁ hu₂ hne hperm
  refine ⟨TM.plane u₁, TM.plane u₂, hLS, hBu₁, ?_⟩
  intro v hvQ hv1 hvcl
  by_cases hvZ : v ∈ Z
  · exact Or.inl (Z_le_plane u₁ hvZ)
  · obtain ⟨g, z, hz, -, hvg⟩ := hvcl
    obtain ⟨g', hg'Q, hvg'⟩ := stroth_2_6 hc.hyp hvQ hvZ ⟨g, z, hz, hvg⟩
    have hCtx : Ctx M Q Z (conjSubgroup g' Z) :=
      ⟨hc.hyp, ⟨g', rfl⟩, hg'Q, fun h => hvZ (h ▸ hvg')⟩
    rcases key _ hCtx with h | h
    · exact Or.inl (h hvg')
    · exact Or.inr (h hvg')

theorem LinSetup.exists_two_planes (hc : Ctx M Q Z B) {V₁ V₂ : Subgroup G}
    (hS : LinSetup M Q Z B 2 V₁ V₂) :
    ∃ W₁ W₂ : Subgroup G, LinSetup M Q Z B 2 W₁ W₂ ∧ B ≤ W₁ ∧
      ∀ v ∈ Q, v ≠ 1 → InZClass Z v → v ∈ W₁ ∨ v ∈ W₂ := by
  obtain ⟨TM⟩ := exists_tensorModel hc hS
  exact exists_two_planes_of_model hc TM (hS.width hc.hyp) hS.centDvdN

theorem lin31TwoStatement_holds : Lin31TwoStatement := by
  intro G _ _ M Q Z B V₁ V₂ _ hc hS
  obtain ⟨W₁, W₂, hLS, hBW, hfwd⟩ := LinSetup.exists_two_planes hc hS
  exact ⟨W₁, W₂, hLS, hBW, fun v hvQ hv1 =>
    ⟨fun hcl => hfwd v hvQ hv1 hcl, fun hv => lin31Back_two hc hLS le_rfl hBW hv1 hv⟩⟩

theorem lin31Statement_holds : Lin31Statement :=
  lin31Statement_of_two lin31TwoStatement_holds

theorem lin3Statement_of_seven_leaves (h28c : Lin28CondStatement) (h7 : Lin212C7Statement)
    (hrest : Lin212RestStatement) (h212two : Lin212TwoStatement) (h28two : Lin28TwoStatement)
    (h213 : Lin213Statement) (h26 : Lin26Statement) : Lin3Statement :=
  lin3Statement_of_eight_leaves lin31TwoStatement_holds h28c h7 hrest h212two h28two h213 h26

end CFSG.RankThree.GF2n.Smith81
