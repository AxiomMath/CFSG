module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSkeleton
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Fischer.Classification.Recognition.SymOBasic

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

@[expose] def LSS92TorusOrderInput {ι : Type} (M : CoxeterMatrix ι) (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsEm m (⊤ : Subgroup G) → IsSimpleGroup G →
    ∀ E : Subgroup G, IsElemAbelian 3 E → Nat.card E = 3 ^ m →
      Nat.card (Subgroup.normalizer (E : Set G)) ≤ 3 ^ m * Nat.card M.Group

private theorem g0_not_isCyclic_of_isElemAbelian_card {R : Type} [Group R] {E : Subgroup R}
    {k : ℕ} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ k) (hk : 2 ≤ k) :
    ¬ IsCyclic E := by
  intro hcyc
  haveI : IsCyclic E := hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hE.2 (g : R) g.2)
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hg3
  have hle : Nat.card E ≤ 3 := by
    rw [← hg]
    exact Nat.le_of_dvd (by norm_num) hdvd
  have h9 : 9 ≤ Nat.card E := by
    rw [hcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

private theorem g0_bs_le_normalizer_ggG0 {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J) :
    Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  refine le_normalizer_of_map_conj_le fun b hb => ?_
  unfold ggG0
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer
    (GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1 hb)]
  refine sup_le le_sup_left ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun y => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun K => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hyK => ?_
  rw [map_conj_eq_of_mem_normalizer
    (GGDichotomy.le_normalizer_of_innerDiagOn (hR.2.2.1.2 y K hyK) hb)]
  exact le_ggG0_of_ggNbr hyK

theorem normalizer_bstar_le_normalizer_ggG0_of_le {ι : Type} (M : CoxeterMatrix ι) (m : ℕ)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) {A₀ : Subgroup (MulAut ↥Bs)} (e : M.Group ≃* ↥A₀)
    (hA₀G0 : A₀ ≤ ggAutomizer (ggG0 3 B x L D J) Bs) (hcard : Nat.card Bs = 3 ^ m)
    (hN : Nat.card (Subgroup.normalizer (Bs : Set G)) ≤ 3 ^ m * Nat.card M.Group) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  have hEab : IsElemAbelian 3 Bs := hR.1.2.1.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEab.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hBsC : Bs ≤ Subgroup.centralizer (Bs : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hcomm b hb c hc).symm
  have hrange : (Subgroup.normalizerMonoidHom Bs).range = ggAutomizer ⊤ Bs := by
    rw [ggAutomizer_eq]
    refine le_antisymm ?_ ?_
    · rintro φ ⟨u, rfl⟩
      exact ⟨(u : G), Subgroup.mem_top _, u.2, fun b =>
        Subgroup.normalizerMonoidHom_apply_apply_coe Bs u b⟩
    · rintro φ ⟨g, -, hgN, hg⟩
      refine ⟨⟨g, hgN⟩, ?_⟩
      ext b
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (hg b).symm
  have hsplit : Nat.card (Subgroup.centralizer (Bs : Set G)) * Nat.card (ggAutomizer ⊤ Bs) =
      Nat.card (Subgroup.normalizer (Bs : Set G)) := by
    have h := Subgroup.card_ker_mul_card_range (Subgroup.normalizerMonoidHom Bs)
    rw [Subgroup.normalizerMonoidHom_ker] at h
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer (Bs : Set G))).toEquiv, hrange] at h
    exact h
  have hA₀X : A₀ ≤ ggAutomizer ⊤ Bs := hA₀G0.trans (ggAutomizer_mono Bs le_top)
  have hcardA₀ : Nat.card A₀ = Nat.card M.Group :=
    (Nat.card_congr e.toEquiv).symm
  have hcx_le : Nat.card (Subgroup.centralizer (Bs : Set G)) * Nat.card (ggAutomizer ⊤ Bs) ≤
      Nat.card Bs * Nat.card M.Group :=
    calc Nat.card (Subgroup.centralizer (Bs : Set G)) * Nat.card (ggAutomizer ⊤ Bs)
        = Nat.card (Subgroup.normalizer (Bs : Set G)) := hsplit
      _ ≤ 3 ^ m * Nat.card M.Group := hN
      _ = Nat.card Bs * Nat.card M.Group := by rw [hcard]
  have haC : Nat.card Bs ≤ Nat.card (Subgroup.centralizer (Bs : Set G)) :=
    Subgroup.card_le_of_le hBsC
  have hwX : Nat.card M.Group ≤ Nat.card (ggAutomizer ⊤ Bs) := by
    rw [← hcardA₀]
    exact Subgroup.card_le_of_le hA₀X
  have hax_le_cx : Nat.card Bs * Nat.card (ggAutomizer ⊤ Bs) ≤
      Nat.card (Subgroup.centralizer (Bs : Set G)) * Nat.card (ggAutomizer ⊤ Bs) :=
    mul_le_mul_left haC (Nat.card (ggAutomizer ⊤ Bs))
  have hax_le_aw : Nat.card Bs * Nat.card (ggAutomizer ⊤ Bs) ≤
      Nat.card Bs * Nat.card M.Group := hax_le_cx.trans hcx_le
  have haw_le_ax : Nat.card Bs * Nat.card M.Group ≤
      Nat.card Bs * Nat.card (ggAutomizer ⊤ Bs) :=
    mul_le_mul_right hwX (Nat.card Bs)
  have hax_eq : Nat.card Bs * Nat.card (ggAutomizer ⊤ Bs) =
      Nat.card Bs * Nat.card M.Group :=
    le_antisymm hax_le_aw haw_le_ax
  have hcx_eq : Nat.card (Subgroup.centralizer (Bs : Set G)) * Nat.card (ggAutomizer ⊤ Bs) =
      Nat.card Bs * Nat.card M.Group :=
    le_antisymm hcx_le (haw_le_ax.trans hax_le_cx)
  have hBs_ne : Nat.card Bs ≠ 0 := by
    rw [hcard]
    exact pow_ne_zero _ (by norm_num)
  have hX_eq_w : Nat.card (ggAutomizer ⊤ Bs) = Nat.card M.Group :=
    mul_left_cancel₀ hBs_ne hax_eq
  have hw_ne : Nat.card M.Group ≠ 0 := by
    have hw_pos : 0 < Nat.card M.Group := by
      rw [← hcardA₀]
      exact Nat.card_pos
    exact hw_pos.ne'
  have hCcard : Nat.card (Subgroup.centralizer (Bs : Set G)) = Nat.card Bs := by
    have h := hcx_eq
    rw [hX_eq_w] at h
    exact mul_right_cancel₀ hw_ne h
  have hC_eq : Subgroup.centralizer (Bs : Set G) = Bs :=
    (Subgroup.eq_of_le_of_card_ge hBsC (le_of_eq hCcard)).symm
  have hXcard : Nat.card (ggAutomizer ⊤ Bs) = Nat.card A₀ := by
    rw [hX_eq_w, hcardA₀]
  have hX_eq_A₀ : ggAutomizer ⊤ Bs = A₀ :=
    (Subgroup.eq_of_le_of_card_ge hA₀X (le_of_eq hXcard)).symm
  intro g hg
  have hφX : ggConjAut Bs hg ∈ ggAutomizer ⊤ Bs :=
    ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hg
  have hφA₀ : ggConjAut Bs hg ∈ A₀ := by
    rwa [hX_eq_A₀] at hφX
  have hφG0 : ggConjAut Bs hg ∈ ggAutomizer (ggG0 3 B x L D J) Bs := hA₀G0 hφA₀
  obtain ⟨g₀, hg₀G0, _, hg₀conj⟩ := mem_ggAutomizer_iff.mp hφG0
  have hmemC : g₀⁻¹ * g ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := hg₀conj ⟨b, hb⟩
    rw [ggConjAut_apply] at h1
    calc b * (g₀⁻¹ * g) = g₀⁻¹ * (g₀ * b * g₀⁻¹) * g := by group
      _ = g₀⁻¹ * (g * b * g⁻¹) * g := by rw [← h1]
      _ = (g₀⁻¹ * g) * b := by group
  have hmemBs : g₀⁻¹ * g ∈ Bs := by
    rwa [hC_eq] at hmemC
  have hg₀N0 : g₀ ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    Subgroup.le_normalizer hg₀G0
  have hmemN0 : g₀⁻¹ * g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    g0_bs_le_normalizer_ggG0 hR hmemBs
  have heq : g = g₀ * (g₀⁻¹ * g) := by group
  rw [heq]
  exact Subgroup.mul_mem _ hg₀N0 hmemN0

theorem not_le_normalizer_bstar {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J) {m : ℕ} (hm : 2 ≤ m)
    (hcard : Nat.card Bs = 3 ^ m) : ¬ L ≤ Subgroup.normalizer (Bs : Set G) := by
  intro hLle
  have hSstar : LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  have hcomp : Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hSstar.2.2.2.1
  have hLq : Assembly.IsQuasisimple ↥L := hcomp.2.2
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S := hSstar.2.2.2.2
  have hEab : IsElemAbelian 3 Bs := hR.1.2.1.2.1
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1
  have hAnormal : ((L ⊓ Bs).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      ((le_inf Subgroup.le_normalizer hLle).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hAcomm : ∀ a ∈ (L ⊓ Bs).subgroupOf L, ∀ b ∈ (L ⊓ Bs).subgroupOf L,
      a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    show (a : G) * (b : G) = (b : G) * (a : G)
    exact congrArg Subtype.val (hEab.1.is_comm.comm
      (⟨(a : G), (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).2⟩ : ↥Bs)
      (⟨(b : G), (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hb)).2⟩ : ↥Bs))
  have hAcenter : (L ⊓ Bs).subgroupOf L ≤ Subgroup.center ↥L :=
    CFSG.Fischer.Classification.Recognition.SymO.le_center_of_normal (Y := ↥L) hLq hAnormal
      hAcomm
  have hA_le_cent : L ⊓ Bs ≤ Subgroup.centralizer (L : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro l' hl'
    have hmemN : (⟨z, (Subgroup.mem_inf.mp hz).1⟩ : ↥L) ∈ (L ⊓ Bs).subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact hz
    have hc := hAcenter hmemN
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨l', hl'⟩)
  have hcommL : ⁅L, Bs⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hBsL
  have hcommBs : ⁅L, Bs⁆ ≤ Bs := by
    have h := Subgroup.le_normalizer_iff_commutator_le_left.mp hLle
    rwa [Subgroup.commutator_comm] at h
  have hcomm_le : ⁅L, Bs⁆ ≤ Subgroup.centralizer (L : Set G) :=
    (le_inf hcommL hcommBs).trans hA_le_cent
  have h1 : ⁅⁅L, Bs⁆, L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcomm_le
  have h2 : ⁅⁅Bs, L⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm Bs L]; exact h1
  have h3 : ⁅⁅L, L⁆, Bs⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [commutator_self_eq_of_isQuasisimple hLq] at h3
  have hBsc : Bs ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h3)
  exact absurd (hcyc Bs hBsc (CFSG.Open.IsElemAbelian.isPGroup hEab))
    (g0_not_isCyclic_of_isElemAbelian_card hEab hcard hm)

theorem ggG0_eq_top_of_torusInputs_of_le {ι : Type} (M : CoxeterMatrix ι) (m : ℕ) (hm : 2 ≤ m)
    (hMax : LSS92TorusMaxInput) (hOrd : LSS92TorusOrderInput M m)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) {A₀ : Subgroup (MulAut ↥Bs)} (e : M.Group ≃* ↥A₀)
    (hA₀G0 : A₀ ≤ ggAutomizer (ggG0 3 B x L D J) Bs)
    (hEm : IsEm m (⊤ : Subgroup G)) (hcard : Nat.card Bs = 3 ^ m) :
    ggG0 3 B x L D J = ⊤ := by
  have hsimple : IsSimpleGroup G := hR.1.1.1
  have hEab : IsElemAbelian 3 Bs := hR.1.2.1.2.1
  have hMaxBs : IsCoatom (Subgroup.normalizer (Bs : Set G)) :=
    hMax G m hEm hsimple hR.1.1.2.2.1 Bs hEab hcard
  have hOrdBs : Nat.card (Subgroup.normalizer (Bs : Set G)) ≤ 3 ^ m * Nat.card M.Group :=
    hOrd G hEm hsimple Bs hEab hcard
  have hNle := normalizer_bstar_le_normalizer_ggG0_of_le M m hR e hA₀G0 hcard hOrdBs
  rcases (IsCoatom.le_iff hMaxBs).mp hNle with htop | heq
  · have hnormal : (ggG0 3 B x L D J).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ggG0 3 B x L D J) with hbot | htop'
    · exfalso
      have hLbot : L ≤ (⊥ : Subgroup G) := hbot ▸ le_ggG0_left 3 B x L D J
      exact ne_bot_of_isComponentOf' (hR.1.1.2.2.2.2.2.2.1.2.2.2.1) (le_bot_iff.mp hLbot)
    · exact htop'
  · exfalso
    have hLle : L ≤ Subgroup.normalizer (Bs : Set G) := by
      have h1 : L ≤ ggG0 3 B x L D J := le_ggG0_left 3 B x L D J
      have h2 : ggG0 3 B x L D J ≤
          Subgroup.normalizer (ggG0 3 B x L D J : Set G) := Subgroup.le_normalizer
      rw [heq] at h2
      exact h1.trans h2
    exact not_le_normalizer_bstar hR hm hcard hLle

end CFSG.StandardType.FrameRoute
