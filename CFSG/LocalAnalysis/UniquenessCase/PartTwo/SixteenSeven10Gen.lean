module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

theorem s16c1610_center_fstar {W : Type} [CommGroup W] [Finite W] {Mb : Subgroup (MulAut W)}
    {p : ℕ} [NeZero p] {Q : Type} [Group Q] (hQ : Subgroup.center Q = ⊥)
    (e : ↥(Fstar Mb) ≃* Multiplicative (ZMod p) × Q) :
    ∃ X : Subgroup (MulAut W), X ≤ Fstar Mb ∧ X ≤ Mb ∧ Nat.card X = p ∧
      (∀ m ∈ Mb, ∀ x ∈ X, m * x * m⁻¹ ∈ X) ∧ ∀ f ∈ Fstar Mb, ∀ x ∈ X, f * x = x * f := by
  obtain ⟨hle, hnorm, -⟩ := s16c167_cfg10_fstar_facts Mb
  refine ⟨(Subgroup.center ↥(Fstar Mb)).map (Fstar Mb).subtype, Subgroup.map_subtype_le _,
    (Subgroup.map_subtype_le _).trans hle, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (f := (Fstar Mb).subtype) (Fstar Mb).subtype_injective]
    have h1 : Nat.card (Subgroup.center ↥(Fstar Mb)) =
        Nat.card (Subgroup.center (Multiplicative (ZMod p) × Q)) :=
      Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rw [h1, Subgroup.center_prod, hQ, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,
      Nat.card_prod, Subgroup.center_eq_top, Subgroup.card_top, Subgroup.card_bot,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, mul_one]
  · intro m hm x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : m * (x' : MulAut W) * m⁻¹ ∈ Fstar Mb := hnorm m hm x' x'.2
    refine Subgroup.mem_map.mpr ⟨⟨m * (x' : MulAut W) * m⁻¹, hmem⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : m⁻¹ * (g : MulAut W) * m⁻¹⁻¹ ∈ Fstar Mb := hnorm m⁻¹ (inv_mem hm) g g.2
    have hc := Subgroup.mem_center_iff.mp hx' ⟨_, hg⟩
    have hc' : (m⁻¹ * (g : MulAut W) * m⁻¹⁻¹) * (x' : MulAut W) =
        (x' : MulAut W) * (m⁻¹ * (g : MulAut W) * m⁻¹⁻¹) := congrArg Subtype.val hc
    apply Subtype.ext
    show (g : MulAut W) * (m * (x' : MulAut W) * m⁻¹) =
      (m * (x' : MulAut W) * m⁻¹) * (g : MulAut W)
    calc (g : MulAut W) * (m * (x' : MulAut W) * m⁻¹)
        = m * ((m⁻¹ * (g : MulAut W) * m⁻¹⁻¹) * (x' : MulAut W)) * m⁻¹ := by group
      _ = m * ((x' : MulAut W) * (m⁻¹ * (g : MulAut W) * m⁻¹⁻¹)) * m⁻¹ := by rw [hc']
      _ = (m * (x' : MulAut W) * m⁻¹) * (g : MulAut W) := by group
  · intro f hf x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx' ⟨f, hf⟩)

theorem s16c1610_derived_fstar {W : Type} [CommGroup W] [Finite W] {Mb : Subgroup (MulAut W)}
    {p : ℕ} [NeZero p] {Q : Type} [Group Q] (hQ : _root_.commutator Q = ⊤)
    (e : ↥(Fstar Mb) ≃* Multiplicative (ZMod p) × Q) :
    ∃ N : Subgroup (MulAut W), N ≤ Fstar Mb ∧ Nat.card N = Nat.card Q ∧
      ∀ m ∈ Mb, ∀ n ∈ N, m * n * m⁻¹ ∈ N := by
  obtain ⟨-, hnorm, -⟩ := s16c167_cfg10_fstar_facts Mb
  refine ⟨⁅Fstar Mb, Fstar Mb⁆, ?_, ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (Fstar Mb).mul_mem ((Fstar Mb).mul_mem ((Fstar Mb).mul_mem ha hb)
      ((Fstar Mb).inv_mem ha)) ((Fstar Mb).inv_mem hb)
  · have hF : (⊤ : Subgroup ↥(Fstar Mb)).map (Fstar Mb).subtype = Fstar Mb := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h1 : ⁅Fstar Mb, Fstar Mb⁆ = (_root_.commutator ↥(Fstar Mb)).map (Fstar Mb).subtype := by
      rw [_root_.commutator, Subgroup.map_commutator, hF]
    have hZ : ⁅(⊤ : Subgroup (Multiplicative (ZMod p))),
        (⊤ : Subgroup (Multiplicative (ZMod p)))⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm a b
    have h2 : (_root_.commutator ↥(Fstar Mb)).map e.toMonoidHom =
        (⊥ : Subgroup (Multiplicative (ZMod p))).prod (⊤ : Subgroup Q) := by
      rw [_root_.commutator, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective, ← Subgroup.top_prod_top,
        Subgroup.commutator_prod_prod, hZ,
        show ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ from hQ]
    rw [h1, Subgroup.card_map_of_injective (f := (Fstar Mb).subtype) (Fstar Mb).subtype_injective,
      ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, h2,
      Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot,
      Subgroup.card_top, one_mul]
  · intro m hm n hn
    have key : ⁅Fstar Mb, Fstar Mb⁆ ≤
        (⁅Fstar Mb, Fstar Mb⁆).comap (MulAut.conj m).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_comap]
      have h : (MulAut.conj m).toMonoidHom ⁅a, b⁆ = ⁅m * a * m⁻¹, m * b * m⁻¹⁆ := by
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
          commutatorElement_def]
        group
      rw [h]
      exact Subgroup.commutator_mem_commutator (hnorm m hm a ha) (hnorm m hm b hb)
    have h := key hn
    rw [Subgroup.mem_comap] at h
    simpa [MulAut.conj_apply] using h

theorem s16c1610_rk_vStar_le {G : Type} [Group G] [Finite G] (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) :
    rk (vStar D.M V₀ V h.isElemAbelian L) ≤ rk (Vtil V₀ V h.isElemAbelian) := by
  have hV := h.isElemAbelian
  have h₀V : V₀ ≤ V := h.pairFacts.le
  have h₁V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h hV
  have h₀₁ : V₀ ≤ v1Sub D.M V₀ V hV L := s15_Infra_le_v1Sub D.M V₀ V hV L
  have e0 := s15_Infra_mSub_eq_rk_imgTil_add V₀ V V hV le_rfl
  have e1 := s15_Infra_mSub_eq_rk_imgTil_add (v1Sub D.M V₀ V hV L) V V hV le_rfl
  rw [s15_Infra_imgTil_top, rk_top, inf_eq_right.2 h₀V] at e0
  rw [s15_Infra_imgTil_top, rk_top, inf_eq_right.2 h₁V] at e1
  have hm : mSub V₀ ≤ mSub (v1Sub D.M V₀ V hV L) := rk_mono h₀₁
  show rk (Vtil (v1Sub D.M V₀ V hV L) V hV) ≤ rk (Vtil V₀ V hV)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
