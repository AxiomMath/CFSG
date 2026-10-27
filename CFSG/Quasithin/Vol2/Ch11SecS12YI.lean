module

public import CFSG.Quasithin.Vol2.Ch11SecS12YH
public import CFSG.Quasithin.Vol2.Ch11SecS12X

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 SecD
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.SL3Model

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

theorem exists_elemAb_cU (hC : SecS.CartanFacts) (hN : SecA.NatFacts)
    (hG2 : SecA.FactG2DerivedOrder) (hFb : SecA.Facts12b) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h : SecS.StarHyp G T L I V₁ V₂ X K) (hSL3 : KindSL3 L (fsuV T I) 2) :
    IsElemAbelian 2 (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
        Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G)) ∧
      16 ≤ Nat.card ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
        Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G)) ∧
      ∃ y ∈ X ⊓ LOf L V₁, ∃ e ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
        Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G), y * e * y⁻¹ ≠ e := by
  set E := conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
    Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G) with hEdef
  have hE := isElemAbelian_cU hC hN hG2 hFb h1102 h1103 h hSL3
  obtain ⟨y, hy, hyE⟩ := exists_noncomm_cU hC hN hG2 hFb h1102 h1103 h hSL3
  refine ⟨hE, ?_, y, hy, hyE⟩
  have hc := (SecS.cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan).1
  have hXN : X ≤ Subgroup.normalizer (LOf L V₁ : Set G) := fun _ hx =>
    SecS.cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan hx
  have hX9 : Nat.card ↥X = 9 := SecS.card_cartan hc hXN
    (SecS.cartan_inf_lOf_inf_sectionCentralizer hN h1102 h.hyp h.v₁ h.cartan)
  have hcomm : IsMulCommutative ↥X :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hX9]; norm_num)
  obtain ⟨D⟩ := (natural_star h1102 h1103 hG2 h.hyp h.v₁ hSL3).nonempty_data
  have hV₁V := SecA.IsVi.le_fsuV h.v₁
  have hK2 : IsPGroup 2 ↥(pCoreOf 2 (L ⊔ T)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hα₀ := NatData3'.alpha0_surjective D le_rfl hV₁V
  have hker := NatData3'.alpha0_ker D le_rfl hV₁V hK2
  have hF : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  set H := LOf L V₁ ⊓ Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G) with hH
  have hHL : H ≤ LOf L V₁ := inf_le_left
  have hX₁p : IsPGroup 3 ↥(SecA.xOne X (LOf L V₁)) := IsPGroup.of_card (n := 1) (by
    rw [hc.cardX₁, pow_one])
  have hcov : ∀ l : ↥(LOf L V₁), ∃ h' : ↥H,
      NatData3'.alpha0 D hV₁V (Subgroup.inclusion hHL h') = NatData3'.alpha0 D hV₁V l := by
    intro l
    obtain ⟨b, hb, hlb⟩ := exists_mul_mem_centralizer hX₁p (fun x hx => hx.2.1)
      (fun x hx l hl => hx.2.2.2 l hl) l.2
    have hbL : b ∈ LOf L V₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hb
    refine ⟨⟨(l : G) * b, (LOf L V₁).mul_mem l.2 hbL, hlb⟩, ?_⟩
    have hb' : (⟨b, hbL⟩ : ↥(LOf L V₁)) ∈ (NatData3'.alpha0 D hV₁V).ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hb
    have e1 : Subgroup.inclusion hHL ⟨(l : G) * b, (LOf L V₁).mul_mem l.2 hbL, hlb⟩ =
        l * ⟨b, hbL⟩ := rfl
    rw [e1, map_mul, MonoidHom.mem_ker.mp hb', mul_one]
  have hHE : H ≤ Subgroup.normalizer (E : Set G) := by
    intro g hg
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, Subgroup.le_normalizer hg.2⟩
    have hgN : g ∈ Subgroup.normalizer (V₁ : Set G) :=
      (perfectCore_le _ hg.1 : g ∈ L ⊓ Subgroup.normalizer (V₁ : Set G)).2
    exact le_normalizer_conjClosure _ _ hgN
  have hyH : y ∈ H := by
    refine ⟨hy.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have := hcomm.is_comm.comm (⟨x, hx.1⟩ : ↥X) ⟨y, hy.1⟩
    simpa using congrArg Subtype.val this
  have hy3 : y ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(X ⊓ LOf L V₁)) (x := ⟨y, hy⟩)
    rw [hc.card₁] at this
    simpa using congrArg Subtype.val this
  obtain ⟨σ, hσ5, hσ1⟩ := exists_pow_five hF (NatData3'.alpha0 D hV₁V) hα₀ hker hHL hcov hHE
    hyH hy3 hyE
  have hEp : IsPGroup 2 ↥E := fun z => ⟨1, Subtype.ext (by simpa using hE.2 z z.2)⟩
  exact sixteen_le_card_of_pow_five hEp hσ5 hσ1

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
