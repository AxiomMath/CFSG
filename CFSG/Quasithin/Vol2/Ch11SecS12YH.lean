module

public import CFSG.Quasithin.Vol2.Ch11SecS12YG
public import CFSG.Quasithin.Vol2.Ch11SecS12W
public import CFSG.Quasithin.Vol2.Ch11SecS12Y
public import CFSG.Quasithin.Vol2.Ch11SecS12M

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 SecD
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.SL3Model
open Matrix
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

theorem exists_weyl_K' (hC : SecS.CartanFacts) (hN : SecA.NatFacts)
    (hG2 : SecA.FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h : SecS.StarHyp G T L I V₁ V₂ X K)
    {x₁ : G} (hx₁ : x₁ ∈ SecA.xOne X (LOf L V₁)) (hx₁1 : x₁ ≠ 1) :
    ∃ w ∈ K, w ∈ Subgroup.normalizer (X : Set G) ∧ w * x₁ * w⁻¹ ∉ SecA.xOne X (LOf L V₁) := by
  have hc := (SecS.cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan).1
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.pgl
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 2) (by norm_num) (by rw [hF]; norm_num)
  have hSY := h.isSylowTwoOf_inf_sup hN h1102 hc
  have hKΓ : K ≤ K ⊔ SecA.xOne X (LOf L V₁) := le_sup_left
  have hL₁Γ : LOf L V₁ ≤ K ⊔ SecA.xOne X (LOf L V₁) := h.L₁_le_K.trans hKΓ
  have hL₁ne : LOf L V₁ ≠ ⊥ := by
    intro hb
    have : Nat.card ↥(X ⊓ LOf L V₁) = 1 := by
      rw [hb, inf_bot_eq, Subgroup.card_bot]
    rw [hc.card₁] at this
    norm_num at this
  have hperf : ⁅((LOf L V₁).subgroupOf (K ⊔ SecA.xOne X (LOf L V₁))).map (alphaPGL e),
      ((LOf L V₁).subgroupOf (K ⊔ SecA.xOne X (LOf L V₁))).map (alphaPGL e)⁆ =
      ((LOf L V₁).subgroupOf (K ⊔ SecA.xOne X (LOf L V₁))).map (alphaPGL e) := by
    rw [map_alphaPGL, ← Subgroup.map_commutator, modO2Image_perfect hL₁Γ h.perfect_L₁]
  have hne : ((LOf L V₁).subgroupOf (K ⊔ SecA.xOne X (LOf L V₁))).map (alphaPGL e) ≠ ⊥ := by
    rw [map_alphaPGL]
    intro hb
    exact modO2Image_ne_bot hL₁Γ h.perfect_L₁ hL₁ne
      ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hb)
  have hneR : ((LOf L V₁).subgroupOf (K ⊔ SecA.xOne X (LOf L V₁))).map (alphaPGL e) ≠
      commutator (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) := by
    rw [map_alphaPGL, commutator_eq_map e]
    intro heq
    exact modO2Image_L₁_ne_commutator hN h1102 h hc (Subgroup.map_injective e.injective heq)
  have hS : ∃ S : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)),
      QuasithinUnique.IsSylowTwoOf S ⊤ ∧ S ≤ Subgroup.normalizer
        ((((LOf L V₁).subgroupOf (K ⊔ SecA.xOne X (LOf L V₁))).map (alphaPGL e) :
          Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))) : Set _) := by
    refine ⟨(modO2Image (K ⊔ SecA.xOne X (LOf L V₁)) (T ⊓ K)).map e.toMonoidHom,
      isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_modO2Image hSY) _ e.surjective, ?_⟩
    rw [map_alphaPGL]
    exact (Subgroup.map_mono (modO2Image_le_normalizer
      (inf_le_left.trans h.T_le_normalizer_L₁))).trans (Subgroup.le_normalizer_map _)
  have hKR : (K.subgroupOf (K ⊔ SecA.xOne X (LOf L V₁))).map (alphaPGL e) ≤
      commutator (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) := by
    rw [map_alphaPGL, ← modO2Image_perfect hKΓ h.perfect, Subgroup.map_commutator,
      commutator_eq_map e, Subgroup.map_commutator]
    exact Subgroup.commutator_mono (Subgroup.map_mono le_top) (Subgroup.map_mono le_top)
  exact exists_weyl_aux hC hN hG2 h1102 h hF rfl (alphaPGL e) (alphaPGL_surjective e)
    (alphaPGL_eq_one_iff e) hperf hne hneR hS hKR
    ((pCoreOf_two_le_of_isSylowTwoOf hSY).trans inf_le_right) hx₁ hx₁1

theorem exists_noncomm_cU (hC : SecS.CartanFacts) (hN : SecA.NatFacts)
    (hG2 : SecA.FactG2DerivedOrder) (hFb : SecA.Facts12b) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h : SecS.StarHyp G T L I V₁ V₂ X K) (hSL3 : KindSL3 L (fsuV T I) 2) :
    ∃ y ∈ X ⊓ LOf L V₁, ∃ e ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
      Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G), y * e * y⁻¹ ≠ e := by
  have hc := (SecS.cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan).1
  have hXN : X ≤ Subgroup.normalizer (LOf L V₁ : Set G) := fun _ hx =>
    SecS.cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan hx
  have hX9 : Nat.card ↥X = 9 := SecS.card_cartan hc hXN
    (SecS.cartan_inf_lOf_inf_sectionCentralizer hN h1102 h.hyp h.v₁ h.cartan)
  have hXodd : Odd (Nat.card ↥X) := by rw [hX9]; decide
  have hcomm : IsMulCommutative ↥X :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hX9]; norm_num)
  obtain ⟨D⟩ := (natural_star h1102 h1103 hG2 h.hyp h.v₁ hSL3).nonempty_data
  have hV₁V := SecA.IsVi.le_fsuV h.v₁
  obtain ⟨x₁, hx₁, hx₁1⟩ : ∃ x₁ ∈ SecA.xOne X (LOf L V₁), x₁ ≠ 1 := by
    have : Nontrivial ↥(SecA.xOne X (LOf L V₁)) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hc.cardX₁]
      norm_num
    obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : ↥(SecA.xOne X (LOf L V₁)))
    exact ⟨y, hy, fun h => hy1 (Subtype.ext h)⟩
  obtain ⟨hX₁z, -⟩ := eq_zpowers_of_card_three hc.cardX₁ hx₁ hx₁1
  obtain ⟨w, hwK, hwN, hwm⟩ := exists_weyl_K' hC hN hG2 h1102 h hx₁ hx₁1
  have hdX : w * x₁ * w⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hwN x₁).mp hx₁.1
  have hdec : ∀ z ∈ X, ∃ a ∈ SecA.xOne X (LOf L V₁), ∃ b ∈ X ⊓ LOf L V₁, a * b = z := by
    intro z hz
    have hsup : SecA.xOne X (LOf L V₁) ⊔ X ⊓ LOf L V₁ = X :=
      le_antisymm (sup_le inf_le_left inf_le_left) hc.a
    have htop : (SecA.xOne X (LOf L V₁)).subgroupOf X ⊔ (X ⊓ LOf L V₁).subgroupOf X = ⊤ := by
      rw [← Subgroup.subgroupOf_sup inf_le_left inf_le_left, hsup, Subgroup.subgroupOf_self]
    have hz' : (⟨z, hz⟩ : ↥X) ∈
        (SecA.xOne X (LOf L V₁)).subgroupOf X ⊔ (X ⊓ LOf L V₁).subgroupOf X :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hz'
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, b, Subgroup.mem_subgroupOf.mp hb,
      congrArg Subtype.val hab⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hdec _ hdX
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [mul_one] at hab
    exact hwm (hab ▸ ha)
  have haL : a ∈ L := (h.cartan.1 ha.1).1
  obtain ⟨c, hc3, hac⟩ :=
    SecS.C11AmS.S12.exists_scalar_of_xOne hFb hN h1102 h.hyp h.v₁ h.v₂ h.cartan hSL3 D ha haL
  have hb3 : b ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(X ⊓ LOf L V₁)) (x := ⟨b, hb⟩)
    rw [hc.card₁] at this
    simpa using congrArg Subtype.val this
  have hθb : D.θ ⟨b, NatData3'.lOf_le hb.2⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨b, NatData3'.lOf_le hb.2⟩ : ↥L) ∈ D.θ.ker := h1
    rw [D.ker_eq, Subgroup.mem_subgroupOf] at h2
    exact hb1 (eq_one_of_odd hXodd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)) hb.1 h2)
  obtain ⟨v, hvV, hv1, hdv⟩ := exists_fixed_of_mul D hV₁V haL hb.2 hc3 hac hb3 hθb
  rw [hab] at hdv
  have hdvc : Commute (w * x₁ * w⁻¹) v := by
    show w * x₁ * w⁻¹ * v = v * (w * x₁ * w⁻¹)
    calc w * x₁ * w⁻¹ * v = w * x₁ * w⁻¹ * v * (w * x₁ * w⁻¹)⁻¹ * (w * x₁ * w⁻¹) := by group
      _ = v * (w * x₁ * w⁻¹) := by rw [hdv]
  have heU : w⁻¹ * v * w ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) := by
    have := mem_conjClosure (h.K_le_normalizer_V₁ (K.inv_mem hwK)) hvV
    simpa using this
  have heC : w⁻¹ * v * w ∈ Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hX₁z] at hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h1 := (hdvc.zpow_left k)
    rw [conj_zpow] at h1
    have h2 : x₁ ^ k = w⁻¹ * (w * x₁ ^ k * w⁻¹) * w := by group
    rw [h2]
    calc w⁻¹ * (w * x₁ ^ k * w⁻¹) * w * (w⁻¹ * v * w) = w⁻¹ * ((w * x₁ ^ k * w⁻¹) * v) * w := by
          group
      _ = w⁻¹ * (v * (w * x₁ ^ k * w⁻¹)) * w := by rw [h1.eq]
      _ = w⁻¹ * v * w * (w⁻¹ * (w * x₁ ^ k * w⁻¹) * w) := by group
  by_contra hall
  push Not at hall
  have hXv : ∀ z ∈ X, z * v = v * z := by
    intro z hz
    have hz' : w⁻¹ * z * w ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwN) z).mp hz
      simpa using this
    obtain ⟨a', ha', b', hb', hab'⟩ := hdec _ hz'
    have e1 : z = (w * a' * w⁻¹) * (w * b' * w⁻¹) := by
      calc z = w * (w⁻¹ * z * w) * w⁻¹ := by group
        _ = w * (a' * b') * w⁻¹ := by rw [hab']
        _ = _ := by group
    have c1 : Commute (w * a' * w⁻¹) v := by
      rw [hX₁z] at ha'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
      have := hdvc.zpow_left k
      rwa [conj_zpow] at this
    have c2 : Commute (w * b' * w⁻¹) v := by
      have h1 := hall b' hb' _ ⟨heU, heC⟩
      show w * b' * w⁻¹ * v = v * (w * b' * w⁻¹)
      calc w * b' * w⁻¹ * v = w * (b' * (w⁻¹ * v * w) * b'⁻¹) * b' * w⁻¹ := by group
        _ = w * (w⁻¹ * v * w) * b' * w⁻¹ := by rw [h1]
        _ = v * (w * b' * w⁻¹) := by group
    rw [e1]
    exact (c1.mul_left c2).eq
  exact hv1 (eq_one_of_commute_xOne hC hN hG2 hFb h1102 h1103 h hSL3 hvV fun x hx => hXv x hx.1)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
