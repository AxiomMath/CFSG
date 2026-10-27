module

public import CFSG.Quasithin.EmptyFaithful.SzC4NdEnv
public import CFSG.Quasithin.Background.FLc2UD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.InternalSec
open scoped commutatorElement IsMulCommutative

section VmainG2

variable {G : Type} [Group G] [Finite G] {L S R Yp Y₁ Y₂ Vp : Subgroup G}

theorem vmain_G2 (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    (E : Env4 L S R Yp Y₁ Y₂ Vp) {z : G} (hzV : z ∈ Vp) (hzB : ∀ b ∈ S ⊓ L, b * z * b⁻¹ = z)
    (hzY : ∃ y ∈ Y₁ ⊔ Y₂, y * z * y⁻¹ ≠ z) :
    (∀ w ∈ Vp, ∃ c ∈ Vp ⊓ Subgroup.centralizer (L : Set G), ∃ u ∈ ⁅Vp, L⁆, w = c * u) ∧
    (∀ u ∈ ⁅Vp, L⁆, u ∈ Subgroup.centralizer (L : Set G) → u = 1) ∧
    (∀ u ∈ ⁅Vp, L⁆, (∀ b ∈ S ⊓ L, b * u * b⁻¹ = u) → (∀ y ∈ Y₁ ⊔ Y₂, y * u * y⁻¹ = u) → u = 1) ∧
    ((∀ y ∈ Y₁, y * z * y⁻¹ = z) ∨ (∀ y ∈ Y₂, y * z * y⁻¹ = z) ∨ MSG2 L S Vp Yp Y₁ Y₂) := by
  classical
  have hcomm : IsMulCommutative ↥Vp := E.Vp_elem.1
  have hV2 : ∀ v : ↥Vp, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using E.Vp_elem.2 v v.2)
  have hLN := E.L_N
  have hYp₁ : Y₁ ≤ L := E.Y₁_Yp.trans E.Yp_L
  have hYp₂ : Y₂ ≤ L := E.Y₂_Yp.trans E.Yp_L
  have hY₁N : Y₁ ≤ Subgroup.normalizer (Vp : Set G) := hYp₁.trans hLN
  have hY₂N : Y₂ ≤ Subgroup.normalizer (Vp : Set G) := hYp₂.trans hLN
  have hYS₁ : S ≤ Subgroup.normalizer (Y₁ : Set G) := FLc.le_normalizer_of_conj_mem E.Y₁_S
  have hYS₂ : S ≤ Subgroup.normalizer (Y₂ : Set G) := FLc.le_normalizer_of_conj_mem E.Y₂_S
  have hSB : S ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, E.S_L hs⟩
  have hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (Vp : Set G)) := E.kerP
  have hF : Frame4 (autOn L Vp) (autOn (S ⊓ L) Vp) (autOn S Vp) (autOn Y₁ Vp) (autOn Y₂ Vp) := by
    refine ⟨Setup.isSylowTwoOf_autOn E.sylow hLN, autOn_le_autOn Vp inf_le_left,
      autOn_normal_of E.S_L, autOn_normal_of hSB, autOn_le_autOn_of_le hYp₁, autOn_normal_of hYS₁,
      ?_, autOn_le_autOn_of_le hYp₂, autOn_normal_of hYS₂, ?_, ?_⟩
    · obtain ⟨a, ha⟩ := E.Y₁_card
      exact card_form_autOn hY₁N (hker.to_le (inf_le_inf_right _ hYp₁)) ha
    · obtain ⟨a, ha⟩ := E.Y₂_card
      exact card_form_autOn hY₂N (hker.to_le (inf_le_inf_right _ hYp₂)) ha
    · have hYpN : Yp ≤ Subgroup.normalizer (Vp : Set G) := E.Yp_L.trans hLN
      have h9 := nine_dvd_autOn hYpN (hker.to_le (inf_le_inf_right _ E.Yp_L)) E.Yp_nine
      refine h9.trans (Subgroup.card_dvd_of_le ?_)
      rw [← CFSG.Quasithin.autOn_sup hY₁N hY₂N]
      exact autOn_le_autOn Vp E.Yp_Y
  have hAlt : Alt15127 (autOn L Vp) (commV (autOn L Vp)) := by
    obtain ⟨e⟩ := E.equiv4
    exact alt15127_of_b51 h51 hI16 hA8 hV2 E.b51
      (Or.inl (LRed4.isPSL_two_of_statedSL' (by norm_num) e))
  have hp2 := (h51 ↥Vp hV2 _ _ E.b51).2.1.2
  have hodd : Odd ((S ⊓ L).relIndex L) :=
    Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 E.sylow.2.2)
  have hUc : ∀ a ∈ Vp, ∀ b ∈ Vp, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hzfix : ∀ s ∈ S ⊓ L, ∀ z' ∈ Subgroup.zpowers z, s * z' * s⁻¹ = z' := by
    intro s hs z' hz'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
    have := hzB s hs
    calc s * z ^ k * s⁻¹ = (s * z * s⁻¹) ^ k := by rw [conj_zpow]
      _ = z ^ k := by rw [this]
  obtain ⟨u, hu, hfix⟩ := FLc.ud_decomp hLN hUc E.Vp_elem.2 hodd
    (Subgroup.zpowers_le.2 hzV) hzfix z (Subgroup.mem_zpowers z)
  have huVp : u ∈ Vp := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN hu
  have hbu : ∀ b ∈ S ⊓ L, b * u * b⁻¹ = u := by
    intro b hb
    have h1 := hfix b hb.2
    have h2 := hzB b hb
    calc b * u * b⁻¹ = (b * z * b⁻¹)⁻¹ * (b * (z * u) * b⁻¹) := by group
      _ = z⁻¹ * (z * u) := by rw [h2, h1]
      _ = u := by group
  have hzu : ∀ y ∈ L, y * u * y⁻¹ = u → y * z * y⁻¹ = z := by
    intro y hy h
    have h1 := hfix y hy
    calc y * z * y⁻¹ = (y * (z * u) * y⁻¹) * (y * u * y⁻¹)⁻¹ := by group
      _ = (z * u) * u⁻¹ := by rw [h1, h]
      _ = z := by group
  let u' : ↥Vp := ⟨u, huVp⟩
  have hcoe : ∀ g : Subgroup.normalizer (Vp : Set G),
      ((conjAct Vp g u' : ↥Vp) : G) = (g : G) * u * (g : G)⁻¹ := fun g =>
    Setup.coe_conjAct_apply g u'
  have hu'comm : u' ∈ commV (autOn L Vp) := by
    rw [commV_autOn_eq1527d hLN]
    exact hu
  have huB : ∀ b ∈ autOn (S ⊓ L) Vp, b u' = u' := by
    intro b hb
    obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hb
    exact Subtype.ext ((hcoe g).trans (hbu _ hg))
  have huY : ¬ ∀ y ∈ autOn Y₁ Vp ⊔ autOn Y₂ Vp, y u' = u' := by
    intro h
    obtain ⟨y, hy, hyz⟩ := hzY
    apply hyz
    have hyL : y ∈ L := sup_le hYp₁ hYp₂ hy
    have hyN : y ∈ Subgroup.normalizer (Vp : Set G) := hLN hyL
    have hmem : conjAct Vp ⟨y, hyN⟩ ∈ autOn Y₁ Vp ⊔ autOn Y₂ Vp := by
      rw [← CFSG.Quasithin.autOn_sup hY₁N hY₂N]
      exact Setup.mem_autOn_iff.2 ⟨⟨y, hyN⟩, hy, rfl⟩
    have h1 := congrArg Subtype.val (h _ hmem)
    rw [hcoe ⟨y, hyN⟩] at h1
    exact hzu y hyL h1
  obtain ⟨hsplit, hkey, htri⟩ := vmain2 hV2 hF E.Λne E.card_Λ hAlt hp2 u' hu'comm huB huY
  have hcommG : ∀ {a : G}, ∀ ha : a ∈ Vp, (⟨a, ha⟩ : ↥Vp) ∈ commV (autOn L Vp) ↔ a ∈ ⁅Vp, L⁆ := by
    intro a ha
    rw [commV_autOn_eq1527d hLN]
    exact Subgroup.mem_subgroupOf
  have hfixG : ∀ {a : G}, ∀ ha : a ∈ Vp, (⟨a, ha⟩ : ↥Vp) ∈ fixV (autOn L Vp) ↔
      a ∈ Subgroup.centralizer (L : Set G) := by
    intro a ha
    constructor
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := congrArg Subtype.val (h _ (conjAct_mem_autOn1527d hLN hl))
      rw [Setup.coe_conjAct_apply] at h1
      calc l * a = (l * a * l⁻¹) * l := by group
        _ = a * l := by rw [show l * a * l⁻¹ = a from h1]
    · intro h x hx
      obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hx
      apply Subtype.ext
      rw [Setup.coe_conjAct_apply]
      have := Subgroup.mem_centralizer_iff.1 h g hg
      calc (g : G) * a * (g : G)⁻¹ = a * g * (g : G)⁻¹ := by rw [← this]
        _ = a := by group
  have hsplitG : ∀ w ∈ Vp, ∃ c ∈ Vp ⊓ Subgroup.centralizer (L : Set G), ∃ u ∈ ⁅Vp, L⁆,
      w = c * u := by
    intro w hw
    have hmem : (⟨w, hw⟩ : ↥Vp) ∈ commV (autOn L Vp) ⊔ fixV (autOn L Vp) := by
      rw [hsplit.1]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hmem
    have hbG : (b : G) ∈ Subgroup.centralizer (L : Set G) := (hfixG b.2).1 (by simpa using hb)
    have haG : (a : G) ∈ ⁅Vp, L⁆ := (hcommG a.2).1 (by simpa using ha)
    refine ⟨(b : G), ⟨b.2, hbG⟩, (a : G), haG, ?_⟩
    have h1 : (a : G) * (b : G) = w := congrArg Subtype.val hab
    calc w = (a : G) * (b : G) := h1.symm
      _ = (b : G) * (a : G) := hUc _ a.2 _ b.2
  have hdirG : ∀ u0 ∈ ⁅Vp, L⁆, u0 ∈ Subgroup.centralizer (L : Set G) → u0 = 1 := by
    intro u0 hu0 hu0c
    have hu0V : u0 ∈ Vp := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN hu0
    have hmem : (⟨u0, hu0V⟩ : ↥Vp) ∈ commV (autOn L Vp) ⊓ fixV (autOn L Vp) :=
      ⟨(hcommG hu0V).2 hu0, (hfixG hu0V).2 hu0c⟩
    rw [hsplit.2] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  have hkeyG : ∀ u0 ∈ ⁅Vp, L⁆, (∀ b ∈ S ⊓ L, b * u0 * b⁻¹ = u0) →
      (∀ y ∈ Y₁ ⊔ Y₂, y * u0 * y⁻¹ = u0) → u0 = 1 := by
    intro u0 hu0 hB hY
    have hu0V : u0 ∈ Vp := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN hu0
    have := hkey ⟨u0, hu0V⟩ ((hcommG hu0V).2 hu0) (fun b hb => by
        obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hb
        exact Subtype.ext ((Setup.coe_conjAct_apply g _).trans (hB _ hg)))
      (fun y hy => by
        rw [← CFSG.Quasithin.autOn_sup hY₁N hY₂N] at hy
        obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hy
        exact Subtype.ext ((Setup.coe_conjAct_apply g _).trans (hY _ hg)))
    exact congrArg Subtype.val this
  refine ⟨hsplitG, hdirG, hkeyG, ?_⟩
  rcases htri with h1 | h2 | hms
  · refine Or.inl fun y hy => ?_
    have hyL : y ∈ L := hYp₁ hy
    have h := h1 (conjAct Vp ⟨y, hLN hyL⟩) (Setup.mem_autOn_iff.2 ⟨⟨y, hLN hyL⟩, hy, rfl⟩)
    have h' := congrArg Subtype.val h
    rw [hcoe ⟨y, hLN hyL⟩] at h'
    exact hzu y hyL h'
  · refine Or.inr (Or.inl fun y hy => ?_)
    have hyL : y ∈ L := hYp₂ hy
    have h := h2 (conjAct Vp ⟨y, hLN hyL⟩) (Setup.mem_autOn_iff.2 ⟨⟨y, hLN hyL⟩, hy, rfl⟩)
    have h' := congrArg Subtype.val h
    rw [hcoe ⟨y, hLN hyL⟩] at h'
    exact hzu y hyL h'
  · exact Or.inr (Or.inr (msg2_of_msData2 E hms))

end VmainG2

end CFSG.Quasithin.A38c10
