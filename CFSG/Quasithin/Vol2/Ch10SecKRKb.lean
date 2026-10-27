module

public import CFSG.Quasithin.Vol2.Ch10SecKRKa
public import CFSG.Quasithin.Background.A3StructureListNative
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch10SecKRPb
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRK

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {Γ : Type} [Group Γ] [Finite Γ]

structure K1Hyp (H R J L V₁ : Subgroup Γ) : Prop where
  sqtk : SQTKGroup ↥H
  syl : IsSylowTwoOf R H
  comp : J ∈ cComp H
  quasi : CFSG.IsQuasisimple ↥J
  lfam : L ∈ lFamily R
  le : L ≤ J
  ne : L ≠ J
  nR : R ≤ Subgroup.normalizer (L : Set Γ)
  vle : V₁ ≤ L
  vel : IsElemAbelian 2 V₁
  vn : L ⊔ R ≤ Subgroup.normalizer (V₁ : Set Γ)
  vc : ⁅V₁, L⁆ = V₁
  vcent : pCoreOf 2 L ≤ Subgroup.centralizer (V₁ : Set Γ)
  vJ : J ⊓ Subgroup.normalizer (V₁ : Set Γ) ≤ Subgroup.normalizer (L : Set Γ)

namespace K1Hyp

variable {H R J L V₁ : Subgroup Γ} (h : K1Hyp H R J L V₁)
include h

theorem l_ne_bot : L ≠ ⊥ := ne_bot_of_mem_cComp (show L ∈ cComp (L ⊔ R) from h.lfam)

theorem l_perfect : ⁅L, L⁆ = L := perfect_of_mem_cComp (show L ∈ cComp (L ⊔ R) from h.lfam)

theorem pCore_le_center : CFSG.pCore 2 ↥J ≤ Subgroup.center ↥J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups h.quasi CFSG.pCore_normal with ht | hc
  · exfalso
    apply not_isSolvable_of_mem_cComp h.comp
    have hJ2 : IsPGroup 2 ↥J := fun g => by
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := ↥J) (p := 2)) ⟨g, ht ▸ Subgroup.mem_top g⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    have := hJ2.isNilpotent
    infer_instance
  · exact hc

theorem not_le_center (hc : L.subgroupOf J ≤ Subgroup.center ↥J) : False := by
  apply h.l_ne_bot
  apply SecB.KRP.eq_bot_of_subgroupOf_eq_bot h.le
  rw [← SecB.KRP.perfect_subgroupOf h.le h.l_perfect,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y _
  exact ((Subgroup.mem_center_iff.mp (hc hx)) y)

theorem not_normal (hn : (L.subgroupOf J).Normal) : False := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups h.quasi hn with ht | hc
  · apply h.ne
    refine le_antisymm h.le fun x hx => ?_
    have : (⟨x, hx⟩ : ↥J) ∈ L.subgroupOf J := by rw [ht]; trivial
    exact this
  · exact h.not_le_center hc

theorem not_le_normalizer (hJ : J ≤ Subgroup.normalizer (L : Set Γ)) : False :=
  h.not_normal ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hJ g.2) n).mp hn⟩

theorem v_ne_bot : V₁ ≠ ⊥ := by
  intro hV
  apply h.not_le_normalizer
  have h1 : Subgroup.normalizer (V₁ : Set Γ) = ⊤ := by
    rw [hV]
    exact Subgroup.normalizer_eq_top (H := (⊥ : Subgroup Γ))
  have h2 := h.vJ
  rwa [h1, inf_top_eq] at h2

theorem isSQTKCat_J : CFSG.SectionRank.IsSQTKCat ↥J := by
  have hH := SQTKGroup.isSQTKCat h.sqtk
  have hJH : J ≤ H := le_of_mem_cComp h.comp
  exact CFSG.SectionRank.IsSQTKCat.of_le hJH hH

end K1Hyp

abbrev QJ (J : Subgroup Γ) : Type := ↥J ⧸ CFSG.pCore 2 ↥J

abbrev piJ (J : Subgroup Γ) : ↥J →* QJ J := QuotientGroup.mk' (CFSG.pCore 2 ↥J)

abbrev imJ (J A : Subgroup Γ) : Subgroup (QJ J) := (A.subgroupOf J).map (piJ J)

namespace K1Hyp

variable {H R J L V₁ : Subgroup Γ} (h : K1Hyp H R J L V₁)
include h

theorem sqtkHyp_QJ : Vol2Native.SQTKHypCat (QJ J) :=
  Vol2Native.SQTKHypCat.quotient_pCore ↥J h.isSQTKCat_J

theorem quasi_QJ : CFSG.IsQuasisimple (QJ J) :=
  (CFSG.LocalCores.quasisimple_central_quotient h.quasi _ h.pCore_le_center).1

theorem sylow_T : IsSylowTwoOf (imJ J R) ⊤ := by
  have hRJ : IsSylowTwoOf (R ⊓ J) J :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp h.comp) h.syl
  have h1 : IsSylowTwoOf ((R ⊓ J).subgroupOf J) ⊤ := by
    rw [A312.isSylowTwoOf_top_iff_map, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    exact hRJ
  have h2 : (R ⊓ J).subgroupOf J = R.subgroupOf J := Subgroup.inf_subgroupOf_right R J
  show IsSylowTwoOf ((R.subgroupOf J).map (piJ J)) ⊤
  rw [← h2]
  exact A312.isSylowTwoOf_top_map (piJ J) (QuotientGroup.mk'_surjective _) h1

omit [Finite Γ] h in
theorem isPGroup_ker_piJ : IsPGroup 2 (piJ J).ker := by
  rw [QuotientGroup.ker_mk']
  exact CFSG.pCore_isPGroup

theorem lfam_B : imJ J L ∈ lFamily (imJ J R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : L ∈ cComp (L ⊔ R) := h.lfam
  have hL1 : L ∈ cComp (L ⊔ (R ⊓ J)) :=
    cComp_mem_of_le hL le_sup_left (sup_le_sup_left inf_le_left L)
  have h2 := A312.mem_cComp_subgroupOf (L := J) (sup_le h.le inf_le_right) hL1
  rw [Subgroup.subgroupOf_sup h.le inf_le_right, Subgroup.inf_subgroupOf_right] at h2
  have hsolv : Group.IsSolvable ↥((piJ J).ker ⊓ (L.subgroupOf J ⊔ R.subgroupOf J)) := by
    have := (isPGroup_ker_piJ (J := J)).isNilpotent
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : (piJ J).ker ⊓ _ ≤ (piJ J).ker))
      (Subgroup.inclusion_injective _)
  have h3 := A312.map_mem_cComp (piJ J) hsolv h2
  rwa [Subgroup.map_sup] at h3

theorem le_normalizer_B : imJ J R ≤ Subgroup.normalizer (imJ J L : Set (QJ J)) := by
  refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map (piJ J))
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact Subgroup.mem_normalizer_iff.mp (h.nR (Subgroup.mem_subgroupOf.mp hs)) (x : Γ)

theorem B_ne_top : imJ J L ≠ ⊤ := by
  intro htop
  apply h.not_normal
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨l, hl, hlg⟩ : piJ J g ∈ imJ J L := by rw [htop]; trivial
  have hz : l⁻¹ * g ∈ Subgroup.center ↥J := by
    apply h.pCore_le_center
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥J), MonoidHom.mem_ker, map_mul, map_inv, hlg,
      inv_mul_cancel]
  have hg : g = l * (l⁻¹ * g) := by group
  have hzc := Subgroup.mem_center_iff.mp hz n
  have : g * n * g⁻¹ = l * n * l⁻¹ := by
    calc g * n * g⁻¹ = l * ((l⁻¹ * g) * n * (l⁻¹ * g)⁻¹) * l⁻¹ := by group
      _ = l * n * l⁻¹ := by rw [← hzc]; group
  rw [this]
  exact (L.subgroupOf J).mul_mem ((L.subgroupOf J).mul_mem hl hn) ((L.subgroupOf J).inv_mem hl)

omit [Finite Γ] h in
theorem isPGroup_ker_restr :
    IsPGroup 2 ((piJ J).subgroupMap (L.subgroupOf J)).ker := by
  intro x
  have hx : ((x : ↥(L.subgroupOf J)) : ↥J) ∈ CFSG.pCore 2 ↥J := by
    have h1 : piJ J ((x : ↥(L.subgroupOf J)) : ↥J) = 1 := congrArg Subtype.val x.2
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥J) (p := 2)) ⟨_, hx⟩
  exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩

noncomputable def modO2B : ModO2 (imJ J L) ≃* ModO2 L :=
  (modO2EquivOfSurjective (MonoidHom.subgroupMap_surjective _ _) isPGroup_ker_restr).symm.trans
    (A312.modO2Equiv (Subgroup.subgroupOfEquivOfLe h.le))

end K1Hyp

end CFSG.Quasithin.Vol2.Ch10.SecC.KRK
