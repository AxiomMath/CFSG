module

public import CFSG.Quasithin.Background.A1a
import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Assembly.Subnormal
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin

open scoped Pointwise

variable {G : Type*} [Group G]

private theorem isSubnormal_le {L Y : Subgroup G} (h : CFSG.Open.IsSubnormal L Y) : L ≤ Y :=
  h.le

private theorem isSubnormal_subgroupOf {L K : Subgroup G} (h : CFSG.Open.IsSubnormal L K)
    (Y : Subgroup G) : CFSG.Open.IsSubnormal (L.subgroupOf Y) (K.subgroupOf Y) :=
  h.comap Y.subtype

theorem isSubnormal_subgroupOf_top_iff {L Y : Subgroup G} (hle : L ≤ Y) :
    CFSG.Open.IsSubnormal (L.subgroupOf Y) ⊤ ↔ CFSG.Open.IsSubnormal L Y := by
  constructor
  · intro h
    have hmapped := CFSG.ComponentClassification.Components.chain_map Y.subtype h
    simpa only [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_top,
      Subgroup.range_subtype] using hmapped
  · intro h
    simpa only [Subgroup.subgroupOf_self] using isSubnormal_subgroupOf h Y

theorem isComponentOf_iff_subgroupOf {K Y : Subgroup G} :
    CFSG.Open.IsComponentOf K Y ↔ K ≤ Y ∧ CFSG.Open.IsComponentOf (K.subgroupOf Y) ⊤ := by
  constructor
  · rintro ⟨hle, hsub, hqs⟩
    exact ⟨hle, le_top, (isSubnormal_subgroupOf_top_iff hle).mpr hsub,
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (Subgroup.subgroupOfEquivOfLe hle) hqs⟩
  · rintro ⟨hle, _, hsub, hqs⟩
    exact ⟨hle, (isSubnormal_subgroupOf_top_iff hle).mp hsub,
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (Subgroup.subgroupOfEquivOfLe hle).symm hqs⟩

private theorem subgroupOf_map_subtype' (Y : Subgroup G) (c : Subgroup Y) :
    (c.map Y.subtype).subgroupOf Y = c :=
  Subgroup.comap_map_eq_self_of_injective Y.subtype_injective c

private theorem quasithinGenFitting_eq_map (Y : Subgroup G) :
    CFSG.Open.quasithinGenFitting Y =
      (CFSG.ComponentClassification.GeneralizedFitting.subgroup Y).map Y.subtype := by
  unfold CFSG.Open.quasithinGenFitting; simp only [CFSG.ComponentClassification.GeneralizedFitting.subgroup.eq_sup]
  rw [Subgroup.map_sup]
  congr 1
  ·
    simp only [CFSG.ComponentClassification.Fitting.subgroup.eq_sSup]
    apply le_antisymm
    · refine sSup_le fun N hN => ?_
      obtain ⟨hNY, hNn, hNnil⟩ := hN
      have hnil : Group.IsNilpotent (N.subgroupOf Y) :=
        (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hNY)).mpr hNnil
      calc N = (N.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hNY).symm
        _ ≤ _ := Subgroup.map_mono (le_sSup (show N.subgroupOf Y ∈
            {c : Subgroup Y | c.Normal ∧ Group.IsNilpotent c} from ⟨hNn, hnil⟩))
    · rw [(Subgroup.gc_map_comap Y.subtype).l_sSup]
      refine iSup₂_le fun c hc => ?_
      obtain ⟨hcn, hcnil⟩ := hc
      refine le_sSup ?_
      refine ⟨Subgroup.map_subtype_le c, ?_, ?_⟩
      · rw [subgroupOf_map_subtype']
        exact hcn
      · exact (Group.isNilpotent_congr (c.equivMapOfInjective Y.subtype Y.subtype_injective)).mp
          hcnil
  ·
    simp only [CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
    apply le_antisymm
    · refine sSup_le fun K hK => ?_
      obtain ⟨hKY, hK'⟩ := isComponentOf_iff_subgroupOf.mp hK
      calc K = (K.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hKY).symm
        _ ≤ _ := Subgroup.map_mono (le_sSup hK')
    · rw [(Subgroup.gc_map_comap Y.subtype).l_sSup]
      refine iSup₂_le fun c hc => le_sSup ?_
      refine isComponentOf_iff_subgroupOf.mpr ⟨Subgroup.map_subtype_le c, ?_⟩
      rw [subgroupOf_map_subtype']
      exact hc

theorem quasithinGenFitting_le (Y : Subgroup G) : CFSG.Open.quasithinGenFitting Y ≤ Y := by
  rw [quasithinGenFitting_eq_map]
  exact Subgroup.map_subtype_le _

theorem normalizer_le_normalizer_quasithinGenFitting (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer (CFSG.Open.quasithinGenFitting Y : Set G) := by
  have := CFSG.ComponentClassification.GeneralizedFitting.characteristic (G := Y)
  rw [quasithinGenFitting_eq_map]
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

theorem le_normalizer_quasithinGenFitting (Y : Subgroup G) :
    Y ≤ Subgroup.normalizer (CFSG.Open.quasithinGenFitting Y : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_quasithinGenFitting Y)

theorem centralizer_quasithinGenFitting_le [Finite G] (Y : Subgroup G) :
    Y ⊓ Subgroup.centralizer (CFSG.Open.quasithinGenFitting Y : Set G) ≤
      CFSG.Open.quasithinGenFitting Y := by
  intro x hx
  rw [quasithinGenFitting_eq_map]
  have hy : (⟨x, hx.1⟩ : Y) ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.GeneralizedFitting.subgroup Y : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hx.2 (u : G)
      (by rw [quasithinGenFitting_eq_map]; exact ⟨u, hu, rfl⟩)
  exact ⟨_, CFSG.ComponentClassification.GeneralizedFitting.centralizer_le Y hy, rfl⟩


theorem quasithinGenFitting_eq_pCoreOf_iff [Finite G] (Y : Subgroup G) (p : ℕ) [Fact p.Prime] :
    CFSG.Open.quasithinGenFitting Y = CFSG.Open.pCoreOf p Y ↔
      Y ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf p Y : Set G) ≤ CFSG.Open.pCoreOf p Y := by
  rw [← centralizer_pCore_le_iff_pCoreOf p Y, quasithinGenFitting_eq_map]
  unfold CFSG.Open.pCoreOf
  rw [(Subgroup.map_injective Y.subtype_injective).eq_iff,
    ← CFSG.generalizedFitting_eq_componentClassification]
  exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore Y p).symm

theorem centralizer_of_centralizes_genFitting [Finite G] {p : ℕ} [Fact p.Prime] {P Y : Subgroup G}
    (hP : IsPGroup p P) (hPY : P ≤ Subgroup.normalizer (Y : Set G))
    (hY : CFSG.Open.pCoreOf p Y = ⊥)
    (hPF : P ≤ Subgroup.centralizer (CFSG.Open.quasithinGenFitting Y : Set G)) :
    P ≤ Subgroup.centralizer (Y : Set G) := by
  obtain ⟨F, hF⟩ : ∃ F : Subgroup G, F = CFSG.Open.quasithinGenFitting Y := ⟨_, rfl⟩
  rw [← hF] at hPF
  have hFY : F ≤ Y := hF ▸ quasithinGenFitting_le Y
  have hYF : Y ≤ Subgroup.normalizer (F : Set G) := hF ▸ le_normalizer_quasithinGenFitting Y
  have hPF' : P ≤ Subgroup.normalizer (F : Set G) :=
    hPY.trans (hF ▸ normalizer_le_normalizer_quasithinGenFitting Y)
  have hCY : Y ⊓ Subgroup.centralizer (F : Set G) ≤ F := hF ▸ centralizer_quasithinGenFitting_le Y
  have hPc : ∀ u ∈ P, ∀ f ∈ F, f * u = u * f := fun u hu f hf =>
    Subgroup.mem_centralizer_iff.mp (hPF hu) f hf
  have hcY : ∀ y ∈ Y, ∀ u ∈ P, y * u * y⁻¹ * u⁻¹ ∈ Y := by
    intro y hy u hu
    have h1 : u * y⁻¹ * u⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hPY hu) y⁻¹).mp (Y.inv_mem hy)
    have := Y.mul_mem hy h1
    simpa [mul_assoc] using this
  have hcF : ∀ y ∈ Y, ∀ u ∈ P, y * u * y⁻¹ * u⁻¹ ∈ F := by
    intro y hy u hu
    refine hCY ⟨hcY y hy u hu, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
    have hf₁ : y⁻¹ * f * y ∈ F := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hYF (Y.inv_mem hy)) f).mp hf
    have hu1 : u⁻¹ * f * u = f := by
      have := hPc u hu f hf
      calc u⁻¹ * f * u = u⁻¹ * (f * u) := by group
        _ = u⁻¹ * (u * f) := by rw [this]
        _ = f := by group
    have hu2 : u * (y⁻¹ * f * y) * u⁻¹ = y⁻¹ * f * y := by
      have := hPc u hu _ hf₁
      calc u * (y⁻¹ * f * y) * u⁻¹ = (u * (y⁻¹ * f * y)) * u⁻¹ := by group
        _ = ((y⁻¹ * f * y) * u) * u⁻¹ := by rw [← this]
        _ = y⁻¹ * f * y := by group
    have hconj : y * u * y⁻¹ * u⁻¹ * f * (y * u * y⁻¹ * u⁻¹)⁻¹ = f := by
      calc y * u * y⁻¹ * u⁻¹ * f * (y * u * y⁻¹ * u⁻¹)⁻¹
          = y * (u * (y⁻¹ * (u⁻¹ * f * u) * y) * u⁻¹) * y⁻¹ := by group
        _ = y * (u * (y⁻¹ * f * y) * u⁻¹) * y⁻¹ := by rw [hu1]
        _ = y * (y⁻¹ * f * y) * y⁻¹ := by rw [hu2]
        _ = f := by group
    calc f * (y * u * y⁻¹ * u⁻¹) = (y * u * y⁻¹ * u⁻¹ * f * (y * u * y⁻¹ * u⁻¹)⁻¹) *
          (y * u * y⁻¹ * u⁻¹) := by rw [hconj]
      _ = y * u * y⁻¹ * u⁻¹ * f := by group

  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = F ⊔ P := ⟨_, rfl⟩
  have hDset : (D : Set G) = (F : Set G) * (P : Set G) := by
    rw [hD]; exact Subgroup.coe_mul_of_right_le_normalizer_left F P hPF'
  have hFD : F ≤ D := hD ▸ le_sup_left
  have hPD : P ≤ D := hD ▸ le_sup_right
  have hFnP : F ≤ Subgroup.normalizer (P : Set G) := fun f hf =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun u hu => (hPc u hu f hf).symm)
  have hDP : D ≤ Subgroup.normalizer (P : Set G) := by
    rw [hD]
    exact sup_le hFnP Subgroup.le_normalizer
  have hPR : P ≤ CFSG.Open.pCoreOf p D :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p hPD hDP hP
  have hRP : CFSG.Open.pCoreOf p D ≤ P := by
    intro r hr
    have hrD : r ∈ D := CFSG.LieType.BorelTits.pCoreOf_le p D hr
    have hr' : r ∈ (F : Set G) * (P : Set G) := hDset ▸ hrD
    obtain ⟨f, hf, u, hu, rfl⟩ := hr'
    have hfR : f ∈ CFSG.Open.pCoreOf p D := by
      have : f = (f * u) * u⁻¹ := by group
      rw [this]
      exact (CFSG.Open.pCoreOf p D).mul_mem hr ((CFSG.Open.pCoreOf p D).inv_mem (hPR hu))
    have hnormR : D ≤ Subgroup.normalizer (CFSG.Open.pCoreOf p D : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf p D
    have h1 : CFSG.Open.pCoreOf p D ⊓ F ≤ CFSG.Open.pCoreOf p F :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p inf_le_right
        (A1a.le_normalizer_inf (hFD.trans hnormR) Subgroup.le_normalizer)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup p D).to_le inf_le_left)
    have h2 : CFSG.Open.pCoreOf p F ≤ CFSG.Open.pCoreOf p Y :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
        ((CFSG.LieType.BorelTits.pCoreOf_le p F).trans hFY)
        (hYF.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p F))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup p F)
    have hf1 : f = 1 := by
      have := h2 (h1 ⟨hfR, hf⟩)
      rw [hY] at this
      exact Subgroup.mem_bot.mp this
    rw [hf1]
    simpa using hu
  have hRPeq : CFSG.Open.pCoreOf p D = P := le_antisymm hRP hPR
  have hYD : ∀ y ∈ Y, ∀ x ∈ D, y * x * y⁻¹ ∈ D := by
    intro y hy x hx
    have hx' : x ∈ (F : Set G) * (P : Set G) := hDset ▸ hx
    obtain ⟨f, hf, u, hu, rfl⟩ := hx'
    have hf1 : y * f * y⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp (hYF hy) f).mp hf
    have hc := hcF y hy u hu
    have : y * (f * u) * y⁻¹ = (y * f * y⁻¹ * (y * u * y⁻¹ * u⁻¹)) * u := by group
    rw [this]
    exact D.mul_mem (D.mul_mem (hFD hf1) (hFD hc)) (hPD hu)
  have hYN : Y ≤ Subgroup.normalizer (D : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hYD y hy x, fun h => ?_⟩
    have := hYD y⁻¹ (Y.inv_mem hy) _ h
    simpa [mul_assoc] using this
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := by
    have := hYN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p D)
    rwa [hRPeq] at this
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hc1 : y * u * y⁻¹ * u⁻¹ ∈ P := by
    have h1 : y * u * y⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hYP hy) u).mp hu
    exact P.mul_mem h1 (P.inv_mem hu)
  have hc2 := hcY y hy u hu
  have hPYp : P ⊓ Y ≤ CFSG.Open.pCoreOf p Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p inf_le_right
      (A1a.le_normalizer_inf hYP Subgroup.le_normalizer) (hP.to_le inf_le_left)
  have h3 := hPYp ⟨hc1, hc2⟩
  rw [hY, Subgroup.mem_bot] at h3
  calc y * u = (y * u * y⁻¹ * u⁻¹) * u * y := by group
    _ = u * y := by rw [h3]; group

end CFSG.Quasithin
