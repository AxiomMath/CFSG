module

public import CFSG.RankThree.PartTwo.Sec15.ThmCDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec15.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmC

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem thmc_mem_center_quot {P : Type} [Group P] (N : Subgroup P) [N.Normal] (p : P) :
    (QuotientGroup.mk p : P ⧸ N) ∈ Subgroup.center (P ⧸ N) ↔ ∀ q : P, ⁅p, q⁆ ∈ N := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h q
    have h1 : ⁅(QuotientGroup.mk p : P ⧸ N), (QuotientGroup.mk q : P ⧸ N)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (h (QuotientGroup.mk q)).symm
    exact (QuotientGroup.eq_one_iff ⁅p, q⁆).mp
      ((map_commutatorElement (f := QuotientGroup.mk' N) (g₁ := p) (g₂ := q)).trans h1)
  · intro h g
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 : ⁅(QuotientGroup.mk p : P ⧸ N), (QuotientGroup.mk q : P ⧸ N)⁆ = 1 :=
      (map_commutatorElement (f := QuotientGroup.mk' N) (g₁ := p) (g₂ := q)).symm.trans
        ((QuotientGroup.eq_one_iff ⁅p, q⁆).mpr (h q))
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

private theorem thmc_grun {P : Type} [Group P] [Group.IsPerfect P] (V D : Subgroup P) [D.Normal]
    (hVD : ∀ v ∈ V, ∀ q : P, ⁅v, q⁆ ∈ D) (x : P) (hx : ∀ q : P, ⁅x, q⁆ ∈ V) (q : P) :
    ⁅x, q⁆ ∈ D := by
  have hcen : (QuotientGroup.mk x : P ⧸ D) ∈ Subgroup.upperCentralSeries (P ⧸ D) 2 := by
    refine (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mpr fun y => ?_
    rw [Subgroup.upperCentralSeries_one]
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
    have hmk : ⁅(QuotientGroup.mk x : P ⧸ D), (QuotientGroup.mk r : P ⧸ D)⁆
        = (QuotientGroup.mk' D) ⁅x, r⁆ :=
      (map_commutatorElement (f := QuotientGroup.mk' D) (g₁ := x) (g₂ := r)).symm
    rw [hmk]
    exact (thmc_mem_center_quot D _).mpr fun s => hVD _ (hx r) s
  rw [Group.IsPerfect.upperCentralSeries_eq_center (G := P ⧸ D) (n := 2) two_ne_zero] at hcen
  exact (thmc_mem_center_quot D x).mp hcen q

private theorem thmc_two_bound {P : Type} [Group P] [Finite P] [Group.IsPerfect P]
    (V D : Subgroup P) [V.Normal] [D.Normal] (hDV : D ≤ V)
    (hVD : ∀ v ∈ V, ∀ q : P, ⁅v, q⁆ ∈ D) (hV2 : IsPGroup 2 ↥V)
    (hM : TwoMultLeTwo ((P ⧸ V) ⧸ Subgroup.center (P ⧸ V))) :
    ∀ u ∈ V, ∀ v ∈ V, u ∉ D → v ∉ D → u⁻¹ * v ∈ D := by
  let F : P →* (P ⧸ V) ⧸ Subgroup.center (P ⧸ V) :=
    (QuotientGroup.mk' (Subgroup.center (P ⧸ V))).comp (QuotientGroup.mk' V)
  let π : P →* (P ⧸ D) ⧸ Subgroup.center (P ⧸ D) :=
    (QuotientGroup.mk' (Subgroup.center (P ⧸ D))).comp (QuotientGroup.mk' D)
  have hF : Function.Surjective F :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = F.ker := by
    ext p
    have h1 : π p = 1 ↔ (QuotientGroup.mk p : P ⧸ D) ∈ Subgroup.center (P ⧸ D) :=
      QuotientGroup.eq_one_iff _
    have h2 : F p = 1 ↔ (QuotientGroup.mk p : P ⧸ V) ∈ Subgroup.center (P ⧸ V) :=
      QuotientGroup.eq_one_iff _
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, h1, h2]
    constructor
    · intro h
      exact (thmc_mem_center_quot V p).mpr fun q => hDV ((thmc_mem_center_quot D p).mp h q)
    · intro h
      exact (thmc_mem_center_quot D p).mpr fun q =>
        thmc_grun V D hVD p ((thmc_mem_center_quot V p).mp h) q
  let iso : ((P ⧸ D) ⧸ Subgroup.center (P ⧸ D)) ≃* ((P ⧸ V) ⧸ Subgroup.center (P ⧸ V)) :=
    (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective F hF))
  let Z : Subgroup (P ⧸ D) := V.map (QuotientGroup.mk' D)
  have hZc : Z ≤ Subgroup.center (P ⧸ D) := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hz
    exact (thmc_mem_center_quot D v).mpr (hVD v hv)
  have hZ2 : IsPGroup 2 ↥Z := by
    rintro ⟨z, hz⟩
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨k, hk⟩ := hV2 ⟨v, hv⟩
    have hv' : v ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨k, Subtype.ext ?_⟩
    show (QuotientGroup.mk' D v) ^ 2 ^ k = 1
    rw [← map_pow, hv', map_one]
  have hcard : Nat.card ↥Z ≤ 2 := hM (P ⧸ D) inferInstance ⟨iso⟩ Z hZc hZ2
  intro u hu v hv hun hvn
  by_contra hne
  have hu1 : (1 : P ⧸ D) ≠ QuotientGroup.mk u :=
    fun h => hun ((QuotientGroup.eq_one_iff u).mp h.symm)
  have hv1 : (1 : P ⧸ D) ≠ QuotientGroup.mk v :=
    fun h => hvn ((QuotientGroup.eq_one_iff v).mp h.symm)
  have huv : (QuotientGroup.mk u : P ⧸ D) ≠ QuotientGroup.mk v :=
    fun h => hne (QuotientGroup.eq.mp h)
  let f : Fin 3 → ↥Z := ![⟨1, Z.one_mem⟩, ⟨QuotientGroup.mk u, Subgroup.mem_map_of_mem _ hu⟩,
    ⟨QuotientGroup.mk v, Subgroup.mem_map_of_mem _ hv⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hval := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact absurd hval hu1
      | exact absurd hval.symm hu1
      | exact absurd hval hv1
      | exact absurd hval.symm hv1
      | exact absurd hval huv
      | exact absurd hval.symm huv
  have h3 := Nat.card_le_card_of_injective f hf
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  omega

private theorem thmc_conj_mem {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    {y : G} (hy : y ∈ H) : g⁻¹ * y * g ∈ H := by
  have h := Subgroup.mem_normalizer_iff.mp (inv_mem hg) y
  rw [inv_inv] at h
  exact h.mp hy

private theorem thmc_conj_comm {Y : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    ∀ x ∈ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆, g⁻¹ * x * g ∈ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ := by
  have hgV : g ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hg
  let c : G →* G := MonoidHom.mk' (fun x => g⁻¹ * x * g) (fun a b => by simp [mul_assoc])
  have hc : ∀ x, c x = g⁻¹ * x * g := fun x => rfl
  have hcomm : ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ ≤ (⁅CFSG.Open.pCoreOf 2 Y, Y⁆).comap c := by
    rw [Subgroup.commutator_le]
    intro v hv y hy
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator
      (by rw [hc]; exact thmc_conj_mem hgV hv) (by rw [hc]; exact thmc_conj_mem hg hy)
  intro x hx
  have h := Subgroup.mem_comap.mp (hcomm hx)
  rwa [hc] at h

private theorem thmc_G_elt {Y : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G))
    (hVD2 : ∀ u ∈ CFSG.Open.pCoreOf 2 Y, ∀ v ∈ CFSG.Open.pCoreOf 2 Y,
      u ∉ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ → v ∉ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ →
        u⁻¹ * v ∈ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆)
    {v : G} (hv : v ∈ CFSG.Open.pCoreOf 2 Y) : ⁅v, g⁆ ∈ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ := by
  have hg'V : g⁻¹ ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) :=
    inv_mem (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hg)
  have hg' : g⁻¹ ∈ Subgroup.normalizer (Y : Set G) := inv_mem hg
  have hcomm := thmc_conj_comm hg
  have hcomm' := thmc_conj_comm hg'
  have hVD3 : ∀ a ∈ CFSG.Open.pCoreOf 2 Y, ∀ b ∈ CFSG.Open.pCoreOf 2 Y,
      a ∉ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ → b ∉ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ →
        a * b⁻¹ ∈ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ := by
    intro a ha b hb haD hbD
    by_contra ht
    have h1 := hVD2 a ha (a * b⁻¹) (mul_mem ha (inv_mem hb)) haD ht
    rw [show a⁻¹ * (a * b⁻¹) = b⁻¹ by group] at h1
    have h2 := inv_mem h1
    rw [inv_inv] at h2
    exact hbD h2
  have hw : (g⁻¹)⁻¹ * v * g⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := thmc_conj_mem hg'V hv
  have hrw : v * g * v⁻¹ * g⁻¹ = v * ((g⁻¹)⁻¹ * v * g⁻¹)⁻¹ := by group
  rw [commutatorElement_def, hrw]
  by_cases hvD : v ∈ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆
  · exact mul_mem hvD (inv_mem (hcomm' v hvD))
  · have hwD : (g⁻¹)⁻¹ * v * g⁻¹ ∉ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ := by
      intro h
      apply hvD
      have h2 := hcomm _ h
      rwa [show g⁻¹ * ((g⁻¹)⁻¹ * v * g⁻¹) * g = v by group] at h2
    exact hVD3 v hv _ hw hvD hwD

theorem lemma9_of {A : Subgroup G} {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A))
    (hperf : Group.IsPerfect ↥Y)
    (hodd : Odd (Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))))
    (hM : TwoMultLeTwo ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)))
    {e : G} (he : e ∈ Subgroup.normalizer (Y : Set G)) (he3 : IsPGroup 3 ↥(Subgroup.zpowers e)) :
    ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers e⁆ ≤ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ := by
  have hV2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥Y) := CFSG.pCore_isPGroup
  have hY2 := thmc_two_bound (CFSG.pCore 2 ↥Y) ⁅CFSG.pCore 2 ↥Y, ⊤⁆
    (Subgroup.commutator_le_left _ _)
    (fun v hv q => Subgroup.commutator_mem_commutator hv (Subgroup.mem_top q)) hV2 hM
  have hmapTop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    ext x
    constructor
    · rintro ⟨z, -, rfl⟩
      exact z.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hD : (⁅CFSG.pCore 2 ↥Y, ⊤⁆ : Subgroup ↥Y).map Y.subtype
      = ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ := by
    rw [Subgroup.map_commutator, hmapTop]
    rfl
  have hVD2 : ∀ u ∈ CFSG.Open.pCoreOf 2 Y, ∀ v ∈ CFSG.Open.pCoreOf 2 Y,
      u ∉ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ → v ∉ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ →
        u⁻¹ * v ∈ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ := by
    intro u hu v hv hun hvn
    have hu' : u ∈ (CFSG.pCore 2 ↥Y).map Y.subtype := hu
    have hv' : v ∈ (CFSG.pCore 2 ↥Y).map Y.subtype := hv
    obtain ⟨U, hU, rfl⟩ := Subgroup.mem_map.mp hu'
    obtain ⟨W, hW, rfl⟩ := Subgroup.mem_map.mp hv'
    rw [← hD] at hun hvn ⊢
    have hUn : U ∉ ⁅CFSG.pCore 2 ↥Y, ⊤⁆ := fun h => hun (Subgroup.mem_map_of_mem _ h)
    have hWn : W ∉ ⁅CFSG.pCore 2 ↥Y, ⊤⁆ := fun h => hvn (Subgroup.mem_map_of_mem _ h)
    have h := Subgroup.mem_map_of_mem Y.subtype (hY2 U hU W hW hUn hWn)
    rwa [map_mul, map_inv] at h
  refine Subgroup.commutator_le.mpr fun v hv g hg => ?_
  exact thmc_G_elt ((Subgroup.zpowers_le.mpr he) hg) hVD2 hv

end CFSG.RankThree.PartTwo.Sec15.ThmC
