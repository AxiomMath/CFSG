module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.W3Lem45Holds
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs
import CFSG.ClassicalGroups.PCoreSection
import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer

open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.E2.E22N CFSG.Open Subgroup
open CFSG.Quasithin.RonanE111 CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.Vol2.Ch11.SecB (E111Reduced)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (CompFactorAutInF)
open CFSG.SignalizerFunctorTheorem.McBride.Near (IsChiefFactorOf)
open scoped commutatorElement Pointwise

variable {Q : Type} [Group Q] {T F Z : Subgroup Q}

theorem layer_inf_eq_bot (hT : IsSylowIn 2 T ⊤)
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥)
    (hZ : Z ≤ Subgroup.centralizer (F : Set Q)) (hchief : IsChiefFactorOf ⊤ F Z) :
    Z ⊓ T = ⊥ := by
  have hZF : Z ≤ F := le_of_lt hchief.2.2.1
  have hZn : Z.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hchief.1.2)
  have hZab : ∀ z ∈ Z, ∀ w ∈ Z, z * w = w * z := by
    intro z hz w hw
    exact (Subgroup.mem_centralizer_iff.mp (hZ hz) w (hZF hw)).symm
  have hnorm : ∀ z ∈ Z, ∀ y ∈ Z ⊓ T, z * y * z⁻¹ ∈ Z ⊓ T := by
    intro z hz y hy
    rw [Subgroup.mem_inf] at hy ⊢
    refine ⟨hZn.conj_mem y hy.1 z, ?_⟩
    have hzy : z * y * z⁻¹ = y := by
      rw [hZab z hz y hy.1]
      group
    rw [hzy]
    exact hy.2
  have hle : Z ⊓ T ≤ pCoreOf 2 Z :=
    CFSG.ClassicalGroups.PCoreSection.le_pCoreOf (p := 2) (X := Z) (N := Z ⊓ T)
      inf_le_left hnorm (hT.isPGroup.to_le inf_le_right)
  have hpc : pCoreOf 2 Z ≤ pCoreOf 2 (⊤ : Subgroup Q) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer (p := 2) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hZn])
  rw [hO2] at hpc
  exact le_bot_iff.mp (hle.trans hpc)

private theorem layer_chief_map_ne_bot [Z.Normal] (hchief : IsChiefFactorOf ⊤ F Z) :
    F.map (QuotientGroup.mk' Z) ≠ ⊥ := by
  intro hbot
  have hFZ : F ≤ Z := by
    rw [Subgroup.map_eq_bot_iff] at hbot
    rw [QuotientGroup.ker_mk'] at hbot
    exact hbot
  exact (ne_of_lt hchief.2.2.1) (le_antisymm (le_of_lt hchief.2.2.1) hFZ)

private theorem layer_comap_le [Z.Normal] (hZF : Z ≤ F) {N : Subgroup (Q ⧸ Z)}
    (hNle : N ≤ F.map (QuotientGroup.mk' Z)) : N.comap (QuotientGroup.mk' Z) ≤ F := by
  intro q hq
  have hqN : (QuotientGroup.mk' Z) q ∈ N := hq
  obtain ⟨f, hfF, hfq⟩ := Subgroup.mem_map.mp (hNle hqN)
  have hqZ : q * f⁻¹ ∈ Z := by
    have h1 : (QuotientGroup.mk' Z) (q * f⁻¹) = 1 := by
      rw [map_mul, map_inv, hfq]
      group
    have h1' : q * f⁻¹ ∈ (QuotientGroup.mk' Z).ker := MonoidHom.mem_ker.mpr h1
    rwa [QuotientGroup.ker_mk'] at h1'
  have hqeq : q = (q * f⁻¹) * f := by group
  rw [hqeq]
  exact F.mul_mem (hZF hqZ) hfF

private theorem layer_minimal_map [Z.Normal] (hchief : IsChiefFactorOf ⊤ F Z) :
    ∀ N : Subgroup (Q ⧸ Z), N.Normal → N ≤ F.map (QuotientGroup.mk' Z) →
      N = ⊥ ∨ N = F.map (QuotientGroup.mk' Z) := by
  intro N hNn hNle
  obtain ⟨-, -, hZltF, hmin⟩ := hchief
  have hN'F : N.comap (QuotientGroup.mk' Z) ≤ F :=
    layer_comap_le (Z := Z) (le_of_lt hZltF) hNle
  have hN'in : CFSG.SignalizerFunctorTheorem.McBride.Near.IsNormalIn
      (N.comap (QuotientGroup.mk' Z)) ⊤ :=
    ⟨le_top, (Subgroup.normalizer_eq_top_iff.mpr
      (hNn.comap (QuotientGroup.mk' Z))).ge⟩
  have hN'Z : Z ≤ N.comap (QuotientGroup.mk' Z) := by
    intro z hz
    rw [Subgroup.mem_comap]
    have hz1 : (QuotientGroup.mk' Z) z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [hz1]
    exact N.one_mem
  rcases hmin (N.comap (QuotientGroup.mk' Z)) hN'in hN'Z hN'F with hN' | hN'
  · left
    have hmap := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) N
    rw [← hmap, hN', Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  · right
    have hmap := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) N
    rw [← hmap, hN']

private theorem layer_map_not_isMulCommutative [Z.Normal] (hperf : ⁅F, F⁆ = F)
    (hchief : IsChiefFactorOf ⊤ F Z) : ¬ IsMulCommutative ↥(F.map (QuotientGroup.mk' Z)) := by
  intro hcomm
  have hle : ⁅F, F⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hcommab : (⟨(QuotientGroup.mk' Z) a, Subgroup.mem_map_of_mem _ ha⟩ :
        ↥(F.map (QuotientGroup.mk' Z))) *
        ⟨(QuotientGroup.mk' Z) b, Subgroup.mem_map_of_mem _ hb⟩ =
        ⟨(QuotientGroup.mk' Z) b, Subgroup.mem_map_of_mem _ hb⟩ *
        ⟨(QuotientGroup.mk' Z) a, Subgroup.mem_map_of_mem _ ha⟩ :=
      hcomm.is_comm.comm _ _
    have h1 : (QuotientGroup.mk' Z) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val hcommab
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker]
    exact h1
  have hFZ : F ≤ Z := hperf ▸ hle
  exact (ne_of_lt hchief.2.2.1) (le_antisymm (le_of_lt hchief.2.2.1) hFZ)

private theorem layer_comap_centralizer_le [Z.Normal] (hperf : ⁅F, F⁆ = F)
    (hZ : Z ≤ Subgroup.centralizer (F : Set Q))
    (hC : Subgroup.centralizer (F : Set Q) ≤ F) :
    (Subgroup.centralizer ((F.map (QuotientGroup.mk' Z) : Subgroup (Q ⧸ Z)) :
      Set (Q ⧸ Z))).comap (QuotientGroup.mk' Z) ≤ F := by
  classical
  let X : Subgroup (Q ⧸ Z) := F.map (QuotientGroup.mk' Z)
  let C : Subgroup Q := (Subgroup.centralizer (X : Set (Q ⧸ Z))).comap
    (QuotientGroup.mk' Z)
  change C ≤ F
  have hCFz : ⁅C, F⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro c hc f hf
    have hcX : (QuotientGroup.mk' Z) c ∈ Subgroup.centralizer (X : Set (Q ⧸ Z)) := hc
    have hcomm : (QuotientGroup.mk' Z) c * (QuotientGroup.mk' Z) f =
        (QuotientGroup.mk' Z) f * (QuotientGroup.mk' Z) c :=
      (Subgroup.mem_centralizer_iff.mp hcX _ (Subgroup.mem_map_of_mem _ hf)).symm
    have h1 : (QuotientGroup.mk' Z) ⁅c, f⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker]
    exact h1
  have hbot1 : ⁅⁅C, F⁆, F⁆ = ⊥ := by
    have hZFbot : ⁅Z, F⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZ
    exact le_bot_iff.mp ((Subgroup.commutator_mono hCFz le_rfl).trans (le_of_eq hZFbot))
  have hbot2 : ⁅⁅F, C⁆, F⁆ = ⊥ := by
    rw [Subgroup.commutator_comm F C]
    exact hbot1
  have hthree : ⁅⁅F, F⁆, C⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := F) (H₂ := F) (H₃ := C) hbot2 hbot1
  rw [hperf] at hthree
  have hCle : C ≤ Subgroup.centralizer (F : Set Q) := by
    rw [Subgroup.commutator_comm] at hthree
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hthree
  intro c hc
  exact (hCle.trans hC) hc

private theorem layer_centerIn_eq_bot [Z.Normal] (hperf : ⁅F, F⁆ = F)
    (hchief : IsChiefFactorOf ⊤ F Z) :
    F.map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer
      ((F.map (QuotientGroup.mk' Z) : Subgroup (Q ⧸ Z)) : Set (Q ⧸ Z)) = ⊥ := by
  have hXn : (F.map (QuotientGroup.mk' Z)).Normal :=
    (Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hchief.2.1.2)).map _
      (QuotientGroup.mk'_surjective Z)
  have hmin := layer_minimal_map (Z := Z) hchief
  have hcenterInNormal : (F.map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer
      ((F.map (QuotientGroup.mk' Z) : Subgroup (Q ⧸ Z)) : Set (Q ⧸ Z))).Normal :=
    @Subgroup.normal_inf_normal (Q ⧸ Z) _ (F.map (QuotientGroup.mk' Z))
      (Subgroup.centralizer ((F.map (QuotientGroup.mk' Z) : Subgroup (Q ⧸ Z)) :
        Set (Q ⧸ Z))) hXn
      (@Subgroup.normal_centralizer (Q ⧸ Z) _ (F.map (QuotientGroup.mk' Z)) hXn)
  rcases hmin (F.map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer
      ((F.map (QuotientGroup.mk' Z) : Subgroup (Q ⧸ Z)) : Set (Q ⧸ Z)))
      hcenterInNormal inf_le_left with h | h
  · exact h
  · exfalso
    apply layer_map_not_isMulCommutative (Z := Z) hperf hchief
    exact (Subgroup.le_centralizer_iff_isMulCommutative
      (K := F.map (QuotientGroup.mk' Z))).mp ((le_of_eq h.symm).trans inf_le_right)

private theorem layer_centralizer_eq_bot [Z.Normal] (hperf : ⁅F, F⁆ = F)
    (hZ : Z ≤ Subgroup.centralizer (F : Set Q)) (hchief : IsChiefFactorOf ⊤ F Z)
    (hC : Subgroup.centralizer (F : Set Q) ≤ F) :
    Subgroup.centralizer ((F.map (QuotientGroup.mk' Z) : Subgroup (Q ⧸ Z)) :
      Set (Q ⧸ Z)) = ⊥ := by
  have hcentle : Subgroup.centralizer ((F.map (QuotientGroup.mk' Z) : Subgroup (Q ⧸ Z)) :
      Set (Q ⧸ Z)) ≤ F.map (QuotientGroup.mk' Z) := by
    intro x hx
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    exact Subgroup.mem_map_of_mem _
      (layer_comap_centralizer_le (Z := Z) hperf hZ hC hx)
  have hcenterIn := layer_centerIn_eq_bot (Z := Z) hperf hchief
  exact le_bot_iff.mp ((le_inf hcentle le_rfl).trans (le_of_eq hcenterIn))

theorem layer_reduced [Finite Q] [Z.Normal] (hT : IsSylowIn 2 T ⊤)
    (hperf : ⁅F, F⁆ = F) (hZ : Z ≤ Subgroup.centralizer (F : Set Q))
    (hchief : IsChiefFactorOf ⊤ F Z)
    (hC : Subgroup.centralizer (F : Set Q) ≤ F) (hFT : F ⊔ T = ⊤) :
    E111Reduced (Q ⧸ Z) (F.map (QuotientGroup.mk' Z)) (T.map (QuotientGroup.mk' Z)) := by
  have hFn : F.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hchief.2.1.2)
  have hXn : (F.map (QuotientGroup.mk' Z)).Normal :=
    hFn.map _ (QuotientGroup.mk'_surjective Z)
  have hXnc : ¬ IsMulCommutative ↥(F.map (QuotientGroup.mk' Z)) :=
    layer_map_not_isMulCommutative (Z := Z) hperf hchief
  have hnab : ∃ a b : ↥(F.map (QuotientGroup.mk' Z)), a * b ≠ b * a := by
    by_contra h
    apply hXnc
    refine ⟨⟨fun a b => ?_⟩⟩
    by_contra hab
    exact h ⟨a, b, hab⟩
  refine ⟨hXn, layer_chief_map_ne_bot (Z := Z) hchief,
    layer_minimal_map (Z := Z) hchief, hnab,
    layer_centralizer_eq_bot (Z := Z) hperf hZ hchief hC,
    E1.isSylowIn_two_map_top (QuotientGroup.mk'_surjective Z) hT, ?_⟩
  rw [← Subgroup.map_sup, hFT,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)]

theorem layer_pCore_eq_bot [Finite Q] [Z.Normal] (hT : IsSylowIn 2 T ⊤)
    (hperf : ⁅F, F⁆ = F) (hZ : Z ≤ Subgroup.centralizer (F : Set Q))
    (hchief : IsChiefFactorOf ⊤ F Z)
    (hC : Subgroup.centralizer (F : Set Q) ≤ F) (hFT : F ⊔ T = ⊤) :
    pCoreOf 2 (⊤ : Subgroup (Q ⧸ Z)) = ⊥ :=
  E111R.pCoreOf_two_eq_bot (layer_reduced hT hperf hZ hchief hC hFT)

theorem layer_tauOf_map [Z.Normal] (hZT : Z ⊓ T = ⊥)
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥)
    (hO2' : pCoreOf 2 (⊤ : Subgroup (Q ⧸ Z)) = ⊥) {A : Subgroup Q} (hA : A ≤ T) :
    tauOf ⊤ (T.map (QuotientGroup.mk' Z)) (A.map (QuotientGroup.mk' Z)) =
      (tauOf ⊤ T A).map (QuotientGroup.mk' Z) := by
  ext x
  constructor
  · intro hx
    rw [mem_tauOf] at hx
    obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp hx.1
    refine Subgroup.mem_map_of_mem _ (mem_tauOf.mpr ⟨htT, ?_, fun a ha => ?_⟩)
    · rw [hO2, Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top t
    · have h1 : (QuotientGroup.mk' Z) ⁅t, a⁆ = 1 := by
        rw [map_commutatorElement]
        have hmem := hx.2.2 _ (Subgroup.mem_map_of_mem _ ha)
        simpa [hO2'] using hmem
      have h1' : ⁅t, a⁆ ∈ (QuotientGroup.mk' Z).ker := MonoidHom.mem_ker.mpr h1
      rw [QuotientGroup.ker_mk'] at h1'
      have hmem : ⁅t, a⁆ ∈ Z ⊓ T :=
        ⟨h1', T.mul_mem (T.mul_mem (T.mul_mem htT (hA ha)) (T.inv_mem htT))
          (T.inv_mem (hA ha))⟩
      rw [hZT] at hmem
      simpa [hO2] using hmem
  · intro hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    have ht' : t ∈ T ∧ t ∈ Subgroup.normalizer (pCoreOf 2 (⊤ : Subgroup Q)) ∧
        ∀ a ∈ A, ⁅t, a⁆ ∈ pCoreOf 2 (⊤ : Subgroup Q) := mem_tauOf.mp ht
    refine mem_tauOf.mpr ⟨Subgroup.mem_map_of_mem _ ht'.1, ?_, fun y hy => ?_⟩
    · rw [hO2', Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      have h0 : ⁅t, a⁆ ∈ pCoreOf 2 (⊤ : Subgroup Q) := ht'.2.2 a ha
      rw [hO2] at h0
      rw [hO2']
      simpa using congrArg (QuotientGroup.mk' Z) (show ⁅t, a⁆ = 1 from h0)

theorem layer_map_ne_bot [Z.Normal] (hZT : Z ⊓ T = ⊥) {A : Subgroup Q}
    (hA : A ≤ T) (hA1 : A ≠ ⊥) : A.map (QuotientGroup.mk' Z) ≠ ⊥ := by
  intro hbot
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hA1 (le_bot_iff.mp ((le_inf hbot hA).trans (le_of_eq hZT)))

theorem layer_isInvColl_map [Z.Normal] {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω) :
    E1.IsInvColl ⊤ ((fun A => A.map (QuotientGroup.mk' Z)) '' Ω) :=
  E1.isInvColl_map_of_surjective (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) hΩ

private theorem layer_quotient_equiv [Z.Normal] :
    ∃ e : (↥(⊤ : Subgroup Q) ⧸ Z.subgroupOf ⊤) ≃* (Q ⧸ Z),
      ((T.subgroupOf ⊤).map (QuotientGroup.mk' (Z.subgroupOf ⊤))).map e.toMonoidHom =
        T.map (QuotientGroup.mk' Z) := by
  classical
  let π : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  let φ : ↥(⊤ : Subgroup Q) →* Q ⧸ Z :=
    π.comp (Subgroup.topEquiv (G := Q)).toMonoidHom
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective Z).comp (Subgroup.topEquiv (G := Q)).surjective
  have hker : φ.ker = Z.subgroupOf ⊤ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk' Z) ((Subgroup.topEquiv (G := Q)) x) = 1 ↔ (x : Q) ∈ Z
    rw [show ((Subgroup.topEquiv (G := Q)) x : Q) = (x : Q) from rfl]
    exact QuotientGroup.eq_one_iff _
  let e : (↥(⊤ : Subgroup Q) ⧸ Z.subgroupOf ⊤) ≃* (Q ⧸ Z) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have he_mk : ∀ t : ↥(⊤ : Subgroup Q),
      e (QuotientGroup.mk' (Z.subgroupOf ⊤) t) = φ t := by
    intro t
    rfl
  refine ⟨e, ?_⟩
  ext x
  constructor
  · rintro ⟨y, ⟨t, htT, rfl⟩, rfl⟩
    change e (QuotientGroup.mk' (Z.subgroupOf ⊤) t) ∈ T.map (QuotientGroup.mk' Z)
    rw [he_mk]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) (Subgroup.mem_subgroupOf.mp htT)
  · rintro ⟨q, hq, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨QuotientGroup.mk' (Z.subgroupOf ⊤) ⟨q, Subgroup.mem_top q⟩,
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hq), ?_⟩
    exact he_mk ⟨q, Subgroup.mem_top q⟩

theorem layer_local [Finite Q] [Z.Normal] {j : ℕ} (hcf : CompFactorAutInF j ⊤ T)
    (hT : IsSylowIn 2 T ⊤) (hperf : ⁅F, F⁆ = F)
    (hZ : Z ≤ Subgroup.centralizer (F : Set Q)) (hchief : IsChiefFactorOf ⊤ F Z)
    (hC : Subgroup.centralizer (F : Set Q) ≤ F) (hFT : F ⊔ T = ⊤)
    {J : Subgroup (Q ⧸ Z)} (hJ : E111R.IsComp (F.map (QuotientGroup.mk' Z)) J) :
    fourFiveFAS j (↥(F12.autNL (T.map (QuotientGroup.mk' Z)) J) ⧸
      (F12.autC (T.map (QuotientGroup.mk' Z)) J).subgroupOf
        (F12.autNL (T.map (QuotientGroup.mk' Z)) J)) := by
  classical
  have hR := layer_reduced (Z := Z) hT hperf hZ hchief hC hFT
  obtain ⟨e, hTmap⟩ := layer_quotient_equiv (Z := Z)
  have hQ1 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.fourFive_quotCompFAS_of_compFactorAutInF
    (j := j) hcf
  have hQ1b := fourFive_quotCompFAS_quotient (j := j) (Q := ↥(⊤ : Subgroup Q))
    (T := T.subgroupOf ⊤) (Z.subgroupOf ⊤) hQ1
  have hQ1c := fourFive_compFAS_of_quotCompFAS (j := j) hQ1b
  have hQ2 := fourFive_compFAS_mulEquiv (j := j) e hQ1c
  have hcomp : fourFiveCompFAS j (Q ⧸ Z) (T.map (QuotientGroup.mk' Z)) := by
    rwa [hTmap] at hQ2
  have hXnc : ¬ IsMulCommutative ↥(F.map (QuotientGroup.mk' Z)) := by
    rintro ⟨hcomm⟩
    obtain ⟨a, b, hab⟩ := hR.2.2.2.1
    exact hab (hcomm.comm a b)
  obtain ⟨_hinst, hF⟩ := hcomp (F.map (QuotientGroup.mk' Z)) hR.1 hR.2.1 hR.2.2.1 hXnc J
    (fourFive_isComponentOf_of_isComp hJ)
  exact hF

end CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer
