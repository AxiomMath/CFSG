module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatKGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneInputs
import CFSG.Assembly.Subnormal
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.StandardType.GGSummandStructBasic
import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizer
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructBasic
import CFSG.LocalAnalysis.StandardType.GGSixStepTwoDefs
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummand
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G]

theorem ggRCS_perfect_lift {r : G} {M G₀ : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (G₀ : Set G))
    (hSch : ∀ D : Subgroup G, D ≤ Subgroup.normalizer (G₀ : Set G) → ⁅D, D⁆ = D → D ≤ G₀)
    {P : Subgroup (GGRCSNbar r)} (hP : P ≤ ggRCSImg r M) (hPperf : ⁅P, P⁆ = P) :
    ∃ K : Subgroup G, K ≤ G₀ ⊓ Subgroup.centralizer ({r} : Set G) ∧ ⁅K, K⁆ = K ∧
      (K.subgroupOf (Subgroup.centralizer ({r} : Set G))).map
        (QuotientGroup.mk' (CFSG.Assembly.pCore 2
          ↥(Subgroup.centralizer ({r} : Set G)))) = P := by
  let N := Subgroup.centralizer ({r} : Set G)
  let π : ↥N →* GGRCSNbar r := QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N)
  have hP' : P ≤ (M.subgroupOf N).map π := hP
  let ρ : ↥(M.subgroupOf N) →* GGRCSNbar r := π.comp (M.subgroupOf N).subtype
  have hρrange : ρ.range = (M.subgroupOf N).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hCV' : P ≤ ρ.range := hρrange ▸ hP'
  let P₀ : Subgroup ↥(M.subgroupOf N) := P.comap ρ
  have hP₀map : P₀.map ρ = P := Subgroup.map_comap_eq_self (f := ρ) (H := P) hCV'
  have hPperf' : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hPperf
  have hDmap : ((CFSG.perfectResidual P₀).map P₀.subtype).map ρ = P := by
    have h := CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map ρ P₀
    rw [hP₀map] at h
    rw [h, CFSG.SignalizerFunctorTheorem.Nonsolvable.perfectResidual_map_eq_of_isPerfect hPperf']
  have hDperf : Group.IsPerfect ↥(CFSG.perfectResidual P₀) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
  let Kn : Subgroup ↥N := ((CFSG.perfectResidual P₀).map P₀.subtype).map (M.subgroupOf N).subtype
  let K : Subgroup G := Kn.map N.subtype
  have hKnperf : Group.IsPerfect ↥Kn := by
    have h1 : Group.IsPerfect ↥((CFSG.perfectResidual P₀).map P₀.subtype) :=
      Group.IsPerfect.map (H := CFSG.perfectResidual P₀) P₀.subtype
    exact Group.IsPerfect.map (H := (CFSG.perfectResidual P₀).map P₀.subtype)
      (M.subgroupOf N).subtype
  have hKperf : Group.IsPerfect ↥K := by
    haveI : Group.IsPerfect ↥Kn := hKnperf
    exact Group.IsPerfect.map (H := Kn) N.subtype
  have hKnM : Kn ≤ M.subgroupOf N := Subgroup.map_subtype_le _
  have hKM : K ≤ M := by
    calc K = Kn.map N.subtype := rfl
      _ ≤ (M.subgroupOf N).map N.subtype := Subgroup.map_mono hKnM
      _ = M ⊓ N := Subgroup.subgroupOf_map_subtype M N
      _ ≤ M := inf_le_left
  have hKg0 : K ≤ G₀ := hSch K (hKM.trans hM) (Subgroup.isPerfect_iff.mp hKperf)
  have hKeq : (K.subgroupOf N).map π = P := by
    have h1 : K.subgroupOf N = Kn :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective Kn
    rw [h1]
    have h2 : Kn.map π = ((CFSG.perfectResidual P₀).map P₀.subtype).map ρ := by
      rw [show Kn = Subgroup.map (M.subgroupOf N).subtype
          (Subgroup.map P₀.subtype (CFSG.perfectResidual P₀)) from rfl, Subgroup.map_map]
    rw [h2, hDmap]
  exact ⟨K, le_inf hKg0 (Subgroup.map_subtype_le _), Subgroup.isPerfect_iff.mp hKperf, hKeq⟩

end Lift

section PCoreImg

variable {G : Type} [Group G] [Finite G]

theorem ggRCSImg_pCoreOf {r : G} (M : Subgroup G) :
    pCoreOf 2 (ggRCSImg r M) =
      ggRCSImg r (pCoreOf 2 (Subgroup.centralizer ({r} : Set G) ⊓ M)) := by
  classical
  let N := Subgroup.centralizer ({r} : Set G)
  let Q := pCoreOf 2 (N ⊓ M)
  have hQM : Q ≤ M := (pCoreOf_le' 2 (N ⊓ M)).trans inf_le_right
  have hQN : Q ≤ N := (pCoreOf_le' 2 (N ⊓ M)).trans inf_le_left
  have hle : ggRCSImg r Q ≤ pCoreOf 2 (ggRCSImg r M) := by
    refine le_pCoreOf_of_normalized 2 (ggRCSImg_mono r hQM) (ggRCSImg_isPGroup r
      (isPGroup_pCoreOf' 2 (N ⊓ M))) ?_
    have hnorm : ((ggRCSImg r Q).subgroupOf (ggRCSImg r M)).Normal := by
      refine ggRCSImg_normal r hQM ?_
      intro x hx
      exact ggMem_normalizer_pCoreOf (p := 2) (H := N ⊓ M) (by simpa [N, inf_comm] using hx)
    intro x hx q hq
    have hnorm' : ggRCSImg r M ≤ Subgroup.normalizer (ggRCSImg r Q : Set (GGRCSNbar r)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (ggRCSImg_mono r hQM)).mp hnorm
    exact (Subgroup.mem_normalizer_iff.mp (hnorm' hx) q).mp hq
  refine le_antisymm ?_ hle
  let T := pCoreOf 2 (ggRCSImg r M)
  have hT2 : IsPGroup 2 T := isPGroup_pCoreOf' 2 (ggRCSImg r M)
  have hTV : T ≤ ggRCSImg r M := pCoreOf_le' 2 (ggRCSImg r M)
  let K : Subgroup ↥N := (M.subgroupOf N) ⊓ (T.comap (QuotientGroup.mk'
    (CFSG.Assembly.pCore 2 ↥N)))
  have hKA : K ≤ M.subgroupOf N := inf_le_left
  have hKn : (K.subgroupOf (M.subgroupOf N)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKA]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    have hkeq : x⁻¹ * (x * k * x⁻¹) * x = k := by group
    constructor
    · intro hk
      refine ⟨(M.subgroupOf N).mul_mem ((M.subgroupOf N).mul_mem hx (hKA hk))
        ((M.subgroupOf N).inv_mem hx), ?_⟩
      have hπxV : (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N)) x ∈ ggRCSImg r M :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      have h := conj_mem_pCoreOf' 2 hπxV hk.2
      simpa [map_mul, map_inv] using h
    · intro hk
      refine ⟨?_, ?_⟩
      · have hkM : x * k * x⁻¹ ∈ M.subgroupOf N := hKA hk
        have hkM' : x⁻¹ * (x * k * x⁻¹) * x ∈ M.subgroupOf N :=
          (M.subgroupOf N).mul_mem
            ((M.subgroupOf N).mul_mem ((M.subgroupOf N).inv_mem hx) hkM) hx
        simpa [hkeq] using hkM'
      · have hπx : (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N)) x⁻¹ ∈ ggRCSImg r M :=
          Subgroup.mem_map.mpr ⟨x⁻¹, (M.subgroupOf N).inv_mem hx, rfl⟩
        have h := conj_mem_pCoreOf' 2 hπx hk.2
        have h' : (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N))
            (x⁻¹ * (x * k * x⁻¹) * x) ∈ T := by
          simpa [map_mul, map_inv] using h
        simpa [hkeq] using h'
  have hK2 : IsPGroup 2 ↥K := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let f : ↥K →* GGRCSNbar r :=
      (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N)).comp K.subtype
    have hfr : f.range ≤ T := by
      rintro _ ⟨k, rfl⟩
      exact k.2.2
    have hrange2 : IsPGroup 2 ↥f.range := IsPGroup.to_le hT2 hfr
    have hP2 : IsPGroup 2 ↥(CFSG.Assembly.pCore 2 ↥N) := by
      have h := (isPGroup_pCoreOf' 2 N).comap_of_injective N.subtype N.subtype_injective
      rw [show pCoreOf 2 N = (CFSG.Assembly.pCore 2 ↥N).map N.subtype from rfl,
        Subgroup.comap_map_eq_self_of_injective N.subtype_injective] at h
      exact h
    have hker2 : IsPGroup 2 ↥f.ker := by
      refine IsPGroup.to_le (hP2.comap_of_injective K.subtype K.subtype_injective) ?_
      intro k hk
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hk
      exact hk
    have hcard := ggRCSS_card_eq_range_mul_ker f
    obtain ⟨a, ha⟩ := hrange2.exists_card_eq
    obtain ⟨b, hb⟩ := hker2.exists_card_eq
    refine IsPGroup.of_card (n := a + b) ?_
    rw [hcard, ha, hb, pow_add]
  have hKQ : K.map N.subtype ≤ Q := by
    refine le_pCoreOf_of_normalized 2 ?_ (hK2.map N.subtype) ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact ⟨k.2, Subgroup.mem_subgroupOf.mp (hKA hk)⟩
    · intro x hx y hy
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
      have hxM : (⟨x, hx.1⟩ : ↥N) ∈ M.subgroupOf N := Subgroup.mem_subgroupOf.mpr hx.2
      have hnorm' : M.subgroupOf N ≤ Subgroup.normalizer (K : Set ↥N) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKA).mp hKn
      have hk' : (⟨x, hx.1⟩ : ↥N) * k * (⟨x, hx.1⟩ : ↥N)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hnorm' hxM) k).mp hk
      exact Subgroup.mem_map.mpr ⟨_, hk', by simp⟩
  intro t ht
  have htV : t ∈ ggRCSImg r M := hTV ht
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp htV
  have haK : a ∈ K := ⟨ha, ht⟩
  exact mem_ggRCSImg r (y := a) (hKQ (Subgroup.mem_map.mpr ⟨a, haK, rfl⟩))

end PCoreImg

section ImgLattice

variable {G : Type} [Group G] [Finite G]

private theorem ggRCSImg_sup {r : G} {A B : Subgroup G}
    (hA : A ≤ Subgroup.centralizer ({r} : Set G))
    (hB : B ≤ Subgroup.centralizer ({r} : Set G)) :
    ggRCSImg r (A ⊔ B) = ggRCSImg r A ⊔ ggRCSImg r B := by
  have hsub : (A ⊔ B).subgroupOf (Subgroup.centralizer ({r} : Set G)) =
      A.subgroupOf (Subgroup.centralizer ({r} : Set G)) ⊔
        B.subgroupOf (Subgroup.centralizer ({r} : Set G)) :=
    Subgroup.subgroupOf_sup hA hB
  rw [ggRCSImg, ggRCSImg, ggRCSImg, hsub, Subgroup.map_sup]

private theorem ggRCSImg_commutator {r : G} {A B : Subgroup G}
    (hA : A ≤ Subgroup.centralizer ({r} : Set G))
    (hB : B ≤ Subgroup.centralizer ({r} : Set G)) :
    ggRCSImg r ⁅A, B⁆ = ⁅ggRCSImg r A, ggRCSImg r B⁆ := by
  have hABC : ⁅A, B⁆ ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 : ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := rfl
    rw [h1]
    exact (Subgroup.centralizer ({r} : Set G)).mul_mem
      ((Subgroup.centralizer ({r} : Set G)).mul_mem
        ((Subgroup.centralizer ({r} : Set G)).mul_mem (hA ha) (hB hb))
        ((Subgroup.centralizer ({r} : Set G)).inv_mem (hA ha)))
      ((Subgroup.centralizer ({r} : Set G)).inv_mem (hB hb))
  have hsub : (⁅A, B⁆ : Subgroup G).subgroupOf (Subgroup.centralizer ({r} : Set G)) =
      ⁅A.subgroupOf (Subgroup.centralizer ({r} : Set G)),
        B.subgroupOf (Subgroup.centralizer ({r} : Set G))⁆ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (Subgroup.centralizer ({r} : Set G)))
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hABC]
  rw [ggRCSImg, ggRCSImg, ggRCSImg, hsub, Subgroup.map_commutator]

private theorem ggRCSImg_pCoreOf_self {r : G} :
    ggRCSImg r (pCoreOf 2 (Subgroup.centralizer ({r} : Set G))) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
  have hnc : (n : G) ∈ pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hn
  have hmem : (n : ↥(Subgroup.centralizer {r})) ∈
      CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G)) := by
    have h := hnc
    rw [show pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) =
      (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))).map
        (Subgroup.centralizer ({r} : Set G)).subtype from rfl] at h
    obtain ⟨z, hz, hzm⟩ := Subgroup.mem_map.mp h
    rwa [show z = n from Subtype.ext hzm] at hz
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hmem

end ImgLattice

section QuotEquiv

variable {G : Type} [Group G]

@[expose] noncomputable def ggRCSImgHom {r : G} {Y : Subgroup G}
    (hY : Y ≤ Subgroup.centralizer ({r} : Set G)) : ↥Y →* ↥(ggRCSImg r Y) :=
  ((QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G)))).comp
    (Subgroup.inclusion hY)).codRestrict (ggRCSImg r Y) fun y =>
      Subgroup.mem_map.mpr ⟨Subgroup.inclusion hY y, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩

theorem ggRCSImgHom_apply {r : G} {Y : Subgroup G}
    (hY : Y ≤ Subgroup.centralizer ({r} : Set G)) (y : ↥Y) :
    (ggRCSImgHom hY y : GGRCSNbar r) =
      QuotientGroup.mk' (CFSG.Assembly.pCore 2
        ↥(Subgroup.centralizer ({r} : Set G))) ⟨(y : G), hY y.2⟩ := rfl

theorem ggRCSImgHom_mk_eq {r : G} {Y Q : Subgroup G}
    (hY : Y ≤ Subgroup.centralizer ({r} : Set G))
    (hP : pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ≤ Q)
    [(Q.subgroupOf Y).Normal]
    {y y' : ↥Y} (h : ggRCSImgHom hY y = ggRCSImgHom hY y') :
    QuotientGroup.mk y = (QuotientGroup.mk y' : ↥Y ⧸ Q.subgroupOf Y) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hval : (QuotientGroup.mk' (CFSG.Assembly.pCore 2
      ↥(Subgroup.centralizer {r})) (⟨(y : G), hY y.2⟩ : ↥(Subgroup.centralizer {r}))) =
      (QuotientGroup.mk' (CFSG.Assembly.pCore 2
      ↥(Subgroup.centralizer {r})) (⟨(y' : G), hY y'.2⟩ : ↥(Subgroup.centralizer {r}))) :=
    congrArg Subtype.val h
  have h1 : (⟨(y : G), hY y.2⟩ : ↥(Subgroup.centralizer {r}))⁻¹ *
      ⟨(y' : G), hY y'.2⟩ ∈ CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}) := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r})))
      ((⟨(y : G), hY y.2⟩ : ↥(Subgroup.centralizer {r}))⁻¹ *
        ⟨(y' : G), hY y'.2⟩) = 1
    rw [map_mul, map_inv, hval, inv_mul_cancel]
  exact hP ⟨_, h1, rfl⟩

theorem ggRCSImg_quotEquiv {r : G} {Y Q : Subgroup G}
    (hY : Y ≤ Subgroup.centralizer ({r} : Set G))
    (hQker : ∀ y : ↥Y, (QuotientGroup.mk' (CFSG.Assembly.pCore 2
        ↥(Subgroup.centralizer ({r} : Set G))) ⟨(y : G), hY y.2⟩ ∈ ggRCSImg r Q ↔
      (y : G) ∈ Q))
    [(Q.subgroupOf Y).Normal]
    [((ggRCSImg r Q).subgroupOf (ggRCSImg r Y)).Normal] :
    ∃ e : (↥(ggRCSImg r Y) ⧸ (ggRCSImg r Q).subgroupOf (ggRCSImg r Y)) ≃*
        (↥Y ⧸ Q.subgroupOf Y),
      ∀ y : ↥Y, e (QuotientGroup.mk (ggRCSImgHom hY y)) = QuotientGroup.mk y := by
  classical
  let f : ↥Y →* (↥(ggRCSImg r Y) ⧸ (ggRCSImg r Q).subgroupOf (ggRCSImg r Y)) :=
    (QuotientGroup.mk' ((ggRCSImg r Q).subgroupOf (ggRCSImg r Y))).comp (ggRCSImgHom hY)
  have hfker : f.ker = Q.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hQker y
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective
      ((ggRCSImg r Q).subgroupOf (ggRCSImg r Y)) z
    obtain ⟨n, hn, hns⟩ := Subgroup.mem_map.mp (s : ↥(ggRCSImg r Y)).2
    have hy : (n : G) ∈ Y := Subgroup.mem_subgroupOf.mp hn
    refine ⟨⟨(n : G), hy⟩, ?_⟩
    have hφ : ggRCSImgHom hY ⟨(n : G), hy⟩ = s := by
      apply Subtype.ext
      rw [ggRCSImgHom_apply]
      simpa using hns
    rw [MonoidHom.comp_apply, hφ]
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective f hfsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hfker), ?_⟩
  intro y
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).symm
      (QuotientGroup.mk (ggRCSImgHom hY y)) = QuotientGroup.mk y := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]

end QuotEquiv

section Reduction

theorem ggRootCentStructKGInput_of_tags (hSP : GGSchreierPerfectInput)
    (hS : ∀ t, GGRootCentKGStructTag t) (hO : ∀ t, GGRootCentOTwoTag t) :
    GGRootCentStructKGInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  classical
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨hBs, -, ⟨hadm, hrank⟩, ⟨hrange, hker⟩, ⟨hperf0, hmodel⟩, ⟨hBsN, hinn⟩, -, -⟩ := hctx.2
  have hcard : p ^ 4 ≤ Nat.card Bs := by
    obtain ⟨⟨-, -, -, -, -, ⟨hpp, -, -, hrk⟩, hSB, -⟩, -⟩ := hctx
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hpp.pos hrk
      _ = Nat.card B := hSB.1.2.1.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hperfR : commutator ↥ψ.range = ⊤ := by
    rw [hrange]
    exact hperf0
  have hmodelR : LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) t n 2 f := by
    rw [hrange]
    exact hmodel
  have h9iii : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J := by
    intro d hd hd1 g hg
    refine s1.2.1.mem_of_conj_mem hd hd1 ?_
    have hgd : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have : g⁻¹ * d * g = d := by rw [mul_assoc, ← hgd, inv_mul_cancel_left]
    rw [this]
    exact s1.2.1.1 hd
  have h4 : GGTwoLocalRankFour p (Subgroup.normalizer (ψ.range : Set G)) := by
    rw [hrange]
    exact hctx.twoLocalRankFour h9iii
  have hSch : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (ψ.range : Set G) →
      ⁅P, P⁆ = P → P ≤ ψ.range := by
    intro P hP hPP
    rw [hrange] at hP
    rw [hrange]
    have hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) := by
      rw [s1.1, Subgroup.card_bot]
      exact odd_one
    exact hSP G t n f ψ _ ⟨⟨hadm, hrank⟩, ⟨hrange, hker⟩, hperf0, hmodel⟩ hodd P hP hPP
  obtain ⟨-, hPQ, hQZ⟩ := ggSixRootCentralizer_core hctx hch
  have hEM : E ≤ ggM p B x L D J := hch.1.trans hBsN
  have hEp : IsPGroup p E := hch.2.1.isPGroup
  have hinnE : ∀ e ∈ E, GGPsiInnerDiag (ggU t n f).D ψ e := fun e he => hinn e (hch.1 he)
  let C := Subgroup.centralizer ({r} : Set G)
  let M := ggM p B x L D J
  let G₀ := ggG0 p B x L D J
  let C₀ := G₀ ⊓ C
  let Q := pCoreOf 2 (C ⊓ M)
  let Q₀ := pCoreOf 2 C₀
  have hQ0C₀ : Q₀ ≤ C₀ := pCoreOf_le' 2 C₀
  have hQ0C : Q₀ ≤ C := hQ0C₀.trans inf_le_right
  have hQ0G₀ : Q₀ ≤ G₀ := hQ0C₀.trans inf_le_left
  have hQ0M : Q₀ ≤ M := hQ0G₀.trans Subgroup.le_normalizer
  have hMle : M ≤ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hrange]
  by_cases hsol : Group.IsSolvable ↥C₀
  · refine ⟨∅, ?_, ?_⟩
    · intro P hPV hPperf
      rw [sSup_empty]
      obtain ⟨K, hKC, hKperf, hKmap⟩ :=
        ggRCS_perfect_lift (M := M) (G₀ := ψ.range) hMle hSch hPV hPperf
      rw [hrange] at hKC
      have hKbot : K = ⊥ := CFSG.SeitzReduction.perfect_eq_bot_of_le hsol hKperf hKC
      rw [← hKmap, hKbot]
      simp
    · simp
  · have hnsol : ¬ Group.IsSolvable ↥(ψ.range ⊓ C) := by
      rw [hrange]
      exact hsol
    have hQle : pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓ C) ≤ ψ.range :=
      hO t G n f ψ hadm hrank hker hperfR hmodelR hC
        ⟨p, Bs, hp, hp2, hBs.2.1, hcard, hBsN.trans hMle, hinn⟩ r hch.rootInvolution hnsol
    rw [hrange, inf_comm] at hQle
    have hQ0le : Q₀ ≤ Q := by
      refine pCoreOf_le_of_normal 2 (A := C₀) (M := C ⊓ M) ?_ ?_
      · intro x hx
        exact ⟨hx.2, Subgroup.le_normalizer hx.1⟩
      · have hle : C₀ ≤ C ⊓ M := fun x hx => ⟨hx.2, Subgroup.le_normalizer hx.1⟩
        have hconj : ∀ u ∈ C ⊓ M, ∀ v ∈ C₀, u * v * u⁻¹ ∈ C₀ := by
          intro u hu v hv
          refine ⟨?_, ?_⟩
          · exact (Subgroup.mem_normalizer_iff.mp hu.2 v).mp hv.1
          · exact C.mul_mem (C.mul_mem hu.1 hv.2) (C.inv_mem hu.1)
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
        intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          exact hconj x hx y hy
        · intro hy
          have h := hconj x⁻¹ ((C ⊓ M).inv_mem hx) (x * y * x⁻¹) hy
          rwa [show x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y from by group] at h
    have hQ0ge : Q ≤ Q₀ := by
      refine le_pCoreOf_of_normalized 2 ?_ (isPGroup_pCoreOf' 2 (C ⊓ M)) ?_
      · change Q ≤ G₀ ⊓ C
        exact le_inf hQle ((pCoreOf_le' 2 (C ⊓ M)).trans inf_le_left)
      · intro x hx q hq
        exact conj_mem_pCoreOf' 2 (show x ∈ C ⊓ M from
          ⟨hx.2, Subgroup.le_normalizer hx.1⟩) hq
    have hQeqQ : Q = Q₀ := le_antisymm hQ0ge hQ0le
    have hPC : pCoreOf 2 C ≤ Q₀ := by
      have h := hPQ
      change pCoreOf 2 C ≤ Q at h
      rw [hQeqQ] at h
      exact h
    obtain ⟨𝒥₀, hcov₀, hJ₀⟩ :=
      hS t G p n f ψ hp hp2 hadm hrank hker hperfR hmodelR hC h4
        ⟨Bs, hBs.2.1, hcard, hBsN.trans hMle, hinn⟩ r hch.rootInvolution hnsol E
        (by rw [hrange]; exact hEM) hch.le_centralizer hEp hinnE
    have hJ₀' : ∀ Y ∈ 𝒥₀, GGRCSKGPiece C₀ E Y := by
      intro Y hY
      have h := hJ₀ Y hY
      rw [hrange] at h
      exact h
    refine ⟨(ggRCSImg r) '' 𝒥₀, ?_, ?_⟩
    · intro P hPV hPperf
      obtain ⟨K, hKC, hKperf, hKmap⟩ :=
        ggRCS_perfect_lift (M := M) (G₀ := ψ.range) hMle hSch hPV hPperf
      have hKcov : K ≤ sSup 𝒥₀ := hcov₀ K hKC hKperf
      have hSle : sSup 𝒥₀ ≤ ((sSup ((ggRCSImg r) '' 𝒥₀)).comap
          (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C))).map C.subtype := by
        refine sSup_le fun Y hY => ?_
        intro y hy
        have hyC : y ∈ C := (hJ₀' Y hY).1 hy |>.2
        refine ⟨⟨y, hyC⟩, ?_, rfl⟩
        exact Subgroup.mem_comap.mpr
          ((le_sSup ⟨Y, hY, rfl⟩ : ggRCSImg r Y ≤ sSup ((ggRCSImg r) '' 𝒥₀))
            (mem_ggRCSImg r (y := ⟨y, hyC⟩) hy))
      rw [← hKmap]
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
      have hnK : (n : G) ∈ K := Subgroup.mem_subgroupOf.mp hn
      obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp (hSle (hKcov hnK))
      have hmn' : (n : ↥C) = m := Subtype.ext (by simpa using hmn.symm)
      have hm' : (n : ↥C) ∈ (sSup ((ggRCSImg r) '' 𝒥₀)).comap
          (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C)) := by
        rw [hmn']
        exact hm
      exact Subgroup.mem_comap.mp hm'
    · rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨hYC₀, hYsn, hYperf, hQ0Y, hQ0J, hEY, hYq⟩ := hJ₀' Y hY
      have hYC : Y ≤ C := hYC₀.trans inf_le_right
      have hYG₀ : Y ≤ G₀ := hYC₀.trans inf_le_left
      have hYM : Y ≤ M := hYG₀.trans Subgroup.le_normalizer
      have hYsub : IsSubnormal Y (M ⊓ C) := by
        have hG0sub : IsSubnormal G₀ M :=
          ggIsSubnormal_of_normal Subgroup.le_normalizer
            ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)
        exact ggIsSubnormal_trans hYsn (ggIsSubnormal_inf hG0sub C)
      have hpcore : pCoreOf 2 (ggRCSImg r M) = ggRCSImg r Q₀ := by
        rw [ggRCSImg_pCoreOf M, show pCoreOf 2 (C ⊓ M) = Q₀ from hQeqQ]
      have hQZ' : Q₀ ⊓ Subgroup.centralizer (Q₀ : Set G) ≤ pCoreOf 2 C := by
        have h := hQZ
        change Q ⊓ Subgroup.centralizer (Q : Set G) ≤ pCoreOf 2 C at h
        rwa [hQeqQ] at h
      have hZim : ggRCSImg r (Q₀ ⊓ Subgroup.centralizer (Q₀ : Set G)) = ⊥ := by
        rw [eq_bot_iff]
        exact le_trans (ggRCSImg_mono r hQZ') (ggRCSImg_pCoreOf_self (r := r)).le
      have hQ0YC : ⁅Y, Q₀⁆ ≤ C := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        simp only [commutatorElement_def]
        exact C.mul_mem (C.mul_mem (C.mul_mem (hYC ha) (hQ0C hb)) (C.inv_mem (hYC ha)))
          (C.inv_mem (hQ0C hb))
      have hQbar_le : ggRCSImg r Q₀ ≤ ggRCSImg r Y := by
        have h1 : ggRCSImg r Q₀ ≤
            ggRCSImg r (Y ⊔ (Q₀ ⊓ Subgroup.centralizer (Q₀ : Set G))) :=
          ggRCSImg_mono r hQ0Y
        rw [ggRCSImg_sup hYC (inf_le_left.trans hQ0C), hZim, sup_bot_eq] at h1
        exact h1
      haveI hQ0nY' : (Q₀.subgroupOf Y).Normal := by
        refine ⟨fun n hn g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact conj_mem_pCoreOf' 2 (hYC₀ g.2) hn
      refine ⟨ggRCSImg_mono r hYM, ggRCSImg_isSubnormal r hYsub,
        ggRCSImg_perfect r hYC hYperf, ?_, ?_, ?_, ?_⟩
      · rw [hpcore]
        exact hQbar_le
      · rw [hpcore]
        refine le_antisymm ?_ ?_
        · rw [Subgroup.commutator_le]
          intro a ha b hb
          have haV : a ∈ ggRCSImg r M := (ggRCSImg_mono r hYM) ha
          have hnorm : ggRCSImg r M ≤
              Subgroup.normalizer (ggRCSImg r Q₀ : Set (GGRCSNbar r)) := by
            rw [← hpcore]
            exact fun x hx => ggMem_normalizer_pCoreOf hx
          have hab : a * b * a⁻¹ ∈ ggRCSImg r Q₀ :=
            (Subgroup.mem_normalizer_iff.mp (hnorm haV) b).mp hb
          simp only [commutatorElement_def]
          exact (ggRCSImg r Q₀).mul_mem hab ((ggRCSImg r Q₀).inv_mem hb)
        · calc ggRCSImg r Q₀ ≤ ggRCSImg r (⁅Y, Q₀⁆ ⊔
                (Q₀ ⊓ Subgroup.centralizer (Q₀ : Set G))) := ggRCSImg_mono r hQ0J
            _ = ggRCSImg r ⁅Y, Q₀⁆ ⊔
                  ggRCSImg r (Q₀ ⊓ Subgroup.centralizer (Q₀ : Set G)) :=
                ggRCSImg_sup hQ0YC (inf_le_left.trans hQ0C)
            _ = ⁅ggRCSImg r Y, ggRCSImg r Q₀⁆ ⊔ ⊥ := by
                rw [ggRCSImg_commutator hYC hQ0C, hZim]
            _ = ⁅ggRCSImg r Y, ggRCSImg r Q₀⁆ := by rw [sup_bot_eq]
      · intro εb hεb
        obtain ⟨ε0, hε0E, hε0⟩ := Subgroup.mem_map.mp hεb
        have hεE : (ε0 : G) ∈ E := Subgroup.mem_subgroupOf.mp hε0E
        have hεN : (ε0 : G) ∈ Subgroup.normalizer (Y : Set G) := hEY hεE
        have hεC : (ε0 : G) ∈ C := hch.le_centralizer hεE
        have hconj : ∀ (u : G) (huN : u ∈ Subgroup.normalizer (Y : Set G)) (huC : u ∈ C)
            (a : GGRCSNbar r), a ∈ ggRCSImg r Y →
              (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) ⟨u, huC⟩) * a *
                ((QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) ⟨u, huC⟩))⁻¹ ∈
                  ggRCSImg r Y := by
          intro u huN huC a ha
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
          have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
          have hconjY : u * (y : G) * u⁻¹ ∈ Y :=
            (Subgroup.mem_normalizer_iff.mp huN y).mp hyY
          have hconjC : u * (y : G) * u⁻¹ ∈ C :=
            C.mul_mem (C.mul_mem huC (hYC hyY)) (C.inv_mem huC)
          refine Subgroup.mem_map.mpr ⟨⟨_, hconjC⟩, Subgroup.mem_subgroupOf.mpr hconjY, ?_⟩
          have hsub : (⟨u * (y : G) * u⁻¹, hconjC⟩ : ↥C) =
              ⟨u, huC⟩ * y * ⟨u, huC⟩⁻¹ := Subtype.ext rfl
          rw [hsub, map_mul, map_mul, map_inv]
        have hεinv : (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) ⟨(ε0 : G)⁻¹,
            C.inv_mem hεC⟩) =
            ((QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) ⟨(ε0 : G), hεC⟩))⁻¹ := by
          rw [← map_inv]
          congr 1
        rw [Subgroup.mem_normalizer_iff]
        intro a
        constructor
        · intro ha
          have h1 := hconj (ε0 : G) hεN hεC a ha
          rwa [hε0] at h1
        · intro ha
          rw [← hε0] at ha
          have h1 := hconj (ε0 : G)⁻¹ ((Subgroup.normalizer (Y : Set G)).inv_mem hεN)
            (C.inv_mem hεC)
            ((QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) ⟨(ε0 : G), hεC⟩) * a *
              ((QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) ⟨(ε0 : G), hεC⟩))⁻¹) ha
          rw [hεinv] at h1
          rwa [show ((QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) ⟨(ε0 : G), hεC⟩))⁻¹ *
              ((QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) ⟨(ε0 : G), hεC⟩) * a *
                ((QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) ⟨(ε0 : G), hεC⟩))⁻¹) *
              ((QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) ⟨(ε0 : G), hεC⟩)⁻¹)⁻¹ = a
            from by group] at h1
      · intro hQ0nY
        have hkerpi : ∀ y : ↥Y, (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C)
            ⟨(y : G), hYC y.2⟩ ∈ ggRCSImg r Q₀ ↔ (y : G) ∈ Q₀) := by
          intro y
          constructor
          · intro hy
            obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hy
            have hqQ₀ : (q : G) ∈ Q₀ := Subgroup.mem_subgroupOf.mp hq
            have hdiff : (⟨(y : G), hYC y.2⟩ : ↥C) * q⁻¹ ∈ CFSG.Assembly.pCore 2 ↥C := by
              rw [← QuotientGroup.eq_one_iff]
              change (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C))
                ((⟨(y : G), hYC y.2⟩ : ↥C) * q⁻¹) = 1
              rw [map_mul, map_inv, hqy]
              exact mul_inv_cancel _
            have h1 : ((⟨(y : G), hYC y.2⟩ : ↥C) * q⁻¹ : ↥C) ∈ Q₀.subgroupOf C := by
              rw [Subgroup.mem_subgroupOf]
              exact hPC ⟨_, hdiff, rfl⟩
            have h2 : (⟨(y : G), hYC y.2⟩ : ↥C) =
                ((⟨(y : G), hYC y.2⟩ : ↥C) * q⁻¹) * q := by group
            have h2' : (y : G) = (↑((⟨(y : G), hYC y.2⟩ : ↥C) * q⁻¹) : G) * (q : G) := by
              rw [← Subgroup.coe_mul]
              exact congrArg Subtype.val h2
            have h3 := Q₀.mul_mem (Subgroup.mem_subgroupOf.mp h1) hqQ₀
            rwa [← h2'] at h3
          · intro hy
            exact mem_ggRCSImg r (y := ⟨(y : G), hYC y.2⟩) hy
        haveI hQ0bar : ((ggRCSImg r Q₀).subgroupOf (ggRCSImg r Y)).Normal := by
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQbar_le]
          rw [← hpcore]
          intro x hx
          exact ggMem_normalizer_pCoreOf ((ggRCSImg_mono r hYM) hx)
        obtain ⟨e₀, he₀⟩ := ggRCSImg_quotEquiv hYC hkerpi
        have hsubeq : (pCoreOf 2 (ggRCSImg r M)).subgroupOf (ggRCSImg r Y) =
            (ggRCSImg r Q₀).subgroupOf (ggRCSImg r Y) := by rw [hpcore]
        let e : (↥(ggRCSImg r Y) ⧸
              (pCoreOf 2 (ggRCSImg r M)).subgroupOf (ggRCSImg r Y)) ≃*
            (↥Y ⧸ Q₀.subgroupOf Y) :=
          (QuotientGroup.quotientMulEquivOfEq hsubeq).trans e₀
        have he : ∀ y : ↥Y, e (QuotientGroup.mk (ggRCSImgHom hYC y)) =
            QuotientGroup.mk y := by
          intro y
          change e₀ ((QuotientGroup.quotientMulEquivOfEq hsubeq)
            (QuotientGroup.mk (ggRCSImgHom hYC y))) = QuotientGroup.mk y
          rw [QuotientGroup.quotientMulEquivOfEq_mk]
          exact he₀ y
        obtain ⟨hquasiY, hmarkY⟩ := hYq
        refine ⟨?_, ?_⟩
        · exact (CFSG.Assembly.IsQuasisimple.congr e).mpr hquasiY
        · let LY := ↥Y ⧸ Q₀.subgroupOf Y
          let Lbar := ↥(ggRCSImg r Y) ⧸
            (pCoreOf 2 (ggRCSImg r M)).subgroupOf (ggRCSImg r Y)
          have hB : commutator Lbar = ⊤ := by
            haveI : Group.IsPerfect LY := ⟨hmarkY.1⟩
            exact (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
              e.symm.surjective).commutator_eq_top
          let eC : LY ⧸ Subgroup.center LY ≃* Lbar ⧸ Subgroup.center Lbar :=
            QuotientGroup.congr (Subgroup.center LY) (Subgroup.center Lbar) e.symm
              (Subgroup.map_center_eq e.symm)
          have hPP : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
              (θ : LY ⧸ Subgroup.center LY ≃* R),
              (GGChevStTag lab ∧ ∀ ε ∈ E, ∃ φ ∈ I, LargeEvenInduces θ
                (fun l l' => ∃ s s' : ↥Y, QuotientGroup.mk s = l ∧
                  QuotientGroup.mk s' = l' ∧ (s' : G) = ε⁻¹ * s * ε) φ) →
              (GGChevStTag lab ∧ ∀ epsb ∈ ggRCSImg r E, ∃ φ ∈ I, LargeEvenInduces
                (eC.symm.trans θ) (fun l l' => ∃ s s' : ↥(ggRCSImg r Y),
                  QuotientGroup.mk s = l ∧ QuotientGroup.mk s' = l' ∧
                    (s' : GGRCSNbar r) = epsb⁻¹ * s * epsb) φ) := by
            rintro lab R _ I F θ ⟨hchev, hact⟩
            refine ⟨hchev, fun εb hεb => ?_⟩
            obtain ⟨ε0, hε0E, hε0⟩ := Subgroup.mem_map.mp hεb
            have hεE : (ε0 : G) ∈ E := Subgroup.mem_subgroupOf.mp hε0E
            obtain ⟨φ, hφI, hφ⟩ := hact (ε0 : G) hεE
            refine ⟨φ, hφI, ?_⟩
            intro l l' hll'
            obtain ⟨s, s', hs, hs', hss'⟩ := hll'
            obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.mp s.2
            obtain ⟨y', hy', hy's⟩ := Subgroup.mem_map.mp s'.2
            have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
            have hy'Y : (y' : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy'
            have hεN : (ε0 : G) ∈ Subgroup.normalizer (Y : Set G) := hEY hεE
            have hconjY : (ε0 : G)⁻¹ * (y : G) * (ε0 : G) ∈ Y := by
              simpa using (Subgroup.mem_normalizer_iff.mp
                ((Subgroup.normalizer (Y : Set G)).inv_mem hεN) y).mp hyY
            let yy : ↥Y := ⟨(y : G), hyY⟩
            let yy' : ↥Y := ⟨(y' : G), hy'Y⟩
            let zz : ↥Y := ⟨(ε0 : G)⁻¹ * (y : G) * (ε0 : G), hconjY⟩
            have hφy : ggRCSImgHom hYC yy = s := by
              apply Subtype.ext
              rw [ggRCSImgHom_apply]
              simpa using hys
            have hφy' : ggRCSImgHom hYC yy' = s' := by
              apply Subtype.ext
              rw [ggRCSImgHom_apply]
              simpa using hy's
            have hel : e l = QuotientGroup.mk yy := by
              have hl : l = QuotientGroup.mk (ggRCSImgHom hYC yy) := by
                rw [hφy]
                exact hs.symm
              rw [hl]
              exact he yy
            have hel' : e l' = QuotientGroup.mk yy' := by
              have hl : l' = QuotientGroup.mk (ggRCSImgHom hYC yy') := by
                rw [hφy']
                exact hs'.symm
              rw [hl]
              exact he yy'
            have hφy_eq : ggRCSImgHom hYC zz = ggRCSImgHom hYC yy' := by
              apply Subtype.ext
              rw [ggRCSImgHom_apply, ggRCSImgHom_apply]
              have h1 : (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C)
                  ⟨(zz : G), hYC zz.2⟩) =
                  ((QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) ε0))⁻¹ *
                  ((QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) y)) *
                  ((QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥C) ε0)) := by
                rw [← map_inv, ← map_mul, ← map_mul]
                congr 1
              rw [h1, hε0, hys, ← hss', ← hy's]
            have hstep := hφ (QuotientGroup.mk yy) (QuotientGroup.mk zz)
              ⟨yy, zz, rfl, rfl, rfl⟩
            have hgoal : φ ((eC.symm.trans θ) (QuotientGroup.mk l)) =
                (eC.symm.trans θ) (QuotientGroup.mk l') := by
              have heCsymm : ∀ x : Lbar, eC.symm (QuotientGroup.mk x) =
                  QuotientGroup.mk (e x) := by
                intro x
                rw [MulEquiv.symm_apply_eq]
                change QuotientGroup.mk x =
                  (QuotientGroup.congr (Subgroup.center LY) (Subgroup.center Lbar)
                    e.symm (Subgroup.map_center_eq e.symm)) (QuotientGroup.mk (e x))
                rw [QuotientGroup.congr_mk, MulEquiv.symm_apply_apply]
              rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
              have h1 : eC.symm (QuotientGroup.mk l) =
                  QuotientGroup.mk (QuotientGroup.mk yy) := by
                rw [heCsymm, hel]
              have h2 : eC.symm (QuotientGroup.mk l') =
                  QuotientGroup.mk (QuotientGroup.mk yy') := by
                rw [heCsymm, hel']
              rw [h1, h2, hstep]
              rw [ggRCSImgHom_mk_eq hYC hPC hφy_eq]
            exact hgoal
          exact ggLargeEvenMarking_of_centerQuot_equiv' hB eC hPP hmarkY

end Reduction

end CFSG.StandardType
