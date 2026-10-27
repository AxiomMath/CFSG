module

public import CFSG.GroupTheory.PCoreOfSubnormal
public import CFSG.RankThree.PartTwo.Sec18.Claim184LcProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveComponents
public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveFstar
public import CFSG.Quasithin.Background.S1567BYE
public import CFSG.GroupTheory.SylowInfNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ConjClosureSimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive72
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21j
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupAlmostSimple
public import CFSG.LocalAnalysis.WeakClosure81.InFSqComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev piBar2 (H : Subgroup G) : ↥H →* Bar2 H :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥H)

abbrev imageBar2 (H K : Subgroup G) : Subgroup (Bar2 H) :=
  (K.subgroupOf H).map (piBar2 H)

theorem subgroupOf_map_conj_of_le {K H : Subgroup G} (hKH : K ≤ H) {t : G} (ht : t ∈ H) :
    (K.map (MulAut.conj t).toMonoidHom).subgroupOf H =
      (K.subgroupOf H).map (MulAut.conj (⟨t, ht⟩ : ↥H)).toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
    ext
    simpa [MulAut.conj_apply] using hkx
  · intro hx
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨(k : G), Subgroup.mem_subgroupOf.mp hk, ?_⟩
    have := congrArg (Subtype.val) hkx
    simpa [MulAut.conj_apply] using this

theorem imageBar2_map_conj {H K : Subgroup G} (hKH : K ≤ H) {t : G} (ht : t ∈ H) :
    (imageBar2 H K).map (MulAut.conj (piBar2 H ⟨t, ht⟩)).toMonoidHom =
      imageBar2 H (K.map (MulAut.conj t).toMonoidHom) := by
  rw [imageBar2, imageBar2, subgroupOf_map_conj_of_le hKH ht]
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem imageBar2_sup {H K T : Subgroup G} (hKH : K ≤ H) (hTH : T ≤ H) :
    imageBar2 H (K ⊔ T) = imageBar2 H K ⊔ imageBar2 H T := by
  rw [imageBar2, imageBar2, imageBar2, ← Subgroup.map_sup,
    ← Subgroup.subgroupOf_sup hKH hTH]

theorem imageBar2_self (H : Subgroup G) : imageBar2 H H = ⊤ := by
  rw [imageBar2, Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem imageBar2_inf_of_isSylowIn {H T K : Subgroup G} (hT : IsSylowIn 2 T H) :
    imageBar2 H T ⊓ imageBar2 H K = imageBar2 H (T ⊓ K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_inf
    (Subgroup.map_mono (Subgroup.subgroupOf_mono _ inf_le_left))
    (Subgroup.map_mono (Subgroup.subgroupOf_mono _ inf_le_right)))
  rintro x ⟨hxT, hxK⟩
  obtain ⟨t, htT, htx⟩ := Subgroup.mem_map.mp hxT
  obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp hxK
  have hO2T : pCoreOf 2 H ≤ T := CFSG.Quasithin.pCoreOf_le_of_isSylowIn hT
  have htk : piBar2 H t = piBar2 H k := htx.trans hkx.symm
  have hmem : ((t : ↥H)⁻¹ * (k : ↥H)) ∈ CFSG.pCore 2 ↥H := by
    refine (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥H) _).mp ?_
    show piBar2 H ((t : ↥H)⁻¹ * (k : ↥H)) = 1
    rw [map_mul, map_inv, htk]
    exact inv_mul_cancel _
  have hmemG : ((t : G)⁻¹ * (k : G)) ∈ pCoreOf 2 H := by
    have h := hmem
    rw [← CFSG.openPCoreOf_subgroupOf 2 H] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hkT : (k : G) ∈ T := by
    have h1 : (t : G) * ((t : G)⁻¹ * (k : G)) ∈ T :=
      T.mul_mem htT (hO2T hmemG)
    simpa [mul_assoc] using h1
  refine Subgroup.mem_map.mpr ⟨k, ?_, hkx⟩
  exact Subgroup.mem_subgroupOf.mpr ⟨hkT, Subgroup.mem_subgroupOf.mp hkK⟩

abbrev bar2Incl {H K : Subgroup G} (hKH : K ≤ H) : ↥K →* Bar2 H :=
  (piBar2 H).comp (Subgroup.inclusion hKH)

theorem bar2Incl_range {H K : Subgroup G} (hKH : K ≤ H) :
    (bar2Incl hKH).range = imageBar2 H K := by
  rw [bar2Incl, MonoidHom.range_comp, Subgroup.inclusion_range]

theorem bar2Incl_map_subgroupOf {H K P : Subgroup G} (hKH : K ≤ H) (hPK : P ≤ K) :
    (P.subgroupOf K).map (bar2Incl hKH) = imageBar2 H P := by
  rw [bar2Incl, ← Subgroup.map_map, imageBar2]
  congr 1
  ext x
  constructor
  · rintro ⟨a, haP, -, rfl⟩
    simpa [Subgroup.mem_subgroupOf] using haP
  · intro hx
    exact ⟨⟨(x : G), hPK hx⟩, by simpa [Subgroup.mem_subgroupOf] using hx, Subtype.ext rfl⟩

theorem bar2Incl_ker_le_subgroupOf {H K P : Subgroup G} (hKH : K ≤ H)
    (hKn : (K.subgroupOf H).Normal) (hO2 : pCoreOf 2 K ≤ P) :
    (bar2Incl hKH).ker ≤ P.subgroupOf K := by
  intro x hx
  have hx' : (bar2Incl hKH) x = 1 := hx
  have hpCore : pCoreOf 2 K = K ⊓ pCoreOf 2 H :=
    CFSG.Quasithin.S1567.pCoreOf_eq_inf_pCoreOf_of_normal hKH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn)
  have hxH : (x : G) ∈ pCoreOf 2 H := by
    have h1 : Subgroup.inclusion hKH x ∈ CFSG.pCore 2 ↥H :=
      (QuotientGroup.eq_one_iff _).mp hx'
    rw [← CFSG.openPCoreOf_subgroupOf 2 H] at h1
    exact h1
  have hxK : (x : G) ∈ pCoreOf 2 K := by
    rw [hpCore]
    exact ⟨x.2, hxH⟩
  exact Subgroup.mem_subgroupOf.mpr (hO2 hxK)

theorem imageBar2_isMaxParabolicOver {H K T P : Subgroup G}
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hT : IsSylowIn 2 T H)
    (hP : S17.IsMaxParabolicOver K (T ⊓ K) P) :
    S17.IsMaxParabolicOver (imageBar2 H K) (imageBar2 H (T ⊓ K)) (imageBar2 H P) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPK, hPnorm, hPne, hPmax⟩ := hP
  have hO2K : pCoreOf 2 K ≤ T ⊓ K := by
    have hTK : IsSylowIn 2 (T ⊓ K) K := by
      have h2 : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ K) K := by
        have h3 := CFSG.isSylowTwoOf_inf_of_normal (S := T) (X := H) (N := K)
          ⟨hT.1, hT.2.1, hT.2.2⟩ hKH
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn)
        rwa [inf_comm] at h3
      exact ⟨h2.1, h2.2.1, h2.2.2⟩
    have hKnorm : ((pCoreOf 2 K).subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (CFSG.LieType.BorelTits.pCoreOf_le 2 K)]
      intro x y hx hy
      exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hy hx
    exact hTK.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hKnorm
      (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 K)
  have hO2P : pCoreOf 2 K ≤ P := by
    intro x hx
    exact hPnorm ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 K hx,
      Subgroup.le_normalizer (hO2K hx)⟩
  have hTKleP : T ⊓ K ≤ P := by
    intro x hx
    exact hPnorm ⟨hx.2, Subgroup.le_normalizer hx⟩
  let ψ : ↥K →* Bar2 H := bar2Incl hKH
  let U : Subgroup ↥K := (T ⊓ K).subgroupOf K
  let Pk : Subgroup ↥K := P.subgroupOf K
  have hψrange : ψ.range = imageBar2 H K := bar2Incl_range hKH
  have hkerU : ψ.ker ≤ U := by
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 K := by
      have hpCore : pCoreOf 2 K = K ⊓ pCoreOf 2 H :=
        CFSG.Quasithin.S1567.pCoreOf_eq_inf_pCoreOf_of_normal hKH
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn)
      have h1 : (x : G) ∈ pCoreOf 2 H := by
        have h2 : Subgroup.inclusion hKH x ∈ CFSG.pCore 2 ↥H :=
          (QuotientGroup.eq_one_iff _).mp hx
        rw [← CFSG.openPCoreOf_subgroupOf 2 H] at h2
        exact h2
      rw [hpCore]
      exact ⟨x.2, h1⟩
    exact Subgroup.mem_subgroupOf.mpr (hO2K hx')
  have hUP : U ≤ Pk := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hTKleP (Subgroup.mem_subgroupOf.mp hx))
  have hkerP : ψ.ker ≤ Pk := hkerU.trans hUP
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← bar2Incl_map_subgroupOf hKH hPK, ← bar2Incl_map_subgroupOf hKH le_rfl]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hPK)
  · rintro c ⟨hcC, hcN⟩
    have hcR : c ∈ ψ.range := by rwa [hψrange]
    obtain ⟨k, rfl⟩ := hcR
    have hUmap : U.map ψ = imageBar2 H (T ⊓ K) :=
      bar2Incl_map_subgroupOf hKH inf_le_right
    rw [← hUmap] at hcN
    have hkU : k ∈ Subgroup.normalizer (U : Set ↥K) := by
      have hnorm : (Subgroup.normalizer
          ((U.map ψ : Subgroup (Bar2 H)) : Set (Bar2 H))).comap ψ =
          Subgroup.normalizer (U : Set ↥K) := by
        rw [Subgroup.comap_normalizer_eq_of_le_range (f := ψ) (H := U.map ψ)
          (Subgroup.map_le_range ψ U)]
        rw [Subgroup.comap_map_eq_self hkerU]
      rw [← hnorm]
      exact Subgroup.mem_comap.mpr hcN
    have hkNormG : (k : G) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      have h1 : k ∈ (Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)).subgroupOf K := by
        rw [Subgroup.subgroupOf_normalizer_eq (inf_le_right : T ⊓ K ≤ K)]
        exact hkU
      exact Subgroup.mem_subgroupOf.mp h1
    rw [← bar2Incl_map_subgroupOf hKH hPK]
    exact Subgroup.mem_map.mpr ⟨k, Subgroup.mem_subgroupOf.mpr
      (hPnorm ⟨k.2, hkNormG⟩), rfl⟩
  · intro h
    have h1 : Pk.map ψ = imageBar2 H K := by
      rw [bar2Incl_map_subgroupOf hKH hPK, h]
    have h2 : Pk = ⊤ := by
      have hcomap : (Pk.map ψ).comap ψ = (imageBar2 H K).comap ψ := congrArg _ h1
      rw [Subgroup.comap_map_eq_self hkerP] at hcomap
      have hright : (imageBar2 H K).comap ψ = ⊤ := by
        rw [← hψrange, ← Subgroup.map_top, Subgroup.comap_map_eq_self (le_top)]
      rwa [hright] at hcomap
    have hPK' : P = K := by
      calc P = Pk.map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hPK).symm
        _ = (⊤ : Subgroup ↥K).map K.subtype := by rw [h2]
        _ = K := by rw [Subgroup.map_top, Subgroup.range_subtype]
    exact hPne hPK'
  · intro Q hPQ hQK
    have hQrange : Q ≤ ψ.range := by rwa [hψrange]
    let Qk : Subgroup ↥K := Q.comap ψ
    let Q' : Subgroup G := Qk.map K.subtype
    have hQ'K : Q' ≤ K := Subgroup.map_subtype_le _
    have hPQ' : P ≤ Q' := by
      intro p hp
      have hpbar : ψ ⟨p, hPK hp⟩ ∈ imageBar2 H P := by
        rw [← bar2Incl_map_subgroupOf hKH hPK]
        exact Subgroup.mem_map.mpr ⟨⟨p, hPK hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
      have hpQ : ψ ⟨p, hPK hp⟩ ∈ Q := hPQ hpbar
      exact Subgroup.mem_map.mpr ⟨⟨p, hPK hp⟩, Subgroup.mem_comap.mpr hpQ, rfl⟩
    have hQk : Qk = Q'.subgroupOf K := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hQ'K]
    have hQmap : Qk.map ψ = Q := Subgroup.map_comap_eq_self hQrange
    rcases hPmax Q' hPQ' hQ'K with h | h
    · left
      calc Q = Qk.map ψ := hQmap.symm
        _ = (Q'.subgroupOf K).map ψ := by rw [hQk]
        _ = (P.subgroupOf K).map ψ := by rw [h]
        _ = imageBar2 H P := bar2Incl_map_subgroupOf hKH hPK
    · right
      calc Q = Qk.map ψ := hQmap.symm
        _ = (Q'.subgroupOf K).map ψ := by rw [hQk]
        _ = (K.subgroupOf K).map ψ := by rw [h]
        _ = (⊤ : Subgroup ↥K).map ψ := by rw [Subgroup.subgroupOf_self]
        _ = imageBar2 H K := by rw [Subgroup.map_top, hψrange]

theorem imageBar2_injective_of_pCoreOf_le {H K P₁ P₂ : Subgroup G}
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal)
    (hP₁K : P₁ ≤ K) (hP₂K : P₂ ≤ K)
    (hP₁ : pCoreOf 2 K ≤ P₁) (hP₂ : pCoreOf 2 K ≤ P₂)
    (h : imageBar2 H P₁ = imageBar2 H P₂) : P₁ = P₂ := by
  let ψ : ↥K →* Bar2 H := bar2Incl hKH
  have hker₁ : ψ.ker ≤ P₁.subgroupOf K :=
    bar2Incl_ker_le_subgroupOf hKH hKn hP₁
  have hker₂ : ψ.ker ≤ P₂.subgroupOf K :=
    bar2Incl_ker_le_subgroupOf hKH hKn hP₂
  have h₁ : (P₁.subgroupOf K).map ψ = imageBar2 H P₁ :=
    bar2Incl_map_subgroupOf hKH hP₁K
  have h₂ : (P₂.subgroupOf K).map ψ = imageBar2 H P₂ :=
    bar2Incl_map_subgroupOf hKH hP₂K
  have hcomap : ((P₁.subgroupOf K).map ψ).comap ψ = ((P₂.subgroupOf K).map ψ).comap ψ := by
    rw [h₁, h₂, h]
  rw [Subgroup.comap_map_eq_self hker₁, Subgroup.comap_map_eq_self hker₂] at hcomap
  calc P₁ = (P₁.subgroupOf K).map K.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hP₁K).symm
    _ = (P₂.subgroupOf K).map K.subtype := by rw [hcomap]
    _ = P₂ := Subgroup.map_subgroupOf_eq_of_le hP₂K

theorem isSylowIn_imageBar2 {H T : Subgroup G} (hTsyl : IsSylowIn 2 T H) :
    IsSylowIn 2 (imageBar2 H T) ⊤ := by
  have hPidx : ¬ 2 ∣ ((T).subgroupOf H).index := by
    simpa [Subgroup.relIndex] using hTsyl.2.2
  let P0 : Sylow 2 ↥H :=
    (hTsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTsyl.1).symm).toSylow hPidx
  let Q0 : Sylow 2 (Bar2 H) :=
    Sylow.mapSurjective (f := piBar2 H) (QuotientGroup.mk'_surjective _) P0
  have hQ0 : (Q0 : Subgroup (Bar2 H)) = imageBar2 H T := by
    rw [Sylow.coe_mapSurjective, imageBar2, piBar2, IsPGroup.toSylow_coe]
  rw [← hQ0]
  exact isSylowIn_top Q0

theorem fstar_imageBar2_of_normal {H K T : Subgroup G}
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hTsyl : IsSylowIn 2 T H)
    (hsup : K ⊔ T = H) (hperf : ⁅K, K⁆ = K) (hsimple : IsSimpleGroup (Bar2 K)) :
    Nonempty (Bar2 K ≃* ↥(imageBar2 H K)) ∧
      (imageBar2 H K).Normal ∧ IsSimpleGroup ↥(imageBar2 H K) ∧
      ¬ IsMulCommutative ↥(imageBar2 H K) ∧
      Fstar (⊤ : Subgroup (Bar2 H)) = imageBar2 H K ∧
      Subgroup.centralizer (imageBar2 H K : Set (Bar2 H)) = ⊥ ∧
      IsPGroup 2 (Bar2 H ⧸ imageBar2 H K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn
  have hpCore : pCoreOf 2 K = K ⊓ pCoreOf 2 H :=
    CFSG.Quasithin.S1567.pCoreOf_eq_inf_pCoreOf_of_normal hKH hKN
  have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec18.Claim184LcProof.quotient_mulEquiv_map hKH
    (hpCore.le.trans inf_le_right)
  let π : ↥H →* Bar2 H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  let C : Subgroup (Bar2 H) := imageBar2 H K
  have hCnormal : C.Normal :=
    Subgroup.Normal.map hKn π (QuotientGroup.mk'_surjective _)
  haveI : C.Normal := hCnormal
  have hsimpleC : IsSimpleGroup ↥C := e.isSimpleGroup_congr.mp hsimple
  haveI : Group.IsPerfect ↥K := hperfK
  have hperfC : Group.IsPerfect ↥C := by
    let φ' : ↥K →* ↥C := (π.comp (Subgroup.inclusion hKH)).codRestrict C
      (fun k => Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKH k, k.2, rfl⟩)
    have hφ'surj : Function.Surjective φ' := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
      exact Subtype.ext hxy
    exact Group.IsPerfect.ofSurjective (f := φ') hφ'surj
  have hncC : ¬ IsMulCommutative ↥C := fun h =>
    hperfC.not_isMulCommutative ↥C h
  have hnabC' : ¬ ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
    rintro h
    exact hncC ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩
  have hnabC : ∃ a b : ↥C, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hnabC' (fun x hx y hy => congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩))
  have hT2 : IsPGroup 2 T := hTsyl.isPGroup
  have hTH : T ≤ H := hTsyl.1
  have hTbar2 : IsPGroup 2 (imageBar2 H T) := by
    have h1 : IsPGroup 2 (T.subgroupOf H) :=
      hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
    exact IsPGroup.map h1 (piBar2 H)
  have hsupC : C ⊔ imageBar2 H T = ⊤ := by
    have h1 : imageBar2 H (K ⊔ T) = imageBar2 H K ⊔ imageBar2 H T := by
      rw [imageBar2, imageBar2, imageBar2, ← Subgroup.map_sup,
        ← Subgroup.subgroupOf_sup hKH hTH]
    rw [← h1, hsup]
    simp [imageBar2, piBar2, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)]
  haveI : (C.subgroupOf (⊤ : Subgroup (Bar2 H))).Normal := hCnormal.subgroupOf ⊤
  have hquotTop : IsPGroup 2 ((⊤ : Subgroup (Bar2 H)) ⧸ C.subgroupOf ⊤) :=
    CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (p := 2) (G := Bar2 H)
      (L := C) (Q := imageBar2 H T) (K := ⊤) hTbar2 le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hCnormal]; exact le_top) hsupC
  have hquot : IsPGroup 2 (Bar2 H ⧸ C) := by
    have he : (C.subgroupOf (⊤ : Subgroup (Bar2 H))).map
        (Subgroup.topEquiv (G := Bar2 H)).toMonoidHom = C := by
      ext x
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact IsPGroup.of_equiv hquotTop
      (QuotientGroup.congr (C.subgroupOf ⊤) C Subgroup.topEquiv he)
  have hcent : Subgroup.centralizer (C : Set (Bar2 H)) = ⊥ := by
    have hZ : C ⊓ Subgroup.centralizer (C : Set (Bar2 H)) = ⊥ := by
      refine le_bot_iff.mp ?_
      rintro z ⟨hzC, hzc⟩
      have hz' : (⟨z, hzC⟩ : ↥C) ∈ Subgroup.center ↥C := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc (y : Bar2 H) y.2)
      have hc : Subgroup.center ↥C = ⊥ :=
        CFSG.Quasithin.Vol2.Ch11.SecE3.center_eq_bot_of_simple hnabC
      rw [hc] at hz'
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hz')
    have hinj : Function.Injective
        ((QuotientGroup.mk' C).comp (Subgroup.centralizer (C : Set (Bar2 H))).subtype) := by
      intro a b hab
      have h1 : (QuotientGroup.mk' C) (a : Bar2 H) = (QuotientGroup.mk' C) (b : Bar2 H) := hab
      have h2 : ((a : Bar2 H)⁻¹ * (b : Bar2 H)) ∈ C := QuotientGroup.eq.mp h1
      have h3 : ((a : Bar2 H)⁻¹ * (b : Bar2 H)) ∈
          Subgroup.centralizer (C : Set (Bar2 H)) :=
        (Subgroup.centralizer (C : Set (Bar2 H))).mul_mem
          ((Subgroup.centralizer (C : Set (Bar2 H))).inv_mem a.2) b.2
      have h4 : ((a : Bar2 H)⁻¹ * (b : Bar2 H)) ∈
          C ⊓ Subgroup.centralizer (C : Set (Bar2 H)) := ⟨h2, h3⟩
      rw [hZ] at h4
      exact Subtype.ext (inv_mul_eq_one.mp (Subgroup.mem_bot.mp h4))
    have h2 : IsPGroup 2 ↥(Subgroup.centralizer (C : Set (Bar2 H))) :=
      IsPGroup.of_injective hquot _ hinj
    have hnorm : (Subgroup.centralizer (C : Set (Bar2 H))).Normal :=
      Subgroup.normal_centralizer
    have hle : Subgroup.centralizer (C : Set (Bar2 H)) ≤
        pCoreOf 2 (⊤ : Subgroup (Bar2 H)) :=
      CFSG.ClassicalGroups.PCoreSection.le_pCoreOf le_top
        (fun x _ y hy => hnorm.conj_mem y hy x) h2
    rw [CFSG.CGT.PushingUpLit.Glue.pCoreOf_top_eq, pCore_two_bar2_eq_bot] at hle
    exact le_bot_iff.mp hle
  have hFstar : Fstar (⊤ : Subgroup (Bar2 H)) = C := by
    refine CFSG.LocalAnalysis.WeakClosure81.fstar_eq_of_isSimpleGroup_of_centralizer_eq_bot
      (H := ⊤) (X := C) le_top (hCnormal.subgroupOf ⊤) hsimpleC hnabC' ?_
    rw [top_inf_eq]
    exact hcent
  exact ⟨⟨e⟩, hCnormal, hsimpleC, hncC, hFstar, hcent, hquot⟩

theorem inFSq_of_isL2_of_normal_sup {H K T : Subgroup G} {m : ℕ}
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hTsyl : IsSylowIn 2 T H)
    (hsup : K ⊔ T = H) (hperf : ⁅K, K⁆ = K) (hL2 : IsL2 (Bar2 K) m)
    (hKc : K_L2SzAutRank) :
    InFSq m H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimpleK : IsSimpleGroup (Bar2 K) := isSimpleGroup_of_isL2_or_isSz (Or.inl hL2)
  obtain ⟨⟨e⟩, hCnormal, hsimpleC, hncC, -, hcent, hquot⟩ :=
    fstar_imageBar2_of_normal hKH hKn hTsyl hsup hperf hsimpleK
  have hnabC : ∃ a b : ↥(imageBar2 H K), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hncC ⟨⟨fun a b => h a b⟩⟩
  have hshapeC : IsL2 ↥(imageBar2 H K) m := LieModel.of_mulEquiv e hL2
  have hm : CFSG.Open.pRank 2 (⊤ : Subgroup (Bar2 H)) ≤ m :=
    hKc (Bar2 H) (imageBar2 H K) m hsimpleC hncC hcent hquot (Or.inl hshapeC)
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := Bar2 H)
  have hS : IsSylowIn 2 (S : Subgroup (Bar2 H)) ⊤ := isSylowIn_top S
  have hsupC : (imageBar2 H K) ⊔ (S : Subgroup (Bar2 H)) = ⊤ := by
    haveI : (imageBar2 H K).Normal := hCnormal
    rw [sup_comm]
    exact CFSG.section10_sylow_sup_normal_of_p_quotient_eq_top (N := imageBar2 H K) hquot S
  have hInF : InFGroup m (Bar2 H) :=
    inFGroup_of_twoRank_le hCnormal hsimpleC hnabC hcent ⟨_, hS, hsupC⟩ hm
  exact inF_top_of_inFGroup m hInF

theorem inFSq_conjClosure_sup_of_components {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) (h43c : W3Lem45_2Chief)
    (hL2 : IsL2 (Bar2 L) (S17.nOf L) ∨ IsSz (Bar2 L) (S17.nOf L))
    (hgen : orbitClosure (imageBar2 (UC22.conjClosure D.M L ⊔ D.T) L)
        (imageBar2 (UC22.conjClosure D.M L ⊔ D.T) D.T) ⊔
      imageBar2 (UC22.conjClosure D.M L ⊔ D.T) D.T = ⊤)
    (hcf : ∀ T' : Subgroup (Bar2 (UC22.conjClosure D.M L ⊔ D.T)),
      CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ → CompFactorAutInF (S17.nOf L) ⊤ T') :
    InFSq (S17.nOf L) (UC22.conjClosure D.M L ⊔ D.T) := by
  let X : Subgroup G := UC22.conjClosure D.M L
  let H : Subgroup G := X ⊔ D.T
  have hXH : X ≤ H := le_sup_left
  have hHM : H ≤ D.M := sup_le (TwelveTwentyThree.conjClosure_le hL.1.le) D.sylowM.le
  have hXN : (X.subgroupOf H).Normal := by
    have hXNM : D.M ≤ Subgroup.normalizer (X : Set G) :=
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSetOf_subset_calC_conjClosure hL).2.1
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr (hHM.trans hXNM)
  have hLXnorm : (L.subgroupOf X).Normal :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.component_normal_in_conjClosure hL
  have hLX : L ≤ X := TwelveTwentyThree.le_conjClosure D.M L
  have hLH : L ≤ H := hLX.trans hXH
  have hLsub : CFSG.Open.IsSubnormal L H :=
    CFSG.Open.IsSubnormal.trans
      (CFSG.Open.IsSubnormal.step hLX hLXnorm (CFSG.Open.IsSubnormal.refl X))
      (CFSG.Open.IsSubnormal.step hXH hXN (CFSG.Open.IsSubnormal.refl H))
  have hpCore : pCoreOf 2 L = L ⊓ pCoreOf 2 H :=
    pCoreOf_eq_inf_pCoreOf_of_isSubnormal hLsub
  have hKsub : (imageBar2 H L).IsSubnormal := by
    have h1 : CFSG.Open.IsSubnormal (L.subgroupOf H) (⊤ : Subgroup ↥H) := by
      have h2 : CFSG.Open.IsSubnormal ((L.subgroupOf H)) (H.subgroupOf H) :=
        CFSG.Quasithin.A3.subnormal_comap H.subtype hLsub
      simpa only [Subgroup.subgroupOf_self] using h2
    have h2 : CFSG.Open.IsSubnormal (imageBar2 H L) (⊤ : Subgroup (Bar2 H)) := by
      have h3 := h1.map (piBar2 H)
      rw [Subgroup.map_top,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h3
      exact h3
    exact CFSG.Open.IsSubnormal.top_iff.mp h2
  have hKq : CFSG.IsQuasisimple ↥(imageBar2 H L) := by
    obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec18.Claim184LcProof.quotient_mulEquiv_map hLH
      (hpCore.le.trans inf_le_right)
    have hqBL : CFSG.IsQuasisimple (Bar2 L) :=
      (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := Bar2 L)).mpr hL.2.2
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqBL
  refine inFSq_of_components h43c (hL2.elim (fun h => h.admissible.2.1)
    (fun h => h.admissible.2.1)) ⟨hKq, hKsub⟩ ?_ hgen hcf
  exact isSylowIn_imageBar2 (TwelveShort.isSylowIn_of_le D le_sup_right)

section Certified


variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}

theorem r18_7b_of_ne_bot_XT_diag_of_inputs (h : Hyp18 D V₀ V p L) (hx : DataExt D)
    (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (hV₀ : V₀ ≠ ⊥) (hX1 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (h43c : W3Lem45_2Chief) {H : Subgroup G}
    (hH : H = UC22.conjClosure D.M L ⊔ D.T)
    (hL2 : IsL2 (Bar2 L) (S17.nOf L) ∨ IsSz (Bar2 L) (S17.nOf L))
    (hgen : orbitClosure (imageBar2 H L) (imageBar2 H D.T) ⊔ imageBar2 H D.T = ⊤)
    (hcf : ∀ T' : Subgroup (Bar2 H), CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ →
      CompFactorAutInF (S17.nOf L) ⊤ T') :
    R18_7bAt D V₀ V p L h := by
  subst hH
  exact r18_7b_of_ne_bot_XT h hx h61 h127 h1114 h162 hTor h1482 h126 hSg hV₀ hX1
    h17_66_1 h18_4 (inFSq_conjClosure_sup_of_components h.hL.1 h43c hL2 hgen hcf)

theorem r18_7b_of_ne_bot_XT_l2 (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (hV₀ : V₀ ≠ ⊥) (hX1 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (hK : K_L2SzAutRank) (hX : UC22.conjClosure D.M L = L)
    (hL2 : IsL2 (Bar2 L) (S17.nOf L)) :
    R18_7bAt D V₀ V p L h := by
  refine r18_7b_of_ne_bot_XT h hx h61 h127 h1114 h162 hTor h1482 h126 hSg hV₀ hX1
    h17_66_1 h18_4 ?_
  rw [hX]
  set H : Subgroup G := L ⊔ D.T with hH
  have hLH : L ≤ H := le_sup_left
  have hHM : H ≤ D.M := sup_le h.hL.1.1.le D.sylowM.le
  have hNM : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.hL.1.1.le).mp
      (uc22p21j_normal_of_conjClosure_eq h.hL.1.1.le hX.symm)
  have hNH : H ≤ Subgroup.normalizer (L : Set G) := hHM.trans hNM
  have hKn : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hNH
  have hTsyl : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D le_sup_right
  have hperf : ⁅L, L⁆ = L := h.hL.1.2.1
  have hsup : L ⊔ D.T = H := rfl
  exact inFSq_of_isL2_of_normal_sup hLH hKn hTsyl hsup hperf hL2 hK

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
