module

public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1D
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

theorem exists_j2_surj_of_le {L H : Subgroup G} (hHL : H ≤ L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {S : Type} [Group S] [IsSimpleGroup S] (hnab : ∃ x y : S, x * y ≠ y * x)
    (f : ↥H →* S) (hf : Function.Surjective f) :
    ∃ (H' : Subgroup CFSG.Blueprint.NativeSporadic.J2) (f' : ↥H' →* S),
      Function.Surjective f' := by
  obtain ⟨e⟩ := hJ
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set ψ : ↥H →* CFSG.Blueprint.NativeSporadic.J2 :=
    e.toMonoidHom.comp ((QuotientGroup.mk' θ).comp (Subgroup.inclusion hHL)) with hψ
  have hker_eq : ψ.ker = θ.comap (Subgroup.inclusion hHL) := by
    rw [hψ, MonoidHom.ker_comp_of_injective _ _ e.injective,
      ← MonoidHom.comap_ker (QuotientGroup.mk' θ) (Subgroup.inclusion hHL),
      QuotientGroup.ker_mk']
  have hθsolv : Group.IsSolvable ↥θ :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  have hker_solv : Group.IsSolvable ↥ψ.ker := by
    haveI := hθsolv
    rw [hker_eq]
    let g : ↥(θ.comap (Subgroup.inclusion hHL)) →* ↥θ :=
      { toFun := fun x => ⟨Subgroup.inclusion hHL x.1, x.2⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun a b => Subtype.ext rfl }
    have hg : Function.Injective g := by
      intro a b hab
      exact Subtype.ext (Subgroup.inclusion_injective hHL (congrArg Subtype.val hab))
    exact Group.isSolvable_of_isSolvable_injective (f := g) hg
  have hker_le : ψ.ker ≤ f.ker := by
    have hnormal : ((ψ.ker).map f).Normal := Subgroup.Normal.map inferInstance f hf
    haveI := hnormal
    have hsolv_image : Group.IsSolvable ↥((ψ.ker).map f) := by
      haveI := hker_solv
      exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective f ψ.ker)
    rcases Subgroup.Normal.eq_bot_or_eq_top ((ψ.ker).map f) with hbot | htop
    · exact (Subgroup.map_eq_bot_iff _).mp hbot
    · exfalso
      have hSsolv : Group.IsSolvable S := by
        have htop' : Group.IsSolvable ↥(⊤ : Subgroup S) := htop ▸ hsolv_image
        haveI := htop'
        exact Group.isSolvable_of_surjective
          (f := ((Subgroup.topEquiv (G := S) : ↥(⊤ : Subgroup S) ≃* S) :
            ↥(⊤ : Subgroup S) →* S)) (Subgroup.topEquiv (G := S)).surjective
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hSsolv x y)
  let L1 : ↥H ⧸ ψ.ker →* S := QuotientGroup.lift ψ.ker f hker_le
  have hL1 : Function.Surjective L1 :=
    QuotientGroup.lift_surjective_of_surjective ψ.ker f hf hker_le
  let E1 : ↥ψ.range ≃* ↥H ⧸ ψ.ker := (QuotientGroup.quotientKerEquivRange ψ).symm
  refine ⟨ψ.range, L1.comp (E1 : ↥ψ.range →* ↥H ⧸ ψ.ker), ?_⟩
  intro s
  obtain ⟨q, hq⟩ := hL1 s
  obtain ⟨r, rfl⟩ := E1.surjective q
  exact ⟨r, by simpa using hq⟩

theorem exists_mul_inv_mem_pPrimeCoreOf {K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (hc : ∀ x ∈ K, c * x * c⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 K)
    (hcard : Nat.card (Subgroup.zpowers c) = 3)
    {x : G} (hx : x ∈ K) :
    ∃ t ∈ K ⊓ Subgroup.centralizer ({c} : Set G), t * x⁻¹ ∈ pPrimeCoreOf 3 K := by
  have hc3 : c ^ 3 = 1 := by
    rw [← hcard, Nat.card_zpowers]
    exact pow_orderOf_eq_one c
  obtain ⟨y, hyK, hyx, hfix⟩ := exists_fixed_mul_inv_mem_pPrimeCoreOf hcN le_rfl hc3 hc hx
  refine ⟨y, ⟨hyK, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, hyx⟩
  calc y * c = (c * y * c⁻¹) * c := by rw [hfix]
    _ = c * y := by group

theorem inf_centralizer_le_normalizer_inf {K L : Subgroup G} {c : G}
    (hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    K ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ L : Set G) := by
  intro t ht
  have hconj : ∀ u ∈ K ⊓ Subgroup.centralizer ({c} : Set G),
      ∀ x ∈ (K ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ L,
        u * x * u⁻¹ ∈ (K ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ L := by
    intro u hu x hx
    refine ⟨⟨K.mul_mem (K.mul_mem hu.1 hx.1.1) (K.inv_mem hu.1), ?_⟩, ?_⟩
    · exact (Subgroup.centralizer ({c} : Set G)).mul_mem
        ((Subgroup.centralizer ({c} : Set G)).mul_mem hu.2 hx.1.2)
        ((Subgroup.centralizer ({c} : Set G)).inv_mem hu.2)
    · exact (Subgroup.mem_normalizer_iff.mp (hCL hu.2) x).mp hx.2
  change t ∈ Subgroup.normalizer (((K ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ L : Subgroup G) : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨hconj t ht x, fun hx => by
    have h := hconj t⁻¹ (Subgroup.inv_mem _ ht) (t * x * t⁻¹) hx
    rwa [show t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ = x by group] at h⟩

theorem surjective_inf_of_covers {K : Subgroup G} {c : G} {S : Type} [Group S]
    (φ : ↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* S)
    (hcov : ∀ x ∈ K, ∃ t ∈ K ⊓ Subgroup.centralizer ({c} : Set G), t * x⁻¹ ∈ pPrimeCoreOf 3 K) :
    ∀ s : S, ∃ t : ↥(K ⊓ Subgroup.centralizer ({c} : Set G)),
      (φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)))
        (Subgroup.inclusion (show K ⊓ Subgroup.centralizer ({c} : Set G) ≤ K from inf_le_left) t)
        = s := by
  set π : ↥K →* S := φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) with hπ
  have hπ_surj : Function.Surjective π := by
    intro s
    obtain ⟨q, rfl⟩ := φ.surjective s
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥K) q
    exact ⟨z, rfl⟩
  have hπ_ker : ∀ z : ↥K, π z = 1 ↔ z ∈ CFSG.pPrimeCore 3 ↥K := by
    intro z
    have h1 : π z = φ (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) z) := rfl
    rw [h1, map_eq_one_iff φ φ.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  intro s
  obtain ⟨x, rfl⟩ := hπ_surj s
  obtain ⟨t, htT, htO⟩ := hcov (x : G) x.2
  have hTle : K ⊓ Subgroup.centralizer ({c} : Set G) ≤ K := inf_le_left
  have hzO : (⟨t * (x : G)⁻¹, K.mul_mem htT.1 (K.inv_mem x.2)⟩ : ↥K) ∈
      CFSG.pPrimeCore 3 ↥K :=
    (Subgroup.mem_map_iff_mem (f := K.subtype) K.subtype_injective).mp htO
  have h1 : π ⟨t * (x : G)⁻¹, K.mul_mem htT.1 (K.inv_mem x.2)⟩ = 1 := (hπ_ker _).mpr hzO
  have h2 : π (Subgroup.inclusion hTle ⟨t, htT⟩) * (π x)⁻¹ = 1 := by
    have hEq : π (Subgroup.inclusion hTle ⟨t, htT⟩) * (π x)⁻¹ =
        π ⟨t * (x : G)⁻¹, K.mul_mem htT.1 (K.inv_mem x.2)⟩ := by
      rw [← map_inv, ← map_mul]
      congr 1
    rw [hEq, h1]
  have h3 : π (Subgroup.inclusion hTle ⟨t, htT⟩) = π x := by
    have h4 := congrArg (fun y => y * π x) h2
    simpa [mul_assoc] using h4
  exact ⟨⟨t, htT⟩, h3⟩

theorem inf_le_pPrimeCoreOf_of_surj {K L : Subgroup G} {c : G} {S : Type} [Group S]
    [IsSimpleGroup S] {φ : ↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* S}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hnab : ∃ x y : S, x * y ≠ y * x)
    (hSJ : ∀ (H' : Subgroup CFSG.Blueprint.NativeSporadic.J2) (f' : ↥H' →* S),
      ¬ Function.Surjective f')
    (hT_surj : ∀ s : S, ∃ t : ↥(K ⊓ Subgroup.centralizer ({c} : Set G)),
      (φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)))
        (Subgroup.inclusion (show K ⊓ Subgroup.centralizer ({c} : Set G) ≤ K from inf_le_left) t)
        = s)
    (hTM : K ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ L : Set G)) :
    (K ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ L ≤ pPrimeCoreOf 3 K := by
  classical
  set T : Subgroup G := K ⊓ Subgroup.centralizer ({c} : Set G) with hT
  set M : Subgroup G := T ⊓ L with hM
  set π : ↥K →* S := φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) with hπ
  have hTK : T ≤ K := inf_le_left
  have hMK : M ≤ K := fun x hx => hx.1.1
  have hπ_ker : ∀ z : ↥K, π z = 1 ↔ z ∈ CFSG.pPrimeCore 3 ↥K := by
    intro z
    have h1 : π z = φ (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) z) := rfl
    rw [h1, map_eq_one_iff φ φ.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcovπ : ∀ s : S, ∃ t : ↥T, π (Subgroup.inclusion hTK t) = s := by
    intro s
    obtain ⟨t, hts⟩ := hT_surj s
    exact ⟨t, hts⟩
  have hN_normal : ((⊤ : Subgroup ↥M).map (π.comp (Subgroup.inclusion hMK))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, -, hfm⟩ := (Subgroup.mem_map (f := π.comp (Subgroup.inclusion hMK)) (K := ⊤)).mp hn
    obtain ⟨t, htg⟩ := hcovπ g
    have htm : (t : G) * (m : G) * (t : G)⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp (hTM t.2) (m : G)).mp m.2
    have hEq : g * n * g⁻¹ =
        (π.comp (Subgroup.inclusion hMK)) ⟨(t : G) * (m : G) * (t : G)⁻¹, htm⟩ := by
      rw [← htg, ← hfm]
      simp only [MonoidHom.comp_apply, Subgroup.coe_inclusion]
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
    rw [hEq]
    exact Subgroup.mem_map_of_mem (π.comp (Subgroup.inclusion hMK))
      (x := ⟨(t : G) * (m : G) * (t : G)⁻¹, htm⟩) (Subgroup.mem_top _)
  haveI := hN_normal
  rcases Subgroup.Normal.eq_bot_or_eq_top
      ((⊤ : Subgroup ↥M).map (π.comp (Subgroup.inclusion hMK))) with hbot | htop
  · intro x hx
    have hxker : (⟨x, hx⟩ : ↥M) ∈ (π.comp (Subgroup.inclusion hMK)).ker :=
      (Subgroup.map_eq_bot_iff ⊤).mp hbot (Subgroup.mem_top _)
    have h1 : π ⟨x, hMK hx⟩ = 1 := by
      have h1' : (π.comp (Subgroup.inclusion hMK)) ⟨x, hx⟩ = 1 := hxker
      rwa [show (π.comp (Subgroup.inclusion hMK)) ⟨x, hx⟩ = π ⟨x, hMK hx⟩ from rfl] at h1'
    exact Subgroup.mem_map_of_mem K.subtype ((hπ_ker _).mp h1)
  · exfalso
    have hsurj : Function.Surjective (π.comp (Subgroup.inclusion hMK)) := by
      intro s
      have hs : s ∈ (⊤ : Subgroup ↥M).map (π.comp (Subgroup.inclusion hMK)) := by
        rw [htop]
        exact Subgroup.mem_top s
      obtain ⟨m, -, hfm⟩ :=
        (Subgroup.mem_map (f := π.comp (Subgroup.inclusion hMK)) (K := ⊤)).mp hs
      exact ⟨m, hfm⟩
    obtain ⟨H', f', hf'⟩ :=
      exists_j2_surj_of_le (L := L) (H := M) inf_le_right hJ hnab
        (π.comp (Subgroup.inclusion hMK)) hsurj
    exact hSJ H' f' hf'

theorem centralizes_of_mem_inf {A L K : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hK : K ∈ scriptY A) {S : Type} [Group S] [IsSimpleGroup S]
    (hnab : ∃ x y : S, x * y ≠ y * x) (φ : ↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* S)
    (hSJ : ∀ (H' : Subgroup CFSG.Blueprint.NativeSporadic.J2) (f' : ↥H' →* S),
      ¬ Function.Surjective f')
    (hc : ∀ x ∈ K, c * x * c⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 K) {d : G} (hdA : d ∈ A) (hdL : d ∈ L) :
    ∀ x ∈ K, d * x * d⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 K := by
  intro x hx
  have hcA : c ∈ A := hR.toSec14Std.toSec13Data.mem_A
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hK.2
  have hcard : Nat.card (Subgroup.zpowers c) = 3 := hR.toSec14Std.toSec13Data.card_zpowers
  have e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2 := hJ.some
  have h3 : 3 ∣ Nat.card L :=
    three_dvd_card_of_thetaQuot e
      (by rw [CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2]; norm_num)
  have hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd hR.toSec14Std h3
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := hR.toSec14Std.toSec13Data.A_le_centralizer
  have hcov : ∀ y ∈ K, ∃ t ∈ K ⊓ Subgroup.centralizer ({c} : Set G),
      t * y⁻¹ ∈ pPrimeCoreOf 3 K := fun y hy =>
    exists_mul_inv_mem_pPrimeCoreOf (hAK hcA) hc hcard hy
  have hTM : K ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ L : Set G) :=
    inf_centralizer_le_normalizer_inf hCL
  have hT_surj := surjective_inf_of_covers (φ := φ) hcov
  have hMle : (K ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ L ≤ pPrimeCoreOf 3 K :=
    inf_le_pPrimeCoreOf_of_surj (φ := φ) hJ hnab hSJ hT_surj hTM
  obtain ⟨t, htT, htO⟩ := hcov x hx
  have hdN : d ∈ Subgroup.normalizer (K : Set G) := hAK hdA
  have hdO : d ∈ Subgroup.normalizer (pPrimeCoreOf 3 K : Set G) :=
    normalizer_le_normalizer_pPrimeCoreOf 3 K hdN
  have hdT : ∀ y ∈ K ⊓ Subgroup.centralizer ({c} : Set G),
      d * y * d⁻¹ ∈ K ⊓ Subgroup.centralizer ({c} : Set G) := by
    intro y hy
    refine ⟨(Subgroup.mem_normalizer_iff.mp hdN y).mp hy.1, ?_⟩
    exact (Subgroup.centralizer ({c} : Set G)).mul_mem
      ((Subgroup.centralizer ({c} : Set G)).mul_mem (hAC hdA) hy.2)
      ((Subgroup.centralizer ({c} : Set G)).inv_mem (hAC hdA))
  have hMmem : t * d * t⁻¹ * d⁻¹ ∈ (K ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ L := by
    refine ⟨?_, ?_⟩
    · have h1 : d * t⁻¹ * d⁻¹ ∈ K ⊓ Subgroup.centralizer ({c} : Set G) :=
        hdT t⁻¹ (Subgroup.inv_mem _ htT)
      rw [show t * d * t⁻¹ * d⁻¹ = t * (d * t⁻¹ * d⁻¹) by group]
      exact Subgroup.mul_mem _ htT h1
    · exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCL htT.2) d).mp hdL) (L.inv_mem hdL)
  have hdt : d * t * d⁻¹ * t⁻¹ ∈ pPrimeCoreOf 3 K := by
    have hinv : (t * d * t⁻¹ * d⁻¹)⁻¹ ∈ (K ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ L :=
      Subgroup.inv_mem _ hMmem
    have hO : (t * d * t⁻¹ * d⁻¹)⁻¹ ∈ pPrimeCoreOf 3 K := hMle hinv
    rwa [show (t * d * t⁻¹ * d⁻¹)⁻¹ = d * t * d⁻¹ * t⁻¹ by group] at hO
  have hdo : d * (t * x⁻¹)⁻¹ * d⁻¹ ∈ pPrimeCoreOf 3 K :=
    (Subgroup.mem_normalizer_iff.mp hdO (t * x⁻¹)⁻¹).mp ((pPrimeCoreOf 3 K).inv_mem htO)
  have hgoal : d * x * d⁻¹ * x⁻¹ =
      (d * (t * x⁻¹)⁻¹ * d⁻¹) * (d * t * d⁻¹ * t⁻¹) * (t * x⁻¹) := by
    have hx' : x = (t * x⁻¹)⁻¹ * t := by group
    rw [hx']
    group
  rw [hgoal]
  exact (pPrimeCoreOf 3 K).mul_mem ((pPrimeCoreOf 3 K).mul_mem hdo hdt) htO

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1
