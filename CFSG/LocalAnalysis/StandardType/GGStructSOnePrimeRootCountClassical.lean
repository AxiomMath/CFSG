module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCountLevi
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSU
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSp
public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.ChevTwo CFSG.LieType.Universal
  CFSG.LieType.BorelTits CFSG.SeitzReduction.LinearPilot Matrix Subgroup
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (iotaHom)
open CFSG.LieType.Universal.Symplectic (rootDatum)
open CFSG.LieType.Universal.Symplectic.SpExtras (elt elt_zero exists_stdVec_of_mem_roots
  mem_rootGroup_iff)
open CFSG.LieType.Universal.Unitary
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot CFSG.StandardType.RCSTSp CFSG.StandardType.RootCentSp

theorem ggRootInvolCountTag_PSL : GGRootInvolCountTag .PSL := by
  intro X _ _ n f ψ hadm hrk hker _ r hr
  obtain ⟨-, hf, hn, -⟩ := hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := hrk
  let ψs : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X := ψ
  have hkers : ψs.ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) := hker
  have hrs : GGRootInvolution (SpecialLinear.rootDatum m (GaloisField 2 f)) .PSL ψs r := hr
  obtain ⟨ψ', hrange, hker', hr'⟩ :=
    RCSPSL.exists_conj (F := GaloisField 2 f) (by omega) ψs hkers hrs
  have hm1 : 1 ≤ m := by omega
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  refine ⟨[ordA (m - 2) (2 ^ f)], ?_, ?_⟩
  · have hnm : (m + 1) - 3 = m - 2 := by omega
    simp [ggRootFactorOrders, hnm]
  change GGInvolCentTypedBy ψs.range r [ordA (m - 2) (2 ^ f)]
  rw [← hrange, hr']
  set P := LinFusion.ggTransPlacement (m := m) hm1 with hP
  set T := ggInvSL (m + 1) 1 (GaloisField 2 f) with hT
  set N : Subgroup X := ggRCSX ψ'.range (ψ' T)
  set Q : Subgroup X := (P.radical (GaloisField 2 f)).map ψ' with hQ
  set L : Subgroup X := (blockSpecialLinear (K := GaloisField 2 f) P.free).map ψ' with hLdef
  have hcardJ : Fintype.card P.free = m - 1 := by
    rw [Fintype.card_coe, P.card_free]
    omega
  have hcardF : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
  have hsub : m - 1 - 1 = m - 2 := by omega
  have hL : IsChevTwoLayeredBy ↥L [ordA (m - 2) (2 ^ f)] := by
    have hLrange : (ψ'.comp (blockEmbed P.free)).range = L := by
      rw [MonoidHom.range_comp, range_blockEmbed]
    let fJ : SpecialLinearGroup P.free (GaloisField 2 f) →* ↥L :=
      (ψ'.comp (blockEmbed P.free)).codRestrict L fun x => by
        rw [← hLrange]
        exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    have hfJ : Function.Surjective fJ := by
      intro y
      have hy : (y : X) ∈ (ψ'.comp (blockEmbed P.free)).range := by
        rw [hLrange]
        exact y.2
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hy
      exact ⟨w, Subtype.ext hw⟩
    have hkercenter : fJ.ker ≤
        Subgroup.center (SpecialLinearGroup P.free (GaloisField 2 f)) := by
      intro d hd
      rw [Subgroup.mem_center_iff]
      intro e
      have hd1 : blockEmbed P.free d ∈ ψ'.ker := by
        rw [MonoidHom.mem_ker]
        have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hd)
        simpa [fJ] using h
      have hdc := hker' hd1
      have hcomm : blockEmbed P.free d * blockEmbed P.free e =
          blockEmbed P.free e * blockEmbed P.free d :=
        (Subgroup.mem_center_iff.mp hdc (blockEmbed P.free e)).symm
      have hEq : blockEmbed P.free (d * e * d⁻¹) = blockEmbed P.free e := by
        rw [map_mul, map_mul, map_inv, hcomm]
        group
      have hEq' : d * e * d⁻¹ = e := blockEmbed_injective P.free hEq
      calc e * d = (d * e * d⁻¹) * d := by rw [hEq']
        _ = d * e := by group
    have hker_solv : Group.IsSolvable ↥fJ.ker :=
      Group.isSolvable_of_comm fun a b => by
        refine Subtype.ext ?_
        have h := (Subgroup.mem_center_iff.mp (hkercenter a.2)
          (b : SpecialLinearGroup P.free (GaloisField 2 f))).symm
        simpa only [Subgroup.coe_mul] using h
    exact IsChevTwoLayeredBy.of_surjective fJ hfJ hker_solv
      (by
        simpa [hcardJ, hcardF, hsub] using
          isChevTwoLayeredBy_specialLinear P.free (GaloisField 2 f))
  have hX : N = Q ⊔ L := by
    rw [show N = ggRCSX ψ'.range (ψ' T) from rfl,
      RCSPSL.X_eq (F := GaloisField 2 f) hm1 ψ' hker']
    rw [InvPlacement.core, RCSPSL.leviOne_eq_bot, bot_sup_eq, Subgroup.map_sup]
  have hQ2 : IsPGroup 2 Q := by
    have h := (RCSPSL.radical_isPGroup (F := GaloisField 2 f) hm1).map ψ'
    simpa [Q, P, hP] using h
  have hQN : Q ≤ N := by
    rw [hX]
    exact le_sup_left
  have hQn : (Q.subgroupOf N).Normal := by
    simpa [Q, N, P, T, hP, hT] using
      RCSPSL.radical_normal_X (F := GaloisField 2 f) hm1 ψ' hker'
  have hQnorm : N ≤ Subgroup.normalizer (Q : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).1 hQn
  have hLN : L ≤ N := by
    rw [hX]
    exact le_sup_right
  have hLQ : L ≤ Subgroup.normalizer (Q : Set X) := hLN.trans hQnorm
  exact ggInvolCentTypedBy_of_oTwoPrime_eq_sup hQ2 hLQ hX hL

theorem ggRootInvolCountTag_PSU : GGRootInvolCountTag .PSU := by
  intro X _ _ n f
  by_cases hf : 1 ≤ f
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have e : ggU .PSU n f =
        ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [e] at ⊢
    intro ψ _hadm hrk hker _hC r hr
    have hn : 4 ≤ n := by
      change 2 ≤ n / 2 at hrk
      omega
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hnk : (k + 2) - 3 = k - 1 := by omega
    refine ⟨[ordTwistedA (k - 1) (2 ^ f)], ?_, ?_⟩
    · simp [ggRootFactorOrders, hnk]
    change GGInvolCentTypedBy ψ.range r [ordTwistedA (k - 1) (2 ^ f)]
    have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
      card_galoisField_two_mul 2 f hf
    obtain ⟨hr2, γ, ⟨-, hlong⟩, u₀, hru⟩ := hr
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
    have hx1 : x ≠ 1 := by
      rintro rfl
      simp at hr2
    obtain ⟨a, ha⟩ := exists_conj_ggInvSU_of_longRoot hF (hlong (Or.inl rfl)) hx hx1
    set h := u₀ * a with hh
    set ψ' := ψ.comp (MulAut.conj h).toMonoidHom with hψ'
    have hr' : ψ' (ggInvSU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (k + 2) 1) =
        ψ ((MulAut.conj u₀).toMonoidHom x) := by
      simp only [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ha,
        hh]
      congr 1
      group
    have hrange : ψ'.range = ψ.range := by
      rw [hψ', MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
        ← MonoidHom.range_eq_map]
    have hker' : ψ'.ker ≤ center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
        (k + 2)) := by
      intro v hv
      have hz : h * v * h⁻¹ ∈ center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
          (k + 2)) := hker hv
      have h1 := (inferInstance :
        (center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (k + 2))).Normal).conj_mem _
        hz h⁻¹
      rwa [inv_inv, show h⁻¹ * (h * v * h⁻¹) * h = v by group] at h1
    have hQ2 : IsPGroup 2 ((RCSTSU.suRad (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
        k).map ψ') := RCSTSU.suRad_isPGroup.map ψ'
    have hQX : (RCSTSU.suRad (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) k).map ψ' ≤
        ggRCSX ψ'.range (ψ' (ggInvSU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
          (k + 2) 1)) :=
      ggRCST_map_le_ggRCSX_of_isPGroup ψ' (RCSTSU.suRad_le_centralizer (k := k))
        RCSTSU.suRad_isPGroup
    have hXQ : ggRCSX ψ'.range (ψ' (ggInvSU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
          (k + 2) 1)) ≤
        normalizer (((RCSTSU.suRad (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) k).map ψ') :
          Set X) :=
      ggRCST_ggRCSX_le_normalizer hker' (RCSTSU.hZ_su _) RCSTSU.ggInvSU_mul_self
        (RCSTSU.centralizer_le_normalizer_suRad (σ := unitaryInvolution (GaloisField 2 (2 * f))
          2 f) (k := k))
    have hL₀X : (ψ'.comp (iotaHom (σ := unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
          (m := k))).range ≤
        ggRCSX ψ'.range (ψ' (ggInvSU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
          (k + 2) 1)) :=
      ggRCST_range_le_ggRCSX ψ' iotaHom RCSTSU.range_iotaHom_le_centralizer
        (RootCentSU.top_le_closure_SU hF (by omega))
    have hXle := RCSTSU.ggRCSX_le_sup hf ψ' hker'
    have hXeq : ggRCSX ψ'.range (ψ' (ggInvSU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
          (k + 2) 1)) =
        (RCSTSU.suRad (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) k).map ψ' ⊔
          (ψ'.comp (iotaHom (σ := unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
            (m := k))).range :=
      le_antisymm hXle (sup_le hQX hL₀X)
    have hLQ : (ψ'.comp (iotaHom (σ := unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
          (m := k))).range ≤
        normalizer (((RCSTSU.suRad (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) k).map ψ') :
          Set X) := hL₀X.trans hXQ
    haveI : Fintype (GaloisField 2 (2 * f)) := Fintype.ofFinite _
    have hSU : IsChevTwoLayeredBy (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) k)
        [ordTwistedA (k - 1) (2 ^ f)] := by
      have hcard : Fintype.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
        rw [← Nat.card_eq_fintype_card]
        exact hF
      exact (isChevTwoLayeredBy_statedSU k (2 ^ f) (GaloisField 2 (2 * f)) hcard).of_mulEquiv
        (equivStatedSU (p := 2) hF k)
    have hL : IsChevTwoLayeredBy ↥((ψ'.comp (iotaHom (σ := unitaryInvolution
        (GaloisField 2 (2 * f)) 2 f) (m := k))).range)
        [ordTwistedA (k - 1) (2 ^ f)] := by
      let φ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) k →*
          ↥((ψ'.comp (iotaHom (σ := unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
            (m := k))).range) :=
        (ψ'.comp (iotaHom (σ := unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
          (m := k))).rangeRestrict
      have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective _
      have hkerφ : φ.ker ≤ center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) k) := by
        rw [MonoidHom.ker_rangeRestrict]
        exact RCSTSU.ker_comp_iotaHom_le ψ' hker'
      have hsolv : Group.IsSolvable ↥φ.ker :=
        Group.isSolvable_of_comm fun a b =>
          Subtype.ext (Subgroup.mem_center_iff.1 (hkerφ a.2)
            (b : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) k)).symm
      exact IsChevTwoLayeredBy.of_surjective φ hφ hsolv hSU
    have hmain : GGInvolCentTypedBy ψ'.range
        (ψ' (ggInvSU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (k + 2) 1))
        [ordTwistedA (k - 1) (2 ^ f)] :=
      ggInvolCentTypedBy_of_oTwoPrime_eq_sup hQ2 hLQ hXeq hL
    rwa [hrange, hr'] at hmain
  · intro ψ hadm
    exact absurd hadm.2.1 hf

private theorem ggInvolCentTypedBy_top_of_sup_eq {U : Type} [Group U] [Finite U] {y : U}
    {Q L : Subgroup U} {o : List ℕ} (hQ2 : IsPGroup 2 Q)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set U))
    (hC : Subgroup.centralizer ({y} : Set U) = Q ⊔ L)
    (hL : IsChevTwoLayeredBy ↥L o) : GGInvolCentTypedBy (⊤ : Subgroup U) y o :=
  ggInvolCentTypedBy_of_sup_eq hQ2 hLQ (by rw [inf_top_eq, hC]) hL

private theorem ggInvolCentTypedBy_top_siegDiag {n : ℕ} {F : Type} [Field F] [Fintype F]
    [Finite F] [CharP F 2] (i : Fin n) :
    GGInvolCentTypedBy (⊤ : Subgroup (StatedSp n F)) (siegDiag F i 1)
      [ggSpLayerOrd (n - 1) (Fintype.card F)] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.isLt; omega⟩
  have hL : IsChevTwoLayeredBy ↥(complSp F i) [ggSpLayerOrd m (Fintype.card F)] :=
    (isChevTwoLayeredBy_statedSp m F).of_mulEquiv (complSpEquiv (K := F) i).symm
  simpa using ggInvolCentTypedBy_top_of_sup_eq (isPGroup_transvRadical (K := F) (p := i))
    (complSp_le_normalizer_transvRadical (K := F) (p := i))
    (centralizer_siegDiag_eq_sup (K := F) (p := i)) hL

private theorem ggInvolCentTypedBy_top_short_two {F : Type} [Field F] [Fintype F] [Finite F]
    [CharP F 2] {i j : Fin 2} (hij : i ≠ j) :
    GGInvolCentTypedBy (⊤ : Subgroup (StatedSp 2 F)) (twoCentralElt 2 i j (0 : F) 1)
      [ordA 1 (Fintype.card F)] := by
  have hC : Subgroup.centralizer ({twoCentralElt 2 i j (0 : F) 1} :
      Set (StatedSp 2 F)) = wRadical F i j ⊔ (shortBlock F hij).range := by
    refine le_antisymm ?_ (sup_le (wRadical_le_centralizer_twoCentralElt 0 1) ?_)
    · have h := centralizer_a2_le_of_ne (K := F) hij
      rwa [suppGroup_offPQ_two hij, sup_bot_eq] at h
    · rintro _ ⟨A, rfl⟩
      exact shortBlock_mem_centralizer hij A 1
  have hCN : Subgroup.centralizer ({twoCentralElt 2 i j (0 : F) 1} :
      Set (StatedSp 2 F)) ≤ normalizer (wRadical F i j : Set (StatedSp 2 F)) := by
    rw [centralizer_twoCentralElt_eq_sup hij (one_ne_zero (α := F))]
    exact sup_le le_normalizer (range_leviHom_le_normalizer_wRadical hij one_ne_zero)
  have hLQ : (shortBlock F hij).range ≤
      normalizer (wRadical F i j : Set (StatedSp 2 F)) := by
    rw [hC] at hCN
    exact le_sup_right.trans hCN
  have hL : IsChevTwoLayeredBy ↥((shortBlock F hij).range) [ordA 1 (Fintype.card F)] :=
    (isChevTwoLayeredBy_specialLinear (Fin 2) F).of_mulEquiv
      (MonoidHom.ofInjective (f := shortBlock F hij) (shortBlock_injective hij)).symm
  exact ggInvolCentTypedBy_top_of_sup_eq (isPGroup_wRadical hij) hLQ hC hL

private theorem ggInvolCentTypedBy_top_short {F : Type} [Field F] [Fintype F] [Finite F]
    [CharP F 2] (n : ℕ) :
    GGInvolCentTypedBy (⊤ : Subgroup (StatedSp (n + 3) F))
      (twoCentralElt (n + 3) 1 2 (0 : F) 1)
      [ordA 1 (Fintype.card F), ggSpLayerOrd (n + 1) (Fintype.card F)] := by
  have h12 := one_ne_two_fin (n := n)
  set S : Subgroup (StatedSp (n + 3) F) := (shortBlock F h12).range with hS
  set T : Subgroup (StatedSp (n + 3) F) := spCompl12 F n with hT
  obtain ⟨hC, hSQ, hTQ, hST⟩ := centralizer_a2_facts (F := F) (n := n)
  have hS' : IsChevTwoLayeredBy ↥(S.subgroupOf (S ⊔ T)) [ordA 1 (Fintype.card F)] :=
    (isChevTwoLayeredBy_specialLinear (Fin 2) F).of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe (le_sup_left : S ≤ S ⊔ T)).trans
        (MonoidHom.ofInjective (f := shortBlock F h12) (shortBlock_injective h12)).symm)
  have hT' : IsChevTwoLayeredBy ↥(T.subgroupOf (S ⊔ T))
      [ggSpLayerOrd (n + 1) (Fintype.card F)] :=
    (isChevTwoLayeredBy_statedSp (n + 1) F).of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe (le_sup_right : T ≤ S ⊔ T)).trans
        (spCompl12Equiv F n).symm)
  have hsup : S.subgroupOf (S ⊔ T) ⊔ T.subgroupOf (S ⊔ T) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : S ≤ S ⊔ T) (le_sup_right : T ≤ S ⊔ T)]
    exact Subgroup.subgroupOf_self (S ⊔ T)
  have hcomm : ∀ a ∈ S.subgroupOf (S ⊔ T), ∀ b ∈ T.subgroupOf (S ⊔ T), Commute a b := by
    intro a ha b hb
    have ha' : ((a : ↥(S ⊔ T)) : StatedSp (n + 3) F) ∈ S := ha
    have hb' : ((b : ↥(S ⊔ T)) : StatedSp (n + 3) F) ∈ T := hb
    refine Subtype.ext ?_
    exact (Subgroup.mem_centralizer_iff.mp (hST ha') _ hb').symm
  have hL : IsChevTwoLayeredBy ↥(S ⊔ T)
      [ordA 1 (Fintype.card F), ggSpLayerOrd (n + 1) (Fintype.card F)] := by
    simpa using IsChevTwoLayeredBy.of_commute_sup _ _ hcomm hsup hS' hT'
  exact ggInvolCentTypedBy_top_of_sup_eq (isPGroup_wRadical h12) (sup_le hSQ hTQ) hC hL

theorem ggRootInvolCountTag_PSp : GGRootInvolCountTag .PSp := by
  intro X _ _ n f ψ hadm _ hker _ r hr
  obtain ⟨-, hf, -, -⟩ := hadm
  let ψ' : StatedSp n (GaloisField 2 f) →* X := ψ
  have hker' : ψ'.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)) := hker
  have hr' : GGRootInvolution (rootDatum n (GaloisField 2 f)) .PSp ψ' r := hr
  change ∃ o ∈ ggRootFactorOrders .PSp n f, GGInvolCentTypedBy ψ'.range r o
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcardF : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
  have hψ : Function.Injective ψ' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker'.trans (center_statedSp_eq_bot (K := GaloisField 2 f) n).le
  obtain ⟨hr2, γ, hγ, u, hru⟩ := hr'
  obtain ⟨-, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  obtain ⟨ρ, hρ⟩ := exists_stdVec_of_mem_roots hγ.1
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hρ).1 hx
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx1 (elt_zero ρ)
  have hcongr : ∀ o : List ℕ,
      GGInvolCentTypedBy (⊤ : Subgroup (StatedSp n (GaloisField 2 f))) (elt ρ c) o ↔
        GGInvolCentTypedBy (⊤ : Subgroup (StatedSp n (GaloisField 2 f))) (elt ρ 1) o := by
    intro o
    refine ggInvolCentTypedBy_congr ?_
    simpa using centralizer_elt_eq (F := GaloisField 2 f) ρ hc
  have hgoal : ∃ o ∈ ggRootFactorOrders .PSp n f,
      GGInvolCentTypedBy (⊤ : Subgroup (StatedSp n (GaloisField 2 f))) (elt ρ 1) o := by
    rcases elt_one_eq_conj (F := GaloisField 2 f) ρ with ⟨g, i, hg⟩ | ⟨g, i, j, hij, hg⟩
    ·
      refine ⟨[ggSpLayerOrd (n - 1) (2 ^ f)], ?_, ?_⟩
      · simp [ggRootFactorOrders]
      · rw [hg]
        exact (ggInvolCentTypedBy_conj_iff
          (o := [ggSpLayerOrd (n - 1) (2 ^ f)])
          (G₀ := (⊤ : Subgroup (StatedSp n (GaloisField 2 f))))
          (r := siegDiag (GaloisField 2 f) i 1) (g := g)
          (hg := Subgroup.le_normalizer (Subgroup.mem_top g))).mpr
          (by simpa [hcardF] using ggInvolCentTypedBy_top_siegDiag (F := GaloisField 2 f) i)
    · by_cases hn3 : 3 ≤ n
      ·
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
        obtain ⟨g', hg'⟩ := exists_conj_one_two (F := GaloisField 2 f) (n := m) hij
        have hne : ¬ (m + 3 = 2) := by omega
        have hnm : (m + 3) - 2 = m + 1 := by omega
        refine ⟨[ordA 1 (2 ^ f), ggSpLayerOrd (m + 1) (2 ^ f)], ?_, ?_⟩
        · simp [ggRootFactorOrders, hne, hnm]
        · rw [hg]
          refine (ggInvolCentTypedBy_conj_iff
            (o := [ordA 1 (2 ^ f), ggSpLayerOrd (m + 1) (2 ^ f)])
            (G₀ := (⊤ : Subgroup (StatedSp (m + 3) (GaloisField 2 f))))
            (r := twoCentralElt (m + 3) i j (0 : GaloisField 2 f) 1) (g := g)
            (hg := Subgroup.le_normalizer (Subgroup.mem_top g))).mpr ?_
          rw [hg']
          exact (ggInvolCentTypedBy_conj_iff
            (o := [ordA 1 (2 ^ f), ggSpLayerOrd (m + 1) (2 ^ f)])
            (G₀ := (⊤ : Subgroup (StatedSp (m + 3) (GaloisField 2 f))))
            (r := twoCentralElt (m + 3) 1 2 (0 : GaloisField 2 f) 1) (g := g')
            (hg := Subgroup.le_normalizer (Subgroup.mem_top g'))).mpr
            (by
              simpa [hcardF] using ggInvolCentTypedBy_top_short (F := GaloisField 2 f) m)
      ·
        have hn2 : n = 2 := by omega
        subst hn2
        refine ⟨[ordA 1 (2 ^ f)], ?_, ?_⟩
        · simp [ggRootFactorOrders]
        · rw [hg]
          exact (ggInvolCentTypedBy_conj_iff
            (o := [ordA 1 (2 ^ f)])
            (G₀ := (⊤ : Subgroup (StatedSp 2 (GaloisField 2 f))))
            (r := twoCentralElt 2 i j (0 : GaloisField 2 f) 1) (g := g)
            (hg := Subgroup.le_normalizer (Subgroup.mem_top g))).mpr
            (by
              simpa [hcardF] using
                ggInvolCentTypedBy_top_short_two (F := GaloisField 2 f) hij)
  obtain ⟨o, ho, hP⟩ := hgoal
  refine ⟨o, ho, ?_⟩
  have hrange : GGInvolCentTypedBy ψ'.range (ψ' (elt ρ c)) o :=
    ggInvolCentTypedBy_range_of_top hψ ((hcongr o).mpr hP)
  have hEq : ψ' ((MulEquiv.toMonoidHom (MulAut.conj u)) (elt ρ c)) =
      ψ' u * ψ' (elt ρ c) * (ψ' u)⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  rw [hEq]
  exact (ggInvolCentTypedBy_conj_iff (o := o) (G₀ := ψ'.range) (r := ψ' (elt ρ c))
    (g := ψ' u) (hg := Subgroup.le_normalizer
      (show ψ' u ∈ ψ'.range from ⟨u, rfl⟩))).mpr hrange

end CFSG.StandardType
