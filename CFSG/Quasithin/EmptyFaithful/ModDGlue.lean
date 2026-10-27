module

public import CFSG.Quasithin.EmptyFaithful.ModDNonsplit
public import CFSG.Quasithin.EmptyFaithful.ModCGlue
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6CatSetting
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146R2
public import CFSG.Quasithin.EmptyFaithful.S146R3
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import Certificates.Certificate8026Base
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.ModD

open CFSG.CosetTable CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open scoped IsMulCommutative

section Klein

variable {U : Type*} [CommGroup U] [Finite U]

theorem eq_one_of_fixed_odd (hsq : ∀ a : U, a * a = 1) (α : MulAut U) {V : Subgroup U}
    (hV4 : Nat.card V = 4) (hα : ∀ v ∈ V, α v ∈ V) {z : U} (hzV : z ∈ V) (hz : α z ≠ z) {n : ℕ}
    (hn : Odd n) (hαn : α ^ n = 1) {w : U} (hwV : w ∈ V) (hw : α w = w) : w = 1 := by
  classical
  by_contra hw1
  have hz1 : z ≠ 1 := fun h => hz (by rw [h, map_one])
  have hwz : w ≠ z := fun h => hz (h ▸ hw)
  have hsub : ({1, w, z, w * z} : Set U) ⊆ (V : Set U) := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact hwV
    · exact hzV
    · exact V.mul_mem hwV hzV
  have h4 : ({1, w, z, w * z} : Set U).ncard = 4 := by
    have e : ({1, w, z, w * z} : Set U) = ↑({1, w, z, w * z} : Finset U) := by simp
    rw [e, Set.ncard_coe_finset]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      exact hw1 (mul_right_cancel (b := z) (by rw [one_mul]; exact h.symm))
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hwz, fun h => hz1 (mul_eq_left.1 h.symm)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hw1, Ne.symm hz1,
        fun h => hwz (mul_right_cancel (b := z) (by rw [hsq z]; exact h.symm))⟩
  have hVn : (V : Set U).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hV4
  have hVeq : (V : Set U) = {1, w, z, w * z} :=
    (Set.eq_of_subset_of_ncard_le hsub (by rw [hVn, h4]) (Set.toFinite _)).symm
  have hαzV : α z ∈ ({1, w, z, w * z} : Set U) := by
    rw [← hVeq]
    exact hα z hzV
  have hαz : α z = w * z := by
    rcases hαzV with h | h | h | h
    · exact absurd (α.injective (h.trans (map_one α).symm)) hz1
    · exact absurd (α.injective (h.trans hw.symm)) (Ne.symm hwz)
    · exact absurd h hz
    · exact h
  have h2 : α (α z) = z := by
    rw [hαz, map_mul, hw, hαz, ← mul_assoc, hsq w, one_mul]
  have h2' : (α ^ 2) z = z := by
    rw [pow_two, MulAut.mul_apply]
    exact h2
  have hpow : ∀ k : ℕ, ((α ^ 2) ^ k) z = z := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, h2', ih]
  obtain ⟨m, rfl⟩ := hn
  have hfin : (α ^ (2 * m + 1)) z = α z := by
    rw [pow_succ', MulAut.mul_apply, pow_mul, hpow]
  rw [hαn, MulAut.one_apply] at hfin
  exact hz hfin.symm

end Klein


theorem exists_psi {K : Type} [Group K] [Finite K] (hQ : IsPSU 3 3 1 (K ⧸ CFSG.pCore 2 K))
    (P : Sylow 2 K) :
    ∃ ψ : K →* U33G, Function.Surjective ψ ∧ ψ.ker = CFSG.pCore 2 K ∧
      (P : Subgroup K).map ψ = u33Data.T := by
  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel (Or.inl ⟨by decide, hQ⟩)
  obtain ⟨e2⟩ := CFSG.Quasithin.u33Pres_mulEquiv_PSU3
  let e : (K ⧸ CFSG.pCore 2 K) ≃* U33G := e1.trans e2.symm
  let ψ₀ : K →* U33G := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 K))
  have hψ₀s : Function.Surjective ψ₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have : Finite U33G := (CFSG.Quasithin.u33Pres_finite_card_le).1
  let P' : Sylow 2 U33G := P.mapSurjective hψ₀s
  let Q : Sylow 2 U33G := u33_syl.1.toSylow u33_syl.2
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq U33G P' Q
  refine ⟨(MulAut.conj c).toMonoidHom.comp ψ₀, ?_, ?_, ?_⟩
  · exact (MulAut.conj c).surjective.comp hψ₀s
  · ext k
    simp [ψ₀]
  · have h1 : ((c • P' : Sylow 2 U33G) : Subgroup U33G) = u33Data.T := by
      rw [hc]
      rfl
    rw [← h1, Sylow.coe_subgroup_smul]
    rw [← Subgroup.map_map, Subgroup.pointwise_smul_def]
    have h2 : (↑P' : Subgroup U33G) = (↑P : Subgroup K).map ψ₀ := Sylow.coe_mapSurjective hψ₀s P
    rw [h2]
    rfl


theorem psi_not_mem_T {K : Type} [Group K] [Finite K] (ψ : K →* U33G) (hψk : ψ.ker = CFSG.pCore 2 K) {y : K}
    (hy1 : y ≠ 1) (hodd : Odd (orderOf y)) : ψ y ∉ u33Data.T := by
  intro hT
  have h2 : IsPGroup 2 ↥u33Data.T := u33_syl.1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2) ⟨ψ y, hT⟩
  have hk' : orderOf (ψ y) = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (⟨ψ y, hT⟩ : ↥u33Data.T)
  have hdvd : orderOf (ψ y) ∣ orderOf y := orderOf_map_dvd ψ y
  have hk0 : k = 0 := by
    by_contra hk0
    have h2dvd : 2 ∣ orderOf y := by
      have : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
      rw [← hk'] at this
      exact this.trans hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
  have hmem : y ∈ ψ.ker := hk'
  rw [hψk] at hmem
  have hpc : IsPGroup 2 ↥(CFSG.pCore 2 K) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup (G := K) 2
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hpc) ⟨y, hmem⟩
  have hj' : orderOf y = 2 ^ j := by
    rw [← hj]
    exact Subgroup.orderOf_coe (⟨y, hmem⟩ : ↥(CFSG.pCore 2 K))
  have hj0 : j = 0 := by
    by_contra hj0
    have : 2 ∣ orderOf y := by
      rw [hj']
      exact dvd_pow_self 2 hj0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj'
  exact hy1 hj'

theorem eq_top_of_map_eq_top {K : Type} [Group K] (ψ : K →* U33G) (hψk : ψ.ker = CFSG.pCore 2 K)
    {N : Subgroup K} (hN : CFSG.pCore 2 K ≤ N) (htop : N.map ψ = ⊤) : N = ⊤ := by
  rw [eq_top_iff]
  intro k _
  have hk : ψ k ∈ N.map ψ := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨n, hn, hnk⟩ := Subgroup.mem_map.1 hk
  have h1 : n⁻¹ * k ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnk, inv_mul_cancel]
  rw [hψk] at h1
  have := N.mul_mem hn (hN h1)
  simpa using this

theorem exists_phi {G : Type} [Group G] [Finite G] {K : Subgroup G} (hshort : IsShort2 K)
    (ψ : ↥K →* U33G) (hψs : Function.Surjective ψ) (hψk : ψ.ker = CFSG.pCore 2 ↥K) :
    ∃ φ : U33G →* MulAut ↥(blockU K), ∀ (k : ↥K) (w : ↥(blockU K)),
      ((φ (ψ k) w : ↥(blockU K)) : G) = (k : G) * w * (k : G)⁻¹ := by
  have hKW : K ≤ Subgroup.normalizer (blockU K : Set G) := C1.le_normalizer_blockU K
  let φ₀ : ↥K →* MulAut ↥(blockU K) := A4.actionOn (blockU K) K hKW
  have hker : ψ.ker ≤ φ₀.ker := by
    intro q hq
    rw [hψk] at hq
    rw [MonoidHom.mem_ker]
    ext w
    have hq' : q ∈ CFSG.Open.pCore 2 ↥K := by
      exact hq
    have hqmem : (q : G) ∈ pCoreOf 2 K := ⟨q, hq', rfl⟩
    have hwc : (w : G) ∈ Subgroup.centralizer (blockQ K : Set G) := (hshort.2.2.1.1 w.2).2
    have h1 := Subgroup.mem_centralizer_iff.1 hwc (q : G) hqmem
    show (q : G) * w * (q : G)⁻¹ = w
    rw [h1]
    group
  refine ⟨ψ.liftOfSurjective hψs ⟨φ₀, hker⟩, fun k w => ?_⟩
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  try rfl


theorem g22_bound {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {u : G} {I I₂ K : Subgroup G}
    (c : Facts14610 T M H u I I₂) (hK : Concl14610List T M I I₂ K) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hG2 : IsG2Block K) :
    Nat.card (conjClosure (VZ T M) I₂) ≤ 2 ^ 3 := by
  classical
  have S : Setting146 G T M := c.setting
  have hshort : IsShort2 K := hG2.1
  have hTM : T ≤ M := S.hyp1281.inM.2
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hI₂I : I₂ ≤ I := c.gen ▸ le_sup_right
  have hTI₂ : T ⊓ I ≤ I₂ := c.le_I₂
  have hKI : K ≤ I := hK.le
  have hWU : wOf1469 K = blockU K := ModB.wOf1469_eq_blockU_of_short hshort
  have hVW : VZ T M ≤ blockU K := hWU ▸ hK.v_le_w
  have hI1M : i1Of1469 T M I ≤ M := by
    refine sup_le ?_ (inf_le_left.trans hTM)
    exact ((oTwoUpper_le _).trans inf_le_left).trans S.hyp1281.le
  have hTI₁ : T ⊓ I ≤ i1Of1469 T M I := le_sup_right
  have hnormKI : (K.subgroupOf I).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKI).2 hK.normal
  have hO2K : pCoreOf 2 K ≤ T ⊓ I :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K I hKI hnormKI).trans
      (pCoreOf_le_of_isSylowTwoOf hsyl)
  have hsub : (K.subgroupOf I).IsSubnormal := hnormKI.isSubnormal
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.RankOneRecog.exists_sylow_inf_of_subnormal hsyl hKI hsub
  obtain ⟨ψ, hψs, hψk, hψP⟩ := exists_psi hG2.2.1 P
  obtain ⟨φ, hφ⟩ := exists_phi hshort ψ hψs hψk
  have hPmem : ∀ k : ↥K, k ∈ (P : Subgroup ↥K) ↔ (k : G) ∈ T ⊓ I := by
    intro k
    constructor
    · intro hk
      have h1 : (k : G) ∈ (P : Subgroup ↥K).map K.subtype := ⟨k, hk, rfl⟩
      rw [hP] at h1
      exact h1.1
    · intro hk
      have h1 : (k : G) ∈ (T ⊓ I) ⊓ K := ⟨hk, k.2⟩
      rw [← hP] at h1
      obtain ⟨k', hk', hkk'⟩ := h1
      have : k' = k := Subtype.ext hkk'
      rw [← this]
      exact hk'
  have hy : ∃ y ∈ yOfL22 T M ⊓ I, Odd (orderOf y) ∧ y ∉ mcOf T := by
    by_contra hcon
    push Not at hcon
    exact S.not_lI_le_mcOf hLT ((Subgroup.closure_le _).mpr fun y hy => hcon y hy.1 hy.2)
  obtain ⟨y, hyLI, hyodd, hyG⟩ := hy
  obtain ⟨z₀, hzZ, hzy⟩ : ∃ z ∈ quasithinOmegaOneCenter T, ¬ (z * y = y * z) := by
    by_contra hno
    push Not at hno
    exact hyG (Subgroup.mem_centralizer_iff.mpr hno)
  have hzV : z₀ ∈ VZ T M := le_conjClosure _ _ hzZ
  have hz1 : z₀ ≠ 1 := by
    rintro rfl
    exact hzy (by simp)
  have hyI : y ∈ I := hyLI.2
  have hyK : y ∈ K := by
    rw [hK.eq_residual]
    exact mem_oTwoUpper_of_odd hyI hyodd
  have hyI₁ : y ∈ i1Of1469 T M I := Subgroup.mem_sup_left (mem_oTwoUpper_of_odd hyLI hyodd)
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyG (Subgroup.one_mem _)
  obtain ⟨b, hb⟩ := ModC.card_eq_of_s3 c.s3
  have h3 : 3 ∣ Nat.card ↥I₂ := ⟨2 * 2 ^ b, by rw [hb]; ring⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥I₂) 3 h3
  set g : G := (g₀ : G) with hgdef
  have hgI₂ : g ∈ I₂ := g₀.2
  have hgI : g ∈ I := hI₂I hgI₂
  have hgord : orderOf g = 3 := by rw [hgdef, Subgroup.orderOf_coe, hg₀]
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hgord
    omega
  have hgK : g ∈ K := by
    rw [hK.eq_residual]
    exact mem_oTwoUpper_of_odd hgI (by rw [hgord]; exact ⟨1, rfl⟩)
  have hsqU : ∀ w : ↥(blockU K), w ^ 2 = 1 := fun w => Subtype.ext (hshort.2.2.1.2 w w.2)
  have hcomm : IsMulCommutative ↥(blockU K) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext
      (C1.blockU_comm hshort a.1 a.2 b.1 (C1.blockU_le_blockQ hshort b.2))
  have hsq : ∀ a : ↥(blockU K), a * a = 1 := fun a => by rw [← pow_two]; exact hsqU a
  have hZU : blockZ K ≤ blockU K := inf_le_left
  let Z' : Subgroup ↥(blockU K) := (blockZ K).subgroupOf (blockU K)
  have hcardU : Nat.card (↥(blockU K) ⧸ Z') = 2 ^ 6 := hG2.2.2.1
  have hZfix : ∀ g : U33G, ∀ ζ ∈ Z', φ g ζ = ζ := by
    intro g ζ hζ
    obtain ⟨k, rfl⟩ := hψs g
    apply Subtype.ext
    rw [hφ]
    have hζc : (ζ : G) ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_subgroupOf.1 hζ).2
    have h1 := Subgroup.mem_centralizer_iff.1 hζc (k : G) k.2
    show (k : G) * (ζ : G) * (k : G)⁻¹ = (ζ : G)
    rw [h1, mul_inv_cancel_right]
  have hirr : ∀ N : Subgroup ↥(blockU K), Z' ≤ N → (∀ g : U33G, ∀ n ∈ N, φ g n ∈ N) →
      N = Z' ∨ N = ⊤ := by
    intro N hZN hN
    have hfwd : ∀ k ∈ K, ∀ h ∈ N.map (blockU K).subtype, k * h * k⁻¹ ∈ N.map (blockU K).subtype := by
      intro k hk h hh
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hh
      refine Subgroup.mem_map.2 ⟨φ (ψ ⟨k, hk⟩) n, hN _ n hn, ?_⟩
      exact hφ ⟨k, hk⟩ n
    have hnorm : K ≤ Subgroup.normalizer ((N.map (blockU K).subtype : Subgroup G) : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨hfwd k hk h, fun hh => ?_⟩
      have h1 := hfwd k⁻¹ (K.inv_mem hk) _ hh
      have e : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
      rwa [e] at h1
    have hZW : blockZ K ≤ N.map (blockU K).subtype := by
      intro x hx
      exact Subgroup.mem_map.2 ⟨⟨x, hZU hx⟩, hZN (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    rcases hshort.2.2.2.2.2 (N.map (blockU K).subtype) hZW
      (Subgroup.map_subtype_le N) hnorm with h | h
    · left
      apply Subgroup.map_injective (blockU K).subtype_injective
      rw [h]
      exact (Subgroup.map_subgroupOf_eq_of_le hZU).symm
    · right
      apply Subgroup.map_injective (blockU K).subtype_injective
      rw [h, Subgroup.map_top, Subgroup.range_subtype]
  have hzU : z₀ ∈ blockU K := hVW hzV
  let z : ↥(blockU K) := ⟨z₀, hzU⟩
  have hzT : ∀ g ∈ u33Data.T, φ g z = z := by
    intro g hg
    rw [← hψP] at hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
    have hkT : (k : G) ∈ T := ((hPmem k).1 hk).1
    have h1 := S146T.comm_Z_T hkT hzZ
    apply Subtype.ext
    rw [hφ]
    show (k : G) * z₀ * (k : G)⁻¹ = z₀
    rw [h1]
    group
  let V' : Subgroup ↥(blockU K) := (VZ T M).subgroupOf (blockU K)
  have hzV' : z ∈ V' := hzV
  have hV4 : Nat.card ↥V' = 4 := by
    have h1 : Nat.card ↥V' = Nat.card ↥(VZ T M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv
    rw [h1]
    exact S.hyp.rank_two
  let Y₁ : Subgroup U33G := ((i1Of1469 T M I).subgroupOf K).map ψ
  let Y₂ : Subgroup U33G := (I₂.subgroupOf K).map ψ
  have hY₁T : u33Data.T ≤ Y₁ := by
    rw [← hψP]
    exact Subgroup.map_mono (fun k hk => hTI₁ ((hPmem k).1 hk))
  have hY₂T : u33Data.T ≤ Y₂ := by
    rw [← hψP]
    exact Subgroup.map_mono (fun k hk => hTI₂ ((hPmem k).1 hk))
  have hY₁1 : Y₁ ≠ u33Data.T := by
    intro h
    refine psi_not_mem_T ψ hψk (y := (⟨y, hyK⟩ : ↥K)) (fun h' => hy1 (congrArg Subtype.val h')) ?_ ?_
    · rw [← Subgroup.orderOf_coe]
      exact hyodd
    · rw [← h]
      exact Subgroup.mem_map.2 ⟨⟨y, hyK⟩, hyI₁, rfl⟩
  have hY₂1 : Y₂ ≠ u33Data.T := by
    intro h
    refine psi_not_mem_T ψ hψk (y := (⟨g, hgK⟩ : ↥K)) (fun h' => hg1 (congrArg Subtype.val h')) ?_ ?_
    · rw [← Subgroup.orderOf_coe]
      show Odd (orderOf g)
      rw [hgord]
      exact ⟨1, rfl⟩
    · rw [← h]
      exact Subgroup.mem_map.2 ⟨⟨g, hgK⟩, hgI₂, rfl⟩
  have hqT : ∀ q ∈ CFSG.pCore 2 ↥K, (q : G) ∈ T ⊓ I := by
    intro q hq
    have hq' : q ∈ CFSG.Open.pCore 2 ↥K := by
      exact hq
    exact hO2K ⟨q, hq', rfl⟩
  have hKI₁ : Y₁ = ⊤ → I ≤ i1Of1469 T M I := by
    intro h
    have h1 := eq_top_of_map_eq_top ψ hψk (N := (i1Of1469 T M I).subgroupOf K)
      (fun q hq => hTI₁ (hqT q hq)) h
    have hK1 : K ≤ i1Of1469 T M I := by
      intro k hk
      have h2 : (⟨k, hk⟩ : ↥K) ∈ (i1Of1469 T M I).subgroupOf K := by
        rw [h1]
        exact Subgroup.mem_top _
      exact h2
    exact hK.eq_sup.le.trans (sup_le hK1 hTI₁)
  have hKI₂ : Y₂ = ⊤ → I ≤ I₂ := by
    intro h
    have h1 := eq_top_of_map_eq_top ψ hψk (N := I₂.subgroupOf K)
      (fun q hq => hTI₂ (hqT q hq)) h
    have hK1 : K ≤ I₂ := by
      intro k hk
      have h2 : (⟨k, hk⟩ : ↥K) ∈ I₂.subgroupOf K := by
        rw [h1]
        exact Subgroup.mem_top _
      exact h2
    exact hK.eq_sup.le.trans (sup_le hK1 hTI₂)
  have hY₁2 : Y₁ ≠ ⊤ := fun h => c.hI.1.2.2 ((hKI₁ h).trans hI1M)
  have hHmc : H ≤ mcOf T := S.le_mcOf c.hH
  have hY₂2 : Y₂ ≠ ⊤ := fun h => c.hI.1.2.1 (((hKI₂ h).trans c.I₂_le).trans hHmc)
  have hY12 : Y₁ ≠ Y₂ := by
    intro hY
    apply hY₁2
    have hN₁ : oTwoUpper (i1Of1469 T M I) ≤ (Y₁.comap ψ).map K.subtype := by
      intro x hx
      have hxI₁ : x ∈ i1Of1469 T M I := oTwoUpper_le _ hx
      have hxK : x ∈ K :=
        ((oTwoUpper_mono (i1Of1469_le T M I)).trans (le_of_eq hK.eq_residual.symm)) hx
      exact Subgroup.mem_map.2 ⟨⟨x, hxK⟩, Subgroup.mem_comap.2
        (Subgroup.mem_map.2 ⟨⟨x, hxK⟩, hxI₁, rfl⟩), rfl⟩
    have hN₂ : oTwoUpper I₂ ≤ (Y₁.comap ψ).map K.subtype := by
      intro x hx
      have hxI₂ : x ∈ I₂ := oTwoUpper_le _ hx
      have hxK : x ∈ K := ((oTwoUpper_mono hI₂I).trans (le_of_eq hK.eq_residual.symm)) hx
      refine Subgroup.mem_map.2 ⟨⟨x, hxK⟩, Subgroup.mem_comap.2 ?_, rfl⟩
      rw [hY]
      exact Subgroup.mem_map.2 ⟨⟨x, hxK⟩, hxI₂, rfl⟩
    have hKN := sup_le hN₁ hN₂
    rw [← hK.gen] at hKN
    rw [eq_top_iff]
    intro g' _
    obtain ⟨k, rfl⟩ := hψs g'
    obtain ⟨k', hk', hkk'⟩ := Subgroup.mem_map.1 (hKN k.2)
    have : k' = k := Subtype.ext hkk'
    rw [← this]
    exact Subgroup.mem_comap.1 hk'
  have hVinv : ∀ g ∈ Y₁, ∀ v ∈ V', φ g v ∈ V' := by
    intro g' hg' v hv
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg'
    have hkM : (k : G) ∈ M := hI1M hk
    show ((φ (ψ k) v : ↥(blockU K)) : G) ∈ VZ T M
    rw [hφ]
    exact (Subgroup.mem_normalizer_iff.mp (hMV hkM) (v : G)).mp hv
  have hzY : ∀ g ∈ Y₂, φ g z = z := by
    intro g' hg'
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg'
    have hkH : (k : G) ∈ mcOf T := hHmc (c.I₂_le hk)
    have h1 := Subgroup.mem_centralizer_iff.1 hkH z₀ hzZ
    apply Subtype.ext
    rw [hφ]
    show (k : G) * z₀ * (k : G)⁻¹ = z₀
    rw [← h1, mul_inv_cancel_right]
  have hyY₁ : ψ ⟨y, hyK⟩ ∈ Y₁ := Subgroup.mem_map.2 ⟨⟨y, hyK⟩, hyI₁, rfl⟩
  have hαz : φ (ψ ⟨y, hyK⟩) z ≠ z := by
    intro h
    apply hzy
    have h1 := congrArg Subtype.val h
    rw [hφ] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have hαn : (φ (ψ ⟨y, hyK⟩)) ^ orderOf y = 1 := by
    rw [← map_pow, ← map_pow]
    have : (⟨y, hyK⟩ : ↥K) ^ orderOf y = 1 := by
      rw [← Subgroup.orderOf_mk y hyK]
      exact pow_orderOf_eq_one _
    rw [this, map_one, map_one]
  have hVZ : V' ⊓ Z' = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    exact Subgroup.mem_bot.2 (eq_one_of_fixed_odd hsq (φ (ψ ⟨y, hyK⟩)) hV4 (hVinv _ hyY₁) hzV' hαz
      hyodd hαn hw.1 (hZfix _ w hw.2))
  have hzZ' : z ∉ Z' := fun h => hαz (hZfix _ z h)
  have hb := pencil_bound hsq φ Z' hZfix hcardU hirr hzZ' hzT hzV' hV4 hVZ hY₁T hY₂T hY₁1 hY₁2 hY₂1 hY₂2
    hY12 hzY hVinv
  have hle : conjClosure (VZ T M) I₂ ≤
      (Subgroup.closure {m : ↥(blockU K) | ∃ g ∈ Y₂, ∃ v ∈ V', m = φ g v}).map (blockU K).subtype := by
    refine conjClosure_le fun h hh a ha => ?_
    have hhI : h ∈ I := hI₂I hh
    have hmem : h ∈ ((K ⊔ (T ⊓ I) : Subgroup G) : Set G) := by
      rw [← hK.eq_sup]
      exact hhI
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K (T ⊓ I) (inf_le_right.trans hK.normal)] at hmem
    obtain ⟨k, hk, t, ht, rfl⟩ := hmem
    have hkI₂ : k ∈ I₂ := by
      have h1 : k * t * t⁻¹ ∈ I₂ := I₂.mul_mem hh (I₂.inv_mem (hTI₂ ht))
      simpa using h1
    have hta : t * a * t⁻¹ ∈ VZ T M :=
      (Subgroup.mem_normalizer_iff.mp (hMV (hTM ht.1)) a).mp ha
    have e : k * t * a * (k * t)⁻¹ = k * (t * a * t⁻¹) * k⁻¹ := by group
    rw [e]
    have haU : a ∈ blockU K := hVW ha
    have htaU : t * a * t⁻¹ ∈ blockU K := hVW hta
    refine Subgroup.mem_map.2 ⟨φ (ψ ⟨k, hk⟩) ⟨t * a * t⁻¹, htaU⟩, Subgroup.subset_closure
      ⟨ψ ⟨k, hk⟩, Subgroup.mem_map.2 ⟨⟨k, hk⟩, hkI₂, rfl⟩, ⟨t * a * t⁻¹, htaU⟩, hta, rfl⟩, ?_⟩
    exact (hφ ⟨k, hk⟩ ⟨t * a * t⁻¹, htaU⟩)
  have hcard1 : Nat.card ↥(conjClosure (VZ T M) I₂) ≤ 8 := by
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Subgroup.card_map_of_injective (blockU K).subtype_injective]
    exact hb
  exact hcard1.trans (by norm_num)

end CFSG.Quasithin.ModD
