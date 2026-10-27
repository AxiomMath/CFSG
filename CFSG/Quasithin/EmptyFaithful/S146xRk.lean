module

public import CFSG.Quasithin.EmptyFaithful.S146F22
public import CFSG.Quasithin.EmptyFaithful.S146D7
public import CFSG.Quasithin.EmptyFaithful.S146E4
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section KBarHom

variable {G : Type} [Group G] [Finite G]

noncomputable def kbarActHom (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (KBar K) where
  toFun s := kbarAut K s.1 s.2
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    rw [kbarAut_mk]
    show (QuotientGroup.mk (conjAutOn K 1 _ k) : KBar K) = QuotientGroup.mk k
    congr 1
    exact Subtype.ext (by simp [conjAutOn_apply])
  map_mul' a b := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    show kbarAut K (a * b : ↥(Subgroup.normalizer (K : Set G))).1 _ (QuotientGroup.mk k) =
      kbarAut K a.1 a.2 (kbarAut K b.1 b.2 (QuotientGroup.mk k))
    rw [kbarAut_mk, kbarAut_mk, kbarAut_mk]
    congr 1
    exact Subtype.ext (by simp [conjAutOn_apply, mul_assoc])

theorem kbarActHom_mk (K : Subgroup G) (s : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    kbarActHom K s (QuotientGroup.mk k) = QuotientGroup.mk (conjAutOn K s.1 s.2 k) :=
  kbarAut_mk K s.1 s.2 k

omit [Finite G] in
theorem card_le_four_of_kbarIsL3Two {K : Subgroup G} (h : KbarIsL3Two K)
    (A : Subgroup (MulAut (KBar K))) [CFSG.IsElementaryAbelian 2 ↥A] : Nat.card A ≤ 2 ^ 2 := by
  obtain ⟨e⟩ := h
  let e' : KBar K ≃* CFSG.QuasithinUnique.Setup.Family.GL32 :=
    e.trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3)
  let Φ := MulAut.congr e'
  have : Finite (MulAut (KBar K)) := Finite.of_equiv _ Φ.symm.toEquiv
  have hcard : Nat.card (MulAut (KBar K)) = 336 := by
    rw [Nat.card_congr Φ.toEquiv, CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.SteinbergBR.card_le_sq_of_orderOf
    (g := Φ.symm CFSG.LieType.SteinbergBR.AutGL32.alphaAut) (k := 3)
    (by rw [MulEquiv.orderOf_eq, CFSG.LieType.SteinbergBR.AutGL32.orderOf_alphaAut])
    (by rw [hcard]; norm_num) A

end KBarHom

theorem input14624FourRank_proof : Input14624FourRank := by
  intro G _ _ T M S _hB K U₁ U₂ s u γ γ' g hfull hKeq hL3
  classical
  obtain ⟨⟨c19, _, c23, hK, _, _, _, _⟩, _, hgeom⟩ := hfull
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hHKT : mcOf T = K ⊔ T := by
    rw [hKeq]
    exact c23.1.2
  have hsimple : IsSimpleGroup (KBar K) := (c19 (mcOf T) hG).2 K hK
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) (mcOf T)) := S.lemma_14_5_15_two hG
  have hXH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T :=
    (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2.Uγ_le_H hgeom.1
  have hXN : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (K : Set G) := hXH.trans hKn
  set X := F8.Uγ (VZ T M) (mcOf T) (g : G) with hX
  have hXab : IsElemAbelian 2 X := by
    rw [isElemAbelian_iff]
    constructor
    · intro x hx y hy
      have hx' := B6.mem_conjSub.mp hx
      have hy' := B6.mem_conjSub.mp hy
      have hc := isElemAbelian_comm hUab hx' hy'
      calc x * y = (g : G) * ((g : G)⁻¹ * x * (g : G) * ((g : G)⁻¹ * y * (g : G))) * (g : G)⁻¹ := by
            group
        _ = (g : G) * ((g : G)⁻¹ * y * (g : G) * ((g : G)⁻¹ * x * (g : G))) * (g : G)⁻¹ := by
            rw [hc]
        _ = y * x := by group
    · intro x hx
      have hx' := B6.mem_conjSub.mp hx
      have h2 := isElemAbelian_pow_eq_one hUab hx'
      have e : ((g : G)⁻¹ * x * (g : G)) ^ 2 = (g : G)⁻¹ * x ^ 2 * (g : G) := by
        simp only [pow_two]; group
      rw [e] at h2
      have : x ^ 2 = (g : G) * ((g : G)⁻¹ * x ^ 2 * (g : G)) * (g : G)⁻¹ := by group
      rw [this, h2]; group
  let Φ : ↥X →* MulAut (KBar K) := (kbarActHom K).comp (Subgroup.inclusion hXN)
  have hΦmk : ∀ (x : ↥X) (k : ↥K), Φ x (QuotientGroup.mk k) =
      QuotientGroup.mk (conjAutOn K (x : G) (hXN x.2) k) := fun x k =>
    kbarActHom_mk K (Subgroup.inclusion hXN x) k
  have hcommX : ∀ x y : ↥X, x * y = y * x := fun x y =>
    Subtype.ext (isElemAbelian_comm hXab x.2 y.2)
  have hsqX : ∀ x : ↥X, x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa using isElemAbelian_pow_eq_one hXab x.2)
  have hEA : CFSG.IsElementaryAbelian 2 ↥(Φ.range) := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨a, x, rfl⟩ := a
      obtain ⟨b, y, rfl⟩ := b
      apply Subtype.ext
      show Φ x * Φ y = Φ y * Φ x
      rw [← map_mul, ← map_mul, hcommX]
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
      obtain ⟨a, x, rfl⟩ := a
      apply Subtype.ext
      show (Φ x) ^ 2 = 1
      rw [← map_pow, hsqX, map_one]
  have hcard4 : Nat.card Φ.range ≤ 2 ^ 2 := card_le_four_of_kbarIsL3Two hL3 Φ.range
  have hker : Φ.ker ≤
      (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)).subgroupOf X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx1 : Φ x = 1 := hx
    have hcomm : ∀ k ∈ K, (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 (mcOf T) := by
      intro k hk
      have h1 := congrArg (fun α : MulAut (KBar K) => α (QuotientGroup.mk (⟨k, hk⟩ : ↥K))) hx1
      simp only [hΦmk, MulAut.one_apply] at h1
      have h2 := QuotientGroup.eq.mp h1.symm
      have h3 : k⁻¹ * ((x : G) * k * (x : G)⁻¹) ∈ pCoreOf 2 K := Subgroup.mem_subgroupOf.mp h2
      have hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T) :=
        A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
      have h4 : k * (k⁻¹ * ((x : G) * k * (x : G)⁻¹)) * k⁻¹ ∈ pCoreOf 2 K :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hk) _).mp h3
      have e : (x : G) * k * (x : G)⁻¹ * k⁻¹ = k * (k⁻¹ * ((x : G) * k * (x : G)⁻¹)) * k⁻¹ := by
        group
      rw [e]
      exact hQK h4
    have hxQ : (x : G) ∈ pCoreOf 2 (mcOf T) :=
      mem_pCoreOf_of_commutator_mem hK hsimple hKn hT2 hHKT (hXH x.2) hcomm
    rw [← S.lemma_14_5_15_four hG] at hxQ
    exact ⟨x.2, hxQ.2.1, hxQ.2.2⟩
  have hdvd : (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)).relIndex X ∣
      Nat.card Φ.range := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_of_le hker
  have hpos : 0 < Nat.card Φ.range := Nat.card_pos
  have hle4 : (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)).relIndex X ≤ 4 :=
    (Nat.le_of_dvd hpos hdvd).trans (by simpa using hcard4)
  unfold mIdx
  have hne : (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)).relIndex X ≠ 0 :=
    (Nat.pos_of_dvd_of_pos hdvd hpos).ne'
  generalize (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)).relIndex X = n
    at hle4 hne
  have h1 : padicValNat 2 n ≤ Nat.log 2 n := padicValNat_le_nat_log n
  have h2 : Nat.log 2 n < 3 := Nat.log_lt_of_lt_pow hne (by omega : n < 2 ^ 3)
  omega

end CFSG.Quasithin
