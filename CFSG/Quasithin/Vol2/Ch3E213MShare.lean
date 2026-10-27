module

public import CFSG.Quasithin.Vol2.Ch3E213MDefs
public import CFSG.Quasithin.Vol2.Ch3E213MTr
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedCore
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonNonsplitTorus
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)

theorem exists_equiv_projectiveSL_of_isPSL {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ n ∧
      Nonempty (X ≃* projectiveSL 2 k) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK,
    ⟨e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 2 K).symm⟩⟩

theorem exists_equiv_suzukiGroup_of_isSz {X : Type} [Group X] {n : ℕ} (h : IsSz n X) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = 2 ^ n ∧ Nonempty (X ≃* CFSG.Blueprint.suzukiGroup a k) := by
  obtain ⟨-, a, ha, K, _, _, hn, hK, he⟩ := h
  exact ⟨a, ha, hn, K, inferInstance, inferInstance, hK, he⟩

theorem card_projectiveSL_two_pow {k : Type} [Field k] [Finite k] {n : ℕ}
    (hk : Nat.card k = 2 ^ n) : Nat.card (projectiveSL 2 k) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := by
    have : Fintype k := Fintype.ofFinite k
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  rw [Nat.card_congr
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL k).toEquiv]
  obtain ⟨-, hS, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linear_order (K := k) 2 (2 ^ n) hk le_rfl
  rw [hS]
  simp

theorem exists_orderOf_nine_projectiveSL {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2 ^ 3) : ∃ c : projectiveSL 2 k, orderOf c = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hScard, -⟩ :=
    CFSG.Glauberman.Dickson.h84_nonsplit_torus_data (F := k) (p := 2) (f := 3) hk
  rw [hk] at hScard
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hg9 : orderOf (g : CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup k) = 9 := by
    rw [Subgroup.orderOf_coe, hg, hScard]
    norm_num
  let e : CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup k ≃* projectiveSL 2 k :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 k).trans
      (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 2 k).symm
  exact ⟨e g, by rw [MulEquiv.orderOf_eq, hg9]⟩

section OddResidual

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem exists_two_pow_mem_of_sup_eq_top {N S : Subgroup X} [N.Normal] (hS : IsPGroup 2 S)
    (hNS : N ⊔ S = ⊤) (x : X) : ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
  have hq : (⊤ : Subgroup X).map (QuotientGroup.mk' N) ≤ S.map (QuotientGroup.mk' N) := by
    rw [← hNS, Subgroup.map_sup]
    refine sup_le ?_ le_rfl
    rw [Subgroup.map_le_iff_le_comap]
    intro n hn
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).2 hn]
    exact one_mem _
  obtain ⟨y, hy, hyx⟩ := hq ⟨x, Subgroup.mem_top x, rfl⟩
  obtain ⟨k, hk⟩ := (hS.map (QuotientGroup.mk' N)) ⟨_, ⟨y, hy, rfl⟩⟩
  refine ⟨k, (QuotientGroup.eq_one_iff _).1 ?_⟩
  have h1 := congrArg Subtype.val hk
  rw [Subgroup.coe_pow, OneMemClass.coe_one] at h1
  rw [QuotientGroup.mk_pow, ← QuotientGroup.mk'_apply, ← hyx]
  exact h1

theorem map_oddResidualPreimage_eq {D : Subgroup X} [D.Normal]
    (hRD : CFSG.Open.pCore 2 X ≤ D) {N : Subgroup X} (hN : ⁅N, N⁆ = N)
    (hNn : (N.map (QuotientGroup.mk' D)).Normal)
    (h2 : ∀ x : X, ∃ k : ℕ, QuotientGroup.mk' D x ^ 2 ^ k ∈ N.map (QuotientGroup.mk' D)) :
    (oddResidualPreimage X).map (QuotientGroup.mk' D) = N.map (QuotientGroup.mk' D) := by
  have := Subgroup.isPerfect_iff.2 hN
  apply le_antisymm
  · rw [CFSG.QuasithinUnique.Setup.oddResidualPreimage_eq, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      refine twoResidual_le_of_isTwoQuotient le_top
        (Subgroup.normalizer_eq_top_iff.mpr (hNn.comap _)).symm.le fun y _ => ?_
      obtain ⟨k, hk⟩ := h2 y
      exact ⟨k, by rw [Subgroup.mem_comap, map_pow]; exact hk⟩
    · rw [Subgroup.map_le_iff_le_comap]
      intro r hr
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff r).2 (hRD hr)]
      exact one_mem _
  · refine Subgroup.map_mono (perfect_le_twoResidual.trans ?_)
    rw [CFSG.QuasithinUnique.Setup.oddResidualPreimage_eq]
    exact le_sup_left

end OddResidual

section Star

variable {G : Type} [Group G]

theorem kerIn_subgroupOf_top_eq {H M : Subgroup G} (hMH : M ≤ H) :
    kerIn (M.subgroupOf H) ⊤ = (kerIn M H).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [map_subtype_kerIn, Subgroup.map_subgroupOf_eq_of_le hMH, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, Subgroup.map_subgroupOf_eq_of_le (kerIn_le.trans hMH)]

instance kerIn_subgroupOf_top_normal (H M : Subgroup G) :
    (kerIn (M.subgroupOf H) (⊤ : Subgroup H)).Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_kerIn _ ⊤))

theorem nonempty_mulEquiv_star {H M : Subgroup G} (hMH : M ≤ H) (K : Subgroup G) :
    Nonempty (↥((K.subgroupOf H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))) ≃*
      ↥(E2.star M H K)) := by
  have hD := kerIn_subgroupOf_top_eq hMH
  let e : ↥H ⧸ kerIn (M.subgroupOf H) ⊤ ≃* E2.StarQuot M H :=
    QuotientGroup.quotientMulEquivOfEq hD
  have hmap : ((K.subgroupOf H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))).map
      e.toMonoidHom = E2.star M H K := by
    rw [Subgroup.map_map]
    rfl
  exact ⟨((K.subgroupOf H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))).equivMapOfInjective
    e.toMonoidHom e.injective |>.trans (MulEquiv.subgroupCongr hmap)⟩

@[expose] def barIn (M H X : Subgroup G) : Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))

@[expose] noncomputable def starEquiv {H M : Subgroup G} (hMH : M ≤ H) :
    (↥H ⧸ kerIn (M.subgroupOf H) ⊤) ≃* E2.StarQuot M H :=
  QuotientGroup.quotientMulEquivOfEq (kerIn_subgroupOf_top_eq hMH)

theorem starEquiv_mk {H M : Subgroup G} (hMH : M ≤ H) (x : H) :
    starEquiv hMH (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) x) =
      QuotientGroup.mk' ((kerIn M H).subgroupOf H) x :=
  rfl

theorem map_barIn_starEquiv {H M : Subgroup G} (hMH : M ≤ H) (X : Subgroup G) :
    (barIn M H X).map (starEquiv hMH).toMonoidHom = E2.star M H X := by
  rw [barIn, Subgroup.map_map]
  rfl

end Star

section Cases

variable {G : Type} [Group G] [Finite G]

theorem map_map_conj_eq {G₁ G₂ : Type*} [Group G₁] [Group G₂] (f : G₁ →* G₂) (A : Subgroup G₁)
    (g : G₁) : (A.map (MulAut.conj g).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem pCore_le_kerIn_subgroupOf {H T M V : Subgroup G} (hyp : E2.Hyp28 H T M V) :
    CFSG.Open.pCore 2 H ≤ kerIn (M.subgroupOf H) ⊤ := by
  rw [kerIn_subgroupOf_top_eq hyp.minParabolic.maximal.1.le,
    ← CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_subgroupOf 2 H]
  exact Subgroup.comap_mono hyp.minParabolic.pCoreOf_le_kerIn

omit [Finite G] in
theorem subgroupOf_sup_eq_top {H K T : Subgroup G} (hHK : H = K ⊔ T) :
    K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (le_sup_left.trans hHK.ge),
    Subgroup.map_subgroupOf_eq_of_le (le_sup_right.trans hHK.ge), ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, ← hHK]

theorem map_oddResidualPreimage_eq_of_case2 {H T M V K : Subgroup G} (hS : Setting H T M V K)
    (h2 : Case2 H T M K) :
    (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) =
      (K.subgroupOf H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) := by
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hKn : (K.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH, hS.eq_sup]
    exact sup_le Subgroup.le_normalizer h2.1
  have hT2 : IsPGroup 2 (T.subgroupOf H) := hS.hyp.minParabolic.isSylow.2.1.comap_subtype
  refine map_oddResidualPreimage_eq (pCore_le_kerIn_subgroupOf hS.hyp)
    (perfect_of_mem_cComp (subgroupOf_mem_cComp hS.mem_cComp))
    (hKn.map _ (QuotientGroup.mk'_surjective _)) fun x => ?_
  obtain ⟨k, hk⟩ := exists_two_pow_mem_of_sup_eq_top hT2 (subgroupOf_sup_eq_top hS.eq_sup) x
  exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_map_of_mem _ hk⟩

theorem exists_paired_of_case1' (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat)
    {H T M V K : Subgroup G} (hS : Setting H T M V K) (h1 : Case1 H T M K) :
    ∃ t₀ ∈ T.subgroupOf H,
      t₀ ∉ Subgroup.normalizer ((K.subgroupOf H : Subgroup H) : Set H) ∧
      (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) =
        barIn M H K ⊔ (barIn M H K).map
          (MulAut.conj (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) t₀)).toMonoidHom ∧
      (∀ a ∈ barIn M H K, ∀ b ∈ (barIn M H K).map
          (MulAut.conj (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) t₀)).toMonoidHom,
        a * b = b * a) ∧
      barIn M H K ⊓ (barIn M H K).map
          (MulAut.conj (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) t₀)).toMonoidHom = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hMH : M ≤ H := hmp.maximal.1.le
  have hTH : T ≤ H := hmp.isSylow.1
  set R := CFSG.pCore 2 ↥H with hRdef
  set D := kerIn (M.subgroupOf H) (⊤ : Subgroup H) with hDdef
  have hRD : R = D := by
    rw [hDdef, kerIn_subgroupOf_top_eq hMH, h1.1,
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_subgroupOf]
  set bar := QuotientGroup.mk' R with hbar
  set e : (↥H ⧸ R) ≃* (↥H ⧸ D) := QuotientGroup.quotientMulEquivOfEq hRD with he
  have hebar : e.toMonoidHom.comp bar = QuotientGroup.mk' D := by
    ext x
    rfl
  have hbarsurj : Function.Surjective bar := QuotientGroup.mk'_surjective R
  have hbarker : Group.IsSolvable bar.ker := by
    rw [hbar, QuotientGroup.ker_mk']
    have : Group.IsNilpotent (CFSG.pCore 2 ↥H) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).isNilpotent
    infer_instance
  set K' := K.subgroupOf H with hK'
  have hK'c : K' ∈ cComp (⊤ : Subgroup H) := subgroupOf_mem_cComp hS.mem_cComp
  set Kb := K'.map bar with hKb
  have hKbc : Kb ∈ cComp (⊤ : Subgroup (↥H ⧸ R)) := map_mem_cComp_top bar hbarsurj hbarker hK'c
  have hYcat : CFSG.QuasithinUnique.Vol2Native.SQTKHypCat (↥H ⧸ R) := by
    have h := SQTKHyp.of_sqtkGroup ↥H hS.hyp.sqtk
    exact ⟨h.finite, CFSG.SectionRank.isStronglyQuasithin_iff.mpr h.sqt, h.kgroup, h.o2⟩
  obtain ⟨T', hT'⟩ := exists_sylow_subgroupOf hmp.isSylow
  set Tb := (T.subgroupOf H).map bar with hTb
  have hTb2 : IsPGroup 2 Tb := by
    rw [hTb, ← hT']
    exact T'.isPGroup'.map bar
  have hTbsyl : IsSylowTwoOf Tb ⊤ := by
    refine ⟨le_top, hTb2, ?_⟩
    show ¬ 2 ∣ Tb.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h := (T'.mapSurjective hbarsurj).not_dvd_index
    rwa [Sylow.coe_mapSurjective, hT'] at h
  have hKTb : Kb ⊔ Tb = ⊤ := by
    rw [hKb, hTb, ← Subgroup.map_sup, subgroupOf_sup_eq_top hS.eq_sup,
      Subgroup.map_top_of_surjective _ hbarsurj]
  obtain ⟨-, hA⟩ := h38 _ hYcat Kb hKbc
  rcases hA Tb hTbsyl with ⟨hn, -, -⟩ | ⟨tb, htb, htbN, -, -, hcomm, hdisj, hnorm, hsup⟩
  · exfalso
    obtain ⟨-, t, ht, hKt, -⟩ := h1
    apply hKt
    set t' : H := ⟨t, hTH ht⟩
    have h1 : (K'.map (MulAut.conj t').toMonoidHom).map bar = K'.map bar := by
      rw [map_map_conj_eq, ← hKb]
      exact (CFSG.Quasithin.A38.map_conj_eq_iff).2
        ((Subgroup.normalizer_eq_top_iff.mpr hn).symm ▸ Subgroup.mem_top _)
    have h2 : K'.map (MulAut.conj t').toMonoidHom = K' :=
      map_injOn_cComp_top bar hbarker (CFSG.Quasithin.A38.cComp_conj hK'c) hK'c h1
    have h3 := congrArg (Subgroup.map H.subtype) h2
    rw [map_map_conj_eq, hK', Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hS.mem_cComp)]
      at h3
    exact h3
  · obtain ⟨t₀, ht₀T, rfl⟩ := htb
    set Kb₂ := Kb.map (MulAut.conj (bar t₀)).toMonoidHom with hKb₂
    have hN : (K' ⊔ K'.map (MulAut.conj t₀).toMonoidHom).map bar = Kb ⊔ Kb₂ := by
      rw [Subgroup.map_sup, map_map_conj_eq]
    have hNT : (Kb ⊔ Kb₂) ⊔ Tb = ⊤ := hsup ▸ hKTb
    have hNn : (Kb ⊔ Kb₂).Normal := by
      refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
      rw [← hNT]
      exact sup_le Subgroup.le_normalizer hnorm
    have hperf : ⁅K' ⊔ K'.map (MulAut.conj t₀).toMonoidHom,
        K' ⊔ K'.map (MulAut.conj t₀).toMonoidHom⁆ = K' ⊔ K'.map (MulAut.conj t₀).toMonoidHom := by
      refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le ?_ ?_)
      · calc K' = ⁅K', K'⁆ := (perfect_of_mem_cComp hK'c).symm
          _ ≤ _ := Subgroup.commutator_mono le_sup_left le_sup_left
      · calc K'.map (MulAut.conj t₀).toMonoidHom
            = ⁅K'.map (MulAut.conj t₀).toMonoidHom, K'.map (MulAut.conj t₀).toMonoidHom⁆ := by
              rw [← Subgroup.map_commutator, perfect_of_mem_cComp hK'c]
          _ ≤ _ := Subgroup.commutator_mono le_sup_right le_sup_right
    have hodd : (oddResidualPreimage H).map bar = Kb ⊔ Kb₂ := by
      rw [← hN]
      refine map_oddResidualPreimage_eq (CFSG.pCore_eq_open _ _).ge hperf (hN ▸ hNn) fun x => ?_
      have := hNn
      obtain ⟨k, hk⟩ := exists_two_pow_mem_of_sup_eq_top hTb2 hNT (bar x)
      exact ⟨k, hN ▸ hk⟩
    have hK₁ : Kb.map e.toMonoidHom = barIn M H K := by
      rw [hKb, Subgroup.map_map, hebar]
      rfl
    have hK₂ : Kb₂.map e.toMonoidHom = (barIn M H K).map
        (MulAut.conj (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) t₀)).toMonoidHom := by
      rw [hKb₂, map_map_conj_eq, hK₁]
      rfl
    refine ⟨t₀, ht₀T, fun ht₀ => htbN ?_, ?_, ?_, ?_⟩
    · rw [← CFSG.Quasithin.A38.map_conj_eq_iff, hKb, ← map_map_conj_eq,
        (CFSG.Quasithin.A38.map_conj_eq_iff).2 ht₀]
    · rw [← hK₂, ← hK₁, ← hebar, ← Subgroup.map_map, hodd, Subgroup.map_sup]
    · rw [← hK₂, ← hK₁]
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hab : b * a = a * b :=
        Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) ha) b hb
      rw [← map_mul, ← map_mul, hab]
    · rw [← hK₂, ← hK₁, ← Subgroup.map_inf _ _ _ e.injective, hdisj, Subgroup.map_bot]

theorem exists_paired_of_case1 (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat)
    {H T M V K : Subgroup G} (hS : Setting H T M V K) (h1 : Case1 H T M K) :
    ∃ K₁ K₂ : Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤),
      (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) = K₁ ⊔ K₂ ∧
      (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧ K₁ ⊓ K₂ = ⊥ ∧
      Nonempty (↥K₁ ≃* ↥(E2.star M H K)) ∧ Nonempty (↥K₂ ≃* ↥(E2.star M H K)) := by
  have hMH : M ≤ H := hS.hyp.minParabolic.maximal.1.le
  obtain ⟨t₀, -, -, hK, hc, hd⟩ := exists_paired_of_case1' h38 hS h1
  obtain ⟨φ⟩ := nonempty_mulEquiv_star hMH K
  refine ⟨_, _, hK, hc, hd, ⟨φ⟩, ⟨?_⟩⟩
  exact ((barIn M H K).equivMapOfInjective _ (MulAut.conj _).injective).symm.trans φ

end Cases

end CFSG.Quasithin.Ch3E213M
