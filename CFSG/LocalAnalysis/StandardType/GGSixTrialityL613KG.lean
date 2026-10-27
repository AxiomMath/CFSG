module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNotLongRoot
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms

namespace L613KG

section Index

variable {G : Type} [Group G]

theorem relIndex_mul_index_sup [Finite G] (A N : Subgroup G) [N.Normal] :
    A.relIndex N * (A ⊔ N).index = A.index := by
  have h1 := Subgroup.relIndex_inf_mul_relIndex A N ⊤
  rw [inf_top_eq, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h1
  have h2 := Subgroup.relIndex_mul_index (inf_le_left : A ⊓ N ≤ A)
  rw [Subgroup.inf_relIndex_left] at h2
  have h3 := Subgroup.relIndex_mul_index (le_sup_right : N ≤ A ⊔ N)
  rw [Subgroup.relIndex_sup_right] at h3
  have hpos : 0 < N.relIndex A := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have key : N.relIndex A * (A.relIndex N * (A ⊔ N).index) = N.relIndex A * A.index := by
    calc N.relIndex A * (A.relIndex N * (A ⊔ N).index)
        = A.relIndex N * (N.relIndex A * (A ⊔ N).index) := by ring
      _ = A.relIndex N * N.index := by rw [h3]
      _ = (A ⊓ N).index := h1
      _ = N.relIndex A * A.index := h2.symm
  exact Nat.eq_of_mul_eq_mul_left hpos key

theorem relIndex_dvd_relIndex_of_normal [Finite G] (H : Subgroup G) {N M : Subgroup G}
    (hNM : N ≤ M) (hMN : M ≤ Subgroup.normalizer (N : Set G)) : H.relIndex N ∣ H.relIndex M := by
  have : (N.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNM]
    intro s u hs hu
    exact (Subgroup.mem_normalizer_iff.mp (hMN hu) s).mp hs
  have h := relIndex_mul_index_sup (H.subgroupOf M) (N.subgroupOf M)
  rw [Subgroup.relIndex_subgroupOf hNM] at h
  exact Dvd.intro _ h

theorem relIndex_eq_relIndex_of_mul [Finite G] (H : Subgroup G) {N M : Subgroup G}
    (hNM : N ≤ M) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hmul : ∀ m ∈ M, ∃ n ∈ N, n⁻¹ * m ∈ H) : H.relIndex M = H.relIndex N := by
  have : (N.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNM]
    intro s u hs hu
    exact (Subgroup.mem_normalizer_iff.mp (hMN hu) s).mp hs
  have htop : H.subgroupOf M ⊔ N.subgroupOf M = ⊤ := by
    rw [eq_top_iff]
    intro m _
    obtain ⟨n, hn, hnm⟩ := hmul m m.2
    have hm : m = (⟨n, hNM hn⟩ : M) * ⟨n⁻¹ * m, M.mul_mem (M.inv_mem (hNM hn)) m.2⟩ :=
      Subtype.ext (by simp)
    rw [hm, sup_comm]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hn) (Subgroup.mem_subgroupOf.mpr hnm)
  have h := relIndex_mul_index_sup (H.subgroupOf M) (N.subgroupOf M)
  rw [Subgroup.relIndex_subgroupOf hNM, htop, Subgroup.index_top, mul_one] at h
  exact h.symm

theorem exists_sylow_le_of_not_dvd [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : ¬ p ∣ H.index) : ∃ S : Sylow p G, (S : Subgroup G) ≤ H := by
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p H))
  have hT : IsPGroup p ((T : Subgroup H).map H.subtype) := T.isPGroup'.map _
  have hidx : ¬ p ∣ ((T : Subgroup H).map H.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h1 | h1
    · exact T.not_dvd_index h1
    · exact hH h1
  exact ⟨hT.toSylow hidx, by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.map_subtype_le _⟩

theorem exists_conj_commute_of_pCentral [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    {z y : G} (hz : GGPCentralIn p M z) (hyM : y ∈ M) (hyo : orderOf y = p) :
    ∃ m ∈ M, (m⁻¹ * y * m) * z = z * (m⁻¹ * y * m) := by
  classical
  set Cz : Subgroup M := (Subgroup.centralizer {z}).subgroupOf M with hCz
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p Cz))
  have hT' : IsPGroup p ((T : Subgroup Cz).map Cz.subtype) := T.isPGroup'.map _
  have hidx : ¬ p ∣ ((T : Subgroup Cz).map Cz.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h1 | h1
    · exact T.not_dvd_index h1
    · exact hz.2 h1
  set P : Sylow p M := hT'.toSylow hidx
  have hY : IsPGroup p (Subgroup.zpowers (⟨y, hyM⟩ : M)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hyo, pow_one])
  obtain ⟨Q, hYQ⟩ := hY.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M P Q
  have hyQ : (⟨y, hyM⟩ : M) ∈ (Q : Subgroup M) := hYQ (Subgroup.mem_zpowers _)
  rw [← hm, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyQ
  obtain ⟨r, hr, hry⟩ := hyQ
  have hr' : r ∈ (T : Subgroup Cz).map Cz.subtype := hr
  obtain ⟨t, -, rfl⟩ := hr'
  have htz : ((t : M) : G) * z = z * ((t : M) : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp t.2)
  have hy : y = (m : G) * ((t : M) : G) * (m : G)⁻¹ := by
    have := congrArg Subtype.val hry
    simpa [MulAut.smul_def, MulAut.conj_apply] using this.symm
  refine ⟨m, m.2, ?_⟩
  have e : (m : G)⁻¹ * y * (m : G) = ((t : M) : G) := by rw [hy]; group
  rw [e]
  exact htz

theorem centralizer_zpowers_eq (z : G) :
    Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) =
      Subgroup.centralizer {z} := by
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h z (Subgroup.mem_zpowers z)).symm
  · rintro h _ ⟨k, rfl⟩
    exact ((Commute.zpow_right (h : Commute g z) k).eq).symm

end Index

section Transport

variable {Γ G : Type} [Group Γ] [Group G] {ι : Γ →* G}

theorem exists_mulAut_of_mem_normalizer (hinj : Function.Injective ι) {c : G}
    (hc : c ∈ Subgroup.normalizer (ι.range : Set G)) :
    ∃ β : MulAut Γ, ∀ x, ι (β x) = c * ι x * c⁻¹ := by
  obtain ⟨β, hβ⟩ := D4Rank.exists_mulAut_conj ι hinj (inv_mem hc)
  exact ⟨β, fun x => by rw [hβ, inv_inv]⟩

theorem mulAut_pow_three_eq_one (hinj : Function.Injective ι) {c : G} {β : MulAut Γ}
    (hβ : ∀ x, ι (β x) = c * ι x * c⁻¹) (hc3 : c ^ 3 = 1) : β ^ 3 = 1 := by
  refine MulEquiv.ext fun x => hinj ?_
  rw [MulAut.one_apply, pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hβ, hβ,
    hβ]
  have hc3' : c * c * c = 1 := by rwa [pow_succ, pow_succ, pow_one] at hc3
  have e : c * (c * (c * ι x * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * ι x * (c * c * c)⁻¹ := by
    group
  rw [e, hc3', one_mul, inv_one, mul_one]

theorem mulAut_apply_eq_iff (hinj : Function.Injective ι) {c : G} {β : MulAut Γ}
    (hβ : ∀ x, ι (β x) = c * ι x * c⁻¹) (x : Γ) : β x = x ↔ c * ι x = ι x * c := by
  constructor
  · intro h
    have h1 := hβ x
    rw [h] at h1
    calc c * ι x = (c * ι x * c⁻¹) * c := by group
      _ = ι x * c := by rw [← h1]
  · intro h
    apply hinj
    rw [hβ, h, mul_inv_cancel_right]

theorem mem_range_of_mulAut_mem_inner (hC : Subgroup.centralizer (ι.range : Set G) = ⊥) {c : G}
    {β : MulAut Γ} (hβ : ∀ x, ι (β x) = c * ι x * c⁻¹) (hin : β ∈ inner Γ) : c ∈ ι.range := by
  obtain ⟨γ, hγ⟩ := hin
  have hcen : (ι γ)⁻¹ * c ∈ Subgroup.centralizer (ι.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    have h1 := hβ x
    rw [← hγ, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
    calc ι x * ((ι γ)⁻¹ * c) = (ι γ)⁻¹ * (ι γ * ι x * (ι γ)⁻¹) * c := by group
      _ = (ι γ)⁻¹ * (c * ι x * c⁻¹) * c := by rw [h1]
      _ = (ι γ)⁻¹ * c * ι x := by group
  rw [hC, Subgroup.mem_bot] at hcen
  refine ⟨γ, ?_⟩
  calc ι γ = ι γ * ((ι γ)⁻¹ * c) := by rw [hcen, mul_one]
    _ = c := by group

theorem mulAut_mem_inner_of_mem_range (hinj : Function.Injective ι) {c : G} {β : MulAut Γ}
    (hβ : ∀ x, ι (β x) = c * ι x * c⁻¹) (hc : c ∈ ι.range) : β ∈ inner Γ := by
  obtain ⟨γ, rfl⟩ := hc
  refine ⟨γ, MulEquiv.ext fun x => hinj ?_⟩
  rw [MulAut.conj_apply, hβ, map_mul, map_mul, map_inv]

theorem comap_centralizer_eq (hinj : Function.Injective ι) (x : Γ) :
    (Subgroup.centralizer {ι x}).comap ι = Subgroup.centralizer {x} := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  exact hinj.eq_iff

theorem index_centralizer_eq (hinj : Function.Injective ι) (x : Γ) :
    (Subgroup.centralizer {x}).index = (Subgroup.centralizer {ι x}).relIndex ι.range := by
  rw [← Subgroup.index_comap, comap_centralizer_eq hinj]

theorem exists_sylow_fixed [Finite Γ] {p : ℕ} [Fact p.Prime] (hinj : Function.Injective ι)
    {c : G} {β : MulAut Γ} (hβ : ∀ x, ι (β x) = c * ι x * c⁻¹)
    (hidx : ¬ p ∣ (Subgroup.centralizer {c}).relIndex ι.range) :
    ∃ S : Sylow p Γ, ∀ s ∈ (S : Subgroup Γ), β s = s := by
  have h1 : ¬ p ∣ ((Subgroup.centralizer {c}).comap ι).index := by rwa [Subgroup.index_comap]
  obtain ⟨S, hS⟩ := exists_sylow_le_of_not_dvd h1
  refine ⟨S, fun s hs => (mulAut_apply_eq_iff hinj hβ s).mpr ?_⟩
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hS hs)).symm

theorem commutator_comap_eq (hinj : Function.Injective ι) {Y : Subgroup G} (hY : Y ≤ ι.range)
    (hYp : ⁅Y, Y⁆ = Y) : ⁅Y.comap ι, Y.comap ι⁆ = Y.comap ι := by
  apply Subgroup.map_injective hinj
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hY, hYp]

noncomputable def comapEquiv (hinj : Function.Injective ι) {Y : Subgroup G} (hY : Y ≤ ι.range) :
    ↥(Y.comap ι) ≃* ↥Y :=
  ((Y.comap ι).equivMapOfInjective ι hinj).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hY))

end Transport

section Layer

variable {G : Type} [Group G]

theorem largeEvenLayer_le_of_normal {N H : Subgroup G} (hNH : N ≤ H)
    (hn : ∀ u ∈ H, ∀ s ∈ N, u * s * u⁻¹ ∈ N) : LargeEvenLayer N ≤ LargeEvenLayer H := by
  refine sSup_le fun K hK => le_sSup ?_
  obtain ⟨hKN, hsub, hq⟩ := hK
  exact ⟨hKN.trans hNH,
    LayerCores.ggSubnormal_trans hsub (LayerCores.ggSubnormal_of_normal hNH hn), hq⟩

noncomputable def centerQuotEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (Subgroup.map_center_eq e)

theorem card_eq_of_lieModel_psl3 {H : Type} [Group H] {f : ℕ} (hH : LieModel H .PSL 3 2 f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) :
    Nat.card H = Nat.card (StatedProj (StatedSL 3 K)) := by
  rcases hH with ⟨-, -, K', _, _, hK', ⟨e⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num),
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK', hK]
  all_goals exact absurd h (by norm_num)

theorem perfect_le_of_mulEquiv_om8 [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {G₀ : Subgroup G} (e : Om8 K ≃* G₀)
    (hC : Subgroup.centralizer (G₀ : Set G) = ⊥) {X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (G₀ : Set G)) (hX : ⁅X, X⁆ = X) : X ≤ G₀ := by
  have hOut : Group.IsSolvable (Outer ↥G₀) :=
    CFSG.SeitzReduction.OmegaPilot.isSolvable_outer_of_mulEquiv_plus (le_refl 4) hf hK
      (e.symm.trans projEquiv8)
  have hCs : Group.IsSolvable
      (Subgroup.centralizer (G₀ : Set G) ⊓ Subgroup.normalizer (G₀ : Set G) : Subgroup G) := by
    rw [hC, bot_inf_eq]
    infer_instance
  exact CFSG.SeitzReduction.perfect_le_of_isSolvable_outer hOut Subgroup.le_normalizer le_rfl hCs
    hX hXN

end Layer

section Embed

variable {G : Type} [Group G]

theorem exists_om8_embedding {G₀ : Subgroup G} {f : ℕ} {ψ : (ggU .POmegaPlus 4 f).K →* G}
    (hpres : GGPresentsG0 G₀ (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ) :
    ∃ ι : Om8 (GaloisField 2 f) →* G, Function.Injective ι ∧ ι.range = G₀ ∧
      ∀ u : Sp8 (GaloisField 2 f), ι (model8 u) = ψ u := by
  have hcen := RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo
    (K := GaloisField 2 f) (n := 4) (by norm_num)
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hpres.2.1.2.trans hcen.le
  refine ⟨(ψ : Sp8 (GaloisField 2 f) →* G).comp
    (modelEquiv8 (K := GaloisField 2 f)).symm.toMonoidHom,
    hψinj.comp (modelEquiv8 (K := GaloisField 2 f)).symm.injective, ?_, fun u => ?_⟩
  · rw [← hpres.2.1.1]
    ext g
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨modelEquiv8 u, ?_⟩
      exact congrArg ψ (MulEquiv.symm_apply_apply (modelEquiv8 (K := GaloisField 2 f)) u)
  · exact congrArg ψ (MulEquiv.symm_apply_apply (modelEquiv8 (K := GaloisField 2 f)) u)

end Embed

end L613KG

section Main

open L613KG

theorem ggD4TrialityCentralInput_of_om8 (h1 : GGD4OuterSylowInput)
    (h2 : GGD4SemilinearLayerInput) (h3 : GGD4CentralClassThreeInput)
    (h4 : GGD4ClassThreeLayerInput) : GGD4TrialityCentralInput := by
  intro G _ _ G₀ t n f ψ hpres hC y hyM hyo htri z hzo hzc
  obtain ⟨rfl, rfl, -, h3f, hni, hlie⟩ := htri
  have hf1 : 1 ≤ f := hpres.1.1.2.1
  have hKc : Nat.card (GaloisField 2 f) = 2 ^ f := by
    exact GaloisField.card 2 f (by omega)
  have hK3 : 3 ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hKc]; exact h3f
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ι, hinj, hrange, hιψ⟩ := exists_om8_embedding hpres
  set M := Subgroup.normalizer (G₀ : Set G) with hM
  have hCι : Subgroup.centralizer (ι.range : Set G) = ⊥ := by rw [hrange]; exact hC
  have hNι : ∀ c ∈ M, c ∈ Subgroup.normalizer (ι.range : Set G) := fun c hc => by
    rw [hrange]; exact hc
  obtain ⟨m, hmM, hcomm⟩ := exists_conj_commute_of_pCentral hzc hyM hyo
  have hG₀idx : ¬ 3 ∣ (Subgroup.centralizer {z}).relIndex G₀ := fun h =>
    hzc.2 (h.trans (relIndex_dvd_relIndex_of_normal _ Subgroup.le_normalizer le_rfl))
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hzG₀ : z ∈ G₀ := by
    obtain ⟨β, hβ⟩ := exists_mulAut_of_mem_normalizer hinj (hNι z hzc.1)
    obtain ⟨S, hS⟩ := exists_sylow_fixed (p := 3) hinj hβ (by rw [hrange]; exact hG₀idx)
    have hin := h1 _ hK3 β (mulAut_pow_three_eq_one hinj hβ hz3) S hS
    rw [← hrange]
    exact mem_range_of_mulAut_mem_inner hCι hβ hin
  obtain ⟨zb, rfl⟩ : z ∈ ι.range := by rw [hrange]; exact hzG₀
  have hzb3 : zb ^ 3 = 1 := hinj (by rw [map_pow, hz3, map_one])
  have hzb1 : zb ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  have hzbidx : ¬ 3 ∣ (Subgroup.centralizer {zb}).index := by
    rw [index_centralizer_eq hinj, hrange]
    exact hG₀idx
  set y₁ := m⁻¹ * y * m with hy₁
  have hy₁M : y₁ ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hmM) hyM) hmM
  have hy₁3 : y₁ ^ 3 = 1 := by
    have hy3 : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
    have e : y₁ ^ 3 = m⁻¹ * y ^ 3 * m := by
      rw [hy₁, pow_succ, pow_succ, pow_one, pow_succ, pow_succ, pow_one]
      group
    rw [e, hy3, mul_one, inv_mul_cancel]
  obtain ⟨β, hβ⟩ := exists_mulAut_of_mem_normalizer hinj (hNι y₁ hy₁M)
  have hβ3 : β ^ 3 = 1 := mulAut_pow_three_eq_one hinj hβ hy₁3
  have hβz : β zb = zb := (mulAut_apply_eq_iff hinj hβ zb).mpr hcomm
  have hβout :
      β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (Om8 (GaloisField 2 f)) := by
    intro hin
    have hy₁G₀ : y₁ ∈ G₀ := by
      rw [← hrange]
      exact mem_range_of_mulAut_mem_inner hCι hβ hin
    have hyG₀ : y ∈ G₀ := by
      have h := (Subgroup.mem_normalizer_iff.mp hmM y₁).mp hy₁G₀
      rwa [hy₁, show m * (m⁻¹ * y * m) * m⁻¹ = y by group] at h
    exact hni (ggPsiInnerDiag_of_mem_range _ (by rw [hpres.2.1.1]; exact hyG₀))
  have hβns : ∀ g : similarityPairs (coordinateQuadPlus 4 (GaloisField 2 f)), conjAct _ g ≠ β := by
    intro g hg
    set Ly := LargeEvenLayer (G₀ ⊓ Subgroup.centralizer {y}) with hLy
    set Y := Ly.map (MulAut.conj m⁻¹).toMonoidHom with hY
    have hLyle : Ly ≤ G₀ ⊓ Subgroup.centralizer {y} := LayerCC.largeEvenLayer_le _
    have hYG₀ : Y ≤ ι.range := by
      rw [hrange]
      rintro _ ⟨l, hl, rfl⟩
      have h := (Subgroup.mem_normalizer_iff.mp (M.inv_mem hmM) l).mp (hLyle hl).1
      simpa [MulAut.conj_apply] using h
    have hYp : ⁅Y, Y⁆ = Y := by
      rw [hY, ← Subgroup.map_commutator, LayerCC.commutator_largeEvenLayer]
    have hfix : ∀ x ∈ Y.comap ι, β x = x := by
      intro x hx
      rw [mulAut_apply_eq_iff hinj hβ]
      obtain ⟨l, hl, hlx⟩ := (Subgroup.mem_comap.mp hx : ι x ∈ Y)
      have hly : l * y = y * l := Subgroup.mem_centralizer_singleton_iff.mp (hLyle hl).2
      rw [← hlx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hy₁]
      calc m⁻¹ * y * m * (m⁻¹ * l * m) = m⁻¹ * (y * l) * m := by group
        _ = m⁻¹ * (l * y) * m := by rw [hly]
        _ = m⁻¹ * l * m * (m⁻¹ * y * m) := by group
    have eY : ↥(Y.comap ι) ≃* ↥Ly :=
      (comapEquiv hinj hYG₀).trans (Ly.equivMapOfInjective _ (MulAut.conj m⁻¹).injective).symm
    exact h2 _ f hKc β hβ3 hβout ⟨g, hg⟩ (Y.comap ι) hfix (commutator_comap_eq hinj hYG₀ hYp)
      (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (centerQuotEquiv eY).symm hlie)
  have hd2 := h3 _ hK3 zb hzb3 hzb1 hzbidx β hβ3 hβns hβz
  obtain ⟨Sb, hSp, hzS, hSC, hSmax, hScard⟩ := h4 _ hK3 zb hzb3 hd2
  set S := Sb.map ι with hS
  have hSG₀ : S ≤ G₀ ⊓ Subgroup.centralizer {ι zb} := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨by rw [← hrange]; exact ⟨s, rfl⟩, ?_⟩
    change ι s ∈ Subgroup.centralizer {ι zb}
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hSC hs)]
  have hSperf : ⁅S, S⁆ = S := by rw [hS, ← Subgroup.map_commutator, hSp]
  have hSmax' : ∀ X : Subgroup G, X ≤ G₀ ⊓ Subgroup.centralizer {ι zb} → ⁅X, X⁆ = X →
      X ≤ S := by
    intro X hX hXp
    have hXι : X ≤ ι.range := by rw [hrange]; exact hX.trans inf_le_left
    have hXc : X.comap ι ≤ Subgroup.centralizer {zb} := by
      rw [← comap_centralizer_eq hinj]
      exact Subgroup.comap_mono (hX.trans inf_le_right)
    have h := Subgroup.map_mono (f := ι) (hSmax _ hXc (commutator_comap_eq hinj hXι hXp))
    rwa [Subgroup.map_comap_eq_self hXι] at h
  have hperfM : ∀ X : Subgroup G, X ≤ M → ⁅X, X⁆ = X → X ≤ G₀ := fun X hXM hXp =>
    perfect_le_of_mulEquiv_om8 hf1 hKc
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)) hC hXM hXp
  have hodd : Odd (Nat.card (Subgroup.centralizer (G₀ : Set G))) := by
    rw [hC, Subgroup.card_bot]
    exact odd_one
  have hzzG₀ : Subgroup.zpowers (ι zb) ≤ G₀ := by
    rw [Subgroup.zpowers_le]
    exact hzG₀
  have hlayer : ∀ X : Subgroup G, X ≤ G₀ ⊓ Subgroup.centralizer {ι zb} → ⁅X, X⁆ = X →
      X ≤ LargeEvenLayer (G₀ ⊓ Subgroup.centralizer {ι zb}) := by
    intro X hX hXp
    have h := ggLayerTags_POmegaPlus.2 G 4 f ψ G₀ hpres hodd 3 Nat.prime_three (by norm_num)
      (Subgroup.zpowers (ι zb))
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one]))
      (by
        rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
        exact zpow_mul_comm _ i j)
      (hzzG₀.trans Subgroup.le_normalizer)
      (fun e he => ggPsiInnerDiag_of_mem_range _ (by rw [hpres.2.1.1]; exact hzzG₀ he))
      X (by rwa [centralizer_zpowers_eq])
      hXp
    rwa [centralizer_zpowers_eq] at h
  have hnormal : ∀ u ∈ M ⊓ Subgroup.centralizer {ι zb},
      ∀ s ∈ G₀ ⊓ Subgroup.centralizer {ι zb}, u * s * u⁻¹ ∈ G₀ ⊓ Subgroup.centralizer {ι zb} :=
    fun u hu s hs => ⟨(Subgroup.mem_normalizer_iff.mp hu.1 s).mp hs.1,
      (Subgroup.centralizer {ι zb}).mul_mem ((Subgroup.centralizer {ι zb}).mul_mem hu.2 hs.2)
        ((Subgroup.centralizer {ι zb}).inv_mem hu.2)⟩
  have hLE := largeEvenLayer_le_of_normal (inf_le_inf_right _ Subgroup.le_normalizer) hnormal
  have hLM : LargeEvenLayer (M ⊓ Subgroup.centralizer {ι zb}) ≤ S := by
    have hle := LayerCC.largeEvenLayer_le (M ⊓ Subgroup.centralizer {ι zb})
    have hp := LayerCC.commutator_largeEvenLayer (M ⊓ Subgroup.centralizer {ι zb})
    exact hSmax' _ (le_inf (hperfM _ (hle.trans inf_le_left) hp) (hle.trans inf_le_right)) hp
  refine ⟨hLE (hlayer S hSG₀ hSperf ⟨zb, hzS, rfl⟩), fun X hX hXp => (hlayer X
    (le_inf (hperfM X (hX.trans inf_le_left) hXp) (hX.trans inf_le_right)) hXp).trans hLE,
    fun H _ hH => ?_⟩
  rw [card_eq_of_lieModel_psl3 hH hKc]
  calc Nat.card (LargeEvenLayer (M ⊓ Subgroup.centralizer {ι zb}))
      ≤ Nat.card S := Subgroup.card_le_of_le hLM
    _ = Nat.card Sb := Subgroup.card_map_of_injective hinj
    _ ≤ 3 * Nat.card (StatedProj (StatedSL 3 (GaloisField 2 f))) := hScard

theorem ggSixTrialityDCentralInput_of_om8 (ha : GGSixTrialityDClassThreeInput)
    (hb : GGD4ClassThreeCentralInput) : GGSixTrialityDCentralInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hC y hy hyo htri
  have htri' := htri
  obtain ⟨rfl, rfl, rfl, h3f, -, -⟩ := htri
  obtain ⟨d, hdD, hd1, u, hu, hdu⟩ := ha G B Bs x L D J f ψ hctx hC y hy hyo htri'
  have hpres := hctx.presents
  have hf1 : 1 ≤ f := hpres.1.1.2.1
  have hKc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK3 : 3 ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hKc]; exact h3f
  obtain ⟨ι, hinj, hrange, hιψ⟩ := exists_om8_embedding hpres
  have hιzb : ι (model8 u) = d := by rw [hιψ, hu]
  have hd3 : d ^ 3 = 1 := hctx.d_elem.2 d hdD
  have hzb3 : (model8 u) ^ 3 = 1 := hinj (by rw [map_pow, hιzb, hd3, map_one])
  obtain ⟨hidx, hAut⟩ := hb _ hK3 (model8 u) hzb3 hdu
  have hdG₀ : d ∈ ggG0 3 B x L D J := by rw [← hιzb, ← hrange]; exact ⟨model8 u, rfl⟩
  refine ⟨d, hdD, hd1, Subgroup.le_normalizer hdG₀, ?_⟩
  have hmul : ∀ m ∈ ggM 3 B x L D J, ∃ g ∈ ggG0 3 B x L D J,
      g⁻¹ * m ∈ Subgroup.centralizer {d} := by
    intro m hm
    obtain ⟨β, hβ⟩ := exists_mulAut_of_mem_normalizer hinj
      (show m ∈ Subgroup.normalizer (ι.range : Set G) by rw [hrange]; exact hm)
    obtain ⟨g, hg⟩ := hAut β
    refine ⟨ι g, by rw [← hrange]; exact ⟨g, rfl⟩, ?_⟩
    have h1 := hβ (model8 u)
    rw [hg, map_mul, map_mul, map_inv, hιzb] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (ι g)⁻¹ * m * d = (ι g)⁻¹ * (m * d * m⁻¹) * m := by group
      _ = (ι g)⁻¹ * (ι g * d * (ι g)⁻¹) * m := by rw [h1]
      _ = d * ((ι g)⁻¹ * m) := by group
  rw [relIndex_eq_relIndex_of_mul _ Subgroup.le_normalizer le_rfl hmul, ← hrange, ← hιzb,
    ← index_centralizer_eq hinj]
  exact hidx

theorem ggSixTrialityInput_of_om8 (h611 : GGSixLSixElevenInput) (h1 : GGD4OuterSylowInput)
    (h2 : GGD4SemilinearLayerInput) (h3 : GGD4CentralClassThreeInput)
    (h4 : GGD4ClassThreeLayerInput) (h5 : GGD4ClassThreeCentralInput)
    (h6 : GGSixTrialityDClassThreeInput) : GGSixTrialityInput :=
  ggSixTrialityInput_of_lSixEleven_central h611 (ggD4TrialityCentralInput_of_om8 h1 h2 h3 h4)
    (ggSixTrialityDCentralInput_of_om8 h6 h5)

end Main

end CFSG.StandardType
