module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExc
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcToral
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaInnerCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEBundle
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicModelCoroot
public import CFSG.RankThree.PartOne.KF.F128Cyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley LayerExc LayerSixE

@[expose] def GGRootCompCenterCycInput
    (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (F : Set (Fin τ.rank → Kˣ))
    (i : KernelComponent (famChar F)) (p : ℕ), p.Prime → p ≠ 2 →
      p ∣ Nat.card (componentWeylGroup (componentRoots (famChar F) i)) →
      (∀ w ∈ componentWeylGroup (componentRoots (famChar F) i),
        ∃ γ ∈ componentRoots (famChar F) i, w • γ ≠ -γ) →
        ∀ T : Subgroup (componentRootSpan K (famChar F) i),
          T ≤ Subgroup.center (componentRootSpan K (famChar F) i) → IsPGroup p T → IsCyclic T

@[expose] def GGExcAdjLayerCycNonToralInput
    (τ : Tag) (n₀ b : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), n₀ ≤ n → Nat.card K = 2 ^ n →
    ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3)) → p < b →
      ∀ h : adjointGroup τ K, h ^ p = 1 → ¬ GGExcToral τ K (Subgroup.zpowers h) →
        GGModelLayerCyclic p (MulAut.conj h)

@[expose] def GGE6AdjLayerCycNonToralInput :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
    ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3)) →
      (p ≠ 3 ∨ ¬ 3 ∣ 2 ^ n - 1) → p < 7 →
        ∀ h : adjointGroup .E6 K, h ^ p = 1 → ¬ GGExcToral .E6 K (Subgroup.zpowers h) →
          GGModelLayerCyclic p (MulAut.conj h)

@[expose] def GGLayerCenterCyclicModelRest :
    Prop :=
  (GGRootCompCenterCycInput .G2 ∧ GGRootCompCenterCycInput .F4 ∧ GGRootCompCenterCycInput .E6 ∧
      GGRootCompCenterCycInput .E7 ∧ GGRootCompCenterCycInput .E8) ∧
    (GGExcAdjLayerCycNonToralInput .G2 2 5 ∧ GGExcAdjLayerCycNonToralInput .F4 1 5 ∧
      GGE6AdjLayerCycNonToralInput ∧ GGExcAdjLayerCycNonToralInput .E7 1 11 ∧
      GGExcAdjLayerCycNonToralInput .E8 1 11) ∧
    GGLayerInnerModelOn (fun lab => lab.tag = .triD4 ∨ lab.tag = .twF4) ∧
    GGLayerCenterCyclicExcSixRestInput

namespace LayerCycModel

theorem ggFix_conj_eq {R : Type*} [Group R] (t : R) :
    ggFix (MulAut.conj t) = Subgroup.centralizer ({t} : Set R) := by
  ext x
  rw [mem_ggFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  · intro h
    rw [← h]
    group

theorem ne_one_of_conj_ne_one {R : Type*} [Group R] {h : R} (hα : MulAut.conj h ≠ 1) : h ≠ 1 := by
  rintro rfl
  exact hα (map_one MulAut.conj)

theorem pow_eq_one_of_conj_pow {R : Type*} [Group R] (hZ : Subgroup.center R = ⊥) {h : R}
    {p : ℕ} (hαp : MulAut.conj h ^ p = 1) : h ^ p = 1 := by
  have h1 : MulAut.conj (h ^ p) = 1 := by rw [map_pow]; exact hαp
  have hz : h ^ p ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := congrArg (fun φ : MulAut R => φ g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    calc g * h ^ p = h ^ p * g * (h ^ p)⁻¹ * h ^ p := by rw [hg]
      _ = h ^ p * g := by group
  rw [hZ, Subgroup.mem_bot] at hz
  exact hz

theorem sq_ne_one_of_ne_one {K : Type*} [Field K] [CharP K 2] {a : Kˣ} (ha : a ≠ 1) :
    (a : K) ^ 2 ≠ 1 := by
  intro h
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : ((a : K) - 1) ^ 2 = 0 := by linear_combination h + (1 - (a : K)) * h2
  exact ha (Units.ext (by simpa [sub_eq_zero] using h3))

theorem pow_eq_one_of_mem_zpowers {R : Type*} [Group R] {h : R} {p : ℕ} (hh : h ^ p = 1)
    {x : R} (hx : x ∈ Subgroup.zpowers h) : x ^ p = 1 := by
  obtain ⟨k, rfl⟩ := hx
  change (h ^ k) ^ p = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hh, one_zpow]

theorem isCyclic_of_le_center_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {p : ℕ} (h : ∀ T : Subgroup A, T ≤ Subgroup.center A → IsPGroup p T → IsCyclic T)
    {T : Subgroup B} (hT : T ≤ Subgroup.center B) (hTp : IsPGroup p T) : IsCyclic T := by
  have hcen : ∀ t ∈ Subgroup.center B, e.symm t ∈ Subgroup.center A := fun t ht => by
    rw [Subgroup.mem_center_iff] at ht ⊢
    intro g
    calc g * e.symm t = e.symm (e g * t) := by rw [map_mul, e.symm_apply_apply]
      _ = e.symm (t * e g) := by rw [ht (e g)]
      _ = e.symm t * g := by rw [map_mul, e.symm_apply_apply]
  have := h (T.map e.symm.toMonoidHom) (by rintro _ ⟨t, ht, rfl⟩; exact hcen t (hT ht))
    (hTp.map _)
  exact isCyclic_of_surjective (T.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
    (MulEquiv.surjective _)

theorem isCyclic_of_subCoreFamily_pCenter {G : Type*} [Group G] {p : ℕ} {C : Subgroup G}
    {β : Type} {S : β → Subgroup G} (hS : LayerCores.IsSubCoreFamily C S)
    (hZ : ∀ c (T : Subgroup (S c)), T ≤ Subgroup.center (S c) → IsPGroup p T → IsCyclic T)
    (hcomp : IsComponentOf (LargeEvenLayer C) C) {T : Subgroup G} (hTE : T ≤ LargeEvenLayer C)
    (hTC : T ≤ Subgroup.centralizer (LargeEvenLayer C : Set G)) (hTp : IsPGroup p T) :
    IsCyclic T := by
  obtain ⟨hle, hsn, hq, ⟨k, hk⟩, -⟩ := hS
  set E := LargeEvenLayer C with hEdef
  have hEq : CFSG.IsQuasisimple E := (TableBSymp.isQuasisimple_iff _).mp hcomp.2.2
  have hSE : ∀ c, S c ≤ E := fun c =>
    le_sSup ⟨hle c, hsn c, (TableBSymp.isQuasisimple_iff _).mpr (hq c)⟩
  have hEle : E ≤ ⨆ c, S c := by
    have hEp : ⁅E, E⁆ = E := LayerCC.commutator_largeEvenLayer C
    calc E = LayerFacts.ggDer E k := (LayerFacts.ggDer_of_perfect hEp k).symm
      _ ≤ LayerFacts.ggDer C k := LayerFacts.ggDer_mono (LayerCC.largeEvenLayer_le C) k
      _ ≤ ⨆ c, S c := hk
  obtain ⟨c⟩ : Nonempty β := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have hbot : (⨆ c, S c) = ⊥ := iSup_of_empty _
    obtain ⟨x, hx1⟩ := LayerCC.exists_ne_one_of_isQuasisimple hEq
    apply hx1
    have hx : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact hEle x.2
    exact Subtype.ext (Subgroup.mem_bot.mp hx)
  have hES : E ≤ S c := by
    rcases LayerCyc.le_or_commute_of_isSubnormal
        (LayerCores.ggSubnormal_mono (hsn c) (hSE c) (LayerCC.largeEvenLayer_le C)) hEq with h | h
    · exact h
    · exfalso
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple (hq c)
      exact hab (Subtype.ext (h a ha b (hSE c hb)))
  have hTS : T ≤ S c := hTE.trans hES
  have hT₀ : T.subgroupOf (S c) ≤ Subgroup.center (S c) := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hTC ht) g (hSE c g.2)
  have e : T.subgroupOf (S c) ≃* T := Subgroup.subgroupOfEquivOfLe hTS
  have := hZ c _ hT₀ (hTp.of_equiv e.symm)
  exact isCyclic_of_surjective e e.surjective

theorem ggModelLayerCyclic_of_subCoreFamily_pCenter {p : ℕ} {H : Type} [Group H]
    {α : MulAut H}
    (h : α ≠ 1 → α ^ p = 1 → ∃ (β : Type) (S : β → Subgroup H),
      LayerCores.IsSubCoreFamily (ggFix α) S ∧
        ∀ c (T : Subgroup (S c)), T ≤ Subgroup.center (S c) → IsPGroup p T → IsCyclic T) :
    GGModelLayerCyclic p α := by
  intro hα1 hαp hcomp T hTE hTC hTp
  obtain ⟨β, S, hS, hZ⟩ := h hα1 hαp
  exact isCyclic_of_subCoreFamily_pCenter hS hZ hcomp hTE hTC hTp

end LayerCycModel

namespace LayerCycModel

section Toral


variable {τ : Tag} {K : Type} [Field K]

theorem isCyclic_of_le_center_componentRootSpan [Finite K] [CharP K 2]
    (hcyc : GGRootCompCenterCycInput τ) {F : Set (Fin τ.rank → Kˣ)}
    {i : KernelComponent (famChar F)} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {T : Subgroup (componentRootSpan K (famChar F) i)}
    (hT : T ≤ Subgroup.center (componentRootSpan K (famChar F) i)) (hTp : IsPGroup p T) :
    IsCyclic T := by
  by_cases hneg : ∃ w ∈ componentWeylGroup (componentRoots (famChar F) i),
      ∀ γ ∈ componentRoots (famChar F) i, w • γ = -γ
  · obtain ⟨w, hw, hwγ⟩ := hneg
    have hZ := LayerCycCoroot.center_eq_bot_of_neg_mem (K := K) hw hwγ
    have : Subsingleton T := ⟨fun a b => Subtype.ext (by
      have ha := hT a.2
      have hb := hT b.2
      rw [hZ, Subgroup.mem_bot] at ha hb
      rw [ha, hb])⟩
    exact isCyclic_of_subsingleton
  push Not at hneg
  by_cases hd : p ∣ Nat.card (componentWeylGroup (componentRoots (famChar F) i))
  · exact hcyc K F i p hp hp2 hd hneg T hT hTp
  · have := Fact.mk hp
    have h1 : ∀ z ∈ T, z = 1 := by
      intro z hz
      have hzW := LayerCycCoroot.pow_card_eq_one_of_mem_center (hT hz)
      have hzW' : z ^ Nat.card (componentWeylGroup (componentRoots (famChar F) i)) = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hzW)
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hTp) ⟨z, hz⟩
      rw [Subgroup.orderOf_mk] at hk
      have hdvd : p ^ k ∣ Nat.card (componentWeylGroup (componentRoots (famChar F) i)) :=
        hk ▸ orderOf_dvd_of_pow_eq_one hzW'
      rcases k with _ | k
      · rwa [pow_zero, orderOf_eq_one_iff] at hk
      · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hdvd) hd
    have : Subsingleton T := ⟨fun a b => Subtype.ext ((h1 a a.2).trans (h1 b b.2).symm)⟩
    exact isCyclic_of_subsingleton

theorem ggModelLayerCyclic_conj_of_toral [Finite K] [CharP K 2]
    (hcyc : GGRootCompCenterCycInput τ) (hWq : GGWeylFamQuotSolvInput τ) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {h : adjointGroup τ K}
    (hT : GGExcToral τ K (Subgroup.zpowers h)) : GGModelLayerCyclic p (MulAut.conj h) := by
  refine ggModelLayerCyclic_of_subCoreFamily_pCenter fun hα1 hαp => ?_
  have hh1 := ne_one_of_conj_ne_one hα1
  have hhp := pow_eq_one_of_conj_pow center_adjointGroup_eq_bot hαp
  obtain ⟨g, hg⟩ := hT
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hg h (Subgroup.mem_zpowers h))
  have hlp : l ^ p = 1 := pow_eq_one_of_coe_eq_rootDiagUnit hl
    (by rw [conj_pow, hhp, mul_one, mul_inv_cancel])
  have hl1 : l ≠ 1 := by
    rintro rfl
    apply hh1
    have h1 : g * h * g⁻¹ = 1 := Subtype.ext (by rw [hl, rootDiagUnit_one]; rfl)
    calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨j, hj⟩ : ∃ j, l j ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hl1 (funext hcon)
  have hF : ∀ b ∈ ({l} : Set (Fin τ.rank → Kˣ)), ∃ n : ℕ, b ^ p ^ n = 1 := fun b hb =>
    ⟨1, by rw [Set.mem_singleton_iff.mp hb, pow_one]; exact hlp⟩
  have hW : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup ({l} : Set (Fin τ.rank → Kˣ))) k ≤
      famReflectionGroup {l} := by
    by_cases hd : p ∣ Nat.card (famStabilizerSubgroup ({l} : Set (Fin τ.rank → Kˣ)))
    · exact hWq K p hp hp2 {l} hF hd
    · exact ⟨0, famStabilizer_subset_closure_of_coprime hp {l} hF hd⟩
  have hfam := LayerPDivExc.isSubCoreFamily_famCentralizer (K := K) {l} (sq_ne_one_of_ne_one hj) hW
  have hC : (famCentralizer ({l} : Set (Fin τ.rank → Kˣ))).comap (MulAut.conj g).toMonoidHom =
      ggFix (MulAut.conj h) := by
    rw [ggFix_conj_eq, ← LayerPDivExc.centralizer_singleton_eq_famCentralizer hl,
      ← MulAut.conj_apply, ← LayerPDivExc.map_centralizer_singleton,
      Subgroup.comap_map_eq_self_of_injective (MulAut.conj g).injective]
  have hrange : ∀ {L : Subgroup (adjointGroup τ K)}, L ≤ (MulAut.conj g).toMonoidHom.range :=
    fun {L} x _ => ⟨(MulAut.conj g).symm x, (MulAut.conj g).apply_symm_apply x⟩
  have hmap := hfam.comap (MulAut.conj g).toMonoidHom (MulAut.conj g).injective hrange
  rw [hC] at hmap
  refine ⟨_, _, hmap, fun c T hT hTp => ?_⟩
  set S := componentRootSpan K (famChar ({l} : Set (Fin τ.rank → Kˣ))) c
  have hS : S ≤ (adjointGroup τ K).subtype.range := by
    rw [Subgroup.range_subtype]
    exact rootSpan_le_adjointGroup K _
  have e₁ : S ≃* S.comap (adjointGroup τ K).subtype :=
    (((S.comap (adjointGroup τ K).subtype).equivMapOfInjective _
      (adjointGroup τ K).subtype_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hS))).symm
  have e₂ : S.comap (adjointGroup τ K).subtype ≃*
      (S.comap (adjointGroup τ K).subtype).comap (MulAut.conj g).toMonoidHom :=
    ((((S.comap (adjointGroup τ K).subtype).comap (MulAut.conj g).toMonoidHom).equivMapOfInjective
      _ (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hrange))).symm
  exact isCyclic_of_le_center_of_mulEquiv (e₁.trans e₂)
    (fun T' hT' hT'p => isCyclic_of_le_center_componentRootSpan hcyc hp hp2 hT' hT'p) hT hTp

end Toral

section Sylow


variable {τ : Tag} {K : Type} [Field K]

theorem ggExcToral_zpowers_of_not_dvd_index [Finite K] {p : ℕ} (hp : p.Prime)
    (hidx : ¬ p ∣ ((torusGroup τ K).subgroupOf (adjointGroup τ K)).index)
    {h : adjointGroup τ K} (hh : h ^ p = 1) : GGExcToral τ K (Subgroup.zpowers h) := by
  obtain ⟨g, hg⟩ := TableBExc.exists_conj_le_torusPow hp hidx (E := Subgroup.zpowers h)
    ⟨inferInstance, fun x hx => pow_eq_one_of_mem_zpowers hh hx⟩
  exact ⟨g, fun x hx => (hg (Subgroup.mem_map_of_mem _ hx)).1⟩

end Sylow

section WeylG2


theorem isSolvable_weylGroup_G2 : Group.IsSolvable (WeylGroup .G2) := by
  classical
  have : Fintype (WeylGroup .G2) := Fintype.ofFinite _
  have h : Fintype.card (WeylGroup .G2) = 12 := by
    rw [← Nat.card_eq_fintype_card]
    exact CFSG.RankThree.PartOne.K133H.card_weylGroup_G2
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 2) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) (h.trans (by norm_num))

end WeylG2

end LayerCycModel

theorem ggWeylFamQuotSolvInput_G2 :
    GGWeylFamQuotSolvInput .G2 := fun _ _ _ _ _ _ _ F _ _ =>
  LayerExc.exists_ggDer_famStabilizerSubgroup_le_of_isSolvable
    LayerCycModel.isSolvable_weylGroup_G2 F

section Restrict


theorem ggExcAdjLayerCycNonToralInput_of_input {τ : Tag} {n₀ b : ℕ}
    (h : GGExcAdjLayerCycInput τ n₀) : GGExcAdjLayerCycNonToralInput τ n₀ b :=
  fun K _ _ n hn hK p hp hp2 hs _ x _ _ => h K n hn hK p hp hp2 hs x

theorem ggE6AdjLayerCycNonToralInput_of_input (h : GGE6AdjLayerCycInput) :
    GGE6AdjLayerCycNonToralInput :=
  fun K _ _ n hn hK p hp hp2 hs hp3 _ x _ _ => h K n hn hK p hp hp2 hs hp3 x

end Restrict

section Tags

theorem ggExcAdjLayerCycInput_of_nonToral {τ : Tag} {n₀ b : ℕ} (hb : 3 < b)
    (hcyc : GGRootCompCenterCycInput τ) (hWq : GGWeylFamQuotSolvInput τ)
    (hidx : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → b ≤ p →
      p ∣ Nat.card K - 1 → ¬ p ∣ ((torusGroup τ K).subgroupOf (adjointGroup τ K)).index)
    (hnt : GGExcAdjLayerCycNonToralInput τ n₀ b) : GGExcAdjLayerCycInput τ n₀ := by
  intro K _ _ n hn hK p hp hp2 hsplit h
  have := LayerCC.charP_two_of_natCard hK
  by_cases hT : GGExcToral τ K (Subgroup.zpowers h)
  · exact LayerCycModel.ggModelLayerCyclic_conj_of_toral hcyc hWq hp hp2 hT
  · intro hα1 hαp
    have hhp := LayerCycModel.pow_eq_one_of_conj_pow center_adjointGroup_eq_bot hαp
    by_cases hpb : p < b
    · exact hnt K n hn hK p hp hp2 hsplit hpb h hhp hT hα1 hαp
    · exfalso
      refine hT (LayerCycModel.ggExcToral_zpowers_of_not_dvd_index hp
        (hidx K p hp (not_lt.mp hpb) ?_) hhp)
      rcases hsplit with h1 | ⟨-, rfl⟩
      · rwa [hK]
      · exact absurd hb hpb

theorem ggExcAdjLayerCycInput_G2_of_nonToral (hcyc : GGRootCompCenterCycInput .G2)
    (hnt : GGExcAdjLayerCycNonToralInput .G2 2 5) : GGExcAdjLayerCycInput .G2 2 :=
  ggExcAdjLayerCycInput_of_nonToral (by norm_num) hcyc ggWeylFamQuotSolvInput_G2
    (fun _ _ _ _ _ hp hp5 hpq =>
      CFSG.RankThree.Chevalley.not_dvd_index_torusGroup_G2 hp (by omega) hpq) hnt

theorem ggExcAdjLayerCycInput_F4_of_nonToral (hcyc : GGRootCompCenterCycInput .F4)
    (hnt : GGExcAdjLayerCycNonToralInput .F4 1 5) : GGExcAdjLayerCycInput .F4 1 :=
  ggExcAdjLayerCycInput_of_nonToral (by norm_num) hcyc ggWeylFamQuotSolvInput_F4
    (fun _ _ _ _ _ hp hp5 hpq => TableBF4.not_dvd_index_torusGroup hp hp5 hpq) hnt

theorem ggExcAdjLayerCycInput_E7_of_nonToral (hcyc : GGRootCompCenterCycInput .E7)
    (hWq : GGWeylFamQuotSolvInput .E7) (hnt : GGExcAdjLayerCycNonToralInput .E7 1 11) :
    GGExcAdjLayerCycInput .E7 1 :=
  ggExcAdjLayerCycInput_of_nonToral (by norm_num) hcyc hWq
    (fun _ _ _ _ _ hp hp11 hpq => TableBExc.not_dvd_index_torusGroup_E7 hp hp11 hpq) hnt

theorem ggExcAdjLayerCycInput_E8_of_nonToral (hcyc : GGRootCompCenterCycInput .E8)
    (hWq : GGWeylFamQuotSolvInput .E8) (hnt : GGExcAdjLayerCycNonToralInput .E8 1 11) :
    GGExcAdjLayerCycInput .E8 1 :=
  ggExcAdjLayerCycInput_of_nonToral (by norm_num) hcyc hWq
    (fun _ _ _ _ _ hp hp11 hpq => TableBExc.not_dvd_index_torusGroup_E8 hp hp11 hpq) hnt

theorem ggE6AdjLayerCycInput_of_nonToral (hcyc : GGRootCompCenterCycInput .E6)
    (hWq : GGWeylFamQuotSolvInput .E6) (hnt : GGE6AdjLayerCycNonToralInput) :
    GGE6AdjLayerCycInput := by
  intro K _ _ n hn hK p hp hp2 hsplit hp3 h
  have := LayerCC.charP_two_of_natCard hK
  by_cases hT : GGExcToral .E6 K (Subgroup.zpowers h)
  · exact LayerCycModel.ggModelLayerCyclic_conj_of_toral hcyc hWq hp hp2 hT
  · intro hα1 hαp
    have hhp := LayerCycModel.pow_eq_one_of_conj_pow center_adjointGroup_eq_bot hαp
    by_cases hpb : p < 7
    · exact hnt K n hn hK p hp hp2 hsplit hp3 hpb h hhp hT hα1 hαp
    · exfalso
      refine hT (LayerCycModel.ggExcToral_zpowers_of_not_dvd_index hp
        (TableBExc.not_dvd_index_torusGroup_E6 hp (not_lt.mp hpb) ?_) hhp)
      rcases hsplit with h1 | ⟨-, rfl⟩
      · rwa [hK]
      · exact absurd (by norm_num : 3 < 7) hpb

theorem ggLayerCenterCyclicExcRest_of_modelRest (hlay : GGLayerTagsPilotRestSix)
    (h : GGLayerCenterCyclicModelRest) : GGLayerCenterCyclicExcRest := by
  obtain ⟨⟨cG2, cF4, cE6, cE7, cE8⟩, ⟨nG2, nF4, nE6, nE7, nE8⟩, hTw, hSix⟩ := h
  exact ⟨ggExcAdjLayerCycInput_G2_of_nonToral cG2 nG2, ggExcAdjLayerCycInput_F4_of_nonToral cF4 nF4,
    ggExcAdjLayerCycInput_E7_of_nonToral cE7 hlay.2.1.1 nE7,
    ggExcAdjLayerCycInput_E8_of_nonToral cE8 hlay.2.2.1.1 nE8,
    ggE6AdjLayerCycInput_of_nonToral cE6 hlay.2.2.2.1.1 nE6, hTw, hSix⟩

end Tags

section Bundle

theorem ggLayerCenterCyclicExcInput_of_modelRest (hlay : GGLayerTagsPilotRestSix)
    (h : GGLayerCenterCyclicModelRest) : GGLayerCenterCyclicExcInput :=
  ggLayerCenterCyclicExcInput_of_rest (ggLayerCenterCyclicExcRest_of_modelRest hlay h)

end Bundle

end CFSG.StandardType

end
