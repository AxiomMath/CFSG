module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankSix
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotInnerAction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotOuterFusion
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectW
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace TwE6Rank

section ElemAbelian

variable {G H : Type*} [Group G] [Group H] {p : ℕ}

theorem isElemAbelian_comap {f : G →* H} (hf : Function.Injective f) {A : Subgroup H}
    (hA : IsElemAbelian p A) : IsElemAbelian p (A.comap f) := CFSG.Open.IsElemAbelian.comap hA hf

theorem isElemAbelian_map (f : G →* H) {A : Subgroup G} (hA : IsElemAbelian p A) :
    IsElemAbelian p (A.map f) := CFSG.SectionRank.isElemAbelian_map hA _

end ElemAbelian

theorem orderOf_natCast_eq_two {q p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1) :
    orderOf ((q : ℕ) : ZMod p) = 2 := by
  have hx : ((q : ℕ) : ZMod p) = -1 := by
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    exact hpq
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  rw [hx, orderOf_neg_one, ZMod.ringChar_zmod_n]
  simp [hp2]

theorem card_le_four_E6
    {k : Type} [Field k] [Finite k] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card k + 1) {B : Subgroup (adjointGroup Tag.E6 k)} (hB : IsElemAbelian p B) :
    Nat.card B ≤ p ^ 4 := by
  have h5 := CFSG.LieType.SeitzGeneration.five_le_of_three_lt hp hp3
  have he := orderOf_natCast_eq_two hp (by omega) hpq
  have hpk : ¬ p ∣ Nat.card k := fun h => by
    have h1 : p ∣ 1 := (Nat.dvd_add_right h).1 hpq
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hST := CFSG.HardMathSupport.Timmesfeld.CrossChar.sylowTorus_of_blocks_of_three_lt 3
    (Or.inl ⟨rfl, rfl⟩) k hp hp3 hpk
    (CFSG.RankThree.PartOne.KE.IsWeylMatrix.of_word Tag.E6
      CFSG.LieType.SeitzGeneration.e6TwoWord)
    [1, 1, 2, 2, 2, 2] CFSG.LieType.SeitzGeneration.e6Two_charpoly
    CFSG.LieType.SeitzGeneration.e6Two_pow he
    (fun d hd hd2 => by
      have h1 : d = 1 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        omega
      rw [h1]
      exact hp.not_dvd_one)
    (fun d hd h2 => CFSG.LieType.SeitzGeneration.not_dvd_small hp h5
      ((by decide : ∀ d ∈ CFSG.LieType.SeitzGeneration.degreesE Tag.E6, 2 ∣ d →
        d / 2 ∈ [1, 2, 3, 4, 6]) d hd h2))
    (by decide)
  have h4 : [1, 1, 2, 2, 2, 2].count 2 = 4 := by decide
  rw [h4] at hST
  exact hST.rank_le hp ⟨hB.1, hB.2⟩

theorem exists_subfield_card {n : ℕ} {K : Type} [Field K] (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) : ∃ S : Subfield K, Nat.card S = 2 ^ n := by
  obtain ⟨φ, -, hord, -, -, hsub⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * n) (by rw [hK, ← pow_mul, mul_comm])
  have hA : Nat.card (Subgroup.zpowers (φ ^ n)) = 2 := by
    rw [Nat.card_zpowers, orderOf_pow' φ (by omega : n ≠ 0), hord, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel 2 (by omega : 0 < n)]
  obtain ⟨-, S, -, hS⟩ := hsub (Subgroup.zpowers (φ ^ n))
  exact ⟨S, by rw [hS, hA, Nat.mul_div_cancel_left n two_pos]⟩

section Outer


open CFSG.SeitzReduction.TwistedE6Pilot in
theorem card_le_four_of_outer {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ 2 ^ f + 1)
    {α : MulAut (graphFixedRootGroup TwistTag.E6 K σ)} (hα : α ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ →*
      MulAut (graphFixedRootGroup TwistTag.E6 K σ)).range)
    {A : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)} (hA : IsElemAbelian p A)
    (hfix : ∀ a ∈ A, α a = a) : Nat.card A ≤ p ^ 4 := by
  have : Finite K := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨S, hS⟩ := exists_subfield_card hf hK
  set hσσ := apply_apply_eq hK hσ
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
      φ * α * φ⁻¹ = etaAut σ hσσ ∨ φ * α * φ⁻¹ = xiAut σ hσσ := by
    rcases (conj_etaAut_or_xiAut_of_outer hf hK σ hσ).1 α hα hαo with ⟨φ, h⟩ | ⟨φ, h⟩
    · exact ⟨φ, Or.inl h⟩
    · exact ⟨φ, Or.inr h⟩
  have hJ : ∀ g : graphFixedRootGroup TwistTag.E6 K σ, (φ * α * φ⁻¹) g = g →
      (g : ModGL TwistTag.E6.tag K) ∈
        (twistedFixedGroup TwistTag.E6 S (RingHom.id S)).map (baseChangeGL (algebraMap S K)) := by
    intro g hg
    have hη : g ∈ (etaAut σ hσσ).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)) := by
      rcases hφ with h | h
      · rw [h] at hg
        exact hg
      · rw [h] at hg
        exact eqLocus_xiAut_le_etaAut hf hS hK σ hσ hg
    rw [eqLocus_etaAut_eq hf hS hK σ hσ, Subgroup.mem_subgroupOf] at hη
    exact hη
  have hfix' : ∀ a ∈ A, (φ * α * φ⁻¹) (φ a) = φ a := fun a ha => by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfix a ha]
  set ι : adjointGroup TwistTag.E6.tag S →* ModGL TwistTag.E6.tag K :=
    (baseChangeGL (algebraMap S K)).comp (adjointGroup TwistTag.E6.tag S).subtype with hιdef
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  set A'' : Subgroup (ModGL TwistTag.E6.tag K) :=
    (A.map φ.toMonoidHom).map (graphFixedRootGroup TwistTag.E6 K σ).subtype with hA''
  have hle : A'' ≤ (A''.comap ι).map ι := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨g, hg, hge⟩ := hJ (φ a) (hfix' a ha)
    exact ⟨⟨g, hg.1⟩, by
      change ι ⟨g, hg.1⟩ ∈ A''
      rw [show ι ⟨g, hg.1⟩ = _ from hge]
      exact ⟨φ a, ⟨a, ha, rfl⟩, rfl⟩, hge⟩
  have hB : IsElemAbelian p (A''.comap ι) :=
    isElemAbelian_comap hι (isElemAbelian_map _ (isElemAbelian_map _ hA))
  have hpS : p ∣ Nat.card S + 1 := by rw [hS]; exact hpq
  calc Nat.card A = Nat.card (A.map φ.toMonoidHom) :=
        (Subgroup.card_map_of_injective φ.injective).symm
    _ = Nat.card A'' := (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
    _ ≤ Nat.card ((A''.comap ι).map ι) := Subgroup.card_le_of_le hle
    _ = Nat.card (A''.comap ι) := Subgroup.card_map_of_injective hι
    _ ≤ p ^ 4 := card_le_four_E6 hp hp3 hpS hB

end Outer

section Recipe


variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_mulEquiv_graphFixedRootGroup (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    Nonempty (TwE6Delta.RecipeR K n ≃* graphFixedRootGroup TwistTag.E6 K σ) := by
  obtain ⟨-, T, -, -⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) n σ hσ
  have hZ := TwE6Delta.center_recipeH_eq_bot hn hK
  have hC := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ hσ).2.2.1
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
    (T.symm.trans (MulEquiv.subgroupCongr hC))⟩

theorem card_le_four_of_outer_recipeR (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ 2 ^ n + 1) {u : MulAut (TwE6Delta.RecipeR K n)}
    (hu : u ^ 2 = 1)
    (huo : u ∉ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range)
    {A : Subgroup (TwE6Delta.RecipeR K n)} (hA : IsElemAbelian p A) (hfix : ∀ a ∈ A, u a = a) :
    Nat.card A ≤ p ^ 4 := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  obtain ⟨e⟩ := exists_mulEquiv_graphFixedRootGroup hn hK _ (iterateFrobenius_def 2 n)
  set α : MulAut (graphFixedRootGroup TwistTag.E6 K (iterateFrobenius K 2 n)) :=
    (e.symm.trans u).trans e with hαdef
  have hαx : ∀ x, α x = e (u (e.symm x)) := fun x => rfl
  have hα : α ^ 2 = 1 := by
    refine MulEquiv.ext fun x => ?_
    have h := congrArg (fun φ : MulAut (TwE6Delta.RecipeR K n) => φ (e.symm x)) hu
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply] at h ⊢
    rw [hαx, hαx, MulEquiv.symm_apply_apply, h, MulEquiv.apply_symm_apply]
  have hαo : α ∉ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K (iterateFrobenius K 2 n) →*
      MulAut (graphFixedRootGroup TwistTag.E6 K (iterateFrobenius K 2 n))).range := by
    rintro ⟨c, hc⟩
    apply huo
    refine ⟨e.symm c, MulEquiv.ext fun x => e.injective ?_⟩
    have h := congrArg (fun φ : MulAut _ => φ (e x)) hc
    simp only [MulAut.conj_apply] at h
    rw [hαx, MulEquiv.symm_apply_apply] at h
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  refine card_le_four_of_outer hn hK _ (iterateFrobenius_def 2 n) hp hp3 hpq hα hαo
    (isElemAbelian_map _ hA) ?_
  rintro _ ⟨a, ha, rfl⟩
  change α (e a) = e a
  rw [hαx, MulEquiv.symm_apply_apply, hfix a ha]

end Recipe

end TwE6Rank

@[expose] def GGTwE6EndNodeInnerInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → p ≠ 3 → ∀ A : Subgroup (TwE6Delta.RecipeR K n), IsElemAbelian p A →
      p ^ 5 ≤ Nat.card A →
      (∃ U : Subgroup (TwE6Delta.RecipeR K n), U ≠ ⊥ ∧ IsPGroup 2 U ∧
        A ≤ Subgroup.normalizer (U : Set (TwE6Delta.RecipeR K n))) →
      ∃ t ∈ A, t ≠ 1 ∧
        IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({t} : Set (TwE6Delta.RecipeR K n))))
          (Subgroup.centralizer ({t} : Set (TwE6Delta.RecipeR K n))) ∧
        ∀ s ∈ A, (∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set (TwE6Delta.RecipeR K n))),
          s * j = j * s) → s ∈ Subgroup.zpowers t

theorem ggTwE6EndNodeInput_of_inner
    (h : GGTwE6EndNodeInnerInput) : GGTwE6EndNodeInput := by
  intro K _ _ n p hn hK hp hpn hp3
  rw [TwE6Delta.liftRank_of_ne hp3]
  intro A hA h5 _ hU
  obtain ⟨U, hU1, hU2, hUN⟩ := hU
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  have hp3' : 3 < p := by
    have := hp.two_le
    omega
  have := TwE6Delta.finite_recipeR hK
  have := TwE6Delta.finite_mulAut_recipeR hK
  have hinj := mulAut_conj_injective_of_center_eq_bot (TwE6Delta.center_recipeR_eq_bot hn hK)
  have hAN : ∀ a ∈ A, MulAut.conj a ∈
      Subgroup.normalizer (U : Set (MulAut (TwE6Delta.RecipeR K n))) :=
    fun a ha => hUN ⟨a, ha, rfl⟩
  by_cases hinn : ∃ u ∈ U, u ≠ 1 ∧
      u ∈ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range
  ·
    obtain ⟨u, huU, hu1, y, rfl⟩ := hinn
    have hU₀ : U.comap MulAut.conj ≠ ⊥ := by
      intro hbot
      have hy : y ∈ U.comap MulAut.conj := huU
      rw [hbot, Subgroup.mem_bot] at hy
      exact hu1 (by rw [hy, map_one])
    have hU₀N : A ≤ Subgroup.normalizer ((U.comap MulAut.conj : Subgroup _) :
        Set (TwE6Delta.RecipeR K n)) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hx := Subgroup.mem_normalizer_iff.1 (hAN a ha) (MulAut.conj x)
      change MulAut.conj x ∈ U ↔ MulAut.conj (a * x * a⁻¹) ∈ U
      rw [map_mul, map_mul, map_inv]
      exact hx
    obtain ⟨t, htA, ht1, hcomp, hcent⟩ := h K n p hn hK hp hpn hp3 A hA h5
      ⟨_, hU₀, hU2.comap_of_injective _ hinj, hU₀N⟩
    refine ⟨t, htA, ht1, hcomp, fun s hs => ⟨hcent s hs, fun hst j hj => ?_⟩⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hst
    have hle : LargeEvenLayer (Subgroup.centralizer ({t} : Set (TwE6Delta.RecipeR K n))) ≤
        Subgroup.centralizer ({t} : Set (TwE6Delta.RecipeR K n)) := by
      unfold LargeEvenLayer
      exact sSup_le fun L hL => hL.1
    have hjt : t * j = j * t := Subgroup.mem_centralizer_iff.1 (hle hj) t (Set.mem_singleton t)
    exact (Commute.zpow_left hjt k).eq
  ·
    exfalso
    push Not at hinn
    have hcardU : 2 ∣ Nat.card U := by
      rcases hU2.card_eq_or_dvd with h1 | h2
      · exact absurd (Subgroup.card_eq_one.1 h1) hU1
      · exact h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hcardU
    have hx2 : x ^ 2 = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    have hu2 : (x : MulAut (TwE6Delta.RecipeR K n)) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, hx2, Subgroup.coe_one]
    have hu1 : (x : MulAut (TwE6Delta.RecipeR K n)) ≠ 1 := by
      intro h1
      have hx1 : x = 1 := Subtype.ext h1
      rw [hx1, orderOf_one] at hx
      exact absurd hx (by norm_num)
    have hfix : ∀ a ∈ A, (x : MulAut (TwE6Delta.RecipeR K n)) a = a := by
      intro a ha
      set u : MulAut (TwE6Delta.RecipeR K n) := (x : MulAut (TwE6Delta.RecipeR K n)) with hu
      have hc1 : MulAut.conj a * u * (MulAut.conj a)⁻¹ * u⁻¹ ∈ U :=
        U.mul_mem ((Subgroup.mem_normalizer_iff.1 (hAN a ha) u).1 x.2) (U.inv_mem x.2)
      have hc2 : MulAut.conj a * u * (MulAut.conj a)⁻¹ * u⁻¹ = MulAut.conj (a * (u a)⁻¹) := by
        refine MulEquiv.ext fun y => ?_
        simp only [MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply, map_mul, map_inv,
          MulAut.apply_inv_self]
      have hc3 : MulAut.conj (a * (u a)⁻¹) = 1 := by
        by_contra hne
        rw [hc2] at hc1
        exact hinn _ hc1 hne ⟨_, rfl⟩
      have h1 : a * (u a)⁻¹ = 1 := hinj (hc3.trans (map_one _).symm)
      exact (mul_inv_eq_one.1 h1).symm
    have h4 := TwE6Rank.card_le_four_of_outer_recipeR hn hK hp hp3' hpn hu2 (hinn _ x.2 hu1) hA
      hfix
    have h54 : p ^ 5 ≤ p ^ 4 := h5.trans h4
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h54
    omega

end CFSG.StandardType
