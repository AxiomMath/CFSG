module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoOrderFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoAutHolds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerSylowTransfer
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qYamLat
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Is3D4)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup graphFixedPosUnipotent graphFixedRootTorus
  graphFixedRootBorel)

theorem exists_mem_conj_pow_three {A : Type} [Group A] {Y : Subgroup A}
    (hOut : Nat.card (Outer ↥Y) = 3) {r : A} (hr : r ∈ normalizer (Y : Set A)) :
    ∃ y ∈ Y, ∀ t ∈ Y, r ^ 3 * t * (r ^ 3)⁻¹ = y * t * y⁻¹ := by
  set φ : MulAut ↥Y := Y.normalizerMonoidHom ⟨r, hr⟩ with hφ
  have h1 : ((φ ^ 3 : MulAut ↥Y) : Outer ↥Y) = 1 := by
    rw [QuotientGroup.mk_pow, ← hOut]
    exact pow_card_eq_one'
  rw [QuotientGroup.eq_one_iff] at h1
  change φ ^ 3 ∈ (MulAut.conj : ↥Y →* MulAut ↥Y).range at h1
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp h1
  refine ⟨y, y.2, fun t ht => ?_⟩
  have h2 := congrArg (fun α : MulAut ↥Y => ((α ⟨t, ht⟩ : ↥Y) : A)) hy
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rw [hφ, ← map_pow, normalizerMonoidHom_apply_apply_coe] at h2
  simpa only [Subgroup.coe_pow] using h2.symm

theorem exists_two_pow_of_relIndex_seven {A : Type} [Group A] {B U : Subgroup A}
    (hUB : U ≤ B) (hBN : B ≤ normalizer (U : Set A)) (hidx : U.relIndex B = 7)
    {r y : A} (hrB : r ∈ normalizer (B : Set A)) (hrU : r ∈ normalizer (U : Set A))
    (hyB : y ∈ B) (hy : ∀ b ∈ B, r ^ 3 * b * (r ^ 3)⁻¹ = y * b * y⁻¹) :
    ∃ j : ℕ, ∀ b ∈ B, r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U := by
  have h7 : ∀ c : ZMod 7, c ^ 3 = 1 → c = 1 ∨ c = 2 ∨ c = 4 := by decide +kernel
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : (U.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mpr hBN
  have hcard : Nat.card (↥B ⧸ U.subgroupOf B) = 7 := hidx
  have : IsCyclic (↥B ⧸ U.subgroupOf B) := isCyclic_of_prime_card hcard
  have hcomm : ∀ a b : ↥B ⧸ U.subgroupOf B, a * b = b * a := fun a b =>
    (IsCyclic.commutative (α := ↥B ⧸ U.subgroupOf B)).is_comm.comm a b
  set c : ↥B →* ↥B := (B.normalizerMonoidHom ⟨r, hrB⟩).toMonoidHom with hc
  have hcoe : ∀ b : ↥B, ((c b : ↥B) : A) = r * b * r⁻¹ := fun b =>
    normalizerMonoidHom_apply_apply_coe B ⟨r, hrB⟩ b
  have hcN : U.subgroupOf B ≤ (U.subgroupOf B).comap c := by
    intro b hb
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hcoe]
    exact (Subgroup.mem_normalizer_iff.mp hrU _).mp (Subgroup.mem_subgroupOf.mp hb)
  set ψ := QuotientGroup.map (U.subgroupOf B) (U.subgroupOf B) c hcN with hψ
  have hψmk : ∀ b : ↥B, ψ (b : ↥B ⧸ U.subgroupOf B) = ((c b : ↥B) : ↥B ⧸ U.subgroupOf B) :=
    fun b => QuotientGroup.map_mk _ _ _ _ b
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic ψ
  have hψ3 : ∀ q : ↥B ⧸ U.subgroupOf B, q ^ (m * (m * m)) = q := by
    intro q
    refine QuotientGroup.induction_on q fun b => ?_
    have h1 : ψ (ψ (ψ (b : ↥B ⧸ U.subgroupOf B))) = (b : ↥B ⧸ U.subgroupOf B) := by
      rw [hψmk, hψmk, hψmk]
      have h2 : c (c (c b)) = ⟨y, hyB⟩ * b * (⟨y, hyB⟩ : ↥B)⁻¹ := by
        apply Subtype.ext
        rw [hcoe, hcoe, hcoe]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hy b b.2, pow_three]
        group
      rw [h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        hcomm _ (b : ↥B ⧸ U.subgroupOf B), mul_assoc, mul_inv_cancel, mul_one]
    rw [hm, hm, hm, ← zpow_mul, ← zpow_mul] at h1
    exact h1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥B ⧸ U.subgroupOf B)
  have hog : orderOf g = 7 := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : ((7 : ℕ) : ℤ) ∣ m * (m * m) - 1 := by
    rw [← hog]
    refine orderOf_dvd_iff_zpow_eq_one.mpr ?_
    rw [zpow_sub, zpow_one, hψ3 g, mul_inv_cancel]
  have hx : (m : ZMod 7) * ((m : ZMod 7) * m) = 1 := by
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (m * (m * m)) 7).mpr hdvd
    push_cast at h
    exact h.symm
  have hpow : ∃ j : ℕ, ((7 : ℕ) : ℤ) ∣ m - 2 ^ j := by
    rcases h7 _ (by simpa [pow_three, mul_assoc] using hx) with h | h | h
    · refine ⟨0, (ZMod.intCast_eq_intCast_iff_dvd_sub (2 ^ 0) m 7).mp ?_⟩
      push_cast
      rw [h]
    · refine ⟨1, (ZMod.intCast_eq_intCast_iff_dvd_sub (2 ^ 1) m 7).mp ?_⟩
      push_cast
      rw [h]
    · refine ⟨2, (ZMod.intCast_eq_intCast_iff_dvd_sub (2 ^ 2) m 7).mp ?_⟩
      push_cast
      rw [h]
  obtain ⟨j, k, hk⟩ := hpow
  have hm' : m = ((2 ^ j : ℕ) : ℤ) + ((7 : ℕ) : ℤ) * k := by
    push_cast
    exact sub_eq_iff_eq_add'.mp hk
  refine ⟨j, fun b hb => ?_⟩
  have h7 : ∀ q : ↥B ⧸ U.subgroupOf B, q ^ ((7 : ℕ) : ℤ) = 1 := fun q => by
    rw [zpow_natCast, ← hcard]
    exact pow_card_eq_one'
  have h1 : ((c ⟨b, hb⟩ : ↥B) : ↥B ⧸ U.subgroupOf B) =
      (((⟨b, hb⟩ : ↥B) ^ 2 ^ j : ↥B) : ↥B ⧸ U.subgroupOf B) := by
    rw [← hψmk, hm, hm', zpow_add, zpow_mul, h7, one_zpow, mul_one, zpow_natCast,
      QuotientGroup.mk_pow]
  have h2 : ((c ⟨b, hb⟩ * ((⟨b, hb⟩ : ↥B) ^ 2 ^ j)⁻¹ : ↥B) : ↥B ⧸ U.subgroupOf B) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hcoe] using h2

theorem card_inf_normalizer_of_is3D4_one
    {A : Type} [Group A] [Finite A] {Y U : Subgroup A} (hY : Is3D4 ↥Y 1)
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U Y) :
    Nat.card ↥(Y ⊓ normalizer (U : Set A)) = 7 * Nat.card U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    Inputs1719.exists_mulEquiv_graphFixedRootGroup_of_is3D4_one hY
  have hK3 : Nat.card K = (2 ^ 1) ^ 3 := by simpa only [pow_one] using hK
  have hσ1 : ∀ c, σ.toRingHom c = c ^ ((2 ^ 1) ^ 1) := fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, pow_one, pow_one]
    exact hσ c
  obtain ⟨-, hH, hU0⟩ := CFSG.LieType.Chevalley.triality_both_orientations_exact_finite_order
    2 1 Nat.prime_two le_rfl K hK3 1 (Or.inl rfl) σ.toRingHom hσ1
  have hB : Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) = 7 * 2 ^ 12 := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootBorel σ.surjective, hH, hU0]
    norm_num
  have hN0 : Nat.card ↥(normalizer (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) = 7 * 2 ^ 12 := by
    rw [CFSG.Quasithin.H13.F431.D4q.Hex.d4_normalizer_eq σ, ← hB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (CFSG.LieType.Chevalley.graphFixedRootBorel_le _ _ _)).toEquiv
  have hcU : Nat.card ↥((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = 2 ^ 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (CFSG.LieType.Chevalley.graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)).toEquiv, hU0]
    norm_num
  have hC : Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = 211341312 := by
    rw [← Nat.card_congr e.toEquiv]
    exact Inputs1719.card_eq_of_is3D4_one hY
  have hidx : ¬ 2 ∣ ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).index := by
    have h1 := Subgroup.card_mul_index
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    rw [hcU, hC] at h1
    have h2 : ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).index = 51597 := by omega
    rw [h2]
    norm_num
  let S₀ : Sylow 2 ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (IsPGroup.of_card hcU).toSylow hidx
  let P : Sylow 2 ↥Y := CFSG.AGLEmbedding.TwoGenInner.sylowOfIsSylowTwoOf hU
  let P' : Sylow 2 ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P
  have h1 : Nat.card ↥(Y ⊓ normalizer (U : Set A)) =
      Nat.card ↥(normalizer (((P : Subgroup ↥Y).map e.toMonoidHom :
        Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
    rw [CFSG.AGLEmbedding.TwoGenInner.card_inf_normalizer_eq hU.1,
      CFSG.AGLEmbedding.TwoGenInner.card_normalizer_map_equiv e]
    rfl
  have h2 : Nat.card ↥(normalizer (((P : Subgroup ↥Y).map e.toMonoidHom :
        Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) =
      Nat.card ↥(normalizer ((S₀ : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :=
    CFSG.AGLEmbedding.TwoGenInner.card_normalizer_sylow_eq P' S₀
  have h3 : Nat.card ↥((P : Subgroup ↥Y).map e.toMonoidHom) =
      Nat.card (S₀ : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    (Sylow.card_eq_multiplicity P').trans (Sylow.card_eq_multiplicity S₀).symm
  rw [Subgroup.card_map_of_injective e.injective] at h3
  have hUcard : Nat.card U = 2 ^ 12 := by
    rw [← hcU]
    calc Nat.card U = Nat.card ↥(U.subgroupOf Y) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU.1).toEquiv).symm
      _ = _ := h3
  rw [h1, h2, hUcard]
  exact hN0

theorem k_3D4TwoBorel_holds :
    Inputs1719.K_3D4TwoBorel := by
  intro A _ _ Y U hY hU
  have hcard := card_inf_normalizer_of_is3D4_one hY hU
  refine ⟨Dvd.intro _ hcard.symm, fun r hr => ?_⟩
  obtain ⟨hrY, hrU⟩ := Subgroup.mem_inf.mp hr
  have hUB : U ≤ Y ⊓ normalizer (U : Set A) := le_inf hU.1 Subgroup.le_normalizer
  have hidx : U.relIndex (Y ⊓ normalizer (U : Set A)) = 7 := by
    have h1 := Subgroup.relIndex_mul_card (H := U) (K := Y ⊓ normalizer (U : Set A))
    rw [inf_eq_left.mpr hUB, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hrB : r ∈ normalizer ((Y ⊓ normalizer (U : Set A) : Subgroup A) : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    simp only [Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp hrY g)
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hrU) g)
  obtain ⟨-, -, hOut⟩ := Inputs1719.k_3D4TwoAut_holds ↥Y hY
  obtain ⟨y, hyY, hy⟩ := exists_mem_conj_pow_three hOut hrY
  have hr3 : r ^ 3 ∈ normalizer (U : Set A) := Subgroup.pow_mem _ hrU 3
  have hyN : y ∈ normalizer (U : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [← hy u (hU.1 hu)]
      exact (Subgroup.mem_normalizer_iff.mp hr3 u).mp hu
    · intro hu
      have huY : u ∈ Y := by
        have h1 : y⁻¹ * (y * u * y⁻¹) * y ∈ Y :=
          Y.mul_mem (Y.mul_mem (Y.inv_mem hyY) (hU.1 hu)) hyY
        rwa [show y⁻¹ * (y * u * y⁻¹) * y = u by group] at h1
      rw [← hy u huY] at hu
      exact (Subgroup.mem_normalizer_iff.mp hr3 u).mpr hu
  exact exists_two_pow_of_relIndex_seven hUB inf_le_right hidx hrB hrU ⟨hyY, hyN⟩
    (fun b hb => hy b hb.1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
