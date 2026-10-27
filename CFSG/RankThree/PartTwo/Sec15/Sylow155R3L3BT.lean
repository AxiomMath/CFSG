module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L3Conj
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016Core
import CFSG.Quasithin.H13.A6S13821zz20
import CFSG.RankThree.PartTwo.KFacts.K71SU3TwoFree

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

private theorem eq_bot_of_normalizes_comap {G H : Type} [Group G] [Finite G] [Group H]
    (φ : G →* H) (hker : φ.ker ≤ Subgroup.center G) {W : Subgroup H} (hW : IsPGroup 2 W)
    (hWr : W ≤ φ.range) {y : G} (hWy : φ y ∈ Subgroup.normalizer (W : Set H))
    (hBT : ∀ X : Subgroup G, IsPGroup 2 X → (∀ x ∈ X, y⁻¹ * x * y ∈ X) → X = ⊥) :
    W = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI : Finite W :=
    Finite.of_injective (Subgroup.inclusion hWr) (Subgroup.inclusion_injective hWr)
  set P : Subgroup G := W.comap φ
  set F : P →* W := (φ.comp P.subtype).codRestrict W (fun x => x.2)
  have hFs : Function.Surjective F := by
    rintro ⟨w, hw⟩
    obtain ⟨x, rfl⟩ := hWr hw
    exact ⟨⟨x, hw⟩, rfl⟩
  have hZc : F.ker ≤ Subgroup.center P := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hφx : φ x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hφx)) g)
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  have hcard : Nat.card (P ⧸ F.ker) = 2 ^ k := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective F hFs).toEquiv]
    exact hk
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 P))
  have hSn : (S : Subgroup P).Normal :=
    CFSG.LocalAnalysis.GLTheoremA.I2016.sylow_two_normal_of_central F.ker hZc hcard S
  have hSu : Unique (Sylow 2 P) := Sylow.unique_of_normal S hSn
  set T : Subgroup G := (S : Subgroup P).map P.subtype
  have hT2 : IsPGroup 2 T := S.isPGroup'.map _
  have hTP : T ≤ P := Subgroup.map_subtype_le _
  have hle : ∀ X : Subgroup G, X ≤ P → IsPGroup 2 X → X ≤ T := by
    intro X hXP hX2
    have hX2' : IsPGroup 2 (X.subgroupOf P) :=
      hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXP).symm
    obtain ⟨S', hS'⟩ := hX2'.exists_le_sylow
    rw [Subsingleton.elim S' S] at hS'
    intro x hx
    exact ⟨⟨x, hXP hx⟩, hS' (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hTy : ∀ x ∈ T, y⁻¹ * x * y ∈ T := by
    intro x hx
    have hT'P : T.map (MulAut.conj y⁻¹).toMonoidHom ≤ P := by
      rintro _ ⟨t, ht, rfl⟩
      have h1 : φ t ∈ W := hTP ht
      have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hWy) (φ t)).mp h1
      show φ (y⁻¹ * t * y⁻¹⁻¹) ∈ W
      simpa only [map_mul, map_inv] using h2
    have h3 := hle _ hT'P (hT2.map _) (Subgroup.mem_map_of_mem _ hx)
    simpa [MulAut.conj_apply] using h3
  have hT1 : T = ⊥ := hBT T hT2 hTy
  have hS1 : (S : Subgroup P) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).mp hT1
  have h2P : ¬ 2 ∣ Nat.card P := fun h => S.ne_bot_of_dvd_card h hS1
  have hWP : Nat.card W ∣ Nat.card P := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup F.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective F hFs).toEquiv]
    exact dvd_mul_right _ _
  rcases k with _ | k
  · exact Subgroup.eq_bot_of_card_eq W (by rw [hk, pow_zero])
  · have h2W : 2 ∣ Nat.card W := by
      rw [hk]
      exact dvd_pow_self 2 (Nat.succ_ne_zero k)
    exact absurd (h2W.trans hWP) h2P

variable {π : Bool} {f : ℕ} {K : Type} [Field K]

theorem eq_bot_of_normalizes_range (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (2 ^ f) K)
    (hBT : ∀ X : Subgroup (GL (Fin 3) K), X ≤ glPi π 3 (2 ^ f) K → IsPGroup 2 X →
      (∀ x ∈ X, y⁻¹ * x * y ∈ X) → X = ⊥)
    {W : Subgroup (MulAut (slPi π 3 (2 ^ f) K))} (hW : IsPGroup 2 W)
    (hWr : W ≤ (slPiConj hK).range)
    (hWy : slPiConj hK ⟨y, hy⟩ ∈ Subgroup.normalizer (W : Set (MulAut (slPi π 3 (2 ^ f) K)))) :
    W = ⊥ := by
  have := hK.finite
  refine eq_bot_of_normalizes_comap (slPiConj hK) (fun x hx => ?_) hW hWr hWy
    (fun X hX2 hXy => ?_)
  · obtain ⟨ℓ, hℓ⟩ := exists_scalar_of_slPiConj_eq_one hK hq (MonoidHom.mem_ker.mp hx)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (commute_of_mem_statedScalars ⟨ℓ, hℓ.symm⟩ (g : GL (Fin 3) K))
  · have hXb : X.map (glPi π 3 (2 ^ f) K).subtype = ⊥ := by
      refine hBT _ (Subgroup.map_subtype_le X) (hX2.map _) ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, hXy x hx, rfl⟩
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hXb

private theorem inf_range_eq_bot_of_hBT (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (2 ^ f) K)
    (hBT : ∀ X : Subgroup (GL (Fin 3) K), X ≤ glPi π 3 (2 ^ f) K → IsPGroup 2 X →
      (∀ x ∈ X, y⁻¹ * x * y ∈ X) → X = ⊥)
    {V : Subgroup (MulAut (slPi π 3 (2 ^ f) K))} (hV : IsPGroup 2 V)
    (hVy : slPiConj hK ⟨y, hy⟩ ∈ Subgroup.normalizer (V : Set (MulAut (slPi π 3 (2 ^ f) K)))) :
    V ⊓ (slPiConj hK).range = ⊥ :=
  eq_bot_of_normalizes_range hK hq hy hBT (hV.to_inf_left) inf_le_right
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hVy, Subgroup.le_normalizer ⟨⟨y, hy⟩, rfl⟩⟩)

theorem inf_range_eq_bot_of_irreducible (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (2 ^ f) K) {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy3 : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1)
    {V : Subgroup (MulAut (slPi π 3 (2 ^ f) K))} (hV : IsPGroup 2 V)
    (hVy : slPiConj hK ⟨y, hy⟩ ∈ Subgroup.normalizer (V : Set (MulAut (slPi π 3 (2 ^ f) K)))) :
    V ⊓ (slPiConj hK).range = ⊥ := by
  have := hK.finite
  have := hK.charP
  refine inf_range_eq_bot_of_hBT hK hq hy (fun X _ hX2 hXy => ?_) hV hVy
  by_contra hX1
  exact CFSG.Quasithin.H13.A6.A6S20.false_of_irreducible_of_normalizes hX2 hX1 hXy
    fun W hW => eq_bot_or_eq_top_of_invariant hℓ hy3 hW

theorem inf_range_eq_bot_of_unitary (hK : PiField false 2 f K) (hq : ModThree false (2 ^ f))
    {j : slPi false 3 (2 ^ f) K} (hj3 : j ^ 3 = 1)
    (hjz : j ∉ Subgroup.center (slPi false 3 (2 ^ f) K))
    {V : Subgroup (MulAut (slPi false 3 (2 ^ f) K))} (hV : IsPGroup 2 V)
    (hVj : MulAut.conj j ∈ Subgroup.normalizer (V : Set (MulAut (slPi false 3 (2 ^ f) K)))) :
    V ⊓ (slPiConj hK).range = ⊥ := by
  have hy : (j : GL (Fin 3) K) ∈ glPi false 3 (2 ^ f) K :=
    slPi_le_glPi (fun _ => hK.unitary) j.2
  rw [conj_eq_slPiConj hK j] at hVj
  refine inf_range_eq_bot_of_hBT hK hq hy (fun X hXu hX2 hXy => ?_) hV hVj
  refine KFacts.eq_bot_of_normalizes hK hq (v := (j : GL (Fin 3) K)⁻¹) (inv_mem j.2) ?_ ?_ hXu hX2
    fun x hx => ?_
  · rw [inv_pow, ← Subgroup.coe_pow, hj3, Subgroup.coe_one, inv_one]
  · intro c hc
    apply hjz
    rw [Subgroup.mem_center_iff]
    intro g
    refine Subtype.ext ?_
    have hcomm : ∀ g : GL (Fin 3) K, ((j : GL (Fin 3) K)⁻¹) * g = g * (j : GL (Fin 3) K)⁻¹ :=
      fun g => Units.ext (by
        rw [Units.val_mul, Units.val_mul, hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
          Matrix.mul_one])
    exact ((Commute.inv_left_iff.mp (hcomm (g : GL (Fin 3) K))).symm).eq
  · rw [inv_inv]
    exact hXy x hx

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
