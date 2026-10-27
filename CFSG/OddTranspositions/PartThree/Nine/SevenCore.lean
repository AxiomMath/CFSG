module

public import CFSG.OddTranspositions.PartThree.Nine.Delta
public import CFSG.GroupTheory.PGroup.ExistsNeOneCommute

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex (cosetNormalizerPerm
  cosetNormalizerPerm_apply cosetNormalizerPerm_ker_eq_entire_centralizer)
open CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger (apply_eq_linear_add
  eq_toAffineEquiv_linear)
open CFSG.ProperTwoGeneratedCore.RankOnePair (cosetCoordinates cosetCoordinates_eq_iff
  cosetAffinePerm cosetAffinePerm_injective cosetAffinePerm_apply_coordinates
  cosetAffinePerm_comp_eq affine_apply_zero_eq_zero_iff map_eq_map_of_eqOn linearToAffineHom
  linearToAffineHom_injective inf_normalizer_le_normalizer_coset)
open scoped IsMulCommutative

section Affine

variable {G : Type} [Group G] {U : Subgroup G} [IsElementaryAbelian 2 U] {u : G}

theorem affine_linear_apply
    (φ : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) →*
      (Additive U ≃ᵃ[ZMod 2] Additive U))
    (hφ : ∀ (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) (v : U),
      (n : G) * (u * v) * (n : G)⁻¹ = u * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G))
    (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) (v : U) :
    ((Additive.toMul ((φ n).linear (Additive.ofMul v)) : U) : G) = (n : G) * v * (n : G)⁻¹ := by
  have h1 := hφ n 1
  have hv := hφ n v
  rw [apply_eq_linear_add (φ n) (Additive.ofMul v), toMul_add, Subgroup.coe_mul] at hv
  rw [OneMemClass.coe_one, mul_one, ofMul_one] at h1
  have hlb : ((Additive.toMul ((φ n).linear (Additive.ofMul v)) : U) : G) *
      ((Additive.toMul (φ n 0) : U) : G) =
      ((Additive.toMul (φ n 0) : U) : G) *
        ((Additive.toMul ((φ n).linear (Additive.ofMul v)) : U) : G) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, mul_comm]
  calc ((Additive.toMul ((φ n).linear (Additive.ofMul v)) : U) : G) =
        ((Additive.toMul (φ n 0) : U) : G)⁻¹ *
          (((Additive.toMul ((φ n).linear (Additive.ofMul v)) : U) : G) *
            ((Additive.toMul (φ n 0) : U) : G)) := by
        rw [hlb, inv_mul_cancel_left]
    _ = (u * ((Additive.toMul (φ n 0) : U) : G))⁻¹ *
          (u * (((Additive.toMul ((φ n).linear (Additive.ofMul v)) : U) : G) *
            ((Additive.toMul (φ n 0) : U) : G))) := by group
    _ = ((n : G) * u * (n : G)⁻¹)⁻¹ * ((n : G) * (u * v) * (n : G)⁻¹) := by rw [h1, hv]
    _ = (n : G) * v * (n : G)⁻¹ := by group

theorem affine_linear_eq_one_iff
    (φ : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) →*
      (Additive U ≃ᵃ[ZMod 2] Additive U))
    (hφ : ∀ (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) (v : U),
      (n : G) * (u * v) * (n : G)⁻¹ = u * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G))
    (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) :
    (φ n).linear = 1 ↔ (n : G) ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have hc := affine_linear_apply φ hφ n ⟨v, hv⟩
    rw [h] at hc
    change v = (n : G) * v * (n : G)⁻¹ at hc
    calc v * n = (n : G) * v * (n : G)⁻¹ * n := by rw [← hc]
      _ = n * v := by group
  · intro h
    refine LinearEquiv.ext fun w => Additive.toMul.injective (Subtype.ext ?_)
    have hc := affine_linear_apply φ hφ n (Additive.toMul w)
    rw [ofMul_toMul] at hc
    change ((Additive.toMul ((φ n).linear w) : U) : G) = ((Additive.toMul w : U) : G)
    rw [hc, ← h _ (Additive.toMul w).2, mul_inv_cancel_right]

private theorem exists_semilinear_coordinates_of_linear_eq [Finite G] {k : ℕ} (hk1 : 1 ≤ k)
    (hk : Nat.card U = 2 ^ k)
    (φ : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) →*
      (Additive U ≃ᵃ[ZMod 2] Additive U))
    (hφ : ∀ (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) (v : U),
      (n : G) * (u * v) * (n : G)⁻¹ = u * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G))
    (X : Subgroup (Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))))
    (hXu : ∀ x ∈ X, (x : G) ∈ Subgroup.centralizer ({u} : Set G))
    (hXn : ∀ m : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)),
      (m : G) ∈ Subgroup.centralizer ({u} : Set G) → ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hcyc : IsCyclic (X.map (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G)))))
    (hcard : Nat.card (X.map (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G)))) =
      Nat.card U - 1)
    (hreg : ∀ x y : (fun v : G => u * v) '' (U : Set G), (x : G) ≠ u → (y : G) ≠ u →
      ∃! σ : X.map (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))),
        (σ : Equiv.Perm ((fun v : G => u * v) '' (U : Set G))) x = y)
    (hstab : ∀ n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)),
      ∃ m : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)),
        (m : G) ∈ Subgroup.centralizer ({u} : Set G) ∧
          (AffineEquiv.linearHom.comp φ) n = (AffineEquiv.linearHom.comp φ) m) :
    ∃ ψ : Additive U ≃ₗ[ZMod 2] GaloisField 2 k,
      (∀ n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)),
        ∃ (c : (GaloisField 2 k)ˣ) (σ : GaloisField 2 k ≃+* GaloisField 2 k),
          ∀ v, ψ ((φ n).linear v) = c * σ (ψ v)) ∧
      (∀ g : Additive U ≃ₗ[ZMod 2] Additive U,
        g ∈ X.map (AffineEquiv.linearHom.comp φ) ↔
          ∃ c : (GaloisField 2 k)ˣ, ∀ v, ψ (g v) = c * ψ v) ∧
      ∃ d, d ∣ k ∧ Nat.card (AffineEquiv.linearHom.comp φ).range = (2 ^ k - 1) * d := by
  classical
  have : Finite (Additive U) := inferInstanceAs (Finite U)
  have : Module.Finite (ZMod 2) (Additive U) := Module.Finite.of_finite
  have hV : Module.finrank (ZMod 2) (Additive U) = k := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    rw [Nat.card_zmod, show Nat.card (Additive U) = Nat.card U from rfl, hk] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  set ℓ := AffineEquiv.linearHom.comp φ
  let f := (cosetAffinePerm U u).comp (linearToAffineHom (Additive U))
  have hf : Function.Injective f :=
    (cosetAffinePerm_injective U u).comp (linearToAffineHom_injective (Additive U))
  have hX0 : ∀ x ∈ X, φ x 0 = 0 := fun x hx =>
    (affine_apply_zero_eq_zero_iff φ hφ x).mpr (hXu x hx)
  have hAC : (X.map ℓ).map f =
      X.map (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))) := by
    rw [Subgroup.map_map]
    refine map_eq_map_of_eqOn X fun x hx => ?_
    change cosetAffinePerm U u (φ x).linear.toAffineEquiv = _
    rw [← eq_toAffineEquiv_linear (hX0 x hx), ← cosetAffinePerm_comp_eq φ hφ]
    rfl
  have happly : ∀ (t : Additive U ≃ₗ[ZMod 2] Additive U) (v : Additive U),
      f t (cosetCoordinates U u v) = cosetCoordinates U u (t v) := fun t v =>
    cosetAffinePerm_apply_coordinates U u t.toAffineEquiv v
  have hcomm : ∀ a ∈ X.map ℓ, ∀ b ∈ X.map ℓ, a * b = b * a := by
    have : IsCyclic ((X.map ℓ).map f) := hAC ▸ hcyc
    have : IsCyclic (X.map ℓ) :=
      CFSG.ProperTwoGeneratedCore.RankOnePair.isCyclic_of_map_of_injective hf (X.map ℓ)
    let _ := IsCyclic.commGroup (α := X.map ℓ)
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : X.map ℓ) ⟨b, hb⟩)
  have hreg' : ∀ v w : Additive U, v ≠ 0 → w ≠ 0 → ∃ t ∈ X.map ℓ, t v = w := by
    intro v w hv hw
    obtain ⟨σ, hσ, -⟩ := hreg (cosetCoordinates U u v) (cosetCoordinates U u w)
      (fun h => hv ((cosetCoordinates_eq_iff U u v).mp h))
      (fun h => hw ((cosetCoordinates_eq_iff U u w).mp h))
    have hσA : (σ : Equiv.Perm ((fun v : G => u * v) '' (U : Set G))) ∈ (X.map ℓ).map f := by
      rw [hAC]
      exact σ.2
    obtain ⟨t, ht, hft⟩ := hσA
    refine ⟨t, ht, (cosetCoordinates U u).injective ?_⟩
    rw [← happly, hft]
    exact hσ
  have hAn : ((X.map ℓ).subgroupOf ℓ.range).Normal := by
    refine (Subgroup.normal_subgroupOf_iff (Subgroup.map_le_range ℓ X)).mpr ?_
    rintro _ _ ⟨x, hx, rfl⟩ ⟨n, rfl⟩
    obtain ⟨m, hmu, hnm⟩ := hstab n
    rw [hnm]
    exact ⟨m * x * m⁻¹, hXn m hmu x hx, by rw [map_mul, map_mul, map_inv]⟩
  obtain ⟨ψ, hsemi, hTiff, ⟨d, hd, hcardΓ⟩, -⟩ :=
    CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger.exists_semilinear_coordinates hk1 hV
      (Subgroup.map_le_range ℓ X) hAn hcomm hreg'
  have hcardA : Nat.card (X.map ℓ) = 2 ^ k - 1 := by
    rw [← Subgroup.card_map_of_injective hf, hAC, hcard, hk]
  refine ⟨ψ, fun n => hsemi (ℓ n) ⟨n, rfl⟩, hTiff, d, hd, ?_⟩
  rw [hcardΓ, hcardA]

end Affine

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace DeltaSetup

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

private theorem commute_of_mem_pResidualOf (hC : HypothesisC D) :
    ∀ l ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), Commute hC.d l := fun _ hl =>
  (Subgroup.mem_centralizer_singleton_iff.mp
    (PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ hl))).symm

private theorem exists_conj_of_ne_one (hU : DeltaSetup hC T S U) {v w : G} (hv : v ∈ U)
    (hw : w ∈ U) (hv1 : v ≠ 1) (hw1 : w ≠ 1) :
    ∃ m ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊓ Subgroup.normalizer (U : Set G),
      m * v * m⁻¹ = w := by
  obtain ⟨⟨_, m, hm, rfl⟩, hσ, -⟩ := hU.singer_regular ⟨hC.d * v, v, hv, rfl⟩
    ⟨hC.d * w, w, hw, rfl⟩ (fun h => hv1 (mul_eq_left.mp h)) (fun h => hw1 (mul_eq_left.mp h))
  have hmX := Subgroup.mem_subgroupOf.mp hm
  have h : (m : G) * (hC.d * v) * (m : G)⁻¹ = hC.d * w := congrArg Subtype.val hσ
  have hmu : (m : G) * hC.d = hC.d * m := (commute_of_mem_pResidualOf hC _ hmX.1).eq.symm
  refine ⟨m, hmX, mul_left_cancel (a := hC.d) ?_⟩
  calc hC.d * ((m : G) * v * (m : G)⁻¹) = ((m : G) * hC.d) * v * (m : G)⁻¹ := by
        rw [hmu]
        group
    _ = hC.d * w := by
        rw [← h]
        group

private theorem conj_mem_singer [IsElementaryAbelian 2 U] (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U) (m : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)))
    (hm : (m : G) ∈ Subgroup.centralizer ({hC.d} : Set G))
    {x : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G))}
    (hx : x ∈ (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊓
      Subgroup.normalizer (U : Set G)).subgroupOf
        (Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)))) :
    m * x * m⁻¹ ∈ (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊓
      Subgroup.normalizer (U : Set G)).subgroupOf
        (Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G))) := by
  obtain ⟨hNU, -⟩ := hU.affine h3
  obtain ⟨hxL, hxU⟩ := Subgroup.mem_subgroupOf.mp hx
  have hmα : (m : G) ∈ Subgroup.normalizer hC.alpha := by
    rw [h3.1]
    exact Subgroup.centralizer_le_normalizer _ hm
  have hmL := CFSG.Quasithin.normalizer_le_normalizer_pResidualOf 2 _
    (CFSG.OddTranspositions.normalizer_le_normalizer_Halpha hC.setup.normal hmα)
  refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hmL _).mp hxL
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hNU m.2) hxU) (Subgroup.inv_mem _ (hNU m.2))

theorem regularCore_le_centralizer (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    {Q : Subgroup G} (hQ : IsRegularCore ((fun v : G => hC.d * v) '' (U : Set G)) Q) :
    Q ≤ Subgroup.centralizer (U : Set G) := by
  have := hU.isElementaryAbelian
  obtain ⟨hNU, -⟩ := hU.affine h3
  obtain ⟨hQN, hQn, hQ2, -, -, -⟩ := hQ
  obtain ⟨o, hoU, ho1, hoQ⟩ := CFSG.GroupTheory.exists_ne_one_commute_of_normalizes hQ2
    (IsElementaryAbelian.isPGroup 2 U) hU.ne_bot
    (fun g hg v hv => (Subgroup.mem_normalizer_iff.mp (hNU (hQN hg)) v).mp hv)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1, one_mul, mul_one]
  obtain ⟨m, hmX, rfl⟩ := hU.exists_conj_of_ne_one hoU hw ho1 hw1
  have hmN := inf_normalizer_le_normalizer_coset (commute_of_mem_pResidualOf hC) hmX
  have hx' : m⁻¹ * x * m ∈ Q := by
    have h := hQn m⁻¹ (Subgroup.inv_mem _ hmN) x hx
    rwa [inv_inv] at h
  have hc := hoQ _ hx'
  calc m * o * m⁻¹ * x = m * (o * (m⁻¹ * x * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * x * m) * o) * m⁻¹ := by rw [hc]
    _ = x * (m * o * m⁻¹) := by group

theorem mem_regularCore_of_linear_eq_one [IsElementaryAbelian 2 U] (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((fun v : G => hC.d * v) '' (U : Set G)) Q)
    (φ : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) →*
      (Additive U ≃ᵃ[ZMod 2] Additive U))
    (hφ : ∀ (n : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G))) (v : U),
      (n : G) * (hC.d * v) * (n : G)⁻¹ =
        hC.d * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G))
    {n : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G))}
    (hn : (φ n).linear = 1) : (n : G) ∈ Q := by
  have hnU := (affine_linear_eq_one_iff φ hφ n).mp hn
  have hQU := hU.regularCore_le_centralizer h3 hQ
  obtain ⟨-, -, -, hcent, htr, -⟩ := hQ
  have hu : hC.d ∈ (fun v : G => hC.d * v) '' (U : Set G) := ⟨1, U.one_mem, mul_one _⟩
  have hnu : (n : G) * hC.d * (n : G)⁻¹ ∈ (fun v : G => hC.d * v) '' (U : Set G) :=
    (Subgroup.mem_set_normalizer_iff.mp n.2 _).mp hu
  obtain ⟨x, hxQ, hxu⟩ := htr _ hu _ hnu
  have hm : x⁻¹ * n ∈ Subgroup.centralizer ((fun v : G => hC.d * v) '' (U : Set G)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have hxv : x⁻¹ * v = v * x⁻¹ :=
      (Commute.inv_left (Subgroup.mem_centralizer_iff.mp (hQU hxQ) v hv).symm).eq
    have hnv : (n : G) * v = v * n := (Subgroup.mem_centralizer_iff.mp hnU v hv).symm
    symm
    calc x⁻¹ * n * (hC.d * v) = x⁻¹ * ((n : G) * hC.d * (n : G)⁻¹) * ((n : G) * v) := by group
      _ = x⁻¹ * (x * hC.d * x⁻¹) * (v * n) := by rw [← hxu, hnv]
      _ = hC.d * (x⁻¹ * v) * n := by group
      _ = hC.d * (v * x⁻¹) * n := by rw [hxv]
      _ = hC.d * v * (x⁻¹ * n) := by group
  have hn' : (n : G) = x * (x⁻¹ * n) := by group
  rw [hn']
  exact Q.mul_mem hxQ (hcent hm)

theorem mem_centralizer_of_mul_self_eq_one (hU : DeltaSetup hC T S U) {t : G}
    (htL : t ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    (htU : t ∈ Subgroup.normalizer (U : Set G)) (ht : t * t = 1) :
    t ∈ Subgroup.centralizer ((fun v : G => hC.d * v) '' (U : Set G)) := by
  have htN := inf_normalizer_le_normalizer_coset (commute_of_mem_pResidualOf hC) ⟨htL, htU⟩
  set m : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) := ⟨t, htN⟩
  have hmP : cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G)) m ∈
      ((CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊓
        Subgroup.normalizer (U : Set G)).subgroupOf
          (Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)))).map
            (cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G))) :=
    ⟨m, Subgroup.mem_subgroupOf.mpr ⟨htL, htU⟩, rfl⟩
  have hm2 : m ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact ht)
  have h1 : orderOf (cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G)) m) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hm2, map_one])
  have h2 := Subgroup.orderOf_dvd_natCard _ hmP
  rw [hU.singer_card] at h2
  obtain ⟨k, hk, hcard⟩ := hU.exists_card
  have hodd : Odd (Nat.card U - 1) := by
    rw [hcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hm1 : cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G)) m = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h2
      exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)
  have hker : m ∈ (cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G))).ker :=
    MonoidHom.mem_ker.mpr hm1
  rw [cosetNormalizerPerm_ker_eq_entire_centralizer, Subgroup.mem_subgroupOf] at hker
  exact hker

theorem mem_of_involution_normalizer_pResidualOf (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U) (h5 : Conclusion9_5 D hC T S) {t : G}
    (htL : t ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    (htU : t ∈ Subgroup.normalizer (U : Set G)) (ht : t * t = 1) : t ∈ U := by
  have hc := hU.mem_centralizer_of_mul_self_eq_one htL htU ht
  rw [← hU.sylow_inter, h5.1] at hc
  by_cases ht1 : t = 1
  · rw [ht1]
    exact U.one_mem
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht) ht1
  have hD := (mul_mem_commSet_of_orderOf_eq_two hC hH h3 htL hord).1
  have hT := Subgroup.mul_mem _ (d_mem_sylow_map hC h3 T) hc
  have hmem : hC.d * t ∈ (fun v : G => hC.d * v) '' (U : Set G) := by
    rw [← hU.sylow_map_inter]
    exact ⟨hT, hD⟩
  obtain ⟨w, hw, hwt⟩ := hmem
  rwa [← mul_left_cancel hwt]

omit [Finite G] in
private theorem mul_mul_self_eq_one (hC : HypothesisC D) {d e : G} (hd : d ∈ D) (he : e ∈ D)
    (hc : Commute d e) : d * e * (d * e) = 1 := by
  rw [mul_assoc, ← mul_assoc e d e, ← hc.eq, mul_assoc, hC.setup.oddT.mul_self_eq_one he,
    mul_one, hC.setup.oddT.mul_self_eq_one hd]

private theorem exists_conj_mul_mem_pResidualOf (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U) {d e : G} (hd : d ∈ D) (he : e ∈ D) (hde : d ≠ e)
    (hc : Commute d e) {δ : G} (hδ : δ ∈ (fun v : G => hC.d * v) '' (U : Set G))
    (hδc : Commute δ (d * e)) :
    ∃ g ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)),
      g⁻¹ * (d * e) * g ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
  have hδD : δ ∈ D := by
    rw [← hU.sylow_inter] at hδ
    exact hδ.2
  obtain ⟨hδd, hδe⟩ := (hC.setup.oddT.commute_mul_iff hd he hδD hde hc).mp hδc
  obtain ⟨g, hg, hgu⟩ := hU.transitive hC.d ⟨1, U.one_mem, mul_one _⟩ δ hδ
  refine ⟨g, hg, ?_⟩
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hconj : ∀ x, Commute δ x → Commute (g⁻¹ * x * g) hC.d := fun x hδx => by
    have h := (Commute.conj_iff g⁻¹).mpr hδx.symm
    rwa [inv_inv, ← hgu, show g⁻¹ * (g * hC.d * g⁻¹) * g = hC.d by group] at h
  have hD' : ∀ x ∈ D, g⁻¹ * x * g ∈ D := fun x hx => by
    have h := hC.setup.conj_mem g⁻¹ hx
    rwa [inv_inv] at h
  have hmem : ∀ x ∈ D, Commute x hC.d → x ≠ hC.d →
      hC.d * x ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := fun x hx hxu hne =>
    mul_mem_of_mem_commSet hC h3 ⟨hx, hxu, hne⟩
  obtain ⟨d', hd'⟩ : ∃ d', d' = g⁻¹ * d * g := ⟨_, rfl⟩
  obtain ⟨e', he'⟩ : ∃ e', e' = g⁻¹ * e * g := ⟨_, rfl⟩
  have hd'D : d' ∈ D := by rw [hd']; exact hD' d hd
  have he'D : e' ∈ D := by rw [he']; exact hD' e he
  have hd'u : Commute d' hC.d := by rw [hd']; exact hconj d hδd
  have he'u : Commute e' hC.d := by rw [he']; exact hconj e hδe
  have hne : d' ≠ e' := by
    intro h
    apply hde
    calc d = g * d' * g⁻¹ := by rw [hd']; group
      _ = g * e' * g⁻¹ := by rw [h]
      _ = e := by rw [he']; group
  have hy : g⁻¹ * (d * e) * g = d' * e' := by rw [hd', he']; group
  rw [hy]
  by_cases hdu : d' = hC.d
  · have heu : e' ≠ hC.d := fun h => hne (hdu.trans h.symm)
    rw [hdu]
    exact hmem e' he'D he'u heu
  · by_cases heu : e' = hC.d
    · rw [heu, hd'u.eq]
      exact hmem d' hd'D hd'u hdu
    · have h : d' * e' = (hC.d * d') * (hC.d * e') := by
        rw [← mul_assoc, mul_assoc hC.d d' hC.d, hd'u.eq, ← mul_assoc, hu2, one_mul]
      rw [h]
      exact Subgroup.mul_mem _ (hmem d' hd'D hd'u hdu) (hmem e' he'D he'u heu)

private theorem exists_conj_mul_mem_involution (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U) {d e : G} (hd : d ∈ D) (he : e ∈ D) (hde : d ≠ e)
    (hc : Commute d e) (hN : d * e ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)))
    {δ : G} (hδ : δ ∈ (fun v : G => hC.d * v) '' (U : Set G)) (hδc : Commute δ (d * e)) :
    ∃ g ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)),
      g⁻¹ * (d * e) * g ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ∧
        g⁻¹ * (d * e) * g ∈ Subgroup.normalizer (U : Set G) ∧
          g⁻¹ * (d * e) * g * (g⁻¹ * (d * e) * g) = 1 := by
  have := hU.isElementaryAbelian
  obtain ⟨hNU, -⟩ := hU.affine h3
  obtain ⟨g, hg, hyL⟩ := hU.exists_conj_mul_mem_pResidualOf h3 hd he hde hc hδ hδc
  refine ⟨g, hg, hyL, hNU (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hN) hg),
    ?_⟩
  rw [show g⁻¹ * (d * e) * g * (g⁻¹ * (d * e) * g) = g⁻¹ * (d * e * (d * e)) * g by group,
    mul_mul_self_eq_one hC hd he hc, mul_one, inv_mul_cancel]

theorem mul_mem_centralizer_of_commute (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    {d e : G} (hd : d ∈ D) (he : e ∈ D) (hde : d ≠ e) (hc : Commute d e)
    (hN : d * e ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)))
    {δ : G} (hδ : δ ∈ (fun v : G => hC.d * v) '' (U : Set G)) (hδc : Commute δ (d * e)) :
    d * e ∈ Subgroup.centralizer ((fun v : G => hC.d * v) '' (U : Set G)) := by
  obtain ⟨g, hg, hyL, hyU, hy2⟩ := hU.exists_conj_mul_mem_involution h3 hd he hde hc hN hδ hδc
  have hcent := hU.mem_centralizer_of_mul_self_eq_one hyL hyU hy2
  rw [Subgroup.mem_centralizer_iff] at hcent ⊢
  intro x hx
  have h := hcent _ ((Subgroup.mem_set_normalizer_iff''.mp hg x).mp hx)
  calc x * (d * e) = g * ((g⁻¹ * x * g) * (g⁻¹ * (d * e) * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * (d * e) * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    _ = d * e * x := by group

theorem exists_semilinear_coordinates_of_isRegularCore [IsElementaryAbelian 2 U]
    (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((fun v : G => hC.d * v) '' (U : Set G)) Q)
    (φ : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) →*
      (Additive U ≃ᵃ[ZMod 2] Additive U))
    (hφ : ∀ (n : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G))) (v : U),
      (n : G) * (hC.d * v) * (n : G)⁻¹ =
        hC.d * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G))
    {k : ℕ} (hk : Nat.card U = 2 ^ k) :
    ∃ ψ : Additive U ≃ₗ[ZMod 2] GaloisField 2 k,
      (∀ n : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)),
        ∃ (c : (GaloisField 2 k)ˣ) (σ : GaloisField 2 k ≃+* GaloisField 2 k),
          ∀ v, ψ ((φ n).linear v) = c * σ (ψ v)) ∧
      (∀ g : Additive U ≃ₗ[ZMod 2] Additive U,
        g ∈ ((CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊓
            Subgroup.normalizer (U : Set G)).subgroupOf
              (Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)))).map
            (AffineEquiv.linearHom.comp φ) ↔
          ∃ c : (GaloisField 2 k)ˣ, ∀ v, ψ (g v) = c * ψ v) ∧
      ∃ d, d ∣ k ∧ Nat.card (AffineEquiv.linearHom.comp φ).range = (2 ^ k - 1) * d := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hk, pow_zero])) hU.ne_bot
    · exact h
  have hQU := hU.regularCore_le_centralizer h3 hQ
  obtain ⟨hQN, -, -, -, htr, -⟩ := hQ
  refine exists_semilinear_coordinates_of_linear_eq hk1 hk φ hφ
    ((CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊓
      Subgroup.normalizer (U : Set G)).subgroupOf
        (Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G))))
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_of_mem_pResidualOf hC _ (Subgroup.mem_subgroupOf.mp hx).1).eq.symm)
    (fun m hm x hx => hU.conj_mem_singer h3 m hm hx) hU.singer_isCyclic hU.singer_card
    hU.singer_regular fun n => ?_
  have hu : hC.d ∈ (fun v : G => hC.d * v) '' (U : Set G) := ⟨1, U.one_mem, mul_one _⟩
  obtain ⟨x, hxQ, hxu⟩ := htr _ hu _ ((Subgroup.mem_set_normalizer_iff.mp n.2 _).mp hu)
  have hx'1 : (AffineEquiv.linearHom.comp φ) ⟨x, hQN hxQ⟩ = 1 :=
    (affine_linear_eq_one_iff φ hφ ⟨x, hQN hxQ⟩).mpr (hQU hxQ)
  refine ⟨⟨x, hQN hxQ⟩⁻¹ * n, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    change x⁻¹ * n * hC.d = hC.d * (x⁻¹ * n)
    calc x⁻¹ * n * hC.d = x⁻¹ * ((n : G) * hC.d * (n : G)⁻¹) * n := by group
      _ = x⁻¹ * (x * hC.d * x⁻¹) * n := by rw [hxu]
      _ = hC.d * (x⁻¹ * n) := by group
  · rw [map_mul, map_inv, hx'1, inv_one, one_mul]

end DeltaSetup

end CFSG.OddTranspositions.PartThree.Nine
