module

public import CFSG.Quasithin.Vol2.Ch10SecABasicCent
public import CFSG.Quasithin.Vol2.Ch10SecD32B
public import CFSG.Quasithin.Background.E3Basic
public import CFSG.Quasithin.Vol2.Ch10SecD211C
public import CFSG.Quasithin.Vol2.Ch10SecD211F
public import CFSG.Quasithin.Vol2.Ch10SecDFacts211

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem L3.pow_twelve_eq_one_of_fix :
    ∀ γ : CFSG.Quasithin.L3.Γ, ∀ c : CFSG.Quasithin.L3.Vec, c ≠ 0 →
      CFSG.Quasithin.L3.act γ c = c → γ ^ 12 = 1 := by
  decide +kernel

theorem L3.eq_fix_add_comm :
    ∀ γ : CFSG.Quasithin.L3.Γ, ∀ c : CFSG.Quasithin.L3.Vec, c ≠ 0 →
      CFSG.Quasithin.L3.act γ c = c → γ ^ 3 = 1 → γ ≠ 1 →
      ∀ w : CFSG.Quasithin.L3.Vec, ∃ u : CFSG.Quasithin.L3.Vec,
        w = CFSG.Quasithin.L3.act γ u - u ∨ w = CFSG.Quasithin.L3.act γ u - u + c := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem conjAct_apply_coe {V : Subgroup G} (g : Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ((conjAct V g v : ↥V) : G) = (g : G) * v * (g : G)⁻¹ := rfl

omit [Finite G] in
theorem pow_twelve_mem_centralizer_V1 (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥)
    {x : G} (hxN : x ∈ Subgroup.normalizer (fsuUL T L I : Set G)) {v : G} (hv : v ∈ fsuUL T L I)
    (hv1 : v ≠ 1) (hxv : x * v = v * x) :
    x ^ 12 ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  have hβinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (D.ker_β u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  obtain ⟨γ, hγ⟩ := D.exists_rho (g := conjAct (fsuUL T L I) ⟨x, hxN⟩)
    (by rw [autOn_L_V1_eq_top h3 hc]; trivial)
  have hσv : conjAct (fsuUL T L I) ⟨x, hxN⟩ ⟨v, hv⟩ = ⟨v, hv⟩ := by
    apply Subtype.ext
    rw [conjAct_apply_coe]
    change x * v * x⁻¹ = v
    rw [hxv, mul_inv_cancel_right]
  have hfix : CFSG.Quasithin.L3.act γ (Multiplicative.toAdd (D.β ⟨⟨v, hv⟩, trivial⟩)) =
      Multiplicative.toAdd (D.β ⟨⟨v, hv⟩, trivial⟩) := by
    have h1 := D.β_rho γ ⟨v, hv⟩ trivial trivial
    have h2 : (⟨D.rho γ ⟨v, hv⟩, trivial⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) =
        ⟨⟨v, hv⟩, trivial⟩ := by
      apply Subtype.ext
      change D.rho γ ⟨v, hv⟩ = ⟨v, hv⟩
      rw [hγ]
      exact hσv
    rw [h2] at h1
    exact (congrArg Multiplicative.toAdd h1).symm
  have hc0 : Multiplicative.toAdd (D.β ⟨⟨v, hv⟩, trivial⟩) ≠ 0 := by
    intro h0
    apply hv1
    have h1 : D.β ⟨⟨v, hv⟩, trivial⟩ = 1 := Multiplicative.toAdd.injective (by simpa using h0)
    have h2 := hβinj (h1.trans (map_one D.β).symm)
    have := congrArg (fun w : ↥(⊤ : Subgroup ↥(fsuUL T L I)) => ((w : ↥(fsuUL T L I)) : G)) h2
    simpa using this
  have h12 := L3.pow_twelve_eq_one_of_fix γ _ hc0 hfix
  have hσ12 : conjAct (fsuUL T L I) (⟨x, hxN⟩ ^ 12) = 1 := by
    rw [map_pow, ← hγ, ← map_pow, h12, map_one]
  exact (conjAct_eq_one_iff _).mp hσ12

omit [Finite G] in
theorem pow_twelve_mem_centralizer_V2 (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥)
    {t : G} (ht : t ∈ T) {x : G}
    (hxN : x ∈ Subgroup.normalizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G))
    {v : G} (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hv1 : v ≠ 1) (hxv : x * v = v * x) :
    x ^ 12 ∈ Subgroup.centralizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
  have hyN : t * x * t⁻¹ ∈ Subgroup.normalizer (fsuUL T L I : Set G) := by
    have h1 : x ∈ conjSubgroup (Subgroup.normalizer (fsuUL T L I : Set G)) t := by
      rw [E3.conjSubgroup_normalizer]
      rw [V2_eq_conjugate ht] at hxN
      exact hxN
    exact mem_conjSubgroup_iff.mp h1
  have hvt : t * v * t⁻¹ ∈ fsuUL T L I := by
    rw [V2_eq_conjugate ht, SecA.mem_conjugate_iff] at hv
    exact hv
  have hvt1 : t * v * t⁻¹ ≠ 1 := fun h' => hv1 (by
    calc v = t⁻¹ * (t * v * t⁻¹) * t := by group
      _ = 1 := by rw [h']; group)
  have hyv : t * x * t⁻¹ * (t * v * t⁻¹) = t * v * t⁻¹ * (t * x * t⁻¹) := by
    calc t * x * t⁻¹ * (t * v * t⁻¹) = t * (x * v) * t⁻¹ := by group
      _ = t * (v * x) * t⁻¹ := by rw [hxv]
      _ = t * v * t⁻¹ * (t * x * t⁻¹) := by group
  have h12 := pow_twelve_mem_centralizer_V1 h3 hc hyN hvt hvt1 hyv
  rw [conj_pow] at h12
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hwt : t * w * t⁻¹ ∈ fsuUL T L I := by
    have hw' : w ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := hw
    rw [V2_eq_conjugate ht, SecA.mem_conjugate_iff] at hw'
    exact hw'
  have h1 := (Subgroup.mem_centralizer_iff.mp h12) _ hwt
  calc w * x ^ 12 = t⁻¹ * (t * w * t⁻¹ * (t * x ^ 12 * t⁻¹)) * t := by group
    _ = t⁻¹ * (t * x ^ 12 * t⁻¹ * (t * w * t⁻¹)) * t := by rw [h1]
    _ = x ^ 12 * w := by group

theorem pow_three_eq_one_of_mem (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) {x : G}
    (hx : x ∈ fsuL0 T L ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G)) (hxo : Odd (orderOf x)) :
    x ^ 3 = 1 := by
  have hxE := fsuL0_inf_centralizer_z_le h37 h38 h hc hd hx
  obtain ⟨ht, htn, hv1, hv11, hv2, hv21⟩ := hd
  have hxv1 : x * v₁ = v₁ * x := ((Subgroup.mem_centralizer_iff.mp hxE) v₁
    (Subgroup.subset_closure (Set.mem_insert _ _))).symm
  have hxv2 : x * v₂ = v₂ * x := ((Subgroup.mem_centralizer_iff.mp hxE) v₂
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))).symm
  obtain ⟨hN1, hN2⟩ := fsuL0_le_normalizer_V12 h37 h38 h ht htn
  have h1 := pow_twelve_mem_centralizer_V1 h3 hc (hN1 hx.1) hv1.1 hv11 hxv1
  have h2 := pow_twelve_mem_centralizer_V2 h3 hc ht (hN2 hx.1) hv2.1 hv21 hxv2
  have hV : x ^ 12 ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    have hle : fsuUL T L I ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤
        Subgroup.centralizer ({x ^ 12} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp h1) a ha)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp h2) a ha)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [SecA.fsuVM_eq_sup h37 h38 h ht htn] at hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have hO2 := SecA.fsuL0_inf_centralizer_le h37 h38 h ⟨(fsuL0 T L).pow_mem hx.1 12, hV⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L) ⟨_, hO2⟩
  have hk' : x ^ (12 * 2 ^ k) = 1 := by
    rw [pow_mul]
    simpa using congrArg Subtype.val hk
  have hdvd : orderOf x ∣ 3 * 2 ^ (k + 2) := by
    have := orderOf_dvd_of_pow_eq_one hk'
    have e : 12 * 2 ^ k = 3 * 2 ^ (k + 2) := by ring
    rwa [e] at this
  have hcop : Nat.Coprime (orderOf x) (2 ^ (k + 2)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hxo)
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd)

theorem factXThree_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    FactXThree := by
  intro G _ _ T L I h h3 hc t v₁ v₂ hd
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hx, hxo⟩
  refine mem_oPrimeResidualOf_of_pow Nat.prime_three (mem_oTwoUpper_of_odd hx hxo) (k := 1) ?_
  rw [pow_one]
  exact pow_three_eq_one_of_mem h37 h38 h h3 hc hd hx hxo

end CFSG.Quasithin.Vol2.Ch10.SecD
