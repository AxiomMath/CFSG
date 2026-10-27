module

public import CFSG.Quasithin.H13.A6S1372L76N3j
public import CFSG.Quasithin.H13.U3S1348S
public import CFSG.Quasithin.H13.L32NLem14413i

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

@[expose] def e1C3 (K : Subgroup G) : Subgroup G :=
  conjClosure (pCoreOf 2 (g1 T V)) (Subgroup.normalizer (S.V2 : Set G)) ⊔
    ((K ⊔ T) ⊓ Subgroup.centralizer (S.V2 : Set G))

theorem conj_inv_mul_v2 {q t : G} (hqz : q * S.z * q⁻¹ = S.z)
    (hq : q * S.v2 * q⁻¹ = S.z * S.v2) (ht : t * S.v2 * t⁻¹ = S.z * S.v2) :
    (q⁻¹ * t) * S.v2 * (q⁻¹ * t)⁻¹ = S.v2 := by
  have hzz : S.z * S.z = 1 := by rw [← pow_two]; exact S.z_sq
  have e1 : q⁻¹ * S.z * q = S.z := by
    calc q⁻¹ * S.z * q = q⁻¹ * (q * S.z * q⁻¹) * q := by rw [hqz]
      _ = S.z := by group
  have e2 : q⁻¹ * S.v2 * q = S.z * S.v2 := by
    calc q⁻¹ * S.v2 * q = q⁻¹ * (S.z * (S.z * S.v2)) * q := by
          rw [← mul_assoc S.z S.z S.v2, hzz, one_mul]
      _ = q⁻¹ * (S.z * (q * S.v2 * q⁻¹)) * q := by rw [hq]
      _ = (q⁻¹ * S.z * q) * S.v2 := by group
      _ = S.z * S.v2 := by rw [e1]
  calc (q⁻¹ * t) * S.v2 * (q⁻¹ * t)⁻¹ = q⁻¹ * (t * S.v2 * t⁻¹) * q := by group
    _ = q⁻¹ * (S.z * S.v2) * q := by rw [ht]
    _ = (q⁻¹ * S.z * q) * (q⁻¹ * S.v2 * q) := by group
    _ = S.z * (S.z * S.v2) := by rw [e1, e2]
    _ = S.v2 := by rw [← mul_assoc S.z S.z S.v2, hzz, one_mul]

variable {S} {H K : Subgroup G} (D : S.C3Hom H K)
include D

theorem C3Hom.C_le (hH : H ∈ S.Hz) : (K ⊔ T) ⊓ Subgroup.centralizer (S.V2 : Set G) ≤
    H ⊓ Subgroup.normalizer (K : Set G) :=
  inf_le_left.trans (D.KT_le hH)

theorem C3Hom.inX1_C (hH : H ∈ S.Hz) (c : ↥((K ⊔ T) ⊓ Subgroup.centralizer (S.V2 : Set G))) :
    SL3.InX1 (D.Φ (Subgroup.inclusion (D.C_le hH) c)) := by
  apply D.fix
  have h := Subgroup.mem_centralizer_iff.1 c.2.2 S.v2 S.v2_mem_V2
  have e : (c : G) * S.v2 * (c : G)⁻¹ * S.v2⁻¹ = 1 := by
    rw [← h]
    group
  show (c : G) * S.v2 * (c : G)⁻¹ * S.v2⁻¹ ∈ fsuV1 T V
  rw [e]
  exact Subgroup.one_mem _

@[expose] noncomputable def C3Hom.ψC (hH : H ∈ S.Hz) :
    ↥((K ⊔ T) ⊓ Subgroup.centralizer (S.V2 : Set G)) →* SL22.S2 :=
  A6L76N3.blockHom.comp ((D.Φ.comp (Subgroup.inclusion (D.C_le hH))).codRestrict SL3.X1
    fun c => D.inX1_C hH c)

theorem C3Hom.ψC_eq_one_iff (hH : H ∈ S.Hz)
    (c : ↥((K ⊔ T) ⊓ Subgroup.centralizer (S.V2 : Set G))) :
    D.ψC hH c = 1 ↔ A6L76N3.InR (D.Φ (Subgroup.inclusion (D.C_le hH) c)) := by
  constructor
  · intro h
    exact ⟨D.inX1_C hH c, congrArg (fun x : SL22.S2 => (x : Matrix (Fin 2) (Fin 2) (ZMod 2))) h⟩
  · intro h
    exact Subtype.ext h.2

theorem C3Hom.ψC_surjective (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (hhat : ¬ IsHatA6 L) (hH : H ∈ S.Hz) (hK : K ∈ cComp H) :
    Function.Surjective (D.ψC hH) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k₀, hk0K, hk0C, hk03, -, -, hk0R⟩ := D.exists_k0 hH
  obtain ⟨c₂, hc2T, hc2C, hc2R⟩ := D.exists_c2 h13314 h13315 hhat hH hK
  have hk0 : (k₀ : G) ∈ (K ⊔ T) ⊓ Subgroup.centralizer (S.V2 : Set G) :=
    ⟨Subgroup.mem_sup_left hk0K, hk0C⟩
  have hc2 : (c₂ : G) ∈ (K ⊔ T) ⊓ Subgroup.centralizer (S.V2 : Set G) :=
    ⟨Subgroup.mem_sup_right hc2T, hc2C⟩
  obtain ⟨r, hr⟩ : ∃ r, D.ψC hH ⟨k₀, hk0⟩ = r := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, D.ψC hH ⟨c₂, hc2⟩ = s := ⟨_, rfl⟩
  have hr3 : r ^ 3 = 1 := by
    have e : (⟨k₀, hk0⟩ : ↥((K ⊔ T) ⊓ Subgroup.centralizer (S.V2 : Set G))) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hk03)
    rw [← hr, ← map_pow, e]
    exact map_one _
  have hr1 : r ≠ 1 := fun h => hk0R ((D.ψC_eq_one_iff hH _).1 (hr.trans h))
  have hs1 : s ≠ 1 := fun h => hc2R ((D.ψC_eq_one_iff hH _).1 (hs.trans h))
  have hss : s * s = 1 := by
    obtain ⟨n, hn⟩ := S.h13.sylow.1 ⟨c₂, hc2T⟩
    have e : (⟨c₂, hc2⟩ : ↥((K ⊔ T) ⊓ Subgroup.centralizer (S.V2 : Set G))) ^ 2 ^ n = 1 :=
      Subtype.ext (by
        rw [Subgroup.coe_pow]
        simpa using congrArg Subtype.val hn)
    have hsn : s ^ 2 ^ n = 1 := by
      rw [← hs, ← map_pow, e]
      exact map_one _
    exact A6L76N3.mul_self_of_pow_two_pow hsn (A6L76N3.sl2_pow_six s)
  intro x
  rcases A6L76N3.sl2_word r s hr3 hr1 hss hs1 x with h | h | h | h | h | h <;> rw [h]
  · exact ⟨1, map_one _⟩
  · exact ⟨⟨k₀, hk0⟩, hr⟩
  · exact ⟨⟨k₀, hk0⟩ * ⟨k₀, hk0⟩, by rw [map_mul, hr]⟩
  · exact ⟨⟨c₂, hc2⟩, hs⟩
  · exact ⟨⟨c₂, hc2⟩ * ⟨k₀, hk0⟩, by rw [map_mul, hr, hs]⟩
  · exact ⟨⟨c₂, hc2⟩ * (⟨k₀, hk0⟩ * ⟨k₀, hk0⟩), by rw [map_mul, map_mul, hr, hs]⟩

theorem C3Hom.ψC_ker (hH : H ∈ S.Hz) : IsPGroup 2 ↥(D.ψC hH).ker := by
  rintro ⟨c, hc⟩
  have hR := (D.ψC_eq_one_iff hH c).1 hc
  have h2 := A6L76N3.mul_self_of_inR _ hR
  have hcc : (c : G) * c ∈ K ⊔ T := (K ⊔ T).mul_mem c.2.1 c.2.1
  have h3 : D.Φ ⟨(c : G) * c, D.KT_le hH hcc⟩ = 1 := by
    have e : (⟨(c : G) * c, D.KT_le hH hcc⟩ : ↥(H ⊓ Subgroup.normalizer (K : Set G))) =
        Subgroup.inclusion (D.C_le hH) c * Subgroup.inclusion (D.C_le hH) c := rfl
    rw [e, map_mul]
    exact h2
  obtain ⟨n, hn⟩ := D.ker_two hH hcc h3
  refine ⟨n + 1, Subtype.ext (Subtype.ext ?_)⟩
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [pow_succ', pow_mul, sq]
  exact hn

theorem C3Hom.d2C (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (hhat : ¬ IsHatA6 L) (hH : H ∈ S.Hz) (hK : K ∈ cComp H) :
    quasithinO2QuotientIso ((K ⊔ T) ⊓ Subgroup.centralizer (S.V2 : Set G)) SL22.S2 :=
  A6L76N3.quasithinO2QuotientIso_of_isPGroup_ker (D.ψC hH)
    (D.ψC_surjective h13314 h13315 hhat hH hK) (D.ψC_ker hH) A6L76N3.sl2_normal_two

theorem C3Hom.d2a (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (hhat : ¬ IsHatA6 L) (hH : H ∈ S.Hz) (hK : K ∈ cComp H) :
    T ≤ S.e1C3 K ∧ L₁Of L S.V2 ≤ S.e1C3 K ∧
      S.e1C3 K ≤ Subgroup.normalizer (S.V2 : Set G) ∧
      quasithinO2QuotientIso (S.e1C3 K) (SL22.S2 × SL22.S2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hI1, hI2, hI3, hI4, -, -, -, -, hI9⟩ := S.lemma13_5_4 h13314 h13315 (L₁Of L S.V2)
    (fun h => absurd h hhat) (fun _ => rfl)
  set I₂ := conjClosure (pCoreOf 2 (g1 T V)) (Subgroup.normalizer (S.V2 : Set G)) with hI₂
  set C := (K ⊔ T) ⊓ Subgroup.centralizer (S.V2 : Set G) with hC
  have hE : S.e1C3 K = I₂ ⊔ C := rfl
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  have hTG1 : T ≤ g1 T V := hg1 ▸ hTH.trans hH.2.1
  have hzT : ∀ t ∈ T, t * S.z * t⁻¹ = S.z := by
    intro t ht
    have h1 : t ∈ S.G1 := hH.2.1 (hTH ht)
    rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
    rw [h1, mul_inv_cancel_right]
  have hO2T : pCoreOf 2 (g1 T V) ≤ T := pCoreOf_le_of_sylow S.h13.sylow hTG1
  have hL2N : L₁Of L S.V2 ≤ Subgroup.normalizer (S.V2 : Set G) :=
    (oTwoRes_le _).trans inf_le_right
  have hL2I : L₁Of L S.V2 ≤ I₂ := by
    rw [hI2]
    exact le_sup_left
  have hI2N : I₂ ≤ Subgroup.normalizer (S.V2 : Set G) := by
    rw [hI2]
    exact sup_le hL2N (hO2T.trans S.T_le_normalizer_V2)
  have hCN : C ≤ Subgroup.normalizer (S.V2 : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hEN : S.e1C3 K ≤ Subgroup.normalizer (S.V2 : Set G) := by
    rw [hE]
    exact sup_le hI2N hCN
  have hCI : C ≤ Subgroup.normalizer (I₂ : Set G) := hCN.trans hI1
  have hcoe : (S.e1C3 K : Set G) = (I₂ : Set G) * C := by
    rw [hE]
    exact Subgroup.coe_mul_of_right_le_normalizer_left I₂ C hCI
  have hO2I2T : pCoreOf 2 I₂ ≤ T := by
    have h1 : pCoreOf 2 I₂ ≤ pCoreOf 2 (I₂ ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 I₂).trans le_sup_left)
        (sup_le (le_normalizer_pCoreOf 2 I₂) ((S.T_le_normalizer_V2.trans hI1).trans
          (normalizer_le_normalizer_pCoreOf 2 I₂)))
        (pCoreOf_isPGroup 2 I₂)
    exact h1.trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)
  obtain ⟨q₀, hq₀G, hq₀C⟩ := IsConcreteLE.not_le_iff_exists.1 hI9
  have hq₀T : q₀ ∈ T := hO2T hq₀G
  have hq₀I : q₀ ∈ I₂ := by
    rw [hI2]
    exact Subgroup.mem_sup_right hq₀G
  have hq₀v : q₀ * S.v2 * q₀⁻¹ = S.z * S.v2 := by
    rcases S.conj_v2_cases (S.T_le_normalizer_V2 hq₀T) (hzT q₀ hq₀T) with h | h
    · exact absurd (S.mem_centralizer_V2_of (hzT q₀ hq₀T) h) hq₀C
    · exact h
  have hTE : T ≤ S.e1C3 K := by
    intro t ht
    rcases S.conj_v2_cases (S.T_le_normalizer_V2 ht) (hzT t ht) with h | h
    · rw [hE]
      exact Subgroup.mem_sup_right ⟨Subgroup.mem_sup_right ht, S.mem_centralizer_V2_of (hzT t ht) h⟩
    · have hc : q₀⁻¹ * t ∈ T := T.mul_mem (T.inv_mem hq₀T) ht
      have hcC : q₀⁻¹ * t ∈ C := ⟨Subgroup.mem_sup_right hc,
        S.mem_centralizer_V2_of (hzT _ hc) (S.conj_inv_mul_v2 (hzT q₀ hq₀T) hq₀v h)⟩
      rw [show t = q₀ * (q₀⁻¹ * t) by group, hE]
      exact (I₂ ⊔ C).mul_mem (Subgroup.mem_sup_left hq₀I) (Subgroup.mem_sup_right hcC)
  have hEC : S.e1C3 K ⊓ Subgroup.centralizer (S.V2 : Set G) = C := by
    refine le_antisymm (fun e he => ?_) (le_inf (hE ▸ le_sup_right) inf_le_right)
    have he1 : e ∈ (I₂ : Set G) * C := by
      rw [← hcoe]
      exact he.1
    obtain ⟨i, hi, c, hc, rfl⟩ := he1
    have hiC : i ∈ Subgroup.centralizer (S.V2 : Set G) := by
      have e : i = (i * c) * c⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ he.2 (Subgroup.inv_mem _ hc.2)
    have hiO : i ∈ pCoreOf 2 I₂ := by
      rw [← hI3]
      exact ⟨hi, hiC⟩
    exact C.mul_mem ⟨Subgroup.mem_sup_right (hO2I2T hiO), hiC⟩ hc
  have hCE : C ≤ S.e1C3 K := hE ▸ le_sup_right
  have hIE : I₂ ≤ S.e1C3 K := hE ▸ le_sup_left
  have hO2I2E : pCoreOf 2 I₂ ≤ pCoreOf 2 (S.e1C3 K) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 I₂).trans hIE)
      (hEN.trans (hI1.trans (normalizer_le_normalizer_pCoreOf 2 I₂))) (pCoreOf_isPGroup 2 I₂)
  have hAB : I₂ ⊓ C ≤ pCoreOf 2 (S.e1C3 K) := fun x hx => hO2I2E (by
    rw [← hI3]
    exact ⟨hx.1, hx.2.2⟩)
  have hOA : pCoreOf 2 I₂ = I₂ ⊓ pCoreOf 2 (S.e1C3 K) :=
    le_antisymm (le_inf (pCoreOf_le 2 I₂) hO2I2E) (U3.inf_pCoreOf_le_pCoreOf_of_le hIE)
  have hO2ET : pCoreOf 2 (S.e1C3 K) ≤ T := pCoreOf_le_of_sylow S.h13.sylow hTE
  have hO2EC : pCoreOf 2 (S.e1C3 K) ≤ Subgroup.centralizer (S.V2 : Set G) := by
    intro n hn
    have hnT := hO2ET hn
    rcases S.conj_v2_cases (S.T_le_normalizer_V2 hnT) (hzT n hnT) with h | h
    · exact S.mem_centralizer_V2_of (hzT n hnT) h
    · exfalso
      obtain ⟨ℓ, hℓL2, -, hℓz⟩ := S.exists_L2_three hhat
      have hℓI : ℓ ∈ I₂ := hL2I hℓL2
      have hℓN : ℓ ∈ Subgroup.normalizer (S.V2 : Set G) := hL2N hℓL2
      have hc1 : n * ℓ * n⁻¹ * ℓ⁻¹ ∈ pCoreOf 2 (S.e1C3 K) := by
        have h1 : ℓ * n⁻¹ * ℓ⁻¹ ∈ pCoreOf 2 (S.e1C3 K) :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (S.e1C3 K) (hIE hℓI)) _).mp
            ((pCoreOf 2 (S.e1C3 K)).inv_mem hn)
        rw [show n * ℓ * n⁻¹ * ℓ⁻¹ = n * (ℓ * n⁻¹ * ℓ⁻¹) by group]
        exact (pCoreOf 2 (S.e1C3 K)).mul_mem hn h1
      have hc2 : n * ℓ * n⁻¹ * ℓ⁻¹ ∈ I₂ := by
        have h1 : n * ℓ * n⁻¹ ∈ I₂ :=
          (Subgroup.mem_normalizer_iff.mp (hI1 (S.T_le_normalizer_V2 hnT)) ℓ).mp hℓI
        exact I₂.mul_mem h1 (I₂.inv_mem hℓI)
      have hcC : n * ℓ * n⁻¹ * ℓ⁻¹ ∈ Subgroup.centralizer (S.V2 : Set G) := by
        have h1 : n * ℓ * n⁻¹ * ℓ⁻¹ ∈ pCoreOf 2 I₂ := by
          rw [hOA]
          exact ⟨hc2, hc1⟩
        rw [← hI3] at h1
        exact h1.2
      have hzV2 : S.z ∈ S.V2 := S.V1_le_V2 (S.mem_V1_iff.2 (Or.inr rfl))
      have hwV2 : ℓ * S.z * ℓ⁻¹ ∈ S.V2 := (Subgroup.mem_normalizer_iff.mp hℓN _).mp hzV2
      have hnw : n * (ℓ * S.z * ℓ⁻¹) * n⁻¹ = ℓ * S.z * ℓ⁻¹ := by
        have e1 : n * (ℓ * S.z * ℓ⁻¹) * n⁻¹ = (n * ℓ * n⁻¹ * ℓ⁻¹) *
            (ℓ * (n * S.z * n⁻¹) * ℓ⁻¹) * (n * ℓ * n⁻¹ * ℓ⁻¹)⁻¹ := by group
        rw [e1, hzT n hnT]
        have h1 := Subgroup.mem_centralizer_iff.1 hcC _ hwV2
        rw [← h1]
        group
      have hzz : S.z * S.z = 1 := by rw [← pow_two]; exact S.z_sq
      rcases S.mem_V1_or_of_mem_V2 S.v2_mem_V2 S.v2_not_mem_V1 hwV2 with h1 | h1
      · rcases S.mem_V1_iff.1 h1 with h2 | h2
        · apply S.z_ne_one
          calc S.z = ℓ⁻¹ * (ℓ * S.z * ℓ⁻¹) * ℓ := by group
            _ = 1 := by rw [h2]; group
        · exact hℓz h2
      · rcases S.mem_V1_iff.1 h1 with h2 | h2
        · have hw : ℓ * S.z * ℓ⁻¹ = S.v2 := mul_inv_eq_one.1 h2
          rw [hw, h] at hnw
          apply S.z_ne_one
          calc S.z = S.z * S.v2 * S.v2⁻¹ := by group
            _ = 1 := by rw [hnw, mul_inv_cancel]
        · have hw : ℓ * S.z * ℓ⁻¹ = S.z * S.v2 := mul_inv_eq_iff_eq_mul.1 h2
          rw [hw] at hnw
          have e2 : n * (S.z * S.v2) * n⁻¹ = S.v2 := by
            calc n * (S.z * S.v2) * n⁻¹ = (n * S.z * n⁻¹) * (n * S.v2 * n⁻¹) := by group
              _ = S.v2 := by rw [hzT n hnT, h, ← mul_assoc, hzz, one_mul]
          rw [e2] at hnw
          apply S.z_ne_one
          calc S.z = S.z * S.v2 * S.v2⁻¹ := by group
            _ = 1 := by rw [← hnw, mul_inv_cancel]
  have hENC : S.e1C3 K ≤ Subgroup.normalizer (C : Set G) := by
    intro e he
    have h1 : e ∈ Subgroup.normalizer
        ((S.e1C3 K ⊓ Subgroup.centralizer (S.V2 : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf_of (Subgroup.le_normalizer he)
        (normalizes_of_conj_mem (X := S.e1C3 K) (fun g hg y hy => conj_centralizer_mem (hEN hg) hy)
          he)
    rwa [hEC] at h1
  have hOB : pCoreOf 2 C = pCoreOf 2 (S.e1C3 K) := by
    refine le_antisymm (U3.pCoreOf_le_pCoreOf hCE hENC) fun x hx => ?_
    have hxC : x ∈ C := by
      rw [← hEC]
      exact ⟨pCoreOf_le 2 _ hx, hO2EC hx⟩
    exact U3.inf_pCoreOf_le_pCoreOf_of_le hCE ⟨hxC, hx⟩
  have hdec : ∀ e ∈ S.e1C3 K, ∃ a ∈ I₂, ∃ b ∈ C, e = a * b := by
    intro e he
    have he1 : e ∈ (I₂ : Set G) * C := by
      rw [← hcoe]
      exact he
    obtain ⟨a, ha, b, hb, rfl⟩ := he1
    exact ⟨a, ha, b, hb, rfl⟩
  have hA : quasithinO2QuotientIso I₂ SL22.S2 := by
    obtain ⟨e⟩ := hI4
    exact (H13.quasithinO2QuotientIso_iff I₂ _).2 ⟨e.trans L14413.s3Equiv'⟩
  refine ⟨hTE, hL2I.trans hIE, hEN, ?_⟩
  exact U3.quasithinO2QuotientIso_prod hIE hCE (hEN.trans hI1) hENC hdec hAB hA
    (D.d2C h13314 h13315 hhat hH hK) hOA hOB

end Setting4

end CFSG.Quasithin.H13.A6
