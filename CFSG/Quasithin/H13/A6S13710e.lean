module

public import CFSG.Quasithin.H13.A6S13710c

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem K4L_cases : ∀ κ ∈ K4L, κ = 1 ∨ ∃ τ ∈ [swap (1 : Fin 6) 2 * swap 2 3,
    swap (0 : Fin 6) 1 * swap 1 3, swap (0 : Fin 6) 3 * swap 3 2],
    Perm.sign τ = 1 ∧ τ 4 = 4 ∧ τ 5 = 5 ∧ τ ^ 3 = 1 ∧ (swap 0 1 * swap 1 2) * τ = κ := by
  decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_L1_rho (hhat : ¬ IsHatA6 L) {σ : Perm (Fin 6)}
    (hs : Perm.sign σ = 1) (h4 : σ 4 = 4) (h5 : σ 5 = 5) (h3 : σ ^ 3 = 1) :
    ∃ x : ↥(Subgroup.normalizer (V : Set G)), (x : G) ∈ S.L1 ∧ S.frame.ρ x = σ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hlL, hρl⟩ := (S.frame.image_L σ).2 (Equiv.Perm.mem_alternatingGroup.2 hs)
  have hl3 : ((l ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
      L ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨by simpa using L.pow_mem hlL 3, (S.rho_eq_one_iff _).1 ?_⟩
    rw [map_pow, hρl, h3]
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, S.inf_centralizer_le_pCoreOf hhat hl3⟩
  have hk' : ((l : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hρx : S.frame.ρ (l ^ 4 ^ k) = σ := by
    rw [map_pow, hρl, pow_four_pow_of_cube h3]
  refine ⟨l ^ 4 ^ k, ?_, hρx⟩
  have hxL : ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ L := by
    simpa using L.pow_mem hlL (4 ^ k)
  have hx3 : ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G) ^ 3 = 1 := by
    have e : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
    simp only [SubgroupClass.coe_pow]
    rw [← pow_mul, mul_comm, pow_mul, e, pow_mul, hk', one_pow]
  have hfix := fix_e0123_of (S.frame.ρ (l ^ 4 ^ k)) (by rw [hρx]; exact h4) (by rw [hρx]; exact h5)
  have hz : ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G) * S.z *
      ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ = S.z := by
    refine (S.conj_eq_iff _ ⟨S.z, S.z_mem_V⟩).2 ?_
    rw [S.psi_z]
    exact Subtype.ext hfix
  have hN : ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
      Subgroup.normalizer (fsuV1 T V : Set G) := by
    rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
    calc ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G) * S.z =
        ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G) * S.z *
          ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ *
            ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G) := by group
      _ = S.z * ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G) := by rw [hz]
  exact Subgroup.subset_closure ⟨⟨hxL, hN⟩, 3, by decide, hx3⟩

theorem rho_O2L1_eq_K4 (hhat : ¬ IsHatA6 L) :
    S.rhoO2L1.range = K4sub := by
  refine le_antisymm ?_ fun κ hκ => ?_
  · intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    exact S.rho_O2L1_mem_K4 x.2 _
  · rcases K4L_cases κ hκ with rfl | ⟨τ, -, hs, h4, h5, h3, hτ⟩
    · exact Subgroup.one_mem _
    · obtain ⟨x, hxL, hρx⟩ := S.exists_L1_rho hhat hs h4 h5 h3
      have hc := S.cL1_mem hhat
      have hmem : ((S.cL1 hhat * x : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
          pCoreOf 2 S.L1 :=
        S.mem_pCoreOf_L1_of_K4 hhat (S.L1.mul_mem hc hxL)
          (by rw [map_mul, S.cL1_rho, hρx, hτ]; exact hκ)
      refine MonoidHom.mem_range.2 ⟨⟨_, hmem⟩, ?_⟩
      show S.frame.ρ (S.cL1 hhat * x) = κ
      rw [map_mul, S.cL1_rho, hρx, hτ]

theorem relIndex_O2L1_eq_four (hhat : ¬ IsHatA6 L) :
    (pCoreOf 2 S.L1 ⊓ ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))).relIndex (pCoreOf 2 S.L1) =
      4 := by
  rw [S.relIndex_O2L1_eq, S.rho_O2L1_eq_K4 hhat, card_K4sub]

namespace Conf

variable {S}

theorem nu_O2L1_eq (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (C : S.Conf H) (hhat : ¬ IsHatA6 L)
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14) :
    ∃ c₁ : ↥(Subgroup.normalizer (V : Set G)), (c₁ : G) ∈ S.L1 ∧ (c₁ : G) ^ 3 = 1 ∧
      (c₁ : G) ∉ pCoreOf 2 S.L1 ∧
      nu (c₁ : G) (pCoreOf 2 S.L1) =
        16 * ((C.VHg ⊓ pCoreOf 2 (L ⊔ T) ⊓ pCoreOf 2 H).relIndex
          (C.VHg ⊓ pCoreOf 2 (L ⊔ T))) ^ 2 := by
  obtain ⟨c₁, hc₁L, hc₁3, hρc₁, hν⟩ := C.exists_c1 hNS h13315 h1356two hH hab hhat
  refine ⟨c₁, hc₁L, hc₁3, ?_, ?_⟩
  · intro h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, h⟩
    have hk' : (c₁ : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf (c₁ : G) ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc₁3) (orderOf_dvd_of_pow_eq_one hk')
    have h2 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
    rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
    have h4 : c₁ = 1 := Subtype.ext h1
    rw [h4, map_one] at hρc₁
    exact absurd hρc₁.symm (by decide)
  · rw [S.nu_O2L1_eq_mul hhat c₁ hc₁L hc₁3 hρc₁, S.relIndex_O2L1_eq_four hhat, hν,
      C.nu_cQ hNS h13315 h1356two hH hab hhat, ← C.A_eq hNS h13315 h1356two hH hab hhat,
      C.A_inf_QH hNS h13315 h1356two hH hab hhat hna h13314]
    ring

end Conf

end Setting4

end CFSG.Quasithin.H13.A6
