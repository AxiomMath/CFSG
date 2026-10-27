module

public import CFSG.RankThree.GF2n.Parrott.Section5HbadUTSigma

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem exists_conj_mem_of_qH_eq_utA
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {y : G} (hyH : y ∈ H z) (hy : orderOf y = 2)
    (hq : qH (z := z) D ⟨y, hyH⟩ = uA * tA)
    (B : Subgroup G) (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hcard : Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B) :
    ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y := by
  classical
  have hy2 : y * y = 1 := by
    have h' := pow_orderOf_eq_one y
    rw [hy, pow_two] at h'
    exact h'
  have hz2 : z * z = 1 := by
    have h' := pow_orderOf_eq_one z
    rw [h.1, pow_two] at h'
    exact h'
  have hzy : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyH
  have hzz : z ∈ centerIn (J z) := z_mem_centerIn_J h
  by_cases hcenter : ∀ n ∈ B, n ∈ J z → n ∈ centerIn (J z)
  · have h32 := card_le_of_forall_mem_centerIn_of_utA D hyH hy2 hq h P hP B hBC hBn hzB hcenter
    have h64 := card_J_inf_centralizer_of_utA D hyH hy2 hq h P hP
    omega
  · push Not at hcenter
    obtain ⟨n, hnB, hnJ, hnZ⟩ := hcenter
    have hny : n * y = y * n :=
      Subgroup.mem_centralizer_singleton_iff.mp (mem_inf.mp (hBC hnB)).2
    obtain ⟨k, hkJ, ζ, hζZ, hn_eq, hxZ⟩ :=
      exists_eq_conj_mul_inv_mul_of_utA D hyH hy2 hq h P hP hnJ hny hnZ
    have hBkζ : k * y * k⁻¹ * y⁻¹ * ζ ∈ B := by
      rw [← hn_eq]
      exact hnB
    have hxmem := conj_mul_inv_mul_mem_of_utA D hyH hy2 hq h P hP B hBn hkJ hζZ hBkζ
    by_cases hf : b (hbadCoord h P k) (((rhoA hbadS : GL8) : Mat8) *ᵥ
        (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P k + hbadCoord h P k)) = 0
    ·
      have hxB : k * y * k⁻¹ * y⁻¹ ∈ B := by
        have h' := hxmem
        rw [if_pos hf, mul_one] at h'
        exact h'
      refine ⟨k, J_le_H hkJ, ?_, ?_⟩
      · rw [show k * y * k⁻¹ = (k * y * k⁻¹ * y⁻¹) * y by group]
        exact B.mul_mem hxB hyB
      · intro heq
        have hx1 : k * y * k⁻¹ * y⁻¹ = 1 := by
          rw [heq, mul_inv_cancel]
        exact hxZ (hx1 ▸ (centerIn (J z)).one_mem)
    ·
      have hf1 : b (hbadCoord h P k) (((rhoA hbadS : GL8) : Mat8) *ᵥ
          (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P k + hbadCoord h P k)) = 1 := by
        have hall : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
        exact hall _ hf
      obtain ⟨hb_ne, hb2⟩ := spin_hbadA (hbadCoord h P k) hf1
      have hBkz : k * y * k⁻¹ * y⁻¹ * z ∈ B := by
        have h' := hxmem
        rw [if_neg hf] at h'
        exact h'
      obtain ⟨a, hqa, ζ₁, hζ₁Z, hay⟩ := exists_lift_hbadA_of_utA D hyH hy2 hq h P hP
      have key : (∃ u ∈ H z, u * y * u⁻¹ = y * z) →
          ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y := by
        rintro ⟨u, huH, huy⟩
        have hzk : z * k = k * z :=
          (Subgroup.mem_centralizer_iff.mp (z_centralizes_J h) k hkJ).symm
        have hzk' : z * k⁻¹ = k⁻¹ * z := ((commute_iff_eq z k).mpr hzk).inv_right
        have hcalc : k * u * y * (k * u)⁻¹ = (k * y * k⁻¹ * y⁻¹ * z) * y := by
          calc k * u * y * (k * u)⁻¹
              = k * (u * y * u⁻¹) * k⁻¹ := by group
            _ = k * (y * z) * k⁻¹ := by rw [huy]
            _ = k * y * (z * k⁻¹) := by group
            _ = k * y * (k⁻¹ * z) := by rw [hzk']
            _ = k * y * k⁻¹ * z := by group
            _ = k * y * k⁻¹ * y⁻¹ * (y * z) := by group
            _ = k * y * k⁻¹ * y⁻¹ * (z * y) := by rw [hzy]
            _ = (k * y * k⁻¹ * y⁻¹ * z) * y := by group
        refine ⟨k * u, (H z).mul_mem (J_le_H hkJ) huH, ?_, ?_⟩
        · rw [hcalc]
          exact B.mul_mem hBkz hyB
        · intro heq
          have h1 : (k * y * k⁻¹ * y⁻¹ * z) * y = y := by
            rw [← hcalc]
            exact heq
          have h2 : k * y * k⁻¹ * y⁻¹ * z = 1 :=
            mul_right_cancel (h1.trans (one_mul y).symm)
          have h3 : k * y * k⁻¹ * y⁻¹ = z := by
            calc k * y * k⁻¹ * y⁻¹
                = k * y * k⁻¹ * y⁻¹ * (z * z) := by rw [hz2, mul_one]
              _ = (k * y * k⁻¹ * y⁻¹ * z) * z := by group
              _ = 1 * z := by rw [h2]
              _ = z := one_mul z
          exact hxZ (h3 ▸ hzz)
      by_cases hzp : ζ₁ ∈ Subgroup.zpowers z
      · rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two h.1 hzp with hζ1 | hζ1
        ·
          have hay1 : (a : G) * y * (a : G)⁻¹ = y := by rw [hay, hζ1, mul_one]
          have hayy : (a : G) * y = y * (a : G) := by
            calc (a : G) * y = ((a : G) * y * (a : G)⁻¹) * (a : G) := by group
              _ = y * (a : G) := by rw [hay1]
          have haC : (a : G) ∈ H z ⊓ centralizer ({y} : Set G) :=
            mem_inf.mpr ⟨a.2, Subgroup.mem_centralizer_singleton_iff.mpr hayy⟩
          have hBconj := hBn (a : G) haC (k * y * k⁻¹ * y⁻¹ * z) hBkz
          have hk'J : (a : G) * k * (a : G)⁻¹ ∈ J z := H_conj_mem_J a hkJ
          have hx'J : ((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹ ∈
              J z :=
            (hbadCoord_conj_mul_inv_of_utA D hyH hq h P hP hk'J).1
          have hzconj : (a : G) * z * (a : G)⁻¹ = z :=
            Commute.mul_inv_cancel
              ((commute_iff_eq (a : G) z).mpr (Subgroup.mem_centralizer_singleton_iff.mp a.2))
          have hconjxk : (a : G) * (k * y * k⁻¹ * y⁻¹) * (a : G)⁻¹ =
              ((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹ := by
            calc (a : G) * (k * y * k⁻¹ * y⁻¹) * (a : G)⁻¹
                = ((a : G) * k * (a : G)⁻¹) * ((a : G) * y * (a : G)⁻¹) *
                    ((a : G) * k * (a : G)⁻¹)⁻¹ * ((a : G) * y * (a : G)⁻¹)⁻¹ := by group
              _ = ((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹ := by
                    rw [hay1]
          have heqB : (a : G) * (k * y * k⁻¹ * y⁻¹ * z) * (a : G)⁻¹ =
              ((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹ * z := by
            calc (a : G) * (k * y * k⁻¹ * y⁻¹ * z) * (a : G)⁻¹
                = ((a : G) * (k * y * k⁻¹ * y⁻¹) * (a : G)⁻¹) *
                    ((a : G) * z * (a : G)⁻¹) := by group
              _ = ((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹ * z := by
                    rw [hconjxk, hzconj]
          have hBk'z : ((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹ * z ∈
              B := heqB ▸ hBconj
          have hzx' : z * (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) =
              (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) * z :=
            (Subgroup.mem_centralizer_iff.mp (z_centralizes_J h) _ hx'J).symm
          have hp_eq : (k * y * k⁻¹ * y⁻¹ * z) *
              (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹ * z) =
              (k * y * k⁻¹ * y⁻¹) *
                (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) := by
            calc (k * y * k⁻¹ * y⁻¹ * z) *
                  (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹ * z)
                = (k * y * k⁻¹ * y⁻¹) *
                    (z * (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)) *
                    z := by group
              _ = (k * y * k⁻¹ * y⁻¹) *
                    ((((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) * z) *
                    z := by rw [hzx']
              _ = (k * y * k⁻¹ * y⁻¹) *
                    ((((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)) *
                    (z * z) := by group
              _ = (k * y * k⁻¹ * y⁻¹) *
                    (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) := by
                    rw [hz2, mul_one]
          have hp : (k * y * k⁻¹ * y⁻¹) *
              (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) ∈ B := by
            rw [← hp_eq]
            exact B.mul_mem hBkz hBk'z
          have hk₂J : k * ((a : G) * k * (a : G)⁻¹) ∈ J z := (J z).mul_mem hkJ hk'J
          have hxkJ : k * y * k⁻¹ * y⁻¹ ∈ J z :=
            (hbadCoord_conj_mul_inv_of_utA D hyH hq h P hP hkJ).1
          have hfix : ∀ v : V,
              ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ
                (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ v) = v := by
            intro v
            rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, utA_mul_self, map_one,
              Units.val_one, Matrix.one_mulVec]
          have hfixXK : ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P (k * y * k⁻¹ * y⁻¹) =
              hbadCoord h P (k * y * k⁻¹ * y⁻¹) := by
            rw [(hbadCoord_conj_mul_inv_of_utA D hyH hq h P hP hkJ).2, Matrix.mulVec_add, hfix,
              add_comm]
          have hfixXKP :
              ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ
                hbadCoord h P (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) =
              hbadCoord h P (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) := by
            rw [(hbadCoord_conj_mul_inv_of_utA D hyH hq h P hP hk'J).2, Matrix.mulVec_add, hfix,
              add_comm]
          have hky : k * y * k⁻¹ * y⁻¹ * y = y * (k * y * k⁻¹ * y⁻¹) :=
            (commute_iff_of_utA D hyH hy2 hq h P hP hxkJ).mpr hfixXK
          have hkpy : (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) * y =
              y * (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) :=
            (commute_iff_of_utA D hyH hy2 hq h P hP hx'J).mpr hfixXKP
          have hcomm_x : (k * y * k⁻¹ * y⁻¹) *
              (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) =
              (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) *
                (k * y * k⁻¹ * y⁻¹) :=
            commute_of_utA D hyH hy2 hq h P hP hxkJ hx'J hky hkpy
          have he_zp : k *
              (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) * k⁻¹ *
              (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)⁻¹ ∈
              Subgroup.zpowers z :=
            commutator_mem_zpowers_z h hkJ hx'J
          have he_Z : k *
              (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) * k⁻¹ *
              (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)⁻¹ ∈
              centerIn (J z) :=
            Subgroup.zpowers_le.mpr hzz he_zp
          have hp_comm :
              (k * (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) * k⁻¹ *
                (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)⁻¹) *
                ((k * y * k⁻¹ * y⁻¹) *
                  (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)) =
              ((k * y * k⁻¹ * y⁻¹) *
                  (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)) *
                (k * (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) * k⁻¹ *
                  (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)⁻¹) :=
            (Subgroup.mem_centralizer_iff.mp (mem_inf.mp he_Z).2 _ ((J z).mul_mem hxkJ hx'J)).symm
          have hx₂_eq :
              (k * ((a : G) * k * (a : G)⁻¹)) * y * (k * ((a : G) * k * (a : G)⁻¹))⁻¹ * y⁻¹ =
                (k * (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) * k⁻¹ *
                  (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)⁻¹) *
                  ((k * y * k⁻¹ * y⁻¹) *
                    (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)) := by
            calc (k * ((a : G) * k * (a : G)⁻¹)) * y *
                  (k * ((a : G) * k * (a : G)⁻¹))⁻¹ * y⁻¹
                = k * (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) *
                    k⁻¹ * (k * y * k⁻¹ * y⁻¹) := by group
              _ = (k * (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) *
                    k⁻¹ *
                    (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)⁻¹) *
                    ((((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) *
                      (k * y * k⁻¹ * y⁻¹)) := by group
              _ = (k * (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) *
                    k⁻¹ *
                    (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)⁻¹) *
                    ((k * y * k⁻¹ * y⁻¹) *
                      (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)) := by
                    rw [hcomm_x]
          have hB2 : (k * ((a : G) * k * (a : G)⁻¹)) * y *
              (k * ((a : G) * k * (a : G)⁻¹))⁻¹ * y⁻¹ *
              (k * (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) * k⁻¹ *
                (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)⁻¹)⁻¹ ∈ B := by
            have h1 : (k * ((a : G) * k * (a : G)⁻¹)) * y *
                  (k * ((a : G) * k * (a : G)⁻¹))⁻¹ * y⁻¹ *
                  (k * (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) * k⁻¹ *
                    (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹)⁻¹)⁻¹ =
                (k * y * k⁻¹ * y⁻¹) *
                  (((a : G) * k * (a : G)⁻¹) * y * ((a : G) * k * (a : G)⁻¹)⁻¹ * y⁻¹) := by
              rw [hx₂_eq, hp_comm]
              group
            rw [h1]
            exact hp
          have hres := conj_mul_inv_mul_mem_of_utA D hyH hy2 hq h P hP B hBn hk₂J
            ((centerIn (J z)).inv_mem he_Z) hB2
          have hm2 : hbadCoord h P (k * ((a : G) * k * (a : G)⁻¹)) =
              hbadCoord h P k + ((rhoA hbadA : GL8) : Mat8) *ᵥ hbadCoord h P k := by
            rw [hbadCoord_mul h P hkJ hk'J, hbadCoord_conj D h P hP a.2 hkJ]
            rw [show qH (z := z) D ⟨(a : G), a.2⟩ = hbadA from hqa]
          have hif : (if b (hbadCoord h P (k * ((a : G) * k * (a : G)⁻¹)))
                (((rhoA hbadS : GL8) : Mat8) *ᵥ
                  (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ
                    hbadCoord h P (k * ((a : G) * k * (a : G)⁻¹)) +
                    hbadCoord h P (k * ((a : G) * k * (a : G)⁻¹)))) = 0 then (1 : G) else z) = 1 := by
            rw [hm2]
            rw [if_pos hb2]
          have hxB₂ : (k * ((a : G) * k * (a : G)⁻¹)) * y *
              (k * ((a : G) * k * (a : G)⁻¹))⁻¹ * y⁻¹ ∈ B := by
            have h' := hres
            rw [hif, mul_one] at h'
            exact h'
          have hne : (k * ((a : G) * k * (a : G)⁻¹)) * y *
              (k * ((a : G) * k * (a : G)⁻¹))⁻¹ * y⁻¹ ≠ 1 := by
            intro h1
            have hcoord := (hbadCoord_conj_mul_inv_of_utA D hyH hq h P hP hk₂J).2
            rw [h1] at hcoord
            have hz0 : hbadCoord h P (1 : G) = 0 :=
              (hbadCoord_eq_zero_iff h P (one_mem (J z))).mpr ((centerIn (J z)).one_mem)
            rw [hz0] at hcoord
            rw [hm2] at hcoord
            rw [add_comm] at hcoord
            exact hb_ne hcoord.symm
          refine ⟨k * ((a : G) * k * (a : G)⁻¹), J_le_H hk₂J, ?_, ?_⟩
          · rw [show (k * ((a : G) * k * (a : G)⁻¹)) * y *
                (k * ((a : G) * k * (a : G)⁻¹))⁻¹ =
                ((k * ((a : G) * k * (a : G)⁻¹)) * y *
                  (k * ((a : G) * k * (a : G)⁻¹))⁻¹ * y⁻¹) * y by group]
            exact B.mul_mem hxB₂ hyB
          · intro heq
            exact hne (by
              calc (k * ((a : G) * k * (a : G)⁻¹)) * y *
                    (k * ((a : G) * k * (a : G)⁻¹))⁻¹ * y⁻¹
                  = y * y⁻¹ := by rw [heq]
                _ = 1 := mul_inv_cancel y)
        ·
          exact key ⟨a, a.2, by rw [hay, hζ1]⟩
      ·
        have hζ₁z : ζ₁ ∉ Subgroup.zpowers z := hzp
        have hconjζ : (a : G) * ζ₁ * (a : G)⁻¹ = z * ζ₁ := by
          have ha_not : qH (z := z) D a ∉
              QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
            rw [hqa]
            exact hbadA_not_mem_QP45
          exact conj_eq_z_mul_of_not_mem_QP45 D h hZ ha_not hζ₁Z hζ₁z
        have hζ₁y : ζ₁ * y = y * ζ₁ := commute_of_mem_centerIn_of_utA D hyH hq h hζ₁Z
        have hζ₁2 : ζ₁ * ζ₁ = 1 := centerIn_J_sq h hζ₁Z
        have hzζ : ζ₁ * z = z * ζ₁ :=
          (Subgroup.mem_centralizer_iff.mp (mem_inf.mp hζ₁Z).2 z (z_mem_J h)).symm
        have hua : ((a : G) * (a : G)) * y * ((a : G) * (a : G))⁻¹ = y * z := by
          calc (a : G) * (a : G) * y * ((a : G) * (a : G))⁻¹
              = (a : G) * ((a : G) * y * (a : G)⁻¹) * (a : G)⁻¹ := by group
            _ = (a : G) * (y * ζ₁) * (a : G)⁻¹ := by rw [hay]
            _ = ((a : G) * y * (a : G)⁻¹) * ((a : G) * ζ₁ * (a : G)⁻¹) := by group
            _ = (y * ζ₁) * (z * ζ₁) := by rw [hay, hconjζ]
            _ = y * z := by
                calc (y * ζ₁) * (z * ζ₁) = y * (ζ₁ * z) * ζ₁ := by group
                  _ = y * (z * ζ₁) * ζ₁ := by rw [hzζ]
                  _ = y * z * (ζ₁ * ζ₁) := by group
                  _ = y * z := by rw [hζ₁2, mul_one]
        exact key ⟨(a : G) * (a : G), (H z).mul_mem a.2 a.2, hua⟩

omit [Finite G]
  in
private theorem conj_inv_mul_comm {g x y : G} (h : x * (g * y * g⁻¹) = g * y * g⁻¹ * x) :
    g⁻¹ * x * g⁻¹⁻¹ * y = y * (g⁻¹ * x * g⁻¹⁻¹) :=
  calc g⁻¹ * x * g⁻¹⁻¹ * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * y * g⁻¹ * x) * g := by rw [h]
    _ = y * (g⁻¹ * x * g⁻¹⁻¹) := by group

omit hN
  in
private theorem card_J_inf_centralizer_conj_le {g y : G} (hg : g ∈ H z) :
    Nat.card ↥(J z ⊓ centralizer ({g * y * g⁻¹} : Set G)) ≤
      Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) := by
  have hHJ : H z ≤ normalizer (J z : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  rw [← card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective]
  refine card_le_of_le ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hxJ, hxc⟩ := mem_inf.mp hx
  exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hHJ ((H z).inv_mem hg)) x).mp hxJ,
    mem_centralizer_singleton_iff.mpr (conj_inv_mul_comm (mem_centralizer_singleton_iff.mp hxc))⟩

theorem exists_conj_mem_of_isConj_utA
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {y : G} (hyH : y ∈ H z) (hy : orderOf y = 2)
    (hcls : IsConj (qH (z := z) D ⟨y, hyH⟩) (uA * tA))
    (B : Subgroup G) (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hcard : Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B) :
    ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y := by
  classical
  have hy2 : y * y = 1 := by
    have h' := pow_orderOf_eq_one y
    rw [hy, pow_two] at h'
    exact h'
  obtain ⟨ā, hā⟩ := isConj_iff.mp hcls
  obtain ⟨g, hg⟩ := qH_surjective D ā
  let y' : G := (g : G) * y * (g : G)⁻¹
  have hy'H : y' ∈ H z := (H z).mul_mem ((H z).mul_mem g.2 hyH) ((H z).inv_mem g.2)
  have hy' : orderOf y' = 2 := by
    have hc : IsConj y y' := isConj_iff.mpr ⟨(g : G), rfl⟩
    exact hc.orderOf_eq.symm.trans hy
  have hq' : qH (z := z) D ⟨y', hy'H⟩ = uA * tA := by
    have h1 : (⟨y', hy'H⟩ : ↥(H z)) = g * ⟨y, hyH⟩ * g⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv, hg]
    exact hā
  let f : G →* G := (MulAut.conj (g : G)).toMonoidHom
  let B' : Subgroup G := B.map f
  have hconjH : ∀ {a c : G}, a ∈ H z → c ∈ H z → a * c * a⁻¹ ∈ H z :=
    fun ha hc => (H z).mul_mem ((H z).mul_mem ha hc) ((H z).inv_mem ha)
  have hconjC : ∀ {a c x : G}, c * x = x * c →
      (a * c * a⁻¹) * (a * x * a⁻¹) = (a * x * a⁻¹) * (a * c * a⁻¹) := fun {a c x} h =>
    calc a * c * a⁻¹ * (a * x * a⁻¹) = a * (c * x) * a⁻¹ := by group
      _ = a * (x * c) * a⁻¹ := by rw [h]
      _ = a * x * a⁻¹ * (a * c * a⁻¹) := by group
  have hB' : B' ≤ H z ⊓ centralizer ({y'} : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨hbH, hbc⟩ := mem_inf.mp (hBC hb)
    exact mem_inf.mpr ⟨hconjH g.2 hbH, mem_centralizer_singleton_iff.mpr
      (hconjC (mem_centralizer_singleton_iff.mp hbc))⟩
  have hBn' : ∀ c ∈ H z ⊓ centralizer ({y'} : Set G), ∀ b ∈ B', c * b * c⁻¹ ∈ B' := by
    rintro c hc _ ⟨b, hb, rfl⟩
    obtain ⟨hcH, hcc⟩ := mem_inf.mp hc
    have hc' : (g : G)⁻¹ * c * (g : G)⁻¹⁻¹ ∈ H z ⊓ centralizer ({y} : Set G) := by
      refine mem_inf.mpr ⟨hconjH ((H z).inv_mem g.2) hcH, mem_centralizer_singleton_iff.mpr ?_⟩
      exact conj_inv_mul_comm (mem_centralizer_singleton_iff.mp hcc)
    refine mem_map.mpr ⟨_, hBn _ hc' b hb, ?_⟩
    show (g : G) * ((g : G)⁻¹ * c * (g : G)⁻¹⁻¹ * b * ((g : G)⁻¹ * c * (g : G)⁻¹⁻¹)⁻¹) *
        (g : G)⁻¹ = c * ((g : G) * b * (g : G)⁻¹) * c⁻¹
    group
  have hzB' : z ∉ B' := by
    rintro ⟨b, hb, hbz⟩
    have hbz' : (g : G) * b * (g : G)⁻¹ = z := hbz
    have hgz : (g : G) * z = z * (g : G) := Subgroup.mem_centralizer_singleton_iff.mp g.2
    have h1 : (g : G) * b = z * (g : G) := by
      calc (g : G) * b = ((g : G) * b * (g : G)⁻¹) * (g : G) := by group
        _ = z * (g : G) := by rw [hbz']
    have h2 : b = z := mul_left_cancel (h1.trans hgz.symm)
    exact hzB (h2 ▸ hb)
  have hcard' : Nat.card ↥(J z ⊓ centralizer ({y'} : Set G)) ≤ Nat.card B' := by
    calc Nat.card ↥(J z ⊓ centralizer ({y'} : Set G))
        ≤ Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) :=
          card_J_inf_centralizer_conj_le (g := (g : G)) g.2
      _ ≤ Nat.card B := hcard
      _ = Nat.card B' := (card_map_of_injective (MulAut.conj (g : G)).injective).symm
  have hy'B' : y' ∈ B' := mem_map_of_mem f hyB
  obtain ⟨c', hc'H, hc'B', hc'ne⟩ :=
    exists_conj_mem_of_qH_eq_utA (z := z) (D := D) h hZ P hP hy'H hy' hq' B' hB' hBn' hy'B'
      hzB' hcard'
  obtain ⟨b, hbB, hbeq⟩ := mem_map.mp hc'B'
  refine ⟨(g : G)⁻¹ * c' * (g : G), ?_, ?_, ?_⟩
  · exact (H z).mul_mem ((H z).mul_mem ((H z).inv_mem g.2) hc'H) g.2
  · have hb' : (g : G)⁻¹ * c' * (g : G) * y * ((g : G)⁻¹ * c' * (g : G))⁻¹ = b := by
      have hbeq' : (g : G) * b * (g : G)⁻¹ =
          c' * ((g : G) * y * (g : G)⁻¹) * c'⁻¹ := hbeq
      calc (g : G)⁻¹ * c' * (g : G) * y * ((g : G)⁻¹ * c' * (g : G))⁻¹
          = (g : G)⁻¹ * (c' * ((g : G) * y * (g : G)⁻¹) * c'⁻¹) * (g : G) := by group
        _ = (g : G)⁻¹ * ((g : G) * b * (g : G)⁻¹) * (g : G) := by rw [← hbeq']
        _ = b := by group
    rw [hb']
    exact hbB
  · intro heq
    apply hc'ne
    calc c' * y' * c'⁻¹
        = (g : G) * ((g : G)⁻¹ * c' * (g : G) * y * ((g : G)⁻¹ * c' * (g : G))⁻¹) *
            (g : G)⁻¹ := by
          show c' * ((g : G) * y * (g : G)⁻¹) * c'⁻¹ = _
          group
      _ = (g : G) * y * (g : G)⁻¹ := by rw [heq]
      _ = y' := rfl

end CFSG.RankThree.GF2n.Parrott
