module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectCount
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectStep2

open CFSG.Quasithin.H13.Direct523Semi CFSG.Quasithin.H13.Direct523Count

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}

abbrev Ugrp (Z₁ D₃ : Subgroup G) : Subgroup G :=
  conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))

theorem coordN_congr {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) {x y : G} (hx : x ∈ N)
    (hy : y ∈ N) (h : x = y) : coordN D x hx = coordN D y hy := by
  subst h
  rfl

theorem coordN_conj {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) {u : G}
    (hu : u ∈ Subgroup.normalizer (N : Set G)) {v : G} (hv : v ∈ N) :
    D.conj ⟨u, hu⟩ (coordN D v hv) = coordN D (u * v * u⁻¹)
      ((Subgroup.mem_normalizer_iff.mp hu v).mp hv) := by
  unfold coordN
  rw [NatL2Data.conj_apply]
  congr 2

theorem coordN_inv {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) {v : G} (hv : v ∈ N)
    (hv' : v⁻¹ ∈ N) : coordN D v⁻¹ hv' = -coordN D v hv := by
  unfold coordN
  have : (⟨v⁻¹, hv'⟩ : ↥N) = (⟨v, hv⟩ : ↥N)⁻¹ := rfl
  rw [this, map_inv, toAdd_inv]

theorem coordN_comm {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) {u : G}
    (hu : u ∈ Subgroup.normalizer (N : Set G)) {v : G} (hv : v ∈ N)
    (h : u * v * u⁻¹ * v⁻¹ ∈ N) :
    coordN D (u * v * u⁻¹ * v⁻¹) h = D.conj ⟨u, hu⟩ (coordN D v hv) - coordN D v hv := by
  have hA : u * v * u⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hu v).mp hv
  have hB : v⁻¹ ∈ N := N.inv_mem hv
  rw [coordN_mul D hA hB h,
    coordN_inv D hv hB, ← coordN_conj D hu hv, sub_eq_add_neg]

theorem NatL2Data.mem_comm {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) {a b : G}
    (ha : a ∈ N) (hb : b ∈ N) : a * b = b * a := by
  have h : (⟨a, ha⟩ : ↥N) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
    D.E.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  exact congrArg Subtype.val h

theorem T_le_centralizer_Z₁ (s : Setup521 G T M L V H B D D₃ Z₁ n) :
    T ≤ Subgroup.centralizer (Z₁ : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' := (quasithinOmegaOneCenter_le_inf T (s.z1.1 hz)).2
  exact (Subgroup.mem_centralizer_iff.mp hz' t ht).symm

theorem conj_fix_of_centralizes {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) {u z : G}
    (hu : u ∈ Subgroup.normalizer (N : Set G)) {hzN : z ∈ N} (hcomm : u * z = z * u) :
    D.conj ⟨u, hu⟩ (coordN D z hzN) = coordN D z hzN := by
  rw [coordN_conj D hu hzN]
  apply coordN_congr
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem Ugrp_le_T (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact) : Ugrp Z₁ D₃ ≤ T :=
  s.U_le_T h5114 hF

theorem exists_frob_semilinear (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact)
    (hU : ¬ IsMulCommutative ↥(Ugrp Z₁ D₃))
    {N : Subgroup G} (D : NatL2Data L N 2) {z : G} (hz : z ∈ Z₁) (hzN : z ∈ N)
    (hTN : T ≤ Subgroup.normalizer (N : Set G))
    (hV2 : ∀ v ∈ conjClosure Z₁ D₃, ∃ hv : v ∈ N, ∃ μ : D.K, μ ^ 4 = μ ∧
      coordN D v hv = μ • coordN D z hzN) :
    ∃ u ∈ Ugrp Z₁ D₃, ∃ hu : u ∈ Subgroup.normalizer (N : Set G), ∃ σ : D.K ≃+* D.K,
      IsSemi (D.conj ⟨u, hu⟩) σ ∧ σ ≠ RingEquiv.refl D.K := by
  obtain ⟨u, hu, v, hv, huv⟩ := exists_noncomm_V₂_U s h5114 hF hU
  have huT : u ∈ T := s.U_le_T h5114 hF hu
  have huN : u ∈ Subgroup.normalizer (N : Set G) := hTN huT
  have huL : u ∈ Subgroup.normalizer (L : Set G) :=
    (s.hyp.hyp.toHyp5_0_1.T_le.trans s.hyp.hyp.toHyp5_0_1.normal) huT
  obtain ⟨σ, hσ⟩ := D.exists_semilinear ⟨u, huN⟩ huL
  have huz : u * z = z * u :=
    (Subgroup.mem_centralizer_iff.mp (s.U_le_G₁ hu) z hz).symm
  refine ⟨u, hu, huN, σ, hσ, ?_⟩
  intro hσid
  obtain ⟨hvN, μ, hμ, hcoord⟩ := hV2 v hv
  apply huv
  have hcv : D.conj ⟨u, huN⟩ (coordN D v hvN) = coordN D v hvN := by
    rw [hcoord, hσ, hσid, conj_fix_of_centralizes D huN huz]
    rfl
  have h2 := coordN_conj D huN hvN
  rw [hcv] at h2
  have h3 : u * v * u⁻¹ = v :=
    coordN_injective D ((Subgroup.mem_normalizer_iff.mp huN v).mp hvN) hvN h2.symm
  calc u * v = (u * v * u⁻¹) * u := by group
    _ = v * u := by rw [h3]

end CFSG.Quasithin.H13
