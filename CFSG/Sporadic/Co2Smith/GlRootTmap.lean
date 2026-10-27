module

public import CFSG.Sporadic.Co2Smith.GlRootTrans
public import CFSG.Sporadic.Co2Smith.G21

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

theorem phi_zC_of_ne_one
    {G : Type*} [Group G]
    {z : G} (φ : centralizer ({z} : Set G) ≃* Cz) (hz : z ≠ 1) : φ (zC z) = zCz := by
  have hcen : ∀ q ∈ Qsub, (φ (zC z) : K) * q = q * (φ (zC z) : K) := by
    intro q hq
    have hqC : q ∈ Cz := Qsub_le_Cz hq
    have e := (mem_center_iff.mp (zC_mem_center z)) (φ.symm ⟨q, hqC⟩)
    have e2 := congrArg (fun x => (φ x : K)) e
    simp only [map_mul, MulEquiv.apply_symm_apply] at e2
    exact e2.symm
  rcases centralizer_Q _ (φ (zC z)).2 hcen with h | h
  · exfalso
    apply hz
    have h1 : φ (zC z) = 1 := Subtype.ext h
    have h2 : zC z = 1 := φ.injective (h1.trans (map_one φ).symm)
    exact congrArg Subtype.val h2
  · exact Subtype.ext h

section Tmap

variable
  {G : Type*} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G} {α : Cz}

@[expose] noncomputable def Ax25 : Subgroup K := Cz ⊓ centralizer ({x25K} : Set K)

theorem mem_Ax25 {y : K} : y ∈ Ax25 ↔ y ∈ Cz ∧ y * x25K = x25K * y := by
  rw [Ax25, Subgroup.mem_inf]
  exact and_congr Iff.rfl mem_centralizer_singleton_iff

theorem x25K_mem_Cz : x25K ∈ Cz :=
  mem_Cz_of_comm (by
    have := xLongK_comm (k := 1) (l := 0) (by norm_num) (by norm_num) (by norm_num)
    rwa [xLongK_zero] at this)

theorem x25K_mem_C0c : x25K ∈ C0c :=
  C0c.mul_mem (C0c.mul_mem δ1hK_mem_C0c x16K_mem_C0c) δ1hK_mem_C0c

theorem comm_conj_iff {d a b : K} (hd : d * d = 1) :
    d * a * d * b = b * (d * a * d) ↔ a * (d * b * d) = d * b * d * a := by
  constructor
  · intro h
    calc a * (d * b * d) = d * (d * a * d * b) * d := by
          rw [show d * (d * a * d * b) * d = (d * d) * a * (d * b * d) by group, hd, one_mul]
      _ = d * (b * (d * a * d)) * d := by rw [h]
      _ = d * b * d * a := by
          rw [show d * (b * (d * a * d)) * d = d * b * d * a * (d * d) by group, hd, mul_one]
  · intro h
    calc d * a * d * b = d * (a * (d * b * d)) * d := by
          rw [show d * (a * (d * b * d)) * d = d * a * d * b * (d * d) by group, hd, mul_one]
      _ = d * (d * b * d * a) * d := by rw [h]
      _ = b * (d * a * d) := by
          rw [show d * (d * b * d * a) * d = (d * d) * b * (d * a * d) by group, hd, one_mul]

theorem conj_δ1hK_comm_z0_iff {y : K} :
    δ1hK * y * δ1hK * z0 = z0 * (δ1hK * y * δ1hK) ↔ y * x25K = x25K * y := by
  rw [comm_conj_iff δ1hK_mul_self, ← x16K_eq]
  rfl

theorem conj_δ1hK_mem_Cz_of_Ax25 {y : K} (hy : y ∈ Ax25) : δ1hK * y * δ1hK ∈ Cz :=
  mem_Cz_of_comm (conj_δ1hK_comm_z0_iff.2 (mem_Ax25.1 hy).2)

theorem mem_Ax25_of_conj {y : K} (hy : y ∈ Cz) (hy' : δ1hK * y * δ1hK ∈ Cz) : y ∈ Ax25 :=
  mem_Ax25.2 ⟨hy, conj_δ1hK_comm_z0_iff.1 (comm_of_mem_Cz hy')⟩

theorem α3K_mem_Ax25 : α3K ∈ Ax25 := by
  exact mem_Ax25.2 ⟨α3K_mem_Cz, (mem_C0c.1 x25K_mem_C0c).1⟩

theorem rhoK_δ1hK_sq : rhoK ρ δ1hK * rhoK ρ δ1hK = 1 := by
  rw [← rhoK_mul ρ δ1hK_mem_C0c δ1hK_mem_C0c, δ1hK_mul_self, rhoK_one]

theorem rhoK_δ1hK_inv : (rhoK ρ δ1hK)⁻¹ = rhoK ρ δ1hK :=
  inv_eq_of_mul_eq_one_right rhoK_δ1hK_sq

theorem phiInv_z0 (hφz : φ (zC z) = zCz) : phiInv φ z0 = z := by
  rw [phiInv_of_mem φ z0_mem_Cz, show (⟨z0, z0_mem_Cz⟩ : Cz) = zCz from rfl, ← hφz,
    MulEquiv.symm_apply_apply]
  rfl

theorem rhoK_conj_z (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) :
    rhoK ρ δ1hK * z * rhoK ρ δ1hK = phiInv φ x25K := by
  have hz0 : rhoK ρ z0 = z := by
    rw [rhoK_eq_phiInv hm (x16K_eq ▸ x16K_mem_C0c) z0_mem_Cz, phiInv_z0 hφz]
  conv_lhs => rw [← hz0]
  rw [← rhoK_mul ρ δ1hK_mem_C0c (x16K_eq ▸ x16K_mem_C0c),
    ← rhoK_mul ρ (C0c.mul_mem δ1hK_mem_C0c (x16K_eq ▸ x16K_mem_C0c)) δ1hK_mem_C0c, ← x16K_eq,
    ← x25K, rhoK_eq_phiInv hm x25K_mem_C0c x25K_mem_Cz]

variable (φ ρ) in
@[expose] noncomputable def chartT (y : K) : K := by
  classical
  exact if h : rhoK ρ δ1hK * phiInv φ y * rhoK ρ δ1hK ∈ centralizer ({z} : Set G) then
    (φ ⟨_, h⟩ : K) else 1

theorem conj_phiInv_mem (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) {y : K}
    (hy : y ∈ Ax25) :
    rhoK ρ δ1hK * phiInv φ y * rhoK ρ δ1hK ∈ centralizer ({z} : Set G) := by
  obtain ⟨hyC, hyx⟩ := mem_Ax25.1 hy
  have hd := rhoK_δ1hK_sq (ρ := ρ)
  set d := rhoK ρ δ1hK
  have hb := rhoK_conj_z hm hφz
  have hab : phiInv φ y * phiInv φ x25K = phiInv φ x25K * phiInv φ y := by
    rw [← phiInv_mul φ hyC x25K_mem_Cz, hyx, phiInv_mul φ x25K_mem_Cz hyC]
  have hz : z = d * phiInv φ x25K * d := by
    rw [← hb, show d * (d * z * d) * d = (d * d) * z * (d * d) by group, hd]
    group
  rw [mem_centralizer_singleton_iff]
  have key : d * phiInv φ y * d * (d * phiInv φ x25K * d) =
      d * phiInv φ x25K * d * (d * phiInv φ y * d) := by
    calc d * phiInv φ y * d * (d * phiInv φ x25K * d)
        = d * (phiInv φ y * phiInv φ x25K) * d := by
          rw [show d * phiInv φ y * d * (d * phiInv φ x25K * d) =
            d * phiInv φ y * (d * d) * phiInv φ x25K * d by group, hd]
          group
      _ = d * (phiInv φ x25K * phiInv φ y) * d := by rw [hab]
      _ = d * phiInv φ x25K * d * (d * phiInv φ y * d) := by
          rw [show d * phiInv φ x25K * d * (d * phiInv φ y * d) =
            d * phiInv φ x25K * (d * d) * phiInv φ y * d by group, hd]
          group
  rw [← hz] at key
  exact key

theorem phiInv_chartT (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) {y : K}
    (hy : y ∈ Ax25) :
    phiInv φ (chartT φ ρ y) = rhoK ρ δ1hK * phiInv φ y * rhoK ρ δ1hK := by
  classical
  rw [chartT, dite_eq_left (conj_phiInv_mem hm hφz hy), phiInv_phi]

theorem chartT_mem_Cz (y : K) : chartT φ ρ y ∈ Cz := by
  classical
  unfold chartT
  split_ifs
  · exact (φ _).2
  · exact Cz.one_mem

theorem chartT_mem (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) {y : K}
    (hy : y ∈ Ax25) : chartT φ ρ y ∈ Ax25 := by
  refine mem_Ax25.2 ⟨chartT_mem_Cz y, ?_⟩
  have hd := rhoK_δ1hK_sq (ρ := ρ)
  have hc := chartT_mem_Cz (φ := φ) (ρ := ρ) y
  apply phiInv_injOn φ (Cz.mul_mem hc x25K_mem_Cz) (Cz.mul_mem x25K_mem_Cz hc)
  have hyz : phiInv φ y * z = z * phiInv φ y :=
    mem_centralizer_singleton_iff.mp (phiInv_mem φ y)
  rw [phiInv_mul φ hc x25K_mem_Cz, phiInv_mul φ x25K_mem_Cz hc, phiInv_chartT hm hφz hy,
    ← rhoK_conj_z hm hφz]
  set d := rhoK ρ δ1hK
  rw [show d * phiInv φ y * d * (d * z * d) = d * phiInv φ y * (d * d) * z * d by group, hd,
    show d * z * d * (d * phiInv φ y * d) = d * z * (d * d) * phiInv φ y * d by group, hd,
    mul_one, mul_one, mul_assoc d, hyz, ← mul_assoc]

theorem chartT_mul (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) {y y' : K}
    (hy : y ∈ Ax25) (hy' : y' ∈ Ax25) :
    chartT φ ρ (y * y') = chartT φ ρ y * chartT φ ρ y' := by
  have hd := rhoK_δ1hK_sq (ρ := ρ)
  have hyC := (mem_Ax25.1 hy).1
  have hyC' := (mem_Ax25.1 hy').1
  apply phiInv_injOn φ (chartT_mem_Cz _) (Cz.mul_mem (chartT_mem_Cz _) (chartT_mem_Cz _))
  rw [phiInv_mul φ (chartT_mem_Cz _) (chartT_mem_Cz _), phiInv_chartT hm hφz (Ax25.mul_mem hy hy'),
    phiInv_chartT hm hφz hy, phiInv_chartT hm hφz hy', phiInv_mul φ hyC hyC']
  set d := rhoK ρ δ1hK
  rw [show d * phiInv φ y * d * (d * phiInv φ y' * d) =
    d * phiInv φ y * (d * d) * phiInv φ y' * d by group, hd]
  group

theorem chartT_chartT (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) {y : K}
    (hy : y ∈ Ax25) : chartT φ ρ (chartT φ ρ y) = y := by
  have hd := rhoK_δ1hK_sq (ρ := ρ)
  apply phiInv_injOn φ (chartT_mem_Cz _) (mem_Ax25.1 hy).1
  rw [phiInv_chartT hm hφz (chartT_mem hm hφz hy), phiInv_chartT hm hφz hy]
  set d := rhoK ρ δ1hK
  rw [show d * (d * phiInv φ y * d) * d = (d * d) * phiInv φ y * (d * d) by group, hd]
  group

theorem chartT_one (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) :
    chartT φ ρ 1 = 1 := by
  have h := chartT_mul hm hφz Ax25.one_mem Ax25.one_mem
  rw [mul_one] at h
  exact (mul_eq_left.1 h.symm)

theorem chartT_of_mem_C0c (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) {y : K}
    (hy : y ∈ Ax25) (hy0 : y ∈ C0c) : chartT φ ρ y = δ1hK * y * δ1hK := by
  have hc : δ1hK * y * δ1hK ∈ C0c :=
    C0c.mul_mem (C0c.mul_mem δ1hK_mem_C0c hy0) δ1hK_mem_C0c
  apply phiInv_injOn φ (chartT_mem_Cz _) (conj_δ1hK_mem_Cz_of_Ax25 hy)
  rw [phiInv_chartT hm hφz hy, ← rhoK_eq_phiInv hm hy0 (mem_Ax25.1 hy).1,
    ← rhoK_eq_phiInv hm hc (conj_δ1hK_mem_Cz_of_Ax25 hy), rhoK_mul ρ (C0c.mul_mem δ1hK_mem_C0c hy0)
      δ1hK_mem_C0c, rhoK_mul ρ δ1hK_mem_C0c hy0]

theorem chartT_α3K (hm : SmithC0Marking φ α3c ρ) (hφz : φ (zC z) = zCz) :
    chartT φ ρ α3K = α3K := by
  have hd := rhoK_δ1hK_sq (ρ := ρ)
  have hc := hm.2.1 ⟨δ1hK, δ1hK_mem_C0c⟩
  rw [← rhoK_of_mem ρ δ1hK_mem_C0c] at hc
  have ha : phiInv φ α3K = (φ.symm α3c : G) := phiInv_of_mem φ α3K_mem_Cz
  apply phiInv_injOn φ (chartT_mem_Cz _) α3K_mem_Cz
  rw [phiInv_chartT hm hφz α3K_mem_Ax25, ha, hc, mul_assoc, hd, mul_one]

theorem d1Core_of_chartT (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz)
    (h : ∀ y ∈ rootSet, y ∈ Ax25 → chartT φ ρ y = δ1hK * y * δ1hK) : D1Core φ ρ := by
  intro y hyR hy hy'
  have hA := mem_Ax25_of_conj hy hy'
  rw [rhoK_δ1hK_inv, ← phiInv_chartT hm hφz hA, h y hyR hA]

end Tmap

end CFSG.Sporadic.Co2Smith
