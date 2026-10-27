module

public import CFSG.Sporadic.Recognition.JankoWongSec4Cd

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

@[expose] def cmt {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

section Generic

variable {G : Type*} [Group G]

theorem cmt_def (x y : G) : cmt x y = x⁻¹ * y⁻¹ * x * y := rfl

theorem cmt_swap (x y : G) : cmt y x = (cmt x y)⁻¹ := by simp [cmt, mul_assoc]

theorem cj_cmt (x y g : G) : cj (cmt x y) g = cmt (cj x g) (cj y g) := cj_comm x y g

theorem cj_eq_mul_cmt (x y : G) : cj x y = x * cmt x y := by simp [cj, cmt, mul_assoc]

theorem cmt_inv_right {x y : G} (h : cmt x y * y = y * cmt x y) : cmt x y⁻¹ = (cmt x y)⁻¹ := by
  have e1 : y⁻¹ * x * y = x * cmt x y := cj_eq_mul_cmt x y
  have e3 : y * cmt x y * y⁻¹ = cmt x y := by rw [← h]; group
  have e0 : x = y * (x * cmt x y) * y⁻¹ := by rw [← e1]; group
  have e2 : y * x * y⁻¹ = x * (cmt x y)⁻¹ := by
    calc y * x * y⁻¹ = (y * x * y⁻¹) * (y * cmt x y * y⁻¹) * (cmt x y)⁻¹ := by rw [e3]; group
      _ = (y * (x * cmt x y) * y⁻¹) * (cmt x y)⁻¹ := by group
      _ = x * (cmt x y)⁻¹ := by rw [← e0]
  calc cmt x y⁻¹ = x⁻¹ * (y * x * y⁻¹) := by simp [cmt, mul_assoc]
    _ = (cmt x y)⁻¹ := by rw [e2]; group

theorem cj_of_relation {A x y : G} (hAx : A * x = x * A) (hA3 : A * A * A = 1)
    (e : y * (A * x⁻¹) = x⁻¹ * (y * A⁻¹)) : y⁻¹ * x * y = x * A := by
  have hAx' : x⁻¹ * A = A * x⁻¹ := by
    calc x⁻¹ * A = x⁻¹ * (A * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * A) * x⁻¹ := by rw [hAx]
      _ = A * x⁻¹ := by group
  have e1 : y⁻¹ * x⁻¹ * y = A * A * x⁻¹ := by
    calc y⁻¹ * x⁻¹ * y = y⁻¹ * (x⁻¹ * (y * A⁻¹)) * A := by group
      _ = y⁻¹ * (y * (A * x⁻¹)) * A := by rw [← e]
      _ = A * x⁻¹ * A := by group
      _ = A * A * x⁻¹ := by rw [mul_assoc, hAx', ← mul_assoc]
  have e2 : A⁻¹ * A⁻¹ = A := by
    calc A⁻¹ * A⁻¹ = A⁻¹ * A⁻¹ * (A * A * A) := by rw [hA3, mul_one]
      _ = A := by group
  calc y⁻¹ * x * y = (y⁻¹ * x⁻¹ * y)⁻¹ := by group
    _ = (A * A * x⁻¹)⁻¹ := by rw [e1]
    _ = x * (A⁻¹ * A⁻¹) := by group
    _ = x * A := by rw [e2]

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {S : Setup G}

omit [Finite G] in
theorem mem_zpowers_comm {a x y : G} (hx : x ∈ zpowers a) (hy : a * y = y * a) :
    x * y = y * x := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ((show Commute a y from hy).zpow_left j).eq

omit [Finite G] in
theorem eq_one_of_mem_zpowers_of_eq_inv {a x : G} (ha3 : a ^ 3 = 1) (hx : x ∈ zpowers a)
    (h : x = x⁻¹) : x = 1 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h3 : (a ^ j) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; simp [ha3]
  have h2 : a ^ j * a ^ j = 1 := mul_eq_one_iff_eq_inv.mpr h
  calc a ^ j = (a ^ j * a ^ j) * a ^ j := by rw [h2, one_mul]
    _ = (a ^ j) ^ 3 := (pow_three' _).symm
    _ = 1 := h3

section NoCerts

variable {c : Ctx S} {a₁ v v₁ : G} (h : Sec4Hyp c a₁ v v₁)

theorem Ctx.a_comm_MG {m : G} (hm : m ∈ c.MG) : (c.a : G) * m = m * (c.a : G) :=
  (Subgroup.mem_centralizer_singleton_iff.mp (c.MG_le_Kg hm)).symm

include h in
theorem Sec4Hyp.cj_a2_of_mem_zpowers {x : G} (hx : x ∈ zpowers (c.a : G)) :
    cj x (c.a2 a₁) = x := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact cj_eq_self_of_comm ((show Commute (c.a : G) (c.a2 a₁) from h.a2_comm_a.symm).zpow_left j).eq

include h in
theorem Sec4Hyp.cj_v_of_mem_zpowers {x : G} (hx : x ∈ zpowers (c.a : G)) : cj x v = x⁻¹ := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [cj_zpow_left, show cj (c.a : G) v = (c.a : G)⁻¹ from h.rel.sigma1_by_v, inv_zpow', zpow_neg]

omit [Finite G] in
theorem zpow_eq_inv_of_cube {x : G} (hx : x ^ 3 = 1) {p : ℤ} (hp : 3 ∣ p + 1) : x ^ p = x⁻¹ := by
  have h1 : x ^ (p + 1) = 1 := zpow_eq_one_of_cube hx hp
  rw [zpow_add_one] at h1
  exact eq_inv_of_mul_eq_one_left h1

include h in
theorem Sec4Hyp.a2_b_cube : (c.a2 a₁ * (c.b : G)) ^ 3 = 1 := by
  have := h.rel.a2_sigma2_cube
  rw [show (c.t : G)⁻¹ * (c.a : G) * (c.t : G) = (c.b : G) from c.cj_a_t] at this
  exact this

include h in
theorem Sec4Hyp.b_a2_b :
    (c.b : G) * c.a2 a₁ * (c.b : G) = c.a2 a₁ * (c.b : G)⁻¹ * c.a2 a₁ := by
  have hz : S.z * S.z = 1 := Ctx.z_mul_z (S := S)
  have hzb : S.z * (c.b : G)⁻¹ = (c.b : G)⁻¹ * S.z := (Ctx.zc (S.H.inv_mem c.b.2)).symm
  have hza : S.z * c.a2 a₁ = c.a2 a₁ * S.z := h.a2_comm_z.symm
  have e := h.a2_b_cube
  rw [pow_three'] at e
  have e1 : (c.b : G) * c.a2 a₁ * (c.b : G) = (c.a2 a₁)⁻¹ * (c.b : G)⁻¹ * (c.a2 a₁)⁻¹ := by
    calc (c.b : G) * c.a2 a₁ * (c.b : G)
        = (c.a2 a₁)⁻¹ * (c.a2 a₁ * (c.b : G) * (c.a2 a₁ * (c.b : G)) * (c.a2 a₁ * (c.b : G)))
          * (c.b : G)⁻¹ * (c.a2 a₁)⁻¹ := by group
      _ = (c.a2 a₁)⁻¹ * (c.b : G)⁻¹ * (c.a2 a₁)⁻¹ := by rw [e]; group
  rw [e1, h.a2_inv]
  calc c.a2 a₁ * S.z * (c.b : G)⁻¹ * (c.a2 a₁ * S.z)
      = c.a2 a₁ * (S.z * (c.b : G)⁻¹) * (c.a2 a₁ * S.z) := by group
    _ = c.a2 a₁ * ((c.b : G)⁻¹ * S.z) * (c.a2 a₁ * S.z) := by rw [hzb]
    _ = c.a2 a₁ * (c.b : G)⁻¹ * (S.z * c.a2 a₁) * S.z := by group
    _ = c.a2 a₁ * (c.b : G)⁻¹ * (c.a2 a₁ * S.z) * S.z := by rw [hza]
    _ = c.a2 a₁ * (c.b : G)⁻¹ * c.a2 a₁ * (S.z * S.z) := by group
    _ = c.a2 a₁ * (c.b : G)⁻¹ * c.a2 a₁ := by rw [hz, mul_one]

end NoCerts

section Certs


namespace Phi1

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} {W : Subgroup G} (hφ : Phi1 c φ₁)
  (h : Sec4Hyp c a₁ v v₁) (hW : c.IsW W)

include hW in
theorem cmt_mem_zpowers {x y : G} (hx : x ∈ c.MG) (hy : y ∈ c.MG) :
    cmt x y ∈ zpowers (c.a : G) := by
  have := (c.isExtraspecialThree_MG hW).commutator x⁻¹ (c.MG.inv_mem hx) y⁻¹ (c.MG.inv_mem hy)
  simpa [cmt] using this

include hφ h hW in
theorem cmt14_eq_one : cmt φ₁ (phi4 c a₁ v φ₁) = 1 ∧
    cmt (cj φ₁ v) (phi3 c a₁ φ₁) = 1 := by
  have hM1 := hφ.phi1_mem_MG
  have hM2 := hφ.phi2_mem_MG h
  have hM3 := hφ.phi3_mem_MG h
  have hM4 := hφ.phi4_mem_MG h
  have hc14 := cmt_mem_zpowers hW hM1 hM4
  have e1 : cj (cmt φ₁ (phi4 c a₁ v φ₁)) (c.a2 a₁) = cmt φ₁ (phi4 c a₁ v φ₁) :=
    h.cj_a2_of_mem_zpowers hc14
  have e2 : cj (cmt φ₁ (phi4 c a₁ v φ₁)) v = (cmt φ₁ (phi4 c a₁ v φ₁))⁻¹ :=
    h.cj_v_of_mem_zpowers hc14
  have e3 : cj (cmt φ₁ (phi4 c a₁ v φ₁)) (c.a2 a₁) =
      cmt (phi3 c a₁ φ₁) (cj φ₁ v)⁻¹ := by
    rw [cj_cmt, hφ.phi4_by_a2 h]
  have e4 : cj (cmt φ₁ (phi4 c a₁ v φ₁)) v = cmt (cj φ₁ v) (phi3 c a₁ φ₁) := by
    rw [cj_cmt, hφ.phi4_by_v h]
  have e5 : cmt (phi3 c a₁ φ₁) (cj φ₁ v)⁻¹ = cmt (cj φ₁ v) (phi3 c a₁ φ₁) := by
    rw [cmt_inv_right (mem_zpowers_comm (cmt_mem_zpowers hW hM3 hM2) (Ctx.a_comm_MG hM2))]
    exact (cmt_swap _ _).symm
  have h1 : cmt φ₁ (phi4 c a₁ v φ₁) = (cmt φ₁ (phi4 c a₁ v φ₁))⁻¹ :=
    calc cmt φ₁ (phi4 c a₁ v φ₁) = cj (cmt φ₁ (phi4 c a₁ v φ₁)) (c.a2 a₁) := e1.symm
      _ = cmt (phi3 c a₁ φ₁) (cj φ₁ v)⁻¹ := e3
      _ = cmt (cj φ₁ v) (phi3 c a₁ φ₁) := e5
      _ = cj (cmt φ₁ (phi4 c a₁ v φ₁)) v := e4.symm
      _ = (cmt φ₁ (phi4 c a₁ v φ₁))⁻¹ := e2
  have h0 : cmt φ₁ (phi4 c a₁ v φ₁) = 1 :=
    eq_one_of_mem_zpowers_of_eq_inv c.aG_cube hc14 h1
  refine ⟨h0, ?_⟩
  rw [← e4, e2, h0, inv_one]

include hφ h hW in
theorem cmt24_eq : cmt (cj φ₁ v) (phi4 c a₁ v φ₁) = cmt φ₁ (phi3 c a₁ φ₁) := by
  have hM1 := hφ.phi1_mem_MG
  have hM2 := hφ.phi2_mem_MG h
  have hM3 := hφ.phi3_mem_MG h
  have hM4 := hφ.phi4_mem_MG h
  have hκ := cmt_mem_zpowers hW hM1 hM3
  have e1 : cj (cmt φ₁ (phi3 c a₁ φ₁)) v = (cmt φ₁ (phi3 c a₁ φ₁))⁻¹ :=
    h.cj_v_of_mem_zpowers hκ
  have e2 : cj (cmt φ₁ (phi3 c a₁ φ₁)) v = cmt (cj φ₁ v) (phi4 c a₁ v φ₁)⁻¹ := by
    rw [cj_cmt, hφ.phi3_by_v h]
  have e3 : cmt (cj φ₁ v) (phi4 c a₁ v φ₁)⁻¹ = (cmt (cj φ₁ v) (phi4 c a₁ v φ₁))⁻¹ :=
    cmt_inv_right (mem_zpowers_comm (cmt_mem_zpowers hW hM2 hM4) (Ctx.a_comm_MG hM4))
  have : (cmt (cj φ₁ v) (phi4 c a₁ v φ₁))⁻¹ = (cmt φ₁ (phi3 c a₁ φ₁))⁻¹ := by
    rw [← e3, ← e2, e1]
  exact inv_injective this

include hφ h in
theorem star : cj (phi3 c a₁ φ₁) (c.b : G) =
    cj (cj (phi3 c a₁ φ₁) (c.b : G)⁻¹) (c.a2 a₁) := by
  have h81 := c.card_OG_eq_81
  have hbN : (c.b : G) ∈ c.OG := c.PG_le_OG h81 c.bG_mem_PG
  have hφb : cj φ₁ (c.b : G) = φ₁ := cj_eq_self_of_comm (c.OG_comm φ₁ hφ.mem _ hbN)
  have e := congrArg (fun g => cj φ₁ g) h.b_a2_b
  simp only [cj_mul_right, hφb] at e
  exact e

include hφ h hW in
theorem exists_k : ∃ k : ℤ,
    cj (phi3 c a₁ φ₁) (c.b : G) = φ₁⁻¹ * phi3 c a₁ φ₁ * (c.a : G) ^ (-k) ∧
    cj φ₁ (phi3 c a₁ φ₁) = φ₁ * (c.a : G) ^ k ∧
    cj (c.b : G) (phi3 c a₁ φ₁) = (c.b : G) * (φ₁ * (c.a : G) ^ (-k)) := by
  have h81 := c.card_OG_eq_81
  obtain ⟨cd, hcd⟩ := hφ.exists_cd h hW
  have hbN : (c.b : G) ∈ c.OG := c.PG_le_OG h81 c.bG_mem_PG
  have hM1 := hφ.phi1_mem_MG
  have hM2 := hφ.phi2_mem_MG h
  have hM3 := hφ.phi3_mem_MG h
  have hM4 := hφ.phi4_mem_MG h
  have hφ3NG : phi3 c a₁ φ₁ ∈ c.NG := hW.le_NG (c.MG_le_W hW hM3)
  obtain ⟨w, hwdef⟩ : ∃ w : G, w = (phi3 c a₁ φ₁)⁻¹ * cj (phi3 c a₁ φ₁) (c.b : G) := ⟨_, rfl⟩
  have hbKg : (c.b : G) ∈ c.Kg := c.OG_le_Kg hbN
  have hcjM : cj (phi3 c a₁ φ₁) (c.b : G) ∈ c.MG := by
    have := c.MG_conj (c.Kg.inv_mem hbKg) hM3
    simpa [cj] using this
  have hwM : w ∈ c.MG := by rw [hwdef]; exact c.MG.mul_mem (c.MG.inv_mem hM3) hcjM
  have hwN : w ∈ c.OG := by
    have h1 : cj (c.b : G)⁻¹ (phi3 c a₁ φ₁) ∈ c.OG :=
      c.cj_mem_OG_of_mem_NG' hφ3NG (c.OG.inv_mem hbN)
    have h2 : w = cj (c.b : G)⁻¹ (phi3 c a₁ φ₁) * (c.b : G) := by
      rw [hwdef]; unfold cj; group
    rw [h2]; exact c.OG.mul_mem h1 hbN
  have hu3 : cj (phi3 c a₁ φ₁) (c.b : G) = phi3 c a₁ φ₁ * w := by rw [hwdef]; group
  have hwb : cj w (c.b : G) = w := cj_eq_self_of_comm (c.OG_comm w hwN _ hbN)
  have hinv : cj (phi3 c a₁ φ₁) (c.b : G)⁻¹ = phi3 c a₁ φ₁ * w⁻¹ := by
    have e : cj (phi3 c a₁ φ₁ * w⁻¹) (c.b : G) = phi3 c a₁ φ₁ := by
      rw [cj_mul_left, cj_inv_left, hwb, hu3]; group
    calc cj (phi3 c a₁ φ₁) (c.b : G)⁻¹
        = cj (cj (phi3 c a₁ φ₁ * w⁻¹) (c.b : G)) (c.b : G)⁻¹ := by rw [e]
      _ = phi3 c a₁ φ₁ * w⁻¹ := cj_cj_inv _ _
  have hE : phi3 c a₁ φ₁ * w = φ₁⁻¹ * (cj w (c.a2 a₁))⁻¹ := by
    have e := hφ.star h
    rw [hu3, hinv, cj_mul_left, cj_inv_left, hφ.phi3_by_a2 h] at e
    exact e
  obtain ⟨k₀, p₁, p₂, p₃, p₄, hnf⟩ := hφ.normal_form h hW hwM
  have hcw : cd w = (p₁ : ZMod 3) • (Pi.single 0 1 : Fin 4 → ZMod 3) +
      (p₂ : ZMod 3) • (Pi.single 1 1 : Fin 4 → ZMod 3) +
      (p₃ : ZMod 3) • (Pi.single 2 1 : Fin 4 → ZMod 3) +
      (p₄ : ZMod 3) • (Pi.single 3 1 : Fin 4 → ZMod 3) := by
    rw [hnf, hcd.cd_five hM1 hM2 hM3 hM4, hcd.phi1, hcd.phi2, hcd.phi3, hcd.phi4]
  have hMcj : cj w (c.a2 a₁) ∈ c.MG := by
    have := c.MG_conj (c.Kg.inv_mem h.a2_mem_Kg) hwM
    simpa [cj] using this
  have ha2k : cj ((c.a : G) ^ k₀) (c.a2 a₁) = (c.a : G) ^ k₀ :=
    h.cj_a2_of_mem_zpowers (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k₀)
  have hcjw : cj w (c.a2 a₁) = (c.a : G) ^ k₀ * phi3 c a₁ φ₁ ^ p₁ * phi4 c a₁ v φ₁ ^ p₂ *
      (φ₁⁻¹) ^ p₃ * ((cj φ₁ v)⁻¹) ^ p₄ := by
    rw [hnf]
    simp only [cj_mul_left, cj_zpow_left, ha2k, hφ.phi3_by_a2 h, hφ.phi4_by_a2 h]
  have hcc : cd (cj w (c.a2 a₁)) = (p₁ : ZMod 3) • (Pi.single 2 1 : Fin 4 → ZMod 3) +
      (p₂ : ZMod 3) • (Pi.single 3 1 : Fin 4 → ZMod 3) +
      (p₃ : ZMod 3) • (-(Pi.single 0 1 : Fin 4 → ZMod 3)) +
      (p₄ : ZMod 3) • (-(Pi.single 1 1 : Fin 4 → ZMod 3)) := by
    rw [hcjw, hcd.cd_five hM3 hM4 (c.MG.inv_mem hM1) (c.MG.inv_mem hM2), hcd.phi3, hcd.phi4,
      hcd.inv hM1, hcd.inv hM2, hcd.phi1, hcd.phi2]
  have key := congrArg cd hE
  rw [hcd.add _ hM3 _ hwM, hcd.add _ (c.MG.inv_mem hM1) _ (c.MG.inv_mem hMcj), hcd.inv hM1,
    hcd.inv hMcj, hcd.phi3, hcd.phi1, hcw, hcc] at key
  have sol : ∀ P₁ P₂ P₃ P₄ : ZMod 3,
      (Pi.single 2 1 : Fin 4 → ZMod 3) + (P₁ • (Pi.single 0 1 : Fin 4 → ZMod 3) +
        P₂ • (Pi.single 1 1 : Fin 4 → ZMod 3) + P₃ • (Pi.single 2 1 : Fin 4 → ZMod 3) +
        P₄ • (Pi.single 3 1 : Fin 4 → ZMod 3)) =
      -(Pi.single 0 1 : Fin 4 → ZMod 3) + -(P₁ • (Pi.single 2 1 : Fin 4 → ZMod 3) +
        P₂ • (Pi.single 3 1 : Fin 4 → ZMod 3) + P₃ • -(Pi.single 0 1 : Fin 4 → ZMod 3) +
        P₄ • -(Pi.single 1 1 : Fin 4 → ZMod 3)) →
      P₁ + 1 = 0 ∧ P₂ = 0 ∧ P₃ = 0 ∧ P₄ = 0 := by decide
  obtain ⟨s1, s2, s3, s4⟩ := sol _ _ _ _ key
  have d1 : (3 : ℤ) ∣ p₁ + 1 := by
    have : (((p₁ + 1 : ℤ)) : ZMod 3) = 0 := by push_cast; exact s1
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (p₁ + 1) 3).mp this
  have d2 : (3 : ℤ) ∣ p₂ := by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd p₂ 3).mp s2
  have d3 : (3 : ℤ) ∣ p₃ := by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd p₃ 3).mp s3
  have d4 : (3 : ℤ) ∣ p₄ := by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd p₄ 3).mp s4
  have hw : w = (c.a : G) ^ k₀ * φ₁⁻¹ := by
    rw [hnf, zpow_eq_inv_of_cube hφ.cube d1, zpow_eq_one_of_cube (hφ.phi2_cube h) d2,
      zpow_eq_one_of_cube hφ.phi3_cube d3, zpow_eq_one_of_cube (hφ.phi4_cube h) d4]
    simp
  have hE2 : phi3 c a₁ φ₁ * ((c.a : G) ^ k₀ * φ₁⁻¹) =
      φ₁⁻¹ * (phi3 c a₁ φ₁ * ((c.a : G) ^ k₀)⁻¹) := by
    have e := hE
    rw [hw, cj_mul_left, ha2k, cj_inv_left] at e
    simpa [mul_inv_rev] using e
  have hA : (c.a : G) ^ k₀ ∈ zpowers (c.a : G) :=
    Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k₀
  have hA1 : (c.a : G) ^ k₀ * φ₁ = φ₁ * (c.a : G) ^ k₀ :=
    mem_zpowers_comm hA (Ctx.a_comm_MG hM1)
  have hAc : ((c.a : G) ^ k₀) * ((c.a : G) ^ k₀) * ((c.a : G) ^ k₀) = 1 := by
    rw [← zpow_add, ← zpow_add, show k₀ + k₀ + k₀ = 3 * k₀ by ring, zpow_mul]
    simp [c.aG_cube]
  refine ⟨k₀, ?_, cj_of_relation hA1 hAc hE2, ?_⟩
  · rw [hu3, hw, hE2, zpow_neg]
    exact (mul_assoc _ _ _).symm
  · have e3 : cj (c.b : G) (phi3 c a₁ φ₁) = (c.b : G) * w⁻¹ := by
      have hu3' : (c.b : G)⁻¹ * phi3 c a₁ φ₁ * (c.b : G) = phi3 c a₁ φ₁ * w := hu3
      calc cj (c.b : G) (phi3 c a₁ φ₁) = (phi3 c a₁ φ₁)⁻¹ * (c.b : G) * phi3 c a₁ φ₁ := rfl
        _ = ((phi3 c a₁ φ₁)⁻¹ * ((c.b : G) * (phi3 c a₁ φ₁ * w))) * w⁻¹ := by group
        _ = ((phi3 c a₁ φ₁)⁻¹ * ((c.b : G) * ((c.b : G)⁻¹ * phi3 c a₁ φ₁ * (c.b : G)))) * w⁻¹ := by
            rw [hu3']
        _ = (c.b : G) * w⁻¹ := by group
    rw [e3, hw]
    have : ((c.a : G) ^ k₀ * φ₁⁻¹)⁻¹ = φ₁ * (c.a : G) ^ (-k₀) := by
      rw [mul_inv_rev, inv_inv, zpow_neg]
    rw [this]

end Phi1

end Certs

end Setup

end CFSG.Sporadic.Recognition.JankoWong
