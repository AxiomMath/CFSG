module

public import CFSG.Sporadic.Recognition.JankoWongSec4Local
public import CFSG.Sporadic.Recognition.JankoWongSec4Crd
public import CFSG.Sporadic.Recognition.JankoWongLemma17d

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

theorem sq_of_sq_sq {G : Type*} [Group G] {A B z : G} (hz : z * z = 1) (hzA : z * A = A * z)
    (hzB : z * B = B * z) (hA : A * A = z) (hAB : A * B * (A * B) = z) :
    B * A⁻¹ * (B * A⁻¹) = z := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hAinv : A⁻¹ = A * z := by
    calc A⁻¹ = A⁻¹ * (A * A) * z⁻¹ := by rw [hA]; group
      _ = A * z⁻¹ := by group
      _ = A * z := by rw [hzinv]
  have h1 : B * A⁻¹ * (B * A⁻¹) = B * A * B * A * (z * z) := by
    rw [hAinv]
    calc B * (A * z) * (B * (A * z)) = B * A * (z * B) * A * z := by group
      _ = B * A * (B * z) * A * z := by rw [hzB]
      _ = B * A * B * (z * A) * z := by group
      _ = B * A * B * (A * z) * z := by rw [hzA]
      _ = B * A * B * A * (z * z) := by group
  have h2 : B * A * B * A = z := by
    calc B * A * B * A = A⁻¹ * (A * B * (A * B)) * A := by group
      _ = A⁻¹ * z * A := by rw [hAB]
      _ = A⁻¹ * (z * A) := by group
      _ = A⁻¹ * (A * z) := by rw [hzA]
      _ = z := by group
  rw [h1, h2, hz, mul_one]

namespace Setup

variable {G : Type} [Group G] [Finite G] {S : Setup G}

abbrev phi3 (c : Ctx S) (a₁ φ₁ : G) : G := cj φ₁ (c.a2 a₁)

abbrev phi4 (c : Ctx S) (a₁ v φ₁ : G) : G := cj (cj φ₁ v) (c.a2 a₁)

section NoCerts

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} (h : Sec4Hyp c a₁ v v₁)

include h in
theorem Sec4Hyp.a2_comm_a : c.a2 a₁ * (c.a : G) = (c.a : G) * c.a2 a₁ := by
  have e := h.rel.a1_sigma2_comm
  rw [show (c.t : G)⁻¹ * (c.a : G) * (c.t : G) = (c.b : G) from c.cj_a_t] at e
  have := congrArg (fun x => cj x (c.t : G)) e
  simpa [cj_mul_left, Ctx.a2, c.cj_b_t] using this

include h in
theorem Sec4Hyp.a2_mem_Kg : c.a2 a₁ ∈ c.Kg :=
  Subgroup.mem_centralizer_singleton_iff.mpr h.a2_comm_a

theorem Ctx.a_mul_t : (c.a : G) * (c.t : G) = (c.t : G) * (c.b : G) := by
  have h1 := c.cj_a_t
  unfold cj at h1
  calc (c.a : G) * (c.t : G) = (c.t : G) * ((c.t : G)⁻¹ * (c.a : G) * (c.t : G)) := by group
    _ = (c.t : G) * (c.b : G) := by rw [h1]

include h in
theorem Sec4Hyp.b2_rel :
    cj (cj (c.a2 a₁) (c.b : G)) (c.b : G) = c.a2 a₁ * cj (c.a2 a₁) (c.b : G) := by
  have e : cj (cj a₁ (c.a : G)) (c.a : G) = a₁ * cj a₁ (c.a : G) := h.rel.b1_by_sigma1
  have key := congrArg (fun x => cj x (c.t : G)) e
  simp only [cj_mul_left, cj_cj] at key
  have e3 : (c.a : G) * (c.a : G) * (c.t : G) = (c.t : G) * ((c.b : G) * (c.b : G)) := by
    rw [mul_assoc, Ctx.a_mul_t, ← mul_assoc, Ctx.a_mul_t, mul_assoc]
  have l : cj a₁ ((c.a : G) * (c.a : G) * (c.t : G)) =
      cj (cj (cj a₁ (c.t : G)) (c.b : G)) (c.b : G) := by
    rw [e3, cj_mul_right, cj_mul_right]
  have r : cj a₁ ((c.a : G) * (c.t : G)) = cj (cj a₁ (c.t : G)) (c.b : G) := by
    rw [Ctx.a_mul_t, cj_mul_right]
  rw [l, r] at key
  exact key

theorem cj_z_eq {x : G} (hx : x ∈ S.H) : cj S.z x = S.z :=
  cj_eq_self_of_comm (Ctx.zc hx).symm

include h in
theorem Sec4Hyp.b2_mem : cj (c.a2 a₁) (c.b : G) ∈ S.H :=
  S.H.mul_mem (S.H.mul_mem (S.H.inv_mem c.b.2) h.a2_mem) c.b.2

include h in
theorem Sec4Hyp.b2_sq' : cj (c.a2 a₁) (c.b : G) * cj (c.a2 a₁) (c.b : G) = S.z := by
  rw [← pow_two, ← cj_pow_left, h.a2_sq]
  exact cj_z_eq c.b.2

include h in
theorem Sec4Hyp.b2_a2_sq :
    cj (c.a2 a₁) (c.b : G) * (c.a2 a₁)⁻¹ * (cj (c.a2 a₁) (c.b : G) * (c.a2 a₁)⁻¹) = S.z := by
  have hz : S.z * S.z = 1 := by rw [← pow_two]; exact Ctx.z_sq (S := S)
  have hzA : S.z * c.a2 a₁ = c.a2 a₁ * S.z := h.a2_comm_z.symm
  have hzB : S.z * cj (c.a2 a₁) (c.b : G) = cj (c.a2 a₁) (c.b : G) * S.z :=
    (Ctx.zc h.b2_mem).symm
  have hA : c.a2 a₁ * c.a2 a₁ = S.z := by rw [← pow_two]; exact h.a2_sq
  have hAB : c.a2 a₁ * cj (c.a2 a₁) (c.b : G) * (c.a2 a₁ * cj (c.a2 a₁) (c.b : G)) = S.z := by
    rw [← h.b2_rel, ← cj_mul_left, h.b2_sq']
    exact cj_z_eq c.b.2
  exact sq_of_sq_sq hz hzA hzB hA hAB

include h in
theorem Sec4Hyp.a2_mul_a2 : c.a2 a₁ * c.a2 a₁ = S.z := by rw [← pow_two]; exact h.a2_sq

include h in
theorem Sec4Hyp.a2_mul_v : c.a2 a₁ * v = v * (c.a2 a₁)⁻¹ := by
  have e : v⁻¹ * c.a2 a₁ * v = (c.a2 a₁)⁻¹ := h.rel.a2_by_v
  calc c.a2 a₁ * v = v * (v⁻¹ * c.a2 a₁ * v) := by group
    _ = v * (c.a2 a₁)⁻¹ := by rw [e]

namespace Phi1

variable (hφ : Phi1 c φ₁)

include hφ h in
theorem phi3_by_a2 : cj (phi3 c a₁ φ₁) (c.a2 a₁) = φ₁⁻¹ := by
  rw [cj_cj, h.a2_mul_a2, hφ.by_z]

include hφ h in
theorem phi4_by_a2 : cj (phi4 c a₁ v φ₁) (c.a2 a₁) = (cj φ₁ v)⁻¹ := by
  rw [cj_cj, h.a2_mul_a2, hφ.phi2_by_z h]

include hφ h in
theorem phi3_by_z : cj (phi3 c a₁ φ₁) S.z = (phi3 c a₁ φ₁)⁻¹ := by
  rw [cj_cj, h.a2_comm_z, cj_mul_right, hφ.by_z, cj_inv_left]

include hφ h in
theorem phi4_by_z : cj (phi4 c a₁ v φ₁) S.z = (phi4 c a₁ v φ₁)⁻¹ := by
  rw [cj_cj, h.a2_comm_z, cj_mul_right, hφ.phi2_by_z h, cj_inv_left]

include hφ h in
theorem phi3_by_v : cj (phi3 c a₁ φ₁) v = (phi4 c a₁ v φ₁)⁻¹ := by
  rw [cj_cj, h.a2_mul_v, cj_mul_right, h.a2_inv, cj_mul_right]
  exact hφ.phi4_by_z h

include hφ h in
theorem phi4_by_v : cj (phi4 c a₁ v φ₁) v = phi3 c a₁ φ₁ := by
  rw [cj_cj, h.a2_mul_v, cj_mul_right, hφ.phi2_by_v h, cj_inv_left, h.a2_inv, cj_mul_right,
    hφ.phi3_by_z h, inv_inv]

end Phi1

theorem Ctx.a_mem_MG : (c.a : G) ∈ c.MG := c.mem_MG_iff.mpr ⟨c.a_mem_Kg, c.aK_mem_oddCore⟩

theorem Ctx.z_mul_z : S.z * S.z = 1 := by rw [← pow_two]; exact Ctx.z_sq (S := S)

theorem Ctx.zN_conj : ∀ x ∈ c.OG, S.z * x * S.z⁻¹ ∈ c.OG := fun _ hx =>
  c.conj_mem_OG_of_mem_NG c.z_mem_NG hx

omit [Finite G] in
theorem zpow_eq_one_of_cube {x : G} (hx : x ^ 3 = 1) {p : ℤ} (hp : 3 ∣ p) : x ^ p = 1 := by
  obtain ⟨m, rfl⟩ := hp
  rw [zpow_mul]
  simpa using congrArg (fun y => y ^ m) hx

omit [Finite G] in
theorem eq_one_of_mem_negSub {N : Subgroup G} {z w : G} {hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x}
    (hw : w ∈ negSub N z hN) (hw3 : w ^ 3 = 1) (hc : w * z = z * w) : w = 1 := by
  have h1 : z * w * z⁻¹ = w := by
    calc z * w * z⁻¹ = (w * z) * z⁻¹ := by rw [hc]
      _ = w := by group
  have h2 : w = w⁻¹ := h1.symm.trans hw.2
  have h3 : w * w = 1 := mul_eq_one_iff_eq_inv.mpr h2
  calc w = (w * w) * w := by rw [h3, one_mul]
    _ = w ^ 3 := (pow_three' w).symm
    _ = 1 := hw3

end NoCerts

section Certs


namespace Ctx

variable (c : Ctx S)

theorem card_negSub_OG : Nat.card ↥(negSub c.OG S.z c.OG_comm) = 9 := by
  have h81 := c.card_OG_eq_81
  have h := card_eq c.OG S.z c.OG_comm c.OG_pow_three (z_sq (S := S)) c.zN_conj
  have h9 : Nat.card ↥(c.OG ⊓ centralizer ({S.z} : Set G)) = 9 := (c.card_CO_z_t h81).1
  rw [h81, h9] at h
  omega

theorem negSub_le_MG : negSub c.OG S.z c.OG_comm ≤ c.MG := by
  have h81 := c.card_OG_eq_81
  set A : Subgroup G := c.MG ⊓ c.OG with hA
  have hAN : A ≤ c.OG := inf_le_right
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => c.OG_comm x (hAN hx) y (hAN hy)
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := fun x hx => c.OG_pow_three x (hAN hx)
  have hzA : ∀ x ∈ A, S.z * x * S.z⁻¹ ∈ A := fun x hx =>
    ⟨c.MG_conj c.z_mem_Kg hx.1, c.zN_conj x (hAN hx)⟩
  have hcard := card_eq A S.z hAc hA3 (z_sq (S := S)) hzA
  have hA27 : Nat.card A = 27 := c.card_MG_inf_OG_eq
  have hAz : A ⊓ centralizer ({S.z} : Set G) = zpowers (c.a : G) := by
    apply le_antisymm
    · intro y hy
      have hyPG : y ∈ c.PG := by
        rw [← c.CO_z_eq_PG h81]; exact ⟨hy.1.2, hy.2⟩
      exact c.PG_inf_MG_le ⟨hyPG, hy.1.1⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨c.a_mem_MG, c.aG_mem_OG⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr (Ctx.zc c.a.2)⟩
  have hAz3 : Nat.card ↥(A ⊓ centralizer ({S.z} : Set G)) = 3 := by
    rw [hAz, Nat.card_zpowers]; exact c.orderOf_aG
  have hneg9 : Nat.card ↥(negSub A S.z hAc) = 9 := by
    rw [hA27, hAz3] at hcard; omega
  have hle : negSub A S.z hAc ≤ negSub c.OG S.z c.OG_comm := fun y hy => ⟨hAN hy.1, hy.2⟩
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hneg9, c.card_negSub_OG])
  intro y hy
  rw [← heq] at hy
  exact hy.1.1

end Ctx

namespace Phi1

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} (hφ : Phi1 c φ₁) (h : Sec4Hyp c a₁ v v₁)

include hφ in
theorem mem_Q : φ₁ ∈ negSub c.OG S.z c.OG_comm := by
  refine ⟨hφ.mem, ?_⟩
  have e := hφ.by_z
  rw [cj, Ctx.zG_inv (S := S)] at e
  rw [Ctx.zG_inv (S := S)]
  exact e

include hφ h in
theorem phi2_mem_Q : cj φ₁ v ∈ negSub c.OG S.z c.OG_comm := by
  refine ⟨hφ.phi2_mem h, ?_⟩
  have e := hφ.phi2_by_z h
  rw [cj, Ctx.zG_inv (S := S)] at e
  rw [Ctx.zG_inv (S := S)]
  exact e

include hφ in
theorem phi1_mem_MG : φ₁ ∈ c.MG := c.negSub_le_MG hφ.mem_Q

include hφ h in
theorem phi2_mem_MG : cj φ₁ v ∈ c.MG := c.negSub_le_MG (hφ.phi2_mem_Q h)

include hφ h in
theorem phi3_mem_MG : phi3 c a₁ φ₁ ∈ c.MG := by
  have := c.MG_conj (c.Kg.inv_mem h.a2_mem_Kg) hφ.phi1_mem_MG
  simpa [cj] using this

include hφ h in
theorem phi4_mem_MG : phi4 c a₁ v φ₁ ∈ c.MG := by
  have := c.MG_conj (c.Kg.inv_mem h.a2_mem_Kg) (hφ.phi2_mem_MG h)
  simpa [cj] using this

include hφ h in
theorem phi12_comm : φ₁ * cj φ₁ v = cj φ₁ v * φ₁ := c.OG_comm _ hφ.mem _ (hφ.phi2_mem h)

include hφ h in
theorem phi34_comm : phi3 c a₁ φ₁ * phi4 c a₁ v φ₁ = phi4 c a₁ v φ₁ * phi3 c a₁ φ₁ := by
  have := congrArg (fun x => cj x (c.a2 a₁)) (hφ.phi12_comm h)
  simpa only [cj_mul_left] using this

include hφ in
theorem phi3_cube : (phi3 c a₁ φ₁) ^ 3 = 1 := by
  rw [← cj_pow_left, hφ.cube, cj_one_left]

include hφ h in
theorem phi4_cube : (phi4 c a₁ v φ₁) ^ 3 = 1 := by
  rw [← cj_pow_left, hφ.phi2_cube h, cj_one_left]

include hφ h in
theorem indepN (q₃ q₄ : ℤ)
    (hN : phi3 c a₁ φ₁ ^ q₃ * phi4 c a₁ v φ₁ ^ q₄ ∈ c.OG) : 3 ∣ q₃ ∧ 3 ∣ q₄ := by
  have h81 := c.card_OG_eq_81
  have hQ := hφ.mem_Q
  have hQ2 := hφ.phi2_mem_Q h
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup G, Q = negSub c.OG S.z c.OG_comm := ⟨_, rfl⟩
  rw [← hQdef] at hQ hQ2
  have hQN : ∀ y ∈ Q, y ∈ c.OG := fun y hy => by rw [hQdef] at hy; exact hy.1
  have hQ3 : ∀ y ∈ Q, y ^ 3 = 1 := fun y hy => c.OG_pow_three y (hQN y hy)
  have hQ1 : ∀ y ∈ Q, y * S.z = S.z * y → y = 1 := fun y hy hc => by
    have hy' : y ∈ negSub c.OG S.z c.OG_comm := by rw [← hQdef]; exact hy
    exact eq_one_of_mem_negSub hy' (hQ3 y hy) hc
  obtain ⟨x, hx⟩ : ∃ x : G, x = φ₁ ^ q₃ * (cj φ₁ v) ^ q₄ := ⟨_, rfl⟩
  have hy : cj x (c.a2 a₁) = phi3 c a₁ φ₁ ^ q₃ * phi4 c a₁ v φ₁ ^ q₄ := by
    rw [hx, cj_mul_left, cj_zpow_left, cj_zpow_left]
  have hxQ : x ∈ Q := by rw [hx]; exact Q.mul_mem (Q.zpow_mem hQ q₃) (Q.zpow_mem hQ2 q₄)
  have hxN : x ∈ c.OG := hQN x hxQ
  have hyN : cj x (c.a2 a₁) ∈ c.OG := by rw [hy]; exact hN
  have hbN : (c.b : G) ∈ c.OG := c.PG_le_OG h81 c.bG_mem_PG
  have hbx : x * (c.b : G) = (c.b : G) * x := c.OG_comm x hxN _ hbN
  have hby : cj x (c.a2 a₁) * (c.b : G) = (c.b : G) * cj x (c.a2 a₁) := c.OG_comm _ hyN _ hbN
  have hb₂ : cj x (cj (c.a2 a₁) (c.b : G)) = cj x (c.a2 a₁) := by
    have e1 : cj x (c.b : G)⁻¹ = x := cj_eq_self_of_comm (by
      calc x * (c.b : G)⁻¹ = (c.b : G)⁻¹ * ((c.b : G) * x) * (c.b : G)⁻¹ := by group
        _ = (c.b : G)⁻¹ * (x * (c.b : G)) * (c.b : G)⁻¹ := by rw [hbx]
        _ = (c.b : G)⁻¹ * x := by group)
    have e2 : cj (cj x (c.a2 a₁)) (c.b : G) = cj x (c.a2 a₁) := cj_eq_self_of_comm hby
    calc cj x (cj (c.a2 a₁) (c.b : G)) = cj (cj (cj x (c.b : G)⁻¹) (c.a2 a₁)) (c.b : G) := by
          unfold cj; group
      _ = cj x (c.a2 a₁) := by rw [e1, e2]
  obtain ⟨g, hgdef⟩ : ∃ g : G, g = cj (c.a2 a₁) (c.b : G) * (c.a2 a₁)⁻¹ := ⟨_, rfl⟩
  have hg : cj x g = x := by
    rw [hgdef, cj_mul_right, hb₂, cj_cj_inv]
  have hcomm : x * g = g * x := comm_of_cj_eq hg
  have hgg : g * g = S.z := by rw [hgdef]; exact h.b2_a2_sq
  have hxz : x * S.z = S.z * x :=
    calc x * S.z = x * (g * g) := by rw [hgg]
      _ = (x * g) * g := (mul_assoc x g g).symm
      _ = (g * x) * g := by rw [hcomm]
      _ = g * (x * g) := mul_assoc g x g
      _ = g * (g * x) := by rw [hcomm]
      _ = (g * g) * x := (mul_assoc g g x).symm
      _ = S.z * x := by rw [hgg]
  have hx1 : x = 1 := hQ1 x hxQ hxz
  exact hφ.indep12 h q₃ q₄ (by rw [← hx]; exact hx1)

include hφ h in
theorem indep4 (p₁ p₂ p₃ p₄ : ℤ)
    (hmem : φ₁ ^ p₁ * (cj φ₁ v) ^ p₂ * (phi3 c a₁ φ₁) ^ p₃ * (phi4 c a₁ v φ₁) ^ p₄ ∈
      zpowers (c.a : G)) : 3 ∣ p₁ ∧ 3 ∣ p₂ ∧ 3 ∣ p₃ ∧ 3 ∣ p₄ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hQ := hφ.mem_Q
  have hQ2 := hφ.phi2_mem_Q h
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup G, Q = negSub c.OG S.z c.OG_comm := ⟨_, rfl⟩
  rw [← hQdef] at hQ hQ2
  have hQN : ∀ y ∈ Q, y ∈ c.OG := fun y hy => by rw [hQdef] at hy; exact hy.1
  have hQ3 : ∀ y ∈ Q, y ^ 3 = 1 := fun y hy => c.OG_pow_three y (hQN y hy)
  have hQ1 : ∀ y ∈ Q, y * S.z = S.z * y → y = 1 := fun y hy hc => by
    have hy' : y ∈ negSub c.OG S.z c.OG_comm := by rw [← hQdef]; exact hy
    exact eq_one_of_mem_negSub hy' (hQ3 y hy) hc
  obtain ⟨w, hw⟩ : ∃ w : G, w = φ₁ ^ p₁ * (cj φ₁ v) ^ p₂ := ⟨_, rfl⟩
  have hwQ : w ∈ Q := by rw [hw]; exact Q.mul_mem (Q.zpow_mem hQ p₁) (Q.zpow_mem hQ2 p₂)
  have hwN : w ∈ c.OG := hQN w hwQ
  have hkw : (c.a : G) ^ k = w * (phi3 c a₁ φ₁ ^ p₃ * phi4 c a₁ v φ₁ ^ p₄) := by
    rw [hw]; exact hk.trans (mul_assoc _ _ _)
  have hyN : phi3 c a₁ φ₁ ^ p₃ * phi4 c a₁ v φ₁ ^ p₄ ∈ c.OG := by
    have : phi3 c a₁ φ₁ ^ p₃ * phi4 c a₁ v φ₁ ^ p₄ = w⁻¹ * (c.a : G) ^ k := by
      rw [hkw]; group
    rw [this]
    exact c.OG.mul_mem (c.OG.inv_mem hwN) (c.OG.zpow_mem c.aG_mem_OG k)
  obtain ⟨hp3, hp4⟩ := hφ.indepN h p₃ p₄ hyN
  have hφ3 : phi3 c a₁ φ₁ ^ p₃ = 1 := zpow_eq_one_of_cube hφ.phi3_cube hp3
  have hφ4 : phi4 c a₁ v φ₁ ^ p₄ = 1 := zpow_eq_one_of_cube (hφ.phi4_cube h) hp4
  have hwa : w = (c.a : G) ^ k := by
    rw [hkw, hφ3, hφ4, mul_one, mul_one]
  have hwz : w * S.z = S.z * w := by
    rw [hwa]
    exact ((show Commute (c.a : G) S.z from Ctx.zc c.a.2).zpow_left k).eq
  have hw1 : w = 1 := hQ1 w hwQ hwz
  obtain ⟨hp1, hp2⟩ := hφ.indep12 h p₁ p₂ (by rw [← hw]; exact hw1)
  exact ⟨hp1, hp2, hp3, hp4⟩

include hφ h in
theorem heis4Data {W : Subgroup G} (hW : c.IsW W) :
    Heis4Data (⟨(c.a : G), c.a_mem_MG⟩ : c.MG) ⟨φ₁, hφ.phi1_mem_MG⟩
      ⟨cj φ₁ v, hφ.phi2_mem_MG h⟩ ⟨phi3 c a₁ φ₁, hφ.phi3_mem_MG h⟩
      ⟨phi4 c a₁ v φ₁, hφ.phi4_mem_MG h⟩ := by
  have hE := c.isExtraspecialThree_MG hW
  have hmemz : ∀ m : c.MG, m ∈ zpowers (⟨(c.a : G), c.a_mem_MG⟩ : c.MG) ↔
      (m : G) ∈ zpowers (c.a : G) := by
    intro m
    constructor
    · rintro hm
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
        have := congrArg Subtype.val hk
        simpa using this⟩
    · intro hm
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  refine ⟨by rw [hE.card]; norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext (by simpa using c.aG_cube)
  · exact fun e => c.aG_ne_one (congrArg Subtype.val e)
  · intro x
    have := (hE.center (c.a : G) c.a_mem_MG).mpr (Subgroup.mem_zpowers _) x x.2
    exact Subtype.ext this.symm
  · intro x
    exact Subtype.ext (by simpa using hE.exponent x x.2)
  · intro x y
    exact (hmemz _).mpr (hE.commutator x x.2 y y.2)
  · intro p₁ p₂ p₃ p₄ hmem
    refine hφ.indep4 h p₁ p₂ p₃ p₄ ?_
    have := (hmemz _).mp hmem
    simpa using this

include hφ h in
theorem normal_form {W : Subgroup G} (hW : c.IsW W) {m : G} (hm : m ∈ c.MG) :
    ∃ k p₁ p₂ p₃ p₄ : ℤ, m = (c.a : G) ^ k * φ₁ ^ p₁ * (cj φ₁ v) ^ p₂ *
      phi3 c a₁ φ₁ ^ p₃ * phi4 c a₁ v φ₁ ^ p₄ := by
  obtain ⟨k, p₁, p₂, p₃, p₄, hk⟩ := (hφ.heis4Data h hW).exists_normal_form ⟨m, hm⟩
  exact ⟨k, p₁, p₂, p₃, p₄, by simpa using congrArg Subtype.val hk⟩

include hφ h in
theorem exists_crd {W : Subgroup G} (hW : c.IsW W) :
    ∃ crd : c.MG →* Multiplicative (Fin 4 → ZMod 3),
      Function.Surjective crd ∧ (∀ m : c.MG, crd m = 1 ↔ (m : G) ∈ zpowers (c.a : G)) ∧
      crd ⟨φ₁, hφ.phi1_mem_MG⟩ = Multiplicative.ofAdd (Pi.single 0 1) ∧
      crd ⟨cj φ₁ v, hφ.phi2_mem_MG h⟩ = Multiplicative.ofAdd (Pi.single 1 1) ∧
      crd ⟨phi3 c a₁ φ₁, hφ.phi3_mem_MG h⟩ = Multiplicative.ofAdd (Pi.single 2 1) ∧
      crd ⟨phi4 c a₁ v φ₁, hφ.phi4_mem_MG h⟩ = Multiplicative.ofAdd (Pi.single 3 1) := by
  obtain ⟨crd, hs, hker, h1, h2, h3, h4⟩ := (hφ.heis4Data h hW).exists_crd
  refine ⟨crd, hs, fun m => ?_, h1, h2, h3, h4⟩
  rw [hker m]
  constructor
  · intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      have := congrArg Subtype.val hk
      simpa using this⟩
  · intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

end Phi1

end Certs

end Setup

end CFSG.Sporadic.Recognition.JankoWong
