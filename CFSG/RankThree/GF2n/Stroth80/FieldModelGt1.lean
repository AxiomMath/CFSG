module

public import CFSG.RankThree.GF2n.Stroth80.FieldModelModule
public import CFSG.RankThree.GF2n.Tim79Swap
public import CFSG.RankThree.GF2n.Tim79CentBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80.FieldModel

open scoped commutatorElement Matrix
open Polynomial CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim79 CFSG.Timmesfeld
  CFSG.Timmesfeld.RankOne

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

section Helpers

theorem exists_mul_of_mem_sup' {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', (a'⁻¹ * b * a') * b', B.mul_mem ?_ hb', ?_⟩
        · simpa using hAB a'⁻¹ (A.inv_mem ha') b hb
        · group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, ?_, ?_⟩
        · exact hAB a ha b⁻¹ (B.inv_mem hb)
        · group }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  exact hle hx


abbrev Wg (V : Subgroup G) (g : G) : Subgroup G := V ⊔ conjSubgroup g V

variable (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q)

include H hgV hgQ

theorem CW_normalizes_Q {z : G} (hz : z ∈ Subgroup.centralizer (Wg V g : Set G)) :
    z ∈ Subgroup.normalizer (Q : Set G) :=
  (H.toHyp218 hgV hgQ).M_le_normalizer_Q ((H.toHyp218 hgV hgQ).mem_M_of_mem_centralizer hz)

theorem CW_normalizes_Qg {z : G} (hz : z ∈ Subgroup.centralizer (Wg V g : Set G)) :
    z ∈ Subgroup.normalizer ((conjSubgroup g Q : Subgroup G) : Set G) := by
  have h := H.toHyp218 hgV hgQ
  have hPQ := (h.conclusions H.q4 rfl).2.2.2.1
  have := h.mem_normalizer_Pg (s := z) fun a ha =>
    (Subgroup.mem_centralizer_iff.mp hz a (h.V1_le_W ha)).symm
  rwa [hPQ] at this

theorem comm_P_P' {x y : G} (hx : x ∈ Q ⊓ Subgroup.centralizer (Wg V g : Set G))
    (hy : y ∈ conjSubgroup g Q ⊓ Subgroup.centralizer (Wg V g : Set G)) :
    ⁅x, y⁆ ∈ Q ⊓ conjSubgroup g Q := by
  have hxg := CW_normalizes_Qg H hgV hgQ hx.2
  have hyQ := CW_normalizes_Q H hgV hgQ hy.2
  refine ⟨?_, ?_⟩
  · have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hx.1 ((Subgroup.mem_normalizer_iff.mp hyQ _).mp
      (Subgroup.inv_mem _ hx.1))
  · have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hxg _).mp hy.1)
      (Subgroup.inv_mem _ hy.1)

theorem Hh_normalizes_CW {z : G} (hz : z ∈ Q ⊔ conjSubgroup g Q) :
    ∀ c ∈ Subgroup.centralizer (Wg V g : Set G),
      z * c * z⁻¹ ∈ Subgroup.centralizer (Wg V g : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro w hw
  have hw' : z⁻¹ * w * z ∈ (Wg V g : Subgroup G) := by
    have := (Subgroup.mem_normalizer_iff.mp
      (H.sup_le_normalizer_W hgV hgQ (inv_mem hz)) w).mp hw
    simpa using this
  have h1 := hc _ hw'
  calc w * (z * c * z⁻¹) = z * ((z⁻¹ * w * z) * c) * z⁻¹ := by group
    _ = z * (c * (z⁻¹ * w * z)) * z⁻¹ := by rw [h1]
    _ = z * c * z⁻¹ * w := by group

theorem exists_mul_of_mem_K {r : G}
    (hr : r ∈ (Q ⊔ conjSubgroup g Q) ⊓ Subgroup.centralizer (Wg V g : Set G)) :
    ∃ x ∈ Q ⊓ Subgroup.centralizer (Wg V g : Set G),
      ∃ y ∈ conjSubgroup g Q ⊓ Subgroup.centralizer (Wg V g : Set G), r = x * y := by
  rw [H.centralizer_W_eq_sup hgV hgQ] at hr
  refine exists_mul_of_mem_sup' (fun x hx y hy => ?_) hr
  refine ⟨(Subgroup.mem_normalizer_iff.mp (CW_normalizes_Qg H hgV hgQ hx.2) y).mp hy.1, ?_⟩
  exact Hh_normalizes_CW H hgV hgQ (Subgroup.mem_sup_left hx.1) y hy.2

theorem comm_K_K {a b : G}
    (ha : a ∈ (Q ⊔ conjSubgroup g Q) ⊓ Subgroup.centralizer (Wg V g : Set G))
    (hb : b ∈ (Q ⊔ conjSubgroup g Q) ⊓ Subgroup.centralizer (Wg V g : Set G)) :
    ⁅a, b⁆ ∈ Q ⊓ conjSubgroup g Q := by
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_K H hgV hgQ ha
  obtain ⟨x', hx', y', hy', rfl⟩ := exists_mul_of_mem_K H hgV hgQ hb
  obtain ⟨hWL, -, -, -⟩ := H.L_facts hgV hgQ
  have hLn := H.L_normal hgV hgQ
  have hxy' := comm_P_P' H hgV hgQ hx hy'
  have hyx' : ⁅y, x'⁆ ∈ Q ⊓ conjSubgroup g Q := by
    rw [← commutatorElement_inv]
    exact inv_mem (comm_P_P' H hgV hgQ hx' hy)
  have hxx' : ⁅x, x'⁆ ∈ Q ⊓ conjSubgroup g Q :=
    hWL (Subgroup.mem_sup_left (H.comm_mem_V hx.1 hx'.1))
  have hyy' : ⁅y, y'⁆ ∈ Q ⊓ conjSubgroup g Q :=
    hWL (Subgroup.mem_sup_right (H.comm_mem_conj g hy.1 hy'.1))
  have hx'H : x' ∈ Q ⊔ conjSubgroup g Q := Subgroup.mem_sup_left hx'.1
  have hxH : x ∈ Q ⊔ conjSubgroup g Q := Subgroup.mem_sup_left hx.1
  have e1 : ⁅y, x' * y'⁆ = ⁅y, x'⁆ * (x' * ⁅y, y'⁆ * x'⁻¹) := by
    simp only [commutatorElement_def]; group
  have e2 : ⁅x, x' * y'⁆ = ⁅x, x'⁆ * (x' * ⁅x, y'⁆ * x'⁻¹) := by
    simp only [commutatorElement_def]; group
  have e3 : ⁅x * y, x' * y'⁆ = x * ⁅y, x' * y'⁆ * x⁻¹ * ⁅x, x' * y'⁆ := by
    simp only [commutatorElement_def]; group
  have h1 : ⁅y, x' * y'⁆ ∈ Q ⊓ conjSubgroup g Q := by
    rw [e1]; exact mul_mem hyx' (hLn x' hx'H _ hyy')
  have h2 : ⁅x, x' * y'⁆ ∈ Q ⊓ conjSubgroup g Q := by
    rw [e2]; exact mul_mem hxx' (hLn x' hx'H _ hxy')
  rw [e3]
  exact mul_mem (hLn x hxH _ h1) h2



theorem exists_Q_mul_K {n : ℕ} (N : NatData V Q g n) {x : ↥(Q ⊔ conjSubgroup g Q)}
    (hx : N.φ x ∈ upperUnipotent (GaloisField 2 n)) :
    ∃ q : G, q ∈ Q ∧ q⁻¹ * (x : G) ∈ Subgroup.centralizer (Wg V g : Set G) := by
  have hmem : N.φ x ∈ (Q.subgroupOf (Q ⊔ conjSubgroup g Q)).map N.φ := by
    rw [N.upper]
    exact hx
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hmem
  refine ⟨q, hq, ?_⟩
  have h1 : q⁻¹ * x ∈ N.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqx, inv_mul_cancel]
  rw [N.ker, Subgroup.mem_subgroupOf] at h1
  simpa using h1

theorem V_le_P : V ≤ Q ⊓ Subgroup.centralizer (Wg V g : Set G) := by
  obtain ⟨hWL, hLab, -, -⟩ := H.L_facts hgV hgQ
  intro v hv
  refine ⟨H.V_le_Q hv, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  exact hLab w (hWL hw) v (hWL (Subgroup.mem_sup_left hv))

theorem L_le_P : Q ⊓ conjSubgroup g Q ≤ Q ⊓ Subgroup.centralizer (Wg V g : Set G) := by
  obtain ⟨hWL, hLab, -, -⟩ := H.L_facts hgV hgQ
  intro l hl
  refine ⟨hl.1, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  exact hLab w (hWL hw) l hl



theorem gt1_concrete {n : ℕ} (N : NatData V Q g n) {τ : G} (hτH : τ ∈ Q ⊔ conjSubgroup g Q)
    (hτ10 : ((N.φ ⟨τ, hτH⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) 1 0 = 0)
    (p : ℕ[X]) (hp : p.eval₂ (Nat.castRingHom (GaloisField 2 n))
      (((N.φ ⟨τ, hτH⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) 0 0) = 0)
    {x : G} (hxP : x ∈ Q ⊓ Subgroup.centralizer (Wg V g : Set G)) :
    (((List.range (p.natDegree + 1)).map fun i => (τ ^ i * x * (τ ^ i)⁻¹) ^ p.coeff i).prod)
      ∈ Q ⊓ conjSubgroup g Q := by
  classical
  set Hh : Subgroup G := Q ⊔ conjSubgroup g Q with hHh
  set L : Subgroup G := Q ⊓ conjSubgroup g Q with hLdef
  set CW : Subgroup G := Subgroup.centralizer (Wg V g : Set G) with hCW
  have hQHh : Q ≤ Hh := le_sup_left
  have hLn := H.L_normal hgV hgQ
  obtain ⟨hWL, hLab, -, -⟩ := H.L_facts hgV hgQ
  have hVL : V ≤ L := le_sup_left.trans hWL
  have hcoeComm : ∀ a b : ↥Hh, ((⁅a, b⁆ : ↥Hh) : G) = ⁅(a : G), (b : G)⁆ := fun a b => by
    simp [commutatorElement_def]
  obtain ⟨m, hmH, hm1, -⟩ := H.exists_swap hgV hgQ
  have hP'K : ∀ y ∈ conjSubgroup g Q ⊓ CW, y ∈ Hh ⊓ CW :=
    fun y hy => ⟨Subgroup.mem_sup_right hy.1, hy.2⟩
  have hPK : ∀ y ∈ Q ⊓ CW, y ∈ Hh ⊓ CW := fun y hy => ⟨hQHh hy.1, hy.2⟩
  have hLP : L ≤ Q ⊓ CW := L_le_P H hgV hgQ
  have hVP : V ≤ Q ⊓ CW := V_le_P H hgV hgQ
  have hcommQK : ∀ q ∈ Q, ∀ c ∈ Hh ⊓ CW, ⁅q, c⁆ ∈ Q ⊓ CW := by
    intro q hq c hc
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := exists_mul_of_mem_K H hgV hgQ hc
    have e : ⁅q, x₁ * y₁⁆ = ⁅q, x₁⁆ * (x₁ * ⁅q, y₁⁆ * x₁⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine Subgroup.mul_mem _ (hVP (H.comm_mem_V hq hx₁.1))
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx₁ ?_) (Subgroup.inv_mem _ hx₁))
    have hyQ := CW_normalizes_Q H hgV hgQ hy₁.2
    refine ⟨?_, ?_⟩
    · have e' : ⁅q, y₁⁆ = q * (y₁ * q⁻¹ * y₁⁻¹) := by rw [commutatorElement_def]; group
      rw [e']
      exact Subgroup.mul_mem _ hq
        ((Subgroup.mem_normalizer_iff.mp hyQ _).mp (Subgroup.inv_mem _ hq))
    · have e' : ⁅q, y₁⁆ = (q * y₁ * q⁻¹) * y₁⁻¹ := by rw [commutatorElement_def]
      rw [e']
      exact Subgroup.mul_mem _ (Hh_normalizes_CW H hgV hgQ (hQHh hq) y₁ hy₁.2)
        (Subgroup.inv_mem _ hy₁.2)
  have hmain := gt1_abs N.φ N.surj ((Hh ⊓ CW).subgroupOf Hh) (L.subgroupOf Hh)
    ((Q ⊓ CW).subgroupOf Hh)
    (by
      intro l hl
      exact hLP hl)
    (by
      intro c hc
      exact hPK _ hc)
    (by
      intro z c hc
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ z.2 hc.1) (Subgroup.inv_mem _ z.2), ?_⟩
      exact Hh_normalizes_CW H hgV hgQ z.2 c hc.2)
    (by
      intro z l hl
      exact hLn z z.2 l hl)
    (by
      intro a ha b hb
      show ((⁅a, b⁆ : ↥Hh) : G) ∈ L
      rw [hcoeComm]
      exact comm_K_K H hgV hgQ ha hb)
    (by
      intro z hz c hc
      have hz' : z ∈ N.φ.ker := hz
      rw [N.ker, Subgroup.mem_subgroupOf] at hz'
      show ((⁅z, c⁆ : ↥Hh) : G) ∈ L
      rw [hcoeComm]
      exact comm_K_K H hgV hgQ ⟨z.2, hz'⟩ hc)
    (by
      intro c hc hz
      show (c : G) ∈ L
      have hcG : (c : G) ∈ Hh ⊓ CW := hc
      obtain ⟨x₁, hx₁, y₁, hy₁, hcxy⟩ := exists_mul_of_mem_K H hgV hgQ hcG
      have hxb : ∀ q ∈ Q, ⁅q, y₁⁆ ∈ L := by
        intro q hq
        have h1 := hz ⟨q, hQHh hq⟩
        have h1' : ⁅q, (c : G)⁆ ∈ L := by
          have := h1
          rw [Subgroup.mem_subgroupOf, hcoeComm] at this
          exact this
        rw [hcxy] at h1'
        have e : ⁅q, x₁ * y₁⁆ = ⁅q, x₁⁆ * (x₁ * ⁅q, y₁⁆ * x₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e] at h1'
        have h2 : ⁅q, x₁⁆ ∈ L := hVL (H.comm_mem_V hq hx₁.1)
        have h3 : x₁ * ⁅q, y₁⁆ * x₁⁻¹ ∈ L := by
          have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1'
          rwa [inv_mul_cancel_left] at this
        have h4 := hLn x₁⁻¹ (Subgroup.inv_mem _ (hQHh hx₁.1)) _ h3
        rwa [show x₁⁻¹ * (x₁ * ⁅q, y₁⁆ * x₁⁻¹) * x₁⁻¹⁻¹ = ⁅q, y₁⁆ by group] at h4
      have hyL : y₁ ∈ L := H.mem_L_of_comm_mem hgV hgQ hy₁.1 hxb
      have hmx := hz ⟨m, hmH⟩
      rw [Subgroup.mem_subgroupOf, hcoeComm] at hmx
      rw [hcxy] at hmx
      have e : ⁅m, x₁ * y₁⁆ = ⁅m, x₁⁆ * (x₁ * ⁅m, y₁⁆ * x₁⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e] at hmx
      have hmy : ⁅m, y₁⁆ ∈ L := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (hLn m hmH y₁ hyL) (Subgroup.inv_mem _ hyL)
      have h3 : x₁ * ⁅m, y₁⁆ * x₁⁻¹ ∈ L := by
        have := hLn x₁ (hQHh hx₁.1) _ hmy
        exact this
      have hmx1 : ⁅m, x₁⁆ ∈ L := by
        have := Subgroup.mul_mem _ hmx (Subgroup.inv_mem _ h3)
        rwa [mul_inv_cancel_right] at this
      have hmxL : m * x₁ * m⁻¹ ∈ L := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [show m * x₁ * m⁻¹ = ⁅m, x₁⁆ * x₁ by rw [commutatorElement_def]; group]
          exact Subgroup.mul_mem _ hmx1.1 hx₁.1
        · rw [← hm1, mem_conjSubgroup]
          simpa [mul_assoc] using hx₁.1
      have hx₁L : x₁ ∈ L := by
        have h4 := hLn m⁻¹ (Subgroup.inv_mem _ hmH) _ hmxL
        rwa [show m⁻¹ * (m * x₁ * m⁻¹) * m⁻¹⁻¹ = x₁ by group] at h4
      rw [hcxy]
      exact Subgroup.mul_mem _ hx₁L hyL)
    (by
      intro x x' hx hx' c hc
      show ((⁅x', ⁅x, c⁆⁆ : ↥Hh) : G) ∈ L
      rw [hcoeComm, hcoeComm]
      obtain ⟨q, hq, hr⟩ := exists_Q_mul_K H hgV hgQ N hx
      obtain ⟨q', hq', hr'⟩ := exists_Q_mul_K H hgV hgQ N hx'
      have hrK : q⁻¹ * (x : G) ∈ Hh ⊓ CW :=
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQHh hq)) x.2, hr⟩
      have hr'K : q'⁻¹ * (x' : G) ∈ Hh ⊓ CW :=
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQHh hq')) x'.2, hr'⟩
      have hcK : (c : G) ∈ Hh ⊓ CW := hc
      have hd : ⁅(x : G), (c : G)⁆ ∈ Q ⊓ CW := by
        have e : ⁅(x : G), (c : G)⁆ = q * ⁅q⁻¹ * (x : G), (c : G)⁆ * q⁻¹ * ⁅q, (c : G)⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        have h1 : q * ⁅q⁻¹ * (x : G), (c : G)⁆ * q⁻¹ ∈ L :=
          hLn q (hQHh hq) _ (comm_K_K H hgV hgQ hrK hcK)
        exact Subgroup.mul_mem _ (hLP h1) (hcommQK q hq _ hcK)
      have hdK : ⁅(x : G), (c : G)⁆ ∈ Hh ⊓ CW := hPK _ hd
      have e : ⁅(x' : G), ⁅(x : G), (c : G)⁆⁆ = q' * ⁅q'⁻¹ * (x' : G), ⁅(x : G), (c : G)⁆⁆ * q'⁻¹ *
          ⁅q', ⁅(x : G), (c : G)⁆⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ (hLn q' (hQHh hq') _ (comm_K_K H hgV hgQ hr'K hdK))
        (hVL (H.comm_mem_V hq' hd.1)))
    (by
      intro c hc x hx
      show ((⁅x, c⁆ : ↥Hh) : G) ∈ L
      rw [hcoeComm]
      obtain ⟨q, hq, hr⟩ := exists_Q_mul_K H hgV hgQ N hx
      have hrK : q⁻¹ * (x : G) ∈ Hh ⊓ CW :=
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQHh hq)) x.2, hr⟩
      have hcK : (c : G) ∈ Hh ⊓ CW := hPK _ hc
      have e : ⁅(x : G), (c : G)⁆ = q * ⁅q⁻¹ * (x : G), (c : G)⁆ * q⁻¹ * ⁅q, (c : G)⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ (hLn q (hQHh hq) _ (comm_K_K H hgV hgQ hrK hcK))
        (hVL (H.comm_mem_V hq hc.1)))
    (by
      intro S hLS hSC hSn hC₁S
      refine le_antisymm hSC fun c hc => ?_
      have hcG : (c : G) ∈ Hh ⊓ CW := hc
      obtain ⟨x₁, hx₁, y₁, hy₁, hcxy⟩ := exists_mul_of_mem_K H hgV hgQ hcG
      have hx₁H : x₁ ∈ Hh := hQHh hx₁.1
      have hy₁H : y₁ ∈ Hh := Subgroup.mem_sup_right hy₁.1
      have hx₁S : (⟨x₁, hx₁H⟩ : ↥Hh) ∈ S := hC₁S hx₁
      have hb₁Q : m⁻¹ * y₁ * m ∈ Q := by
        have : y₁ ∈ conjSubgroup m Q := by
          rw [hm1]
          exact hy₁.1
        exact mem_conjSubgroup.mp this
      have hb₁C : m⁻¹ * y₁ * m ∈ CW := by
        have := Hh_normalizes_CW H hgV hgQ (Subgroup.inv_mem _ hmH) y₁ hy₁.2
        simpa using this
      have hb₁H : m⁻¹ * y₁ * m ∈ Hh :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hmH) hy₁H) hmH
      have hb₁S : (⟨m⁻¹ * y₁ * m, hb₁H⟩ : ↥Hh) ∈ S := hC₁S ⟨hb₁Q, hb₁C⟩
      have hyS : (⟨y₁, hy₁H⟩ : ↥Hh) ∈ S := by
        have := hSn ⟨m, hmH⟩ _ hb₁S
        convert this using 1
        ext
        simp [mul_assoc]
      have hcS : c = ⟨x₁, hx₁H⟩ * ⟨y₁, hy₁H⟩ := by
        ext
        exact hcxy
      rw [hcS]
      exact S.mul_mem hx₁S hyS)
    ⟨τ, hτH⟩ hτ10 p hp (c := ⟨x, hQHh hxP.1⟩) hxP
  have hmem := Subgroup.mem_subgroupOf.mp hmain
  have hcoe : ((((List.range (p.natDegree + 1)).map fun i =>
      ((⟨τ, hτH⟩ : ↥Hh) ^ i * (⟨x, hQHh hxP.1⟩ : ↥Hh) * ((⟨τ, hτH⟩ : ↥Hh) ^ i)⁻¹) ^ p.coeff i).prod
        : ↥Hh) : G) =
      ((List.range (p.natDegree + 1)).map fun i => (τ ^ i * x * (τ ^ i)⁻¹) ^ p.coeff i).prod := by
    rw [show ((((List.range (p.natDegree + 1)).map fun i =>
      ((⟨τ, hτH⟩ : ↥Hh) ^ i * (⟨x, hQHh hxP.1⟩ : ↥Hh) * ((⟨τ, hτH⟩ : ↥Hh) ^ i)⁻¹) ^ p.coeff i).prod
        : ↥Hh) : G) = Hh.subtype (((List.range (p.natDegree + 1)).map fun i =>
      ((⟨τ, hτH⟩ : ↥Hh) ^ i * (⟨x, hQHh hxP.1⟩ : ↥Hh) * ((⟨τ, hτH⟩ : ↥Hh) ^ i)⁻¹) ^ p.coeff i).prod)
      from rfl, map_list_prod, List.map_map]
    congr 1
  rw [← hcoe]
  exact hmem

end Helpers

end CFSG.RankThree.GF2n.Stroth80.FieldModel
