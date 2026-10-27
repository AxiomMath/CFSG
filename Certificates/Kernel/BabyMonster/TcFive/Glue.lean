
module

public import CFSG.Sporadic.Bridge.BTcData
public import CFSG.Monster.B.Pinned.Primes.FiveWords
public import Certificates.Kernel.BabyMonster.TcFive.Mem
public import Certificates.Kernel.BabyMonster.TcFive.Facts
public import Certificates.Kernel.BabyMonster.FiveA.CoverB
public import Certificates.Kernel.BabyMonster.FiveA.Facts13625
public import Certificates.Kernel.BabyMonster.PcFive.Census
public import Certificates.Kernel.BabyMonster.Seeds
public import CFSG.Monster.B.TwoA.Unitary.LinThree

public section

namespace CertificateChecks.KernelBM.TcFive

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.KC.BM.PcFive CFSG.Monster.B CFSG.Blueprint
  CFSG.Sporadic.Bridge.B CertificateChecks.KernelBM.FiveA CertificateChecks.KernelBM.Five
open CFSG.Monster.B.Pinned (xFive hFive qFive zFive)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "SB" => NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1
  NativeSporadic.BSeed2

set_option maxRecDepth 100000

theorem pow_eq_one_of_mem {X : MatB} (hX : X ∈ SB) :
    ∃ n, n ≠ 0 ∧ X ^ n = 1 := by
  have hU : SB ≤ IsUnit.submonoid MatB := by
    refine Submonoid.closure_le.2 ?_
    rintro _ (rfl | hy)
    · exact ⟨⟨genA₁, genA₁, genA₁_mul_self, genA₁_mul_self⟩, rfl⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨⟨genA₂, genA₂ * genA₂, by rw [← mul_assoc]; exact genA₂_cube, genA₂_cube⟩, rfl⟩
  obtain ⟨u, rfl⟩ := hU hX
  have : Finite MatBˣ :=
    Finite.of_injective (fun u : MatBˣ => (u : MatB)) (fun _ _ h => Units.ext h)
  refine ⟨orderOf u, (orderOf_pos u).ne', ?_⟩
  rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]

theorem bMat_q (i : Fin 4) : bMat (qFive i) = ((qW xU hU i : MatBˣ) : MatB) := by
  rw [qFive_eq, bMat_qW]

theorem bMat_z : bMat zFive = stripMat CFSG.KC.BM.Five.Z := by
  rw [zFive_eq, bMat_zW]

theorem bMat_u : bMat (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) =
    stripMat CFSG.KC.BM.TcFive.U := by
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, bMat_q, bMat_q, bMat_q, bMat_z, cq1, cq2, cq3,
    u_eq, c2, z4]

theorem mem_SB_Q : ∀ a ∈ [Seeds.A1, Seeds.A2, CFSG.KC.BM.Five.Q2, CFSG.KC.BM.Five.Q3,
    CFSG.KC.BM.Five.Q4, CFSG.KC.BM.Five.Z], stripMat a ∈ SB := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← CertificateChecks.KernelBM.genA₁_eq_stripMat]
    exact Submonoid.subset_closure (Set.mem_insert _ _)
  · rw [← CertificateChecks.KernelBM.genA₂_eq_stripMat]
    exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
  · rw [← cq1, ← bMat_q]
    exact bMat_mem _
  · rw [← cq2, ← bMat_q]
    exact bMat_mem _
  · rw [← cq3, ← bMat_q]
    exact bMat_mem _
  · rw [← bMat_z]
    exact bMat_mem _

theorem u_nf : qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4 =
    nfQ (qW xFive hFive) (zW xFive hFive) ⟨0, 1, 2, 1, 4⟩ := by
  simp only [nfQ, pow_zero, pow_one, one_mul, qFive_eq, zFive_eq]

theorem nf_z (a : ℕ) : zFive ^ a = nfQ (qW xFive hFive) (zW xFive hFive) ⟨0, 0, 0, 0, a⟩ := by
  simp only [nfQ, pow_zero, one_mul, zFive_eq]

theorem nf_q0 (b : ℕ) :
    qFive 0 ^ b = nfQ (qW xFive hFive) (zW xFive hFive) ⟨b, 0, 0, 0, 0⟩ := by
  simp only [nfQ, pow_zero, mul_one, qFive_eq]

theorem enc_ne' : ∀ a b c : Fin 5, (b.val ≠ 0 ∨ c.val ≠ 0) →
    encQ (mulQ cmFive (mulQ cmFive ⟨0, 0, 0, 0, a.val⟩ ⟨b.val, 0, 0, 0, 0⟩)
      (powQ cmFive ⟨0, 1, 2, 1, 4⟩ c.val)) ≠ 0 := by
  decide +kernel

theorem enc_ne (a : ℕ) (ha : a < 5) (b : ℕ) (hb : b < 5) (c : ℕ) (hc : c < 5)
    (hbc : b ≠ 0 ∨ c ≠ 0) :
    encQ (mulQ cmFive (mulQ cmFive ⟨0, 0, 0, 0, a⟩ ⟨b, 0, 0, 0, 0⟩)
      (powQ cmFive ⟨0, 1, 2, 1, 4⟩ c)) ≠ 0 :=
  enc_ne' ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ hbc

theorem u_facts : (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) ^ 5 = 1 ∧
    (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) * qFive 0 =
      qFive 0 * (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) ∧
    ∀ a b c : ℕ, a < 5 → b < 5 → c < 5 → (b ≠ 0 ∨ c ≠ 0) →
      zFive ^ a * qFive 0 ^ b * (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) ^ c ≠ 1 := by
  have R := fiveRel_B
  have H := R.pcHyp
  have := CFSG.Monster.B.Pinned.finite_B
  have e0 : qFive 0 = nfQ (qW xFive hFive) (zW xFive hFive) ⟨1, 0, 0, 0, 0⟩ := by
    have := nf_q0 1
    rwa [pow_one] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [u_nf, nfQ_pow H.rel]
    exact nfQ_one
  · rw [u_nf, e0, nfQ_mul H.rel, nfQ_mul H.rel]
    rfl
  · intro a b c ha hb hc hbc h
    rw [u_nf, nf_z, nf_q0, nfQ_pow H.rel, nfQ_mul H.rel, nfQ_mul H.rel] at h
    set v := mulQ cmFive (mulQ cmFive ⟨0, 0, 0, 0, a⟩ ⟨b, 0, 0, 0, 0⟩)
      (powQ cmFive ⟨0, 1, 2, 1, 4⟩ c) with hv
    have hred : v.red := mulQ_red _ _ _
    have hlt := encQ_lt hred
    have h1 : psi xFive (qW xFive hFive) (zW xFive hFive) (dec (encQ v)) =
        psi xFive (qW xFive hFive) (zW xFive hFive) (dec 0) := by
      rw [psi_dec_Q hlt, decQ_encQ hred, h, psi_dec_Q (by norm_num)]
      simp [nfQ, decQ]
    exact enc_ne a ha b hb c hc hbc
      (psi_dec_inj (i := encQ v) (j := 0) H CertificateChecks.KernelBM.PcFive.phiOK_true R.z1
        (by omega) (by norm_num) h1)

theorem fact9726 :
    (∀ i : Fin 4, hFive⁻¹ * qFive i * hFive =
      (List.ofFn fun j => qFive j ^ (tcHR.getD i []).getD j 0).prod * zFive ^ tcHC.getD i 0) ∧
    (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) ^ 5 = 1 ∧
    (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) * qFive 0 =
      qFive 0 * (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) ∧
    (∀ a b c : ℕ, a < 5 → b < 5 → c < 5 → (b ≠ 0 ∨ c ≠ 0) →
      zFive ^ a * qFive 0 ^ b * (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) ^ c ≠ 1) ∧
    ∃ e : NativeSporadic.B, e * qFive 0 = qFive 0 * e ∧
      e * (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) =
        (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) * e ∧
      ∃ a ∈ Subgroup.closure ({xFive, hFive, e} : Set NativeSporadic.B),
        ∃ b ∈ Subgroup.closure ({xFive, hFive, e} : Set NativeSporadic.B),
          ∃ G Gi : MatB, G * Gi = 1 ∧ genA₁ * G = G * bMat a ∧ genA₂ * G = G * bMat b := by
  obtain ⟨u5, uq, ind⟩ := u_facts
  have mE := e_mem.2 SB mem_SB_Q _ (List.mem_singleton_self _)
  obtain ⟨n, hn, hpow⟩ := pow_eq_one_of_mem mE
  obtain ⟨e, ve⟩ : ∃ e : NativeSporadic.B, bMat e = stripMat CFSG.KC.BM.TcFive.E :=
    ⟨seedUnit mE hn hpow, bMat_seedUnit _ _ _⟩
  have hact : ∀ i : Fin 4, hFive⁻¹ * qFive i * hFive =
      (List.ofFn fun j => qFive j ^ (tcHR.getD i []).getD j 0).prod * zFive ^ tcHC.getD i 0 := by
    have e1 : tcHR = CFSG.RankThree.Native.bFiveHRows := rfl
    have e2 : tcHC = CFSG.RankThree.Native.bFiveHC := rfl
    rw [e1, e2]
    exact fact8120.1
  have he0 : bMat e * bMat (qFive 0) = bMat (qFive 0) * bMat e := by
    rw [ve, bMat_q, cq0]
    exact e_q0
  have heu : bMat e * bMat (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) =
      bMat (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) * bMat e := by
    rw [ve, bMat_u]
    exact e_u
  refine ⟨hact, u5, uq, ind, e, comm_of_bMat he0, comm_of_bMat heu, ?_⟩
  set H := Subgroup.closure ({xFive, hFive, e} : Set NativeSporadic.B)
  have hsrc : ∀ t ∈ [CFSG.KC.BM.Five.f85, CFSG.KC.BM.Five.f86, CFSG.KC.BM.TcFive.E],
      stripMat t ∈ H.toSubmonoid.map bMat := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨xFive, Subgroup.subset_closure (by simp), five_bridge.1⟩
    · exact ⟨hFive, Subgroup.subset_closure (by simp), five_bridge.2⟩
    · exact ⟨e, Subgroup.subset_closure (by simp), ve⟩
  obtain ⟨a, ha, hav⟩ := ab_mem.2 _ hsrc CFSG.KC.BM.TcFive.AP (by simp)
  obtain ⟨b, hb, hbv⟩ := ab_mem.2 _ hsrc CFSG.KC.BM.TcFive.BP (by simp)
  refine ⟨a, ha, b, hb, stripMat CFSG.KC.BM.TcFive.G, stripMat CFSG.KC.BM.TcFive.Gi, conj_i, ?_,
    ?_⟩
  · rw [CertificateChecks.KernelBM.genA₁_eq_stripMat, hav]
    exact conj_a
  · rw [CertificateChecks.KernelBM.genA₂_eq_stripMat, hbv]
    exact conj_b

end CertificateChecks.KernelBM.TcFive

end
