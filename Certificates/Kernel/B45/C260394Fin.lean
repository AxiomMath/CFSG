module

public import Certificates.Kernel.B45.C260394Srch
public import Certificates.Kernel.B45.C260394Z0
public import Certificates.Kernel.B45.C260394Z1
public import Certificates.Kernel.B45.C260394Z2
public import CFSG.Certificates.Kernel.B45RuSylDblSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuPerm
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion

public section

set_option Elab.async false

#kon_join CertificateChecks.KernelB45.C260394.dblAll CertificateChecks.KernelB45.C260394.dblB 10

namespace CertificateChecks.KernelB45.C260394

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.TCP
  CFSG.KC.InvTabK CFSG.KC.B45P.RuSyl CFSG.KC.B45P.RuSylS CFSG.KC.B45P.RuSylD
  CertificateChecks.KernelMisc CertificateChecks.KernelSporSch.RuG CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Quasithin.B45Exc.Tab
  CFSG.QuasithinUnique.Bridge.RuExcl CFSG.KS.Raw.Orb

theorem wn_le : Nat.ble (WN 0) 120 = true := by quickRfl

theorem gens_eq : unpackP 4060 12 [A0, A1] [A0I, A1I] = [ruA0P, ruA1P] := by
  unfold ruA0P ruA1P
  rw [(inv_of a0_eq pA0).1, (inv_of a1_eq pA1).1, a0_eq, a1_eq]
  rfl

theorem dbl_of {k : Nat} (hk : k < WN 0) :
    idK 4060 12 (mask 12) = true ∧ gensTc 4060 12 [A0, A1] [A0I, A1I] = true ∧
      dblC RuSqS.TR CD (roff 4060 48720 (RuSqS.LR 0)) (roff 4060 48720 (RuSqS.LR 1))
        (pidn 4060 12) [A0, A1] [A0I, A1I] (quadC WQ k) (wdOf k) = true := by
  have hw := Nat.le_of_ble_eq_true wn_le
  have hq : k / 12 < 10 := by omega
  have h := dblAll (k / 12) hq
  unfold dblB at h
  rw [CFSG.KC.B45P.RuSylS.bAnd_eq, CFSG.KC.B45P.RuSylS.bAnd_eq, CFSG.KC.LQT.TCK.sB,
    CFSG.KC.LQT.TCK.sB, CFSG.KC.LQT.TCK.sB, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h⟩ := h
  have h3 := allN_spec h (k % 12) (Nat.mod_lt _ (by norm_num))
  beta_reduce at h3
  have e : Nat.add (Nat.mul 12 (k / 12)) (k % 12) = k := Nat.div_add_mod k 12
  rw [e] at h3
  have hb : Nat.blt k (WN 0) = true := by rw [Nat.blt_eq]; exact hk
  rw [hb] at h3
  exact ⟨h1, h2, h3⟩


noncomputable abbrev Xc : ℕ → Equiv.Perm (Fin 4060) := CFSG.KC.B45P.RuSylS.X (lT 0) (lT 1) CD

theorem hT0 : ∀ a < 2048, PRep 4060 12 (RuSqS.TR (Nat.add (roff 4060 48720 (RuSqS.LR 0)) a))
    (lT 0 a) := fun a ha => hT (by norm_num) (by rw [hc.1]; exact ha)

theorem hT1 : ∀ b < 8, PRep 4060 12 (RuSqS.TR (Nat.add (roff 4060 48720 (RuSqS.LR 1)) b))
    (lT 1 b) := fun b hb => hT (by norm_num) (by rw [hc.2]; exact hb)

theorem hgen : ∀ g ∈ ruS, ∃ a < 2048, ∃ b < 8, g = lT 0 a * lT 1 b := fun g hg =>
  hgen' (by rw [ruChainS4060_sub]; exact hg)

theorem hin : ∀ a < 2048, ∀ b < 8, lT 0 a * lT 1 b ∈ ruS := fun a ha b hb => by
  rw [← ruChainS4060_sub]
  exact hin' ha hb

theorem tabXc : TabSpec 495 (cK CM) (pK PR) Xc :=
  ⟨fun _ hi => x_one hi, fun _ hi _ hj => x_inj hT0 hT1 hcov hinv hk hi hj,
    x_comm hT0 hT1 hgen hin hcov hinv hrow hk,
    fun _ hi _ hj => x_prod hT0 hT1 hgen hin hcov hinv hrow hk hi hj⟩

theorem covXc : ∀ x ∈ ruS, x * x = 1 → (fixFinset x).card = 92 → ∃ i < 495, x = Xc i :=
  fun _ hx h2 h92 => x_cover hT0 hT1 hgen hin hcov hinv hk hx h2 h92

theorem xP_rep : ∀ i < 495, PRep 4060 12 (xP RuSqS.TR (roff 4060 48720 (RuSqS.LR 0))
    (roff 4060 48720 (RuSqS.LR 1)) (CD i)) (Xc i) := fun i hi => by
  have hcd := (inv_parts (hinv i hi)).1
  obtain ⟨ha, hb⟩ := code_lt hcd
  have e : Xc i = lT 0 (Nat.shiftRight (CD i) 3) * lT 1 (Nat.land (CD i) 7) := by
    simp only [Xc, CFSG.KC.B45P.RuSylS.X, if_pos hi, sig]
  rw [e]
  exact prep_pcomp (by norm_num) (hT0 _ ha) (hT1 _ hb)

theorem wit_ord {k : Nat} (hk : k < WN 0) : (∀ t < 4, quadC WQ k t < 495) ∧ ∃ G ∈ ruP,
    (Xc (quadC WQ k 0) * (G * Xc (quadC WQ k 1) * G⁻¹) * Xc (quadC WQ k 2) *
      (G * Xc (quadC WQ k 3) * G⁻¹)) ^ 29 = 1 ∧
    Xc (quadC WQ k 0) * (G * Xc (quadC WQ k 1) * G⁻¹) * Xc (quadC WQ k 2) *
      (G * Xc (quadC WQ k 3) * G⁻¹) ≠ 1 := by
  obtain ⟨h1, h2, h3⟩ := dbl_of hk
  obtain ⟨hlt, g, hg, h29, hne⟩ := dblC_sound h1 h2 xP_rep h3
  rw [gens_eq] at hg
  obtain ⟨G, hG, hGr⟩ := regIn_ruP.word (wdOf k)
  have e : g = G := hg.1.unique hGr.1
  rw [e] at h29 hne
  exact ⟨hlt, G, hG, h29, hne⟩

theorem dbl5 {B : Subgroup (Equiv.Perm (Fin 4060))} (hBS : B ≤ ruS)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (h2A : ∀ x ∈ B, x ≠ 1 → (fixFinset x).card = 92) (hcard : Nat.card B = 2 ^ 5) :
    ∃ x₁ ∈ B, ∃ x₂ ∈ B, ∃ x₃ ∈ B, ∃ x₄ ∈ B, ∃ G ∈ ruP,
      (x₁ * (G * x₂ * G⁻¹) * x₃ * (G * x₄ * G⁻¹)) ^ 29 = 1 ∧
        x₁ * (G * x₂ * G⁻¹) * x₃ * (G * x₄ * G⁻¹) ≠ 1 := by
  obtain ⟨k, hk, hmem⟩ := wit_mem tabXc covXc hBS hcomm hsq h2A hcard
  obtain ⟨-, G, hG, h29, hne⟩ := wit_ord hk
  exact ⟨_, hmem 0 (by norm_num), _, hmem 1 (by norm_num), _, hmem 2 (by norm_num), _,
    hmem 3 (by norm_num), G, hG, h29, hne⟩

theorem ru_syl : ∀ B : Subgroup (Equiv.Perm (Fin 4060)), B ≤ ruS →
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
    (∀ x ∈ B, x ≠ 1 → (fixFinset x).card = 92) →
    Nat.card B ≤ 2 ^ 6 ∧ (Nat.card B = 2 ^ 5 ∨ Nat.card B = 2 ^ 6 →
      ∃ x₁ ∈ B, ∃ x₂ ∈ B, ∃ x₃ ∈ B, ∃ x₄ ∈ B, ∃ G ∈ ruP,
        (x₁ * (G * x₂ * G⁻¹) * x₃ * (G * x₄ * G⁻¹)) ^ 29 = 1 ∧
          x₁ * (G * x₂ * G⁻¹) * x₃ * (G * x₄ * G⁻¹) ≠ 1) := by
  intro B hBS hcomm hsq h2A
  refine ⟨card_le tabXc covXc hBS hcomm hsq h2A, fun hcard => ?_⟩
  rcases hcard with h5 | h6
  · exact dbl5 hBS hcomm hsq h2A h5
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 5) (G := ↥B)
      (by rw [h6]; exact Nat.pow_dvd_pow 2 (by norm_num))
    set B' : Subgroup (Equiv.Perm (Fin 4060)) := K.map B.subtype with hB'
    have hcard : Nat.card B' = 2 ^ 5 := by
      rw [hB', Subgroup.card_map_of_injective (Subgroup.subtype_injective B), hK]
    have hB'B : ∀ x ∈ B', x ∈ B := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    obtain ⟨x₁, h1, x₂, h2, x₃, h3, x₄, h4, G, hG, h29, hne⟩ :=
      dbl5 (B := B') (fun x hx => hBS (hB'B x hx))
        (fun x hx y hy => hcomm x (hB'B x hx) y (hB'B y hy)) (fun x hx => hsq x (hB'B x hx))
        (fun x hx hx1 => h2A x (hB'B x hx) hx1) hcard
    exact ⟨x₁, hB'B _ h1, x₂, hB'B _ h2, x₃, hB'B _ h3, x₄, hB'B _ h4, G, hG, h29, hne⟩

end CertificateChecks.KernelB45.C260394

end
