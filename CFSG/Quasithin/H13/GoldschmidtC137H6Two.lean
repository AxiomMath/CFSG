module

public import CFSG.Quasithin.H13.GoldschmidtC137H6Main
public import CFSG.Quasithin.H13.GoldschmidtC137H6Str3
public import CFSG.Quasithin.H13.GoldschmidtC137H6Str2

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem concl_caseII [Finite G] (hC124 : C124StatementSQTK (G := G))
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32) {X T V L P M : Subgroup G}
    (h : H6Ctx X T V L P) (hPM : P ≤ M) (hMX : M < X)
    (hmax : ∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) (h3 : P.relIndex M = 3)
    (hnDP : ¬ A6.o2Z L ≤ P) : Concl X T V L P := by
  have hTM : T ≤ M := h.hTP.trans hPM
  have hDM : A6.o2Z L ≤ M := by
    have := h.D_le_of_maximal hTM hMX hmax
    rwa [h.D_eq_o2Z] at this
  have hsup : P ⊔ A6.o2Z L = M := by
    apply le_antisymm (sup_le hPM hDM)
    have h1 := Subgroup.relIndex_mul_relIndex P (P ⊔ A6.o2Z L) M le_sup_left (sup_le hPM hDM)
    rw [h3] at h1
    have h2 : P.relIndex (P ⊔ A6.o2Z L) ≠ 1 := fun h1' =>
      hnDP (le_sup_right.trans (Subgroup.relIndex_eq_one.1 h1'))
    have hd : P.relIndex (P ⊔ A6.o2Z L) ∣ 3 := ⟨_, h1.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h4 | h4
    · exact absurd h4 h2
    · rw [h4] at h1
      have : (P ⊔ A6.o2Z L).relIndex M = 1 := by omega
      exact Subgroup.relIndex_eq_one.1 this
  have hDN : A6.o2Z L ≤ normalizer (V : Set G) := (o2Z_le_gc L).trans (h.hLX.trans h.hXN)
  have hPN : P ≤ normalizer (V : Set G) := h.hPX.le.trans h.hXN
  have hDbot : autI h.hVe (A6.o2Z L) = ⊥ :=
    autI_eq_bot_of_le_centralizer h.hVe (h.o2Z_le_D.trans inf_le_right)
  have hautIM : autI h.hVe M = autI h.hVe P := by
    rw [← hsup, autI_sup h.hVe hPN hDN, hDbot, sup_bot_eq]
  have hOP : pCoreOf 2 L ≤ P := (h.toBaum.hOL_le_Q.trans h.hQR).trans
    (CFSG.LieType.BorelTits.pCoreOf_le 2 P)
  have hPmax : ∀ K : Subgroup (MulAut (IntMod V h.hVe)), autI h.hVe P ≤ K → K ≤ autI h.hVe X →
      K = autI h.hVe P ∨ K = autI h.hVe X := by
    intro K hPK hKX
    have hMH : M ≤ starPreIn h.hVe X K := by
      intro m hm
      have hmN : m ∈ normalizer (V : Set G) := h.hXN (hMX.le hm)
      refine mem_starPreIn.2 ⟨hMX.le hm, hmN, ?_⟩
      have : convI h.hVe ⟨m, hmN⟩ ∈ autI h.hVe M := convI_mem_autI h.hVe hm hmN
      rw [hautIM] at this
      exact hPK this
    have hpre := autI_starPreIn h.hVe h.hXN hKX
    rcases hmax _ hMH (starPreIn_le h.hVe) with h1 | h1
    · left
      rw [← hpre, h1, hautIM]
    · right
      rw [← hpre, h1]
  have hPne : autI h.hVe P ≠ autI h.hVe X := by
    intro heq
    apply hMX.not_ge
    intro x hx
    have hxN := h.hXN hx
    have hx1 : convI h.hVe ⟨x, hxN⟩ ∈ autI h.hVe P := heq ▸ convI_mem_autI h.hVe hx hxN
    obtain ⟨p, hpP, hp⟩ := (mem_autI h.hVe).1 hx1
    have hc : convI h.hVe (p⁻¹ * ⟨x, hxN⟩) = 1 := by
      rw [map_mul, map_inv, hp, inv_mul_cancel]
    have hcen := (convI_eq_one_iff h.hVe _).1 hc
    have hcM : (p : G)⁻¹ * x ∈ M := h.C_le_of_maximal hTM hMX hmax
      ⟨X.mul_mem (X.inv_mem (h.hPX.le hpP)) hx, hcen⟩
    have : x = (p : G) * ((p : G)⁻¹ * x) := by group
    rw [this]
    exact M.mul_mem (hPM hpP) hcM
  have hPpg : IsPGroup 2 ↥(P ⊓ centralizer (V : Set G)) := by
    refine (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le ?_
    intro p hp
    have hpX : p ∈ X := h.hPX.le hp.1
    obtain ⟨d, hd, t, ht, rfl⟩ := h.C_le_D_mul_T ⟨hpX, hp.2⟩
    have hdP : d ∈ P := by
      have : d = (d * t) * t⁻¹ := by group
      rw [this]
      exact P.mul_mem hp.1 (P.inv_mem (h.hTP ht))
    have hdz : d ∈ A6.o2Z L := h.D_eq_o2Z ▸ hd
    have hdO : d ∈ pCoreOf 2 L := by
      by_contra hdn
      exact hnDP (h.o2Z_le_of_mem hOP hdP hdz hdn)
    have hdT : d ∈ T := h.hQT (h.toBaum.hOL_le_Q hdO)
    have hdt : d * t ∈ T ⊓ centralizer (V : Set G) := ⟨T.mul_mem hdT ht, hp.2⟩
    rw [h.hTC] at hdt
    exact hdt
  have hZ : ¬ oTwoUpper (A6.o2Z L) ≤ P := by
    intro hZP
    obtain ⟨u, hu, hu3⟩ := h.exists_order_three
    have huO : u ∉ pCoreOf 2 L := by
      intro huO
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨u, huO⟩
      have h2k : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hdvd : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2k
      rw [hu3] at hdvd
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      omega
    have huP : u ∈ P := hZP (mem_oTwoUpper_of_odd hu (by rw [hu3]; decide))
    exact hnDP (h.o2Z_le_of_mem hOP huP hu huO)
  exact h6_concl hC124 hC132 h hPpg hPmax hPne hZ

end CFSG.Quasithin.H13.U3.GC137
