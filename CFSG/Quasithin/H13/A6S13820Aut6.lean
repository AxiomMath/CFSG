module

public import CFSG.Quasithin.H13.A6S13820Aut5
public import CFSG.Quasithin.H13.A6S13821za

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Aut20

theorem odd_card_center20 {Q : Type} [Group Q] [Finite Q] (h : CFSG.pCore 2 Q = ⊥) :
    Odd (Nat.card (Subgroup.center Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
  have hzc : ∀ a ∈ Subgroup.zpowers (x : Q), a ∈ Subgroup.center Q := by
    rintro _ ⟨k, rfl⟩
    exact Subgroup.zpow_mem _ x.2 k
  have hn : (Subgroup.zpowers (x : Q)).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_center_iff.mp (hzc a ha) g, mul_inv_cancel_right]
    exact ha
  have hx2 : orderOf (x : Q) = 2 := by rw [Subgroup.orderOf_coe, hx]
  have hp : IsPGroup 2 (Subgroup.zpowers (x : Q)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
  have hle : Subgroup.zpowers (x : Q) ≤ CFSG.pCore 2 Q := le_sSup ⟨hn, hp⟩
  rw [h] at hle
  have h1 : (x : Q) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
  rw [h1, orderOf_one] at hx2
  omega

end Aut20

theorem fact13820Aut_of
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hL2 : AutBorel13820L2) (hL3 : AutBorel13820L3) (hU3 : AutBorel13820U3)
    (hSp4 : AutBorel13820Sp4) (hG2 : AutBorel13820G2) : Fact13820Aut := by
  intro G _ _ T L V S H K n hctx hBsolv
  obtain ⟨hS, hH, hK, hKn, hHe, hn, hLie⟩ := hctx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  obtain ⟨e⟩ := S.kst_equiv hS hH hK
  have hLieQ : LieF2n (ModO2 K) n := lieF2n_congr e.symm hLie
  have hq : CFSG.IsQuasisimple (ModO2 K) := S.isQuasisimple_modO2 h36 h139 h1334 h13 hS hH hK
  have hZ : Odd (Nat.card (Subgroup.center (ModO2 K))) :=
    Aut20.odd_card_center20 (pCore_two_quotient_pCore_two ↥K)
  have hB : Aut20.borel20 T K ≤ Subgroup.normalizer (L : Set G) :=
    hBsolv (isSolvable_inf_normalizer_of_isSylowTwoOf (S.isSylowTwoOf_TK hH hKH hKn))
  have hLT := S.L1T_le_normalizer_TK h1334 hS hH hKH hKn hn hLieQ
  obtain ⟨t, htTL, htX⟩ := S.exists_t20
  have htN : t ∈ Subgroup.normalizer (K : Set G) := hKn (hTH htTL.1)
  have hbor := S.borelAut20 h1334 hH hKH hKn hB htTL htN
  by_cases hinn : ∃ g : ModO2 K, Aut20.act20 K ⟨t, htN⟩ = MulAut.conj g
  ·
    left
    obtain ⟨g, hg⟩ := hinn
    obtain ⟨kt, hkt⟩ := hbor.2.2.2.2.2.1
    obtain ⟨_, ⟨u, hu, rfl⟩, hαu⟩ :=
      Aut20.exists_mem_conj20 hZ hbor.1 hkt hbor.2.2.2.2.2.2.1 hg
    exact S.caseA20 hH hK hKn hHe hLT htTL htX htN (u := (u : G)) (Subgroup.mem_subgroupOf.mp hu)
      hαu
  ·
    right
    have hfam : IsPSL 2 2 2 (ModO2 K ⧸ Subgroup.center (ModO2 K)) ∨
        IsPSL 3 2 2 (ModO2 K ⧸ Subgroup.center (ModO2 K)) ∨
        IsPSU 3 2 3 (ModO2 K ⧸ Subgroup.center (ModO2 K)) := by
      rcases hLieQ with h | h | h | h | h
      · rcases hL2 (ModO2 K) n hq hZ hn h _ _ _ hbor with h' | rfl
        · exact absurd h' hinn
        · exact Or.inl h
      · rcases hL3 (ModO2 K) n hq hZ hn h _ _ _ hbor with h' | rfl
        · exact absurd h' hinn
        · exact Or.inr (Or.inl h)
      · rcases hU3 (ModO2 K) n hq hZ hn h _ _ _ hbor with h' | rfl
        · exact absurd h' hinn
        · exact Or.inr (Or.inr h)
      · exact absurd (hSp4 (ModO2 K) n hq hZ hn h _ _ _ hbor) hinn
      · exact absurd (hG2 (ModO2 K) n hq hZ hn h _ _ _ hbor) hinn
    let ec : (ModO2 K ⧸ Subgroup.center (ModO2 K)) ≃*
        (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) :=
      QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
    refine ⟨?_, t, htTL, htX, fun k hk => ?_⟩
    · rcases hfam with h | h | h
      · exact Or.inl (IsPSL.of_mulEquiv ec h)
      · exact Or.inr (Or.inl (IsPSL.of_mulEquiv ec h))
      · exact Or.inr (Or.inr (IsPSU.of_mulEquiv ec h))
    · by_contra hcon
      push Not at hcon
      apply hinn
      refine ⟨Aut20.mk20 K ⟨k, hk⟩, ?_⟩
      ext y
      induction y using QuotientGroup.induction_on with
      | H y =>
        rw [Aut20.act20_mk, MulAut.conj_apply]
        have hky : k * y * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk y.2) (K.inv_mem hk)
        have hw := hcon _ hky
        have hty : t * y * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htN y).mp y.2
        have hw' : (k * y * k⁻¹)⁻¹ * (t * y * t⁻¹) ∈ pCoreOf 2 K := by
          have h1 := (Subgroup.mem_normalizer_iff.mp
            (le_normalizer_pCoreOf 2 K (K.inv_mem hky)) _).mp hw
          rw [inv_inv] at h1
          have e1 : (k * y * k⁻¹)⁻¹ * ((t * k⁻¹) * (k * y * k⁻¹) * (t * k⁻¹)⁻¹ * (k * y * k⁻¹)⁻¹) *
              (k * y * k⁻¹) = (k * y * k⁻¹)⁻¹ * (t * y * t⁻¹) := by group
          rwa [e1] at h1
        show ((⟨t * y * t⁻¹, hty⟩ : ↥K) : ModO2 K) = ((⟨k, hk⟩ : ↥K) : ModO2 K) * (y : ModO2 K) *
          ((⟨k, hk⟩ : ↥K) : ModO2 K)⁻¹
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        refine (QuotientGroup.eq (s := CFSG.pCore 2 ↥K)).2 ?_
        rw [← Setting4.pCoreOf_subgroupOf_eq K, Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using (pCoreOf 2 K).inv_mem hw'

end CFSG.Quasithin.H13.A6
