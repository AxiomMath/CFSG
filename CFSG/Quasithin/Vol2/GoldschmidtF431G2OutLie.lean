module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutKFields
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFusK
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFixMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSOutDatum

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.H13.F431.F45
  CFSG.QuasithinUnique CFSG.GH74.GLS.Stage4.Hex

section Assemble


variable {K : Type} [Field K] [Finite K] [CharP K 2] {A : LieAmalgamExt (C K)}

theorem f431TwoOut_of_gen {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    {σ₁ : K ≃+* K} (hσ₁ : σ₁ ∈ Fz A) (hgen : ∀ σ ∈ Fz A, σ ∈ Subgroup.zpowers σ₁)
    (hev : Even (orderOf σ₁)) {N N' : Subgroup ↥A.K}
    (hN : ∀ x : ↥A.K, x ∈ N ↔ ∃ g ∈ Pmin K ⟨1, by decide⟩, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ)
    (hN' : ∀ x : ↥A.K, x ∈ N' ↔ ∃ g ∈ Pmin K ⟨0, by decide⟩, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ) :
    F431TwoOut (outT (h.inn_le_K hn hK) (psiK h hσ₁)) (outS (h.inn_le_K hn hK))
      (outf (psiK h hσ₁)) N N' (iK A (h.inn_le_K hn hK) (xc 1)) (outI (h.inn_le_K hn hK)) := by
  have hFinK := finite_C (K := K)
  have hFinA : Finite (MulAut (C K)) := finite_mulAut_C (K := K)
  have hgenK := h.inn_le_K hn hK
  have O := outK_of_gen hn hK h hσ₁ hgen hev hN hN'
  have P := outProps_of_gen hn hK h hσ₁ hgen
  have hzN := z_mem_centerOf_perfectCore hn hK hgenK P hN
  set r : ℕ := 2 ^ (n / 2) with hr
  have hn2 : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even O.even_n
  have hKr : Nat.card K = r ^ 2 := by
    rw [hK, hr, ← pow_mul]
    congr 1
    omega
  have hr2 : 2 ≤ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set σ : K ≃+* K := σ₁ ^ (oddPart (psiK h hσ₁) * 2 ^ (twoExp (psiK h hσ₁) - 1)) with hσdef
  have hσr : ∀ x, σ x = x ^ r := by
    intro x
    have := O.delta (σ₁ ^ oddPart (psiK h hσ₁)) rfl x
    rwa [← pow_mul] at this
  have hδ : involAut (psiK h hσ₁) (fieldAut K σ₁) = fieldAut K σ := by
    rw [involAut, map_pow]
  have hroots : ∀ i ∈ outI hgenK, ∃ y : C K,
      (y = xa 1 ∨ y = xu 1 ∨ y = xv 1 ∨ y = xb 1 ∨ y = xc 1) ∧ i = iK A hgenK y := by
    intro i hi
    obtain ⟨u, hu, hiu⟩ := (mem_outI_iff hgenK i).1 hi
    refine ⟨u, ?_, Subtype.ext hiu⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hu
  exact
    { sylow := O.sylow
      T_le := O.T_le
      T_le' := O.T_le'
      S_le := O.S_le
      S_norm := O.S_norm
      cyc := ⟨psi2 (psiK h hσ₁), O.cyc⟩
      z_mem := O.z_mem
      z_two := O.z_two
      z_ZN := hzN
      center_T := center_T_of hn hK h hσ₁ hgen hN
      I_le := O.I_le
      fusion := fusion_of_gen hn hK h hN hN'
      f_mem := O.f_mem
      f_not := O.f_not
      f_sq := O.f_sq
      Tf_lt := fun i hi => by
        obtain ⟨y, hy, rfl⟩ := hroots i hi
        exact P.g2_card_Tf_lt hr2 hKr hσr hδ hy
      Sylow_Tf := P.g2_isSylowTwoOf_Tf O.a_pos hr2 hKr hσr hδ g2_sylow O.T_le
      Z_sq := O.Z_sq
      Z_S := centerOf_outS_le hn hK hgenK P hN
      W_le := P.g2_W_le
      W_ne := ⟨_, (P.g2_W_mem).1, hzN, (P.g2_W_mem).2⟩ }

end Assemble

end CFSG.Quasithin.H13.F431.G2.OutK
