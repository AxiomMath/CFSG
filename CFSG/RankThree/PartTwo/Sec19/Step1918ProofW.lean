module

public import CFSG.RankThree.PartTwo.Sec19.Step1915W
public import CFSG.RankThree.PartTwo.Sec19.Step1918ProofEnd
public import CFSG.RankThree.PartTwo.Sec19.Step1918ProofGen
public import CFSG.RankThree.PartTwo.Sec19.Step1918ProofInner
public import CFSG.RankThree.PartTwo.Sec19.Step1916Proof2
public import CFSG.RankThree.PartTwo.Sec19.Step1914TriSeitz434
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL)

open Step1918Proof in
theorem step1918W_of
    (h1913 : Step1913) (h1915 : Step1915W) (h1916D : Step1916D) (h1917 : Step1917)
    (hS199 : Seitz199) (hSL : SeitzL3Pi) : Step1918 := by
  intro G _ _ A c L E M hctx hLM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  obtain ⟨hθ, hZ, hL3⟩ := Step1916Proof2.lBar_facts h1913 hctx
  have hE := Step1916Proof2.isE27_E hctx
  have hA := Step1916Proof2.isE27_A hctx
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAe : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  set D := A ⊓ E with hDdef
  have hD9 : Nat.card D = 9 := h1916D G A c L E M hctx
  have hDA : D ≤ A := inf_le_left
  have hD3 : IsPGroup 3 D := hA.isPGroup.to_le hDA
  have hND : ∀ X : Subgroup G, X ≤ D → X ≠ ⊥ → Subgroup.normalizer (X : Set G) ≤ M :=
    (gammaOne_le_iff hD3).mp (h1917 G A c L E M hctx hLM)
  obtain ⟨z, hzD, hzL, hz1, hz3⟩ := Step1916Proof2.exists_mem_inf_of_three_dvd hctx hL3
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  obtain ⟨F, hFL, hF, hF9⟩ := exists_elemAbelian_nine h1913 hctx
  have hΓA : ¬ gamma 2 A ≤ M := fun hle => hctx.not_mem_partTwoT
    (mem_partTwoT_iff.mpr ⟨hctx.mem_partTwoE, M, hctx.mem_scriptM.1, hle⟩)
  rw [gamma_le_iff] at hΓA
  push Not at hΓA
  obtain ⟨B, hBA, hB2, hBM⟩ := hΓA
  have hB9 : 9 ≤ Nat.card B := by
    have hdvd : Nat.card B ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
      exact Subgroup.card_dvd_of_le hBA
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hlog := CFSG.RankThreeEvenClassification.Helpers.pRank_le_log_card 3 Nat.prime_three B
    rw [hk, Nat.log_pow (by norm_num)] at hlog
    have hk2 : 2 ≤ k := hB2.trans hlog
    rw [hk]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  obtain ⟨g, hgB, hgM⟩ := Set.not_subset.mp hBM
  have hBD : B ⊓ D ≠ ⊥ := by
    intro h
    have hBN : B ≤ Subgroup.normalizer (D : Set G) := fun b hb =>
      (Subgroup.centralizer_le_normalizer (D : Set G))
        (Subgroup.mem_centralizer_iff.mpr fun d hd => (hAc b (hBA hb) d (hDA hd)).symm)
    have h1 := Sec6.card_sup_mul_card_inf hBN
    rw [h, Subgroup.card_bot, mul_one, hD9] at h1
    have h2 : Nat.card (B ⊔ D : Subgroup G) ≤ 27 :=
      hA.2 ▸ Subgroup.card_le_of_le (sup_le hBA hDA)
    omega
  have hBDM : Subgroup.normalizer ((B ⊓ D : Subgroup G) : Set G) ≤ M := hND _ inf_le_right hBD
  have hconjA : ∀ y ∈ Subgroup.normalizer (B : Set G),
      A.map (MulAut.conj y).toMonoidHom ≤ M := by
    intro y hy
    rintro _ ⟨a, ha, rfl⟩
    refine hBDM ((Subgroup.centralizer_le_normalizer _) (Subgroup.mem_centralizer_iff.mpr ?_))
    intro w hw
    have hw' : y⁻¹ * w * y ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hy) w).mp hw.1
      simpa using this
    have hc := hAc a ha _ (hBA hw')
    change w * (y * a * y⁻¹) = (y * a * y⁻¹) * w
    calc w * (y * a * y⁻¹) = y * ((y⁻¹ * w * y) * a) * y⁻¹ := by group
      _ = y * (a * (y⁻¹ * w * y)) * y⁻¹ := by rw [hc]
      _ = (y * a * y⁻¹) * w := by group
  obtain ⟨K, hK, hLK, halt⟩ := h1915 G A c L E M hctx hLM
  have hKp : Group.IsPerfect K := isPerfect_of_mem_oTwoComponentsIn hK
  have hKn : ∀ m ∈ M, K.map (MulAut.conj m).toMonoidHom = K := fun m hm =>
    map_conj_eq_of_mem hctx hZ hK hLK hFL hF hF9 hm
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := fun m hm =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hKn m hm)
  have hZL2 : Subgroup.center (L ⧸ CFSG.pCore 2 L) = ⊥ :=
    Step1916Proof2.center_eq_bot_of_mulEquiv' (QuotientGroup.quotientMulEquivOfEq hθ.symm) hZ
  have hgen : ∀ y ∈ Subgroup.normalizer (B : Set G), y ∉ M →
      K.map (MulAut.conj y).toMonoidHom ≤ M := by
    intro y hyB hyM
    set A' := A.map (MulAut.conj y⁻¹).toMonoidHom with hA'def
    set D' := D.map (MulAut.conj y⁻¹).toMonoidHom with hD'def
    set M' := M.map (MulAut.conj y⁻¹).toMonoidHom with hM'def
    have hA'M : A' ≤ M := hconjA y⁻¹ (inv_mem hyB)
    have hA'E : A' ∈ partTwoE G :=
      CFSG.RankThree.PartTwo.map_mem_partTwoE (MulAut.conj y⁻¹) hctx.mem_partTwoE
    have hD'A' : D' ≤ A' := Subgroup.map_mono hDA
    have hD'K : D' ≤ Subgroup.normalizer (K : Set G) := hD'A'.trans (hA'M.trans hMK)
    have hD'9 : Nat.card D' = 9 := by
      rw [hD'def, Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective, hD9]
    have hD'ab : CFSG.Assembly.IsElemAbelian 3 D' :=
      Sec13.isElemAbelian_map (isElemAbelian_of_le hA.1 hDA) _
    have hCM' : ∀ d ∈ D', d ≠ 1 → Subgroup.centralizer ({d} : Set G) ≤ M' := by
      rintro _ ⟨d₀, hd₀, rfl⟩ hd1 x hx
      have hd₀1 : d₀ ≠ 1 := by
        rintro rfl
        exact hd1 (map_one _)
      have hX : Subgroup.zpowers d₀ ≠ ⊥ := by
        rwa [Ne, Subgroup.zpowers_eq_bot]
      rw [Step199Proof.mem_map_conj_iff, inv_inv]
      apply hND _ ((Subgroup.zpowers_le).mpr hd₀) hX
      apply Sec12.mem_normalizer_zpowers_of_commute
      have hx' : x * (y⁻¹ * d₀ * y) = (y⁻¹ * d₀ * y) * x := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hx
        simpa [MulAut.conj_apply] using this
      calc y * x * y⁻¹ * d₀ = y * (x * (y⁻¹ * d₀ * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * d₀ * y) * x) * y⁻¹ := by rw [hx']
        _ = d₀ * (y * x * y⁻¹) := by group
    suffices hKM' : K ≤ M' by
      rintro _ ⟨k, hk, rfl⟩
      have h1 := hKM' hk
      rw [hM'def, Step199Proof.mem_map_conj_iff, inv_inv] at h1
      exact h1
    have hii : ∀ (_ : K = L ⊔ CFSG.Open.pCoreOf 2 K)
        (_ : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 2)) ∨
          Nonempty (K ⧸ CFSG.pCore 2 K ≃* CFSG.Blueprint.NativeSporadic.M12)),
        K ≤ M' := by
      intro hKL htype
      obtain ⟨ι, -⟩ := exists_quotientEquiv hLK hKL
      have hZK : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥ :=
        Step1916Proof2.center_eq_bot_of_mulEquiv' ι.symm hZL2
      rcases le_or_inner hD'ab hD'9 hD'K hCM' htype with hle | ⟨hinj, hinn⟩
      · exact hle
      exfalso
      obtain ⟨d, hdD', hd1, x, hxM, hxd⟩ := exists_conj_mem_E hctx hZ hK hLK hKL hMK hZK hFL hF
        hF9 hzD.2 hzL hzo htype hA'E hA'M hD'A' hD'9 hD'K hinj hinn
      have hEx : E.map (MulAut.conj x⁻¹).toMonoidHom ≤ M' := by
        have hdE : d ∈ E.map (MulAut.conj x⁻¹).toMonoidHom := by
          rw [Step199Proof.mem_map_conj_iff, inv_inv]
          exact hxd
        have hab : IsMulCommutative (E.map (MulAut.conj x⁻¹).toMonoidHom) :=
          (Sec13.isElemAbelian_map hE.1 (MulAut.conj x⁻¹).toMonoidHom).1
        exact (le_centralizer_of_mem hab hdE).trans (hCM' d hdD' hd1)
      have hyx : (y * x⁻¹) ∈ M := by
        refine mem_of_map_conj_le hctx.hyp191 hE hctx.mem_scriptM ?_
        rintro _ ⟨e, he, rfl⟩
        have h1 := hEx ⟨e, he, rfl⟩
        rw [hM'def, Step199Proof.mem_map_conj_iff, inv_inv] at h1
        have e1 : (MulAut.conj (y * x⁻¹)).toMonoidHom e =
            y * ((MulAut.conj x⁻¹).toMonoidHom e) * y⁻¹ := by
          simp [MulAut.conj_apply, mul_assoc]
        rw [e1]
        exact h1
      exact hyM (by simpa using M.mul_mem hyx hxM)
    rcases halt with hKL | ⟨p, e, hp, he, -, hisoK, -⟩ | ⟨n, -, -, hmodel, -⟩
    · obtain ⟨ι, -⟩ := exists_quotientEquiv hLK hKL
      rcases h1913 G A c L E M hctx with ⟨p, e, hp, he, hiso⟩ | hM12
      · by_cases h4 : p ^ e = 4
        ·
          have hp2 : p = 2 := by
            have hpd : p ∣ 2 ^ 2 := by
              rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4]
              exact dvd_pow_self p (by omega)
            exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
              (hp.out.dvd_of_dvd_pow hpd)
          subst hp2
          have he2 : e = 2 := Nat.pow_right_injective le_rfl (show 2 ^ e = 2 ^ 2 by rw [h4])
          subst he2
          obtain ⟨φP⟩ : Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) := by
            rcases hiso with ⟨-, hφ⟩ | ⟨hq', -⟩
            · exact hφ
            · norm_num at hq'
          exact hii hKL (Or.inl ⟨ι.symm.trans φP⟩)
        ·
          refine le_of_seitz hS199 hSL hKp hD'ab hD'9 hD'K hCM' (Or.inl ⟨p, e, hp, he, ?_, h4⟩)
          rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
          · exact Or.inl ⟨hq, ⟨ι.symm.trans φ⟩⟩
          · exact Or.inr ⟨hq, ⟨ι.symm.trans φ⟩⟩
      ·
        obtain ⟨φ⟩ := hM12
        exact hii hKL (Or.inr ⟨ι.symm.trans φ⟩)
    ·
      refine le_of_seitz hS199 hSL hKp hD'ab hD'9 hD'K hCM'
        (Or.inl ⟨p, 3 * e, hp, by omega, hisoK, ?_⟩)
      have h8 : 2 ^ 3 ≤ p ^ (3 * e) :=
        (Nat.pow_le_pow_left hp.out.two_le 3).trans (Nat.pow_le_pow_right hp.out.pos (by omega))
      omega
    ·
      exact le_of_seitz hS199 hSL hKp hD'ab hD'9 hD'K hCM' (Or.inr ⟨2, n, by norm_num, hmodel⟩)
  have h1 : K.map (MulAut.conj g).toMonoidHom ≤ M := hgen g hgB hgM
  have h2 : K.map (MulAut.conj g⁻¹).toMonoidHom ≤ M :=
    hgen g⁻¹ (inv_mem hgB) fun h => hgM (by simpa using M.inv_mem h)
  have hKg : K ≤ M.map (MulAut.conj g).toMonoidHom := by
    intro k hk
    rw [Step199Proof.mem_map_conj_iff]
    have := h2 ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply] using this
  have hKeq := map_conj_eq_of_le hctx hZ hK hLK hFL hF hF9 hKg h1
  exact hgM (mem_of_map_conj_eq hctx hK hKn hKeq)

theorem step1918W_of_seitz434
    (h1913 : Step1913) (h1915 : Step1915W) (h1916D : Step1916D) (h1917 : Step1917)
    (hS199 : Seitz199) (h434 : Sec4.Seitz434) (hgap : SeitzL3PiGap) : Step1918 :=
  step1918W_of h1913 h1915 h1916D h1917 hS199 (seitzL3Pi_of_seitz434 h434 hgap)

theorem step1918W_of_step1913
    (h1913 : Step1913) (h1915 : Step1915W) (h1917 : Step1917) (hS199 : Seitz199)
    (hSL : SeitzL3Pi) : Step1918 :=
  step1918W_of h1913 h1915 (step1916D_of h1913) h1917 hS199 hSL

end CFSG.RankThree.PartTwo.Sec19
