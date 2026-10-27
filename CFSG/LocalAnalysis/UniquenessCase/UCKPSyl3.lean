module

public import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl2
public import CFSG.LocalAnalysis.UniquenessCase.UCKPAutQuot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem exists_frame_sylow {E : Type} [Field E] {n k : ℕ} (hU : UnitaryFieldData 2 n E)
    (hn : 2 ≤ n) (hk : 2 ^ n = k + 1) [Finite (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))]
    {q : ℕ} [Fact q.Prime] (hq3 : 3 < q) (hqk : q ∣ k + 2)
    (hcard : Nat.card (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) * Nat.gcd 3 (k + 2) =
      (k + 1) ^ 3 * (k * (k + 2)) * ((k + 2) * (k ^ 2 + k + 1))) :
    ∃ T : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)),
      T ≤ Frame.frameTorus hU (fun i => Pi.single i 1) ∧ IsPGroup q T ∧ ¬ q ∣ T.index ∧
      ∀ t ∈ Frame.frameTorus hU (fun i => Pi.single i 1), t ^ q = 1 → t ∈ T := by
  classical
  have hv := isOrthonormalFrame_single (p := 2) hU
  obtain ⟨-, -, hcomm, -, hFcard, -, -⟩ := Frame.frame_group_structure hU hn hv
  set F := Frame.frameTorus hU (fun i => Pi.single i 1) with hFdef
  have hFcard' : Nat.card F * Nat.gcd 3 (k + 2) = (k + 2) ^ 2 := by
    rw [show k + 2 = 2 ^ n + 1 by omega]
    exact hFcard
  have hFidx : F.index = (k + 1) ^ 3 * k * (k ^ 2 + k + 1) := by
    have h1 := F.index_mul_card
    apply Nat.eq_of_mul_eq_mul_right (show 0 < (k + 2) ^ 2 by positivity)
    calc F.index * (k + 2) ^ 2 = F.index * (Nat.card F * Nat.gcd 3 (k + 2)) := by
          rw [hFcard']
      _ = _ := by rw [← mul_assoc, h1, hcard]; ring
  set k₀ := (Nat.card F).factorization q
  obtain ⟨T, hTdef⟩ : ∃ T, T = torsionSubgroup F hcomm (q ^ k₀) := ⟨_, rfl⟩
  have hmemT : ∀ y, y ∈ T ↔ y ∈ F ∧ y ^ (q ^ k₀) = 1 := fun y => by
    rw [hTdef, mem_torsionSubgroup]
  have hTq : IsPGroup q T := fun y => ⟨k₀, Subtype.ext ((hmemT y).1 y.2).2⟩
  have hTF : T ≤ F := fun y hy => ((hmemT y).1 hy).1
  have hTidx : ¬ q ∣ T.index := by
    rw [← Subgroup.relIndex_mul_index hTF]
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).1 h with h | h
    · obtain ⟨S₀⟩ : Nonempty (Sylow q F) := inferInstance
      have hS₀ : (S₀ : Subgroup F) ≤ T.subgroupOf F := by
        intro y hy
        rw [Subgroup.mem_subgroupOf, hmemT]
        refine ⟨y.2, ?_⟩
        have h1 : (⟨y, hy⟩ : S₀) ^ Nat.card S₀ = 1 := pow_card_eq_one'
        rw [S₀.card_eq_multiplicity] at h1
        have h2 := congrArg
          (fun z : S₀ => ((z : F) : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) h1
        simpa using h2
      exact S₀.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hS₀))
    · exact not_dvd_torusIndex Fact.out hq3 hqk (hFidx ▸ h)
  have hqF : q ∣ Nat.card F := by
    have h1 : q ∣ Nat.card F * Nat.gcd 3 (k + 2) := by
      rw [hFcard']
      exact dvd_pow hqk two_ne_zero
    rcases (Nat.Prime.dvd_mul Fact.out).1 h1 with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left 3 _))) (by omega)
  have hk₀ : 1 ≤ k₀ := ((Fact.out : q.Prime).dvd_iff_one_le_factorization Nat.card_pos.ne').1 hqF
  refine ⟨T, hTF, hTq, hTidx, fun t ht htq => (hmemT t).2 ⟨ht, ?_⟩⟩
  rw [show q ^ k₀ = q * q ^ (k₀ - 1) by rw [← pow_succ', Nat.sub_add_cancel hk₀], pow_mul, htq,
    one_pow]

theorem u3Syl_of_griess (hgr : CFSG.Open.GriessAllModelsStatement) : U3Syl := by
  intro X _ _ n hX q hq hq3 hqn S hSq hSidx
  refine ⟨?_, ?_⟩
  · obtain ⟨E, hES, hE, hEc, -⟩ := u3SylOmega_of_griess hgr X n hX q hq hq3 hqn S hSq hSidx
    exact ⟨E, hES, hE, hEc⟩
  rintro α ⟨k, hαk⟩ hαS s hs hsq
  haveI : Fact q.Prime := ⟨hq⟩
  have hn2 : 2 ≤ n := u3Range X n hX
  have hZ : ¬ q ∣ Nat.card (center X) := fun h =>
    absurd (Nat.le_of_dvd (by norm_num) (h.trans (u3Center_of_griess hgr X n hX))) (by omega)
  obtain ⟨e', hB⟩ := CFSG.SeitzReduction.RankOne.exists_benderType_of_lieModel_psu3 hn2 hX.2
  obtain ⟨hU, ⟨φ₀⟩⟩ := BenderType.exists_equiv_unitaryModelP hB
  let φ : X ⧸ center X ≃* primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))) :=
    φ₀
  obtain ⟨-, K, _, _, hK, ⟨ψ⟩⟩ :=
    CFSG.SeitzReduction.RankOne.statedClassicalModel_of_lieModel_psu3 hX.2
  have hKU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨k', hk'⟩ : ∃ k', 2 ^ n = k' + 1 :=
    ⟨2 ^ n - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
  haveI : Finite (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)))) :=
    Finite.of_equiv _ φ.toEquiv
  have hcard : Nat.card (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)))) *
      Nat.gcd 3 (k' + 2) = (k' + 1) ^ 3 * (k' * (k' + 2)) * ((k' + 2) * (k' ^ 2 + k' + 1)) := by
    have h := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul hKU
    rw [← Nat.card_congr φ.toEquiv, Nat.card_congr ψ.toEquiv, show k' + 2 = 2 ^ n + 1 by omega,
      h, hk', show (k' + 1) ^ 2 - 1 = k' * (k' + 2) from Nat.sub_eq_of_eq_add (by ring)]
    ring
  obtain ⟨T, hTF, hTq, hTidx, hΩT⟩ :=
    exists_frame_sylow hU hn2 hk' hq3 (by rwa [show k' + 2 = 2 ^ n + 1 by omega]) hcard
  set β₀ := MulAut.congr φ (autQuot α) with hβ₀def
  have hβ₀ : ∀ y, β₀ (φ y) = φ (autQuot α y) := fun y => by
    rw [hβ₀def, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hβ₀k : β₀ ^ (q ^ k) = 1 := by rw [hβ₀def, ← map_pow, ← map_pow, hαk, map_one, map_one]
  set Sb := (S.map (QuotientGroup.mk' (center X))).map φ.toMonoidHom with hSbdef
  have hSbq : IsPGroup q Sb := (hSq.map _).map _
  have hSbidx : ¬ q ∣ Sb.index := fun h => hSidx (h.trans ((Subgroup.index_map_dvd _
    φ.surjective).trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _))))
  have hmemSb : ∀ s' ∈ S, φ (QuotientGroup.mk s') ∈ Sb := fun s' hs' => ⟨_, ⟨s', hs', rfl⟩, rfl⟩
  have hβ₀S : ∀ x ∈ Sb, β₀ x ∈ Sb := by
    rintro _ ⟨_, ⟨s', hs', rfl⟩, rfl⟩
    change β₀ (φ (QuotientGroup.mk s')) ∈ Sb
    rw [hβ₀, autQuot_mk]
    exact hmemSb _ (hαS s' hs')
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))))
    (hTq.toSylow hTidx) (hSbq.toSylow hSbidx)
  have hgS : ∀ x, x ∈ Sb ↔ ∃ t ∈ T, g * t * g⁻¹ = x := by
    intro x
    have h1 : x ∈ ((g • hTq.toSylow hTidx : Sylow q _) :
        Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))))) ↔
        x ∈ Sb := by
      rw [hg]
      rfl
    rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    rfl
  set c := MulAut.conj g⁻¹ with hc
  have hc1 : ∀ x, c x = g⁻¹ * x * g := fun x => by rw [hc, MulAut.conj_apply, inv_inv]
  have hc2 : ∀ x, c⁻¹ x = g * x * g⁻¹ := fun x => by
    rw [hc, ← map_inv, inv_inv, MulAut.conj_apply]
  set β := c * β₀ * c⁻¹ with hβdef
  have hβ : ∀ t, β t = c (β₀ (c⁻¹ t)) := fun t => rfl
  have hβk : β ^ (q ^ k) = 1 := by rw [hβdef, conj_pow, hβ₀k, mul_one, mul_inv_cancel]
  have hβT : ∀ t ∈ T, β t ∈ T := by
    intro t ht
    obtain ⟨t', ht', h'⟩ := (hgS _).1 (hβ₀S _ ((hgS _).2 ⟨t, ht, (hc2 t).symm⟩))
    rw [hβ, ← h', hc1, show g⁻¹ * (g * t' * g⁻¹) * g = t' by group]
    exact ht'
  have hfix := fix_of_normalizes_frame hU hn2 (isOrthonormalFrame_single hU) hq hq3 hqn hTF hΩT
    hβk hβT
  obtain ⟨t, htT, hgt⟩ := (hgS _).1 (hmemSb s hs)
  have htq : t ^ q = 1 := by
    have h1 : (φ (QuotientGroup.mk s)) ^ q = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow, hsq, QuotientGroup.mk_one, map_one]
    rwa [← hgt, conj_pow, conj_eq_one_iff] at h1
  have h2 : β₀ (c⁻¹ t) = c⁻¹ t := by
    have h1 := hfix t htT htq
    rw [hβ] at h1
    calc β₀ (c⁻¹ t) = c⁻¹ (c (β₀ (c⁻¹ t))) := (MulAut.inv_apply_self _ c _).symm
      _ = c⁻¹ t := by rw [h1]
  rw [hc2, hgt, hβ₀, autQuot_mk] at h2
  have h4 : s⁻¹ * α s ∈ center X := QuotientGroup.eq.1 (φ.injective h2).symm
  have h5 : s⁻¹ * α s ∈ S := S.mul_mem (S.inv_mem hs) (hαS s hs)
  have h6 : s⁻¹ * α s = 1 := by
    obtain ⟨j, hj⟩ := hSq ⟨_, h5⟩
    have hj' : (s⁻¹ * α s) ^ (q ^ j) = 1 := by simpa using congrArg Subtype.val hj
    have hd2 : orderOf (s⁻¹ * α s) ∣ Nat.card (center X) := by
      rw [← Subgroup.orderOf_mk (s⁻¹ * α s) h4]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (orderOf (s⁻¹ * α s)) (Nat.card (center X)) :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hj')
        (Nat.Coprime.pow_left _ (hq.coprime_iff_not_dvd.2 hZ))
    exact orderOf_eq_one_iff.1 (hcop.eq_one_of_dvd hd2)
  exact (inv_mul_eq_one.1 h6).symm

end CFSG.LocalAnalysis.UniquenessCase.UCK
