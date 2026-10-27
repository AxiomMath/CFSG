module

public import CFSG.LocalAnalysis.UniquenessCase.UCKU3b
public import CFSG.LocalAnalysis.UniquenessCase.UCKP1
public import CFSG.LocalAnalysis.UniquenessCase.UCKPCenter
public import CFSG.GH74.Uniqueness.Bender.Unitary311
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal
public import CFSG.RankThree.PartOne.K1214.Omega
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisHomC
public import CFSG.LocalAnalysis.SteinbergBVCcommHomocyclicFrattini
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
public import CFSG.LargeExtraspecial.Bender

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem dvd_six_of_dvd_torusIndex {p k : ℕ} (hpk : p ∣ k + 2)
    (h : p ∣ (k + 1) ^ 3 * k * (k ^ 2 + k + 1)) : p ∣ 6 := by
  have hk : ((k : ℕ) : ZMod p) = -2 := by
    have h2 := (ZMod.natCast_eq_zero_iff (k + 2) p).2 hpk
    push_cast at h2
    linear_combination h2
  have h0 := (ZMod.natCast_eq_zero_iff _ p).2 h
  push_cast at h0
  rw [hk] at h0
  have h6 : ((6 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination h0
  exact (ZMod.natCast_eq_zero_iff 6 p).1 h6

theorem eq_two_or_three_of_dvd_six {p : ℕ} (hp : p.Prime) (h : p ∣ 6) : p = 2 ∨ p = 3 := by
  rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 from h) with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)

theorem not_dvd_torusIndex {q k : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hqk : q ∣ k + 2) :
    ¬ q ∣ (k + 1) ^ 3 * k * (k ^ 2 + k + 1) := fun h => by
  rcases eq_two_or_three_of_dvd_six hq (dvd_six_of_dvd_torusIndex hqk h) with h | h <;> omega

theorem not_dvd_of_six_mul {p k N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p ∣ k + 2)
    (h6 : 6 * N = (k + 1) ^ 3 * k * (k ^ 2 + k + 1)) : ¬ p ∣ N := by
  intro hpN
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨j, hj⟩ := hpk
    obtain ⟨i, rfl⟩ : ∃ i, k = 3 * i + 1 := ⟨j - 1, by omega⟩
    have h3 : 3 * (2 * N) = 3 * ((3 * i + 2) ^ 3 * (3 * i + 1) * (3 * i ^ 2 + 3 * i + 1)) := by
      rw [show 3 * (2 * N) = 6 * N by ring, h6]
      ring
    have h2 := Nat.eq_of_mul_eq_mul_left (by norm_num) h3
    have h4 : 3 ∣ (3 * i + 2) ^ 3 * (3 * i + 1) * (3 * i ^ 2 + 3 * i + 1) :=
      h2 ▸ dvd_mul_of_dvd_right hpN 2
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h4 with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
      · have := Nat.prime_three.dvd_of_dvd_pow h
        omega
      · omega
    · rw [show 3 * i ^ 2 + 3 * i + 1 = 3 * (i ^ 2 + i) + 1 by ring] at h
      have h1 : 3 ∣ 1 := (Nat.dvd_add_right (dvd_mul_right 3 _)).1 h
      omega
  · rcases eq_two_or_three_of_dvd_six hp
      (dvd_six_of_dvd_torusIndex hpk (h6 ▸ dvd_mul_of_dvd_right hpN 6)) with h | h
    · exact hp2 h
    · exact hp3 h

theorem isOrthonormalFrame_single {E : Type} [Field E] {p f : ℕ} (hU : UnitaryFieldData p f E) :
    Frame.IsOrthonormalFrame hU (fun i => Pi.single i 1) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Frame.herm, Fin.sum_univ_three]

theorem frame_sylow_count {E : Type} [Field E] {n k : ℕ} (hU : UnitaryFieldData 2 n E)
    (hn : 2 ≤ n) (hk : 2 ^ n = k + 1) [Finite (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))]
    {q : ℕ} [Fact q.Prime] (hq3 : 3 < q) (hqk : q ∣ k + 2)
    (hcard : Nat.card (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) * Nat.gcd 3 (k + 2) =
      (k + 1) ^ 3 * (k * (k + 2)) * ((k + 2) * (k ^ 2 + k + 1))) :
    ∃ N : ℕ, Nat.card (Sylow q (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) ∣ N ∧
      6 * N = (k + 1) ^ 3 * k * (k ^ 2 + k + 1) := by
  classical
  have hv := isOrthonormalFrame_single (p := 2) hU
  obtain ⟨hFF₀, hnorm, hcomm, -, hFcard, -, π, hπ, hker⟩ := Frame.frame_group_structure hU hn hv
  set F := Frame.frameTorus hU (fun i => Pi.single i 1) with hFdef
  set F₀ := Frame.frameMono hU (fun i => Pi.single i 1) with hF₀def
  have hFcard' : Nat.card F * Nat.gcd 3 (k + 2) = (k + 2) ^ 2 := by
    rw [show k + 2 = 2 ^ n + 1 by omega]
    exact hFcard
  have hFidx : F.index = (k + 1) ^ 3 * k * (k ^ 2 + k + 1) := by
    have h1 := F.index_mul_card
    apply Nat.eq_of_mul_eq_mul_right (show 0 < (k + 2) ^ 2 by positivity)
    calc F.index * (k + 2) ^ 2 = F.index * (Nat.card F * Nat.gcd 3 (k + 2)) := by
          rw [hFcard']
      _ = _ := by rw [← mul_assoc, h1, hcard]; ring
  have h6 : 6 * F₀.index = F.index := by
    rw [← Subgroup.relIndex_mul_index hFF₀]
    congr 1
    change 6 = (F.subgroupOf F₀).index
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hπ, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
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
  have hF₀N : F₀ ≤ normalizer (T : Set (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmemT, hmemT]
    constructor
    · rintro ⟨hyF, hy⟩
      exact ⟨hnorm x hx y hyF, by rw [conj_pow, hy, mul_one, mul_inv_cancel]⟩
    · rintro ⟨hyF, hy⟩
      have h1 := hnorm x⁻¹ (F₀.inv_mem hx) _ hyF
      rw [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1
      exact ⟨h1, conj_eq_one_iff.1 (conj_pow.symm.trans hy)⟩
  refine ⟨F₀.index, ?_, by rw [h6, hFidx]⟩
  rw [Sylow.card_eq_index_normalizer (hTq.toSylow hTidx)]
  exact Subgroup.index_dvd_of_le hF₀N

theorem card_sylow_quotient_center {X : Type*} [Group X] [Finite X] {q : ℕ} [Fact q.Prime]
    (hZ : Nat.Coprime q (Nat.card (center X))) :
    Nat.card (Sylow q (X ⧸ center X)) = Nat.card (Sylow q X) := by
  obtain ⟨S⟩ : Nonempty (Sylow q X) := inferInstance
  haveI : Fact (IsPGroup q (S : Subgroup X)) := ⟨S.isPGroup'⟩
  have hidx : ¬ q ∣ ((S : Subgroup X).map (QuotientGroup.mk' (center X))).index := fun h =>
    S.not_dvd_index (h.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
  have hN : normalizer (((S : Subgroup X).map (QuotientGroup.mk' (center X)) : Subgroup _) :
      Set (X ⧸ center X)) = (normalizer ((S : Subgroup X) : Set X)).map
        (QuotientGroup.mk' (center X)) :=
    CFSG.normalizer_map_quotient_eq_map_normalizer q (S : Subgroup X) (center X) inferInstance hZ
  rw [Sylow.card_eq_index_normalizer ((S.isPGroup'.map _).toSylow hidx),
    Sylow.card_eq_index_normalizer S]
  change (normalizer (((S : Subgroup X).map (QuotientGroup.mk' (center X)) : Subgroup _) :
    Set (X ⧸ center X))).index = (normalizer ((S : Subgroup X) : Set X)).index
  have hle : (QuotientGroup.mk' (center X)).ker ≤ normalizer ((S : Subgroup X) : Set X) := by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.center_le_normalizer _
  rw [hN, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hle]

theorem u3SylOmega_of_griess (hgr : CFSG.Open.GriessAllModelsStatement) : U3SylOmega := by
  intro X _ _ n hX q hq hq3 hqn S hSq hSidx
  have hZ : ¬ q ∣ Nat.card (center X) := fun h =>
    absurd (Nat.le_of_dvd (by norm_num) (h.trans (u3Center_of_griess hgr X n hX))) (by omega)
  set e := (2 ^ n + 1).factorization q
  have he1 : 1 ≤ e := (hq.dvd_iff_one_le_factorization (by positivity)).1 hqn
  have hQ : 2 ^ n + 1 = q ^ e * ((2 ^ n + 1) / q ^ e) :=
    (Nat.mul_div_cancel' (Nat.ordProj_dvd _ _)).symm
  have hm : ¬ q ∣ (2 ^ n + 1) / q ^ e := Nat.not_dvd_ordCompl hq (by positivity)
  have hshape := CFSG.RankThree.PartOne.K1214.sylowShape_of_psu3Model hq (by omega) (by omega)
    he1 hQ hm (CFSG.SeitzReduction.RankOne.statedClassicalModel_of_lieModel_psu3 hX.2)
  obtain ⟨φ⟩ := CFSG.RankThree.PartOne.K1214.SylowShape.exists_equiv hq (center X) hZ hshape
    hSq hSidx
  have hab := homC_comm (p := q) (a := e) (r := 2) φ
  refine ⟨torsionSubgroup S hab q, fun x hx => ((mem_torsionSubgroup _ _ _).1 hx).1,
    ⟨torsionSubgroup_comm S hab q, fun x hx => ((mem_torsionSubgroup _ _ _).1 hx).2⟩, ?_,
    fun s hs hsq => (mem_torsionSubgroup _ _ _).2 ⟨hs, hsq⟩⟩
  rw [torsionSubgroup_card]
  have h1 : Nat.card {x : S // x ^ q = 1} =
      Nat.card {y : Fin 2 → Multiplicative (ZMod (q ^ e)) // y ^ q = 1} :=
    Nat.card_congr (φ.toEquiv.subtypeEquiv fun x => by
      change x ^ q = 1 ↔ φ x ^ q = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  have h2 : {y : Fin 2 → Multiplicative (ZMod (q ^ e)) // y ^ q = 1} ≃
      (Fin 2 → {z : Multiplicative (ZMod (q ^ e)) // z ^ q = 1}) :=
    (Equiv.subtypeEquivRight fun y => by
      rw [funext_iff]
      simp only [Pi.pow_apply, Pi.one_apply]).trans Equiv.subtypePiEquivPi
  rw [h1, Nat.card_congr h2, Nat.card_fun,
    CFSG.LocalAnalysis.SteinbergBV.card_cyclic_pow_eq_one hq he1]
  simp

theorem u3SylCount_of_griess (hgr : CFSG.Open.GriessAllModelsStatement) : U3SylCount := by
  intro X _ _ n hX q p hq hq3 hqn hp hp2 hpn
  haveI : Fact q.Prime := ⟨hq⟩
  have hn2 : 2 ≤ n := u3Range X n hX
  have hZ : Nat.Coprime q (Nat.card (center X)) := hq.coprime_iff_not_dvd.2 fun h =>
    absurd (Nat.le_of_dvd (by norm_num) (h.trans (u3Center_of_griess hgr X n hX))) (by omega)
  obtain ⟨e', hB⟩ := CFSG.SeitzReduction.RankOne.exists_benderType_of_lieModel_psu3 hn2 hX.2
  obtain ⟨hU, ⟨φ₀⟩⟩ := BenderType.exists_equiv_unitaryModelP hB
  let φ : X ⧸ center X ≃* primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))) :=
    φ₀
  obtain ⟨-, K, _, _, hK, ⟨ψ⟩⟩ :=
    CFSG.SeitzReduction.RankOne.statedClassicalModel_of_lieModel_psu3 hX.2
  have hKU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
  haveI : Finite (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)))) :=
    Finite.of_equiv _ φ.toEquiv
  have hcard : Nat.card (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)))) *
      Nat.gcd 3 (k + 2) = (k + 1) ^ 3 * (k * (k + 2)) * ((k + 2) * (k ^ 2 + k + 1)) := by
    have h := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul hKU
    rw [← Nat.card_congr φ.toEquiv, Nat.card_congr ψ.toEquiv, show k + 2 = 2 ^ n + 1 by omega, h,
      hk, show (k + 1) ^ 2 - 1 = k * (k + 2) from Nat.sub_eq_of_eq_add (by ring)]
    ring
  have hqk : q ∣ k + 2 := by rwa [show k + 2 = 2 ^ n + 1 by omega]
  have hpk : p ∣ k + 2 := by rwa [show k + 2 = 2 ^ n + 1 by omega]
  obtain ⟨N, hN, h6⟩ := frame_sylow_count hU hn2 hk hq3 hqk hcard
  rw [← card_sylow_quotient_center hZ,
    CFSG.LargeExtraspecial.Bender.card_sylow_congr φ q]
  exact fun h => not_dvd_of_six_mul hp hp2 hpk h6 (h.trans hN)

end CFSG.LocalAnalysis.UniquenessCase.UCK
