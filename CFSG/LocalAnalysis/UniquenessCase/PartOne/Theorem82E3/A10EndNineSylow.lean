module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPhi
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.AltCase
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
import CFSG.GroupTheory.CardMapInfKer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace A10Perm

open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

private def binv (k : Fin 3) : Perm (Fin 10) := swap (blockPt k 1) (blockPt k 2)

private def pat (i j k : Fin 3) : Perm (Fin 10) :=
  (if i = 2 then binv 0 else 1) * (if j = 2 then binv 1 else 1) * (if k = 2 then binv 2 else 1)

private theorem mem_normalizer_atilde_of_conj_gens {g : Perm (Fin 10)}
    (ha : g * pa * g⁻¹ ∈ atilde) (hb : g * pb * g⁻¹ ∈ atilde)
    (hc : g * pc * g⁻¹ ∈ atilde) :
    g ∈ normalizer (atilde : Set (Perm (Fin 10))) := by
  have hle : atilde.map (MulAut.conj g).toMonoidHom ≤ atilde := by
    rw [atilde, MonoidHom.map_closure, Subgroup.closure_le]
    rintro a ⟨b, hb', rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
    rcases hb' with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have heq : atilde.map (MulAut.conj g).toMonoidHom = atilde := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

private theorem pat_inv (i j k : Fin 3) : (pat i j k)⁻¹ = pat i j k := by
  have h2 : pat i j k * pat i j k = 1 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel
  exact inv_eq_of_mul_eq_one_right h2

private theorem binv_mem_normalizer (k : Fin 3) :
    binv k ∈ normalizer (atilde : Set (Perm (Fin 10))) := by
  fin_cases k
  · apply mem_normalizer_atilde_of_conj_gens
    · rw [mem_atilde_iff]; exact ⟨2, 0, 0, by decide +kernel⟩
    · rw [mem_atilde_iff]; exact ⟨0, 1, 0, by decide +kernel⟩
    · rw [mem_atilde_iff]; exact ⟨0, 0, 1, by decide +kernel⟩
  · apply mem_normalizer_atilde_of_conj_gens
    · rw [mem_atilde_iff]; exact ⟨1, 0, 0, by decide +kernel⟩
    · rw [mem_atilde_iff]; exact ⟨0, 2, 0, by decide +kernel⟩
    · rw [mem_atilde_iff]; exact ⟨0, 0, 1, by decide +kernel⟩
  · apply mem_normalizer_atilde_of_conj_gens
    · rw [mem_atilde_iff]; exact ⟨1, 0, 0, by decide +kernel⟩
    · rw [mem_atilde_iff]; exact ⟨0, 1, 0, by decide +kernel⟩
    · rw [mem_atilde_iff]; exact ⟨0, 0, 2, by decide +kernel⟩

private theorem pat_mem_normalizer (i j k : Fin 3) :
    pat i j k ∈ normalizer (atilde : Set (Perm (Fin 10))) := by
  simp only [pat]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · split_ifs with h
    · exact binv_mem_normalizer 0
    · exact Subgroup.one_mem _
  · split_ifs with h
    · exact binv_mem_normalizer 1
    · exact Subgroup.one_mem _
  · split_ifs with h
    · exact binv_mem_normalizer 2
    · exact Subgroup.one_mem _

private theorem pw_mem_normalizer : pw ∈ normalizer (atilde : Set (Perm (Fin 10))) := by
  apply mem_normalizer_atilde_of_conj_gens
  · rw [mem_atilde_iff]; exact ⟨0, 1, 0, by simpa [toP] using pw_mul_toP 1 0 0⟩
  · rw [mem_atilde_iff]; exact ⟨0, 0, 1, by simpa [toP] using pw_mul_toP 0 1 0⟩
  · rw [mem_atilde_iff]; exact ⟨1, 0, 0, by simpa [toP] using pw_mul_toP 0 0 1⟩

private theorem pw_notin_atilde : pw ∉ atilde := by
  intro h
  obtain ⟨i, j, k, hijk⟩ := mem_atilde_iff.mp h
  revert hijk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

private theorem support_toP_ne_zero (i j k : Fin 3) (h : (toP i j k).support.card = 9) :
    i ≠ 0 ∧ j ≠ 0 ∧ k ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    rw [support_toP] at h
    revert h
    fin_cases j <;> fin_cases k <;> decide +kernel
  · rintro rfl
    rw [support_toP] at h
    revert h
    fin_cases i <;> fin_cases k <;> decide +kernel
  · rintro rfl
    rw [support_toP] at h
    revert h
    fin_cases i <;> fin_cases j <;> decide +kernel

private theorem pw_commute_toP : Commute pw (toP 1 1 1) := by
  show pw * toP 1 1 1 = toP 1 1 1 * pw
  calc pw * toP 1 1 1 = (pw * toP 1 1 1 * pw⁻¹) * pw := by group
    _ = toP 1 1 1 * pw := by rw [pw_mul_toP]

private theorem pat_toP_conj {i j k : Fin 3} (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0) :
    pat i j k * toP i j k * (pat i j k)⁻¹ = toP 1 1 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    first
    | exact absurd rfl hi
    | exact absurd rfl hj
    | exact absurd rfl hk
    | decide +kernel

private theorem exists_commute_toP {i j k : Fin 3} (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0) :
    ∃ t : Perm (Fin 10), t ∈ normalizer (atilde : Set (Perm (Fin 10))) ∧ t ∉ atilde ∧
      t ^ 3 = 1 ∧ Commute t (toP i j k) := by
  have hpat_conj := pat_toP_conj hi hj hk
  have hp2 : pat i j k * pat i j k = 1 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel
  have hpinv := pat_inv i j k
  have hpw : Commute pw (toP 1 1 1) := pw_commute_toP
  have hx_eq : toP i j k = pat i j k * toP 1 1 1 * pat i j k := by
    have h := hpat_conj
    rw [hpinv] at h
    rw [← h]
    calc toP i j k = (pat i j k * pat i j k) * toP i j k * (pat i j k * pat i j k) := by
          rw [hp2]; group
      _ = pat i j k * (pat i j k * toP i j k * pat i j k) * pat i j k := by group
  refine ⟨pat i j k * pw * (pat i j k)⁻¹, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.normalizer (atilde : Set (Perm (Fin 10)))).mul_mem
      ((Subgroup.normalizer (atilde : Set (Perm (Fin 10)))).mul_mem
        (pat_mem_normalizer i j k) pw_mem_normalizer)
      ((Subgroup.normalizer (atilde : Set (Perm (Fin 10)))).inv_mem (pat_mem_normalizer i j k))
  · intro ht
    have hconj_mem : ∀ y ∈ atilde, (MulAut.conj (pat i j k)) y ∈ atilde := by
      intro y hy
      have h := (Subgroup.mem_normalizer_iff.mp (pat_mem_normalizer i j k)) y
      rw [MulAut.conj_apply]
      exact h.mp hy
    have hval : (MulAut.conj (pat i j k)) (pat i j k * pw * (pat i j k)⁻¹) = pw := by
      rw [MulAut.conj_apply, hpinv]
      calc pat i j k * (pat i j k * pw * pat i j k) * pat i j k
          = (pat i j k * pat i j k) * pw * (pat i j k * pat i j k) := by group
        _ = pw := by rw [hp2]; group
    have hpw_mem : (MulAut.conj (pat i j k)) (pat i j k * pw * (pat i j k)⁻¹) ∈ atilde :=
      hconj_mem _ ht
    rw [hval] at hpw_mem
    exact pw_notin_atilde hpw_mem
  · have hcube : (pat i j k * pw * (pat i j k)⁻¹) ^ 3 =
        pat i j k * pw ^ 3 * (pat i j k)⁻¹ := by
      simpa [MulAut.conj_apply] using
        (map_pow (MulAut.conj (pat i j k)).toMonoidHom pw 3).symm
    rw [hcube, pw_pow_three]
    group
  · have hconj := hpw.conj (pat i j k)
    simpa [hx_eq, hpinv] using hconj

theorem exists_mem_normalizer_commute {x : Perm (Fin 10)} (hx : x ∈ atilde)
    (hsupp : x.support.card = 9) :
    ∃ t : Perm (Fin 10), t ∈ normalizer (atilde : Set (Perm (Fin 10))) ∧ t ∉ atilde ∧
      t ^ 3 = 1 ∧ Commute t x := by
  obtain ⟨i, j, k, rfl⟩ := mem_atilde_iff.mp hx
  obtain ⟨hi, hj, hk⟩ := support_toP_ne_zero i j k hsupp
  exact exists_commute_toP hi hj hk

end A10Perm

namespace Ctx82E3.A10Frame

open scoped commutatorElement
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

variable {c : Ctx82E3 D}

private theorem factorization_card_alternatingGroup :
    (Nat.card (alternatingGroup (Fin 10))).factorization 3 = 4 := by
  obtain ⟨m, hm, hcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435.card_alt_eq (n := 10)
      (by norm_num) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 3)
  rw [hcard, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
    show (81 : ℕ) = 3 ^ 4 by norm_num, Nat.Prime.factorization_pow Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd hm]
  simp

private theorem factorization_card_M (F : A10Frame c) :
    (Nat.card ↥D.M).factorization 3 = 4 := by
  have hker : Nat.Coprime (Nat.card F.phiA.ker) 3 := F.coprime_card_ker_phiA
  have hnotdvd : ¬ 3 ∣ Nat.card F.phiA.ker :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hker.symm
  have hkerfact : (Nat.card F.phiA.ker).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnotdvd
  have h81dvd : 81 ∣ Nat.card F.phiA.range := by
    obtain ⟨m, -, hcard⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435.card_alt_eq (n := 10)
        (by norm_num) (by norm_num)
    have hdvd : Nat.card (alternatingGroup (Fin 10)) ∣ Nat.card F.phiA.range :=
      Subgroup.card_dvd_of_le F.alternatingGroup_le_range_phiA
    rw [hcard] at hdvd
    exact (dvd_mul_right 81 m).trans hdvd
  have hnot243 : ¬ 3 ^ 5 ∣ Nat.card F.phiA.range := by
    intro h
    have hdvd : 3 ^ 5 ∣ Nat.card (Equiv.Perm (Fin 10)) :=
      h.trans (Subgroup.card_subgroup_dvd_card F.phiA.range)
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hdvd
    norm_num [Nat.factorial] at hdvd
  have hne : Nat.card F.phiA.range ≠ 0 := Nat.card_pos.ne'
  have hge : 4 ≤ (Nat.card F.phiA.range).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hne).mp h81dvd
  have hle : (Nat.card F.phiA.range).factorization 3 ≤ 4 := by
    by_contra h
    have h5 : 5 ≤ (Nat.card F.phiA.range).factorization 3 := by omega
    exact hnot243 ((Nat.prime_three.pow_dvd_iff_le_factorization hne).mpr h5)
  have hrfact : (Nat.card F.phiA.range).factorization 3 = 4 := by omega
  have hMcard := Subgroup.card_ker_mul_card_range F.phiA
  rw [← hMcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
    Finsupp.add_apply, hkerfact, hrfact]

private noncomputable def phiQ (F : A10Frame c) {Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) : ↥Q →* Equiv.Perm (Fin 10) :=
  F.phiA.comp (Subgroup.inclusion hQ.le)

private theorem card_sylow_eq_81 (F : A10Frame c) {Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) : Nat.card Q = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [hQ.card_eq, factorization_card_M F]
  norm_num

private theorem phiQ_ker_eq_bot (F : A10Frame c) {Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) : (phiQ F hQ).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxK : Subgroup.inclusion hQ.le x ∈ F.phiA.ker := hx
  have hQ81 : Nat.card Q = 81 := card_sylow_eq_81 F hQ
  have hordQ : orderOf x ∣ Nat.card Q := by
    have h := Subgroup.orderOf_dvd_natCard Q x.2
    rwa [Subgroup.orderOf_coe] at h
  rw [hQ81] at hordQ
  have hordK : orderOf x ∣ Nat.card F.phiA.ker := by
    have h := Subgroup.orderOf_dvd_natCard F.phiA.ker hxK
    have hord_eq : orderOf (Subgroup.inclusion hQ.le x) = orderOf x :=
      orderOf_injective _ (Subgroup.inclusion_injective hQ.le) x
    rwa [hord_eq] at h
  have hcop : Nat.Coprime 81 (Nat.card F.phiA.ker) := by
    rw [show (81 : ℕ) = 3 ^ 4 by norm_num]
    exact Nat.Coprime.pow_left 4 F.coprime_card_ker_phiA.symm
  have hone : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hordQ hordK
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)

private theorem phiQ_injective (F : A10Frame c) {Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) :
    Function.Injective (phiQ F hQ) :=
  (MonoidHom.ker_eq_bot_iff (phiQ F hQ)).mp (phiQ_ker_eq_bot F hQ)

private theorem phiQ_range_le_alternating (F : A10Frame c) {Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) :
    (phiQ F hQ).range ≤ alternatingGroup (Fin 10) := by
  rintro y ⟨x, rfl⟩
  rw [Equiv.Perm.mem_alternatingGroup]
  have hQ81 : Nat.card Q = 81 := card_sylow_eq_81 F hQ
  have hx81 : x ^ 81 = 1 := by
    have h := orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard Q x.2)
    rw [hQ81] at h
    exact Subtype.ext (by simpa using h)
  have hsign : (Equiv.Perm.sign (phiQ F hQ x)) ^ 81 = 1 := by
    rw [← map_pow, ← map_pow, hx81, map_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (phiQ F hQ x)) with h | h
  · exact h
  · rw [h] at hsign
    norm_num at hsign

private theorem phiQ_card_range (F : A10Frame c) {Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) : Nat.card (phiQ F hQ).range = 81 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (phiQ_injective F hQ)).toEquiv,
    card_sylow_eq_81 F hQ]

theorem nonempty_mulEquiv_zwr (F : A10Frame c) {Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) :
    Nonempty (↥Q ≃* UC326.ZWr 1) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRle : (phiQ F hQ).range ≤ alternatingGroup (Fin 10) := phiQ_range_le_alternating F hQ
  let R' : Subgroup (alternatingGroup (Fin 10)) :=
    (phiQ F hQ).range.subgroupOf (alternatingGroup (Fin 10))
  have hcardR' : Nat.card R' = 81 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv).trans
      (phiQ_card_range F hQ)
  let S : Sylow 3 (alternatingGroup (Fin 10)) :=
    Sylow.ofCard R' (by rw [hcardR', factorization_card_alternatingGroup]; norm_num)
  have hScoe : (S : Subgroup (alternatingGroup (Fin 10))) = R' := Sylow.coe_ofCard _ _
  obtain ⟨e⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435.sylow_alt_W3 (n := 10)
    (by norm_num) (by norm_num) S
  exact ⟨(MonoidHom.ofInjective (phiQ_injective F hQ)).trans
    ((Subgroup.subgroupOfEquivOfLe hRle).symm.trans
      ((MulEquiv.subgroupCongr hScoe.symm).trans e))⟩

private theorem exists_zpowers_of_card_three {B : Subgroup G} (hB3 : Nat.card B = 3) :
    ∃ b : G, B = Subgroup.zpowers b := by
  haveI : IsCyclic ↥B := isCyclic_of_prime_card hB3
  obtain ⟨bB, hbB⟩ := IsCyclic.exists_generator (α := ↥B)
  refine ⟨(bB : G), ?_⟩
  have htop : Subgroup.zpowers bB = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact hbB y
  have hmap : Subgroup.map B.subtype (⊤ : Subgroup ↥B) = B := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h := congrArg (Subgroup.map B.subtype) htop
  rw [MonoidHom.map_zpowers, hmap] at h
  exact h.symm

private theorem exists_zpowers_deg_nine (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9) :
    ∃ b : G, B = Subgroup.zpowers b ∧ b ∈ F.A ∧ F.deg (Subgroup.zpowers b) = 9 := by
  obtain ⟨b, hbz⟩ := exists_zpowers_of_card_three hB3
  refine ⟨b, hbz, hBA (hbz.symm ▸ Subgroup.mem_zpowers b), ?_⟩
  rw [← hbz]
  exact hB9

private theorem mem_atilde_of_mem_A (F : A10Frame c) {a : G} (ha : a ∈ F.A) :
    F.phiA ⟨a, F.A_le_M ha⟩ ∈ A10Perm.atilde := by
  rw [← F.map_A_phiA]
  exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr ha)

private theorem support_phiA_of_deg_nine (F : A10Frame c) {a : G} (ha : a ∈ F.A)
    (hdeg : F.deg (Subgroup.zpowers a) = 9) :
    (F.phiA ⟨a, F.A_le_M ha⟩).support.card = 9 := by
  have h := F.deg_zpowers_eq (b := a) (F.P_le_L (F.A_le ha))
  rw [hdeg] at h
  simpa using h.symm

private theorem exists_t_commute_of_deg_nine (F : A10Frame c) {b : G} (hbA : b ∈ F.A)
    (hb9 : F.deg (Subgroup.zpowers b) = 9) :
    ∃ t : Equiv.Perm (Fin 10),
      t ∈ Subgroup.normalizer (A10Perm.atilde : Set (Equiv.Perm (Fin 10))) ∧
        t ∉ A10Perm.atilde ∧ t ^ 3 = 1 ∧
        Commute t (F.phiA ⟨b, F.A_le_M hbA⟩) :=
  A10Perm.exists_mem_normalizer_commute (mem_atilde_of_mem_A F hbA)
    (support_phiA_of_deg_nine F hbA hb9)

private theorem card_sup_atilde_zpowers (F : A10Frame c) {t : Equiv.Perm (Fin 10)}
    (htN : t ∈ Subgroup.normalizer (A10Perm.atilde : Set (Equiv.Perm (Fin 10))))
    (htnot : t ∉ A10Perm.atilde) (ht3 : t ^ 3 = 1) :
    Nat.card (A10Perm.atilde ⊔ Subgroup.zpowers t : Subgroup (Equiv.Perm (Fin 10))) = 81 := by
  have htne : t ≠ 1 := fun h1 => htnot (h1 ▸ Subgroup.one_mem A10Perm.atilde)
  have htord : orderOf t = 3 := orderOf_eq_prime ht3 htne
  have hcardz : Nat.card (Subgroup.zpowers t) = 3 := by
    rw [Nat.card_zpowers, htord]
  have hdisj : Disjoint A10Perm.atilde (Subgroup.zpowers t) := by
    rw [disjoint_iff]
    have hdvd : Nat.card (A10Perm.atilde ⊓ Subgroup.zpowers t :
        Subgroup (Equiv.Perm (Fin 10))) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_right : A10Perm.atilde ⊓ Subgroup.zpowers t ≤ Subgroup.zpowers t)
      rwa [hcardz] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : A10Perm.atilde ⊓ Subgroup.zpowers t = Subgroup.zpowers t :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcardz, h3])
      exact htnot (heq.ge (Subgroup.mem_zpowers t)).1
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    (Subgroup.zpowers_le.mpr htN) hdisj, A10Perm.card_atilde, hcardz]

private theorem sup_atilde_zpowers_le_alternating {t : Equiv.Perm (Fin 10)} (ht3 : t ^ 3 = 1) :
    A10Perm.atilde ⊔ Subgroup.zpowers t ≤ alternatingGroup (Fin 10) := by
  apply sup_le A10Perm.atilde_le_alternatingGroup
  rw [Subgroup.zpowers_le, Equiv.Perm.mem_alternatingGroup]
  have hs3 : (Equiv.Perm.sign t) ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign t) with h | h
  · exact h
  · rw [h] at hs3
    norm_num at hs3

private theorem sup_atilde_zpowers_le_centralizer {t x : Equiv.Perm (Fin 10)}
    (htcomm : Commute t x) (hxat : x ∈ A10Perm.atilde) :
    A10Perm.atilde ⊔ Subgroup.zpowers t ≤
      Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 10))) := by
  apply sup_le ?_ ?_
  · intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (A10Perm.isElemAbelian_atilde.1.is_comm.comm ⟨a, ha⟩ ⟨x, hxat⟩)
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact htcomm.eq

private theorem range_comap_subtype (F : A10Frame c) {S' : Subgroup (Equiv.Perm (Fin 10))}
    (hS'leR : S' ≤ F.phiA.range) :
    (F.phiA.comp (S'.comap F.phiA).subtype).range = S' := by
  have hmap_top : Subgroup.map (S'.comap F.phiA).subtype
      (⊤ : Subgroup ↥(S'.comap F.phiA)) = S'.comap F.phiA := by
    simpa using Subgroup.map_subgroupOf_eq_of_le (H := S'.comap F.phiA)
      (K := S'.comap F.phiA) le_rfl
  rw [MonoidHom.range_eq_map, ← Subgroup.map_map, hmap_top]
  exact Subgroup.map_comap_eq_self hS'leR

private theorem card_comap_of_le_range (F : A10Frame c) {S' : Subgroup (Equiv.Perm (Fin 10))}
    (hS'leR : S' ≤ F.phiA.range) :
    Nat.card (S'.comap F.phiA) = Nat.card F.phiA.ker * Nat.card S' := by
  let N : Subgroup ↥D.M := S'.comap F.phiA
  let φN : ↥N →* Equiv.Perm (Fin 10) := F.phiA.comp N.subtype
  have hkerN : Nat.card φN.ker = Nat.card F.phiA.ker := by
    have hker_le : F.phiA.ker ≤ N := by
      intro y hy
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mpr hy]
      exact Subgroup.one_mem S'
    have hker_eq : φN.ker = F.phiA.ker.subgroupOf N := by
      change (F.phiA.comp N.subtype).ker = _
      rw [← MonoidHom.comap_ker, Subgroup.comap_subtype]
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  have hrangeN : φN.range = S' := by
    change (F.phiA.comp (S'.comap F.phiA).subtype).range = S'
    exact range_comap_subtype F hS'leR
  have h := Subgroup.card_ker_mul_card_range φN
  rw [hkerN, hrangeN] at h
  exact h.symm

private theorem exists_sylow_comap (F : A10Frame c) {S' : Subgroup (Equiv.Perm (Fin 10))}
    (hS'card : Nat.card S' = 81) (hS'leR : S' ≤ F.phiA.range) (hAS' : A10Perm.atilde ≤ S') :
    ∃ Q : Subgroup ↥D.M, Nat.card Q = 81 ∧ (F.A.subgroupOf D.M) ≤ Q ∧ Q.map F.phiA ≤ S' := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥D.M := S'.comap F.phiA
  have hAleN : F.A.subgroupOf D.M ≤ N := by
    intro y hy
    rw [Subgroup.mem_comap]
    exact hAS' (by
      rw [← F.map_A_phiA]
      exact Subgroup.mem_map_of_mem F.phiA hy)
  have hA3M : IsPGroup 3 (F.A.subgroupOf D.M) := by
    have h := (F.elemAbelian.isPGroup).comap_subtype (K := D.M)
    rwa [Subgroup.comap_subtype] at h
  have hA3N : IsPGroup 3 ((F.A.subgroupOf D.M).subgroupOf N) := by
    have h := hA3M.comap_subtype (K := N)
    rwa [Subgroup.comap_subtype] at h
  obtain ⟨S, hSle⟩ := hA3N.exists_le_sylow
  let Q : Subgroup ↥D.M := (S : Subgroup ↥N).map N.subtype
  have hNcard : Nat.card ↥N = Nat.card F.phiA.ker * Nat.card S' := by
    change Nat.card (S'.comap F.phiA) = _
    exact card_comap_of_le_range F hS'leR
  have hkerfact : (Nat.card F.phiA.ker).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp F.coprime_card_ker_phiA.symm)
  have hS'fact : (Nat.card S').factorization 3 = 4 := by
    rw [hS'card, show (81 : ℕ) = 3 ^ 4 by norm_num,
      Nat.factorization_pow_self Nat.prime_three]
  have hNfact : (Nat.card ↥N).factorization 3 = 4 := by
    rw [hNcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Finsupp.add_apply, hkerfact, hS'fact]
  have hS81 : Nat.card (S : Subgroup ↥N) = 81 := by
    rw [Sylow.card_eq_multiplicity, hNfact]
    norm_num
  have hQ81 : Nat.card Q = 81 := by
    change Nat.card ((S : Subgroup ↥N).map N.subtype) = 81
    rw [Subgroup.card_map_of_injective N.subtype_injective, hS81]
  refine ⟨Q, hQ81, ?_, ?_⟩
  · intro y hy
    exact Subgroup.mem_map.mpr ⟨⟨y, hAleN hy⟩, hSle (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  · have h1 : Q.map F.phiA = Subgroup.map (F.phiA.comp N.subtype) (S : Subgroup ↥N) := by
      change Subgroup.map F.phiA (Subgroup.map N.subtype (S : Subgroup ↥N)) = _
      rw [Subgroup.map_map]
    rw [h1]
    have h2 := Subgroup.map_le_range (F.phiA.comp N.subtype) (S : Subgroup ↥N)
    have hrange : (F.phiA.comp N.subtype).range = S' := by
      change (F.phiA.comp (S'.comap F.phiA).subtype).range = S'
      exact range_comap_subtype F hS'leR
    rwa [hrange] at h2

private theorem inf_ker_eq_bot_of_card_eq_81 (F : A10Frame c) {Q : Subgroup ↥D.M}
    (hQ81 : Nat.card Q = 81) : Q ⊓ F.phiA.ker = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyQ, hyK⟩ := Subgroup.mem_inf.mp hy
  have hordQ : orderOf y ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard Q hyQ
  rw [hQ81] at hordQ
  have hordK : orderOf y ∣ Nat.card F.phiA.ker :=
    Subgroup.orderOf_dvd_natCard F.phiA.ker hyK
  have hcop : Nat.Coprime 81 (Nat.card F.phiA.ker) := by
    rw [show (81 : ℕ) = 3 ^ 4 by norm_num]
    exact Nat.Coprime.pow_left 4 F.coprime_card_ker_phiA.symm
  have hone : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop hordQ hordK
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)

private theorem centralizes_of_map_le (F : A10Frame c) {Q : Subgroup ↥D.M}
    {S' : Subgroup (Equiv.Perm (Fin 10))} {x : Equiv.Perm (Fin 10)}
    (hQ81 : Nat.card Q = 81) (hQmap : Q.map F.phiA ≤ S')
    (hS'cent : S' ≤ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 10))))
    {bM : ↥D.M} (hbM : bM ∈ Q) (hx : x = F.phiA bM) :
    Q ≤ Subgroup.centralizer ({bM} : Set ↥D.M) := by
  intro q hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hqphi : F.phiA q ∈ S' := hQmap (Subgroup.mem_map_of_mem F.phiA hq)
  have hcommphi : F.phiA q * x = x * F.phiA q :=
    Subgroup.mem_centralizer_singleton_iff.mp (hS'cent hqphi)
  have hmemQ : ⁅q, bM⁆ ∈ Q :=
    Subgroup.commutator_le_self Q (Subgroup.commutator_mem_commutator hq hbM)
  have hmemK : ⁅q, bM⁆ ∈ F.phiA.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    simpa [hx] using hcommphi
  have hcomm_one : ⁅q, bM⁆ = 1 := by
    have hinf : ⁅q, bM⁆ ∈ Q ⊓ F.phiA.ker := ⟨hmemQ, hmemK⟩
    rw [inf_ker_eq_bot_of_card_eq_81 F hQ81] at hinf
    exact Subgroup.mem_bot.mp hinf
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm_one

private theorem isSylowOf_map_of_card_81 (F : A10Frame c) {Q : Subgroup ↥D.M}
    (hQ81 : Nat.card Q = 81) :
    CFSG.ABGLocalTools.IsSylowOf 3 (Q.map D.M.subtype) D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply CFSG.ABGLocalTools.isSylowOf_of_card (P := Q.map D.M.subtype) (K := D.M)
  · exact Subgroup.map_subtype_le _
  · rw [Subgroup.card_map_of_injective D.M.subtype_injective, hQ81, factorization_card_M F]
    norm_num

private theorem A_le_map_of_le (F : A10Frame c) {Q : Subgroup ↥D.M}
    (hAQ : F.A.subgroupOf D.M ≤ Q) : F.A ≤ Q.map D.M.subtype := by
  intro a ha
  have hM : a ∈ D.M := F.A_le_M ha
  have hmemA : (⟨a, hM⟩ : ↥D.M) ∈ F.A.subgroupOf D.M := Subgroup.mem_subgroupOf.mpr ha
  exact Subgroup.mem_map.mpr ⟨⟨a, hM⟩, hAQ hmemA, rfl⟩

private theorem map_subtype_le_centralizer {B : Subgroup G} {Q : Subgroup ↥D.M} {b : G}
    (hbz : B = Subgroup.zpowers b) (hbM : b ∈ D.M)
    (hQcent : Q ≤ Subgroup.centralizer ({(⟨b, hbM⟩ : ↥D.M)} : Set ↥D.M)) :
    Q.map D.M.subtype ≤ Subgroup.centralizer (B : Set G) := by
  have hcent : Subgroup.centralizer (B : Set G) = Subgroup.centralizer ({b} : Set G) := by
    rw [hbz, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  intro x hx
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hx
  rw [← hqx, hcent, Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hQcent hq))

theorem exists_isSylowOf_le_centralizer (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9) :
    ∃ P' : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P' D.M ∧ F.A ≤ P' ∧
      P' ≤ Subgroup.centralizer (B : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hbz, hbA, hb9⟩ := exists_zpowers_deg_nine F hBA hB3 hB9
  obtain ⟨t, htN, htnot, ht3, htcomm⟩ := exists_t_commute_of_deg_nine F hbA hb9
  let S' : Subgroup (Equiv.Perm (Fin 10)) := A10Perm.atilde ⊔ Subgroup.zpowers t
  have hS'card : Nat.card S' = 81 := card_sup_atilde_zpowers F htN htnot ht3
  have hS'leA : S' ≤ alternatingGroup (Fin 10) := sup_atilde_zpowers_le_alternating ht3
  have hS'leR : S' ≤ F.phiA.range := hS'leA.trans F.alternatingGroup_le_range_phiA
  have hxat : F.phiA ⟨b, F.A_le_M hbA⟩ ∈ A10Perm.atilde := mem_atilde_of_mem_A F hbA
  have hS'cent : S' ≤ Subgroup.centralizer
      ({F.phiA ⟨b, F.A_le_M hbA⟩} : Set (Equiv.Perm (Fin 10))) :=
    sup_atilde_zpowers_le_centralizer htcomm hxat
  obtain ⟨Q, hQ81, hAQ, hQmap⟩ :=
    exists_sylow_comap F hS'card hS'leR (show A10Perm.atilde ≤ S' from le_sup_left)
  have hbM : (⟨b, F.A_le_M hbA⟩ : ↥D.M) ∈ Q := hAQ (Subgroup.mem_subgroupOf.mpr hbA)
  have hQcent := centralizes_of_map_le F hQ81 hQmap hS'cent hbM rfl
  exact ⟨Q.map D.M.subtype, isSylowOf_map_of_card_81 F hQ81, A_le_map_of_le F hAQ,
    map_subtype_le_centralizer hbz (F.A_le_M hbA) hQcent⟩

private lemma exists_mem_A_phiA_eq (F : A10Frame c) {g : Equiv.Perm (Fin 10)}
    (hg : g ∈ A10Perm.atilde) :
    ∃ a : G, ∃ ha : a ∈ F.A, F.phiA ⟨a, F.A_le_M ha⟩ = g := by
  rw [← F.map_A_phiA] at hg
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
  exact ⟨(x : G), Subgroup.mem_subgroupOf.mp hx, by simpa using hxg⟩

private lemma deg_zpowers_of_phiA_eq (F : A10Frame c) {a : G} (ha : a ∈ F.A)
    {g : Equiv.Perm (Fin 10)} (hg : F.phiA ⟨a, F.A_le_M ha⟩ = g) :
    F.deg (Subgroup.zpowers a) = g.support.card := by
  have h := F.deg_zpowers_eq (b := a) (F.P_le_L (F.A_le ha))
  rw [h]
  exact congrArg (fun t : Equiv.Perm (Fin 10) => t.support.card) hg

private theorem inf_ker_phiA_eq_bot (F : A10Frame c) :
    F.A.subgroupOf D.M ⊓ F.phiA.ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxK⟩ := Subgroup.mem_inf.mp hx
  have hx3G : (x : G) ^ 3 = 1 :=
    F.elemAbelian.2 (x : G) (Subgroup.mem_subgroupOf.mp hxA)
  have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa using hx3G)
  have hord3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have hordK : orderOf x ∣ Nat.card F.phiA.ker :=
    Subgroup.orderOf_dvd_natCard F.phiA.ker hxK
  have hone : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes F.coprime_card_ker_phiA.symm hord3 hordK
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)

private theorem map_subgroupOf_closure_eq_atilde (F : A10Frame c) {C : Subgroup G}
    (hC_le_A : C ≤ F.A) {a1 a2 a3 : G}
    (hC1 : a1 ∈ C) (hC2 : a2 ∈ C) (hC3 : a3 ∈ C)
    (hphi1 : F.phiA ⟨a1, F.A_le_M (hC_le_A hC1)⟩ = pa)
    (hphi2 : F.phiA ⟨a2, F.A_le_M (hC_le_A hC2)⟩ = pb)
    (hphi3 : F.phiA ⟨a3, F.A_le_M (hC_le_A hC3)⟩ = pc) :
    (C.subgroupOf D.M).map F.phiA = A10Perm.atilde := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxM : (x : G) ∈ F.A :=
      hC_le_A (Subgroup.mem_subgroupOf.mp hx)
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr hxM)
  · rw [A10Perm.atilde]
    apply (Subgroup.closure_le ((C.subgroupOf D.M).map F.phiA)).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Subgroup.mem_map.mpr ⟨⟨a1, F.A_le_M (hC_le_A hC1)⟩,
        Subgroup.mem_subgroupOf.mpr hC1, hphi1⟩
    · exact Subgroup.mem_map.mpr ⟨⟨a2, F.A_le_M (hC_le_A hC2)⟩,
        Subgroup.mem_subgroupOf.mpr hC2, hphi2⟩
    · exact Subgroup.mem_map.mpr ⟨⟨a3, F.A_le_M (hC_le_A hC3)⟩,
        Subgroup.mem_subgroupOf.mpr hC3, hphi3⟩

private theorem card_closure_eq_27 (F : A10Frame c) {C : Subgroup G} (hC_le_A : C ≤ F.A)
    (hCMmap : (C.subgroupOf D.M).map F.phiA = A10Perm.atilde) : Nat.card C = 27 := by
  have hC_le_M : C ≤ D.M := hC_le_A.trans F.A_le_M
  have hCM_le_A : C.subgroupOf D.M ≤ F.A.subgroupOf D.M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hC_le_A hx
  have hdisjCM : C.subgroupOf D.M ⊓ F.phiA.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxCM, hxK⟩ := Subgroup.mem_inf.mp hx
    have hxinf : x ∈ F.A.subgroupOf D.M ⊓ F.phiA.ker := ⟨hCM_le_A hxCM, hxK⟩
    rwa [inf_ker_phiA_eq_bot F] at hxinf
  have hCMcard : Nat.card (C.subgroupOf D.M) = 27 := by
    rw [← CFSG.card_map_eq_card_of_inf_ker_eq_bot F.phiA hdisjCM, hCMmap,
      A10Perm.card_atilde]
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC_le_M).toEquiv]
  exact hCMcard

private theorem A_le_closure_of_phiA_generators (F : A10Frame c) {a1 a2 a3 : G}
    (ha1 : a1 ∈ F.A) (ha2 : a2 ∈ F.A) (ha3 : a3 ∈ F.A)
    (hphi1 : F.phiA ⟨a1, F.A_le_M ha1⟩ = pa)
    (hphi2 : F.phiA ⟨a2, F.A_le_M ha2⟩ = pb)
    (hphi3 : F.phiA ⟨a3, F.A_le_M ha3⟩ = pc) :
    F.A ≤ Subgroup.closure ({a1, a2, a3} : Set G) := by
  let C : Subgroup G := Subgroup.closure ({a1, a2, a3} : Set G)
  have hC_le_A : C ≤ F.A := by
    apply (Subgroup.closure_le F.A).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha1
    · exact ha2
    · exact ha3
  have hC1 : a1 ∈ C := Subgroup.subset_closure (by simp)
  have hC2 : a2 ∈ C := Subgroup.subset_closure (by simp)
  have hC3 : a3 ∈ C := Subgroup.subset_closure (by simp)
  have hmap := map_subgroupOf_closure_eq_atilde F hC_le_A hC1 hC2 hC3
    (by simpa using hphi1) (by simpa using hphi2) (by simpa using hphi3)
  have hcard := card_closure_eq_27 F hC_le_A hmap
  have hCeq : C = F.A :=
    Subgroup.eq_of_le_of_card_ge hC_le_A (by rw [hcard, F.card_A])
  change F.A ≤ C
  rw [hCeq]

private theorem card_inf_z2Of_eq_nine (F : A10Frame c) {P' : Subgroup G}
    (hP' : CFSG.ABGLocalTools.IsSylowOf 3 P' D.M) (hAP' : F.A ≤ P') :
    Nat.card (F.A ⊓ UC326.z2Of P' : Subgroup G) = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_zwr F hP'
  obtain ⟨AP, hET, -, -, huniq, -⟩ := UC326.zwr_unique_E27 (n := 1) le_rfl e
  have hAQ_elem : CFSG.Open.IsElemAbelian 3 (F.A.subgroupOf P') :=
    F.elemAbelian.subgroupOf P'
  have hAQ_card : Nat.card (F.A.subgroupOf P') = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP').toEquiv).trans F.card_A
  have hAQ_eq : F.A.subgroupOf P' = AP := huniq _ hAQ_elem hAQ_card
  have hET' : CFSG.elemThompson ↥P' 3 = F.A.subgroupOf P' := by
    rw [hET, hAQ_eq]
  have h9 := (UC326.zwr_A_uniserial (n := 1) le_rfl e hET').2.1
  have hz2sub : (UC326.z2Of P').subgroupOf P' = Subgroup.upperCentralSeries ↥P' 2 := by
    rw [UC326.z2Of, ← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective P'.subtype_injective _
  have hinfsub : (F.A ⊓ UC326.z2Of P').subgroupOf P' =
      F.A.subgroupOf P' ⊓ Subgroup.upperCentralSeries ↥P' 2 := by
    ext x
    have hx2 : (x : G) ∈ UC326.z2Of P' ↔ x ∈ Subgroup.upperCentralSeries ↥P' 2 := by
      rw [← Subgroup.mem_subgroupOf, hz2sub]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, hx2.mp h.2⟩, fun h => ⟨h.1, hx2.mpr h.2⟩⟩
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (H := F.A ⊓ UC326.z2Of P') (K := P') (le_trans inf_le_left hAP')).toEquiv,
    hinfsub]
  exact h9

theorem exists_deg_three_not_mem_z2Of (F : A10Frame c) {P' : Subgroup G}
    (hP' : CFSG.ABGLocalTools.IsSylowOf 3 P' D.M) (hAP' : F.A ≤ P') :
    ∃ a ∈ F.A, F.deg (Subgroup.zpowers a) = 3 ∧ a ∉ UC326.z2Of P' := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpa : pa ∈ A10Perm.atilde := Subgroup.subset_closure (by simp)
  have hpb : pb ∈ A10Perm.atilde := Subgroup.subset_closure (by simp)
  have hpc : pc ∈ A10Perm.atilde := Subgroup.subset_closure (by simp)
  obtain ⟨a1, ha1, hphi1⟩ := exists_mem_A_phiA_eq F hpa
  obtain ⟨a2, ha2, hphi2⟩ := exists_mem_A_phiA_eq F hpb
  obtain ⟨a3, ha3, hphi3⟩ := exists_mem_A_phiA_eq F hpc
  have hdeg1 : F.deg (Subgroup.zpowers a1) = 3 := by
    rw [deg_zpowers_of_phiA_eq F ha1 hphi1]
    decide +kernel
  have hdeg2 : F.deg (Subgroup.zpowers a2) = 3 := by
    rw [deg_zpowers_of_phiA_eq F ha2 hphi2]
    decide +kernel
  have hdeg3 : F.deg (Subgroup.zpowers a3) = 3 := by
    rw [deg_zpowers_of_phiA_eq F ha3 hphi3]
    decide +kernel
  have hA_le_closure := A_le_closure_of_phiA_generators F ha1 ha2 ha3 hphi1 hphi2 hphi3
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hz1 : a1 ∈ UC326.z2Of P' := hcon a1 ha1 hdeg1
  have hz2 : a2 ∈ UC326.z2Of P' := hcon a2 ha2 hdeg2
  have hz3 : a3 ∈ UC326.z2Of P' := hcon a3 ha3 hdeg3
  have hAz : F.A ≤ UC326.z2Of P' := by
    refine hA_le_closure.trans ?_
    apply (Subgroup.closure_le (UC326.z2Of P')).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hz1
    · exact hz2
    · exact hz3
  have h9 := card_inf_z2Of_eq_nine F hP' hAP'
  have h27 : Nat.card (F.A ⊓ UC326.z2Of P' : Subgroup G) = 27 := by
    rw [inf_eq_left.mpr hAz, F.card_A]
  rw [h27] at h9
  exact absurd h9 (by norm_num)

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
