module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.Walter.W67.Section5.P56AbHallTools
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1616Comm

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card_thetaCen (X : Set G) : ¬ 3 ∣ Nat.card (thetaCen X) := by
  obtain ⟨-, -, hc3, -⟩ := solvable_prime_complement_core_characterization
    (H := ↥(Subgroup.centralizer X)) Nat.prime_three
  rw [thetaCen, inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact hc3

theorem isSolvable_thetaCen (X : Set G) : Group.IsSolvable (thetaCen X) := by
  obtain ⟨hs, -⟩ := solvable_prime_complement_core_characterization
    (H := ↥(Subgroup.centralizer X)) Nat.prime_three
  set e := (aschbacherSolvableCore 3 ↥(Subgroup.centralizer X)).equivMapOfInjective
    (Subgroup.centralizer X).subtype (Subgroup.subtype_injective _)
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

theorem mem_scriptQ_of_le_thetaCen {A Q : Subgroup G} {a : G}
    (ha : a ∈ A) (hQ : Q ≤ thetaCen ({a} : Set G))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (LB : Subgroup G → Subgroup G) :
    Q ∈ scriptQ A LB := by
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set θ := thetaCen ({a} : Set G) with hθ
  have hθ3 : ¬ 3 ∣ Nat.card θ := not_three_dvd_card_thetaCen _
  have hCaθ : Ca ≤ Subgroup.normalizer (θ : Set G) := centralizer_le_normalizer_thetaCen _
  have hθCa : θ ≤ Ca := Subgroup.map_subtype_le _
  have hQ3 : ¬ 3 ∣ Nat.card Q := fun h => hθ3 (h.trans (Subgroup.card_dvd_of_le hQ))
  refine ⟨⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three Q).mpr hQ3, hAQ⟩, fun B hB => ?_⟩
  set Y := θ ⊓ Subgroup.centralizer (B : Set G) with hY
  have hQY : Q ⊓ Subgroup.centralizer (B : Set G) ≤ Y := inf_le_inf_right _ hQ
  have hcop : Nat.Coprime 3 (Nat.card Y) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      fun h => hθ3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  refine hQY.trans ?_
  unfold qBound
  by_cases haB : a ∈ B
  · have hCB : Subgroup.centralizer (B : Set G) ≤ Ca :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)
    have hle : Y ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
      le_pPrimeCoreOf inf_le_right (le_normalizer_inf (hCB.trans hCaθ) Subgroup.le_normalizer)
        hcop
    exact hle.trans (le_sup_left.trans le_sup_left)
  · have hAM := le_zpowers_sup_of_not_mem hB ha haB
    have hCAB : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.centralizer_le hB.1
    have hCACa : Subgroup.centralizer (A : Set G) ≤ Ca :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)
    have hleA : Y ≤ Subgroup.centralizer (A : Set G) := by
      rintro x ⟨hxθ, hxB⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hsub : Subgroup.zpowers a ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp (hθCa hxθ)).symm
        · intro z hz
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hxB z hz)
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hsub (hAM hy)))
    have hle : Y ≤ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
      le_pPrimeCoreOf hleA (le_normalizer_inf (hCACa.trans hCaθ)
        (hCAB.trans Subgroup.le_normalizer)) hcop
    exact hle.trans (le_sup_right.trans le_sup_left)

theorem coprime_of_primes {π : Set Nat.Primes} {m n : ℕ}
    (hm : ∀ p : Nat.Primes, (p : ℕ) ∣ m → p ∈ π) (hn : ∀ p : Nat.Primes, (p : ℕ) ∣ n → p ∉ π) :
    Nat.Coprime m n :=
  Nat.coprime_of_dvd fun k hk hkm hkn => hn ⟨k, hk⟩ hkn (hm ⟨k, hk⟩ hkm)

theorem exists_mul_eq_of_isHall {K : Type*} [Group K] [Finite K] {π : Set Nat.Primes}
    {R T : Subgroup K} (hR : IsHallSubgroup π R) (hT : IsHallSubgroup πᶜ T) (x : K) :
    ∃ r ∈ R, ∃ t ∈ T, x = r * t := by
  have hRT : Nat.Coprime (Nat.card R) (Nat.card T) :=
    coprime_of_primes (π := π) hR.p_in_pi_of_p_dvd_card fun p hp hpπ =>
      hT.p_in_pi_of_p_dvd_card p hp hpπ
  have hRi : Nat.Coprime R.index T.index :=
    coprime_of_primes (π := πᶜ) (fun p hp => hR.p_in_pi_of_p_dvd_index p hp)
      fun p hp hpπ => hT.p_in_pi_of_p_dvd_index p hp hpπ
  have hcardR := R.card_mul_index
  have hcardT := T.card_mul_index
  have hcard : Nat.card R * Nat.card T = Nat.card K := by
    apply Nat.dvd_antisymm
    · exact hRT.mul_dvd_of_dvd_of_dvd (Subgroup.card_subgroup_dvd_card R)
        (Subgroup.card_subgroup_dvd_card T)
    · have hdvd : R.index ∣ Nat.card T := by
        have h1 : R.index ∣ Nat.card T * T.index := by
          rw [hcardT]
          exact R.index_dvd_card
        exact (Nat.Coprime.dvd_of_dvd_mul_right hRi h1)
      rw [← hcardR]
      exact Nat.mul_dvd_mul_left _ hdvd
  have hc := Subgroup.isComplement'_of_coprime hcard hRT
  obtain ⟨⟨r, t⟩, hrt, -⟩ := hc.existsUnique x
  exact ⟨r, r.2, t, t.2, hrt.symm⟩

omit [Finite G] in
theorem commutator_le_of_mul_eq {X A R T : Subgroup G}
    (hX : ∀ x ∈ X, ∃ r ∈ R, ∃ t ∈ T, x = r * t)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hTA : ⁅T, A⁆ = ⊥) : ⁅X, A⁆ ≤ R := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨r, hr, t, ht, rfl⟩ := hX x hx
  have hty : t * y = y * t := by
    have h1 : ⁅t, y⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator ht hy
      rw [hTA] at this
      exact this
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have heq : ⁅r * t, y⁆ = r * (y * r⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]
    calc r * t * y * (r * t)⁻¹ * y⁻¹ = r * (t * y) * t⁻¹ * r⁻¹ * y⁻¹ := by group
      _ = r * (y * t) * t⁻¹ * r⁻¹ * y⁻¹ := by rw [hty]
      _ = r * (y * r⁻¹ * y⁻¹) := by group
  rw [heq]
  refine R.mul_mem hr ?_
  exact (Subgroup.mem_normalizer_iff.mp (hAR hy) r⁻¹).mp (R.inv_mem hr)

omit [Finite G] in
theorem commutator_map_conj_eq_bot {S A : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) (hSA : ⁅S, A⁆ = ⊥) :
    ⁅S.map (MulAut.conj w).toMonoidHom, A⁆ = ⊥ := by
  have hA : A.map (MulAut.conj w).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hw
  rw [← hA, ← Subgroup.map_commutator, hSA, Subgroup.map_bot]

end CFSG.RankThree.PartTwo.Sec16.Proof1616Comm

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.RankThree.PartTwo.Sec16.Proof1616Comm CFSG.GH74.GLS

theorem step1616Comm_of (h1411 : Item1411_1R) : Step1616Comm := by
  intro G _ _ A c L h S hS hSA a ha ha1
  set θ := thetaCen ({a} : Set G) with hθdef
  have hAab : IsMulCommutative A := h.isElemAbelian.1
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa using congrArg Subtype.val (hAab.is_comm.comm ⟨x, hx⟩ ⟨a, ha⟩))
  have hAθ : A ≤ Subgroup.normalizer (θ : Set G) :=
    hAC.trans (centralizer_le_normalizer_thetaCen _)
  have hθs : Group.IsSolvable θ := isSolvable_thetaCen _
  have hθ3 : ¬ 3 ∣ Nat.card θ := not_three_dvd_card_thetaCen _
  have hcop : Nat.Coprime (Nat.card A) (Nat.card θ) := by
    rw [h.card_eq, show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
  obtain ⟨R, hRθ, hRH, hAR, -⟩ := CFSG.Walter.W67.P56Ab.exists_hall_invariant (π := (piOf 2)ᶜ)
    hAθ hθs hcop bot_le (fun p hp => by rw [Subgroup.card_bot] at hp
                                        exact absurd hp p.2.not_dvd_one)
    (by rw [Subgroup.normalizer_eq_top ⊥]; exact le_top)
  obtain ⟨T, hTθ, hTH, hAT, -⟩ := CFSG.Walter.W67.P56Ab.exists_hall_invariant (π := piOf 2)
    hAθ hθs hcop bot_le (fun p hp => by rw [Subgroup.card_bot] at hp
                                        exact absurd hp p.2.not_dvd_one)
    (by rw [Subgroup.normalizer_eq_top ⊥]; exact le_top)
  have hTH' : IsHallSubgroup (piOf 2)ᶜᶜ (T.subgroupOf θ) := by rwa [compl_compl]
  have hfac : ∀ x ∈ θ, ∃ r ∈ R, ∃ t ∈ T, x = r * t := by
    intro x hx
    obtain ⟨r, hr, t, ht, hrt⟩ := exists_mul_eq_of_isHall hRH hTH' ⟨x, hx⟩
    exact ⟨r, Subgroup.mem_subgroupOf.mp hr, t, Subgroup.mem_subgroupOf.mp ht,
      congrArg Subtype.val hrt⟩
  have hTcard : Nat.card (T.subgroupOf θ) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTθ).toEquiv
  have hT2 : IsPiSubgroup (piOf 2) T := by
    intro p hp
    rw [← hTcard] at hp
    exact hTH.p_in_pi_of_p_dvd_card p hp
  have hTQ : T ∈ scriptQ A (lB A) := mem_scriptQ_of_le_thetaCen ha hTθ hAT (lB A)
  have hTmem : T ∈ scriptQPi A (lB A) ⊤ (piOf 2) := ⟨⟨hTQ, le_top⟩, hT2⟩
  obtain ⟨S', hTS', hS'⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) hTmem
  obtain ⟨w, hw, hS'eq⟩ := h1411 G A c L h.toSec15R S hS S' hS'
  have hS'A : ⁅S', A⁆ = ⊥ := by
    rw [hS'eq]
    exact commutator_map_conj_eq_bot (Subgroup.mem_inf.mp hw).1 hSA
  have hTA : ⁅T, A⁆ = ⊥ :=
    le_bot_iff.mp (hS'A ▸ Subgroup.commutator_mono hTS' le_rfl)
  have hle : ⁅θ, A⁆ ≤ R := commutator_le_of_mul_eq hfac hAR hTA
  have hRcard : Nat.card (R.subgroupOf θ) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRθ).toEquiv
  have hR2 : ¬ 2 ∣ Nat.card R := by
    intro h2
    rw [← hRcard] at h2
    exact hRH.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h2 rfl
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  exact fun h2 => hR2 (h2.trans (Subgroup.card_dvd_of_le hle))

end CFSG.RankThree.PartTwo.Sec16
