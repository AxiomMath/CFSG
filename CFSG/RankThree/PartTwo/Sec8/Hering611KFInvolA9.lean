module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFS6
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofA9
public import CFSG.RankThree.PartTwo.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Equiv

def a9S : Perm (Fin 9) := swap 0 1 * swap 1 2

def a9T : Perm (Fin 9) := swap 0 1 * swap 3 4

def a9V1 : Perm (Fin 9) := swap 5 6 * swap 7 8

def a9V2 : Perm (Fin 9) := swap 5 7 * swap 6 8

def a9H : Perm (Fin 9) := swap 5 7 * swap 7 6

def a9X : Perm (Fin 9) := swap 3 5 * swap 5 6

theorem a9T_mem : a9T ∈ alternatingGroup (Fin 9) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem a9V1_mem : a9V1 ∈ alternatingGroup (Fin 9) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem a9V2_mem : a9V2 ∈ alternatingGroup (Fin 9) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem a9H_mem : a9H ∈ alternatingGroup (Fin 9) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem a9X_mem : a9X ∈ alternatingGroup (Fin 9) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem a9_relations :
    a9S ^ 3 = 1 ∧ a9S ≠ 1 ∧ a9T * a9T = 1 ∧ a9T * a9S * a9T⁻¹ = a9S⁻¹ ∧
      a9V1 ≠ 1 ∧ a9V2 ≠ 1 ∧ a9V1 ≠ a9V2 ∧ a9V1 * a9V1 = 1 ∧ a9V2 * a9V2 = 1 ∧
      a9V1 * a9V2 = a9V2 * a9V1 ∧ a9H * a9V1 * a9H⁻¹ = a9V2 ∧
      a9H * a9V2 * a9H⁻¹ = a9V1 * a9V2 ∧ a9T * a9V1 * a9T⁻¹ = a9V1 ∧
      a9T * a9V2 * a9T⁻¹ = a9V2 ∧ a9T * a9H * a9T⁻¹ = a9H ∧ a9T * a9X * a9T⁻¹ ≠ a9X := by
  unfold a9S a9T a9V1 a9V2 a9H a9X
  decide

theorem a9V1_fix : a9V1 0 = 0 ∧ a9V1 1 = 1 ∧ a9V1 2 = 2 := by
  unfold a9V1
  decide

theorem a9V2_fix : a9V2 0 = 0 ∧ a9V2 1 = 1 ∧ a9V2 2 = 2 := by
  unfold a9V2
  decide

theorem a9H_fix : a9H 0 = 0 ∧ a9H 1 = 1 ∧ a9H 2 = 2 := by
  unfold a9H
  decide

theorem a9X_fix : a9X 0 = 0 ∧ a9X 1 = 1 ∧ a9X 2 = 2 := by
  unfold a9X
  decide

theorem a9T_perm012 : a9T 0 = 1 ∧ a9T 1 = 0 ∧ a9T 2 = 2 := by
  unfold a9T
  decide

theorem a9S_support : ∀ x : Fin 9, x ∈ a9S.support ↔ x = 0 ∨ x = 1 ∨ x = 2 := by
  unfold a9S
  decide

theorem a9S_isThreeCycle : a9S.IsThreeCycle := by
  unfold a9S
  rw [← card_support_eq_three_iff]
  decide

def stab012 : Subgroup (Perm (Fin 9)) where
  carrier := {g | g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2}
  mul_mem' := by
    rintro a b ⟨ha0, ha1, ha2⟩ ⟨hb0, hb1, hb2⟩
    exact ⟨by simp [Perm.mul_apply, ha0, hb0], by simp [Perm.mul_apply, ha1, hb1],
      by simp [Perm.mul_apply, ha2, hb2]⟩
  one_mem' := ⟨rfl, rfl, rfl⟩
  inv_mem' := by
    rintro a ⟨ha0, ha1, ha2⟩
    exact ⟨Perm.inv_eq_iff_eq.mpr ha0.symm, Perm.inv_eq_iff_eq.mpr ha1.symm,
      Perm.inv_eq_iff_eq.mpr ha2.symm⟩

theorem mem_stab012 {g : Perm (Fin 9)} : g ∈ stab012 ↔ g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2 := Iff.rfl

theorem std_case {Kb : Type} [Group Kb] [Finite Kb] (e : Kb ≃* alternatingGroup (Fin 9)) {γ : Kb}
    (hγ : (e γ : Perm (Fin 9)) = a9S) {P : Subgroup Kb} (hPperf : Group.IsPerfect P)
    (hPC : P ≤ Subgroup.centralizer ({γ} : Set Kb))
    (hq : Nat.card (P ⧸ aschbacherSolvableCore 3 P) = 360) :
    ∃ t : Kb, t ^ 2 = 1 ∧ t * γ * t⁻¹ = γ⁻¹ ∧ S6Act P t := by
  classical
  obtain ⟨hS3, hS1, hTT, hTS, hV1, hV2, hV12, hV1sq, hV2sq, hVc, hH1, hH2, hT1, hT2, hTH, hTX⟩ :=
    a9_relations
  set ι : Kb →* Perm (Fin 9) := (alternatingGroup (Fin 9)).subtype.comp e.toMonoidHom with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιγ : ι γ = a9S := hγ
  have hιalt : ∀ x, ι x ∈ alternatingGroup (Fin 9) := fun x => (e x).2
  set Pp : Subgroup (Perm (Fin 9)) := P.map ι with hPp
  have hPpP : Nat.card Pp = Nat.card P := Subgroup.card_map_of_injective hιinj
  have hPpperf : Group.IsPerfect Pp :=
    Group.IsPerfect.ofSurjective (f := (P.equivMapOfInjective ι hιinj).toMonoidHom)
      (MulEquiv.surjective _)
  have hPpC : Pp ≤ Subgroup.centralizer ({a9S} : Set (Perm (Fin 9))) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hιγ, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hPC hx)]
  have hfix := Item8KFacts3.fixes_support_of_isPerfect (by simp) hS3 hPpperf hPpC
  set T : Subgroup (Perm (Fin 9)) := alternatingGroup (Fin 9) ⊓ stab012 with hT
  have hPpT : Pp ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hιalt x, ?_⟩
    have h0 := hfix (ι x) ⟨x, hx, rfl⟩
    exact ⟨h0 0 ((a9S_support 0).mpr (Or.inl rfl)),
      h0 1 ((a9S_support 1).mpr (Or.inr (Or.inl rfl))),
      h0 2 ((a9S_support 2).mpr (Or.inr (Or.inr rfl)))⟩
  have h360 : 360 ∣ Nat.card P := hq ▸ Subgroup.card_quotient_dvd_card _
  have hW : Nat.card stab012 ∣ 720 := by
    have hF : ({3, 4, 5, 6, 7, 8} : Finset (Fin 9)).card.factorial = 720 := by decide
    have := Item8KFacts3.card_dvd_factorial_of_fixes (T := stab012)
      ({3, 4, 5, 6, 7, 8} : Finset (Fin 9)) (by
        intro g hg x hx
        have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by
          revert x
          decide
        rcases hx' with rfl | rfl | rfl
        · exact hg.1
        · exact hg.2.1
        · exact hg.2.2)
    rwa [hF] at this
  have hswap : Equiv.swap (3 : Fin 9) 4 ∈ stab012 ∧
      Equiv.swap (3 : Fin 9) 4 ∉ alternatingGroup (Fin 9) := by
    refine ⟨mem_stab012.mpr (by decide), ?_⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have hTlt : Nat.card T < Nat.card stab012 := by
    by_contra hle
    have hTle : T ≤ stab012 := inf_le_right
    have heq : T = stab012 := Subgroup.eq_of_le_of_card_ge hTle (not_lt.mp hle)
    have h2 : Equiv.swap (3 : Fin 9) 4 ∈ T := by rw [heq]; exact hswap.1
    exact hswap.2 h2.1
  have hWle : Nat.card stab012 ≤ 720 := Nat.le_of_dvd (by norm_num) hW
  have hPpdvd : Nat.card Pp ∣ Nat.card T := Subgroup.card_dvd_of_le hPpT
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hT360 : Nat.card T = 360 := by
    have h1 : 360 ∣ Nat.card T := (hPpP ▸ h360).trans hPpdvd
    obtain ⟨k, hk⟩ := h1
    omega
  have hPp360 : Nat.card Pp = 360 := by
    have h1 : 360 ∣ Nat.card Pp := hPpP ▸ h360
    exact Nat.dvd_antisymm (hT360 ▸ hPpdvd) h1
  have hPpeq : Pp = T := Subgroup.eq_of_le_of_card_ge hPpT (by rw [hT360, hPp360])
  have hPcard : Nat.card P = 360 := by rw [← hPpP, hPp360]
  have memP : ∀ x : Kb, x ∈ P ↔ ι x ∈ T := by
    intro x
    constructor
    · intro hx
      rw [← hPpeq]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hPpeq] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [← hιinj hyx]
      exact hy
  have hlift : ∀ w ∈ alternatingGroup (Fin 9), ∃ x : Kb, ι x = w := fun w hw =>
    ⟨e.symm ⟨w, hw⟩, by simp [hι]⟩
  obtain ⟨t, ht⟩ := hlift a9T a9T_mem
  obtain ⟨v₁, hv1⟩ := hlift a9V1 a9V1_mem
  obtain ⟨v₂, hv2⟩ := hlift a9V2 a9V2_mem
  obtain ⟨h, hh⟩ := hlift a9H a9H_mem
  obtain ⟨x, hx⟩ := hlift a9X a9X_mem
  have hmemT : ∀ {w : Perm (Fin 9)}, w ∈ alternatingGroup (Fin 9) →
      w 0 = 0 ∧ w 1 = 1 ∧ w 2 = 2 → w ∈ T := fun hA hW => ⟨hA, mem_stab012.mpr hW⟩
  have hinvT : a9T⁻¹ = a9T := inv_eq_of_mul_eq_one_right hTT
  have hTnorm : ∀ g ∈ T, a9T * g * a9T⁻¹ ∈ T := by
    rintro g ⟨hgA, hgW⟩
    obtain ⟨hg0, hg1, hg2⟩ := mem_stab012.mp hgW
    obtain ⟨hT0, hT1, hT2⟩ := a9T_perm012
    refine hmemT ((inferInstance : (alternatingGroup (Fin 9)).Normal).conj_mem g hgA a9T) ?_
    rw [hinvT]
    refine ⟨?_, ?_, ?_⟩
    · simp [Perm.mul_apply, hT0, hT1, hg1, hg0]
    · simp [Perm.mul_apply, hT0, hT1, hg1, hg0]
    · simp [Perm.mul_apply, hT2, hg2]
  refine ⟨t, hιinj (by rw [map_pow, ht, map_one, pow_two]; exact hTT),
    hιinj (by rw [map_mul, map_mul, map_inv, map_inv, ht, hιγ]; exact hTS), ?_, ?_, ?_, ?_⟩
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [memP] at hy ⊢
      rw [map_mul, map_mul, map_inv, ht]
      exact hTnorm _ hy
    · intro hy
      rw [memP] at hy ⊢
      rw [map_mul, map_mul, map_inv, ht] at hy
      have := hTnorm _ hy
      rw [hinvT] at this
      have e1 : a9T * (a9T * ι y * a9T) * a9T = ι y := by
        calc a9T * (a9T * ι y * a9T) * a9T = (a9T * a9T) * ι y * (a9T * a9T) := by group
          _ = ι y := by rw [hTT]; group
      rwa [e1] at this
  ·
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 P)
    rw [hPcard, hq] at h1
    have h2 : Nat.card (aschbacherSolvableCore 3 P) = 1 := by omega
    exact Subgroup.eq_bot_of_card_eq _ h2
  ·
    refine ⟨v₁, v₂, h, (memP v₁).mpr (by rw [hv1]; exact hmemT a9V1_mem a9V1_fix),
      (memP v₂).mpr (by rw [hv2]; exact hmemT a9V2_mem a9V2_fix),
      (memP h).mpr (by rw [hh]; exact hmemT a9H_mem a9H_fix), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · intro h1; apply hV1; rw [← hv1, h1, map_one]
    · intro h1; apply hV2; rw [← hv2, h1, map_one]
    · intro h1; apply hV12; rw [← hv1, ← hv2, h1]
    · exact hιinj (by rw [map_mul, map_one, hv1]; exact hV1sq)
    · exact hιinj (by rw [map_mul, map_one, hv2]; exact hV2sq)
    · exact hιinj (by rw [map_mul, map_mul, hv1, hv2]; exact hVc)
    · exact hιinj (by rw [map_mul, map_mul, map_inv, hh, hv1, hv2]; exact hH1)
    · exact hιinj (by rw [map_mul, map_mul, map_inv, map_mul, hh, hv1, hv2]; exact hH2)
    · exact hιinj (by rw [map_mul, map_mul, map_inv, ht, hv1]; exact hT1)
    · exact hιinj (by rw [map_mul, map_mul, map_inv, ht, hv2]; exact hT2)
    · exact hιinj (by rw [map_mul, map_mul, map_inv, ht, hh]; exact hTH)
  ·
    refine ⟨x, (memP x).mpr (by rw [hx]; exact hmemT a9X_mem a9X_fix), fun h1 => hTX ?_⟩
    have := congrArg ι h1
    rwa [map_mul, map_mul, map_inv, ht, hx] at this

theorem isThreeCycle_of_perfect {Kb : Type} [Group Kb] [Finite Kb]
    (e : Kb ≃* alternatingGroup (Fin 9)) {γ : Kb} (hγ3 : γ ^ 3 = 1) (hγ1 : γ ≠ 1)
    {P : Subgroup Kb} (hPperf : Group.IsPerfect P)
    (hPC : P ≤ Subgroup.centralizer ({γ} : Set Kb)) (h5 : 5 ∣ Nat.card P) :
    (e γ : Perm (Fin 9)).IsThreeCycle := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ι : Kb →* Perm (Fin 9) := (alternatingGroup (Fin 9)).subtype.comp e.toMonoidHom with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hσ3 : (ι γ) ^ 3 = 1 := by rw [← map_pow, hγ3, map_one]
  have hσ1 : ι γ ≠ 1 := fun h => hγ1 (hιinj (h.trans (map_one ι).symm))
  set Pp : Subgroup (Perm (Fin 9)) := P.map ι with hPp
  have hPpP : Nat.card Pp = Nat.card P := Subgroup.card_map_of_injective hιinj
  have hPpperf : Group.IsPerfect Pp :=
    Group.IsPerfect.ofSurjective (f := (P.equivMapOfInjective ι hιinj).toMonoidHom)
      (MulEquiv.surjective _)
  have hPpC : Pp ≤ Subgroup.centralizer ({ι γ} : Set (Perm (Fin 9))) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hPC hx)]
  have hfix := Item8KFacts3.fixes_support_of_isPerfect (by simp) hσ3 hPpperf hPpC
  have hdvd : Nat.card Pp ∣ ((ι γ).support)ᶜ.card.factorial :=
    Item8KFacts3.card_dvd_factorial_of_fixes (T := Pp) ((ι γ).support)ᶜ
      (fun t ht x hx => hfix t ht x (by simpa using hx))
  have h5' : 5 ∣ ((ι γ).support)ᶜ.card.factorial := (hPpP ▸ h5).trans hdvd
  have h5le : 5 ≤ ((ι γ).support)ᶜ.card :=
    (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 5)).mp h5'
  rw [Finset.card_compl, Fintype.card_fin] at h5le
  have hord : orderOf (ι γ) = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := ι γ) (by rw [hord]; norm_num)
  have hsum := Equiv.Perm.sum_cycleType (ι γ)
  rw [hn, hord, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hn0 : n = 0 := by omega
  rw [hn0, hord] at hn
  exact hn

theorem exists_inverting_s6act {Kb : Type} [Group Kb] [Finite Kb]
    (e : Kb ≃* alternatingGroup (Fin 9)) {γ : Kb} (hγ3 : γ ^ 3 = 1) (hγ1 : γ ≠ 1)
    {P : Subgroup Kb} (hP : P ∈ thetaComponentsIn (Subgroup.centralizer ({γ} : Set Kb)))
    (hq : Nat.card (P ⧸ aschbacherSolvableCore 3 P) = 360) :
    ∃ t : Kb, t ^ 2 = 1 ∧ t * γ * t⁻¹ = γ⁻¹ ∧ S6Act P t := by
  classical
  have hPperf := isPerfect_of_mem_thetaComponentsIn hP
  have hPC := le_of_mem_thetaComponentsIn hP
  have h5 : 5 ∣ Nat.card P :=
    ((by norm_num : 5 ∣ 360).trans (hq ▸ Subgroup.card_quotient_dvd_card _))
  have h3c := isThreeCycle_of_perfect e hγ3 hγ1 hPperf hPC h5
  have hconj : IsConj (e γ : Perm (Fin 9)) a9S :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (h3c.cycleType.trans a9S_isThreeCycle.cycleType.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  set e' : Kb ≃* alternatingGroup (Fin 9) := e.trans (MulAut.conjNormal g) with he'
  have he'γ : (e' γ : Perm (Fin 9)) = a9S := by
    rw [he']
    change g * (e γ : Perm (Fin 9)) * g⁻¹ = a9S
    exact hg
  exact std_case e' he'γ hPperf hPC hq

end CFSG.RankThree.PartTwo.Sec8.Hering611
