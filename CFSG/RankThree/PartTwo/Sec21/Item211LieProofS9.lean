module

public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Assembly (IsElemAbelian)

namespace Item211LieProof

@[expose] def maxPartProd : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 6
  | 6 => 9
  | 7 => 12
  | 8 => 18
  | _ => 27

theorem maxPartProd_step : ∀ n < 10, ∀ k < 10, 1 ≤ k → k ≤ n →
    k * maxPartProd (n - k) ≤ maxPartProd n := by
  decide

theorem card_le_maxPartProd {Ω : Type*} [Finite Ω] :
    ∀ n : ℕ, n ≤ 9 → ∀ A : Subgroup (Equiv.Perm Ω), IsMulCommutative A → ∀ S : Set Ω,
      S.ncard = n → (∀ a ∈ A, ∀ x ∉ S, a x = x) → Nat.card A ≤ maxPartProd n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn A hA S hSn hfix
  rcases S.eq_empty_or_nonempty with hS | ⟨x, hx⟩
  · have hbot : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro a ha
      ext y
      exact congrArg id (hfix a ha y (by rw [hS]; exact Set.notMem_empty y))
    have hn0 : n = 0 := by rw [← hSn, hS, Set.ncard_empty]
    rw [hbot, Subgroup.card_bot, hn0]
    decide
  · set O : Set Ω := MulAction.orbit A x with hO
    have hOS : O ⊆ S := by
      rintro _ ⟨b, rfl⟩
      by_contra hy
      change (b : Equiv.Perm Ω) x ∉ S at hy
      have h1 := hfix ((b : Equiv.Perm Ω)⁻¹) (A.inv_mem b.2) _ hy
      rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply] at h1
      rw [← h1] at hy
      exact hy hx
    have hxO : x ∈ O := MulAction.mem_orbit_self x
    set A' : Subgroup (Equiv.Perm Ω) := (MulAction.stabilizer A x).map A.subtype with hA'
    have hA'le : A' ≤ A := Subgroup.map_subtype_le _
    have hA'comm : IsMulCommutative A' := by
      rw [← Subgroup.le_centralizer_iff_isMulCommutative]
      exact hA'le.trans ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hA).trans
        (Subgroup.centralizer_le hA'le))
    have hA'fix : ∀ a ∈ A', ∀ y ∉ S \ O, a y = y := by
      rintro _ ⟨s, hs, rfl⟩ y hy
      rw [Set.mem_sdiff, not_and, not_not] at hy
      by_cases hyS : y ∈ S
      · obtain ⟨b, rfl⟩ := hy hyS
        have hsx : (s : Equiv.Perm Ω) x = x := hs
        have hcomm : (s : Equiv.Perm Ω) * (b : Equiv.Perm Ω) = (b : Equiv.Perm Ω) * s :=
          congrArg Subtype.val (hA.is_comm.comm s b)
        change (s : Equiv.Perm Ω) ((b : Equiv.Perm Ω) x) = (b : Equiv.Perm Ω) x
        rw [← Equiv.Perm.mul_apply, hcomm, Equiv.Perm.mul_apply, hsx]
      · exact hfix _ s.2 y hyS
    have hcard : Nat.card A = O.ncard * Nat.card A' := by
      rw [Subgroup.card_map_of_injective A.subtype_injective, ← Nat.card_coe_set_eq,
        ← Nat.card_prod]
      exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A x)).symm
    have hOpos : 1 ≤ O.ncard := (Set.ncard_pos).mpr ⟨x, hxO⟩
    have hOle : O.ncard ≤ n := hSn ▸ Set.ncard_le_ncard hOS
    have hdiff : (S \ O).ncard = n - O.ncard := by rw [Set.ncard_sdiff hOS, hSn]
    have hrec := ih (n - O.ncard) (by omega) (by omega) A' hA'comm (S \ O) hdiff hA'fix
    calc Nat.card A = O.ncard * Nat.card A' := hcard
      _ ≤ O.ncard * maxPartProd (n - O.ncard) := Nat.mul_le_mul_left _ hrec
      _ ≤ maxPartProd n := maxPartProd_step n (by omega) _ (by omega) hOpos hOle

theorem card_le_twentySeven (A : Subgroup (Equiv.Perm (Fin 9))) (hA : IsMulCommutative A) :
    Nat.card A ≤ 27 :=
  card_le_maxPartProd 9 le_rfl A hA Set.univ (by rw [Set.ncard_univ, Nat.card_fin])
    fun _ _ x hx => absurd (Set.mem_univ x) hx

end Item211LieProof

open Item211LieProof

theorem ks211S9CentE9 :
    ∀ D T : Subgroup (Equiv.Perm (Fin 9)), IsElemAbelian 3 D → Nat.card D = 9 → IsPGroup 2 T →
      T ≤ Subgroup.centralizer (D : Set (Equiv.Perm (Fin 9))) → Nat.card T ≤ 2 := by
  intro D T hD hD9 hT hTD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  obtain ⟨m, hm⟩ := hT.exists_card_eq
  have h4 : 2 ^ 2 ∣ Nat.card T := by
    rw [hm]
    refine pow_dvd_pow 2 ?_
    by_contra hm2
    interval_cases m <;> simp_all
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
  set T₀ : Subgroup (Equiv.Perm (Fin 9)) := H.map T.subtype with hT₀
  have hT₀4 : Nat.card T₀ = 2 ^ 2 := by
    rw [hT₀, Subgroup.card_map_of_injective T.subtype_injective, hH]
  have hT₀T : T₀ ≤ T := Subgroup.map_subtype_le _
  have hT₀comm : IsMulCommutative T₀ := IsPGroup.isMulCommutative_of_card_eq_prime_sq hT₀4
  have hT₀D : T₀ ≤ Subgroup.centralizer (D : Set (Equiv.Perm (Fin 9))) := hT₀T.trans hTD
  have hDT₀ : D ≤ Subgroup.centralizer (T₀ : Set (Equiv.Perm (Fin 9))) :=
    Subgroup.le_centralizer_iff.mp hT₀D
  have hAcomm : IsMulCommutative (T₀ ⊔ D : Subgroup (Equiv.Perm (Fin 9))) := by
    rw [← Subgroup.le_centralizer_iff_isMulCommutative]
    refine sup_le (Subgroup.le_centralizer_iff.mpr (sup_le ?_ hDT₀))
      (Subgroup.le_centralizer_iff.mpr (sup_le hT₀D ?_))
    · exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hT₀comm
    · exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hD.1
  have hle := card_le_twentySeven _ hAcomm
  have h4A : 4 ∣ Nat.card (T₀ ⊔ D : Subgroup (Equiv.Perm (Fin 9))) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : T₀ ≤ T₀ ⊔ D)
    rwa [hT₀4] at this
  have h9A : 9 ∣ Nat.card (T₀ ⊔ D : Subgroup (Equiv.Perm (Fin 9))) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : D ≤ T₀ ⊔ D)
    rwa [hD9] at this
  have h36 : 4 * 9 ∣ Nat.card (T₀ ⊔ D : Subgroup (Equiv.Perm (Fin 9))) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4A h9A
  have h36' := Nat.le_of_dvd Nat.card_pos h36
  omega

end CFSG.RankThree.PartTwo.Sec21
