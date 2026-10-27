module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofA6Data
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148HJ

open Equiv
open scoped commutatorElement

theorem conj_mem_of_mem_normalizer {G : Type*} [Group G] {V : Subgroup G} {c v : G}
    (hc : c ∈ Subgroup.normalizer (V : Set G)) (hv : v ∈ V) : c * v * c⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp hc v).mp hv

theorem not_isSolvable_of_le_commutator {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    (hH : H ≤ ⁅H, H⁆) (hne : H ≠ ⊥) : ¬ Group.IsSolvable K := by
  intro hK
  have hHs : Group.IsSolvable H :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hHK)
      (Subgroup.inclusion_injective hHK)
  have hHp : Group.IsPerfect H :=
    Subgroup.isPerfect_iff.mpr (le_antisymm (Subgroup.commutator_le_self H) hH)
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  exact Group.IsPerfect.not_isSolvable H hHs

theorem not_isSolvable_of_mem_commutator {K : Subgroup (Perm (Fin 6))}
    {g₁ g₂ g₃ g₄ : Perm (Fin 6)} (h₁ : g₁ ∈ K) (h₂ : g₂ ∈ K) (h₃ : g₃ ∈ K) (h₄ : g₄ ∈ K)
    (hne : g₁ ≠ 1)
    (e : ∀ g ∈ ({g₁, g₂, g₃, g₄} : Set (Perm (Fin 6))),
      g ∈ ⁅Subgroup.closure {g₁, g₂, g₃, g₄}, Subgroup.closure {g₁, g₂, g₃, g₄}⁆) :
    ¬ Group.IsSolvable K := by
  refine not_isSolvable_of_le_commutator ?_ ((Subgroup.closure_le _).mpr e) ?_
  · rw [Subgroup.closure_le]
    rintro g (rfl | rfl | rfl | rfl)
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
  · intro hbot
    apply hne
    have : g₁ ∈ Subgroup.closure {g₁, g₂, g₃, g₄} := Subgroup.subset_closure (by simp)
    rw [hbot, Subgroup.mem_bot] at this
    exact this

theorem not_isSolvable_patternA {K : Subgroup (Perm (Fin 6))} {g₁ g₂ g₃ g₄ : Perm (Fin 6)}
    (h₁ : g₁ ∈ K) (h₂ : g₂ ∈ K) (h₃ : g₃ ∈ K) (h₄ : g₄ ∈ K) (hne : g₁ ≠ 1)
    (e₁ : ⁅g₂, g₃ * g₁ * g₂ * g₄⁆ = g₁) (e₂ : ⁅g₁, g₃ * g₂ * g₃ * g₄⁆ = g₂)
    (e₃ : ⁅g₄, g₁ * g₂ * g₄ * g₁⁆ = g₃) (e₄ : ⁅g₃, g₁ * g₂ * g₃ * g₂⁆ = g₄) :
    ¬ Group.IsSolvable K := by
  refine not_isSolvable_of_mem_commutator h₁ h₂ h₃ h₄ hne ?_
  set H := Subgroup.closure ({g₁, g₂, g₃, g₄} : Set (Perm (Fin 6)))
  have m₁ : g₁ ∈ H := Subgroup.subset_closure (by simp)
  have m₂ : g₂ ∈ H := Subgroup.subset_closure (by simp)
  have m₃ : g₃ ∈ H := Subgroup.subset_closure (by simp)
  have m₄ : g₄ ∈ H := Subgroup.subset_closure (by simp)
  rintro g (rfl | rfl | rfl | rfl)
  · rw [← e₁]
    exact Subgroup.commutator_mem_commutator m₂
      (mul_mem (mul_mem (mul_mem m₃ m₁) m₂) m₄)
  · rw [← e₂]
    exact Subgroup.commutator_mem_commutator m₁
      (mul_mem (mul_mem (mul_mem m₃ m₂) m₃) m₄)
  · rw [← e₃]
    exact Subgroup.commutator_mem_commutator m₄
      (mul_mem (mul_mem (mul_mem m₁ m₂) m₄) m₁)
  · rw [← e₄]
    exact Subgroup.commutator_mem_commutator m₃
      (mul_mem (mul_mem (mul_mem m₁ m₂) m₃) m₂)

theorem not_isSolvable_patternB {K : Subgroup (Perm (Fin 6))} {g₁ g₂ g₃ g₄ : Perm (Fin 6)}
    (h₁ : g₁ ∈ K) (h₂ : g₂ ∈ K) (h₃ : g₃ ∈ K) (h₄ : g₄ ∈ K) (hne : g₁ ≠ 1)
    (e₁ : ⁅g₂, g₃ * g₂ * g₄⁆ = g₁) (e₂ : ⁅g₁, g₄ * g₂ * g₃⁆ = g₂)
    (e₃ : ⁅g₄, g₁ * g₃ * g₂⁆ = g₃) (e₄ : ⁅g₃, g₂ * g₃ * g₁⁆ = g₄) :
    ¬ Group.IsSolvable K := by
  refine not_isSolvable_of_mem_commutator h₁ h₂ h₃ h₄ hne ?_
  set H := Subgroup.closure ({g₁, g₂, g₃, g₄} : Set (Perm (Fin 6)))
  have m₁ : g₁ ∈ H := Subgroup.subset_closure (by simp)
  have m₂ : g₂ ∈ H := Subgroup.subset_closure (by simp)
  have m₃ : g₃ ∈ H := Subgroup.subset_closure (by simp)
  have m₄ : g₄ ∈ H := Subgroup.subset_closure (by simp)
  rintro g (rfl | rfl | rfl | rfl)
  · rw [← e₁]
    exact Subgroup.commutator_mem_commutator m₂ (mul_mem (mul_mem m₃ m₂) m₄)
  · rw [← e₂]
    exact Subgroup.commutator_mem_commutator m₁ (mul_mem (mul_mem m₄ m₂) m₃)
  · rw [← e₃]
    exact Subgroup.commutator_mem_commutator m₄ (mul_mem (mul_mem m₁ m₃) m₂)
  · rw [← e₄]
    exact Subgroup.commutator_mem_commutator m₃ (mul_mem (mul_mem m₂ m₃) m₁)

@[expose] def NotSolvableReps (c : Perm (Fin 6)) (r : Fin 3 → Perm (Fin 6)) : Prop :=
  ∀ k k' : Fin 3, k ≠ k' → ∀ K : Subgroup (Perm (Fin 6)), r k ∈ K → c * r k * c⁻¹ ∈ K →
    r k' ∈ K → c * r k' * c⁻¹ ∈ K → ¬ Group.IsSolvable K

theorem notSolvableReps_A : NotSolvableReps cA repA := by
  intro k k' hkk K h₁ h₂ h₃ h₄
  fin_cases k <;> fin_cases k' <;> simp only [ne_eq, not_true_eq_false] at hkk
  all_goals
    refine not_isSolvable_patternA h₁ h₂ h₃ h₄ ?_ ?_ ?_ ?_ ?_ <;> decide +kernel

theorem notSolvableReps_B : NotSolvableReps cB repB := by
  intro k k' hkk K h₁ h₂ h₃ h₄
  fin_cases k <;> fin_cases k' <;> simp only [ne_eq, not_true_eq_false] at hkk
  all_goals first
    | (refine not_isSolvable_patternB h₁ h₂ h₃ h₄ ?_ ?_ ?_ ?_ ?_ <;> decide +kernel)
    | (refine not_isSolvable_patternB h₃ h₄ h₁ h₂ ?_ ?_ ?_ ?_ ?_ <;> decide +kernel)

section Rep

variable {c : Perm (Fin 6)} {l : List (Perm (Fin 6))} {r : Fin 3 → Perm (Fin 6)}

theorem mem_list_of_mem (h : RepData c l r) {V : Subgroup (Perm (Fin 6))}
    (hVA : V ≤ alternatingGroup (Fin 6)) (hcV : c ∈ Subgroup.normalizer (V : Set (Perm (Fin 6))))
    (hV3 : ¬ 3 ∣ Nat.card V) {v : Perm (Fin 6)} (hv : v ∈ V) : v = 1 ∨ v ∈ l := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hv1, hvl⟩ := hcon
  have hsign : Perm.sign v = 1 := Perm.mem_alternatingGroup.mp (hVA hv)
  have m₁ : c * v * c⁻¹ ∈ V := conj_mem_of_mem_normalizer hcV hv
  have m₂ : c * (c * v * c⁻¹) * c⁻¹ ∈ V := conj_mem_of_mem_normalizer hcV m₁
  have key : ∀ w ∈ V, w ≠ 1 → w ^ 3 = 1 → False := fun w hw hw1 hw3 =>
    hV3 ((orderOf_eq_prime hw3 hw1) ▸ Subgroup.orderOf_dvd_natCard V hw)
  rcases h.w3 v hsign hv1 hvl with ⟨e₁, e₃⟩ | ⟨e₁, e₃⟩ | ⟨e₁, e₃⟩
  · exact key _ (mul_mem (mul_mem (mul_mem hv hv) m₁) m₂) e₁ e₃
  · exact key _ (mul_mem (mul_mem (mul_mem hv hv) m₂) m₁) e₁ e₃
  · exact key _ (mul_mem (mul_mem (mul_mem hv m₁) hv) m₂) e₁ e₃

theorem inS_of_mem (h : RepData c l r) {V : Subgroup (Perm (Fin 6))}
    (hVA : V ≤ alternatingGroup (Fin 6)) (hcV : c ∈ Subgroup.normalizer (V : Set (Perm (Fin 6))))
    (hV3 : ¬ 3 ∣ Nat.card V) {u v : Perm (Fin 6)} (hu : u ∈ V) (hu1 : u ≠ 1) (hv : v ∈ V) :
    v = 1 ∨ InS c u v := by
  rcases mem_list_of_mem h hVA hcV hV3 hv with hv1 | hvl
  · exact Or.inl hv1
  have hul : u ∈ l := (mem_list_of_mem h hVA hcV hV3 hu).resolve_left hu1
  rcases h.prod u hul v hvl with hs | ⟨h₁, h₂⟩
  · exact Or.inr hs
  · rcases mem_list_of_mem h hVA hcV hV3 (mul_mem hu hv) with h' | h'
    · exact absurd h' h₁
    · exact absurd h' h₂

theorem mem_of_inS {K : Subgroup (Perm (Fin 6))} {u v : Perm (Fin 6)} (hu : u ∈ K)
    (hcu : c * u * c⁻¹ ∈ K) (hv : InS c u v) : v ∈ K := by
  rcases hv with rfl | rfl | rfl
  · exact hu
  · exact hcu
  · exact mul_mem hu hcu

theorem le_normalizer_map_subtype {G : Type*} [Group G] {T : Subgroup G} {N : Subgroup T}
    (hN : N.Normal) : T ≤ Subgroup.normalizer ((N.map T.subtype : Subgroup G) : Set G) := by
  have hle : N.map T.subtype ≤ T := Subgroup.map_subtype_le N
  have h : ((N.map T.subtype).subgroupOf T).Normal := by
    rwa [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective T.subtype_injective]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp h

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem le_normalizer_of_rep (h : RepData c l r) (h7 : NotSolvableReps c r)
    {T U : Subgroup (Perm (Fin 6))} (hTA : T ≤ alternatingGroup (Fin 6))
    (hcT : c ∈ Subgroup.normalizer (T : Set (Perm (Fin 6)))) (hTs : Group.IsSolvable T)
    (hUT : U ≤ T) (hU3 : ¬ 3 ∣ Nat.card U)
    (hcU : c ∈ Subgroup.normalizer (U : Set (Perm (Fin 6)))) :
    T ≤ Subgroup.normalizer (U : Set (Perm (Fin 6))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hU : U = ⊥
  · subst hU
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨⟨u₀, hu₀U⟩, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  have hu₀1' : u₀ ≠ 1 := fun h1 => hu₀1 (Subtype.ext h1)
  have hUA : U ≤ alternatingGroup (Fin 6) := hUT.trans hTA
  have hu₀l : u₀ ∈ l := (mem_list_of_mem h hUA hcU hU3 hu₀U).resolve_left hu₀1'
  obtain ⟨hu₀2, -, hcu₀l, hu₀c, -⟩ := h.inv u₀ hu₀l
  have hcu₀U : c * u₀ * c⁻¹ ∈ U := conj_mem_of_mem_normalizer hcU hu₀U
  have hT360 : Nat.card T ∣ 360 := card_alternatingGroup_six ▸ Subgroup.card_dvd_of_le hTA
  have : Nontrivial T := ⟨⟨⟨u₀, hUT hu₀U⟩, 1, fun h1 => hu₀1' (congrArg Subtype.val h1)⟩⟩
  obtain ⟨M, hM⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_minimal_nontrivial_normal (G := T)
  have hMs : Group.IsSolvable M :=
    Group.isSolvable_of_isSolvable_injective (f := M.subtype) M.subtype_injective
  obtain ⟨p, hp, ⟨hMcomm, hMpow⟩, d, hd, hMcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.minimal_normal_solvable_elementary M hM hMs
  have hMn : M.Normal := hM.1.1
  have hMne : M ≠ ⊥ := hM.1.2
  have : Fact p.Prime := ⟨hp⟩
  have hMp : IsPGroup p M := IsPGroup.of_card hMcard
  have hp360 : p ∣ 360 :=
    ((hMcard ▸ dvd_pow_self p hd.ne' : p ∣ Nat.card M).trans
      (Subgroup.card_subgroup_dvd_card M)).trans hT360
  have hp235 : p = 2 ∨ p = 3 ∨ p = 5 := by
    rw [show (360 : ℕ) = 2 ^ 3 * (3 ^ 2 * 5) by norm_num] at hp360
    rcases (Nat.Prime.dvd_mul hp).mp hp360 with h2 | h35
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
    · rcases (Nat.Prime.dvd_mul hp).mp h35 with h3 | h5
      · exact Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3)))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5))
  have hchar : ∀ N : Subgroup T, N.Characteristic →
      c ∈ Subgroup.normalizer ((N.map T.subtype : Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))) :=
    fun N hN =>
      CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map T N hN hcT
  obtain ⟨⟨m, hmM⟩, hm1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hMne
  set y : Perm (Fin 6) := ((m : T) : Perm (Fin 6)) with hydef
  have hy1 : y ≠ 1 := fun h1 => hm1 (Subtype.ext (Subtype.ext h1))
  rcases hp235 with rfl | rfl | rfl
  ·
    set N := (CFSG.pCore 2 T).map T.subtype with hNdef
    have hMN : M ≤ CFSG.pCore 2 T := le_sSup ⟨hMn, hMp⟩
    have hNT : N ≤ T := Subgroup.map_subtype_le _
    have hcN : c ∈ Subgroup.normalizer (N : Set (Perm (Fin 6))) := hchar _ inferInstance
    have hN3 : ¬ 3 ∣ Nat.card N := by
      rw [hNdef, Subgroup.card_map_of_injective T.subtype_injective]
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := T))
      rw [hk]
      intro h3
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)) (by norm_num)
    have hyN : y ∈ N := ⟨m, hMN hmM, rfl⟩
    have hNA : N ≤ alternatingGroup (Fin 6) := hNT.trans hTA
    have hyl : y ∈ l := (mem_list_of_mem h hNA hcN hN3 hyN).resolve_left hy1
    have hcyN : c * y * c⁻¹ ∈ N := conj_mem_of_mem_normalizer hcN hyN
    rcases h.reps u₀ hu₀l y hyl with hS | ⟨k, k', hkk, h₁, h₂, h₃, h₄⟩
    · have hyU : y ∈ U := mem_of_inS hu₀U hcu₀U hS
      have hcyU : c * y * c⁻¹ ∈ U := conj_mem_of_mem_normalizer hcU hyU
      have hS' : InS c y u₀ := h.symm u₀ hu₀l y hyl hS
      have hu₀N : u₀ ∈ N := mem_of_inS hyN hcyN hS'
      have hcu₀N : c * u₀ * c⁻¹ ∈ N := conj_mem_of_mem_normalizer hcN hu₀N
      have hNU : N ≤ U := by
        intro x hx
        rcases inS_of_mem h hNA hcN hN3 hyN hy1 hx with rfl | hx'
        · exact one_mem U
        · exact mem_of_inS hyU hcyU hx'
      have hUN : U ≤ N := by
        intro x hx
        rcases inS_of_mem h hUA hcU hU3 hu₀U hu₀1' hx with rfl | hx'
        · exact one_mem N
        · exact mem_of_inS hu₀N hcu₀N hx'
      rw [le_antisymm hUN hNU]
      exact le_normalizer_map_subtype CFSG.pCore_normal
    · exact absurd hTs (h7 k k' hkk T (mem_of_inS (hUT hu₀U) (hUT hcu₀U) h₁)
        (mem_of_inS (hUT hu₀U) (hUT hcu₀U) h₂) (mem_of_inS (hNT hyN) (hNT hcyN) h₃)
        (mem_of_inS (hNT hyN) (hNT hcyN) h₄))
  ·
    exfalso
    set M' := M.map T.subtype with hM'def
    have hM'T : T ≤ Subgroup.normalizer (M' : Set (Perm (Fin 6))) :=
      le_normalizer_map_subtype hMn
    have hM'comm : ∀ a ∈ M', ∀ b ∈ M', a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have := hMcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg (fun z : M => ((z : T) : Perm (Fin 6))) this
    have hM'pow : ∀ a ∈ M', a ^ 3 = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      have := hMpow a ha
      simpa using congrArg Subtype.val this
    have hyM : y ∈ M' := ⟨m, hmM, rfl⟩
    have hy3 : y ^ 3 = 1 := hM'pow y hyM
    have hinv : ∀ v ∈ U, v ∈ l → v * y * v⁻¹ = y⁻¹ := by
      intro v hvU hvl
      have hv2 : v * v = 1 := (h.inv v hvl).1
      have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
      have hvy : v * y * v⁻¹ ∈ M' := conj_mem_of_mem_normalizer (hM'T (hUT hvU)) hyM
      have hc := hM'comm y hyM _ hvy
      have hz : y * (v * y * v⁻¹) ∈ M' := mul_mem hyM hvy
      have key : v * (y * (v * y * v⁻¹)) * v⁻¹ = y * (v * y * v⁻¹) := by
        calc v * (y * (v * y * v⁻¹)) * v⁻¹ = v * ((v * y * v⁻¹) * y) * v⁻¹ := by rw [hc]
          _ = (v * v) * y * v⁻¹ * y * v⁻¹ := by group
          _ = y * v⁻¹ * y * v⁻¹ := by rw [hv2, one_mul]
          _ = y * (v * y * v⁻¹) := by rw [hvi]; group
      have hvz : v * (y * (v * y * v⁻¹)) = y * (v * y * v⁻¹) * v := by
        calc v * (y * (v * y * v⁻¹)) = v * (y * (v * y * v⁻¹)) * v⁻¹ * v := by group
          _ = y * (v * y * v⁻¹) * v := by rw [key]
      by_contra hne
      have hz1 : y * (v * y * v⁻¹) ≠ 1 := fun h1 => hne (eq_inv_of_mul_eq_one_right h1)
      exact h.three _ hz1 (hM'pow _ hz) v hvl hvz
    have hv₃l : u₀ * (c * u₀ * c⁻¹) ∈ l := hu₀c ▸ (h.inv _ hcu₀l).2.2.1
    have e₁ := hinv u₀ hu₀U hu₀l
    have e₂ := hinv _ hcu₀U hcu₀l
    have e₃ := hinv _ (mul_mem hu₀U hcu₀U) hv₃l
    have hyy : y⁻¹ = y := by
      calc y⁻¹ = (u₀ * (c * u₀ * c⁻¹)) * y * (u₀ * (c * u₀ * c⁻¹))⁻¹ := e₃.symm
        _ = u₀ * ((c * u₀ * c⁻¹) * y * (c * u₀ * c⁻¹)⁻¹) * u₀⁻¹ := by group
        _ = u₀ * y⁻¹ * u₀⁻¹ := by rw [e₂]
        _ = (u₀ * y * u₀⁻¹)⁻¹ := by group
        _ = y := by rw [e₁, inv_inv]
    have hy2 : y * y = 1 := by
      calc y * y = y * y⁻¹ := by rw [hyy]
        _ = 1 := mul_inv_cancel y
    apply hy1
    calc y = y ^ 3 * (y * y)⁻¹ := by group
      _ = 1 := by rw [hy3, hy2, inv_one, one_mul]
  ·
    exfalso
    set N := (CFSG.pCore 5 T).map T.subtype with hNdef
    have hMN : M ≤ CFSG.pCore 5 T := le_sSup ⟨hMn, hMp⟩
    have hcN : c ∈ Subgroup.normalizer (N : Set (Perm (Fin 6))) := hchar _ inferInstance
    have hyN : y ∈ N := ⟨m, hMN hmM, rfl⟩
    have hNcard : Nat.card N = 5 := by
      rw [hNdef, Subgroup.card_map_of_injective T.subtype_injective]
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 5) (G := T))
      have hdvd : Nat.card (CFSG.pCore 5 T) ∣ 360 :=
        (Subgroup.card_subgroup_dvd_card _).trans hT360
      rw [hk] at hdvd ⊢
      have hk2 : k ≤ 1 := by
        by_contra hk2
        have : 5 ^ 2 ∣ 360 := (pow_dvd_pow 5 (by omega)).trans hdvd
        norm_num at this
      have hk0 : k ≠ 0 := by
        rintro rfl
        have h1 : Nat.card N = 1 := by
          rw [hNdef, Subgroup.card_map_of_injective T.subtype_injective, hk, pow_zero]
        have := Subgroup.eq_bot_of_card_eq N h1
        rw [this] at hyN
        exact hy1 hyN
      interval_cases k
      · exact absurd rfl hk0
      · rfl
    have hy5 : orderOf y = 5 := by
      have hdvd : orderOf y ∣ 5 := hNcard ▸ Subgroup.orderOf_dvd_natCard N hyN
      rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
      · exact absurd (orderOf_eq_one_iff.mp h1) hy1
      · exact h5
    have hNy : N = Subgroup.zpowers y :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyN)
        (by rw [Nat.card_zpowers, hy5, hNcard])).symm
    have hcy : c * y * c⁻¹ ∈ Subgroup.zpowers y := hNy ▸ conj_mem_of_mem_normalizer hcN hyN
    rw [mem_zpowers_iff_mem_range_orderOf, hy5] at hcy
    obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hcy
    obtain ⟨f₁, f₂, f₃, f₄⟩ := h.five y hy1 (by rw [← hy5]; exact pow_orderOf_eq_one y)
    have hi5 : i < 5 := Finset.mem_range.mp hi
    interval_cases i
    · apply hy1
      have : y = c⁻¹ * (c * y * c⁻¹) * c := by group
      rw [this, ← hiy, pow_zero, mul_one, inv_mul_cancel]
    · exact f₁ (by rw [← hiy, pow_one])
    · exact f₂ hiy.symm
    · exact f₃ hiy.symm
    · exact f₄ hiy.symm

end Rep

theorem cycleType_cA : cA.cycleType = Multiset.replicate 1 3 := by
  rw [Multiset.replicate_one]
  exact card_support_eq_three_iff.mp (by decide)

theorem cycleType_cB : cB.cycleType = Multiset.replicate 2 3 := by
  have hd : (swap 0 1 * swap 1 2 : Perm (Fin 6)).Disjoint (swap 3 4 * swap 4 5) := fun i => by
    fin_cases i <;> decide
  have h₁ : (swap 0 1 * swap 1 2 : Perm (Fin 6)).cycleType = {3} :=
    card_support_eq_three_iff.mp (by decide)
  have h₂ : (swap 3 4 * swap 4 5 : Perm (Fin 6)).cycleType = {3} :=
    card_support_eq_three_iff.mp (by decide)
  rw [cB, hd.cycleType_mul, h₁, h₂]
  rfl

theorem exists_conj_eq_rep {x : Perm (Fin 6)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ σ : Perm (Fin 6), σ * x * σ⁻¹ = cA ∨ σ * x * σ⁻¹ = cB := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (hord ▸ Nat.prime_three)
  rw [hord] at hn
  have hsum := Perm.sum_cycleType_le x
  rw [hn, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hn1 : n = 0 ∨ n = 1 := by omega
  rcases hn1 with rfl | rfl
  · obtain ⟨σ, hσ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr (hn.trans cycleType_cA.symm))
    exact ⟨σ, Or.inl hσ⟩
  · obtain ⟨σ, hσ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr (hn.trans cycleType_cB.symm))
    exact ⟨σ, Or.inr hσ⟩

theorem le_normalizer_of_isSolvable {x : Perm (Fin 6)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {T U : Subgroup (Perm (Fin 6))} (hTA : T ≤ alternatingGroup (Fin 6))
    (hxT : x ∈ Subgroup.normalizer (T : Set (Perm (Fin 6)))) (hTs : Group.IsSolvable T)
    (hUT : U ≤ T) (hU3 : ¬ 3 ∣ Nat.card U)
    (hxU : x ∈ Subgroup.normalizer (U : Set (Perm (Fin 6)))) :
    T ≤ Subgroup.normalizer (U : Set (Perm (Fin 6))) := by
  obtain ⟨σ, hσ⟩ := exists_conj_eq_rep hx3 hx1
  set φ : Perm (Fin 6) ≃* Perm (Fin 6) := MulAut.conj σ with hφ
  have hφx : φ x = σ * x * σ⁻¹ := MulAut.conj_apply σ x
  have hTA' : T.map φ.toMonoidHom ≤ alternatingGroup (Fin 6) := by
    rintro _ ⟨t, ht, rfl⟩
    have hs := Perm.mem_alternatingGroup.mp (hTA ht)
    rw [Perm.mem_alternatingGroup]
    change Perm.sign (σ * t * σ⁻¹) = 1
    rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hs, mul_one, Int.units_mul_self]
  have hxT' : φ x ∈ Subgroup.normalizer ((T.map φ.toMonoidHom : Subgroup _) : Set _) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hxT
  have hTs' : Group.IsSolvable (T.map φ.toMonoidHom) :=
    Group.isSolvable_of_surjective
      (f := (T.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom) (MulEquiv.surjective _)
  have hUT' : U.map φ.toMonoidHom ≤ T.map φ.toMonoidHom := Subgroup.map_mono hUT
  have hU3' : ¬ 3 ∣ Nat.card (U.map φ.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective φ.injective]
  have hxU' : φ x ∈ Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup _) : Set _) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hxU
  have key : T.map φ.toMonoidHom ≤
      Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup _) : Set (Perm (Fin 6))) := by
    rw [hφx] at hxT' hxU'
    rcases hσ with hσ | hσ
    · rw [hσ] at hxT' hxU'
      exact le_normalizer_of_rep repData_A notSolvableReps_A hTA' hxT' hTs' hUT' hU3' hxU'
    · rw [hσ] at hxT' hxU'
      exact le_normalizer_of_rep repData_B notSolvableReps_B hTA' hxT' hTs' hUT' hU3' hxU'
  rwa [← Subgroup.map_equiv_normalizer_eq, Subgroup.map_le_map_iff_of_injective φ.injective]
    at key

end CFSG.RankThree.PartTwo.Sec14.Item148HJ
