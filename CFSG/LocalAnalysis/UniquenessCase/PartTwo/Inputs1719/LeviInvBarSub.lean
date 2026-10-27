module

public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LeviInvCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G] {P : Subgroup G}

abbrev barSub (P X : Subgroup G) : Subgroup (Bar2 P) :=
  (X.subgroupOf P).map (QuotientGroup.mk' (CFSG.pCore 2 ↥P))

theorem map_oUpperTwo' {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B)
    (X : Subgroup A) : (S17.oUpperTwo X).map f = S17.oUpperTwo (X.map f) := by
  rw [S17.oUpperTwo_eq_closure, S17.oUpperTwo_eq_closure, MonoidHom.map_closure]
  apply le_antisymm
  · refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hx, ho⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f hx, ho.of_dvd_nat (orderOf_map_dvd f x)⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨x, hx, rfl⟩, ho⟩
    obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hcop : (2 ^ a).Coprime (orderOf (f x)) :=
      Nat.Coprime.pow_left a (Odd.coprime_two_right ho).symm
    obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
    have h1 : orderOf (x ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (by positivity) (hxm ▸ dvd_mul_right _ _), hxm,
        Nat.mul_div_cancel_left m (by positivity)]
    refine Subgroup.subset_closure ⟨(x ^ 2 ^ a) ^ c, ⟨X.pow_mem (X.pow_mem hx _) _, ?_⟩, ?_⟩
    · exact (h1 ▸ hm).of_dvd_nat (orderOf_pow_dvd c)
    · rw [map_pow, map_pow, hc]

theorem map_opp' {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B) (X : Subgroup A) :
    (Opp 2 X).map f = Opp 2 (X.map f) := by
  rw [Opp, Opp, CFSG.RankThree.PartOne.pElementSubgroup, CFSG.RankThree.PartOne.pElementSubgroup,
    MonoidHom.map_closure]
  apply le_antisymm
  · refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hx, k, hk⟩, rfl⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hk ▸ orderOf_map_dvd f x)
    exact ⟨Subgroup.mem_map_of_mem f hx, j, hj⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨x, hx, rfl⟩, k, hk⟩
    obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hcop : m.Coprime (orderOf (f x)) := by
      rw [hk]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm)
    obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
    have h1 : orderOf (x ^ m) = 2 ^ a := by
      rw [orderOf_pow_of_dvd (by rintro rfl; simp at hm) (hxm ▸ dvd_mul_left _ _), hxm,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hm))]
    refine Subgroup.subset_closure ⟨(x ^ m) ^ c, ⟨X.pow_mem (X.pow_mem hx _) _, ?_⟩, ?_⟩
    · obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (h1 ▸ orderOf_pow_dvd c)
      exact ⟨j, hj⟩
    · rw [map_pow, map_pow, hc]

omit [Finite G] in
theorem subgroupOf_pCoreOf : (pCoreOf 2 P).subgroupOf P = CFSG.pCore 2 ↥P :=
  CFSG.openPCoreOf_subgroupOf 2 P

omit [Finite G] in
theorem subgroupOf_sup_of_le {X Y : Subgroup G} (hX : X ≤ P) (hY : Y ≤ P) :
    (X ⊔ Y).subgroupOf P = X.subgroupOf P ⊔ Y.subgroupOf P :=
  Subgroup.subgroupOf_sup hX hY

omit [Finite G] in
theorem map_subtype_subgroupOf {X : Subgroup G} (hX : X ≤ P) :
    (X.subgroupOf P).map P.subtype = X := by
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hX]

omit [Finite G] in
theorem subgroupOf_inj {X Y : Subgroup G} (hX : X ≤ P) (hY : Y ≤ P)
    (h : X.subgroupOf P = Y.subgroupOf P) : X = Y := by
  rw [← map_subtype_subgroupOf hX, ← map_subtype_subgroupOf hY, h]

omit [Finite G] in
theorem subgroupOf_commutator {X Y : Subgroup G} (hX : X ≤ P) (hY : Y ≤ P) :
    ⁅X, Y⁆.subgroupOf P = ⁅X.subgroupOf P, Y.subgroupOf P⁆ := by
  apply Subgroup.map_injective P.subtype_injective
  rw [Subgroup.map_commutator, map_subtype_subgroupOf hX, map_subtype_subgroupOf hY,
    map_subtype_subgroupOf ((Subgroup.commutator_mono hX hY).trans (Subgroup.commutator_le_self P))]

omit [Finite G] in
theorem subgroupOf_iSup {ι : Type*} {X : ι → Subgroup G} (hX : ∀ i, X i ≤ P) :
    (⨆ i, X i).subgroupOf P = ⨆ i, (X i).subgroupOf P := by
  apply Subgroup.map_injective P.subtype_injective
  rw [Subgroup.map_iSup, map_subtype_subgroupOf (iSup_le hX)]
  exact iSup_congr fun i => (map_subtype_subgroupOf (hX i)).symm

theorem subgroupOf_opp {X : Subgroup G} (hX : X ≤ P) :
    (Opp 2 X).subgroupOf P = Opp 2 (X.subgroupOf P) := by
  apply Subgroup.map_injective P.subtype_injective
  rw [map_subtype_subgroupOf ((opp_le X).trans hX), map_opp', map_subtype_subgroupOf hX]

theorem subgroupOf_oUpperTwo {X : Subgroup G} (hX : X ≤ P) :
    (S17.oUpperTwo X).subgroupOf P = S17.oUpperTwo (X.subgroupOf P) := by
  apply Subgroup.map_injective P.subtype_injective
  rw [map_subtype_subgroupOf ((S17.oUpperTwo_le X).trans hX), map_oUpperTwo',
    map_subtype_subgroupOf hX]

omit [Finite G] in
theorem hO2_bar2 : ∀ R : Subgroup (Bar2 P), R.Normal → IsPGroup 2 R → R = ⊥ := by
  intro R hR h2
  have hle : R ≤ CFSG.pCore 2 (Bar2 P) := le_sSup ⟨hR, h2⟩
  rwa [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, le_bot_iff] at hle

omit [Finite G] in
theorem barSub_eq_bot_iff {X : Subgroup G} (hX : X ≤ P) : barSub P X = ⊥ ↔ X ≤ pCoreOf 2 P := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', ← subgroupOf_pCoreOf]
  constructor
  · intro h x hx
    have : (⟨x, hX hx⟩ : ↥P) ∈ (pCoreOf 2 P).subgroupOf P := h hx
    exact this
  · intro h x hx
    exact h hx

omit [Finite G] in
theorem barSub_inj {X Y : Subgroup G} (hOX : pCoreOf 2 P ≤ X) (hX : X ≤ P)
    (hOY : pCoreOf 2 P ≤ Y) (hY : Y ≤ P) (h : barSub P X = barSub P Y) : X = Y := by
  have hk : ∀ Z : Subgroup G, pCoreOf 2 P ≤ Z →
      (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).ker ≤ Z.subgroupOf P := fun Z hZ => by
    rw [QuotientGroup.ker_mk', ← subgroupOf_pCoreOf]
    exact fun x hx => hZ hx
  have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥P))) h
  rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, sup_of_le_left (hk X hOX),
    sup_of_le_left (hk Y hOY)] at h1
  exact subgroupOf_inj hX hY h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

end
