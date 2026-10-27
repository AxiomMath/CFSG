module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Facts
public import CFSG.Quasithin.Recognition.M12AmalClass
public import CFSG.Quasithin.Recognition.M12AmalAutFeit

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.Bridge

@[expose] def SylowCenterCyclicSLEps3 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (p : ℕ), (p % 8 = 3 ∨ p % 8 = 5) →
    F6.IsSLEps3GraphExt p D → ∀ P : Sylow 2 D, IsCyclic ↥(Subgroup.center ↥(P : Subgroup D))

namespace Insp15418

theorem isCyclic_of_forall_eq {X : Type*} [Group X] [Finite X]
    (h : ∀ a b : X, a ≠ 1 → b ≠ 1 → a = b) : IsCyclic X := by
  classical
  by_cases hX : ∃ a : X, a ≠ 1
  · obtain ⟨a, ha⟩ := hX
    refine ⟨a, fun b => ?_⟩
    by_cases hb : b = 1
    · exact ⟨0, by simp [hb]⟩
    · exact ⟨1, by simp [h b a hb ha]⟩
  · push Not at hX
    have : Subsingleton X := ⟨fun a b => (hX a).trans (hX b).symm⟩
    exact isCyclic_of_subsingleton

theorem isCyclic_center_of_mulEquiv {D G' : Type*} [Group D] [Finite D] [Group G']
    (ε : D ≃* G') {T : Subgroup G'} (hT : IsPGroup 2 T ∧ ¬ 2 ∣ T.index)
    (hc : IsCyclic ↥(Subgroup.center ↥T)) (P : Sylow 2 D) :
    IsCyclic ↥(Subgroup.center ↥(P : Subgroup D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T' := T.comap ε.toMonoidHom with hT'
  have hT'2 : IsPGroup 2 ↥T' := hT.1.comap_of_injective ε.toMonoidHom ε.injective
  have hT'idx : ¬ 2 ∣ T'.index := by
    rw [hT', Subgroup.index_comap_of_surjective _ ε.surjective]
    exact hT.2
  let S : Sylow 2 D := hT'2.toSylow hT'idx
  have e₁ : ↥(P : Subgroup D) ≃* ↥T' := Sylow.equiv P S
  have e₂ : ↥T' ≃* ↥T := by
    have hmap : T'.map ε.toMonoidHom = T :=
      Subgroup.map_comap_eq_self_of_surjective ε.surjective T
    exact (T'.equivMapOfInjective ε.toMonoidHom ε.injective).trans (MulEquiv.subgroupCongr hmap)
  exact (Subgroup.centerCongr (e₁.trans e₂)).isCyclic.mpr hc

theorem m12_center_chk : ∀ i < 64, (compL (M12Amal.tl i) (M12Amal.gl 0) =
      compL (M12Amal.gl 0) (M12Amal.tl i) ∧
    compL (M12Amal.tl i) (M12Amal.gl 1) = compL (M12Amal.gl 1) (M12Amal.tl i) ∧
    compL (M12Amal.tl i) (M12Amal.gl 2) = compL (M12Amal.gl 2) (M12Amal.tl i)) →
    i = 0 ∨ i = 4 := by
  decide +kernel

open M12Amal in
theorem m12_center_T {c : M12G} (hc : c ∈ m12Data.T)
    (hcent : ∀ t ∈ m12Data.T, c * t = t * c) : c = 1 ∨ c = telG 4 := by
  obtain ⟨i, rfl⟩ := (m12Data.mem_T_iff c).mp hc
  have hgen : ∀ k, k < 3 → genG k ∈ m12Data.T := by
    intro k hk
    interval_cases k
    · exact m12Data.a_mem_T
    · exact m12Data.b_mem_T
    · exact m12Data.s_mem_T
  have hcomm : ∀ k, k < 3 → compL (tl i) (gl k) = compL (gl k) (tl i) := by
    intro k hk
    have h := hcent (genG k) (hgen k hk)
    have hA : ReprG (compL (tl i) (gl k)) (telG i * genG k) :=
      reprG_mul (reprG_tel i i.2) (reprG_gen k (by omega))
    have hB : ReprG (compL (gl k) (tl i)) (genG k * telG i) :=
      reprG_mul (reprG_gen k (by omega)) (reprG_tel i i.2)
    change telG i * genG k = genG k * telG i at h
    rw [h] at hA
    exact repL_unique hA hB
  rcases m12_center_chk i i.2 ⟨hcomm 0 (by norm_num), hcomm 1 (by norm_num),
    hcomm 2 (by norm_num)⟩ with h | h
  · left
    change telG i = 1
    rw [h, tel_zero]
  · right
    change telG i = telG 4
    rw [h]

theorem isCyclic_center_m12T : IsCyclic ↥(Subgroup.center ↥M12Amal.m12Data.T) := by
  refine isCyclic_of_forall_eq fun a b ha hb => ?_
  have key : ∀ x : ↥(Subgroup.center ↥M12Amal.m12Data.T), x ≠ 1 →
      ((x : ↥M12Amal.m12Data.T) : M12Amal.M12G) = M12Amal.telG 4 := by
    intro x hx
    have hc : ∀ t ∈ M12Amal.m12Data.T, ((x : ↥M12Amal.m12Data.T) : M12Amal.M12G) * t = t * x := by
      intro t ht
      have := Subgroup.mem_center_iff.mp x.2 ⟨t, ht⟩
      exact (congrArg Subtype.val this).symm
    rcases m12_center_T (x : ↥M12Amal.m12Data.T).2 hc with h | h
    · exact absurd (Subtype.ext (Subtype.ext h)) hx
    · exact h
  exact Subtype.ext (Subtype.ext ((key a ha).trans (key b hb).symm))

theorem sylowCenterCyclic_m12 {D : Type} [Group D] [Finite D] (h : F6.IsM12 D)
    (P : Sylow 2 D) : IsCyclic ↥(Subgroup.center ↥(P : Subgroup D)) := by
  obtain ⟨ε⟩ := nonempty_mulEquiv_quasithinM12_of_isM12 h
  exact isCyclic_center_of_mulEquiv ε M12Amal.m12_syl isCyclic_center_m12T P

theorem aut_center_chk : ∀ i < 128, (compL (M12AmalAut.tl i) (M12AmalAut.gl 0) =
      compL (M12AmalAut.gl 0) (M12AmalAut.tl i) ∧
    compL (M12AmalAut.tl i) (M12AmalAut.gl 1) = compL (M12AmalAut.gl 1) (M12AmalAut.tl i) ∧
    compL (M12AmalAut.tl i) (M12AmalAut.gl 2) = compL (M12AmalAut.gl 2) (M12AmalAut.tl i)) →
    i = 0 ∨ i = 111 := by
  decide +kernel

open M12AmalAut in
theorem aut_center_T {c : AutG} (hc : c ∈ autData.T)
    (hcent : ∀ t ∈ autData.T, c * t = t * c) : c = 1 ∨ c = telG 111 := by
  obtain ⟨i, rfl⟩ := (autData.mem_T_iff c).mp hc
  have hgen : ∀ k, k < 3 → genG k ∈ autData.T := by
    intro k hk
    interval_cases k
    · exact autData.a_mem_T
    · exact autData.b_mem_T
    · exact autData.s_mem_T
  have hcomm : ∀ k, k < 3 → compL (tl i) (gl k) = compL (gl k) (tl i) := by
    intro k hk
    have h := hcent (genG k) (hgen k hk)
    have hA : ReprG (compL (tl i) (gl k)) (telG i * genG k) :=
      reprG_mul (reprG_tel i i.2) (reprG_gen k (by omega))
    have hB : ReprG (compL (gl k) (tl i)) (genG k * telG i) :=
      reprG_mul (reprG_gen k (by omega)) (reprG_tel i i.2)
    change telG i * genG k = genG k * telG i at h
    rw [h] at hA
    exact repL_unique hA hB
  rcases aut_center_chk i i.2 ⟨hcomm 0 (by norm_num), hcomm 1 (by norm_num),
    hcomm 2 (by norm_num)⟩ with h | h
  · left
    change telG i = 1
    rw [h, tel_zero]
  · right
    change telG i = telG 111
    rw [h]

theorem isCyclic_center_autT : IsCyclic ↥(Subgroup.center ↥M12AmalAut.autData.T) := by
  refine isCyclic_of_forall_eq fun a b ha hb => ?_
  have key : ∀ x : ↥(Subgroup.center ↥M12AmalAut.autData.T), x ≠ 1 →
      ((x : ↥M12AmalAut.autData.T) : M12AmalAut.AutG) = M12AmalAut.telG 111 := by
    intro x hx
    have hc : ∀ t ∈ M12AmalAut.autData.T,
        ((x : ↥M12AmalAut.autData.T) : M12AmalAut.AutG) * t = t * x := by
      intro t ht
      have := Subgroup.mem_center_iff.mp x.2 ⟨t, ht⟩
      exact (congrArg Subtype.val this).symm
    rcases aut_center_T (x : ↥M12AmalAut.autData.T).2 hc with h | h
    · exact absurd (Subtype.ext (Subtype.ext h)) hx
    · exact h
  exact Subtype.ext (Subtype.ext ((key a ha).trans (key b hb).symm))

theorem sylowCenterCyclic_autM12
    {D : Type} [Group D] [Finite D] (h : F6.IsAutM12 D)
    (P : Sylow 2 D) : IsCyclic ↥(Subgroup.center ↥(P : Subgroup D)) := by
  obtain ⟨eD⟩ := h
  obtain ⟨m⟩ := autM12PermModel
  exact isCyclic_center_of_mulEquiv (eD.trans m.symm) M12AmalAut.aut_syl isCyclic_center_autT P

end Insp15418

open Insp15418

theorem sylowCenterCyclic15418_of
    (hSL : SylowCenterCyclicSLEps3) : SylowCenterCyclic15418 := by
  intro D _ _ hD P
  rcases hD with h | h | ⟨p, hp, h⟩
  · exact sylowCenterCyclic_m12 h P
  · exact sylowCenterCyclic_autM12 h P
  · exact hSL D p hp h P

end CFSG.Quasithin.EmptyFaithfulMultiple
