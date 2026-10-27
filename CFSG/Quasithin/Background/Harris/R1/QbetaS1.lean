module

public import CFSG.Quasithin.Recognition.F112J2FamB

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
  CFSG.Quasithin.A5Model

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem exists_S1_act (C5 : F112J2.FiveCtx K1 L2 S Zs) {τ : A5} (hτ : τ ∈ K4) :
    ∃ k : ↥K1, (k : G) ∈ S ∧ C5.D.θ k = τ := by
  classical
  let S1 : Subgroup ↥K1 := (S ⊓ K1).subgroupOf K1
  have hsyl := C5.h.hyp.h1.sylow
  have hS1p : IsPGroup 2 S1 := by
    intro x
    obtain ⟨n, hn⟩ := C5.h.hyp.h1.pgroup ⟨(x : ↥K1).1, (Subgroup.mem_subgroupOf.mp x.2).1⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hn
  have hS1i : ¬ 2 ∣ S1.index := hsyl.2.2
  let P2 : Subgroup A5 := S1.map C5.D.θ
  have hP2K4 : P2 ≤ K4 := by
    rintro _ ⟨s, hs, rfl⟩
    have hsB : (s : G) ∈ borelOf K1 S :=
      F1.sylow_le_borelOf K1 S (Subgroup.mem_subgroupOf.mp hs)
    have hA4 : C5.D.θ s ∈ A4s := (C5.D.stab s).mpr hsB
    obtain ⟨n, hn⟩ := hS1p ⟨s, hs⟩
    have h1 : (C5.D.θ s) ^ (2 ^ n) = 1 := by
      rw [← map_pow]
      have : s ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
      rw [this, map_one]
    have h12 := A4s_pow_twelve _ hA4
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    have h2 : 2 ^ a ∣ 12 := ha ▸ orderOf_dvd_of_pow_eq_one h12
    have ha2 : a ≤ 2 := by
      by_contra hcon
      push Not at hcon
      have : 2 ^ 3 ∣ 2 ^ a := Nat.pow_dvd_pow 2 hcon
      have := this.trans h2
      omega
    have h4 : (C5.D.θ s) ^ 4 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ha]
      have : 2 ^ a ∣ 2 ^ 2 := Nat.pow_dvd_pow 2 ha2
      simpa using this
    exact mem_K4_of_pow_four _ hA4 h4
  have hP2i : ¬ 2 ∣ P2.index := fun hd =>
    hS1i (hd.trans (Subgroup.index_map_dvd S1 C5.D.surj))
  have hrel : P2.relIndex K4 = 1 := by
    have h1 : P2.relIndex K4 * K4.index = P2.index := Subgroup.relIndex_mul_index hP2K4
    have h2 : ¬ 2 ∣ P2.relIndex K4 := fun hd => hP2i (h1 ▸ hd.mul_right _)
    have h3 : P2.relIndex K4 ∣ 4 := card_K4 ▸ Subgroup.relIndex_dvd_card P2 K4
    have h4 : P2.relIndex K4 ∣ 2 ^ 2 := by simpa using h3
    obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
    rcases e with _ | e
    · simpa using he
    · exfalso
      apply h2
      rw [he]
      exact dvd_pow_self 2 (Nat.succ_ne_zero e)
  have hK4P2 : K4 ≤ P2 := Subgroup.relIndex_eq_one.mp hrel
  obtain ⟨s, hs, hsτ⟩ := hK4P2 hτ
  exact ⟨s, (Subgroup.mem_subgroupOf.mp hs).1, hsτ⟩

end CFSG.Quasithin.Background.Harris.R1
