
module

public import CFSG.Quasithin.H13.OverSylowDc
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.He.Simple

public section

namespace CFSG.Quasithin.H13.LocDbl.OverHe

open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Sporadic.He (J a b card_J heEquivJ)

@[expose] def oTwoUp {A : Type} [Group A] (X : Subgroup A) : Subgroup A :=
  Subgroup.closure {x | x ∈ X ∧ Odd (orderOf x)}

theorem mem_oTwoUp_of_odd {A : Type} [Group A] {X : Subgroup A} {x : A} (hx : x ∈ X)
    (ho : Odd (orderOf x)) : x ∈ oTwoUp X :=
  Subgroup.subset_closure ⟨hx, ho⟩

theorem oTwoUpper_map {A B : Type} [Group A] [Group B] (e : A ≃* B) (U : Subgroup A) :
    oTwoUp (U.map e.toMonoidHom) = (oTwoUp U).map e.toMonoidHom := by
  unfold oTwoUp
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, hodd⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    rwa [show orderOf (e.toMonoidHom x) = orderOf x from orderOf_injective e.toMonoidHom e.injective x]
      at hodd
  · rintro ⟨x, ⟨hx, hodd⟩, rfl⟩
    refine ⟨Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
    rwa [show orderOf (e.toMonoidHom x) = orderOf x from orderOf_injective e.toMonoidHom e.injective x]

@[expose] def SubO2Prop {A : Type} [Group A] (m : ℕ) (U : Subgroup A) : Prop :=
  ∃ Y : Subgroup A, Y ≤ U ∧ (Y.subgroupOf U).Normal ∧ Nat.card Y = m ∧ Y ≤ oTwoUp U

theorem SubO2Prop.of_map {A B : Type} [Group A] [Group B] (e : A ≃* B) {m : ℕ} {U : Subgroup A}
    (h : SubO2Prop m (U.map e.toMonoidHom)) : SubO2Prop m U := by
  obtain ⟨Y, hYU, hYn, hYc, hYo⟩ := h
  have hmemY : ∀ z : A, z ∈ Y.map e.symm.toMonoidHom → e z ∈ Y := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    simpa using hy
  refine ⟨Y.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp (hYU (hmemY z hz))
    have : u = z := e.injective hue
    exact this ▸ hu
  · refine ⟨fun n hn g => ?_⟩
    have hn1 : (n : A) ∈ Y.map e.symm.toMonoidHom := Subgroup.mem_subgroupOf.mp hn
    have hn' : (⟨e n, Subgroup.mem_map.mpr ⟨n, n.2, rfl⟩⟩ : ↥(U.map e.toMonoidHom)) ∈
        Y.subgroupOf (U.map e.toMonoidHom) := Subgroup.mem_subgroupOf.mpr (hmemY _ hn1)
    have := hYn.conj_mem _ hn'
      (⟨e g, Subgroup.mem_map.mpr ⟨g, g.2, rfl⟩⟩ : ↥(U.map e.toMonoidHom))
    rw [Subgroup.mem_subgroupOf] at this ⊢
    have h2 : e ((g : A) * n * (g : A)⁻¹) ∈ Y := by
      have h := this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at h
      rw [map_mul, map_mul, map_inv]
      exact h
    refine Subgroup.mem_map.mpr ⟨e ((g : A) * n * (g : A)⁻¹), h2, ?_⟩
    simp
  · rw [Subgroup.card_map_of_injective e.symm.injective]; exact hYc
  · intro z hz
    have h1 : e z ∈ Y := hmemY z hz
    have h2 := hYo h1
    rw [oTwoUpper_map] at h2
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp h2
    have : x = z := e.injective hxe
    exact this ▸ hx

theorem SubO2Prop.of_sylow {Γ : Type} [Group Γ] [Finite Γ] {R : Subgroup Γ} (hR : Nat.card R = 2 ^ 10)
    (hnd : ¬ 2 ^ (10 + 1) ∣ Nat.card Γ) {m : ℕ}
    (hP : ∀ U : Subgroup Γ, R ≤ U → Nat.card U = 2 ^ 10 * 3 ^ 2 → SubO2Prop m U) :
    ∀ U : Subgroup Γ, Nat.card U = 2 ^ 10 * 3 ^ 2 → SubO2Prop m U := by
  intro U hU
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥U) 2 (n := 10)
    (by rw [hU]; exact Dvd.intro (3 ^ 2) rfl)
  have hS : Nat.card (K.map U.subtype) = 2 ^ 10 := by
    rw [Subgroup.card_map_of_injective U.subtype_injective, hK]
  obtain ⟨g, hg⟩ := exists_conj_of_card_two hR hS hnd
  have hRU : R ≤ U.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro y hy
    have hy1 : g * y * g⁻¹ ∈ K.map U.subtype := by
      rw [← hg]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.mp hy1
    refine Subgroup.mem_map.mpr ⟨g * y * g⁻¹, ?_, ?_⟩
    · rw [← hu]; exact u.2
    · simp [MulAut.conj_apply, mul_assoc]
  have hcard : Nat.card (U.map (MulAut.conj g⁻¹).toMonoidHom) = 2 ^ 10 * 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]; exact hU
  exact SubO2Prop.of_map (MulAut.conj g⁻¹) (hP _ hRU hcard)

theorem SubO2Prop.of_gens {Γ : Type} [Group Γ] [Finite Γ] {U V : Subgroup Γ} (hUV : U ≤ V)
    {yL : List Γ} (hcard : Nat.card (Subgroup.closure {x | x ∈ yL}) = 2 ^ 6 * 3)
    (hy3 : ∀ y ∈ yL, y ^ 3 = 1) (hnorm : V ≤ Subgroup.normalizer (Subgroup.closure {x | x ∈ yL} : Set Γ))
    (hgen : ∀ y ∈ yL, y ∈ U) : SubO2Prop (2 ^ 6 * 3) U := by
  have hYU : Subgroup.closure {x | x ∈ yL} ≤ U := (Subgroup.closure_le _).mpr hgen
  refine ⟨Subgroup.closure {x | x ∈ yL}, hYU, ?_, hcard, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hYU).mpr (hUV.trans hnorm)
  · refine (Subgroup.closure_le _).mpr fun y hy => ?_
    refine mem_oTwoUp_of_odd (hgen y hy) ?_
    have hd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one (hy3 y hy)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h <;> rw [h] <;> decide

theorem SubO2Prop.of_equiv_card {Q B : Type} [Group Q] [Group B] {m n : ℕ}
    (h : ∀ V : Subgroup B, Nat.card V = n → SubO2Prop m V) (e : Q ≃* B) (U : Subgroup Q)
    (hU : Nat.card U = n) : SubO2Prop m U := by
  apply SubO2Prop.of_map e
  apply h
  rw [Subgroup.card_map_of_injective e.injective]
  exact hU

end CFSG.Quasithin.H13.LocDbl.OverHe
