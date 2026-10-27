module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AltSeven
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParDef
public import CFSG.Quasithin.EmptyFaithful.R3c9Alt7

public section

namespace CFSG.Quasithin.CLA7

open Equiv Equiv.Perm CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.AltSeven

theorem sq_mem_inner_of_mulEquiv_alt_seven {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 7)) (α : MulAut X) :
    α ^ 2 ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (Or.inr le_rfl : (7 : ℕ) = 5 ∨ 7 ≤ 7) (MulAut.congr e α)
  have hβ : ∀ y : X, ((e (α y) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      σ * ((e y : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ⁻¹ := fun y => by
    simpa [MulAut.congr_apply] using hσ (e y)
  have hmem : σ * σ ∈ alternatingGroup (Fin 7) := by
    rw [Perm.mem_alternatingGroup, map_mul, Int.units_mul_self]
  refine ⟨e.symm ⟨σ * σ, hmem⟩, MulEquiv.ext fun x => e.injective (Subtype.ext ?_)⟩
  rw [pow_two, MulAut.mul_apply, MulAut.conj_apply, hβ, hβ]
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem fixCount_eq_three_of_even_involution {σ : Perm (Fin 7)} (h2 : σ * σ = 1) (h1 : σ ≠ 1)
    (hs : Perm.sign σ = 1) : fixCount σ = 3 := by
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (hord ▸ Nat.prime_two : (orderOf σ).Prime)
  rw [hord] at hn
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hsign := Equiv.Perm.sign_of_cycleType σ
  rw [hs, hn, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  have hsupp : σ.support.card + fixCount σ = 7 := by
    have : σ.support = Finset.univ.filter (fun i : Fin 7 => ¬ σ i = i) := by
      ext i; simp [Equiv.Perm.mem_support]
    rw [this]
    have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 7)))
      (fun i : Fin 7 => σ i = i)
    simp only [fixCount]
    simp at h3
    omega
  have hev : Even ((n + 1) * 2 + (n + 1)) := by
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    exact (neg_one_pow_eq_one_iff_even hne).1 hsign.symm
  have hle : (n + 1) * 2 ≤ 7 := by omega
  obtain ⟨k, hk⟩ := hev
  omega

theorem pCore_eq_bot_of_mulEquiv_alt_seven {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 7)) : CFSG.pCore 2 X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hsimple : IsSimpleGroup X :=
    (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup
      (by norm_num : 5 ≤ Nat.card (Fin 7)))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 X) with h | h
  · exact h
  · exfalso
    have h2 : IsPGroup 2 X := by
      have := CFSG.pCore_isPGroup (p := 2) (G := X)
      rw [h] at this
      exact IsPGroup.of_equiv this Subgroup.topEquiv
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h2
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.R3c9.card_a7] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 2520)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem center_eq_bot_of_mulEquiv_alt_seven {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 7)) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hc : e x ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 7)),
    Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.mpr (e.injective (hc.trans (map_one e).symm))

noncomputable def centralizerEquivCent {G : Type} [Group G] {L : Subgroup G}
    (e : ↥L ≃* alternatingGroup (Fin 7)) {l : G} (hl : l ∈ L) :
    ↥(L ⊓ Subgroup.centralizer ({l} : Set G)) ≃*
      ↥(cent ((e ⟨l, hl⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7))) := by
  let ψ : ↥L →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.injective
  let H : Subgroup ↥L := (L ⊓ Subgroup.centralizer ({l} : Set G)).subgroupOf L
  have hmap : H.map ψ = cent ((e ⟨l, hl⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hcomm : (x : G) * l = l * (x : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hx).2
      have hax : (⟨l, hl⟩ : ↥L) * x = x * ⟨l, hl⟩ := Subtype.ext hcomm.symm
      refine ⟨Perm.mem_alternatingGroup.mp (e x).2, ?_⟩
      have := congrArg (fun y : ↥L => ((e y : alternatingGroup (Fin 7)) : Perm (Fin 7))) hax
      simpa [ψ] using this
    · rintro ⟨hs, hc⟩
      let ag : alternatingGroup (Fin 7) := ⟨g, Perm.mem_alternatingGroup.mpr hs⟩
      have h1 : e ((e.symm ag) * ⟨l, hl⟩) = e (⟨l, hl⟩ * (e.symm ag)) := by
        apply Subtype.ext
        simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, ag]
        exact hc.symm
      have hmem : e.symm ag ∈ H := Subgroup.mem_subgroupOf.mpr
        ⟨(e.symm ag).2, Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (e.injective h1))⟩
      exact ⟨e.symm ag, hmem, by simp [ψ, ag]⟩
  exact (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans
    ((H.equivMapOfInjective ψ hψ).trans (MulEquiv.subgroupCongr hmap))

theorem not_charTwo_centralizer_of_mulEquiv_alt_seven {G : Type}
    [Group G] {L : Subgroup G} (e : ↥L ≃* alternatingGroup (Fin 7)) {l : G} (hl : l ∈ L)
    (hl1 : l ≠ 1) (hll : l * l = 1) :
    ¬ CharTwo (L ⊓ Subgroup.centralizer ({l} : Set G)) := by
  intro h
  set σ : Perm (Fin 7) := ((e ⟨l, hl⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) with hσ
  have hσ2 : σ * σ = 1 := by
    have h1 : e ⟨l, hl⟩ * e ⟨l, hl⟩ = 1 := by
      rw [← map_mul, ← map_one e]
      exact congrArg e (Subtype.ext hll)
    simpa using congrArg Subtype.val h1
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hl1
    have : e ⟨l, hl⟩ = 1 := Subtype.ext h1
    have h2 : (⟨l, hl⟩ : ↥L) = 1 := e.injective (this.trans (map_one e).symm)
    exact congrArg Subtype.val h2
  have hsign : Perm.sign σ = 1 := Perm.mem_alternatingGroup.mp (e ⟨l, hl⟩).2
  have hf : fixCount σ = 3 := fixCount_eq_three_of_even_involution hσ2 hσ1 hsign
  exact not_charTwo_cent_of_fix_three hσ2 hf
    (CFSG.Quasithin.Rk2.charTwo_of_equiv (centralizerEquivCent e hl) h)

end CFSG.Quasithin.CLA7
