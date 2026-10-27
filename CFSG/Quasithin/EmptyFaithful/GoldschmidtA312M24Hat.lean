module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Mem
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesHat

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped commutatorElement

theorem perfectCore_perm {α : Type} [Fintype α] [DecidableEq α] (h5 : 5 ≤ Nat.card α) :
    perfectCore (⊤ : Subgroup (Equiv.Perm α)) = alternatingGroup α :=
  le_antisymm
    ((Seven.perfectCore_le_commutator ⊤).trans (alternatingGroup.commutator_perm_eq h5).le)
    (le_perfectCore_of_perfect le_top (commutator_alternatingGroup_eq_self h5))

section Hat

variable {G : Type} [Group G] [Finite G]

theorem isExt_hat_of_member {T B Z : Subgroup G} (hT : IsPGroup 2 T) (hB : B ∈ lFamily T)
    (hZ : B ⊔ T = Z) (ρ : ↥Z →* Equiv.Perm (Fin 6)) (hρ : Function.Surjective ρ)
    {V : Subgroup G} (hVZ : V ≤ Z) (hVker : V.subgroupOf Z ≤ ρ.ker)
    (hVn : Z ≤ Subgroup.normalizer (V : Set G))
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVsq : ∀ x ∈ V, x * x = 1)
    (hVcard : Nat.card V = 2 ^ 6) (hkerc : Nat.card ρ.ker = 3 * 2 ^ 6) {u : G} (hu : u ∈ Z)
    (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) (hρu : ρ ⟨u, hu⟩ = 1)
    (hcomm : ∀ v ∈ V, ∃ x ∈ V, ⁅x, u⁆ = v) :
    IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6))) := by
  have hAZ : perfectCore Z ≤ Z := perfectCore_le Z
  have hVA : V ≤ perfectCore Z := by
    have := le_perfectCore_of_commutators hT hB (hZ ▸ hVZ) (hZ ▸ hu) (m := 3) (by norm_num) hu3
      hcomm
    rwa [hZ] at this
  have huA : u ∈ perfectCore Z := by
    have := odd_mem_perfectCore hT hB (hZ ▸ hu) (m := 3) (by norm_num) hu3
    rwa [hZ] at this
  have hA'eq : (perfectCore Z).subgroupOf Z = perfectCore (⊤ : Subgroup ↥Z) :=
    subgroupOf_perfectCore Z
  have hV64 : Nat.card (V.subgroupOf Z) = 2 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVZ).toEquiv, hVcard]
  have hKA : ρ.ker ≤ (perfectCore Z).subgroupOf Z := by
    set N : Subgroup ↥Z := (perfectCore Z).subgroupOf Z ⊓ ρ.ker with hN
    have hVN : V.subgroupOf Z ≤ N := le_inf (fun x hx => hVA hx) hVker
    have huN : (⟨u, hu⟩ : ↥Z) ∈ N := ⟨huA, hρu⟩
    have h64 : 2 ^ 6 ∣ Nat.card N := hV64 ▸ Subgroup.card_dvd_of_le hVN
    have hord : orderOf (⟨u, hu⟩ : ↥Z) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine orderOf_eq_prime (Subtype.ext (by simpa using hu3)) ?_
      intro h
      exact hu1 (congrArg Subtype.val h)
    have h3 : 3 ∣ Nat.card N := hord ▸ Subgroup.orderOf_dvd_natCard N huN
    have h192 : 3 * 2 ^ 6 ∣ Nat.card N := by
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime (2 ^ 6) 3) h64 h3
      rwa [mul_comm] at this
    have hpos : 0 < Nat.card N := Nat.card_pos
    have hNK : N = ρ.ker :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hkerc]; exact Nat.le_of_dvd hpos h192)
    intro k hk
    rw [← hNK] at hk
    exact hk.1
  have hmapA : ((perfectCore Z).subgroupOf Z).map ρ = alternatingGroup (Fin 6) := by
    rw [hA'eq, map_perfectCore ρ ⊤, Subgroup.map_top, MonoidHom.range_eq_top.mpr hρ]
    exact perfectCore_perm (by simp)
  have hcomap : (perfectCore Z).subgroupOf Z = (alternatingGroup (Fin 6)).comap ρ := by
    ext z
    constructor
    · intro hz
      rw [Subgroup.mem_comap, ← hmapA]
      exact ⟨z, hz, rfl⟩
    · intro hz
      rw [Subgroup.mem_comap, ← hmapA] at hz
      obtain ⟨a, ha, haz⟩ := hz
      have hk : a⁻¹ * z ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, haz, inv_mul_cancel]
      have := Subgroup.mul_mem _ ha (hKA hk)
      simpa using this
  have hidx : ((perfectCore Z).subgroupOf Z).index = 2 := by
    rw [hcomap, Subgroup.index_comap_of_surjective _ hρ]
    exact alternatingGroup.index_eq_two
  have hcardZ : Nat.card Z = 2 * Nat.card (perfectCore Z) := by
    have h := Subgroup.card_mul_index ((perfectCore Z).subgroupOf Z)
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv] at h
    omega
  have hcommZ : ⁅Z, Z⁆ ≤ perfectCore Z :=
    PermLat.commutator_le_of_card_eq_two_mul hAZ hcardZ
  have hπ0 : ∀ a : ↥(perfectCore Z), ρ (Subgroup.inclusion hAZ a) ∈ alternatingGroup (Fin 6) := by
    intro a
    rw [← hmapA]
    exact ⟨Subgroup.inclusion hAZ a, a.2, rfl⟩
  let π : ↥(perfectCore Z) →* alternatingGroup (Fin 6) :=
    (ρ.comp (Subgroup.inclusion hAZ)).codRestrict _ hπ0
  have hπs : Function.Surjective π := by
    rintro ⟨s, hs⟩
    rw [← hmapA] at hs
    obtain ⟨z, hz, hzs⟩ := hs
    exact ⟨⟨z.1, hz⟩, Subtype.ext hzs⟩
  have hπk : Nat.card π.ker = 3 * Nat.card (V.subgroupOf (perfectCore Z)) := by
    have hZc : Nat.card Z = 138240 := by
      rw [card_eq_range_mul_ker ρ, hkerc, MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top,
        Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    have hAc := card_eq_range_mul_ker π
    rw [MonoidHom.range_eq_top.mpr hπs, Subgroup.card_top, h360] at hAc
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv, hVcard]
    have hAcard : Nat.card (perfectCore Z) = 69120 := by omega
    rw [hAcard] at hAc
    omega
  have : (V.subgroupOf (perfectCore Z)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVA).mpr (hAZ.trans hVn)
  refine A312ExtShapes.isExt_e2_hat6_of_lFamily hB hZ hAZ hcommZ (perfectCore_perfect Z)
    (V.subgroupOf (perfectCore Z)) (fun x hx y hy => Subtype.ext (hVc x.1 hx y.1 hy))
    (fun x hx => Subtype.ext (hVsq x.1 hx)) ?_ π hπs (fun x hx => ?_) hπk
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv, hVcard]
  · exact Subtype.ext (hVker (show (⟨x.1, hAZ x.2⟩ : ↥Z) ∈ V.subgroupOf Z from hx))

end Hat

end CFSG.Quasithin.A312M24
