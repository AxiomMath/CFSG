module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore

namespace CFSG
end CFSG
open CFSG

/-!
# Reflection arithmetic for the Section 2 setup

The paper uses without comment that an element of the reflection coset of the
cyclic index-two subgroup of a dihedral Sylow subgroup is an involution.  The
`CentralizerSetup` structure stores only the cyclic/index-two data, so this
module supplies the missing transport argument explicitly.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! A cyclic subgroup of the full `2`-power index has to be the rotation
subgroup once the dihedral parameter is at least `2`. -/
public lemma dihedral_cyclic_index_two_eq_rotation
    {m : ℕ} (hm : 2 ≤ m) (A : Subgroup (DihedralGroup (2 ^ m)))
    (hAcyc : IsCyclic A) (hAcard : Nat.card (↥A) = 2 ^ m) :
    A = Subgroup.zpowers (DihedralGroup.r 1) := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  obtain ⟨a, ha⟩ := hAcyc.exists_generator
  rcases dihedralGroup_cases (a : DihedralGroup (2 ^ m)) with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hAle : A ≤ Subgroup.zpowers (DihedralGroup.r 1) := by
      intro x hx
      let xA : ↥A := ⟨x, hx⟩
      obtain ⟨n, hn⟩ := ha xA
      have hn' : (x : DihedralGroup (2 ^ m)) = (a : DihedralGroup (2 ^ m)) ^ n := by
        simpa [xA] using congrArg Subtype.val hn.symm
      rw [hn']
      have hai : (a : DihedralGroup (2 ^ m)) ∈
          Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) := by
        rw [hi]
        exact r_mem_zpowers_r_one (n := 2 ^ m) i
      exact Subgroup.zpow_mem _ hai n
    refine Subgroup.eq_of_le_of_card_ge (H := A)
      (K := Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m))) hAle ?_
    have hcardR : Nat.card (↥(Subgroup.zpowers
        (DihedralGroup.r 1 : DihedralGroup (2 ^ m)))) = 2 ^ m := by
      calc
        Nat.card (↥(Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m)))) =
            orderOf (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) :=
              Nat.card_zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m))
        _ = 2 ^ m := DihedralGroup.orderOf_r_one
    rw [hcardR, hAcard]
  · have horderA : orderOf a = orderOf (a : DihedralGroup (2 ^ m)) :=
      (orderOf_injective A.subtype A.subtype_injective a).symm
    have hcardA2 : Nat.card (↥A) = 2 := by
      calc
        Nat.card (↥A) = orderOf a := by
          rw [← Nat.card_zpowers]
          rw [show Subgroup.zpowers a = ⊤ by
            ext x
            exact ⟨fun _ => trivial, fun hx => (ha x)⟩]
          simp
        _ = orderOf (a : DihedralGroup (2 ^ m)) := horderA
        _ = 2 := by rw [hi, DihedralGroup.orderOf_sr]
    have hpowEq : 2 ^ m = 2 := hAcard.symm.trans hcardA2
    have hpow : 2 ^ m ≤ 2 ^ 1 := by rw [hpowEq]; norm_num
    have : m ≤ 1 := by
      by_contra h
      have hlt : 1 < m := by omega
      have hpowlt : 2 ^ 1 < 2 ^ m := by
        exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt
      omega
    omega

/-! The parameter-one edge case is a Klein four group, so every element has
square one.  We keep the elementary modular argument local to the setup
theorem rather than adding a special-purpose global instance. -/
public theorem centralizerSetup_reflection_isInvolution
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s) :
    IsInvolution s := by
  classical
  rcases c.dihedralEquiv with ⟨e⟩
  let S' : Subgroup G := c.S
  let S0' : Subgroup (↥S') := c.S0.subgroupOf S'
  let A : Subgroup (DihedralGroup (2 ^ c.m)) := S0'.map e.toMonoidHom
  have hcardS0' : Nat.card (↥S0') = 2 ^ c.m := by
    have hcardS : Nat.card (↥S') = 2 * 2 ^ c.m := by
      calc
        Nat.card (↥S') = Nat.card (DihedralGroup (2 ^ c.m)) := Nat.card_congr e.toEquiv
        _ = 2 * 2 ^ c.m := DihedralGroup.nat_card
    have hsub : Nat.card (↥S0') = Nat.card (↥c.S0) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.S0_le_S).toEquiv
    have h1 : Nat.card (↥S') = 2 * Nat.card (↥S0') := by
      have hraw := c.S_index_two
      change Nat.card (↥S') = 2 * Nat.card (↥c.S0) at hraw
      rw [← hsub] at hraw
      exact hraw
    rw [hcardS] at h1
    omega
  have hcardA : Nat.card (↥A) = 2 ^ c.m := by
    change Nat.card (↥(S0'.map e.toMonoidHom)) = 2 ^ c.m
    rw [Subgroup.card_map_of_injective e.injective, hcardS0']
  have hcycS0' : IsCyclic (↥S0') := by
    have e0 := Subgroup.subgroupOfEquivOfLe c.S0_le_S
    have hc0 : IsCyclic (↥(c.S0.subgroupOf (c.S : Subgroup G))) :=
      e0.isCyclic.mpr c.S0_cyclic
    simpa [S0', S'] using hc0
  have hcycA : IsCyclic (↥A) := by
    let em : (↥S0') ≃* (↥A) :=
      Subgroup.equivMapOfInjective S0' e.toMonoidHom e.injective
    exact isCyclic_of_surjective em em.surjective
  have hsS : s ∈ S' := hs.1
  let sS : ↥S' := ⟨s, hsS⟩
  have hsnotA : e sS ∉ A := by
    intro hA
    rcases Subgroup.mem_map.mp hA with ⟨x, hx, hxe⟩
    have hxs : x = sS := by
      apply e.injective
      simpa using hxe
    have hs0 : s ∈ c.S0 := by
      have : sS ∈ S0' := hxs ▸ hx
      exact this
    exact hs.2 hs0
  have hsne : s ≠ 1 := by
    intro h
    apply hs.2
    simpa [h] using c.S0.one_mem
  by_cases hm1 : c.m = 1
  · have hsq : s ^ 2 = 1 := by
      have he_sq : (e sS) ^ 2 = 1 := by
        have esS2 : (e sS : DihedralGroup (2 ^ c.m)) ^ 2 = 1 := by
          rcases dihedralGroup_cases (e sS) with ⟨i, hi⟩ | ⟨i, hi⟩
          · rw [hi, pow_two, DihedralGroup.r_mul_r]
            have hi0 : i + i = 0 := by
              have hi_repr : i = (i.val : ZMod (2 ^ c.m)) :=
                (ZMod.natCast_zmod_val i).symm
              rw [hi_repr, ← Nat.cast_add]
              apply (ZMod.natCast_eq_zero_iff _ _).2
              have hdiv2 : 2 ∣ i.val + i.val := by
                have hi_lt : i.val < 2 := by simpa [hm1] using ZMod.val_lt i
                interval_cases h : i.val <;> simp [h]
              simpa [hm1] using hdiv2
            calc
              DihedralGroup.r (i + i) = DihedralGroup.r 0 := congrArg DihedralGroup.r hi0
              _ = 1 := DihedralGroup.r_zero
          · rw [hi, pow_two, DihedralGroup.sr_mul_sr]
            rw [sub_self]
            exact DihedralGroup.r_zero
        simpa [hm1] using esS2
      have hmap : e (sS ^ 2) = 1 := by
        calc
          e (sS ^ 2) = (e sS) ^ 2 := map_pow e sS 2
          _ = 1 := he_sq
      have : sS ^ 2 = 1 := by
        apply e.injective
        simpa using hmap
      simpa [sS] using congrArg Subtype.val this
    exact ⟨hsne, hsq⟩
  · have hm2 : 2 ≤ c.m := by have hmge := c.one_le_m; omega
    have hArot : A = Subgroup.zpowers (DihedralGroup.r 1) := by
      exact dihedral_cyclic_index_two_eq_rotation hm2 A hcycA hcardA
    have hnotrot : e sS ∉ Subgroup.zpowers (DihedralGroup.r 1) := by
      intro h
      apply hsnotA
      rw [hArot]
      exact h
    rcases dihedralGroup_cases (e sS) with ⟨i, hi⟩ | ⟨i, hi⟩
    · exfalso
      apply hnotrot
      rw [hi]
      exact r_mem_zpowers_r_one (n := 2 ^ c.m) i
    · refine ⟨hsne, ?_⟩
      have hord : orderOf s = 2 := by
        calc
          orderOf s = orderOf sS := by
            have horder := orderOf_injective (c.S : Subgroup G).subtype
              (c.S : Subgroup G).subtype_injective sS
            simpa [sS] using horder.symm
          _ = orderOf (e sS) := (e.orderOf_eq sS).symm
          _ = 2 := by rw [hi, DihedralGroup.orderOf_sr]
      exact (orderOf_dvd_iff_pow_eq_one).mp (by simpa [hord])

end CFSG.GorensteinWalter
