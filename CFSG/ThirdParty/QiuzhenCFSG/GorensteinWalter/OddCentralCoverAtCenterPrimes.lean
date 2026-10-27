module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd central covers controlled at primes in the kernel

This is the kernel-prime form of
`BenderSuzuki.lemma114_oddCentralCover_eq_bot`: cyclicity of quotient Sylow
subgroups is needed only at primes dividing the central kernel.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A perfect finite central extension with odd central kernel is trivial if,
at every prime dividing the kernel, the corresponding Sylow subgroups of the
quotient are cyclic. -/
public theorem oddCentralCover_eq_bot_of_cyclic_sylow_at_center_primes
    {E : Type u} [Group E] [Finite E]
    (hperfect : commutator E = ⊤)
    (Z : Subgroup E) [Z.Normal]
    (hZcenter : Z = Subgroup.center E)
    (hZodd : Odd (Nat.card Z))
    (hquot : ∀ r [Fact r.Prime], r ∣ Nat.card Z → r ≠ 2 →
      ∀ S : Sylow r (E ⧸ Z), IsCyclic S) :
    Z = ⊥ := by
  classical
  apply le_antisymm
  · intro z hz
    by_contra hz1
    have hZcard_ne_one : Nat.card Z ≠ 1 := by
      intro hcard
      let : Subsingleton Z := (Nat.card_eq_one_iff_unique.mp hcard).1
      have huniq : ∀ x y : Z, x = y := fun x y => Subsingleton.elim _ _
      apply hz1
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val (huniq ⟨z, hz⟩ 1)
    obtain ⟨r, hrprime, hrdiv⟩ := Nat.exists_prime_and_dvd hZcard_ne_one
    let : Fact r.Prime := ⟨hrprime⟩
    have hrne2 : r ≠ 2 := by
      intro hr
      subst r
      exact hZodd.not_two_dvd_nat hrdiv
    obtain ⟨zZ, hzZorder⟩ :=
      exists_prime_orderOf_dvd_card' (G := Z) r hrdiv
    let zE : E := zZ
    have hzEorder : orderOf zE = r := by
      simpa [zE] using hzZorder
    have hzEcenter : zE ∈ Subgroup.center E := by
      rw [← hZcenter]
      exact zZ.property
    have hzp : IsPGroup r (Subgroup.zpowers zE) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hzEorder]
      simp
    obtain ⟨S, hzS⟩ := hzp.exists_le_sylow
    let q : E →* E ⧸ Z := QuotientGroup.mk' Z
    let SbarSylow : Sylow r (E ⧸ Z) :=
      Sylow.mapSurjective (QuotientGroup.mk'_surjective Z) S
    let Sbar : Subgroup (E ⧸ Z) := SbarSylow
    have hSbarCyclic : IsCyclic Sbar := hquot r hrdiv hrne2 SbarSylow
    let : IsCyclic Sbar := hSbarCyclic
    let qS : S →* Sbar :=
      ((q.comp (S : Subgroup E).subtype).codRestrict Sbar (by
        intro x
        change q (x : E) ∈ Sbar
        rw [show Sbar = (SbarSylow : Subgroup (E ⧸ Z)) by rfl,
          Sylow.coe_mapSurjective]
        exact Subgroup.mem_map_of_mem q
          (show (x : E) ∈ (S : Subgroup E) from x.property)))
    have hqSker : qS.ker ≤ Subgroup.center S := by
      intro x hx
      apply Subgroup.mem_center_iff.mpr
      intro y
      have hxZ : (x : E) ∈ Z := by
        apply (QuotientGroup.eq_one_iff (x : E)).mp
        exact congrArg Subtype.val hx
      have hxcent : (x : E) ∈ Subgroup.center E := by
        rw [← hZcenter]
        exact hxZ
      have hxy : (x : E) * (y : E) = (y : E) * (x : E) :=
        (Subgroup.mem_center_iff.mp hxcent (y : E)).symm
      apply Subtype.ext
      exact hxy.symm
    have hcommS : ∀ a b : S, a * b = b * a := by
      intro a b
      exact commutative_of_cyclic_center_quotient qS hqSker a b
    let : IsMulCommutative S := ⟨⟨hcommS⟩⟩
    let : CommGroup S := IsMulCommutative.instCommGroup
    let tr : E →* S := MonoidHom.transfer (MonoidHom.id S)
    have htrivial : ∀ x : E, tr x = 1 := by
      intro x
      have hxcomm : x ∈ commutator E := by
        rw [hperfect]
        trivial
      have hxker : x ∈ tr.ker :=
        Abelianization.commutator_subset_ker tr hxcomm
      exact hxker
    have hkey : ∀ (k : ℕ) (g₀ : E),
        g₀⁻¹ * zE ^ k * g₀ ∈ (S : Subgroup E) →
          g₀⁻¹ * zE ^ k * g₀ = zE ^ k := by
      intro k g₀ _
      have hzpowcent : zE ^ k ∈ Subgroup.center E :=
        (Subgroup.center E).pow_mem hzEcenter k
      have h := Subgroup.mem_center_iff.mp hzpowcent g₀
      calc
        g₀⁻¹ * zE ^ k * g₀ = g₀⁻¹ * (g₀ * zE ^ k) := by
          rw [mul_assoc, h.symm]
        _ = zE ^ k := by group
    have htransfer_pow :=
      MonoidHom.transfer_eq_pow (MonoidHom.id S) zE hkey
    have hpow_one : zE ^ (S : Subgroup E).index = 1 := by
      have htr := htrivial zE
      rw [htransfer_pow] at htr
      exact congrArg Subtype.val htr
    have hord_dvd_index : r ∣ (S : Subgroup E).index := by
      have h : orderOf zE ∣ (S : Subgroup E).index :=
        (orderOf_dvd_iff_pow_eq_one).2 hpow_one
      simpa [hzEorder] using h
    exact S.not_dvd_index hord_dvd_index
  · exact bot_le

end CFSG.GorensteinWalter
