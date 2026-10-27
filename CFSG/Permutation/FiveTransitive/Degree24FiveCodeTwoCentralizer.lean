module

public import CFSG.Permutation.FiveTransitive.Degree24FiveAut
public import CFSG.Permutation.FiveTransitive.Degree24LocalCentralizerSupport
public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeTwoPermutation

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem sylow_five_card_twenty_five_centralizer_card_dvd_seven_hundred_fifty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s))
    (hScard : Nat.card S = 25) :
    Nat.card
        (Subgroup.centralizer
          (S : Set (fixingSubgroup P s))) ∣
      750 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let inclusion : S →* Equiv.Perm X :=
    P.subtype.comp
      (H.subtype.comp
        (S : Subgroup H).subtype)
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  let R : Subgroup (Equiv.Perm X) :=
    inclusion.range
  let eSR : S ≃* R :=
    MonoidHom.ofInjective hinclusion
  have hRcard : Nat.card R = 25 := by
    calc
      Nat.card R = Nat.card S :=
        Nat.card_congr eSR.symm.toEquiv
      _ = 25 := hScard
  have hsFixed :
      s ⊆ MulAction.fixedPoints R X := by
    intro x hx
    rw [MulAction.mem_fixedPoints]
    intro r
    obtain ⟨u, hu⟩ := r.prop
    change (r.1 : Equiv.Perm X) x = x
    rw [← hu]
    have hfix :=
      (mem_fixingSubgroup_iff P).mp
        (((S : Subgroup H).subtype u : H).prop)
        x hx
    change
      (((u : H) : P) : Equiv.Perm X) x = x
    simpa [Subgroup.smul_def,
      Equiv.Perm.smul_def] using hfix
  obtain ⟨r, hrSupport⟩ :
      ∃ r : R,
        (r.1 : Equiv.Perm X).support.card = 15 := by
    rcases
        subgroup_card_twenty_five_support_distribution
          X hcard R hRcard with
      hfive | ⟨_, _, hfifteen⟩ |
        ⟨hfixedFour, _⟩
    · obtain ⟨r⟩ :=
        (Nat.card_pos_iff.mp hfive).1
      have hr :
          (r.1.1 : Equiv.Perm X).support.card = 5 :=
        r.prop
      obtain ⟨u, hu⟩ := r.1.prop
      have hmem :
          (r.1 : Equiv.Perm X) ∈ P := by
        rw [← hu]
        exact
          (((S : Subgroup H).subtype u : H) : P).prop
      have hne : (r.1 : Equiv.Perm X) ≠ 1 := by
        intro hrone
        rw [hrone, Equiv.Perm.support_one] at hr
        norm_num at hr
      exact False.elim
        (hnotAlt
          (alternatingGroup_le_of_nontrivial_support_le_seven
            X P hcard h5 hmem hne (by omega)))
    · obtain ⟨r⟩ :=
        (Nat.card_pos_iff.mp (by omega : 0 <
          permutationSubgroupSupportCount R 15)).1
      exact ⟨r.1, r.prop⟩
    · have hfixedNcard :
          (MulAction.fixedPoints R X).ncard = 4 := by
        rw [← Nat.card_coe_set_eq]
        exact hfixedFour
      have hle :=
        Set.ncard_le_ncard hsFixed
      rw [hs, hfixedNcard] at hle
      omega
  let u : S := eSR.symm r
  let g : Equiv.Perm X := ((u : H) : P)
  have hgu : g = (r : Equiv.Perm X) := by
    change inclusion u = r.1
    exact congrArg Subtype.val
      (eSR.apply_symm_apply r)
  have hsupport : g.support.card = 15 := by
    rw [hgu]
    exact hrSupport
  have hgpow : g ^ 5 = 1 := by
    have hrpow :=
      subgroup_card_twenty_five_pow_five_eq_one
        X hcard R hRcard r
    have hrpowPerm :
        ((r : Equiv.Perm X) ^ 5) = 1 :=
      congrArg Subtype.val hrpow
    rwa [hgu]
  have hgCycleTypeRaw :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hgpow
  have hsum := g.sum_cycleType
  rw [hgCycleTypeRaw, Multiset.sum_replicate,
    nsmul_eq_mul, Nat.cast_id, hsupport] at hsum
  have hcycleCard : g.cycleType.card = 3 := by
    omega
  have hgCycleType : g.cycleType = {5, 5, 5} := by
    rw [hgCycleTypeRaw, hcycleCard]
    norm_num
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hgSupportExtend :
      Equiv.Perm.ofSubtype gSupport = g := by
    exact Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgSupportCycleType :
      gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hgSupportExtend]
  have hsupportSubtypeCard :
      Fintype.card g.support = 15 := by
    calc
      Fintype.card g.support = g.support.card :=
        Fintype.card_coe _
      _ = 15 := hsupport
  have hsupportCentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) = 750 := by
    rw [Equiv.Perm.nat_card_centralizer,
      hgSupportCycleType, hgCycleType,
      hsupportSubtypeCard]
    norm_num
  have hdvd :
      Nat.card
          (Subgroup.centralizer
            ((S : Subgroup H) : Set H)) ∣
        Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) := by
    simpa only [H, g, gSupport] using
      local_centralizer_card_dvd_support_centralizer
        X P hcard h5 hnotAlt s hs
          (S : Subgroup H) u (by
            change 12 ≤ g.support.card
            omega)
  have hSset :
      ((S : Subgroup H) : Set H) = (S : Set H) :=
    rfl
  rw [hSset] at hdvd
  rw [hsupportCentralizerCard] at hdvd
  simpa only [H] using hdvd

end FiveTransitive.Degree24

end CFSG
