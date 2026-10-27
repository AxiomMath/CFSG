module

public import CFSG.LieType.Ree.LargeReeCentralTwoCover
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiCoverBound
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

universe u

namespace CFSG.RankThree.PartOne.KEXC

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem odd_card_ker_of_central_two_cover {T : Type*} [Group T] {E : Type u} [Group E] [Finite E]
    [Group.IsPerfect E] (η : E →* T) (hη : Function.Surjective η) (hC : η.ker ≤ center E)
    (H : ∀ {E' : Type u} [Group E'] [Finite E'] [Group.IsPerfect E'] (θ : E' →* T),
      Function.Surjective θ → θ.ker ≤ center E' → IsPGroup 2 θ.ker → θ.ker = ⊥) :
    Odd (Nat.card η.ker) := by
  set N := CFSG.LieType.Steinberg.oddPart η.ker hC
  have hN : N ≤ η.ker := fun _ hc => hc.1
  set η' : E ⧸ N →* T := QuotientGroup.lift N η hN
  have hη'mk : ∀ x : E, η' (x : E ⧸ N) = η x := fun x => QuotientGroup.lift_mk _ _ _
  have hη' : Function.Surjective η' := by
    intro q
    obtain ⟨x, rfl⟩ := hη q
    exact ⟨x, hη'mk x⟩
  have hker' : η'.ker = η.ker.map (QuotientGroup.mk' N) := QuotientGroup.ker_lift N η hN
  have hcen' : η'.ker ≤ center (E ⧸ N) := by
    rw [hker']
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    exact congrArg (QuotientGroup.mk (s := N)) (mem_center_iff.1 (hC hc) g)
  have h2' : IsPGroup 2 η'.ker := by
    rintro ⟨x, hx⟩
    rw [hker'] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨a, ha⟩ := CFSG.LieType.Steinberg.exists_pow_two_pow_mem_oddPart hC hc
    refine ⟨a, Subtype.ext ?_⟩
    change (QuotientGroup.mk' N c) ^ 2 ^ a = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ha
  have : Group.IsPerfect (E ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hbot := H η' hη' hcen' h2'
  have hodd : ∀ c ∈ η.ker, Odd (orderOf c) := by
    intro c hc
    have hmem : (c : E ⧸ N) ∈ η'.ker := by
      rw [MonoidHom.mem_ker, hη'mk]
      exact hc
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hmem.2
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hx' : orderOf ((x : η.ker) : E) = 2 := by rw [Subgroup.orderOf_coe, hx]
  have := hodd _ x.2
  rw [hx'] at this
  exact (Nat.not_even_iff_odd.2 this) even_two

section Main


theorem odd_center_of_suzuki_ree_model {J : Type} [Group J] [Finite J] [Group.IsPerfect J]
    {t : StatedLieTag} {m : ℕ} (hm : 5 ≤ m) (ht : t = .twistedB2 ∨ t = .twistedF4)
    (hmodel : LieModel (J ⧸ center J) t 0 2 m) : Odd (Nat.card (center J)) := by
  let η : J →* J ⧸ center J := QuotientGroup.mk' (center J)
  have hη : Function.Surjective η := QuotientGroup.mk'_surjective _
  have hker : η.ker = center J := QuotientGroup.ker_mk' _
  have hodd : Odd (Nat.card η.ker) := by
    refine odd_card_ker_of_central_two_cover η hη hker.le fun θ hθ hθC h2 => ?_
    rcases ht with rfl | rfl
    · exact (even_Suzuki_catalog_perfect_central_two_kernel_bound θ hθ hθC h2 hmodel).2.1
        (by omega)
    · exact (CFSG.LieType.Ree.large_Ree_large_even_field_central_two_cover_trivial θ hθ hθC h2
        hm hmodel).1
  rwa [hker] at hodd

end Main

end CFSG.RankThree.PartOne.KEXC
