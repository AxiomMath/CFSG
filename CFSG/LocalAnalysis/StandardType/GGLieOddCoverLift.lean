module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftBasic

public section

namespace CFSG.StandardType.LieOddCover


theorem ggOddCover_lift {U J : Type} [Group U] [Group J] [Finite U] [Finite J]
    (hsplit : CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit U) (hperf : commutator J = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center J))) {q : U →* J ⧸ Subgroup.center J}
    (hq : Function.Surjective q) (hqk : q.ker ≤ Subgroup.center U) :
    ∃ φ : U →* J, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center U := by
  have hc : Nat.Coprime 2 (Nat.card (Subgroup.center J)) := Nat.coprime_two_left.mpr hodd
  obtain ⟨α, hα, hαs⟩ := CFSG.StandardType.StdSubRestU.exists_surjective_of_oddKernel hq
    (fun E _ _ π hπ hcen hcop => hsplit E π hπ hcen (Nat.coprime_two_left.mp hcop))
    (QuotientGroup.mk'_surjective (Subgroup.center J)) (by rw [QuotientGroup.ker_mk']) hperf
    (fun y hy hy2 => by
      rw [QuotientGroup.ker_mk'] at hy
      have h1 : orderOf (⟨y, hy⟩ : Subgroup.center J) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hy2))
      have h2 : orderOf (⟨y, hy⟩ : Subgroup.center J) ∣ Nat.card (Subgroup.center J) :=
        orderOf_dvd_natCard _
      have h3 : orderOf (⟨y, hy⟩ : Subgroup.center J) = 1 :=
        Nat.dvd_one.mp (Nat.Coprime.gcd_eq_one hc ▸ Nat.dvd_gcd h1 h2)
      simpa using congrArg Subtype.val (orderOf_eq_one_iff.mp h3))
  refine ⟨α, hαs, fun u hu => hqk ?_⟩
  rw [MonoidHom.mem_ker] at hu ⊢
  rw [← hα u, hu, map_one]

end CFSG.StandardType.LieOddCover
