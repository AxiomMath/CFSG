module

public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType

section Act

variable {G : Type} [Group G] {Bs K : Subgroup G} {z : G}

theorem p8dAct_ker_ggGamma (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z) :
    (ggGamma K hN).ker = (Subgroup.zpowers z).subgroupOf Bs := by
  ext b
  rw [MonoidHom.mem_ker, ggGamma_eq_one_iff, Subgroup.mem_subgroupOf, ← hker]
  exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩

theorem p8dAct_ker_ggBeta {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R)
    (hperf : commutator K = ⊤) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z) :
    (ggBeta K θ hN).ker = (Subgroup.zpowers z).subgroupOf Bs := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker]
  constructor
  · intro h
    exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one K θ hperf (g := ⟨b, hN b.2⟩) h⟩
  · rintro ⟨-, hc⟩
    exact ggLAut_eq_one_of_mem_centralizer K θ hc

theorem p8dAct_card_zpowers (hBs : IsElemAbelian 3 Bs) (hz : z ∈ Bs) (hz1 : z ≠ 1) :
    Nat.card ((Subgroup.zpowers z).subgroupOf Bs) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hz)).toEquiv,
    Nat.card_zpowers, orderOf_eq_prime (hBs.2 z hz) hz1]

theorem p8dAct_card_range_ggGamma (hBs : IsElemAbelian 3 Bs) (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z) :
    Nat.card (ggGamma K hN).range * 3 = Nat.card Bs := by
  have h1 := Subgroup.card_ker_mul_card_range (ggGamma K hN)
  rw [p8dAct_ker_ggGamma hN hker, p8dAct_card_zpowers hBs hz hz1] at h1
  rw [mul_comm]
  exact h1

theorem p8dAct_card_range_ggBeta {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R)
    (hperf : commutator K = ⊤) (hBs : IsElemAbelian 3 Bs) (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z) :
    Nat.card (ggBeta K θ hN).range * 3 = Nat.card Bs := by
  have h1 := Subgroup.card_ker_mul_card_range (ggBeta K θ hN)
  rw [p8dAct_ker_ggBeta θ hperf hN hker, p8dAct_card_zpowers hBs hz hz1] at h1
  rw [mul_comm]
  exact h1

theorem p8dAct_isElemAbelian_range_ggGamma (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) : IsElemAbelian 3 (ggGamma K hN).range :=
  isElemAbelian_range (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2))
    (fun a => Subtype.ext (by simpa using hBs.2 a a.2)) _

theorem p8dAct_isElemAbelian_range_ggBeta {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) : IsElemAbelian 3 (ggBeta K θ hN).range :=
  isElemAbelian_range (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2))
    (fun a => Subtype.ext (by simpa using hBs.2 a a.2)) _

theorem p8dAct_card_range_ggBeta_eq {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R)
    (hperf : commutator K = ⊤) (hBs : IsElemAbelian 3 Bs) (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z) :
    Nat.card (ggBeta K θ hN).range = Nat.card (ggGamma K hN).range :=
  Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3)
    ((p8dAct_card_range_ggBeta θ hperf hBs hz hz1 hN hker).trans
      (p8dAct_card_range_ggGamma hBs hz hz1 hN hker).symm)

end Act

end CFSG.StandardType.FrameRoute

end
