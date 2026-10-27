module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open SpCoord

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

@[expose] public def qMap {L : Subgroup G} (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    ↥L →* OrthRest.RPlus K 4 :=
  θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))

public theorem qMap_apply {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) (l : ↥L) :
    qMap (K := K) θ l = θ (QuotientGroup.mk' (Subgroup.center L) l) := rfl

public theorem qMap_ker {L : Subgroup G} (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    (qMap (K := K) θ).ker = Subgroup.center L := by
  ext l
  simp [qMap, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]

@[expose] public def EB (Bs L : Subgroup G) : Subgroup ↥Bs := (Bs ⊓ L).subgroupOf Bs

@[expose] public def EL (Bs L : Subgroup G) : Subgroup ↥L := (Bs ⊓ L).subgroupOf L

public theorem mem_EL {Bs L : Subgroup G} {l : ↥L} : l ∈ EL Bs L ↔ (l : G) ∈ Bs ⊓ L :=
  Subgroup.mem_subgroupOf

public theorem mem_EB {Bs L : Subgroup G} {b : ↥Bs} : b ∈ EB Bs L ↔ (b : G) ∈ Bs ⊓ L :=
  Subgroup.mem_subgroupOf

@[expose] public def Ebar (Bs L : Subgroup G) (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    Subgroup (OrthRest.RPlus K 4) :=
  (EL Bs L).map (qMap (K := K) θ)

public theorem mem_Ebar {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) {y : OrthRest.RPlus K 4} :
    y ∈ Ebar Bs L θ ↔ ∃ e : ↥L, e ∈ EL Bs L ∧ qMap (K := K) θ e = y :=
  Subgroup.mem_map

end CFSG.StandardType.E6QTwo

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open SpCoord

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

public theorem bstar_isComplement {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hxBs : x ∈ Bs) (hord : orderOf x = 3)
    (hExbot : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥) :
    Subgroup.IsComplement' (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs) := by
  classical
  haveI : IsMulCommutative ↥Bs := hBs.1
  have hEB : Nat.card ↥(EB Bs L) = 3 ^ 4 := by
    rw [← hcardE]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Bs ⊓ L ≤ Bs)).toEquiv
  have hXB : Nat.card ↥((Subgroup.zpowers x).subgroupOf Bs) = 3 := by
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxBs)).toEquiv, Nat.card_zpowers, hord]
  have hdisj : Disjoint (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs) := by
    rw [disjoint_iff, eq_bot_iff]
    intro y hy
    have hyE : (y : G) ∈ Bs ⊓ L := hy.1
    have hyX : (y : G) ∈ Subgroup.zpowers x := hy.2
    have hbot : (y : G) ∈ (Bs ⊓ L) ⊓ Subgroup.zpowers x := ⟨hyE, hyX⟩
    rw [hExbot] at hbot
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ hdisj
  rw [hEB, hXB, hcard]
  norm_num

end CFSG.StandardType.E6QTwo

end
