module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

@[expose] def tmRowOrders : ℕ → List ℕ
  | 7 => [
    300165342889299148800,
    10696127538423398400,
    14869942101658828800,
    6773326479360,
    11919092613120,
    225740390400,
    319548063744,
    14679168,
    429683151044011150540800,
    1377584634307947370905600,
    6348948480,
    ]
  | 8 => [
    911666827031785075278550369566720000,
    47984856252454798554602923576084817510400,
    1399224620066395285094400,
    1952839756326650668646400,
    72186769375393873290854400,
    99186093670172210705203200,
    399948801638400,
    749200107110400,
    1068879052800000,
    1068879052800000,
    364074101637120000,
    804130746531840000,
    267990900947288064,
    406814103856742400,
    38236520448,
    104485552128,
    31150080000,
    34233876480,
    4571242905600,
    576600,
    373403520,
    28800000,
    9930,
    48672,
    4530,
    72600,
    ]
  | _ => []

@[expose] def tmSurvivorOrder : ℕ → ℕ
  | 7 => 1377584634307947370905600
  | 8 => 99186093670172210705203200
  | _ => 0

@[expose] def LSS92MaxOvergroupInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), IsEm m (⊤ : Subgroup G) → IsSimpleGroup G →
    KProper InCatalog G → ∀ E : Subgroup G, IsElemAbelian 3 E → Nat.card E = 3 ^ m →
      ∀ H : Subgroup G, IsCoatom H → Subgroup.normalizer (E : Set G) < H →
        (∃ P : Subgroup G, P ≤ H ∧ (P.subgroupOf H).Normal ∧ IsPGroup 2 P ∧ P ≠ ⊥ ∧
            padicValNat 3 (Nat.card (H ⧸ P.subgroupOf H)) ≤ (if m = 7 then 8 else 11)) ∨
        (Nat.card H ∈ tmRowOrders m ∧
            (Nat.card H = tmSurvivorOrder m →
              ∃ Q : Subgroup G, Q ≤ H ∧ (Q.subgroupOf H).Normal ∧ Nat.card Q = 3)) ∨
        (∃ J : Subgroup G, J ≤ H ∧ (J.subgroupOf H).Normal ∧ IsSimpleGroup J ∧
            (∃ a b : J, a * b ≠ b * a) ∧ ∀ h ∈ H, (∀ j ∈ J, h * j = j * h) → h = 1)

end CFSG.StandardType.FrameRoute

end
