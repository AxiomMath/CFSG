module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

structure Ctx {G : Type} [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G)
    (t d x : G) : Prop where
  c : Counter T M g
  c18 : Concl14318 T M g A t
  c19 : Concl14319 T M A
  hΓ : Subgroup.centralizer (A : Set G) = A
  c21 : Concl14321 T M
  hD : dOf T M = Subgroup.zpowers d
  hd4 : orderOf d = 4
  hx : x ∈ yOfL22 T M
  hx3 : orderOf x = 3
  hSyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({wOfX d x} : Set G))
    (Subgroup.centralizer ({wOfX d x} : Set G))
  hN1 : ∀ y : G, y * (d * d) * y⁻¹ ≠ wOfX d x
  hN2 : ∃ s : G, s * wOfX d x * s⁻¹ = wOfX d x * (d * d)
  hR : IsZ4Sq ↥(rOf T M ⊓ Subgroup.centralizer ({wOfX d x} : Set G))
  hO : IsZ4StarSL23 ↥(oTwoUpper (mcOf T) ⊓ Subgroup.centralizer ({wOfX d x} : Set G))

abbrev Gw {G : Type} [Group G] (d x : G) : Subgroup G := Subgroup.centralizer ({wOfX d x} : Set G)

abbrev Cw {G : Type} [Group G] (T : Subgroup G) (d x : G) : Subgroup G := mcOf T ⊓ Gw d x

abbrev K0 {G : Type} [Group G] (T : Subgroup G) (d x : G) : Subgroup G :=
  oTwoUpper (mcOf T) ⊓ Gw d x

abbrev Tw {G : Type} [Group G] (T : Subgroup G) (d x : G) : Subgroup G := T ⊓ Gw d x

abbrev Bw {G : Type} [Group G] (T : Subgroup G) (d x : G) : Subgroup G :=
  Cw T d x ⊓ Subgroup.centralizer (K0 T d x : Set G)

structure Wp0 {G : Type} [Group G] [Finite G] (T : Subgroup G) (d x : G) : Prop where
  card_Tw : Nat.card ↥(Tw T d x) = 2 ^ 7
  card_Cw : Nat.card ↥(Cw T d x) = 384
  K0_normal : ((K0 T d x).subgroupOf (Cw T d x)).Normal
  K0_contains_z : ∀ N : Subgroup G, N ≤ K0 T d x → (N.subgroupOf (K0 T d x)).Normal → N ≠ ⊥ →
    d * d ∈ N
  Bw_pGroup : IsPGroup 2 ↥(Bw T d x)
  Bw_card : Nat.card ↥(Bw T d x) ∣ 16
  Bw_inf_Q : Bw T d x ⊓ qOf T ≤ Subgroup.zpowers (u0Of d x) ⊔ Subgroup.zpowers (wOfX d x)
  Bw_relIndex : (qOf T).relIndex (Bw T d x) ≤ 2
  Bw_invol : ∀ c ∈ Bw T d x, c * c = 1 → c ∈ qOf T

structure Wp1 {G : Type} [Group G] [Finite G] (T : Subgroup G) (d x : G) : Prop where
  z_not_mem_P : d * d ∉ pCoreOf 2 (Gw d x)
  P_inf_K0 : pCoreOf 2 (Gw d x) ⊓ K0 T d x = ⊥
  P_le_Bw : pCoreOf 2 (Gw d x) ≤ Bw T d x
  w_mem_P : Subgroup.zpowers (wOfX d x) ≤ pCoreOf 2 (Gw d x)
  P_inf_Q : pCoreOf 2 (Gw d x) ⊓ qOf T = Subgroup.zpowers (wOfX d x)
  card_P : Nat.card ↥(pCoreOf 2 (Gw d x)) ≤ 4
  P_invol : ∀ c ∈ pCoreOf 2 (Gw d x), c * c = 1 → c = 1 ∨ c = wOfX d x

structure LocalFacts {G : Type} [Group G] [Finite G] (T : Subgroup G) (d x : G) : Prop where
  wp0 : Wp0 T d x
  wp1 : Wp1 T d x

structure InspData (L : Type) [Group L] : Prop where
  quasisimple : CFSG.IsQuasisimple L
  data : ∃ (Gc : Type) (_ : Group Gc) (_ : Finite Gc) (ρ : Gc →* MulAut L) (ž : Gc)
    (Ŝ Kh : Subgroup Gc), InspInput ρ ž Ŝ Kh ∧
      (ListCasesCD L ∨
        (Insp7.ListCases L ∧ ∃ l : L, l * l ∈ Subgroup.center L ∧ ρ ž = MulAut.conj l))

@[expose] def Clause4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t d x : G),
    Ctx T M g A t d x → ∀ L : Subgroup G, IsComponentIn L (Gw d x) →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 3 1 →
        T ⊓ Gw d x ⊓ (rOf T M ⊔ qOf T) ≤ Subgroup.zpowers (wOfX d x) ⊔ L

end InspW2

end S143

end CFSG.Quasithin
