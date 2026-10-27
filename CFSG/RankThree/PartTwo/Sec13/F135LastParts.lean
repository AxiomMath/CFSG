module

public import CFSG.RankThree.PartTwo.Sec13.F135LastKDefs
public import CFSG.RankThree.PartTwo.Sec13.Item135CritProofA7
public import CFSG.RankThree.PartTwo.Sec13.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open CritProof
open scoped commutatorElement

@[expose] noncomputable def dOf {G : Type} [Group G] (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)) : Subgroup G :=
  (omegaOneCore p C).map L.subtype

@[expose] noncomputable def dPrime {G : Type} [Group G] (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)) (z : G) : Subgroup G :=
  ⁅dOf L p C, Subgroup.zpowers z⁆

@[expose] noncomputable def frattiniOf {G : Type} [Group G] (D : Subgroup G) : Subgroup G :=
  (frattini D).map D.subtype

structure Cfg0 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)) : Prop where
  data : Sec13Data G A c L
  hST : HypS A ∨ HypT A
  not_qs : ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L)
  pCore_two : CFSG.pCore 2 L = ⊥
  rank_two : CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2
  qs_odd : IsQuasisimple (L ⧸ CFSG.oddCore L)
  alt7 : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7))
  prod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7))
  autIn : Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4))
  c_not_mem : c ∉ L
  card_nine : Nat.card (A ⊓ L : Subgroup G) = 9
  w_disj : (Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∨
      ((Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
          Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∧
        Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) ∧
        (omegaA A).ncard = 3 ∧
        (∀ F ∈ omegaA A, ∃ w ∈ Subgroup.normalizer (A : Set G),
          F = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom) ∧
        ∃ t ∈ Subgroup.normalizer (A : Set G), t * c * t⁻¹ = c⁻¹ ∧
          ∃ (ht : t ∈ Subgroup.normalizer (L : Set G))
            (e : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7))
            (τ : Equiv.Perm (Fin 7)), τ.IsSwap ∧ ∀ y : L ⧸ aschbacherSolvableCore 3 L,
              ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨t, ht⟩) y) :
                  Equiv.Perm (Fin 7))) = τ * (e y : Equiv.Perm (Fin 7)) * τ⁻¹))
  crit : Crit135 L p C
  odd_alt7 : OddCoreAlt7 L (aschbacherSolvableCore 3 L)
  center_two : Nat.card (Subgroup.center (L ⧸ CFSG.oddCore L)) = 2


structure Cfg1 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)) extends Cfg0 G A c L p C where
  t : G
  t_mem_W : t ∈ Subgroup.normalizer (A : Set G)
  t_norm_L : t ∈ Subgroup.normalizer (L : Set G)
  t_two : ∃ n : ℕ, t ^ 2 ^ n = 1
  t_inv : t * c * t⁻¹ = c⁻¹

@[expose] def R0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)), Cfg0 G A c L p C → Nonempty (Cfg1 G A c L p C)

structure Cfg2 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)) extends Cfg1 G A c L p C where
  z : G
  u : G
  p_ge_seven : 7 ≤ p
  z_mem : z ∈ L
  u_sq : u * u = 1
  u_ne : u ≠ 1
  Dp_rank : 4 ≤ CFSG.pRank p (↥(dPrime L p C z) ⧸ frattini ↥(dPrime L p C z))
  Cu_rank : p ^ 2 ≤ (frattiniOf (dPrime L p C z)).relIndex
    ((dPrime L p C z ⊓ Subgroup.centralizer ({u} : Set G)) ⊔ frattiniOf (dPrime L p C z))

@[expose] def R1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)), Cfg1 G A c L p C → Nonempty (Cfg2 G A c L p C)

structure Cfg3 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)) extends Cfg2 G A c L p C where
  Y : Subgroup G
  U : Subgroup G
  Y_le : Y ≤ dPrime L p C z ⊓ Subgroup.centralizer ({u} : Set G)
  Y_card : Nat.card Y = p
  Y_not_frattini : ¬ Y ≤ frattiniOf (dPrime L p C z)
  U_eq : U = ⁅CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
      Subgroup.centralizer (Y : Set G),
    dPrime L p C z ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G)⁆
  U_ne : U ≠ ⊥

@[expose] def R2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)), Cfg2 G A c L p C → Nonempty (Cfg3 G A c L p C)

@[expose] abbrev cM {G : Type} [Group G] (Y : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (Y : Set G)

@[expose] noncomputable def eOf {G : Type} [Group G] (Dp Y : Subgroup G) : Subgroup (cM Y) :=
  (Dp ⊓ cM Y).subgroupOf (cM Y)

structure Cfg4 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)) extends Cfg3 G A c L p C where
  R : Subgroup (cM Y)
  [R_normal : R.Normal]
  R_eq : R.map (cM Y).subtype = CFSG.Open.relPPrimeCore p (cM Y)
  R_odd : Odd (Nat.card R)
  R_coprime : Nat.Coprime p (Nat.card R)
  J : Subgroup (cM Y ⧸ R)
  J_comp : CFSG.IsComponent J
  J_normE : ∀ e ∈ eOf (dPrime L p C z) Y, (e : cM Y ⧸ R) ∈ Subgroup.normalizer (J : Set (cM Y ⧸ R))
  J_normc : ∀ hc : c ∈ cM Y,
    ((⟨c, hc⟩ : cM Y) : cM Y ⧸ R) ∈ Subgroup.normalizer (J : Set (cM Y ⧸ R))
  J_U : ⁅J, (U.subgroupOf (cM Y)).map (QuotientGroup.mk' R)⁆ = J
  J_normU : (U.subgroupOf (cM Y)).map (QuotientGroup.mk' R) ≤ Subgroup.normalizer (J : Set (cM Y ⧸ R))
  J_normu : ∀ hu : u ∈ cM Y,
    ((⟨u, hu⟩ : cM Y) : cM Y ⧸ R) ∈ Subgroup.normalizer (J : Set (cM Y ⧸ R))

@[expose] def R3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)), Cfg3 G A c L p C → Nonempty (Cfg4 G A c L p C)

structure Cfg5 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)) extends Cfg4 G A c L p C where
  E_index : p ^ 3 ≤
    (Subgroup.centralizer (J : Set (cM Y ⧸ R)) ⊓
      (eOf (dPrime L p C z) Y).map (QuotientGroup.mk' R)).relIndex
      ((eOf (dPrime L p C z) Y).map (QuotientGroup.mk' R))
  U_nontrivial : ¬ (U.subgroupOf (cM Y)).map (QuotientGroup.mk' R) ≤
    Subgroup.centralizer (J : Set (cM Y ⧸ R))
  u_nontrivial : ∀ hu : u ∈ cM Y,
    ¬ (((⟨u, hu⟩ : cM Y) : cM Y ⧸ R) ∈ Subgroup.centralizer (J : Set (cM Y ⧸ R)))
  U_comm_Eu : (U.subgroupOf (cM Y)).map (QuotientGroup.mk' R) ≤
    ⁅(U.subgroupOf (cM Y)).map (QuotientGroup.mk' R),
      ((dPrime L p C z ⊓ cM Y ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf (cM Y)).map
        (QuotientGroup.mk' R)⁆ ⊔ Subgroup.centralizer (J : Set (cM Y ⧸ R))
  E_ker : Subgroup.centralizer (J : Set (cM Y ⧸ R)) ⊓
      (eOf (dPrime L p C z) Y).map (QuotientGroup.mk' R) ≤
    (Y.subgroupOf (cM Y)).map (QuotientGroup.mk' R)

@[expose] def R4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)), Cfg4 G A c L p C → Nonempty (Cfg5 G A c L p C)

@[expose] def R5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)) (c5 : Cfg5 G A c L p C),
    Identified p (↥c5.J ⧸ Subgroup.center ↥c5.J)

end CFSG.RankThree.PartTwo.Sec13.F135Last
