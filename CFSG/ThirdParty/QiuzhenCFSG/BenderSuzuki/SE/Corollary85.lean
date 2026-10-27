module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary85Field
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

namespace CFSG
end CFSG
open CFSG

/-!
# Corollary 8.5

This file isolates the three model-automorphism inputs cited in the source as
`[II4; 3.2(b,f,g)]` and proves all remaining deductions from the completed
`Proposition84Statement` interface.  In particular, the normality of
`F = O^{2'}(C_X(Y))`, the equality `N_I(Y) = C_I(Y)`, and faithfulness of the
conjugation action of `P` on `F` are checked here.

The source phrase that `P` induces nontrivial field automorphisms is represented
operationally by the exponent-linked Bender model together with the checked
faithful conjugation action.  No separate abstract notion of a field
automorphism of an arbitrary recognized quotient exists on the current import
surface.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1 PFchapter1section2
open scoped Pointwise

universe u

/-- The exact Proposition 8.4 fields used by Corollary 8.5. -/
public structure Corollary85Proposition84Data
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u0 : X) (Y : Subgroup X) where
  n : ℕ
  J : Subgroup X
  two_le_n : 2 ≤ n
  normalizer_eq_mul :
    ((Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X) =
      (centralizerTwoPrimeResidual Y : Set X) *
        (normalizerIn
          ((M ⊓ rightConjugate M t) ⊓
            Subgroup.centralizer ({u0} : Set X)) Y : Set X)
  J_eq_normalizer :
    (J : Set X) =
      {x : X | x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
        x ∈ Subgroup.normalizer (Y : Set X)}
  J_le_residual : J ≤ centralizerTwoPrimeResidual Y
  J_cyclic : IsCyclic J
  J_card : Nat.card J = 2 ^ n - 1
  oddCore_eq_center :
    twoPrimeCore (centralizerTwoPrimeResidual Y) =
      Subgroup.center (centralizerTwoPrimeResidual Y)
  model : IsSimpleBenderGroupAtExponent n
    (centralizerTwoPrimeResidual Y ⧸
      twoPrimeCore (centralizerTwoPrimeResidual Y))

/-- The source hypothesis `C_{N_I(Y)}(g) = 1` for every `1 ≠ g ∈ P`, written
without choosing the Proposition 8.4 subgroup `J`. -/
@[expose] public def Corollary85FixedPointFree
    {X : Type u} [Group X]
    (D : Subgroup X) (t : X) (Y P : Subgroup X) : Prop :=
  ∀ g : X, g ∈ P → g ≠ 1 →
    ∀ j : X, j ∈ peterfalviKSet D t →
      j ∈ Subgroup.normalizer (Y : Set X) →
      j * g = g * j → j = 1

/-- Proof-support data from the local field calculation in Corollary 8.5.

This package deliberately stays separate from `Corollary85Conclusion`: the
numbered corollary does not state a choice of Sylow subgroup or root subgroup,
but Lemma 11.4 needs the particular subgroups already constructed in its
proof. -/
public structure Corollary85FixedRootData
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u0 : X) (Y P : Subgroup X) where
  S : Subgroup X
  S_le_normalizer : S ≤ normalizerIn M Y
  S_le_residual : S ≤ centralizerTwoPrimeResidual Y
  S_le_M : S ≤ M
  S_normal : (S.subgroupOf (normalizerIn M Y)).Normal
  S_sylow :
    ∃ PSyl : Sylow 2 ↥(centralizerTwoPrimeResidual Y ⊓ M),
      S = (PSyl : Subgroup ↥(centralizerTwoPrimeResidual Y ⊓ M)).map
        (centralizerTwoPrimeResidual Y ⊓ M).subtype
  S_isPGroup : IsPGroup 2 S
  S_regular :
    IsRegularOn S
      {omega : conjugateCosetSpace M |
        omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y ∧
          omega ≠ QuotientGroup.mk 1}
  J : Subgroup X
  J_le_residual : J ≤ centralizerTwoPrimeResidual Y
  J_eq_normalizer :
    (J : Set X) =
      {x : X | x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
        x ∈ Subgroup.normalizer (Y : Set X)}
  J_card : Nat.card J = 2 ^ Nat.card P - 1
  normalizerIn_eq_mul :
    (normalizerIn M Y : Set X) =
      (S : Set X) *
        (normalizerIn (M ⊓ rightConjugate M t) Y : Set X)
  Q0 : Subgroup (Subgroup.normalizer (Y : Set X))
  Q0_le_S :
    Q0 ≤ S.subgroupOf (Subgroup.normalizer (Y : Set X))
  Q0_def : ∀ x : Subgroup.normalizer (Y : Set X),
    x ∈ Q0 ↔
      x = 1 ∨
        (x ∈ (normalizerIn M Y).subgroupOf
          (Subgroup.normalizer (Y : Set X)) ∧ IsInvolution x)
  Q0_commutative : IsMulCommutative Q0
  Q0_sq : ∀ x : Q0, x ^ 2 = 1
  P_le_normalizer : P ≤ Subgroup.normalizer (Y : Set X)
  Q0_card : Nat.card Q0 = 2 ^ Nat.card P
  fixed_Q0_card :
    Nat.card
      (Q0 ⊓ Subgroup.centralizer
        ((P.subgroupOf (Subgroup.normalizer (Y : Set X))) :
          Set (Subgroup.normalizer (Y : Set X))) :
        Subgroup (Subgroup.normalizer (Y : Set X))) = 2

/-- The three model-automorphism outputs used by Corollary 8.5. -/
public structure Corollary85II4Endpoints
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u0 : X) (Y P : Subgroup X)
    (d : Corollary85Proposition84Data M t u0 Y) : Prop where
  card_P_prime : Nat.Prime (Nat.card P)
  exponent_eq_card_P : d.n = Nat.card P
  local_factorization :
    (normalizerIn
      ((M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({u0} : Set X)) Y : Set X) =
      ((normalizerIn
          ((M ⊓ rightConjugate M t) ⊓
            Subgroup.centralizer ({u0} : Set X)) Y ⊓
        Subgroup.centralizer (d.J : Set X) : Subgroup X) : Set X) *
        (P : Set X)
  fixedRoot : Nonempty (Corollary85FixedRootData M t u0 Y P)

/-- The operational formalization of Corollary 8.5(a)--(c). -/
public structure Corollary85Conclusion
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u0 : X) (Y P : Subgroup X) where
  J : Subgroup X
  card_P_prime : Nat.Prime (Nat.card P)
  residual_normal_in_normalizer :
    ((centralizerTwoPrimeResidual Y).subgroupOf
      (Subgroup.normalizer (Y : Set X))).Normal
  normalizer_eq_mul :
    ((Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X) =
      (centralizerTwoPrimeResidual Y : Set X) *
        (normalizerIn
          ((M ⊓ rightConjugate M t) ⊓
            Subgroup.centralizer ({u0} : Set X)) Y : Set X)
  oddCore_eq_center :
    twoPrimeCore (centralizerTwoPrimeResidual Y) =
      Subgroup.center (centralizerTwoPrimeResidual Y)
  model : IsSimpleBenderGroupAtExponent (Nat.card P)
    (centralizerTwoPrimeResidual Y ⧸
      twoPrimeCore (centralizerTwoPrimeResidual Y))
  P_normalizes_residual :
    P ≤ Subgroup.normalizer (centralizerTwoPrimeResidual Y : Set X)
  P_faithful_on_residual :
    P ⊓ Subgroup.centralizer (centralizerTwoPrimeResidual Y : Set X) = ⊥
  J_eq_normalizer :
    (J : Set X) =
      {x : X | x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
        x ∈ Subgroup.normalizer (Y : Set X)}
  J_eq_centralizer :
    (J : Set X) =
      {x : X | x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
        x ∈ Subgroup.centralizer (Y : Set X)}
  J_cyclic : IsCyclic J
  J_card : Nat.card J = 2 ^ Nat.card P - 1
  normalizer_involutions_card :
    Nat.card {z : normalizerIn M Y | IsInvolution (z : X)} =
      2 ^ Nat.card P - 1
  local_normalizer_eq_mul_centralizer :
    (normalizerIn
      ((M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({u0} : Set X)) Y : Set X) =
      ((normalizerIn
          ((M ⊓ rightConjugate M t) ⊓
            Subgroup.centralizer ({u0} : Set X)) Y ⊓
        Subgroup.centralizer (J : Set X) : Subgroup X) : Set X) *
        (P : Set X)

/-- Corollary 8.5 together with the proof-support Sylow/root data retained for
Lemma 11.4. -/
public structure Corollary85SupportedConclusion
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u0 : X) (Y P : Subgroup X) where
  conclusion : Corollary85Conclusion M t u0 Y P
  fixedRoot : Corollary85FixedRootData M t u0 Y P

namespace Proposition84Statement

/-- Extract the exact Corollary 8.5 fields from Proposition 8.4. -/
public theorem exists_corollary85_data
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t u0 : X}
    (h84 : Proposition84Statement M t u0)
    {Y : Subgroup X}
    (hYV : Y ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({u0} : Set X))
    (hYne : Y ≠ ⊥)
    (hI : HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t Y) :
    Nonempty (Corollary85Proposition84Data M t u0 Y) := by
  have hsubnormal : (Y.subgroupOf Y).IsSubnormal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.IsSubnormal.top
  obtain ⟨hAB, hCD⟩ :=
    h84 Y Y hYV hYne le_rfl hsubnormal hI
  have hCD' := hCD hI
  dsimp [Proposition84ABConclusion] at hAB
  dsimp [Proposition84CDConclusion] at hCD'
  rcases hCD' with
    ⟨n, J, hn, hJset, hJF, hJcyclic, hJcard, hcore, hmodel⟩
  exact ⟨{
    n := n
    J := J
    two_le_n := hn
    normalizer_eq_mul := hAB.2.1
    J_eq_normalizer := hJset
    J_le_residual := hJF
    J_cyclic := hJcyclic
    J_card := hJcard
    oddCore_eq_center := hcore
    model := hmodel }⟩

end Proposition84Statement

/-- Checked assembly of Corollary 8.5 from the Proposition 8.4 fields and the
three cited `[II4]` endpoints. -/
public theorem corollary85Conclusion_of_data
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t u0 : X} {Y P : Subgroup X}
    (d : Corollary85Proposition84Data M t u0 Y)
    (hI : HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t Y)
    (hPV : P ≤ normalizerIn
      ((M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({u0} : Set X)) Y)
    (hfixed : Corollary85FixedPointFree
      (M ⊓ rightConjugate M t) t Y P)
    (hcount :
      Nat.card {z : normalizerIn M Y | IsInvolution (z : X)} = Nat.card d.J)
    (hII4 : Corollary85II4Endpoints M t u0 Y P d) :
    Nonempty (Corollary85Conclusion M t u0 Y P) := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let F : Subgroup X := centralizerTwoPrimeResidual Y
  let N : Subgroup X := Subgroup.normalizer (Y : Set X)
  have hFC : F ≤ Subgroup.centralizer (Y : Set X) := by
    simpa [F] using centralizerTwoPrimeResidual_le_ambientCentralizer Y
  have hFleN : F ≤ N := by
    exact hFC.trans (centralizer_le_normalizer Y)
  have hFnormal : (F.subgroupOf N).Normal := by
    simpa [F, N] using centralizerTwoPrimeResidual_normal_in_normalizer Y
  letI : (F.subgroupOf N).Normal := hFnormal
  have hNnormF : N ≤ Subgroup.normalizer (F : Set X) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hFleN
  have hP_N : P ≤ N := by
    exact hPV.trans inf_le_right
  have hPnormF : P ≤ Subgroup.normalizer (F : Set X) :=
    hP_N.trans hNnormF
  have hJcentralizer :
      (d.J : Set X) =
        {x : X | x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (Y : Set X)} := by
    ext x
    constructor
    · intro hxJ
      have hxN' :
          x ∈ {x : X |
            x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
              x ∈ Subgroup.normalizer (Y : Set X)} := by
        rw [← d.J_eq_normalizer]
        exact hxJ
      have hxN : x ∈ peterfalviKSet D t ∧ x ∈ N := by
        simpa [D, N] using hxN'
      exact ⟨hxN.1, hFC (d.J_le_residual hxJ)⟩
    · rintro ⟨hxI, hxC⟩
      rw [d.J_eq_normalizer]
      exact ⟨hxI, centralizer_le_normalizer Y hxC⟩
  have hfaithful :
      P ⊓ Subgroup.centralizer (F : Set X) = ⊥ := by
    apply le_antisymm
    · intro g hg
      rw [Subgroup.mem_bot]
      by_contra hgOne
      obtain ⟨j, hjI, hjN, hjOne⟩ := hI
      have hjJ : j ∈ d.J := by
        show j ∈ (d.J : Set X)
        rw [d.J_eq_normalizer]
        exact ⟨hjI, hjN⟩
      have hgj : j * g = g * j :=
        (Subgroup.mem_centralizer_iff.mp hg.2) j
          (d.J_le_residual hjJ)
      exact hjOne (hfixed g hg.1 hgOne j hjI hjN hgj)
    · exact bot_le
  have hJcard : Nat.card d.J = 2 ^ Nat.card P - 1 := by
    simpa [hII4.exponent_eq_card_P] using d.J_card
  have hmodel : IsSimpleBenderGroupAtExponent (Nat.card P)
      (F ⧸ twoPrimeCore F) := by
    simpa [F, hII4.exponent_eq_card_P] using d.model
  have hinvolutions :
      Nat.card {z : normalizerIn M Y | IsInvolution (z : X)} =
        2 ^ Nat.card P - 1 :=
    hcount.trans hJcard
  exact ⟨{
    J := d.J
    card_P_prime := hII4.card_P_prime
    residual_normal_in_normalizer := by simpa [F, N] using hFnormal
    normalizer_eq_mul := d.normalizer_eq_mul
    oddCore_eq_center := d.oddCore_eq_center
    model := by simpa [F] using hmodel
    P_normalizes_residual := by simpa [F] using hPnormF
    P_faithful_on_residual := by simpa [F] using hfaithful
    J_eq_normalizer := d.J_eq_normalizer
    J_eq_centralizer := by simpa [D] using hJcentralizer
    J_cyclic := d.J_cyclic
    J_card := hJcard
    normalizer_involutions_card := hinvolutions
    local_normalizer_eq_mul_centralizer := hII4.local_factorization }⟩

/- The Peterfalvi semilinear field model proves all `[II4]` endpoints needed
by Corollary 8.5 from the Proposition 8.4 local action. -/
set_option maxHeartbeats 1600000 in
public theorem Proposition84Statement.corollary85_II4
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    {Y P : Subgroup X}
    (hYV : Y ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({d83.u} : Set X))
    (hYne : Y ≠ ⊥)
    (d : Corollary85Proposition84Data M t d83.u Y)
    (hI : HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t Y)
    (hPV : P ≤ normalizerIn
      ((M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X)) Y)
    (hfixed : Corollary85FixedPointFree
      (M ⊓ rightConjugate M t) t Y P)
    (hPne : P ≠ ⊥) :
    Corollary85II4Endpoints M t d83.u Y P d := by
  classical
  let D0 : Subgroup X := M ⊓ rightConjugate M t
  let V0 : Subgroup X := D0 ⊓ Subgroup.centralizer ({d83.u} : Set X)
  let N : Subgroup X := Subgroup.normalizer (Y : Set X)
  let H0 : Subgroup X := normalizerIn M Y
  let D1 : Subgroup X := normalizerIn D0 Y
  let V1 : Subgroup X := normalizerIn V0 Y
  have hsubnormal : (Y.subgroupOf Y).IsSubnormal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.IsSubnormal.top
  obtain ⟨hAB, _hCD⟩ :=
    h84 Y Y hYV hYne le_rfl hsubnormal hI
  dsimp [Proposition84ABConclusion] at hAB
  rcases hAB with
    ⟨htwo, _hNormalizer, S, hSle, hSnormal, hSsylow,
      hSregular, hSfactor⟩
  have hYDt : Y ≤ D0 ⊓ Subgroup.centralizer ({t} : Set X) := by
    rw [d83.centralizer_eq]
    exact hYV
  have htN : t ∈ N := by
    apply centralizer_le_normalizer Y
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYDt hy).2
  have hFleN : centralizerTwoPrimeResidual Y ≤ N :=
    (centralizerTwoPrimeResidual_le_ambientCentralizer Y).trans
      (centralizer_le_normalizer Y)
  obtain ⟨PSyl, hSdef⟩ := hSsylow
  have hSp : IsPGroup 2 S := by
    rw [hSdef]
    exact PSyl.isPGroup'.map
      (centralizerTwoPrimeResidual Y ⊓ M).subtype
  have huC : d83.u ∈ Subgroup.centralizer (Y : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYV hy).2
  have huF : d83.u ∈ centralizerTwoPrimeResidual Y :=
    (zpowers_le_centralizerTwoPrimeResidual_of_isInvolution
      Y d83.u_involution huC) (Subgroup.mem_zpowers d83.u)
  have huFM : d83.u ∈ centralizerTwoPrimeResidual Y ⊓ M :=
    ⟨huF, d83.u_mem_M⟩
  have htwoAmbient : 2 ∣
      Nat.card ↥(centralizerTwoPrimeResidual Y ⊓ M) := by
    have hzle : Subgroup.zpowers
        (⟨d83.u, huFM⟩ : ↥(centralizerTwoPrimeResidual Y ⊓ M)) ≤ ⊤ := le_top
    have hzcard : Nat.card (Subgroup.zpowers
        (⟨d83.u, huFM⟩ : ↥(centralizerTwoPrimeResidual Y ⊓ M))) = 2 := by
      rw [Nat.card_zpowers]
      exact (orderOf_eq_prime_iff).2
        ⟨(IsInvolution.subtype d83.u_involution huFM).sq_eq_one,
          (IsInvolution.subtype d83.u_involution huFM).ne_one⟩
    rw [← hzcard]
    simpa only [Subgroup.card_top] using Subgroup.card_dvd_of_le hzle
  have htwoPSyl : 2 ∣ Nat.card
      (PSyl : Subgroup ↥(centralizerTwoPrimeResidual Y ⊓ M)) :=
    Sylow.dvd_card_of_dvd_card PSyl htwoAmbient
  have hmapCard :
      Nat.card ((PSyl : Subgroup ↥(centralizerTwoPrimeResidual Y ⊓ M)).map
        (centralizerTwoPrimeResidual Y ⊓ M).subtype) =
        Nat.card (PSyl : Subgroup ↥(centralizerTwoPrimeResidual Y ⊓ M)) :=
    Subgroup.card_map_of_injective
      (centralizerTwoPrimeResidual Y ⊓ M).subtype_injective
  have hSeven : Even (Nat.card S) := by
    rw [hSdef, hmapCard]
    exact even_iff_two_dvd.mpr htwoPSyl
  let tn : N := ⟨t, htN⟩
  let H : Subgroup N := H0.subgroupOf N
  let D : Subgroup N := D1.subgroupOf N
  let Q : Subgroup N := S.subgroupOf N
  let OmegaY := {omega : conjugateCosetSpace M //
    omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y}
  letI : MulAction N OmegaY :=
    normalizerFixedPointAction X (conjugateCosetSpace M) Y
  have hA1 : HypothesisA1 N OmegaY H D Q tn := by
    simpa [N, D0, H0, D1, tn, H, D, Q, OmegaY] using
      normalizer_fixedPoint_hypothesisA1 M Y
        (centralizerTwoPrimeResidual Y) S t htN hM ht htM hYDt
          hFleN htwo hSle hSnormal hSp hSeven hSfactor
  have hQp : IsPGroup 2 Q := by
    exact hSp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (hSle.trans inf_le_right)).symm
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQnil : Group.IsNilpotent Q := IsPGroup.isNilpotent hQp
  obtain ⟨Q0, hQ0Q, hQ0def, hQ0comm, hQ0sq⟩ :=
    proposition_1_c_exists_Q0_of_hypothesisA1 H D Q tn hA1 hQnil
  have hJleN : d.J ≤ N := by
    intro j hj
    have hj' : j ∈ {x : X |
        x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
          x ∈ Subgroup.normalizer (Y : Set X)} := by
      rw [← d.J_eq_normalizer]
      exact hj
    exact hj'.2
  let K : Subgroup N := d.J.subgroupOf N
  let V : Subgroup N := V1.subgroupOf N
  let W1 : Subgroup X := V1 ⊓ Subgroup.centralizer (d.J : Set X)
  let W : Subgroup N := W1.subgroupOf N
  have hKdef : ∀ x : N,
      x ∈ K ↔ x ∈ D ∧ rightConjugateElem x tn = x⁻¹ := by
    intro x
    have hJmem : (x : X) ∈ d.J ↔
        (x : X) ∈ peterfalviKSet D0 t ∧ (x : X) ∈ N := by
      change (x : X) ∈ (d.J : Set X) ↔ _
      rw [d.J_eq_normalizer]
      rfl
    change (x : X) ∈ d.J ↔ x ∈ D ∧ rightConjugateElem x tn = x⁻¹
    rw [hJmem]
    constructor
    · rintro ⟨hxI, hxN⟩
      refine ⟨?_, ?_⟩
      · change (x : X) ∈ D1
        exact ⟨hxI.1, hxN⟩
      · apply Subtype.ext
        simpa [tn, rightConjugateElem] using hxI.2
    · rintro ⟨hxD, hxanti⟩
      have hxD1 : (x : X) ∈ D1 := hxD
      refine ⟨⟨hxD1.1, ?_⟩, x.property⟩
      simpa [tn, rightConjugateElem] using congrArg Subtype.val hxanti
  have hKleD : K ≤ D := fun x hx => (hKdef x).mp hx |>.1
  have hKcyclic : IsCyclic K := by
    exact (Subgroup.subgroupOfEquivOfLe hJleN).isCyclic.mpr d.J_cyclic
  have hKnormal : (K.subgroupOf D).Normal := by
    have hclosure_eq :
        K.subgroupOf D = Subgroup.closure
          {x : D | rightConjugateElem (x : N) tn = (x : N)⁻¹} := by
      apply le_antisymm
      · intro x hx
        apply Subgroup.subset_closure
        exact ((hKdef (x : N)).mp hx).2
      · rw [Subgroup.closure_le]
        intro x hx
        exact (hKdef (x : N)).mpr ⟨x.property, hx⟩
    have hclosure_normal :
        (Subgroup.closure
          {x : D | rightConjugateElem (x : N) tn = (x : N)⁻¹}).Normal := by
      simpa using PFchapter1section1.lemma_b tn D hA1.involution_t hA1.D_odd
        (hypothesisA1_t_mem_normalizer_D H D Q tn hA1)
    rw [hclosure_eq]
    exact hclosure_normal
  have hVeq : V = peterfalviV D tn := by
    have hVtV0 : D0 ⊓ Subgroup.centralizer ({t} : Set X) = V0 := by
      simpa [D0, V0] using d83.centralizer_eq
    ext x
    constructor
    · intro hx
      have hxV1 : (x : X) ∈ V1 := hx
      have hxVt : (x : X) ∈ D0 ⊓ Subgroup.centralizer ({t} : Set X) := by
        rw [hVtV0]
        exact hxV1.1
      refine ⟨?_, ?_⟩
      · change (x : X) ∈ D1
        exact ⟨hxVt.1, hxV1.2⟩
      · apply Subgroup.mem_centralizer_singleton_iff.mpr
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp hxVt.2
    · rintro ⟨hxD, hxC⟩
      have hxD1 : (x : X) ∈ D1 := hxD
      have hxCX : (x : X) ∈ Subgroup.centralizer ({t} : Set X) := by
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact congrArg Subtype.val
          (Subgroup.mem_centralizer_singleton_iff.mp hxC)
      have hxV0 : (x : X) ∈ V0 := by
        rw [← hVtV0]
        exact ⟨hxD1.1, hxCX⟩
      exact ⟨hxV0, hxD1.2⟩
  have hVleD : V ≤ D := by
    rw [hVeq]
    exact inf_le_left
  have hWleV : W ≤ V := by
    intro x hx
    exact hx.1
  have hWeq : W = peterfalviW V (K : Set N) := by
    ext x
    constructor
    · intro hx
      have hxW1 : (x : X) ∈ W1 := hx
      refine ⟨hxW1.1, ?_⟩
      apply Subgroup.mem_centralizer_iff.mpr
      intro k hk
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hxW1.2) (k : X) hk
    · rintro ⟨hxV, hxC⟩
      refine ⟨hxV, ?_⟩
      apply Subgroup.mem_centralizer_iff.mpr
      intro k hk
      let kN : N := ⟨k, hJleN hk⟩
      have hkK : kN ∈ K := hk
      exact congrArg Subtype.val
        ((Subgroup.mem_centralizer_iff.mp hxC) kN hkK)
  let hsec : Proposition3FieldModelA1Data (Ω := OmegaY)
      H D Q K V W Q0 tn :=
    { hA1 := hA1
      K_le_D := hKleD
      K_def := hKdef
      V_eq := hVeq
      V_le_D := hVleD
      W_le_V := hWleV
      W_eq := hWeq
      Q0_def := hQ0def
      K_cyclic := hKcyclic
      K_normal_D := hKnormal
      Q0_commutative := hQ0comm
      Q0_sq := hQ0sq }
  have hPleN : P ≤ N := hPV.trans inf_le_right
  let Plocal : Subgroup N := P.subgroupOf N
  have hPlocal_ne : Plocal ≠ ⊥ := by
    obtain ⟨p, hpOne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    let pN : N := ⟨(p : X), hPleN p.property⟩
    refine ⟨⟨pN, p.property⟩, ?_⟩
    intro hp
    apply hpOne
    apply Subtype.ext
    simpa [pN] using congrArg (fun z : Plocal => ((z : N) : X)) hp
  have hKne : K ≠ ⊥ := by
    obtain ⟨k, hkI, hkN, hkOne⟩ := hI
    have hkJ : k ∈ d.J := by
      have hmem := congrArg (fun s : Set X => k ∈ s) d.J_eq_normalizer
      exact (Iff.of_eq hmem).mpr ⟨hkI, hkN⟩
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    let kN : N := ⟨k, hkN⟩
    refine ⟨⟨kN, hkJ⟩, ?_⟩
    intro hk
    apply hkOne
    exact congrArg Subtype.val (congrArg Subtype.val hk)
  have hfixedLocal : ∀ p : N, p ∈ Plocal → p ≠ 1 →
      ∀ k : N, k ∈ K → k * p = p * k → k = 1 := by
    intro p hpP hpOne k hkK hcomm
    have hpOneX : (p : X) ≠ 1 := by
      intro hp
      exact hpOne (Subtype.ext hp)
    have hkJ : (k : X) ∈ d.J := hkK
    have hkI : (k : X) ∈ peterfalviKSet D0 t ∧ (k : X) ∈ N := by
      have hk' : (k : X) ∈ {x : X |
          x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
            x ∈ Subgroup.normalizer (Y : Set X)} := by
        rw [← d.J_eq_normalizer]
        exact hkJ
      simpa [D0, N] using hk'
    apply Subtype.ext
    exact hfixed (p : X) hpP hpOneX (k : X) hkI.1 hkI.2
      (congrArg Subtype.val hcomm)
  obtain ⟨hPprime, hKcard, hVfactor, hQ0card, hfixedQ0Card⟩ :=
    corollary85_fixedField_endpoints H D Q K V W Q0 tn hsec
      Plocal (by
        intro p hp
        exact hPV hp) hPlocal_ne hKne hfixedLocal
  have hPcard : Nat.card Plocal = Nat.card P :=
    natCard_subgroupOf_eq P N hPleN
  have hKcardAmbient : Nat.card K = Nat.card d.J :=
    natCard_subgroupOf_eq d.J N hJleN
  have hn : d.n = Nat.card P := by
    have hsub : 2 ^ d.n - 1 = 2 ^ Nat.card P - 1 := by
      calc
        2 ^ d.n - 1 = Nat.card d.J := d.J_card.symm
        _ = Nat.card K := hKcardAmbient.symm
        _ = 2 ^ Nat.card Plocal - 1 := hKcard
        _ = 2 ^ Nat.card P - 1 := by rw [hPcard]
    have hleft : 1 ≤ 2 ^ d.n := Nat.one_le_two_pow
    have hright : 1 ≤ 2 ^ Nat.card P := Nat.one_le_two_pow
    have hpow : 2 ^ d.n = 2 ^ Nat.card P := by omega
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  refine
    { card_P_prime := ?_
      exponent_eq_card_P := hn
      local_factorization := ?_
      fixedRoot := ?_ }
  · simpa [hPcard] using hPprime
  · apply Set.Subset.antisymm
    · intro x hx
      let xN : N := ⟨x, hx.2⟩
      have hxV : xN ∈ V := hx
      have hxProduct : xN ∈ (W : Set N) * (Plocal : Set N) := by
        rw [← hVfactor]
        exact hxV
      rw [Set.mem_mul] at hxProduct ⊢
      rcases hxProduct with ⟨w, hw, p, hp, hwp⟩
      refine ⟨(w : X), hw, (p : X), hp, ?_⟩
      exact congrArg Subtype.val hwp
    · intro x hx
      rw [Set.mem_mul] at hx
      rcases hx with ⟨w, hw, p, hp, rfl⟩
      exact V1.mul_mem hw.1 (hPV hp)
  · exact ⟨{
        S := S
        S_le_normalizer := hSle
        S_le_residual := by
          rw [hSdef]
          rintro _ ⟨s, _hs, rfl⟩
          exact s.property.1
        S_le_M := by
          rw [hSdef]
          rintro _ ⟨s, _hs, rfl⟩
          exact s.property.2
        S_normal := hSnormal
        S_sylow := ⟨PSyl, hSdef⟩
        S_isPGroup := hSp
        S_regular := hSregular
        J := d.J
        J_le_residual := d.J_le_residual
        J_eq_normalizer := d.J_eq_normalizer
        J_card := by simpa [hn] using d.J_card
        normalizerIn_eq_mul := hSfactor
        Q0 := Q0
        Q0_le_S := by simpa [Q, N] using hQ0Q
        Q0_def := by simpa [H, H0, N] using hQ0def
        Q0_commutative := hQ0comm
        Q0_sq := hQ0sq
        P_le_normalizer := by simpa [N] using hPleN
        Q0_card := by simpa [hPcard] using hQ0card
        fixed_Q0_card := by simpa [Plocal, N] using hfixedQ0Card }⟩

/-- Corollary 8.5 together with the Sylow/root data constructed by its local
field-model proof. -/
public theorem Proposition84Statement.corollary85_supported
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    {Y P : Subgroup X}
    (hYV : Y ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({d83.u} : Set X))
    (hYne : Y ≠ ⊥)
    (hI : HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t Y)
    (hPV : P ≤ normalizerIn
      ((M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X)) Y)
    (hPne : P ≠ ⊥)
    (hfixed : Corollary85FixedPointFree
      (M ⊓ rightConjugate M t) t Y P) :
    Nonempty (Corollary85SupportedConclusion M t d83.u Y P) := by
  obtain ⟨d⟩ := h84.exists_corollary85_data hYV hYne hI
  have hcount := h84.normalizerIn_involutions_card_eq
    d83 hM ht htM hYV hYne hI d.J d.J_eq_normalizer
  let hII4 := Proposition84Statement.corollary85_II4
    d83 h84 hM ht htM hYV hYne d hI hPV hfixed hPne
  obtain ⟨conclusion⟩ :=
    corollary85Conclusion_of_data d hI hPV hfixed hcount hII4
  obtain ⟨fixedRoot⟩ := hII4.fixedRoot
  exact ⟨{
    conclusion := conclusion
    fixedRoot := fixedRoot }⟩

/-- Corollary 8.5, with the Peterfalvi field-model endpoints and involution
count derived from Proposition 8.4. -/
public theorem Proposition84Statement.corollary85
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    {Y P : Subgroup X}
    (hYV : Y ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({d83.u} : Set X))
    (hYne : Y ≠ ⊥)
    (hI : HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t Y)
    (hPV : P ≤ normalizerIn
      ((M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X)) Y)
    (hPne : P ≠ ⊥)
    (hfixed : Corollary85FixedPointFree
      (M ⊓ rightConjugate M t) t Y P) :
    Nonempty (Corollary85Conclusion M t d83.u Y P) := by
  obtain ⟨supported⟩ := h84.corollary85_supported
    d83 hM ht htM hYV hYne hI hPV hPne hfixed
  exact ⟨supported.conclusion⟩

end CFSG.BenderSuzuki
