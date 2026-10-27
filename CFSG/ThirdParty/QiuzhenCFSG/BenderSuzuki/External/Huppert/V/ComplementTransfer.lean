module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.SamePrime

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v
/--
Huppert V.8.13 step 3 in the minimal-counterexample branch: after the proper
invariant subgroups and proper invariant quotients have been disposed of, a
solvable counterexample is impossible.
-/
public theorem hkt_nonsolvable_of_minimal_branch
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    (hprime : Nat.Prime p) (hp2 : p ≠ 2)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (hnon_nil : ¬ Group.IsNilpotent Q)
    (hproper_invariant_subgroup_nil :
      ∀ N : Subgroup Q, N ≠ ⊥ → N ≠ ⊤ →
        (∀ q : Q, q ∈ N ↔ φ q ∈ N) → Group.IsNilpotent N)
    (hproper_invariant_quotient_nil :
      ∀ N : Subgroup Q, [N.Normal] → N ≠ ⊥ → N ≠ ⊤ →
        (∀ q : Q, q ∈ N ↔ φ q ∈ N) → Group.IsNilpotent (Q ⧸ N))
    (hcenter_bot : Subgroup.center Q = ⊥) :
    ¬ IsSolvable Q := by
  intro hsolv
  obtain ⟨N, hNnorm, hNinv, hN_ne_top, hNmax⟩ :=
    hkt_exists_maximal_proper_invariant_normal φ hnon_nil
  haveI : N.Normal := hNnorm
  have hN_ne_bot : N ≠ ⊥ := by
    intro hNbot
    obtain ⟨M, hMnorm, hMinv, hM_ne_bot, hMmin⟩ :=
      hkt_exists_minimal_invariant_normal φ hnon_nil
    haveI : M.Normal := hMnorm
    have hM_ne_top : M ≠ ⊤ :=
      hkt_minimal_invariant_normal_ne_top_of_solvable_branch
        φ hnon_nil hsolv M hMmin
    have hM_eq_N : M = N :=
      hNmax M hMnorm hMinv (by
        rw [hNbot]
        exact bot_le) hM_ne_top
    have hM_eq_bot : M = ⊥ := by
      rw [hM_eq_N, hNbot]
    exact hM_ne_bot hM_eq_bot
  have hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N :=
    hkt_zpowers_invariant_generator φ N
  have hN_nil : Group.IsNilpotent N :=
    hproper_invariant_subgroup_nil N hN_ne_bot hN_ne_top hNφ
  have hquot_nil : Group.IsNilpotent (Q ⧸ N) :=
    hproper_invariant_quotient_nil N hN_ne_bot hN_ne_top hNφ
  exact
    hkt_false_of_solvable_maximal_branch_core φ hprime hp2 hperiod hprod
      hnon_nil hsolv N hNinv hN_ne_bot hN_ne_top hNmax hN_nil
      hquot_nil hproper_invariant_quotient_nil hcenter_bot

/--
Bridge from the HKT minimal-counterexample induction hypothesis to local
`p`-nilpotence: once a proper nontrivial subgroup is `φ`-invariant, the
induction hypothesis gives nilpotence, hence a normal `p`-complement.
-/
public theorem hkt_hasNormalPComplement_of_proper_invariant_subgroup_induction
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ} [Fact p.Prime]
    (N : Subgroup Q)
    (hproper_invariant_subgroup_nil :
      ∀ N : Subgroup Q, N ≠ ⊥ → N ≠ ⊤ →
        (∀ q : Q, q ∈ N ↔ φ q ∈ N) → Group.IsNilpotent N)
    (hN_ne_bot : N ≠ ⊥) (hN_ne_top : N ≠ ⊤)
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N) :
    HasNormalPComplement p N := by
  exact hkt_hasNormalPComplement_of_nilpotent
    (Q := N) (p := p)
    (hproper_invariant_subgroup_nil N hN_ne_bot hN_ne_top hNφ)

/-- If a subgroup is invariant under `φ`, then it is invariant under `φ.symm`. -/
public theorem hkt_subgroup_invariant_symm
    {Q : Type u} [Group Q] (φ : MulAut Q) (H : Subgroup Q)
    (hH : ∀ q : Q, q ∈ H ↔ φ q ∈ H) :
    ∀ q : Q, q ∈ H ↔ φ.symm q ∈ H := by
  intro q
  have h := hH (φ.symm q)
  constructor
  · intro hq
    exact h.mpr (by simpa using hq)
  · intro hq
    simpa using h.mp hq

/-- A normalizer is invariant under an automorphism that preserves the subgroup. -/
public theorem hkt_normalizer_mem_of_invariant
    {Q : Type u} [Group Q] (φ : MulAut Q) (H : Subgroup Q)
    (hH : ∀ q : Q, q ∈ H ↔ φ q ∈ H) {x : Q}
    (hx : x ∈ Subgroup.normalizer (H : Set Q)) :
    φ x ∈ Subgroup.normalizer (H : Set Q) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  calc
    h ∈ H ↔ φ.symm h ∈ H := hkt_subgroup_invariant_symm φ H hH h
    _ ↔ x * φ.symm h * x⁻¹ ∈ H := hx (φ.symm h)
    _ ↔ φ (x * φ.symm h * x⁻¹) ∈ H := hH (x * φ.symm h * x⁻¹)
    _ ↔ φ x * h * (φ x)⁻¹ ∈ H := by simp

/-- A normalizer is invariant exactly when the underlying subgroup is. -/
public theorem hkt_normalizer_invariant_of_invariant
    {Q : Type u} [Group Q] (φ : MulAut Q) (H : Subgroup Q)
    (hH : ∀ q : Q, q ∈ H ↔ φ q ∈ H) :
    ∀ x : Q,
      x ∈ Subgroup.normalizer (H : Set Q) ↔
        φ x ∈ Subgroup.normalizer (H : Set Q) := by
  intro x
  constructor
  · exact hkt_normalizer_mem_of_invariant φ H hH
  · intro hx
    have hHsymm : ∀ q : Q, q ∈ H ↔ φ.symm q ∈ H :=
      hkt_subgroup_invariant_symm φ H hH
    have hx' := hkt_normalizer_mem_of_invariant φ.symm H hHsymm hx
    simpa using hx'

/-- A centralizer is invariant under an automorphism that preserves the set centralized. -/
public theorem hkt_centralizer_mem_of_invariant
    {Q : Type u} [Group Q] (φ : MulAut Q) (H : Subgroup Q)
    (hH : ∀ q : Q, q ∈ H ↔ φ q ∈ H) {x : Q}
    (hx : x ∈ Subgroup.centralizer (H : Set Q)) :
    φ x ∈ Subgroup.centralizer (H : Set Q) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro h hh
  have hpre : φ.symm h ∈ H :=
    (hH (φ.symm h)).mpr (by simpa using hh)
  have hcomm := hx (φ.symm h) hpre
  simpa using congrArg φ hcomm

/-- A centralizer is invariant exactly when the underlying subgroup is. -/
public theorem hkt_centralizer_invariant_of_invariant
    {Q : Type u} [Group Q] (φ : MulAut Q) (H : Subgroup Q)
    (hH : ∀ q : Q, q ∈ H ↔ φ q ∈ H) :
    ∀ x : Q,
      x ∈ Subgroup.centralizer (H : Set Q) ↔
        φ x ∈ Subgroup.centralizer (H : Set Q) := by
  intro x
  constructor
  · exact hkt_centralizer_mem_of_invariant φ H hH
  · intro hx
    have hHsymm : ∀ q : Q, q ∈ H ↔ φ.symm q ∈ H :=
      hkt_subgroup_invariant_symm φ H hH
    have hx' := hkt_centralizer_mem_of_invariant φ.symm H hHsymm hx
    simpa using hx'

/--
If `S` is invariant under `φ` and `H` is characteristic in `S`, then the
ambient subgroup `H` is invariant under `φ`.
-/
public theorem hkt_ambient_invariant_of_subgroupOf_characteristic
    {Q : Type u} [Group Q] (φ : MulAut Q) (S H : Subgroup Q)
    (hH_le : H ≤ S)
    (hSφ : ∀ q : Q, q ∈ S ↔ φ q ∈ S)
    [hchar : (H.subgroupOf S).Characteristic] :
    ∀ q : Q, q ∈ H ↔ φ q ∈ H := by
  intro q
  constructor
  · intro hq
    let qS : S := ⟨q, hH_le hq⟩
    have hqSub : qS ∈ H.subgroupOf S := hq
    have hmap : (H.subgroupOf S).map (invariantSubgroupAut φ S hSφ).toMonoidHom =
        H.subgroupOf S :=
      Subgroup.characteristic_iff_map_eq.mp hchar (invariantSubgroupAut φ S hSφ)
    have : invariantSubgroupAut φ S hSφ qS ∈ H.subgroupOf S := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem (invariantSubgroupAut φ S hSφ).toMonoidHom hqSub
    simpa [qS, invariantSubgroupAut, Subgroup.mem_subgroupOf] using this
  · intro hq
    let qS : S := ⟨q, (hSφ q).mpr (hH_le hq)⟩
    have hφqSub : invariantSubgroupAut φ S hSφ qS ∈ H.subgroupOf S := by
      simpa [qS, invariantSubgroupAut, Subgroup.mem_subgroupOf] using hq
    have hmap : (H.subgroupOf S).map (invariantSubgroupAut φ S hSφ).symm.toMonoidHom =
        H.subgroupOf S :=
      Subgroup.characteristic_iff_map_eq.mp hchar (invariantSubgroupAut φ S hSφ).symm
    have : (invariantSubgroupAut φ S hSφ).symm (invariantSubgroupAut φ S hSφ qS) ∈
        H.subgroupOf S := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem (invariantSubgroupAut φ S hSφ).symm.toMonoidHom hφqSub
    simpa [qS, invariantSubgroupAut, Subgroup.mem_subgroupOf] using this

/-- `J(S)` is invariant when the Sylow subgroup `S` is invariant. -/
public theorem hkt_thompsonSubgroup_invariant_of_invariant_sylow
    {Q : Type u} [Group Q] (φ : MulAut Q) {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hSφ : ∀ x : Q, x ∈ (S : Subgroup Q) ↔ φ x ∈ (S : Subgroup Q)) :
    ∀ x : Q,
      x ∈ thompsonSubgroup (G := Q) (S : Subgroup Q) ↔
        φ x ∈ thompsonSubgroup (G := Q) (S : Subgroup Q) := by
  haveI : ((thompsonSubgroup (G := Q) (S : Subgroup Q)).subgroupOf
      (S : Subgroup Q)).Characteristic :=
    section8_thompsonSubgroup_subgroupOf_characteristic (S : Subgroup Q)
  exact hkt_ambient_invariant_of_subgroupOf_characteristic φ (S : Subgroup Q)
    (thompsonSubgroup (G := Q) (S : Subgroup Q))
    (section8_thompsonSubgroup_le (S : Subgroup Q)) hSφ

/-- `Z(S)`, viewed inside the ambient group, is invariant when `S` is invariant. -/
public theorem hkt_centerIn_sylow_invariant_of_invariant_sylow
    {Q : Type u} [Group Q] (φ : MulAut Q) {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hSφ : ∀ x : Q, x ∈ (S : Subgroup Q) ↔ φ x ∈ (S : Subgroup Q)) :
    ∀ x : Q,
      x ∈ centerIn (G := Q) (S : Subgroup Q) ↔
        φ x ∈ centerIn (G := Q) (S : Subgroup Q) := by
  have hcenter_subgroupOf :
      (centerIn (G := Q) (S : Subgroup Q)).subgroupOf (S : Subgroup Q) =
        Subgroup.center (S : Subgroup Q) := by
    rw [centerIn_eq_map_center_local]
    change ((Subgroup.center (S : Subgroup Q)).map (S : Subgroup Q).subtype).comap
        (S : Subgroup Q).subtype = Subgroup.center (S : Subgroup Q)
    exact Subgroup.comap_map_eq_self_of_injective
      (H := Subgroup.center (S : Subgroup Q)) (f := (S : Subgroup Q).subtype)
      (S : Subgroup Q).subtype_injective
  haveI : ((centerIn (G := Q) (S : Subgroup Q)).subgroupOf
      (S : Subgroup Q)).Characteristic := by
    rw [hcenter_subgroupOf]
    exact Subgroup.centerCharacteristic
  exact hkt_ambient_invariant_of_subgroupOf_characteristic φ (S : Subgroup Q)
    (centerIn (G := Q) (S : Subgroup Q)) inf_le_left hSφ

/--
The characteristic-subgroup branch of the HKT minimal-counterexample argument:
if every proper nontrivial invariant subgroup and quotient is nilpotent, then a
nonsolvable counterexample has no proper nontrivial characteristic subgroup.
-/
public theorem hkt_characteristically_simple_of_minimal_branch
    {Q : Type u} [Group Q] (φ : MulAut Q)
    (hnot_solvable : ¬ IsSolvable Q)
    (hproper_invariant_subgroup_nil :
      ∀ N : Subgroup Q, N ≠ ⊥ → N ≠ ⊤ →
        (∀ q : Q, q ∈ N ↔ φ q ∈ N) → Group.IsNilpotent N)
    (hproper_invariant_quotient_nil :
      ∀ N : Subgroup Q, [N.Normal] → N ≠ ⊥ → N ≠ ⊤ →
        (∀ q : Q, q ∈ N ↔ φ q ∈ N) → Group.IsNilpotent (Q ⧸ N)) :
    ∀ N : Subgroup Q, N.Characteristic → N = ⊥ ∨ N = ⊤ := by
  intro N hNchar
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  by_cases hNtop : N = ⊤
  · exact Or.inr hNtop
  exfalso
  haveI : N.Characteristic := hNchar
  have hNinv : ∀ q : Q, q ∈ N ↔ φ q ∈ N :=
    hkt_characteristic_subgroup_invariant φ N
  have hN_nil : Group.IsNilpotent N :=
    hproper_invariant_subgroup_nil N hNbot hNtop hNinv
  have hquot_nil : Group.IsNilpotent (Q ⧸ N) :=
    hproper_invariant_quotient_nil N hNbot hNtop hNinv
  exact hnot_solvable
    (hkt_solvable_of_normal_nilpotent_and_quotient_nilpotent N hN_nil hquot_nil)
/--
If an HKT minimal counterexample is already known to be nonsolvable and
characteristically simple, then it cannot have a normal complement for a prime
that divides its order. This is the formal end of Huppert V.8.13 step 4 after
Thompson IV.6.2 supplies the normal complement.
-/
public theorem hkt_no_normal_p_complement_of_characteristic_simple
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hnot_solvable : ¬ IsSolvable Q)
    (hq_dvd : q ∣ Nat.card Q)
    (hchar_simple : ∀ N : Subgroup Q, N.Characteristic → N = ⊥ ∨ N = ⊤)
    (hcomp : HasNormalPComplement q Q) : False := by
  classical
  have hquot_p : IsPGroup q (Q ⧸ pPrimeCore q Q) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := q) Q hcomp
  rcases hchar_simple (pPrimeCore q Q) (inferInstance : (pPrimeCore q Q).Characteristic) with hcore_bot | hcore_top
  · let e : Q ⧸ pPrimeCore q Q ≃* Q ⧸ (⊥ : Subgroup Q) :=
      QuotientGroup.quotientMulEquivOfEq hcore_bot
    have hquot_bot : IsPGroup q (Q ⧸ (⊥ : Subgroup Q)) := hquot_p.of_equiv e
    have hQ_p : IsPGroup q Q :=
      hquot_bot.of_equiv (QuotientGroup.quotientBot (G := Q))
    have hQ_nil : Group.IsNilpotent Q := hQ_p.isNilpotent
    haveI : Group.IsNilpotent Q := hQ_nil
    exact hnot_solvable IsNilpotent.to_isSolvable
  · have hcop : Nat.Coprime q (Nat.card Q) := by
      simpa [hcore_top] using pPrimeCore_coprime_card (G := Q) (p := q)
    exact ((Fact.out : Nat.Prime q).coprime_iff_not_dvd.mp hcop) hq_dvd

/--
The final minimal-counterexample contradiction once the local Thompson step has
produced a normal `q`-complement. This is the reusable recoupling of the
nonsolvable and characteristic-simple HKT branches.
-/
public theorem hkt_false_of_normal_p_complement_in_minimal_branch
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {q : ℕ} [Fact q.Prime]
    (hnot_solvable : ¬ IsSolvable Q)
    (hproper_invariant_subgroup_nil :
      ∀ N : Subgroup Q, N ≠ ⊥ → N ≠ ⊤ →
        (∀ q : Q, q ∈ N ↔ φ q ∈ N) → Group.IsNilpotent N)
    (hproper_invariant_quotient_nil :
      ∀ N : Subgroup Q, [N.Normal] → N ≠ ⊥ → N ≠ ⊤ →
        (∀ q : Q, q ∈ N ↔ φ q ∈ N) → Group.IsNilpotent (Q ⧸ N))
    (hq_dvd : q ∣ Nat.card Q) (hcomp : HasNormalPComplement q Q) : False := by
  have hchar_simple :
      ∀ N : Subgroup Q, N.Characteristic → N = ⊥ ∨ N = ⊤ :=
    hkt_characteristically_simple_of_minimal_branch
      φ hnot_solvable hproper_invariant_subgroup_nil
      hproper_invariant_quotient_nil
  exact hkt_no_normal_p_complement_of_characteristic_simple
    hnot_solvable hq_dvd hchar_simple hcomp

/--
The Sylow fixed-point core for the HKT odd-prime step: a prime-power operator
group fixes a Sylow subgroup whenever the operator prime does not divide the
finite set of Sylow subgroups.
-/
public theorem hkt_exists_invariant_sylow_of_prime_period_not_dvd_sylow_card
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p q : ℕ}
    (hprime : Nat.Prime p) [Fact q.Prime]
    (hφpow : φ ^ p = 1)
    (hp_not_dvd_sylow : ¬ p ∣ Nat.card (Sylow q Q)) :
    ∃ S : Sylow q Q, ∀ x : Q, x ∈ (S : Subgroup Q) ↔ φ x ∈ (S : Subgroup Q) := by
  classical
  letI : Fact p.Prime := ⟨hprime⟩
  let A : Subgroup (MulAut Q) := Subgroup.zpowers φ
  have hA_p : IsPGroup p A := by
    rw [IsPGroup.iff_card]
    rw [Nat.card_zpowers]
    have horder_dvd : orderOf φ ∣ p := orderOf_dvd_of_pow_eq_one hφpow
    rcases hprime.eq_one_or_self_of_dvd (orderOf φ) horder_dvd with horder | horder
    · exact ⟨0, by simp [horder]⟩
    · exact ⟨1, by simp [horder]⟩
  letI : Fact (IsPGroup p A) := ⟨hA_p⟩
  rcases (Fact.out : IsPGroup p A).nonempty_fixed_point_of_prime_not_dvd_card
      (Sylow q Q) hp_not_dvd_sylow with
    ⟨S, hSfix⟩
  refine ⟨S, ?_⟩
  let a : A := ⟨φ, by simp [A]⟩
  have hsmulS : a • S = S := (MulAction.mem_fixedPoints.mp hSfix) a
  have hsub_eq : a • (S : Subgroup Q) = (S : Subgroup Q) := by
    simpa [MulAction.subgroup_smul_def, Sylow.pointwise_smul_def] using
      congrArg (fun T : Sylow q Q => (T : Subgroup Q)) hsmulS
  intro x
  constructor
  · intro hx
    have hx' : a • x ∈ a • (S : Subgroup Q) :=
      Subgroup.smul_mem_pointwise_smul x a (S : Subgroup Q) hx
    change φ x ∈ (S : Subgroup Q)
    simpa [hsub_eq, a, A] using hx'
  · intro hx
    have hsmulSinv : a⁻¹ • (S : Subgroup Q) = (S : Subgroup Q) := by
      have hfix := (MulAction.mem_fixedPoints.mp hSfix) a⁻¹
      simpa [MulAction.subgroup_smul_def, Sylow.pointwise_smul_def] using
        congrArg (fun T : Sylow q Q => (T : Subgroup Q)) hfix
    have hx' : a⁻¹ • (a • x) ∈ a⁻¹ • (S : Subgroup Q) :=
      Subgroup.smul_mem_pointwise_smul (a • x) a⁻¹ (S : Subgroup Q) (by
        change φ x ∈ (S : Subgroup Q) at hx
        simpa [a, A] using hx)
    simpa [hsmulSinv] using hx'

/--
The coprime-period Sylow fixed-point subcase of Huppert V.8.13 step 4.
-/
public theorem hkt_exists_invariant_sylow_of_prime_period
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p q : ℕ}
    (hprime : Nat.Prime p) [Fact q.Prime]
    (hφpow : φ ^ p = 1)
    (hcop : Nat.Coprime p (Nat.card Q)) :
    ∃ S : Sylow q Q, ∀ x : Q, x ∈ (S : Subgroup Q) ↔ φ x ∈ (S : Subgroup Q) := by
  classical
  let S₀ : Sylow q Q := default
  have hcard_dvd : Nat.card (Sylow q Q) ∣ Nat.card Q := by
    exact dvd_trans (Sylow.card_dvd_index S₀)
      (Subgroup.index_dvd_card (H := (S₀ : Subgroup Q)))
  have hcop_sylow : Nat.Coprime p (Nat.card (Sylow q Q)) :=
    Nat.Coprime.of_dvd_right hcard_dvd hcop
  have hp_not_dvd_sylow : ¬ p ∣ Nat.card (Sylow q Q) :=
    (hprime.coprime_iff_not_dvd).mp hcop_sylow
  exact hkt_exists_invariant_sylow_of_prime_period_not_dvd_sylow_card
    φ hprime hφpow hp_not_dvd_sylow

/--
If the automorphism prime itself divides the group order, Huppert V.8.13 can
choose a `p`-Sylow fixed by the automorphism. This is the Sylow counting part of
the source branch; the fixed-point-free input is used separately in Huppert
8.11 to get invariant Sylows for all prime divisors.
-/
public theorem hkt_exists_invariant_sylow_of_same_prime_period
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    (hprime : Nat.Prime p)
    (hφpow : φ ^ p = 1) :
    ∃ S : Sylow p Q, ∀ x : Q, x ∈ (S : Subgroup Q) ↔ φ x ∈ (S : Subgroup Q) := by
  classical
  letI : Fact p.Prime := ⟨hprime⟩
  exact hkt_exists_invariant_sylow_of_prime_period_not_dvd_sylow_card
    φ hprime hφpow (not_dvd_card_sylow (p := p) (G := Q))

public theorem hkt_exists_prime_dvd_ne_of_not_prime_power {m p : ℕ}
    (hm0 : m ≠ 0) (hm_not : ∀ n, m ≠ p ^ n) :
    ∃ q, Nat.Prime q ∧ q ∣ m ∧ q ≠ p := by
  by_contra! h
  have h' : ∀ {d}, Nat.Prime d → d ∣ m → d = p := by
    intro d hprime hdvd
    exact h d hprime hdvd
  apply hm_not (Nat.primeFactorsList m).length
  exact Nat.eq_prime_pow_of_unique_prime_dvd hm0 h'

/--
The first choice in Huppert V.8.13 step 4: if the counterexample is not already
a 2-group, then an odd prime divisor can be chosen, and the Sylow subgroup for
that prime may be taken invariant under the HKT automorphism.
-/
public theorem hkt_exists_invariant_odd_sylow_of_not_two_group
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    (hprime : Nat.Prime p) (hp2 : p ≠ 2)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hnot_two : ¬ IsPGroup 2 Q) :
    ∃ q : ℕ, Nat.Prime q ∧ q ≠ 2 ∧ q ∣ Nat.card Q ∧
      ∃ S : Sylow q Q, ∀ x : Q, x ∈ (S : Subgroup Q) ↔ φ x ∈ (S : Subgroup Q) := by
  classical
  have hφpow : φ ^ p = 1 := hkt_mulAut_pow_eq_one_of_function_period φ hperiod
  by_cases hp_dvd : p ∣ Nat.card Q
  · letI : Fact p.Prime := ⟨hprime⟩
    refine ⟨p, hprime, hp2, hp_dvd, ?_⟩
    exact hkt_exists_invariant_sylow_of_same_prime_period φ hprime hφpow
  · have hcard_ne_zero : Nat.card Q ≠ 0 := Nat.card_pos.ne'
    have hnot_pow : ∀ n, Nat.card Q ≠ 2 ^ n := by
      intro n hcard
      exact hnot_two (IsPGroup.of_card (p := 2) hcard)
    rcases hkt_exists_prime_dvd_ne_of_not_prime_power hcard_ne_zero hnot_pow with
      ⟨q, hqprime, hq_dvd, hq_ne_two⟩
    letI : Fact q.Prime := ⟨hqprime⟩
    have hcop : Nat.Coprime p (Nat.card Q) :=
      (hprime.coprime_iff_not_dvd).mpr hp_dvd
    refine ⟨q, hqprime, hq_ne_two, hq_dvd, ?_⟩
    exact hkt_exists_invariant_sylow_of_prime_period φ hprime hφpow hcop

/--
Local `q`-nilpotence of `N_Q(J(S))` in Huppert V.8.13 step 4, isolated in the
source shape used by the minimal-counterexample argument.  Once the normalizer
is known to be a proper nontrivial `φ`-invariant subgroup, the induction
hypothesis gives nilpotence and hence a normal `q`-complement.
-/
public theorem hkt_normalizer_thompsonSubgroup_has_normal_p_complement_of_invariant_odd_sylow
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {q : ℕ}
    [Fact q.Prime]
    (S : Sylow q Q)
    (hproper_invariant_subgroup_nil :
      ∀ N : Subgroup Q, N ≠ ⊥ → N ≠ ⊤ →
        (∀ q : Q, q ∈ N ↔ φ q ∈ N) → Group.IsNilpotent N)
    (hnormalizer_ne_bot :
      Subgroup.normalizer
        (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊥)
    (hnormalizer_ne_top :
      Subgroup.normalizer
        (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤)
    (hnormalizerφ :
      ∀ x : Q,
        x ∈ Subgroup.normalizer
            (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) ↔
          φ x ∈ Subgroup.normalizer
            (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q)) :
    HasNormalPComplement q
      (↥(Subgroup.normalizer
        (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))) := by
  exact hkt_hasNormalPComplement_of_proper_invariant_subgroup_induction
    (Q := Q) (φ := φ) (p := q)
    (N := Subgroup.normalizer
      (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q))
    hproper_invariant_subgroup_nil hnormalizer_ne_bot hnormalizer_ne_top
    hnormalizerφ

/--
Local `q`-nilpotence of `C_Q(Z(S))` in Huppert V.8.13 step 4, in the same
minimal-counterexample-induction shape as the normalizer input.
-/
public theorem hkt_centralizer_center_sylow_has_normal_p_complement_of_invariant_odd_sylow
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {q : ℕ}
    [Fact q.Prime]
    (S : Sylow q Q)
    (hproper_invariant_subgroup_nil :
      ∀ N : Subgroup Q, N ≠ ⊥ → N ≠ ⊤ →
        (∀ q : Q, q ∈ N ↔ φ q ∈ N) → Group.IsNilpotent N)
    (hcentralizer_ne_bot :
      Subgroup.centralizer
        (centerIn (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊥)
    (hcentralizer_ne_top :
      Subgroup.centralizer
        (centerIn (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤)
    (hcentralizerφ :
      ∀ x : Q,
        x ∈ Subgroup.centralizer
            (centerIn (G := Q) (S : Subgroup Q) : Set Q) ↔
          φ x ∈ Subgroup.centralizer
            (centerIn (G := Q) (S : Subgroup Q) : Set Q)) :
    HasNormalPComplement q
      (↥(Subgroup.centralizer
        (centerIn (G := Q) (S : Subgroup Q) : Set Q))) := by
  exact hkt_hasNormalPComplement_of_proper_invariant_subgroup_induction
    (Q := Q) (φ := φ) (p := q)
    (N := Subgroup.centralizer
      (centerIn (G := Q) (S : Subgroup Q) : Set Q))
    hproper_invariant_subgroup_nil hcentralizer_ne_bot hcentralizer_ne_top
    hcentralizerφ

/--
In the center-free minimal branch, `C_Q(Z(S))` is a proper subgroup.  If every
element of `Q` centralized `Z(S)`, then `Z(S)` would lie in `Z(Q) = 1`,
contradicting the nontrivial center of the nontrivial Sylow `q`-subgroup.
-/
public theorem hkt_centralizer_center_sylow_ne_top_of_center_eq_bot
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hq_dvd : q ∣ Nat.card Q)
    (hcenter_bot : Subgroup.center Q = ⊥) :
    Subgroup.centralizer
        (centerIn (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤ := by
  intro htop
  have hS_ne_bot : (S : Subgroup Q) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := Q) (p := q) S hq_dvd
  have hZ_ne_bot : centerIn (G := Q) (S : Subgroup Q) ≠ ⊥ :=
    section8_centerIn_ne_bot_of_isPGroup S.isPGroup' hS_ne_bot
  have hZ_le_center :
      centerIn (G := Q) (S : Subgroup Q) ≤ Subgroup.center Q := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hgC :
        g ∈ Subgroup.centralizer
          (centerIn (G := Q) (S : Subgroup Q) : Set Q) := by
      rw [htop]
      simp
    exact (Subgroup.mem_centralizer_iff.mp hgC z hz).symm
  have hZ_le_bot : centerIn (G := Q) (S : Subgroup Q) ≤ (⊥ : Subgroup Q) := by
    simpa [hcenter_bot] using hZ_le_center
  exact hZ_ne_bot (le_bot_iff.mp hZ_le_bot)

/--
In the nonsolvable characteristically-simple minimal branch, `N_Q(J(S))` is a
proper subgroup.  If `J(S)` were normal in `Q`, then the nontrivial normal
`q`-subgroup it contains would force `O_q(Q) = Q`; hence `Q` would be a
`q`-group, nilpotent, and solvable.
-/
public theorem hkt_normalizer_thompsonSubgroup_ne_top_of_characteristically_simple
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hq_dvd : q ∣ Nat.card Q)
    (hnot_solvable : ¬ IsSolvable Q)
    (hchar_simple : ∀ N : Subgroup Q, N.Characteristic → N = ⊥ ∨ N = ⊤) :
    Subgroup.normalizer
        (thompsonSubgroup (G := Q) (S : Subgroup Q) : Set Q) ≠ ⊤ := by
  intro htop
  have hS_ne_bot : (S : Subgroup Q) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := Q) (p := q) S hq_dvd
  have hJ_ne_bot : thompsonSubgroup (G := Q) (S : Subgroup Q) ≠ ⊥ :=
    section8_thompsonSubgroup_ne_bot_of_ne_bot hS_ne_bot
  have hJ_normal :
      (thompsonSubgroup (G := Q) (S : Subgroup Q)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp htop
  have hJ_p : IsPGroup q (thompsonSubgroup (G := Q) (S : Subgroup Q)) :=
    IsPGroup.to_le
      (K := (S : Subgroup Q))
      S.isPGroup'
      (section8_thompsonSubgroup_le (S : Subgroup Q))
  have hJ_le_pCore :
      thompsonSubgroup (G := Q) (S : Subgroup Q) ≤ pCore q Q :=
    le_sSup ⟨hJ_normal, hJ_p⟩
  have hpCore_ne_bot : pCore q Q ≠ ⊥ := by
    intro hcore_bot
    have hJ_le_bot :
        thompsonSubgroup (G := Q) (S : Subgroup Q) ≤ (⊥ : Subgroup Q) := by
      simpa [hcore_bot] using hJ_le_pCore
    exact hJ_ne_bot (le_bot_iff.mp hJ_le_bot)
  rcases hchar_simple (pCore q Q) (pCore_characteristic (G := Q) (p := q)) with
    hcore_bot | hcore_top
  · exact hpCore_ne_bot hcore_bot
  · have htop_q : IsPGroup q (⊤ : Subgroup Q) := by
      have hpcore_q : IsPGroup q (pCore q Q) :=
        pCore_isPGroup (G := Q) (p := q)
      rwa [hcore_top] at hpcore_q
    have hQ_q : IsPGroup q Q :=
      htop_q.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
    haveI : Group.IsNilpotent Q := hQ_q.isNilpotent
    exact hnot_solvable IsNilpotent.to_isSolvable
end External
end CFSG.BenderSuzuki
