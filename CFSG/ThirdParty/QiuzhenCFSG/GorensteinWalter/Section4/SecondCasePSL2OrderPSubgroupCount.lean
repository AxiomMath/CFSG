module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeOrderSubgroupIntersection
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: order-`p` subgroups in a cyclic torus family

This is the finite counting core used in Bender's equation (11).  If the
nonidentity elements of order `p` lie in a unique conjugate of a cyclic torus
`U`, then the order-`p` subgroups are parametrized by the conjugates of `U`.
The orbit has cardinality `|G| / |N_G(U)|`; for `|N_G(U)| = 2 |U|` and
`|G| = 2 q |U| k'`, this is `q k'`.
-/

noncomputable section

open scoped BigOperators

namespace CFSG.GorensteinWalter

private theorem conjugate_family_card
    {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) :
    Nat.card {T : Subgroup G // ∃ g : G,
      T = U.map (MulAut.conj g).toMonoidHom} =
      (Subgroup.normalizer (U : Set G)).index := by
  classical
  let : MulAction G (Subgroup G) :=
    { smul := fun g H => H.map (MulAut.conj g).toMonoidHom
      one_smul := by
        intro H
        change H.map (MulAut.conj (1 : G)).toMonoidHom = H
        apply Subgroup.ext
        intro x
        rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
          ext x; simp]
        simp
      mul_smul := by
        intro g h H
        change H.map (MulAut.conj (g * h)).toMonoidHom =
          (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc] }
  have horbit :
      MulAction.orbit G U =
        {T : Subgroup G | ∃ g : G,
          T = U.map (MulAut.conj g).toMonoidHom} := by
    ext T
    constructor
    · intro hT
      rcases hT with ⟨g, rfl⟩
      exact ⟨g, by change U.map _ = _; rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, by change U.map _ = _; rfl⟩
  have hstab : MulAction.stabilizer G U =
      Subgroup.normalizer (U : Set G) := by
    ext g
    change g • U = U ↔ g ∈ Subgroup.normalizer (U : Set G)
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := G) (H := Subgroup.normalizer U),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact forall_congr' fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
          fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
            MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩
  change Nat.card ↥{T : Subgroup G | ∃ g : G,
    T = U.map (MulAut.conj g).toMonoidHom} = _
  rw [← horbit, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer G U, hstab]

private theorem order_p_elements_card_of_cyclic
    {G : Type*} [Group G] [Finite G]
    {p k : ℕ} [Fact p.Prime]
    (U : Subgroup G) (hcyc : IsCyclic U) (hcard : Nat.card U = k)
    (hpk : p ∣ k) :
    Nat.card {x : U // orderOf (x : G) = p} = p - 1 := by
  let : Fintype U := Fintype.ofFinite U
  have hpk' : p ∣ Fintype.card U := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact hpk
  have hfin : Fintype.card {x : U // orderOf (x : G) = p} = p - 1 := by
    calc
      Fintype.card {x : U // orderOf (x : G) = p} = p.totient := by
        rw [Fintype.card_subtype]
        simpa only [Subgroup.orderOf_coe] using
          hcyc.card_orderOf_eq_totient hpk'
      _ = p - 1 := Nat.totient_prime (Fact.out : Nat.Prime p)
  rw [Nat.card_eq_fintype_card]
  exact hfin

/-- In a unique conjugate family of cyclic tori, the number of subgroups of
prime order `p` is the number of torus conjugates.  The hypotheses are the
abstract form of Huppert II.8.5(a) and II.8.22 used for `PSL₂(q)`.

For a split or nonsplit `PSL₂` torus, instantiate `U` with the corresponding
Huppert torus, `hUN` with its normalizer-card theorem, `hpart` with the
restricted II.8.5 partition for order-`p` elements, and
`hGcard` with `|PSL₂(q)| = 2 q k k'`.
-/
public theorem psl2_order_p_subgroup_card_of_unique_torus_family
    {G : Type*} [Group G] [Finite G]
    {p q k k' : ℕ} [Fact p.Prime]
    (U : Subgroup G)
    (hcyc : IsCyclic U) (hUcard : Nat.card U = k)
    (hUN : Nat.card (Subgroup.normalizer (U : Set G)) = 2 * k)
    (hpart : ∀ x : G, orderOf x = p →
      ∃! T : {T : Subgroup G // ∃ g : G,
        T = U.map (MulAut.conj g).toMonoidHom}, (x : G) ∈ T.1)
    (hpk : p ∣ k)
    (hGcard : Nat.card G = 2 * q * k * k') :
    Nat.card {P : Subgroup G // Nat.card P = p} = q * k' := by
  classical
  let Tor := {T : Subgroup G // ∃ g : G,
      T = U.map (MulAut.conj g).toMonoidHom}
  let Alpha := {x : G // orderOf x = p}
  let Piece := Σ T : Tor, {x : T.1 // orderOf (x : G) = p}
  have hTorcard : Nat.card Tor = (Subgroup.normalizer (U : Set G)).index :=
    conjugate_family_card U
  have hindex : (Subgroup.normalizer (U : Set G)).index =
      (Nat.card G) / (Nat.card (Subgroup.normalizer (U : Set G))) := by
    rw [Subgroup.index_eq_card]
    have hm := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.normalizer (U : Set G))
    have hdiv : Nat.card G / Nat.card (Subgroup.normalizer (U : Set G)) =
        Nat.card (G ⧸ Subgroup.normalizer (U : Set G)) := by
      apply Nat.div_eq_of_eq_mul_right (Nat.card_pos)
      simpa [mul_comm] using hm
    exact hdiv.symm
  have hTorcard' : Nat.card Tor = q * k' := by
    rw [hTorcard, hindex, hGcard, hUN]
    have hkpos : 0 < k := by simpa [← hUcard] using (Nat.card_pos (α := U))
    rw [Nat.div_eq_of_eq_mul_right (by omega)]
    simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hTcard (T : Tor) : Nat.card T.1 = k := by
    rcases T.2 with ⟨g, hg⟩
    rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hUcard]
  have hTcyc (T : Tor) : IsCyclic T.1 := by
    rcases T.2 with ⟨g, hg⟩
    rw [hg]
    exact (MulEquiv.isCyclic ((MulAut.conj g).subgroupMap U)).mp hcyc
  have hpiece_fiber (T : Tor) :
      Nat.card {x : T.1 // orderOf (x : G) = p} = p - 1 := by
    exact order_p_elements_card_of_cyclic T.1 (hTcyc T) (hTcard T) hpk
  let hdecode : Piece → Alpha := fun z => ⟨(z.2 : G), z.2.property⟩
  have hdecode_bij : Function.Bijective hdecode := by
    constructor
    · intro a b hab
      rcases a with ⟨Ta, xa⟩
      rcases b with ⟨Tb, xb⟩
      have hxa : (xa : G) ≠ 1 := by
        intro hx
        have hp1 : p = 1 := by simpa [hx] using xa.property.symm
        exact (Fact.out : Nat.Prime p).ne_one hp1
      have hxab : (xa : G) = (xb : G) := by
        simpa [hdecode] using congrArg Subtype.val hab
      have huniq := ExistsUnique.unique (hpart (xa : G) xa.property)
        (y₁ := Ta) (y₂ := Tb)
      have hTab : Ta = Tb := huniq xa.1.property (hxab ▸ xb.1.property)
      cases hTab
      apply congrArg (fun y => (⟨Ta, y⟩ : Piece))
      apply Subtype.ext
      exact Subtype.ext hxab
    · intro x
      have hxne : (x : G) ≠ 1 := by
        intro hx
        have hp1 : p = 1 := by simpa [hx] using x.property.symm
        exact (Fact.out : Nat.Prime p).ne_one hp1
      obtain ⟨T, hTx⟩ := (hpart (x : G) x.property).exists
      let T' : Tor := T
      let z : Piece := ⟨T', ⟨⟨x, hTx⟩, x.property⟩⟩
      refine ⟨z, ?_⟩
      simpa [hdecode, z]
  let : Fintype Tor := Fintype.ofFinite Tor
  have hAlpha_card : Nat.card Alpha = (q * k') * (p - 1) := by
    calc
      Nat.card Alpha = Nat.card Piece :=
        (Nat.card_congr (Equiv.ofBijective hdecode hdecode_bij)).symm
      _ = ∑ T : Tor, Nat.card {x : T.1 // orderOf (x : G) = p} := Nat.card_sigma
      _ = ∑ _T : Tor, (p - 1) := by simp_rw [hpiece_fiber]
      _ = Nat.card Tor * (p - 1) := by
        rw [Finset.sum_const, Finset.card_univ]
        rw [Nat.nsmul_eq_mul, Nat.card_eq_fintype_card]
      _ = (q * k') * (p - 1) := by rw [hTorcard']
  let Subps := {P : Subgroup G // Nat.card P = p}
  let PPiece := Σ P : Subps, {x : P.1 // (x : G) ≠ 1}
  have hporder (z : PPiece) : orderOf (z.2 : G) = p := by
    have hdvd : orderOf (z.2 : G) ∣ p := by
      simpa [z.1.2] using Subgroup.orderOf_dvd_natCard z.1.1 z.2.1.property
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdvd with h1 | hp'
    · exfalso
      apply z.2.property
      exact orderOf_eq_one_iff.mp h1
    · exact hp'
  let pdecode : PPiece → Alpha := fun z => ⟨(z.2 : G), hporder z⟩
  have hpdecode_bij : Function.Bijective pdecode := by
    constructor
    · intro a b hab
      rcases a with ⟨Pa, xa⟩
      rcases b with ⟨Pb, xb⟩
      have hxab : (xa : G) = (xb : G) := by
        simpa [pdecode] using congrArg Subtype.val hab
      have hP : Pa = Pb := by
        have hpeq := subgroup_eq_of_card_eq_prime_of_common_ne_one
          (Fact.out : Nat.Prime p) Pa.1 Pb.1 Pa.2 Pb.2
          xa.1.property (hxab ▸ xb.1.property) xa.property
        exact Subtype.ext hpeq
      cases hP
      apply congrArg (fun y => (⟨Pa, y⟩ : PPiece))
      apply Subtype.ext
      exact Subtype.ext hxab
    · intro x
      have hxne : (x : G) ≠ 1 := by
        intro hx
        have hp1 : p = 1 := by simpa [hx] using x.property.symm
        exact (Fact.out : Nat.Prime p).ne_one hp1
      let P : Subgroup G := Subgroup.zpowers (x : G)
      have hPcard : Nat.card P = p := by
        dsimp [P]
        rw [Nat.card_zpowers, x.property]
      have hxP : (x : G) ∈ P := by exact Subgroup.mem_zpowers _
      let z : PPiece := ⟨⟨P, hPcard⟩, ⟨⟨x, hxP⟩, hxne⟩⟩
      exact ⟨z, rfl⟩
  have hPPiece_card : Nat.card PPiece = Nat.card Subps * (p - 1) := by
    let : Fintype Subps := Fintype.ofFinite Subps
    rw [Nat.card_sigma]
    have hfiber (P : Subps) :
        Nat.card {x : P.1 // (x : G) ≠ 1} = p - 1 := by
      let : Fintype P.1 := Fintype.ofFinite P.1
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
      rw [← Nat.card_eq_fintype_card, P.2]
      simp
    simp_rw [hfiber]
    rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
      Nat.card_eq_fintype_card]
  have hSubps_card : Nat.card Subps * (p - 1) = Nat.card Alpha := by
    calc
      Nat.card Subps * (p - 1) = Nat.card PPiece := hPPiece_card.symm
      _ = Nat.card Alpha := Nat.card_congr (Equiv.ofBijective pdecode hpdecode_bij)
  have hSubps_card' : Nat.card Subps * (p - 1) =
      (q * k') * (p - 1) := hSubps_card.trans hAlpha_card
  have hp1 : 0 < p - 1 := by
    have := (Fact.out : Nat.Prime p).one_lt
    omega
  exact Nat.eq_of_mul_eq_mul_right hp1 hSubps_card'

end CFSG.GorensteinWalter
