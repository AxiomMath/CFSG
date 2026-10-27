module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2QuotientTorusCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPSL2TorusPartition
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The compatible quotient-torus family for equation (11)

The quotient torus retained by the Section-4 equation-(9) package is chosen
from Huppert's reflected-torus data.  This module proves that the same torus,
not merely an independently chosen torus of the same cardinality, carries the
restricted Huppert II.8.5(a) partition needed by equation (11).
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open BenderSuzuki
open BenderSuzuki.External

/-- Restricted Huppert partition for one of the two torus families, assuming
that the selected prime divides this family and not the characteristic or the
other torus family. -/
private theorem restricted_family_of_huppert_partition
    {K : Type u} [Field K] [Finite K]
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime]
    (P : Sylow r (PSL2 K)) (C D : Subgroup (PSL2 K))
    (hpne : p ≠ r) (hpD : ¬ p ∣ Nat.card D)
    (hpart : ∀ x : PSL2 K, x ≠ 1 →
      ∃! T : Subgroup (PSL2 K),
        x ∈ T ∧
          ((∃ g, T = (P : Subgroup (PSL2 K)).map
            (MulAut.conj g).toMonoidHom) ∨
          (∃ g, T = C.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, T = D.map (MulAut.conj g).toMonoidHom))) :
    ∀ x : PSL2 K, orderOf x = p →
      ∃! T : {T : Subgroup (PSL2 K) // ∃ g : PSL2 K,
        T = C.map (MulAut.conj g).toMonoidHom}, x ∈ T.1 := by
  classical
  intro x hxord
  have hxne : x ≠ 1 := by
    intro hx
    have hp1 : p = 1 := by simpa [hx] using hxord.symm
    exact (Fact.out : Nat.Prime p).ne_one hp1
  obtain ⟨T, hTx, hTuniq⟩ := hpart x hxne
  have hTC : ∃ g : PSL2 K, T = C.map (MulAut.conj g).toMonoidHom := by
    rcases hTx.2 with hP | hC | hD
    · exfalso
      rcases hP with ⟨g, rfl⟩
      rcases Subgroup.mem_map.mp hTx.1 with ⟨y, hy, hyx⟩
      have hyord : orderOf y = p := by
        calc
          orderOf y = orderOf ((MulAut.conj g) y) :=
            ((MulAut.conj g).orderOf_eq y).symm
          _ = orderOf x := congrArg orderOf hyx
          _ = p := hxord
      have hyordP : orderOf (⟨y, hy⟩ : (P : Subgroup (PSL2 K))) = p := by
        simpa [Subgroup.orderOf_coe] using hyord
      obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup')
        (⟨y, hy⟩ : (P : Subgroup (PSL2 K)))
      have hpPow : p ∣ r ^ n := by rw [← hn, hyordP]
      have hpr : p ∣ r := (Fact.out : Nat.Prime p).dvd_of_dvd_pow hpPow
      exact hpne ((Nat.prime_dvd_prime_iff_eq
        (Fact.out : Nat.Prime p) (Fact.out : Nat.Prime r)).mp hpr)
    · exact hC
    · exfalso
      rcases hD with ⟨g, rfl⟩
      rcases Subgroup.mem_map.mp hTx.1 with ⟨y, hy, hyx⟩
      have hyord : orderOf y = p := by
        calc
          orderOf y = orderOf ((MulAut.conj g) y) :=
            ((MulAut.conj g).orderOf_eq y).symm
          _ = orderOf x := congrArg orderOf hyx
          _ = p := hxord
      apply hpD
      have hydiv : orderOf y ∣ Nat.card D :=
        Subgroup.orderOf_dvd_natCard D hy
      simpa [hyord] using hydiv
  refine ⟨⟨T, hTC⟩, hTx.1, ?_⟩
  intro T' hT'x
  rcases T'.2 with ⟨g, hg⟩
  have hglobal :
      x ∈ T'.1 ∧
        ((∃ a, T'.1 = (P : Subgroup (PSL2 K)).map
          (MulAut.conj a).toMonoidHom) ∨
        (∃ a, T'.1 = C.map (MulAut.conj a).toMonoidHom) ∨
        (∃ a, T'.1 = D.map (MulAut.conj a).toMonoidHom)) :=
    ⟨hT'x, Or.inr (Or.inl ⟨g, hg⟩)⟩
  exact Subtype.ext (hTuniq T'.1 hglobal)

/-- A unique conjugate-family partition is unchanged when its base subgroup
is replaced by a conjugate. -/
private theorem conjugate_base_family_partition
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (C V : Subgroup G) (g : G)
    (hV : V = C.map (MulAut.conj g).toMonoidHom)
    (hpart : ∀ x : G, orderOf x = p →
      ∃! T : {T : Subgroup G // ∃ a : G,
        T = C.map (MulAut.conj a).toMonoidHom}, x ∈ T.1) :
    ∀ x : G, orderOf x = p →
      ∃! T : {T : Subgroup G // ∃ a : G,
        T = V.map (MulAut.conj a).toMonoidHom}, x ∈ T.1 := by
  classical
  intro x hx
  obtain ⟨T, hxT, huniq⟩ := hpart x hx
  rcases T.2 with ⟨a, ha⟩
  have hTV : ∃ b : G, T.1 = V.map (MulAut.conj b).toMonoidHom := by
    refine ⟨a * g⁻¹, ?_⟩
    rw [hV, Subgroup.map_map]
    rw [ha]
    apply congrArg (fun f : G →* G => C.map f)
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨⟨T.1, hTV⟩, hxT, ?_⟩
  intro T' hxT'
  rcases T'.2 with ⟨b, hb⟩
  have hTC : ∃ a' : G, T'.1 = C.map (MulAut.conj a').toMonoidHom := by
    refine ⟨b * g, ?_⟩
    rw [hb, hV, Subgroup.map_map]
    apply congrArg (fun f : G →* G => C.map f)
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have heq := huniq ⟨T'.1, hTC⟩ hxT'
  have hval : T'.1 = T.1 := congrArg
    (fun Z : {W : Subgroup G // ∃ a : G,
      W = C.map (MulAut.conj a).toMonoidHom} => Z.1) heq
  exact Subtype.ext hval

/-- A cyclic even half-torus in `PSL₂(K)` is a conjugate of the corresponding
Huppert torus and therefore carries the restricted unique-family partition
for every odd prime dividing its order. -/
private theorem selected_half_torus_partition
    {K : Type u} [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime]
    (hK : IsOddPrimePower (Nat.card K))
    (V : Subgroup (PSL2 K)) (hVcyc : IsCyclic V)
    (hVeven : Even (Nat.card V))
    (hVcard : Nat.card V = (Nat.card K - 1) / 2 ∨
      Nat.card V = (Nat.card K + 1) / 2)
    (hpodd : Odd p) (hpV : p ∣ Nat.card V) :
    ∀ x : PSL2 K, orderOf x = p →
      ∃! T : {T : Subgroup (PSL2 K) // ∃ g : PSL2 K,
        T = V.map (MulAut.conj g).toMonoidHom}, x ∈ T.1 := by
  classical
  rcases hK with ⟨r, f, hr, hrOdd, hf, hKcard⟩
  let : Fact r.Prime := ⟨hr⟩
  let P : Sylow r (PSL2 K) := Classical.choice Sylow.nonempty
  obtain ⟨U, S, hUcyc, hUcard, hScyc, hScard, hpart⟩ :=
    huppert_II_8_5_a_psl2_cover hKcard P
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact hrOdd.pow
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 :=
    gcd_sub_one_two_of_odd hKodd
  have hUcard' : Nat.card U = (Nat.card K - 1) / 2 := by
    simpa [hgcd] using hUcard
  have hScard' : Nat.card S = (Nat.card K + 1) / 2 := by
    simpa [hgcd] using hScard
  have hhalves : (Nat.card K + 1) / 2 = (Nat.card K - 1) / 2 + 1 := by
    rcases hKodd with ⟨a, ha⟩
    omega
  have hpne : p ≠ r := by
    intro hpr
    subst p
    have hrK : r ∣ Nat.card K := by
      rw [hKcard]
      exact dvd_pow_self r (by omega)
    have hrTwice : r ∣ 2 * Nat.card V := dvd_mul_of_dvd_right hpV 2
    have hrOne : r ∣ 1 := by
      rcases hVcard with hminus | hplus
      · have hrMinus : r ∣ Nat.card K - 1 := by
          convert hrTwice using 1
          rw [hminus]
          rcases hKodd with ⟨a, ha⟩
          omega
        convert Nat.dvd_sub hrK hrMinus using 1
        omega
      · have hrPlus : r ∣ Nat.card K + 1 := by
          convert hrTwice using 1
          rw [hplus]
          rcases hKodd with ⟨a, ha⟩
          omega
        convert Nat.dvd_sub hrPlus hrK using 1
        omega
    exact hr.ne_one (Nat.dvd_one.mp hrOne)
  have hnotOpposite :
      (Nat.card V = (Nat.card K - 1) / 2 → ¬ p ∣ Nat.card S) ∧
      (Nat.card V = (Nat.card K + 1) / 2 → ¬ p ∣ Nat.card U) := by
    constructor
    · intro hVminus hpS
      have hpMinus : p ∣ (Nat.card K - 1) / 2 := by simpa [hVminus] using hpV
      have hpPlus : p ∣ (Nat.card K + 1) / 2 := by simpa [hScard'] using hpS
      have hpOne : p ∣ 1 := by
        convert Nat.dvd_sub hpPlus hpMinus using 1
        omega
      exact (Fact.out : Nat.Prime p).ne_one (Nat.dvd_one.mp hpOne)
    · intro hVplus hpU
      have hpPlus : p ∣ (Nat.card K + 1) / 2 := by simpa [hVplus] using hpV
      have hpMinus : p ∣ (Nat.card K - 1) / 2 := by simpa [hUcard'] using hpU
      have hpOne : p ∣ 1 := by
        convert Nat.dvd_sub hpPlus hpMinus using 1
        omega
      exact (Fact.out : Nat.Prime p).ne_one (Nat.dvd_one.mp hpOne)
  let : IsCyclic V := hVcyc
  obtain ⟨v, hvgen⟩ := IsCyclic.exists_generator (α := V)
  let vG : PSL2 K := v
  have hzV : Subgroup.zpowers vG = V := by
    apply le_antisymm
    · exact Subgroup.zpowers_le.mpr v.2
    · intro x hx
      rcases hvgen ⟨x, hx⟩ with ⟨n, hn⟩
      exact ⟨n, congrArg Subtype.val hn⟩
  have hvord : orderOf vG = Nat.card V := by
    calc
      orderOf vG = Nat.card (Subgroup.zpowers vG) := (Nat.card_zpowers vG).symm
      _ = Nat.card V := by rw [hzV]
  have hvne : vG ≠ 1 := by
    intro hv1
    have hcard1 : Nat.card V = 1 := by
      rw [← hvord, hv1]
      simp
    rw [hcard1] at hVeven
    norm_num at hVeven
  obtain ⟨T, hvT, _hTuniq⟩ := hpart vG hvne
  have hVleT : V ≤ T := by
    rw [← hzV]
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact T.zpow_mem hvT.1 n
  rcases hVcard with hVminus | hVplus
  · have hTS : ¬ ∃ g, T = S.map (MulAut.conj g).toMonoidHom := by
      intro h
      rcases h with ⟨g, hg⟩
      apply hnotOpposite.1 hVminus
      have hvdiv : orderOf vG ∣ Nat.card T :=
        Subgroup.orderOf_dvd_natCard T hvT.1
      have hVdvdS : Nat.card V ∣ Nat.card S := by
        rw [hg, Subgroup.card_map_of_injective
          (K := S) (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective, hvord] at hvdiv
        exact hvdiv
      exact dvd_trans hpV hVdvdS
    have hTU : ∃ g, T = U.map (MulAut.conj g).toMonoidHom := by
      rcases hvT.2 with hP | hU | hS
      · exfalso
        rcases hP with ⟨g, hg⟩
        have hvP : vG ∈ (P : Subgroup (PSL2 K)).map
            (MulAut.conj g).toMonoidHom := by
          rw [← hg]
          exact hvT.1
        rcases Subgroup.mem_map.mp hvP with ⟨y, hy, hyv⟩
        have hyord : orderOf y = Nat.card V := by
          calc
            orderOf y = orderOf ((MulAut.conj g) y) :=
              ((MulAut.conj g).orderOf_eq y).symm
            _ = orderOf vG := congrArg orderOf hyv
            _ = Nat.card V := hvord
        have hyordP : orderOf (⟨y, hy⟩ : (P : Subgroup (PSL2 K))) =
            Nat.card V := by simpa [Subgroup.orderOf_coe] using hyord
        obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup')
          (⟨y, hy⟩ : (P : Subgroup (PSL2 K)))
        have hpPow : p ∣ r ^ n := by
          rw [← hn, hyordP]
          exact hpV
        have hpr : p ∣ r := (Fact.out : Nat.Prime p).dvd_of_dvd_pow hpPow
        exact hpne ((Nat.prime_dvd_prime_iff_eq
          (Fact.out : Nat.Prime p) hr).mp hpr)
      · exact hU
      · exact (hTS hS).elim
    rcases hTU with ⟨g, hg⟩
    have hTcard : Nat.card T = Nat.card V := by
      rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
        hUcard', hVminus]
    have hVT : V = T := Subgroup.eq_of_le_of_card_ge hVleT (by rw [hTcard])
    have hVconj : V = U.map (MulAut.conj g).toMonoidHom := hVT.trans hg
    have hrestricted := restricted_family_of_huppert_partition P U S hpne
      (hnotOpposite.1 hVminus) hpart
    exact conjugate_base_family_partition U V g hVconj hrestricted
  · have hTU : ¬ ∃ g, T = U.map (MulAut.conj g).toMonoidHom := by
      intro h
      rcases h with ⟨g, hg⟩
      apply hnotOpposite.2 hVplus
      have hvdiv : orderOf vG ∣ Nat.card T :=
        Subgroup.orderOf_dvd_natCard T hvT.1
      have hVdvdU : Nat.card V ∣ Nat.card U := by
        rw [hg, Subgroup.card_map_of_injective
          (K := U) (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective, hvord] at hvdiv
        exact hvdiv
      exact dvd_trans hpV hVdvdU
    have hTS : ∃ g, T = S.map (MulAut.conj g).toMonoidHom := by
      rcases hvT.2 with hP | hU | hS
      · exfalso
        rcases hP with ⟨g, hg⟩
        have hvP : vG ∈ (P : Subgroup (PSL2 K)).map
            (MulAut.conj g).toMonoidHom := by
          rw [← hg]
          exact hvT.1
        rcases Subgroup.mem_map.mp hvP with ⟨y, hy, hyv⟩
        have hyord : orderOf y = Nat.card V := by
          calc
            orderOf y = orderOf ((MulAut.conj g) y) :=
              ((MulAut.conj g).orderOf_eq y).symm
            _ = orderOf vG := congrArg orderOf hyv
            _ = Nat.card V := hvord
        have hyordP : orderOf (⟨y, hy⟩ : (P : Subgroup (PSL2 K))) =
            Nat.card V := by simpa [Subgroup.orderOf_coe] using hyord
        obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup')
          (⟨y, hy⟩ : (P : Subgroup (PSL2 K)))
        have hpPow : p ∣ r ^ n := by
          rw [← hn, hyordP]
          exact hpV
        have hpr : p ∣ r := (Fact.out : Nat.Prime p).dvd_of_dvd_pow hpPow
        exact hpne ((Nat.prime_dvd_prime_iff_eq
          (Fact.out : Nat.Prime p) hr).mp hpr)
      · exact (hTU hU).elim
      · exact hS
    rcases hTS with ⟨g, hg⟩
    have hTcard : Nat.card T = Nat.card V := by
      rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
        hScard', hVplus]
    have hVT : V = T := Subgroup.eq_of_le_of_card_ge hVleT (by rw [hTcard])
    have hVconj : V = S.map (MulAut.conj g).toMonoidHom := hVT.trans hg
    have hrestricted := restricted_family_of_huppert_partition P S U hpne
      (hnotOpposite.2 hVplus) (by
        intro x hx
        obtain ⟨T0, hT0, huniq⟩ := hpart x hx
        refine ⟨T0, ⟨hT0.1, ?_⟩, ?_⟩
        · rcases hT0.2 with hP | hU | hS
          · exact Or.inl hP
          · exact Or.inr (Or.inr hU)
          · exact Or.inr (Or.inl hS)
        · intro T' hT'
          apply huniq T'
          refine ⟨hT'.1, ?_⟩
          rcases hT'.2 with hP | hS | hU
          · exact Or.inl hP
          · exact Or.inr (Or.inr hS)
          · exact Or.inr (Or.inl hU))
    exact conjugate_base_family_partition S V g hVconj hrestricted

/-- The exact quotient torus stored by equation (9) carries Huppert's unique
conjugate-family partition for every odd prime dividing its order. -/
public theorem secondCase_linear_quotientTorus_family_partition
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (torus : SecondCasePSL2QuotientTorusCard d K)
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hpT : p ∣ Nat.card torus.T) :
    ∀ x : d.E ⧸ Subgroup.center d.E, orderOf x = p →
      ∃! T : {T : Subgroup (d.E ⧸ Subgroup.center d.E) //
        ∃ g : d.E ⧸ Subgroup.center d.E,
          T = torus.T.map (MulAut.conj g).toMonoidHom}, x ∈ T.1 := by
  classical
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let e : Q ≃* PSL2 K := torus.modelEquiv.some
  let V : Subgroup (PSL2 K) := torus.T.map e.toMonoidHom
  have hVcyc : IsCyclic V := by
    let eT : torus.T ≃* V := Subgroup.equivMapOfInjective torus.T
      e.toMonoidHom e.injective
    exact (MulEquiv.isCyclic eT).mp torus.T_cyclic
  have hVcard_eq : Nat.card V = Nat.card torus.T :=
    Subgroup.card_map_of_injective e.injective
  have hVeven : Even (Nat.card V) := by
    rw [hVcard_eq]
    exact torus.T_even
  have hVcard : Nat.card V = (Nat.card K - 1) / 2 ∨
      Nat.card V = (Nat.card K + 1) / 2 := by
    simpa [hVcard_eq] using torus.T_card
  have hpV : p ∣ Nat.card V := by simpa [hVcard_eq] using hpT
  have hpartV := selected_half_torus_partition torus.primePower V hVcyc
    hVeven hVcard hpodd hpV
  have htransport := transport_psl2_torus_family_partition e V hpartV
  have hback : V.map e.symm.toMonoidHom = torus.T := by
    dsimp [V]
    rw [Subgroup.map_map]
    convert Subgroup.map_id torus.T using 1
    ext x
    simp
  rw [hback] at htransport
  exact htransport

end CFSG.GorensteinWalter
