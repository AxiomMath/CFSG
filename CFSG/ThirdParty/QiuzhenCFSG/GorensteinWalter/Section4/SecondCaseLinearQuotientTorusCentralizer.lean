module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPSL2TorusFamily
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2QuotientTorusReflection
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private lemma zpow_eq_one_or_self_of_sq_eq_one_qtc
    {H : Type u} [Group H] {t : H}
    (ht : t * t = 1) (k : ℤ) : t ^ k = 1 ∨ t ^ k = t := by
  by_cases ht1 : t = 1
  · left
    simp [ht1]
  · have hord : orderOf t = 2 :=
      (orderOf_eq_prime_iff (x := t)).2 ⟨by simpa [pow_two] using ht, ht1⟩
    rw [← zpow_mod_orderOf, hord]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      change k % (2 : ℤ) = 0 at hk
      simp [hk]
    · right
      change k % (2 : ℤ) = 1 at hk
      simp [hk]

private lemma orderOf_eq_prime_of_mem_qtc
    {H : Type u} [Group H] {p : ℕ} [Fact p.Prime]
    {R : Subgroup H} (hRcard : Nat.card R = p) {x : H}
    (hxR : x ∈ R) (hx1 : x ≠ 1) : orderOf x = p := by
  have hdvd : orderOf x ∣ p := by
    simpa [hRcard] using Subgroup.orderOf_dvd_natCard R hxR
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp
  · exact (hx1 (orderOf_eq_one_iff.mp h1)).elim
  · exact hp

/-- An order-`p` subgroup of the selected quotient torus has the full torus
as its centralizer.  The unique Huppert torus family forces its centralizer
into the torus normalizer, while the reflected-dihedral action excludes the
nontrivial normalizer coset because `p` is odd. -/
public theorem secondCase_linear_quotientTorus_centralizer_orderP
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (torus : SecondCasePSL2QuotientTorusCard d K)
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p)
    (R : Subgroup (d.E ⧸ Subgroup.center d.E))
    (hRleT : R ≤ torus.T) (hRcard : Nat.card R = p) :
    Subgroup.centralizer (R : Set (d.E ⧸ Subgroup.center d.E)) = torus.T := by
  classical
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let T : Subgroup Q := torus.T
  have hpT : p ∣ Nat.card T := by
    simpa [T, hRcard] using Subgroup.card_dvd_of_le hRleT
  have hpart := secondCase_linear_quotientTorus_family_partition
    c w d K torus hpodd hpT
  obtain ⟨s, hsI, hsnotT, hinvT, _hCt⟩ :=
    secondCase_psl2_quotient_torus_reflection c w d K torus
  have hsNorm : s ∈ Subgroup.normalizer (T : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hinvT x hx]
      exact T.inv_mem hx
    · intro hx
      have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
      have hsInv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
      have hback : s * (s * x * s⁻¹) * s⁻¹ = x := by
        rw [hsInv]
        calc
          s * (s * x * s) * s = (s * s) * x * (s * s) := by group
          _ = x := by rw [hs2]; simp
      have hy := hinvT (s * x * s⁻¹) hx
      rw [hback] at hy
      rw [hy]
      exact T.inv_mem hx
  let Zs : Subgroup Q := Subgroup.zpowers s
  have hZsLeN : Zs ≤ Subgroup.normalizer (T : Set Q) :=
    Subgroup.zpowers_le.mpr hsNorm
  have hjoinLeN : T ⊔ Zs ≤ Subgroup.normalizer (T : Set Q) :=
    sup_le Subgroup.le_normalizer hZsLeN
  have hjoinCard : Nat.card (↥(T ⊔ Zs)) = 2 * Nat.card (↥T) := by
    rw [show T = torus.T from rfl, show Zs = Subgroup.zpowers s from rfl]
    rw [← torus.T_centralizer_card]
    exact congrArg (fun H : Subgroup Q => Nat.card H) _hCt.symm
  have hjoinEqN : T ⊔ Zs = Subgroup.normalizer (T : Set Q) := by
    apply Subgroup.eq_of_le_of_card_ge hjoinLeN
    rw [torus.T_normalizer_card, hjoinCard]
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hc : Nat.card R = 1 := by rw [hbot]; simp
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨x, hxR, hx1⟩ : ∃ x : Q, x ∈ R ∧ x ≠ 1 := by
    by_contra h
    apply hRne
    apply le_bot_iff.mp
    intro x hx
    apply Subgroup.mem_bot.mpr
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  have hxord : orderOf x = p :=
    orderOf_eq_prime_of_mem_qtc hRcard hxR hx1
  have hxT : x ∈ T := hRleT hxR
  apply le_antisymm
  · intro y hy
    have hyNorm : y ∈ Subgroup.normalizer (T : Set Q) := by
      let Ty : Subgroup Q := T.map (MulAut.conj y).toMonoidHom
      have hTyFam : ∃ g : Q, Ty = T.map (MulAut.conj g).toMonoidHom := ⟨y, rfl⟩
      have hTFam : ∃ g : Q, T = T.map (MulAut.conj g).toMonoidHom := by
        refine ⟨1, ?_⟩
        ext z
        simp
      have hcomm : y * x = x * y :=
        ((Subgroup.mem_centralizer_iff.mp hy) x hxR).symm
      have hxTy : x ∈ Ty := by
        exact Subgroup.mem_map.mpr ⟨x, hxT, by
          change y * x * y⁻¹ = x
          calc
            y * x * y⁻¹ = x * y * y⁻¹ := by rw [hcomm]
            _ = x := by simp⟩
      obtain ⟨T0, hxT0, huniq⟩ := hpart x hxord
      have hTyEq0 : (⟨Ty, hTyFam⟩ : {U : Subgroup Q // ∃ g : Q,
          U = T.map (MulAut.conj g).toMonoidHom}) = T0 := huniq _ hxTy
      have hTEq0 : (⟨T, hTFam⟩ : {U : Subgroup Q // ∃ g : Q,
          U = T.map (MulAut.conj g).toMonoidHom}) = T0 := huniq _ hxT
      have hTyEq : Ty = T := congrArg Subtype.val (hTyEq0.trans hTEq0.symm)
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have hzTy : y * z * y⁻¹ ∈ Ty :=
          Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
        rwa [hTyEq] at hzTy
      · intro hz
        have hzTy : y * z * y⁻¹ ∈ Ty := by rwa [hTyEq]
        rcases Subgroup.mem_map.mp hzTy with ⟨a, haT, hay⟩
        have haz : a = z := (MulAut.conj y).injective hay
        rwa [← haz]
    have hyJoin : y ∈ T ⊔ Zs := by
      rw [hjoinEqN]
      exact hyNorm
    have hyProd : y ∈ (T : Set Q) * (Zs : Set Q) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left T Zs hZsLeN]
      exact hyJoin
    rcases hyProd with ⟨a, haT, b, hbZs, hab⟩
    rcases Subgroup.mem_zpowers_iff.mp hbZs with ⟨n, hn⟩
    have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
    rcases zpow_eq_one_or_self_of_sq_eq_one_qtc hs2 n with hn1 | hns
    · have hb1 : b = 1 := hn.symm.trans hn1
      rw [← hab, hb1]
      simpa using haT
    · have hbs : b = s := hn.symm.trans hns
      have hax : Commute a x := by
        let : IsCyclic T := torus.T_cyclic
        let : CommGroup T := IsCyclic.commGroup
        exact congrArg Subtype.val
          (show (⟨a, haT⟩ : T) * ⟨x, hxT⟩ = ⟨x, hxT⟩ * ⟨a, haT⟩ by
            exact mul_comm _ _)
      have hyConj : y * x * y⁻¹ = x := by
        have hxy : x * y = y * x :=
          (Subgroup.mem_centralizer_iff.mp hy) x hxR
        calc
          y * x * y⁻¹ = x * y * y⁻¹ := by rw [hxy]
          _ = x := by simp
      have hyInv : y * x * y⁻¹ = x⁻¹ := by
        rw [← hab, hbs]
        calc
          (a * s) * x * (a * s)⁻¹ = a * (s * x * s⁻¹) * a⁻¹ := by group
          _ = a * x⁻¹ * a⁻¹ := by rw [hinvT x hxT]
          _ = x⁻¹ := by
            rw [hax.inv_right.eq]
            simp
      have hxxinv : x = x⁻¹ := hyConj.symm.trans hyInv
      have hx2 : x ^ 2 = 1 := by
        calc
          x ^ 2 = x * x := by rw [pow_two]
          _ = x * x⁻¹ := congrArg (fun z : Q => x * z) hxxinv
          _ = 1 := by simp
      have hpdiv2 : p ∣ 2 := by
        rw [← hxord]
        exact orderOf_dvd_of_pow_eq_one hx2
      have hp2 : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hpdiv2
      have hodd2 : Odd 2 := hp2 ▸ hpodd
      norm_num at hodd2
  · intro y hyT
    rw [Subgroup.mem_centralizer_iff]
    intro x hxR'
    have hxT' : x ∈ T := hRleT hxR'
    let : IsCyclic T := torus.T_cyclic
    let : CommGroup T := IsCyclic.commGroup
    exact congrArg Subtype.val
      (show (⟨x, hxT'⟩ : T) * ⟨y, hyT⟩ = ⟨y, hyT⟩ * ⟨x, hxT'⟩ by
        exact mul_comm _ _)

end CFSG.GorensteinWalter
