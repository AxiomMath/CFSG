module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardH
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalKleinFourIndexThree
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The normalizer in the order-two Brauer--Suzuki--Wall branch

When the abelian subgroup `K` has order two, the involution centralizer `H`
is Klein four.  Its normalizer fuses the three nonidentity elements of `H`,
has `H` as a self-centralizing normal subgroup of index three, and is
therefore isomorphic to `A₄`.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- In the `|K| = 2` branch of the Brauer--Suzuki--Wall hypotheses, the
normalizer of the involution centralizer is isomorphic to `A₄`. -/
public theorem
    BrauerSuzukiWallHypotheses.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2) :
    Nonempty
      (↑(Subgroup.normalizer (h.H : Set G)) ≃*
        alternatingGroup (Fin 4)) := by
  classical
  have hH : IsKleinFour h.H := by
    let T : Subgroup G := Subgroup.zpowers h.t
    let S : Subgroup G := Subgroup.zpowers h.s
    have htOrder : orderOf h.t = 2 :=
      orderOf_eq_prime h.t_involution.2 h.t_involution.1
    have hsOrder : orderOf h.s = 2 :=
      orderOf_eq_prime h.s_involution.2 h.s_involution.1
    have hTcard : Nat.card T = 2 := by
      simp [T, Nat.card_zpowers, htOrder]
    have hScard : Nat.card S = 2 := by
      simp [S, Nat.card_zpowers, hsOrder]
    have hTleK : T ≤ h.K := Subgroup.zpowers_le.mpr h.t_mem_K
    have hTK : T = h.K := by
      apply Subgroup.eq_of_le_of_card_ge hTleK
      rw [hTcard, hk]
    have hst : h.s * h.t * h.s⁻¹ = h.t := by
      rw [h.s_inverts_K h.t h.t_mem_K]
      exact inv_eq_of_mul_eq_one_right (by
        simpa [pow_two] using h.t_involution.2)
    have hsNorm : h.s ∈ Subgroup.normalizer (T : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [hTK] at hx ⊢
        exact h.s_inverts_K x hx ▸ h.K.inv_mem hx
      · intro hx
        rw [hTK] at hx ⊢
        have hss : h.s * h.s = 1 := by
          simpa [pow_two] using h.s_involution.2
        have hsinv : h.s⁻¹ = h.s :=
          inv_eq_of_mul_eq_one_right (by
            simpa [pow_two] using h.s_involution.2)
        have hinv := h.s_inverts_K (h.s * x * h.s⁻¹) hx
        have hdouble : h.s * (h.s * x * h.s⁻¹) * h.s⁻¹ = x := by
          rw [hsinv]
          calc
            h.s * (h.s * x * h.s) * h.s =
                (h.s * h.s) * x * (h.s * h.s) := by group
            _ = x := by rw [hss]; simp
        rw [hdouble.symm.trans hinv]
        exact h.K.inv_mem hx
    have hSNorm : S ≤ Subgroup.normalizer (T : Set G) :=
      Subgroup.zpowers_le.mpr hsNorm
    have htT : h.t ∈ T := Subgroup.mem_zpowers h.t
    have hsS : h.s ∈ S := Subgroup.mem_zpowers h.s
    have htTne : (⟨h.t, htT⟩ : T) ≠ 1 := by
      intro ht
      exact h.t_involution.1 (congrArg Subtype.val ht)
    have hsSne : (⟨h.s, hsS⟩ : S) ≠ 1 := by
      intro hs
      exact h.s_involution.1 (congrArg Subtype.val hs)
    have hTcases : ∀ x : T, x = 1 ∨ x = ⟨h.t, htT⟩ := by
      intro x
      by_cases hx : x = 1
      · exact Or.inl hx
      · rcases (Nat.card_eq_two_iff' (1 : T)).mp hTcard with
          ⟨y, _hy, hyuniq⟩
        exact Or.inr ((hyuniq x hx).trans (hyuniq ⟨h.t, htT⟩ htTne).symm)
    have hScases : ∀ x : S, x = 1 ∨ x = ⟨h.s, hsS⟩ := by
      intro x
      by_cases hx : x = 1
      · exact Or.inl hx
      · rcases (Nat.card_eq_two_iff' (1 : S)).mp hScard with
          ⟨y, _hy, hyuniq⟩
        exact Or.inr ((hyuniq x hx).trans (hyuniq ⟨h.s, hsS⟩ hsSne).symm)
    have hHcard : Nat.card h.H = 4 := by rw [h.card_H, hk]
    have hpow : ∀ x : h.H, x ^ 2 = 1 := by
      intro x
      have hxprod : (x : G) ∈ (T : Set G) * (S : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left T S hSNorm]
        change (x : G) ∈ (T ⊔ S : Subgroup G)
        rw [hTK]
        change (x : G) ∈ h.K ⊔ Subgroup.zpowers h.s
        rw [← h.H_eq_join]
        exact x.property
      rcases hxprod with ⟨a, haT, b, hbS, hab⟩
      let aT : T := ⟨a, haT⟩
      let bS : S := ⟨b, hbS⟩
      rcases hTcases aT with ha | ha
      · have haG : a = 1 := congrArg Subtype.val ha
        rw [haG] at hab
        have hxb : (x : G) = b := hab.symm.trans (one_mul b)
        rcases hScases bS with hb | hb
        · have hbG : b = 1 := congrArg Subtype.val hb
          apply Subtype.ext
          simpa [hxb, hbG]
        · have hbG : b = h.s := congrArg Subtype.val hb
          apply Subtype.ext
          simpa [hxb, hbG, pow_two] using h.s_involution.2
      · have haG : a = h.t := congrArg Subtype.val ha
        rcases hScases bS with hb | hb
        · have hbG : b = 1 := congrArg Subtype.val hb
          apply Subtype.ext
          change (x : G) ^ 2 = 1
          simpa [← hab, haG, hbG, pow_two] using h.t_involution.2
        · have hbG : b = h.s := congrArg Subtype.val hb
          apply Subtype.ext
          change (x : G) ^ 2 = 1
          rw [← hab, haG, hbG, pow_two]
          have htcomm : h.t * h.s = h.s * h.t := by
            symm
            calc
              h.s * h.t = (h.s * h.t * h.s⁻¹) * h.s := by group
              _ = h.t * h.s := by rw [hst]
          calc
            (h.t * h.s) * (h.t * h.s) =
                h.t * (h.s * h.t) * h.s := by group
            _ = h.t * (h.t * h.s) * h.s := by rw [htcomm.symm]
            _ = (h.t * h.t) * (h.s * h.s) := by group
            _ = 1 := by
              rw [show h.t * h.t = 1 by
                    simpa [pow_two] using h.t_involution.2,
                show h.s * h.s = 1 by
                    simpa [pow_two] using h.s_involution.2]
              simp
    have : Nontrivial h.H :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hHcard]; norm_num)
    exact {
      card_four := hHcard
      exponent_two :=
        (Monoid.exponent_eq_prime_iff Nat.prime_two).2 fun x hx ↦
          orderOf_eq_prime (hpow x) hx }
  let : IsKleinFour h.H := hH
  let : IsMulCommutative h.H := IsKleinFour.isMulCommutative
  have hHcard : Nat.card h.H = 4 := hH.card_four
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have htH : h.t ∈ h.H := hKleH h.t_mem_K
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  have hHleN : h.H ≤ N := Subgroup.le_normalizer
  have hHnormalN : (h.H.subgroupOf N).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hHleN).2
    intro x n hxH hnN
    exact (Subgroup.mem_normalizer_iff.mp hnN x).mp hxH
  have hcentH : Subgroup.centralizer (h.H : Set G) = h.H := by
    apply le_antisymm
    · intro x hx
      rw [h.H_eq_centralizer]
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hx) h.t htH).symm
    · exact Subgroup.le_centralizer h.H
  have hcentInv : ∀ {a : G}, a ∈ h.H → IsInvolution a →
      Subgroup.centralizer ({a} : Set G) = h.H := by
    intro a haH haI
    have hHleC : h.H ≤ Subgroup.centralizer ({a} : Set G) := by
      intro x hxH
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val
        ((IsKleinFour.isMulCommutative (G := h.H)).is_comm.comm
          ⟨x, hxH⟩ ⟨a, haH⟩)
    obtain ⟨g, hga⟩ := h.involutions_conjugate a haI
    let Ca : Subgroup G := Subgroup.centralizer ({a} : Set G)
    let Ct : Subgroup G := Subgroup.centralizer ({h.t} : Set G)
    let e : Ca ≃ Ct :=
      { toFun := fun x ↦ ⟨g * (x : G) * g⁻¹, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hxcomm : (x : G) * a = a * (x : G) :=
            Subgroup.mem_centralizer_singleton_iff.mp x.property
          rw [← hga]
          calc
            (g * (x : G) * g⁻¹) * (g * a * g⁻¹) =
                g * ((x : G) * a) * g⁻¹ := by group
            _ = g * (a * (x : G)) * g⁻¹ := by rw [hxcomm]
            _ = (g * a * g⁻¹) * (g * (x : G) * g⁻¹) := by group⟩
        invFun := fun x ↦ ⟨g⁻¹ * (x : G) * g, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hxcomm : (x : G) * h.t = h.t * (x : G) :=
            Subgroup.mem_centralizer_singleton_iff.mp x.property
          have ha : a = g⁻¹ * h.t * g := by
            calc
              a = g⁻¹ * (g * a * g⁻¹) * g := by group
              _ = g⁻¹ * h.t * g := by rw [hga]
          rw [ha]
          calc
            (g⁻¹ * (x : G) * g) * (g⁻¹ * h.t * g) =
                g⁻¹ * ((x : G) * h.t) * g := by group
            _ = g⁻¹ * (h.t * (x : G)) * g := by rw [hxcomm]
            _ = (g⁻¹ * h.t * g) * (g⁻¹ * (x : G) * g) := by group⟩
        left_inv := by intro x; apply Subtype.ext; group
        right_inv := by intro x; apply Subtype.ext; group }
    have hCcard : Nat.card Ca = 4 := by
      calc
        Nat.card Ca = Nat.card Ct := Nat.card_congr e
        _ = Nat.card h.H := by rw [h.H_eq_centralizer]
        _ = 4 := hHcard
    exact (Subgroup.eq_of_le_of_card_ge hHleC (by
      change Nat.card (Subgroup.centralizer ({a} : Set G)) ≤ Nat.card h.H
      rw [show Nat.card (Subgroup.centralizer ({a} : Set G)) = 4 by
        simpa [Ca] using hCcard, hHcard])).symm
  have hconjMemN : ∀ {a g : G}, a ∈ h.H → IsInvolution a →
      g * a * g⁻¹ = h.t → g ∈ N := by
    intro a g haH haI hga
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hxH
      have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := by
        rw [hcentInv haH haI]
        exact hxH
      rw [Subgroup.mem_centralizer_singleton_iff] at hxC
      rw [h.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      rw [← hga]
      calc
        (g * x * g⁻¹) * (g * a * g⁻¹) =
            g * (x * a) * g⁻¹ := by group
        _ = g * (a * x) * g⁻¹ := by rw [hxC]
        _ = (g * a * g⁻¹) * (g * x * g⁻¹) := by group
    · intro hgxH
      have hgxC : g * x * g⁻¹ ∈
          Subgroup.centralizer ({h.t} : Set G) := by
        rw [← h.H_eq_centralizer]
        exact hgxH
      rw [Subgroup.mem_centralizer_singleton_iff] at hgxC
      have hxcomm : x * a = a * x := by
        have hc := congrArg (fun z : G ↦ g⁻¹ * z * g) hgxC
        rw [← hga] at hc
        simpa [mul_assoc] using hc
      rw [← hcentInv haH haI]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxcomm
  let HN : Subgroup N := h.H.subgroupOf N
  have hHNcard : Nat.card HN = 4 := by
    exact
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleN).toEquiv).trans
        hHcard
  have hHNklein : IsKleinFour HN := {
    card_four := hHNcard
    exponent_two := by
      rw [← hH.exponent_two]
      exact Monoid.exponent_eq_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hHleN) }
  let : HN.Normal := hHnormalN
  let : IsKleinFour HN := hHNklein
  have hfusion : ∀ x y : HN, x ≠ 1 → y ≠ 1 →
      ∃ n : N, n * x * n⁻¹ = y := by
    intro x y hx hy
    have hxI : IsInvolution (x : G) := by
      constructor
      · intro hx1
        apply hx
        exact Subtype.ext (Subtype.ext hx1)
      · have hsquare := IsKleinFour.mul_self x
        simpa [pow_two] using
          congrArg (fun z : HN ↦ (((z : N) : G))) hsquare
    have hyI : IsInvolution (y : G) := by
      constructor
      · intro hy1
        apply hy
        exact Subtype.ext (Subtype.ext hy1)
      · have hsquare := IsKleinFour.mul_self y
        simpa [pow_two] using
          congrArg (fun z : HN ↦ (((z : N) : G))) hsquare
    obtain ⟨gx, hgx⟩ := h.involutions_conjugate (x : G) hxI
    obtain ⟨gy, hgy⟩ := h.involutions_conjugate (y : G) hyI
    have hgxN : gx ∈ N := hconjMemN x.property hxI hgx
    have hgyN : gy ∈ N := hconjMemN y.property hyI hgy
    let n : N := ⟨gy⁻¹ * gx, N.mul_mem (N.inv_mem hgyN) hgxN⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    change (gy⁻¹ * gx) * (x : G) * (gy⁻¹ * gx)⁻¹ = (y : G)
    have hyback : (y : G) = gy⁻¹ * h.t * gy := by
      calc
        (y : G) = gy⁻¹ * (gy * (y : G) * gy⁻¹) * gy := by group
        _ = gy⁻¹ * h.t * gy := by rw [hgy]
    rw [hyback, ← hgx]
    group
  let : MulDistribMulAction N HN :=
    MulDistribMulAction.compHom HN (MulAut.conjNormal (H := HN))
  let tN : N := ⟨h.t, hHleN htH⟩
  let tHN : HN := ⟨tN, htH⟩
  let U : Set HN := {x | x ≠ 1}
  have horbit :
      MulAction.orbit N tHN = U := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      change MulAut.conjNormal n tHN ≠ 1
      exact (MulEquiv.map_ne_one_iff (MulAut.conjNormal n)).2 (by
        intro ht1
        exact h.t_involution.1 (by
          simpa [tHN, tN] using
            congrArg (fun z : HN ↦ (((z : N) : G))) ht1))
    · intro hx
      change x ≠ 1 at hx
      obtain ⟨n, hn⟩ :=
        hfusion tHN x
          (by
            intro ht1
            exact h.t_involution.1 (by
              simpa [tHN, tN] using
                congrArg (fun z : HN ↦ (((z : N) : G))) ht1)) hx
      refine ⟨n, ?_⟩
      change MulAut.conjNormal n tHN = x
      apply Subtype.ext
      exact hn
  have hUcard : U.ncard = 3 := by
    have hset : U = Set.univ \ {1} := by ext x; simp [U]
    rw [hset, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ (1 : HN))]
    simpa [hHNcard]
  let St : Subgroup N :=
    MulAction.stabilizer N tHN
  have hSt : St = HN := by
    ext n
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hn
      change MulAut.conjNormal n tHN = tHN at hn
      have hnG : (n : G) * h.t * (n : G)⁻¹ = h.t := by
        simpa [MulAut.conjNormal_apply, tHN, tN] using
          congrArg (fun z : HN ↦ (((z : N) : G))) hn
      have hnCent : (n : G) ∈ Subgroup.centralizer ({h.t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact eq_mul_of_mul_inv_eq hnG
      change (n : G) ∈ h.H
      rw [h.H_eq_centralizer]
      exact hnCent
    · intro hn
      change MulAut.conjNormal n tHN = tHN
      apply Subtype.ext
      apply Subtype.ext
      change (n : G) * h.t * (n : G)⁻¹ = h.t
      have hnCent : (n : G) ∈ Subgroup.centralizer ({h.t} : Set G) := by
        rw [← h.H_eq_centralizer]
        exact hn
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hnCent
      exact mul_inv_eq_of_eq_mul hc
  have hHNindex : HN.index = 3 := by
    rw [← hSt]
    exact
      (MulAction.index_stabilizer N
        tHN).trans (horbit ▸ hUcard)
  have hcentHN : Subgroup.centralizer (HN : Set N) = HN := by
    ext n
    constructor
    · intro hn
      change (n : G) ∈ h.H
      have hnC : (n : G) ∈ Subgroup.centralizer (h.H : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hxH
        let xN : N := ⟨x, hHleN hxH⟩
        have hc :=
          (Subgroup.mem_centralizer_iff.mp hn) xN
            (show xN ∈ HN from hxH)
        exact congrArg Subtype.val hc
      rw [hcentH] at hnC
      exact hnC
    · intro hn
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact congrArg Subtype.val
        ((IsKleinFour.isMulCommutative (G := HN)).is_comm.comm
          ⟨x, hx⟩ ⟨n, hn⟩)
  exact mulEquiv_alternatingGroup_four_of_normal_kleinFour_index_three
    HN hHnormalN hHNklein hcentHN hHNindex

end CFSG.GorensteinWalter
