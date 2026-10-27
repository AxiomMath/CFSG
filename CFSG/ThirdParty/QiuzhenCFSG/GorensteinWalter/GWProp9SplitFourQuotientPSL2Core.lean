module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Split-four quotient transport: `C'(Z)` equality across `G/O₂'(G)`

This module contains the quotient-transport step needed by the split-four
quotient classification lane.  Given a Klein four subgroup `Z` whose
normalizer equals `C'(Z)` in `G`, the same equality holds for the image of
`Z` in `G/O₂'(G)`, provided `Z` meets the odd core trivially.

The proof reduces the normalizer preimage `P` of the image of `Z` to the
semidirect product of the odd core `O` by `Z`, and uses Schur--Zassenhaus
complement conjugacy inside `P` to lift each normalizer element of the image
to a representative in `N_G(Z)` lying in the same `O`-coset.  The original
equality then gives that representative's square centralizes `Z`, and the
same square-centralizing condition descends to the quotient.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

private lemma subgroup_of_complement_of_disjoint_sup
    {G : Type u} [Group G] (P O K : Subgroup G) [O.Normal]
    (hOP : O ≤ P) (hKP : K ≤ P)
    (hdisj : Disjoint O K) (hsup : O ⊔ K = P) :
    (O.subgroupOf P).IsComplement' (K.subgroupOf P) := by
  haveI : (O.subgroupOf P).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := P) (N := O)
      (Subgroup.le_normalizer_of_normal (H := O) (K := P))
  have hsup' : O.subgroupOf P ⊔ K.subgroupOf P = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hOP hKP, hsup, Subgroup.subgroupOf_self]
  have hdisj' : Disjoint (O.subgroupOf P) (K.subgroupOf P) := by
    rw [disjoint_iff]
    apply le_bot_iff.mp
    intro x hx
    have hxO : (x : G) ∈ O := hx.1
    have hxK : (x : G) ∈ K := hx.2
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
      hdisj.le_bot ⟨hxO, hxK⟩
    rw [Subgroup.mem_bot]
    exact Subtype.ext hxbot
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj' ?_
  rw [← Subgroup.normal_mul (N := O.subgroupOf P) (H := K.subgroupOf P), hsup']
  simp

/-- The `C'(Z) = N(Z)` equality is preserved by the odd-core quotient
`G → G/O₂'(G)` for a Klein four subgroup `Z` disjoint from `O₂'(G)`. -/
public theorem cPrime_eq_normalizer_of_quotient_pPrimeCore
    {G : Type u} [Group G] [Finite G]
    (Z : Subgroup G) (hZ : IsKleinFour Z)
    (hdisj : Disjoint (pPrimeCore 2 G) Z)
    (h : cPrime Z = (Subgroup.normalizer (Z : Set G) : Set G)) :
    cPrime (Z.map (QuotientGroup.mk' (pPrimeCore 2 G))) =
      (Subgroup.normalizer ((Z.map (QuotientGroup.mk' (pPrimeCore 2 G)) : Subgroup (G ⧸ pPrimeCore 2 G)) : Set (G ⧸ pPrimeCore 2 G))) := by
  classical
  let O : Subgroup G := pPrimeCore 2 G
  let q : G →* G ⧸ O := QuotientGroup.mk' O
  let Zbar : Subgroup (G ⧸ O) := Z.map q
  let P : Subgroup G := Zbar.comap q
  have hOleP : O ≤ P := by
    intro x hx
    apply Subgroup.mem_comap.mpr
    have hx1 : q x = 1 := by
      dsimp [q]
      have hxker : x ∈ q.ker := by
        dsimp [q]
        rwa [QuotientGroup.ker_mk']
      exact MonoidHom.mem_ker.mp hxker
    simp [Zbar, hx1]
  have hZleP : Z ≤ P := by
    intro x hx
    apply Subgroup.mem_comap.mpr
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  haveI : O.Normal := by dsimp [O]; infer_instance
  let O' : Subgroup P := O.subgroupOf P
  let Z' : Subgroup P := Z.subgroupOf P
  have hOZcomp : O'.IsComplement' Z' := by
    have hsupOZ : O ⊔ Z = P := by
      apply le_antisymm
      · exact sup_le hOleP hZleP
      · intro x hx
        rcases Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx) with ⟨z, hz, hxz⟩
        exact (Subgroup.mem_sup_of_normal_left (s := O) (t := Z) (x := x)).mpr
          ⟨x * z⁻¹, by
            dsimp [q] at hxz
            rw [← QuotientGroup.ker_mk' (N := O)]
            rw [MonoidHom.mem_ker]
            dsimp [q]
            rw [hxz]
            simp, z, hz, inv_mul_cancel_right x z⟩
    exact subgroup_of_complement_of_disjoint_sup P O Z hOleP hZleP hdisj hsupOZ
  have hOidx : O'.index = 4 := by
    rw [Subgroup.IsComplement'.index_eq_card (hOZcomp.symm)]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleP).toEquiv).trans hZ.card_four
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))
  have hOodd' : Odd (Nat.card O') := by
    have hc : Nat.card O' = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOleP).toEquiv
    rwa [hc]
  have hcop : Nat.Coprime (Nat.card O') O'.index := by
    rw [hOidx]
    have hc2 : Nat.Coprime 2 (Nat.card O') := Nat.coprime_two_left.mpr hOodd'
    exact Nat.Coprime.symm (hc2.pow_left 2)
  ext y
  constructor
  · intro hy
    exact hy.1
  · intro hy
    refine ⟨hy, ?_⟩
    rcases (QuotientGroup.mk'_surjective O) y with ⟨g, hgy⟩
    let K : Subgroup G := Z.map (MulAut.conj g).toMonoidHom
    have hqg : q g ∈ Subgroup.normalizer (Zbar : Set (G ⧸ O)) := by
      change QuotientGroup.mk' O g ∈ Subgroup.normalizer (Zbar : Set (G ⧸ O))
      rw [hgy]
      simpa [Zbar, q] using hy
    have hqK : K.map q = Zbar := by
      rw [Subgroup.map_map]
      have hcomp : q.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj (q g)).toMonoidHom.comp q := by
        ext a
        simp [MulAut.conj_apply]
      rw [hcomp, ← Subgroup.map_map]
      exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := Zbar) (g := q g)).mp hqg
    have hKleP : K ≤ P := by
      intro x hx
      apply Subgroup.mem_comap.mpr
      rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
      change q (g * z * g⁻¹) ∈ Zbar
      have hzbar : q z ∈ Zbar := Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      have hzbar' : q g * q z * (q g)⁻¹ ∈ Zbar :=
        (Subgroup.mem_normalizer_iff.mp hqg (q z)).mp hzbar
      rw [map_mul, map_mul, map_inv]
      exact hzbar'
    have hKcard : Nat.card K = 4 := by
      let e : Z ≃* K :=
        Subgroup.equivMapOfInjective Z (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      calc
        Nat.card K = Nat.card Z := (Nat.card_congr e.toEquiv).symm
        _ = 4 := hZ.card_four
    have hcopKO : Nat.Coprime (Nat.card K) (Nat.card O) := by
      rw [hKcard]
      have hc2 : Nat.Coprime 2 (Nat.card O) := Nat.coprime_two_left.mpr hOodd
      simpa using (hc2.pow_left 2)
    have hdisjOK : Disjoint O K :=
      (Subgroup.disjoint_of_coprime_natCard hcopKO).symm
    have hsupOK : O ⊔ K = P := by
      apply le_antisymm
      · exact sup_le hOleP hKleP
      · intro x hx
        have hxq : q x ∈ K.map q := by
          rw [hqK]
          exact Subgroup.mem_comap.mp hx
        rcases Subgroup.mem_map.mp hxq with ⟨k, hk, hxk⟩
        exact (Subgroup.mem_sup_of_normal_left (s := O) (t := K) (x := x)).mpr
          ⟨x * k⁻¹, by
            rw [← QuotientGroup.ker_mk' (N := O)]
            rw [MonoidHom.mem_ker]
            dsimp [q]
            dsimp [q] at hxk
            rw [hxk]
            simp, k, hk, inv_mul_cancel_right x k⟩
    let K' : Subgroup P := K.subgroupOf P
    have hOKcomp : O'.IsComplement' K' :=
      subgroup_of_complement_of_disjoint_sup P O K hOleP hKleP hdisjOK hsupOK
    haveI : O'.Normal := by
      exact Subgroup.normal_subgroupOf_of_le_normalizer (H := P) (N := O)
        (Subgroup.le_normalizer_of_normal (H := O) (K := P))
    rcases SchurZassenhaus.complements_conjugate_of_coprime O' Z' K'
        inferInstance hOZcomp hOKcomp hcop with ⟨u, hu⟩
    rcases SchurZassenhaus.exists_mem_normal_conjugator (N := O') (H := Z') (K := K')
        hOZcomp hu with ⟨n, hn⟩
    let nG : G := (n : P)
    have hqng : q nG = 1 := by
      have hnO : nG ∈ O :=
        Subgroup.mem_subgroupOf.mp (show (n : P) ∈ O' from n.property)
      have hxker : nG ∈ q.ker := by
        dsimp [q]
        rwa [QuotientGroup.ker_mk']
      exact MonoidHom.mem_ker.mp hxker
    have hnormZ : nG⁻¹ * g ∈ Subgroup.normalizer (Z : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        have hK : g * a * g⁻¹ ∈ K := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
        have hK' : (⟨g * a * g⁻¹, hKleP hK⟩ : P) ∈ K' := hK
        rw [hn] at hK'
        rcases Subgroup.mem_map.mp hK' with ⟨b, hb, hb_eq⟩
        have hbZ : (b : G) ∈ Z := hb
        have hconj : nG * (b : G) * nG⁻¹ = g * a * g⁻¹ := by
          apply congrArg Subtype.val hb_eq
        have hgoal : nG⁻¹ * (g * a * g⁻¹) * nG ∈ Z := by
          rw [← hconj]
          group
          exact hbZ
        have htarget : (nG⁻¹ * g) * a * (nG⁻¹ * g)⁻¹ =
            nG⁻¹ * (g * a * g⁻¹) * nG := by group
        rw [htarget]
        exact hgoal
      · intro ha
        let x : G := (nG⁻¹ * g) * a * (nG⁻¹ * g)⁻¹
        have hxZ : x ∈ Z := ha
        have hxP : x ∈ P := hZleP hxZ
        let xP : P := ⟨x, hxP⟩
        have hK' : (⟨nG * x * nG⁻¹, by
            let nP : P := n
            exact P.mul_mem (P.mul_mem nP.2 xP.2) (P.inv_mem nP.2)
          ⟩ : P) ∈ K' := by
          rw [hn]
          exact Subgroup.mem_map.mpr ⟨xP, hxZ, rfl⟩
        have hKmem : nG * x * nG⁻¹ ∈ K := Subgroup.mem_subgroupOf.mp hK'
        have hEq : g * a * g⁻¹ = nG * x * nG⁻¹ := by
          dsimp [x]
          group
        have hKmem' : g * a * g⁻¹ ∈ K := by rwa [← hEq] at hKmem
        rcases Subgroup.mem_map.mp hKmem' with ⟨b, hbZ, hb_eq⟩
        have haeq : a = b := by
          have hb_eq' : (MulAut.conj g) b = (MulAut.conj g) a := by
            simpa [MulAut.conj_apply] using hb_eq
          exact ((MulAut.conj g).injective hb_eq').symm
        rwa [haeq]
    have hcP : nG⁻¹ * g ∈ cPrime Z := by
      rw [h]
      exact hnormZ
    have hsq : (nG⁻¹ * g) ^ 2 ∈ Subgroup.centralizer (Z : Set G) := hcP.2
    rw [Subgroup.mem_centralizer_iff]
    intro zbar hzbar
    rcases Subgroup.mem_map.mp hzbar with ⟨z, hz, hzbar_eq⟩
    have hyq : q (nG⁻¹ * g) = y := by
      calc
        q (nG⁻¹ * g) = q (nG⁻¹) * q g := by rw [map_mul]
        _ = (q nG)⁻¹ * q g := by rw [map_inv]
        _ = y := by rw [hqng, hgy]; simp
    have hcent := (Subgroup.mem_centralizer_iff.mp hsq) z hz
    have hzbar' : q z = zbar := hzbar_eq
    calc
      zbar * y ^ 2 = q z * y ^ 2 := by rw [hzbar']
      _ = q z * q ((nG⁻¹ * g) ^ 2) := by rw [map_pow, hyq]
      _ = q (z * (nG⁻¹ * g) ^ 2) := by rw [map_mul]
      _ = q ((nG⁻¹ * g) ^ 2 * z) := by rw [hcent.symm]
      _ = q ((nG⁻¹ * g) ^ 2) * q z := by rw [map_mul]
      _ = y ^ 2 * zbar := by rw [map_pow, hyq, hzbar']

end CFSG.GorensteinWalter
