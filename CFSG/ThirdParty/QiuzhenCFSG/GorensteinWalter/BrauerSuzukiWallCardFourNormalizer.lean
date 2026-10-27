module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardH
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGroupExtension
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The Klein-four normalizer in the order-four Brauer--Suzuki--Wall branch

This is the subgroup-theoretic preamble to Bender's two involution-counting
cases.  The distinguished commuting involutions generate a self-centralizing
Klein four contained in two distinct Sylow two-subgroups.  Its faithful
normalizer action on the three nonidentity elements forces normalizer order
24 and supplies the required subgroup of order three.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem card_sup_eq_mul_of_disjoint_of_le_normalizer_card_four
    {G : Type u} [Group G]
    (A B : Subgroup G)
    (hnormal : B ≤ Subgroup.normalizer (A : Set G))
    (hdisjoint : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩
  have hinjective : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have hsurjective : Function.Surjective toSup := by
    intro z
    have hz : (z : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnormal]
      exact z.2
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinjective, hsurjective⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

private noncomputable def centralizerSingletonMulEquivOfConjEqCardFour
    {G : Type u} [Group G] {a b g : G}
    (hg : g * a * g⁻¹ = b) :
    Subgroup.centralizer ({a} : Set G) ≃*
      Subgroup.centralizer ({b} : Set G) := by
  let e : G ≃* G := MulAut.conj g
  have hmap :
      (Subgroup.centralizer ({a} : Set G)).map e.toMonoidHom =
        Subgroup.centralizer ({b} : Set G) := by
    ext x
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyb : y = b := by simpa using hy
      subst y
      have hxa := Subgroup.mem_centralizer_iff.mp hx a (by simp)
      change b * x = x * b
      rw [← hg]
      have hxa' : a * (g⁻¹ * x * g) = (g⁻¹ * x * g) * a := hxa
      calc
        (g * a * g⁻¹) * x = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * a) * g⁻¹ := by rw [hxa']
        _ = x * (g * a * g⁻¹) := by group
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hya : y = a := by simpa using hy
      subst y
      have hxb := Subgroup.mem_centralizer_iff.mp hx b (by simp)
      change a * (g⁻¹ * x * g) = (g⁻¹ * x * g) * a
      have hxb' : b * x = x * b := hxb
      calc
        a * (g⁻¹ * x * g) =
            g⁻¹ * ((g * a * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (b * x) * g := by rw [hg]
        _ = g⁻¹ * (x * b) * g := by rw [hxb']
        _ = g⁻¹ * (x * (g * a * g⁻¹)) * g := by rw [hg]
        _ = (g⁻¹ * x * g) * a := by group
  exact (Subgroup.centralizer ({a} : Set G)).equivMapOfInjective
      e.toMonoidHom e.injective |>.trans (MulEquiv.subgroupCongr hmap)

private theorem BrauerSuzukiWallHypotheses.standardKleinFour
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    IsKleinFour (Subgroup.zpowers h.t ⊔ Subgroup.zpowers h.s : Subgroup G) := by
  classical
  let T : Subgroup G := Subgroup.zpowers h.t
  let S : Subgroup G := Subgroup.zpowers h.s
  let V : Subgroup G := T ⊔ S
  have htOrder : orderOf h.t = 2 :=
    orderOf_eq_prime h.t_involution.2 h.t_involution.1
  have hsOrder : orderOf h.s = 2 :=
    orderOf_eq_prime h.s_involution.2 h.s_involution.1
  have hTcard : Nat.card T = 2 := by
    simp [T, Nat.card_zpowers, htOrder]
  have hScard : Nat.card S = 2 := by
    simp [S, Nat.card_zpowers, hsOrder]
  have htT : h.t ∈ T := Subgroup.mem_zpowers h.t
  have hsS : h.s ∈ S := Subgroup.mem_zpowers h.s
  have htTne : (⟨h.t, htT⟩ : T) ≠ 1 := by
    intro ht1
    exact h.t_involution.1 (congrArg Subtype.val ht1)
  have hsSne : (⟨h.s, hsS⟩ : S) ≠ 1 := by
    intro hs1
    exact h.s_involution.1 (congrArg Subtype.val hs1)
  have hTeq : ∀ z : T, z = 1 ∨ z = ⟨h.t, htT⟩ := by
    intro z
    by_cases hz : z = 1
    · exact Or.inl hz
    · rcases (Nat.card_eq_two_iff' (1 : T)).mp hTcard with
        ⟨z0, _hz0ne, hz0uniq⟩
      exact Or.inr ((hz0uniq z hz).trans
        (hz0uniq ⟨h.t, htT⟩ htTne).symm)
  have hSeq : ∀ z : S, z = 1 ∨ z = ⟨h.s, hsS⟩ := by
    intro z
    by_cases hz : z = 1
    · exact Or.inl hz
    · rcases (Nat.card_eq_two_iff' (1 : S)).mp hScard with
        ⟨z0, _hz0ne, hz0uniq⟩
      exact Or.inr ((hz0uniq z hz).trans
        (hz0uniq ⟨h.s, hsS⟩ hsSne).symm)
  have hdisjoint : Disjoint T S := by
    rw [Subgroup.disjoint_def]
    intro x hxT hxS
    rcases hTeq ⟨x, hxT⟩ with hx1 | hxt
    · exact congrArg Subtype.val hx1
    · rcases hSeq ⟨x, hxS⟩ with hx1 | hxs
      · exact congrArg Subtype.val hx1
      · exfalso
        apply h.s_not_mem_K
        have hts : h.t = h.s := by
          exact (congrArg Subtype.val hxt).symm.trans
            (congrArg Subtype.val hxs)
        rw [← hts]
        exact h.t_mem_K
  have htCentS : h.t ∈ Subgroup.centralizer ({h.s} : Set G) := by
    have htInf : h.t ∈ h.K ⊓ Subgroup.centralizer ({h.s} : Set G) := by
      rw [h.fixed_subgroup_eq]
      exact Subgroup.mem_zpowers h.t
    exact htInf.2
  have hcomm : Commute h.t h.s := by
    exact (Subgroup.mem_centralizer_iff.mp htCentS h.s (by simp)).symm
  have hsCentT : h.s ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hxT
    rcases hxT with ⟨n, rfl⟩
    exact hcomm.zpow_left n
  have hSNormT : S ≤ Subgroup.normalizer (T : Set G) := by
    apply Subgroup.zpowers_le.mpr
    exact Subgroup.centralizer_le_normalizer (T : Set G) hsCentT
  have hVcard : Nat.card V = 4 := by
    dsimp [V]
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer_card_four T S hSNormT hdisjoint,
      hTcard, hScard]
  have hAllSq : ∀ x : V, x ^ 2 = 1 := by
    intro x
    have hx : (x : G) ∈ (T : Set G) * (S : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left T S hSNormT]
      exact x.property
    rcases hx with ⟨a, haT, b, hbS, hab⟩
    rcases hTeq ⟨a, haT⟩ with ha1 | hat
    · have ha1G : a = 1 := congrArg Subtype.val ha1
      rcases hSeq ⟨b, hbS⟩ with hb1 | hbs
      · have hb1G : b = 1 := congrArg Subtype.val hb1
        apply Subtype.ext
        change (x : G) ^ 2 = 1
        rw [← hab, ha1G, hb1G]
        simp
      · have hbsG : b = h.s := congrArg Subtype.val hbs
        apply Subtype.ext
        change (x : G) ^ 2 = 1
        rw [← hab, ha1G, hbsG]
        simpa using h.s_involution.2
    · have hatG : a = h.t := congrArg Subtype.val hat
      rcases hSeq ⟨b, hbS⟩ with hb1 | hbs
      · have hb1G : b = 1 := congrArg Subtype.val hb1
        apply Subtype.ext
        change (x : G) ^ 2 = 1
        rw [← hab, hatG, hb1G]
        simpa using h.t_involution.2
      · have hbsG : b = h.s := congrArg Subtype.val hbs
        apply Subtype.ext
        have ht2 : h.t * h.t = 1 := by
          simpa [pow_two] using h.t_involution.2
        have hs2 : h.s * h.s = 1 := by
          simpa [pow_two] using h.s_involution.2
        change (x : G) ^ 2 = 1
        rw [← hab, hatG, hbsG, pow_two]
        calc
          h.t * h.s * (h.t * h.s) =
              h.t * (h.s * h.t) * h.s := by group
          _ = h.t * (h.t * h.s) * h.s := by rw [hcomm.eq.symm]
          _ = (h.t * h.t) * (h.s * h.s) := by group
          _ = 1 := by rw [ht2, hs2, one_mul]
  have hVnc : ¬ IsCyclic V := by
    intro hcyc
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
    have hg4 : orderOf g = 4 := hg.trans hVcard
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (hAllSq g)
    rw [hg4] at hdvd
    norm_num at hdvd
  have hV : IsKleinFour V := {
    card_four := hVcard
    exponent_two :=
      (not_isCyclic_iff_exponent_eq_prime Nat.prime_two
        (by simpa using hVcard)).mp hVnc
  }
  simpa [V, T, S] using hV

/-- In the order-four branch, Bender's standard Klein four is self-centralizing,
its normalizer has order twenty-four, and that normalizer contains a subgroup
of order three. -/
public theorem
    BrauerSuzukiWallHypotheses.exists_kleinFour_normalizer_card_twenty_four
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4) :
    ∃ V : Subgroup G,
      IsKleinFour V ∧
      Subgroup.centralizer (V : Set G) = V ∧
      Nat.card (Subgroup.normalizer (V : Set G)) = 24 ∧
      ∃ X : Subgroup G,
        X ≤ Subgroup.normalizer (V : Set G) ∧ Nat.card X = 3 := by
  classical
  let T : Subgroup G := Subgroup.zpowers h.t
  let S : Subgroup G := Subgroup.zpowers h.s
  let V : Subgroup G := T ⊔ S
  let Cs : Subgroup G := Subgroup.centralizer ({h.s} : Set G)
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  have hV : IsKleinFour V := by
    simpa [V, T, S] using h.standardKleinFour
  have hVcard : Nat.card V = 4 := hV.card_four
  have hHcard : Nat.card h.H = 8 := by
    rw [h.card_H, hk]
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have htH : h.t ∈ h.H := hKleH h.t_mem_K
  have hsH : h.s ∈ h.H := by
    rw [h.H_eq_join]
    exact (le_sup_right : Subgroup.zpowers h.s ≤
      h.K ⊔ Subgroup.zpowers h.s) (Subgroup.mem_zpowers h.s)
  have hVleH : V ≤ h.H := by
    dsimp [V, T, S]
    exact sup_le (Subgroup.zpowers_le.mpr htH)
      (Subgroup.zpowers_le.mpr hsH)
  have htCentS : h.t ∈ Cs := by
    have htInf : h.t ∈ h.K ⊓ Subgroup.centralizer ({h.s} : Set G) := by
      rw [h.fixed_subgroup_eq]
      exact Subgroup.mem_zpowers h.t
    exact htInf.2
  have hsCentS : h.s ∈ Cs := by
    change h.s ∈ Subgroup.centralizer ({h.s} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : x = h.s := by simpa using hx
    simp [hx']
  have hVleCs : V ≤ Cs := by
    dsimp [V, T, S]
    exact sup_le (Subgroup.zpowers_le.mpr htCentS)
      (Subgroup.zpowers_le.mpr hsCentS)
  have hCscard : Nat.card Cs = 8 := by
    obtain ⟨g, hgs⟩ := h.involutions_conjugate h.s h.s_involution
    let e := centralizerSingletonMulEquivOfConjEqCardFour hgs
    calc
      Nat.card Cs = Nat.card (Subgroup.centralizer ({h.t} : Set G)) :=
        Nat.card_congr e.toEquiv
      _ = Nat.card h.H := by rw [h.H_eq_centralizer]
      _ = 8 := hHcard
  have hHneCs : h.H ≠ Cs := by
    intro hEq
    have hKleCs : h.K ≤ Cs := hKleH.trans_eq hEq
    have hKleT : h.K ≤ T := by
      intro x hxK
      have hxInf : x ∈ h.K ⊓ Subgroup.centralizer ({h.s} : Set G) :=
        ⟨hxK, hKleCs hxK⟩
      rw [h.fixed_subgroup_eq] at hxInf
      exact hxInf
    have hTleK : T ≤ h.K := Subgroup.zpowers_le.mpr h.t_mem_K
    have hKT : h.K = T := le_antisymm hKleT hTleK
    have hTcard : Nat.card T = 2 := by
      simp [T, Nat.card_zpowers,
        orderOf_eq_prime h.t_involution.2 h.t_involution.1]
    rw [hKT, hTcard] at hk
    omega
  let I : Subgroup G := h.H ⊓ Cs
  have hVleI : V ≤ I := le_inf hVleH hVleCs
  have hVdvdI : Nat.card V ∣ Nat.card I :=
    Subgroup.card_dvd_of_le hVleI
  have hIdvdH : Nat.card I ∣ Nat.card h.H :=
    Subgroup.card_dvd_of_le inf_le_left
  have hIcard_ne_eight : Nat.card I ≠ 8 := by
    intro hI8
    have hIH : I = h.H :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hHcard, hI8])
    have hHleCs : h.H ≤ Cs := by
      rw [← hIH]
      exact inf_le_right
    have hHCs : h.H = Cs :=
      Subgroup.eq_of_le_of_card_ge hHleCs (by rw [hCscard, hHcard])
    exact hHneCs hHCs
  have hIcard : Nat.card I = 4 := by
    rw [hVcard] at hVdvdI
    rw [hHcard] at hIdvdH
    rcases (Nat.dvd_prime_pow Nat.prime_two
      (m := 3) (i := Nat.card I)).mp (by simpa using hIdvdH) with
      ⟨i, hi, hIc⟩
    interval_cases i
    · simp only [pow_zero] at hIc
      norm_num [hIc] at hVdvdI
    · simp only [pow_one] at hIc
      norm_num [hIc] at hVdvdI
    · simpa using hIc
    · norm_num at hIc
      exact False.elim (hIcard_ne_eight hIc)
  have hCentV : Subgroup.centralizer (V : Set G) = V := by
    apply le_antisymm
    · intro x hx
      have hxt : x ∈ Subgroup.centralizer ({h.t} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyt : y = h.t := by simpa using hy
        subst y
        exact Subgroup.mem_centralizer_iff.mp hx h.t
          ((le_sup_left : T ≤ V) (Subgroup.mem_zpowers h.t))
      have hxH : x ∈ h.H := by
        rw [h.H_eq_centralizer]
        exact hxt
      have hxs : x ∈ Cs := by
        change x ∈ Subgroup.centralizer ({h.s} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hys : y = h.s := by simpa using hy
        subst y
        exact Subgroup.mem_centralizer_iff.mp hx h.s
          ((le_sup_right : S ≤ V) (Subgroup.mem_zpowers h.s))
      have hxI : x ∈ I := ⟨hxH, hxs⟩
      have hVI : V = I :=
        Subgroup.eq_of_le_of_card_ge hVleI (by rw [hVcard, hIcard])
      rwa [hVI]
    · intro x hxV
      rw [Subgroup.mem_centralizer_iff]
      intro y hyV
      let : IsKleinFour V := hV
      have hcomm := (IsKleinFour.isMulCommutative (G := V)).is_comm.comm
        (⟨y, hyV⟩ : V) (⟨x, hxV⟩ : V)
      exact congrArg Subtype.val hcomm
  have hVsubHindex : (V.subgroupOf h.H).index = 2 := by
    have hmul := (V.subgroupOf h.H).card_mul_index
    rw [natCard_subgroupOf_eq V h.H hVleH, hVcard, hHcard] at hmul
    omega
  have hHleN : h.H ≤ N := by
    have hnormal : (V.subgroupOf h.H).Normal :=
      Subgroup.normal_of_index_eq_two hVsubHindex
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hVleH).mp hnormal
  have hVsubCsindex : (V.subgroupOf Cs).index = 2 := by
    have hmul := (V.subgroupOf Cs).card_mul_index
    rw [natCard_subgroupOf_eq V Cs hVleCs, hVcard, hCscard] at hmul
    omega
  have hCsleN : Cs ≤ N := by
    have hnormal : (V.subgroupOf Cs).Normal :=
      Subgroup.normal_of_index_eq_two hVsubCsindex
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hVleCs).mp hnormal
  have hNgt : 8 < Nat.card N := by
    by_contra hnot
    have hNle : Nat.card N ≤ 8 := Nat.le_of_not_gt hnot
    have hHN : h.H = N :=
      Subgroup.eq_of_le_of_card_ge hHleN (by simpa [hHcard] using hNle)
    have hCsN : Cs = N :=
      Subgroup.eq_of_le_of_card_ge hCsleN (by simpa [hCscard] using hNle)
    exact hHneCs (hHN.trans hCsN.symm)
  have hVleN : V ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := V))
  let VN : Subgroup N := V.subgroupOf N
  have hVNcard : Nat.card VN = 4 := by
    rw [natCard_subgroupOf_eq V N hVleN, hVcard]
  have hVNnormal : VN.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hVleN).mpr
    exact le_rfl
  have hCentVN : Subgroup.centralizer (VN : Set N) = VN := by
    apply le_antisymm
    · intro x hx
      have hxG : (x : G) ∈ Subgroup.centralizer (V : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hyV
        let yN : N := ⟨y, hVleN hyV⟩
        have hcommN := Subgroup.mem_centralizer_iff.mp hx yN hyV
        exact congrArg Subtype.val hcommN
      rw [hCentV] at hxG
      exact hxG
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      let : IsKleinFour V := hV
      have hcomm := (IsKleinFour.isMulCommutative (G := V)).is_comm.comm
        (⟨(y : G), hy⟩ : V) (⟨(x : G), hx⟩ : V)
      have hcommG : (y : G) * (x : G) = (x : G) * (y : G) :=
        congrArg (fun z : V => (z : G)) hcomm
      exact Subtype.ext hcommG
  let : VN.Normal := hVNnormal
  obtain ⟨phi, hphi⟩ := quotient_centralizer_mulAut_embedding VN
  let eQ : (N ⧸ VN) ≃* (N ⧸ Subgroup.centralizer (VN : Set N)) :=
    QuotientGroup.quotientMulEquivOfEq hCentVN.symm
  let phiV : (N ⧸ VN) →* MulAut VN := phi.comp eQ.toMonoidHom
  have hphiV : Function.Injective phiV := hphi.comp eQ.injective
  let Omega : Type u := {x : VN // x ≠ (1 : VN)}
  have hOmegaCard : Nat.card Omega = 3 := by
    dsimp [Omega]
    have hcardT : Nat.card (SubMulAction.ofStabilizer VN (1 : VN)) + 1 =
        Nat.card VN :=
      SubMulAction.nat_card_ofStabilizer_add_one_eq VN (1 : VN)
    change Nat.card {x : VN // x ∉ ({1} : Set VN)} + 1 = Nat.card VN at hcardT
    have hcardT' : Nat.card {x : VN // x ≠ (1 : VN)} + 1 = Nat.card VN := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hcardT
    have hsub := Nat.eq_sub_of_add_eq hcardT'
    simpa [hVNcard] using hsub
  let autToPerm : MulAut VN →* Equiv.Perm Omega :=
    { toFun := fun f =>
        ((MulAut.toPerm VN) f).subtypePerm (fun x => by
          change f x ≠ (1 : VN) ↔ x ≠ (1 : VN)
          rw [f.map_ne_one_iff])
      map_one' := by
        ext x
        rfl
      map_mul' := by
        intro f g
        ext x
        rfl }
  have hAutToPermInj : Function.Injective autToPerm := by
    intro f g hfg
    apply MulEquiv.ext
    intro z
    by_cases hz : z = 1
    · simp [hz, f.map_one, g.map_one]
    · let zOmega : Omega := ⟨z, hz⟩
      have hval := DFunLike.congr_fun hfg zOmega
      exact congrArg Subtype.val hval
  let psi : (N ⧸ VN) →* Equiv.Perm Omega := autToPerm.comp phiV
  have hpsi : Function.Injective psi := hAutToPermInj.comp hphiV
  have hQdvd : Nat.card (N ⧸ VN) ∣ 6 := by
    have hdvd := Subgroup.card_dvd_of_injective psi hpsi
    let : Fintype Omega := Fintype.ofFinite Omega
    have hPermCard : Nat.card (Equiv.Perm Omega) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm,
        ← Nat.card_eq_fintype_card, hOmegaCard]
      norm_num
    rw [hPermCard] at hdvd
    exact hdvd
  have hNcardFactor :
      Nat.card N = Nat.card (N ⧸ VN) * 4 := by
    simpa [hVNcard] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup VN)
  have hEightDvdN : 8 ∣ Nat.card N := by
    simpa [hHcard] using Subgroup.card_dvd_of_le hHleN
  have hQgt : 2 < Nat.card (N ⧸ VN) := by
    by_contra hnot
    have hQle : Nat.card (N ⧸ VN) ≤ 2 := Nat.le_of_not_gt hnot
    rw [hNcardFactor] at hNgt
    omega
  have hQeven : 2 ∣ Nat.card (N ⧸ VN) := by
    rw [hNcardFactor] at hEightDvdN
    obtain ⟨c, hc⟩ := hEightDvdN
    refine ⟨c, ?_⟩
    omega
  have hQcard : Nat.card (N ⧸ VN) = 6 := by
    have hQle : Nat.card (N ⧸ VN) ≤ 6 :=
      Nat.le_of_dvd (by norm_num) hQdvd
    interval_cases hq : Nat.card (N ⧸ VN)
    · norm_num [hq] at hQeven
    · norm_num [hq] at hQdvd
    · norm_num [hq] at hQeven
    · rfl
  have hNcard : Nat.card N = 24 := by
    rw [hNcardFactor, hQcard]
  let : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨XN, hXNcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := N) 3 (n := 1) (by
      rw [hNcard]
      norm_num)
  let X : Subgroup G := XN.map N.subtype
  have hXleN : X ≤ N := Subgroup.map_subtype_le XN
  have hXcard : Nat.card X = 3 := by
    let eXN : XN ≃* X :=
      XN.equivMapOfInjective N.subtype Subtype.coe_injective
    calc
      Nat.card X = Nat.card XN := (Nat.card_congr eXN.toEquiv).symm
      _ = 3 := by simpa using hXNcard
  refine ⟨V, hV, hCentV, ?_, X, ?_, hXcard⟩
  · simpa [N] using hNcard
  · simpa [N] using hXleN

end CFSG.GorensteinWalter
