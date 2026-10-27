module

public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepZpowersInf
public import CFSG.LocalAnalysis.StandardType.GGE6DepNormalizerOfConj
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem isElemAbelian_closure_pair_aux {p : ℕ} {b e : G} (hb : b ^ p = 1)
    (he : e ^ p = 1) (hbe : Commute b e) :
    IsElemAbelian p (Subgroup.closure ({b, e} : Set G)) := by
  have hpair : ({b, e} : Set G).Pairwise Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    all_goals first | exact hbe | exact hbe.symm | exact Commute.refl b | exact Commute.refl e
  haveI hcomm : IsMulCommutative ↥(Subgroup.closure ({b, e} : Set G)) :=
    Subgroup.isMulCommutative_closure hpair
  refine ⟨hcomm, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem a ha =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with ha | ha
      · rw [ha]; exact hb
      · rw [ha]; exact he
  | one => simp
  | mul a c ha hc iha ihc =>
      have hac : a * c = c * a :=
        congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(Subgroup.closure ({b, e} : Set G)))
          (⟨c, hc⟩ : ↥(Subgroup.closure ({b, e} : Set G))))
      rw [Commute.mul_pow hac, iha, ihc, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

private theorem mem_zpowers_of_mem_centralizer_of_commute_of_pow_eq_one {p : ℕ} (hp : p.Prime)
    {L : Subgroup G} {x c : G} (hxp : x ^ p = 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    (hx1 : x ≠ 1) (hcp : c ^ p = 1) (hcC : c ∈ Subgroup.centralizer (L : Set G))
    (hcx : Commute x c) : c ∈ Subgroup.zpowers x := by
  have hE : IsElemAbelian p (Subgroup.closure ({x, c} : Set G)) :=
    isElemAbelian_closure_pair_aux hxp hcp hcx
  have hxE : x ∈ Subgroup.closure ({x, c} : Set G) := Subgroup.subset_closure (by simp)
  have h := inf_centralizer_eq_zpowers_of_elemAbelian hp hE hxE hx1 hLx hcyc
  have hmem : c ∈ Subgroup.closure ({x, c} : Set G) ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨Subgroup.subset_closure (by simp), hcC⟩
  rw [h] at hmem
  exact hmem

theorem ggE6Dep_hZ {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hxL : x ∉ L) :
    ¬ p ∣ Nat.card ↥(Subgroup.center ↥L) := by
  intro hdiv
  obtain ⟨hp, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hcyc := hS.2.2.2.2
  have hxp : x ^ p = 1 := hBs.2 x hxB
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' p hdiv
  let z' : G := ((z : ↥L) : G)
  have hz'ord : orderOf z' = p := by
    change orderOf (((z : ↥L) : G)) = p
    rw [Subgroup.orderOf_coe (z : ↥L), Subgroup.orderOf_coe z, hzord]
  have hz'p : z' ^ p = 1 := by
    rw [← hz'ord]
    exact pow_orderOf_eq_one z'
  have hz'C : z' ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := Subgroup.mem_center_iff.mp z.2 (⟨l, hl⟩ : ↥L)
    have h' := congrArg (fun w : ↥L => (w : G)) h
    simpa [z'] using h'
  have hz'L : z' ∈ L := (z : ↥L).2
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := mem_centralizer_of_le_centralizer hLx
  have hz'x : Commute x z' := by
    have h := Subgroup.mem_centralizer_iff.mp hxC z' hz'L
    exact h.symm
  have hz'zp : z' ∈ Subgroup.zpowers x :=
    mem_zpowers_of_mem_centralizer_of_commute_of_pow_eq_one hp hxp hLx hcyc hx1 hz'p hz'C hz'x
  have hzx : Subgroup.zpowers z' ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hz'zp
  have hcard_eq : Nat.card (Subgroup.zpowers x) = Nat.card (Subgroup.zpowers z') := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hcfg.orderOf_x, hz'ord]
  have heq : Subgroup.zpowers z' = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hzx (le_of_eq hcard_eq)
  have hx_zp : x ∈ Subgroup.zpowers z' := by
    rw [heq]; exact Subgroup.mem_zpowers x
  exact hxL (Subgroup.zpowers_le.mpr hz'L hx_zp)

theorem ggE6Dep_hBsL {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hp : p = 3) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Z : Subgroup ↥L} (hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5)
    (hmodel : GGE6ThreeWeylModel Z (ggGamma L hBsN).range) :
    ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k := by
  subst hp
  obtain ⟨hp, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hcyc := hS.2.2.2.2
  have hxp : x ^ 3 = 1 := hBs.2 x hxB
  have hxord : orderOf x = 3 := hcfg.orderOf_x
  let A : Subgroup (MulAut ↥L) := (ggGamma L hBsN).range
  have hcardA : Nat.card A = 3 ^ 5 := hcard
  obtain ⟨Φ, T, w, hΦinj, hΦrange, hTcomm, hZT, hAT, hwT, hwAT, hwrefl, hnine, hN, hNα, hodd⟩ :=
    hmodel
  have hΦne : Φ.range ≠ ⊤ := by
    intro htop
    have h1 : Nat.card A = Nat.card Φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv
    have h2 : Nat.card Φ.range = Nat.card (Multiplicative (Fin 6 → ZMod 3)) := by
      rw [htop, Subgroup.card_top]
    have h3 : Nat.card (Multiplicative (Fin 6 → ZMod 3)) = 3 ^ 6 := by
      rw [Nat.card_congr (Multiplicative.toAdd (α := Fin 6 → ZMod 3)), Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    have : (3 : ℕ) ^ 5 = 3 ^ 6 := by rw [← hcardA, h1, h2, h3]
    norm_num at this
  have hrangeE6 : ∀ y, Multiplicative.ofAdd y ∈ Φ.range ↔ y ∈ NoOffRest.hypE6 :=
    hΦrange.resolve_left hΦne
  intro b hb
  let a : A := ⟨(ggGamma L hBsN) ⟨b, hb⟩, MonoidHom.mem_range.mpr ⟨⟨b, hb⟩, rfl⟩⟩
  have ha_val : (a : MulAut ↥L) = (ggGamma L hBsN) ⟨b, hb⟩ := rfl
  have hva : Multiplicative.toAdd (Φ a) ∈ NoOffRest.hypE6 :=
    (hrangeE6 (Multiplicative.toAdd (Φ a))).mp (by
      rw [ofAdd_toAdd]
      exact ⟨a, rfl⟩)
  obtain ⟨t, htT, ht3, b', hb'conj, hb'Φ⟩ := hnine (Multiplicative.toAdd (Φ a)) hva
  have hb'a : b' = a := hΦinj (Multiplicative.toAdd.injective hb'Φ)
  have hconj : MulAut.conj t = (a : MulAut ↥L) := by rw [hb'conj, hb'a]
  have hact : ∀ l : ↥L, b * (l : G) * b⁻¹ = (t : G) * (l : G) * (t : G)⁻¹ := by
    intro l
    have h1 : ((MulAut.conj t) l : G) = (((a : MulAut ↥L) l) : G) :=
      congrArg (fun w : ↥L => (w : G)) (congrArg (fun φ : MulAut ↥L => φ l) hconj)
    rw [ha_val, MulAut.conj_apply, ggGamma_coe] at h1
    push_cast at h1
    exact h1.symm
  have hbt : b * (t : G) * b⁻¹ = (t : G) := by simpa using hact t
  have hcomm_tb : Commute (t : G) b := by
    have h : b * (t : G) = (t : G) * b := by
      calc b * (t : G) = (b * (t : G) * b⁻¹) * b := by group
        _ = (t : G) * b := by rw [hbt]
    exact h.symm
  let c : G := (t : G)⁻¹ * b
  have hc_def : c = (t : G)⁻¹ * b := rfl
  have hcC : c ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := hact (⟨l, hl⟩ : ↥L)
    have hcl : c * l * c⁻¹ = l := by
      rw [hc_def]
      calc (t : G)⁻¹ * b * l * ((t : G)⁻¹ * b)⁻¹
          = (t : G)⁻¹ * (b * l * b⁻¹) * (t : G) := by group
        _ = (t : G)⁻¹ * ((t : G) * l * (t : G)⁻¹) * (t : G) := by rw [h]
        _ = l := by group
    have hcl' : c * l = l * c := by
      calc c * l = (c * l * c⁻¹) * c := by group
        _ = l * c := by rw [hcl]
    exact hcl'.symm
  have htG3 : (t : G) ^ 3 = 1 := by
    have := congrArg (fun w : ↥L => (w : G)) ht3
    simpa using this
  have hb3 : b ^ 3 = 1 := hBs.2 b hb
  have hc3 : c ^ 3 = 1 := by
    have hcomm_inv : Commute ((t : G)⁻¹) b := hcomm_tb.inv_left
    rw [hc_def, Commute.mul_pow hcomm_inv, inv_pow, htG3, hb3, inv_one, one_mul]
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := mem_centralizer_of_le_centralizer hLx
  have hct : Commute (t : G) x := Subgroup.mem_centralizer_iff.mp hxC (t : G) t.2
  have hcb : Commute b x := by
    have h : b * x = x * b := by
      have := congrArg Subtype.val
        (hBs.1.is_comm.comm (⟨b, hb⟩ : ↥Bs) (⟨x, hxB⟩ : ↥Bs))
      simpa using this
    exact h
  have hccx : Commute c x := by
    rw [hc_def]
    exact (hct.inv_left).mul_left hcb
  have hc_zp : c ∈ Subgroup.zpowers x :=
    mem_zpowers_of_mem_centralizer_of_commute_of_pow_eq_one hp hxp hLx hcyc hx1 hc3 hcC hccx.symm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc_zp
  have hm : x ^ (k % (3 : ℤ)) = c := by
    have h1 := zpow_mod_orderOf x k
    rw [hxord] at h1
    exact h1.trans hk
  have hm' : x ^ (k % (3 : ℤ)).toNat = c := by
    rw [← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num : (3 : ℤ) ≠ 0))]
    exact hm
  refine ⟨(t : G), t.2, (k % (3 : ℤ)).toNat, ?_⟩
  rw [hm', hc_def]
  group

end CFSG.StandardType

end
