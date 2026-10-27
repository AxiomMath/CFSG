module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLPhi
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

namespace E6Dep

namespace ZL

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

private theorem zla_gamma_conj {L Bs : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {n : G} (hnL : n ∈ L) (hn : n ∈ Subgroup.normalizer (Bs : Set G)) (c : ↥Bs) :
    ggGamma L hBsN (ggConjAut Bs hn c) =
      MulAut.conj (⟨n, hnL⟩ : ↥L) * ggGamma L hBsN c *
        (MulAut.conj (⟨n, hnL⟩ : ↥L))⁻¹ := by
  have hnb : n * (c : G) * n⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hn c).mp c.2
  have h1 : ggConjAut Bs hn c = (⟨n * (c : G) * n⁻¹, hnb⟩ : ↥Bs) :=
    Subtype.ext (ggConjAut_apply Bs hn c)
  rw [h1]
  exact ggGamma_conj L hBsN ⟨n, hnL⟩ c hnb

theorem phiB_refl {L Bs : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)} {w : Fin 6 → ↥L}
    (hw : ∀ i, ((w i : ↥L) : G) ∈ Subgroup.normalizer (Bs : Set G))
    (hcl8 : ∀ (i : Fin 6) (a : ↥(ggGamma L hBsN).range),
      ∃ b : ↥(ggGamma L hBsN).range,
        MulAut.conj (w i) * (a : MulAut ↥L) * (MulAut.conj (w i))⁻¹ = b ∧
          Multiplicative.toAdd (Φ b) = adRefl .E6 3 i (Multiplicative.toAdd (Φ a)))
    (i : Fin 6) (v : Additive ↥Bs) :
    phiB hBsN Φ (Additive.ofMul (ggConjAut Bs (hw i) (Additive.toMul v))) =
      adRefl .E6 3 i (phiB hBsN Φ v) := by
  let b₀ : ↥Bs := Additive.toMul v
  let a : ↥(ggGamma L hBsN).range := (ggGamma L hBsN).rangeRestrict b₀
  obtain ⟨b, hb1, hb2⟩ := hcl8 i a
  have ha : (a : MulAut ↥L) = ggGamma L hBsN b₀ := MonoidHom.coe_rangeRestrict _ _
  have hb1' : (b : MulAut ↥L) =
      MulAut.conj (w i) * ggGamma L hBsN b₀ * (MulAut.conj (w i))⁻¹ := by
    rw [← ha]
    exact hb1.symm
  have hγ := zla_gamma_conj hBsN (w i).2 (hw i) b₀
  have hbeq : (ggGamma L hBsN).rangeRestrict (ggConjAut Bs (hw i) b₀) = b := by
    apply Subtype.ext
    rw [MonoidHom.coe_rangeRestrict]
    exact hγ.trans hb1'.symm
  change Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict
      (ggConjAut Bs (hw i) (Additive.toMul v)))) =
    adRefl .E6 3 i (Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict
      (Additive.toMul v))))
  rw [hbeq, hb2]

theorem phiB_weyl {L Bs : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)}
    (hcl10 : ∀ n : ↥L, MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L)) →
        ∃ u : WeylGroup .E6, ∀ a b : ↥(ggGamma L hBsN).range,
          (b : MulAut ↥L) = MulAut.conj n * (a : MulAut ↥L) * (MulAut.conj n)⁻¹ →
            Multiplicative.toAdd (Φ b) = adAct .E6 3 u (Multiplicative.toAdd (Φ a)))
    {n : G} (hnL : n ∈ L) (hnN : n ∈ Subgroup.normalizer (Bs : Set G)) :
    ∃ u : WeylGroup .E6, ∀ v : Additive ↥Bs,
      phiB hBsN Φ (Additive.ofMul (ggConjAut Bs hnN (Additive.toMul v))) =
        adAct .E6 3 u (phiB hBsN Φ v) := by
  have hnN' : MulAut.conj (⟨n, hnL⟩ : ↥L) ∈
      Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L)) :=
    conj_mem_normalizer_range_ggGamma (X := L) hBsN hnL hnN
  obtain ⟨u, hu⟩ := hcl10 ⟨n, hnL⟩ hnN'
  refine ⟨u, fun v => ?_⟩
  let b₀ : ↥Bs := Additive.toMul v
  let a : ↥(ggGamma L hBsN).range := (ggGamma L hBsN).rangeRestrict b₀
  have ha : (a : MulAut ↥L) = ggGamma L hBsN b₀ := MonoidHom.coe_rangeRestrict _ _
  have hrel : (↑((ggGamma L hBsN).rangeRestrict (ggConjAut Bs hnN b₀)) : MulAut ↥L) =
      MulAut.conj (⟨n, hnL⟩ : ↥L) * (a : MulAut ↥L) *
        (MulAut.conj (⟨n, hnL⟩ : ↥L))⁻¹ := by
    rw [MonoidHom.coe_rangeRestrict]
    refine (zla_gamma_conj hBsN hnL hnN b₀).trans ?_
    rw [ha]
  change Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict
      (ggConjAut Bs hnN (Additive.toMul v)))) =
    adAct .E6 3 u (Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict
      (Additive.toMul v))))
  exact hu a ((ggGamma L hBsN).rangeRestrict (ggConjAut Bs hnN b₀)) hrel

theorem phiB_cobdry {L Bs : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {w : Fin 6 → ↥L} (hw : ∀ i, ((w i : ↥L) : G) ∈ Subgroup.normalizer (Bs : Set G)) {x : G}
    (hxBs : x ∈ Bs) (hxL : x ∈ L)
    (hcob : (⟨x, hxL⟩ : ↥L) ∈ ggE6WeylCobdry (ggGamma L hBsN).range w) :
    Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) ∈ AddSubgroup.closure
      {u | ∃ (i : Fin 6) (v : Additive ↥Bs),
        u = Additive.ofMul (ggConjAut Bs (hw i) (Additive.toMul v)) - v} := by
  let S : AddSubgroup (Additive ↥Bs) := AddSubgroup.closure
    {u | ∃ (i : Fin 6) (v : Additive ↥Bs),
      u = Additive.ofMul (ggConjAut Bs (hw i) (Additive.toMul v)) - v}
  let H : Subgroup ↥L :=
    { carrier := {c | ∃ hc : (c : G) ∈ Bs,
        Additive.ofMul (⟨(c : G), hc⟩ : ↥Bs) ∈ S}
      one_mem' := by
        refine ⟨Bs.one_mem, ?_⟩
        have h1 : (⟨((1 : ↥L) : G), Bs.one_mem⟩ : ↥Bs) = 1 := Subtype.ext rfl
        rw [h1, ofMul_one]
        exact S.zero_mem
      mul_mem' := by
        rintro c d ⟨hc, hcS⟩ ⟨hd, hdS⟩
        have hcd : ((c * d : ↥L) : G) ∈ Bs := by
          rw [Subgroup.coe_mul]
          exact Bs.mul_mem hc hd
        refine ⟨hcd, ?_⟩
        have he : (⟨((c * d : ↥L) : G), hcd⟩ : ↥Bs) =
            (⟨(c : G), hc⟩ : ↥Bs) * ⟨(d : G), hd⟩ := Subtype.ext rfl
        rw [he, ofMul_mul]
        exact S.add_mem hcS hdS
      inv_mem' := by
        rintro c ⟨hc, hcS⟩
        have hci : ((c⁻¹ : ↥L) : G) ∈ Bs := by
          rw [Subgroup.coe_inv]
          exact Bs.inv_mem hc
        refine ⟨hci, ?_⟩
        have he : (⟨((c⁻¹ : ↥L) : G), hci⟩ : ↥Bs) = (⟨(c : G), hc⟩ : ↥Bs)⁻¹ :=
          Subtype.ext rfl
        rw [he, ofMul_inv]
        exact S.neg_mem hcS }
  have hle : ggE6WeylCobdry (ggGamma L hBsN).range w ≤ H := by
    unfold ggE6WeylCobdry
    rw [Subgroup.closure_le]
    rintro c ⟨i, a, ha, rfl⟩
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp ha
    have hgen : ((w i * (a (w i))⁻¹ : ↥L) : G) =
        ((ggConjAut Bs (hw i) b : ↥Bs) : G) * (b : G)⁻¹ := by
      rw [← hb, Subgroup.coe_mul, Subgroup.coe_inv, ggGamma_coe, ggConjAut_apply]
      group
    have hc : ((w i * (a (w i))⁻¹ : ↥L) : G) ∈ Bs := by
      rw [hgen]
      exact Bs.mul_mem (ggConjAut Bs (hw i) b).2 (Bs.inv_mem b.2)
    refine ⟨hc, ?_⟩
    have hbeq : (⟨((w i * (a (w i))⁻¹ : ↥L) : G), hc⟩ : ↥Bs) =
        ggConjAut Bs (hw i) b * b⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hgen
    have hsub : Additive.ofMul (⟨((w i * (a (w i))⁻¹ : ↥L) : G), hc⟩ : ↥Bs) =
        Additive.ofMul (ggConjAut Bs (hw i) b) - Additive.ofMul b := by
      rw [hbeq, ofMul_mul, ofMul_inv, sub_eq_add_neg]
    rw [hsub]
    exact AddSubgroup.subset_closure ⟨i, Additive.ofMul b, rfl⟩
  obtain ⟨hc, hcS⟩ := hle hcob
  have hxx : (⟨x, hxBs⟩ : ↥Bs) = ⟨x, hc⟩ := Subtype.ext rfl
  rwa [hxx]

end ZL

end E6Dep

end CFSG.StandardType

end
