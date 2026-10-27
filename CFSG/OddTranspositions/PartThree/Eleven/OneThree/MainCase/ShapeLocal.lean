module

public import CFSG.Timmesfeld.Bridge.Asc72Local
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import CFSG.OddTranspositions.PartThree.EightOne.Defs
import CFSG.OddTranspositions.PartThree.LocalBenderCenter
import CFSG.OddTranspositions.TheoremTwo.StepSeven
import CFSG.Timmesfeld.Basic
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Timmesfeld.Bridge.Asc72BenderInvolution
import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic
import CFSG.GH74.GLS.Bg.Iii2.L41Basic
import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc73Quotient
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.Fischer.NoF25.Local
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
import CFSG.GH74.Statements
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
import CFSG.OddTranspositions.AlmostSimple
import CFSG.OddTranspositions.Disconnected
import CFSG.OddTranspositions.WreathQuotient
import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
import CFSG.Timmesfeld.Transvection.Statement


public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section Helpers

variable {X : Type} [Group X] {F : Set X} {U : Type} [Group U]
  (p : X →* Multiplicative (ZMod 2) × U)

private theorem eq_one_of_mem_of_odd {K : Subgroup X} (hK : Odd (Nat.card K)) {k : X}
    (hk : k ∈ K) (h2 : k * k = 1) : k = 1 := by
  have hdvd : orderOf k ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hk
  have h2' : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2' with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hdvd
    exact absurd hdvd hK.not_two_dvd_nat

private theorem commute_iff_eq_or_map (hF : IsOddTransp F) (hodd : Odd (Nat.card p.ker))
    {d e : X} (hd : d ∈ F) (he : e ∈ F) :
    Commute d e ↔ d = e ∨ (p d ≠ p e ∧ Commute (p d) (p e)) := by
  have hd2 := hF.mul_self_eq_one hd
  have he2 := hF.mul_self_eq_one he
  constructor
  · intro hc
    by_cases hde : d = e
    · exact Or.inl hde
    · refine Or.inr ⟨fun hpe => hde ?_, hc.map p⟩
      have hmem : d * e ∈ p.ker := by
        rw [MonoidHom.mem_ker, map_mul, hpe, ← map_mul, he2, map_one]
      have hsq : d * e * (d * e) = 1 := by
        calc d * e * (d * e) = d * (e * d) * e := by group
          _ = d * (d * e) * e := by rw [hc.eq]
          _ = d * d * (e * e) := by group
          _ = 1 := by rw [hd2, he2, one_mul]
      exact hF.eq_of_mul_eq_one hd (eq_one_of_mem_of_odd hodd hmem hsq)
  · rintro (rfl | ⟨hne, hc⟩)
    · exact Commute.refl d
    · rcases hF.commute_or_odd hd he with h | h
      · exact h
      · exfalso
        have hpe : p e * p e = 1 := by rw [← map_mul, he2, map_one]
        have hpd : p d * p d = 1 := by rw [← map_mul, hd2, map_one]
        have h2 : p (d * e) * p (d * e) = 1 := by
          rw [map_mul]
          calc p d * p e * (p d * p e) = p d * (p e * p d) * p e := by group
            _ = p d * (p d * p e) * p e := by rw [hc.eq]
            _ = p d * p d * (p e * p e) := by group
            _ = 1 := by rw [hpd, hpe, one_mul]
        have h1 : p (d * e) ≠ 1 := by
          intro h1
          rw [map_mul] at h1
          apply hne
          calc p d = p d * (p e * p e) := by rw [hpe, mul_one]
            _ = (p d * p e) * p e := by group
            _ = p e := by rw [h1, one_mul]
        have hord : orderOf (p (d * e)) = 2 :=
          orderOf_eq_prime (by rw [pow_two]; exact h2) h1
        have hdvd : orderOf (p (d * e)) ∣ orderOf (d * e) := orderOf_map_dvd p (d * e)
        rw [hord] at hdvd
        exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr hdvd)

private theorem fst_eq_of_mem (hS : Setup X F) {d e : X} (hd : d ∈ F) (he : e ∈ F) :
    (p d).1 = (p e).1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hd he)
  rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv]
  exact (mul_inv_cancel_comm _ _).symm

private theorem eq_iff_snd_eq (hS : Setup X F) {d e : X} (hd : d ∈ F) (he : e ∈ F) :
    p d = p e ↔ (p d).2 = (p e).2 :=
  ⟨fun h => congrArg Prod.snd h, fun h => Prod.ext (fst_eq_of_mem p hS hd he) h⟩

private theorem commute_iff_commute_snd {d e : X} :
    Commute (p d) (p e) ↔ Commute (p d).2 (p e).2 := by
  constructor
  · intro h
    have := congrArg Prod.snd h.eq
    simp only [Prod.snd_mul] at this
    exact this
  · intro h
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul]
      exact mul_comm _ _
    · simp only [Prod.snd_mul]
      exact h.eq

private theorem snd_mul_self (hS : Setup X F) {f : X} (hf : f ∈ F) : (p f).2 * (p f).2 = 1 := by
  rw [← Prod.snd_mul, ← map_mul, hS.oddT.mul_self_eq_one hf, map_one, Prod.snd_one]

private theorem snd_ne_one [Finite U] (hS : Setup X F) (hp : Function.Surjective p)
    (hU : CFSG.BenderSuzuki.IsBenderGroup U) {f : X} (hf : f ∈ F) : (p f).2 ≠ 1 := by
  intro h1
  have hle : Subgroup.closure F ≤ ((MonoidHom.snd _ _).comp p).ker := by
    rw [Subgroup.closure_le]
    intro e he
    obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hf he)
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.coe_snd, map_mul,
      map_mul, Prod.snd_mul, Prod.snd_mul, h1, mul_one, ← Prod.snd_mul, ← map_mul, mul_inv_cancel,
      map_one, Prod.snd_one]
  rw [hS.gen] at hle
  have htriv : ∀ u : U, u = 1 := by
    intro u
    obtain ⟨x, hx⟩ := hp (1, u)
    have := hle (Subgroup.mem_top x)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hx] at this
    simpa using this
  obtain ⟨a, b, hab⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hU
  exact hab (by rw [htriv a]; exact Commute.one_left b)

private theorem fst_ne_one (hS : Setup X F) (hp : Function.Surjective p) {f : X} (hf : f ∈ F) :
    (p f).1 ≠ 1 := by
  intro h1
  have hle : Subgroup.closure F ≤ ((MonoidHom.fst _ _).comp p).ker := by
    rw [Subgroup.closure_le]
    intro e he
    have := fst_eq_of_mem p hS he hf
    simp [this, h1]
  rw [hS.gen] at hle
  obtain ⟨x, hx⟩ := hp (Multiplicative.ofAdd 1, 1)
  have := hle (Subgroup.mem_top x)
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hx, MonoidHom.coe_fst] at this
  change Multiplicative.ofAdd (1 : ZMod 2) = 1 at this
  exact absurd this (by decide)

private theorem orderOf_snd [Finite U] (hS : Setup X F) (hp : Function.Surjective p)
    (hU : CFSG.BenderSuzuki.IsBenderGroup U) {f : X} (hf : f ∈ F) : orderOf (p f).2 = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact snd_mul_self p hS hf) (snd_ne_one p hS hp hU hf)

private theorem exists_conj_commute (hS : Setup X F) (hodd : Odd (Nat.card p.ker)) {z : X}
    (hz : z * z = 1) (hpz : (p z).2 = 1) {d : X} (hd : d ∈ F) :
    ∃ g ∈ p.ker, Commute (g * d * g⁻¹) z := by
  set c := z * d * z⁻¹ * d⁻¹ with hcdef
  have hcK : c ∈ p.ker := by
    rw [MonoidHom.mem_ker]
    refine Prod.ext ?_ ?_
    · have hab : ∀ a b : Multiplicative (ZMod 2), a * b * a⁻¹ * b⁻¹ = 1 := fun a b =>
        mul_inv_eq_one.mpr (mul_inv_cancel_comm a b)
      rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, Prod.fst_mul, Prod.fst_mul,
        Prod.fst_mul, Prod.fst_inv, Prod.fst_inv, Prod.fst_one]
      exact hab _ _
    · rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, Prod.snd_mul, Prod.snd_mul,
        Prod.snd_mul, Prod.snd_inv, Prod.snd_inv, hpz, Prod.snd_one, one_mul, inv_one, mul_one,
        mul_inv_cancel]
  have hcodd : Odd (orderOf c) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hcK)
  obtain ⟨k, hk⟩ := CFSG.GH74.GLS.Bg.Iii2.L41.exists_pow_conj_commute hz
    (hS.oddT.mul_self_eq_one hd) hcodd
  refine ⟨(c ^ k)⁻¹, inv_mem (pow_mem hcK k), ?_⟩
  show (c ^ k)⁻¹ * d * (c ^ k)⁻¹⁻¹ * z = z * ((c ^ k)⁻¹ * d * (c ^ k)⁻¹⁻¹)
  rw [inv_inv]
  calc (c ^ k)⁻¹ * d * c ^ k * z
      = (c ^ k)⁻¹ * (d * (c ^ k * z * (c ^ k)⁻¹)) * c ^ k := by group
    _ = (c ^ k)⁻¹ * ((c ^ k * z * (c ^ k)⁻¹) * d) * c ^ k := by rw [hk]
    _ = z * ((c ^ k)⁻¹ * d * c ^ k) := by group

private theorem exists_mem_F_not_commute_snd [Finite U] (hS : Setup X F)
    (hU : CFSG.BenderSuzuki.IsBenderGroup U) (hp : Function.Surjective p) {v : X}
    (htv1 : (p v).2 ≠ 1) :
    ∃ a ∈ F, ¬ Commute (p v).2 (p a).2 := by
  have hlift : ∀ u : U, ∃ g : X, (p g).2 = u := fun u => by
    obtain ⟨g, hg⟩ := hp (1, u)
    exact ⟨g, by rw [hg]⟩
  by_contra hno
  push Not at hno
  have hle : Subgroup.closure F ≤
      (Subgroup.centralizer ({(p v).2} : Set U)).comap ((MonoidHom.snd _ _).comp p) := by
    rw [Subgroup.closure_le]
    intro e he
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (hno e he).symm
  rw [hS.gen] at hle
  have hcenter : (p v).2 ∈ Subgroup.center U := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨x, hx⟩ := hlift w
    have := hle (Subgroup.mem_top x)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, MonoidHom.comp_apply,
      MonoidHom.coe_snd, hx] at this
    exact this
  have := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hU
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center U) with hb | ht
  · rw [hb, Subgroup.mem_bot] at hcenter
    exact htv1 hcenter
  · obtain ⟨x, y, hxy⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hU
    apply hxy
    have hy : y ∈ Subgroup.center U := ht ▸ Subgroup.mem_top y
    exact Subgroup.mem_center_iff.mp hy x

end Helpers

variable {X : Type} [Group X] [Finite X] {F : Set X} {U : Type} [Group U] [Finite U]
  {p : X →* Multiplicative (ZMod 2) × U}

omit [Finite X] [Finite U] in
theorem commute_iff_eq_or_snd (hS : Setup X F) (hodd : Odd (Nat.card p.ker)) {d e : X}
    (hd : d ∈ F) (he : e ∈ F) :
    Commute d e ↔ d = e ∨ ((p d).2 ≠ (p e).2 ∧ Commute (p d).2 (p e).2) := by
  rw [commute_iff_eq_or_map p hS.oddT hodd hd he, ne_eq, eq_iff_snd_eq p hS hd he,
    commute_iff_commute_snd p, ← ne_eq]

omit [Finite X] [Finite U] in
private theorem snd_facts_of_isTriangle (hS : Setup X F) (hodd : Odd (Nat.card p.ker))
    {v a c : X} (htri : IsTriangle F v a c) :
    (p v).2 ≠ (p c).2 ∧ Commute (p v).2 (p c).2 ∧ (p v).2 ≠ (p a).2 ∧
      ¬ Commute (p v).2 (p a).2 := by
  obtain ⟨hv, hc, ha, hvc, hcvc, hva, hca⟩ := htri
  have P0 := fun {d e : X} (hd : d ∈ F) (he : e ∈ F) =>
    commute_iff_eq_or_snd hS hodd hd he
  have hvc' : (p v).2 ≠ (p c).2 ∧ Commute (p v).2 (p c).2 :=
    ((P0 hv hc).mp hcvc).resolve_left hvc
  have hva_ne : (p v).2 ≠ (p a).2 := by
    intro heq
    apply hca
    refine (P0 hc ha).mpr (Or.inr ⟨fun h' => hvc'.1 (heq.trans h'.symm), ?_⟩)
    rw [← heq]
    exact hvc'.2.symm
  have hva' : ¬ Commute (p v).2 (p a).2 := fun h' =>
    hva ((P0 hv ha).mpr (Or.inr ⟨hva_ne, h'⟩))
  exact ⟨hvc'.1, hvc'.2, hva_ne, hva'⟩

omit [Finite X] in
private theorem odd_orderOf_mul_of_isBenderGroup
    (hU : CFSG.BenderSuzuki.IsBenderGroup U) {tv tc ta : U}
    (htvo : orderOf tv = 2) (htco : orderOf tc = 2) (htao : orderOf ta = 2)
    (hc : Commute tv tc) (hne : tv ≠ tc) (hna : ¬ Commute tv ta) :
    Odd (orderOf (tv * tc * ta)) ∧ orderOf (tv * tc * ta) ≠ 1 := by
  have htv2 : tv * tv = 1 := by rw [← pow_two, ← htvo]; exact pow_orderOf_eq_one tv
  have htc2 : tc * tc = 1 := by rw [← pow_two, ← htco]; exact pow_orderOf_eq_one tc
  have hta2 : ta * ta = 1 := by rw [← pow_two, ← htao]; exact pow_orderOf_eq_one ta
  have hs2 : tv * tc * (tv * tc) = 1 := by
    calc tv * tc * (tv * tc) = tv * (tc * tv) * tc := by group
      _ = tv * (tv * tc) * tc := by rw [hc.eq]
      _ = tv * tv * (tc * tc) := by group
      _ = 1 := by rw [htv2, htc2, one_mul]
  have hs1 : tv * tc ≠ 1 := by
    intro h1
    apply hne
    calc tv = tv * (tc * tc) := by rw [htc2, mul_one]
      _ = tv * tc * tc := by group
      _ = tc := by rw [h1, one_mul]
  have hso : orderOf (tv * tc) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  have htvs : Commute tv (tv * tc) := (Commute.refl tv).mul_right hc
  have hsta : ¬ Commute (tv * tc) ta := fun h' =>
    hna (CFSG.Timmesfeld.Bridge.OddLocal.IsBenderGroup.commute_trans hU htvo hso htao htvs h')
  have hsodd : Odd (orderOf (tv * tc * ta)) := by
    by_contra h
    exact hsta (CFSG.OddTranspositions.commute_of_even_orderOf_mul_of_isBenderGroup hU hs2 hta2
      (Nat.not_odd_iff_even.mp h))
  have hm1 : orderOf (tv * tc * ta) ≠ 1 := by
    intro h1
    apply hsta
    rw [orderOf_eq_one_iff] at h1
    have : ta = tv * tc := by
      calc ta = (tv * tc) * (tv * tc) * ta := by rw [hs2, one_mul]
        _ = (tv * tc) * ((tv * tc) * ta) := by group
        _ = tv * tc := by rw [h1, mul_one]
    rw [this]
  exact ⟨hsodd, hm1⟩

omit [Finite X] [Finite U] in
private theorem image_mul_dvd_of_isTriangle (hS : Setup X F) (hp : Function.Surjective p)
    {v a c : X} (htri : IsTriangle F v a c) :
    (p (v * c * a)).1 = (p v).1 ∧
      (p (v * c * a)).2 = (p v).2 * (p c).2 * (p a).2 ∧
      2 ∣ orderOf (v * c * a) ∧
      orderOf ((p v).2 * (p c).2 * (p a).2) ∣ orderOf (v * c * a) := by
  obtain ⟨hv, hc, ha, -, -, -, -⟩ := htri
  have hfst : (p (v * c * a)).1 = (p v).1 := by
    rw [map_mul, map_mul, Prod.fst_mul, Prod.fst_mul, fst_eq_of_mem p hS hc hv,
      fst_eq_of_mem p hS ha hv, mul_assoc, ← Prod.fst_mul, ← map_mul,
      hS.oddT.mul_self_eq_one hv, map_one, Prod.fst_one, mul_one]
  have hsnd : (p (v * c * a)).2 = (p v).2 * (p c).2 * (p a).2 := by
    rw [map_mul, map_mul, Prod.snd_mul, Prod.snd_mul]
  have hpow : ∀ N : ℕ, (v * c * a) ^ N = 1 →
      (p v).1 ^ N = 1 ∧ ((p v).2 * (p c).2 * (p a).2) ^ N = 1 := by
    intro N hN
    have := congrArg p hN
    rw [map_pow, map_one] at this
    refine ⟨?_, ?_⟩
    · have h1 := congrArg Prod.fst this
      rwa [Prod.pow_fst, hfst, Prod.fst_one] at h1
    · have h2 := congrArg Prod.snd this
      rwa [Prod.pow_snd, hsnd, Prod.snd_one] at h2
  have hv1 : (p v).1 * (p v).1 = 1 := by
    rw [← Prod.fst_mul, ← map_mul, hS.oddT.mul_self_eq_one hv, map_one, Prod.fst_one]
  have hvo : orderOf (p v).1 = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hv1) (fst_ne_one p hS hp hv)
  refine ⟨hfst, hsnd, ?_, ?_⟩
  · rw [← hvo]
    exact orderOf_dvd_of_pow_eq_one (hpow _ (pow_orderOf_eq_one _)).1
  · exact orderOf_dvd_of_pow_eq_one (hpow _ (pow_orderOf_eq_one _)).2

theorem isThirdKind_of_isTriangle (hS : Setup X F) (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (hp : Function.Surjective p) (hodd : Odd (Nat.card p.ker)) {v a c : X}
    (htri : IsTriangle F v a c) :
    IsThirdKind v a c ∧ ∀ n : ℕ, orderOf (v * c * a) = 2 * n → (p ((v * c * a) ^ n)).2 = 1 := by
  have hv : v ∈ F := htri.1
  have hc : c ∈ F := htri.2.1
  have ha : a ∈ F := htri.2.2.1
  obtain ⟨hvc_ne, hvc_c, hva_ne, hva'⟩ := snd_facts_of_isTriangle hS hodd htri
  obtain ⟨hsodd, hm1⟩ := odd_orderOf_mul_of_isBenderGroup hU
    (orderOf_snd p hS hp hU hv) (orderOf_snd p hS hp hU hc)
    (orderOf_snd p hS hp hU ha) hvc_c hvc_ne hva'
  obtain ⟨hfst, hsnd, h2dvd, hmdvd⟩ := image_mul_dvd_of_isTriangle hS hp htri
  have hcop : (orderOf ((p v).2 * (p c).2 * (p a).2)).Coprime 2 :=
    Nat.coprime_two_right.mpr hsodd
  refine ⟨?_, fun n hn => ?_⟩
  · rcases IsTriangle.orderOf_cases hS.oddT hS.normal htri with ⟨hodd', -⟩ | h4 | h3
    · exact absurd (even_iff_two_dvd.mpr h2dvd) (Nat.not_even_iff_odd.mpr hodd')
    · exfalso
      rw [h4, show (4 : ℕ) = 2 * 2 from rfl] at hmdvd
      exact hm1 (Nat.Coprime.eq_one_of_dvd hcop (hcop.dvd_of_dvd_mul_right hmdvd))
    · exact h3
  · rw [map_pow, Prod.pow_snd, hsnd]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hn, mul_comm] at hmdvd
    exact hcop.dvd_of_dvd_mul_right hmdvd

omit [Finite X] in
theorem exists_isTriangle (hS : Setup X F) (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (hp : Function.Surjective p) (hodd : Odd (Nat.card p.ker)) {v : X} (hv : v ∈ F) :
    ∃ a c : X, IsTriangle F v a c := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tv := (p v).2 with htv
  have htvo : orderOf tv = 2 := orderOf_snd p hS hp hU hv
  have htv1 : tv ≠ 1 := snd_ne_one p hS hp hU hv
  have hlift : ∀ u : U, ∃ g : X, (p g).2 = u := fun u => by
    obtain ⟨g, hg⟩ := hp (1, u)
    exact ⟨g, by rw [hg]⟩
  obtain ⟨tc, htco, htcv, hvc⟩ :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_involution_commute_ne hU htvo
  obtain ⟨u, hu⟩ := isConj_iff.mp
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hU htvo htco)
  obtain ⟨g, hg⟩ := hlift u
  have hcF : g * v * g⁻¹ ∈ F := hS.conj_mem g hv
  have hcsnd : (p (g * v * g⁻¹)).2 = tc := by
    rw [map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, hg, ← htv, hu]
  obtain ⟨a, haF, hva⟩ := exists_mem_F_not_commute_snd p hS hU hp htv1
  refine ⟨a, g * v * g⁻¹, hv, hcF, haF, ?_, ?_, ?_, ?_⟩
  · intro h'
    apply htcv
    rw [← hcsnd, ← h']
  · exact (commute_iff_eq_or_snd hS hodd hv hcF).mpr
      (Or.inr ⟨by rw [hcsnd]; exact htcv.symm, by rw [hcsnd]; exact hvc⟩)
  · intro h'
    rcases (commute_iff_eq_or_snd hS hodd hv haF).mp h' with h'' | ⟨-, h''⟩
    · exact hva (h'' ▸ Commute.refl _)
    · exact hva h''
  · intro h'
    rcases (commute_iff_eq_or_snd hS hodd hcF haF).mp h' with h'' | ⟨-, h''⟩
    · apply hva
      rw [← h'', hcsnd]
      exact hvc
    · rw [hcsnd] at h''
      exact hva (CFSG.Timmesfeld.Bridge.OddLocal.IsBenderGroup.commute_trans hU htvo htco
        (orderOf_snd p hS hp hU haF) hvc h'')

omit [Finite X] [Finite U] in
theorem ker_sup_localGroup_eq_top (hS : Setup X F) (hodd : Odd (Nat.card p.ker)) {z : X}
    (hz : z * z = 1) (hpz : (p z).2 = 1) :
    p.ker ⊔ localGroup F z = ⊤ := by
  rw [eq_top_iff, ← hS.gen, Subgroup.closure_le]
  intro d hd
  obtain ⟨g, hg, hgc⟩ := exists_conj_commute p hS hodd hz hpz hd
  have hmem : g * d * g⁻¹ ∈ localGroup F z :=
    mem_localGroup_of_mem ⟨hS.conj_mem g hd, hgc⟩
  have hd' : d = g⁻¹ * (g * d * g⁻¹) * g := by group
  rw [SetLike.mem_coe, hd']
  exact mul_mem (mul_mem (Subgroup.mem_sup_left (inv_mem hg)) (Subgroup.mem_sup_right hmem))
    (Subgroup.mem_sup_left hg)

omit [Finite X] [Finite U] in
theorem exists_conj_eq_of_mem_centSet (hS : Setup X F) (hodd : Odd (Nat.card p.ker)) {z : X}
    (hz : z * z = 1) (hpz : (p z).2 = 1) {x y : X}
    (hx : x ∈ centSet F z) (hy : y ∈ centSet F z) : ∃ h ∈ localGroup F z, h * x * h⁻¹ = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj hx.1 hy.1)
  have hgtop : g ∈ ((p.ker ⊔ localGroup F z : Subgroup X) : Set X) := by
    rw [ker_sup_localGroup_eq_top hS hodd hz hpz]
    exact Subgroup.mem_top g
  rw [Subgroup.normal_mul] at hgtop
  obtain ⟨k, hk, l, hl, rfl⟩ := Set.mem_mul.mp hgtop
  obtain ⟨x', hx'⟩ : ∃ x', x' = l * x * l⁻¹ := ⟨_, rfl⟩
  have hlz : Commute l z := commute_of_mem_localGroup hl
  have hx'c : x' ∈ centSet F z := by
    rw [hx']
    exact ⟨hS.conj_mem l hx.1, (hlz.mul_left hx.2).mul_left hlz.inv_left⟩
  have hy' : y = k * x' * k⁻¹ := by rw [← hg, hx']; group
  have hpk : p k = 1 := hk
  have hpy : p y = p x' := by
    have hpk' : p k⁻¹ = 1 := (inv_mem hk : k⁻¹ ∈ p.ker)
    rw [hy', map_mul, map_mul, hpk, hpk']
    exact (mul_one (1 * p x')).trans (one_mul (p x'))
  have hmem : x' * y ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, hpy, ← map_mul, hS.oddT.mul_self_eq_one hx'c.1, map_one]
  have hxyodd : Odd (orderOf (x' * y)) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hmem)
  obtain ⟨g', hg', hg'x⟩ := CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul
    (hS.oddT.mul_self_eq_one hx'c.1) (hS.oddT.mul_self_eq_one hy.1) hxyodd
  have hcl : Subgroup.closure ({x', y} : Set X) ≤ localGroup F z := by
    rw [Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | rfl
    · exact mem_localGroup_of_mem hx'c
    · exact mem_localGroup_of_mem hy
  refine ⟨g' * l, mul_mem (hcl hg') hl, ?_⟩
  rw [← hg'x, hx']
  group

theorem injOn_centSet_of_isTriangle (hS : Setup X F) (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (hp : Function.Surjective p) (hodd : Odd (Nat.card p.ker)) {v a c : X}
    (htri : IsTriangle F v a c) {n : ℕ} (hn : orderOf (v * c * a) = 2 * n) :
    Set.InjOn p (centSet F ((v * c * a) ^ n)) := by
  obtain ⟨h3, hz⟩ := isThirdKind_of_isTriangle hS hU hp hodd htri
  have hn' : Odd n := by
    obtain ⟨m, hm, -, hmord⟩ := h3
    rw [show n = m by omega]
    exact hm
  obtain ⟨hzz, -, hzv, hzc, -, hvcz⟩ := htri.third_kind hS.oddT hS.normal hn' hn
  have hpz := hz n hn
  have hcent := CFSG.OddTranspositions.PartThree.oddCore_le_center_localGroup hS
    (z := (v * c * a) ^ n) (u := v) (v := c) ⟨htri.1, hzv.symm⟩ ⟨htri.2.1, hzc.symm⟩
    htri.2.2.2.1 htri.2.2.2.2.1 hvcz
    (fun x hx y hy => exists_conj_eq_of_mem_centSet hS hodd hzz hpz hx hy)
  set L := localGroup F ((v * c * a) ^ n) with hL
  have hKL : Odd (Nat.card (p.ker.subgroupOf L)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_comap_dvd_of_injective p.ker L.subtype
      Subtype.val_injective)
  have hle := CFSG.ABGLocalTools.le_oddCore_of_normal (H := L) inferInstance hKL
  intro x hx y hy hxy
  have hx2 := hS.oddT.mul_self_eq_one hx.1
  have hmem : x * y ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, hxy, ← map_mul, hS.oddT.mul_self_eq_one hy.1, map_one]
  have hxL : x ∈ L := mem_localGroup_of_mem hx
  have hxyL : x * y ∈ L := mul_mem hxL (mem_localGroup_of_mem hy)
  have hcen : (⟨x * y, hxyL⟩ : L) ∈ Subgroup.center L :=
    hcent (hle (by rw [Subgroup.mem_subgroupOf]; exact hmem))
  have hc : Commute (x * y) x :=
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨x, hxL⟩)).symm
  have hxy' : Commute x y := by
    have hc' : x * y * x = x * (x * y) := hc
    show x * y = y * x
    calc x * y = x * y * x * x := by rw [mul_assoc (x * y) x x, hx2, mul_one]
      _ = x * (x * y) * x := by rw [hc']
      _ = y * x := by rw [← mul_assoc, hx2, one_mul]
  rcases (commute_iff_eq_or_map p hS.oddT hodd hx.1 hy.1).mp hxy' with h' | ⟨hne, -⟩
  · exact h'
  · exact absurd hxy hne

omit [Finite X] in
theorem commute_of_commute_of_injOn (hS : Setup X F) (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (hp : Function.Surjective p) (hodd : Odd (Nat.card p.ker)) {z : X}
    (hinj : Set.InjOn p (centSet F z)) {y₀ y₁ y₂ : X} (h₀ : y₀ ∈ centSet F z)
    (h₁ : y₁ ∈ centSet F z) (h₂ : y₂ ∈ centSet F z) (h01 : Commute y₀ y₁)
    (h02 : Commute y₀ y₂) : Commute y₁ y₂ := by
  refine (commute_iff_eq_or_snd hS hodd h₁.1 h₂.1).mpr ?_
  by_cases heq : (p y₁).2 = (p y₂).2
  · exact Or.inl (hinj h₁ h₂ ((eq_iff_snd_eq p hS h₁.1 h₂.1).mpr heq))
  · have hc01 : Commute (p y₀).2 (p y₁).2 := (commute_iff_commute_snd p).mp (h01.map p)
    have hc02 : Commute (p y₀).2 (p y₂).2 := (commute_iff_commute_snd p).mp (h02.map p)
    exact Or.inr ⟨heq, CFSG.Timmesfeld.Bridge.OddLocal.IsBenderGroup.commute_trans hU
      (orderOf_snd p hS hp hU h₁.1) (orderOf_snd p hS hp hU h₀.1) (orderOf_snd p hS hp hU h₂.1)
      hc01.symm hc02⟩

omit [Finite X] in
theorem commute_of_four_point (hS : Setup X F) (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (hp : Function.Surjective p) (hodd : Odd (Nat.card p.ker)) {a a' b b' : X}
    (ha : a ∈ F) (ha' : a' ∈ F) (hb : b ∈ F) (hb' : b' ∈ F) (hab : Commute a b)
    (ha'b : Commute a' b) (hab' : Commute a b') (haa' : ¬ Commute a a') (hbb' : ¬ Commute b b') :
    Commute a' b' := by
  have P0 := fun {d e : X} (hd : d ∈ F) (he : e ∈ F) => commute_iff_eq_or_snd hS hodd hd he
  have ho := fun {d : X} (hd : d ∈ F) => orderOf_snd p hS hp hU hd
  have htrans := fun {i j k : X} (hi : i ∈ F) (hj : j ∈ F) (hk : k ∈ F)
      (hij : Commute (p i).2 (p j).2) (hjk : Commute (p j).2 (p k).2) =>
    CFSG.Timmesfeld.Bridge.OddLocal.IsBenderGroup.commute_trans hU (ho hi) (ho hj) (ho hk) hij hjk
  have hab0 : (p a).2 ≠ (p b).2 ∧ Commute (p a).2 (p b).2 :=
    ((P0 ha hb).mp hab).resolve_left fun h => hbb' (h ▸ hab')
  have ha'b0 : (p a').2 ≠ (p b).2 ∧ Commute (p a').2 (p b).2 :=
    ((P0 ha' hb).mp ha'b).resolve_left fun h => haa' (h ▸ hab)
  have hab'0 : (p a).2 ≠ (p b').2 ∧ Commute (p a).2 (p b').2 :=
    ((P0 ha hb').mp hab').resolve_left fun h => hbb' (h ▸ hab.symm)
  have haa'c : Commute (p a).2 (p a').2 := htrans ha hb ha' hab0.2 ha'b0.2.symm
  have hbb'c : Commute (p b).2 (p b').2 := htrans hb ha hb' hab0.2.symm hab'0.2
  have haa'e : (p a).2 = (p a').2 := by
    by_contra hne
    exact haa' ((P0 ha ha').mpr (Or.inr ⟨hne, haa'c⟩))
  have hbb'e : (p b).2 = (p b').2 := by
    by_contra hne
    exact hbb' ((P0 hb hb').mpr (Or.inr ⟨hne, hbb'c⟩))
  refine (P0 ha' hb').mpr (Or.inr ⟨?_, ?_⟩)
  · rw [← haa'e]
    exact hab'0.1
  · rw [← haa'e]
    exact hab'0.2

noncomputable abbrev shapeProj
    (φ : X ⧸ EightOne.twoOddCore X ≃* Multiplicative (ZMod 2) × U) :
    X →* Multiplicative (ZMod 2) × U :=
  φ.toMonoidHom.comp (QuotientGroup.mk' (EightOne.twoOddCore X))

theorem odd_card_twoOddCore (hQ1 : CFSG.pCore 2 X = ⊥) :
    Odd (Nat.card (EightOne.twoOddCore X)) := by
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hQ1]
  exact Odd.of_dvd_nat CFSG.ABGLocalTools.odd_card_oddCore
    (Subgroup.card_comap_dvd_of_injective _ _ hinj)

omit [Finite U] in
theorem ker_shapeProj (φ : X ⧸ EightOne.twoOddCore X ≃* Multiplicative (ZMod 2) × U) :
    (shapeProj φ).ker = EightOne.twoOddCore X := by
  change (φ.toMonoidHom.comp (QuotientGroup.mk' (EightOne.twoOddCore X))).ker =
    EightOne.twoOddCore X
  rw [MonoidHom.ker_comp_of_injective _ _ φ.injective, QuotientGroup.ker_mk']

omit [Finite U] in
theorem shapeProj_surjective (φ : X ⧸ EightOne.twoOddCore X ≃* Multiplicative (ZMod 2) × U) :
    Function.Surjective (shapeProj φ) := by
  intro y
  obtain ⟨q, rfl⟩ := φ.surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (EightOne.twoOddCore X) q
  exact ⟨x, rfl⟩

end CFSG.OddTranspositions.PartThree.ElevenThree
