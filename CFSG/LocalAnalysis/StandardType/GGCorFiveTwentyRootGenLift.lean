module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenKGDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
public import CFSG.LocalAnalysis.StandardType.GGNbrReflectionLift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestTypeA
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_isReflection_overGamma_of_weylElt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs K : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {n : K}
    (hnW : GGTorusWeylElt p (ggGamma K hN).range n)
    (hn : MulAut.conj n ∈ Subgroup.normalizer ((ggGamma K hN).range : Set (MulAut ↥K)))
    (hrefl : GGIsReflection p (ggConjAut (ggGamma K hN).range hn)) :
    ∃ (m : ℕ) (hg : (n : G) ^ m ∈ Subgroup.normalizer (Bs : Set G)),
      GGIsReflection p (ggConjAut Bs hg) ∧
        GGOverGamma hN (ggConjAut Bs hg) (ggConjAut (ggGamma K hN).range hn) := by
  classical
  have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_ggTorusWeylElt hN hSC hnW
  have h₀ : GGOverGamma hN (ggConjAut Bs hnN)
      (ggConjAut (ggGamma K hN).range hn) := by
    have h := ggOverGamma_conjAut (hN := hN) n.2 hnN
    have heq : ggConjAut (ggGamma K hN).range
          (conj_mem_normalizer_range_ggGamma hN n.2 hnN)
        = ggConjAut (ggGamma K hN).range hn := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rfl
    rwa [heq] at h
  obtain ⟨k, m, hm_odd, horder⟩ :=
    Nat.exists_eq_two_pow_mul_odd (orderOf_pos (n : G)).ne'
  let g : G := (n : G) ^ m
  have hgK : g ∈ K := Subgroup.pow_mem K n.2 m
  have hg : g ∈ Subgroup.normalizer (Bs : Set G) :=
    Subgroup.pow_mem (Subgroup.normalizer (Bs : Set G)) hnN m
  have hg_eq : ggConjAut Bs hg = ggConjAut Bs hnN ^ m := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply Bs hg b, ggConjAut_pow_apply Bs hnN m b]
  have ham : (ggConjAut (ggGamma K hN).range hn) ^ m
      = ggConjAut (ggGamma K hN).range hn := by
    obtain ⟨j, hj⟩ := hm_odd
    rw [hj, pow_succ, pow_mul, hrefl.1, one_pow, one_mul]
  have hGOGm : GGOverGamma hN (ggConjAut Bs hnN ^ m)
      (ggConjAut (ggGamma K hN).range hn) := by
    have h := h₀.pow m
    rwa [ham] at h
  have hfix : ∀ v ∈ (ggGamma K hN).rangeRestrict.ker,
      (ggConjAut Bs hnN ^ m) v = v := by
    intro v hv
    have hv1 : ggGamma K hN v = 1 := by
      have h := (MonoidHom.mem_ker (f := (ggGamma K hN).rangeRestrict)).mp hv
      simpa using Subtype.ext_iff.mp h
    have hvc : (v : G) ∈ Subgroup.centralizer (K : Set G) :=
      (ggGamma_eq_one_iff K hN v).mp hv1
    have hcomm : (n : G) ^ m * (v : G) = (v : G) * (n : G) ^ m :=
      (Subgroup.mem_centralizer_iff.mp hvc) ((n : G) ^ m) hgK
    apply Subtype.ext
    rw [ggConjAut_pow_apply Bs hnN m v, hcomm]
    group
  have hc : (ggConjAut Bs hnN ^ m) ^ 2 ^ k = 1 := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [← pow_mul, ggConjAut_pow_apply Bs hnN (m * 2 ^ k) b]
    have hpow : (n : G) ^ (m * 2 ^ k) = 1 := by
      rw [Nat.mul_comm m (2 ^ k), ← horder, pow_orderOf_eq_one]
    rw [hpow]
    simp
  have hVc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
    Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2)
  have hVp : ∀ v : ↥Bs, v ^ p = 1 := fun v => Subtype.ext (hBs.2 v v.2)
  have hlifts : GGIsReflection p (ggConjAut Bs hnN ^ m) :=
    isReflection_of_quotient hp hp2 hVc hVp (ggGamma K hN).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _) (ggConjAut Bs hnN ^ m)
      (ggConjAut (ggGamma K hN).range hn) hGOGm hfix hc hrefl.1 hrefl.2
  exact ⟨m, hg, by rw [hg_eq]; exact hlifts, by rw [hg_eq]; exact hGOGm⟩

omit [Finite G] in
theorem map_ggHypCent_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) {n : X}
    (hn : MulAut.conj n ∈ Subgroup.normalizer ((ggGamma X hBsN).range : Set (MulAut ↥X)))
    {g : G} (hgX : g ∈ X) (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (ht2 : ggConjAut Bs hg ^ 2 = 1)
    (hover : GGOverGamma hBsN (ggConjAut Bs hg) (ggConjAut (ggGamma X hBsN).range hn)) :
    (ggHypCent (ggGamma X hBsN).range n).map X.subtype =
      X ⊓ Subgroup.centralizer (ggFixG Bs (ggConjAut Bs hg) : Set G) := by
  set γ := ggGamma X hBsN with hγ
  set t := ggConjAut Bs hg with ht
  have hγt : ∀ b : Bs, γ (t b) = MulAut.conj n * γ b * (MulAut.conj n)⁻¹ := by
    intro b
    have h := congrArg Subtype.val (hover b)
    simpa [ggConjAut_apply] using h
  have htt : ∀ b : Bs, t (t b) = b := by
    intro b
    have := congrArg (fun φ : MulAut ↥Bs => φ b) ht2
    simpa [pow_two, MulAut.mul_apply] using this
  have key : ∀ b : Bs, MulAut.conj n * γ b = γ b * MulAut.conj n ↔ t b = b := by
    intro b
    constructor
    · intro hc
      have h1 : γ (t b) = γ b := by rw [hγt b, hc, mul_inv_cancel_right]
      set u : Bs := t b * b⁻¹ with hu
      have hu1 : γ u = 1 := by rw [hu, map_mul, map_inv, h1, mul_inv_cancel]
      have huc : (u : G) ∈ Subgroup.centralizer (X : Set G) :=
        (ggGamma_eq_one_iff X hBsN u).mp hu1
      have hufix : t u = u := by
        apply Subtype.ext
        rw [ht, ggConjAut_apply, Subgroup.mem_centralizer_iff.mp huc g hgX, mul_inv_cancel_right]
      have htu : t u = u⁻¹ := by
        rw [hu, map_mul, map_inv, htt, mul_inv_rev, inv_inv]
      have huu : u = u⁻¹ := hufix.symm.trans htu
      have hu2 : u ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 2 [huu]
        exact mul_inv_cancel u
      have hup : u ^ p = 1 := Subtype.ext (by simpa using hBs.2 (u : G) u.2)
      have hcop : Nat.Coprime 2 p :=
        (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
      have hord : orderOf u = 1 := by
        have h2 := orderOf_dvd_of_pow_eq_one hu2
        have hp' := orderOf_dvd_of_pow_eq_one hup
        have h := Nat.dvd_gcd h2 hp'
        rw [Nat.Coprime.gcd_eq_one hcop] at h
        exact Nat.dvd_one.mp h
      have hu1' : u = 1 := orderOf_eq_one_iff.mp hord
      exact mul_inv_eq_one.mp hu1'
    · intro hfix
      rw [← mul_inv_eq_iff_eq_mul, ← hγt b, hfix]
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro e ⟨b, hb, rfl⟩
    have hb' : t b = b := hb
    have hc := (key b).mpr hb'
    have hmem : l ∈ ggFix (γ b) := by
      have h := hl
      simp only [ggHypCent, Subgroup.mem_iInf] at h
      exact h (γ b) ⟨⟨b, rfl⟩, hc⟩
    have hfx : γ b l = l := hmem
    have h := congrArg Subtype.val hfx
    rw [hγ, ggGamma_coe] at h
    simp only [Subgroup.coe_subtype]
    calc (b : G) * l = ((b : G) * l * (b : G)⁻¹) * b := by group
      _ = l * b := by rw [h]
  · rintro ⟨hyX, hyC⟩
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    simp only [ggHypCent, Subgroup.mem_iInf]
    rintro a ⟨⟨b, rfl⟩, hc⟩
    have hb := (key b).mp hc
    have hbE : (b : G) ∈ ggFixG Bs t := ⟨b, hb, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hyC (b : G) hbE
    change γ b ⟨y, hyX⟩ = ⟨y, hyX⟩
    apply Subtype.ext
    rw [hγ, ggGamma_coe]
    simp only
    rw [hcomm, mul_inv_cancel_right]

theorem isReflection_or_eq_one_of_overGamma {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    {c : MulAut ↥Bs} {a : MulAut ↥(ggGamma X hBsN).range} (hover : GGOverGamma hBsN c a)
    (hc : GGIsReflection p c) : GGIsReflection p a ∨ a = 1 := by
  classical
  have := Fact.mk hp
  set π := (ggGamma X hBsN).rangeRestrict with hπ
  have hπs : Function.Surjective π := MonoidHom.rangeRestrict_surjective _
  have hBc : ∀ u v : ↥Bs, u * v = v * u := fun u v =>
    Subtype.ext (IsElemAbelian.comm hBs u.2 v.2)
  have hBp : ∀ u : ↥Bs, u ^ p = 1 := fun u => Subtype.ext (by simpa using hBs.2 u u.2)
  have hAc : ∀ u v : ↥(ggGamma X hBsN).range, u * v = v * u := by
    intro u v
    obtain ⟨u', rfl⟩ := hπs u
    obtain ⟨v', rfl⟩ := hπs v
    rw [← map_mul, ← map_mul, hBc]
  have hcc : ∀ u, c (c u) = u := by
    intro u
    have := congrArg (fun φ : MulAut ↥Bs => φ u) hc.1
    simpa [pow_two, MulAut.mul_apply] using this
  have ha2 : a ^ 2 = 1 := by
    apply MulEquiv.ext
    intro w
    obtain ⟨u, rfl⟩ := hπs w
    have h := (hover.pow 2) u
    rw [hc.1] at h
    rw [← h]
    rfl
  let δ : ↥Bs →* ↥Bs :=
    { toFun := fun u => u * (c u)⁻¹
      map_one' := by simp
      map_mul' := fun u v => by
        rw [map_mul, mul_inv_rev]
        calc u * v * ((c v)⁻¹ * (c u)⁻¹) = u * (v * (c v)⁻¹ * (c u)⁻¹) := by group
          _ = u * ((c u)⁻¹ * (v * (c v)⁻¹)) := by rw [hBc _ (c u)⁻¹]
          _ = u * (c u)⁻¹ * (v * (c v)⁻¹) := by group }
  have hδapp : ∀ u, δ u = u * (c u)⁻¹ := fun _ => rfl
  have hker : Nat.card δ.ker = Nat.card {u : ↥Bs // c u = u} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun u => by
      rw [MonoidHom.mem_ker, hδapp, mul_inv_eq_one, eq_comm])
  have hrange : Nat.card δ.range = p := by
    have h := TableB.card_range_mul_card_ker δ
    rw [hker, ← hc.2] at h
    have hpos : 0 < Nat.card {u : ↥Bs // c u = u} := by
      have : Nonempty {u : ↥Bs // c u = u} := ⟨⟨1, map_one c⟩⟩
      exact Nat.card_pos
    rw [mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  have hcyc : IsCyclic δ.range := isCyclic_of_prime_card hrange
  obtain ⟨⟨b₁, hb₁⟩, hgen⟩ := hcyc.exists_generator
  have hδmem : ∀ u, ∃ e : ℕ, δ u = b₁ ^ e := by
    intro u
    have hx := hgen ⟨δ u, ⟨u, rfl⟩⟩
    rw [← mem_powers_iff_mem_zpowers] at hx
    obtain ⟨e, he⟩ := hx
    exact ⟨e, by simpa using (congrArg Subtype.val he).symm⟩
  obtain ⟨u₀, hu₀⟩ := hb₁
  have hcb₁ : c b₁ = b₁⁻¹ := by
    rw [← hu₀, hδapp, map_mul, map_inv, hcc, mul_inv_rev, inv_inv]
  set a₁ := π b₁ with ha₁
  have ha₁p : a₁ ^ p = 1 := by rw [ha₁, ← map_pow, hBp, map_one]
  have haa₁ : a a₁ = a₁⁻¹ := by rw [ha₁, ← hover b₁, hcb₁, map_inv]
  have hδa : ∀ w, ∃ e : ℕ, w * (a w)⁻¹ = a₁ ^ e := by
    intro w
    obtain ⟨u, rfl⟩ := hπs w
    obtain ⟨e, he⟩ := hδmem u
    refine ⟨e, ?_⟩
    rw [← hover u, ← map_inv, ← map_mul, ← hδapp, he, map_pow]
  by_cases h1 : a₁ = 1
  · right
    apply MulEquiv.ext
    intro w
    obtain ⟨e, he⟩ := hδa w
    rw [h1, one_pow, mul_inv_eq_one] at he
    exact he.symm
  · left
    refine ⟨ha2, card_fix_mul_of_le_zpowers hp hAc a ha₁p hδa ?_⟩
    rw [haa₁, inv_inv]
    intro h
    have h2 : a₁ ^ 2 = 1 := by rw [pow_two]; exact h
    apply h1
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one ha₁p)
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem isPComponent_subgroupOf_of_isComponentOf_of_dvd {p : ℕ} [Fact p.Prime]
    {J Y : Subgroup G} (hJ : IsComponentOf J Y) (hpJ : p ∣ Nat.card J) :
    IsPComponent p (J.subgroupOf Y) :=
  (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p Y J
    hJ.1).mpr (lBalanceIsPComponent_of_isComponentOf hJ (not_le_lBalancePrimeCore_of_dvd hpJ))

omit [Finite G] in
theorem ggTorusWeylElt_of_mem_normalizer {p : ℕ} {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) {g : G} (hgX : g ∈ X)
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) :
    GGTorusWeylElt p (ggGamma X hBsN).range ⟨g, hgX⟩ := by
  rintro _ ⟨b, rfl⟩
  have hw : (((⟨g, hgX⟩ : X) * (ggGamma X hBsN b ⟨g, hgX⟩)⁻¹ : X) : G) =
      g * b * g⁻¹ * (b : G)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ggGamma_coe]
    group
  have hwBs : g * b * g⁻¹ * (b : G)⁻¹ ∈ Bs :=
    Bs.mul_mem ((Subgroup.mem_normalizer_iff.mp hg b).mp b.2) (Bs.inv_mem b.2)
  refine ⟨?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, hw, Subgroup.coe_one]
    exact hBs.2 _ hwBs
  · rintro _ ⟨b', rfl⟩
    apply Subtype.ext
    rw [ggGamma_coe, hw, IsElemAbelian.comm hBs b'.2 hwBs, mul_inv_cancel_right]

theorem ggTorusWeylElt_of_conj_mem_normalizer {L' : Type} [Group L'] {p : ℕ} {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hinn : ∀ a ∈ A, ∃ x : L', a = MulAut.conj x)
    (hcomm : ∀ x y : L', MulAut.conj x ∈ A → MulAut.conj y ∈ A → x * y = y * x)
    {n : L'} (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    GGTorusWeylElt p A n := by
  let P : Subgroup L' := A.comap (MulAut.conj : L' →* MulAut L')
  have hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    hcomm x y (Subgroup.mem_comap.mp hx) (Subgroup.mem_comap.mp hy)
  intro a ha
  obtain ⟨x, hx⟩ := hinn a ha
  have hxP' : MulAut.conj x ∈ A := by rw [← hx]; exact ha
  have hxP : x ∈ P := Subgroup.mem_comap.mpr hxP'
  have huP' : MulAut.conj (n * x * n⁻¹) ∈ A := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hn (MulAut.conj x)).mp hxP'
  have huP : n * x * n⁻¹ ∈ P := Subgroup.mem_comap.mpr huP'
  have hz : n * (a n)⁻¹ = (n * x * n⁻¹) * x⁻¹ := by
    rw [hx, MulAut.conj_apply, mul_inv_rev, mul_inv_rev]
    group
  have hxp : x ^ p ∈ Subgroup.center L' := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : MulAut.conj (x ^ p) = 1 := by
      rw [map_pow]
      exact hA.2 (MulAut.conj x) hxP'
    have h2 : MulAut.conj (x ^ p) y = y := by rw [h1]; rfl
    rw [MulAut.conj_apply] at h2
    have h3 : x ^ p * y = y * x ^ p := by
      calc x ^ p * y = x ^ p * y * (x ^ p)⁻¹ * (x ^ p) := by group
        _ = y * x ^ p := by rw [h2]
    exact h3.symm
  have hcen : MulAut.conj n (x ^ p) = x ^ p := by
    rw [MulAut.conj_apply, Subgroup.mem_center_iff.mp hxp n, mul_assoc, mul_inv_cancel, mul_one]
  have hup : (n * x * n⁻¹) ^ p = x ^ p := by
    rw [show n * x * n⁻¹ = MulAut.conj n x from (MulAut.conj_apply n x).symm, ← map_pow, hcen]
  refine ⟨?_, fun a' ha' => ?_⟩
  · rw [hz]
    have hc : Commute (n * x * n⁻¹) x⁻¹ := hP (n * x * n⁻¹) huP x⁻¹ (P.inv_mem hxP)
    rw [hc.mul_pow, hup, inv_pow]
    exact mul_inv_cancel _
  · obtain ⟨y, hy⟩ := hinn a' ha'
    have hyP' : MulAut.conj y ∈ A := by rw [← hy]; exact ha'
    have hyP : y ∈ P := Subgroup.mem_comap.mpr hyP'
    have h1 : Commute y (n * x * n⁻¹) := hP y hyP (n * x * n⁻¹) huP
    have h2 : Commute y x⁻¹ := hP y hyP x⁻¹ (P.inv_mem hxP)
    have hc : Commute y ((n * x * n⁻¹) * x⁻¹) := h1.mul_right h2
    rw [hz, hy, MulAut.conj_apply, hc.eq, mul_assoc, mul_inv_cancel, mul_one]


end CFSG.StandardType

end
