module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockCentral
public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType

open CFSG.ComponentClassification.OuterAutomorphisms

private theorem ggHalfKGCReduce_pow_two_eq_one {P : Type} [Group P] [Finite P]
    (h : Nat.card P ≤ 2) (g : P) : g ^ 2 = 1 := by
  have hdvd : orderOf g ∣ Nat.card P := orderOf_dvd_natCard g
  have hle : orderOf g ≤ 2 := le_trans (Nat.le_of_dvd Nat.card_pos hdvd) h
  have hge : 1 ≤ orderOf g := orderOf_pos g
  rcases (by omega : orderOf g = 1 ∨ orderOf g = 2) with ho | ho
  · rw [show g = 1 from orderOf_eq_one_iff.mp ho, one_pow]
  · rw [← ho, pow_orderOf_eq_one]

private theorem ggHalfKGCReduce_isSolvable_of_card_le_two {P : Type} [Group P] [Finite P]
    (h : Nat.card P ≤ 2) : Group.IsSolvable P := by
  apply Group.isSolvable_of_comm
  intro a b
  have ha : a * a = 1 := by simpa [pow_two] using ggHalfKGCReduce_pow_two_eq_one h a
  have hb : b * b = 1 := by simpa [pow_two] using ggHalfKGCReduce_pow_two_eq_one h b
  have hab : a * b * (a * b) = 1 := by
    simpa [pow_two] using ggHalfKGCReduce_pow_two_eq_one h (a * b)
  calc a * b = a * (a * b * (a * b)) * b := by rw [hab]; group
    _ = (a * a) * (b * a) * (b * b) := by group
    _ = b * a := by rw [ha, hb]; group

private theorem ggHalfKGCReduce_center_eq_bot_of_mulEquiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (hH : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hgH : e g ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨k, rfl⟩ := e.surjective h
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hg k]
  rw [hH, Subgroup.mem_bot] at hgH
  exact e.injective (by rw [hgH, map_one])

theorem ggHalfNbrCent_of_centSolv {Y : Type} [Group Y] [Finite Y] (X J R : Subgroup Y) (x : Y)
    (n : ℕ) (hX : CFSG.Assembly.IsQuasisimple ↥X)
    (hOut : Nat.card (Outer (↥X ⧸ Subgroup.center ↥X)) ≤ 2)
    (hlt : Nat.card (Matrix.SpecialLinearGroup (Fin (n - 1)) (GaloisField 2 1)) <
      Nat.card (↥X ⧸ Subgroup.center ↥X))
    (hcs : GGKGCCentSolv (↥X ⧸ Subgroup.center ↥X) n)
    (hx : x ∈ Subgroup.normalizer (X : Set Y)) (hx3 : x ^ 3 = 1)
    (hJ : Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin (n - 1)) (GaloisField 2 1)))
    (hJc : CFSG.Assembly.IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set Y)))
    (hR : R ≤ Subgroup.normalizer (X : Set Y)) (hRJ : R ≤ Subgroup.centralizer (J : Set Y))
    (hRp : ⁅R, R⁆ = R) : R ≤ Subgroup.centralizer (X : Set Y) := by
  haveI hPerfX : Group.IsPerfect ↥X := Group.IsPerfect.mk hX.1
  haveI hSolvOutP : Group.IsSolvable (Outer (↥X ⧸ Subgroup.center ↥X)) :=
    ggHalfKGCReduce_isSolvable_of_card_le_two hOut
  haveI hSolvOutX : Group.IsSolvable (Outer ↥X) := solvable_of_centerQuotient ↥X
  haveI hPerfR : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hRp
  let P : Type := ↥X ⧸ Subgroup.center ↥X
  let π : ↥X →* P := QuotientGroup.mk' (Subgroup.center ↥X)
  have hker : (MulAut.conj : ↥X →* MulAut ↥X).ker = Subgroup.center ↥X := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h b
      have hb : (MulAut.conj a) b = (1 : MulAut ↥X) b := congrArg (fun f : MulAut ↥X => f b) h
      rw [MulAut.conj_apply, MulAut.one_apply] at hb
      have hab : a * b = b * a := by
        calc a * b = a * b * a⁻¹ * a := by group
          _ = b * a := by rw [hb]
      exact hab.symm
    · intro h
      ext b
      rw [MulAut.conj_apply, MulAut.one_apply, ← h b]
      group
  have hJX : J ≤ X := hJc.1.trans inf_le_left
  have hcenterJ : Subgroup.center ↥J = ⊥ :=
    ggHalfKGCReduce_center_eq_bot_of_mulEquiv (Classical.choice hJ) (by
      simpa using CFSG.StandardType.GGHalf.center_eq_bot (n - 1))
  let cx : MulAut ↥X := (Subgroup.normalizerMonoidHom X) ⟨x, hx⟩
  have hcx_apply (u : ↥X) : ((cx u : ↥X) : Y) = x * (u : Y) * x⁻¹ := by
    change (((Subgroup.normalizerMonoidHom X) ⟨x, hx⟩) u : Y) = x * (u : Y) * x⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hx3N : (⟨x, hx⟩ : Subgroup.normalizer (X : Set Y)) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hx3
  have hcx3 : cx ^ 3 = 1 := by
    change ((Subgroup.normalizerMonoidHom X) ⟨x, hx⟩) ^ 3 = 1
    rw [← map_pow, hx3N, map_one]
  have hOutP2 : ∀ w : Outer (↥X ⧸ Subgroup.center ↥X), w ^ 2 = 1 :=
    ggHalfKGCReduce_pow_two_eq_one hOut
  let z : Outer ↥X := (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥X)) cx
  have hz3 : z ^ 3 = 1 := by
    change ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥X)) cx) ^ 3 = 1
    rw [← map_pow, hcx3, map_one]
  have hz1 : z = 1 := by
    apply centerQuotient_outer_injective ↥X
    rw [map_one]
    have h2 : (centerQuotientOuterHom ↥X z) ^ 2 = 1 := hOutP2 _
    have h3 : (centerQuotientOuterHom ↥X z) ^ 3 = 1 := by
      rw [← map_pow, hz3, map_one]
    calc centerQuotientOuterHom ↥X z = centerQuotientOuterHom ↥X z * 1 := (mul_one _).symm
      _ = centerQuotientOuterHom ↥X z * (centerQuotientOuterHom ↥X z) ^ 2 := by rw [h2]
      _ = (centerQuotientOuterHom ↥X z) ^ 3 := by group
      _ = 1 := h3
  have hcxInner : cx ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥X :=
    (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner ↥X) cx).mp
      (show (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥X)) cx = 1 from hz1)
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hcxInner
  have ha : MulAut.conj a = cx := ha
  have ha3 : a ^ 3 ∈ Subgroup.center ↥X := by
    rw [← hker, MonoidHom.mem_ker]
    change MulAut.conj (a ^ 3) = 1
    rw [map_pow, ha, hcx3]
  let k : P := π a
  have hk3 : k ^ 3 = 1 := by
    change (QuotientGroup.mk' (Subgroup.center ↥X) a) ^ 3 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center ↥X) (a ^ 3)).mpr ha3
  let toNorm : ↥R →* Subgroup.normalizer (X : Set Y) :=
    { toFun := fun r => ⟨(r : Y), hR r.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun r s => Subtype.ext rfl }
  let c : ↥R →* MulAut ↥X := (Subgroup.normalizerMonoidHom X).comp toNorm
  have hc_apply (r : ↥R) (u : ↥X) :
      ((c r u : ↥X) : Y) = (r : Y) * (u : Y) * (r : Y)⁻¹ := by
    change (((Subgroup.normalizerMonoidHom X) ⟨(r : Y), hR r.2⟩) u : Y) =
      (r : Y) * (u : Y) * (r : Y)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  let aR : ↥R → ↥X := fun r => Classical.choose (perfect_action_inner c r)
  have haR' : ∀ r : ↥R, c r = MulAut.conj (aR r) := fun r => Classical.choose_spec (perfect_action_inner c r)
  have hcommR : ∀ (r : ↥R) (u : ↥J),
      aR r * Subgroup.inclusion hJX u = Subgroup.inclusion hJX u * aR r := by
    intro r u
    have hcomm : (u : Y) * (r : Y) = (r : Y) * (u : Y) :=
      Subgroup.mem_centralizer_iff.mp (hRJ r.2) (u : Y) u.2
    have hcru : c r (Subgroup.inclusion hJX u) = Subgroup.inclusion hJX u := by
      apply Subtype.ext
      rw [hc_apply]
      change (r : Y) * (u : Y) * (r : Y)⁻¹ = (u : Y)
      rw [← hcomm]
      group
    have hru := congrArg (fun f : MulAut ↥X => f (Subgroup.inclusion hJX u)) (haR' r)
    rw [hcru, MulAut.conj_apply] at hru
    calc aR r * Subgroup.inclusion hJX u
        = aR r * Subgroup.inclusion hJX u * (aR r)⁻¹ * aR r := by group
      _ = Subgroup.inclusion hJX u * aR r := by rw [← hru]
  have hub : ∀ u : ↥J, a * Subgroup.inclusion hJX u = Subgroup.inclusion hJX u * a := by
    intro u
    have hcomm : (u : Y) * x = x * (u : Y) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hJc.1 u.2).2
    have hcxu : cx (Subgroup.inclusion hJX u) = Subgroup.inclusion hJX u := by
      apply Subtype.ext
      rw [hcx_apply]
      change x * (u : Y) * x⁻¹ = (u : Y)
      rw [← hcomm]
      group
    have hax := congrArg (fun f : MulAut ↥X => f (Subgroup.inclusion hJX u)) ha
    rw [hcxu, MulAut.conj_apply] at hax
    calc a * Subgroup.inclusion hJX u = a * Subgroup.inclusion hJX u * a⁻¹ * a := by group
      _ = Subgroup.inclusion hJX u * a := by rw [hax]
  let πJ : ↥J →* P := (QuotientGroup.mk' (Subgroup.center ↥X)).comp (Subgroup.inclusion hJX)
  have hHZ : (J.subgroupOf X) ⊓ Subgroup.center ↥X = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    rw [Subgroup.mem_inf] at hu
    have hmem : (⟨(u : Y), hu.1⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro v
      have h2 : ((v : Y) * (u : Y)) = ((u : Y) * (v : Y)) :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hu.2 ⟨(v : Y), hJX v.2⟩)
      exact Subtype.ext h2
    rw [hcenterJ, Subgroup.mem_bot] at hmem
    exact Subtype.ext (by simpa using congrArg Subtype.val hmem)
  have hinj : Function.Injective πJ := by
    intro u v huv
    have h1 : πJ (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
    have hZ : Subgroup.inclusion hJX (u * v⁻¹) ∈ Subgroup.center ↥X :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center ↥X) (Subgroup.inclusion hJX (u * v⁻¹))).mp h1
    have hH : Subgroup.inclusion hJX (u * v⁻¹) ∈ J.subgroupOf X := by
      change ((u * v⁻¹ : ↥J) : Y) ∈ J
      exact (u * v⁻¹).2
    have hbot : Subgroup.inclusion hJX (u * v⁻¹) ∈ (⊥ : Subgroup ↥X) := by
      rw [← hHZ]
      exact ⟨hH, hZ⟩
    rw [Subgroup.mem_bot] at hbot
    have : u * v⁻¹ = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hbot
    exact mul_inv_eq_one.mp this
  let Jbar : Subgroup P := πJ.range
  have hJbarIso : Nonempty (↥Jbar ≃* Matrix.SpecialLinearGroup (Fin (n - 1)) (GaloisField 2 1)) :=
    ⟨(MonoidHom.ofInjective hinj).symm.trans (Classical.choice hJ)⟩
  have hkCent : k ∈ Subgroup.centralizer (Jbar : Set P) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    change y ∈ πJ.range at hy
    rw [MonoidHom.mem_range] at hy
    obtain ⟨u, rfl⟩ := hy
    have h := congrArg (QuotientGroup.mk' (Subgroup.center ↥X)) (hub u)
    rw [map_mul, map_mul] at h
    exact h.symm
  let φ : ↥R →* P :=
    { toFun := fun r => QuotientGroup.mk' (Subgroup.center ↥X) (aR r)
      map_one' := by
        apply (QuotientGroup.eq_one_iff (N := Subgroup.center ↥X) (aR 1)).mpr
        rw [← hker, MonoidHom.mem_ker]
        change MulAut.conj (aR 1) = 1
        rw [← haR' 1, map_one]
      map_mul' := by
        intro r s
        have hconj : MulAut.conj (aR (r * s)) = MulAut.conj (aR r * aR s) := by
          rw [← haR' (r * s), map_mul, haR' r, haR' s, map_mul]
        have hmem : (aR (r * s))⁻¹ * (aR r * aR s) ∈ Subgroup.center ↥X := by
          rw [← hker, MonoidHom.mem_ker]
          change MulAut.conj ((aR (r * s))⁻¹ * (aR r * aR s)) = 1
          rw [map_mul, map_inv, hconj, map_mul]
          group
        have hEq : QuotientGroup.mk' (Subgroup.center ↥X) (aR (r * s)) =
            QuotientGroup.mk' (Subgroup.center ↥X) (aR r * aR s) :=
          (QuotientGroup.eq (s := Subgroup.center ↥X)).mpr hmem
        rw [hEq, map_mul] }
  have hφle : φ.range ≤ Subgroup.centralizer (Jbar : Set P) := by
    intro y hy
    rw [MonoidHom.mem_range] at hy
    obtain ⟨r, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    change w ∈ πJ.range at hw
    rw [MonoidHom.mem_range] at hw
    obtain ⟨u, rfl⟩ := hw
    have h := congrArg (QuotientGroup.mk' (Subgroup.center ↥X)) (hcommR r u)
    rw [map_mul, map_mul] at h
    exact h.symm
  by_cases hk1 : k = 1
  ·
    have haZ : a ∈ Subgroup.center ↥X := (QuotientGroup.eq_one_iff (N := Subgroup.center ↥X) a).mp hk1
    have haK : a ∈ (MulAut.conj : ↥X →* MulAut ↥X).ker := by rwa [hker]
    have hconj_a : MulAut.conj a = 1 := MonoidHom.mem_ker.mp haK
    have hcx1 : cx = 1 := by rw [← ha, hconj_a]
    have hxCent : x ∈ Subgroup.centralizer (X : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hcu : cx ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [hcx1]; rfl
      have hcoe := congrArg Subtype.val hcu
      rw [hcx_apply] at hcoe
      have hxu : x * u = u * x := by
        calc x * u = x * u * x⁻¹ * x := by group
          _ = u * x := by rw [hcoe]
      exact hxu.symm
    have hXleC : X ≤ Subgroup.centralizer ({x} : Set Y) := by
      intro u hu
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hxCent u hu
    have hinf : X ⊓ Subgroup.centralizer ({x} : Set Y) = X := inf_eq_left.mpr hXleC
    have hJcX : CFSG.Assembly.IsComponentOf J X := by
      refine ⟨hJc.1.trans (le_of_eq hinf), ?_, hJc.2.2⟩
      have hsn := hJc.2.1
      rwa [hinf] at hsn
    have hJX' : J ≤ X := hJcX.1
    let H : Subgroup ↥X := J.subgroupOf X
    have hHsub : H.IsSubnormal := (CFSG.Assembly.IsSubnormal.iff_subgroupOf hJX').mp hJcX.2.1
    have hOsn : CFSG.Open.IsSubnormal H ⊤ := (CFSG.Open.IsSubnormal.top_iff).mpr hHsub
    have hQ : CFSG.Open.IsQuasisimple ↥X := hX
    rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hQ H hOsn with
      hcenter | htop
    ·
      have hJabel : ∀ p q : ↥J, p * q = q * p := by
        intro p q
        apply Subtype.ext
        have hp : (⟨(p : Y), hJX p.2⟩ : ↥X) ∈ H := by
          change (p : Y) ∈ J
          exact p.2
        have hc := hcenter hp
        simpa using (Subgroup.mem_center_iff.mp hc ⟨(q : Y), hJX q.2⟩).symm
      haveI hPerfJ : Group.IsPerfect ↥J := Group.IsPerfect.mk hJc.2.2.1
      have hsolv : Group.IsSolvable ↥J := Group.isSolvable_of_comm fun p q => hJabel p q
      haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJc.2.2.2
      haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := IsSimpleGroup.toNontrivial
      haveI : Nontrivial ↥J :=
        Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
      exfalso
      exact Group.IsPerfect.not_isSolvable (G := ↥J) hsolv
    ·
      have hXJ : X ≤ J := by
        intro y hy
        have : (⟨y, hy⟩ : ↥X) ∈ J.subgroupOf X := by
          change (⟨y, hy⟩ : ↥X) ∈ H
          rw [htop]
          exact Subgroup.mem_top _
        exact this
      have hJeq : J = X := le_antisymm hJX' hXJ
      simpa [hJeq] using hRJ
  ·
    have hDsolv : Group.IsSolvable ↥(Subgroup.centralizer (Jbar : Set P)) :=
      hcs Jbar k hJbarIso hk3 hk1 hkCent
    have hφperf : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
    let incl : ↥φ.range →* ↥(Subgroup.centralizer (Jbar : Set P)) :=
      { toFun := fun y => ⟨y, hφle y.2⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun y z => Subtype.ext rfl }
    have hincl : Function.Injective incl := by
      intro y z h
      have h' : (incl y : P) = (incl z : P) := congrArg Subtype.val h
      exact Subtype.ext h'
    have hφrangeSolv : Group.IsSolvable ↥φ.range :=
      Group.isSolvable_of_isSolvable_injective (f := incl) hincl
    have hφbot : φ.range = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      by_contra hyne
      haveI : Nontrivial ↥φ.range :=
        ⟨⟨y, hy⟩, ⟨1, φ.range.one_mem⟩, fun h => hyne (Subtype.ext_iff.mp h)⟩
      haveI : Group.IsPerfect ↥φ.range := hφperf
      exact Group.IsPerfect.not_isSolvable (G := ↥φ.range) hφrangeSolv
    have hcr1_all : ∀ r : ↥R, c r = 1 := by
      intro r
      have hφr1 : φ r = 1 := by
        have hmem : φ r ∈ φ.range := MonoidHom.mem_range.mpr ⟨r, rfl⟩
        rw [hφbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      have haRZ : aR r ∈ Subgroup.center ↥X :=
        (QuotientGroup.eq_one_iff (N := Subgroup.center ↥X) (aR r)).mp hφr1
      have hmemker : aR r ∈ (MulAut.conj : ↥X →* MulAut ↥X).ker := by rwa [hker]
      have hconj : MulAut.conj (aR r) = 1 := MonoidHom.mem_ker.mp hmemker
      rw [haR' r, hconj]
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hcu : c ⟨r, hr⟩ ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [hcr1_all ⟨r, hr⟩]; rfl
    have hcoe := congrArg Subtype.val hcu
    rw [hc_apply ⟨r, hr⟩ ⟨u, hu⟩] at hcoe
    have hru : (r : Y) * u = u * (r : Y) := by
      calc (r : Y) * u = (r : Y) * u * (r : Y)⁻¹ * (r : Y) := by group
        _ = u * (r : Y) := by rw [hcoe]
    exact hru.symm

end CFSG.StandardType

end
