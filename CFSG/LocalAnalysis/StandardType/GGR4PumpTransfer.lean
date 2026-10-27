module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs
public import CFSG.LocalAnalysis.StandardType.GGR4Lemma47c
public import CFSG.LocalAnalysis.StandardType.GGR4AutInn
public import CFSG.LocalAnalysis.StandardType.GGR4Centre
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

open scoped Pointwise

private theorem r4m_coprime_of_order_eq_two_pow {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {g : Y} (h : ∃ k : ℕ, orderOf g = 2 ^ k) : Nat.Coprime p (orderOf g) := by
  obtain ⟨k, hk⟩ := h
  rw [hk]
  refine Nat.Coprime.pow_right k ((hp.coprime_iff_not_dvd).mpr ?_)
  intro hdvd
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact hp2 (le_antisymm hle hp.two_le)

private theorem r4m_center_coprime {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hZ : GGCentreTwoKnown) {lab : LargeEvenLabel}
    (hlab2 : LargeEvenInLambda2 lab)
    (htag : ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank) ∨ lab.tag = .F4)
    (hperf : commutator Y = ⊤) (hlab : GGHasLabel lab (Y ⧸ Subgroup.center Y)) :
    ∀ g ∈ Subgroup.center Y, Nat.Coprime p (orderOf g) := fun g hg =>
  r4m_coprime_of_order_eq_two_pow hp hp2 (ggCentreTwo_of_label hZ hlab2 htag hperf hlab g hg)

private theorem r4m_eq_of_mul_inv_mem_center {X : Type} [Group X] (hperf : commutator X = ⊤)
    {α β : MulAut X} (h : ∀ l : X, α l * (β l)⁻¹ ∈ Subgroup.center X) : α = β := by
  let δ : X →* X :=
    { toFun := fun l => α l * (β l)⁻¹
      map_one' := by simp
      map_mul' := fun l m => by
        have hzm : (α m * (β m)⁻¹) * (β l)⁻¹ = (β l)⁻¹ * (α m * (β m)⁻¹) :=
          (Subgroup.mem_center_iff.mp (h m) ((β l)⁻¹)).symm
        show α (l * m) * (β (l * m))⁻¹ = (α l * (β l)⁻¹) * (α m * (β m)⁻¹)
        rw [map_mul, map_mul, mul_inv_rev]
        calc α l * α m * ((β m)⁻¹ * (β l)⁻¹)
            = α l * ((α m * (β m)⁻¹) * (β l)⁻¹) := by group
          _ = α l * ((β l)⁻¹ * (α m * (β m)⁻¹)) := by rw [hzm]
          _ = (α l * (β l)⁻¹) * (α m * (β m)⁻¹) := by group }
  have hδcenter : ∀ l, δ l ∈ Subgroup.center X := h
  have hker : commutator X ≤ δ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hδcenter b)) (δ a)
  have htop : δ.ker = ⊤ := by rw [eq_top_iff, ← hperf]; exact hker
  ext l
  have hl : l ∈ δ.ker := by rw [htop]; exact Subgroup.mem_top l
  exact mul_inv_eq_one.mp (by simpa [δ] using hl)

theorem r4m_inn_of_subset_inn {G : Type} [Group G]
    {Bs X : Subgroup G} {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* R) (hperf : commutator ↥X = ⊤)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (hIinn : I ⊆ LargeEvenInnSet R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∀ b ∈ Bs, ∃ k ∈ X, ∀ l ∈ X, b * l * b⁻¹ = k * l * k⁻¹ := by
  intro b hb
  let b' : ↥Bs := ⟨b, hb⟩
  have hβmem : ggBeta X θ hBsN b' ∈ I := ggBeta_mem X θ hBsN hBs3 b'
  obtain ⟨ρ, hρ⟩ := hIinn hβmem
  obtain ⟨q, hq⟩ := θ.surjective ρ
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hk : ggQuotHom θ k = ρ := by rw [ggQuotHom_apply, hq]
  have hconj : (MulAut.conj k : MulAut ↥X) = ggGamma X hBsN b' := by
    apply r4m_eq_of_mul_inv_mem_center hperf
    intro m
    rw [← ker_ggQuotHom θ, MonoidHom.mem_ker]
    have hL : ggQuotHom θ ((MulAut.conj k) m) = MulAut.conj ρ (ggQuotHom θ m) := by
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hk, MulAut.conj_apply]
    have hR : ggQuotHom θ (ggGamma X hBsN b' m) = MulAut.conj ρ (ggQuotHom θ m) := by
      rw [← ggBeta_ggQuotHom X hBsN θ b' m, hρ]
    rw [map_mul, map_inv, hL, hR, mul_inv_cancel]
  refine ⟨(k : G), k.2, ?_⟩
  intro l hl
  let l' : ↥X := ⟨l, hl⟩
  have hl' : (MulAut.conj k) l' = (ggGamma X hBsN b') l' := by rw [hconj]
  have h1 := congrArg (fun z : ↥X => (z : G)) hl'
  rw [MulAut.conj_apply, ggGamma_coe] at h1
  exact h1.symm

theorem r4m_hasLabel_subgroupOf {G : Type} [Group G] {lab : LargeEvenLabel}
    {J X : Subgroup G} (hJX : J ≤ X)
    (h : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J)) :
    GGHasLabel lab (↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X)) := by
  let e : ↥(J.subgroupOf X) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJX
  have hmap : Subgroup.map e (Subgroup.center ↥(J.subgroupOf X)) = Subgroup.center ↥J :=
    Subgroup.map_center_eq e
  let iso : (↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X)) ≃*
      (↥J ⧸ Subgroup.center ↥J) := QuotientGroup.congr _ _ e hmap
  refine largeEvenRawDatum_mono (fun R _ _ _ hq => ?_) h
  obtain ⟨g⟩ := hq
  exact ⟨iso.trans g⟩

theorem r4m_component_J {G : Type} [Group G] {p : ℕ} {Bs X J : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) {x : G} (hxBs : x ∈ Bs)
    (hJc : LargeEvenPComponent p (X ⊓ Subgroup.centralizer ({x} : Set G)) J)
    (hJq : CFSG.Assembly.IsQuasisimple J) :
    CFSG.Assembly.IsComponentOf (J.subgroupOf X) (ggFixSub (ggGamma X hBsN ⟨x, hxBs⟩)) := by
  have hmapfix : (ggFixSub (ggGamma X hBsN ⟨x, hxBs⟩)).map X.subtype =
      X ⊓ Subgroup.centralizer ({x} : Set G) := by
    show (ggFix (ggGamma X hBsN ⟨x, hxBs⟩)).map X.subtype = _
    exact map_ggFix_ggGamma X hBsN ⟨x, hxBs⟩
  have hcomp : CFSG.Assembly.IsComponentOf J
      ((ggFixSub (ggGamma X hBsN ⟨x, hxBs⟩)).map X.subtype) := by
    rw [hmapfix]
    exact ⟨hJc.1, hJc.2.1, hJq⟩
  have h := (isComponentOf_comap_of_injective X.subtype X.subtype_injective hcomp).1
  rwa [Subgroup.comap_subtype] at h

theorem r4m_finish {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* R)
    (hBsEA : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hXperf : commutator ↥X = ⊤)
    (hZ' : ∀ g ∈ Subgroup.center ↥X, Nat.Coprime p (orderOf g))
    (hIinn : I ⊆ LargeEvenInnSet R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (z : G) (hzBs : z ∈ Bs) (hzC : z ∈ Subgroup.centralizer (X : Set G)) (hz1 : z ≠ 1)
    {J : Subgroup G} (hJX : J ≤ X) (hEJ : 3 ≤ Nat.log p (Nat.card ↥(Bs ⊓ J))) :
    ∃ A : Subgroup (MulAut ↥X),
      IsElemAbelian p A ∧
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : ↥X, φ (ggQuotHom θ l) = ggQuotHom θ (a l)) ∧
      p ^ 3 ≤ Nat.card ↥A ∧ GGTorusSelfCent p A ∧
      Nat.card ↥(ggAutomizer X Bs) =
        Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range A) ∧
      Nat.card ↥A = Nat.card ↥(Bs ⊓ X) ∧
      Nat.card ↥Bs = Nat.card ↥(Bs ⊓ X) *
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ∧
      p ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ∧
      (ggGamma X hBsN).range = A := by
  have hp : p.Prime := Fact.out
  have hInn : ∀ b ∈ Bs, ∃ k ∈ X, ∀ l ∈ X, b * l * b⁻¹ = k * l * k⁻¹ :=
    r4m_inn_of_subset_inn θ hXperf hBsN hIinn hBs3
  obtain ⟨hsup, hdisj, hself, _hnorm, hcard_aut⟩ := ggLemma47c hBsEA hSC hZ' hInn
  have hBXea : IsElemAbelian p (Bs ⊓ X) := isElemAbelian_mono hBsEA inf_le_left
  let A : Subgroup (MulAut ↥X) :=
    Subgroup.map (MulAut.conj : ↥X →* MulAut ↥X) ((Bs ⊓ X).subgroupOf X)
  have hAker : (MulAut.conj.comp ((Bs ⊓ X).subgroupOf X).subtype).ker = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hkcenter : (k : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro u
      have h2 : (k : ↥X) * u * (k : ↥X)⁻¹ = u := by
        have h := congrArg (fun f : MulAut ↥X => f u) hk
        change (MulAut.conj (k : ↥X)) u = (1 : MulAut ↥X) u at h
        rwa [MulAut.conj_apply, MulAut.one_apply] at h
      have h3 : (k : ↥X) * u = u * (k : ↥X) := by
        calc (k : ↥X) * u = ((k : ↥X) * u * (k : ↥X)⁻¹) * (k : ↥X) := by group
          _ = u * (k : ↥X) := by rw [h2]
      exact h3.symm
    have hmem : (k : ↥X) ∈ (Bs ⊓ X).subgroupOf X ⊓ Subgroup.center ↥X := ⟨k.2, hkcenter⟩
    have hbot : (Bs ⊓ X).subgroupOf X ⊓ Subgroup.center ↥X = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      have hyBX : (y : G) ∈ Bs ⊓ X := Subgroup.mem_subgroupOf.mp hy.1
      have hyp : y ^ p = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hBXea.2 (y : G) hyBX)
      have hcop : Nat.Coprime p (orderOf y) := hZ' y hy.2
      exact orderOf_eq_one_iff.mp (hcop.symm.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hyp))
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hmem))
  have hBXcard : Nat.card ↥A = Nat.card ↥(Bs ⊓ X) := by
    have hf := card_range_mul_card_ker (MulAut.conj.comp ((Bs ⊓ X).subgroupOf X).subtype)
    rw [hAker, Subgroup.card_bot, mul_one] at hf
    have hrange : (MulAut.conj.comp ((Bs ⊓ X).subgroupOf X).subtype).range = A := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange] at hf
    rw [hf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hAabel : IsElemAbelian p A := by
    have hc : ∀ a b : ↥((Bs ⊓ X).subgroupOf X), a * b = b * a := fun a b =>
      Subtype.ext (by
        apply Subtype.ext
        simpa using IsElemAbelian.comm hBXea (Subgroup.mem_subgroupOf.mp a.2)
          (Subgroup.mem_subgroupOf.mp b.2))
    have hpow : ∀ a : ↥((Bs ⊓ X).subgroupOf X), a ^ p = 1 := fun a =>
      Subtype.ext (by
        apply Subtype.ext
        simpa using hBXea.2 ((a : ↥X) : G) (Subgroup.mem_subgroupOf.mp a.2))
    have h := isElemAbelian_range hc hpow
      (MulAut.conj.comp ((Bs ⊓ X).subgroupOf X).subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hAind : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : ↥X, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp ha
    have hk' : (k : G) ∈ Bs ⊓ X := Subgroup.mem_subgroupOf.mp hk
    have hkBs : (k : G) ∈ Bs := (Subgroup.mem_inf.mp hk').1
    refine ⟨ggBeta X θ hBsN ⟨(k : G), hkBs⟩,
      ggBeta_mem X θ hBsN hBs3 ⟨(k : G), hkBs⟩, ?_⟩
    intro l
    rw [ggBeta_ggQuotHom]
    have hthis : ggGamma X hBsN ⟨(k : G), hkBs⟩ l = (MulAut.conj k) l := by
      apply Subtype.ext
      rw [ggGamma_coe, MulAut.conj_apply]
      rfl
    rw [hthis]
  have hp3J : p ^ 3 ≤ Nat.card ↥(Bs ⊓ J) := by
    have hne : Nat.card ↥(Bs ⊓ J) ≠ 0 := by
      intro h0
      have : Nat.log p (Nat.card ↥(Bs ⊓ J)) = 0 := by rw [h0, Nat.log_of_lt hp.pos]
      omega
    exact le_trans (Nat.pow_le_pow_right hp.pos hEJ) (Nat.pow_log_le_self p hne)
  have hp3A : p ^ 3 ≤ Nat.card ↥A := by
    rw [hBXcard]
    exact le_trans hp3J (Subgroup.card_le_of_le (inf_le_inf_left Bs hJX))
  have hAself : GGTorusSelfCent p A := by
    intro n hn hnp
    have hnC : (n : G) ∈ Subgroup.centralizer ((Bs ⊓ X : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hcX : c ∈ X := (Subgroup.mem_inf.mp hc).2
      have hcn : (MulAut.conj ⟨c, hcX⟩ : MulAut ↥X) n = n :=
        hn _ (Subgroup.mem_map.mpr ⟨⟨c, hcX⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩)
      have h2 : c * (n : G) * c⁻¹ = (n : G) := by
        have h := congrArg (fun u : ↥X => (u : G)) hcn
        simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h
      calc c * (n : G) = (c * n * c⁻¹) * c := by group
        _ = (n : G) * c := by rw [h2]
    have hnp' : (n : G) ^ p = 1 := by
      have h := congrArg (fun u : ↥X => (u : G)) hnp
      simpa using h
    have hnBX : (n : G) ∈ Bs ⊓ X := hself (n : G) n.2 hnC hnp'
    exact Subgroup.mem_map.mpr ⟨n, Subgroup.mem_subgroupOf.mpr hnBX, rfl⟩
  have hcardinn : Nat.card ↥(ggAutomizer X (Bs ⊓ X)) =
      Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range A) :=
    ggAutomizer_card_eq_inn inf_le_right hBXea hZ'
  have hcardAutEq : Nat.card ↥(ggAutomizer X Bs) =
      Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range A) :=
    hcard_aut.trans hcardinn
  have hnormC : (Bs ⊓ Subgroup.centralizer (X : Set G)) ≤
      Subgroup.normalizer ((Bs ⊓ X : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer ((Bs ⊓ X : Subgroup G) : Set G))
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (IsElemAbelian.comm hBsEA hc.1 hb.1).symm
  have hdisj' : (Bs ⊓ X) ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have hy' : y ∈ (Bs ⊓ X) ⊓ Subgroup.centralizer (X : Set G) := ⟨hy.1, hy.2.2⟩
    rw [hdisj] at hy'
    exact Subgroup.mem_bot.mp hy'
  have hcardBs : Nat.card ↥Bs = Nat.card ↥(Bs ⊓ X) *
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
    calc Nat.card ↥Bs = Nat.card ↥((Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G))) := by
          conv_lhs => rw [hsup]
      _ = Nat.card ↥(Bs ⊓ X) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
          CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
            (Bs ⊓ X) (Bs ⊓ Subgroup.centralizer (X : Set G)) hnormC (disjoint_iff.mpr hdisj')
  have hzC' : z ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := ⟨hzBs, hzC⟩
  have hpC : p ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    have h1 := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hzC' :
      Subgroup.zpowers z ≤ Bs ⊓ Subgroup.centralizer (X : Set G))
    rwa [Nat.card_zpowers, orderOf_eq_prime (hBsEA.2 z hzBs) hz1] at h1
  have hleBX : (Bs ⊓ X) ≤
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G)) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G)) : Set G))
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (IsElemAbelian.comm hBsEA hb.1 hc.1).symm
  have hgammaA : (ggGamma X hBsN).range = A := by
    apply le_antisymm
    · rintro _ ⟨b, rfl⟩
      have hbsup : (b : G) ∈ (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
        rw [← hsup]; exact b.2
      have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (Bs ⊓ X)
        (Bs ⊓ Subgroup.centralizer (X : Set G)) hleBX
      have hbsup' : (b : G) ∈ ((Bs ⊓ X : Subgroup G) : Set G) *
          ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
        rw [← hcoe]
        exact hbsup
      obtain ⟨b1, hb1, c, hc, hbc⟩ := Set.mem_mul.mp hbsup'
      have hb1X : b1 ∈ X := (Subgroup.mem_inf.mp hb1).2
      have hb1Bs : b1 ∈ Bs := (Subgroup.mem_inf.mp hb1).1
      have hcBs : c ∈ Bs := (Subgroup.mem_inf.mp hc).1
      have hcC : c ∈ Subgroup.centralizer (X : Set G) := hc.2
      have hb_eq : b = (⟨b1, hb1Bs⟩ : ↥Bs) * ⟨c, hcBs⟩ := Subtype.ext (by
        rw [Subgroup.coe_mul]; exact hbc.symm)
      have hc1 : ggGamma X hBsN ⟨c, hcBs⟩ = 1 := by
        rw [ggGamma_eq_one_iff]
        exact hcC
      rw [hb_eq, map_mul, hc1, mul_one]
      exact Subgroup.mem_map.mpr ⟨⟨b1, hb1X⟩, Subgroup.mem_subgroupOf.mpr hb1, by
        ext u
        rw [ggGamma_coe, MulAut.conj_apply]
        rfl⟩
    · rintro _ ⟨k, hk, rfl⟩
      have hk' : (k : G) ∈ Bs ⊓ X := Subgroup.mem_subgroupOf.mp hk
      refine ⟨⟨(k : G), (Subgroup.mem_inf.mp hk').1⟩, ?_⟩
      ext u
      rw [ggGamma_coe, MulAut.conj_apply]
      rfl
  exact ⟨A, hAabel, hAind, hp3A, hAself, hcardAutEq, hBXcard, hcardBs, hpC, hgammaA⟩

theorem ggPumpCInput_of_known
    (hKG : GGPumpCLabelKnown) (hKA : GGPumpCAutKnown) (hZ : GGCentreTwoKnown) :
    GGPumpCInput := by
  intro G _ _ p B Bs x L D J hcfg f hlab hpq z hzD hz1 X hX hJX hJc hmark hEJ hnot
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBS : B ≤ Bs := hcfg.2.1.1
  have hBsEA : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hxBs : x ∈ Bs := hBS hS.2.1
  have hDB : D ≤ B := hcfg.2.2.1.1
  have hzBs : z ∈ Bs := hBS (hDB hzD)
  have hJq : CFSG.Assembly.IsQuasisimple J := (hcfg.2.2.1.2.2.2.2.2.1).2.2
  have hzC : z ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hX.1 hl)
  have hzx : z ∉ Subgroup.zpowers x := by
    intro hz
    apply hnot
    have hzp : z ^ p = 1 := hBsEA.2 z hzBs
    have hzx' : Subgroup.zpowers z = Subgroup.zpowers x := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hzp hz1,
        orderOf_eq_prime (hBsEA.2 x hxBs) hS.2.2.1]
    have hcent := centralizer_singleton_eq_of_zpowers_eq hzx'
    have hXx : X ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [← hcent]
      exact hX.1
    have hxCX : x ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mp (hXx hl)
    have hcomm : (⁅X, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
      exact Subgroup.zpowers_le.mpr hxCX
    rw [hcomm]
    exact bot_le
  have hD : D = Subgroup.closure {x, z} := eq_closure_pair_of_mem hcfg.1 hcfg.2.2 hzD hzx
  obtain ⟨hXperf, lab, hlab2, hraw0⟩ := hmark
  rcases lab with ⟨tag, rank, n⟩
  have hrawKG := hKG p hp hp2 ⟨tag, rank, n⟩ hlab2 _ hraw0
  obtain ⟨R₀, _, I₀, _, hq₀⟩ := largeEvenRawDatum_exists hrawKG
  obtain ⟨_, _, θ₀, hBsN₀, hBs3₀⟩ := hq₀.1
  have hKGinst₀ := hq₀.2
  have hlabX : GGHasLabel ⟨tag, rank, n⟩ (↥X ⧸ Subgroup.center ↥X) :=
    largeEvenRawDatum_mono (fun R _ _ _ h => ⟨h.2.2.choose⟩) hraw0
  let e₀ : MulAut ↥X := ggGamma X hBsN₀ ⟨x, hxBs⟩
  have he1 : e₀ ≠ 1 := by
    intro he
    apply hnot
    have hxC : x ∈ Subgroup.centralizer (X : Set G) :=
      (ggGamma_eq_one_iff X hBsN₀ ⟨x, hxBs⟩).mp he
    have hcomm : (⁅X, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
      exact Subgroup.zpowers_le.mpr hxC
    rw [hcomm]
    exact bot_le
  have hep : e₀ ^ p = 1 := by
    have h1 : (⟨x, hxBs⟩ : ↥Bs) ^ p = 1 := Subtype.ext (by simpa using hBsEA.2 x hxBs)
    show (ggGamma X hBsN₀ ⟨x, hxBs⟩) ^ p = 1
    rw [← map_pow, h1, map_one]
  have hφe : ∃ φ ∈ I₀, ∀ l : ↥X, φ (ggQuotHom θ₀ l) = ggQuotHom θ₀ (e₀ l) :=
    ⟨ggBeta X θ₀ hBsN₀ ⟨x, hxBs⟩,
      ggBeta_mem X θ₀ hBsN₀ hBs3₀ ⟨x, hxBs⟩,
      fun l => ggBeta_ggQuotHom X hBsN₀ θ₀ ⟨x, hxBs⟩ l⟩
  have hJ'comp₀ : IsComponentOf (J.subgroupOf X) (ggFixSub e₀) :=
    r4m_component_J hBsN₀ hxBs hJc hJq
  have hlab' : GGHasLabel ⟨.C, 3, f⟩
      (↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X)) :=
    r4m_hasLabel_subgroupOf hJX hlab
  have hKGuse := hKGinst₀ X (ggQuotHom θ₀) (ggQuotHom_surjective θ₀)
    (by rw [ker_ggQuotHom]) hXperf e₀ he1 hep hφe (J.subgroupOf X) 3 f hJ'comp₀ (by norm_num) hlab'
  have hID : GGInnerDiagInnLabel ⟨tag, rank, n⟩ := by
    rcases hKGuse with ⟨hBC, -, -⟩ | ⟨-, hF4, -⟩
    · rcases hBC with hB | hC
      · exact Or.inl (Or.inl hB)
      · exact Or.inl (Or.inr (Or.inl hC))
    · exact Or.inr (Or.inr (Or.inl hF4))
  have htag' : ((tag = .B ∨ tag = .C) ∧ 3 ≤ rank) ∨ tag = .F4 := by
    rcases hKGuse with ⟨hBC, hlt, -⟩ | ⟨-, hF4, -⟩
    · exact Or.inl ⟨hBC, le_of_lt hlt⟩
    · exact Or.inr hF4
  have hZ' : ∀ g ∈ Subgroup.center ↥X, Nat.Coprime p (orderOf g) :=
    r4m_center_coprime (lab := ⟨tag, rank, n⟩) hp hp2 hZ hlab2 htag' hXperf hlabX
  rcases hKGuse with ⟨hBC, hlt, hn⟩ | ⟨-, hF4, hn⟩
  · rcases hBC with htag | htag
    · subst htag
      subst hn
      have hN3 : 3 ≤ rank := le_of_lt hlt
      have hf : 1 ≤ n := hlab2.1
      have hraw_inn := (largeEvenLabelAll_subset_inn hlab2 hID) _ hraw0
      have hKA_all := (hKA p hp hp2 n hf hpq).1 rank hN3
      have hraw2 := hKA_all _ hraw_inn
      obtain ⟨R, _, I, _, hq2⟩ := largeEvenRawDatum_exists hraw2
      obtain ⟨hQ0guard, hKAinst⟩ := hq2
      obtain ⟨hQ0, hguard⟩ := hQ0guard
      obtain ⟨hs, hna, θ, hBsN, hBs3⟩ := hQ0
      have hIinn : I ⊆ LargeEvenInnSet R := hguard hs hna
      obtain ⟨A, hAabel, hAind, hp3A, hAself, hcardAutEq, hBXcard, hcardBs, hpC, _hgammaA⟩ :=
        r4m_finish θ hBsEA hSC hBsN hXperf hZ' hIinn hBs3 z hzBs hzC hz1 hJX hEJ
      have hKAapp := hKAinst X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
        hXperf A hAabel hAind hp3A hAself
      have hcardAutX : Nat.card ↥(ggAutomizer X Bs) = 2 ^ rank * rank.factorial := by
        rw [hcardAutEq, hKAapp.2]
      have hpN1 : p ^ (rank + 1) ≤ Nat.card ↥Bs := by
        rw [hcardBs, pow_succ]
        exact Nat.mul_le_mul (hBXcard ▸ hKAapp.1) hpC
      exact ⟨rank, hN3, hpN1, Or.inl hcardAutX⟩
    · subst htag
      subst hn
      have hN3 : 3 ≤ rank := le_of_lt hlt
      have hf : 1 ≤ n := hlab2.1
      have hraw_inn := (largeEvenLabelAll_subset_inn hlab2 hID) _ hraw0
      have hKA_all := (hKA p hp hp2 n hf hpq).1 rank hN3
      have hraw2 := hKA_all _ hraw_inn
      obtain ⟨R, _, I, _, hq2⟩ := largeEvenRawDatum_exists hraw2
      obtain ⟨hQ0guard, hKAinst⟩ := hq2
      obtain ⟨hQ0, hguard⟩ := hQ0guard
      obtain ⟨hs, hna, θ, hBsN, hBs3⟩ := hQ0
      have hIinn : I ⊆ LargeEvenInnSet R := hguard hs hna
      obtain ⟨A, hAabel, hAind, hp3A, hAself, hcardAutEq, hBXcard, hcardBs, hpC, _hgammaA⟩ :=
        r4m_finish θ hBsEA hSC hBsN hXperf hZ' hIinn hBs3 z hzBs hzC hz1 hJX hEJ
      have hKAapp := hKAinst X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
        hXperf A hAabel hAind hp3A hAself
      have hcardAutX : Nat.card ↥(ggAutomizer X Bs) = 2 ^ rank * rank.factorial := by
        rw [hcardAutEq, hKAapp.2]
      have hpN1 : p ^ (rank + 1) ≤ Nat.card ↥Bs := by
        rw [hcardBs, pow_succ]
        exact Nat.mul_le_mul (hBXcard ▸ hKAapp.1) hpC
      exact ⟨rank, hN3, hpN1, Or.inl hcardAutX⟩
  · subst hF4
    subst hn
    have hf : 1 ≤ n := hlab2.1
    have hraw_inn := (largeEvenLabelAll_subset_inn hlab2 hID) _ hraw0
    have hKA_all := (hKA p hp hp2 n hf hpq).2
    have hraw2 := hKA_all _ hraw_inn
    obtain ⟨R, _, I, _, hq2⟩ := largeEvenRawDatum_exists hraw2
    obtain ⟨hQ0guard, hKAinst⟩ := hq2
    obtain ⟨hQ0, hguard⟩ := hQ0guard
    obtain ⟨hs, hna, θ, hBsN, hBs3⟩ := hQ0
    have hIinn : I ⊆ LargeEvenInnSet R := hguard hs hna
    obtain ⟨A, hAabel, hAind, hp3A, hAself, hcardAutEq, hBXcard, hcardBs, hpC, hgammaA⟩ :=
      r4m_finish θ hBsEA hSC hBsN hXperf hZ' hIinn hBs3 z hzBs hzC hz1 hJX hEJ
    have heA : ggGamma X hBsN ⟨x, hxBs⟩ ∈ A := by
      rw [← hgammaA]
      exact ⟨⟨x, hxBs⟩, rfl⟩
    have hJ'comp : IsComponentOf (J.subgroupOf X)
        (ggFixSub (ggGamma X hBsN ⟨x, hxBs⟩)) :=
      r4m_component_J hBsN hxBs hJc hJq
    have hlab'' : GGHasLabel ⟨.C, 3, n⟩
        (↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X)) :=
      r4m_hasLabel_subgroupOf hJX hlab
    have hKAapp := hKAinst X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
      hXperf A hAabel hAind hp3A hAself
      ⟨ggGamma X hBsN ⟨x, hxBs⟩, heA, J.subgroupOf X, hJ'comp, hlab''⟩
    have hcardAutX : Nat.card ↥(ggAutomizer X Bs) = 1152 := by
      rw [hcardAutEq, hKAapp.2]
    have hpN1 : p ^ (4 + 1) ≤ Nat.card ↥Bs := by
      rw [hcardBs, pow_succ]
      exact Nat.mul_le_mul (hBXcard ▸ hKAapp.1) hpC
    exact ⟨4, by norm_num, hpN1, Or.inr ⟨rfl, hcardAutX⟩⟩


end CFSG.StandardType
