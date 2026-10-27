module

public import CFSG.LocalAnalysis.StandardType.GGPZEndpointSplit
public import CFSG.LocalAnalysis.StandardType.GGPZMultHolds
public import CFSG.LocalAnalysis.StandardType.GGPZRankTwo
public import CFSG.LocalAnalysis.StandardType.GGPZTrivCoprime
public import CFSG.LocalAnalysis.StandardType.GGPZTrivCore
public import CFSG.LocalAnalysis.StandardType.GGPZTrivAut
public import CFSG.LocalAnalysis.StandardType.GGPZTrivTypeA
public import CFSG.LocalAnalysis.StandardType.GGPZTrivTwA
public import CFSG.LocalAnalysis.StandardType.GGPZTrivD4
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.Fischer.Classification.Symmetric.LocalData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGPZEndpointJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (labJ labX : LargeEvenLabel)
    (X : Subgroup G) (m : ℕ) (z : ↥Bs), GGPZPrem p B Bs x L D J y K labJ labX X m z →
      GGPZEndpointAt (Bs := Bs) J labJ m

theorem ggPZ_prem_facts {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {labJ labX : LargeEvenLabel} {X : Subgroup G} {m : ℕ} {z : ↥Bs}
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J))
    (h : GGPZPrem p B Bs x L D J y K labJ labX X m z) :
    IsElemAbelian p Bs ∧ D ≤ Bs ∧ D ≤ Subgroup.centralizer (J : Set G) ∧
      (Bs ⊓ J) ⊓ D = ⊥ ∧ (∀ b ∈ Bs, ∃ a ∈ Bs ⊓ J, ∃ d ∈ D, b = a * d) ∧
      m = labJ.rank + 2 ∧ 2 ≤ labJ.rank ∧ p ∣ Nat.card ↥J ∧
      Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank := by
  have hrank2 : 2 ≤ labJ.rank := ggPZ_rank_two h
  obtain ⟨hH, -, -, -, -, -, hrow, hm, hBscard, hJcard, -, -, -, -⟩ := h
  have hB : GGBstar p B Bs := hH.1.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hmr : m = labJ.rank + 2 := by
    obtain ⟨hrowTN, -⟩ := hrow
    rcases hm with ⟨htag, hm⟩ | ⟨htag, hm⟩
    · rcases hrowTN with ⟨-, -, -, hXe⟩ | ⟨-, -, -, hXe⟩ | ⟨-, -, -, hXe⟩ | ⟨-, -, -, hXe⟩
      · rw [hXe] at hm
        simp only at hm
        omega
      · rw [hXe] at hm
        simp only at hm
        omega
      · rw [hXe] at htag
        rcases htag with h | h <;> simp at h
      · rw [hXe] at htag
        rcases htag with h | h <;> simp at h
    · rcases hrowTN with ⟨-, -, -, hXe⟩ | ⟨-, -, -, hXe⟩ | ⟨hJe, -, -, -⟩ | ⟨hJe, -, -, -⟩
      · rw [hXe] at htag
        rcases htag with h | h <;> simp at h
      · rw [hXe] at htag
        rcases htag with h | h <;> simp at h
      · have : labJ.rank = 4 := congrArg LargeEvenLabel.rank hJe
        omega
      · have : labJ.rank = 4 := congrArg LargeEvenLabel.rank hJe
        omega
  have hpJ : p ∣ Nat.card ↥J := by
    have h1 : p ∣ Nat.card ↥(Bs ⊓ J) := by
      rw [hJcard]
      exact dvd_pow_self p (by omega)
    exact h1.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hDcent : D ≤ Subgroup.centralizer (J : Set G) := by
    rw [hDJ.1.2.2.2.2.2.2]
    exact inf_le_right
  have hDBs : D ≤ Bs := (hDJ.1.1).trans hB.1
  have hint : (Bs ⊓ J) ⊓ D = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun d hd => ?_
    by_contra hd1
    have hdJ : d ∈ J := hd.1.2
    have hdp : d ^ p = 1 := hDJ.1.2.1.2 d hd.2
    have hdc : (⟨d, hdJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (by simpa using (Subgroup.mem_centralizer_iff.mp (hDcent hd.2) g g.2))
    have hord : orderOf d = p := orderOf_eq_prime hdp hd1
    have hdvd : orderOf (⟨⟨d, hdJ⟩, hdc⟩ : ↥(Subgroup.center ↥J)) ∣
        Nat.card ↥(Subgroup.center ↥J) :=
      orderOf_dvd_natCard _
    have hordc : orderOf (⟨⟨d, hdJ⟩, hdc⟩ : ↥(Subgroup.center ↥J)) = p := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord]
    exact hZ (hordc ▸ hdvd)
  have hprod : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ J, ∃ d ∈ D, b = a * d := by
    let F : ↥(Bs ⊓ J) × ↥D → ↥Bs := fun ad =>
      ⟨(ad.1 : G) * (ad.2 : G), Bs.mul_mem ad.1.2.1 (hDBs ad.2.2)⟩
    have hFinj : Function.Injective F := by
      rintro ⟨a, d⟩ ⟨a', d'⟩ hF
      have h1 : (a : G) * d = a' * d' := congrArg Subtype.val hF
      have h2 : (a' : G)⁻¹ * a = d' * (d : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * d) * (d : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * d') * (d : G)⁻¹ := by rw [h1]
          _ = d' * (d : G)⁻¹ := by group
      have h3 : (a' : G)⁻¹ * a ∈ (Bs ⊓ J) ⊓ D :=
        ⟨(Bs ⊓ J).mul_mem ((Bs ⊓ J).inv_mem a'.2) a.2, h2 ▸ D.mul_mem d'.2 (D.inv_mem d.2)⟩
      rw [hint, Subgroup.mem_bot] at h3
      have h4 : (a : G) = a' := (inv_mul_eq_one.mp h3).symm
      have h5 : (d : G) = d' := by
        rw [h3] at h2
        have h6 : (d' : G) * (d : G)⁻¹ = 1 := h2.symm
        exact (mul_inv_eq_one.mp h6).symm
      exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
    have hcard : Nat.card ↥Bs ≤ Nat.card (↥(Bs ⊓ J) × ↥D) := by
      rw [Nat.card_prod, hJcard, hDJ.1.2.2.1, hBscard, ← pow_add]
      exact le_of_eq (by rw [hmr])
    have hFsurj : Function.Surjective F := (hFinj.bijective_of_nat_card_le hcard).2
    intro b hb
    obtain ⟨⟨a, d⟩, hF⟩ := hFsurj ⟨b, hb⟩
    exact ⟨a, a.2, d, d.2, (congrArg Subtype.val hF).symm⟩
  exact ⟨hB.2.1, hDBs, hDcent, hint, hprod, hmr, hrank2, hpJ, hJcard⟩

theorem ggPZEndpointTriv_of_J (hM : GGPZMultInput) (hJ : GGPZEndpointJ) :
    GGPZEndpointTriv := by
  intro G _ _ p _ B Bs x L D J y K labJ labX X m z h Y hY hJY hBsY htriv
  have hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J) := hM G p B Bs x L D J y K labJ labX X m z h
  have hJ' := hJ G p B Bs x L D J y K labJ labX X m z h
  obtain ⟨hE, hDBs, hDcent, -, hprod, -, -, hpJ, -⟩ := ggPZ_prem_facts hZ h
  obtain ⟨hH, -, -, -, -, -, -, -, -, -, -, hzD, hzx, -⟩ := h
  have hI : GGThmIHyp p B x L := hH.1.1
  have hB : GGBstar p B Bs := hH.1.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxD : x ∈ D := hDJ.1.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hxp : x ^ p = 1 := hDJ.1.2.1.2 x hxD
  have hxY : x ∈ Subgroup.normalizer (Y : Set G) := hBsY (hB.1 (hDJ.1.1 hxD))
  have hDeq : D = Subgroup.closure {x, (z : G)} := eq_closure_pair_of_mem hI hDJ hzD hzx
  have hJcomp : IsComponentOf J (Subgroup.centralizer ({(z : G)} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hDeq
  have hYz : Y ≤ Subgroup.centralizer ({(z : G)} : Set G) := hY.1
  have hJq : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).1 hJcomp.2.2
  have hJsub : IsSubnormal J (Y ⊓ Subgroup.centralizer ({x} : Set G)) := by
    have hJle : J ≤ Y ⊓ Subgroup.centralizer ({x} : Set G) :=
      le_inf hJY fun j hj => (hJcomp.1 hj).2
    have h1 := LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hJcomp.2.1
      (Y ⊓ Subgroup.centralizer ({x} : Set G))
    rwa [inf_eq_left.mpr hJle, inf_eq_right.mpr (inf_le_inf_right _ hYz)] at h1
  have hED : Bs = (Bs ⊓ J) ⊔ D := by
    refine le_antisymm (fun b hb => ?_) (sup_le inf_le_left hDBs)
    obtain ⟨a, ha, d, hd, rfl⟩ := hprod b hb
    exact Subgroup.mul_mem_sup ha hd
  have hYJ := ggPZ_eq_mul_core hY hxp hx1 hxY htriv hJsub hJq hpJ
  have hAut : ggAutomizer Y Bs ≤ ggAutomizer J Bs :=
    ggPZ_automizer_le_of_eq_mul hE hBsY hJY hJq hpJ hZ hYJ hDBs hDcent hED
  obtain ⟨r, n, c, W, instG, instF, f, hWg, hr, hrm, hn, hc, hle⟩ := hJ'
  exact ⟨r, n, c, W, instG, instF, f, hWg, hr, hrm, hn, hc, hAut.trans hle⟩

theorem ggPZ_automizer_extend {G : Type} [Group G] [Finite G] {Bs J D : Subgroup G}
    (hBs : IsMulCommutative Bs) (hDBs : D ≤ Bs) (hDJ : D ≤ Subgroup.centralizer (J : Set G))
    (hint : (Bs ⊓ J) ⊓ D = ⊥) (hprod : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ J, ∃ d ∈ D, b = a * d)
    {W : Type} [Group W] (f : W →* MulAut ↥(Bs ⊓ J))
    (hf : ggAutomizer J (Bs ⊓ J) ≤ f.range) :
    ∃ f' : W →* MulAut ↥Bs, ggAutomizer J Bs ≤ f'.range := by
  have hcomm : ∀ a b : G, a ∈ Bs → b ∈ Bs → a * b = b * a := fun a b ha hb =>
    congrArg Subtype.val (hBs.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let Φ : ↥(Bs ⊓ J) × ↥D →* ↥Bs :=
    { toFun := fun ad => ⟨(ad.1 : G) * (ad.2 : G), Bs.mul_mem ad.1.2.1 (hDBs ad.2.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun ad ad' => Subtype.ext (by
        have h := hcomm (ad.2 : G) (ad'.1 : G) (hDBs ad.2.2) ad'.1.2.1
        show (ad.1 : G) * ad'.1 * ((ad.2 : G) * ad'.2) = (ad.1 * ad.2) * (ad'.1 * ad'.2)
        calc (ad.1 : G) * ad'.1 * ((ad.2 : G) * ad'.2)
            = ad.1 * ((ad.2 : G) * ad'.1) * ad'.2 := by rw [h]; group
          _ = (ad.1 * ad.2) * (ad'.1 * ad'.2) := by group) }
  have hΦinj : Function.Injective Φ := by
    rintro ⟨a, d⟩ ⟨a', d'⟩ hF
    have h1 : (a : G) * d = a' * d' := congrArg Subtype.val hF
    have h2 : (a' : G)⁻¹ * a = d' * (d : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * d) * (d : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * d') * (d : G)⁻¹ := by rw [h1]
        _ = d' * (d : G)⁻¹ := by group
    have h3 : (a' : G)⁻¹ * a ∈ (Bs ⊓ J) ⊓ D :=
      ⟨(Bs ⊓ J).mul_mem ((Bs ⊓ J).inv_mem a'.2) a.2, h2 ▸ D.mul_mem d'.2 (D.inv_mem d.2)⟩
    rw [hint, Subgroup.mem_bot] at h3
    have h4 : (a : G) = a' := (inv_mul_eq_one.mp h3).symm
    have h5 : (d : G) = d' := by
      rw [h3] at h2
      have h6 : (d' : G) * (d : G)⁻¹ = 1 := h2.symm
      exact (mul_inv_eq_one.mp h6).symm
    exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
  have hΦsurj : Function.Surjective Φ := by
    intro b
    obtain ⟨a, ha, d, hd, hb⟩ := hprod b b.2
    exact ⟨(⟨a, ha⟩, ⟨d, hd⟩), Subtype.ext hb.symm⟩
  let ι : ↥(Bs ⊓ J) × ↥D ≃* ↥Bs := MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have hι : ∀ (a : ↥(Bs ⊓ J)) (d : ↥D), ((ι (a, d) : ↥Bs) : G) = (a : G) * d := fun _ _ => rfl
  let ext : MulAut ↥(Bs ⊓ J) → MulAut ↥Bs := fun φ =>
    ι.symm.trans ((MulEquiv.prodCongr φ (MulEquiv.refl ↥D)).trans ι)
  have ext_mul : ∀ φ ψ, ext (φ * ψ) = ext φ * ext ψ := by
    intro φ ψ
    refine MulEquiv.ext fun b => ?_
    obtain ⟨⟨a, d⟩, rfl⟩ := ι.surjective b
    simp only [ext, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  refine ⟨(MonoidHom.mk' ext ext_mul).comp f, fun ψ hψ => ?_⟩
  obtain ⟨g, hgJ, hgN, hg⟩ := mem_ggAutomizer_iff.mp hψ
  have hgNE : g ∈ Subgroup.normalizer ((Bs ⊓ J : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨hhB, hhJ⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hgN h).mp hhB,
        J.mul_mem (J.mul_mem hgJ hhJ) (J.inv_mem hgJ)⟩
    · rintro ⟨hhB, hhJ⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hgN h).mpr hhB, ?_⟩
      have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
      rw [this]
      exact J.mul_mem (J.mul_mem (J.inv_mem hgJ) hhJ) hgJ
  obtain ⟨w, hw⟩ := hf (ggConjAut_mem_ggAutomizer hgJ hgNE)
  refine ⟨w, ?_⟩
  refine MulEquiv.ext fun b => Subtype.ext ?_
  obtain ⟨a, ha, d, hd, hb⟩ := hprod b b.2
  have hbι : ι (⟨a, ha⟩, ⟨d, hd⟩) = b := Subtype.ext hb.symm
  have hgd : g * d = d * g := Subgroup.mem_centralizer_iff.mp (hDJ hd) g hgJ
  subst hbι
  show ((ext (f w) (ι (⟨a, ha⟩, ⟨d, hd⟩)) : ↥Bs) : G) =
    ((ψ (ι (⟨a, ha⟩, ⟨d, hd⟩)) : ↥Bs) : G)
  rw [hg, hw]
  simp only [ext, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [show (MulEquiv.prodCongr (ggConjAut (Bs ⊓ J) hgNE) (MulEquiv.refl ↥D))
      (⟨a, ha⟩, ⟨d, hd⟩) = (ggConjAut (Bs ⊓ J) hgNE ⟨a, ha⟩, ⟨d, hd⟩) from rfl, hι, hι,
    ggConjAut_apply]
  simp only
  calc g * a * g⁻¹ * d = g * a * (g⁻¹ * d) := by group
    _ = g * (a * d) * g⁻¹ := by
      have h1 : g⁻¹ * d = d * g⁻¹ := by
        calc g⁻¹ * d = g⁻¹ * (d * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * d) * g⁻¹ := by rw [hgd]
          _ = d * g⁻¹ := by group
      rw [h1]
      group

theorem ggPZEndpointAt_of_perm {G : Type} [Group G] [Finite G] {J Bs : Subgroup G} {l m : ℕ}
    {labJ : LargeEvenLabel} (hl : 2 ≤ l) (hrk : labJ.rank ≤ l) (hlm : l ≤ m)
    (f : Equiv.Perm (Fin (l + 1)) →* MulAut ↥Bs) (hf : ggAutomizer J Bs ≤ f.range) :
    GGPZEndpointAt (Bs := Bs) J labJ m := by
  refine ⟨l, (l + 1).factorial, 1, Equiv.Perm (Fin (l + 1)), inferInstance, inferInstance, f,
    Or.inl ⟨by omega, rfl, by rw [if_neg (by omega)]⟩, hrk, hlm, ?_, ?_, hf⟩
  · rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  · rw [CFSG.Fischer.Classification.SymPair.center_perm_eq_bot (by simp; omega), Subgroup.card_bot]

theorem ggPZEndpointAt_of_b4 {G : Type} [Group G] [Finite G] {J Bs : Subgroup G} {m : ℕ}
    {labJ : LargeEvenLabel} (hrk : labJ.rank ≤ 4) (hm : 4 ≤ m) {W : Type} [Group W] [Finite W]
    (hW : Nat.card W = 384) (hc : Nat.card ↥(Subgroup.center W) = 2)
    (f : W →* MulAut ↥Bs) (hf : ggAutomizer J Bs ≤ f.range) :
    GGPZEndpointAt (Bs := Bs) J labJ m :=
  ⟨4, 384, 2, W, inferInstance, inferInstance, f,
    Or.inr (Or.inl ⟨by norm_num, by norm_num [Nat.factorial], rfl⟩), hrk, hm, hW, hc, hf⟩

theorem ggPZEndpointJ (hM : GGPZMultInput) : GGPZEndpointJ := by
  intro G _ _ p _ B Bs x L D J y K labJ labX X m z h
  have hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J) := hM G p B Bs x L D J y K labJ labX X m z h
  obtain ⟨hE, hDBs, hDcent, hint, hprod, hmr, hrank2, -, hJcard⟩ := ggPZ_prem_facts hZ h
  obtain ⟨hH, -, hΛJ, -, hJlab, -, hrow, -⟩ := h
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hJq : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).1
      hDJ.1.2.2.2.2.2.1.2.2
  have hEJabel : IsElemAbelian p (Bs ⊓ J) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => hE.2 g hg.1⟩
    have h1 := hE.1.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩
    exact Subtype.ext (congrArg (fun t : ↥Bs => (t : G)) h1)
  have hn1 : 1 ≤ labJ.n := hΛJ.1
  obtain ⟨hrowTN, -⟩ := hrow
  rcases hrowTN with ⟨hJt, hpq, hpl, -⟩ | ⟨hJt, hpq, hpl, -⟩ | ⟨hJe, hp3, hpq, -⟩ |
      ⟨hJe, hp3, hpq, -⟩
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hpq
      obtain ⟨j, hj⟩ : 2 ∣ 2 ^ labJ.n := dvd_pow_self 2 (by omega)
      have : 0 < 2 ^ labJ.n := by positivity
      omega
    have hJlab' : GGHasLabel ⟨.A, labJ.rank, labJ.n⟩ (↥J ⧸ Subgroup.center ↥J) := by
      cases labJ
      simp only at hJt hJlab ⊢
      subst hJt
      exact hJlab
    obtain ⟨f, hf⟩ := ggPZ_automizer_typeA hp2 hrank2 hpq hpl hJlab' hJq hZ inf_le_right hEJabel
      hJcard
    obtain ⟨f', hf'⟩ := ggPZ_automizer_extend hE.1 hDBs hDcent hint hprod f hf
    exact ggPZEndpointAt_of_perm hrank2 le_rfl (by omega) f' hf'
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hpq
      obtain ⟨j, hj⟩ : 2 ∣ 2 ^ labJ.n := dvd_pow_self 2 (by omega)
      have : 0 < 2 ^ labJ.n := by positivity
      omega
    have hJlab' : GGHasLabel ⟨.twA, labJ.rank, labJ.n⟩ (↥J ⧸ Subgroup.center ↥J) := by
      cases labJ
      simp only at hJt hJlab ⊢
      subst hJt
      exact hJlab
    obtain ⟨f, hf⟩ := ggPZ_automizer_twA hp2 hrank2 hpq hpl hJlab' hJq hZ inf_le_right hEJabel
      hJcard
    obtain ⟨f', hf'⟩ := ggPZ_automizer_extend hE.1 hDBs hDcent hint hprod f hf
    exact ggPZEndpointAt_of_perm hrank2 le_rfl (by omega) f' hf'
  ·
    subst hp3
    have hrk4 : labJ.rank = 4 := congrArg LargeEvenLabel.rank hJe
    have hJlab' : GGHasLabel ⟨.D, 4, labJ.n⟩ (↥J ⧸ Subgroup.center ↥J) := hJe ▸ hJlab
    obtain ⟨W, instG, instF, f, hW, hc, hf⟩ := ggPZ_automizer_D4 (Or.inl hpq) hJlab' hJq hZ
      inf_le_right hEJabel (hrk4 ▸ hJcard)
    obtain ⟨f', hf'⟩ := ggPZ_automizer_extend hE.1 hDBs hDcent hint hprod f hf
    exact ggPZEndpointAt_of_b4 (by omega) (by omega) hW hc f' hf'
  ·
    subst hp3
    have hrk4 : labJ.rank = 4 := congrArg LargeEvenLabel.rank hJe
    have hJlab' : GGHasLabel ⟨.D, 4, labJ.n⟩ (↥J ⧸ Subgroup.center ↥J) := hJe ▸ hJlab
    obtain ⟨W, instG, instF, f, hW, hc, hf⟩ := ggPZ_automizer_D4 (Or.inr hpq) hJlab' hJq hZ
      inf_le_right hEJabel (hrk4 ▸ hJcard)
    obtain ⟨f', hf'⟩ := ggPZ_automizer_extend hE.1 hDBs hDcent hint hprod f hf
    exact ggPZEndpointAt_of_b4 (by omega) (by omega) hW hc f' hf'

theorem ggPZEndpointTriv_holds :
    GGPZEndpointTriv :=
  ggPZEndpointTriv_of_J ggPZMultInput_holds (ggPZEndpointJ ggPZMultInput_holds)

theorem ggPZEndpointInput_of_nbr
    (hPU : GGPumpupInput)
    (hN : GGPZEndpointNbr) : GGPZEndpointInput :=
  ggPZEndpointInput_of_triv_nbr hPU ggPZEndpointTriv_holds hN

end CFSG.StandardType

end
