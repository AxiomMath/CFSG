module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLBridge
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFAbs2
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFIn2
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6Components
public import CFSG.Foundations.MaxOrderThompsonImage
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Foundations.MaxOrderThompson

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


private theorem ggAutomizer_map_of_ker_le_center {G G' : Type} [Group G] [Finite G]
    [Group G'] {p : ℕ} [Fact p.Prime] {f : G →* G'} (hker : f.ker ≤ Subgroup.center G)
    (hpker : ¬ p ∣ Nat.card f.ker) {Bs : Subgroup G} (hBs : IsPGroup p Bs) (H : Subgroup G)
    {Bs' : Subgroup G'} (hmap : Bs.map f = Bs') (e : ↥Bs ≃* ↥Bs')
    (he : ∀ b : ↥Bs, (e b : G') = f b) :
    ggAutomizer (H.map f) Bs' = (ggAutomizer H Bs).map (MulAut.congr e).toMonoidHom := by
  subst Bs'
  classical
  have hconj : ∀ g : G, f g ∈ Subgroup.normalizer (Bs.map f : Set G') →
      ∀ b ∈ Bs, (MulAut.conj g) b ∈ Bs := by
    intro g hg b hb
    let x : G := g * b * g⁻¹
    have hfg : f x ∈ Bs.map f := by
      have hmem := (Subgroup.mem_normalizer_iff.mp hg) (f b)
      have hb' : f b ∈ Bs.map f := Subgroup.mem_map_of_mem f hb
      have := hmem.mp hb'
      simpa [x, map_mul, map_inv] using this
    obtain ⟨b', hb'Bs, hb'eq⟩ := Subgroup.mem_map.mp hfg
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hBs ⟨b, hb⟩
    obtain ⟨n', hn'⟩ := IsPGroup.iff_orderOf.mp hBs ⟨b', hb'Bs⟩
    have hxord : orderOf x = p ^ n := by
      have h := MulEquiv.orderOf_eq (MulAut.conj g) b
      have hbord : orderOf b = p ^ n := (Subgroup.orderOf_coe ⟨b, hb⟩).trans hn
      simpa [x, MulAut.conj_apply] using h.trans hbord
    have hb'ord : orderOf b' = p ^ n' :=
      (Subgroup.orderOf_coe ⟨b', hb'Bs⟩).trans hn'
    have hk_ker : x * b'⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [show f x = f b' from hb'eq.symm, mul_inv_cancel]
    have hk_center : x * b'⁻¹ ∈ Subgroup.center G := hker hk_ker
    have hxc : x * b' = b' * x := by
      have h := Subgroup.mem_center_iff.mp hk_center b'
      calc x * b' = ((x * b'⁻¹) * b') * b' := by group
        _ = (b' * (x * b'⁻¹)) * b' := by rw [h]
        _ = b' * x := by group
    let N : ℕ := max n n'
    have hxpow : x ^ (p ^ N) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hxord]
      exact Nat.pow_dvd_pow p (Nat.le_max_left n n')
    have hb'pow : b' ^ (p ^ N) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hb'ord]
      exact Nat.pow_dvd_pow p (Nat.le_max_right n n')
    have hkpow : (x * b'⁻¹) ^ (p ^ N) = 1 := by
      rw [(show Commute x b' from hxc).inv_right.mul_pow (p ^ N), hxpow,
        inv_pow, hb'pow, inv_one, mul_one]
    have hord_dvd_p : orderOf (x * b'⁻¹) ∣ p ^ N :=
      orderOf_dvd_of_pow_eq_one hkpow
    have hord_dvd_ker : orderOf (x * b'⁻¹) ∣ Nat.card f.ker :=
      Subgroup.orderOf_dvd_natCard f.ker hk_ker
    have hcop : Nat.Coprime (p ^ N) (Nat.card f.ker) :=
      (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hpker |>.pow_left N
    have hord_one : orderOf (x * b'⁻¹) = 1 := by
      have hgcd : Nat.gcd (p ^ N) (Nat.card f.ker) = 1 :=
        Nat.coprime_iff_gcd_eq_one.mp hcop
      exact Nat.dvd_one.mp (hgcd ▸ Nat.dvd_gcd hord_dvd_p hord_dvd_ker)
    have hkone : x * b'⁻¹ = 1 := orderOf_eq_one_iff.mp hord_one
    have hxb : x = b' := by
      calc x = (x * b'⁻¹) * b' := by group
        _ = b' := by rw [hkone, one_mul]
    have hxBs : x ∈ Bs := by
      rw [hxb]
      exact hb'Bs
    simpa [x, MulAut.conj_apply] using hxBs
  have hf_norm : ∀ g : G, f g ∈ Subgroup.normalizer (Bs.map f : Set G') →
      g ∈ Subgroup.normalizer (Bs : Set G) := by
    intro g hg
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hle : Bs.map (MulAut.conj g).toMonoidHom ≤ Bs := by
      rintro _ ⟨b, hb, rfl⟩
      exact hconj g hg b hb
    have hcard : Nat.card (Bs.map (MulAut.conj g).toMonoidHom) = Nat.card Bs :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  refine le_antisymm ?_ ?_
  · intro φ' hφ'
    obtain ⟨g', hg'H, hg'N, hφ'g'⟩ := mem_ggAutomizer_iff.mp hφ'
    obtain ⟨g, hgH, hfg⟩ := Subgroup.mem_map.mp hg'H
    have hgN : g ∈ Subgroup.normalizer (Bs : Set G) := by
      apply hf_norm g
      simpa [hfg] using hg'N
    refine Subgroup.mem_map.mpr ⟨ggConjAut Bs hgN,
      ggConjAut_mem_ggAutomizer hgH hgN, ?_⟩
    ext b'
    obtain ⟨b, rfl⟩ := e.surjective b'
    calc ((MulAut.congr e (ggConjAut Bs hgN)) (e b) : G')
        = f (ggConjAut Bs hgN b) := by
          rw [MulAut.congr_apply]
          simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
          exact he _
      _ = f (g * b * g⁻¹) := by rw [ggConjAut_apply]
      _ = f g * f b * (f g)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = g' * (e b) * g'⁻¹ := by rw [hfg, he b]
      _ = (φ' (e b) : G') := (hφ'g' (e b)).symm
  · intro φ' hφ'
    obtain ⟨φ, hφA, rfl⟩ := Subgroup.mem_map.mp hφ'
    obtain ⟨g, hgH, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφA
    refine mem_ggAutomizer_iff.mpr ⟨f g, Subgroup.mem_map_of_mem f hgH, ?_, ?_⟩
    · exact Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f hgN)
    · intro b'
      obtain ⟨b, rfl⟩ := e.surjective b'
      calc ((MulAut.congr e φ) (e b) : G')
          = f (φ b) := by
            rw [MulAut.congr_apply]
            simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
            exact he _
        _ = f (g * b * g⁻¹) := by rw [hφg]
        _ = f g * f b * (f g)⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = f g * (e b) * (f g)⁻¹ := by rw [he b]

theorem ggQTwoXInL_frame_lift (hLB : GGLBalanceInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hxL : x ∈ L) {R : Type} [Group R]
    (θ : ↥(ggG0 3 B x L D J) ⧸ Subgroup.center ↥(ggG0 3 B x L D J) ≃* R)
    (hBG : Bs ≤ ggG0 3 B x L D J)
    (hC : GGQTwoFRConcl ((Bs.subgroupOf (ggG0 3 B x L D J)).map (ggMarkHom θ))
      (ggMarkHom θ ⟨x, le_ggG0_left 3 B x L D J hxL⟩)
      ((L.subgroupOf (ggG0 3 B x L D J)).map (ggMarkHom θ))
      ((D.subgroupOf (ggG0 3 B x L D J)).map (ggMarkHom θ))
      ((J.subgroupOf (ggG0 3 B x L D J)).map (ggMarkHom θ))) :
    ∃ (n : ℕ) (_ : 6 ≤ n) (y : G) (K : Subgroup G) (hx : x ∈ Bs) (hy : y ∈ Bs)
      (ι : Additive ↥Bs ≃+ (Fin n → ZMod 3)), GGNbr 3 B x D J y K ∧
      (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
        Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
          T v i = v (σ i)} ∧
      (ggAutomizer K Bs).map (ggLin (p := 3) ι) =
        Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
          T v i = ((if i.val = 0 then (-1 : ZMod 3) else 1) *
            (if (σ i).val = 0 then (-1 : ZMod 3) else 1)) * v (σ i)} ∧
      ι (Additive.ofMul ⟨x, hx⟩) = (fun _ => 1) ∧
      ι (Additive.ofMul ⟨y, hy⟩) = (fun i => if i.val = 0 then (-1 : ZMod 3) else 1) := by
  let G0 : Subgroup G := ggG0 3 B x L D J
  let π : ↥G0 →* R := ggMarkHom θ
  let Bs0 : Subgroup ↥G0 := Bs.subgroupOf G0
  let E : Subgroup R := Bs0.map π
  let L0 : Subgroup ↥G0 := L.subgroupOf G0
  let Lbar : Subgroup R := L0.map π
  let D0 : Subgroup ↥G0 := D.subgroupOf G0
  let Dbar : Subgroup R := D0.map π
  let J0 : Subgroup ↥G0 := J.subgroupOf G0
  let Jbar : Subgroup R := J0.map π
  let x0 : ↥G0 := ⟨x, le_ggG0_left 3 B x L D J hxL⟩
  let xbar : R := π x0
  have hC' : GGQTwoFRConcl E xbar Lbar Dbar Jbar := by
    simpa only [G0, π, Bs0, E, L0, Lbar, D0, Dbar, J0, Jbar, x0, xbar] using hC
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  obtain ⟨hp, hBsElem, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hLG0 : L ≤ G0 := le_ggG0_left 3 B x L D J
  have hDleBs : D ≤ Bs := hDJ.1.1.trans hcfg.2.1.1
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hDJ.1.2.2.2.2.2.1
  have hJleG0 : J ≤ G0 := hJcomp.1.trans (inf_le_left.trans hLG0)
  have hkerπ : π.ker = Subgroup.center ↥G0 := by
    rw [show π = ggQuotHom (L := G0) θ from rfl, ker_ggQuotHom]
  have hπsurj : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥G0))
  have hpker3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hkerπ]
    simpa [G0] using not_three_dvd_card_center_ggG0 hS
  have hcop3 : Nat.Coprime 3 (Nat.card π.ker) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hpker3
  have hker_le_center : π.ker ≤ Subgroup.center ↥G0 := hkerπ.le
  have hBsP : IsPGroup 3 Bs := CFSG.Open.IsElemAbelian.isPGroup hBsElem
  have hBs0P : IsPGroup 3 Bs0 :=
    hBsP.of_equiv (Subgroup.subgroupOfEquivOfLe hBG).symm
  have hπinj : Function.Injective (π.comp Bs0.subtype) :=
    @CFSG.injective_comp_subtype_of_coprime_card_ker ↥G0 _ R _ _ 3 (Fact.mk hp)
      π hcop3 Bs0 hBs0P
  obtain ⟨n, hn, ybar, Kbar, hxbarE, hybarE, ιbar, hybarD, hybarnot, h3Jbar,
    hKbarComp, hJbarle, hxbarNotCent, hLauto, hKauto, hιbarx, hιbary⟩ := hC'
  obtain ⟨b0, hb0Bs0, hb0eq⟩ := Subgroup.mem_map.mp hybarE
  let y : G := (b0 : G)
  have hy : y ∈ Bs := Subgroup.mem_subgroupOf.mp hb0Bs0
  have hyG0 : y ∈ G0 := b0.2
  let z : ↥G0 := b0
  obtain ⟨d0, hd0D0, hd0eq⟩ := Subgroup.mem_map.mp hybarD
  have hd0Bs : (d0 : G) ∈ Bs := hDleBs (Subgroup.mem_subgroupOf.mp hd0D0)
  have hd0Bs0 : d0 ∈ Bs0 := Subgroup.mem_subgroupOf.mpr hd0Bs
  have hb0d0 : b0 = d0 := by
    have h := hπinj (a₁ := (⟨b0, hb0Bs0⟩ : ↥Bs0)) (a₂ := ⟨d0, hd0Bs0⟩) (by
      change π b0 = π d0
      rw [hb0eq, hd0eq])
    exact congrArg Subtype.val h
  have hyD : y ∈ D := by
    have hyval : y = (d0 : G) := congrArg Subtype.val hb0d0
    rw [hyval]
    exact Subgroup.mem_subgroupOf.mp hd0D0
  have hyNot : y ∉ Subgroup.zpowers x := by
    intro hmem
    apply hybarnot
    rw [Subgroup.mem_zpowers_iff] at hmem ⊢
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, ?_⟩
    have h1 : xbar ^ k = π (x0 ^ k) := by rw [map_zpow]
    have h2 : π (x0 ^ k) = π b0 := by
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_zpow, hk]
    exact h1.trans (h2.trans hb0eq)
  have hcardJ0 : Nat.card J0 = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJleG0).toEquiv
  have hpJ : 3 ∣ Nat.card J := by
    rw [← hcardJ0]
    exact h3Jbar.trans (Subgroup.card_map_dvd (H := J0) (f := π))
  have hz3 : z ^ 3 = 1 := by
    apply Subtype.ext
    simpa [z, y] using hBsElem.2 y hy
  obtain ⟨X', hX'comp, hX'map, hX'univ⟩ :=
    exists_isComponentOf_centralizer_lift (π := π) hπsurj hker_le_center (n := 3)
      hcop3 (z := z) hz3 (X₀ := Kbar) (by simpa [z, hb0eq] using hKbarComp)
  have hJ0comp : IsComponentOf J0 ((L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G0) :=
    ggIsComponentOf_subgroupOf_of_le G0 hJleG0 hJcomp
  have hJ0perf : ⁅J0, J0⁆ = J0 := by
    have hperf : Group.IsPerfect ↥J0 := ⟨hJ0comp.2.2.1⟩
    exact Subgroup.isPerfect_iff.mp hperf
  have hJ0le : J0 ≤ X' :=
    hX'univ J0 hJ0perf (by simpa [Jbar] using hJbarle)
  let X : Subgroup G := X'.map G0.subtype
  have hcentMap : (Subgroup.centralizer ({z} : Set ↥G0)).map G0.subtype =
      G0 ⊓ Subgroup.centralizer ({y} : Set G) := by
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨a.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp ha)
    · intro hg
      obtain ⟨hgG0, hgC⟩ := Subgroup.mem_inf.mp hg
      refine ⟨⟨g, hgG0⟩, ?_, rfl⟩
      change (⟨g, hgG0⟩ : ↥G0) ∈ Subgroup.centralizer ({z} : Set ↥G0)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgC)
  have hXsub : IsSubnormal X (G0 ⊓ Subgroup.centralizer ({y} : Set G)) := by
    have h := hX'comp.2.1.map G0.subtype
    rw [hcentMap] at h
    exact h
  have hXq : CFSG.Assembly.IsQuasisimple X := by
    let eX : ↥X ≃* ↥X' :=
      (X'.equivMapOfInjective G0.subtype G0.subtype_injective).symm
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv eX hX'comp.2.2
  have hXcomp : IsComponentOf X (G0 ⊓ Subgroup.centralizer ({y} : Set G)) := by
    refine ⟨?_, hXsub, hXq⟩
    dsimp [X]
    rw [← hcentMap]
    exact Subgroup.map_mono hX'comp.1
  have hJX : J ≤ X := by
    intro j hj
    have hjG0 : j ∈ G0 := hJleG0 hj
    have hj0 : (⟨j, hjG0⟩ : ↥G0) ∈ J0 := Subgroup.mem_subgroupOf.mpr hj
    change j ∈ X'.map G0.subtype
    exact Subgroup.mem_map.mpr ⟨⟨j, hjG0⟩, hJ0le hj0, rfl⟩
  have hxX : x ∉ Subgroup.centralizer (X : Set G) := by
    intro hx
    apply hxbarNotCent
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [← hX'map] at hk
    obtain ⟨k0, hk0X', rfl⟩ := Subgroup.mem_map.mp hk
    have hkX : (k0 : G) ∈ X := Subgroup.mem_map_of_mem G0.subtype hk0X'
    have hcomm : (k0 : G) * x = x * (k0 : G) :=
      (Subgroup.mem_centralizer_iff.mp hx) (k0 : G) hkX
    calc π k0 * xbar = π (k0 * x0) := by rw [map_mul]
      _ = π (x0 * k0) := by rw [show k0 * x0 = x0 * k0 from Subtype.ext hcomm]
      _ = xbar * π k0 := by rw [map_mul]
  have hNbr : GGNbr 3 B x D J y X :=
    ggNbr_of_isComponentOf_ggG0_inf hLB hS.1 hpJ hyD hyNot hXcomp hJX hxX
  have hBsMap : Bs0.map G0.subtype = Bs := Subgroup.map_subgroupOf_eq_of_le hBG
  have hL0map : L0.map G0.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLG0
  let eBt : ↥Bs0 ≃* ↥Bs := Subgroup.subgroupOfEquivOfLe hBG
  let e0 : ↥Bs0 ≃* ↥E :=
    MulEquiv.ofBijective (π.subgroupMap Bs0)
      ⟨fun _ _ h => hπinj (congrArg Subtype.val h), π.subgroupMap_surjective Bs0⟩
  let fBt : ↥Bs ≃* ↥Bs0 := eBt.symm
  let e : ↥Bs ≃* ↥E := fBt.trans e0
  let ι1 : Additive ↥Bs0 ≃+ (Fin n → ZMod 3) := e0.toAdditive.trans ιbar
  let ι : Additive ↥Bs ≃+ (Fin n → ZMod 3) := e.toAdditive.trans ιbar
  have he0 : ∀ b : ↥Bs0, (e0 b : R) = π b := fun _ => rfl
  have hfBt_coe : ∀ b : ↥Bs, (fBt b : G) = (b : G) := by
    intro b
    rfl
  have he : ∀ b : ↥Bs, (e b : R) = π ⟨(b : G), hBG b.2⟩ := by
    intro b
    change π (fBt b) = π ⟨(b : G), hBG b.2⟩
    congr 1
  have hL0auto : ggAutomizer Lbar E =
      (ggAutomizer L0 Bs0).map (MulAut.congr e0).toMonoidHom :=
    ggAutomizer_map_of_ker_le_center (f := π) hker_le_center hpker3 hBs0P L0 rfl e0 he0
  have hX0auto : ggAutomizer Kbar E =
      (ggAutomizer X' Bs0).map (MulAut.congr e0).toMonoidHom := by
    have h := ggAutomizer_map_of_ker_le_center (f := π) hker_le_center hpker3 hBs0P X' rfl e0 he0
    rwa [hX'map] at h
  have hkerSub : (G0.subtype : ↥G0 →* G).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).mpr G0.subtype_injective
  have hkerSubLe : (G0.subtype : ↥G0 →* G).ker ≤ Subgroup.center ↥G0 := by
    rw [hkerSub]
    exact bot_le
  have hpkerSub : ¬ 3 ∣ Nat.card (G0.subtype : ↥G0 →* G).ker := by
    rw [hkerSub, Subgroup.card_bot]
    norm_num
  have hLglobal : ggAutomizer L Bs =
      (ggAutomizer L0 Bs0).map (MulAut.congr eBt).toMonoidHom := by
    have h := ggAutomizer_map_of_ker_le_center (f := G0.subtype) hkerSubLe hpkerSub
      hBs0P L0 hBsMap eBt (fun _ => rfl)
    rwa [hL0map] at h
  have hXglobal : ggAutomizer X Bs =
      (ggAutomizer X' Bs0).map (MulAut.congr eBt).toMonoidHom := by
    have h := ggAutomizer_map_of_ker_le_center (f := G0.subtype) hkerSubLe hpkerSub
      hBs0P X' hBsMap eBt (fun _ => rfl)
    change ggAutomizer (X'.map G0.subtype) Bs = _ at h
    exact h
  have hcompι : eBt.toAdditive.trans ι = ι1 := by
    ext v
    simp [ι, ι1, e, fBt, AddEquiv.trans_apply]
  have hcompL : (ggLin (p := 3) ι).comp (MulAut.congr eBt).toMonoidHom =
      (ggLin (p := 3) ιbar).comp (MulAut.congr e0).toMonoidHom := by
    refine MonoidHom.ext fun φ => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    calc ggLin ι (MulAut.congr eBt φ)
        = ggLin (eBt.toAdditive.trans ι) φ := (ggLin_trans_congr eBt ι φ).symm
      _ = ggLin ι1 φ := by rw [hcompι]
      _ = ggLin ιbar (MulAut.congr e0 φ) := ggLin_trans_congr e0 ιbar φ
  have hLautoG : (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
        T v i = v (σ i)} := by
    rw [hLglobal, Subgroup.map_map]
    rw [hcompL]
    rw [← Subgroup.map_map, ← hL0auto]
    exact hLauto
  have hKautoG : (ggAutomizer X Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
        T v i = ((if i.val = 0 then (-1 : ZMod 3) else 1) *
          (if (σ i).val = 0 then (-1 : ZMod 3) else 1)) * v (σ i)} := by
    rw [hXglobal, Subgroup.map_map]
    rw [hcompL]
    rw [← Subgroup.map_map, ← hX0auto]
    exact hKauto
  refine ⟨n, hn, y, X, hxBs, hy, ι, hNbr, hLautoG, hKautoG, ?_, ?_⟩
  · have hfx0 : (fBt ⟨x, hxBs⟩ : ↥G0) = x0 := by
      apply Subtype.ext
      exact hfBt_coe ⟨x, hxBs⟩
    have hex : e ⟨x, hxBs⟩ = ⟨xbar, hxbarE⟩ := by
      apply Subtype.ext
      change π (fBt ⟨x, hxBs⟩) = xbar
      rw [hfx0]
    change ιbar (Additive.ofMul (e ⟨x, hxBs⟩)) = _
    rw [hex]
    exact hιbarx
  · have hfb0 : (fBt ⟨y, hy⟩ : ↥G0) = b0 := by
      apply Subtype.ext
      exact hfBt_coe ⟨y, hy⟩
    have hey : e ⟨y, hy⟩ = ⟨ybar, hybarE⟩ := by
      apply Subtype.ext
      change π (fBt ⟨y, hy⟩) = ybar
      rw [hfb0, hb0eq]
    change ιbar (Additive.ofMul (e ⟨y, hy⟩)) = _
    rw [hey]
    exact hιbary

end CFSG.StandardType

end
