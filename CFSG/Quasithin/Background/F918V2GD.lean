module

public import CFSG.Quasithin.Background.F918V2GDB
public import CFSG.Quasithin.Background.F918V2D
public import CFSG.Quasithin.Background.F918N3
public import CFSG.Quasithin.Background.F918YE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Z391

open CFSG.Quasithin CFSG.Quasithin.B5.Ln CFSG.Assembly.LowTwoRank Module Matrix
open scoped Pointwise Matrix

theorem v2gd_irr_facts {X : Type} [CommGroup X] {Lb : Subgroup (MulAut X)} {S : Subgroup X}
    (hinv : XMod.IsInv ↥Lb S) (hirr : XMod.IsIrrSec ↥Lb ⊥ S) :
    (∀ l ∈ Lb, ∀ s ∈ S, l s ∈ S) ∧ S ≠ ⊥ ∧
      ∀ J : Subgroup X, (∀ l ∈ Lb, ∀ x ∈ J, l x ∈ J) → J ≤ S → J = ⊥ ∨ J = S :=
  ⟨fun l hl s hs => hinv ⟨l, hl⟩ s hs, hirr.1.ne', fun J hJ hJS =>
    hirr.2 J (fun a x hx => hJ a a.2 x hx) bot_le hJS⟩

variable {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem v2g_natData (hA21 : AsA21SQTKSection) (hNC : AsA36NoOddCover) (hZ35 : Z35Main)
    (hD : D3Std M L T L V) (hlt : V < orbSup T V)
    (hC : ∀ g ∈ L, (∀ v ∈ V, g v = v) → ∀ x ∈ L, g * x = x * g)
    {Q : Type} [CommGroup Q] [MulDistribMulAction ↥M Q] (π : W →* Q)
    (hπs : Function.Surjective π)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (hker : π.ker = fixV L)
    (t : ↥M) (htT : (t : MulAut W) ∈ T) (htV : (t : MulAut W) ∉ stabSub V)
    (hn : ∃ n, SumNatDual (autSec L (orbSup T V) (orbSup T V ⊓ fixV L))
      (⊤ : Subgroup (Sec (orbSup T V) (orbSup T V ⊓ fixV L))) n) :
    EndUnitsTrivial (L.subgroupOf M) (V.map π) ∧ EndUnitsTrivial (L.subgroupOf M) (t • V.map π) ∧
      AutFromGroup (L.subgroupOf M) (V.map π) ∧ FaithfulOn (L.subgroupOf M) (V.map π) ∧
      (∀ c : MulAut W, c ∈ M → c ^ 3 = 1 → (∀ l ∈ L, c * l = l * c) → c = 1) := by
  have _ := hπs
  have _ := htV
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  have hG := n1_sup_le_stabSub_sec hD.hyp
  have hLVT : L ≤ stabSub (orbSup T V) := le_sup_left.trans (hG.trans inf_le_left)
  have hLC : L ≤ stabSub (orbSup T V ⊓ fixV L) := le_sup_left.trans (hG.trans inf_le_right)
  have hTVT : T ≤ stabSub (orbSup T V) := le_stabSub_orbSup T V
  have hTC : T ≤ stabSub (orbSup T V ⊓ fixV L) := le_sup_right.trans (hG.trans inf_le_right)
  have hZ := z35_of_d3Std hD hlt hC
  obtain ⟨-, -, -, h5⟩ := hZ35 _ _ _ _ _ hZ
  have hfaith := d35_faithful hA21 hNC hD hlt hC rfl h5
  let θ : Sec (orbSup T V) (orbSup T V ⊓ fixV L) →* Q :=
    QuotientGroup.lift ((orbSup T V ⊓ fixV L).subgroupOf (orbSup T V))
      (π.comp (orbSup T V).subtype) (fun x hx => by
        have h1 : (x : W) ∈ π.ker := by
          rw [hker]
          exact (Subgroup.mem_inf.1 hx).2
        exact h1)
  have hθ : ∀ v : ↥(orbSup T V), θ (QuotientGroup.mk v) = π (v : W) := fun v => rfl
  have hθinj : Function.Injective θ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [hθ, hθ] at hab
        rw [QuotientGroup.eq]
        refine ⟨(a⁻¹ * b).2, ?_⟩
        rw [← hker]
        show π (((a⁻¹ * b : ↥(orbSup T V))) : W) = 1
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hab, inv_mul_cancel]
  let resL : ↥L →* ↥(autSec L (orbSup T V) (orbSup T V ⊓ fixV L)) :=
    (B5.secHom L hLVT hLC).codRestrict (autSec L (orbSup T V) (orbSup T V ⊓ fixV L)) (fun g => by
      rw [← B5.range_secHom L hLVT hLC]
      exact ⟨g, rfl⟩)
  have hresL_surj : Function.Surjective resL := by
    rintro ⟨φ, hφ⟩
    rw [← B5.range_secHom L hLVT hLC] at hφ
    obtain ⟨g, hg⟩ := hφ
    exact ⟨g, Subtype.ext hg⟩
  have hresL_inj : Function.Injective resL := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : B5.secHom L hLVT hLC g = 1 := congrArg Subtype.val hg
    have h2 := (B5.mem_ker_secHom L hLVT hLC g).1 (MonoidHom.mem_ker.2 h1)
    have h3 : (g : MulAut W) ∈ (L ⊔ T) ⊓ centSec (orbSup T V) (orbSup T V ⊓ fixV L) :=
      ⟨(le_sup_left : L ≤ L ⊔ T) g.2, h2⟩
    have h4 := n1_inf_centSec_le_centSub hD h3
    exact Subtype.ext (hfaith g g.2 fun v hv => h4 v (le_orbSup T V hv))
  let eΛ : ↥(L.subgroupOf M) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLM
  let res : ↥(L.subgroupOf M) →* ↥(autSec L (orbSup T V) (orbSup T V ⊓ fixV L)) :=
    resL.comp eΛ.toMonoidHom
  have hres_bij : Function.Bijective res :=
    ⟨hresL_inj.comp eΛ.injective, hresL_surj.comp eΛ.surjective⟩
  have hθres : ∀ (l : ↥(L.subgroupOf M)) (x : Sec (orbSup T V) (orbSup T V ⊓ fixV L)),
      θ (((res l : ↥(autSec L (orbSup T V) (orbSup T V ⊓ fixV L))) :
        MulAut (Sec (orbSup T V) (orbSup T V ⊓ fixV L))) x) = l • θ x := by
    intro l x
    induction x using QuotientGroup.induction_on with
    | H w =>
      show θ (B5.secHom L hLVT hLC (eΛ l) (QuotientGroup.mk w)) = _
      rw [B5.secHom_mk]
      exact (hπM (l : ↥M) w).symm
  obtain ⟨n, hn45, π₀, U₁, U₂, ⟨hsup, hinf⟩, hR₁, hR₂⟩ := hn
  have hn3 : 3 ≤ n := by rcases hn45 with rfl | rfl <;> norm_num
  have h₁ := B5.Ln.realM_mat_iff.2 hR₁
  have h₂ := B5.Ln.realM_dmat_iff.2 hR₂
  have hπ₀bij : Function.Bijective π₀ := ⟨RealM.injective h₁ (Or.inl rfl), h₁.1⟩
  let eπ : ↥(StatedSL n (ZMod 2)) ≃* ↥(autSec L (orbSup T V) (orbSup T V ⊓ fixV L)) :=
    MulEquiv.ofBijective π₀ hπ₀bij
  let σ : ↥(L.subgroupOf M) →* ↥(StatedSL n (ZMod 2)) := eπ.symm.toMonoidHom.comp res
  have hσ : ∀ l, π₀ (σ l) = res l := fun l => eπ.apply_symm_apply (res l)
  have hσbij : Function.Bijective σ := ⟨eπ.symm.injective.comp hres_bij.1,
    eπ.symm.surjective.comp hres_bij.2⟩
  obtain ⟨hVbinv, hVb0, hVbirr⟩ := v2gd_irr_facts hZ.irr.1 hZ.irr.2
  have hPV : ∀ q, q ∈ V.map π ↔
      ∃ s ∈ sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V, θ s = q := by
    intro q
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨QuotientGroup.mk ⟨v, le_orbSup T V hv⟩, ⟨⟨v, le_orbSup T V hv⟩, hv, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨(u : W), hu, rfl⟩
  let g₀ : stabSub (orbSup T V) := ⟨(t : MulAut W), hTVT htT⟩
  have hg₀C : resHom (orbSup T V) g₀ ∈ stabSub ((orbSup T V ⊓ fixV L).subgroupOf (orbSup T V)) :=
    autSub_le_stabSub_subgroupOf hTC (mem_autSub.mpr ⟨g₀, htT, rfl⟩)
  let tstar : MulAut (Sec (orbSup T V) (orbSup T V ⊓ fixV L)) :=
    quotHom ((orbSup T V ⊓ fixV L).subgroupOf (orbSup T V)) ⟨resHom (orbSup T V) g₀, hg₀C⟩
  have htstar : tstar ∈ autSec T (orbSup T V) (orbSup T V ⊓ fixV L) :=
    B1Red.mem_autSec_iff.mpr ⟨g₀, htT, hg₀C, rfl⟩
  have hθt : ∀ y, θ (tstar y) = t • θ y := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H w => exact (hπM t w).symm
  obtain ⟨-, -, hVb'inv, hVb'irr⟩ := v2d_irrSec hZ rfl htstar
  obtain ⟨hVb'inv', hVb'0, hVb'irr'⟩ := v2gd_irr_facts hVb'inv hVb'irr
  have hPtV : ∀ q, q ∈ t • V.map π ↔
      ∃ s ∈ (sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V).map tstar.toMonoidHom, θ s = q := by
    intro q
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s', hs', rfl⟩
      obtain ⟨y, hy, rfl⟩ := (hPV s').1 hs'
      exact ⟨tstar y, ⟨y, hy, rfl⟩, hθt y⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨θ y, (hPV _).2 ⟨y, hy, rfl⟩, (hθt y).symm⟩
  obtain ⟨M₁, hM₁, hN₁⟩ := v2gd_natRep_of_irr hn3 hsup hinf h₁ h₂ θ hθinj res σ hσ hθres
    hVbinv hVb0 hVbirr hPV
  obtain ⟨M₂, hM₂, hN₂⟩ := v2gd_natRep_of_irr hn3 hsup hinf h₁ h₂ θ hθinj res σ hσ hθres
    hVb'inv' hVb'0 hVb'irr' hPtV
  refine ⟨v2gd_endUnitsTrivial (by omega) hM₁ hσbij.2 hN₁,
    v2gd_endUnitsTrivial (by omega) hM₂ hσbij.2 hN₂, v2gd_autFromGroup hM₁ hσbij.2 hN₁,
    v2gd_faithfulOn hM₁ hσbij.1 hN₁, ?_⟩
  intro c hcM hc3 hcomm
  let σinv : ↥(StatedSL n (ZMod 2)) →* ↥(L.subgroupOf M) :=
    (MulEquiv.ofBijective σ hσbij).symm.toMonoidHom
  let ρ : ↥(StatedSL n (ZMod 2)) →* ↥M := (L.subgroupOf M).subtype.comp σinv
  have hρinj : Function.Injective ρ :=
    Subtype.val_injective.comp (MulEquiv.ofBijective σ hσbij).symm.injective
  have key := eq_one_of_pow_three_centralizes_statedSL hD.hyp.qsqtk hn45 ρ hρinj
    (c := ⟨c, hcM⟩) (Subtype.ext hc3) (fun g => Subtype.ext (hcomm _ (σinv g).2))
  exact congrArg Subtype.val key

end CFSG.Quasithin.Z391
