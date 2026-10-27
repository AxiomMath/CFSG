module

public import CFSG.RankThree.GF2n.Tim79a34BigModel
public import CFSG.RankThree.GF2n.Tim79a34BigLocal
public import CFSG.RankThree.GF2n.Tim79a34CentreSmall
public import CFSG.RankThree.GF2n.Tim79a34IW
public import CFSG.RankThree.GF2n.Tim79a34BigStabQuot
public import CFSG.RankThree.GF2n.Tim79a34BigBar
public import CFSG.RankThree.GF2n.Tim79a34BigNatural

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

theorem bigRI_range_equiv {K N S : Type} [Group K] [Group N] [Group S] (ν : K →* N) (θ : K →* S)
    (hθ : Function.Surjective θ) (hker : θ.ker = ν.ker) : Nonempty (↥ν.range ≃* S) :=
  ⟨(QuotientGroup.quotientKerEquivRange ν).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθ))⟩

abbrev bigRIsub (M V H : Subgroup G) : Subgroup ↥M :=
  (xOf V H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf M

@[expose] def bigRInu (M V H : Subgroup G) : ↥(bigRIsub M V H) →* Mbar M :=
  (QuotientGroup.mk' ((inSubgroup (pCore 2) M).subgroupOf M)).comp (bigRIsub M V H).subtype

theorem bigRInu_range (M V H : Subgroup G) : (bigRInu M V H).range = RbarM M V H := by
  ext x
  simp only [bigRInu, RbarM, MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.coe_comp,
    Function.comp_apply, Subgroup.subtype_apply]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r.1, r.2, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩

@[expose] def bigRIincl (M V H : Subgroup G) : ↥(bigRIsub M V H) →* ↥(xOf V H) :=
  MonoidHom.codRestrict (M.subtype.comp (bigRIsub M V H).subtype) (xOf V H)
    fun r => (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp r.2)).1

theorem bigRIincl_coe (M V H : Subgroup G) (r : ↥(bigRIsub M V H)) :
    ((bigRIincl M V H r : ↥(xOf V H)) : G) = ((r : ↥M) : G) := rfl

theorem bigRIsub_centralizes {M V H : Subgroup G} (r : ↥(bigRIsub M V H)) :
    ((r : ↥M) : G) ∈ Subgroup.centralizer (V : Set G) :=
  (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp r.2)).2

@[expose] noncomputable def bigRIrho {n f : ℕ} (M V H : Subgroup G) (hVH : V ≤ H)
    (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H) :
    ↥(bigRIsub M V H) →* ↥(StatedSp n (GaloisField 2 f)) :=
  Φ.symm.toMonoidHom.comp ((xToXbar hVH).comp (bigRIincl M V H))

theorem bigRIrho_apply {n f : ℕ} (M V H : Subgroup G) (hVH : V ≤ H)
    (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H) (r : ↥(bigRIsub M V H)) :
    Φ (bigRIrho M V H hVH Φ r) = xToXbar hVH (bigRIincl M V H r) :=
  Φ.apply_symm_apply _

theorem bigRI_mem_Vy {V H : Subgroup G} (hVH : V ≤ H) {y : Xbar V H} (hy : y ∈ Vy V H) :
    ∃ v : ↥(xOf V H), (v : G) ∈ V ∧ xToXbar hVH v = y := by
  obtain ⟨x, hxV, hx⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hy)
  refine ⟨⟨(x : G), le_xOf (V_mem_omegaOf V H) hxV⟩, hxV, Subtype.ext ?_⟩
  rw [coe_xToXbar]
  exact hx

theorem bigRIrho_mem_spFix [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) {n f : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H) {a : Fin n ⊕ Fin n → GaloisField 2 f}
    {T : Subgroup ↥(StatedSp n (GaloisField 2 f))} (ha : a ≠ 0) (hT : CaseM.IsTransGroup a T)
    (hTV : T.map Φ.toMonoidHom = Vy V H) (r : ↥(bigRIsub M V H)) :
    bigRIrho M V H hc.V_le_H Φ r ∈ spFix a := by
  rw [mem_spFix_iff]
  refine mat_mulVec_eq_of_mem_centralizer hT ha ?_
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have hΦt : Φ t ∈ Vy V H := hTV ▸ Subgroup.mem_map_of_mem Φ.toMonoidHom ht
  obtain ⟨v, hvV, hv⟩ := bigRI_mem_Vy hc.V_le_H hΦt
  apply Φ.injective
  rw [map_mul, map_mul, bigRIrho_apply, ← hv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, bigRIincl_coe]
  exact Subgroup.mem_centralizer_iff.mp (bigRIsub_centralizes r) _ hvV

theorem bigRIrho_mem_spRad_iff [Finite G] {M V Q P H : Subgroup G}
    (hH : BigEndHyp M V Q P H) {n f : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H) {a : Fin n ⊕ Fin n → GaloisField 2 f}
    (hRbar : Rbar V H P = (spRad a).map Φ.toMonoidHom) (r : ↥(bigRIsub M V H)) :
    bigRIrho M V H hH.setup.mc.toMinCex.V_le_H Φ r ∈ spRad a ↔ ((r : ↥M) : G) ∈ P := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have h1 : bigRIrho M V H hVH Φ r ∈ spRad a ↔ xToXbar hVH (bigRIincl M V H r) ∈ Rbar V H P := by
    rw [hRbar, ← bigRIrho_apply M V H hVH Φ r, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [h1, mem_Rbar, coe_xToXbar]
  constructor
  · intro h
    obtain ⟨p, hpP, hp⟩ := mem_barOf_iff.mp h
    have h2 : piBar V H (p⁻¹ * Subgroup.inclusion (xOf_le_H hVH) (bigRIincl M V H r)) = 1 := by
      rw [map_mul, map_inv, hp, inv_mul_cancel]
    have h3 := (piBar_eq_one_iff _).mp h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, bigRIincl_coe] at h3
    have hpC : (p : G) ∈ Subgroup.centralizer (V : Set G) := by
      have : (p : G) ∈ Q ⊓ Subgroup.centralizer (V : Set G) := hc.hP ▸ hpP
      exact (Subgroup.mem_inf.mp this).2
    have h4 : (p : G)⁻¹ * ((r : ↥M) : G) ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hpC) (bigRIsub_centralizes r)
    have h5 : (p : G)⁻¹ * ((r : ↥M) : G) ∈ P ⊓ wOf V H :=
      hH.wOf_inf_centralizer_eq ▸ Subgroup.mem_inf.mpr ⟨h3, h4⟩
    have h6 : (p : G) * ((p : G)⁻¹ * ((r : ↥M) : G)) ∈ P :=
      P.mul_mem hpP (Subgroup.mem_inf.mp h5).1
    simpa using h6
  · intro h
    exact mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) (bigRIincl M V H r), h, rfl⟩

theorem bigRInu_eq_one_iff [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H)
    (r : ↥(bigRIsub M V H)) : bigRInu M V H r = 1 ↔ ((r : ↥M) : G) ∈ P := by
  have h1 : bigRInu M V H r = 1 ↔ ((r : ↥M) : G) ∈ inSubgroup (pCore 2) M := by
    show ((r : ↥M) : Mbar M) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rw [h1, ← hc.hQ]
  constructor
  · intro h
    rw [hc.hP]
    exact Subgroup.mem_inf.mpr ⟨h, bigRIsub_centralizes r⟩
  · intro h
    exact hc.P_le_Q h

theorem bigRI_le_M [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) :
    xOf V H ⊓ Subgroup.centralizer (V : Set G) ≤ M := fun r hr => by
  rw [← hc.normalizer_eq]
  exact Subgroup.centralizer_le_normalizer (V : Set G) (Subgroup.mem_inf.mp hr).2

theorem bigRI_exists_of_mem_V [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) {v : G}
    (hv : v ∈ V) : ∃ r : ↥(bigRIsub M V H), ((r : ↥M) : G) = v := by
  have hvX : v ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hv
  have hvC : v ∈ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hc.maxAb.prop.2.2 hv
  exact ⟨⟨⟨v, hc.maxAb.prop.1 hv⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hvX, hvC⟩)⟩,
    rfl⟩

section Natural

variable {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f} {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}

theorem bigRI_psi_injective {u v : Fin n ⊕ Fin n → GaloisField 2 f}
    (h : ((Additive.toMul (ψ u) : ↥(wOf V H)) : G) = ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)) :
    u = v :=
  ψ.injective (Additive.toMul.injective (Subtype.ext h))

theorem bigRI_spFix_le_range [Finite G] (hH : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    (hroot : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f),
      CaseM.spForm a c = 0 → (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
        ∀ y, r * ((Additive.toMul (ψ y) : ↥(wOf V H)) : G) * r⁻¹ =
          ((Additive.toMul (ψ (y + (μ * CaseM.spForm c y) • c)) : ↥(wOf V H)) : G)) :
    spFix a ≤ (bigRIrho M V H hH.setup.mc.toMinCex.V_le_H Φ).range := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  intro g hg
  refine (Subgroup.closure_le _).mpr ?_ (spStabGenModel_holds n (GaloisField 2 f) a ha g hg)
  rintro x ⟨b, c, hb, hx⟩
  by_cases hbl : ∃ l : GaloisField 2 f, b = l • a
  · obtain ⟨l, rfl⟩ := hbl
    have hxT : x ∈ T := (hT.1 x).2 ⟨l * l * c, by rw [hx, CaseM.spTrans_smul]⟩
    have hΦx : Φ x ∈ Vy V H := hTV ▸ Subgroup.mem_map_of_mem Φ.toMonoidHom hxT
    obtain ⟨v, hvV, hv⟩ := bigRI_mem_Vy hVH hΦx
    obtain ⟨r, hr⟩ := bigRI_exists_of_mem_V hc hvV
    refine ⟨r, ?_⟩
    have hrv : bigRIincl M V H r = v := Subtype.ext hr
    apply Φ.injective
    rw [bigRIrho_apply, hrv, hv]
  · by_cases hc0 : c = 0
    · subst hc0
      have h1 : x = 1 := SpExtras.mat_injective (by rw [hx, ModelRank.spTrans_zero, map_one])
      rw [h1]
      exact one_mem _
    · obtain ⟨r, hrR, hr⟩ := hroot b c hb (fun l hl => hbl ⟨l, hl⟩) hc0
      have hrM : r ∈ M := bigRI_le_M hc hrR
      refine ⟨⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr hrR⟩, ?_⟩
      apply eq_of_mat_mulVec_eq
      intro y
      refine bigRI_psi_injective (ψ := ψ) ?_
      exact (hNat.equiv ⟨r, hrR.1⟩ y).trans ((hr y).trans (by
        rw [hx, ModelRank.spTrans_mulVec]))

theorem bigRI_main [Finite G] (hH : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    (hRbar : Rbar V H P = (spRad a).map Φ.toMonoidHom)
    (hroot : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f),
      CaseM.spForm a c = 0 → (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
        ∀ y, r * ((Additive.toMul (ψ y) : ↥(wOf V H)) : G) * r⁻¹ =
          ((Additive.toMul (ψ (y + (μ * CaseM.spForm c y) • c)) : ↥(wOf V H)) : G))
    (hStab : ∃ π : ↥(spFix a) →* StatedSp (n - 1) (GaloisField 2 f),
      Function.Surjective π ∧ π.ker = (spRad a).subgroupOf (spFix a)) :
    Nonempty (↥(RbarM M V H) ≃* StatedSp (n - 1) (GaloisField 2 f)) := by
  obtain ⟨π, hπs, hπk⟩ := hStab
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  set ρ' : ↥(bigRIsub M V H) →* ↥(spFix a) :=
    (bigRIrho M V H hVH Φ).codRestrict (spFix a) (bigRIrho_mem_spFix hc Φ ha hT hTV)
  have hρ'val : ∀ r, ((ρ' r : ↥(spFix a)) : StatedSp n (GaloisField 2 f)) =
      bigRIrho M V H hVH Φ r := fun r => rfl
  have hθs : Function.Surjective (π.comp ρ') := by
    intro y
    obtain ⟨g, rfl⟩ := hπs y
    obtain ⟨r, hr⟩ := bigRI_spFix_le_range hH hNat ha hT hTV hroot g.2
    refine ⟨r, ?_⟩
    have : ρ' r = g := Subtype.ext hr
    simp only [MonoidHom.comp_apply, this]
  have hθk : (π.comp ρ').ker = (bigRInu M V H).ker := by
    ext r
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, bigRInu_eq_one_iff hc, MonoidHom.comp_apply,
      ← MonoidHom.mem_ker, hπk, Subgroup.mem_subgroupOf, hρ'val,
      bigRIrho_mem_spRad_iff hH Φ hRbar]
  obtain ⟨e⟩ := bigRI_range_equiv (bigRInu M V H) (π.comp ρ') hθs hθk
  exact ⟨(MulEquiv.subgroupCongr (bigRInu_range M V H).symm).trans e⟩

end Natural

theorem bigRbarIsoStatement_of_local (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) (hLoc : BigPLocalStatement) (hroot : BigRootElementStatement)
    : BigRbarIsoStatement := by
  have hStab := @spStabQuotStatement_holds
  intro G _ _ M V Q P H hH n f hn2 hfq ⟨e⟩
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · exfalso
      have h4 := hH.q_big
      rw [← hfq, h] at h4
      norm_num at h4
    · exact h
  obtain ⟨n', f', Φ, ψ, hn', hf'q, hequiv, ⟨a, T, ha, hTT, hTV⟩, hpoint⟩ :=
    hN G M V Q P H hH hcentre
  obtain rfl : f' = f := Nat.pow_right_injective (le_refl 2) (hf'q.trans hfq.symm)
  have e' : ↥(StatedSp n (GaloisField 2 f')) ≃* Xbar V H :=
    e.trans (MulEquiv.ofBijective (projZ V H) (iw_projZ_bijective hcentre)).symm
  have hcard : Nat.card ↥(StatedSp n' (GaloisField 2 f')) =
      Nat.card ↥(StatedSp n (GaloisField 2 f')) := Nat.card_congr (Φ.trans e'.symm).toEquiv
  have hval := padicValNat_card_statedSp f' hf n'
  rw [hcard, padicValNat_card_statedSp f' hf n] at hval
  obtain rfl : n' = n := by
    have h1 : n ^ 2 = n' ^ 2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f') hval
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) h1).symm
  have hNat : BigNatCfg V H hVH Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨-, hRbar, -, -⟩ := hLoc G M V Q P H hH hcentre hcP hfq Φ ψ hNat a T ha hTT hTV
  exact bigRI_main hH hNat ha hTT hTV hRbar
    (hroot G M V Q P H hH hcentre hcP hfq Φ ψ hNat a T ha hTT hTV) (hStab hn2 a ha)

end CFSG.RankThree.GF2n.Tim79a
