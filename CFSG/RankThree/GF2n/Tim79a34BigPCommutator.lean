module

public import CFSG.RankThree.GF2n.Tim79a34BigModel
public import CFSG.RankThree.GF2n.Tim78Frattini
public import CFSG.RankThree.GF2n.Tim79a34BigNatural
public import CFSG.RankThree.GF2n.Tim79a34SpRad
public import CFSG.RankThree.GF2n.Tim79aSec24Inner
public import CFSG.Timmesfeld.ARS.CaseOADegSpAlign

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

theorem bigPsi_mul {G : Type} [Group G] {V H : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (ψ : (Fin n ⊕ Fin n → F) ≃+ Additive ↥(wOf V H)) (u v : Fin n ⊕ Fin n → F) :
    ((Additive.toMul (ψ u) : ↥(wOf V H)) : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) =
      ((Additive.toMul (ψ (u + v)) : ↥(wOf V H)) : G) := by
  rw [map_add]
  rfl

theorem bigPsi_comm {G : Type} [Group G] {V H : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (ψ : (Fin n ⊕ Fin n → F) ≃+ Additive ↥(wOf V H)) (u v : Fin n ⊕ Fin n → F) :
    ((Additive.toMul (ψ u) : ↥(wOf V H)) : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) =
      ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * ((Additive.toMul (ψ u) : ↥(wOf V H)) : G) := by
  rw [bigPsi_mul ψ u v, bigPsi_mul ψ v u, add_comm u v]

theorem bigP_exists_act {G : Type} [Group G] {V H P : Subgroup G} (hVH : V ≤ H) {n f : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    (hNat : BigNatCfg V H hVH Φ ψ) (hxOf : xOf V H = H)
    {a : Fin n ⊕ Fin n → GaloisField 2 f}
    (hRbar : Rbar V H P = (spRad a).map Φ.toMonoidHom)
    {g : ↥(StatedSp n (GaloisField 2 f))} (hg : g ∈ spRad a) :
    ∃ p ∈ P, ∀ v, ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 f) g *ᵥ v)) :
      ↥(wOf V H)) : G) = p * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * p⁻¹ := by
  have hΦg : Φ.toMonoidHom g ∈ Rbar V H P := by
    rw [hRbar]
    exact Subgroup.mem_map_of_mem _ hg
  obtain ⟨x, hxP, hxg⟩ := mem_barOf_iff.mp (mem_Rbar.mp hΦg)
  have hpX : (x : G) ∈ xOf V H := by
    rw [hxOf]
    exact x.2
  have hxX : xToXbar hVH ⟨(x : G), hpX⟩ = Φ g :=
    Subtype.ext (by rw [coe_xToXbar]; exact hxg)
  refine ⟨(x : G), hxP, fun v => ?_⟩
  have hkey := hNat.equiv ⟨(x : G), hpX⟩ v
  rw [hxX, MulEquiv.symm_apply_apply] at hkey
  exact hkey

theorem bigPCommutatorStatement_of_local (hN : BigNaturalStatement) (hLoc : BigPLocalStatement)
    (hR : SpRadGeneralStatement) : BigPCommutatorStatement := by
  intro G _ _ M V Q P H hH hZ hcP
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨n, f, Φ, ψ, hn2, hf, hNat, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hZ
  have hNC : BigNatCfg V H hVH Φ ψ := ⟨hNat, hpoint⟩
  obtain ⟨hiff, hRbar, hxOf, -⟩ := hLoc G M V Q P H hH hZ hcP hf Φ ψ hNC a T ha hT hTV
  have hn : 1 ≤ n := by omega
  have hR' := hR n hn (GaloisField 2 f) a ha
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h4 := hH.q_big
    rw [← hf] at h4
    norm_num at h4
  have hFcard : Nat.card (GaloisField 2 f) = qBar V H := by
    rw [GaloisField.card 2 f hf0, hf]
  have hVW : Nat.card ↥(V ⊓ wOf V H) = Nat.card (GaloisField 2 f) := hH.module.trans hFcard.symm
  have hPH : P ≤ H := hc.PleH
  have hPX : P ≤ xOf V H := by
    rw [hxOf]
    exact hPH
  have hmemR : ∀ p : G, ∀ hp : p ∈ P, xToXbar hVH ⟨p, hPX hp⟩ ∈ Rbar V H P := by
    intro p hp
    rw [mem_Rbar, coe_xToXbar]
    exact mem_barOf_iff.mpr ⟨⟨p, hPH hp⟩, hp, rfl⟩
  have hsp : ∀ p : G, ∀ hp : p ∈ P, ∃ g ∈ spRad a,
      Φ.toMonoidHom g = xToXbar hVH ⟨p, hPX hp⟩ := by
    intro p hp
    have h := hmemR p hp
    rw [hRbar] at h
    exact Subgroup.mem_map.mp h
  have hker : ∀ z : ↥(xOf V H), xToXbar hVH z = 1 ↔ (z : G) ∈ wOf V H := by
    intro z
    constructor
    · intro h
      have h1 : piBar V H (Subgroup.inclusion (xOf_le_H hVH) z) = 1 := by
        rw [← coe_xToXbar hVH z, h]
        rfl
      exact (piBar_eq_one_iff _).mp h1
    · intro h
      apply Subtype.ext
      rw [coe_xToXbar hVH z]
      exact (piBar_eq_one_iff _).mpr h
  have hcommW : ∀ p : G, ∀ hp : p ∈ P, ∀ q : G, ∀ hq : q ∈ P, ⁅p, q⁆ ∈ wOf V H := by
    intro p hp q hq
    obtain ⟨g, hg, hgp⟩ := hsp p hp
    obtain ⟨h, hh, hhq⟩ := hsp q hq
    have hgh : Φ.toMonoidHom g * Φ.toMonoidHom h = Φ.toMonoidHom h * Φ.toMonoidHom g := by
      rw [← map_mul, ← map_mul, hR'.1 g hg h hh]
    have h1 : xToXbar hVH ⁅(⟨p, hPX hp⟩ : ↥(xOf V H)), ⟨q, hPX hq⟩⁆ = 1 := by
      rw [map_commutatorElement, ← hgp, ← hhq, commutatorElement_eq_one_iff_mul_comm]
      exact hgh
    exact (hker _).mp h1
  have hsqW : ∀ p : G, ∀ hp : p ∈ P, p * p ∈ wOf V H := by
    intro p hp
    obtain ⟨g, hg, hgp⟩ := hsp p hp
    have h1 : xToXbar hVH ((⟨p, hPX hp⟩ : ↥(xOf V H)) * ⟨p, hPX hp⟩) = 1 := by
      rw [map_mul, ← hgp, ← map_mul, hR'.2.1 g hg, map_one]
    exact (hker _).mp h1
  have hPPV : ⁅P, P⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    exact hc.commutator_mem_V_of_mem_P hp hq
  have hPPW : ⁅P, P⁆ ≤ wOf V H := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    exact hcommW p hp q hq
  have hwex : ∃ w : Fin n ⊕ Fin n → GaloisField 2 f, CaseM.spForm a w = 0 ∧
      ∀ c : GaloisField 2 f, w ≠ c • a := by
    obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
    have hba : CaseM.spForm b a = -1 := by
      rw [CaseM.spForm_comm, hb]
    obtain ⟨w, hw0, hw⟩ := exists_ne_zero_forall_spForm_eq_zero ![a, b]
      (by rw [Fintype.card_fin]; omega)
    refine ⟨w, hw 0, fun c hc => hw0 ?_⟩
    have h1 : CaseM.spForm b w = 0 := hw 1
    rw [hc, spForm_smul_right', hba] at h1
    have hc0 : c = 0 := by linear_combination -h1
    rw [hc, hc0, zero_smul]
  obtain ⟨w, haw, hwa⟩ := hwex
  obtain ⟨u, hau, hwu⟩ := exists_dual ha haw hwa
  have huw : CaseM.spForm u w = 1 := by
    rw [CaseM.spForm_comm, hwu, CharTwo.neg_eq]
  have hxP : ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P := (hiff w).mpr haw
  have hPaG : ∀ l : GaloisField 2 f,
      ((Additive.toMul (ψ (l • a)) : ↥(wOf V H)) : G) ∈ ⁅P, P⁆ := by
    intro l
    have hul : CaseM.spForm a (l • u) = 0 := by
      rw [spForm_smul_right', hau, mul_zero]
    obtain ⟨p, hp, hpact⟩ := bigP_exists_act hVH hNC hxOf hRbar (spTau_mem a (l • u) 0 hul)
    have hτw : SpExtras.mat n (GaloisField 2 f) (spTau a (l • u) 0 hul) *ᵥ w = w + l • a := by
      rw [spTau_mulVec, haw, spForm_smul_left', huw]
      simp
    have hact : ((Additive.toMul (ψ (w + l • a)) : ↥(wOf V H)) : G) =
        p * ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) * p⁻¹ := by
      have h := hpact w
      rw [hτw] at h
      exact h
    have hconj : p * ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) * p⁻¹ =
        ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) *
          ((Additive.toMul (ψ (l • a)) : ↥(wOf V H)) : G) := by
      rw [← hact, bigPsi_mul ψ w (l • a)]
    have hcm := Subgroup.commutator_mem_commutator hp hxP
    have heq : ⁅p, ((Additive.toMul (ψ w) : ↥(wOf V H)) : G)⁆ =
        ((Additive.toMul (ψ (l • a)) : ↥(wOf V H)) : G) := by
      rw [commutatorElement_def, hconj, bigPsi_comm ψ w (l • a), mul_inv_cancel_right]
    rw [← heq]
    exact hcm
  have hVWmem : ∀ l : GaloisField 2 f,
      ((Additive.toMul (ψ (l • a)) : ↥(wOf V H)) : G) ∈ V ⊓ wOf V H := by
    intro l
    refine Subgroup.mem_inf.mpr ⟨?_, (Additive.toMul (ψ (l • a))).2⟩
    by_cases hl : l = 0
    · rw [hl, zero_smul, map_zero]
      exact V.one_mem
    · exact hpoint (l • a) T (smul_ne_zero hl ha) (CaseOADeg.isTransGroup_smul hl hT) hTV
  have hbij : Function.Bijective (fun l : GaloisField 2 f =>
      (⟨((Additive.toMul (ψ (l • a)) : ↥(wOf V H)) : G), hVWmem l⟩ : ↥(V ⊓ wOf V H))) := by
    refine Function.Injective.bijective_of_nat_card_le ?_ hVW.le
    intro l l' h
    have h0 : ((Additive.toMul (ψ (l • a)) : ↥(wOf V H)) : G) =
        ((Additive.toMul (ψ (l' • a)) : ↥(wOf V H)) : G) :=
      congrArg (Subtype.val : ↥(V ⊓ wOf V H) → G) h
    have h1 : ψ (l • a) = ψ (l' • a) := Additive.toMul.injective (Subtype.ext h0)
    have h2 : l • a = l' • a := ψ.injective h1
    by_contra hll
    apply ha
    have h3 : (l - l') • a = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) hll
    · exact h
  have hVWle : V ⊓ wOf V H ≤ ⁅P, P⁆ := by
    intro x hx
    obtain ⟨l, hl⟩ := hbij.2 ⟨x, hx⟩
    have hx' : ((Additive.toMul (ψ (l • a)) : ↥(wOf V H)) : G) = x :=
      congrArg (Subtype.val : ↥(V ⊓ wOf V H) → G) hl
    rw [← hx']
    exact hPaG l
  have hcomm_eq : ⁅P, P⁆ = V ⊓ wOf V H := le_antisymm (le_inf hPPV hPPW) hVWle
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hc.isPGroup_P⟩
  have hP2 : IsPGroup 2 P := hc.isPGroup_P
  have hfr_le : inSubgroup frattini P ≤ V ⊓ wOf V H := by
    have hle : frattini ↥P ≤ (V ⊓ wOf V H).subgroupOf P := by
      rw [frattini_eq_closure_commutator_union_powers (p := 2)]
      apply (Subgroup.closure_le _).mpr
      rintro x (hx | ⟨y, rfl⟩)
      · have hcomm_le : _root_.commutator ↥P ≤ (V ⊓ wOf V H).subgroupOf P := by
          show ⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆ ≤ _
          refine Subgroup.commutator_le.mpr ?_
          intro g₁ _ g₂ _
          rw [Subgroup.mem_subgroupOf, ← hcomm_eq]
          exact Subgroup.commutator_mem_commutator g₁.2 g₂.2
        exact hcomm_le hx
      · simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.coe_pow]
        exact ⟨hc.frattini_P_le (Tim78.sq_mem_inSubgroup_frattini hP2 y.2),
          by rw [pow_two]; exact hsqW _ y.2⟩
    exact Subgroup.map_le_iff_le_comap.mpr hle
  refine ⟨hcomm_eq, ?_, hc.centralizer_P_eq⟩
  apply le_antisymm hfr_le
  rw [← hcomm_eq]
  exact Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ =>
    Tim78.commutatorElement_mem_inSubgroup_frattini hP2 hg₁ hg₂

theorem exists_spTau_mulVec_eq {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a b u : Fin n ⊕ Fin n → F} (hb : CaseM.spForm a b ≠ 0) (hu : CaseM.spForm a u = 0) :
    ∃ (u' : Fin n ⊕ Fin n → F) (c : F) (hu' : CaseM.spForm a u' = 0),
      SpExtras.mat n F (spTau a u' c hu') *ᵥ b = b + u := by
  obtain ⟨μ, hμ⟩ : ∃ μ : F, CaseM.spForm a b = μ := ⟨_, rfl⟩
  rw [hμ] at hb
  have hu' : CaseM.spForm a (μ⁻¹ • u) = 0 := by
    rw [spForm_smul_right', hu, mul_zero]
  refine ⟨μ⁻¹ • u, μ⁻¹ * CaseM.spForm (μ⁻¹ • u) b, hu', ?_⟩
  rw [spTau_mulVec, hμ, smul_smul, mul_inv_cancel₀ hb, one_smul]
  have h2 : μ⁻¹ * CaseM.spForm (μ⁻¹ • u) b * μ = CaseM.spForm (μ⁻¹ • u) b := by
    field_simp
  rw [h2]
  linear_combination (norm := module)
    CFSG.Timmesfeld.Transvection.ModelRank.vec_add_self (CaseM.spForm (μ⁻¹ • u) b • a)

theorem bigPCoverStatement_of_local (hR : SpRadGeneralStatement) (hLoc : BigPLocalStatement) :
    BigPCoverStatement := by
  intro G _ _ M V Q P H hH hZ hcP n f hf Φ ψ hNat a T ha hT hTV b hb w hw
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨hiff, hRbar, hxOf, -⟩ := hLoc G M V Q P H hH hZ hcP hf Φ ψ hNat a T ha hT hTV
  have hwP : w ∈ P := (Subgroup.mem_inf.mp hw).1
  have hwW : w ∈ wOf V H := (Subgroup.mem_inf.mp hw).2
  obtain ⟨u, hψu⟩ : ∃ u : Fin n ⊕ Fin n → GaloisField 2 f,
      ((Additive.toMul (ψ u) : ↥(wOf V H)) : G) = w :=
    ⟨ψ.symm (Additive.ofMul ⟨w, hwW⟩), by rw [AddEquiv.apply_symm_apply]; rfl⟩
  have hu : CaseM.spForm a u = 0 := (hiff u).mp (by rw [hψu]; exact hwP)
  obtain ⟨u', c, hu', hτb⟩ := exists_spTau_mulVec_eq hb hu
  obtain ⟨p, hp, hpact⟩ := bigP_exists_act hVH hNat hxOf hRbar (spTau_mem a u' c hu')
  have hkey : ((Additive.toMul (ψ (b + u)) : ↥(wOf V H)) : G) =
      p * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) * p⁻¹ := by
    have h := hpact b
    rw [hτb] at h
    exact h
  refine ⟨p, hp, ?_⟩
  rw [commutatorElement_def, ← hkey, ← bigPsi_mul ψ b u, mul_inv_eq_iff_eq_mul,
    bigPsi_comm ψ b u, hψu]

end CFSG.RankThree.GF2n.Tim79a
