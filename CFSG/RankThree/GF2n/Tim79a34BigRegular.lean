module

public import CFSG.RankThree.GF2n.Tim79a34BigModel
public import CFSG.RankThree.GF2n.Tim79a34BigWCentral
public import CFSG.RankThree.GF2n.Tim79aSec34Torus
public import CFSG.Timmesfeld.Transvection.ModelRadical

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.LieType.Universal.Symplectic
open Matrix

theorem bigReg_exists_pow_eq {F : Type} [Field F] [Finite F] {ν : F} (hν : ν ≠ 0)
    (hord : ν ^ (Nat.card F - 1) = 1) (hreg : ∀ i : ℕ, 0 < i → i < Nat.card F - 1 → ν ^ i ≠ 1)
    {z : F} (hz : z ≠ 0) : ∃ k : ℕ, ν ^ k = z := by
  have hcard : 0 < Nat.card F - 1 := by
    have := Finite.one_lt_card (α := F)
    omega
  set u : Fˣ := Units.mk0 ν hν with hu
  have hord' : orderOf u = Nat.card F - 1 := by
    rw [orderOf_eq_iff hcard]
    refine ⟨Units.ext (by simpa [hu] using hord), fun m hm hm0 h => hreg m hm0 hm ?_⟩
    simpa [hu] using congrArg Units.val h
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord', Nat.card_units]
  have hmem : Units.mk0 z hz ∈ Subgroup.zpowers u := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.mpr hmem
  exact ⟨k, by simpa [hu] using congrArg Units.val hk⟩

theorem bigReg_mat_pow_mulVec {n : ℕ} {F : Type} [Field F] {g : ↥(StatedSp n F)}
    {a : Fin n ⊕ Fin n → F} {ν : F} (hg : SpExtras.mat n F g *ᵥ a = ν • a) (k : ℕ) :
    SpExtras.mat n F (g ^ k) *ᵥ a = ν ^ k • a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', map_mul, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hg, smul_smul,
      pow_succ]

theorem bigReg_spForm_pow {n : ℕ} {F : Type} [Field F] {g : ↥(StatedSp n F)}
    {a : Fin n ⊕ Fin n → F} {ν : F} (hg : SpExtras.mat n F g *ᵥ a = ν • a) (k : ℕ)
    (y : Fin n ⊕ Fin n → F) :
    ν ^ k * CaseM.spForm a (SpExtras.mat n F (g ^ k) *ᵥ y) = CaseM.spForm a y := by
  have h1 := ModelRank.spForm_mat_mulVec (g ^ k) a y
  rw [bigReg_mat_pow_mulVec hg k, ModelRank.spForm_smul_left'] at h1
  exact h1

theorem bigReg_mem_normalizer_RbarM {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}
    (hc : MinCex M V Q P H) {x : G} (hxX : x ∈ xOf V H) (hxM : x ∈ M) :
    ((⟨x, hxM⟩ : ↥M) : Mbar M) ∈ Subgroup.normalizer (RbarM M V H : Set (Mbar M)) := by
  have key : ∀ k : ↥M, (k : G) ∈ xOf V H → ∀ b ∈ RbarM M V H,
      (k : Mbar M) * b * (k : Mbar M)⁻¹ ∈ RbarM M V H := by
    intro k hkX b hb
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hb
    have hrG : (r : G) ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_subgroupOf.mp hr
    refine Subgroup.mem_map.mpr ⟨k * r * k⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine Subgroup.mem_inf.mpr ⟨(xOf V H).mul_mem ((xOf V H).mul_mem hkX hrG.1)
        ((xOf V H).inv_mem hkX), Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro v hv
      have hkM' : (k : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
        rw [hc.normalizer_eq]
        exact M.inv_mem k.2
      have hv' : (k : G)⁻¹ * v * (k : G) ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp hkM' v).mp hv
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hrG.2 _ hv'
      have e1 : v * ((k : G) * r * (k : G)⁻¹) =
          (k : G) * (((k : G)⁻¹ * v * (k : G)) * r) * (k : G)⁻¹ := by group
      have e2 : ((k : G) * r * (k : G)⁻¹) * v =
          (k : G) * (r * ((k : G)⁻¹ * v * (k : G))) * (k : G)⁻¹ := by group
      rw [e1, e2, hcomm]
    · simp only [map_mul, map_inv, QuotientGroup.mk'_apply]
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · exact key ⟨x, hxM⟩ hxX b
  · intro hb
    set k0 : ↥M := ⟨x, hxM⟩ with hk0
    have h1 := key k0⁻¹ ((xOf V H).inv_mem hxX) _ hb
    rw [QuotientGroup.mk_inv, inv_inv] at h1
    have e : (k0 : Mbar M)⁻¹ * ((k0 : Mbar M) * b * (k0 : Mbar M)⁻¹) * (k0 : Mbar M) = b := by
      group
    rwa [e] at h1

section Natural

variable {G : Type} [Group G] {V H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem bigReg_psi_pow {hVH : V ≤ H} (hNat : BigNatCfg V H hVH Φ ψ) (x : ↥(xOf V H)) (k : ℕ)
    (v : Fin n ⊕ Fin n → GaloisField 2 f) :
    ψG (SpExtras.mat n (GaloisField 2 f) (Φ.symm (xToXbar hVH x) ^ k) *ᵥ v) =
      (x : G) ^ k * ψG v * ((x : G) ^ k)⁻¹ := by
  have h := hNat.equiv (x ^ k) v
  simp only [map_pow, Subgroup.coe_pow] at h
  exact h

theorem bigReg_wbar_rep [Finite G] {M P Q : Subgroup G} (hc : MinCex M V Q P H)
    {a : Fin n ⊕ Fin n → GaloisField 2 f}
    (hiff : ∀ w, ψG w ∈ P ↔ CaseM.spForm a w = 0) {b : Mbar M} (hb : b ∈ WbarM M V H)
    (hb1 : b ≠ 1) :
    ∃ (w : ↥M) (y : Fin n ⊕ Fin n → GaloisField 2 f), (w : G) = ψG y ∧
      CaseM.spForm a y ≠ 0 ∧ (w : Mbar M) = b := by
  obtain ⟨w, hwW, rfl⟩ := mem_WbarM_iff.mp hb
  obtain ⟨y, hy⟩ : ∃ y : Fin n ⊕ Fin n → GaloisField 2 f, ψG y = (w : G) :=
    ⟨ψ.symm (Additive.ofMul ⟨(w : G), hwW⟩), by rw [AddEquiv.apply_symm_apply]; rfl⟩
  refine ⟨w, y, hy.symm, fun h0 => hb1 ?_, rfl⟩
  have hP : (w : G) ∈ P := by
    rw [← hy]
    exact (hiff y).mpr h0
  have hQ : (w : G) ∈ inSubgroup (pCore 2) M := by
    have h1 := hc.P_le_Q hP
    rwa [hc.hQ] at h1
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr hQ

theorem bigReg_mk_eq [Finite G] {M P Q : Subgroup G} (hc : MinCex M V Q P H)
    {a : Fin n ⊕ Fin n → GaloisField 2 f}
    (hiff : ∀ w, ψG w ∈ P ↔ CaseM.spForm a w = 0)
    {z y' : Fin n ⊕ Fin n → GaloisField 2 f} (hzy : CaseM.spForm a z = CaseM.spForm a y')
    {u u' : ↥M} (hu : (u : G) = ψG z) (hu' : (u' : G) = ψG y') :
    (u : Mbar M) = (u' : Mbar M) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hz0 : CaseM.spForm a (z + y') = 0 := by
    rw [ModelRank.spForm_add_right, hzy]
    exact CharTwo.add_self_eq_zero _
  have hP : ψG (z + y') ∈ P := (hiff _).mpr hz0
  have hQ : ψG (z + y') ∈ inSubgroup (pCore 2) M := by
    have h1 := hc.P_le_Q hP
    rwa [hc.hQ] at h1
  have hinv : (ψG z)⁻¹ = ψG z := inv_eq_of_mul_eq_one_right (bigRW_psi_mul_self z)
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hu, hu', hinv, bigRW_psi_mul]
  exact hQ

theorem bigRegularStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hT : Sec34TorusStatement) (hN : BigNaturalStatement) (hIW : BigIWStatement)
    (hLoc : BigPLocalStatement) : BigRegularStatement := by
  intro G _ _ M V Q P H hH
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  obtain ⟨n, f, Φ, ψ, hn2, hf, hequiv, ⟨a, T, ha, hTT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hcentre
  have hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  have hiff := (hLoc G M V Q P H hH hcentre hcP hf Φ ψ hNat a T ha hTT hTV).1
  obtain ⟨f₀, -, hf₀, h, hhX, hhV, hord, hreg, -⟩ :=
    hT G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h4 := hH.q_big
    rw [← hf] at h4
    norm_num at h4
  have hFcard : Nat.card (GaloisField 2 f) = qBar V H := by
    rw [GaloisField.card 2 f hf0, hf]
  have hq : 2 ^ f₀ = Nat.card (GaloisField 2 f) := hf₀.trans hFcard.symm
  have hhH : h ∈ H := xOf_le_H hVH hhX
  have hhM : h ∈ M := hc.normalizer_eq ▸ mem_normalizer_of_conjSubgroup_eq hhV
  obtain ⟨g, hg⟩ : ∃ g : ↥(StatedSp n (GaloisField 2 f)),
      g = Φ.symm (xToXbar hVH ⟨h, hhX⟩) := ⟨_, rfl⟩
  have hgk : ∀ (k : ℕ) (v : Fin n ⊕ Fin n → GaloisField 2 f),
      ψG (SpExtras.mat n (GaloisField 2 f) (g ^ k) *ᵥ v) = h ^ k * ψG v * (h ^ k)⁻¹ := by
    intro k v
    rw [hg]
    exact bigReg_psi_pow hNat ⟨h, hhX⟩ k v
  have haV : ψG a ∈ V := hpoint a T ha hTT hTV
  have haA : ψG a ∈ V ⊓ wOf V H := Subgroup.mem_inf.mpr ⟨haV, (Additive.toMul (ψ a)).2⟩
  have hpowN : ∀ k : ℕ, h ^ k ∈ Subgroup.normalizer (V : Set G) := fun k =>
    Subgroup.pow_mem _ (mem_normalizer_of_conjSubgroup_eq hhV) k
  have hconjA : ∀ k : ℕ, ∀ u ∈ V ⊓ wOf V H, h ^ k * u * (h ^ k)⁻¹ ∈ V ⊓ wOf V H :=
    fun k u hu =>
      ⟨((Subgroup.mem_normalizer_iff.mp (hpowN k)) u).mp hu.1,
        ((Subgroup.mem_normalizer_iff.mp
          (H_le_normalizer_wOf V H (Subgroup.pow_mem H hhH k))) u).mp hu.2⟩
  obtain ⟨ν, hν⟩ : ∃ ν : GaloisField 2 f, SpExtras.mat n (GaloisField 2 f) g *ᵥ a = ν • a := by
    have h1 := hgk 1 a
    simp only [pow_one] at h1
    have h2 : ψG (SpExtras.mat n (GaloisField 2 f) g *ᵥ a) ∈ V := by
      rw [h1]
      have := (hconjA 1 _ haA).1
      simpa using this
    obtain ⟨l, hl⟩ := bigRW_eq_smul_of_psi_mem_V hH hf hNat ha hTT hTV h2
    exact ⟨l, hl⟩
  have hν0 : ν ≠ 0 := by
    rintro rfl
    have h1 := CaseOADeg.mat_mulVec_ne_zero' g ha
    rw [hν, zero_smul] at h1
    exact h1 rfl
  have hνord : ν ^ (Nat.card (GaloisField 2 f) - 1) = 1 := by
    have h1 := hgk (2 ^ f₀ - 1) a
    rw [bigReg_mat_pow_mulVec hν, hord _ haA] at h1
    have h2 := bigRW_psi_injective h1
    have h3 : ν ^ (2 ^ f₀ - 1) = 1 :=
      smul_left_injective (GaloisField 2 f) ha (by simpa using h2)
    rwa [hq] at h3
  have hνreg : ∀ i : ℕ, 0 < i → i < Nat.card (GaloisField 2 f) - 1 → ν ^ i ≠ 1 := by
    intro i hi0 hi h1
    have h2 := hgk i a
    rw [bigReg_mat_pow_mulVec hν, h1, one_smul] at h2
    have h3 : ψG a = 1 := hreg i hi0 (by rw [hq]; exact hi) (ψG a) haA h2.symm
    exact ha (bigRW_psi_injective (h3.trans (bigRW_psi_zero (ψ := ψ)).symm))
  have hgen : ∀ z : GaloisField 2 f, z ≠ 0 → ∃ k : ℕ, ν ^ k = z := fun z hz =>
    bigReg_exists_pow_eq hν0 hνord hνreg hz
  refine ⟨((⟨h, hhM⟩ : ↥M) : Mbar M), bigReg_mem_normalizer_RbarM hc hhX hhM, ?_⟩
  intro b hb hb1 b' hb' hb1'
  obtain ⟨w, y, hwy, hy, rfl⟩ := bigReg_wbar_rep hc hiff hb hb1
  obtain ⟨w', y', hwy', hy', rfl⟩ := bigReg_wbar_rep hc hiff hb' hb1'
  obtain ⟨k, hk⟩ := hgen (CaseM.spForm a y / CaseM.spForm a y') (div_ne_zero hy hy')
  refine ⟨k, ?_⟩
  have hform := bigReg_spForm_pow hν k y
  have hzy : CaseM.spForm a (SpExtras.mat n (GaloisField 2 f) (g ^ k) *ᵥ y) =
      CaseM.spForm a y' := by
    refine mul_left_cancel₀ (pow_ne_zero k hν0) ?_
    rw [hform, hk, div_mul_cancel₀ _ hy']
  have hu : (((⟨h, hhM⟩ : ↥M) ^ k * w * ((⟨h, hhM⟩ : ↥M) ^ k)⁻¹ : ↥M) : G) =
      ψG (SpExtras.mat n (GaloisField 2 f) (g ^ k) *ᵥ y) := by
    rw [hgk k y, ← hwy]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  have h1 := bigReg_mk_eq hc hiff hzy hu hwy'
  simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_inv] using h1

end Natural

end CFSG.RankThree.GF2n.Tim79a
