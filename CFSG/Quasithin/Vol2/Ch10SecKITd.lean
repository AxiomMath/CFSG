module

public import CFSG.Quasithin.Vol2.Ch10SecKITc
public import CFSG.Quasithin.Vol2.Ch1List
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch10SecFAct

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF

variable {G : Type} [Group G] [Finite G] {M T L X : Subgroup G} {n : ℕ}

theorem IsNatBlock.false_of_surj (h : IsNatBlock X n) (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (φ : ↥X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hφ : Function.Surjective φ) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := hφ (-1)
  set N : Subgroup G := φ.ker.map X.subtype with hNdef
  have hNX : N ≤ X := Subgroup.map_subtype_le _
  have hNn : X ≤ Subgroup.normalizer (N : Set G) := by
    have hk : (φ.ker).Normal := inferInstance
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨⟨g, hg⟩ * y' * ⟨g, hg⟩⁻¹, hk.conj_mem y' hy' ⟨g, hg⟩, by simp⟩
    · rintro ⟨y', hy', hy⟩
      refine ⟨⟨g, hg⟩⁻¹ * y' * (⟨g, hg⟩ : ↥X)⁻¹⁻¹, hk.conj_mem y' hy' _, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hy ⊢
      rw [hy]
      group
  have hcen : ∀ x ∈ X, (c : G) * x * (c : G)⁻¹ * x⁻¹ ∈ N := by
    intro x hx
    refine ⟨c * ⟨x, hx⟩ * c⁻¹ * (⟨x, hx⟩ : ↥X)⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    simp
  obtain ⟨c', hc', hcc⟩ := h.mem_of_central_mod hn hNX hNn c.2 hcen
  have hcc' : c' = c := Subtype.ext hcc
  rw [hcc', SetLike.mem_coe, MonoidHom.mem_ker, hc] at hc'
  have : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
    (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) hc'
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at h1
  exact ZMod.neg_one_ne_one h1

theorem xbar_mem_lFamily (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M) (hX : X ∈ lFamily T)
    (hXL : X ≤ L) :
    modO2Image L X ∈
      lFamily (((T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) := by
  have hLsyl : IsSylowTwoOf (T ⊓ L) L :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hL) hT
  have hX' : X ∈ lFamily (T ⊓ L) :=
    cComp_mem_of_le (show X ∈ cComp (X ⊔ T) from hX) le_sup_left (sup_le_sup_left inf_le_left X)
  exact modO2Image_mem_lFamily hLsyl hXL hX'

omit [Finite G] in
theorem le_sup_of_xbar_le {X₁ X₂ : Subgroup G} (hX₁ : X₁ ≤ L)
    (hle : modO2Image L X₁ ≤ modO2Image L X₂) : X₁ ≤ X₂ ⊔ pCoreOf 2 L := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hle ⟨⟨x, hX₁ hx⟩, hx, rfl⟩
  have h1 : y⁻¹ * ⟨x, hX₁ hx⟩ ∈ CFSG.pCore 2 ↥L := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
    exact hyx
  have h2 : ((y⁻¹ * ⟨x, hX₁ hx⟩ : ↥L) : G) ∈ pCoreOf 2 L :=
    (C1Pack.coe_mem_pCoreOf_iff L _).mpr h1
  have e : x = (y : G) * ((y⁻¹ * ⟨x, hX₁ hx⟩ : ↥L) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy))
    (Subgroup.mem_sup_right h2)

theorem perfectCore_sup_eq (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M) (hX : X ∈ lFamily T)
    (hXL : X ≤ L) : perfectCore (X ⊔ pCoreOf 2 L) = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hXL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  exact perfectCore_eq_of_le_sup hXQ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    (perfect_of_mem_cComp (show X ∈ cComp (X ⊔ T) from hX)) le_sup_left le_rfl
    (sup_le Subgroup.le_normalizer (pCoreOf_le_normalizer hT hL hX hXL))

theorem xbar_ne {X₁ X₂ : Subgroup G} (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M)
    (hX₁ : X₁ ∈ lFamily T) (hX₂ : X₂ ∈ lFamily T) (hne : X₁ ≠ X₂) (hX₁L : X₁ ≤ L)
    (hX₂L : X₂ ≤ L) : modO2Image L X₁ ≠ modO2Image L X₂ := by
  intro heq
  apply hne
  have h1 : X₁ ⊔ pCoreOf 2 L = X₂ ⊔ pCoreOf 2 L :=
    le_antisymm (sup_le (le_sup_of_xbar_le hX₁L heq.le) le_sup_right)
      (sup_le (le_sup_of_xbar_le hX₂L heq.ge) le_sup_right)
  rw [← perfectCore_sup_eq hT hL hX₁ hX₁L, ← perfectCore_sup_eq hT hL hX₂ hX₂L, h1]

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
