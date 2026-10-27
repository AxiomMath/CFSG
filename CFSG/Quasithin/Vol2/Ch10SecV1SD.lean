module

public import CFSG.Quasithin.Vol2.Ch10SecV1SA
public import CFSG.Quasithin.Vol2.KGNatComm

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C.A319

open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {H : Type} [Group H] {L : Subgroup H} {K : Type} [Field K]

theorem commutant_SL3 (T : (Fin 3 → K) →+ (Fin 3 → K))
    (hT : ∀ (γ : ↥(StatedSL 3 K)) (x : Fin 3 → K),
      T (((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) =
        ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ T x) :
    ∃ a : K, ∀ x, T x = a • x :=
  KGNat.commutant_statedSL (by norm_num) T fun γ x => by
    rw [KGNat.linModelNat_lin, KGNat.linModelNat_lin]
    exact hT γ x

namespace NatCoord

variable {φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)} {I : Subgroup H}

theorem conj_mem {g : H} (hgL : g ∈ Subgroup.normalizer (L : Set H)) (l : ↥L) :
    g⁻¹ * (l : H) * g ∈ L := by
  simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgL) l).mp l.2

theorem cact_inv_mat (c : NatCoord φ I) {g : H} (hg : g ∈ Subgroup.normalizer (I : Set H))
    (hgL : g ∈ Subgroup.normalizer (L : Set H)) (l : ↥L) (x : Fin 3 → K) :
    c.cact g⁻¹ (Subgroup.inv_mem _ hg) (mat φ l *ᵥ x) =
      mat φ ⟨_, conj_mem hgL l⟩ *ᵥ c.cact g⁻¹ (Subgroup.inv_mem _ hg) x := by
  rw [← c.cact_of_mem l, ← c.cact_of_mem ⟨_, conj_mem hgL l⟩, ← c.cact_mul, ← c.cact_mul]
  exact c.cact_congr (by group) _ _ x

theorem exists_semilinear (c : NatCoord φ I) {g : H} (hg : g ∈ Subgroup.normalizer (I : Set H))
    (hgL : g ∈ Subgroup.normalizer (L : Set H)) :
    ∃ σ : K →+* K, ∀ (a : K) (x : Fin 3 → K), c.cact g hg (a • x) = σ a • c.cact g hg x := by
  set T := c.cact g hg with hT
  set T' := c.cact g⁻¹ (Subgroup.inv_mem _ hg) with hT'
  have hTT' : ∀ x, T (T' x) = x := c.cact_cact_inv g hg
  have hT'T : ∀ x, T' (T x) = x := c.cact_inv_cact g hg
  have hsc : ∀ a : K, ∃ b : K, ∀ x, T (a • T' x) = b • x := by
    intro a
    let S : (Fin 3 → K) →+ (Fin 3 → K) :=
      { toFun := fun x => T (a • T' x)
        map_zero' := by
          have h0 := c.cact_add g⁻¹ (Subgroup.inv_mem _ hg) 0 0
          have h1 := c.cact_add g hg 0 0
          rw [add_zero] at h0 h1
          rw [← hT'] at h0
          rw [← hT] at h1
          rw [show T' 0 = 0 from (add_eq_left.mp h0.symm), smul_zero,
            show T 0 = 0 from (add_eq_left.mp h1.symm)]
        map_add' := fun x y => by
          show T (a • T' (x + y)) = T (a • T' x) + T (a • T' y)
          rw [hT', c.cact_add, smul_add, hT, c.cact_add] }
    refine commutant_SL3 S fun γ x => ?_
    obtain ⟨l, hl⟩ := exists_mat φ γ
    rw [← hl]
    show T (a • T' (mat φ l *ᵥ x)) = mat φ l *ᵥ T (a • T' x)
    rw [hT', cact_inv_mat c hg hgL, ← Matrix.mulVec_smul, ← c.cact_of_mem, hT, ← c.cact_mul,
      ← c.cact_of_mem, ← c.cact_mul]
    exact c.cact_congr (by group) _ _ _
  choose σf hσf using hsc
  have hx₀ : (Pi.single 0 1 : Fin 3 → K) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hinj : ∀ a b : K, a • (Pi.single 0 1 : Fin 3 → K) = b • Pi.single 0 1 → a = b :=
    fun a b h => smul_left_injective K hx₀ h
  have hσ1 : σf 1 = 1 := hinj _ _ (by rw [← hσf, one_smul, hTT', one_smul])
  have hσadd : ∀ a b, σf (a + b) = σf a + σf b := fun a b => hinj _ _ (by
    rw [← hσf, add_smul, hT, c.cact_add, ← hT, hσf, hσf, add_smul])
  have hσmul : ∀ a b, σf (a * b) = σf a * σf b := fun a b => hinj _ _ (by
    rw [← hσf, mul_smul, mul_smul, ← hσf b, ← hσf a, hT'T])
  have hσ0 : σf 0 = 0 := by
    have h := hσadd 0 0
    rw [add_zero] at h
    exact add_eq_left.mp h.symm
  let σ : K →+* K :=
    { toFun := σf
      map_one' := hσ1
      map_mul' := hσmul
      map_zero' := hσ0
      map_add' := hσadd }
  refine ⟨σ, fun a x => ?_⟩
  show T (a • x) = σf a • T x
  rw [← hσf, hT'T]

end NatCoord

end CFSG.Quasithin.Vol2.Ch10.V1C.A319
