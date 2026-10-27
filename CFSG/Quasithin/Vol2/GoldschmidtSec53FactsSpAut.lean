module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsSpMod
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2X

public section

namespace CFSG.Quasithin.H13.Sec53F

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.SteinbergBS
  CFSG.QuasithinUnique.Fin257.Sp4 CFSG.Open CFSG.Quasithin CFSG.RankThree.PartOne.KCRootAxis
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.SpOut2 CFSG.Quasithin.H13.F431.SpModel
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2)

section Aut

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

abbrev StabRad (α : MulAut (antiSp F)) : Prop :=
  (∀ x, α x ∈ radA1 F ↔ x ∈ radA1 F) ∧ (∀ x, α x ∈ radA2 F ↔ x ∈ radA2 F)

theorem aut_form_both (hn : 2 ≤ n) (hK : Nat.card F = 2 ^ n) {α : MulAut (antiSp F)}
    (h : StabRad α) : ∃ g ∈ bor F, ∃ k : ℕ, α = MulAut.conj g * frobAut F ^ k := by
  obtain ⟨g, k, hgk⟩ := aut_form_antiSp hn hK α (Or.inl h.1)
  refine ⟨g, ?_, k, hgk⟩
  have hst : ∀ H : Subgroup (antiSp F), (∀ x, α x ∈ H ↔ x ∈ H) →
      (∀ x, (frobAut F ^ k) x ∈ H ↔ x ∈ H) → g ∈ Subgroup.normalizer (H : Set (antiSp F)) := by
    intro H hα hfr
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e : α ((frobAut F ^ k)⁻¹ y) = g * y * g⁻¹ := by
      rw [hgk, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.conj_apply]
    rw [← e, hα, ← hfr ((frobAut F ^ k)⁻¹ y), MulAut.apply_inv_self]
  have h1 := hst _ h.1 (frobAut_pow_mem_iff frobAut_mem_radA1_iff k)
  have h2 := hst _ h.2 (frobAut_pow_mem_iff frobAut_mem_radA2_iff k)
  rw [← (pCoreOf_inf_sp hn hK).1]
  exact ⟨h1, h2⟩

theorem frob_pow_mem_bor_iff (k : ℕ) (h : antiSp F) : (frobAut F ^ k) h ∈ bor F ↔ h ∈ bor F := by
  have hU := frobAut_pow_mem_antiUnipotent_iff (F := F) k
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro H y
    have := H ((frobAut F ^ k) y)
    rwa [hU, ← map_inv, ← map_mul, ← map_mul, hU] at this
  · intro H y
    obtain ⟨y', rfl⟩ := (frobAut F ^ k).surjective y
    have := H y'
    rw [← hU y', ← hU (h * y' * h⁻¹), map_mul, map_mul, map_inv] at this
    exact this

theorem conj_injective_sp (hn : 2 ≤ n) (hK : Nat.card F = 2 ^ n) :
    Function.Injective (MulAut.conj : antiSp F →* MulAut (antiSp F)) := by
  have hB := borel_antiSp (F := F) hn hK
  rw [injective_iff_map_eq_one]
  intro d hd
  apply hB.center_trivial d
  intro y
  have h := congrArg (fun φ : MulAut (antiSp F) => φ y) hd
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h

theorem isSolvable_of_stabRad (hn : 2 ≤ n) (hK : Nat.card F = 2 ^ n)
    (N : Subgroup (MulAut (antiSp F))) (h1 : ∀ α ∈ N, StabRad α) : Group.IsSolvable ↥N := by
  have hB := borel_antiSp (F := F) hn hK
  have hinj := conj_injective_sp (F := F) hn hK
  set inn : Subgroup (MulAut (antiSp F)) :=
    (bor F).map (MulAut.conj : antiSp F →* MulAut (antiSp F)) with hinn
  have hBs : Group.IsSolvable ↥(bor F) := isSolvable_bor hB.sylow.2.1
  have hinnS : Group.IsSolvable ↥inn :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective (bor F) _ hinj).symm.toMonoidHom)
      (Subgroup.equivMapOfInjective (bor F) _ hinj).symm.injective
  have hFr : frobAut F ∈ Subgroup.normalizer (inn : Set (MulAut (antiSp F))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [mulAut_conj_conj]
      exact ⟨frobAut F g, (frob_pow_mem_bor_iff 1 g).mpr hg, rfl⟩
    · rintro ⟨g, hg, hga⟩
      have hae : a = (frobAut F)⁻¹ * MulAut.conj g * (frobAut F)⁻¹⁻¹ := by
        rw [hga]
        group
      rw [hae, mulAut_conj_conj]
      refine ⟨(frobAut F)⁻¹ g, ?_, rfl⟩
      have := (frob_pow_mem_bor_iff 1 ((frobAut F)⁻¹ g)).mp
      rw [pow_one, MulAut.apply_inv_self] at this
      exact (frob_pow_mem_bor_iff 1 ((frobAut F)⁻¹ g)).mp (by simpa using hg)
  have hzp : Subgroup.zpowers (frobAut F) ≤ Subgroup.normalizer (inn : Set (MulAut (antiSp F))) :=
    Subgroup.zpowers_le.mpr hFr
  have hW : Group.IsSolvable ↥(inn ⊔ Subgroup.zpowers (frobAut F)) :=
    A3.isSolvable_sup_of_le_normalizer hzp
  have hle : N ≤ inn ⊔ Subgroup.zpowers (frobAut F) := by
    intro α hα
    obtain ⟨g, hg, k, hαk⟩ := aut_form_both hn hK (h1 α hα)
    rw [hαk]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨g, hg, rfl⟩)
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k))
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

omit [Finite F] [CharP F 2] in
theorem comm_conj_aut (φ : MulAut (antiSp F)) (g h : antiSp F) :
    MulAut.conj h * (MulAut.conj g * φ) * (MulAut.conj h)⁻¹ * (MulAut.conj g * φ)⁻¹ =
      MulAut.conj (h * g * (φ h)⁻¹ * g⁻¹) := by
  have e1 : MulAut.conj h * (MulAut.conj g * φ) * (MulAut.conj h)⁻¹ * (MulAut.conj g * φ)⁻¹ =
      MulAut.conj h * MulAut.conj g * (φ * (MulAut.conj h)⁻¹ * φ⁻¹) * (MulAut.conj g)⁻¹ := by
    group
  have e2 : φ * (MulAut.conj h)⁻¹ * φ⁻¹ = MulAut.conj (φ h)⁻¹ := by
    rw [← map_inv, mulAut_conj_conj, map_inv]
  rw [e1, e2]
  simp only [map_mul, map_inv]

theorem pCoreOf_le_innU (hn : 2 ≤ n) (hK : Nat.card F = 2 ^ n)
    (N : Subgroup (MulAut (antiSp F))) (h1 : ∀ α ∈ N, StabRad α)
    (h2 : ∀ h ∈ bor F, (MulAut.conj h : MulAut (antiSp F)) ∈ N) :
    pCoreOf 2 N ≤ (antiUnipotent F).map (MulAut.conj : antiSp F →* MulAut (antiSp F)) := by
  have hinj := conj_injective_sp (F := F) hn hK
  have hRn : N ≤ Subgroup.normalizer (pCoreOf 2 N : Set (MulAut (antiSp F))) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
  have hR2 : IsPGroup 2 (pCoreOf 2 N) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  intro α hα
  have hαN : α ∈ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N hα
  obtain ⟨g, hg, k, hαk⟩ := aut_form_both hn hK (h1 α hαN)
  obtain ⟨b, hb⟩ := hR2 ⟨α, hα⟩
  have hαb : α ^ 2 ^ b = 1 := congrArg Subtype.val hb
  have hFr : frobAut F ^ k = 1 := by
    apply frobAut_pow_eq_one_of_fix
    intro y
    by_cases hy : y = 0
    · rw [hy, zero_pow (pow_ne_zero k two_ne_zero)]
    set s : Fˣ := Units.mk0 y hy with hs
    have hh : dSp s 1 ∈ bor F := dSp_mem_normalizer s 1
    have hc : (MulAut.conj (dSp s 1) : MulAut (antiSp F)) ∈ N := h2 _ hh
    have hγ : MulAut.conj (dSp s 1) * α * (MulAut.conj (dSp s 1))⁻¹ * α⁻¹ ∈ pCoreOf 2 N := by
      have := (Subgroup.mem_normalizer_iff.mp (hRn hc) α).mp hα
      exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ hα)
    rw [hαk, comm_conj_aut] at hγ
    obtain ⟨a, ha⟩ := hR2 ⟨_, hγ⟩
    have hxa : (dSp s 1 * g * ((frobAut F ^ k) (dSp s 1))⁻¹ * g⁻¹) ^ 2 ^ a = 1 := by
      apply hinj
      rw [map_pow, map_one]
      exact congrArg Subtype.val ha
    have hφh : (frobAut F ^ k) (dSp s 1) ∈ bor F := (frob_pow_mem_bor_iff k _).mpr hh
    have hx : dSp s 1 * g * ((frobAut F ^ k) (dSp s 1))⁻¹ * g⁻¹ ∈ bor F :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hg)
        (Subgroup.inv_mem _ hφh)) (Subgroup.inv_mem _ hg)
    have hxU := mem_U_of_pow_eq_one hx hxa
    have hraw : (dSp s 1 * g * ((frobAut F ^ k) (dSp s 1))⁻¹ * g⁻¹) * g *
        (frobAut F ^ k) (dSp s 1) = dSp s 1 * g := by group
    have hrel : (⟨_, hx⟩ : ↥(bor F)) * ⟨g, hg⟩ * ⟨_, hφh⟩ = ⟨_, hh⟩ * ⟨g, hg⟩ :=
      Subtype.ext hraw
    have hd := congrArg (dgHom F 0) hrel
    rw [map_mul, map_mul, map_mul] at hd
    have hx0 : dgHom F 0 ⟨_, hx⟩ = 1 := glMat_diag_of_mem_U hxU 0
    have hg0 : dgHom F 0 ⟨g, hg⟩ ≠ 0 := (upper_diag_ne_zero (upper_of_mem_normalizer hg)).1
    rw [hx0, one_mul] at hd
    have hcancel := mul_left_cancel₀ hg0 (hd.trans (mul_comm _ _))
    have hφ0 : dgHom F 0 ⟨_, hφh⟩ = (s : F) ^ 2 ^ k := by
      have := mat_frobAut_pow (F := F) k (dSp s 1)
      have h00 := congrFun (congrFun this 0) 0
      simpa [dgHom_apply, (glMat_dSp_diag (F := F) s 1).1] using h00
    have hs0 : dgHom F 0 ⟨_, hh⟩ = (s : F) := (glMat_dSp_diag (F := F) s 1).1
    rw [hφ0, hs0] at hcancel
    simpa [hs] using hcancel
  rw [hFr, mul_one] at hαk
  rw [hαk] at hαb
  have hgb : g ^ 2 ^ b = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact hαb
  exact ⟨g, mem_U_of_pow_eq_one hg hgb, hαk.symm⟩

end Aut

end CFSG.Quasithin.H13.Sec53F
