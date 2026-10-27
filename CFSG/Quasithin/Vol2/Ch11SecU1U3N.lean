module

public import CFSG.Quasithin.Vol2.Ch11SecU1U3D
public import CFSG.Quasithin.Vol2.Ch11SecU1U3G
public import CFSG.Quasithin.Vol2.Ch11SecU1U3M
public import CFSG.Quasithin.Vol2.Ch11SecU1U3C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.QuasithinUnique.Ch1 (transAut transAut_apply isInnerAut_of_transAut_mem_inner
  inner_of_sigma_id)
open CFSG.Quasithin.A312U3 (uniData)

variable {G : Type} [Group G] {L : Subgroup G} [L.Normal]

section Rep

variable {p : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p 1 F)

theorem exists_rep_bar_data (hp2 : p ≠ 2) (hC : Subgroup.centralizer (L : Set G) = ⊥)
    (ψh : ↥L ≃* hypPSU h 1 1) {t : G} (htL : t ∉ L) (ht2 : orderOf t = 2) :
    ∃ (A : GL (HypIndex 1 1) F) (σ : F ≃+* F)
      (hx : (⟨A, σ⟩ : SemiGL (HypIndex 1 1) F) ∈ semilinearSimilitudes h 1 1),
      A ∈ hypUnitary h 1 1 ∧ (∀ c, σ c = h.bar c) ∧
      (∃ c : F, c ≠ 0 ∧ (A : Matrix (HypIndex 1 1) (HypIndex 1 1) F) *
        (A : Matrix (HypIndex 1 1) (HypIndex 1 1) F).map h.bar = c • 1) ∧
      semilinearAutHom h (le_refl 1) (le_refl 1) ⟨_, hx⟩ = transAut ψh (MulAut.conjNormal t) := by
  set β : MulAut ↥L := MulAut.conjNormal t with hβ
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hβ2 : ∀ x, β (β x) = x := fun x => by
    rw [← MulAut.mul_apply, hβ, ← map_mul, htt, map_one, MulAut.one_apply]
  have hinner : ¬ CFSG.QuasithinUnique.Ch1.IsInnerAut β := fun hin =>
    htL (mem_of_isInnerAut hC hin)
  have hα1 : transAut ψh β ≠ 1 := fun h1 => hinner ⟨1, fun x => by
    have : β x = x := ψh.injective (by rw [← transAut_apply, h1, MulAut.one_apply])
    rw [this, inv_one, one_mul, mul_one]⟩
  have hord : orderOf (transAut ψh β) = 2 := orderOf_eq_prime
    (by rw [sq]; exact CFSG.QuasithinUnique.Ch1.transAut_mul_self ψh β hβ2) hα1
  obtain ⟨A, σ, hx, hA, hΦ, hσ, hid, hbar⟩ :=
    (odd_unitary_automorphism_semilinear_representation h hp2 (le_refl 1) (le_refl 1)
      (by norm_num)).2.2.2 _ hord
  rcases hσ with rfl | hσ
  · exfalso
    have hin := inner_of_sigma_id h hA hx (hid rfl)
    rw [hΦ] at hin
    exact hinner (isInnerAut_of_transAut_mem_inner ψh β hin)
  · obtain ⟨c, hc0, hAc⟩ := hbar hσ
    exact ⟨A, σ, hx, hA, hσ, ⟨c, hc0, hAc⟩, hΦ⟩

end Rep

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

theorem outer_sigma (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 2)
    (hC : Subgroup.centralizer (L : Set G) = ⊥) (ψ : PSU3F p F ≃* ↥L) :
    ∀ b : G, b ∉ L → orderOf b = 2 → SigmaFacts L b := by
  intro b hbL hb2
  have hLn : L.Normal := inferInstance
  obtain ⟨ψh⟩ := exists_hyp_equiv hF ψ
  obtain ⟨A, σ, hx, hA, hσ, ⟨c, hc0, hAc⟩, hΦ⟩ :=
    exists_rep_bar_data (uniData hF) (by omega) hC ψh hbL hb2
  obtain ⟨M, hM, hsimple, ⟨a₁, a₂, ha⟩, hcen⟩ :=
    exists_fixed_sigma (uniData hF) hp5 hA hc0 hAc hσ hx
  have hLb : L ⊓ Subgroup.centralizer ({b} : Set G) = M.map (embU ψh.symm) := by
    ext g
    constructor
    · rintro ⟨hgL, hgb⟩
      have hgb' : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.mp hgb
      refine ⟨ψh ⟨g, hgL⟩, (hM _).mpr ?_, ?_⟩
      · rw [hΦ, transAut_apply]
        congr 1
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        show b * g * b⁻¹ = g
        rw [← hgb', mul_inv_cancel_right]
      · show ((ψh.symm (ψh ⟨g, hgL⟩) : ↥L) : G) = g
        rw [MulEquiv.symm_apply_apply]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(ψh.symm y).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hα := (hM y).mp hy
      rw [hΦ, ← ψh.apply_symm_apply y, transAut_apply] at hα
      have h1 := congrArg Subtype.val (ψh.injective hα)
      rw [MulAut.conjNormal_apply] at h1
      show ((ψh.symm y : ↥L) : G) * b = b * ((ψh.symm y : ↥L) : G)
      calc ((ψh.symm y : ↥L) : G) * b = b * ((ψh.symm y : ↥L) : G) * b⁻¹ * b := by rw [h1]
        _ = b * ((ψh.symm y : ↥L) : G) := by rw [inv_mul_cancel_right]
  have hMle : ⁅M, M⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hx hy) (M.inv_mem hx)) (M.inv_mem hy)
  have hL₀ : (⁅M, M⁆).map (embU ψh.symm) = ⁅L ⊓ Subgroup.centralizer ({b} : Set G),
      L ⊓ Subgroup.centralizer ({b} : Set G)⁆ := by
    rw [hLb, Subgroup.map_commutator]
  set E := (⁅M, M⁆).equivMapOfInjective (embU ψh.symm) (embU_injective ψh.symm) with hE
  refine ⟨(⁅M, M⁆).map (embU ψh.symm), ?_, E.symm.isSimpleGroup,
    ⟨E a₁, E a₂, fun h12 => ha (E.injective (by rw [map_mul, map_mul, h12]))⟩, ?_, ?_⟩
  · rw [hLb]
    exact Subgroup.map_mono hMle
  · rw [hL₀]
    exact CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer _ _ _
      (centralizer_le_normalizer_inf hLn b) (centralizer_le_normalizer_inf hLn b)
  · rw [inf_centralizer_map_embU ψh.symm, hcen, Subgroup.map_bot]

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
