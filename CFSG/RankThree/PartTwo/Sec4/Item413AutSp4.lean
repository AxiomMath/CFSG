module

public import CFSG.RankThree.PartTwo.Sec4.Item413Classical
import CFSG.RankThree.PartTwo.Census.Classical.Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.QuasithinUnique.Lin2.Five (tauAut tauAut_mul_self frobAut)
open CFSG.Assembly.RankThreeEven (projSp)
open scoped Pointwise

theorem sq_mem_sup_of_normal_form {G : Type*} [Group G] {N C : Subgroup G} [hN : N.Normal]
    {t : G} (htC : ∀ c ∈ C, t * c = c * t) (ht2 : t * t ∈ C)
    (hG : ∀ g : G, ∃ n ∈ N, ∃ c ∈ C, ∃ ε : ℕ, ε ≤ 1 ∧ g = n * c * t ^ ε) (g : G) :
    g * g ∈ N ⊔ C := by
  obtain ⟨n, hn, c, hc, ε, hε, rfl⟩ := hG g
  have hnc : n * c ∈ N ⊔ C :=
    (N ⊔ C).mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hc)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one]
    exact (N ⊔ C).mul_mem hnc hnc
  · have h1 : t * n * t⁻¹ ∈ N := hN.conj_mem n hn t
    have h2 : t * c * t⁻¹ = c := by rw [htC c hc, mul_inv_cancel_right]
    have h3 : n * c * t ^ 1 * (n * c * t ^ 1) =
        n * c * ((t * n * t⁻¹) * (t * c * t⁻¹)) * (t * t) := by group
    rw [h3, h2]
    exact (N ⊔ C).mul_mem ((N ⊔ C).mul_mem hnc ((N ⊔ C).mul_mem (Subgroup.mem_sup_left h1)
      (Subgroup.mem_sup_right hc))) (Subgroup.mem_sup_right ht2)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem eq_one_of_proj_eq_one {s : StatedSp 2 F} (hs : proj 2 F s = 1) : s = 1 := by
  rw [proj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hs
  obtain ⟨c, hc⟩ := hs
  have hc2 : c ^ 2 = 1 := sq_of_scalar_mem_closure_sp (n := 2) (by norm_num) (by
    rw [hc]
    exact s.2)
  have hc1 : c = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have hc2' : (c : F) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hc2, Units.val_one]
    have : ((c : F) - 1) ^ 2 = 0 := by linear_combination hc2' + (1 - (c : F)) * h2
    exact Units.ext (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp this))
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

omit [Finite F] in
theorem conj_proj_injective :
    Function.Injective ((MulAut.conj : StatedProj (StatedSp 2 F) →* _).comp (proj 2 F)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hs
  have hcen : s ∈ Subgroup.center (StatedSp 2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 F)) => φ (proj 2 F g)) hs
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    have h2 : proj 2 F (s * g * s⁻¹ * g⁻¹) = 1 := by
      rw [map_mul, h1, map_inv, mul_inv_cancel]
    have h3 := eq_one_of_proj_eq_one h2
    calc g * s = s * g * s⁻¹ * g⁻¹ * (g * s) := by rw [h3, one_mul]
      _ = s * g := by group
  rw [CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num)] at hcen
  exact hcen

theorem card_le_27_of_mulAut_sp4 (B : Subgroup (MulAut (StatedProj (StatedSp 2 F))))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 27 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h3 : (3 : F) ≠ 0 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    intro h
    have : (1 : F) = 0 := by linear_combination h - h2
    exact one_ne_zero this
  set N := (conjAut 2 F).range
  set C := (fieldAut 2 F).range
  have hNn : N.Normal := range_conjAut_normal_of_charTwo
  obtain ⟨p, -, f, hp, hK⟩ := FiniteField.card' F
  have hcycK := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F
    (by rw [Nat.card_eq_fintype_card, hK])).2
  have hcyc : IsCyclic C :=
    isCyclic_of_surjective (fieldAut 2 F).rangeRestrict (fieldAut 2 F).rangeRestrict_surjective
  have hCN : C ≤ Subgroup.normalizer (N : Set (MulAut (StatedProj (StatedSp 2 F)))) :=
    fun c _ => mem_normalizer_of_conj_mem fun x hx => hNn.conj_mem x hx c
  have hsq := sq_mem_sup_of_normal_form (N := N) (C := C) (t := tauAut)
    (fun c hc => by
      obtain ⟨σ, rfl⟩ := hc
      exact tauAut_mul_fieldAut σ)
    ⟨frobAut F, tauAut_mul_self.symm⟩
    (fun g => by
      obtain ⟨A, σ, ε, hε, h⟩ := exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow g
      exact ⟨_, ⟨A, rfl⟩, _, ⟨σ, rfl⟩, ε, hε, h⟩)
  have hBNC : ∀ b ∈ B, ∃ n ∈ N, ∃ c ∈ C, b = n * c := by
    intro b hb
    have hb3 : b ^ 3 = 1 := hB.2 b hb
    have hbsup : b ∈ N ⊔ C := by
      have hb4 : b = (b * b) * (b * b) := by
        calc b = b ^ 3 * b := by rw [hb3, one_mul]
          _ = (b * b) * (b * b) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [hb4]
      exact (N ⊔ C).mul_mem (hsq b) (hsq b)
    have hmem : b ∈ (N : Set (MulAut (StatedProj (StatedSp 2 F)))) *
        (C : Set (MulAut (StatedProj (StatedSp 2 F)))) := by
      rw [← Subgroup.normal_mul]
      exact hbsup
    obtain ⟨n, hn, c, hc, hnc⟩ := Set.mem_mul.mp hmem
    exact ⟨n, hn, c, hc, hnc.symm⟩
  have h1 := card_le_three_mul_card_inf hB hcyc hCN hBNC
  set ψ := (MulAut.conj : StatedProj (StatedSp 2 F) →* _).comp (proj 2 F)
  have hψ : Function.Injective ψ := conj_proj_injective
  have hle : B ⊓ N ≤ ψ.range := by
    rintro α ⟨-, A, rfl⟩
    obtain ⟨y, hy⟩ := conjAut_mem_inner_of_charTwo A
    obtain ⟨s, rfl⟩ := proj_surjective y
    exact ⟨s, hy⟩
  set E := (B ⊓ N).comap ψ
  have hcardE : Nat.card E = Nat.card (B ⊓ N : Subgroup _) := by
    have h := Subgroup.card_map_of_injective (K := E) hψ
    rw [Subgroup.map_comap_eq_self hle] at h
    exact h.symm
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set E' := E.map (StatedSp 2 F).subtype
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (StatedSp 2 F).subtype_injective
  have hsq9 := card_sq_le_of_mem_closure_sp h3 E' (by rintro _ ⟨x, -, rfl⟩; exact x.2)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply hψ
      rw [map_mul, map_mul]
      exact hBc _ (Subgroup.mem_comap.mp hx).1 _ (Subgroup.mem_comap.mp hy).1)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := hψ (by rw [map_pow, map_one]; exact hB.2 _ (Subgroup.mem_comap.mp hx).1)
      rw [this, map_one])
  rw [show (3 : ℕ) ^ (2 * 2) = 81 by norm_num] at hsq9
  have h9 : Nat.card (B ⊓ N : Subgroup _) ≤ 9 := by
    rw [← hcardE, ← hcardE']
    nlinarith
  omega

theorem rankAutSp4_holds : ∀ n : ℕ, 1 ≤ n →
    CFSG.pRank 3 (MulAut (projSp 2 (GaloisField 2 n))) ≤ 3 := by
  intro n _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact pRank_three_le_of_card_le (card_le_of_mulEquiv_mulAut
    (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
      (StatedSp 2 (GaloisField 2 n))).symm card_le_27_of_mulAut_sp4)

end CFSG.RankThree.PartTwo.Sec4
