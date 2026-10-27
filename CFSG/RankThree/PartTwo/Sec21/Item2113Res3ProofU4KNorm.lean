module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofU4KDefs
public import CFSG.RankThree.PartOne.KF.U4Perm
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (torusSU mem_torusSU_iff diagU diagU_val diagU_pow diagU_one
  diagU_injective det_diagU exists_diagU_of_isDiag ent NormPerm exists_perm_of_normalizes
  isDiag_of_mem_torusSU torus_char_distinct exists_isPrimitiveRoot)

theorem exists_three_cycle : ∀ σ : Equiv.Perm (Fin 4), σ * σ * σ = 1 → σ ≠ 1 →
    ∃ a e : Fin 4, σ e = e ∧ ∀ i, i ≠ e → i = a ∨ i = σ a ∨ i = σ (σ a) := by
  decide

theorem eq_ite_of_three_cycle {K : Type} [Field K] {σ : Equiv.Perm (Fin 4)} {a e : Fin 4}
    (hcover : ∀ i, i ≠ e → i = a ∨ i = σ a ∨ i = σ (σ a)) {d : Fin 4 → Kˣ}
    (hd : ∀ i, d (σ i) = d i) (hd3 : ∀ i, d i ^ 3 = 1) (hdp : ∏ i, d i = 1) (i : Fin 4) :
    d i = if i = e then 1 else d a := by
  classical
  have hconst : ∀ j, j ≠ e → d j = d a := by
    intro j hj
    rcases hcover j hj with rfl | rfl | rfl
    · rfl
    · exact hd a
    · exact (hd (σ a)).trans (hd a)
  have he : d e = 1 := by
    have h1 := Finset.mul_prod_erase Finset.univ d (Finset.mem_univ e)
    have h2 : ∏ j ∈ Finset.univ.erase e, d j = ∏ _j ∈ Finset.univ.erase e, d a :=
      Finset.prod_congr rfl fun j hj => hconst j (Finset.ne_of_mem_erase hj)
    rw [hdp, h2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ e),
      Finset.card_univ, Fintype.card_fin, show 4 - 1 = 3 from rfl, hd3 a, mul_one] at h1
    exact h1
  split_ifs with hi
  · rw [hi, he]
  · exact hconst i hi

variable {f : ℕ} {K : Type} [Field K]

theorem le_torusSU_of_le_normalizer (hU : UnitaryFieldData 2 f K) (hpq : 3 ∣ 2 ^ f + 1)
    {F : Subgroup (GL (Fin 4) K)} (hFU : F ≤ unitarySU 2 f K 4)
    (hFe : CFSG.Assembly.IsElemAbelian 3 F) (hF27 : 3 ^ 3 ≤ Nat.card F)
    (hFN : F ≤ Subgroup.normalizer (torusSU 3 4 K : Set (GL (Fin 4) K))) :
    F ≤ torusSU 3 4 K := by
  classical
  have hfinK := hU.finite
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hU Nat.prime_three hpq
  have hz0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζu : IsPrimitiveRoot (Units.mk0 ζ hz0) 3 :=
    IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  have hdist : ∀ i j : Fin 4, i ≠ j → ∃ x ∈ torusSU 3 4 K, ent x i i ≠ ent x j j :=
    fun i j hij => torus_char_distinct hζu.pow_eq_one
      (hζu.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)) i j hij
  have hconj : ∀ g ∈ F, ∀ x ∈ torusSU 3 4 K, g * x * g⁻¹ ∈ torusSU 3 4 K := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hFN hg) x).mp hx
  have hconj' : ∀ g ∈ F, ∀ x ∈ torusSU 3 4 K, g⁻¹ * x * g ∈ torusSU 3 4 K := fun g hg x hx => by
    simpa using hconj g⁻¹ (F.inv_mem hg) x hx
  have hex : ∀ g : F, ∃ τ : Equiv.Perm (Fin 4),
      (∀ i k, ent (g : GL (Fin 4) K) k i ≠ 0 → k = τ i) ∧ NormPerm 3 (g : GL (Fin 4) K) τ := by
    intro g
    obtain ⟨τ, -, hmono, hτ⟩ := exists_perm_of_normalizes (torusSU 3 4 K)
      (fun x hx => isDiag_of_mem_torusSU hx) hdist (hconj g g.2) (hconj' g g.2)
    exact ⟨τ, hmono, hconj g g.2, hτ⟩
  choose σ hmono hσ using hex
  have huniq : ∀ (g : F) (τ : Equiv.Perm (Fin 4)), NormPerm 3 (g : GL (Fin 4) K) τ → σ g = τ :=
    fun g τ hτ => NormPerm.eq_of_conj_eq hdist (hσ g) hτ fun _ _ => rfl
  let ρ : F →* Equiv.Perm (Fin 4) :=
    { toFun := σ
      map_one' := huniq 1 1 NormPerm.one
      map_mul' := fun g h => huniq (g * h) _ ((hσ g).mul (hσ h)) }
  have hρ : ∀ g : F, ρ g = σ g := fun _ => rfl
  have hF3 : ∀ g : F, g ^ 3 = 1 := fun g => Subtype.ext (hFe.2 _ g.2)
  have hker : ∀ g : F, σ g = 1 → (g : GL (Fin 4) K) ∈ torusSU 3 4 K := by
    intro g hg1
    have hdiag : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag := by
      intro i k hik
      by_contra hne
      have h1 := hmono g k i hne
      rw [hg1, Equiv.Perm.one_apply] at h1
      exact hik h1
    obtain ⟨d, hd⟩ := exists_diagU_of_isDiag hdiag
    refine mem_torusSU_iff.mpr ⟨d, fun i => ?_, ?_, hd⟩
    · have h1 : diagU (d ^ 3) = (1 : GL (Fin 4) K) := by
        rw [← diagU_pow, hd]
        exact hFe.2 _ g.2
      exact congrFun (diagU_injective (h1.trans diagU_one.symm)) i
    · have hdet := ((mem_unitarySU_iff hU).mp (hFU g.2)).1
      rw [← hd, det_diagU] at hdet
      exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact hdet)
  by_contra hFT
  obtain ⟨g₀, hg₀⟩ : ∃ g : F, σ g ≠ 1 := by
    by_contra h
    push Not at h
    exact hFT fun x hx => hker ⟨x, hx⟩ (h ⟨x, hx⟩)
  have hrange : Nat.card ρ.range ≤ 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hp : IsPGroup 3 ρ.range := by
      rintro ⟨x, g, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      change ρ g ^ 3 ^ 1 = 1
      rw [pow_one, ← map_pow, hF3, map_one]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have hdvd : Nat.card ρ.range ∣ 24 := by
      have h1 := Subgroup.card_subgroup_dvd_card ρ.range
      rw [Nat.card_perm, Nat.card_fin] at h1
      exact h1
    rw [hk] at hdvd ⊢
    have hk2 : k < 2 := by
      by_contra hk2
      push Not at hk2
      have h1 : 3 ^ 2 ∣ 24 := (pow_dvd_pow 3 hk2).trans hdvd
      norm_num at h1
    interval_cases k <;> norm_num
  have hσ3 : σ g₀ * σ g₀ * σ g₀ = 1 := by
    rw [← hρ, ← map_mul, ← map_mul, ← pow_three', hF3, map_one]
  obtain ⟨a, e, -, hcover⟩ := exists_three_cycle (σ g₀) hσ3 hg₀
  have hkerle : Nat.card ρ.ker ≤ 3 := by
    have hd : ∀ t : ρ.ker, ∃ d : Fin 4 → Kˣ, (∀ i, d i ^ 3 = 1) ∧ ∏ i, d i = 1 ∧
        diagU d = ((t : F) : GL (Fin 4) K) :=
      fun t => mem_torusSU_iff.mp (hker t (MonoidHom.mem_ker.mp t.2))
    choose d hd3 hdp hdt using hd
    have hfix : ∀ t : ρ.ker, ∀ i, d t (σ g₀ i) = d t i := by
      intro t i
      have hc : (g₀ : GL (Fin 4) K) * ((t : F) : GL (Fin 4) K) =
          ((t : F) : GL (Fin 4) K) * g₀ := congrArg Subtype.val (hFe.1.is_comm.comm g₀ (t : F))
      have h1 := (hσ g₀).2 _ (hker t (MonoidHom.mem_ker.mp t.2)) i
      rw [hc, mul_inv_cancel_right, ← hdt t] at h1
      simp only [ent, diagU_val, Matrix.diagonal_apply_eq] at h1
      exact Units.ext h1
    let κ : ρ.ker → rootsOfUnity 3 K := fun t => ⟨d t a, (mem_rootsOfUnity 3 _).mpr (hd3 t a)⟩
    have hκ : Function.Injective κ := by
      intro t t' htt'
      have ha : d t a = d t' a := congrArg Subtype.val htt'
      have hdd : d t = d t' := funext fun i => by
        rw [eq_ite_of_three_cycle hcover (hfix t) (hd3 t) (hdp t) i,
          eq_ite_of_three_cycle hcover (hfix t') (hd3 t') (hdp t') i, ha]
      apply Subtype.ext
      apply Subtype.ext
      rw [← hdt t, ← hdt t', hdd]
    exact (Nat.card_le_card_of_injective κ hκ).trans (card_rootsOfUnity K 3)
  have hcard := Subgroup.card_ker_mul_card_range ρ
  have h9 : Nat.card F ≤ 9 := by
    rw [← hcard]
    exact Nat.mul_le_mul hkerle hrange
  omega

theorem item2115U4KTorusE27_holds : Item2115U4KTorusE27 := by
  intro f K _ hU _ hpq F hFU hFe hF27 hFN
  exact le_torusSU_of_le_normalizer hU hpq hFU hFe hF27 hFN

end CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof
