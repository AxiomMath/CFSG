module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUNormal
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUDict
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUFixSemi
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUFixThree
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelConj
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUAut
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidM

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK

open Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ComponentClassification.RankTwoClassical (hform)

variable {m n : ℕ} {F : Type} [Field F] [Finite F]

theorem mem_range_conj_of_fix_conj_iff_commute_statedProjSU (hF : Nat.card F = (2 ^ n) ^ 2)
    (hn : 1 < n) (hm : 3 ≤ m) {t₀ : StatedProj (StatedSU m (2 ^ n) F)}
    (ht : IsUnitaryTransvectionIn m n t₀)
    (α : MulAut (StatedProj (StatedSU m (2 ^ n) F))) (g : StatedProj (StatedSU m (2 ^ n) F))
    (hα2 : α * α = 1) (hg : g * g = 1) (hα : α t₀ = t₀)
    (hfix : ∀ s : StatedProj (StatedSU m (2 ^ n) F),
      α (s * t₀ * s⁻¹) = s * t₀ * s⁻¹ ↔ g * (s * t₀ * s⁻¹) = s * t₀ * s⁻¹ * g) :
    α ∈ (MulAut.conj : StatedProj (StatedSU m (2 ^ n) F) →*
      MulAut (StatedProj (StatedSU m (2 ^ n) F))).range := by
  have h : UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, Nat.mul_comm n 2]⟩
  haveI : CharP F 2 := h.charP
  have hq : ¬(m = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨-, h2⟩
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨a, c, N₀, ha, haa, hc0, hc, hN₀, rfl⟩ := borel86_un_exists_eq_mk h ht
  by_cases hg1 : g = 1
  · subst hg1
    haveI : IsSimpleGroup (StatedProj (StatedSU m (2 ^ n) F)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 n hF m hm
        fun h3 => hq (Prod.mk.inj h3)
    have h1 : α = 1 := borel86_conj_eq_one_of_forall_fix (borel86_un_ne_one h ht) α
      fun s => (hfix s).mpr (by rw [one_mul, mul_one])
    exact ⟨1, by rw [h1, map_one]⟩
  · obtain ⟨G, rfl, hG⟩ := borel86_ud_exists_lift h (by omega) hg
    have hG1 : G ≠ 1 := fun h1 => hg1 (by rw [h1]; rfl)
    obtain ⟨σ, A, hA, hαA⟩ :=
      CFSG.ComponentClassification.RankTwoClassical.exists_unitary_semilinear_statedProj h hm hq α
    have hdict : ∀ u : Fin m → F, u ≠ 0 → hform h.bar u u = 0 → ∀ b : F, b ≠ 0 → h.bar b = b →
        ((∃ κ : F, (A : Matrix (Fin m) (Fin m) F) *ᵥ (σ ∘ u) = κ • u ∧
          σ b * (h.bar κ * κ) = b) ↔ (G : GL (Fin m) F).val *ᵥ u = u) := by
      intro u hu huu b hb0 hb
      obtain ⟨N, hN⟩ :=
        CFSG.ComponentClassification.RankTwoClassical.URigid.exists_one_add_mem h huu hb
      obtain ⟨S, hS⟩ := borel86_un_exists_conj h hm ha haa hu huu hc0 hc hb0 hb hN₀ hN
      have hs : (QuotientGroup.mk S : StatedProj (StatedSU m (2 ^ n) F)) * QuotientGroup.mk N₀ *
          (QuotientGroup.mk S)⁻¹ = QuotientGroup.mk N := by
        rw [← hS, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have key := hfix (QuotientGroup.mk S)
      rw [hs] at key
      rw [← borel86_ud_fix_iff h hA hαA hu huu hb0 hN,
        ← borel86_ud_commute_iff h hG hu huu hb0 hN]
      exact key
    have hGa : (G : GL (Fin m) F).val *ᵥ a = a :=
      (hdict a ha haa c hc0 hc).mp ((borel86_ud_fix_iff h hA hαA ha haa hc0 hN₀).mp hα)
    rcases borel86_ufs_refl_or_bar h ha (fun b hb0 hb => (hdict a ha haa b hb0 hb).mpr hGa)
      with rfl | hσ
    · exact borel86_ufs_mem_range_conj_of_refl h hA hαA hα2
    · exfalso
      have hσu : ∀ u : Fin m → F, σ ∘ u = h.bar ∘ u := fun u => funext fun i => hσ (u i)
      rcases Nat.lt_or_ge m 4 with hm4 | hm4
      · obtain rfl : m = 3 := by omega
        have hAA := borel86_uft_mul_map_bar_eq_one_of_sq h (by norm_num) hσ hA hαA hα2
        refine borel86_uft_false h hA hAA hG hG1 fun u hu huu hAu => ?_
        refine (hdict u hu huu 1 one_ne_zero (map_one h.bar)).mp ⟨1, ?_, ?_⟩
        · rw [hσu u, hAu, one_smul]
        · simp
      · refine borel86_ufs_false_of_bar h hm4 hG hG1 A fun u hu huu hGu => ?_
        obtain ⟨κ, hκ, -⟩ := (hdict u hu huu 1 one_ne_zero (map_one h.bar)).mpr hGu
        exact ⟨κ, by rw [← hσu u]; exact hκ⟩

end CFSG.LocalAnalysis.WeakClosure81

end
