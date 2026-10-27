module

public import CFSG.LocalAnalysis.WeakClosure81.NineTwoE
public import CFSG.LocalAnalysis.WeakClosure81.NineThirteenAux
public import CFSG.LocalAnalysis.WeakClosure81.NineMinimalI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T X : Subgroup G}

theorem coe_sup_eq_mul_of_mul_eq_mul {A B : Subgroup G} (hAB : (A : Set G) * B = B * A) :
    ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * B := by
  let S : Subgroup G :=
    { carrier := (A : Set G) * B
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro a b ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        have hba : b₁ * a₂ ∈ (B : Set G) * (A : Set G) := ⟨b₁, hb₁, a₂, ha₂, rfl⟩
        rw [← hAB] at hba
        obtain ⟨a₃, ha₃, b₃, hb₃, hba_eq⟩ := hba
        refine ⟨a₁ * a₃, A.mul_mem ha₁ ha₃, b₃ * b₂, B.mul_mem hb₃ hb₂, ?_⟩
        calc
          (a₁ * a₃) * (b₃ * b₂) = a₁ * (a₃ * b₃) * b₂ := by group
          _ = a₁ * (b₁ * a₂) * b₂ := by rw [show a₃ * b₃ = b₁ * a₂ from hba_eq]
          _ = (a₁ * b₁) * (a₂ * b₂) := by group
      inv_mem' := by
        rintro a ⟨x, hx, y, hy, rfl⟩
        have hyx : y⁻¹ * x⁻¹ ∈ (B : Set G) * (A : Set G) :=
          ⟨y⁻¹, B.inv_mem hy, x⁻¹, A.inv_mem hx, rfl⟩
        rw [← hAB] at hyx
        obtain ⟨x', hx', y', hy', hyx_eq⟩ := hyx
        exact ⟨x', hx', y', hy', by rw [hyx_eq]; group⟩ }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun x hx => ⟨x, hx, 1, B.one_mem, mul_one x⟩)
      (fun y hy => ⟨1, A.one_mem, y, hy, one_mul y⟩)
  refine le_antisymm (fun g hg => hle hg) ?_
  rintro g ⟨x, hx, y, hy, rfl⟩
  exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)

theorem card_inf_lt_card_of_not_le {A B : Subgroup G} (h : ¬ B ≤ A) :
    Nat.card ↥(A ⊓ B) < Nat.card ↥B := by
  refine lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_right) fun hcard => h ?_
  have heq : A ⊓ B = B :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq hcard.symm)
  exact heq ▸ inf_le_left

theorem nine_thirteen (h9 : Hyp9 V T) (h93 : Thm93 V T) (hX : X ∈ calP V)
    (hXT : (X : Set G) * T = T * X) :
    normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G) ∨
      X ⊔ T ≤ normalizer (E3.wClos V 0 T : Set G) := by
  by_cases h1 : normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G)
  · exact Or.inl h1
  refine Or.inr ?_
  have hTW : T ≤ normalizer (E3.wClos V 0 T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) T)
  suffices key : ∀ n : ℕ, ∀ Y : Subgroup G, Nat.card Y = n → Y ∈ calP V →
      (Y : Set G) * T = T * Y → Y ⊔ T ≤ normalizer (E3.wClos V 0 T : Set G) from
    key _ X rfl hX hXT
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y hn hY hYT
    by_contra hKW
    have hYcalP : Y ∈ calP V := hY
    have hY1 : Y ≠ ⊥ := by
      rintro rfl
      exact hKW (by rw [bot_sup_eq]; exact hTW)
    have hmin : ∀ K₀ : Subgroup G, T ≤ K₀ → K₀ < Y ⊔ T →
        K₀ ≤ normalizer (E3.wClos V 0 T : Set G) := by
      intro K₀ hTK hlt
      obtain ⟨hsup, hperm⟩ := exists_inf_sup_of_le_sup hYT hTK hlt.le
      have hY₀ : K₀ ⊓ Y ∈ calP V := calP_mono hY inf_le_right
      have hcard : Nat.card ↥(K₀ ⊓ Y) < n := by
        rw [← hn]
        refine card_inf_lt_card_of_not_le fun hYK => ?_
        exact (sup_le hYK hTK).not_gt hlt
      have := ih _ hcard (K₀ ⊓ Y) rfl hY₀ hperm
      rwa [hsup] at this
    obtain ⟨p, hp, hp2, hYp, hYM, -, -⟩ := hY
    have hK1 : Nine1Hyp V (Y ⊔ T) T Y p :=
      nine1Hyp_of_minimal hp hp2 hYp hYM h9.sylow.isPGroup h9.sylow.le hYT hTW hKW hmin
    have hK2 : Nine2Hyp V (Y ⊔ T) T Y p :=
      ⟨hK1, hYcalP, hKW, commutator_cClos_ne_bot_of_not_normalizer_le h9 hYcalP hY1 h1⟩
    obtain ⟨A, hAconj, hAT, hAV, hAsyl⟩ := exists_conj_sylow_centralizer h9
    have hAΩ : A ∈ nineOmegaIn V (Y ⊔ T) T :=
      ((nine_two_one h9.hyp7 h9.rk_gt hK2).2 A hAconj hAT).resolve_right hAV
    have hIsE : E1.IsE 1 (Y ⊔ T) T A (Y ⊔ T) := nine_two_isE h9.hyp7 h9.rk_gt hK2 hAΩ
    have hTK : T ≤ Y ⊔ T := le_sup_right
    have hTinf : T ⊓ (Y ⊔ T) = T := inf_eq_left.2 hTK
    have hprod : ((Y ⊔ T : Subgroup G) : Set G) =
        ((T ⊓ (Y ⊔ T) : Subgroup G) : Set G) * (Y : Set G) := by
      rw [hTinf, ← hYT]
      exact coe_sup_eq_mul_of_mul_eq_mul hYT
    have hAab : IsElemAbelian 2 A := by
      obtain ⟨g, hg⟩ := hAconj
      rw [hg]
      exact E3.isElemAbelian_conjSubgroup h9.hyp7.1 g
    have hSyl : IsSylowIn 2 (T ⊓ (Y ⊔ T)) (Y ⊔ T) := by
      rw [hTinf]
      exact hK1.sylowTwo
    have hτ : E1.tauOf (normalizer (V : Set G)) T A ≤ T ⊓ (Y ⊔ T) :=
      le_inf (E1.tauOf_le _ _ _) ((E1.tauOf_le _ _ _).trans hTK)
    have hEany : E1.IsEAny (normalizer (V : Set G)) T A (Y ⊔ T) := by
      refine ⟨1, E1.eight_two h9.sylow hAT hAab hK1.le hτ hSyl ?_⟩
      rw [hTinf]
      exact hIsE
    have hmem : (Y ⊔ T) ∈ calPMTA V T A := ⟨hEany, Y, hYcalP, hprod⟩
    rcases h93 h9 A hAconj hAT hAsyl with h | h
    · exact h1 h
    · rw [h] at hmem
      exact hmem

end CFSG.LocalAnalysis.WeakClosure81
