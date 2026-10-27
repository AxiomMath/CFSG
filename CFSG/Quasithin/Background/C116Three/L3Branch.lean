module

public import CFSG.Quasithin.Background.C116Three.L3Pair
public import CFSG.Quasithin.Background.C116Three.L3CoreOfPiece
public import CFSG.Quasithin.Background.C116Three.L3Offender
public import CFSG.Quasithin.Background.C116Three.L3Sylow

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] [Finite V]

theorem l3Branch (hV : ∀ v : V, v ^ 2 = 1) {X L₁ L₂ Q : Subgroup (MulAut V)} {τ : MulAut V}
    (P : JPair X L₁ L₂ τ) (h : TwoB56GenInv X L₁ L₂) (hL : IsL32 L₁) (hFF : IsFFModule X)
    (hO2 : pCoreOf 2 X = ⊥) (𝒜 : Set (Subgroup (MulAut V))) (hQ2 : IsPGroup 2 Q) (hQJ : Q ≤ ffJ X)
    (hA : ∀ A ∈ 𝒜, IsFFStarOffender X A) (hAQ : ∀ A ∈ 𝒜, A ≤ Q) :
    ∃ w : V, w ∉ fixV L₁ ∧ w ∈ fixV L₂ ∧ ∀ A ∈ 𝒜, w ∈ fixV A := by
  obtain ⟨G₁, G₂, W₁, W₂, hJ, hbot, hcomm, hL₁, hL₂, hG₁, hG₂, hf₁, hf₂, hsup, hWinf, hp₁, hp₂,
    hI₁, hI₂⟩ := h
  have hcard₁ : Nat.card ↥L₁ = 168 := l3_card_eq hL
  have hcard₂ : Nat.card ↥L₂ = 168 := by
    rw [P.conj, Subgroup.card_map_of_injective (MulAut.conj τ).injective]
    exact hcard₁
  have hG₁eq : L₁ = G₁ := by
    rcases hG₁ with h | ⟨-, h60⟩
    · exact h.symm
    · omega
  have hG₂eq : L₂ = G₂ := by
    rcases hG₂ with h | ⟨-, h60⟩
    · exact h.symm
    · omega
  subst hG₁eq hG₂eq
  have hPD : PairData L₁ L₂ W₁ W₂ (fixV (L₁ ⊔ L₂)) :=
    pairData_l3 hcomm hbot P.q₁.1 P.q₂.1 hsup hWinf hp₁ hp₂ hI₁ hI₂
  have hCfix : ∀ g ∈ L₁, ∀ c ∈ fixV (L₁ ⊔ L₂), g c = c := fun g hg c hc =>
    hPD.fix_C g (Subgroup.mem_sup_left hg) c hc
  have hCW₂ : fixV (L₁ ⊔ L₂) ≤ W₂ := hPD.le₂
  obtain ⟨M₁, hM₁W, hM₁c, ⟨D⟩⟩ := l3Core_of_piece hL hPD.le₁ hPD.inv₁ hp₁
  have hQJ' : Q ≤ L₁ ⊔ L₂ := by rw [← hJ]; exact hQJ
  have hQ₁2 : IsPGroup 2 (R3c23.projSub L₁ L₂ Q hPD.comm) := projSub_isPGroup hPD.comm hbot hQ2
  have hQ₁G : R3c23.projSub L₁ L₂ Q hPD.comm ≤ L₁ := R3c23.projSub_le hPD.comm
  have hproj_mono : ∀ A : Subgroup (MulAut V), A ≤ Q →
      R3c23.projSub L₁ L₂ A hPD.comm ≤ R3c23.projSub L₁ L₂ Q hPD.comm := by
    intro A hAQ' x hx
    obtain ⟨hxG, y, hyG, hxy⟩ := R3c23.mem_projSub.mp hx
    exact R3c23.mem_projSub.mpr ⟨hxG, y, hyG, hAQ' hxy⟩
  have hfixA : ∀ A : Subgroup (MulAut V), A ≤ L₁ ⊔ L₂ → ∀ w ∈ W₁,
      (∀ x ∈ R3c23.projSub L₁ L₂ A hPD.comm, x w = w) → w ∈ fixV A := by
    intro A hAJ w hw hx
    rw [mem_fixV]
    intro a ha
    obtain ⟨x, hxG, y, hyG, rfl⟩ := R3c23.exists_decomp hPD.comm (hAJ ha)
    have hxA : x ∈ R3c23.projSub L₁ L₂ A hPD.comm := R3c23.mem_projSub.mpr ⟨hxG, y, hyG, ha⟩
    rw [MulAut.mul_apply, hPD.triv₁ y hyG w hw]
    exact hx x hxA
  have key : ∃ w ∈ M₁, w ∉ fixV L₁ ∧ ∀ A ∈ 𝒜, w ∈ fixV A := by
    rcases l3core_dichotomy D hCfix with hfix | hb
    ·
      obtain ⟨w, hwM, hwG, hwP⟩ := hfix _ hQ₁G hQ₁2
      exact ⟨w, hwM, hwG, fun A hAm =>
        hfixA A ((hAQ A hAm).trans hQJ') w (hM₁W hwM) fun x hx =>
          hwP x (hproj_mono A (hAQ A hAm) hx)⟩
    ·
      have hb₁ : Bounds L₁ W₁ (fixV (L₁ ⊔ L₂)) := bounds_mono hM₁W hb
      have hCτ : (fixV (L₁ ⊔ L₂)).map τ.toMonoidHom = fixV (L₁ ⊔ L₂) :=
        map_fixV_of_norm (fun l hl => P.norm τ P.τ_mem l hl) fun l hl => by
          simpa using P.norm τ⁻¹ (X.inv_mem P.τ_mem) l hl
      have hM₂W₂ : M₁.map τ.toMonoidHom ≤ W₂ := by
        calc M₁.map τ.toMonoidHom
            ≤ (commV L₁ ⊔ fixV (L₁ ⊔ L₂)).map τ.toMonoidHom := Subgroup.map_mono hM₁c
          _ = (commV L₁).map τ.toMonoidHom ⊔ (fixV (L₁ ⊔ L₂)).map τ.toMonoidHom :=
              Subgroup.map_sup _ _ _
          _ = commV L₂ ⊔ fixV (L₁ ⊔ L₂) := by rw [commV_map_conj P.conj, hCτ]
          _ ≤ W₂ := sup_le (commV_le_of_piece hp₂) hCW₂
      have hb₂ : Bounds L₂ W₂ (fixV (L₁ ⊔ L₂)) := by
        have h1 := bounds_map τ hb
        rw [← P.conj, hCτ] at h1
        exact bounds_mono hM₂W₂ h1
      obtain ⟨w, hwM, hwG, hwT⟩ := l3core_tight D hCfix hQ₁G hQ₁2
      refine ⟨w, hwM, hwG, fun A hAm => ?_⟩
      have hAJ : A ≤ L₁ ⊔ L₂ := (hAQ A hAm).trans hQJ'
      have hAoff := hA A hAm
      have hAel : IsElemAbelian2 A := hAoff.2.2.1
      have hcardV : Nat.card V ≤ Nat.card A * Nat.card ↥(fixV A) := by
        have h := hAoff.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
        rwa [B1.card_bot_mul_card_fixV] at h
      have htW := offender_tight hPD hb₁ hb₂ hAJ hAel hcardV
      have hA₁el := R3c23.isElemAbelian2_projSub hPD.comm hPD.inf_eq_bot hAel
      have hA₁G : R3c23.projSub L₁ L₂ A hPD.comm ≤ L₁ := R3c23.projSub_le hPD.comm
      have htM := tight_of_tight hM₁W hb hA₁G hA₁el htW
      exact hfixA A hAJ w (hM₁W hwM) (hwT _ (hproj_mono A (hAQ A hAm)) hA₁el htM)
  obtain ⟨w, hwM, hwG, hwA⟩ := key
  refine ⟨w, hwG, ?_, hwA⟩
  rw [mem_fixV]
  intro b hb
  exact hPD.triv₁ b hb w (hM₁W hwM)

end CFSG.Quasithin.C116Three
