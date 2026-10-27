module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qYam
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Recognition.F4Thirtyone

public section

namespace CFSG.Quasithin.H13.F431.D4q.Hex

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.Yam

theorem sup_eq_top_of_yamStd {C Y : Type} [Group C] [Finite C] [Group Y] {U P₀ P₁ : Subgroup C}
    (S : YamStd C U P₀ P₁) (e : Y ≃* C) {T M₁ M₂ : Subgroup Y} (h : IsYAmalgamPair T M₁ M₂) :
    M₁ ⊔ M₂ = ⊤ := by
  have hsup : P₀ ⊔ P₁ = ⊤ := S.coatom₀.sup_eq_top_of_ne S.coatom₁ S.ne
  have key : (M₁ ⊔ M₂).map e.toMonoidHom = ⊤ := by
    obtain ⟨c, -, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := S.pair e h
    · rw [Subgroup.map_sup, h₁, h₂, ← Subgroup.map_sup, hsup]
      exact Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective
    · rw [Subgroup.map_sup, h₁, h₂, ← Subgroup.map_sup, sup_comm, hsup]
      exact Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective
  exact Subgroup.map_injective e.injective
    (key.trans (Subgroup.map_top_of_surjective _ e.surjective).symm)

theorem range_conj_le_K_of_sup {D : Type} [Group D] (A : LieAmalgamExt D)
    (hsup : A.P1 ⊔ A.P2 = ⊤) : (MulAut.conj : D →* MulAut D).range ≤ A.K := by
  have hc : ∀ {P : Subgroup D} {p : D}, p ∈ P → (MulAut.conj p : MulAut D) ∈ autStab P :=
    fun {P p} hp x => by
      rw [MulAut.conj_apply]
      constructor
      · exact fun hx => P.mul_mem (P.mul_mem hp hx) (P.inv_mem hp)
      · intro hx
        simpa [mul_assoc] using P.mul_mem (P.mul_mem (P.inv_mem hp) hx) hp
  have h1 : A.P1.map (MulAut.conj : D →* MulAut D) ≤ A.N1 := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨A.inn_le ⟨p, rfl⟩, hc hp⟩
  have h2 : A.P2.map (MulAut.conj : D →* MulAut D) ≤ A.N2 := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨A.inn_le ⟨p, rfl⟩, hc hp⟩
  have h : (⊤ : Subgroup D).map (MulAut.conj : D →* MulAut D) ≤ A.K := by
    rw [← hsup, Subgroup.map_sup]
    exact sup_le (h1.trans A.N1_le_K) (h2.trans A.N2_le_K)
  rintro _ ⟨d, rfl⟩
  exact h ⟨d, Subgroup.mem_top d, rfl⟩


theorem f431Generation_d4 (f : ℕ) : F431Generation .trialityD4 0 f := by
  intro D _ hD A
  obtain ⟨hf, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := d4q_model_data hD
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  exact range_conj_le_K_of_sup A (sup_eq_top_of_yamStd (d4_yamStd σ hf hK hσ) e A.yam)

end CFSG.Quasithin.H13.F431.D4q.Hex
