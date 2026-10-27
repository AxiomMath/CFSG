module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Red
public import CFSG.Quasithin.H13.VolII16Restrict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

theorem s16c11_v1_model_pair {W : Type} [CommGroup W] {X K L : Subgroup (MulAut W)}
    {J₀ : Subgroup W} (hM : S16C11Model X K J₀) (hLX : L ≤ X)
    (hLK : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l) :
    ∃ hJ : (∀ l ∈ L, ∀ j ∈ J₀, l j ∈ J₀), ∃ Θ : ↥J₀ × ↥J₀ ≃* W,
      ∀ (l : ↥L) (p : ↥J₀ × ↥J₀),
        (l : MulAut W) (Θ p) =
          Θ (CFSG.Quasithin.H13.VolI.resHom L J₀ hJ l p.1,
            CFSG.Quasithin.H13.VolI.resHom L J₀ hJ l p.2) := by
  obtain ⟨s, ψ, h1, h2⟩ := hM
  have hJ : ∀ l ∈ L, ∀ j ∈ J₀, l j ∈ J₀ := by
    intro l hl j hj
    let t : Fin 3 → ↥J₀ := ![⟨j, hj⟩, 1, ⟨j, hj⟩⁻¹]
    have ht : t ∈ s16c2m_Triples ↥J₀ := by
      rw [s16c2m_mem_Triples_iff]
      simp [t]
    let w : W := ψ.symm ⟨t, ht⟩
    have hw : (ψ w).1 0 = ⟨j, hj⟩ := by
      simp [w, t]
    have h := h2 l (hLX hl) (fun k hk => hLK l hl k hk) w 0
    rw [hw] at h
    have hmem : (((ψ (l w)).1 0 : ↥J₀) : W) ∈ J₀ := ((ψ (l w)).1 0).2
    rwa [h] at hmem
  refine ⟨hJ, ?_⟩
  let q : ↥J₀ × ↥J₀ ≃* ↥(s16c2m_Triples ↥J₀) := (s16c2m_tripleEquiv ↥J₀).symm
  let Θ : ↥J₀ × ↥J₀ ≃* W := q.trans ψ.symm
  have hΘ : ∀ x : ↥J₀ × ↥J₀, ψ (Θ x) = q x := fun x => by
    change ψ ((q.trans ψ.symm) x) = q x
    simp
  refine ⟨Θ, ?_⟩
  intro l p
  have hcomm : ∀ k ∈ K, (l : MulAut W) * k = k * (l : MulAut W) :=
    fun k hk => hLK (l : MulAut W) l.2 k hk
  apply ψ.injective
  rw [hΘ (CFSG.Quasithin.H13.VolI.resHom L J₀ hJ l p.1,
    CFSG.Quasithin.H13.VolI.resHom L J₀ hJ l p.2)]
  apply Subtype.ext
  funext i
  apply Subtype.ext
  rw [h2 (l : MulAut W) (hLX l.2) hcomm (Θ p) i, hΘ p]
  fin_cases i <;>
    simp [q, s16c2m_tripleEquiv, CFSG.Quasithin.H13.VolI.coe_resHom_apply]

theorem s16c11_v1_commV_of_surj {W M : Type} [CommGroup W] [CommGroup M]
    {A : Subgroup (MulAut W)} {H : Subgroup (MulAut M)} (f : W →* M)
    (hf : Function.Surjective f)
    (hequiv : ∀ a ∈ A, ∃ h ∈ H, ∀ w : W, f (a w) = h (f w)) (hcomm : commV A = ⊤) :
    commV H = ⊤ := by
  rw [eq_top_iff]
  intro m _
  obtain ⟨w, rfl⟩ := hf m
  have hle : commV A ≤ (commV H).comap f := by
    rw [commV, Subgroup.closure_le]
    rintro c ⟨a, ha, v, rfl⟩
    change f (a v * v⁻¹) ∈ commV H
    obtain ⟨h, hh, hah⟩ := hequiv a ha
    have hgen : f (a v * v⁻¹) = h (f v) * (f v)⁻¹ := by
      rw [map_mul, map_inv, hah v]
    rw [hgen]
    exact Subgroup.subset_closure ⟨h, hh, f v, rfl⟩
  have hw : w ∈ commV A := by
    rw [hcomm]
    exact Subgroup.mem_top w
  exact Subgroup.mem_comap.1 (hle hw)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
