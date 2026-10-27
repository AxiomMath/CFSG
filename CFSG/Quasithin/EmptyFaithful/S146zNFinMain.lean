module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinZ
public import CFSG.Quasithin.EmptyFaithful.S146zNFinV

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.A6Mod

theorem a6Fin_proved : A6Fin := by
  intro W _ _ hsq hcard L ⟨e⟩ _
  let ρ : alternatingGroup (Fin 6) →* MulAut W := L.subtype.comp e.symm.toMonoidHom
  have hρe : ∀ l : L, ρ (e l) = (l : MulAut W) := fun l => by simp [ρ]
  have h : A6Fin.Setup ρ :=
    ⟨fun w => by simpa [pow_two] using hsq w, hcard,
      (Subgroup.subtype_injective L).comp e.symm.injective⟩
  have key : ∀ n ∈ Subgroup.normalizer (L : Set (MulAut W)), ∀ g : alternatingGroup (Fin 6),
      ∃ k, ρ k = n * ρ g * n⁻¹ := by
    intro n hn g
    have hmem := (Subgroup.mem_normalizer_iff.mp hn (ρ g)).mp (e.symm g).2
    exact ⟨e ⟨_, hmem⟩, hρe ⟨_, hmem⟩⟩
  have hnot : ∀ n : MulAut W, n ∉ L → ¬ ∃ k, ρ k = n := by
    rintro n hn ⟨k, hk⟩
    exact hn (hk ▸ (e.symm k).2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    apply h.centralizer_trivial n
    intro g
    exact hn _ (e.symm g).2
  · intro l hl hl1 hl2
    have hg : ρ (e ⟨l, hl⟩) = l := hρe ⟨l, hl⟩
    have hne : e ⟨l, hl⟩ ≠ 1 := fun e1 => hl1 (by rw [← hg, e1, map_one])
    have hsq' : e ⟨l, hl⟩ * e ⟨l, hl⟩ = 1 := by
      apply h.inj
      rw [map_mul, hg, map_one, ← pow_two]
      exact hl2
    have := h.rank_invol hne hsq'
    rwa [hg] at this
  · intro n₁ hn₁ n₂ hn₂ h1 h2
    obtain ⟨k, hk⟩ := h.normalizer_coset n₁ n₂ (key n₁ hn₁) (key n₂ hn₂) (hnot n₁ h1) (hnot n₂ h2)
    rw [← hk]
    exact (e.symm k).2
  · intro β hβ
    let β' : MulAut (alternatingGroup (Fin 6)) := (e.symm.trans β).trans e
    have hβ' : ∀ g, ρ (β' g) = (β (e.symm g) : MulAut W) := fun g => by simp [β', ρ]
    have hfus : ∃ x : alternatingGroup (Fin 6), x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l, l * x * l⁻¹ ≠ β' x := by
      obtain ⟨x, hx3, hx1, hx⟩ := hβ
      refine ⟨e x, by rw [← map_pow, hx3, map_one], fun e1 => hx1 (e.injective (e1.trans (map_one e).symm)),
        fun l hl => hx (e.symm l) ?_⟩
      apply e.injective
      rw [map_mul, map_mul, map_inv]
      simpa [β'] using hl
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨n, hn⟩
      apply h.not_induced β' hfus
      refine ⟨n, fun g => ?_⟩
      rw [hβ']
      exact hn (e.symm g)
    · intro n hn n' hn' hn2 hn'2 hnL hn'L hrel
      refine h.rank_sum β' hfus n n' (key n hn) (key n' hn') (by rw [← pow_two, hn2])
        (by rw [← pow_two, hn'2]) (hnot n hnL) (hnot n' hn'L) ?_
      intro g k hgk
      have := hrel (e.symm g) (e.symm k) hgk
      rw [hβ', hβ']
      exact this
    · intro a b hab ha1 hb1 ha2 hb2 hcomm
      let α : MulAut (alternatingGroup (Fin 6)) := β'.symm
      have hα : ∃ x : alternatingGroup (Fin 6), x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l, l * x * l⁻¹ ≠ α x := by
        obtain ⟨x, hx3, hx1, hx⟩ := hfus
        refine ⟨β' x, by rw [← map_pow, hx3, map_one],
          fun e1 => hx1 (β'.injective (e1.trans (map_one β').symm)), fun l hl => ?_⟩
        apply hx l⁻¹
        have : α (β' x) = x := β'.symm_apply_apply x
        rw [this] at hl
        calc l⁻¹ * x * l⁻¹⁻¹ = l⁻¹ * (l * β' x * l⁻¹) * l := by rw [hl]; group
          _ = β' x := by group
      have hαa : ρ (α (e a)) = ((β.symm a : L) : MulAut W) := by simp [α, β', ρ]
      have hαb : ρ (α (e b)) = ((β.symm b : L) : MulAut W) := by simp [α, β', ρ]
      have hmain := h.no_quad_pair α hα (a := e a) (b := e b) (fun e1 => hab (e.injective e1))
        (fun e1 => ha1 (e.injective (e1.trans (map_one e).symm)))
        (fun e1 => hb1 (e.injective (e1.trans (map_one e).symm)))
        (by rw [← map_mul, ← pow_two, ha2, map_one]) (by rw [← map_mul, ← pow_two, hb2, map_one])
        (by rw [← map_mul, ← map_mul, hcomm])
      rwa [hρe, hρe, hαa, hαb] at hmain

end CFSG.Quasithin
