module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKSetup
import CFSG.RankThree.PartTwo.Sec13.Naturality

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem zpowers_conj_mem_omegaA {E : Subgroup G} {a w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) (ha : Subgroup.zpowers a ∈ omegaA E) :
    Subgroup.zpowers (w * a * w⁻¹) ∈ omegaA E := by
  have := (map_conj_mem_omegaA_iff (F := Subgroup.zpowers a) hw).mpr ha
  rwa [MonoidHom.map_zpowers] at this

theorem false_of_case1 {A L E F : Subgroup G} {c x y t : G} (hfr : Frame138 A L E F c x y t)
    (hcΩ : Subgroup.zpowers c ∉ omegaA E) (hdΩ : E ⊓ L ∉ omegaA E) {e : G}
    (heΩ : Subgroup.zpowers e ∈ omegaA E)
    (hU : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G)) :
    False := by
  obtain ⟨heE, he3', -⟩ := zpowers_mem_omegaA_iff.mp heΩ
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at he3'
    norm_num at he3'
  have hconj : ∀ w ∈ Subgroup.normalizer (E : Set G), w * e * w⁻¹ ∈ Subgroup.zpowers e :=
    fun w hw => (Subgroup.mem_normalizer_iff.mp (hU hw) e).mp (Subgroup.mem_zpowers e)
  rcases zpowers_eq_or_eq_of_normalizes hfr.frame hfr.hd1 hfr.hxE hfr.hyF hfr.hE27 hfr.hF27
      hfr.h9 hfr.hFN hfr.hEab hfr.hE3 hfr.hc1 hfr.hcE hfr.hZgen
      (by rw [hfr.htc, mul_inv_cancel_right]) hfr.htd heE he1 (hconj y (hfr.hFN hfr.hyF))
      (hconj t hfr.htE) with h | h
  · exact hcΩ (h ▸ heΩ)
  · exact hdΩ (by rw [hfr.hEL, ← h]; exact heΩ)

theorem false_of_case2 {A L E F : Subgroup G} {c x y t : G} (hfr : Frame138 A L E F c x y t)
    (hcΩ : Subgroup.zpowers c ∉ omegaA E) (hdΩ : E ⊓ L ∉ omegaA E) {e : G}
    (heΩ : Subgroup.zpowers e ∈ omegaA E) (heF : e ∈ F) (hΩ3 : (omegaA E).ncard = 3) :
    False := by
  set d := ⁅x, y⁆ with hd
  obtain ⟨heE, he3', -⟩ := zpowers_mem_omegaA_iff.mp heΩ
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at he3'
    norm_num at he3'
  have htc' : t * c * t⁻¹ = c := by rw [hfr.htc, mul_inv_cancel_right]
  have hdΩ' : Subgroup.zpowers d ∉ omegaA E := by rw [← hfr.hEL]; exact hdΩ
  have hyE : y ∈ Subgroup.normalizer (E : Set G) := hfr.hFN hfr.hyF
  obtain ⟨α, β, rfl⟩ := hfr.hZgen _ (Subgroup.mem_inf.mpr ⟨heE, heF⟩)
  set e := c ^ α * d ^ β with he
  have hcd : c * d = d * c := hfr.hEab c hfr.hcE d hfr.hdE
  have hte : t * e * t⁻¹ ∉ Subgroup.zpowers e := by
    intro hmem
    rcases three_dvd_or_of_conj_mem hfr.hc3 hfr.hc1 hfr.hd3 hfr.hd1 hcd htc' hfr.htd he1 hmem
      with ⟨m, hm⟩ | ⟨m, hm⟩
    · apply hdΩ'
      have : e = d ^ β := by rw [he, hm, pow_mul, hfr.hc3, one_pow, one_mul]
      rw [this] at heΩ he1
      have heq := zpowers_eq_of_mem (by rw [← pow_mul, mul_comm, pow_mul, hfr.hd3, one_pow])
        he1 hfr.hd3 hfr.hd1 (pow_mem (Subgroup.mem_zpowers d) β)
      rwa [heq] at heΩ
    · apply hcΩ
      have : e = c ^ α := by rw [he, hm, pow_mul, hfr.hd3, one_pow, mul_one]
      rw [this] at heΩ he1
      have heq := zpowers_eq_of_mem (by rw [← pow_mul, mul_comm, pow_mul, hfr.hc3, one_pow])
        he1 hfr.hc3 hfr.hc1 (pow_mem (Subgroup.mem_zpowers c) α)
      rwa [heq] at heΩ
  set e' := t * e * t⁻¹ with he'
  have he'Ω : Subgroup.zpowers e' ∈ omegaA E := zpowers_conj_mem_omegaA hfr.htE heΩ
  have hne : Subgroup.zpowers e ≠ Subgroup.zpowers e' := fun h =>
    hte (h ▸ Subgroup.mem_zpowers e')
  obtain ⟨X, hXΩ, hXe, hXe'⟩ : ∃ X ∈ omegaA E, X ≠ Subgroup.zpowers e ∧
      X ≠ Subgroup.zpowers e' := by
    by_contra hall
    push Not at hall
    have hsub : omegaA E ⊆ {Subgroup.zpowers e, Subgroup.zpowers e'} := by
      intro X hX
      by_cases h1 : X = Subgroup.zpowers e
      · exact Or.inl h1
      · exact Or.inr (hall X hX h1)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hΩ3] at this
    have h2 := Set.ncard_pair hne
    omega
  have hΩeq : omegaA E = {Subgroup.zpowers e, Subgroup.zpowers e', X} := by
    symm
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro Y hY
      rcases hY with rfl | rfl | rfl
      · exact heΩ
      · exact he'Ω
      · exact hXΩ
    · rw [hΩ3, Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hXe')]
      rintro (h | h)
      · exact hne h
      · exact hXe h.symm
  obtain ⟨-, hX3, a, rfl, -⟩ := id hXΩ
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hX3
    norm_num at hX3
  have haE : a ∈ E := (zpowers_mem_omegaA_iff.mp hXΩ).1
  have hconjX : ∀ w ∈ Subgroup.normalizer (E : Set G),
      Subgroup.zpowers (w * a * w⁻¹) ≠ Subgroup.zpowers e →
      Subgroup.zpowers (w * a * w⁻¹) ≠ Subgroup.zpowers e' →
      w * a * w⁻¹ ∈ Subgroup.zpowers a := by
    intro w hw h1 h2
    have hmem : Subgroup.zpowers (w * a * w⁻¹) ∈ omegaA E := zpowers_conj_mem_omegaA hw hXΩ
    rw [hΩeq] at hmem
    rcases hmem with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h ▸ Subgroup.mem_zpowers _
  have hback : ∀ w : G, ∀ b : G, Subgroup.zpowers (w * a * w⁻¹) = Subgroup.zpowers b →
      Subgroup.zpowers a = Subgroup.zpowers (w⁻¹ * b * w) := by
    intro w b h
    have h' := congrArg (fun Y : Subgroup G => Y.map (MulAut.conj w⁻¹).toMonoidHom) h
    simp only [MonoidHom.map_zpowers] at h'
    convert h' using 2 <;> simp [mul_assoc]
  have hyZ : ∀ z ∈ E ⊓ F, y⁻¹ * z * y = z := fun z hz => by
    rw [mul_assoc, hfr.hFab z (Subgroup.mem_inf.mp hz).2 y hfr.hyF, inv_mul_cancel_left]
  have heZ : e ∈ E ⊓ F := Subgroup.mem_inf.mpr ⟨heE, heF⟩
  have he'Z : e' ∈ E ⊓ F := by
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hfr.htE e).mp heE, ?_⟩
    rw [he', he, show t * (c ^ α * d ^ β) * t⁻¹ = (t * c * t⁻¹) ^ α * (t * d * t⁻¹) ^ β by
      rw [conj_pow, conj_pow]; group, htc', hfr.htd]
    exact mul_mem (pow_mem hfr.hcF α) (pow_mem (inv_mem (Subgroup.mem_inf.mp hfr.hdZ).2) β)
  have hya : y * a * y⁻¹ ∈ Subgroup.zpowers a := by
    refine hconjX y hyE (fun h => hXe ?_) (fun h => hXe' ?_)
    · rw [hback y e h, hyZ e heZ]
    · rw [hback y e' h, hyZ e' he'Z]
  have htinv : t⁻¹ * e * t = e' := by
    have htd' : t⁻¹ * d * t = d⁻¹ := by
      have h1 : t⁻¹ * (t * d * t⁻¹) * t = d := by simp [mul_assoc]
      rw [hfr.htd] at h1
      have h2 := congrArg (·⁻¹) h1
      simp only [mul_inv_rev, inv_inv] at h2
      rw [mul_assoc]
      exact h2
    have htc'' : t⁻¹ * c * t = c := by
      rw [mul_assoc, ← hfr.htc, inv_mul_cancel_left]
    rw [he', he, show t⁻¹ * (c ^ α * d ^ β) * t = (t⁻¹ * c * t) ^ α * (t⁻¹ * d * t) ^ β by
      rw [show t⁻¹ * c * t = t⁻¹ * c * t⁻¹⁻¹ by rw [inv_inv],
        show t⁻¹ * d * t = t⁻¹ * d * t⁻¹⁻¹ by rw [inv_inv], conj_pow, conj_pow]; group,
      show t * (c ^ α * d ^ β) * t⁻¹ = (t * c * t⁻¹) ^ α * (t * d * t⁻¹) ^ β by
      rw [conj_pow, conj_pow]; group, htc', htc'', htd', hfr.htd]
  have hta : t * a * t⁻¹ ∈ Subgroup.zpowers a := by
    refine hconjX t hfr.htE (fun h => hXe' ?_) (fun h => hXe ?_)
    · rw [hback t e h, htinv]
    · rw [hback t e' h, he', show t⁻¹ * (t * e * t⁻¹) * t = e by group]
  rcases zpowers_eq_or_eq_of_normalizes hfr.frame hfr.hd1 hfr.hxE hfr.hyF hfr.hE27 hfr.hF27
      hfr.h9 hfr.hFN hfr.hEab hfr.hE3 hfr.hc1 hfr.hcE hfr.hZgen htc' hfr.htd haE ha1 hya hta
    with h | h
  · exact hcΩ (h ▸ hXΩ)
  · exact hdΩ' (h ▸ hXΩ)

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
