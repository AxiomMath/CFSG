module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SBase
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKCase2
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138T

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open Ronan138S (zpowers_conj_mem_omegaA zpowers_eq_or_eq_of_normalizes three_dvd_or_of_conj_mem
  zpowers_eq_of_mem)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_case1 {A L E F : Subgroup G} {c x y t : G}
    (hfr : Ronan138S.Frame138Base A L E F c x y t)
    (hcΩ : Subgroup.zpowers c ∉ omegaA E) (hdΩ : Subgroup.zpowers ⁅x, y⁆ ∉ omegaA E) {e : G}
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
  · exact hdΩ (h ▸ heΩ)

theorem false_of_case2 {A L E F : Subgroup G} {c x y t : G}
    (hfr : Ronan138S.Frame138Base A L E F c x y t)
    (hcΩ : Subgroup.zpowers c ∉ omegaA E) (hdΩ : Subgroup.zpowers ⁅x, y⁆ ∉ omegaA E) {e : G}
    (heΩ : Subgroup.zpowers e ∈ omegaA E) (heF : e ∈ F) (hΩ3 : (omegaA E).ncard = 3) :
    False := by
  set d := ⁅x, y⁆ with hd
  obtain ⟨heE, he3', -⟩ := zpowers_mem_omegaA_iff.mp heΩ
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at he3'
    norm_num at he3'
  have htc' : t * c * t⁻¹ = c := by rw [hfr.htc, mul_inv_cancel_right]
  have hdΩ' : Subgroup.zpowers d ∉ omegaA E := hdΩ
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

theorem false_of_case3 {A L E F : Subgroup G} {c x y t : G}
    (hfr : Ronan138S.Frame138Base A L E F c x y t)
    (hcΩ : Subgroup.zpowers c ∉ omegaA E) (hdΩ : Subgroup.zpowers ⁅x, y⁆ ∉ omegaA E) {e : G}
    {K : Subgroup G}
    (hD : Sec13Data G E e K) (heF : e ∈ F)
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (K ⊓ Subgroup.normalizer (E : Set G)) (E ⊓ K)))
    (hWB : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G))
    (hΩ : omegaA E = orbitIn (Subgroup.normalizer (E : Set G)) (Subgroup.zpowers e))
    (hΩ9 : (omegaA E).ncard = 9) (hB9 : Nat.card (E ⊓ K : Subgroup G) = 9) : False := by
  have hE3 : CFSG.Assembly.IsElemAbelian 3 E := hfr.hH.2.2.2.1
  set B := E ⊓ K with hBdef
  have heE : e ∈ E := hD.mem_A
  have he3 : e ^ 3 = 1 := hE3.2 e heE
  have he1 : e ≠ 1 := hD.ne_one
  have hKe : ∀ k ∈ K, k * e = e * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hk)
  have heB : e ∉ B := by
    intro heB
    rcases eq_bot_or_eq_of_isIrreducibleOn hirr (Subgroup.zpowers_le.mpr heB) (fun k hk => by
      apply mem_normalizer_of_map_le
      rw [MonoidHom.map_zpowers]
      apply Subgroup.zpowers_le.mpr
      change k * e * k⁻¹ ∈ Subgroup.zpowers e
      rw [hKe k (Subgroup.mem_inf.mp hk).1, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers e) with h0 | h0
    · exact he1 (by simpa using (Subgroup.zpowers_eq_bot).mp h0)
    · have : Nat.card (Subgroup.zpowers e) = Nat.card B := by rw [h0]
      rw [card_zpowers_of_pow_three he3 he1, hB9] at this
      norm_num at this
  have hBE : B ≤ E := inf_le_left
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun a b => Subtype.ext (hfr.hEab a (hBE a.2) b (hBE b.2))⟩⟩,
      fun z hz => hE3.2 z (hBE hz)⟩
  obtain ⟨-, he27⟩ := isElemAbelian_zpowers_sup_of_card_nine he3 heB le_rfl hB9
    (fun z hz => hBe.2 z hz) (fun z hz => hfr.hEab e heE z (hBE hz))
  have hEeB : E = Subgroup.zpowers e ⊔ B :=
    (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr heE) hBE)
      (by rw [he27, hfr.hE27])).symm
  have hepts : Subgroup.zpowers e ∈ pointsOff E B :=
    ⟨Subgroup.zpowers_le.mpr heE, card_zpowers_of_pow_three he3 he1,
      fun hle => heB (hle (Subgroup.mem_zpowers e))⟩
  have hΩpts : omegaA E ⊆ pointsOff E B := by
    intro X hX
    rw [hΩ] at hX
    obtain ⟨w, hwE, rfl⟩ := hX
    exact map_conj_mem_pointsOff hwE (hWB hwE) hepts
  have hΩeq : omegaA E = pointsOff E B :=
    Set.eq_of_subset_of_ncard_le hΩpts
      (by rw [ncard_pointsOff hE3 heE hEeB heB hB9, hΩ9])
      (Set.toFinite _)
  have hmemB : ∀ a ∈ E, a ^ 3 = 1 → a ≠ 1 → Subgroup.zpowers a ∉ omegaA E → a ∈ B := by
    intro a haE ha3 ha1 haΩ
    by_contra haB
    apply haΩ
    rw [hΩeq]
    exact ⟨Subgroup.zpowers_le.mpr haE, card_zpowers_of_pow_three ha3 ha1,
      fun hle => haB (hle (Subgroup.mem_zpowers a))⟩
  have hcB : c ∈ B := hmemB c hfr.hcE hfr.hc3 hfr.hc1 hcΩ
  have hdB : ⁅x, y⁆ ∈ B := hmemB _ hfr.hdE hfr.hd3 hfr.hd1 hdΩ
  obtain ⟨α, β, heq⟩ := hfr.hZgen e (Subgroup.mem_inf.mpr ⟨heE, heF⟩)
  exact heB (heq ▸ mul_mem (pow_mem hcB α) (pow_mem hdB β))

end CFSG.RankThree.PartTwo.Sec13.Ronan138T
