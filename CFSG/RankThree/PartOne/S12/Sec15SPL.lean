module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools
public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.RankThree.PartOne

open StrongP

namespace SPL

variable {M : Type} [Group M] [Finite M] {p : ℕ}

theorem inf_conjSub_eq_bot [Fact p.Prime] {P H : Subgroup M} (hP : IsSylowOf p P ⊤) (hP1 : P ≠ ⊥)
    (hPH : P ≤ H)
    (hN : ∀ R : Subgroup M, R ≤ P → R ≠ ⊥ → Subgroup.normalizer (R : Set M) ≤ H) :
    ∀ g : M, g ∉ H → P ⊓ conjSub g P = ⊥ := by
  classical
  have hPp : IsPGroup p P := hP.2.1
  have hPH' : CFSG.ABGLocalTools.IsSylowOf p P H := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hPH, hPp, ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex P H ⊤ hPH le_top
    intro hd
    exact hP.2.2 (h1 ▸ dvd_mul_of_dvd_left hd _)
  by_contra hcon
  have hex : ∃ g : M, g ∉ H ∧ P ⊓ conjSub g P ≠ ⊥ := by
    by_contra h
    exact hcon fun g hg => by
      by_contra hne
      exact h ⟨g, hg, hne⟩
  let S : Set M := {g | g ∉ H ∧ P ⊓ conjSub g P ≠ ⊥}
  obtain ⟨g, hgS, hmax⟩ := Set.exists_max_image S (fun g => Nat.card ↥(P ⊓ conjSub g P))
    (Set.toFinite S) (by obtain ⟨g, hg⟩ := hex; exact ⟨g, hg⟩)
  obtain ⟨hgH, hR1⟩ := hgS
  set R : Subgroup M := P ⊓ conjSub g P with hR
  set T : Subgroup M := conjSub g P with hT
  have hTp : IsPGroup p T := hPp.map _
  have hRT : R ≤ T := inf_le_right
  have hRP : R ≤ P := inf_le_left
  have hRTne : R ≠ T := by
    intro hRT'
    have hTP : T ≤ P := hRT' ▸ inf_le_left
    have hTP' : T = P := Subgroup.eq_of_le_of_card_ge hTP (by rw [hT, card_conjSub])
    have hgN : g ∈ Subgroup.normalizer (P : Set M) := by
      rw [Subgroup.mem_normalizer_iff'']
      intro x
      have := mem_conjSub_iff (g := g) (x := x) (Y := P)
      rw [← hT, hTP'] at this
      rw [← this]
    exact hgH (hN P le_rfl hP1 hgN)
  obtain ⟨x, hxT, hxR, hxN⟩ := CFSG.ComponentClassification.FooteLit.exists_mem_normalizer_of_lt
    (p := p) hTp (lt_of_le_of_ne hRT hRTne)
  set Q : Subgroup M := T ⊓ Subgroup.normalizer (R : Set M) with hQ
  have hQp : IsPGroup p Q := hTp.to_le inf_le_left
  have hRQ : R ≤ Q := le_inf hRT Subgroup.le_normalizer
  have hQH : Q ≤ H := inf_le_right.trans (hN R hRP hR1)
  have hxQ : x ∈ Q := ⟨hxT, hxN⟩
  obtain ⟨k, hkH, hk⟩ := CFSG.ComponentClassification.FooteLit.exists_conj_le_of_isSylowOf
    (p := p) hPH' hQH hQp
  have hg'H : k⁻¹ * g ∉ H := fun h => hgH (by simpa using H.mul_mem hkH h)
  have hsub : conjSub k⁻¹ Q ≤ P ⊓ conjSub (k⁻¹ * g) P := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    have haP := hk a ha
    refine ⟨by simpa [MulAut.conj_apply] using haP, mem_conjSub_iff.2 ?_⟩
    obtain ⟨z, hz, rfl⟩ := (Subgroup.mem_inf.1 ha).1
    have hz' : g⁻¹ * k * (k⁻¹ * (g * z * g⁻¹) * k) * (k⁻¹ * g) ∈ P := by
      have e : g⁻¹ * k * (k⁻¹ * (g * z * g⁻¹) * k) * (k⁻¹ * g) = z := by group
      rw [e]; exact hz
    simpa using hz'
  have hRQlt : Nat.card R < Nat.card Q := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hRQ) fun h => hxR ?_
    have := Subgroup.eq_of_le_of_card_ge hRQ h.ge
    exact this ▸ hxQ
  have hS' : k⁻¹ * g ∈ S := by
    refine ⟨hg'H, fun h => ?_⟩
    obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hR1
    have : (MulAut.conj k⁻¹ (r : M)) ∈ P ⊓ conjSub (k⁻¹ * g) P :=
      hsub ⟨r, hRQ r.2, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    have h2 : k⁻¹ * (r : M) * k = 1 := by simpa [MulAut.conj_apply] using this
    apply hr1
    apply Subtype.ext
    have h1 : (r : M) = k * (k⁻¹ * (r : M) * k) * k⁻¹ := by group
    rw [h1, h2]; simp
  have hle := hmax (k⁻¹ * g) hS'
  have hcard : Nat.card Q ≤ Nat.card ↥(P ⊓ conjSub (k⁻¹ * g) P) := by
    calc Nat.card Q = Nat.card (conjSub k⁻¹ Q) := card_conjSub.symm
      _ ≤ _ := Subgroup.card_le_of_le hsub
  omega

end SPL

theorem stronglyPEmbedded_of_normalizers_le {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P H : Subgroup M} (hP : IsSylowOf p P ⊤) (hP1 : P ≠ ⊥) (hPH : P ≤ H) (hH : H ≠ ⊤)
    (hN : ∀ R : Subgroup M, R ≤ P → R ≠ ⊥ → Subgroup.normalizer (R : Set M) ≤ H) :
    IsStronglyPEmbedded p H := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hPp : IsPGroup p P := hP.2.1
  have hPH' : CFSG.ABGLocalTools.IsSylowOf p P H := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hPH, hPp, ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex P H ⊤ hPH le_top
    intro hd
    exact hP.2.2 (h1 ▸ dvd_mul_of_dvd_left hd _)
  have hbot := SPL.inf_conjSub_eq_bot hP hP1 hPH hN
  refine ⟨hH, ?_, fun g hg hdvd => ?_⟩
  · have hpP : p ∣ Nat.card P := by
      rcases hPp.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hP1
      · exact h
    exact hpP.trans (Subgroup.card_dvd_of_le hPH)
  ·
    obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ conjSub g H)) p hdvd
    set t : M := (t' : M) with ht
    have htH : t ∈ H := t'.2.1
    have htg : g⁻¹ * t * g ∈ H := mem_conjSub_iff.1 t'.2.2
    have hord : orderOf t = p := by
      rw [ht, Subgroup.orderOf_coe]; exact ht'
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord
      exact (Fact.out : p.Prime).one_lt.ne hord
    have hzp : ∀ y : M, orderOf y = p → IsPGroup p (Subgroup.zpowers y) := fun y hy =>
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
    have hzp' : orderOf (g⁻¹ * t * g) = p := by
      rw [show g⁻¹ * t * g = (MulAut.conj g⁻¹) t by simp, MulEquiv.orderOf_eq]
      exact hord
    obtain ⟨h₁, hh₁, hk₁⟩ := CFSG.ComponentClassification.FooteLit.exists_conj_le_of_isSylowOf
      (p := p) hPH' ((Subgroup.zpowers_le).2 htH) (hzp t hord)
    obtain ⟨h₂, hh₂, hk₂⟩ := CFSG.ComponentClassification.FooteLit.exists_conj_le_of_isSylowOf
      (p := p) hPH' ((Subgroup.zpowers_le).2 htg) (hzp _ hzp')
    have h1 : h₁⁻¹ * t * h₁ ∈ P := hk₁ t (Subgroup.mem_zpowers t)
    have h2 : h₂⁻¹ * (g⁻¹ * t * g) * h₂ ∈ P := hk₂ _ (Subgroup.mem_zpowers _)
    have hg' : h₁⁻¹ * g * h₂ ∉ H := fun h => hg (by
      have := H.mul_mem (H.mul_mem hh₁ h) (H.inv_mem hh₂)
      simpa [mul_assoc] using this)
    have hmem : h₁⁻¹ * t * h₁ ∈ P ⊓ conjSub (h₁⁻¹ * g * h₂) P := by
      refine ⟨h1, mem_conjSub_iff.2 ?_⟩
      have : (h₁⁻¹ * g * h₂)⁻¹ * (h₁⁻¹ * t * h₁) * (h₁⁻¹ * g * h₂) =
          h₂⁻¹ * (g⁻¹ * t * g) * h₂ := by group
      rw [this]
      exact h2
    rw [hbot _ hg', Subgroup.mem_bot] at hmem
    apply ht1
    have : t = h₁ * (h₁⁻¹ * t * h₁) * h₁⁻¹ := by group
    rw [this, hmem]
    group

end CFSG.RankThree.PartOne
