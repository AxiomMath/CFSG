module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155NOCore
public import CFSG.RankThree.PartTwo.Sec15.Sylow155NODeg
public import CFSG.RankThree.PartTwo.Sec15.Sylow155NONorm
public import CFSG.RankThree.PartTwo.Sec15.Sylow155TwinGrp
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6Cent

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155NO

open CFSG.RankThree.PartTwo

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem sup_le_normalizer_left {J₁ J₂ : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥) :
    J₁ ⊔ J₂ ≤ Subgroup.normalizer (J₁ : Set Q) := by
  refine sup_le Subgroup.le_normalizer fun y hy => Subgroup.mem_normalizer_iff.mpr fun x => ?_
  have hc : ∀ x ∈ J₁, y * x * y⁻¹ = x := fun x hx => by
    rw [(Sec14.Item148PtRes.commute_of_commutator_eq_bot hJ hx hy).symm, mul_inv_cancel_right]
  constructor
  · intro hx
    rw [hc x hx]
    exact hx
  · intro hx
    have h := hc _ hx
    have e : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
        _ = y⁻¹ * (y * (y * x * y⁻¹) * y⁻¹) * y := by rw [h]
        _ = y * x * y⁻¹ := by group
    rw [e]
    exact hx

theorem card_map_conj (J : Subgroup Q) (d : Q) :
    Nat.card (J.map (MulAut.conj d).toMonoidHom) = Nat.card J :=
  Subgroup.card_map_of_injective (MulAut.conj d).injective

theorem card_inf_centralizer (J : Subgroup Q) :
    Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set Q)) = Nat.card (Subgroup.center ↥J) := by
  have h : J ⊓ Subgroup.centralizer (J : Set Q) = (Subgroup.center ↥J).map J.subtype := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_map,
      Subgroup.mem_center_iff, Subgroup.coe_subtype]
    constructor
    · rintro ⟨hx, hc⟩
      exact ⟨⟨x, hx⟩, fun g => Subtype.ext (hc g g.2), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun g hg => congrArg Subtype.val (hy ⟨g, hg⟩)⟩
  rw [h, Subgroup.card_map_of_injective J.subtype_injective]

theorem map_conj_eq_or_eq {J₁ J₂ : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥)
    (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3) (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6))) {d : Q}
    (hd : d ∈ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup Q) : Set Q)) {J : Subgroup Q}
    (hJJ : J ≤ J₁ ⊔ J₂) (hJn : J₁ ⊔ J₂ ≤ Subgroup.normalizer (J : Set Q))
    (hJc : Nat.card J = 1080) :
    J.map (MulAut.conj d).toMonoidHom = J₁ ∨ J.map (MulAut.conj d).toMonoidHom = J₂ := by
  refine eq_or_eq_of_le_normalizer hJ h3 hT₁ hT₂ ?_ ?_ (by rw [card_map_conj, hJc])
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hd x).mp (hJJ hx)
  · intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hy' : d⁻¹ * y * d ∈ J₁ ⊔ J₂ := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hd) y).mp hy
      simpa using this
    have hn := Subgroup.mem_normalizer_iff.mp (hJn hy')
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(d⁻¹ * y * d) * x * (d⁻¹ * y * d)⁻¹, (hn x).mp hx, by group⟩
    · rintro ⟨x, hx, hxz⟩
      refine ⟨(d⁻¹ * y * d)⁻¹ * x * (d⁻¹ * y * d), ?_, ?_⟩
      · have := (hn ((d⁻¹ * y * d)⁻¹ * x * (d⁻¹ * y * d))).mpr (by
          simpa [mul_assoc] using hx)
        exact this
      · calc d * ((d⁻¹ * y * d)⁻¹ * x * (d⁻¹ * y * d)) * d⁻¹
            = y⁻¹ * (d * x * d⁻¹) * y := by group
          _ = y⁻¹ * (y * z * y⁻¹) * y := by rw [hxz]
          _ = z := by group

theorem exists_inner_of_elemAbelian {Γ : Type} [Group Γ] [Finite Γ] (π : Γ →* Q)
    {Ā J₁ J₂ : Subgroup Q}
    (hĀc : ∀ a ∈ Ā, ∀ b ∈ Ā, a * b = b * a) (hĀ3 : ∀ a ∈ Ā, a ^ 3 = 1)
    (hĀ27 : Nat.card Ā = 27)
    (hĀC : ∀ q ∈ Subgroup.centralizer (Ā : Set Q), q ^ 3 = 1 → q ∈ Ā)
    (hĀY : Ā ≤ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup Q) : Set Q))
    (hJ : ⁅J₁, J₂⁆ = ⊥) (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3)
    (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6)))
    {T K : Subgroup Γ} (hKT : K ≤ T) (hK3 : ¬ 3 ∣ Nat.card K)
    (f : ↥T →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hker : f.ker = K.subgroupOf T) (hTπ : T ⊓ π.ker ≤ K) (hTJ : T.map π ≤ J₁ ⊔ J₂)
    {δ : Γ} (hδT : ∀ x ∈ T, δ * x * δ⁻¹ ∈ T)
    (hδY : π δ ∈ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup Q) : Set Q))
    (hδĀ : ∀ a ∈ Ā, a * π δ = π δ * a) :
    ∃ t ∈ T, ∀ x ∈ T, (δ * x * δ⁻¹) * (t * x * t⁻¹)⁻¹ ∈ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ' : ⁅J₂, J₁⁆ = ⊥ := by rw [Subgroup.commutator_comm, hJ]
  have h3' : Nat.card ↥(J₂ ⊓ J₁) = 3 := by rwa [inf_comm]
  have hĀJ : ∀ a ∈ Ā, a ∈ Subgroup.normalizer (J₁ : Set Q) ∧
      a ∈ Subgroup.normalizer (J₂ : Set Q) := fun a ha =>
    normalizes_of_pow_three hJ h3 hT₁ hT₂ (hĀ3 a ha) (hĀY ha)
  have hĀJ₁ : Ā ≤ Subgroup.normalizer (J₁ : Set Q) := fun a ha => (hĀJ a ha).1
  have hĀJ₂ : Ā ≤ Subgroup.normalizer (J₂ : Set Q) := fun a ha => (hĀJ a ha).2
  have hperf₁ := commutator_eq_top_of_elemAbelian hĀc hĀ3 hĀ27 hĀC hĀJ₁ hĀJ₂ hJ h3 hT₁ hT₂
  have hperf₂ := commutator_eq_top_of_elemAbelian hĀc hĀ3 hĀ27 hĀC hĀJ₂ hĀJ₁ hJ' h3' hT₂ hT₁
  set d := π δ with hd
  have hL : ∀ q ∈ Subgroup.centralizer (Ā : Set Q), q ^ 3 = 1 → d * q * d⁻¹ = q := by
    intro q hq hq3
    rw [← hδĀ q (hĀC q hq hq3), mul_inv_cancel_right]
  have hcU := Sec14.Item148PtRes.card_eq_of_isTripleCover hT₁
  have hcV := Sec14.Item148PtRes.card_eq_of_isTripleCover hT₂
  have hne : J₁ ≠ J₂ := by
    intro h
    rw [h, inf_idem, hcV] at h3
    norm_num at h3
  have hinj : ∀ X Y : Subgroup Q, X.map (MulAut.conj d).toMonoidHom =
      Y.map (MulAut.conj d).toMonoidHom → X = Y := fun X Y h =>
    Subgroup.map_injective (MulAut.conj d).injective h
  have hN₁ : J₁ ⊔ J₂ ≤ Subgroup.normalizer (J₁ : Set Q) := sup_le_normalizer_left hJ
  have hN₂ : J₁ ⊔ J₂ ≤ Subgroup.normalizer (J₂ : Set Q) := by
    rw [sup_comm]
    exact sup_le_normalizer_left hJ'
  have hm₁ := map_conj_eq_or_eq hJ h3 hT₁ hT₂ hδY le_sup_left hN₁ hcU
  have hm₂ := map_conj_eq_or_eq hJ h3 hT₁ hT₂ hδY le_sup_right hN₂ hcV
  have hfix₁ : J₁.map (MulAut.conj d).toMonoidHom = J₁ := by
    rcases hm₁ with h | h
    · exact h
    exfalso
    have h₂ : J₂.map (MulAut.conj d).toMonoidHom = J₁ := by
      rcases hm₂ with h' | h'
      · exact h'
      · exact absurd (hinj _ _ (h.trans h'.symm)) hne
    have hsq : J₁.map (MulAut.conj (d ^ 2)).toMonoidHom = J₁ := by
      have e : (MulAut.conj (d ^ 2)).toMonoidHom =
          (MulAut.conj d).toMonoidHom.comp (MulAut.conj d).toMonoidHom := by
        ext x
        simp [pow_two, mul_assoc]
      rw [e, ← Subgroup.map_map, h, h₂]
    obtain ⟨x, hx3, hxZ⟩ := exists_pow_three_not_mem_center hT₁
    have hfC : (x : Q) ∉ Subgroup.centralizer (J₁ : Set Q) := by
      intro hc
      apply hxZ
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc g g.2)
    have hĀp : IsPGroup 3 Ā := fun a =>
      ⟨1, Subtype.ext (by simpa using hĀ3 a a.2)⟩
    obtain ⟨T', hT', hĀT', hT'W, hT'Z⟩ := Sylow155T.exists_isPGroup_inf_not_le hĀp hĀJ₁
      x.2 (by simpa using congrArg Subtype.val hx3) hfC
    refine Sylow155T.false_of_fixed (W := J₁) (W₂ := J₂) (Ā := Ā) (T := T') (d := d)
      (fun w hw w₂ hw₂ => Sec14.Item148PtRes.commute_of_commutator_eq_bot hJ hw hw₂) h hsq
      hT' hĀT' hT'W (fun a ha => hδĀ a ha) hL ?_ hT'Z
    rw [card_inf_centralizer, hT₁.1]
  have hfix₂ : J₂.map (MulAut.conj d).toMonoidHom = J₂ := by
    rcases hm₂ with h | h
    · exact absurd (hinj _ _ (h.trans hfix₁.symm)) hne.symm
    · exact h
  have hconj : ∀ {J : Subgroup Q}, J.map (MulAut.conj d).toMonoidHom = J →
      ∀ x ∈ J, d * x * d⁻¹ ∈ J := fun {J} hJm x hx => by
    rw [← hJm]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hδZ : ∀ z ∈ J₁ ⊓ J₂, d * z * d⁻¹ = z := by
    intro z hz
    have hĀZ : Ā ≤ Subgroup.normalizer ((J₁ ⊓ J₂ : Subgroup Q) : Set Q) :=
      Sylow155T.le_normalizer_inf_of_le hĀJ₁ hĀJ₂
    have hzC : z ∈ Subgroup.centralizer (Ā : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := Sylow155T.conj_eq_of_card_le_three (Z := J₁ ⊓ J₂) h3.le (hĀZ ha)
        (k := 1) (by rw [pow_one]; exact hĀ3 a ha) hz
      calc a * z = a * z * a⁻¹ * a := by group
        _ = z * a := by rw [h]
    have hz3 : z ^ 3 = 1 := by
      have h1 : orderOf (⟨z, hz⟩ : ↥(J₁ ⊓ J₂)) ∣ 3 := h3 ▸ orderOf_dvd_natCard _
      have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
      simpa using congrArg Subtype.val h2
    exact hL z hzC hz3
  exact exists_inner_of_centralProduct π hperf₁ hT₁ hperf₂ hT₂ hJ h3 hKT hK3 f hf hker hTπ hTJ
    hδT (hconj hfix₁) (hconj hfix₂) hδZ

end CFSG.RankThree.PartTwo.Sec15.Sylow155NO
