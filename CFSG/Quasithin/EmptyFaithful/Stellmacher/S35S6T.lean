module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDict
public import CFSG.Quasithin.EmptyFaithful.SzF53MSecA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

namespace S35.S6

variable {G : Type} [Group G]

theorem isModelSec_of_sup_eq {n : ℕ} {M : Model n} {F K N N' : Subgroup G}
    (h : IsModelSec M F K N) (hN' : N' ≤ N) (hF : F ≤ Subgroup.normalizer (N' : Set G))
    (hsup : N' ⊔ K = N) : IsModelSec M F (N' ⊓ K) N' := by
  have hKN : K ≤ N := hsup ▸ le_sup_right
  have hs := h.isSec hKN
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  have hKconj : ∀ x ∈ N, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x hx k hk => by
    have := K.mul_mem (hs.comm x hx k (hKN hk)) hk
    simpa [mul_assoc] using this
  have hnorm : ∀ x ∈ N, x ∈ Subgroup.normalizer (K : Set G) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨hKconj x hx k, fun hk => ?_⟩
    simpa [mul_assoc] using hKconj x⁻¹ (N.inv_mem hx) _ hk
  have hn' : ((N' ⊓ K).subgroupOf N').Normal :=
    ⟨fun a ha g => by
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      exact ⟨N'.mul_mem (N'.mul_mem g.2 ha.1) (N'.inv_mem g.2), hKconj g (hN' g.2) a ha.2⟩⟩
  let ψ : ↥N' →* ↥N ⧸ K.subgroupOf N :=
    (QuotientGroup.mk' (K.subgroupOf N)).comp (Subgroup.inclusion hN')
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hx' : x ∈ K ⊔ N' := by
      rw [sup_comm]
      exact hsup ▸ hx
    obtain ⟨k, hk, y, hy, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes (fun p hp => hnorm p (hN' hp))).mp hx'
    refine ⟨⟨y, hy⟩, ?_⟩
    show QuotientGroup.mk _ = QuotientGroup.mk _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := hKconj y⁻¹ (N.inv_mem (hN' hy)) k hk
    simpa [mul_assoc] using this
  have hψk : ψ.ker = (N' ⊓ K).subgroupOf N' := by
    ext ⟨y, hy⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' (K.subgroupOf N) (Subgroup.inclusion hN' ⟨y, hy⟩) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun hk => ⟨hy, hk⟩, fun hk => hk.2⟩
  let E : ↥N' ⧸ (N' ⊓ K).subgroupOf N' ≃* ↥N ⧸ K.subgroupOf N :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hE : ∀ y : ↥N', E (QuotientGroup.mk y) = QuotientGroup.mk (Subgroup.inclusion hN' y) :=
    fun y => rfl
  have hFK : F ≤ Subgroup.normalizer (K : Set G) := hs.normL
  have hFinf : F ≤ Subgroup.normalizer ((N' ⊓ K : Subgroup G) : Set G) := by
    intro x hx
    have h1 := Subgroup.mem_normalizer_iff.mp (hF hx)
    have h2 := Subgroup.mem_normalizer_iff.mp (hFK hx)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_inf]
    exact and_congr (h1 y) (h2 y)
  have hc : cSecIn F (N' ⊓ K) N' = cSecIn F K N := by
    ext f
    rw [mem_cSecIn_iff hFinf, mem_cSecIn_iff hFK]
    refine and_congr_right fun hf => ⟨fun hall y hy => ?_, fun hall y hy => ?_⟩
    · have hy' : y ∈ K ⊔ N' := by
        rw [sup_comm]
        exact hsup ▸ hy
      obtain ⟨k, hk, y', hy'', rfl⟩ :=
        (F1.mem_sup_iff_exists_mul_of_normalizes (fun p hp => hnorm p (hN' hp))).mp hy'
      have e : f * (k * y') * f⁻¹ * (k * y')⁻¹ =
          (f * k * f⁻¹) * (f * y' * f⁻¹ * y'⁻¹) * k⁻¹ := by group
      rw [e]
      exact K.mul_mem (K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hFK hf) k).mp hk)
        (hall y' hy'').2) (K.inv_mem hk)
    · refine ⟨N'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hF hf) y).mp hy) (N'.inv_mem hy),
        hall y (hN' hy)⟩
  have := hn
  have := hn'
  refine ⟨hn', θ, E.symm.toMonoidHom.comp β, hθs, hc ▸ hθk, ?_, ?_, ?_⟩
  · exact E.symm.surjective.comp hsd.surj
  · exact E.symm.injective.comp hsd.inj
  · intro k u x hux
    have hu : β u = QuotientGroup.mk (Subgroup.inclusion hN' x) := by
      have h1 : E.symm (β u) = QuotientGroup.mk x := hux
      rw [← E.apply_symm_apply (β u), h1]
      rfl
    obtain ⟨hkx, h2⟩ := hsd.equiv k u (Subgroup.inclusion hN' x) hu
    have hkx' : (k : G) * (x : G) * (k : G)⁻¹ ∈ N' :=
      (Subgroup.mem_normalizer_iff.mp (hF k.2) x).mp x.2
    refine ⟨hkx', ?_⟩
    show E.symm (β (M.act (θ k) u)) = _
    rw [h2]
    exact E.symm_apply_eq.mpr rfl

end S35.S6

end F53.Stellmacher

end CFSG.Quasithin
