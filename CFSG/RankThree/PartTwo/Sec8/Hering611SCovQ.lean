module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovAB
public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovQc
public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovQf

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

variable {P : Type*} [Group P] [Finite P] {σ : MulAut P} {Zh : Subgroup P}

theorem exists_hom_zhat (h : CoverP P σ Zh) : ∃ μ : P →* Zh, ∀ z : Zh, μ (z : P) = z := by
  obtain ⟨σB, hσB⟩ : ∃ σB : MulAut (Abelianization P),
      ∀ p : P, σB (Abelianization.of p) = Abelianization.of (σ p) :=
    ⟨MulEquiv.abelianizationCongr σ, fun p => rfl⟩
  have hsurj : ∀ b : Abelianization P, ∃ p : P, Abelianization.of p = b := fun b => by
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective b
    exact ⟨p, hp⟩
  have hab : ∀ p : P, Abelianization.of p = 1 ↔ p ∈ commutator P := fun p => by
    rw [← Abelianization.ker_of P]
    exact MonoidHom.mem_ker.symm
  have hσBpow : ∀ (j : ℕ) (p : P),
      (σB ^ j) (Abelianization.of p) = Abelianization.of ((σ ^ j) p) := by
    intro j
    induction j with
    | zero => intro p; simp
    | succ k ih =>
      intro p
      rw [pow_succ' σB, MulAut.mul_apply, ih, hσB, pow_succ' σ, MulAut.mul_apply]
  have hσB8 : σB ^ 8 = 1 := by
    refine MulEquiv.ext fun b => ?_
    obtain ⟨p, rfl⟩ := hsurj b
    simp [hσBpow, h.sigma_pow]
  have hinj : Function.Injective (Abelianization.of.comp Zh.subtype : Zh →* Abelianization P) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hz1 : (z : P) ∈ Zh ⊓ commutator P :=
      Subgroup.mem_inf.mpr ⟨z.2, (hab (z : P)).mp hz⟩
    rw [(commutator_facts h).2.1, Subgroup.mem_bot] at hz1
    exact Subtype.ext hz1
  have hfix : ∀ x ∈ (Abelianization.of.comp Zh.subtype : Zh →* Abelianization P).range,
      σB x = x := by
    intro x hx
    obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hx
    show σB (Abelianization.of (z : P)) = Abelianization.of (z : P)
    rw [hσB, h.sigma_Z (z : P) z.2]
  have hfix' : ∀ b : Abelianization P, σB b = b →
      b ∈ (Abelianization.of.comp Zh.subtype : Zh →* Abelianization P).range := by
    intro b hb
    obtain ⟨p, rfl⟩ := hsurj b
    have hp : σ p * p⁻¹ ∈ commutator P := by
      rw [← hab, map_mul, map_inv, ← hσB, hb, mul_inv_cancel]
    have hpW := mem_covW_of_sigma_mul_inv_mem h hp
    rw [(commutator_facts h).2.2, Subgroup.mem_sup_of_normal_right] at hpW
    obtain ⟨y, hy, c, hc, rfl⟩ := hpW
    refine MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, ?_⟩
    show Abelianization.of y = Abelianization.of (y * c)
    rw [map_mul, (hab c).mpr hc, mul_one]
  have hm : ∀ b : Abelianization P, b ^ 81 = 1 := by
    intro b
    obtain ⟨p, rfl⟩ := hsurj b
    have hp : p ^ 81 = 1 := by
      have := pow_card_eq_one' (G := P) (x := p)
      rwa [h.card_P] at this
    rw [← map_pow, hp, map_one]
  obtain ⟨ρ, hρ, -⟩ := exists_retraction_of_fixed_le σB hσB8 hm
    (by decide : 8 * 71 ≡ 1 [MOD 81]) _ hfix hfix'
  refine ⟨(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (ρ.comp Abelianization.of),
    fun z => ?_⟩
  obtain ⟨w, hw⟩ : ∃ w : (Abelianization.of.comp Zh.subtype : Zh →* Abelianization P).range,
      (w : Abelianization P) = Abelianization.of (z : P) :=
    ⟨⟨Abelianization.of (z : P), MonoidHom.mem_range.mpr ⟨z, rfl⟩⟩, rfl⟩
  have hρw : ρ (Abelianization.of (z : P)) = w := by
    rw [← hw]
    exact hρ w
  have hψw : (MonoidHom.ofInjective hinj).symm w = z := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hw
  show (MonoidHom.ofInjective hinj).symm (ρ (Abelianization.of (z : P))) = z
  rw [hρw, hψw]

end CFSG.RankThree.PartTwo.Sec8.Hering611
