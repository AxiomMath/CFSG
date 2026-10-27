module

public import CFSG.Quasithin.Background.GoldschmidtS146PGroups
public import CFSG.Quasithin.Background.HL42Aut
public import CFSG.Quasithin.H13.VolIAutSLFive

public section

namespace CFSG.Quasithin

namespace SBc15

open CFSG.Quasithin.GoldS146P

section General

instance instNormalRangeConj (L : Type*) [Group L] :
    (MulAut.conj : L →* MulAut L).range.Normal := by
  constructor
  rintro _ ⟨g, rfl⟩ β
  exact ⟨β g, by ext x; simp [MulAut.conj_apply]⟩

variable {L : Type*} [Group L] [Finite L]

theorem index_conj_range_le [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a)
    (hcard : Nat.card (MulAut L) ≤ 2 * Nat.card L) :
    (MulAut.conj : L →* MulAut L).range.index ≤ 2 := by
  have hinj := conj_injective_of_simple hnc
  have hinn : Nat.card (MulAut.conj : L →* MulAut L).range = Nat.card L :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx := (MulAut.conj : L →* MulAut L).range.index_mul_card
  rw [hinn] at hidx
  have hpos : 0 < Nat.card L := Nat.card_pos
  have h1 : (MulAut.conj : L →* MulAut L).range.index * Nat.card L ≤ 2 * Nat.card L :=
    hidx ▸ hcard
  exact Nat.le_of_mul_le_mul_right h1 hpos

theorem isPGroup_quotient_conj_range [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a)
    (hcard : Nat.card (MulAut L) ≤ 2 * Nat.card L) :
    IsPGroup 2 (MulAut L ⧸ (MulAut.conj : L →* MulAut L).range) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut L) := finite_mulAut_of_finite L
  have hidx := index_conj_range_le hnc hcard
  rw [IsPGroup.iff_card]
  have hpos : 0 < Nat.card (MulAut L ⧸ (MulAut.conj : L →* MulAut L).range) := Nat.card_pos
  have hq : (MulAut.conj : L →* MulAut L).range.index =
      Nat.card (MulAut L ⧸ (MulAut.conj : L →* MulAut L).range) := Subgroup.index_eq_card _
  rcases (by omega : Nat.card (MulAut L ⧸ (MulAut.conj : L →* MulAut L).range) = 1 ∨
      Nat.card (MulAut L ⧸ (MulAut.conj : L →* MulAut L).range) = 2) with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

variable {Γ K : Type*} [Group Γ] [Finite Γ] [Group K]

theorem range_comp_eq_conj [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a)
    (hcard : Nat.card (MulAut L) ≤ 2 * Nat.card L) [Group.IsPerfect K] [Nontrivial K]
    (ψ : Γ →* MulAut L) (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) (j : K →* Γ)
    (hj : Function.Injective j) (hjn : j.range.Normal) :
    (ψ.comp j).range = (MulAut.conj : L →* MulAut L).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut L) := finite_mulAut_of_finite L
  have hquot := isPGroup_quotient_conj_range hnc hcard
  have : Group.IsNilpotent (MulAut L ⧸ (MulAut.conj : L →* MulAut L).range) := hquot.isNilpotent
  set R := (ψ.comp j).range with hR
  have : Group.IsPerfect R := Group.IsPerfect.range (ψ.comp j)
  have hRn : R.Normal := by
    rw [hR, MonoidHom.range_comp]
    exact hjn.map ψ hψ
  have hRInn : R ≤ (MulAut.conj : L →* MulAut L).range :=
    perfect_le_of_solvable_quotient _ (Subgroup.isPerfect_iff.mp inferInstance)
  refine le_antisymm hRInn ?_
  have hR'n : (R.comap (MulAut.conj : L →* MulAut L)).Normal := hRn.comap _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.comap (MulAut.conj : L →* MulAut L)) with h | h
  · exfalso
    have hR1 : ∀ k : K, ψ (j k) = 1 := by
      intro k
      have hk : ψ (j k) ∈ R := ⟨k, rfl⟩
      obtain ⟨s, hs⟩ := hRInn hk
      have hs' : s ∈ R.comap (MulAut.conj : L →* MulAut L) := by
        rw [Subgroup.mem_comap, hs]
        exact hk
      rw [h, Subgroup.mem_bot] at hs'
      rw [← hs, hs', map_one]
    have hK2 : IsPGroup 2 K := by
      refine hker.of_injective (j.codRestrict ψ.ker fun k => MonoidHom.mem_ker.mpr (hR1 k)) ?_
      intro a b hab
      exact hj (congrArg Subtype.val hab)
    have : Finite K := Finite.of_injective j hj
    have : Group.IsNilpotent K := hK2.isNilpotent
    exact Group.IsPerfect.not_isSolvable K inferInstance
  · rintro _ ⟨s, rfl⟩
    have hs : s ∈ R.comap (MulAut.conj : L →* MulAut L) := by
      rw [h]
      trivial
    exact hs

theorem exists_theta_of_aut [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a)
    (hcard : Nat.card (MulAut L) ≤ 2 * Nat.card L) [Group.IsPerfect K] [Nontrivial K]
    (ψ : Γ →* MulAut L) (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) (j : K →* Γ)
    (hj : Function.Injective j) (hjn : j.range.Normal) :
    ∃ θ : K →* L, Function.Surjective θ ∧ IsPGroup 2 θ.ker := by
  have hR := range_comp_eq_conj hnc hcard ψ hψ hker j hj hjn
  have hconj : Function.Injective (MulAut.conj : L →* MulAut L) := conj_injective_of_simple hnc
  have hmem : ∀ k : K, (ψ.comp j) k ∈ (MulAut.conj : L →* MulAut L).range := fun k =>
    hR ▸ ⟨k, rfl⟩
  let e : L ≃* (MulAut.conj : L →* MulAut L).range := MonoidHom.ofInjective hconj
  let θ : K →* L := e.symm.toMonoidHom.comp ((ψ.comp j).codRestrict _ hmem)
  refine ⟨θ, ?_, ?_⟩
  · intro s
    have hs : (MulAut.conj : L →* MulAut L) s ∈ (ψ.comp j).range := hR ▸ ⟨s, rfl⟩
    obtain ⟨k, hk⟩ := hs
    refine ⟨k, ?_⟩
    show e.symm ⟨(ψ.comp j) k, hmem k⟩ = s
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hk
  · have hθ : ∀ x : K, θ x = 1 → ψ (j x) = 1 := by
      intro x hx
      have h1 : (⟨(ψ.comp j) x, hmem x⟩ : (MulAut.conj : L →* MulAut L).range) = 1 :=
        (e.symm.map_eq_one_iff).mp hx
      exact congrArg Subtype.val h1
    refine hker.of_injective ((j.comp θ.ker.subtype).codRestrict ψ.ker fun x => ?_) ?_
    · exact MonoidHom.mem_ker.mpr (hθ x x.2)
    · intro a b hab
      exact Subtype.ext (hj (congrArg Subtype.val hab))

theorem exists_mul_eq_of_aut [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a)
    (hcard : Nat.card (MulAut L) ≤ 2 * Nat.card L) [Group.IsPerfect K] [Nontrivial K]
    (ψ : Γ →* MulAut L) (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) (j : K →* Γ)
    (hj : Function.Injective j) (hjn : j.range.Normal) {P : Subgroup Γ} (hP : IsPGroup 2 P)
    (hPi : ¬ 2 ∣ P.index) (g : Γ) : ∃ k : K, ∃ y ∈ P, g = j k * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut L) := finite_mulAut_of_finite L
  have hquot := isPGroup_quotient_conj_range hnc hcard
  have hR := range_comp_eq_conj hnc hcard ψ hψ hker j hj hjn
  set ρ : Γ →* MulAut L ⧸ (MulAut.conj : L →* MulAut L).range :=
    (QuotientGroup.mk' _).comp ψ with hρ
  have hρs : Function.Surjective ρ := (QuotientGroup.mk'_surjective _).comp hψ
  have htop : P.map ρ = ⊤ := by
    have h1 : (P.map ρ).index ∣ P.index := Subgroup.index_map_dvd P hρs
    obtain ⟨m, hm⟩ := hquot.index (P.map ρ)
    rw [← Subgroup.index_eq_one]
    by_contra hne
    have hm0 : m ≠ 0 := fun h0 => hne (by rw [hm, h0, pow_zero])
    exact hPi ((dvd_pow_self 2 hm0).trans (hm ▸ h1))
  have hg : ρ g ∈ P.map ρ := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨y, hyP, hy⟩ := hg
  have h1 : ψ (y⁻¹ * g) ∈ (MulAut.conj : L →* MulAut L).range := by
    have : ρ (y⁻¹ * g) = 1 := by rw [map_mul, map_inv, hy, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  rw [← hR] at h1
  obtain ⟨k, hk⟩ := h1
  have hz : (j k)⁻¹ * (y⁻¹ * g) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have hk' : ψ (j k) = ψ (y⁻¹ * g) := hk
    rw [hk', inv_mul_cancel]
  have hzP : (j k)⁻¹ * (y⁻¹ * g) ∈ P := hker.le_sylow_of_normal (hP.toSylow hPi) hz
  obtain ⟨k', hk'⟩ := hjn.conj_mem (j k) ⟨k, rfl⟩ y
  refine ⟨k', y * ((j k)⁻¹ * (y⁻¹ * g)), P.mul_mem hyP hzP, ?_⟩
  rw [hk']
  group

end General

section SL

variable {n : ℕ}

theorem card_mulAut_sl_le (hn : n = 4 ∨ n = 5) :
    Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) ≤
      2 * Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  rcases hn with rfl | rfl
  · exact CFSG.Quasithin.H.L4.card_mulAut_SL_four
  · exact CFSG.Quasithin.H13.VolI.autSLFiveTwo_holds

variable {Γ K : Type*} [Group Γ] [Finite Γ] [Group K] [Group.IsPerfect K] [Nontrivial K]

theorem exists_theta_sl (hn : n = 4 ∨ n = 5)
    (ψ : Γ →* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) (hψ : Function.Surjective ψ)
    (hker : IsPGroup 2 ψ.ker) (j : K →* Γ) (hj : Function.Injective j) (hjn : j.range.Normal) :
    ∃ θ : K →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      Function.Surjective θ ∧ IsPGroup 2 θ.ker := by
  have := sl_simple n (by omega)
  exact exists_theta_of_aut (sl_nonabelian n (by omega)) (card_mulAut_sl_le hn) ψ hψ hker j hj
    hjn

theorem exists_mul_eq_sl (hn : n = 4 ∨ n = 5)
    (ψ : Γ →* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) (hψ : Function.Surjective ψ)
    (hker : IsPGroup 2 ψ.ker) (j : K →* Γ) (hj : Function.Injective j) (hjn : j.range.Normal)
    {P : Subgroup Γ} (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index) (g : Γ) :
    ∃ k : K, ∃ y ∈ P, g = j k * y := by
  have := sl_simple n (by omega)
  exact exists_mul_eq_of_aut (sl_nonabelian n (by omega)) (card_mulAut_sl_le hn) ψ hψ hker j hj
    hjn hP hPi g

end SL

end SBc15

end CFSG.Quasithin
