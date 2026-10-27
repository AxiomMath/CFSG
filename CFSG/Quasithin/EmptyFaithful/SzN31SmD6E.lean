module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6D
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6C
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6GrpC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11
open scoped Pointwise

namespace SmD6

open CntLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {Γ A : Subgroup (GLV V)}

theorem Ctx.three_pow_le (hC : Ctx Γ A) {n : ℕ} (hn : 3 ^ n ∣ Nat.card ↥Γ) : 3 ^ n ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Sylow 3 ↥Γ := default
  have hS := S.card_eq_multiplicity
  have hSle : Nat.card (S : Subgroup ↥Γ) ≤ 27 := by
    have := hC.three ((S : Subgroup ↥Γ).map Γ.subtype) (Subgroup.map_subtype_le _)
      (S.isPGroup'.map Γ.subtype)
    rwa [Subgroup.card_map_of_injective Γ.subtype_injective] at this
  have hv : n ≤ (Nat.card ↥Γ).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').1 hn
  calc 3 ^ n ≤ 3 ^ (Nat.card ↥Γ).factorization 3 := Nat.pow_le_pow_right (by norm_num) hv
    _ = Nat.card (S : Subgroup ↥Γ) := hS.symm
    _ ≤ 27 := hSle

theorem Ctx.card_le_nine (hC : Ctx Γ A) (h3 : 3 ∣ ((CFSG.Open.pCoreOf 3 Γ).subgroupOf Γ).index) :
    Nat.card ↥(CFSG.Open.pCoreOf 3 Γ) ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := (isPGroup_pCoreOf 3 Γ).exists_card_eq
  have hcard : Nat.card ((CFSG.Open.pCoreOf 3 Γ).subgroupOf Γ) = 3 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 3 Γ)).toEquiv, ha]
  have hmul := Subgroup.card_mul_index ((CFSG.Open.pCoreOf 3 Γ).subgroupOf Γ)
  rw [hcard] at hmul
  obtain ⟨m, hm⟩ := h3
  have hdvd : 3 ^ (a + 1) ∣ Nat.card ↥Γ := ⟨m, by rw [← hmul, hm, pow_succ]; ring⟩
  have := hC.three_pow_le hdvd
  rw [ha]
  have h2 : 3 ^ (a + 1) = 3 * 3 ^ a := by ring
  omega

omit [Finite V] in
theorem normal_isPGroup_le_pCoreOf (p : ℕ) (Γ : Subgroup (GLV V)) {N : Subgroup ↥Γ} (hN : N.Normal)
    (hp : IsPGroup p N) : N ≤ (CFSG.Open.pCoreOf p Γ).subgroupOf Γ := by
  intro g hg
  rw [Subgroup.mem_subgroupOf]
  have h1 : g ∈ CFSG.pCore p ↥Γ := le_sSup (show N ∈ {K : Subgroup ↥Γ | K.Normal ∧ IsPGroup p K} from
    ⟨hN, hp⟩) hg
  have h2 : g ∈ CFSG.Open.pCore p ↥Γ := by exact h1
  exact Subgroup.mem_map.2 ⟨g, h2, rfl⟩

theorem Ctx.false_of_planes (hC : Ctx Γ A) {W : Fin 3 → Submodule (ZMod 2) V}
    (hW : ThreePlanes Γ (CFSG.Open.pCoreOf 3 Γ) W) : False := by
  set P := CFSG.Open.pCoreOf 3 Γ with hPdef
  have hP3 : IsPGroup 3 P := isPGroup_pCoreOf 3 Γ
  have hfix : fixedSpace P = ⊥ := hC.fixedSpace_eq_bot
  have hPn : ∀ γ ∈ Γ, ∀ n ∈ P, γ * n * γ⁻¹ ∈ P := pCoreOf_normal_conj 3 Γ
  have h9le : 9 ≤ Nat.card P := hC.nine_le_card
  rcases hW.kernels_eq_or_ne hP3 hfix hPn with ⟨h01, h12⟩ | ⟨h01, h02, h12⟩
  · have := hW.card_le_three_of_eq hP3 hfix h01 h12
    omega
  · have hdist : ∀ i j : Fin 3, i ≠ j → centralizerOn P (W i) ≠ centralizerOn P (W j) := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact h01
      · exact h02
      · exact Ne.symm h01
      · exact absurd rfl hij
      · exact h12
      · exact Ne.symm h02
      · exact Ne.symm h12
      · exact absurd rfl hij
    have h3 := hW.three_dvd_index_of_distinct hP3 hfix hPn hdist
    have h9 : Nat.card P = 9 := le_antisymm (hC.card_le_nine h3) h9le
    have hK : ∀ i, Nat.card (centralizerOn P (W i)) = 3 := fun i => by
      have := card_eq_three_mul_card_centralizerOn hP3 hfix (hW.inv i) (hW.rank i)
      omega
    have hKP : ∀ i, centralizerOn P (W i) ≤ P := fun i k hk => (mem_centralizerOn.1 hk).1
    obtain ⟨h, hhP, hh1, hh0, hh1', hh2, -, hexp, hmem⟩ := exists_outside_three_subgroups
      (P := P) (K₀ := centralizerOn P (W 0)) (K₁ := centralizerOn P (W 1))
      (K₂ := centralizerOn P (W 2)) h9 (hKP 0) (hKP 1) (hKP 2) (hK 0) (hK 1) (hK 2) h01 h02 h12
    have hhK : ∀ l, h ∉ centralizerOn P (W l) := by
      intro l
      fin_cases l
      · exact hh0
      · exact hh1'
      · exact hh2
    have hΓh : h ∈ Γ := pCoreOf_le 3 Γ hhP
    set h' : ↥Γ := ⟨h, hΓh⟩ with hh'def
    have hhP' : h' ∈ (CFSG.Open.pCoreOf 3 Γ).subgroupOf Γ := hhP
    refine not_three_dvd_index_of_normal_line ((CFSG.Open.pCoreOf 3 Γ).subgroupOf Γ) ?_ ?_ ?_ ?_
      hhP' ?_ ?_ h3
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 3 Γ)).toEquiv, h9]
    · intro x hx
      exact Subtype.ext (hexp x.1 hx)
    · intro g hg
      have : (g : GLV V) ∈ P := by
        refine hC.mem_pCoreOf_of_centralizes g.2 fun x hx => ?_
        have := hg ⟨x, pCoreOf_le 3 Γ hx⟩ hx
        exact congrArg Subtype.val this
      exact this
    · intro N hN hNp
      exact normal_isPGroup_le_pCoreOf 3 Γ hN hNp
    · intro h1
      exact hh1 (congrArg Subtype.val h1)
    · intro g
      have hgΓ : (g : GLV V) ∈ Γ := g.2
      have hxP : (g : GLV V) * h * (g : GLV V)⁻¹ ∈ P := hPn g hgΓ h hhP
      have hxK : ∀ j, (g : GLV V) * h * (g : GLV V)⁻¹ ∉ centralizerOn P (W j) := by
        intro j hxj
        obtain ⟨l, hl⟩ := hW.conj_mem_of_distinct hP3 hfix hPn hdist (Γ.inv_mem hgΓ) j
        apply hhK l
        refine mem_centralizerOn.2 ⟨hhP, fun w hw => ?_⟩
        rw [← hl] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        have hfixx := (mem_centralizerOn.1 hxj).2 w' hw'
        have h1 : (g : GLV V) (h ((g : GLV V).symm w')) = w' := hfixx
        have h2 := congrArg (g : GLV V).symm h1
        rw [LinearEquiv.symm_apply_apply] at h2
        show h (((g : GLV V)⁻¹ : GLV V) w') = ((g : GLV V)⁻¹ : GLV V) w'
        exact h2
      have hzp := hmem _ hxP (hxK 0) (hxK 1) (hxK 2)
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hzp
      exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩


end SmD6

end CFSG.Quasithin.SzN31
