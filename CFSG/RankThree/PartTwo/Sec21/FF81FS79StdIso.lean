module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Std
public import CFSG.RankThree.PartTwo.Sec21.CarterFS79Setup

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem J6.pow_three_of_mem_Efin : ∀ x ∈ J6.Efin, x ^ 3 = 1 := by decide +kernel

theorem J6.card_S6 : Nat.card J6.S6 = 720 := by
  rw [Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]

theorem J6.not_dvd_index_of_card_nine {E : Subgroup J6.S6} (hE : Nat.card E = 9) :
    ¬ 3 ∣ E.index := by
  have h := Subgroup.card_mul_index E
  rw [hE, J6.card_S6] at h
  have : E.index = 80 := by omega
  rw [this]
  norm_num


theorem FS79Hyp.exists_std (h : FS79Hyp b t b₁ b₂ J) :
    ∃ φ : ↥J ≃* J6.S6, φ ⟨b₁, h.b₁_mem⟩ = J6.c₁ ∧ φ ⟨b₂, h.b₂_mem⟩ = J6.c₂ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.J_perm
  set b₁' : ↥J := ⟨b₁, h.b₁_mem⟩ with hb₁'
  set b₂' : ↥J := ⟨b₂, h.b₂_mem⟩ with hb₂'
  set A : Subgroup ↥J := Subgroup.closure {b₁', b₂'} with hA
  set B₁ : Subgroup H := Subgroup.closure ({b₁, b₂} : Set H) with hB₁
  have hAB : A.map J.subtype = B₁ := by
    rw [hA, MonoidHom.map_closure, hB₁]
    congr 1
    ext x
    simp [hb₁', hb₂']
  have hcardA : Nat.card A = 9 := by
    have h1 : Nat.card (A.map J.subtype) = Nat.card A :=
      Subgroup.card_map_of_injective J.subtype_injective
    rw [← h1, hAB]
    simpa [hB₁] using h.E9.2
  set E₀ : Subgroup J6.S6 := A.map e.toMonoidHom with hE₀
  have hE₀card : Nat.card E₀ = 9 := by
    rw [hE₀, Subgroup.card_map_of_injective e.injective, hcardA]
  have hE₀3 : IsPGroup 3 E₀ := IsPGroup.of_card (n := 2) (by rw [hE₀card]; norm_num)
  have hE₆3 : IsPGroup 3 J6.E6 := IsPGroup.of_card (n := 2) (by rw [J6.card_E6]; norm_num)
  let S₀ : Sylow 3 J6.S6 := hE₀3.toSylow (J6.not_dvd_index_of_card_nine hE₀card)
  let S₁ : Sylow 3 J6.S6 := hE₆3.toSylow (J6.not_dvd_index_of_card_nine J6.card_E6)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J6.S6 S₀ S₁
  have hgE : E₀.map (MulAut.conj g).toMonoidHom = J6.E6 := by
    have := congrArg (fun S : Sylow 3 J6.S6 => (S : Subgroup J6.S6)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, S₀, S₁] at this
    exact this
  let e₁ : ↥J ≃* J6.S6 := e.trans (MulAut.conj g)
  have hmapA : A.map e₁.toMonoidHom = J6.E6 := by
    rw [← hgE, hE₀, Subgroup.map_map]
    rfl
  have hmem : ∀ x : ↥J, x ∈ A ↔ e₁ x ∈ J6.E6 := by
    intro x
    rw [← hmapA]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e₁.injective hyx
      rwa [this] at hy
  set x₀ : J6.S6 := e₁ b₁' with hx₀
  set y₀ : J6.S6 := e₁ b₂' with hy₀
  have hb₁A : b₁' ∈ A := Subgroup.subset_closure (by simp)
  have hb₂A : b₂' ∈ A := Subgroup.subset_closure (by simp)
  have hx₀E : x₀ ∈ J6.Efin := (hmem b₁').mp hb₁A
  have hy₀E : y₀ ∈ J6.Efin := (hmem b₂').mp hb₂A
  have hcl : Subgroup.closure ({x₀, y₀} : Set J6.S6) = J6.E6 := by
    rw [← hmapA, hA, MonoidHom.map_closure]
    congr 1
    ext z
    simp [hx₀, hy₀]
  have hx₀3 : x₀ ^ 3 = 1 := J6.pow_three_of_mem_Efin x₀ hx₀E
  have hy₀3 : y₀ ^ 3 = 1 := J6.pow_three_of_mem_Efin y₀ hy₀E
  have hcyc : ∀ z : J6.S6, z ^ 3 = 1 →
      Subgroup.closure ({x₀, y₀} : Set J6.S6) ≤ Subgroup.zpowers z → False := by
    intro z hz hle
    rw [hcl] at hle
    have h1 : Nat.card J6.E6 ≤ Nat.card (Subgroup.zpowers z) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hle)
    have h2 : Nat.card (Subgroup.zpowers z) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz)
    rw [J6.card_E6] at h1
    omega
  have hx₀1 : x₀ ≠ 1 := by
    intro h1
    refine hcyc y₀ hy₀3 ?_
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · rw [h1]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  have hy₀k : ∀ k : Fin 3, x₀ ^ k.val ≠ y₀ := by
    intro k hk
    refine hcyc x₀ hx₀3 ?_
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact Subgroup.mem_zpowers _
    · rw [← hk]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hmono6 : ∀ n ∈ J6.N6,
      (n * x₀ * n⁻¹ = x₀ ∨ n * x₀ * n⁻¹ = x₀⁻¹ ∨ n * x₀ * n⁻¹ = y₀ ∨ n * x₀ * n⁻¹ = y₀⁻¹) ∧
      (n * y₀ * n⁻¹ = x₀ ∨ n * y₀ * n⁻¹ = x₀⁻¹ ∨ n * y₀ * n⁻¹ = y₀ ∨ n * y₀ * n⁻¹ = y₀⁻¹) := by
    intro n hn
    have hnE : ∀ e' ∈ J6.Efin, n * e' * n⁻¹ ∈ J6.Efin := by
      simpa [J6.N6] using hn
    set n' : ↥J := e₁.symm n with hn'
    have hn'B : (n' : H) ∈ Nor B₁ := by
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      have hyJ : y ∈ J := by
        have : y ∈ A.map J.subtype := by rw [hAB]; exact hy
        obtain ⟨a, -, rfl⟩ := this
        exact a.2
      have hyA : (⟨y, hyJ⟩ : ↥J) ∈ A := by
        have : y ∈ A.map J.subtype := by rw [hAB]; exact hy
        obtain ⟨a, ha, rfl⟩ := this
        exact ha
      have h1 : e₁ ⟨y, hyJ⟩ ∈ J6.E6 := (hmem _).mp hyA
      have h2 : n * e₁ ⟨y, hyJ⟩ * n⁻¹ ∈ J6.Efin := hnE _ h1
      have h3 : n' * ⟨y, hyJ⟩ * n'⁻¹ ∈ A := by
        have e2 : e₁ (n' * ⟨y, hyJ⟩ * n'⁻¹) = n * e₁ ⟨y, hyJ⟩ * n⁻¹ := by simp [hn']
        rw [hmem, e2]
        exact h2
      have h4 : ((n' * ⟨y, hyJ⟩ * n'⁻¹ : ↥J) : H) ∈ A.map J.subtype := ⟨_, h3, rfl⟩
      rw [hAB] at h4
      simpa using h4
    have hmo := h.mono (n' : H) ⟨n'.2, hn'B⟩
    have transfer : ∀ (w z : ↥J), (n' : H) * (w : H) * (n' : H)⁻¹ = (z : H) →
        n * e₁ w * n⁻¹ = e₁ z := by
      intro w z hwz
      have h1 : n' * w * n'⁻¹ = z := Subtype.ext (by simpa using hwz)
      have h2 := congrArg e₁ h1
      simpa [hn'] using h2
    have hcase : ∀ w : ↥J, ((w : H) ∈ ({b₁, b₂} : Set H)) →
        (n * e₁ w * n⁻¹ = x₀ ∨ n * e₁ w * n⁻¹ = x₀⁻¹ ∨ n * e₁ w * n⁻¹ = y₀ ∨
          n * e₁ w * n⁻¹ = y₀⁻¹) := by
      intro w hw
      have hm := hmo (w : H) hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with hm | hm | hm | hm
      · exact Or.inl (transfer w b₁' hm)
      · exact Or.inr (Or.inl (by simpa [hx₀] using transfer w b₁'⁻¹ (by simpa using hm)))
      · exact Or.inr (Or.inr (Or.inl (transfer w b₂' hm)))
      · exact Or.inr (Or.inr (Or.inr (by simpa [hy₀] using transfer w b₂'⁻¹ (by simpa using hm))))
    exact ⟨hcase b₁' (by simp [hb₁']), hcase b₂' (by simp [hb₂'])⟩
  have hnp := J6.norm_pairs x₀ hx₀E y₀ hy₀E hx₀1 hy₀k hmono6
  rcases hnp with ⟨g', hg1, hg2⟩ | ⟨g', hg1, hg2⟩
  · refine ⟨e₁.trans (MulAut.conj g'), ?_, ?_⟩
    · simpa [MulAut.conj_apply] using hg1
    · simpa [MulAut.conj_apply] using hg2
  · obtain ⟨g'', hd1, hd2⟩ := J6.diag_std
    refine ⟨e₁.trans (((MulAut.conj g').trans (MulAut.conj g'')).trans
      CFSG.Quasithin.H13.U3.S6Out.phiEquiv), ?_, ?_⟩
    · have : (g'' * (g' * x₀ * g'⁻¹) * g''⁻¹) = g'' * J6.d * g''⁻¹ := by rw [hg1]
      simp only [MulEquiv.trans_apply, MulAut.conj_apply]
      change CFSG.Quasithin.H13.U3.S6Out.phi (g'' * (g' * x₀ * g'⁻¹) * g''⁻¹) = J6.c₁
      rw [this]
      exact hd1
    · have : (g'' * (g' * y₀ * g'⁻¹) * g''⁻¹) = g'' * J6.d' * g''⁻¹ := by rw [hg2]
      simp only [MulEquiv.trans_apply, MulAut.conj_apply]
      change CFSG.Quasithin.H13.U3.S6Out.phi (g'' * (g' * y₀ * g'⁻¹) * g''⁻¹) = J6.c₂
      rw [this]
      exact hd2

end CFSG.RankThree.PartTwo.Sec21.FF81
