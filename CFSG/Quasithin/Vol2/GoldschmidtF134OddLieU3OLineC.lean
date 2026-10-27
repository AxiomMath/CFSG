module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OLineB
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OLines

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieOdd

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ} {p : ℕ}

namespace PModel

variable (h : PModel p H M) {ζ : Kˣ} (hζM : ζ ∈ M) (hζ : orderOf ζ = p) [hp : Fact p.Prime]
  (hp5 : 5 ≤ p)

include h hζM hζ hp5

section Lines

variable {c₂ c₃ : ℕ}

theorem xB_one_ne_one : h.xB hζM 1 ≠ 1 := by
  intro h1
  have := (h.proj_s12H_comm_iff hζM hζ hp5 1 1).1 (by
    rw [xB] at h1
    rw [h1]
    simp)
  apply three_ne_zero_zmod (p := p) (by omega)
  push_cast at this
  linear_combination this

theorem xB_two_ne_one (hc₂ : (1 : ZMod p) + 2 * c₂ = 0) : h.xB hζM c₂ ≠ 1 := by
  intro h1
  have := (h.proj_s01H_comm_iff hζM hζ hp5 1 c₂).1 (by
    rw [xB] at h1
    rw [h1]
    simp)
  apply three_ne_zero_zmod (p := p) (by omega)
  push_cast at this
  linear_combination hc₂ - 2 * this

theorem xB_three_ne_one (hc₃ : (2 : ZMod p) + c₃ = 0) : h.xB hζM c₃ ≠ 1 := by
  intro h1
  have := (h.proj_s01H_comm_iff hζM hζ hp5 1 c₃).1 (by
    rw [xB] at h1
    rw [h1]
    simp)
  apply three_ne_zero_zmod (p := p) (by omega)
  push_cast at this
  linear_combination hc₃ - this

omit hp hp5 in
theorem mem_pstd_dd_one_zero : proj H (h.ddH hζM 1 0) ∈ pstd p H M :=
  mem_pstd.2 ⟨_, dd_mem_omegaP hζM hζ 1 0, rfl⟩

theorem notCentralizing_lineB_one : NotCentralizing (pstd p H M) (h.lineB hζM 1) := by
  have hx : proj H h.s01H * h.xB hζM 1 = h.xB hζM 1 * proj H h.s01H :=
    (h.proj_s01H_comm_iff hζM hζ hp5 1 1).2 rfl
  refine ⟨proj H h.s01H, fun y hy => comm_of_mem_zpowers hx hy, fun hall => ?_⟩
  have := (h.proj_s01H_comm_iff hζM hζ hp5 1 0).1 (hall _ (h.mem_pstd_dd_one_zero hζM hζ))
  simp at this

theorem notCentralizing_lineB_two (hc₂ : (1 : ZMod p) + 2 * c₂ = 0) :
    NotCentralizing (pstd p H M) (h.lineB hζM c₂) := by
  have hx : proj H h.s12H * h.xB hζM c₂ = h.xB hζM c₂ * proj H h.s12H :=
    (h.proj_s12H_comm_iff hζM hζ hp5 1 c₂).2 (by push_cast; linear_combination hc₂)
  refine ⟨proj H h.s12H, fun y hy => comm_of_mem_zpowers hx hy, fun hall => ?_⟩
  have := (h.proj_s12H_comm_iff hζM hζ hp5 1 0).1 (hall _ (h.mem_pstd_dd_one_zero hζM hζ))
  simp at this

theorem notCentralizing_lineB_three (hc₃ : (2 : ZMod p) + c₃ = 0) :
    NotCentralizing (pstd p H M) (h.lineB hζM c₃) := by
  have hx : proj H h.s02H * h.xB hζM c₃ = h.xB hζM c₃ * proj H h.s02H :=
    (h.proj_s02H_comm_iff hζM hζ hp5 1 c₃).2 (by push_cast; linear_combination hc₃)
  refine ⟨proj H h.s02H, fun y hy => comm_of_mem_zpowers hx hy, fun hall => ?_⟩
  have := (h.proj_s02H_comm_iff hζM hζ hp5 1 0).1 (hall _ (h.mem_pstd_dd_one_zero hζM hζ))
  apply two_ne_zero_zmod (p := p) (by omega)
  simpa using this

theorem lineB_one_ne_two (hc₂ : (1 : ZMod p) + 2 * c₂ = 0) :
    h.lineB hζM 1 ≠ h.lineB hζM c₂ := by
  intro heq
  have hx : proj H h.s01H * h.xB hζM 1 = h.xB hζM 1 * proj H h.s01H :=
    (h.proj_s01H_comm_iff hζM hζ hp5 1 1).2 rfl
  have hmem : h.xB hζM c₂ ∈ h.lineB hζM 1 := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  have := (h.proj_s01H_comm_iff hζM hζ hp5 1 c₂).1 (comm_of_mem_zpowers hx hmem)
  apply three_ne_zero_zmod (p := p) (by omega)
  push_cast at this
  linear_combination hc₂ - 2 * this

theorem lineB_one_ne_three (hc₃ : (2 : ZMod p) + c₃ = 0) :
    h.lineB hζM 1 ≠ h.lineB hζM c₃ := by
  intro heq
  have hx : proj H h.s01H * h.xB hζM 1 = h.xB hζM 1 * proj H h.s01H :=
    (h.proj_s01H_comm_iff hζM hζ hp5 1 1).2 rfl
  have hmem : h.xB hζM c₃ ∈ h.lineB hζM 1 := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  have := (h.proj_s01H_comm_iff hζM hζ hp5 1 c₃).1 (comm_of_mem_zpowers hx hmem)
  apply three_ne_zero_zmod (p := p) (by omega)
  push_cast at this
  linear_combination hc₃ - this

theorem lineB_two_ne_three (hc₂ : (1 : ZMod p) + 2 * c₂ = 0) (hc₃ : (2 : ZMod p) + c₃ = 0) :
    h.lineB hζM c₂ ≠ h.lineB hζM c₃ := by
  intro heq
  have hx : proj H h.s12H * h.xB hζM c₂ = h.xB hζM c₂ * proj H h.s12H :=
    (h.proj_s12H_comm_iff hζM hζ hp5 1 c₂).2 (by push_cast; linear_combination hc₂)
  have hmem : h.xB hζM c₃ ∈ h.lineB hζM c₂ := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  have := (h.proj_s12H_comm_iff hζM hζ hp5 1 c₃).1 (comm_of_mem_zpowers hx hmem)
  apply three_ne_zero_zmod (p := p) (by omega)
  push_cast at this
  linear_combination 2 * hc₃ - this

theorem eq_lineB_of_notCentralizing [Finite K] (hc₂ : (1 : ZMod p) + 2 * c₂ = 0)
    (hc₃ : (2 : ZMod p) + c₃ = 0) {Q : Subgroup (StatedProj H)} (hQP : Q ≤ pstd p H M)
    (hQp : Nat.card Q = p) (hQ : NotCentralizing (pstd p H M) Q) :
    Q = h.lineB hζM 1 ∨ Q = h.lineB hζM c₂ ∨ Q = h.lineB hζM c₃ := by
  obtain ⟨g, hgQ, hgP⟩ := hQ
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQp]; exact hp.out.ne_zero)
  have hnt : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.1 (by rw [hQp]; exact hp.out.one_lt)
  obtain ⟨q, hq1⟩ := exists_ne (1 : Q)
  have hq1' : (q : StatedProj H) ≠ 1 := fun h' => hq1 (Subtype.ext h')
  obtain ⟨t, ht, hty⟩ := mem_pstd.1 (hQP q.2)
  obtain ⟨a, b, -, -, hdd⟩ := exists_dd_of_mem_omegaP hζ ht
  have hq : (q : StatedProj H) = proj H (h.ddH hζM a b) := by
    rw [← hty]
    congr 1
    exact Subtype.ext hdd
  obtain ⟨g0, rfl⟩ := proj_surjective (H := H) g
  have hgq : proj H g0 * proj H (h.ddH hζM a b) = proj H (h.ddH hζM a b) * proj H g0 := by
    rw [← hq]
    exact hgQ q q.2
  have hnd : (a : ZMod p) = b ∨ (a : ZMod p) + 2 * b = 0 ∨ 2 * (a : ZMod p) + b = 0 := by
    by_contra hcon
    push Not at hcon
    exact hgP (h.commute_pstd_of_distinct hζM hζ hp5 hcon.1 hcon.2.1 hcon.2.2 hgq)
  have hQeq : Q = Subgroup.zpowers (q : StatedProj H) := eq_zpowers_of_card_prime hQp q.2 hq1'
  have key : ∀ c : ℕ, Nat.card (h.lineB hζM c) = p → (q : StatedProj H) ∈ h.lineB hζM c →
      Q = h.lineB hζM c := fun c hB hmem => by
    rw [hQeq]
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hmem) (by
      rw [hB, ← hQeq, hQp])
  have hone := h.xB_one_ne_one hζM hζ hp5
  have htwo := h.xB_two_ne_one hζM hζ hp5 hc₂
  have hthree := h.xB_three_ne_one hζM hζ hp5 hc₃
  rcases hnd with hc | hc | hc
  · left
    refine key 1 (card_zpowers_prime (h.xB_pow_p hζM hζ 1) hone) ?_
    rw [hq, h.proj_ddH_eq_pow_xB hζM hζ 1 (by rw [← hc]; simp)]
    exact Subgroup.npow_mem_zpowers _ _
  · right
    left
    refine key c₂ (card_zpowers_prime (h.xB_pow_p hζM hζ c₂) htwo) ?_
    rw [hq, h.proj_ddH_eq_pow_xB hζM hζ c₂ (eq_mul_of_add_two_mul hc hc₂)]
    exact Subgroup.npow_mem_zpowers _ _
  · right
    right
    refine key c₃ (card_zpowers_prime (h.xB_pow_p hζM hζ c₃) hthree) ?_
    rw [hq, h.proj_ddH_eq_pow_xB hζM hζ c₃ (eq_mul_of_two_mul_add hc hc₃)]
    exact Subgroup.npow_mem_zpowers _ _

theorem lineSet_pstd [Finite K] (hc₂ : (1 : ZMod p) + 2 * c₂ = 0) (hc₃ : (2 : ZMod p) + c₃ = 0) :
    lineSet p (pstd p H M) (NotCentralizing (pstd p H M)) =
      {h.lineB hζM 1, h.lineB hζM c₂, h.lineB hζM c₃} := by
  have hone := h.xB_one_ne_one hζM hζ hp5
  have htwo := h.xB_two_ne_one hζM hζ hp5 hc₂
  have hthree := h.xB_three_ne_one hζM hζ hp5 hc₃
  ext Q
  constructor
  · rintro ⟨hQP, hQp, hQ⟩
    rcases h.eq_lineB_of_notCentralizing hζM hζ hp5 hc₂ hc₃ hQP hQp hQ with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨h.lineB_le_pstd hζM hζ 1, card_zpowers_prime (h.xB_pow_p hζM hζ 1) hone,
        h.notCentralizing_lineB_one hζM hζ hp5⟩
    · exact ⟨h.lineB_le_pstd hζM hζ c₂, card_zpowers_prime (h.xB_pow_p hζM hζ c₂) htwo,
        h.notCentralizing_lineB_two hζM hζ hp5 hc₂⟩
    · exact ⟨h.lineB_le_pstd hζM hζ c₃, card_zpowers_prime (h.xB_pow_p hζM hζ c₃) hthree,
        h.notCentralizing_lineB_three hζM hζ hp5 hc₃⟩

omit hζM hζ in
theorem oddLines_pstd [Finite K] : OddLines p (pstd p H M) := by
  obtain ⟨ζ, hζM, hζ⟩ := h.exists_orderP
  obtain ⟨c₂, c₃, hc₂, hc₃⟩ := exists_special (p := p) (by omega)
  refine ⟨NotCentralizing (pstd p H M), fun α hα Q hQ => hQ.map α hα, ?_⟩
  rw [h.lineSet_pstd hζM hζ hp5 hc₂ hc₃, Set.ncard_eq_three.2 ⟨_, _, _,
    h.lineB_one_ne_two hζM hζ hp5 hc₂, h.lineB_one_ne_three hζM hζ hp5 hc₃,
    h.lineB_two_ne_three hζM hζ hp5 hc₂ hc₃, rfl⟩]
  exact ⟨1, rfl⟩

omit hζM hζ in
theorem torusProp [Finite K] : PTorusProp p (StatedProj H) := by
  intro P hexp
  refine ⟨h.comm_of_exp (by omega) hexp, fun hP => ?_⟩
  obtain ⟨φ, hφ⟩ := h.exists_map_eq_pstd (by omega) hP hexp
  exact OddLines.of_map_eq φ hφ (h.oddLines_pstd hp5)

end Lines

end PModel

end CFSG.Quasithin.H13.NQCore.U3O
