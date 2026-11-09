module

public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OLineB
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OLines

section

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

end

end

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieOdd

variable {K : Type} [Field K]

theorem factorization_sq_mul {e R p : ℕ} (he : e ≠ 0) (hR : R ≠ 0) (hp : ¬ p ∣ R) :
    (e ^ 2 * R).factorization p = (e ^ 2).factorization p := by
  rw [Nat.factorization_mul (pow_ne_zero 2 he) hR, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hp, add_zero]

theorem not_dvd_cofactor {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpk : p ∣ k + 3) :
    ¬ p ∣ (k + 2) ^ 3 * (k + 1) * (k ^ 2 + 3 * k + 3) := by
  intro hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have h1 := hp.dvd_of_dvd_pow h
      have h2 : p ∣ 1 := (Nat.dvd_add_right h1).1 (by rwa [show k + 2 + 1 = k + 3 by ring])
      exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
    · have h2 : p ∣ 2 := (Nat.dvd_add_right h).1 (by rwa [show k + 1 + 2 = k + 3 by ring])
      have := Nat.le_of_dvd (by norm_num) h2
      omega
  · have h3 : p ∣ 3 := by
      have e : k ^ 2 + 3 * k + 3 = (k + 3) * k + 3 := by ring
      rw [e] at h
      exact (Nat.dvd_add_right (Dvd.dvd.mul_right hpk k)).1 h
    have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem pModel_statedSU [Finite K] {r p : ℕ} (hr : r.Prime) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : p ∣ r + 1) (hK : Nat.card K = (r ^ 1) ^ 2) :
    PModel p (StatedSU 3 (r ^ 1) K) (normOne K (r ^ 1)) := by
  have : Fact r.Prime := ⟨hr⟩
  have := Fintype.ofFinite K
  have hK' : Nat.card K = r ^ 2 := by rw [hK, pow_one]
  have hchar : CharP K r :=
    charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK'])
  have hr2 := hr.two_le
  refine ⟨monomialData_statedSU, ?_, ?_, ?_⟩
  · intro d hd i
    have hu := unitary_of_mem_statedSU hK hd
    rw [coe_diagHom, Matrix.diagonal_map (by simp [hr.ne_zero]), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal] at hu
    have hii := congrFun (congrFun hu i) i
    rw [diagonal_apply_eq, Matrix.one_apply_eq] at hii
    rw [mem_normOne]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
    exact hii
  · rw [card_statedSU_three hK, card_normOne hK]
    simp only [pow_one]
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    have e1 : (k + 2) ^ 2 - 1 = (k + 1) * (k + 3) := by
      have : (k + 2) ^ 2 = (k + 1) * (k + 3) + 1 := by ring
      omega
    have e2 : (k + 2) ^ 3 + 1 = (k + 3) * (k ^ 2 + 3 * k + 3) := by ring
    rw [e1, e2, show (k + 2) ^ 3 * ((k + 1) * (k + 3)) * ((k + 3) * (k ^ 2 + 3 * k + 3)) =
      (k + 2 + 1) ^ 2 * ((k + 2) ^ 3 * (k + 1) * (k ^ 2 + 3 * k + 3)) by ring]
    exact factorization_sq_mul (by omega) (by positivity)
      (not_dvd_cofactor hp hp5 (by simpa [show k + 2 + 1 = k + 3 by ring] using hpr))
  · rw [card_normOne hK, pow_one]
    exact hpr

theorem pTorusProp_of_model {X : Type} [Group X] {r p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : p ∣ r + 1) (hX : StatedClassicalModel X .PSU 3 r 1) : PTorusProp p X := by
  obtain ⟨⟨hr, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX
  have : Fact p.Prime := ⟨hp⟩
  exact PTorusProp.of_mulEquiv e ((pModel_statedSU hr hp hp5 hpr hK).torusProp hp5)

end CFSG.Quasithin.H13.NQCore.U3O
