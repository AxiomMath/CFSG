module

public import CFSG.Quasithin.EmptyFaithful.S146zYFOStd
public import CFSG.Quasithin.EmptyFaithful.S146zYFOLines

public section

namespace CFSG.Quasithin.S146zY

namespace FiveOdd

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieOdd

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ}

@[expose] def NotCentralizing {X : Type*} [Group X] (P Q : Subgroup X) : Prop :=
  ∃ g : X, (∀ y ∈ Q, g * y = y * g) ∧ ¬ ∀ y ∈ P, g * y = y * g

theorem NotCentralizing.map {X : Type*} [Group X] {P : Subgroup X} (α : X ≃* X)
    (hα : P.map α.toMonoidHom = P) {Q : Subgroup X} (h : NotCentralizing P Q) :
    NotCentralizing P (Q.map α.toMonoidHom) := by
  obtain ⟨g, hgQ, hgP⟩ := h
  refine ⟨α g, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    show α g * α y = α y * α g
    rw [← map_mul, ← map_mul, hgQ y hy]
  · intro hall
    apply hgP
    intro y hy
    have hy' : α y ∈ P := by
      rw [← hα]
      exact ⟨y, hy, rfl⟩
    have := hall (α y) hy'
    rw [← map_mul, ← map_mul] at this
    exact α.injective this

theorem comm_of_mem_zpowers {X : Type*} [Group X] {g x y : X} (hx : g * x = x * g)
    (hy : y ∈ Subgroup.zpowers x) : g * y = y * g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ((show Commute g x from hx).zpow_right k).eq

theorem eq_zpowers_of_card_five {X : Type*} [Group X] {Q : Subgroup X} (hQ : Nat.card Q = 5)
    {q : X} (hq : q ∈ Q) (hq1 : q ≠ 1) : Q = Subgroup.zpowers q := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  have hord : orderOf q ∣ 5 := by
    have := orderOf_dvd_natCard (⟨q, hq⟩ : Q)
    rwa [Subgroup.orderOf_mk, hQ] at this
  have hord5 : orderOf q = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).1 hord with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hq1
    · exact h
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hq) ?_
  rw [Nat.card_zpowers, hord5, hQ]

theorem card_zpowers_five {X : Type*} [Group X] {q : X} (hq5 : q ^ 5 = 1) (hq1 : q ≠ 1) :
    Nat.card (Subgroup.zpowers q) = 5 := by
  have hord : orderOf q ∣ 5 := orderOf_dvd_of_pow_eq_one hq5
  rw [Nat.card_zpowers]
  rcases (Nat.dvd_prime Nat.prime_five).1 hord with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hq1
  · exact h

theorem s01_comm_diag_iff (d : Fin 3 → Kˣ) :
    (s01GL : GL (Fin 3) K) * diagHom 3 d = diagHom 3 d * s01GL ↔ d 1 = d 0 := by
  rw [← mul_inv_eq_iff_eq_mul, s01GL_conj_diagHom, (diagHom_injective 3).eq_iff]
  constructor
  · intro h
    simpa using congrFun h 0
  · intro h
    funext i
    fin_cases i <;> simp [h]

theorem s12_comm_diag_iff (d : Fin 3 → Kˣ) :
    (s12GL : GL (Fin 3) K) * diagHom 3 d = diagHom 3 d * s12GL ↔ d 2 = d 1 := by
  rw [← mul_inv_eq_iff_eq_mul, s12GL_conj_diagHom, (diagHom_injective 3).eq_iff]
  constructor
  · intro h
    simpa using congrFun h 1
  · intro h
    funext i
    fin_cases i <;> simp [h]

theorem s02_comm_diag_iff (d : Fin 3 → Kˣ) :
    (s02GL : GL (Fin 3) K) * diagHom 3 d = diagHom 3 d * s02GL ↔ d 2 = d 0 := by
  rw [← mul_inv_eq_iff_eq_mul, s02GL_conj_diagHom, (diagHom_injective 3).eq_iff]
  constructor
  · intro h
    simpa using congrFun h 0
  · intro h
    funext i
    fin_cases i <;> simp [h]

section Dd

variable {ζ : Kˣ}

theorem s01_comm_dd_iff (hζ : orderOf ζ = 5) (a b : ℕ) :
    (s01GL : GL (Fin 3) K) * dd ζ a b = dd ζ a b * s01GL ↔ b % 5 = a % 5 := by
  unfold dd
  rw [s01_comm_diag_iff]
  exact pow_eq_pow_iff_mod hζ

theorem s12_comm_dd_iff (hζ : orderOf ζ = 5) (a b : ℕ) :
    (s12GL : GL (Fin 3) K) * dd ζ a b = dd ζ a b * s12GL ↔ (4 * (a + b)) % 5 = b % 5 := by
  unfold dd
  rw [s12_comm_diag_iff]
  exact pow_eq_pow_iff_mod hζ

theorem s02_comm_dd_iff (hζ : orderOf ζ = 5) (a b : ℕ) :
    (s02GL : GL (Fin 3) K) * dd ζ a b = dd ζ a b * s02GL ↔ (4 * (a + b)) % 5 = a % 5 := by
  unfold dd
  rw [s02_comm_diag_iff]
  exact pow_eq_pow_iff_mod hζ

theorem injective_dd_entries (hζ : orderOf ζ = 5) {a b : ℕ} (hab : a % 5 ≠ b % 5)
    (hbc : b % 5 ≠ (4 * (a + b)) % 5) (hac : a % 5 ≠ (4 * (a + b)) % 5) :
    Function.Injective (fun i : Fin 3 => ((![ζ ^ a, ζ ^ b, ζ ^ (4 * (a + b))] i : Kˣ) : K)) := by
  intro i j hij
  have hij' : ![ζ ^ a, ζ ^ b, ζ ^ (4 * (a + b))] i = ![ζ ^ a, ζ ^ b, ζ ^ (4 * (a + b))] j :=
    Units.ext hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd ((pow_eq_pow_iff_mod hζ).1 hij') hab
  · exact absurd ((pow_eq_pow_iff_mod hζ).1 hij') hac
  · exact absurd ((pow_eq_pow_iff_mod hζ).1 hij').symm hab
  · rfl
  · exact absurd ((pow_eq_pow_iff_mod hζ).1 hij') hbc
  · exact absurd ((pow_eq_pow_iff_mod hζ).1 hij').symm hac
  · exact absurd ((pow_eq_pow_iff_mod hζ).1 hij').symm hbc
  · rfl

end Dd

namespace FiveModel

variable (h : FiveModel H M)
include h

@[expose] def s01H : H := ⟨s01GL, h.mono.s01_mem⟩

@[expose] def s12H : H := ⟨s12GL, h.mono.s12_mem⟩

@[expose] def s02H : H := ⟨s02GL, h.mono.s02_mem⟩

variable {ζ : Kˣ} (hζM : ζ ∈ M) (hζ : orderOf ζ = 5)
include hζM hζ

theorem proj_comm_iff (s : H) (a b : ℕ) :
    proj H s * proj H (h.ddH hζM hζ a b) = proj H (h.ddH hζM hζ a b) * proj H s ↔
      s * h.ddH hζM hζ a b = h.ddH hζM hζ a b * s := by
  constructor
  · intro hc
    exact h.commute_of_proj_commute hc (h.ddH_pow_five hζM hζ a b)
  · intro hc
    rw [← map_mul, ← map_mul, hc]

theorem proj_s01H_comm_iff (a b : ℕ) :
    proj H h.s01H * proj H (h.ddH hζM hζ a b) = proj H (h.ddH hζM hζ a b) * proj H h.s01H ↔
      b % 5 = a % 5 := by
  rw [h.proj_comm_iff hζM hζ, ← s01_comm_dd_iff hζ a b, Subtype.ext_iff]
  rfl

theorem proj_s12H_comm_iff (a b : ℕ) :
    proj H h.s12H * proj H (h.ddH hζM hζ a b) = proj H (h.ddH hζM hζ a b) * proj H h.s12H ↔
      (4 * (a + b)) % 5 = b % 5 := by
  rw [h.proj_comm_iff hζM hζ, ← s12_comm_dd_iff hζ a b, Subtype.ext_iff]
  rfl

theorem proj_s02H_comm_iff (a b : ℕ) :
    proj H h.s02H * proj H (h.ddH hζM hζ a b) = proj H (h.ddH hζM hζ a b) * proj H h.s02H ↔
      (4 * (a + b)) % 5 = a % 5 := by
  rw [h.proj_comm_iff hζM hζ, ← s02_comm_dd_iff hζ a b, Subtype.ext_iff]
  rfl

theorem commute_pstd_of_distinct {a b : ℕ} (hab : a % 5 ≠ b % 5)
    (hbc : b % 5 ≠ (4 * (a + b)) % 5) (hac : a % 5 ≠ (4 * (a + b)) % 5) {g : H}
    (hg : proj H g * proj H (h.ddH hζM hζ a b) = proj H (h.ddH hζM hζ a b) * proj H g) :
    ∀ y ∈ pstd H M, proj H g * y = y * proj H g := by
  have hcomm : g * h.ddH hζM hζ a b = h.ddH hζM hζ a b * g :=
    h.commute_of_proj_commute hg (h.ddH_pow_five hζM hζ a b)
  have hmat : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      diagonal (fun i => ((![ζ ^ a, ζ ^ b, ζ ^ (4 * (a + b))] i : Kˣ) : K)) =
      diagonal (fun i => ((![ζ ^ a, ζ ^ b, ζ ^ (4 * (a + b))] i : Kˣ) : K)) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun z : H => (((z : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) hcomm
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_ddH, dd, coe_diagHom] using this
  have hdiag : IsDiag3 ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    isDiag3_of_commute_diagonal (injective_dd_entries hζ hab hbc hac) hmat
  have hgT : (g : GL (Fin 3) K) ∈ torus3 M := h.mem_torus3_of_isDiag3 g.2 hdiag
  intro y hy
  obtain ⟨t, ht, rfl⟩ := mem_pstd.1 hy
  have : g * t = t * g := Subtype.ext (torus3_comm M hgT ht.1)
  rw [← map_mul, ← map_mul, this]

@[expose] noncomputable def xB (c : ℕ) : StatedProj H := proj H (h.ddH hζM hζ 1 c)

@[expose] noncomputable def lineB (c : ℕ) : Subgroup (StatedProj H) :=
  Subgroup.zpowers (h.xB hζM hζ c)

theorem xB_mem_pstd (c : ℕ) : h.xB hζM hζ c ∈ pstd H M :=
  mem_pstd.2 ⟨_, dd_mem_omega5 hζM hζ 1 c, rfl⟩

theorem xB_pow_five (c : ℕ) : h.xB hζM hζ c ^ 5 = 1 := by
  rw [xB, ← map_pow, h.ddH_pow_five hζM hζ, map_one]

theorem lineB_le_pstd (c : ℕ) : h.lineB hζM hζ c ≤ pstd H M :=
  Subgroup.zpowers_le.2 (h.xB_mem_pstd hζM hζ c)

theorem xB_one_ne_one : h.xB hζM hζ 1 ≠ 1 := by
  intro h1
  have := (h.proj_s12H_comm_iff hζM hζ 1 1).1 (by rw [xB] at h1; rw [h1]; simp)
  omega

theorem xB_two_ne_one : h.xB hζM hζ 2 ≠ 1 := by
  intro h1
  have := (h.proj_s01H_comm_iff hζM hζ 1 2).1 (by rw [xB] at h1; rw [h1]; simp)
  omega

theorem xB_three_ne_one : h.xB hζM hζ 3 ≠ 1 := by
  intro h1
  have := (h.proj_s01H_comm_iff hζM hζ 1 3).1 (by rw [xB] at h1; rw [h1]; simp)
  omega

theorem card_lineB_one [Finite K] : Nat.card (h.lineB hζM hζ 1) = 5 :=
  card_zpowers_five (h.xB_pow_five hζM hζ 1) (h.xB_one_ne_one hζM hζ)

theorem card_lineB_two [Finite K] : Nat.card (h.lineB hζM hζ 2) = 5 :=
  card_zpowers_five (h.xB_pow_five hζM hζ 2) (h.xB_two_ne_one hζM hζ)

theorem card_lineB_three [Finite K] : Nat.card (h.lineB hζM hζ 3) = 5 :=
  card_zpowers_five (h.xB_pow_five hζM hζ 3) (h.xB_three_ne_one hζM hζ)

theorem notCentralizing_lineB_one : NotCentralizing (pstd H M) (h.lineB hζM hζ 1) := by
  have hx : proj H h.s01H * h.xB hζM hζ 1 = h.xB hζM hζ 1 * proj H h.s01H :=
    (h.proj_s01H_comm_iff hζM hζ 1 1).2 rfl
  refine ⟨proj H h.s01H, fun y hy => comm_of_mem_zpowers hx hy, fun hall => ?_⟩
  have := (h.proj_s01H_comm_iff hζM hζ 1 0).1
    (hall _ (mem_pstd.2 ⟨_, dd_mem_omega5 hζM hζ 1 0, rfl⟩))
  omega

theorem notCentralizing_lineB_two : NotCentralizing (pstd H M) (h.lineB hζM hζ 2) := by
  have hx : proj H h.s12H * h.xB hζM hζ 2 = h.xB hζM hζ 2 * proj H h.s12H :=
    (h.proj_s12H_comm_iff hζM hζ 1 2).2 rfl
  refine ⟨proj H h.s12H, fun y hy => comm_of_mem_zpowers hx hy, fun hall => ?_⟩
  have := (h.proj_s12H_comm_iff hζM hζ 1 0).1
    (hall _ (mem_pstd.2 ⟨_, dd_mem_omega5 hζM hζ 1 0, rfl⟩))
  omega

theorem notCentralizing_lineB_three : NotCentralizing (pstd H M) (h.lineB hζM hζ 3) := by
  have hx : proj H h.s02H * h.xB hζM hζ 3 = h.xB hζM hζ 3 * proj H h.s02H :=
    (h.proj_s02H_comm_iff hζM hζ 1 3).2 rfl
  refine ⟨proj H h.s02H, fun y hy => comm_of_mem_zpowers hx hy, fun hall => ?_⟩
  have := (h.proj_s02H_comm_iff hζM hζ 1 0).1
    (hall _ (mem_pstd.2 ⟨_, dd_mem_omega5 hζM hζ 1 0, rfl⟩))
  omega

theorem lineB_one_ne_two : h.lineB hζM hζ 1 ≠ h.lineB hζM hζ 2 := by
  intro heq
  have hx : proj H h.s01H * h.xB hζM hζ 1 = h.xB hζM hζ 1 * proj H h.s01H :=
    (h.proj_s01H_comm_iff hζM hζ 1 1).2 rfl
  have hmem : h.xB hζM hζ 2 ∈ h.lineB hζM hζ 1 := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  have := (h.proj_s01H_comm_iff hζM hζ 1 2).1 (comm_of_mem_zpowers hx hmem)
  omega

theorem lineB_one_ne_three : h.lineB hζM hζ 1 ≠ h.lineB hζM hζ 3 := by
  intro heq
  have hx : proj H h.s01H * h.xB hζM hζ 1 = h.xB hζM hζ 1 * proj H h.s01H :=
    (h.proj_s01H_comm_iff hζM hζ 1 1).2 rfl
  have hmem : h.xB hζM hζ 3 ∈ h.lineB hζM hζ 1 := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  have := (h.proj_s01H_comm_iff hζM hζ 1 3).1 (comm_of_mem_zpowers hx hmem)
  omega

theorem lineB_two_ne_three : h.lineB hζM hζ 2 ≠ h.lineB hζM hζ 3 := by
  intro heq
  have hx : proj H h.s12H * h.xB hζM hζ 2 = h.xB hζM hζ 2 * proj H h.s12H :=
    (h.proj_s12H_comm_iff hζM hζ 1 2).2 rfl
  have hmem : h.xB hζM hζ 3 ∈ h.lineB hζM hζ 2 := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  have := (h.proj_s12H_comm_iff hζM hζ 1 3).1 (comm_of_mem_zpowers hx hmem)
  omega

theorem proj_ddH_eq_pow_xB (c : ℕ) {a b : ℕ} (hb : b % 5 = (a * c) % 5) :
    proj H (h.ddH hζM hζ a b) = h.xB hζM hζ c ^ a := by
  rw [xB, ← map_pow, h.ddH_pow hζM hζ]
  congr 1
  exact h.ddH_congr hζM hζ (by simp) hb

theorem eq_lineB_of_notCentralizing [Finite K] {Q : Subgroup (StatedProj H)}
    (hQP : Q ≤ pstd H M) (hQ5 : Nat.card Q = 5) (hQ : NotCentralizing (pstd H M) Q) :
    Q = h.lineB hζM hζ 1 ∨ Q = h.lineB hζM hζ 2 ∨ Q = h.lineB hζM hζ 3 := by
  obtain ⟨g, hgQ, hgP⟩ := hQ
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ5]; norm_num)
  have hnt : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.1 (by rw [hQ5]; norm_num)
  obtain ⟨q, hq1⟩ := exists_ne (1 : Q)
  have hq1' : (q : StatedProj H) ≠ 1 := fun h' => hq1 (Subtype.ext h')
  obtain ⟨t, ht, hty⟩ := mem_pstd.1 (hQP q.2)
  obtain ⟨a, b, -, -, hdd⟩ := exists_dd_of_mem_omega5 hζ ht
  have hq : (q : StatedProj H) = proj H (h.ddH hζM hζ a b) := by
    rw [← hty]
    congr 1
    exact Subtype.ext hdd
  obtain ⟨g0, rfl⟩ := proj_surjective (H := H) g
  have hgq : proj H g0 * proj H (h.ddH hζM hζ a b) = proj H (h.ddH hζM hζ a b) * proj H g0 := by
    rw [← hq]
    exact hgQ q q.2
  have hnd : a % 5 = b % 5 ∨ b % 5 = (4 * (a + b)) % 5 ∨ a % 5 = (4 * (a + b)) % 5 := by
    by_contra hcon
    push Not at hcon
    exact hgP (h.commute_pstd_of_distinct hζM hζ hcon.1 hcon.2.1 hcon.2.2 hgq)
  have hQeq : Q = Subgroup.zpowers (q : StatedProj H) := eq_zpowers_of_card_five hQ5 q.2 hq1'
  have hz5 : Nat.card (Subgroup.zpowers (q : StatedProj H)) = 5 := by
    rw [← hQeq]
    exact hQ5
  have key : ∀ c : ℕ, Nat.card (h.lineB hζM hζ c) = 5 → (q : StatedProj H) ∈ h.lineB hζM hζ c →
      Q = h.lineB hζM hζ c := fun c hB hmem => by
    rw [hQeq]
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hmem) (by rw [hB, hz5])
  rcases hnd with hc | hc | hc
  · left
    refine key 1 (h.card_lineB_one hζM hζ) ?_
    rw [hq, h.proj_ddH_eq_pow_xB hζM hζ 1 (by omega)]
    exact Subgroup.npow_mem_zpowers _ _
  · right
    left
    refine key 2 (h.card_lineB_two hζM hζ) ?_
    rw [hq, h.proj_ddH_eq_pow_xB hζM hζ 2 (by omega)]
    exact Subgroup.npow_mem_zpowers _ _
  · right
    right
    refine key 3 (h.card_lineB_three hζM hζ) ?_
    rw [hq, h.proj_ddH_eq_pow_xB hζM hζ 3 (by omega)]
    exact Subgroup.npow_mem_zpowers _ _

theorem lineSet_pstd [Finite K] :
    lineSet (pstd H M) (NotCentralizing (pstd H M)) =
      {h.lineB hζM hζ 1, h.lineB hζM hζ 2, h.lineB hζM hζ 3} := by
  ext Q
  constructor
  · rintro ⟨hQP, hQ5, hQ⟩
    rcases h.eq_lineB_of_notCentralizing hζM hζ hQP hQ5 hQ with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨h.lineB_le_pstd hζM hζ 1, h.card_lineB_one hζM hζ, h.notCentralizing_lineB_one hζM hζ⟩
    · exact ⟨h.lineB_le_pstd hζM hζ 2, h.card_lineB_two hζM hζ, h.notCentralizing_lineB_two hζM hζ⟩
    · exact ⟨h.lineB_le_pstd hζM hζ 3, h.card_lineB_three hζM hζ,
        h.notCentralizing_lineB_three hζM hζ⟩

end FiveModel

namespace FiveModel

variable (h : FiveModel H M)
include h

theorem oddLines_pstd [Finite K] : OddLines (pstd H M) := by
  obtain ⟨ζ, hζM, hζ⟩ := h.exists_orderFive
  refine ⟨NotCentralizing (pstd H M), fun α hα Q hQ => hQ.map α hα, ?_⟩
  rw [h.lineSet_pstd hζM hζ, Set.ncard_eq_three.2 ⟨_, _, _, h.lineB_one_ne_two hζM hζ,
    h.lineB_one_ne_three hζM hζ, h.lineB_two_ne_three hζM hζ, rfl⟩]
  exact ⟨1, rfl⟩

theorem e25OddLines [Finite K] : E25OddLines (StatedProj H) := by
  intro P hP hexp
  obtain ⟨φ, hφ⟩ := h.exists_map_eq_pstd hP hexp
  exact OddLines.of_map_eq φ hφ h.oddLines_pstd

end FiveModel

end FiveOdd

end CFSG.Quasithin.S146zY
