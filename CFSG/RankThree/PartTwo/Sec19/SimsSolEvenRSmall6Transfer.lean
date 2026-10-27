module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall6Step
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall6Facts

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.CGT.PushingUpLit.SolK Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6}

theorem commutator_X_eq_top (C : Cfg G M X 6) : commutator ↥X = ⊤ := by
  set N := commutator ↥X with hN
  have hA : commutator ↥(alternatingGroup (Fin 6)) = N.map C.α := by
    rw [hN, commutator, commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ C.α_surj]
  have hq2 : IsPGroup 2 (↥X ⧸ N) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : C.α x ∈ N.map C.α := by
      rw [← hA, commutator_alternatingGroup_eq_top (by simp)]
      exact Subgroup.mem_top _
    obtain ⟨h, hh, hhx⟩ := hx
    have hy : h⁻¹ * x ∈ CFSG.pCore 2 ↥X := by
      rw [← C.α_ker, MonoidHom.mem_ker, map_mul, map_inv, hhx, inv_mul_cancel]
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨_, hy⟩
    refine ⟨j, ?_⟩
    have e : (x : ↥X ⧸ N) = ((h⁻¹ * x : ↥X) : ↥X ⧸ N) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (N.inv_mem hh), one_mul]
    rw [e, ← QuotientGroup.mk_pow]
    have : (h⁻¹ * x) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    rw [this, QuotientGroup.mk_one]
  exact C.S.block.1.eq_twoResidual N hq2

@[expose] noncomputable def evenY (D : C.PiData) : Subgroup ↥X where
  carrier := {x | ∃ hY : (x : G) ∈ CFSG.Open.pCoreOf 2 X, parK D ⟨x, Y_le_K C hY⟩ = 0}
  mul_mem' := by
    rintro a b ⟨ha, hpa⟩ ⟨hb, hpb⟩
    refine ⟨(CFSG.Open.pCoreOf 2 X).mul_mem ha hb, ?_⟩
    have e : (⟨((a * b : ↥X) : G), Y_le_K C ((CFSG.Open.pCoreOf 2 X).mul_mem ha hb)⟩ : ↥C.K) =
        ⟨a, Y_le_K C ha⟩ * ⟨b, Y_le_K C hb⟩ := rfl
    rw [e, parK_mul, hpa, hpb, add_zero]
  one_mem' := ⟨(CFSG.Open.pCoreOf 2 X).one_mem, parK_one D⟩
  inv_mem' := by
    rintro a ⟨ha, hpa⟩
    refine ⟨(CFSG.Open.pCoreOf 2 X).inv_mem ha, ?_⟩
    have e : (⟨((a⁻¹ : ↥X) : G), Y_le_K C ((CFSG.Open.pCoreOf 2 X).inv_mem ha)⟩ : ↥C.K) =
        (⟨a, Y_le_K C ha⟩ : ↥C.K)⁻¹ := rfl
    rw [e, parK_inv, hpa]

instance evenY_normal (D : C.PiData) : (evenY D).Normal where
  conj_mem := by
    rintro a ⟨ha, hpa⟩ g
    have hc : ((g * a * g⁻¹ : ↥X) : G) ∈ CFSG.Open.pCoreOf 2 X :=
      pCoreOf_normalized X g.2 ha
    refine ⟨hc, ?_⟩
    rw [parK_conj D ⟨g, C.S.le g.2⟩ ⟨a, Y_le_K C ha⟩ ⟨_, Y_le_K C hc⟩ rfl, hpa]

theorem mul_self_mem_evenY (D : C.PiData) {a x : G} (ha : a ∈ X) (hx : x ∈ X) (haa : a * a = 1)
    (hθ : C.θ ⟨x, C.S.le hx⟩ = C.θ ⟨a, C.S.le ha⟩) :
    (⟨x * x, X.mul_mem hx hx⟩ : ↥X) ∈ evenY D := by
  have hyK : a⁻¹ * x ∈ C.K := inv_mul_mem_K (C.S.le ha) (C.S.le hx) hθ.symm
  have hyY : a⁻¹ * x ∈ CFSG.Open.pCoreOf 2 X :=
    mem_Y_of_mem_K C (X.mul_mem (X.inv_mem ha) hx) hyK
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hcY : a * (a⁻¹ * x) * a⁻¹ ∈ CFSG.Open.pCoreOf 2 X := pCoreOf_normalized X ha hyY
  have e : x * x = a * (a⁻¹ * x) * a⁻¹ * (a⁻¹ * x) := by
    calc x * x = a * (a⁻¹ * x) * a * (a⁻¹ * x) := by group
      _ = a * (a⁻¹ * x) * a⁻¹ * (a⁻¹ * x) := by rw [hai]
  have hxxY : x * x ∈ CFSG.Open.pCoreOf 2 X := by
    rw [e]
    exact (CFSG.Open.pCoreOf 2 X).mul_mem hcY hyY
  refine ⟨hxxY, ?_⟩
  have e' : (⟨((⟨x * x, X.mul_mem hx hx⟩ : ↥X) : G), Y_le_K C hxxY⟩ : ↥C.K) =
      ⟨a * (a⁻¹ * x) * a⁻¹, Y_le_K C hcY⟩ * ⟨a⁻¹ * x, Y_le_K C hyY⟩ := Subtype.ext e
  rw [e', parK_mul, parK_conj D ⟨a, C.S.le ha⟩ ⟨a⁻¹ * x, Y_le_K C hyY⟩ _ rfl]
  exact (show ∀ c : ZMod 2, c + c = 0 by decide) _

theorem theta_eq_one_of_mem_evenY (D : C.PiData) {x : ↥X} (hx : x ∈ evenY D) :
    C.θ ⟨x, C.S.le x.2⟩ = 1 := by
  obtain ⟨hY, -⟩ := hx
  exact (C.mem_K.1 (Y_le_K C hY)).2

theorem false_of_odd_of_involutions (D : C.PiData) (π : Perm (Fin 6)) {y₀ : G}
    (hy₀ : y₀ ∈ CFSG.Open.pCoreOf 2 X) (hodd : parK D ⟨y₀, Y_le_K C hy₀⟩ = 1)
    {a₁ a₂ b₁ : G} (ha₁ : a₁ ∈ X) (ha₂ : a₂ ∈ X) (hb₁ : b₁ ∈ X) (ha₁₁ : a₁ * a₁ = 1)
    (ha₂₂ : a₂ * a₂ = 1) (hb₁₁ : b₁ * b₁ = 1) (hθa₁ : C.θ ⟨a₁, C.S.le ha₁⟩ = sig1 π)
    (hθa₂ : C.θ ⟨a₂, C.S.le ha₂⟩ = sig2 π) (hθb₁ : C.θ ⟨b₁, C.S.le hb₁⟩ = esc1 π) : False := by
  classical
  set N := evenY D with hN
  set Q := ↥X ⧸ N
  have hy₀X : y₀ ∈ X := pCoreOf_le_self X hy₀
  set z : Q := ((⟨y₀, hy₀X⟩ : ↥X) : Q) with hz
  have hθY : ∀ {g : ↥X}, (g : G) ∈ CFSG.Open.pCoreOf 2 X → C.θ ⟨g, C.S.le g.2⟩ = 1 :=
    fun hg => (C.mem_K.1 (Y_le_K C hg)).2
  have hθeq : ∀ {g h : ↥X}, (g : Q) = (h : Q) → C.θ ⟨g, C.S.le g.2⟩ = C.θ ⟨h, C.S.le h.2⟩ := by
    intro g h hgh
    rw [QuotientGroup.eq] at hgh
    have h1 := theta_eq_one_of_mem_evenY D hgh
    have e : (⟨((g⁻¹ * h : ↥X) : G), C.S.le (g⁻¹ * h).2⟩ : ↥M) =
        (⟨g, C.S.le g.2⟩ : ↥M)⁻¹ * ⟨h, C.S.le h.2⟩ := rfl
    rw [e, map_mul, map_inv] at h1
    exact (inv_mul_eq_one.1 h1)
  have hzc : ∀ g : Q, g * z = z * g := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hz, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hcY : (x : G)⁻¹ * y₀ * (x : G)⁻¹⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
      pCoreOf_normalized X (X.inv_mem x.2) hy₀
    have hmem : ((((x * ⟨y₀, hy₀X⟩)⁻¹ * (⟨y₀, hy₀X⟩ * x)) : ↥X) : G) =
        y₀⁻¹ * ((x : G)⁻¹ * y₀ * (x : G)⁻¹⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hY : y₀⁻¹ * ((x : G)⁻¹ * y₀ * (x : G)⁻¹⁻¹) ∈ CFSG.Open.pCoreOf 2 X :=
      (CFSG.Open.pCoreOf 2 X).mul_mem ((CFSG.Open.pCoreOf 2 X).inv_mem hy₀) hcY
    refine ⟨hmem ▸ hY, ?_⟩
    have e : (⟨((((x * ⟨y₀, hy₀X⟩)⁻¹ * (⟨y₀, hy₀X⟩ * x)) : ↥X) : G), Y_le_K C (hmem ▸ hY)⟩ :
        ↥C.K) = (⟨y₀, Y_le_K C hy₀⟩ : ↥C.K)⁻¹ * ⟨_, Y_le_K C hcY⟩ := Subtype.ext hmem
    rw [e, parK_mul, parK_inv,
      parK_conj D ⟨(x : G)⁻¹, C.S.le (X.inv_mem x.2)⟩ ⟨y₀, Y_le_K C hy₀⟩ ⟨_, Y_le_K C hcY⟩ rfl]
    exact (show ∀ c : ZMod 2, c + c = 0 by decide) _
  have hz2 : z * z = 1 := by
    rw [hz, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    have hY : y₀ * y₀ ∈ CFSG.Open.pCoreOf 2 X := (CFSG.Open.pCoreOf 2 X).mul_mem hy₀ hy₀
    refine ⟨hY, ?_⟩
    have e : (⟨(((⟨y₀, hy₀X⟩ : ↥X) * ⟨y₀, hy₀X⟩ : ↥X) : G), Y_le_K C hY⟩ : ↥C.K) =
        ⟨y₀, Y_le_K C hy₀⟩ * ⟨y₀, Y_le_K C hy₀⟩ := rfl
    rw [e, parK_mul, hodd]
    decide
  have hz1 : z ≠ 1 := by
    rw [hz, Ne, QuotientGroup.eq_one_iff]
    rintro ⟨hY, h⟩
    have h' : parK D ⟨y₀, Y_le_K C hY⟩ = 1 := hodd
    rw [h'] at h
    exact absurd h (by decide)
  obtain ⟨q, hq⟩ := C.exists_lift (quad1_mem_alternatingGroup π)
  set c : Q := (q : Q) with hc
  set d : Q := ((⟨a₂, ha₂⟩ : ↥X) : Q) with hd
  have hd2 : d * d = 1 := by
    rw [hd, ← QuotientGroup.mk_mul]
    have : (⟨a₂, ha₂⟩ : ↥X) * ⟨a₂, ha₂⟩ = 1 := Subtype.ext ha₂₂
    rw [this, QuotientGroup.mk_one]
  have hc4 : c ^ 4 = 1 := by
    have hqq : C.θ ⟨((q * q : ↥X) : G), C.S.le (q * q).2⟩ = C.θ ⟨a₁, C.S.le ha₁⟩ := by
      have e : (⟨((q * q : ↥X) : G), C.S.le (q * q).2⟩ : ↥M) =
          ⟨q, C.S.le q.2⟩ * ⟨q, C.S.le q.2⟩ := rfl
      rw [e, map_mul, hq, quad1_mul_self, hθa₁]
    have h := mul_self_mem_evenY D ha₁ (q * q).2 ha₁₁ hqq
    have e : c ^ 4 = ((((q * q) * (q * q) : ↥X)) : Q) := by
      rw [hc, ← QuotientGroup.mk_pow, show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [e, QuotientGroup.eq_one_iff]
    exact h
  have hdc2 : d * c * (d * c) = 1 := by
    have hθdc : C.θ ⟨(((⟨a₂, ha₂⟩ : ↥X) * q : ↥X) : G), C.S.le (⟨a₂, ha₂⟩ * q : ↥X).2⟩ =
        C.θ ⟨b₁, C.S.le hb₁⟩ := by
      have e : (⟨(((⟨a₂, ha₂⟩ : ↥X) * q : ↥X) : G), C.S.le (⟨a₂, ha₂⟩ * q : ↥X).2⟩ : ↥M) =
          ⟨a₂, C.S.le ha₂⟩ * ⟨q, C.S.le q.2⟩ := rfl
      rw [e, map_mul, hθa₂, hq, sig2_mul_quad1, hθb₁]
    have h := mul_self_mem_evenY D hb₁ (⟨a₂, ha₂⟩ * q : ↥X).2 hb₁₁ hθdc
    have e : d * c * (d * c) =
        ((((⟨a₂, ha₂⟩ * q) * (⟨a₂, ha₂⟩ * q) : ↥X)) : Q) := by
      rw [hd, hc, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rw [e, QuotientGroup.eq_one_iff]
    exact h
  have hci : c⁻¹ = c ^ 3 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hc4]
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hdc : d * c = c ^ 3 * d := by
    have h1 : d * c = (d * c)⁻¹ := eq_inv_of_mul_eq_one_left hdc2
    rw [h1, mul_inv_rev, hci, hdi]
  have hdck : ∀ k : ℕ, d * c ^ k = c ^ (3 * k) * d := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hdc, ← mul_assoc, ← pow_add]
      ring_nf
  set Dh : Subgroup Q := Subgroup.closure {c, d} with hDh
  have hform : ∀ g ∈ Dh, ∃ i : ℕ, g = c ^ i ∨ g = c ^ i * d := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨1, Or.inl (pow_one _).symm⟩
      · exact ⟨0, Or.inr (by rw [pow_zero, one_mul])⟩
    | one => exact ⟨0, Or.inl (pow_zero _).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, rfl | rfl⟩ := hx <;> obtain ⟨k, rfl | rfl⟩ := hy
      · exact ⟨i + k, Or.inl (pow_add _ _ _).symm⟩
      · exact ⟨i + k, Or.inr (by rw [pow_add, mul_assoc])⟩
      · exact ⟨i + 3 * k, Or.inr (by rw [mul_assoc, hdck, ← mul_assoc, ← pow_add])⟩
      · refine ⟨i + 3 * k, Or.inl ?_⟩
        rw [mul_assoc, ← mul_assoc d, hdck, mul_assoc, hd2, mul_one, ← pow_add]
    | inv x _ hx =>
      obtain ⟨i, rfl | rfl⟩ := hx
      · refine ⟨3 * i, Or.inl ?_⟩
        rw [← inv_pow, hci, ← pow_mul]
      · refine ⟨9 * i, Or.inr ?_⟩
        rw [mul_inv_rev, hdi, ← inv_pow, hci, ← pow_mul, hdck, show 3 * (3 * i) = 9 * i by ring]
  have hq4 : quad1 π ^ 4 = 1 := by
    have e : quad1 π ^ 4 = (quad1 π * quad1 π) * (quad1 π * quad1 π) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    have h1 : sig1 1 * sig1 1 = 1 := by decide
    rw [e, quad1_mul_self, sig1_eq π]
    calc π * sig1 1 * π⁻¹ * (π * sig1 1 * π⁻¹) = π * (sig1 1 * sig1 1) * π⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hθq : ∀ i : ℕ, C.θ ⟨((q ^ i : ↥X) : G), C.S.le (q ^ i).2⟩ = quad1 π ^ (i % 4) := by
    intro i
    have e : (⟨((q ^ i : ↥X) : G), C.S.le (q ^ i).2⟩ : ↥M) = (⟨q, C.S.le q.2⟩ : ↥M) ^ i :=
      Subtype.ext (by simp)
    rw [e, map_pow, hq, ← pow_eq_pow_mod i hq4]
  have hθqa : ∀ i : ℕ, C.θ ⟨((q ^ i * ⟨a₂, ha₂⟩ : ↥X) : G), C.S.le (q ^ i * ⟨a₂, ha₂⟩ : ↥X).2⟩ =
      quad1 π ^ (i % 4) * sig2 π ^ 1 := by
    intro i
    have e : (⟨((q ^ i * ⟨a₂, ha₂⟩ : ↥X) : G), C.S.le (q ^ i * ⟨a₂, ha₂⟩ : ↥X).2⟩ : ↥M) =
        ⟨((q ^ i : ↥X) : G), C.S.le (q ^ i).2⟩ * ⟨a₂, C.S.le ha₂⟩ := rfl
    rw [e, map_mul, hθq, hθa₂, pow_one]
  have hc_pow : ∀ i : ℕ, c ^ i = c ^ (i % 4) := fun i => pow_eq_pow_mod i hc4
  have hzD : z ∉ Dh := by
    intro hzD
    obtain ⟨i, hi | hi⟩ := hform z hzD
    · have h := hθeq (g := ⟨y₀, hy₀X⟩) (h := q ^ i)
        (by rw [← hz, hi, hc, QuotientGroup.mk_pow])
      rw [hθY (g := ⟨y₀, hy₀X⟩) hy₀, hθq] at h
      have h0 := quad1_pow_mul_eq_one π (Nat.mod_lt i (by norm_num)) (by norm_num : 0 < 2)
        (by rw [pow_zero, mul_one]; exact h.symm)
      apply hz1
      rw [hi, hc_pow, h0.1, pow_zero]
    · have h := hθeq (g := ⟨y₀, hy₀X⟩) (h := q ^ i * ⟨a₂, ha₂⟩)
        (by rw [← hz, hi, hc, hd, QuotientGroup.mk_mul, QuotientGroup.mk_pow])
      rw [hθY (g := ⟨y₀, hy₀X⟩) hy₀, hθqa] at h
      have h0 := quad1_pow_mul_eq_one π (Nat.mod_lt i (by norm_num)) (by norm_num : 1 < 2) h.symm
      exact absurd h0.2 (by norm_num)
  set H : Subgroup ↥X := (cent1 π).comap C.α with hH
  set Hh : Subgroup Q := H.map (QuotientGroup.mk' N) with hHh
  have hNH : N ≤ H := by
    intro x hx
    obtain ⟨hY, -⟩ := hx
    have hxY : x ∈ CFSG.pCore 2 ↥X := by
      obtain ⟨x', hx', hxx'⟩ := hY
      have : x' = x := Subtype.ext hxx'
      rw [← this]
      exact hx'
    rw [← C.α_ker] at hxY
    show C.α x ∈ cent1 π
    rw [hxY]
    exact (cent1 π).one_mem
  have hindex : Hh.index = 45 := by
    have h1 : Hh.index = H.index := Subgroup.index_map_eq (H := H)
      (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk']; exact hNH)
    have h2 : H.index = (cent1 π).index := Subgroup.index_comap_of_surjective _ C.α_surj
    rw [h1, h2, index_cent1]
  have hHform : ∀ h ∈ Hh, h ∈ Dh ∨ h * z ∈ Dh := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi, j, hj, hxij⟩ := eq_of_mem_cent1 π hx
    set g : ↥X := q ^ i * (⟨a₂, ha₂⟩ : ↥X) ^ j with hg
    have hθg : C.θ ⟨g, C.S.le g.2⟩ = C.θ ⟨x, C.S.le x.2⟩ := by
      have e : (⟨(g : G), C.S.le g.2⟩ : ↥M) = (⟨q, C.S.le q.2⟩ : ↥M) ^ i *
          (⟨a₂, C.S.le ha₂⟩ : ↥M) ^ j := Subtype.ext (by simp [hg])
      rw [e, map_mul, map_pow, map_pow, hq, hθa₂, C.θ_X x, ← hxij]
    have hgD : (g : Q) ∈ Dh := by
      rw [hg, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow]
      exact Dh.mul_mem (Dh.pow_mem (Subgroup.subset_closure (Or.inl rfl)) _)
        (Dh.pow_mem (Subgroup.subset_closure (Or.inr rfl)) _)
    have hyK : (g : G)⁻¹ * x ∈ C.K := inv_mul_mem_K (C.S.le g.2) (C.S.le x.2) hθg
    have hyY : (g : G)⁻¹ * x ∈ CFSG.Open.pCoreOf 2 X :=
      mem_Y_of_mem_K C (X.mul_mem (X.inv_mem g.2) x.2) hyK
    have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases h01 (parK D ⟨(g : G)⁻¹ * x, Y_le_K C hyY⟩) with h0 | h1
    · left
      have : (g : Q) = (x : Q) := QuotientGroup.eq.2 ⟨hyY, h0⟩
      show (x : Q) ∈ Dh
      rw [← this]
      exact hgD
    · right
      have hmem : ((g⁻¹ * (x * ⟨y₀, hy₀X⟩⁻¹) : ↥X) : G) ∈ CFSG.Open.pCoreOf 2 X := by
        have e : ((g⁻¹ * (x * ⟨y₀, hy₀X⟩⁻¹) : ↥X) : G) = (g : G)⁻¹ * x * y₀⁻¹ := by
          simp [mul_assoc]
        rw [e]
        exact (CFSG.Open.pCoreOf 2 X).mul_mem hyY ((CFSG.Open.pCoreOf 2 X).inv_mem hy₀)
      have hpar : parK D ⟨_, Y_le_K C hmem⟩ = 0 := by
        have e : (⟨_, Y_le_K C hmem⟩ : ↥C.K) = ⟨(g : G)⁻¹ * x, Y_le_K C hyY⟩ *
            (⟨y₀, Y_le_K C hy₀⟩ : ↥C.K)⁻¹ := Subtype.ext (by simp [mul_assoc])
        rw [e, parK_mul, parK_inv, h1, hodd]
        decide
      have : (g : Q) = ((x * ⟨y₀, hy₀X⟩⁻¹ : ↥X) : Q) := QuotientGroup.eq.2 ⟨hmem, hpar⟩
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
      show (x : Q) * z ∈ Dh
      have e2 : (x : Q) * z = (x : Q) * z⁻¹ := by rw [hzi]
      rw [e2, hz, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← this]
      exact hgD
  have hnot : ∀ h ∈ Hh, ¬ (h ∈ Dh ∧ h * z ∈ Dh) := by
    rintro h - ⟨h1, h2⟩
    apply hzD
    have : z = h⁻¹ * (h * z) := by group
    rw [this]
    exact Dh.mul_mem (Dh.inv_mem h1) h2
  let ϕ : ↥Hh →* Multiplicative (ZMod 2) :=
    { toFun := fun h => if (h : Q) ∈ Dh then 1 else Multiplicative.ofAdd 1
      map_one' := by simp [Dh.one_mem]
      map_mul' := by
        rintro ⟨h₁, hh₁⟩ ⟨h₂, hh₂⟩
        simp only [Subgroup.coe_mul]
        have hz' : ∀ g : Q, g * z = z * g := hzc
        rcases hHform h₁ hh₁ with p₁ | p₁ <;> rcases hHform h₂ hh₂ with p₂ | p₂
        · rw [if_pos (Dh.mul_mem p₁ p₂), if_pos p₁, if_pos p₂, mul_one]
        · have hn : h₁ * h₂ ∉ Dh := fun h => hnot _ (Hh.mul_mem hh₁ hh₂)
            ⟨h, by rw [mul_assoc]; exact Dh.mul_mem p₁ p₂⟩
          have hn2 : h₂ ∉ Dh := fun h => hnot _ hh₂ ⟨h, p₂⟩
          rw [if_neg hn, if_pos p₁, if_neg hn2, one_mul]
        · have hn : h₁ * h₂ ∉ Dh := fun h => hnot _ (Hh.mul_mem hh₁ hh₂)
            ⟨h, by
              have e : h₁ * h₂ * z = h₁ * z * h₂ := by rw [mul_assoc, hz' h₂, ← mul_assoc]
              rw [e]; exact Dh.mul_mem p₁ p₂⟩
          have hn1 : h₁ ∉ Dh := fun h => hnot _ hh₁ ⟨h, p₁⟩
          rw [if_neg hn, if_neg hn1, if_pos p₂, mul_one]
        · have hp : h₁ * h₂ ∈ Dh := by
            have e : h₁ * h₂ = h₁ * z * (h₂ * z) := by
              rw [mul_assoc, ← mul_assoc z, ← hz' h₂, mul_assoc, hz2, mul_one]
            rw [e]; exact Dh.mul_mem p₁ p₂
          have hn1 : h₁ ∉ Dh := fun h => hnot _ hh₁ ⟨h, p₁⟩
          have hn2 : h₂ ∉ Dh := fun h => hnot _ hh₂ ⟨h, p₂⟩
          rw [if_pos hp, if_neg hn1, if_neg hn2]
          rfl }
  have hkey : ∀ (k : ℕ) (g₀ : Q), g₀⁻¹ * z ^ k * g₀ ∈ Hh → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : ∀ g : Q, g * z ^ k = z ^ k * g := fun g => (Commute.pow_right (hzc g) k).eq
    rw [mul_assoc, ← hzk g₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have htr := MonoidHom.transfer_eq_pow ϕ z hkey
  have hz45 : z ^ Hh.index = z := by
    rw [hindex, pow_eq_pow_mod 45 (by rw [pow_two]; exact hz2)]
    norm_num
  have hϕz : ϕ ⟨z ^ Hh.index, MonoidHom.transfer_eq_pow_aux z hkey⟩ = Multiplicative.ofAdd 1 := by
    show (if z ^ Hh.index ∈ Dh then 1 else Multiplicative.ofAdd 1) = Multiplicative.ofAdd 1
    rw [hz45, if_neg hzD]
  have hcomm : commutator Q = ⊤ := by
    have h1 : (commutator ↥X).map (QuotientGroup.mk' N) = commutator Q := by
      rw [commutator, commutator, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    rw [← h1, commutator_X_eq_top C,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have hker : z ∈ (MonoidHom.transfer ϕ).ker :=
    Abelianization.commutator_subset_ker _ (by rw [hcomm]; exact Subgroup.mem_top z)
  rw [MonoidHom.mem_ker, htr, hϕz] at hker
  exact absurd hker (by decide)

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6
