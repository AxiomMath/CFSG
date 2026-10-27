module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofLinBasics
import CFSG.GH74.GLS.IVK.L2.Fixed
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofL3Red

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Assembly (IsElemAbelian)
open scoped MatrixGroups

section DInn

variable {K : Type} [Field K]

theorem exists_conjAut_of_fieldPart_eq_one [Finite K] {x : MulAut (projectiveSL 3 K)}
    (hφ : ProjectivePlane.linearFieldPart K (le_refl 3) x = 1) (h3 : x ^ 3 = 1) :
    ∃ A : GL (Fin 3) K, x = conjAut 3 K A := by
  obtain ⟨σ, A, ε, hε, hx⟩ := ProjectivePlane.exists_standard_form K 3 (le_refl 3) x
  have hσ : σ = 1 := by
    rw [hx, ProjectivePlane.linearFieldPart_eq (le_refl 3) hε] at hφ
    exact hφ
  subst hσ
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · exact ⟨A, by rw [hx, map_one, mul_one, pow_zero, mul_one]⟩
  · exfalso
    rw [map_one, mul_one, pow_one] at hx
    have htrans := standard_automorphism_transport (K := K) (n := 3)
    have hδδ : dualAut 3 K * dualAut 3 K = 1 := htrans.2.2.2.1
    have hcube : x ^ 3 = conjAut 3 K (A * Matrix.GeneralLinearGroup.inverseTranspose A * A) *
        fieldAut 3 K 1 * dualAut 3 K ^ 1 := by
      rw [hx, map_one, mul_one, pow_one, pow_three, map_mul, map_mul]
      calc conjAut 3 K A * dualAut 3 K * (conjAut 3 K A * dualAut 3 K *
            (conjAut 3 K A * dualAut 3 K))
          = conjAut 3 K A * (dualAut 3 K * conjAut 3 K A) * (dualAut 3 K *
            conjAut 3 K A) * dualAut 3 K := by group
        _ = conjAut 3 K A * (conjAut 3 K (Matrix.GeneralLinearGroup.inverseTranspose A) *
            dualAut 3 K) * (dualAut 3 K * conjAut 3 K A) * dualAut 3 K := by
            rw [show dualAut 3 K * conjAut 3 K A =
              conjAut 3 K (Matrix.GeneralLinearGroup.inverseTranspose A) * dualAut 3 K by
              rw [← htrans.2.2.2.2.1 A, mul_assoc, hδδ, mul_one]]
        _ = conjAut 3 K A * conjAut 3 K (Matrix.GeneralLinearGroup.inverseTranspose A) *
            (dualAut 3 K * dualAut 3 K) * conjAut 3 K A * dualAut 3 K := by group
        _ = _ := by rw [hδδ, mul_one]
    have h1 : conjAut 3 K (A * Matrix.GeneralLinearGroup.inverseTranspose A * A) *
        fieldAut 3 K 1 * dualAut 3 K ^ 1 = conjAut 3 K 1 * fieldAut 3 K 1 * dualAut 3 K ^ 0 := by
      rw [← hcube, h3, map_one, map_one, pow_zero, mul_one, mul_one]
    have := (ProjectivePlane.standard_form_unique (le_refl 3) le_rfl (Nat.zero_le 1) h1).2
    omega

theorem exists_pow_eq_of_generator [Finite K] {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) (a : Kˣ) : ∃ i : ℕ, g ^ i = a := by
  have h := (mem_powers_iff_mem_zpowers (x := g) (y := a)).mpr (hg a)
  obtain ⟨i, hi⟩ := h
  exact ⟨i, hi⟩

theorem isCube_mul_or_div [Finite K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hna : ¬ ∃ ν : K, a = ν ^ 3) (hnb : ¬ ∃ ν : K, b = ν ^ 3) :
    (∃ ν : K, a * b = ν ^ 3) ∨ ∃ ν : K, a * b⁻¹ = ν ^ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨i, hi⟩ := exists_pow_eq_of_generator hg (Units.mk0 a ha)
  obtain ⟨j, hj⟩ := exists_pow_eq_of_generator hg (Units.mk0 b hb)
  have hai : a = ((g : K)) ^ i := by
    have := congrArg Units.val hi
    simpa using this.symm
  have hbj : b = ((g : K)) ^ j := by
    have := congrArg Units.val hj
    simpa using this.symm
  have hi3 : ¬ 3 ∣ i := by
    rintro ⟨i', rfl⟩
    exact hna ⟨(g : K) ^ i', by rw [hai, ← pow_mul, mul_comm]⟩
  have hj3 : ¬ 3 ∣ j := by
    rintro ⟨j', rfl⟩
    exact hnb ⟨(g : K) ^ j', by rw [hbj, ← pow_mul, mul_comm]⟩
  have hg0 : (g : K) ≠ 0 := g.ne_zero
  by_cases hij : i % 3 = j % 3
  · right
    obtain ⟨c, hc⟩ : 3 ∣ i + 2 * j := by omega
    refine ⟨(g : K) ^ c / b, ?_⟩
    rw [div_pow, ← pow_mul, mul_comm c 3, ← hc]
    rw [hai, hbj]
    field_simp
    ring
  · left
    obtain ⟨c, hc⟩ : 3 ∣ i + j := by omega
    refine ⟨(g : K) ^ c, ?_⟩
    rw [hai, hbj, ← pow_add, hc, ← pow_mul, mul_comm]

theorem isCube_of_fixed [Finite K] (hK3 : Nat.card K % 3 = 1) {ψ : K ≃+* K}
    (hψ : orderOf ψ = 3) {x : K} (hx : x ≠ 0) (hfix : ψ x = x) : ∃ ν : K, x = ν ^ 3 := by
  classical
  set K₀ := CFSG.GH74.GLS.IVK.fixedField ψ with hK₀
  have hcard := CFSG.GH74.GLS.IVK.fixedField_card_pow ψ
  rw [hψ] at hcard
  set r := Nat.card K₀ with hr
  have hr1 : 1 < r := CFSG.GH74.GLS.IVK.one_lt_card_fixedField ψ
  have hxK₀ : x ∈ K₀ := (CFSG.GH74.GLS.IVK.mem_fixedField_iff ψ x).mpr hfix
  have hxr : x ^ (r - 1) = 1 := by
    have : Finite K₀ := Subtype.finite
    have hu : (Units.mk0 (⟨x, hxK₀⟩ : K₀) (by
        intro h; exact hx (congrArg Subtype.val h))) ^ (Nat.card K₀ˣ) = 1 := pow_card_eq_one'
    rw [Nat.card_units] at hu
    have := congrArg (fun u : K₀ˣ => ((u : K₀) : K)) hu
    simpa using this
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨a, ha⟩ := exists_pow_eq_of_generator hg (Units.mk0 x hx)
  have hord : orderOf g = r ^ 3 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, ← hcard]
  have hdvd : r ^ 3 - 1 ∣ a * (r - 1) := by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, pow_mul, ha]
    apply Units.ext
    simpa using hxr
  have hfac : r ^ 3 - 1 = (r - 1) * (r ^ 2 + r + 1) := by
    obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [hs, Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)
  have hdvd' : r ^ 2 + r + 1 ∣ a := by
    rw [hfac, mul_comm a] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd
  have hr3 : r % 3 = 1 := by
    have h1 : (r ^ 3) % 3 = 1 := by rw [hcard]; exact hK3
    have : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
    rcases this with h | h | h
    · rw [Nat.pow_mod, h] at h1; norm_num at h1
    · exact h
    · rw [Nat.pow_mod, h] at h1; norm_num at h1
  have h3 : 3 ∣ r ^ 2 + r + 1 := by
    have : (r ^ 2 + r + 1) % 3 = 0 := by
      rw [Nat.add_mod, Nat.add_mod (r ^ 2), Nat.pow_mod, hr3]
    omega
  obtain ⟨b, rfl⟩ := dvd_trans h3 hdvd'
  refine ⟨(g : K) ^ b, ?_⟩
  have := congrArg Units.val ha
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
  rw [← this, ← pow_mul, mul_comm]

theorem eq_pow_of_pow_three_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {τ τ' : G} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hτ' : τ' ^ 3 = 1) :
    τ' = 1 ∨ τ' = τ ∨ τ' = τ ^ 2 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hle := IsCyclic.card_pow_eq_one_le (α := G) (n := 3) (by norm_num)
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 * (τ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hτ, h]; group
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    calc τ = τ ^ 2 * τ⁻¹ := by group
      _ = 1 := by rw [← h]; group
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3⟩ := hne
  have hsub : ({1, τ, τ ^ 2, τ'} : Finset G) ⊆ Finset.univ.filter (fun a : G => a ^ 3 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · exact hτ
    · rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hτ, one_pow]
    · exact hτ'
  have hcard : ({1, τ, τ ^ 2, τ'} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h3)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hττ2, Ne.symm h2⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hτ1, Ne.symm hτ2, Ne.symm h1⟩
  have := Finset.card_le_card hsub
  omega

theorem card_le_three_of_subset {G : Type*} [Group G] {D : Subgroup G} {y : G}
    (h : ∀ d ∈ D, d = 1 ∨ d = y ∨ d = y⁻¹) : Nat.card D ≤ 3 := by
  classical
  have hsub : (D : Set G) ⊆ ({1, y, y⁻¹} : Finset G) := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    exact h d hd
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h1
  rw [← Nat.card_coe_set_eq] at h1
  exact h1.trans (Finset.card_le_three)

theorem exists_mem_inf_range_ne_one [Finite K] (hK3 : Nat.card K % 3 = 1)
    {D : Subgroup (MulAut (projectiveSL 3 K))} (hDe : IsElemAbelian 3 D) (hD9 : Nat.card D = 9) :
    ∃ d ∈ D, d ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ∧
      d ≠ 1 := by
  classical
  set I := (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range with hI
  set φ := ProjectivePlane.linearFieldPart K (le_refl 3) with hφ
  by_contra hcon
  push Not at hcon
  have hD3 : ∀ d ∈ D, d ^ 3 = 1 := hDe.2
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : p.Prime := CharP.char_is_prime K p
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hf⟩ := FiniteField.card K p
  have hcyc : IsCyclic (K ≃+* K) :=
    (card_ringAut_and_isCyclic hp K (by rw [Nat.card_eq_fintype_card, hf.2])).2
  have : Finite (K ≃+* K) := CFSG.GH74.GLS.IVK.instFiniteRingEquiv K
  have hpair : ∀ y ∈ D, ∀ z ∈ D, φ y = 1 → φ z = 1 → y ≠ 1 → z ≠ 1 → z = y ∨ z = y⁻¹ := by
    intro y hy z hz hφy hφz hy1 hz1
    obtain ⟨M, rfl⟩ := exists_conjAut_of_fieldPart_eq_one hφy (hD3 _ hy)
    obtain ⟨N, rfl⟩ := exists_conjAut_of_fieldPart_eq_one hφz (hD3 _ hz)
    have hMn : ¬ ∃ ν : K, (M : Matrix (Fin 3) (Fin 3) K).det = ν ^ 3 := fun h =>
      hy1 (hcon _ hy (conjAut_mem_range_of_det h.choose_spec))
    have hNn : ¬ ∃ ν : K, (N : Matrix (Fin 3) (Fin 3) K).det = ν ^ 3 := fun h =>
      hz1 (hcon _ hz (conjAut_mem_range_of_det h.choose_spec))
    rcases isCube_mul_or_div (Matrix.isUnits_det_units N).ne_zero
        (Matrix.isUnits_det_units M).ne_zero hNn hMn with ⟨ν, hν⟩ | ⟨ν, hν⟩
    · right
      have hmem : conjAut 3 K N * conjAut 3 K M ∈ I := by
        rw [← map_mul]
        refine conjAut_mem_range_of_det (ν := ν) ?_
        rw [Units.val_mul, Matrix.det_mul, hν]
      have h1 := hcon _ (D.mul_mem hz hy) hmem
      exact eq_inv_of_mul_eq_one_left h1
    · left
      have hmem : conjAut 3 K N * (conjAut 3 K M)⁻¹ ∈ I := by
        rw [← map_inv, ← map_mul]
        refine conjAut_mem_range_of_det (ν := ν) ?_
        rw [Units.val_mul, Matrix.det_mul, Matrix.coe_units_inv, Matrix.det_nonsing_inv,
          ← hν, Ring.inverse_eq_inv']
      have h1 := hcon _ (D.mul_mem hz (D.inv_mem hy)) hmem
      exact mul_inv_eq_one.mp h1
  have hD1 : ∃ y ∈ D, y ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card D ≤ 3 := card_le_three_of_subset (y := 1) fun d hd => Or.inl (h d hd)
    omega
  by_cases hall : ∀ d ∈ D, φ d = 1
  · obtain ⟨y, hy, hy1⟩ := hD1
    have : Nat.card D ≤ 3 := card_le_three_of_subset (y := y) fun z hz => by
      by_cases hz1 : z = 1
      · exact Or.inl hz1
      · exact Or.inr (hpair y hy z hz (hall y hy) (hall z hz) hy1 hz1)
    omega
  push Not at hall
  obtain ⟨e, he, hφe⟩ := hall
  have he3 : e ^ 3 = 1 := hD3 e he
  have hcoset : ∀ d ∈ D, φ d = 1 ∨ φ (d * e⁻¹) = 1 ∨ φ (d * (e ^ 2)⁻¹) = 1 := by
    intro d hd
    have hφ3 : (φ e) ^ 3 = 1 := by rw [← map_pow, he3, map_one]
    have hφd3 : (φ d) ^ 3 = 1 := by rw [← map_pow, hD3 d hd, map_one]
    rcases eq_pow_of_pow_three_of_isCyclic hφ3 hφe hφd3 with h | h | h
    · exact Or.inl h
    · right; left; rw [map_mul, map_inv, h, mul_inv_cancel]
    · right; right; rw [map_mul, map_inv, map_pow, h, mul_inv_cancel]
  have hy : ∃ y ∈ D, y ≠ 1 ∧ φ y = 1 := by
    by_contra h
    push Not at h
    have : Nat.card D ≤ 3 := card_le_three_of_subset (y := e) fun d hd => by
      rcases hcoset d hd with h1 | h1 | h1
      · exact Or.inl (by_contra fun h' => h' (h d hd h' |> fun h'' => absurd h1 h''))
      · right; left
        by_contra h'
        have : d * e⁻¹ ≠ 1 := fun h0 => h' (mul_inv_eq_one.mp h0)
        exact h _ (D.mul_mem hd (D.inv_mem he)) this h1
      · right; right
        have hne : d * (e ^ 2)⁻¹ = 1 := by
          by_contra h'
          exact h _ (D.mul_mem hd (D.inv_mem (D.pow_mem he 2))) h' h1
        have : d = e ^ 2 := mul_inv_eq_one.mp hne
        rw [this]
        calc e ^ 2 = e ^ 3 * e⁻¹ := by group
          _ = e⁻¹ := by rw [he3, one_mul]
    omega
  obtain ⟨y, hyD, hy1, hφy⟩ := hy
  obtain ⟨M, rfl⟩ := exists_conjAut_of_fieldPart_eq_one hφy (hD3 _ hyD)
  have heD : e ∉ linearAutGroup 3 K := by
    intro hmem
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hmem
    apply hφe
    have := ProjectivePlane.linearFieldPart_eq (K := K) (le_refl 3) (A := A) (σ := 1)
      (Nat.zero_le 1)
    rw [map_one, mul_one, pow_zero, mul_one] at this
    exact this
  obtain ⟨ψ, hψ, H, rfl⟩ := KFacts.linear_order_three_field_descent (le_refl 3) _ he3 heD
  set M' := H⁻¹ * M * H with hM'
  have hcomm : conjAut 3 K M' * fieldAut 3 K ψ = fieldAut 3 K ψ * conjAut 3 K M' := by
    have h := hDc _ hyD _ he
    rw [hM', map_mul, map_mul, map_inv]
    calc (conjAut 3 K H)⁻¹ * conjAut 3 K M * conjAut 3 K H * fieldAut 3 K ψ
        = (conjAut 3 K H)⁻¹ * (conjAut 3 K M *
            (conjAut 3 K H * fieldAut 3 K ψ * (conjAut 3 K H)⁻¹)) * conjAut 3 K H := by group
      _ = (conjAut 3 K H)⁻¹ * ((conjAut 3 K H * fieldAut 3 K ψ * (conjAut 3 K H)⁻¹) *
            conjAut 3 K M) * conjAut 3 K H := by rw [h]
      _ = fieldAut 3 K ψ * ((conjAut 3 K H)⁻¹ * conjAut 3 K M * conjAut 3 K H) := by group
  have htrans := standard_automorphism_transport (K := K) (n := 3)
  have hψM : conjAut 3 K (Matrix.GeneralLinearGroup.map (ψ : K →+* K) M') = conjAut 3 K M' := by
    rw [← htrans.2.2.1 ψ M', ← hcomm]
    group
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq hψM
  have hM'0 : (M' : Matrix (Fin 3) (Fin 3) K) ≠ 0 := by
    intro h0
    have := (Matrix.isUnits_det_units M').ne_zero
    rw [h0, Matrix.det_zero] at this
    exact this rfl
  obtain ⟨i, j, hij⟩ : ∃ i j, (M' : Matrix (Fin 3) (Fin 3) K) i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hM'0 (Matrix.ext h)
  set m := (M' : Matrix (Fin 3) (Fin 3) K) i j with hm
  have hentry : ∀ a b, ψ ((M' : Matrix (Fin 3) (Fin 3) K) a b) =
      (c : K) * (M' : Matrix (Fin 3) (Fin 3) K) a b := by
    intro a b
    have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) a b) hc
    simp only [Units.val_mul, coe_scalar_three, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul] at this
    exact this
  have hψm : ψ m = (c : K) * m := hentry i j
  set M₀ : Matrix (Fin 3) (Fin 3) K := m⁻¹ • (M' : Matrix (Fin 3) (Fin 3) K) with hM₀
  have hM₀fix : M₀.map ψ = M₀ := by
    ext a b
    simp only [M₀, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [map_mul, map_inv₀, hψm, hentry a b]
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    field_simp
  have hdetfix : ψ M₀.det = M₀.det := by
    have h := RingHom.map_det (ψ : K →+* K) M₀
    rw [show (ψ : K →+* K).mapMatrix M₀ = M₀.map ψ from rfl, hM₀fix] at h
    exact h
  have hdet0 : M₀.det ≠ 0 := by
    rw [hM₀, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hij)) (Matrix.isUnits_det_units M').ne_zero
  obtain ⟨ν, hν⟩ := isCube_of_fixed hK3 hψ hdet0 hdetfix
  have hM'cube : (M' : Matrix (Fin 3) (Fin 3) K).det = (m * ν) ^ 3 := by
    have e1 : (M' : Matrix (Fin 3) (Fin 3) K) = m • M₀ := by
      rw [hM₀, smul_smul, mul_inv_cancel₀ hij, one_smul]
    rw [e1, Matrix.det_smul, Fintype.card_fin, hν, mul_pow]
  have hy' : conjAut 3 K M' ∈ I := conjAut_mem_range_of_det hM'cube
  have hyI : conjAut 3 K M ∈ I := by
    have e2 : conjAut 3 K M = conjAut 3 K H * conjAut 3 K M' * (conjAut 3 K H)⁻¹ := by
      rw [hM', map_mul, map_mul, map_inv]
      group
    rw [e2]
    exact Item211Res5Proof.conj_mem_range_conj' _ hy'
  exact hy1 (hcon _ hyD hyI)

end DInn

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
