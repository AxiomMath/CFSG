module

public import CFSG.RankThree.GF2n.Smith81.S81JMat
public import CFSG.Open.StatedDefs
public import CFSG.Open.StatedAPI
public import CFSG.RankThree.GF2n.Smith81.S81BA5Rank

public section

namespace CFSG.RankThree.GF2n.Smith81.S81J

open CFSG.Open

theorem gl_comm_of_sq_one {Γ : Type*} [Group Γ] {h h' : Γ} (n : Γ) (hh : h * h = 1)
    (hn : n = h * h' * h⁻¹ * h'⁻¹) (hc : ∀ x : Γ, n * x = x * n) (h3 : n ^ 3 = 1) :
    h * h' = h' * h := by
  have hinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  have hn' : n * h' = h * h' * h⁻¹ := by
    rw [hn]
    group
  have e1 : h * (n * h') * h⁻¹ * h'⁻¹ = n * n := by
    calc h * (n * h') * h⁻¹ * h'⁻¹ = (h * n) * h' * h⁻¹ * h'⁻¹ := by simp only [mul_assoc]
      _ = (n * h) * h' * h⁻¹ * h'⁻¹ := by rw [hc h]
      _ = n * (h * h' * h⁻¹ * h'⁻¹) := by simp only [mul_assoc]
      _ = n * n := by rw [← hn]
  have e2 : h * (n * h') * h⁻¹ * h'⁻¹ = 1 := by
    rw [hn']
    calc h * (h * h' * h⁻¹) * h⁻¹ * h'⁻¹ = (h * h) * h' * (h⁻¹ * h⁻¹) * h'⁻¹ := by
          simp only [mul_assoc]
      _ = 1 := by simp [hinv, hh]
  have hnn : n * n = 1 := by
    rw [← e1]
    exact e2
  have hn1 : n = 1 := by
    calc n = n * (n * n) := by rw [hnn, mul_one]
      _ = n ^ 3 := (pow_three n).symm
      _ = 1 := h3
  rw [hn1] at hn
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hn.symm)

theorem gl_det_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin 6) R) :
    (Matrix.GeneralLinearGroup.map f g : Matrix (Fin 6) (Fin 6) S).det =
      f ((g : Matrix (Fin 6) (Fin 6) R).det) :=
  (RingHom.map_det f _).symm

theorem gl_symm_map_map {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') (g : GL (Fin 6) K) :
    Matrix.GeneralLinearGroup.map (e.symm : K' →+* K)
      (Matrix.GeneralLinearGroup.map (e : K →+* K') g) = g := by
  apply Units.ext
  ext i j
  simp

theorem gl_map_symm_map {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') (g : GL (Fin 6) K') :
    Matrix.GeneralLinearGroup.map (e : K →+* K')
      (Matrix.GeneralLinearGroup.map (e.symm : K' →+* K) g) = g := by
  apply Units.ext
  ext i j
  simp

theorem exists_lift_involutions {Γ X : Type*} [Group Γ] [Group X] (π : Γ →* X)
    (hπ : Function.Surjective π) (hker3 : ∀ n ∈ π.ker, n ^ 3 = 1)
    (hkerc : ∀ n ∈ π.ker, ∀ x : Γ, n * x = x * n) (E' : Subgroup X)
    (hcomm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x) (hsq : ∀ x ∈ E', x * x = 1) :
    ∃ E : Subgroup Γ, (∀ h ∈ E, h * h = 1) ∧ (∀ h ∈ E, ∀ h' ∈ E, h * h' = h' * h) ∧
      E.map π = E' ∧ Nat.card E = Nat.card E' := by
  have hC : ∀ x y : Γ, π x ∈ E' → π y ∈ E' → x * x = 1 → x * y = y * x := by
    intro x y hx hy hxx
    have hxy := hcomm _ hx _ hy
    have hpi : π (x * y * x⁻¹ * y⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      calc π x * π y * (π x)⁻¹ * (π y)⁻¹ = π y * π x * (π x)⁻¹ * (π y)⁻¹ := by rw [hxy]
        _ = 1 := by group
    have hker : x * y * x⁻¹ * y⁻¹ ∈ π.ker := MonoidHom.mem_ker.mpr hpi
    exact gl_comm_of_sq_one (h := x) (h' := y) _ hxx rfl (hkerc _ hker) (hker3 _ hker)
  obtain ⟨E, hE⟩ : ∃ E : Subgroup Γ, ∀ h : Γ, h ∈ E ↔ (π h ∈ E' ∧ h * h = 1) := by
    refine ⟨{ carrier := {h | π h ∈ E' ∧ h * h = 1}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun h => Iff.rfl⟩
    · rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
      show π (a * b) ∈ E' ∧ a * b * (a * b) = 1
      refine ⟨?_, ?_⟩
      · rw [map_mul]
        exact E'.mul_mem ha hb
      · have hab : a * b = b * a := hC a b ha hb ha2
        calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
          _ = a * (a * b) * b := by rw [hab]
          _ = (a * a) * (b * b) := by simp only [mul_assoc]
          _ = 1 := by rw [ha2, hb2, one_mul]
    · show π 1 ∈ E' ∧ (1 : Γ) * 1 = 1
      refine ⟨?_, mul_one 1⟩
      rw [map_one]
      exact E'.one_mem
    · rintro a ⟨ha, ha2⟩
      show π a⁻¹ ∈ E' ∧ a⁻¹ * a⁻¹ = 1
      have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
      refine ⟨?_, ?_⟩
      · rw [map_inv]
        exact E'.inv_mem ha
      · rw [hinv]
        exact ha2
  have hsurj : ∀ x ∈ E', ∃ k : Γ, k ∈ E ∧ π k = x := by
    intro x hx
    obtain ⟨h, hh⟩ := hπ x
    have hxx : x * x = 1 := hsq x hx
    have hπhh : π (h * h) = 1 := by rw [map_mul, hh, hxx]
    have hπk : π (h * h * h) = x := by rw [map_mul, map_mul, hh, hxx, one_mul]
    refine ⟨h * h * h, (hE _).2 ⟨?_, ?_⟩, hπk⟩
    · rw [hπk]
      exact hx
    · have h3 := hker3 (h * h) (MonoidHom.mem_ker.mpr hπhh)
      calc h * h * h * (h * h * h) = (h * h) ^ 3 := by simp only [pow_three, mul_assoc]
        _ = 1 := h3
  have hinj : ∀ a ∈ E, ∀ b ∈ E, π a = π b → a = b := by
    intro a ha b hb hab
    obtain ⟨ha1, ha2⟩ := (hE a).1 ha
    obtain ⟨hb1, hb2⟩ := (hE b).1 hb
    obtain ⟨m, hm⟩ : ∃ m : Γ, m = a⁻¹ * b := ⟨_, rfl⟩
    have hmker : m ∈ π.ker := by
      rw [MonoidHom.mem_ker, hm, map_mul, map_inv, hab, inv_mul_cancel]
    have hmc : ∀ x : Γ, m * x = x * m := hkerc m hmker
    have hm3 : m ^ 3 = 1 := hker3 m hmker
    have hb_eq : b = a * m := by
      rw [hm, mul_inv_cancel_left]
    have hmm : m * m = 1 := by
      have e : b * b = m * m := by
        calc b * b = (a * m) * (a * m) := by rw [hb_eq]
          _ = a * (m * a) * m := by simp only [mul_assoc]
          _ = a * (a * m) * m := by rw [hmc a]
          _ = (a * a) * (m * m) := by simp only [mul_assoc]
          _ = m * m := by rw [ha2, one_mul]
      rw [← e]
      exact hb2
    have hm1 : m = 1 := by
      calc m = m * (m * m) := by rw [hmm, mul_one]
        _ = m ^ 3 := (pow_three m).symm
        _ = 1 := hm3
    rw [hb_eq, hm1, mul_one]
  have hmap : E.map π = E' := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ((hE h).1 hh).1
    · intro hx
      obtain ⟨k, hk, hkx⟩ := hsurj x hx
      exact ⟨k, hk, hkx⟩
  have hcard : Nat.card E = Nat.card E' := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun h : E => (⟨π h.1, ((hE h.1).1 h.2).1⟩ : E')) ⟨?_, ?_⟩)
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have hab' : π a = π b := congrArg Subtype.val hab
      exact Subtype.ext (hinj a ha b hb hab')
    · rintro ⟨y, hy⟩
      obtain ⟨k, hk, hky⟩ := hsurj y hy
      exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
  exact ⟨E, fun h hh => ((hE h).1 hh).2,
    fun h hh h' hh' => hC h h' ((hE h).1 hh).1 ((hE h').1 hh').1 ((hE h).1 hh).2, hmap, hcard⟩

theorem scalar_mem_statedSL_pow_three {K : Type} [Field K] [CharP K 2] {h : GL (Fin 6) K}
    (hSL : h ∈ StatedSL 6 K) (c : Kˣ) (hc : h = Matrix.GeneralLinearGroup.scalar (Fin 6) c) :
    h ^ 3 = 1 := by
  have hdet : ((h : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    StatedAPI.mem_statedSL_iff.mp hSL
  have hmat : ((h : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = (c : K) • 1 := by
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have h6 : (c : K) ^ 6 = 1 := by
    rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    exact hdet
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : ((c : K) ^ 3 - 1) ^ 2 = 0 := by
    linear_combination h6 + (1 - (c : K) ^ 3) * h2
  have hc3 : (c : K) ^ 3 = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  have hcu : c ^ 3 = 1 := Units.ext (by simpa using hc3)
  rw [hc, ← map_pow, hcu, map_one]

theorem exists_Theta {K K' : Type} [Field K] [Field K'] [CharP K 2] (e : K ≃+* K') {X : Type}
    [Group X] (θ : X ≃* StatedProj (StatedSL 6 K')) :
    ∃ Θ : ↥(StatedSL 6 K) →* X, Function.Surjective Θ ∧ (∀ n ∈ Θ.ker, n ^ 3 = 1) ∧
      (∀ n ∈ Θ.ker, ∀ x : ↥(StatedSL 6 K), n * x = x * n) := by
  have hmem : ∀ g : GL (Fin 6) K, g ∈ StatedSL 6 K →
      Matrix.GeneralLinearGroup.map (e : K →+* K') g ∈ StatedSL 6 K' := by
    intro g hg
    rw [StatedAPI.mem_statedSL_iff, gl_det_map, StatedAPI.mem_statedSL_iff.mp hg, map_one]
  let eeSL : ↥(StatedSL 6 K) →* ↥(StatedSL 6 K') :=
    MonoidHom.codRestrict
      ((Matrix.GeneralLinearGroup.map (e : K →+* K')).comp (StatedSL 6 K).subtype)
      (StatedSL 6 K') (fun g => hmem g.1 g.2)
  have hsurjE : Function.Surjective eeSL := by
    rintro ⟨g', hg'⟩
    have hmem' : Matrix.GeneralLinearGroup.map (e.symm : K' →+* K) g' ∈ StatedSL 6 K := by
      rw [StatedAPI.mem_statedSL_iff, gl_det_map, StatedAPI.mem_statedSL_iff.mp hg', map_one]
    exact ⟨⟨_, hmem'⟩, Subtype.ext (gl_map_symm_map e g')⟩
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ↥(StatedSL 6 K) →* X, ∀ n, Θ n =
      θ.symm (QuotientGroup.mk' ((StatedScalars (Fin 6) K').subgroupOf (StatedSL 6 K')) (eeSL n)) :=
    ⟨θ.symm.toMonoidHom.comp
      ((QuotientGroup.mk' ((StatedScalars (Fin 6) K').subgroupOf (StatedSL 6 K'))).comp eeSL),
      fun n => rfl⟩
  have hker : ∀ n ∈ Θ.ker, ∃ c : Kˣ,
      ((n : ↥(StatedSL 6 K)) : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    intro n hn
    rw [MonoidHom.mem_ker, hΘ] at hn
    have h1 := θ.symm.map_eq_one_iff.mp hn
    rw [QuotientGroup.mk'_apply] at h1
    have h2 : eeSL n ∈ (StatedScalars (Fin 6) K').subgroupOf (StatedSL 6 K') :=
      (QuotientGroup.eq_one_iff _).mp h1
    have h3 : ((eeSL n : ↥(StatedSL 6 K')) : GL (Fin 6) K') ∈ StatedScalars (Fin 6) K' :=
      Subgroup.mem_subgroupOf.mp h2
    obtain ⟨c', hc'⟩ := MonoidHom.mem_range.mp h3
    have hφn : Matrix.GeneralLinearGroup.map (e : K →+* K') ((n : ↥(StatedSL 6 K)) : GL (Fin 6) K)
        = Matrix.GeneralLinearGroup.scalar (Fin 6) c' := hc'.symm
    refine ⟨Units.map (e.symm : K' →+* K).toMonoidHom c', ?_⟩
    calc ((n : ↥(StatedSL 6 K)) : GL (Fin 6) K)
        = Matrix.GeneralLinearGroup.map (e.symm : K' →+* K)
            (Matrix.GeneralLinearGroup.map (e : K →+* K') ((n : ↥(StatedSL 6 K)) : GL (Fin 6) K)) :=
          (gl_symm_map_map e _).symm
      _ = Matrix.GeneralLinearGroup.map (e.symm : K' →+* K)
            (Matrix.GeneralLinearGroup.scalar (Fin 6) c') := by rw [hφn]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6)
            (Units.map (e.symm : K' →+* K).toMonoidHom c') :=
          Matrix.GeneralLinearGroup.map_scalar (e.symm : K' →+* K) c'
  refine ⟨Θ, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
      ((StatedScalars (Fin 6) K').subgroupOf (StatedSL 6 K')) (θ x)
    obtain ⟨n, rfl⟩ := hsurjE g
    refine ⟨n, ?_⟩
    rw [hΘ, hg]
    exact θ.symm_apply_apply x
  · intro n hn
    obtain ⟨c, hc⟩ := hker n hn
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact scalar_mem_statedSL_pow_three n.2 c hc
  · intro n hn x
    obtain ⟨c, hc⟩ := hker n hn
    have hz : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ Subgroup.center (GL (Fin 6) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact MonoidHom.mem_range.mpr ⟨c, rfl⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact (Subgroup.mem_center_iff.mp hz (x : GL (Fin 6) K)).symm

end CFSG.RankThree.GF2n.Smith81.S81J
