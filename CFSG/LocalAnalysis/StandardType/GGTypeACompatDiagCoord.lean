module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarDiagB
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix

private def ggDiagCoordTarget (p n : ℕ) (F : Type) [Field F] :
    Subgroup (Fin (n + 1) → Fˣ) where
  carrier := {v | v 0 = 1 ∧ ∀ i, v i ^ p = 1}
  mul_mem' := by
    intro a b ha hb
    exact ⟨by rw [Pi.mul_apply, ha.1, hb.1, one_mul],
      fun i => by rw [Pi.mul_apply, mul_pow, ha.2 i, hb.2 i, one_mul]⟩
  one_mem' := ⟨by simp, fun i => by simp⟩
  inv_mem' := by
    intro a ha
    exact ⟨by rw [Pi.inv_apply, ha.1, inv_one],
      fun i => by rw [Pi.inv_apply, inv_pow, ha.2 i, inv_one]⟩

private theorem card_units_pow_eq_one_le {F : Type} [Field F] [Finite F] {p : ℕ} (hp : 0 < p) :
    Nat.card {x : Fˣ // x ^ p = 1} ≤ p := by
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  haveI : DecidableEq Fˣ := Classical.decEq Fˣ
  haveI : IsCyclic Fˣ := instIsCyclicUnitsOfFinite
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsCyclic.card_pow_eq_one_le hp

private theorem natCard_ggDiagCoordTarget_le {F : Type} [Field F] [Finite F] {p n : ℕ}
    (hp : 0 < p) : Nat.card (ggDiagCoordTarget p n F) ≤ p ^ n := by
  have hS : Nat.card {x : Fˣ // x ^ p = 1} ≤ p := card_units_pow_eq_one_le hp
  have hinj : Function.Injective (fun v : ↥(ggDiagCoordTarget p n F) =>
      fun i : Fin n => (⟨v.1 i.succ, v.2.2 i.succ⟩ : {x : Fˣ // x ^ p = 1})) := by
    intro v w h
    apply Subtype.ext
    funext i
    induction i using Fin.cases with
    | zero => rw [v.2.1, w.2.1]
    | succ j => exact Subtype.ext_iff.mp (congrFun h j)
  have h1 : Nat.card (↥(ggDiagCoordTarget p n F)) ≤
      Nat.card (Fin n → {x : Fˣ // x ^ p = 1}) :=
    Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (Fin n → {x : Fˣ // x ^ p = 1}) = Nat.card {x : Fˣ // x ^ p = 1} ^ n := by
    rw [Nat.card_fun, Nat.card_fin]
  calc Nat.card (↥(ggDiagCoordTarget p n F))
      ≤ Nat.card (Fin n → {x : Fˣ // x ^ p = 1}) := h1
    _ = Nat.card {x : Fˣ // x ^ p = 1} ^ n := h2
    _ ≤ p ^ n := Nat.pow_le_pow_left hS n

private theorem exists_diagAt_of_not_dvd {X : Type} [Group X] {F : Type} [Field F]
    {p n : ℕ} (hp : p.Prime) {ζ : Fˣ} (hζ : orderOf ζ = p) (hpn : ¬ p ∣ n + 1)
    {Bs : Subgroup X}
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set X), g ^ p = 1 → g ∈ Bs)
    {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b) :
    ∃ k : Fin (n + 1), ∃ τ : Fˣ, τ ≠ 1 ∧ ∃ g ∈ Bs, GGActsVec φ g (diagAt k τ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hζp : ζ ^ p = 1 := (orderOf_eq_prime_iff.mp hζ).1
  have hζne : ζ ≠ 1 := (orderOf_eq_prime_iff.mp hζ).2
  let u : Fin (n + 1) → Fˣ := Fin.cons (ζ⁻¹ ^ n) (fun _ : Fin n => ζ)
  have hu0 : u 0 = ζ⁻¹ ^ n := Fin.cons_zero _ _
  have husucc : ∀ i : Fin n, u i.succ = ζ := fun i => Fin.cons_succ _ _ i
  have hupow : ∀ i, u i ^ p = 1 := by
    intro i
    induction i using Fin.cases with
    | zero =>
        rw [hu0, inv_pow, inv_pow, ← pow_mul, mul_comm, pow_mul, hζp, one_pow, inv_one]
    | succ j => rw [husucc j, hζp]
  have huprod : ∏ i, u i = 1 := by
    rw [Fin.prod_univ_succ]
    simp only [hu0, husucc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [inv_pow, inv_mul_cancel]
  let t : SpecialLinearGroup (Fin (n + 1)) F :=
    ⟨diagonal (fun i => (u i : F)), by
      rw [det_diagonal]
      have h := congrArg (fun w : Fˣ => (w : F)) huprod
      simpa using h⟩
  have ht_coe : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F) = diagonal (fun i => (u i : F)) := rfl
  have ht_pow : t ^ p = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ht_coe, Matrix.diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one, ← diagonal_one]
    congr 1
    funext i
    rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val, hupow i, Units.val_one]
  have htinv : (↑(t⁻¹) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
      diagonal (fun i => ((u i)⁻¹ : F)) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, ht_coe, adjugate_diagonal]
    congr 1
    funext i
    have hdet : (∏ j, (u j : F)) = 1 := by
      have h' := congrArg (fun w : Fˣ => (w : F)) huprod
      simpa using h'
    have h := Finset.prod_erase_mul (Finset.univ : Finset (Fin (n + 1)))
      (fun j => (u j : F)) (Finset.mem_univ i)
    rw [hdet] at h
    simpa [Units.val_inv_eq_inv_val] using eq_inv_of_mul_eq_one_left h
  have hcomm : φ t ∈ Subgroup.centralizer (Bs : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨w, hw⟩ := hdiag b hb
    have e : ggDiagConj w t = t := by
      apply Subtype.ext
      ext i j
      rw [ggDiagConj_apply, ht_coe]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq]
        rw [Units.val_inv_eq_inv_val]
        have hwi : (↑(w i) : F) ≠ 0 := Units.ne_zero (w i)
        field_simp
      · rw [Matrix.diagonal_apply_ne _ hij, mul_zero, zero_mul]
    calc b * φ t = b * φ t * b⁻¹ * b := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = φ (ggDiagConj w t) * b := by rw [hw t]
      _ = φ t * b := by rw [e]
  have hg0 : φ t ∈ Bs := hBsC (φ t) hcomm (by rw [← map_pow, ht_pow, map_one])
  have hU : GGActsVec φ (φ t) u := by
    intro s
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ht_coe, htinv,
      coe_ggDiagConj]
    simp only [Units.val_inv_eq_inv_val]
  let τ : Fˣ := ζ⁻¹ ^ (n + 1)
  have hu_eq : u = (fun _ : Fin (n + 1) => ζ) * diagAt 0 τ := by
    funext i
    induction i using Fin.cases with
    | zero =>
        rw [Pi.mul_apply, hu0, diagAt_apply_self]
        show ζ⁻¹ ^ n = ζ * (ζ⁻¹ ^ (n + 1))
        rw [pow_succ', ← mul_assoc, mul_inv_cancel, one_mul]
    | succ j =>
        rw [Pi.mul_apply, husucc j, diagAt_apply_of_ne (Fin.succ_ne_zero j), mul_one]
  have hV : GGActsVec φ (φ t) (diagAt 0 τ) :=
    hU.of_vecEq (by rw [hu_eq]; exact ggVecEq_iff_exists.mpr ⟨ζ, fun i => rfl⟩)
  have hτ : τ ≠ 1 := by
    intro h
    apply hpn
    have h1 : ζ ^ (n + 1) = 1 := by
      have := congrArg (fun x : Fˣ => x⁻¹) h
      simpa [τ, inv_pow] using this
    have h2 : orderOf ζ ∣ n + 1 := orderOf_dvd_iff_pow_eq_one.mpr h1
    rwa [hζ] at h2
  exact ⟨0, τ, hτ, φ t, hg0, hV⟩

private theorem div_const_normalize {G : Type} [CommGroup G] (d x y : G) :
    (d * x) * (d * y)⁻¹ = x * y⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv x y, div_eq_div_iff_mul_eq_mul, mul_comm d x, mul_assoc]

private theorem div_const_normalize_mul {G : Type} [CommGroup G] (d x1 x2 y1 y2 : G) :
    (d * (x1 * x2)) * (d * (y1 * y2))⁻¹ = (x1 * y1⁻¹) * (x2 * y2⁻¹) := by
  rw [div_const_normalize d (x1 * x2) (y1 * y2)]
  rw [← div_eq_mul_inv (x1 * x2) (y1 * y2), ← div_eq_mul_inv x1 y1, ← div_eq_mul_inv x2 y2,
      div_mul_div_comm]

private theorem exists_diagAt_of_dvd {X : Type} [Group X] [Finite X] {F : Type} [Field F]
    [Finite F] {p n : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card Fˣ) (hpn : p ∣ n + 1)
    {Bs : Subgroup X} (hBs : IsElemAbelian p Bs)
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set X), g ^ p = 1 → g ∈ Bs)
    {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b)
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (φ.range : Set X)) ≤ p)
    (hfull : p ^ (n + 1) ≤ Nat.card Bs) :
    ∃ k : Fin (n + 1), ∃ τ : Fˣ, τ ≠ 1 ∧ ∃ g ∈ Bs, GGActsVec φ g (diagAt k τ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hpF
  have hζp : ζ ^ p = 1 := (orderOf_eq_prime_iff.mp hζ).1
  have hζne : ζ ≠ 1 := (orderOf_eq_prime_iff.mp hζ).2
  let hv : Bs → (Fin (n + 1) → Fˣ) := fun b => Classical.choose (hdiag b b.2)
  have hv_spec : ∀ b : Bs, GGActsVec φ (b : X) (hv b) := fun b =>
    Classical.choose_spec (hdiag b b.2)
  let Theta : Bs →* (Fin (n + 1) → Fˣ) :=
    { toFun := fun b => fun i => hv b i * (hv b 0)⁻¹
      map_one' := by
        funext i
        have hconst : ∀ i j, hv 1 i = hv 1 j := by
          have e : GGVecEq (hv 1) 1 :=
            GGActsVec.vecEq hker (hv_spec 1)
              (GGActsVec.one_of_commute (fun s => by simp))
          exact ggVecEq_one_iff.mp e
        show hv 1 i * (hv 1 0)⁻¹ = 1
        rw [hconst i 0, mul_inv_cancel]
      map_mul' := by
        intro a b
        funext i
        obtain ⟨d, hd⟩ := ggVecEq_iff_exists.mp
          (GGActsVec.vecEq hker (hv_spec (a * b)) (GGActsVec.mul (hv_spec a) (hv_spec b)))
        show hv (a * b) i * (hv (a * b) 0)⁻¹ =
          (hv a i * (hv a 0)⁻¹) * (hv b i * (hv b 0)⁻¹)
        rw [hd i, hd 0, Pi.mul_apply, Pi.mul_apply]
        exact div_const_normalize_mul d (hv a i) (hv b i) (hv a 0) (hv b 0) }
  have Theta_apply : ∀ (b : Bs) (i : Fin (n + 1)), Theta b i = hv b i * (hv b 0)⁻¹ :=
    fun b i => rfl
  let Target : Subgroup (Fin (n + 1) → Fˣ) := ggDiagCoordTarget p n F
  have hpow_const : ∀ (b : Bs) (i : Fin (n + 1)), hv b i ^ p = hv b 0 ^ p := by
    intro b i
    have h2 : GGActsVec φ ((b : X) ^ p) ((hv b) ^ p) := GGActsDiag.pow (hv_spec b) p
    rw [hBs.2 b b.2] at h2
    have e : GGVecEq ((hv b) ^ p) 1 :=
      GGActsVec.vecEq hker h2 (GGActsVec.one_of_commute (fun s => by simp))
    have := ggVecEq_one_iff.mp e
    simpa [Pi.pow_apply] using this i 0
  have hrange_le : Theta.range ≤ Target := by
    rintro v ⟨b, rfl⟩
    change Theta b 0 = 1 ∧ ∀ i, Theta b i ^ p = 1
    refine ⟨?_, ?_⟩
    · rw [Theta_apply, mul_inv_cancel]
    · intro i
      rw [Theta_apply, mul_pow, hpow_const b i, inv_pow, mul_inv_cancel]
  have hker_le : Nat.card Theta.ker ≤ p := by
    have hmap : ∀ x : Theta.ker, (x.1 : X) ∈ Bs ⊓ Subgroup.centralizer (φ.range : Set X) := by
      intro x
      refine Subgroup.mem_inf.mpr ⟨x.1.2, ?_⟩
      change (x.1 : X) ∈ Subgroup.centralizer (φ.range : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨s, rfl⟩ := hy
      have hx : ∀ k l, hv x.1 k = hv x.1 l := by
        intro k l
        have hk := congrFun (MonoidHom.mem_ker.mp x.2) k
        have hl := congrFun (MonoidHom.mem_ker.mp x.2) l
        rw [Theta_apply, Pi.one_apply] at hk hl
        exact (mul_inv_eq_one.mp hk).trans (mul_inv_eq_one.mp hl).symm
      exact (GGActsVec.commute_of_vecEq_one (hv_spec x.1) (ggVecEq_one_iff.mpr hx) s).symm
    have hinj : Function.Injective (fun x : Theta.ker =>
        (⟨(x.1 : X), hmap x⟩ : ↥(Bs ⊓ Subgroup.centralizer (φ.range : Set X)))) := by
      intro x y h
      have h1 : (x.1 : X) = (y.1 : X) :=
        congrArg (fun z : ↥(Bs ⊓ Subgroup.centralizer (φ.range : Set X)) => (z.1 : X)) h
      exact Subtype.ext (Subtype.ext h1)
    calc Nat.card Theta.ker ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (φ.range : Set X)) :=
          Nat.card_le_card_of_injective _ hinj
      _ ≤ p := hC
  have hrange_ge : p ^ n ≤ Nat.card Theta.range := by
    have hprod := Subgroup.card_ker_mul_card_range Theta
    have h1 : p ^ (n + 1) ≤ Nat.card Theta.ker * Nat.card Theta.range := hprod ▸ hfull
    have h2 : p ^ (n + 1) = p * p ^ n := by rw [pow_succ']
    have h3 : Nat.card Theta.ker * Nat.card Theta.range ≤ p * Nat.card Theta.range :=
      Nat.mul_le_mul_right _ hker_le
    have h4 : p * p ^ n ≤ p * Nat.card Theta.range := by rw [← h2]; exact le_trans h1 h3
    exact Nat.le_of_mul_le_mul_left h4 hp.pos
  have hTarget_le : Nat.card Target ≤ p ^ n := by
    simpa [Target] using natCard_ggDiagCoordTarget_le (F := F) (p := p) (n := n) hp.pos
  have hrange_eq : Theta.range = Target :=
    Subgroup.eq_of_le_of_card_ge hrange_le (le_trans hTarget_le hrange_ge)
  have hn1 : 1 < n + 1 := by
    have hp2 : 2 ≤ p := hp.two_le
    have hle : p ≤ n + 1 := Nat.le_of_dvd (by omega) hpn
    omega
  let k : Fin (n + 1) := ⟨1, hn1⟩
  have hk0 : (0 : Fin (n + 1)) ≠ k := by
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)
  let v : Fin (n + 1) → Fˣ := diagAt k ζ
  have hvTarget : v ∈ Target := by
    change v 0 = 1 ∧ ∀ i, v i ^ p = 1
    refine ⟨?_, ?_⟩
    · show diagAt k ζ 0 = 1
      rw [diagAt_apply_of_ne hk0]
    · intro i
      by_cases hi : i = k
      · subst hi
        rw [show v k = ζ from diagAt_apply_self k ζ, hζp]
      · rw [show v i = 1 from diagAt_apply_of_ne hi ζ, one_pow]
  have hvRange : v ∈ Theta.range := by rw [hrange_eq]; exact hvTarget
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hvRange
  have hvec : GGVecEq (hv b) v := by
    apply ggVecEq_iff_exists.mpr
    refine ⟨hv b 0, fun i => ?_⟩
    have hi := congrFun hb i
    rw [Theta_apply, mul_inv_eq_iff_eq_mul] at hi
    rw [hi, mul_comm]
  refine ⟨k, ζ, hζne, b, b.2, ?_⟩
  exact (hv_spec b).of_vecEq (by simpa [v] using hvec)

theorem exists_actsVec_diagAt_of_bstar {X : Type} [Group X] [Finite X] {F : Type} [Field F]
    [Finite F] (h2 : (2 : F) = 0) {p n : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card Fˣ)
    {Bs : Subgroup X}
    (hBs : IsElemAbelian p Bs)
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set X), g ^ p = 1 → g ∈ Bs)
    {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b)
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (φ.range : Set X)) ≤ p)
    (hfull : p ∣ n + 1 → p ^ (n + 1) ≤ Nat.card Bs) (r : Fin (n + 1)) :
    ∃ g ∈ Bs, ∃ τ : Fˣ, τ ≠ 1 ∧ GGActsVec φ g (diagAt r τ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hpF
  by_cases hpn : p ∣ n + 1
  · obtain ⟨k, τ, hτ, g, hg, hv⟩ :=
      exists_diagAt_of_dvd hp hpF hpn hBs hBsC hker hdiag hC (hfull hpn)
    obtain ⟨g', hg', hv'⟩ := exists_mem_actsVec_diagAt h2 hBs.2 hBsC hker hdiag hg hv r
    exact ⟨g', hg', τ, hτ, hv'⟩
  · obtain ⟨k, τ, hτ, g, hg, hv⟩ :=
      exists_diagAt_of_not_dvd hp hζ hpn hBsC hdiag
    obtain ⟨g', hg', hv'⟩ := exists_mem_actsVec_diagAt h2 hBs.2 hBsC hker hdiag hg hv r
    exact ⟨g', hg', τ, hτ, hv'⟩

end CFSG.StandardType

end
