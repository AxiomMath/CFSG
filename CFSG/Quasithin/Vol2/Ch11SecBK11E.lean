module

public import CFSG.Quasithin.Vol2.Ch11SecBK11D
public import CFSG.Quasithin.Vol2.Ch11SecBK11A
public import CFSG.Quasithin.Vol2.Ch11SecBK11B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.BK11

open CFSG.Open CFSG.QuasithinUnique
open CFSG.RankThree.SubgroupLists (negDiag3 exists_conj_negDiag3 exists_lift_pow_eq_one
  commute_of_commute_mk)

variable {S : Type} [Group S] {B : Subgroup S} [Finite S] {K : Type} [Field K] [Finite K]
  {H : Subgroup (GL (Fin 3) K)} {Z : Subgroup ↥H} [Z.Normal]

theorem card_le_of_pCore_ne_bot (h2 : (2 : K) ≠ 0)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZc : Z ≤ Subgroup.center ↥H) (hZ3 : ∀ z ∈ Z, z ^ 3 = 1) (e : S ≃* ↥H ⧸ Z) (Λ : Finset K)
    (hΛ : ∀ (z t P : GL (Fin 3) K) (l m : K) (k : ℕ), z ∈ H → t ∈ H →
      P⁻¹ * z * P = negDiag3 K →
      ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![l, l, m] →
      t ^ 2 ^ k = 1 → l ∈ Λ)
    (hO : CFSG.pCore 2 ↥B ≠ ⊥) (hZB : ∀ o ∈ pCoreOf 2 B, ∀ y ∈ B, o * y = y * o)
    (eA : ↥B ⧸ CFSG.pCore 2 ↥B ≃* alternatingGroup (Fin 5)) {T : Subgroup S}
    (hT2 : ∀ t ∈ T, ∃ k : ℕ, t ^ 2 ^ k = 1) (hTB : ∀ t ∈ T, ∀ y ∈ B, t * y = y * t) :
    Nat.card T ≤ Λ.card := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m₀, hm₀⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
  have h2O : 2 ∣ Nat.card ↥(CFSG.pCore 2 ↥B) := by
    rw [hm₀]
    rcases m₀ with _ | m₀
    · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hm₀, pow_zero])) hO
    · exact dvd_pow_self 2 (Nat.succ_ne_zero m₀)
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 2 h2O
  have hzO : (((z₀ : ↥B) : S)) ∈ pCoreOf 2 B := coe_mem_pCoreOf_iff.mpr z₀.2
  have hz2 : ((z₀ : ↥B) : S) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z₀
    rw [hz₀] at h
    have h' := congrArg (fun w : ↥(CFSG.pCore 2 ↥B) => ((w : ↥B) : S)) h
    simpa using h'
  have hz1 : ((z₀ : ↥B) : S) ≠ 1 := by
    intro h
    have : z₀ = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hz₀
    exact absurd hz₀ (by norm_num)
  set z : S := ((z₀ : ↥B) : S) with hz
  have hzB : z ∈ B := (z₀ : ↥B).2
  have hzc : ∀ y ∈ B, z * y = y * z := hZB z hzO
  obtain ⟨y₁, y₂, hy₁, hy₂, hy⟩ : ∃ y₁ y₂ : S, y₁ ∈ B ∧ y₂ ∈ B ∧ y₁ * y₂ ≠ y₂ * y₁ := by
    obtain ⟨q₁, hq₁⟩ := QuotientGroup.mk_surjective (eA.symm a5u)
    obtain ⟨q₂, hq₂⟩ := QuotientGroup.mk_surjective (eA.symm a5w)
    refine ⟨q₁, q₂, q₁.2, q₂.2, fun h => a5_noncomm ?_⟩
    have h' : q₁ * q₂ = q₂ * q₁ := Subtype.ext h
    have h'' := congrArg (fun q : ↥B => eA (q : ↥B ⧸ CFSG.pCore 2 ↥B)) h'
    simp only [QuotientGroup.mk_mul, map_mul, hq₁, hq₂, MulEquiv.apply_symm_apply] at h''
    exact h''
  have hcm : ∀ (x y : ↥H) (s s' : S) (n : ℕ), Nat.Coprime n 3 → (x : ↥H ⧸ Z) = e s →
      (y : ↥H ⧸ Z) = e s' → x ^ n = 1 → s * s' = s' * s → (x : GL (Fin 3) K) * y = y * x :=
    fun x y s s' n hn hx hy hxn hss' => congrArg Subtype.val (commute_of_commute_mk hZc hZ3 hn
      hxn (by rw [hx, hy, ← map_mul, hss', map_mul]))
  obtain ⟨z', hz'e, hz'2⟩ := exists_lift_pow_eq_one hZc hZ3 (n := 2) (by norm_num) (e z)
    (by rw [← map_pow, hz2, map_one])
  obtain ⟨y₁', hy₁'⟩ := QuotientGroup.mk_surjective (e y₁)
  obtain ⟨y₂', hy₂'⟩ := QuotientGroup.mk_surjective (e y₂)
  have hz'y₁ : (y₁' : GL (Fin 3) K) * z' = z' * y₁' :=
    (hcm z' y₁' z y₁ 2 (by norm_num) hz'e hy₁' hz'2 (hzc y₁ hy₁)).symm
  have hz'y₂ : (y₂' : GL (Fin 3) K) * z' = z' * y₂' :=
    (hcm z' y₂' z y₂ 2 (by norm_num) hz'e hy₂' hz'2 (hzc y₂ hy₂)).symm
  have hy' : (y₁' : GL (Fin 3) K) * y₂' ≠ y₂' * y₁' := by
    intro h
    apply hy
    apply e.injective
    have h' : y₁' * y₂' = y₂' * y₁' := Subtype.ext h
    rw [map_mul, map_mul, ← hy₁', ← hy₂', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h']
  have hz'1 : (z' : GL (Fin 3) K) ≠ 1 := fun h => hz1 (e.injective (by
    rw [map_one, ← hz'e, show z' = 1 from Subtype.ext h, QuotientGroup.mk_one]))
  have hz'sq : (z' : GL (Fin 3) K) * z' = 1 := by
    rw [← Subgroup.coe_mul, ← pow_two, hz'2, Subgroup.coe_one]
  obtain ⟨P, hP⟩ := exists_conj_negDiag3 h2 hz'sq hz'1 (hdet _ z'.2)
  have hscal : ∀ t : ↥T, ∃ l ∈ Λ, ∃ t' : ↥H, (t' : ↥H ⧸ Z) = e t ∧ ∃ m : K,
      ((P⁻¹ * t' * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal ![l, l, m] := by
    rintro ⟨t, ht⟩
    obtain ⟨k, hk⟩ := hT2 t ht
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
    obtain ⟨t', ht'e, ht'k⟩ := exists_lift_pow_eq_one hZc hZ3 hcop (e t)
      (by rw [← map_pow, hk, map_one])
    obtain ⟨l, m, hlm⟩ := exists_diagonal_of_commute h2 hP
      (hcm t' z' t z _ hcop ht'e hz'e ht'k (hTB t ht z hzB)) hz'y₁ hz'y₂
      (hcm t' y₁' t y₁ _ hcop ht'e hy₁' ht'k (hTB t ht y₁ hy₁))
      (hcm t' y₂' t y₂ _ hcop ht'e hy₂' ht'k (hTB t ht y₂ hy₂)) hy'
    refine ⟨l, hΛ z' t' P l m k z'.2 t'.2 hP hlm (by
      rw [← Subgroup.coe_pow, ht'k, Subgroup.coe_one]), t', ht'e, m, hlm⟩
  choose l hl t' ht'e m hm using hscal
  have hdetc : ∀ x : ↥H, ((P⁻¹ * x * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    intro x
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet _ x.2, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  have hinj : Function.Injective (fun t : ↥T => (⟨l t, hl t⟩ : ↥Λ)) := by
    intro t s hts
    have hl' : l t = l s := congrArg Subtype.val hts
    have ht1 := hdetc (t' t)
    have hs1 := hdetc (t' s)
    rw [hm t, Matrix.det_diagonal, Fin.prod_univ_three] at ht1
    rw [hm s, Matrix.det_diagonal, Fin.prod_univ_three] at hs1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at ht1 hs1
    have hmeq : m t = m s := by
      rw [hl'] at ht1
      have hll : l s * l s ≠ 0 := fun h => by rw [h, zero_mul] at hs1; exact zero_ne_one hs1
      exact mul_left_cancel₀ hll (ht1.trans hs1.symm)
    have hPP : P⁻¹ * (t' t : GL (Fin 3) K) * P = P⁻¹ * (t' s : GL (Fin 3) K) * P :=
      Units.ext (by rw [hm t, hm s, hl', hmeq])
    have htt : t' t = t' s := Subtype.ext (mul_left_cancel (mul_right_cancel hPP))
    exact Subtype.ext (e.injective (by rw [← ht'e t, ← ht'e s, htt]))
  have hcard := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := ↥Λ), Fintype.card_coe] at hcard

theorem outerLevi_of_model (h2 : (2 : K) ≠ 0)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZc : Z ≤ Subgroup.center ↥H) (hZ3 : ∀ z ∈ Z, z ^ 3 = 1) (e : S ≃* ↥H ⧸ Z) (Λ : Finset K)
    (hΛ : ∀ (z t P : GL (Fin 3) K) (l m : K) (k : ℕ), z ∈ H → t ∈ H →
      P⁻¹ * z * P = negDiag3 K →
      ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![l, l, m] →
      t ^ 2 ^ k = 1 → l ∈ Λ)
    (h64 : ¬ 64 ∣ Nat.card S) {R : Subgroup S} (hR2 : IsPGroup 2 R)
    (hRc : 4 * Λ.card < Nat.card R) (hR4 : 4 < Nat.card R)
    (hRB : R ≤ Subgroup.normalizer (B : Set S)) (hB : ⁅B, B⁆ = B)
    (hF : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∃ r ∈ R, ∀ b ∈ B, ∃ y ∈ B, r * y * r⁻¹ * (b * y * b⁻¹)⁻¹ ∉ pCoreOf 2 B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨F, _, _, hF4, ⟨eF⟩⟩ := hF
  have h60 := card_quot hF4 eF
  have hidx := relIndex_secCent_dvd_four hR2 hRB (by rw [relIndex_pCoreOf_eq, h60]) hcon
  have hRT : Nat.card R ≤ 4 * Nat.card ↥(secCent B ⊓ R) := by
    rw [← Subgroup.relIndex_mul_card (secCent B) R]
    exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (by norm_num) hidx)
  have hZB := commute_pCore hB hF4 eF (card_pCore_le_eight h64 h60)
  have hZB' : ∀ o ∈ pCoreOf 2 B, ∀ y ∈ B, o * y = y * o := by
    intro o ho y hy
    have hoB := pCoreOf_le ho
    exact congrArg Subtype.val (hZB ⟨o, hoB⟩ (coe_mem_pCoreOf_iff.mp ho) ⟨y, hy⟩)
  have hTB : ∀ x ∈ secCent B ⊓ R, ∀ y ∈ B, x * y = y * x := fun x hx =>
    commute_of_mem_secCent hB hZB' (Subgroup.mem_inf.mp hx).1
  have hT2 : ∀ x ∈ secCent B ⊓ R, ∃ k : ℕ, x ^ 2 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hR2 ⟨x, (Subgroup.mem_inf.mp hx).2⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨eA⟩ := nonempty_quot_equiv_a5 hF4 eF
  by_cases hO : CFSG.pCore 2 ↥B = ⊥
  ·
    have hTp : IsPGroup 2 ↥(secCent B ⊓ R) := hR2.to_le inf_le_right
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTp
    have h2dvd : 2 ∣ Nat.card ↥(secCent B ⊓ R) := by
      rw [hn]
      rcases n with _ | n
      · rw [hn, pow_zero] at hRT
        omega
      · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
    obtain ⟨⟨t, htT⟩, htord⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    have ht2 : t * t = 1 := by
      have h := pow_orderOf_eq_one (⟨t, htT⟩ : ↥(secCent B ⊓ R))
      rw [htord, pow_two] at h
      exact congrArg Subtype.val h
    have ht1 : t ≠ 1 := by
      intro h
      have : (⟨t, htT⟩ : ↥(secCent B ⊓ R)) = 1 := Subtype.ext h
      rw [this, orderOf_one] at htord
      exact absurd htord (by norm_num)
    exact false_of_pCore_eq_bot h2 hdet hZc hZ3 e hO eA ht2 ht1 (hTB t htT)
  · have hle := card_le_of_pCore_ne_bot h2 hdet hZc hZ3 e Λ hΛ hO hZB' eA hT2 hTB
    omega

end CFSG.Quasithin.Vol2.Ch11.SecA.BK11
