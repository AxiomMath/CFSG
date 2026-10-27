module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15418Inspection

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace L15420

variable {G : Type*} [Group G]

theorem relIndex_sup_eq {D T : Subgroup G} (hT : T ≤ Subgroup.normalizer (D : Set G)) :
    D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

theorem relIndex_inf_eq [Finite G] {T N : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (N : Set G)) : (T ⊓ N).relIndex N = T.relIndex (T ⊔ N) := by
  have h1 := relIndex_sup_eq hT
  have e1 := Subgroup.relIndex_mul_card N (T ⊔ N)
  have e2 := Subgroup.relIndex_mul_card T (T ⊔ N)
  have e3 := Subgroup.relIndex_mul_card (T ⊓ N) T
  have e4 := Subgroup.relIndex_mul_card (T ⊓ N) N
  rw [inf_eq_left.mpr (le_sup_right : N ≤ T ⊔ N), h1] at e1
  rw [inf_eq_left.mpr (le_sup_left : T ≤ T ⊔ N)] at e2
  rw [inf_eq_left.mpr (inf_le_left : T ⊓ N ≤ T), Subgroup.inf_relIndex_left] at e3
  rw [inf_eq_left.mpr (inf_le_right : T ⊓ N ≤ N)] at e4
  have ha : 0 < N.relIndex T := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have ht : 0 < Nat.card ↥(T ⊓ N) := Nat.card_pos
  have key : (T ⊓ N).relIndex N * (N.relIndex T * Nat.card ↥(T ⊓ N)) =
      T.relIndex (T ⊔ N) * (N.relIndex T * Nat.card ↥(T ⊓ N)) := by
    calc (T ⊓ N).relIndex N * (N.relIndex T * Nat.card ↥(T ⊓ N))
        = N.relIndex T * ((T ⊓ N).relIndex N * Nat.card ↥(T ⊓ N)) := by ring
      _ = N.relIndex T * Nat.card N := by rw [e4]
      _ = Nat.card ↥(T ⊔ N) := e1
      _ = T.relIndex (T ⊔ N) * Nat.card T := e2.symm
      _ = T.relIndex (T ⊔ N) * (N.relIndex T * Nat.card ↥(T ⊓ N)) := by rw [e3]
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos ha ht) key

theorem isPGroup_of_le_sup [Finite G] {K R P : Subgroup G} (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hP : P ≤ K ⊔ R) (hPK : IsPGroup 2 ↥(K ⊓ P)) :
    IsPGroup 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKRN : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have hPN : P ≤ Subgroup.normalizer (K : Set G) := hP.trans hKRN
  have h1 : K.relIndex (P ⊔ K) = K.relIndex P := relIndex_sup_eq hPN
  have h2 : K.relIndex (R ⊔ K) = K.relIndex R := relIndex_sup_eq hRK
  have hle : P ⊔ K ≤ R ⊔ K := sup_le (hP.trans (sup_comm K R).le) le_sup_right
  have h3 := Subgroup.relIndex_mul_relIndex K (P ⊔ K) (R ⊔ K) le_sup_right hle
  obtain ⟨r, hr⟩ := hR.exists_card_eq
  have hdvd : K.relIndex P ∣ 2 ^ r := by
    rw [← h1, ← hr]
    refine (Dvd.intro _ h3).trans ?_
    rw [h2]
    exact Subgroup.relIndex_dvd_card K R
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  obtain ⟨j, hj⟩ := hPK.exists_card_eq
  refine IsPGroup.of_card (n := i + j) ?_
  rw [← Subgroup.relIndex_mul_card K P, hi, hj, pow_add]

theorem exists_mul_mem_centralizer [Finite G] {K T U : Subgroup G} (hodd : ¬ 2 ∣ T.relIndex K)
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU2 : ∀ u ∈ U, u * u = 1)
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) {z : G} (hzT : ∀ t ∈ T, t * z = z * t)
    (hδ : ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ U) :
    ∃ w ∈ U, ∀ k ∈ K, k * (w⁻¹ * z) = (w⁻¹ * z) * k := by
  classical
  let _ : CommGroup U :=
    { (inferInstance : Group U) with mul_comm := fun a b => Subtype.ext (hUc a a.2 b b.2) }
  set T' : Subgroup K := T.subgroupOf K with hT'def
  let δ : G → G := fun k => k * z * k⁻¹ * z⁻¹
  have hcoc : ∀ a b : G, δ (a * b) = a * δ b * a⁻¹ * δ a := fun a b => by
    simp only [δ]; group
  have hδT : ∀ t ∈ T, δ t = 1 := fun t ht => by
    simp only [δ]
    rw [hzT t ht]
    group
  have hδcos : ∀ (k : K) (t : T'), δ ((k * t : K) : G) = δ (k : G) := by
    intro k t
    rw [Subgroup.coe_mul, hcoc, hδT ((t : K) : G) t.2]
    group
  have : Fintype (K ⧸ T') := Fintype.ofFinite _
  let e : K ⧸ T' → U := fun q => ⟨δ (q.out : K), hδ _ q.out.2⟩
  have he : ∀ k : K, e (QuotientGroup.mk k) = ⟨δ (k : G), hδ _ k.2⟩ := by
    intro k
    apply Subtype.ext
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T' k
    change δ ((QuotientGroup.mk k : K ⧸ T').out : G) = δ (k : G)
    rw [ht, hδcos]
  set w₀ : U := ∏ q, e q with hw₀
  refine ⟨w₀, w₀.2, fun k hk => ?_⟩
  let ck : U →* U :=
    { toFun := fun u => ⟨k * u * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU hk) u).mp u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hck : ∀ u : U, ((ck u : U) : G) = k * u * k⁻¹ := fun u => rfl
  set d : U := ⟨δ k, hδ k hk⟩ with hd
  have hd2 : d * d = 1 := Subtype.ext (hU2 _ d.2)
  have hstep : ∀ q : K ⧸ T', ck (e q) = e ((⟨k, hk⟩ : K) • q) * d⁻¹ := by
    intro q
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAction.Quotient.smul_mk, he, he]
    apply Subtype.ext
    rw [hck, Subgroup.coe_mul, Subgroup.coe_inv]
    change k * δ q * k⁻¹ = δ (k * q) * (δ k)⁻¹
    rw [hcoc]
    group
  have hperm : ∏ q, e ((⟨k, hk⟩ : K) • q) = w₀ :=
    Fintype.prod_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ (fun _ => rfl)
  have hcard : Fintype.card (K ⧸ T') = T.relIndex K := by
    rw [Fintype.card_eq_nat_card]
    rfl
  have hodd' : Odd (Fintype.card (K ⧸ T')) := by
    rw [hcard]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have hdpow : d⁻¹ ^ Fintype.card (K ⧸ T') = d := by
    obtain ⟨m, hm⟩ := hodd'
    rw [hm, pow_succ, pow_mul, sq, ← mul_inv, hd2, inv_one, one_pow, one_mul]
    calc d⁻¹ = d⁻¹ * (d * d) := by rw [hd2, mul_one]
      _ = d := by group
  have hkw : ck w₀ = w₀ * d := by
    rw [hw₀, map_prod]
    simp_rw [hstep]
    rw [Finset.prod_mul_distrib, hperm, Finset.prod_const, Finset.card_univ, hdpow]
  have hkw' : k * (w₀ : G) * k⁻¹ = w₀ * δ k := by
    have := congrArg Subtype.val hkw
    rwa [hck, Subgroup.coe_mul] at this
  have hcomm : (w₀ : G) * δ k = δ k * w₀ := hUc _ w₀.2 _ (hδ k hk)
  have e1 : k * ((w₀ : G)⁻¹ * z) * k⁻¹ = (k * (w₀ : G) * k⁻¹)⁻¹ * (δ k * z) := by
    simp only [δ]; group
  have e2 : k * ((w₀ : G)⁻¹ * z) * k⁻¹ = (w₀ : G)⁻¹ * z := by
    calc k * ((w₀ : G)⁻¹ * z) * k⁻¹ = (k * (w₀ : G) * k⁻¹)⁻¹ * (δ k * z) := e1
      _ = ((w₀ : G) * δ k)⁻¹ * (δ k * z) := by rw [hkw']
      _ = (δ k * (w₀ : G))⁻¹ * (δ k * z) := by rw [hcomm]
      _ = (w₀ : G)⁻¹ * z := by group
  calc k * ((w₀ : G)⁻¹ * z) = k * ((w₀ : G)⁻¹ * z) * k⁻¹ * k := by group
    _ = ((w₀ : G)⁻¹ * z) * k := by rw [e2]

theorem pow_mul_comm_of_conj_eq {k w c : G} (hc : k * w * k⁻¹ = c * w) (hck : c * k = k * c)
    (hc2 : c * c = 1) {a m : ℕ} (hm : Odd m)
    (hN : orderOf k = 2 ^ a * m) : k ^ 2 ^ a * w = w * k ^ 2 ^ a := by
  have hkw : k * w = c * w * k := by
    calc k * w = k * w * k⁻¹ * k := by group
      _ = c * w * k := by rw [hc]
  have hpow : ∀ n : ℕ, k ^ n * w = c ^ n * w * k ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcn : c ^ n * k = k * c ^ n := ((Commute.pow_left hck n)).eq
      calc k ^ (n + 1) * w = k * (k ^ n * w) := by rw [pow_succ', mul_assoc]
        _ = k * (c ^ n * w * k ^ n) := by rw [ih]
        _ = (k * c ^ n) * w * k ^ n := by group
        _ = c ^ n * (k * w) * k ^ n := by rw [← hcn]; group
        _ = c ^ n * (c * w * k) * k ^ n := by rw [hkw]
        _ = c ^ (n + 1) * w * k ^ (n + 1) := by rw [pow_succ, pow_succ]; group
  have hcN : c ^ orderOf k = 1 := by
    have := hpow (orderOf k)
    rw [pow_orderOf_eq_one, mul_one, one_mul] at this
    calc c ^ orderOf k = c ^ orderOf k * w * w⁻¹ := by group
      _ = 1 := by rw [← this]; group
  have hc2' : c ^ 2 = 1 := by rw [sq]; exact hc2
  have hdvd2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2'
  have hdvdN : orderOf c ∣ 2 ^ a * m := hN ▸ orderOf_dvd_of_pow_eq_one hcN
  have hcop : Nat.Coprime (orderOf c) m :=
    Nat.Coprime.coprime_dvd_left hdvd2 (Nat.coprime_two_left.mpr hm)
  have hca : c ^ 2 ^ a = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvdN)
  rw [hpow, hca, one_mul]

theorem eq_zero_of_mulVec_eq_self {F : Type*} [Field F] (h2 : (2 : F) = 0)
    {g : Matrix.SpecialLinearGroup (Fin 2) F} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) {v : Fin 2 → F}
    (hv : (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : v = 0 := by
  by_contra hv0
  have hdet : ((g : Matrix (Fin 2) (Fin 2) F) - 1).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, hv, Matrix.one_mulVec, sub_self]
  have hdg : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet hdg
  simp at hdet
  have htr : (g : Matrix (Fin 2) (Fin 2) F) 0 0 + (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    linear_combination hdg - hdet + h2
  have hsq : g ^ 2 = 1 := by
    ext i j
    rw [sq, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (g : Matrix (Fin 2) (Fin 2) F) 0 0 * htr - hdg - h2
    · linear_combination (g : Matrix (Fin 2) (Fin 2) F) 0 1 * htr
    · linear_combination (g : Matrix (Fin 2) (Fin 2) F) 1 0 * htr
    · linear_combination (g : Matrix (Fin 2) (Fin 2) F) 1 1 * htr - hdg - h2
  apply hg1
  calc g = g ^ 3 * (g ^ 2)⁻¹ := by group
    _ = 1 := by rw [hg3, hsq]; group

end L15420

end CFSG.Quasithin.EmptyFaithfulMultiple
