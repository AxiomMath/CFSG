module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2A6
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover

public section

namespace CFSG.Quasithin.H13

namespace S126T2

open CFSG.Open Equiv

section SL2

variable {K : Type*} [Field K]

theorem trace_eq_neg_one_of_pow_three {x : Matrix.SpecialLinearGroup (Fin 2) K} (h : x ^ 3 = 1)
    (hx : x ≠ 1) : Matrix.trace (x : Matrix (Fin 2) (Fin 2) K) = -1 := by
  set M := (x : Matrix (Fin 2) (Fin 2) K) with hM
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact x.2
  have h3 : M ^ 3 = 1 := by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K)) h
    simpa using this
  rw [Matrix.eta_fin_two M, pow_succ, pow_succ, pow_one, Matrix.mul_fin_two, Matrix.mul_fin_two,
    Matrix.one_fin_two] at h3
  have e00 := congrFun (congrFun h3 0) 0
  have e01 := congrFun (congrFun h3 0) 1
  have e10 := congrFun (congrFun h3 1) 0
  have e11 := congrFun (congrFun h3 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10 e11
  rw [Matrix.trace_fin_two]
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  have f00 : ((a + d) ^ 2 - 1) * a = a + d + 1 := by linear_combination e00 + (2 * a + d) * hdet
  have f01 : ((a + d) ^ 2 - 1) * b = 0 := by linear_combination e01 + b * hdet
  have f10 : ((a + d) ^ 2 - 1) * c = 0 := by linear_combination e10 + c * hdet
  have f11 : ((a + d) ^ 2 - 1) * d = a + d + 1 := by linear_combination e11 + (a + 2 * d) * hdet
  by_contra hne
  have ht1 : a + d + 1 ≠ 0 := fun h0 => hne (by linear_combination h0)
  have ha : (a + d - 1) * a = 1 := by
    apply mul_left_cancel₀ ht1; linear_combination f00
  have hd : (a + d - 1) * d = 1 := by
    apply mul_left_cancel₀ ht1; linear_combination f11
  have htm : a + d - 1 ≠ 0 := fun h0 => by rw [h0, zero_mul] at ha; exact zero_ne_one ha
  have hsq : (a + d) ^ 2 - 1 ≠ 0 := by
    rw [show (a + d) ^ 2 - 1 = (a + d + 1) * (a + d - 1) by ring]; exact mul_ne_zero ht1 htm
  have hb : b = 0 := (mul_eq_zero.1 f01).resolve_left hsq
  have hc : c = 0 := (mul_eq_zero.1 f10).resolve_left hsq
  have had : a = d := by
    apply mul_left_cancel₀ htm; rw [ha, hd]
  have ha1 : a = 1 := by
    have h1 : a * a = 1 := by rw [hb, hc, ← had] at hdet; linear_combination hdet
    have h2 : (a + a - 1) * a = 1 := by rw [← had] at ha; exact ha
    linear_combination 2 * h1 - h2
  apply hx
  ext i j
  fin_cases i <;> fin_cases j
  · show a = 1; exact ha1
  · show b = 0; exact hb
  · show c = 0; exact hc
  · show d = 1; rw [← had]; exact ha1

theorem trace_mul_add_trace_mul_inv (x y : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.trace ((x * y : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) +
      Matrix.trace ((x * y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
      Matrix.trace (x : Matrix (Fin 2) (Fin 2) K) *
        Matrix.trace (y : Matrix (Fin 2) (Fin 2) K) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  rw [Matrix.adjugate_fin_two, Matrix.eta_fin_two (x : Matrix (Fin 2) (Fin 2) K),
    Matrix.eta_fin_two (y : Matrix (Fin 2) (Fin 2) K)]
  simp only [Matrix.mul_fin_two, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem false_of_commute_pow_three (h3 : (3 : K) ≠ 0) {x y : Matrix.SpecialLinearGroup (Fin 2) K}
    (hxy : x * y = y * x) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hx : x ≠ 1) (hy : y ≠ 1)
    (hyx : y ≠ x) (hyx' : y ≠ x⁻¹) : False := by
  have hc : Commute x y := hxy
  have h1 : (x * y) ^ 3 = 1 := by rw [hc.mul_pow, hx3, hy3, one_mul]
  have h2 : (x * y⁻¹) ^ 3 = 1 := by
    rw [(hc.inv_right).mul_pow, hx3, inv_pow, hy3, inv_one, one_mul]
  have h1' : x * y ≠ 1 := fun e => hyx' (eq_inv_of_mul_eq_one_right e)
  have h2' : x * y⁻¹ ≠ 1 := fun e => hyx (mul_inv_eq_one.1 e).symm
  have key := trace_mul_add_trace_mul_inv x y
  rw [trace_eq_neg_one_of_pow_three h1 h1', trace_eq_neg_one_of_pow_three h2 h2',
    trace_eq_neg_one_of_pow_three hx3 hx, trace_eq_neg_one_of_pow_three hy3 hy] at key
  exact h3 (by linear_combination -key)

theorem false_of_elemAbelian_nine (h3 : (3 : K) ≠ 0) {Y : Type*} [Group Y] {A : Subgroup Y}
    (hA : IsElemAbelian 3 A) (hcA : Nat.card A = 9) (φ : ↥A →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hφ : ∀ a, φ a = 1 → a = 1) : False := by
  classical
  have : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hcA]; norm_num)
  have : Fintype ↥A := Fintype.ofFinite _
  have hcomm : ∀ a b : ↥A, a * b = b * a := fun a b => hA.1.is_comm.comm a b
  have hpow : ∀ a : ↥A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hA.2 _ a.2)
  have hcard : (Finset.univ : Finset ↥A).card = 9 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcA]
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1} : Finset ↥A)) (t := Finset.univ) (by rw [hcard, Finset.card_singleton]; norm_num)
  rw [Finset.mem_singleton] at hx
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, x, x⁻¹} : Finset ↥A)) (t := Finset.univ)
    (lt_of_le_of_lt Finset.card_le_three (by rw [hcard]; norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨hy1, hyx, hyx'⟩ := hy
  refine false_of_commute_pow_three h3 (x := φ x) (y := φ y) (by rw [← map_mul, hcomm, map_mul])
    (by rw [← map_pow, hpow, map_one]) (by rw [← map_pow, hpow, map_one])
    (fun h => hx (hφ x h)) (fun h => hy1 (hφ y h)) (fun h => hyx ?_) (fun h => hyx' ?_)
  · have h1 : φ (y * x⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    exact mul_inv_eq_one.1 (hφ _ h1)
  · have h1 : φ (y * x) = 1 := by rw [map_mul, h, inv_mul_cancel]
    exact eq_inv_of_mul_eq_one_left (hφ _ h1)

end SL2

theorem isSimpleGroup_A6s : IsSimpleGroup ↥A6s := by
  have hinj : Function.Injective (Perm.ofSubtype : Perm ↥six →* Perm (Fin 8)) :=
    Equiv.Perm.ofSubtype_injective
  have : IsSimpleGroup ↥(alternatingGroup ↥six) :=
    alternatingGroup.isSimpleGroup (by rw [card_six]; norm_num)
  have : Nontrivial ↥A6s :=
    ⟨⟨⟨cy 2 3 4, cy_mem (by decide) (by decide) (by decide) (by decide) (by decide)⟩, 1,
      fun h => cyc_three.2 (congrArg Subtype.val h)⟩⟩
  exact IsSimpleGroup.isSimpleGroup_of_surjective
    (Subgroup.equivMapOfInjective _ _ hinj).toMonoidHom
    (Subgroup.equivMapOfInjective _ _ hinj).surjective

theorem two_le_pRank_A6s : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥A6s) := by
  classical
  have hinj : Function.Injective (Perm.ofSubtype : Perm ↥six →* Perm (Fin 8)) :=
    Equiv.Perm.ofSubtype_injective
  have hcard : Fintype.card ↥six = Fintype.card (Fin 6) := by
    rw [← Nat.card_eq_fintype_card, card_six, Fintype.card_fin]
  let e₁ : ↥(alternatingGroup ↥six) ≃* ↥A6s := Subgroup.equivMapOfInjective _ _ hinj
  let e₂ : ↥(alternatingGroup ↥six) ≃* ↥(alternatingGroup (Fin 6)) :=
    Equiv.altCongrHom (Fintype.equivOfCardEq hcard)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (e₂.symm.trans e₁)]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top
    (CFSG.SectionRank.isElemAbelian_sylowThreeAlt (n := 6) le_rfl)
    (CFSG.SectionRank.card_sylowThreeAlt (n := 6) le_rfl)

variable {G : Type} [Group G] [Finite G]

theorem coprime_card_sSup {p : ℕ} [Fact p.Prime] {𝒮 : Set (Subgroup G)}
    (hN : ∀ K ∈ 𝒮, sSup 𝒮 ≤ Subgroup.normalizer (K : Set G))
    (hc : ∀ K ∈ 𝒮, Nat.Coprime p (Nat.card K)) : Nat.Coprime p (Nat.card ↥(sSup 𝒮)) := by
  set P := sSup 𝒮 with hP
  have hle : ∀ K ∈ 𝒮, K ≤ (CFSG.pPrimeCore p ↥P).map P.subtype := by
    intro K hK
    have hKP : K ≤ P := le_sSup hK
    have hn : (K.subgroupOf P).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).2 (hN K hK)
    have hcK : Nat.Coprime p (Nat.card ↥(K.subgroupOf P)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv]
      exact hc K hK
    have h1 : K.subgroupOf P ≤ CFSG.pPrimeCore p ↥P := le_sSup ⟨hn, hcK⟩
    calc K = (K.subgroupOf P).map P.subtype := (Subgroup.map_subgroupOf_eq_of_le hKP).symm
      _ ≤ _ := Subgroup.map_mono h1
  have htop : CFSG.pPrimeCore p ↥P = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := (sSup_le hle : P ≤ _) x.2
    rwa [show y = x from Subtype.ext hyx] at hy
  have := CFSG.pPrimeCore_coprime_card (p := p) (G := ↥P)
  rwa [htop, Subgroup.card_top] at this

omit [Finite G] in
theorem mem_of_pow_three {K P' : Subgroup G} (hn : P' ≤ Subgroup.normalizer (K : Set G))
    (hc : Nat.Coprime 3 (Nat.card P')) {x : G} (hx : x ∈ K ⊔ P') {k : ℕ} (hk : x ^ 3 ^ k = 1) :
    x ∈ K := by
  set W := K ⊔ P' with hW
  have hKW : K ≤ W := le_sup_left
  have hPW : P' ≤ W := le_sup_right
  have hWN : W ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hn
  have : (K.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKW).2 hWN
  set π := QuotientGroup.mk' (K.subgroupOf W) with hπ
  set I := (P'.subgroupOf W).map π with hI
  have hall : W ≤ (I.comap π).map W.subtype := by
    refine sup_le (fun y hy => ⟨⟨y, hKW hy⟩, ?_, rfl⟩) (fun y hy => ⟨⟨y, hPW hy⟩, ?_, rfl⟩)
    · show π ⟨y, hKW hy⟩ ∈ I
      rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 (show _ ∈ K.subgroupOf W
        from hy)]
      exact I.one_mem
    · exact ⟨⟨y, hPW hy⟩, hy, rfl⟩
  obtain ⟨z, hz, hzx⟩ := hall hx
  have hz' : z = ⟨x, hx⟩ := Subtype.ext hzx
  rw [hz'] at hz
  have hcI : Nat.Coprime 3 (Nat.card I) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (H := P'.subgroupOf W) π) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPW).toEquiv]
    exact hc
  have hd1 : orderOf (π ⟨x, hx⟩) ∣ Nat.card I := Subgroup.orderOf_dvd_natCard I hz
  have hd2 : orderOf (π ⟨x, hx⟩) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥W) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have h1 : orderOf (π ⟨x, hx⟩) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd2 (Nat.Coprime.pow_left k hcI)) hd1
  rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end S126T2

end CFSG.Quasithin.H13
