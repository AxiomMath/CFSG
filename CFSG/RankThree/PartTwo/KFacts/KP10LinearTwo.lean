module

public import CFSG.RankThree.SubgroupLists.DicksonGL2
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP10

open Matrix Subgroup
open scoped commutatorElement MatrixGroups

section Complement

variable {G : Type*} [Group G] [Finite G]

theorem coprime_two_card_of_forall {X : Subgroup G} (h : ∀ x ∈ X, x ^ 2 = 1 → x = 1) :
    Nat.Coprime 2 (Nat.card X) := by
  rw [Nat.coprime_two_left]
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (even_iff_two_dvd.1 hodd)
  have h1 := h x x.2 (by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this)
  have : x = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem hasNormalPComplement_two_of_index_dvd_two {C : Subgroup G}
    (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) (hidx : C.index ∣ 2) :
    CFSG.HasNormalPComplement 2 G := by
  classical
  have hCn : C.Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h
  obtain ⟨k, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := C)).ne'
  let N : Subgroup G :=
    { carrier := {y | y ∈ C ∧ y ^ m = 1}
      mul_mem' := fun {a b} ha hb => ⟨C.mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hC a ha.1 b hb.1) m), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨C.one_mem, one_pow m⟩
      inv_mem' := fun {a} ha => ⟨C.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hNn : N.Normal := ⟨fun n hn g => ⟨hCn.conj_mem n hn.1 g, by
    rw [conj_pow, hn.2, mul_one, mul_inv_cancel]⟩⟩
  refine ⟨N, hNn, coprime_two_card_of_forall fun x hx hx2 => ?_, ?_⟩
  · have h1 : x ^ Nat.gcd 2 m = 1 := pow_gcd_eq_one.2 ⟨hx2, hx.2⟩
    rwa [show Nat.gcd 2 m = 1 from (Nat.coprime_two_left.2 hm), pow_one] at h1
  · intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨k + 1, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have hg2 : g ^ 2 ∈ C := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h | h
      · rw [Subgroup.index_eq_one] at h
        rw [h]
        trivial
      · exact Subgroup.sq_mem_of_index_two h g
    refine ⟨by rw [pow_succ', pow_mul]; exact C.pow_mem hg2 _, ?_⟩
    have hgc : (⟨g ^ 2, hg2⟩ : C) ^ Nat.card C = 1 := pow_card_eq_one'
    rw [hcard] at hgc
    have := congrArg Subtype.val hgc
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    rw [← this, ← pow_mul, ← pow_mul, pow_succ', mul_comm 2]
    ring_nf

omit [Finite G] in
theorem eq_one_of_sq_eq_one {X : Subgroup G} (hX : Nat.Coprime 2 (Nat.card X)) {y : G}
    (hy : y ∈ X) (h2 : y ^ 2 = 1) : y = 1 := by
  have h := orderOf_dvd_natCard (⟨y, hy⟩ : X)
  rw [← Subgroup.orderOf_coe] at h
  have h' : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h' hX) h)

theorem hasNormalPComplement_two_of_quotient {K : Subgroup G} [K.Normal]
    (hK : Nat.Coprime 2 (Nat.card K)) (h : CFSG.HasNormalPComplement 2 (G ⧸ K)) :
    CFSG.HasNormalPComplement 2 G := by
  obtain ⟨M, hMn, hM2, hMq⟩ := h
  refine ⟨M.comap (QuotientGroup.mk' K), hMn.comap _,
    coprime_two_card_of_forall fun x hx hx2 => ?_, ?_⟩
  · have hxK : QuotientGroup.mk' K x = 1 :=
      eq_one_of_sq_eq_one hM2 hx (by rw [← map_pow, hx2, map_one])
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxK
    exact eq_one_of_sq_eq_one hK hxK hx2
  · intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, hn⟩ := hMq (QuotientGroup.mk (QuotientGroup.mk g))
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hn ⊢
    rw [Subgroup.mem_comap, map_pow]
    exact hn

theorem hasNormalPComplement_two_of_commutator_le (X : Subgroup G) {K : Subgroup G}
    (hK : Nat.Coprime 2 (Nat.card K)) (hXK : ⁅X, X⁆ ≤ K) : CFSG.HasNormalPComplement 2 X := by
  classical
  set K₀ := K.subgroupOf X with hK₀
  have hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ K := fun x hx y hy =>
    hXK (Subgroup.commutator_mem_commutator hx hy)
  have hK₀n : K₀.Normal := ⟨fun k hk x => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    have h1 := hcomm x x.2 k k.2
    have h2 : ((x * k * x⁻¹ : X) : G) = (x * k * x⁻¹ * k⁻¹) * k := by
      simp [mul_assoc]
    rw [h2]
    exact K.mul_mem h1 hk⟩
  have hK₀2 : Nat.Coprime 2 (Nat.card K₀) := by
    refine Nat.Coprime.coprime_dvd_right ?_ hK
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  refine hasNormalPComplement_two_of_quotient hK₀2
    (hasNormalPComplement_two_of_index_dvd_two (C := ⊤) (fun a _ b _ => ?_) (by simp))
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  rw [Subgroup.mem_subgroupOf]
  have := hcomm b⁻¹ (X.inv_mem b.2) a⁻¹ (X.inv_mem a.2)
  simpa [mul_assoc] using this

omit [Finite G] in
theorem hasNormalPComplement_two_of_isPGroup (h : IsPGroup 2 G) : CFSG.HasNormalPComplement 2 G :=
  ⟨⊥, inferInstance, by rw [Subgroup.card_bot]; exact Nat.coprime_one_right 2,
    h.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥)⟩

end Complement

section GLTwo

variable {p : ℕ} [hp : Fact p.Prime]

open CFSG.RankThree.SubgroupLists (upperGL coe_upperGL upperGL_one_pow mem_statedSL_iff)

theorem entry_eq_zero_of_mem_normalizer {g : GL (Fin 2) (ZMod p)}
    (hg : g ∈ normalizer ((zpowers (upperGL (1 : ZMod p)) : Subgroup (GL (Fin 2) (ZMod p))) :
      Set (GL (Fin 2) (ZMod p)))) :
    (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := by
  have hu := (mem_normalizer_iff.1 hg (upperGL 1)).1 (mem_zpowers _)
  have hfin : IsOfFinOrder (upperGL (1 : ZMod p)) := isOfFinOrder_of_finite _
  obtain ⟨n, hn⟩ := (hfin.mem_powers_iff_mem_zpowers).2 hu
  simp only at hn
  rw [upperGL_one_pow] at hn
  have h := congrArg (fun A : GL (Fin 2) (ZMod p) => (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1)
    (show upperGL (n : ZMod p) * g = g * upperGL 1 by rw [hn]; group)
  simpa [Matrix.mul_apply, Fin.sum_univ_two, coe_upperGL] using h

theorem mulVec_e_zero {g : GL (Fin 2) (ZMod p)}
    (hg : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ ![1, 0] =
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 • ![1, 0] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hg]

theorem exists_upperGL_eq_commutatorElement {g h : GL (Fin 2) (ZMod p)}
    (hg : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0)
    (hh : (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0) :
    ∃ r : ZMod p, ⁅g, h⁆ = upperGL r := by
  have hdet : ∀ x : GL (Fin 2) (ZMod p), (x : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 →
      (x : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 ≠ 0 := by
    intro x hx h0
    apply ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero
    rw [Matrix.det_fin_two, hx, h0]
    ring
  have hinv : ∀ x : GL (Fin 2) (ZMod p), (x : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 →
      ((x⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ ![1, 0] =
        ((x : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0)⁻¹ • ![1, 0] := by
    intro x hx
    have h1 : (x : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ
        (((x : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0)⁻¹ • ![1, 0]) = ![1, 0] := by
      rw [Matrix.mulVec_smul, mulVec_e_zero hx, smul_smul, inv_mul_cancel₀ (hdet x hx), one_smul]
    conv_lhs => rw [← h1]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hc : ((⁅g, h⁆ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ ![1, 0] =
      ![1, 0] := by
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv h hh]
    simp only [Matrix.mulVec_smul, hinv g hg, mulVec_e_zero hh, mulVec_e_zero hg, smul_smul]
    have hgh := hdet g hg
    have hhh := hdet h hh
    rw [show ((h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0)⁻¹ *
        ((g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0)⁻¹ * (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 *
          (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 by field_simp, one_smul]
  have hc0 := congrFun hc 0
  have hc1 := congrFun hc 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hc0 hc1
  have hdc : ((⁅g, h⁆ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det ⁅g, h⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)
    have h2 : ((⁅g, h⁆ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).det =
        ((Matrix.GeneralLinearGroup.det ⁅g, h⁆ : (ZMod p)ˣ) : ZMod p) := rfl
    rw [h2, h1, Units.val_one]
  rw [Matrix.det_fin_two, hc0, hc1] at hdc
  refine ⟨((⁅g, h⁆ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1, Units.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_upperGL, hc0, hc1]
  linear_combination hdc

theorem orderOf_upperGL_one : orderOf (upperGL (1 : ZMod p)) = p := by
  refine orderOf_eq_prime ?_ ?_
  · rw [upperGL_one_pow, ZMod.natCast_self]
    exact Units.ext (by ext i j; fin_cases i <;> fin_cases j <;> simp [coe_upperGL])
  · intro h
    have := congrArg (fun A : GL (Fin 2) (ZMod p) => (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) h
    simp [coe_upperGL] at this

theorem commutator_le_zpowers_of_le_normalizer {H : Subgroup (GL (Fin 2) (ZMod p))}
    (hH : H ≤ normalizer ((zpowers (upperGL (1 : ZMod p)) : Subgroup (GL (Fin 2) (ZMod p))) :
      Set (GL (Fin 2) (ZMod p)))) :
    ⁅H, H⁆ ≤ zpowers (upperGL (1 : ZMod p)) := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  obtain ⟨r, hr⟩ := exists_upperGL_eq_commutatorElement (entry_eq_zero_of_mem_normalizer (hH hg))
    (entry_eq_zero_of_mem_normalizer (hH hh))
  rw [hr, ← ZMod.natCast_zmod_val r, ← upperGL_one_pow]
  exact Subgroup.pow_mem _ (mem_zpowers _) _

theorem commutator_le_of_normal_sylow {H : Subgroup (GL (Fin 2) (ZMod p))} (P : Sylow p H)
    (hPn : (P : Subgroup H).Normal) (hPc : Nat.card P = p) :
    ⁅H, H⁆ ≤ (P : Subgroup H).map H.subtype := by
  classical
  have : Nontrivial (P : Subgroup H) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hPc]
    exact hp.out.one_lt
  obtain ⟨⟨v, hvP⟩, hv1⟩ := exists_ne (1 : (P : Subgroup H))
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvp : v ^ p = 1 := by
    have h := pow_card_eq_one' (G := (P : Subgroup H)) (x := ⟨v, hvP⟩)
    rw [hPc] at h
    exact congrArg Subtype.val h
  have hPz : (P : Subgroup H) = zpowers v := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hvP) ?_).symm
    rw [Nat.card_zpowers, hPc, orderOf_eq_prime hvp hv1']
  set v₀ : GL (Fin 2) (ZMod p) := (v : GL (Fin 2) (ZMod p))
  have hv₀1 : v₀ ≠ 1 := fun h => hv1' (Subtype.ext h)
  have hv₀p : v₀ ^ p = 1 := congrArg Subtype.val hvp
  obtain ⟨g, hg⟩ := CFSG.RankThree.SubgroupLists.exists_conj_transvection v₀ hv₀p hv₀1
  have hconj : (MulAut.conj g⁻¹) v₀ = upperGL 1 := by
    rw [MulAut.conj_apply, inv_inv]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_upperGL, Matrix.mul_assoc, hg, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hP₀ : (P : Subgroup H).map H.subtype = zpowers v₀ := by
    rw [hPz, MonoidHom.map_zpowers]
    rfl
  have hHP : H ≤ normalizer ((zpowers v₀ : Subgroup (GL (Fin 2) (ZMod p))) :
      Set (GL (Fin 2) (ZMod p))) := by
    have h := le_normalizer_map (H := (P : Subgroup H)) H.subtype
    rw [normalizer_eq_top_iff.2 hPn, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hP₀] at h
    exact h
  set φ := (MulAut.conj g⁻¹).toMonoidHom
  have hH' : H.map φ ≤ normalizer ((zpowers (upperGL (1 : ZMod p)) :
      Subgroup (GL (Fin 2) (ZMod p))) : Set (GL (Fin 2) (ZMod p))) := by
    refine (Subgroup.map_mono hHP).trans ?_
    have h := le_normalizer_map (H := zpowers v₀) φ
    rwa [MonoidHom.map_zpowers, show φ v₀ = upperGL 1 from hconj] at h
  have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
    (commutator_le_zpowers_of_le_normalizer hH')
  have hid : (MulAut.conj g).toMonoidHom.comp φ = MonoidHom.id _ := by
    ext x : 1
    simp [φ, MulAut.conj_apply, mul_assoc]
  rw [Subgroup.map_commutator, Subgroup.map_map, hid, Subgroup.map_id,
    MonoidHom.map_zpowers] at h1
  have hv : (MulAut.conj g).toMonoidHom (upperGL 1) = v₀ := by
    rw [← hconj]
    simp [MulAut.conj_apply, mul_assoc]
  rw [hP₀, ← hv]
  exact h1

theorem hasNormalPComplement_two_of_normal_sylow (hp2 : p ≠ 2) {H : Subgroup (GL (Fin 2) (ZMod p))}
    (P : Sylow p H) (hPn : (P : Subgroup H).Normal) (hPc : Nat.card P = p) :
    CFSG.HasNormalPComplement 2 H := by
  refine hasNormalPComplement_two_of_commutator_le H ?_ (commutator_le_of_normal_sylow P hPn hPc)
  rw [Subgroup.card_map_of_injective H.subtype_injective, hPc]
  exact (Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2)

theorem pgl_tame_cases {k : Type*} [Field k] [Finite k] [CharP k p]
    (J : Subgroup PGL(Fin 2, k)) (hJ : ¬ p ∣ Nat.card J) :
    IsCyclic J ∨ (∃ z : ℕ, Nonempty (J ≃* DihedralGroup z)) ∨
      Nat.card J = 12 ∨ Nat.card J = 24 ∨ Nat.card J = 60 := by
  have := Fintype.ofFinite k
  let E := FiniteField.Extension k p 2
  have := Fintype.ofFinite E
  have hEcard : Nat.card E = Nat.card k ^ 2 := FiniteField.natCard_extension k p 2
  obtain ⟨f, -, hkcard⟩ := FiniteField.card k p
  have hEp : Nat.card E = p ^ (2 * (f : ℕ)) := by
    rw [hEcard, Nat.card_eq_fintype_card, hkcard, ← pow_mul, mul_comm]
  have hsq : ∀ x : k, IsSquare (algebraMap k E x) :=
    CFSG.LinearGroups.isSquare_algebraMap_of_card_eq_sq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hEcard])
  set ι := ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := E)
  set J₁ := J.map (CFSG.LinearGroups.pglExtend k E)
  have hJ₁ : J₁ ≤ ι.range := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.LinearGroups.pglExtend_mem_range_toPGL hsq x
  set H : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) E) := J₁.comap ι
  have hmap : H.map ι = J₁ := Subgroup.map_comap_eq_self hJ₁
  let eH : H ≃* J :=
    ((H.equivMapOfInjective ι ProjectiveSpecialLinearGroup.toPGL_injective).trans
      (MulEquiv.subgroupCongr hmap)).trans
      (J.equivMapOfInjective (CFSG.LinearGroups.pglExtend k E)
        CFSG.LinearGroups.pglExtend_injective).symm
  have hcard : Nat.card H = Nat.card J := Nat.card_congr eH.toEquiv
  have hHp : ¬ p ∣ Nat.card H := hcard ▸ hJ
  rcases CFSG.Glauberman.Dickson.huppert_II_8_24_dickson_case_no_p_part hEp H hHp with
    ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · exact Or.inl (isCyclic_of_surjective eH.toMonoidHom eH.surjective)
  · exact Or.inr (Or.inl ⟨z, ⟨eH.symm.trans e⟩⟩)
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [← hcard, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [← hcard, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [← hcard, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide

theorem ker_le_center (H : Subgroup (GL (Fin 2) (ZMod p))) :
    (ProjGenLinGroup.mk.subgroupMap H).ker ≤ center H := by
  intro x hx
  have hx' : ProjGenLinGroup.mk (x : GL (Fin 2) (ZMod p)) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  have hc : (x : GL (Fin 2) (ZMod p)) ∈ center (GL (Fin 2) (ZMod p)) :=
    (QuotientGroup.eq_one_iff _).1 hx'
  exact Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 hc y)

theorem exists_comm_of_not_dvd (H : Subgroup (GL (Fin 2) (ZMod p))) (hpH : ¬ p ∣ Nat.card H) :
    (∃ C : Subgroup H, (∀ a ∈ C, ∀ b ∈ C, a * b = b * a) ∧ C.index ∣ 2) ∨
      Nat.card (H.map ProjGenLinGroup.mk) = 12 ∨ Nat.card (H.map ProjGenLinGroup.mk) = 24 ∨
        Nat.card (H.map ProjGenLinGroup.mk) = 60 := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin 2) (ZMod p)) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  set π := ProjGenLinGroup.mk.subgroupMap H
  have hπ : Function.Surjective π := ProjGenLinGroup.mk.subgroupMap_surjective H
  have hJ : ¬ p ∣ Nat.card (H.map ProjGenLinGroup.mk) := fun h =>
    hpH (h.trans (Subgroup.card_dvd_of_surjective (f := π) hπ))
  rcases pgl_tame_cases (k := ZMod p) _ hJ with hcyc | ⟨z, ⟨e⟩⟩ | h
  · have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center π (ker_le_center H)
    exact Or.inl ⟨⊤, fun a _ b _ => this.is_comm.comm a b, by simp⟩
  · refine Or.inl ⟨((zpowers (DihedralGroup.r 1 : DihedralGroup z)).comap e.toMonoidHom).comap π,
      fun a ha b hb => ?_, ?_⟩
    ·
      set C := ((zpowers (DihedralGroup.r 1 : DihedralGroup z)).comap e.toMonoidHom).comap π
      let ψ : C →* zpowers (DihedralGroup.r 1 : DihedralGroup z) :=
        ((e.toMonoidHom.comp π).comp C.subtype).codRestrict _ fun c => c.2
      have hψ : ψ.ker ≤ center C := by
        intro c hc
        have h1 : e (π c) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hc)
        have h2 : π c = 1 := by simpa using h1
        have h3 : (c : H) ∈ center H := ker_le_center H (MonoidHom.mem_ker.2 h2)
        exact Subgroup.mem_center_iff.2 fun y =>
          Subtype.ext (Subgroup.mem_center_iff.1 h3 (y : H))
      have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center ψ hψ
      exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rw [Subgroup.index_comap_of_surjective _ hπ,
        Subgroup.index_comap_of_surjective _ e.surjective]
      have hz : z ≠ 0 := by
        rintro rfl
        have h1 := Nat.card_congr e.toEquiv
        rw [DihedralGroup.nat_card, mul_zero] at h1
        exact Nat.card_pos.ne' h1
      have : NeZero z := ⟨hz⟩
      have h := (zpowers (DihedralGroup.r 1 : DihedralGroup z)).card_mul_index
      rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h
      rw [show (zpowers (DihedralGroup.r 1 : DihedralGroup z)).index = 2 by
        have := Nat.pos_of_ne_zero hz
        nlinarith]
  · exact Or.inr h

theorem det_orderThree {R : Type*} [CommRing R] :
    (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) R).det = 1 := by
  simp [Matrix.det_fin_two]

theorem orderThree_pow_three {R : Type*} [CommRing R] :
    (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) R) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def orderThreeGL : GL (Fin 2) (ZMod p) :=
  Matrix.SpecialLinearGroup.toGL ⟨!![0, -1; 1, -1], det_orderThree⟩

theorem coe_orderThreeGL :
    (orderThreeGL : GL (Fin 2) (ZMod p)) = (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) (ZMod p)) :=
  rfl

theorem orderThreeGL_pow_three : (orderThreeGL : GL (Fin 2) (ZMod p)) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, coe_orderThreeGL]
  exact orderThree_pow_three

theorem orderThreeGL_ne_one : (orderThreeGL : GL (Fin 2) (ZMod p)) ≠ 1 := by
  intro h
  have := congrArg (fun A : GL (Fin 2) (ZMod p) => (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  simp [coe_orderThreeGL] at this

theorem three_dvd_card_of_statedSL_le {H : Subgroup (GL (Fin 2) (ZMod p))}
    (h : CFSG.Assembly.LowTwoRank.StatedSL 2 (ZMod p) ≤ H) : 3 ∣ Nat.card H := by
  have hmem : (orderThreeGL : GL (Fin 2) (ZMod p)) ∈ H := h ((mem_statedSL_iff _).2 (by
    rw [coe_orderThreeGL]
    exact det_orderThree))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf (orderThreeGL : GL (Fin 2) (ZMod p)) = 3 :=
    orderOf_eq_prime orderThreeGL_pow_three orderThreeGL_ne_one
  rw [← ho]
  exact Subgroup.orderOf_dvd_natCard H hmem

theorem hasNormalPComplement_two_of_not_three_dvd (H : Subgroup (GL (Fin 2) (ZMod p)))
    (h3 : ¬ 3 ∣ Nat.card H) : CFSG.HasNormalPComplement 2 H := by
  by_cases hpH : p ∣ Nat.card H
  · by_cases hp2 : p = 2
    · subst hp2
      have h6 : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
        rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
        rfl
      have hdvd : Nat.card H ∣ 2 * 3 := by
        rw [show 2 * 3 = 6 from rfl, ← h6]
        exact Subgroup.card_subgroup_dvd_card H
      have h2 : Nat.card H ∣ 2 := Nat.Coprime.dvd_of_dvd_mul_right
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)) hdvd
      refine hasNormalPComplement_two_of_isPGroup ?_
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
    · rcases CFSG.RankThree.SubgroupLists.dickson_gl_two H hpH with ⟨P, hPn, hPc⟩ | hSL
      · exact hasNormalPComplement_two_of_normal_sylow hp2 P hPn hPc
      · exact absurd (three_dvd_card_of_statedSL_le hSL) h3
  · rcases exists_comm_of_not_dvd H hpH with ⟨C, hC, hidx⟩ | hcard
    · exact hasNormalPComplement_two_of_index_dvd_two hC hidx
    · exfalso
      apply h3
      have hdvd : Nat.card (H.map ProjGenLinGroup.mk) ∣ Nat.card H :=
        Subgroup.card_dvd_of_surjective (f := ProjGenLinGroup.mk.subgroupMap H)
          (ProjGenLinGroup.mk.subgroupMap_surjective H)
      rcases hcard with h | h | h <;> rw [h] at hdvd <;> exact (by norm_num : 3 ∣ _).trans hdvd

end GLTwo

end CFSG.RankThree.PartTwo.KFacts.KP10
