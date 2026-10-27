module

public import CFSG.OddTranspositions.O4PairSTwisted
public import CFSG.OddTranspositions.O4PairCommutingTransport

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter CFSG.PSL2Table

theorem psl2FieldAut_eq_one_or_frob25t (τ : F25t ≃+* F25t) : τ = 1 ∨ τ = frob25t := by
  have hτ : τ ∈ Subgroup.zpowers frob25t := by
    rw [zpowers_frob25t_eq_top]
    exact Subgroup.mem_top τ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hτ
  have h2 : frob25t ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
    exact frob25t_mul_self
  have hred := zpow_eq_zpow_emod (x := frob25t) k h2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← hk, hred, h]
    simp
  · right
    rw [← hk, hred, h]
    simp

theorem conj_inr_frob25t (p : PSL2 F25t) (τ : F25t ≃+* F25t) :
    (SemidirectProduct.mk p τ : PSigmaL2t) * SemidirectProduct.inr frob25t *
        (SemidirectProduct.mk p τ : PSigmaL2t)⁻¹ =
      (SemidirectProduct.mk (p * psl2FieldAut F25t frob25t p⁻¹) frob25t : PSigmaL2t) := by
  have hff : (SemidirectProduct.inr frob25t : PSigmaL2t) *
      SemidirectProduct.inr frob25t = 1 := by
    rw [← map_mul, frob25t_mul_self, map_one]
  have hinr_inv : (SemidirectProduct.inr frob25t : PSigmaL2t)⁻¹ =
      SemidirectProduct.inr frob25t :=
    inv_eq_of_mul_eq_one_right hff
  have hsinr : (SemidirectProduct.inr (frob25t⁻¹) : PSigmaL2t) =
      SemidirectProduct.inr frob25t := by
    rw [map_inv, hinr_inv]
  have hinvτ : (SemidirectProduct.inr τ : PSigmaL2t) * SemidirectProduct.inr frob25t *
      (SemidirectProduct.inr τ)⁻¹ = SemidirectProduct.inr frob25t := by
    rcases psl2FieldAut_eq_one_or_frob25t τ with hτ | hτ
    · rw [hτ]
      simp
    · rw [hτ]
      group
  have hkey : (SemidirectProduct.inr frob25t : PSigmaL2t) *
      (SemidirectProduct.inl p : PSigmaL2t)⁻¹ =
      (SemidirectProduct.inl (psl2FieldAut F25t frob25t p⁻¹) : PSigmaL2t) *
        SemidirectProduct.inr frob25t := by
    rw [← map_inv]
    have h := SemidirectProduct.inl_aut (φ := psl2FieldAut F25t) frob25t p⁻¹
    rw [h, hsinr, mul_assoc, hff, mul_one]
  have hstep : (SemidirectProduct.inl p : PSigmaL2t) * SemidirectProduct.inr frob25t *
      (SemidirectProduct.inl p : PSigmaL2t)⁻¹ =
      (SemidirectProduct.inl (p * psl2FieldAut F25t frob25t p⁻¹) : PSigmaL2t) *
        SemidirectProduct.inr frob25t := by
    rw [mul_assoc, hkey, ← mul_assoc, ← map_mul]
  have hmk : (SemidirectProduct.mk p τ : PSigmaL2t) =
      SemidirectProduct.inl p * SemidirectProduct.inr τ :=
    SemidirectProduct.mk_eq_inl_mul_inr τ p
  have htarget : (SemidirectProduct.mk (p * psl2FieldAut F25t frob25t p⁻¹) frob25t : PSigmaL2t) =
      SemidirectProduct.inl (p * psl2FieldAut F25t frob25t p⁻¹) *
        SemidirectProduct.inr frob25t :=
    SemidirectProduct.mk_eq_inl_mul_inr frob25t (p * psl2FieldAut F25t frob25t p⁻¹)
  rw [hmk, htarget]
  calc (SemidirectProduct.inl p * SemidirectProduct.inr τ : PSigmaL2t) *
        SemidirectProduct.inr frob25t *
          (SemidirectProduct.inl p * SemidirectProduct.inr τ : PSigmaL2t)⁻¹
      = (SemidirectProduct.inl p * SemidirectProduct.inr τ : PSigmaL2t) *
          SemidirectProduct.inr frob25t *
            ((SemidirectProduct.inr τ)⁻¹ * (SemidirectProduct.inl p)⁻¹) := by
        rw [mul_inv_rev]
    _ = SemidirectProduct.inl p *
          (SemidirectProduct.inr τ * SemidirectProduct.inr frob25t *
            (SemidirectProduct.inr τ)⁻¹) * (SemidirectProduct.inl p)⁻¹ := by
        group
    _ = SemidirectProduct.inl p * SemidirectProduct.inr frob25t *
          (SemidirectProduct.inl p)⁻¹ := by
        rw [hinvτ]
    _ = SemidirectProduct.inl (p * psl2FieldAut F25t frob25t p⁻¹) *
          SemidirectProduct.inr frob25t := hstep

theorem mem_class65t_iff_left_right (x : PSigmaL2t) :
    x ∈ class65t ↔ x.left ∈ St ∧ x.right = frob25t := by
  have hmk : ∀ P : Matrix.SpecialLinearGroup (Fin 2) F25t,
      psl2FieldAut F25t frob25t (CFSG.PSL2Table.mk P) =
        CFSG.PSL2Table.mk (Matrix.SpecialLinearGroup.map frob25t.toRingHom P) := by
    intro P
    show psl2RingEquiv frob25t
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F25t)) P) = _
    rw [CFSG.GorensteinWalter.psl2RingEquiv_mk]
    rfl
  rcases x with ⟨q, σ⟩
  change (⟨q, σ⟩ ∈ class65t ↔ q ∈ St ∧ σ = frob25t)
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := isConj_iff.mp ((mem_class65t_iff (⟨q, σ⟩ : PSigmaL2t)).mp hx)
    rcases g with ⟨p, τ⟩
    rw [conj_inr_frob25t] at hg
    have hq : q = p * psl2FieldAut F25t frob25t p⁻¹ :=
      (congrArg SemidirectProduct.left hg).symm
    have hσ : σ = frob25t := (congrArg SemidirectProduct.right hg).symm
    refine ⟨?_, hσ⟩
    rw [hq]
    obtain ⟨P, rfl⟩ := CFSG.PSL2Table.mk_surjective p
    exact mem_St_iff.mpr ⟨P, by rw [map_inv, ← hmk]⟩
  · rintro ⟨hq, hσ⟩
    rw [hσ]
    refine (mem_class65t_iff (⟨q, frob25t⟩ : PSigmaL2t)).mpr ?_
    obtain ⟨P, hP⟩ := mem_St_iff.mp hq
    refine isConj_iff.mpr ⟨(SemidirectProduct.mk (CFSG.PSL2Table.mk P) 1 : PSigmaL2t), ?_⟩
    have hqP : CFSG.PSL2Table.mk P * psl2FieldAut F25t frob25t (CFSG.PSL2Table.mk P)⁻¹ = q := by
      rw [map_inv, hmk]
      exact hP.symm
    rw [conj_inr_frob25t, hqP]

theorem mem_commuting_class65t_iff (x : PSigmaL2t) :
    (x ∈ class65t ∧ Commute x (SemidirectProduct.inr frob25t)) ↔
      x.left ∈ St ∧ x.right = frob25t ∧ x.left * x.left = 1 := by
  rcases x with ⟨q, σ⟩
  change ((⟨q, σ⟩ : PSigmaL2t) ∈ class65t ∧
      Commute (⟨q, σ⟩ : PSigmaL2t) (SemidirectProduct.inr frob25t)) ↔
    q ∈ St ∧ σ = frob25t ∧ q * q = 1
  rw [mem_class65t_iff_left_right]
  constructor
  · rintro ⟨⟨hq, hσ⟩, hcomm⟩
    have hcent : (⟨q, σ⟩ : PSigmaL2t) ∈
        Subgroup.centralizer ({SemidirectProduct.inr frob25t} : Set PSigmaL2t) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hfix : q = psl2FieldAut F25t frob25t q :=
      (mem_centralizer_inr_frob25t_iff q σ).mp hcent
    exact ⟨hq, hσ, (St_fixed_iff_sq hq).mp hfix.symm⟩
  · rintro ⟨hq, hσ, hsq⟩
    rw [hσ]
    refine ⟨⟨hq, rfl⟩, ?_⟩
    have hfix : q = psl2FieldAut F25t frob25t q :=
      ((St_fixed_iff_sq hq).mpr hsq).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp
      ((mem_centralizer_inr_frob25t_iff q frob25t).mpr hfix)

noncomputable def commutingClass65tEquiv :
    {x : PSigmaL2t // x ∈ class65t ∧ Commute x (SemidirectProduct.inr frob25t)} ≃
      {q : PSL2 F25t // q ∈ St ∧ q * q = 1} where
  toFun x := ⟨x.1.left, by
    have h := (mem_commuting_class65t_iff x.1).mp x.2
    exact ⟨h.1, h.2.2⟩⟩
  invFun q := ⟨SemidirectProduct.mk q.1 frob25t, by
    exact (mem_commuting_class65t_iff _).mpr ⟨q.2.1, rfl, q.2.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    have hx := (mem_class65t_iff_left_right x.1).mp x.2.1
    apply SemidirectProduct.ext
    · rfl
    · exact hx.2.symm
  right_inv q := by
    apply Subtype.ext
    rfl

theorem card_comm_class65t :
    Nat.card {x : PSigmaL2t // x ∈ class65t ∧ Commute x (SemidirectProduct.inr frob25t)} = 11 :=
  (Nat.card_congr commutingClass65tEquiv).trans card_St_involutions

theorem card_comm_class65 : ∀ u ∈ class65,
    Nat.card {d : PSigmaL225 // d ∈ class65 ∧ Commute d u} = 11 :=
  card_comm_class65_of_class65t card_comm_class65t

theorem commuting_class65t_eq :
    {x : PSigmaL2t | x ∈ class65t ∧ Commute x (SemidirectProduct.inr frob25t)} =
      insert (SemidirectProduct.inr frob25t)
        (Set.range (fun i : Fin 10 => SemidirectProduct.mk (x i) frob25t)) := by
  have hiff : ∀ q : PSL2 F25t, (q ∈ St ∧ q * q = 1) ↔
      q ∈ insert (1 : PSL2 F25t) (Set.range x) := by
    intro q
    rw [← St_involutions_eq]
    rfl
  ext y
  change (y ∈ class65t ∧ Commute y (SemidirectProduct.inr frob25t)) ↔
    y ∈ insert (SemidirectProduct.inr frob25t)
      (Set.range (fun i : Fin 10 => SemidirectProduct.mk (x i) frob25t))
  rw [mem_commuting_class65t_iff]
  constructor
  · rintro ⟨hq, hσ, hsq⟩
    rcases (hiff y.left).mp ⟨hq, hsq⟩ with h1 | ⟨i, hi⟩
    · left
      rw [← SemidirectProduct.inl_left_mul_inr_right y, h1, hσ]
      simp
    · right
      refine ⟨i, ?_⟩
      change SemidirectProduct.mk (x i) frob25t = y
      rw [← SemidirectProduct.inl_left_mul_inr_right y, ← hi, hσ]
      exact SemidirectProduct.mk_eq_inl_mul_inr frob25t (x i)
  · rintro (h | ⟨i, h⟩)
    · rw [h]
      have h1 := (hiff 1).mpr (Or.inl rfl)
      exact ⟨by simpa using h1.1, by simp, by simp⟩
    · have h' : y = SemidirectProduct.mk (x i) frob25t := h.symm
      rw [h']
      have h1 := (hiff (x i)).mpr (Or.inr ⟨i, rfl⟩)
      exact ⟨by simpa using h1.1, by simp, by simpa using h1.2⟩

end CFSG.OddTranspositions.QZ
