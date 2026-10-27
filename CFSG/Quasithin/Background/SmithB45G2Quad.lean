module

public import CFSG.Quasithin.Background.SmithB42G2FRank

public section

namespace CFSG.Quasithin.B45G2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2Ten
  CFSG.Quasithin.B42G2F Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)
open scoped Kronecker

variable {F : Type} [Field F] [CharP F 2]

theorem exists_conj_stab [Finite F] {Γ : Subgroup ↥(cayleyGroup F)}
    (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1) (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) :
    ∃ g : ↥(cayleyGroup F), Γ.map (MulAut.conj g⁻¹).toMonoidHom ≤ stabV0 F ∧
      Γ.map (MulAut.conj g⁻¹).toMonoidHom ⊓ pCoreOf 2 (stabV0 F) ≤ A1 F := by
  have hconjc : ∀ x : ↥(cayleyGroup F), ∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom,
      ∀ δ ∈ Γ.map (MulAut.conj x).toMonoidHom, γ * δ = δ * γ := by
    rintro x _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    change x * g * x⁻¹ * (x * h * x⁻¹) = x * h * x⁻¹ * (x * g * x⁻¹)
    rw [show x * g * x⁻¹ * (x * h * x⁻¹) = x * (g * h) * x⁻¹ by group, hΓc g hg h hh]
    group
  by_cases hA : ∃ r ∈ Γ, ∃ x, qr r x ≠ 0
  · obtain ⟨r, hrΓ, x₀, hx₀⟩ := hA
    obtain ⟨p, hp⟩ := exists_qr_eq_sq (hΓ1 r hrΓ)
    have hp0 : p ≠ 0 := by
      rintro rfl
      apply hx₀
      rw [hp]
      simp [polarQ]
    obtain ⟨g, hg⟩ := exists_g2Act_eu_eq hp0
    obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = Γ.map (MulAut.conj g⁻¹).toMonoidHom := ⟨_, rfl⟩
    have hΓ'c : ∀ γ ∈ Γ', ∀ δ ∈ Γ', γ * δ = δ * γ := hΓ' ▸ hconjc g⁻¹
    have hr' : g⁻¹ * r * g ∈ Γ' := by
      have h1 := hΓ' ▸ conj_apply_mem_map g⁻¹ hrΓ
      rwa [inv_inv] at h1
    have hqr' : ∀ x, qr (g⁻¹ * r * g) x = x (.inr 0) * x (.inr 0) := by
      intro x
      have h1 := qr_conj g⁻¹ r (g2Act g x)
      rw [inv_inv, g2Act_inv_apply] at h1
      rw [h1, hp, ← polarQ_g2Act g⁻¹, g2Act_inv_apply, ← hg, g2Act_inv_apply, polarQ_eu0]
    have hr2 : g⁻¹ * r * g * (g⁻¹ * r * g) = 1 := by
      rw [show g⁻¹ * r * g * (g⁻¹ * r * g) = g⁻¹ * (r * r) * g by group, hΓ1 r hrΓ]
      group
    obtain ⟨a, b, hab⟩ := eq_kerElt_of_qr hr2 hqr'
    have hS : Γ' ≤ stabV0 F := fun s hs =>
      fix_of_qr_sq (r := g⁻¹ * r * g) (p := eu 0 1) (fun x => by rw [hqr', polarQ_eu0])
        (hΓ'c s hs _ hr')
    have hR : Γ' ⊓ pCoreOf 2 (stabV0 F) ≤ A1 F := by
      rintro h ⟨hhΓ', hhR⟩
      obtain ⟨hhS, hM⟩ := mem_pCoreOf_stabV0_iff.mp hhR
      obtain ⟨α, β, γ, p', q', rfl⟩ := eq_of_levi1Mat_eq_one hhS hM
      have hc := hΓ'c _ hhΓ' _ hr'
      rw [hab] at hc
      obtain ⟨rfl, rfl⟩ := kerElt_eq_of_comm hc
      exact kerElt_mem_A1 α p' q'
    exact ⟨g, hΓ' ▸ hS, hΓ' ▸ hR⟩
  · have hA' : ∀ r ∈ Γ, ∀ x, qr r x = 0 := fun r hr x => by
      by_contra h
      exact hA ⟨r, hr, x, h⟩
    obtain ⟨w₀, hw₀, hfix₀⟩ := exists_fix_ne_zero hΓ1
    obtain ⟨g, hg⟩ := exists_g2Act_eu_eq hw₀
    obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = Γ.map (MulAut.conj g⁻¹).toMonoidHom := ⟨_, rfl⟩
    have hS : Γ' ≤ stabV0 F := by
      rw [hΓ']
      rintro _ ⟨γ, hγ, rfl⟩
      show g2Act (g⁻¹ * γ * g⁻¹⁻¹) (eu 0 1) = eu 0 1
      rw [inv_inv, g2Act_mul_apply, g2Act_mul_apply, hg, hfix₀ γ hγ, ← hg, g2Act_inv_apply]
    have hq0 : ∀ r ∈ Γ', ∀ x, qr r x = 0 := by
      rw [hΓ']
      rintro _ ⟨γ, hγ, rfl⟩ x
      have h1 := qr_conj g⁻¹ γ (g2Act g x)
      rw [inv_inv, g2Act_inv_apply] at h1
      change qr (g⁻¹ * γ * g⁻¹⁻¹) x = 0
      rw [inv_inv, h1, hA' γ hγ]
    have hR : Γ' ⊓ pCoreOf 2 (stabV0 F) ≤ A1 F := by
      rintro h ⟨hhΓ', hhR⟩
      obtain ⟨hhS, hM⟩ := mem_pCoreOf_stabV0_iff.mp hhR
      obtain ⟨α, β, γ, p', q', rfl⟩ := eq_of_levi1Mat_eq_one hhS hM
      obtain ⟨rfl, rfl, rfl⟩ := kerElt_eq_of_qr_zero (hq0 _ hhΓ')
      exact Z1_le_A1 ⟨(p', q'), eq_uSL_of_A1⟩
    exact ⟨g, hΓ' ▸ hS, hΓ' ▸ hR⟩

@[expose] def wedge (u v : Ix3 → F) : Ix3 × Ix3 → F := fun p => u p.1 * v p.2 + v p.1 * u p.2

theorem rep2_wedge (g : ↥(cayleyGroup F)) (u v : Ix3 → F) :
    (rep2 g).mulVec (wedge u v) = wedge (g2Act g u) (g2Act g v) := by
  funext p
  obtain ⟨i, j⟩ := p
  rw [← repQ_mulVec, ← repQ_mulVec]
  simp only [wedge, rep2, kron2Rep_apply, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1 <;> (conv_rhs => rw [Finset.sum_comm]) <;>
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_ <;> ring

theorem rep2_sub_one_wedge (g : ↥(cayleyGroup F)) (u v : Ix3 → F) :
    (rep2 g - 1).mulVec (wedge u v) = wedge (g2Act g u) (g2Act g v) - wedge u v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, rep2_wedge]

abbrev kE (α p q' : F) : ↥(cayleyGroup F) := g2X ![α, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p q' 0)

omit [CharP F 2] in
theorem wedge_apply (u v : Ix3 → F) (i j : Ix3) : wedge u v (i, j) = u i * v j + v i * u j := rfl

theorem quad_wedge_vals (s t α p q' : F) :
    (rep2 (kE 0 s t) - 1).mulVec ((rep2 (kE α p q') - 1).mulVec
        (wedge (q6 0 0 0 1 0 0) (q6 0 1 0 0 0 0))) (.inr 1, .inr 2) = s * α ∧
    (rep2 (kE 0 s t) - 1).mulVec ((rep2 (kE α p q') - 1).mulVec
        (wedge (q6 0 0 0 1 0 0) (q6 0 1 0 0 0 0))) (.inr 2, .inl 0) = t * p + s * q' ∧
    (rep2 (kE 0 s t) - 1).mulVec ((rep2 (kE α p q') - 1).mulVec
        (wedge (q6 0 0 0 1 0 0) (q6 0 0 1 0 0 0))) (.inr 2, .inr 1) = t * α := by
  simp only [rep2_sub_one_wedge, Matrix.mulVec_sub, g2Act_A1, Pi.sub_apply, wedge_apply,
    q6_apply_inl0, q6_apply_inr1, q6_apply_inr2]
  refine ⟨?_, ?_, ?_⟩ <;> ring

omit [CharP F 2] in
theorem wedge_mem_lieSub {a b : Ix3} (hab : a ≠ b) (h1 : b ≠ Sum.swap a) :
    wedge (Pi.single a (1 : F)) (Pi.single b 1) ∈ lieSub F := by
  refine ⟨fun i j => ?_, fun i => ?_, ?_⟩
  · simp only [wedge_apply]
    ring
  · simp only [wedge_apply, Pi.single_apply]
    split_ifs <;> simp_all
  · simp only [wedge_apply, Pi.single_apply]
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
      simp_all

theorem rep2_sub_one_secL (g : ↥(cayleyGroup F)) (t : LIdx → F) :
    (rep2 g - 1).mulVec ((secL F).mulVec t) = (secL F).mulVec ((repLie g - 1).mulVec t) := by
  have h := sec_mul_pivotRep isPivot_lie g
  change secL F * repLie g = rep2 g * secL F at h
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]

theorem rep2_quad_of_repLie {x y : ↥(cayleyGroup F)} (h : (repLie x - 1) * (repLie y - 1) = 0)
    {T : Ix3 × Ix3 → F} (hT : T ∈ lieSub F) :
    (rep2 x - 1).mulVec ((rep2 y - 1).mulVec T) = 0 := by
  rw [← secL_restrict hT, rep2_sub_one_secL, rep2_sub_one_secL,
    Matrix.mulVec_mulVec (fun p => T (lP p)) (repLie x - 1) (repLie y - 1), h,
    Matrix.zero_mulVec, Matrix.mulVec_zero]

theorem repLie_kE_mul_ne {s t α p q' : F} (hst : s ≠ 0 ∨ t ≠ 0) (h : α ≠ 0 ∨ t * p + s * q' ≠ 0) :
    (repLie (kE 0 s t) - 1) * (repLie (kE α p q') - 1) ≠ 0 := by
  intro h0
  have hT1 := rep2_quad_of_repLie h0 (wedge_mem_lieSub (F := F) (a := .inr 0) (b := .inl 1)
    (by decide) (by decide))
  have hT2 := rep2_quad_of_repLie h0 (wedge_mem_lieSub (F := F) (a := .inr 0) (b := .inl 2)
    (by decide) (by decide))
  have e1 : (Pi.single (.inr 0) (1 : F) : Ix3 → F) = q6 0 0 0 1 0 0 := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  have e2 : (Pi.single (.inl 1) (1 : F) : Ix3 → F) = q6 0 1 0 0 0 0 := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  have e3 : (Pi.single (.inl 2) (1 : F) : Ix3 → F) = q6 0 0 1 0 0 0 := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  rw [e1, e2] at hT1
  rw [e1, e3] at hT2
  obtain ⟨v1, v2, v3⟩ := quad_wedge_vals s t α p q'
  have a1 := congrFun hT1 (.inr 1, .inr 2)
  have a2 := congrFun hT1 (.inr 2, .inl 0)
  have a3 := congrFun hT2 (.inr 2, .inr 1)
  rw [v1] at a1
  rw [v2] at a2
  rw [v3] at a3
  simp only [Pi.zero_apply] at a1 a2 a3
  rcases h with hα | hd
  · rcases hst with hs | ht
    · exact hs ((mul_eq_zero.mp a1).resolve_right hα)
    · exact ht ((mul_eq_zero.mp a3).resolve_right hα)
  · exact hd a2

theorem exists_not_quadratic_repLie [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {Γ : Subgroup ↥(cayleyGroup F)} (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1)
    (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) (hcard : Nat.card F ^ 3 ≤ Nat.card Γ) :
    ∃ x ∈ Γ, ∃ y ∈ Γ, (repLie x - 1) * (repLie y - 1) ≠ 0 := by
  have := finite_cayleyGroup (F := F)
  have hq : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨g, hS, hR⟩ := exists_conj_stab hΓ1 hΓc
  set Γ' := Γ.map (MulAut.conj g⁻¹).toMonoidHom with hΓ'
  have hΓ'1 : ∀ γ ∈ Γ', γ * γ = 1 := by
    rintro _ ⟨γ, hγ, rfl⟩
    change g⁻¹ * γ * g⁻¹⁻¹ * (g⁻¹ * γ * g⁻¹⁻¹) = 1
    rw [show g⁻¹ * γ * g⁻¹⁻¹ * (g⁻¹ * γ * g⁻¹⁻¹) = g⁻¹ * (γ * γ) * g⁻¹⁻¹ by group, hΓ1 γ hγ]
    group
  have hc' : Nat.card Γ' = Nat.card Γ := Subgroup.card_map_of_injective (MulAut.conj _).injective
  set B := Γ' ⊓ pCoreOf 2 (stabV0 F) with hB
  have h1 := card_le_mul_card_inf_R1 hF hn hS hΓ'1
  have hB2 : Nat.card F ^ 2 ≤ Nat.card B := by
    rw [hc'] at h1
    have h3 : Nat.card F * Nat.card F ^ 2 ≤ Nat.card F * Nat.card B := by
      calc Nat.card F * Nat.card F ^ 2 = Nat.card F ^ 3 := by ring
        _ ≤ _ := hcard.trans h1
    exact Nat.le_of_mul_le_mul_left h3 (by omega)
  have h2 := card_le_mul_card_inf_Z1 hR
  have hBZ : 2 ≤ Nat.card ↥(B ⊓ Z1 F) := by
    by_contra hlt
    push Not at hlt
    have h4 : Nat.card B ≤ 1 * Nat.card F :=
      h2.trans (Nat.mul_le_mul_right _ (by omega))
    have h5 : Nat.card F * Nat.card F ≤ 1 * Nat.card F := by rw [← sq]; exact hB2.trans h4
    have := Nat.le_of_mul_le_mul_right h5 (by omega)
    omega
  obtain ⟨⟨x, hxBZ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp hBZ)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨v, hv⟩ := hxBZ.2
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hx1'
    rw [hv, Prod.fst_zero, Prod.snd_zero,
      CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one]
  obtain ⟨y, hyB, hyD⟩ : ∃ y ∈ B, y ∉ rootD (dirV v) := by
    by_contra hall
    push Not at hall
    have h6 : Nat.card B ≤ Nat.card F :=
      (Subgroup.card_le_of_le hall).trans (card_rootD_le _)
    have h7 : Nat.card F * Nat.card F ≤ 1 * Nat.card F := by
      rw [← sq, one_mul]; exact hB2.trans h6
    have := Nat.le_of_mul_le_mul_right h7 (by omega)
    omega
  obtain ⟨α, p, q', hy⟩ := exists_eq_of_mem_A1 (hR hyB)
  have hxk : x = kE 0 v.1 v.2 := by rw [hv]; exact eq_uSL_of_A1.symm
  have hy' : y = kE α p q' := hy
  have hst : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (Prod.ext hcon.1 hcon.2)
  have hgood : α ≠ 0 ∨ v.2 * p + v.1 * q' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hα, hd⟩ := hcon
    apply hyD
    refine ⟨(p, q'), onLine_dirV_of hv0 ?_, by rw [hy, hα, eq_uSL_of_A1]⟩
    have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
    show p * v.2 = q' * v.1
    linear_combination hd - q' * v.1 * h2'
  have hne := repLie_kE_mul_ne hst hgood
  rw [← hxk, ← hy'] at hne
  obtain ⟨x₀, hx₀, rfl⟩ := hxBZ.1.1
  obtain ⟨y₀, hy₀, rfl⟩ := hyB.1
  refine ⟨x₀, hx₀, y₀, hy₀, fun h0 => hne ?_⟩
  change (repLie (g⁻¹ * x₀ * g⁻¹⁻¹) - 1) * (repLie (g⁻¹ * y₀ * g⁻¹⁻¹) - 1) = 0
  have e : ∀ z : ↥(cayleyGroup F), repLie (g⁻¹ * z * g⁻¹⁻¹) - 1 =
      repLie g⁻¹ * (repLie z - 1) * repLie g⁻¹⁻¹ := by
    intro z
    have hgg : repLie g⁻¹ * repLie g⁻¹⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hgg, ← map_mul, ← map_mul]
  rw [e, e]
  calc repLie g⁻¹ * (repLie x₀ - 1) * repLie g⁻¹⁻¹ * (repLie g⁻¹ * (repLie y₀ - 1) *
        repLie g⁻¹⁻¹)
      = repLie g⁻¹ * (repLie x₀ - 1) * (repLie g⁻¹⁻¹ * repLie g⁻¹) * (repLie y₀ - 1) *
        repLie g⁻¹⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by
      rw [← map_mul, inv_mul_cancel, map_one, Matrix.mul_one, Matrix.mul_assoc _ (repLie x₀ - 1),
        h0, Matrix.mul_zero, Matrix.zero_mul]

end CFSG.Quasithin.B45G2
