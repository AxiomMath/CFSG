module

public import CFSG.Sporadic.Co1.Module.LeechOddChecks
public import CFSG.Sporadic.Co1.Module.LeechOddLitFacts
public import CFSG.Sporadic.Co1.Module.OddCent
public import CFSG.Monster.GMS.Leech.Linear
import all CFSG.Sporadic.Co1.Module.OddGroup
import all CFSG.Sporadic.Co1.Module.OddFacts

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix
open CFSG.Monster.GMS (IsCo1TwoA Co1CommonFour Co1OddType Co1OddPairFacts Co1InvolutionFacts
  co1Fix co1Orbit)

attribute [local instance] vecAct vecSMul
attribute [local irreducible] rr regsRows

attribute [local irreducible] Wk vecsOne vecsTwo

theorem isT2_iff
    (x : ℕ) (hx : x < 2 ^ 24) :
    isT2 x = true ↔ toVecD 24 x ∈ MulAction.orbit Jmat v₂ := by
  rw [isT2]
  exact inPts_iff x hx

theorem mem_vecs_iff (k : ℕ) (x : ℕ) :
    x ∈ Wk k ↔ x < 2 ^ 24 ∧ rowsMatrix 24 (rr 27) *ᵥ toVecD 24 x = toVecD 24 x ∧
      rowsMatrix 24 (rr (sIdx[k]!)) *ᵥ toVecD 24 x = toVecD 24 x := by
  unfold Wk
  rw [mem_fixList [rr 27, rr (sIdx[k]!)] x]
  simp

theorem noTwo_facts :
    ∀ v : Vec24, rho3 • v = v → sRep 1 • v = v →
    v ∉ MulAction.orbit Jmat v₂ := by
  intro v h1 h2 hv
  obtain ⟨x, hx, rfl⟩ := exists_toVecD v
  have hmem : x ∈ vecsOne := by
    unfold vecsOne
    rw [mem_vecs_iff]
    exact ⟨hx, (smul_reg_iff 27 _).1 h1, (smul_reg_iff _ _).1 h2⟩
  have h := noTwoOK_true
  simp only [noTwoOK, List.all_eq_true, Bool.not_eq_true'] at h
  have h2' := h x hmem
  have h3 := (isT2_iff x hx).2 hv
  rw [h2'] at h3
  exact Bool.false_ne_true h3

theorem card_cent_rho3 :
    Nat.card ↥(Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) = 89181388800 := by
  have h := isCo1TwoA_rho3.2
  rw [rho3_ncard_fix] at h
  norm_num at h
  omega

theorem card_Zst
    (k : Fin 3) :
    Nat.card ↥(Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep k} : Set NativeSporadic.Co1)) = ![384, 1344, 96] k := by
  obtain ⟨C, hω, hρ, hs, hZn, -, -⟩ := exists_cert card_cent_rho3
  have h := C.Z_card k
  rw [hZn] at h
  have e : C.Z k = Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep k} : Set NativeSporadic.Co1) := by
    unfold OddCert.Z
    rw [hω, hρ, hs k]
  rw [← e]
  exact h

theorem disj_facts :

    ∀ y ∈ Hst, y ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) →
    y ∈ Subgroup.centralizer ({sRep 1} : Set NativeSporadic.Co1) → ¬ IsConj rho3 y :=
  disj_facts_lit zOneLit_true (card_Zst 1)

theorem isT4'_iff
    (x : ℕ) (hx : x < 2 ^ 24) :
    isT4' x = true ↔ toVecD 24 x ∈ MulAction.orbit Jmat v₄ := by
  rw [isT4']
  exact type4N_iff x hx

theorem mem_vecsTwo_iff (x : ℕ) :
    x ∈ vecsTwo ↔ x < 2 ^ 24 ∧ rho3 • toVecD 24 x = toVecD 24 x ∧
      sRep 2 • toVecD 24 x = toVecD 24 x := by
  unfold vecsTwo
  rw [mem_vecs_iff]
  constructor
  · rintro ⟨hx, h1, h2⟩
    exact ⟨hx, (smul_reg_iff 27 _).2 h1, (smul_reg_iff _ _).2 h2⟩
  · rintro ⟨hx, h1, h2⟩
    exact ⟨hx, (smul_reg_iff 27 _).1 h1, (smul_reg_iff _ _).1 h2⟩

theorem cover_facts :
    ∀ u : Vec24, rho3 • u = u → sRep 2 • u = u →
    u ∈ MulAction.orbit Jmat v₂ →
    ∃ ω : Vec24, rho3 • ω = ω ∧ sRep 2 • ω = ω ∧ ω ∈ MulAction.orbit Jmat v₄ ∧
      u + ω ∈ MulAction.orbit Jmat v₂ := by
  intro u h1 h2 hu
  obtain ⟨x, hx, rfl⟩ := exists_toVecD u
  have hw : x ∈ w2List := by
    unfold w2List
    rw [List.mem_filter]
    exact ⟨(mem_vecsTwo_iff x).2 ⟨hx, h1, h2⟩, (isT2_iff x hx).2 hu⟩
  have h := coverOK_true
  simp only [coverOK, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨y, hy, hxy⟩ := h x hw
  have hy' : y ∈ vecsTwo ∧ isT4' y = true := by
    unfold f4List at hy
    rw [List.mem_filter] at hy
    exact hy
  obtain ⟨hy24, hy1, hy2⟩ := (mem_vecsTwo_iff y).1 hy'.1
  refine ⟨toVecD 24 y, hy1, hy2, (isT4'_iff y hy24).1 hy'.2, ?_⟩
  rw [← toVecD_xor]
  exact (isT2_iff _ (Nat.xor_lt_two_pow hx hy24)).1 hxy

attribute [local irreducible] yList w2List f4List zsTwo zsTwoList

theorem orbitY_facts :
    ∃ u₀ : Vec24, rho3 • u₀ = u₀ ∧ sRep 2 • u₀ = u₀ ∧
    u₀ ∈ MulAction.orbit Jmat v₂ ∧ u₀ + omega0 ∈ MulAction.orbit Jmat v₂ ∧
    ∀ u : Vec24, rho3 • u = u → sRep 2 • u = u → u ∈ MulAction.orbit Jmat v₂ →
      u + omega0 ∈ MulAction.orbit Jmat v₂ →
      ∃ z ∈ Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
        Subgroup.centralizer ({sRep 2} : Set NativeSporadic.Co1), z • u₀ = u :=
  orbitY_facts_lit zTwoLit_true.1 zTwoLit_true.2

theorem triple_facts :
    ∃ u₁ u₂ : Vec24, rho3 • u₁ = u₁ ∧ sRep 2 • u₁ = u₁ ∧
    rho3 • u₂ = u₂ ∧ sRep 2 • u₂ = u₂ ∧ u₁ ∈ MulAction.orbit Jmat v₂ ∧
    u₂ ∈ MulAction.orbit Jmat v₂ ∧ u₁ + u₂ ∈ MulAction.orbit Jmat v₄ := by
  have h := tripleOK_true
  unfold tripleOK at h
  simp only [List.any_eq_true] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  have hw : ∀ x ∈ w2List, x ∈ vecsTwo ∧ isT2 x = true := by
    intro x hx
    unfold w2List at hx
    exact List.mem_filter.1 hx
  obtain ⟨hx1, hx2⟩ := hw x hx
  obtain ⟨hy1, hy2⟩ := hw y hy
  obtain ⟨hx24, hxa, hxb⟩ := (mem_vecsTwo_iff x).1 hx1
  obtain ⟨hy24, hya, hyb⟩ := (mem_vecsTwo_iff y).1 hy1
  refine ⟨toVecD 24 x, toVecD 24 y, hxa, hxb, hya, hyb, (isT2_iff x hx24).1 hx2,
    (isT2_iff y hy24).1 hy2, ?_⟩
  rw [← toVecD_xor]
  exact (isT4'_iff _ (Nat.xor_lt_two_pow hx24 hy24)).1 hxy

theorem outer_facts :

    ∀ y ∈ Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
    Subgroup.centralizer ({sRep 2} : Set NativeSporadic.Co1), IsConj rho3 y →
    ∃ u v : Vec24, rho3 • v = v ∧ sRep 2 • v = v ∧ v ∈ MulAction.orbit Jmat v₄ ∧
      y • u + u = v :=
  outer_facts_lit zTwoLit_true.1 outerLit_true (card_Zst 2)

theorem co1Orbit_zero_eq : co1Orbit 0 = MulAction.orbit Jmat v₂ := by
  rw [← range_co1Act v₂]
  rfl

theorem co1Orbit_two_eq : co1Orbit 2 = MulAction.orbit Jmat v₄ := by
  rw [← range_co1Act v₄]
  rfl

theorem fix4_trans
    (k : Fin 3) {ω : Vec24} (hω : ω ∈ MulAction.orbit NativeSporadic.Co1 omega0)
    (h1 : rho3 • ω = ω) (h2 : sRep k • ω = ω) :
    ∃ z ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep k} : Set NativeSporadic.Co1), z • omega0 = ω := by
  obtain ⟨C, hω₀, hρ, hs, -, -, -⟩ := exists_cert card_cent_rho3
  obtain ⟨h, rfl⟩ := hω
  have hp : (h⁻¹ * rho3 * h, h⁻¹ * sRep k * h) ∈ C.Pairs k := by
    unfold OddCert.Pairs
    rw [hω₀, hρ, hs k]
    refine ⟨?_, ?_, h⁻¹, by simp, by simp⟩
    · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, h1, inv_smul_smul]
    · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, h2, inv_smul_smul]
  rw [C.pairs_eq_orbit k] at hp
  unfold OddCert.Orb at hp
  obtain ⟨n, hn, hn'⟩ := hp
  rw [hω₀] at hn
  rw [hρ, hs k] at hn'
  simp only [Prod.mk.injEq] at hn'
  obtain ⟨hn1, hn2⟩ := hn'
  refine ⟨h * n, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have : h * n * rho3 * (h * n)⁻¹ = rho3 := by
      calc h * n * rho3 * (h * n)⁻¹ = h * (n * rho3 * n⁻¹) * h⁻¹ := by group
        _ = h * (h⁻¹ * rho3 * h) * h⁻¹ := by rw [hn1]
        _ = rho3 := by group
    exact mul_inv_eq_iff_eq_mul.1 this
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have : h * n * sRep k * (h * n)⁻¹ = sRep k := by
      calc h * n * sRep k * (h * n)⁻¹ = h * (n * sRep k * n⁻¹) * h⁻¹ := by group
        _ = h * (h⁻¹ * sRep k * h) * h⁻¹ := by rw [hn2]
        _ = sRep k := by group
    exact mul_inv_eq_iff_eq_mul.1 this
  · rw [mul_smul, MulAction.mem_stabilizer_iff.1 hn]

theorem exists_fixedPoint_of_involutive {α : Type*} [Finite α] (f : α → α)
    (hf : Function.Involutive f) (hodd : Odd (Nat.card α)) : ∃ a, f a = a := by
  have : Fintype α := Fintype.ofFinite α
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : ¬ 2 ∣ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hodd)
  have hσ : (hf.toPerm f) ^ 2 ^ 1 = 1 := by
    ext a
    show f (f a) = a
    exact hf a
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime hnd hσ
  exact ⟨a, ha⟩

@[expose] def fixed4 (k : Fin 3) : Set Vec24 :=
  {ω | ω ∈ MulAction.orbit NativeSporadic.Co1 omega0 ∧ rho3 • ω = ω ∧ sRep k • ω = ω}

theorem fixed4_ncard
    (k : Fin 3) : (fixed4 k).ncard = ![405, 135, 75] k := pair_fix4_ncard k

section Generic

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem exists_fixed_of_odd [Finite Ω] {ρ s : G} {ω₀ : Ω}
    (hodd : Odd {ω | ω ∈ MulAction.orbit G ω₀ ∧ ρ • ω = ω ∧ s • ω = ω}.ncard) {y : G}
    (hy : y ∈ Subgroup.centralizer ({ρ} : Set G) ⊓ Subgroup.centralizer ({s} : Set G))
    (hy2 : y * y = 1) :
    ∃ ω, ω ∈ MulAction.orbit G ω₀ ∧ ρ • ω = ω ∧ s • ω = ω ∧ y • ω = ω := by
  have hyρ : y * ρ = ρ * y := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).1
  have hys : y * s = s * y := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2
  set F : Set Ω := {ω | ω ∈ MulAction.orbit G ω₀ ∧ ρ • ω = ω ∧ s • ω = ω} with hF
  have hmem : ∀ ω ∈ F, y • ω ∈ F := by
    rintro ω ⟨hω, h1, h2⟩
    refine ⟨(smul_mem_orbit_iff' y ω₀ ω).2 hω, ?_, ?_⟩
    · rw [← mul_smul, ← hyρ, mul_smul, h1]
    · rw [← mul_smul, ← hys, mul_smul, h2]
  obtain ⟨ω, hω⟩ := exists_fixedPoint_of_involutive (α := ↥F)
    (fun ω => ⟨y • (ω : Ω), hmem ω ω.2⟩)
    (fun ω => Subtype.ext (by
      show y • y • (ω : Ω) = ω
      rw [← mul_smul, hy2, one_smul]))
    (by rw [Nat.card_coe_set_eq]; exact hodd)
  exact ⟨ω, ω.2.1, ω.2.2.1, ω.2.2.2, congrArg Subtype.val hω⟩

theorem exists_conj_mem_stabilizer [Finite Ω] {ρ s : G} {ω₀ : Ω}
    (hodd : Odd {ω | ω ∈ MulAction.orbit G ω₀ ∧ ρ • ω = ω ∧ s • ω = ω}.ncard)
    (htrans : ∀ ω ∈ MulAction.orbit G ω₀, ρ • ω = ω → s • ω = ω →
      ∃ z ∈ Subgroup.centralizer ({ρ} : Set G) ⊓ Subgroup.centralizer ({s} : Set G),
        z • ω₀ = ω) {y : G}
    (hy : y ∈ Subgroup.centralizer ({ρ} : Set G) ⊓ Subgroup.centralizer ({s} : Set G))
    (hy2 : y * y = 1) :
    ∃ z ∈ Subgroup.centralizer ({ρ} : Set G) ⊓ Subgroup.centralizer ({s} : Set G),
      z * y * z⁻¹ ∈ MulAction.stabilizer G ω₀ := by
  obtain ⟨ω, hω, h1, h2, hyω⟩ := exists_fixed_of_odd hodd hy hy2
  obtain ⟨z, hz, hzω⟩ := htrans ω hω h1 h2
  refine ⟨z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
  rw [MulAction.mem_stabilizer_iff, inv_inv, mul_smul, mul_smul, hzω, hyω, ← hzω,
    inv_smul_smul]

end Generic

theorem exists_conj_base
    {r s : NativeSporadic.Co1} {k : Fin 3} (hr : IsCo1TwoA r)
    (hrs : IsConj r s) (hne : s ≠ r) (hcf : Co1CommonFour r s) (ht : Co1OddType r s k) :
    ∃ g : NativeSporadic.Co1, g * rho3 * g⁻¹ = r ∧ g * sRep k * g⁻¹ = s := by
  have hI : Co1InvolutionFacts := CFSG.Monster.GMS.co1InvolutionFacts
  have hρ : IsCo1TwoA rho3 := isCo1TwoA_rho3
  obtain ⟨x₀, hx₀⟩ := isConj_iff.1 (hI.2.2 rho3 r hρ.1 hr.1 hρ.2 hr.2)
  have hs' : x₀ * (x₀⁻¹ * s * x₀) * x₀⁻¹ = s := by group
  have hconj' : IsConj rho3 (x₀⁻¹ * s * x₀) := by
    rw [← isConj_conj_iff x₀ rho3 (x₀⁻¹ * s * x₀), hx₀, hs']
    exact hrs
  have hne' : x₀⁻¹ * s * x₀ ≠ rho3 := by
    rw [← conj_ne_iff x₀ rho3 (x₀⁻¹ * s * x₀), hx₀, hs']
    exact hne
  have hcf' : Co1CommonFour rho3 (x₀⁻¹ * s * x₀) := by
    rw [← commonFour_conj x₀ rho3 (x₀⁻¹ * s * x₀), hx₀, hs']
    exact hcf
  have ht' : Co1OddType rho3 (x₀⁻¹ * s * x₀) k := by
    rw [← oddType_conj x₀ rho3 (x₀⁻¹ * s * x₀) k, hx₀, hs']
    exact ht
  have hN2 := (rho3_facts card_cent_rho3).2.1
  have htype : Co1OddType rho3 (sRep k) k := oddType_sRep hN2 k
  have hcf0 : Co1CommonFour rho3 (sRep k) := by
    refine ⟨omega0, by rw [co1Orbit_two]; exact MulAction.mem_orbit_self omega0, ?_, ?_⟩
    · rw [co1Fix_eq]
      exact MulAction.mem_stabilizer_iff.1 rho3_mem
    · rw [co1Fix_eq]
      exact MulAction.mem_stabilizer_iff.1 (sRep_mem k)
  obtain ⟨g₁, hg₁, hg₁s⟩ := (oddPf_rho3 card_cent_rho3).2.2.1 k (sRep k) (x₀⁻¹ * s * x₀)
    (sRep_conj k) hconj' hcf0 hcf' htype ht'
  refine ⟨x₀ * g₁, ?_, ?_⟩
  · have := conj_eq_of_mem_centralizer (G := NativeSporadic.Co1) hg₁
    calc x₀ * g₁ * rho3 * (x₀ * g₁)⁻¹ = x₀ * (g₁ * rho3 * g₁⁻¹) * x₀⁻¹ := by group
      _ = r := by rw [this, hx₀]
  · calc x₀ * g₁ * sRep k * (x₀ * g₁)⁻¹ = x₀ * (g₁ * sRep k * g₁⁻¹) * x₀⁻¹ := by group
      _ = s := by rw [hg₁s, hs']

theorem exists_conj_mem_Hst
    (k : Fin 3) (hodd : Odd (fixed4 k).ncard) {y : NativeSporadic.Co1}
    (hy : y ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep k} : Set NativeSporadic.Co1)) (hy2 : y * y = 1) :
    ∃ z ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep k} : Set NativeSporadic.Co1), z * y * z⁻¹ ∈ Hst ⊓
      Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep k} : Set NativeSporadic.Co1) := by
  obtain ⟨z, hz, hzy⟩ := exists_conj_mem_stabilizer (G := NativeSporadic.Co1) (Ω := Vec24)
    (ρ := rho3) (s := sRep k) (ω₀ := omega0) hodd (fun ω hω h1 h2 => fix4_trans k hω h1 h2)
    hy hy2
  refine ⟨z, hz, ?_⟩
  have hzy' : z * y * z⁻¹ ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep k} : Set NativeSporadic.Co1) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hz hy) (Subgroup.inv_mem _ hz)
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hzy, (Subgroup.mem_inf.1 hzy').1⟩,
    (Subgroup.mem_inf.1 hzy').2⟩

structure OddPairHyp (r s : NativeSporadic.Co1) : Prop where
  twoA : IsCo1TwoA r
  conj : IsConj r s
  ne : s ≠ r
  four : Co1CommonFour r s

theorem isConj_rho3_of_twoA
    {y : NativeSporadic.Co1} (hy : IsCo1TwoA y) : IsConj rho3 y :=
  CFSG.Monster.GMS.co1InvolutionFacts.2.2 rho3 y isCo1TwoA_rho3.1 hy.1 isCo1TwoA_rho3.2 hy.2

theorem mem_fix_pair_iff (g r s : NativeSporadic.Co1) (v : Vec24) :
    v ∈ co1Fix (g * r * g⁻¹) ∩ co1Fix (g * s * g⁻¹) ↔
      g⁻¹ • v ∈ co1Fix r ∩ co1Fix s := by
  show ((g * r * g⁻¹) • v = v ∧ (g * s * g⁻¹) • v = v) ↔
    (r • g⁻¹ • v = g⁻¹ • v ∧ s • g⁻¹ • v = g⁻¹ • v)
  rw [mem_fix_conj_iff, mem_fix_conj_iff]

theorem threeC_no_two
    {r s : NativeSporadic.Co1} (h : OddPairHyp r s) (ht : Co1OddType r s 1) :
    ∀ v ∈ co1Fix r ∩ co1Fix s, v ∉ co1Orbit 0 := by
  obtain ⟨g, rfl, rfl⟩ := exists_conj_base h.twoA h.conj h.ne h.four ht
  intro v hv hv0
  have hv' := (mem_fix_pair_iff g rho3 (sRep 1) v).1 hv
  refine noTwo_facts (g⁻¹ • v) hv'.1 hv'.2 ?_
  rw [← co1Orbit_zero_eq]
  exact CFSG.Monster.GMS.Leech.co1Act_mem_co1Orbit hv0 g⁻¹

theorem mul_self_of_orderOf_two {M : Type*} [Monoid M] {y : M} (h : orderOf y = 2) :
    y * y = 1 := by
  have := pow_orderOf_eq_one y
  rwa [h, pow_two] at this

theorem threeC_no_twoA_base
    {y : NativeSporadic.Co1}
    (hy : y ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep 1} : Set NativeSporadic.Co1)) (hyy : y * y = 1)
    (hconj : IsConj rho3 y) : False := by
  obtain ⟨z, hz, hzy⟩ := exists_conj_mem_Hst 1 (by rw [fixed4_ncard]; decide) hy hyy
  have hc2 : IsConj y (z * y * z⁻¹) := isConj_iff.2 ⟨z, rfl⟩
  have h1 := Subgroup.mem_inf.1 hzy
  have h2 := Subgroup.mem_inf.1 h1.1
  exact disj_facts _ h2.1 h2.2 h1.2 (hconj.trans hc2)

theorem threeC_no_twoA
    {r s : NativeSporadic.Co1} (h : OddPairHyp r s)
    (ht : Co1OddType r s 1) :
    ∀ y ∈ Subgroup.centralizer ({r} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({s} : Set NativeSporadic.Co1), ¬ IsCo1TwoA y := by
  obtain ⟨g, rfl, rfl⟩ := exists_conj_base h.twoA h.conj h.ne h.four ht
  intro y hy hy2A
  have hyρ : g⁻¹ * y * g ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) :=
    (mem_centralizer_conj_iff g rho3 y).1 (Subgroup.mem_inf.1 hy).1
  have hys : g⁻¹ * y * g ∈ Subgroup.centralizer ({sRep 1} : Set NativeSporadic.Co1) :=
    (mem_centralizer_conj_iff g (sRep 1) y).1 (Subgroup.mem_inf.1 hy).2
  have hyy : y * y = 1 := mul_self_of_orderOf_two (M := NativeSporadic.Co1) hy2A.1
  have hyy' : (g⁻¹ * y * g) * (g⁻¹ * y * g) = 1 := by
    have e : (g⁻¹ * y * g) * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
    rw [e, hyy]
    group
  have hc1 : IsConj y (g⁻¹ * y * g) := isConj_iff.2 ⟨g⁻¹, by group⟩
  exact threeC_no_twoA_base (Subgroup.mem_inf.2 ⟨hyρ, hys⟩) hyy'
    ((isConj_rho3_of_twoA hy2A).trans hc1)

section Generic5A

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem transitive_of_cover {Zf Zω : Subgroup G} (hle : Zω ≤ Zf) (W F : Set Ω) (R : Ω → Ω → Prop)
    (ω₀ u₀ : Ω) (hWstab : ∀ z ∈ Zf, ∀ u ∈ W, z • u ∈ W)
    (hRinv : ∀ z ∈ Zf, ∀ u ω, R (z • u) (z • ω) ↔ R u ω)
    (hF : ∀ ω ∈ F, ∃ z ∈ Zf, z • ω₀ = ω) (hcover : ∀ u ∈ W, ∃ ω ∈ F, R u ω)
    (hY : ∀ w ∈ W, R w ω₀ → ∃ z ∈ Zω, z • u₀ = w) {u u' : Ω} (hu : u ∈ W) (hu' : u' ∈ W) :
    ∃ z ∈ Zf, z • u = u' := by
  have key : ∀ v ∈ W, ∃ z ∈ Zf, z • u₀ = v := by
    intro v hv
    obtain ⟨ω, hωF, hRω⟩ := hcover v hv
    obtain ⟨z₁, hz₁, hz₁ω⟩ := hF ω hωF
    have hz₁i : z₁⁻¹ ∈ Zf := Zf.inv_mem hz₁
    have hR : R (z₁⁻¹ • v) ω₀ := by
      have := (hRinv z₁⁻¹ hz₁i v ω).2 hRω
      rwa [← hz₁ω, inv_smul_smul] at this
    obtain ⟨za, hza, hzau⟩ := hY (z₁⁻¹ • v) (hWstab _ hz₁i v hv) hR
    refine ⟨z₁ * za, Zf.mul_mem hz₁ (hle hza), ?_⟩
    rw [mul_smul, hzau, smul_inv_smul]
  obtain ⟨z₁, hz₁, h₁⟩ := key u hu
  obtain ⟨z₂, hz₂, h₂⟩ := key u' hu'
  refine ⟨z₂ * z₁⁻¹, Zf.mul_mem hz₂ (Zf.inv_mem hz₁), ?_⟩
  rw [mul_smul, ← h₁, inv_smul_smul, h₂]

end Generic5A

theorem smul_fixed_co1 {ρ z : NativeSporadic.Co1} (hz : z * ρ = ρ * z) {v : Vec24}
    (h : ρ • v = v) : ρ • z • v = z • v := by
  rw [← mul_smul, ← hz, mul_smul, h]

theorem smul_add_vec (g : NativeSporadic.Co1) (u v : Vec24) : g • (u + v) = g • u + g • v := by
  simp only [smul_eq_co1Act, co1Act_eq_mulVec, Matrix.mulVec_add]

theorem orbit_Co1_eq (v : Vec24) :
    MulAction.orbit NativeSporadic.Co1 v = MulAction.orbit Jmat v :=
  (orbit_eq_range v).trans (range_co1Act v)

theorem smul_mem_orbit_Jmat (z : NativeSporadic.Co1) (v w : Vec24) :
    z • w ∈ MulAction.orbit Jmat v ↔ w ∈ MulAction.orbit Jmat v := by
  rw [← orbit_Co1_eq]
  exact smul_mem_orbit_iff' z v w

theorem fiveA_trans_base
    {u u' : Vec24} (hu1 : rho3 • u = u) (hu2 : sRep 2 • u = u)
    (hu : u ∈ MulAction.orbit Jmat v₂) (hu1' : rho3 • u' = u') (hu2' : sRep 2 • u' = u')
    (hu' : u' ∈ MulAction.orbit Jmat v₂) :
    ∃ z ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep 2} : Set NativeSporadic.Co1), z • u = u' := by
  obtain ⟨u₀, -, -, -, -, hY⟩ := orbitY_facts
  refine transitive_of_cover (G := NativeSporadic.Co1) (Ω := Vec24)
    (Zf := Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep 2} : Set NativeSporadic.Co1))
    (Zω := Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep 2} : Set NativeSporadic.Co1))
    ?_ {v : Vec24 | rho3 • v = v ∧ sRep 2 • v = v ∧ v ∈ MulAction.orbit Jmat v₂} (fixed4 2)
    (fun v ω => v + ω ∈ MulAction.orbit Jmat v₂) omega0 u₀ ?_ ?_ ?_ ?_ ?_ ⟨hu1, hu2, hu⟩
    ⟨hu1', hu2', hu'⟩
  · intro z hz
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hz).1).2,
      (Subgroup.mem_inf.1 hz).2⟩
  · rintro z hz v ⟨h1, h2, h3⟩
    have hzρ : z * rho3 = rho3 * z :=
      comm_of_mem_centralizer (G := NativeSporadic.Co1) (Subgroup.mem_inf.1 hz).1
    have hzs : z * sRep 2 = sRep 2 * z :=
      comm_of_mem_centralizer (G := NativeSporadic.Co1) (Subgroup.mem_inf.1 hz).2
    exact ⟨smul_fixed_co1 hzρ h1, smul_fixed_co1 hzs h2,
      (smul_mem_orbit_Jmat z v₂ v).2 h3⟩
  · intro z _ v ω
    show z • v + z • ω ∈ MulAction.orbit Jmat v₂ ↔ v + ω ∈ MulAction.orbit Jmat v₂
    rw [← smul_add_vec]
    exact smul_mem_orbit_Jmat z v₂ _
  · intro ω hω
    exact fix4_trans 2 hω.1 hω.2.1 hω.2.2
  · rintro v ⟨h1, h2, h3⟩
    obtain ⟨ω, hω1, hω2, hω3, hω4⟩ := cover_facts v h1 h2 h3
    exact ⟨ω, ⟨by rw [orbit_omega0]; exact hω3, hω1, hω2⟩, hω4⟩
  · rintro w ⟨h1, h2, h3⟩ h4
    exact hY w h1 h2 h3 h4

theorem fiveA_outer_base
    {y : NativeSporadic.Co1}
    (hy : y ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep 2} : Set NativeSporadic.Co1)) (hyy : y * y = 1)
    (hconj : IsConj rho3 y) :
    ∃ u v : Vec24, rho3 • v = v ∧ sRep 2 • v = v ∧ v ∈ MulAction.orbit Jmat v₄ ∧
      y • u + u = v := by
  obtain ⟨z, hz, hzy⟩ := exists_conj_mem_Hst 2 (by rw [fixed4_ncard]; decide) hy hyy
  have hconj' : IsConj rho3 (z * y * z⁻¹) := hconj.trans (isConj_iff.2 ⟨z, rfl⟩)
  obtain ⟨u, v, h1, h2, h3, h4⟩ := outer_facts _ hzy hconj'
  have hzρ : z⁻¹ * rho3 = rho3 * z⁻¹ :=
    comm_of_mem_centralizer (G := NativeSporadic.Co1) (Subgroup.inv_mem _ (Subgroup.mem_inf.1 hz).1)
  have hzs : z⁻¹ * sRep 2 = sRep 2 * z⁻¹ :=
    comm_of_mem_centralizer (G := NativeSporadic.Co1) (Subgroup.inv_mem _ (Subgroup.mem_inf.1 hz).2)
  refine ⟨z⁻¹ • u, z⁻¹ • v, smul_fixed_co1 hzρ h1, smul_fixed_co1 hzs h2,
    (smul_mem_orbit_Jmat z⁻¹ v₄ v).2 h3, ?_⟩
  have e : z⁻¹ * (z * y * z⁻¹) = y * z⁻¹ := by group
  rw [← h4, smul_add_vec, ← mul_smul (z⁻¹) (z * y * z⁻¹) u, e, mul_smul]

theorem fiveA_triple_base :
    ∃ u₁ u₂ : Vec24, rho3 • u₁ = u₁ ∧ sRep 2 • u₁ = u₁ ∧
    rho3 • u₂ = u₂ ∧ sRep 2 • u₂ = u₂ ∧ u₁ ∈ MulAction.orbit Jmat v₂ ∧
    u₂ ∈ MulAction.orbit Jmat v₂ ∧ u₁ + u₂ ∈ MulAction.orbit Jmat v₄ := triple_facts

theorem smul_mem_co1Orbit_zero (g : NativeSporadic.Co1) (v : Vec24) :
    g • v ∈ co1Orbit 0 ↔ v ∈ co1Orbit 0 := by
  rw [co1Orbit_zero_eq]
  exact smul_mem_orbit_Jmat g v₂ v

theorem smul_mem_co1Orbit_two (g : NativeSporadic.Co1) (v : Vec24) :
    g • v ∈ co1Orbit 2 ↔ v ∈ co1Orbit 2 := by
  rw [co1Orbit_two_eq]
  exact smul_mem_orbit_Jmat g v₄ v

theorem fiveA_nondeg
    {r s : NativeSporadic.Co1} (h : OddPairHyp r s) (ht : Co1OddType r s 2) :
    ∀ u ∈ co1Fix r ∩ co1Fix s, (∀ v ∈ co1Fix r ∩ co1Fix s,
      CFSG.Sporadic.Co1.Module.bil₀ u v = 0) → u = 0 :=
  ((co1OddPairFacts r h.twoA).2.2.2 2 s (by decide) h.conj h.four ht).1

theorem fiveA_trans
    {r s : NativeSporadic.Co1} (h : OddPairHyp r s) (ht : Co1OddType r s 2) :
    ∀ u ∈ co1Fix r ∩ co1Fix s, ∀ u' ∈ co1Fix r ∩ co1Fix s, u ∈ co1Orbit 0 → u' ∈ co1Orbit 0 →
      ∃ z ∈ Subgroup.centralizer ({r} : Set NativeSporadic.Co1) ⊓
        Subgroup.centralizer ({s} : Set NativeSporadic.Co1),
        CFSG.Monster.GMS.co1Act z u = u' := by
  obtain ⟨g, rfl, rfl⟩ := exists_conj_base h.twoA h.conj h.ne h.four ht
  intro u hu u' hu' hu0 hu0'
  have hv := (mem_fix_pair_iff g rho3 (sRep 2) u).1 hu
  have hv' := (mem_fix_pair_iff g rho3 (sRep 2) u').1 hu'
  have ho : g⁻¹ • u ∈ MulAction.orbit Jmat v₂ := by
    rw [← co1Orbit_zero_eq]
    exact (smul_mem_co1Orbit_zero g⁻¹ u).2 hu0
  have ho' : g⁻¹ • u' ∈ MulAction.orbit Jmat v₂ := by
    rw [← co1Orbit_zero_eq]
    exact (smul_mem_co1Orbit_zero g⁻¹ u').2 hu0'
  obtain ⟨z, hz, hzu⟩ := fiveA_trans_base hv.1 hv.2 ho hv'.1 hv'.2 ho'
  refine ⟨g * z * g⁻¹, Subgroup.mem_inf.2 ⟨(mem_centralizer_conj_iff g rho3 _).2 ?_,
    (mem_centralizer_conj_iff g (sRep 2) _).2 ?_⟩, ?_⟩
  · rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group]
    exact (Subgroup.mem_inf.1 hz).1
  · rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group]
    exact (Subgroup.mem_inf.1 hz).2
  · show (g * z * g⁻¹) • u = u'
    rw [mul_smul, mul_smul, hzu, smul_inv_smul]

theorem fiveA_outer
    {r s : NativeSporadic.Co1} (h : OddPairHyp r s) (ht : Co1OddType r s 2) :
    ∀ y ∈ Subgroup.centralizer ({r} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({s} : Set NativeSporadic.Co1), IsCo1TwoA y →
      ∃ u v : Vec24, v ∈ co1Fix r ∩ co1Fix s ∧ v ∈ co1Orbit 2 ∧
        CFSG.Monster.GMS.co1Act y u + u = v := by
  obtain ⟨g, rfl, rfl⟩ := exists_conj_base h.twoA h.conj h.ne h.four ht
  intro y hy hy2A
  have hyρ : g⁻¹ * y * g ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) :=
    (mem_centralizer_conj_iff g rho3 y).1 (Subgroup.mem_inf.1 hy).1
  have hys : g⁻¹ * y * g ∈ Subgroup.centralizer ({sRep 2} : Set NativeSporadic.Co1) :=
    (mem_centralizer_conj_iff g (sRep 2) y).1 (Subgroup.mem_inf.1 hy).2
  have hyy : y * y = 1 := mul_self_of_orderOf_two (M := NativeSporadic.Co1) hy2A.1
  have hyy' : (g⁻¹ * y * g) * (g⁻¹ * y * g) = 1 := by
    have e : (g⁻¹ * y * g) * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
    rw [e, hyy]
    group
  have hc1 : IsConj y (g⁻¹ * y * g) := isConj_iff.2 ⟨g⁻¹, by group⟩
  obtain ⟨u, v, h1, h2, h3, h4⟩ := fiveA_outer_base (Subgroup.mem_inf.2 ⟨hyρ, hys⟩) hyy'
    ((isConj_rho3_of_twoA hy2A).trans hc1)
  refine ⟨g • u, g • v, ?_, ?_, ?_⟩
  · rw [mem_fix_pair_iff, inv_smul_smul]
    exact ⟨h1, h2⟩
  · rw [co1Orbit_two_eq]
    exact (smul_mem_orbit_Jmat g v₄ v).2 h3
  · show y • g • u + g • u = g • v
    have e : y * g = g * (g⁻¹ * y * g) := by group
    rw [← h4, smul_add_vec, ← mul_smul, ← mul_smul, e]

theorem fiveA_triple
    {r s : NativeSporadic.Co1} (h : OddPairHyp r s) (ht : Co1OddType r s 2) :
    ∃ u₁ u₂ : Vec24, u₁ ∈ co1Fix r ∩ co1Fix s ∧ u₂ ∈ co1Fix r ∩ co1Fix s ∧
      u₁ + u₂ ∈ co1Fix r ∩ co1Fix s ∧ u₁ ∈ co1Orbit 0 ∧ u₂ ∈ co1Orbit 0 ∧
      u₁ + u₂ ∈ co1Orbit 2 := by
  obtain ⟨g, rfl, rfl⟩ := exists_conj_base h.twoA h.conj h.ne h.four ht
  obtain ⟨u₁, u₂, h1, h2, h3, h4, h5, h6, h7⟩ := fiveA_triple_base
  have hs : ∀ {v : Vec24}, rho3 • v = v → sRep 2 • v = v →
      g • v ∈ co1Fix (g * rho3 * g⁻¹) ∩ co1Fix (g * sRep 2 * g⁻¹) := by
    intro v hv1 hv2
    rw [mem_fix_pair_iff, inv_smul_smul]
    exact ⟨hv1, hv2⟩
  refine ⟨g • u₁, g • u₂, hs h1 h2, hs h3 h4, ?_, ?_, ?_, ?_⟩
  · rw [← smul_add_vec]
    exact hs (by rw [smul_add_vec, h1, h3]) (by rw [smul_add_vec, h2, h4])
  · rw [smul_mem_co1Orbit_zero, co1Orbit_zero_eq]
    exact h5
  · rw [smul_mem_co1Orbit_zero, co1Orbit_zero_eq]
    exact h6
  · rw [← smul_add_vec, smul_mem_co1Orbit_two, co1Orbit_two_eq]
    exact h7

end CFSG.Sporadic.Co1.Module.Odd
