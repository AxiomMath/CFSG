module

public import CFSG.Quasithin.Vol2.E2FourteenA
public import CFSG.Quasithin.Background.G2SixCore
public import CFSG.Quasithin.Background.G13Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 SL2Model
open scoped MatrixGroups commutatorElement

namespace E2

section SLTwo

variable {F : Type*} [Field F]

theorem mul_e12_eq_of_lower_left_eq_zero {A : SL(2, F)} (hA : A.1 1 0 = 0) (c : F) :
    A * e12 c = e12 (A.1 0 0 * A.1 0 0 * c) * A := by
  have hdet := det_eq_one' A
  rw [hA, mul_zero, sub_zero] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hA]
  linear_combination (-(A.1 0 0 * c)) * hdet

theorem mem_normalizer_Rg_of_lower_left_eq_zero {A : SL(2, F)} (hA : A.1 1 0 = 0) :
    A ∈ Subgroup.normalizer (Rg F : Set SL(2, F)) := by
  have key : ∀ B : SL(2, F), B.1 1 0 = 0 → ∀ r ∈ Rg F, B * r * B⁻¹ ∈ Rg F := by
    intro B hB r hr
    obtain ⟨c, rfl⟩ := mem_Rg.1 hr
    rw [mul_e12_eq_of_lower_left_eq_zero hB c, mul_inv_cancel_right]
    exact e12_mem_Rg _
  have hA' : (A⁻¹).1 1 0 = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hA]
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨key A hA r, fun h => ?_⟩
  have := key A⁻¹ hA' _ h
  simpa [mul_assoc] using this

theorem lower_left_eq_zero_of_mem_normalizer_Rg {A : SL(2, F)}
    (hA : A ∈ Subgroup.normalizer (Rg F : Set SL(2, F))) : A.1 1 0 = 0 := by
  obtain ⟨c, hc⟩ := mem_Rg.1 ((Subgroup.mem_normalizer_iff.mp hA (e12 1)).mp (e12_mem_Rg 1))
  have e : A * e12 1 = e12 c * A := by
    rw [hc]
    group
  have h11 := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F) 1 1) e
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h11
  linear_combination h11

variable [CharP F 2]

theorem upper_left_ne_one {A : SL(2, F)} (hA : A.1 1 0 = 0) (h1 : A ≠ 1)
    (hodd : Odd (orderOf A)) : A.1 0 0 ≠ 1 := by
  intro ha
  have hdet := det_eq_one' A
  rw [hA, ha, mul_zero, sub_zero, one_mul] at hdet
  have hAe : A = e12 (A.1 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hA, hdet]
  have h2 : A ^ 2 = 1 := by
    rw [pow_two, hAe, e12_mul_self]
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  have hord : orderOf A = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact h1 (orderOf_eq_one_iff.mp hord)

omit [CharP F 2] in
theorem eq_zero_of_smul_eq {A : SL(2, F)} (hA : A.1 1 0 = 0) (ha : A.1 0 0 ≠ 1)
    {w : Fin 2 → F} (hw : A • w = w) : w = 0 := by
  have hdet := det_eq_one' A
  rw [hA, mul_zero, sub_zero] at hdet
  have hd : A.1 1 1 ≠ 1 := fun h => ha (by rw [h, mul_one] at hdet; exact hdet)
  have hw' : A • (![w 0, w 1] : Fin 2 → F) = ![w 0, w 1] := by
    have e : (![w 0, w 1] : Fin 2 → F) = w := by
      ext i
      fin_cases i <;> rfl
    rw [e]
    exact hw
  rw [smul_vec, hA, zero_mul, zero_add] at hw'
  have h0 := congrFun hw' 0
  have h1 := congrFun hw' 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hw1 : w 1 = 0 := by
    have : (A.1 1 1 - 1) * w 1 = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hd
    · exact h
  have hw0 : w 0 = 0 := by
    have : (A.1 0 0 - 1) * w 0 = 0 := by linear_combination h0 - A.1 0 1 * hw1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) ha
    · exact h
  ext i
  fin_cases i
  · exact hw0
  · exact hw1

theorem eq_zero_of_conj_e12_eq {A : SL(2, F)} (hA : A.1 1 0 = 0) (ha : A.1 0 0 ≠ 1) {c : F}
    (hc : A * e12 c * A⁻¹ = e12 c) : c = 0 := by
  rw [mul_e12_eq_of_lower_left_eq_zero hA c, mul_inv_cancel_right] at hc
  have h1 := e12_injective hc
  have h2 : (A.1 0 0 * A.1 0 0 - 1) * c = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h | h
  · exfalso
    apply ha
    have h3 : (A.1 0 0 - 1) * (A.1 0 0 - 1) = 0 := by
      have h4 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination h + (1 - A.1 0 0) * h4
    rcases mul_eq_zero.1 h3 with h5 | h5 <;> exact sub_eq_zero.1 h5
  · exact h

end SLTwo

section Natural

variable {G : Type} [Group G] [Finite G]

theorem not_isSz_three_of_isPSL {X : Type} [Group X] {k : ℕ}
    (hP : IsPSL 2 2 k X) : ¬ IsSz 3 X := by
  intro hS
  obtain ⟨-, hc⟩ := card_of_isSz hS
  obtain ⟨K, _, _, hK, ⟨θ⟩⟩ := Ch3E213M.exists_equiv_projectiveSL_of_isPSL hP
  rw [Nat.card_congr θ.toEquiv, Ch3E213M.card_projectiveSL_two_pow hK] at hc
  have hk := two_le_of_isPSL hP
  rcases Nat.lt_or_ge k 7 with hk7 | hk7
  · interval_cases k <;> norm_num at hc
  · have hq : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk7
    set q := 2 ^ k
    have h1 : 128 * 128 ≤ q * q := Nat.mul_le_mul (by simpa using hq) (by simpa using hq)
    have h2 : 16383 ≤ q ^ 2 - 1 := by
      rw [pow_two]
      omega
    have h3 : 128 * 16383 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul (by simpa using hq) h2
    norm_num at hc
    omega

theorem exists_natural_of_psl {T M V I : Subgroup G} {g : G} (hp : Pair I (T ⊓ I) (M ⊓ I) V g)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) (hg : g ∈ I) (hgen : I = V ⊔ B6.conjSub g V)
    (hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set G)) (hJ : pCoreOf 2 I = kerIn (M ⊓ I) I)
    (hPJ : Pair.PP (M ⊓ I) V I g = kerIn (M ⊓ I) I)
    (hBor : star (M ⊓ I) I (M ⊓ I) =
      Subgroup.normalizer (star (M ⊓ I) I (T ⊓ I) : Set (StarQuot (M ⊓ I) I)))
    (hVZ : star (M ⊓ I) I V = ASInputs.e214ZT T M I) {k : ℕ} (hk : 2 ≤ k)
    (hY : IsPSL 2 2 k (StarQuot (M ⊓ I) I)) :
    ∃ s : ℕ, (V ⊓ B6.conjSub g V).relIndex (kerIn (M ⊓ I) I ⊓ V) = (2 ^ k) ^ s ∧
      (∀ y ∈ M ⊓ I, y ∉ kerIn (M ⊓ I) I → Odd (orderOf y) →
        (∀ x ∈ Pair.PP (M ⊓ I) V I g, y * x * y⁻¹ * x⁻¹ ∈ V ⊓ B6.conjSub g V →
          x ∈ V ⊓ B6.conjSub g V) ∧
        ∀ v ∈ V, y * v * y⁻¹ = v → v ∈ kerIn (M ⊓ I) I) ∧
      (s = 1 → ∀ x ∈ Pair.PP (M ⊓ I) V I g, x ^ 2 = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := E2P.finite_starQuot (M ⊓ I) I
  have hS := isSylowTwoOf_star_inf (M := M) hsyl
  set Ts := star (M ⊓ I) I (T ⊓ I) with hTs
  have hVT : star (M ⊓ I) I V = Ts := by
    rw [hVZ]
    exact le_antisymm inf_le_left fun t ht => ⟨ht, Subgroup.mem_centralizer_iff.mpr fun x hx =>
      comm_of_mem_sylow_isPSL hY hS hx ht⟩
  obtain ⟨K, _, _, hK, ⟨θ₀⟩⟩ := Ch3E213M.exists_equiv_projectiveSL_of_isPSL hY
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  set θ₁ := θ₀.trans (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL K)
    with hθ₁
  have hT1 := isSylowTwoOf_map_equiv θ₁ hS
  have hR : IsSylowTwoOf (Rg K) ⊤ := by
    refine ⟨le_top, Rg_isPGroup, ?_⟩
    rw [show ((Rg K).subgroupOf ⊤).index = (Rg K).index from Subgroup.relIndex_top_right _]
    exact Rg_index_odd
  obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj hR hT1
  set θ := θ₁.trans (MulAut.conj c⁻¹) with hθ
  have hθapp : ∀ t, θ t = c⁻¹ * θ₁ t * c⁻¹⁻¹ := fun t => rfl
  have hθT : ∀ t, t ∈ Ts ↔ θ t ∈ Rg K := by
    intro t
    rw [hθapp, inv_inv, ← mem_conjSub, ← hc]
    constructor
    · intro ht
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t', ht', he⟩
      rwa [θ₁.injective he] at ht'
  set β : ↥I →* SL(2, K) := θ.toMonoidHom.comp (E2P.starMap (M ⊓ I) I) with hβ
  have hβapp : ∀ x, β x = θ (E2P.starMap (M ⊓ I) I x) := fun x => rfl
  have hβs : Function.Surjective β := θ.surjective.comp (E2P.starMap_surjective _ _)
  have hβker : ∀ x : ↥I, β x = 1 ↔ (x : G) ∈ kerIn (M ⊓ I) I := by
    intro x
    rw [hβapp, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, E2P.ker_starMap,
      Subgroup.mem_subgroupOf]
  have hβV : ∀ v (hv : v ∈ V) (hvI : v ∈ I), β ⟨v, hvI⟩ ∈ Rg K := by
    intro v hv hvI
    rw [hβapp, ← hθT, ← hVT]
    exact ⟨⟨v, hvI⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩
  have hNiff : ∀ x : ↥I, β x ∈ Subgroup.normalizer (Rg K : Set SL(2, K)) ↔
      E2P.starMap (M ⊓ I) I x ∈ Subgroup.normalizer (Ts : Set (StarQuot (M ⊓ I) I)) := by
    intro x
    rw [hβapp, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h t
      rw [hθT, hθT, map_mul, map_mul, map_inv]
      exact h (θ t)
    · intro h r
      obtain ⟨t, rfl⟩ := θ.surjective r
      rw [← hθT, ← map_inv, ← map_mul, ← map_mul, ← hθT]
      exact h t
  have hNV : ∀ x : ↥I, β x ∈ Subgroup.normalizer (Rg K : Set SL(2, K)) →
      (x : G) ∈ Subgroup.normalizer (V : Set G) := by
    intro x hx
    have h1 : E2P.starMap (M ⊓ I) I x ∈ star (M ⊓ I) I (M ⊓ I) := by
      rw [hBor]
      exact (hNiff x).1 hx
    obtain ⟨m, hm, hmx⟩ := h1
    replace hm : (m : G) ∈ M ⊓ I := hm
    have hmx' : (QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) m : StarQuot (M ⊓ I) I) =
        QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) x := hmx
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hmx'
    have hj : (m : G)⁻¹ * x ∈ pCoreOf 2 I := by
      rw [hJ]
      simpa using hmx'
    have e : (x : G) = m * ((m : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hMN hm) (hp.pCoreOf_le_normalizer hj)
  have hinv : ∀ i : ↥I, (β i).1 1 0 = 0 → ∀ w ∈ kerIn (M ⊓ I) I ⊓ V,
      (i : G) * w * (i : G)⁻¹ ∈ kerIn (M ⊓ I) I ⊓ V := by
    intro i hi w hw
    have hiN := hNV i (mem_normalizer_Rg_of_lower_left_eq_zero hi)
    exact ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn (M ⊓ I) I i.2) w).mp hw.1,
      (Subgroup.mem_normalizer_iff.mp hiN w).mp hw.2⟩
  have hh : (β ⟨g, hg⟩).1 1 0 ≠ 0 := by
    intro h0
    have hgN := hNV ⟨g, hg⟩ (mem_normalizer_Rg_of_lower_left_eq_zero h0)
    have hIV : ∀ x ∈ I, x ∈ V := by
      intro x hx
      rw [hgen, conjSub_eq_self hgN, sup_idem] at hx
      exact hx
    obtain ⟨a, b, hab⟩ := nonabelian_of_psl_or_sz (by omega : 1 < k) (Or.inl hY)
    obtain ⟨a', rfl⟩ := E2P.starMap_surjective (M ⊓ I) I a
    obtain ⟨b', rfl⟩ := E2P.starMap_surjective (M ⊓ I) I b
    apply hab
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hp.comm (hIV _ a'.2) (hIV _ b'.2))
  have hRU : ∀ r ∈ Rg K, ∃ u : ↥I, (u : G) ∈ V ∧ β u = r := by
    intro r hr
    obtain ⟨t, rfl⟩ := θ.surjective r
    have ht : t ∈ star (M ⊓ I) I V := by
      rw [hVT, hθT]
      exact hr
    obtain ⟨u, hu, rfl⟩ := ht
    exact ⟨u, Subgroup.mem_subgroupOf.1 hu, rfl⟩
  have hcomm : ∀ u ∈ V, ∀ x ∈ Pair.PP (M ⊓ I) V I g, ⁅u, x⁆ ∈ kerIn (M ⊓ I) I ⊓ V :=
    fun u hu x hx => by
      rw [commutatorElement_def]
      exact hp.commutator_mem_B hu (hp.P_le_pCoreOf hx)
  have hfix : ∀ u ∈ V, ∀ w ∈ kerIn (M ⊓ I) I ⊓ V, ⁅u, w⁆ ∈ V ⊓ B6.conjSub g V :=
    fun u hu w hw => by
      rw [commutatorElement_def, hp.comm hu hw.2, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
  have Q : QuotSetting I (Pair.PP (M ⊓ I) V I g) (V ⊓ B6.conjSub g V) :=
    ⟨hp.inf_conj_le_P, hp.P_le_X,
      fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (hp.le_normalizer_P hx) y).mp hy,
      fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (hp.le_normalizer_Z hx) y).mp hy,
      fun a ha b hb => (hp.commutator_sq_mem_Z ha hb).1,
      fun a ha => by
        rw [← pow_two]
        exact (hp.commutator_sq_mem_Z ha ha).2⟩
  obtain ⟨s, φ, hφs, hφk, hφe, hcardB, -⟩ := exists_sum_natural_of_halves
    (G1.theorem_G_1_3_two (F := K)) Q β hβs
    (fun x hx => by rw [hPJ]; exact (hβker x).1 hx)
    hp.inf_conj_le_kerIn_inf le_sup_left ⟨g, hg⟩ hh (fun y => mem_conjSub) hinv hRU hcomm hfix
    hp.B_inf_A rfl
  have hrel : (V ⊓ B6.conjSub g V).relIndex (kerIn (M ⊓ I) I ⊓ V) = (2 ^ k) ^ s := by
    have h1 := Subgroup.relIndex_mul_card (V ⊓ B6.conjSub g V) (kerIn (M ⊓ I) I ⊓ V)
    rw [inf_eq_left.2 hp.inf_conj_le_kerIn_inf, hcardB, hK, mul_comm (Nat.card _)] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  refine ⟨s, hrel, fun y hy hyJ hyo => ?_, fun hs1 x hx => ?_⟩
  · set yI : ↥I := ⟨y, hy.2⟩ with hyI
    have hyN : β yI ∈ Subgroup.normalizer (Rg K : Set SL(2, K)) := by
      rw [hNiff, ← hBor]
      exact ⟨yI, Subgroup.mem_subgroupOf.2 hy, rfl⟩
    have h10 := lower_left_eq_zero_of_mem_normalizer_Rg hyN
    have hy1 : β yI ≠ 1 := fun h1 => hyJ ((hβker yI).1 h1)
    have hodd : Odd (orderOf (β yI)) := by
      have h1 : orderOf (β yI) ∣ orderOf yI := orderOf_map_dvd β yI
      rw [hyI, Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hyo h1
    have ha := upper_left_ne_one h10 hy1 hodd
    refine ⟨fun x hx hxy => ?_, fun v hv hvy => ?_⟩
    ·
      set xP : ↥(Pair.PP (M ⊓ I) V I g) := ⟨x, hx⟩ with hxP
      have hyx : y * x * y⁻¹ ∈ Pair.PP (M ⊓ I) V I g :=
        (Subgroup.mem_normalizer_iff.mp (hp.le_normalizer_P hy.2) x).mp hx
      have h1 := hφe yI xP ⟨y * x * y⁻¹, hyx⟩ rfl
      have h2 : φ ⟨y * x * y⁻¹, hyx⟩ = φ xP := by
        have hz : (⟨y * x * y⁻¹, hyx⟩ : ↥(Pair.PP (M ⊓ I) V I g)) =
            ⟨y * x * y⁻¹ * x⁻¹, Q.S₂_le hxy⟩ * xP := by
          apply Subtype.ext
          show y * x * y⁻¹ = y * x * y⁻¹ * x⁻¹ * x
          group
        rw [hz, map_mul, (hφk _).2 hxy, one_mul]
      rw [h2] at h1
      have h3 : Multiplicative.toAdd (φ xP) = 0 := by
        funext j
        have h4 := congrArg (fun w : Multiplicative (Fin s → Fin 2 → K) =>
          Multiplicative.toAdd w j) h1
        simp only [toAdd_ofAdd] at h4
        exact eq_zero_of_smul_eq h10 ha h4.symm
      refine (hφk xP).1 ?_
      rw [← ofAdd_toAdd (φ xP), h3, ofAdd_zero]
    ·
      have hvI : v ∈ I := hp.V_le hv
      obtain ⟨c', hc'⟩ := mem_Rg.1 (hβV v hv hvI)
      have h1 : β yI * e12 c' * (β yI)⁻¹ = e12 c' := by
        rw [hc', ← map_inv, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hvy
      have h2 := eq_zero_of_conj_e12_eq h10 ha h1
      rw [h2, e12_zero] at hc'
      exact (hβker ⟨v, hvI⟩).1 hc'.symm
  ·
    subst hs1
    by_cases hxZ : x ∈ V ⊓ B6.conjSub g V
    · exact hp.elem.2 x hxZ.1
    obtain ⟨b, hbB, hbZ⟩ : ∃ b ∈ kerIn (M ⊓ I) I ⊓ V, b ∉ V ⊓ B6.conjSub g V := by
      by_contra hno
      push Not at hno
      have h1 : (V ⊓ B6.conjSub g V).relIndex (kerIn (M ⊓ I) I ⊓ V) = 1 :=
        Subgroup.relIndex_eq_one.2 fun b hb => hno b hb
      rw [hrel, pow_one] at h1
      have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega
    have hcoord : ∀ w : ↥(Pair.PP (M ⊓ I) V I g), (w : G) ∉ V ⊓ B6.conjSub g V →
        Multiplicative.toAdd (φ w) 0 ≠ 0 := by
      intro w hw h0
      apply hw
      refine (hφk w).1 ?_
      have h3 : Multiplicative.toAdd (φ w) = 0 := by
        funext j
        rw [Fin.fin_one_eq_zero j]
        exact h0
      rw [← ofAdd_toAdd (φ w), h3, ofAdd_zero]
    set xP : ↥(Pair.PP (M ⊓ I) V I g) := ⟨x, hx⟩ with hxP
    set bP : ↥(Pair.PP (M ⊓ I) V I g) := ⟨b, le_sup_left (a := kerIn (M ⊓ I) I ⊓ V) hbB⟩
      with hbP
    obtain ⟨A0, hA0⟩ := exists_smul_eq _ _ (hcoord bP hbZ) (hcoord xP hxZ)
    obtain ⟨m, rfl⟩ := hβs A0
    have hmb : (m : G) * b * (m : G)⁻¹ ∈ Pair.PP (M ⊓ I) V I g :=
      (Subgroup.mem_normalizer_iff.mp (hp.le_normalizer_P m.2) b).mp bP.2
    have h1 := hφe m bP ⟨m * b * m⁻¹, hmb⟩ rfl
    have h2 : φ ⟨m * b * m⁻¹, hmb⟩ = φ xP := by
      rw [h1]
      apply Multiplicative.toAdd.injective
      funext j
      rw [Fin.fin_one_eq_zero j, toAdd_ofAdd]
      exact hA0
    have hz : ((m : G) * b * (m : G)⁻¹)⁻¹ * x ∈ V ⊓ B6.conjSub g V := by
      have h3 := (hφk ((⟨m * b * m⁻¹, hmb⟩ : ↥(Pair.PP (M ⊓ I) V I g))⁻¹ * xP)).1
        (by rw [map_mul, map_inv, h2, inv_mul_cancel])
      simpa using h3
    have hmbI : (m : G) * b * (m : G)⁻¹ ∈ I := hp.P_le_X hmb
    have hzc := hp.mem_center hz hmbI
    have hb2 : b * b = 1 := by
      rw [← pow_two]
      exact hp.elem.2 b hbB.2
    have hz2 : (((m : G) * b * (m : G)⁻¹)⁻¹ * x) * (((m : G) * b * (m : G)⁻¹)⁻¹ * x) = 1 := by
      rw [← pow_two]
      exact hp.elem.2 _ hz.1
    have hxz : x = ((m : G) * b * (m : G)⁻¹) * (((m : G) * b * (m : G)⁻¹)⁻¹ * x) := by group
    rw [hxz, pow_two]
    calc (m : G) * b * (m : G)⁻¹ * (((m : G) * b * (m : G)⁻¹)⁻¹ * x) *
          ((m : G) * b * (m : G)⁻¹ * (((m : G) * b * (m : G)⁻¹)⁻¹ * x)) =
        (m : G) * b * (m : G)⁻¹ * ((((m : G) * b * (m : G)⁻¹)⁻¹ * x) *
          ((m : G) * b * (m : G)⁻¹)) * (((m : G) * b * (m : G)⁻¹)⁻¹ * x) := by group
      _ = (m : G) * b * (m : G)⁻¹ * (((m : G) * b * (m : G)⁻¹) *
          (((m : G) * b * (m : G)⁻¹)⁻¹ * x)) * (((m : G) * b * (m : G)⁻¹)⁻¹ * x) := by
        rw [hzc]
      _ = (m : G) * (b * b) * (m : G)⁻¹ * ((((m : G) * b * (m : G)⁻¹)⁻¹ * x) *
          (((m : G) * b * (m : G)⁻¹)⁻¹ * x)) := by group
      _ = 1 := by rw [hb2, hz2]; group

end Natural

end E2

theorem ASInputs.isBorelIn_star_of_psl_or_sz {G : Type} [Group G] [Finite G]
    {H T M V I : Subgroup G} (hI : ASInputs.IsInIHTVC H T M V I) {k : ℕ} (hk : 2 ≤ k)
    (hY : IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) :
    E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I)) := by
  have := E2P.finite_starQuot (M ⊓ I) I
  obtain ⟨-, -, hsyl, -, k', -, hc⟩ := hI
  rcases hc with ⟨-, -, hB⟩ | ⟨-, p, a, hp', hp2, -, ⟨e⟩⟩ | ⟨-, -, -, hB, -⟩
  · exact hB
  · exfalso
    have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
    obtain ⟨hcard, -⟩ := E2.exists_conj_of_mem_center hk hY hS
    have h2 := E2.card_le_two_of_isPGroup_dihedral (hp'.odd_of_ne_two hp2).pow e hS.2.1
    have h3 := Subgroup.card_le_of_le (inf_le_left : E2.star (M ⊓ I) I (T ⊓ I) ⊓
      Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)) ≤
        E2.star (M ⊓ I) I (T ⊓ I))
    rw [hcard] at h3
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  · exact hB

theorem ASInputs.e2_14_three_nine
    (hKG1 : E2.KGSz8CoverInvolutions) (hKG3 : E2.KGI22One)
    {G : Type} [Group G] [Finite G] {H T M V I : Subgroup G} {g : G} (h : E2.Hyp28 H T M V)
    (hTI : IsTISetIn V M) (hI : ASInputs.IsInIHTVC H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V) (hZ : V ⊓ B6.conjSub g V ≠ ⊥) :
    (∀ k : ℕ, 1 < k → IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) →
      ∀ X : Subgroup G, X ≤ M ⊓ I → Nat.card X = 2 ^ k - 1 →
        ∀ x ∈ ASInputs.e214P V I g, (∀ y ∈ X, y * x * y⁻¹ * x⁻¹ ∈ V ⊓ B6.conjSub g V) →
          x ∈ V ⊓ B6.conjSub g V) ∧
    ∀ k : ℕ, 1 < k → IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) →
      ∀ X : Subgroup G, X ≤ M ⊓ I → Nat.card X = 2 ^ k - 1 →
        V ⊓ Subgroup.centralizer (X : Set G) = V ⊓ B6.conjSub g V := by
  have hp := h.pair_of_member (ASInputs.isInIHTVNoRoot_of_isInIHTVC hI) hg hgen
  have hPeq : ASInputs.e214P V I g = E2.Pair.PP (M ⊓ I) V I g := by
    show B6.conjSub g V ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I =
      (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V)
    rw [hp.conjSub_kerIn_inf_eq, hp.kerIn_inf_eq, sup_comm]
  have key : ∀ k : ℕ, 1 < k → IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) →
      ∀ X : Subgroup G, X ≤ M ⊓ I → Nat.card X = 2 ^ k - 1 →
      ∃ y ∈ X, (∀ x ∈ ASInputs.e214P V I g, y * x * y⁻¹ * x⁻¹ ∈ V ⊓ B6.conjSub g V →
          x ∈ V ⊓ B6.conjSub g V) ∧
        ∀ v ∈ V, y * v * y⁻¹ = v → v ∈ V ⊓ B6.conjSub g V := by
    intro k hk1 hY X hXM hXc
    have hD : ASInputs.IsDihL2Sz (E2.StarQuot (M ⊓ I) I) := Or.inr (Or.inl ⟨k, hY⟩)
    obtain ⟨h1, ⟨hP2, hVZ⟩, -⟩ := ASInputs.e2_14_one_two_six hKG1 hKG3 h hTI hI hg hgen hZ hD
    obtain ⟨-, -, -, -, hJ, -⟩ := ASInputs.e2_11C_of_not_S6 hKG1 hKG3 h
      (ASInputs.isInIHTVNoRoot_of_isInIHTVC hI) (E2.isEmpty_perm_six_of_isDihL2Sz hD) hg hgen
    have hsyl := hI.2.2.1
    have hTMI : T ⊓ I ≤ M ⊓ I := inf_le_inf_right I h.minParabolic.le
    have hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set G) := h1.le.trans inf_le_right
    have hPJ : E2.Pair.PP (M ⊓ I) V I g = kerIn (M ⊓ I) I := by
      rw [← hPeq]
      exact hP2.resolve_right (E2.not_isSz_three_of_isPSL hY)
    have hBor := E2.star_eq_normalizer_of_isBorelIn hTMI hsyl
      (ASInputs.isBorelIn_star_of_psl_or_sz hI hk1 (Or.inl hY))
    obtain ⟨-, -, hfix, -⟩ := E2.exists_natural_of_psl hp hsyl hg hgen hMN hJ hPJ hBor hVZ hk1 hY
    obtain ⟨y, hyX, hy1⟩ : ∃ y ∈ X, y ≠ 1 := by
      by_contra hne
      push Not at hne
      have hXb : X = ⊥ := (Subgroup.eq_bot_iff_forall X).2 hne
      rw [hXb, Subgroup.card_bot] at hXc
      have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
      omega
    have hyo : Odd (orderOf y) := by
      have h4 : Odd (Nat.card X) := by
        rw [hXc]
        exact Ch3E213M.odd_two_pow_sub_one (by omega)
      exact Odd.of_dvd_nat h4 (Subgroup.orderOf_dvd_natCard X hyX)
    have hyJ : y ∉ kerIn (M ⊓ I) I := by
      intro hyK
      rw [← hJ] at hyK
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I ⟨y, hyK⟩
      have hn' : y ^ 2 ^ n = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      exact hy1 (E2.eq_one_of_two_pow_of_odd hn' hyo)
    obtain ⟨hfP, hfV⟩ := hfix y (hXM hyX) hyJ hyo
    refine ⟨y, hyX, fun x hx hxy => hfP x (hPeq ▸ hx) hxy, fun v hv hvy => ?_⟩
    have hvJ := hfV v hv hvy
    refine hfP v (Subgroup.mem_sup_left ⟨hvJ, hv⟩) ?_
    rw [hvy, mul_inv_cancel]
    exact Subgroup.one_mem _
  refine ⟨fun k hk1 hY X hXM hXc x hx hxy => ?_, fun k hk1 hY X hXM hXc => ?_⟩
  · obtain ⟨y, hyX, hfP, -⟩ := key k hk1 hY X hXM hXc
    exact hfP x hx (hxy y hyX)
  · obtain ⟨y, hyX, -, hfV⟩ := key k hk1 hY X hXM hXc
    refine le_antisymm (fun v hv => hfV v hv.1 ?_) fun z hz =>
      ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun x hx => (hp.mem_center hz (hXM hx).2).symm⟩
    rw [(Subgroup.mem_centralizer_iff.mp hv.2 y hyX), mul_inv_cancel_right]

end CFSG.Quasithin
