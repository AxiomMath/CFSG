module

public import CFSG.Quasithin.H13.L32AH63b
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.L32A.G58

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.Family

theorem alt5_pow : ∀ z : alternatingGroup (Fin 5), z ^ 2 = 1 ∨ z ^ 3 = 1 ∨ z ^ 5 = 1 := by
  decide +kernel

theorem alt5_not_comm {a v : alternatingGroup (Fin 5)} (ha : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hv : v ^ 2 = 1) (hv1 : v ≠ 1) : a * v ≠ v * a := by
  intro hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : orderOf a = 3 := orderOf_eq_prime ha ha1
  have h2 : orderOf v = 2 := orderOf_eq_prime hv hv1
  have h6 : orderOf (a * v) = 6 := by
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hc (by rw [h3, h2]; norm_num), h3, h2]
  rcases alt5_pow (a * v) with h | h | h <;>
  · have := orderOf_dvd_of_pow_eq_one h
    rw [h6] at this
    norm_num at this

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem congr_conj {X Y : Type*} [Group X] [Group Y] (E : X ≃* Y) (c : X) :
    MulAut.congr E (MulAut.conj c) = MulAut.conj (E c) := by
  ext h
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem exists_conj_of_pow_three {X : Type*} [Group X] (E : X ≃* GL32) (α : MulAut X)
    (hα : α ^ 3 = 1) : ∃ c : X, α = MulAut.conj c := by
  set β := MulAut.congr E α with hβdef
  have hβ : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  obtain ⟨g, hg⟩ :=
    Subgroup.sq_mem_of_index_two CFSG.LieType.SteinbergBR.AutGL32.index_inner β
  have hβ' : β = (β ^ 2)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    rw [pow_succ'] at hβ
    exact hβ
  refine ⟨E.symm g⁻¹, (MulAut.congr E).injective ?_⟩
  rw [congr_conj, MulEquiv.apply_symm_apply, ← hβdef, hβ', ← hg, map_inv]

theorem center_sl32 : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have key : ∀ r : ZMod 2, r ^ 3 = 1 → r = 1 := by decide
  have hr1 : r = 1 := key r (by rwa [Fintype.card_fin] at hr)
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by rw [← hrA, hr1]; simp)

theorem isSimpleGroup_sl32 : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hs := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  have e : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq center_sl32.symm)
  exact (MulEquiv.isSimpleGroup_congr e).mpr hs

theorem mem_borel_of_conj :
    ∀ g : H6.Γ, (∀ i : Fin 8, g * H6.bel i * g⁻¹ ∈ H6.borel) → g ∈ H6.borel := by
  decide +kernel

theorem mem_of_normalizes_of_card_eight {Q : Subgroup H6.Γ} (hQ : Nat.card Q = 8) {c : H6.Γ}
    (hc : ∀ x ∈ Q, c * x * c⁻¹ ∈ Q) : c ∈ Q := by
  have hcard : Nat.card Q = 2 ^ (Nat.card H6.Γ).factorization 2 := by
    rw [hQ, H6.card_gamma_factorization]
    norm_num
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq H6.Γ H6.sylowBorel (Sylow.ofCard Q hcard)
  have e := congrArg (fun R : Sylow 2 H6.Γ => (R : Subgroup H6.Γ)) hy
  simp only [Sylow.coe_subgroup_smul, H6.sylowBorel, Sylow.coe_ofCard] at e
  have hmemQ : ∀ t ∈ H6.borel, y * t * y⁻¹ ∈ Q := fun t ht => by
    rw [← e, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨t, ht, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  have hmemB : ∀ x ∈ Q, y⁻¹ * x * y ∈ H6.borel := fun x hx => by
    rw [← e, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨s, hs, hse⟩ := hx
    rw [MulAut.smul_def, MulAut.conj_apply] at hse
    rw [← hse, show y⁻¹ * (y * s * y⁻¹) * y = s by group]
    exact hs
  have h1 : y⁻¹ * c * y ∈ H6.borel := mem_borel_of_conj _ fun i => by
    have h4 := hmemB _ (hc _ (hmemQ _ (H6.bel_mem i)))
    convert h4 using 1
    group
  have := hmemQ _ h1
  rwa [show y * (y⁻¹ * c * y) * y⁻¹ = c by group] at this

section Transport

variable {S : Type*} [Group S]

theorem not_comm_of_alt5 (e : S ≃* alternatingGroup (Fin 5)) {a v : S} (ha : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hv : v ^ 2 = 1) (hv1 : v ≠ 1) : a * v ≠ v * a := by
  intro hc
  refine alt5_not_comm (a := e a) (v := e v) (by rw [← map_pow, ha, map_one])
    (fun h => ha1 (e.injective (h.trans (map_one e).symm))) (by rw [← map_pow, hv, map_one])
    (fun h => hv1 (e.injective (h.trans (map_one e).symm))) ?_
  rw [← map_mul, ← map_mul, hc]

theorem center_eq_bot_of_gl32 (e : S ≃* GL32) : Subgroup.center S = ⊥ := by
  set e' : S ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := e.trans (slEquivGL 3).symm
  rw [eq_bot_iff]
  intro z hz
  have h1 : e' z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e'.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) g']
  rw [center_sl32, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (e'.injective (h1.trans (map_one e').symm))

theorem isSimpleGroup_of_gl32 (e : S ≃* GL32) : IsSimpleGroup S :=
  (MulEquiv.isSimpleGroup_congr (e.trans (slEquivGL 3).symm)).mpr isSimpleGroup_sl32

theorem card_of_gl32 (e : S ≃* GL32) : Nat.card S = 168 := by
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.LieType.SteinbergBR.AutGL32.card_GL32

theorem mem_of_normalizes_of_gl32 (e : S ≃* GL32) {Q : Subgroup S} (hQ : Nat.card Q = 8) {c : S}
    (hc : ∀ x ∈ Q, c * x * c⁻¹ ∈ Q) : c ∈ Q := by
  set e' : S ≃* H6.Γ := e.trans (slEquivGL 3).symm
  have hQ' : Nat.card ↥(Q.map e'.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e'.injective, hQ]
  have h := mem_of_normalizes_of_card_eight hQ' (c := e' c) (by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨c * x * c⁻¹, hc x hx, by simp⟩)
  obtain ⟨c', hc', hcc'⟩ := h
  rwa [show c' = c from e'.injective hcc'] at hc'

end Transport

variable {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem card_eq_of_isSylowIn {P X : Subgroup D} (hP : IsSylowIn 2 P X) {a m : ℕ}
    (hX : Nat.card X = 2 ^ a * m) (hm : Odd m) : Nat.card P = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.2.1.exists_card_eq
  have hmul := Subgroup.relIndex_mul_card (H := P) (K := X)
  rw [inf_eq_left.mpr hP.1, hk, hX] at hmul
  have hodd : Odd (P.relIndex X) :=
    Nat.not_even_iff_odd.mp fun he => hP.2.2 (even_iff_two_dvd.mp he)
  rw [hk]
  have h1 : (2 ^ k * P.relIndex X).factorization 2 = (2 ^ a * m).factorization 2 := by
    rw [mul_comm, hmul]
  rw [Nat.factorization_mul (by positivity) hodd.pos.ne', Nat.factorization_mul (by positivity)
    hm.pos.ne'] at h1
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same] at h1
  rw [Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr h)),
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hm)
      (even_iff_two_dvd.mpr h))] at h1
  simp at h1
  rw [h1]

omit [Finite D] in
theorem eq_of_card_two {C : Subgroup D} (hC : Nat.card C = 2) {x y : C} (hx : x ≠ 1)
    (hy : y ≠ 1) : x = y := by
  obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hC
  exact (hz x hx).trans (hz y hy).symm

theorem le_normalizer_of_alt5 (h : IsGoldschmidtTriple G₁ G₂) {S : Subgroup D} [S.Normal]
    (e : ↥S ≃* alternatingGroup (Fin 5)) (hL : twoResidual G₁ ≤ S) :
    G₁ ≤ Subgroup.normalizer ((G₁ ⊓ G₂ ⊓ S : Subgroup D) : Set D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := G₁ ⊓ G₂ ⊓ S with hPdef
  set A := G₁ ⊓ S with hAdef
  have hPsyl : IsSylowIn 2 P S :=
    F6.isSylowIn_inf_of_isSubnormal F6.isSubnormal_top_of_normal (F6.isSylowTwoOf_inf_top h)
  have hP4 : Nat.card P = 4 := by
    have := card_eq_of_isSylowIn hPsyl (a := 2) (m := 15)
      (by rw [Nat.card_congr e.toEquiv, card_alt5]; norm_num) (by decide)
    simpa using this
  have hPA : P ≤ A := inf_le_inf_right S inf_le_left
  have hidx : P.relIndex A ≤ 3 := by
    have h1 : P.relIndex A = (G₁ ⊓ G₂).relIndex A := by
      rw [← Subgroup.inf_relIndex_right (G₁ ⊓ G₂) A]
      congr 1
      rw [hPdef, hAdef, ← inf_assoc, inf_assoc G₁ G₂ G₁, inf_comm G₂ G₁, ← inf_assoc, inf_idem]
    rw [h1, ← h.relIndex_inf_left]
    exact Subgroup.relIndex_le_of_le_right inf_le_left (by rw [h.relIndex_inf_left]; norm_num)
  obtain ⟨a, haG, ha3⟩ := F6.exists_orderOf_eq_three_left h
  have haL : a ∈ twoResidual G₁ := F6.mem_twoResidual_of_odd haG (by rw [ha3]; decide)
  have haA : a ∈ A := ⟨haG, hL haL⟩
  have haP : a ∉ P := fun haP => by
    obtain ⟨k, hk⟩ := hPsyl.2.1 ⟨a, haP⟩
    have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd := orderOf_dvd_of_pow_eq_one hk'
    rw [ha3] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hAcard : Nat.card A = P.relIndex A * 4 := by
    have := Subgroup.relIndex_mul_card (H := P) (K := A)
    rw [inf_eq_left.mpr hPA, hP4] at this
    exact this.symm
  have hidx2 : 2 ≤ P.relIndex A := by
    by_contra hlt
    have hpos : 0 < Nat.card A := Nat.card_pos
    have h1 : P.relIndex A = 1 := by omega
    exact haP (Subgroup.relIndex_eq_one.mp h1 haA)
  set P' : Subgroup ↥A := P.subgroupOf A with hP'def
  set C : Subgroup ↥A := P'.normalCore with hCdef
  have hCle : C ≤ P' := Subgroup.normalCore_le P'
  have hP'4 : Nat.card P' = 4 := by
    rw [hP'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv, hP4]
  have hCidx : C.index ≤ 6 := by
    have h1 := Subgroup.index_normalCore_le_factorial_index P'
    have h2 : P'.index = P.relIndex A := rfl
    rw [h2] at h1
    have h3 : (P.relIndex A).factorial ≤ (3 : ℕ).factorial := Nat.factorial_le hidx
    exact h1.trans (h3.trans (by decide))
  have hCmul := C.card_mul_index
  rw [hAcard] at hCmul
  have hCdvd : Nat.card C ∣ 4 := hP'4 ▸ Subgroup.card_dvd_of_le hCle
  have hC2 : 2 ≤ Nat.card C := by
    by_contra hlt
    have hC1 : Nat.card C ≤ 1 := by omega
    have h1 : P.relIndex A * 4 ≤ 1 * 6 := by
      rw [← hCmul]
      exact Nat.mul_le_mul hC1 hCidx
    omega
  have hAN : A ≤ Subgroup.normalizer (P : Set D) := by
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card C ∣ 2 ^ 2 by simpa using hCdvd)
      with ⟨j, hj, hCj⟩
    interval_cases j
    · rw [pow_zero] at hCj
      omega
    ·
      exfalso
      have hC : Nat.card C = 2 := by simpa using hCj
      obtain ⟨v, hv⟩ : ∃ v : C, v ≠ 1 := by
        by_contra hall
        push Not at hall
        have : Nat.card C ≤ 1 :=
          Finite.card_le_one_iff_subsingleton.mpr ⟨fun x y => (hall x).trans (hall y).symm⟩
        omega
      set a' : ↥A := ⟨a, haA⟩
      have hconj : a' * (v : ↥A) * a'⁻¹ = v := by
        have hm : a' * (v : ↥A) * a'⁻¹ ∈ C := (Subgroup.normalCore_normal P').conj_mem _ v.2 a'
        have hne : (⟨a' * (v : ↥A) * a'⁻¹, hm⟩ : C) ≠ 1 := by
          intro h1
          apply hv
          have h2 : a' * (v : ↥A) * a'⁻¹ = 1 := congrArg Subtype.val h1
          have h3 : (v : ↥A) = 1 := by
            have := congrArg (fun x => a'⁻¹ * x * a') h2
            simpa [mul_assoc] using this
          exact Subtype.ext h3
        exact congrArg Subtype.val (eq_of_card_two hC hne hv)
      have hv2 : v ^ 2 = 1 := by
        have := orderOf_dvd_natCard v
        rw [hC] at this
        exact orderOf_dvd_iff_pow_eq_one.mp this
      have hvS : ((v : ↥A) : D) ∈ S := ((v : ↥A)).2.2
      refine not_comm_of_alt5 e (a := ⟨a, hL haL⟩) (v := ⟨((v : ↥A) : D), hvS⟩) ?_ ?_ ?_ ?_ ?_
      · apply Subtype.ext
        simp [← ha3]
      · intro h1
        have : a = 1 := congrArg Subtype.val h1
        rw [this, orderOf_one] at ha3
        norm_num at ha3
      · apply Subtype.ext
        have := congrArg (fun x : C => ((x : ↥A) : D)) hv2
        simpa using this
      · intro h1
        apply hv
        apply Subtype.ext
        apply Subtype.ext
        have h2 := congrArg Subtype.val h1
        simpa using h2
      · apply Subtype.ext
        have h1 := congrArg Subtype.val hconj
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
        show a * ((v : ↥A) : D) = ((v : ↥A) : D) * a
        calc a * ((v : ↥A) : D) = (a * ((v : ↥A) : D) * a⁻¹) * a := by group
          _ = ((v : ↥A) : D) * a := by rw [h1]
    ·
      have hCeq : C = P' := Subgroup.eq_of_le_of_card_ge hCle (by rw [hP'4, hCj]; norm_num)
      have hn : P'.Normal := hCeq ▸ Subgroup.normalCore_normal P'
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPA).mp hn
  rw [← F6.inf_sup_twoResidual_left h]
  refine sup_le ?_ ((le_inf (twoResidual_le G₁) hL).trans hAN)
  exact F6.le_normalizer_inf_of_normal (G₁ ⊓ G₂)

theorem le_of_gl32 (h : IsGoldschmidtTriple G₁ G₂) {S : Subgroup D} [hSn : S.Normal]
    (e : ↥S ≃* GL32) (hL₁ : twoResidual G₁ ≤ S) : twoResidual G₂ ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hL₂
  have hX : IsSubnormal S ⊤ := F6.isSubnormal_top_of_normal
  obtain ⟨e₁, e₂, hsyl⟩ := ((F6.tfae_inf_le_pCoreOf h.symm hX).out 3 2).mp hL₂
  set P := G₁ ⊓ G₂ ⊓ S with hPdef
  have hP : G₂ ⊓ S = P := by rw [e₁, e₂, inf_comm G₂ G₁]
  have hG₂P : G₂ ≤ Subgroup.normalizer (P : Set D) := hP ▸ F6.le_normalizer_inf_of_normal G₂
  have hsyl' : IsSylowIn 2 P S := by rw [hPdef, inf_comm G₁ G₂]; exact hsyl
  have hP8 : Nat.card P = 8 := by
    have := card_eq_of_isSylowIn hsyl' (a := 3) (m := 21) (by rw [card_of_gl32 e]; norm_num)
      (by decide)
    simpa using this
  have hPS : P ≤ S := inf_le_right
  set P' : Subgroup ↥S := P.subgroupOf S with hP'def
  have hP'8 : Nat.card P' = 8 := by
    rw [hP'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv, hP8]
  have hcent : ∀ y ∈ G₂, Odd (orderOf y) → ∀ s ∈ S, y * s * y⁻¹ = s := by
    intro y hy hyo
    have hy3 : y ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (F6.orderOf_dvd_three_of_odd h.symm hy hyo)
    set α : MulAut ↥S := MulAut.conjNormal y with hαdef
    have hα3 : α ^ 3 = 1 := by rw [hαdef, ← map_pow, hy3, map_one]
    obtain ⟨c, hc⟩ := exists_conj_of_pow_three e α hα3
    have hcα : ∀ x : ↥S, c * x * c⁻¹ = α x := fun x => by rw [hc, MulAut.conj_apply]
    have hcP : c ∈ P' := mem_of_normalizes_of_gl32 e hP'8 fun x hx => by
      rw [hcα, Subgroup.mem_subgroupOf, hαdef, MulAut.conjNormal_apply]
      exact (Subgroup.mem_normalizer_iff.mp (hG₂P hy) x).mp hx
    have hc3 : c ^ 3 = 1 := by
      have hz : c ^ 3 ∈ Subgroup.center ↥S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 : MulAut.conj (c ^ 3) g = g := by
          rw [map_pow, ← hc, hα3]
          rfl
        rw [MulAut.conj_apply] at h1
        calc g * c ^ 3 = (c ^ 3 * g * (c ^ 3)⁻¹)⁻¹⁻¹ * c ^ 3 := by rw [h1, inv_inv]
          _ = c ^ 3 * g := by group
      rw [center_eq_bot_of_gl32 e, Subgroup.mem_bot] at hz
      exact hz
    have hc1 : c = 1 := by
      have hP'2 : IsPGroup 2 P' := by
        have := hsyl'.2.1
        exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hPS).symm
      obtain ⟨k, hk⟩ := hP'2 ⟨c, hcP⟩
      have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 : orderOf c ∣ Nat.gcd 3 (2 ^ k) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one hk')
      have h2 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
      rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
      exact h1
    intro s hs
    have h1 := hcα ⟨s, hs⟩
    rw [hc1, one_mul, inv_one, mul_one, hαdef] at h1
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h2
    exact h2.symm
  have hL₂C : twoResidual G₂ ≤ Subgroup.centralizer (S : Set D) := by
    rw [F6.twoResidual_eq_oTwoUpper]
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨hyG, hyo⟩ := hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := hcent y hyG hyo s hs
    calc s * y = (y * s * y⁻¹) * y := by rw [h1]
      _ = y * s := by group
  have hN : (⊤ : Subgroup D) ≤ Subgroup.normalizer (twoResidual G₁ : Set D) := by
    rw [← h.gen]
    refine sup_le (le_normalizer_twoResidual G₁) ?_
    rw [← F6.inf_sup_twoResidual_right h]
    refine sup_le (inf_le_left.trans (le_normalizer_twoResidual G₁)) ?_
    exact (hL₂C.trans (Subgroup.centralizer_le hL₁)).trans (Subgroup.centralizer_le_normalizer _)
  have := isSimpleGroup_of_gl32 e
  have hn : ((twoResidual G₁).subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL₁).mpr (le_top.trans hN)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((twoResidual G₁).subgroupOf S) with hb | ht
  · obtain ⟨x, hx, h3⟩ := F6.exists_orderOf_eq_three_left h
    have hxL := F6.mem_twoResidual_of_odd hx (by rw [h3]; decide)
    have h1 : (⟨x, hL₁ hxL⟩ : ↥S) ∈ (twoResidual G₁).subgroupOf S := hxL
    rw [hb, Subgroup.mem_bot] at h1
    have h2 : x = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at h3
    norm_num at h3
  · have hSL : S ≤ twoResidual G₁ := fun s hs => by
      have h1 : (⟨s, hs⟩ : ↥S) ∈ (twoResidual G₁).subgroupOf S := ht ▸ Subgroup.mem_top _
      exact h1
    have hdvd : Nat.card S ∣ Nat.card G₁ :=
      Subgroup.card_dvd_of_le (hSL.trans (twoResidual_le G₁))
    rw [card_of_gl32 e, F6.card_left h] at hdvd
    obtain ⟨a, ha⟩ := F6.exists_card_inf_eq h
    rw [ha] at hdvd
    have h7 : 7 ∣ 3 * 2 ^ a := (show 7 ∣ 168 by norm_num).trans hdvd
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7 with h | h
    · norm_num at h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h) (by norm_num)

theorem gl32_of_amalgam (h : IsGoldschmidtTriple G₁ G₂) (hO : Open.pCore 2 D = ⊥)
    {S : Subgroup D} [S.Normal]
    (hS : Nonempty (↥S ≃* alternatingGroup (Fin 5)) ∨ Nonempty (↥S ≃* GL32))
    (hL : twoResidual G₁ ≤ S ∨ twoResidual G₂ ≤ S) :
    Nonempty (↥S ≃* GL32) ∧ twoResidual G₁ ≤ S ∧ twoResidual G₂ ≤ S := by
  rcases hS with hS5 | hS3
  · exfalso
    obtain ⟨e⟩ := hS5
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hX : IsSubnormal S ⊤ := F6.isSubnormal_top_of_normal
    have key : ∀ {H₁ H₂ : Subgroup D}, IsGoldschmidtTriple H₁ H₂ → twoResidual H₁ ≤ S →
        (⊤ : Subgroup D) ≤ Subgroup.normalizer ((H₁ ⊓ H₂ ⊓ S : Subgroup D) : Set D) := by
      intro H₁ H₂ hh hL₁
      rw [← hh.gen]
      refine sup_le (le_normalizer_of_alt5 hh e hL₁) ?_
      by_cases hL₂ : twoResidual H₂ ≤ S
      · have := le_normalizer_of_alt5 hh.symm e hL₂
        rwa [inf_comm H₂ H₁] at this
      · obtain ⟨e₁, e₂, -⟩ := ((F6.tfae_inf_le_pCoreOf hh.symm hX).out 3 2).mp hL₂
        have hP : H₂ ⊓ S = H₁ ⊓ H₂ ⊓ S := by rw [e₁, e₂, inf_comm H₂ H₁]
        rw [← hP]
        exact F6.le_normalizer_inf_of_normal H₂
    have hNt : (⊤ : Subgroup D) ≤ Subgroup.normalizer ((G₁ ⊓ G₂ ⊓ S : Subgroup D) : Set D) := by
      rcases hL with h1 | h2
      · exact key h h1
      · have := key h.symm h2
        rwa [inf_comm G₂ G₁] at this
    have hPn : (G₁ ⊓ G₂ ⊓ S).Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hNt)
    have hle : G₁ ⊓ G₂ ⊓ S ≤ Open.pCore 2 D := h.le_pCore_of_normal_le_inf inf_le_left
    rw [hO, le_bot_iff] at hle
    have hPsyl : IsSylowIn 2 (G₁ ⊓ G₂ ⊓ S) S :=
      F6.isSylowIn_inf_of_isSubnormal hX (F6.isSylowTwoOf_inf_top h)
    have hP4 := card_eq_of_isSylowIn hPsyl (a := 2) (m := 15)
      (by rw [Nat.card_congr e.toEquiv, card_alt5]; norm_num) (by decide)
    rw [hle, Subgroup.card_bot] at hP4
    norm_num at hP4
  · obtain ⟨e⟩ := hS3
    refine ⟨⟨e⟩, ?_⟩
    rcases hL with h1 | h2
    · exact ⟨h1, le_of_gl32 h e h1⟩
    · exact ⟨le_of_gl32 h.symm e h2, h2⟩

end CFSG.Quasithin.H13.L32A.G58
