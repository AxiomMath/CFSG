module

public import CFSG.Quasithin.Vol2.KGFact12614U35a
public import CFSG.Quasithin.Vol2.KGFact12614Proof
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Cen

public section

namespace CFSG.Quasithin.H13.U35A6

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts
open scoped commutatorElement

variable {K : Type} [Field K]

section GroupSteps

theorem isPerfect_alt6 : Group.IsPerfect ↥(alternatingGroup (Fin 6)) := by
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥(alternatingGroup (Fin 6))) with
    h | h
  · exfalso
    let a : ↥(alternatingGroup (Fin 6)) := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
      simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]⟩
    let b : ↥(alternatingGroup (Fin 6)) := ⟨Equiv.swap 0 1 * Equiv.swap 0 3, by
      simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]⟩
    have hab : a * b ≠ b * a := by decide
    have : ⁅a, b⁆ ∈ commutator ↥(alternatingGroup (Fin 6)) := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact hab this
  · exact h

theorem exists_pow_involution {G : Type*} [Group G] {t : G} {n : ℕ} (ht : t ^ 2 ^ n = 1)
    (ht1 : t ≠ 1) : ∃ k : ℕ, (t ^ k) ^ 2 = 1 ∧ t ^ k ≠ 1 := by
  have hdvd : orderOf t ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one ht
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm
    exact ht1 hm
  refine ⟨2 ^ (m - 1), ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm0), ← hm]
    exact pow_orderOf_eq_one t
  · refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hm]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem factorization_three {m : ℕ} (hm : ¬ 3 ∣ m) : (3 ^ 2 * m).factorization 3 = 2 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 3)
  rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd hm]
  rfl

theorem exists_conj_mem {P : Type} [Group P] [Finite P] (hcard : Nat.card P = 126000)
    (H : Subgroup P) (hH : CFSG.Quasithin.IsAlt 6 ↥H) {x₁ x₂ : P} (h12 : x₁ * x₂ = x₂ * x₁)
    (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) :
    ∃ g : P, x₁ ∈ H.map (MulAut.conj g).toMonoidHom ∧ x₂ ∈ H.map (MulAut.conj g).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E₀ := Subgroup.closure ({x₁, x₂} : Set P) with hE₀def
  have hpair : ({x₁, x₂} : Set P).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact Commute.refl _
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact h12
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact h12.symm
    · rw [Set.mem_singleton_iff] at ha hb
      subst ha hb
      exact Commute.refl _
  have hcomm : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
    intro a ha b hb
    have := (Subgroup.isMulCommutative_closure hpair).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have key : ∀ y ∈ E₀, y ^ 3 = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | hz
      · exact h1
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact h2
    | one => exact one_pow 3
    | mul a b ha hb iha ihb => rw [(Commute.mul_pow (hcomm a ha b hb) 3), iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hE₀ : IsPGroup 3 ↥E₀ := fun y =>
    ⟨1, Subtype.ext (by rw [pow_one]; simpa using key y y.2)⟩
  obtain ⟨S₁, hS₁⟩ := hE₀.exists_le_sylow
  obtain ⟨e⟩ := hH
  have hcH : Nat.card ↥H = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  obtain ⟨SH⟩ : Nonempty (Sylow 3 ↥H) := inferInstance
  have hSH : Nat.card ↥(SH : Subgroup ↥H) = 9 := by
    rw [Sylow.card_eq_multiplicity, hcH, show (360 : ℕ) = 3 ^ 2 * 40 by norm_num,
      factorization_three (by norm_num)]
    norm_num
  set E := (SH : Subgroup ↥H).map H.subtype with hEdef
  have hE : Nat.card ↥E = 3 ^ (Nat.card P).factorization 3 := by
    rw [hEdef, Subgroup.card_map_of_injective H.subtype_injective, hSH, hcard,
      show (126000 : ℕ) = 3 ^ 2 * 14000 by norm_num, factorization_three (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (Sylow.ofCard E hE) S₁
  have hmem : ∀ x ∈ E₀, x ∈ H.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    have hx1 : x ∈ ((g • Sylow.ofCard E hE : Sylow 3 P) : Subgroup P) := by
      rw [hg]
      exact hS₁ hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx1
    obtain ⟨y, hy, rfl⟩ := hx1
    have hyE : y ∈ E := hy
    obtain ⟨z, -, rfl⟩ := hyE
    exact ⟨z, z.2, rfl⟩
  exact ⟨g, hmem _ (Subgroup.subset_closure (Set.mem_insert _ _)),
    hmem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))⟩

end GroupSteps

theorem center_eq_bot_of_simple {X : Type*} [Group X] (hs : IsSimpleGroup X) {a b : X}
    (hab : a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have ha : a ∈ Subgroup.center X := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

section Model

variable (h : UnitaryFieldData 5 1 K)

theorem false_of_inv_centralizes {s : unitaryPSU h 3}
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) {L : Subgroup (unitaryPSU h 3)}
    (hL : CFSG.Quasithin.IsAlt 6 ↥L) (hLs : ∀ x ∈ L, x * s = s * x) : False := by
  have := h.finite
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hq : 2 < 5 ^ 1 := by norm_num
  have hK : Nat.card K = 5 ^ 2 := h.card
  let eZ : (↥(unitarySU 5 1 K 3) ⧸ Subgroup.center ↥(unitarySU 5 1 K 3)) ≃* unitaryPSU h 3 :=
    QuotientGroup.quotientMulEquivOfEq (center_unitarySU_three (h := h) hq)
  have hdet : ∀ x ∈ unitarySU 5 1 K 3, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    fun x hx => ((mem_unitarySU_iff h).1 hx).1
  have hZ : Nat.card (Subgroup.center ↥(unitarySU 5 1 K 3)) ∣ 3 := by
    rw [center_unitarySU_three (h := h) hq, card_unitaryScalars h (by norm_num)]
    norm_num
  set t := eZ.symm s with htdef
  have ht2 : t ^ 2 = 1 := by rw [htdef, ← map_pow, hs2, map_one]
  have ht1 : t ≠ 1 := fun h1 => hs1 (by rw [← eZ.apply_symm_apply s, ← htdef, h1, map_one])
  obtain ⟨e⟩ := hL
  set L' := L.map eZ.symm.toMonoidHom with hL'def
  let eL' : ↥L' ≃* ↥(alternatingGroup (Fin 6)) :=
    (L.equivMapOfInjective _ eZ.symm.injective).symm.trans e
  have := isPerfect_alt6
  have : Group.IsPerfect ↥L' :=
    Group.IsPerfect.ofSurjective (f := eL'.symm.toMonoidHom) eL'.symm.surjective
  have hc : Nat.card ↥L' = 360 := by
    rw [Nat.card_congr eL'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hL' : L' ≠ ⊥ := fun h1 => by
    rw [h1, Subgroup.card_bot] at hc
    norm_num at hc
  have hLt : ∀ x ∈ L', x * t = t * x := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, htdef, ← map_mul, hLs y hy]
  have := CFSG.Quasithin.A312U3.card_perfect_of_le_centralizer_K (p := 5) (by norm_num) hK hdet
    hZ ht2 ht1 L' hL' hLt
  rw [hc] at this
  norm_num at this

end Model

section Main

variable (h : UnitaryFieldData 5 1 K)

theorem model_eq_one (hcard : Nat.card (unitaryPSU h 3) = 126000)
    (hZ : Subgroup.center (unitaryPSU h 3) = ⊥) (α : MulAut (unitaryPSU h 3))
    (H : Subgroup (unitaryPSU h 3)) (hH : CFSG.Quasithin.IsAlt 6 ↥H)
    (hfix : ∀ x ∈ H, α x = x) (hpow : ∃ n : ℕ, α ^ 2 ^ n = 1) : α = 1 := by
  classical
  have := h.finite
  obtain ⟨n, hn⟩ := hpow
  obtain ⟨ω, hω3, hω1⟩ : ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fintype K := Fintype.ofFinite K
    have hU : Nat.card Kˣ = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, h.card]
      norm_num
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hU]; norm_num)
    refine ⟨(u : K), ?_, ?_⟩
    · have : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
      have := congrArg Units.val this
      simpa using this
    · intro h1
      have : u = 1 := Units.ext h1
      rw [this, orderOf_one] at hu
      norm_num at hu
  obtain ⟨g, hg1, hg2⟩ := exists_conj_mem hcard H hH (x_comm h hω3) (x1_pow h hω3) (x2_pow h)
  set β := MulAut.conj g * α * (MulAut.conj g)⁻¹ with hβ
  have hβfix : ∀ x ∈ H.map (MulAut.conj g).toMonoidHom, β x = x := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [hβ, MulAut.mul_apply, MulEquiv.coe_toMonoidHom, MulAut.inv_apply,
      MulEquiv.symm_apply_apply, hfix y hy]
  have hβn : β ^ 2 ^ n = 1 := by rw [hβ, conj_pow, hn, mul_one, mul_inv_cancel]
  obtain ⟨B, σ, hBσ⟩ := exists_psuConj_mul_psuField (h := h) (by norm_num) β
  have hσω : σ ω = ω := sigma_eq_of_fix h hω3 B σ (by rw [← hBσ]; exact hβfix _ hg1)
    (by rw [← hBσ]; exact hβfix _ hg2)
  have hσ1 : σ = 1 := eq_one_of_fix_omega h hω3 hω1 hσω
  rw [hσ1, map_one, mul_one] at hBσ
  obtain ⟨g', hg'⟩ := exists_conj_of_pow h B (by rw [← hBσ]; exact hβn)
  set t : unitaryPSU h 3 := (g' : unitaryPSU h 3) with htdef
  have hβt : β = MulAut.conj t := hBσ.trans hg'
  have ht : t ^ 2 ^ n = 1 := by
    have h1 : MulAut.conj (t ^ 2 ^ n) = 1 := by rw [map_pow, ← hβt, hβn]
    have h2 : t ^ 2 ^ n ∈ Subgroup.center (unitaryPSU h 3) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut (unitaryPSU h 3) => φ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * t ^ 2 ^ n = (t ^ 2 ^ n * y * (t ^ 2 ^ n)⁻¹) * t ^ 2 ^ n := by rw [this]
        _ = t ^ 2 ^ n * y := by group
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  by_contra hα
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hα
    calc α = (MulAut.conj g)⁻¹ * β * MulAut.conj g := by rw [hβ]; group
      _ = 1 := by rw [h1, mul_one, inv_mul_cancel]
  have ht1 : t ≠ 1 := fun h1 => hβ1 (by rw [hβt, h1, map_one])
  obtain ⟨k, hk2, hk1⟩ := exists_pow_involution ht ht1
  refine false_of_inv_centralizes h hk2 hk1 (L := H.map (MulAut.conj g).toMonoidHom) ?_ ?_
  · obtain ⟨e⟩ := hH
    exact ⟨(H.equivMapOfInjective _ (MulAut.conj g).injective).symm.trans e⟩
  · intro x hx
    have h1 : t * x * t⁻¹ = x := by
      have := hβfix x hx
      rwa [hβt, MulAut.conj_apply] at this
    have h2 : Commute x t := by
      show x * t = t * x
      calc x * t = (t * x * t⁻¹) * t := by rw [h1]
        _ = t * x := by group
    exact (h2.pow_right k).eq

end Main

end CFSG.Quasithin.H13.U35A6

namespace CFSG.Quasithin.H13

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts

theorem factU35A6Cent_holds : FactU35A6Cent := by
  intro Q _ _ hQ α H hH hfix hpow
  obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := hQ
  have h : UnitaryFieldData 5 1 K := ⟨Nat.prime_five, le_rfl, by rw [hcard]; norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let f : Q ≃* unitaryPSU h 3 := e.trans (unitaryPSUEquiv h (by norm_num)).symm
  have hcardP : Nat.card (unitaryPSU h 3) = 126000 := by
    have h1 := CFSG.Quasithin.card_statedProj_statedSU_three_mul_gcd (K := K) Nat.prime_five
      le_rfl hcard
    rw [Nat.card_congr (unitaryPSUEquiv h (n := 3) (by norm_num)).toEquiv]
    rw [show Nat.gcd 3 (5 ^ 1 + 1) = 3 by norm_num,
      show (5 ^ 1) ^ 3 * (((5 ^ 1) ^ 2 - 1) * ((5 ^ 1) ^ 3 + 1)) = 378000 by norm_num] at h1
    omega
  have hZP : Subgroup.center (unitaryPSU h 3) = ⊥ := by
    obtain ⟨⟨-, hs, a, b, hab⟩, -⟩ :=
      CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := 5) (f := 1)
        hcard le_rfl (by decide)
    let eS := suCenterEquiv h (by norm_num : 2 < 5 ^ 1)
    have hZ := U35A6.center_eq_bot_of_simple hs hab
    rw [eq_bot_iff]
    intro z hz
    have h1 : eS.symm z ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      apply eS.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz]
    rw [hZ, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, ← eS.apply_symm_apply z, h1, map_one]
  set α' : MulAut (unitaryPSU h 3) := MulAut.congr f α with hα'
  have h1 : α' = 1 := by
    refine U35A6.model_eq_one h hcardP hZP α' (H.map f.toMonoidHom) ?_ ?_ ?_
    · obtain ⟨eH⟩ := hH
      exact ⟨(H.equivMapOfInjective _ f.injective).symm.trans eH⟩
    · rintro _ ⟨y, hy, rfl⟩
      simp [hα', hfix y hy]
    · obtain ⟨n, hn⟩ := hpow
      exact ⟨n, by rw [hα', ← map_pow, hn, map_one]⟩
  have h2 : α = (MulAut.congr f).symm α' := by rw [hα', MulEquiv.symm_apply_apply]
  rw [h2, h1, map_one]

theorem factKv12614_of_list
    (hList : QuasithinUnique.Vol2Native.A312ListFactsCat) :
    FactKv12614 :=
  factKv12614_of hList factU35A6Cent_holds

end CFSG.Quasithin.H13
