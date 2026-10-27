module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Linear
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15423

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F6 Matrix
open scoped commutatorElement

namespace L15422

section AltSix

open Equiv

private def dihR : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5

private def dihS : Perm (Fin 6) := swap 0 2 * swap 4 5

private def d8Finset : Finset (Perm (Fin 6)) :=
  {1, dihR, dihR ^ 2, dihR ^ 3, dihS, dihR * dihS, dihR ^ 2 * dihS, dihR ^ 3 * dihS}

private theorem d8_mul : ∀ a ∈ d8Finset, ∀ b ∈ d8Finset, a * b ∈ d8Finset := by decide +kernel

private theorem d8_one : (1 : Perm (Fin 6)) ∈ d8Finset := by decide +kernel

private theorem d8_inv : ∀ a ∈ d8Finset, a⁻¹ ∈ d8Finset := by decide +kernel

private theorem d8_sign : ∀ a ∈ d8Finset, Perm.sign a = 1 := by decide +kernel

private theorem d8_card : d8Finset.card = 8 := by decide +kernel

private theorem dihR_mem : dihR ∈ d8Finset := by decide +kernel

private theorem dihS_mem : dihS ∈ d8Finset := by decide +kernel

private theorem dihS_sq : dihS ^ 2 = 1 := by decide +kernel

private theorem dihR_mul_dihS : dihR * dihS ≠ dihS * dihR := by decide +kernel

private def d8Perm : Subgroup (Perm (Fin 6)) where
  carrier := ↑d8Finset
  mul_mem' ha hb := d8_mul _ ha _ hb
  one_mem' := d8_one
  inv_mem' ha := d8_inv _ ha

private theorem d8Perm_le : d8Perm ≤ alternatingGroup (Fin 6) := fun _ ha =>
  Perm.mem_alternatingGroup.mpr (d8_sign _ ha)

theorem exists_noncentral_involution_alt (P : Subgroup (alternatingGroup (Fin 6)))
    (hP : Nat.card P = 8) : ∃ b ∈ P, b ^ 2 = 1 ∧ ∃ a ∈ P, a * b ≠ b * a := by
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hsyl : ∀ U : Subgroup (alternatingGroup (Fin 6)), Nat.card U = 8 →
      CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
    intro U hU
    refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [hU]; norm_num), ?_⟩
    change ¬ 2 ∣ U.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h := Subgroup.index_mul_card U
    rw [hU, hcard] at h
    omega
  have hD : Nat.card (d8Perm.subgroupOf (alternatingGroup (Fin 6))) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d8Perm_le).toEquiv]
    exact (Nat.card_eq_finsetCard d8Finset).trans d8_card
  obtain ⟨h, -, hh⟩ := A4.exists_conj_of_isSylowTwoOf (hsyl P hP) (hsyl _ hD)
  obtain ⟨a, hadef⟩ : ∃ a : alternatingGroup (Fin 6), a = ⟨dihR, d8Perm_le dihR_mem⟩ :=
    ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : alternatingGroup (Fin 6), b = ⟨dihS, d8Perm_le dihS_mem⟩ :=
    ⟨_, rfl⟩
  have ha : a ∈ d8Perm.subgroupOf (alternatingGroup (Fin 6)) := by
    rw [hadef]
    exact Subgroup.mem_subgroupOf.mpr dihR_mem
  have hb : b ∈ d8Perm.subgroupOf (alternatingGroup (Fin 6)) := by
    rw [hbdef]
    exact Subgroup.mem_subgroupOf.mpr dihS_mem
  refine ⟨h⁻¹ * b * h, (hh b).mp hb, ?_, h⁻¹ * a * h, (hh a).mp ha, fun heq => ?_⟩
  · have hb2 : b ^ 2 = 1 := by rw [hbdef]; exact Subtype.ext dihS_sq
    calc (h⁻¹ * b * h) ^ 2 = h⁻¹ * b ^ 2 * h := by rw [sq, sq]; group
      _ = 1 := by rw [hb2, mul_one, inv_mul_cancel]
  · have hab : a * b = b * a := by
      have e1 : a * b = h * ((h⁻¹ * a * h) * (h⁻¹ * b * h)) * h⁻¹ := by group
      have e2 : b * a = h * ((h⁻¹ * b * h) * (h⁻¹ * a * h)) * h⁻¹ := by group
      rw [e1, e2, heq]
    have := congrArg Subtype.val hab
    rw [hadef, hbdef] at this
    exact dihR_mul_dihS this

theorem exists_noncentral_involution {X : Type*} [Group X] (ψ : X ≃* alternatingGroup (Fin 6))
    (P : Subgroup X) (hP : Nat.card P = 8) : ∃ b ∈ P, b ^ 2 = 1 ∧ ∃ a ∈ P, a * b ≠ b * a := by
  have hP' : Nat.card (P.map ψ.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hP]
  obtain ⟨b, hb, hb2, a, ha, hab⟩ := exists_noncentral_involution_alt _ hP'
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
  refine ⟨x, hx, ?_, y, hy, fun hxy => hab ?_⟩
  · apply ψ.injective
    simpa using hb2
  · simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hxy]

end AltSix

section SL

variable {F : Type*} [Field F]

theorem sl2_eq_one_or_neg_one_of_sq (h2 : (2 : F) ≠ 0) {A : SpecialLinearGroup (Fin 2) F}
    (hA : A ^ 2 = 1) : A = 1 ∨ A = -1 := by
  have hA' : (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
      Matrix.scalar (Fin 2) 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← sq, hA, Matrix.SpecialLinearGroup.coe_one,
      map_one]
  by_cases hns : ∀ t : F, (A : Matrix (Fin 2) (Fin 2) F) ≠ Matrix.scalar (Fin 2) t
  · exfalso
    obtain ⟨h1, -⟩ := sq_eq_neg_one_of_sq_eq_scalar A.2 hA' hns
    rw [hA', map_one] at h1
    have h00 := congrFun (congrFun h1 0) 0
    simp only [Matrix.one_apply_eq, Matrix.neg_apply] at h00
    apply h2
    linear_combination h00
  · push Not at hns
    obtain ⟨t, ht⟩ := hns
    have hdet := A.2
    rw [ht, Matrix.det_fin_two] at hdet
    simp at hdet
    have : (t - 1) * (t + 1) = 0 := by linear_combination hdet
    rcases mul_eq_zero.mp this with h | h
    · left
      apply Subtype.ext
      rw [ht, Matrix.SpecialLinearGroup.coe_one, sub_eq_zero.mp h, map_one]
    · right
      apply Subtype.ext
      rw [ht, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
        eq_neg_of_add_eq_zero_left h, map_neg, map_one]

theorem sl2_mem_center_iff (h2 : (2 : F) ≠ 0) {A : SpecialLinearGroup (Fin 2) F} :
    A ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ↔ A = 1 ∨ A = -1 := by
  constructor
  · intro hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    apply sl2_eq_one_or_neg_one_of_sq h2
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrA, ← map_pow, Matrix.SpecialLinearGroup.coe_one]
    simp only [Fintype.card_fin] at hr
    rw [hr, map_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · rw [Subgroup.mem_center_iff]
      intro g
      simp

end SL

section Commutator

variable {G : Type*} [Group G]

theorem commutatorElement_mul_center_left {a z : G} (hz : z ∈ Subgroup.center G) (x : G) :
    ⁅a * z, x⁆ = ⁅a, x⁆ := by
  have hz' : z * x * z⁻¹ = x := by
    rw [← (Subgroup.mem_center_iff.mp hz x)]
    group
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * x * (a * z)⁻¹ * x⁻¹ = a * (z * x * z⁻¹) * a⁻¹ * x⁻¹ := by group
    _ = a * x * a⁻¹ * x⁻¹ := by rw [hz']

theorem commutatorElement_mul_center_right {b w : G} (hw : w ∈ Subgroup.center G) (y : G) :
    ⁅y, b * w⁆ = ⁅y, b⁆ := by
  have hw' : w * y⁻¹ * w⁻¹ = y⁻¹ := by
    rw [← (Subgroup.mem_center_iff.mp hw y⁻¹)]
    group
  rw [commutatorElement_def, commutatorElement_def]
  calc y * (b * w) * y⁻¹ * (b * w)⁻¹ = y * b * (w * y⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = y * b * y⁻¹ * b⁻¹ := by rw [hw']

end Commutator

section Layer

variable {H : Type*} [Group H] [Finite H]

theorem mem_of_isPGroup_zpowers {Q N : Subgroup H} [hQ : Q.Normal] (hQN : IsSylowIn 2 Q N)
    {n : H} (hn : n ∈ N) (h2 : IsPGroup 2 (Subgroup.zpowers n)) : n ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Q ⊔ Subgroup.zpowers n
  have hM2 : IsPGroup 2 M := IsPGroup.to_sup_of_normal_left hQN.isPGroup h2
  have hMN : M ≤ N := sup_le hQN.le (Subgroup.zpowers_le.mpr hn)
  have hQM : Q ≤ M := le_sup_left
  have hmul := Subgroup.relIndex_mul_relIndex Q M N hQM hMN
  have hodd : ¬ 2 ∣ Q.relIndex M := fun h =>
    hQN.not_dvd_relIndex (hmul ▸ Dvd.dvd.mul_right h _)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hM2
  have hdvd : Q.relIndex M ∣ 2 ^ a := ha ▸ Subgroup.relIndex_dvd_card Q M
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hb0 : b = 0 := by
    by_contra hb0
    apply hodd
    rw [hb]
    exact dvd_pow_self 2 hb0
  have h1 : Q.relIndex M = 1 := by rw [hb, hb0, pow_zero]
  exact (Subgroup.relIndex_eq_one.mp h1) (le_sup_right (a := Q) (Subgroup.mem_zpowers n))

open CFSG.LocalAnalysis.ComponentInitial in
theorem inf_eq_bot_of_psl_nine
    {N K T₀ : Subgroup H} [hN : N.Normal]
    (hQN : IsSylowIn 2 (Open.pCore 2 H) N) (hKn : K.Normal) {N₀ : Subgroup (H ⧸ N)}
    (hKmap : K.map (QuotientGroup.mk' N) = N₀) (hKN : K ⊓ N ≤ Open.pCore 2 H)
    (hKC : K ≤ Subgroup.centralizer (Open.pCore 2 H : Set H)) (hKp : ⁅K, K⁆ = K)
    (hNK : N ≤ Subgroup.centralizer (K : Set H)) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 9) (e : ↥N₀ ≃* ProjectiveSpecialLinearGroup (Fin 2) F)
    (hT₀ : IsPGroup 2 T₀) (hT₀i : ¬ 2 ∣ T₀.index) {u : H} (huT : u ∈ T₀)
    (huc : ∀ t ∈ T₀, t * u = u * t) (hu2 : u ^ 2 = 1)
    (huN₀ : QuotientGroup.mk' N u ∈ N₀) (hu1 : QuotientGroup.mk' N u ≠ 1) : K ⊓ N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP F 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2) (by rw [hF]; norm_num)
  have h2 : (2 : F) ≠ 0 := by
    have : ((2 : ℕ) : F) ≠ 0 := fun h => by
      have := (CharP.cast_eq_zero_iff F 3 2).mp h
      omega
    exact_mod_cast this
  set π := QuotientGroup.mk' N
  set Q := Open.pCore 2 H
  have hQn : Q.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  obtain ⟨ψ⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism F hF
  have hπK1 : ∀ x : K, π x ∈ N₀ := fun x => hKmap ▸ Subgroup.mem_map_of_mem π x.2
  let πK : K →* N₀ := (π.comp K.subtype).codRestrict N₀ hπK1
  have hπK : Function.Surjective πK := by
    rintro ⟨y, hy⟩
    rw [← hKmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ∀ x : K, x ∈ πK.ker ↔ (x : H) ∈ N := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hkerc : πK.ker ≤ Subgroup.center K := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp (hKC y.2)) x (hKN ⟨x.2, (hker x).mp hx⟩)).symm
  have hker2 : IsPGroup 2 πK.ker := by
    intro x
    obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := H))
      ⟨(x : K), hKN ⟨(x : K).2, (hker x).mp x.2⟩⟩
    exact ⟨j, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hj))⟩
  have hker3 : ¬ 3 ∣ Nat.card πK.ker := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hker2
    rw [hm]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  let ρ : SpecialLinearGroup (Fin 2) F →* N₀ :=
    e.symm.toMonoidHom.comp (CFSG.GorensteinWalter.psl2QuotientMap F)
  obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift (p := 3) hπK hkerc
    hker3 ρ
  have hρ'π : ∀ A, πK (ρ' A) = ρ A := fun A => congrArg (fun f => f A) hρ'
  have hρ's : Function.Surjective ρ' := by
    have hdec : ∀ x : K, ∃ A, ∃ z ∈ πK.ker, x = ρ' A * z := by
      intro x
      obtain ⟨A, hA⟩ : ∃ A, ρ A = πK x := by
        obtain ⟨A, hA⟩ := CFSG.GorensteinWalter.psl2QuotientMap_surjective (e (πK x))
        exact ⟨A, by simp [ρ, hA]⟩
      refine ⟨A, (ρ' A)⁻¹ * x, ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρ'π, hA, inv_mul_cancel]
    have hperf : commutator K = ⊤ := by
      apply Subgroup.map_injective K.subtype_injective
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype, hKp]
    have hle : commutator K ≤ ρ'.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨A, z, hz, rfl⟩ := hdec x
      obtain ⟨B, w, hw, rfl⟩ := hdec y
      refine ⟨⁅A, B⁆, ?_⟩
      rw [map_commutatorElement, commutatorElement_mul_center_left (hkerc hz),
        commutatorElement_mul_center_right (hkerc hw)]
    intro x
    exact hle (hperf ▸ Subgroup.mem_top x)
  have hkerρ : ∀ A, ρ A = 1 ↔ A = 1 ∨ A = -1 := by
    intro A
    rw [← sl2_mem_center_iff h2]
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff A
  by_cases hc : ρ' (-1) = 1
  ·
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨A, hA⟩ := hρ's ⟨x, hx.1⟩
    have hAk : ρ A = 1 := by
      rw [← hρ'π, hA]
      exact (hker _).mpr hx.2
    rcases (hkerρ A).mp hAk with rfl | rfl
    · rw [map_one] at hA
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hA).symm
    · rw [hc] at hA
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hA).symm
  exfalso
  have hρ'i : Function.Injective ρ' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro A hA
    have hAk : ρ A = 1 := by rw [← hρ'π, MonoidHom.mem_ker.mp hA, map_one]
    rcases (hkerρ A).mp hAk with h | h
    · exact Subgroup.mem_bot.mpr h
    · exact absurd (by rw [← h]; exact MonoidHom.mem_ker.mp hA) hc
  have hinv : ∀ y : K, y ^ 2 = 1 → y = 1 ∨ y = ρ' (-1) := by
    intro y hy
    obtain ⟨A, rfl⟩ := hρ's y
    have : A ^ 2 = 1 := hρ'i (by rw [map_pow, hy, map_one])
    rcases sl2_eq_one_or_neg_one_of_sq h2 this with rfl | rfl
    · exact Or.inl (map_one ρ')
    · exact Or.inr rfl
  have hkerK : ∀ y : K, (y : H) ∈ N → y = 1 ∨ y = ρ' (-1) := by
    intro y hy
    obtain ⟨A, rfl⟩ := hρ's y
    have hAk : ρ A = 1 := by
      rw [← hρ'π]
      exact (hker _).mpr hy
    rcases (hkerρ A).mp hAk with rfl | rfl
    · exact Or.inl (map_one ρ')
    · exact Or.inr rfl
  have hc2 : ρ' (-1) * ρ' (-1) = 1 := by
    rw [← map_mul, show (-1 : SpecialLinearGroup (Fin 2) F) * -1 = 1 by simp, map_one]
  obtain ⟨k, hkK, hk⟩ : π u ∈ K.map π := hKmap ▸ huN₀
  have hn : k⁻¹ * u ∈ N := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    change π (k⁻¹ * u) = 1
    rw [map_mul, map_inv, hk, inv_mul_cancel]
  have hnk : ∀ y ∈ K, (k⁻¹ * u) * y = y * (k⁻¹ * u) := fun y hy =>
    ((Subgroup.mem_centralizer_iff.mp (hNK hn)) y hy).symm
  have hk2 : k ^ 2 ∈ N := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    change π (k ^ 2) = 1
    rw [map_pow, hk, ← map_pow, hu2, map_one]
  have hn2 : (k⁻¹ * u) ^ 2 = (k ^ 2)⁻¹ := by
    have hcomm : k * (k⁻¹ * u) = (k⁻¹ * u) * k := (hnk k hkK).symm
    have : u ^ 2 = k ^ 2 * (k⁻¹ * u) ^ 2 := by
      rw [← Commute.mul_pow hcomm]
      group
    rw [hu2] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hnQ : k⁻¹ * u ∈ Q := by
    refine mem_of_isPGroup_zpowers hQN hn ?_
    have hk2Q : k ^ 2 ∈ Q := hKN ⟨K.pow_mem hkK 2, hk2⟩
    obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := H)) ⟨_, hk2Q⟩
    have hj' : (k ^ 2) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hpow : (k⁻¹ * u) ^ 2 ^ (j + 1) = 1 := by
      rw [pow_succ', pow_mul, hn2, inv_pow, hj', inv_one]
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hQT : Q ≤ T₀ := IsPGroup.le_sylow_of_normal
    (CFSG.LieType.BorelTits.pCore_isPGroup 2) (hT₀.toSylow hT₀i)
  have hkT : k ∈ T₀ := by
    have : k = u * (k⁻¹ * u)⁻¹ := by group
    rw [this]
    exact T₀.mul_mem huT (T₀.inv_mem (hQT hnQ))
  have hkc : ∀ s ∈ T₀ ⊓ K, s * k = k * s := by
    intro s hs
    have h1 := huc s hs.1
    have h2' := hnk s hs.2
    calc s * k = s * (u * (k⁻¹ * u)⁻¹) := by group
      _ = u * s * (k⁻¹ * u)⁻¹ := by rw [← mul_assoc, h1]
      _ = u * (k⁻¹ * u)⁻¹ * ((k⁻¹ * u) * s) * (k⁻¹ * u)⁻¹ := by group
      _ = u * (k⁻¹ * u)⁻¹ * (s * (k⁻¹ * u)) * (k⁻¹ * u)⁻¹ := by rw [h2']
      _ = k * s := by group
  have hTsyl : IsSylowIn 2 T₀ ⊤ := ⟨le_top, hT₀, by rwa [Subgroup.relIndex_top_right]⟩
  have hSsyl : IsSylowIn 2 (T₀ ⊓ K) K :=
    hTsyl.inf_normal le_top ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mpr
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hKn]))
  let S' : Sylow 2 K := hSsyl.toSylow
  let P₀ : Sylow 2 N₀ := S'.mapSurjective hπK
  have hN₀card : Nat.card N₀ = 360 := by
    rw [Nat.card_congr (e.trans ψ).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hP₀card : Nat.card (P₀ : Subgroup N₀) = 8 := by
    refine AltSix.card_eq_eight_of_isSylowTwoOf (K := ⊤) ⟨le_top, P₀.isPGroup', ?_⟩ ?_
    · change ¬ 2 ∣ (P₀ : Subgroup N₀).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact P₀.not_dvd_index
    · rw [Subgroup.card_top, hN₀card]
  obtain ⟨b₀, hb₀P, hb₀2, a₀, ha₀P, hab₀⟩ := exists_noncentral_involution (e.trans ψ) _ hP₀card
  obtain ⟨b, hbS, hb⟩ : b₀ ∈ (S' : Subgroup K).map πK := hb₀P
  set k' : K := ⟨k, hkK⟩
  have hk'S : k' ∈ (S' : Subgroup K) := by
    change k' ∈ (T₀ ⊓ K).subgroupOf K
    exact Subgroup.mem_subgroupOf.mpr ⟨hkT, hkK⟩
  have hk'c : ∀ s ∈ (S' : Subgroup K), s * k' = k' * s := by
    intro s hs
    have hs' : (s : H) ∈ T₀ ⊓ K := Subgroup.mem_subgroupOf.mp hs
    exact Subtype.ext (hkc s hs')
  have hπk' : πK k' = ⟨π u, huN₀⟩ := Subtype.ext hk
  have hπk'c : ∀ y ∈ (P₀ : Subgroup N₀), y * πK k' = πK k' * y := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ : y ∈ (S' : Subgroup K).map πK := hy
    rw [← map_mul, ← map_mul, hk'c s hs]
  have hπk'1 : πK k' ≠ 1 := by
    rw [hπk']
    exact fun h => hu1 (congrArg Subtype.val h)
  have hcK : πK (ρ' (-1)) = 1 := by
    rw [hρ'π]
    exact (hkerρ _).mpr (Or.inr rfl)
  have hval : ∀ y : K, y = 1 ∨ y = ρ' (-1) → πK y = 1 := by
    rintro y (rfl | rfl)
    · exact map_one _
    · exact hcK
  have hb1 : b ^ 2 = ρ' (-1) := by
    have hbN : ((b ^ 2 : K) : H) ∈ N := (hker _).mp (by
      rw [MonoidHom.mem_ker, map_pow, hb]
      exact hb₀2 ▸ rfl)
    rcases hkerK _ hbN with h | h
    · exfalso
      have := hval b (hinv b h)
      rw [hb] at this
      exact hab₀ (by rw [this, mul_one, one_mul])
    · exact h
  have hk'2 : k' ^ 2 = ρ' (-1) := by
    have hkN : ((k' ^ 2 : K) : H) ∈ N := hk2
    rcases hkerK _ hkN with h | h
    · exact absurd (hval k' (hinv k' h)) hπk'1
    · exact h
  have hbk : (b * k') ^ 2 = 1 := by
    have hc : Commute b k' := hk'c b hbS
    rw [hc.mul_pow, hb1, hk'2, hc2]
  have h1 := hval _ (hinv _ hbk)
  rw [map_mul, hb] at h1
  have hb₀' : b₀ = (πK k')⁻¹ := eq_inv_of_mul_eq_one_left h1
  apply hab₀
  rw [hb₀']
  exact (Commute.inv_right (hπk'c a₀ ha₀P)).eq

end Layer

end L15422

end CFSG.Quasithin.EmptyFaithfulMultiple
