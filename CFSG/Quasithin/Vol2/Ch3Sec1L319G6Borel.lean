module

public import CFSG.Quasithin.Vol2.Ch3zBlocks

public section

namespace CFSG.Quasithin.H13.L319

open Matrix CFSG.SL2MinimalFaithful CFSG.Quasithin CFSG.Quasithin.Ch3z CFSG.QuasithinUnique

section SL2

private def borelG6 (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 2) K) where
  carrier := {z | (z : Matrix (Fin 2) (Fin 2) K) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : (a : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := ha
    have hb' : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hb
    show ((a * b : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha', hb']
  inv_mem' := by
    intro a ha
    have ha' : (a : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := ha
    show ((a⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ha']

private noncomputable def borelDiagG6 (K : Type) [Field K] : ↥(borelG6 K) →* Kˣ :=
  MonoidHom.toHomUnits
    { toFun := fun z => (z.1 : Matrix (Fin 2) (Fin 2) K) 0 0
      map_one' := by simp
      map_mul' := by
        intro a b
        have hb : (b.1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := b.2
        show ((a.1 * b.1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = _
        simp [Matrix.mul_apply, Fin.sum_univ_two, hb] }

private theorem borel_ker_entries_G6 {K : Type} [Field K] (a : ↥(borelDiagG6 K).ker) :
    (a.1.1 : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 ∧ (a.1.1 : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 ∧
      (a.1.1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  have h10 : (a.1.1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := a.1.2
  have h1 : borelDiagG6 K a.1 = 1 := a.2
  have h00 : (a.1.1 : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have := congrArg Units.val h1
    simpa [borelDiagG6] using this
  have hdet := Matrix.SpecialLinearGroup.det_coe a.1.1
  rw [Matrix.det_fin_two, h10, h00] at hdet
  refine ⟨h00, ?_, h10⟩
  linear_combination hdet

private theorem borel_ker_comm_G6 {K : Type} [Field K] (a b : ↥(borelDiagG6 K).ker) :
    a * b = b * a := by
  obtain ⟨a00, a11, a10⟩ := borel_ker_entries_G6 a
  obtain ⟨b00, b11, b10⟩ := borel_ker_entries_G6 b
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, a00, a11, a10, b00, b11, b10, add_comm]

private theorem borelG6_solvable (K : Type) [Field K] : Group.IsSolvable ↥(borelG6 K) := by
  haveI : IsMulCommutative ↥(borelDiagG6 K).ker := ⟨⟨borel_ker_comm_G6⟩⟩
  have h1 : Group.IsSolvable ↥(borelDiagG6 K).ker := inferInstance
  exact Group.isSolvable_of_ker_le_range (borelDiagG6 K).ker.subtype (borelDiagG6 K) (by simp)

private theorem lower_left_eq_zero_G6 {K : Type} [Field K] (z : SpecialLinearGroup (Fin 2) K)
    {r : K} (h : z * unipotent (1 : K) * z⁻¹ = unipotent r) :
    (z : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  have key : ((z * unipotent (1 : K) * z⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 1 0 =
      -((z : Matrix (Fin 2) (Fin 2) K) 1 0 * (z : Matrix (Fin 2) (Fin 2) K) 1 0) := by
    simp [coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] <;> ring
  have h10 : ((z * unipotent (1 : K) * z⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 1 0 =
      ((unipotent r : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    rw [h]
  have hr : ((unipotent r : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    simp [coe_unipotent]
  rw [key, hr] at h10
  have hcc : (z : Matrix (Fin 2) (Fin 2) K) 1 0 * (z : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    linear_combination -h10
  exact mul_self_eq_zero.mp hcc

private theorem normalizer_le_conj_borel_G6 {K : Type} [Field K] [Finite K] {f : ℕ}
    (hcard : Nat.card K = 2 ^ f) {Q₀ : Subgroup (SpecialLinearGroup (Fin 2) K)}
    (hQ₀ : Nat.card Q₀ = Nat.card K) :
    ∃ g : SpecialLinearGroup (Fin 2) K,
      ∀ z ∈ Subgroup.normalizer (Q₀ : Set (SpecialLinearGroup (Fin 2) K)), g⁻¹ * z * g ∈ borelG6 K := by
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem Nat.prime_two hcard hQ₀
  have hSmem : ∀ s ∈ Q₀, ∃ t : K, s = g * unipotent t * g⁻¹ := by
    let ψ : K → Q₀ := fun t => ⟨g * unipotent t * g⁻¹, hg t⟩
    have hinj : Function.Injective ψ := by
      intro t t' h
      have h' : g * unipotent t * g⁻¹ = g * unipotent t' * g⁻¹ := congrArg Subtype.val h
      exact unipotent_injective (mul_left_cancel (mul_right_cancel h'))
    intro s hs
    obtain ⟨t, ht⟩ := (hinj.bijective_of_nat_card_le hQ₀.le).2 ⟨s, hs⟩
    exact ⟨t, (congrArg Subtype.val ht).symm⟩
  refine ⟨g, fun z hz => ?_⟩
  have hmem : z * (g * unipotent (1 : K) * g⁻¹) * z⁻¹ ∈ Q₀ :=
    (Subgroup.mem_normalizer_iff.mp hz (g * unipotent (1 : K) * g⁻¹)).mp (hg 1)
  obtain ⟨r, hr⟩ := hSmem _ hmem
  have key : (g⁻¹ * z * g) * unipotent (1 : K) * (g⁻¹ * z * g)⁻¹ = unipotent r := by
    have : (g⁻¹ * z * g) * unipotent (1 : K) * (g⁻¹ * z * g)⁻¹ =
        g⁻¹ * (z * (g * unipotent (1 : K) * g⁻¹) * z⁻¹) * g := by group
    rw [this, hr]
    group
  exact lower_left_eq_zero_G6 _ key

end SL2

section Natural

variable {V : Type} [CommGroup V]

private theorem natBlock_data_G6 {H Q : Subgroup (MulAut V)} {U : Subgroup V} {e : ℕ} (he : 1 ≤ e)
    (hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) (hN : NatBlockData H U e) (hQ : IsSylowTwoOf Q H) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : SpecialLinearGroup (Fin 2) K →* ↥H),
      Nat.card K = 2 ^ e ∧ Function.Bijective π ∧
        Nat.card ((Q.subgroupOf H).comap π) = Nat.card K := by
  obtain ⟨K, instK, instF, hK, π, β, hπs, hβ, hβeq⟩ := hN
  have hact : ∀ (γ : SpecialLinearGroup (Fin 2) K) (u : ↥U),
      β ⟨((π γ : ↥H) : MulAut V) (u : V), hUinv _ (π γ).2 _ u.2⟩ =
        Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u))) :=
    fun γ u => hβeq γ u _
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply sl2_eq_one_of_mulVec
    intro w
    obtain ⟨u, hu⟩ := hβ.2 (Multiplicative.ofAdd w)
    have h1 := hact γ u
    have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hUinv _ (π γ).2 _ u.2⟩ : ↥U) = u := by
      apply Subtype.ext
      rw [hγ]
      rfl
    rw [h2, hu] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    simpa using h3.symm
  have hQH : Q ≤ H := hQ.1
  have hcardH : Nat.card H = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr (Equiv.ofBijective π ⟨hπinj, hπs⟩),
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have : Finite H := Finite.of_surjective π hπs
  have : Finite Q := Finite.of_injective (Subgroup.inclusion hQH) (Subgroup.inclusion_injective hQH)
  have hQcard : Nat.card Q = Nat.card K := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ.2.1
    have hidx : Odd (Q.subgroupOf H).index :=
      Nat.not_even_iff_odd.mp (fun h => hQ.2.2 (even_iff_two_dvd.mp h))
    have h1 : Nat.card (Q.subgroupOf H) * (Q.subgroupOf H).index = Nat.card H :=
      Subgroup.card_mul_index _
    have h2 : Nat.card (Q.subgroupOf H) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
    rw [h2, hk, hcardH, hK] at h1
    have hm : Odd ((2 ^ e) ^ 2 - 1) := by
      have h2e : Even ((2 ^ e) ^ 2) := (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩,
        two_ne_zero⟩)
      exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) h2e odd_one
    have hc1 : Nat.Coprime (2 ^ k) ((2 ^ e) ^ 2 - 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
    have hc2 : Nat.Coprime (2 ^ e) (Q.subgroupOf H).index :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hidx)
    have hd1 : 2 ^ k ∣ 2 ^ e := hc1.dvd_of_dvd_mul_right ⟨_, h1.symm⟩
    have hd2 : 2 ^ e ∣ 2 ^ k := by
      have : 2 ^ e ∣ 2 ^ k * (Q.subgroupOf H).index := ⟨_, h1⟩
      exact hc2.dvd_of_dvd_mul_right this
    have : k = e := le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd1)
      ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd2)
    rw [hk, hK, this]
  have hQ''card : Nat.card ((Q.subgroupOf H).comap π) = Nat.card K := by
    have : Nat.card ((Q.subgroupOf H).comap π) = Nat.card (Q.subgroupOf H) :=
      Nat.card_congr (Equiv.subtypeEquiv (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).toEquiv
        (fun γ => Iff.rfl))
    rw [this, ← hQcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  exact ⟨K, instK, instF, π, hK, ⟨hπinj, hπs⟩, hQ''card⟩

theorem natBlock_normalizer_solvable {H Q : Subgroup (MulAut V)} {U : Subgroup V} {e : ℕ}
    (he : 1 ≤ e) (hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) (hN : NatBlockData H U e)
    (hQ : IsSylowTwoOf Q H) :
    Group.IsSolvable ↥(H ⊓ Subgroup.normalizer (Q : Set (MulAut V))) := by
  obtain ⟨K, instK, instF, π, hK, hbij, hQ''card⟩ := natBlock_data_G6 he hUinv hN hQ
  obtain ⟨g, hg⟩ := normalizer_le_conj_borel_G6 hK hQ''card
  let e0 : SpecialLinearGroup (Fin 2) K ≃* ↥H := MulEquiv.ofBijective π hbij
  let ι₀ : ↥(H ⊓ Subgroup.normalizer (Q : Set (MulAut V))) →* ↥H := Subgroup.inclusion inf_le_left
  let ρ₀ : ↥(H ⊓ Subgroup.normalizer (Q : Set (MulAut V))) →* SpecialLinearGroup (Fin 2) K :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (e0.symm.toMonoidHom.comp ι₀)
  have hρ₀inj : Function.Injective ρ₀ := by
    intro a b hab
    have h1 : e0.symm (ι₀ a) = e0.symm (ι₀ b) := (MulAut.conj g⁻¹).injective hab
    have h2 : ι₀ a = ι₀ b := e0.symm.injective h1
    exact Subgroup.inclusion_injective _ h2
  have hρ₀ : ∀ x, ρ₀ x = g⁻¹ * e0.symm (ι₀ x) * g := by
    intro x
    show (MulAut.conj g⁻¹) (e0.symm (ι₀ x)) = _
    simp [MulAut.conj_apply]
  have hmem : ∀ x, ρ₀ x ∈ borelG6 K := by
    intro x
    rw [hρ₀]
    apply hg
    set z := e0.symm (ι₀ x) with hz
    have hπz : ((π z : ↥H) : MulAut V) = (x : MulAut V) := by
      have : e0 z = ι₀ x := e0.apply_symm_apply _
      exact congrArg Subtype.val this
    have hxN : (x : MulAut V) ∈ Subgroup.normalizer (Q : Set (MulAut V)) := x.2.2
    have hQmem : ∀ γ : SpecialLinearGroup (Fin 2) K,
        γ ∈ (Q.subgroupOf H).comap π ↔ ((π γ : ↥H) : MulAut V) ∈ Q := fun γ => Iff.rfl
    refine B6.mem_normalizer_of_forall_mem (fun q hq => ?_) (fun q hq => ?_)
    · rw [hQmem] at hq ⊢
      have := (Subgroup.mem_normalizer_iff.mp hxN _).mp hq
      simpa [map_mul, map_inv, hπz] using this
    · rw [hQmem] at hq ⊢
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp hq
      simpa [map_mul, map_inv, hπz] using this
  let ρ : ↥(H ⊓ Subgroup.normalizer (Q : Set (MulAut V))) →* ↥(borelG6 K) :=
    ρ₀.codRestrict (borelG6 K) hmem
  haveI := borelG6_solvable K
  exact Group.isSolvable_of_isSolvable_injective (f := ρ) (fun a b hab => hρ₀inj (congrArg Subtype.val hab))

end Natural

section Sylow

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem normalizer_inf_normalizer_self {H Q : Subgroup Γ} (hQ : IsSylowTwoOf Q H) {h : Γ} (hh : h ∈ H)
    (hn : h ∈ Subgroup.normalizer ((H ⊓ Subgroup.normalizer (Q : Set Γ) : Subgroup Γ) : Set Γ)) :
    h ∈ Subgroup.normalizer (Q : Set Γ) := by
  let P : Sylow 2 ↥H := B6.toSylow2 hQ
  have hP : (P : Subgroup ↥H) = Q.subgroupOf H := B6.toSylow2_coe hQ
  have key := Sylow.normalizer_normalizer P
  have hPset : (P : Set ↥H) = ((Q.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [← hP]
    rfl
  have hN : (Subgroup.normalizer (P : Set ↥H) : Subgroup ↥H) =
      (Subgroup.normalizer (Q : Set Γ)).subgroupOf H := by
    rw [hPset, ← Subgroup.subgroupOf_normalizer_eq hQ.1]
  have hmem : (⟨h, hh⟩ : ↥H) ∈ Subgroup.normalizer
      ((Subgroup.normalizer (P : Set ↥H) : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hN]
    have h1 := Subgroup.mem_normalizer_iff.mp hn (y : Γ)
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h1 ⊢
    have hy : (y : Γ) ∈ H := y.2
    have hy' : h * (y : Γ) * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hy) (H.inv_mem hh)
    constructor
    · intro hy2
      exact (h1.mp ⟨hy, hy2⟩).2
    · intro hy2
      exact (h1.mpr ⟨hy', hy2⟩).2
  rw [key, hN] at hmem
  exact hmem

end Sylow

end CFSG.Quasithin.H13.L319
