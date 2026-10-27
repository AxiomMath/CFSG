module

public import CFSG.Quasithin.EmptyFaithful.T1521SU3Base
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Quasithin.EmptyFaithful.T1521SU3Out

public section

namespace CFSG.Quasithin.U31521

open CFSG.Open CFSG.Quasithin CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.OutStructure
open CFSG.QuasithinUnique

theorem eq_of_sq_eq_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {x y : C}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  have := Fintype.ofFinite C
  by_contra hxy
  have h := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [*]
  have h3 : ({1, x, y} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hxy
    · simp [hx1.symm, hy1.symm]
  have := Finset.card_le_card hsub
  omega

theorem mem_of_pow_eq_one_of_mem_normalizer_aux {K : Type*} [Group K] (P : Sylow 2 K) {g : K}
    (hg : g ∈ Subgroup.normalizer ((P : Subgroup K) : Set K)) {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    g ∈ (P : Subgroup K) := by
  have hpg : IsPGroup 2 (Subgroup.zpowers g) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card ((Nat.card_zpowers g).trans hj)
  have hHN : Subgroup.zpowers g ≤ Subgroup.normalizer ((P : Subgroup K) : Set K) :=
    (Subgroup.zpowers_le (H := Subgroup.normalizer ((P : Subgroup K) : Set K))).mpr hg
  have h := P.is_maximal' (hpg.to_sup_of_normal_right' P.isPGroup' hHN) le_sup_right
  have hmem : g ∈ Subgroup.zpowers g ⊔ (P : Subgroup K) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
  rwa [h] at hmem

theorem card_eq_of_isSylowTwoOf {G : Type*} [Group G] [Finite G] {H P : Subgroup G}
    (h : IsSylowTwoOf P H) : Nat.card P = 2 ^ (Nat.card H).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Sylow.card_eq_multiplicity (A4.toSylow h)
  have h2 : Nat.card ((A4.toSylow h : Sylow 2 H) : Subgroup H) = Nat.card P := by
    rw [A4.toSylow_coe]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv
  rw [← h2]
  exact h1

section Stab

variable {X : Type} [Group X] {R : Subgroup X}

@[expose] def autStab (R : Subgroup X) : Subgroup (MulAut X) := rootCenterAut R ⊥

theorem map_eq_iff_aux {γ : MulAut X} :
    R.map γ.toMonoidHom = R ↔ ∀ x, γ x ∈ R ↔ x ∈ R := by
  constructor
  · intro h x
    have := SetLike.ext_iff.mp h (γ x)
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at this
    exact this.symm
  · intro h
    ext y
    rw [Subgroup.mem_map_equiv]
    have := h (γ.symm y)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm

theorem mem_autStab {γ : MulAut X} : γ ∈ autStab R ↔ ∀ x, γ x ∈ R ↔ x ∈ R := by
  rw [← map_eq_iff_aux]
  exact ⟨fun h => h.1, fun h => ⟨h, fun u hu => by rw [Subgroup.mem_bot.mp hu, map_one]⟩⟩

theorem conj_mem_autStab {r : X} (hr : r ∈ R) : MulAut.conj r ∈ autStab R := by
  rw [mem_autStab]
  intro x
  rw [MulAut.conj_apply]
  constructor
  · intro h
    have := R.mul_mem (R.mul_mem (R.inv_mem hr) h) hr
    simpa [mul_assoc] using this
  · intro h
    exact R.mul_mem (R.mul_mem hr h) (R.inv_mem hr)

theorem map_center_aux {γ : MulAut X} (hγ : γ ∈ autStab R) {u : X} (hu : u ∈ R)
    (hc : ∀ y ∈ R, u * y = y * u) : γ u ∈ R ∧ ∀ y ∈ R, γ u * y = y * γ u := by
  refine ⟨(mem_autStab.mp hγ u).2 hu, fun y hy => ?_⟩
  have hy' : γ.symm y ∈ R := by
    rw [← mem_autStab.mp hγ (γ.symm y), MulEquiv.apply_symm_apply]
    exact hy
  have := congrArg γ (hc _ hy')
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this

end Stab

theorem factorization_two_pow_mul_odd {a m : ℕ} (hm : Odd m) :
    (2 ^ a * m).factorization 2 = a := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hnd : ¬ 2 ∣ m := fun h => by
    have := Nat.odd_iff.mp hm
    omega
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]

section Zc

variable {X : Type} [Group X] [Finite X]

theorem centralizes_center_of_sq_eq_one {n : ℕ} (hn : 2 ≤ n)
    (hX : IsPSU 3 2 n X) (R : Sylow 2 X) {β : MulAut X} (hβ : β ∈ autStab (R : Subgroup X))
    (hβ2 : β ^ 2 = 1) {u : X} (hu : u ∈ (R : Subgroup X))
    (hc : ∀ y ∈ (R : Subgroup X), u * y = y * u) : β u = u := by
  classical
  have hRC := rootCenterData_of_isPSU hn hX R
  have hinj := conj_injective_of_isPSU hn hX
  set U := omegaU (R : Subgroup X) with hUdef
  set A := rootCenterAut (R : Subgroup X) U with hAdef
  set Nh := autStab (R : Subgroup X) with hNh
  set cR := (R : Subgroup X).map (MulAut.conj : X →* MulAut X) with hcR
  suffices hβA : β ∈ A from hβA.2 u ((hRC.center_iff u).2 ⟨hu, hc⟩)
  obtain ⟨D, hD1, hD2, hD3, hD4⟩ := hRC.exists_D
  have hAN : A ≤ Nh := fun γ hγ => mem_autStab.mpr (map_eq_iff_aux.mp hγ.1)
  have hcRA : cR ≤ A := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨(map_eq_iff_aux).mpr (mem_autStab.mp (conj_mem_autStab hr)), fun v hv => ?_⟩
    obtain ⟨-, hv2⟩ := (hRC.center_iff v).1 hv
    rw [MulAut.conj_apply, ← hv2 r hr]
    group
  have hcRN : cR ≤ Nh := hcRA.trans hAN
  have hAnorm : ∀ γ ∈ Nh, ∀ a ∈ A, γ * a * γ⁻¹ ∈ A := by
    intro γ hγ a ha
    have hγ' : γ⁻¹ ∈ Nh := Nh.inv_mem hγ
    have hmem : γ * a * γ⁻¹ ∈ Nh := Nh.mul_mem (Nh.mul_mem hγ (hAN ha)) hγ'
    refine ⟨map_eq_iff_aux.mpr (mem_autStab.mp hmem), fun v hv => ?_⟩
    obtain ⟨hv1, hv2⟩ := (hRC.center_iff v).1 hv
    obtain ⟨h1, h2⟩ := map_center_aux hγ' hv1 hv2
    have h3 : a (γ⁻¹ v) = γ⁻¹ v := ha.2 _ ((hRC.center_iff _).2 ⟨h1, h2⟩)
    rw [MulAut.mul_apply, MulAut.mul_apply, h3]
    simp
  have hAnormalizer : Nh ≤ Subgroup.normalizer (A : Set (MulAut X)) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hAnorm γ hγ a ha, fun ha => ?_⟩
    have := hAnorm γ⁻¹ (Nh.inv_mem hγ) _ ha
    simpa [mul_assoc] using this
  have hcRnorm : (cR.subgroupOf Nh).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hcRN]
    rintro _ γ ⟨r, hr, rfl⟩ hγ
    refine ⟨γ r, (mem_autStab.mp hγ r).2 hr, ?_⟩
    exact (mul_conj_mul_inv γ r).symm
  have hcRp : IsPGroup 2 cR := R.isPGroup'.map (MulAut.conj : X →* MulAut X)
  have hβp : IsPGroup 2 (Subgroup.zpowers β) := by
    have hk : β ^ 2 ^ 1 = 1 := by simpa using hβ2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card ((Nat.card_zpowers β).trans hj)
  obtain ⟨Ŝ, hŜ, hβŜ⟩ := A4.exists_isSylowTwoOf_ge
    ((Subgroup.zpowers_le (H := Nh)).mpr hβ) hβp
  have hβS : β ∈ Ŝ := hβŜ (Subgroup.mem_zpowers β)
  have hcRS : cR ≤ Ŝ := A4.le_of_normal_of_isSylowTwoOf hŜ hcRN hcRnorm hcRp
  have hŜA : IsSylowTwoOf (Ŝ ⊓ A) A := A4.isSylowTwoOf_inf_normal hŜ hAN hAnormalizer
  have hcRcard : Nat.card cR = Nat.card (R : Subgroup X) :=
    Subgroup.card_map_of_injective hinj
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp R.isPGroup'
  have hAcard : Nat.card A = Nat.card cR * (2 * (2 ^ n + 1)) := by
    have hAnrm : A ≤ Subgroup.normalizer (cR : Set (MulAut X)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hcRA).mp hD3
    have hD2' : cR ⊔ D = A := hD2
    have hDle : D ≤ Subgroup.normalizer (cR : Set (MulAut X)) := by
      refine le_trans ?_ hAnrm
      rw [← hD2']
      exact le_sup_right
    have := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer cR D hDle
      (disjoint_iff.mpr hD1)
    rw [hD2'] at this
    rw [this, hD4]
  have hSylA : Nat.card (Ŝ ⊓ A : Subgroup (MulAut X)) = 2 ^ (a + 1) := by
    rw [card_eq_of_isSylowTwoOf hŜA, hAcard, hcRcard, ha]
    have : 2 ^ a * (2 * (2 ^ n + 1)) = 2 ^ (a + 1) * (2 ^ n + 1) := by ring
    rw [this, factorization_two_pow_mul_odd (odd_two_pow_add_one_of_pos (by omega))]
  have hidx : (cR.subgroupOf (Ŝ ⊓ A)).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card cR (Ŝ ⊓ A)
    have h2 : cR ⊓ (Ŝ ⊓ A) = cR := inf_eq_left.mpr (le_inf hcRS hcRA)
    rw [h2, hSylA, hcRcard, ha, pow_succ] at h1
    have hpos : 0 < 2 ^ a := by positivity
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    change cR.relIndex (Ŝ ⊓ A) * 2 ^ a = 2 * 2 ^ a
    rw [h1, mul_comm]
  set Θ : MulAut X →* Outer X := QuotientGroup.mk' (Inn X) with hΘ
  have hΘone : ∀ γ, Θ γ = 1 ↔ γ ∈ Inn X := fun γ => QuotientGroup.eq_one_iff γ
  have hcRinn : cR ≤ Inn X := by
    rintro _ ⟨r, -, rfl⟩
    exact ⟨r, rfl⟩
  have hker : ∀ γ ∈ Ŝ, Θ γ = 1 → γ ∈ cR := by
    intro γ hγS hγ1
    obtain ⟨x, rfl⟩ := (hΘone γ).1 hγ1
    have hγN : (MulAut.conj x : MulAut X) ∈ Nh := hŜ.1 hγS
    have hxN : x ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have := mem_autStab.mp hγN y
      rw [MulAut.conj_apply] at this
      exact this.symm
    obtain ⟨k, hk⟩ := hŜ.2.1 ⟨_, hγS⟩
    have hk' : (MulAut.conj x : MulAut X) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hxk : x ^ 2 ^ k = 1 := by
      apply hinj
      rw [map_pow, map_one]
      exact hk'
    exact ⟨x, mem_of_pow_eq_one_of_mem_normalizer_aux R hxN hxk, rfl⟩
  have hcyc : IsCyclic (Ŝ.map Θ) := cyclic_map_outer_of_isPGroup hn hX hŜ.2.1
  obtain ⟨a₀, ha₀, ha₀R⟩ : ∃ a₀ ∈ Ŝ ⊓ A, a₀ ∉ cR := by
    by_contra hcon
    push Not at hcon
    have hle : Ŝ ⊓ A ≤ cR := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    rw [hSylA, hcRcard, ha] at this
    have : 2 ^ a < 2 ^ (a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have ha₀sq : a₀ * a₀ ∈ cR := by
    have := Subgroup.mul_self_mem_of_index_two hidx (⟨a₀, ha₀⟩ : ↥(Ŝ ⊓ A))
    simpa [Subgroup.mem_subgroupOf] using this
  have hΘa₀ : Θ a₀ ≠ 1 := fun h1 => ha₀R (hker a₀ ha₀.1 h1)
  have hΘa₀2 : Θ a₀ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    exact (hΘone _).2 (hcRinn ha₀sq)
  by_cases hΘβ : Θ β = 1
  · exact hcRA (hker β hβS hΘβ)
  · have hΘβ2 : Θ β ^ 2 = 1 := by rw [← map_pow, hβ2, map_one]
    let x : ↥(Ŝ.map Θ) := ⟨Θ β, Subgroup.mem_map_of_mem Θ hβS⟩
    let y : ↥(Ŝ.map Θ) := ⟨Θ a₀, Subgroup.mem_map_of_mem Θ ha₀.1⟩
    have hxy : x = y :=
      eq_of_sq_eq_one_of_isCyclic (Subtype.ext hΘβ2) (Subtype.ext hΘa₀2)
        (fun h => hΘβ (congrArg Subtype.val h)) (fun h => hΘa₀ (congrArg Subtype.val h))
    have hβa : Θ (β * a₀⁻¹) = 1 := by
      have h1 : Θ β = Θ a₀ := congrArg Subtype.val hxy
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have hmem : β * a₀⁻¹ ∈ cR := hker _ (Ŝ.mul_mem hβS (Ŝ.inv_mem ha₀.1)) hβa
    have : β = (β * a₀⁻¹) * a₀ := by group
    rw [this]
    exact A.mul_mem (hcRA hmem) ha₀.2

end Zc

end CFSG.Quasithin.U31521
