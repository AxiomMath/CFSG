module

public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
public import CFSG.RankThree.PartOne.KC.ThetaCoreSimpleFixedGroup
public import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentLift
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningPCore

public section

namespace CFSG.RankThree.PartOne

open Matrix Subgroup CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.Chevalley CFSG.RankThree.Classical
open scoped commutatorElement

namespace KCEvenUnitaryFive

theorem inSubgroup_theta_centralizer_eq_bot_of_simple_normal_fixed {T : Type*} [Group T]
    [Finite T] {p : ℕ} (hp : p.Prime) (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    {a : MulAut T} (hord : orderOf a = p) {H : Subgroup T} (hfix : ∀ x ∈ H, a x = x)
    (hinv : ∀ c : MulAut T, c * a = a * c → ∀ x ∈ H, c x ∈ H) (hsimple : IsSimpleGroup H)
    (hnonab : ¬ ∀ x y : H, x * y = y * x)
    (hstab : ∀ s : MulAut T, (∀ x ∈ H, s x = x) → s ∈ zpowers a)
    {B : Subgroup (MulAut T)} (hB : (MulAut.conj : T →* MulAut T).range ≤ B) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer ({a} : Set (MulAut T))) =
      ⊥ := by
  classical
  have : Finite (MulAut T) := inferInstance
  set C : Subgroup (MulAut T) := B ⊓ Subgroup.centralizer ({a} : Set (MulAut T)) with hC
  set W : Subgroup (MulAut T) := H.map (MulAut.conj : T →* MulAut T) with hW
  obtain ⟨hSC, hSn, hSp, hSs⟩ := inSubgroup_theta_solvable_normal_prime_complement hp C
  generalize inSubgroup (aschbacherSolvableCore p) C = S at hSC hSn hSp hSs ⊢
  have hSnorm : ∀ y ∈ C, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    have := hSn.conj_mem ⟨s, hSC hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hcH : ∀ c ∈ C, ∀ x ∈ H, c x ∈ H := fun c hc x hx =>
    hinv c (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.1 hc).2) x hx
  have hWC : W ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hB ⟨x, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := KCUnitaryDefining.conj_apply_mulAut a x
    rw [hfix x hx] at h1
    calc MulAut.conj x * a = (a * MulAut.conj x * a⁻¹) * a := by rw [← h1]
      _ = a * MulAut.conj x := by group
  have hWnorm : ∀ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    rintro c hc _ ⟨x, hx, rfl⟩
    exact ⟨c x, hcH c hc x hx, KCUnitaryDefining.conj_apply_mulAut c x⟩
  have hSWtriv : ∀ x ∈ H, MulAut.conj x ∈ S → x = 1 := by
    intro x hx hxS
    let N : Subgroup H := S.comap ((MulAut.conj : T →* MulAut T).comp H.subtype)
    have hNn : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hgC : (MulAut.conj (g : T) : MulAut T) ∈ C := hWC ⟨g, g.2, rfl⟩
      have := hSnorm _ hgC _ hn
      simpa [N, map_mul, map_inv] using this
    have := hNn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · have hmem : (⟨x, hx⟩ : H) ∈ N := hxS
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exfalso
      apply hnonab
      rw [IsSimpleGroup.comm_iff_isSolvable (G := H)]
      let f : H →* S := ((MulAut.conj : T →* MulAut T).comp H.subtype).codRestrict S
        (fun y => by
          have : y ∈ N := h ▸ Subgroup.mem_top y
          exact this)
      have hfinj : Function.Injective f := by
        intro y z hyz
        apply Subtype.ext
        apply hinj
        exact congrArg Subtype.val hyz
      exact Group.isSolvable_of_isSolvable_injective hfinj
  have hSpt : ∀ s ∈ S, ∀ x ∈ H, s x = x := by
    intro s hs x hx
    have hsC := hSC hs
    have hWx : MulAut.conj x ∈ W := ⟨x, hx, rfl⟩
    have h1 : s * MulAut.conj x * s⁻¹ * (MulAut.conj x)⁻¹ ∈ W :=
      W.mul_mem (hWnorm s hsC _ hWx) (W.inv_mem hWx)
    have h2 : s * MulAut.conj x * s⁻¹ * (MulAut.conj x)⁻¹ ∈ S := by
      have := S.mul_mem hs (hSnorm _ (hWC hWx) s⁻¹ (S.inv_mem hs))
      rwa [← mul_assoc, ← mul_assoc] at this
    obtain ⟨y, hy, hyeq⟩ := h1
    have hyS : MulAut.conj y ∈ S := hyeq ▸ h2
    have hy1 : y = 1 := hSWtriv y hy hyS
    rw [hy1, map_one] at hyeq
    have h3 : s * MulAut.conj x = MulAut.conj x * s := by
      calc s * MulAut.conj x
          = s * MulAut.conj x * s⁻¹ * (MulAut.conj x)⁻¹ * (MulAut.conj x * s) := by group
        _ = MulAut.conj x * s := by rw [← hyeq, one_mul]
    apply hinj
    rw [KCUnitaryDefining.conj_apply_mulAut, h3, mul_inv_cancel_right]
  have hSle : S ≤ zpowers a := fun s hs => hstab s (hSpt s hs)
  have hdvd : Nat.card S ∣ p := by
    have := Subgroup.card_dvd_of_le hSle
    rwa [Nat.card_zpowers, hord] at this
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exact absurd (h ▸ dvd_refl _) hSp

section Commutator

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem commutatorElement_mul_center_left {G : Type*} [Group G] (a y : G) {s : G}
    (hs : s ∈ Subgroup.center G) : ⁅a * s, y⁆ = ⁅a, y⁆ := by
  have h1 : s * y = y * s := (Subgroup.mem_center_iff.mp hs y).symm
  simp only [commutatorElement_def, _root_.mul_inv_rev, mul_assoc]
  congr 1
  rw [← mul_assoc s y, h1, mul_assoc y s, mul_inv_cancel_left]

theorem commutatorElement_mul_of_mem_center {G : Type*} [Group G] (a b : G) {s s' : G}
    (hs : s ∈ Subgroup.center G) (hs' : s' ∈ Subgroup.center G) :
    ⁅a * s, b * s'⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv (b * s') (a * s), commutatorElement_mul_center_left b (a * s) hs',
    commutatorElement_inv, commutatorElement_mul_center_left a b hs]

theorem exists_scalar_of_fixed {n : ℕ} (σ : K ≃+* K)
    {g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hg : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = g) :
    ∃ c : Kˣ, (g : GL (Fin n) K) =
      glAut σ (g : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c := by
  have h1 : primeFormFieldAut h (isPrimeFormGram_one (n := n)) σ
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = g := hg
  rw [primeFormFieldAut_mk, QuotientGroup.eq] at h1
  obtain ⟨c, -, -, hc⟩ := h1
  refine ⟨c, ?_⟩
  have hc' : (glAut σ (g : GL (Fin n) K))⁻¹ * (g : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c := hc
  rw [← hc']
  group

variable {σ : K ≃+* K} {e : ℕ} {h₀ : UnitaryFieldData ℓ e (fixSubfield σ)}
  (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c) (n : ℕ)

theorem commutator_fieldFixedPSU_le_range :
    ⁅fieldFixedPSU h n σ, fieldFixedPSU h n σ⁆ ≤ (subfieldPSU h h₀ hbar n).range := by
  classical
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
  have hx' : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = g := hx
  have hy' : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ
      (g' : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = g' := hy
  obtain ⟨c, hc⟩ := exists_scalar_of_fixed h σ hx'
  obtain ⟨c', hc'⟩ := exists_scalar_of_fixed h σ hy'
  have hs : GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hs' : GeneralLinearGroup.scalar (Fin n) c' ∈ Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c', rfl⟩
  set k : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⁅g, g'⁆ with hk
  have hkGL : (k : GL (Fin n) K) = ⁅(g : GL (Fin n) K), (g' : GL (Fin n) K)⁆ :=
    map_commutatorElement (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).subtype g g'
  have e1 : ⁅(g : GL (Fin n) K), (g' : GL (Fin n) K)⁆ =
      ⁅glAut σ (g : GL (Fin n) K), glAut σ (g' : GL (Fin n) K)⁆ :=
    calc ⁅(g : GL (Fin n) K), (g' : GL (Fin n) K)⁆
        = ⁅glAut σ (g : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c,
            glAut σ (g' : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c'⁆ := by
          rw [← hc, ← hc']
      _ = _ := commutatorElement_mul_of_mem_center _ _ hs hs'
  have hkfix : glAut σ (k : GL (Fin n) K) = k := by
    rw [hkGL, map_commutatorElement, ← e1]
  obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed n hkfix
  have hg₀mem := mem_gramSU_of_subfieldGL h n h₀ hbar (g₀ := g₀) (by rw [hg₀]; exact k.2)
  refine ⟨((⟨g₀, hg₀mem⟩ : gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
    Matrix (Fin n) (Fin n) (fixSubfield σ))) : primeFormP h₀ _), ?_⟩
  rw [subfieldPSU_mk]
  have hmk : ((k : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      ⁅(g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
        (g' : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁆ :=
    map_commutatorElement (QuotientGroup.mk' (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n)) g g'
  rw [← hmk]
  congr 1
  exact Subtype.ext hg₀

theorem commutator_fieldFixedPSU_eq_range (hn : 3 ≤ n) (hq₀ : ¬(n = 3 ∧ ℓ ^ e = 2)) :
    ⁅fieldFixedPSU h n σ, fieldFixedPSU h n σ⁆ = (subfieldPSU h h₀ hbar n).range := by
  refine le_antisymm (commutator_fieldFixedPSU_le_range h hbar n) ?_
  have : Group.IsPerfect (gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) := isPerfect_gramSU_one h₀ hn hq₀
  have hperf : Group.IsPerfect (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hJ : (subfieldPSU h h₀ hbar n).range =
      ⁅(subfieldPSU h h₀ hbar n).range, (subfieldPSU h h₀ hbar n).range⁆ := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      hperf.commutator_eq_top]
  rw [hJ]
  exact Subgroup.commutator_mono (range_subfieldPSU_le h n h₀ hbar)
    (range_subfieldPSU_le h n h₀ hbar)

theorem map_mem_range_of_commute (hn : 3 ≤ n) (hq₀ : ¬(n = 3 ∧ ℓ ^ e = 2))
    {c : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hc : c * primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ =
      primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ * c)
    {x : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hx : x ∈ (subfieldPSU h h₀ hbar n).range) : c x ∈ (subfieldPSU h h₀ hbar n).range := by
  have hcF : ∀ y ∈ fieldFixedPSU h n σ, c y ∈ fieldFixedPSU h n σ := fun y hy => by
    have hy' : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ y = y := hy
    change primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ (c y) = c y
    have h1 := congrArg (fun γ : MulAut _ => γ y) hc
    simp only [MulAut.mul_apply] at h1
    rw [hy'] at h1
    exact h1.symm
  have hJ := (commutator_fieldFixedPSU_eq_range h hbar n hn hq₀).symm
  have hmap : (⁅fieldFixedPSU h n σ, fieldFixedPSU h n σ⁆).map c.toMonoidHom ≤
      ⁅fieldFixedPSU h n σ, fieldFixedPSU h n σ⁆ := by
    rw [Subgroup.map_commutator]
    have hle : (fieldFixedPSU h n σ).map c.toMonoidHom ≤ fieldFixedPSU h n σ := by
      rintro _ ⟨z, hz, rfl⟩
      exact hcF z hz
    exact Subgroup.commutator_mono hle hle
  rw [hJ] at hx ⊢
  exact hmap (Subgroup.mem_map_of_mem _ hx)

end Commutator

section FieldActor

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem theta_centralizer_fieldHom_eq_bot {σ : K ≃+* K} (hσ : orderOf σ = 5)
    {B : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)))}
    (hB : (MulAut.conj : primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) →*
      MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))).range ≤ B) :
    inSubgroup (aschbacherSolvableCore 5) (B ⊓ Subgroup.centralizer
      ({primeFormFieldHom h (isPrimeFormGram_one (n := 5)) σ} :
        Set (MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))))) = ⊥ := by
  have : Finite K := h.finite
  have hp : Nat.Prime 5 := Nat.prime_five
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hn : 3 ≤ 5 := by norm_num
  have hq : ¬(5 = 3 ∧ ℓ ^ f = 2) := fun h' => absurd h'.1 (by norm_num)
  have hq₀ : ¬(5 = 3 ∧ ℓ ^ (f / 5) = 2) := fun h' => absurd h'.1 (by norm_num)
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hinj := KCUnitaryRegular.conj_injective_primeFormP h (isPrimeFormGram_one (n := 5)) hn hq
  have hjinj := subfieldPSU_injective h h₀ hbar 5 (by norm_num)
  have hsimple0 := isSimpleGroup_primeFormP_one h₀ hn hq₀
  have hnc0 := not_commute_primeFormP_one h₀ hn hq₀
  let eJ : primeFormP h₀ ((1 : GL (Fin 5) (fixSubfield σ)) :
      Matrix (Fin 5) (Fin 5) (fixSubfield σ)) ≃* (subfieldPSU h h₀ hbar 5).range :=
    MonoidHom.ofInjective hjinj
  obtain ⟨hfixing, hmap, -⟩ := fixingSubgroup_range_subfieldPSU h 5 h₀ hbar hn hq hq₀
  refine inSubgroup_theta_centralizer_eq_bot_of_simple_normal_fixed hp hinj
    (a := primeFormFieldHom h (isPrimeFormGram_one (n := 5)) σ)
    (by rw [orderOf_injective _ (primeFormFieldHom_injective h 5 hn hq) σ, hσ])
    (H := (subfieldPSU h h₀ hbar 5).range)
    (fun x hx => range_subfieldPSU_le h 5 h₀ hbar hx)
    (fun c hc x hx => map_mem_range_of_commute h hbar 5 hn hq₀ hc hx)
    eJ.symm.isSimpleGroup
    (fun hc => hnc0 fun x y => ?_) (fun s hs => ?_) hB
  · have h1 := congrArg eJ.symm (hc (eJ x) (eJ y))
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h1
  · have hs' : s ∈ fixingSubgroup (MulAut (primeFormP h
        ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)))
        ((subfieldPSU h h₀ hbar 5).range : Set (primeFormP h
          ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))) :=
      (mem_fixingSubgroup_iff _).2 fun y hy => by
        rw [MulAut.smul_def]
        exact hs y hy
    rw [hfixing, hmap] at hs'
    exact hs'

end FieldActor

end KCEvenUnitaryFive

theorem even_unitary_five_field_actor_solvable_core_trivial {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (_h5 : 5 ∣ 2 ^ f + 1)
    (B : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))))
    (hB : (MulAut.conj : primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) →*
      MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))).range ≤ B)
    {a : MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))} (_haB : a ∈ B)
    (haD : a ∉ primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))
    (hord : orderOf a = 5) :
    inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (primeFormP h
        ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))))) = ⊥ := by
  classical
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin 5) K) := isPrimeFormGram_one
  have hn : 3 ≤ 5 := by norm_num
  have hq : ¬(5 = 3 ∧ 2 ^ f = 2) := fun h' => absurd h'.1 (by norm_num)
  set σ := primeFormFieldFactor h hC hn hq a with hσdef
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply haD
    rw [← ker_primeFormFieldFactor h hC hn hq]
    exact h1
  have ha5 : a ^ 5 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [hord] at this
  have hσ5 : σ ^ 5 = 1 := by
    rw [hσdef, ← map_pow, ha5, map_one]
  have hσord : orderOf σ = 5 := by
    have hd : orderOf σ ∣ 5 := orderOf_dvd_of_pow_eq_one hσ5
    rcases (Nat.dvd_prime Nat.prime_five).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hσ1
    · exact h1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hq Nat.prime_five
      (by norm_num) (by norm_num) a hord σ rfl hσord
  set γ := primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) M with hγ
  set φ : MulAut (MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))) :=
    MulAut.conj γ⁻¹ with hφ
  have hφapp : ∀ x, φ.toMonoidHom x = γ⁻¹ * x * γ := fun x => by simp [hφ]
  have hφa : φ a = primeFormFieldHom h hC σ := by
    show φ.toMonoidHom a = _
    rw [hφapp]
    exact hM
  set B' := B.map φ.toMonoidHom with hB'
  have hB'conj : (MulAut.conj : primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) →*
      MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))).range ≤ B' := by
    rintro _ ⟨x, rfl⟩
    refine Subgroup.mem_map.mpr ⟨MulAut.conj (γ x), hB ⟨γ x, rfl⟩, ?_⟩
    rw [hφapp, KCUnitaryDefining.conj_apply_mulAut γ x]
    group
  have h1 := map_inSubgroup_theta_centralizer_mulEquiv Nat.prime_five φ B a
  rw [hφa, KCEvenUnitaryFive.theta_centralizer_fieldHom_eq_bot h hσord hB'conj] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1

end CFSG.RankThree.PartOne
