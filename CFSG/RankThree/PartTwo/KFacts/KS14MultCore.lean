module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open scoped commutatorElement

section Transfer

variable {X : Type*} [Group X] [Finite X]

theorem pow_index_eq_one_of_isPerfect [Group.IsPerfect X] (P : Subgroup X)
    (hP : ∀ a b : P, a * b = b * a) {z : X} (hzc : z ∈ Subgroup.center X) :
    z ^ P.index = 1 := by
  have hkey : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k * g₀ = g₀ * z ^ k :=
      ((Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hzc k)) g₀).symm
    rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 := MonoidHom.transfer_eq_pow (Abelianization.of : P →* Abelianization P) z hkey
  have h2 : MonoidHom.transfer (Abelianization.of : P →* Abelianization P) z = 1 := by
    have hle : commutator X ≤
        (MonoidHom.transfer (Abelianization.of : P →* Abelianization P)).ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    rw [Group.IsPerfect.commutator_eq_top] at hle
    exact hle (Subgroup.mem_top z)
  rw [h2] at h1
  have hmem : (⟨z ^ P.index, MonoidHom.transfer_eq_pow_aux z hkey⟩ : P) ∈
      commutator P := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact h1.symm
  have hcomm : commutator P = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    exact Subgroup.mem_centralizer_iff.mpr fun b _ => hP b a
  rw [hcomm, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

omit [Finite X] in
theorem sylow_comm_of_isCyclic_map {Z : Subgroup X} [Z.Normal] (hZc : Z ≤ Subgroup.center X)
    {p : ℕ} (P : Sylow p X)
    (hcyc : IsCyclic ((QuotientGroup.mk' Z).comp (P : Subgroup X).subtype).range) :
    ∀ a b : (P : Subgroup X), a * b = b * a := by
  set f : (P : Subgroup X) →* X ⧸ Z := (QuotientGroup.mk' Z).comp (P : Subgroup X).subtype
    with hf
  have hker : f.rangeRestrict.ker ≤ Subgroup.center (P : Subgroup X) := by
    intro a ha
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hf, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZc ha) b)
  exact (f.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm

theorem eq_bot_of_isPerfect_of_sylow_comm [Group.IsPerfect X] {Z : Subgroup X} [Z.Normal]
    (hZc : Z ≤ Subgroup.center X)
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card Z → ∀ P : Sylow p X,
      ∀ a b : (P : Subgroup X), a * b = b * a) : Z = ⊥ := by
  by_contra hne
  have h1 : Nat.card Z ≠ 1 := fun h1 => hne (Subgroup.eq_bot_of_card_eq _ h1)
  obtain ⟨p, hp, hpZ⟩ := Nat.exists_prime_and_dvd h1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨z, hzZ⟩, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) p hpZ
  have hzo : orderOf z = p := by
    rw [← hz, Subgroup.orderOf_mk]
  obtain ⟨P⟩ : Nonempty (Sylow p X) := inferInstance
  have hpow := pow_index_eq_one_of_isPerfect (P : Subgroup X) (h p hp hpZ P) (hZc hzZ)
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  rw [hzo] at hdvd
  exact P.not_dvd_index hdvd

theorem eq_bot_of_isPerfect_of_isCyclic_sylow [Group.IsPerfect X] {Z : Subgroup X} [Z.Normal]
    (hZc : Z ≤ Subgroup.center X)
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card Z → ∀ Q : Sylow p (X ⧸ Z), IsCyclic Q) : Z = ⊥ := by
  refine eq_bot_of_isPerfect_of_sylow_comm hZc fun p hp hpZ P => ?_
  have : Fact p.Prime := ⟨hp⟩
  set f : (P : Subgroup X) →* X ⧸ Z := (QuotientGroup.mk' Z).comp (P : Subgroup X).subtype
    with hf
  have hR : IsPGroup p f.range :=
    (P.isPGroup').of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  have hQ := h p hp hpZ Q
  have hcyc : IsCyclic f.range :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hRQ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hRQ).surjective
  exact sylow_comm_of_isCyclic_map hZc P hcyc

theorem sylow_comm_of_not_sq_dvd {Z : Subgroup X} [Z.Normal] (hZc : Z ≤ Subgroup.center X)
    {p : ℕ} [Fact p.Prime] (h : ¬ p ^ 2 ∣ Nat.card (X ⧸ Z)) (P : Sylow p X) :
    ∀ a b : (P : Subgroup X), a * b = b * a := by
  set f : (P : Subgroup X) →* X ⧸ Z := (QuotientGroup.mk' Z).comp (P : Subgroup X).subtype
    with hf
  have hR : IsPGroup p f.range :=
    (P.isPGroup').of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra hk1
    apply h
    have : p ^ k ∣ Nat.card (X ⧸ Z) := hk ▸ Subgroup.card_subgroup_dvd_card _
    exact (pow_dvd_pow p (by omega)).trans this
  have hcyc : IsCyclic f.range := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with rfl | rfl
    · rw [pow_zero] at hk
      have := (Nat.card_eq_one_iff_unique.mp hk).1
      infer_instance
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk
  exact sylow_comm_of_isCyclic_map hZc P hcyc

theorem eq_bot_of_isPerfect_of_not_sq_dvd [Group.IsPerfect X] {Z : Subgroup X} [Z.Normal]
    (hZc : Z ≤ Subgroup.center X)
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card Z → ¬ p ^ 2 ∣ Nat.card (X ⧸ Z)) : Z = ⊥ := by
  refine eq_bot_of_isPerfect_of_isCyclic_sylow hZc fun p hp hpZ Q => ?_
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra hk1
    apply h p hp hpZ
    have : p ^ k ∣ Nat.card (X ⧸ Z) := hk ▸ Subgroup.card_subgroup_dvd_card _
    exact (pow_dvd_pow p (by omega)).trans this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with rfl | rfl
  · rw [pow_zero] at hk
    have := (Nat.card_eq_one_iff_unique.mp hk).1
    infer_instance
  · rw [pow_one] at hk
    exact isCyclic_of_prime_card hk

end Transfer

section FivePart

variable {X : Type} [Group X]

omit [Group X] in
theorem pow_conj_eq_of_conj_eq {G : Type*} [Group G] {x y c : G} (hc : ∀ g : G, g * c = c * g)
    (hxy : x * y * x⁻¹ = c * y) (n : ℕ) : x ^ n * y * (x ^ n)⁻¹ = c ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹ = x * (x ^ n * y * (x ^ n)⁻¹) * x⁻¹ := by group
      _ = x * (c ^ n * y) * x⁻¹ := by rw [ih]
      _ = c ^ n * (x * y * x⁻¹) := by
          have hcn : ∀ g : G, g * c ^ n = c ^ n * g := fun g => (Commute.pow_right (hc g) n).eq
          rw [← mul_assoc, hcn x]
          group
      _ = c ^ (n + 1) * y := by rw [hxy, pow_succ, mul_assoc]

theorem commute_of_mem_closure {G : Type*} [Group G] {T : Set G}
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {u v : G} (hu : u ∈ Subgroup.closure T)
    (hv : v ∈ Subgroup.closure T) : u * v = v * u := by
  have h1 : Subgroup.closure T ≤ Subgroup.centralizer T := by
    rw [Subgroup.closure_le]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun b hb => hT b hb a ha
  have h2 : Subgroup.closure T ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (h1 hu) a ha
  exact (Subgroup.mem_centralizer_singleton_iff.mp (h2 hv)).symm

theorem sylow_five_comm_of_witness [Finite X] {S : Type} [Group S] {Z : Subgroup X} [Z.Normal]
    (hZc : Z ≤ Subgroup.center X) (e : X ⧸ Z ≃* S) {x y g : S} (hx5 : x ^ 5 = 1)
    (hxy : x * y = y * x) (hgx : g * x * g⁻¹ = x ^ 4) (hgy : g * y * g⁻¹ = x ^ 3 * y)
    (hE : Nat.card (Subgroup.closure ({x, y} : Set S)) = 25)
    (hfac : (Nat.card S).factorization 5 = 2) (P : Sylow 5 X) :
    ∀ a b : (P : Subgroup X), a * b = b * a := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite S := Finite.of_equiv _ e.toEquiv
  set π : X →* S := e.toMonoidHom.comp (QuotientGroup.mk' Z) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hπk : ∀ w, π w = 1 ↔ w ∈ Z := by
    intro w
    simp only [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcen : ∀ w ∈ Z, ∀ v : X, v * w = w * v := fun w hw v =>
    Subgroup.mem_center_iff.mp (hZc hw) v
  set E := Subgroup.closure ({x, y} : Set S) with hEdef
  let SE : Sylow 5 S := Sylow.ofCard E (by rw [hE, hfac]; norm_num)
  let SP : Sylow 5 S := P.mapSurjective hπs
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq S SP SE
  obtain ⟨s', rfl⟩ := hπs s
  set P' : Subgroup X := (P : Subgroup X).map (MulAut.conj s').toMonoidHom with hP'
  have hP'E : P'.map π = E := by
    have h2 := congrArg (fun T : Sylow 5 S => (T : Subgroup S)) hs
    simp only [SP, SE, Sylow.coe_ofCard] at h2
    have hsm : ((π s' • SP : Sylow 5 S) : Subgroup S) =
        (SP : Subgroup S).map (MulAut.conj (π s')).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [hsm, Sylow.coe_mapSurjective] at h2
    rw [← h2, hP', Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext w
    simp [hπ, MulAut.conj_apply]
  obtain ⟨x', hx'P, hx'⟩ : ∃ x' ∈ P', π x' = x := by
    have : x ∈ P'.map π := hP'E ▸ Subgroup.subset_closure (Set.mem_insert x {y})
    exact this
  obtain ⟨y', hy'P, hy'⟩ : ∃ y' ∈ P', π y' = y := by
    have : y ∈ P'.map π := hP'E ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
    exact this
  obtain ⟨g', hg'⟩ := hπs g
  set c := x' * y' * x'⁻¹ * y'⁻¹ with hcdef
  have hcZ : c ∈ Z := by
    rw [← hπk, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hx', hy', hxy]
    group
  have hcc : ∀ v : X, v * c = c * v := hcen c hcZ
  have hconj : x' * y' * x'⁻¹ = c * y' := by rw [hcdef]; group
  have hx5' : x' ^ 5 ∈ Z := by rw [← hπk, map_pow, hx', hx5]
  have hc5 : c ^ 5 = 1 := by
    have h1 := pow_conj_eq_of_conj_eq hcc hconj 5
    rw [← hcen _ hx5' y', mul_assoc, mul_inv_cancel, mul_one] at h1
    have := congrArg (· * y'⁻¹) h1
    simpa using this.symm
  have hz1 : (x' ^ 4)⁻¹ * (g' * x' * g'⁻¹) ∈ Z := by
    rw [← hπk, map_mul, map_inv, map_pow, map_mul, map_mul, map_inv, hx', hg', hgx]
    group
  have hz2 : (x' ^ 3 * y')⁻¹ * (g' * y' * g'⁻¹) ∈ Z := by
    rw [← hπk, map_mul, map_inv, map_mul, map_pow, map_mul, map_mul, map_inv, hx', hy', hg', hgy]
    group
  set z₁ := (x' ^ 4)⁻¹ * (g' * x' * g'⁻¹) with hz₁
  set z₂ := (x' ^ 3 * y')⁻¹ * (g' * y' * g'⁻¹) with hz₂
  have hgx' : g' * x' * g'⁻¹ = x' ^ 4 * z₁ := by rw [hz₁]; group
  have hgy' : g' * y' * g'⁻¹ = x' ^ 3 * y' * z₂ := by rw [hz₂]; group
  have hc4 : c = c ^ 4 := by
    have h1 : g' * c * g'⁻¹ = c := by rw [hcc g', mul_assoc, mul_inv_cancel, mul_one]
    have h4 := pow_conj_eq_of_conj_eq hcc hconj 4
    have hcc4 : ∀ v : X, v * c ^ 4 = c ^ 4 * v := fun v => (Commute.pow_right (hcc v) 4).eq
    have hA : ∀ a : X, (g' * x' * g'⁻¹) * a * (g' * x' * g'⁻¹)⁻¹ = x' ^ 4 * a * (x' ^ 4)⁻¹ := by
      intro a
      rw [hgx', mul_inv_rev]
      have hz : z₁ * a * z₁⁻¹ = a := by rw [← hcen z₁ hz1 a, mul_assoc, mul_inv_cancel, mul_one]
      calc x' ^ 4 * z₁ * a * (z₁⁻¹ * (x' ^ 4)⁻¹) = x' ^ 4 * (z₁ * a * z₁⁻¹) * (x' ^ 4)⁻¹ := by
            group
        _ = x' ^ 4 * a * (x' ^ 4)⁻¹ := by rw [hz]
    have hB : x' ^ 4 * (x' ^ 3 * y' * z₂) * (x' ^ 4)⁻¹ = x' ^ 3 * (c ^ 4 * y') * z₂ := by
      have hz : z₂ * (x' ^ 4)⁻¹ = (x' ^ 4)⁻¹ * z₂ := (hcen z₂ hz2 _).symm
      have hx34 : x' ^ 4 * x' ^ 3 = x' ^ 3 * x' ^ 4 := (Commute.pow_pow_self x' 4 3).eq
      calc x' ^ 4 * (x' ^ 3 * y' * z₂) * (x' ^ 4)⁻¹ =
          x' ^ 4 * x' ^ 3 * y' * (z₂ * (x' ^ 4)⁻¹) := by group
        _ = x' ^ 3 * (x' ^ 4 * y' * (x' ^ 4)⁻¹) * z₂ := by rw [hz, hx34]; group
        _ = x' ^ 3 * (c ^ 4 * y') * z₂ := by rw [h4]
    have hC : x' ^ 3 * (c ^ 4 * y') * z₂ * (x' ^ 3 * y' * z₂)⁻¹ = c ^ 4 := by
      calc x' ^ 3 * (c ^ 4 * y') * z₂ * (x' ^ 3 * y' * z₂)⁻¹ = x' ^ 3 * c ^ 4 * (x' ^ 3)⁻¹ := by
            group
        _ = c ^ 4 := by rw [hcc4 (x' ^ 3)]; group
    have h2 : g' * c * g'⁻¹ =
        ((g' * x' * g'⁻¹) * (g' * y' * g'⁻¹) * (g' * x' * g'⁻¹)⁻¹) * (g' * y' * g'⁻¹)⁻¹ := by
      rw [hcdef]
      group
    rw [hA, hgy', hB, hC] at h2
    exact h1.symm.trans h2
  have hc1 : c = 1 := by
    have h3 : c ^ 3 = 1 := by
      have : c ^ 4 = c ^ 3 * c := pow_succ c 3
      rw [this] at hc4
      have := congrArg (· * c⁻¹) hc4
      simpa using this.symm
    calc c = c ^ 6 * (c ^ 5)⁻¹ := by group
      _ = 1 := by rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, h3, hc5]; group
  have hx'y' : x' * y' = y' * x' := by
    have : x' * y' * x'⁻¹ * y'⁻¹ = 1 := hc1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  set T : Set X := {x', y'} ∪ (Z : Set X) with hT
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    rintro a (ha | ha) b (hb | hb)
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hx'y'
      · exact hx'y'.symm
      · rfl
    · exact (hcen b hb a)
    · exact (hcen a ha b).symm
    · exact (hcen a ha b).symm
  have hP'T : P' ≤ Subgroup.closure T := by
    intro w hw
    have hπw : π w ∈ (Subgroup.closure ({x', y'} : Set X)).map π := by
      rw [MonoidHom.map_closure, Set.image_pair, hx', hy', ← hEdef, ← hP'E]
      exact ⟨w, hw, rfl⟩
    obtain ⟨u, hu, hπu⟩ := hπw
    have hk : u⁻¹ * w ∈ Z := by
      rw [← hπk, map_mul, map_inv, hπu, inv_mul_cancel]
    have : w = u * (u⁻¹ * w) := by group
    rw [this]
    exact mul_mem (Subgroup.closure_mono Set.subset_union_left hu)
      (Subgroup.subset_closure (Set.mem_union_right _ hk))
  intro a b
  have ha : s' * a * s'⁻¹ ∈ P' := ⟨a, a.2, by simp [MulAut.conj_apply]⟩
  have hb : s' * b * s'⁻¹ ∈ P' := ⟨b, b.2, by simp [MulAut.conj_apply]⟩
  have h := commute_of_mem_closure hTcomm (hP'T ha) (hP'T hb)
  apply Subtype.ext
  have h' : s' * ((a : X) * b) * s'⁻¹ = s' * ((b : X) * a) * s'⁻¹ := by
    calc s' * ((a : X) * b) * s'⁻¹ = (s' * a * s'⁻¹) * (s' * b * s'⁻¹) := by group
      _ = (s' * b * s'⁻¹) * (s' * a * s'⁻¹) := h
      _ = s' * ((b : X) * a) * s'⁻¹ := by group
  simpa using h'

end FivePart

end CFSG.RankThree.PartTwo.KFacts.KS14
