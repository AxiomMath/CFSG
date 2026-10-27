module

public import CFSG.Sporadic.FischerOddCore.Fi22LocalComp

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG CFSG.LocalCores CFSG.LocalAnalysis.ComponentInitial

theorem conj_eq_of_perfect_of_invariant {G : Type*} [Group G] {H : Subgroup G} {Y : Set G}
    (hY : Y.Finite) (hY3 : Y.ncard ≤ 3) (hinv : ∀ c ∈ H, ∀ y ∈ Y, c * y * c⁻¹ ∈ Y)
    {B : Subgroup H} (hB : Group.IsPerfect B) {b : H} (hb : b ∈ B) {y : G} (hy : y ∈ Y) :
    (b : G) * y * (b : G)⁻¹ = y := by
  classical
  have : Finite Y := hY.to_subtype
  let act : MulAction H Y :=
    { smul := fun c x => ⟨(c : G) * x * (c : G)⁻¹, hinv c c.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : H) : G) * (x : G) * ((1 : H) : G)⁻¹ = x
        simp)
      mul_smul := fun c e x => Subtype.ext (by
        show ((c * e : H) : G) * (x : G) * ((c * e : H) : G)⁻¹ =
          (c : G) * ((e : G) * (x : G) * (e : G)⁻¹) * (c : G)⁻¹
        rw [Subgroup.coe_mul]
        group) }
  let f : B →* Equiv.Perm Y := (MulAction.toPermHom H Y).comp B.subtype
  have hsolv : Group.IsSolvable (Equiv.Perm Y) := by
    apply isSolvable_of_card_primeFactors_le_two
    rw [Nat.card_perm, Nat.card_coe_set_eq]
    have h3 := hY3
    generalize Y.ncard = m at h3 ⊢
    interval_cases m
    · simp
    · simp
    · rw [show (2 : ℕ).factorial = 2 from rfl, Nat.Prime.primeFactors Nat.prime_two]
      decide
    · rw [show (3 : ℕ).factorial = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
      decide
  have hRR : ⁅f.range, f.range⁆ = f.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    congr 1
    exact hB.commutator_eq_top
  obtain ⟨n, hn⟩ := hsolv.solvable
  have hle : ∀ m, f.range ≤ derivedSeries (Equiv.Perm Y) m := by
    intro m
    induction m with
    | zero => exact le_top
    | succ m ih =>
      rw [derivedSeries_succ, ← hRR]
      exact Subgroup.commutator_mono ih ih
  have hR : f.range = ⊥ := le_bot_iff.1 (hn ▸ hle n)
  have hfb : f ⟨b, hb⟩ = 1 := by
    have : f ⟨b, hb⟩ ∈ f.range := ⟨⟨b, hb⟩, rfl⟩
    rwa [hR, Subgroup.mem_bot] at this
  have := congrArg (fun σ : Equiv.Perm Y => ((σ ⟨y, hy⟩ : Y) : G)) hfb
  exact this

section NoComp

variable {L M : Type*} [Group L] [Group M]

theorem not_isComponent_of_le_two_group [Finite L] {Q B : Subgroup L} (hQ : IsPGroup 2 Q)
    (hBQ : B ≤ Q) : ¬ IsComponent B := by
  rintro ⟨hq, -⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial B := isQuasisimple_nontrivial hq
  have : Group.IsPerfect B := hq.1
  have hB : IsPGroup 2 B := hQ.to_le hBQ
  have : Group.IsSolvable B := @IsNilpotent.to_isSolvable _ _ hB.isNilpotent
  exact Group.IsPerfect.not_isSolvable B this

theorem not_isComponent_of_surj_selfCentralizing [Finite L] (ρ : L →* M)
    (hρ : Function.Surjective ρ) (hker : ∀ x, ρ x = 1 → x * x = 1) {Q : Subgroup M}
    (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) (hQc : Subgroup.centralizer (Q : Set M) ≤ Q)
    (B : Subgroup L) : ¬ IsComponent B := by
  intro hB
  have hQLn : (Q.comap ρ).Normal := hQn.comap ρ
  have hQL2 : IsPGroup 2 (Q.comap ρ) := fun q => by
    obtain ⟨n, hn⟩ := hQ2 ⟨ρ q, q.2⟩
    refine ⟨n + 1, Subtype.ext ?_⟩
    have h1 : ρ ((q : L) ^ 2 ^ n) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hn
    have h2 := hker _ h1
    rw [SubmonoidClass.coe_pow, pow_succ, pow_mul, sq]
    exact h2
  have hcen : Subgroup.centralizer ((Q.comap ρ : Subgroup L) : Set L) ≤ Q.comap ρ := by
    intro y hy
    show ρ y ∈ Q
    apply hQc
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    obtain ⟨x, rfl⟩ := hρ m
    have := Subgroup.mem_centralizer_iff.1 hy x hm
    rw [← map_mul, ← map_mul, this]
  rcases CFSG.LocalCores.component_normal_subgroup hB hQLn with h | h
  · exact not_isComponent_of_le_two_group hQL2 h hB
  · exact not_isComponent_of_le_two_group hQL2
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 h).trans hcen) hB

theorem not_isComponent_of_hom_solvable [Finite L] (ρ : L →* M)
    (hker : ∀ x, ρ x = 1 → x * x = 1) (hM : Group.IsSolvable M) (B : Subgroup L) :
    ¬ IsComponent B := by
  have hk2 : IsPGroup 2 ρ.ker := fun x => ⟨1, Subtype.ext (by
    rw [SubmonoidClass.coe_pow, pow_one, sq]
    exact hker x (MonoidHom.mem_ker.1 x.2))⟩
  have : Group.IsSolvable ρ.ker := @IsNilpotent.to_isSolvable _ _ hk2.isNilpotent
  have : Group.IsSolvable L := Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ (by
    rw [Subgroup.range_subtype])
  exact not_isComponent_of_isSolvable this

theorem exists_selfCentralizing_of_mulEquiv (e : L ≃* M) {Q : Subgroup M} (hQn : Q.Normal)
    (hQ2 : IsPGroup 2 Q) (hQc : Subgroup.centralizer (Q : Set M) ≤ Q) :
    ∃ Q' : Subgroup L, Q'.Normal ∧ IsPGroup 2 Q' ∧ Subgroup.centralizer (Q' : Set L) ≤ Q' := by
  refine ⟨Q.comap e.toMonoidHom, hQn.comap _, fun q => ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hQ2 ⟨e q, q.2⟩
    refine ⟨n, Subtype.ext (e.injective ?_)⟩
    rw [SubmonoidClass.coe_pow, map_pow, Subgroup.coe_one, map_one]
    exact congrArg Subtype.val hn
  · intro y hy
    show e y ∈ Q
    apply hQc
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have := Subgroup.mem_centralizer_iff.1 hy (e.symm m)
      (by show e (e.symm m) ∈ Q; rwa [MulEquiv.apply_symm_apply])
    have h := congrArg e this
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h

theorem not_isComponent_of_commute {G F : Type*} [Group G] [Finite G] [Group F] {d t : G}
    (hd : d * d = 1) (hdt : t ∈ Subgroup.centralizer ({d} : Set G))
    (κ : ↥(Subgroup.centralizer ({d} : Set G)) →* F) (hκ : Function.Surjective κ)
    (hkerκ : ∀ c, κ c = 1 → (c : G) = 1 ∨ (c : G) = d)
    (hnt : ∀ c : G, c * t * c⁻¹ ≠ d * t)
    (hF : (∃ Q : Subgroup ↥(Subgroup.centralizer ({κ ⟨t, hdt⟩} : Set F)), Q.Normal ∧
        IsPGroup 2 Q ∧ Subgroup.centralizer (Q : Set _) ≤ Q) ∨
      Group.IsSolvable ↥(Subgroup.centralizer ({κ ⟨t, hdt⟩} : Set F)))
    {B : Subgroup ↥(Subgroup.centralizer ({t} : Set G))} (hB : IsComponent B)
    (hBd : ∀ b ∈ B, (b : G) * d = d * (b : G)) : False := by
  let t' : ↥(Subgroup.centralizer ({d} : Set G)) := ⟨t, hdt⟩
  let L : Subgroup ↥(Subgroup.centralizer ({d} : Set G)) := Subgroup.centralizer {t'}
  let ρ : ↥L →* ↥(Subgroup.centralizer ({κ t'} : Set F)) :=
    { toFun := fun c => ⟨κ c, by
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.1 c.2]⟩
      map_one' := Subtype.ext (map_one κ)
      map_mul' := fun x y => Subtype.ext (map_mul κ (x : ↥(Subgroup.centralizer ({d} : Set G)))
        (y : ↥(Subgroup.centralizer ({d} : Set G)))) }
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨c, hc⟩ := hκ y
    have hyf := Subgroup.mem_centralizer_singleton_iff.1 y.2
    have hk : κ (c * t' * c⁻¹ * t'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, hyf, mul_inv_cancel_right,
        mul_inv_cancel]
    have hct : c * t' = t' * c := by
      rcases hkerκ _ hk with h | h
      · apply Subtype.ext
        have h' : (c : G) * t * (c : G)⁻¹ * t⁻¹ = 1 := by simpa [t'] using h
        calc (c : G) * t = (c : G) * t * (c : G)⁻¹ * t⁻¹ * (t * (c : G)) := by group
          _ = t * (c : G) := by rw [h', one_mul]
      · exfalso
        have h' : (c : G) * t * (c : G)⁻¹ * t⁻¹ = d := by simpa [t'] using h
        apply hnt c
        calc (c : G) * t * (c : G)⁻¹ = (c : G) * t * (c : G)⁻¹ * t⁻¹ * t := by group
          _ = d * t := by rw [h']
    exact ⟨⟨c, Subgroup.mem_centralizer_singleton_iff.2 hct⟩, Subtype.ext hc⟩
  have hker : ∀ x, ρ x = 1 → x * x = 1 := fun x hx => by
    have h1 : κ (x : ↥(Subgroup.centralizer ({d} : Set G))) = 1 := congrArg Subtype.val hx
    apply Subtype.ext
    apply Subtype.ext
    show ((x : ↥(Subgroup.centralizer ({d} : Set G))) : G) *
      ((x : ↥(Subgroup.centralizer ({d} : Set G))) : G) = 1
    rcases hkerκ _ h1 with h | h
    · rw [h, one_mul]
    · rw [h, hd]
  let W : Subgroup ↥(Subgroup.centralizer ({t} : Set G)) :=
    (Subgroup.centralizer ({d} : Set G)).comap (Subgroup.centralizer ({t} : Set G)).subtype
  have hBW : B ≤ W := fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hBd b hb)
  let φ : ↥W ≃* ↥L :=
    { toFun := fun w => ⟨⟨(w : G), w.2⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 w.1.2))⟩
      invFun := fun c => ⟨⟨((c : ↥(Subgroup.centralizer ({d} : Set G))) : G),
        Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 c.2))⟩, c.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hBL := isComponent_map_mulEquiv φ (CFSG.LocalCores.component_overgroup hB hBW)
  rcases hF with ⟨Q, hQn, hQ2, hQc⟩ | hsolv
  · exact not_isComponent_of_surj_selfCentralizing ρ hρ hker hQn hQ2 hQc _ hBL
  · exact not_isComponent_of_hom_solvable ρ hker hsolv _ hBL

end NoComp

end CFSG.Sporadic.FischerOddCore
