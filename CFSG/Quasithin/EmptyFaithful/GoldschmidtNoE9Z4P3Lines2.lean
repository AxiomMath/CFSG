module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P3Lines

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace E9P2.Lines

section Perm

theorem perm4_ne : ∀ (τ π : Equiv.Perm (Fin 4)), (∀ i, τ i ≠ i) → τ * τ = 1 → π ^ 3 = 1 →
    π ≠ 1 → π * τ * π⁻¹ ≠ τ := by decide

theorem perm4_comm : ∀ (τ π : Equiv.Perm (Fin 4)), (∀ i, τ i ≠ i) → τ * τ = 1 → π ^ 3 = 1 →
    π ≠ 1 → π * τ * π⁻¹ * τ = τ * (π * τ * π⁻¹) := by decide

variable {α : Type*} [Finite α]

theorem perm_key (hα : Nat.card α = 4) {τ π : Equiv.Perm α} (hfpf : ∀ i, τ i ≠ i)
    (hτ : τ * τ = 1) (hπ3 : π ^ 3 = 1) (hπ1 : π ≠ 1) :
    π * τ * π⁻¹ ≠ τ ∧ π * τ * π⁻¹ * τ = τ * (π * τ * π⁻¹) := by
  have : Fintype α := Fintype.ofFinite α
  have hcard : Fintype.card α = 4 := by rw [← Nat.card_eq_fintype_card, hα]
  let e : α ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  let φ : Equiv.Perm α ≃* Equiv.Perm (Fin 4) := e.permCongrHom
  have h1 : φ π ≠ 1 := fun h => hπ1 (φ.injective (by rw [h, map_one]))
  have hf : ∀ j, φ τ j ≠ j := fun j h => by
    apply hfpf (e.symm j)
    have h' : e (τ (e.symm j)) = j := h
    exact e.injective (by rw [h', Equiv.apply_symm_apply])
  have h2 : φ τ * φ τ = 1 := by rw [← map_mul, hτ, map_one]
  have h3 : φ π ^ 3 = 1 := by rw [← map_pow, hπ3, map_one]
  refine ⟨fun h => perm4_ne (φ τ) (φ π) hf h2 h3 h1 ?_, φ.injective ?_⟩
  · simp only [← map_inv, ← map_mul, h]
  · have := perm4_comm (φ τ) (φ π) hf h2 h3 h1
    simpa only [← map_inv, ← map_mul] using this

end Perm

section Sylow

variable {N P : Type*} [Group N] [Finite N] [Group P]

theorem card_le_of_isPGroup_range (f : N →* P) {T : Subgroup N} (hT : IsSylowTwoOf T ⊤)
    {V : Subgroup P} (hV : V ≤ f.range) (hV2 : IsPGroup 2 V) :
    Nat.card V ≤ Nat.card (T.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have : Finite f.range := Finite.of_surjective _ hf
  have hidx : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.2.2
  let Q : Sylow 2 f.range := (hT.2.1.toSylow hidx).mapSurjective hf
  obtain ⟨Q', hQ'⟩ := (hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hV).symm).exists_le_sylow
  have hmap : (T.map f.rangeRestrict).map f.range.subtype = T.map f := by
    rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
  calc Nat.card V = Nat.card (V.subgroupOf f.range) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv.symm
    _ ≤ Nat.card Q' := Subgroup.card_le_of_le hQ'
    _ = Nat.card Q := by rw [Q'.card_eq_multiplicity, Q.card_eq_multiplicity]
    _ = Nat.card (T.map f.rangeRestrict) := rfl
    _ = Nat.card (T.map f) := by
        rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

end Sylow

section Odd

variable {N α : Type*} [Group N] [Finite N] [Finite α]

theorem odd_acts_trivially_on_lines (hα : Nat.card α = 4) (ρ : N →* Equiv.Perm α)
    {T : Subgroup N} (hT : IsSylowTwoOf T ⊤) {τ : N} (hτ : τ ∈ T) (hfpf : ∀ i, ρ τ i ≠ i)
    (hT' : ∀ t ∈ T, ρ t = 1 ∨ ρ t = ρ τ) : ∀ x : N, ¬ 2 ∣ orderOf x → ρ x = 1 := by
  classical
  intro x hx
  by_contra hρ
  have hne : Nonempty α := Nat.card_pos_iff.mp (by omega) |>.1
  have hπ3 : ρ x ^ 3 = 1 := by
    have hcard : Nat.card (Equiv.Perm α) = 24 := by
      rw [Nat.card_perm, hα]
      rfl
    have hd1 : orderOf (ρ x) ∣ 24 := hcard ▸ orderOf_dvd_natCard (ρ x)
    have hodd : ¬ 2 ∣ orderOf (ρ x) := fun h2 => hx (h2.trans (orderOf_map_dvd ρ x))
    have hmem : orderOf (ρ x) ∈ Nat.divisors 24 := Nat.mem_divisors.mpr ⟨hd1, by norm_num⟩
    have h24 : Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} := by decide
    rw [h24] at hmem
    have h13 : orderOf (ρ x) = 1 ∨ orderOf (ρ x) = 3 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    rcases h13 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hρ
    · rw [← h]; exact pow_orderOf_eq_one _
  have ha1 : ρ τ ≠ 1 := fun h => by
    obtain ⟨i⟩ := hne
    exact hfpf i (by rw [h]; rfl)
  have ha2 : ρ τ * ρ τ = 1 := by
    rcases hT' (τ * τ) (T.mul_mem hτ hτ) with h | h
    · rw [← map_mul, h]
    · exfalso
      rw [map_mul] at h
      exact ha1 (by simpa using h)
  obtain ⟨hba, hab⟩ := perm_key hα hfpf ha2 hπ3 hρ
  set a := ρ τ with ha
  set b := ρ x * a * (ρ x)⁻¹ with hb
  have hbr : b ∈ ρ.range := ⟨x * τ * x⁻¹, by simp [hb, ha]⟩
  have hb2 : b * b = 1 := by
    calc b * b = ρ x * (a * a) * (ρ x)⁻¹ := by simp only [hb, mul_assoc, inv_mul_cancel_left]
      _ = 1 := by rw [ha2]; simp
  have hb1 : b ≠ 1 := fun h => ha1 (by
    calc a = (ρ x)⁻¹ * b * ρ x := by simp [hb, mul_assoc]
      _ = 1 := by rw [h]; simp)
  have hT2 : Nat.card (T.map ρ) ≤ 2 := by
    have hsub : ((T.map ρ : Subgroup (Equiv.Perm α)) : Set (Equiv.Perm α)) ⊆ {1, a} := by
      rintro _ ⟨t, ht, rfl⟩
      rcases hT' t ht with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, a} : Set (Equiv.Perm α)).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by simp [Set.ncard_singleton])
    calc Nat.card (T.map ρ) = ((T.map ρ : Subgroup (Equiv.Perm α)) : Set (Equiv.Perm α)).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ 2 := h1.trans h2
  let V : Subgroup (Equiv.Perm α) := Subgroup.closure {a, b}
  have hVr : V ≤ ρ.range := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨τ, rfl⟩
    · exact hbr
  have hcomm : IsMulCommutative V := Subgroup.isMulCommutative_closure (by
    intro u hu v hv _
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Commute.refl _
    · exact hab.symm
    · exact hab
    · exact Commute.refl _)
  have hsq : ∀ u ∈ V, u * u = 1 := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem u hu => rcases hu with rfl | rfl <;> assumption
    | one => simp
    | mul u v hu hv ihu ihv =>
      have huv : u * v = v * u := setLike_mul_comm (s := V) hu hv
      calc u * v * (u * v) = u * (v * u) * v := by simp only [mul_assoc]
        _ = u * (u * v) * v := by rw [← huv]
        _ = (u * u) * (v * v) := by simp only [mul_assoc]
        _ = 1 := by rw [ihu, ihv, one_mul]
    | inv u hu ihu => rw [← mul_inv_rev, ihu, inv_one]
  have hV2 : IsPGroup 2 V := fun u => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hsq u u.2⟩
  have h3 : 3 ≤ Nat.card V := by
    have hsub : ({1, a, b} : Set (Equiv.Perm α)) ⊆ (V : Set (Equiv.Perm α)) := by
      rintro _ (rfl | rfl | rfl)
      · exact V.one_mem
      · exact Subgroup.subset_closure (Or.inl rfl)
      · exact Subgroup.subset_closure (Or.inr rfl)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, a, b} : Set (Equiv.Perm α)).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨1, a, b, ha1.symm, hb1.symm, hba.symm, rfl⟩
    calc 3 = ({1, a, b} : Set (Equiv.Perm α)).ncard := h2.symm
      _ ≤ (V : Set (Equiv.Perm α)).ncard := h1
      _ = Nat.card V := (Nat.card_coe_set_eq _).symm
  have := card_le_of_isPGroup_range ρ hT hVr hV2
  omega

end Odd

section Centralizes

variable {Y : Type*} [Group Y]

theorem isSylowTwoOf_top_subgroupOf {P K : Subgroup Y} (hP : IsSylowTwoOf P K) :
    IsSylowTwoOf (P.subgroupOf K) ⊤ := by
  refine ⟨le_top, hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm, ?_⟩
  have h : ((P.subgroupOf K).subgroupOf (⊤ : Subgroup K)).index = (P.subgroupOf K).index :=
    Subgroup.relIndex_top_right (P.subgroupOf K)
  rw [h]
  exact hP.2.2

theorem conjSub_sq_eq {K : Subgroup Y} {σ : Y} (hσ2 : ∀ k ∈ K, σ ^ 2 * k * σ⁻¹ ^ 2 = k⁻¹)
    {A : Subgroup Y} (hA : A ≤ K) : conjSub (σ ^ 2) A = A := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h1 : (MulAut.conj (σ ^ 2)).toMonoidHom a = a⁻¹ := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← inv_pow]
      exact hσ2 a (hA ha)
    rw [h1]
    exact A.inv_mem ha
  · intro hy
    refine ⟨y⁻¹, A.inv_mem hy, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← inv_pow, hσ2 _ (hA (A.inv_mem hy)), inv_inv]

theorem conjSub_pow_even {K : Subgroup Y} {σ : Y} (hσ2 : ∀ k ∈ K, σ ^ 2 * k * σ⁻¹ ^ 2 = k⁻¹)
    {A : Subgroup Y} (hA : A ≤ K) (m : ℕ) : conjSub (σ ^ (2 * m)) A = A := by
  induction m with
  | zero => simp [conjSub_one]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, conjSub_mul, conjSub_sq_eq hσ2 hA, ih]

theorem odd_order_centralizes_of_lines [Finite Y] {K T N : Subgroup Y} (h9 : Nat.card K = 9)
    (hexp : ∀ k ∈ K, k ^ 3 = 1) (hKN : N ≤ Subgroup.normalizer (K : Set Y))
    (hT : IsSylowTwoOf T N) {σ : Y} (hσ : σ ∈ T) (hσ2 : ∀ k ∈ K, σ ^ 2 * k * σ⁻¹ ^ 2 = k⁻¹)
    (hTK : ∀ t ∈ T, ∃ i : ℕ, ∀ k ∈ K, t * k * t⁻¹ = σ ^ i * k * σ⁻¹ ^ i) :
    ∀ x ∈ N, ¬ 2 ∣ orderOf x → ∀ k ∈ K, x * k * x⁻¹ = k := by
  have hcard := card_lines h9 hexp
  have : Finite (lines K) := Nat.finite_of_card_ne_zero (by omega)
  let ρ : ↥N →* Equiv.Perm (lines K) := (linePermHom K).comp (Subgroup.inclusion hKN)
  have hρ : ∀ (n : ↥N) (A : lines K), ((ρ n A : lines K) : Subgroup Y) = conjSub (n : Y) A :=
    fun _ _ => rfl
  let τ : ↥N := ⟨σ, hT.1 hσ⟩
  have hfpf : ∀ A, ρ τ A ≠ A := fun A h =>
    moves_line_of_sq_inverts hexp hσ2 A.2 (by rw [← hρ τ A, h])
  have hT'' : ∀ t ∈ T.subgroupOf N, ρ t = 1 ∨ ρ t = ρ τ := by
    intro t ht
    obtain ⟨i, hi⟩ := hTK t ht
    have hconj : ∀ A : lines K, conjSub (t : Y) A = conjSub (σ ^ i) A := by
      intro A
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨a, ha, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply, hi a (A.2.1 ha), inv_pow]
      · rintro ⟨a, ha, rfl⟩
        refine ⟨a, ha, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply, hi a (A.2.1 ha), inv_pow]
    rcases Nat.even_or_odd' i with ⟨m, rfl | rfl⟩
    · left
      refine Equiv.ext fun A => Subtype.ext ?_
      rw [hρ, hconj, conjSub_pow_even hσ2 A.2.1]
      rfl
    · right
      refine Equiv.ext fun A => Subtype.ext ?_
      rw [hρ, hρ, hconj, pow_succ', conjSub_mul, conjSub_pow_even hσ2 A.2.1]
  have hodd := odd_acts_trivially_on_lines hcard ρ (isSylowTwoOf_top_subgroupOf hT)
    (show τ ∈ T.subgroupOf N from hσ) hfpf hT''
  intro x hxN hx
  apply centralizes_of_fixes_lines hexp hx
  intro A hA
  have h1 := hodd ⟨x, hxN⟩ (by rwa [Subgroup.orderOf_mk])
  have h2 := congrArg (fun p : Equiv.Perm (lines K) => ((p ⟨A, hA⟩ : lines K) : Subgroup Y)) h1
  exact h2

end Centralizes

end E9P2.Lines

end CFSG.Quasithin
