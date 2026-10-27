module

public import CFSG.Quasithin.H13.A5W1622c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def ModelFix {X N : Type*} [Group X] [Group N] (act : X →* MulAut N)
    (S₀ : Subgroup X) : Prop :=
  ∀ n p : N, n ≠ 1 → p ≠ 1 → (∀ s ∈ S₀, act s n = n) → (∀ s ∈ S₀, act s p = p) →
    ∀ x : X, act x n = n → act x p = p

theorem modelFix_of_center {X N : Type*} [Group X] [Group N] {act : X →* MulAut N}
    {S₀ : Subgroup X}
    (h : ∀ n p : N, n ≠ 1 → p ≠ 1 → (∀ s ∈ S₀, act s n = n) → (∀ s ∈ S₀, act s p = p) →
      ∃ c ∈ Subgroup.center X, n = act c p) : ModelFix act S₀ := by
  intro n p hn hp hnS hpS x hx
  obtain ⟨c, hc, rfl⟩ := h n p hn hp hnS hpS
  have hcomm : x * c = c * x := Subgroup.mem_center_iff.mp hc x
  rw [← MulAut.mul_apply, ← map_mul, hcomm, map_mul, MulAut.mul_apply] at hx
  exact (act c).injective hx

theorem exists_fixed_ne_one_of_isPGroup {N : Type*} [Group N] [Finite N]
    {F : Subgroup (MulAut N)} (hF : IsPGroup 2 F) {W : Subgroup N} (hW : 2 ∣ Nat.card W)
    (hWF : ∀ φ ∈ F, ∀ w ∈ W, φ w ∈ W) : ∃ w ∈ W, w ≠ 1 ∧ ∀ φ ∈ F, φ w = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Sm : SubMulAction F N :=
    { carrier := W
      smul_mem' := fun φ w hw => hWF φ φ.2 w hw }
  have hcard : Nat.card ↥Sm = Nat.card W := rfl
  have h1 : (⟨1, W.one_mem⟩ : ↥Sm) ∈ MulAction.fixedPoints F ↥Sm := by
    intro φ
    apply Subtype.ext
    show (φ : MulAut N) 1 = 1
    exact map_one _
  obtain ⟨⟨w, hw⟩, hwfix, hne⟩ :=
    hF.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥Sm (hcard ▸ hW) h1
  refine ⟨w, hw, fun h => hne (Subtype.ext h.symm), fun φ hφ => ?_⟩
  have := hwfix ⟨φ, hφ⟩
  exact congrArg Subtype.val this

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem fixed_of_modelFix {K₀ Y S A Zc : Subgroup G}
    (hZc : Zc ≤ Subgroup.centralizer (K₀ : Set G))
    {X N : Type} [Group X] [Finite X] [Group N] [Finite N] (hN2 : ∀ n : N, n ^ 2 = 1)
    (act : X →* MulAut N) {S₀ : Subgroup X} (hS₀ : IsSylowTwoOf S₀ ⊤) (hFix : ModelFix act S₀)
    (α : ↥K₀ →* X) (hα : Function.Surjective α) (β : ↥A →* N) (hβk : β.ker = Zc.subgroupOf A)
    (hβe : ∀ (ℓ : ↥K₀) (u v : ↥A), (v : G) = ℓ * u * ℓ⁻¹ → β v = act (α ℓ) (β u))
    (hS : IsSylowTwoOf S K₀) (hYK : Y ≤ K₀) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    {y p : G} (hy : y ∈ Y) (hp : p ∈ A) (hq : y * p * y⁻¹ ∈ A)
    (hpq : y * p * y⁻¹ * p⁻¹ ∉ Zc) (hSp : ∀ s ∈ S, s * p * s⁻¹ = p) :
    ∀ m ∈ A, (∀ l ∈ Y, l * m * l⁻¹ = m) → ∀ k ∈ K₀, k * m * k⁻¹ = m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyK : y ∈ K₀ := hYK hy
  have hβ1 : ∀ (w : G) (hw : w ∈ A), β ⟨w, hw⟩ = 1 ↔ w ∈ Zc := by
    intro w hw
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  intro m hm hmY k hk
  by_cases hmZ : m ∈ Zc
  · rw [Subgroup.mem_centralizer_iff.mp (hZc hmZ) k hk, mul_inv_cancel_right]
  exfalso
  let W : Subgroup N :=
    { carrier := {n | ∀ l : ↥K₀, (l : G) ∈ Y → act (α l) n = n}
      mul_mem' := fun {a b} ha hb l hl => by rw [map_mul, ha l hl, hb l hl]
      one_mem' := fun l _ => map_one _
      inv_mem' := fun {a} ha l hl => by rw [map_inv, ha l hl] }
  have hmW : β ⟨m, hm⟩ ∈ W := by
    intro l hl
    exact (hβe l ⟨m, hm⟩ ⟨m, hm⟩ (hmY l hl).symm).symm
  have hm1 : β ⟨m, hm⟩ ≠ 1 := fun h => hmZ ((hβ1 m hm).mp h)
  have hN2' : IsPGroup 2 N := fun n => ⟨1, by rw [pow_one]; exact hN2 n⟩
  have hW2 : 2 ∣ Nat.card W := by
    obtain ⟨k', hk'⟩ := IsPGroup.iff_card.mp (hN2'.to_subgroup W)
    have hne : Nat.card W ≠ 1 := by
      intro h
      have := (Subgroup.card_eq_one.mp h)
      have hmem : β ⟨m, hm⟩ ∈ (⊥ : Subgroup N) := this ▸ hmW
      exact hm1 hmem
    rw [hk'] at hne ⊢
    rcases k' with _ | k'
    · exact absurd rfl hne
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k')
  set F : Subgroup (MulAut N) := ((S.subgroupOf K₀).map α).map act with hFdef
  have hF2 : IsPGroup 2 F := by
    have h1 : IsPGroup 2 ↥(S.subgroupOf K₀) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    exact (h1.map α).map act
  have hWF : ∀ φ ∈ F, ∀ w ∈ W, φ w ∈ W := by
    rintro φ ⟨x, ⟨t, ht, rfl⟩, rfl⟩ w hw l hl
    have htS : (t : G) ∈ S := ht
    have hlt : (t : G)⁻¹ * l * t ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hSY htS)) l).mp hl
      simpa using this
    have hlK : (t : G)⁻¹ * l * t ∈ K₀ := hYK hlt
    have e : l = t * ⟨(t : G)⁻¹ * l * t, hlK⟩ * t⁻¹ := Subtype.ext (by simp; group)
    have hw' := hw ⟨_, hlK⟩ hlt
    show act (α l) (act (α t) w) = act (α t) w
    rw [e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [hw']
  obtain ⟨n, hnW, hn1, hnF⟩ := exists_fixed_ne_one_of_isPGroup hF2 hW2 hWF
  have hSsyl : IsSylowTwoOf (S.subgroupOf K₀) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    · have := hS.2.2
      rwa [show ((S.subgroupOf K₀).subgroupOf ⊤).index = (S.subgroupOf K₀).index from
        Subgroup.relIndex_top_right _]
  have hαS := isSylowTwoOf_map_top α hα hSsyl
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hαS hS₀
  have hmemS₀ : ∀ s ∈ S₀, ∃ t : ↥K₀, (t : G) ∈ S ∧ s = g * α t * g⁻¹ := by
    intro s hs
    rw [← hg] at hs
    obtain ⟨s', ⟨t, ht, rfl⟩, rfl⟩ := hs
    exact ⟨t, ht, rfl⟩
  have hact_conj : ∀ (h : X) (n' : N), act (g * h * g⁻¹) (act g n') = act g (act h n') := by
    intro h n'
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, map_inv, MulAut.inv_apply_self]
  have hbp1 : β ⟨p, hp⟩ ≠ 1 := by
    intro h
    have hpZ : p ∈ Zc := (hβ1 p hp).mp h
    apply hpq
    rw [Subgroup.mem_centralizer_iff.mp (hZc hpZ) y hyK, mul_inv_cancel_right, mul_inv_cancel]
    exact Zc.one_mem
  have hyfix : act (α ⟨y, hyK⟩) (β ⟨p, hp⟩) = β ⟨p, hp⟩ := by
    have h := hFix (act g n) (act g (β ⟨p, hp⟩))
      (fun h => hn1 ((MulEquiv.map_eq_one_iff _).mp h))
      (fun h => hbp1 ((MulEquiv.map_eq_one_iff _).mp h))
      (by
        intro s hs
        obtain ⟨t, ht, rfl⟩ := hmemS₀ s hs
        rw [hact_conj]
        exact congrArg (act g) (hnF _ ⟨α t, ⟨t, ht, rfl⟩, rfl⟩))
      (by
        intro s hs
        obtain ⟨t, ht, rfl⟩ := hmemS₀ s hs
        rw [hact_conj, ← hβe t ⟨p, hp⟩ ⟨p, hp⟩ (hSp t ht).symm])
      (g * α ⟨y, hyK⟩ * g⁻¹) (by rw [hact_conj, hnW ⟨y, hyK⟩ hy])
    rw [hact_conj] at h
    exact (act g).injective h
  apply hpq
  have hpqA : y * p * y⁻¹ * p⁻¹ ∈ A := A.mul_mem hq (A.inv_mem hp)
  rw [← hβ1 _ hpqA]
  have e : (⟨y * p * y⁻¹ * p⁻¹, hpqA⟩ : ↥A) = ⟨y * p * y⁻¹, hq⟩ * (⟨p, hp⟩)⁻¹ := rfl
  rw [e, map_mul, map_inv, hβe ⟨y, hyK⟩ ⟨p, hp⟩ ⟨y * p * y⁻¹, hq⟩ rfl, hyfix, mul_inv_cancel]

end Transfer

end CFSG.Quasithin.H13.A5
