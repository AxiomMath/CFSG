module

public import CFSG.Quasithin.Recognition.CertF6Bridge
public import CFSG.Quasithin.Recognition.CertTwoLocal

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open CFSG.QuasithinUnique

structure TwoLocalLattice (N : Type*) [Group N] where
  S : Subgroup N
  P₁ : Subgroup N
  P₂ : Subgroup N
  sylow : IsPGroup 2 S ∧ ¬ 2 ∣ S.index
  lattice : ∀ H : Subgroup N, S ≤ H → H = S ∨ H = P₁ ∨ H = P₂ ∨ H = ⊤
  S_le_P₁ : S ≤ P₁
  S_le_P₂ : S ≤ P₂
  S_ne_P₁ : S ≠ P₁
  S_ne_P₂ : S ≠ P₂
  P₁_not_le_P₂ : ¬ P₁ ≤ P₂
  P₂_not_le_P₁ : ¬ P₂ ≤ P₁
  O₂ : ∀ Q : Subgroup N, Q.Normal → IsPGroup 2 Q → Q = ⊥
  loc₁ : ∃ Q : Subgroup N, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ P₁ ≤ Subgroup.normalizer (Q : Set N)
  loc₂ : ∃ Q : Subgroup N, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ P₂ ≤ Subgroup.normalizer (Q : Set N)
  normS : Subgroup.normalizer (S : Set N) ≤ S

private theorem map_symm_map_lattice {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (M : Subgroup G) : (M.map φ.toMonoidHom).map φ.symm.toMonoidHom = M := by
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    simpa using hm
  · intro hg
    exact ⟨φ g, ⟨g, hg, rfl⟩, by simp⟩

namespace TwoLocalLattice

variable {N : Type*} [Group N] (L : TwoLocalLattice N)

include L

theorem not_isTwoLocal_top : ¬ IsTwoLocal (⊤ : Subgroup N) := by
  rintro ⟨Q, hQ, hQp, hQeq⟩
  exact hQ (L.O₂ Q (Subgroup.normalizer_eq_top_iff.1 hQeq.symm) hQp)

theorem isTwoLocal_P₁ : IsTwoLocal L.P₁ := by
  obtain ⟨Q, hQ, hQp, hle⟩ := L.loc₁
  refine ⟨Q, hQ, hQp, ?_⟩
  rcases L.lattice _ (L.S_le_P₁.trans hle) with h | h | h | h
  · exact absurd (le_antisymm L.S_le_P₁ (h ▸ hle)) L.S_ne_P₁
  · exact h.symm
  · exact absurd (h ▸ hle) L.P₁_not_le_P₂
  · exact absurd (Subgroup.normalizer_eq_top_iff.1 h) (fun hn => hQ (L.O₂ Q hn hQp))

theorem isTwoLocal_P₂ : IsTwoLocal L.P₂ := by
  obtain ⟨Q, hQ, hQp, hle⟩ := L.loc₂
  refine ⟨Q, hQ, hQp, ?_⟩
  rcases L.lattice _ (L.S_le_P₂.trans hle) with h | h | h | h
  · exact absurd (le_antisymm L.S_le_P₂ (h ▸ hle)) L.S_ne_P₂
  · exact absurd (h ▸ hle) L.P₂_not_le_P₁
  · exact h.symm
  · exact absurd (Subgroup.normalizer_eq_top_iff.1 h) (fun hn => hQ (L.O₂ Q hn hQp))

theorem isMaximalTwoLocal_P₁ : IsMaximalTwoLocal L.P₁ := by
  refine ⟨L.isTwoLocal_P₁, fun M' hM' hle => ?_⟩
  rcases L.lattice _ (L.S_le_P₁.trans hle) with h | h | h | h
  · exact absurd (le_antisymm L.S_le_P₁ (h ▸ hle)) L.S_ne_P₁
  · exact h
  · exact absurd (h ▸ hle) L.P₁_not_le_P₂
  · exact absurd (h ▸ hM') L.not_isTwoLocal_top

theorem isMaximalTwoLocal_P₂ : IsMaximalTwoLocal L.P₂ := by
  refine ⟨L.isTwoLocal_P₂, fun M' hM' hle => ?_⟩
  rcases L.lattice _ (L.S_le_P₂.trans hle) with h | h | h | h
  · exact absurd (le_antisymm L.S_le_P₂ (h ▸ hle)) L.S_ne_P₂
  · exact absurd (h ▸ hle) L.P₂_not_le_P₁
  · exact h
  · exact absurd (h ▸ hM') L.not_isTwoLocal_top

theorem eq_P₁_or_P₂_of_maxTwoLocal {M : Subgroup N} (hM : IsMaximalTwoLocal M) (hS : L.S ≤ M) :
    M = L.P₁ ∨ M = L.P₂ := by
  rcases L.lattice M hS with h | h | h | h
  · exfalso
    have hA := hM.2 L.P₁ L.isTwoLocal_P₁ (by rw [h]; exact L.S_le_P₁)
    exact L.S_ne_P₁ (by rw [← h, hA])
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (h ▸ hM.1) L.not_isTwoLocal_top

theorem isYAmalgamPair_S {K₁ K₂ : Subgroup N} (h₁ : IsMaximalTwoLocal K₁)
    (h₂ : IsMaximalTwoLocal K₂) (hne : K₁ ≠ K₂) (hS₁ : L.S ≤ K₁) (hS₂ : L.S ≤ K₂) :
    IsYAmalgamPair L.S K₁ K₂ := by
  refine ⟨⟨le_top, L.sylow.1, ?_⟩, hne, fun M => ⟨?_, ?_⟩⟩
  · have e1 : (L.S.subgroupOf ⊤).index = L.S.index := Subgroup.relIndex_top_right L.S
    rw [e1]
    exact L.sylow.2
  · rintro ⟨hM, hN⟩
    have hSM : L.S ≤ M := le_trans Subgroup.le_normalizer hN
    rcases L.eq_P₁_or_P₂_of_maxTwoLocal hM hSM with hM' | hM' <;>
    rcases L.eq_P₁_or_P₂_of_maxTwoLocal h₁ hS₁ with h1 | h1 <;>
    rcases L.eq_P₁_or_P₂_of_maxTwoLocal h₂ hS₂ with h2 | h2 <;>
    first
      | exact absurd (h1.trans h2.symm) hne
      | exact Or.inl (hM'.trans h1.symm)
      | exact Or.inr (hM'.trans h2.symm)
  · rintro (rfl | rfl)
    · exact ⟨h₁, L.normS.trans hS₁⟩
    · exact ⟨h₂, L.normS.trans hS₂⟩

theorem twoLocalPairProp [Finite N] : TwoLocalPairProp N := by
  intro S' K₁ K₂ hS h₁ h₂ hne hS₁ hS₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp', hidx'⟩ := hS
  have e1 : (S'.subgroupOf ⊤).index = S'.index := Subgroup.relIndex_top_right S'
  have hidx : ¬ 2 ∣ S'.index := by rwa [e1] at hidx'
  let S₀ : Sylow 2 N := L.sylow.1.toSylow L.sylow.2
  let S'' : Sylow 2 N := hp'.toSylow hidx
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq N S₀ S''
  have hk' : MulAut.conj k • L.S = S' := by
    have h1 := congrArg (fun P : Sylow 2 N => (P : Subgroup N)) hk
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hSmap : S' = L.S.map (MulAut.conj k).toMonoidHom := by
    rw [← hk']
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  let φ : N ≃* N := (MulAut.conj k).symm
  have hSφ : S'.map φ.toMonoidHom = L.S := by
    rw [hSmap]
    exact map_symm_map_lattice (MulAut.conj k) L.S
  have hK₁ : IsMaximalTwoLocal (K₁.map φ.toMonoidHom) := isMaximalTwoLocal_map φ h₁
  have hK₂ : IsMaximalTwoLocal (K₂.map φ.toMonoidHom) := isMaximalTwoLocal_map φ h₂
  have hT₁ : L.S ≤ K₁.map φ.toMonoidHom := by
    rw [← hSφ]
    exact Subgroup.map_mono hS₁
  have hT₂ : L.S ≤ K₂.map φ.toMonoidHom := by
    rw [← hSφ]
    exact Subgroup.map_mono hS₂
  have hne' : K₁.map φ.toMonoidHom ≠ K₂.map φ.toMonoidHom := fun h =>
    hne (Subgroup.map_injective φ.injective h)
  have hpair := L.isYAmalgamPair_S hK₁ hK₂ hne' hT₁ hT₂
  have hh := IsYAmalgamPair.map φ.symm hpair
  rw [map_symm_map_lattice φ K₁, map_symm_map_lattice φ K₂] at hh
  have hTS : L.S.map φ.symm.toMonoidHom = S' := by
    rw [hSmap]
    rfl
  rw [hTS] at hh
  exact hh

end TwoLocalLattice

structure IndexTwoCore {J N : Type*} [Group J] [Group N] (f : J →* N) (ρ : N) (Φ : J ≃* J) :
    Prop where
  sq : ρ * ρ = 1
  conj : ∀ x, ρ * f x * ρ⁻¹ = f (Φ x)

structure IndexTwoData {J N : Type*} [Group J] [Group N] (f : J →* N) (ρ : N) (Φ : J ≃* J) :
    Prop extends IndexTwoCore f ρ Φ where
  inj : Function.Injective f
  cover : ∀ g : N, g ∈ f.range ∨ g * ρ ∈ f.range
  outer : ¬ ∃ w : J, ∀ x, Φ x = w * x * w⁻¹

namespace IndexTwoCore

variable {J N : Type*} [Group J] [Group N] {f : J →* N} {ρ : N} {Φ : J ≃* J}
  (C : IndexTwoCore f ρ Φ)

include C

theorem rho_inv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right C.sq

theorem conj' (x : J) : ρ * f x * ρ = f (Φ x) := by
  have := C.conj x
  rwa [C.rho_inv] at this

@[expose] def ext (H₀ : Subgroup J) (hH : ∀ x ∈ H₀, Φ x ∈ H₀) : Subgroup N where
  carrier := {g | g ∈ H₀.map f ∨ g * ρ ∈ H₀.map f}
  one_mem' := Or.inl (Subgroup.one_mem _)
  mul_mem' := by
    have hn : ∀ g ∈ H₀.map f, ρ * g * ρ ∈ H₀.map f := by
      rintro _ ⟨x, hx, rfl⟩
      rw [C.conj' x]
      exact ⟨Φ x, hH x hx, rfl⟩
    rintro g g' (hg | hg) (hg' | hg')
    · exact Or.inl (Subgroup.mul_mem _ hg hg')
    · refine Or.inr ?_
      rw [mul_assoc]
      exact Subgroup.mul_mem _ hg hg'
    · refine Or.inr ?_
      have e : g * g' * ρ = (g * ρ) * (ρ * g' * ρ) := by
        calc g * g' * ρ = g * (ρ * ρ) * g' * ρ := by rw [C.sq, mul_one]
          _ = (g * ρ) * (ρ * g' * ρ) := by simp only [mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ hg (hn g' hg')
    · refine Or.inl ?_
      have e : g * g' = (g * ρ) * (ρ * (g' * ρ) * ρ) := by
        calc g * g' = g * (ρ * ρ) * g' * (ρ * ρ) := by rw [C.sq, mul_one, mul_one]
          _ = (g * ρ) * (ρ * (g' * ρ) * ρ) := by simp only [mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ hg (hn _ hg')
  inv_mem' := by
    have hn : ∀ g ∈ H₀.map f, ρ * g * ρ ∈ H₀.map f := by
      rintro _ ⟨x, hx, rfl⟩
      rw [C.conj' x]
      exact ⟨Φ x, hH x hx, rfl⟩
    rintro g (hg | hg)
    · exact Or.inl (Subgroup.inv_mem _ hg)
    · refine Or.inr ?_
      have h1 : ρ * g⁻¹ ∈ H₀.map f := by
        have := Subgroup.inv_mem _ hg
        rwa [mul_inv_rev, C.rho_inv] at this
      have := hn _ h1
      have e : ρ * (ρ * g⁻¹) * ρ = g⁻¹ * ρ := by
        calc ρ * (ρ * g⁻¹) * ρ = (ρ * ρ) * g⁻¹ * ρ := by simp only [mul_assoc]
          _ = g⁻¹ * ρ := by rw [C.sq, one_mul]
      rwa [e] at this

theorem mem_ext {H₀ : Subgroup J} {hH : ∀ x ∈ H₀, Φ x ∈ H₀} {g : N} :
    g ∈ C.ext H₀ hH ↔ g ∈ H₀.map f ∨ g * ρ ∈ H₀.map f := Iff.rfl

theorem map_le_ext {H₀ : Subgroup J} (hH : ∀ x ∈ H₀, Φ x ∈ H₀) : H₀.map f ≤ C.ext H₀ hH :=
  fun _ hg => Or.inl hg

theorem rho_mem_ext {H₀ : Subgroup J} (hH : ∀ x ∈ H₀, Φ x ∈ H₀) : ρ ∈ C.ext H₀ hH :=
  Or.inr (by rw [C.sq]; exact Subgroup.one_mem _)

end IndexTwoCore

namespace IndexTwoData

variable {J N : Type*} [Group J] [Group N] {f : J →* N} {ρ : N} {Φ : J ≃* J}
  (D : IndexTwoData f ρ Φ)

include D

theorem rho_not_mem : ρ ∉ f.range := by
  rintro ⟨w, hw⟩
  apply D.outer
  refine ⟨w, fun x => D.inj ?_⟩
  have := D.conj x
  rw [← hw] at this
  simpa [map_mul, map_inv] using this.symm

theorem index_range : f.range.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨ρ, fun b => ?_⟩
  rcases D.cover b with h | h
  · refine Or.inr ⟨h, fun h' => D.rho_not_mem ?_⟩
    have := f.range.mul_mem (f.range.inv_mem h) h'
    simpa using this
  · refine Or.inl ⟨h, fun h' => D.rho_not_mem ?_⟩
    have := f.range.mul_mem (f.range.inv_mem h') h
    simpa using this

theorem mem_iff_of_rho_mem {H : Subgroup N} (hρ : ρ ∈ H) {g : N} :
    g ∈ H ↔ g ∈ (H.comap f).map f ∨ g * ρ ∈ (H.comap f).map f := by
  constructor
  · intro hg
    rcases D.cover g with ⟨x, rfl⟩ | ⟨x, hx⟩
    · exact Or.inl ⟨x, hg, rfl⟩
    · refine Or.inr ⟨x, ?_, hx⟩
      show f x ∈ H
      rw [hx]
      exact H.mul_mem hg hρ
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, hxg⟩)
    · exact hx
    · have : g = f x * ρ⁻¹ := by rw [hxg]; simp
      rw [this]
      exact H.mul_mem hx (H.inv_mem hρ)

theorem mem_of_map_mem_ext {H₀ : Subgroup J} {hH : ∀ x ∈ H₀, Φ x ∈ H₀} {x : J}
    (hx : f x ∈ D.ext H₀ hH) : x ∈ H₀ := by
  rcases (D.mem_ext).1 hx with ⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩
  · exact D.inj hyx ▸ hy
  · exfalso
    apply D.rho_not_mem
    have : ρ = (f x)⁻¹ * f y := by rw [hyx]; simp
    rw [this]
    exact f.range.mul_mem (f.range.inv_mem ⟨x, rfl⟩) ⟨y, rfl⟩

theorem lattice {ι κ : Type*} {d : OvergroupData J ι κ} (hT : ∀ x ∈ d.T, Φ x ∈ d.T)
    (hA : ∀ x ∈ d.A, Φ x ∈ d.A) (hB : ∀ x ∈ d.B, Φ x ∈ d.B) (H : Subgroup N)
    (hH : D.ext d.T hT ≤ H) :
    H = D.ext d.T hT ∨ H = D.ext d.A hA ∨ H = D.ext d.B hB ∨ H = ⊤ := by
  have hρ : ρ ∈ H := hH (D.rho_mem_ext hT)
  have hTH : d.T ≤ H.comap f := fun t ht => hH (D.map_le_ext hT ⟨t, ht, rfl⟩)
  have key : ∀ (H₀ : Subgroup J) (hH₀ : ∀ x ∈ H₀, Φ x ∈ H₀), H.comap f = H₀ →
      H = D.ext H₀ hH₀ := by
    intro H₀ hH₀ h
    ext g
    rw [D.mem_iff_of_rho_mem hρ, h]
    exact Iff.rfl
  rcases d.lattice (H.comap f) hTH with h | h | h | h
  · exact Or.inl (key _ hT h)
  · exact Or.inr (Or.inl (key _ hA h))
  · exact Or.inr (Or.inr (Or.inl (key _ hB h)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [eq_top_iff]
    intro g _
    rw [D.mem_iff_of_rho_mem hρ, h]
    rcases D.cover g with ⟨x, rfl⟩ | ⟨x, hx⟩
    · exact Or.inl ⟨x, trivial, rfl⟩
    · exact Or.inr ⟨x, trivial, hx⟩

theorem isPGroup_ext {H₀ : Subgroup J} (hH : ∀ x ∈ H₀, Φ x ∈ H₀) (h2 : IsPGroup 2 H₀) :
    IsPGroup 2 (D.ext H₀ hH) := by
  have h2' : IsPGroup 2 (H₀.map f) := h2.map f
  rintro ⟨g, hg⟩
  rcases (D.mem_ext).1 hg with hg1 | hg1
  · obtain ⟨n, hn⟩ := h2' ⟨g, hg1⟩
    have h1 : g ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    exact ⟨n, Subtype.ext (by simpa using h1)⟩
  · have hn' : ρ * (g * ρ) * ρ ∈ H₀.map f := by
      obtain ⟨x, hx, hxg⟩ := hg1
      rw [← hxg, D.conj' x]
      exact ⟨Φ x, hH x hx, rfl⟩
    have e : g * g = (g * ρ) * (ρ * (g * ρ) * ρ) := by
      calc g * g = g * (ρ * ρ) * g * (ρ * ρ) := by rw [D.sq, mul_one, mul_one]
        _ = (g * ρ) * (ρ * (g * ρ) * ρ) := by simp only [mul_assoc]
    have hsq : g * g ∈ H₀.map f := by
      rw [e]
      exact Subgroup.mul_mem _ hg1 hn'
    obtain ⟨n, hn⟩ := h2' ⟨g * g, hsq⟩
    refine ⟨n + 1, Subtype.ext ?_⟩
    have h1 : (g * g) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    show g ^ (2 ^ (n + 1)) = 1
    rw [pow_succ, mul_comm, pow_mul, pow_two]
    exact h1

theorem index_ext_T {ι κ : Type*} {d : OvergroupData J ι κ} (hT : ∀ x ∈ d.T, Φ x ∈ d.T) :
    (D.ext d.T hT).index = d.T.index := by
  have h1 : (d.T.map f).index = d.T.index * 2 := by
    rw [Subgroup.index_map, (MonoidHom.ker_eq_bot_iff f).2 D.inj, sup_bot_eq, D.index_range]
  have h2 : (d.T.map f).relIndex (D.ext d.T hT) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨ρ, D.rho_mem_ext hT, fun b hb => ?_⟩
    rcases (D.mem_ext).1 hb with h | h
    · refine Or.inr ⟨h, fun h' => D.rho_not_mem ?_⟩
      have := f.range.mul_mem (f.range.inv_mem (d.T.map_le_range f h)) (d.T.map_le_range f h')
      simpa using this
    · refine Or.inl ⟨h, fun h' => D.rho_not_mem ?_⟩
      have := f.range.mul_mem (f.range.inv_mem (d.T.map_le_range f h')) (d.T.map_le_range f h)
      simpa using this
  have h3 := Subgroup.relIndex_mul_index (D.map_le_ext hT)
  rw [h1, h2] at h3
  omega

omit [Group N] D in
theorem x_not_mem_T {ι κ : Type*} {d : OvergroupData J ι κ} (e : d.Extra) : d.x ∉ d.T := by
  intro hx
  obtain ⟨i, hi⟩ := e.xN
  obtain ⟨i', hi'⟩ := (d.mem_T_iff _).1
    (d.T.mul_mem (d.T.mul_mem hx (d.Tel_mem_T i)) (d.T.inv_mem hx))
  exact hi i' hi'.symm

omit [Group N] D in
theorem y_not_mem_T {ι κ : Type*} {d : OvergroupData J ι κ} (e : d.Extra) : d.y ∉ d.T := by
  intro hy
  obtain ⟨i, hi⟩ := e.yN
  obtain ⟨i', hi'⟩ := (d.mem_T_iff _).1
    (d.T.mul_mem (d.T.mul_mem hy (d.Tel_mem_T i)) (d.T.inv_mem hy))
  exact hi i' hi'.symm

theorem eq_bot_of_normal {ι κ : Type*} {d : OvergroupData J ι κ} (e : d.Extra) (Q : Subgroup N)
    (hQ : Q.Normal) (hQp : IsPGroup 2 Q) : Q = ⊥ := by
  have hbot : Q.comap f = ⊥ :=
    e.eq_bot_of_normal _ (hQ.comap f) (hQp.comap_of_injective f D.inj)
  have hQr : ∀ x : J, f x ∈ Q → x = 1 := fun x hx => by
    have : x ∈ Q.comap f := hx
    rw [hbot] at this
    exact this
  by_contra hne
  obtain ⟨⟨g, hgQ⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hgr : g ∉ f.range := by
    rintro ⟨x, rfl⟩
    exact hg1' (by rw [hQr x hgQ, map_one])
  obtain ⟨r, hr⟩ : g * ρ ∈ f.range := (D.cover g).resolve_left hgr
  have hg : g = f r * ρ := by
    rw [hr]
    calc g = g * (ρ * ρ) := by rw [D.sq, mul_one]
      _ = g * ρ * ρ := by rw [mul_assoc]
  have hgi : g⁻¹ = ρ * (f r)⁻¹ := by rw [hg, mul_inv_rev, D.rho_inv]
  have key : ∀ x : J, Φ x = r⁻¹ * x * r := by
    intro x
    have hc : f x * g * (f x)⁻¹ * g⁻¹ ∈ Q :=
      Q.mul_mem (hQ.conj_mem g hgQ (f x)) (Q.inv_mem hgQ)
    have e1 : f x * g * (f x)⁻¹ * g⁻¹ = f (x * r * Φ x⁻¹ * r⁻¹) := by
      calc f x * g * (f x)⁻¹ * g⁻¹ = f x * (f r * ρ) * (f x)⁻¹ * (ρ * (f r)⁻¹) := by
            rw [← hg, hgi]
        _ = f x * f r * (ρ * (f x)⁻¹ * ρ) * (f r)⁻¹ := by simp only [mul_assoc]
        _ = f (x * r * Φ x⁻¹ * r⁻¹) := by
            rw [← map_inv f x, D.conj' x⁻¹]
            simp [map_mul, map_inv]
    rw [e1] at hc
    have h1 : x * r * Φ x⁻¹ * r⁻¹ = 1 := hQr _ hc
    have h2 : x * r * (Φ x)⁻¹ * r⁻¹ = 1 := by simpa [map_inv] using h1
    have h3 : (Φ x)⁻¹ = r⁻¹ * x⁻¹ * r := by
      calc (Φ x)⁻¹ = (x * r)⁻¹ * (x * r * (Φ x)⁻¹ * r⁻¹) * r := by group
        _ = r⁻¹ * x⁻¹ * r := by rw [h2]; group
    calc Φ x = ((Φ x)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (r⁻¹ * x⁻¹ * r)⁻¹ := by rw [h3]
      _ = r⁻¹ * x * r := by group
  exact D.outer ⟨r⁻¹, fun x => by rw [key x]; simp⟩

omit D in
theorem map_mem_normalizer {P' : Subgroup J} {a : J}
    (ha : a ∈ Subgroup.normalizer (P' : Set J)) :
    f a ∈ Subgroup.normalizer ((P'.map f : Subgroup N) : Set N) := by
  rw [Subgroup.mem_normalizer_iff] at ha ⊢
  intro z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨a * p * a⁻¹, (ha p).1 hp, by simp⟩
  · rintro ⟨q, hq, hqz⟩
    have hz : z = f (a⁻¹ * q * a) := by
      rw [map_mul, map_mul, map_inv, hqz]
      group
    refine ⟨a⁻¹ * q * a, ?_, hz.symm⟩
    show a⁻¹ * q * a ∈ P'
    refine (ha _).2 ?_
    have : a * (a⁻¹ * q * a) * a⁻¹ = q := by group
    rw [this]
    exact hq

theorem rho_mem_normalizer {P' : Subgroup J} (hP : ∀ x ∈ P', Φ x ∈ P') :
    ρ ∈ Subgroup.normalizer ((P'.map f : Subgroup N) : Set N) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [D.conj p]
    exact ⟨Φ p, hP p hp, rfl⟩
  · rintro ⟨q, hq, hqz⟩
    have hz : z = f (Φ q) := by
      rw [← D.conj' q, hqz]
      have : ρ⁻¹ = ρ := D.rho_inv
      calc z = ρ⁻¹ * (ρ * z * ρ⁻¹) * ρ := by group
        _ = ρ * (ρ * z * ρ⁻¹) * ρ := by rw [this]
    exact ⟨Φ q, hP q hq, hz.symm⟩

theorem ext_le_normalizer {A' P' : Subgroup J} (hA : ∀ x ∈ A', Φ x ∈ A')
    (hP : ∀ x ∈ P', Φ x ∈ P') (hAP : A' ≤ Subgroup.normalizer (P' : Set J)) :
    D.ext A' hA ≤ Subgroup.normalizer ((P'.map f : Subgroup N) : Set N) := by
  intro g hg
  rcases (D.mem_ext).1 hg with ⟨a, ha, rfl⟩ | ⟨a, ha, hag⟩
  · exact map_mem_normalizer (f := f) (hAP ha)
  · have h1 : f a ∈ Subgroup.normalizer ((P'.map f : Subgroup N) : Set N) :=
      map_mem_normalizer (f := f) (hAP ha)
    have h2 := D.rho_mem_normalizer hP
    have : g = f a * ρ⁻¹ := by rw [hag]; simp
    rw [this]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)

theorem ext_mono {H₀ H₁ : Subgroup J} (hH₀ : ∀ x ∈ H₀, Φ x ∈ H₀) (hH₁ : ∀ x ∈ H₁, Φ x ∈ H₁)
    (h : H₀ ≤ H₁) : D.ext H₀ hH₀ ≤ D.ext H₁ hH₁ := fun _ hg =>
  (D.mem_ext).2 (((D.mem_ext).1 hg).imp (Subgroup.map_mono h ·) (Subgroup.map_mono h ·))

noncomputable def toTwoLocalLattice {ι κ : Type*} {d : OvergroupData J ι κ} (e : d.Extra)
    (hT : ∀ x ∈ d.T, Φ x ∈ d.T) (hA : ∀ x ∈ d.A, Φ x ∈ d.A) (hB : ∀ x ∈ d.B, Φ x ∈ d.B)
    (hPA : ∀ x ∈ e.PA, Φ x ∈ e.PA) (hPB : ∀ x ∈ e.PB, Φ x ∈ e.PB) : TwoLocalLattice N where
  S := D.ext d.T hT
  P₁ := D.ext d.A hA
  P₂ := D.ext d.B hB
  sylow := ⟨D.isPGroup_ext hT e.syl.1, by rw [D.index_ext_T hT]; exact e.syl.2⟩
  lattice := D.lattice hT hA hB
  S_le_P₁ := D.ext_mono hT hA d.T_le_A
  S_le_P₂ := D.ext_mono hT hB d.T_le_B
  S_ne_P₁ := by
    intro h
    apply x_not_mem_T e
    apply D.mem_of_map_mem_ext (hH := hT)
    rw [h]
    exact D.map_le_ext hA ⟨d.x, d.x_mem_A, rfl⟩
  S_ne_P₂ := by
    intro h
    apply y_not_mem_T e
    apply D.mem_of_map_mem_ext (hH := hT)
    rw [h]
    exact D.map_le_ext hB ⟨d.y, d.y_mem_B, rfl⟩
  P₁_not_le_P₂ := by
    intro h
    apply d.T_ne_A
    refine le_antisymm d.T_le_A ?_
    rw [← d.inf_AB]
    refine le_inf le_rfl fun x hx => ?_
    exact D.mem_of_map_mem_ext (h (D.map_le_ext hA ⟨x, hx, rfl⟩))
  P₂_not_le_P₁ := by
    intro h
    apply d.T_ne_B
    refine le_antisymm d.T_le_B ?_
    rw [← d.inf_AB]
    refine le_inf (fun x hx => ?_) le_rfl
    exact D.mem_of_map_mem_ext (h (D.map_le_ext hB ⟨x, hx, rfl⟩))
  O₂ := fun Q hQ hQp => D.eq_bot_of_normal e Q hQ hQp
  loc₁ := ⟨e.PA.map f, (Subgroup.map_eq_bot_iff_of_injective e.PA D.inj).not.2 e.PA_ne,
    e.PA_p.map f, D.ext_le_normalizer hA hPA e.PA_norm⟩
  loc₂ := ⟨e.PB.map f, (Subgroup.map_eq_bot_iff_of_injective e.PB D.inj).not.2 e.PB_ne,
    e.PB_p.map f, D.ext_le_normalizer hB hPB e.PB_norm⟩
  normS := by
    have hSM : D.ext d.T hT ≤ Subgroup.normalizer ((D.ext d.T hT : Subgroup N) : Set N) :=
      Subgroup.le_normalizer
    rcases D.lattice hT hA hB _ hSM with h | h | h | h
    · exact h.le
    · exfalso
      have hfx : f d.x ∈ Subgroup.normalizer ((D.ext d.T hT : Subgroup N) : Set N) := by
        rw [h]; exact D.map_le_ext hA ⟨d.x, d.x_mem_A, rfl⟩
      obtain ⟨i, hi⟩ := e.xN
      have h1 : f (d.Tel i) ∈ D.ext d.T hT := D.map_le_ext hT ⟨d.Tel i, d.Tel_mem_T i, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 hfx _).1 h1
      have h3 : f (d.x * d.Tel i * d.x⁻¹) ∈ D.ext d.T hT := by simpa [map_mul, map_inv] using h2
      obtain ⟨i', hi'⟩ := (d.mem_T_iff _).1 (D.mem_of_map_mem_ext h3)
      exact hi i' hi'.symm
    · exfalso
      have hfy : f d.y ∈ Subgroup.normalizer ((D.ext d.T hT : Subgroup N) : Set N) := by
        rw [h]; exact D.map_le_ext hB ⟨d.y, d.y_mem_B, rfl⟩
      obtain ⟨i, hi⟩ := e.yN
      have h1 : f (d.Tel i) ∈ D.ext d.T hT := D.map_le_ext hT ⟨d.Tel i, d.Tel_mem_T i, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 hfy _).1 h1
      have h3 : f (d.y * d.Tel i * d.y⁻¹) ∈ D.ext d.T hT := by simpa [map_mul, map_inv] using h2
      obtain ⟨i', hi'⟩ := (d.mem_T_iff _).1 (D.mem_of_map_mem_ext h3)
      exact hi i' hi'.symm
    · exfalso
      have hn : (D.ext d.T hT).Normal := Subgroup.normalizer_eq_top_iff.1 h
      have hbot := D.eq_bot_of_normal e _ hn (D.isPGroup_ext hT e.syl.1)
      have hρ : ρ ∈ D.ext d.T hT := D.rho_mem_ext hT
      rw [hbot] at hρ
      exact D.rho_not_mem ⟨1, by rw [map_one, (Subgroup.mem_bot.1 hρ)]⟩

theorem twoLocalPairProp [Finite N] {ι κ : Type*} {d : OvergroupData J ι κ} (e : d.Extra)
    (hT : ∀ x ∈ d.T, Φ x ∈ d.T) (hA : ∀ x ∈ d.A, Φ x ∈ d.A) (hB : ∀ x ∈ d.B, Φ x ∈ d.B)
    (hPA : ∀ x ∈ e.PA, Φ x ∈ e.PA) (hPB : ∀ x ∈ e.PB, Φ x ∈ e.PB) : TwoLocalPairProp N :=
  (D.toTwoLocalLattice e hT hA hB hPA hPB).twoLocalPairProp

end IndexTwoData

end CFSG.Quasithin
