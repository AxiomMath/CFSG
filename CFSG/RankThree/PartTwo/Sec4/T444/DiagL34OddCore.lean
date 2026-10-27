module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.L34Odd

theorem card_le_eight_of_quotient {S : Type*} [Group S] [Finite S] (B : Subgroup S)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBi : B.index ≤ 2)
    (hB2 : ∀ F : Subgroup S, F ≤ B → (∀ x ∈ F, x ^ 2 = 1) → Nat.card F ≤ 4)
    {E : Type*} [Group E] (hE : ∀ x : E, x ^ 2 = 1)
    (ρ : S →* E) (hρ : Function.Surjective ρ) : Nat.card E ≤ 8 := by
  haveI : Finite E := Finite.of_surjective ρ hρ
  have hidx : (B.map ρ).index ≤ 2 := by
    have hdvd := Subgroup.index_map_dvd (H := B) hρ
    have hB0 : B.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hB0) hdvd).trans hBi
  have hB' : Nat.card (B.map ρ) ≤ 4 := by
    let ρB : B →* E := ρ.comp B.subtype
    let sq : B →* B :=
      { toFun := fun x => x ^ 2
        map_one' := one_pow 2
        map_mul' := fun x y => Commute.mul_pow (Subtype.ext (hBc x x.2 y y.2)) 2 }
    have h1 : Nat.card sq.ker * Nat.card sq.range = Nat.card B := by
      rw [← Subgroup.index_ker sq]
      exact Subgroup.card_mul_index sq.ker
    have h2 : Nat.card ρB.ker * Nat.card ρB.range = Nat.card B := by
      rw [← Subgroup.index_ker ρB]
      exact Subgroup.card_mul_index ρB.ker
    have h3 : sq.range ≤ ρB.ker := by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker]
      show ρB (x ^ 2) = 1
      rw [map_pow]
      exact hE _
    have h4 : Nat.card sq.range ≤ Nat.card ρB.ker :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h3)
    have h5 : Nat.card sq.ker ≤ 4 := by
      have h := hB2 (sq.ker.map B.subtype)
        (by rintro _ ⟨x, _, rfl⟩; exact x.2)
        (by
          rintro _ ⟨x, hx, rfl⟩
          have hx' : x ^ 2 = 1 := hx
          simpa using congrArg Subtype.val hx')
      rwa [Subgroup.card_map_of_injective B.subtype_injective] at h
    have h6 : Nat.card ρB.ker * Nat.card ρB.range ≤ Nat.card ρB.ker * 4 := by
      calc Nat.card ρB.ker * Nat.card ρB.range
          = Nat.card sq.ker * Nat.card sq.range := by rw [h1, h2]
        _ ≤ 4 * Nat.card ρB.ker := Nat.mul_le_mul h5 h4
        _ = Nat.card ρB.ker * 4 := mul_comm _ _
    have h7 : Nat.card ρB.range ≤ 4 := Nat.le_of_mul_le_mul_left h6 Nat.card_pos
    have h8 : B.map ρ = ρB.range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rwa [h8]
  have := Subgroup.card_mul_index (B.map ρ)
  calc Nat.card E = Nat.card (B.map ρ) * (B.map ρ).index := this.symm
    _ ≤ 4 * 2 := Nat.mul_le_mul hB' hidx

@[expose] def GL2Type (S : Type*) [Group S] : Prop :=
  ∃ B : Subgroup S, (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ B.index ≤ 2 ∧
    ∀ F : Subgroup S, F ≤ B → (∀ x ∈ F, x ^ 2 = 1) → Nat.card F ≤ 4

theorem index_comap_le_of_finite {S T : Type*} [Group S] [Group T] [Finite T] (σ : S →* T)
    (B : Subgroup T) : (B.comap σ).index ≤ B.index := by
  rw [Subgroup.index_comap, ← Subgroup.relIndex_top_right (H := B)]
  refine Subgroup.relIndex_le_of_le_right le_top ?_
  rw [Subgroup.relIndex_top_right]
  exact Subgroup.index_ne_zero_of_finite

theorem GL2Type.of_injective {S T : Type*} [Group S] [Group T] [Finite T] (σ : S →* T)
    (hσ : Function.Injective σ) (hT : GL2Type T) : GL2Type S := by
  obtain ⟨B, hBc, hBi, hB2⟩ := hT
  refine ⟨B.comap σ, ?_, (index_comap_le_of_finite σ B).trans hBi, ?_⟩
  · intro a ha b hb
    apply hσ
    rw [map_mul, map_mul]
    exact hBc _ ha _ hb
  · intro F hF hF2
    have h := hB2 (F.map σ) (by rintro _ ⟨x, hx, rfl⟩; exact hF hx)
      (by rintro _ ⟨x, hx, rfl⟩; rw [← map_pow, hF2 x hx, map_one])
    rwa [Subgroup.card_map_of_injective hσ] at h

theorem exists_isPGroup_map_eq {Γ Q : Type*} [Group Γ] [Finite Γ] [Group Q] (p : ℕ)
    [Fact p.Prime] (f : Γ →* Q) (S : Subgroup Q) (hS : IsPGroup p S) (hSf : S ≤ f.range) :
    ∃ T : Subgroup Γ, IsPGroup p T ∧ T.map f = S := by
  set Γ₁ : Subgroup Γ := S.comap f with hΓ₁
  obtain ⟨T₀⟩ : Nonempty (Sylow p Γ₁) := inferInstance
  let g : Γ₁ →* S := (f.comp Γ₁.subtype).codRestrict S (fun x => x.2)
  have hg : Function.Surjective g := by
    intro s
    obtain ⟨x, hx⟩ := hSf s.2
    exact ⟨⟨x, show f x ∈ S by rw [hx]; exact s.2⟩, Subtype.ext hx⟩
  refine ⟨(T₀ : Subgroup Γ₁).map Γ₁.subtype, T₀.isPGroup'.map Γ₁.subtype, ?_⟩
  have hfin : Finite S := Finite.of_surjective g hg
  have htop : ((T₀.mapSurjective hg : Sylow p S) : Subgroup S) = ⊤ := by
    set P : Sylow p S := T₀.mapSurjective hg
    haveI : (P : Subgroup S).FiniteIndex := P.finiteIndex_of_finite
    obtain ⟨n, hn⟩ := hS.index (P : Subgroup S)
    have hn0 : n = 0 := by
      by_contra hne
      exact P.not_dvd_index (hn ▸ dvd_pow_self p hne)
    rw [hn0, pow_zero] at hn
    exact Subgroup.index_eq_one.mp hn
  rw [Sylow.coe_mapSurjective] at htop
  rw [Subgroup.map_map]
  have hcomp : Γ₁.subtype.comp (MonoidHom.id Γ₁) = Γ₁.subtype := rfl
  have e : f.comp Γ₁.subtype = S.subtype.comp g := by
    ext x; rfl
  rw [e, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

@[expose] def TwoQuot (p : ℕ) (Γ : Type*) [Group Γ] (E : Type*) [Group E] : Prop :=
  ∃ S : Subgroup Γ, IsPGroup p S ∧ ∃ ρ : S →* E, Function.Surjective ρ

theorem TwoQuot.of_surjective {p : ℕ} [Fact p.Prime] {Γ Q E : Type*} [Group Γ] [Finite Γ]
    [Group Q] [Group E] (f : Γ →* Q) (hf : Function.Surjective f) (h : TwoQuot p Q E) :
    TwoQuot p Γ E := by
  obtain ⟨S, hS, ρ, hρ⟩ := h
  obtain ⟨T, hT, hTS⟩ := exists_isPGroup_map_eq p f S hS
    (by rw [MonoidHom.range_eq_top.2 hf]; exact le_top)
  refine ⟨T, hT, ρ.comp ((f.comp T.subtype).codRestrict S
    (fun x => by rw [← hTS]; exact ⟨x, x.2, rfl⟩)), hρ.comp ?_⟩
  intro s
  have hs : (s : Q) ∈ T.map f := by rw [hTS]; exact s.2
  obtain ⟨x, hx, hxs⟩ := hs
  exact ⟨⟨x, hx⟩, Subtype.ext hxs⟩

theorem TwoQuot.of_subgroup {p : ℕ} {Γ E : Type*} [Group Γ] [Group E] (A : Subgroup Γ)
    (h : TwoQuot p A E) : TwoQuot p Γ E := by
  obtain ⟨S, hS, ρ, hρ⟩ := h
  let φ : S ≃* S.map A.subtype := Subgroup.equivMapOfInjective S A.subtype A.subtype_injective
  exact ⟨S.map A.subtype, hS.map A.subtype, ρ.comp φ.symm.toMonoidHom,
    hρ.comp φ.symm.surjective⟩

theorem TwoQuot.of_isPGroup {p : ℕ} {L : Type*} [Group L] (E : Subgroup L) (hE : IsPGroup p E) :
    TwoQuot p L E :=
  ⟨E, hE, MonoidHom.id _, Function.surjective_id⟩

theorem isPGroup_two_of_sq_eq_one {L : Type*} [Group L] (E : Subgroup L)
    (hE : ∀ x ∈ E, x ^ 2 = 1) : IsPGroup 2 E := by
  intro g
  exact ⟨1, by
    apply Subtype.ext
    simpa using hE g g.2⟩

end CFSG.RankThree.PartTwo.Sec4.L34Odd

end
