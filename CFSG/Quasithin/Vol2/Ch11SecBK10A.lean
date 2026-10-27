module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace BK10

@[expose] def IsCoprimePrimeAut {X : Type} [Group X] (β : MulAut X) : Prop :=
  ∃ r : ℕ, r.Prime ∧ β ^ r = 1 ∧ β ≠ 1 ∧ ¬ r ∣ Nat.card X

@[expose] def TorusRigidAt (X : Type) [Group X] (P : Subgroup X) : Prop :=
  ∀ S : Subgroup (MulAut X), IsPGroup 2 S → (∀ p ∈ P, MulAut.conj p ∈ S) →
    (∀ s ∈ S, ∀ x, x ∈ P ↔ s x ∈ P) →
    ∃ y : X, (∀ s ∈ S, y * (s y)⁻¹ ∈ P) ∧ Odd (orderOf y) ∧
      ∀ y' : X, y' * y⁻¹ ∈ P → Odd (orderOf y') →
        ∀ β : MulAut X, IsCoprimePrimeAut β → β y' = y' → β = 1

@[expose] def TorusRigid (X : Type) [Group X] : Prop :=
  ∀ P : Subgroup X, QuasithinUnique.IsSylowTwoOf P ⊤ → TorusRigidAt X P

variable {X : Type} [Group X]

theorem torusRigid_of_forall_eq_one (h : ∀ β : MulAut X, IsCoprimePrimeAut β → β = 1) :
    TorusRigid X := by
  intro P _ S _ _ _
  refine ⟨1, fun s _ => ?_, ?_, fun _ _ _ β hβ _ => h β hβ⟩
  · rw [map_one, inv_one, mul_one]
    exact P.one_mem
  · rw [orderOf_one]
    exact odd_one

theorem IsCoprimePrimeAut.congr {Y : Type} [Group Y] (e : X ≃* Y) {β : MulAut X}
    (hβ : IsCoprimePrimeAut β) : IsCoprimePrimeAut (MulAut.congr e β) := by
  obtain ⟨r, hr, hβr, hβ1, hrX⟩ := hβ
  refine ⟨r, hr, by rw [← map_pow, hβr, map_one], fun h => hβ1 ?_, ?_⟩
  · have := congrArg (MulAut.congr e).symm h
    rwa [MulEquiv.symm_apply_apply, map_one] at this
  · rwa [← Nat.card_congr e.toEquiv]

theorem TorusRigidAt.of_mulEquiv {Y : Type} [Group Y] (e : X ≃* Y) {P : Subgroup X}
    (h : TorusRigidAt X P) : TorusRigidAt Y (P.map e.toMonoidHom) := by
  intro S hS2 hSP hSs
  set e' := MulAut.congr e with he'
  set S₀ := S.map e'.symm.toMonoidHom with hS₀
  have hmemP : ∀ x : X, e x ∈ P.map e.toMonoidHom ↔ x ∈ P := fun x => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hS₀2 : IsPGroup 2 S₀ := hS2.map _
  have hmemS₀ : ∀ s : MulAut X, s ∈ S₀ ↔ e' s ∈ S := fun s => by
    rw [hS₀, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have he's : ∀ (s : MulAut X) (x : X), e' s (e x) = e (s x) := fun s x => by
    simp [he', MulAut.congr_apply]
  have hSP₀ : ∀ p ∈ P, MulAut.conj p ∈ S₀ := by
    intro p hp
    rw [hmemS₀]
    have h1 : e' (MulAut.conj p) = MulAut.conj (e p) :=
      CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e p
    rw [h1]
    exact hSP _ ((hmemP p).mpr hp)
  have hSs₀ : ∀ s ∈ S₀, ∀ x, x ∈ P ↔ s x ∈ P := by
    intro s hs x
    rw [← hmemP, ← hmemP, ← he's]
    exact hSs _ ((hmemS₀ s).mp hs) _
  obtain ⟨y, hy, hyodd, hyrig⟩ := h S₀ hS₀2 hSP₀ hSs₀
  have hsymm : ∀ (β : MulAut Y) (z : X), e'.symm β z = e.symm (β (e z)) := fun β z => by
    have h := he's (e'.symm β) z
    rw [MulEquiv.apply_symm_apply] at h
    rw [h, MulEquiv.symm_apply_apply]
  refine ⟨e y, fun s hs => ?_, ?_, fun y' hy' hy'odd β hβ hβy' => ?_⟩
  · have h1 := hy (e'.symm s) ((hmemS₀ _).mpr (by rwa [MulEquiv.apply_symm_apply]))
    rw [← hmemP] at h1
    have h2 : e (e'.symm s y) = s (e y) := by
      rw [← he's, MulEquiv.apply_symm_apply]
    rwa [map_mul, map_inv, h2] at h1
  · rwa [MulEquiv.orderOf_eq]
  · have hβ' : e'.symm β = MulAut.congr e.symm β := MulEquiv.ext fun z => by
      rw [hsymm]
      simp [MulAut.congr_apply]
    have h1 := hyrig (e.symm y') (by
      rw [← hmemP, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hy') (by rwa [MulEquiv.orderOf_eq]) (e'.symm β) (by rw [hβ']; exact hβ.congr e.symm)
      (by rw [hsymm, MulEquiv.apply_symm_apply, hβy'])
    have := congrArg e' h1
    rwa [MulEquiv.apply_symm_apply, map_one] at this

theorem map_map_symm {Y : Type} [Group Y] (e : X ≃* Y) (P : Subgroup Y) :
    (P.map e.symm.toMonoidHom).map e.toMonoidHom = P := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_symm,
    MulEquiv.apply_symm_apply]

theorem TorusRigid.of_mulEquiv {Y : Type} [Group Y] (e : X ≃* Y) (h : TorusRigid X) :
    TorusRigid Y := by
  intro P hP
  have hP₀ : QuasithinUnique.IsSylowTwoOf (P.map e.symm.toMonoidHom) ⊤ := by
    obtain ⟨-, h2, hidx⟩ := hP
    refine ⟨le_top, h2.map _, ?_⟩
    have h1 : ((P.map e.symm.toMonoidHom).subgroupOf ⊤).index = (P.subgroupOf ⊤).index := by
      change (P.map e.symm.toMonoidHom).relIndex ⊤ = P.relIndex ⊤
      rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right]
      exact Subgroup.index_map_equiv P e.symm
    rwa [h1]
  have := (h _ hP₀).of_mulEquiv e
  rwa [map_map_symm] at this

theorem TorusRigid.of_at [Finite X] {P₀ : Subgroup X} (hP₀ : QuasithinUnique.IsSylowTwoOf P₀ ⊤)
    (h : TorusRigidAt X P₀) : TorusRigid X := by
  intro P hP
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.A4.exists_conj_of_isSylowTwoOf hP₀ hP
  have hPeq : P₀.map (MulAut.conj g).toMonoidHom = P := by
    ext x
    rw [Subgroup.mem_map_equiv, hg]
    simp [MulAut.conj_symm_apply]
  rw [← hPeq]
  exact h.of_mulEquiv (MulAut.conj g)

omit [Group X] in
theorem card_inner_dvd [Group X] [Finite X] : Nat.card (inner X) ∣ Nat.card X := by
  have h := Subgroup.card_range_dvd (MulAut.conj : X →* MulAut X)
  exact h

theorem eq_one_of_mem_inner [Finite X] {β : MulAut X} (hβ : IsCoprimePrimeAut β)
    (hin : β ∈ inner X) : β = 1 := by
  obtain ⟨r, hr, hβr, hβ1, hrX⟩ := hβ
  exfalso
  apply hβ1
  have hβ' : (⟨β, hin⟩ : inner X) ^ r = 1 := Subtype.ext (by simpa using hβr)
  have h1 : orderOf (⟨β, hin⟩ : inner X) ∣ Nat.card X :=
    (orderOf_dvd_natCard _).trans card_inner_dvd
  have h2 : orderOf (⟨β, hin⟩ : inner X) ∣ r := orderOf_dvd_of_pow_eq_one hβ'
  have h3 : orderOf (⟨β, hin⟩ : inner X) = 1 := by
    rcases (Nat.dvd_prime hr).mp h2 with h | h
    · exact h
    · exact absurd (h ▸ h1) hrX
  have := orderOf_eq_one_iff.mp h3
  exact congrArg Subtype.val this

theorem eq_one_of_outer [Finite X]
    (hout : ∀ q : ℕ, q.Prime → q ∣ Nat.card (Outer X) → q ∣ Nat.card X) {β : MulAut X}
    (hβ : IsCoprimePrimeAut β) : β = 1 := by
  refine eq_one_of_mem_inner hβ ?_
  obtain ⟨r, hr, hβr, -, hrX⟩ := hβ
  have : Finite (Outer X) := inferInstance
  set π := QuotientGroup.mk' (inner X)
  have h1 : orderOf (π β) ∣ r := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hβr, map_one])
  have h2 : orderOf (π β) ∣ Nat.card (Outer X) := orderOf_dvd_natCard (π β)
  have h3 : orderOf (π β) = 1 := by
    rcases (Nat.dvd_prime hr).mp h1 with h | h
    · exact h
    · exact absurd (hout r hr (h ▸ h2)) hrX
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

end BK10

end CFSG.Quasithin.Vol2.Ch11.SecD
