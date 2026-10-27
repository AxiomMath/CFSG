module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open CFSG Subgroup

variable {A A' : Type*} [Group A] [Group A']

structure ModelFacts (p : ℕ) (Inn Dg S V : Subgroup A) : Prop where
  le_inn : S ≤ Inn
  irreducible : ∀ R : Subgroup A, R ≤ S → Inn ⊓ normalizer (S : Set A) ≤ normalizer (R : Set A) →
    R = ⊥ ∨ R = V ∨ R = S
  core : ∀ R : Subgroup A, IsPGroup 2 R →
    Inn ⊓ normalizer (S : Set A) ≤ normalizer (R : Set A) → R ≤ S
  faithful : ∀ B : Subgroup A, B ≤ normalizer (S : Set A) ⊓ Dg → IsElementaryAbelian p B →
    Nat.card B = p ^ 2 → ∃ b ∈ B, b ≠ 1 ∧ b ∈ centralizer (V : Set A)
  cyclic : ∀ P : Subgroup A, IsPGroup p P → P ≤ centralizer (V : Set A) → IsCyclic P

theorem mem_normalizer_comap_equiv (θ : A ≃* A') (R : Subgroup A') (x : A) :
    x ∈ normalizer ((R.comap θ.toMonoidHom : Subgroup A) : Set A) ↔
      θ x ∈ normalizer (R : Set A') := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h y
    obtain ⟨z, rfl⟩ := θ.surjective y
    have := h z
    simpa [Subgroup.mem_comap, map_mul, map_inv] using this
  · intro h z
    have := h (θ z)
    simpa [Subgroup.mem_comap, map_mul, map_inv] using this

theorem mem_normalizer_map_equiv (θ : A ≃* A') (S : Subgroup A) (x : A) :
    θ x ∈ normalizer ((S.map θ.toMonoidHom : Subgroup A') : Set A') ↔
      x ∈ normalizer (S : Set A) := by
  have := mem_normalizer_comap_equiv θ (S.map θ.toMonoidHom) x
  rw [Subgroup.comap_map_eq_self_of_injective θ.injective] at this
  exact this.symm

theorem map_map_symm (θ : A ≃* A') (X : Subgroup A) :
    (X.map θ.toMonoidHom).map θ.symm.toMonoidHom = X := by
  ext x
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

namespace ModelFacts

variable {p : ℕ} {Inn Dg S V : Subgroup A}

theorem mono {Dg' : Subgroup A} (h : ModelFacts p Inn Dg' S V) (hD : Dg ≤ Dg') :
    ModelFacts p Inn Dg S V :=
  { h with faithful := fun B hB => h.faithful B (hB.trans (inf_le_inf_left _ hD)) }

theorem map (hp : p.Prime) (h : ModelFacts p Inn Dg S V) (θ : A ≃* A') :
    ModelFacts p (Inn.map θ.toMonoidHom) (Dg.map θ.toMonoidHom) (S.map θ.toMonoidHom)
      (V.map θ.toMonoidHom) where
  le_inn := Subgroup.map_mono h.le_inn
  irreducible R' hR' hN := by
    set R : Subgroup A := R'.comap θ.toMonoidHom with hR
    have hRS : R ≤ S := fun x hx => (Subgroup.mem_map_iff_mem θ.injective).1 (hR' hx)
    have hNR : Inn ⊓ normalizer (S : Set A) ≤ normalizer (R : Set A) := by
      intro x hx
      rw [hR, mem_normalizer_comap_equiv]
      exact hN ⟨Subgroup.mem_map_of_mem θ.toMonoidHom hx.1,
        (mem_normalizer_map_equiv θ S x).2 hx.2⟩
    have hR'eq : R' = R.map θ.toMonoidHom :=
      (Subgroup.map_comap_eq_self_of_surjective θ.surjective R').symm
    rcases h.irreducible R hRS hNR with h1 | h1 | h1
    · left
      rw [hR'eq, h1, Subgroup.map_bot]
    · right; left
      rw [hR'eq, h1]
    · right; right
      rw [hR'eq, h1]
  core R' hR2 hN := by
    set R : Subgroup A := R'.comap θ.toMonoidHom with hR
    have hRp : IsPGroup 2 R := hR2.comap_of_injective θ.toMonoidHom θ.injective
    have hNR : Inn ⊓ normalizer (S : Set A) ≤ normalizer (R : Set A) := by
      intro x hx
      rw [hR, mem_normalizer_comap_equiv]
      exact hN ⟨Subgroup.mem_map_of_mem θ.toMonoidHom hx.1,
        (mem_normalizer_map_equiv θ S x).2 hx.2⟩
    have hRS := h.core R hRp hNR
    intro y hy
    have hy' : θ.symm y ∈ R := by
      show θ (θ.symm y) ∈ R'
      simpa using hy
    exact ⟨θ.symm y, hRS hy', by simp⟩
  faithful B' hB'N hB'el hB'card := by
    have : Fact p.Prime := ⟨hp⟩
    have hBeq : B'.comap θ.toMonoidHom = B'.map θ.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm' θ B'
    set B : Subgroup A := B'.comap θ.toMonoidHom with hB
    have hBN : B ≤ normalizer (S : Set A) ⊓ Dg := by
      intro x hx
      have hx' := hB'N hx
      exact ⟨(mem_normalizer_map_equiv θ S x).1 hx'.1,
        (Subgroup.mem_map_iff_mem θ.injective).1 hx'.2⟩
    have hBel : IsElementaryAbelian p B := by
      rw [hBeq]
      have := hB'el
      exact IsElementaryAbelian.map θ.symm.toMonoidHom
    have hBcard : Nat.card B = p ^ 2 := by
      rw [hBeq, Subgroup.card_map_of_injective θ.symm.injective, hB'card]
    obtain ⟨b, hb, hb1, hbC⟩ := h.faithful B hBN hBel hBcard
    refine ⟨θ b, hb, fun h1 => hb1 (θ.injective (by rw [h1, map_one])), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hbC w hw
    change θ w * θ b = θ b * θ w
    rw [← map_mul, ← map_mul, this]
  cyclic P' hP' hPC := by
    set P : Subgroup A := P'.comap θ.toMonoidHom with hP
    have hPp : IsPGroup p P := hP'.comap_of_injective θ.toMonoidHom θ.injective
    have hPV : P ≤ centralizer (V : Set A) := by
      intro x hx
      rw [mem_centralizer_iff]
      intro w hw
      have := Subgroup.mem_centralizer_iff.1 (hPC hx) (θ w) (Subgroup.mem_map_of_mem _ hw)
      apply θ.injective
      rw [map_mul, map_mul]
      exact this
    have hcyc := h.cyclic P hPp hPV
    let φ : P →* P' := (θ.toMonoidHom.comp P.subtype).codRestrict P' (fun x => x.2)
    have hφ : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      refine ⟨⟨θ.symm y, ?_⟩, ?_⟩
      · show θ (θ.symm y) ∈ P'
        simpa using hy
      · apply Subtype.ext
        simp [φ]
    exact isCyclic_of_surjective φ hφ

theorem of_map (hp : p.Prime) (θ : A ≃* A')
    (h : ModelFacts p (Inn.map θ.toMonoidHom) (Dg.map θ.toMonoidHom) (S.map θ.toMonoidHom)
      (V.map θ.toMonoidHom)) : ModelFacts p Inn Dg S V := by
  have := h.map hp θ.symm
  rwa [map_map_symm, map_map_symm, map_map_symm, map_map_symm] at this

end ModelFacts

end CFSG.RankThree.PartOne.U5K.Hyp
