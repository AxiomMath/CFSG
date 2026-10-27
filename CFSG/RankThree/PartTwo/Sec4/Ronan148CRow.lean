module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (AutNoE27)
open CFSG.GH74.GLS (pPrimeCoreOf)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

structure CfgS148 (S : Type) [Group S] (F E X R : Subgroup (MulAut S)) : Prop where
  isE27 : Late.IsE27 F
  le : E ≤ F
  card : Nat.card E = 9
  inner_le : (MulAut.conj : S →* MulAut S).range ≤ X
  le_core : ∀ e ∈ E, e ≠ 1 →
    R ≤ pPrimeCoreOf 3 (X ⊓ Subgroup.centralizer ({e} : Set (MulAut S)))
  le_normalizer : F ≤ Subgroup.normalizer (R : Set (MulAut S))
  eq_commutator : R = ⁅R, F⁆

@[expose] def RowS148 (S : Type) [Group S] : Prop :=
  ∀ F E X R : Subgroup (MulAut S), CfgS148 S F E X R → R = ⊥

@[expose] def RowSOf148 (X : Type) [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → RowS148 S

theorem rowS148_of_autNoE27 {S : Type} [Group S] (h : AutNoE27 S) : RowS148 S :=
  fun F _ _ _ hc => absurd hc.isE27 (h F)

theorem rowSOf148_of_autNoE27 {X : Type} [Group X]
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* X) → AutNoE27 S) : RowSOf148 X :=
  fun S _ _ hs hna hX => rowS148_of_autNoE27 (h S hs hna hX)

section Transport

variable {S T : Type} [Group S] [Group T]

theorem mulAutCongr_conj (e : S ≃* T) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext t
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem map_range_conj (e : S ≃* T) :
    (MulAut.conj : S →* MulAut S).range.map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : T →* MulAut T).range := by
  ext x
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨e s, (mulAutCongr_conj e s).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨MulAut.conj (e.symm t), ⟨e.symm t, rfl⟩, ?_⟩
    change MulAut.congr e (MulAut.conj (e.symm t)) = MulAut.conj t
    rw [mulAutCongr_conj, MulEquiv.apply_symm_apply]

theorem map_centralizer_singleton {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (g : G) :
    (Subgroup.centralizer ({g} : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ g} : Set G') := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg φ h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    exact this
  · intro h
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h

theorem map_le_normalizer {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') {F R : Subgroup G}
    (h : F ≤ Subgroup.normalizer (R : Set G)) :
    F.map φ.toMonoidHom ≤ Subgroup.normalizer ((R.map φ.toMonoidHom : Subgroup G') : Set G') := by
  rintro _ ⟨f, hf, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hf' := Subgroup.mem_normalizer_iff.mp (h hf) (φ.symm y)
  simp only [Subgroup.mem_map_equiv] at hf' ⊢
  rw [show φ.symm (φ.toMonoidHom f * y * (φ.toMonoidHom f)⁻¹) = f * φ.symm y * f⁻¹ by
    simp [map_mul, map_inv]]
  exact hf'

theorem RowS148.of_mulEquiv (e : S ≃* T) (h : RowS148 T) : RowS148 S := by
  intro F E X R hc
  set φ : MulAut S ≃* MulAut T := MulAut.congr e with hφ
  have hR : R.map φ.toMonoidHom = ⊥ := by
    refine h (F.map φ.toMonoidHom) (E.map φ.toMonoidHom) (X.map φ.toMonoidHom)
      (R.map φ.toMonoidHom) ⟨hc.isE27.map φ, Subgroup.map_mono hc.le, ?_, ?_, ?_,
        map_le_normalizer φ hc.le_normalizer, ?_⟩
    · rw [Subgroup.card_map_of_injective φ.injective, hc.card]
    · rw [← map_range_conj e]
      exact Subgroup.map_mono hc.inner_le
    · rintro _ ⟨x, hx, rfl⟩ hx1
      have hx1' : x ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
      have hle := Subgroup.map_mono (f := φ.toMonoidHom) (hc.le_core x hx hx1')
      have heq : (X ⊓ Subgroup.centralizer ({x} : Set (MulAut S))).map φ.toMonoidHom =
          X.map φ.toMonoidHom ⊓ Subgroup.centralizer ({φ.toMonoidHom x} : Set (MulAut T)) := by
        rw [Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective, map_centralizer_singleton]
        rfl
      rw [Sec14.map_pPrimeCoreOf, heq] at hle
      exact hle
    · rw [← Subgroup.map_commutator, ← hc.eq_commutator]
  exact (Subgroup.map_eq_bot_iff_of_injective R φ.injective).mp hR

theorem rowSOf148_of_rowS148 {X : Type} [Group X] (h : RowS148 X) : RowSOf148 X :=
  fun _ _ _ _ _ ⟨e⟩ => h.of_mulEquiv e

end Transport

structure K148RowsS : Prop where
  one : ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e → RowSOf148 (projSL 2 (GaloisField p e))
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    RowSOf148 (projSL 3 (GaloisField p e))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowSOf148 (projSU 3 p e)
  three : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p →
    q.exponent = 1 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
      RowSOf148 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSOf148 (projSp 2 (GaloisField p 1))
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSOf148 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSOf148 (projSU 4 p 1)
  five : ∀ n : ℕ, 5 ≤ n → n ≤ 12 → RowSOf148 (alternatingGroup (Fin n))
  six : ∀ s ∈ sporadics42, RowSOf148 (Spor s)
  seven_SL2 : ∀ n : ℕ, 1 ≤ n → RowSOf148 (projSL 2 (GaloisField 2 n))
  seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowSOf148 (projSL 3 (GaloisField 2 n))
  seven_SU3 : ∀ n : ℕ, 1 ≤ n → RowSOf148 (projSU 3 2 n)
  seven_Sp4 : ∀ n : ℕ, 1 ≤ n → RowSOf148 (projSp 2 (GaloisField 2 n))
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowSOf148 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    q.p = 2 → RowSOf148 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_Sz : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group
  eight_SL5 : RowSOf148 (projSL 5 (GaloisField 2 1))
  eight_SU5 : RowSOf148 (projSU 5 2 1)
  eight_SL6 : RowSOf148 (projSL 6 (GaloisField 2 1))
  eight_SU6 : RowSOf148 (projSU 6 2 1)
  eight_SL7 : RowSOf148 (projSL 7 (GaloisField 2 1))
  eight_Sp6 : RowSOf148 (projSp 3 (GaloisField 2 1))
  eight_Sp8 : RowSOf148 (projSp 4 (GaloisField 2 1))
  eight_OmegaPlus : RowSOf148 (projOmegaPlus 4 (GaloisField 2 1))
  eight_OmegaMinus : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowSOf148 (projOmegaMinus 3 (GaloisField 2 1) b c)
  eight_SL4 : RowSOf148 (projSL 4 (GaloisField 2 2))
  eight_Sp6_4 : RowSOf148 (projSp 3 (GaloisField 2 2))
  eight_SU5_4 : RowSOf148 (projSU 5 2 2)
  eight_SU5_8 : RowSOf148 (projSU 5 2 3)
  eight_F4 : RowSOf148 (TauCeti.CFSGIndex.lie f4TwoIndex).Group
  nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf148 (projSL 3 (GaloisField 3 e))
  nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf148 (projSU 3 3 e)
  nine_G2 : RowSOf148 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group
  nine_SL4 : RowSOf148 (projSL 4 (GaloisField 3 1))
  nine_SU4 : RowSOf148 (projSU 4 3 1)

namespace K148RowsS

variable {S : Type} [Group S] [Finite S]

theorem rowS_of_list42 (R : K148RowsS) (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : Census.List42 S) : RowS148 S := by
  rcases h with ⟨p, e, hp, h2, he, hf⟩ | ⟨p, e, hp, h3, he, he2, hf | hf⟩ | ⟨hr, hf⟩ |
    ⟨p, hp, h3, ⟨q, hqp, hqe, hq, hf⟩ | hf | hf | hf⟩ | ⟨n, hn5, hn12, hf⟩ |
    ⟨s, hsp, hf⟩ | h7 | h8 | h9
  · exact R.one p e h2 he S hs hna hf
  · exact R.two_SL p e h3 he he2 S hs hna hf
  · exact R.two_SU p e h3 he he2 S hs hna hf
  · exact R.three hr S hs hna hf
  · exact R.four_G2 p h3 q hqp hqe hq S hs hna hf
  · exact R.four_Sp p h3 S hs hna hf
  · exact R.four_SL p h3 S hs hna hf
  · exact R.four_SU p h3 S hs hna hf
  · exact R.five n hn5 hn12 S hs hna hf
  · exact R.six s hsp S hs hna hf
  · rcases h7 with ⟨n, hn, hf | hf | hf | hf | hf⟩ | ⟨q, hq2, hq, hf⟩ |
      ⟨q, hq, hq2, hf⟩ | ⟨m, hm, hf⟩ | ⟨m, hm, hf⟩ | ⟨ht, hf⟩
    · exact R.seven_SL2 n hn S hs hna hf
    · exact R.seven_SL3 n hn S hs hna hf
    · exact R.seven_SU3 n hn S hs hna hf
    · exact R.seven_Sp4 n hn S hs hna hf
    · exact R.seven_SU4 n hn S hs hna hf
    · exact R.seven_G2 q hq2 hq S hs hna hf
    · exact R.seven_D4 q hq hq2 S hs hna hf
    · exact R.seven_Sz m hm S hs hna hf
    · exact R.seven_F4 m hm S hs hna hf
    · exact R.seven_Tits ht S hs hna hf
  · rcases h8 with hf | hf | hf | hf | hf | hf | hf | hf | ⟨b, c, hbc, hf⟩ | hf |
      hf | hf | hf | hf
    · exact R.eight_SL5 S hs hna hf
    · exact R.eight_SU5 S hs hna hf
    · exact R.eight_SL6 S hs hna hf
    · exact R.eight_SU6 S hs hna hf
    · exact R.eight_SL7 S hs hna hf
    · exact R.eight_Sp6 S hs hna hf
    · exact R.eight_Sp8 S hs hna hf
    · exact R.eight_OmegaPlus S hs hna hf
    · exact R.eight_OmegaMinus b c hbc S hs hna hf
    · exact R.eight_SL4 S hs hna hf
    · exact R.eight_Sp6_4 S hs hna hf
    · exact R.eight_SU5_4 S hs hna hf
    · exact R.eight_SU5_8 S hs hna hf
    · exact R.eight_F4 S hs hna hf
  · rcases h9 with ⟨e, he, he3, hf | hf⟩ | hf | hf | hf
    · exact R.nine_SL3 e he he3 S hs hna hf
    · exact R.nine_SU3 e he he3 S hs hna hf
    · exact R.nine_G2 S hs hna hf
    · exact R.nine_SL4 S hs hna hf
    · exact R.nine_SU4 S hs hna hf

end K148RowsS

structure Seitz82Balance : Prop where
  one : ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ 3 → 1 ≤ e →
    RowSOf148 (projSL 2 (GaloisField p e))
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    RowSOf148 (projSL 3 (GaloisField p e))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowSOf148 (projSU 3 p e)
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p →
    q.exponent = 1 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
      RowSOf148 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSOf148 (projSp 2 (GaloisField p 1))
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSOf148 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSOf148 (projSU 4 p 1)
  seven_SL2 : ∀ n : ℕ, 1 ≤ n → RowSOf148 (projSL 2 (GaloisField 2 n))
  seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowSOf148 (projSL 3 (GaloisField 2 n))
  seven_SU3 : ∀ n : ℕ, 1 ≤ n → RowSOf148 (projSU 3 2 n)
  seven_Sp4 : ∀ n : ℕ, 1 ≤ n → RowSOf148 (projSp 2 (GaloisField 2 n))
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowSOf148 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    q.p = 2 → RowSOf148 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_Sz : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group
  eight_SL5 : RowSOf148 (projSL 5 (GaloisField 2 1))
  eight_SU5 : RowSOf148 (projSU 5 2 1)
  eight_SL6 : RowSOf148 (projSL 6 (GaloisField 2 1))
  eight_SU6 : RowSOf148 (projSU 6 2 1)
  eight_SL7 : RowSOf148 (projSL 7 (GaloisField 2 1))
  eight_Sp6 : RowSOf148 (projSp 3 (GaloisField 2 1))
  eight_Sp8 : RowSOf148 (projSp 4 (GaloisField 2 1))
  eight_OmegaPlus : RowSOf148 (projOmegaPlus 4 (GaloisField 2 1))
  eight_OmegaMinus : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowSOf148 (projOmegaMinus 3 (GaloisField 2 1) b c)
  eight_SL4 : RowSOf148 (projSL 4 (GaloisField 2 2))
  eight_Sp6_4 : RowSOf148 (projSp 3 (GaloisField 2 2))
  eight_SU5_4 : RowSOf148 (projSU 5 2 2)
  eight_SU5_8 : RowSOf148 (projSU 5 2 3)
  eight_F4 : RowSOf148 (TauCeti.CFSGIndex.lie f4TwoIndex).Group

theorem K148RowsS.ofSeitz (hS : Seitz82Balance)
    (h1 : ∀ e : ℕ, 1 ≤ e → RowSOf148 (projSL 2 (GaloisField 3 e)))
    (h3 : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
      RowSOf148 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group)
    (h5 : ∀ n : ℕ, 5 ≤ n → n ≤ 12 → RowSOf148 (alternatingGroup (Fin n)))
    (h6 : ∀ s ∈ sporadics42, RowSOf148 (Spor s))
    (h9a : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf148 (projSL 3 (GaloisField 3 e)))
    (h9b : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf148 (projSU 3 3 e))
    (h9c : RowSOf148 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group)
    (h9d : RowSOf148 (projSL 4 (GaloisField 3 1))) (h9e : RowSOf148 (projSU 4 3 1)) :
    K148RowsS where
  one p e _ hp2 he := by
    by_cases hp3 : p = 3
    · subst hp3
      exact h1 e he
    · exact hS.one p e hp2 hp3 he
  two_SL := hS.two_SL
  two_SU := hS.two_SU
  three := h3
  four_G2 := hS.four_G2
  four_Sp := hS.four_Sp
  four_SL := hS.four_SL
  four_SU := hS.four_SU
  five := h5
  six := h6
  seven_SL2 := hS.seven_SL2
  seven_SL3 := hS.seven_SL3
  seven_SU3 := hS.seven_SU3
  seven_Sp4 := hS.seven_Sp4
  seven_SU4 := hS.seven_SU4
  seven_G2 := hS.seven_G2
  seven_D4 := hS.seven_D4
  seven_Sz := hS.seven_Sz
  seven_F4 := hS.seven_F4
  seven_Tits := hS.seven_Tits
  eight_SL5 := hS.eight_SL5
  eight_SU5 := hS.eight_SU5
  eight_SL6 := hS.eight_SL6
  eight_SU6 := hS.eight_SU6
  eight_SL7 := hS.eight_SL7
  eight_Sp6 := hS.eight_Sp6
  eight_Sp8 := hS.eight_Sp8
  eight_OmegaPlus := hS.eight_OmegaPlus
  eight_OmegaMinus := hS.eight_OmegaMinus
  eight_SL4 := hS.eight_SL4
  eight_Sp6_4 := hS.eight_Sp6_4
  eight_SU5_4 := hS.eight_SU5_4
  eight_SU5_8 := hS.eight_SU5_8
  eight_F4 := hS.eight_F4
  nine_SL3 := h9a
  nine_SU3 := h9b
  nine_G2 := h9c
  nine_SL4 := h9d
  nine_SU4 := h9e

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
