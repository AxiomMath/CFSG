module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgIso
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectA6

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (AutNoE27 NoE27 quotPCoreTwoCongr)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

@[expose] def IsType431 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* alternatingGroup (Fin 6))

structure CfgS431 (S : Type) [Group S] [Finite S] (A : Subgroup (MulAut S)) (σ : MulAut S)
    (K : Subgroup S) : Prop where
  isE27 : Late.IsE27 A
  mem : σ ∈ A
  ne_one : σ ≠ 1
  pRank_le : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3
  le_autFix : K ≤ autFix σ
  isSubnormal : (K.subgroupOf (autFix σ)).IsSubnormal
  isPerfect : Group.IsPerfect K
  map_mem : ∀ a ∈ A, ∀ k ∈ K, (a : MulAut S) k ∈ K
  isType : IsType431 (K ⧸ CFSG.pCore 2 K)
  faithful : ∀ a ∈ A, (∀ k ∈ K, (a : MulAut S) k * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) →
    a ∈ Subgroup.zpowers σ

@[expose] def ConclS431 (S : Type) [Group S] : Prop :=
  Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ Nonempty (S ≃* Blueprint.NativeSporadic.J3) ∨
    Nonempty (S ≃* projSp 3 (GaloisField 2 1)) ∨ Nonempty (S ≃* alternatingGroup (Fin 9)) ∨
    Nonempty (S ≃* projSp 2 (GaloisField 2 3))

@[expose] def RowS431 (S : Type) [Group S] [Finite S] : Prop :=
  ∀ (A : Subgroup (MulAut S)) (σ : MulAut S) (K : Subgroup S), CfgS431 S A σ K → ConclS431 S

@[expose] def NoCfgS431 (S : Type) [Group S] [Finite S] : Prop :=
  ∀ (A : Subgroup (MulAut S)) (σ : MulAut S) (K : Subgroup S), ¬ CfgS431 S A σ K

@[expose] def RowSOf431 (X : Type) [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → RowS431 S

theorem NoCfgS431.rowS431 {S : Type} [Group S] [Finite S] (h : NoCfgS431 S) : RowS431 S :=
  fun A σ K hc => absurd hc (h A σ K)

theorem rowSOf431_of_noCfg {X : Type} [Group X]
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* X) → NoCfgS431 S) : RowSOf431 X :=
  fun S _ _ hs hna hX => (h S hs hna hX).rowS431

structure K431RowsS : Prop where
  one : ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e → RowSOf431 (projSL 2 (GaloisField p e))
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    RowSOf431 (projSL 3 (GaloisField p e))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowSOf431 (projSU 3 p e)
  three : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    RowSOf431 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowSOf431 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSOf431 (projSp 2 (GaloisField p 1))
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSOf431 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSOf431 (projSU 4 p 1)
  five : ∀ n : ℕ, 5 ≤ n → n ≤ 12 → RowSOf431 (alternatingGroup (Fin n))
  six : ∀ s ∈ sporadics42, RowSOf431 (Spor s)
  seven_SL2 : ∀ n : ℕ, 1 ≤ n → RowSOf431 (projSL 2 (GaloisField 2 n))
  seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowSOf431 (projSL 3 (GaloisField 2 n))
  seven_SU3 : ∀ n : ℕ, 1 ≤ n → RowSOf431 (projSU 3 2 n)
  seven_Sp4 : ∀ n : ℕ, 1 ≤ n → RowSOf431 (projSp 2 (GaloisField 2 n))
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowSOf431 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowSOf431 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    RowSOf431 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_Sz : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    RowSOf431 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowSOf431 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowSOf431 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group
  eight_SL5 : RowSOf431 (projSL 5 (GaloisField 2 1))
  eight_SU5 : RowSOf431 (projSU 5 2 1)
  eight_SL6 : RowSOf431 (projSL 6 (GaloisField 2 1))
  eight_SU6 : RowSOf431 (projSU 6 2 1)
  eight_SL7 : RowSOf431 (projSL 7 (GaloisField 2 1))
  eight_Sp6 : RowSOf431 (projSp 3 (GaloisField 2 1))
  eight_Sp8 : RowSOf431 (projSp 4 (GaloisField 2 1))
  eight_OmegaPlus : RowSOf431 (projOmegaPlus 4 (GaloisField 2 1))
  eight_OmegaMinus : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowSOf431 (projOmegaMinus 3 (GaloisField 2 1) b c)
  eight_SL4 : RowSOf431 (projSL 4 (GaloisField 2 2))
  eight_Sp6_4 : RowSOf431 (projSp 3 (GaloisField 2 2))
  eight_SU5_4 : RowSOf431 (projSU 5 2 2)
  eight_SU5_8 : RowSOf431 (projSU 5 2 3)
  eight_F4 : RowSOf431 (TauCeti.CFSGIndex.lie f4TwoIndex).Group
  nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf431 (projSL 3 (GaloisField 3 e))
  nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf431 (projSU 3 3 e)
  nine_G2 : RowSOf431 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group
  nine_SL4 : RowSOf431 (projSL 4 (GaloisField 3 1))
  nine_SU4 : RowSOf431 (projSU 4 3 1)

namespace K431RowsS

variable {S : Type} [Group S] [Finite S]

theorem rowS_of_list42 (R : K431RowsS) (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : Census.List42 S) : RowS431 S := by
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

end K431RowsS

section Cover

variable {K : Type} [Group K] [Finite K]

@[expose] noncomputable def coverHom (e : K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 6)) :
    K →* alternatingGroup (Fin 6) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 K))

theorem coverHom_surjective (e : K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 6)) :
    Function.Surjective (coverHom e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem coverHom_ker (e : K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 6)) :
    (coverHom e).ker = CFSG.pCore 2 K := by
  ext x
  rw [MonoidHom.mem_ker, coverHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem not_three_dvd_card_pCore_two : ¬ 3 ∣ Nat.card (CFSG.pCore 2 K) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)).exists_card_eq
  rw [hn] at h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h)
  omega

theorem not_three_dvd_card_ker_coverHom (e : K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 6)) :
    ¬ 3 ∣ Nat.card (coverHom e).ker := by
  rw [coverHom_ker]
  exact not_three_dvd_card_pCore_two

theorem card_eq_of_isType431 (h : IsType431 (K ⧸ CFSG.pCore 2 K)) :
    Nat.card K = 360 * Nat.card (CFSG.pCore 2 K) := by
  obtain ⟨e⟩ := h
  rw [Sec8.Hering611R.card_eq_of_surjective (coverHom e) (coverHom_surjective e), coverHom_ker]

theorem five_dvd_card_of_isType431 (h : IsType431 (K ⧸ CFSG.pCore 2 K)) : 5 ∣ Nat.card K := by
  rw [card_eq_of_isType431 h]
  exact Dvd.dvd.mul_right (by norm_num) _

theorem nine_dvd_card_of_isType431 (h : IsType431 (K ⧸ CFSG.pCore 2 K)) : 9 ∣ Nat.card K := by
  rw [card_eq_of_isType431 h]
  exact Dvd.dvd.mul_right (by norm_num) _

theorem le_card_of_isType431 (h : IsType431 (K ⧸ CFSG.pCore 2 K)) : 360 ≤ Nat.card K := by
  rw [card_eq_of_isType431 h]
  have : 0 < Nat.card (CFSG.pCore 2 K) := Nat.card_pos
  nlinarith

theorem exists_elemAbelian_nine_of_isType431 (h : IsType431 (K ⧸ CFSG.pCore 2 K)) :
    ∃ R : Subgroup K, CFSG.Open.IsElemAbelian 3 R ∧ Nat.card R = 9 ∧ R ⊓ CFSG.pCore 2 K = ⊥ := by
  obtain ⟨e⟩ := h
  obtain ⟨R, hR, hR9, hRker⟩ := Sec8.Hering611R.exists_elemAbelian_nine (coverHom e)
    (coverHom_surjective e) (not_three_dvd_card_ker_coverHom e)
  exact ⟨R, hR, hR9, by rwa [coverHom_ker] at hRker⟩

theorem eq_one_of_mem_center_of_isType431 (h : IsType431 (K ⧸ CFSG.pCore 2 K)) {z : K}
    (hz : z ∈ Subgroup.center K) (h9 : z ^ 9 = 1) : z = 1 := by
  obtain ⟨e⟩ := h
  exact Sec8.Hering611R.eq_one_of_mem_center (coverHom e) (coverHom_surjective e)
    (not_three_dvd_card_ker_coverHom e) hz h9

theorem center_quot_eq_bot_of_isType431 (h : IsType431 (K ⧸ CFSG.pCore 2 K)) :
    Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥ := by
  obtain ⟨e⟩ := h
  refine RonanK429.center_eq_bot_of_mulEquiv e ?_
  exact alternatingGroup.center_eq_bot (by simp)

end Cover

theorem isType431_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) (h : IsType431 Y) :
    IsType431 X := by
  obtain ⟨ψ⟩ := h
  exact ⟨φ.trans ψ⟩

section NoCfg

variable {S : Type} [Group S] [Finite S]

theorem noCfgS431_of_autNoE27 (h : AutNoE27 S) : NoCfgS431 S :=
  fun A _ _ hc => h A hc.isE27

theorem CfgS431.five_dvd_card {A : Subgroup (MulAut S)} {σ : MulAut S} {K : Subgroup S}
    (hc : CfgS431 S A σ K) : 5 ∣ Nat.card S :=
  (five_dvd_card_of_isType431 hc.isType).trans (Subgroup.card_subgroup_dvd_card K)

theorem CfgS431.nine_dvd_card {A : Subgroup (MulAut S)} {σ : MulAut S} {K : Subgroup S}
    (hc : CfgS431 S A σ K) : 9 ∣ Nat.card S :=
  (nine_dvd_card_of_isType431 hc.isType).trans (Subgroup.card_subgroup_dvd_card K)

theorem noCfgS431_of_not_five_dvd (h : ¬ 5 ∣ Nat.card S) : NoCfgS431 S :=
  fun _ _ _ hc => h hc.five_dvd_card

theorem noCfgS431_of_not_three_dvd (h : ¬ 3 ∣ Nat.card S) : NoCfgS431 S :=
  fun _ _ _ hc => h ((show 3 ∣ 9 by norm_num).trans hc.nine_dvd_card)

theorem noCfgS431_of_card_lt (h : Nat.card S < 720) : NoCfgS431 S := fun _ σ K hc => by
  have hle := le_card_of_isType431 hc.isType
  obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card K
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hm1 : m = 1 := by
    rcases m with _ | _ | m
    · omega
    · rfl
    · nlinarith
  rw [hm1, mul_one] at hm
  have hK : K = ⊤ := Subgroup.card_eq_iff_eq_top K |>.mp hm.symm
  apply hc.ne_one
  ext x
  have hx : x ∈ autFix σ := hc.le_autFix (hK ▸ Subgroup.mem_top x)
  exact hx

end NoCfg

section Iso

variable {S T : Type} [Group S] [Group T]

theorem CfgS431.map [Finite S] [Finite T] {A : Subgroup (MulAut S)} {σ : MulAut S}
    {K : Subgroup S} (h : CfgS431 S A σ K) (e : S ≃* T) :
    CfgS431 T (A.map (MulAut.congr e).toMonoidHom) (MulAut.congr e σ) (K.map e.toMonoidHom) := by
  have hfix := autFix_congr e σ
  refine
    { isE27 := h.isE27.map (MulAut.congr e)
      mem := Subgroup.mem_map_of_mem _ h.mem
      ne_one := fun h1 => h.ne_one ((MulAut.congr e).injective (by rw [h1, map_one]))
      pRank_le := by
        rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
        exact h.pRank_le
      le_autFix := by rw [hfix]; exact Subgroup.map_mono h.le_autFix
      isSubnormal := ?_
      isPerfect := ?_
      map_mem := ?_
      isType := ?_
      faithful := ?_ }
  · rw [hfix, ← RonanK429.map_subgroupOf_equivMap]
    exact h.isSubnormal.map (MulEquiv.surjective _)
  · haveI := h.isPerfect
    exact Group.IsPerfect.map _
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨k, hk, rfl⟩
    refine ⟨a k, h.map_mem a ha k hk, ?_⟩
    change e (a k) = e (a (e.symm (e k)))
    rw [MulEquiv.symm_apply_apply]
  · exact isType431_of_mulEquiv
      (quotPCoreTwoCongr (K.equivMapOfInjective e.toMonoidHom e.injective)).symm h.isType
  · rintro _ ⟨a, ha, rfl⟩ hK
    have hinj : Function.Injective (e.toMonoidHom.comp K.subtype) :=
      e.injective.comp K.subtype_injective
    have ha' : a ∈ Subgroup.zpowers σ := by
      refine h.faithful a ha fun k hk => ?_
      have h1 := hK (e k) ⟨k, hk, rfl⟩
      have h2 : ((MulAut.congr e).toMonoidHom a) (e k) * (e k)⁻¹ =
          e.toMonoidHom (a k * k⁻¹) := by
        change e (a (e.symm (e k))) * (e k)⁻¹ = e (a k * k⁻¹)
        rw [MulEquiv.symm_apply_apply, map_mul, map_inv]
      rw [h2] at h1
      exact (RonanK429.map_mem_pCoreOf_map_iff 2 e.toMonoidHom hinj
        (Subgroup.mul_mem _ (h.map_mem a ha k hk) (Subgroup.inv_mem _ hk))).mp h1
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    change (MulAut.congr e).toMonoidHom (σ ^ m) ∈ _
    rw [map_zpow]
    exact Subgroup.zpow_mem_zpowers _ m

theorem ConclS431.of_mulEquiv (e : S ≃* T) (h : ConclS431 T) : ConclS431 S := by
  rcases h with h | h | h | h | h <;> obtain ⟨φ⟩ := h
  · exact Or.inl ⟨e.trans φ⟩
  · exact Or.inr (Or.inl ⟨e.trans φ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans φ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans φ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans φ⟩)))

theorem RowS431.of_mulEquiv [Finite S] [Finite T] (e : S ≃* T) (h : RowS431 T) : RowS431 S :=
  fun _ _ _ hc => ConclS431.of_mulEquiv e (h _ _ _ (hc.map e))

theorem NoCfgS431.of_mulEquiv [Finite S] [Finite T] (e : S ≃* T) (h : NoCfgS431 T) :
    NoCfgS431 S :=
  fun _ _ _ hc => h _ _ _ (hc.map e)

theorem rowSOf431_of_rowS431 {X : Type} [Group X] [Finite X] (h : RowS431 X) : RowSOf431 X :=
  fun _ _ _ _ _ ⟨e⟩ => h.of_mulEquiv e

theorem rowSOf431_of_noCfgS431 {X : Type} [Group X] [Finite X] (h : NoCfgS431 X) :
    RowSOf431 X :=
  rowSOf431_of_rowS431 h.rowS431

theorem rowSOf431_of_concl {X : Type} [Group X] (h : ConclS431 X) : RowSOf431 X :=
  fun _ _ _ _ _ ⟨e⟩ _ _ _ _ => ConclS431.of_mulEquiv e h

end Iso

theorem rowSOf431_alternatingGroup_nine : RowSOf431 (alternatingGroup (Fin 9)) :=
  rowSOf431_of_concl (Or.inr (Or.inr (Or.inr (Or.inl ⟨MulEquiv.refl _⟩))))

theorem rowSOf431_sp6_two : RowSOf431 (projSp 3 (GaloisField 2 1)) :=
  rowSOf431_of_concl (Or.inr (Or.inr (Or.inl ⟨MulEquiv.refl _⟩)))

theorem rowSOf431_sp4_eight : RowSOf431 (projSp 2 (GaloisField 2 3)) :=
  rowSOf431_of_concl (Or.inr (Or.inr (Or.inr (Or.inr ⟨MulEquiv.refl _⟩))))

end CFSG.RankThree.PartTwo.Sec4.Ronan431
