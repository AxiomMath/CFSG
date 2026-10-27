module

public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofMax
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec8.Outer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)

@[expose] def NoE9 (X : Type*) [Group X] : Prop :=
  ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E ≤ 3

@[expose] def OuterThreeRankTwo (X : Type*) [Group X] : Prop :=
  ∀ Γ : Subgroup (MulAut X), IsElemAbelian 3 Γ → (∃ τ ∈ Γ, ¬ IsInnerAut τ) → Nat.card Γ ≤ 9

theorem isElemAbelian_map {X Y : Type*} [Group X] [Group Y] {p : ℕ} {Γ : Subgroup X}
    (hΓ : IsElemAbelian p Γ) (f : X →* Y) : IsElemAbelian p (Γ.map f) :=
  CFSG.SectionRank.isElemAbelian_map hΓ _

theorem NoE9.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (hY : NoE9 Y) (e : X ≃* Y) :
    NoE9 X := by
  intro E hE
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact hY _ (isElemAbelian_map hE _)

theorem OuterThreeRankTwo.of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (hY : OuterThreeRankTwo Y) (e : X ≃* Y) : OuterThreeRankTwo X := by
  intro Γ hΓ ⟨τ, hτΓ, hτ⟩
  set f : MulAut X →* MulAut Y := (MulAut.congr e).toMonoidHom with hf
  have hinj : Function.Injective f := (MulAut.congr e).injective
  have hcard : Nat.card (Γ.map f) = Nat.card Γ := Subgroup.card_map_of_injective hinj
  rw [← hcard]
  refine hY _ (isElemAbelian_map hΓ f) ⟨f τ, Subgroup.mem_map_of_mem f hτΓ, fun h => hτ ?_⟩
  exact (isInnerAut_congr e τ).mp h

theorem isElemAbelian_autThetaQuot {G : Type} [Group G] [Finite G] {A L : Subgroup G}
    (hAe : IsElemAbelian 3 A) : IsElemAbelian 3 (autThetaQuot A L) :=
  ⟨⟨⟨fun x y => Subtype.ext (Item82OneProof.commute_of_mem_autThetaQuot hAe x.2 y.2).eq⟩⟩,
    fun _ hβ => Item82OneProof.pow_three_of_mem_autThetaQuot hAe hβ⟩

section Hyp


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}

theorem card_autThetaQuot_eq_27 (h : Hyp81 G A c L a) (h81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) : Nat.card (autThetaQuot A L) = 27 := by
  have hAe := h.mem_partTwoF.1
  have hset := Sec13.sectionCentralizer_eq_inf hAN
  rw [h.sectionCentralizer_eq] at hset
  have heq : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c := SetLike.coe_injective hset.symm
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hAe.2 c h.mem_A) h.ne_one
  have hmul := Sec13.card_inf_mul_card_autThetaQuot hAN
  rw [heq, hc3, h81] at hmul
  omega

theorem false_of_outerThreeRankTwo (h : Hyp81 G A c L a) (h81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hK : OuterThreeRankTwo (L ⧸ aschbacherSolvableCore 3 L)) : False := by
  have h27 := card_autThetaQuot_eq_27 h h81 hAN
  have hτ : thetaQuotMulAut L (compAction L ⟨a, h.a_mem_normalizer⟩) ∈ autThetaQuot A L :=
    mem_autThetaQuot_iff.mpr ⟨a, h.a_mem_normalizer, h.a_mem, rfl⟩
  have h9 := hK _ (isElemAbelian_autThetaQuot h.mem_partTwoF.1) ⟨_, hτ, h.not_isInnerAut_induced⟩
  omega

theorem nine_le_card_inf_inner (h : Hyp81 G A c L a) (h81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L)) :
    9 ≤ Nat.card (autThetaQuot A L ⊓ (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range : Subgroup _) := by
  have hAe := h.mem_partTwoF.1
  set τ := thetaQuotMulAut L (compAction L ⟨a, hAN h.a_mem⟩) with hτ
  have hτΓ : τ ∈ autThetaQuot A L := mem_autThetaQuot_iff.mpr ⟨a, hAN h.a_mem, h.a_mem, rfl⟩
  have hτout : ¬ IsInnerAut τ := h.not_isInnerAut_induced
  have hk : ∀ β ∈ autThetaQuot A L, ∃ k < 3, τ ^ k * β ∈
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
        MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := fun β hβ =>
    hcyc τ β (Item82OneProof.commute_of_mem_autThetaQuot hAe hτΓ hβ)
      (Item82OneProof.pow_three_of_mem_autThetaQuot hAe hτΓ)
      (Item82OneProof.pow_three_of_mem_autThetaQuot hAe hβ) hτout
  have hle3 := card_le_three_mul_card_inf_of_forall_pow_mul_mem hτΓ hk
  rw [card_autThetaQuot_eq_27 h h81 hAN] at hle3
  omega

theorem three_dvd_card_of_hyp81 (h : Hyp81 G A c L a) (h81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L)) :
    3 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
  have h9 := nine_le_card_inf_inner h h81 hAN hcyc
  obtain ⟨⟨β, hβΓ, x, rfl⟩, hβ1⟩ : ∃ β : (autThetaQuot A L ⊓
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
        MulAut (L ⧸ aschbacherSolvableCore 3 L)).range : Subgroup _), β ≠ 1 := by
    have : Nontrivial (autThetaQuot A L ⊓ (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
        MulAut (L ⧸ aschbacherSolvableCore 3 L)).range : Subgroup _) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne 1
  have hβ1' : MulAut.conj x ≠ 1 := fun h1 => hβ1 (Subtype.ext h1)
  have ho : orderOf (MulAut.conj x) = 3 :=
    orderOf_eq_prime (Item82OneProof.pow_three_of_mem_autThetaQuot h.mem_partTwoF.1 hβΓ) hβ1'
  have h1 : orderOf (MulAut.conj x) ∣ orderOf x := orderOf_map_dvd _ x
  rw [ho] at h1
  exact h1.trans (orderOf_dvd_natCard x)

theorem false_of_noE9 (h : Hyp81 G A c L a) (h81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hE9 : NoE9 (Sec8.barCentralizer (Subgroup.zpowers a) L)) : False := by
  have hAe := h.mem_partTwoF.1
  have hinj := Item82OneProof.conj_injective_of_center_eq_bot hZ
  set ι : L ⧸ aschbacherSolvableCore 3 L →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    MulAut.conj with hι
  set Γ := autThetaQuot A L with hΓ
  set τ := thetaQuotMulAut L (compAction L ⟨a, hAN h.a_mem⟩) with hτ
  have hτΓ : τ ∈ Γ := mem_autThetaQuot_iff.mpr ⟨a, hAN h.a_mem, h.a_mem, rfl⟩
  have h9 := nine_le_card_inf_inner h h81 hAN hcyc
  set X : Subgroup (L ⧸ aschbacherSolvableCore 3 L) := (Γ ⊓ ι.range).comap ι with hX
  have hXcard : Nat.card X = Nat.card (Γ ⊓ ι.range : Subgroup _) := by
    have hmap : X.map ι = Γ ⊓ ι.range := Subgroup.map_comap_eq_self inf_le_right
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  have hXe : IsElemAbelian 3 X := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have h1 := (Item82OneProof.commute_of_mem_autThetaQuot hAe
        (Subgroup.mem_comap.mp x.2).1 (Subgroup.mem_comap.mp y.2).1).eq
      change ι ((x : L ⧸ aschbacherSolvableCore 3 L) * y) =
        ι ((y : L ⧸ aschbacherSolvableCore 3 L) * x)
      rw [map_mul, map_mul]
      exact h1
    · rw [map_pow, map_one]
      exact Item82OneProof.pow_three_of_mem_autThetaQuot hAe (Subgroup.mem_comap.mp hx).1
  have hXC : X ≤ Sec8.barCentralizer (Subgroup.zpowers a) L := by
    intro x hx
    rw [barCentralizer_zpowers_eq_autFix (hAN h.a_mem)]
    have hcomm := (Item82OneProof.commute_of_mem_autThetaQuot hAe hτΓ
      (Subgroup.mem_comap.mp hx).1).eq
    apply hinj
    change MulAut.conj (τ x) = MulAut.conj x
    rw [← mul_mulAutConj_mul_inv]
    change τ * ι x * τ⁻¹ = ι x
    rw [hcomm, mul_inv_cancel_right]
  have hcard : Nat.card (X.subgroupOf (Sec8.barCentralizer (Subgroup.zpowers a) L)) =
      Nat.card X := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv
  have hEe : IsElemAbelian 3 (X.subgroupOf (Sec8.barCentralizer (Subgroup.zpowers a) L)) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have h1 := congrArg Subtype.val (hXe.1.is_comm.comm
        ⟨((x : Sec8.barCentralizer (Subgroup.zpowers a) L) : L ⧸ aschbacherSolvableCore 3 L),
          Subgroup.mem_subgroupOf.mp x.2⟩
        ⟨((y : Sec8.barCentralizer (Subgroup.zpowers a) L) : L ⧸ aschbacherSolvableCore 3 L),
          Subgroup.mem_subgroupOf.mp y.2⟩)
      exact h1
    · have h1 := hXe.2 _ (Subgroup.mem_subgroupOf.mp hx)
      change ((x : L ⧸ aschbacherSolvableCore 3 L)) ^ 3 = 1
      exact h1
  have hE := hE9 _ hEe
  have h9' : 9 ≤ Nat.card (Γ ⊓ ι.range : Subgroup _) := h9
  rw [hcard, hXcard] at hE
  omega

end Hyp

@[expose] def KF82TwoNoE9PSL2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p e : ℕ), p.Prime → Nat.card K = p ^ e → (p ≠ 3 ∨ e = 1) →
    NoE9 (CFSG.GorensteinWalter.PSL2 K)

@[expose] def KF82TwoNoE9PGU : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), Even f → Sec8.IsoPGUThree X (2 ^ f) → NoE9 X

@[expose] def KF82TwoPSL3Odd : Prop :=
  ∀ n : ℕ, Odd n → OuterThreeRankTwo (projSL 3 (GaloisField 2 n))

section Kinds


@[expose] def KF82TwoLThreeKinds : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (n : ℕ), Even n → 1 ≤ n →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)) → x ^ 3 = 1 →
    InducesStdKind L x .diagonal →
      ¬ InducesStdKind L x .field ∧ ¬ InducesStdKind L x .graphField

@[expose] def Item82TwoSLThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    Hyp81 G A c L a → Nat.card A = 81 → ∀ n : ℕ, Even n → 4 ≤ n →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n →
      IsEmpty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K)

@[expose] def Item82TwoPSL2Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    Hyp81 G A c L a → Nat.card A = 81 → ∀ e : ℕ, 2 ≤ e →
      IsEmpty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * e)))

end Kinds

end CFSG.RankThree.PartTwo.Sec8.Item82Proof
