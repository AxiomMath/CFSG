module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93
public import CFSG.RankThree.PartTwo.Sec19.Item194Proof
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock IsTwoPrimeComponent NineThreeConclusion barM
  InClassXBlock NineThreeTwo NineThreeThree NineThreeFour NineThreeFive NineThreeEight
  IsClassicalTwoOrG2 IsParabolicTwo Asc81bEightFive)
open CFSG.QuasithinUnique (IsShort2 IsSylowTwoOf)

namespace Item19Res3Proof

section BarM

variable {G : Type} [Group G]

@[expose] noncomputable def barMHom {X K : Subgroup G} (hKX : K ≤ X) : ↥K →* ↥X ⧸ CFSG.pCore 2 ↥X :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hKX)

theorem ker_barMHom {X K : Subgroup G} (hKX : K ≤ X)
    (h : K ⊓ CFSG.Open.pCoreOf 2 X = CFSG.Open.pCoreOf 2 K) :
    (barMHom hKX).ker = CFSG.pCore 2 ↥K := by
  ext k
  rw [MonoidHom.mem_ker, barMHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Item194Proof.mem_pCore_iff, Item194Proof.mem_pCore_iff, ← h,
    Subgroup.coe_inclusion]
  exact ⟨fun hk => ⟨k.2, hk⟩, fun hk => hk.2⟩

theorem range_barMHom {X K : Subgroup G} (hKX : K ≤ X) : (barMHom hKX).range = barM X K := by
  rw [barMHom, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

@[expose] noncomputable def barMEquiv {X K : Subgroup G} (hKX : K ≤ X)
    (h : K ⊓ CFSG.Open.pCoreOf 2 X = CFSG.Open.pCoreOf 2 K) :
    ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(barM X K) :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_barMHom hKX h)).symm.trans
    (QuotientGroup.quotientKerEquivRange (barMHom hKX))).trans
    (MulEquiv.subgroupCongr (range_barMHom hKX))

theorem barMEquiv_mk {X K : Subgroup G} (hKX : K ≤ X)
    (h : K ⊓ CFSG.Open.pCoreOf 2 X = CFSG.Open.pCoreOf 2 K) (k : ↥K) :
    ((barMEquiv hKX h (QuotientGroup.mk k) : ↥(barM X K)) : ↥X ⧸ CFSG.pCore 2 ↥X) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) (Subgroup.inclusion hKX k) :=
  rfl

theorem map_starIm_barMEquiv {X K : Subgroup G} (hKX : K ≤ X)
    (h : K ⊓ CFSG.Open.pCoreOf 2 X = CFSG.Open.pCoreOf 2 K) (Y : Subgroup G) :
    (starIm K Y).map (barMEquiv hKX h).toMonoidHom = (barM X (Y ⊓ K)).subgroupOf (barM X K) := by
  ext x
  constructor
  · rintro ⟨q, ⟨k, hk, rfl⟩, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨Subgroup.inclusion hKX k, ?_, ?_⟩
    · simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk ⊢
      exact ⟨hk, k.2⟩
    · rfl
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨m, hm, hmx⟩ := hx
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hm
    refine ⟨QuotientGroup.mk ⟨(m : G), hm.2⟩, ⟨⟨(m : G), hm.2⟩, ?_, rfl⟩, ?_⟩
    · simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact hm.1
    · apply Subtype.ext
      rw [MulEquiv.coe_toMonoidHom, barMEquiv_mk, ← hmx]
      rfl

end BarM

section Transport

variable {X X' : Type} [Group X] [Group X']

theorem nonempty_mulEquiv_trans {M : Type*} [Group M] (e : X' ≃* X) (h : Nonempty (X ≃* M)) :
    Nonempty (X' ≃* M) :=
  h.map e.trans

theorem isList194_of_mulEquiv (e : X' ≃* X) (h : IsList194 X) : IsList194 X' := by
  have t := fun {M : Type} [Group M] (h : Nonempty (X ≃* M)) => nonempty_mulEquiv_trans e h
  rcases h with ⟨n, hn, f | f | f | ⟨K, hK1, hK2, hK, f⟩⟩ | f | f | f | f | f | f | f | f |
      ⟨b, c, hbc, f⟩ | f
  · exact Or.inl ⟨n, hn, Or.inl (t f)⟩
  · exact Or.inl ⟨n, hn, Or.inr (Or.inl (t f))⟩
  · exact Or.inl ⟨n, hn, Or.inr (Or.inr (Or.inl (t f)))⟩
  · exact Or.inl ⟨n, hn, Or.inr (Or.inr (Or.inr ⟨K, hK1, hK2, hK, t f⟩))⟩
  · exact Or.inr (Or.inl (t f))
  · exact Or.inr (Or.inr (Or.inl (t f)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (t f))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (t f)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (t f))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (t f)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (t f))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (t f)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨b, c, hbc, t f⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (t f))))))))))

theorem isSmall194_of_mulEquiv (e : X' ≃* X) (h : IsSmall194 X) : IsSmall194 X' := by
  rcases h with f | f
  · exact Or.inl (nonempty_mulEquiv_trans e f)
  · exact Or.inr (nonempty_mulEquiv_trans e f)

theorem isTripleA6_of_mulEquiv (e : X' ≃* X) (h : IsTripleA6 X) : IsTripleA6 X' := by
  obtain ⟨hZ, ⟨f⟩⟩ := h
  have hc : (Subgroup.center X').map (e : X' →* X) = Subgroup.center X :=
    Subgroup.map_center_eq e
  refine ⟨?_, ⟨(QuotientGroup.congr _ _ e hc).trans f⟩⟩
  rw [← hZ, ← hc, Subgroup.card_map_of_injective e.injective]

theorem isExtOf_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : X' ≃* X)
    (h : Sec4.IsExtOf X A B) : Sec4.IsExtOf X' A B := by
  obtain ⟨N, hN, ⟨f⟩, ⟨g⟩⟩ := h
  refine ⟨N.comap (e : X' →* X), inferInstance, ⟨?_⟩, ⟨?_⟩⟩
  · exact (MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm' e N)).trans
      ((N.equivMapOfInjective _ e.symm.injective).symm.trans f)
  · exact (QuotientGroup.congr _ _ e (Subgroup.map_comap_eq_self_of_surjective
      e.surjective N)).trans g

end Transport

section Ranks

variable {G : Type} [Group G] [Finite G]

theorem pRank_barM_le {X K : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (barM X K) ≤ CFSG.Open.pRank p X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hker : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥X) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).exists_card_eq
    rw [hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  calc CFSG.Open.pRank p (barM X K)
      ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) :=
        CFSG.SectionRank.pRank_mono hp.one_lt le_top
    _ = CFSG.Open.pRank p (⊤ : Subgroup ↥X) := CFSG.SectionRank.pRank_quotient_eq _ hker
    _ = CFSG.Open.pRank p X := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup X).symm

theorem pRank_top_eq_of_mulEquiv_barM {X K : Subgroup G} {Y : Type} [Group Y] [Finite Y]
    {p : ℕ} (hp : p.Prime) (e : Y ≃* ↥(barM X K)) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) = CFSG.Open.pRank p (barM X K) := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]

end Ranks

section Alternating

@[expose] def shear3 (v : Fin 4 → ZMod 3) : Equiv.Perm (Fin 4 × ZMod 3) :=
  Equiv.prodShear (Equiv.refl _) fun i => Equiv.addRight (v i)

theorem shear3_apply (v : Fin 4 → ZMod 3) (x : Fin 4 × ZMod 3) :
    shear3 v x = (x.1, x.2 + v x.1) :=
  rfl

@[expose] def shearHom (m : ℕ) :
    Multiplicative (Fin 4 → ZMod 3) →* Equiv.Perm ((Fin 4 × ZMod 3) ⊕ Fin m) where
  toFun v := Equiv.sumCongr (shear3 (Multiplicative.toAdd v)) (Equiv.refl _)
  map_one' := by
    ext x
    rcases x with x | x <;> simp [shear3_apply]
  map_mul' v w := by
    ext x
    rcases x with x | x
    · simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.Perm.coe_mul, Function.comp_apply,
        shear3_apply, toAdd_mul, Pi.add_apply]
      congr 2
      ring
    · simp

theorem shearHom_injective (m : ℕ) : Function.Injective (shearHom m) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have hv' : ∀ i : Fin 4, Multiplicative.toAdd v i = 0 := by
    intro i
    have h := congrArg (fun σ : Equiv.Perm ((Fin 4 × ZMod 3) ⊕ Fin m) => σ (Sum.inl (i, 0))) hv
    simp only [shearHom, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.sumCongr_apply, Sum.map_inl,
      shear3_apply, zero_add, Equiv.Perm.coe_one, id_eq, Sum.inl.injEq, Prod.mk.injEq,
      true_and] at h
    exact h
  have : Multiplicative.toAdd v = 0 := funext hv'
  exact this

theorem sign_eq_one_of_pow_three' {α : Type*} [DecidableEq α] [Fintype α] {σ : Equiv.Perm α}
    (hσ : σ ^ 3 = 1) : Equiv.Perm.sign σ = 1 := by
  have h := congrArg Equiv.Perm.sign hσ
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

theorem four_le_pRank_alternatingGroup {N : ℕ} (hN : 12 ≤ N) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(alternatingGroup (Fin N))) := by
  set m := N - 12 with hm
  let e : (Fin 4 × ZMod 3) ⊕ Fin m ≃ Fin N :=
    ((Equiv.sumCongr (finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin 12) (Equiv.refl _)).trans
      finSumFinEquiv).trans (finCongr (by omega))
  set φ : Multiplicative (Fin 4 → ZMod 3) →* Equiv.Perm (Fin N) :=
    (e.permCongrHom).toMonoidHom.comp (shearHom m) with hφ
  have hφinj : Function.Injective φ :=
    (e.permCongrHom.injective).comp (shearHom_injective m)
  have h3 : ∀ x : ZMod 3, 3 • x = 0 := by decide
  have hpow : ∀ v : Multiplicative (Fin 4 → ZMod 3), v ^ 3 = 1 := by
    intro v
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    exact h3 _
  have hcomm : ∀ v w : Multiplicative (Fin 4 → ZMod 3), v * w = w * v := fun v w => mul_comm v w
  have hle : 4 ≤ CFSG.Open.pRank 3 (alternatingGroup (Fin N)) := by
    refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) hcomm hpow ?_ φ hφinj ?_
    · rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
        ZMod.card, Fintype.card_fin]
    · rintro _ ⟨v, rfl⟩
      rw [Equiv.Perm.mem_alternatingGroup]
      exact sign_eq_one_of_pow_three' (by rw [← map_pow, hpow, map_one])
  rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at hle

end Alternating

section Setting

variable {G : Type} [Group G] [Finite G]

theorem twoCore_le_of_asc81bHyp {X S : Subgroup G} (h : Asc81bHyp X S) :
    CFSG.Open.pCoreOf 2 X ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact AGLEmbedding.le_of_two_radical h.twoRadical.1 h.twoRadical.2.2
    (CFSG.LieType.BorelTits.pCoreOf_le 2 X) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))

theorem isPGroup_of_asc81bHyp {X S : Subgroup G} (h : Asc81bHyp X S) : IsPGroup 2 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊓ Subgroup.normalizer (S : Set G))
  rwa [← h.twoRadical.2.2] at h2

theorem barM_inf_ne {X S K : Subgroup G} (h : Asc81bHyp X S) (hK : IsWeakSBlock X S K) :
    barM X (Subgroup.normalizer (S : Set G) ⊓ K) ≠ barM X K := by
  intro heq
  apply hK.not_le_normalizer
  intro k hk
  have hkX : k ∈ X := hK.le hk
  have hm : QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨k, hkX⟩ : ↥X) ∈ barM X K :=
    ⟨⟨k, hkX⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  rw [← heq] at hm
  obtain ⟨y, hy, hyk⟩ := hm
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
  have h1 : y⁻¹ * ⟨k, hkX⟩ ∈ CFSG.pCore 2 ↥X := QuotientGroup.eq.mp hyk
  have h2 : ((y⁻¹ * ⟨k, hkX⟩ : ↥X) : G) ∈ S :=
    twoCore_le_of_asc81bHyp h ((Item194Proof.mem_pCore_iff _).mp h1)
  have e : k = (y : G) * ((y⁻¹ * ⟨k, hkX⟩ : ↥X) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem _ hy.1 (Subgroup.le_normalizer h2)

theorem isScriptLBlock_of_isShort2 {X L : Subgroup G} (hL : IsTwoPrimeComponent X L)
    (hs : IsShort2 L) (ht : IsTypeScriptL L) : IsScriptLBlock X L :=
  ⟨⟨IsShort2.isShort hs, hL.le, hL.isSubnormal_subgroupOf⟩, ht⟩

omit [Finite G] in
theorem barM_inf_le (X Y K : Subgroup G) : barM X (Y ⊓ K) ≤ barM X K := by
  rintro _ ⟨m, hm, rfl⟩
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hm
  exact ⟨m, Subgroup.mem_subgroupOf.mpr hm.2, rfl⟩

theorem isSylowTwoOf_inf_of_card {X K S : Subgroup G} (hK : IsTwoPrimeComponent X K)
    (hOS : CFSG.Open.pCoreOf 2 X ≤ S) (hS2 : IsPGroup 2 S)
    {T : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} (hT : IsSylowTwoOf T (barM X K))
    (hcard : Nat.card (barM X (S ⊓ K)) = Nat.card T) : IsSylowTwoOf (S ⊓ K) K := by
  refine ⟨inf_le_right, hS2.to_le inf_le_left, ?_⟩
  have hinf := hK.inf_twoCore
  set e := barMEquiv hK.le hinf with he
  set H : Subgroup ↥K := (S ⊓ K).subgroupOf K with hH
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker ≤ H := by
    intro k hk
    rw [QuotientGroup.ker_mk'] at hk
    have hk' : (k : G) ∈ K ⊓ CFSG.Open.pCoreOf 2 X := by
      rw [hinf]
      exact (Item194Proof.mem_pCore_iff k).mp hk
    rw [hH, Subgroup.mem_subgroupOf]
    exact ⟨hOS hk'.2, k.2⟩
  have h1 : (starIm K (S ⊓ K)).index = H.index :=
    Subgroup.index_map_eq H (QuotientGroup.mk'_surjective _) hker
  have h2 : ((starIm K (S ⊓ K)).map e.toMonoidHom).index = (starIm K (S ⊓ K)).index :=
    Subgroup.index_map_eq _ e.surjective (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
      exact bot_le)
  rw [map_starIm_barMEquiv, inf_assoc, inf_idem] at h2
  have hle : barM X (S ⊓ K) ≤ barM X K := barM_inf_le X S K
  have h3 : ((barM X (S ⊓ K)).subgroupOf (barM X K)).index =
      (T.subgroupOf (barM X K)).index := by
    have ha := ((barM X (S ⊓ K)).subgroupOf (barM X K)).index_mul_card
    have hb := (T.subgroupOf (barM X K)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at ha
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv] at hb
    rw [hcard] at ha
    have hpos : 0 < Nat.card T := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (ha.trans hb.symm)
  rw [← h1, ← h2, h3]
  exact hT.2.2

end Setting

section Cases

variable {G : Type} [Group G] [Finite G]

@[expose] def Concl194Wide (K N : Subgroup G) : Prop :=
  (IsList194 (K ⧸ CFSG.pCore 2 K) ∨ IsSmall194 (K ⧸ CFSG.pCore 2 K) ∨
      IsTripleA6 (K ⧸ CFSG.pCore 2 K)) ∧
    ((IsEmpty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
        IsProperParabolic (starIm K N)) ∨
      (Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
        Sec4.IsExtOf (starIm K N) (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2))))

theorem false_of_alternating {X K : Subgroup G} {N : ℕ} (hN : 12 ≤ N)
    (φ : ↥(barM X K) ≃* alternatingGroup (Fin N)) (hp3 : CFSG.Open.pRank 3 X ≤ 3) : False := by
  have h4 := four_le_pRank_alternatingGroup hN
  rw [pRank_top_eq_of_mulEquiv_barM Nat.prime_three φ.symm] at h4
  have := pRank_barM_le (X := X) (K := K) Nat.prime_three (by norm_num)
  omega

@[expose] noncomputable def starImEquiv {X K : Subgroup G} (hKX : K ≤ X)
    (h : K ⊓ CFSG.Open.pCoreOf 2 X = CFSG.Open.pCoreOf 2 K) (Y : Subgroup G) :
    ↥(starIm K Y) ≃* ↥(barM X (Y ⊓ K)) :=
  ((barMEquiv hKX h).subgroupMap (starIm K Y)).trans
    ((MulEquiv.subgroupCongr (map_starIm_barMEquiv hKX h Y)).trans
      (Subgroup.subgroupOfEquivOfLe (barM_inf_le X Y K)))

theorem concl_of_nineThreeSixNat {X S K : Subgroup G} (hK : IsWeakSBlock X S K)
    (hp3 : CFSG.Open.pRank 3 X ≤ 3) (h6 : NineThreeSixNat X S K) :
    Concl194Wide K (Subgroup.normalizer (S : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, n, hn5, ⟨φ⟩, hSO, hSab, hScard, ⟨ψ⟩⟩ := h6
  rcases (show n = 5 ∨ 6 ≤ n by omega) with rfl | hn6
  · have hinf := hK.inf_twoCore
    set e := barMEquiv hK.le hinf with he
    have hA : Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) := ⟨e.trans φ⟩
    refine ⟨Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr hA)))))))))), Or.inr ⟨hA, ?_⟩⟩
    refine isExtOf_of_mulEquiv (starImEquiv hK.le hinf _) ?_
    set Jb := barM X (Subgroup.normalizer (S : Set G) ⊓ K) with hJb
    have hc : ∀ a b : ↥(barM X (S ⊓ K)), a * b = b * a := fun a b => hSab.1.is_comm.comm a b
    have hpw : ∀ a : ↥(barM X (S ⊓ K)), a ^ 2 = 1 := fun a => Subtype.ext (hSab.2 a a.2)
    obtain ⟨f⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hc hpw (n := 4)
      (by rw [hScard])
    refine ⟨CFSG.pCore 2 ↥Jb, inferInstance, ⟨?_⟩, ⟨ψ⟩⟩
    have hO : (CFSG.pCore 2 ↥Jb).map Jb.subtype = barM X (S ⊓ K) := by
      rw [hSO]
      rfl
    exact ((CFSG.pCore 2 ↥Jb).equivMapOfInjective Jb.subtype Jb.subtype_injective).trans
      ((MulEquiv.subgroupCongr hO).trans f)
  · exact (false_of_alternating (N := 2 * n) (by omega) φ hp3).elim

theorem card_pCoreOf_eq {W W' : Type} [Group W] [Group W'] {A : Subgroup W} {B : Subgroup W'}
    (ψ : ↥A ≃* ↥B) : Nat.card (CFSG.Open.pCoreOf 2 A) = Nat.card (CFSG.Open.pCoreOf 2 B) := by
  unfold CFSG.Open.pCoreOf
  rw [Subgroup.card_map_of_injective A.subtype_injective,
    Subgroup.card_map_of_injective B.subtype_injective, ← CFSG.pCore_map_iso 2 ψ,
    Subgroup.card_map_of_injective ψ.injective]

theorem isProperParabolic_map {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] (e : Y ≃* Y')
    {J : Subgroup Y} (hJ : J ≠ ⊤) (T : Sylow 2 Y)
    (hTJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) :
    IsProperParabolic (J.map e.toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun h => hJ ?_, T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  · rw [← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective J, h,
      Subgroup.comap_top]
  · change Subgroup.normalizer (((T : Subgroup Y).map e.toMonoidHom : Subgroup Y') : Set Y') ≤ _
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hTJ

theorem concl_of_nineThreeTwo (h85 : Asc81bEightFive) (hC : KS194ClassicalCensus)
    {X S K : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hhyp : Asc81bHyp X S)
    (hK : IsWeakSBlock X S K) (hL : ∀ L : Subgroup G, ¬ IsScriptLBlock X L)
    (hp : ∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p X ≤ 2)
    (hp3 : CFSG.Open.pRank 3 X ≤ 3) (h2 : NineThreeTwo X S K) :
    Concl194Wide K (Subgroup.normalizer (S : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcl, ⟨hJK, T, hT, hTJ⟩, hO⟩ := h2
  have hinf := hK.inf_twoCore
  set Kb := barM X K with hKb
  set Jb := barM X (Subgroup.normalizer (S : Set G) ⊓ K) with hJb
  set J : Subgroup ↥Kb := Jb.subgroupOf Kb with hJ
  obtain ⟨e, he⟩ : ∃ e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥Kb, e = barMEquiv hK.le hinf := ⟨_, rfl⟩
  have hmap : (starIm K (Subgroup.normalizer (S : Set G))).map e.toMonoidHom = J := by
    rw [he]
    exact map_starIm_barMEquiv hK.le hinf _
  have hq : CFSG.IsQuasisimple ↥Kb := Item194Proof.isQuasisimple_of_open hK.component.2.2
  have hO2 : CFSG.pCore 2 ↥Kb = ⊥ := by
    rw [← CFSG.pCore_map_iso 2 e, CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot',
      Subgroup.map_bot]
  have hrank : ∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p (⊤ : Subgroup ↥Kb) ≤ 2 := by
    intro p hp' hp3'
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (pRank_barM_le hp' (by omega)).trans (hp p hp' hp3')
  have hrank3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Kb) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (pRank_barM_le Nat.prime_three (by norm_num)).trans hp3
  have hT2 : IsPGroup 2 (T.subgroupOf Kb) := hT.2.1.comap_subtype
  set T' : Sylow 2 ↥Kb := IsPGroup.toSylow hT2 hT.2.2 with hT'
  have hT'c : (T' : Subgroup ↥Kb) = T.subgroupOf Kb := IsPGroup.toSylow_coe hT2 hT.2.2
  have hJne : J ≠ ⊤ := by
    intro h
    apply barM_inf_ne hhyp hK
    exact le_antisymm hJK (Subgroup.subgroupOf_eq_top.mp h)
  have hNJ : Subgroup.normalizer ((T' : Subgroup ↥Kb) : Set ↥Kb) ≤ J := by
    intro y hy
    rw [hT'c, ← Subgroup.subgroupOf_normalizer_eq hT.1, Subgroup.mem_subgroupOf] at hy
    rw [hJ, Subgroup.mem_subgroupOf]
    exact hTJ ⟨y.2, hy⟩
  have hcard : Nat.card (CFSG.Open.pCoreOf 2 J) ≠ Nat.card T' := by
    intro heq
    have h1 : Nat.card (CFSG.Open.pCoreOf 2 J) = Nat.card (barM X (S ⊓ K)) := by
      rw [hO]
      exact card_pCoreOf_eq (Subgroup.subgroupOfEquivOfLe hJK)
    have h2 : Nat.card T' = Nat.card T := by
      rw [hT'c]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv
    have hsyl := isSylowTwoOf_inf_of_card hK.toIsTwoPrimeComponent
      (twoCore_le_of_asc81bHyp hhyp) (isPGroup_of_asc81bHyp hhyp) hT (by rw [← h1, heq, h2])
    exact hL K (Item194Proof.isScriptLBlock_of_inClassXBlock hK.le hK.subnormal
      (h85 G X S K hX hhyp hK.toIsTwoPrimeComponent hsyl))
  obtain ⟨hlist, hA10⟩ := hC ↥Kb hq hO2 hcl hrank hrank3 J T' hJne hNJ hcard
  refine ⟨?_, Or.inl ⟨⟨fun f => hA10.false (e.symm.trans f)⟩, ?_⟩⟩
  · rcases hlist with h | h | h
    · exact Or.inl (isList194_of_mulEquiv e h)
    · exact Or.inr (Or.inl (isSmall194_of_mulEquiv e h))
    · exact Or.inr (Or.inr (isTripleA6_of_mulEquiv e h))
  · have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    have hstar : starIm K (Subgroup.normalizer (S : Set G)) = J.map e.symm.toMonoidHom := by
      rw [← hmap, Subgroup.map_map, hid, Subgroup.map_id]
    rw [hstar]
    exact isProperParabolic_map e.symm hJne T' hNJ

end Cases

end Item19Res3Proof

open Item19Res3Proof

theorem asc81bNineThree_of_nat (hN : Asc81bNineThreeNat) : AGLEmbedding.Asc81bNineThree := by
  intro G _ _ X S L hX hhyp hL
  rcases hN G X S L hX hhyp hL with h | h | h | h | h | ⟨hirr, n, hn, ⟨φ⟩, -, -, -, hψ⟩ |
      ⟨hirr, n, hn, hφ, hψ⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h.1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h.1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.1))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hirr, n, ?_, hψ⟩)))))
    have hZ : Subgroup.center ↥(barM X L) = ⊥ := by
      have h4 : 4 ≤ Nat.card (Fin (2 * n)) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        omega
      have hc := Subgroup.map_center_eq φ
      rw [alternatingGroup.center_eq_bot h4] at hc
      exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hc
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans φ⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hirr, n, hφ, hψ⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.1))))))

end CFSG.RankThree.PartTwo.Sec19
