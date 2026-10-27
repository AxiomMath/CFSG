module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec16.Item16Tail23
import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def KS1623Parab : Prop :=
  ∀ m : ℕ, 1 ≤ m → 2 ^ m % 9 ≠ 1 →
    ∀ b : ↥(projSL 3 (GaloisField 2 m)), orderOf b = 3 →
    ∀ p : ℕ, p.Prime → 3 < p →
    ∀ P : Subgroup ↥(projSL 3 (GaloisField 2 m)),
      P ≤ Subgroup.centralizer ({b} : Set ↥(projSL 3 (GaloisField 2 m))) →
      CFSG.Assembly.IsElemAbelian p P → Nat.card P = p ^ 2 →
      ∃ V X : Subgroup ↥(projSL 3 (GaloisField 2 m)),
        CFSG.Assembly.IsElemAbelian 2 V ∧ Nat.card V = 2 ^ (2 * m) ∧ X ≤ P ∧ Nat.card X = p ∧
        b ∈ inSubgroup perfectResidual
          (Subgroup.normalizer (V : Set ↥(projSL 3 (GaloisField 2 m)))) ∧
        X ≤ inSubgroup perfectResidual
          (Subgroup.normalizer (V : Set ↥(projSL 3 (GaloisField 2 m)))) ∧
        V ≤ inSubgroup perfectResidual
          (Subgroup.normalizer (V : Set ↥(projSL 3 (GaloisField 2 m)))) ∧
        ∃ _ : (V.subgroupOf (inSubgroup perfectResidual
            (Subgroup.normalizer (V : Set ↥(projSL 3 (GaloisField 2 m)))))).Normal,
          Nonempty (↥(inSubgroup perfectResidual
              (Subgroup.normalizer (V : Set ↥(projSL 3 (GaloisField 2 m))))) ⧸
            V.subgroupOf (inSubgroup perfectResidual
              (Subgroup.normalizer (V : Set ↥(projSL 3 (GaloisField 2 m))))) ≃*
            projSL 2 (GaloisField 2 m))

namespace Proof1623Para

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_perfectResidual_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (perfectResidual A).map e.toMonoidHom = perfectResidual B := by
  unfold perfectResidual
  rw [Subgroup.map_iInf _ e.injective]
  congr 1
  ext1 n
  exact map_derivedSeries_eq e.surjective n

omit [Finite G] in
theorem inSubgroup_perfectResidual_map {Y : Type} [Group Y] {ι : Y →* G}
    (hι : Function.Injective ι) (H : Subgroup Y) :
    inSubgroup perfectResidual (H.map ι) = (inSubgroup perfectResidual H).map ι := by
  set e := H.equivMapOfInjective ι hι with he
  unfold inSubgroup
  rw [← map_perfectResidual_of_mulEquiv e, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem inf_normalizer_map_eq {Y : Type} [Group Y] [Finite Y] {ι : Y →* G}
    (hι : Function.Injective ι) {L : Subgroup G} (hL : ι.range = L) (V : Subgroup Y) :
    L ⊓ Subgroup.normalizer ((V.map ι : Subgroup G) : Set G) =
      (Subgroup.normalizer (V : Set Y)).map ι := by
  apply le_antisymm
  · rintro g ⟨hgL, hgN⟩
    rw [← hL] at hgL
    obtain ⟨y, rfl⟩ := hgL
    refine ⟨y, ?_, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    have h1 : ι (y * v * y⁻¹) ∈ V.map ι := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hgN (ι v)).mp ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hwv⟩ := h1
    rw [← hι hwv]
    exact hw
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨hL ▸ ⟨y, rfl⟩, Subgroup.mem_normalizer_fintype fun x hx => ?_⟩
    obtain ⟨v, hv, rfl⟩ := hx
    refine ⟨y * v * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy v).mp hv, ?_⟩
    rw [map_mul, map_mul, map_inv]

omit [Finite G] in
theorem exists_quot_map {Y Q : Type*} [Group Y] [Group Q] {ι : Y →* G}
    (hι : Function.Injective ι) {K V : Subgroup Y} (hn : (V.subgroupOf K).Normal)
    (e : ↥K ⧸ V.subgroupOf K ≃* Q) :
    ∃ _ : ((V.map ι).subgroupOf (K.map ι)).Normal,
      Nonempty (↥(K.map ι) ⧸ (V.map ι).subgroupOf (K.map ι) ≃* Q) := by
  set f := K.equivMapOfInjective ι hι with hf
  have hmap : (V.subgroupOf K).map f.toMonoidHom = (V.map ι).subgroupOf (K.map ι) := by
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨k, hk, hkx⟩
      rw [Subgroup.mem_subgroupOf]
      have hkx' : ι k = x := congrArg Subtype.val hkx
      change x ∈ V.map ι
      rw [← hkx']
      exact ⟨k, Subgroup.mem_subgroupOf.mp hk, rfl⟩
    · intro hxV
      rw [Subgroup.mem_subgroupOf] at hxV
      obtain ⟨k, hkK, hkx⟩ := hx
      obtain ⟨v, hv, hvx⟩ := hxV
      have hkv : k = v := hι (hkx.trans hvx.symm)
      refine ⟨⟨k, hkK⟩, Subgroup.mem_subgroupOf.mpr (hkv ▸ hv), ?_⟩
      exact Subtype.ext hkx
  have hn' : ((V.map ι).subgroupOf (K.map ι)).Normal := by
    rw [← hmap]
    exact hn.map f.toMonoidHom f.surjective
  refine ⟨hn', ⟨(QuotientGroup.congr _ _ f hmap).symm.trans e⟩⟩

end Proof1623Para

open Proof1623Para

theorem para1623_of (h138 : Item138N) (hK : KS1623Parab) : Para1623 := by
  intro G _ _ A c L h b n p P hD m hm hφ
  obtain ⟨φ⟩ := hφ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := ↥(projSL 3 (GaloisField 2 m)) with hYdef
  have : Finite Y := Finite.of_equiv _ φ.toEquiv
  have hLs : IsSimpleGroup ↥L := by
    have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 m)
    exact φ.isSimpleGroup
  have hθ := Proof1623.theta_eq_bot_of_isSimpleGroup
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt)
  have eL : ↥L ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hθ.symm)
  have h9 : 2 ^ m % 9 ≠ 1 := by
    intro h91
    have h31 : 2 ^ m % 3 = 1 := by omega
    have hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m :=
      Or.inl ⟨h31, ⟨eL.symm.trans φ⟩⟩
    exact Sec15.not_modNine_of_inner h.toSec15R h138 KFacts.kSL3PiOrder3TypeC hm hiso
      hD.isZ3.2.2 (Or.inl h91)
  have hbL : b ∈ L := hD.mem_L
  have hb1 : b ≠ 1 := fun h1 => hD.not_mem (h1 ▸ Subgroup.one_mem _)
  have hb3 : orderOf b = 3 :=
    orderOf_eq_prime (h.isElemAbelian.2 b hD.mem_A) hb1
  set bY : Y := φ ⟨b, hbL⟩ with hbY
  have hbY3 : orderOf bY = 3 := by
    rw [hbY, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hb3]
  have hPL : P ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := hD.mem_Q.1.2
  set PY : Subgroup Y := (P.subgroupOf L).map φ.toMonoidHom with hPY
  have hPYC : PY ≤ Subgroup.centralizer ({bY} : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change φ x * φ ⟨b, hbL⟩ = φ ⟨b, hbL⟩ * φ x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (hPL (Subgroup.mem_subgroupOf.mp hx)).2)
  have hPYel : CFSG.Assembly.IsElemAbelian p PY := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩
      apply Subtype.ext
      change φ x * φ y = φ y * φ x
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (show (x : G) * y = y * x from congrArg Subtype.val
        (hD.elem.1.is_comm.comm ⟨x, Subgroup.mem_subgroupOf.mp hx⟩
          ⟨y, Subgroup.mem_subgroupOf.mp hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ p = 1 := Subtype.ext (by
        simpa using hD.elem.2 _ (Subgroup.mem_subgroupOf.mp hx))
      rw [this, map_one]
  have hPLe : P ≤ L := fun x hx => (hPL hx).1
  have hPYc : Nat.card PY = p ^ 2 := by
    rw [hPY, Subgroup.card_map_of_injective φ.injective, ← hD.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPLe).toEquiv
  obtain ⟨V₀, X₀, hV₀el, hV₀c, hX₀P, hX₀c, hbK, hXK, hVK, hquot⟩ :=
    hK m hm h9 bY hbY3 p hD.prime hD.three_lt PY hPYC hPYel hPYc
  set ι : Y →* G := L.subtype.comp φ.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := L.subtype_injective.comp φ.symm.injective
  have hιrange : ι.range = L := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      exact (φ.symm y).2
    · intro x hx
      exact ⟨φ ⟨x, hx⟩, by simp [hι]⟩
  set K₀ := inSubgroup perfectResidual (Subgroup.normalizer (V₀ : Set Y)) with hK₀
  have hKeq : kPara1623 L (V₀.map ι) = K₀.map ι := by
    rw [kPara1623, inf_normalizer_map_eq hιinj hιrange V₀, inSubgroup_perfectResidual_map hιinj]
  have hιb : ι bY = b := by simp [hι, hbY]
  have hιP : PY.map ι = P := by
    rw [hPY, Subgroup.map_map]
    have : ι.comp φ.toMonoidHom = L.subtype := by
      ext x
      simp [hι]
    rw [this, Subgroup.map_subgroupOf_eq_of_le hPLe]
  refine ⟨V₀.map ι, X₀.map ι, ?_⟩
  obtain ⟨hn₀, ⟨e₀⟩⟩ := hquot
  obtain ⟨hn, ⟨e⟩⟩ := exists_quot_map hιinj hn₀ e₀
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hιrange]
    exact Subgroup.map_le_range ι V₀
  · exact ⟨⟨⟨fun x y => Subtype.ext (by
      obtain ⟨_, ⟨x', hx', rfl⟩⟩ := x
      obtain ⟨_, ⟨y', hy', rfl⟩⟩ := y
      change ι x' * ι y' = ι y' * ι x'
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hV₀el.1.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩))⟩⟩,
      by
        rintro _ ⟨x, hx, rfl⟩
        rw [← map_pow, hV₀el.2 x hx, map_one]⟩
  · rw [Subgroup.card_map_of_injective hιinj, hV₀c]
  · rw [← hιP]
    exact Subgroup.map_mono hX₀P
  · rw [Subgroup.card_map_of_injective hιinj, hX₀c]
  · rw [hKeq, ← hιb]
    exact ⟨bY, hbK, rfl⟩
  · rw [hKeq]
    exact Subgroup.map_mono hXK
  · rw [hKeq]
    exact Subgroup.map_mono hVK
  · rw [hKeq]
    exact ⟨hn, ⟨e⟩⟩

end CFSG.RankThree.PartTwo.Sec16
