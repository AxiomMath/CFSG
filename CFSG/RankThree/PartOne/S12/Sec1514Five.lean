module

public import CFSG.RankThree.PartOne.S12.Sec1514Defs
public import CFSG.RankThree.PartOne.S12.Sec1514FiveLift
public import CFSG.RankThree.PartOne.U5K.Main
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

@[expose] def KF1514Five : Prop :=
  ∀ (f p : ℕ), 1 ≤ f → p.Prime → 5 ≤ p → p ∣ 2 ^ f + 1 →
    ∀ H Ē Ā : Subgroup (MulAut (projSU 5 2 f)), U5K.U5Inn f ≤ H → Ē ≤ H → Ā ≤ Ē →
      Ē ≤ U5K.U5Inndiag f → IsElementaryAbelian p Ē → Nat.card Ē = p ^ 4 → Nat.card Ā = p ^ 3 →
      (∃ S : Subgroup (MulAut (projSU 5 2 f)), S ≤ H ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
        Ā ≤ Subgroup.normalizer (S : Set (MulAut (projSU 5 2 f)))) →
      ∃ T : Subgroup (MulAut (projSU 5 2 f)), IsSylowOf 2 T H ∧
        Ā ≤ Subgroup.centralizer (omegaOneCenterIn T : Set (MulAut (projSU 5 2 f))) ∧
        ∃ B : Subgroup (MulAut (projSU 5 2 f)), B ≤ Ā ∧ Nat.card B = p ^ 2 ∧
          B ≤ Subgroup.normalizer (pushingUpS T : Set (MulAut (projSU 5 2 f)))

namespace Sec1514Five

section Transport

variable {H H' : Type} [Group H] [Group H']

omit [Group H'] in
theorem omegaOne_le {q : ℕ} {K T : Subgroup H} (h : K ≤ T) : omegaOne q K ≤ T :=
  (Subgroup.closure_le _).2 fun _ hx => h hx.1

theorem map_omegaOne (f : H →* H') {K : Subgroup H} (hf : Set.InjOn f K) (q : ℕ) :
    (omegaOne q K).map f = omegaOne q (K.map f) := by
  unfold omegaOne
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨x, ⟨hxK, hxq⟩, rfl⟩
    exact ⟨⟨x, hxK, rfl⟩, by rw [← map_pow, hxq, map_one]⟩
  · rintro ⟨⟨x, hxK, rfl⟩, hy⟩
    refine ⟨x, ⟨hxK, ?_⟩, rfl⟩
    have h1 : f (x ^ q) = f 1 := by rw [map_pow, hy, map_one]
    exact hf (K.pow_mem hxK q) K.one_mem h1

theorem omegaOneCenterIn_le_zOf (T : Subgroup H) : omegaOneCenterIn T ≤ U5K.zOf T :=
  omegaOne_le le_rfl

theorem omegaOneCenterIn_le (T : Subgroup H) : omegaOneCenterIn T ≤ T :=
  (omegaOneCenterIn_le_zOf T).trans (U5K.zOf_le T)

theorem map_omegaOneCenterIn (f : H →* H') {T : Subgroup H}
    (hf : Function.Injective (f.comp T.subtype)) :
    (omegaOneCenterIn T).map f = omegaOneCenterIn (T.map f) := by
  have hz : Set.InjOn f (U5K.zOf T : Set H) := by
    intro x hx y hy hxy
    have hxT : x ∈ T := U5K.zOf_le T hx
    have hyT : y ∈ T := U5K.zOf_le T hy
    exact congrArg Subtype.val (@hf ⟨x, hxT⟩ ⟨y, hyT⟩ hxy)
  show (omegaOne 2 (U5K.zOf T)).map f = omegaOne 2 (U5K.zOf (T.map f))
  rw [map_omegaOne f hz 2, U5K.map_zOf f hf]

theorem injective_conj_comp (k : H) (T : Subgroup H) :
    Function.Injective ((MulAut.conj k).toMonoidHom.comp T.subtype) := by
  intro a b h
  exact Subtype.ext ((MulAut.conj k).injective h)

end Transport

section Rm

variable {G Â : Type} [Group G] [Finite G] [Group Â] {N : Subgroup G} {ρ : ↥N →* Â}

omit [Finite G] in
theorem rm_omegaOneCenterIn {T : Subgroup G} (hTN : T ≤ N)
    (hinj : ∀ t ∈ T, ∀ ht : t ∈ N, ρ ⟨t, ht⟩ = 1 → t = 1) :
    U5K.rm N ρ (omegaOneCenterIn T) = omegaOneCenterIn (U5K.rm N ρ T) := by
  have hT : (T.subgroupOf N).map N.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTN
  have hinjT := U5K.injective_comp_subtype (ρ := ρ) hinj
  have hinjN : Function.Injective (N.subtype.comp (T.subgroupOf N).subtype) :=
    N.subtype_injective.comp (T.subgroupOf N).subtype_injective
  have h1 : (omegaOneCenterIn (T.subgroupOf N)).map N.subtype = omegaOneCenterIn T := by
    rw [map_omegaOneCenterIn N.subtype hinjN, hT]
  have h2 : (omegaOneCenterIn T).subgroupOf N = omegaOneCenterIn (T.subgroupOf N) := by
    rw [← h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  unfold U5K.rm
  rw [h2, map_omegaOneCenterIn ρ hinjT]

theorem exists_isSylowOf_rm_eq {Tb : Subgroup Â} (hTb : IsSylowOf 2 Tb ρ.range) :
    ∃ T : Subgroup G, IsSylowOf 2 T N ∧ U5K.rm N ρ T = Tb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTbR, hTb2, hTbidx⟩ := hTb
  have hTb2' : IsPGroup 2 (Tb.subgroupOf ρ.range) := hTb2.comap_subtype
  have hidx : ¬ 2 ∣ (Tb.subgroupOf ρ.range).index := hTbidx
  let S : Sylow 2 ↥ρ.range := hTb2'.toSylow hidx
  have hS : (S : Subgroup ↥ρ.range).map ρ.range.subtype = Tb := by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.map_subgroupOf_eq_of_le hTbR
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective ρ.rangeRestrict_surjective 2 S
  refine ⟨(P : Subgroup ↥N).map N.subtype, (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 ⟨P, rfl⟩, ?_⟩
  have hP' : (P : Subgroup ↥N).map ρ.rangeRestrict = (S : Subgroup ↥ρ.range) := by
    have := congrArg (fun Q : Sylow 2 ↥ρ.range => (Q : Subgroup ↥ρ.range)) hP
    simpa using this
  unfold U5K.rm
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective, ← hS, ← hP',
    Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]

end Rm


section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElementaryAbelian_of_le_aux {p : ℕ} {A K : Subgroup G} (hA : IsElementaryAbelian p ↥A)
    (hKA : K ≤ A) : IsElementaryAbelian p ↥K := CFSG.IsElementaryAbelian.of_le hA hKA

theorem isSylowOf_conjSub {N T : Subgroup G} {k : G} (hT : IsSylowOf 2 T N) (hk : k ∈ N) :
    IsSylowOf 2 (StrongP.conjSub k T) N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 T N := CFSG.ABGLocalTools.isSylowOf_iff.2 hT
  refine CFSG.ABGLocalTools.isSylowOf_iff.1 (CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_)
  · rintro _ ⟨t, ht, rfl⟩
    exact N.mul_mem (N.mul_mem hk (hT.1 ht)) (N.inv_mem hk)
  · rw [StrongP.card_conjSub]
    exact hT'.card_eq

theorem node1514Five_of_inputs (h1511 : Node1511) (hEin : U5K.U5EInndiag) (hKF : KF1514Five) :
    Node1514Five := by
  intro G _ _ p A c L E h15 hF hout
  classical
  obtain ⟨f, hf, hpf, ⟨e⟩, -, hcardE, -, -⟩ := id hout
  have h := h15.h12
  have hp := h.prime
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by have := h.three_lt; omega)
    (by have := h.three_lt; omega)
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  let N : Subgroup G := Subgroup.normalizer (lieGenerated p E : Set G)
  let ρ : ↥N →* MulAut (projSU 5 2 f) := U5K.U5Act (lieGenerated p E) e
  have hker := U5K.u5_kernel_facts h15 hF hout h1511 hEin hf e
  have hEN : E ≤ N := U5K.E_le_lieNormalizer h15
  have hAE : A ≤ E := h.A_le_E
  have hAN : A ≤ N := hAE.trans hEN
  have hinjE : ∀ x ∈ E, ∀ hx : x ∈ N, ρ ⟨x, hx⟩ = 1 → x = 1 := fun x hxE hxN hρ =>
    (hEin G p A c L E h15 hF hout f hf e x hxN hxE).2 hρ
  have hinjA : ∀ x ∈ A, ∀ hx : x ∈ N, ρ ⟨x, hx⟩ = 1 → x = 1 := fun x hxA => hinjE x (hAE hxA)
  have hcardA : Nat.card A = p ^ 3 := h.setup.2.2.2.2.2.2.2.1
  have hEel : IsElementaryAbelian p E := h.E_elem
  have hAel : IsElementaryAbelian p A := h.setup.2.2.2.2.2.2.1
  have hEbcard : Nat.card (U5K.rm N ρ E) = p ^ 4 := by
    rw [U5K.card_rm hEN (U5K.injective_comp_subtype hinjE), hcardE]
  have hAbcard : Nat.card (U5K.rm N ρ A) = p ^ 3 := by
    rw [U5K.card_rm hAN (U5K.injective_comp_subtype hinjA), hcardA]
  have hEbel : IsElementaryAbelian p ↥(U5K.rm N ρ E) := U5K.isElementaryAbelian_rm hEel
  have hEbInd : U5K.rm N ρ E ≤ U5K.U5Inndiag f := by
    intro a ha
    obtain ⟨x, hxN, hxE, rfl⟩ := U5K.mem_rm.1 ha
    exact (hEin G p A c L E h15 hF hout f hf e x hxN hxE).1
  obtain ⟨S₀, hS₀ne, hS₀2, hAS₀⟩ := h.setup.2.2.2.2.2.2.2.2.1
  have hS₀N : S₀ ≤ N := by
    have := Sec15Final.normalizer_le_of_forall_maximal (N := lieNormalizer p E) (Z := S₀) (X := A)
      hS₀ne hS₀2 hAS₀ (fun M hM => h1511 G p A c L E h15 hF
        (Or.inr (Or.inr (Or.inr (Or.inr hout)))) A le_rfl (Or.inr ⟨hout, rfl⟩) M hM)
    exact Subgroup.le_normalizer.trans this
  have hinjS₀ : ∀ x ∈ S₀, ∀ hx : x ∈ N, ρ ⟨x, hx⟩ = 1 → x = 1 := fun x hxS hxN hρ =>
    U5K.eq_one_of_isPGroup_two hker.1 hS₀2 hxS hxN hρ
  have hS₀b : ∃ S : Subgroup (MulAut (projSU 5 2 f)), S ≤ ρ.range ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      U5K.rm N ρ A ≤ Subgroup.normalizer (S : Set (MulAut (projSU 5 2 f))) := by
    refine ⟨U5K.rm N ρ S₀, U5K.rm_le_range _, ?_, (hS₀2.comap_subtype).map ρ,
      U5K.rm_le_normalizer hAS₀⟩
    intro hbot
    apply hS₀ne
    rw [eq_bot_iff]
    intro x hx
    have hxN : x ∈ N := hS₀N hx
    have : ρ ⟨x, hxN⟩ ∈ U5K.rm N ρ S₀ := U5K.mem_rm.2 ⟨x, hxN, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (hinjS₀ x hx hxN this)
  obtain ⟨Tb, hTb, hAZb, Bb, hBbA, hBbcard, hBbS⟩ := hKF f p hf hp hp5 hpf ρ.range
    (U5K.rm N ρ E) (U5K.rm N ρ A) (U5K.U5Inn_le_range f (lieGenerated p E) e)
    (U5K.rm_le_range E) (U5K.rm_mono hAE) hEbInd hEbel hEbcard hAbcard hS₀b
  obtain ⟨T, hTsyl, hTbT⟩ := exists_isSylowOf_rm_eq (ρ := ρ) hTb
  have hTN : T ≤ N := hTsyl.1
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have hinjT : ∀ t ∈ T, ∀ ht : t ∈ N, ρ ⟨t, ht⟩ = 1 → t = 1 := fun t htT htN hρ =>
    U5K.eq_one_of_isPGroup_two hker.1 hT2 htT htN hρ
  have hZb : U5K.rm N ρ (omegaOneCenterIn T) = omegaOneCenterIn Tb := by
    rw [← hTbT]; exact rm_omegaOneCenterIn hTN hinjT
  have hSb : U5K.rm N ρ (pushingUpS T) = pushingUpS Tb := by
    rw [← hTbT]; exact (U5K.rm_pushingUpS hTN hinjT).1
  let B : Subgroup G := A ⊓ (Bb.comap ρ).map N.subtype
  have hmemB : ∀ x (hx : x ∈ N), x ∈ B ↔ x ∈ A ∧ ρ ⟨x, hx⟩ ∈ Bb := by
    intro x hx
    constructor
    · rintro ⟨hxA, y, hy, hyx⟩
      have hyx' : y = ⟨x, hx⟩ := Subtype.ext hyx
      rw [hyx'] at hy
      exact ⟨hxA, hy⟩
    · rintro ⟨hxA, hxB⟩
      exact ⟨hxA, ⟨x, hx⟩, hxB, rfl⟩
  have hBA : B ≤ A := inf_le_left
  have hBE : B ≤ E := hBA.trans hAE
  have hBN : B ≤ N := hBE.trans hEN
  have hrmB : U5K.rm N ρ B = Bb := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hxN, hxB, rfl⟩ := U5K.mem_rm.1 hy
      exact ((hmemB x hxN).1 hxB).2
    · intro hy
      obtain ⟨a, haN, haA, ha⟩ := U5K.mem_rm.1 (hBbA hy)
      refine U5K.mem_rm.2 ⟨a, haN, (hmemB a haN).2 ⟨haA, ?_⟩, ha⟩
      rw [ha]
      exact hy
  have hBcard : Nat.card B = p ^ 2 := by
    have hinjB : ∀ x ∈ B, ∀ hx : x ∈ N, ρ ⟨x, hx⟩ = 1 → x = 1 := fun x hxB hxN hρ =>
      hinjA x (hBA hxB) hxN hρ
    rw [← U5K.card_rm hBN (U5K.injective_comp_subtype hinjB), hrmB, hBbcard]
  have hBel : IsElementaryAbelian p ↥B := isElementaryAbelian_of_le_aux hAel hBA
  let K : Subgroup G := ρ.ker.map N.subtype
  have hKN : K ≤ N := Subgroup.map_subtype_le _
  have hmemK : ∀ x (hx : x ∈ N), x ∈ K ↔ ρ ⟨x, hx⟩ = 1 := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = ⟨x, hx⟩ := Subtype.ext hyx
      rw [hyx'] at hy
      exact hy
    · intro h1
      exact ⟨⟨x, hx⟩, h1, rfl⟩
  have hNK : N ≤ Subgroup.normalizer (K : Set G) := by
    intro n hn
    apply Sec1514Five.mem_normalizer_of_forall
    intro x hx
    have hxN : x ∈ N := hKN hx
    have hnxn : n * x * n⁻¹ ∈ N := N.mul_mem (N.mul_mem hn hxN) (N.inv_mem hn)
    rw [hmemK _ hnxn]
    have : (⟨n * x * n⁻¹, hnxn⟩ : ↥N) = ⟨n, hn⟩ * ⟨x, hxN⟩ * ⟨n, hn⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, (hmemK x hxN).1 hx, mul_one, mul_inv_cancel]
  have hKcard : Nat.card K = Nat.card ρ.ker := Subgroup.card_map_of_injective N.subtype_injective
  have hKodd : ¬ 2 ∣ Nat.card K := by rw [hKcard]; exact hker.1
  have hKp : ¬ p ∣ Nat.card K := by rw [hKcard]; exact hker.2
  have hZ : IsPGroup 2 (omegaOneCenterIn T) := hT2.to_le (omegaOneCenterIn_le T)
  have hS : IsPGroup 2 (pushingUpS T) := hT2.to_le (U5K.pushingUpS_le T)
  have hA : IsPGroup p A := IsPGroup.of_card hcardA
  have hZN : omegaOneCenterIn T ≤ N := (omegaOneCenterIn_le T).trans hTN
  have hSN : pushingUpS T ≤ N := (U5K.pushingUpS_le T).trans hTN
  have hZS : ∀ z ∈ omegaOneCenterIn T, ∀ s ∈ pushingUpS T, z * s = s * z := by
    intro z hz s hs
    have hzZ := U5K.mem_zOf_iff.1 (omegaOneCenterIn_le_zOf T hz)
    exact (hzZ.2 s (U5K.pushingUpS_le T hs)).symm
  have hAZ : ∀ a ∈ A, ∀ z ∈ omegaOneCenterIn T, a * z * a⁻¹ * z⁻¹ ∈ K := by
    intro a ha z hz
    have haN : a ∈ N := hAN ha
    have hzN : z ∈ N := hZN hz
    have hwN : a * z * a⁻¹ * z⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem (N.mul_mem haN hzN) (N.inv_mem haN)) (N.inv_mem hzN)
    rw [hmemK _ hwN]
    have hAimg : ρ ⟨a, haN⟩ ∈ U5K.rm N ρ A := U5K.mem_rm.2 ⟨a, haN, ha, rfl⟩
    have hZimg : ρ ⟨z, hzN⟩ ∈ omegaOneCenterIn Tb := by
      rw [← hZb]
      exact U5K.mem_rm.2 ⟨z, hzN, hz, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 (hAZb hAimg) _ hZimg
    have : (⟨a * z * a⁻¹ * z⁻¹, hwN⟩ : ↥N) = ⟨a, haN⟩ * ⟨z, hzN⟩ * ⟨a, haN⟩⁻¹ * ⟨z, hzN⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  have hBS : ∀ b ∈ B, ∀ s ∈ pushingUpS T, ∃ s' ∈ pushingUpS T, b * s * b⁻¹ * s'⁻¹ ∈ K := by
    intro b hb s hs
    have hbN : b ∈ N := hBN hb
    have hsN : s ∈ N := hSN hs
    have hBimg : ρ ⟨b, hbN⟩ ∈ Bb := ((hmemB b hbN).1 hb).2
    have hBimgS := hBbS hBimg
    rw [← hSb] at hBimgS
    have hSimg : ρ ⟨s, hsN⟩ ∈ U5K.rm N ρ (pushingUpS T) := U5K.mem_rm.2 ⟨s, hsN, hs, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.1 hBimgS _).1 hSimg
    have hbsN : b * s * b⁻¹ ∈ N := N.mul_mem (N.mul_mem hbN hsN) (N.inv_mem hbN)
    have hcm : ρ ⟨b * s * b⁻¹, hbsN⟩ = ρ ⟨b, hbN⟩ * ρ ⟨s, hsN⟩ * (ρ ⟨b, hbN⟩)⁻¹ :=
      U5K.map_conj_mk hbN hsN hbsN
    rw [← hcm] at hconj
    obtain ⟨s', hs'N, hs'S, hs'⟩ := U5K.mem_rm.1 hconj
    refine ⟨s', hs'S, ?_⟩
    have hwN : b * s * b⁻¹ * s'⁻¹ ∈ N := N.mul_mem hbsN (N.inv_mem hs'N)
    rw [hmemK _ hwN]
    have : (⟨b * s * b⁻¹ * s'⁻¹, hwN⟩ : ↥N) = ⟨b * s * b⁻¹, hbsN⟩ * ⟨s', hs'N⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, hs', mul_inv_cancel]
  obtain ⟨k, hkK, hkA, hkB⟩ := Sec1514Five.exists_pair_lift hp2 hKN hNK hKodd hKp hZ hS hA hBA
    hZN hSN hAN hZS hAZ hBS
  have hkN : k ∈ N := hKN hkK
  have hinj := injective_conj_comp k T
  have hOmg : omegaOneCenterIn (StrongP.conjSub k T) = StrongP.conjSub k (omegaOneCenterIn T) :=
    (map_omegaOneCenterIn (MulAut.conj k).toMonoidHom hinj).symm
  have hPush : pushingUpS (StrongP.conjSub k T) = StrongP.conjSub k (pushingUpS T) :=
    (U5K.map_pushingUpS (MulAut.conj k).toMonoidHom hinj).symm
  refine ⟨StrongP.conjSub k T, isSylowOf_conjSub hTsyl hkN, ?_, B, hBE, ?_, hBel, hBcard⟩
  · refine le_inf (hAE.trans le_sup_right) ?_
    rw [hOmg]
    exact hkA
  · refine le_inf (hBE.trans le_sup_right) ?_
    rw [hPush]
    exact hkB

end Main

end Sec1514Five

end CFSG.RankThree.PartOne
