module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofExcl
public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof432Use
import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Late.Item2010
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

namespace Res5

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_one (S : Subgroup G) : S.map (MulAut.conj (1 : G)).toMonoidHom = S := by
  ext x
  simp

omit [Finite G] in
theorem map_conj_map_conj (S : Subgroup G) (a b : G) :
    (S.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      S.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev,
    mul_assoc]

theorem map_conj_eq_of_le {P : Subgroup G} {c : G} (hP : IsSylowOf 3 P ⊤)
    (hconj : Sec18.conjugatesIn (Subgroup.zpowers c) P = {Subgroup.zpowers c})
    {R : Subgroup G} (hR : IsPGroup 3 R) (hcR : c ∈ R) {g : G}
    (hgR : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤ R) :
    (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P', hP', hRP'⟩ := Sec20.exists_isSylowOf_le hR (le_top : R ≤ ⊤)
  obtain ⟨h, -, rfl⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hP hP'
  have key : ∀ k : G, (Subgroup.zpowers c).map (MulAut.conj k).toMonoidHom ≤
      P.map (MulAut.conj h).toMonoidHom →
      (Subgroup.zpowers c).map (MulAut.conj (h⁻¹ * k)).toMonoidHom = Subgroup.zpowers c := by
    intro k hk
    have hmem : (Subgroup.zpowers c).map (MulAut.conj (h⁻¹ * k)).toMonoidHom ∈
        Sec18.conjugatesIn (Subgroup.zpowers c) P := by
      refine ⟨⟨h⁻¹ * k, rfl⟩, ?_⟩
      rw [← map_conj_map_conj]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨p, hp, hpy⟩ := hk hy
      rw [← hpy]
      simpa [MulAut.conj_apply, mul_assoc] using hp
    rw [hconj] at hmem
    exact hmem
  have h1 : (Subgroup.zpowers c).map (MulAut.conj (h⁻¹ * 1)).toMonoidHom =
      Subgroup.zpowers c := by
    refine key 1 ?_
    rw [map_conj_one]
    exact (Subgroup.zpowers_le.mpr hcR).trans hRP'
  have h2 := key g (hgR.trans hRP')
  have hh : (Subgroup.zpowers c).map (MulAut.conj h).toMonoidHom = Subgroup.zpowers c := by
    calc (Subgroup.zpowers c).map (MulAut.conj h).toMonoidHom
        = ((Subgroup.zpowers c).map (MulAut.conj (h⁻¹ * 1)).toMonoidHom).map
            (MulAut.conj h).toMonoidHom := by rw [h1]
      _ = Subgroup.zpowers c := by
          rw [map_conj_map_conj, mul_one, mul_inv_cancel, map_conj_one]
  calc (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom
      = ((Subgroup.zpowers c).map (MulAut.conj (h⁻¹ * g)).toMonoidHom).map
          (MulAut.conj h).toMonoidHom := by rw [map_conj_map_conj, mul_inv_cancel_left]
    _ = Subgroup.zpowers c := by rw [h2, hh]

theorem weaklyClosed_of_conjugatesIn {P : Subgroup G} {c : G} (hP : IsSylowOf 3 P ⊤)
    (hc : orderOf c = 3)
    (hconj : Sec18.conjugatesIn (Subgroup.zpowers c) P = {Subgroup.zpowers c}) :
    ∀ g : G, (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c := by
  intro g hg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have hZg : IsPGroup 3 ((Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom) := hZ.map _
  exact map_conj_eq_of_le hP hconj (IsPGroup.to_sup_of_normal_left' hZ hZg hg)
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) le_sup_right

theorem false_of_comm {P : Subgroup G} {c : G} (hP : IsSylowOf 3 P ⊤) (hc : orderOf c = 3)
    (hconj : Sec18.conjugatesIn (Subgroup.zpowers c) P = {Subgroup.zpowers c})
    (hfr : c ∉ (frattini (Sec18.omegaOneThree P)).map (Sec18.omegaOneThree P).subtype)
    {x y : G} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : ⁅x, y⁆ ∈ Subgroup.zpowers c)
    (hxy1 : ⁅x, y⁆ ≠ 1) (hp : IsPGroup 3 (Subgroup.closure ({x, y} : Set G))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := Subgroup.closure ({x, y} : Set G) with hR
  have hxR : x ∈ R := Subgroup.subset_closure (by simp)
  have hyR : y ∈ R := Subgroup.subset_closure (by simp)
  have hcomR : ⁅x, y⁆ ∈ R := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxR hyR) (inv_mem hxR)) (inv_mem hyR)
  have h3 : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc]
  have hceq : Subgroup.zpowers c = Subgroup.zpowers ⁅x, y⁆ :=
    Sec17.Proof176Steps.eq_zpowers_of_card_three h3 hxy hxy1
  have hcR : c ∈ R := (Subgroup.zpowers_le.mpr hcomR) (hceq ▸ Subgroup.mem_zpowers c)
  obtain ⟨P', hP', hRP'⟩ := Sec20.exists_isSylowOf_le hp (le_top : R ≤ ⊤)
  obtain ⟨h, -, rfl⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hP hP'
  have hmem : ∀ z ∈ R, h⁻¹ * z * h ∈ P := by
    intro z hz
    obtain ⟨p, hp, hpz⟩ := hRP' hz
    rw [← hpz]
    simpa [MulAut.conj_apply, mul_assoc] using hp
  have hch : (Subgroup.zpowers c).map (MulAut.conj h⁻¹).toMonoidHom = Subgroup.zpowers c := by
    have hmem' : (Subgroup.zpowers c).map (MulAut.conj h⁻¹).toMonoidHom ∈
        Sec18.conjugatesIn (Subgroup.zpowers c) P := by
      refine ⟨⟨h⁻¹, rfl⟩, ?_⟩
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      have := hmem c hcR
      simpa [MulAut.conj_apply] using this
    rw [hconj] at hmem'
    exact hmem'
  set x' := h⁻¹ * x * h with hx'
  set y' := h⁻¹ * y * h with hy'
  have hx'P : x' ∈ P := hmem x hxR
  have hy'P : y' ∈ P := hmem y hyR
  have hx'3 : x' ^ 3 = 1 := by
    rw [hx', show h⁻¹ * x * h = h⁻¹ * x * h⁻¹⁻¹ by rw [inv_inv], conj_pow, hx3, mul_one,
      mul_inv_cancel]
  have hy'3 : y' ^ 3 = 1 := by
    rw [hy', show h⁻¹ * y * h = h⁻¹ * y * h⁻¹⁻¹ by rw [inv_inv], conj_pow, hy3, mul_one,
      mul_inv_cancel]
  have hcom' : ⁅x', y'⁆ = h⁻¹ * ⁅x, y⁆ * h := by
    rw [hx', hy', commutatorElement_def, commutatorElement_def]
    group
  have hcom'Z : ⁅x', y'⁆ ∈ Subgroup.zpowers c := by
    rw [hcom', ← hch]
    refine ⟨⁅x, y⁆, hxy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hcom'1 : ⁅x', y'⁆ ≠ 1 := by
    rw [hcom']
    intro h1
    apply hxy1
    have : ⁅x, y⁆ = h * (h⁻¹ * ⁅x, y⁆ * h) * h⁻¹ := by group
    rw [this, h1]
    group
  set Ω := Sec18.omegaOneThree P with hΩ
  have hx'Ω : x' ∈ Ω := Subgroup.subset_closure ⟨hx'P, hx'3⟩
  have hy'Ω : y' ∈ Ω := Subgroup.subset_closure ⟨hy'P, hy'3⟩
  have hΩP : Ω ≤ P := (Subgroup.closure_le P).mpr fun z hz => hz.1
  have hΩ3 : IsPGroup 3 Ω := hP.isPGroup.to_le hΩP
  have hfrat : ⁅(⟨x', hx'Ω⟩ : ↥Ω), ⟨y', hy'Ω⟩⁆ ∈ frattini ↥Ω :=
    OrderReductions.FrattiniElementary.commutator_le_frattini 3 hΩ3
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hcom'F : ⁅x', y'⁆ ∈ (frattini ↥Ω).map Ω.subtype := ⟨_, hfrat, rfl⟩
  have hceq' : Subgroup.zpowers c = Subgroup.zpowers ⁅x', y'⁆ :=
    Sec17.Proof176Steps.eq_zpowers_of_card_three h3 hcom'Z hcom'1
  exact hfr ((Subgroup.zpowers_le.mpr hcom'F) (hceq' ▸ Subgroup.mem_zpowers c))

theorem pRank_normalClosureIn_le_one
    (h432 : Sec4.Item4_32Comp) (h41 : Sec4.Item4_1LargePrime) (hG2 : Sec17.KS176GTwo)
    (hG : TheoremFourHyp G) {X : Subgroup G} (hX : X ≠ ⊤) {c : G} (hc : orderOf c = 3)
    (hcX : c ∈ X)
    (hweak : ∀ g : G, (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c)
    (hcomm : ∀ x y : G, x ^ 3 = 1 → y ^ 3 = 1 → ⁅x, y⁆ ∈ Subgroup.zpowers c → ⁅x, y⁆ ≠ 1 →
      IsPGroup 3 (Subgroup.closure ({x, y} : Set G)) → False) :
    CFSG.Open.pRank 3 (normalClosureIn X c) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pPrimeCore 3 ↥X with hN
  set Zt := (Subgroup.zpowers (⟨c, hcX⟩ : ↥X)).map (QuotientGroup.mk' N) with hZt
  set H := Subgroup.normalClosure (Zt : Set (↥X ⧸ N)) with hH
  have hZ3 : Nat.card Zt = 3 := Sec17.Proof176.card_map_zpowers hc hcX
  have hwc := Sec17.Proof176.weaklyClosed_quot hc hweak hcX
  have hZH : Zt ≤ H := Subgroup.subset_normalClosure
  have hZ3' : Nat.card (Zt.subgroupOf H) = 3 := by
    rw [Sec17.Proof176Steps.card_subgroupOf_eq hZH, hZ3]
  have hwc' := Sec17.Proof176Steps.weaklyClosed_subgroupOf hZH hwc
  have key : Sec17.Proof176Steps.HasCommOfZ (Zt.subgroupOf H) → False := fun hh => by
    obtain ⟨x, y, hx3, hy3, -, -, hxy, hxy1, hp⟩ :=
      Sec17.Proof176Steps.exists_lift_of_hasComm hc hcX
        (Sec17.Proof176Steps.hasCommOfZ_of_subgroupOf hZH hh)
    exact hcomm x y hx3 hy3 hxy hxy1 hp
  have hcomp : ∀ K : Subgroup (↥X ⧸ N), IsComponent K → SectionFourHyp K := fun _ hK =>
    Sec4.Item432Proof.sectionFourHyp_component_quot_pPrimeCore h41 (hG.sectionFourHyp hX) hK
  rcases h432 (↥X ⧸ N) hcomp (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3) Zt hZ3 hwc with
    h1 | h2 | h3
  · exact (Sec17.Proof176.pRank_le_quot hcX).trans h1.le
  · exact (key (hG2 _ h2 _ hZ3' hwc')).elim
  · exact (key (Sec17.Proof176Steps.hasCommOfZ_of_j2 h3 hZ3' hwc')).elim

omit [Finite G] in
theorem kTwenty_one (M : Subgroup G) : kTwenty M (1 : G) = ⊥ := by
  rw [eq_bot_iff, kTwenty, normalClosureIn, Subgroup.closure_le]
  rintro _ ⟨m, -, rfl⟩
  simp

theorem orderOf_eq_three {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hKN : ¬ kTwenty M c ≤ N) : orderOf c = 3 := by
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hc3 : c ^ 3 = 1 := hT.mem_partTwoE.1.2 c hcA
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hKN ((kTwenty_one M).symm ▸ bot_le)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime hc3 hc1

end Res5

theorem step204Cyclic_of
    (h432 : Sec4.Item4_32Comp)
    (h41 : Sec4.Item4_1LargePrime) (hG2 : Sec17.KS176GTwo) : Step204Cyclic := by
  intro G _ _ A M L N c T i j P hset X hX hXM
  have hT := hset.toCtx20
  have : IsSimpleGroup G := hT.isSimpleGroup
  have hc : orderOf c = 3 := Res5.orderOf_eq_three hT hset.not_le
  have hXtop : X ≠ ⊤ := by
    obtain ⟨⟨Q, hQ1, hQ2, hXQ⟩, -⟩ := hX.1
    rw [hXQ]
    exact normalizer_ne_top_of_isPGroup_two hT.nonabelian hQ2 hQ1
  have hcX : c ∈ X := hX.2 (Subgroup.mem_sup_left (self_mem_normalClosureIn M c))
  exact Res5.pRank_normalClosureIn_le_one h432 h41 hG2 hT.toTheoremFourHyp hXtop hc hcX
    (Res5.weaklyClosed_of_conjugatesIn hset.sylow_top hc hset.conjugatesIn_eq)
    (fun x y hx3 hy3 hxy hxy1 hp => Res5.false_of_comm hset.sylow_top hc hset.conjugatesIn_eq
      hset.not_mem_frattini hx3 hy3 hxy hxy1 hp)

end CFSG.RankThree.PartTwo.Sec20
