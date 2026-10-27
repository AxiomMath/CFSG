module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Mod
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofJ2
import CFSG.RankThree.PartTwo.Sec14.Ronan148DTwoON
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofWE
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ronan152SL25

theorem card_map_of_isPGroup_three {H Q : Type*} [Group H] [Group Q] [Finite H] (π : H →* Q)
    (hker : IsPGroup 2 π.ker) {K : Subgroup H} (hK : IsPGroup 3 K) :
    Nat.card (K.map π) = Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdisj : Disjoint K π.ker := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hker
    exact Subgroup.disjoint_of_coprime_natCard (by
      rw [hk, hm]
      exact Nat.Coprime.pow k m (by norm_num))
  have hinj : Function.Injective (π.comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : (k : H) ∈ K ⊓ π.ker := ⟨k.2, hk⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hk'
    exact Subtype.ext hk'
  have e : K.map π = (π.comp K.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [e]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

section Config

theorem eq_bot_of_le_normalizer_of_j2 {Lx R E : Subgroup G}
    (hJ : Nonempty (↥Lx ⧸ CFSG.pCore 2 ↥Lx ≃* CFSG.Blueprint.NativeSporadic.J2))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hR : IsPGroup p R) (hRL : R ≤ Lx)
    (hE : IsPGroup 3 E) (hEL : E ≤ Lx) (hE9 : Nat.card E = 9)
    (hER : E ≤ Subgroup.normalizer (R : Set G)) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set N := CFSG.pCore 2 ↥Lx with hN
  set π := QuotientGroup.mk' N with hπ
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hEb9 : Nat.card ((E.subgroupOf Lx).map π) = 9 := by
    rw [card_map_of_isPGroup_three π hker (K := E.subgroupOf Lx) hE.comap_subtype,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE9]
  have hRbp : IsPGroup p ((R.subgroupOf Lx).map π) := hR.comap_subtype.map π
  have hEbN : (E.subgroupOf Lx).map π ≤
      Subgroup.normalizer (((R.subgroupOf Lx).map π : Subgroup (↥Lx ⧸ N)) : Set (↥Lx ⧸ N)) := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨r, hr, rfl⟩ := hz
    refine ⟨x * r * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp only [map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hER (Subgroup.mem_subgroupOf.mp hx)) r).mp
      (Subgroup.mem_subgroupOf.mp hr)
  have hRb := Sec17.Proof17Res3.j2_eq_bot_of_le_normalizer Sec4.Sporadic.rank3II_4_15 hJ hEb9 hp
    hp3 hRbp hEbN
  rw [eq_bot_iff]
  intro r hr
  have hrL : r ∈ Lx := hRL hr
  have h1 : π ⟨r, hrL⟩ ∈ (R.subgroupOf Lx).map π :=
    ⟨⟨r, hrL⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  rw [hRb, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 N) ⟨⟨r, hrL⟩, h1⟩
  have hk' : r ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hm' : r ^ 2 ^ m = 1 := by
    have h2 := congrArg (fun z : ↥N => ((z : ↥Lx) : G)) hm
    simpa using h2
  have hcop : Nat.Coprime (p ^ k) (2 ^ m) :=
    Nat.Coprime.pow k m ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  have h3 : orderOf r = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk') hcop)
      (orderOf_dvd_of_pow_eq_one hm')
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp h3

theorem inf_centralizer_le_centralizer_of_j2 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {x : G} (hxΩ : Subgroup.zpowers x ∈ omegaA A) {Lx : Subgroup G} (hLx : Lx ∈ lA A x)
    (hJ : Nonempty (↥Lx ⧸ CFSG.pCore 2 ↥Lx ≃* CFSG.Blueprint.NativeSporadic.J2))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {P : Subgroup G} (hP : IsPGroup p P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) :
    P ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer (A : Set G) := by
  obtain ⟨eJ⟩ := hJ
  have hJθ :
      Nonempty (↥Lx ⧸ aschbacherSolvableCore 3 ↥Lx ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq (theta_eq_pCore_two_of_j2 eJ)).trans eJ⟩
  have h' : Sec14Std G A x Lx := { h with zpowers_mem_omegaA := hxΩ, mem_lA := hLx }
  have hCN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (Lx : Set G) :=
    centralizer_le_normalizer_of_j2 h' hJθ
  obtain ⟨-, hAL9, hAeq⟩ := j2_point_facts h'.toSec13Data hJθ
  have hxA : x ∈ A := (zpowers_mem_omegaA_iff.mp hxΩ).1
  have hAC : A ≤ Subgroup.centralizer ({x} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute hy hxA)
  set Px := P ⊓ Subgroup.centralizer ({x} : Set G) with hPx
  have hPxN : Px ≤ Subgroup.normalizer (Lx : Set G) := inf_le_right.trans hCN
  have hAPx : A ≤ Subgroup.normalizer (Px : Set G) :=
    Late.le_normalizer_inf hAP (hAC.trans Subgroup.le_normalizer)
  have hbot : Px ⊓ Lx = ⊥ :=
    eq_bot_of_le_normalizer_of_j2 ⟨eJ⟩ hp hp3 (hP.to_le (inf_le_left.trans inf_le_left))
      inf_le_right (h.isE27'.isPGroup.to_le inf_le_left) inf_le_right hAL9
      (inf_le_left.trans (Late.le_normalizer_inf hAPx (hAC.trans hCN)))
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hA' : A ≤ Subgroup.centralizer ({w} : Set G) := by
    rw [hAeq]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hw.2).symm
    · intro y hy
      have hcomm := commute_of_inf_eq_bot hPxN hy.2 (hAPx hy.1) hbot hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm.symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hA' ha)

theorem inf_centralizer_le_frattini_of_j2 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {x : G} (hxΩ : Subgroup.zpowers x ∈ omegaA A) {Lx : Subgroup G} (hLx : Lx ∈ lA A x)
    (hJ : Nonempty (↥Lx ⧸ CFSG.pCore 2 ↥Lx ≃* CFSG.Blueprint.NativeSporadic.J2))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {P : Subgroup G} (hP : IsPGroup p P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) {b : G} (hbA : b ∈ A)
    (hfr : P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype) :
    P ⊓ Subgroup.centralizer ({x} : Set G) ≤ (frattini ↥P).map P.subtype := by
  intro w hw
  have hwA := inf_centralizer_le_centralizer_of_j2 h hxΩ hLx hJ hp hp3 hP hAP hw
  exact hfr ⟨hw.1, Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp hwA) b hbA).symm⟩

theorem false_of_omegaA_ncard_twelve (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G}
    {c : G} (h : Sec14Std G A c L) {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B)
    (hc : IsLBConfig A B b d Lb) {e : G} (heB : e ∈ B) (heb : e ∉ Subgroup.zpowers b)
    (heΩ : Subgroup.zpowers e ∉ omegaA A)
    (hII : ∀ (D : Subgroup G) (b' d' : G) (L' : Subgroup G), IsHyperplane A D → e ∈ D →
      IsLBConfig A D b' d' L' → Subgroup.zpowers e = Subgroup.zpowers d')
    (h12 : (omegaA A).ncard = 12) {X : Subgroup G} {p : ℕ} {P : Subgroup G}
    (hP : PData152 A X p P) (hp3 : 3 < p)
    (hfr : P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype)
    (hPe : P ≤ Subgroup.centralizer ({e} : Set G)) : False := by
  have hA := h.isE27'
  have hp : p.Prime := hP.prime
  have : Fact p.Prime := ⟨hp⟩
  have hPp : IsPGroup p P := by
    rcases hP.type_p with ⟨-, h2⟩ | ⟨-, h3⟩
    · exact IsPGroup.of_card h2
    · exact IsPGroup.of_card h3
  have heA : e ∈ A := hB.1 heB
  have he1 : e ≠ 1 := fun h1 => heb (h1 ▸ Subgroup.one_mem _)
  have hda : Subgroup.zpowers e = Subgroup.zpowers d := hII B b d Lb hB heB hc
  obtain ⟨-, -, -, -, hbA, hb1, hdA, -, -, -⟩ := lbConfig_facts hA hB hc
  have hbB : b ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b _)
  have heB' : e ∈ Subgroup.closure ({b, d} : Set G) := hc.1 ▸ heB
  have he3 := Proof152WE.card_zpowers_eq_three hA heA he1
  have hB9 : Nat.card B = 9 := by
    have h2 := hB.2
    rw [hA.2] at h2
    omega
  have hlt : B < A := by
    refine lt_of_le_of_ne hB.1 fun hBA => ?_
    rw [hBA, hA.2] at hB9
    norm_num at hB9
  obtain ⟨y, hyA, hyB⟩ := SetLike.exists_of_lt hlt
  have hy1 : y ≠ 1 := fun h1 => hyB (h1 ▸ B.one_mem)
  have hyb : y ∉ Subgroup.zpowers b := fun hyb => hyB (Subgroup.zpowers_le.mpr hbB hyb)
  set E := Subgroup.closure ({b, y} : Set G) with hE
  have hEA : E ≤ A := by
    rw [hE, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hbA
    · exact hyA
  have hE9 : Nat.card E = 9 := by
    have h1 := Proof152WE.card_closure_pair hA hbA hyA
    rw [Proof152WE.zpowers_inf_eq_bot (Proof152WE.card_zpowers_eq_three hA hyA hy1) hyb,
      Subgroup.card_bot, mul_one, Proof152WE.card_zpowers_eq_three hA hbA hb1,
      Proof152WE.card_zpowers_eq_three hA hyA hy1] at h1
    exact h1
  have heE : e ∉ E := by
    intro heE
    have hBE : B ≤ E := by
      rw [hc.1, ← Proof152WE.closure_eq_of_mem hA hbA hdA hb1 heB' heb, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact heE
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
    have hBE' : B = E := Subgroup.eq_of_le_of_card_ge hBE (by rw [hB9, hE9])
    exact hyB (hBE' ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hEcomm : ∀ x y : ↥E, x * y = y * x := fun x y => Subtype.ext (by
    have h1 := congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hEA x.2⟩ ⟨y, hEA y.2⟩)
    simpa using h1)
  have hEab : CFSG.Open.IsElemAbelian 3 E := ⟨⟨⟨hEcomm⟩⟩, fun x hx => hA.1.2 x (hEA hx)⟩
  have hPcop : Nat.Coprime 3 (Nat.card P) := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three E P hEab (by rw [hE9]; norm_num) (hEA.trans hP.norm_p) hPcop
  have hF : ∀ F ∈ CFSG.Open.signalizerFunctorEk 3 1 E,
      P ⊓ Subgroup.centralizer (F : Set G) ≤ (frattini ↥P).map P.subtype := by
    rintro F ⟨hFE, hF3⟩
    obtain ⟨x, hxF, hx1⟩ : ∃ x ∈ F, x ≠ 1 := by
      by_contra hno
      push Not at hno
      have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).mpr hno
      rw [hbot, Subgroup.card_bot, pow_one] at hF3
      exact absurd hF3 (by norm_num)
    have hxA : x ∈ A := hEA (hFE hxF)
    have hx3 := Proof152WE.card_zpowers_eq_three hA hxA hx1
    have hxe : x ∉ Subgroup.zpowers e := by
      intro hxe
      have hzeq : Subgroup.zpowers x = Subgroup.zpowers e :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxe) (by rw [hx3, he3])
      have hex : e ∈ Subgroup.zpowers x := by
        rw [hzeq]
        exact Subgroup.mem_zpowers e
      exact heE (hFE (Subgroup.zpowers_le.mpr hxF hex))
    have hex : e ∉ Subgroup.zpowers x := by
      intro hex
      have hzeq : Subgroup.zpowers e = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hex) (by rw [hx3, he3])
      have hxe' : x ∈ Subgroup.zpowers e := by
        rw [hzeq]
        exact Subgroup.mem_zpowers x
      exact hxe hxe'
    set D := Subgroup.closure ({x, e} : Set G) with hDdef
    have hDA : D ≤ A := by
      rw [hDdef, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact hxA
      · exact heA
    have hD9 : Nat.card D = 9 := by
      have h1 := Proof152WE.card_closure_pair hA hxA heA
      rw [Proof152WE.zpowers_inf_eq_bot he3 hex, Subgroup.card_bot, mul_one, hx3, he3] at h1
      exact h1
    have hD : IsHyperplane A D := ⟨hDA, by rw [hA.2, hD9]⟩
    have heD : e ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    obtain ⟨b', d', L', hc'⟩ :=
      Ronan148D.exists_isLBConfig_of_twelve h134 h48 h heA he1 heΩ hB heB hc hda h12 hD heD
    obtain ⟨hb'Ω, hL', -, -, -, -, -, -, -, -⟩ := lbConfig_facts hA hD hc'
    have hb'D : b' ∈ D := hc'.1 ▸ Subgroup.subset_closure (Set.mem_insert b' _)
    have hfr' := inf_centralizer_le_frattini_of_j2 h hb'Ω hL' hc'.2.2.2.1 hp hp3 hPp hP.norm_p
      hbA hfr
    intro w hw
    refine hfr' ⟨hw.1, ?_⟩
    have hDw : D ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [hDdef, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hw.2) _ hxF)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hPe hw.1)).symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hDw hb'D)).symm
  refine Proof152WE.false_of_le_frattini hP ?_
  have hle := iSup₂_le hF
  rw [hgen] at hle
  exact hle

end Config

theorem exists_isLBConfig_of_mem_orbit {A B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B)
    (hc : IsLBConfig A B b d Lb) {W : Subgroup G} (hW : W ≤ Subgroup.normalizer (A : Set G))
    {e : G} (he : Subgroup.zpowers e ∈ orbitIn W (Subgroup.zpowers b)) :
    ∃ (D : Subgroup G) (x d' : G) (L' : Subgroup G), IsHyperplane A D ∧
      Subgroup.zpowers x = Subgroup.zpowers e ∧ IsLBConfig A D x d' L' := by
  obtain ⟨w, hwW, hwe⟩ := he
  have hw := hW hwW
  refine ⟨B.map (MulAut.conj w).toMonoidHom, MulAut.conj w b, MulAut.conj w d,
    Lb.map (MulAut.conj w).toMonoidHom, hB.map_conj hw, ?_, ?_⟩
  · rw [hwe, MonoidHom.map_zpowers]
    rfl
  · have h1 := hc.map (MulAut.conj w)
    rwa [map_conj_eq_of_mem_normalizer' hw] at h1

end Ronan152SL25

@[expose] noncomputable def Step152SL25PureTwoA6R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A →
    ∀ M X : Subgroup G, Ctx152J A (lB A) M X →
    ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → IsLBConfig A B b d Lb →
      Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G) →
    ∀ (p : ℕ) (P : Subgroup G), PData152 A X p P → 3 < p →
      P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype →
    ∀ e ∈ B, e ∉ Subgroup.zpowers b → Subgroup.zpowers e ∉ omegaA A →
      P ≤ Subgroup.centralizer ({e} : Set G) →
      (∀ (D : Subgroup G) (b' d' : G) (L' : Subgroup G), IsHyperplane A D → e ∈ D →
        IsLBConfig A D b' d' L' → Subgroup.zpowers e = Subgroup.zpowers d') →
      (∀ K ∈ thetaComponentsAt 3 e, lB A B ≤ K →
        K = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) K →
        P ≤ Subgroup.normalizer (K : Set G) →
        ¬ P ⊓ Subgroup.centralizer ((A ⊓ Lb : Subgroup G) : Set G) ≤
          (frattini ↥P).map P.subtype) →
      (omegaA A).ncard ≠ 12 → False

theorem step152SL25PureTwoR_of_a6
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (hA6 : Step152SL25PureTwoA6R) : Step152SL25PureTwoR := by
  intro G _ _ A c L h hHJ M X hctx B b d Lb hB hc hcent p P hP hp3 hfr e heB heb heΩ hPe hII hK
  by_cases h12 : (omegaA A).ncard = 12
  · exact Ronan152SL25.false_of_omegaA_ncard_twelve h134 h48 h.toSec14Std hB hc heB heb heΩ hII
      h12 hP hp3 hfr hPe
  · exact hA6 G A c L h hHJ M X hctx B b d Lb hB hc hcent p P hP hp3 hfr e heB heb heΩ hPe hII hK
      h12

@[expose] noncomputable def Step152SL25EOmegaSixR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A →
    ∀ M X : Subgroup G, Ctx152J A (lB A) M X →
    ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → IsLBConfig A B b d Lb →
      Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G) →
    ∀ (p : ℕ) (P : Subgroup G), PData152 A X p P → 3 < p →
      P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype →
    ∀ e ∈ B, e ∉ Subgroup.zpowers b → Subgroup.zpowers e ∈ omegaA A →
      P ≤ Subgroup.centralizer ({e} : Set G) →
      (∀ (D : Subgroup G) (x d' : G) (L' : Subgroup G), IsHyperplane A D →
        Subgroup.zpowers x = Subgroup.zpowers e → ¬ IsLBConfig A D x d' L') →
      (omegaA A).ncard = 6 → False

theorem step152SL25EOmegaNCR_of_six
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (hsix : Step152SL25EOmegaSixR) : Step152SL25EOmegaNCR := by
  intro G _ _ A c L h hHJ M X hctx B b d Lb hB hc hcent p P hP hp3 hfr e heB heb heΩ hPe hnc
  have hS := h.toSec14Std
  have hA := h.isE27
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨-, hLb, -, -, -, -, hdA, hd1, -, hdb⟩ := Ronan152SL25.lbConfig_facts hA hB hc
  have hdB : d ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨K, hK, hDK⟩ := Desc143X.exists_mem_le_residual h48 hS hB hc hdB hd1 hdb
  have hJ := Item148HJ.j2_of_isLBConfig hc
  have hdata : Sec13Data G A b Lb :=
    { hS.toSec13Data with zpowers_mem_omegaA := hc.2.1, mem_lA := hLb }
  obtain ⟨hdL, S, hdS, hSd⟩ := hc.2.2.2.2
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hSz := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  have hfalse : ∀ W : Subgroup G, W ≤ Subgroup.normalizer (A : Set G) →
      Subgroup.zpowers e ∈ orbitIn W (Subgroup.zpowers b) → False := by
    intro W hW he
    obtain ⟨D, x, d', L', hD, hxe, hc'⟩ := Ronan152SL25.exists_isLBConfig_of_mem_orbit hB hc hW he
    exact hnc D x d' L' hD hxe hc'
  have key := h134 G A b Lb hdata hJ d hdA hd1 ⟨_, hSz⟩ K hK hDK
  rcases key with ⟨-, -, hΩ1⟩ | ⟨-, -, -, -, -, -, hΩ⟩ | ⟨-, -, hΩN, -⟩
  ·
    rw [hΩ1, Set.mem_singleton_iff] at heΩ
    exact heb (heΩ ▸ Subgroup.mem_zpowers e)
  · rcases hΩ with ⟨hΩP, -⟩ | ⟨-, -, -, -, -, -, -, -, h6, -⟩
    ·
      rw [hΩP] at heΩ
      exact hfalse _ (Subgroup.map_subtype_le _) heΩ
    ·
      exact hsix G A c L h hHJ M X hctx B b d Lb hB hc hcent p P hP hp3 hfr e heB heb heΩ hPe
        hnc h6
  ·
    rw [hΩN] at heΩ
    exact hfalse _ le_rfl heΩ

theorem y4CoreExclSL25HJR_of_narrow
    (h142 : Item142AllS14)
    (h425 : Sec4.Item4_25Fix) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h41 : Sec4.Item4_1LargePrime) (hGW : Sec6.GWLBalanceStatement)
    (hmod : Step152SL25ModR) (hA6 : Step152SL25PureTwoA6R) (hsix : Step152SL25EOmegaSixR) :
    Y4CoreExclSL25HJR :=
  y4CoreExclSL25HJR_of_mod h142 h425 h134 h48 h41 hGW hmod (step152SL25PureTwoR_of_a6 h134 h48 hA6)
    (step152SL25EOmegaNCR_of_six h134 h48 hsix)

end CFSG.RankThree.PartTwo.Sec15
