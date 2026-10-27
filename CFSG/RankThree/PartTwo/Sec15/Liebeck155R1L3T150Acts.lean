module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150Defs
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Tau

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
open CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90
open scoped commutatorElement

theorem conj_injective_of_center_eq_bot {S : Type*} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro x y h
  have hz : y⁻¹ * x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h' := congrArg (fun φ : MulAut S => φ g) h
    simp only [MulAut.conj_apply] at h'
    calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * x := by group
      _ = y⁻¹ * (x * g * x⁻¹) * x := by rw [h']
      _ = y⁻¹ * x * g := by group
  rw [hZ, Subgroup.mem_bot] at hz
  exact (inv_mul_eq_one.mp hz).symm

theorem mulAut_mul_conj_mul_inv {S : Type*} [Group S] (t : MulAut S) (a : S) :
    t * MulAut.conj a * t⁻¹ = MulAut.conj (t a) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

section Y

variable {Y : Type} [Group Y] [Finite Y]

theorem comm_mem_theta_of_noTwo {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y)
    {L X U : Subgroup Y} (hLperf : Group.IsPerfect L) (hLΛ : L ≤ Λ) (hL1 : L ≠ ⊥) (hLX : L ≤ X)
    (hUX : U ≤ X) (hXU : X ≤ Subgroup.normalizer (U : Set Y)) (hU2 : IsPGroup 2 U)
    (hNP : NoTwoNormalized (((L.subgroupOf Λ).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Λ))).map
        (QuotientGroup.mk' (Subgroup.center (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ)))))
    (hAC : NoTwoCentAut (((L.subgroupOf Λ).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Λ))).map
        (QuotientGroup.mk' (Subgroup.center (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ))))) :
    ∀ u ∈ U, ∀ l ∈ L, u * l * u⁻¹ * l⁻¹ ∈ aschbacherSolvableCore 3 Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θΛ := aschbacherSolvableCore 3 ↥Λ with hθΛ
  set Zc := Subgroup.center (↥Λ ⧸ θΛ) with hZc
  let πS : ↥Λ →* Liebeck155R1T150.Pump.ThetaCenterQuot Λ :=
    (QuotientGroup.mk' Zc).comp (QuotientGroup.mk' θΛ)
  have hπS : Function.Surjective πS :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  set K : Subgroup (Liebeck155R1T150.Pump.ThetaCenterQuot Λ) :=
    ((L.subgroupOf Λ).map (QuotientGroup.mk' θΛ)).map (QuotientGroup.mk' Zc) with hK
  have hKeq : K = (L.subgroupOf Λ).map πS := by
    rw [hK, Subgroup.map_map]
  have hX : CFSG.IsQuasisimple (↥Λ ⧸ θΛ) := hΛ.2.2
  have hSs : IsSimpleGroup (Liebeck155R1T150.Pump.ThetaCenterQuot Λ) := hX.2.1
  have hZS : Subgroup.center (Liebeck155R1T150.Pump.ThetaCenterQuot Λ) = ⊥ := by
    rcases hSs.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hX.2.2
      apply hab
      have ha : a ∈ Subgroup.center (Liebeck155R1T150.Pump.ThetaCenterQuot Λ) :=
        h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  have hconj := conj_injective_of_center_eq_bot hZS
  set N := Subgroup.normalizer (Λ : Set Y) with hN
  have hΛN : Λ ≤ N := Subgroup.le_normalizer
  let ρ := Liebeck155R1T150.Pump.actOnS Λ
  have hinner : ∀ (x : Y) (hx : x ∈ Λ), ρ ⟨x, hΛN hx⟩ = MulAut.conj (πS ⟨x, hx⟩) := by
    intro x hx
    ext t : 1
    obtain ⟨l, rfl⟩ := hπS t
    rw [MulAut.conj_apply]
    have h1 : Λ.normalizerMonoidHom ⟨x, hΛN hx⟩ l = ⟨x, hx⟩ * l * ⟨x, hx⟩⁻¹ := Subtype.ext rfl
    show πS (Λ.normalizerMonoidHom ⟨x, hΛN hx⟩ l) = _
    rw [h1, map_mul, map_mul, map_inv]
  have hUsol : Group.IsSolvable U := by
    have := hU2.isNilpotent
    infer_instance
  have hUN : ∀ u ∈ U, u ∈ N := fun u hu =>
    Liebeck155R1T150.Pump.mem_normalizer_of_mem hΛ hLperf hLΛ hL1 hLX hUX hXU hUsol hu
  have hXUmem : ∀ x ∈ X, ∀ v ∈ U, x * v * x⁻¹ ∈ U := fun x hx v hv =>
    (Subgroup.mem_normalizer_iff.mp (hXU hx) v).mp hv
  set T : Subgroup (MulAut (Liebeck155R1T150.Pump.ThetaCenterQuot Λ)) :=
    (U.subgroupOf N).map ρ with hT
  have hρU : ∀ (u : Y) (hu : u ∈ U), ρ ⟨u, hUN u hu⟩ ∈ T := fun u hu =>
    ⟨⟨u, hUN u hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  have hT2 : ∀ t ∈ T, ∃ m : ℕ, t ^ 2 ^ m = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨m, hm⟩ := hU2 ⟨(v : Y), Subgroup.mem_subgroupOf.mp hv⟩
    refine ⟨m, ?_⟩
    have hv1 : v ^ 2 ^ m = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
    rw [← map_pow, hv1, map_one]
  have hKT : ∀ (l : Y) (hl : l ∈ L), ∀ t ∈ T,
      MulAut.conj (πS ⟨l, hLΛ hl⟩) * t * (MulAut.conj (πS ⟨l, hLΛ hl⟩))⁻¹ ∈ T := by
    rintro l hl _ ⟨v, hv, rfl⟩
    rw [← hinner l (hLΛ hl), ← map_inv, ← map_mul, ← map_mul]
    refine ⟨_, ?_, rfl⟩
    show (((⟨l, hΛN (hLΛ hl)⟩ : ↥N) * v * (⟨l, hΛN (hLΛ hl)⟩ : ↥N)⁻¹ : ↥N) : Y) ∈ U
    exact hXUmem l (hLX hl) _ (Subgroup.mem_subgroupOf.mp hv)
  set W : Subgroup (Liebeck155R1T150.Pump.ThetaCenterQuot Λ) := T.comap MulAut.conj with hW
  have hW2 : IsPGroup 2 W := by
    intro w
    obtain ⟨m, hm⟩ := hT2 _ w.2
    refine ⟨m, Subtype.ext ?_⟩
    have h1 : MulAut.conj ((w : Liebeck155R1T150.Pump.ThetaCenterQuot Λ) ^ 2 ^ m) =
        MulAut.conj 1 := by
      rw [map_pow, map_one]
      exact hm
    simpa using hconj h1
  have hWK : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W := by
    intro k hk w hw
    rw [hKeq] at hk
    obtain ⟨⟨l, hlΛ⟩, hl, rfl⟩ := hk
    have hl' : l ∈ L := Subgroup.mem_subgroupOf.mp hl
    show MulAut.conj (πS ⟨l, hlΛ⟩ * w * (πS ⟨l, hlΛ⟩)⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact hKT l hl' _ hw
  have hW1 : W = ⊥ := hNP W hW2 hWK
  have hTK : ∀ t ∈ T, ∀ k ∈ K, t k = k := by
    intro t ht k hk
    have hk' := hk
    rw [hKeq] at hk'
    obtain ⟨⟨l, hlΛ⟩, hl, rfl⟩ := hk'
    have hl' : l ∈ L := Subgroup.mem_subgroupOf.mp hl
    have h1 : MulAut.conj (πS ⟨l, hlΛ⟩) * t * (MulAut.conj (πS ⟨l, hlΛ⟩))⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem (hKT l hl' t ht) (T.inv_mem ht)
    have h2 : MulAut.conj (πS ⟨l, hlΛ⟩) * t * (MulAut.conj (πS ⟨l, hlΛ⟩))⁻¹ * t⁻¹ =
        MulAut.conj (πS ⟨l, hlΛ⟩ * t (πS ⟨l, hlΛ⟩)⁻¹) := by
      rw [map_mul, ← mulAut_mul_conj_mul_inv, map_inv]
      group
    rw [h2] at h1
    have h3 : πS ⟨l, hlΛ⟩ * t (πS ⟨l, hlΛ⟩)⁻¹ ∈ W := h1
    rw [hW1, Subgroup.mem_bot, map_inv, mul_inv_eq_one] at h3
    exact h3.symm
  intro u hu l hl
  have ht1 : ρ ⟨u, hUN u hu⟩ = 1 :=
    hAC _ (hT2 _ (hρU u hu)) (hTK _ (hρU u hu))
  have hmem : u ∈ Sec4.thetaQuotCentralizer Λ := by
    by_contra hcc
    exact Liebeck155R1T150.Pump.actOnS_ne_one hΛ (hUN u hu) hcc ht1
  exact comm_mem_of_mem_thetaQuotCentralizer hΛ.2.1 hmem (hLΛ hl)

end Y

open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Sylow155R1

theorem res1T150Acts_of_noTwo (h149 : Sec16.Item149S14) {Q : ∀ (X : Type) [Group X], Prop}
    {P : ∀ (Y : Type) [Group Y], Prop}
    (hnoTwo : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
      (L X K Y M T P' : Subgroup G) (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau Q P A c L X K Y M T P' Yc z →
      ∀ j ∈ res1J A X Y M z, j ≠ 1 →
      ∀ Λ : Subgroup ↥(Subgroup.centralizer ({j} : Set G)),
        Λ ∈ thetaComponents 3 ↥(Subgroup.centralizer ({j} : Set G)) →
        A.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤ Subgroup.normalizer (Λ : Set _) →
        ∀ c' : ↥(Subgroup.centralizer ({j} : Set G)), (c' : G) = c →
        L.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤
          Λ ⊓ Subgroup.centralizer ({c'} : Set ↥(Subgroup.centralizer ({j} : Set G))) →
        c' ∉ Sec4.thetaQuotCentralizer Λ →
        NoTwoNormalized ((((L.subgroupOf (Subgroup.centralizer ({j} : Set G))).subgroupOf Λ).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Λ))).map
            (QuotientGroup.mk' (Subgroup.center (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ)))) ∧
        NoTwoCentAut ((((L.subgroupOf (Subgroup.centralizer ({j} : Set G))).subgroupOf Λ).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Λ))).map
            (QuotientGroup.mk' (Subgroup.center (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ))))) :
    Liebeck155R1T150.Res1T150Acts Q P := by
  intro G _ _ A c L X K Y M T P' Yc z τ j hj hj1
  set Yj := Subgroup.centralizer ({j} : Set G) with hYj
  intro Λ hΛ hAΛ c' hc' hLΛ hcc
  obtain ⟨hNP, hAC⟩ := hnoTwo G A c L X K Y M T P' Yc z τ j hj hj1 Λ hΛ hAΛ c' hc' hLΛ hcc
  have hXY : X ≤ Yj := τ.x_le_centralizer_of_mem_j (h149 G A c L τ.std) hj
  have hLX : L ≤ X := τ.l_le
  have hLY : L ≤ Yj := hLX.trans hXY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := CFSG.Open.pCoreOf 2 X with hU
  have hUp : IsPGroup 2 U := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype
  have hUX : U ≤ X := Subgroup.map_subtype_le _
  have hUY : U ≤ Yj := hUX.trans hXY
  have hXU : X ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hUp' : IsPGroup 2 (U.subgroupOf Yj) :=
    hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUY).symm
  have hLX' : L.subgroupOf Yj ≤ X.subgroupOf Yj := fun x hx => hLX hx
  have hUX' : U.subgroupOf Yj ≤ X.subgroupOf Yj := fun x hx => hUX hx
  have hXU' : X.subgroupOf Yj ≤ Subgroup.normalizer ((U.subgroupOf Yj : Subgroup ↥Yj) : Set ↥Yj) :=
    fun x hx => Subgroup.mem_normalizer_iff.mpr fun y =>
      Subgroup.mem_normalizer_iff.mp (hXU hx) (y : G)
  have hLperf : Group.IsPerfect (L.subgroupOf Yj) := by
    have := τ.isPerfect_l
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLY).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLY).symm.surjective
  have hL1 : L.subgroupOf Yj ≠ ⊥ := by
    rw [← Subgroup.nontrivial_iff_ne_bot]
    have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt τ.std.mem_thetaComponentsAt
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have : Nontrivial ↥L := (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L)).nontrivial
    exact (Subgroup.subgroupOfEquivOfLe hLY).symm.injective.nontrivial
  have hP := comm_mem_theta_of_noTwo hΛ hLperf (fun x hx => (Subgroup.mem_inf.mp (hLΛ hx)).1) hL1
    hLX' hUX' hXU' hUp' hNP hAC
  rw [Subgroup.commutator_le]
  intro l hl u hu
  have hlY : l ∈ Yj := hLY hl
  have huY : u ∈ Yj := hUY hu
  have h := hP ⟨u, huY⟩ hu ⟨l, hlY⟩ hl
  refine ⟨(⟨u, huY⟩ * ⟨l, hlY⟩ * ⟨u, huY⟩⁻¹ * ⟨l, hlY⟩⁻¹ : ↥Yj)⁻¹,
    (aschbacherSolvableCore 3 ↥Yj).inv_mem h, ?_⟩
  change (u * l * u⁻¹ * l⁻¹)⁻¹ = ⁅l, u⁆
  rw [commutatorElement_def]
  group

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150
