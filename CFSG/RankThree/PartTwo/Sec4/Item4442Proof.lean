module

public import CFSG.RankThree.PartTwo.Sec4.T444.Part1Main
public import CFSG.RankThree.PartTwo.KFacts.L34CenterProof
import CFSG.RankThree.PartTwo.Sec4.Item447Proof
import CFSG.RankThree.PartTwo.KFacts.KS44Transport
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

namespace Item4442

section General

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mem_sup_of_isPGroup {p : ℕ} [hp : Fact p.Prime] {A L : Subgroup G}
    (hA : IsPGroup p A) (hAL : A ≤ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ A ⊔ L)
    (hxp : ¬ p ∣ orderOf x) : x ∈ L := by
  set W := A ⊔ L with hW
  have hWL : W ≤ Subgroup.normalizer (L : Set G) := sup_le hAL Subgroup.le_normalizer
  have : (L.subgroupOf W).Normal := ⟨fun y hy w => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hWL w.2) _).mp hy⟩
  have hmul : ((A ⊔ L : Subgroup G) : Set G) = (A : Set G) * (L : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A L hAL
  have hsurj : Function.Surjective ((QuotientGroup.mk' (L.subgroupOf W)).comp
      (Subgroup.inclusion (le_sup_left : A ≤ W))) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      have hw : (w : G) ∈ (A : Set G) * (L : Set G) := hmul ▸ w.2
      obtain ⟨a, ha, l, hl, hal⟩ := hw
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      change a⁻¹ * (w : G) ∈ L
      rw [← hal, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hl
  have hpq : IsPGroup p (W ⧸ L.subgroupOf W) := hA.of_surjective _ hsurj
  obtain ⟨k, hk⟩ := hpq (QuotientGroup.mk' (L.subgroupOf W) ⟨x, hx⟩)
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
  have hxL : x ^ p ^ k ∈ L := by simpa [Subgroup.mem_subgroupOf] using hk
  have hcop : (p ^ k).Coprime (orderOf x) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hxp)
  exact mem_of_pow_mem_of_coprime hcop hxL

theorem isPGroup_two_of_forall_odd {P : Subgroup G}
    (h : ∀ z ∈ P, Odd (orderOf z) → z = 1) : IsPGroup 2 P := by
  intro y
  obtain ⟨k, m, hm, hy⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hyo : orderOf (y : G) = 2 ^ k * m := by rw [Subgroup.orderOf_coe]; exact hy
  have hzo : orderOf ((y : G) ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero) ⟨m, hyo⟩, hyo]
    exact Nat.mul_div_cancel_left m (pow_pos two_pos k)
  have hz : (y : G) ^ 2 ^ k = 1 := h _ (P.pow_mem y.2 _) (by rw [hzo]; exact hm)
  exact ⟨k, Subtype.ext (by simpa using hz)⟩

omit [Finite G] in
theorem eq_one_of_mem_of_isPGroup_two {T : Subgroup G} (hT : IsPGroup 2 T) {z : G}
    (hz : z ∈ T) (hodd : Odd (orderOf z)) : z = 1 := by
  obtain ⟨j, hj⟩ := hT ⟨z, hz⟩
  have hzj : z ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have h1 : orderOf z ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hzj
  have hcop : Nat.Coprime (2 ^ j) (orderOf z) :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 dvd_rfl)

omit [Finite G] in
theorem mem_normalizer_sup {H K : Subgroup G} {x : G}
    (hH : x ∈ Subgroup.normalizer (H : Set G)) (hK : x ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem mem_thetaComponents_of_mem_oTwoComponents {K : Subgroup G}
    (hK : K ∈ oTwoComponents G) : K ∈ thetaComponents 3 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hK.1, hK.2.1, Sec14.isQuasisimple_quotient_theta_of_surjective hK.2.2
    (QuotientGroup.mk' (CFSG.pCore 2 K)) (QuotientGroup.mk'_surjective _) ?_ ?_⟩
  · rw [QuotientGroup.ker_mk']
    exact isSolvable_of_isPGroup CFSG.pCore_isPGroup
  · rw [QuotientGroup.ker_mk']
    exact not_three_dvd_card_of_isPGroup_two CFSG.pCore_isPGroup

omit [Finite G] in
theorem mem_oTwoComponents_of_mem_oTwoComponentsIn_top {K : Subgroup G}
    (hK : K ∈ oTwoComponentsIn (⊤ : Subgroup G)) : K ∈ oTwoComponents G := by
  obtain ⟨K', ⟨hperf, hsn, hq⟩, rfl⟩ := hK
  set e := K'.equivMapOfInjective (⊤ : Subgroup G).subtype (Subgroup.subtype_injective _)
  refine ⟨?_, hsn.map (f := (⊤ : Subgroup G).subtype) fun g => ⟨⟨g, trivial⟩, rfl⟩, ?_⟩
  · have := hperf
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · exact isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)) hq

theorem inSubgroup_perfectResidual_top_normal :
    (inSubgroup perfectResidual (⊤ : Subgroup G)).Normal := by
  have : (perfectResidual (⊤ : Subgroup G)).Characteristic :=
    (perfect_residual_characterization (G := (⊤ : Subgroup G))).2.1
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (H := (⊤ : Subgroup G)) (perfectResidual (⊤ : Subgroup G))
  rw [Subgroup.normalizer_eq_top (⊤ : Subgroup G)] at h
  exact h

theorem le_inSubgroup_perfectResidual_top {L : Subgroup G} (hL : Group.IsPerfect L) :
    L ≤ inSubgroup perfectResidual (⊤ : Subgroup G) := by
  have hL' : Group.IsPerfect (L.subgroupOf ⊤) := Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe (le_top : L ≤ ⊤)).symm.toMonoidHom)
    (MulEquiv.surjective _)
  have hle : L.subgroupOf ⊤ ≤ perfectResidual (⊤ : Subgroup G) :=
    (perfect_residual_transport (MonoidHom.id (⊤ : Subgroup G))).2.2 _ hL'
  intro x hx
  exact ⟨⟨x, trivial⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end General

section Model

variable {W : Type} [Group W] [Finite W]

theorem exists_mem_conj_eq_of_isZ3L34OrHeisSL34 (hW : IsZ3L34OrHeisSL34 W) {N : Subgroup W}
    [N.Normal] [Group.IsPerfect N] (hs : Group.IsSolvable (W ⧸ N)) (w : W) :
    ∃ n ∈ N, ∀ x ∈ N, w * x * w⁻¹ = n * x * n⁻¹ := by
  rcases hW with he | ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, -⟩
  ·
    obtain ⟨e⟩ := he
    set P := projSL 3 (GaloisField 2 2)
    have : Group.IsPerfect P := isPerfect_projSL
    set Pw : Subgroup W := ((MonoidHom.inr (Multiplicative (ZMod 3)) P).range).comap
      e.toMonoidHom with hPw
    have hPwe : Pw.map e.toMonoidHom = (MonoidHom.inr (Multiplicative (ZMod 3)) P).range :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective _
    set ePw : Pw ≃* P := (Pw.equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hPwe).trans
        ((MonoidHom.inr (Multiplicative (ZMod 3)) P).ofInjective
          (fun a b h => congrArg Prod.snd h)).symm) with hePw
    have : Group.IsPerfect Pw :=
      Group.IsPerfect.ofSurjective (f := ePw.symm.toMonoidHom) ePw.symm.surjective
    have hPwN : Pw ≤ N := le_of_isPerfect_of_isSolvable_quotient hs
    set n : W := e.symm (1, (e w).2) with hn
    set c : W := e.symm ((e w).1, 1) with hc
    have hwcn : w = c * n := e.injective (by
      rw [map_mul, hc, hn, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact Prod.ext (by simp) (by simp))
    have hcen : ∀ y : W, c * y = y * c := fun y => e.injective (by
      rw [map_mul, map_mul, hc, MulEquiv.apply_symm_apply]
      exact Prod.ext (by simp [mul_comm]) (by simp))
    have hnN : n ∈ N := hPwN ⟨(e w).2, by
      change (1, (e w).2) = e n
      rw [hn, MulEquiv.apply_symm_apply]⟩
    refine ⟨n, hnN, fun x _ => ?_⟩
    rw [hwcn]
    calc c * n * x * (c * n)⁻¹ = c * (n * x * n⁻¹) * c⁻¹ := by group
      _ = n * x * n⁻¹ := by rw [hcen, mul_inv_cancel_right]
  ·
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    have : Group.IsPerfect V :=
      Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
    have hVN : V ≤ N := le_of_isPerfect_of_isSolvable_quotient hs
    have hkey : ∀ u ∈ U, ∀ x ∈ V, u * x * u⁻¹ = x := fun u hu x hx => by
      rw [hcomm u hu x hx, mul_inv_cancel_right]
    have hVn : V.Normal := by
      refine ⟨fun v hv w => ?_⟩
      obtain ⟨u, hu, v', hv', rfl⟩ := KFacts.L34.exists_mul_eq_of_sup_eq_top hUV hcomm w
      have hx : v' * v * v'⁻¹ ∈ V := V.mul_mem (V.mul_mem hv' hv) (V.inv_mem hv')
      have h1 : u * v' * v * (u * v')⁻¹ = u * (v' * v * v'⁻¹) * u⁻¹ := by group
      rw [h1, hkey u hu _ hx]
      exact hx
    have hUp : IsPGroup 3 U := IsPGroup.of_card (n := 3) hU.2.1
    have hsV : Group.IsSolvable (W ⧸ V) := by
      have : Group.IsNilpotent U := hUp.isNilpotent
      refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' V).comp U.subtype) ?_
      intro q
      induction q using QuotientGroup.induction_on with
      | H w =>
        obtain ⟨u, hu, v, hv, rfl⟩ := KFacts.L34.exists_mul_eq_of_sup_eq_top hUV hcomm w
        refine ⟨⟨u, hu⟩, ?_⟩
        rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        change u⁻¹ * (u * v) ∈ V
        rwa [inv_mul_cancel_left]
    have hNV : N ≤ V := le_of_isPerfect_of_isSolvable_quotient hsV
    obtain ⟨u, hu, v, hv, rfl⟩ := KFacts.L34.exists_mul_eq_of_sup_eq_top hUV hcomm w
    refine ⟨v, hVN hv, fun x hx => ?_⟩
    have hx' : v * x * v⁻¹ ∈ V := V.mul_mem (V.mul_mem hv (hNV hx)) (V.inv_mem hv)
    calc u * v * x * (u * v)⁻¹ = u * (v * x * v⁻¹) * u⁻¹ := by group
      _ = v * x * v⁻¹ := hkey u hu _ hx'

end Model

section Star

variable {G : Type} [Group G] [Finite G]

theorem not_mem_map_starQuot_of_inducesOuterTheta {A L : Subgroup G} (hA : IsPGroup 3 A)
    (hL : L ∈ thetaComponents 3 G) (h3 : 3 ∣ Nat.card L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hZ : IsZ3L34OrHeisSL34 ((A ⊔ L).map (starQuot G))) {s : G} (hs : InducesOuterTheta s L) :
    starQuot G s ∉ (A ⊔ L).map (starQuot G) := by
  intro hsW
  obtain ⟨hsN, hout⟩ := hs
  set π := starQuot G with hπ
  set W := (A ⊔ L).map π with hW
  set Ls := L.map π with hLs
  have hLW : Ls ≤ W := Subgroup.map_mono le_sup_right
  set N := Ls.subgroupOf W with hN
  have hWL : A ⊔ L ≤ Subgroup.normalizer (L : Set G) := sup_le hAL Subgroup.le_normalizer
  have hNn : N.Normal := by
    refine ⟨fun x hx w => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨y, hy, hyw⟩ := w.2
    have hyn : π y ∈ Subgroup.normalizer (Ls : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
      Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π (hWL hy))
    change (w : G ⧸ CFSG.pPrimeCore 3 G) * x * (w : G ⧸ CFSG.pPrimeCore 3 G)⁻¹ ∈ Ls
    rw [← hyw]
    exact (Subgroup.mem_normalizer_iff.mp hyn _).mp hx
  have : Group.IsPerfect L := hL.1
  have : Group.IsPerfect Ls := Group.IsPerfect.map π
  have : Group.IsPerfect N := Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe hLW).symm.toMonoidHom) (MulEquiv.surjective _)
  have hsWN : Group.IsSolvable (W ⧸ N) := by
    have : Group.IsNilpotent A := hA.isNilpotent
    set ι : A →* W := (π.comp A.subtype).codRestrict W
      (fun a => Subgroup.mem_map_of_mem π (le_sup_left (b := L) a.2)) with hι
    refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' N).comp ι) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      obtain ⟨x, hx, hxw⟩ := w.2
      have hx' : x ∈ (A : Set G) * (L : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right A L hAL]
        exact hx
      obtain ⟨a, ha, l, hl, rfl⟩ := hx'
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      change (π a)⁻¹ * (w : G ⧸ CFSG.pPrimeCore 3 G) ∈ Ls
      rw [← hxw, map_mul, inv_mul_cancel_left]
      exact Subgroup.mem_map_of_mem π hl
  obtain ⟨n, hnN, hconj⟩ := exists_mem_conj_eq_of_isZ3L34OrHeisSL34 hZ hsWN ⟨π s, hsW⟩
  obtain ⟨l₀, hl₀, hl₀n⟩ : (n : G ⧸ CFSG.pPrimeCore 3 G) ∈ Ls := Subgroup.mem_subgroupOf.mp hnN
  have key : ∀ l ∈ L, π (s * l * s⁻¹) = π (l₀ * l * l₀⁻¹) := by
    intro l hl
    have hx : (⟨π l, hLW (Subgroup.mem_map_of_mem π hl)⟩ : W) ∈ N :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem π hl)
    have h1 := congrArg Subtype.val (hconj _ hx)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hl₀n]
    exact h1
  have hθL := inf_pPrimeCore_eq_of_mem_thetaComponents hL h3
  apply hout
  refine ⟨((⟨l₀, hl₀⟩ : L) : L ⧸ aschbacherSolvableCore 3 L), ?_⟩
  ext q
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [MulAut.conj_apply, thetaQuotMulAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq]
    set y : L := ((⟨l₀, hl₀⟩ : L) * l * (⟨l₀, hl₀⟩ : L)⁻¹)⁻¹ * compAction L ⟨s, hsN⟩ l with hy
    have hc : ((compAction L ⟨s, hsN⟩ l : L) : G) = s * l * s⁻¹ :=
      normalizerMonoidHom_apply_coe hsN l
    have hyG : (y : G) = (l₀ * l * l₀⁻¹)⁻¹ * (s * l * s⁻¹) := by
      rw [hy, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hc]
    have hyP : (y : G) ∈ CFSG.pPrimeCore 3 G := by
      rw [← QuotientGroup.eq_one_iff]
      change π (y : G) = 1
      rw [hyG, map_mul, map_inv, key l l.2, inv_mul_cancel]
    have hmem : (y : G) ∈ L ⊓ CFSG.pPrimeCore 3 G := ⟨y.2, hyP⟩
    rw [hθL] at hmem
    obtain ⟨t, ht, hte⟩ := hmem
    rwa [← Subtype.ext hte]

theorem isPGroup_two_pPrimeCore_of_sup_eq_top {A R L : Subgroup G} (htop : A ⊔ R ⊔ L = ⊤)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hLP : IsPGroup 2 (L ⊓ CFSG.pPrimeCore 3 G : Subgroup G)) :
    IsPGroup 2 (CFSG.pPrimeCore 3 G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isPGroup_two_of_forall_odd fun z hz hodd => ?_
  have hz3 : ¬ 3 ∣ orderOf z := not_three_dvd_orderOf_of_mem hz not_three_dvd_card_pPrimeCore
  have hzRL : z ∈ R ⊔ L :=
    mem_sup_of_not_three_dvd hA hAR hAL (by rw [htop]; exact Subgroup.mem_top z) hz3
  have hz2 : ¬ 2 ∣ orderOf z := by
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  have hzL : z ∈ L := mem_of_mem_sup_of_isPGroup hR hRL hzRL hz2
  exact eq_one_of_mem_of_isPGroup_two hLP ⟨hzL, hz⟩ hodd

theorem mem_aschbacherSolvableCore_iff_of_eq_top {H : Subgroup G} (hH : H = ⊤)
    (hP2 : IsPGroup 2 (CFSG.pPrimeCore 3 G)) (x : H) :
    x ∈ aschbacherSolvableCore 3 H ↔ (x : G) ∈ CFSG.pPrimeCore 3 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hθc, hθ3, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  constructor
  · intro hx
    set Θ : Subgroup G := (aschbacherSolvableCore 3 H).map H.subtype with hΘ
    have hΘn : Θ.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hH]
      exact Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
    have hΘ3 : ¬ 3 ∣ Nat.card Θ := by
      rw [hΘ, Subgroup.card_map_of_injective H.subtype_injective]
      exact hθ3
    exact le_pPrimeCore_of_normal hΘn hΘ3 ⟨x, hx, rfl⟩
  · intro hx
    have hn : ((CFSG.pPrimeCore 3 G).subgroupOf H).Normal := Subgroup.normal_subgroupOf
    have h2 : IsPGroup 2 ((CFSG.pPrimeCore 3 G).subgroupOf H) :=
      hP2.comap_of_injective H.subtype H.subtype_injective
    exact hθmax _ hn (isSolvable_of_isPGroup h2) (not_three_dvd_card_of_isPGroup_two h2)
      (Subgroup.mem_subgroupOf.mpr hx)

theorem concl434_consequences
    (h434 : Item4_34Sec)
    {A M : Subgroup G} (h : Ctx444 G A M) {L R : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hLM : ¬ L ≤ M)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hR3 : ¬ 3 ∣ Nat.card R)
    (hs : Group.IsSolvable (A ⊔ R : Subgroup G))
    (hact : ¬ R.map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))) :
    (∃ x : ↥(A ⊔ R ⊔ L), (x : G) ∈ R ∧ x ∉ aschbacherSolvableCore 3 ↥(A ⊔ R ⊔ L)) ∧
    (∀ x y : ↥(A ⊔ R ⊔ L), (x : G) ∈ R → (y : G) ∈ R →
      x ∉ aschbacherSolvableCore 3 ↥(A ⊔ R ⊔ L) → y ∉ aschbacherSolvableCore 3 ↥(A ⊔ R ⊔ L) →
      x⁻¹ * y ∈ aschbacherSolvableCore 3 ↥(A ⊔ R ⊔ L)) ∧
    (∀ x : ↥(A ⊔ R ⊔ L), (x : G) ∈ R → x ∉ aschbacherSolvableCore 3 ↥(A ⊔ R ⊔ L) →
      KFacts.InducesStdKind L (x : G) .graphField) := by
  set H := A ⊔ R ⊔ L with hH
  set f := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hf
  have hcore := ctx434Core_quotient h hL hLM hAL hRL hAR hR3 hs hact
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    rw [hf, QuotientGroup.ker_mk']
    exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  obtain ⟨-, h2, hgf⟩ :=
    h434 G h.sectionFourHyp H _ f (QuotientGroup.mk'_surjective _) hker _ _ _ hcore
  obtain ⟨q, hq1, huniq⟩ := (Nat.card_eq_two_iff' (1 : (R.subgroupOf H).map f)).mp h2
  have hmemR : ∀ x : H, (x : G) ∈ R → f x ∈ (R.subgroupOf H).map f := fun x hx =>
    Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hx)
  have hne : ∀ x : H, x ∉ aschbacherSolvableCore 3 H → f x ≠ 1 := fun x hx h1 =>
    hx ((QuotientGroup.eq_one_iff _).mp h1)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, hxq⟩ := q.2
    refine ⟨x, Subgroup.mem_subgroupOf.mp hx, fun hxθ => hq1 (Subtype.ext ?_)⟩
    rw [← hxq]
    exact (QuotientGroup.eq_one_iff _).mpr hxθ
  · intro x y hx hy hxθ hyθ
    have hxq : (⟨f x, hmemR x hx⟩ : (R.subgroupOf H).map f) = q :=
      huniq _ fun h1 => hne x hxθ (congrArg Subtype.val h1)
    have hyq : (⟨f y, hmemR y hy⟩ : (R.subgroupOf H).map f) = q :=
      huniq _ fun h1 => hne y hyθ (congrArg Subtype.val h1)
    have hxy : (x : H ⧸ aschbacherSolvableCore 3 H) = y :=
      congrArg Subtype.val (hxq.trans hyq.symm)
    exact QuotientGroup.eq.mp hxy
  · intro x hx hxθ
    have hLH : L ≤ H := le_sup_right
    have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_sup_le hAL hRL
    have hLn : (L.subgroupOf H).Normal := ⟨fun y hy k => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hHL k.2) _).mp hy⟩
    have hL' := mem_thetaComponents_subgroupOf_of_le_normalizer hL hLH hHL
    have hlayer := layer_quotient_eq_map hL' (isSolvable_quotient_subgroupOf hAL hRL hs)
    have hk := hgf (f x) (hmemR x hx) (hne x hxθ)
    rw [hlayer] at hk
    have hθcond : ∀ l : L.subgroupOf H, f.subgroupMap (L.subgroupOf H) l ∈
        aschbacherSolvableCore 3 ((L.subgroupOf H).map f) ↔
        l ∈ aschbacherSolvableCore 3 (L.subgroupOf H) := by
      intro l
      have hsn : ((L.subgroupOf H).map f).IsSubnormal :=
        (hLn.map f (QuotientGroup.mk'_surjective _)).isSubnormal
      rw [aschbacherSolvableCore_eq_subgroupOf Nat.prime_three hsn,
        (theta_quotient_core_and_ranks (G := H)).1, Subgroup.bot_subgroupOf, Subgroup.mem_bot,
        aschbacherSolvableCore_eq_subgroupOf Nat.prime_three hLn.isSubnormal,
        Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
      · intro h1
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h1)
    have hxN : x ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup H) : Set H) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top x
    have hk0 := KFacts.InducesStdKind.of_map f (L.subgroupOf H) hθcond hxN hk
    have hk1 := KFacts.InducesStdKind.map H.subtype (L.subgroupOf H)
      (KFacts.thetaQuotMap_iff_of_injective H.subtype H.subtype_injective _) hk0
    rwa [Subgroup.map_subgroupOf_eq_of_le hLH] at hk1

theorem not_map_pCoreOf_le_centralizer {A M : Subgroup G} (h : Ctx444 G A M)
    (hG : ⊤ ∈ Late.scriptH₀ A M) {L : Subgroup G}
    (htop : A ⊔ CFSG.Open.pCoreOf 2 M ⊔ L = ⊤) (hP2 : IsPGroup 2 (CFSG.pPrimeCore 3 G)) :
    ¬ (CFSG.Open.pCoreOf 2 M).map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hle
  have hsurj : Function.Surjective (starQuot G) := QuotientGroup.mk'_surjective _
  have hRn : ((CFSG.Open.pCoreOf 2 M).map (starQuot G)).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff,
      ← Subgroup.map_top_of_surjective (starQuot G) hsurj, ← htop,
      Subgroup.map_sup (A ⊔ CFSG.Open.pCoreOf 2 M) L,
      Subgroup.map_sup A (CFSG.Open.pCoreOf 2 M)]
    refine sup_le (sup_le ?_ Subgroup.le_normalizer) ?_
    · exact (Subgroup.map_mono
        (h.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))).trans
        (Subgroup.le_normalizer_map _)
    · exact (Subgroup.le_centralizer_iff.mp hle).trans (Subgroup.centralizer_le_normalizer _)
  have hR3 : ¬ 3 ∣ Nat.card ((CFSG.Open.pCoreOf 2 M).map (starQuot G)) :=
    not_three_dvd_card_of_isPGroup_two ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).map _)
  have hRP : CFSG.Open.pCoreOf 2 M ≤ CFSG.pPrimeCore 3 G := by
    have h1 := le_pPrimeCore_of_normal hRn hR3
    rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3, le_bot_iff, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk'] at h1
    exact h1
  apply hG.2.2
  rw [top_inf_eq]
  apply le_antisymm
  ·
    have hn : (⊤ : Subgroup G) ≤ Subgroup.normalizer
        (CFSG.Open.pCoreOf 2 (⊤ : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤
    have h2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup G)
    have hnormal : (CFSG.Open.pCoreOf 2 (⊤ : Subgroup G)).Normal :=
      ⟨fun x hx g => by
        have := (Subgroup.mem_normalizer_iff.mp (hn (Subgroup.mem_top g)) x).mp hx
        simpa using this⟩
    have hleP : CFSG.Open.pCoreOf 2 (⊤ : Subgroup G) ≤ CFSG.pPrimeCore 3 G :=
      le_pPrimeCore_of_normal hnormal (not_three_dvd_card_of_isPGroup_two h2)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hleP.trans h.pPrimeCore_le)
      (le_top.trans hn) h2
  ·
    refine hRP.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top ?_ hP2)
    rw [Subgroup.normalizer_eq_top]

omit [Finite G] in
theorem exists_quotient_top_of_starQuot (hPeq : CFSG.pCore 2 G = CFSG.pPrimeCore 3 G)
    {W : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)} (hWn : W.Normal) (hWZ : IsZ3L34OrHeisSL34 W)
    {s : G} (hWs : W ⊔ Subgroup.zpowers (starQuot G s) = ⊤) (hsW : starQuot G s ∉ W) :
    ∃ X : Subgroup ((⊤ : Subgroup G) ⧸ CFSG.pCore 2 (⊤ : Subgroup G)), X.Normal ∧
      IsZ3L34OrHeisSL34 X ∧
      X ⊔ Subgroup.zpowers
          (QuotientGroup.mk' (CFSG.pCore 2 (⊤ : Subgroup G)) ⟨s, Subgroup.mem_top s⟩) = ⊤ ∧
      QuotientGroup.mk' (CFSG.pCore 2 (⊤ : Subgroup G)) ⟨s, Subgroup.mem_top s⟩ ∉ X := by
  have he : Subgroup.map ((Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G) : ↥(⊤ : Subgroup G) →* G)
      (CFSG.pCore 2 ↥(⊤ : Subgroup G)) = CFSG.pPrimeCore 3 G := by
    rw [← hPeq]
    exact CFSG.pCore_map_iso 2 Subgroup.topEquiv
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (⊤ : Subgroup G) ⧸ CFSG.pCore 2 (⊤ : Subgroup G) ≃*
      G ⧸ CFSG.pPrimeCore 3 G,
      Φ (QuotientGroup.mk' (CFSG.pCore 2 (⊤ : Subgroup G)) ⟨s, Subgroup.mem_top s⟩) =
        starQuot G s :=
    ⟨QuotientGroup.congr _ _ Subgroup.topEquiv he, by rw [QuotientGroup.congr_mk']; rfl⟩
  have hΦs : QuotientGroup.mk' (CFSG.pCore 2 (⊤ : Subgroup G)) ⟨s, Subgroup.mem_top s⟩ =
      Φ.symm.toMonoidHom (starQuot G s) := by
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.eq_symm_apply, hΦ]
  refine ⟨W.map Φ.symm.toMonoidHom, hWn.map _ Φ.symm.surjective,
    IsZ3L34OrHeisSL34.of_mulEquiv (W.equivMapOfInjective _ Φ.symm.injective) hWZ, ?_, ?_⟩
  · rw [hΦs, ← MonoidHom.map_zpowers, ← Subgroup.map_sup, hWs,
      Subgroup.map_top_of_surjective Φ.symm.toMonoidHom Φ.symm.surjective]
  · rw [hΦs, Subgroup.mem_map_iff_mem (f := Φ.symm.toMonoidHom) Φ.symm.injective]
    exact hsW

end Star

end Item4442

open Item4442 in
theorem rank3II_4_44_2_of_inputs
    (h45 : Item4_5)
    (h434 : Item4_34Sec) (hmult : KFacts.L34CenterThreePrimeTwo) : Item4_44_2 := by
  intro G _ _ A M h hG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA3 : IsPGroup 3 A := h.isE27.isPGroup
  obtain ⟨L, hL, hQL, hcomm, hLM⟩ :=
    rank3II_4_50_of_item4_47 (rank3II_4_47_of h45) G A M h (Or.inr hG)
  have hAL := h.le_normalizer_of_mem_thetaComponents h45 hL
  have h3L := h.three_dvd_card_of_not_le h45 hL hLM
  have hZ := h.isZ3L34OrHeisSL34_map_starQuot h434 h45 hL hQL hcomm hLM
  have hIC : inSubgroup perfectResidual (⊤ : Subgroup G) ∈ oTwoComponents G :=
    mem_oTwoComponents_of_mem_oTwoComponentsIn_top hG.2.1
  have hLne : L ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at h3L
    norm_num at h3L
  have hLI : L = inSubgroup perfectResidual (⊤ : Subgroup G) :=
    theta_component_eq_of_perfect_le Nat.prime_three hL
      (mem_thetaComponents_of_mem_oTwoComponents hIC) hLne hL.1 le_rfl
      (le_inSubgroup_perfectResidual_top hL.1)
  have hLC : L ∈ oTwoComponents G := hLI ▸ hIC
  have hLn : L.Normal := hLI ▸ inSubgroup_perfectResidual_top_normal
  have htop : A ⊔ CFSG.Open.pCoreOf 2 M ⊔ L = ⊤ := by
    have h1 : ⊤ = L ⊔ A ⊔ CFSG.Open.pCoreOf 2 M := by
      have h2 := hG.1
      rwa [top_inf_eq, ← hLI] at h2
    rw [eq_top_iff, h1]
    exact sup_le (sup_le le_sup_right (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)
  obtain ⟨K, _, -, -, ⟨ψ⟩⟩ := exists_solvable_quotient_projSL hA3 hL h3L hAL hZ
  have : Group.IsPerfect L := hL.1
  have hθ2 := isPGroup_two_aschbacherSolvableCore hmult hLC.2.2 ψ
  have hLP2 : IsPGroup 2 (L ⊓ CFSG.pPrimeCore 3 G : Subgroup G) := by
    rw [inf_pPrimeCore_eq_of_mem_thetaComponents hL h3L]
    exact hθ2.map _
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    h.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hRL : CFSG.Open.pCoreOf 2 M ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact le_top
  have hP2 := isPGroup_two_pPrimeCore_of_sup_eq_top htop hA3 hR2 hAR hAL hRL hLP2
  have hPR : CFSG.pPrimeCore 3 G ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.pPrimeCore_le
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) hP2
  have hPeq : CFSG.pCore 2 G = CFSG.pPrimeCore 3 G := le_antisymm
    (le_pPrimeCore_of_normal CFSG.pCore_normal
      (not_three_dvd_card_of_isPGroup_two CFSG.pCore_isPGroup))
    (le_sSup ⟨inferInstance, hP2⟩)
  have hact := not_map_pCoreOf_le_centralizer h hG htop hP2
  have hR3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 M) := not_three_dvd_card_of_isPGroup_two hR2
  have hs : Group.IsSolvable (A ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) :=
    isSolvable_sup_of_le_normalizer (isSolvable_of_isPGroup hA3) (isSolvable_of_isPGroup hR2) hAR
  obtain ⟨hex, hpair, hgf⟩ := concl434_consequences h434 h hL hLM hAL hRL hAR hR3 hs hact
  have hθP := mem_aschbacherSolvableCore_iff_of_eq_top htop hP2
  have hRH : CFSG.Open.pCoreOf 2 M ≤ A ⊔ CFSG.Open.pCoreOf 2 M ⊔ L :=
    le_sup_right.trans le_sup_left
  have hpair' : ∀ t₁ ∈ CFSG.Open.pCoreOf 2 M, ∀ t₂ ∈ CFSG.Open.pCoreOf 2 M,
      t₁ ∉ CFSG.pPrimeCore 3 G → t₂ ∉ CFSG.pPrimeCore 3 G → t₁⁻¹ * t₂ ∈ CFSG.pPrimeCore 3 G := by
    intro t₁ h₁ t₂ h₂ hn₁ hn₂
    exact (hθP _).mp (hpair ⟨t₁, hRH h₁⟩ ⟨t₂, hRH h₂⟩ h₁ h₂
      (fun h0 => hn₁ ((hθP _).mp h0)) (fun h0 => hn₂ ((hθP _).mp h0)))
  have hcomm2 : ∀ t ∈ CFSG.Open.pCoreOf 2 M, ∀ a ∈ A,
      t * a * t⁻¹ * a⁻¹ ∈ CFSG.pPrimeCore 3 G := by
    intro t ht a ha
    by_cases htP : t ∈ CFSG.pPrimeCore 3 G
    · have h1 : a * t⁻¹ * a⁻¹ ∈ CFSG.pPrimeCore 3 G :=
        (inferInstance : (CFSG.pPrimeCore 3 G).Normal).conj_mem _ (inv_mem htP) a
      have h2 : t * a * t⁻¹ * a⁻¹ = t * (a * t⁻¹ * a⁻¹) := by group
      rw [h2]
      exact mul_mem htP h1
    · have ht' : t⁻¹ ∉ CFSG.pPrimeCore 3 G := fun h0 => htP (by simpa using inv_mem h0)
      have haR : a * t⁻¹ * a⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
        (Subgroup.mem_normalizer_iff.mp (hAR ha) _).mp (inv_mem ht)
      have haP : a * t⁻¹ * a⁻¹ ∉ CFSG.pPrimeCore 3 G := fun h0 => ht' (by
        have := (inferInstance : (CFSG.pPrimeCore 3 G).Normal).conj_mem _ h0 a⁻¹
        simpa [mul_assoc] using this)
      have h1 := hpair' t⁻¹ (inv_mem ht) _ haR ht' haP
      have h2 : t * a * t⁻¹ * a⁻¹ = t⁻¹⁻¹ * (a * t⁻¹ * a⁻¹) := by group
      rw [h2]
      exact h1
  have hcen : ∀ t ∈ CFSG.Open.pCoreOf 2 M, starQuot G t ∈
      Subgroup.centralizer ((A.map (starQuot G) : Subgroup _) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h1 : starQuot G (t * a * t⁻¹ * a⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hcomm2 t ht a ha)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  obtain ⟨x₀, hx₀R, hx₀θ⟩ := hex
  have ht₀P : (x₀ : G) ∉ CFSG.pPrimeCore 3 G := fun h0 => hx₀θ ((hθP x₀).mpr h0)
  obtain ⟨s, hsA, hsR, hsP⟩ : ∃ s ∈ Subgroup.centralizer (A : Set G),
      s ∈ CFSG.Open.pCoreOf 2 M ∧ s ∉ CFSG.pPrimeCore 3 G := by
    have hy := hcen _ hx₀R
    rw [← CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 (CFSG.pPrimeCore 3 G)
      not_three_dvd_card_pPrimeCore A hA3] at hy
    obtain ⟨c, hc, hce⟩ := hy
    have hce' : ((x₀ : G) : G ⧸ CFSG.pPrimeCore 3 G) = (c : G ⧸ CFSG.pPrimeCore 3 G) := hce.symm
    have hct : (x₀ : G)⁻¹ * c ∈ CFSG.pPrimeCore 3 G := QuotientGroup.eq.mp hce'
    refine ⟨c, hc, ?_, fun hcP => ht₀P ?_⟩
    · have h1 : c = (x₀ : G) * ((x₀ : G)⁻¹ * c) := by group
      rw [h1]
      exact mul_mem hx₀R (hPR hct)
    · have h1 : (x₀ : G) = c * ((x₀ : G)⁻¹ * c)⁻¹ := by group
      rw [h1]
      exact mul_mem hcP (inv_mem hct)
  have hsgf : KFacts.InducesStdKind L s .graphField :=
    hgf ⟨s, hRH hsR⟩ hsR fun h0 => hsP ((hθP _).mp h0)
  have hsout : InducesOuterTheta s L := hsgf.inducesOuterTheta L (by decide)
  have hsurj : Function.Surjective (starQuot G) := QuotientGroup.mk'_surjective _
  have hLsn : (L.map (starQuot G)).Normal := hLn.map _ hsurj
  have hWn : ((A ⊔ L).map (starQuot G)).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff,
      ← Subgroup.map_top_of_surjective (starQuot G) hsurj, ← htop,
      Subgroup.map_sup (A ⊔ CFSG.Open.pCoreOf 2 M) L,
      Subgroup.map_sup A (CFSG.Open.pCoreOf 2 M)]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (Subgroup.map_mono le_sup_left).trans Subgroup.le_normalizer
    · rintro _ ⟨t, ht, rfl⟩
      rw [Subgroup.map_sup]
      refine mem_normalizer_sup (Subgroup.centralizer_le_normalizer _ (hcen t ht)) ?_
      rw [Subgroup.normalizer_eq_top_iff.mpr hLsn]
      exact Subgroup.mem_top _
    · exact (Subgroup.map_mono le_sup_right).trans Subgroup.le_normalizer
  have hWs : (A ⊔ L).map (starQuot G) ⊔ Subgroup.zpowers (starQuot G s) = ⊤ := by
    rw [eq_top_iff, ← Subgroup.map_top_of_surjective (starQuot G) hsurj, ← htop,
      Subgroup.map_sup (A ⊔ CFSG.Open.pCoreOf 2 M) L,
      Subgroup.map_sup A (CFSG.Open.pCoreOf 2 M)]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (Subgroup.map_mono le_sup_left).trans le_sup_left
    · rintro _ ⟨t, ht, rfl⟩
      refine Subgroup.mem_sup_right ?_
      by_cases htP : t ∈ CFSG.pPrimeCore 3 G
      · have h1 : starQuot G t = 1 := (QuotientGroup.eq_one_iff t).mpr htP
        rw [h1]
        exact one_mem _
      · have h1 := hpair' s hsR t ht hsP htP
        have h2 : starQuot G t = starQuot G s :=
          QuotientGroup.eq.mpr (by simpa using inv_mem h1)
        rw [h2]
        exact Subgroup.mem_zpowers _
    · exact (Subgroup.map_mono le_sup_right).trans le_sup_left
  have hsW := not_mem_map_starQuot_of_inducesOuterTheta hA3 hL h3L hAL hZ hsout
  obtain ⟨X, hX⟩ := exists_quotient_top_of_starQuot hPeq hWn hZ hWs hsW
  refine ⟨s, ?_, hsA, ?_, Subgroup.mem_top s, X, hX⟩
  · rw [top_inf_eq]
    exact hsR
  · rw [← hLI]
    exact hsgf

theorem rank3II_4_44_2_of
    (h45 : Item4_5)
    (h434 : Item4_34Sec) : Item4_44_2 :=
  rank3II_4_44_2_of_inputs h45 h434 KFacts.l34CenterThreePrimeTwo

theorem rank3II_4_53_of_core
    (h434 : Item4_34Sec)
    (h45 : Item4_5) (h452 : Item4_52) : Item4_53 :=
  rank3II_4_53_of h434 h45 h452 KFacts.l34CenterThreePrimeTwo

theorem rank3II_4_44_1_of_core
    (h434 : Item4_34Sec)
    (h447 : Item4_47) (h45 : Item4_5) (h44 : Item4_4) (hres : Item4_52Residual) : Item4_44_1 :=
  rank3II_4_44_1_of_inputs h434 h447 h45 h44 hres KFacts.l34CenterThreePrimeTwo

theorem rank3II_4_44_1_of_item4_5
    (h434 : Item4_34Sec)
    (h45 : Item4_5) (h44 : Item4_4) (hres : Item4_52Residual) : Item4_44_1 :=
  rank3II_4_44_1_of_core h434 (rank3II_4_47_of h45) h45 h44 hres

end CFSG.RankThree.PartTwo.Sec4
