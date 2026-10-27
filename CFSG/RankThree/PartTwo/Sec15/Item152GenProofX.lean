module

public import CFSG.RankThree.PartTwo.Sec15.Item152StepsGen
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofXTools
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.RankThree.PartTwo.Sec14.Item14J2

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Step152GenXCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    ∀ Y M X : Subgroup G, Ctx152 A (lB A) Y M X →
    ∀ (d : G) (p : ℕ) (P T K S : Subgroup G), Data152 A (lB A) X c L d p P T K S →
      X ≤ (X ⊓ L) ⊔ (aschbacherSolvableCore 3 ↥X).map X.subtype

namespace Proof152Gen

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_theta_quot_of_ctx152
    {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y M X : Subgroup G} (hctx : Ctx152 A LB Y M X) :
    IsSimpleGroup (↥X ⧸ aschbacherSolvableCore 3 ↥X) ∧
      Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXq := isQuasisimple_theta_of_mem_thetaComponentsIn hctx.mem_comp
  have hθ : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60 ∧
      CFSG.pPrimeCore 3 ↥X = aschbacherSolvableCore 3 ↥X := by
    rcases hctx.sl25 with he | he
    · obtain ⟨e⟩ := he
      exact sl25_theta hXq e
    · obtain ⟨e⟩ := he
      exact sl25_theta hXq e
  obtain ⟨h60, hcore⟩ := hθ
  set θ := aschbacherSolvableCore 3 ↥X with hθdef
  have hθ3 := (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
  have hQp : Group.IsPerfect (↥X ⧸ θ) := hXq.1
  have hZ : Subgroup.center (↥X ⧸ θ) = ⊥ := by
    by_cases h3 : 3 ∣ Nat.card (Subgroup.center (↥X ⧸ θ))
    · exfalso
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
      set T := Subgroup.zpowers (z : ↥X ⧸ θ) with hT
      have hTc : T ≤ Subgroup.center (↥X ⧸ θ) := Subgroup.zpowers_le.mpr z.2
      have : T.Normal := Subgroup.normal_of_le_center hTc
      have hT3 : Nat.card T = 3 := by
        rw [hT, Nat.card_zpowers, Subgroup.orderOf_coe, hz]
      have hperf : Group.IsPerfect ((↥X ⧸ θ) ⧸ T) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T)
      have h20 : Nat.card ((↥X ⧸ θ) ⧸ T) = 20 := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup T
        rw [h60, hT3] at h
        omega
      exact false_of_isPerfect_of_card_twenty hperf h20
    · set K := (Subgroup.center (↥X ⧸ θ)).comap (QuotientGroup.mk' θ) with hK
      have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
      have hKcard : Nat.card K = Nat.card θ * Nat.card (Subgroup.center (↥X ⧸ θ)) :=
        QuotientGroup.card_preimage_mk θ (Subgroup.center (↥X ⧸ θ) : Set (↥X ⧸ θ))
      have hK3 : Nat.Coprime 3 (Nat.card K) := by
        rw [hKcard]
        exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
      have hKle : K ≤ CFSG.pPrimeCore 3 ↥X := le_sSup ⟨hKn, hK3⟩
      rw [hcore] at hKle
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ q
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hKle hq
  have : IsSimpleGroup ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)) := hXq.2.1
  have e1 : (↥X ⧸ θ) ≃* (↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact ⟨e1.isSimpleGroup, h60⟩

omit [Finite G] in
theorem map_subgroupOf_eq_top_of_le_sup {X W : Subgroup G} (hWX : W ≤ X)
    (h : X ≤ W ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    (W.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hx : (x : G) ∈ ((W ⊔ inSubgroup (aschbacherSolvableCore 3) X : Subgroup G) : Set G) :=
    h x.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hWX.trans (Sec6.le_normalizer_theta X))] at hx
  obtain ⟨w, hw, t, ⟨t', ht', rfl⟩, hwt⟩ := Set.mem_mul.mp hx
  refine ⟨⟨w, hWX hw⟩, Subgroup.mem_subgroupOf.mpr hw, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have he : (⟨w, hWX hw⟩ : ↥X)⁻¹ * x = t' := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hwt]
    simp
  rw [he]
  exact ht'

theorem map_inf_centralizer_eq {X W : Subgroup G} {d : G} (hWX : W ≤ X)
    (hdW : d ∈ Subgroup.normalizer (W : Set G)) (hd3 : d ^ 3 = 1)
    (hdC : d ∈ Sec4.thetaQuotCentralizer X) :
    ((W ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) =
      (W.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  obtain ⟨-, hθ3⟩ := Sec6.theta_solvable_and_not_dvd X
  have hWθ : W ≤ Subgroup.normalizer (θX : Set G) := hWX.trans (Sec6.le_normalizer_theta X)
  have hZW : Subgroup.zpowers d ≤ Subgroup.normalizer (W : Set G) := Subgroup.zpowers_le.mpr hdW
  have hZC : Subgroup.zpowers d ≤ Sec4.thetaQuotCentralizer X := Subgroup.zpowers_le.mpr hdC
  have hZ3 : IsPGroup 3 (Subgroup.zpowers d) := by
    rintro ⟨b, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hd3, one_zpow]
  set N := θX.subgroupOf W with hN
  have hNn : N.Normal := by
    constructor
    intro n hn w
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hWθ w.2) n).mp hn
  let α : Subgroup.zpowers d →* MulAut W := W.normalizerMonoidHom.comp (Subgroup.inclusion hZW)
  have hα : ∀ (b : Subgroup.zpowers d) (w : W), ((α b w : W) : G) = b * w * (b : G)⁻¹ :=
    fun _ _ => rfl
  have hNα : ∀ b : Subgroup.zpowers d, ∀ n ∈ N, α b n ∈ N := by
    intro b n hn
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hα]
    exact (Subgroup.mem_normalizer_iff.mp
      (Sec6.normalizer_le_normalizer_theta X (Sec6.thetaQuotCentralizer_le_normalizer X
        (hZC b.2))) _).mp hn
  have hcop : ¬ 3 ∣ Nat.card N := by
    intro h3
    apply hθ3
    have h1 : Nat.card N = Nat.card (θX ⊓ W : Subgroup G) := by
      rw [hN, ← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : θX ⊓ W ≤ W)).toEquiv
    rw [h1] at h3
    exact h3.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hZ3 α N hNα hcop
  refine le_antisymm (Subgroup.map_mono fun y hy =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy).1) ?_
  rintro _ ⟨x, hxW, rfl⟩
  have hxW' : (x : G) ∈ W := Subgroup.mem_subgroupOf.mp hxW
  have hfix : ((⟨x, hxW'⟩ : W) : W ⧸ N) ∈
      {q : W ⧸ N | ∀ b, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction
        α N hNα b q = q} := by
    intro b
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    obtain ⟨-, hbl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp (hZC b.2)
    have h1 := inv_mem (hbl (x : G) x.2)
    have he : ((α b ⟨x, hxW'⟩ : W)⁻¹ * ⟨x, hxW'⟩ : W).val =
        ((x : G)⁻¹ * ((b : G) * x * (b : G)⁻¹))⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hα]
      group
    rw [he]
    exact h1
  rw [hlift] at hfix
  obtain ⟨c₀, hc₀, hc₀w⟩ := hfix
  have hc₀d : (c₀ : G) ∈ Subgroup.centralizer ({d} : Set G) := by
    have h := congrArg Subtype.val (hc₀ ⟨d, Subgroup.mem_zpowers d⟩)
    rw [hα] at h
    change d * (c₀ : G) * d⁻¹ = c₀ at h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c₀ : G) * d = d * c₀ * d⁻¹ * d := by rw [h]
      _ = d * c₀ := by group
  refine ⟨⟨c₀, hWX c₀.2⟩, Subgroup.mem_subgroupOf.mpr ⟨c₀.2, hc₀d⟩, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hc₀w
  obtain ⟨t, ht, hte⟩ := hc₀w
  have hte' : (t : G) = (c₀ : G)⁻¹ * x := by simpa using hte
  have he : (⟨c₀, hWX c₀.2⟩ : ↥X)⁻¹ * x = t := by
    apply Subtype.ext
    rw [hte', Subgroup.coe_mul, Subgroup.coe_inv]
  rw [he]
  exact ht

theorem map_inf_centralizer_eq_top {X W : Subgroup G} {d : G} (hWX : W ≤ X)
    (hdW : d ∈ Subgroup.normalizer (W : Set G)) (hd3 : d ^ 3 = 1)
    (hdC : d ∈ Sec4.thetaQuotCentralizer X)
    (hW : (W.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤) :
    ((W ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ := by
  rw [map_inf_centralizer_eq hWX hdW hd3 hdC, hW]

theorem exists_isPerfect_cover {X W₀ : Subgroup G}
    (hperf : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hW₀ : (W₀.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤) :
    ∃ D : Subgroup G, D ≤ W₀ ∧ Group.IsPerfect D ∧
      (D.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) with hπ
  obtain ⟨D', -, hD'⟩ := Finite.exists_le_minimal
    (p := fun D' : Subgroup ↥X => D' ≤ W₀.subgroupOf X ∧ D'.map π = ⊤)
    (a := W₀.subgroupOf X) ⟨le_rfl, hW₀⟩
  obtain ⟨hD'W, hD'top⟩ := hD'.prop
  have hcomm : ⁅D', D'⁆ = D' := by
    refine le_antisymm (Subgroup.commutator_le_self D') (hD'.2 ⟨(Subgroup.commutator_le_self
      D').trans hD'W, ?_⟩ (Subgroup.commutator_le_self D'))
    rw [Subgroup.map_commutator, hD'top, ← commutator_def]
    exact hperf.commutator_eq_top
  have hD'p : Group.IsPerfect D' := by
    refine ⟨Subgroup.map_injective D'.subtype_injective ?_⟩
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hcomm]
  refine ⟨D'.map X.subtype, ?_, isPerfect_map_subtype hD'p, ?_⟩
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact Subgroup.mem_subgroupOf.mp (hD'W hy')
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    exact hD'top

theorem card_map_eq_sixty
    {X L D : Subgroup G}
    (hXs : IsSimpleGroup (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hX60 : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hθL2 : IsPGroup 2 (aschbacherSolvableCore 3 ↥L)) (hDX : D ≤ X) (hDL : D ≤ L)
    (hDtop : (D.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤)
    (hDp : Group.IsPerfect D) {z : ↥L ⧸ aschbacherSolvableCore 3 ↥L} (hz1 : z ≠ 1)
    (hzc : ∃ S' : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L), z ∈ (S' : Subgroup _) ∧
      (S' : Subgroup _) ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (hDz : (D.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤
      Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :
    Nat.card ((D.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 60 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  let θX := aschbacherSolvableCore 3 ↥X
  let θL := aschbacherSolvableCore 3 ↥L
  let πX := QuotientGroup.mk' θX
  let ρ := QuotientGroup.mk' θL
  let F := (D.subgroupOf L).map ρ
  let fX : ↥D →* ↥X ⧸ θX := πX.comp (Subgroup.inclusion hDX)
  let fL : ↥D →* ↥L ⧸ θL := ρ.comp (Subgroup.inclusion hDL)
  have hincl : ∀ {K : Subgroup G} (hDK : D ≤ K),
      (Subgroup.inclusion hDK).range = D.subgroupOf K := by
    intro K hDK
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr y.2
    · intro hx
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hfXr : fX.range = (D.subgroupOf X).map πX := by
    rw [MonoidHom.range_comp, hincl hDX]
  have hfLr : fL.range = F := by
    rw [MonoidHom.range_comp, hincl hDL]
  have hcardX : Nat.card fX.ker * 60 = Nat.card D := by
    have h := Subgroup.card_mul_index fX.ker
    rw [Subgroup.index_ker, hfXr, hDtop, Subgroup.card_top, hX60] at h
    exact h
  have hcardL : Nat.card fL.ker * Nat.card F = Nat.card D := by
    have h := Subgroup.card_mul_index fL.ker
    rw [Subgroup.index_ker, hfLr] at h
    exact h
  have hkerL : fL.ker.map (Subgroup.inclusion hDL) ≤ θL := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp hx
  have hkerX : fX.ker.map (Subgroup.inclusion hDX) ≤ θX := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp hx
  have hker2 : IsPGroup 2 fL.ker :=
    ((hθL2.to_le hkerL).of_equiv
      (fL.ker.equivMapOfInjective _ (Subgroup.inclusion_injective hDL)).symm)
  have hkerX3 : ¬ 3 ∣ Nat.card fX.ker := by
    intro h3
    have h1 : Nat.card fX.ker = Nat.card (fX.ker.map (Subgroup.inclusion hDX)) :=
      (Subgroup.card_map_of_injective (Subgroup.inclusion_injective hDX)).symm
    rw [h1] at h3
    exact (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
      (h3.trans (Subgroup.card_dvd_of_le hkerX))
  have hfXs : Function.Surjective fX := by
    rw [← MonoidHom.range_eq_top, hfXr, hDtop]
  have hle : fL.ker ≤ fX.ker := by
    have hn : (fL.ker.map fX).Normal := (fL.normal_ker).map fX hfXs
    rcases hn.eq_bot_or_eq_top with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have h2 : IsPGroup 2 (fL.ker.map fX) := hker2.map fX
      rw [h] at h2
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (h2.of_equiv Subgroup.topEquiv)
      rw [hX60] at hk
      have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 60)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hm := Subgroup.relIndex_mul_card fL.ker fX.ker
  rw [inf_eq_left.mpr hle] at hm
  let m := fL.ker.relIndex fX.ker
  have hFm : Nat.card F = 60 * m := by
    have hpos : 0 < Nat.card fL.ker := Nat.card_pos
    have h : Nat.card fL.ker * Nat.card F = Nat.card fL.ker * (60 * m) := by
      rw [hcardL, ← hcardX, ← hm]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos h
  have hm3 : Nat.Coprime m 9 := by
    have hmd : m ∣ Nat.card fX.ker := Subgroup.relIndex_dvd_card _ _
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (fun h3 => hkerX3 (h3.trans hmd))).symm
  obtain ⟨-, hZ3, hZn, ⟨eA⟩⟩ := KFacts.KS14.j2_centralizer_quotient h415 hJ hz1 hzc
  let C := Subgroup.centralizer ({z} : Set (↥L ⧸ θL))
  let Z := (Subgroup.zpowers z).subgroupOf C
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := KFacts.KS14.card_alternatingGroup_six
  have hC1080 : Nat.card C = 1080 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [Nat.card_congr eA.toEquiv, hA6, hZ3] at h
    exact h
  have hFC : 60 * m ∣ 60 * 18 := by
    have h := Subgroup.card_dvd_of_le hDz
    rw [hC1080, hFm] at h
    exact h
  have hm18 : m ∣ 2 * 9 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hFC
  have hm2 : m ∣ 2 := hm3.dvd_of_dvd_mul_right hm18
  rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with h1 | h2
  · rw [hFm, h1]
  · exfalso
    have hF120 : Nat.card F = 120 := by rw [hFm, h2]
    have : Group.IsPerfect (D.subgroupOf L) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hDL).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have hFp : Group.IsPerfect F := Group.IsPerfect.map _
    have hF'card : Nat.card (F.subgroupOf C) = 120 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDz).toEquiv, hF120]
    have hF'p : Group.IsPerfect (F.subgroupOf C) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hDz).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have : Group.IsPerfect (alternatingGroup (Fin 6)) := Sec14.alternatingGroup_six_isPerfect
    have hQp : Group.IsPerfect (↥C ⧸ Z) :=
      Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom) eA.symm.surjective
    have hQ360 : Nat.card (↥C ⧸ Z) = 360 := by rw [Nat.card_congr eA.toEquiv, hA6]
    exact false_of_isPerfect_card_one_hundred_twenty Z hZ3 hQp hQ360 _ hF'p hF'card

end Proof152Gen

open Proof152Gen

theorem step152GenX_of
    (hcov : Step152GenXCover) : Step152GenX := by
  intro G _ _ A c L h Y M X hctx d p P T K S hD _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS13 := h.toSec13Data
  obtain ⟨hXs, hX60⟩ := isSimpleGroup_theta_quot_of_ctx152 hctx
  have hXp : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    (isQuasisimple_theta_of_mem_thetaComponentsIn hctx.mem_comp).1
  have hdA := hD.mem_d
  have hd3 : d ^ 3 = 1 := (Late.isE27_of_mem_partTwoE hS13.mem_partTwoE).1.2 d hdA
  obtain ⟨hdL, S3, hdS3, hS3d⟩ := hD.central_d
  have hdX : d ∈ Subgroup.normalizer (X : Set G) := hctx.norm_x hdA
  have hdXL : d ∈ Subgroup.normalizer ((X ⊓ L : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hctx.norm_x hS13.le_normalizer hdA
  have hdsc : d ∈ Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) := by
    rw [hD.cent]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hdC : d ∈ Sec4.thetaQuotCentralizer X := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hdX, fun l hl => ?_⟩
    have h1 := hdsc.2 l hl
    have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta X (inv_mem hl)) _).mp h1
    have he : l⁻¹ * (d * l * d⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (d * l * d⁻¹) := by group
    rw [he] at h2
    exact h2
  have hW : ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ :=
    map_subgroupOf_eq_top_of_le_sup inf_le_left (hcov G A c L h Y M X hctx d p P T K S hD)
  have hW' := map_inf_centralizer_eq_top inf_le_left hdXL hd3 hdC hW
  obtain ⟨D, hDW, hDp, hDtop⟩ := exists_isPerfect_cover hXp hW'
  have hDX : D ≤ X := hDW.trans (inf_le_left.trans inf_le_left)
  have hDL : D ≤ L := hDW.trans (inf_le_left.trans inf_le_right)
  have hDd : D ≤ Subgroup.centralizer ({d} : Set G) := hDW.trans inf_le_right
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set ρ := QuotientGroup.mk' θ with hρ
  set z : ↥L ⧸ θ := ρ ⟨d, hdL⟩ with hz
  have hz1 : z ≠ 1 := by
    intro hz1
    have hmem : (⟨d, hdL⟩ : ↥L) ∈ θ := (QuotientGroup.eq_one_iff _).mp hz1
    have hord : orderOf (⟨⟨d, hdL⟩, hmem⟩ : θ) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hd3 hD.ne_d
    have h3 := orderOf_dvd_natCard (⟨⟨d, hdL⟩, hmem⟩ : θ)
    rw [hord] at h3
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1 h3
  have hzc : ∃ S' : Sylow 3 (↥L ⧸ θ), z ∈ (S' : Subgroup (↥L ⧸ θ)) ∧
      (S' : Subgroup (↥L ⧸ θ)) ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    refine ⟨S3.mapSurjective (QuotientGroup.mk'_surjective θ), ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact ⟨⟨d, hdL⟩, hdS3, rfl⟩
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨s, hs, rfl⟩
      have hs' := hS3d hs
      rw [Subgroup.mem_centralizer_singleton_iff] at hs' ⊢
      rw [hz, ← map_mul, ← map_mul, hs']
  have hcomm : ∀ y ∈ (D.subgroupOf L).map ρ, ∀ k : ℤ, ∀ hk : d ^ k ∈ L,
      ρ ⟨d ^ k, hk⟩ * y = y * ρ ⟨d ^ k, hk⟩ := by
    rintro _ ⟨y, hy, rfl⟩ k hk
    have hyd : (y : G) * d = d * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hDd (Subgroup.mem_subgroupOf.mp hy))
    have hyk : (d ^ k) * (y : G) = y * d ^ k := (Commute.zpow_right hyd k).eq.symm
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyk
  have hDz : (D.subgroupOf L).map ρ ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hcomm y hy 1 (by rw [zpow_one]; exact hdL)
    have hz' : ρ ⟨d ^ (1 : ℤ), by rw [zpow_one]; exact hdL⟩ = z := by
      rw [hz]
      congr 1
      exact Subtype.ext (zpow_one d)
    rw [hz'] at h
    exact h.symm
  refine ⟨(D.subgroupOf L).map ρ, Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hDX (Subgroup.mem_subgroupOf.mp hx)), ?_,
    card_map_eq_sixty hXs hX60 hD.hj (isPGroup_theta_of_j2 h hD.hj) hDX hDL hDtop hDp hz1 hzc
      hDz, ?_⟩
  · have : Group.IsPerfect (D.subgroupOf L) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hDL).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact Group.IsPerfect.map _
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hw)
    have hw' : w = ⟨d ^ k, hk ▸ w.2⟩ := Subtype.ext hk.symm
    rw [hw']
    exact hcomm y hy k _

end CFSG.RankThree.PartTwo.Sec15
