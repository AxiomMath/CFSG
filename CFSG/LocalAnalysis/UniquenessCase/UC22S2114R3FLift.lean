module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3URank
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UCK47
import CFSG.LocalAnalysis.UniquenessCase.UC6G.S28
import CFSG.LocalAnalysis.GL83PartI.I_24_3.InnerPGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Semidihedral.Principal (coprime_fixed_point_lifting)
open CFSG.Semidihedral.Principal.CoprimeFixedPoint (quotientAction)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114r3f_exists_fixed_lift {L B : Subgroup G} (hBL : B ≤ normalizer (L : Set G))
    {r : ℕ} [Fact r.Prime] (hB : IsPGroup r ↥B)
    (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) {p : ℕ} [Fact p.Prime]
    {X : Subgroup (BarInf L)} (hX : IsPGroup p ↥X)
    (hfix : ∀ b (hb : b ∈ B), ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hBL hb⟩ x = x) :
    ∃ Q : Subgroup ↥L, IsPGroup p ↥Q ∧ Q.map (QuotientGroup.mk' (CFSG.solvableRadical ↥L)) = X ∧
      ∀ y ∈ Q, ∀ b ∈ B, b * (y : G) * b⁻¹ = y := by
  classical
  let N : Subgroup ↥L := CFSG.solvableRadical ↥L
  let π : ↥L →* BarInf L := QuotientGroup.mk' N
  let α : ↥B →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBL)
  have hN : ∀ a : ↥B, ∀ n ∈ N, α a n ∈ N := fun a n hn => by
    change α a n ∈ CFSG.solvableRadical ↥L
    rw [← CFSG.LieType.SteinbergBR.solvableRadical_map_equiv (α a)]
    exact Subgroup.mem_map_of_mem _ hn
  have hact : ∀ (a : ↥B) (q : BarInf L),
      quotientAction α N hN a q = inducedBarInfAutHom L ⟨a, hBL a.2⟩ q := by
    intro a q
    induction q using QuotientGroup.induction_on with
    | H x => rfl
  have hlift := coprime_fixed_point_lifting r hB α N hN hrK
  have hαc : ∀ (a : ↥B) (c : ↥L), ((α a c : ↥L) : G) = (a : G) * c * (a : G)⁻¹ :=
    fun _ _ => rfl
  let C : Subgroup ↥L := (centralizer (B : Set G)).comap L.subtype
  let Y : Subgroup ↥L := X.comap π ⊓ C
  have hYX : Y.map π = X := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_inf.1 hy).1
    · intro x hx
      have hxfix : x ∈ {q : BarInf L | ∀ a : ↥B, quotientAction α N hN a q = q} := fun a => by
        rw [hact]
        exact hfix a a.2 x hx
      rw [hlift] at hxfix
      obtain ⟨c, hc, rfl⟩ := hxfix
      refine ⟨c, Subgroup.mem_inf.2 ⟨hx, ?_⟩, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
      have h := congrArg Subtype.val (hc ⟨g, hg⟩)
      rw [hαc] at h
      change g * (c : G) = (c : G) * g
      calc g * (c : G) = g * c * g⁻¹ * g := by group
        _ = c * g := by rw [h]
  have hfY : ∀ y : ↥Y, π y ∈ X := fun y => (Subgroup.mem_inf.1 y.2).1
  let g : ↥Y →* ↥X := (π.comp Y.subtype).codRestrict X hfY
  have hg : Function.Surjective g := by
    rintro ⟨x, hx⟩
    rw [← hYX] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥Y))
  have hS : ((P.mapSurjective hg : Sylow p ↥X) : Subgroup ↥X) = ⊤ :=
    ((P.mapSurjective hg).is_maximal' (hX.to_subgroup ⊤) le_top).symm
  refine ⟨(P : Subgroup ↥Y).map Y.subtype, P.isPGroup'.map _, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact hfY y
    · intro x hx
      have hx' : (⟨x, hx⟩ : ↥X) ∈ ((P.mapSurjective hg : Sylow p ↥X) : Subgroup ↥X) := by
        rw [hS]
        exact Subgroup.mem_top _
      rw [Sylow.coe_mapSurjective] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      exact ⟨y, ⟨y, hy, rfl⟩, congrArg Subtype.val hyx⟩
  · rintro _ ⟨y, -, rfl⟩ b hb
    have h := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 b hb
    change b * ((y : ↥L) : G) = ((y : ↥L) : G) * b at h
    change b * ((y : ↥L) : G) * b⁻¹ = ((y : ↥L) : G)
    rw [h, mul_inv_cancel_right]

theorem uc22s2114r3f_two_le_pRank_centralizer {L B : Subgroup G}
    (hBL : B ≤ normalizer (L : Set G)) {r : ℕ} [Fact r.Prime] (hB : IsPGroup r ↥B)
    (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Subgroup (BarInf L)} (hX : IsPGroup p ↥X) (hXc : ¬ IsCyclic ↥X)
    (hfix : ∀ b (hb : b ∈ B), ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hBL hb⟩ x = x) :
    2 ≤ CFSG.Open.pRank p (L ⊓ centralizer (B : Set G)) := by
  obtain ⟨Q, hQp, hQX, hQB⟩ := uc22s2114r3f_exists_fixed_lift hBL hB hrK hX hfix
  have hQc : ¬ IsCyclic ↥(Q.map L.subtype) := by
    intro hc
    apply hXc
    rw [← hQX]
    haveI : IsCyclic ↥Q := isCyclic_of_surjective
      (Q.equivMapOfInjective L.subtype L.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
    exact isCyclic_of_surjective ((QuotientGroup.mk' _).subgroupMap Q)
      ((QuotientGroup.mk' _).subgroupMap_surjective Q)
  obtain ⟨D, hDQ, hD, hDc⟩ :=
    GL83.I243.Inner.exists_isElemAbelian_card_sq_of_not_isCyclic hp2 (hQp.map L.subtype) hQc
  refine CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt (hDQ.trans ?_) hD hDc
  rintro _ ⟨y, hy, rfl⟩
  refine Subgroup.mem_inf.2 ⟨y.2, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
  have h := hQB y hy b hb
  change b * (y : G) = (y : G) * b
  calc b * (y : G) = b * y * b⁻¹ * b := by group
    _ = y * b := by rw [h]

theorem uc22s2114r3f_exists_fixed_lift_elem {L B : Subgroup G}
    (hBL : B ≤ normalizer (L : Set G)) {r : ℕ} [Fact r.Prime] (hB : IsPGroup r ↥B)
    (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) {p : ℕ} [Fact p.Prime]
    (hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L)) {X : Subgroup (BarInf L)}
    (hX : IsPGroup p ↥X)
    (hfix : ∀ b (hb : b ∈ B), ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hBL hb⟩ x = x)
    {x : BarInf L} (hx : x ∈ X) :
    ∃ y : ↥L, QuotientGroup.mk' (CFSG.solvableRadical ↥L) y = x ∧ orderOf y = orderOf x ∧
      ∀ b ∈ B, b * (y : G) * b⁻¹ = y := by
  have hp : p.Prime := Fact.out
  obtain ⟨Q, hQp, hQX, hQB⟩ := uc22s2114r3f_exists_fixed_lift hBL hB hrK hX hfix
  rw [← hQX] at hx
  obtain ⟨y, hyQ, rfl⟩ := hx
  refine ⟨y, rfl, ?_, hQB y hyQ⟩
  have hdisj : Disjoint Q (CFSG.solvableRadical ↥L) := by
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK)
  refine Nat.dvd_antisymm ?_ (orderOf_map_dvd _ _)
  refine orderOf_dvd_of_pow_eq_one ?_
  have h1 : y ^ orderOf (QuotientGroup.mk' (CFSG.solvableRadical ↥L) y) ∈
      Q ⊓ CFSG.solvableRadical ↥L := by
    refine Subgroup.mem_inf.2 ⟨Q.pow_mem hyQ _, ?_⟩
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, pow_orderOf_eq_one]
  rwa [hdisj.eq_bot, Subgroup.mem_bot] at h1

theorem uc22s2114r3f_exists_lift {L : Subgroup G} {b : G} (hb : b ∈ normalizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (hbr : orderOf b = r)
    (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) {p : ℕ} [Fact p.Prime]
    (hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L)) {A : Type} [Group A]
    (hA : IsPGroup p A) (ι : A →* BarInf L) (hι : Function.Injective ι) (κ : A →* A)
    (hκ : ∀ a, inducedBarInfAutHom L ⟨b, hb⟩ (ι a) = ι (κ a)) :
    ∃ ψ : A →* G, Function.Injective ψ ∧ (∀ a, ψ a ∈ L) ∧ ∀ a, b * ψ a * b⁻¹ = ψ (κ a) := by
  classical
  have hp : p.Prime := Fact.out
  have : Fact r.Prime := ⟨hr⟩
  let π : ↥L →* BarInf L := QuotientGroup.mk' (CFSG.solvableRadical ↥L)
  let U : Subgroup (BarInf L) := ι.range
  have hUp : IsPGroup p ↥U := hA.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  let E : Subgroup G := (U.comap π).map L.subtype
  have hEL : E ≤ L := Subgroup.map_subtype_le _
  have hbE : b ∈ normalizer (E : Set G) := by
    refine Subgroup.mem_normalizer_fintype ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := hx
    refine ⟨L.normalizerMonoidHom ⟨b, hb⟩ x, ⟨κ a, ?_⟩, rfl⟩
    change ι (κ a) = inducedBarInfAutHom L ⟨b, hb⟩ (π x)
    rw [← hκ, ha]
  have hB : IsPGroup r ↥(zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one, Nat.card_zpowers, hbr])
  have hBE : zpowers b ≤ normalizer (E : Set G) := Subgroup.zpowers_le.2 hbE
  have hfE : ∀ x : ↥E, π (Subgroup.inclusion hEL x) ∈ U := by
    rintro ⟨_, y, hy, rfl⟩
    exact hy
  let f : ↥E →* ↥U := (π.comp (Subgroup.inclusion hEL)).codRestrict U hfE
  have hf : Function.Surjective f := by
    rintro ⟨u, hu⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥L) u
    exact ⟨⟨x, x, hu, rfl⟩, rfl⟩
  have hker : Nat.card f.ker ∣ Nat.card (CFSG.solvableRadical ↥L) := by
    have hkerEq : f.ker = (CFSG.solvableRadical ↥L).comap (Subgroup.inclusion hEL) := by
      ext x
      show f x = 1 ↔ Subgroup.inclusion hEL x ∈ CFSG.solvableRadical ↥L
      rw [← QuotientGroup.eq_one_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hkerEq]
    exact Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hEL)
  have hnd : ¬ r ∣ Nat.card (Sylow p ↥E) := by
    obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥E))
    have h1 : Nat.card (Sylow p ↥E) ∣ Nat.card ↥E :=
      (Sylow.card_dvd_index P₀).trans (Subgroup.index_dvd_card _)
    rw [← Subgroup.card_ker_mul_card_of_surjective hf] at h1
    obtain ⟨k, hk⟩ := hUp.exists_card_eq
    rw [hk] at h1
    have hcop : Nat.Coprime (Nat.card (Sylow p ↥E)) (p ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_comm.1
        ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_sylow p ↥E)))
    intro hr'
    exact hrK (hr'.trans ((hcop.dvd_of_dvd_mul_right h1).trans hker))
  let φ : ↥(zpowers b) →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hBE)
  let : MulDistribMulAction ↥(zpowers b) ↥E := MulDistribMulAction.compHom ↥E φ
  obtain ⟨P, hP⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p ↥E) hnd
  have hPb : ∀ x ∈ (P : Subgroup ↥E), E.normalizerMonoidHom ⟨b, hbE⟩ x ∈ (P : Subgroup ↥E) := by
    intro x hx
    have h := congrArg (fun Q : Sylow p ↥E => (Q : Subgroup ↥E))
      (MulAction.mem_fixedPoints.mp hP (⟨b, mem_zpowers b⟩ : ↥(zpowers b)))
    rw [Sylow.pointwise_smul_def] at h
    rw [← h]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hx, rfl⟩
  have hdisj : Disjoint (P : Subgroup ↥E) f.ker := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hk]
    exact Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpK (h.trans hker))
  have hinj : ∀ x ∈ (P : Subgroup ↥E), ∀ y ∈ (P : Subgroup ↥E), f x = f y → x = y := by
    intro x hx y hy hxy
    have hxy' : x⁻¹ * y ∈ (P : Subgroup ↥E) ⊓ f.ker :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hx) hy,
        MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hxy, inv_mul_cancel])⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hxy'
    exact inv_mul_eq_one.1 hxy'
  have hsurj : ∀ u : ↥U, ∃ x ∈ (P : Subgroup ↥E), f x = u := by
    intro u
    have hS : ((P.mapSurjective hf : Sylow p ↥U) : Subgroup ↥U) = ⊤ :=
      ((P.mapSurjective hf).is_maximal' (hUp.to_subgroup ⊤) le_top).symm
    have hu : u ∈ ((P.mapSurjective hf : Sylow p ↥U) : Subgroup ↥U) := by
      rw [hS]
      exact Subgroup.mem_top u
    rw [Sylow.coe_mapSurjective] at hu
    obtain ⟨x, hx, hxu⟩ := hu
    exact ⟨x, hx, hxu⟩
  let ρ : ↥(P : Subgroup ↥E) →* ↥U := f.comp (P : Subgroup ↥E).subtype
  have hρ : Function.Bijective ρ := by
    refine ⟨fun x y hxy => Subtype.ext (hinj x x.2 y y.2 hxy), fun u => ?_⟩
    obtain ⟨x, hx, hxu⟩ := hsurj u
    exact ⟨⟨x, hx⟩, hxu⟩
  let e : ↥(P : Subgroup ↥E) ≃* ↥U := MulEquiv.ofBijective ρ hρ
  let j : A →* ↥(P : Subgroup ↥E) := e.symm.toMonoidHom.comp ι.rangeRestrict
  have hj : ∀ a, f (j a : ↥E) = ι.rangeRestrict a := fun a => e.apply_symm_apply _
  refine ⟨E.subtype.comp ((P : Subgroup ↥E).subtype.comp j), ?_, fun a => hEL (j a : ↥E).2,
    fun a => ?_⟩
  · intro a a' h
    have h1 : (j a : ↥E) = j a' := Subtype.ext h
    have h2 : ι.rangeRestrict a = ι.rangeRestrict a' := by rw [← hj, ← hj, h1]
    exact hι (congrArg Subtype.val h2)
  ·
    have hy : E.normalizerMonoidHom ⟨b, hbE⟩ (j a : ↥E) ∈ (P : Subgroup ↥E) := hPb _ (j a).2
    have hfy : f (E.normalizerMonoidHom ⟨b, hbE⟩ (j a : ↥E)) = f (j (κ a) : ↥E) := by
      rw [hj]
      apply Subtype.ext
      change π (L.normalizerMonoidHom ⟨b, hb⟩ (Subgroup.inclusion hEL (j a : ↥E))) = ι (κ a)
      rw [← hκ]
      change inducedBarInfAutHom L ⟨b, hb⟩ (π (Subgroup.inclusion hEL (j a : ↥E))) = _
      congr 1
      exact congrArg Subtype.val (hj a)
    exact congrArg Subtype.val (hinj _ hy _ (j (κ a)).2 hfy)

theorem uc22s2114r3f_card_solvableRadical {M L : Subgroup G} (hL : L ∈ calC M) :
    Nat.card (CFSG.solvableRadical ↥L) =
      Nat.card (CFSG.pCore 2 ↥L) * Nat.card (center (Bar2 L)) := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have h1 : Nat.card ↥L = Nat.card (BarInf L) * Nat.card (CFSG.solvableRadical ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card ↥L = Nat.card (Bar2 L) * Nat.card (CFSG.pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card (Bar2 L) =
      Nat.card (Bar2 L ⧸ center (Bar2 L)) * Nat.card (center (Bar2 L)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h4 : Nat.card (BarInf L) = Nat.card (Bar2 L ⧸ center (Bar2 L)) := Nat.card_congr e.toEquiv
  have hpos : 0 < Nat.card (BarInf L) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← h1, h2, h3, h4]
  ring

theorem uc22s2114r3f_not_dvd_card_solvableRadical (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M) {m f : ℕ} (hm : m = 6 ∨ m = 7)
    (hX : LieModel (BarInf L) .PSU m 2 f) {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) :
    ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [uc22s2114r3f_card_solvableRadical hL]
  intro h
  rcases (Nat.Prime.dvd_mul hr).1 h with h2 | hZ
  · obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)).exists_card_eq
    rw [hk] at h2
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2)
    omega
  · exact uc22s2114r3u_not_dvd_card_center hGA hL hm hX hr hr7 hZ

theorem uc22s2114r3f_two_lt_card_of_fpf (hK : UCK.K47) {Mg : Type} [Group Mg] [Finite Mg]
    (hMg : CFSG.Open.IsKGroup Mg) (Q₀ : Subgroup Mg) [Q₀.Normal] (hQ₀ : IsPGroup 2 ↥Q₀)
    (hchar : centralizer (Q₀ : Set Mg) ≤ Q₀) {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hr : r.Prime) (hr2 : r ≠ 2) (hqr : q ≠ r) {A : Type} [CommGroup A] [Finite A]
    (hA : IsPGroup q A) (hAc : ¬ IsCyclic A) (κ : A →* A) (hκ : ∀ a, κ a = a → a = 1)
    (ψ : A →* Mg) (hψ : Function.Injective ψ) {b : Mg} (hbr : orderOf b = r)
    (hbψ : ∀ a, b * ψ a * b⁻¹ = ψ (κ a)) :
    2 < Nat.card ↥(Q₀ ⊓ centralizer ((zpowers b : Subgroup Mg) : Set Mg)) := by
  classical
  rw [← not_le]
  intro hfix
  let Q : Subgroup Mg := ψ.range
  have hQp : IsPGroup q ↥Q := hA.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hQab : IsMulCommutative ↥Q := ⟨⟨fun x y => by
    obtain ⟨_, a, rfl⟩ := x
    obtain ⟨_, a', rfl⟩ := y
    apply Subtype.ext
    change ψ a * ψ a' = ψ a' * ψ a
    rw [← map_mul, mul_comm, map_mul]⟩⟩
  have hbQ : b ∈ normalizer (Q : Set Mg) := by
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨a, rfl⟩ := hg
    rw [hbψ]
    exact ⟨κ a, rfl⟩
  have hDQ : zpowers b ≤ normalizer (Q : Set Mg) := Subgroup.zpowers_le.2 hbQ
  let δ : A →* A := κ / MonoidHom.id A
  have hδ : Function.Surjective δ := by
    refine Finite.injective_iff_surjective.1 ((injective_iff_map_eq_one δ).2 fun c hc => ?_)
    exact hκ c (div_eq_one.1 hc)
  have hcomm : ⁅zpowers b, Q⁆ = Q := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro d hd g hg
      rw [commutatorElement_def]
      exact Q.mul_mem ((Subgroup.mem_normalizer_iff.1 (hDQ hd) g).1 hg) (Q.inv_mem hg)
    · rintro _ ⟨a, rfl⟩
      obtain ⟨c, hca⟩ := hδ a
      have hg : ψ a = ⁅b, ψ c⁆ := by
        rw [← hca, MonoidHom.div_apply, MonoidHom.id_apply, map_div, ← hbψ, div_eq_mul_inv,
          commutatorElement_def]
      rw [hg]
      exact Subgroup.commutator_mem_commutator (mem_zpowers b) ⟨c, rfl⟩
  haveI hcyc : IsCyclic ↥Q := UC6.k47_transport_two_uc6 hK hMg Q₀ hQ₀ hchar hq hr hq2 hr2 hqr
    (zpowers b) (by rw [Nat.card_zpowers, hbr]) hfix Q hQp hQab hDQ hcomm
  exact hAc (isCyclic_of_surjective (MonoidHom.ofInjective hψ).symm.toMonoidHom
    (MulEquiv.surjective _))

theorem uc22s2114r3f_two_lt_card {D : Data G} {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hr : r.Prime) (hr2 : r ≠ 2) (hqr : q ≠ r) {A : Type} [CommGroup A] [Finite A]
    (hA : IsPGroup q A) (hAc : ¬ IsCyclic A) (κ : A →* A) (hκ : ∀ a, κ a = a → a = 1)
    (ψ : A →* G) (hψ : Function.Injective ψ) (hψM : ∀ a, ψ a ∈ D.M) {b : G} (hbM : b ∈ D.M)
    (hbr : orderOf b = r) (hbψ : ∀ a, b * ψ a * b⁻¹ = ψ (κ a)) :
    2 < Nat.card ↥(F07.Q7 D ⊓ centralizer ({b} : Set G)) := by
  let ψM : A →* ↥D.M := ψ.codRestrict D.M hψM
  have hψM' : Function.Injective ψM := fun a a' h => hψ (congrArg Subtype.val h)
  have hbMr : orderOf (⟨b, hbM⟩ : ↥D.M) = r := by
    rw [Subgroup.orderOf_mk]
    exact hbr
  have hbψM : ∀ a, (⟨b, hbM⟩ : ↥D.M) * ψM a * (⟨b, hbM⟩ : ↥D.M)⁻¹ = ψM (κ a) := fun a =>
    Subtype.ext (hbψ a)
  obtain ⟨hMg, hQ₀, hchar⟩ := UC6G.moduleData_uc6 D
  have key := uc22s2114r3f_two_lt_card_of_fpf UCK.k47 hMg _ hQ₀ hchar hq hq2 hr hr2 hqr hA hAc
    κ hκ ψM hψM' hbMr hbψM
  refine key.trans_le ?_
  have hle : (CFSG.pCore 2 ↥D.M ⊓
      centralizer ((zpowers (⟨b, hbM⟩ : ↥D.M) : Subgroup ↥D.M) : Set ↥D.M)).map D.M.subtype ≤
      F07.Q7 D ⊓ centralizer ({b} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨x, hxQ, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hxC _ (mem_zpowers _)).symm)⟩
  have h := Subgroup.card_le_of_le hle
  rwa [Subgroup.card_map_of_injective D.M.subtype_injective] at h

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
