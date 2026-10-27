module

public import CFSG.LocalAnalysis.StandardType.GGSporKStepOne
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement

private def gk6_omegaOneCenter {G : Type*} [Group G] (p : ℕ) (X : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ X ∧ z ∈ Subgroup.centralizer (X : Set G) ∧ z ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haX, haC, hap⟩ ⟨hbX, hbC, hbp⟩
    refine ⟨X.mul_mem haX hbX, Subgroup.mul_mem _ haC hbC, ?_⟩
    have hcomm : Commute a b := (Subgroup.mem_centralizer_iff.mp hbC) a haX
    rw [hcomm.mul_pow, hap, hbp, one_mul]
  one_mem' := ⟨X.one_mem, Subgroup.one_mem _, one_pow p⟩
  inv_mem' := by
    rintro a ⟨haX, haC, hap⟩
    exact ⟨X.inv_mem haX, Subgroup.inv_mem _ haC, by rw [inv_pow, hap, inv_one]⟩

private theorem gk6_omegaOneCenter_le {G : Type*} [Group G] (p : ℕ) (X : Subgroup G) :
    gk6_omegaOneCenter p X ≤ X := fun _ h => h.1

private theorem gk6_isElemAbelian_omegaOneCenter {G : Type*} [Group G] (p : ℕ) (X : Subgroup G) :
    IsElemAbelian p (gk6_omegaOneCenter p X) := by
  constructor
  · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact (Subgroup.mem_centralizer_iff.mp b.2.2.1) a a.2.1
  · intro x hx
    exact hx.2.2

private theorem gk6_omegaOneCenter_ne_bot {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} (hX : IsPGroup p X) (hX1 : X ≠ ⊥) : gk6_omegaOneCenter p X ≠ ⊥ := by
  have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have hZ : Nontrivial (Subgroup.center X) := hX.center_nontrivial
  have hdvd : p ∣ Nat.card (Subgroup.center X) := by
    obtain ⟨k, hk⟩ := (hX.to_subgroup (Subgroup.center X)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center X) := Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hk] at h1 ⊢
    exact dvd_pow_self p (by rintro rfl; rw [pow_zero] at h1; exact lt_irrefl 1 h1)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) p hdvd
  intro h
  have hmem : (((z : Subgroup.center X) : X) : G) ∈ gk6_omegaOneCenter p X := by
    refine ⟨(z : X).2, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)
    · have h1 := pow_orderOf_eq_one z
      rw [hz] at h1
      simpa using congrArg (fun w : Subgroup.center X => ((w : X) : G)) h1
  rw [h, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hz1, orderOf_one] at hz
  exact (Fact.out : p.Prime).one_lt.ne hz

theorem ggSporK_pCore_eq_bot {W : Type} [Group W] [Finite W] {p : ℕ}
    (hCen : BMNoLiePComp p W) (hG1 : BMPPrimeCore p W) (hZ : BMCentreZ p W) {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat p H E) (hP' : LargeEvenPPrimeCore p ↥H = ⊥)
    (hJ : ∃ J : Subgroup W, IsComponentOf J H) : CFSG.pCore p ↥H = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hyp.1.1⟩
  by_contra hP0bot
  set P0 : Subgroup ↥H := CFSG.pCore p ↥H with hP0def
  have hP0ne : P0 ≠ ⊥ := by rwa [hP0def]
  have hP0normal : P0.Normal := CFSG.pCore_normal
  have hP0p : IsPGroup p P0 := CFSG.pCore_isPGroup
  set P0map : Subgroup W := P0.map H.subtype with hP0mapdef
  have hP0map_p : IsPGroup p P0map := hP0p.map H.subtype
  have hP0map_ne : P0map ≠ ⊥ := by
    intro h
    rw [hP0mapdef] at h
    exact hP0ne ((Subgroup.map_eq_bot_iff_of_injective P0 H.subtype_injective).mp h)
  have hHnorm : H ≤ Subgroup.normalizer (P0map : Set W) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    rw [hP0mapdef]
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨(⟨h, hh⟩ : ↥H)⁻¹ * y * ⟨h, hh⟩, ?_, ?_⟩
      · simpa [inv_inv] using hP0normal.conj_mem y hy (⟨h, hh⟩ : ↥H)⁻¹
      · rfl
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hx
      refine ⟨⟨h, hh⟩ * y * (⟨h, hh⟩ : ↥H)⁻¹, hP0normal.conj_mem y hy ⟨h, hh⟩, ?_⟩
      change h * (y : W) * h⁻¹ = x
      rw [show (y : W) = h⁻¹ * x * h from hyx]
      group
  have hEne : E ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card E = p ^ 2 := hyp.1.2.2.2.1
    rw [hbot, Subgroup.card_bot] at hcard
    have hp2 : 2 ≤ p := hyp.1.1.two_le
    have h4 : 4 ≤ p ^ 2 := by
      calc 4 = 2 * 2 := by norm_num
        _ ≤ p * p := Nat.mul_le_mul hp2 hp2
        _ = p ^ 2 := by ring
    omega
  obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEne
  have heE : (e : W) ∈ E := e.2
  have he1W : (e : W) ≠ 1 := fun h => he1 (Subtype.ext h)
  have hord : orderOf (e : W) = p := by
    have hep : (e : W) ^ p = 1 := hyp.1.2.2.1.2 (e : W) e.2
    have hdvd : orderOf (e : W) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hep
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (orderOf (e : W)) hdvd with h1 | hp
    · exact absurd h1 (by rw [orderOf_eq_one_iff]; exact he1W)
    · exact hp
  obtain ⟨hC, hnoP, hP'C, hnoComp⟩ := ggSporK_step_one hCen hG1 hyp heE he1W
  have he_norm : (e : W) ∈ Subgroup.normalizer (P0map : Set W) :=
    hHnorm (hyp.1.2.2.2.2.1 heE)
  have hzp_norm : Subgroup.zpowers (e : W) ≤ Subgroup.normalizer (P0map : Set W) :=
    Subgroup.zpowers_le.mpr he_norm
  letI : MulDistribMulAction (Subgroup.zpowers (e : W)) P0map :=
    MulDistribMulAction.compHom P0map
      (P0map.normalizerMonoidHom.comp (Subgroup.inclusion hzp_norm))
  have hact : ∀ (a : Subgroup.zpowers (e : W)) (x : P0map),
      ((a • x : P0map) : W) = (a : W) * (x : W) * (a : W)⁻¹ := fun _ _ => rfl
  have hzp_p : IsPGroup p (Subgroup.zpowers (e : W)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hord, pow_one]
  have hp_dvd_P0map : p ∣ Nat.card P0map := by
    obtain ⟨n, hn⟩ := hP0map_p.exists_card_eq
    have hnt : Nontrivial P0map := (Subgroup.nontrivial_iff_ne_bot P0map).mpr hP0map_ne
    have hgt : 1 < Nat.card P0map := Finite.one_lt_card_iff_nontrivial.mpr hnt
    rw [hn] at hgt ⊢
    exact dvd_pow_self p (by rintro rfl; rw [pow_zero] at hgt; exact lt_irrefl 1 hgt)
  have hone_fixed : (⟨1, P0map.one_mem⟩ : P0map) ∈
      MulAction.fixedPoints (Subgroup.zpowers (e : W)) P0map := fun g => smul_one g
  obtain ⟨b, hb_fixed, hb_ne⟩ :=
    hzp_p.exists_fixed_point_of_prime_dvd_card_of_fixed_point P0map hp_dvd_P0map hone_fixed
  have hb_ne' : (b : W) ≠ 1 := by
    intro hb1
    exact hb_ne (Subtype.ext hb1.symm)
  have hb_cent : (b : W) ∈ Subgroup.centralizer ({(e : W)} : Set W) := by
    have h1 : (e : W) * (b : W) * (e : W)⁻¹ = (b : W) := by
      have := congrArg (fun x : P0map => (x : W))
        (hb_fixed ⟨(e : W), Subgroup.mem_zpowers (e : W)⟩)
      simpa [hact] using this
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hX_ne : P0map ⊓ Subgroup.centralizer ({(e : W)} : Set W) ≠ ⊥ := by
    intro h
    have hb_mem : (b : W) ∈ P0map ⊓ Subgroup.centralizer ({(e : W)} : Set W) := ⟨b.2, hb_cent⟩
    rw [h, Subgroup.mem_bot] at hb_mem
    exact hb_ne' hb_mem
  set X : Subgroup W := P0map ⊓ Subgroup.centralizer ({(e : W)} : Set W) with hXdef
  have hXp : IsPGroup p X := hP0map_p.to_le inf_le_left
  set A : Subgroup W := gk6_omegaOneCenter p X with hAdef
  have hA_ne : A ≠ ⊥ := gk6_omegaOneCenter_ne_bot hXp hX_ne
  have hAelem : IsElemAbelian p A := gk6_isElemAbelian_omegaOneCenter p X
  have hAle : A ≤ Subgroup.centralizer ({(e : W)} : Set W) :=
    (gk6_omegaOneCenter_le p X).trans inf_le_right
  have hCnorm : Subgroup.centralizer ({(e : W)} : Set W) ≤ Subgroup.normalizer (X : Set W) := by
    rw [hXdef]
    exact (le_inf (hC.trans hHnorm) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hAnorm : ∀ g ∈ Subgroup.centralizer ({(e : W)} : Set W), ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    intro g hg a ha
    obtain ⟨haX, haC, hap⟩ := ha
    have hgN := hCnorm hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hgN
    have hgX : g * a * g⁻¹ ∈ X := by
      have : MulAut.conj g a ∈ X.map (MulAut.conj g) := ⟨a, haX, rfl⟩
      rwa [hgN] at this
    refine ⟨hgX, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hginvN := hCnorm (Subgroup.inv_mem _ hg)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hginvN
      have hgyX : g⁻¹ * y * g ∈ X := by
        have : MulAut.conj g⁻¹ y ∈ X.map (MulAut.conj g⁻¹) := ⟨y, hy, rfl⟩
        rw [hginvN] at this
        simpa only [MulAut.conj_apply, inv_inv] using this
      have hcomm := (Subgroup.mem_centralizer_iff.mp haC) (g⁻¹ * y * g) hgyX
      calc y * (g * a * g⁻¹) = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by group
        _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by rw [← hcomm]
        _ = (g * a * g⁻¹) * y := by group
    · rw [conj_pow, hap, mul_one, mul_inv_cancel]
  have hA_le_zp : A ≤ Subgroup.zpowers (e : W) :=
    hZ (e : W) hord hnoP A hAle hAnorm hAelem
  have hcardA : Nat.card A = p := by
    have hdvd : Nat.card A ∣ p := by
      have := Subgroup.card_dvd_of_le hA_le_zp
      rwa [Nat.card_zpowers, hord] at this
    have hA_nt : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA_ne
    have hA_gt1 : 1 < Nat.card A := Finite.one_lt_card_iff_nontrivial.mpr hA_nt
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (Nat.card A) hdvd with h1 | hp
    · exact absurd h1 hA_gt1.ne'
    · exact hp
  have hA_eq : A = Subgroup.zpowers (e : W) := by
    apply Subgroup.eq_of_le_of_card_ge hA_le_zp
    rw [Nat.card_zpowers, hord]
    exact le_of_eq hcardA.symm
  have he_A : (e : W) ∈ A := by rw [hA_eq]; exact Subgroup.mem_zpowers (e : W)
  have he_P0map : (e : W) ∈ P0map := by
    have h1 := gk6_omegaOneCenter_le p X he_A
    rw [hXdef] at h1
    exact (Subgroup.mem_inf.mp h1).1
  obtain ⟨J, hJcomp⟩ := hJ
  have hJH : J ≤ H := hJcomp.1
  have hP0solv : Group.IsSolvable P0 := by
    haveI : Group.IsNilpotent P0 := hP0p.isNilpotent
    infer_instance
  have hJq : CFSG.IsQuasisimple (J.subgroupOf H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJH).symm
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).mp
        hJcomp.2.2)
  have hJcompN : CFSG.IsComponent (J.subgroupOf H) :=
    ⟨hJq, hJcomp.2.1.subgroupOf⟩
  have hcomm : ⁅J.subgroupOf H, P0⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hP0solv hP0normal.isSubnormal).1
      (J.subgroupOf H) hJcompN
  have hJcentral : J ≤ Subgroup.centralizer (P0map : Set W) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := hy
    have hj' : (⟨j, hJH hj⟩ : ↥H) ∈ J.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]; exact hj
    have h1 : ⁅(⟨j, hJH hj⟩ : ↥H), y'⁆ ∈ ⁅J.subgroupOf H, P0⁆ :=
      Subgroup.commutator_mem_commutator hj' hy'
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact (congrArg Subtype.val h1).symm
  have hJ_cent_e : J ≤ Subgroup.centralizer ({(e : W)} : Set W) := by
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (hJcentral hj)) (e : W) he_P0map).symm
  have hJcomp' : IsComponentOf J (Subgroup.centralizer ({(e : W)} : Set W)) :=
    hJcomp.of_le_of_le hJ_cent_e hC
  exact hnoComp J hJcomp'

end CFSG.StandardType.SporadicShape
