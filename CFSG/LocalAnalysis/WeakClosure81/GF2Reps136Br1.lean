module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Sec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SectContext
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136FstarComponent
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {W : Type} [CommGroup W] [Finite W]

private theorem w136b_stab_L (L : Subgroup (MulAut W)) :
    StabPair L (Wd L) (Cd L) := by
  have hgenU : ∀ l ∈ L, ∀ u ∈ Wd L, l u ∈ Wd L := by
    intro l hl u hu
    refine Subgroup.closure_induction (p := fun u _ => l u ∈ Wd L) ?_ ?_ ?_ ?_ hu
    · rintro c ⟨x, hx, w, -, rfl⟩
      refine Subgroup.subset_closure
        ⟨l * x * l⁻¹, L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl), l w, trivial, ?_⟩
      simp [MulAut.mul_apply, map_mul, map_inv]
    · simp
    · intro a b _ _ ha hb
      rw [map_mul]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      rw [map_inv]
      exact Subgroup.inv_mem _ ha
  intro l hl
  refine ⟨hgenU l hl, fun z hz => ?_⟩
  rw [Subgroup.mem_inf] at hz ⊢
  refine ⟨hgenU l hl z hz.1, ?_⟩
  intro x hx
  have h1 : (l⁻¹ * x * l) ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
  have h2 : (l⁻¹ * x * l) z = z := hz.2 _ h1
  calc x (l z) = (x * l) z := rfl
    _ = (l * (l⁻¹ * x * l)) z := by group
    _ = l ((l⁻¹ * x * l) z) := rfl
    _ = l z := by rw [h2]

private theorem w136b_conj_inv_eq {L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : L.map (MulAut.conj t).toMonoidHom = L) :
    L.map (MulAut.conj t⁻¹).toMonoidHom = L := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ L.map (MulAut.conj t).toMonoidHom := by rw [ht]; exact hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    have : t⁻¹ * x * t = y := by
      rw [← hyx]
      simp [MulAut.conj_apply, mul_assoc]
    show t⁻¹ * x * t ∈ L
    rw [this]
    exact hy
  · intro x hx
    refine ⟨t * x * t⁻¹, ?_, ?_⟩
    · have hmem : (MulAut.conj t) x ∈ L.map (MulAut.conj t).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rwa [ht] at hmem
    · simp [MulAut.conj_apply, mul_assoc]

private theorem w136b_stab_t {L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : L.map (MulAut.conj t).toMonoidHom = L) :
    StabPair (Subgroup.zpowers t) (Wd L) (Cd L) := by
  have ht_inv := w136b_conj_inv_eq ht
  have hgenU : ∀ u ∈ Wd L, t u ∈ Wd L := by
    intro u hu
    refine Subgroup.closure_induction (p := fun u _ => t u ∈ Wd L) ?_ ?_ ?_ ?_ hu
    · rintro c ⟨x, hx, w, -, rfl⟩
      refine Subgroup.subset_closure ⟨t * x * t⁻¹, ?_, t w, trivial, ?_⟩
      · have hmem : (MulAut.conj t) x ∈ L.map (MulAut.conj t).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hx
        rwa [ht] at hmem
      · simp [MulAut.mul_apply, map_mul, map_inv]
    · simp
    · intro a b _ _ ha hb
      rw [map_mul]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      rw [map_inv]
      exact Subgroup.inv_mem _ ha
  have hgenU_inv : ∀ u ∈ Wd L, t⁻¹ u ∈ Wd L := by
    intro u hu
    refine Subgroup.closure_induction (p := fun u _ => t⁻¹ u ∈ Wd L) ?_ ?_ ?_ ?_ hu
    · rintro c ⟨x, hx, w, -, rfl⟩
      refine Subgroup.subset_closure ⟨t⁻¹ * x * t, ?_, t⁻¹ w, trivial, ?_⟩
      · have hmem : (MulAut.conj t⁻¹) x ∈ L.map (MulAut.conj t⁻¹).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hx
        rwa [ht_inv] at hmem
      · simp [MulAut.mul_apply, map_mul, map_inv]
    · simp
    · intro a b _ _ ha hb
      rw [map_mul]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      rw [map_inv]
      exact Subgroup.inv_mem _ ha
  have htU : t ∈ stabSub (Wd L) := by
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by simpa using hgenU_inv (t u) hu, hgenU u⟩
  have htZ : t ∈ stabSub (Cd L) := by
    rw [mem_stabSub]
    intro z
    constructor
    ·
      intro hz
      rw [Subgroup.mem_inf] at hz ⊢
      refine ⟨by simpa using hgenU_inv (t z) hz.1, ?_⟩
      intro x hx
      have h1 : (t * x * t⁻¹) ∈ L := by
        have hmem : (MulAut.conj t) x ∈ L.map (MulAut.conj t).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hx
        rwa [ht] at hmem
      have h2 : (t * x * t⁻¹) (t z) = t z := hz.2 _ h1
      have h4 : t (x z) = t z := by
        calc t (x z) = (t * x) z := rfl
          _ = (t * x * t⁻¹ * t) z := by group
          _ = ((t * x * t⁻¹) * t) z := by group
          _ = (t * x * t⁻¹) (t z) := rfl
          _ = t z := h2
      exact t.injective h4
    ·
      intro hz
      rw [Subgroup.mem_inf] at hz ⊢
      refine ⟨hgenU z hz.1, ?_⟩
      intro x hx
      have h1 : (t⁻¹ * x * t) ∈ L := by
        have hmem : (MulAut.conj t⁻¹) x ∈ L.map (MulAut.conj t⁻¹).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hx
        rwa [ht_inv] at hmem
      have h2 : (t⁻¹ * x * t) z = z := hz.2 _ h1
      calc x (t z) = (x * t) z := rfl
        _ = (t * (t⁻¹ * x * t)) z := by group
        _ = t ((t⁻¹ * x * t) z) := rfl
        _ = t z := by rw [h2]
  intro a ha
  exact ⟨fun u hu => (mem_stabSub.mp ((Subgroup.zpowers_le.mpr htU) ha) u).2 hu,
    fun z hz => (mem_stabSub.mp ((Subgroup.zpowers_le.mpr htZ) ha) z).2 hz⟩

private theorem w136b_mem_stabSub_of_forall_mem {U : Subgroup W} {g : MulAut W}
    (h : ∀ u ∈ U, g u ∈ U) : g ∈ stabSub U :=
  mem_stabSub_of_invariant h (inv_mem_of_forall_mem g h)

private theorem w136b_stabPair_le_stabSub_left {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) : A ≤ stabSub U :=
  fun a ha => w136b_mem_stabSub_of_forall_mem (hA a ha).1

private theorem w136b_stabPair_le_stabSub_right {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) : A ≤ stabSub Z :=
  fun a ha => w136b_mem_stabSub_of_forall_mem (hA a ha).2

private theorem w136b_stabPair_sup {A B : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) (hB : StabPair B U Z) : StabPair (A ⊔ B) U Z := fun a ha =>
  ⟨fun u hu => (mem_stabSub.mp (sup_le (w136b_stabPair_le_stabSub_left hA)
      (w136b_stabPair_le_stabSub_left hB) ha) u).2 hu,
    fun z hz => (mem_stabSub.mp (sup_le (w136b_stabPair_le_stabSub_right hA)
      (w136b_stabPair_le_stabSub_right hB) ha) z).2 hz⟩

private theorem w136b_isQuasisimple_of_open {X : Type*} [Group X]
    (h : CFSG.Open.IsQuasisimple X) : CFSG.IsQuasisimple X :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).1 h

private theorem w136b_mem_of_sq_mem_of_odd {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (hodd : Odd (orderOf x)) (hx2 : x ^ 2 ∈ H) : x ∈ H := by
  have hx : x = (x ^ 2) ^ ((orderOf x + 1) / 2) := by
    rw [← pow_mul]
    have h2 : 2 * ((orderOf x + 1) / 2) = orderOf x + 1 := by
      rw [mul_comm, Nat.div_mul_cancel]
      obtain ⟨k, hk⟩ := hodd
      exact ⟨k + 1, by omega⟩
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [hx]
  exact H.pow_mem hx2 _

private theorem w136b_exists_ne_one_fixed_of_pgroup {A : Type*} [Group A] [Finite A] {p : ℕ}
    [hp : Fact p.Prime] (hA : IsPGroup p A) (hA1 : 1 < Nat.card A)
    {Y : Subgroup (MulAut A)} (hY : IsPGroup p Y) :
    ∃ a : A, a ≠ 1 ∧ ∀ y ∈ Y, (y : MulAut A) a = a := by
  classical
  have hmod := hY.card_modEq_card_fixedPoints A
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; omega
  have hpA : Nat.card A ≡ 0 [MOD p] := by
    rw [hn, Nat.modEq_zero_iff_dvd]
    exact dvd_pow_self p hn0
  have hfix : Nat.card (MulAction.fixedPoints Y A) ≡ 0 [MOD p] := hmod.symm.trans hpA
  have h1 : (1 : A) ∈ MulAction.fixedPoints Y A := fun y => map_one (y : MulAut A)
  have hcard : 1 < Nat.card (MulAction.fixedPoints Y A) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints Y A) := Nat.card_pos_iff.mpr
      ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
    have := Nat.modEq_zero_iff_dvd.mp hfix
    have := Nat.le_of_dvd hpos this
    have := hp.out.two_le
    omega
  have := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (⟨1, h1⟩ : MulAction.fixedPoints Y A)
  exact ⟨a, fun h0 => ha1 (Subtype.ext h0), fun y hy => ha ⟨y, hy⟩⟩

private theorem w136b_eq_one_of_centralizes_irreducible {M : Type*} [CommGroup M] [Finite M]
    [Nontrivial M] (hM : ∀ m : M, m * m = 1) (L : Subgroup (MulAut M))
    (hirr : ∀ U : Subgroup M, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {z : MulAut M} (hz : ∀ g ∈ L, g * z = z * g) {k : ℕ} (hzk : z ^ (2 ^ k) = 1) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsPGroup 2 M := fun m => ⟨1, by simpa [sq] using hM m⟩
  have hA1 : 1 < Nat.card M := Finite.one_lt_card
  have hY : IsPGroup 2 (Subgroup.zpowers z) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzk, one_zpow]
  obtain ⟨a, ha1, hafix⟩ := w136b_exists_ne_one_fixed_of_pgroup hA hA1 hY
  have hUne : fixV (Subgroup.zpowers z) ≠ ⊥ := by
    intro hbot
    have : a ∈ fixV (Subgroup.zpowers z) := fun y hy => hafix y hy
    rw [hbot, Subgroup.mem_bot] at this
    exact ha1 this
  have hinv : ∀ g ∈ L, ∀ u ∈ fixV (Subgroup.zpowers z), g u ∈ fixV (Subgroup.zpowers z) := by
    intro g hg u hu
    rw [mem_fixV_zpowers_iff_apply] at hu ⊢
    have := congrArg (fun m : MulAut M => m u) (hz g hg)
    simp only [MulAut.mul_apply] at this
    rw [← this, hu]
  rcases hirr _ hinv with h0 | htop
  · exact absurd h0 hUne
  · apply MulEquiv.ext
    intro w
    have : w ∈ fixV (Subgroup.zpowers z) := by rw [htop]; exact Subgroup.mem_top w
    rw [mem_fixV_zpowers_iff_apply] at this
    simpa using this

private theorem w136b_centralizer_odd {M : Type*} [CommGroup M] [Finite M] [Nontrivial M]
    (hM : ∀ m : M, m * m = 1) (L : Subgroup (MulAut M))
    (hirr : ∀ U : Subgroup M, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    Odd (Nat.card (Subgroup.centralizer (L : Set (MulAut M)))) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have h2 : 2 ∣ Nat.card (Subgroup.centralizer (L : Set (MulAut M))) := even_iff_two_dvd.mp hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hzc : (z : MulAut M) ∈ Subgroup.centralizer (L : Set (MulAut M)) := z.2
  have hcomm : ∀ g ∈ L, g * (z : MulAut M) = (z : MulAut M) * g :=
    Subgroup.mem_centralizer_iff.mp hzc
  have hz2 : (z : MulAut M) ^ (2 ^ 1) = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    have h' := congrArg Subtype.val this
    simpa using h'
  have := w136b_eq_one_of_centralizes_irreducible hM L hirr hcomm hz2
  have hz1 : z = 1 := Subtype.ext this
  rw [hz1, orderOf_one] at hz
  omega

theorem is135_section (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (c : Ctx136 Y t L) (hf : FaithOn L (Wd L) (Cd L))
    (hirr : IsIrrOn L (Wd L) (Cd L)) :
    Is135Context (secSub (Wd L) (Cd L) (L ⊔ Subgroup.zpowers t)) (secSub (Wd L) (Cd L) L) := by
  set Lb : Subgroup (MulAut (Sect (Wd L) (Cd L))) := secSub (Wd L) (Cd L) L with hLb
  set Y1 : Subgroup (MulAut (Sect (Wd L) (Cd L))) :=
    secSub (Wd L) (Cd L) (L ⊔ Subgroup.zpowers t) with hY1
  have hZU : Cd L ≤ Wd L := inf_le_left
  have hZltU : Cd L < Wd L := hirr.1
  have hL_stab : StabPair L (Wd L) (Cd L) := w136b_stab_L L
  have ht_norm : L.map (MulAut.conj t).toMonoidHom = L := c.hfix L c.comp
  have ht_stab : StabPair (Subgroup.zpowers t) (Wd L) (Cd L) := w136b_stab_t ht_norm
  have hLY1 : Lb ≤ Y1 :=
    autSec_mono le_sup_left _ _
  have hirr_L : IsIrrOn (Lb) ⊤ ⊥ :=
    (secSub_irr hL_stab hZltU).mpr hirr
  have hntM : Nontrivial (Sect (Wd L) (Cd L)) := by
    obtain ⟨u, huU, huZ⟩ := IsConcreteLE.exists_of_lt hZltU
    refine ⟨QuotientGroup.mk ⟨u, huU⟩, 1, ?_⟩
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact huZ h
  have hM2 : ∀ m : Sect (Wd L) (Cd L), m * m = 1 := by
    intro m
    rw [← pow_two]
    exact sect_exp_two hw2 (Wd L) (Cd L) m
  have hCodd_Aut : Odd (Nat.card (Subgroup.centralizer
      (Lb : Set (MulAut (Sect (Wd L) (Cd L)))))) :=
    w136b_centralizer_odd hM2 (Lb)
      (fun U hU => hirr_L.2.2.2 U hU bot_le le_top)
  have hU : ∀ u ∈ Wd L, t u ∈ Wd L := (ht_stab t (Subgroup.mem_zpowers t)).1
  have hZ : ∀ z ∈ Cd L, t z ∈ Cd L := (ht_stab t (Subgroup.mem_zpowers t)).2
  set tbar := secAut (Wd L) (Cd L) t hU hZ with htbar
  have hY1_eq : Y1 =
      Lb ⊔ Subgroup.zpowers (tbar) := by
    rw [hY1, hLb, secSub_sup hL_stab ht_stab, secSub_zpowers hU hZ]
  have htbar_norm : (Lb).map
      (MulAut.conj (tbar)).toMonoidHom = Lb := by
    have h := secSub_map_conj hL_stab hU hZ (t := t)
    rwa [ht_norm] at h
  have htbar_norm_mem : tbar ∈ Subgroup.normalizer
      (Lb : Set (MulAut (Sect (Wd L) (Cd L)))) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr htbar_norm
  have ht2 : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rw [c.std.t2] at h
    simpa using h
  have htbar2 : (tbar) ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [pow_two, MulAut.mul_apply, secAut_mk, secAut_mk]
    have htu : t (t (u : W)) = (u : W) := by
      have h := congrArg (fun f : MulAut W => f (u : W)) ht2
      simpa [pow_two, MulAut.mul_apply] using h
    have heq : (⟨t (t (u : W)), hU (t (u : W)) (hU (u : W) u.2)⟩ : ↥(Wd L)) = u :=
      Subtype.ext htu
    exact congrArg (QuotientGroup.mk' ((Cd L).subgroupOf (Wd L))) heq
  have hCodd : Odd (Nat.card ↥(Subgroup.centralizer
      (Lb : Set (MulAut (Sect (Wd L) (Cd L)))) ⊓
      Y1)) :=
    Odd.of_dvd_nat hCodd_Aut (Subgroup.card_dvd_of_le inf_le_left)
  have hC_le : Subgroup.centralizer
      (Lb : Set (MulAut (Sect (Wd L) (Cd L)))) ⊓
      Y1 ≤ Lb := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxcen, hxY⟩ := hx
    have hxodd : Odd (orderOf x) :=
      Odd.of_dvd_nat hCodd (Subgroup.orderOf_dvd_natCard _
        (Subgroup.mem_inf.mpr ⟨hxcen, hxY⟩))
    have hx2 : x ^ 2 ∈ Lb :=
      w1369_sq_mem_of_sup_zpowers htbar2 htbar_norm_mem (by rw [← hY1_eq]; exact hxY)
    exact w136b_mem_of_sq_mem_of_odd hxodd hx2
  have hq_open : CFSG.Open.IsQuasisimple ↥(Lb) :=
    w1369_isQuasisimple_secSub_open hL_stab hf c.comp.2.2
  have hq_L : IsQuasisimple ↥(Lb) := w136b_isQuasisimple_of_open hq_open
  have hLb_normal : ((Lb).subgroupOf
      (Y1)).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    rw [hY1_eq]
    exact sup_le Subgroup.le_normalizer
      (Subgroup.zpowers_le.mpr htbar_norm_mem)
  have hZodd : Odd (Nat.card ↥((Subgroup.center ↥(Lb)).map
      (Lb).subtype)) := by
    refine Odd.of_dvd_nat hCodd_Aut (Subgroup.card_dvd_of_le ?_)
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
  have hO2 : O2Trivial Y1 :=
    w1369_o2Trivial_of_odd_centralizer hLY1 hLb_normal hq_open hZodd hCodd
  have hFstar : Fstar Y1 = Lb :=
    w1369_fstar_eq_of_centralizer_le hLY1 hLb_normal hq_open hC_le
  have hK_Y1 : IsKGroup ↥(Y1) :=
    w1369_isKGroup_secSub c.std.isK (sup_le c.comp.1 (Subgroup.zpowers_le.mpr c.std.tY))
      (w136b_stabPair_sup hL_stab ht_stab)
  exact ⟨hK_Y1, hO2, hLY1, hFstar, hq_L, hirr_L⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
