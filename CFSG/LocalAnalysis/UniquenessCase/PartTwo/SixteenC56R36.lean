module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R34
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_of_forall_actTil_mem_imgTil {V U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hUV : U ≤ V) {g : G} (hgs : g ∈ stabTil ⊥ V)
    (hmap : ∀ w ∈ imgTil ⊥ V hV U, actTil ⊥ V hV ⟨g, hgs⟩ w ∈ imgTil ⊥ V hV U) :
    g ∈ normalizer (U : Set G) := by
  have hconj : ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro u hu
    have huV : u ∈ V := hUV hu
    have hw : mkTil ⊥ V hV (IntMod.mk hV ⟨u, huV⟩) ∈ imgTil ⊥ V hV U :=
      (mem_imgTil ⊥ V hV U _).2 ⟨IntMod.mk hV ⟨u, huV⟩, hu, rfl⟩
    have h1 := hmap _ hw
    rw [actTil_mk] at h1
    obtain ⟨y, hyU, hy⟩ := (mem_imgTil ⊥ V hV U _).1 h1
    have h2 := (mkTil_eq_iff ⊥ V hV y
      (actStab ⊥ V hV ⟨g, hgs⟩ (IntMod.mk hV ⟨u, huV⟩))).1 hy
    rw [actStab_apply_val, Subgroup.mem_bot, mul_inv_eq_one] at h2
    have h2' : y.val = g * u * g⁻¹ := by
      rwa [show (IntMod.mk hV ⟨u, huV⟩).val = u from rfl] at h2
    rw [← h2']
    exact hyU
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hconj x hx
  · intro hx
    let c : ↥U → ↥U := fun u => ⟨g * (u : G) * g⁻¹, hconj u u.2⟩
    have hc : Function.Injective c := by
      intro a b hab
      apply Subtype.ext
      have h : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val hab
      exact mul_left_cancel (mul_right_cancel h)
    obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hc) ⟨g * x * g⁻¹, hx⟩
    have h2 : (w : G) = x := by
      have h3 : g * (w : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hw
      exact mul_left_cancel (mul_right_cancel h3)
    rw [← h2]
    exact w.2

theorem exists_noncyclic_normalizer_of_perfect_bar (D : Data G) {p : ℕ} (hpp : p.Prime)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (hP : PairFacts D.M ⊥ V) {U : Subgroup G}
    (hUV : U ≤ V) {P₀ : Subgroup (MulAut (Vtil ⊥ V hV))} (hP₀ : P₀ ≤ Mbar D.M ⊥ V hV)
    (hperf : Group.IsPerfect P₀) (hpP₀ : p ∣ Nat.card P₀)
    (hstab : ∀ h ∈ P₀, ∀ w ∈ imgTil ⊥ V hV U, h w ∈ imgTil ⊥ V hV U)
    (hpker : p ∣ Nat.card (F11.CTilde D.M ⊥ V)) :
    ∃ X : Subgroup G, X ≤ D.M ⊓ normalizer (U : Set G) ∧ IsPGroup p X ∧ ¬ IsCyclic X := by
  classical
  haveI : Fact p.Prime := ⟨hpp⟩
  let N : Subgroup G := D.M ⊓ normalizer (U : Set G)
  have hNst : N ≤ stabTil ⊥ V :=
    le_stabTil (inf_le_left.trans hP.le_normalizer) (inf_le_left.trans hP.le_normalizer₀)
  let ψ : ↥N →* MulAut (Vtil ⊥ V hV) :=
    (actTil ⊥ V hV).comp (Subgroup.inclusion hNst)
  have hCTle : F11.CTilde D.M ⊥ V ≤ N := by
    intro g hg
    obtain ⟨hgM, hgs, h1⟩ := (mem_cTilde_iff hV hP.le_normalizer).1 hg
    refine Subgroup.mem_inf.2 ⟨hgM, ?_⟩
    have hfix : ∀ v ∈ V, g * v * g⁻¹ = v := by
      intro v hv
      have h3 := (actTil_eq_one_iff ⊥ V hV ⟨g, hgs⟩).1 h1 v hv
      rwa [Subgroup.mem_bot, mul_inv_eq_one] at h3
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hfix x (hUV hx)]
      exact hx
    · intro hx
      have hxv : x ∈ V := by
        have h3 := (Subgroup.mem_normalizer_iff''.1 (Subgroup.mem_inf.1 hgs).1
          (g * x * g⁻¹)).1 (hUV hx)
        rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h3
      rw [← hfix x hxv]
      exact hx
  have hPR : P₀ ≤ ψ.range := by
    intro h hh
    obtain ⟨g, hgM, hgact⟩ := (mem_barSub ⊥ V hV D.M h).1 (hP₀ hh)
    have hmap : ∀ w ∈ imgTil ⊥ V hV U, actTil ⊥ V hV g w ∈ imgTil ⊥ V hV U := by
      intro w hw
      rw [hgact]
      exact hstab h hh w hw
    have hgnorm : (g : G) ∈ normalizer (U : Set G) :=
      mem_normalizer_of_forall_actTil_mem_imgTil hV hUV g.2 hmap
    rw [MonoidHom.mem_range]
    refine ⟨⟨(g : G), Subgroup.mem_inf.2 ⟨hgM, hgnorm⟩⟩, ?_⟩
    have hx : (Subgroup.inclusion hNst
        (⟨(g : G), Subgroup.mem_inf.2 ⟨hgM, hgnorm⟩⟩ : ↥N) : stabTil ⊥ V) = g :=
      Subtype.ext rfl
    show actTil ⊥ V hV (Subgroup.inclusion hNst
      (⟨(g : G), Subgroup.mem_inf.2 ⟨hgM, hgnorm⟩⟩ : ↥N)) = h
    rw [hx]
    exact hgact
  haveI : Group.IsPerfect ↥P₀ := hperf
  have hker_eq : (ψ.rangeRestrict).ker = (F11.CTilde D.M ⊥ V).subgroupOf N := by
    rw [MonoidHom.ker_rangeRestrict]
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cTilde_iff hV hP.le_normalizer]
    constructor
    · intro hc
      refine ⟨c.2.1, hNst c.2, ?_⟩
      have hc' : actTil ⊥ V hV (Subgroup.inclusion hNst c) = 1 := by
        simpa [ψ] using hc
      have he : Subgroup.inclusion hNst c = (⟨(c : G), hNst c.2⟩ : stabTil ⊥ V) :=
        Subtype.ext rfl
      rwa [he] at hc'
    · rintro ⟨-, h, h1⟩
      change actTil ⊥ V hV (Subgroup.inclusion hNst c) = 1
      have he : Subgroup.inclusion hNst c = (⟨(c : G), h⟩ : stabTil ⊥ V) := Subtype.ext rfl
      rw [he]
      exact h1
  have hpker' : p ∣ Nat.card ↥(ψ.rangeRestrict).ker := by
    have hcard : Nat.card ↥(ψ.rangeRestrict).ker = Nat.card (F11.CTilde D.M ⊥ V) := by
      rw [hker_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCTle).toEquiv
    rw [hcard]
    exact hpker
  have hperfP' : Group.IsPerfect ↥(P₀.subgroupOf ψ.range) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hPR).symm.toMonoidHom) (MulEquiv.surjective _)
  have hcardP' : Nat.card ↥(P₀.subgroupOf ψ.range) = Nat.card P₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv
  have hpP' : p ∣ Nat.card ↥(P₀.subgroupOf ψ.range) := hcardP'.symm ▸ hpP₀
  obtain ⟨X₀, hX₀p, hX₀c⟩ :=
    exists_noncyclic_pGroup_of_perfect_section ψ.rangeRestrict ψ.rangeRestrict_surjective
      hperfP' hpP' hpker'
  refine ⟨X₀.map N.subtype, ?_, hX₀p.map N.subtype, ?_⟩
  · rintro - ⟨c, -, rfl⟩
    exact c.2
  · exact SpLift.not_isCyclic_map N.subtype (Subgroup.subtype_injective N) hX₀c

private theorem r36_mul_self_eq_one {W : Type} [CommGroup W] (S : OmegaModel W) (w : W) :
    w * w = 1 := by
  apply S.vec_injective
  rw [S.vec_mul, S.vec_one]
  exact CharTwo.add_self_eq_zero (S.vec w)

theorem r16_36_holds (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D) :
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV → ∀ m : ℕ,
      Case1633 D V₀ V hV L m → V₀ = ⊥ → m = 2 → (4 : ℕ∞) < rMV D.M V := by
  intro V₀ V L hV hS m hm hV0 hm2
  subst hV0
  subst hm2
  obtain ⟨S, hSω, hSK⟩ := exists_omegaModel_of_case1633 hm
  have hsig : D.sig = {5} := by
    rcases hm with ⟨hc, -⟩ | ⟨-, h⟩
    · exact hc.2.2
    · omega
  have hH125 : Hyp125 D ⊥ V := hS.setting.hyp16.hyp125
  have hP : PairFacts D.M ⊥ V := hH125.pairFacts
  have hW2 : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := fun w => by
    rw [pow_two]
    exact r36_mul_self_eq_one S w
  have hsig5 : 5 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 5
  have hb : ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ D.M →
      rk ↥(imgTil ⊥ V hV U) ≤ 3 := by
    intro U hUV hUC
    by_contra hrk
    have hrk4 : 4 ≤ rk ↥(imgTil ⊥ V hV U) := by omega
    have hsing : ∀ u ∈ imgTil ⊥ V hV U, S.Q u = 0 := by
      intro u hu
      obtain ⟨x, hxU, rfl⟩ := (mem_imgTil ⊥ V hV U u).1 hu
      by_contra hne
      exact hUC ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)).trans
        (r16_34_coord D h61 hext h5 hS hm S hSω hSK hsig hne).2)
    have hcard : Nat.card S.K ^ 2 ≤ Nat.card (imgTil ⊥ V hV U) := by
      rw [card_eq_two_pow hW2 (imgTil ⊥ V hV U), hSK]
      calc (2 ^ 2) ^ 2 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ rk ↥(imgTil ⊥ V hV U) := Nat.pow_le_pow_right (by norm_num) hrk4
    obtain ⟨P₀, hP₀le, hperf, hcardP, hstab⟩ :=
      S.exists_perfect_normalizing_of_totallySingular hsing hcard
    have hP₀ : P₀ ≤ Mbar D.M ⊥ V hV :=
      hP₀le.trans (S.omega0_le_omega.trans
        (hSω ▸ barSub_mono ⊥ V hV hS.setting.hyp151.le))
    have hp5 : 5 ∣ Nat.card P₀ := by
      rw [hcardP, hSK]
      norm_num
    have hker := dvd_card_cTilde_of_case1633 D hext h5 hS hm S hSK hsig
    obtain ⟨X, hXle, hXp, hXc⟩ := exists_noncyclic_normalizer_of_perfect_bar D (by norm_num) hV hP
      hUV hP₀ hperf hp5 hstab hker
    have hU2 : IsPGroup 2 U := hV.isPGroup.to_le hUV
    have hU1 : U ≠ ⊥ := by
      rintro rfl
      have : imgTil ⊥ V hV (⊥ : Subgroup G) = ⊥ := by
        ext q
        rw [mem_imgTil, Subgroup.mem_bot]
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [Subgroup.mem_bot] at hx
          have : x = 1 := IntMod.val_injective hx
          rw [this, map_one]
        · rintro rfl
          exact ⟨1, Subgroup.one_mem _, map_one _⟩
      rw [this, rk_bot] at hrk4
      omega
    have hN : normalizer (U : Set G) ≤ D.M :=
      normalizer_le_of_noncyclic D h61 hsig5 (hXle.trans inf_le_left) hXp hXc hU1 hU2
        (hXle.trans inf_le_right)
    exact hUC ((Subgroup.centralizer_le_normalizer _).trans hN)
  have hrk8 : mSub V = 8 := by
    have h1 := rk_top_vtil_add_mSub ⊥ V hV bot_le
    rw [rk_top, rk, S.card_eq, hSK] at h1
    have h0 : mSub (⊥ : Subgroup G) = 0 := rk_bot
    rw [h0] at h1
    have h2 : padicValNat 2 ((2 ^ 2) ^ 4) = 8 := by
      rw [← pow_mul, padicValNat.prime_pow]
    omega
  have h5le : ((5 : ℕ) : ℕ∞) ≤ rMV D.M V :=
    le_rMV_of_forall_rk_imgTil_le D hH125 (b := 3) (c := 5) (by omega) hb
  exact lt_of_lt_of_le (by norm_num) h5le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
