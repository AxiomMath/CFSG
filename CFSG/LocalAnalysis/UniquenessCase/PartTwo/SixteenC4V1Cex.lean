module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Bad
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1CexA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4OutBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16c4v1_cex_inv (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D)
    (hr : (6 : ℕ∞) ≤ rMV D.M V) {g : G} (hg : s16c4v1_Cex D V g) : s16c4v1_Cex D V g⁻¹ := by
  have h1217 := hstd.r1217
  have hVn := S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer
  have hA2 : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hEN : barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g) ≤
      Subgroup.normalizer (lBar (v1Sub D.M ⊥ V hV L) V hV L :
        Set (MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV))) := by
    intro φ hφ
    obtain ⟨a, haA, rfl⟩ := (mem_barSub _ V hV _ φ).1 hφ
    exact Sixteen24.actTil_v1Sub_mem_normalizer D h1217 S.sect.setting.hyp151 hV (hg.1 haA)
      (by rw [Sixteen24.nBar_eq_of_uFrame D S.sect.setting.hyp151 hV S.F]; exact hg.1 haA)
      (s16c4v1_mem_stabTil S (hg.1 haA))
  have hE2 : IsElemAbelian2 (barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g)) :=
    isElemAbelian2_barSub hV hA2
  have hcardE : Nat.card (barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g)) ≤ 2 ^ 4 :=
    S.F.s16c4_card_le_sixteen hEN hE2
  have hrel : (Subgroup.centralizer (V : Set G)).relIndex (conjSubgroup V g) ≤ 16 := by
    rw [← s16c4v1_cxh_card_barSub S h1217 hg.1]
    exact hcardE
  have hmq4 : E3.mQuot (conjSubgroup V g) (Subgroup.centralizer (V : Set G)) ≤ 4 := by
    have h := E3.relIndex_eq_two_pow hA2.isPGroup
      (Subgroup.centralizer (V : Set G))
    rw [h, show (16 : ℕ) = 2 ^ 4 by norm_num] at hrel
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hrel
  have hkey : ∀ u ∈ V, g * u * g⁻¹ ∈ D.M := by
    intro u hu
    let C : Subgroup G := conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G)
    let U : Subgroup G := conjSubgroup C g⁻¹
    have hUV : U ≤ V := by
      have h1 : conjSubgroup C g⁻¹ ≤ conjSubgroup (conjSubgroup V g) g⁻¹ :=
        E3.conjSubgroup_mono_left g⁻¹ inf_le_left
      rwa [E3.conjSubgroup_conj_inv] at h1
    have hVU : E3.mQuot V U = E3.mQuot (conjSubgroup V g) C := by
      conv_lhs => rw [show V = conjSubgroup (conjSubgroup V g) g⁻¹ from
        (E3.conjSubgroup_conj_inv V g).symm]
      exact E3.mQuot_conjSubgroup (conjSubgroup V g) C g⁻¹
    have hCS : conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G) ≤ C :=
      le_inf inf_le_left (inf_le_right.trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hu)))
    have hmC : E3.mQuot (conjSubgroup V g) C ≤
        E3.mQuot (conjSubgroup V g)
          (conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) :=
      E3.mQuot_mono hCS
    have hmCeq : E3.mQuot (conjSubgroup V g)
        (conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) =
        E3.mQuot (conjSubgroup V g) (Subgroup.centralizer (V : Set G)) := by
      simp only [E3.mQuot, Subgroup.inf_relIndex_left]
    have hmU : E3.mQuot V U ≤ 4 :=
      hVU.trans_le ((hmC.trans hmCeq.le).trans hmq4)
    have hlt : (E3.mQuot V U : ℕ∞) < rMV D.M V :=
      lt_of_le_of_lt (by exact_mod_cast hmU)
        (lt_of_lt_of_le (by norm_num : (4 : ℕ∞) < 6) hr)
    have hcentU := CFSG.LocalAnalysis.WeakClosure81.centralizer_le_of_mQuot_lt_rMV hUV hlt
    have hu_cent : u ∈ Subgroup.centralizer (C : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 u
        (Set.mem_singleton u)).symm
    have hgu : g * u * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
      have h1 : g * u * g⁻¹ ∈ conjSubgroup (Subgroup.centralizer (C : Set G)) g⁻¹ := by
        refine (mem_conjSubgroup_iff).2 ?_
        show g⁻¹ * (g * u * g⁻¹) * (g⁻¹)⁻¹ ∈ Subgroup.centralizer (C : Set G)
        have h2 : g⁻¹ * (g * u * g⁻¹) * (g⁻¹)⁻¹ = u := by group
        rw [h2]
        exact hu_cent
      rwa [E3.conjSubgroup_centralizer C g⁻¹] at h1
    exact hcentU hgu
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxu : g⁻¹ * x * g ∈ V := by
      simpa using (mem_conjSubgroup_iff).1 hx
    have h1 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [h1]
    exact hkey (g⁻¹ * x * g) hxu
  · intro hbot
    apply hg.2
    have h := E3.conjSubgroup_commutator V (conjSubgroup V g⁻¹) g
    rw [hbot, E3.conjSubgroup_bot, conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one] at h
    rw [Subgroup.commutator_comm]
    exact h.symm

theorem s16c4v1_cex_comm_le (hVn : D.M ≤ Subgroup.normalizer (V : Set G)) {g : G}
    (hA : conjSubgroup V g ≤ D.M) (hA' : conjSubgroup V g⁻¹ ≤ D.M) :
    ⁅V, conjSubgroup V g⁆ ≤ V ⊓ conjSubgroup V g := by
  rw [Subgroup.commutator_le]
  intro v hv a ha
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    have h1 : a * v⁻¹ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hVn (hA ha)) v⁻¹).1 (V.inv_mem hv)
    rw [show v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) by group]
    exact V.mul_mem hv h1
  · rw [commutatorElement_def]
    have h1 : v * a * v⁻¹ ∈ conjSubgroup V g :=
      s16c4v1_cxh_conj_mem_of_conj_le hVn hA' hv ha
    exact (conjSubgroup V g).mul_mem h1 ((conjSubgroup V g).inv_mem ha)

theorem s16c4v1_cex_cent_V1 (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {g : G}
    (hg : s16c4v1_Cex D V g) (hg' : s16c4v1_Cex D V g⁻¹) :
    ∀ a ∈ conjSubgroup V g, ∀ x ∈ v1Sub D.M ⊥ V hV L, a * x * a⁻¹ = x := by
  intro a ha x hx
  have hVn := S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer
  have hxV : x ∈ V := s16c4v1_v1_le S hx
  have hcV1 : a * x * a⁻¹ * x⁻¹ ∈ v1Sub D.M ⊥ V hV L := by
    have h1 := s16c4v1_conj_mem_v1 S (hg.1 ha) hx
    exact (v1Sub D.M ⊥ V hV L).mul_mem h1 ((v1Sub D.M ⊥ V hV L).inv_mem hx)
  have hcA : a * x * a⁻¹ * x⁻¹ ∈ conjSubgroup V g := by
    have h1 : x * a⁻¹ * x⁻¹ ∈ conjSubgroup V g :=
      s16c4v1_cxh_conj_mem_of_conj_le hVn hg'.1 hxV ((conjSubgroup V g).inv_mem ha)
    have h2 : a * (x * a⁻¹ * x⁻¹) ∈ conjSubgroup V g :=
      (conjSubgroup V g).mul_mem ha h1
    rwa [show a * (x * a⁻¹ * x⁻¹) = a * x * a⁻¹ * x⁻¹ by group] at h2
  have hc1 : a * x * a⁻¹ * x⁻¹ = 1 := by
    by_contra hne
    have hcV : a * x * a⁻¹ * x⁻¹ ∈ V := s16c4v1_v1_le S hcV1
    have hbad := (s16c4v1_bad_of_mem_inf S hstd (s16c4v1_cxh_not_mem S hg) hcV hne
      ((mem_conjSubgroup_iff).1 hcA)).1
    have hsing := (s16c4v1_bad_sing S hstd hcV hne hbad).1
    exact hsing ((s16c4v1_vec_eq_zero_iff S hcV).2 hcV1)
  exact mul_inv_eq_one.1 hc1

theorem s16c4v1_cex_D_sing (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {g : G}
    (hg : s16c4v1_Cex D V g) (hg' : s16c4v1_Cex D V g⁻¹) :
    ∀ d ∈ ⁅V, conjSubgroup V g⁆, d ≠ 1 →
      s16c4v1_vec S d ≠ 0 ∧ herm S.F.σ (s16c4v1_vec S d) (s16c4v1_vec S d) = 0 := by
  intro d hd hd1
  have hVn := S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer
  have hdle : d ∈ V ⊓ conjSubgroup V g :=
    s16c4v1_cex_comm_le hVn hg.1 hg'.1 hd
  have hdV : d ∈ V := (Subgroup.mem_inf.1 hdle).1
  have hdA : d ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hdle).2
  exact s16c4v1_bad_sing S hstd hdV hd1
    ((s16c4v1_bad_of_mem_inf S hstd (s16c4v1_cxh_not_mem S hg) hdV hd1
      ((mem_conjSubgroup_iff).1 hdA)).1)

theorem s16c4v1_cex_D_subspace (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) {g : G} (hg : s16c4v1_Cex D V g)
    (hg' : s16c4v1_Cex D V g⁻¹) :
    ∃ P : Submodule S.F.K (Fin 4 → S.F.K),
      (∀ d ∈ ⁅V, conjSubgroup V g⁆, s16c4v1_vec S d ∈ P) ∧
      (∀ x ∈ P, ∃ d ∈ ⁅V, conjSubgroup V g⁆, s16c4v1_vec S d = x) ∧
      (∀ x ∈ P, herm S.F.σ x x = 0) ∧
      Nat.card (⁅V, conjSubgroup V g⁆ : Subgroup G) = Nat.card P := by
  classical
  have h1217 := hstd.r1217
  have hVn := S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer
  let D : Subgroup G := ⁅V, conjSubgroup V g⁆
  have hDV : D ≤ V := (s16c4v1_cex_comm_le hVn hg.1 hg'.1).trans inf_le_left
  have hspanω : ∀ c : S.F.K, c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω ^ 2 := by
    haveI : Fintype S.F.K := Fintype.ofFinite S.F.K
    intro c
    have hc : c ∈ ({0, 1, ω, ω ^ 2} : Finset S.F.K) := by
      rw [← TauCeti.univ_eq_zero_one_root_sq (F := S.F.K) S.F.card_K
        (s16c4v1_scalar_cube S hz)]
      exact Finset.mem_univ c
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
  have hzD' : ⁅conjSubgroup V g, V⁆ ≤
      (⁅conjSubgroup V g, V⁆).comap (MulAut.conj z).toMonoidHom := by
    rw [Subgroup.commutator_def]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨a, ha, v, hv, rfl⟩
    change z * ⁅a, v⁆ * z⁻¹ ∈ ⁅conjSubgroup V g, V⁆
    have halin : s16c4v1_Lin S a :=
      s16c4v1_lin_of_cent_V1 S h1217 hz (hg.1 ha)
        (s16c4v1_cex_cent_V1 S hstd hg hg' a ha)
    have hcomm := s16c4v1_commute_of_lin S h1217 hz (hg.1 ha) halin v hv
    have hzv : z * v * z⁻¹ ∈ V := s16c4v1_conj_mem S hz.1 hv
    have key : z * ⁅a, v⁆ * z⁻¹ = ⁅a, z * v * z⁻¹⁆ := by
      simp only [commutatorElement_def]
      rw [hcomm]
      group
    rw [key]
    exact Subgroup.commutator_mem_commutator ha hzv
  have hzD : ∀ d ∈ D, z * d * z⁻¹ ∈ D := by
    intro d hd
    rw [show D = ⁅conjSubgroup V g, V⁆ from Subgroup.commutator_comm V (conjSubgroup V g)]
      at hd ⊢
    exact hzD' hd
  let P : Submodule S.F.K (Fin 4 → S.F.K) :=
    { carrier := {x | ∃ d ∈ D, s16c4v1_vec S d = x}
      zero_mem' := ⟨1, D.one_mem, s16c4v1_vec_one S⟩
      add_mem' := by
        rintro x y ⟨d, hd, rfl⟩ ⟨e, he, rfl⟩
        exact ⟨d * e, D.mul_mem hd he, s16c4v1_vec_mul S (hDV hd) (hDV he)⟩
      smul_mem' := by
        intro c x hx
        obtain ⟨d, hd, rfl⟩ := hx
        rcases hspanω c with hc | hc | hc | hc
        · rw [hc]
          exact ⟨1, D.one_mem, by rw [s16c4v1_vec_one, zero_smul]⟩
        · rw [hc, one_smul]
          exact ⟨d, hd, rfl⟩
        · rw [hc]
          exact ⟨z * d * z⁻¹, hzD d hd, hz.2.2 d (hDV hd)⟩
        · rw [hc]
          refine ⟨z * (z * d * z⁻¹) * z⁻¹, hzD _ (hzD d hd), ?_⟩
          rw [hz.2.2 _ (hDV (hzD d hd)), hz.2.2 d (hDV hd), smul_smul, ← sq] }
  have hmem1 : ∀ d ∈ D, s16c4v1_vec S d ∈ P := fun d hd => ⟨d, hd, rfl⟩
  have hmem2 : ∀ x ∈ P, ∃ d ∈ D, s16c4v1_vec S d = x := fun x hx => hx
  have hsing : ∀ x ∈ P, herm S.F.σ x x = 0 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := hx
    by_cases hd1 : d = 1
    · rw [hd1, s16c4v1_vec_one]
      simp
    · exact (s16c4v1_cex_D_sing S hstd hg hg' d hd hd1).2
  let f : ↥D → ↥P := fun d => ⟨s16c4v1_vec S d, hmem1 d d.2⟩
  have hf_inj : Function.Injective f := by
    intro d₁ d₂ h
    have hvec : s16c4v1_vec S (d₁ : G) = s16c4v1_vec S (d₂ : G) :=
      Subtype.ext_iff.mp h
    apply Subtype.ext
    by_contra hne
    have hmul : (d₁ : G) * (d₂ : G)⁻¹ ∈ D := D.mul_mem d₁.2 (D.inv_mem d₂.2)
    have hne' : (d₁ : G) * (d₂ : G)⁻¹ ≠ 1 := fun h1 => hne (mul_inv_eq_one.1 h1)
    have hsing' := (s16c4v1_cex_D_sing S hstd hg hg' _ hmul hne').1
    apply hsing'
    have hv2 : (d₂ : G)⁻¹ = (d₂ : G) :=
      mul_eq_one_iff_inv_eq.1 (by simpa [pow_two] using hV.2 (d₂ : G) (hDV d₂.2))
    calc s16c4v1_vec S ((d₁ : G) * (d₂ : G)⁻¹)
        = s16c4v1_vec S (d₁ : G) + s16c4v1_vec S ((d₂ : G)⁻¹) :=
          s16c4v1_vec_mul S (hDV d₁.2) (V.inv_mem (hDV d₂.2))
      _ = s16c4v1_vec S (d₂ : G) + s16c4v1_vec S (d₂ : G) := by rw [hvec, hv2]
      _ = 0 := by
          haveI : CharP S.F.K 2 :=
            CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero S.F.two_eq_zero
          exact CharTwo.add_self_eq_zero _
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨d, hd, hdx⟩ := x.2
    exact ⟨⟨d, hd⟩, Subtype.ext hdx⟩
  refine ⟨P, hmem1, hmem2, hsing, ?_⟩
  exact Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)

theorem s16c4v1_cex_D_card (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) {g : G} (hg : s16c4v1_Cex D V g)
    (hg' : s16c4v1_Cex D V g⁻¹) :
    Nat.card (⁅V, conjSubgroup V g⁆ : Subgroup G) = 4 ∨
      Nat.card (⁅V, conjSubgroup V g⁆ : Subgroup G) = 16 := by
  obtain ⟨P, -, -, hsing, hcard⟩ := s16c4v1_cex_D_subspace S hstd hz hg hg'
  have hle : Module.finrank S.F.K P ≤ 2 :=
    (s16c4v1_isotropic S.F.σ S.F.card_K S.F.isUnitary P hsing).2
  have hpow : Nat.card P = 4 ^ Module.finrank S.F.K P := by
    rw [Module.natCard_eq_pow_finrank (K := S.F.K), S.F.card_K]
  have hne : Module.finrank S.F.K P ≠ 0 := by
    intro h0
    have h1 : Nat.card P = 1 := by rw [hpow, h0, pow_zero]
    exact hg.2 (Subgroup.eq_bot_of_card_eq _ (by rw [hcard, h1]))
  rw [hcard, hpow]
  have h12 : Module.finrank S.F.K P = 1 ∨ Module.finrank S.F.K P = 2 := by omega
  rcases h12 with h | h
  · left
    rw [h, pow_one]
  · right
    rw [h]
    norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
