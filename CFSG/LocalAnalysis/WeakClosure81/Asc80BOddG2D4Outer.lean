module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddInner
import CFSG.GroupTheory.ConjNormalFaithful
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FD4
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2Three
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddG23
import CFSG.ClassicalInvolution.Uniform.U9G2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2L0
import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
import CFSG.LocalAnalysis.SeitzReduction.F4PilotZStar
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2OutInv
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KNG2Out
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87D4Out

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.RankThree.PartTwo.KFacts
  CFSG.Blueprint.Chevalley CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.LieType.Ree (ReeTag)

open CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

theorem iSup_centralizer_eq_of_conj_centralizer_sup {G : Type} [Group G] (L E : Subgroup G)
    {u x h : G} (huE : u ∈ E) (hu1 : u ≠ 1) (hxE : x ∈ E) (hx1 : x ≠ 1) (hhL : h ∈ L)
    (hhx : h * x = x * h)
    (hgen : L ⊓ centralizer ({u} : Set G) ⊔ L ⊓ centralizer ({h * u * h⁻¹} : Set G) = L) :
    (⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G)) = L := by
  have hhC : h ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hhx
  let N : Subgroup G := L ⊓ centralizer ({u} : Set G) ⊔ L ⊓ centralizer ({x} : Set G)
  have hhN : h ∈ N := Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hhL, hhC⟩)
  have hle : L ⊓ centralizer ({u} : Set G) ⊔
      L ⊓ centralizer ({h * u * h⁻¹} : Set G) ≤ N := by
    refine sup_le le_sup_left ?_
    rintro y ⟨hyL, hyC⟩
    have hconj : h⁻¹ * y * h ∈ L ⊓ centralizer ({u} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact L.mul_mem (L.mul_mem (L.inv_mem hhL) hyL) hhL
      · have hcomm : y * (h * u * h⁻¹) = (h * u * h⁻¹) * y :=
          Subgroup.mem_centralizer_singleton_iff.mp hyC
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (h⁻¹ * y * h) * u = h⁻¹ * (y * (h * u * h⁻¹)) * h := by group
          _ = h⁻¹ * ((h * u * h⁻¹) * y) * h := by rw [hcomm]
          _ = u * (h⁻¹ * y * h) := by group
    have hy : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
    rw [hy]
    exact N.mul_mem (N.mul_mem hhN (Subgroup.mem_sup_left hconj)) (N.inv_mem hhN)
  have hLM : L ≤ N := by rw [← hgen]; exact hle
  have hMS : N ≤ ⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G) :=
    sup_le (le_iSup₂_of_le u huE (le_iSup_of_le hu1 le_rfl))
      (le_iSup₂_of_le x hxE (le_iSup_of_le hx1 le_rfl))
  exact le_antisymm (iSup₂_le fun e _ => iSup_le fun _ => inf_le_left) (hLM.trans hMS)

theorem exists_ne_one_mem_range_conj_of_four {Y M : Type} [Group Y] [Group M] [IsCyclic M]
    (Θ : MulAut Y →* M) (hΘ : Θ.ker = (MulAut.conj : Y →* MulAut Y).range)
    (A : Subgroup (MulAut Y)) (hA : IsElemAbelian 2 A) (h4 : Nat.card A = 4) :
    ∃ a ∈ A, a ≠ 1 ∧ a ∈ (MulAut.conj : Y →* MulAut Y).range := by
  set ψ : A →* M := Θ.comp A.subtype with hψ
  have hexp : ∀ b ∈ ψ.range, b * b = 1 := by
    rintro - ⟨a, rfl⟩
    have ha2 : a * a = 1 := Subtype.ext (by simpa [pow_two] using hA.2 a a.2)
    calc ψ a * ψ a = ψ (a * a) := by rw [map_mul]
      _ = 1 := by rw [ha2, map_one]
  have hcard : Nat.card ψ.range ≤ 2 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ψ.range)
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact Nat.le_of_dvd (by norm_num)
      (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact Subtype.ext (hexp g g.2)))
  have hker : Nat.card ψ.ker * Nat.card ψ.range = Nat.card A := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [h4] at hker
  have h2 : 1 < Nat.card ψ.ker := by
    by_contra hle
    push Not at hle
    have hpos : 1 ≤ Nat.card ψ.ker := Nat.one_le_iff_ne_zero.mpr (fun h => by
      rw [h, zero_mul] at hker; omega)
    have h1 : Nat.card ψ.ker = 1 := le_antisymm hle hpos
    rw [h1, one_mul] at hker
    omega
  rcases Subgroup.bot_or_exists_ne_one ψ.ker with hbot | ⟨a, ha, ha1⟩
  · rw [hbot, Subgroup.card_bot] at h2
    omega
  · refine ⟨(a : A), a.2, fun h => ha1 (Subtype.ext h), ?_⟩
    rw [← hΘ]
    simpa [hψ] using ha

private theorem centralizer_sup_eq_top_of_mulEquiv {X Z : Type} [Group X] [Group Z]
    (e : X ≃* Z) {u v : X}
    (h : Subgroup.centralizer ({e u} : Set Z) ⊔ Subgroup.centralizer ({e v} : Set Z) = ⊤) :
    Subgroup.centralizer ({u} : Set X) ⊔ Subgroup.centralizer ({v} : Set X) = ⊤ := by
  have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ e.symm.surjective,
    CFSG.centralizer_singleton_map, CFSG.centralizer_singleton_map] at hmap
  simpa using hmap

theorem centralizer_sup_centralizer_eq_top_g2_td4
    {Y : Type} [Group Y] {p f : ℕ}
    (hp2 : p ≠ 2)
    (hY : CFSG.Models.LieModel Y .trialityD4 0 p f ∨ CFSG.Models.LieModel Y .G2 0 p f)
    {u v : Y} (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hcomm : u * v = v * u) :
    Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({v} : Set Y) = ⊤ := by
  have hp : p.Prime := hY.elim (fun h => h.1.1) (fun h => h.1.1)
  have hf : 1 ≤ f := hY.elim (fun h => h.1.2.1) (fun h => h.1.2.1)
  have : Fact p.Prime := ⟨hp⟩
  rcases hY with hY | hY
  · obtain ⟨e⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.equiv_modelUniv_d4 hp hp2 hf
      (blueprintLieModel_of_models_of_ne_tits hY (by decide))
    refine centralizer_sup_eq_top_of_mulEquiv e ?_
    exact CFSG.ClassicalInvolution.G2D4Models.sup_centralizer_eq_top_model_td4 (p := p) (e := f)
      hp2 hY.1 (u := e u) (v := e v) (by rw [← map_mul, hu2, map_one])
      (by rw [← map_mul, hv2, map_one])
      (fun h => hu1 (e.injective (by simpa using h)))
      (fun h => hv1 (e.injective (by simpa using h))) (fun h => huv (e.injective h))
      (by rw [← map_mul, ← map_mul, hcomm])
  · have h3 : 3 ≤ p ^ f := hY.1.2.2.2
    by_cases h5 : 5 ≤ p ^ f
    · obtain ⟨e⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.equiv_modelUniv_g2 hp hp2 hf h3
        (blueprintLieModel_of_models_of_ne_tits hY (by decide))
      refine centralizer_sup_eq_top_of_mulEquiv e ?_
      exact CFSG.ClassicalInvolution.G2D4Models.g2CentralizersGenerate_of_nonToral
        CFSG.ClassicalInvolution.G2D4Models.g2NonToralGenerate_all hp2 h5 hY.1
        (e u) (e v) (by rw [← map_mul, hu2, map_one]) (by rw [← map_mul, hv2, map_one])
        (fun h => hu1 (e.injective (by simpa using h)))
        (fun h => hv1 (e.injective (by simpa using h)))
        (fun h => huv (e.injective h)) (by rw [← map_mul, ← map_mul, hcomm])
    ·
      have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
      have hpf : p ^ f = 3 := by
        have hle : p ^ f ≤ 4 := by omega
        obtain ⟨k, hk⟩ := hodd
        omega
      have hp3 : p = 3 := by
        have hdvd : p ∣ 3 := by rw [← hpf]; exact dvd_pow_self p (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
      have hf1 : f = 1 := by
        have h31 : p ^ f = p ^ 1 := by rw [hpf, pow_one, hp3]
        exact Nat.pow_right_injective hp.two_le h31
      obtain rfl : p = 3 := hp3
      obtain rfl : f = 1 := hf1
      obtain ⟨e⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.equiv_modelUniv_g2
        (p := 3) (f := 1) Nat.prime_three (by norm_num) le_rfl (by norm_num)
        (blueprintLieModel_of_models_of_ne_tits hY (by decide))
      refine centralizer_sup_eq_top_of_mulEquiv e ?_
      exact CFSG.ClassicalInvolution.Uniform.g2_pairGen3_proved (e u) (e v)
        (by rw [← map_mul, hu2, map_one]) (by rw [← map_mul, hv2, map_one])
        (fun h => hu1 (e.injective (by simpa using h)))
        (fun h => hv1 (e.injective (by simpa using h)))
        (fun h => huv (e.injective h)) (by rw [← map_mul, ← map_mul, hcomm])

private theorem exists_ne_one_mem_range_conj_of_four_of_congr {Y C M : Type} [Group Y]
    [Group C] [Group M] [IsCyclic M] (e : Y ≃* C) (Θ : MulAut C →* M)
    (hΘ : Θ.ker = (MulAut.conj : C →* MulAut C).range)
    (A : Subgroup (MulAut Y)) (hA : IsElemAbelian 2 A) (h4 : Nat.card A = 4) :
    ∃ a ∈ A, a ≠ 1 ∧ a ∈ (MulAut.conj : Y →* MulAut Y).range := by
  refine exists_ne_one_mem_range_conj_of_four (Θ.comp (MulAut.congr e).toMonoidHom) ?_ A hA h4
  rw [← MonoidHom.comap_ker, hΘ]
  ext α
  rw [Subgroup.mem_comap]
  exact CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff e α

theorem exists_ne_one_mem_range_conj_of_four_g2_td4
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    (hp2 : p ≠ 2)
    (hY : CFSG.Models.LieModel Y .trialityD4 0 p f ∨ CFSG.Models.LieModel Y .G2 0 p f)
    (A : Subgroup (MulAut Y)) (hA : IsElemAbelian 2 A) (h4 : Nat.card A = 4) :
    ∃ a ∈ A, a ≠ 1 ∧ a ∈ (MulAut.conj : Y →* MulAut Y).range := by
  have hp : p.Prime := hY.elim (fun h => h.1.1) (fun h => h.1.1)
  have hf : 1 ≤ f := hY.elim (fun h => h.1.2.1) (fun h => h.1.2.1)
  rcases hY with hY | hY
  ·
    have htw : CFSG.Blueprint.TwistedChevalleyModel Y .D4 (p ^ f) :=
      (blueprintLieModel_of_models_of_ne_tits hY (by decide)).chevalleyExceptionalModel
        (by decide) |>.2
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
    obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
      CFSG.LieType.Chevalley.odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
    have := hcyc
    exact exists_ne_one_mem_range_conj_of_four_of_congr e Θ hker A hA h4
  ·
    have hU : CFSG.Blueprint.UntwistedChevalleyModel Y .G2 (p ^ f) :=
      (blueprintLieModel_of_models_of_ne_tits hY (by decide)).chevalleyExceptionalModel
        (by decide) |>.2
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hU
    let e' : Y ≃* CFSG.Blueprint.Chevalley.adjointGroup .G2 K :=
      e.trans ((QuotientGroup.quotientMulEquivOfEq
        CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)
    by_cases h3 : p = 3
    · subst h3
      have : CharP K CFSG.LieType.Ree.ReeTag.G2.prime :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_three hf hK
      obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
        CFSG.LieType.Chevalley.G2_three_exact_automorphism_normal_form hf K hK
      exact exists_ne_one_mem_range_conj_of_four_of_congr e' Θ hker A hA h4
    · have hcyc : IsCyclic (K ≃+* K) :=
        CFSG.RankThree.PartOne.CTP.isCyclic_ringEquiv_of_card hp hf hK
      obtain ⟨-, ⟨Θ, -, -, hker, -⟩⟩ :=
        CFSG.LieType.Chevalley.odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf
          K hK .G2 (Or.inr ⟨rfl, h3⟩)
      have := hcyc
      exact exists_ne_one_mem_range_conj_of_four_of_congr e' Θ hker A hA h4

private theorem exists_conj_ne_commute_of_fixSub {Y : Type} [Group Y] [Finite Y]
    {α : MulAut Y}
    (hodd : ∀ N : Subgroup ↥(fixSub α), N.Normal → Odd (Nat.card N) → N = ⊥)
    {u : Y} (hu : α u = u) (hu2 : u * u = 1)
    (htZ : (⟨u, hu⟩ : ↥(fixSub α)) ∉ Subgroup.center ↥(fixSub α)) :
    ∃ h : Y, α h = h ∧ h * u * h⁻¹ ≠ u ∧ h * u * h⁻¹ * u = u * (h * u * h⁻¹) := by
  obtain ⟨g, hgne, hgc⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_conj_ne_commute_of_forall_odd_normal_eq_bot hodd
      (Subtype.ext (by simpa using hu2)) htZ
  refine ⟨(g : Y)⁻¹, ?_, ?_, ?_⟩
  · have hg : α (g : Y) = (g : Y) := g.2
    show α ((g : Y)⁻¹) = ((g : Y))⁻¹
    rw [map_inv, hg]
  · intro hEq
    apply hgne
    apply Subtype.ext
    show ((g⁻¹ * ⟨u, hu⟩ * g : ↥(fixSub α)) : Y) = u
    calc ((g⁻¹ * ⟨u, hu⟩ * g : ↥(fixSub α)) : Y) = (g : Y)⁻¹ * u * (g : Y) := by simp
      _ = u := by simpa using hEq
  · have := congrArg (fun w : ↥(fixSub α) => (w : Y)) hgc
    simpa using this

private theorem exists_conj_ne_commute_of_fixSub_simple {Y : Type} [Group Y] [Finite Y]
    {α : MulAut Y} (hs : IsSimpleGroup ↥(fixSub α))
    (hnab : ∃ a b : ↥(fixSub α), a * b ≠ b * a)
    {u : Y} (hu : α u = u) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ h : Y, α h = h ∧ h * u * h⁻¹ ≠ u ∧ h * u * h⁻¹ * u = u * (h * u * h⁻¹) := by
  have := hs
  have huH : u ∈ fixSub α := mem_fixSub.mpr hu
  have ht2 : (⟨u, huH⟩ : ↥(fixSub α)) * ⟨u, huH⟩ = 1 := Subtype.ext (by simpa using hu2)
  have ht1 : (⟨u, huH⟩ : ↥(fixSub α)) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have htord : orderOf (⟨u, huH⟩ : ↥(fixSub α)) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  obtain ⟨hodd, htZ⟩ :=
    CFSG.SeitzReduction.F4Pilot.forall_odd_normal_eq_bot_and_not_mem_center_of_isSimpleGroup
      (G := ↥(fixSub α)) hnab htord
  exact exists_conj_ne_commute_of_fixSub hodd hu hu2 htZ

private theorem exists_conj_ne_commute_of_outer_involution_td4
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp2 : p ≠ 2)
    (hY : CFSG.Models.LieModel Y .trialityD4 0 p f)
    (α : MulAut Y) (hα : α * α = 1)
    (hout : α ∉ (MulAut.conj : Y →* MulAut Y).range)
    {u : Y} (hu : α u = u) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ h : Y, α h = h ∧ h * u * h⁻¹ ≠ u ∧ h * u * h⁻¹ * u = u * (h * u * h⁻¹) := by
  have hp : p.Prime := hY.1.1
  have hf : 1 ≤ f := hY.1.2.1
  have hα2 : α ^ 2 = 1 := by rw [sq]; exact hα
  obtain ⟨-, -, hs, hnab, -⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.td4_outer_involution_fixed hp hp2 hf
      (blueprintLieModel_of_models_of_ne_tits hY (by decide)) α hα2 hout
  exact exists_conj_ne_commute_of_fixSub_simple hs hnab hu hu2 hu1

private theorem odd_normal_eq_bot_of_isSimpleGroup {Y : Type} [Group Y] [Finite Y]
    {α : MulAut Y} (hs : IsSimpleGroup ↥(fixSub α))
    {t : ↥(fixSub α)} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∀ N : Subgroup ↥(fixSub α), N.Normal → Odd (Nat.card N) → N = ⊥ := by
  have := hs
  intro N hN hNodd
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top] at hNodd
    have hdvd : 2 ∣ Nat.card ↥(fixSub α) := by
      have h2 := orderOf_dvd_natCard t
      rwa [orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1] at h2
    exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 hdvd)

private theorem exists_conj_ne_commute_of_fixSub_center {Y : Type} [Group Y] [Finite Y]
    {α : MulAut Y} (hZ : Subgroup.center ↥(fixSub α) = ⊥)
    (hodd : ∀ N : Subgroup ↥(fixSub α), N.Normal → Odd (Nat.card N) → N = ⊥)
    {u : Y} (hu : α u = u) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ h : Y, α h = h ∧ h * u * h⁻¹ ≠ u ∧ h * u * h⁻¹ * u = u * (h * u * h⁻¹) := by
  refine exists_conj_ne_commute_of_fixSub hodd hu hu2 ?_
  intro hmem
  rw [hZ, Subgroup.mem_bot] at hmem
  exact hu1 (by simpa using congrArg Subtype.val hmem)

private theorem exists_conj_ne_commute_of_congr {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z)
    (α : MulAut Y) {u : Y}
    (h : ∃ h' : Z, MulAut.congr e α h' = h' ∧ h' * e u * h'⁻¹ ≠ e u ∧
      h' * e u * h'⁻¹ * e u = e u * (h' * e u * h'⁻¹)) :
    ∃ h : Y, α h = h ∧ h * u * h⁻¹ ≠ u ∧ h * u * h⁻¹ * u = u * (h * u * h⁻¹) := by
  obtain ⟨h', hfix, hne, hcomm⟩ := h
  have hfix' : α (e.symm h') = e.symm h' := by
    have := congrArg e.symm hfix
    simpa [MulAut.congr_apply] using this
  refine ⟨e.symm h', hfix', ?_, ?_⟩
  · intro hEq
    apply hne
    have := congrArg e hEq
    simpa using this
  · have := congrArg e.symm hcomm
    simpa using this

private theorem exists_conj_ne_commute_of_outer_involution_g2_ne_three
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hY : CFSG.Models.LieModel Y .G2 0 p f) (α : MulAut Y) (hα : α * α = 1)
    (hout : α ∉ (MulAut.conj : Y →* MulAut Y).range)
    {u : Y} (hu : α u = u) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ h : Y, α h = h ∧ h * u * h⁻¹ ≠ u ∧ h * u * h⁻¹ * u = u * (h * u * h⁻¹) := by
  have hp : p.Prime := hY.1.1
  have hf : 1 ≤ f := hY.1.2.1
  have hU : CFSG.Blueprint.UntwistedChevalleyModel Y .G2 (p ^ f) :=
    (blueprintLieModel_of_models_of_ne_tits hY (by decide)).chevalleyExceptionalModel
      (by decide) |>.2
  obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := hU
  let e : Y ≃* CFSG.Blueprint.Chevalley.adjointGroup .G2 K :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
      QuotientGroup.quotientBot)
  let α' : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := MulAut.congr e α
  have hα'2 : α' ^ 2 = 1 := by
    change (MulAut.congr e α) ^ 2 = 1
    rw [pow_two, ← map_mul, show α * α = 1 from hα, map_one]
  have hα'inn : ¬ IsInnerAut α' := by
    intro hin
    exact hout ((CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff e α).mp hin)
  have hα'1 : α' ≠ 1 := by
    intro h
    exact hα'inn (by rw [h]; exact Subgroup.one_mem _)
  have htord : orderOf α' = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hα'2) hα'1
  obtain ⟨k, hk1, hkf, kk, _, _, hkcard, ⟨eK⟩, hs, hZ⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.g2_fixSub_outer_involution hp hp2 hp3 hf K hK htord hα'inn
  have hu' : α' (e u) = e u := by
    show MulAut.congr e α (e u) = e u
    rw [MulAut.congr_apply]
    simp [hu]
  have hu'2 : e u * e u = 1 := by rw [← map_mul, hu2, map_one]
  have hu'1 : e u ≠ 1 := fun h => hu1 (e.injective (by simpa using h))
  have huH : e u ∈ fixSub α' := mem_fixSub.mpr hu'
  have ht2 : (⟨e u, huH⟩ : ↥(fixSub α')) * ⟨e u, huH⟩ = 1 := by
    apply Subtype.ext
    show e u * e u = 1
    simpa using hu'2
  have hodd := odd_normal_eq_bot_of_isSimpleGroup (α := α') hs ht2
    (fun h => hu'1 (congrArg Subtype.val h))
  exact exists_conj_ne_commute_of_congr e α
    (exists_conj_ne_commute_of_fixSub_center (α := α') hZ hodd hu' hu'2 hu'1)

private theorem exists_conj_ne_commute_of_outer_involution_g2_three
    {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (hY : CFSG.Models.LieModel Y .G2 0 3 f) (α : MulAut Y) (hα : α * α = 1)
    (hout : α ∉ (MulAut.conj : Y →* MulAut Y).range)
    {u : Y} (hu : α u = u) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ h : Y, α h = h ∧ h * u * h⁻¹ ≠ u ∧ h * u * h⁻¹ * u = u * (h * u * h⁻¹) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hf : 1 ≤ f := hY.1.2.1
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hU : CFSG.Blueprint.UntwistedChevalleyModel Y .G2 (3 ^ f) :=
    (blueprintLieModel_of_models_of_ne_tits hY (by decide)).chevalleyExceptionalModel
      (by decide) |>.2
  obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := hU
  have : CharP K ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_three hf hK
  let e : Y ≃* adjointGroup ReeTag.G2.tag K :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
      QuotientGroup.quotientBot)
  let α' : MulAut (adjointGroup ReeTag.G2.tag K) := MulAut.congr e α
  have hα'2 : α' ^ 2 = 1 := by
    change (MulAut.congr e α) ^ 2 = 1
    rw [pow_two, ← map_mul, show α * α = 1 from hα, map_one]
  have hα'inn : ¬ IsInnerAut α' := by
    intro hin
    exact hout ((CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff e α).mp hin)
  have hα'1 : α' ≠ 1 := by
    intro h
    exact hα'inn (by rw [h]; exact Subgroup.one_mem _)
  have hu' : α' (e u) = e u := by
    show MulAut.congr e α (e u) = e u
    rw [MulAut.congr_apply]
    simp [hu]
  have hu'2 : e u * e u = 1 := by rw [← map_mul, hu2, map_one]
  have hu'1 : e u ≠ 1 := fun h => hu1 (e.injective (by simpa using h))
  have huH : e u ∈ fixSub α' := mem_fixSub.mpr hu'
  have ht2 : (⟨e u, huH⟩ : ↥(fixSub α')) * ⟨e u, huH⟩ = 1 := by
    apply Subtype.ext
    show e u * e u = 1
    simpa using hu'2
  have ht1 : (⟨e u, huH⟩ : ↥(fixSub α')) ≠ 1 := fun h => hu'1 (congrArg Subtype.val h)
  have hmain : ∃ h : adjointGroup ReeTag.G2.tag K, α' h = h ∧ h * e u * h⁻¹ ≠ e u ∧
      h * e u * h⁻¹ * e u = e u * (h * e u * h⁻¹) := by
    rcases CFSG.LieType.AlgebraicGroups.G2_three_involution_inner_quadratic_or_exceptional
      hf hK hα'2 with ⟨g, a, hαg⟩ | ⟨k, hk1, hKk, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, hαβ⟩
    · exact absurd (CFSG.GH74.GLS.IVK.Proofs2.ivk93res_inner_of_diag hαg) hα'inn
    ·
      have hF2 : ringChar K ≠ 2 := by
        rw [ringChar.eq K ReeTag.G2.prime]
        decide
      obtain ⟨hs, hnab⟩ := kn_g2_quadratic_fixed hF2 hp hk1 hKk δ hδ hαg hα'2
      exact exists_conj_ne_commute_of_fixSub_simple hs hnab hu' hu'2 hu'1
    ·
      have hKb : Nat.card K = 3 ^ (2 * b + 1) := by rw [hK, hfb]
      have hαβ2 : (MulAut.conj g * ReeTag.G2.finiteReeAut K b) ^ 2 = 1 := hαβ ▸ hα'2
      rcases Nat.eq_zero_or_pos b with hb | hb
      ·
        subst hb
        have hK0 : Nat.card K = 3 ^ (2 * 0 + 1) := hKb
        have hoddY : FixOddFree (MulAut.conj g * ReeTag.G2.finiteReeAut K 0) :=
          fixed_oddFree_exceptional_zero hK0 g hαβ2
        obtain ⟨⟨ψ, hψ⟩, -, -⟩ :=
          CFSG.LieType.Ree.G2_exceptional_coset_involution_fixed_p_components 0 K hK0 g hαβ2
        obtain ⟨-, ⟨eFix, -⟩, -, -⟩ :=
          CFSG.LieType.Chevalley.fixed_centralizer_of_conj_eq hψ
        have hmap : ((ReeTag.G2.finiteReeAut K 0).toMonoidHom.eqLocus (MonoidHom.id _)).map
            (adjointGroup ReeTag.G2.tag K).subtype = ReeTag.G2.reeGamma K 0 := rfl
        let Ψ : ↥(fixSub (MulAut.conj g * ReeTag.G2.finiteReeAut K 0)) ≃*
            ↥(ReeTag.G2.reeGamma K 0) :=
          eFix.trans ((Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
            (MulEquiv.subgroupCongr hmap))
        have hZ0 : Subgroup.center
            ↥(fixSub (MulAut.conj g * ReeTag.G2.finiteReeAut K 0)) = ⊥ :=
          center_eq_bot_of_mulEquiv_target Ψ (ReeTag.center_reeGamma_G2_eq_bot (a := 0) hK0)
        have hZ : Subgroup.center ↥(fixSub α') = ⊥ := by
          rw [hαβ]
          exact hZ0
        have hoddY' : FixOddFree α' := by
          rw [hαβ]
          exact hoddY
        have hodd : ∀ N : Subgroup ↥(fixSub α'), N.Normal → Odd (Nat.card N) → N = ⊥ := by
          intro N hN hNodd
          have h1 : N.map (fixSub α').subtype ≤ fixSub α' := Subgroup.map_subtype_le N
          have h2 : ∀ c ∈ fixSub α', ∀ n ∈ N.map (fixSub α').subtype,
              c * n * c⁻¹ ∈ N.map (fixSub α').subtype := by
            intro c hc n hn
            obtain ⟨n', hn', rfl⟩ := hn
            exact ⟨⟨c, hc⟩ * n' * ⟨c, hc⟩⁻¹, hN.conj_mem n' hn' ⟨c, hc⟩, rfl⟩
          have h3 : Odd (Nat.card ↥(N.map (fixSub α').subtype)) := by
            rw [← Nat.card_congr (N.equivMapOfInjective (fixSub α').subtype
              (fixSub α').subtype_injective).toEquiv]
            exact hNodd
          exact (Subgroup.map_eq_bot_iff_of_injective N (fixSub α').subtype_injective).mp
            (hoddY' _ h1 h2 h3)
        exact exists_conj_ne_commute_of_fixSub_center hZ hodd hu' hu'2 hu'1
      ·
        obtain ⟨hs, hnab⟩ := kn_g2_ree_fixed hb hKb hαβ2
        rw [hαβ] at hu' ⊢
        exact exists_conj_ne_commute_of_fixSub_simple hs hnab hu' hu'2 hu'1
  exact exists_conj_ne_commute_of_congr e α hmain

theorem exists_conj_ne_commute_of_outer_involution_g2_td4
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp2 : p ≠ 2)
    (hY : CFSG.Models.LieModel Y .trialityD4 0 p f ∨ CFSG.Models.LieModel Y .G2 0 p f)
    (α : MulAut Y) (hα : α * α = 1) (hout : α ∉ (MulAut.conj : Y →* MulAut Y).range)
    {u : Y} (hu : α u = u) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ h : Y, α h = h ∧ h * u * h⁻¹ ≠ u ∧ h * u * h⁻¹ * u = u * (h * u * h⁻¹) := by
  rcases hY with hY | hY
  · exact exists_conj_ne_commute_of_outer_involution_td4 hp2 hY α hα hout hu hu2 hu1
  · by_cases h3 : p = 3
    · subst h3
      exact exists_conj_ne_commute_of_outer_involution_g2_three hY α hα hout hu hu2 hu1
    · exact exists_conj_ne_commute_of_outer_involution_g2_ne_three hp2 h3 hY α hα hout hu hu2 hu1

private theorem inf_centralizer_eq_map_centralizer {G : Type} [Group G] (L : Subgroup G)
    (u : ↥L) :
    L ⊓ Subgroup.centralizer ({(u : G)} : Set G) =
      (Subgroup.centralizer ({u} : Set ↥L)).map L.subtype := by
  ext y
  constructor
  · rintro ⟨hyL, hyC⟩
    refine ⟨⟨y, hyL⟩, ?_, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hyC))
  · rintro ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨z.2, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hz))

theorem seitzFourOuter_g2_td4 :
    SeitzFourOuter fun X _ => ∃ p f : ℕ, p ≠ 2 ∧
      (CFSG.Models.LieModel X .trialityD4 0 p f ∨ CFSG.Models.LieModel X .G2 0 p f) := by
  intro G _ _ L E hLn hLs hnab hP hC hE h4 hEL
  obtain ⟨p, f, hp2, hY⟩ := hP
  have : L.Normal := hLn
  set A : Subgroup (MulAut ↥L) := E.map (MulAut.conjNormal : G →* MulAut ↥L) with hAdef
  have hA : IsElemAbelian 2 A := hE.map _
  have hA4 : Nat.card A = 4 := by
    rw [Subgroup.card_map_of_injective (conjNormal_injective_of_centralizer_eq_bot hC), h4]
  obtain ⟨a, haA, ha1, hainn⟩ :=
    exists_ne_one_mem_range_conj_of_four_g2_td4 hp2 hY A hA hA4
  obtain ⟨u, huE, haeq⟩ := haA
  have hu1 : u ≠ 1 := fun h => ha1 (by rw [← haeq, h, map_one])
  rw [← haeq] at hainn
  obtain ⟨l, hl⟩ := hainn
  have hconjN : ∀ m : ↥L, (MulAut.conjNormal m : MulAut ↥L) = MulAut.conj m := by
    intro m
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.conj_apply]
    rfl
  have hinj : Function.Injective (MulAut.conjNormal : G →* MulAut ↥L) :=
    conjNormal_injective_of_centralizer_eq_bot hC
  have huL : u ∈ L := by
    have hlu : (l : G) = u := hinj (by rw [hconjN l]; exact hl)
    exact hlu ▸ l.2
  obtain ⟨x, hxE, hxL⟩ := Set.not_subset.mp hEL
  have hx1 : x ≠ 1 := fun h => hxL (h ▸ L.one_mem)
  have : IsMulCommutative E := hE.1
  have hux : u * x = x * u := Subgroup.mul_comm_of_mem_isMulCommutative E huE hxE
  have hx2 : x * x = 1 := by
    have h := hE.2 x hxE
    rwa [pow_two] at h
  have hu2 : u * u = 1 := by
    have h := hE.2 u huE
    rwa [pow_two] at h
  let α : MulAut ↥L := MulAut.conjNormal x
  have hαcoe : α = MulAut.conjNormal x := rfl
  have hα : α * α = 1 := by
    rw [hαcoe, ← map_mul, hx2, map_one]
  have hout : α ∉ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    intro h
    obtain ⟨m, hm⟩ := h
    have hmx : (m : G) = x := hinj (by rw [hconjN m]; exact hαcoe ▸ hm)
    exact hxL (hmx ▸ m.2)
  have hfix : α ⟨u, huL⟩ = ⟨u, huL⟩ := by
    rw [hαcoe]
    apply Subtype.ext
    show x * u * x⁻¹ = u
    rw [← hux]
    group
  have huL2 : (⟨u, huL⟩ : ↥L) * ⟨u, huL⟩ = 1 := by
    apply Subtype.ext
    show u * u = 1
    exact hu2
  have huL1 : (⟨u, huL⟩ : ↥L) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  obtain ⟨h, hhfix, hhne, hhcomm⟩ :=
    exists_conj_ne_commute_of_outer_involution_g2_td4 hp2 hY α hα hout hfix huL2 huL1
  have hhx : (h : G) * x = x * h := by
    have h1 : α h = h := hhfix
    have h2 : (α h : ↥L) = x * (h : G) * x⁻¹ := by rw [hαcoe]; rfl
    have h3 : x * (h : G) * x⁻¹ = (h : G) := by rw [← h2]; exact congrArg Subtype.val h1
    calc (h : G) * x = (x * (h : G) * x⁻¹) * x := by rw [h3]
      _ = x * h := by group
  set v : ↥L := h * ⟨u, huL⟩ * h⁻¹ with hvdef
  have hv2 : v * v = 1 := by
    have h1 : v * v = h * (⟨u, huL⟩ * ⟨u, huL⟩) * h⁻¹ := by
      rw [hvdef]
      group
    rw [h1, huL2]
    group
  have hv1 : v ≠ 1 := by
    intro h1
    apply huL1
    calc (⟨u, huL⟩ : ↥L) = h⁻¹ * (h * ⟨u, huL⟩ * h⁻¹) * h := by group
      _ = h⁻¹ * (1 : ↥L) * h := by rw [← hvdef, h1]
      _ = 1 := by group
  have huv : (⟨u, huL⟩ : ↥L) ≠ v := by
    intro h1
    exact hhne (by rw [hvdef]; exact h1.symm)
  have hcomm : (⟨u, huL⟩ : ↥L) * v = v * ⟨u, huL⟩ := hhcomm.symm
  have h5 := centralizer_sup_centralizer_eq_top_g2_td4 hp2 hY huL2 hv2 huL1 hv1 huv hcomm
  have hgen : L ⊓ centralizer ({u} : Set G) ⊔ L ⊓ centralizer ({h * u * h⁻¹} : Set G) = L := by
    have hmap := congrArg (Subgroup.map L.subtype) h5
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at hmap
    rw [← inf_centralizer_eq_map_centralizer L (⟨u, huL⟩ : ↥L),
      ← inf_centralizer_eq_map_centralizer L v] at hmap
    have hcoev : ((v : ↥L) : G) = h * u * h⁻¹ := by
      rw [hvdef]
      rfl
    simpa [hcoev] using hmap
  exact iSup_centralizer_eq_of_conj_centralizer_sup L E huE hu1 hxE hx1 h.2 hhx hgen

theorem seitzFour_g2_td4 :
    SeitzFour fun X _ => ∃ p f : ℕ, p ≠ 2 ∧
      (CFSG.Models.LieModel X .trialityD4 0 p f ∨ CFSG.Models.LieModel X .G2 0 p f) := by
  intro G _ _ L E hLn hLs hnab hP hC hE h4 hx
  by_cases hEL : E ≤ L
  · have hnotExc : ¬ SeitzFourExc ↥L := fun hse => hx ⟨hEL, hse⟩
    obtain ⟨p, f, hp2, hY | hY⟩ := hP
    · exact seitzFourInner_g2_td4 L E hLn hLs hnab ⟨p, f, hp2, Or.inl hY⟩ hC hE h4 hEL hnotExc
    · by_cases h5 : 5 ≤ p ^ f
      · exact seitzFourInner_g2_td4 L E hLn hLs hnab ⟨p, f, hp2, Or.inr ⟨h5, hY⟩⟩ hC hE h4
          hEL hnotExc
      ·
        have h3 : 3 ≤ p ^ f := hY.1.2.2.2
        have hp : p.Prime := hY.1.1
        have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
        have hpf : p ^ f = 3 := by
          have hle : p ^ f ≤ 4 := by omega
          obtain ⟨k, hk⟩ := hodd
          omega
        have hf0 : f ≠ 0 := by
          rintro rfl
          simp at h3
        have hp3 : p = 3 := by
          have hdvd : p ∣ 3 := by rw [← hpf]; exact dvd_pow_self p hf0
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
        have hf1 : f = 1 := by
          have h31 : p ^ f = p ^ 1 := by rw [hpf, pow_one, hp3]
          exact Nat.pow_right_injective hp.two_le h31
        obtain rfl : p = 3 := hp3
        obtain rfl : f = 1 := hf1
        exact seitzFourInner_g2_three L E hLn hLs hnab hY hC hE h4 hEL hnotExc
  · exact seitzFourOuter_g2_td4 L E hLn hLs hnab hP hC hE h4 hEL

end CFSG.LocalAnalysis.WeakClosure81

end
