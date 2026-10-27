module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaCA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoLem
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Hyp
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.Monster.B.Short.Extraspecial
public import CFSG.Quasithin.Background.Asc81cPfBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_centerIn_eq_zpowers {P : Subgroup (MulAut W)} {z : MulAut W}
    (hzP : z ∈ P) (hzc : ∀ y ∈ P, y * z = z * y)
    (hZP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z) :
    CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.centerIn P =
      Subgroup.zpowers z := by
  rw [CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.centerIn]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hZP y y.2 (fun w hw => by
      simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨w, hw⟩))
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_map.mpr ⟨⟨z, hzP⟩,
      Subgroup.mem_center_iff.mpr (fun g => Subtype.ext (hzc g.1 g.2)), rfl⟩

private theorem w16g_exponent_eq_three {P : Subgroup (MulAut W)} (hP : IsPOnePlusTwo 3 ↥P)
    {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3) : Monoid.exponent ↥P = 3 := by
  have hdvd : Monoid.exponent ↥P ∣ 3 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun g => hP.2.2 g)
  have hne1 : Monoid.exponent ↥P ≠ 1 := by
    intro h1
    haveI : Subsingleton ↥P := Monoid.exp_eq_one_iff.mp h1
    have hzPne1 : (⟨z, hzP⟩ : ↥P) ≠ 1 := fun h => by
      have hz1 : z = 1 := congrArg Subtype.val h
      rw [hz1, orderOf_one] at hz3
      norm_num at hz3
    exact hzPne1 (Subsingleton.elim _ _)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd h hne1
  · exact h

theorem s13_six_le_rk_of_stable (hW : ∀ w : W, w * w = 1) {P : Subgroup (MulAut W)}
    (hP : IsPOnePlusTwo 3 ↥P) {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3)
    (hzc : ∀ y ∈ P, y * z = z * y)
    (hZP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z) {J : Subgroup W}
    (hJ : StableUnder P J) (hJ1 : J ≠ ⊥) (hfix : J ⊓ fixV (Subgroup.zpowers z) = ⊥) :
    6 ≤ rk ↥J := by
  classical
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hz3pow : z ^ 3 = 1 := by simpa [hz3] using pow_orderOf_eq_one z
  have hZp : Subgroup.zpowers z ≤ P := Subgroup.zpowers_le.mpr hzP
  obtain ⟨a, haP, ha_notin⟩ : ∃ x : MulAut W, x ∈ P ∧ x ∉ Subgroup.zpowers z := by
    by_contra hcon
    push Not at hcon
    have hPeq : Subgroup.zpowers z = P := le_antisymm hZp (fun x hx => hcon x hx)
    have hcardP : Nat.card ↥P = 27 := by rw [hP.2.1]; norm_num
    have hcardz : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
    rw [hPeq] at hcardz
    omega
  have ha_ne1 : a ≠ 1 := fun h1 => ha_notin (by rw [h1]; exact Subgroup.one_mem _)
  have ha3pow : a ^ 3 = 1 := by simpa using congrArg Subtype.val (hP.2.2 ⟨a, haP⟩)
  have ha3 : orderOf a = 3 := orderOf_eq_prime ha3pow ha_ne1
  have hzk : Commute z a := (hzc a haP).symm
  set Zs : Subgroup (MulAut W) := Subgroup.zpowers z with hZs
  set X : Subgroup (MulAut W) := Subgroup.zpowers a with hX
  set E : Subgroup (MulAut W) := Zs ⊔ X with hE
  have hEelem : IsElemAbelian 3 E := by
    rw [hE, hZs, hX]
    exact w16g_isElemAbelian_sup_zpowers hz3pow ha3pow hzk
  have hEcard : Nat.card ↥E = 9 := by
    rw [hE, hZs, hX]
    have h := w16g_card_sup_zpowers Nat.prime_three hz3 ha3 hzk ha_notin
    simpa using h
  have hEodd : Odd (Nat.card E) := by rw [hEcard]; norm_num
  have hEcomm : ∀ a' ∈ E, ∀ b' ∈ E, a' * b' = b' * a' := fun a' ha' b' hb' =>
    congrArg Subtype.val (hEelem.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
  have hEPle : E ≤ P := by
    rw [hE]
    exact sup_le (Subgroup.zpowers_le.mpr hzP) (Subgroup.zpowers_le.mpr haP)
  have hJstabE : StableUnder E J := fun x hx u hu => hJ x (hEPle hx) u hu
  have hJfixE : J ⊓ fixV E = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have h1 : u ∈ J ⊓ fixV Zs := by
      refine ⟨hu.1, ?_⟩
      intro g hg
      exact hu.2 g (by rw [hE]; exact Subgroup.mem_sup_left hg)
    have h2 : J ⊓ fixV Zs = ⊥ := by rw [hZs]; exact hfix
    rw [h2] at h1
    exact h1
  have hJE : commSub J E = J := by
    have hdec := CFSG.Quasithin.B1.coprime_decomp hW2 hEodd hJstabE
    rw [hJfixE] at hdec
    rw [bot_sup_eq] at hdec
    exact hdec.1
  have hdecomp := inf_fixV_hyperplane_decomposition (W := W) hW2 Nat.prime_three (by norm_num)
    E hEelem hJstabE hJE
  have hhyper : hyperplanes 3 E =
      {Zs} ∪ Set.range (fun j : Fin 3 => Subgroup.zpowers (a * z ^ (j : ℕ))) := by
    rw [hE, hZs, hX]
    exact w16g_hyperplanes_sup_zpowers Nat.prime_three hz3 ha3 hzk ha_notin
  let Dj : Fin 3 → hyperplanes 3 E := fun j =>
    ⟨Subgroup.zpowers (a * z ^ (j : ℕ)), by rw [hhyper]; exact Or.inr ⟨j, rfl⟩⟩
  have hDj_inj : Function.Injective Dj := by
    intro i j hij
    have h1 : Subgroup.zpowers (a * z ^ (i : ℕ)) = Subgroup.zpowers (a * z ^ (j : ℕ)) :=
      congrArg Subtype.val hij
    exact (w16g_zpowers_mul_pow_injective Nat.prime_three hz3 ha3 hzk ha_notin).1 h1
  have hDj0 : (Dj 0 : Subgroup (MulAut W)) = X := by
    show Subgroup.zpowers (a * z ^ ((0 : Fin 3) : ℕ)) = X
    rw [hX]
    simp
  let F : Fin 3 → Subgroup W := fun j => J ⊓ fixV (Dj j : Subgroup (MulAut W))
  have hFind : iSupIndep F := hdecomp.1.comp hDj_inj
  let Zhyp : hyperplanes 3 E := ⟨Zs, by rw [hhyper]; exact Or.inl rfl⟩
  have hsup_eq : (⨆ D : hyperplanes 3 E, J ⊓ fixV (D : Subgroup (MulAut W))) =
      (J ⊓ fixV Zs) ⊔ ⨆ j : Fin 3, F j := by
    apply le_antisymm
    · refine iSup_le fun D => ?_
      have hD : D.1 ∈ {Zs} ∪ Set.range (fun j : Fin 3 => Subgroup.zpowers (a * z ^ (j : ℕ))) := by
        rw [← hhyper]
        exact D.2
      rcases hD with hD | ⟨j, hDj⟩
      · have hDZ : D = Zhyp := Subtype.ext hD
        rw [hDZ]
        exact le_sup_left
      · have hDD : D = Dj j := Subtype.ext hDj.symm
        rw [hDD]
        exact le_sup_of_le_right (le_iSup F j)
    · refine sup_le ?_ ?_
      · exact le_iSup (fun D : hyperplanes 3 E => J ⊓ fixV (D : Subgroup (MulAut W))) Zhyp
      · refine iSup_le fun j => ?_
        exact le_iSup (fun D : hyperplanes 3 E => J ⊓ fixV (D : Subgroup (MulAut W))) (Dj j)
  have hJ_eq : J = (J ⊓ fixV Zs) ⊔ ⨆ j : Fin 3, F j := by
    nth_rewrite 1 [← hdecomp.2]
    exact hsup_eq
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEP : CFSG.IsExtraspecialPGroup 3 ↥P :=
    (CFSG.isExtraspecialPGroup_iff_isExtraspecial (p := 3) (P := ↥P)).mpr hP.1
  have hcenterIn := w16g_centerIn_eq_zpowers hzP hzc hZP
  have hexp := w16g_exponent_eq_three hP hzP hz3
  have hXH : X ≤ P := Subgroup.zpowers_le.mpr haP
  have hXp : Nat.card ↥X = 3 := by rw [hX, Nat.card_zpowers, ha3]
  have hXZ : X ≠ CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.centerIn P := by
    intro h
    apply ha_notin
    have h' : a ∈ X := Subgroup.mem_zpowers a
    rw [h] at h'
    rwa [hcenterIn] at h'
  have hhypEq := ExtraspecialHyperplaneGeometry.hyperplanes_eq
    (p := 3) Nat.prime_three (by norm_num) P hEP hexp X hXH hXp hXZ
  have hhypEq' : hyperplanes 3 E = {Zs} ∪ conjClass P X := by
    have h1 : X ⊔ CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.centerIn P = E := by
      rw [hcenterIn, hE]
      exact sup_comm X Zs
    rw [← h1, hhypEq, hcenterIn]
  have hDjmem : ∀ j : Fin 3, (Dj j : Subgroup (MulAut W)) ∈ conjClass P X := by
    intro j
    have hmem : (Dj j : Subgroup (MulAut W)) ∈ ({Zs} ∪ conjClass P X) := by
      rw [← hhypEq']
      exact (Dj j).2
    rcases hmem with h | h
    · rw [Set.mem_singleton_iff] at h
      exfalso
      have h2 : Subgroup.zpowers (a * z ^ (j : ℕ)) = Subgroup.zpowers z := by
        have h3 := h
        rw [hZs] at h3
        exact h3
      exact (w16g_zpowers_mul_pow_injective Nat.prime_three hz3 ha3 hzk ha_notin).2 j h2
    · exact h
  have hFrank : ∀ j : Fin 3, rk (F j) = rk (F 0) := by
    intro j
    obtain ⟨g, hgP, hgmap⟩ := hDjmem j
    have hJmap : J.map g.toMonoidHom = J := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro u hu
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
        exact hJ g hgP v hv
      · rw [Subgroup.card_map_of_injective g.injective]
    have hGmap : (F 0).map g.toMonoidHom = F j := by
      change (J ⊓ fixV (Dj 0 : Subgroup (MulAut W))).map g.toMonoidHom =
        J ⊓ fixV (Dj j : Subgroup (MulAut W))
      have hfixj : fixV (Dj j : Subgroup (MulAut W)) =
          (fixV (Dj 0 : Subgroup (MulAut W))).map g.toMonoidHom := by
        rw [hgmap, ← hDj0]
        exact CFSG.Quasithin.Asc81c.fixV_map_conj (Dj 0 : Subgroup (MulAut W)) g
      rw [hfixj, Subgroup.map_inf _ _ _ g.injective, hJmap]
    have hcard := Subgroup.card_map_of_injective (K := F 0) (f := g.toMonoidHom) g.injective
    rw [hGmap] at hcard
    unfold rk
    rw [hcard]
  have hsum : rk ↥(⨆ j : Fin 3, F j) = 3 * rk (F 0) := by
    rw [w16g_rk_iSup_eq_sum hW2 F hFind]
    calc ∑ j : Fin 3, rk (F j) = ∑ _j : Fin 3, rk (F 0) :=
          Finset.sum_congr rfl fun j _ => hFrank j
      _ = 3 * rk (F 0) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hfixZs : J ⊓ fixV Zs = ⊥ := by rw [hZs]; exact hfix
  have hrkJ : rk ↥J = 3 * rk (F 0) := by
    have h1 : J = ⨆ j : Fin 3, F j := by rw [hJ_eq, hfixZs, bot_sup_eq]
    rw [h1, hsum]
  have hF0stab : StableUnder Zs (F 0) := by
    change StableUnder Zs (J ⊓ fixV (Dj 0 : Subgroup (MulAut W)))
    rw [hDj0]
    have hJstabZs : StableUnder Zs J := fun x hx u hu =>
      hJ x (hEPle (by rw [hE]; exact Subgroup.mem_sup_left hx)) u hu
    have hfixXstab : StableUnder Zs (fixV X) :=
      stableUnder_fixV (Y := Zs) (H := X) (fun z' hz' x' hx' => by
        have hcomm : z' * x' = x' * z' :=
          hEcomm z' (by rw [hE]; exact Subgroup.mem_sup_left hz')
            x' (by rw [hE]; exact Subgroup.mem_sup_right hx')
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact hx')
    exact stableUnder_inf hJstabZs hfixXstab
  have hF0fix : F 0 ⊓ fixV Zs = ⊥ := by
    change (J ⊓ fixV (Dj 0 : Subgroup (MulAut W))) ⊓ fixV Zs = ⊥
    rw [hDj0, inf_assoc, ← w16g_fixV_sup X Zs]
    rw [show X ⊔ Zs = E by rw [hE]; exact sup_comm X Zs]
    exact hJfixE
  have hF0free : ∀ u ∈ F 0, z u = u → u = 1 := by
    intro u hu hzu
    have h1 : u ∈ F 0 ⊓ fixV Zs := by
      refine ⟨hu, ?_⟩
      rw [hZs]
      exact CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr hzu
    rw [hF0fix] at h1
    exact Subgroup.mem_bot.mp h1
  have hF0stabZ : ∀ u ∈ F 0, z u ∈ F 0 := fun u hu =>
    hF0stab z (by rw [hZs]; exact Subgroup.mem_zpowers z) u hu
  have hF0even : Even (rk (F 0)) :=
    w16h_even_rk_of_fixedFree hW2 hz3pow hF0stabZ hF0free
  have hF0ne : F 0 ≠ ⊥ := by
    intro hbot
    have hall : ∀ j : Fin 3, F j = ⊥ := fun j =>
      (rk_eq_zero_iff hW2).mp (by rw [hFrank j, hbot, rk_bot])
    have hJbot : J = ⊥ := by
      rw [hJ_eq, hfixZs, bot_sup_eq]
      exact iSup_eq_bot.mpr hall
    exact hJ1 hJbot
  have hF0pos : 0 < rk (F 0) := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hF0ne ((rk_eq_zero_iff hW2).mp h0)
  have hge2 : 2 ≤ rk (F 0) := by
    obtain ⟨m, hm⟩ := hF0even
    omega
  calc 6 = 3 * 2 := by norm_num
    _ ≤ 3 * rk (F 0) := Nat.mul_le_mul_left 3 hge2
    _ = rk ↥J := hrkJ.symm

theorem s13_W6_irreducible (hW : ∀ w : W, w * w = 1) {P : Subgroup (MulAut W)}
    (hP : IsPOnePlusTwo 3 ↥P) {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3)
    (hzc : ∀ y ∈ P, y * z = z * y)
    (hZP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers z)) = 6) :
    IsIrrOn P (commSub ⊤ (Subgroup.zpowers z)) ⊥ := by
  classical
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hodd : Odd (Nat.card (Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers, hz3]
    norm_num
  have hinf : fixV (Subgroup.zpowers z) ⊓ commSub ⊤ (Subgroup.zpowers z) = ⊥ :=
    CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW2 hodd
  unfold IsIrrOn
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro hbot
    have : rk ↥(commSub ⊤ (Subgroup.zpowers z)) = 0 := by rw [hbot, rk_bot]
    omega
  · intro y hy u hu
    exact CFSG.Quasithin.Asc81c.Pf.commSub_stable_of_commute
      (X := Subgroup.zpowers z) (c := y)
      (fun x hx => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact (show Commute y z from hzc y hy).zpow_right n) hu
  · intro y hy u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro J hJ hbotJ hJle
    by_cases hJbot : J = ⊥
    · exact Or.inl hJbot
    · refine Or.inr ?_
      have hfixJ : J ⊓ fixV (Subgroup.zpowers z) = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        have h1 : u ∈ fixV (Subgroup.zpowers z) ⊓ commSub ⊤ (Subgroup.zpowers z) :=
          ⟨hu.2, hJle hu.1⟩
        rw [hinf] at h1
        exact h1
      have h6 := s13_six_le_rk_of_stable hW hP hzP hz3 hzc hZP hJ hJbot hfixJ
      exact eq_of_le_of_rk_le hW2 hJle (by rw [hrk]; exact h6)

end CFSG.LocalAnalysis.WeakClosure81
