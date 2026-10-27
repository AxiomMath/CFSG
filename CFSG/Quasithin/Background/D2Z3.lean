module

public import CFSG.Quasithin.Background.D2Z2
public import CFSG.Quasithin.Background.D2Z1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

theorem three_group_card_dvd_nine_le (hV : ∀ v : V, v ^ 2 = 1) (hrk : rk V ≤ 4)
    {P : Subgroup (MulAut V)} (hP : IsPGroup 3 P) : Nat.card P ∣ 9 := by
  have hdvd : Nat.card P ∣ Nat.card (MulAut V) := Subgroup.card_subgroup_dvd_card P
  rw [card_mulAut_eq hV] at hdvd
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  rw [ha] at hdvd ⊢
  have ha2 : a ≤ 2 := by
    by_contra h
    have h3 : 3 ^ 3 ∣ 3 ^ a := pow_dvd_pow 3 (by omega)
    have h4 := h3.trans hdvd
    have hprod : ∀ d ≤ 4, ¬ (27 ∣ ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ))) := by decide
    exact hprod (rk V) hrk (by simpa using h4)
  exact pow_dvd_pow 3 ha2

omit [Finite V] in
theorem comm_of_card_dvd_nine {G : Type*} [Group G] (h : Nat.card G ∣ 9) (x y : G) :
    x * y = y * x := by
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9] at h
  have hp : Nat.Prime 3 := by norm_num
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).mp h
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  interval_cases i
  · have h1 : Nat.card G = 1 := by simpa using hi'
    have := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  · have : IsCyclic G := isCyclic_of_prime_card (p := 3) (by simpa using hi')
    exact (inferInstance : IsMulCommutative G).is_comm.comm x y
  · have : IsMulCommutative G := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
      (by simpa using hi')
    exact this.is_comm.comm x y

theorem comm_mem_centSub_of_small (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V} (hU : rk U ≤ 4)
    {Pp : Subgroup (MulAut V)} (hP : IsPGroup 3 Pp) (hinv : ∀ g ∈ Pp, ∀ u ∈ U, g u ∈ U)
    {g g' : MulAut V} (hg : g ∈ Pp) (hg' : g' ∈ Pp) : g * g' * g⁻¹ * g'⁻¹ ∈ centSub U := by
  have hPs : Pp ≤ stabSub U := fun x hx =>
    mem_stabSub_of_zpowers (fun y hy w hw => hinv y (Subgroup.zpowers_le.mpr hx hy) w hw)
  have hK : IsPGroup 3 ↥(Pp.subgroupOf (stabSub U)) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPs).symm
  have hΓ : IsPGroup 3 ↥((Pp.subgroupOf (stabSub U)).map (resHom U)) := hK.map (resHom U)
  have hVU : ∀ w : U, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have hcard : Nat.card ((Pp.subgroupOf (stabSub U)).map (resHom U)) ∣ 9 :=
    three_group_card_dvd_nine_le hVU hU hΓ
  have hsK : (⟨g, hPs hg⟩ : stabSub U) ∈ Pp.subgroupOf (stabSub U) := hg
  have hs'K : (⟨g', hPs hg'⟩ : stabSub U) ∈ Pp.subgroupOf (stabSub U) := hg'
  have hxx := comm_of_card_dvd_nine hcard
    ⟨resHom U ⟨g, hPs hg⟩, Subgroup.mem_map_of_mem _ hsK⟩
    ⟨resHom U ⟨g', hPs hg'⟩, Subgroup.mem_map_of_mem _ hs'K⟩
  have hxx' : resHom U ⟨g, hPs hg⟩ * resHom U ⟨g', hPs hg'⟩ =
      resHom U ⟨g', hPs hg'⟩ * resHom U ⟨g, hPs hg⟩ := congrArg Subtype.val hxx
  rw [mem_centSub]
  intro u hu
  have key : resHom U (⟨g, hPs hg⟩ * ⟨g', hPs hg'⟩ * ⟨g, hPs hg⟩⁻¹ * ⟨g', hPs hg'⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc resHom U ⟨g, hPs hg⟩ * resHom U ⟨g', hPs hg'⟩ * (resHom U ⟨g, hPs hg⟩)⁻¹ *
          (resHom U ⟨g', hPs hg'⟩)⁻¹
        = (resHom U ⟨g', hPs hg'⟩ * resHom U ⟨g, hPs hg⟩) * (resHom U ⟨g, hPs hg⟩)⁻¹ *
          (resHom U ⟨g', hPs hg'⟩)⁻¹ := by rw [hxx']
      _ = 1 := by group
  have h2 := congrArg (fun φ : MulAut U => ((φ ⟨u, hu⟩ : U) : V)) key
  exact h2

omit [Finite V] in
theorem KleinData.exists_partner {A : Subgroup (MulAut V)} {a b : MulAut V} (k : KleinData A a b)
    {t : MulAut V} (ht : t ∈ A) (ht1 : t ≠ 1) : ∃ t' : MulAut V, KleinData A t t' := by
  rcases k.mem t ht with e | e | e | e
  · exact absurd e ht1
  · exact ⟨b, e ▸ k⟩
  · exact ⟨a, e ▸ k.symm⟩
  · exact ⟨a, e ▸ k.third.symm⟩

omit [Finite V] in
theorem exists_eigen {A N : Subgroup (MulAut V)} {a b : MulAut V} (k : KleinData A a b)
    (hN : ∀ g ∈ A, ∀ y ∈ N, g * y * g⁻¹ ∈ N) (hcomm : ∀ y ∈ N, ∀ z ∈ N, y * z = z * y)
    (hne : N ≠ ⊥) : ∃ t ∈ A, t ≠ 1 ∧ ∃ y ∈ N, y ≠ 1 ∧ t * y = y * t := by
  obtain ⟨w, hw⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hw' : (w : MulAut V) ∈ N := w.2
  have hw1 : (w : MulAut V) ≠ 1 := fun e => hw (Subtype.ext e)
  have key : ∀ g ∈ A, g ^ 2 = 1 → ∀ y ∈ N,
      g * (y * (g * y * g⁻¹)) = (y * (g * y * g⁻¹)) * g := by
    intro g hg hg2 y hy
    have hgy : g * y * g⁻¹ ∈ N := hN g hg y hy
    have hgg : g * g = 1 := by rw [← pow_two]; exact hg2
    have e : g * (y * (g * y * g⁻¹)) * g⁻¹ = (g * y * g⁻¹) * y := by
      have : g * (y * (g * y * g⁻¹)) * g⁻¹ = (g * y * g⁻¹) * ((g * g) * y * (g * g)⁻¹) := by group
      rw [this, hgg]; simp
    have e2 : (g * y * g⁻¹) * y = y * (g * y * g⁻¹) := hcomm _ hgy y hy
    rw [e2] at e
    exact mul_inv_eq_iff_eq_mul.mp e
  by_cases h1 : ∃ y ∈ N, y * (a * y * a⁻¹) ≠ 1
  · obtain ⟨y, hy, hy1⟩ := h1
    exact ⟨a, k.ha, k.ha1, y * (a * y * a⁻¹), N.mul_mem hy (hN a k.ha y hy), hy1,
      key a k.ha k.ha2 y hy⟩
  · push Not at h1
    by_cases h2 : ∃ y ∈ N, y * (b * y * b⁻¹) ≠ 1
    · obtain ⟨y, hy, hy1⟩ := h2
      exact ⟨b, k.hb, k.hb1, y * (b * y * b⁻¹), N.mul_mem hy (hN b k.hb y hy), hy1,
        key b k.hb k.hb2 y hy⟩
    · push Not at h2
      refine ⟨a * b, A.mul_mem k.ha k.hb, k.third.hb1, w, hw', hw1, ?_⟩
      have e1 : a * (w : MulAut V) * a⁻¹ = (w : MulAut V)⁻¹ :=
        eq_inv_of_mul_eq_one_right (h1 w hw')
      have e2 : b * (w : MulAut V) * b⁻¹ = (w : MulAut V)⁻¹ :=
        eq_inv_of_mul_eq_one_right (h2 w hw')
      calc a * b * (w : MulAut V)
          = a * (b * (w : MulAut V) * b⁻¹) * a⁻¹ * (a * b) := by group
        _ = a * (w : MulAut V)⁻¹ * a⁻¹ * (a * b) := by rw [e2]
        _ = (a * (w : MulAut V) * a⁻¹)⁻¹ * (a * b) := by group
        _ = (w : MulAut V) * (a * b) := by rw [e1, inv_inv]

section D214

variable {X A : Subgroup (MulAut V)} {r : ℚ}

theorem commV_centR_facts (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {a b : MulAut V}
    (k : KleinData A a b) (hne : centR X a ≠ ⊥) :
    rk (commV (centR X a) ⊓ fixV (Subgroup.zpowers a) : Subgroup V) = 2 ∧
      rk (commV (centR X a)) ≤ 4 ∧ Even (rk (commV (centR X a))) ∧ 2 ≤ rk (commV (centR X a)) := by
  obtain ⟨hcard, hrk2⟩ := centR_data hV h k hne
  have hQodd : Odd (Nat.card (centR X a)) := by rw [hcard]; exact ⟨1, rfl⟩
  have hcomm : ∀ q ∈ centR X a, q * a = a * q := fun q hq => (mem_centR.mp hq).2
  have hE := commSub_fixV_eq hV hQodd hcomm
  rw [hE] at hrk2
  have hinv : ∀ x ∈ Subgroup.zpowers a, ∀ w ∈ commV (centR X a), x w ∈ commV (centR X a) := by
    intro x hx w hw
    refine commV_smul_mem (fun q hq => ?_) hw
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute a q := (hcomm q hq).symm
    have : a ^ j * q * (a ^ j)⁻¹ = q := by
      rw [(hc.zpow_left j).eq, mul_inv_cancel_right]
    rw [this]; exact hq
  have h1 := rk_commSub_add_rk_inf_fixV hinv
  have h2 := rk_mono (commSub_zpowers_le_inf_fixV hV k.ha2 hinv)
  have h3 : 2 ≤ rk (commV (centR X a)) := by
    have := rk_mono (inf_le_left : commV (centR X a) ⊓ fixV (Subgroup.zpowers a) ≤ commV (centR X a))
    omega
  refine ⟨hrk2, by omega, (commV_card_three hV hcard).2.2.2, h3⟩

omit [Finite V] in
theorem commutator_comm_le_of_normal {P : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ y ∈ P, g * y * g⁻¹ ∈ P) :
    ⁅P, P⁆ ≤ (⁅P, P⁆).comap (MulAut.conj g).toMonoidHom := by
  refine Subgroup.commutator_le.mpr fun u hu v hv => ?_
  show g * ⁅u, v⁆ * g⁻¹ ∈ ⁅P, P⁆
  have : g * ⁅u, v⁆ * g⁻¹ = ⁅g * u * g⁻¹, g * v * g⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  rw [this]
  exact Subgroup.commutator_mem_commutator (hg u hu) (hg v hv)

theorem pCoreOf_comm (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    ∀ x ∈ pCoreOf 3 X, ∀ y ∈ pCoreOf 3 X, x * y = y * x := by
  by_contra hnc
  push Not at hnc
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ := hnc
  obtain ⟨a, b, k⟩ := h.exists_klein hV
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set P := pCoreOf 3 X with hP
  have hnil : Group.IsNilpotent ↥P := (pCoreOf_isPGroup 3 X).isNilpotent
  have hcne : commutator ↥P ≠ ⊥ := by
    intro hbot
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    have h1 := Subgroup.mem_centralizer_iff.mp (hbot (Subgroup.mem_top (⟨x₀, hx₀⟩ : ↥P)))
      ⟨y₀, hy₀⟩ (Subgroup.mem_top _)
    exact hxy (congrArg Subtype.val h1).symm
  have hinfc := Group.IsNilpotent.inf_center_ne_bot_of_normal hcne
  obtain ⟨n, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hinfc
  have hnC : (n : ↥P) ∈ commutator ↥P := n.2.1
  have hnZ : (n : ↥P) ∈ Subgroup.center ↥P := n.2.2
  set N : Subgroup (MulAut V) :=
    ⁅P, P⁆ ⊓ (P ⊓ Subgroup.centralizer (P : Set (MulAut V))) with hN
  have hwN : ((n : ↥P) : MulAut V) ∈ N := by
    refine ⟨?_, (n : ↥P).2, ?_⟩
    · have hmap : (commutator ↥P).map P.subtype ≤ ⁅P, P⁆ := by
        have e : (⊤ : Subgroup P).map P.subtype = P := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
        rw [commutator_def, Subgroup.map_commutator, e]
      exact hmap ⟨(n : ↥P), hnC, rfl⟩
    · refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
      have := Subgroup.mem_center_iff.mp hnZ ⟨g, hg⟩
      exact congrArg Subtype.val this
  have hNne : N ≠ ⊥ := by
    intro hbot
    rw [hbot] at hwN
    exact hn1 (Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp hwN)))
  have hNinv : ∀ g ∈ A, ∀ y ∈ N, g * y * g⁻¹ ∈ N := by
    intro g hg y hy
    obtain ⟨hy1, hy2, hy3⟩ := hy
    refine ⟨?_, h.conj_mem hg hy2, ?_⟩
    · exact commutator_comm_le_of_normal (fun u hu => h.conj_mem hg hu) hy1
    · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      have hz' : g⁻¹ * z * g ∈ P := by
        have := h.conj_mem (A.inv_mem hg) hz
        simpa using this
      have e := Subgroup.mem_centralizer_iff.mp hy3 _ hz'
      calc z * (g * y * g⁻¹) = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by rw [e]
        _ = (g * y * g⁻¹) * z := by group
  obtain ⟨t, htA, ht1, y, hyN, hy1, hty⟩ := exists_eigen k hNinv
    (fun y hy z hz => Subgroup.mem_centralizer_iff.mp hz.2.2 y hy.2.1) hNne
  obtain ⟨t', kt⟩ := k.exists_partner htA ht1
  have hyC : y ∈ centR X t := mem_centR.mpr ⟨hyN.2.1, hty.symm⟩
  have hCne : centR X t ≠ ⊥ := by
    intro hbot
    rw [hbot] at hyC
    exact hy1 (Subgroup.mem_bot.mp hyC)
  obtain ⟨hcard, -⟩ := centR_data hV h kt hCne
  have hz : Subgroup.zpowers y = centR X t := zpowers_eq_of_prime_card hcard hyC hy1
  have hQN : centR X t ≤ N := by
    rw [← hz]
    exact Subgroup.zpowers_le.mpr hyN
  obtain ⟨-, hU4, -, -⟩ := commV_centR_facts hV h kt hCne
  have hUinv : ∀ g ∈ P, ∀ u ∈ commV (centR X t), g u ∈ commV (centR X t) := by
    intro g hg u hu
    refine commV_smul_mem (fun q hq => ?_) hu
    have hc := Subgroup.mem_centralizer_iff.mp (hQN hq).2.2 g hg
    rw [hc, mul_inv_cancel_right]
    exact hq
  have hcent : ⁅P, P⁆ ≤ centSub (commV (centR X t)) := by
    refine Subgroup.commutator_le.mpr fun g hg g' hg' => ?_
    exact comm_mem_centSub_of_small hV hU4 (pCoreOf_isPGroup 3 X) hUinv hg hg'
  have hQodd : Odd (Nat.card (centR X t)) := by rw [hcard]; exact ⟨1, rfl⟩
  have hdec := (coprime_decomp hQodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)).1
  have hyone : y = 1 := by
    ext v
    have hv : v ∈ commSub ⊤ (centR X t) ⊔ (⊤ ⊓ fixV (centR X t)) := by
      rw [hdec]; exact Subgroup.mem_top v
    obtain ⟨c, hc, f, hf, rfl⟩ := Subgroup.mem_sup.mp hv
    have hcV : c ∈ commV (centR X t) := by rwa [commV_eq_commSub]
    have h1 : y c = c := (mem_centSub.mp (hcent (hQN hyC).1)) c hcV
    have h2 : y f = f := hf.2 y hyC
    simp [map_mul, h1, h2]
  exact hy1 hyone

end D214

end CFSG.Quasithin
