module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofW
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHJ
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarSetup
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofComp
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

theorem zpowers_eq_of_isLBConfig_conj
    (h415 : Sec4.Item4_15) {A B B' Lb Lb' : Subgroup G} {b d b' d' : G}
    (hA : Late.IsE27 A) (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (hB' : IsHyperplane A B') (hc' : IsLBConfig A B' b' d' Lb')
    {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G))
    (hWd : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hbw : Subgroup.zpowers b' = Subgroup.zpowers (w * b * w⁻¹)) :
    Subgroup.zpowers d = Subgroup.zpowers d' := by
  obtain ⟨-, hdB, -, hd1, -⟩ := Main148.lbConfig_points hB hA.2 hc
  obtain ⟨-, hd'B', -, hd'1, -⟩ := Main148.lbConfig_points hB' hA.2 hc'
  have hdA : d ∈ A := hB.1 hdB
  have hd'A : d' ∈ A := hB'.1 hd'B'
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have hLbw : Lb.map (MulAut.conj w).toMonoidHom ∈ lA A (w * b * w⁻¹) :=
    (map_conj_mem_lA_iff hw).mpr hLb
  rw [← lA_eq_of_zpowers_eq hbw, hc'.2.2.1, Set.mem_singleton_iff] at hLbw
  have hcent : IsThreeCentralIn Lb d := hc.2.2.2.2
  have hcent' := Item148PtRes.isThreeCentralIn_map_conj hcent w
  rw [hLbw] at hcent'
  have hJ2' := Item148HJ.j2_of_isLBConfig hc'
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hwdA : w * d * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw d).mp hdA
  have hwd1 : w * d * w⁻¹ ≠ 1 := by
    intro h0
    apply hd1
    calc d = w⁻¹ * (w * d * w⁻¹) * w := by group
      _ = 1 := by rw [h0]; group
  obtain ⟨hwdL, hc1⟩ := hcent'
  obtain ⟨hd'L, hc2⟩ := hc'.2.2.2.2
  have h1 := Item134SylowBarProof.zpowers_eq_of_central_of_quot_j2 h415 hJ2' hAp hwdA hd'A hwdL
    hd'L hwd1 hd'1 hc1 hc2
  have h2 : Subgroup.zpowers (w * d * w⁻¹) = Subgroup.zpowers d := by
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWd hw)
    rw [MonoidHom.map_zpowers] at h
    exact h
  rw [← h2, h1]

theorem pow_nine_mem_centralizer_of_mem_oThreeWPre {A : Subgroup G}
    (h9 : Nat.card (oThreeWStar A) = 9) {u : G} (hu : u ∈ oThreeWPre A) :
    u ∈ Subgroup.normalizer (A : Set G) ∧ ∀ y ∈ A, u ^ 9 * y * (u ^ 9)⁻¹ = y := by
  obtain ⟨n, hn, rfl⟩ := hu
  refine ⟨n.2, fun y hy => ?_⟩
  have hφ : (A.normalizerMonoidHom n) ^ 9 = 1 := by
    have h := orderOf_dvd_natCard (⟨A.normalizerMonoidHom n, hn⟩ : ↥(oThreeWStar A))
    rw [h9] at h
    have h' := orderOf_dvd_iff_pow_eq_one.mp h
    exact congrArg Subtype.val h'
  have h2 : (A.normalizerMonoidHom (n ^ 9)) ⟨y, hy⟩ = ⟨y, hy⟩ := by
    rw [map_pow, hφ]
    rfl
  have h3 := congrArg Subtype.val h2
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
  simpa using h3

theorem conj_eq_of_mem_oThreeWPre {A : Subgroup G} (hA : Late.IsE27 A)
    (h9 : Nat.card (oThreeWStar A) = 9)
    {u : G} (hu : u ∈ oThreeWPre A) {y : G} (hyA : y ∈ A) (hy1 : y ≠ 1)
    (huy : u * y * u⁻¹ ∈ Subgroup.zpowers y) : u * y * u⁻¹ = y := by
  obtain ⟨huN, hu9⟩ := pow_nine_mem_centralizer_of_mem_oThreeWPre h9 hu
  have hy3 : y ^ 3 = 1 := hA.1.2 y hyA
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp huy
  have hk' : u * y * u⁻¹ = y ^ (k % 3) := by
    rw [← hk]
    have h := zpow_mod_orderOf y k
    rw [hord] at h
    exact h.symm
  have hy2 : y * y = y⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc y * y * y = y ^ 3 := by rw [pow_three, mul_assoc]
      _ = 1 := hy3
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hk'
    apply hy1
    calc y = u⁻¹ * (u * y * u⁻¹) * u := by group
      _ = 1 := by rw [hk']; group
  · rw [h1, zpow_one] at hk'
    exact hk'
  · exfalso
    have hinv : u * y * u⁻¹ = y⁻¹ := by
      rw [hk', h2, ← hy2, zpow_two]
    have hinv' : u * y⁻¹ * u⁻¹ = y := by
      rw [show u * y⁻¹ * u⁻¹ = (u * y * u⁻¹)⁻¹ by group, hinv, inv_inv]
    have hsq : (u * u) * y * (u * u)⁻¹ = y := by
      calc (u * u) * y * (u * u)⁻¹ = u * (u * y * u⁻¹) * u⁻¹ := by group
        _ = y := by rw [hinv, hinv']
    have h8 : ∀ m : ℕ, (u * u) ^ m * y * ((u * u) ^ m)⁻¹ = y := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        calc (u * u) ^ (m + 1) * y * ((u * u) ^ (m + 1))⁻¹ =
            (u * u) * ((u * u) ^ m * y * ((u * u) ^ m)⁻¹) * (u * u)⁻¹ := by
              rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
          _ = y := by rw [ih, hsq]
    have h9' : u ^ 9 * y * (u ^ 9)⁻¹ = y⁻¹ := by
      have e : u ^ 9 = u * (u * u) ^ 4 := by
        rw [← pow_two, ← pow_mul, ← pow_succ']
      calc u ^ 9 * y * (u ^ 9)⁻¹ = u * ((u * u) ^ 4 * y * ((u * u) ^ 4)⁻¹) * u⁻¹ := by
            rw [e]; group
        _ = y⁻¹ := by rw [h8 4, hinv]
    rw [hu9 y hyA] at h9'
    apply hy1
    have hyy : y * y = 1 := by
      calc y * y = y * y⁻¹ := by rw [← h9']
        _ = 1 := mul_inv_cancel y
    calc y = y ^ 3 * (y * y)⁻¹ := by group
      _ = 1 := by rw [hy3, hyy]; group

theorem card_le_of_le_isE27 {A H : Subgroup G} (hA : Late.IsE27 A) (hHA : H ≤ A) :
    Nat.card H = 1 ∨ Nat.card H = 3 ∨ Nat.card H = 9 ∨ Nat.card H = 27 := by
  have h := Subgroup.card_dvd_of_le hHA
  rw [hA.2, show (27 : ℕ) = 3 ^ 3 by norm_num] at h
  obtain ⟨i, hi, hiH⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h
  rw [hiH]
  interval_cases i <;> norm_num

theorem sup_sup_zpowers_eq {A : Subgroup G} (hA : Late.IsE27 A) {d d' x : G} (hdA : d ∈ A)
    (hd'A : d' ∈ A) (hxA : x ∈ A) (hd1 : d ≠ 1) (hd'1 : d' ≠ 1)
    (hne : Subgroup.zpowers d ≠ Subgroup.zpowers d')
    (hx : x ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers d') :
    Subgroup.zpowers d ⊔ Subgroup.zpowers d' ⊔ Subgroup.zpowers x = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := Subgroup.zpowers d ⊔ Subgroup.zpowers d' with hD
  have hDA : D ≤ A := sup_le (Subgroup.zpowers_le.mpr hdA) (Subgroup.zpowers_le.mpr hd'A)
  have hXA : D ⊔ Subgroup.zpowers x ≤ A := sup_le hDA (Subgroup.zpowers_le.mpr hxA)
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (hA.1.2 d hdA) hd1
  have hd'3 : Nat.card (Subgroup.zpowers d') = 3 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (hA.1.2 d' hd'A) hd'1
  have hd'D : d' ∉ Subgroup.zpowers d := by
    intro h
    apply hne
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h)
      (by rw [hd3, hd'3])).symm
  have hlt : Subgroup.zpowers d < D := by
    refine lt_of_le_of_ne le_sup_left fun h => hd'D ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d')
  have hD9 : 9 ≤ Nat.card D := by
    have h1 : Nat.card (Subgroup.zpowers d) < Nat.card D := Subgroup.card_lt_of_lt hlt
    rw [hd3] at h1
    rcases card_le_of_le_isE27 hA hDA with h | h | h | h <;> omega
  have hlt2 : D < D ⊔ Subgroup.zpowers x := by
    refine lt_of_le_of_ne le_sup_left fun h => hx ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have h2 : Nat.card D < Nat.card ↥(D ⊔ Subgroup.zpowers x) := Subgroup.card_lt_of_lt hlt2
  refine Subgroup.eq_of_le_of_card_ge hXA ?_
  rw [hA.2]
  rcases card_le_of_le_isE27 hA hXA with h | h | h | h <;> omega

omit [Finite G] in
theorem conj_eq_iff_mem_centralizer_singleton {u y : G} :
    u * y * u⁻¹ = y ↔ y ∈ Subgroup.centralizer ({u} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem orbitIn_eq_singleton_or_nine_le {A : Subgroup G} (hA : Late.IsE27 A)
    (h9 : Nat.card (oThreeWStar A) = 9) {d d' : G} (hdA : d ∈ A) (hd'A : d' ∈ A)
    (hd1 : d ≠ 1) (hd'1 : d' ≠ 1) (hne : Subgroup.zpowers d ≠ Subgroup.zpowers d')
    (hWd : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hWd' : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d' : Set G))
    {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1) :
    orbitIn (oThreeWPre A) (Subgroup.zpowers x) = {Subgroup.zpowers x} ∨
      9 ≤ (orbitIn (oThreeWPre A) (Subgroup.zpowers x)).ncard := by
  have hmemN : ∀ {u : G} {y : G}, u ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) →
      u * y * u⁻¹ ∈ Subgroup.zpowers y := fun hu =>
    (Subgroup.mem_normalizer_iff.mp hu _).mp (Subgroup.mem_zpowers _)
  have hfix : ∀ u ∈ oThreeWPre A, u * d * u⁻¹ = d ∧ u * d' * u⁻¹ = d' := fun u hu =>
    ⟨conj_eq_of_mem_oThreeWPre hA h9 hu hdA hd1
        (hmemN (hWd (pow_nine_mem_centralizer_of_mem_oThreeWPre h9 hu).1)),
      conj_eq_of_mem_oThreeWPre hA h9 hu hd'A hd'1
        (hmemN (hWd' (pow_nine_mem_centralizer_of_mem_oThreeWPre h9 hu).1))⟩
  have hfixD : ∀ u ∈ oThreeWPre A, Subgroup.zpowers d ⊔ Subgroup.zpowers d' ≤
      Subgroup.centralizer ({u} : Set G) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hfix u hu
    exact sup_le (Subgroup.zpowers_le.mpr (conj_eq_iff_mem_centralizer_singleton.mp h1))
      (Subgroup.zpowers_le.mpr (conj_eq_iff_mem_centralizer_singleton.mp h2))
  by_cases hxD : x ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers d'
  · left
    ext F
    simp only [orbitIn, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hux : u * x * u⁻¹ = x :=
        conj_eq_iff_mem_centralizer_singleton.mpr (hfixD u hu hxD)
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (u * x * u⁻¹) = _
      rw [hux]
    · rintro rfl
      refine ⟨1, (oThreeWPre A).one_mem, ?_⟩
      rw [MonoidHom.map_zpowers]
      change _ = Subgroup.zpowers (1 * x * 1⁻¹)
      simp
  · right
    have hlift : ∀ φ : ↥(oThreeWStar A), ∃ n : ↥(Subgroup.normalizer (A : Set G)),
        A.normalizerMonoidHom n = φ := by
      intro φ
      have hφW : (φ : MulAut ↥A) ∈ wStar A := by
        obtain ⟨ψ, -, hψ⟩ := φ.2
        rw [← hψ]
        exact ψ.2
      obtain ⟨n, -, hn⟩ := hφW
      exact ⟨n, hn⟩
    choose nφ hnφ using hlift
    set f : ↥(oThreeWStar A) → Subgroup G :=
      fun φ => (Subgroup.zpowers x).map (MulAut.conj ((nφ φ : G))).toMonoidHom with hf
    have hfP : ∀ φ, ((nφ φ : G)) ∈ oThreeWPre A := fun φ =>
      ⟨nφ φ, (show A.normalizerMonoidHom (nφ φ) ∈ oThreeWStar A by rw [hnφ φ]; exact φ.2), rfl⟩
    have hfmem : ∀ φ, f φ ∈ orbitIn (oThreeWPre A) (Subgroup.zpowers x) := fun φ =>
      ⟨_, hfP φ, rfl⟩
    have hfinj : Function.Injective f := by
      intro φ ψ hfφψ
      set u : G := ((nφ ψ : G))⁻¹ * (nφ φ : G) with hu
      have huP : u ∈ oThreeWPre A := (oThreeWPre A).mul_mem ((oThreeWPre A).inv_mem (hfP ψ)) (hfP φ)
      have huN : u ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
        Item148Res5.map_conj_eq_map_conj_iff.mp hfφψ.symm
      have hux : u * x * u⁻¹ = x := conj_eq_of_mem_oThreeWPre hA h9 huP hxA hx1 (hmemN huN)
      have hA' : A ≤ Subgroup.centralizer ({u} : Set G) := by
        rw [← sup_sup_zpowers_eq hA hdA hd'A hxA hd1 hd'1 hne hxD]
        exact sup_le (hfixD u huP)
          (Subgroup.zpowers_le.mpr (conj_eq_iff_mem_centralizer_singleton.mp hux))
      have hn : A.normalizerMonoidHom (nφ ψ) = A.normalizerMonoidHom (nφ φ) := by
        ext a
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
          Subgroup.normalizerMonoidHom_apply_apply_coe]
        have h := conj_eq_iff_mem_centralizer_singleton.mpr (hA' a.2)
        rw [hu] at h
        calc (nφ ψ : G) * a * ((nφ ψ : G))⁻¹ =
            (nφ ψ : G) * ((((nφ ψ : G))⁻¹ * (nφ φ : G)) * a * (((nφ ψ : G))⁻¹ * (nφ φ : G))⁻¹) *
              ((nφ ψ : G))⁻¹ := by rw [h]
          _ = (nφ φ : G) * a * ((nφ φ : G))⁻¹ := by group
      rw [hnφ φ, hnφ ψ] at hn
      exact (Subtype.ext hn).symm
    have hfin : (orbitIn (oThreeWPre A) (Subgroup.zpowers x)).Finite := Set.toFinite _
    have hcard : Nat.card ↥(oThreeWStar A) ≤
        Nat.card ↥(orbitIn (oThreeWPre A) (Subgroup.zpowers x)) := by
      have : Finite ↥(orbitIn (oThreeWPre A) (Subgroup.zpowers x)) := hfin.to_subtype
      exact Nat.card_le_card_of_injective (fun φ => ⟨f φ, hfmem φ⟩)
        fun φ ψ h => hfinj (congrArg Subtype.val h)
    rw [h9, Nat.card_coe_set_eq] at hcard
    exact hcard

theorem zpowers_eq_of_isLBConfig
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {B B' Lb Lb' : Subgroup G} {b d b' d' : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (hB' : IsHyperplane A B') (hc' : IsLBConfig A B' b' d' Lb') :
    Subgroup.zpowers d = Subgroup.zpowers d' := by
  by_contra hne
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := h.isE27
  have hW := HJRes148.normalizer_le_normalizer_zpowers_d h134 h48 h hB hc
  have hW' := HJRes148.normalizer_le_normalizer_zpowers_d h134 h48 h hB' hc'
  have hc0 := hc
  have hJ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  obtain ⟨-, hd'1⟩ := hc'.ne_one hB' hA
  obtain ⟨-, hdB, -, -, -⟩ := Main148.lbConfig_points hB hA.2 hc
  obtain ⟨-, hd'B', -, -, -⟩ := Main148.lbConfig_points hB' hA.2 hc'
  have hdA : d ∈ A := hB.1 hdB
  have hd'A : d' ∈ A := hB'.1 hd'B'
  obtain ⟨hBbd, hbΩ, hLbeq, -, hdL, S, hdS, hSd⟩ := hc
  have hLb : Lb ∈ lA A b := hLbeq ▸ Set.mem_singleton Lb
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
  have hb'Ω : Subgroup.zpowers b' ∈ omegaA A := hc'.2.1
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1
    ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hbA hdA hb1 hLb.1 hJq
  have hdata : Sec13Data G A b Lb :=
    { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
  rcases h134 G A b Lb hdata hJ d hdA hd1 ⟨_, hS⟩ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, -, -, h9, -, hΩ⟩ | ⟨-, -, hΩ, -⟩
  ·
    apply hne
    rw [h1, Set.mem_singleton_iff] at hb'Ω
    refine zpowers_eq_of_isLBConfig_conj h415 hA hB hc0 hB' hc'
      (Subgroup.normalizer (A : Set G)).one_mem hW ?_
    rw [hb'Ω]
    congr 1
    group
  ·
    have hor := fun {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1) =>
      orbitIn_eq_singleton_or_nine_le hA h9 hdA hd'A hd1 hd'1 hne hW hW' hxA hx1
    have hfinΩ : (omegaA A).Finite := Set.toFinite _
    rcases hΩ with ⟨hΩeq, hΩ3⟩ | ⟨-, -, -, -, a, ha, had, hΩeq, hΩ6, -⟩
    · rcases hor hbA hb1 with h1 | h1
      · rw [hΩeq, h1, Set.ncard_singleton] at hΩ3
        omega
      · rw [hΩeq] at hΩ3
        omega
    · have ha1 : a ≠ 1 := fun h0 => had (h0 ▸ Subgroup.one_mem _)
      have hle1 : (orbitIn (oThreeWPre A) (Subgroup.zpowers b)).ncard ≤ (omegaA A).ncard :=
        Set.ncard_le_ncard (hΩeq ▸ Set.subset_union_left) hfinΩ
      have hle2 : (orbitIn (oThreeWPre A) (Subgroup.zpowers a)).ncard ≤ (omegaA A).ncard :=
        Set.ncard_le_ncard (hΩeq ▸ Set.subset_union_right) hfinΩ
      rcases hor hbA hb1 with h1 | h1
      · rcases hor ha.1 ha1 with h2 | h2
        · rw [hΩeq, h1, h2] at hΩ6
          have := Set.ncard_union_le ({Subgroup.zpowers b} : Set (Subgroup G))
            {Subgroup.zpowers a}
          rw [hΩ6, Set.ncard_singleton, Set.ncard_singleton] at this
          omega
        · omega
      · omega
  ·
    apply hne
    rw [hΩ] at hb'Ω
    obtain ⟨w, hw, hbw⟩ := hb'Ω
    refine zpowers_eq_of_isLBConfig_conj h415 hA hB hc0 hB' hc' hw hW ?_
    rw [hbw, MonoidHom.map_zpowers]
    rfl

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
