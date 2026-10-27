module

public import CFSG.RankThree.PartTwo.Sec10.HWNormalizes
public import CFSG.RankThree.PartTwo.Sec12.Item125DiagSLE81
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
public import CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct
public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofInner

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]


theorem commutator_mem_theta_sSup {d : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d) {Kd : Subgroup G} (hKd : Kd ∈ thetaComponentsAt 3 d)
    (hKd𝒳 : Kd ∉ 𝒳) {k x : G} (hkKd : k ∈ Kd) (hkX : k ∈ sSup 𝒳) (hxX : x ∈ sSup 𝒳) :
    k * x * k⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) := by
  set H := Subgroup.centralizer ({d} : Set G) with hH
  have hXH : sSup 𝒳 ≤ H :=
    sSup_le fun Y hY => Sec6.le_centralizer_of_mem_thetaComponentsAt (h𝒳 hY)
  have hkH : k ∈ H := hXH hkX
  set θH : Subgroup ↥H := aschbacherSolvableCore 3 ↥H with hθH
  set mk : ↥H →* (↥H ⧸ θH) := QuotientGroup.mk' θH with hmk
  have hYle : ∀ Y ∈ 𝒳, Y ≤ ((Subgroup.centralizer ({mk ⟨k, hkH⟩} : Set (↥H ⧸ θH))).comap
      mk).map H.subtype := by
    intro Y hY y hy
    have hyH : y ∈ H := hXH (le_sSup hY hy)
    have hne : Kd ≠ Y := fun h => hKd𝒳 (h ▸ hY)
    have hcomm : k * y * k⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) H :=
      Sec10.commutator_mem_theta_of_ne hKd (h𝒳 hY) hne hkKd hy
    have hHmem : k * y * k⁻¹ * y⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem hkH hyH) (H.inv_mem hkH)) (H.inv_mem hyH)
    obtain ⟨u, hu, hue⟩ := hcomm
    have huel : (⟨k * y * k⁻¹ * y⁻¹, hHmem⟩ : ↥H) = u := Subtype.ext hue.symm
    have hθmem : (⟨k * y * k⁻¹ * y⁻¹, hHmem⟩ : ↥H) ∈ θH := huel ▸ hu
    have hzero : mk (⟨k * y * k⁻¹ * y⁻¹, hHmem⟩ : ↥H) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hθmem
    have hsplit : (⟨k, hkH⟩ : ↥H) * ⟨y, hyH⟩ =
        (⟨k * y * k⁻¹ * y⁻¹, hHmem⟩ : ↥H) * (⟨y, hyH⟩ * ⟨k, hkH⟩) := by
      ext
      simp only [Subgroup.coe_mul]
      group
    have hcommute : mk ⟨k, hkH⟩ * mk ⟨y, hyH⟩ = mk ⟨y, hyH⟩ * mk ⟨k, hkH⟩ := by
      rw [← map_mul, ← map_mul, hsplit, map_mul, hzero, one_mul]
    exact ⟨⟨y, hyH⟩, Subgroup.mem_comap.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr hcommute.symm), rfl⟩
  have hZle : sSup 𝒳 ≤ ((Subgroup.centralizer ({mk ⟨k, hkH⟩} : Set (↥H ⧸ θH))).comap
      mk).map H.subtype := sSup_le hYle
  obtain ⟨u, hu, hue⟩ := hZle hxX
  have hxH : x ∈ H := hXH hxX
  have hux : u = ⟨x, hxH⟩ := Subtype.ext hue
  have hcent : mk ⟨x, hxH⟩ ∈ Subgroup.centralizer ({mk ⟨k, hkH⟩} : Set (↥H ⧸ θH)) :=
    hux ▸ Subgroup.mem_comap.mp hu
  have hcommute : mk ⟨x, hxH⟩ * mk ⟨k, hkH⟩ = mk ⟨k, hkH⟩ * mk ⟨x, hxH⟩ :=
    Subgroup.mem_centralizer_singleton_iff.mp hcent
  have hxHmem : k * x * k⁻¹ * x⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem hkH hxH) (H.inv_mem hkH)) (H.inv_mem hxH)
  have hmk_eq : mk (⟨k, hkH⟩ * ⟨x, hxH⟩) = mk (⟨x, hxH⟩ * ⟨k, hkH⟩) := by
    rw [map_mul, map_mul]
    exact hcommute.symm
  have hdiv : ((⟨k, hkH⟩ * ⟨x, hxH⟩) / (⟨x, hxH⟩ * ⟨k, hkH⟩) : ↥H) ∈ θH :=
    QuotientGroup.eq_iff_div_mem.mp hmk_eq
  have hdivel : ((⟨k, hkH⟩ * ⟨x, hxH⟩) / (⟨x, hxH⟩ * ⟨k, hkH⟩) : ↥H) =
      (⟨k * x * k⁻¹ * x⁻¹, hxHmem⟩ : ↥H) := by
    ext
    simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv,
      mul_inv_rev]
    group
  have hθmem : (⟨k * x * k⁻¹ * x⁻¹, hxHmem⟩ : ↥H) ∈ θH := hdivel ▸ hdiv
  refine Sec12.Item125Diag.inf_le_inSubgroup_theta hXH ⟨?_, ?_⟩
  · exact Subgroup.mem_map_of_mem H.subtype hθmem
  · exact (sSup 𝒳).mul_mem ((sSup 𝒳).mul_mem ((sSup 𝒳).mul_mem hkX hxX)
      ((sSup 𝒳).inv_mem hkX)) ((sSup 𝒳).inv_mem hxX)

theorem mk_mem_center_of_not_mem {d : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d) {Kd : Subgroup G} (hKd : Kd ∈ thetaComponentsAt 3 d)
    (hKd𝒳 : Kd ∉ 𝒳) {B : Subgroup G} (hBK : B ≤ Kd) (hBX : B ≤ sSup 𝒳) :
    ∀ b : ↥B, (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(sSup 𝒳)))
        (Subgroup.inclusion hBX b) ∈
      Subgroup.center (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)) := by
  set X := sSup 𝒳 with hX
  set θXc : Subgroup ↥X := aschbacherSolvableCore 3 ↥X with hθXc
  set mk : ↥X →* (↥X ⧸ θXc) := QuotientGroup.mk' θXc with hmk
  intro b
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θXc q
  have hcomm : (b : G) * x * (b : G)⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) X :=
    commutator_mem_theta_sSup h𝒳 hKd hKd𝒳 (hBK b.2) (hBX b.2) x.2
  have hXmem : (b : G) * x * (b : G)⁻¹ * x⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem (X.mul_mem (hBX b.2) x.2) (X.inv_mem (hBX b.2))) (X.inv_mem x.2)
  obtain ⟨u, hu, hue⟩ := hcomm
  have huel : (⟨(b : G) * x * (b : G)⁻¹ * x⁻¹, hXmem⟩ : ↥X) = u := Subtype.ext hue.symm
  have hθmem : (⟨(b : G) * x * (b : G)⁻¹ * x⁻¹, hXmem⟩ : ↥X) ∈ θXc := huel ▸ hu
  have hzero : mk (⟨(b : G) * x * (b : G)⁻¹ * x⁻¹, hXmem⟩ : ↥X) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hθmem
  have hsplit : (⟨b, hBX b.2⟩ : ↥X) * x =
      (⟨(b : G) * x * (b : G)⁻¹ * x⁻¹, hXmem⟩ : ↥X) * (x * ⟨b, hBX b.2⟩) := by
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hq : mk ((⟨b, hBX b.2⟩ : ↥X) * x) = mk (x * ⟨b, hBX b.2⟩) := by
    rw [hsplit, map_mul, hzero, one_mul]
  show mk x * mk (Subgroup.inclusion hBX b) = mk (Subgroup.inclusion hBX b) * mk x
  rw [← map_mul, ← map_mul]
  exact hq.symm

theorem eq_one_of_mk_inclusion_eq_one {X B : Subgroup G} (hBX : B ≤ X) (hB3 : IsPGroup 3 B)
    {b : ↥B} (hb : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))
      (Subgroup.inclusion hBX b) = 1) : b = 1 := by
  have hθX3 : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) X) := by
    rw [inSubgroup, Subgroup.card_map_of_injective X.subtype_injective]
    exact (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
  have hbX : (Subgroup.inclusion hBX b : ↥X) ∈ aschbacherSolvableCore 3 ↥X := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hb
    exact hb
  have hbG : (b : G) ∈ inSubgroup (aschbacherSolvableCore 3) X :=
    ⟨Subgroup.inclusion hBX b, hbX, rfl⟩
  have hP : IsPGroup 3 ↥(B ⊓ inSubgroup (aschbacherSolvableCore 3) X) := hB3.to_inf_left
  have h3 : ¬ 3 ∣ Nat.card ↥(B ⊓ inSubgroup (aschbacherSolvableCore 3) X) := fun h =>
    hθX3 (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have h1 : Nat.card ↥(B ⊓ inSubgroup (aschbacherSolvableCore 3) X) = 1 :=
    hP.card_eq_or_dvd.resolve_right h3
  have hbot : (B ⊓ inSubgroup (aschbacherSolvableCore 3) X : Subgroup G) = ⊥ :=
    Subgroup.eq_bot_of_card_eq (B ⊓ inSubgroup (aschbacherSolvableCore 3) X) h1
  have hmem : (b : G) ∈ (B ⊓ inSubgroup (aschbacherSolvableCore 3) X : Subgroup G) :=
    ⟨b.2, hbG⟩
  rw [hbot] at hmem
  exact Subtype.ext (Subgroup.mem_bot.mp hmem)

theorem card_le_center_of_not_mem {d : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d) {Kd : Subgroup G} (hKd : Kd ∈ thetaComponentsAt 3 d)
    (hKd𝒳 : Kd ∉ 𝒳) {B : Subgroup G} (hBK : B ≤ Kd) (hBX : B ≤ sSup 𝒳)
    (hB3 : IsPGroup 3 B) :
    Nat.card B ≤ Nat.card (Subgroup.center
      (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))) := by
  set X := sSup 𝒳 with hX
  set θXc : Subgroup ↥X := aschbacherSolvableCore 3 ↥X with hθXc
  let f : ↥B →* (↥X ⧸ θXc) :=
    (QuotientGroup.mk' θXc).comp (Subgroup.inclusion hBX)
  have hcent : ∀ b : ↥B, f b ∈ Subgroup.center (↥X ⧸ θXc) :=
    mk_mem_center_of_not_mem h𝒳 hKd hKd𝒳 hBK hBX
  have hker : ∀ b : ↥B, f b = 1 → b = 1 := fun b hb =>
    eq_one_of_mk_inclusion_eq_one hBX hB3 (b := b) hb
  have hinj : Function.Injective f := by
    intro b1 b2 h
    have h1 : f (b1 * b2⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have h2 : (b1 * b2⁻¹ : ↥B) = 1 := hker (b1 * b2⁻¹) h1
    have h3 : (b1 : G) * (b2 : G)⁻¹ = 1 := congrArg Subtype.val h2
    have h4 : (b1 : G) = b2 := by
      have := congrArg (· * (b2 : G)) h3
      simpa [mul_assoc] using this
    exact Subtype.ext h4
  have hcinj : Function.Injective
      (fun b : ↥B => (⟨f b, hcent b⟩ : Subgroup.center (↥X ⧸ θXc))) := by
    intro b1 b2 h
    have h' : f b1 = f b2 := congrArg (fun z : ↥(Subgroup.center (↥X ⧸ θXc)) => z.val) h
    exact hinj h'
  have hle := Nat.card_le_card_of_injective
    (fun b : ↥B => (⟨f b, hcent b⟩ : Subgroup.center (↥X ⧸ θXc))) hcinj
  simpa using hle

theorem three_part_card_Kd {Kd : Subgroup G}
    (hKd6 : Sec4.IsTripleCover (↥Kd ⧸ aschbacherSolvableCore 3 ↥Kd) (alternatingGroup (Fin 6))) :
    27 ∣ Nat.card Kd ∧ ¬ 81 ∣ Nat.card Kd := by
  have hcard : Nat.card Kd = 1080 * Nat.card (aschbacherSolvableCore 3 ↥Kd) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥Kd),
      HJRes2.card_of_isTripleCover_six hKd6]
  have h3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥Kd) :=
    (solvable_prime_complement_core_characterization (H := ↥Kd) Nat.prime_three).2.2.1
  refine ⟨?_, ?_⟩
  · rw [hcard]
    exact ⟨40 * Nat.card (aschbacherSolvableCore 3 ↥Kd), by ring⟩
  · intro h
    rw [hcard] at h
    have hcop3 : Nat.Coprime 3 (Nat.card (aschbacherSolvableCore 3 ↥Kd)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have hcop : Nat.Coprime 81 (Nat.card (aschbacherSolvableCore 3 ↥Kd)) := by
      simpa using hcop3.pow_left 4
    have h81 : 81 ∣ 1080 := hcop.dvd_of_dvd_mul_right h
    norm_num at h81

theorem three_part_card_image {X Kd : Subgroup G} (hKdX : Kd ≤ X)
    (hKd6 : Sec4.IsTripleCover (↥Kd ⧸ aschbacherSolvableCore 3 ↥Kd) (alternatingGroup (Fin 6))) :
    27 ∣ Nat.card ((Kd.subgroupOf X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))) ∧
    ¬ 81 ∣ Nat.card ((Kd.subgroupOf X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))) := by
  have hθX3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥X) :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
  set mk : ↥X →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) with hmk
  set f : ↥Kd →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) := mk.comp (Subgroup.inclusion hKdX)
    with hf
  have hrange : f.range = (Kd.subgroupOf X).map mk := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hcard : Nat.card Kd = Nat.card ((Kd.subgroupOf X).map mk) * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange]
  have hker3 : ¬ 3 ∣ Nat.card f.ker := by
    have hmem : ∀ x : f.ker,
        (Subgroup.inclusion hKdX x.val : ↥X) ∈ aschbacherSolvableCore 3 ↥X := by
      intro x
      have hx : mk (Subgroup.inclusion hKdX x.val) = 1 := x.2
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      exact hx
    let g : f.ker →* ↥(aschbacherSolvableCore 3 ↥X) :=
      { toFun := fun x => ⟨Subgroup.inclusion hKdX x.val, hmem x⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hginj : Function.Injective g := by
      intro a b h
      apply Subtype.ext
      apply Subgroup.inclusion_injective hKdX
      exact congrArg (fun z : ↥(aschbacherSolvableCore 3 ↥X) => (z : ↥X)) h
    have hdvd : Nat.card f.ker ∣ Nat.card (aschbacherSolvableCore 3 ↥X) :=
      Subgroup.card_dvd_of_injective g hginj
    exact fun h => hθX3 (h.trans hdvd)
  obtain ⟨h27, h81⟩ := three_part_card_Kd hKd6
  refine ⟨?_, ?_⟩
  · have h : 27 ∣ Nat.card ((Kd.subgroupOf X).map mk) * Nat.card f.ker := by
      rw [← hcard]
      exact h27
    have hcop : Nat.Coprime 27 (Nat.card f.ker) := by
      have h' : Nat.Coprime 3 (Nat.card f.ker) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker3
      simpa using h'.pow_left 3
    exact hcop.dvd_of_dvd_mul_right h
  · intro h
    apply h81
    rw [hcard]
    exact dvd_mul_of_dvd_left h _

theorem le_normalizer_sup_theta {d : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d) {Kd : Subgroup G} (hKd𝒳 : Kd ∈ 𝒳) :
    sSup 𝒳 ≤ Subgroup.normalizer
      ((Kd ⊔ inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) : Subgroup G) : Set G) := by
  set X := sSup 𝒳 with hX
  set θX : Subgroup G := inSubgroup (aschbacherSolvableCore 3) X with hθX
  have hXH : X ≤ Subgroup.centralizer ({d} : Set G) :=
    sSup_le fun Y hY => Sec6.le_centralizer_of_mem_thetaComponentsAt (h𝒳 hY)
  have hθXle : θX ≤ X := Subgroup.map_subtype_le _
  have hKdX : Kd ≤ X := le_sSup hKd𝒳
  refine sSup_le fun Y hY => ?_
  rw [Subgroup.le_normalizer_iff]
  intro y hy m hm
  have hmaple : (Kd ⊔ θX : Subgroup G).map (MulAut.conj y).toMonoidHom ≤ Kd ⊔ θX := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      by_cases hYKd : Y = Kd
      · have hyK : y ∈ Kd := hYKd ▸ hy
        exact Subgroup.mem_sup_left (Kd.mul_mem (Kd.mul_mem hyK hk) (Kd.inv_mem hyK))
      · have hcomm : y * k * y⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3)
            (Subgroup.centralizer ({d} : Set G)) :=
          Sec10.commutator_mem_theta_of_ne (h𝒳 hY) (h𝒳 hKd𝒳) hYKd hy hk
        have hXmem : y * k * y⁻¹ * k⁻¹ ∈ X :=
          X.mul_mem (X.mul_mem (X.mul_mem (le_sSup hY hy) (hKdX hk))
            (X.inv_mem (le_sSup hY hy))) (X.inv_mem (hKdX hk))
        have hθmem : y * k * y⁻¹ * k⁻¹ ∈ θX :=
          Sec12.Item125Diag.inf_le_inSubgroup_theta hXH ⟨hcomm, hXmem⟩
        have hk' : y * k * y⁻¹ = (y * k * y⁻¹ * k⁻¹) * k := by group
        show y * k * y⁻¹ ∈ Kd ⊔ θX
        rw [hk']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hθmem) (Subgroup.mem_sup_left hk)
    · rintro _ ⟨t, ht, rfl⟩
      exact Subgroup.mem_sup_right
        (Sec13.conj_mem_inSubgroup_theta (le_sSup hY hy) ht)
  show y * m * y⁻¹ ∈ Kd ⊔ θX
  exact hmaple (Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hm)

theorem false_of_not_mem {d : G} {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    {Kd : Subgroup G} (hKd : Kd ∈ thetaComponentsAt 3 d) (hKd𝒳 : Kd ∉ 𝒳)
    (hZ : Nat.card (Subgroup.center (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))) = 3)
    {B : Subgroup G} (hBK : B ≤ Kd) (hBX : B ≤ sSup 𝒳) (hB3 : IsPGroup 3 B)
    (hB9 : Nat.card B = 9) : False := by
  have hle := card_le_center_of_not_mem h𝒳 hKd hKd𝒳 hBK hBX hB3
  rw [hZ, hB9] at hle
  omega

theorem dvd_card_of_map_center_eq_top {Q : Type} [Group Q] [Finite Q] {Nbar : Subgroup Q}
    (hZcard : Nat.card (Subgroup.center Q) = 3)
    (htop : Nbar.map (QuotientGroup.mk' (Subgroup.center Q)) = ⊤)
    (hQcard : Nat.card Q = 3 * 460815505920) : 81 ∣ Nat.card Nbar := by
  have hkey : ∀ q : Q, ∃ z ∈ Subgroup.center Q, ∃ n ∈ Nbar, q = z * n := by
    intro q
    have hq' : (QuotientGroup.mk' (Subgroup.center Q)) q ∈
        Nbar.map (QuotientGroup.mk' (Subgroup.center Q)) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hnq⟩ := Subgroup.mem_map.mp hq'
    refine ⟨q * n⁻¹, ?_, n, hn, by group⟩
    have h1 : (QuotientGroup.mk' (Subgroup.center Q)) (q * n⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hnq, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center Q) (q * n⁻¹)).mp h1
  have hjoin : Nbar ⊔ Subgroup.center Q = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨z, hz, n, hn, rfl⟩ := hkey q
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hn)
  have hZnorm : Subgroup.center Q ≤ Subgroup.normalizer (Nbar : Set Q) := by
    rw [Subgroup.le_normalizer_iff]
    intro z hz n hn
    have hc : n * z = z * n := Subgroup.mem_center_iff.mp hz n
    have hconj : z * n * z⁻¹ = n := by
      rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
    exact hn
  have hdvd : Nat.card Q ∣ Nat.card Nbar * 3 := by
    have h :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct.card_dvd_product
        Nbar (Subgroup.center Q) hZnorm
    rwa [hjoin, Subgroup.card_top, hZcard] at h
  have h243 : 243 ∣ Nat.card Q := by
    rw [hQcard]
    norm_num
  have h : 243 ∣ Nat.card Nbar * 3 := h243.trans hdvd
  have h' : 3 * 81 ∣ 3 * Nat.card Nbar := by
    rw [show 3 * 81 = 243 from by norm_num,
      show 3 * Nat.card Nbar = Nat.card Nbar * 3 from by ring]
    exact h
  exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)).mp h'

theorem false_of_normal_subgroup {Q : Type} [Group Q] [Finite Q] {Nbar : Subgroup Q}
    (hNbarNormal : Nbar.Normal) (hZcard : Nat.card (Subgroup.center Q) = 3)
    (hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q))
    (h27 : 27 ∣ Nat.card Nbar) (h81 : ¬ 81 ∣ Nat.card Nbar)
    (hQcard : Nat.card Q = 3 * 460815505920) : False := by
  haveI hmapnormal : (Nbar.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    hNbarNormal.map _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal
    (Nbar.map (QuotientGroup.mk' (Subgroup.center Q))) with hbot | htop
  · have hleZ : Nbar ≤ Subgroup.center Q := by
      intro x hx
      have hmem : (QuotientGroup.mk' (Subgroup.center Q)) x ∈
          Nbar.map (QuotientGroup.mk' (Subgroup.center Q)) := Subgroup.mem_map_of_mem _ hx
      rw [hbot, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff x).mp hmem
    have hle3 : Nat.card Nbar ≤ 3 := by
      have hdvd : Nat.card Nbar ∣ Nat.card (Subgroup.center Q) := Subgroup.card_dvd_of_le hleZ
      rw [hZcard] at hdvd
      exact Nat.le_of_dvd (by norm_num) hdvd
    have h27le : 27 ≤ Nat.card Nbar := Nat.le_of_dvd (by norm_num) h27
    omega
  · exact h81 (dvd_card_of_map_center_eq_top hZcard htop hQcard)

theorem false_of_mem {d : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d) {Kd : Subgroup G} (hKd𝒳 : Kd ∈ 𝒳)
    (hKd6 : Sec4.IsTripleCover (↥Kd ⧸ aschbacherSolvableCore 3 ↥Kd) (alternatingGroup (Fin 6)))
    (hON : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
      CFSG.Blueprint.NativeSporadic.ON) : False := by
  set X := sSup 𝒳 with hX
  set Q := ↥X ⧸ aschbacherSolvableCore 3 ↥X with hQ
  set θXc : Subgroup ↥X := aschbacherSolvableCore 3 ↥X with hθXc
  set mk : ↥X →* Q := QuotientGroup.mk' θXc with hmk
  have hKdX : Kd ≤ X := le_sSup hKd𝒳
  set Nbar : Subgroup Q := (Kd.subgroupOf X).map mk with hNbar
  have hMXle : (Kd ⊔ inSubgroup (aschbacherSolvableCore 3) X : Subgroup G) ≤ X :=
    sup_le hKdX (Subgroup.map_subtype_le _)
  have hMXnormal : ((Kd ⊔ inSubgroup (aschbacherSolvableCore 3) X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMXle).mpr
      (le_normalizer_sup_theta h𝒳 hKd𝒳)
  have hsub : (Subgroup.map X.subtype (aschbacherSolvableCore 3 ↥X)).subgroupOf X =
      aschbacherSolvableCore 3 ↥X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le (aschbacherSolvableCore 3 ↥X))]
  have hMeq : ((Kd ⊔ inSubgroup (aschbacherSolvableCore 3) X).subgroupOf X) =
      Kd.subgroupOf X ⊔ aschbacherSolvableCore 3 ↥X := by
    show (Kd ⊔ Subgroup.map X.subtype (aschbacherSolvableCore 3 ↥X)).subgroupOf X =
      Kd.subgroupOf X ⊔ aschbacherSolvableCore 3 ↥X
    rw [Subgroup.subgroupOf_sup hKdX (Subgroup.map_subtype_le _), hsub]
  have hkermap : (aschbacherSolvableCore 3 ↥X).map mk = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨u, hu, rfl⟩
    show QuotientGroup.mk' θXc u ∈ (⊥ : Subgroup Q)
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hu
  have hNbarEq : Nbar =
      ((Kd ⊔ inSubgroup (aschbacherSolvableCore 3) X).subgroupOf X).map mk := by
    rw [hMeq, Subgroup.map_sup, hkermap, sup_bot_eq]
  have hNbarNormal : Nbar.Normal := by
    rw [hNbarEq]
    exact hMXnormal.map mk (QuotientGroup.mk'_surjective θXc)
  obtain ⟨h27Nbar, h81Nbar⟩ := three_part_card_image hKdX hKd6
  have h27Nbar' : 27 ∣ Nat.card Nbar := by
    rw [hNbar]
    simpa only [hθXc, hmk] using h27Nbar
  have h81Nbar' : ¬ 81 ∣ Nat.card Nbar := by
    rw [hNbar]
    simpa only [hθXc, hmk] using h81Nbar
  haveI hONsimple : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  obtain ⟨eON⟩ := hON.2
  haveI hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) :=
    (MulEquiv.isSimpleGroup_congr eON).mpr hONsimple
  have hZcard : Nat.card (Subgroup.center Q) = 3 := hON.1
  exact false_of_normal_subgroup hNbarNormal hZcard hsimple h27Nbar' h81Nbar'
    (HJRes2.card_of_isTripleCover_ON hON)

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1
