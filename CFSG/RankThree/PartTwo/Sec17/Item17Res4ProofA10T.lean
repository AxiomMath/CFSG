module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res4ProofA10S
import CFSG.RankThree.PartTwo.Sec17.Item171ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late Equiv
open CFSG.RankThree.PartTwo.KFacts.KP2 CFSG.RankThree.PartTwo.Sec17.Proof171Gen

theorem eTwentySevenF_eq_one_of_comm : ∀ i j k : Fin 3,
    eTwentySevenF i j k * wCycle = wCycle * eTwentySevenF i j k →
    eTwentySevenF i j k * sTen = sTen * eTwentySevenF i j k → eTwentySevenF i j k = 1 := by
  decide +kernel

theorem monoRep_normalizes_k : ∀ (π : Fin 6) (ε : Fin 8),
    monoRep π ε * dOne * (monoRep π ε)⁻¹ = dOne⁻¹ →
    monoRep π ε * dTwo * (monoRep π ε)⁻¹ = dTwo⁻¹ →
    monoRep π ε * dThree = dThree * monoRep π ε →
    (∀ m : Fin 4, ∃ n : Fin 4, monoRep π ε * kOneF m * (monoRep π ε)⁻¹ = kOneF n) ∧
    (∀ m : Fin 4, ∃ n : Fin 4, monoRep π ε * kTwoF m * (monoRep π ε)⁻¹ = kTwoF n) := by
  decide +kernel

theorem eTwentySevenF_seven : ∀ i j k : Fin 3, eTwentySevenF i j k 7 = 7 → k = 0 := by
  decide +kernel

theorem monoRep_one_four_spec : evenTable 1 4 = true ∧
    (∀ i j : Fin 3, ∃ i' j' : Fin 3,
      monoRep 1 4 * eTwentySevenF i j 0 * (monoRep 1 4)⁻¹ = eTwentySevenF i' j' 0) ∧
    (∀ m n : Fin 4, m ≠ 0 → monoRep 1 4 * kOneF m * (monoRep 1 4)⁻¹ ≠ kOneF n) ∧
    (∀ m n : Fin 4, m ≠ 0 → monoRep 1 4 * kTwoF m * (monoRep 1 4)⁻¹ ≠ kTwoF n) := by
  decide +kernel

theorem kF_disjoint : (∀ m n : Fin 4, kOneF m = kTwoF n → m = 0) ∧
    (∀ m n : Fin 4, kOneF m = kThreeF n → m = 0) ∧
    (∀ m n : Fin 4, kTwoF m = kThreeF n → m = 0) := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
  {φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)} {g : Perm (Fin 10)}

omit [Finite G] in
theorem actTen_eq_projTen (y : ↥Y₀) :
    actTen Y₀ φ ⟨y, Y₀.le_normalizer y.2⟩ = projTen Y₀ φ y := by
  set σ := actTen Y₀ φ ⟨y, Y₀.le_normalizer y.2⟩ with hσ
  set τ := projTen Y₀ φ y with hτ
  have key : ∀ x : ↥Y₀, σ * projTen Y₀ φ x * σ⁻¹ = τ * projTen Y₀ φ x * τ⁻¹ := by
    intro x
    rw [← projTen_conj]
    have hx : Y₀.normalizerMonoidHom ⟨y, Y₀.le_normalizer y.2⟩ x = y * x * y⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    rw [hx, map_mul, map_mul, map_inv]
  set u := τ⁻¹ * σ with hu
  have hcomm : ∀ z ∈ alternatingGroup (Fin 10), u * z = z * u := by
    intro z hz
    obtain ⟨x, rfl⟩ := Res162b.mem_range_projTen Y₀ φ hz
    have hk := key x
    calc u * projTen Y₀ φ x = τ⁻¹ * (σ * projTen Y₀ φ x * σ⁻¹) * σ := by rw [hu]; group
      _ = τ⁻¹ * (τ * projTen Y₀ φ x * τ⁻¹) * σ := by rw [hk]
      _ = projTen Y₀ φ x * u := by rw [hu]; group
  have huE : u ∈ eTwentySeven := by
    rw [← centralizer_eTwentySeven]
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (hcomm x (eTwentySeven_le_alternatingGroup hx)).symm
  obtain ⟨i, j, k, hijk⟩ := huE
  have h1 := hcomm wCycle (Subgroup.mem_inf.mp wCycle_mem_normAlt).2
  have h2 := hcomm sTen (Subgroup.mem_inf.mp sTen_mem_normAlt).2
  rw [hijk] at h1 h2
  have hu1 : τ⁻¹ * σ = 1 := hijk.trans (eTwentySevenF_eq_one_of_comm i j k h1 h2)
  exact (inv_mul_eq_one.mp hu1).symm

omit [Finite G] in
theorem mem_cQuot_of_actTen_eq_one {m : Subgroup.normalizer (Y₀ : Set G)}
    (hm : actTen Y₀ φ m = 1) : (m : G) ∈ cQuot Y₀ := by
  rw [← SetLike.mem_coe, coe_cQuot]
  refine ⟨m.2, fun y hy => ?_⟩
  have h1 := projTen_conj Y₀ φ m ⟨y, hy⟩
  rw [hm, one_mul, inv_one, mul_one] at h1
  have h2 := Res162b.mem_pCoreOf_of_projTen_eq_one (φ := φ)
    (y := Y₀.normalizerMonoidHom m ⟨y, hy⟩ * (⟨y, hy⟩ : ↥Y₀)⁻¹)
    (by rw [map_mul, map_inv, h1, mul_inv_cancel])
  simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h2

theorem le_sup_cQuot_of_a10 {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A10Pic A c L Y₀ φ g)
    (h142 : Concl142 A (lB A)) (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G)) :
    S ≤ (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set ψ := actTen Y₀ φ with hψ
  set R' : Subgroup (Perm (Fin 10)) := ((S.subgroupOf M).map ψ).map (MulAut.conj g).toMonoidHom
    with hR'
  have hmemR' : ∀ z, z ∈ R' ↔ ∃ m : M, (m : G) ∈ S ∧ g * ψ m * g⁻¹ = z := by
    intro z
    constructor
    · rintro ⟨w, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨m, Subgroup.mem_subgroupOf.mp hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨ψ m, ⟨m, Subgroup.mem_subgroupOf.mpr hm, rfl⟩, rfl⟩
  have hSQ : S ∈ scriptQ A (lB A) := h.mem_qStar_two.prop.1.1
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hR'3 : ¬ 3 ∣ Nat.card R' := by
    rw [hR', Subgroup.card_map_of_injective (MulAut.conj g).injective]
    intro h3
    have hd := Subgroup.card_map_dvd (S.subgroupOf M) ψ
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv] at hd
    exact Proof171.not_three_dvd_of_isPGroup_two hS2 (h3.trans hd)
  have hER' : eTwentySeven ≤ Subgroup.normalizer (R' : Set (Perm (Fin 10))) := by
    refine le_normalizer_of_conj fun x hx z hz => ?_
    obtain ⟨a, ha, rfl⟩ := hP.surj x hx
    obtain ⟨m, hm, rfl⟩ := (hmemR' z).mp hz
    have haM : (a : G) ∈ M := Y₀.le_normalizer a.2
    refine (hmemR' _).mpr ⟨⟨a, haM⟩ * m * ⟨a, haM⟩⁻¹, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hSQ.1.2.2 ha) (m : G)).mp hm
      simpa using this
    · rw [map_mul, map_mul, map_inv, show (⟨a, haM⟩ : M) = ⟨a, Y₀.le_normalizer a.2⟩ from rfl,
        actTen_eq_projTen]
      group
  have hle : cimg Y₀ φ g (S ⊓ Y₀) ≤ R' := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_cimg.mp hz
    exact (hmemR' _).mpr ⟨⟨y, Y₀.le_normalizer y.2⟩, hy.1, by rw [actTen_eq_projTen]⟩
  obtain ⟨hd12, hd13, hd23⟩ := kF_disjoint
  have hR'le : R' ≤ cimg Y₀ φ g (S ⊓ Y₀) := by
    have hmem1 : kOneF 1 ∈ kOne := ⟨1, rfl⟩
    have hmem2 : kTwoF 1 ∈ kTwo := ⟨1, rfl⟩
    rcases cimg_eq h hP h142 with h1 | h1 <;> rw [h1] at hle ⊢ <;>
      rcases le_kOne_or_le_kTwo_or_le_kThree hR'3 hER' with h2 | h2 | h2
    · exact h2
    · obtain ⟨n, hn⟩ := h2 (hle hmem1)
      exact absurd (hd12 1 n hn) (by decide)
    · obtain ⟨n, hn⟩ := h2 (hle hmem1)
      exact absurd (hd13 1 n hn) (by decide)
    · obtain ⟨n, hn⟩ := h2 (hle hmem2)
      exact absurd (hd12 n 1 hn.symm) (by
        intro hn0
        subst hn0
        exact absurd hn (by decide))
    · exact h2
    · obtain ⟨n, hn⟩ := h2 (hle hmem2)
      exact absurd (hd23 1 n hn) (by decide)
  intro s hs
  have hz : g * ψ ⟨s, hSM hs⟩ * g⁻¹ ∈ cimg Y₀ φ g (S ⊓ Y₀) :=
    hR'le ((hmemR' _).mpr ⟨_, hs, rfl⟩)
  obtain ⟨y, hy, hyz⟩ := mem_cimg.mp hz
  have he : projTen Y₀ φ y = ψ ⟨s, hSM hs⟩ := by
    have := congrArg (fun z => g⁻¹ * z * g) hyz
    simpa [mul_assoc] using this
  have hu : ψ (⟨y, Y₀.le_normalizer y.2⟩⁻¹ * ⟨s, hSM hs⟩) = 1 := by
    rw [map_mul, map_inv, actTen_eq_projTen, he, inv_mul_cancel]
  have huC := mem_cQuot_of_actTen_eq_one hu
  have hs' : s = (y : G) * ((y : G)⁻¹ * s) := by group
  rw [hs']
  refine Subgroup.mul_mem_sup hy (Subgroup.mem_inf.mpr
    ⟨mul_mem (inv_mem (Subgroup.mem_inf.mp hy).1) hs, ?_⟩)
  simpa using huC

omit [Finite G] in
theorem cimg_inf_L_le (hP : A10Pic A c L Y₀ φ g) : cimg Y₀ φ g (A ⊓ L) ≤ planeOne := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := mem_cimg.mp hz
  obtain ⟨i, j, k, hijk⟩ := hP.mem y hy.1
  obtain ⟨σ, -, hσ⟩ := hP.L_seven y hy.2
  have h7 : (g * projTen Y₀ φ y * g⁻¹) 7 = 7 := by
    rw [← hσ]
    exact embedSeven_apply_of_ge σ (by decide)
  rw [hijk] at h7
  have hk := eTwentySevenF_seven i j k h7
  subst hk
  exact ⟨i, j, hijk⟩

omit [Finite G] in
theorem cimg_inf_L (hP : A10Pic A c L Y₀ φ g) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    cimg Y₀ φ g (A ⊓ L) = planeOne := by
  have hle := cimg_inf_L_le hP
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_planeOne]
  set f : ↥((A ⊓ L).subgroupOf Y₀) →* Perm (Fin 10) :=
    ((MulAut.conj g).toMonoidHom.comp (projTen Y₀ φ)).comp (Subgroup.subtype _) with hf
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hxy' : g * projTen Y₀ φ x * g⁻¹ = g * projTen Y₀ φ y * g⁻¹ := hxy
    have he : projTen Y₀ φ (x : ↥Y₀) = projTen Y₀ φ (y : ↥Y₀) := by
      have := congrArg (fun z => g⁻¹ * z * g) hxy'
      simpa [mul_assoc] using this
    have hA : (((x : ↥Y₀)⁻¹ * y : ↥Y₀) : G) ∈ A := by
      have hx := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp x.2)).1
      have hy := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp y.2)).1
      simpa using mul_mem (inv_mem hx) hy
    have h1 := hP.inj _ hA (by rw [map_mul, map_inv, he, inv_mul_cancel])
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  have hrange : f.range = cimg Y₀ φ g (A ⊓ L) := by
    ext z
    rw [mem_cimg]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mp x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, Subgroup.mem_subgroupOf.mpr hy⟩, rfl⟩
  have hcard := Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv
  rw [hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left.trans hP.le_y0 : A ⊓ L ≤ Y₀)).toEquiv, h9] at hcard
  rw [← hcard]

omit [Finite G] in
theorem exists_inf_L_axis (hP : A10Pic A c L Y₀ φ g) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    (∃ a : ↥Y₀, (a : G) ∈ A ⊓ L ∧ g * projTen Y₀ φ a * g⁻¹ = dOne) ∧
      ∃ b : ↥Y₀, (b : G) ∈ A ⊓ L ∧ g * projTen Y₀ φ b * g⁻¹ = dTwo := by
  have hpl := cimg_inf_L hP h9
  have h1 : dOne ∈ cimg Y₀ φ g (A ⊓ L) := hpl ▸ ⟨1, 0, by decide +kernel⟩
  have h2 : dTwo ∈ cimg Y₀ φ g (A ⊓ L) := hpl ▸ ⟨0, 1, by decide +kernel⟩
  exact ⟨mem_cimg.mp h1, mem_cimg.mp h2⟩

theorem mem_normalizer_inf_L_of_a10 {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A10Pic A c L Y₀ φ g)
    (h142 : Concl142 A (lB A)) (hO2 : CFSG.Open.pCoreOf 2 Y₀ ≤ S)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {t : G} (htL : t ∈ L)
    (htinv : ∀ x ∈ A ⊓ L, t * x * t⁻¹ = x⁻¹) :
    t ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  have htY : t ∈ Y₀ := hP.L_le htL
  set t' : ↥Y₀ := ⟨t, htY⟩ with ht'
  set π := projTen Y₀ φ with hπ
  set τ := g * π t' * g⁻¹ with hτ
  obtain ⟨⟨a, haAL, ha⟩, ⟨b, hbAL, hb⟩⟩ := exists_inf_L_axis hP h9
  have hinv : ∀ x : ↥Y₀, (x : G) ∈ A ⊓ L →
      τ * (g * π x * g⁻¹) * τ⁻¹ = (g * π x * g⁻¹)⁻¹ := by
    intro x hx
    have hx' : t' * x * t'⁻¹ = x⁻¹ := Subtype.ext (by simpa using htinv x hx)
    calc τ * (g * π x * g⁻¹) * τ⁻¹ = g * π (t' * x * t'⁻¹) * g⁻¹ := by
          rw [hτ, map_mul, map_mul, map_inv]
          group
      _ = (g * π x * g⁻¹)⁻¹ := by
          rw [hx', map_inv]
          group
  have h1 : τ * dOne * τ⁻¹ = dOne⁻¹ := by
    rw [← ha]
    exact hinv a haAL
  have h2 : τ * dTwo * τ⁻¹ = dTwo⁻¹ := by
    rw [← hb]
    exact hinv b hbAL
  have h3 : τ * dThree = dThree * τ := hP.L_cent t' htL
  have h1' : τ⁻¹ * dOne * τ = dOne⁻¹ := by
    calc τ⁻¹ * dOne * τ = τ⁻¹ * (τ * dOne * τ⁻¹)⁻¹ * τ := by rw [h1, inv_inv]
      _ = dOne⁻¹ := by group
  have h2' : τ⁻¹ * dTwo * τ = dTwo⁻¹ := by
    calc τ⁻¹ * dTwo * τ = τ⁻¹ * (τ * dTwo * τ⁻¹)⁻¹ * τ := by rw [h2, inv_inv]
      _ = dTwo⁻¹ := by group
  have h3' : τ⁻¹ * dThree * τ = dThree := by
    calc τ⁻¹ * dThree * τ = τ⁻¹ * (dThree * τ) := by group
      _ = dThree := by rw [← h3]; group
  have hτN : τ ∈ normTen := by
    refine mem_normTen_of_axisGen (fun i => ?_) (fun i => ?_)
    · fin_cases i
      · change τ * dOne * τ⁻¹ ∈ eTwentySeven
        rw [h1]
        exact inv_mem dOne_mem
      · change τ * dTwo * τ⁻¹ ∈ eTwentySeven
        rw [h2]
        exact inv_mem dTwo_mem
      · change τ * dThree * τ⁻¹ ∈ eTwentySeven
        rw [h3, mul_inv_cancel_right]
        exact dThree_mem
    · fin_cases i
      · change τ⁻¹ * dOne * τ ∈ eTwentySeven
        rw [h1']
        exact inv_mem dOne_mem
      · change τ⁻¹ * dTwo * τ ∈ eTwentySeven
        rw [h2']
        exact inv_mem dTwo_mem
      · change τ⁻¹ * dThree * τ ∈ eTwentySeven
        rw [h3']
        exact dThree_mem
  obtain ⟨πb, ε, i, j, k, hτe⟩ := exists_monoRep_of_mem_normTen hτN
  set μ := monoRep πb ε with hμ
  set e := eTwentySevenF i j k with he
  have heD : e * dOne = dOne * e ∧ e * dTwo = dTwo * e ∧ e * dThree = dThree * e := by
    have e1 : dOne = eTwentySevenF 1 0 0 := by decide +kernel
    have e2 : dTwo = eTwentySevenF 0 1 0 := by decide +kernel
    have e3 : dThree = eTwentySevenF 0 0 1 := by decide +kernel
    rw [he, e1, e2, e3]
    exact ⟨eTwentySevenF_comm _ _ _ _ _ _, eTwentySevenF_comm _ _ _ _ _ _,
      eTwentySevenF_comm _ _ _ _ _ _⟩
  have hμτ : μ = τ * e⁻¹ := by rw [hτe]; group
  have hμ1 : μ * dOne * μ⁻¹ = dOne⁻¹ := by
    rw [hμτ, show τ * e⁻¹ * dOne * (τ * e⁻¹)⁻¹ = τ * (e⁻¹ * (dOne * e)) * τ⁻¹ by group,
      ← heD.1]
    rw [show τ * (e⁻¹ * (e * dOne)) * τ⁻¹ = τ * dOne * τ⁻¹ by group, h1]
  have hμ2 : μ * dTwo * μ⁻¹ = dTwo⁻¹ := by
    rw [hμτ, show τ * e⁻¹ * dTwo * (τ * e⁻¹)⁻¹ = τ * (e⁻¹ * (dTwo * e)) * τ⁻¹ by group,
      ← heD.2.1]
    rw [show τ * (e⁻¹ * (e * dTwo)) * τ⁻¹ = τ * dTwo * τ⁻¹ by group, h2]
  have hμ3 : μ * dThree = dThree * μ := by
    rw [hμτ]
    calc τ * e⁻¹ * dThree = τ * (e⁻¹ * (dThree * e)) * e⁻¹ := by group
      _ = τ * (e⁻¹ * (e * dThree)) * e⁻¹ := by rw [← heD.2.2]
      _ = (τ * dThree) * e⁻¹ := by group
      _ = dThree * (τ * e⁻¹) := by rw [h3]; group
  obtain ⟨hμk1, hμk2⟩ := monoRep_normalizes_k πb ε hμ1 hμ2 hμ3
  have heE : e ∈ eTwentySeven := ⟨i, j, k, rfl⟩
  have hτK : ∀ z ∈ cimg Y₀ φ g (S ⊓ Y₀), τ * z * τ⁻¹ ∈ cimg Y₀ φ g (S ⊓ Y₀) := by
    intro z hz
    rcases cimg_eq h hP h142 with hK | hK <;> rw [hK] at hz ⊢
    · have hez := (Subgroup.mem_normalizer_iff.mp (eTwentySeven_le_normalizer_k.1 heE) z).mp hz
      obtain ⟨m, hm⟩ := hez
      obtain ⟨n, hn⟩ := hμk1 m
      refine ⟨n, ?_⟩
      rw [hτe, ← hn, ← hm, hμ]
      group
    · have hez := (Subgroup.mem_normalizer_iff.mp (eTwentySeven_le_normalizer_k.2.1 heE) z).mp hz
      obtain ⟨m, hm⟩ := hez
      obtain ⟨n, hn⟩ := hμk2 m
      refine ⟨n, ?_⟩
      rw [hτe, ← hn, ← hm, hμ]
      group
  have htSY : t ∈ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hx' : x ∈ S ⊓ Y₀ := hx
    have hxY : x ∈ Y₀ := hx'.2
    have hz := hτK _ (mem_cimg.mpr ⟨⟨x, hxY⟩, hx', rfl⟩)
    obtain ⟨y, hy, hyz⟩ := mem_cimg.mp hz
    have hyz' : g * π y * g⁻¹ = g * π (t' * ⟨x, hxY⟩ * t'⁻¹) * g⁻¹ := by
      rw [hyz, hτ, map_mul, map_mul, map_inv, hπ]
      group
    have he' : π y = π (t' * ⟨x, hxY⟩ * t'⁻¹) := by
      have := congrArg (fun z => g⁻¹ * z * g) hyz'
      simpa [mul_assoc] using this
    have hO := inv_mul_mem_of_projTen_eq he'
    have hS : ((y⁻¹ * (t' * ⟨x, hxY⟩ * t'⁻¹) : ↥Y₀) : G) ∈ S := hO2 hO
    have hSx : t * x * t⁻¹ ∈ S := by
      have := mul_mem (Subgroup.mem_inf.mp hy).1 hS
      simpa [ht'] using this
    exact Subgroup.mem_inf.mpr ⟨hSx, mul_mem (mul_mem htY hxY) (inv_mem htY)⟩
  have hSL : S ⊓ L = (S ⊓ Y₀) ⊓ L := by rw [inf_assoc, inf_eq_right.mpr hP.L_le]
  rw [hSL]
  exact Late.le_normalizer_inf (Subgroup.zpowers_le.mpr htSY)
    (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer htL)) (Subgroup.mem_zpowers t)

theorem exists_w_of_a10 {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A10Pic A c L Y₀ φ g)
    (h142 : Concl142 A (lB A)) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    ∃ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
      w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
        w ∉ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) := by
  obtain ⟨hev, hpl, hk1, hk2⟩ := monoRep_one_four_spec
  set π := projTen Y₀ φ with hπ
  set h' := monoRep 1 4 with hh'
  obtain ⟨y, hyN, hy, a₀, ha₀, hya₀⟩ := hP.lift h' (monoRep_mem_normAlt hev)
  refine ⟨y, Subgroup.mem_inf.mpr ⟨hyN, y.2⟩, ?_, ?_⟩
  ·
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hx' : x ∈ A ⊓ L := hx
    have hxY : x ∈ Y₀ := hP.le_y0 hx'.1
    have hxA : (y : G) * x * (y : G)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hyN x).mp hx'.1
    have himg : g * π (y * ⟨x, hxY⟩ * y⁻¹) * g⁻¹ ∈ planeOne := by
      rw [hy ⟨x, hxY⟩ hx'.1]
      have hpx : g * π ⟨x, hxY⟩ * g⁻¹ ∈ planeOne :=
        (cimg_inf_L hP h9) ▸ mem_cimg.mpr ⟨_, hx', rfl⟩
      obtain ⟨i, j, hij⟩ := hpx
      obtain ⟨i', j', h''⟩ := hpl i j
      exact ⟨i', j', by rw [hij, h'']⟩
    rw [← cimg_inf_L hP h9] at himg
    obtain ⟨x', hx'AL, hx'e⟩ := mem_cimg.mp himg
    have he : π x' = π (y * ⟨x, hxY⟩ * y⁻¹) := by
      have := congrArg (fun z => g⁻¹ * z * g) hx'e
      simpa [mul_assoc] using this
    have hA : ((x'⁻¹ * (y * ⟨x, hxY⟩ * y⁻¹) : ↥Y₀) : G) ∈ A := by
      have := mul_mem (inv_mem (Subgroup.mem_inf.mp hx'AL).1) hxA
      simpa using this
    have h1 := hP.inj _ hA (by rw [map_mul, map_inv, he, inv_mul_cancel])
    have heq : (y : G) * x * (y : G)⁻¹ = x' := by
      have := congrArg Subtype.val (inv_mul_eq_one.mp h1)
      simpa using this.symm
    rw [heq]
    exact hx'AL
  ·
    intro hyS
    set e₀ := g * π a₀ * g⁻¹ with he₀
    have he₀E : e₀ ∈ eTwentySeven := hP.mem a₀ ha₀
    have hσK : ∀ z ∈ cimg Y₀ φ g (S ⊓ Y₀),
        (g * π y * g⁻¹) * z * (g * π y * g⁻¹)⁻¹ ∈ cimg Y₀ φ g (S ⊓ Y₀) := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_cimg.mp hz
      have hyx : (y : G) * x * (y : G)⁻¹ ∈ S ⊓ Y₀ :=
        (Subgroup.mem_normalizer_iff.mp hyS x).mp hx
      refine mem_cimg.mpr ⟨y * x * y⁻¹, by simpa using hyx, ?_⟩
      rw [map_mul, map_mul, map_inv, hπ]
      group
    have hh'K : ∀ z ∈ cimg Y₀ φ g (S ⊓ Y₀), h' * z * h'⁻¹ ∈ cimg Y₀ φ g (S ⊓ Y₀) := by
      intro z hz
      have hez : e₀⁻¹ * z * e₀ ∈ cimg Y₀ φ g (S ⊓ Y₀) := by
        have hN := eTwentySeven_le_normalizer_cimg hP
          (Late.le_normalizer_inf h.mem_qStar_two.prop.1.1.1.2.2 h.le_normalizer_y0)
          (inv_mem he₀E)
        have := (Subgroup.mem_normalizer_iff.mp hN z).mp hz
        simpa using this
      have := hσK _ hez
      rw [hya₀] at this
      simpa [mul_assoc] using this
    rcases cimg_eq h hP h142 with hK | hK
    · have hm : kOneF 1 ∈ cimg Y₀ φ g (S ⊓ Y₀) := hK ▸ ⟨1, rfl⟩
      have := hh'K _ hm
      rw [hK] at this
      obtain ⟨n, hn⟩ := this
      exact hk1 1 n (by decide) hn
    · have hm : kTwoF 1 ∈ cimg Y₀ φ g (S ⊓ Y₀) := hK ▸ ⟨1, rfl⟩
      have := hh'K _ hm
      rw [hK] at this
      obtain ⟨n, hn⟩ := this
      exact hk2 1 n (by decide) hn

end CFSG.RankThree.PartTwo.Sec17.Proof17Res4
