module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Blocks
public import CFSG.Quasithin.Background.OddCoprimeFixV
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private lemma s16h_rkIdx_fixV_conj {V : Type} [CommGroup V] [Finite V] (g a : MulAut V) :
    rkIdx (fixV (Subgroup.zpowers (g * a * g⁻¹))) = rkIdx (fixV (Subgroup.zpowers a)) := by
  have h1 := rk_add_rkIdx (fixV (Subgroup.zpowers (g * a * g⁻¹)))
  have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers a))
  have h3 : rk (fixV (Subgroup.zpowers (g * a * g⁻¹))) = rk (fixV (Subgroup.zpowers a)) := by
    unfold rk
    rw [card_fixV_zpowers_conj]
  omega

theorem s16h_three_le_rk_of_stab_Z7 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hconc : Conc4_136W A t L) (hLp : IsCyclicOrd ↥L 7)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6) {i : MulAut W} (hi2 : i ^ 2 = 1)
    (hiN : i ∈ normalizer (L : Set (MulAut W)))
    (hiW : ∃ u ∈ commSub (⊤ : Subgroup W) L, i u ≠ u) :
    3 ≤ rk ↥(commSub (⊤ : Subgroup W) (zpowers i)) := by
  classical
  let U : Subgroup W := commSub (⊤ : Subgroup W) L
  have hi_stab : i ∈ stabSub U := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have hiNinv : i⁻¹ ∈ normalizer (L : Set (MulAut W)) :=
        (normalizer (L : Set (MulAut W))).inv_mem hiN
      have h := commSub_top_map151b (X := L) (Y := L) (g := i⁻¹)
        (fun x hx => (Subgroup.mem_normalizer_iff.mp hiNinv x).mp hx) (i u) hu
      rwa [MulAut.inv_apply_self] at h
    · intro hu
      exact commSub_top_map151b (X := L) (Y := L) (g := i)
        (fun x hx => (Subgroup.mem_normalizer_iff.mp hiN x).mp hx) u hu
  have hLstab : L ≤ stabSub U := s16h_dc_le_stabSub_commSub L
  let φ : ↥L →* MulAut U :=
    { toFun := fun l => resHom U ⟨l.1, hLstab l.2⟩
      map_one' := by ext u; rfl
      map_mul' := fun l₁ l₂ => by ext u; rfl }
  let L' : Subgroup (MulAut U) := φ.range
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    apply Subtype.ext
    apply s16h_bl_eq_one_of_fixes hconc l.2
    intro u hu
    have h2 : φ l ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [hl]; rfl
    have h3 : ((resHom U ⟨l.1, hLstab l.2⟩ ⟨u, hu⟩ : U) : W) = u :=
      congrArg Subtype.val h2
    rw [resHom_apply] at h3
    simpa using h3
  have hcyc : IsCyclic ↥L' := by
    haveI : IsCyclic ↥L := hLp.1
    exact isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hcard : Nat.card ↥L' = 7 := by
    change Nat.card ↥φ.range = 7
    have h1 : Nat.card ↥L = Nat.card ↥φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    rw [← h1, hLp.2]
  have hL' : IsCyclicOrd ↥L' 7 := ⟨hcyc, hcard⟩
  have hfpf : ∀ w : U, (∀ l ∈ L', l w = w) → w = 1 := by
    intro w hw
    have hwU : (w : W) ∈ commV L := by
      rw [commV_eq_commSub]; exact w.2
    have hwfix : (w : W) ∈ fixV L := by
      rw [mem_fixV]
      intro l hl
      have h := hw (φ ⟨l, hl⟩) (MonoidHom.mem_range.mpr ⟨⟨l, hl⟩, rfl⟩)
      have h2 : ((resHom U ⟨l, hLstab hl⟩ w : U) : W) = (w : W) :=
        congrArg Subtype.val h
      rw [resHom_apply] at h2
      simpa using h2
    have hbot : commV L ⊓ fixV L = ⊥ :=
      commV_inf_fixV_eq_bot_of_odd_card hW L (by rw [hLp.2]; norm_num)
    have hmem : (w : W) ∈ commV L ⊓ fixV L := ⟨hwU, hwfix⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  let i' : MulAut U := resHom U ⟨i, hi_stab⟩
  have hi'2 : i' ^ 2 = 1 := by
    change resHom U ⟨i, hi_stab⟩ ^ 2 = 1
    rw [← map_pow]
    have h : (⟨i, hi_stab⟩ : stabSub U) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hi2
    rw [h, map_one]
  have hinv : i'⁻¹ = i' := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two]
    exact hi'2
  have hi'1 : i' ≠ 1 := by
    obtain ⟨u, hu, hiu⟩ := hiW
    intro h
    apply hiu
    have h2 : i' ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [h]; rfl
    have h3 : ((resHom U ⟨i, hi_stab⟩ ⟨u, hu⟩ : U) : W) = u :=
      congrArg Subtype.val h2
    rw [resHom_apply] at h3
    simpa using h3
  have hconj : ∀ (g : MulAut W) (hg : g ∈ normalizer (L : Set (MulAut W)))
      (hgs : g ∈ stabSub U) (l : ↥L),
      resHom U ⟨g, hgs⟩ * φ l * (resHom U ⟨g, hgs⟩)⁻¹ ∈ L' := by
    intro g hg hgs l
    refine MonoidHom.mem_range.mpr ⟨⟨g * l.1 * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp hg l.1).mp l.2⟩, ?_⟩
    show resHom U ⟨g * l.1 * g⁻¹, _⟩ =
      resHom U ⟨g, hgs⟩ * resHom U ⟨l.1, hLstab l.2⟩ * (resHom U ⟨g, hgs⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg (resHom U) (Subtype.ext rfl)
  have hconjI' : ∀ l : ↥L, i' * φ l * i' ∈ L' := by
    intro l
    have h := hconj i hiN hi_stab l
    have h' : i' * φ l * i'⁻¹ ∈ L' := h
    rwa [hinv] at h'
  have hi'N : i' ∈ normalizer (L' : Set (MulAut U)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hx
      exact hconj i hiN hi_stab l
    · intro hx
      obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hx
      have hxe : x = i' * φ l * i' := by
        rw [hl]
        have hii : i' * i' = 1 := by rw [← pow_two]; exact hi'2
        have hcalc : i' * (i' * x * i'⁻¹) * i' = x := by
          calc i' * (i' * x * i'⁻¹) * i' = (i' * i') * x * (i'⁻¹ * i') := by group
            _ = x := by rw [hii]; group
        exact hcalc.symm
      rw [hxe]
      exact hconjI' l
  have hW_U : ∀ w : U, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hW (w : W))
  have hrk_U : rk U = 6 := hrk
  have h3' : 3 ≤ rk ↥(commSub (⊤ : Subgroup U) (Subgroup.zpowers i')) :=
    s16h_three_le_rk_of_normalizes_Z7 (W := U) hW_U hL' hfpf hrk_U hi'2 hi'1 hi'N
  have hW' : ∀ x ∈ Subgroup.zpowers i, ∀ w ∈ U, x w ∈ U := by
    intro x hx w hw
    exact (mem_stabSub.mp (Subgroup.zpowers_le.mpr hi_stab hx) w).2 hw
  have hres := rk_commV_resHom (V := W) (W := U) (g := i) hi_stab hW'
  have hfinal : 3 ≤ rk (commSub U (Subgroup.zpowers i)) := by
    rw [← hres, commV_eq_commSub]
    exact h3'
  exact le_trans hfinal (rk_mono (commSub_mono le_top le_rfl))

theorem s16h_two_lt_mParam_of_Z7_six {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hconc : Conc4_136W A t L) (hind : sSupIndep (conjSubs A (commSub (⊤ : Subgroup W) L)))
    (hLp : IsCyclicOrd ↥L 7) (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6) :
    2 < E3.mParam A := by
  classical
  let U : Subgroup W := commSub (⊤ : Subgroup W) L
  have hinv : ∀ i ∈ A, orderOf i = 2 → 3 ≤ rkIdx (fixV (Subgroup.zpowers i)) := by
    intro i hiA hiord
    have hi2 : i ^ 2 = 1 := by rw [← hiord]; exact pow_orderOf_eq_one i
    have hi1 : i ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hiord
      omega
    have hex : ∃ a ∈ A, ∃ u ∈ U, i (a u) ≠ a u := by
      by_contra hcon
      have hcon' : ∀ a ∈ A, ∀ u ∈ U, i (a u) = a u := by
        intro a ha u hu
        by_contra hne
        exact hcon ⟨a, ha, u, hu, hne⟩
      have hfix : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers i) := by
        rw [← hconc.1]
        apply iSup_le
        intro X
        apply iSup_le
        intro hX
        intro w hw
        rw [mem_fixV_zpowers_iff]
        obtain ⟨a, ha, rfl⟩ := hX
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
        exact hcon' a ha u hu
      have htop : fixV (Subgroup.zpowers i) = ⊤ := top_le_iff.mp hfix
      apply hi1
      ext w
      have hw : w ∈ fixV (Subgroup.zpowers i) := by rw [htop]; exact Subgroup.mem_top w
      rw [mem_fixV_zpowers_iff] at hw
      simpa using hw
    obtain ⟨a, haA, u, huU, hiau⟩ := hex
    let j : MulAut W := a⁻¹ * i * a
    have hjA : j ∈ A := A.mul_mem (A.mul_mem (A.inv_mem haA) hiA) haA
    have hj2 : j ^ 2 = 1 := by
      show (a⁻¹ * i * a) ^ 2 = 1
      rw [pow_two]
      calc (a⁻¹ * i * a) * (a⁻¹ * i * a) = a⁻¹ * (i * i) * a := by group
        _ = 1 := by rw [← pow_two, hi2]; group
    have hjW : ∃ v ∈ U, j v ≠ v := by
      refine ⟨u, huU, ?_⟩
      intro hju
      apply hiau
      have h := congrArg (fun w : W => a w) hju
      simpa [j, MulAut.mul_apply, MulAut.apply_inv_self] using h
    have h3 : 3 ≤ rk (commSub (⊤ : Subgroup W) (Subgroup.zpowers j)) := by
      by_cases hjN : j ∈ normalizer (L : Set (MulAut W))
      · exact s16h_three_le_rk_of_stab_Z7 hW hconc hLp hrk hj2 hjN hjW
      · have hne : U.map j.toMonoidHom ≠ U := by
          intro heq
          refine hjN (s16h_bl_mem_normalizer_of_stab hconc hjA (mem_stabSub.2 fun v => ?_))
          constructor
          · intro hv
            have hv' : j v ∈ U.map j.toMonoidHom := by
              have hvU : j v ∈ U := hv
              rw [← heq] at hvU
              exact hvU
            obtain ⟨v', hv'', hv'e⟩ := Subgroup.mem_map.1 hv'
            exact (j.injective hv'e) ▸ hv''
          · intro hv
            have hv' : j v ∈ U.map j.toMonoidHom := Subgroup.mem_map_of_mem _ hv
            rwa [heq] at hv'
        have hdis := hind.pairwiseDisjoint
          (show U ∈ conjSubs A U from ⟨1, A.one_mem, by ext; simp⟩)
          (show U.map j.toMonoidHom ∈ conjSubs A U from ⟨j, hjA, rfl⟩) (Ne.symm hne)
        have h6 : 6 ≤ rk (commSub (⊤ : Subgroup W) (Subgroup.zpowers j)) :=
          le_trans (le_of_eq hrk.symm) (s16h_bl_rk_le_of_inf_eq_bot (disjoint_iff.mp hdis))
        omega
    have h3j : 3 ≤ rkIdx (fixV (Subgroup.zpowers j)) := by
      rw [rkIdx_fixV_zpowers j, commV_eq_commSub]
      exact h3
    have hji : a * j * a⁻¹ = i := by
      show a * (a⁻¹ * i * a) * a⁻¹ = i
      group
    have hconj := s16h_rkIdx_fixV_conj a j
    rw [hji] at hconj
    rw [hconj]
    exact h3j
  unfold E3.mParam
  split_ifs with hev
  · set S : Set ℕ := {n : ℕ | ∃ t ∈ A, orderOf t = 2 ∧
        n = rkIdx (fixV (Subgroup.zpowers t))}
    have hne : S.Nonempty := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 2 (even_iff_two_dvd.1 hev)
      refine ⟨rkIdx (fixV (Subgroup.zpowers (x : MulAut W))), (x : MulAut W), x.2, ?_, rfl⟩
      rw [Subgroup.orderOf_coe]
      exact hx
    obtain ⟨s, hsA, hs2, hn⟩ := Nat.sInf_mem hne
    rw [hn]
    have := hinv s hsA hs2
    omega
  · have h6 : rk (commSub (⊤ : Subgroup W) L) ≤ rk W := by
      have h := rk_mono (H := commSub (⊤ : Subgroup W) L) (K := (⊤ : Subgroup W)) le_top
      rwa [rk_top] at h
    rw [hrk] at h6
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
