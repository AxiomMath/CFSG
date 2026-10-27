module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylPath
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma conj_mem_zpowers {G : Type*} [Group G] {u s : G} (hs : s * s = 1)
    (hu : s * u * s = u⁻¹) : ∀ c ∈ Subgroup.zpowers u, s * c * s ∈ Subgroup.zpowers u := by
  intro c hc
  rw [Subgroup.zpowers_eq_closure] at hc
  have hsinv : s⁻¹ = s := by
    rw [inv_eq_iff_mul_eq_one]
    exact hs
  refine Subgroup.closure_induction (p := fun g _ => s * g * s ∈ Subgroup.zpowers u)
    ?_ ?_ ?_ ?_ hc
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx, hu]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers u)
  · simp [hs]
  · intro x y hx hy ihx ihy
    have hxy : (s * x * s) * (s * y * s) = s * (x * y) * s := by
      calc (s * x * s) * (s * y * s)
          = (s * x) * (s * ((s * y) * s)) := by rw [mul_assoc (s * x) s ((s * y) * s)]
        _ = (s * x) * ((s * (s * y)) * s) := by rw [← mul_assoc s (s * y) s]
        _ = (s * x) * (((s * s) * y) * s) := by rw [← mul_assoc s s y]
        _ = (s * x) * ((1 * y) * s) := by rw [hs]
        _ = (s * x) * (y * s) := by rw [one_mul]
        _ = s * (x * y) * s := by rw [← mul_assoc (s * x) y s, ← mul_assoc s x y]
    rw [← hxy]
    exact Subgroup.mul_mem _ ihx ihy
  · intro x hx ihx
    have hxinv : s * x⁻¹ * s = (s * x * s)⁻¹ := by
      calc s * x⁻¹ * s = s * x⁻¹ * s⁻¹ := by rw [hsinv]
        _ = (s * x * s⁻¹)⁻¹ := (conj_inv).symm
        _ = (s * x * s)⁻¹ := by rw [hsinv]
    rw [hxinv]
    exact Subgroup.inv_mem _ ihx

private lemma natCard_group_fin1_le (M : CoxeterMatrix (Fin 1)) : Nat.card M.Group ≤ 2 := by
  let cs := M.toCoxeterSystem
  let s : M.Group := cs.simple 0
  have hs2 : s * s = 1 := by dsimp [s]; exact cs.simple_mul_simple_self 0
  have htop : Subgroup.zpowers s = ⊤ := by
    rw [Subgroup.zpowers_eq_closure]
    apply le_antisymm le_top
    rw [← cs.subgroup_closure_range_simple]
    apply Subgroup.closure_mono
    rintro x ⟨i, rfl⟩
    fin_cases i
    simp [s]
  have hcard : Nat.card M.Group = Nat.card (Subgroup.zpowers s) := by
    rw [htop]
    exact (Nat.card_congr (Subgroup.topEquiv (G := M.Group)).toEquiv).symm
  rw [hcard, Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (n := 2) (by norm_num) (by rw [pow_two]; exact hs2)

private lemma natCard_group_fin2_le (M : CoxeterMatrix (Fin 2)) (hlo : 2 ≤ M 0 1) :
    Nat.card M.Group ≤ 2 * M 0 1 := by
  let cs := M.toCoxeterSystem
  let s : M.Group := cs.simple 0
  let t : M.Group := cs.simple 1
  let u : M.Group := s * t
  have hs2 : s * s = 1 := by dsimp [s]; exact cs.simple_mul_simple_self 0
  have ht2 : t * t = 1 := by dsimp [t]; exact cs.simple_mul_simple_self 1
  have hsinv : s⁻¹ = s := by dsimp [s]; exact cs.inv_simple 0
  have htinvt : t⁻¹ = t := by dsimp [t]; exact cs.inv_simple 1
  have hupow : u ^ (M 0 1) = 1 := by
    dsimp [u, s, t]
    exact cs.simple_mul_simple_pow 0 1
  have hsus : s * u * s = u⁻¹ := by
    dsimp [u]
    rw [← mul_assoc s s t, hs2, one_mul, mul_inv_rev, hsinv, htinvt]
  have hconj : ∀ c ∈ Subgroup.zpowers u, s * c * s ∈ Subgroup.zpowers u :=
    conj_mem_zpowers hs2 hsus
  let C : Subgroup M.Group := Subgroup.zpowers u
  let U : Set M.Group := {x | x ∈ C ∨ ∃ c ∈ C, x = c * s}
  have ht_eq : u⁻¹ * s = t := by
    dsimp [u]
    rw [mul_inv_rev, hsinv, htinvt, mul_assoc, hs2, mul_one]
  have hs_mem : s ∈ U := Or.inr ⟨1, C.one_mem, by rw [one_mul]⟩
  have ht_mem : t ∈ U :=
    Or.inr ⟨u⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers u), ht_eq.symm⟩
  let P : Submonoid M.Group :=
    { carrier := U
      one_mem' := Or.inl C.one_mem
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx | ⟨c1, hc1, rfl⟩
        · rcases hy with hy | ⟨c2, hc2, rfl⟩
          · exact Or.inl (C.mul_mem hx hy)
          · exact Or.inr ⟨x * c2, C.mul_mem hx hc2, by rw [mul_assoc]⟩
        · rcases hy with hy | ⟨c2, hc2, rfl⟩
          · have hy' : s * y * s ∈ C := hconj y hy
            refine Or.inr ⟨c1 * (s * y * s), C.mul_mem hc1 hy', ?_⟩
            simp only [mul_assoc, hs2, mul_one]
          · have hc2' : s * c2 * s ∈ C := hconj c2 hc2
            refine Or.inl ?_
            rw [mul_assoc c1 s (c2 * s), ← mul_assoc s c2 s]
            exact C.mul_mem hc1 hc2' }
  have hP : Submonoid.closure (Set.range cs.simple) ≤ P := by
    rw [Submonoid.closure_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact hs_mem
    · exact ht_mem
  have hPtop : P = ⊤ := by
    apply le_antisymm le_top
    rw [← cs.submonoid_closure_range_simple]
    exact hP
  have hUuniv : U = Set.univ := by
    have := congrArg (fun Q : Submonoid M.Group => (Q : Set M.Group)) hPtop
    simpa [P] using this
  have hUeq : Nat.card M.Group = Nat.card U := by
    rw [hUuniv, Nat.card_univ]
  have hCcard : Nat.card C ≤ M 0 1 := by
    change Nat.card (Subgroup.zpowers u) ≤ M 0 1
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by omega) hupow
  have hUbound : Nat.card U ≤ 2 * Nat.card C := by
    have : Finite C :=
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨M 0 1, by omega, hupow⟩).finite_zpowers
    let f : C ⊕ C → U := fun z =>
      match z with
      | Sum.inl c => ⟨(c : M.Group), Or.inl c.2⟩
      | Sum.inr c => ⟨(c : M.Group) * s, Or.inr ⟨c, c.2, rfl⟩⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rcases hx with hx | ⟨c, hc, rfl⟩
      · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
      · exact ⟨Sum.inr ⟨c, hc⟩, rfl⟩
    calc Nat.card U ≤ Nat.card (C ⊕ C) := Nat.card_le_card_of_surjective f hf
      _ = Nat.card C + Nat.card C := Nat.card_sum
      _ = 2 * Nat.card C := by ring
  calc Nat.card M.Group = Nat.card U := hUeq
    _ ≤ 2 * Nat.card C := hUbound
    _ ≤ 2 * (M 0 1) := by omega

private lemma card_group_le_eight_of_weylMatrix {ι : Type} (M : CoxeterMatrix ι)
    (hM : GGIsWeylMatrix M) (hcard : Nat.card ι ≤ 2)
    (hnotG2 : ¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e) :
    Nat.card M.Group ≤ 8 := by
  rcases hM with ⟨n, e, hn, hA | ⟨hnB, hB⟩ | ⟨hnD, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
    ⟨e, hF4⟩ | ⟨e, hG2⟩
  ·
    have hne : n ≤ 2 := by
      have h := Nat.card_congr e
      rw [Nat.card_fin] at h
      omega
    rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
    · rw [hA]
      calc Nat.card ((CoxeterMatrix.A 1).reindex e).Group
          = Nat.card (CoxeterMatrix.A 1).Group :=
            Nat.card_congr ((CoxeterMatrix.A 1).reindexGroupEquiv e).toEquiv
        _ ≤ 2 := natCard_group_fin1_le _
        _ ≤ 8 := by norm_num
    · have hA21 : (CoxeterMatrix.A 2) 0 1 = 3 := by decide
      rw [hA]
      calc Nat.card ((CoxeterMatrix.A 2).reindex e).Group
          = Nat.card (CoxeterMatrix.A 2).Group :=
            Nat.card_congr ((CoxeterMatrix.A 2).reindexGroupEquiv e).toEquiv
        _ ≤ 2 * (CoxeterMatrix.A 2) 0 1 := natCard_group_fin2_le _ (by rw [hA21]; norm_num)
        _ ≤ 8 := by rw [hA21]; norm_num
  ·
    have hne : n ≤ 2 := by
      have h := Nat.card_congr e
      rw [Nat.card_fin] at h
      omega
    have hn2 : n = 2 := by omega
    subst hn2
    have hB21 : (CoxeterMatrix.B 2) 0 1 = 4 := by decide
    rw [hB]
    calc Nat.card ((CoxeterMatrix.B 2).reindex e).Group
        = Nat.card (CoxeterMatrix.B 2).Group :=
          Nat.card_congr ((CoxeterMatrix.B 2).reindexGroupEquiv e).toEquiv
      _ ≤ 2 * (CoxeterMatrix.B 2) 0 1 := natCard_group_fin2_le _ (by rw [hB21]; norm_num)
      _ ≤ 8 := by norm_num [hB21]
  ·
    exfalso
    have h1 : n ≤ 2 := by
      have h := Nat.card_congr e
      simp only [Nat.card_fin] at h
      omega
    omega
  ·
    exfalso
    have h1 : (6 : ℕ) ≤ 2 := by
      have h := Nat.card_congr e
      simp only [Nat.card_fin] at h
      omega
    omega
  ·
    exfalso
    have h1 : (7 : ℕ) ≤ 2 := by
      have h := Nat.card_congr e
      simp only [Nat.card_fin] at h
      omega
    omega
  ·
    exfalso
    have h1 : (8 : ℕ) ≤ 2 := by
      have h := Nat.card_congr e
      simp only [Nat.card_fin] at h
      omega
    omega
  ·
    exfalso
    have h1 : (4 : ℕ) ≤ 2 := by
      have h := Nat.card_congr e
      simp only [Nat.card_fin] at h
      omega
    omega
  ·
    exact absurd ⟨e, hG2⟩ hnotG2

theorem ggSecFive_L_rank_three
    (hPump : GGSecFivePumpReadInput) (hFix : GGSecFiveFixInput) (hJA2 : GGSecFiveJA2Input) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
        ∃ (ι : Type) (M : CoxeterMatrix ι) (f : M.Group ≃* ↥(ggAutomizer L Bs)),
          GGIsWeylMatrix M ∧ (∀ i : ι, GGIsReflection p ((f (M.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) ∧
            3 ≤ Nat.card ι := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hI : GGThmIHyp p B x L := hconf.1
  have hBstar : GGBstar p B Bs := hconf.2.1
  have hStdSub : LargeEvenStdSub p B x L D J := hconf.2.2
  obtain ⟨_, _, _, _, _, _, hSStar, hStdType⟩ := hI
  obtain ⟨hPre, _⟩ := hStdSub
  obtain ⟨hDB, hD_ea, hDcard, -, hJeq, hJcomp, hBD⟩ := hPre
  have hJLraw : J ≤ L := hJcomp.1.trans inf_le_left
  have hJcent : J ≤ Subgroup.centralizer (D : Set G) := hJcomp.1.trans inf_le_right
  have hDBs : D ≤ Bs := hDB.trans hBstar.1
  obtain ⟨hp, hBs_ea, hxBs, -, -⟩ := hconf.tableB_facts
  have hp2 : 2 ≤ p := hp.two_le
  have : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hSStar.2.2.1
  have hxpow : x ^ p = 1 := hBs_ea.2 x hxBs
  have hox : orderOf x = p := orderOf_eq_prime hxpow hx1
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hox]
  obtain ⟨hW, hnotG2⟩ := hPump.1 G p B Bs x L D J 𝒦 hcfg hsplit
  have hJL : ggAutomizer J Bs ≤ ggAutomizer L Bs := ggAutomizer_mono Bs hJLraw
  obtain ⟨ι, M, hM, f, hf⟩ := hW
  refine ⟨ι, M, f, hM, hf, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hcard2 : Nat.card ι ≤ 2 := by omega
  have hcardM : Nat.card M.Group ≤ 8 :=
    card_group_le_eight_of_weylMatrix M hM hcard2 (by
      rintro ⟨e, he⟩
      have hMweyl : GGWeylOfType p (CoxeterMatrix.G₂.reindex e) (ggAutomizer L Bs) := by
        rw [← he]
        exact ⟨f, hf⟩
      exact hnotG2 (GGWeylOfType.of_reindex hMweyl))
  have hcardAL : Nat.card (ggAutomizer L Bs) = Nat.card M.Group :=
    (Nat.card_congr f.toEquiv).symm
  obtain ⟨r, hrJ, r', hr'J, hrrefl, hr'refl, horder⟩ :=
    hJA2 G p B Bs x L D J 𝒦 hcfg hsplit
  have hr1 : r ≠ 1 := by
    intro h
    have h2 := hrrefl.2
    rw [h] at h2
    have h3 : Nat.card ↥Bs * p = Nat.card ↥Bs * 1 := by simpa using h2
    have hp1 : p = 1 := mul_left_cancel₀ (Nat.card_pos.ne') h3
    exact hp.ne_one hp1
  have hordr : orderOf r = 2 := orderOf_eq_prime hrrefl.1 hr1
  have hordrJ : orderOf (⟨r, hrJ⟩ : ↥(ggAutomizer J Bs)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hordr
  have h2dvd : 2 ∣ Nat.card (ggAutomizer J Bs) := by
    have h := orderOf_dvd_natCard (⟨r, hrJ⟩ : ↥(ggAutomizer J Bs))
    rwa [hordrJ] at h
  have h3dvd : 3 ∣ Nat.card (ggAutomizer J Bs) := by
    have hmem : r * r' ∈ ggAutomizer J Bs := Subgroup.mul_mem _ hrJ hr'J
    have hordr' : orderOf (⟨r * r', hmem⟩ : ↥(ggAutomizer J Bs)) = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact horder
    have h := orderOf_dvd_natCard (⟨r * r', hmem⟩ : ↥(ggAutomizer J Bs))
    rwa [hordr'] at h
  have h6dvd : 6 ∣ Nat.card (ggAutomizer J Bs) := by
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2dvd h3dvd
    norm_num at h ⊢
    exact h
  have hcard_le : Nat.card (ggAutomizer J Bs) ≤ Nat.card (ggAutomizer L Bs) :=
    Subgroup.card_le_of_le hJL
  have hAJ_le8 : Nat.card (ggAutomizer J Bs) ≤ 8 := by
    calc Nat.card (ggAutomizer J Bs) ≤ Nat.card (ggAutomizer L Bs) := hcard_le
      _ = Nat.card M.Group := hcardAL
      _ ≤ 8 := hcardM
  have hAJ_eq6 : Nat.card (ggAutomizer J Bs) = 6 := by
    have hpos : 0 < Nat.card (ggAutomizer J Bs) := Nat.card_pos
    obtain ⟨k, hk⟩ := h6dvd
    omega
  have h6dvdL : 6 ∣ Nat.card (ggAutomizer L Bs) :=
    dvd_trans h6dvd (Subgroup.card_dvd_of_le hJL)
  have hAL_le8 : Nat.card (ggAutomizer L Bs) ≤ 8 := by rw [hcardAL]; exact hcardM
  have hAL_eq6 : Nat.card (ggAutomizer L Bs) = 6 := by
    have hpos : 0 < Nat.card (ggAutomizer L Bs) := Nat.card_pos
    obtain ⟨k, hk⟩ := h6dvdL
    omega
  have hAJe : ggAutomizer J Bs = ggAutomizer L Bs :=
    Subgroup.eq_of_le_of_card_ge hJL (by rw [hAL_eq6, hAJ_eq6])
  have hfixJ : ∀ φ ∈ ggAutomizer J Bs, ∀ d : ↥D,
      φ ⟨(d : G), hDBs d.2⟩ = ⟨(d : G), hDBs d.2⟩ := by
    intro φ hφ d
    obtain ⟨g, hgJ, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hφ
    apply Subtype.ext
    rw [hgφ]
    rw [← Subgroup.mem_centralizer_iff.mp (hJcent hgJ) (d : G) d.2, mul_assoc, mul_inv_cancel,
      mul_one]
  have hDle : D ≤ Subgroup.zpowers x := by
    intro d hd
    have h := hFix G p B Bs x L D J 𝒦 hcfg hsplit ⟨d, hDBs hd⟩ (by
      intro φ hφ
      rw [← hAJe] at hφ
      exact hfixJ φ hφ ⟨d, hd⟩)
    simpa using h
  have hcardD : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
  rw [hcardx, hDcard] at hcardD
  have hp_lt_p2 : p < p ^ 2 := by
    have h : p < p * p := lt_mul_of_one_lt_right hp.pos hp.one_lt
    simpa [pow_two] using h
  exact absurd hcardD (not_le.mpr hp_lt_p2)

end CFSG.StandardType

end
