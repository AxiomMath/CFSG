module

public import CFSG.Quasithin.Background.SmithD39TwoSzR2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SzOff

public section

namespace CFSG.Quasithin.SmithD39Two

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.LieType.BorelTits
  CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W]

private theorem two_le_of_qhatOf_le (h38 : D38Top) (hW : ∀ w : W, w ^ 2 = 1)
    {X T L : Subgroup (MulAut W)} {I : Subgroup W} (hXq : IsQuotientOfSQTKTC ↥X)
    (hT : IsSylowTwoOf T X) (hL : L ∈ cComp X) (hLq : CFSG.IsQuasisimple ↥L)
    (hSz : ∃ n : ℕ, SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n)
    (hI : I ∈ IrrPlusOn (conjClosure L T) (orbSup T I) T) (hLU : ¬ L ≤ centSub (orbSup T I))
    {s : ℚ} (hs : qhatOf (autSub (conjClosure L T ⊔ T) (orbSup T I)) ≤ (s : WithTop ℚ))
    (hs2 : s ≤ 2) : 2 ≤ s := by
  set Y := conjClosure L T with hYdef
  set U := orbSup T I with hUdef
  have hTY : T ≤ Subgroup.normalizer (Y : Set (MulAut W)) := le_normalizer_conjClosure L T
  have hLY : L ≤ Y := le_conjClosure L T
  have hIU : I ≤ U := le_orbSup T I
  have hIY : ∀ y ∈ Y, ∀ w ∈ I, y w ∈ I := fun y hy w hw => hI.1.2.1 ⟨y, hy⟩ w hw
  have hYs : Y ≤ stabSub U := H13.le_stabSub_orbSup hTY hIY
  have hTs : T ≤ stabSub U :=
    le_stabSub_of_forall_mem fun t ht w hw => mem_orbSup_of_mem_map ht hw
  have hLs : L ≤ stabSub U := hLY.trans hYs
  have hstd := d3Std_of_irrPlusOn hW hXq hT hL hLq hI hLU
    (hs.trans (WithTop.coe_le_coe.mpr hs2))
  have hSz' : ∃ n : ℕ, SuzukiModel (↥(autSub L U) ⧸ Subgroup.center ↥(autSub L U)) 2 n := by
    obtain ⟨n, hn⟩ := hSz
    have hrange : autSub L U = (resHomOn U hLs).range := autSub_eq_range_resHomOn hLs
    let ψ : ↥L →* ↥(autSub L U) :=
      (MulEquiv.subgroupCongr hrange.symm).toMonoidHom.comp (resHomOn U hLs).rangeRestrict
    have hψs : Function.Surjective ψ :=
      (MulEquiv.subgroupCongr hrange.symm).surjective.comp
        (resHomOn U hLs).rangeRestrict_surjective
    have hψ1 : ∃ l, ψ l ≠ 1 := by
      by_contra hall
      push Not at hall
      apply hLU
      intro l hl u hu
      have h1 := congrArg (fun f : ↥(autSub L U) => (((f : MulAut ↥U) ⟨u, hu⟩ : ↥U) : W))
        (hall ⟨l, hl⟩)
      exact h1
    have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hLq hψ1
    have e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hLq hψs hker
    exact ⟨n, suzukiModel_of_mulEquiv e.symm hn⟩
  have htop : orbSup (autSub T U) (I.subgroupOf U) = ⊤ :=
    orbSup_autSub_subgroupOf_eq_top hIU hTs le_rfl
  have h2 := h38 _ _ _ _ _ _ hstd htop hSz'
  have hsup : autSub Y U ⊔ autSub T U = autSub (Y ⊔ T) U := by
    rw [autSub_eq_map_resHomOn le_sup_left (sup_le hYs hTs),
      autSub_eq_map_resHomOn le_sup_right (sup_le hYs hTs),
      autSub_eq_map_resHomOn le_rfl (sup_le hYs hTs), ← Subgroup.map_sup,
      ← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
  have hexpU : ∀ w : ↥U, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hW])
  have hle : qhatOf (autSub (autSub Y U ⊔ autSub T U)
      (orbSup (autSub T U) (I.subgroupOf U))) ≤ (s : WithTop ℚ) := by
    rw [qhatOf_autSub_congr htop, hsup]
    exact qhatOf_autSub_top_le hexpU hs
  rw [h2] at hle
  exact WithTop.coe_le_coe.mp hle


theorem sz_comp_le_centralizer (h38 : D38Top) (hW : ∀ w : W, w ^ 2 = 1)
    {M N A K : Subgroup (MulAut W)} {r : ℚ} (hMq : IsQuotientOfSQTKTC ↥M)
    (hNM : M ≤ Subgroup.normalizer (N : Set (MulAut W))) (_hNle : N ≤ M) (hNperf : ⁅N, N⁆ = N)
    (hNcomm : commV N = ⊤) (hr : qhatOf M = (r : WithTop ℚ)) (hr2 : r ≤ 2) (hA : A ∈ QhatStar M)
    (hK : K ∈ cComp M) (hKq : CFSG.IsQuasisimple ↥K)
    (hKN : K ≤ Subgroup.centralizer (N : Set (MulAut W)))
    (hSz : ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 n) :
    A ≤ Subgroup.centralizer (K : Set (MulAut W)) := by
  classical
  by_contra hKA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hAM : A ≤ M := hA2.1
  have hA2p : IsPGroup 2 ↥A := hA2.2.2.isPGroup
  obtain ⟨T, hT, hAT⟩ := A4.exists_isSylowTwoOf_ge hAM hA2p
  have hTM : T ≤ M := hT.1
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  set Y := conjClosure K T with hYdef
  have hTY : T ≤ Subgroup.normalizer (Y : Set (MulAut W)) := le_normalizer_conjClosure K T
  have hKY : K ≤ Y := le_conjClosure K T
  have hYperf : ⁅Y, Y⁆ = Y := A3.conjClosure_perfect (perfect_of_mem_cComp hK)
  have hYne : commV Y ≠ ⊥ := by
    intro h
    rw [commV_eq_commSub, commSub_eq_bot_iff] at h
    apply ne_bot_of_mem_cComp hK
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    ext w
    simpa using h (Subgroup.mem_top w) l (hKY hl)
  obtain ⟨I₀, hI₀⟩ := B1Red.exists_mem_irrPlus hYperf hYne
  obtain ⟨I, hI₁⟩ := irrPlusOn_nonempty hW hTY hT2 hI₀
  have hactY : ActCompat (MonoidHom.id W) Y Y :=
    ⟨fun b hb => ⟨b, hb, fun _ => rfl⟩, fun a ha => ⟨a, ha, fun _ => rfl⟩⟩
  have hactT : ActCompat (MonoidHom.id W) T T :=
    ⟨fun b hb => ⟨b, hb, fun _ => rfl⟩, fun a ha => ⟨a, ha, fun _ => rfl⟩⟩
  have hI' : I ∈ IrrPlusOn Y (⨆ y ∈ T, y • I) T :=
    hactY.mem_irrPlusOn_of_map (fun _ _ h => h) hactT hTY hTY (Wq := ⨆ y ∈ T, y • I₀)
      (fun t ht w hw => smul_mem_biSup_smul ht hw) (by rw [Subgroup.map_id]; exact hI₁)
  set U := orbSup T I with hUdef
  have hIU' : I ∈ IrrPlusOn Y U T := by rw [hUdef, orbSup_eq_biSup_smul]; exact hI'
  have hIU : I ≤ U := le_orbSup T I
  have hIY : ∀ y ∈ Y, ∀ w ∈ I, y w ∈ I := fun y hy w hw => hIU'.1.2.1 ⟨y, hy⟩ w hw
  have hYs : Y ≤ stabSub U := H13.le_stabSub_orbSup hTY hIY
  have hTs : T ≤ stabSub U :=
    le_stabSub_of_forall_mem fun t ht w hw => mem_orbSup_of_mem_map ht hw
  have hKs : K ≤ stabSub U := hKY.trans hYs
  have hKnot : ¬ K ≤ centSub U := by
    intro hKU
    have hYU : Y ≤ centSub U := conjClosure_le fun t ht l hl u hu => by
      have htu : t⁻¹ u ∈ U := (hTs (T.inv_mem ht) u).mpr hu
      show (t * l * t⁻¹) u = u
      simp only [MulAut.mul_apply]
      rw [hKU hl _ htu]
      simp
    have hfix : XMod.fixed ↥Y I = I :=
      le_antisymm (XMod.fixed_le I) fun w hw => ⟨hw, fun y => hYU y.2 w (hIU hw)⟩
    have hlt := hIU'.1.2.2.2.1
    rw [hfix] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨a, haA, haK⟩ := Set.not_subset.mp hKA
  have hKa : K.map (MulAut.conj a).toMonoidHom ∈ cComp M :=
    CFSG.Quasithin.map_conj_mem_cComp hK (hAM haA)
  have hKaq : CFSG.IsQuasisimple ↥(K.map (MulAut.conj a).toMonoidHom) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ((MulAut.conj a).subgroupMap K) hKq
  have hdich : K.map (MulAut.conj a).toMonoidHom = K ∨
      ⁅K, K.map (MulAut.conj a).toMonoidHom⁆ = ⊥ := by
    rcases cComp_eq_or_commutator_eq_bot_of_isQuasisimple hKa hK hKaq hKq with h | h
    · exact Or.inl h
    · right
      rw [Subgroup.commutator_comm]
      exact h
  have hAU : commSub U A ≠ ⊥ := by
    intro hbot
    rw [commSub_eq_bot_iff] at hbot
    have haU : a ∈ centSub U := fun u hu => hbot hu a haA
    exact hKnot (le_centSub_of_conj hKq hKs haU haK hdich)
  rcases (D2_7 hW hr hA (hAT.trans hTs) hAU).2 with ⟨ε, hε, hQ⟩ | ⟨-, hsum⟩
  ·
    have hle : qhatOf (autSub (Y ⊔ T) U) ≤ ((r - ε : ℚ) : WithTop ℚ) :=
      kq_le_iff.mpr ⟨autSub A U,
        ⟨autSub_mono (hAT.trans le_sup_right) U, hQ.1.1.2.1, hQ.1.1.2.2⟩, hQ.2, hQ.1.2⟩
    have h2 := two_le_of_qhatOf_le h38 hW hMq hT hK hKq hSz hIU' hKnot hle (by linarith)
    linarith
  ·
    exact sz_false_of_sup_fixV_eq_top hW hNperf hNcomm (hTM.trans hNM) hKq
      (ne_bot_of_mem_cComp hK)
      (fun k hk n hn => ((Subgroup.mem_centralizer_iff.1 (hKN hk)) n hn).symm) hIU' hAT hsum
      haA haK hdich

end CFSG.Quasithin.SmithD39Two
