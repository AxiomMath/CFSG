module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34SzOff

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise

section Module

variable {W : Type} [CommGroup W] [Finite W]

theorem sz_core (h38 : D38Top) (hW : ∀ w : W, w ^ 2 = 1) {X A K T : Subgroup (MulAut W)}
    {r : ℚ} (hXq : IsQuotientOfSQTKTC ↥X) (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2)
    (hA : A ∈ QhatStar X) (hT : IsSylowTwoOf T X) (hAT : A ≤ T)
    (hK : K ∈ cComp X) (hKq : CFSG.IsQuasisimple ↥K)
    (hSz : ∃ n : ℕ, SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 n)
    (hKA : ¬ A ≤ Subgroup.centralizer (K : Set (MulAut W))) :
    ∃ I : Subgroup W, I ∈ IrrPlusOn (conjClosure K T) (orbSup T I) T ∧
      orbSup T I ⊔ fixV A = ⊤ ∧ ¬ K ≤ centSub (orbSup T I) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hAX : A ≤ X := hA2.1
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hKX : K ≤ X := le_of_mem_cComp hK
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
  have hYs : Y ≤ stabSub U := le_stabSub_orbSup hTY hIY
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
  have hAU : commSub U A ≠ ⊥ := by
    intro hbot
    rw [commSub_eq_bot_iff] at hbot
    obtain ⟨a, haA, haK⟩ := Set.not_subset.mp hKA
    have haU : a ∈ centSub U := fun u hu => hbot hu a haA
    have hKa : K.map (MulAut.conj a).toMonoidHom ∈ cComp X :=
      CFSG.Quasithin.map_conj_mem_cComp hK (hAX haA)
    have hKaq : CFSG.IsQuasisimple ↥(K.map (MulAut.conj a).toMonoidHom) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv ((MulAut.conj a).subgroupMap K) hKq
    have hdich : K.map (MulAut.conj a).toMonoidHom = K ∨
        ⁅K, K.map (MulAut.conj a).toMonoidHom⁆ = ⊥ := by
      rcases cComp_eq_or_commutator_eq_bot_of_isQuasisimple hKa hK hKaq hKq with h | h
      · exact Or.inl h
      · right
        rw [Subgroup.commutator_comm]
        exact h
    exact hKnot (le_centSub_of_conj hKq hKs haU haK hdich)
  obtain ⟨-, h7⟩ := D2_7 hW hr hA (hAT.trans hTs) hAU
  rcases h7 with ⟨ε, hε, hεA⟩ | ⟨-, hfix⟩
  · exfalso
    obtain ⟨⟨hA2', hrle⟩, hk⟩ := hεA
    have h27 : qhatOf (autSub (Y ⊔ T) U) ≤ ((r - ε : ℚ) : WithTop ℚ) :=
      kq_le_iff.mpr ⟨autSub A U, ⟨autSub_mono (hAT.trans le_sup_right) U, hA2'.2⟩, hk, hrle⟩
    have hc2 : ((r - ε : ℚ) : WithTop ℚ) ≤ ((2 : ℚ) : WithTop ℚ) :=
      WithTop.coe_le_coe.mpr (by linarith)
    have hstd := d3Std_of_irrPlusOn hW hXq hT hK hKq hIU' hKnot (h27.trans hc2)
    have hSz' : ∃ n : ℕ, SuzukiModel (↥(autSub K U) ⧸ Subgroup.center ↥(autSub K U)) 2 n := by
      obtain ⟨n, hn⟩ := hSz
      have hrange : autSub K U = (resHomOn U hKs).range := autSub_eq_range_resHomOn hKs
      let ψ : ↥K →* ↥(autSub K U) :=
        (MulEquiv.subgroupCongr hrange.symm).toMonoidHom.comp (resHomOn U hKs).rangeRestrict
      have hψs : Function.Surjective ψ :=
        (MulEquiv.subgroupCongr hrange.symm).surjective.comp
          (resHomOn U hKs).rangeRestrict_surjective
      have hψ1 : ∃ l, ψ l ≠ 1 := by
        by_contra hall
        push Not at hall
        apply hKnot
        intro l hl u hu
        have h1 := congrArg (fun f : ↥(autSub K U) => (((f : MulAut ↥U) ⟨u, hu⟩ : ↥U) : W))
          (hall ⟨l, hl⟩)
        exact h1
      have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hKq hψ1
      have e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hKq hψs hker
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
        (orbSup (autSub T U) (I.subgroupOf U))) ≤ ((r - ε : ℚ) : WithTop ℚ) := by
      rw [qhatOf_autSub_congr htop, hsup]
      exact qhatOf_autSub_top_le hexpU h27
    rw [h2] at hle
    have h3 : (2 : ℚ) ≤ r - ε := WithTop.coe_le_coe.mp hle
    linarith
  · exact ⟨I, hIU', hfix, hKnot⟩

end Module

end CFSG.Quasithin.H13
