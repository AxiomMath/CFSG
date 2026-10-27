module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Shape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Good

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

private theorem s16t3_branch_map_mem_fixV {H : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (H : Set (MulAut W))) (w : W) :
    g w ∈ fixV H ↔ w ∈ fixV H := by
  constructor
  · intro hw x hx
    have h1 := hw (g * x * g⁻¹) (conj_mem_of_mem_normalizer hg hx)
    have h3 : g (x w) = g w := by
      calc g (x w) = (g * x * g⁻¹) (g w) := by simp [MulAut.mul_apply]
        _ = g w := h1
    exact g.injective h3
  · intro hw x hx
    have h1 := hw (g⁻¹ * x * g) (inv_conj_mem_of_mem_normalizer hg hx)
    calc x (g w) = g ((g⁻¹ * x * g) w) := by simp [MulAut.mul_apply]
      _ = g w := by rw [h1]

private theorem s16t3_branch_sumOfNat_map
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} {k : ℕ} {g : MulAut W}
    (hN : ∀ (I Z' : Subgroup W), N L I Z' →
      N L (I.map g.toMonoidHom) (Z'.map g.toMonoidHom))
    (h : SumOfNat N L U Z k) :
    SumOfNat N L (U.map g.toMonoidHom) (Z.map g.toMonoidHom) k := by
  obtain ⟨I, hZI, hind, hsup, hnat⟩ := h
  refine ⟨fun i => (I i).map g.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Subgroup.map_mono (hZI i)
  · intro i
    have h' := Subgroup.map_mono (f := g.toMonoidHom) (hind i)
    rw [Subgroup.map_inf (I i) (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) g.toMonoidHom
      g.injective] at h'
    simpa only [Subgroup.map_sup, Subgroup.map_iSup] using h'
  · rw [← hsup, Subgroup.map_sup, Subgroup.map_iSup]
  · intro i
    exact hN (I i) Z (hnat i)

private theorem s16t3_natShapeGood_map {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    {g : MulAut W} (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (h : NatShapeGood L U Z) :
    NatShapeGood L (U.map g.toMonoidHom) (Z.map g.toMonoidHom) := by
  obtain ⟨n, hcases⟩ := h
  rcases hcases with ⟨hSLn, hn, hsum⟩ | ⟨hSpn, hn, hsum⟩ | ⟨hOPn, hn, hsum⟩ |
    ⟨hOMn, hn, hsum⟩ | ⟨hAltn, hn, hsum⟩
  · refine ⟨n, Or.inl ⟨hSLn, hn, s16t3_branch_sumOfNat_map ?_ hsum⟩⟩
    intro I Z' hI
    obtain ⟨K, hKf, hKfin, hKcard, hReal⟩ := hI
    exact ⟨K, hKf, hKfin, hKcard, s16t3_realizes_map_of_mem_normalizer hg hReal⟩
  · refine ⟨n, Or.inr (Or.inl ⟨hSpn, hn, s16t3_branch_sumOfNat_map ?_ hsum⟩)⟩
    intro I Z' hI
    obtain ⟨hev, K, hKf, hKfin, hKcard, hReal⟩ := hI
    exact ⟨hev, K, hKf, hKfin, hKcard, s16t3_realizes_map_of_mem_normalizer hg hReal⟩
  · refine ⟨n, Or.inr (Or.inr (Or.inl ⟨hOPn, hn,
      s16t3_branch_sumOfNat_map ?_ hsum⟩))⟩
    intro I Z' hI
    obtain ⟨hev, K, hKf, hKfin, hKcard, hReal⟩ := hI
    exact ⟨hev, K, hKf, hKfin, hKcard, s16t3_realizes_map_of_mem_normalizer hg hReal⟩
  · refine ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hOMn, hn,
      s16t3_branch_sumOfNat_map ?_ hsum⟩)))⟩
    intro I Z' hI
    obtain ⟨hev, K, hKf, hKfin, b, c, hKcard, hpoly, hReal⟩ := hI
    exact ⟨hev, K, hKf, hKfin, b, c, hKcard, hpoly,
      s16t3_realizes_map_of_mem_normalizer hg hReal⟩
  · refine ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ⟨hAltn, hn,
      s16t3_branch_sumOfNat_map ?_ hsum⟩)))⟩
    intro I Z' hI
    exact s16t3_realizes_map_of_mem_normalizer hg hI

theorem ThreeNat.natShapeGood_of_mem_irrSet (h : ThreeNat A L T)
    (hE : T3EngineBranch L ⊤ (fixV L) 3) {I : Subgroup W} (hI : I ∈ irrSet L) :
    NatShapeGood L I (I ⊓ fixV L) := by
  have hex : ∃ I₀ : Subgroup W, I₀ ∈ irrSet L ∧ NatShapeGood L I₀ (I₀ ⊓ fixV L) := by
    rcases hE with ⟨n, hSL | hSp | hOP | hOM | hAlt⟩
    · obtain ⟨hSLn, hn, hsum⟩ := hSL
      obtain ⟨J, hZJ, -, hJsum⟩ := s16t3_sumOfNat_summand hsum (0 : Fin 3)
      have hJN : BinaryNaturalSL L J (fixV L) n 1 := s16t3_sumOfNat_one hJsum
      have hJshape : SumOfNatShape L J (fixV L) 1 := ⟨n, Or.inl ⟨hSLn, hJsum⟩⟩
      obtain ⟨hYmem, -, hYsup⟩ :=
        s16t3_commSub_mem_irrSet_of_natural (L := L) h.quasi hZJ hJshape
      have hIJ : commSub J L ≤ J := le_trans le_sup_left (le_of_eq hYsup)
      have hstable : StableUnder L (commSub J L) := hYmem.2.2.1
      refine ⟨commSub J L, hYmem, n, Or.inl ⟨hSLn, hn, ?_⟩⟩
      exact s16t3_sumOfNat_singleton inf_le_left
        (s16t3_restrict_binaryNaturalSL hJN hIJ hstable hYsup)
    · obtain ⟨hSpn, hn, hsum⟩ := hSp
      obtain ⟨J, hZJ, -, hJsum⟩ := s16t3_sumOfNat_summand hsum (0 : Fin 3)
      have hJN : NatSpn L J (fixV L) n 1 := s16t3_sumOfNat_one hJsum
      have hJshape : SumOfNatShape L J (fixV L) 1 := ⟨n, Or.inr (Or.inl ⟨hSpn, hJsum⟩)⟩
      obtain ⟨hYmem, -, hYsup⟩ :=
        s16t3_commSub_mem_irrSet_of_natural (L := L) h.quasi hZJ hJshape
      have hIJ : commSub J L ≤ J := le_trans le_sup_left (le_of_eq hYsup)
      have hstable : StableUnder L (commSub J L) := hYmem.2.2.1
      refine ⟨commSub J L, hYmem, n, Or.inr (Or.inl ⟨hSpn, hn, ?_⟩)⟩
      exact s16t3_sumOfNat_singleton inf_le_left
        (s16t3_restrict_natSpn hJN hIJ hstable hYsup)
    · obtain ⟨hOPn, hn, hsum⟩ := hOP
      obtain ⟨J, hZJ, -, hJsum⟩ := s16t3_sumOfNat_summand hsum (0 : Fin 3)
      have hJN : NatOmegaPlus L J (fixV L) n 1 := s16t3_sumOfNat_one hJsum
      have hJshape : SumOfNatShape L J (fixV L) 1 :=
        ⟨n, Or.inr (Or.inr (Or.inl ⟨hOPn, hJsum⟩))⟩
      obtain ⟨hYmem, -, hYsup⟩ :=
        s16t3_commSub_mem_irrSet_of_natural (L := L) h.quasi hZJ hJshape
      have hIJ : commSub J L ≤ J := le_trans le_sup_left (le_of_eq hYsup)
      have hstable : StableUnder L (commSub J L) := hYmem.2.2.1
      refine ⟨commSub J L, hYmem, n, Or.inr (Or.inr (Or.inl ⟨hOPn, hn, ?_⟩))⟩
      exact s16t3_sumOfNat_singleton inf_le_left
        (s16t3_restrict_natOmegaPlus hJN hIJ hstable hYsup)
    · obtain ⟨hOMn, hn, hsum⟩ := hOM
      obtain ⟨J, hZJ, -, hJsum⟩ := s16t3_sumOfNat_summand hsum (0 : Fin 3)
      have hJN : NatOmegaMinus L J (fixV L) n 1 := s16t3_sumOfNat_one hJsum
      have hJshape : SumOfNatShape L J (fixV L) 1 :=
        ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hOMn, hJsum⟩)))⟩
      obtain ⟨hYmem, -, hYsup⟩ :=
        s16t3_commSub_mem_irrSet_of_natural (L := L) h.quasi hZJ hJshape
      have hIJ : commSub J L ≤ J := le_trans le_sup_left (le_of_eq hYsup)
      have hstable : StableUnder L (commSub J L) := hYmem.2.2.1
      refine ⟨commSub J L, hYmem, n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hOMn, hn, ?_⟩)))⟩
      exact s16t3_sumOfNat_singleton inf_le_left
        (s16t3_restrict_natOmegaMinus hJN hIJ hstable hYsup)
    · obtain ⟨hAltn, hn, hsum⟩ := hAlt
      obtain ⟨J, hZJ, -, hJsum⟩ := s16t3_sumOfNat_summand hsum (0 : Fin 3)
      have hJN : AlternatingNatural L J (fixV L) n := s16t3_sumOfNat_one hJsum
      have hJshape : SumOfNatShape L J (fixV L) 1 :=
        ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ⟨hAltn, hJsum⟩)))⟩
      obtain ⟨hYmem, -, hYsup⟩ :=
        s16t3_commSub_mem_irrSet_of_natural (L := L) h.quasi hZJ hJshape
      have hIJ : commSub J L ≤ J := le_trans le_sup_left (le_of_eq hYsup)
      have hstable : StableUnder L (commSub J L) := hYmem.2.2.1
      refine ⟨commSub J L, hYmem, n, Or.inr (Or.inr (Or.inr (Or.inr ⟨hAltn, hn, ?_⟩)))⟩
      exact s16t3_sumOfNat_singleton inf_le_left
        (s16t3_restrict_alternatingNatural hJN hIJ hstable hYsup)
  obtain ⟨I₀, hI₀, hI₀good⟩ := hex
  obtain ⟨g, hg, hgI⟩ := h.trans I₀ hI₀ I hI
  have hgn : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := hg.2
  have hfix : (fixV L).map g.toMonoidHom = fixV L := by
    apply le_antisymm
    · intro w hw
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
      exact (s16t3_branch_map_mem_fixV hgn z).2 hz
    · intro w hw
      exact Subgroup.mem_map.2 ⟨g⁻¹ w,
        (s16t3_branch_map_mem_fixV hgn (g⁻¹ w)).1 (by simpa using hw), by simp⟩
  have hinf : (I₀ ⊓ fixV L).map g.toMonoidHom = I₀.map g.toMonoidHom ⊓ fixV L := by
    rw [Subgroup.map_inf _ _ _ g.injective, hfix]
  rw [hgI, ← hinf]
  exact s16t3_natShapeGood_map hgn hI₀good

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
