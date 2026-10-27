module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16t3_map_mem_fixV_iff {H : Subgroup (MulAut W)} {g : MulAut W}
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

private theorem s16t3_stableUnder_commSub {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : StableUnder L J) : StableUnder L (commSub J L) := by
  intro l hl i hi
  unfold commSub at hi ⊢
  induction hi using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hc
    have e : l (x w * w⁻¹) = ((l * x) w * w⁻¹) * (l w * w⁻¹)⁻¹ := by
      simp only [map_mul, map_inv, MulAut.mul_apply]
      group
    rw [e]
    exact mul_mem (Subgroup.subset_closure ⟨l * x, L.mul_mem hl hx, w, hw, rfl⟩)
      (inv_mem (Subgroup.subset_closure ⟨l, hl, w, hw, rfl⟩))
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

theorem s16t3_realizes_map_of_mem_normalizer {D : FFModel} {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} {g : MulAut W} (hg : g ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (h : D.Realizes H U Z) : D.Realizes H (U.map g.toMonoidHom) (Z.map g.toMonoidHom) := by
  obtain ⟨π, hπ⟩ := h
  let π' : D.Gam →* ↥H :=
    { toFun := fun γ => ⟨g * (π γ : MulAut W) * g⁻¹,
        conj_mem_of_mem_normalizer hg (π γ).2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hπ'val : ∀ γ : D.Gam, ((π' γ : ↥H) : MulAut W) = g * (π γ : MulAut W) * g⁻¹ :=
    fun γ => rfl
  refine ⟨π', ?_⟩
  obtain ⟨hπs, hZU, hkersec, hUinv, hZinv, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hπ
  refine ⟨?_, Subgroup.map_mono hZU, hkersec, ?_, ?_, hsec, hkerinv, ?_⟩
  · intro x
    have hxg : g⁻¹ * (x : MulAut W) * g ∈ H := inv_conj_mem_of_mem_normalizer hg x.2
    obtain ⟨γ, hγ⟩ := hπs ⟨g⁻¹ * (x : MulAut W) * g, hxg⟩
    exact ⟨γ, by ext; rw [hπ'val, congrArg Subtype.val hγ]; group⟩
  · intro h u hu
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
    exact Subgroup.mem_map.2 ⟨(g⁻¹ * (h : MulAut W) * g) u',
      hUinv ⟨g⁻¹ * (h : MulAut W) * g, inv_conj_mem_of_mem_normalizer hg h.2⟩ u' hu',
      by simp [MulAut.mul_apply]⟩
  · intro h z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
    exact Subgroup.mem_map.2 ⟨(g⁻¹ * (h : MulAut W) * g) z',
      hZinv ⟨g⁻¹ * (h : MulAut W) * g, inv_conj_mem_of_mem_normalizer hg h.2⟩ z' hz',
      by simp [MulAut.mul_apply]⟩
  · have hpre : ∀ x : ↥(U.map g.toMonoidHom), g⁻¹ (x : W) ∈ U := by
      intro x
      obtain ⟨u, hu, hx⟩ := Subgroup.mem_map.1 x.2
      rw [← hx]; simpa using hu
    let β' : ↥(U.map g.toMonoidHom) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
      { toFun := fun x => β ⟨g⁻¹ (x : W), hpre x⟩
        map_one' := by
          change β (⟨g⁻¹ (1 : W), hpre 1⟩ : ↥U) = 1
          rw [show (⟨g⁻¹ (1 : W), hpre 1⟩ : ↥U) = 1 from Subtype.ext (by simp)]
          exact map_one β
        map_mul' := fun x y => by
          change β (⟨g⁻¹ ((x : W) * (y : W)), hpre (x * y)⟩ : ↥U) =
            β (⟨g⁻¹ (x : W), hpre x⟩ : ↥U) * β (⟨g⁻¹ (y : W), hpre y⟩ : ↥U)
          rw [← map_mul]
          congr 1
          ext
          simp [map_mul] }
    refine ⟨β', ?_, ?_, ?_⟩
    · intro q
      obtain ⟨u, hu⟩ := hβs q
      refine ⟨⟨g (u : W), Subgroup.mem_map.2 ⟨u, u.2, rfl⟩⟩, ?_⟩
      have hβval : β' ⟨g (u : W), Subgroup.mem_map.2 ⟨u, u.2, rfl⟩⟩ =
          β (⟨g⁻¹ (g (u : W)),
            hpre ⟨g (u : W), Subgroup.mem_map.2 ⟨u, u.2, rfl⟩⟩⟩ : ↥U) := rfl
      rw [hβval]
      have hval : (⟨g⁻¹ (g (u : W)),
          hpre ⟨g (u : W), Subgroup.mem_map.2 ⟨u, u.2, rfl⟩⟩⟩ : ↥U) = u :=
        Subtype.ext (by simp)
      rw [hval]
      exact hu
    · intro x
      have hβval : β' x = β (⟨g⁻¹ (x : W), hpre x⟩ : ↥U) := rfl
      rw [hβval, hβk]
      constructor
      · intro hz
        exact Subgroup.mem_map.2 ⟨g⁻¹ (x : W), hz, by simp⟩
      · intro hx
        change g⁻¹ (x : W) ∈ Z
        obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx
        rw [show g⁻¹ (x : W) = z by rw [← hzx]; simp]
        exact hz
    · intro γ x m hu hm hβx
      have hpre' : ((π γ : ↥H) : MulAut W) (g⁻¹ (x : W)) ∈ U := by
        have hx' : g⁻¹ (((π' γ : ↥H) : MulAut W) (x : W)) ∈ U :=
          hpre ⟨((π' γ : ↥H) : MulAut W) (x : W), hu⟩
        rw [hπ'val γ] at hx'
        simpa [MulAut.mul_apply] using hx'
      have hβx' : β (⟨g⁻¹ (x : W), hpre x⟩ : ↥U) = QuotientGroup.mk m := hβx
      have h1 := hβe γ (⟨g⁻¹ (x : W), hpre x⟩ : ↥U) m hpre' hm hβx'
      have hβval : β' (⟨((π' γ : ↥H) : MulAut W) (x : W), hu⟩ : ↥(U.map g.toMonoidHom)) =
          β (⟨g⁻¹ (((π' γ : ↥H) : MulAut W) (x : W)),
            hpre ⟨((π' γ : ↥H) : MulAut W) (x : W), hu⟩⟩ : ↥U) := rfl
      have hβeq : β (⟨g⁻¹ (((π' γ : ↥H) : MulAut W) (x : W)),
            hpre ⟨((π' γ : ↥H) : MulAut W) (x : W), hu⟩⟩ : ↥U) =
          β (⟨((π γ : ↥H) : MulAut W) (g⁻¹ (x : W)), hpre'⟩ : ↥U) := by
        apply congrArg β
        apply Subtype.ext
        change g⁻¹ (((π' γ : ↥H) : MulAut W) (x : W)) =
          ((π γ : ↥H) : MulAut W) (g⁻¹ (x : W))
        rw [hπ'val γ]
        simp [MulAut.mul_apply]
      rw [hβval, hβeq]
      exact h1

private theorem s16t3_sumOfNat_map {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} {k : ℕ} {g : MulAut W}
    (hN : ∀ (I Z' : Subgroup W), N L I Z' → N L (I.map g.toMonoidHom) (Z'.map g.toMonoidHom))
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

theorem SumOfNatShape.map_of_mem_normalizer {L : Subgroup (MulAut W)} {U Z : Subgroup W} {k : ℕ}
    {g : MulAut W} (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hS : SumOfNatShape L U Z k) :
    SumOfNatShape L (U.map g.toMonoidHom) (Z.map g.toMonoidHom) k := by
  rcases hS with ⟨n, hSL | hSp | hOp | hOm | hAlt⟩
  · refine ⟨n, Or.inl ⟨hSL.1, ?_⟩⟩
    refine s16t3_sumOfNat_map (N := fun H U Z => BinaryNaturalSL H U Z n 1) ?_ hSL.2
    intro I Z' hI
    obtain ⟨K, hKf, hKfin, hKcard, hReal⟩ := hI
    exact ⟨K, hKf, hKfin, hKcard, s16t3_realizes_map_of_mem_normalizer hg hReal⟩
  · refine ⟨n, Or.inr (Or.inl ⟨hSp.1, ?_⟩)⟩
    refine s16t3_sumOfNat_map (N := fun H U Z => NatSpn H U Z n 1) ?_ hSp.2
    intro I Z' hI
    obtain ⟨hev, K, hKf, hKfin, hKcard, hReal⟩ := hI
    exact ⟨hev, K, hKf, hKfin, hKcard, s16t3_realizes_map_of_mem_normalizer hg hReal⟩
  · refine ⟨n, Or.inr (Or.inr (Or.inl ⟨hOp.1, ?_⟩))⟩
    refine s16t3_sumOfNat_map (N := fun H U Z => NatOmegaPlus H U Z n 1) ?_ hOp.2
    intro I Z' hI
    obtain ⟨hev, K, hKf, hKfin, hKcard, hReal⟩ := hI
    exact ⟨hev, K, hKf, hKfin, hKcard, s16t3_realizes_map_of_mem_normalizer hg hReal⟩
  · refine ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hOm.1, ?_⟩)))⟩
    refine s16t3_sumOfNat_map (N := fun H U Z => NatOmegaMinus H U Z n 1) ?_ hOm.2
    intro I Z' hI
    obtain ⟨hev, K, hKf, hKfin, b, c, hKcard, hpoly, hReal⟩ := hI
    exact ⟨hev, K, hKf, hKfin, b, c, hKcard, hpoly,
      s16t3_realizes_map_of_mem_normalizer hg hReal⟩
  · refine ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ⟨hAlt.1, ?_⟩)))⟩
    refine s16t3_sumOfNat_map (N := fun H U Z => AlternatingNatural H U Z n) ?_ hAlt.2
    intro I Z' hI
    exact s16t3_realizes_map_of_mem_normalizer hg hI

variable [Finite W] {A L T : Subgroup (MulAut W)}

theorem ThreeNat.exists_natural_irr (h : ThreeNat A L T) :
    ∃ I ∈ irrSet L, SumOfNatShape L I (I ⊓ fixV L) 1 := by
  obtain ⟨J, hZJ, -, hJnat⟩ := SumOfNatShape.exists_summand h.sum (0 : Fin 3)
  have hJirr := SumOfNatShape.isIrrOn h.quasi hJnat
  have hperf : ⁅L, L⁆ = L := by
    have htop : commutator ↥L = ⊤ := h.quasi.1
    have hmap := congrArg (Subgroup.map (L.subtype : ↥L →* MulAut W)) htop
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, L.range_subtype] at hmap
    exact hmap
  have hstable : StableUnder L (commSub J L) := s16t3_stableUnder_commSub hJirr.2.1
  have hIJ : commSub J L ≤ J := commSub_le_of_invariant hJirr.2.1
  have hcomm : commSub (commSub J L) L = commSub J L :=
    CFSG.Quasithin.SmithD310U.commSub_commSub_eq hperf J
  have hIZ : commSub J L ⊔ fixV L = J := by
    have hle : commSub J L ⊔ fixV L ≤ J := sup_le hIJ hZJ
    have hstab : StableUnder L (commSub J L ⊔ fixV L) := by
      intro l hl x hx
      rcases Subgroup.mem_sup.1 hx with ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mem_sup.2
        ⟨l a, hstable l hl a ha, l b, hJirr.2.2.1 l hl b hb, (map_mul l a b).symm⟩
    rcases hJirr.2.2.2 (commSub J L ⊔ fixV L) hstab le_sup_right hle with hZ | hJ
    · exfalso
      obtain ⟨l, hl, u, hu, hlu⟩ := SumOfNatShape.exists_move h.quasi hJnat
      have hgen : l u * u⁻¹ ∈ commSub J L := Subgroup.subset_closure ⟨l, hl, u, hu, rfl⟩
      have hleZ : commSub J L ≤ fixV L := by rw [← hZ]; exact le_sup_left
      exact hlu (hleZ hgen)
    · exact hJ
  have hInat : SumOfNatShape L (commSub J L) (commSub J L ⊓ fixV L) 1 :=
    SumOfNatShape.restrict hJnat hIJ hstable hIZ
  exact ⟨commSub J L, ⟨hcomm, SumOfNatShape.isIrrOn h.quasi hInat⟩, hInat⟩

theorem ThreeNat.natural_of_mem_irrSet (h : ThreeNat A L T) {I : Subgroup W}
    (hI : I ∈ irrSet L) : SumOfNatShape L I (I ⊓ fixV L) 1 := by
  obtain ⟨I₀, hI₀, hI₀nat⟩ := h.exists_natural_irr
  obtain ⟨g, hg, hgI⟩ := h.trans I₀ hI₀ I hI
  have hgn : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := hg.2
  have hfix : (fixV L).map g.toMonoidHom = fixV L := by
    apply le_antisymm
    · intro w hw
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
      exact (s16t3_map_mem_fixV_iff hgn z).2 hz
    · intro w hw
      exact Subgroup.mem_map.2 ⟨g⁻¹ w,
        (s16t3_map_mem_fixV_iff hgn (g⁻¹ w)).1 (by simpa using hw), by simp⟩
  have hinf : (I₀ ⊓ fixV L).map g.toMonoidHom = I₀.map g.toMonoidHom ⊓ fixV L := by
    rw [Subgroup.map_inf _ _ _ g.injective, hfix]
  rw [hgI, ← hinf]
  exact SumOfNatShape.map_of_mem_normalizer hgn hI₀nat

theorem ThreeNat.exists_stable_natural (h : ThreeNat A L T) :
    ∃ I ∈ irrSet L, StableUnder T I ∧ SumOfNatShape L I (I ⊓ fixV L) 1 := by
  obtain ⟨I, hI, hT⟩ := h.exists_stable_irr h.odd_card_irrSet
  exact ⟨I, hI, hT, h.natural_of_mem_irrSet hI⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
