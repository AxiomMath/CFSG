module

public import CFSG.Quasithin.Vol2.Ch11SecA13
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Vol2.Ch11SecA13Comm
public import CFSG.Quasithin.Vol2.Ch11SecA13Line2
public import CFSG.Quasithin.Vol2.Ch11SecAViN13

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem centralizer_V_of_perfect_le_M (hLp : FactLineSp4) (hLg : FactLineG2)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hk : ¬ KindSL3 L (fsuV T I) n)
    {U₂ : Subgroup G} (hU₂ : IsVi T L I n 2 U₂) {K : Subgroup G} (hKK : ⁅K, K⁆ = K)
    (hKM : K ≤ Subgroup.normalizer (L : Set G))
    (hKV : K ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hKN : K ≤ Subgroup.normalizer (U₂ : Set G))
    (hKL₂ : ⁅K, LOf L U₂⁆ ≤ pCoreOf 2 (LOf L U₂)) :
    K ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  have hUV := IsVi.le_fsuV hU₂
  have hP := perfCentFacts hLp hLg h1102 h hk hU₂
  have hfix := hP (autOn K (fsuV T I)) (autOn_perfect hKV hKK)
    (fun g hg => by
      obtain ⟨k, hk', hkV, rfl⟩ := mem_autOn_iff.mp hg
      exact conjV_normalizes_autOn (hKM hk') hkV)
    (fun g hg => by
      obtain ⟨k, hk', hkV, rfl⟩ := mem_autOn_iff.mp hg
      exact conjV_mem_stabW_centralizer (hKM hk') hkV)
    (fun g hg => by
      obtain ⟨k, hk', hkV, rfl⟩ := mem_autOn_iff.mp hg
      exact (conjV_mem_stabW_iff hUV hkV).mpr (hKN hk'))
    (fun g hg s hs => by
      obtain ⟨k, hk', hkV, rfl⟩ := mem_autOn_iff.mp hg
      rw [perfectCore_eq_autOn_lOf h hUV] at hs
      obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hs
      rw [pCoreOf_perfectCore_eq h1102 h hUV, ← conjV_inv, ← conjV_inv, ← conjV_mul,
        ← conjV_mul, ← conjV_mul]
      refine conjV_mem_autOn ?_ _
      have := hKL₂ (Subgroup.commutator_mem_commutator hk' hl)
      simpa [commutatorElement_def, mul_assoc] using this)
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hkV := hKV hk
  have e := congrArg Subtype.val (hfix (conjV (fsuV T I) k hkV) (conjV_mem_autOn hk hkV)
    ⟨v, hv⟩)
  rw [conjV_apply_coe] at e
  calc v * k = (k * v * k⁻¹) * k := by rw [e]
    _ = k * v := by group

theorem stmt11_1_3_of (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat) (hF : NatFacts)
    (hG2 : FactG2DerivedOrder) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1112 : Stmt11_1_2) (hL3 : FactLineSL3) (hLp : FactLineSp4) (hLg : FactLineG2) :
    Stmt11_1_3 := by
  intro G _ _ T L I n V₂ h hV₂
  have hV₂V := IsVi.le_fsuV hV₂
  obtain ⟨V₁, hV₁, -⟩ := isVi_existsUnique hF h1102 h (i := 1) le_rfl (by norm_num)
  obtain ⟨X, hX⟩ := exists_isCartanX h
  obtain ⟨K₂, -, hK₂, -, -, hor⟩ := h1112 G T L I n 2 V₂ V₁ V₂ X h (Or.inr rfl) hV₂ hV₁ hV₂ hX
  have hC : quasithinIsCComponent (LOf L V₂) (Subgroup.normalizer (V₂ : Set G)) := by
    rcases hor with heq | ⟨h21, -⟩
    · rw [heq]
      exact hK₂
    · omega
  refine ⟨hC, not_lOf_le_centralizer hL3 hLp hLg h1102 h hV₂, fun K hK hKC => ?_⟩
  by_contra hne
  have := h.fsu.simple
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  have hKL₂ : ⁅K, LOf L V₂⁆ ≤ pCoreOf 2 (LOf L V₂) :=
    (QuasithinUnique.Vol2Native.lemma_1_2_1_two hloc h37
      (pCoreOf_normalizer_ne_bot_vi h (by norm_num) hV₂) hK hC hne).1.trans inf_le_right
  have hO₂ := pCoreOf_lOf_le_centralizer hL3 hLp hLg h1102 h hV₂
  have hKN : K ≤ Subgroup.normalizer (V₂ : Set G) := le_of_mem_cComp hK
  have hL₂N : LOf L V₂ ≤ Subgroup.normalizer (V₂ : Set G) :=
    (iInf_le (derivedSeriesOf _) 0).trans inf_le_right
  have hcomm : ∀ k ∈ K, ∀ l ∈ LOf L V₂, ∀ v ∈ V₂,
      k * (l * v * l⁻¹) * k⁻¹ = l * (k * v * k⁻¹) * l⁻¹ := by
    intro k hk l hl v hv
    have hc : ⁅k, l⁆ ∈ Subgroup.centralizer (V₂ : Set G) :=
      hO₂ (hKL₂ (Subgroup.commutator_mem_commutator hk hl))
    have hkv : k * v * k⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hKN hk) v).mp hv
    have hlkv : l * (k * v * k⁻¹) * l⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (hL₂N hl) _).mp hkv
    have hc' := Subgroup.mem_centralizer_iff.mp hc _ hlkv
    rw [commutatorElement_def] at hc'
    calc k * (l * v * l⁻¹) * k⁻¹
        = (k * l * k⁻¹ * l⁻¹) * (l * (k * v * k⁻¹) * l⁻¹) * (k * l * k⁻¹ * l⁻¹)⁻¹ := by group
      _ = l * (k * v * k⁻¹) * l⁻¹ := by rw [← hc']; group
  have hKY := centralizer_commS_of_perfect hL3 hLp hLg h1102 h hV₂ hK.2.1 hKN hcomm
  apply hKC
  by_cases hZ : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥
  ·
    have hd := (lineFacts hL3 hLp hLg h1102 h hV₂).2.2.2.1
    have hZ' : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
      rw [← inf_centralizer_subgroupOf, hZ, Subgroup.bot_subgroupOf]
    rw [hZ', sup_bot_eq] at hd
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : (⟨v, hV₂V hv⟩ : ↥(fsuV T I)) ∈ commS (perfectCore (autOn L (fsuV T I) ⊓
        stabW (V₂.subgroupOf (fsuV T I)))) (V₂.subgroupOf (fsuV T I)) := by
      rw [← hd]
      exact hv
    have e := hKY k hk _ hv'
    calc v * k = (k * v * k⁻¹) * k := by rw [e]
      _ = k * v := by group
  ·
    obtain ⟨-, -, h3, -, -⟩ := h1103 G T L I n h
    obtain ⟨hk', hVM, -, -⟩ := h3.resolve_left fun h' => hZ h'.1
    have hk : ¬ KindSL3 L (fsuV T I) n := by
      intro hs
      rcases hk' with hp | hg
      · exact kind_not_SL3_Sp4 (by have := h.one_lt; omega) hs hp
      · exact kind_not_SL3_G2 hG2 h.one_lt hs hg
    have hKZ : K ≤ Subgroup.normalizer
        ((fsuV T I ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      intro k hk
      refine mem_normalizer_of_map_le ?_
      rintro _ ⟨z, hz, rfl⟩
      have hz2 : z ∈ V₂ := IsVi.cV_le hV₂ hz
      have hkz : k * z * k⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hKN hk) z).mp hz2
      have hfz := (fixed_lOf_iff hL3 hLp hLg h1102 h hV₂ hz2).mpr (Subgroup.mem_inf.mp hz).2
      have : (MulAut.conj k).toMonoidHom z = k * z * k⁻¹ := by simp
      rw [this]
      refine Subgroup.mem_inf.mpr ⟨hV₂V hkz, (fixed_lOf_iff hL3 hLp hLg h1102 h hV₂ hkz).mp ?_⟩
      intro l hl
      have hl' : k⁻¹ * l * k ∈ LOf L V₂ := by
        have hkL : k⁻¹ ∈ Subgroup.normalizer (LOf L V₂ : Set G) := by
          refine Subgroup.inv_mem _ ?_
          refine mem_normalizer_of_map_le ?_
          rintro _ ⟨m, hm, rfl⟩
          have hcm : ⁅k, m⁆ ∈ LOf L V₂ := (Subgroup.map_subtype_le _)
            (hKL₂ (Subgroup.commutator_mem_commutator hk hm))
          have e : (MulAut.conj k).toMonoidHom m = ⁅k, m⁆ * m := by
            simp [commutatorElement_def]
          rw [e]
          exact (LOf L V₂).mul_mem hcm hm
        have := (Subgroup.mem_normalizer_iff.mp hkL l).mp hl
        simpa using this
      have e := hfz _ hl'
      calc l * (k * z * k⁻¹) * l⁻¹ = k * ((k⁻¹ * l * k) * z * (k⁻¹ * l * k)⁻¹) * k⁻¹ := by group
        _ = k * z * k⁻¹ := by rw [e]
    have hKM : K ≤ Subgroup.normalizer (L : Set G) := by
      refine le_trans hKZ (normalizer_le_of_isPGroup h331 h
        ((isPGroup_fsuV h).to_le inf_le_left) hZ (sup_le ?_ ?_))
      · intro l hl
        exact mem_normalizer_inf (L_le_normalizer_fsuV h hl)
          (mem_normalizer_centralizer (Subgroup.le_normalizer hl))
      · intro t ht
        exact mem_normalizer_inf (T_le_normalizer_fsuV T I ht)
          (mem_normalizer_centralizer (h.normal ht))
    have hKV : K ≤ Subgroup.normalizer (fsuV T I : Set G) := by
      rw [hVM]
      exact hKM.trans (le_normalizer_conjClosure _ _)
    exact (centralizer_V_of_perfect_le_M hLp hLg h1102 h hk hV₂ hK.2.1 hKM hKV hKN hKL₂).trans
      (Subgroup.centralizer_le (by exact_mod_cast hV₂V))

end CFSG.Quasithin.Vol2.Ch11.SecA
