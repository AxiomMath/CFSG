module

public import CFSG.Quasithin.EmptyFaithful.S153D50

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def TrivialOnDiagram {G : Type} [Group G] (A L SL : Subgroup G) : Prop :=
  A ≤ Subgroup.normalizer (L : Set G) ∧
    ∀ P : Subgroup G, IsParabolic2 L P → L ⊓ Subgroup.normalizer (SL : Set G) ≤ P →
      A ≤ Subgroup.normalizer (P : Set G)

@[expose] def Input15320Diagram : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → (IsSL3Quot L ∨ IsSp4Quot L) →
      TrivialOnDiagram (Sgp153 T V₁) L (Sgp153 T V₁ ⊓ L)

@[expose] def Input15320Overgroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → (IsSL3Quot L ∨ IsSp4Quot L) →
      ∀ X : Subgroup G, Sgp153 T V₁ ⊓ L ≤ X → X ≤ L ⊔ Yp → Group.IsSolvable ↥X →
        IsSylowTwoOf (pCoreOf 2 X) X

@[expose] def Input15320Parabolics : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → (IsSL3Quot L ∨ IsSp4Quot L) →
      ∃ P₁ P₂ : Subgroup G, IsMaxParabolic2 L P₁ ∧ IsMaxParabolic2 L P₂ ∧ P₁ ≠ P₂ ∧
        L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ P₁ ∧
        L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ P₂ ∧
        ∀ P : Subgroup G, IsMaxParabolic2 L P →
          L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ P → P = P₁ ∨ P = P₂

namespace S153D

section Generic

variable {G : Type} [Group G]

theorem normalizer_conjSub (g : G) (W : Subgroup G) :
    Subgroup.normalizer ((B6.conjSub g W : Subgroup G) : Set G) =
      B6.conjSub g (Subgroup.normalizer (W : Set G)) := by
  ext x
  rw [B6.mem_conjSub, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h z
    have := h (g * z * g⁻¹)
    simp only [B6.mem_conjSub] at this
    have e1 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    have e2 : g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * z * (g⁻¹ * x * g)⁻¹ := by group
    rw [e1, e2] at this
    exact this
  · intro h z
    simp only [B6.mem_conjSub]
    have := h (g⁻¹ * z * g)
    have e2 : g⁻¹ * (x * z * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * z * g) * (g⁻¹ * x * g)⁻¹ := by group
    rw [e2]
    exact this

theorem isParabolic2_conjSub {L P : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (hP : IsParabolic2 L P) :
    IsParabolic2 L (B6.conjSub y P) := by
  obtain ⟨hPL, S', hS', hNS'⟩ := hP
  refine ⟨?_, B6.conjSub y S', ?_, ?_⟩
  · have := (B6.conjSub y).monotone hPL
    rwa [B6.conjSub_eq_self hy] at this
  · have := B6.isSylowTwoOf_conjSub hS' y
    rwa [B6.conjSub_eq_self hy] at this
  · rw [normalizer_conjSub]
    have h1 : L ⊓ B6.conjSub y (Subgroup.normalizer (S' : Set G)) =
        B6.conjSub y (L ⊓ Subgroup.normalizer (S' : Set G)) := by
      rw [OrderIso.map_inf, B6.conjSub_eq_self hy]
    rw [h1]
    exact (B6.conjSub y).monotone hNS'

theorem isMaxParabolic2_conjSub {L P : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (hP : IsMaxParabolic2 L P) :
    IsMaxParabolic2 L (B6.conjSub y P) := by
  obtain ⟨hpar, hne, hmax⟩ := hP
  have hy' : y⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem hy
  have hinv : ∀ X : Subgroup G, B6.conjSub y⁻¹ (B6.conjSub y X) = X := fun X => by
    rw [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  refine ⟨isParabolic2_conjSub hy hpar, fun h => hne ?_, fun Q hQ hQne hle => ?_⟩
  · have := congrArg (B6.conjSub y⁻¹) h
    rwa [hinv, B6.conjSub_eq_self hy'] at this
  · have h1 : P ≤ B6.conjSub y⁻¹ Q := by
      have := (B6.conjSub y⁻¹).monotone hle
      rwa [hinv] at this
    have h2 : B6.conjSub y⁻¹ Q = P := by
      refine hmax _ (isParabolic2_conjSub hy' hQ) (fun hQL => hQne ?_) h1
      have := congrArg (B6.conjSub y) hQL
      rwa [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one, B6.conjSub_eq_self hy] at this
    have := congrArg (B6.conjSub y) h2
    rwa [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one] at this

theorem le_normalizer_of_two {Yp P₁ P₂ : Subgroup G} (hYp : oTwoUpper Yp = Yp) (hne : P₁ ≠ P₂)
    (h1 : ∀ y ∈ Yp, B6.conjSub y P₁ = P₁ ∨ B6.conjSub y P₁ = P₂)
    (h2 : ∀ y ∈ Yp, B6.conjSub y P₂ = P₁ ∨ B6.conjSub y P₂ = P₂) :
    Yp ≤ Subgroup.normalizer (P₁ : Set G) := by
  rw [← hYp]
  refine oTwoUpper_le_of_pow_mem (fun x hx => ⟨1, ?_⟩)
  have hxx : B6.conjSub (x * x) P₁ = P₁ := by
    rw [B6.conjSub_mul]
    rcases h1 x hx with e | e
    · rw [e, e]
    · rcases h2 x hx with e' | e'
      · rw [e, e']
      · exact absurd ((B6.conjSub x).injective (e.trans e'.symm)) hne
  have : x ^ 2 ^ 1 = x * x := by rw [pow_one, pow_two]
  rw [this]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hxx

section Finite

variable [Finite G]

theorem isSylowTwoOf_inf_of_isSubnormal {T H L : Subgroup G} (h : IsSubnormal L H) :
    IsSylowTwoOf T H → IsSylowTwoOf (T ⊓ L) L := by
  induction h with
  | refl K =>
    intro hT
    rwa [inf_eq_left.mpr hT.1]
  | @step L M K hLM hN _ ih =>
    intro hT
    have h1 := ih hT
    have hnorm : M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hN
    have h2 := B6.isSylowTwoOf_inf_normal h1 hLM hnorm
    rwa [inf_assoc, inf_eq_right.mpr hLM] at h2

theorem le_of_normal_sylow {X Q D : Subgroup G} (hQ : IsSylowTwoOf Q X)
    (hQn : X ≤ Subgroup.normalizer (Q : Set G)) (hD : IsPGroup 2 D) (hDX : D ≤ X) : D ≤ Q := by
  obtain ⟨Q', hQ', hDQ'⟩ := B6.exists_isSylowTwoOf_ge hD hDX
  obtain ⟨g, hg, hgQ⟩ := B6.isSylowTwoOf_exists_conj hQ hQ'
  rw [hgQ, B6.conjSub_eq_self (hQn hg)] at hDQ'
  exact hDQ'

end Finite

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem input15320M_of_kernel (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (kA : Input15320Diagram) (kB : Input15320Overgroups) (kC : Input15320Parabolics) :
    Input15320M := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c _ _ _
  have key : IsSL3Quot L ∨ IsSp4Quot L → False := by
    intro hlie
    have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
    have hI : IsHPlus Yp (Sgp153 T V₁) M I := c.ctx.inH
    have hF : Facts15311 T M V₁ Yp I := c.facts
    obtain ⟨hLc, hLn, -, -, -, -⟩ := c.conc
    have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
    have hLle : L ≤ I := le_of_mem_cComp hLI
    have hSL : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
      isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hLI) hF.sylow
    have c15316 : Ctx15316 T Mc M V₁ V₂ Yp I L t := c.toCtx15316
    obtain ⟨-, hAP⟩ := kA G T Mc M V₁ V₂ Yp I L t c15316 hlie
    have hBsolv := kB G T Mc M V₁ V₂ Yp I L t c15316 hlie
    obtain ⟨P₁, P₂, hP₁, hP₂, hne, hB₁, hB₂, huniq⟩ := kC G T Mc M V₁ V₂ Yp I L t c15316 hlie
    have hYL : Yp ≤ Subgroup.normalizer (L : Set G) := Yp_le_normalizer h37 h38 hh hI hLI
    have hSLsolv : Group.IsSolvable ↥(Sgp153 T V₁ ⊓ L) := F1.isSolvable_of_isPGroup_two hSL.2.1
    have hSLn : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (Yp : Set G) :=
      inf_le_left.trans (Sgp153_le_normalizer_Yp hh)
    have hXsolv : Group.IsSolvable ↥(Yp ⊔ (Sgp153 T V₁ ⊓ L)) :=
      F1.isSolvable_sup_of_le_normalizer (isSolvable_Yp hF) hSLsolv hSLn
    have hXle : Yp ⊔ (Sgp153 T V₁ ⊓ L) ≤ L ⊔ Yp :=
      sup_le le_sup_right (inf_le_right.trans le_sup_left)
    have hQ : IsSylowTwoOf (pCoreOf 2 (Yp ⊔ (Sgp153 T V₁ ⊓ L))) (Yp ⊔ (Sgp153 T V₁ ⊓ L)) :=
      hBsolv _ le_sup_right hXle hXsolv
    have hQn : Yp ⊔ (Sgp153 T V₁ ⊓ L) ≤
        Subgroup.normalizer (pCoreOf 2 (Yp ⊔ (Sgp153 T V₁ ⊓ L)) : Set G) :=
      le_normalizer_pCoreOf 2 _
    have hSLQ : Sgp153 T V₁ ⊓ L ≤ pCoreOf 2 (Yp ⊔ (Sgp153 T V₁ ⊓ L)) :=
      le_of_normal_sylow hQ hQn hSL.2.1 le_sup_right
    have hQL : pCoreOf 2 (Yp ⊔ (Sgp153 T V₁ ⊓ L)) ⊓ L ≤ Sgp153 T V₁ ⊓ L :=
      (A4.isSylowTwoOf_iff_maximal.mp hSL).2.2 _ inf_le_right hQ.2.1.to_inf_left
        (le_inf hSLQ inf_le_right)
    have hYSL : Yp ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := by
      have key1 : ∀ y ∈ Yp, ∀ x ∈ Sgp153 T V₁ ⊓ L, y * x * y⁻¹ ∈ Sgp153 T V₁ ⊓ L := by
        intro y hy x hx
        have hyQ : y ∈ Subgroup.normalizer
            (pCoreOf 2 (Yp ⊔ (Sgp153 T V₁ ⊓ L)) : Set G) := hQn (Subgroup.mem_sup_left hy)
        have h1 : y * x * y⁻¹ ∈ pCoreOf 2 (Yp ⊔ (Sgp153 T V₁ ⊓ L)) :=
          (Subgroup.mem_normalizer_iff.mp hyQ x).mp (hSLQ hx)
        have h2 : y * x * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hYL hy) x).mp hx.2
        exact hQL ⟨h1, h2⟩
      intro y hy
      refine B6.mem_normalizer_of_forall_mem (key1 y hy) (fun x hx => ?_)
      have := key1 y⁻¹ (inv_mem hy) x hx
      rwa [inv_inv] at this
    have hyB : ∀ y ∈ Yp, B6.conjSub y
        (L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G)) =
        L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := by
      intro y hy
      rw [OrderIso.map_inf, B6.conjSub_eq_self (hYL hy),
        B6.conjSub_eq_self (Subgroup.le_normalizer (hYSL hy))]
    have hconj : ∀ y ∈ Yp, ∀ P : Subgroup G, IsMaxParabolic2 L P →
        L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ P →
        B6.conjSub y P = P₁ ∨ B6.conjSub y P = P₂ := by
      intro y hy P hP hBP
      refine huniq _ (isMaxParabolic2_conjSub (hYL hy) hP) ?_
      have := (B6.conjSub y).monotone hBP
      rwa [hyB y hy] at this
    have hYp : oTwoUpper Yp = Yp := hh.oTwoUpper_eq
    have hYP₁ : Yp ≤ Subgroup.normalizer (P₁ : Set G) :=
      le_normalizer_of_two hYp hne (fun y hy => hconj y hy P₁ hP₁ hB₁)
        (fun y hy => hconj y hy P₂ hP₂ hB₂)
    have hYP₂ : Yp ≤ Subgroup.normalizer (P₂ : Set G) :=
      le_normalizer_of_two hYp hne.symm (fun y hy => (hconj y hy P₂ hP₂ hB₂).symm)
        (fun y hy => (hconj y hy P₁ hP₁ hB₁).symm)
    have hPM : ∀ P : Subgroup G, IsMaxParabolic2 L P →
        L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ P →
        Yp ≤ Subgroup.normalizer (P : Set G) → P ≤ M := by
      intro P hP hBP hYP
      have hSP : Sgp153 T V₁ ≤ Subgroup.normalizer (P : Set G) := hAP P hP.1 hBP
      have hYS : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (P : Set G) := sup_le hYP hSP
      have hPle : P ≤ L := hP.1.1
      have hXI : P ⊔ (Yp ⊔ Sgp153 T V₁) ≤ I := sup_le (hPle.trans hLle) hI.1.1
      have hne' : P ⊔ (Yp ⊔ Sgp153 T V₁) ≠ I := by
        intro heq
        have hIN : I ≤ Subgroup.normalizer (P : Set G) :=
          heq ▸ sup_le Subgroup.le_normalizer hYS
        have hLN : L ≤ Subgroup.normalizer (P : Set G) := hLle.trans hIN
        obtain ⟨-, S', hS', hNS'⟩ := hP.1
        have hS'P : S' ≤ P := (le_inf hS'.1 Subgroup.le_normalizer).trans hNS'
        have hS'syl : IsSylowTwoOf S' P := A4.isSylowTwoOf_mono hS' hS'P hPle
        have hfr := B6.frattini_two hPle hLN hS'syl
        apply hP.2.1
        refine le_antisymm hPle ?_
        exact hfr.trans (sup_le le_rfl hNS')
      exact le_sup_left.trans (le_M_of_minCE c.ctx hF c.minimal hXI le_sup_right hne')
    have hLsup : P₁ ⊔ P₂ = L := by
      by_contra hQne
      have hQpar : IsParabolic2 L (P₁ ⊔ P₂) := by
        obtain ⟨-, S', hS', hNS'⟩ := hP₁.1
        exact ⟨sup_le hP₁.1.1 hP₂.1.1, S', hS', hNS'.trans le_sup_left⟩
      have e1 : P₁ ⊔ P₂ = P₁ := hP₁.2.2 _ hQpar hQne le_sup_left
      have e2 : P₁ ⊔ P₂ = P₂ := hP₂.2.2 _ hQpar hQne le_sup_right
      exact hne (e1.symm.trans e2)
    have hP₁M := hPM P₁ hP₁ hB₁ hYP₁
    have hP₂M := hPM P₂ hP₂ hB₂ hYP₂
    exact hLn (le_inf (hLsup ▸ sup_le hP₁M hP₂M) hLle)
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

end Main

end S153D

end CFSG.Quasithin
