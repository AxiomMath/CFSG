module

public import CFSG.Quasithin.EmptyFaithful.R3c11L3
public import CFSG.Quasithin.EmptyFaithful.R3c10Elim

public section

namespace CFSG.Quasithin.R3c10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open scoped commutatorElement

section Core

variable {G : Type} [Group G] [Finite G]

theorem borel_elim_core {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L)
    (hD : BorelData (↥L ⧸ Subgroup.center ↥L))
    (hPAR : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L → Nat.card V₂ = 4 →
      (∀ x ∈ V₂, x ∈ centerOf L → x = 1) → V₂ ≤ Sgp153 T V₁ ⊓ L →
      Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (V₂ : Set G) →
      ∀ H : Subgroup G, Sgp153 T V₁ ⊓ L ≤ H → H ≤ L → H ≤ Subgroup.normalizer (V₂ : Set G) →
        H ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ∨ L ≤ H) : False := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hV2S : V₂ ≤ Sgp153 T V₁ := R3c8.V₂_le_Sgp153 hh.hyp hh.decomp
  have hVS : VZ T M ≤ Sgp153 T V₁ := by
    intro v hv
    refine ⟨hh.hyp.VZ_le_T hv, A4.mem_normalizer_of_conj_mem fun k hk => ?_⟩
    have hc' := congrArg Subtype.val
      (hh.hyp.elemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨k, hh.decomp.le₁ hk⟩)
    have : v * k * v⁻¹ = k := by
      have h1 : v * k = k * v := hc'
      rw [h1]
      group
    rw [this]
    exact hk
  have hV1S : V₁ ≤ Sgp153 T V₁ := fun v hv => hVS (hh.decomp.le₁ hv)
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hYpM : Yp ≤ M := hh.Yp_le_Y153.trans (Y153_le Mc M)
  have hYpI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hq : CFSG.IsQuasisimple ↥L := c.c33.quasisimple
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  set Q : Subgroup G := Sgp153 T V₁ ⊓ L with hQdef
  have hMIY : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
    exact this.2
  have hMIV : M ⊓ I ≤ Subgroup.normalizer (V₂ : Set G) :=
    R3c8.MI_le_normalizer_V₂ hh o.b_V1 o.b_V2.1 c.facts.norm_eq
  have hV2Y : V₂ ≤ Yp := by
    have h1 : ⁅V₂, Yp⁆ ≤ Yp := by
      rw [Subgroup.commutator_le]
      intro v hv y hy
      have hvN : v ∈ Subgroup.normalizer (Yp : Set G) := hMIY ⟨hSM (hV2S hv), hSI (hV2S hv)⟩
      have h2 : v * y * v⁻¹ ∈ Yp := (Subgroup.mem_normalizer_iff.mp hvN y).mp hy
      have : ⁅v, y⁆ = (v * y * v⁻¹) * y⁻¹ := rfl
      rw [this]
      exact Yp.mul_mem h2 (Yp.inv_mem hy)
    rwa [o.b_V2.1] at h1
  have hYN : Yp ≤ Subgroup.normalizer (V₂ : Set G) := fun y hy => hMIV ⟨hYpM hy, hYpI hy⟩
  obtain ⟨eV⟩ := o.b_V2.2
  have hV4 : Nat.card V₂ = 4 := by
    rw [Nat.card_congr eV.toEquiv, Nat.card_eq_fintype_card]
    simp
  have hgen : Yp = Subgroup.closure {x : G | x ∈ Yp ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    apply le_antisymm
    · conv_lhs => rw [o.a_eq]
      rw [oPrimeResidualOf, Subgroup.closure_le]
      intro x hx
      have hxY : x ∈ Yp := by
        rw [o.a_eq]
        exact Subgroup.subset_closure hx
      exact Subgroup.subset_closure ⟨hxY, hx.2⟩
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
  have hact : ¬ Yp ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro hle
    have h1 : ⁅Yp, V₂⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    have h2 : ⁅V₂, Yp⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h1
    rw [o.b_V2.1] at h2
    have : Nat.card V₂ = 1 := by rw [h2]; simp
    omega
  have hfix : ∀ x ∈ V₂, (∀ a ∈ Yp, a * x = x * a) → x = 1 :=
    fixed_eq_one_of_gen hV4 hgen hYN hact
  have hSQ : Sgp153 T V₁ ≤ Subgroup.normalizer (Q : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hSL hs⟩
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hVQ : V₂ ≤ Q := le_inf hV2S hV2L
  have hQS : Q ≤ Sgp153 T V₁ := inf_le_left
  have hQV : Q ≤ Subgroup.normalizer (V₂ : Set G) := fun q hq => hMIV ⟨hSM (hQS hq), hSI (hQS hq)⟩
  have hVz : ∀ x ∈ V₂, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix x hx fun a ha => Subgroup.mem_centralizer_iff.mp hxc.2 a (hYL ha)
  have hYQ : Yp ≤ Subgroup.normalizer (Q : Set G) := by
    rcases hPAR hQsyl hV4 hVz hVQ hQV (Yp ⊔ Q) le_sup_right (sup_le hYL (inf_le_right : Q ≤ L))
        (sup_le hYN hQV) with h | h
    · exact le_sup_left.trans h
    · exact (c.c33.not_le (h.trans (sup_le hYpM (inf_le_left.trans hSM)))).elim
  have hXL : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (hYL.trans Subgroup.le_normalizer) hSL
  have hXQ : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (Q : Set G) := sup_le hYQ hSQ
  have hBX : Yp ⊔ Sgp153 T V₁ ≤
      Subgroup.normalizer ((L ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) : Set G) :=
    SBc2.le_normalizer_borel hXL hXQ
  have hcent := (R3c8.borelLift_of_pkg hq hZ hQsyl hD.pkg).1
  have hChar : CharTwo (L ⊓ Subgroup.normalizer (Q : Set G)) :=
    R3c8.charTwo_borel_of_cent hQsyl hcent
  have hBMI : L ⊓ Subgroup.normalizer (Q : Set G) ≤ M ⊓ I :=
    c.c33.inv_le _ (inf_le_left.trans (le_conjClosure L (Sgp153 T V₁))) hBX hChar
  have hBA : L ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Yp : Set G) :=
    hBMI.trans hMIY
  have hBV : L ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (V₂ : Set G) :=
    hBMI.trans hMIV
  have hVnZ : ¬ V₂ ≤ centerOf L := by
    intro hle
    apply hact
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' := (hle hv).2
    exact (Subgroup.mem_centralizer_iff.mp hv' y (hYL hy)).symm
  have hVA : ∀ x ∈ V₂, (∀ a ∈ Yp, x * a * x⁻¹ * a⁻¹ ∈ centerOf L) → x ∈ centerOf L := by
    intro x hx hcomm
    have hx1 : x = 1 := by
      refine hfix x hx fun a ha => ?_
      have hu := hcomm a ha
      have huV : x * a * x⁻¹ * a⁻¹ ∈ V₂ := by
        have h1 : a * x⁻¹ * a⁻¹ ∈ V₂ :=
          (Subgroup.mem_normalizer_iff.mp (hYN ha) x⁻¹).mp (V₂.inv_mem hx)
        have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
        rw [e]
        exact V₂.mul_mem hx h1
      have hu1 : x * a * x⁻¹ * a⁻¹ = 1 := by
        refine hfix _ huV fun b hb => ?_
        exact Subgroup.mem_centralizer_iff.mp hu.2 b (hYL hb)
      calc a * x = (x * a * x⁻¹ * a⁻¹)⁻¹ * (x * a) := by group
        _ = x * a := by rw [hu1]; group
    rw [hx1]
    exact Subgroup.one_mem _
  have hV1C : V₁ ≤ Subgroup.centralizer (L : Set G) := by
    intro v hv
    refine centralizes_of_borel_fixed hq hZ hQsyl hD (hSL (hV1S hv)) (hSQ (hV1S hv)) ?_
      hYL hBA ?_ hVQ hBV hVnZ hVA
    · have := hh.hyp.elemAbelian.2 v (hh.decomp.le₁ hv)
      rw [← sq]
      exact this
    · intro a ha
      have := Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp o.b_V1 hv) a ha
      exact this.symm
  exact o.c_comm (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hV1C)


theorem l3_elim {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) {f : ℕ} (hf : 2 ≤ f)
    (h : IsPSL 3 2 f (↥L ⧸ Subgroup.center ↥L)) : False :=
  borel_elim_core c o hN hYL (borelData_psl3 hf h)
    (fun hQsyl hV4 hVz hVQ hQV H hQH hHL hHV =>
      l3_par hf c.c33.center_eq hQsyl h hV4 hVz hVQ hQV H hQH hHL hHV)

end Core

section Cases

@[expose] def Lemma115LieRest (X : Type) [Group X] : Prop :=
  (((∃ f : ℕ, (f = 1 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 f) ∨
      (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f)) ∨
    ReeTitsModel X .Tits 2 1) ∨
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n 2 1)) ∨
  Nonempty (X ≃* alternatingGroup (Fin 6)) ∨ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1

theorem lemma115LieHigh_cases_rest {X : Type} [Group X] (h : Lemma115LieHigh X) :
    Lemma115LieRest X ∨ ∃ f : ℕ, 2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 f := by
  rcases h with (((⟨f, hfam⟩ | hTits) | hL45) | ⟨⟨e⟩⟩ | hU33)
  · rcases hfam with ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hodd, hf, hm⟩
    · by_cases hf1 : f = 1
      · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inl ⟨hf1, hm⟩⟩)))
      · exact Or.inr ⟨f, by omega, hm⟩
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hm⟩)⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inl ⟨hf, hm⟩))⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hm⟩)))⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr ⟨hodd, hf, hm⟩)))⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hTits)))
  · exact Or.inl (Or.inl (Or.inr hL45))
  · exact Or.inl (Or.inr (Or.inl ⟨e⟩))
  · exact Or.inl (Or.inr (Or.inr hU33))

end Cases

section Main

@[expose] def Input15343ElimLieRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieRest (↥L ⧸ Subgroup.center ↥L) → False

theorem input15343ElimLieHigh_of_rest (kR : Input15343ElimLieRest) : Input15343ElimLieHigh := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hHigh
  rcases lemma115LieHigh_cases_rest hHigh with hRest | ⟨f, hf, h⟩
  · exact kR G T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hRest
  · exact l3_elim c o hN hYL hf h

end Main

end CFSG.Quasithin.R3c10
