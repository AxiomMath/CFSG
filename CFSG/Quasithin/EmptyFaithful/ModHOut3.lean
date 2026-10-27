module

public import CFSG.Quasithin.EmptyFaithful.ModHOut2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Quasithin.EmptyFaithful.ModHNS
public import CFSG.Quasithin.EmptyFaithful.ModHOut1

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

structure ConfigData (Q : Type) [Group Q] (Sb Yb : Subgroup Q) : Prop where
  sylow : IsSylowTwoOf Sb ⊤
  normalizes : Sb ≤ Subgroup.normalizer (Yb : Set Q)
  solvable : Group.IsSolvable ↥Yb
  nine : 9 ∣ Nat.card ↥Yb
  s3s3 : ∃ φ : ↥(Yb ⊔ Sb) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), Function.Surjective φ
  maximal : ∀ N : Subgroup Q, IsPGroup 2 ↥N → N ≠ ⊥ → Yb ⊔ Sb ≤ Subgroup.normalizer (N : Set Q) →
    Subgroup.normalizer (N : Set Q) ≠ ⊤ →
      Subgroup.normalizer (N : Set Q) ≤ Subgroup.normalizer (Yb : Set Q)

@[expose] def Config (Q : Type) [Group Q] : Prop :=
  ¬ Group.IsSolvable Q ∧ ∃ Sb Yb : Subgroup Q, ConfigData Q Sb Yb

theorem ConfigData.of_equiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') {Sb Yb : Subgroup Q}
    (h : ConfigData Q Sb Yb) : ConfigData Q' (Sb.map e.toMonoidHom) (Yb.map e.toMonoidHom) := by
  obtain ⟨hS, hN, hsol, h9, ⟨φ, hφ⟩, hmin⟩ := h
  have hmapsup : (Yb ⊔ Sb).map e.toMonoidHom = Yb.map e.toMonoidHom ⊔ Sb.map e.toMonoidHom :=
    Subgroup.map_sup _ _ _
  refine ⟨CFSG.QuasithinUnique.Ch1.SporLat.isSylowTwoOf_map e hS, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact (R3c11.mem_normalizer_map_equiv_iff e Yb t₀).mpr (hN ht₀)
  · exact Group.isSolvable_of_surjective (f := e.toMonoidHom.subgroupMap Yb)
      (e.toMonoidHom.subgroupMap_surjective Yb)
  · rw [Nat.card_congr (Yb.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm]
    exact h9
  · let ψ : ↥(Yb.map e.toMonoidHom ⊔ Sb.map e.toMonoidHom) ≃* ↥(Yb ⊔ Sb) :=
      (MulEquiv.subgroupCongr hmapsup.symm).trans
        (Subgroup.equivMapOfInjective (Yb ⊔ Sb) e.toMonoidHom e.injective).symm
    exact ⟨φ.comp ψ.toMonoidHom, hφ.comp ψ.surjective⟩
  · intro N' hNp hN1 hZN hNtop
    set N : Subgroup Q := N'.map e.symm.toMonoidHom with hNdef
    have hNN : N.map e.toMonoidHom = N' := by
      ext x
      simp only [hNdef, Subgroup.mem_map]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
    have hNp' : IsPGroup 2 ↥N :=
      hNp.of_equiv (Subgroup.equivMapOfInjective N' e.symm.toMonoidHom e.symm.injective)
    have hN1' : N ≠ ⊥ := by
      intro hb
      apply hN1
      rw [← hNN, hb, Subgroup.map_bot]
    have hZN' : Yb ⊔ Sb ≤ Subgroup.normalizer (N : Set Q) := by
      intro g hg
      have h1 : e g ∈ Subgroup.normalizer ((N.map e.toMonoidHom : Subgroup Q') : Set Q') := by
        rw [hNN]
        apply hZN
        rw [← hmapsup]
        exact ⟨g, hg, rfl⟩
      exact (R3c11.mem_normalizer_map_equiv_iff e N g).1 h1
    have hNtop' : Subgroup.normalizer (N : Set Q) ≠ ⊤ := by
      intro ht
      apply hNtop
      rw [eq_top_iff]
      intro x _
      have h1 : e (e.symm x) ∈ Subgroup.normalizer ((N.map e.toMonoidHom : Subgroup Q') : Set Q') :=
        (R3c11.mem_normalizer_map_equiv_iff e N (e.symm x)).2 (by rw [ht]; exact Subgroup.mem_top _)
      rw [hNN] at h1
      simpa using h1
    intro x hx
    have h1 : e (e.symm x) ∈ Subgroup.normalizer ((N.map e.toMonoidHom : Subgroup Q') : Set Q') := by
      rw [hNN]
      simpa using hx
    have h2 := hmin N hNp' hN1' hZN' hNtop' ((R3c11.mem_normalizer_map_equiv_iff e N (e.symm x)).1 h1)
    have h3 := (R3c11.mem_normalizer_map_equiv_iff e Yb (e.symm x)).2 h2
    simpa using h3

theorem Config.of_equiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (h : Config Q) : Config Q' := by
  obtain ⟨hns, Sb, Yb, hd⟩ := h
  refine ⟨fun hsolv' => hns ?_, Sb.map e.toMonoidHom, Yb.map e.toMonoidHom, hd.of_equiv e⟩
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

section Ctx

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem config_of_ctx (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hmin : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hIeq : I = L ⊔ Sgp153 T V₁) (hYL : Yp ≤ L)
    (ρ : ↥I →* ↥L ⧸ Subgroup.center ↥L)
    (hρ : ∀ l : ↥L, ρ ⟨l, (le_of_mem_cComp c.c33.mem) l.2⟩ = QuotientGroup.mk l) :
    Config (↥L ⧸ Subgroup.center ↥L) := by
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hYI : Yp ≤ I := hYL.trans hLI
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans c.hyp.hyp.T_le
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hpc := SBd13.pCore_eq_center_of_center_eq hZ
  have hcen : IsPGroup 2 (Subgroup.center ↥L) := SBd11.isPGroup_center_of_center_eq hZ
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := c.facts.sylow.2.1
  have hker : IsPGroup 2 ρ.ker := ker_isPGroup hLI hN hIeq hS2 hSI hcen ρ hρ
  have hMIY : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
    exact this.2
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := fun s hs => hMIY ⟨hSM hs, hSI hs⟩
  have hsup : img ρ (Yp ⊔ Sgp153 T V₁) = img ρ Yp ⊔ img ρ (Sgp153 T V₁) := img_sup hYI hSI
  refine ⟨not_isSolvable_of_ctx c (QuotientGroup.quotientMulEquivOfEq hpc.symm).symm, img ρ (Sgp153 T V₁),
    img ρ Yp, ⟨isSylowTwoOf_img_S c hN hLI ρ hρ, img_le_normalizer_img hSN,
    (solvable_nine_img_Yp c hLI hYL ρ hker).1, (solvable_nine_img_Yp c hLI hYL ρ hker).2, ?_, ?_⟩⟩
  · rw [← hsup]
    exact s3s3_img c hLI hYL ρ hker
  · intro N hNp hN1 hZN hNtop
    rw [← hsup] at hZN
    exact hmin_prop c hmin hLI hYL ρ hρ hker N hNp hN1 hZN hNtop

end Ctx

end CFSG.Quasithin.ModH
