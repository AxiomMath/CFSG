module

public import CFSG.Quasithin.Background.SzG11G64Old
public import CFSG.Quasithin.Background.G119Nat3
public import CFSG.Quasithin.Background.G119Group
public import CFSG.Quasithin.Background.G119Nat1
public import CFSG.Quasithin.Background.G11BridgeRestrictG6

public section

namespace CFSG.Quasithin

namespace G11

open CFSG.QuasithinUnique

section Bridge

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem lemma_G64_toMulSub_of_b5 [Finite V] (h56 : AsB56) {K : Subgroup (GLV V)} {a : GLV V}
    (h : Hypothesis61 K a)
    (htr : Module.finrank (ZMod 2) (LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id)) = 1) :
    (∃ Ks : Fin 1 → Subgroup (MulAut (Multiplicative V)),
        G6.G64Decomposition (toMulSub K) (linEquivMulAut a) Ks ∧
          toMulSub K = G6.classClosure (toMulSub K) (linEquivMulAut a)) ∨
    (∃ Ks : Fin 2 → Subgroup (MulAut (Multiplicative V)),
        G6.G64Decomposition (toMulSub K) (linEquivMulAut a) Ks ∧ G6.IsSmallG64Type (Ks 0) ∧
          G6.IsSmallG64Type (Ks 1) ∧ ∃ t ∈ toMulSub K, t * t = 1 ∧
            toMulSub K = G6.classClosure (toMulSub K) (linEquivMulAut a) ⊔ Subgroup.zpowers t ∧
              conjSubgroup (Ks 0) t = Ks 1) :=
  SzG11.lemma_G64_of_b5 h56 h.toMulSub ((card_commV_zpowers_toMulSub_eq_two_iff a).2 htr)

variable {K : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem lemma_G64_restrict_of_b5 [Finite V] (h56 : AsB56) (hI : IsIrr K I)
    (hq : IsQuotientOfSQTKTauCeti ↥K) {a : GLV V} (ha : a ∈ K) (ha2 : a * a = 1)
    (htr : ∃ c : V, InducesTransvection a I c) :
    (∃ Ks : Fin 1 → Subgroup (MulAut (Multiplicative ↥I)),
        G6.G64Decomposition (toMulSub (restrictRange K I hI.1))
          (linEquivMulAut (restrictEquiv a I (hI.1.conjSub_eq ha))) Ks ∧
          toMulSub (restrictRange K I hI.1) = G6.classClosure (toMulSub (restrictRange K I hI.1))
            (linEquivMulAut (restrictEquiv a I (hI.1.conjSub_eq ha)))) ∨
    (∃ Ks : Fin 2 → Subgroup (MulAut (Multiplicative ↥I)),
        G6.G64Decomposition (toMulSub (restrictRange K I hI.1))
          (linEquivMulAut (restrictEquiv a I (hI.1.conjSub_eq ha))) Ks ∧ G6.IsSmallG64Type (Ks 0) ∧
          G6.IsSmallG64Type (Ks 1) ∧ ∃ t ∈ toMulSub (restrictRange K I hI.1), t * t = 1 ∧
            toMulSub (restrictRange K I hI.1) =
              G6.classClosure (toMulSub (restrictRange K I hI.1))
                (linEquivMulAut (restrictEquiv a I (hI.1.conjSub_eq ha))) ⊔ Subgroup.zpowers t ∧
              conjSubgroup (Ks 0) t = Ks 1) :=
  lemma_G64_toMulSub_of_b5 h56 (hypothesis61_restrict hI hq ha ha2 htr)
    ((inducesTransvection_iff_finrank (hI.1.conjSub_eq ha)).1 htr)

end Bridge

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

namespace G119Ctx

variable (c : G119Ctx B Γ v₁ W X X₀ L I)

include c

theorem natural_package_of_b5 (h56 : AsB56) {x₀ : GLV V} (hx₀ : x₀ ∈ X)
    (hrk : Module.finrank (ZMod 2) (LinearMap.range (commMap x₀ I (c.conjSub_I hx₀))) = 1) :
    ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧
      G119NatSymAction (restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1) n ∧
      ∀ g ∈ restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1,
        g ∈ restrictRange (normalClosure Γ L) I c.irrPlus.1 ∨
          g * restrictEquiv x₀ I (c.conjSub_I hx₀) ∈
            restrictRange (normalClosure Γ L) I c.irrPlus.1 := by
  classical
  set G' := restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1 with hG'
  set ā := restrictEquiv x₀ I (c.conjSub_I hx₀) with hā
  set Hb := restrictRange (normalClosure Γ L) I c.irrPlus.1 with hHb
  have htr : ∃ c' : V, InducesTransvection x₀ I c' :=
    (inducesTransvection_iff_finrank (c.conjSub_I hx₀)).2 hrk
  have hāG : ā ∈ G' := c.restrictEquiv_mem_G hx₀
  rcases lemma_G64_restrict_of_b5 h56 c.irr_sup c.sqtk_sup (Subgroup.mem_sup_right hx₀)
      (c.X_sq hx₀) htr with ⟨Ks, hd, hcl⟩ | ⟨Ks, hd, -, -, t, -, -, hteq, -⟩
  ·
    have hcl' : G' = normalClosure G' (Subgroup.zpowers ā) := (classClosure_eq_iff G' ā).1 hcl
    have hdec : ∀ g ∈ G', g ∈ Hb ∨ g * ā ∈ Hb := fun g hg => c.mem_or_mul_mem hx₀ hcl' hg
    have hKs0 : Ks 0 = toMulSub G' := by
      have h := hd.decomp.iSup_eq
      rw [iSup_unique] at h
      exact h.trans hcl.symm
    have hcomm0 : commV (Ks 0) = ⊤ := by
      have h := hd.decomp.iSup_commV
      rw [iSup_unique] at h
      exact h
    rcases hd.decomp.type 0 with ⟨n, hn2, hn5, hL⟩ | ⟨n, hn5, hn8, hS⟩ | ⟨n, hn, hC⟩
    ·
      exfalso
      rw [hcomm0, hKs0] at hL
      obtain ⟨hfin, ⟨e⟩⟩ := g119_finrank_eq_of_isLnNatural G' hL
      have hn3 : 3 ≤ n := by
        have := c.two_lt
        omega
      have hN : (Hb.subgroupOf G').Normal :=
        ⟨fun n hn g => by
          have h1 := (Subgroup.mem_set_normalizer_iff.1 (c.restrictRange_le_normalizer_H g.2)
            (n : GLV ↥I)).1 hn
          exact h1⟩
      have hNa : Hb.subgroupOf G' ⊔ Subgroup.zpowers (⟨ā, hāG⟩ : ↥G') = ⊤ := by
        rw [eq_top_iff]
        intro g _
        rcases hdec g.1 g.2 with hg | hg
        · exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hg)
        · have h1 : g * ⟨ā, hāG⟩ ∈ Hb.subgroupOf G' := Subgroup.mem_subgroupOf.2 hg
          have h2 : g = g * ⟨ā, hāG⟩ * (⟨ā, hāG⟩ : ↥G')⁻¹ := by group
          rw [h2]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
            (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
      have hNtop := g119_eq_top_of_mulEquiv_glFin hn3 e (Hb.subgroupOf G') ⟨ā, hāG⟩ hNa
      have hGtop : G' = ⊤ := g119_eq_top_of_card_glFin hfin G' e
      apply c.not_autAll
      intro g
      have hgG : g ∈ G' := by rw [hGtop]; exact Subgroup.mem_top g
      have hgHb : g ∈ Hb := by
        have : (⟨g, hgG⟩ : ↥G') ∈ Hb.subgroupOf G' := by rw [hNtop]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.1 this
      obtain ⟨k, hk⟩ := hgHb
      refine ⟨(k : GLV V), k.2, fun i => ?_⟩
      have := congrArg (fun e : ↥I ≃ₗ[ZMod 2] ↥I => ((e i : ↥I) : V)) hk
      simpa using this
    ·
      refine ⟨n, hn5, hn8, ?_, hdec⟩
      rw [hcomm0, hKs0] at hS
      exact g119_natural_of_isSymNatural G' hn5 hS
    ·
      exfalso
      rw [hcomm0, hKs0] at hC
      obtain ⟨m, hm0, hmfix⟩ := g119_exists_fixed_of_isSymCore G' hn hC
      have hmem : ((m : ↥I) : V) ∈ fixedSpace (normalClosure Γ L) := by
        intro k hk
        have h1 := hmfix (restrictEquiv k I (c.irrPlus.1.conjSub_eq hk))
          (c.restrictRange_H_le ⟨⟨k, hk⟩, rfl⟩)
        exact congrArg Subtype.val h1
      rw [c.fixedSpace_H, Submodule.mem_bot] at hmem
      exact hm0 (Subtype.ext hmem)
  ·
    exfalso
    exact c.false_of_two_factors hx₀ Ks hd hteq

end G119Ctx

end G11

end CFSG.Quasithin
