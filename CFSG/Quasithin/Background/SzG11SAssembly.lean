module

public import CFSG.Quasithin.Background.SzG11SStmts
public import CFSG.Quasithin.Background.G9Stmts
public import CFSG.Quasithin.Background.G11Six
public import CFSG.Quasithin.Background.SzG11G64Nat
public import CFSG.Quasithin.Background.G10FifteenSD
public import CFSG.Quasithin.Background.G119Fix
public import CFSG.Quasithin.Background.G119Index
public import CFSG.Quasithin.Background.G119Transv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace SzG11S

theorem g11_4 (h5 : G1005Stmt) : G114Stmt := by
  intro V _ _ _ B Γ v₁ W X X₀ cx
  rcases h5 V B Γ v₁ W X X₀ cx.hyp.toG101Hyp with h | ⟨hd, h18⟩
  · exact h
  · exact absurd (Or.inl (Or.inr (Or.inl ⟨hd, Or.inr h18⟩))) cx.notConcl

theorem theoremG112S_of_lemmas (h4 : G114Stmt) (h5 : G115Stmt) (h5b : G115bStmt)
    (h6 : G116Stmt) (h8 : G118Stmt) (h9 : G119Stmt) : TheoremG112FixS := by
  intro V _ _ _ B Γ v₁ W X X₀ hyp hq
  by_contra hnot
  have cx : G11Cx B Γ v₁ W X X₀ := ⟨hyp, hq, hnot⟩
  have hirr := h4 V B Γ v₁ W X X₀ cx
  have hx := h5 V B Γ v₁ W X X₀ cx hirr
  obtain ⟨L, hLc, hLn, hLnum⟩ := h5b V B Γ v₁ W X X₀ cx hirr hx
  have h108 : G108Hyp B Γ v₁ W X X₀ L :=
    { toG101Hyp := hyp.toG101Hyp
      irreducible := hirr
      component := hLc
      noncomm := hLn
      three := Or.inr hLnum
      four := hyp.four }
  have hs : G11Setup B Γ v₁ W X X₀ L := ⟨cx, h108, hLnum⟩
  obtain ⟨I, hI⟩ := h6 V B Γ v₁ W X X₀ L hs
  obtain ⟨-, hfix, hcI⟩ := h8 V B Γ v₁ W X X₀ L hs I hI
  obtain ⟨-, -, hidx, h3⟩ := h9 V B Γ v₁ W X X₀ L hs I hI
  set C := centralizerIn X (normalClosure Γ L) with hC
  obtain ⟨x, hxX, hxC⟩ : ∃ x ∈ X, x ∉ C := by
    by_contra hall
    have hle : X ≤ C := fun x hx => by_contra fun h => hall ⟨x, hx, h⟩
    have : C.relIndex X = 1 := Subgroup.relIndex_eq_one.2 hle
    rw [hidx] at this
    exact absurd this (by norm_num)
  have hge := h3 x hxX hxC
  have hindex : (C.subgroupOf X).index = 2 := hidx
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hindex
  have hle : fixedSpace (Subgroup.zpowers x) ⊓ I ≤ fixedSpace X := by
    intro i hi y hy
    have hxi : x i = i := hi.1 x (Subgroup.mem_zpowers x)
    by_cases hyC : y ∈ C
    · exact hcI y hyC i hi.2
    ·
      have hxa : (⟨x, hxX⟩ : ↥X) * a ∈ C.subgroupOf X := by
        rcases ha ⟨x, hxX⟩ with ⟨h1, _⟩ | ⟨h2, _⟩
        · exact h1
        · exact absurd (Subgroup.mem_subgroupOf.1 h2) hxC
      have hya : (⟨y, hy⟩ : ↥X) * a ∈ C.subgroupOf X := by
        rcases ha ⟨y, hy⟩ with ⟨h1, _⟩ | ⟨h2, _⟩
        · exact h1
        · exact absurd (Subgroup.mem_subgroupOf.1 h2) hyC
      have hyx : y * x⁻¹ ∈ C := by
        have := (C.subgroupOf X).mul_mem hya ((C.subgroupOf X).inv_mem hxa)
        have h' := Subgroup.mem_subgroupOf.1 this
        simpa [mul_assoc] using h'
      have h1 : (y * x⁻¹) i = i := hcI (y * x⁻¹) hyx i hi.2
      have h2 : y i = (y * x⁻¹) (x i) := by
        show y i = y (x⁻¹ (x i))
        have : x⁻¹ (x i) = i := x.symm_apply_apply i
        rw [this]
      rw [h2, hxi]
      exact h1
  have hle2 : fixedSpace (Subgroup.zpowers x) ⊓ I ≤ Submodule.span (ZMod 2) {v₁} := by
    rw [← hfix]
    exact hle
  have hrank := Submodule.finrank_mono hle2
  have h1 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {v₁}) = 1 :=
    finrank_span_singleton hyp.point
  omega

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace SzG11S

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem g11_5 (h94 : G94Stmt) : G115Stmt := by
  intro V _ _ _ B Γ v₁ W X X₀ cx hirr
  by_contra hcon
  have hfaith : ∀ x ∈ X, (∀ f ∈ fittingOf Γ, x * f = f * x) → x = 1 := by
    intro x hx hc
    by_contra hx1
    exact hcon ⟨x, hx, hx1, hc⟩
  have h101 := cx.hyp.toG101Hyp
  obtain ⟨k, hk⟩ := h101.exists_card_X
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0', pow_zero] at hk
    have hX1 : ∀ x ∈ X, x = 1 := by
      intro x hx
      have hsub : Subsingleton ↥X := Nat.card_eq_one_iff_unique.1 hk |>.1
      exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥X) 1)
    rcases cx.hyp.three with h | ⟨a, ha, -, hv⟩
    ·
      obtain ⟨w, hw⟩ : ∃ w, B v₁ w ≠ 0 := by
        by_contra hall
        push Not at hall
        exact h101.point (h101.nondegenerate v₁ hall)
      rcases h w (fun x hx => by rw [hX1 x hx]; rfl) with hw0 | hw1
      · exact hw (by rw [hw0, map_zero])
      · exact hw (by rw [hw1]; exact h101.alt v₁)
    · have : a = 1 := hX1 a ha
      subst this
      have : v₁ = 0 := by
        obtain ⟨u, hu⟩ := hv
        rw [← hu]
        simp
      exact h101.point this
  have hbound : Module.finrank (ZMod 2) V ≤ 2 * (k + 1) := by
    refine h101.dim_le_two_mul.trans (Nat.mul_le_mul_left 2 (Nat.succ_le_succ ?_))
    have hdvd : X₀.relIndex X ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.relIndex_dvd_card X₀ X
    calc Nat.log 2 (X₀.relIndex X) ≤ Nat.log 2 (2 ^ k) :=
          Nat.log_mono_right (Nat.le_of_dvd (by positivity) hdvd)
      _ = k := Nat.log_pow Nat.one_lt_two k
  have hyp94 : G94Hyp Γ X k :=
    { quotient := cx.sqtk
      A_le := h101.X_le
      A_elem := h101.X_isElemAbelian
      A_card := hk
      A_ne := hk1
      bound := hbound
      irreducible := hirr
      faithful := hfaith }
  have hconcl := (h94 V Γ X k hyp94).toG112
  rcases hconcl with h | h | h
  · exact cx.notConcl (Or.inl (Or.inl h))
  · exact cx.notConcl (Or.inl (Or.inr (Or.inl h)))
  · exact cx.notConcl (Or.inl (Or.inr (Or.inr (Or.inl h))))

theorem theoremG112S_of_inputs (h5 : G1005Stmt) (h94 : G94Stmt) (h5b : G115bStmt)
    (h6 : G116Stmt) (h8 : G118Stmt) (h9 : G119Stmt) : TheoremG112FixS :=
  theoremG112S_of_lemmas (g11_4 h5) (g11_5 h94) h5b h6 h8 h9

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace SzG11S

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem g11_6 (h15 : G1015Stmt) (hII : G116IIStmt) (hIII : G116IIIStmt) : G116Stmt := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs
  have h108 := hs.h108
  have hirrH : ∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I →
      IsIrr (normalClosure Γ L) I := fun I hI => hI.isIrr h108.fixedSpace_H
  obtain ⟨I, hI, hone, htwo, hthree⟩ := (G1015Concl_iff B Γ v₁ W X L).1
    (h15 V B Γ v₁ W X X₀ L h108 hs.cx.sqtk)
  rcases htwo with h2I | h2II | h2III
  ·
    have hone_i : G1015One_i B Γ v₁ W X L I := by
      rcases hone with h | ⟨x, hx, hxI, -, hno, -⟩
      · exact h
      · exfalso
        have hconj : IrrPlus (normalClosure Γ L) (conjSub x I) :=
          ((hirrH I hI).conj_of_normal (normalClosure_normal Γ L) (h108.X_le hx)).irrPlus
            h108.fixedSpace_H
        exact hno (h2I.1 I (conjSub x I) hI hconj)
    have hnot : ¬ AutAll (normalClosure Γ L) I :=
      not_autAll_of_selfDual (h108.two_lt_finrank (hirrH I hI)) h2I.2.1
    refine ⟨I, hI, hone_i.2.2.1, hone_i.2.1, hone_i.2.2.2, hone_i.1, ?_, h2I.2.1, h2I.2.2.1, hnot⟩
    rcases h2I.2.2.2 with h | h
    · exact Or.inr h
    · exact Or.inl h
  ·
    have hone_ii : G1015One_ii B Γ v₁ W X L I := by
      rcases hone with h | h
      · exact absurd h.1 h2II.1
      · exact h
    exfalso
    rcases hII V B Γ v₁ W X X₀ L h108 hs.numConj hs.cx.sqtk I hI hone_ii h2II hthree with h | h
    · apply hs.cx.notConcl
      simp only [G112ConclusionFixS]
      tauto
    · exact hs.cx.notConcl (Or.inr (Or.inl h))
  ·
    have hone_ii : G1015One_ii B Γ v₁ W X L I := by
      rcases hone with h | h
      · exact absurd h.1 h2III.1
      · exact h
    exfalso
    have h12 := hIII V B Γ v₁ W X X₀ L h108 hs.cx.sqtk I hI hone_ii h2III hthree
    apply hs.cx.notConcl
    simp only [G112ConclusionFixS]
    tauto

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace SzG11S

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

variable (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
  (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V)

variable {B Γ v₁ W X X₀ L I}

theorem G119Ctx.of_props (hs : G11Setup B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (hrank : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) V)
    (hfix : fixedSpace X = Submodule.span (ZMod 2) {v₁})
    (hcent : ∀ x ∈ centralizerIn X (normalClosure Γ L), ∀ i ∈ I, x i = i) :
    G119Ctx B Γ v₁ W X X₀ L I := by
  obtain ⟨hirrP, hv₁, hinvX, -, hhom, hiso, -, hfaith, hnot⟩ := hI
  refine ⟨hs.h108, hs.cx.sqtk, hirrP, hv₁, hinvX, hhom, ?_, hfaith, hnot, hrank, hfix, hcent⟩
  rcases hiso with h | h
  · exfalso
    have h1 : Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) V := by
      rw [h]
      exact finrank_top (ZMod 2) V
    omega
  · exact h

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

namespace G11

namespace SzG11S

theorem g11_9_of_b5 (h8 : G118Stmt) (hE11 : E11Stmt) (h14 : G1014Stmt) (h56 : AsB56) :
    G119Stmt := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs I hI
  obtain ⟨hrank, hfix, hcent⟩ := h8 V B Γ v₁ W X X₀ L hs I hI
  have c : G119Ctx B Γ v₁ W X X₀ L I := G119Ctx.of_props hs hI hrank hfix hcent
  have h14c : G1014Concl B Γ v₁ W X L := h14 V B Γ v₁ W X X₀ L hs.h108
  have hE : G119E11Use := g119_e11Use_of_e11Stmt hE11
  have hrk : ∀ (y : GLV V) (hy : y ∈ X), y ∉ centralizerIn X (normalClosure Γ L) →
      Module.finrank (ZMod 2) (LinearMap.range (commMap y I (c.conjSub_I hy))) = 1 := by
    intro y hy hyC
    obtain ⟨J, hJ, hle, hne, hfixJ⟩ := c.exists_fixed hE hy
    exact c.finrank_commMap_I h14c hy hyC hJ hle hne hfixJ
  obtain ⟨x₀, hx₀, hx₀C⟩ := c.exists_not_central
  obtain ⟨n, hn5, hn8, hnat, hdec⟩ := c.natural_package_of_b5 h56 hx₀ (hrk x₀ hx₀ hx₀C)
  have h4 : 4 ≤ Module.finrank (ZMod 2) I := by
    obtain ⟨θ, β, hrange, hker, -, -⟩ := hnat
    have := g119_four_le_finrank_range_of_ker hn5 β hker
    rwa [hrange, finrank_top] at this
  refine ⟨?_, ⟨n, hn5, hn8, c.isNatAltModule_of_natSym hx₀ (hrk x₀ hx₀ hx₀C) hnat hdec⟩,
    c.relIndex_eq_two hx₀ hx₀C hrk hnat, ?_⟩
  · intro x hx hxC
    obtain ⟨J, hJ, hle, hne, hfixJ⟩ := c.exists_fixed hE hx
    obtain ⟨c', hc1, hc2⟩ := c.transvection_Ix h14c hx hxC hJ hle hne hfixJ
    exact ⟨J, hJ, hle, hne, hfixJ, c', hc1, hc2⟩
  · intro x hx hxC
    exact c.three_le_finrank_fixed hx (hrk x hx hxC) h4

end SzG11S

end G11

end CFSG.Quasithin

