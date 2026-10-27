module

public import CFSG.Quasithin.Recognition.G112M13Defs
import CFSG.Quasithin.Background.SzG11G94Final
import CFSG.Quasithin.Background.SzG11B5b2
import CFSG.Quasithin.Background.SzG11B5c
public import CFSG.Quasithin.Background.G118Basic

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG

@[expose] def G_11_8M : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G11CanonicalSetupM B Γ v₁ W X X₀ L →
      ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        (∃ k : ℕ, Module.finrank (ZMod 2) V = k * Module.finrank (ZMod 2) I ∧ 2 < k) ∧
          fixedSpace X = Submodule.span (ZMod 2) {v₁}

@[expose] def G_11_9M : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G11CanonicalSetupM B Γ v₁ W X X₀ L →
      ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        (∀ x ∈ X, x ∉ centralizerIn X (normalClosure Γ L) →
          ∃ Ix : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) Ix ∧ Ix ≤ B.orthogonal I ∧
            Ix ≠ I ∧ conjSub x Ix = Ix ∧
            ∃ c : V, Ix ⊓ W = Submodule.span (ZMod 2) {c} ∧ InducesTransvection x Ix c) ∧
        (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ IsNatAltModule (normalClosure Γ L) I n) ∧
        (centralizerIn X (normalClosure Γ L)).relIndex X = 2

namespace ChG

@[expose] def G114CanonicalM : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G11CanonicalCxM B Γ v₁ W X X₀ → IsIrr Γ ⊤

@[expose] def G115CanonicalM : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G11CanonicalCxM B Γ v₁ W X X₀ →
      ∃ x ∈ X, x ≠ 1 ∧ ∀ f ∈ fittingOf Γ, x * f = f * x

@[expose] def G115ComponentCanonicalM : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G11CanonicalCxM B Γ v₁ W X X₀ → IsIrr Γ ⊤ →
      (∃ x ∈ X, x ≠ 1 ∧ ∀ f ∈ fittingOf Γ, x * f = f * x) →
      ∃ L : Subgroup (GLV V), IsComponentOf L Γ ∧
        (∃ x ∈ X, ∃ l ∈ L, x * l ≠ l * x) ∧ numConjugates Γ L ≤ 2

@[expose] def G116CanonicalM : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G11CanonicalSetupM B Γ v₁ W X X₀ L →
      ∃ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I

@[expose] def G11CanonicalCentralizerOnIM : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G11CanonicalSetupM B Γ v₁ W X X₀ L →
      ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        ∀ x ∈ centralizerIn X (normalClosure Γ L), ∀ i ∈ I, x i = i

@[expose] def G11CanonicalFixedRankM : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G11CanonicalSetupM B Γ v₁ W X X₀ L →
      ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        ∀ x ∈ X, x ∉ centralizerIn X (normalClosure Γ L) →
          3 ≤ Module.finrank (ZMod 2) ↥(fixedSpace (Subgroup.zpowers x) ⊓ I)

theorem g112_u33_handbackM {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V))
    (hU33 : G112ProposedU33 Γ) : G112FaithfulWithU33M B Γ X :=
  Or.inr hU33

theorem g112Canonical_of_lemmasM (h4 : G114CanonicalM) (h5 : G115CanonicalM)
    (h5b : G115ComponentCanonicalM) (h6 : G116CanonicalM)
    (h8 : G_11_8M) (h9 : G_11_9M)
    (hcentralizer : G11CanonicalCentralizerOnIM) (hfixedRank : G11CanonicalFixedRankM) :
    G_11_2M := by
  intro V _ _ _ B Γ v₁ W X X₀ hyp hq
  by_cases hU33 : G112ProposedU33 Γ
  · exact g112_u33_handbackM B Γ X hU33
  by_contra hnot
  have cx : G11CanonicalCxM B Γ v₁ W X X₀ := ⟨hyp, hq, hnot⟩
  have hirr := h4 V B Γ v₁ W X X₀ cx
  have hx := h5 V B Γ v₁ W X X₀ cx
  obtain ⟨L, hLc, hLn, hLnum⟩ := h5b V B Γ v₁ W X X₀ cx hirr hx
  have h108 : G108Hyp B Γ v₁ W X X₀ L :=
    { toG101Hyp := hyp.toG101Hyp
      irreducible := hirr
      component := hLc
      noncomm := hLn
      three := Or.inr hLnum
      four := hyp.four }
  have hs : G11CanonicalSetupM B Γ v₁ W X X₀ L := ⟨cx, h108, hLnum⟩
  obtain ⟨I, hI⟩ := h6 V B Γ v₁ W X X₀ L hs
  obtain ⟨-, hfix⟩ := h8 V B Γ v₁ W X X₀ L hs I hI
  obtain ⟨-, -, hidx⟩ := h9 V B Γ v₁ W X X₀ L hs I hI
  have hcI := hcentralizer V B Γ v₁ W X X₀ L hs I hI
  have h3 := hfixedRank V B Γ v₁ W X X₀ L hs I hI
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

end ChG

theorem g114Canonical_holdsM : CFSG.ASVolI.ChG.G114CanonicalM := by
  intro V _ _ _ B Γ v₁ W X X₀ cx
  have h4 := CFSG.Quasithin.g10_4 CFSG.Quasithin.G11.g10_3 CFSG.Quasithin.G11.SzG11S.b49
  have h5 : CFSG.Quasithin.G11.G1005Stmt := CFSG.Quasithin.g10_5 CFSG.Quasithin.G11.g10_3 h4
  rcases h5 V B Γ v₁ W X X₀ cx.hyp.toG101Hyp with h | ⟨hd, h18⟩
  · exact h
  · exact (cx.notConcl (Or.inl (Or.inr (Or.inl ⟨hd, Or.inr h18⟩)))).elim

theorem g115Canonical_holdsM : CFSG.ASVolI.ChG.G115CanonicalM := by
  intro V _ _ _ B Γ v₁ W X X₀ cx
  have hirr : IsIrr Γ ⊤ := g114Canonical_holdsM V B Γ v₁ W X X₀ cx
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
  have hconcl := (CFSG.Quasithin.SzG11.g94Stmt_proved V Γ X k hyp94).toG112
  rcases hconcl with h | h | h
  · exact cx.notConcl (Or.inl (Or.inl h))
  · exact cx.notConcl (Or.inl (Or.inr (Or.inl h)))
  · exact cx.notConcl (Or.inl (Or.inr (Or.inr (Or.inl h))))

theorem g11CanonicalCentralizerOnI_holdsM : CFSG.ASVolI.ChG.G11CanonicalCentralizerOnIM := by
  intro V _ _ _ B Γ v₁ W X X₀ L cs I hI x hx
  exact CFSG.Quasithin.G11.G118.fixes_of_mem_centralizerIn cs.h108 hI hx

section G115b


theorem g115ComponentCanonical_holdsM
    : CFSG.ASVolI.ChG.G115ComponentCanonicalM := by
  intro V _ _ _ B Γ v₁ W X X₀ cx hirr hx
  obtain ⟨L, hL, hn⟩ :=
    CFSG.Quasithin.G11.SzG11S.g115bPart1 V B Γ v₁ W X X₀ cx.hyp hirr hx
  exact ⟨L, hL, hn, CFSG.Quasithin.G11.SzG11S.numConjugates_le_two_of_asA21
    CFSG.Quasithin.asA21SQTKSection cx.sqtk hL⟩

end G115b

section G116


theorem g116Canonical_holdsM
    : CFSG.ASVolI.ChG.G116CanonicalM := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs
  have h3 := CFSG.Quasithin.G11.g10_3
  have h4 := CFSG.Quasithin.g10_4 h3 CFSG.Quasithin.G11.SzG11S.b49
  have h10 := CFSG.Quasithin.G11.g10_10_of_g10_4 h4
  have h11 := CFSG.Quasithin.G11.g10_11 h10
  have h12 := CFSG.Quasithin.G11.g10_12 h11
  have h13 := CFSG.Quasithin.G11.g10_13 h10 h11
  have h1212 := CFSG.Quasithin.G11.g12_12_of_four
    (CFSG.Quasithin.G11.g12_1_of_four CFSG.Quasithin.G11.g12_four_fact)
    CFSG.Quasithin.G11.g12_part_four_fact
  have h15 : CFSG.Quasithin.G11.G1015Stmt :=
    CFSG.Quasithin.G11.g10_15 h10 h11 h12 h13 h1212 CFSG.Quasithin.G11.outerGLInput
      CFSG.Quasithin.G11.inspect_simple CFSG.Quasithin.G11.inspect_outer
      CFSG.Quasithin.G11.inspect_sylow
      (CFSG.Quasithin.SzG11.sectionSQTInput_of_asA21 CFSG.Quasithin.asA21SQTKSection)
  have hII : CFSG.Quasithin.G11.G116IIStmt :=
    CFSG.Quasithin.G11.g116_II CFSG.Quasithin.G11.Harris.g93StmtDimensionOnly_holds
      CFSG.Quasithin.G11.outerSL34Input
  have hIII : CFSG.Quasithin.G11.G116IIIStmt := CFSG.Quasithin.G11.g116_III
  have h108 := hs.h108
  have hirrH : ∀ I : Submodule (ZMod 2) V,
      IrrPlus (normalClosure Γ L) I → IsIrr (normalClosure Γ L) I :=
    fun I hI => hI.isIrr h108.fixedSpace_H
  have hG : ∃ I : Submodule (ZMod 2) V, CFSG.Quasithin.G11.G116Props B Γ v₁ X L I := by
    obtain ⟨I, hI, hone, htwo, hthree⟩ :=
      (CFSG.Quasithin.G11.G1015Concl_iff B Γ v₁ W X L).1 (h15 V B Γ v₁ W X X₀ L h108 hs.cx.sqtk)
    rcases htwo with h2I | h2II | h2III
    · have hone_i : CFSG.Quasithin.G11.G1015One_i B Γ v₁ W X L I := by
        rcases hone with h | ⟨x, hx, hxI, -, hno, -⟩
        · exact h
        · exfalso
          have hconj : IrrPlus (normalClosure Γ L) (conjSub x I) :=
            ((hirrH I hI).conj_of_normal (normalClosure_normal Γ L) (h108.X_le hx)).irrPlus
              h108.fixedSpace_H
          exact hno (h2I.1 I (conjSub x I) hI hconj)
      have hnot : ¬ AutAll (normalClosure Γ L) I :=
        CFSG.Quasithin.G11.not_autAll_of_selfDual (h108.two_lt_finrank (hirrH I hI)) h2I.2.1
      refine ⟨I, hI, hone_i.2.2.1, hone_i.2.1, hone_i.2.2.2, hone_i.1, ?_, h2I.2.1, h2I.2.2.1,
        hnot⟩
      rcases h2I.2.2.2 with h | h
      · exact Or.inr h
      · exact Or.inl h
    · exfalso
      have hone_ii : CFSG.Quasithin.G11.G1015One_ii B Γ v₁ W X L I := by
        rcases hone with h | h
        · exact absurd h.1 h2II.1
        · exact h
      rcases hII V B Γ v₁ W X X₀ L h108 hs.numConj hs.cx.sqtk I hI hone_ii h2II hthree with
        h | h
      · exact hs.cx.notConcl <| Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inl h
      · exact hs.cx.notConcl <| Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inl h
    · exfalso
      have hone_ii : CFSG.Quasithin.G11.G1015One_ii B Γ v₁ W X L I := by
        rcases hone with h | h
        · exact absurd h.1 h2III.1
        · exact h
      have h12' := hIII V B Γ v₁ W X X₀ L h108 hs.cx.sqtk I hI hone_ii h2III hthree
      exact hs.cx.notConcl <| Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h12'
  exact hG

end G116

end CFSG.ASVolI
