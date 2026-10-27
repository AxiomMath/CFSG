module

public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Background.F9Section
public import CFSG.Quasithin.Background.F9Comp
public import CFSG.Quasithin.Background.F8G2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise commutatorElement

universe u

variable {G : Type u} [Group G]

structure HypF918 (T V L V₁ Vp H K : Subgroup G) : Prop extends HypF98 T V L V₁ Vp H where
  K_cComp : K ∈ cComp H
  K_quasisimple : CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K)
  H_eq : H = conjClosure K T ⊔ ((L ⊔ T) ⊓ H)
  K₀_normal : H ≤ Subgroup.normalizer (conjClosure K T : Set G)

@[expose] def IsIrrPlusTilde (V₁ K₀ I : Subgroup G) : Prop :=
  K₀ ≤ Subgroup.normalizer (I : Set G) ∧ tildeOf V₁ ⁅I, K₀⁆ = tildeOf V₁ I ∧
    centralizerMod V₁ I K₀ < I ∧
    ∀ J : Subgroup G, V₁ ≤ J → J ≤ I → K₀ ≤ Subgroup.normalizer (J : Set G) →
      centralizerMod V₁ I K₀ ≤ J → J = centralizerMod V₁ I K₀ ∨ J = I

@[expose] def IsF918B (T L V₁ Vp H K₀ B : Subgroup G) : Prop :=
  B ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) ∧ QCrit V₁ Vp H B ∧
    ∀ b ∈ B, (∀ k ∈ K₀, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → b ∈ pCoreOf 2 H

@[expose] def HasNoFFModulesMod (X C : Subgroup G) : Prop :=
  ∀ (W : Type u) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ ρ : ↥X →* MulAut W,
    (∀ x : ↥X, (x : G) ∈ C → ρ x = 1) → ¬ IsFFModule ρ.range

namespace F9

@[expose] def IsStrongFFInt (G₁ V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  @IsStrongFFModule ↥V (commGroupOfElemAbelian hV) (autOn G₁ V)

end F9

theorem commutator_acts_trivially {F E : Subgroup G} {x y : G}
    (hxF : x ∈ Subgroup.normalizer (F : Set G)) (hxE : x ∈ Subgroup.normalizer (E : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) (hyE : y ∈ Subgroup.normalizer (E : Set G))
    (hx : ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ F) :
    ∀ e ∈ E, (x * y * x⁻¹ * y⁻¹) * e * (x * y * x⁻¹ * y⁻¹)⁻¹ * e⁻¹ ∈ F := by
  let X : Subgroup G := Subgroup.normalizer (F : Set G) ⊓ Subgroup.normalizer (E : Set G)
  let Tr : Subgroup G := centralizerMod F X E
  have hXn : X ≤ Subgroup.normalizer (Tr : Set G) :=
    le_normalizer_centralizerMod inf_le_left Subgroup.le_normalizer inf_le_right
  have hxTr : x ∈ Tr := ⟨⟨hxF, hxE⟩, hxF, hx⟩
  have hyX : y ∈ X := ⟨hyF, hyE⟩
  have h1 : y * x⁻¹ * y⁻¹ ∈ Tr := (Subgroup.mem_normalizer_iff.mp (hXn hyX) x⁻¹).mp (Tr.inv_mem hxTr)
  have h2 : x * (y * x⁻¹ * y⁻¹) ∈ Tr := Tr.mul_mem hxTr h1
  have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
  rw [e]
  exact h2.2.2

section Fin

variable [Finite G]

namespace HypF918

variable {T V L V₁ Vp H K : Subgroup G}

omit [Finite G] in
theorem K₀_le_H (h : HypF918 T V L V₁ Vp H K) : conjClosure K T ≤ H :=
  conjClosure_le fun _ ht _ hz =>
    H.mul_mem (H.mul_mem (h.T_le_H ht) (le_of_mem_cComp h.K_cComp hz)) (H.inv_mem (h.T_le_H ht))

omit [Finite G] in
theorem K₀T_le_H (h : HypF918 T V L V₁ Vp H K) : conjClosure K T ⊔ T ≤ H :=
  sup_le h.K₀_le_H h.T_le_H

omit [Finite G] in
theorem K₀_perfect (h : HypF918 T V L V₁ Vp H K) :
    ⁅conjClosure K T, conjClosure K T⁆ = conjClosure K T :=
  A3.conjClosure_perfect (perfect_of_mem_cComp h.K_cComp)

omit [Finite G] in
theorem K₀T_le_normalizer_K₀ (T K : Subgroup G) :
    conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
  sup_le Subgroup.le_normalizer (le_normalizer_conjClosure K T)

omit [Finite G] in
theorem K₀T_le_normalizer_V₁ (h : HypF918 T V L V₁ Vp H K) :
    conjClosure K T ⊔ T ≤ Subgroup.normalizer (V₁ : Set G) :=
  h.K₀T_le_H.trans h.H_normalizes_V₁

omit [Finite G] in
theorem K₀T_le_normalizer_U (h : HypF918 T V L V₁ Vp H K) :
    conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure Vp H : Set G) :=
  h.K₀T_le_H.trans (le_normalizer_conjClosure Vp H)

theorem H_eq' (h : HypF918 T V L V₁ Vp H K) :
    H = conjClosure K T ⊔ (L₁Of L V₁ ⊔ T) := by
  rw [← h.toHypF98.toHypF91.LT_inf_H]
  exact h.H_eq

theorem faithful_of_le_pCoreOf (h : HypF918 T V L V₁ Vp H K) {B : Subgroup G}
    (hB : B ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T)) :
    ∀ b ∈ B, (∀ k ∈ conjClosure K T, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → b ∈ pCoreOf 2 H := by
  have h1 := h.toHypF98.toHypF91
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hXH : L₁Of L V₁ ⊔ T ≤ H := h1.L₁T_le_H
  have hPH : pCoreOf 2 (L₁Of L V₁ ⊔ T) ≤ H := (pCoreOf_le 2 _).trans hXH
  have hPT : pCoreOf 2 (L₁Of L V₁ ⊔ T) ≤ T :=
    isSylowTwoOf_pCoreOf_le (isSylowTwoOf_mono_right h1.sylow le_sup_right le_top)
  have hQT : pCoreOf 2 H ≤ T := isSylowTwoOf_pCoreOf_le h1.sylow_H
  let D : Subgroup G :=
    pCoreOf 2 (L₁Of L V₁ ⊔ T) ⊓ centralizerMod (pCoreOf 2 H) H (conjClosure K T)
  let M : Subgroup G := D ⊔ pCoreOf 2 H
  have hMT : M ≤ T := sup_le (inf_le_left.trans hPT) hQT
  have hMH : M ≤ H := hMT.trans h1.T_le_H
  have hK₀M : conjClosure K T ≤ Subgroup.normalizer (M : Set G) := by
    have key : ∀ k ∈ conjClosure K T, ∀ y ∈ M, k * y * k⁻¹ ∈ M := by
      intro k hk
      have hsup : M ≤ M.comap (MulAut.conj k).toMonoidHom := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · have hc := hx.2.2.2 k hk
          have e : k * x * k⁻¹ = (x * k * x⁻¹ * k⁻¹)⁻¹ * x := by group
          show k * x * k⁻¹ ∈ M
          rw [e]
          exact M.mul_mem (Subgroup.mem_sup_right (Subgroup.inv_mem _ hc))
            (Subgroup.mem_sup_left hx)
        · show k * x * k⁻¹ ∈ M
          exact Subgroup.mem_sup_right
            ((Subgroup.mem_normalizer_iff.mp (hQn (h.K₀_le_H hk)) x).mp hx)
      exact fun y hy => hsup hy
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => key k hk y hy, fun hy => by
      simpa [mul_assoc] using key k⁻¹ (inv_mem hk) _ hy⟩
  have hL₁TM : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (M : Set G) := by
    have hX_Q : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := hXH.trans hQn
    have hX_P : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer
        (pCoreOf 2 (L₁Of L V₁ ⊔ T) : Set G) := le_normalizer_pCoreOf 2 _
    have hX_C : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer
        (centralizerMod (pCoreOf 2 H) H (conjClosure K T) : Set G) :=
      le_normalizer_centralizerMod hX_Q (hXH.trans Subgroup.le_normalizer)
        (hXH.trans h.K₀_normal)
    exact (le_inf (le_normalizer_inf hX_P hX_C) hX_Q).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hnorm : H ≤ Subgroup.normalizer (M : Set G) :=
    h.H_eq'.le.trans (sup_le hK₀M hL₁TM)
  have hMQ : M ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer 2 hMH hnorm (h1.sylow_H.2.1.to_le hMT)
  intro b hb hbk
  have hbD : b ∈ D := ⟨hB hb, hPH (hB hb), hQn (hPH (hB hb)), hbk⟩
  exact hMQ (Subgroup.mem_sup_left hbD)

theorem central_kernel_and_faithful (h : HypF918 T V L V₁ Vp H K) {B F E : Subgroup G}
    (hBT : B ≤ T)
    (hfaith : ∀ b ∈ B, (∀ k ∈ conjClosure K T, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 H) →
      b ∈ pCoreOf 2 H)
    (hF : conjClosure K T ⊔ T ≤ Subgroup.normalizer (F : Set G))
    (hE : conjClosure K T ⊔ T ≤ Subgroup.normalizer (E : Set G))
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ e ∈ E, k * e * k⁻¹ * e⁻¹ ∈ F) :
    (∀ k ∈ conjClosure K T, (∀ e ∈ E, k * e * k⁻¹ * e⁻¹ ∈ F) →
        ∀ k' ∈ conjClosure K T, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) ∧
      ∀ b ∈ B, (∀ e ∈ E, b * e * b⁻¹ * e⁻¹ ∈ F) → b ∈ pCoreOf 2 H := by
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  let N : Subgroup G := centralizerMod F (conjClosure K T) E
  have hNn : conjClosure K T ⊔ T ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_centralizerMod hF (K₀T_le_normalizer_K₀ T K) hE
  have hKC : conjClosure K T ≤ N ∨ ⁅N, conjClosure K T⁆ ≤ pCoreOf 2 H :=
    exists_le_or_commutator_le_pCoreOf h.K_cComp h.T_le_H h.K_quasisimple
      (centralizerMod_le_left _ _ _) (le_sup_left.trans hNn) (le_sup_right.trans hNn)
  have hcomm : ⁅N, conjClosure K T⁆ ≤ pCoreOf 2 H := by
    rcases hKC with hle | hcomm
    · exact absurd (fun k hk e he => (hle hk).2.2 e he) hnt
    · exact hcomm
  refine ⟨fun k hk hkE k' hk' => ?_, fun b hb hbE => ?_⟩
  · have hkN : k ∈ N := ⟨hk, hF (Subgroup.mem_sup_left hk), hkE⟩
    exact hcomm (Subgroup.commutator_mem_commutator hkN hk')
  · let A : Subgroup G := centralizerMod F B E
    have hAB : A ≤ B := centralizerMod_le_left _ _ _
    have hAk : ∀ a ∈ A, ∀ k ∈ conjClosure K T, ∀ k' ∈ conjClosure K T,
        (a * k * a⁻¹ * k⁻¹) * k' * (a * k * a⁻¹ * k⁻¹)⁻¹ * k'⁻¹ ∈ pCoreOf 2 H := by
      intro a ha k hk k' hk'
      have haT : a ∈ T := hBT (hAB ha)
      have haF : a ∈ Subgroup.normalizer (F : Set G) := hF (Subgroup.mem_sup_right haT)
      have haE : a ∈ Subgroup.normalizer (E : Set G) := hE (Subgroup.mem_sup_right haT)
      have hkF : k ∈ Subgroup.normalizer (F : Set G) := hF (Subgroup.mem_sup_left hk)
      have hkE : k ∈ Subgroup.normalizer (E : Set G) := hE (Subgroup.mem_sup_left hk)
      have hc : a * k * a⁻¹ * k⁻¹ ∈ N := by
        refine ⟨?_, ?_, commutator_acts_trivially haF haE hkF hkE ha.2.2⟩
        · exact (conjClosure K T).mul_mem
            ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure K T haT) k).mp hk)
            ((conjClosure K T).inv_mem hk)
        · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ haF hkF)
            (Subgroup.inv_mem _ haF)) (Subgroup.inv_mem _ hkF)
      exact hcomm (Subgroup.commutator_mem_commutator hc hk')
    have hsub : ⁅A, conjClosure K T⁆ ≤ centralizerMod (pCoreOf 2 H) H (conjClosure K T) := by
      refine Subgroup.commutator_le.mpr fun a ha k hk => ?_
      have haT : a ∈ T := hBT (hAB ha)
      have hmem : a * k * a⁻¹ * k⁻¹ ∈ conjClosure K T :=
        (conjClosure K T).mul_mem
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure K T haT) k).mp hk)
          ((conjClosure K T).inv_mem hk)
      exact ⟨h.K₀_le_H hmem, hQn (h.K₀_le_H hmem), fun k' hk' => hAk a ha k hk k' hk'⟩
    have hcomm2 : ⁅⁅conjClosure K T, A⁆, conjClosure K T⁆ ≤ pCoreOf 2 H := by
      rw [Subgroup.commutator_comm (conjClosure K T) A]
      exact Subgroup.commutator_le.mpr fun x hx k' hk' => (hsub hx).2.2 k' hk'
    have hAQ : ⁅A, conjClosure K T⁆ ≤ pCoreOf 2 H :=
      commutator_le_of_commutator_commutator_le (hAB.trans (hBT.trans (h.T_le_H.trans hQn)))
        (h.K₀_le_H.trans hQn) h.K₀_perfect hcomm2
    have hbA : b ∈ A := ⟨hb, hF (Subgroup.mem_sup_right (hBT hb)), hbE⟩
    exact hfaith b hb fun k hk => hAQ (Subgroup.commutator_mem_commutator hbA hk)

end HypF918

theorem oTwoUpper_eq_of_perfect_F9 {X : Subgroup G} (hX : ⁅X, X⁆ = X) : oTwoUpper X = X := by
  have hperf : Group.IsPerfect X := Subgroup.isPerfect_iff.mpr hX
  have hN : ((oTwoUpper X).subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoUpper X)
  have hp : IsPGroup 2 (↥X ⧸ (oTwoUpper X).subgroupOf X) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
  have : Group.IsNilpotent (↥X ⧸ (oTwoUpper X).subgroupOf X) := hp.isNilpotent
  have hsub : Subsingleton (↥X ⧸ (oTwoUpper X).subgroupOf X) := by
    by_contra hns
    have : Nontrivial (↥X ⧸ (oTwoUpper X).subgroupOf X) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isNilpotent (↥X ⧸ (oTwoUpper X).subgroupOf X) inferInstance
  refine le_antisymm (oTwoUpper_le X) fun x hx => ?_
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : X) : ↥X ⧸ (oTwoUpper X).subgroupOf X) =
      QuotientGroup.mk 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq] at h1
  simpa [Subgroup.mem_subgroupOf] using h1

namespace HypF918

variable {T V L V₁ Vp H K : Subgroup G}

theorem F918_1 (h : HypF918 T V L V₁ Vp H K) :
    ⁅conjClosure K T, conjClosure K T⁆ = conjClosure K T ∧
      oTwoRes (conjClosure K T) = conjClosure K T ∧
      H ≤ Subgroup.normalizer (conjClosure K T : Set G) ∧
      ∀ E : Subgroup G, E ≤ conjClosure K T →
        conjClosure K T ≤ Subgroup.normalizer (E : Set G) →
        (∀ e ∈ E, ∃ k : ℕ, e ^ 2 ^ k ∈ pCoreOf 2 H) → E ≤ pCoreOf 2 H := by
  refine ⟨h.K₀_perfect, ?_, h.K₀_normal, fun E hEK hKE hE => ?_⟩
  · rw [oTwoRes_eq_oTwoUpper]
    exact oTwoUpper_eq_of_perfect_F9 h.K₀_perfect
  · have hpg : IsPGroup 2 E := by
      intro x
      obtain ⟨k, hk⟩ := hE x x.2
      obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨(x : G) ^ 2 ^ k, hk⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have h2 : ((x : G) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      rw [← pow_mul, ← pow_add] at h2
      simpa using h2
    have hEn : (E.subgroupOf (conjClosure K T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hEK).mpr hKE
    have h1 : E ≤ pCoreOf 2 (conjClosure K T) := le_pCoreOf 2 hEK hEn hpg
    have h2 : pCoreOf 2 (conjClosure K T) ≤ pCoreOf 2 H :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans h.K₀_le_H)
        (h.K₀_normal.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    exact h1.trans h2

theorem F918_2 (h : HypF918 T V L V₁ Vp H K) :
    ∃ B : Subgroup G, IsF918B T L V₁ Vp H (conjClosure K T) B ∧
      autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) ∈
        @Qset ↥(tildeOf V₁ (conjClosure Vp H))
          (commGroupOfElemAbelian h.toHypF98.toHypF91.isElemAbelian_tilde)
          (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) := by
  obtain ⟨B, hBL, hq⟩ := h.toHypF98.F916_3_aux
  exact ⟨B, ⟨hBL, hq, h.faithful_of_le_pCoreOf hBL⟩, h.toHypF98.toHypF91.mem_Qset_of_qcrit hq⟩

end HypF918

omit [Finite G] in
theorem le_normalizer_conjClosure_of_le {A I X : Subgroup G}
    (hAI : A ≤ Subgroup.normalizer (I : Set G)) (hXA : X ≤ Subgroup.normalizer (A : Set G)) :
    A ≤ Subgroup.normalizer (conjClosure I X : Set G) := by
  have key : ∀ a ∈ A, ∀ y ∈ conjClosure I X, a * y * a⁻¹ ∈ conjClosure I X := by
    intro a ha
    have hsup : conjClosure I X ≤ (conjClosure I X).comap (MulAut.conj a).toMonoidHom := by
      refine conjClosure_le fun x hx i hi => ?_
      show a * (x * i * x⁻¹) * a⁻¹ ∈ conjClosure I X
      have ha' : x⁻¹ * a * x ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (hXA (X.inv_mem hx)) a).mp ha
        simpa using this
      have h2 : (x⁻¹ * a * x) * i * (x⁻¹ * a * x)⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.mp (hAI ha') i).mp hi
      have h3 := mem_conjClosure hx h2
      have e : x * ((x⁻¹ * a * x) * i * (x⁻¹ * a * x)⁻¹) * x⁻¹ = a * (x * i * x⁻¹) * a⁻¹ := by
        group
      rwa [e] at h3
    exact fun y hy => hsup hy
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => key a ha y hy, fun hy => by simpa [mul_assoc] using key a⁻¹ (inv_mem ha) _ hy⟩

omit [Finite G] in
theorem conjClosure_le_conjClosure_U {Vp H I X : Subgroup G} (hIU : I ≤ conjClosure Vp H)
    (hXH : X ≤ H) : conjClosure I X ≤ conjClosure Vp H :=
  conjClosure_le fun _ hx _ hi =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H (hXH hx)) _).mp (hIU hi)

namespace HypF918

variable {T V L V₁ Vp H K : Subgroup G}

omit [Finite G] in
theorem T_le_of_cases {X : Subgroup G} (h : HypF918 T V L V₁ Vp H K) (hX : X = T ∨ X = H) :
    T ≤ X ∧ X ≤ H ∧ X ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
  rcases hX with hX | hX
  · rw [hX]
    exact ⟨le_rfl, h.T_le_H, le_normalizer_conjClosure K T⟩
  · rw [hX]
    exact ⟨h.T_le_H, le_rfl, h.K₀_normal⟩

theorem pCoreOf_L₁T_le_T (h : HypF918 T V L V₁ Vp H K) :
    pCoreOf 2 (L₁Of L V₁ ⊔ T) ≤ T :=
  isSylowTwoOf_pCoreOf_le (isSylowTwoOf_mono_right h.sylow le_sup_right le_top)

theorem isElemAbelian_tilde_conjClosure (h : HypF918 T V L V₁ Vp H K) {I X : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) (hX : X = T ∨ X = H) :
    IsElemAbelian 2 (tildeOf V₁ (conjClosure I X)) :=
  isElemAbelian_mono h.toHypF98.toHypF91.isElemAbelian_tilde
    (secImg_mono (conjClosure_le_conjClosure_U hIU (h.T_le_of_cases hX).2.1))

theorem centralizerMod_eq_inf_pCoreOf (h : HypF918 T V L V₁ Vp H K) {B F E : Subgroup G}
    (hV₁F : V₁ ≤ F) (hBF : B ≤ Subgroup.normalizer (F : Set G)) (hEU : E ≤ conjClosure Vp H)
    (hfaith : ∀ b ∈ B, (∀ e ∈ E, b * e * b⁻¹ * e⁻¹ ∈ F) → b ∈ pCoreOf 2 H) :
    centralizerMod F B E = B ⊓ pCoreOf 2 H := by
  ext b
  constructor
  · rintro ⟨hbB, -, hb⟩
    exact ⟨hbB, hfaith b hbB hb⟩
  · rintro ⟨hbB, hbQ⟩
    refine ⟨hbB, hBF hbB, fun e he => hV₁F ?_⟩
    have := V₁.inv_mem (h.toHypF98.toHypF91.commutator_conjClosure_le e (hEU he) b hbQ)
    have e' : (e * b * e⁻¹ * b⁻¹)⁻¹ = b * e * b⁻¹ * e⁻¹ := by group
    rwa [e'] at this

theorem relIndex_centralizerMod_le (F U E B : Subgroup G) (hEU : E ≤ U) :
    (centralizerMod F E B).relIndex E ≤ (centralizerMod F U B).relIndex U := by
  have e : centralizerMod F E B = centralizerMod F U B ⊓ E := by
    ext x
    constructor
    · rintro ⟨hxE, hxN, hx⟩
      exact ⟨⟨hEU hxE, hxN, hx⟩, hxE⟩
    · rintro ⟨⟨-, hxN, hx⟩, hxE⟩
      exact ⟨hxE, hxN, hx⟩
  rw [e, Subgroup.inf_relIndex_right]
  refine Subgroup.relIndex_le_of_le_right hEU ?_
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem F918_3 (h : HypF918 T V L V₁ Vp H K) {I B X : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) (hI : IsIrrPlusTilde V₁ (conjClosure K T) I)
    (hB : IsF918B T L V₁ Vp H (conjClosure K T) B) (hX : X = T ∨ X = H) :
    (∀ k ∈ conjClosure K T, (∀ i ∈ conjClosure I X, k * i * k⁻¹ * i⁻¹ ∈ V₁) →
        ∀ k' ∈ conjClosure K T, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) ∧
      (∀ b ∈ B, (∀ i ∈ conjClosure I X, b * i * b⁻¹ * i⁻¹ ∈ V₁) → b ∈ pCoreOf 2 H) ∧
      autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure I X)) ∈
        @Qset ↥(tildeOf V₁ (conjClosure I X))
          (commGroupOfElemAbelian (h.isElemAbelian_tilde_conjClosure hIU hX))
          (autOn (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ (conjClosure I X))) ∧
      qInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ (conjClosure I X))
        (h.isElemAbelian_tilde_conjClosure hIU hX) ≤ 2 ∧
      qInt (tildeOf V₁ (K ⊔ T)) (tildeOf V₁ (conjClosure I X))
        (h.isElemAbelian_tilde_conjClosure hIU hX) ≤ 2 := by
  obtain ⟨hBL, hq, hfaith⟩ := hB
  have h1 := h.toHypF98.toHypF91
  obtain ⟨hTX, hXH, hXK₀⟩ := h.T_le_of_cases hX
  have hBT : B ≤ T := hBL.trans h.pCoreOf_L₁T_le_T
  have hIX_U : conjClosure I X ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU hXH
  have hIXN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I X : Set G) :=
    sup_le (le_normalizer_conjClosure_of_le hI.1 hXK₀)
      (hTX.trans (le_normalizer_conjClosure I X))
  have hnt_I : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁ := by
    intro hall
    have hIC : I ≤ centralizerMod V₁ I (conjClosure K T) := by
      intro i hi
      refine ⟨hi, h1.H_normalizes_V₁ (pCoreOf_le 2 H (h1.conjClosure_Vp_le_pCoreOf (hIU hi))),
        fun k hk => ?_⟩
      have := V₁.inv_mem (hall k hk i hi)
      have e : (k * i * k⁻¹ * i⁻¹)⁻¹ = i * k * i⁻¹ * k⁻¹ := by group
      rwa [e] at this
    exact (not_le_of_gt hI.2.2.1) hIC
  have hnt_IX : ¬ ∀ k ∈ conjClosure K T, ∀ e ∈ conjClosure I X, k * e * k⁻¹ * e⁻¹ ∈ V₁ :=
    fun hall => hnt_I fun k hk i hi => hall k hk i (le_conjClosure I X hi)
  obtain ⟨hcentral, hfaithIX⟩ :=
    h.central_kernel_and_faithful hBT hfaith h.K₀T_le_normalizer_V₁ hIXN hnt_IX
  have hhC : centralizerMod V₁ B (conjClosure I X) = B ⊓ pCoreOf 2 H :=
    h.centralizerMod_eq_inf_pCoreOf le_rfl (hBT.trans (h.T_le_H.trans h1.H_normalizes_V₁))
      hIX_U hfaithIX
  have hIX_N : conjClosure I X ≤ Subgroup.normalizer (V₁ : Set G) :=
    hIX_U.trans (h1.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans h1.H_normalizes_V₁))
  have hr1 : (centralizerMod V₁ (conjClosure I X) B).relIndex (conjClosure I X) ≤
      ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 :=
    (relIndex_centralizerMod_le V₁ (conjClosure Vp H) (conjClosure I X) B hIX_U).trans
      hq.2.2.2.2
  have hmem : autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure I X)) ∈
      @Qset ↥(tildeOf V₁ (conjClosure I X))
        (commGroupOfElemAbelian (h.isElemAbelian_tilde_conjClosure hIU hX))
        (autOn (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ (conjClosure I X))) := by
    refine mem_Qset_autOn_secImg (K := V₁) (E := conjClosure I X) (X' := conjClosure K T ⊔ T)
      (B := B) (h.isElemAbelian_tilde_conjClosure hIU hX) hIX_N h.K₀T_le_normalizer_V₁ hIXN
      (hBT.trans le_sup_right) hq.2.1 ?_ ?_ ?_
    · intro hall
      exact hq.2.2.1 fun b hb => hfaithIX b hb fun e he => hall b hb e he
    · exact fun b₁ hb₁ b₂ hb₂ e he => hq.2.2.2.1 b₁ hb₁ b₂ hb₂ e (hIX_U he)
    · rw [hhC]; exact hr1
  refine ⟨hcentral, hfaithIX, hmem, ?_, ?_⟩
  · exact @qOf_le_two_of_mem_Qset _
      (commGroupOfElemAbelian (h.isElemAbelian_tilde_conjClosure hIU hX)) inferInstance _ _ hmem
  · refine @qOf_le_two_of_mem_Qset _
      (commGroupOfElemAbelian (h.isElemAbelian_tilde_conjClosure hIU hX)) inferInstance
      (autOn (tildeOf V₁ (K ⊔ T)) (tildeOf V₁ (conjClosure I X)))
      (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure I X))) ?_
    exact @mem_Qset_of_le _
      (commGroupOfElemAbelian (h.isElemAbelian_tilde_conjClosure hIU hX)) _ _ _ hmem
      (autOn_le_autOn _ (secImg_mono (hBT.trans le_sup_right)))

end HypF918

theorem relIndex_mul_le_relIndex {V₁ W U B : Subgroup G} (hV₁W : V₁ ≤ W) (hWU : W ≤ U)
    (hUW : U ≤ Subgroup.normalizer (W : Set G)) (hBW : B ≤ Subgroup.normalizer (W : Set G)) :
    (centralizerMod V₁ W B).relIndex W * (centralizerMod W U B).relIndex U ≤
      (centralizerMod V₁ U B).relIndex U := by
  have hCC₂ : centralizerMod V₁ U B ≤ centralizerMod W U B := fun x hx =>
    ⟨hx.1, hUW hx.1, fun b hb => hV₁W (hx.2.2 b hb)⟩
  have hWC₂ : W ≤ centralizerMod W U B := fun w hw => by
    refine ⟨hWU hw, Subgroup.le_normalizer hw, fun b hb => ?_⟩
    have h1 : b * w⁻¹ * b⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hBW hb) w⁻¹).mp (W.inv_mem hw)
    have e : w * b * w⁻¹ * b⁻¹ = w * (b * w⁻¹ * b⁻¹) := by group
    rw [e]
    exact W.mul_mem hw h1
  have hmul := Subgroup.relIndex_mul_relIndex (centralizerMod V₁ U B) (centralizerMod W U B) U
    hCC₂ (centralizerMod_le_left _ _ _)
  have e : centralizerMod V₁ W B = centralizerMod V₁ U B ⊓ W := by
    ext x
    constructor
    · rintro ⟨hxW, hxN, hx⟩
      exact ⟨⟨hWU hxW, hxN, hx⟩, hxW⟩
    · rintro ⟨⟨-, hxN, hx⟩, hxW⟩
      exact ⟨hxW, hxN, hx⟩
  have hne : (centralizerMod V₁ U B).relIndex (centralizerMod W U B) ≠ 0 := by
    unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite
  rw [e, Subgroup.inf_relIndex_right, ← hmul]
  exact Nat.mul_le_mul_right _ (Subgroup.relIndex_le_of_le_right hWC₂ hne)

namespace HypF918

variable {T V L V₁ Vp H K : Subgroup G}

omit [Finite G] in
theorem isElemAbelian_quotient (h : HypF918 T V L V₁ Vp H K) (W : Subgroup G) :
    IsElemAbelian 2 (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H)) :=
  isElemAbelian_secImg h.toHypF98.F911_3

theorem isElemAbelian_tilde_of_le (h : HypF918 T V L V₁ Vp H K) {W : Subgroup G}
    (hWU : W ≤ conjClosure Vp H) : IsElemAbelian 2 (tildeOf V₁ W) :=
  isElemAbelian_mono h.toHypF98.toHypF91.isElemAbelian_tilde (secImg_mono hWU)

theorem F918_6 (h : HypF918 T V L V₁ Vp H K) {W : Subgroup G}
    (hV₁W : V₁ ≤ W) (hWU : W ≤ conjClosure Vp H)
    (hWN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (W : Set G))
    (hW0 : tildeOf V₁ W ≠ ⊥) (hWK : tildeOf V₁ ⁅W, conjClosure K T⁆ = tildeOf V₁ W) :
    tildeOf V₁ W = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆ ∨
      (IsFFInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ W)
          (h.isElemAbelian_tilde_of_le hWU) ∧
        IsFFInt (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure K T ⊔ T))
          (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H))
          (h.isElemAbelian_quotient W)) ∨
      (F9.IsStrongFFInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ W)
          (h.isElemAbelian_tilde_of_le hWU) ∨
        F9.IsStrongFFInt (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure K T ⊔ T))
          (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H))
          (h.isElemAbelian_quotient W)) := by
  by_cases ha : tildeOf V₁ W = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆
  · exact Or.inl ha
  right
  obtain ⟨B, ⟨hBL, hq, hfaith⟩, -⟩ := h.F918_2
  have h1 := h.toHypF98.toHypF91
  have hBT : B ≤ T := hBL.trans h.pCoreOf_L₁T_le_T
  have hBX : B ≤ conjClosure K T ⊔ T := hBT.trans le_sup_right
  have hUH : conjClosure Vp H ≤ H := h1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hUW : conjClosure Vp H ≤ Subgroup.normalizer (W : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le h.toHypF98.F911_3 hWU
  have hBN₁ : B ≤ Subgroup.normalizer (V₁ : Set G) := hBT.trans (h.T_le_H.trans h1.H_normalizes_V₁)
  have hBNW : B ≤ Subgroup.normalizer (W : Set G) := hBX.trans hWN
  have hnt1 : ¬ ∀ k ∈ conjClosure K T, ∀ w ∈ W, k * w * k⁻¹ * w⁻¹ ∈ V₁ := by
    intro hall
    have hle : ⁅W, conjClosure K T⁆ ≤ V₁ := by
      refine Subgroup.commutator_le.mpr fun w hw k hk => ?_
      have := V₁.inv_mem (hall k hk w hw)
      have e : (k * w * k⁻¹ * w⁻¹)⁻¹ = w * k * w⁻¹ * k⁻¹ := by group
      rwa [e] at this
    apply hW0
    rw [← hWK]
    exact tildeOf_eq_bot_of_le hle
  have hnt2 : ¬ ∀ k ∈ conjClosure K T, ∀ u ∈ conjClosure Vp H, k * u * k⁻¹ * u⁻¹ ∈ W := by
    intro hall
    have hle : ⁅conjClosure Vp H, conjClosure K T⁆ ≤ W := by
      refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
      have := W.inv_mem (hall k hk u hu)
      have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ := by group
      rwa [e] at this
    apply ha
    refine le_antisymm ?_ (secImg_mono hle)
    rw [← hWK]
    exact secImg_mono (Subgroup.commutator_mono le_rfl le_rfl |>.trans' (Subgroup.commutator_mono hWU le_rfl))
  obtain ⟨-, hf1⟩ := h.central_kernel_and_faithful hBT hfaith h.K₀T_le_normalizer_V₁ hWN hnt1
  obtain ⟨-, hf2⟩ := h.central_kernel_and_faithful hBT hfaith hWN h.K₀T_le_normalizer_U hnt2
  have hC1 : centralizerMod V₁ B W = B ⊓ pCoreOf 2 H :=
    h.centralizerMod_eq_inf_pCoreOf le_rfl hBN₁ hWU hf1
  have hC2 : centralizerMod W B (conjClosure Vp H) = B ⊓ pCoreOf 2 H :=
    h.centralizerMod_eq_inf_pCoreOf hV₁W hBNW le_rfl hf2
  have hmul := (relIndex_mul_le_relIndex hV₁W hWU hUW hBNW (B := B)).trans hq.2.2.2.2
  have hβ : 0 < (B ⊓ pCoreOf 2 H).relIndex B := by
    refine Nat.pos_of_ne_zero ?_
    unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite
  have hnt1' : ¬ ∀ b ∈ B, ∀ e ∈ W, b * e * b⁻¹ * e⁻¹ ∈ V₁ := fun hall =>
    hq.2.2.1 fun b hb => hf1 b hb fun e he => hall b hb e he
  have hnt2' : ¬ ∀ b ∈ B, ∀ e ∈ conjClosure Vp H, b * e * b⁻¹ * e⁻¹ ∈ W := fun hall =>
    hq.2.2.1 fun b hb => hf2 b hb fun e he => hall b hb e he
  have FF1 : (centralizerMod V₁ W B).relIndex W ≤ (B ⊓ pCoreOf 2 H).relIndex B →
      IsFFInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ W)
        (h.isElemAbelian_tilde_of_le hWU) := fun hle =>
    isFFModule_autOn_secImg (K := V₁) (E := W) (X' := conjClosure K T ⊔ T) (B := B)
      (h.isElemAbelian_tilde_of_le hWU) (hWU.trans hUH |>.trans h1.H_normalizes_V₁)
      h.K₀T_le_normalizer_V₁ hWN hBX hq.2.1 hnt1' (by rw [hC1]; exact hle)
  have SFF1 : (centralizerMod V₁ W B).relIndex W < (B ⊓ pCoreOf 2 H).relIndex B →
      F9.IsStrongFFInt (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ W)
        (h.isElemAbelian_tilde_of_le hWU) := fun hlt =>
    isStrongFFModule_autOn_secImg (K := V₁) (E := W) (X' := conjClosure K T ⊔ T) (B := B)
      (h.isElemAbelian_tilde_of_le hWU) (hWU.trans hUH |>.trans h1.H_normalizes_V₁)
      h.K₀T_le_normalizer_V₁ hWN hBX hq.2.1 hnt1' (by rw [hC1]; exact hlt)
  have FF2 : (centralizerMod W (conjClosure Vp H) B).relIndex (conjClosure Vp H) ≤
        (B ⊓ pCoreOf 2 H).relIndex B →
      IsFFInt (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure K T ⊔ T))
        (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H))
        (h.isElemAbelian_quotient W) := fun hle =>
    isFFModule_autOn_secImg (K := W) (E := conjClosure Vp H) (X' := conjClosure K T ⊔ T) (B := B)
      (h.isElemAbelian_quotient W) hUW hWN h.K₀T_le_normalizer_U hBX hq.2.1 hnt2'
      (by rw [hC2]; exact hle)
  have SFF2 : (centralizerMod W (conjClosure Vp H) B).relIndex (conjClosure Vp H) <
        (B ⊓ pCoreOf 2 H).relIndex B →
      F9.IsStrongFFInt (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure K T ⊔ T))
        (secImg (Subgroup.normalizer (W : Set G)) W (conjClosure Vp H))
        (h.isElemAbelian_quotient W) := fun hlt =>
    isStrongFFModule_autOn_secImg (K := W) (E := conjClosure Vp H) (X' := conjClosure K T ⊔ T)
      (B := B) (h.isElemAbelian_quotient W) hUW hWN h.K₀T_le_normalizer_U hBX hq.2.1 hnt2'
      (by rw [hC2]; exact hlt)
  set a := (centralizerMod V₁ W B).relIndex W with ha_def
  set c := (centralizerMod W (conjClosure Vp H) B).relIndex (conjClosure Vp H) with hc_def
  set β := (B ⊓ pCoreOf 2 H).relIndex B with hβ_def
  by_cases hb1 : a ≤ β
  · by_cases hb2 : c ≤ β
    · exact Or.inl ⟨FF1 hb1, FF2 hb2⟩
    · refine Or.inr (Or.inl (SFF1 ?_))
      by_contra hnot
      push Not at hnot hb2
      nlinarith
  · refine Or.inr (Or.inr (SFF2 ?_))
    by_contra hnot
    push Not at hnot hb1
    nlinarith

end HypF918

omit [Finite G] in
theorem F9.IsStrongFFInt.isFFInt {G₁ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : F9.IsStrongFFInt G₁ V hV) : IsFFInt G₁ V hV := by
  obtain ⟨A, hA, hne, hel, hlt⟩ := h
  exact ⟨A, hA, hne, hel, hlt.le⟩

theorem not_hasNoFFModulesMod_of_isFFInt {X C F E : Subgroup G}
    (hFN : X ≤ Subgroup.normalizer (F : Set G)) (hEN : X ≤ Subgroup.normalizer (E : Set G))
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (F : Set G)) F E))
    (hC : ∀ x ∈ X ⊓ C, ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ F)
    (hFF : IsFFInt (secImg (Subgroup.normalizer (F : Set G)) F X)
      (secImg (Subgroup.normalizer (F : Set G)) F E) hE) :
    ¬ HasNoFFModulesMod X C := by
  intro hNo
  let S : Subgroup (SecQuot (Subgroup.normalizer (F : Set G)) F) :=
    secImg (Subgroup.normalizer (F : Set G)) F E
  let _ : CommGroup ↥S := commGroupOfElemAbelian hE
  let f : ↥X →* SecQuot (Subgroup.normalizer (F : Set G)) F :=
    (secMk (Subgroup.normalizer (F : Set G)) F).comp (Subgroup.inclusion hFN)
  have hf : ∀ x : ↥X,
      f x ∈ Subgroup.normalizer (S : Set (SecQuot (Subgroup.normalizer (F : Set G)) F)) :=
    fun x => secMk_mem_normalizer_secImg (X := E) (a := ⟨x, hFN x.2⟩) (hEN x.2)
  let ρ : ↥X →* MulAut ↥S := (conjAct S).comp (f.codRestrict _ hf)
  have hsq : ∀ w : ↥S, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hE.2 w w.2)
  have hker : ∀ x : ↥X, (x : G) ∈ C → ρ x = 1 := by
    intro x hxC
    refine MulEquiv.ext fun w => ?_
    rw [MulAut.one_apply]
    apply Subtype.ext
    obtain ⟨e, he, hew⟩ := mem_secImg.mp w.2
    have hcomm : secMk (Subgroup.normalizer (F : Set G)) F ⟨x, hFN x.2⟩ *
        secMk (Subgroup.normalizer (F : Set G)) F e =
        secMk (Subgroup.normalizer (F : Set G)) F e *
        secMk (Subgroup.normalizer (F : Set G)) F ⟨x, hFN x.2⟩ :=
      secMk_comm_of_commutator_mem (hC x ⟨x.2, hxC⟩ e he)
    have hw : (w : SecQuot (Subgroup.normalizer (F : Set G)) F) =
        secMk (Subgroup.normalizer (F : Set G)) F e := hew.symm
    have h1 : ((ρ x w : ↥S) : SecQuot (Subgroup.normalizer (F : Set G)) F) =
        f x * (w : SecQuot (Subgroup.normalizer (F : Set G)) F) * (f x)⁻¹ :=
      conjAct_apply_coe' S ⟨f x, hf x⟩ w
    rw [h1, hw]
    change secMk _ F ⟨x, hFN x.2⟩ * secMk _ F e * (secMk _ F ⟨x, hFN x.2⟩)⁻¹ = secMk _ F e
    rw [hcomm]; group
  have hrange : ρ.range = autOn (secImg (Subgroup.normalizer (F : Set G)) F X) S := by
    ext a
    rw [mem_autOn_iff]
    constructor
    · rintro ⟨x, rfl⟩
      have hfx : f x = secMk (Subgroup.normalizer (F : Set G)) F ⟨x, hFN x.2⟩ := rfl
      refine ⟨⟨f x, hf x⟩, ?_, rfl⟩
      show f x ∈ secImg (Subgroup.normalizer (F : Set G)) F X
      rw [hfx]
      exact secMk_mem_secImg (A := Subgroup.normalizer (F : Set G)) (B := F) (X := X)
        (x := ⟨(x : G), hFN x.2⟩) x.2
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨y, hy, hys⟩ := mem_secImg.mp (hs : (s : SecQuot (Subgroup.normalizer (F : Set G)) F) ∈
        secImg (Subgroup.normalizer (F : Set G)) F X)
      refine ⟨⟨y, hy⟩, ?_⟩
      have : (⟨f ⟨y, hy⟩, hf ⟨y, hy⟩⟩ : ↥(Subgroup.normalizer
          (S : Set (SecQuot (Subgroup.normalizer (F : Set G)) F)))) = s := Subtype.ext hys
      show (conjAct S) _ = conjAct S s
      rw [← this]
      rfl
  have := hNo ↥S hsq ρ hker
  rw [hrange] at this
  exact this hFF

namespace HypF918

variable {T V L V₁ Vp H K : Subgroup G}

theorem tilde_commutator_conjClosure (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) (hI : IsIrrPlusTilde V₁ (conjClosure K T) I) :
    tildeOf V₁ ⁅conjClosure I H, conjClosure K T⁆ = tildeOf V₁ (conjClosure I H) := by
  have h1 := h.toHypF98.toHypF91
  have hIHU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hUH : conjClosure Vp H ≤ H := h1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hHIH : H ≤ Subgroup.normalizer (conjClosure I H : Set G) := le_normalizer_conjClosure I H
  have hK₀IH : conjClosure K T ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    h.K₀_le_H.trans hHIH
  have hle : ⁅conjClosure I H, conjClosure K T⁆ ≤ conjClosure I H := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hK₀IH
  refine le_antisymm (secImg_mono hle) ?_
  have hcommN : H ≤ Subgroup.normalizer
      ((⁅conjClosure I H, conjClosure K T⁆ : Subgroup G) : Set G) :=
    F9.le_normalizer_commutator_of_le hHIH h.K₀_normal
  have hIN : ∀ i ∈ I, i ∈ Subgroup.normalizer (V₁ : Set G) := fun i hi =>
    h1.H_normalizes_V₁ (hUH (hIU hi))
  have hgen : conjClosure I H ≤ ⁅conjClosure I H, conjClosure K T⁆ ⊔ V₁ := by
    refine conjClosure_le fun x hx i hi => ?_
    have hi' : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hIN i hi⟩ ∈
        tildeOf V₁ ⁅I, conjClosure K T⁆ := by
      rw [hI.2.1]
      exact secMk_mem_secImg (x := ⟨i, hIN i hi⟩) hi
    obtain ⟨c, hc, hci⟩ := mem_secImg.mp hi'
    have hv : (c : G)⁻¹ * i ∈ V₁ := secMk_eq_secMk_iff.mp hci
    have hc' : (c : G) ∈ ⁅conjClosure I H, conjClosure K T⁆ :=
      Subgroup.commutator_mono (le_conjClosure I H) le_rfl hc
    have e : x * i * x⁻¹ = (x * (c : G) * x⁻¹) * (x * ((c : G)⁻¹ * i) * x⁻¹) := by group
    have hxv : x * ((c : G)⁻¹ * i) * x⁻¹ = (c : G)⁻¹ * i := by
      have := Subgroup.mem_centralizer_iff.mp (h1.H_le_centralizer hx) _ hv
      rw [← this]; group
    rw [e, hxv]
    exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp (hcommN hx) (c : G)).mp hc') hv
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_secImg.mp hy
  have hcN : ⁅conjClosure I H, conjClosure K T⁆ ≤ Subgroup.normalizer (V₁ : Set G) :=
    hle.trans (hIHU.trans (hUH.trans h1.H_normalizes_V₁))
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right
    (⁅conjClosure I H, conjClosure K T⁆) V₁ hcN
  have hzs' : (z : G) ∈ ((⁅conjClosure I H, conjClosure K T⁆ : Subgroup G) : Set G) *
      (V₁ : Set G) := by
    rw [← hmul]; exact hgen hz
  obtain ⟨c, hc, v, hv, hcv⟩ := hzs'
  refine mem_secImg.mpr ⟨⟨c, hcN hc⟩, hc, ?_⟩
  rw [secMk_eq_secMk_iff]
  show c⁻¹ * (z : G) ∈ V₁
  rw [← hcv]
  simpa using hv

theorem F918_7 (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hI₁ : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hI : IsIrrPlusTilde V₁ (conjClosure K T) I)
    (hNo : HasNoFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 H)) :
    tildeOf V₁ (conjClosure I H) = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆ := by
  have h1 := h.toHypF98.toHypF91
  have hUH : conjClosure Vp H ≤ H := h1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hIHU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hIHN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    h.K₀T_le_H.trans (le_normalizer_conjClosure I H)
  have hQV₁ : ∀ x ∈ pCoreOf 2 H, ∀ e ∈ conjClosure Vp H, x * e * x⁻¹ * e⁻¹ ∈ V₁ := by
    intro x hx e he
    have := V₁.inv_mem (h1.commutator_conjClosure_le e he x hx)
    have e' : (e * x * e⁻¹ * x⁻¹)⁻¹ = x * e * x⁻¹ * e⁻¹ := by group
    rwa [e'] at this
  have hW0 : tildeOf V₁ (conjClosure I H) ≠ ⊥ := by
    intro hbot
    have hIV₁ : I ≤ V₁ := by
      intro i hi
      have hiN : i ∈ Subgroup.normalizer (V₁ : Set G) := h1.H_normalizes_V₁ (hUH (hIU hi))
      have : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hiN⟩ ∈
          tildeOf V₁ (conjClosure I H) :=
        secMk_mem_secImg (x := ⟨i, hiN⟩) (le_conjClosure I H hi)
      rw [hbot] at this
      have h2 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hiN⟩ = 1 := this
      exact secMk_eq_one_iff.mp h2
    have hIC : I ≤ centralizerMod V₁ I (conjClosure K T) := by
      intro i hi
      refine ⟨hi, h1.H_normalizes_V₁ (hUH (hIU hi)), fun k hk => ?_⟩
      have h3 : k * i⁻¹ * k⁻¹ ∈ V₁ :=
        (Subgroup.mem_normalizer_iff.mp (h1.H_normalizes_V₁ (h.K₀_le_H hk)) i⁻¹).mp
          (V₁.inv_mem (hIV₁ hi))
      have e : i * k * i⁻¹ * k⁻¹ = i * (k * i⁻¹ * k⁻¹) := by group
      rw [e]
      exact V₁.mul_mem (hIV₁ hi) h3
    exact (not_le_of_gt hI.2.2.1) hIC
  have hFF1 : ∀ hFF : IsFFInt (secImg (Subgroup.normalizer (V₁ : Set G)) V₁ (conjClosure K T ⊔ T))
      (secImg (Subgroup.normalizer (V₁ : Set G)) V₁ (conjClosure I H))
      (h.isElemAbelian_tilde_of_le hIHU), False := fun hFF =>
    not_hasNoFFModulesMod_of_isFFInt (F := V₁) (E := conjClosure I H) h.K₀T_le_normalizer_V₁
      hIHN (h.isElemAbelian_tilde_of_le hIHU) (fun x hx e he => hQV₁ x hx.2 e (hIHU he)) hFF hNo
  have hFF2 : ∀ hFF : IsFFInt
      (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
        (conjClosure K T ⊔ T))
      (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
        (conjClosure Vp H)) (h.isElemAbelian_quotient (conjClosure I H)), False := fun hFF =>
    not_hasNoFFModulesMod_of_isFFInt (F := conjClosure I H) (E := conjClosure Vp H) hIHN
      h.K₀T_le_normalizer_U (h.isElemAbelian_quotient _)
      (fun x hx e he => le_conjClosure I H (hI₁ (hQV₁ x hx.2 e he))) hFF hNo
  rcases h.F918_6 (le_trans hI₁ (le_conjClosure I H)) hIHU hIHN hW0
      (h.tilde_commutator_conjClosure hIU hI) with ha | ⟨hb1, hb2⟩ | hc
  · exact ha
  · exact (hFF1 hb1).elim
  · rcases hc with hc | hc
    · exact (hFF1 (F9.IsStrongFFInt.isFFInt hc)).elim
    · exact (hFF2 (F9.IsStrongFFInt.isFFInt hc)).elim

end HypF918

end Fin

end CFSG.Quasithin
