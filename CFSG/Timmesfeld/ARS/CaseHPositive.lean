module

public import CFSG.Timmesfeld.ARS.CaseHInterval

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

theorem commutator_le_of_le_of_conjSub_eq {H K N : Subgroup G} (hHN : H ≤ N)
    (hK : ∀ k ∈ K, conjSub N k = N) : ⁅H, K⁆ ≤ N :=
  Subgroup.commutator_le.2 fun x hx k hk => by
    have e : ⁅x, k⁆ = x * (k * x⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    refine N.mul_mem (hHN hx) ?_
    have : k * x⁻¹ * k⁻¹ ∈ conjSub N k := conj_mem_conjSub k (N.inv_mem (hHN hx))
    rwa [hK k hk] at this

theorem conjSub_M_of_commute [Finite G] (hR : IsRootClass R) {X : Subgroup G} (hX : X ∈ R)
    {k : G} (hk : ∀ x ∈ X, Commute k x) : conjSub (M R X) k = M R X :=
  (isPGroup_M hR hX).2.2 k (conjSub_eq_self_iff.1 (conjSub_of_forall_commute hk))

section Positive

variable (h : Hyp G R) (hH : SigmaEqLambda R)
include h hH

theorem commutator_a_ab_le (hT : MTransitive R) {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (h3 : 3 ≤ (linesThrough R A).ncard) (hA₀ : A₀ ∈ omegaSet R A)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPP' : P ≠ P') :
    ⁅shortRoot R A A₀ P', shortRoot R P' ⁅A₀, P⁆ A⁆ ≤ P' ⊔ A ⊔ shortRoot R P ⁅A₀, P'⁆ A := by
  have := h.finite
  have hR := h.root
  have hPR : P ∈ R := hP.2.1
  have hP'R : P' ∈ R := hP'.2.1
  obtain ⟨-, -, -, -, -, -, ⟨hsAQ', hcAQ'⟩, -, hQ'Ω, -⟩ := apartment h hH hA hA₀ hP hP' hPP'
  have hAs : A ∈ lambdaStar R P ⁅A₀, P'⁆ := ⟨mem_lambdaSet_comm hA hP.1, hA, hsAQ'.symm⟩
  have hL : 3 ≤ (linesThrough R P).ncard := (ncard_linesThrough_eq h hA hPR) ▸ h3
  have hline := M_inf_M_eq h hH hT hPR hL hQ'Ω hAs
  rw [Subgroup.commutator_comm ⁅A₀, P'⁆ A, hcAQ'] at hline
  rw [← sup_comm A P', ← hline]
  refine le_inf ?_ ?_
  ·
    rw [Subgroup.commutator_comm]
    exact commutator_le_of_le_of_conjSub_eq (shortRoot_le_M _ _ A) fun k hk =>
      conjSub_M_of_commute hR hA fun x hx => commuting_shortRoot_left A A₀ P' k hk x hx
  ·
    exact commutator_le_of_le_of_conjSub_eq (shortRoot_le_M A A₀ P') fun k hk =>
      conjSub_M_of_commute hR hP'R fun x hx => commuting_shortRoot_left P' _ A k hk x hx

omit hH in
theorem commutator_a_b_le {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) :
    ⁅shortRoot R A A₀ P', P⁆ ≤ M R A ⊓ Subgroup.normalizer (P' : Set G) := by
  have := h.finite
  have hR := h.root
  refine le_inf ?_ ?_
  · rw [Subgroup.commutator_comm]
    exact commutator_le_of_le_of_conjSub_eq (QD.le_M hP.1) fun k hk =>
      conjSub_M_of_commute hR hA fun x hx => commuting_shortRoot_left A A₀ P' k hk x hx
  · refine Subgroup.commutator_le.2 fun y hy p hp => conjSub_eq_self_iff.1 ?_
    have hyV : ∀ v ∈ A ⊔ P', Commute y v := by
      intro v hv
      have hc : Commuting (shortRoot R A A₀ P') (A ⊔ P') :=
        (commuting_shortRoot_left A A₀ P').sup_right (commuting_shortRoot_mid h hP'.2.1)
      exact hc y hy v hv
    have hpV : conjSub (A ⊔ P') p⁻¹ = A ⊔ P' :=
      conjSub_sup_eq_of_mem_M h hA hP'.1 ((M R A).inv_mem (QD.le_M hP.1 hp))
    have hB : conjSub P' p⁻¹ ≤ A ⊔ P' := by
      rw [← hpV]
      exact Subgroup.map_mono le_sup_right
    have hyB : conjSub (conjSub P' p⁻¹) y⁻¹ = conjSub P' p⁻¹ :=
      conjSub_of_forall_commute fun v hv => (hyV v (hB hv)).inv_left
    have hyP' : conjSub P' y = P' := conjSub_of_forall_commute fun v hv =>
      commuting_shortRoot_mid h hP'.2.1 y hy v hv
    calc conjSub P' ⁅y, p⁆ = conjSub (conjSub (conjSub (conjSub P' p⁻¹) y⁻¹) p) y := by
          rw [commutatorElement_def, ← conjSub_mul, ← conjSub_mul, ← conjSub_mul]
      _ = P' := by rw [hyB, Plane.conjSub_inv_conjSub, hyP']

theorem card_M_inf_M (hT : MTransitive R) {X Y Z : Subgroup G} (hX : X ∈ R)
    (h3 : 3 ≤ (linesThrough R X).ncard) (hY : Y ∈ omegaSet R X) (hZ : Z ∈ lambdaStar R X Y) :
    Nat.card ↥(M R Z ⊓ M R ⁅Y, Z⁆) =
      Nat.card X * (Nat.card X * ((linesThrough R X).ncard - 1)) := by
  have := h.finite
  have hR := h.root
  obtain ⟨hZ'Y, -⟩ := commutator_mem_lambdaSet h hY.1 hZ.2.1 hZ.2.2
  refine le_antisymm (card_M_inf_M_le h hH hX hY hZ) ?_
  have hmem : ∀ p : ↥Z × ↥⁅Y, Z⁆ × ↥(shortRoot R X Y Z),
      (p.1 : G) * p.2.1 * p.2.2 ∈ M R Z ⊓ M R ⁅Y, Z⁆ := fun p => by
    rw [M_inf_M_eq h hH hT hX h3 hY hZ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left
      p.1.2)) (Subgroup.mem_sup_left (Subgroup.mem_sup_right p.2.1.2)))
      (Subgroup.mem_sup_right p.2.2.2)
  have hinj := injective_mul_shortRoot h hH hT hX hY hZ
  calc Nat.card X * (Nat.card X * ((linesThrough R X).ncard - 1))
      = Nat.card (↥Z × ↥⁅Y, Z⁆ × ↥(shortRoot R X Y Z)) := by
        rw [Nat.card_prod, Nat.card_prod, hR.card_eq hZ.2.1 hX, hR.card_eq hZ'Y.1.1 hX,
          card_shortRoot h hH hT hX hY hZ]
    _ ≤ Nat.card ↥(M R Z ⊓ M R ⁅Y, Z⁆) :=
        Nat.card_le_card_of_injective (fun p => ⟨_, hmem p⟩) fun p p' e =>
          hinj (congrArg Subtype.val e)

theorem M_inf_normalizer_le (hT : MTransitive R) {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (h3 : 3 ≤ (linesThrough R A).ncard) (hA₀ : A₀ ∈ omegaSet R A)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPP' : P ≠ P') :
    M R A ⊓ Subgroup.normalizer (P' : Set G) ≤
      M R A ⊓ M R P' ⊔ shortRoot R P' ⁅A₀, P⁆ A := by
  classical
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hPR : P ∈ R := hP.2.1
  have hP'R : P' ∈ R := hP'.2.1
  obtain ⟨-, -, -, -, ⟨hsPP', -⟩, ⟨hsAQ, -⟩, ⟨hsAQ', hcAQ'⟩, -, hQ'Ω, hQΩ⟩ :=
    apartment h hH hA hA₀ hP hP' hPP'
  set K := M R A ⊓ M R P' with hK
  set Y := shortRoot R P' ⁅A₀, P⁆ A with hY
  set q := Nat.card A with hq
  set t := (linesThrough R A).ncard - 1 with ht
  have hAs : A ∈ lambdaStar R P ⁅A₀, P'⁆ := ⟨mem_lambdaSet_comm hA hP.1, hA, hsAQ'.symm⟩
  have hLP : (linesThrough R P).ncard = (linesThrough R A).ncard := ncard_linesThrough_eq h hA hPR
  have hcardK : Nat.card K = q * (q * t) := by
    have := card_M_inf_M h hH hT hPR (hLP ▸ h3) hQ'Ω hAs
    rw [Subgroup.commutator_comm ⁅A₀, P'⁆ A, hcAQ', hR.card_eq hPR hA, hLP] at this
    exact this
  have hAs' : A ∈ lambdaStar R P' ⁅A₀, P⁆ := ⟨mem_lambdaSet_comm hA hP'.1, hA, hsAQ.symm⟩
  have hLP' : (linesThrough R P').ncard = (linesThrough R A).ncard :=
    ncard_linesThrough_eq h hA hP'R
  have hcardY : Nat.card Y = t := by
    rw [hY, card_shortRoot h hH hT hP'R hQΩ hAs', hLP']
  have hYK : ∀ y ∈ Y, y ∈ K → y = 1 := by
    intro y hy hyK
    obtain ⟨-, -, hreg⟩ := shortRoot_moufang_of h hH hT hP'R hQΩ hAs'
    obtain ⟨W, hW, hWA⟩ : ∃ W ∈ linesThrough R P', ¬ A ≤ W := by
      by_contra hno
      push Not at hno
      have hsub : linesThrough R P' ⊆ {P' ⊔ A} := fun W hW =>
        eq_sup_of_le h hP'R hAs'.1 hW (hno W hW)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_singleton, hLP'] at this
      omega
    obtain ⟨D, hD, rfl⟩ := (mem_linesThrough_iff h hP'R).1 hW
    have hyW : conjSub (P' ⊔ D) y = P' ⊔ D := conjSub_sup_eq_of_mem_M h hP'R hD hyK.2
    obtain ⟨u₀, -, huniq⟩ := hreg (P' ⊔ D) hW (P' ⊔ D) hW hWA hWA
    exact congrArg Subtype.val ((huniq ⟨y, hy⟩ hyW).trans (huniq 1 (conjSub_one _)).symm)
  have hge : q * (q * t) * t ≤ Nat.card ↥(K ⊔ Y) := by
    rw [← hcardK, ← hcardY, ← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun p => ⟨(p.1 : G) * p.2,
      Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩) ?_
    rintro ⟨⟨k, hk⟩, ⟨y, hy⟩⟩ ⟨⟨k', hk'⟩, ⟨y', hy'⟩⟩ e
    simp only [Subtype.mk.injEq] at e
    have h1 : k'⁻¹ * k = y' * y⁻¹ := by
      calc k'⁻¹ * k = k'⁻¹ * (k * y) * y⁻¹ := by group
        _ = k'⁻¹ * (k' * y') * y⁻¹ := by rw [e]
        _ = y' * y⁻¹ := by group
    have h2 := hYK _ (Y.mul_mem hy' (Y.inv_mem hy)) (h1 ▸ K.mul_mem (K.inv_mem hk') hk)
    have hyy : y = y' := (mul_inv_eq_one.mp h2).symm
    have hkk : k = k' := by
      rw [h2] at h1
      exact (inv_mul_eq_one.mp h1).symm
    subst hyy hkk
    rfl
  have hle : Nat.card ↥(M R A ⊓ Subgroup.normalizer (P' : Set G)) * q ≤ Nat.card (M R A) := by
    let _ : MulAction (M R A) (Subgroup G) :=
      { smul := fun m B => conjSub B (m : G)
        one_smul := fun B => conjSub_one B
        mul_smul := fun m m' B => conjSub_mul B m m' }
    have h1 := (MulAction.stabilizer (M R A) P').card_mul_index
    rw [MulAction.index_stabilizer] at h1
    have hstab : Nat.card (MulAction.stabilizer (M R A) P') =
        Nat.card ↥(M R A ⊓ Subgroup.normalizer (P' : Set G)) :=
      Nat.card_congr
        { toFun := fun m => ⟨m.1.1, m.1.2, conjSub_eq_self_iff.1 m.2⟩
          invFun := fun k => ⟨⟨k.1, k.2.1⟩, conjSub_eq_self_iff.2 k.2.2⟩
          left_inv := fun m => rfl
          right_inv := fun k => rfl }
    have horb : q ≤ (MulAction.orbit (M R A) P').ncard := by
      have hinj : Function.Injective fun p : P => conjSub P' (p : G) := by
        intro p p' e
        have e' : conjSub P' ((p' : G)⁻¹ * p) = P' := by
          change conjSub P' p = conjSub P' p' at e
          rw [conjSub_mul, e, ← conjSub_mul, inv_mul_cancel, conjSub_one]
        by_contra hne
        have h1 : (p' : G)⁻¹ * p ≠ 1 := fun h1 => hne (Subtype.ext (inv_mul_eq_one.mp h1)).symm
        exact Sec3.conjSub_ne_of_special hR hiso hPR hP'R hsPP'
          (P.mul_mem (P.inv_mem p'.2) p.2) h1 e'
      have hsub : Set.range (fun p : P => conjSub P' (p : G)) ⊆ MulAction.orbit (M R A) P' := by
        rintro _ ⟨p, rfl⟩
        exact ⟨⟨p, QD.le_M hP.1 p.2⟩, rfl⟩
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj, hR.card_eq hPR hA] at this
    rw [hstab] at h1
    rw [← h1]
    exact Nat.mul_le_mul_left _ horb
  have hMA : Nat.card (M R A) = t ^ 2 * q ^ 3 := by
    rw [card_M_eq h hT hA, ncard_omegaSet h hH hA rfl rfl]
  have hKY : K ⊔ Y ≤ M R A ⊓ Subgroup.normalizer (P' : Set G) := by
    refine sup_le (le_inf inf_le_left (inf_le_right.trans fun x hx =>
      (isPGroup_M hR hP'R).2.1 hx)) (le_inf (shortRoot_le_M _ _ A) fun y hy => ?_)
    exact conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun v hv =>
      commuting_shortRoot_left P' _ A y hy v hv)
  have hqpos : 0 < q := Nat.card_pos
  have hcard : Nat.card ↥(M R A ⊓ Subgroup.normalizer (P' : Set G)) ≤ Nat.card ↥(K ⊔ Y) := by
    refine Nat.le_of_mul_le_mul_right ?_ hqpos
    calc Nat.card ↥(M R A ⊓ Subgroup.normalizer (P' : Set G)) * q ≤ t ^ 2 * q ^ 3 := hMA ▸ hle
      _ = q * (q * t) * t * q := by ring
      _ ≤ Nat.card ↥(K ⊔ Y) * q := Nat.mul_le_mul_right _ hge
  exact (Subgroup.eq_of_le_of_card_ge hKY hcard).ge

end Positive

end CaseH

end CFSG.Timmesfeld.ARS
