module

public import CFSG.Timmesfeld.ARS.CaseHTwo

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def MTransitive (R : Set (Subgroup G)) : Prop :=
  ∀ A ∈ R, ∀ B ∈ omegaSet R A, ∀ B' ∈ omegaSet R A, ∃ m ∈ M R A, conjSub B m = B'

namespace CaseH

section Moufang

variable (h : Hyp G R)
include h

theorem card_M_eq (hT : MTransitive R) {A : Subgroup G} (hA : A ∈ R) :
    Nat.card (M R A) = (omegaSet R A).ncard := by
  have := h.finite
  obtain ⟨B, hBR, hAB⟩ := h.noIsolated A hA
  have hB : B ∈ omegaSet R A := ⟨hBR, hAB⟩
  have hrange : Set.range (fun m : M R A => conjSub B (m : G)) = omegaSet R A := by
    ext B'
    constructor
    · rintro ⟨m, rfl⟩
      exact conjSub_mem_omegaSet h hA hB m.2
    · intro hB'
      obtain ⟨m, hm, e⟩ := hT A hA B hB B' hB'
      exact ⟨⟨m, hm⟩, e⟩
  rw [← hrange, ← Nat.card_coe_set_eq, Nat.card_range_of_injective (orbitMap_injective h hA hB)]

theorem conjSub_sup_eq_of_mem_M {P X : Subgroup G} (hP : P ∈ R) (hX : X ∈ lambdaSet R P)
    {m : G} (hm : m ∈ M R P) : conjSub (P ⊔ X) m = P ⊔ X := by
  have := h.finite
  obtain ⟨-, -, hMM, -, -⟩ := Q_eq_M h hP
  have hle : conjSub (P ⊔ X) m ≤ P ⊔ X := by
    rintro _ ⟨y, hy, rfl⟩
    have hyM : y ∈ M R P := sup_le QD.le_M_self (QD.le_M hX) hy
    change m * y * m⁻¹ ∈ P ⊔ X
    rw [conj_eq_commutator_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hMM ▸ Subgroup.commutator_mem_commutator hm
      hyM)) hy
  refine le_antisymm hle ?_
  have hle' : conjSub (P ⊔ X) m⁻¹ ≤ P ⊔ X := by
    rintro _ ⟨y, hy, rfl⟩
    have hyM : y ∈ M R P := sup_le QD.le_M_self (QD.le_M hX) hy
    change m⁻¹ * y * m⁻¹⁻¹ ∈ P ⊔ X
    rw [conj_eq_commutator_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hMM ▸ Subgroup.commutator_mem_commutator
      ((M R P).inv_mem hm) hyM)) hy
  have := Subgroup.map_mono (f := (MulAut.conj m).toMonoidHom) hle'
  change conjSub (conjSub (P ⊔ X) m⁻¹) m ≤ conjSub (P ⊔ X) m at this
  rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this

theorem mem_centralizer_of_mem_M_of_conjSub_eq {P A : Subgroup G} (hP : P ∈ R)
    (hA : A ∈ lambdaSet R P) {m : G} (hm : m ∈ M R P) (hmA : conjSub A m = A) :
    m ∈ Subgroup.centralizer (A : Set G) := by
  have := h.finite
  obtain ⟨-, -, hMM, -, -⟩ := Q_eq_M h hP
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 : ⁅m, a⁆ ∈ P := hMM ▸ Subgroup.commutator_mem_commutator hm (QD.le_M hA ha)
  have h2 : ⁅m, a⁆ ∈ A := by
    rw [commutatorElement_def]
    refine A.mul_mem ?_ (A.inv_mem ha)
    have := conj_mem_conjSub m ha
    rwa [hmA] at this
  have h3 : ⁅m, a⁆ ∈ A ⊓ P := ⟨h2, h1⟩
  rw [inf_eq_bot h.root h.noIsolated hA.1.1 hP hA.1.2.1, Subgroup.mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at h3
  exact h3.symm

omit h in
theorem mem_centralizer_of_opposite {A A₀ : Subgroup G} (hop : Opposite A A₀)
    {y : G} (hyA : y ∈ Subgroup.centralizer (A : Set G)) (hyA₀ : conjSub A₀ y = A₀) :
    y ∈ Subgroup.centralizer (A₀ : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  rcases eq_or_ne b 1 with rfl | hb1
  · simp
  obtain ⟨a, ha, ha1, hab⟩ := hop.2.2 b hb hb1
  obtain ⟨b', ⟨hb', hb'e⟩, huniq⟩ := hop.existsUnique_conjSub_eq ha ha1
  have hbb : b = b' := huniq b ⟨hb, hab.symm⟩
  have hya : y * a * y⁻¹ = a := by
    rw [(Subgroup.mem_centralizer_iff.1 hyA a ha).symm, mul_inv_cancel_right]
  have hyAy : conjSub A y = A := conjSub_of_forall_commute fun x hx =>
    (Subgroup.mem_centralizer_iff.1 hyA x hx).symm
  have hyAy' : conjSub A y⁻¹ = A := by
    conv_lhs => rw [← hyAy]
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hc : conjSub A (y * b * y⁻¹) = conjSub A₀ a := by
    calc conjSub A (y * b * y⁻¹) = conjSub (conjSub (conjSub A y⁻¹) b) y := by
          rw [← conjSub_mul, ← conjSub_mul, mul_assoc]
      _ = conjSub (conjSub A₀ a) y := by rw [hyAy', ← hab]
      _ = conjSub (conjSub A₀ y) (y * a * y⁻¹) := by
          rw [← conjSub_mul, ← conjSub_mul]
          congr 1
          group
      _ = conjSub A₀ a := by rw [hyA₀, hya]
  have hyb : y * b * y⁻¹ ∈ A₀ := by
    have := conj_mem_conjSub y hb
    rwa [hyA₀] at this
  have := huniq _ ⟨hyb, hc⟩
  rw [← hbb] at this
  calc b * y = (y * b * y⁻¹) * y := by rw [this]
    _ = y * b := by group

variable (hH : SigmaEqLambda R)
include hH

theorem mTransitive_of_nine {A₁ : Subgroup G} (hA₁ : A₁ ∈ R) (hq : Nat.card A₁ = 2)
    (hL : (linesThrough R A₁).ncard = 9) : MTransitive R := fun _ hA _ hB _ hB' =>
  M_transitive_of_nine h hH hA ((h.root.card_eq hA hA₁).trans hq)
    ((ncard_linesThrough_eq h hA₁ hA).trans hL) hB hB'

theorem setOf_psiSet_lambdaSet {A D : Subgroup G} (hA : A ∈ R) (hD : D ∈ lambdaSet R A) :
    {C | C ∈ psiSet R A ∧ C ∈ lambdaSet R D} = lambdaSet R D \ pointsOn R (A ⊔ D) := by
  have hR := h.root
  ext C
  constructor
  · rintro ⟨hC, hCD⟩
    refine ⟨hCD, fun hCV => Special.not_commuting hR hC.2 ?_⟩
    exact (commuting_sup_self hR hA hD).mono le_sup_left hCV.2
  · rintro ⟨hCD, hCV⟩
    have hCR : C ∈ R := hCD.1.1
    have hCA : C ∉ lambdaSet R A := fun hCA => hCV ⟨hCR, le_line h hH hA hD hA le_sup_left
      hD.1.1 le_sup_right hD.1.2.1.symm hCR hCA.1.2.2.symm hCD.1.2.2.symm⟩
    have hne : C ≠ A := fun e => hCV ⟨hCR, e ▸ le_sup_left⟩
    exact ⟨⟨hCR, (special_of_mem_lambdaSet h hH hA hD hCD hCA hne).1⟩, hCD⟩

theorem ncard_setOf_psiSet_le_sup {P Q : Subgroup G} (hP : P ∈ R) (hQ : Q ∈ lambdaSet R P) :
    {B | B ∈ psiSet R P ∧ ⁅P, B⁆ ≤ P ⊔ Q ∧ ⁅P, B⁆ ≠ P}.ncard =
      Nat.card P * ((lambdaSet R P).ncard - Nat.card P) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have h1 := ncard_mul_eq_ncard_mul (s := {B | B ∈ psiSet R P ∧ ⁅P, B⁆ ≤ P ⊔ Q ∧ ⁅P, B⁆ ≠ P})
    (t := pointsOn R (P ⊔ Q) \ {P}) (Set.toFinite _) (Set.toFinite _)
    (fun B Q' => ⁅P, B⁆ = Q') (m := 1) (n := (lambdaSet R P).ncard - Nat.card P) ?_ ?_
  · have hpts : (pointsOn R (P ⊔ Q) \ {P}).ncard = Nat.card P := by
      have hPm : P ∈ pointsOn R (P ⊔ Q) := ⟨hP, le_sup_left⟩
      rw [Set.ncard_sdiff_singleton_of_mem hPm, ncard_pointsOn h hP hQ, Nat.add_sub_cancel]
    rw [hpts, mul_one] at h1
    exact h1
  · rintro B ⟨hB, hBle, hBne⟩
    rw [Set.ncard_eq_one]
    refine ⟨⁅P, B⁆, ?_⟩
    ext Q'
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, e⟩
      exact e.symm
    · rintro rfl
      exact ⟨⟨⟨hB.2.1, hBle⟩, hBne⟩, rfl⟩
  · rintro Q' ⟨⟨hQ'R, hQ'le⟩, hQ'P⟩
    have hQ'l : Q' ∈ lambdaSet R P :=
      (mem_lambdaSet_of_le_sup hR hiso hP hQ hP le_sup_left hQ'R hQ'le (Ne.symm hQ'P)).1
    have hline : P ⊔ Q' = P ⊔ Q :=
      (mem_lambdaSet_of_le_sup hR hiso hP hQ hP le_sup_left hQ'R hQ'le (Ne.symm hQ'P)).2
    rw [← ncard_lambdaSet_diff_pointsOn h hP hQ'l, ← setOf_psiSet_lambdaSet h hH hP hQ'l]
    congr 1
    ext B
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hB, -, -⟩, e⟩
      refine ⟨hB, ?_⟩
      rw [← e]
      exact mem_lambdaSet_comm hB.1 (commutator_mem_lambdaSet h hP hB.1 hB.2).2
    · rintro ⟨hB, hBQ'⟩
      have e : Q' = ⁅P, B⁆ := eq_commutator h hP hB.1 hB.2 hQ'l (mem_lambdaSet_comm hQ'R hBQ')
      refine ⟨⟨hB, ?_, ?_⟩, e.symm⟩
      · rw [← e, ← hline]
        exact le_sup_right
      · rw [← e]
        exact hQ'P

theorem commutator_mem_omegaSet {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀)
    (hPP' : ¬ P' ≤ A ⊔ P) : ⁅A₀, P'⁆ ∈ omegaSet R P := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hPA : P ∈ lambdaSet R A := hP.1
  have hP'A : P' ∈ lambdaSet R A := hP'.1
  have hPR : P ∈ R := hPA.1.1
  have hP'R : P' ∈ R := hP'A.1.1
  have hA₀R : A₀ ∈ R := hA₀.1
  have hop : Opposite A A₀ := hA₀.2
  obtain ⟨hQA₀, hQP⟩ := commutator_mem_lambdaSet h hA₀R hPR hP.2.2
  obtain ⟨hQ'A₀, hQ'P'⟩ := commutator_mem_lambdaSet h hA₀R hP'R hP'.2.2
  have hQR : ⁅A₀, P⁆ ∈ R := hP.2.2.1
  have hQ'R : ⁅A₀, P'⁆ ∈ R := hP'.2.2.1
  have hfar : ∀ {X : Subgroup G}, X ∈ lambdaSet R A₀ → X ∉ lambdaSet R A ∧ X ≠ A := by
    intro X hX
    refine ⟨fun hXA => notMem_lambdaSet_of_opposite h hA hop hXA hX, ?_⟩
    rintro rfl
    exact hop.not_commuting (hR.ne_bot X hX.1.1) hX.1.2.2.symm
  have hPP'ne : P ≠ P' := fun e => hPP' (e ▸ le_sup_right)
  have hPP'nc : ¬ Commuting P P' := fun hc => hPP' (le_line h hH hA hPA hA le_sup_left hPR
    le_sup_right hPA.1.2.1.symm hP'R hP'A.1.2.2.symm hc.symm)
  have hset := setOf_omegaSet_lambdaSet h hH hPR (show A₀ ∈ psiSet R P from ⟨hA₀R, hP.2.2.symm⟩)
  have hmem : ⁅A₀, P'⁆ ∈ lambdaSet R A₀ \ pointsOn R (A₀ ⊔ ⁅P, A₀⁆) := by
    refine ⟨hQ'A₀, fun hle => ?_⟩
    rw [Subgroup.commutator_comm] at hle
    by_cases hQQ' : ⁅A₀, P'⁆ = ⁅A₀, P⁆
    ·
      have hsp := special_of_mem_lambdaSet_of_mem_lambdaSet h hA hPA hP'A hPP'nc
      have hCB : ⁅A₀, P⁆ ∈ lambdaSet R P' := hQQ' ▸ hQ'P'
      have e := eq_commutator h hPR hP'R hsp.1 hQP hCB
      rw [hsp.2] at e
      exact (hfar hQA₀).2 e
    ·
      have hQQ'l : ⁅A₀, P'⁆ ∈ lambdaSet R ⁅A₀, P⁆ :=
        (mem_lambdaSet_of_le_sup hR hiso hA₀R hQA₀ hQR le_sup_right hQ'R hle.2
          (Ne.symm hQQ')).1
      exact false_of_pentagon h hH hA hPA hQP hQQ'l
        (mem_lambdaSet_comm hP'R hQ'P') (mem_lambdaSet_comm hA hP'A) (hfar hQA₀).1
        (hfar hQA₀).2 (hfar hQ'A₀).1 (hfar hQ'A₀).2 hPP'ne
  rw [← hset] at hmem
  exact hmem.1

theorem shortRoot_moufang_of (hT : MTransitive R) {A A₀ P : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) (hP : P ∈ lambdaStar R A A₀) :
    Commuting (Subgroup.centralizer ((A ⊔ A₀ : Subgroup G) : Set G) ⊓ M R P)
        (Subgroup.centralizer ((A ⊔ A₀ : Subgroup G) : Set G) ⊓ M R P) ∧
      (∀ u ∈ Subgroup.centralizer ((A ⊔ A₀ : Subgroup G) : Set G) ⊓ M R P, u * u = 1) ∧
      ∀ V ∈ linesThrough R A, ∀ W ∈ linesThrough R A, ¬ P ≤ V → ¬ P ≤ W →
        ∃! u : ↥(Subgroup.centralizer ((A ⊔ A₀ : Subgroup G) : Set G) ⊓ M R P),
          conjSub V (u : G) = W := by
  classical
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  set U := Subgroup.centralizer ((A ⊔ A₀ : Subgroup G) : Set G) ⊓ M R P with hU
  set K₀ := M R P ⊓ Subgroup.normalizer (A₀ : Set G) with hK₀
  have hPA : P ∈ lambdaSet R A := hP.1
  have hPR : P ∈ R := hPA.1.1
  have hsp : Special R A₀ P := hP.2.2
  have hA₀R : A₀ ∈ R := hA₀.1
  have hop : Opposite A A₀ := hA₀.2
  have hAP : A ∈ lambdaSet R P := mem_lambdaSet_comm hA hPA
  obtain ⟨hQA₀, hQP⟩ := commutator_mem_lambdaSet h hA₀R hPR hsp
  have hQR : ⁅A₀, P⁆ ∈ R := hsp.1
  obtain ⟨-, -, hMM, -, -⟩ := Q_eq_M h hPR
  have hPN : ∀ p ∈ P, conjSub A₀ p = A₀ → p = 1 := fun p hp e => by
    by_contra hp1
    exact Sec3.conjSub_ne_of_special hR hiso hPR hA₀R hsp.symm hp hp1 e
  have hK₀N : ∀ k ∈ K₀, conjSub A₀ k = A₀ := fun k hk => conjSub_eq_self_iff.2 hk.2
  have hK₀comm : ∀ k ∈ K₀, ∀ k' ∈ K₀, Commute k k' := by
    intro k hk k' hk'
    have h1 : ⁅k, k'⁆ ∈ P := hMM ▸ Subgroup.commutator_mem_commutator hk.1 hk'.1
    have h2 : ⁅k, k'⁆ ∈ K₀ := by
      rw [commutatorElement_def]
      exact K₀.mul_mem (K₀.mul_mem (K₀.mul_mem hk hk') (K₀.inv_mem hk)) (K₀.inv_mem hk')
    exact commutatorElement_eq_one_iff_commute.mp (hPN _ h1 (hK₀N _ h2))
  have hK₀sq : ∀ k ∈ K₀, k * k = 1 := fun k hk =>
    hPN _ (sq_mem_of_mem_M h hPR hk.1) (hK₀N _ (K₀.mul_mem hk hk))
  have hUA : ∀ u ∈ U, conjSub A u = A := fun u hu => conjSub_of_forall_commute fun x hx =>
    (Subgroup.mem_centralizer_iff.1 hu.1 x (Subgroup.mem_sup_left hx)).symm
  have hUA₀ : ∀ u ∈ U, conjSub A₀ u = A₀ := fun u hu => conjSub_of_forall_commute fun x hx =>
    (Subgroup.mem_centralizer_iff.1 hu.1 x (Subgroup.mem_sup_right hx)).symm
  have hUK : U ≤ K₀ := fun u hu => ⟨hu.2, conjSub_eq_self_iff.1 (hUA₀ u hu)⟩
  refine ⟨fun u hu u' hu' => hK₀comm u (hUK hu) u' (hUK hu'), fun u hu => hK₀sq u (hUK hu), ?_⟩
  intro V hV W hW hPV hPW
  have hUlines : ∀ u ∈ U, ∀ X ∈ linesThrough R A, conjSub X u ∈ linesThrough R A := by
    intro u hu X hX
    refine ⟨IsLine.conjSub hR hX.1 u, ?_⟩
    rw [← hUA u hu]
    exact Subgroup.map_mono hX.2
  have hUP : ∀ u ∈ U, conjSub P u = P := fun u hu =>
    conjSub_eq_self_iff.2 ((isPGroup_M hR hPR).2.1 hu.2)
  have hUnotP : ∀ u ∈ U, ∀ X : Subgroup G, ¬ P ≤ X → ¬ P ≤ conjSub X u := by
    intro u hu X hPX hle
    apply hPX
    have := Subgroup.map_mono (f := (MulAut.conj (u : G)⁻¹).toMonoidHom) hle
    change conjSub P u⁻¹ ≤ conjSub (conjSub X u) u⁻¹ at this
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one,
      conjSub_eq_self_iff.2 (Subgroup.inv_mem _ (conjSub_eq_self_iff.1 (hUP u hu)))] at this
  have hsemi : ∀ u ∈ U, ∀ X ∈ linesThrough R A, ¬ P ≤ X → conjSub X u = X → u = 1 := by
    intro u hu X hX hPX hXu
    obtain ⟨D, hD, rfl⟩ := (mem_linesThrough_iff h hA).1 hX
    obtain ⟨P', ⟨hP'R, hP'X, hP'ψ⟩, huniq⟩ :=
      existsUnique_mem_psiSet_of_le hR hiso hA hA₀R hop hD
    have hP'A : P' ∈ lambdaSet R A := by
      refine (mem_lambdaSet_of_le_sup hR hiso hA hD hA le_sup_left hP'R hP'X ?_).1
      rintro rfl
      exact Special.not_opposite hR hA₀R hP'ψ.2 hop.symm
    have hP'u : conjSub P' u = P' := huniq _ ⟨hR.conjSub_mem hP'R u,
      hXu ▸ Subgroup.map_mono hP'X, hR.conjSub_mem hP'R u, by
        have := Sec3.special_conjSub hR hP'ψ.2 u
        rwa [hUA₀ u hu] at this⟩
    have hP'P : ¬ P' ≤ A ⊔ P := fun hle => hPX (by
      rw [eq_of_le_of_le h hA hD hA hPA hA hP'R hP'A.1.2.1.symm le_sup_left hP'X le_sup_left hle]
      exact le_sup_right)
    have hQ'Ω := commutator_mem_omegaSet h hH hA hA₀ hP ⟨hP'A, hP'ψ⟩ hP'P
    refine eq_one_of_mem_M_of_conjSub_eq h hPR hQ'Ω hu.2 ?_
    change Subgroup.map _ ⁅A₀, P'⁆ = _
    rw [Subgroup.map_commutator]
    exact congrArg₂ _ (hUA₀ u hu) hP'u
  set L := (linesThrough R A).ncard with hL
  set q := Nat.card A with hq
  have hcardP : Nat.card P = q := hR.card_eq hPR hA
  have hLP : (linesThrough R P).ncard = L := ncard_linesThrough_eq h hA hPR
  have hΛP : (lambdaSet R P).ncard = L * q := by rw [ncard_lambdaSet h hPR, hLP, hcardP]
  have hqpos : 0 < q := Nat.card_pos
  set 𝓦 := {X | X ∈ linesThrough R A ∧ ¬ P ≤ X} with h𝓦
  have h𝓦eq : 𝓦 = linesThrough R A \ {A ⊔ P} := by
    ext X
    constructor
    · rintro ⟨hX, hPX⟩
      exact ⟨hX, fun e => hPX ((Set.mem_singleton_iff.1 e) ▸ le_sup_right)⟩
    · rintro ⟨hX, hXV⟩
      refine ⟨hX, fun hPX => hXV ?_⟩
      obtain ⟨D, hD, rfl⟩ := (mem_linesThrough_iff h hA).1 hX
      exact (eq_of_le_of_le h hA hD hA hPA hA hPR hPA.1.2.1.symm le_sup_left hPX le_sup_left
        le_sup_right)
  have hV₀ : A ⊔ P ∈ linesThrough R A := (mem_linesThrough_iff h hA).2 ⟨P, hPA, rfl⟩
  have h𝓦card : 𝓦.ncard = L - 1 := by
    rw [h𝓦eq, Set.ncard_sdiff_singleton_of_mem hV₀]
  have hL2 : 2 ≤ L := by
    have : 0 < 𝓦.ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨V, hV, hPV⟩
    omega
  have horbU : ∀ X ∈ 𝓦, Function.Injective fun u : U => conjSub X (u : G) := by
    intro X hX u u' e
    have e' : conjSub X ((u' : G)⁻¹ * u) = X := by
      change conjSub X u = conjSub X u' at e
      rw [conjSub_mul, e, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have := hsemi _ (U.mul_mem (U.inv_mem u'.2) u.2) X hX.1 hX.2 e'
    exact (Subtype.ext (inv_mul_eq_one.mp this)).symm
  have hmaps : ∀ X ∈ 𝓦, ∀ u : U, conjSub X (u : G) ∈ 𝓦 := fun X hX u =>
    ⟨hUlines u u.2 X hX.1, hUnotP u u.2 X hX.2⟩
  have hUle : Nat.card U ≤ L - 1 := by
    rw [← h𝓦card, ← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective (fun u => ⟨_, hmaps V ⟨hV, hPV⟩ u⟩)
      fun u u' e => horbU V ⟨hV, hPV⟩ (congrArg Subtype.val e)
  have hK₀ge : (L - 1) * q ≤ Nat.card K₀ := by
    let : MulAction (M R P) (Subgroup G) :=
      { smul := fun m B => conjSub B (m : G)
        one_smul := fun B => conjSub_one B
        mul_smul := fun m m' B => conjSub_mul B m m' }
    have h1 := (MulAction.stabilizer (M R P) A₀).card_mul_index
    rw [MulAction.index_stabilizer] at h1
    have hstab : Nat.card (MulAction.stabilizer (M R P) A₀) = Nat.card K₀ :=
      Nat.card_congr
        { toFun := fun m => ⟨m.1.1, m.1.2, conjSub_eq_self_iff.1 m.2⟩
          invFun := fun k => ⟨⟨k.1, k.2.1⟩, conjSub_eq_self_iff.2 k.2.2⟩
          left_inv := fun m => rfl
          right_inv := fun k => rfl }
    have horb : MulAction.orbit (M R P) A₀ ⊆
        {B | B ∈ psiSet R P ∧ ⁅P, B⁆ ≤ P ⊔ ⁅A₀, P⁆ ∧ ⁅P, B⁆ ≠ P} := by
      rintro _ ⟨m, rfl⟩
      have hmP : conjSub P (m : G) = P := conjSub_eq_self_iff.2 ((isPGroup_M hR hPR).2.1 m.2)
      have hsp' := Sec3.special_conjSub hR hsp.symm (m : G)
      rw [hmP] at hsp'
      have hcomm : ⁅P, conjSub A₀ (m : G)⁆ = conjSub ⁅P, A₀⁆ (m : G) := by
        change _ = Subgroup.map _ _
        rw [Subgroup.map_commutator]
        exact congrArg₂ _ hmP.symm rfl
      refine ⟨⟨hR.conjSub_mem hA₀R m, hsp'⟩, ?_, ?_⟩
      · change ⁅P, conjSub A₀ (m : G)⁆ ≤ _
        rw [hcomm, ← conjSub_sup_eq_of_mem_M h hPR hQP m.2, Subgroup.commutator_comm]
        exact Subgroup.map_mono le_sup_right
      · change ⁅P, conjSub A₀ (m : G)⁆ ≠ P
        rw [hcomm]
        intro e
        apply hQP.1.2.1
        rw [Subgroup.commutator_comm]
        have := congrArg (fun H => conjSub H (m : G)⁻¹) e
        rwa [← conjSub_mul, inv_mul_cancel, conjSub_one, conjSub_eq_self_iff.2
          (Subgroup.inv_mem _ (conjSub_eq_self_iff.1 hmP))] at this
    have hY := ncard_setOf_psiSet_le_sup h hH hPR hQP
    rw [hΛP, hcardP] at hY
    have horbcard := Set.ncard_le_ncard horb (Set.toFinite _)
    rw [hY] at horbcard
    have hMP : Nat.card (M R P) = (L - 1) ^ 2 * q ^ 3 := by
      rw [card_M_eq h hT hPR, ncard_omegaSet h hH hPR hcardP hLP]
    rw [hMP, hstab] at h1
    have hsub : L * q - q = (L - 1) * q := (Nat.sub_one_mul L q).symm
    rw [hsub] at horbcard
    have key : (L - 1) ^ 2 * q ^ 3 ≤ Nat.card K₀ * (q * ((L - 1) * q)) :=
      h1 ▸ Nat.mul_le_mul_left _ horbcard
    have hpos : 0 < (L - 1) * q * q := Nat.mul_pos (Nat.mul_pos (by omega) hqpos) hqpos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc (L - 1) * q * ((L - 1) * q * q) = (L - 1) ^ 2 * q ^ 3 := by ring
      _ ≤ Nat.card K₀ * (q * ((L - 1) * q)) := key
      _ = Nat.card K₀ * ((L - 1) * q * q) := by ring
  have hQK : ⁅A₀, P⁆ ≤ K₀ := fun x hx => ⟨QD.le_M hQP hx,
    conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun y hy => (hQA₀.1.2.2 y hy x hx).symm)⟩
  have hQA : ¬ Commuting ⁅A₀, P⁆ A := fun hc => notMem_lambdaSet_of_opposite h hA hop
    (mem_lambdaSet_of_commuting hH hA hQR (fun e => hop.not_commuting (hR.ne_bot A hA)
      (e ▸ hQA₀.1.2.2.symm)) hc.symm) hQA₀
  have hsQA := special_of_mem_lambdaSet_of_mem_lambdaSet h hPR hQP hAP hQA
  have hpts : ∀ k ∈ M R P, conjSub A k ∈ pointsOn R (A ⊔ P) \ {P} := by
    intro k hk
    have hkP : conjSub P k = P := conjSub_eq_self_iff.2 ((isPGroup_M hR hPR).2.1 hk)
    refine ⟨⟨hR.conjSub_mem hA k, ?_⟩, fun e => hPA.1.2.1 ?_⟩
    · rw [sup_comm, ← conjSub_sup_eq_of_mem_M h hPR hAP hk]
      exact Subgroup.map_mono le_sup_right
    · have := congrArg (fun H => conjSub H k⁻¹) (Set.mem_singleton_iff.1 e)
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one, conjSub_eq_self_iff.2
        (Subgroup.inv_mem _ (conjSub_eq_self_iff.1 hkP))] at this
      exact this.symm
  have hQsurj : ∀ B ∈ pointsOn R (A ⊔ P) \ {P}, ∃ x ∈ ⁅A₀, P⁆, conjSub A x = B := by
    have hinj : Function.Injective fun x : ↥⁅A₀, P⁆ => conjSub A (x : G) := by
      intro x x' e
      by_contra hne
      have e' : conjSub A ((x' : G)⁻¹ * x) = A := by
        change conjSub A x = conjSub A x' at e
        rw [conjSub_mul, e, ← conjSub_mul, inv_mul_cancel, conjSub_one]
      have h1 : (x' : G)⁻¹ * x ≠ 1 := fun h1 => hne (Subtype.ext (inv_mul_eq_one.mp h1)).symm
      exact Sec3.conjSub_ne_of_special hR hiso hQR hA hsQA.1
        ((⁅A₀, P⁆).mul_mem ((⁅A₀, P⁆).inv_mem x'.2) x.2) h1 e'
    have hrange : Set.range (fun x : ↥⁅A₀, P⁆ => conjSub A (x : G)) =
        pointsOn R (A ⊔ P) \ {P} := by
      refine Set.eq_of_subset_of_ncard_le (Set.range_subset_iff.2 fun x =>
        hpts x (QD.le_M hQP x.2)) ?_ (Set.toFinite _)
      have hPm : P ∈ pointsOn R (A ⊔ P) := ⟨hPR, le_sup_right⟩
      rw [Set.ncard_sdiff_singleton_of_mem hPm, ncard_pointsOn h hA hPA, Nat.add_sub_cancel,
        ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj, hR.card_eq hQR hA]
    intro B hB
    rw [← hrange] at hB
    obtain ⟨x, rfl⟩ := hB
    exact ⟨x, x.2, rfl⟩
  have hK₀le : Nat.card K₀ ≤ q * Nat.card U := by
    rw [hq, ← hR.card_eq hQR hA, ← Nat.card_prod]
    refine Nat.card_le_card_of_surjective
      (fun p : ↥⁅A₀, P⁆ × ↥U => ⟨p.1 * p.2, K₀.mul_mem (hQK p.1.2) (hUK p.2.2)⟩) ?_
    rintro ⟨k, hk⟩
    obtain ⟨x, hx, hxk⟩ := hQsurj _ (hpts k hk.1)
    set y := x⁻¹ * k with hy
    have hyK : y ∈ K₀ := K₀.mul_mem (K₀.inv_mem (hQK hx)) hk
    have hyA : conjSub A y = A := by
      rw [hy, conjSub_mul, ← hxk, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have hyCA := mem_centralizer_of_mem_M_of_conjSub_eq h hPR hAP hyK.1 hyA
    have hyCA₀ := mem_centralizer_of_opposite hop hyCA (hK₀N y hyK)
    have hyU : y ∈ U := by
      refine Subgroup.mem_inf.2 ⟨?_, hyK.1⟩
      have hle : A ⊔ A₀ ≤ Subgroup.centralizer {y} := sup_le
        (fun a ha => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hyCA a ha))
        (fun a ha => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hyCA₀ a ha))
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hz))
    refine ⟨⟨⟨x, hx⟩, ⟨y, hyU⟩⟩, Subtype.ext ?_⟩
    change x * (x⁻¹ * k) = k
    group
  have hUcard : Nat.card U = L - 1 := by
    refine le_antisymm hUle ?_
    have := hK₀ge.trans hK₀le
    rw [mul_comm] at this
    exact Nat.le_of_mul_le_mul_left this hqpos
  have hbij : Set.range (fun u : U => conjSub V (u : G)) = 𝓦 := by
    refine Set.eq_of_subset_of_ncard_le (Set.range_subset_iff.2 (hmaps V ⟨hV, hPV⟩)) ?_
      (Set.toFinite _)
    rw [h𝓦card, ← Nat.card_coe_set_eq, Nat.card_range_of_injective (horbU V ⟨hV, hPV⟩),
      hUcard]
  have hWr : W ∈ Set.range (fun u : U => conjSub V (u : G)) := hbij ▸ ⟨hW, hPW⟩
  obtain ⟨u, hu⟩ := hWr
  exact ⟨u, hu, fun u' hu' => horbU V ⟨hV, hPV⟩ (hu'.trans hu.symm)⟩

end Moufang

end CaseH

end CFSG.Timmesfeld.ARS
