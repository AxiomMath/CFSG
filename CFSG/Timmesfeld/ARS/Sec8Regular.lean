module

public import CFSG.Timmesfeld.ARS.QDClass

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem opposite_conjSub_of_opposite [Finite G] (hR : IsRootClass R) {A B : Subgroup G}
    (hA : A ∈ R) (hB : B ∈ R) (hAB : Opposite A B) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Opposite B (conjSub B a) := by
  have hBa : conjSub B a ∈ R := hR.conjSub_mem hB a
  have hne : B ≠ conjSub B a := fun e => ha1 (hAB.eq_one_of_conjSub_eq ha e.symm)
  have hsup : B ⊔ conjSub B a = B ⊔ A := by
    have := hAB.symm.sup_conjSub_eq (hR.mul_self B hB) (one_mem _) (Subgroup.mem_sup_right ha)
      (by rwa [conjSub_one])
    rwa [conjSub_one] at this
  rcases hR.rel B hB _ hBa hne with hc | ho | hs
  · exfalso
    have hab : Commuting (B ⊔ conjSub B a) (B ⊔ conjSub B a) :=
      Commuting.sup_left (Commuting.sup_right (hR.commuting_self hB) hc)
        (Commuting.sup_right hc.symm (hR.commuting_self hBa))
    rw [hsup] at hab
    exact hAB.not_commuting (hR.ne_bot A hA) (hab.mono le_sup_right le_sup_left)
  · exact ho
  · exfalso
    have hp := hs.isPGroup_sup hR hB hBa
    rw [hsup] at hp
    exact Sec3.not_opposite_of_isPGroup_sup hR hB hA hp hAB.symm

theorem commute_of_conjSub_eq_of_opposite {A B : Subgroup G} (hAB : Opposite A B) {m : G}
    (hmA : ∀ a ∈ A, Commute m a) (hmB : conjSub B m = B) {b : G} (hb : b ∈ B) :
    Commute m b := by
  rcases eq_or_ne b 1 with rfl | hb1
  · exact Commute.one_right m
  obtain ⟨a, ha, ha1, hab⟩ := hAB.2.2 b hb hb1
  have hAm : conjSub A m = A := conjSub_of_forall_commute hmA
  have hAm' : conjSub A m⁻¹ = A := conjSub_of_forall_commute fun x hx => (hmA x hx).inv_left
  have hb' : m * b * m⁻¹ ∈ B := hmB ▸ conj_mem_conjSub m hb
  have key : conjSub A (m * b * m⁻¹) = conjSub B a := by
    calc conjSub A (m * b * m⁻¹) = conjSub (conjSub (conjSub A m⁻¹) b) m := by
          rw [← conjSub_mul, ← conjSub_mul, mul_assoc]
      _ = conjSub (conjSub B a) m := by rw [hAm', ← hab]
      _ = conjSub (conjSub B m) a := by rw [← conjSub_mul, ← conjSub_mul, (hmA a ha).eq]
      _ = conjSub B a := by rw [hmB]
  obtain ⟨b₀, -, huniq⟩ := hAB.existsUnique_conjSub_eq ha ha1
  have h1 := huniq _ ⟨hb', key⟩
  have h2 := huniq _ ⟨hb, hab.symm⟩
  have heq : m * b * m⁻¹ = b := h1.trans h2.symm
  exact (mul_inv_eq_iff_eq_mul.1 heq)

theorem M_eq_gen_lambdaStar (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) : M R A = gen (lambdaStar R A A₀) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨-, -, hcomm, -, hP⟩ := Q_eq_M h hA
  set S := gen (lambdaStar R A A₀) with hS
  have hSM : S ≤ M R A := gen_le fun C hC => QD.le_M hC.1
  have hCS : ∀ C ∈ lambdaSet R A, C ≤ A ⊔ S := by
    intro C hC
    obtain ⟨C', ⟨hC'R, hC'le, hC'ψ⟩, -⟩ :=
      existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hC
    have hC'A : C' ≠ A := by
      rintro rfl
      exact Special.not_opposite hR hA₀.1 hC'ψ.2 hA₀.2.symm
    obtain ⟨hC'l, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hA hC hA le_sup_left hC'R hC'le
      hC'A.symm
    calc C ≤ A ⊔ C := le_sup_right
      _ = A ⊔ C' := hsup.symm
      _ ≤ A ⊔ S := sup_le_sup_left (le_gen (show C' ∈ lambdaStar R A A₀ from ⟨hC'l, hC'ψ⟩)) A
  have hMAS : M R A ≤ A ⊔ S := sup_le le_sup_left (iSup₂_le hCS)
  have hAS : A ≤ S := by
    by_contra hAS
    have hab : ∀ C₁ ∈ lambdaStar R A A₀, ∀ C₂ ∈ lambdaStar R A A₀, Commuting C₁ C₂ := by
      intro C₁ hC₁ C₂ hC₂
      by_contra hnc
      have hne : C₁ ≠ C₂ := fun e => hnc (e ▸ hR.commuting_self hC₁.1.1.1)
      have hC₁M := QD.le_M hC₁.1
      have hC₂M := QD.le_M hC₂.1
      have hsp : Special R C₁ C₂ := by
        rcases hR.rel C₁ hC₁.1.1.1 C₂ hC₂.1.1.1 hne with hc | ho | hs
        · exact absurd hc hnc
        · exact absurd ho (Sec3.not_opposite_of_isPGroup_sup hR hC₁.1.1.1 hC₂.1.1.1
            (hP.to_le (sup_le hC₁M hC₂M)) )
        · exact hs
      have hle : ⁅C₁, C₂⁆ ≤ A := hcomm ▸ Subgroup.commutator_mono hC₁M hC₂M
      have heq := QD.eq_of_le_of_mem hR hiso hsp.1 hA hle
      exact hAS (heq ▸ QD.commutator_le_of_le (le_gen hC₁) (le_gen hC₂))
    have hSab : Commuting S S := commuting_gen_of_pairwise hab
    have hMab : Commuting (M R A) (M R A) := by
      have hAM := QD.commuting_M hR hA
      have h1 : Commuting (A ⊔ S) (A ⊔ S) :=
        Commuting.sup_left (Commuting.sup_right (hR.commuting_self hA) (hAM.mono le_rfl hSM))
          (Commuting.sup_right (hAM.mono le_rfl hSM).symm hSab)
      exact h1.mono hMAS hMAS
    have := commuting_iff_commutator_eq_bot.1 hMab
    rw [hcomm] at this
    exact hR.ne_bot A hA this
  exact le_antisymm (hMAS.trans (sup_le hAS le_rfl)) hSM

theorem eq_one_of_mem_M_of_conjSub_eq (h : Hyp G R) {A B : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ omegaSet R A) {m : G} (hm : m ∈ M R A) (hmB : conjSub B m = B) : m = 1 := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨-, -, hcomm, -, -⟩ := Q_eq_M h hA
  have hBR : B ∈ R := hB.1
  have hAB : Opposite A B := hB.2
  have hAM := QD.commuting_M hR hA
  have hmA : ∀ a ∈ A, Commute m a := fun a ha => (hAM a ha m hm).symm
  have hmB' : ∀ b ∈ B, Commute m b := fun b hb => commute_of_conjSub_eq_of_opposite hAB hmA hmB hb
  by_cases hall : ∀ C ∈ lambdaStar R A B, ∀ c ∈ C, Commute m c
  ·
    have hle : gen (lambdaSet R A) ⊔ B ≤ Subgroup.centralizer {m} := by
      have hMc : M R A ≤ Subgroup.centralizer {m} := by
        rw [M_eq_gen_lambdaStar h hA hB]
        refine gen_le fun C hC c hc => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hall C hC c hc
      refine sup_le (gen_le fun C hC => (QD.le_M hC).trans hMc) fun b hb => ?_
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hmB' b hb
    rw [gen_lambdaSet_sup_eq_top h hA hB] at hle
    have hmZ : m ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g => by
      have := Subgroup.mem_centralizer_iff.1 (hle (Subgroup.mem_top g)) m rfl
      exact this.symm
    rw [h.center, Subgroup.mem_bot] at hmZ
    exact hmZ
  exfalso
  push Not at hall
  obtain ⟨C, ⟨hCl, hCψ⟩, c₀, hc₀, hmc₀⟩ := hall
  apply hmc₀
  have hCR : C ∈ R := hCl.1.1
  have hc₀1 : c₀ ≠ 1 := by
    rintro rfl
    exact hmc₀ (Commute.one_right m)
  set a := ⁅c₀, m⁆ with ha
  have haA : a ∈ A := hcomm ▸ Subgroup.commutator_mem_commutator (QD.le_M hCl hc₀) hm
  set m' := c₀ * m * c₀⁻¹ with hm'
  have hm'eq : m' = a * m := conj_eq_commutator_mul c₀ m
  have hcA : ∀ x ∈ A, Commute c₀ x := fun x hx => (hCl.1.2.2 x hx c₀ hc₀).symm
  have hm'B : ∀ y ∈ conjSub B c₀, Commute m' y := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hmB' y hy).map (MulAut.conj c₀).toMonoidHom
  have hBc : conjSub B c₀ ∈ lambdaSet R B :=
    QD.conjSub_mem_lambdaSet_of_special hR hiso hCR hBR hCψ.2.symm hc₀ hc₀1
  have hBcR : conjSub B c₀ ∈ R := hBc.1.1
  have hconj : conjSub (conjSub B c₀) m = conjSub (conjSub B c₀) a⁻¹ := by
    have hm_eq : m = a⁻¹ * m' := by rw [hm'eq, inv_mul_cancel_left]
    rw [hm_eq, conjSub_mul, conjSub_of_forall_commute hm'B]
  have hcommB : Commuting (conjSub (conjSub B c₀) a⁻¹) B := by
    have := hBc.1.2.2.symm.conjSub m
    rwa [hmB, hconj] at this
  by_cases ha1 : a = 1
  · exact commutatorElement_eq_one_iff_mul_comm.1 ha1 |>.symm
  exfalso
  have hABc : Opposite A (conjSub B c₀) := by
    have := Opposite.conj hAB c₀
    rwa [conjSub_of_forall_commute hcA] at this
  have hop := opposite_conjSub_of_opposite hR hA hBcR hABc (A.inv_mem haA) (inv_ne_one.2 ha1)
  exact not_commuting_of_opposite_of_mem_lambdaSet hR (hR.conjSub_mem hBcR _) hop.symm
    (mem_lambdaSet_comm hBR hBc) hcommB

end CFSG.Timmesfeld.ARS
