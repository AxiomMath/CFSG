module

public import CFSG.Timmesfeld.ARS.Sec8Transitive

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem levi_le_centralizer_right (A A₀ : Subgroup G) :
    levi R A A₀ ≤ Subgroup.centralizer (A₀ : Set G) :=
  iSup₂_le fun _ hB => commuting_iff_le_centralizer.1 hB.2.2.2

theorem levi_le_centralizer_left (A A₀ : Subgroup G) :
    levi R A A₀ ≤ Subgroup.centralizer (A : Set G) :=
  iSup₂_le fun _ hB => commuting_iff_le_centralizer.1 hB.1.2.2

theorem M_inf_levi_eq_bot (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) : M R A ⊓ levi R A A₀ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  refine eq_one_of_mem_M_of_conjSub_eq h hA hA₀ hx.1 (conjSub_of_forall_commute fun a ha => ?_)
  exact (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_right A A₀ hx.2) a ha).symm

theorem centralizer_eq_M_sup (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) :
    Subgroup.centralizer (A : Set G) =
      M R A ⊔ (Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (A₀ : Set G)) := by
  have := h.finite
  have hR := h.root
  have hMC : M R A ≤ Subgroup.centralizer (A : Set G) :=
    commuting_iff_le_centralizer.1 (QD.commuting_M hR hA)
  refine le_antisymm (fun g hg => ?_) (sup_le hMC inf_le_left)
  have hgA : ∀ a ∈ A, Commute g a := fun a ha => (Subgroup.mem_centralizer_iff.1 hg a ha).symm
  have hAg : conjSub A g = A := conjSub_of_forall_commute hgA
  have hA₀g : conjSub A₀ g ∈ omegaSet R A :=
    ⟨hR.conjSub_mem hA₀.1 g, hAg ▸ Opposite.conj hA₀.2 g⟩
  obtain ⟨m, hm, hmg⟩ := exists_mem_M_conjSub_eq_of_mem_omegaSet h hA hAne hA₀ hA₀g
  set k := m⁻¹ * g with hk
  have hkA : ∀ a ∈ A, Commute k a := fun a ha => by
    have h1 : Commute a m⁻¹ := Subgroup.mem_centralizer_iff.1 (hMC (Subgroup.inv_mem _ hm)) a ha
    exact h1.symm.mul_left (hgA a ha)
  have hkA₀ : conjSub A₀ k = A₀ := by
    rw [hk, conjSub_mul, ← hmg, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hkc : k ∈ Subgroup.centralizer (A₀ : Set G) := Subgroup.mem_centralizer_iff.2 fun b hb =>
    (commute_of_conjSub_eq_of_opposite hA₀.2 hkA hkA₀ hb).symm.eq
  have hkc' : k ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun a ha => (hkA a ha).symm.eq
  have : g = m * k := by rw [hk, mul_inv_cancel_left]
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right ⟨hkc', hkc⟩)

theorem centralizer_eq (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (h8 : Sec8 R A)
    (hA₀ : A₀ ∈ omegaSet R A) :
    Subgroup.centralizer (A : Set G) =
        M R A ⊔ (Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (A₀ : Set G)) ∧
      M R A ⊓ levi R A A₀ = ⊥ :=
  ⟨centralizer_eq_M_sup h hA h8.2 hA₀, M_inf_levi_eq_bot h hA hA₀⟩

theorem exists_mem_M_conjSub_mem_leviSet (h : Hyp G R) {A A₀ B : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hBs : B ∈ sigmaSet R A) (hBl : B ∉ lambdaSet R A) :
    ∃ m ∈ M R A, conjSub B m ∈ leviSet R A A₀ := by
  have := h.finite
  have hR := h.root
  have hBR : B ∈ R := hBs.1
  have hAI : A ∉ isolatedSet R B := by
    intro hI
    have hmem : A ∈ {X | X ∈ R ∧ X ≤ M R B} := ⟨hA, (Q_eq_M h hBR).1 ▸ QD.le_Q hI⟩
    rw [(Q_eq_M h hBR).2.1] at hmem
    rcases hmem with h1 | h1
    · exact hBs.2.1 h1.symm
    · exact hBl (mem_lambdaSet_comm hBR h1)
  obtain ⟨C, hCc, hAC⟩ := QD.exists_opposite_of_notMem_isolatedSet ⟨hA, hBs.2.2.symm⟩ hAI
  obtain ⟨m, hm, hmC⟩ := exists_mem_M_conjSub_eq_of_mem_omegaSet h hA hAne hA₀ ⟨hCc.1, hAC⟩
  have hmA : conjSub A m⁻¹ = A := conjSub_of_forall_commute fun a ha =>
    (QD.commuting_M hR hA a ha _ (Subgroup.inv_mem _ hm)).symm
  have hCm : conjSub C m⁻¹ = A₀ := by rw [← hmC, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  refine ⟨m⁻¹, Subgroup.inv_mem _ hm, ⟨hR.conjSub_mem hBR _, fun e => hBs.2.1 ?_, ?_⟩,
    hR.conjSub_mem hBR _, fun e => ?_, ?_⟩
  · rw [← hmA] at e
    exact RankOne.map_conj_inj.1 e
  · have := hBs.2.2.conjSub m⁻¹
    rwa [hmA] at this
  · rw [← hCm] at e
    have hBC : B = C := RankOne.map_conj_inj.1 e
    exact hAC.not_commuting (hR.ne_bot A hA) (hBC ▸ hBs.2.2)
  · have := hCc.2.conjSub m⁻¹
    rw [hCm] at this
    exact this.symm

theorem gen_centralSet_eq (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) :
    gen (centralSet R A) = M R A ⊔ levi R A A₀ := by
  have hR := h.root
  refine le_antisymm (gen_le fun B hB => ?_) (sup_le (sup_le
    (le_gen ⟨hA, hR.commuting_self hA⟩) (iSup₂_le fun B hB => le_gen ⟨hB.1.1, hB.1.2.2⟩))
    (iSup₂_le fun B hB => le_gen ⟨hB.1.1, hB.1.2.2⟩))
  by_cases hBA : B = A
  · exact hBA ▸ QD.le_M_self.trans le_sup_left
  by_cases hBl : B ∈ lambdaSet R A
  · exact (QD.le_M hBl).trans le_sup_left
  obtain ⟨m, hm, hmB⟩ :=
    exists_mem_M_conjSub_mem_leviSet h hA hAne hA₀ ⟨hB.1, hBA, hB.2⟩ hBl
  have hBV : conjSub B m ≤ levi R A A₀ :=
    le_iSup₂ (f := fun E (_ : E ∈ leviSet R A A₀) => E) _ hmB
  calc B = conjSub (conjSub B m) m⁻¹ := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    _ ≤ conjSub (levi R A A₀) m⁻¹ := Subgroup.map_mono hBV
    _ ≤ M R A ⊔ levi R A A₀ :=
      conjSub_le le_sup_right (Subgroup.mem_sup_left (Subgroup.inv_mem _ hm))

end CFSG.Timmesfeld.ARS
