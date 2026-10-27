module

public import CFSG.Milestones.ASVolI.H13

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.ChH

theorem exists_equiv_cocode {d : ℕ} (hd : d ≠ 22) {a b : Fin 24} {Γ : Subgroup S24}
    (hΓ : Γ ≤ AutPerm) {V : Type*} [CommGroup V] {ρ : ↥Γ →* MulAut V}
    (h : IsMathModule false d a b Γ ρ) :
    ∃ e : V ≃* W11, ∀ (γ : ↥Γ) (v : V), e (ρ γ v) = rho11 Γ hΓ γ (e v) := by
  obtain ⟨β, hβ⟩ := h
  let D : Subgroup (G6.PermMod 24) :=
    if d = 22 then golayC ⊔ Subgroup.zpowers (pairVec a b) else golayC
  have hD : D = golayC := if_neg hd
  have hn : ∀ m, m ∈ (G6.coreMod 24 : Subgroup (G6.PermMod 24)) ↔
      G6.permAct 24 (1⁻¹) m ∈ G6.coreMod 24 := by
    intro m; simp
  have hdD : ∀ m, m ∈ D ↔ G6.permAct 24 (1⁻¹) m ∈ golayC := by
    intro m; rw [hD]; simp
  have hβ' : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24) D) ρ.range ⊤ ⊥
      ρ.rangeRestrict β := hβ
  have hΓ' : ∀ σ ∈ Γ, Preserves (G6.coreMod 24) D σ := by
    intro σ hσ
    rw [hD]
    exact preserves_cocode (hΓ hσ)
  obtain ⟨e, he⟩ := (cocodeCoords.conj 1 hn hdD).exists_equiv hΓ' hβ'
  refine ⟨e, fun γ v => ?_⟩
  have h := he γ v
  change e ((((ρ.rangeRestrict) γ : ↥ρ.range) : MulAut V) v) =
      (cocodeCoords.conj 1 hn hdD).rhoHom γ (e v) at h
  rw [cocodeCoords.conj_rhoHom 1 hn hdD γ] at h
  simp only [MonoidHom.coe_rangeRestrict] at h
  have hγ1 : (1⁻¹ * (γ : S24) * 1 : S24) = γ := by group
  rw [hγ1] at h
  exact h

theorem exists_equiv_code {d : ℕ} (hd : d ≠ 22) {a b : Fin 24} {Γ : Subgroup S24}
    (hΓ : Γ ≤ AutPerm) {V : Type*} [CommGroup V] {ρ : ↥Γ →* MulAut V}
    (h : IsMathModule true d a b Γ ρ) :
    ∃ e : V ≃* W11, ∀ (γ : ↥Γ) (v : V), e (ρ γ v) = rhoC11 Γ hΓ γ (e v) := by
  obtain ⟨β, hβ⟩ := h
  let D : Subgroup (G6.PermMod 24) :=
    if d = 22 then golayC ⊓ pairKer a b else golayC
  have hD : D = golayC := if_neg hd
  have hn : ∀ m, m ∈ D ↔ G6.permAct 24 (1⁻¹) m ∈ golayC := by
    intro m; rw [hD]; simp
  have hdD : ∀ m, m ∈ (Subgroup.zpowers (G6.allOnes 24) : Subgroup (G6.PermMod 24)) ↔
      G6.permAct 24 (1⁻¹) m ∈ Subgroup.zpowers (G6.allOnes 24) := by
    intro m; simp
  have hβ' : RealizesBy (FFModel.golaySec Γ D (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β := hβ
  have hΓ' : ∀ σ ∈ Γ, Preserves D (Subgroup.zpowers (G6.allOnes 24)) σ := by
    intro σ hσ
    rw [hD]
    exact preserves_code (hΓ hσ)
  obtain ⟨e, he⟩ := (codeCoords.conj 1 hn hdD).exists_equiv hΓ' hβ'
  refine ⟨e, fun γ v => ?_⟩
  have h := he γ v
  change e ((((ρ.rangeRestrict) γ : ↥ρ.range) : MulAut V) v) =
      (codeCoords.conj 1 hn hdD).rhoHom γ (e v) at h
  rw [codeCoords.conj_rhoHom 1 hn hdD γ] at h
  simp only [MonoidHom.coe_rangeRestrict] at h
  have hγ1 : (1⁻¹ * (γ : S24) * 1 : S24) = γ := by group
  rw [hγ1] at h
  exact h

theorem exists_equiv_cocode22 {a b : Fin 24} (hab : a ≠ b) {τ : S24} (hτ : τ ∈ AutPerm)
    (h0 : τ 0 = a) (h1 : τ 1 = b) {Γ : Subgroup S24} (hΓ : Γ ≤ M2ab a b) {V : Type*}
    [CommGroup V] {ρ : ↥Γ →* MulAut V} (h : IsMathModule false 22 a b Γ ρ) :
    ∃ e : V ≃* W10, ∀ (γ : ↥Γ) (v : V) (hγ : τ⁻¹ * (γ : S24) * τ ∈ mog22plus),
      e (ρ γ v) = rho10 mog22plus le_rfl ⟨τ⁻¹ * (γ : S24) * τ, hγ⟩ (e v) := by
  obtain ⟨β, hβ⟩ := h
  have hβ' : RealizesBy
      (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β := by
    simpa [mathModel] using hβ
  have hn : ∀ m, m ∈ G6.coreMod 24 ↔ G6.permAct 24 τ⁻¹ m ∈ G6.coreMod 24 :=
    (preserves_iff_of_mem hτ).1
  have hC := (preserves_iff_of_mem hτ).2
  have hτ0' : τ⁻¹ a = 0 := by rw [← h0]; simp
  have hτ1' : τ⁻¹ b = 1 := by rw [← h1]; simp
  have hd : ∀ m, m ∈ golayC ⊔ Subgroup.zpowers (pairVec a b) ↔
      G6.permAct 24 τ⁻¹ m ∈ golayC ⊔ Subgroup.zpowers (pairVec 0 1) := by
    intro m
    refine (mem_sup_zpowers_iff' (pairVec_sq a b) m).trans
      (Iff.trans ?_ (mem_sup_zpowers_iff' (pairVec_sq 0 1) _).symm)
    rw [hC m, hC (m * pairVec a b), map_mul, permAct_pairVec, hτ0', hτ1']
  have hΓ' : ∀ σ ∈ Γ, Preserves (G6.coreMod 24)
      (golayC ⊔ Subgroup.zpowers (pairVec a b)) σ := by
    intro σ hσ
    obtain ⟨hσM, hcase⟩ := (CFSG.ASVolI.mem_M2ab_iff a b hab σ).1 (hΓ hσ)
    refine ⟨(preserves_cocode hσM).1, fun m hm => ?_⟩
    refine (mem_sup_zpowers_iff' (pairVec_sq a b) _).2 ?_
    rcases (mem_sup_zpowers_iff' (pairVec_sq a b) m).1 hm with hm | hm
    · exact Or.inl ((preserves_cocode hσM).2 _ hm)
    · right
      have hmem := (preserves_cocode hσM).2 _ hm
      rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rwa [map_mul, permAct_pairVec, ha, hb] at hmem
      · have hswap : pairVec b a = pairVec a b := by rw [pairVec, pairVec, mul_comm]
        rwa [map_mul, permAct_pairVec, ha, hb, hswap] at hmem
  obtain ⟨e, he⟩ := (cocode22Coords.conj τ hn hd).exists_equiv hΓ' hβ'
  refine ⟨e, fun γ v hγ => ?_⟩
  have h := he γ v
  change e ((((ρ.rangeRestrict) γ : ↥ρ.range) : MulAut V) v) =
      (cocode22Coords.conj τ hn hd).rhoHom γ (e v) at h
  rw [cocode22Coords.conj_rhoHom τ hn hd γ] at h
  exact h

theorem exists_equiv_code22 {a b : Fin 24} (hab : a ≠ b) {τ : S24} (hτ : τ ∈ AutPerm)
    (h0 : τ 0 = a) (h1 : τ 1 = b) {Γ : Subgroup S24} (hΓ : Γ ≤ M2ab a b) {V : Type*}
    [CommGroup V] {ρ : ↥Γ →* MulAut V} (h : IsMathModule true 22 a b Γ ρ) :
    ∃ e : V ≃* W10, ∀ (γ : ↥Γ) (v : V) (hγ : τ⁻¹ * (γ : S24) * τ ∈ mog22plus),
      e (ρ γ v) = rhoC10 mog22plus le_rfl ⟨τ⁻¹ * (γ : S24) * τ, hγ⟩ (e v) := by
  obtain ⟨β, hβ⟩ := h
  have hβ' : RealizesBy
      (FFModel.golaySec Γ (golayC ⊓ pairKer a b) (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β := by
    simpa [mathModel] using hβ
  have hC := (preserves_iff_of_mem hτ).2
  have hn : ∀ m, m ∈ golayC ⊓ pairKer a b ↔
      G6.permAct 24 τ⁻¹ m ∈ golayC ⊓ pairKer 0 1 := by
    intro m
    rw [mem_code22, Subgroup.mem_inf, mem_pairKer, hC m]
    refine and_congr Iff.rfl ?_
    rw [toAdd_permAct]
    simp only [permWord, Function.comp_apply, inv_inv, h0, h1]
  have hd := zpowers_allOnes_iff τ
  have hΓ' : ∀ σ ∈ Γ, Preserves (golayC ⊓ pairKer a b)
      (Subgroup.zpowers (G6.allOnes 24)) σ := by
    intro σ hσ
    obtain ⟨hσM, hcase⟩ := (CFSG.ASVolI.mem_M2ab_iff a b hab σ).1 (hΓ hσ)
    refine ⟨fun m hm => ?_, fun _ hm => permAct_mem_zpowers_allOnes σ hm⟩
    refine ⟨(preserves_cocode hσM).2 m hm.1, (mem_pairKer a b _).2 ?_⟩
    rw [toAdd_permAct]
    simp only [permWord, Function.comp_apply]
    rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have ha' : σ⁻¹ a = a := by rw [Equiv.Perm.inv_eq_iff_eq]; exact ha.symm
      have hb' : σ⁻¹ b = b := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hb.symm
      rw [ha', hb']
      exact (mem_pairKer a b m).1 hm.2
    · have ha' : σ⁻¹ a = b := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hb.symm
      have hb' : σ⁻¹ b = a := by rw [Equiv.Perm.inv_eq_iff_eq]; exact ha.symm
      rw [ha', hb', add_comm]
      exact (mem_pairKer a b m).1 hm.2
  obtain ⟨e, he⟩ := (code22Coords.conj τ hn hd).exists_equiv hΓ' hβ'
  refine ⟨e, fun γ v hγ => ?_⟩
  have h := he γ v
  change e ((((ρ.rangeRestrict) γ : ↥ρ.range) : MulAut V) v) =
      (code22Coords.conj τ hn hd).rhoHom γ (e v) at h
  rw [code22Coords.conj_rhoHom τ hn hd γ] at h
  exact h

end CFSG.Quasithin.AppendixH.H14
