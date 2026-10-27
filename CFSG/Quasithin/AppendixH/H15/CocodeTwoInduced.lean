module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoInducedGen

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

theorem induced_24 (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d = 24) :
    InducesOn (rImg ρ (MY Γ (Yd d a b O))) (fixV (rImg ρ (octFix O))) ⊥
      (Multiplicative (Fin 6 → ZMod 2)) (omegaN 6 qPlus6) := by
  obtain ⟨P⟩ := exists_phiData hM
  refine inducesOn_phi hM P (P.ker_ne22 hM (by omega)) (omegaN 6 qPlus6) ?_ ?_
  · intro m hm
    have hg : (m : S24) ∈ octStab O := (mem_mY_24 hM hd _).1 hm
    obtain ⟨σ, hσ, hact⟩ := exists_perm_of_octStab P.o_octad P.o_inj P.o_mem hg
    refine ⟨σ, hσ, hact, ?_⟩
    rw [← map_alternatingGroup_evActHom]
    exact Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
  · intro γ hγ
    rw [← map_alternatingGroup_evActHom] at hγ
    obtain ⟨σ, hσ, hσγ⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨g, hg, hact⟩ := exists_octStab_of_perm P.o_octad P.o_inj P.o_mem hσ
    have hgM : g ∈ M24g := (mem_octStab_iff (O := O)).1 hg |>.1
    have hΓ : Γ = M24g := by
      rcases mctx_cases hM with ⟨h24, hΓ⟩ | ⟨h23, _⟩ | ⟨h22, _, _⟩
      · exact hΓ
      · exact absurd (h23.symm.trans hd) (by norm_num)
      · exact absurd (h22.symm.trans hd) (by norm_num)
    refine ⟨⟨g, by rw [hΓ]; exact hgM⟩, ?_, σ, hσ, hact, hσγ⟩
    exact (mem_mY_24 hM hd g).2 hg

theorem induced_23 (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d = 23) :
    ∃ Γ₇ : Subgroup (MulAut (Multiplicative (Fin 6 → ZMod 2))), Γ₇ ≤ omegaN 6 qPlus6 ∧
      Nonempty (↥Γ₇ ≃* ↥(alternatingGroup (Fin 7))) ∧
      InducesOn (rImg ρ (MY Γ (Yd d a b O))) (fixV (rImg ρ (octFix O))) ⊥
        (Multiplicative (Fin 6 → ZMod 2)) Γ₇ := by
  obtain ⟨P⟩ := exists_phiData hM
  refine ⟨(alternatingGroup (Fin 8) ⊓
    MulAction.stabilizer (Equiv.Perm (Fin 8)) (0 : Fin 8)).map evActHom, ?_, ?_, ?_⟩
  · rw [← map_alternatingGroup_evActHom]
    exact Subgroup.map_mono inf_le_left
  · obtain ⟨e⟩ := nonempty_alt_stab_equiv (0 : Fin 8)
    exact ⟨(Subgroup.equivMapOfInjective
      (alternatingGroup (Fin 8) ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) (0 : Fin 8))
      evActHom evActHom_injective).symm.trans e⟩
  · refine inducesOn_phi hM P (P.ker_ne22 hM (by omega)) _ ?_ ?_
    · intro m hm
      obtain ⟨hg, hma⟩ := (mem_mY_23 hM hd (m : S24)).1 hm
      obtain ⟨σ, hσ, hact⟩ := exists_perm_of_octStab P.o_octad P.o_inj P.o_mem hg
      refine ⟨σ, hσ, hact, ?_⟩
      rw [Subgroup.mem_map]
      refine ⟨σ, Subgroup.mem_inf.mpr ⟨hσ, ?_⟩, rfl⟩
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      apply P.o_inj
      rw [P.o_zero]
      have h := hact 0
      rw [P.o_zero, hma] at h
      exact h.symm
    · intro γ hγ
      rw [Subgroup.mem_map] at hγ
      obtain ⟨σ, hσmem, hσγ⟩ := hγ
      obtain ⟨hσ, hσstab⟩ := Subgroup.mem_inf.mp hσmem
      have hσ0 : σ 0 = 0 := by
        rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at hσstab
        exact hσstab
      obtain ⟨g, hg, hact⟩ := exists_octStab_of_perm P.o_octad P.o_inj P.o_mem hσ
      have hgM : g ∈ M24g := (mem_octStab_iff (O := O)).1 hg |>.1
      have hga : g a = a := by
        have h := hact 0
        rw [P.o_zero] at h
        rw [hσ0, P.o_zero] at h
        exact h
      have hΓ : Γ = M23g a := by
        rcases mctx_cases hM with ⟨h24, _⟩ | ⟨h23, hΓ⟩ | ⟨h22, _, _⟩
        · exact absurd (h24.symm.trans hd) (by norm_num)
        · exact hΓ
        · exact absurd (h22.symm.trans hd) (by norm_num)
      refine ⟨⟨g, by rw [hΓ]; exact (mem_M23g_iff a g).2 ⟨hgM, hga⟩⟩, ?_, σ, hσ, hact, hσγ⟩
      exact (mem_mY_23 hM hd g).2 ⟨hg, hga⟩

theorem induced_22 (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d = 22) :
    ∃ (w : Multiplicative (Fin 6 → ZMod 2)) (π : Multiplicative (Fin 6 → ZMod 2) →* V),
      qPlus6 (Multiplicative.toAdd w) = 1 ∧ π.range = fixV (rImg ρ (octFix O)) ∧
      π.ker = Subgroup.zpowers w ∧
      (∀ g : ↥Γ, (g : S24) ∈ MY Γ (Yd d a b O) →
        ∃ γ ∈ omegaN 6 qPlus6, γ w = w ∧ ∀ x, π (γ x) = ρ g (π x)) ∧
      (Γ ≠ M22g a b → ∀ γ ∈ omegaN 6 qPlus6, γ w = w →
        ∃ g : ↥Γ, (g : S24) ∈ MY Γ (Yd d a b O) ∧ ∀ x, π (γ x) = ρ g (π x)) := by
  obtain ⟨P⟩ := exists_phiData hM
  set w : Multiplicative (Fin 6 → ZMod 2) := Multiplicative.ofAdd (evPair 0 1) with hw
  refine ⟨w, P.φ, ?_, P.range_eq_fixV hM, ?_, ?_, ?_⟩
  · rw [hw, toAdd_ofAdd]
    exact qPlus6_evPair (show (0 : Fin 8) ≠ 1 by decide)
  · rw [hw]
    exact P.ker_eq22 hM hd
  · intro g hg
    have hgoct : (g : S24) ∈ octStab O := mctx_mY_le hM hg
    obtain ⟨σ, hσ, hact⟩ := exists_perm_of_octStab P.o_octad P.o_inj P.o_mem hgoct
    have hM2 : Γ ≤ M2ab a b := by
      rcases mctx_cases hM with ⟨h24, _⟩ | ⟨h23, _⟩ | ⟨h22, _, h2⟩
      · exact absurd (h24.symm.trans hd) (by norm_num)
      · exact absurd (h23.symm.trans hd) (by norm_num)
      · exact h2
    have hdisj := (mem_M2ab_iff a b hM.cfg.ne (g : S24)).1 (hM2 g.2)
    have hne : σ 0 ≠ σ 1 := fun h => (show (0 : Fin 8) ≠ 1 by decide) (σ.injective h)
    have hpair : evPair (σ 0) (σ 1) = evPair 0 1 := by
      rw [evPair_eq_iff hne (show (0 : Fin 8) ≠ 1 by decide)]
      rcases hdisj.2 with ⟨hga, hgb⟩ | ⟨hga, hgb⟩
      · have e0 : σ 0 = 0 := by
          apply P.o_inj
          calc P.o (σ 0) = (g : S24) (P.o 0) := (hact 0).symm
            _ = (g : S24) a := by rw [P.o_zero]
            _ = a := hga
            _ = P.o 0 := P.o_zero.symm
        have e1 : σ 1 = 1 := by
          apply P.o_inj
          calc P.o (σ 1) = (g : S24) (P.o 1) := (hact 1).symm
            _ = (g : S24) b := by rw [P.o_one]
            _ = b := hgb
            _ = P.o 1 := P.o_one.symm
        rw [e0, e1]
      · have e0 : σ 0 = 1 := by
          apply P.o_inj
          calc P.o (σ 0) = (g : S24) (P.o 0) := (hact 0).symm
            _ = (g : S24) a := by rw [P.o_zero]
            _ = b := hga
            _ = P.o 1 := P.o_one.symm
        have e1 : σ 1 = 0 := by
          apply P.o_inj
          calc P.o (σ 1) = (g : S24) (P.o 1) := (hact 1).symm
            _ = (g : S24) b := by rw [P.o_one]
            _ = a := hgb
            _ = P.o 0 := P.o_zero.symm
        rw [e0, e1]
        exact Finset.pair_comm 1 0
    refine ⟨evActHom σ, ?_, ?_, ?_⟩
    · rw [← map_alternatingGroup_evActHom]
      exact Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
    · apply Multiplicative.toAdd.injective
      rw [evActHom_apply, evAct_evPair σ (show (0 : Fin 8) ≠ 1 by decide), hpair]
      rfl
    · intro x
      exact (P.equivariant hM hact x).symm
  · intro hneΓ γ hγ hγw
    rw [← map_alternatingGroup_evActHom] at hγ
    obtain ⟨σ, hσ, hσγ⟩ := Subgroup.mem_map.mp hγ
    have hγw' : evActHom σ w = w := by
      rw [hσγ]
      exact hγw
    have htoAdd : evAct σ (evPair 0 1) = evPair 0 1 := by
      have h := congrArg Multiplicative.toAdd hγw'
      simpa [hw, evActHom_apply] using h
    have hne : σ 0 ≠ σ 1 := fun h => (show (0 : Fin 8) ≠ 1 by decide) (σ.injective h)
    have hpair : evPair (σ 0) (σ 1) = evPair 0 1 := by
      rw [← evAct_evPair σ (show (0 : Fin 8) ≠ 1 by decide)]
      exact htoAdd
    have hset : ({σ 0, σ 1} : Finset (Fin 8)) = {0, 1} :=
      (evPair_eq_iff hne (show (0 : Fin 8) ≠ 1 by decide)).1 hpair
    have hswap : (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
      have hm0 : σ 0 ∈ ({0, 1} : Finset (Fin 8)) := by rw [← hset]; simp
      have hm1 : σ 1 ∈ ({0, 1} : Finset (Fin 8)) := by rw [← hset]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm0 hm1
      rcases hm0 with h0 | h0 <;> rcases hm1 with h1 | h1
      · exact absurd (h0.trans h1.symm) hne
      · exact Or.inl ⟨h0, h1⟩
      · exact Or.inr ⟨h0, h1⟩
      · exact absurd (h0.trans h1.symm) hne
    obtain ⟨g, hg, hact⟩ := exists_octStab_of_perm P.o_octad P.o_inj P.o_mem hσ
    have hgM : g ∈ M24g := (mem_octStab_iff (O := O)).1 hg |>.1
    have hga : g a = P.o (σ 0) := by
      have h := hact 0
      rwa [P.o_zero] at h
    have hgb : g b = P.o (σ 1) := by
      have h := hact 1
      rwa [P.o_one] at h
    have hcase : (g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a) := by
      rcases hswap with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · left
        exact ⟨by rw [hga, h0, P.o_zero], by rw [hgb, h1, P.o_one]⟩
      · right
        exact ⟨by rw [hga, h0, P.o_one], by rw [hgb, h1, P.o_zero]⟩
    have hgM2 : g ∈ M2ab a b := (mem_M2ab_iff a b hM.cfg.ne g).2 ⟨hgM, hcase⟩
    have hΓ : Γ = M2ab a b := by
      rcases mctx_cases hM with ⟨h24, _⟩ | ⟨h23, _⟩ | ⟨h22, h1, h2⟩
      · exact absurd (h24.symm.trans hd) (by norm_num)
      · exact absurd (h23.symm.trans hd) (by norm_num)
      · rcases eq_M22g_or_eq_M2ab hM.cfg.ne h1 h2 with h | h
        · exact absurd h hneΓ
        · exact h
    refine ⟨⟨g, by rw [hΓ]; exact hgM2⟩, ?_, ?_⟩
    · exact (mem_mY_22b hM hd hΓ g).2 ⟨hg, hcase⟩
    · intro x
      rw [← hσγ]
      exact (P.equivariant hM hact x).symm

end CFSG.ASVolI.AppH

