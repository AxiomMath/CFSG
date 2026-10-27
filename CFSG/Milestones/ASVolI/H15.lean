module

public import CFSG.Quasithin.AppendixH.H15.Vocab
public import CFSG.Quasithin.Background.RonanH15O2
public import CFSG.Quasithin.Background.RonanH15Plumb
public import CFSG.Quasithin.Background.RonanH15Stab
public import CFSG.Quasithin.Background.RonanH15Stab3
public import CFSG.Quasithin.Background.H158UMain
public import CFSG.Quasithin.Background.H156Main
public import CFSG.Quasithin.Background.H153Main
public import CFSG.Quasithin.Background.RonanH155Main
import CFSG.Quasithin.AppendixH.H15.CocodeTwoMain
import CFSG.Quasithin.AppendixH.H15.H157Main

public section

open scoped Pointwise Matrix commutatorElement MatrixGroups

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code

@[expose] def H_15_1 : Prop :=
  AllMCtx false (fun d => d = 22 ∨ d = 23 ∨ d = 24) fun d a b _ _ _ _ _ Γ V _ ρ β =>
    ((∀ v : V, IsO2Vec d a b Γ β v → v ≠ 1) ∧
      (∃ v₀ : V, IsO2Vec d a b Γ β v₀ ∧ ∀ v : V, IsO2Vec d a b Γ β v → ∃ g : ↥Γ, ρ g v₀ = v) ∧
      (∀ v : V, IsO2Vec d a b Γ β v → ∀ g : ↥Γ, IsO2Vec d a b Γ β (ρ g v)) ∧
      (∀ v : V, IsO2Vec d a b Γ β v →
        (d = 24 → Nonempty (↥(cenM ρ (Subgroup.zpowers v)) ≃*
          MulAut ↥CFSG.Blueprint.NativeSporadic.M22)) ∧
        (d = 23 → Nonempty (↥(cenM ρ (Subgroup.zpowers v)) ≃* ↥CFSG.Blueprint.NativeSporadic.M22)) ∧
        (d = 22 →
          (∃ j : Fin 24, j ≠ a ∧ j ≠ b ∧
            IsVecOf (mathModel false d a b Γ) β (pairVec a j) v ∧
            ∀ g : ↥Γ, (g ∈ cenM ρ (Subgroup.zpowers v) ↔ (g : S24) j = j)) ∧
          ∃ (K : Type) (_ : Field K), Nat.card K = 4 ∧
            (Γ = M22g a b → Nonempty (↥(cenM ρ (Subgroup.zpowers v)) ≃* PSL(3, K))) ∧
            (Γ ≠ M22g a b → ∃ N : Subgroup ↥(cenM ρ (Subgroup.zpowers v)), N.index = 2 ∧
              Nonempty (↥N ≃* PSL(3, K)))))) ∧
    (∀ v : V, IsO2Vec d a b Γ β v → commOn ⊤ (ρ.range ⊓ centSub (Subgroup.zpowers v)) = ⊤)

private theorem h15_1_pair_eq_iff (p q i j : Fin 24) :
    ({p, q} : Finset (Fin 24)) = {i, j} ↔ (p = i ∧ q = j) ∨ (p = j ∧ q = i) := by
  rw [← Finset.coe_inj]
  simp only [Finset.coe_insert, Finset.coe_singleton]
  exact Set.pair_eq_pair_iff

private theorem h15_1_mctx_cases {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)}
    {Tr S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type}
    [CommGroup V] {ρ : ↥Γ →* MulAut V}
    {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
      (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}
    (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    (d = 24 ∧ Γ = M24g) ∨ (d = 23 ∧ Γ = M23g a) ∨ (d = 22 ∧ M22g a b ≤ Γ ∧ Γ ≤ M2ab a b) := by
  rcases hM.d_mem with rfl | rfl | rfl
  · exact Or.inr (Or.inr ⟨rfl, by simpa [Ld] using hM.L_le, by simpa [AutLd] using hM.le_Aut⟩)
  · exact Or.inr (Or.inl ⟨rfl, le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut)
      (by simpa [Ld] using hM.L_le)⟩)
  · exact Or.inl ⟨rfl, le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut)
      (by simpa [Ld] using hM.L_le)⟩

private theorem h15_1_mem_cenM_iff {V : Type*} [CommGroup V] {Γ : Subgroup S24}
    (ρ : ↥Γ →* MulAut V) (v : V) (g : ↥Γ) :
    g ∈ cenM ρ (Subgroup.zpowers v) ↔ ρ g v = v := by
  unfold cenM
  rw [Subgroup.mem_comap]
  constructor
  · intro h
    exact h v (Subgroup.mem_zpowers v)
  · intro h u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    show ((ρ g : MulAut V) (v ^ k)) = v ^ k
    rw [map_zpow, h]

private theorem h15_1_commOn_eq {V : Type*} [CommGroup V] {A : Subgroup (MulAut V)}
    (h : Subgroup.closure {w | ∃ y ∈ A, ∃ u : V, w = y u * u⁻¹} = ⊤) : commOn ⊤ A = ⊤ := by
  have hset : {u | ∃ a ∈ A, ∃ w ∈ (⊤ : Subgroup V), u = a w * w⁻¹} =
      {w | ∃ y ∈ A, ∃ u : V, w = y u * u⁻¹} := by
    ext u
    simp
  unfold commOn
  rw [hset]
  exact h

section H151

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.RonanH15


theorem as_H_15_1 : H_15_1 := by
  intro d hd a b O Tr S B T₀ Γ V _ ρ β hM
  have hab : a ≠ b := hM.cfg.ne
  have hreal := hM.real
  rcases h15_1_mctx_cases hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hK, hP⟩
  ·
    have hreal' : RealizesBy (FFModel.golaySec M24g (G6.coreMod 24) golayC) ρ.range ⊤ ⊥
        ρ.rangeRestrict β := hreal
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rintro v ⟨i, j, hij, -, hv⟩
      exact vecOf_pair_ne_one_golay hreal' hij hv
    · obtain ⟨v₀, hv₀⟩ := exists_vecOf hreal' (e := pairVec 0 1) (pairVec_mem_coreMod 0 1)
      refine ⟨v₀, ⟨0, 1, by decide, Or.inl rfl, hv₀⟩, ?_⟩
      rintro v ⟨i, j, hij, -, hv⟩
      obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two i j hij
      refine ⟨⟨τ, hτ⟩, ?_⟩
      have h1 := vecOf_act_pair hreal' hv₀ ⟨τ, hτ⟩
      have h2 : ((⟨τ, hτ⟩ : ↥M24g) : Equiv.Perm (Fin 24)) 0 = i := hτ0
      have h3 : ((⟨τ, hτ⟩ : ↥M24g) : Equiv.Perm (Fin 24)) 1 = j := hτ1
      rw [h2, h3] at h1
      exact (vecOf_pair_eq_iff_golay hreal' hij hij h1 hv).2 rfl
    · rintro v ⟨i, j, hij, -, hv⟩ g
      exact ⟨(g : Equiv.Perm (Fin 24)) i, (g : Equiv.Perm (Fin 24)) j,
        (g : Equiv.Perm (Fin 24)).injective.ne hij, Or.inl rfl,
        vecOf_act_pair hreal' hv g⟩
    · rintro v ⟨i, j, hij, -, hv⟩
      refine ⟨fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      have hC : ∀ g : ↥M24g, g ∈ cenM ρ (Subgroup.zpowers v) ↔ (g : S24) ∈ M2ab i j := by
        intro g
        rw [h15_1_mem_cenM_iff, rho_eq_self_iff_golay hreal' hij hv g,
          h15_1_pair_eq_iff, mem_M2ab_iff i j hij]
        exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
      obtain ⟨e⟩ := nonempty_equiv_of_mem_iff (T := M2ab i j) (fun x hx => hx.1) hC
      obtain ⟨e'⟩ := nonempty_iso_M2ab i j hij
      exact ⟨MulEquiv.trans e e'⟩
    · have hMC : MathieuCocode24 ρ.range ⊤ ⊥ :=
        ⟨ρ.rangeRestrict, (realizesVia_iff _ _ _ _ _).2 ⟨β, hreal'⟩⟩
      rintro v ⟨i, j, hij, -, hv⟩
      have hO2 : IsCocodeO2 ρ.range v :=
        Or.inl ⟨ρ.rangeRestrict, β, hreal', i, j, hij, hv.choose_spec⟩
      exact h15_1_commOn_eq (closure_comm_eq_top_24 le_rfl hMC hO2)
  ·
    have hreal' : RealizesBy (FFModel.golaySec (M23g a) (G6.coreMod 24) golayC) ρ.range ⊤ ⊥
        ρ.rangeRestrict β := hreal
    have key : ∀ v : V, IsO2Vec 23 a b (M23g a) β v → ∃ j, a ≠ j ∧
        VecOf (FFModel.golaySec (M23g a) (G6.coreMod 24) golayC) β (pairVec a j) v := by
      rintro v ⟨i, j, hij, hc, hv⟩
      have hia : i = a := by
        rcases hc with h | ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd h (by decide)
        · exact h
        · exact absurd h (by decide)
      subst hia
      exact ⟨j, hij, hv⟩
    have mk : ∀ {j : Fin 24} {v : V}, a ≠ j →
        VecOf (FFModel.golaySec (M23g a) (G6.coreMod 24) golayC) β (pairVec a j) v →
        IsO2Vec 23 a b (M23g a) β v :=
      fun hne hv => ⟨a, _, hne, Or.inr (Or.inl ⟨rfl, rfl⟩), hv⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro v hv
      obtain ⟨j, hne, hvj⟩ := key v hv
      exact vecOf_pair_ne_one_golay hreal' hne hvj
    · have hne : a ≠ a + 1 := by
        intro h
        have := congrArg Fin.val h
        simp [Fin.val_add] at this
        omega
      obtain ⟨v₀, hv₀⟩ := exists_vecOf hreal' (e := pairVec a (a + 1)) (pairVec_mem_coreMod a (a + 1))
      refine ⟨v₀, mk hne hv₀, ?_⟩
      intro v hv
      obtain ⟨j, hj, hvj⟩ := key v hv
      obtain ⟨g, hg, hgj⟩ :=
        exists_mem_stab_maps (a := a) (j := a + 1) (j' := j) (Ne.symm hne) (Ne.symm hj)
      refine ⟨⟨g, hg⟩, ?_⟩
      have h1 := vecOf_act_pair hreal' hv₀ ⟨g, hg⟩
      have h2 : ((⟨g, hg⟩ : ↥(M23g a)) : Equiv.Perm (Fin 24)) a = a := (mem_stab_iff a g).1 hg.2
      have h3 : ((⟨g, hg⟩ : ↥(M23g a)) : Equiv.Perm (Fin 24)) (a + 1) = j := hgj
      rw [h2, h3] at h1
      exact (vecOf_pair_eq_iff_golay hreal' hj hj h1 hvj).2 rfl
    · intro v hv g
      obtain ⟨j, hj, hvj⟩ := key v hv
      have hga : ((g : ↥(M23g a)) : Equiv.Perm (Fin 24)) a = a := ((mem_M23g_iff a g).1 g.2).2
      have h1 := vecOf_act_pair hreal' hvj g
      rw [hga] at h1
      exact mk (fun h => hj ((g : Equiv.Perm (Fin 24)).injective (hga.trans h))) h1
    · intro v hv
      obtain ⟨j, hj, hvj⟩ := key v hv
      refine ⟨fun h => absurd h (by decide), fun _ => ?_, fun h => absurd h (by decide)⟩
      have hC : ∀ g : ↥(M23g a), g ∈ cenM ρ (Subgroup.zpowers v) ↔ (g : S24) ∈ M22g a j := by
        intro g
        have hga := (mem_M23g_iff a g).1 g.2
        rw [h15_1_mem_cenM_iff, rho_eq_self_iff_golay hreal' hj hvj g,
          h15_1_pair_eq_iff, mem_M22g_iff a j]
        constructor
        · rintro (⟨-, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨hga.1, hga.2, h2⟩
          · exact absurd (hga.2.symm.trans h1) hj
        · rintro ⟨-, -, h2⟩
          exact Or.inl ⟨hga.2, h2⟩
      obtain ⟨e⟩ := nonempty_equiv_of_mem_iff (T := M22g a j) (fun x hx => hx.1) hC
      obtain ⟨e'⟩ := nonempty_iso_M22g a j hj
      exact ⟨MulEquiv.trans e e'⟩
    · have hMC : MathieuCocode23 ρ.range ⊤ ⊥ :=
        ⟨a, ρ.rangeRestrict, (realizesVia_iff _ _ _ _ _).2 ⟨β, hreal'⟩⟩
      intro v hv
      obtain ⟨j, hj, hvj⟩ := key v hv
      have hO2 : IsCocodeO2 ρ.range v :=
        Or.inr (Or.inl ⟨a, ρ.rangeRestrict, β, hreal', j, hj, hvj.choose_spec⟩)
      exact h15_1_commOn_eq (closure_comm_eq_top_23 le_rfl hMC hO2)
  ·
    have hreal' : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24)
        (golayC ⊔ Subgroup.zpowers (pairVec a b))) ρ.range ⊤ ⊥ ρ.rangeRestrict β := hreal
    have hgrp : ∀ g : ↥Γ, ((g : S24) a = a ∧ (g : S24) b = b) ∨
        ((g : S24) a = b ∧ (g : S24) b = a) :=
      fun g => ((mem_M2ab_iff a b hab g).1 (hP g.2)).2
    have norm : ∀ {i j : Fin 24} {v : V}, (i = a ∨ i = b) → j ≠ a → j ≠ b →
        VecOf (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)))
          β (pairVec i j) v →
        VecOf (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)))
          β (pairVec a j) v := by
      intro i j v hi hja hjb hv
      rcases hi with rfl | rfl
      · exact hv
      · obtain ⟨w, hw⟩ := exists_vecOf hreal' (e := pairVec a j) (pairVec_mem_coreMod a j)
        have hvw : v = w := (vecOf_pair_eq_iff_sup hreal' hab (Ne.symm hjb) (Ne.symm hja) hv hw).2
          (Or.inr (symmDiff_pair_swap hab hja hjb))
        rw [hvw]
        exact hw
    have key : ∀ v : V, IsO2Vec 22 a b Γ β v → ∃ j, j ≠ a ∧ j ≠ b ∧
        VecOf (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)))
          β (pairVec a j) v := by
      rintro v ⟨i, j, hij, hc, hv⟩
      have hc' : (i = a ∨ i = b) ∧ j ≠ a ∧ j ≠ b := by
        rcases hc with h | ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact h
      exact ⟨j, hc'.2.1, hc'.2.2, norm hc'.1 hc'.2.1 hc'.2.2 hv⟩
    have mk : ∀ {j : Fin 24} {v : V}, j ≠ a → j ≠ b →
        VecOf (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)))
          β (pairVec a j) v → IsO2Vec 22 a b Γ β v :=
      fun hja hjb hv => ⟨a, _, Ne.symm hja, Or.inr (Or.inr ⟨rfl, Or.inl rfl, hja, hjb⟩), hv⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro v hv
      obtain ⟨j, hja, hjb, hvj⟩ := key v hv
      refine vecOf_pair_ne_one_sup hreal' hab (Ne.symm hja) (fun h => ?_) hvj
      have hj : j ∈ ({a, b} : Finset (Fin 24)) := h ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hj | hj
      · exact hja hj
      · exact hjb hj
    · obtain ⟨j₀, hj₀a, hj₀b⟩ := exists_ne_pair a b
      obtain ⟨v₀, hv₀⟩ := exists_vecOf hreal' (e := pairVec a j₀) (pairVec_mem_coreMod a j₀)
      refine ⟨v₀, mk hj₀a hj₀b hv₀, ?_⟩
      intro v hv
      obtain ⟨j, hja, hjb, hvj⟩ := key v hv
      obtain ⟨g, hg, hgj⟩ := exists_mem_stab_stab_maps hab hj₀a hj₀b hja hjb
      have hgK : g ∈ M22g a b := hg
      obtain ⟨-, hga, -⟩ := (mem_M22g_iff a b g).1 hgK
      refine ⟨⟨g, hK hgK⟩, ?_⟩
      have h1 := vecOf_act_pair hreal' hv₀ ⟨g, hK hgK⟩
      have h2 : ((⟨g, hK hgK⟩ : ↥Γ) : Equiv.Perm (Fin 24)) a = a := hga
      have h3 : ((⟨g, hK hgK⟩ : ↥Γ) : Equiv.Perm (Fin 24)) j₀ = j := hgj
      rw [h2, h3] at h1
      exact (vecOf_pair_eq_iff_sup hreal' hab (Ne.symm hja) (Ne.symm hja) h1 hvj).2 (Or.inl rfl)
    · intro v hv g
      obtain ⟨j, hja, hjb, hvj⟩ := key v hv
      have hinj := (g : Equiv.Perm (Fin 24)).injective
      have hgj : (g : S24) j ≠ a ∧ (g : S24) j ≠ b := by
        rcases hgrp g with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨fun h => hja (hinj (h.trans h1.symm)), fun h => hjb (hinj (h.trans h2.symm))⟩
        · exact ⟨fun h => hjb (hinj (h.trans h2.symm)), fun h => hja (hinj (h.trans h1.symm))⟩
      refine ⟨(g : S24) a, (g : S24) j, hinj.ne (Ne.symm hja), Or.inr (Or.inr ⟨rfl, ?_, hgj⟩),
        vecOf_act_pair hreal' hvj g⟩
      rcases hgrp g with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · intro v hv
      obtain ⟨j, hja, hjb, hvj⟩ := key v hv
      have hC : ∀ g : ↥Γ, g ∈ cenM ρ (Subgroup.zpowers v) ↔ (g : S24) j = j := fun g =>
        (h15_1_mem_cenM_iff ρ v g).trans (rho_eq_self_iff_22 hreal' hab hja hjb hvj g (hgrp g))
      refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ?_⟩
      refine ⟨⟨j, hja, hjb, hvj, hC⟩, CFSG.ComponentClassification.PSL3Four.F4, inferInstance,
        CFSG.ComponentClassification.PSL3Four.natCard_F4, ?_, ?_⟩
      · intro hΓ
        subst hΓ
        have hCT : ∀ g : ↥(M22g a b), g ∈ cenM ρ (Subgroup.zpowers v) ↔
            (g : S24) ∈ AutPerm ⊓ stab a ⊓ stab b ⊓ stab j := by
          intro g
          rw [hC, Subgroup.mem_inf]
          exact ⟨fun h => ⟨g.2, (mem_stab_iff j g).2 h⟩, fun h => (mem_stab_iff j g).1 h.2⟩
        obtain ⟨e⟩ := nonempty_equiv_of_mem_iff (T := AutPerm ⊓ stab a ⊓ stab b ⊓ stab j)
          (fun x hx => hx.1) hCT
        obtain ⟨e'⟩ := nonempty_stab3_equiv_PSL hab hja hjb
        exact ⟨MulEquiv.trans e e'⟩
      · intro hΓ
        have hCT : ∀ g : ↥Γ, g ∈ cenM ρ (Subgroup.zpowers v) ↔ (g : S24) ∈ Γ ⊓ stab j := by
          intro g
          rw [hC, Subgroup.mem_inf]
          exact ⟨fun h => ⟨g.2, (mem_stab_iff j g).2 h⟩, fun h => (mem_stab_iff j g).1 h.2⟩
        have hT' : AutPerm ⊓ stab a ⊓ stab b ⊓ stab j ≤ Γ ⊓ stab j :=
          fun x hx => ⟨hK hx.1, hx.2⟩
        have hidx := relIndex_stab_eq_two hab hja hjb (Γ := Γ) hK hP hΓ
        obtain ⟨N, hN, ⟨e⟩⟩ := exists_index_two_equiv (T := Γ ⊓ stab j)
          (T' := AutPerm ⊓ stab a ⊓ stab b ⊓ stab j) inf_le_left hCT hT' hidx
        obtain ⟨e'⟩ := nonempty_stab3_equiv_PSL hab hja hjb
        exact ⟨N, hN, ⟨MulEquiv.trans e e'⟩⟩
    · have hreal22 := realizesBy_golaySec_restrict hK hreal'
      have hMC : MathieuCocode22 (ρ.comp (Subgroup.inclusion hK)).range ⊤ ⊥ :=
        ⟨a, b, hab, (ρ.comp (Subgroup.inclusion hK)).rangeRestrict,
          (realizesVia_iff _ _ _ _ _).2 ⟨β, hreal22⟩⟩
      intro v hv
      obtain ⟨j, hja, hjb, hvj⟩ := key v hv
      have hO2 : IsCocodeO2 (ρ.comp (Subgroup.inclusion hK)).range v :=
        Or.inr (Or.inr ⟨a, b, hab, (ρ.comp (Subgroup.inclusion hK)).rangeRestrict, β, hreal22,
          j, Ne.symm hja, Ne.symm hjb, hvj.choose_spec⟩)
      refine h15_1_commOn_eq (closure_comm_eq_top_22 ?_ hMC hO2)
      rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩

end H151

@[expose] def H_15_2 : Prop :=
  AllMCtx false (fun d => d = 22 ∨ d = 23 ∨ d = 24) fun d a b O _ _ _ T₀ Γ V _ ρ β =>
    ((H.IsFOneOffender ρ.range (rImg ρ (KY Γ (Yd d a b O))) ∧
        ∀ A : Subgroup (MulAut V), A ≤ rImg ρ (T₀ ⊓ Γ) → H.IsFOneOffender ρ.range A →
          A = rImg ρ (KY Γ (Yd d a b O))) ∧
      (rk ↥(fixV (rImg ρ (KY Γ (Yd d a b O)))) = (if d = 22 then 5 else 6) ∧
        (∀ g : ↥Γ, (g : S24) ∈ MY Γ (Yd d a b O) →
          ((∀ u ∈ fixV (rImg ρ (KY Γ (Yd d a b O))), ρ g u = u) ↔ (g : S24) ∈ KY Γ (Yd d a b O))) ∧
        (d = 24 →
          InducesOn (rImg ρ (MY Γ (Yd d a b O))) (fixV (rImg ρ (KY Γ (Yd d a b O)))) ⊥
            (Multiplicative (Fin 6 → ZMod 2)) (omegaN 6 qPlus6)) ∧
        (d = 23 → ∃ Γ₇ : Subgroup (MulAut (Multiplicative (Fin 6 → ZMod 2))), Γ₇ ≤ omegaN 6 qPlus6 ∧
          Nonempty (↥Γ₇ ≃* ↥(alternatingGroup (Fin 7))) ∧
          InducesOn (rImg ρ (MY Γ (Yd d a b O))) (fixV (rImg ρ (KY Γ (Yd d a b O)))) ⊥
            (Multiplicative (Fin 6 → ZMod 2)) Γ₇) ∧
        (d = 22 → ∃ (w : Multiplicative (Fin 6 → ZMod 2)) (π : Multiplicative (Fin 6 → ZMod 2) →* V),
          qPlus6 (Multiplicative.toAdd w) = 1 ∧ π.range = fixV (rImg ρ (KY Γ (Yd d a b O))) ∧
          π.ker = Subgroup.zpowers w ∧
          (∀ g : ↥Γ, (g : S24) ∈ MY Γ (Yd d a b O) →
            ∃ γ ∈ omegaN 6 qPlus6, γ w = w ∧ ∀ x, π (γ x) = ρ g (π x)) ∧
          (Γ ≠ M22g a b → ∀ γ ∈ omegaN 6 qPlus6, γ w = w →
            ∃ g : ↥Γ, (g : S24) ∈ MY Γ (Yd d a b O) ∧ ∀ x, π (γ x) = ρ g (π x))) ∧
        (d = 23 → ∃ π : ↥(MY Γ (Yd d a b O)) →* ↥(alternatingGroup (Fin 7)), Function.Surjective π ∧
          π.ker = (KY Γ (Yd d a b O)).subgroupOf (MY Γ (Yd d a b O))) ∧
        (d = 24 → ∃ π : ↥(MY Γ (Yd d a b O)) →* ↥(alternatingGroup (Fin 8)), Function.Surjective π ∧
          π.ker = (KY Γ (Yd d a b O)).subgroupOf (MY Γ (Yd d a b O))) ∧
        (d = 22 → (Γ = M22g a b → ∃ π : ↥(MY Γ (Yd d a b O)) →* ↥(alternatingGroup (Fin 6)),
            Function.Surjective π ∧ π.ker = (KY Γ (Yd d a b O)).subgroupOf (MY Γ (Yd d a b O))) ∧
          (Γ ≠ M22g a b → ∃ π : ↥(MY Γ (Yd d a b O)) →* Equiv.Perm (Fin 6),
            Function.Surjective π ∧ π.ker = (KY Γ (Yd d a b O)).subgroupOf (MY Γ (Yd d a b O)))))) ∧
    (∀ I : Subgroup V, I ≤ fixV (rImg ρ (KY Γ (Yd d a b O))) → (∀ x ∈ I, ¬ IsO2Vec d a b Γ β x) →
      rk ↥I ≤ (if d = 24 then 3 else 4)) ∧
    rkIdx (xiSub (rImg ρ (KY Γ (Yd d a b O)))) = 1 ∧
    ((∀ z ∈ Γ, orderOf z = 2 → IsTwoCentralElt Γ z →
        cenM ρ (fixV (rImg ρ (Subgroup.zpowers z))) = (Subgroup.zpowers z).subgroupOf Γ) ∧
      (∀ A : Subgroup S24, A ≤ KY Γ (Yd d a b O) → ¬ IsCyclic ↥A →
        fixV (rImg ρ A) = fixV (rImg ρ (KY Γ (Yd d a b O))))) ∧
    FullTranspAxis (rImg ρ (MY Γ (Yd d a b O))) (rImg ρ (KY Γ (Yd d a b O)))
      (fixV (rImg ρ (KY Γ (Yd d a b O)))) (xiSub (rImg ρ (KY Γ (Yd d a b O))))

section H15_2


theorem as_H_15_2 : H_15_2 := by
  intro d _ a b O Tr S B T₀ Γ V _ ρ β hM
  exact AppH.h152_main hM

end H15_2

@[expose] def H_15_3 : Prop :=
  AllMCtxAt false 24 fun a b _ _ S _ _ Γ V _ ρ β =>
    ∃ V₇ : Subgroup V,
      Chain153 a b β ρ S V₇ ∧
      FullTranspCenter (rImg ρ (MY Γ S)) (rImg ρ (KY Γ S)) V₇ (fixV (rImg ρ (KY Γ S))) ∧
      xiSub (rImg ρ (KY Γ S)) = ⊤ ∧
      (∀ x : V, x ∈ V₇ ↔ ∀ g ∈ rImg ρ (KY Γ S), g x * x⁻¹ ∈ fixV (rImg ρ (KY Γ S)))

section H15_3


theorem as_H_15_3 : H_15_3 := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM
  have hΓ : Γ = M24g :=
    le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut) (by simpa [Ld] using hM.L_le)
  subst hΓ
  exact CFSG.Quasithin.H153.h153_main hM.cfg ρ β hM.real

end H15_3

@[expose] def H_15_4 : Prop :=
  AllMCtxAt false 22 fun a b _ _ S B _ Γ V _ ρ _ =>
    Γ = M2ab a b →
      (∃ V₆ : Subgroup V,
        (IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ (S.erase B)))) ⊥
            (fixV (rImg ρ (KY Γ (S.erase B)))) ∧
          rk ↥(fixV (rImg ρ (KY Γ (S.erase B)))) = 1 ∧
          IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ (S.erase B))))
            (fixV (rImg ρ (KY Γ (S.erase B)))) (fixV (rImg ρ (KY Γ (S.erase B) ⊓ M22g a b))) ∧
          rk ↥(fixV (rImg ρ (KY Γ (S.erase B) ⊓ M22g a b))) = 2 ∧
          IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ (S.erase B))))
            (fixV (rImg ρ (KY Γ (S.erase B) ⊓ M22g a b))) V₆ ∧
          IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ (S.erase B)))) V₆ ⊤ ∧ rk ↥V₆ = 6 ∧
          IsDualOfConj ρ (MY Γ (S.erase B)) V₆ (fixV (rImg ρ (KY Γ (S.erase B)))) (KY Γ (S.erase B)) ∧
          InducesOnSub (rImg ρ (MY Γ (S.erase B))) ⊤ V₆ (G6.PermMod 5) (G6.coreMod 5)
            (G6.permAct 5).range ∧
          (∀ g : ↥Γ, (g : S24) ∈ MY Γ (S.erase B) →
            ((∀ x : V, ρ g x * x⁻¹ ∈ V₆) ↔ (g : S24) ∈ KY Γ (S.erase B)))) ∧
        FullTranspCenter (rImg ρ (MY Γ (S.erase B))) (rImg ρ (KY Γ (S.erase B))) V₆
          (fixV (rImg ρ (KY Γ (S.erase B))))) ∧
      (∀ A : Subgroup S24, A ≤ KY Γ (S.erase B) → Nat.card A * 2 = Nat.card (KY Γ (S.erase B)) →
        xiSub (rImg ρ A) = ⊤ ∧ rk ↥(fixV (rImg ρ A)) = 2) ∧
      (⨆ (B' : Subgroup S24) (_ : B' ≤ KY Γ (S.erase B)) (_ : IsE2k 2 B'), fixV (rImg ρ B')) = ⊤

section H154

open CFSG.Quasithin.H.Mathieu


theorem as_H_15_4 : H_15_4 := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM hΓ
  have hreal : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24)
      (golayC ⊔ Subgroup.zpowers (pairVec a b))) ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
  have hL : M22g a b ≤ Γ := by simpa [Ld] using hM.L_le
  exact CFSG.Quasithin.RonanH154.main154 hM.cfg.ne hM.cfg.octad.1 hM.cfg.a_O hM.cfg.b_O
    hM.cfg.sextet hM.cfg.B_mem hM.cfg.a_B hM.cfg.b_B hM.cfg.stab_O hM.cfg.stab_S hL hM.sylow
    hreal hΓ

end H154

@[expose] def H_15_5 : Prop :=
  AllMCtxAt false 22 fun a b O _ S B T₀ Γ _ _ ρ _ =>
    Γ = M2ab a b → ∀ A : Subgroup S24, A ≤ T₀ ⊓ Γ → IsE2k 4 A →
      (A = KY Γ ((O.erase a).erase b) ∧ rk ↥(fixV (rImg ρ A)) = 5 ∧ rkIdx (xiSub (rImg ρ A)) = 1) ∨
      ((∃ g ∈ Γ, conjSubg g A ≤ KY Γ (S.erase B)) ∧ rk ↥(fixV (rImg ρ A)) = 2 ∧
        xiSub (rImg ρ A) = ⊤) ∨
      ((∃ i ∈ A, i ∉ M22g a b ∧
          (∃ O' : Finset (Fin 24), IsOctad O' ∧ ¬ (a ∈ O' ∧ b ∈ O') ∧ fixedSet i = O') ∧
          A = pCoreOf 2 (Γ ⊓ Subgroup.centralizer ({i} : Set S24)) ∧
          ∃ π : ↥(Γ ⊓ Subgroup.centralizer ({i} : Set S24)) →* GL (Fin 3) (ZMod 2),
            Function.Surjective π ∧ π.ker = A.subgroupOf (Γ ⊓ Subgroup.centralizer ({i} : Set S24))) ∧
        rk ↥(fixV (rImg ρ A)) = 3 ∧ xiSub (rImg ρ A) = ⊤) ∨
      (rk ↥(A ⊓ KY Γ ((O.erase a).erase b)) = 3 ∧ rk ↥(fixV (rImg ρ A)) = 3 ∧
        rkIdx (xiSub (rImg ρ A)) ≤ 1)

section H155

open CFSG.Quasithin.H.Mathieu


theorem as_H_15_5 : H_15_5 := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM hΓ
  have hreal : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24)
      (golayC ⊔ Subgroup.zpowers (pairVec a b))) ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
  have hL : M22g a b ≤ Γ := by simpa [Ld] using hM.L_le
  exact CFSG.Quasithin.RonanH155.main155 hM.cfg.ne hM.cfg.octad.1 hM.cfg.a_O hM.cfg.b_O
    hM.cfg.sextet hM.cfg.B_mem hM.cfg.a_B hM.cfg.b_B hM.cfg.stab_O hM.cfg.stab_S hL hM.sylow
    hreal hΓ

end H155

@[expose] def H_15_6 : Prop :=
  AllMCtxAt false 24 fun _ _ _ Tr _ _ _ _ V _ ρ _ =>
    ∃ V₉ : Subgroup V, Chain156 ρ Tr V₉ ∧ TensorFactors156 ρ Tr V₉

section H15_6


theorem as_H_15_6 : H_15_6 := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM
  have hΓ : Γ = M24g :=
    le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut) (by simpa [Ld] using hM.L_le)
  subst hΓ
  exact CFSG.Quasithin.H156.h156_main hM.cfg ρ β hM.real

end H15_6

@[expose] def H_15_7 : Prop :=
  AllMCtxAt false 24 fun a b _ _ S _ _ Γ V _ ρ β =>
    ∀ Mx : Subgroup S24, (Mx = M24g ∨ Mx = M23g a) → ∀ y ∈ Mx, (orderOf y).Prime → Odd (orderOf y) →
      4 ≤ rk ↥(fixV (rImg ρ (Subgroup.zpowers y))) →
      (orderOf y = 3 ∧ rk ↥(fixV (rImg ρ (Subgroup.zpowers y))) = 5 ∧
        ∃ g ∈ M24g,
          (M24g ⊓ Subgroup.normalizer ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24)) ⊓
              KY M24g S = ⊥ ∧
          (M24g ⊓ Subgroup.normalizer ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24)) ⊔
              KY M24g S = MY M24g S ∧
          fixV (rImg ρ (KY M24g S)) =
            fixV (rImg ρ (M24g ⊓ Subgroup.normalizer
              ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24))) ∧
          ∃ π : ↥(M24g ⊓ Subgroup.normalizer ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24))
              →* Equiv.Perm (Fin 6), Function.Surjective π ∧
            π.ker = (conjSubg g (Subgroup.zpowers y)).subgroupOf
              (M24g ⊓ Subgroup.normalizer ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24)) ∧
            ∃ coordinates : Fin 6 ↪ Fin 24,
              (∀ point : Fin 24, (g * y * g⁻¹) point = point ↔
                ∃ index : Fin 6, coordinates index = point) ∧
              ∀ (acting : ↥(M24g ⊓ Subgroup.normalizer
                  ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24))) (index : Fin 6),
                (acting : S24) (coordinates index) = coordinates (π acting index)) ∧
      (∀ x : V, x ∈ fixV (rImg ρ (Subgroup.zpowers y)) ↔
        ∃ u : PM24, u ∈ G6.coreMod 24 ∧ (∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → y i = i) ∧
          IsVecOf (mathModel false 24 a b Γ) β u x) ∧
      (∀ u : PM24, u ≠ 1 → u ∈ G6.coreMod 24 → (∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → y i = i) →
        u ∉ golayC) ∧
      (∀ I : Subgroup V, I ≤ fixV (rImg ρ (Subgroup.zpowers y)) →
        (Mx = M24g → (∀ x ∈ I, ¬ IsO2Vec 24 a b Γ β x) → rk ↥I ≤ 2) ∧
        (Mx = M23g a → (∀ x ∈ I, ¬ ∃ j : Fin 24, j ≠ a ∧
          IsVecOf (mathModel false 24 a b Γ) β (pairVec a j) x) → rk ↥I ≤ 4))

section H15_7


theorem as_H_15_7 : H_15_7 := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM
  have hΓ : Γ = M24g :=
    le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut) (by simpa [Ld] using hM.L_le)
  subst hΓ
  intro Mx hMx y hy hp hodd h4
  exact CFSG.ASVolI.AppH.H157.h157_main hM.cfg ρ β hM.real Mx hMx y hy hp hodd h4

end H15_7

@[expose] def H_15_8 : Prop :=
  AllMCtxAt false 24 fun a b _ Tr S _ _ Γ V _ ρ β =>
    ∀ V₇ V₉ : Subgroup V, Chain153 a b β ρ S V₇ → Chain156 ρ Tr V₉ →
      V₇ ≤ V₉ ∧ ¬ V₇ ≤ fixV (rImg ρ (KY Γ Tr))

section H15_8


theorem as_H_15_8 : H_15_8 := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM V₇ V₉ h153 h156
  have hΓ : Γ = M24g :=
    le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut) (by simpa [Ld] using hM.L_le)
  subst hΓ
  obtain ⟨-, hrk1, hvec, hcf, -, hrk7, -, -⟩ := h153
  obtain ⟨-, hr3, -, -, hV9, -, -, -, -, -⟩ := h156
  refine ⟨?_, CFSG.Quasithin.H158N.not_le_of_rk (by simpa using hrk7) hr3⟩
  obtain ⟨B', hB'⟩ : ∃ B', B' ∈ S := Finset.card_pos.1 (by rw [hM.cfg.sextet.1]; norm_num)
  rw [hV9]
  exact CFSG.Quasithin.H158U.h158_main hM.cfg ρ β hM.real hrk1
    ((hvec B' hB').imp fun v hv => hv.2) hcf hrk7

end H15_8

end CFSG.ASVolI
