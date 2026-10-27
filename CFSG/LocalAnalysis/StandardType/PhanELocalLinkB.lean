module

public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K]

private lemma plh_planes_ne_facts {S T : Submodule K (Fin 4 → K)}
    (hS : finrank K S = 3) (hT : finrank K T = 3) (hne : S ≠ T) :
    S ⊔ T = ⊤ ∧ finrank K ↥(S ⊓ T) = 2 := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S T
  have hle_inf : finrank K ↥(S ⊓ T) ≤ 3 := by
    have h := Submodule.finrank_mono (inf_le_left : S ⊓ T ≤ S)
    rwa [hS] at h
  have htop : S ⊔ T = ⊤ := by
    by_contra h
    have hlt : finrank K ↥(S ⊔ T) < 4 := by
      have h := Submodule.finrank_lt (K := K) (V := Fin 4 → K) h
      rwa [Module.finrank_fin_fun] at h
    have hfin : finrank K ↥(S ⊓ T) = 3 := by omega
    have heq : S ⊓ T = S := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hfin, hS])
    have hle : S ≤ T := by rw [← heq]; exact inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hle (by rw [hS, hT]))
  refine ⟨htop, ?_⟩
  rw [htop, finrank_top, Module.finrank_fin_fun, hS, hT] at hsum
  omega

private lemma plh_lines_ne_facts {p n n' : Submodule K (Fin 4 → K)}
    (hp : finrank K p = 1) (hn : finrank K n = 2) (hn' : finrank K n' = 2)
    (hpn : p ≤ n) (hpn' : p ≤ n') (hne : n ≠ n') :
    n ⊓ n' = p ∧ finrank K ↥(n ⊔ n') = 3 := by
  have hle : p ≤ n ⊓ n' := le_inf hpn hpn'
  have hge : 1 ≤ finrank K ↥(n ⊓ n') := by
    have h := Submodule.finrank_mono hle
    rwa [hp] at h
  have hle2 : finrank K ↥(n ⊓ n') ≤ 2 := by
    have h := Submodule.finrank_mono (inf_le_left : n ⊓ n' ≤ n)
    rwa [hn] at h
  have hlt : finrank K ↥(n ⊓ n') < 2 := by
    by_contra h
    have h2 : finrank K ↥(n ⊓ n') = 2 := by omega
    have heq : n ⊓ n' = n := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h2, hn])
    have hle' : n ≤ n' := by rw [← heq]; exact inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hle' (by rw [hn, hn']))
  have hfin : finrank K ↥(n ⊓ n') = 1 := by omega
  have hinf : n ⊓ n' = p :=
    (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hp])).symm
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq n n'
  rw [hinf, hp, hn, hn'] at hsum
  exact ⟨hinf, by omega⟩

private lemma plh_inf_eq_of_planes_through_line {U T T' : Submodule K (Fin 4 → K)}
    (hU : finrank K U = 2) (hT : finrank K T = 3) (hT' : finrank K T' = 3)
    (hUT : U ≤ T) (hUT' : U ≤ T') (hne : T ≠ T') : T ⊓ T' = U := by
  have hle : U ≤ T ⊓ T' := le_inf hUT hUT'
  have hge : 2 ≤ finrank K ↥(T ⊓ T') := by
    have h := Submodule.finrank_mono hle
    rwa [hU] at h
  have hle3 : finrank K ↥(T ⊓ T') ≤ 3 := by
    have h := Submodule.finrank_mono (inf_le_left : T ⊓ T' ≤ T)
    rwa [hT] at h
  have hlt : finrank K ↥(T ⊓ T') < 3 := by
    by_contra h
    have h3 : finrank K ↥(T ⊓ T') = 3 := by omega
    have heq : T ⊓ T' = T := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h3, hT])
    have hle' : T ≤ T' := by rw [← heq]; exact inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hle' (by rw [hT, hT']))
  have hfin : finrank K ↥(T ⊓ T') = 2 := by omega
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hU])).symm

@[expose] def DualPencilGood (p U : Submodule K (Fin 4 → K))
    (𝒯 : Submodule K (Fin 4 → K) → Prop)
    (a : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K)) : Prop :=
  IsFlag p a.1 a.2 ∧ ¬ U ≤ a.2 ∧ 𝒯 (a.1 ⊔ U)

theorem dualPencilGood_connected {p U : Submodule K (Fin 4 → K)} (hU : finrank K U = 2)
    (hpU : p ≤ U) {𝒯 : Submodule K (Fin 4 → K) → Prop} {T₂ T₃ : Submodule K (Fin 4 → K)}
    (hne : T₂ ≠ T₃) (h₂ : U ≤ T₂ ∧ finrank K T₂ = 3 ∧ 𝒯 T₂)
    (h₃ : U ≤ T₃ ∧ finrank K T₃ = 3 ∧ 𝒯 T₃)
    {a b : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K)}
    (ha : DualPencilGood p U 𝒯 a) (hb : DualPencilGood p U 𝒯 b) :
    Relation.ReflTransGen (fun a b : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K) =>
      DualPencilGood p U 𝒯 a ∧ DualPencilGood p U 𝒯 b ∧ (a.2 = b.2 ∨ a.1 = b.1)) a b := by
  rcases a with ⟨L, H⟩
  rcases b with ⟨L', H'⟩
  obtain ⟨hUT₂, hT₂3, h𝒯T₂⟩ := h₂
  obtain ⟨hUT₃, hT₃3, h𝒯T₃⟩ := h₃
  have hp1 : finrank K p = 1 := ha.1.p1
  have hH3 : finrank K H = 3 := ha.1.H3
  have hpL : p ≤ L := ha.1.pL
  have hLH : L ≤ H := ha.1.LH
  have hH'3 : finrank K H' = 3 := hb.1.H3
  have hpL' : p ≤ L' := hb.1.pL
  have hL'H' : L' ≤ H' := hb.1.LH
  set r : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K) →
      Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K) → Prop :=
    fun a b => DualPencilGood p U 𝒯 a ∧ DualPencilGood p U 𝒯 b ∧ (a.2 = b.2 ∨ a.1 = b.1)
    with hr
  let L₂ : Submodule K (Fin 4 → K) := H ⊓ T₂
  let L₃ : Submodule K (Fin 4 → K) := H' ⊓ T₃
  let R : Submodule K (Fin 4 → K) := L₂ ⊔ L₃
  have hHneT₂ : H ≠ T₂ := by
    intro hEq
    exact ha.2.1 (by rw [hEq]; exact hUT₂)
  have hL₂fin : finrank K L₂ = 2 := (plh_planes_ne_facts hH3 hT₂3 hHneT₂).2
  have hpL₂ : p ≤ L₂ := le_inf (hpL.trans hLH) (hpU.trans hUT₂)
  have hL₂leH : L₂ ≤ H := inf_le_left
  have hL₂neU : L₂ ≠ U := by
    intro hEq
    exact ha.2.1 (by rw [← hEq]; exact hL₂leH)
  have hL₂facts := plh_lines_ne_facts hp1 hL₂fin hU hpL₂ hpU hL₂neU
  have hL₂supU : L₂ ⊔ U = T₂ :=
    Submodule.eq_of_le_of_finrank_eq (sup_le inf_le_right hUT₂) (by rw [hL₂facts.2, hT₂3])
  have hgoodL₂H : DualPencilGood p U 𝒯 (L₂, H) :=
    ⟨⟨hp1, hL₂fin, hH3, hpL₂, hL₂leH⟩, ha.2.1, by rw [hL₂supU]; exact h𝒯T₂⟩
  have hH'neT₃ : H' ≠ T₃ := by
    intro hEq
    exact hb.2.1 (by rw [hEq]; exact hUT₃)
  have hL₃fin : finrank K L₃ = 2 := (plh_planes_ne_facts hH'3 hT₃3 hH'neT₃).2
  have hpL₃ : p ≤ L₃ := le_inf (hpL'.trans hL'H') (hpU.trans hUT₃)
  have hL₃leH' : L₃ ≤ H' := inf_le_left
  have hL₃neU : L₃ ≠ U := by
    intro hEq
    exact hb.2.1 (by rw [← hEq]; exact hL₃leH')
  have hL₃facts := plh_lines_ne_facts hp1 hL₃fin hU hpL₃ hpU hL₃neU
  have hL₃supU : L₃ ⊔ U = T₃ :=
    Submodule.eq_of_le_of_finrank_eq (sup_le inf_le_right hUT₃) (by rw [hL₃facts.2, hT₃3])
  have hgoodL₃H' : DualPencilGood p U 𝒯 (L₃, H') :=
    ⟨⟨hp1, hL₃fin, hH'3, hpL₃, hL₃leH'⟩, hb.2.1, by rw [hL₃supU]; exact h𝒯T₃⟩
  have hL₂neL₃ : L₂ ≠ L₃ := by
    intro hEq
    have hle : L₂ ≤ U := by
      have hle' : L₂ ≤ T₂ ⊓ T₃ :=
        le_inf inf_le_right (by rw [hEq]; exact inf_le_right)
      rwa [plh_inf_eq_of_planes_through_line hU hT₂3 hT₃3 hUT₂ hUT₃ hne] at hle'
    exact hL₂neU (Submodule.eq_of_le_of_finrank_eq hle (by rw [hL₂fin, hU]))
  have hRfacts := plh_lines_ne_facts hp1 hL₂fin hL₃fin hpL₂ hpL₃ hL₂neL₃
  have hpR : p ≤ R := hpL₂.trans le_sup_left
  have hRneU : ¬ U ≤ R := by
    intro hUR
    have hT₂leR : T₂ ≤ R := by
      rw [← hL₂supU]
      exact sup_le le_sup_left hUR
    have hT₂eqR : T₂ = R :=
      Submodule.eq_of_le_of_finrank_eq hT₂leR (by rw [hT₂3, hRfacts.2])
    have hT₃leR : T₃ ≤ R := by
      rw [← hL₃supU]
      exact sup_le le_sup_right hUR
    have hT₃eqR : T₃ = R :=
      Submodule.eq_of_le_of_finrank_eq hT₃leR (by rw [hT₃3, hRfacts.2])
    exact hne (hT₂eqR.trans hT₃eqR.symm)
  have hgoodL₂R : DualPencilGood p U 𝒯 (L₂, R) :=
    ⟨⟨hp1, hL₂fin, hRfacts.2, hpL₂, le_sup_left⟩, hRneU, by rw [hL₂supU]; exact h𝒯T₂⟩
  have hgoodL₃R : DualPencilGood p U 𝒯 (L₃, R) :=
    ⟨⟨hp1, hL₃fin, hRfacts.2, hpL₃, le_sup_right⟩, hRneU, by rw [hL₃supU]; exact h𝒯T₃⟩
  have h1 : Relation.ReflTransGen r (L, H) (L₂, H) :=
    Relation.ReflTransGen.single ⟨ha, hgoodL₂H, Or.inl rfl⟩
  have h2 : Relation.ReflTransGen r (L₂, H) (L₂, R) :=
    Relation.ReflTransGen.single ⟨hgoodL₂H, hgoodL₂R, Or.inr rfl⟩
  have h3 : Relation.ReflTransGen r (L₂, R) (L₃, R) :=
    Relation.ReflTransGen.single ⟨hgoodL₂R, hgoodL₃R, Or.inl rfl⟩
  have h4 : Relation.ReflTransGen r (L₃, R) (L₃, H') :=
    Relation.ReflTransGen.single ⟨hgoodL₃R, hgoodL₃H', Or.inr rfl⟩
  have h5 : Relation.ReflTransGen r (L₃, H') (L', H') :=
    Relation.ReflTransGen.single ⟨hgoodL₃H', hb, Or.inl rfl⟩
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

theorem admFibreConn_of_dual_pencil
    (Adm : Submodule K (Fin 4 → K) → Submodule K (Fin 4 → K) → Submodule K (Fin 4 → K) → Prop)
    (U : Submodule K (Fin 4 → K) → Submodule K (Fin 4 → K))
    (𝒯 : Submodule K (Fin 4 → K) → Submodule K (Fin 4 → K) → Prop)
    (hU : ∀ p L H, AdmCh Adm p L H → finrank K (U p) = 2 ∧ p ≤ U p)
    (hiff : ∀ p L₀ H₀, AdmCh Adm p L₀ H₀ → ∀ L H, IsFlag p L H →
      (Adm p L H ↔ (¬ U p ≤ H ∧ 𝒯 p (L ⊔ U p))))
    (htwo : ∀ p L₀ H₀, AdmCh Adm p L₀ H₀ → ∃ T₂ T₃ : Submodule K (Fin 4 → K), T₂ ≠ T₃ ∧
      (U p ≤ T₂ ∧ finrank K T₂ = 3 ∧ 𝒯 p T₂) ∧ (U p ≤ T₃ ∧ finrank K T₃ = 3 ∧ 𝒯 p T₃)) :
    AdmFibreConn Adm := by
  intro p L H L' H' hp hq
  obtain ⟨hU2, hpU⟩ := hU p L H hp
  obtain ⟨T₂, T₃, hTne, hT₂, hT₃⟩ := htwo p L H hp
  have hgood : DualPencilGood p (U p) (𝒯 p) (L, H) :=
    ⟨hp.1, (hiff p L H hp L H hp.1).mp hp.2⟩
  have hgood' : DualPencilGood p (U p) (𝒯 p) (L', H') :=
    ⟨hq.1, (hiff p L H hp L' H' hq.1).mp hq.2⟩
  have hconn := dualPencilGood_connected (p := p) (U := U p) (𝒯 := 𝒯 p) hU2 hpU hTne hT₂ hT₃
    hgood hgood'
  refine Relation.ReflTransGen.mono ?_ (L, H) (L', H') hconn
  rintro a b ⟨ha1, hb1, hsame⟩
  exact ⟨⟨ha1.1, (hiff p L H hp a.1 a.2 ha1.1).mpr ha1.2⟩,
    ⟨hb1.1, (hiff p L H hp b.1 b.2 hb1.1).mpr hb1.2⟩, hsame⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
