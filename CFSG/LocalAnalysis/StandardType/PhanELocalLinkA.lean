module

public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K]

@[expose] def PencilGood (p W : Submodule K (Fin 4 → K))
    (𝒩 : Submodule K (Fin 4 → K) → Prop)
    (a : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K)) : Prop :=
  IsFlag p a.1 a.2 ∧ ¬ a.1 ≤ W ∧ 𝒩 (a.2 ⊓ W)

private lemma plh_finrank_plane_inf {S T : Submodule K (Fin 4 → K)}
    (hS : finrank K S = 3) (hT : finrank K T = 3) (hne : S ≠ T) :
    S ⊔ T = ⊤ ∧ finrank K ↥(S ⊓ T) = 2 := by
  have hle : finrank K ↥(S ⊔ T) ≤ 4 := by
    have h := Submodule.finrank_le (S ⊔ T)
    rwa [Module.finrank_fin_fun] at h
  have hge : 3 ≤ finrank K ↥(S ⊔ T) := by
    have h := Submodule.finrank_mono (le_sup_left : S ≤ S ⊔ T)
    rwa [hS] at h
  have hfin : finrank K ↥(S ⊔ T) = 4 := by
    have hne3 : finrank K ↥(S ⊔ T) ≠ 3 := by
      intro h3
      have hEq : S = S ⊔ T :=
        Submodule.eq_of_le_of_finrank_eq le_sup_left (by rw [h3, hS])
      have hTS : T ≤ S := hEq.symm ▸ le_sup_right
      exact hne (Submodule.eq_of_le_of_finrank_eq hTS (by rw [hT, hS])).symm
    omega
  refine ⟨Submodule.eq_top_of_finrank_eq (by rw [hfin, Module.finrank_fin_fun]), ?_⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq S T
  rw [hfin, hS, hT] at h
  omega

private lemma plh_inf_eq_of_not_le {p L W : Submodule K (Fin 4 → K)}
    (hp : finrank K p = 1) (hL : finrank K L = 2) (hpL : p ≤ L) (hpW : p ≤ W)
    (hLW : ¬ L ≤ W) : L ⊓ W = p := by
  have hple : p ≤ L ⊓ W := le_inf hpL hpW
  have hlt : L ⊓ W < L :=
    lt_of_le_of_ne inf_le_left fun h => hLW (h.symm.le.trans inf_le_right)
  have hlt2 : finrank K ↥(L ⊓ W) < finrank K L := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hL] at hlt2
  have hge : finrank K p ≤ finrank K ↥(L ⊓ W) := Submodule.finrank_mono hple
  rw [hp] at hge
  have hfin : finrank K ↥(L ⊓ W) = 1 := by omega
  exact (Submodule.eq_of_le_of_finrank_eq hple (by rw [hp, hfin])).symm

private lemma plh_inf_eq_of_lines {p n n' : Submodule K (Fin 4 → K)}
    (hp : finrank K p = 1) (hn : finrank K n = 2) (hn' : finrank K n' = 2)
    (hpn : p ≤ n) (hpn' : p ≤ n') (hne : n ≠ n') : n ⊓ n' = p := by
  have hple : p ≤ n ⊓ n' := le_inf hpn hpn'
  have hlt : n ⊓ n' < n := lt_of_le_of_ne inf_le_left fun h =>
    hne (Submodule.eq_of_le_of_finrank_eq (h.symm.le.trans inf_le_right) (by rw [hn, hn']))
  have hlt2 : finrank K ↥(n ⊓ n') < finrank K n := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hn] at hlt2
  have hge : finrank K p ≤ finrank K ↥(n ⊓ n') := Submodule.finrank_mono hple
  rw [hp] at hge
  have hfin : finrank K ↥(n ⊓ n') = 1 := by omega
  exact (Submodule.eq_of_le_of_finrank_eq hple (by rw [hp, hfin])).symm

theorem pencilGood_connected {p W : Submodule K (Fin 4 → K)} (hW : finrank K W = 3) (hpW : p ≤ W)
    {𝒩 : Submodule K (Fin 4 → K) → Prop} {n₂ n₃ : Submodule K (Fin 4 → K)} (hne : n₂ ≠ n₃)
    (h₂ : p ≤ n₂ ∧ n₂ ≤ W ∧ finrank K n₂ = 2 ∧ 𝒩 n₂)
    (h₃ : p ≤ n₃ ∧ n₃ ≤ W ∧ finrank K n₃ = 2 ∧ 𝒩 n₃)
    {a b : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K)}
    (ha : PencilGood p W 𝒩 a) (hb : PencilGood p W 𝒩 b) :
    Relation.ReflTransGen (fun a b : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K) =>
      PencilGood p W 𝒩 a ∧ PencilGood p W 𝒩 b ∧ (a.2 = b.2 ∨ a.1 = b.1)) a b := by
  obtain ⟨L, H⟩ := a
  obtain ⟨L', H'⟩ := b
  have hflagL : IsFlag p L H := ha.1
  have hLnW : ¬ L ≤ W := ha.2.1
  have hflagL' : IsFlag p L' H' := hb.1
  have hL'nW : ¬ L' ≤ W := hb.2.1
  obtain ⟨hpn₂, hn₂W, hn₂2, hNn₂⟩ := h₂
  obtain ⟨hpn₃, hn₃W, hn₃2, hNn₃⟩ := h₃
  set H₂ : Submodule K (Fin 4 → K) := L ⊔ n₂ with hH₂
  set H₃ : Submodule K (Fin 4 → K) := L' ⊔ n₃ with hH₃
  set R : Submodule K (Fin 4 → K) := H₂ ⊓ H₃ with hR
  have hLW : L ⊓ W = p := plh_inf_eq_of_not_le hflagL.p1 hflagL.L2 hflagL.pL hpW hLnW
  have hL'W : L' ⊓ W = p := plh_inf_eq_of_not_le hflagL'.p1 hflagL'.L2 hflagL'.pL hpW hL'nW
  have hL_n₂ : L ⊓ n₂ = p := by
    apply le_antisymm
    · calc L ⊓ n₂ ≤ L ⊓ W := le_inf inf_le_left (le_trans inf_le_right hn₂W)
        _ = p := hLW
    · exact le_inf hflagL.pL hpn₂
  have hL'_n₃ : L' ⊓ n₃ = p := by
    apply le_antisymm
    · calc L' ⊓ n₃ ≤ L' ⊓ W := le_inf inf_le_left (le_trans inf_le_right hn₃W)
        _ = p := hL'W
    · exact le_inf hflagL'.pL hpn₃
  have hH₂fin : finrank K H₂ = 3 := by
    rw [hH₂]
    have h := Submodule.finrank_sup_add_finrank_inf_eq L n₂
    rw [hL_n₂, hflagL.p1, hflagL.L2, hn₂2] at h
    omega
  have hH₂neW : H₂ ≠ W := by
    intro h
    have hLH₂ : L ≤ H₂ := by rw [hH₂]; exact le_sup_left
    exact hLnW (h ▸ hLH₂)
  have hH₂inf : H₂ ⊓ W = n₂ := by
    have hfin := (plh_finrank_plane_inf hH₂fin hW hH₂neW).2
    exact (Submodule.eq_of_le_of_finrank_eq
      (le_inf (by rw [hH₂]; exact le_sup_right) hn₂W) (by rw [hn₂2, hfin])).symm
  have goodH₂ : PencilGood p W 𝒩 (L, H₂) :=
    ⟨⟨hflagL.p1, hflagL.L2, hH₂fin, hflagL.pL, by rw [hH₂]; exact le_sup_left⟩,
      hLnW, by rw [hH₂inf]; exact hNn₂⟩
  have hH₃fin : finrank K H₃ = 3 := by
    rw [hH₃]
    have h := Submodule.finrank_sup_add_finrank_inf_eq L' n₃
    rw [hL'_n₃, hflagL'.p1, hflagL'.L2, hn₃2] at h
    omega
  have hH₃neW : H₃ ≠ W := by
    intro h
    have hLH₃ : L' ≤ H₃ := by rw [hH₃]; exact le_sup_left
    exact hL'nW (h ▸ hLH₃)
  have hH₃inf : H₃ ⊓ W = n₃ := by
    have hfin := (plh_finrank_plane_inf hH₃fin hW hH₃neW).2
    exact (Submodule.eq_of_le_of_finrank_eq
      (le_inf (by rw [hH₃]; exact le_sup_right) hn₃W) (by rw [hn₃2, hfin])).symm
  have goodH₃ : PencilGood p W 𝒩 (L', H₃) :=
    ⟨⟨hflagL'.p1, hflagL'.L2, hH₃fin, hflagL'.pL, by rw [hH₃]; exact le_sup_left⟩,
      hL'nW, by rw [hH₃inf]; exact hNn₃⟩
  have hH₂neH₃ : H₂ ≠ H₃ := by
    intro h
    exact hne (by rw [← hH₂inf, ← hH₃inf, h])
  have hRfin : finrank K R = 2 := by
    rw [hR]
    exact (plh_finrank_plane_inf hH₂fin hH₃fin hH₂neH₃).2
  have hpR : p ≤ R := by
    rw [hR]
    exact le_inf (hflagL.pL.trans (by rw [hH₂]; exact le_sup_left))
      (hflagL'.pL.trans (by rw [hH₃]; exact le_sup_left))
  have hRnW : ¬ R ≤ W := by
    intro hRW
    have hRn₂ : R ≤ n₂ := by
      have h : R ≤ H₂ ⊓ W := le_inf (by rw [hR]; exact inf_le_left) hRW
      rwa [hH₂inf] at h
    have hRn₃ : R ≤ n₃ := by
      have h : R ≤ H₃ ⊓ W := le_inf (by rw [hR]; exact inf_le_right) hRW
      rwa [hH₃inf] at h
    have hRp : R ≤ p := by
      rw [← plh_inf_eq_of_lines hflagL.p1 hn₂2 hn₃2 hpn₂ hpn₃ hne]
      exact le_inf hRn₂ hRn₃
    have hle : finrank K R ≤ finrank K p := Submodule.finrank_mono hRp
    rw [hflagL.p1, hRfin] at hle
    omega
  have goodRH₂ : PencilGood p W 𝒩 (R, H₂) :=
    ⟨⟨hflagL.p1, hRfin, hH₂fin, hpR, by rw [hR]; exact inf_le_left⟩,
      hRnW, by rw [hH₂inf]; exact hNn₂⟩
  have goodRH₃ : PencilGood p W 𝒩 (R, H₃) :=
    ⟨⟨hflagL.p1, hRfin, hH₃fin, hpR, by rw [hR]; exact inf_le_right⟩,
      hRnW, by rw [hH₃inf]; exact hNn₃⟩
  exact (Relation.ReflTransGen.single ⟨ha, goodH₂, Or.inr rfl⟩).trans
    ((Relation.ReflTransGen.single ⟨goodH₂, goodRH₂, Or.inl rfl⟩).trans
    ((Relation.ReflTransGen.single ⟨goodRH₂, goodRH₃, Or.inr rfl⟩).trans
    ((Relation.ReflTransGen.single ⟨goodRH₃, goodH₃, Or.inl rfl⟩).trans
      (Relation.ReflTransGen.single ⟨goodH₃, hb, Or.inr rfl⟩))))

theorem admFibreConn_of_pencil
    (Adm : Submodule K (Fin 4 → K) → Submodule K (Fin 4 → K) → Submodule K (Fin 4 → K) → Prop)
    (W : Submodule K (Fin 4 → K) → Submodule K (Fin 4 → K))
    (𝒩 : Submodule K (Fin 4 → K) → Submodule K (Fin 4 → K) → Prop)
    (hW : ∀ p L H, AdmCh Adm p L H → finrank K (W p) = 3 ∧ p ≤ W p)
    (hiff : ∀ p L₀ H₀, AdmCh Adm p L₀ H₀ → ∀ L H, IsFlag p L H →
      (Adm p L H ↔ (¬ L ≤ W p ∧ 𝒩 p (H ⊓ W p))))
    (htwo : ∀ p L₀ H₀, AdmCh Adm p L₀ H₀ → ∃ n₂ n₃ : Submodule K (Fin 4 → K), n₂ ≠ n₃ ∧
      (p ≤ n₂ ∧ n₂ ≤ W p ∧ finrank K n₂ = 2 ∧ 𝒩 p n₂) ∧
      (p ≤ n₃ ∧ n₃ ≤ W p ∧ finrank K n₃ = 2 ∧ 𝒩 p n₃)) :
    AdmFibreConn Adm := by
  intro p L H L' H' hp hq
  have hWp : finrank K (W p) = 3 := (hW p L H hp).1
  have hpW : p ≤ W p := (hW p L H hp).2
  obtain ⟨n₂, n₃, hne, h₂, h₃⟩ := htwo p L H hp
  have good_of_adm : ∀ {L₁ H₁ : Submodule K (Fin 4 → K)},
      AdmCh Adm p L₁ H₁ → PencilGood p (W p) (𝒩 p) (L₁, H₁) := by
    intro L₁ H₁ h
    exact ⟨h.1, (hiff p L H hp L₁ H₁ h.1).mp h.2⟩
  have adm_of_good : ∀ {L₁ H₁ : Submodule K (Fin 4 → K)},
      PencilGood p (W p) (𝒩 p) (L₁, H₁) → AdmCh Adm p L₁ H₁ := by
    intro L₁ H₁ h
    exact ⟨h.1, (hiff p L H hp L₁ H₁ h.1).mpr ⟨h.2.1, h.2.2⟩⟩
  have hconn := pencilGood_connected hWp hpW hne h₂ h₃ (good_of_adm hp) (good_of_adm hq)
  refine (Relation.ReflTransGen.mono ?_) (L, H) (L', H') hconn
  rintro ⟨x1, x2⟩ ⟨y1, y2⟩ ⟨hx, hy, hsame⟩
  exact ⟨adm_of_good hx, adm_of_good hy, hsame⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
