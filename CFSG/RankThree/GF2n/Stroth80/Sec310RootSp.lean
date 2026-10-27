module

public import CFSG.RankThree.GF2n.Stroth80.Sec310RootAux
public import CFSG.RankThree.GF2n.Stroth80.Sec310SpInv

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

theorem card_spForm_perp {m : ℕ} {K : Type} [Field K] [Finite K] {u : Fin m ⊕ Fin m → K}
    (hu0 : u ≠ 0) :
    Nat.card {x : Fin m ⊕ Fin m → K // spForm m K x u = 0} =
      Nat.card K ^ (Fintype.card (Fin m ⊕ Fin m) - 1) := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, spForm m K y u ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (spForm_nondegenerate.2 u h)
  let f : (Fin m ⊕ Fin m → K) →ₗ[K] K := (spForm m K).flip u
  have hf : ∀ x, f x = spForm m K x u := fun x => rfl
  have hsurj : Function.Surjective f := fun c =>
    ⟨(c / f y) • y, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ (by rw [hf]; exact hy)]⟩
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at hrank
  have hker : Module.finrank K (LinearMap.ker f) = Fintype.card (Fin m ⊕ Fin m) - 1 := by omega
  have hcard : Nat.card {x : Fin m ⊕ Fin m → K // spForm m K x u = 0} =
      Nat.card (LinearMap.ker f) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [LinearMap.mem_ker, hf])
  rw [hcard, Module.natCard_eq_pow_finrank (K := K), hker]

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.sp_points_flag (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z) {m : ℕ} (hm : 2 ≤ m)
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin m ⊕ Fin m → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    ∃ u : Fin m ⊕ Fin m → K, u ≠ 0 ∧
      (∀ x : Fin m ⊕ Fin m → K,
        (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u) ∧
      (∀ x : Fin m ⊕ Fin m → K,
        (∃ w : ↥(Vt M (LB M Q B) B Z t),
          (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔ spForm m K x u = 0) ∧
      ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = LspGL m K u := by
  classical
  obtain ⟨nn, γ, M₀, h, θ, hθ, u, hu0, hBiff, hW⟩ :=
    hc.sp_perp_data h34 hs hnotQB hK hm φ hφ hker ψ hψ
  have ht : t ∈ LB M Q B := hs.mem
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hBZ : ∀ y ∈ B ⊔ Z, ∃ b ∈ B, ∃ z ∈ Z, y = b * z := fun y hy =>
    exists_mul_of_mem_sup (fun b hb z hz => by
      have := hc.conj_Z_of_mem_Q (hc.le hb) hz
      calc b * z = (b * z * b⁻¹) * b := by group
        _ = z * b := by rw [this]) hy
  have hflag := fun s => commFlag_iff (V := Vt M (LB M Q B) B Z t) (B := B)
    (W := Vt M (LB M Q B) B Z t ⊓ QB B) φ ψ hψ hVR hZV hBV inf_le_left
    (le_inf hZV (hc.Z_le_QB).1) hBZ (u := u) (H := fun x => spForm m K x u = 0) hBiff hW s
  have hcnt := hc.card_map_LB_ge h34 hs hK φ hker ψ h θ hθ {x | spForm m K x u = 0} hW
    (fun c x hx => by
      show spForm m K (c • x) u = 0
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, show spForm m K x u = 0 from hx, mul_zero])
    (card_spForm_perp hu0)
  have hLsub : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ ≤ LspGL m K u := by
    rintro _ ⟨l, hl, rfl⟩
    have hlL : (l : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hl
    refine (mem_LspGL_iff_flag hu0).mpr ⟨hφ ▸ MonoidHom.mem_range.mpr ⟨l, rfl⟩, ?_⟩
    exact (hflag l).mp (hc.LB_flag h35 ht hs.notQ hlL)
  have hK4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  have hcardgt : Nat.card K <
      Nat.card (((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ) := by
    have h2 : Nat.card K ^ 2 ≤ Nat.card K ^ (Fintype.card (Fin m ⊕ Fin m) - 2) :=
      Nat.pow_le_pow_right (by omega) (by simp [Fintype.card_sum]; omega)
    have h3 : Nat.card K < Nat.card K ^ 2 := by nlinarith
    exact lt_of_lt_of_le (lt_of_lt_of_le h3 h2) hcnt
  exact ⟨u, hu0, hBiff, hW, sp_eq_LspGL_of_normalized hK4 hu0 _ hLsub
    (fun A hA hAu l hl => hc.map_LB_normalized hs φ hφ ψ hψ hBiff hA hAu l hl) hcardgt⟩

theorem Ctx.root_sp (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z) {m : ℕ} (hm : 2 ≤ m)
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin m ⊕ Fin m → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (r : ↥(Rt M (LB M Q B) t)) :
    (r : G) ∈ LB M Q B ⊔ hc.CN t ↔
      ((∀ b ∈ B, ⁅(r : G), b⁆ ∈ Z) ∧
        (∀ v ∈ Vt M (LB M Q B) B Z t ⊓ QB B, ⁅(r : G), v⁆ ∈ B ⊔ Z) ∧
        (∀ v ∈ Vt M (LB M Q B) B Z t, ⁅(r : G), v⁆ ∈ Vt M (LB M Q B) B Z t ⊓ QB B)) := by
  classical
  obtain ⟨u, hu0, hBiff, hW, hLeq⟩ :=
    hc.sp_points_flag h34 hs hnotQB hK hm φ hφ hker ψ hψ
  have ht : t ∈ LB M Q B := hs.mem
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBZ : ∀ y ∈ B ⊔ Z, ∃ b ∈ B, ∃ z ∈ Z, y = b * z := fun y hy =>
    exists_mul_of_mem_sup (fun b hb z hz => by
      have := hc.conj_Z_of_mem_Q (hc.le hb) hz
      calc b * z = (b * z * b⁻¹) * b := by group
        _ = z * b := by rw [this]) hy
  have hflag := fun s => commFlag_iff (V := Vt M (LB M Q B) B Z t) (B := B)
    (W := Vt M (LB M Q B) B Z t ⊓ QB B) φ ψ hψ hVR hZV hBV inf_le_left
    (le_inf hZV (hc.Z_le_QB).1) hBZ (u := u) (H := fun x => spForm m K x u = 0) hBiff hW s
  rw [mem_sup_iff_map_mem φ hker (fun x hx => (Ctx.mem_CN.mp hx).1) (le_Rt (LB M Q B) ht) hLeq r,
    mem_LspGL_iff_flag hu0, ← hflag r]
  exact ⟨fun hh => hh.2, fun hh => ⟨hφ ▸ MonoidHom.mem_range.mpr ⟨r, rfl⟩, hh⟩⟩

end CFSG.RankThree.GF2n.Stroth80
