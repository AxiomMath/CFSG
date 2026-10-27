module

public import CFSG.Quasithin.Vol2.Ch9FactsFrob
public import CFSG.Quasithin.Vol2.Ch9Lem926

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

section Model

variable {K : Type} [Field K]

@[expose] def diagT (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 2) K) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two] at ha hb ⊢
    rw [ha.1, ha.2, hb.1, hb.2]
    simp
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two] at ha ⊢
    simp [ha.1, ha.2]

@[expose] def utT (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 2) K) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two] at ha hb ⊢
    rw [ha, hb, zero_mul, mul_zero, add_zero]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two] at ha ⊢
    simp [ha]

theorem mem_utT {g : SpecialLinearGroup (Fin 2) K} :
    g ∈ utT K ↔ (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
  Iff.rfl

theorem uni_le_utT : uni K ≤ utT K := fun g hg => by
  obtain ⟨c, hc⟩ := mem_uni_iff.mp hg
  rw [mem_utT, hc]
  rfl

theorem diagT_le_utT : diagT K ≤ utT K := fun _ hg => hg.2

@[expose] def diagOf (a : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two_of]⟩

theorem coe_diagOf (a : Kˣ) :
    (diagOf a : Matrix (Fin 2) (Fin 2) K) = !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] := rfl

theorem diagOf_mem (a : Kˣ) : diagOf a ∈ diagT K := ⟨rfl, rfl⟩

@[expose] noncomputable def diagEquiv (K : Type) [Field K] : Kˣ ≃ ↥(diagT K) where
  toFun a := ⟨diagOf a, diagOf_mem a⟩
  invFun g := Units.mk0 (((g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0)
    (by
      intro h0
      have h := (g : SpecialLinearGroup (Fin 2) K).2
      rw [Matrix.det_fin_two, h0, g.2.1] at h
      simp at h)
  left_inv a := Units.ext rfl
  right_inv g := by
    obtain ⟨⟨g, hg⟩, h01, h10⟩ := g
    change g 0 1 = 0 at h01
    change g 1 0 = 0 at h10
    have hdet : g 0 0 * g 1 1 = 1 := by
      have h := hg
      rw [Matrix.det_fin_two, h01, h10, mul_zero, sub_zero] at h
      exact h
    have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    apply Subtype.ext
    apply Subtype.ext
    show !![g 0 0, 0; 0, ((Units.mk0 (g 0 0) ha)⁻¹ : Kˣ)] = g
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact h01.symm
    · exact h10.symm
    · show (Units.mk0 (g 0 0) ha)⁻¹.val = g 1 1
      rw [Units.val_inv_eq_inv_val, Units.val_mk0]
      exact (eq_inv_of_mul_eq_one_right hdet).symm

theorem card_diagT [Finite K] : Nat.card ↥(diagT K) = Nat.card K - 1 := by
  rw [← Nat.card_congr (diagEquiv K), Nat.card_units]

theorem exists_uni_mul_diag {g : SpecialLinearGroup (Fin 2) K} (hg : g ∈ utT K) :
    ∃ u ∈ uni K, ∃ d ∈ diagT K, g = u * d := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_two, show (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 from hg, mul_zero,
      sub_zero] at h
    exact h
  have ha : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  set a := Units.mk0 _ ha with hadef
  refine ⟨g * (diagOf a)⁻¹, ?_, diagOf a, diagOf_mem a, by rw [inv_mul_cancel_right]⟩
  refine mem_uni_iff.mpr ⟨(g : Matrix (Fin 2) (Fin 2) K) 0 1 * (a : K), ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_diagOf,
    Matrix.adjugate_fin_two]
  have hg10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hg
  have hinv : ((a⁻¹ : Kˣ) : K) = (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    rw [Units.val_inv_eq_inv_val, hadef, Units.val_mk0]
    exact (eq_inv_of_mul_eq_one_right hdet).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hg10, hadef]
  all_goals first
    | exact mul_inv_cancel₀ ha
    | exact hdet
    | (rw [mul_comm]; exact hdet)

theorem utT_le_normalizer_uni : utT K ≤ Subgroup.normalizer (uni K : Set _) := by
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun u => ⟨fun hu => conj_mem_uni hg hu, fun hu => ?_⟩
  have := conj_mem_uni ((utT K).inv_mem hg) hu
  simpa [mul_assoc] using this

theorem normalizer_uni_prod_le :
    Subgroup.normalizer (((uni K).prod (uni K) : Subgroup _) : Set
      (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K)) ≤ (utT K).prod (utT K) := by
  intro γ hγ
  have hγ' := Subgroup.inv_mem _ hγ
  have h1 : ∀ δ ∈ Subgroup.normalizer (((uni K).prod (uni K) : Subgroup _) : Set
      (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K)), ∀ u ∈ uni K,
      δ.1 * u * δ.1⁻¹ ∈ uni K := fun δ hδ u hu =>
    ((Subgroup.mem_normalizer_iff.mp hδ (u, 1)).mp ⟨hu, (uni K).one_mem⟩).1
  have h2 : ∀ δ ∈ Subgroup.normalizer (((uni K).prod (uni K) : Subgroup _) : Set
      (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K)), ∀ u ∈ uni K,
      δ.2 * u * δ.2⁻¹ ∈ uni K := fun δ hδ u hu =>
    ((Subgroup.mem_normalizer_iff.mp hδ (1, u)).mp ⟨(uni K).one_mem, hu⟩).2
  have hn1 : γ.1 ∈ Subgroup.normalizer (uni K : Set _) := by
    refine Subgroup.mem_normalizer_iff.mpr fun u => ⟨h1 γ hγ u, fun hu => ?_⟩
    have := h1 γ⁻¹ hγ' _ hu
    simpa [mul_assoc] using this
  have hn2 : γ.2 ∈ Subgroup.normalizer (uni K : Set _) := by
    refine Subgroup.mem_normalizer_iff.mpr fun u => ⟨h2 γ hγ u, fun hu => ?_⟩
    have := h2 γ⁻¹ hγ' _ hu
    simpa [mul_assoc] using this
  exact ⟨FactsFrob.ut_of_mem_normalizer_uni hn1, FactsFrob.ut_of_mem_normalizer_uni hn2⟩

theorem utT_prod_le_normalizer :
    (utT K).prod (utT K) ≤ Subgroup.normalizer (((uni K).prod (uni K) : Subgroup _) : Set
      (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K)) := by
  intro γ hγ
  have h1 := utT_le_normalizer_uni hγ.1
  have h2 := utT_le_normalizer_uni hγ.2
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  rw [Subgroup.mem_prod, Subgroup.mem_prod]
  exact and_congr (Subgroup.mem_normalizer_iff.mp h1 x.1) (Subgroup.mem_normalizer_iff.mp h2 x.2)

theorem uni_prod_sup_diagT :
    (uni K).prod (uni K) ⊔ (diagT K).prod (diagT K) = (utT K).prod (utT K) := by
  refine le_antisymm (sup_le (Subgroup.prod_mono uni_le_utT uni_le_utT)
    (Subgroup.prod_mono diagT_le_utT diagT_le_utT)) fun γ hγ => ?_
  obtain ⟨u₁, hu₁, d₁, hd₁, h₁⟩ := exists_uni_mul_diag hγ.1
  obtain ⟨u₂, hu₂, d₂, hd₂, h₂⟩ := exists_uni_mul_diag hγ.2
  have : γ = (u₁, u₂) * (d₁, d₂) := Prod.ext h₁ h₂
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hu₁, hu₂⟩) (Subgroup.mem_sup_right ⟨hd₁, hd₂⟩)

theorem odd_card_diagT_prod [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Odd (Nat.card ↥((diagT K).prod (diagT K))) := by
  rw [Nat.card_congr ((diagT K).prodEquiv (diagT K)).toEquiv, Nat.card_prod, card_diagT, hK]
  have h : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
    (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  exact h.mul h

end Model

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)

include S in
theorem isSylowTwoOf_T_inf_L0_normalizer :
    IsSylowTwoOf (T ⊓ fsuL0 T L)
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)) := by
  set P₀ := T ⊓ fsuL0 T L with hP₀
  set N₀ := fsuL0 T L ⊓ Subgroup.normalizer (P₀ : Set G) with hN₀
  have hP₀N₀ : P₀ ≤ N₀ := fun x hx => ⟨hx.2, Subgroup.le_normalizer hx⟩
  refine ⟨hP₀N₀, S.hyp.fsu.sylow.1.to_le inf_le_left, fun h2 => ?_⟩
  apply S.isSylowTwoOf_T_inf_L0.2.2
  show 2 ∣ P₀.relIndex (fsuL0 T L)
  rw [← Subgroup.relIndex_mul_relIndex P₀ N₀ (fsuL0 T L) hP₀N₀ inf_le_left]
  exact h2.mul_right _

namespace IsCoord

variable {S} {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem conj {γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
    (hγ : γ ∈ (uni K).prod (uni K)) :
    S.IsCoord (e.trans (Om4.rho γ⁻¹)) ((MulAut.conj γ⁻¹).toMonoidHom.comp ψ) := by
  refine ⟨hc.card, (MulAut.conj γ⁻¹).surjective.comp hc.surj, fun k => ?_, ?_⟩
  · refine MulEquiv.ext fun X => ?_
    have h1 := congrArg (fun φ : MulAut (Om4.VM K) => φ ((Om4.rho γ⁻¹).symm X)) (hc.act k)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply] at h1
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
      MonoidHom.comp_apply]
    have hcj : (MulAut.conj γ⁻¹).toMonoidHom (ψ k) = γ⁻¹ * ψ k * γ := by simp
    have hsymm : (Om4.rho γ⁻¹).symm X = Om4.rho γ X := by rw [map_inv]; rfl
    rw [h1, hcj, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hsymm]
  · rw [← Subgroup.map_map, hc.sylow]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (MulAut.conj γ⁻¹).toMonoidHom x = γ⁻¹ * x * γ := by simp
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hγ) hx) hγ
    · intro hy
      refine ⟨γ * y * γ⁻¹,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ hy) (Subgroup.inv_mem _ hγ), ?_⟩
      simp [mul_assoc]

theorem mem_T_iff (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (k : ↥(fsuL0 T L)) :
    (k : G) ∈ T ↔ ψ k ∈ (uni K).prod (uni K) := by
  constructor
  · intro hk
    rw [← hc.sylow]
    exact ⟨k, Subgroup.mem_subgroupOf.mpr ⟨hk, k.2⟩, rfl⟩
  · exact hc.mem_T_of_mem_uni h37c h38c k

theorem map_normalizer (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) :
    ((fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)).subgroupOf
      (fsuL0 T L)).map ψ = (utT K).prod (utT K) := by
  apply le_antisymm
  · rintro _ ⟨k, hk, rfl⟩
    have hkN : (k : G) ∈ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) :=
      (Subgroup.mem_subgroupOf.mp hk).2
    apply normalizer_uni_prod_le
    refine Subgroup.mem_normalizer_iff.mpr fun γ => ⟨fun hγ => ?_, fun hγ => ?_⟩
    · obtain ⟨u, rfl⟩ := hc.surj γ
      have hu : (u : G) ∈ T := (hc.mem_T_iff h37c h38c u).mpr hγ
      have h1 : (k : G) * u * (k : G)⁻¹ ∈ T ⊓ fsuL0 T L :=
        (Subgroup.mem_normalizer_iff.mp hkN u).mp ⟨hu, u.2⟩
      have h2 := (hc.mem_T_iff h37c h38c (k * u * k⁻¹)).mp h1.1
      rwa [map_mul, map_mul, map_inv] at h2
    · obtain ⟨u, rfl⟩ := hc.surj γ
      have h1 : ψ (k * u * k⁻¹) ∈ (uni K).prod (uni K) := by
        rwa [map_mul, map_mul, map_inv]
      have h2 := (hc.mem_T_iff h37c h38c _).mpr h1
      have h3 : (u : G) ∈ T ⊓ fsuL0 T L :=
        (Subgroup.mem_normalizer_iff.mp hkN u).mpr ⟨h2, (k * u * k⁻¹).2⟩
      exact (hc.mem_T_iff h37c h38c u).mp h3.1
  · intro γ hγ
    obtain ⟨k, rfl⟩ := hc.surj γ
    have hN := utT_prod_le_normalizer hγ
    refine ⟨k, Subgroup.mem_subgroupOf.mpr ⟨k.2, ?_⟩, rfl⟩
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have hxL : x ∈ fsuL0 T L := hx.2
      have h1 := (hc.mem_T_iff h37c h38c ⟨x, hxL⟩).mp hx.1
      have h2 : ψ (k * ⟨x, hxL⟩ * k⁻¹) ∈ (uni K).prod (uni K) := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hN _).mp h1
      exact ⟨(hc.mem_T_iff h37c h38c _).mpr h2, (k * ⟨x, hxL⟩ * k⁻¹).2⟩
    · have hxL : x ∈ fsuL0 T L := by
        have := (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem ((fsuL0 T L).inv_mem k.2) hx.2) k.2
        simpa [mul_assoc] using this
      have h1 := (hc.mem_T_iff h37c h38c ⟨(k : G) * x * (k : G)⁻¹, hx.2⟩).mp hx.1
      have h3 : (⟨(k : G) * x * (k : G)⁻¹, hx.2⟩ : ↥(fsuL0 T L)) = k * ⟨x, hxL⟩ * k⁻¹ := rfl
      rw [h3, map_mul, map_mul, map_inv] at h1
      have h2 : ψ ⟨x, hxL⟩ ∈ (uni K).prod (uni K) :=
        (Subgroup.mem_normalizer_iff.mp hN _).mpr h1
      exact ⟨(hc.mem_T_iff h37c h38c _).mpr h2, hxL⟩

end IsCoord

theorem exists_isCoord_diag (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G))) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2) (e : ↥(fsuV T I) ≃* Om4.VM K)
      (ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K),
      S.IsCoord e ψ ∧ (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, e, ψ, hc⟩ := S.exists_isCoord
  have hn1 : 1 ≤ n := by have := S.two_le; omega
  set P := (uni K).prod (uni K) with hP
  set Hd := (diagT K).prod (diagT K) with hHd
  set N₀ := fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hN₀
  set Dψ := (D.subgroupOf (fsuL0 T L)).map ψ with hDψ
  have hP2 : IsPGroup 2 P := (isSylowTwoOf_uni_prod (K := K) hn1 hc.natCard).2.1
  have hHodd : Odd (Nat.card Hd) := odd_card_diagT_prod hn1 hc.natCard
  have hDodd : Odd (Nat.card Dψ) := by
    refine hD.2.1.of_dvd_nat ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hD.1.trans inf_le_left)).toEquiv]
  have hDN : D.subgroupOf (fsuL0 T L) ≤ N₀.subgroupOf (fsuL0 T L) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hD.1 (Subgroup.mem_subgroupOf.mp hx))
  have hDP : Dψ ≤ Subgroup.normalizer (P : Set _) :=
    (Subgroup.map_mono hDN).trans (hc.map_normalizer h37c h38c ▸ utT_prod_le_normalizer)
  have hHP : Hd ≤ Subgroup.normalizer (P : Set _) :=
    (Subgroup.prod_mono diagT_le_utT diagT_le_utT).trans utT_prod_le_normalizer
  have hN₀eq : N₀ = (T ⊓ fsuL0 T L) ⊔ D :=
    le_antisymm (Vol2.Ch10.SecB.C11AmS.le_sup_of_hall S.isSylowTwoOf_T_inf_L0_normalizer hD)
      (sup_le S.isSylowTwoOf_T_inf_L0_normalizer.1 hD.1)
  have hsup : P ⊔ Hd = P ⊔ Dψ := by
    rw [uni_prod_sup_diagT, ← hc.map_normalizer h37c h38c, ← hN₀, hN₀eq,
      Subgroup.subgroupOf_sup inf_le_right (hD.1.trans inf_le_left), Subgroup.map_sup, hc.sylow]
  obtain ⟨γ, hγ, hγD⟩ := Vol2.Ch10.SecB.C11AmS.exists_conj_of_complement hP2 hHodd hHP hDP
    (Vol2.Ch10.SecB.C11AmS.inf_eq_bot_of_odd hP2 hHodd)
    (Vol2.Ch10.SecB.C11AmS.inf_eq_bot_of_odd hP2 hDodd) hsup
  refine ⟨K, inferInstance, inferInstance, inferInstance, _, _, hc.conj (P.inv_mem hγ), ?_⟩
  rw [← Subgroup.map_map, ← hDψ, hγD, Subgroup.map_map]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨x, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

end Setup

end CFSG.Quasithin.H13.Ch9
