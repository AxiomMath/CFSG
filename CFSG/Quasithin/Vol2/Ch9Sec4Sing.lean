module

public import CFSG.Quasithin.Vol2.Ch9Lem943

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H CFSG.Quasithin.E3 Matrix

namespace Om4Pt

variable {K : Type} [Field K]

theorem det_map_ringEquiv (τ : K ≃+* K) (X : Matrix (Fin 2) (Fin 2) K) :
    (X.map τ).det = τ X.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp [map_sub, map_mul]

theorem det_eq_zero_iff_of_form {A B : GL (Fin 2) K} {τ : K ≃+* K} {φ : MulAut (Om4.VM K)}
    (hφ : φ = Om4.lr A B * Om4.frM τ ∨ φ = Om4.lr A B * Om4.frM τ * Om4.trM) (X : Om4.VM K) :
    (Multiplicative.toAdd (φ X)).det = 0 ↔ (Multiplicative.toAdd X).det = 0 := by
  have hA : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A) |>.ne_zero
  have hB : (B : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit B) |>.ne_zero
  have key : ∀ Y : Om4.VM K,
      (Multiplicative.toAdd ((Om4.lr A B * Om4.frM τ) Y)).det = 0 ↔
        (Multiplicative.toAdd Y).det = 0 := by
    intro Y
    rw [MulAut.mul_apply, Om4.toAdd_lr, Om4.toAdd_frM, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, det_map_ringEquiv]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hA
        · exact (map_eq_zero_iff τ τ.injective).mp h
      · exact absurd h hB
    · intro h
      rw [h, map_zero, mul_zero, zero_mul]
  rcases hφ with rfl | rfl
  · exact key X
  · have e1 : (Om4.lr A B * Om4.frM τ * Om4.trM : MulAut (Om4.VM K)) X =
        (Om4.lr A B * Om4.frM τ) (Om4.trM X) := rfl
    rw [e1, key, Om4.toAdd_trM, Matrix.det_transpose]

end Om4Pt

theorem card_le_mul_card_centralizer {G : Type*} [Group G] [Finite G] (H : Subgroup G) (u : G)
    (S : Finset G) (hS : ∀ h ∈ H, h * u * h⁻¹ ∈ S) :
    Nat.card H ≤ S.card * Nat.card ↥(H ⊓ Subgroup.centralizer ({u} : Set G)) := by
  classical
  set C : Subgroup ↥H := (H ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf H with hC
  have h1 : Nat.card ↥H = Nat.card (↥H ⧸ C) * Nat.card C :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have h2 : Nat.card C = Nat.card ↥(H ⊓ Subgroup.centralizer ({u} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrel : ∀ a b : ↥H, (a : G) * u * (a : G)⁻¹ = (b : G) * u * (b : G)⁻¹ ↔ a⁻¹ * b ∈ C := by
    intro a b
    rw [hC, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine ⟨(a⁻¹ * b).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      show (a : G)⁻¹ * b * u = u * ((a : G)⁻¹ * b)
      calc (a : G)⁻¹ * b * u = (a : G)⁻¹ * ((b : G) * u * (b : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * ((a : G) * u * (a : G)⁻¹) * b := by rw [← h]
        _ = u * ((a : G)⁻¹ * b) := by group
    · rintro ⟨-, h⟩
      have h' : (a : G)⁻¹ * b * u = u * ((a : G)⁻¹ * b) :=
        Subgroup.mem_centralizer_singleton_iff.mp h
      calc (a : G) * u * (a : G)⁻¹ = (a : G) * (u * ((a : G)⁻¹ * b)) * (b : G)⁻¹ := by group
        _ = (a : G) * ((a : G)⁻¹ * b * u) * (b : G)⁻¹ := by rw [h']
        _ = (b : G) * u * (b : G)⁻¹ := by group
  let f : ↥H ⧸ C → ↥S := Quotient.lift
    (fun h : ↥H => (⟨(h : G) * u * (h : G)⁻¹, hS h h.2⟩ : ↥S))
    (fun a b hab => Subtype.ext ((hrel a b).mpr (QuotientGroup.leftRel_apply.mp hab)))
  have hf : Function.Injective f := by
    intro q q'
    induction q using Quotient.inductionOn with
    | h a =>
      induction q' using Quotient.inductionOn with
      | h b =>
        intro h
        exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hrel a b).mp
          (congrArg Subtype.val h)))
  have h3 : Nat.card (↥H ⧸ C) ≤ S.card := by
    calc Nat.card (↥H ⧸ C) ≤ Nat.card ↥S := Nat.card_le_card_of_injective f hf
      _ = S.card := by simp
  rw [h1, h2]
  exact Nat.mul_le_mul_right _ h3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem exists_mem_fsuM_conj_eq (h3108 : Stmt3_2_10_eight) {x g : G} (hx : x ∈ fsuV T I)
    (hgx : g * x * g⁻¹ ∈ fsuV T I) : ∃ m ∈ fsuM T L, m⁻¹ * x * m = g * x * g⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  set P : Sylow 2 G := hfsu.sylow.1.toSylow hfsu.sylow.2 with hP
  have hPT : (P : Subgroup G) = T := IsPGroup.toSylow_coe hfsu.sylow.1 hfsu.sylow.2
  have hWT : thompsonJ T ≤ P := hPT ▸ thompsonJ_le_self T
  have hW : IsWeaklyClosedIn (thompsonJ T) P := hPT ▸ Prop3210.thompsonJ_isWeaklyClosedIn
  have hA : ∀ w ∈ thompsonJ T, ∀ a ∈ ({x} : Set G), w * a = a * w := by
    rintro w hw a rfl
    exact (Subgroup.mem_centralizer_iff.mp (S.hJ hw) a hx).symm
  have hB : ∀ w ∈ thompsonJ T, ∀ a ∈ ({x} : Set G),
      w * (g⁻¹⁻¹ * a * g⁻¹) = (g⁻¹⁻¹ * a * g⁻¹) * w := by
    rintro w hw a rfl
    rw [inv_inv]
    exact (Subgroup.mem_centralizer_iff.mp (S.hJ hw) _ hgx).symm
  obtain ⟨m, hmN, hm⟩ := burnside_fusion_pointwise P hWT hW hA hB
  refine ⟨m, (h3108 G T L I (fsuV T I) hfsu S.isVplus_V S.hJ (thompsonJ T)
    (hfsu.sylow.1.to_le (thompsonJ_le_self T)) le_rfl).2 hmN, ?_⟩
  have h := hm x rfl
  rwa [inv_inv] at h

end Setup

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem det_conj_eq_zero_iff {m : G} (hm : m ∈ fsuM T L) {v : G} (hv : v ∈ fsuV T I)
    (hmv : m * v * m⁻¹ ∈ fsuV T I) :
    (Multiplicative.toAdd (e ⟨m * v * m⁻¹, hmv⟩)).det = 0 ↔
      (Multiplicative.toAdd (e ⟨v, hv⟩)).det = 0 := by
  obtain ⟨A, B, τ, hform⟩ := hc.exists_form hm
  rw [S.e_conj_M e hm ⟨v, hv⟩ hmv]
  exact Om4Pt.det_eq_zero_iff_of_form hform _

theorem card_fsuV (h2 : n = 2) : Nat.card ↥(fsuV T I) = 256 := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  rw [Nat.card_congr e.toEquiv, show Nat.card (Om4.VM K) = Nat.card (Fin 2 → Fin 2 → K) from rfl,
    Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := K), hK4]
  simp

theorem mem_normalizer_conj_of_card (hr : (3 : ℕ∞) < rParam (fsuV T I)) (h2 : n = 2)
    {g u : G} (hu : u ∈ fsuV T I) {B : Subgroup G} (hBV : B ≤ conjSubgroup (fsuV T I) g)
    (hBM : B ≤ fsuM T L) (hBu : B ≤ Subgroup.centralizer ({u} : Set G)) (hB : 32 ≤ Nat.card B) :
    u ∈ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := by
  set A := conjSubgroup (fsuV T I) g with hA
  have hA2 : IsPGroup 2 ↥A := isPGroup_conjSubgroup S.isPGroup_fsuV g
  have hAcard : Nat.card ↥A = 256 := by rw [hA, card_conjSubgroup, hc.card_fsuV h2]
  have hm3 : mQuot A B ≤ 3 := by
    have h := card_eq_two_pow_mul hA2 hBV
    rw [hAcard] at h
    by_contra hlt
    push Not at hlt
    have h4 : 2 ^ 4 ≤ 2 ^ mQuot A B := Nat.pow_le_pow_right (by norm_num) hlt
    nlinarith
  have huC : u ∈ fsuV T I ⊓ Subgroup.centralizer (B : Set G) :=
    ⟨hu, Subgroup.mem_centralizer_iff.mpr fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.mp (hBu hb)⟩
  have hCN : fsuV T I ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    by_contra hle
    have h3 := e3_4_one (le_inf hBV (hBM.trans S.hMN)) hle
    have h4 : (3 : ℕ∞) < (mQuot A B : ℕ∞) := lt_of_lt_of_le hr h3
    have h5 : 3 < mQuot A B := by exact_mod_cast h4
    omega
  exact hCN huC

theorem comm_eq_one_of_det_eq_zero (hr : (3 : ℕ∞) < rParam (fsuV T I))
    (h3108 : Stmt3_2_10_eight) (h2 : n = 2) {g u a : G}
    (hu : u ∈ fsuV T I) (ha : a ∈ conjSubgroup (fsuV T I) g) {B : Subgroup G}
    (hBV : B ≤ conjSubgroup (fsuV T I) g) (hBM : B ≤ fsuM T L)
    (hBu : B ≤ Subgroup.centralizer ({u} : Set G)) (hB : 32 ≤ Nat.card B)
    (hx : u * a * u⁻¹ * a⁻¹ ∈ fsuV T I)
    (hdet : (Multiplicative.toAdd (e ⟨u * a * u⁻¹ * a⁻¹, hx⟩)).det = 0) :
    u * a * u⁻¹ * a⁻¹ = 1 := by
  classical
  have huN := hc.mem_normalizer_conj_of_card hr h2 hu hBV hBM hBu hB
  set m' := g * u * g⁻¹ with hm'
  have hm'M : m' ∈ fsuM T L := by
    have h3 : u ∈ conjSubgroup (Subgroup.normalizer (fsuV T I : Set G)) g := by
      rw [conjSubgroup_normalizer]
      exact huN
    exact S.hNM (mem_conjSubgroup_iff.mp h3)
  have hmem : ∀ b ∈ B, g * b * g⁻¹ ∈ fsuV T I ⊓ Subgroup.centralizer ({m'} : Set G) := by
    intro b hb
    refine ⟨mem_conjSubgroup_iff.mp (hBV hb), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hb' : b * u = u * b := Subgroup.mem_centralizer_singleton_iff.mp (hBu hb)
    calc g * b * g⁻¹ * m' = g * (b * u) * g⁻¹ := by rw [hm']; group
      _ = g * (u * b) * g⁻¹ := by rw [hb']
      _ = m' * (g * b * g⁻¹) := by rw [hm']; group
  have hcard : 32 ≤ Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer ({m'} : Set G)) := by
    let f : ↥B → ↥(fsuV T I ⊓ Subgroup.centralizer ({m'} : Set G)) :=
      fun b => ⟨g * b * g⁻¹, hmem b b.2⟩
    have hf : Function.Injective f := by
      intro b b' h
      have h' : g * (b : G) * g⁻¹ = g * b' * g⁻¹ := congrArg Subtype.val h
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
    exact hB.trans (Nat.card_le_card_of_injective f hf)
  have hv : g * a * g⁻¹ ∈ fsuV T I := mem_conjSubgroup_iff.mp ha
  have e1 : m' * (g * a * g⁻¹) * m'⁻¹ * (g * a * g⁻¹)⁻¹ =
      g * (u * a * u⁻¹ * a⁻¹) * g⁻¹ := by
    rw [hm']; group
  rcases hc.centralizer_classify h2 hm'M hcard with hmC | ⟨X₁, hX₁, -, hcomm⟩
  ·
    have h3 : g * a * g⁻¹ * m' = m' * (g * a * g⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hmC _ hv
    have h4 : g * (u * a * u⁻¹ * a⁻¹) * g⁻¹ = 1 := by
      rw [← e1, ← h3]
      group
    exact conj_eq_one_iff.mp h4
  ·
    have h3 := hcomm _ hv
    rw [e1] at h3
    set x := u * a * u⁻¹ * a⁻¹ with hxdef
    have hgx : g * x * g⁻¹ ∈ fsuV T I := inV_le e _ h3
    obtain ⟨m, hmM, hm⟩ := S.exists_mem_fsuM_conj_eq h3108 hx hgx
    have hmx : m⁻¹ * x * m⁻¹⁻¹ ∈ fsuV T I := by rw [inv_inv, hm]; exact hgx
    have hdet' : (Multiplicative.toAdd (e ⟨g * x * g⁻¹, hgx⟩)).det = 0 := by
      have h4 := hc.det_conj_eq_zero_iff ((fsuM T L).inv_mem hmM) hx hmx
      have e2 : (⟨g * x * g⁻¹, hgx⟩ : ↥(fsuV T I)) = ⟨m⁻¹ * x * m⁻¹⁻¹, hmx⟩ := by
        apply Subtype.ext
        show g * x * g⁻¹ = m⁻¹ * x * m⁻¹⁻¹
        rw [inv_inv, hm]
      rw [e2, h4]
      exact hdet
    obtain ⟨hgx', c, hcX⟩ := mem_inV.mp h3
    have h5 : (c • X₁).det = 0 := by
      rw [← hcX]
      exact hdet'
    rw [Matrix.det_smul, Fintype.card_fin] at h5
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp h5 with h | h
      · exact pow_eq_zero_iff (by norm_num) |>.mp h
      · exact absurd h hX₁
    rw [hc0, zero_smul] at hcX
    have h6 : e ⟨g * x * g⁻¹, hgx'⟩ = 1 := Multiplicative.toAdd.injective hcX
    have h7 : g * x * g⁻¹ = 1 := congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h6)
    exact conj_eq_one_iff.mp h7

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
