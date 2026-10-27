module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSecOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaCent
public import CFSG.RankThree.GF2n.Stroth80.Sec78ZtOm4
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndBridge

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
  CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem comm_mem_CN_of_vanish (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {y : G}
    (hyM : y ∈ M) (hyt : ⁅y, t⁆ ∈ Q) (hyV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∈ Z) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) : ⁅r, y⁆ ∈ hc.CN t := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hyN : y ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G) :=
    conjSubgroup_eq_self_iff.mp (endg_F0_Rt hc hyM hyt)
  have hrV : r ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht hr
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  refine Ctx.mem_CN.mpr ⟨?_, fun v hv => ?_⟩
  · have h1 : y * r⁻¹ * y⁻¹ ∈ Rt M (LB M Q B) t :=
      (Subgroup.mem_normalizer_iff.mp hyN r⁻¹).mp ((Rt M (LB M Q B) t).inv_mem hr)
    have e : ⁅r, y⁆ = r * (y * r⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Rt M (LB M Q B) t).mul_mem hr h1
  · have hv' : r⁻¹ * v * r ∈ Vt M (LB M Q B) B Z t := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrV) v).mp hv
      simpa using this
    have h1 : ⁅r * y * r⁻¹, v⁆ ∈ Z := by
      have e : ⁅r * y * r⁻¹, v⁆ = r * ⁅y, r⁻¹ * v * r⁆ * r⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hZn r hrM _ (hyV _ hv')
    have h2 : ⁅y⁻¹, v⁆ ∈ Z := by
      have e : ⁅y⁻¹, v⁆ = y⁻¹ * ⁅y, v⁆⁻¹ * y := by
        simp only [commutatorElement_def]; group
      rw [e]
      have := hZn y⁻¹ (M.inv_mem hyM) _ (Z.inv_mem (hyV v hv))
      simpa using this
    have h3 : ⁅(r * y * r⁻¹) * y⁻¹, v⁆ = (r * y * r⁻¹) * ⁅y⁻¹, v⁆ * (r * y * r⁻¹)⁻¹ *
        ⁅r * y * r⁻¹, v⁆ := by
      simp only [commutatorElement_def]; group
    have hM' : r * y * r⁻¹ ∈ M := M.mul_mem (M.mul_mem hrM hyM) (M.inv_mem hrM)
    have e2 : ⁅r, y⁆ = (r * y * r⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
    rw [e2, h3]
    exact Z.mul_mem (hZn _ hM' _ h2) h1


theorem card_Vt_orthogonal (hc : Ctx M Q Z B) {t : G} {m : ℕ} (hm : 2 ≤ m)
    (h : OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) :
    Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card Z ^ (2 * m) := by
  rcases h with ⟨K, hF, hFin, hK, hnat⟩ | ⟨K, hF, hFin, hK, b, c, hirr, hnat⟩
  · have h1 := card_of_naturalRep hnat sec39_Z_le_Vt hK
    have hι : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rwa [hι] at h1
  · have h1 := card_of_naturalRep hnat sec39_Z_le_Vt hK
    have hι : Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = 2 * m := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rwa [hι] at h1

theorem Ctx.Z_le_conjSubgroup (hc : Ctx M Q Z B) {V : Subgroup G} (hZV : Z ≤ V) {g : G}
    (hg : g ∈ M) : Z ≤ conjSubgroup g V := by
  intro z hz
  rw [mem_conjSubgroup]
  have hzZ : z ∈ conjSubgroup g Z := by
    rw [hc.conj_Z_eq hg]
    exact hz
  exact hZV (mem_conjSubgroup.mp hzZ)

theorem Ctx.conjSubgroup_le_Q (hc : Ctx M Q Z B) {V : Subgroup G} (hVQ : V ≤ Q) {g : G}
    (hg : g ∈ M) : conjSubgroup g V ≤ Q := by
  intro x hx
  rw [← hc.conj_Q_eq hg, mem_conjSubgroup]
  exact hVQ (mem_conjSubgroup.mp hx)

theorem card_sup_mul_card_inf_conj (hc : Ctx M Q Z B) {V : Subgroup G} (hZV : Z ≤ V)
    (hVQ : V ≤ Q) {g : G} (hg : g ∈ M) :
    Nat.card ↥(V ⊔ conjSubgroup g V) * Nat.card ↥(V ⊓ conjSubgroup g V) =
      Nat.card ↥V * Nat.card ↥V := by
  have hWQ : conjSubgroup g V ≤ Q := hc.conjSubgroup_le_Q hVQ hg
  have hZW : Z ≤ conjSubgroup g V := hc.Z_le_conjSubgroup hZV hg
  have hVn : V ≤ Subgroup.normalizer ((conjSubgroup g V : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv y hy
    have hyQ : y ∈ Q := hWQ hy
    have hc' : ⁅v, y⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V (hVQ hv) hyQ
    have key : v * y * v⁻¹ = ⁅v, y⁆ * y := by
      rw [commutatorElement_def]
      group
    rw [key]
    exact (conjSubgroup g V).mul_mem (hZW hc') hy
  have hprod := card_sup_mul_card_inf_of_le_normalizer hVn
  rw [card_conjSubgroup] at hprod
  rw [sup_comm, inf_comm]
  exact hprod

theorem card_sup_conj_mul_le (hc : Ctx M Q Z B) {V : Subgroup G} (hZV : Z ≤ V) (hVQ : V ≤ Q)
    {g : G} (hg : g ∈ M) :
    Nat.card ↥(V ⊔ conjSubgroup g V) * Nat.card ↥Z ≤ Nat.card ↥V * Nat.card ↥V := by
  have hZle : Nat.card ↥Z ≤ Nat.card ↥(V ⊓ conjSubgroup g V) :=
    Subgroup.card_le_of_le (le_inf hZV (hc.Z_le_conjSubgroup hZV hg))
  exact (Nat.mul_le_mul_left _ hZle).trans (card_sup_mul_card_inf_conj hc hZV hVQ hg).le

theorem comm_LB_Wt_mem_QB (hc : Ctx M Q Z B) {V : Subgroup G} (hBV : B ≤ V) {α w : G}
    (hα : α ∈ LB M Q B) (hw : w ∈ Wt Q V) : ⁅α, w⁆ ∈ QB B := by
  obtain ⟨hwQ, hwC⟩ := Subgroup.mem_inf.mp hw
  have hwB : w ∈ Subgroup.normalizer (B : Set G) :=
    Subgroup.centralizer_le_normalizer (B : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun h hh =>
        Subgroup.mem_centralizer_iff.mp hwC h (hBV hh))
  have hconj : conjSubgroup w B = B := conjSubgroup_eq_self_iff.mpr hwB
  have hQB : conjSubgroup w (QB B) = QB B := by
    have h1 := QB_conj w B
    rw [hconj] at h1
    exact h1.symm
  have hwN : w ∈ Subgroup.normalizer ((QB B : Subgroup G) : Set G) :=
    conjSubgroup_eq_self_iff.mp hQB
  have hwz : ∀ z ∈ QB B, w * z * w⁻¹ ∈ QB B := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp hwN z).mp hz
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB hα
  have hyw : ⁅y, w⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hy hwQ
  have hsZ : s * ⁅y, w⁆ * s⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hs.2) _).mp hyw
  have hsw : ⁅s, w⁆ ∈ QB B := by
    have e : ⁅s, w⁆ = s * (w * s⁻¹ * w⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (QB B).mul_mem hs.1 (hwz s⁻¹ ((QB B).inv_mem hs.1))
  have e : ⁅s * y, w⁆ = (s * ⁅y, w⁆ * s⁻¹) * ⁅s, w⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (QB B).mul_mem (hc.Z_le_QB.1 hsZ) hsw

omit [Finite G] in
theorem commutator_mul_expand (q s w : G) :
    ⁅q * s, w⁆ = ⁅q, ⁅s, w⁆⁆ * ⁅s, w⁆ * ⁅q, w⁆ := by
  simp only [commutatorElement_def]
  group

omit [Finite G] in
theorem conj_commutator_conj (g t w : G) :
    g⁻¹ * ⁅g * t * g⁻¹, w⁆ * g = ⁅t, g⁻¹ * w * g⁆ := by
  simp only [commutatorElement_def]
  group

theorem comm_conjMod_mem_conj (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {x : G} (hx : ConjMod M Q t x) :
    ∃ g ∈ M, ∀ w ∈ Q, ⁅x, w⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
  obtain ⟨-, g, hg, hq⟩ := hx
  have htM : t ∈ M := hc.LB_le_M hs.toSec5.mem
  have hsM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
  have hV : Vt M (LB M Q B) B Z t = Ut Q Z t :=
    (h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)).1
  have hZW : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    hc.Z_le_conjSubgroup sec39_Z_le_Vt hg
  obtain ⟨q₀, hq₀, rfl⟩ : ∃ q₀ ∈ Q, x = q₀ * (g * t * g⁻¹) :=
    ⟨x * (g * t * g⁻¹)⁻¹, hq, by group⟩
  refine ⟨g, hg, fun w hw => ?_⟩
  have hw' : g⁻¹ * w * g ∈ Q := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hg)) w).mp hw
    rwa [inv_inv] at h1
  have hsw : ⁅g * t * g⁻¹, w⁆ ∈ Q := by
    have h1 : g * t * g⁻¹ * w * (g * t * g⁻¹)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) w).mp hw
    rw [commutatorElement_def]
    exact Q.mul_mem h1 (Q.inv_mem hw)
  have hTc : ⁅t, g⁻¹ * w * g⁆ ∈ ⁅Q, Subgroup.zpowers t⁆ := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hw' (Subgroup.mem_zpowers t))
  have hsw' : ⁅g * t * g⁻¹, w⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [mem_conjSubgroup, hV, conj_commutator_conj]
    exact Subgroup.mem_sup_left hTc
  have hA : ⁅q₀, w⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    hZW (hc.hyp.toHyp79.comm_mem_V hq₀ hw)
  have hB : ⁅q₀, ⁅g * t * g⁻¹, w⁆⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    hZW (hc.hyp.toHyp79.comm_mem_V hq₀ hsw)
  rw [commutator_mul_expand]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hB hsw') hA

theorem natPoints_of_omegaMinusNat (hPts : Sec5NatPointsOmegaStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {r : G} (hr : Sec7A hc t r) {m : ℕ} (hm : 2 ≤ m)
    (hom : OmegaMinusNat hc t m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
      (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)
      (u u' : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K),
      Nat.card K = Nat.card Z ∧ quadMinus m K b c u = 0 ∧ quadMinus m K b c u' = 0 ∧
        u ≠ 0 ∧ u' ≠ 0 ∧ polar (quadMinus m K b c) u u' ≠ 0 ∧
        φ.range = StatedOmega (StatedQuadMinus m K b c) ∧
        φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
        SectionAct K (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z φ
          (fun g => (g : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)) ∧
        ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = LomGLMinus hm hirr u ∧
        ((conjSubgroup r (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
          LomGLMinus hm hirr u' := by
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  have hMinus' := hom
  obtain ⟨_, _, _, hK₀, _, _, _, hrep₀⟩ := hom
  have hcard₀ := card_of_naturalRep hrep₀ sec39_Z_le_Vt hK₀
  have hι₀ : Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = 2 * m := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  rw [hι₀] at hcard₀
  rcases hcases with
    ⟨m', _, φ, _, _, _, _, _, _, _, hrange, hker, hsec, _, _⟩ |
    ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩
  · exfalso
    have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
        (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
    have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
    exact omegaSignStatement_holds G M Q Z B hc t _ hm ⟨K, hKf, hKfin, hKZ, hnat⟩ hMinus'
  · have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
        (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
        (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
    have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
    exact ⟨K, hKf, hKfin, hchar, b, c, hirr, φ, u, u', hKZ, hu, hu', hu0, hu0', huu', hrange,
      hker, hsec, hLu, hLu'⟩

theorem card_Vt_inf_QB_omegaMinus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {m : ℕ} (hm : 2 ≤ m)
    (hom : OmegaMinusNat hc t m) :
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) = Nat.card Z ^ (2 * m) := by
  obtain ⟨K, fK, finK, hK, b, c, hirr, hnat⟩ := hom
  have hs5 := hs.toSec5
  have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
    Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm, hirr, hnat⟩⟩
  haveI : CharP K 2 := sec7ctr_charP hc hK
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]; omega
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite m K hirr
  have hX := addCommutantScalar_statedOmegaMinus hm hirr
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  have hsing := hc.omega_singular h34 hRoot hs5 hnatSO hK (ElemMatrixIso.minus hm hirr) hQ h3
    hX φ hφ ψ hψ
  obtain ⟨u, -, hu0, -, hW, -, -⟩ := hc.omega_points_core h34 hRoot hs5 hnatSO hK
    (ElemMatrixIso.minus hm hirr) hQ h3 hX φ hφ hker ψ hψ hsing
  have hZW0 : Z ≤ Vt M (LB M Q B) B Z t ⊓ QB B :=
    le_inf (sec39_Z_le_Vt : Z ≤ Vt M (LB M Q B) B Z t) hc.Z_le_QB.1
  have hW0card : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) =
      Nat.card Z * Nat.card K ^ (Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) - 1) := by
    have h1 := card_eq_of_secVec (Z := Z) ψ hZW0 inf_le_left
      {x | polar (quadMinus m K b c) u x = 0} (fun x => hW x)
    rw [h1]
    congr 1
    exact card_polar_perp (quadMinus m K b c) hQ hu0
  have hι : Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = 2 * m := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hpow : Nat.card Z * Nat.card Z ^ (2 * m - 1) = Nat.card Z ^ (2 * m) := by
    rw [← pow_succ', show 2 * m - 1 + 1 = 2 * m by omega]
  rw [hW0card, hι, hK, hpow]

end CFSG.RankThree.GF2n.Stroth80
