module

public import CFSG.LocalAnalysis.StandardType.GGTDModelAssemble
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBAutCard
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGWPlusUnitAutPerm
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13UnitaryDvdGen
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryDvdModel
public import CFSG.LocalAnalysis.StandardType.GGTDModelUPerm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.SpecialLinear
open CFSG.ClassicalGroups.UnitaryFlag

private def l48u1_mu (K : Type) [Field K] (m : ℕ) : Subgroup Kˣ where
  carrier := {x | x ^ m = 1}
  mul_mem' := by
    intro a b ha hb
    show (a * b) ^ m = 1
    rw [mul_pow, ha, hb, one_mul]
  one_mem' := by
    show (1 : Kˣ) ^ m = 1
    exact one_pow m
  inv_mem' := by
    intro a ha
    show (a⁻¹) ^ m = 1
    rw [inv_pow, ha, inv_one]

private theorem l48u1_diag_prod {K : Type} [Field K] {n d : ℕ}
    (hK : UnitaryFieldData 2 n K) {D : ↥(unitarySU 2 n K d)} {w : Fin d → K}
    (hD : ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal w) :
    ∏ i, w i = 1 := by
  have hunit := (mem_unitarySU_iff hK).mp D.2
  rw [hD, Matrix.det_diagonal] at hunit
  exact hunit.1

private theorem l48u1_ratio_norm_one {K : Type} [Field K] {n d : ℕ}
    (hK : UnitaryFieldData 2 n K) (hd : 3 ≤ d) {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} {a : MulAut L'} {t : Fin d → K}
    (ha : LineU.ActsDiagU φ a t) (i j : Fin d) : (t i / t j) ^ (2 ^ n + 1) = 1 := by
  by_cases hij : i = j
  · subst hij
    rw [div_self (ha.ne_zero i), one_pow]
  obtain ⟨D, hD, hDt, hact⟩ := ha
  set σ : Equiv.Perm (Fin d) := Equiv.swap i j with hσ
  set P : ↥(unitarySU 2 n K d) := LineU.permSU hK σ with hP
  have hPN : (P : GL (Fin d) K) ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.le_normalizer P.2
  set Y : ↥(unitarySU 2 n K d) := LineU.conjN D hD P * P⁻¹ with hY
  have hYeq : (Y : GL (Fin d) K) = D * (P * D⁻¹ * P⁻¹) := by
    rw [hY]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, LineU.coe_conjN]
    group
  have hYmat : ((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (fun k => t k * (t (σ⁻¹ k))⁻¹) := by
    rw [hYeq]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rw [hDt, hP, LineU.coe_permSU, LineU.coe_permGL_matrix, LineU.coe_inv_diag hDt,
        LineU.coe_permGL_inv_matrix, LineU.permMatrix_conj_diag σ (fun k => (t k)⁻¹),
        diagonal_mul_diagonal]
  have hnorm := UnitTB.diag_norm_one_of_mem_unitarySU hK hYmat i
  rw [hσ, Equiv.swap_inv, Equiv.swap_apply_left] at hnorm
  simpa [div_eq_mul_inv] using hnorm

private theorem l48u1_mu_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card (l48u1_mu K (2 ^ n + 1)) = 2 ^ n + 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hm_pos : 0 < 2 ^ n + 1 := by positivity
  haveI hcyc : IsCyclic (l48u1_mu K (2 ^ n + 1)) := isCyclic_subgroup_units _
  have hpow : ∀ a : l48u1_mu K (2 ^ n + 1), a ^ (2 ^ n + 1) = 1 :=
    fun a => Subtype.ext a.2
  have hub : Nat.card (l48u1_mu K (2 ^ n + 1)) ≤ 2 ^ n + 1 := by
    have h := IsCyclic.card_pow_eq_one_le (α := l48u1_mu K (2 ^ n + 1))
      (n := 2 ^ n + 1) hm_pos
    have hf : Finset.univ.filter (fun a : l48u1_mu K (2 ^ n + 1) => a ^ (2 ^ n + 1) = 1) =
        Finset.univ := Finset.filter_true_of_mem (fun a _ => hpow a)
    rw [hf, Finset.card_univ] at h
    rwa [Nat.card_eq_fintype_card]
  have hcardK : Fintype.card K = (2 ^ n) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hK]
  have hcard_units : Fintype.card Kˣ = (2 ^ n) ^ 2 - 1 := by
    rw [Fintype.card_units, hcardK]
  have hm_dvd : (2 ^ n + 1) ∣ Fintype.card Kˣ := by
    rw [hcard_units]
    refine ⟨2 ^ n - 1, ?_⟩
    obtain ⟨a, ha⟩ : ∃ a, 2 ^ n = a + 1 :=
      ⟨2 ^ n - 1, by have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow; omega⟩
    rw [ha]
    have e1 : (a + 1) ^ 2 = a ^ 2 + 2 * a + 1 := by ring
    have e2 : (a + 1 + 1) * (a + 1 - 1) = a ^ 2 + 2 * a := by
      rw [Nat.add_sub_cancel]
      ring
    rw [e1, e2]
    omega
  haveI : IsCyclic (⊤ : Subgroup Kˣ) := isCyclic_subgroup_units ⊤
  have htop : Fintype.card (⊤ : Subgroup Kˣ) = Fintype.card Kˣ :=
    Fintype.card_congr (Subgroup.topEquiv : (⊤ : Subgroup Kˣ) ≃* Kˣ).toEquiv
  have hm_dvd_top : (2 ^ n + 1) ∣ Fintype.card (⊤ : Subgroup Kˣ) := by
    rw [htop]; exact hm_dvd
  have hcount := IsCyclic.card_orderOf_eq_totient (α := (⊤ : Subgroup Kˣ)) hm_dvd_top
  have htot : 0 < Nat.totient (2 ^ n + 1) := Nat.totient_pos.mpr (by omega)
  obtain ⟨g, hgmem⟩ := Finset.card_pos.mp (by rw [hcount]; exact htot)
  rw [Finset.mem_filter] at hgmem
  have hgord : orderOf g = 2 ^ n + 1 := hgmem.2
  have ha : (g : Kˣ) ∈ l48u1_mu K (2 ^ n + 1) := by
    show (g : Kˣ) ^ (2 ^ n + 1) = 1
    have h1 : g ^ (2 ^ n + 1) = 1 := by rw [← hgord]; exact pow_orderOf_eq_one g
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg (fun x : (⊤ : Subgroup Kˣ) => (x : Kˣ)) h1
  have hzp : Subgroup.zpowers (g : Kˣ) ≤ l48u1_mu K (2 ^ n + 1) :=
    Subgroup.zpowers_le.mpr ha
  have hcardzp : Nat.card (Subgroup.zpowers (g : Kˣ)) = 2 ^ n + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, ← hgord]
    exact orderOf_injective (Subgroup.subtype (⊤ : Subgroup Kˣ)) (fun a b h => Subtype.ext h) g
  have hlb : 2 ^ n + 1 ≤ Nat.card (l48u1_mu K (2 ^ n + 1)) := by
    calc 2 ^ n + 1 = Nat.card (Subgroup.zpowers (g : Kˣ)) := hcardzp.symm
      _ ≤ Nat.card (l48u1_mu K (2 ^ n + 1)) :=
        Nat.card_le_card_of_injective
          (fun x : ↥(Subgroup.zpowers (g : Kˣ)) => (⟨x.1, hzp x.2⟩ : l48u1_mu K (2 ^ n + 1)))
          (fun x y h => Subtype.ext (congrArg (fun z : l48u1_mu K (2 ^ n + 1) => (z : Kˣ)) h))
  exact le_antisymm hub hlb

private noncomputable def l48u1_iota {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    l48u1_mu K (2 ^ n + 1) ≃* Multiplicative (ZMod (2 ^ n + 1)) :=
  haveI : IsCyclic (l48u1_mu K (2 ^ n + 1)) := isCyclic_subgroup_units _
  haveI : IsCyclic (Multiplicative (ZMod (2 ^ n + 1))) := inferInstance
  mulEquivOfCyclicCardEq (by
    rw [l48u1_mu_card hK]
    change 2 ^ n + 1 = Nat.card (ZMod (2 ^ n + 1))
    rw [Nat.card_eq_fintype_card, ZMod.card])

private theorem l48u1_perm_diag {K : Type} [Field K] {d : ℕ} (σ : Equiv.Perm (Fin d))
    {t s : Fin d → K} (hs : ∀ i, s i = t i * (t (σ i))⁻¹) :
    diagonal t * σ.permMatrix K * diagonal (fun i => (t i)⁻¹) =
      diagonal s * σ.permMatrix K := by
  have hmul : σ.permMatrix K * σ⁻¹.permMatrix K = 1 := by
    have h := congrArg (fun u : GL (Fin d) K => (u : Matrix (Fin d) (Fin d) K))
      (inv_mul_cancel (CFSG.RankThree.Classical.permGL σ))
    rw [Units.val_mul, LineU.coe_permGL_inv_matrix, LineU.coe_permGL_matrix,
        Units.val_one] at h
    exact h
  have hL : σ⁻¹.permMatrix K * (diagonal t * σ.permMatrix K * diagonal (fun i => (t i)⁻¹)) =
      diagonal (fun k => t (σ⁻¹ k) * (t k)⁻¹) := by
    rw [show σ⁻¹.permMatrix K * (diagonal t * σ.permMatrix K * diagonal (fun i => (t i)⁻¹)) =
        (σ⁻¹.permMatrix K * diagonal t * σ.permMatrix K) * diagonal (fun i => (t i)⁻¹) by
          rw [← mul_assoc, ← mul_assoc],
      LineU.permMatrix_conj_diag σ t, diagonal_mul_diagonal]
  have hR : σ⁻¹.permMatrix K * (diagonal s * σ.permMatrix K) =
      diagonal (fun k => t (σ⁻¹ k) * (t k)⁻¹) := by
    rw [show σ⁻¹.permMatrix K * (diagonal s * σ.permMatrix K) =
        (σ⁻¹.permMatrix K * diagonal s * σ.permMatrix K) by rw [← mul_assoc],
      LineU.permMatrix_conj_diag σ s]
    congr 1
    funext k
    rw [hs (σ⁻¹ k)]
    simp
  have h1 := hL.trans hR.symm
  calc diagonal t * σ.permMatrix K * diagonal (fun i => (t i)⁻¹)
      = 1 * (diagonal t * σ.permMatrix K * diagonal (fun i => (t i)⁻¹)) :=
        (one_mul _).symm
    _ = (σ.permMatrix K * σ⁻¹.permMatrix K) *
          (diagonal t * σ.permMatrix K * diagonal (fun i => (t i)⁻¹)) := by rw [hmul]
    _ = σ.permMatrix K * (σ⁻¹.permMatrix K *
          (diagonal t * σ.permMatrix K * diagonal (fun i => (t i)⁻¹))) := by rw [mul_assoc]
    _ = σ.permMatrix K * (σ⁻¹.permMatrix K * (diagonal s * σ.permMatrix K)) := by rw [h1]
    _ = (σ.permMatrix K * σ⁻¹.permMatrix K) * (diagonal s * σ.permMatrix K) := by rw [mul_assoc]
    _ = 1 * (diagonal s * σ.permMatrix K) := by rw [hmul]
    _ = diagonal s * σ.permMatrix K := one_mul _

theorem exists_ggTDModel_U {K : Type} [Field K] [Finite K] {n p N : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hN : 3 ≤ N) {L' : Type} [Group L']
    {φ : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 n K (N + 1)) →* L'} (hM : UnitTB.Model φ) :
    ∃ M : GGTDModel K N (2 ^ n + 1) L',
      (∀ a : MulAut L', (∃ t, M.Act a t) ↔
        ∃ t : Fin (N + 1) → K, LineU.ActsDiagU φ a t) ∧
      ∀ σ : Equiv.Perm (Fin (N + 1)), M.φ (M.Pm σ) = φ (LineU.permSU hM.field σ⁻¹) := by
  classical
  have hKf : UnitaryFieldData 2 n K := hM.field
  haveI : Fintype K := Fintype.ofFinite K
  have hd3 : 3 ≤ N + 1 := by omega
  have hd4 : 4 ≤ N + 1 := by omega
  let μ : Subgroup Kˣ := l48u1_mu K (2 ^ n + 1)
  let ι : μ ≃* Multiplicative (ZMod (2 ^ n + 1)) := l48u1_iota hK
  let Act : MulAut L' → (Fin (N + 1) → Kˣ) → Prop :=
    fun a t => LineU.ActsDiagU φ a (fun i => ((t i : Kˣ) : K))
  have act_one : Act 1 1 := by
    simpa [Act] using LineU.actsDiagU_one (n := n) (d := N + 1) φ
  have act_mul : ∀ {a b : MulAut L'} {t u : Fin (N + 1) → Kˣ},
      Act a t → Act b u → Act (a * b) (t * u) := by
    intro a b t u ha hb
    simpa [Act, Pi.mul_apply] using LineU.ActsDiagU.mul (φ := φ) ha hb
  have act_inv : ∀ {a : MulAut L'} {t : Fin (N + 1) → Kˣ}, Act a t → Act a⁻¹ t⁻¹ := by
    intro a t ha
    simpa [Act, Pi.inv_apply] using LineU.ActsDiagU.inv (φ := φ) ha
  have act_unique : ∀ {a b : MulAut L'} {t : Fin (N + 1) → Kˣ}, Act a t → Act b t → a = b := by
    intro a b t ha hb
    exact LineU.ActsDiagU.unique hM.surj ha hb
  have act_ratio : ∀ {a : MulAut L'} {t u : Fin (N + 1) → Kˣ}, Act a t → Act a u →
      ∃ c : Kˣ, ∀ i, u i = c * t i := by
    intro a t u ha hb
    refine ⟨u 0 / t 0, fun i => ?_⟩
    have h := LineU.ActsDiagU.ratio_eq hM.field hd3 hM.ker ha hb 0 i
    have h' : t 0 * (t i)⁻¹ = u 0 * (u i)⁻¹ := Units.ext (by simpa using h)
    have h2 : u i = t i * (t 0)⁻¹ * u 0 := by
      calc u i = (u 0 * (u i)⁻¹)⁻¹ * u 0 := by group
        _ = (t 0 * (t i)⁻¹)⁻¹ * u 0 := by rw [h']
        _ = t i * (t 0)⁻¹ * u 0 := by group
    rw [h2, div_eq_mul_inv]
    ac_rfl
  have act_const : ∀ {a : MulAut L'} (c : Kˣ), Act a (fun _ => c) → a = 1 := by
    intro a c ha
    exact LineU.ActsDiagU.eq_one_of_const hM.surj ha ⟨0, by omega⟩ (fun i j => rfl)
  have act_ratio_mem : ∀ {a : MulAut L'} {t : Fin (N + 1) → Kˣ}, Act a t →
      ∀ i j, t i / t j ∈ μ := by
    intro a t ha i j
    show (t i / t j) ^ (2 ^ n + 1) = 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h := l48u1_ratio_norm_one hM.field hd3 ha i j
    simpa [div_eq_mul_inv] using h
  have tg_norm : ∀ s : ggTDTg μ N, ∀ i, ((s : Fin (N + 1) → Kˣ) i : K) ^ (2 ^ n + 1) = 1 := by
    intro s i
    have h : ((s : Fin (N + 1) → Kˣ) i) ^ (2 ^ n + 1) = 1 := s.2.1 i
    simpa [Units.val_pow_eq_pow_val] using congrArg (fun x : Kˣ => (x : K)) h
  have tg_prod : ∀ s : ggTDTg μ N, ∏ i, ((s : Fin (N + 1) → Kˣ) i : K) = 1 := by
    intro s
    have h : ∏ i, (s : Fin (N + 1) → Kˣ) i = 1 := s.2.2
    simpa using congrArg (fun x : Kˣ => (x : K)) h
  let dgmFun : ggTDTg μ N → ↥(unitarySU 2 n K (N + 1)) := fun s =>
    Classical.choose (LineU.exists_diagSU hM.field
      (u := fun i => ((s : Fin (N + 1) → Kˣ) i : K)) (tg_norm s) (tg_prod s))
  have dgmFun_spec : ∀ s, ((dgmFun s : GL (Fin (N + 1)) K) :
      Matrix (Fin (N + 1)) (Fin (N + 1)) K) =
      diagonal (fun i => ((s : Fin (N + 1) → Kˣ) i : K)) := fun s =>
    Classical.choose_spec (LineU.exists_diagSU hM.field
      (u := fun i => ((s : Fin (N + 1) → Kˣ) i : K)) (tg_norm s) (tg_prod s))
  let dgm : ggTDTg μ N →* ↥(unitarySU 2 n K (N + 1)) :=
    MonoidHom.mk' dgmFun (by
      intro s t
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, dgmFun_spec, diagonal_mul_diagonal,
        Pi.mul_apply])
  have dgm_spec : ∀ s, ((dgm s : GL (Fin (N + 1)) K) :
      Matrix (Fin (N + 1)) (Fin (N + 1)) K) =
      diagonal (fun i => ((s : Fin (N + 1) → Kˣ) i : K)) := fun s => dgmFun_spec s
  have act_dgm : ∀ s : ggTDTg μ N, Act (MulAut.conj (φ (dgm s))) (s : Fin (N + 1) → Kˣ) := by
    intro s
    exact LineU.actsDiagU_conj (φ := φ) (dgm_spec s)
  have act_fix : ∀ {a : MulAut L'} {t : Fin (N + 1) → Kˣ}, Act a t → ∀ s : ggTDTg μ N,
      a (φ (dgm s)) = φ (dgm s) := by
    intro a t ha s
    exact LineU.ActsDiagU.fix_of_diagonal ha (dgm s) (dgm_spec s)
  have ker_dgm : ∀ s : ggTDTg μ N, φ (dgm s) = 1 → ∃ c : Kˣ,
      ∀ i, (s : Fin (N + 1) → Kˣ) i = c := by
    intro s hs
    obtain ⟨c, hc⟩ := hM.ker (dgm s) hs
    have hcd : (fun i => ((s : Fin (N + 1) → Kˣ) i : K)) = fun _ => c :=
      Matrix.diagonal_injective ((dgm_spec s).symm.trans hc)
    have hc0 : c ≠ 0 := by
      rw [← congrFun hcd 0]
      exact Units.ne_zero ((s : Fin (N + 1) → Kˣ) 0)
    refine ⟨Units.mk0 c hc0, fun i => ?_⟩
    apply Units.ext
    exact congrFun hcd i
  have inner_diag : ∀ (g : ↥(unitarySU 2 n K (N + 1))) {t : Fin (N + 1) → Kˣ},
      Act (MulAut.conj (φ g)) t → ∃ s : ggTDTg μ N, φ g = φ (dgm s) := by
    intro g t hg
    obtain ⟨c, hc⟩ := exists_diagonal_of_actsDiagU_conj hM.field hp hpq hd4 hM.ker hg
    have hnorm : ∀ k, (c * ((t k : Kˣ) : K)) ^ (2 ^ n + 1) = 1 :=
      fun k => UnitTB.diag_norm_one_of_mem_unitarySU hM.field hc k
    have hne : ∀ k, c * ((t k : Kˣ) : K) ≠ 0 := by
      intro k h0
      have h1 := hnorm k
      rw [h0, zero_pow (Nat.succ_ne_zero (2 ^ n))] at h1
      exact zero_ne_one h1
    have hprod : ∏ k, c * ((t k : Kˣ) : K) = 1 := l48u1_diag_prod hM.field hc
    let s : ggTDTg μ N := ⟨fun k => Units.mk0 (c * ((t k : Kˣ) : K)) (hne k),
      ⟨fun k => by
        show (Units.mk0 (c * ((t k : Kˣ) : K)) (hne k)) ^ (2 ^ n + 1) = 1
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
        exact hnorm k, by
        apply Units.ext
        simpa using hprod⟩⟩
    refine ⟨s, ?_⟩
    have hgd : g = dgm s := by
      apply Subtype.ext
      apply Units.ext
      rw [hc, dgm_spec s]
      rfl
    rw [hgd]
  have central_diag : ∀ g : ↥(unitarySU 2 n K (N + 1)), MulAut.conj (φ g) = 1 →
      ∃ s : ggTDTg μ N, φ g = φ (dgm s) := by
    intro g hg
    have hconj : ∀ y, φ (g * y * g⁻¹) = φ y := by
      intro y
      have h := congrArg (fun f : MulAut L' => f (φ y)) hg
      simpa [MulAut.conj_apply] using h
    obtain ⟨c, hc⟩ := LineU.exists_scalar_of_map_conj_eq_U hM.field hd4 hM.ker hconj
    have hnorm : c ^ (2 ^ n + 1) = 1 := UnitTB.diag_norm_one_of_mem_unitarySU hM.field hc 0
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_pow (Nat.succ_ne_zero (2 ^ n))] at hnorm
      exact zero_ne_one hnorm
    have hprod : ∏ _ : Fin (N + 1), c = 1 := l48u1_diag_prod hM.field hc
    let s : ggTDTg μ N := ⟨fun _ => Units.mk0 c hc0,
      ⟨fun _ => by
        show (Units.mk0 c hc0) ^ (2 ^ n + 1) = 1
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
        exact hnorm, by
        apply Units.ext
        simpa using hprod⟩⟩
    refine ⟨s, ?_⟩
    have hgd : g = dgm s := by
      apply Subtype.ext
      apply Units.ext
      rw [hc, dgm_spec s]
      rfl
    rw [hgd]
  have cent_diag : ∀ {ζ : Kˣ}, ζ ∈ μ → ζ ≠ ζ⁻¹ → ∀ g : ↥(unitarySU 2 n K (N + 1)),
      (∀ k l : Fin (N + 1), k ≠ l → ∀ s : ggTDTg μ N,
        (s : Fin (N + 1) → Kˣ) = Pi.mulSingle k ζ * Pi.mulSingle l ζ⁻¹ →
        MulAut.conj (φ g) * MulAut.conj (φ (dgm s)) =
          MulAut.conj (φ (dgm s)) * MulAut.conj (φ g)) →
      ∃ s : ggTDTg μ N, φ g = φ (dgm s) := by
    intro ζ hζ hζ2 g hg
    have hζpow : (ζ : K) ^ (2 ^ n + 1) = 1 := by
      have h := congrArg (fun x : Kˣ => (x : K)) hζ
      simpa [Units.val_pow_eq_pow_val] using h
    have hζ2' : (ζ : K) ≠ (ζ : K)⁻¹ :=
      fun h => hζ2 (Units.ext (by simpa using h))
    have hdiag : ((g : GL (Fin (N + 1)) K) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) K).IsDiag := by
      refine LineU.isDiag_of_conj_comm_U hM.field hd4 hM.ker hζpow hζ2' (s := g) ?_
      intro k l hkl D hD
      let s : ggTDTg μ N := ⟨Pi.mulSingle k ζ * Pi.mulSingle l ζ⁻¹,
        ⟨fun m => by
          rw [Pi.mul_apply, Pi.mulSingle_apply, Pi.mulSingle_apply]
          split_ifs
          · exact μ.mul_mem hζ (μ.inv_mem hζ)
          · simpa using hζ
          · simpa using μ.inv_mem hζ
          · simpa using μ.one_mem, by
          simp [Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle']⟩⟩
      have hdgm : dgm s = D := by
        apply Subtype.ext
        apply Units.ext
        rw [dgm_spec s, hD]
        congr 1
        funext i
        by_cases hil : i = l <;> by_cases hik : i = k <;>
          simp [s, TypeA.ggPairVec, Pi.mul_apply, Pi.mulSingle_apply, hil, hik, hkl]
      rw [← hdgm]
      exact hg k l hkl s rfl
    have hgw : ((g : GL (Fin (N + 1)) K) : Matrix (Fin (N + 1)) (Fin (N + 1)) K) =
        diagonal (fun i => ((g : GL (Fin (N + 1)) K) :
          Matrix (Fin (N + 1)) (Fin (N + 1)) K) i i) :=
      ((Matrix.isDiag_iff_diagonal_diag _).mp hdiag).symm
    have hwnorm : ∀ i, ((g : GL (Fin (N + 1)) K) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) K) i i ^ (2 ^ n + 1) = 1 :=
      fun i => UnitTB.diag_norm_one_of_mem_unitarySU hM.field hgw i
    have hw0 : ∀ i, ((g : GL (Fin (N + 1)) K) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) K) i i ≠ 0 := by
      intro i h0
      have h1 := hwnorm i
      rw [h0, zero_pow (Nat.succ_ne_zero (2 ^ n))] at h1
      exact zero_ne_one h1
    have hwprod : ∏ i, ((g : GL (Fin (N + 1)) K) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) K) i i = 1 := l48u1_diag_prod hM.field hgw
    let s : ggTDTg μ N := ⟨fun i => Units.mk0 (((g : GL (Fin (N + 1)) K) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) K) i i) (hw0 i),
      ⟨fun i => by
        show (Units.mk0 (((g : GL (Fin (N + 1)) K) :
          Matrix (Fin (N + 1)) (Fin (N + 1)) K) i i) (hw0 i)) ^ (2 ^ n + 1) = 1
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
        exact hwnorm i, by
        apply Units.ext
        simpa using hwprod⟩⟩
    refine ⟨s, ?_⟩
    have hgs : g = dgm s := by
      apply Subtype.ext
      apply Units.ext
      rw [hgw, dgm_spec s]
      rfl
    rw [hgs]
  have heart_mem : ∀ {p : ℕ} {A : Subgroup (MulAut L')}, GGTorusSelfCent p A →
      (∀ a ∈ A, ∃ t, Act a t) → ∀ s : ggTDTg μ N,
      (∀ i, (s : Fin (N + 1) → Kˣ) i ^ p = 1) → MulAut.conj (φ (dgm s)) ∈ A := by
    intro p A hsc hdiag s hs
    refine LineU.conj_mem_of_selfCent_U (p := p) hsc ?_ (D := dgm s) (dgm_spec s) ?_
    · intro a ha
      obtain ⟨t, ht⟩ := hdiag a ha
      exact ⟨fun i => (t i : K), ht⟩
    · intro i
      have h := hs i
      simpa [Units.val_pow_eq_pow_val] using congrArg (fun x : Kˣ => (x : K)) h
  have act_perm : ∀ {a : MulAut L'} {t : Fin (N + 1) → Kˣ}
      (σ : Equiv.Perm (Fin (N + 1))), Act a t →
      Act (MulAut.conj (φ (LineU.permSU hM.field σ⁻¹)) * a *
        (MulAut.conj (φ (LineU.permSU hM.field σ⁻¹)))⁻¹) (fun i => t (σ i)) := by
    intro a t σ ha
    simpa [Act] using LineU.ActsDiagU.conj_perm hM.field ha σ⁻¹
  have act_apply_perm : ∀ {a : MulAut L'} {t : Fin (N + 1) → Kˣ}
      (σ : Equiv.Perm (Fin (N + 1))) (s : ggTDTg μ N), Act a t →
      (∀ i, (s : Fin (N + 1) → Kˣ) i = t i / t (σ i)) →
      a (φ (LineU.permSU hM.field σ⁻¹)) = φ (dgm s * LineU.permSU hM.field σ⁻¹) := by
    intro a t σ s ha hs
    obtain ⟨D, hD, hDt, hact⟩ := ha
    rw [hact (LineU.permSU hM.field σ⁻¹)]
    congr 1
    apply Subtype.ext
    apply Units.ext
    have hL : (((LineU.conjN D hD (LineU.permSU hM.field σ⁻¹) :
        ↥(unitarySU 2 n K (N + 1))) : GL (Fin (N + 1)) K) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) K) =
        diagonal (fun i => (t i : K)) * σ.permMatrix K * diagonal (fun i => ((t i : K))⁻¹) := by
      rw [LineU.coe_conjN]
      simp only [Units.val_mul]
      rw [hDt, LineU.coe_permSU, LineU.coe_permGL_matrix, LineU.coe_inv_diag hDt]
      simp [inv_inv]
    have hR : (((dgm s * LineU.permSU hM.field σ⁻¹ :
        ↥(unitarySU 2 n K (N + 1))) : GL (Fin (N + 1)) K) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) K) =
        diagonal (fun i => ((s : Fin (N + 1) → Kˣ) i : K)) * σ.permMatrix K := by
      rw [Subgroup.coe_mul]
      simp only [Units.val_mul]
      rw [dgm_spec s, LineU.coe_permSU, LineU.coe_permGL_matrix]
      simp [inv_inv]
    rw [hL, hR]
    refine l48u1_perm_diag σ ?_
    intro i
    have h := congrArg (fun x : Kˣ => (x : K)) (hs i)
    simpa [div_eq_mul_inv] using h
  refine ⟨{ μ := μ
            ι := ι
            H := ↥(unitarySU 2 n K (N + 1))
            grp := inferInstance
            φ := φ
            surj := hM.surj
            Act := Act
            act_one := act_one
            act_mul := act_mul
            act_inv := act_inv
            act_unique := act_unique
            act_ratio := act_ratio
            act_const := act_const
            act_ratio_mem := act_ratio_mem
            dgm := dgm
            act_dgm := act_dgm
            act_fix := act_fix
            ker_dgm := ker_dgm
            Pm := fun σ => LineU.permSU hM.field σ⁻¹
            act_perm := act_perm
            act_apply_perm := act_apply_perm
            inner_diag := fun g {_} hg => by
              obtain ⟨s, hs⟩ := inner_diag g hg
              exact ⟨s, 1, Subgroup.one_mem _, by rw [hs, mul_one]⟩
            central_diag := fun z hz _ => by
              obtain ⟨g, rfl⟩ := hM.surj z
              have hg : MulAut.conj (φ g) = 1 := by
                ext x
                change φ g * x * (φ g)⁻¹ = x
                rw [(Subgroup.mem_center_iff.mp hz x).symm, mul_inv_cancel_right]
              exact central_diag g hg
            cent_diag := fun {_} hζ hζ2 g hg => by
              obtain ⟨s, hs⟩ := cent_diag hζ hζ2 g hg
              exact ⟨s, 1, Subgroup.one_mem _, by rw [hs, mul_one]⟩
            heart_mem := heart_mem }, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨fun i => (t i : K), ht⟩
    · rintro ⟨t, ht⟩
      refine ⟨fun i => Units.mk0 (t i) (ht.ne_zero i), ?_⟩
      simpa [Act] using ht
  · intro σ
    rfl

theorem exists_torusWit_of_model_U {K : Type} [Field K] [Finite K] {n p N : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    (hN : 3 ≤ N) {L' : Type} [Group L'] [Finite L']
    {φ : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 n K (N + 1)) →* L'} (hM : UnitTB.Model φ)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin (N + 1) → K, LineU.ActsDiagU φ a t) :
    ∃ w : GGTorusTorWit (2 ^ n + 1) N L' A,
      w.Holds (CartanMatrix.A N) (CoxeterMatrix.A N) ∧
        ∀ k : Fin N, w.n k = φ (LineU.permSU hM.field (Equiv.swap k.castSucc k.succ)) := by
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    subst h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by simpa using hpq))
  obtain ⟨M, hMact, hMP⟩ := exists_ggTDModel_U hK hn hp hpq hN hM
  obtain ⟨ρ, hρinj, hρrange, hρsw⟩ :=
    exists_permAut_unitary hM hK hp hp2 hpq (by omega : 4 ≤ N + 1) hA hsc hdiag
  have hN' : ∀ σ, MulAut.conj (M.φ (M.Pm σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    intro σ
    rw [hMP]
    exact unitDvd_conj_perm_mem_normalizer hM hp hpq (by omega) hA.2 hsc hdiag σ⁻¹
  refine ⟨ggTDwit M A hN', ?_, fun k => ?_⟩
  · refine ggTDwit_holds_of_model M hp hp2 hpq (Nat.succ_pos _) (by omega) hsc
      (fun a ha => (hMact a).mpr (hdiag a ha)) hN' ρ hρinj hρrange (fun k => ?_)
    have hσ : MulAut.conj (φ (LineU.permSU hM.field (Equiv.swap k.castSucc k.succ))) ∈
      Subgroup.normalizer (A : Set (MulAut L')) :=
      unitDvd_conj_perm_mem_normalizer hM hp hpq (by omega) hA.2 hsc hdiag _
    rw [hρsw _ hσ]
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply, ggConjAut_apply, hMP, Equiv.swap_inv]
  · change M.φ (M.Pm (Equiv.swap k.castSucc k.succ)) = _
    rw [hMP, Equiv.swap_inv]

theorem ggTorusTorData_of_model_U {K : Type} [Field K] [Finite K] {n p N : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    (hN : 3 ≤ N) {L' : Type} [Group L'] [Finite L']
    {φ : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 n K (N + 1)) →* L'} (hM : UnitTB.Model φ)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin (N + 1) → K, LineU.ActsDiagU φ a t) :
    GGTorusTorData (2 ^ n + 1) N (CartanMatrix.A N) (CoxeterMatrix.A N) L' A := by
  obtain ⟨w, hw, -⟩ := exists_torusWit_of_model_U hK hp hp2 hpq hN hM hA hsc hdiag
  exact ⟨w, hw⟩

theorem ggTorusTorW_unitary (hU : LineU.UnitaryUniversalCover) {K : Type} [Field K] [Finite K]
    {n p N : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hN : 4 ≤ N) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ N + 1) (h63 : ¬ (N + 1 = 6 ∧ p = 3)) :
    GGTorusTorW p (N - 2) (2 ^ n + 1) N (CartanMatrix.A N) (CoxeterMatrix.A N)
      (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n)))
        (LargeEvenGUSet (Fin (N + 1)) K (2 ^ n))) := by
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hTB
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hd5 : 5 ≤ N + 1 := by omega
  have hr' : p ^ (N + 1 - 3) ≤ Nat.card A := by
    have : N + 1 - 3 = N - 2 := by omega
    rwa [this]
  have hcard : p ^ ((N + 1) / p + 2) ≤ Nat.card A := LineU.card_ge_of_dvd hp hp2 hd5 hpd h63 hr' h3
  have hdnd : (N + 1, n) ≠ (6, 1) := by
    rintro h
    obtain ⟨h1, rfl⟩ := Prod.mk.inj h
    have h3' : p ∣ 3 := by simpa using hpq
    exact h63 ⟨h1, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel hK hn hd5 hp hpq hpd (hU n (N + 1) K hK hd5 hdnd) hψ hker hperf hAe hAI
      hcard
  have hM : UnitTB.Model φ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
  exact ggTorusTorData_of_model_U hK hp hp2 hpq (by omega) hM hAe hsc hdiag

theorem exists_eq_conj_diag_of_actsDiagU {K : Type} [Field K] {n d : ℕ}
    (hK : UnitaryFieldData 2 n K) (hd : 3 ≤ d) (hcop : Nat.Coprime d (2 ^ n + 1)) {L' : Type}
    [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'} (hφs : Function.Surjective φ) {a : MulAut L'}
    {t : Fin d → K} (ha : LineU.ActsDiagU φ a t) :
    ∃ (D : ↥(unitarySU 2 n K d)) (u : Fin d → K),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u ∧ a = MulAut.conj (φ D) := by
  classical
  set i₀ : Fin d := ⟨0, by omega⟩
  have hnorm : ∀ k, (t k / t i₀) ^ (2 ^ n + 1) = 1 := fun k => l48u1_ratio_norm_one hK hd ha k i₀
  have ht0 : ∀ k, t k ≠ 0 := ha.ne_zero
  set P : K := ∏ k, t k / t i₀ with hP
  have hPn : P ^ (2 ^ n + 1) = 1 := by
    rw [hP, ← Finset.prod_pow]
    exact Finset.prod_eq_one fun k _ => hnorm k
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => div_ne_zero (ht0 k) (ht0 i₀)
  obtain ⟨e, -, he⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
    (by have := Nat.one_le_two_pow (n := n); omega)
  set lam : K := P ^ e with hlam
  have hlamn : lam ^ (2 ^ n + 1) = 1 := by
    rw [hlam, ← pow_mul, mul_comm, pow_mul, hPn, one_pow]
  have hlamd : lam ^ d = P := by
    rw [hlam, ← pow_mul, mul_comm e d, ← Nat.div_add_mod (d * e) (2 ^ n + 1), he, pow_add,
      pow_mul, hPn, one_pow, one_mul, pow_one]
  have hlam0 : lam ≠ 0 := pow_ne_zero _ hP0
  set c : K := (t i₀ * lam)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (mul_ne_zero (ht0 i₀) hlam0)
  have hu : ∀ k, t k * c = t k / t i₀ * lam⁻¹ := fun k => by
    rw [hc, mul_inv, div_eq_mul_inv, mul_assoc]
  have hun : ∀ k, (t k * c) ^ (2 ^ n + 1) = 1 := fun k => by
    rw [hu, mul_pow, hnorm, inv_pow, hlamn, inv_one, one_mul]
  have hprod : ∏ k, t k * c = 1 := by
    rw [Finset.prod_congr rfl fun k _ => hu k, Finset.prod_mul_distrib, ← hP, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, inv_pow, hlamd, mul_inv_cancel₀ hP0]
  obtain ⟨D, hD⟩ := LineU.exists_diagSU hK (u := fun k => t k * c) hun hprod
  exact ⟨D, fun k => t k * c, hD, LineU.ActsDiagU.unique hφs (UnitTB.actsDiagU_mul_const ha hc0)
    (LineU.actsDiagU_conj hD)⟩

theorem ggTorusTorW_unitary_six_three
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    GGTorusTorW 3 4 (2 ^ n + 1) 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5)
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hTB
  have hcov := LineU.unitaryUniversalCover_holds n 6 K hK (by norm_num)
    (by rintro h; have hh := congrArg Prod.snd h; simp only at hh; omega)
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel hK (by omega) (by norm_num) Nat.prime_three hpq (by norm_num)
      hcov hψ hker hperf hAe hAI (by simpa using hr)
  have hM : UnitTB.Model φ := ⟨TableBU.unitaryFieldData_of_card hK (by omega), hφs, hφker⟩
  exact ggTorusTorData_of_model_U hK Nat.prime_three (by norm_num) hpq (by norm_num) hM hAe hsc
    hdiag

end CFSG.StandardType
