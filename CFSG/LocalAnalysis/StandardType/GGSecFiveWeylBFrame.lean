module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBLevi
public import CFSG.LocalAnalysis.StandardType.GGPresentationReduce
import all CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CoxeterSystem
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin

section Coxeter

variable {n : ℕ}

theorem cartanC_succ_succ (i j : Fin n) : cartanC (n + 1) i.succ j.succ = cartanC n i j := by
  simp only [cartanC, Matrix.of_apply, Fin.succ_inj, Fin.val_succ]
  split_ifs <;> omega

theorem coxeterMatrix_C_succ_succ (i j : Fin n) :
    coxeterMatrix (isFiniteType_cartanC (n + 1)) i.succ j.succ =
      coxeterMatrix (isFiniteType_cartanC n) i j := by
  rw [coxeterMatrix_cartanC_apply, coxeterMatrix_cartanC_apply, cartanC_succ_succ,
    cartanC_succ_succ]

theorem coxeterMatrix_C_zero_zero :
    coxeterMatrix (isFiniteType_cartanC (n + 1)) 0 0 = 1 :=
  (coxeterMatrix (isFiniteType_cartanC (n + 1))).diagonal 0

theorem coxeterMatrix_C_zero_one (hn : 2 ≤ n) (k : Fin n) (hk : k.val = 0) :
    coxeterMatrix (isFiniteType_cartanC (n + 1)) 0 k.succ = 3 :=
  coxeterMatrix_of_succ_short (n + 1) (by simp [hk]) (by simp [hk]; omega)

theorem coxeterMatrix_C_zero_far (k : Fin n) (hk : 1 ≤ k.val) :
    coxeterMatrix (isFiniteType_cartanC (n + 1)) 0 k.succ = 2 :=
  coxeterMatrix_of_far (n + 1) (Fin.succ_ne_zero k).symm (by simp; omega) (by simp)

end Coxeter

section Frame

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]

@[expose] def GGSpEndNode (φ₁ : StatedSp n F →* X) (T : X) : Prop :=
  T * T = 1 ∧ (∀ k : Fin n, k.val = 0 → (T * φ₁ (weylRep n F k)) ^ 3 = 1) ∧
    ∀ r : RootSubgroupIndex n, (∀ k : Fin n, k.val = 0 → stdVec r k = 0) → ∀ c : F,
      T * φ₁ (elt r c) = φ₁ (elt r c) * T

@[expose] noncomputable def spSpecial (φ₁ : StatedSp n F →* X) (T : X) : Fin (n + 1) → X :=
  Fin.cons T fun k => φ₁ (weylRep n F k)

theorem spSpecial_zero (φ₁ : StatedSp n F →* X) (T : X) : spSpecial φ₁ T 0 = T := rfl

theorem spSpecial_succ (φ₁ : StatedSp n F →* X) (T : X) (k : Fin n) :
    spSpecial φ₁ T k.succ = φ₁ (weylRep n F k) := rfl

theorem GGSpEndNode.commute_weylRep {φ₁ : StatedSp n F →* X} {T : X} (h : GGSpEndNode φ₁ T)
    (k : Fin n) (hk : 1 ≤ k.val) : T * φ₁ (weylRep n F k) = φ₁ (weylRep n F k) * T := by
  have hc : ∀ r : RootSubgroupIndex n, (∀ x : Fin n, x.val = 0 → stdVec r x = 0) → ∀ c : F,
      Commute T (φ₁ (elt r c)) := fun r hr c => h.2.2 r hr c
  have hx : ∀ x : Fin n, x.val = 0 → x ≠ k := fun x hx e => by subst e; omega
  by_cases hlt : k.val + 1 < n
  · have hx' : ∀ x : Fin n, x.val = 0 → x ≠ ⟨k.val + 1, hlt⟩ := fun x hx e => by
      have := congrArg Fin.val e
      simp only at this
      omega
    have h1 := hc (.difference k ⟨k.val + 1, hlt⟩ (ne_succ' hlt)) (fun x hx0 => by
      simp [stdVec, hx x hx0, hx' x hx0]) 1
    have h2 := hc (.difference ⟨k.val + 1, hlt⟩ k (ne_succ' hlt).symm) (fun x hx0 => by
      simp [stdVec, hx x hx0, hx' x hx0]) (-1)
    rw [weylRep_eq_elt_of_lt hlt, map_mul, map_mul]
    exact ((h1.mul_right h2).mul_right h1).eq
  · have h1 := hc (.positiveLong k) (fun x hx0 => by simp [stdVec, hx x hx0]) 1
    have h2 := hc (.negativeLong k) (fun x hx0 => by simp [stdVec, hx x hx0]) (-1)
    rw [weylRep_eq_elt_of_not_lt hlt, map_mul, map_mul]
    exact ((h1.mul_right h2).mul_right h1).eq

theorem spSpecial_succ_sq (h2 : (2 : F) = 0) (φ₁ : StatedSp n F →* X) (k : Fin n) :
    φ₁ (weylRep n F k) * φ₁ (weylRep n F k) = 1 := by
  rw [← map_mul, spWeylRep_mul_self n h2, map_one]

theorem spSpecial_isLiftable (h2 : (2 : F) = 0) (hn : 2 ≤ n) {φ₁ : StatedSp n F →* X} {T : X}
    (h : GGSpEndNode φ₁ T) :
    (coxeterMatrix (isFiniteType_cartanC (n + 1))).IsLiftable (spSpecial φ₁ T) := by
  have hW : (coxeterMatrix (isFiniteType_cartanC n)).IsLiftable (weylRep n F) :=
    isLiftable_of_braid _ (spWeylRep_mul_self n h2) (isCTGroupDatum n F).braid
  have hcube : ∀ a b : X, (b * a) ^ 3 = 1 → (a * b) ^ 3 = 1 := by
    intro a b hab
    have e : (a * b) ^ 3 = b⁻¹ * (b * a) ^ 3 * b := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e, hab]
    group
  have hsq2 : ∀ a b : X, a * a = 1 → b * b = 1 → a * b = b * a → (a * b) ^ 2 = 1 := by
    intro a b ha hb hab
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · rw [coxeterMatrix_C_zero_zero, pow_one, spSpecial_zero]
    exact h.1
  · rw [spSpecial_zero, spSpecial_succ]
    by_cases hj : j.val = 0
    · rw [coxeterMatrix_C_zero_one hn j hj]
      exact h.2.1 j hj
    · rw [coxeterMatrix_C_zero_far j (by omega)]
      exact hsq2 _ _ h.1 (spSpecial_succ_sq h2 φ₁ j) (h.commute_weylRep j (by omega))
  · rw [spSpecial_zero, spSpecial_succ, (coxeterMatrix (isFiniteType_cartanC (n + 1))).symmetric]
    by_cases hi : i.val = 0
    · rw [coxeterMatrix_C_zero_one hn i hi]
      exact hcube _ _ (h.2.1 i hi)
    · rw [coxeterMatrix_C_zero_far i (by omega)]
      exact hsq2 _ _ (spSpecial_succ_sq h2 φ₁ i) h.1 (h.commute_weylRep i (by omega)).symm
  · rw [spSpecial_succ, spSpecial_succ, coxeterMatrix_C_succ_succ, ← map_mul, ← map_pow, hW i j,
      map_one]

@[expose] noncomputable def spFrameLift (h2 : (2 : F) = 0) (hn : 2 ≤ n)
    {φ₁ : StatedSp n F →* X} {T : X} (h : GGSpEndNode φ₁ T) :
    (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group →* X :=
  (coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.lift
    ⟨spSpecial φ₁ T, spSpecial_isLiftable h2 hn h⟩

theorem spFrameLift_simple (h2 : (2 : F) = 0) (hn : 2 ≤ n) {φ₁ : StatedSp n F →* X} {T : X}
    (h : GGSpEndNode φ₁ T) (j : Fin (n + 1)) :
    spFrameLift h2 hn h ((coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple j) =
      spSpecial φ₁ T j :=
  (coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.lift_apply_simple _ j

end Frame

section Levi

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]

theorem spWeylLift_mem_levi (h2 : (2 : F) = 0)
    {v : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group} (hv : v ∈ spLeviWeyl n) :
    spWeylLift (n + 1) h2 v ∈ ggSub (Symplectic.rootDatum (n + 1) F)
      (ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n)) := by
  have hν := spWeylLift_spec (n + 1) h2
  refine ggWeylLift_mem_of_closure (D := Symplectic.rootDatum (n + 1) F) ?_ hv
  rintro _ ⟨j, hj, rfl⟩
  exact sup_le (rootGroup_le_ggSub (single_mem_ggSupp hj))
    (rootGroup_le_ggSub (neg_single_mem_ggSupp hj)) (hν.simple_mem j)

variable (h2 : (2 : F) = 0) (hn : 2 ≤ n) {φ₁ : StatedSp n F →* X} {T : X}
  (h : GGSpEndNode φ₁ T)
include h2 hn h

theorem spFrame_special {j : Fin (n + 1)} (hj : j ∈ spLeviJ n) :
    ggExt (spLeviHom φ₁) (weylRep (n + 1) F j) = spFrameLift h2 hn h
      ((coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple j) := by
  have hj0 : j ≠ 0 := fun e => by
    have := mem_spLeviJ.mp hj
    rw [e] at this
    simp at this
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hj0
  rw [spFrameLift_simple, spSpecial_succ, ← spLeviBlock_weylRep, ggExt_spLeviHom]

theorem spFrame_eq_ggExt {v : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group}
    (hv : v ∈ spLeviWeyl n) :
    ggExt (spLeviHom φ₁) (spWeylLift (n + 1) h2 v) = spFrameLift h2 hn h v := by
  have hv' : v ∈ Subgroup.closure
      ((coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple ''
        (spLeviJ n : Set (Fin (n + 1)))) := hv
  induction hv' using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨j, hj, rfl⟩ := ht
    rw [spWeylLift_simple]
    exact spFrame_special h2 hn h hj
  | one => rw [map_one, map_one, ggExt_one]
  | mul x y hx hy ihx ihy =>
    rw [map_mul, map_mul, ggExt_mul _ (spWeylLift_mem_levi h2 hx) (spWeylLift_mem_levi h2 hy),
      ihx hx, ihy hy]
  | inv x hx ihx =>
    rw [map_inv, map_inv, ggExt_inv _ (spWeylLift_mem_levi h2 hx), ihx hx]

end Levi

section Coord

variable {n : ℕ}

theorem toStd_succ_apply_zero (hn : 1 ≤ n) (γ : Fin (n + 1) → ℤ) :
    toStd (n + 1) γ 0 = γ 0 := by
  have h1 : ¬ (0 < (0 : Fin (n + 1)).val) := by simp
  have h2 : ¬ ((0 : Fin (n + 1)).val + 1 = n + 1) := by simp; omega
  rw [toStd_apply_eq, dite_eq_right h1, sub_zero, ite_eq_right h2, one_mul]

theorem exists_ne_zero_ne_ne (hn : 3 ≤ n) (a b : Fin (n + 1)) :
    ∃ c : Fin (n + 1), c ≠ 0 ∧ c ≠ a ∧ c ≠ b := by
  have hcard : ({0, a, b} : Finset (Fin (n + 1))).card <
      (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact Finset.card_le_three.trans_lt (by omega)
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc.1, hc.2.1, hc.2.2⟩

theorem exists_toStd_eq_zero (hn : 3 ≤ n) {α : Fin (n + 1) → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC (n + 1)) ∅) :
    ∃ c : Fin (n + 1), 1 ≤ c.val ∧ toStd (n + 1) α c = 0 := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hα
  have key : ∀ a b : Fin (n + 1), (∀ c, c ≠ a → c ≠ b → stdVec r c = 0) →
      ∃ c : Fin (n + 1), 1 ≤ c.val ∧ toStd (n + 1) α c = 0 := by
    intro a b hab
    obtain ⟨c, hc0, hca, hcb⟩ := exists_ne_zero_ne_ne hn a b
    refine ⟨c, ?_, by rw [← hr]; exact hab c hca hcb⟩
    have := Fin.val_ne_of_ne hc0
    simp only [Fin.val_zero] at this
    omega
  cases r with
  | positiveLong i => exact key i i (fun c hc _ => by simp [stdVec, hc])
  | negativeLong i => exact key i i (fun c hc _ => by simp [stdVec, hc])
  | difference i j _ => exact key i j (fun c hci hcj => by simp [stdVec, hci, hcj])
  | positiveSum i j _ => exact key i j (fun c hci hcj => by simp [stdVec, hci, hcj])
  | negativeSum i j _ => exact key i j (fun c hci hcj => by simp [stdVec, hci, hcj])

end Coord

section Cent

variable {X : Type*} [Group X]

theorem sp_conj_mul_eq_of_conj {a b x : X} (ha : a * x * a⁻¹ = x) (hb : b * x * b⁻¹ = x) :
    (a * b) * x * (a * b)⁻¹ = x := by
  calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    _ = x := by rw [hb, ha]

theorem sp_conj_inv_eq_of_conj {a x : X} (ha : a * x * a⁻¹ = x) : a⁻¹ * x * a⁻¹⁻¹ = x := by
  calc a⁻¹ * x * a⁻¹⁻¹ = a⁻¹ * (a * x * a⁻¹) * a := by rw [ha]; group
    _ = x := by group

variable {n : ℕ} {F : Type} [Field F]

theorem GGSpEndNode.commute_ggExt {φ₁ : StatedSp n F →* X} {T : X} (h : GGSpEndNode φ₁ T)
    (hn : 1 ≤ n) {γ : Fin (n + 1) → ℤ}
    (hγ : γ ∈ ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n))
    (h1 : toStd (n + 1) γ ⟨1, by omega⟩ = 0) {z : StatedSp (n + 1) F}
    (hz : z ∈ rootGroup (n + 1) F γ) :
    T * ggExt (spLeviHom φ₁) z = ggExt (spLeviHom φ₁) z * T := by
  obtain ⟨hr, h0⟩ := mem_ggSupp_spLeviJ_iff.mp hγ
  obtain ⟨γ₀, hγ₀, rfl⟩ := exists_cons_of_root hr h0
  rw [rootGroup_cons hγ₀] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ₀
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).mp hy
  rw [ggExt_spLeviHom]
  refine h.2.2 r (fun k hk => ?_) c
  have e : k.succ = (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext (by simp [hk])
  rw [toStd_cons, ← e, Fin.cons_succ] at h1
  rw [hr]
  exact h1

variable (h2 : (2 : F) = 0) (hn : 2 ≤ n) {φ₁ : StatedSp n F →* X} {T : X}
  (h : GGSpEndNode φ₁ T)
include h2 hn h

theorem spFrame_cent_levi {v : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group}
    (hv : v ∈ spLeviWeyl n) {α : Fin (n + 1) → ℤ}
    (hα : α ∈ ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n))
    (hfix : weylAction (isFiniteType_cartanC (n + 1)) v α = α) {z : StatedSp (n + 1) F}
    (hz : z ∈ rootGroup (n + 1) F α) :
    spFrameLift h2 hn h v * ggExt (spLeviHom φ₁) z * (spFrameLift h2 hn h v)⁻¹ =
      ggExt (spLeviHom φ₁) z := by
  have hu := spWeylLift_mem_levi h2 hv
  have hzL := rootGroup_le_ggSub (D := Symplectic.rootDatum (n + 1) F) hα hz
  have key : spWeylLift (n + 1) h2 v * z * (spWeylLift (n + 1) h2 v)⁻¹ = z :=
    (spWeylLift_standardCopy (m := n + 1) h2).2 v α hα.1 hfix z hz
  rw [← spFrame_eq_ggExt h2 hn h hv, ← ggExt_inv _ hu, ← ggExt_mul _ hu hzL,
    ← ggExt_mul _ (mul_mem hu hzL) (inv_mem hu), key]

theorem spFrame_cent_zeroSwap {u : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group}
    {c : Fin (n + 1)} (hc : 1 ≤ c.val) (hu : SpRealizes (n + 1) u (Equiv.swap 0 c) 1)
    {α : Fin (n + 1) → ℤ} (hα : α ∈ ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n))
    (hαc : toStd (n + 1) α c = 0) {z : StatedSp (n + 1) F} (hz : z ∈ rootGroup (n + 1) F α) :
    spFrameLift h2 hn h u * ggExt (spLeviHom φ₁) z * (spFrameLift h2 hn h u)⁻¹ =
      ggExt (spLeviHom φ₁) z := by
  obtain ⟨v, hv, hvr, hu'⟩ := exists_spZeroSwap (by omega) c hc
  obtain rfl := hu.inj hu'
  have hρs : spFrameLift h2 hn h
      ((coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple 0) = T := by
    rw [spFrameLift_simple, spSpecial_zero]
  have hρv : spFrameLift h2 hn h v = ggExt (spLeviHom φ₁) (spWeylLift (n + 1) h2 v) :=
    (spFrame_eq_ggExt h2 hn h hv).symm
  have hνv := spWeylLift_mem_levi h2 hv
  have hzL := rootGroup_le_ggSub (D := Symplectic.rootDatum (n + 1) F) hα hz
  have hz' : (spWeylLift (n + 1) h2 v)⁻¹ * z * spWeylLift (n + 1) h2 v ∈
      rootGroup (n + 1) F (weylAction (isFiniteType_cartanC (n + 1)) v⁻¹ α) := by
    have e : (spWeylLift (n + 1) h2 v)⁻¹ * z * spWeylLift (n + 1) h2 v =
        spWeylLift (n + 1) h2 v⁻¹ * z * (spWeylLift (n + 1) h2 v⁻¹)⁻¹ := by
      rw [map_inv, inv_inv]
    rw [e]
    exact (spWeylLift_spec (n + 1) h2).conj_mem v⁻¹ α hα.1 z hz
  have hstd := hvr.inv_one α
  have h1c : (Equiv.swap (⟨1, by omega⟩ : Fin (n + 1)) c)⁻¹.symm ⟨1, by omega⟩ = c := by
    rw [Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.swap_apply_left]
  have h0 : (Equiv.swap (⟨1, by omega⟩ : Fin (n + 1)) c)⁻¹.symm 0 = 0 := by
    rw [Equiv.Perm.inv_def, Equiv.symm_symm]
    refine Equiv.swap_apply_of_ne_of_ne (fun e => ?_) (fun e => ?_)
    · have := congrArg Fin.val e
      simp at this
    · have := congrArg Fin.val e
      simp at this
      omega
  have hmem : weylAction (isFiniteType_cartanC (n + 1)) v⁻¹ α ∈
      ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n) := by
    refine mem_ggSupp_spLeviJ_iff.mpr
      ⟨(ggIsCTRootSystem (Symplectic.rootDatum (n + 1) F)).smul_mem v⁻¹ α hα.1, ?_⟩
    rw [← toStd_succ_apply_zero (n := n) (by omega)
      (weylAction (isFiniteType_cartanC (n + 1)) v⁻¹ α), hstd]
    simp only [Pi.one_apply, one_mul]
    rw [h0, toStd_succ_apply_zero (by omega)]
    exact (mem_ggSupp_spLeviJ_iff.mp hα).2
  have h1 : toStd (n + 1) (weylAction (isFiniteType_cartanC (n + 1)) v⁻¹ α) ⟨1, by omega⟩ = 0 := by
    rw [hstd]
    simp only [Pi.one_apply, one_mul]
    rw [h1c, hαc]
  have hT := h.commute_ggExt (by omega) hmem h1 hz'
  rw [ggExt_mul _ (mul_mem (inv_mem hνv) hzL) hνv, ggExt_mul _ (inv_mem hνv) hzL,
    ggExt_inv _ hνv, ← hρv] at hT
  rw [map_mul, map_mul, map_inv, hρs]
  calc spFrameLift h2 hn h v * T * (spFrameLift h2 hn h v)⁻¹ * ggExt (spLeviHom φ₁) z *
        (spFrameLift h2 hn h v * T * (spFrameLift h2 hn h v)⁻¹)⁻¹
      = spFrameLift h2 hn h v * (T * ((spFrameLift h2 hn h v)⁻¹ * ggExt (spLeviHom φ₁) z *
          spFrameLift h2 hn h v)) * T⁻¹ * (spFrameLift h2 hn h v)⁻¹ := by group
    _ = spFrameLift h2 hn h v * (((spFrameLift h2 hn h v)⁻¹ * ggExt (spLeviHom φ₁) z *
          spFrameLift h2 hn h v) * T) * T⁻¹ * (spFrameLift h2 hn h v)⁻¹ := by rw [hT]
    _ = ggExt (spLeviHom φ₁) z := by group

theorem spFrame_cent_zeroSign (hn3 : 3 ≤ n)
    {z₀ : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group}
    (hz₀ : SpRealizes (n + 1) z₀ 1 (spSgn 0)) {α : Fin (n + 1) → ℤ}
    (hα : α ∈ ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n)) {z : StatedSp (n + 1) F}
    (hz : z ∈ rootGroup (n + 1) F α) :
    spFrameLift h2 hn h z₀ * ggExt (spLeviHom φ₁) z * (spFrameLift h2 hn h z₀)⁻¹ =
      ggExt (spLeviHom φ₁) z := by
  obtain ⟨c, hc, hαc⟩ := exists_toStd_eq_zero hn3 hα.1
  obtain ⟨v, -, -, hu⟩ := exists_spZeroSwap (by omega) c hc
  obtain ⟨y, hy, hyr⟩ := exists_spLeviW_sgn (by omega) c hc
  have hprod := (hu.mul hyr).mul hu.inv_one
  have e := hz₀.inj (hprod.congr (by rw [mul_one, mul_inv_cancel]) (by
    funext x
    simp [spSgn, Equiv.swap_inv, Equiv.swap_apply_eq_iff]))
  have hyfix : weylAction (isFiniteType_cartanC (n + 1)) y α = α := hyr.fix fun b => by
    change spSgn c b * toStd (n + 1) α b = toStd (n + 1) α b
    unfold spSgn
    split_ifs with hb
    · subst hb
      rw [hαc]
      ring
    · ring
  have hcy := spFrame_cent_levi h2 hn h hy hα hyfix hz
  have hcu := spFrame_cent_zeroSwap h2 hn h hc hu hα hαc hz
  rw [e, map_mul, map_mul, map_inv]
  exact sp_conj_mul_eq_of_conj (sp_conj_mul_eq_of_conj hcu hcy) (sp_conj_inv_eq_of_conj hcu)

theorem spFrame_hcent (hn3 : 3 ≤ n) :
    ∀ (w : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group) (α : Fin (n + 1) → ℤ),
      α ∈ ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n) →
        weylAction (isFiniteType_cartanC (n + 1)) w α = α → ∀ z ∈ rootGroup (n + 1) F α,
          spFrameLift h2 hn h w * ggExt (spLeviHom φ₁) z * (spFrameLift h2 hn h w)⁻¹ =
            ggExt (spLeviHom φ₁) z := by
  intro w α hα hfix z hz
  obtain ⟨π, s, hs, hw⟩ := exists_spRealizes w
  obtain ⟨u, z₀, hu, hz₀, hv⟩ := spLevi_decomp (by omega) hs hw
  have hα0 : toStd (n + 1) α 0 = 0 := by
    rw [toStd_succ_apply_zero (by omega)]
    exact (mem_ggSupp_spLeviJ_iff.mp hα).2
  have hαπ : toStd (n + 1) α (π 0) = 0 := by
    have := congrFun (hw α) (π 0)
    rw [hfix, Equiv.symm_apply_apply, hα0, mul_zero] at this
    exact this
  have hcu : spFrameLift h2 hn h u * ggExt (spLeviHom φ₁) z * (spFrameLift h2 hn h u)⁻¹ =
      ggExt (spLeviHom φ₁) z ∧ weylAction (isFiniteType_cartanC (n + 1)) u α = α := by
    rcases hu with rfl | hu
    · simp [Module.End.one_apply]
    · by_cases h0 : π 0 = 0
      · have : u = 1 := hu.inj (spRealizes_one.congr
          (by rw [h0, Equiv.swap_self, Equiv.Perm.one_def]) rfl)
        subst this
        simp [Module.End.one_apply]
      · have hc : 1 ≤ (π 0).val := by
          have := Fin.val_ne_of_ne h0
          simp only [Fin.val_zero] at this
          omega
        refine ⟨spFrame_cent_zeroSwap h2 hn h hc hu hα hαπ hz, hu.fix fun b => ?_⟩
        simp only [Pi.one_apply, one_mul, Equiv.symm_swap]
        rcases eq_or_ne b 0 with rfl | hb0
        · rw [Equiv.swap_apply_left, hαπ, hα0]
        rcases eq_or_ne b (π 0) with rfl | hbc
        · rw [Equiv.swap_apply_right, hα0, hαπ]
        · rw [Equiv.swap_apply_of_ne_of_ne hb0 hbc]
  have hcz : spFrameLift h2 hn h z₀ * ggExt (spLeviHom φ₁) z * (spFrameLift h2 hn h z₀)⁻¹ =
      ggExt (spLeviHom φ₁) z ∧ weylAction (isFiniteType_cartanC (n + 1)) z₀ α = α := by
    rcases hz₀ with rfl | hz₀
    · simp [Module.End.one_apply]
    · refine ⟨spFrame_cent_zeroSign h2 hn h hn3 hz₀ hα hz, hz₀.fix fun b => ?_⟩
      change spSgn 0 b * toStd (n + 1) α b = toStd (n + 1) α b
      unfold spSgn
      split_ifs with hb
      · subst hb
        rw [hα0]
        ring
      · ring
  have hvfix : weylAction (isFiniteType_cartanC (n + 1)) (z₀ * u * w) α = α := by
    rw [weylAction_mul_apply, weylAction_mul_apply, hfix, hcu.2, hcz.2]
  have hcv := spFrame_cent_levi h2 hn h hv hα hvfix hz
  have e : w = u⁻¹ * z₀⁻¹ * (z₀ * u * w) := by group
  rw [e, map_mul, map_mul, map_inv, map_inv]
  exact sp_conj_mul_eq_of_conj (sp_conj_mul_eq_of_conj (sp_conj_inv_eq_of_conj hcu.1)
    (sp_conj_inv_eq_of_conj hcz.1)) hcv

end Cent

section Injective

theorem elt_one_injective {m : ℕ} {F : Type} [Field F] {r r' : RootSubgroupIndex m}
    (h : elt (F := F) r 1 = elt r' 1) : r = r' := by
  have e := congrFun (congrFun (congrArg (mat m F) h) (pos1 r).1) (pos1 r).2
  rw [mat_elt_apply_pos1, mat_elt, Matrix.add_apply, Matrix.one_apply_ne (pos1_ne r),
    Matrix.smul_apply, one_smul, zero_add] at e
  have hne : E F r' (pos1 r).1 (pos1 r).2 ≠ 0 := by rw [← e]; exact one_ne_zero
  apply stdVec_injective
  rcases eq_pos_of_E_ne_zero r' _ _ hne with hp | hp
  · rw [← wt_pos1 r, ← wt_pos1 r', ← hp]
  · rw [← wt_pos1 r, ← wt_pos2 r', ← hp]

theorem spWeylLift_eq_one {m : ℕ} {F : Type} [Field F] (h2 : (2 : F) = 0)
    {x : (coxeterMatrix (isFiniteType_cartanC m)).Group} (hx : spWeylLift m h2 x = 1) : x = 1 := by
  apply weylAction_injective (isFiniteType_cartanC m)
  rw [map_one]
  refine (Pi.basisFun ℤ (Fin m)).ext fun j => ?_
  rw [Pi.basisFun_apply, Module.End.one_apply]
  have hj : (Pi.single j 1 : Fin m → ℤ) ∈ roots (isFiniteType_cartanC m) ∅ :=
    (ggIsCTRootSystem (Symplectic.rootDatum m F)).single_mem j
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hj
  obtain ⟨r', hr', he⟩ := spWeylLift_conj_elt h2 x hr (1 : F)
  rw [hx, one_mul, inv_one, mul_one] at he
  obtain rfl := elt_one_injective he
  exact SpExtras.toStd_inj (hr'.symm.trans hr)

variable {n : ℕ}

theorem exists_spRealizes_perm (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + 1))) :
    ∃ g : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group, SpRealizes (n + 1) g σ 1 := by
  by_cases h0 : σ 0 = 0
  · obtain ⟨v, -, hv⟩ := exists_spLeviW_perm (n := n) σ.support.card σ le_rfl h0
    exact ⟨v, hv⟩
  · have hc : 1 ≤ (σ 0).val := by
      have := Fin.val_ne_of_ne h0
      simp only [Fin.val_zero] at this
      omega
    obtain ⟨v, -, -, hu⟩ := exists_spZeroSwap hn (σ 0) hc
    have h0' : (Equiv.swap 0 (σ 0) * σ) 0 = 0 := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    obtain ⟨y, -, hy⟩ := exists_spLeviW_perm (n := n) _ _ le_rfl h0'
    refine ⟨_, (hu.mul_one hy).congr ?_ rfl⟩
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

theorem exists_perm_one_two (hn : 2 ≤ n) {a b : Fin (n + 1)} (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), σ a = ⟨1, by omega⟩ ∧ σ b = ⟨2, by omega⟩ := by
  set o : Fin (n + 1) := ⟨1, by omega⟩
  set t : Fin (n + 1) := ⟨2, by omega⟩
  have hot : o ≠ t := fun e => by
    have := congrArg Fin.val e
    simp [o, t] at this
  set b' := Equiv.swap a o b
  have hob' : o ≠ b' := fun e => hab ((Equiv.swap a o).injective (by
    rw [Equiv.swap_apply_left]
    exact e))
  refine ⟨Equiv.swap b' t * Equiv.swap a o, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hob' hot]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

variable {F : Type} [Field F] {X : Type*} [Group X]

theorem ggExt_spLeviHom_injective {φ₁ : StatedSp n F →* X} (hφ : Function.Injective φ₁)
    {u u' : StatedSp (n + 1) F}
    (hu : u ∈ ggSub (Symplectic.rootDatum (n + 1) F)
      (ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n)))
    (hu' : u' ∈ ggSub (Symplectic.rootDatum (n + 1) F)
      (ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n)))
    (h : ggExt (spLeviHom φ₁) u = ggExt (spLeviHom φ₁) u') : u = u' := by
  obtain ⟨g, rfl⟩ := exists_spBlock_eq hu
  obtain ⟨g', rfl⟩ := exists_spBlock_eq hu'
  rw [ggExt_spLeviHom, ggExt_spLeviHom] at h
  rw [hφ h]

variable (h2 : (2 : F) = 0) (hn : 2 ≤ n) {φ₁ : StatedSp n F →* X} {T : X}
  (h : GGSpEndNode φ₁ T)
include h2 hn h

theorem spFrame_eq_one_of_levi (hφ : Function.Injective φ₁)
    {v : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group} (hv : v ∈ spLeviWeyl n)
    (h1 : spFrameLift h2 hn h v = 1) : v = 1 := by
  rw [← spFrame_eq_ggExt h2 hn h hv] at h1
  have hu := spWeylLift_mem_levi h2 hv
  have key := ggExt_spLeviHom_injective hφ hu (one_mem _) (h1.trans (ggExt_one _).symm)
  exact spWeylLift_eq_one h2 key

theorem spFrame_ne_pairFlip (hφ : Function.Injective φ₁)
    {x : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group} (hx : spFrameLift h2 hn h x = 1)
    {a b : Fin (n + 1)} (hab : a ≠ b) (hr : SpRealizes (n + 1) x 1 (spSgnOn {a, b})) : False := by
  obtain ⟨σ, hσa, hσb⟩ := exists_perm_one_two hn hab
  obtain ⟨g, hg⟩ := exists_spRealizes_perm (by omega) σ
  set o : Fin (n + 1) := ⟨1, by omega⟩
  set t : Fin (n + 1) := ⟨2, by omega⟩
  have hconj := ((hg.mul hr).mul hg.inv_one).congr (by rw [mul_one, mul_inv_cancel])
    (s' := spSgnOn {o, t}) (by
      funext c
      simp only [Pi.one_apply, one_mul, mul_one, spSgnOn, Finset.mem_insert,
        Finset.mem_singleton, Equiv.Perm.inv_def]
      congr 1
      apply propext
      constructor
      · rintro (e | e)
        · left
          rw [← hσa, ← e, Equiv.apply_symm_apply]
        · right
          rw [← hσb, ← e, Equiv.apply_symm_apply]
      · rintro (e | e)
        · left
          rw [e, ← hσa, Equiv.symm_apply_apply]
        · right
          rw [e, ← hσb, Equiv.symm_apply_apply])
  have hot : o ≠ t := fun e => by
    have := congrArg Fin.val e
    simp [o, t] at this
  have hsg : SpIsSign (spSgnOn ({o, t} : Finset (Fin (n + 1)))) := spIsSign_spSgnOn _
  obtain ⟨v, hv, hvr⟩ := exists_spLeviW_of_fix (by omega) hsg (π := 1) rfl (by
    simp only [spSgnOn, Finset.mem_insert, Finset.mem_singleton]
    refine ite_eq_right ?_
    rintro (e | e)
    · have := congrArg Fin.val e
      simp [o] at this
    · have := congrArg Fin.val e
      simp [t] at this)
  have he := hconj.inj hvr
  have hρ : spFrameLift h2 hn h (g * x * g⁻¹) = 1 := by
    rw [map_mul, map_mul, hx, mul_one, map_inv, mul_inv_cancel]
  rw [he] at hρ
  have hv1 := spFrame_eq_one_of_levi h2 hn h hφ hv hρ
  rw [hv1] at hvr
  have key := congrFun (hvr (Pi.single o 1)) o
  rw [map_one, Module.End.one_apply] at key
  change toStd (n + 1) (Pi.single o 1) o = spSgnOn {o, t} o * toStd (n + 1) (Pi.single o 1) o
    at key
  have hval : toStd (n + 1) (Pi.single o 1) o ≠ 0 := by
    rw [toStd_apply_eq]
    have h0 : 0 < o.val := by simp [o]
    rw [dite_eq_left h0]
    simp only [Pi.single_eq_same]
    have e0 : (⟨o.val - 1, by omega⟩ : Fin (n + 1)) ≠ o := fun e => by
      have := congrArg Fin.val e
      simp [o] at this
    rw [Pi.single_eq_of_ne e0]
    split_ifs <;> norm_num
  have hs : spSgnOn ({o, t} : Finset (Fin (n + 1))) o = -1 := by simp [spSgnOn]
  rw [hs] at key
  exact hval (by linarith)

theorem spFrameLift_injective (hφ : Function.Injective φ₁) (hn3 : 3 ≤ n) :
    Function.Injective (spFrameLift h2 hn h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨π, s, hs, hxr⟩ := exists_spRealizes x
  have hπ : π = 1 := by
    by_contra hπ1
    obtain ⟨d, hd⟩ : ∃ d, π d ≠ d := by
      by_contra hne
      push Not at hne
      exact hπ1 (Equiv.ext hne)
    obtain ⟨g, hg⟩ : ∃ g : (coxeterMatrix (isFiniteType_cartanC (n + 1))).Group,
        SpRealizes (n + 1) g 1 (spSgn d) := by
      by_cases hd0 : d = 0
      · subst hd0
        exact exists_spZeroSign (by omega)
      · obtain ⟨g, -, hg⟩ := exists_spLeviW_sgn (by omega) d (by
          have := Fin.val_ne_of_ne hd0
          simp only [Fin.val_zero] at this
          omega)
        exact ⟨g, hg⟩
    have hcomm := ((hxr.mul hg).mul (hxr.inv hs)).mul (hg.inv (spIsSign_spSgn d))
    have hc : SpRealizes (n + 1) (x * g * x⁻¹ * g⁻¹) 1 (spSgnOn {d, π d}) := by
      refine hcomm.congr (by rw [mul_one, mul_inv_cancel, inv_one, mul_one]) ?_
      funext c
      change spSgn d c * (s (π.symm c) * (spSgn d (π.symm c) * s (π.symm c))) =
        spSgnOn {d, π d} c
      rw [mul_left_comm (s (π.symm c)), hs.mul_self, mul_one]
      unfold spSgn spSgnOn
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hcd : c = d
      · subst hcd
        have hne : π.symm c ≠ c := fun e => hd (by
          have := congrArg π e
          rw [Equiv.apply_symm_apply] at this
          exact this.symm)
        simp [hne]
      · by_cases hcπ : c = π d
        · subst hcπ
          simp [hcd]
        · have hne : π.symm c ≠ d := fun e => hcπ (by rw [← e, Equiv.apply_symm_apply])
          simp [hcd, hcπ, hne]
    have hρ : spFrameLift h2 hn h (x * g * x⁻¹ * g⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, hx, map_inv, map_inv, hx]
      group
    exact spFrame_ne_pairFlip h2 hn h hφ hρ (Ne.symm hd) hc
  subst hπ
  have hsc : (∀ c, s c = 1) ∨ (∀ c, s c = -1) := by
    by_contra hne
    push Not at hne
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hne
    have ha' : s a = -1 := (hs a).resolve_left ha
    have hb' : s b = 1 := (hs b).resolve_right hb
    have hab : a ≠ b := fun e => by
      rw [e, hb'] at ha'
      norm_num at ha'
    obtain ⟨g, hg⟩ := exists_spRealizes_perm (by omega) (Equiv.swap a b)
    have hy := hxr.mul ((hg.mul hxr).mul hg.inv_one)
    have hc : SpRealizes (n + 1) (x * (g * x * g⁻¹)) 1 (spSgnOn {a, b}) := by
      refine hy.congr (by rw [mul_one, mul_inv_cancel, one_mul]) ?_
      funext c
      simp only [Pi.one_apply, one_mul, mul_one, Equiv.Perm.inv_def, Equiv.symm_swap,
        Equiv.swap_mul_self, Equiv.Perm.one_apply]
      unfold spSgnOn
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hca : c = a
      · subst hca
        simp [ha', hb']
      · by_cases hcb : c = b
        · subst hcb
          simp [ha', hb', hca]
        · rw [Equiv.swap_apply_of_ne_of_ne hca hcb, hs.mul_self]
          simp [hca, hcb]
    have hρ : spFrameLift h2 hn h (x * (g * x * g⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, hx, map_inv]
      group
    exact spFrame_ne_pairFlip h2 hn h hφ hρ hab hc
  rcases hsc with h1 | hm1
  · exact hxr.inj (spRealizes_one.congr rfl (by funext c; exact (h1 c).symm))
  · exfalso
    obtain ⟨z₀, hz₀⟩ := exists_spZeroSign (n := n) (by omega)
    have hsg : SpIsSign (fun c : Fin (n + 1) => s c * spSgn 0 c) := hs.mul (spIsSign_spSgn 0) 1
    have hvr' : SpRealizes (n + 1) (z₀⁻¹ * x) 1 (fun c => s c * spSgn 0 c) :=
      ((hz₀.inv (spIsSign_spSgn 0)).mul hxr).congr (by rw [inv_one, one_mul]) (by funext c; rfl)
    obtain ⟨v, hv, hvr⟩ := exists_spLeviW_of_fix (by omega) hsg (π := 1) rfl
      (by simp [hm1, spSgn])
    have hve : z₀⁻¹ * x = v := hvr'.inj hvr
    have hρv : spFrameLift h2 hn h v = (spFrameLift h2 hn h z₀)⁻¹ := by
      rw [← hve, map_mul, hx, mul_one, map_inv]
    have hlast : ¬ (Fin.last n).val + 1 < n + 1 := by simp
    have hl0 : (0 : Fin (n + 1)) ≠ Fin.last n := fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
    have hr : stdVec (RootSubgroupIndex.positiveLong (Fin.last n)) =
        toStd (n + 1) (Pi.single (Fin.last n) 1) := by
      rw [toStd_single_of_not_lt' hlast]
      rfl
    have hα : (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℤ) ∈
        ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n) :=
      mem_ggSupp_spLeviJ_iff.mpr ⟨mem_roots_of_stdVec hr, Pi.single_eq_of_ne hl0 _⟩
    have hzz : elt (F := F) (.positiveLong (Fin.last n)) 1 ∈
        rootGroup (n + 1) F (Pi.single (Fin.last n) 1) := elt_mem_rootGroup hr 1
    have hcz := spFrame_cent_zeroSign h2 hn h hn3 hz₀ hα hzz
    have hcv : spFrameLift h2 hn h v * ggExt (spLeviHom φ₁) (elt (.positiveLong (Fin.last n)) 1) *
        (spFrameLift h2 hn h v)⁻¹ = ggExt (spLeviHom φ₁) (elt (.positiveLong (Fin.last n)) 1) := by
      rw [hρv]
      exact sp_conj_inv_eq_of_conj hcz
    obtain ⟨r', hr', he⟩ := spWeylLift_conj_elt h2 v hr (1 : F)
    have hr'n : r' = .negativeLong (Fin.last n) := by
      apply stdVec_injective
      rw [hr', hvr]
      funext b
      change (s b * spSgn 0 b) * toStd (n + 1) (Pi.single (Fin.last n) 1) b =
        stdVec (RootSubgroupIndex.negativeLong (Fin.last n)) b
      rw [toStd_single_of_not_lt' hlast, hm1 b]
      by_cases hb : b = Fin.last n
      · subst hb
        simp [spSgn, stdVec, Ne.symm hl0]
      · simp [stdVec, hb]
    have hνv := spWeylLift_mem_levi h2 hv
    have hzzL := rootGroup_le_ggSub (D := Symplectic.rootDatum (n + 1) F) hα hzz
    rw [← spFrame_eq_ggExt h2 hn h hv, ← ggExt_inv _ hνv, ← ggExt_mul _ hνv hzzL,
      ← ggExt_mul _ (mul_mem hνv hzzL) (inv_mem hνv), he, hr'n] at hcv
    have hneg : elt (F := F) (.negativeLong (Fin.last n)) 1 ∈
        ggSub (Symplectic.rootDatum (n + 1) F)
          (ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n)) := by
      rw [← hr'n, ← he]
      exact mul_mem (mul_mem hνv hzzL) (inv_mem hνv)
    have := elt_one_injective (ggExt_spLeviHom_injective hφ hneg hzzL hcv)
    cases this

end Injective

end CFSG.StandardType
