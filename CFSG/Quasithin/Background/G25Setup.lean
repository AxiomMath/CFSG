module

public import CFSG.Quasithin.Background.G2SL3Four
public import CFSG.Quasithin.Background.G25Comm
public import CFSG.Quasithin.Background.G2SL3Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G]

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (St : L3Setting n V V₁ L T H)

include St

theorem mem_normalizer_U_of_stab (i : ↥(L ⊔ conjClosure V H))
    (hi : St.Phi i ∈ Pt (vE (GaloisField 2 n) 0)) :
    (i : G) ∈ Subgroup.normalizer ((conjClosure V H : Subgroup G) : Set G) := by
  have hnorm : conjClosure V H ≤ Subgroup.normalizer (L : Set G) := fun u hu => St.U_le_normL hu
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (conjClosure V H) L hnorm
  have hi' : (i : G) ∈ (↑(conjClosure V H ⊔ L) : Set G) := by
    rw [sup_comm]
    exact i.2
  rw [hmul] at hi'
  obtain ⟨u, hu, l, hl, hil⟩ := Set.mem_mul.1 hi'
  have hu' : u ∈ L ⊔ conjClosure V H := (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu
  have hl' : l ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) hl
  have hiul : i = ⟨u, hu'⟩ * ⟨l, hl'⟩ := Subtype.ext hil.symm
  obtain ⟨b, c, hb⟩ := St.Phi_of_U hu
  have hlθ : St.Phi ⟨l, hl'⟩ = St.D.θ ⟨l, hl⟩ := St.Phi_of_L ⟨l, hl⟩
  have hPhiU : St.Phi ⟨u, hu'⟩ ∈ Pt (vE (GaloisField 2 n) 0) := by
    rw [hb]
    exact Qv_le_Pt _ (tq_mem_Qv b c)
  have hθ : St.D.θ ⟨l, hl⟩ ∈ Pt (vE (GaloisField 2 n) 0) := by
    have h1 : St.D.θ ⟨l, hl⟩ = (St.Phi ⟨u, hu'⟩)⁻¹ * St.Phi i := by
      rw [← hlθ, hiul, map_mul]
      group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hPhiU) hi
  have hlN := St.mem_normalizer_V₁_of_stab ⟨l, hl⟩ hθ
  have hlH : l ∈ H := St.hyp.base.toBase.N_le_H ⟨hl, hlN⟩
  rw [← hil]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer hu) (le_normalizer_conjClosure V H hlH)

@[expose] noncomputable def pvec {a : G} (ha : a ∈ L) : Fin 3 → GaloisField 2 n :=
  St.D.θ ⟨a, ha⟩⁻¹ • vE (GaloisField 2 n) 0

theorem conj_rconj_mem {a b : G} (ha : a ∈ L) (hb : b ∈ L) (x : ↥(L ⊔ conjClosure V H))
    (hx : ∃ c : GaloisField 2 n, St.Phi x • St.pvec ha = c • St.pvec hb) {y : G}
    (hy : y ∈ rconj (conjClosure V H) a) : (x : G) * y * (x : G)⁻¹ ∈ rconj (conjClosure V H) b := by
  obtain ⟨c, hc⟩ := hx
  have haLU : a ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) ha
  have hbLU : b ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) hb
  set m : ↥(L ⊔ conjClosure V H) := ⟨b, hbLU⟩ * x * ⟨a, haLU⟩⁻¹ with hm
  have hmP : St.Phi m ∈ Pt (vE (GaloisField 2 n) 0) := by
    refine ⟨c, ?_⟩
    have h1 : St.Phi ⟨b, hbLU⟩ = St.D.θ ⟨b, hb⟩ := St.Phi_of_L ⟨b, hb⟩
    have h2 : St.Phi ⟨a, haLU⟩ = St.D.θ ⟨a, ha⟩ := St.Phi_of_L ⟨a, ha⟩
    have h3 : (St.D.θ ⟨a, ha⟩)⁻¹ • vE (GaloisField 2 n) 0 = St.pvec ha := by
      rw [pvec, map_inv]
    have h4 : St.D.θ ⟨b, hb⟩ • St.pvec hb = vE (GaloisField 2 n) 0 := by
      rw [pvec, map_inv, smul_inv_smul]
    rw [hm, map_mul, map_mul, map_inv, h1, h2, mul_smul, mul_smul, h3, hc, smul_comm, h4]
  have hmN := St.mem_normalizer_U_of_stab m hmP
  have hy' : a * y * a⁻¹ ∈ conjClosure V H := mem_rconj.1 hy
  have h1 := (Subgroup.mem_normalizer_iff.1 hmN _).1 hy'
  rw [mem_rconj]
  have e : b * ((x : G) * y * (x : G)⁻¹) * b⁻¹ =
      (m : G) * (a * y * a⁻¹) * (m : G)⁻¹ := by
    rw [hm]
    simp
    group
  rw [e]
  exact h1

theorem Phi_mem_Qv_of_mem_rconj {a : G} (ha : a ∈ L) (x : ↥(L ⊔ conjClosure V H))
    (hx : (x : G) ∈ rconj (conjClosure V H) a) : St.Phi x ∈ Qv (St.pvec ha) := by
  have haLU : a ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) ha
  have hu : a * (x : G) * a⁻¹ ∈ conjClosure V H := mem_rconj.1 hx
  have h1 : St.Phi ⟨a * (x : G) * a⁻¹, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu⟩ ∈
      Qv (vE (GaloisField 2 n) 0) := St.betaU_mem_Qv ⟨_, hu⟩
  have e : (⟨a * (x : G) * a⁻¹, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu⟩ :
      ↥(L ⊔ conjClosure V H)) = ⟨a, haLU⟩ * x * ⟨a, haLU⟩⁻¹ := Subtype.ext (by simp)
  rw [e, map_mul, map_mul, map_inv, St.Phi_of_L ⟨a, ha⟩] at h1
  have h2 := (mem_Qv_conj (St.D.θ ⟨a, ha⟩)⁻¹
    (St.D.θ ⟨a, ha⟩ * St.Phi x * (St.D.θ ⟨a, ha⟩)⁻¹)).2 h1
  have e2 : (St.D.θ ⟨a, ha⟩)⁻¹ * (St.D.θ ⟨a, ha⟩ * St.Phi x * (St.D.θ ⟨a, ha⟩)⁻¹) *
      ((St.D.θ ⟨a, ha⟩)⁻¹)⁻¹ = St.Phi x := by group
  rw [e2] at h2
  have h3 : (St.D.θ ⟨a, ha⟩)⁻¹ • vE (GaloisField 2 n) 0 = St.pvec ha := by
    rw [pvec, map_inv]
  rwa [h3] at h2

theorem exists_lift {a : G} (ha : a ∈ L) {r : SL(3, GaloisField 2 n)}
    (hr : r ∈ Qv (St.pvec ha)) :
    ∃ x : ↥(L ⊔ conjClosure V H), (x : G) ∈ rconj (conjClosure V H) a ∧ St.Phi x = r := by
  obtain ⟨x, hx, rfl⟩ := St.Qv_le_Phi_rconj ha hr
  exact ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩

theorem sxFacts : L ⊔ conjClosure V H ≤ L ⊔ T ∧
    pCoreOf 2 (L ⊔ conjClosure V H) ≤ pCoreOf 2 (L ⊔ T) ∧
    pCoreOf 2 (L ⊔ conjClosure V H) ≤ T ∧
    (∀ x ∈ L ⊔ conjClosure V H, ∀ y ∈ pCoreOf 2 (L ⊔ conjClosure V H),
      x * y * x⁻¹ ∈ pCoreOf 2 (L ⊔ conjClosure V H)) ∧
    (∀ y ∈ pCoreOf 2 (L ⊔ conjClosure V H), ∀ x ∈ conjClosure V H, y * x * y⁻¹ ∈ conjClosure V H) :=
  sx_facts_gen rfl St.U_le_T St.hyp.base.G22_three.2 St.hyp.base.T_le_normL St.hyp.base.sylow_LT

theorem Phi_eq_one_iff_mem_S (x : ↥(L ⊔ conjClosure V H)) :
    St.Phi x = 1 ↔ (x : G) ∈ pCoreOf 2 (L ⊔ conjClosure V H) := by
  obtain ⟨hIle, hSxO, -, -, -⟩ := St.sxFacts
  rw [St.Phi_eq_one_iff]
  constructor
  · intro hxO
    exact mem_pCoreOf_of_mem_pCoreOf_of_le hIle x.2 hxO
  · intro hx
    exact hSxO hx

end L3Setting

@[expose] def tripleConj (g h : G) : Fin 3 → G := ![1, g, h]

@[expose] def tripleU (U : Subgroup G) (g h : G) : Fin 3 → Subgroup G :=
  fun k => rconj U (tripleConj g h k)

theorem rconj_one' (X : Subgroup G) : rconj X 1 = X := by
  ext y
  rw [mem_rconj]
  simp

theorem tripleU_zero (U : Subgroup G) (g h : G) : tripleU U g h 0 = U := by
  simp [tripleU, tripleConj, rconj_one']

theorem tripleU_one (U : Subgroup G) (g h : G) : tripleU U g h 1 = rconj U g := by
  simp [tripleU, tripleConj]

theorem tripleU_two (U : Subgroup G) (g h : G) : tripleU U g h 2 = rconj U h := by
  simp [tripleU, tripleConj]

theorem tripleConj_mem {L : Subgroup G} {g h : G} (hg : g ∈ L) (hh : h ∈ L) (k : Fin 3) :
    tripleConj g h k ∈ L := by
  fin_cases k
  · exact L.one_mem
  · exact hg
  · exact hh

theorem rconj_inf_eq_of_normalizes {X Y : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) : rconj (X ⊓ Y) a = rconj X a ⊓ Y := by
  ext y
  simp only [mem_rconj, Subgroup.mem_inf]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨hx, (Subgroup.mem_normalizer_iff.1 ha y).2 hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx, (Subgroup.mem_normalizer_iff.1 ha y).1 hy⟩

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (St : L3Setting n V V₁ L T H)
  {g h : G} (hg : g ∈ L) (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)

include St hg hh hV

theorem tripleGrp : TripleGrp (L ⊔ conjClosure V H) (pCoreOf 2 (L ⊔ conjClosure V H))
    (tripleU (conjClosure V H) g h) := by
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := St.sxFacts
  have hI : conjClosure V H ⊔ rconj (conjClosure V H) g ⊔ rconj (conjClosure V H) h =
      L ⊔ conjClosure V H := St.G25_two_aux hg hh hV
  have hLI : L ≤ L ⊔ conjClosure V H := le_sup_left
  have hUI : conjClosure V H ≤ L ⊔ conjClosure V H := le_sup_right
  have hcm : ∀ k, tripleConj g h k ∈ L := tripleConj_mem hg hh
  have hVU : ∀ k, V ≤ tripleU (conjClosure V H) g h k := fun k => St.V_le_rconj_U (hcm k)
  have hVS₂ : V ≤ TripleGrp.S₂ (tripleU (conjClosure V H) g h) :=
    le_inf (le_inf (hVU 0) (hVU 1)) (hVU 2)
  have hV1 : ∀ k, rconj V₁ (tripleConj g h k) ≤ V := fun k => St.rconj_V₁_le_V (hcm k)
  have hS₂N : L ⊔ conjClosure V H ≤ Subgroup.normalizer
      ((TripleGrp.S₂ (tripleU (conjClosure V H) g h) : Subgroup G) : Set G) := by
    have hc := St.commutator_inter3_le_V hg hh hI.symm hV
    refine le_normalizer_of_conj_mem fun x hx y hy => ?_
    have hy' : y ∈ conjClosure V H ⊓ rconj (conjClosure V H) g ⊓ rconj (conjClosure V H) h := by
      simpa [TripleGrp.S₂, tripleU_zero, tripleU_one, tripleU_two] using hy
    have h1 : y * x * y⁻¹ * x⁻¹ ∈ V := hc (Subgroup.commutator_mem_commutator hy' hx)
    have h2 : x * y * x⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ * y := by group
    rw [h2]
    exact Subgroup.mul_mem _ ((TripleGrp.S₂ (tripleU (conjClosure V H) g h)).inv_mem (hVS₂ h1)) hy
  refine ⟨?_, hINorm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tripleU_zero, tripleU_one, tripleU_two]
    exact hI.symm
  · intro k y hy x hx
    have ha : tripleConj g h k ∈ L ⊔ conjClosure V H := hLI (hcm k)
    have h1 : tripleConj g h k * x * (tripleConj g h k)⁻¹ ∈ conjClosure V H := mem_rconj.1 hx
    have h2 := hINorm _ ha y hy
    have h3 := hSxU _ h2 _ h1
    rw [tripleU, mem_rconj]
    have e : tripleConj g h k * (y * x * y⁻¹) * (tripleConj g h k)⁻¹ =
        (tripleConj g h k * y * (tripleConj g h k)⁻¹) *
          (tripleConj g h k * x * (tripleConj g h k)⁻¹) *
          (tripleConj g h k * y * (tripleConj g h k)⁻¹)⁻¹ := by group
    rw [e]
    exact h3
  · intro k x hx y hy
    have h1 := St.hyp.base.G22_commutator_mem (mem_rconj.1 hx) (mem_rconj.1 hy)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ rconj V₁ (tripleConj g h k) := by
      rw [mem_rconj]
      have : tripleConj g h k * (x * y * x⁻¹ * y⁻¹) * (tripleConj g h k)⁻¹ =
          (tripleConj g h k * x * (tripleConj g h k)⁻¹) *
            (tripleConj g h k * y * (tripleConj g h k)⁻¹) *
            (tripleConj g h k * x * (tripleConj g h k)⁻¹)⁻¹ *
            (tripleConj g h k * y * (tripleConj g h k)⁻¹)⁻¹ := by group
      rwa [this]
    exact hVS₂ (hV1 k h2)
  · intro k x hx
    have h1 := St.hyp.base.G22_sq_mem (mem_rconj.1 hx)
    have h2 : x * x ∈ rconj V₁ (tripleConj g h k) := by
      rw [mem_rconj]
      have : tripleConj g h k * (x * x) * (tripleConj g h k)⁻¹ =
          (tripleConj g h k * x * (tripleConj g h k)⁻¹) ^ 2 := by
        rw [pow_two]
        group
      rwa [this]
    exact hVS₂ (hV1 k h2)
  ·
    have hS₂U : TripleGrp.S₂ (tripleU (conjClosure V H) g h) ≤ conjClosure V H := by
      intro y hy
      have := hy.1.1
      rwa [tripleU_zero] at this
    exact le_pCoreOf_of_le_normalizer 2 (hS₂U.trans hUI) hS₂N (St.isPGroup_U.to_le hS₂U)
  · intro x hx y hy
    exact (Subgroup.mem_normalizer_iff.1 (hS₂N hx) y).1 hy
  ·
    have h3 := (St.hyp.G25_three (U := conjClosure V H) (I := L ⊔ conjClosure V H)
      (S := pCoreOf 2 (L ⊔ conjClosure V H))
      (W := conjClosure V H ⊓ pCoreOf 2 (L ⊔ conjClosure V H)) rfl hg hh hV hI.symm rfl rfl).1
    have hnorm : ∀ a ∈ L, a ∈ Subgroup.normalizer
        ((pCoreOf 2 (L ⊔ conjClosure V H) : Subgroup G) : Set G) := fun a ha =>
      (le_normalizer_of_conj_mem (fun x hx y hy => hINorm x hx y hy)) (hLI ha)
    rw [tripleU_zero, tripleU_one, tripleU_two]
    rw [← rconj_inf_eq_of_normalizes (hnorm g hg), ← rconj_inf_eq_of_normalizes (hnorm h hh)]
    exact h3

end L3Setting

end CFSG.Quasithin
