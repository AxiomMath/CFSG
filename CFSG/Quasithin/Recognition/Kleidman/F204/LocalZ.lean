module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalFive

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem exists_conj_stab_false_S (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) {T : Subgroup G} (hT : IsSylowTwoOf T (stab δ)) :
    ∃ h : G, conjSub h (stab δ) = P1 L1 L2 S ∧ conjSub h (Qv δ) = Q1 L1 L2 S ∧ conjSub h T = S := by
  obtain ⟨g, hg1, hg2⟩ := exists_conj_stab_false (L1 := L1) (L2 := L2) (S := S) hδ
  have hT' : IsSylowTwoOf (conjSub g T) (P1 L1 L2 S) := by
    have := isSylowTwoOf_conj hT g
    rwa [hg1] at this
  obtain ⟨x, hx, hle⟩ := isSylowTwoOf_exists_conj_le F.sylow_P1 hT'.1 hT'.2.1
  have hxS : IsSylowTwoOf (conjSub x S) (P1 L1 L2 S) := by
    have := isSylowTwoOf_conj F.sylow_P1 x
    rwa [conjSub_eq_of_mem hx] at this
  have heq : conjSub g T = conjSub x S := F1.eq_of_isSylowTwoOf_le hT' hxS.1 hxS.2.1 hle
  have hxn : x⁻¹ ∈ Subgroup.normalizer (P1 L1 L2 S : Set G) :=
    Subgroup.le_normalizer ((P1 L1 L2 S).inv_mem hx)
  have hxQ : x⁻¹ ∈ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    P1_le_normalizer_Q1 L1 L2 S ((P1 L1 L2 S).inv_mem hx)
  refine ⟨x⁻¹ * g, ?_, ?_, ?_⟩
  · rw [conjSub_mul, hg1]; exact conjSub_eq_of_mem_normalizer hxn
  · rw [conjSub_mul, hg2]; exact conjSub_eq_of_mem_normalizer hxQ
  · rw [conjSub_mul, heq, ← conjSub_mul, inv_mul_cancel, conjSub_one]

omit [Finite G] in
theorem pow_five_of_mem_X (F : Frame L1 L2 S D X) {x : G} (hx : x ∈ X) : x ^ 5 = 1 := by
  have := pow_card_eq_one' (G := ↥X) (x := ⟨x, hx⟩)
  rw [F.X_card] at this
  simpa using congrArg Subtype.val this

theorem Zv_eq_omega_of_five (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false)
    (h5 : ∀ x ∈ stab δ, x ^ 5 = 1 → x ∈ Subgroup.centralizer (Zv δ : Set G))
    {T : Subgroup G} (hT : IsSylowTwoOf T (stab δ)) : Zv δ = quasithinOmegaOneCenter T := by
  obtain ⟨h, hh1, hh2, hhT⟩ := exists_conj_stab_false_S F hδ hT
  have hWZ : quasithinOmegaOneCenter T ≤ Zv δ := by
    rw [Zv_eq_conjClosure hT]; exact le_conjClosure _ _
  apply le_antisymm _ hWZ
  rw [Zv_eq_conjClosure hT]
  refine conjClosure_le fun k hk z hz => ?_
  have hW : conjSub h (quasithinOmegaOneCenter T) = quasithinOmegaOneCenter S := by
    rw [conjSub_omegaOneCenter, hhT]
  have hkP : h * k * h⁻¹ ∈ P1 L1 L2 S := by
    rw [← hh1]; exact mem_conjSub_of_mem' hk
  have hzW : h * z * h⁻¹ ∈ quasithinOmegaOneCenter S := by
    rw [← hW]; exact mem_conjSub_of_mem' hz
  obtain ⟨x, hxX, b, hbB, hxb⟩ := F.exists_mul _ hkP
  have hbW : b * (h * z * h⁻¹) * b⁻¹ ∈ quasithinOmegaOneCenter S := by
    have e : conjSub b (quasithinOmegaOneCenter S) = quasithinOmegaOneCenter S := by
      rw [conjSub_omegaOneCenter, conjSub_eq_of_mem_normalizer (F.B_le_normalizer_S hbB)]
    rw [← e]; exact mem_conjSub_of_mem' hzW
  set w' := b * (h * z * h⁻¹) * b⁻¹ with hw'
  have hw'T : h⁻¹ * w' * h ∈ quasithinOmegaOneCenter T := by
    have : w' ∈ conjSub h (quasithinOmegaOneCenter T) := by rw [hW]; exact hbW
    exact mem_conjSub.mp this
  have hxP : x ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hxX
  have hx0 : h⁻¹ * x * h ∈ stab δ := by
    have : x ∈ conjSub h (stab δ) := by rw [hh1]; exact hxP
    exact mem_conjSub.mp this
  have hx05 : (h⁻¹ * x * h) ^ 5 = 1 := by
    have := conj_pow (a := h⁻¹) (b := x) (i := 5)
    simp only [inv_inv] at this
    rw [this, pow_five_of_mem_X F hxX]; group
  have hcent := Subgroup.mem_centralizer_iff.mp (h5 _ hx0 hx05) _ (hWZ hw'T)
  have key : x * w' * x⁻¹ = w' := by
    have e1 : h⁻¹ * (x * w' * x⁻¹) * h = (h⁻¹ * x * h) * (h⁻¹ * w' * h) * (h⁻¹ * x * h)⁻¹ := by
      group
    have e2 : (h⁻¹ * x * h) * (h⁻¹ * w' * h) * (h⁻¹ * x * h)⁻¹ = h⁻¹ * w' * h := by
      rw [← hcent]; group
    have e3 : h⁻¹ * (x * w' * x⁻¹) * h = h⁻¹ * w' * h := e1.trans e2
    have := congrArg (fun y => h * y * h⁻¹) e3
    simpa [mul_assoc] using this
  have hfin : h * (k * z * k⁻¹) * h⁻¹ = x * w' * x⁻¹ := by
    have e : h * (k * z * k⁻¹) * h⁻¹ = (h * k * h⁻¹) * (h * z * h⁻¹) * (h * k * h⁻¹)⁻¹ := by group
    rw [e, hxb, hw']
    group
  have : k * z * k⁻¹ = h⁻¹ * w' * h := by
    have := congrArg (fun y => h⁻¹ * y * h) hfin
    rw [key] at this
    simpa [mul_assoc] using this
  rw [this]
  exact hw'T

end CFSG.Quasithin.Kleidman.F204
