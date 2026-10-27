module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZI2Comm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem comm_mul_left_eq (r r' m : D) :
    r * r' * m * (r * r')⁻¹ * m⁻¹ =
      (r * (r' * m * r'⁻¹ * m⁻¹) * r⁻¹) * (r * m * r⁻¹ * m⁻¹) := by
  group

theorem conj_mem_ballStab {n : ℕ} {x : CosetGeom (A ⊔ B) A B} {g ρ : D} (hg : g ∈ stab x)
    (hρ : ρ ∈ ballStab n x) : g * ρ * g⁻¹ ∈ ballStab n x := by
  have hG : g ∈ A ⊔ B := stab_le x hg
  have h1 := ballStab_smul (⟨g, hG⟩ : ↥(A ⊔ B)) n x
  rw [smul_eq_of_mem_stab hg] at h1
  rw [h1]
  exact mul_mem_conjSub hρ

@[expose] def SwapProp (A B : Subgroup D) : Prop :=
  ∀ {u v w : CosetGeom (A ⊔ B) A B}, (graph (A ⊔ B) A B).Adj u v → vtype u = false →
    (graph (A ⊔ B) A B).Adj v w → w ≠ u →
      ∃ g : D, g ∈ ballStab 1 v ∧ g ∈ ballStab 1 u ∧ g ∉ ballStab 1 w

namespace GoldHyp3

variable [Finite D] (h : GoldHyp3 A B z V)

include h

omit [Finite D] in
theorem normal_transport {β a : CosetGeom (A ⊔ B) A B}
    (hM : ∀ g ∈ stab β, conjSub g (EtilT V z a ⊔ Vv V β) ≤ EtilT V z a ⊔ Vv V β)
    (g : ↥(A ⊔ B)) (hga : g • a = a) :
    ∀ k ∈ stab (g • β),
      conjSub k (EtilT V z a ⊔ Vv V (g • β)) ≤ EtilT V z a ⊔ Vv V (g • β) := by
  intro k hk
  have e : conjSub (g : D) (EtilT V z a ⊔ Vv V β) = EtilT V z a ⊔ Vv V (g • β) := by
    rw [conjSub_sup, h.conjSub_EtilT, hga, ← Vv_smul h.natural.reduced.2.1]
  rw [stab_smul, mem_conjSub] at hk
  have h1 := hM _ hk
  have e2 : k * (g : D) = (g : D) * ((g : D)⁻¹ * k * g) := by group
  calc conjSub k (EtilT V z a ⊔ Vv V (g • β))
      = conjSub k (conjSub (g : D) (EtilT V z a ⊔ Vv V β)) := by rw [e]
    _ = conjSub (k * (g : D)) (EtilT V z a ⊔ Vv V β) := by rw [conjSub_mul]
    _ = conjSub (g : D) (conjSub ((g : D)⁻¹ * k * g) (EtilT V z a ⊔ Vv V β)) := by
        rw [e2, conjSub_mul]
    _ ≤ conjSub (g : D) (EtilT V z a ⊔ Vv V β) := conjSub_mono _ h1
    _ = EtilT V z a ⊔ Vv V (g • β) := e

omit [Finite D] in
theorem EtilT_sup_eq {β a a' : CosetGeom (A ⊔ B) A B}
    (hM : ∀ g ∈ stab β, conjSub g (EtilT V z a ⊔ Vv V β) ≤ EtilT V z a ⊔ Vv V β)
    (ha : (graph (A ⊔ B) A B).Adj β a) (ha' : (graph (A ⊔ B) A B).Adj β a') :
    EtilT V z a' ⊔ Vv V β = EtilT V z a ⊔ Vv V β := by
  obtain ⟨g, hgβ, hga⟩ := exists_stab_smul_eq ha ha'
  have hgs : (g : D) ∈ stab β := mem_stab_of_smul_eq hgβ
  have e : conjSub (g : D) (EtilT V z a ⊔ Vv V β) = EtilT V z a' ⊔ Vv V β := by
    rw [conjSub_sup, h.conjSub_EtilT, ← Vv_smul h.natural.reduced.2.1, hga, hgβ]
  refine le_antisymm ?_ ?_
  · rw [← e]
    exact hM _ hgs
  · have h2 := (conjSub_le_iff _).mp (hM ((g : D)⁻¹) ((stab β).inv_mem hgs))
    rw [inv_inv, e] at h2
    exact h2

theorem comm_mem_sup_Vv {b : ℕ} (hb : critDist (A ⊔ B) A B V = b) (hb5 : 5 ≤ b)
    {β a a' : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (ha : (graph (A ⊔ B) A B).Adj β a) (ha' : (graph (A ⊔ B) A B).Adj β a')
    (hM : ∀ g ∈ stab β, conjSub g (EtilT V z a ⊔ Vv V β) ≤ EtilT V z a ⊔ Vv V β)
    {ρ : D} (hρβ : ρ ∈ ballStab 1 β) (hρa' : ρ ∈ ballStab 1 a') (hρa : ρ ∉ ballStab 1 a)
    {q m : D} (hq : q ∈ ballStab 1 β) (hm : m ∈ EtilT V z a ⊔ Vv V β) :
    q * m * q⁻¹ * m⁻¹ ∈ Vv V a ⊔ Vv V a' := by
  obtain ⟨r, ⟨hrβ, hra⟩, r', ⟨hr'β, hr'a'⟩, rfl⟩ :=
    h.exists_mul_of_mem_ballStab_one ha hρβ hρa' hρa hq
  have hat : vtype a = false := vtype_eq_false_of_adj ha hβ
  have hat' : vtype a' = false := vtype_eq_false_of_adj ha' hβ
  have h1 : r * m * r⁻¹ * m⁻¹ ∈ Vv V a :=
    h.comm_mem_Vv_of_mem_sup hb hb5 hat ha.symm hra hrβ hm
  have hm' : m ∈ EtilT V z a' ⊔ Vv V β := by
    rw [h.EtilT_sup_eq hM ha ha']
    exact hm
  have h2 : r' * m * r'⁻¹ * m⁻¹ ∈ Vv V a' :=
    h.comm_mem_Vv_of_mem_sup hb hb5 hat' ha'.symm hr'a' hr'β hm'
  have hrs : r ∈ stab a' :=
    ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr ha').le hrβ
  have h3 : r * (r' * m * r'⁻¹ * m⁻¹) * r⁻¹ ∈ Vv V a' :=
    (Subgroup.mem_normalizer_iff.mp (h.stab_le_normalizer_Vv' a' hrs) _).mp h2
  rw [comm_mul_left_eq]
  exact (Vv V a ⊔ Vv V a').mul_mem (Subgroup.mem_sup_right h3) (Subgroup.mem_sup_left h1)

theorem comm_mem_Zv_of_normal {b : ℕ} (hb : critDist (A ⊔ B) A B V = b) (hb5 : 5 ≤ b)
    (hC2 : InvLeZvProp A B z V) {β a a' : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (ha : (graph (A ⊔ B) A B).Adj β a) (ha' : (graph (A ⊔ B) A B).Adj β a') (haa' : a ≠ a')
    (hM : ∀ g ∈ stab β, conjSub g (EtilT V z a ⊔ Vv V β) ≤ EtilT V z a ⊔ Vv V β)
    {ρ : D} (hρβ : ρ ∈ ballStab 1 β) (hρa' : ρ ∈ ballStab 1 a') (hρa : ρ ∉ ballStab 1 a)
    {w : D} (hw : w ∈ EtilT V z a ⊔ Vv V β) : ρ * w * ρ⁻¹ * w⁻¹ ∈ Zv z β := by
  set c : D := ρ * w * ρ⁻¹ * w⁻¹ with hc
  set S : Set D := {x | ∃ g ∈ stab β, x = g * c * g⁻¹} with hS
  have hXle : Subgroup.closure S ≤ Vv V a ⊔ Vv V a' := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    have hgρ : g * ρ * g⁻¹ ∈ ballStab 1 β := conj_mem_ballStab hg hρβ
    have hgw : g * w * g⁻¹ ∈ EtilT V z a ⊔ Vv V β := hM g hg (mul_mem_conjSub hw)
    have := h.comm_mem_sup_Vv hb hb5 hβ ha ha' hM hρβ hρa' hρa hgρ hgw
    have e : g * c * g⁻¹ = (g * ρ * g⁻¹) * (g * w * g⁻¹) * (g * ρ * g⁻¹)⁻¹ * (g * w * g⁻¹)⁻¹ := by
      rw [hc]
      group
    rw [e]
    exact this
  have hinv : ∀ g ∈ stab β, conjSub g (Subgroup.closure S) ≤ Subgroup.closure S := by
    intro g hg
    rw [conjSub_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, ⟨g₁, hg₁, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨g * g₁, (stab β).mul_mem hg hg₁, by group⟩
  have hX := hC2 hβ ha ha' haa' hXle hinv
  exact hX (Subgroup.subset_closure ⟨1, (stab β).one_mem, by simp [hc]⟩)

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
