module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZI2Base
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WBase
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WTwoRank
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3YBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

@[expose] noncomputable def EtilT (V : Subgroup D) (z : D) (u : CosetGeom (A ⊔ B) A B) :
    Subgroup D :=
  Vv V u ⊔ ⨆ (γ : CosetGeom (A ⊔ B) A B) (_ : (graph (A ⊔ B) A B).Adj u γ), Theta z V u γ

theorem Theta_le_EtilT {u γ : CosetGeom (A ⊔ B) A B} (hadj : (graph (A ⊔ B) A B).Adj u γ) :
    Theta z V u γ ≤ EtilT V z u :=
  le_sup_of_le_right (le_iSup₂_of_le γ hadj le_rfl)

@[expose] def InvLeZvProp (A B : Subgroup D) (z : D) (V : Subgroup D) : Prop :=
  ∀ {β u₁ u₂ : CosetGeom (A ⊔ B) A B}, vtype β = true → (graph (A ⊔ B) A B).Adj β u₁ →
    (graph (A ⊔ B) A B).Adj β u₂ → u₁ ≠ u₂ → ∀ {X : Subgroup D}, X ≤ Vv V u₁ ⊔ Vv V u₂ →
      (∀ g ∈ stab β, conjSub g X ≤ X) → X ≤ Zv z β

namespace GoldHyp3

variable [Finite D] (h : GoldHyp3 A B z V)

include h

omit [Finite D] in
theorem conjSub_EtilT_le (g : ↥(A ⊔ B)) (u : CosetGeom (A ⊔ B) A B) :
    conjSub (g : D) (EtilT V z u) ≤ EtilT V z (g • u) := by
  unfold EtilT
  rw [conjSub_sup]
  refine sup_le ?_ ?_
  · rw [← Vv_smul h.natural.reduced.2.1]
    exact le_sup_left
  · rw [conjSub_le_iff]
    refine iSup₂_le fun γ hγ => ?_
    rw [← conjSub_le_iff, ← h.Theta_smul g u γ]
    exact le_sup_of_le_right (le_iSup₂_of_le (g • γ) ((smul_adj g).mpr hγ) le_rfl)

omit [Finite D] in
theorem conjSub_EtilT (g : ↥(A ⊔ B)) (u : CosetGeom (A ⊔ B) A B) :
    conjSub (g : D) (EtilT V z u) = EtilT V z (g • u) := by
  refine le_antisymm (h.conjSub_EtilT_le g u) ?_
  have h2 := h.conjSub_EtilT_le g⁻¹ (g • u)
  rw [inv_smul_smul, Subgroup.coe_inv] at h2
  have h3 := (conjSub_le_iff _).mp h2
  rwa [inv_inv] at h3

theorem Vn_two_comm {b : ℕ} (hb : critDist (A ⊔ B) A B V = b) (hb5 : 5 ≤ b)
    (x : CosetGeom (A ⊔ B) A B) : ∀ a ∈ Vn V 2 x, ∀ c ∈ Vn V 2 x, a * c = c * a := by
  intro a ha c hc
  have h1 := h.Vn_le_centralizer_Vn (n := 2) (n' := 2) hb (x := x) (x' := x)
    (by rw [CosetGeom.dist_self]; omega)
  exact (Subgroup.mem_centralizer_iff.mp (h1 ha) c hc).symm

theorem EtilT_le_commIn {b : ℕ} (hb : critDist (A ⊔ B) A B V = b) (hb5 : 5 ≤ b)
    {u : CosetGeom (A ⊔ B) A B} (hu : vtype u = false) {r : D} (hr : r ∈ ballStab 1 u) :
    EtilT V z u ≤ commIn (Vn V 2 u) (Vv V u) (h.Vn_two_comm hb hb5 u)
      (Vv_le_Vn hu (by simp [CosetGeom.dist_self])) r := by
  refine sup_le (fun m hm => ⟨Vv_le_Vn hu (by simp [CosetGeom.dist_self]) hm, ?_⟩)
    (iSup₂_le fun γ hγ m hm => ?_)
  · rw [h.ballStab_one_le_centralizer_Vv hu hr hm, mul_inv_cancel]
    exact (Vv V u).one_mem
  · have hrγ : r ∈ stab γ :=
      ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hγ).le hr
    refine ⟨Vv_B_le_Vn_two hu hγ (h.Theta_le_Vv hu hγ hm), ?_⟩
    exact h.Zv_le_Vv hγ hu (h.comm_Theta_le_Zv hu hγ ⟨ballStab_le_stab 1 u hr, hrγ⟩ hm)

theorem comm_mem_Vv_of_mem_sup {b : ℕ} (hb : critDist (A ⊔ B) A B V = b) (hb5 : 5 ≤ b)
    {u β : CosetGeom (A ⊔ B) A B} (hu : vtype u = false) (huβ : (graph (A ⊔ B) A B).Adj u β)
    {r m : D} (hru : r ∈ ballStab 1 u) (hrβ : r ∈ ballStab 1 β)
    (hm : m ∈ EtilT V z u ⊔ Vv V β) : r * m * r⁻¹ * m⁻¹ ∈ Vv V u := by
  have hβt : vtype β = true := vtype_eq_true_of_adj huβ hu
  have h2 : Vv V β ≤ commIn (Vn V 2 u) (Vv V u) (h.Vn_two_comm hb hb5 u)
      (Vv_le_Vn hu (by simp [CosetGeom.dist_self])) r := fun m hm =>
    ⟨Vv_B_le_Vn_two hu huβ hm,
      h.Zv_le_Vv huβ hu (h.commutator_mem_Zv_of_mem_ballStab_one hβt hrβ hm)⟩
  exact ((sup_le (h.EtilT_le_commIn hb hb5 hu hru) h2) hm).2

theorem smul_eq_third {u β γ₁ γ₂ : CosetGeom (A ⊔ B) A B} (h₁ : (graph (A ⊔ B) A B).Adj u β)
    (h₂ : (graph (A ⊔ B) A B).Adj u γ₁) (h₃ : (graph (A ⊔ B) A B).Adj u γ₂) (n12 : β ≠ γ₁)
    (n13 : β ≠ γ₂) (n23 : γ₁ ≠ γ₂) {g : ↥(A ⊔ B)} (hgu : g • u = u) (hgβ : g • β = β)
    (hg1 : g • γ₁ ≠ γ₁) : g • γ₁ = γ₂ := by
  by_contra hne
  have hadj : (graph (A ⊔ B) A B).Adj u (g • γ₁) := by
    have := (smul_adj g).mpr h₂
    rwa [hgu] at this
  have hβ : g • γ₁ ≠ β := fun e => n12 (smul_left_cancel g (e.trans hgβ.symm)).symm
  exact h.nbr_four h₁ h₂ h₃ hadj n12 n13 (Ne.symm hβ) n23 (Ne.symm hg1) (Ne.symm hne)

theorem mul_inv_mem_ballStab_one_of_swap {β a : CosetGeom (A ⊔ B) A B}
    (ha : (graph (A ⊔ B) A B).Adj β a) {ρ q : D} (hρβ : ρ ∈ ballStab 1 β)
    (hρa : ρ ∉ ballStab 1 a) (hq : q ∈ ballStab 1 β) (hqa : q ∉ ballStab 1 a) :
    q * ρ⁻¹ ∈ ballStab 1 a := by
  obtain ⟨γ₁, γ₂, h₂, h₃, n12, n13, n23⟩ := h.exists_two_others ha.symm
  have hd : CosetGeom.dist β a ≤ 1 := (CosetGeom.dist_eq_one_iff_adj.mpr ha).le
  have hρs : ρ ∈ stab a := ballStab_le_stab_of_dist_le hd hρβ
  have hqs : q ∈ stab a := ballStab_le_stab_of_dist_le hd hq
  have hρb : ρ ∈ stab β := ballStab_le_stab 1 β hρβ
  have hqb : q ∈ stab β := ballStab_le_stab 1 β hq
  have hρG : ρ ∈ A ⊔ B := stab_le β hρb
  have hqG : q ∈ A ⊔ B := stab_le β hqb
  have key : ∀ (x : D) (hxG : x ∈ A ⊔ B), x ∈ stab a → x ∈ stab β → x ∉ ballStab 1 a →
      (⟨x, hxG⟩ : ↥(A ⊔ B)) • γ₁ = γ₂ := by
    intro x hxG hxa hxb hxn
    refine h.smul_eq_third ha.symm h₂ h₃ n12 n13 n23 (smul_eq_of_mem_stab hxa)
      (smul_eq_of_mem_stab hxb) fun hfix => hxn ?_
    exact h.mem_ballStab_one_of_fix_two' ha.symm h₂ n12 hxa hxb (mem_stab_of_smul_eq hfix)
  have e1 := key ρ hρG hρs hρb hρa
  have e2 := key q hqG hqs hqb hqa
  have hρinv : (⟨ρ, hρG⟩ : ↥(A ⊔ B))⁻¹ • γ₂ = γ₁ := by
    rw [inv_smul_eq_iff, e1]
  have hfix : ((⟨q, hqG⟩ : ↥(A ⊔ B)) * (⟨ρ, hρG⟩ : ↥(A ⊔ B))⁻¹) • γ₂ = γ₂ := by
    rw [mul_smul, hρinv, e2]
  have hmem : q * ρ⁻¹ ∈ stab γ₂ := by simpa using mem_stab_of_smul_eq hfix
  exact h.mem_ballStab_one_of_fix_two' ha.symm h₃ n13 ((stab a).mul_mem hqs ((stab a).inv_mem hρs))
    ((stab β).mul_mem hqb ((stab β).inv_mem hρb)) hmem

theorem exists_mul_of_mem_ballStab_one {β a a' : CosetGeom (A ⊔ B) A B}
    (ha : (graph (A ⊔ B) A B).Adj β a) {ρ : D} (hρβ : ρ ∈ ballStab 1 β)
    (hρa' : ρ ∈ ballStab 1 a') (hρa : ρ ∉ ballStab 1 a) {q : D} (hq : q ∈ ballStab 1 β) :
    ∃ r ∈ ballStab 1 β ⊓ ballStab 1 a, ∃ r' ∈ ballStab 1 β ⊓ ballStab 1 a', q = r * r' := by
  by_cases hqa : q ∈ ballStab 1 a
  · exact ⟨q, ⟨hq, hqa⟩, 1, ⟨(ballStab 1 β).one_mem, (ballStab 1 a').one_mem⟩, by simp⟩
  · exact ⟨q * ρ⁻¹, ⟨(ballStab 1 β).mul_mem hq ((ballStab 1 β).inv_mem hρβ),
      h.mul_inv_mem_ballStab_one_of_swap ha hρβ hρa hq hqa⟩, ρ, ⟨hρβ, hρa'⟩, by group⟩

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
