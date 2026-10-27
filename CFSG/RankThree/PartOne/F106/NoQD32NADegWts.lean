module

public import CFSG.RankThree.PartOne.F106.NoQD32NADegLin
public import CFSG.RankThree.PartOne.N143X.Weights
public import CFSG.RankThree.PartOne.Q1327T.R8Core

public section

namespace CFSG.RankThree.PartOne.F106.NAD

open Matrix Module CFSG.RankThree.PartOne.N143X CFSG.RankThree.PartOne.Q1327T.R8
open scoped commutatorElement

section Center

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def Fz (Y : Subgroup (GL ι K)) : Subgroup (GL ι K) :=
  Y ⊓ Subgroup.centralizer (Y : Set (GL ι K))

theorem mem_Fz {Y : Subgroup (GL ι K)} {g : GL ι K} :
    g ∈ Fz Y ↔ g ∈ Y ∧ ∀ h ∈ Y, h * g = g * h := by
  simp [Fz, Subgroup.mem_centralizer_iff]

theorem Fz_le (Y : Subgroup (GL ι K)) : Fz Y ≤ Y := inf_le_left

theorem mul_comm_of_mem_Fz {Y : Subgroup (GL ι K)} {f y : GL ι K} (hf : f ∈ Fz Y) (hy : y ∈ Y) :
    y * f = f * y :=
  (mem_Fz.1 hf).2 y hy

theorem comm_mem_Fz {Y : Subgroup (GL ι K)}
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1) {a b : GL ι K} (ha : a ∈ Y) (hb : b ∈ Y) :
    ⁅a, b⁆ ∈ Fz Y := by
  refine mem_Fz.2 ⟨?_, fun h hh => ?_⟩
  · rw [commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb)
  · exact (commutatorElement_eq_one_iff_mul_comm.1 (hcl a ha b hb h hh)).symm

end Center

section Wv

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {L : Type} [Field L]
  {F : Subgroup (GL ι K)}

open scoped _root_.Classical in
@[expose] noncomputable def wv (χ : F → L) (g : GL ι K) : L :=
  if h : g ∈ F then χ ⟨g, h⟩ else 1

theorem wv_of_mem (χ : F → L) {g : GL ι K} (hg : g ∈ F) : wv χ g = χ ⟨g, hg⟩ := by
  simp [wv, hg]

theorem wv_inv (χ : F → L) (g : GL ι K) : wv (fun e => (χ e)⁻¹) g = (wv χ g)⁻¹ := by
  by_cases hg : g ∈ F
  · rw [wv_of_mem _ hg, wv_of_mem _ hg]
  · simp [wv, hg]

end Wv

section Joint

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (L : Type) [Field L]
  [Algebra K L] (Y : Subgroup (GL ι K))

theorem mapL_mem_joint {χ : Fz Y → L} {g : GL ι K} (hg : g ∈ Y) {v : ι → L}
    (hv : v ∈ joint L (Fz Y) χ) : mapL L g *ᵥ v ∈ joint L (Fz Y) χ := by
  rw [mem_joint] at hv ⊢
  intro e
  have h1 : mapL L (e : GL ι K) * mapL L g = mapL L g * mapL L (e : GL ι K) := by
    rw [← mapL_mul, ← mapL_mul, ← mul_comm_of_mem_Fz e.2 hg]
  rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, hv e, Matrix.mulVec_smul]

theorem mapL_comm_rel {χ : Fz Y → L} {a b : GL ι K} (ha : a ∈ Y) (hb : b ∈ Y)
    (hab : ⁅a, b⁆ ∈ Fz Y) {v : ι → L} (hv : v ∈ joint L (Fz Y) χ) :
    mapL L a *ᵥ (mapL L b *ᵥ v) = wv χ ⁅a, b⁆ • (mapL L b *ᵥ (mapL L a *ᵥ v)) := by
  have hw : mapL L b *ᵥ (mapL L a *ᵥ v) ∈ joint L (Fz Y) χ :=
    mapL_mem_joint L Y hb (mapL_mem_joint L Y ha hv)
  have e1 : a * b = ⁅a, b⁆ * (b * a) := by
    rw [commutatorElement_def]
    group
  calc mapL L a *ᵥ (mapL L b *ᵥ v) = mapL L (a * b) *ᵥ v := by
        rw [mapL_mul, Matrix.mulVec_mulVec]
    _ = mapL L (⁅a, b⁆ * (b * a)) *ᵥ v := by rw [e1]
    _ = mapL L ⁅a, b⁆ *ᵥ (mapL L b *ᵥ (mapL L a *ᵥ v)) := by
        simp only [mapL_mul, ← Matrix.mulVec_mulVec]
    _ = wv χ ⁅a, b⁆ • (mapL L b *ᵥ (mapL L a *ᵥ v)) := by
        rw [wv_of_mem χ hab]
        exact (mem_joint L (Fz Y)).1 hw ⟨_, hab⟩

@[expose] noncomputable def opJ (χ : Fz Y → L) {g : GL ι K} (hg : g ∈ Y) :
    Module.End L ↥(joint L (Fz Y) χ) :=
  (linL L g).restrict fun v hv => by
    rw [linL_apply]
    exact mapL_mem_joint L Y hg hv

theorem opJ_coe (χ : Fz Y → L) {g : GL ι K} (hg : g ∈ Y) (v : joint L (Fz Y) χ) :
    ((opJ L Y χ hg v : joint L (Fz Y) χ) : ι → L) = mapL L g *ᵥ (v : ι → L) := by
  rw [opJ, LinearMap.coe_restrict_apply, linL_apply]

theorem opJ_injective (χ : Fz Y → L) {g : GL ι K} (hg : g ∈ Y) :
    Function.Injective (opJ L Y χ hg) := by
  intro v w h
  have h1 : mapL L g *ᵥ (v : ι → L) = mapL L g *ᵥ (w : ι → L) := by
    rw [← opJ_coe L Y χ hg v, ← opJ_coe L Y χ hg w, h]
  have h2 : (v : ι → L) = (w : ι → L) := by
    have := congrArg (fun u => mapL L g⁻¹ *ᵥ u) h1
    simpa only [Matrix.mulVec_mulVec, ← mapL_mul, inv_mul_cancel, mapL_one,
      Matrix.one_mulVec] using this
  exact Subtype.ext h2

theorem opJ_rel (χ : Fz Y → L) {a b : GL ι K} (ha : a ∈ Y) (hb : b ∈ Y) (hab : ⁅a, b⁆ ∈ Fz Y)
    (v : joint L (Fz Y) χ) :
    opJ L Y χ ha (opJ L Y χ hb v) = wv χ ⁅a, b⁆ • opJ L Y χ hb (opJ L Y χ ha v) := by
  apply Subtype.ext
  rw [opJ_coe, opJ_coe, Submodule.coe_smul, opJ_coe, opJ_coe]
  exact mapL_comm_rel L Y ha hb hab v.2

variable {Y}

theorem weight_pow_eq_one_elem {χ : Fz Y → L} (hχ : joint L (Fz Y) χ ≠ ⊥) (e : Fz Y) {q : ℕ}
    (hq : (e : GL ι K) ^ q = 1) : χ e ^ q = 1 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hχ
  have h1 : (χ e ^ q) • v = (1 : L) • v := by
    rw [← pow_mulVec_eigen L ((mem_joint L (Fz Y)).1 hv e) q, ← mapLHom_apply, ← map_pow, hq]
    simp [mapLHom_apply, mapL_one]
  exact smul_left_injective L hv0 h1

theorem q_le_finrank_joint [IsAlgClosed L] {q : ℕ} (hq : q.Prime)
    (hcq : ∀ a ∈ Y, ∀ b ∈ Y, ⁅a, b⁆ ^ q = 1)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1) {χ : Fz Y → L}
    (hχ : joint L (Fz Y) χ ≠ ⊥) {a b : GL ι K} (ha : a ∈ Y) (hb : b ∈ Y)
    (h1 : wv χ ⁅a, b⁆ ≠ 1) : q ≤ finrank L ↥(joint L (Fz Y) χ) := by
  have : Nontrivial ↥(joint L (Fz Y) χ) := Submodule.nontrivial_iff_ne_bot.2 hχ
  have hab := comm_mem_Fz hcl ha hb
  refine le_finrank_of_pair hq (opJ L Y χ ha) (opJ L Y χ hb) (opJ_injective L Y χ ha)
    (opJ_injective L Y χ hb) ?_ h1 (opJ_rel L Y χ ha hb hab)
  rw [wv_of_mem χ hab]
  exact weight_pow_eq_one_elem L hχ ⟨_, hab⟩ (hcq a ha b hb)

theorem sq_le_finrank_joint [IsAlgClosed L] {q : ℕ} (hq : q.Prime)
    (hcq : ∀ a ∈ Y, ∀ b ∈ Y, ⁅a, b⁆ ^ q = 1)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1) {χ : Fz Y → L}
    (hχ : joint L (Fz Y) χ ≠ ⊥) {a₁ b₁ a₂ b₂ : GL ι K} (ha₁ : a₁ ∈ Y) (hb₁ : b₁ ∈ Y)
    (ha₂ : a₂ ∈ Y) (hb₂ : b₂ ∈ Y) (hne₁ : wv χ ⁅a₁, b₁⁆ ≠ 1) (hne₂ : wv χ ⁅a₂, b₂⁆ ≠ 1)
    (hc₁ : wv χ ⁅a₁, a₂⁆ = 1) (hc₂ : wv χ ⁅a₁, b₂⁆ = 1) :
    q ^ 2 ≤ finrank L ↥(joint L (Fz Y) χ) := by
  have : Nontrivial ↥(joint L (Fz Y) χ) := Submodule.nontrivial_iff_ne_bot.2 hχ
  have h11 := comm_mem_Fz hcl ha₁ hb₁
  have h22 := comm_mem_Fz hcl ha₂ hb₂
  refine sq_le_finrank_of_two_pairs hq (opJ L Y χ ha₁) (opJ L Y χ hb₁) (opJ L Y χ ha₂)
    (opJ L Y χ hb₂) (opJ_injective L Y χ ha₁) (opJ_injective L Y χ hb₁)
    (opJ_injective L Y χ ha₂) (opJ_injective L Y χ hb₂) ?_ hne₁ ?_ hne₂
    (opJ_rel L Y χ ha₁ hb₁ h11) (opJ_rel L Y χ ha₂ hb₂ h22) ?_ ?_
  · rw [wv_of_mem χ h11]
    exact weight_pow_eq_one_elem L hχ ⟨_, h11⟩ (hcq a₁ ha₁ b₁ hb₁)
  · rw [wv_of_mem χ h22]
    exact weight_pow_eq_one_elem L hχ ⟨_, h22⟩ (hcq a₂ ha₂ b₂ hb₂)
  · intro v
    have := opJ_rel L Y χ ha₁ ha₂ (comm_mem_Fz hcl ha₁ ha₂) v
    rwa [hc₁, one_smul] at this
  · intro v
    have := opJ_rel L Y χ ha₁ hb₂ (comm_mem_Fz hcl ha₁ hb₂) v
    rwa [hc₂, one_smul] at this

end Joint

end CFSG.RankThree.PartOne.F106.NAD
