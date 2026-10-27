module

public import CFSG.Quasithin.EmptyFaithful.S153E56P2
public import CFSG.Quasithin.EmptyFaithful.S153E56Geo
public import CFSG.Quasithin.EmptyFaithful.S153E57D
public import CFSG.Quasithin.EmptyFaithful.S153E57A
public import CFSG.Quasithin.EmptyFaithful.S153EInputs

public section

namespace CFSG.Quasithin

namespace S153E56p

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153E CFSG.Quasithin.S153E57
open scoped commutatorElement Pointwise

structure Ctx56 {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G)
    (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) (s : ℕ) (y t₁ : G) : Prop where
  cx : Ctx15350 T Mc M V₁ V₂ t
  c : Chain15353 cx N₁ N₂
  hy : y ∈ Yi153 T Mc M V₁ N₁
  ht₁ : t₁ ∈ T ∧ t₁ ∉ UCT153 T M V₁ Mc
  hG : Geo56 cx s y t₁

section General

variable {G : Type} [Group G]

theorem mem_normalizer_conjSubgroup {A : Subgroup G} {g x : G} :
    x ∈ Subgroup.normalizer (conjSubgroup A g : Set G) ↔ g * x * g⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
  simp only [Subgroup.mem_normalizer_iff, mem_conjSubgroup_iff]
  constructor
  · intro h k
    have := h (g⁻¹ * k * g)
    have e1 : g * (g⁻¹ * k * g) * g⁻¹ = k := by group
    have e2 : g * (x * (g⁻¹ * k * g) * x⁻¹) * g⁻¹ = g * x * g⁻¹ * k * (g * x * g⁻¹)⁻¹ := by group
    rwa [e1, e2] at this
  · intro h k
    have := h (g * k * g⁻¹)
    have e2 : g * (x * k * x⁻¹) * g⁻¹ = g * x * g⁻¹ * (g * k * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
    rwa [e2]

end General

section Setting

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {s : ℕ} {y t₁ : G}
  (S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁)

include S

theorem Z_le_U : quasithinOmegaOneCenter T ≤ UH153 T M V₁ Mc :=
  (Z_le_ZS S.cx).trans (ZS_le_U S.cx)

theorem Z_comm_Mc {z m : G} (hz : z ∈ quasithinOmegaOneCenter T) (hm : m ∈ Mc) : z * m = m * z :=
  Subgroup.mem_centralizer_iff.1 (Mc_le_centralizer_Z S.cx hm) z hz

theorem U_le_Mc : UH153 T M V₁ Mc ≤ Mc := (U_le_T S.cx).trans (T_le_Mc S.cx)

theorem exPair_U : ExtraPair (UH153 T M V₁ Mc) (quasithinOmegaOneCenter T) where
  card_Z := Z_card S.cx
  Z_le := Z_le_U S
  central := fun _ hz _ hu => Z_comm_Mc S hz (U_le_Mc S hu)
  comm_mem := fun _ hu _ hv => commutator_U_mem S.cx hu hv
  sq_mem := fun _ hu => sq_U_mem S.cx hu
  rad := fun u hu h => by
    have hmem : u ∈ centerOf (UH153 T M V₁ Mc) := by
      refine ⟨hu, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
      exact (commutatorElement_eq_one_iff_mul_comm.1 (h v hv)).symm
    rw [S.hG.Z_center] at hmem
    exact hmem

theorem exPair_U' :
    ExtraPair (conjSubgroup (UH153 T M V₁ Mc) y) (conjSubgroup (quasithinOmegaOneCenter T) y) :=
  (exPair_U S).conj y

theorem E_le_U : Egp153 T M V₁ Mc y ≤ UH153 T M V₁ Mc := by
  rw [S.hG.E_eq]; exact inf_le_left

theorem E_le_U' : Egp153 T M V₁ Mc y ≤ conjSubgroup (UH153 T M V₁ Mc) y := by
  rw [S.hG.E_eq]; exact inf_le_right

theorem Z_le_E : quasithinOmegaOneCenter T ≤ Egp153 T M V₁ Mc y := S.hG.E_sing.1

theorem Z'_le_E : conjSubgroup (quasithinOmegaOneCenter T) y ≤ Egp153 T M V₁ Mc y :=
  le_sup_right.trans S.hG.V0_le_E

theorem V0_le_E : quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤
    Egp153 T M V₁ Mc y := S.hG.V0_le_E

theorem X_le_U' : Xgp153 T M V₁ Mc y ≤ conjSubgroup (UH153 T M V₁ Mc) y := by
  rw [S.hG.X_eq]; exact inf_le_left

theorem comm_XE {x e : G} (hx : x ∈ Xgp153 T M V₁ Mc y) (he : e ∈ Egp153 T M V₁ Mc y) :
    ⁅x, e⁆ ∈ conjSubgroup (quasithinOmegaOneCenter T) y :=
  (exPair_U' S).comm_mem x (X_le_U' S hx) e (E_le_U' S he)

theorem E_comm {e e' : G} (he : e ∈ Egp153 T M V₁ Mc y) (he' : e' ∈ Egp153 T M V₁ Mc y) :
    e * e' = e' * e := by
  have h1 : ⁅e, e'⁆ ∈ quasithinOmegaOneCenter T := (exPair_U S).comm_mem e (E_le_U S he) e' (E_le_U S he')
  have h2 : ⁅e, e'⁆ ∈ conjSubgroup (quasithinOmegaOneCenter T) y :=
    (exPair_U' S).comm_mem e (E_le_U' S he) e' (E_le_U' S he')
  have h3 : ⁅e, e'⁆ ∈ quasithinOmegaOneCenter T ⊓ conjSubgroup (quasithinOmegaOneCenter T) y := ⟨h1, h2⟩
  rw [S.hG.Z_inf_Z', Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h3

theorem E_elemAbelian : IsElemAbelian 2 (Egp153 T M V₁ Mc y) :=
  B6.isElemAbelian_iff.2 ⟨fun _ ha _ hb => E_comm S ha hb, S.hG.E_sing.2.1⟩

theorem X_conj_E {x e : G} (hx : x ∈ Xgp153 T M V₁ Mc y) (he : e ∈ Egp153 T M V₁ Mc y) :
    x * e * x⁻¹ ∈ Egp153 T M V₁ Mc y := by
  have e1 : x * e * x⁻¹ = ⁅x, e⁆ * e := by
    simp only [commutatorElement_def]
    group
  rw [e1]
  exact Subgroup.mul_mem _ (Z'_le_E S (comm_XE S hx he)) he

theorem X_le_normalizer_E : Xgp153 T M V₁ Mc y ≤
    Subgroup.normalizer (Egp153 T M V₁ Mc y : Set G) :=
  le_normalizer_of_conj_mem fun _ hx _ he => X_conj_E S hx he

theorem X_le_Mc : Xgp153 T M V₁ Mc y ≤ Mc := S.hG.X_le_Mc

theorem X_le_NZ : Xgp153 T M V₁ Mc y ≤ NZ T := fun _ hx => Mc_le_NZ S.cx (S.hG.X_le_Mc hx)

theorem t₁_mem_T : t₁ ∈ T := S.ht₁.1

theorem t₁_mem_Mc : t₁ ∈ Mc := T_le_Mc S.cx S.ht₁.1

theorem t₁_comm_Z {z : G} (hz : z ∈ quasithinOmegaOneCenter T) : z * t₁ = t₁ * z :=
  Z_comm_Mc S hz (t₁_mem_Mc S)

theorem t₁_conj_Z {z : G} (hz : z ∈ quasithinOmegaOneCenter T) : t₁ * z * t₁⁻¹ = z := by
  rw [← t₁_comm_Z S hz]; group

theorem t₁_inv_conj_Z {z : G} (hz : z ∈ quasithinOmegaOneCenter T) : t₁⁻¹ * z * t₁ = z := by
  have h := t₁_comm_Z S hz
  calc t₁⁻¹ * z * t₁ = t₁⁻¹ * (z * t₁) := by rw [mul_assoc]
    _ = t₁⁻¹ * (t₁ * z) := by rw [h]
    _ = z := by group

theorem conj_t₁_U {u : G} (hu : u ∈ UH153 T M V₁ Mc) : t₁ * u * t₁⁻¹ ∈ UH153 T M V₁ Mc :=
  U_conj_mem (t₁_mem_Mc S) hu

theorem conj_t₁_inv_U {u : G} (hu : u ∈ UH153 T M V₁ Mc) : t₁⁻¹ * u * t₁ ∈ UH153 T M V₁ Mc := by
  have := U_conj_mem (Mc.inv_mem (t₁_mem_Mc S)) hu
  simpa using this

theorem t₁_mem_normalizer_V : t₁ ∈ Subgroup.normalizer (VZ T M : Set G) := T_le_N S.cx S.ht₁.1

theorem conj_t₁_V {v : G} (hv : v ∈ VZ T M) : t₁ * v * t₁⁻¹ ∈ VZ T M :=
  (Subgroup.mem_normalizer_iff.1 (t₁_mem_normalizer_V S) v).1 hv

theorem conj_t₁_inv_V {v : G} (hv : v ∈ VZ T M) : t₁⁻¹ * v * t₁ ∈ VZ T M := by
  have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (VZ T M : Set G)).inv_mem
    (t₁_mem_normalizer_V S)) v).1 hv
  simpa using this

theorem y_mem_Y : y ∈ Y153 Mc M := Yi_le_Y N₁ S.hy

theorem y_inv_mem_normalizer_V : y⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
  (Subgroup.normalizer (VZ T M : Set G)).inv_mem
    (S.cx.c.hyp.le_normalizer (Y153_le Mc M (y_mem_Y S)))

theorem Z_le_V : quasithinOmegaOneCenter T ≤ VZ T M := S.cx.c.hyp.Z_le_VZ

theorem Z'_le_V : conjSubgroup (quasithinOmegaOneCenter T) y ≤ VZ T M := by
  intro z hz
  rw [mem_conjSubgroup_iff] at hz
  have := (Subgroup.mem_normalizer_iff.1 (y_inv_mem_normalizer_V S) _).1 (Z_le_V S hz)
  have e : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z := by group
  rwa [e] at this

theorem V0_le_V : quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤
    VZ T M := sup_le (Z_le_V S) (Z'_le_V S)

theorem V0_le_U : quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤
    UH153 T M V₁ Mc := (V0_le_E S).trans (E_le_U S)

theorem V_comm {v v' : G} (hv : v ∈ VZ T M) (hv' : v' ∈ VZ T M) : v * v' = v' * v :=
  B2F.isElemAbelian_comm S.cx.c.hyp.elemAbelian hv hv'

theorem E'_le_U : conjSubgroup (Egp153 T M V₁ Mc y) t₁ ≤ UH153 T M V₁ Mc := fun x hx => by
  rw [mem_conjSubgroup_iff] at hx
  have := conj_t₁_inv_U S (E_le_U S hx)
  simpa [mul_assoc] using this

theorem Z_le_E' : quasithinOmegaOneCenter T ≤ conjSubgroup (Egp153 T M V₁ Mc y) t₁ := fun z hz => by
  rw [mem_conjSubgroup_iff, t₁_conj_Z S hz]
  exact Z_le_E S hz

theorem E'_comm {e e' : G} (he : e ∈ conjSubgroup (Egp153 T M V₁ Mc y) t₁)
    (he' : e' ∈ conjSubgroup (Egp153 T M V₁ Mc y) t₁) : e * e' = e' * e := by
  rw [mem_conjSubgroup_iff] at he he'
  have := E_comm S he he'
  have e1 : t₁ * (e * e') * t₁⁻¹ = t₁ * (e' * e) * t₁⁻¹ := by
    calc t₁ * (e * e') * t₁⁻¹ = (t₁ * e * t₁⁻¹) * (t₁ * e' * t₁⁻¹) := by group
      _ = (t₁ * e' * t₁⁻¹) * (t₁ * e * t₁⁻¹) := this
      _ = t₁ * (e' * e) * t₁⁻¹ := by group
  simpa using e1

theorem EEt : Egp153 T M V₁ Mc y ⊓ conjSubgroup (Egp153 T M V₁ Mc y) t₁ ≤
    quasithinOmegaOneCenter T := S.hG.EEt

theorem V0'_le_VU : conjSubgroup (quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y) t₁ ≤
    VZ T M ⊓ UH153 T M V₁ Mc := fun v hv => by
  rw [mem_conjSubgroup_iff] at hv
  refine ⟨?_, ?_⟩
  · have := conj_t₁_inv_V S (V0_le_V S hv)
    simpa [mul_assoc] using this
  · have := conj_t₁_inv_U S (V0_le_U S hv)
    simpa [mul_assoc] using this

theorem Z_le_V0' : quasithinOmegaOneCenter T ≤
    conjSubgroup (quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y) t₁ :=
  fun z hz => by
    rw [mem_conjSubgroup_iff, t₁_conj_Z S hz]
    exact Subgroup.mem_sup_left hz

theorem X_le_normalizer_V0' : Xgp153 T M V₁ Mc y ≤ Subgroup.normalizer
    (conjSubgroup (quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y) t₁ :
      Set G) := by
  refine le_normalizer_of_conj_mem fun x hx v hv => ?_
  have h1 := S.hG.X_perp x hx v (V0'_le_VU S hv)
  have e : x * v * x⁻¹ = (x * v * x⁻¹ * v⁻¹) * v := by group
  rw [e]
  exact Subgroup.mul_mem _ (Z_le_V0' S h1) hv

theorem X_le_normalizer_E' : Xgp153 T M V₁ Mc y ≤
    Subgroup.normalizer (conjSubgroup (Egp153 T M V₁ Mc y) t₁ : Set G) := by
  intro x hx
  have h1 := X_le_normalizer_V0' S hx
  rw [mem_normalizer_conjSubgroup] at h1 ⊢
  exact S.hG.EN h1

theorem X_conj_E' {x e : G} (hx : x ∈ Xgp153 T M V₁ Mc y)
    (he : e ∈ conjSubgroup (Egp153 T M V₁ Mc y) t₁) :
    x * e * x⁻¹ ∈ conjSubgroup (Egp153 T M V₁ Mc y) t₁ :=
  (Subgroup.mem_normalizer_iff.1 (X_le_normalizer_E' S hx) e).1 he

end Setting

end S153E56p

end CFSG.Quasithin
