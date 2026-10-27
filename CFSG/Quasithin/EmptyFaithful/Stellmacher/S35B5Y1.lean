module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChSyl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_of_conj {Y : Subgroup G} {x : G} (h1 : ∀ y ∈ Y, x * y * x⁻¹ ∈ Y)
    (h2 : ∀ y ∈ Y, x⁻¹ * y * x ∈ Y) : x ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h1 y, fun hy => ?_⟩
  simpa [mul_assoc] using h2 _ hy

omit [Finite G] in
theorem le_normalizer_of_forall_conj {W Y : Subgroup G}
    (h : ∀ w ∈ W, ∀ y ∈ Y, w * y * w⁻¹ ∈ Y) : W ≤ Subgroup.normalizer (Y : Set G) := fun w hw =>
  mem_normalizer_of_conj (h w hw) (fun y hy => by simpa using h w⁻¹ (W.inv_mem hw) y hy)

omit [Finite G] in
theorem conj_mem_sup_of_mem_normalizer {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G))
    {y : G} (hy : y ∈ A ⊔ B) : x * y * x⁻¹ ∈ A ⊔ B := by
  have h : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj x).toMonoidHom :=
    sup_le (fun a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha))
      (fun b hb => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB b).mp hb))
  simpa using h hy

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj (fun y hy => conj_mem_sup_of_mem_normalizer hA hB hy)
    (fun y hy => ?_)
  have hA' : x⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hA
  have hB' : x⁻¹ ∈ Subgroup.normalizer (B : Set G) := Subgroup.inv_mem _ hB
  simpa using conj_mem_sup_of_mem_normalizer hA' hB' hy

theorem Y_le_Kb (hS : Sit H M S) {β l δ l0 γ : Geo H M} (hcfg : Cfg H M β l δ l0 γ)
    (hcomm : ⁅Vn δ, Vn γ⁆ = ⊥) : Yg β δ γ ≤ Kb δ := by
  have hWc : Wb δ ≤ Subgroup.centralizer (Vn δ : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact comm_Vn_Wb hS δ
  have hγc : Vn γ ≤ Subgroup.centralizer (Vn δ : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  have hγQ : Vn γ ≤ Qv δ := fun x hx =>
    Vn_centralizer_le_Qv hS hcfg.vδ x (hcfg.Vγ_le_stab_δ hS hx) fun v hv => by
      have : v * x = x * v := Subgroup.mem_centralizer_iff.mp (hγc hx) v hv
      have e : x * v * x⁻¹ * v⁻¹ = 1 := by
        rw [← this]; group
      rw [e]; exact Subgroup.one_mem _
  have hδW : Vn δ ≤ Wb δ := Vn_le_Wb_self hS hcfg.vδ
  have hβW : Vn β ≤ Wb δ := hcfg.Vβ_le_Wδ
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_inf ((Vn_le_Qv_self hS δ)) (hδW.trans hWc)
  · exact le_inf hγQ hγc
  · exact le_inf (hβW.trans (Wb_le_Qv hS δ)) (hβW.trans hWc)

omit [Finite G] in
theorem Wb_le_normalizer_of_le_Kb (h15c : Claim15c H M) {δ : Geo H M} (hδ : vtype δ = false)
    {Y : Subgroup G} (hY : Y ≤ Kb δ) (hV : Vn δ ≤ Y) :
    Wb δ ≤ Subgroup.normalizer (Y : Set G) := by
  refine le_normalizer_of_forall_conj fun w hw y hy => ?_
  have h1 : ⁅w, y⁆ ∈ Vn δ := h15c δ hδ (Subgroup.commutator_mem_commutator hw (hY hy))
  have e : w * y * w⁻¹ = ⁅w, y⁆ * y := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact Y.mul_mem (hV h1) hy

omit [Finite G] in
theorem Yg_swap (β δ γ : Geo H M) : Yg β δ γ = Yg β γ δ := by
  unfold Yg
  rw [sup_comm (Vn δ)]

omit [Finite G] in
theorem Cfg.swap {β l δ l0 γ : Geo H M} (h : Cfg H M β l δ l0 γ) : Cfg H M β l0 γ l δ :=
  ⟨h.vβ, h.l0_nbr, h.γ_nbr, h.γ_ne, h.l_nbr, h.δ_nbr, h.δ_ne⟩

theorem Q0_le_normalizer_Y (hS : Sit H M S) {β l δ l0 γ : Geo H M}
    (hcfg : Cfg H M β l δ l0 γ) :
    Qv β ⊓ Qv l ⊓ Qv l0 ≤ Subgroup.normalizer ((Yg β δ γ : Subgroup G) : Set G) := by
  intro x hx
  have hxβ : x ∈ stab β := ((mem_Qv_iff hS β).mp hx.1.1).1
  have hxδ : x ∈ stab δ := Qv_le_stab hS hcfg.δ_nbr hx.1.2
  have hxγ : x ∈ stab γ := Qv_le_stab hS hcfg.γ_nbr hx.2
  exact mem_normalizer_sup (mem_normalizer_sup (Vn_normal δ hxδ) (Vn_normal γ hxγ))
    (Vn_normal β hxβ)

theorem Y_normalised (hC : Ch.Ctx H M S) (h15c : Claim15c H M)
    {β l δ l0 γ : Geo H M} (hcfg : Cfg H M β l δ l0 γ) (hcomm : ⁅Vn δ, Vn γ⁆ = ⊥) :
    Wb δ ≤ Subgroup.normalizer ((Yg β δ γ : Subgroup G) : Set G) ∧
    Wb γ ≤ Subgroup.normalizer ((Yg β δ γ : Subgroup G) : Set G) ∧
    Qv β ⊓ Qv l ⊓ Qv l0 ≤ Subgroup.normalizer ((Yg β δ γ : Subgroup G) : Set G) := by
  have hS := hC.sit
  refine ⟨Wb_le_normalizer_of_le_Kb h15c hcfg.vδ (Y_le_Kb hS hcfg hcomm)
    (le_sup_of_le_left le_sup_left), ?_, Q0_le_normalizer_Y hS hcfg⟩
  rw [Yg_swap]
  have hc' : ⁅Vn γ, Vn δ⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcomm
  exact Wb_le_normalizer_of_le_Kb h15c hcfg.vγ (Y_le_Kb hS hcfg.swap hc')
    (le_sup_of_le_left le_sup_left)

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
