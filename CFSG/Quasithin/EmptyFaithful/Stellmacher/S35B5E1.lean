module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChSyl
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
theorem conj_mem_of_le_normalizer {X N : Subgroup G} (h : X ≤ Subgroup.normalizer (N : Set G))
    {g s : G} (hg : g ∈ X) (hs : s ∈ N) : g * s * g⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.mp (h hg) s).mp hs

omit [Finite G] in
theorem conj_inv_mem_of_le_normalizer {X N : Subgroup G}
    (h : X ≤ Subgroup.normalizer (N : Set G)) {g s : G} (hg : g ∈ X) (hs : s ∈ N) :
    g⁻¹ * s * g ∈ N := by
  have := (Subgroup.mem_normalizer_iff.mp (h (X.inv_mem hg)) s).mp hs
  simpa using this

@[expose] def normClosure (X Y : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ g ∈ X, ∃ y ∈ Y, x = g * y * g⁻¹}

omit [Finite G] in
theorem le_normClosure {X Y : Subgroup G} : Y ≤ normClosure X Y := fun y hy =>
  Subgroup.subset_closure ⟨1, X.one_mem, y, hy, by simp⟩

omit [Finite G] in
theorem normalizer_normClosure {X Y : Subgroup G} :
    X ≤ Subgroup.normalizer (normClosure X Y : Set G) := by
  refine le_normalizer_closure _ ?_
  rintro k hk _ ⟨g, hg, y, hy, rfl⟩
  exact ⟨k * g, X.mul_mem hk hg, y, hy, by group⟩

omit [Finite G] in
theorem normClosure_le {X Y W : Subgroup G} (hW : X ≤ Subgroup.normalizer (W : Set G))
    (hY : Y ≤ W) : normClosure X Y ≤ W := by
  rw [normClosure, Subgroup.closure_le]
  rintro _ ⟨g, hg, y, hy, rfl⟩
  exact conj_mem_of_le_normalizer hW hg (hY hy)

omit [Finite G] in
theorem comm_normClosure_le {X Y L V : Subgroup G} (hVX : X ≤ Subgroup.normalizer (V : Set G))
    (hLX : X ≤ Subgroup.normalizer (L : Set G)) (hEX : normClosure X Y ≤ X)
    (hYL : ⁅Y, L⁆ ≤ V) : ⁅normClosure X Y, L⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro e he x hx
  induction he using Subgroup.closure_induction with
  | mem e he =>
    obtain ⟨g, hg, y, hy, rfl⟩ := he
    have h1 : g⁻¹ * x * g ∈ L := conj_inv_mem_of_le_normalizer hLX hg hx
    have h2 : ⁅y, g⁻¹ * x * g⁆ ∈ V := hYL (Subgroup.commutator_mem_commutator hy h1)
    have h3 := conj_mem_of_le_normalizer hVX hg h2
    have e : ⁅g * y * g⁻¹, x⁆ = g * ⁅y, g⁻¹ * x * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rwa [e]
  | one => simp
  | mul a b ha hb iha ihb =>
    have haX : a ∈ X := hEX ha
    have e : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem (conj_mem_of_le_normalizer hVX haX ihb) iha
  | inv a ha iha =>
    have haX : a ∈ X := hEX ha
    have e : ⁅a⁻¹, x⁆ = a⁻¹ * (⁅a, x⁆)⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact conj_inv_mem_of_le_normalizer hVX haX (V.inv_mem iha)

theorem six_b_contra (hC : Ch.Ctx H M S) (h6b : Claim6b H M)
    {β l δ l0 γ : Geo H M} (hcfg : Cfg H M β l δ l0 γ)
    (hYL : ⁅Yg β δ γ, Lr β⁆ ≤ Vn β) : False := by
  have hS := hC.sit
  have hYW : Yg β δ γ ≤ Wb β :=
    sup_le (sup_le hcfg.Vδ_le_Wb hcfg.Vγ_le_Wb) (Vn_le_Wb_self hS hcfg.vβ)
  have hEW : normClosure (stab β) (Yg β δ γ) ≤ Wb β := normClosure_le (Wb_normal β) hYW
  have hEX : normClosure (stab β) (Yg β δ γ) ≤ stab β :=
    hEW.trans ((Wb_le_Qv hS β).trans (Ch.Qv_le_stab' β))
  have hcomm : ⁅normClosure (stab β) (Yg β δ γ), Lr β⁆ ≤ Vn β :=
    comm_normClosure_le (Vn_normal β) (le_normalizer_oTwoRes _) hEX hYL
  have hVY : Vn β ≤ Yg β δ γ := le_sup_right
  have hδY : Vn δ ≤ Yg β δ γ := le_sup_left.trans le_sup_left
  have h1 := h6b β l δ (normClosure (stab β) (Yg β δ γ)) hcfg.vβ hcfg.l_nbr
    (mem_nbrs_symm.mp hcfg.δ_nbr) hcfg.δ_ne normalizer_normClosure (hVY.trans le_normClosure)
    hEW hcomm
  have h2 : Vn δ ≤ Vn β := by
    have : Vn δ ≤ Vn δ ⊓ normClosure (stab β) (Yg β δ γ) :=
      le_inf le_rfl (hδY.trans le_normClosure)
    rw [h1] at this
    exact this.trans inf_le_right
  obtain ⟨hc8, hc32⟩ := hC.caseI δ l β hcfg.vδ (mem_nbrs_symm.mp hcfg.δ_nbr)
    hcfg.l_nbr hcfg.δ_ne.symm
  have : Vn δ ⊓ Vn β = Vn δ := inf_eq_left.mpr h2
  rw [this] at hc8
  omega

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
