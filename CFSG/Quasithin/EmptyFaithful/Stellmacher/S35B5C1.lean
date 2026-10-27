module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModG
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChCent

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

theorem Wb_le_stab_of_path (hS : Sit H M S) {β l δ : Geo H M} (hl : l ∈ nbrs β)
    (hδ : δ ∈ nbrs l) : Wb δ ≤ stab β :=
  (Wb_le_Ql hS (mem_nbrs_symm.mp hδ)).trans (Qv_le_stab hS (mem_nbrs_symm.mp hl))

theorem conj_eq_of_mem_Vn_Wb (hS : Sit H M S) (x : Geo H M) {r w : G} (hr : r ∈ Vn x)
    (hw : w ∈ Wb x) : w * r * w⁻¹ = r := by
  have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (comm_Vn_Wb hS x)
  have := (Subgroup.mem_centralizer_iff.mp (h hr)) w hw
  rw [mul_inv_eq_iff_eq_mul]
  exact this

@[expose] def stabVec (w : orth.W) : Subgroup (Perm (Fin 5)) where
  carrier := {σ | orth.act σ w = w}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show orth.act (a * b) w = w
    rw [map_mul, MulAut.mul_apply]
    have ha' : orth.act a w = w := ha
    have hb' : orth.act b w = w := hb
    rw [hb', ha']
  inv_mem' := fun {a} ha => by
    show orth.act a⁻¹ w = w
    have ha' : orth.act a w = w := ha
    calc orth.act a⁻¹ w = orth.act a⁻¹ (orth.act a w) := by rw [ha']
      _ = w := by rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem mem_stabVec {w : orth.W} {σ : Perm (Fin 5)} : σ ∈ stabVec w ↔ orth.act σ w = w := Iff.rfl

theorem mem_Zv_of_centralised (hC : Ch.Ctx H M S) {β l δ l0 γ : Geo H M}
    (hcfg : Cfg H M β l δ l0 γ) (hgen : stab β ≤ Wb δ ⊔ Wb γ ⊔ Qv β) {r : G} (hr : r ∈ Vn β)
    (hδ : ∀ w ∈ Wb δ, w * r * w⁻¹ = r) (hγ : ∀ w ∈ Wb γ, w * r * w⁻¹ = r) : r ∈ Zv β := by
  have hS := hC.sit
  have hβ := hcfg.vβ
  obtain ⟨c⟩ := hC.nonempty_chart hβ
  let x : ↥(Vn β) := ⟨r, hr⟩
  have key : ∀ g : ↥(stab β), (g : G) * r * (g : G)⁻¹ = r → c.θ g ∈ stabVec (c.π x) := by
    intro g hg
    rw [mem_stabVec, ← c.π_conj g x]
    congr 1
    exact Subtype.ext hg
  have hF1 : Wb δ ≤ c.preθ (stabVec (c.π x)) := fun w hw =>
    (c.mem_preθ_iff ⟨w, Wb_le_stab_of_path hS hcfg.l_nbr hcfg.δ_nbr hw⟩).mpr (key _ (hδ w hw))
  have hF2 : Wb γ ≤ c.preθ (stabVec (c.π x)) := fun w hw =>
    (c.mem_preθ_iff ⟨w, Wb_le_stab_of_path hS hcfg.l0_nbr hcfg.γ_nbr hw⟩).mpr (key _ (hγ w hw))
  have hF : stab β ≤ c.preθ (stabVec (c.π x)) :=
    hgen.trans (sup_le (sup_le hF1 hF2) (c.Qv_le_preθ hS hβ _))
  have hall : ∀ σ : Perm (Fin 5), orth.act σ (c.π x) = c.π x := by
    intro σ
    obtain ⟨g, rfl⟩ := c.surj σ
    exact (c.mem_preθ_iff g).mp (hF g.2)
  have h1 : c.π x = 1 := S43.orth_fix_alt (c.π x) (fun σ _ => hall σ)
  exact (c.π_eq_one x).mp h1

theorem case1_false (hC : Ch.Ctx H M S)
    (hsec : ∀ β : Geo H M, vtype β = false → IsSec (stab β) (Vn β) (Wb β))
    {β l δ l0 γ : Geo H M} (hcfg : Cfg H M β l δ l0 γ)
    (hgen : stab β ≤ Wb δ ⊔ Wb γ ⊔ Qv β) (hne : ⁅Vn δ, Vn γ⁆ ≠ ⊥) : False := by
  have hS := hC.sit
  have hβ := hcfg.vβ
  have hδ := hcfg.vδ
  have hR1 : ⁅Vn δ, Vn γ⁆ ≤ Vn δ ⊓ Vn γ :=
    commutator_le_inf_of_normalizes ((hcfg.Vδ_le_stab_γ hS).trans (Vn_normal γ))
      ((hcfg.Vγ_le_stab_δ hS).trans (Vn_normal δ))
  have hR2 : ⁅Vn δ, Vn γ⁆ ≤ Vn β := Subgroup.commutator_le.mpr fun x hx y hy =>
    (hsec β hβ).comm x (hcfg.Vδ_le_Wb hx) y (hcfg.Vγ_le_Wb hy)
  have hRZ : ⁅Vn δ, Vn γ⁆ ≤ Zv β := fun r hr =>
    mem_Zv_of_centralised hC hcfg hgen (hR2 hr)
      (fun w hw => conj_eq_of_mem_Vn_Wb hS δ (hR1 hr).1 hw)
      (fun w hw => conj_eq_of_mem_Vn_Wb hS γ (hR1 hr).2 hw)
  obtain ⟨c⟩ := hC.nonempty_chart hδ
  have hVγ : Vn γ ≤ Qv δ := fun v hv =>
    c.mem_Qv_of_comm_le_Zv_nbr hS hδ (mem_nbrs_symm.mp hcfg.δ_nbr) (hcfg.Vγ_le_stab_δ hS hv)
      (((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hv)).trans hRZ).trans
        (Zv_le_Zv_of_nbr hS hβ hcfg.l_nbr))
  have hRδ : ⁅Vn δ, Vn γ⁆ ≤ Zv δ :=
    (Subgroup.commutator_mono le_rfl hVγ).trans (comm_Vn_Qv hS hδ).le
  have hinf := (Zv_ne hS hcfg.vl (mem_nbrs_symm.mp hcfg.l_nbr) hcfg.δ_nbr
    (Ne.symm hcfg.δ_ne)).2.2
  exact hne (le_bot_iff.mp (hinf ▸ le_inf hRZ hRδ))

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
