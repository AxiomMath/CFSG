module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7SqA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddThreeB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Gap7

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Sq

theorem exists_rot_comm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α ρ δ : Geo H M}
    (hs : Sit43 α) (h3 : bMin H M = 3) (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ) :
    ∃ d : G, d ∈ stab δ ∧ d ^ 3 = 1 ∧ d ≠ 1 ∧ ∀ c ∈ Cst δ, ⁅c, d⁆ ∈ Vn δ := by
  have hδv : vtype δ = true := Sit43.vtype_true_of_adj hρ hδ
  obtain ⟨γ, -, -, y, -, hyδ, hyQ, hyC⟩ := Three.exists_crit_elt hA h26 (hs.of_vtype_false hρ) h3 hδ
  have hCn : stab δ ≤ Subgroup.normalizer (Cst δ : Set G) := by
    have e : Cst δ = Qv δ ⊓ (stab δ ⊓ Subgroup.centralizer (Vn δ : Set G)) := by
      ext c
      exact ⟨fun h => ⟨h.1, pCoreOf_le 2 _ h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [e]
    exact le_normalizer_inf (le_normalizer_pCoreOf 2 _)
      (normalizer_inf_centralizer (stab_le_normalizer_Vn δ))
  obtain ⟨K, hK, hKX, hKn⟩ := exists_centralizer_quotient (X := stab δ) (N := Cst δ)
    (Z := Vn δ) (stab_le_normalizer_Vn δ) hCn
  have hKQ : ¬ K ≤ pCoreOf 2 (stab δ) := fun h => hyQ (h ((hK y).mpr ⟨hyδ, hyC⟩))
  have hT := sylow_stab_inf_left hA (nbrs_symm hδ)
  have hup := sup_sylow_eq_of_normal_not_le (Or.inl rfl) (quot_stab_three hA hδv) hT hKX hKn hKQ
  have hTn : stab δ ⊓ stab ρ ≤ Subgroup.normalizer (K : Set G) := inf_le_left.trans hKn
  have hL : oTwoRes (stab δ) ≤ K := oTwoRes_le_of_cover hKn hT.2.1 hT.1 fun x hx => by
    obtain ⟨c, hc, t, ht, e⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTn).mp (hup hx)
    exact ⟨c, hc, t, ht, e⟩
  obtain ⟨d, hd, hd3, hd1⟩ := Sit43.exists_d hA hδv
  have hdL : d ∈ oTwoRes (stab δ) := Subgroup.subset_closure ⟨hd, 3, by decide, hd3⟩
  exact ⟨d, hd, hd3, hd1, ((hK d).mp (hL hdL)).2⟩

theorem sq_mem_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α ρ δ : Geo H M}
    (hs : Sit43 α) (h3 : bMin H M = 3) (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ)
    (h6 : Nat.card (Vn δ) = 2 ^ 6) {c : G} (hc : c ∈ Cst δ) (hcV : c * c ∈ Vn δ) :
    c * c ∈ Yv δ := by
  have hδv : vtype δ = true := Sit43.vtype_true_of_adj hρ hδ
  obtain ⟨d, hd, hd3, hd1, hdC⟩ := exists_rot_comm hA h26 hs h3 hρ hδ
  have hVab : IsElemAbelian 2 (Vn δ) := isElemAbelian_Vn hA h3.ge δ
  rw [← (hs.centralizer_rot_iff hA h26 h3.ge hδv hd hd3 hd1).mpr h6]
  refine ⟨hcV, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  rw [Set.mem_singleton_iff] at hg
  subst hg
  have htV : ⁅c, g⁆⁻¹ ∈ Vn δ := Subgroup.inv_mem _ (hdC c hc)
  set t := ⁅c, g⁆⁻¹ with ht
  have e1 : g * c * g⁻¹ = t * c := by simp only [ht, commutatorElement_def]; group
  have htc : t * c = c * t := Subgroup.mem_centralizer_iff.mp hc.2 t htV
  have ht2 : t * t = 1 := by rw [← pow_two]; exact hVab.2 t htV
  have key : g * (c * c) * g⁻¹ = c * c := by
    calc g * (c * c) * g⁻¹ = g * c * g⁻¹ * (g * c * g⁻¹) := by group
      _ = t * c * (t * c) := by rw [e1]
      _ = t * (c * t) * c := by group
      _ = t * t * (c * c) := by rw [← htc]; group
      _ = c * c := by rw [ht2, one_mul]
  calc g * (c * c) = g * (c * c) * g⁻¹ * g := by group
    _ = c * c * g := by rw [key]

end Sq

theorem sq_mem_Yv_of_centralizes (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α ρ : Geo H M}
    (hs : Sit43 α) (h3 : bMin H M = 3) (hρ : vtype ρ = false)
    (hS : ∀ δ ∈ nbrs ρ, Nat.card (Vn δ) = 2 ^ 6) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) {w : G}
    (hw : w ∈ Wn ρ) (hc : ∀ v ∈ Vn δ, w * v = v * w) : w * w ∈ Yv δ := by
  have hδv : vtype δ = true := Sit43.vtype_true_of_adj hρ hδ
  have hwQ : w ∈ Qv ρ := (hs.of_vtype_false hρ).Wn_le_Qv hA h3.ge hw
  have hwc : w ∈ Subgroup.centralizer (Vn δ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun v hv => (hc v hv).symm
  have hwC : w ∈ Cst δ :=
    ⟨Three.mem_Qv_of_mem_centralizer hA h26 hs hδv (Qv_le_stab_of_mem_nbrs hA hδ hwQ) hwc, hwc⟩
  exact Sq.sq_mem_Yv hA h26 hs h3 hρ hδ (hS δ hδ) hwC
    (Sit43.Zv_le_Vn hδ (sq_Wn_mem_Zv hA h26 hs h3 hρ hS w hw))

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
