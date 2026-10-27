module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseF2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Sit43

variable {α : Geo H M}

theorem Wn_eq_iSup_Vn (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {ρ : Geo H M} (hρ : vtype ρ = false) : Wn ρ = ⨆ (δ : Geo H M) (_ : δ ∈ nbrs ρ), Vn δ := by
  have hs' := hs.of_vtype_false hρ
  apply le_antisymm
  · refine iSup₂_le fun l hl => ?_
    obtain ⟨μ, hμ, hlμ⟩ := exists_common_nbr_of_dist_two (α := ρ) hA hl
    exact le_iSup₂_of_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs ρ) => Vn δ) μ hμ
      (le_iSup₂_of_le (f := fun (m : Geo H M) (_ : m ∈ nbrs μ) => Zv m) l hlμ le_rfl)
  · exact iSup₂_le fun δ hδ => hs'.Vn_le_Wn hA h26 hδ

theorem comm_Vn_inf_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {ρ δ : Geo H M} (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ) :
    ⁅Vn δ, Qv ρ ⊓ Qv δ⁆ ≤ Yv δ := by
  have hδv : vtype δ = true := vtype_true_of_adj hρ hδ
  rw [← hs.comm_Vn_Qst hA h26 hδv (nbrs_symm hδ)]
  exact Subgroup.commutator_mono le_rfl (Qv_inf_Qv_le_Qst hA (nbrs_symm hδ))

theorem comm_Vn_Qv_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {ρ δ : Geo H M} (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ)
    (hD4 : Nat.card (Vn δ) = 2 ^ 6) : ⁅Vn δ, Qv ρ⁆ ≤ Zv ρ :=
  (hs.comm_Qv_le_Zv_iff hA h26 hb (vtype_true_of_adj hρ hδ) (nbrs_symm hδ)).mpr hD4

theorem Vn_le_Qv_of_nbr (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {ρ δ : Geo H M} (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ) :
    Vn δ ≤ Qv ρ := by
  have hs' := hs.of_vtype_false hρ
  exact (hs'.Vn_le_Wn hA h26 hδ).trans (hs'.Wn_le_Qv hA hb)

theorem comm_Wn_Qv_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {ρ δ : Geo H M} (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ)
    (hD4 : Nat.card (Vn δ) = 2 ^ 6) : ⁅Wn ρ, Qv ρ⁆ ≤ Zv ρ := by
  rw [hs.Wn_eq_iSup_Vn hA h26 hρ, iSup_subtype']
  refine commutator_iSup_le (X := stab ρ) (fun i => ?_) (stab_le_normalizer_Zv hA ρ)
    (fun i => ?_)
  · exact (hs.Vn_le_Qv_of_nbr hA h26 hb hρ i.2).trans (pCoreOf_le 2 _)
  · have h4 : Nat.card (Vn i.1) = 2 ^ 6 :=
      (card_Vn_eq (vtype_true_of_adj hρ i.2) (vtype_true_of_adj hρ hδ)).trans hD4
    exact hs.comm_Vn_Qv_le hA h26 hb hρ i.2 h4

omit [Finite G] in
theorem relIndex_Zv_Vn (hs : Sit43 α) {ρ δ : Geo H M} (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ)
    (hD4 : Nat.card (Vn δ) = 2 ^ 6) : (Zv ρ).relIndex (Vn δ) = 4 := by
  have h1 := Subgroup.relIndex_mul_card (Zv ρ) (Vn δ)
  rw [inf_eq_left.mpr (Zv_le_Vn (α := ρ) hδ), hs.card_Zv_false hρ, hD4] at h1
  omega

theorem edge_le_normalizer (hA : F53Amalgam H M S) {ρ δ : Geo H M} :
    stab ρ ⊓ stab δ ≤ Subgroup.normalizer (Vn δ : Set G) ⊓
      Subgroup.normalizer (Zv ρ : Set G) :=
  le_inf (inf_le_right.trans (stab_le_normalizer_Vn δ))
    (inf_le_left.trans (stab_le_normalizer_Zv hA ρ))

theorem faithful (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {ρ δ : Geo H M} (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ)
    (hD4 : Nat.card (Vn δ) = 2 ^ 6) {x : G} (hx : x ∈ stab ρ)
    (hxW : ∀ w ∈ Wn ρ, ⁅w, x⁆ ∈ Zv ρ) : x ∈ Qv ρ := by
  have hs' := hs.of_vtype_false hρ
  obtain ⟨C, hC, hCX, hCn⟩ := exists_centralizer_quotient (X := stab ρ) (N := Wn ρ) (Z := Zv ρ)
    (stab_le_normalizer_Zv hA ρ) (stab_le_normalizer_Wn ρ)
  have hQC : Qv ρ ≤ C := fun q hq => (hC q).mpr ⟨pCoreOf_le 2 _ hq, fun n hn =>
    hs.comm_Wn_Qv_le hA h26 hb hρ hδ hD4 (Subgroup.commutator_mem_commutator hn hq)⟩
  by_contra hxQ
  have hxC : x ∈ C := (hC x).mpr ⟨hx, hxW⟩
  have hCQ : ¬ C ≤ pCoreOf 2 (stab ρ) := fun h => hxQ (h hxC)
  have hT := sylow_stab_inf_left hA hδ
  have hup := sup_sylow_eq_of_normal_not_le (Or.inr rfl) (quot_stab_five hA hρ) hT hCX hCn hCQ
  have hTn : stab ρ ⊓ stab δ ≤ Subgroup.normalizer (C : Set G) := inf_le_left.trans hCn
  have hL : Lres ρ ≤ C := oTwoRes_le_of_cover (X := stab ρ) (C := C) (Q := stab ρ ⊓ stab δ) hCn
    hT.2.1 hT.1 (fun y hy => by
      obtain ⟨c, hc, t, ht, e⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTn).mp (hup hy)
      exact ⟨c, hc, t, ht, e⟩)
  have hVW : Vn δ ≤ Wn ρ := hs'.Vn_le_Wn hA h26 hδ
  have hLV : ∀ l ∈ Lres ρ, ∀ v ∈ Vn δ, l * v * l⁻¹ ∈ Vn δ := by
    intro l hl v hv
    have h1 : ⁅v, l⁆ ∈ Zv ρ := ((hC l).mp (hL hl)).2 v (hVW hv)
    have e : l * v * l⁻¹ = ⁅v, l⁆⁻¹ * v := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Vn δ).mul_mem ((Vn δ).inv_mem (Zv_le_Vn (α := ρ) hδ h1)) hv
  have hTV : ∀ t ∈ stab ρ ⊓ stab δ, ∀ v ∈ Vn δ, t * v * t⁻¹ ∈ Vn δ := fun t ht v hv =>
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ ht.2) v).mp hv
  have hρV : stab ρ ≤ Subgroup.normalizer (Vn δ : Set G) := by
    refine le_normalizer_of_conj_mem fun y hy v hv => ?_
    have hTL : stab ρ ⊓ stab δ ≤ Subgroup.normalizer (Lres ρ : Set G) :=
      inf_le_left.trans (le_normalizer_oTwoRes (stab ρ))
    obtain ⟨a, ha, t, ht, e⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTL).mp
      (le_oTwoRes_sup_of_isSylowTwoOf hT hy)
    have : y * v * y⁻¹ = a * (t * v * t⁻¹) * a⁻¹ := by rw [e]; group
    rw [this]
    exact hLV a ha _ (hTV t ht v hv)
  have hU : Vn δ ≤ stab ρ ⊓ stab δ := le_inf
    ((hs.Vn_le_Qv_of_nbr hA h26 hb hρ hδ).trans (pCoreOf_le 2 _))
    ((Vn_le_Qv hs' hδ).trans (pCoreOf_le 2 _))
  have hbot := eq_bot_of_normalizes_both hA (show (graph (H ⊔ M) H M).Adj ρ δ from hδ) hU hρV
    (stab_le_normalizer_Vn δ)
  exact Zv_ne_bot hA ρ (le_bot_iff.mp (hbot ▸ Zv_le_Vn (α := ρ) hδ))

theorem Wn_eq_iSup_conj (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {ρ δ : Geo H M} (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ) :
    Wn ρ = ⨆ (g : G) (_ : g ∈ stab ρ), conjSub g (Vn δ) := by
  rw [hs.Wn_eq_iSup_Vn hA h26 hρ]
  apply le_antisymm
  · refine iSup₂_le fun δ' hδ' => ?_
    obtain ⟨g, hg, hgδ⟩ := stab_transitive_on_nbrs hδ hδ'
    have e : conjSub (g : G) (Vn δ) = Vn δ' := by rw [← hgδ, Vn_smul]
    exact le_iSup₂_of_le (f := fun (x : G) (_ : x ∈ stab ρ) => conjSub x (Vn δ)) (g : G) hg
      e.ge
  · refine iSup₂_le fun g hg => ?_
    have hgδ : (⟨g, stab_le ρ hg⟩ : ↥(H ⊔ M)) • δ ∈ nbrs ρ := by
      have := (smul_mem_nbrs_iff (⟨g, stab_le ρ hg⟩ : ↥(H ⊔ M)) (l := ρ) (δ := δ)).mpr hδ
      rwa [smul_eq_of_mem_stab
        (show ((⟨g, stab_le ρ hg⟩ : ↥(H ⊔ M)) : G) ∈ stab ρ from hg)] at this
    have e : conjSub g (Vn δ) = Vn ((⟨g, stab_le ρ hg⟩ : ↥(H ⊔ M)) • δ) :=
      (Vn_smul (⟨g, stab_le ρ hg⟩ : ↥(H ⊔ M)) δ).symm
    rw [e]
    exact le_iSup₂_of_le (f := fun (m : Geo H M) (_ : m ∈ nbrs ρ) => Vn m) _ hgδ le_rfl

end Sit43

end F53.Stellmacher.S43

end CFSG.Quasithin
