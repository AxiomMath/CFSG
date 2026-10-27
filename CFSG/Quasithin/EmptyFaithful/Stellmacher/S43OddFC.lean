module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddFB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem comm_Wn_Qv_le_Cmax (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 4 ≤ bMin H M) (h : AtMostOneNoncentral α) : ⁅Wn α, Qv α⁆ ≤ Cmax α := by
  have hW := hs.w17Hyp hA h26 hb
  have hZW := hs.Zv_le_Wn hA h26
  obtain ⟨β, hβ⟩ := hs.exists_adj hA
  have hβ' : β ∈ nbrs α := hβ
  obtain ⟨B, hBW, -, hLB, hQB⟩ := F.exists_central_cut hA hW hZW h
  have hXC := stab_le_normalizer_Cmax hA hW hZW
  have hZC := Zv_le_Cmax hA hZW
  have hWX : Wn α ≤ stab α := hW.Wn_le_stab
  have hQX : Qv α ≤ stab α := pCoreOf_le 2 _
  have hWBV : Wn α ≤ B ⊔ Vn β := by
    rw [hs.Wn_eq_iSup_conj hA h26 hs.vα hβ']
    refine iSup₂_le fun g hg v hv => ?_
    obtain ⟨l, hl, t, ht, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      (inf_le_left.trans (le_normalizer_oTwoRes (stab α)))).mp
      (le_oTwoRes_sup_of_isSylowTwoOf (sylow_stab_inf_left hA hβ') hg)
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ Vn β, v = l * u * l⁻¹ :=
      ⟨t * ((l * t)⁻¹ * v * (l * t)) * t⁻¹,
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β ht.2) _).mp (mem_conjSub.mp hv),
        by group⟩
    have e : l * u * l⁻¹ = (l * u * l⁻¹ * u⁻¹) * u := by group
    rw [e]
    exact Subgroup.mul_mem_sup (hLB l hl u (hs.Vn_le_Wn hA h26 hβ' hu)) hu
  set K := cSecIn (stab α) (Cmax α) (Wn α) with hK
  have hmemK : ∀ x, x ∈ K ↔ x ∈ stab α ∧ ∀ w ∈ Wn α, x * w * x⁻¹ * w⁻¹ ∈ Cmax α :=
    fun x => mem_cSecIn_iff hXC
  have hKn : ∀ x ∈ stab α, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk
    obtain ⟨hkX, hkW⟩ := (hmemK k).mp hk
    refine (hmemK _).mpr
      ⟨(stab α).mul_mem ((stab α).mul_mem hx hkX) ((stab α).inv_mem hx), fun w hw => ?_⟩
    have hw' : x⁻¹ * w * x ∈ Wn α := by
      have := (Subgroup.mem_normalizer_iff.mp (hW.stab_le_normalizer ((stab α).inv_mem hx)) w).mp
        hw
      rwa [inv_inv] at this
    have e : x * k * x⁻¹ * w * (x * k * x⁻¹)⁻¹ * w⁻¹ =
        x * (k * (x⁻¹ * w * x) * k⁻¹ * (x⁻¹ * w * x)⁻¹) * x⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hXC hx) _).mp (hkW _ hw')
  have hK0 : Qv α ⊓ Qv β ≤ K := by
    intro q hq
    refine (hmemK q).mpr ⟨hQX hq.1, fun w hw => ?_⟩
    have hle : B ⊔ Vn β ≤ fixer (Cmax α) q := by
      refine sup_le (fun y hy => mem_fixer_iff.mpr ⟨hXC (hWX (hBW hy)), ?_⟩)
        (fun v hv => mem_fixer_iff.mpr ⟨hXC (hWX (hs.Vn_le_Wn hA h26 hβ' hv)), ?_⟩)
      · have h1 := (Cmax α).inv_mem (hQB q hq.1 y hy)
        have e : (q * y * q⁻¹ * y⁻¹)⁻¹ = y * q * y⁻¹ * q⁻¹ := by group
        rwa [e] at h1
      · have h1 : ⁅v, q⁆ ∈ Yv β :=
          hs.comm_Vn_inf_le hA h26 hs.vα hβ' (Subgroup.commutator_mem_commutator hv hq)
        rw [commutatorElement_def] at h1
        exact hZC (Yv_le_Zv (nbrs_symm hβ') h1)
    have h1 := (Cmax α).inv_mem (mem_fixer_iff.mp (hle (hWBV hw))).2
    have e : (w * q * w⁻¹ * q⁻¹)⁻¹ = q * w * q⁻¹ * w⁻¹ := by group
    rwa [e] at h1
  have hQK : Qv α ≤ K := by
    by_contra hcon
    obtain ⟨q, hq, hqK⟩ := IsConcreteLE.not_le_iff_exists.mp hcon
    have h2 := hs.relIndex_Qv_Qv hA h26 hs.vα hβ'
    have hqβ : q ∉ Qv β := fun h' => hqK (hK0 ⟨hq, h'⟩)
    have hconj : ∀ x ∈ stab α, q⁻¹ * (x * q * x⁻¹) ∈ K := by
      intro x hx
      have hxq : x * q * x⁻¹ ∈ Qv α :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab α) hx) q).mp hq
      have hxqK : x * q * x⁻¹ ∉ K := by
        intro h'
        have h3 := hKn x⁻¹ ((stab α).inv_mem hx) _ h'
        have e : x⁻¹ * (x * q * x⁻¹) * x⁻¹⁻¹ = q := by group
        rw [e] at h3
        exact hqK h3
      have hxqβ : x * q * x⁻¹ ∉ Qv β := fun h' => hxqK (hK0 ⟨hxq, h'⟩)
      exact hK0 ⟨(Qv α).mul_mem ((Qv α).inv_mem hq) hxq,
        inv_mul_mem_of_relIndex_two h2 hq hxq hqβ hxqβ⟩
    apply hqK
    refine (hmemK q).mpr ⟨hQX hq, fun w hw => ?_⟩
    have hqW : q * w * q⁻¹ * w⁻¹ ∈ Wn α :=
      (Wn α).mul_mem ((Subgroup.mem_normalizer_iff.mp (hW.stab_le_normalizer (hQX hq)) w).mp hw)
        ((Wn α).inv_mem hw)
    refine mem_Cmax_of_forall hA hW hZW hqW fun l hl => ?_
    have hk := hconj l (oTwoRes_le (stab α) hl)
    have hb := hLB l hl w hw
    have hbW := hBW hb
    have hc₁ := ((hmemK _).mp hk).2 _ ((Wn α).mul_mem hbW hw)
    have hc₂ := (Subgroup.mem_normalizer_iff.mp (hXC (hQX hq)) _).mp hc₁
    have hc₃ := hQB q hq _ hb
    have hc₄ := hZC (hW.comm_le (Subgroup.commutator_mem_commutator hbW hqW))
    rw [commutatorElement_def] at hc₄
    have e : l * (q * w * q⁻¹ * w⁻¹) * l⁻¹ * (q * w * q⁻¹ * w⁻¹)⁻¹ =
        q * (q⁻¹ * (l * q * l⁻¹) * (l * w * l⁻¹ * w⁻¹ * w) * (q⁻¹ * (l * q * l⁻¹))⁻¹ *
          (l * w * l⁻¹ * w⁻¹ * w)⁻¹) * q⁻¹ *
        (q * (l * w * l⁻¹ * w⁻¹) * q⁻¹ * (l * w * l⁻¹ * w⁻¹)⁻¹) *
        ((l * w * l⁻¹ * w⁻¹) * (q * w * q⁻¹ * w⁻¹) * (l * w * l⁻¹ * w⁻¹)⁻¹ *
          (q * w * q⁻¹ * w⁻¹)⁻¹) := by group
    rw [e]
    exact (Cmax α).mul_mem ((Cmax α).mul_mem hc₂ hc₃) hc₄
  rw [Subgroup.commutator_le]
  intro w hw q hq
  have h1 := (Cmax α).inv_mem (((hmemK q).mp (hQK hq)).2 w hw)
  have e : (q * w * q⁻¹ * w⁻¹)⁻¹ = ⁅w, q⁆ := by rw [commutatorElement_def]; group
  rwa [e] at h1

theorem comm_Vn_Qv_le_Zv_of_atMostOne (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (hb : 4 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α)
    (h : AtMostOneNoncentral α) : ⁅Vn β, Qv α⁆ ≤ Zv α := by
  have hW := hs.w17Hyp hA h26 hb
  have hZW := hs.Zv_le_Wn hA h26
  have h1 : ⁅Vn β, Qv α⁆ ≤ Vn β := F.commutator_le_left_of_le_normalizer
    ((Qv_le_stab_of_mem_nbrs hA hβ).trans (stab_le_normalizer_Vn β))
  have h2 : ⁅Vn β, Qv α⁆ ≤ Cmax α :=
    (Subgroup.commutator_mono (hs.Vn_le_Wn hA h26 hβ) le_rfl).trans
      (comm_Wn_Qv_le_Cmax hA h26 hs hb h)
  rw [← hs.S13' hA h26 (stab_le_normalizer_Cmax hA hW hZW) (Zv_le_Cmax hA hZW)
    (comm_Cmax_le hA hW hZW) hβ]
  exact le_inf h1 h2

theorem card_Vn_eq_of_atMostOne (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 4 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : AtMostOneNoncentral α) :
    Nat.card (Vn β) = 2 ^ 6 :=
  (hs.comm_Qv_le_Zv_iff hA h26 (by omega) (Sit43.vtype_true_of_adj hs.vα hβ)
    (nbrs_symm hβ)).mp (comm_Vn_Qv_le_Zv_of_atMostOne hA h26 hs hb hβ h)

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
