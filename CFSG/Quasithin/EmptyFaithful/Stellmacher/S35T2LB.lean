module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T2LA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T2L

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem relIndex_swap_of_card_eq {A B : Subgroup G} (h : Nat.card A = Nat.card B) :
    A.relIndex B = B.relIndex A := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := B)
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_comm] at h2
  have hpos : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
  rw [h, ← h1] at h2
  exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm

theorem Wl_le_Wb (hS : Sit H M S) {β l : Geo H M} (hβ : vtype β = false) (hl : l ∈ nbrs β) :
    Wl l ≤ Wb β := by
  rw [Wb_eq_iSup_Wl hS hβ]
  exact le_iSup₂_of_le (f := fun (l : Geo H M) (_ : l ∈ nbrs β) => Wl l) l hl le_rfl

theorem Wl_le_Qv (hS : Sit H M S) {l : Geo H M} : Wl l ≤ Qv l :=
  Wl_le fun ρ hρ => Vn_le_Qv_dist hS (by
    have : dist ρ l = 1 := by rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hρ
    have := hS.b5
    omega)

theorem not_le_conj (hS : Sit H M S) (I : Inputs H M) {β l : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) {y : G} (hy : y ∈ stab β) (hmov : y ∉ Subgroup.normalizer (Zv l : Set G))
    (hle : Wl l ≤ conjSub y (Wl l)) : False := by
  have heq : conjSub y (Wl l) = Wl l := by
    refine (Subgroup.eq_of_le_of_card_ge (H := Wl l) (K := conjSub y (Wl l)) hle ?_).symm
    exact (Subgroup.card_map_of_injective (MulAut.conj y).injective).le
  have hinv : conjSub y⁻¹ (Wl l) = Wl l :=
    calc conjSub y⁻¹ (Wl l) = conjSub y⁻¹ (conjSub y (Wl l)) := by rw [heq]
      _ = Wl l := conjSub_conjSub_inv y _
  have hyN : y ∈ Subgroup.normalizer ((Wl l : Subgroup G) : Set G) :=
    F7.mem_normalizer_of_conj_le heq.le hinv.le
  rcases I.maximal β l hβ hl (stab β ⊓ Subgroup.normalizer ((Wl l : Subgroup G) : Set G))
      inf_le_left (fun g hg => ⟨hg.1, Wl_normal l hg.2⟩) with hP | hP
  · have hβN : stab β ≤ Subgroup.normalizer ((Wl l : Subgroup G) : Set G) := fun g hg => by
      have : g ∈ stab β ⊓ Subgroup.normalizer ((Wl l : Subgroup G) : Set G) := by rw [hP]; exact hg
      exact this.2
    have hβl : β ∈ nbrs l := mem_nbrs_symm.mpr hl
    have hU : Wl l ≤ stab β ⊓ stab l :=
      le_inf ((Wl_le_Qv hS).trans (Qv_le_stab hS hβl)) ((Wl_le_Qv hS).trans (pCoreOf_le 2 _))
    have hbot := F53.eq_bot_of_normalizes_both hS.glob.amalg
      (show (graph (H ⊔ M) H M).Adj β l from hl) hU hβN (Wl_normal l)
    have hV : Vn β = ⊥ := le_bot_iff.mp (hbot ▸ Vn_le_Wl hβl)
    exact Zv_ne_bot hS.glob.amalg β (le_bot_iff.mp (hV ▸ Zv_le_Vn_S5 hS hβ))
  · exact hmov (hP ⟨hy, hyN⟩)

theorem commonHyp_of_link_aux (hS : Sit H M S) (hN : S35.II.NbarFull H M) (I : Inputs H M)
    {β l : Geo H M} (hβ : vtype β = false) (hl : l ∈ nbrs β) {y : G} (hy : y ∈ stab β)
    (hmov : y ∉ Subgroup.normalizer (Zv l : Set G))
    (hlink : (Wl l ⊓ conjSub y (Wl l)).relIndex (Wl l) = 2) :
    S35.II.CommonHyp β (Wl l ⊓ conjSub y (Wl l)) := by
  set Y₀ : Subgroup G := Wl l ⊓ conjSub y (Wl l) with hY₀
  have hβl : β ∈ nbrs l := mem_nbrs_symm.mpr hl
  have hyG : y ∈ H ⊔ M := stab_le β hy
  set g₀ : ↥(H ⊔ M) := ⟨y, hyG⟩ with hg₀
  have hyV : conjSub y (Vn β) = Vn β := conjSub_eq_of_mem_normalizer (Vn_normal β hy)
  have hyQ : conjSub y (Qv β) = Qv β :=
    conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 (stab β) hy)
  have hV₀ : Vn β ≤ Y₀ := le_inf (Vn_le_Wl hβl) (by rw [← hyV]; exact conjSub_mono _ (Vn_le_Wl hβl))
  have hH0 : HypAt β l Y₀ := by
    refine ⟨hV₀, inf_le_left, hlink, ?_⟩
    refine F7.le_normalizer_inf ((Qv_le_stab hS hl).trans (Wl_normal l)) ?_
    rw [conjSub_normalizer, ← hyQ]
    exact conjSub_mono _ ((Qv_le_stab hS hl).trans (Wl_normal l))
  have hH1 : HypAt β (g₀ • l) Y₀ := by
    have hW : Wl (g₀ • l) = conjSub y (Wl l) := Wl_smul g₀ l
    have hcard : Nat.card (conjSub y (Wl l)) = Nat.card (Wl l) :=
      Subgroup.card_map_of_injective (MulAut.conj y).injective
    refine ⟨hV₀, hW ▸ inf_le_right, ?_, ?_⟩
    · rw [hW, hY₀, Subgroup.inf_relIndex_right, relIndex_swap_of_card_eq hcard.symm,
        ← Subgroup.inf_relIndex_left (Wl l) (conjSub y (Wl l))]
      exact hlink
    · exact hH0.2.2.2
  have hnb : ∀ g : ↥(H ⊔ M), (g : G) ∈ stab β → g • l ∈ nbrs β := fun g hg =>
    smul_mem_nbrs_of_stab hg hl
  have hconj : ∀ g : ↥(H ⊔ M), (g : G) ∈ stab β → HypAt β (g • l) Y₀ →
      conjSub (g : G) Y₀ = Y₀ := fun g hg hgY =>
    hyp_unique hS hN I hβ (hnb g hg) (hyp_smul hH0 g hg) hgY
  let Sg : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ stab β, HypAt β ((⟨g, stab_le β hg⟩ : ↥(H ⊔ M)) • l) Y₀}
      one_mem' := ⟨(stab β).one_mem, by
        have : (⟨1, stab_le β (stab β).one_mem⟩ : ↥(H ⊔ M)) • l = l := one_smul _ l
        rw [this]; exact hH0⟩
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨hga, ha⟩ := ha
        obtain ⟨hgb, hb⟩ := hb
        refine ⟨(stab β).mul_mem hga hgb, ?_⟩
        have h1 := hyp_smul hb ⟨a, stab_le β hga⟩ hga
        rw [hconj ⟨a, stab_le β hga⟩ hga ha] at h1
        have e : (⟨a * b, stab_le β ((stab β).mul_mem hga hgb)⟩ : ↥(H ⊔ M)) =
            ⟨a, stab_le β hga⟩ * ⟨b, stab_le β hgb⟩ := rfl
        rw [e, mul_smul]
        exact h1
      inv_mem' := fun {a} ha => by
        obtain ⟨hga, ha⟩ := ha
        have hga' : a⁻¹ ∈ stab β := (stab β).inv_mem hga
        refine ⟨hga', ?_⟩
        have h1 := hyp_smul hH0 ⟨a⁻¹, stab_le β hga'⟩ hga'
        have hc := hconj ⟨a, stab_le β hga⟩ hga ha
        have h2 : conjSub a⁻¹ Y₀ = Y₀ :=
          calc conjSub a⁻¹ Y₀ = conjSub a⁻¹ (conjSub a Y₀) := by rw [hc]
            _ = Y₀ := conjSub_conjSub_inv a _
        rw [h2] at h1
        exact h1 }
  have hle1 : Sg ≤ stab β := fun g hg => hg.1
  have hle2 : stab β ⊓ stab l ≤ Sg := fun g hg => by
    refine ⟨hg.1, ?_⟩
    have : (⟨g, stab_le β hg.1⟩ : ↥(H ⊔ M)) • l = l := smul_eq_of_mem_stab hg.2
    rw [this]; exact hH0
  have hyS : y ∈ Sg := ⟨hy, hH1⟩
  have hSg : Sg = stab β := by
    rcases I.maximal β l hβ hl Sg hle1 hle2 with h | h
    · exact h
    · exact absurd (h hyS) hmov
  have hall : ∀ g ∈ stab β, ∃ hg : g ∈ stab β,
      HypAt β ((⟨g, stab_le β hg⟩ : ↥(H ⊔ M)) • l) Y₀ := fun g hg => by
    have : g ∈ Sg := by rw [hSg]; exact hg
    exact this
  have hc : ∀ g ∈ stab β, conjSub g Y₀ = Y₀ := fun g hg => by
    obtain ⟨hg', hgY⟩ := hall g hg
    exact hconj ⟨g, stab_le β hg⟩ hg hgY
  refine ⟨fun g hg => F7.mem_normalizer_of_conj_le (hc g hg).le (hc g⁻¹ ((stab β).inv_mem hg)).le,
    hV₀, inf_le_left.trans (Wl_le_Wb hS hβ hl), fun l' hl' => ?_⟩
  obtain ⟨g, hgs, hgl⟩ := stab_transitive_on_nbrs hl hl'
  obtain ⟨hgs', hgY⟩ := hall g hgs
  have e : (⟨(g : G), stab_le β hgs'⟩ : ↥(H ⊔ M)) = g := rfl
  rw [e, hgl] at hgY
  exact ⟨hgY.2.1, hgY.2.2.1, fun δ hδ hne => Vn_not_le_of_hyp hS hβ hl' hgY hδ hne⟩

end S35.T2L

end F53.Stellmacher

end CFSG.Quasithin
