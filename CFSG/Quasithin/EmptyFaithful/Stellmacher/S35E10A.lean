module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.E10

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem Wl_smul (g : ↥(H ⊔ M)) (l : Geo H M) : Wl (g • l) = conjSub (g : G) (Wl l) := by
  unfold Wl
  apply le_antisymm
  · refine iSup₂_le fun δ hδ => ?_
    obtain ⟨δ', rfl⟩ : ∃ δ', δ = g • δ' := ⟨g⁻¹ • δ, by simp⟩
    have hδ' : δ' ∈ nbrs l := (Std.smul_mem_nbrs_iff' g).mp hδ
    rw [Vn_smul]
    exact conjSub_mono _ (le_iSup₂_of_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs l) => Vn δ)
      δ' hδ' le_rfl)
  · rw [conjSub_le_iff]
    refine iSup₂_le fun δ hδ => ?_
    rw [← conjSub_le_iff, ← Vn_smul]
    exact le_iSup₂_of_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs (g • l)) => Vn δ)
      (g • δ) ((Std.smul_mem_nbrs_iff' g).mpr hδ) le_rfl

theorem Wl_le_Wb (hS : Sit H M S) {β l : Geo H M} (hβ : vtype β = false) (hl : l ∈ nbrs β) :
    Wl l ≤ Wb β := by
  rw [Std.Wb_eq_iSup_Wl hS hβ]
  exact le_iSup₂_of_le (f := fun (l : Geo H M) (_ : l ∈ nbrs β) => Wl l) l hl le_rfl

@[expose] def Cen (β : Geo H M) : Subgroup G where
  carrier := {g | g ∈ stab β ∧ ∀ w ∈ Wb β, g * w * g⁻¹ * w⁻¹ ∈ Vn β}
  one_mem' := ⟨one_mem _, fun w _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨mul_mem ha hb, fun w hw => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (Std.Vn_normal β ha) _).mp (hcb w hw)
    have h2 := mul_mem h1 (hca w hw)
    convert h2 using 1
    group
  inv_mem' := by
    rintro a ⟨ha, hca⟩
    refine ⟨inv_mem ha, fun w hw => ?_⟩
    have hw' : a⁻¹ * w * a ∈ Wb β := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Std.Wb_normal β (inv_mem ha)) _).mp hw
    have h := inv_mem (hca _ hw')
    convert h using 1
    group

omit [Finite G] in
theorem Cen_normal (β : Geo H M) : stab β ≤ Subgroup.normalizer (Cen β : Set G) := by
  have key : ∀ s ∈ stab β, ∀ c ∈ Cen β, s * c * s⁻¹ ∈ Cen β := by
    rintro s hs c ⟨hc, hcw⟩
    refine ⟨mul_mem (mul_mem hs hc) (inv_mem hs), fun w hw => ?_⟩
    have hw' : s⁻¹ * w * s ∈ Wb β := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Std.Wb_normal β (inv_mem hs)) _).mp hw
    have h := (Subgroup.mem_normalizer_iff.mp (Std.Vn_normal β hs) _).mp (hcw _ hw')
    convert h using 1
    group
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key s hs c hc, fun hc => ?_⟩
  have := key s⁻¹ (inv_mem hs) _ hc
  simpa [mul_assoc] using this

theorem conjSub_Wl_eq (hS : Sit H M S) {β l : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) {c : G} (hc : c ∈ Cen β) : conjSub c (Wl l) = Wl l := by
  have key : ∀ d ∈ Cen β, conjSub d (Wl l) ≤ Wl l := by
    intro d hd x hx
    have hx' : d * (d⁻¹ * x * d) * d⁻¹ ∈ conjSub d (Wl l) := by simpa [mul_assoc] using hx
    have hy : d⁻¹ * x * d ∈ Wl l := conj_mem_conjSub_iff.mp hx'
    have h1 : d * (d⁻¹ * x * d) * d⁻¹ * (d⁻¹ * x * d)⁻¹ ∈ Vn β :=
      hd.2 _ (Wl_le_Wb hS hβ hl hy)
    have h2 := mul_mem (Std.Vn_le_Wl (Std.mem_nbrs_symm.mp hl) h1) hy
    convert h2 using 1
    group
  refine le_antisymm (key c hc) ?_
  rw [le_conjSub_iff]
  exact key c⁻¹ (inv_mem hc)

theorem Wl_eq_of_smul (hS : Sit H M S) {β l l' : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) {c : ↥(H ⊔ M)} (hc : (c : G) ∈ Cen β) (hcl : c • l = l') :
    Wl l' = Wl l := by
  rw [← hcl, Wl_smul, conjSub_Wl_eq hS hβ hl hc]

theorem not_centralizes_Wb (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false) {x : G}
    (hx : x ∈ stab β) (hxQ : x ∉ Qv β)
    (hc : ∀ w ∈ Wb β, x * w * x⁻¹ * w⁻¹ ∈ Vn β) : False := by
  obtain ⟨l₀, hl₀⟩ := exists_adj β
  have hl₀ : l₀ ∈ nbrs β := hl₀
  have htr : ∀ {l : Geo H M}, l ∈ nbrs β → ∃ c : ↥(H ⊔ M), (c : G) ∈ Cen β ∧ c • l₀ = l := by
    intro l hl
    exact exists_smul_eq_of_normal_not_le hS.glob.amalg hl₀ hl
      (fun g hg => hg.1) (Cen_normal β) fun h => hxQ (h ⟨hx, hc⟩)
  have hY : ∀ {l : Geo H M}, l ∈ nbrs β → Wl l = Wl l₀ := by
    intro l hl
    obtain ⟨c, hcC, hcl⟩ := htr hl
    exact Wl_eq_of_smul hS hβ hl₀ hcC hcl
  have hQβ : Wl l₀ ≤ stab β ⊓ stab l₀ := by
    refine le_inf ?_ ?_
    · exact (Wl_le_Wb hS hβ hl₀).trans ((Std.Wb_le_Qv hS β).trans
        fun y hy => ((Std.mem_Qv_iff hS β).mp hy).1)
    · exact (Wl_le_Wb hS hβ hl₀).trans ((Std.Wb_le_Ql hS hl₀).trans
        fun y hy => ((Std.mem_Qv_iff hS l₀).mp hy).1)
  have hnβ : stab β ≤ Subgroup.normalizer (Wl l₀ : Set G) := by
    intro g hg
    have hmem := stab_le β hg
    have hn : (⟨g, hmem⟩ : ↥(H ⊔ M)) • l₀ ∈ nbrs β :=
      Std.smul_mem_nbrs_of_stab (g := ⟨g, hmem⟩) hg hl₀
    refine mem_normalizer_of_conjSub_eq ?_
    rw [← Wl_smul (⟨g, hmem⟩ : ↥(H ⊔ M)) l₀]
    exact hY hn
  have hbot : Wl l₀ = ⊥ :=
    eq_bot_of_normalizes_both hS.glob.amalg (show (graph (H ⊔ M) H M).Adj β l₀ from hl₀)
      hQβ hnβ (Std.Wl_normal l₀)
  have hZ : Zv β ≤ Wl l₀ :=
    (Std.Zv_le_Vn_S5 hS hβ).trans (Std.Vn_le_Wl (Std.mem_nbrs_symm.mp hl₀))
  rw [hbot, le_bot_iff] at hZ
  exact Zv_ne_bot hS.glob.amalg β hZ

end S35.E10

end F53.Stellmacher

end CFSG.Quasithin
