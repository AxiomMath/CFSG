module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Zl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChMbl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch2

open S35.Std S35.Fin S35.Ch
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def MblC (δ l : Geo H M) : Subgroup G :=
  Subgroup.normalizer ((Zv l ⊔ Cb δ : Subgroup G) : Set G) ⊓ stab δ

omit [Finite G] in
theorem normalizer_inf_le_sup {A B : Subgroup G} :
    Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine Chart2.le_normalizer_of_forall' fun k hk u hu => ?_
  have h : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj k).toMonoidHom := sup_le
    (fun a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hk.1 a).mp ha))
    (fun b hb => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hk.2 b).mp hb))
  exact h hu

theorem inf_le_Mbl (hS : Sit H M S) {δ l : Geo H M} : stab δ ⊓ stab l ≤ Mbl δ l :=
  le_inf (inf_le_right.trans (stab_le_normalizer_Zv hS.glob.amalg l)) inf_le_left

theorem Qv_le_Mbl (hS : Sit H M S) {δ l : Geo H M} (hl : l ∈ nbrs δ) : Qv δ ≤ Mbl δ l :=
  (Qv_le_inf' hS hl).trans (inf_le_Mbl hS)

theorem vp_inv (p : Fin 5) : IsInvSub orth (ptStab p) (Subgroup.zpowers (vp p)) := by
  intro σ hσ y hy
  rcases (mem_zpowers_iff_of_mul_self (vp_mul_self p)).mp hy with rfl | rfl
  · rw [map_one]; exact Subgroup.one_mem _
  · rw [act_vp, mem_ptStab.mp hσ]; exact Subgroup.mem_zpowers _

namespace Chart2

variable {δ : Geo H M} (c : Chart2 δ)

@[expose] noncomputable def pt (l : Geo H M) : Fin 5 := fixPt (c.Dl l)

theorem isFixPt_pt (hS : Sit H M S) {l : Geo H M} (hl : l ∈ nbrs δ) :
    IsFixPt (c.Dl l) (c.pt l) := isFixPt_fixPt (c.card_Dl hS hl)

include c

omit [Finite G] in
theorem conj_mem_Cb {g : G} (hg : g ∈ stab δ) {x : G} (hx : x ∈ Cb δ) : g * x * g⁻¹ ∈ Cb δ := by
  have hxV : x ∈ Vn δ := c.le hx
  have := c.π_conj ⟨g, hg⟩ ⟨x, hxV⟩
  rw [(c.π_eq_one ⟨x, hxV⟩).mpr hx, map_one] at this
  exact (c.π_eq_one ⟨g * x * g⁻¹, conj_mem_Vn hg hxV⟩).mp this

omit [Finite G] in
theorem stab_le_normalizer_Cb : stab δ ≤ Subgroup.normalizer ((Cb δ : Subgroup G) : Set G) :=
  fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => c.conj_mem_Cb hg hx, fun hx => by
      have := c.conj_mem_Cb ((stab δ).inv_mem hg) hx
      simpa [mul_assoc] using this⟩

omit [Finite G] in
theorem img_sup_Cb {U : Subgroup G} (hUV : U ≤ Vn δ) : c.img (U ⊔ Cb δ) = c.img U := by
  apply le_antisymm
  · have h : U ⊔ Cb δ ≤ c.pre (c.img U) :=
      sup_le ((c.le_pre_iff hUV).mpr le_rfl) (c.Cb_le_pre _)
    calc c.img (U ⊔ Cb δ) ≤ c.img (c.pre (c.img U)) := c.img_mono h
      _ = c.img U := c.img_pre _
  · exact c.img_mono le_sup_left

theorem MblC_eq_preθ (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    MblC δ l = c.preθ (ptStab (c.pt l)) := by
  have hU : Zv l ⊔ Cb δ ≤ Vn δ := sup_le (Zv_le_Vn hl) c.le
  have himg : c.img (Zv l ⊔ Cb δ) = Subgroup.zpowers (vp (c.pt l)) := by
    rw [c.img_sup_Cb (Zv_le_Vn hl)]
    exact c.img_Zv_nbr hS hδ hl
  apply le_antisymm
  · intro g hg
    have hgS : g ∈ stab δ := hg.2
    have hinv := (c.le_normalizer_iff (K := MblC δ l) inf_le_right le_sup_right hU).mp inf_le_left
    rw [himg] at hinv
    have h2 := hinv (c.θ ⟨g, hgS⟩) (c.mem_bar_of_mem hg hgS) (vp (c.pt l)) (Subgroup.mem_zpowers _)
    rw [act_vp] at h2
    refine (c.mem_preθ_iff ⟨g, hgS⟩).mpr (mem_ptStab.mpr ?_)
    rcases (mem_zpowers_iff_of_mul_self (vp_mul_self (c.pt l))).mp h2 with h3 | h3
    · exact absurd h3 (vp_ne_one _)
    · exact vp_injective h3
  · intro g hg
    have hgS : g ∈ stab δ := c.preθ_le_stab _ hg
    refine ⟨?_, hgS⟩
    have : c.preθ (ptStab (c.pt l)) ≤ Subgroup.normalizer ((Zv l ⊔ Cb δ : Subgroup G) : Set G) := by
      refine (c.le_normalizer_iff (c.preθ_le_stab _) le_sup_right hU).mpr ?_
      rw [c.bar_preθ, himg]
      exact vp_inv _
    exact this hg

omit [Finite G] in
theorem Mbl_le_MblC {l : Geo H M} : Mbl δ l ≤ MblC δ l := fun _ hg =>
  ⟨normalizer_inf_le_sup ⟨hg.1, c.stab_le_normalizer_Cb hg.2⟩, hg.2⟩

theorem Mbl_le_preθ (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    Mbl δ l ≤ c.preθ (ptStab (c.pt l)) :=
  c.Mbl_le_MblC.trans (c.MblC_eq_preθ hS hδ hl).le

theorem Mbl_ne_stab (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    Mbl δ l ≠ stab δ := by
  intro h
  have h1 := c.Mbl_le_preθ hS hδ hl
  rw [h] at h1
  apply ptStab_ne_top (c.pt l)
  have := c.bar_mono h1
  rwa [c.bar_preθ, c.bar_stab, top_le_iff] at this

theorem Mbl_eq_preθ_of (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ)
    (hN : c.preθ (ptStab (c.pt l)) ≤ Subgroup.normalizer (Zv l : Set G)) :
    Mbl δ l = c.preθ (ptStab (c.pt l)) :=
  le_antisymm (c.Mbl_le_preθ hS hδ hl) fun _ hg => ⟨hN hg, c.preθ_le_stab _ hg⟩

theorem pt_eq_of_Zv_eq (hS : Sit H M S) (hδ : vtype δ = false) {l l' : Geo H M} (hl : l ∈ nbrs δ)
    (hl' : l' ∈ nbrs δ) (h : Zv l = Zv l') : c.pt l = c.pt l' := by
  have h1 := c.img_Zv_nbr hS hδ hl
  have h2 := c.img_Zv_nbr hS hδ hl'
  rw [h] at h1
  exact zpowers_vp_inj (h1.symm.trans h2)

theorem eq_or_le_preθ_pt (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ)
    {P : Subgroup G} (hP : P ≤ stab δ) (hinf : stab δ ⊓ stab l ≤ P) :
    P = stab δ ∨ P ≤ c.preθ (ptStab (c.pt l)) := by
  by_cases hbar : c.bar P = ⊤
  · left
    have := c.preθ_bar hS hδ hP ((Qv_le_inf' hS hl).trans hinf)
    rw [hbar] at this
    rw [← this]
    ext x
    constructor
    · exact fun hx => c.preθ_le_stab _ hx
    · intro hx
      exact (c.mem_preθ_iff ⟨x, hx⟩).mpr (Subgroup.mem_top _)
  · right
    have hD : c.Dl l ≤ c.bar P := c.bar_mono hinf
    have := le_ptStab_of_le (c.card_Dl hS hl) hD hbar
    rw [← c.preθ_bar hS hδ hP ((Qv_le_inf' hS hl).trans hinf)]
    intro x hx
    have hxs : x ∈ stab δ := c.preθ_le_stab _ hx
    exact (c.mem_preθ_iff ⟨x, hxs⟩).mpr (this ((c.mem_preθ_iff ⟨x, hxs⟩).mp hx))

theorem sameBlock_iff (hS : Sit H M S) (hδ : vtype δ = false) {l l' : Geo H M} (hl : l ∈ nbrs δ)
    (hl' : l' ∈ nbrs δ) : S34.SameBlock δ l l' ↔ c.pt l = c.pt l' := by
  have hsub : ∀ m, m ∈ nbrs δ → stab δ ⊓ stab m ≤ c.preθ (ptStab (c.pt m)) := fun m hm => by
    rw [← c.preθ_Dl hS hδ hm]
    intro g hg
    refine (c.mem_preθ_iff ⟨g, c.preθ_le_stab _ hg⟩).mpr (le_ptStab (c.isFixPt_pt hS hm) ?_)
    exact (c.mem_preθ_iff ⟨g, c.preθ_le_stab _ hg⟩).mp hg
  constructor
  · rintro ⟨P, hQP, hPS, hPne, hlP, hl'P⟩
    have h1 := (c.eq_or_le_preθ_pt hS hδ hl hPS hlP).resolve_left hPne
    have h4 := c.bar_mono (hl'P.trans h1)
    rw [c.bar_preθ] at h4
    have h5 : IsFixPt (c.Dl l') (c.pt l) := fun d hd => mem_ptStab.mp (h4 hd)
    exact IsFixPt.unique (c.card_Dl hS hl') h5 (c.isFixPt_pt hS hl')
  · intro h
    refine ⟨c.preθ (ptStab (c.pt l)), c.Qv_le_preθ hS hδ _, c.preθ_le_stab _, ?_, hsub l hl,
      h ▸ hsub l' hl'⟩
    intro h'
    apply ptStab_ne_top (c.pt l)
    have := congrArg c.bar h'
    rwa [c.bar_preθ, c.bar_stab] at this

theorem exists_nbr_pt (hS : Sit H M S) (hδ : vtype δ = false) (p : Fin 5) :
    ∃ l ∈ nbrs δ, c.pt l = p := by
  have hD : Nat.card (cj (swap 4 p) S5Syl) = 8 := card_cj_S5Syl _
  obtain ⟨l, hl, hlD⟩ := c.Dl_surjOn hS hδ hD
  refine ⟨l, hl, ?_⟩
  have h1 : IsFixPt (c.Dl l) p := by
    rw [hlD]
    exact isFixPt_cj_std_iff.mpr (by simp)
  exact (IsFixPt.unique (c.card_Dl hS hl) (c.isFixPt_pt hS hl) h1)

theorem iInf_Mbl (hS : Sit H M S) (hδ : vtype δ = false) :
    ⨅ l ∈ nbrs δ, Mbl δ l = Qv δ := by
  apply le_antisymm
  · intro g hg
    have hg' : ∀ l ∈ nbrs δ, g ∈ Mbl δ l := fun l hl => (Subgroup.mem_iInf.mp
      ((Subgroup.mem_iInf.mp hg) l)) hl
    obtain ⟨μ, hμ⟩ := exists_adj δ
    have hgS : g ∈ stab δ := (hg' μ hμ).2
    rw [← c.ker_iff hS hδ ⟨g, hgS⟩]
    refine Equiv.ext fun p => ?_
    obtain ⟨l, hl, hlp⟩ := c.exists_nbr_pt hS hδ p
    have h1 := c.Mbl_le_preθ hS hδ hl (hg' l hl)
    rw [c.mem_preθ_iff ⟨g, hgS⟩, mem_ptStab, hlp] at h1
    simpa using h1
  · exact le_iInf₂ fun l hl => Qv_le_Mbl hS hl

end Chart2

end S35.Ch2

end F53.Stellmacher

end CFSG.Quasithin
