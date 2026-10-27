module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35TB4Grp
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Mbl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.TB4

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem pt_smul (hS : Sit H M S) {γ : Geo H M} (c : S35.Ch2.Chart2 γ) {g : ↥(H ⊔ M)}
    (hg : (g : G) ∈ stab γ) {l : Geo H M} (hl : l ∈ nbrs γ) :
    c.pt (g • l) = c.θ ⟨g, hg⟩ (c.pt l) := by
  unfold S35.Ch2.Chart2.pt
  rw [c.Dl_smul hg l]
  apply fixPt_eq (by rw [card_cj]; exact c.card_Dl hS hl)
  rw [isFixPt_cj_iff]
  simpa using isFixPt_fixPt (c.card_Dl hS hl)

theorem Qv_inf_eq_all (hS : Sit H M S) (hZB : S35.II.ZvBlock H M) {γ : Geo H M}
    (c : S35.Ch2.Chart2 γ) (hγ : vtype γ = false) {a b : Geo H M} (ha : a ∈ nbrs γ)
    (hb : b ∈ nbrs γ) (hpt : c.pt a ≠ c.pt b) (heq : Qv γ ⊓ Qv a = Qv γ ⊓ Qv b) :
    ∀ l ∈ nbrs γ, Qv γ ⊓ Qv l = Qv γ ⊓ Qv a := by
  intro l hl
  have blk : ∀ x ∈ nbrs γ, ∀ y ∈ nbrs γ, c.pt x = c.pt y →
      Qv γ ⊓ Qv x = Qv γ ⊓ Qv y := fun x hx y hy h =>
    Qv_inf_Qv_eq_of_Zv_eq hS hγ hx hy
      ((hZB γ x y hγ hx hy).mpr ((c.sameBlock_iff hS hγ hx hy).mpr h))
  by_cases h1 : c.pt l = c.pt a
  · exact blk l hl a ha h1
  by_cases h2 : c.pt l = c.pt b
  · exact (blk l hl b hb h2).trans heq.symm
  obtain ⟨x, hx⟩ := c.surj (Equiv.swap (c.pt b) (c.pt l))
  have hg : ((⟨(x : G), stab_le γ x.2⟩ : ↥(H ⊔ M)) : G) ∈ stab γ := x.2
  set g : ↥(H ⊔ M) := ⟨(x : G), stab_le γ x.2⟩ with hgdef
  have hga : g • a ∈ nbrs γ := smul_mem_nbrs_of_stab hg ha
  have hgb : g • b ∈ nbrs γ := smul_mem_nbrs_of_stab hg hb
  have hxx : (⟨(g : G), hg⟩ : ↥(stab γ)) = x := rfl
  have pa : c.pt (g • a) = c.pt a := by
    rw [pt_smul hS c hg ha, hxx, hx]
    exact Equiv.swap_apply_of_ne_of_ne hpt (Ne.symm h1)
  have pb : c.pt (g • b) = c.pt l := by
    rw [pt_smul hS c hg hb, hxx, hx]
    exact Equiv.swap_apply_left _ _
  have e1 := conjSub_Qv_inf (l := a) hg
  have e2 := conjSub_Qv_inf (l := b) hg
  rw [heq, e2] at e1
  exact (blk l hl (g • b) hgb pb.symm).trans (e1.trans (blk (g • a) hga a ha pa))

theorem Qv_inf_sup_eq (hS : Sit H M S) (hZB : S35.II.ZvBlock H M)
    (h6 : S35.II.ClaimS6 H M) {γ a b : Geo H M}
    (hγ : vtype γ = false) (ha : a ∈ nbrs γ) (hb : b ∈ nbrs γ) (hnb : ¬ S34.SameBlock γ a b) :
    (Qv γ ⊓ Qv a) ⊔ (Qv γ ⊓ Qv b) = Qv γ := by
  obtain ⟨c⟩ := S35.Ch2.exists_chart2 hS hγ
  have hpt : c.pt a ≠ c.pt b := fun h => hnb ((c.sameBlock_iff hS hγ ha hb).mpr h)
  have hia := relIndex_Qv hS hγ ha
  have hib := relIndex_Qv hS hγ hb
  have hne : Qv γ ⊓ Qv a ≠ Qv γ ⊓ Qv b := by
    intro heq
    have hall := Qv_inf_eq_all hS hZB c hγ ha hb hpt heq
    have hle : Qv γ ⊓ Qv a ≤ S35.Kb γ := by
      intro q hq
      refine ⟨hq.1, ?_⟩
      have hV : Vn γ ≤ Subgroup.centralizer ({q} : Set G) := by
        unfold Vn
        refine iSup₂_le fun μ hμ z hz => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have : h ∈ Qv μ := ((hall μ hμ) ▸ hq : h ∈ Qv γ ⊓ Qv μ).2
        exact Qv_comm_Zv hS this hz
      show q ∈ Subgroup.centralizer (Vn γ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact ((Subgroup.mem_centralizer_iff.mp (hV hh)) q rfl).symm
    have h2 := Subgroup.relIndex_le_of_le_left hle (by rw [hia]; norm_num)
    have h4 := h6 γ hγ
    omega
  by_contra hne'
  have hle1 : Qv γ ⊓ Qv a ≤ (Qv γ ⊓ Qv a) ⊔ (Qv γ ⊓ Qv b) := le_sup_left
  have hle2 : (Qv γ ⊓ Qv a) ⊔ (Qv γ ⊓ Qv b) ≤ Qv γ := sup_le inf_le_left inf_le_left
  have hm := Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  have hlt : ((Qv γ ⊓ Qv a) ⊔ (Qv γ ⊓ Qv b)).relIndex (Qv γ) ≠ 1 := fun h =>
    hne' (le_antisymm hle2 (Subgroup.relIndex_eq_one.mp h))
  have hpos : ((Qv γ ⊓ Qv a) ⊔ (Qv γ ⊓ Qv b)).relIndex (Qv γ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero, hia] at hm
    omega
  have hone : (Qv γ ⊓ Qv a).relIndex ((Qv γ ⊓ Qv a) ⊔ (Qv γ ⊓ Qv b)) = 1 := by
    rw [hia] at hm
    have : ((Qv γ ⊓ Qv a) ⊔ (Qv γ ⊓ Qv b)).relIndex (Qv γ) = 2 := by
      have hd : ((Qv γ ⊓ Qv a) ⊔ (Qv γ ⊓ Qv b)).relIndex (Qv γ) ∣ 2 := Dvd.intro_left _ hm
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    rw [this] at hm
    omega
  have hba : Qv γ ⊓ Qv b ≤ Qv γ ⊓ Qv a :=
    (le_sup_right.trans (Subgroup.relIndex_eq_one.mp hone))
  have hm2 := Subgroup.relIndex_mul_relIndex _ _ _ hba (inf_le_left : Qv γ ⊓ Qv a ≤ Qv γ)
  rw [hia, hib] at hm2
  have : (Qv γ ⊓ Qv b).relIndex (Qv γ ⊓ Qv a) = 1 := by omega
  exact hne (le_antisymm (Subgroup.relIndex_eq_one.mp this) hba)

end S35.TB4

end F53.Stellmacher

end CFSG.Quasithin
