module

public import CFSG.LocalAnalysis.WeakClosure81.W16Four

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_inf_centralizer_wc16 {A L : Subgroup G} {x : G}
    (hA : x ∈ normalizer (A : Set G)) (hL : x ∈ normalizer (L : Set G)) :
    x ∈ normalizer ((A ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer] at hA hL ⊢
  rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, hA, hL]

namespace Cex16

variable {M V₀ V U S : Subgroup G}

theorem V_le_centralizer (h : Cex16 M V₀ V U S) : V ≤ centralizer (U : Set G) := fun v hv => by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (B2F.isElemAbelian_comm h.hyp.h6.elemAbelian hv (h.le hu)).symm

theorem U_le_conj (h : Cex16 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) :
    U ≤ conjSubgroup V g := fun u hu => by
  rw [mem_conjSubgroup_iff]
  have hu' : g * u * g⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 hg u hu).symm
  rw [hu']
  exact h.le hu

theorem conj_le_centralizer (h : Cex16 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) :
    conjSubgroup V g ≤ centralizer (U : Set G) := fun x hx => by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact B2F.isElemAbelian_comm (E3.isElemAbelian_conjSubgroup h.hyp.h6.elemAbelian g)
    (h.U_le_conj hg hu) hx

theorem mem_of_conj_le_S (h15 : W16Fifteen G) (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G}
    (hle : conjSubgroup V g ≤ S) : g ∈ M := by
  have h2 : conjSubgroup V g ≤ E3.wClos V 0 S :=
    E3.le_wClos ⟨hle, g, le_rfl, E3.mQuot_self _⟩
  rw [h15 hS h] at h2
  have h3 : conjSubgroup V g = V :=
    Subgroup.eq_of_le_of_card_ge h2 (by rw [E3.card_conjSubgroup])
  have h4 : g ∈ normalizer (V : Set G) := conjSubgroup_eq_iff_mem_normalizer.1 h3
  rwa [h.hyp.h6.normalizer_eq] at h4

theorem not_conj_le_M (h15 : W16Fifteen G) (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G}
    (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M) : ¬ conjSubgroup V g ≤ M := by
  intro hle
  have hp : IsPGroup 2 (conjSubgroup V g) := E3.isPGroup_conjSubgroup h.hyp.isPGroup g
  obtain ⟨c, hc, hcle⟩ := E3.exists_le_conj_of_isSylowIn h.sylow
    (le_inf hle (h.conj_le_centralizer hg)) hp
  have h1 : conjSubgroup V (g * c⁻¹) ≤ S := by
    have := E3.conjSubgroup_mono_left c⁻¹ hcle
    rwa [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one] at this
  have h4 := h.mem_of_conj_le_S h15 hS h1
  apply hgM
  have h5 := M.mul_mem h4 hc.1
  simpa using h5

theorem not_comm_conj (h15 : W16Fifteen G) (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G}
    (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M) :
    ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x := by
  intro hcomm
  refine h.not_conj_le_M h15 hS hg hgM fun y hy => ?_
  have hy' : y ∈ centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x hx y hy
  have := Subgroup.centralizer_le_normalizer (V : Set G) hy'
  rwa [h.hyp.h6.normalizer_eq] at this

theorem not_le_pCoreOf (h1 : W16One G) (h15 : W16Fifteen G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) {H : Subgroup G} (hF : Fam16 M U S H) {g : G} (hgH : g ∈ H)
    (hgM : g ∉ M) : ¬ V ≤ pCoreOf 2 H := by
  intro hV
  have hgN : g ∈ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hgH
  have hVg : conjSubgroup V g ≤ pCoreOf 2 H := by
    have := E3.conjSubgroup_mono_left g hV
    rwa [conjSubgroup_eq_iff_mem_normalizer.2 hgN] at this
  exact hgM (h.mem_of_conj_le_S h15 hS (hVg.trans (h.pCoreOf_le_S h1 hS hF)))

theorem inf_conjSubgroup_eq (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G))
    (hgM : g ∉ M) : V ⊓ conjSubgroup M g = U ⊔ V₀ := by
  have hgH : g ∈ S ⊔ zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hF : Fam16 M U S (S ⊔ zpowers g) :=
    ⟨le_sup_left, sup_le h.S_le_centralizer (Subgroup.zpowers_le.2 hg), fun hle => hgM (hle hgH)⟩
  exact h5 hS h hF (h.not_le_pCoreOf h1 h15 hS hF hgH hgM) g hgH (h.not_comm_conj h15 hS hg hgM)

theorem inf_centralizer_eq (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G))
    (hgM : g ∉ M) (hC : conjSubgroup V₀ g ≤ F11.CTilde M V₀ V) {x : G}
    (hx : x ∈ conjSubgroup V₀ g) (hx1 : x ≠ 1) : V ⊓ centralizer ({x} : Set G) = U ⊔ V₀ := by
  have hH := h.hyp
  have hUV₀ := h.inf_conjSubgroup_eq h1 h5 h15 hS hg hgM
  have hw : g * x * g⁻¹ ∈ V₀ := mem_conjSubgroup_iff.1 hx
  apply le_antisymm
  · rw [← hUV₀]
    refine le_inf inf_le_left fun v hv => ?_
    rw [mem_conjSubgroup_iff]
    have hw1 : g * x * g⁻¹ ≠ 1 := fun e => hx1 (by
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, e]
      group)
    refine hH.centralizer_le hw hw1 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    have hxv : x * v = v * x := Subgroup.mem_centralizer_iff.1 hv.2 x rfl
    calc g * x * g⁻¹ * (g * v * g⁻¹) = g * (x * v) * g⁻¹ := by group
      _ = g * (v * x) * g⁻¹ := by rw [hxv]
      _ = g * v * g⁻¹ * (g * x * g⁻¹) := by group
  · refine sup_le ?_ ?_
    · intro u hu
      refine Subgroup.mem_inf.2 ⟨h.le hu, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      rw [hk]
      have he : g * u * g⁻¹ = u := by
        rw [mul_inv_eq_iff_eq_mul]
        exact (Subgroup.mem_centralizer_iff.1 hg u hu).symm
      have hcomm : (g * x * g⁻¹) * (g * u * g⁻¹) = (g * u * g⁻¹) * (g * x * g⁻¹) := by
        rw [he]
        exact B2F.isElemAbelian_comm hH.h6.elemAbelian (hH.h6.le hw) (h.le hu)
      calc x * u = g⁻¹ * ((g * x * g⁻¹) * (g * u * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * u * g⁻¹) * (g * x * g⁻¹)) * g := by rw [hcomm]
        _ = u * x := by group
    · intro v hv0
      have hvV : v ∈ V := hH.h6.le hv0
      refine Subgroup.mem_inf.2 ⟨hvV, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      rw [hk]
      have hvmem : v ∈ V ⊓ conjSubgroup M g := by
        rw [hUV₀]
        exact Subgroup.mem_sup_right hv0
      have hvN : v ∈ normalizer (conjSubgroup V₀ g : Set G) := by
        have := hvmem.2
        rwa [← hH.normalizer₀, E3.conjSubgroup_normalizer] at this
      have hvx : v * x * v⁻¹ ∈ conjSubgroup V₀ g := (Subgroup.mem_normalizer_iff.1 hvN x).1 hx
      have hcomm : x * v * x⁻¹ * v⁻¹ ∈ V₀ :=
        (FourteenTwo.mem_cTilde_iff_comm.1 (hC hx)).2.2 v hvV
      have hc1 : v * x * v⁻¹ * x⁻¹ ∈ conjSubgroup V₀ g :=
        (conjSubgroup V₀ g).mul_mem hvx ((conjSubgroup V₀ g).inv_mem hx)
      have hc2 : v * x * v⁻¹ * x⁻¹ ∈ V₀ := by
        have h' := V₀.inv_mem hcomm
        have e : (x * v * x⁻¹ * v⁻¹)⁻¹ = v * x * v⁻¹ * x⁻¹ := by group
        rwa [e] at h'
      have hbot : v * x * v⁻¹ * x⁻¹ ∈ conjSubgroup V₀ g ⊓ V₀ := ⟨hc1, hc2⟩
      rw [hH.conj_inf_eq_bot hgM, Subgroup.mem_bot] at hbot
      calc x * v = (v * x * v⁻¹ * x⁻¹)⁻¹ * (v * x) := by group
        _ = v * x := by rw [hbot]; group

theorem inf_centralizer_conj_eq (h15 : W16Fifteen G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    {g : G} (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M) :
    V ⊓ centralizer (conjSubgroup V g : Set G) = U := by
  have hH := h.hyp
  set C : Subgroup G := V ⊓ centralizer (conjSubgroup V g : Set G) with hC
  have hUC : U ≤ C := fun u hu => Subgroup.mem_inf.2 ⟨h.le hu, by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact B2F.isElemAbelian_comm (E3.isElemAbelian_conjSubgroup hH.h6.elemAbelian g) hk
      (h.U_le_conj hg hu)⟩
  have hnot : ¬ centralizer (C : Set G) ≤ M := fun hle =>
    h.not_conj_le_M h15 hS hg hgM fun y hy => hle (by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_iff.1 hc.2 y hy).symm)
  have hq1 : (E3.mQuot V U : ℕ∞) ≤ E3.mQuot V C := by
    rw [h.mquot]
    exact rMV_le_mQuot M V C inf_le_left hnot
  have hq2 : E3.mQuot V C ≤ E3.mQuot V U := E3.mQuot_mono hUC
  have hq : E3.mQuot V C = E3.mQuot V U := le_antisymm hq2 (by exact_mod_cast hq1)
  have hcard : Nat.card C = Nat.card U := by
    have e1 := E3.card_eq_two_pow_mul hH.isPGroup (inf_le_left : C ≤ V)
    have e2 := E3.card_eq_two_pow_mul hH.isPGroup h.le
    rw [hq] at e1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (e1.symm.trans e2)
  exact (Subgroup.eq_of_le_of_card_ge hUC (le_of_eq hcard)).symm

theorem inf_centralizer_sup_conj_eq (h15 : W16Fifteen G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M) :
    V ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) = U := by
  rw [← h.inf_centralizer_conj_eq h15 hS hg hgM]
  apply le_antisymm
  · exact inf_le_inf_left V (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.2 (le_sup_right : conjSubgroup V g ≤ V ⊔ conjSubgroup V g)))
  · intro v hv
    refine Subgroup.mem_inf.2 ⟨hv.1, ?_⟩
    have hle : V ⊔ conjSubgroup V g ≤ Subgroup.centralizer ({v} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro k hk
        rw [Set.mem_singleton_iff] at hk
        rw [hk]
        exact B2F.isElemAbelian_comm h.hyp.h6.elemAbelian hv.1 hx
      · rw [Subgroup.mem_centralizer_iff]
        intro k hk
        rw [Set.mem_singleton_iff] at hk
        rw [hk]
        exact (Subgroup.mem_centralizer_iff.1 hv.2 x hx).symm
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.1 (hle hk) v rfl).symm

theorem mem_centralizer_of_mem_normalizer (h : Cex16 M V₀ V U S) {x : G}
    (hx : x ∈ F11.CTilde M V₀ V) (hxU : x ∈ normalizer (U : Set G)) :
    x ∈ centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have h1 : x * u * x⁻¹ * u⁻¹ ∈ V₀ := (FourteenTwo.mem_cTilde_iff_comm.1 hx).2.2 u (h.le hu)
  have h2 : x * u * x⁻¹ * u⁻¹ ∈ U :=
    U.mul_mem ((Subgroup.mem_normalizer_iff.1 hxU u).1 hu) (U.inv_mem hu)
  have h3 : x * u * x⁻¹ * u⁻¹ ∈ U ⊓ V₀ := ⟨h2, h1⟩
  rw [h.inf_eq_bot, Subgroup.mem_bot] at h3
  have h4 : x * u = u * x :=
    calc x * u = (x * u * x⁻¹ * u⁻¹) * (u * x) := by group
      _ = u * x := by rw [h3]; group
  exact h4.symm

end Cex16

end CFSG.LocalAnalysis.WeakClosure81
