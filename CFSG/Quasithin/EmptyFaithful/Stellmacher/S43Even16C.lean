module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even16B

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace C16

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

variable {α α' δ ρ : Geo H M}

theorem R0_le_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (hb : 6 ≤ bMin H M) (h14 : Claim14 α) (h15 : Claim15 α)
    (hno : ¬ Claim17 α) (hc : Cfg α α' δ ρ) : ⁅Wn α ⊓ stab δ, Vn δ⁆ ≤ Zv ρ := by
  have hρv := hc.vρ hA hs he
  have hWρ : Wn α ≤ stab ρ := (h14 hc.crit hc.hδ hc.dδ hc.hρ hc.dρ).1
  have hWN : Wn α ≤ Subgroup.normalizer ((⁅Wn α ⊓ stab δ, Vn δ⁆ ⊔ Zv ρ : Subgroup G) : Set G) :=
    fun w hw => mem_normalizer_sup
      (mem_normalizer_of_conjSub_eq (conjSub_eq_of_mem_centralizer
        (Wn_le_centralizer_R0 hA hs he hb hc hw)))
      (stab_le_normalizer_Zv hA ρ (hWρ hw))
  have hN : stab ρ ≤ Subgroup.normalizer ((⁅Wn α ⊓ stab δ, Vn δ⁆ ⊔ Zv ρ : Subgroup G) : Set G) := by
    rw [← Wn_sup_edge hA h26 hs he (by omega) h14 h15 hno hc]
    exact sup_le hWN (edge_le_normalizer_R0 hA h26 hs he h14 hc)
  have h13 := (hs.of_vtype_false hρv).S13 hA h26 hc.hδρ hN le_sup_right
    (sup_le R0_le_Vn (Sit43.Zv_le_Vn_nbrs hc.hρ))
  exact le_sup_left.trans h13.le

theorem card_Vn_of_cfg (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (hb : 6 ≤ bMin H M) (h14 : Claim14 α) (h15 : Claim15 α)
    (hno : ¬ Claim17 α) (hc : Cfg α α' δ ρ) : Nat.card (Vn δ) = 2 ^ 6 := by
  have hδv := hc.vδ hA hs he
  obtain ⟨w, hw, hwα'⟩ := IsConcreteLE.not_le_iff_exists.mp
    (not_Wn_inf_le_stab hA h26 hs he (by omega) h14 h15 hno hc)
  have hwQ : w ∉ Qv δ := fun h => hwα' (Qv_le_stab_of_mem_nbrs hA hc.hα'δ h)
  have hWρ : Wn α ≤ stab ρ := (h14 hc.crit hc.hδ hc.dδ hc.hρ hc.dρ).1
  have hwE : w ∈ stab ρ ⊓ stab δ := ⟨hWρ hw.1, hw.2⟩
  have hle : ⁅Vn δ, Subgroup.zpowers w⁆ ≤ Zv ρ := by
    refine le_trans ?_ (R0_le_Zv hA h26 hs he hb h14 h15 hno hc)
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hw) le_rfl
  by_cases hwC : w ∈ Subgroup.centralizer (Yv δ : Set G)
  · exact (hs.comm_le_Zv_iff hA h26 (by omega) hδv hc.hρ hwE hwC hwQ).mp hle
  · exact absurd hle (hs.not_comm_le_Zv hA h26 (by omega) hδv hc.hρ hwE hwC)

omit [Finite G] in
theorem comm_mem_zpowers_sup {D D₀ Z : Subgroup G} {w x : G} (h2 : D₀.relIndex D = 2)
    (hw : w ∈ D) (hwD₀ : w ∉ D₀) (hDZ : D ≤ Subgroup.normalizer (Z : Set G))
    (hx : ∀ k ∈ D₀, ⁅k, x⁆ ∈ Z) {d : G} (hd : d ∈ D) :
    ⁅d, x⁆ ∈ Subgroup.zpowers ⁅w, x⁆ ⊔ Z := by
  by_cases hdD₀ : d ∈ D₀
  · exact Subgroup.mem_sup_right (hx d hdD₀)
  · have h1 := inv_mul_mem_of_relIndex_two h2 hw hd hwD₀ hdD₀
    have e : ⁅d, x⁆ = (w * ⁅w⁻¹ * d, x⁆ * w⁻¹) * ⁅w, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hDZ hw) _).mp (hx _ h1)))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

theorem four_le_card_Zv_inf_of_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (he : Even (bMin H M)) (hb : 6 ≤ bMin H M) (h14 : Claim14 α)
    (h15 : Claim15 α) (hno : ¬ Claim17 α) (hc : Cfg α α' δ ρ)
    (h2 : (Zv α ⊓ Qv α').relIndex (Zv α) = 2) : 4 ≤ Nat.card ↥(Zv α ⊓ Zv ρ) := by
  have hb3 : 3 ≤ bMin H M := by omega
  have hδv := hc.vδ hA hs he
  have hρv := hc.vρ hA hs he
  have hD4 := card_Vn_of_cfg hA h26 hs he hb h14 h15 hno hc
  obtain ⟨β, hβ⟩ := hs.exists_adj hA
  have hD4β : Nat.card (Vn β) = 2 ^ 6 :=
    (card_Vn_eq (Sit43.vtype_true_of_adj hs.vα hβ) hδv).trans hD4
  have hWQ : ⁅Wn α, Qv α⁆ ≤ Zv α := hs.comm_Wn_Qv_le hA h26 hb3 hs.vα hβ hD4β
  have hZstab : stab α ≤ Subgroup.normalizer (Zv α : Set G) := stab_le_normalizer_Zv hA α
  have hWα : Wn α ≤ stab α := (hs.Wn_le_Qv hA hb3).trans (pCoreOf_le 2 _)
  have hWρ : Wn α ≤ stab ρ := (h14 hc.crit hc.hδ hc.dδ hc.hρ hc.dρ).1
  obtain ⟨x, hxZ, hxQ, hxH⟩ := h15 hc.crit
  have hxα : x ∈ stab α := hc.Zv_le_stab hA hs he hxZ
  obtain ⟨w, hw, hwα'⟩ := IsConcreteLE.not_le_iff_exists.mp
    (not_Wn_inf_le_stab hA h26 hs he (by omega) h14 h15 hno hc)
  have hDE : Wn α ⊓ stab δ ≤ stab ρ ⊓ stab δ := le_inf (inf_le_left.trans hWρ) inf_le_right
  have hD₀le := relIndex_inf_stab_le_two hA hρv hc.hδρ hc.hα'δ hDE
  have hD₀2 : (Wn α ⊓ stab δ ⊓ stab α').relIndex (Wn α ⊓ stab δ) = 2 := by
    have h0 := relIndex_ne_zero' (Wn α ⊓ stab δ ⊓ stab α') (Wn α ⊓ stab δ)
    have h1 : (Wn α ⊓ stab δ ⊓ stab α').relIndex (Wn α ⊓ stab δ) ≠ 1 := fun h =>
      hwα' (Subgroup.relIndex_eq_one.mp h hw).2
    omega
  have hcW : ⁅w, x⁆ ∈ Wn α := by
    have h1 : x * w⁻¹ * x⁻¹ ∈ Wn α := (Subgroup.mem_normalizer_iff.mp
      (stab_le_normalizer_Wn α hxα) _).mp ((Wn α).inv_mem hw.1)
    have e : ⁅w, x⁆ = w * (x * w⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Wn α).mul_mem hw.1 h1
  have hcc : ⁅w, x⁆ * ⁅w, x⁆ = 1 := by
    have := (hs.isElemAbelian_Wn hA hb).2 _ hcW
    rwa [pow_two] at this
  have hT := relIndex_zpowers_sup_le_two hcc (hZstab (hWα hcW))
  have hDx : ∀ d ∈ Wn α ⊓ stab δ, ⁅d, x⁆ ∈ Subgroup.zpowers ⁅w, x⁆ ⊔ Zv α := fun d hd =>
    comm_mem_zpowers_sup hD₀2 hw (fun h => hwα' h.2) ((inf_le_left.trans hWα).trans hZstab)
      (fun k hk => by rw [commutatorElement_def]; exact hxH k ⟨hk.1.1, hk.2⟩) hd
  have h2' : (Zv α' ⊓ Qv α).relIndex (Zv α') = 2 := (hs.relIndex_Zv_eq hA he hc.crit).symm.trans h2
  have hDz : ∀ d ∈ Wn α ⊓ stab δ, ∀ z ∈ Zv α', ⁅d, z⁆ ∈ Subgroup.zpowers ⁅w, x⁆ ⊔ Zv α := by
    intro d hd z hz
    by_cases hzQ : z ∈ Qv α
    · exact Subgroup.mem_sup_right (hWQ (Subgroup.commutator_mem_commutator hd.1 hzQ))
    · have hq := inv_mul_mem_of_relIndex_two h2' hxZ hz (fun h => hxQ h.2) (fun h => hzQ h.2)
      have e : ⁅d, z⁆ = ⁅d, x⁆ * (x * ⁅d, x⁻¹ * z⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ (hDx d hd) (Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (hZstab hxα) _).mp
          (hWQ (Subgroup.commutator_mem_commutator hd.1 hq.2))))
  have hVsup : Zv ρ ⊔ Zv α' = Vn δ :=
    hs.Zv_sup_Zv_eq hA h26 hb3 hδv hc.hρ hc.hα'δ (hc.ρ_ne hs) hD4
  have hα'ρ : dist α' ρ ≤ bMin H M := by
    have h1 := dist_triangle hA.amalgam.gen α' δ ρ
    rw [dist_eq_one_iff_adj.mpr hc.hδ, dist_eq_one_iff_adj.mpr hc.hρ] at h1
    omega
  have hZα'N : Zv α' ≤ Subgroup.normalizer (Zv ρ : Set G) :=
    (hs.Zv_le_stab_of_dist_le_false hA (hc.vα' hA hs he) hα'ρ).trans (stab_le_normalizer_Zv hA ρ)
  have hZρQ : Zv ρ ≤ Qv α := hs.Zv_le_Qv_of_dist_lt_false hρv
    (by rw [CosetGeom.dist_comm, hc.dρ]; omega)
  have hRT : ⁅Wn α ⊓ stab δ, Vn δ⁆ ≤ Subgroup.zpowers ⁅w, x⁆ ⊔ Zv α := by
    rw [Subgroup.commutator_le]
    intro d hd v hv
    rw [← hVsup] at hv
    obtain ⟨r, hr, z, hz, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZα'N).mp hv
    have hm : ⁅d, z⁆ ∈ Wn α := by
      have h1 : z * d⁻¹ * z⁻¹ ∈ Wn α := (Subgroup.mem_normalizer_iff.mp
        (stab_le_normalizer_Wn α (hc.Zv_le_stab hA hs he hz)) _).mp ((Wn α).inv_mem hd.1)
      have e : ⁅d, z⁆ = d * (z * d⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact (Wn α).mul_mem hd.1 h1
    have e : ⁅d, r * z⁆ = ⁅d, r⁆ * (⁅r, ⁅d, z⁆⁆ * ⁅d, z⁆) := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hrm : ⁅r, ⁅d, z⁆⁆ ∈ Zv α := by
      have h1 := Subgroup.commutator_mem_commutator (hZρQ hr) hm
      rw [Subgroup.commutator_comm] at h1
      exact hWQ h1
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right (hWQ (Subgroup.commutator_mem_commutator hd.1 (hZρQ hr))))
      (Subgroup.mul_mem _ (Subgroup.mem_sup_right hrm) (hDz d hd z hz))
  have hR8 := eight_le_card_R0 hA h26 hs he (by omega) h14 h15 hno hc
  have hR0Z := R0_le_Zv hA h26 hs he hb h14 h15 hno hc
  have h3 : (Zv α).relIndex ⁅Wn α ⊓ stab δ, Vn δ⁆ ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hRT (relIndex_ne_zero' _ _)).trans hT
  have h4 := Subgroup.relIndex_mul_card (Zv α) ⁅Wn α ⊓ stab δ, Vn δ⁆
  have h5 : Nat.card ↥(Zv α ⊓ ⁅Wn α ⊓ stab δ, Vn δ⁆) ≤ Nat.card ↥(Zv α ⊓ Zv ρ) :=
    Subgroup.card_le_of_le (inf_le_inf_left _ hR0Z)
  nlinarith

theorem four_le_card_Zv_inf (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (hb : 6 ≤ bMin H M) (h14 : Claim14 α) (h15 : Claim15 α)
    (hno : ¬ Claim17 α) (hc : Cfg α α' δ ρ) : 4 ≤ Nat.card ↥(Zv α ⊓ Zv ρ) := by
  rcases hs.relIndex_Zv_two_or_four hA h26 he hc.crit hc.hδ (hc.dδ_lt hs) with h2 | h4
  · exact four_le_card_Zv_inf_of_two hA h26 hs he hb h14 h15 hno hc h2
  · have hR1 := hs.comm_eq_Yv_of_four hA h26 he hc.crit hc.hδ (hc.dδ_lt hs) h4
    have hR1Z : ⁅Zv α, Zv α'⁆ ≤ Zv α := by
      rw [Subgroup.commutator_le]
      intro z hz z' hz'
      have h1 : z' * z⁻¹ * z'⁻¹ ∈ Zv α := (Subgroup.mem_normalizer_iff.mp
        (stab_le_normalizer_Zv hA α (hc.Zv_le_stab hA hs he hz')) _).mp ((Zv α).inv_mem hz)
      have e : ⁅z, z'⁆ = z * (z' * z⁻¹ * z'⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact (Zv α).mul_mem hz h1
    have hle : Yv δ ≤ Zv α ⊓ Zv ρ := le_inf (hR1 ▸ hR1Z) (Yv_le_Zv hc.hρ)
    have := Subgroup.card_le_of_le hle
    rw [hs.card_Yv hA h26 (hc.vδ hA hs he)] at this
    exact this

end C16

end CFSG.Quasithin.F53.Stellmacher.S43.Even
