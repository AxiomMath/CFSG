module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3A3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits

namespace F53B3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem comm_mem_of_card {U W : Subgroup G} (hUW : U ≤ W) (hcard : Nat.card W = 2 * Nat.card U)
    {s : G} (hsU : s ∈ Subgroup.normalizer (U : Set G)) (hsW : s ∈ Subgroup.normalizer (W : Set G))
    {z : G} (hz : z ∈ W) : s * z * s⁻¹ * z⁻¹ ∈ U := by
  have hidx : (U.subgroupOf W).index = 2 := by
    have h1 := (U.subgroupOf W).card_mul_index
    have h2 : Nat.card (U.subgroupOf W) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv
    rw [h2, hcard] at h1
    have hpos : 0 < Nat.card U := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm 2 _))
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
  have hmem : ∀ x : G, x ∈ W → (x * (a : G) ∈ U ↔ x ∉ U) := by
    intro x hx
    have := xor_iff_iff_not.mp (ha ⟨x, hx⟩)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using this
  have hsz : s * z * s⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hsW z).mp hz
  by_cases hzU : z ∈ U
  · have : s * z * s⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hsU z).mp hzU
    exact U.mul_mem this (U.inv_mem hzU)
  · have hsU' : s * z * s⁻¹ ∉ U := fun h => hzU ((Subgroup.mem_normalizer_iff.mp hsU z).mpr h)
    have h1 : z * (a : G) ∈ U := (hmem z hz).mpr hzU
    have h2 : s * z * s⁻¹ * (a : G) ∈ U := (hmem _ hsz).mpr hsU'
    have h3 := U.mul_mem h2 (U.inv_mem h1)
    have e : s * z * s⁻¹ * (a : G) * (z * (a : G))⁻¹ = s * z * s⁻¹ * z⁻¹ := by group
    rwa [e] at h3

omit [Finite G] in
theorem not_le_of_isModelSec {n : ℕ} {M' : Model n} [Nontrivial M'.W] {F L X : Subgroup G}
    (h : IsModelSec M' F L X) : ¬ X ≤ L := by
  intro hXL
  obtain ⟨_, θ, β, _, _, hsd⟩ := h
  have hsub : ∀ u v : ↥X ⧸ L.subgroupOf X, u = v := by
    intro u v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.mpr (hXL (X.mul_mem (X.inv_mem x.2) y.2))
  obtain ⟨w, hw⟩ := exists_ne (1 : M'.W)
  exact hw (hsd.inj (hsub _ _))

omit [Finite G] in
theorem not_le_of_isNatSec {F L X : Subgroup G} (h : IsNatSec F L X) : ¬ X ≤ L :=
  have : Nontrivial nat.W := inferInstanceAs (Nontrivial (Multiplicative (Fin 4 → ZMod 2)))
  not_le_of_isModelSec h

omit [Finite G] in
theorem not_le_of_isOrthSec {F L X : Subgroup G} (h : IsOrthSec F L X) : ¬ X ≤ L := by
  have : Nontrivial orth.W := by
    have h4 : Nat.card ↥(G6.coreMod 5) = 16 := X1512.card_coreMod (Or.inr rfl)
    exact Finite.one_lt_card_iff_nontrivial.mp (show 1 < Nat.card ↥(G6.coreMod 5) by rw [h4]; norm_num)
  exact not_le_of_isModelSec h

theorem conj_eq_of_central (hB : B3Base H M S) {β : Geo H M} (hβ : vtype β = false) {x u : G}
    (hx : x ∈ stab β) (hu : u ∈ Zv β) : x * u * x⁻¹ = u := by
  have h := Subgroup.mem_centralizer_iff.mp (hB.central β hβ hu).2 x hx
  rw [h]
  group

theorem comm_zv_mem (hB : B3Base H M S) {β μ : Geo H M} (hβ : vtype β = false)
    (hμ : μ ∈ nbrs β) {q z : G} (hq : q ∈ stab β ⊓ stab μ) (hz : z ∈ Zv μ) :
    q * z * q⁻¹ * z⁻¹ ∈ Zv β := by
  have hμt : vtype μ = true := vtype_nbr_of_false hμ hβ
  refine comm_mem_of_card (zv_le_zv_of_adj hB hβ hμ) ?_ ?_ ?_ hz
  · rw [card_zv_true hB hμt, hB.card_two β hβ]
  · exact stab_le_normalizer_Zv hB.amalgam β hq.1
  · exact stab_le_normalizer_Zv hB.amalgam μ hq.2

theorem comm_vn_qv_le (hB : B3Base H M S) {β : Geo H M} (hβ : vtype β = false) :
    ⁅Vn β, Qv β⁆ ≤ Zv β := by
  have hA := hB.amalgam
  rw [Subgroup.commutator_le]
  intro v hv q hq
  have hcent := fun x (hx : x ∈ stab β) u (hu : u ∈ Zv β) => conj_eq_of_central hB hβ hx hu
  let Wq : Subgroup G :=
    { carrier := {v | v ∈ stab β ∧ v * q * v⁻¹ * q⁻¹ ∈ Zv β}
      mul_mem' := by
        rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
        refine ⟨(stab β).mul_mem hv hw, ?_⟩
        have e : v * w * q * (v * w)⁻¹ * q⁻¹ =
            (v * (w * q * w⁻¹ * q⁻¹) * v⁻¹) * (v * q * v⁻¹ * q⁻¹) := by group
        rw [e, hcent v hv _ hw']
        exact (Zv β).mul_mem hw' hv'
      one_mem' := ⟨(stab β).one_mem, by simp⟩
      inv_mem' := by
        rintro v ⟨hv, hv'⟩
        refine ⟨(stab β).inv_mem hv, ?_⟩
        have e : v⁻¹ * q * v⁻¹⁻¹ * q⁻¹ = v⁻¹ * (v * q * v⁻¹ * q⁻¹)⁻¹ * v⁻¹⁻¹ := by group
        rw [e, hcent v⁻¹ ((stab β).inv_mem hv) _ ((Zv β).inv_mem hv')]
        exact (Zv β).inv_mem hv' }
  have hgen : ∀ μ : Geo H M, μ ∈ nbrs β → Zv μ ≤ Wq := by
    intro μ hμ z hz
    have hβμ : β ∈ nbrs μ := (show (graph (H ⊔ M) H M).Adj β μ from hμ).symm
    have hzβ : z ∈ stab β :=
      ((Zv_le_Qv hA μ).trans (Qv_le_stab_of_mem_nbrs hA hβμ)) hz
    refine ⟨hzβ, ?_⟩
    have h1 := comm_zv_mem hB hβ hμ ⟨pCoreOf_le 2 _ hq, Qv_le_stab_of_mem_nbrs hA hμ hq⟩ hz
    have h2 := (Zv β).inv_mem h1
    have e : (q * z * q⁻¹ * z⁻¹)⁻¹ = z * q * z⁻¹ * q⁻¹ := by group
    rwa [e] at h2
  exact ((iSup₂_le hgen : Vn β ≤ Wq) hv).2

theorem comm_vn_qv_eq (hB : B3Base H M S) {β : Geo H M} (hβ : vtype β = false) :
    ⁅Vn β, Qv β⁆ = Zv β := by
  have hA := hB.amalgam
  refine le_antisymm (comm_vn_qv_le hB hβ) ?_
  obtain ⟨z, hzZ, hz1, hzu⟩ := exists_gen_of_card_two (hB.card_two β hβ)
  by_cases hK : ⁅Vn β, Qv β⁆ = ⊥
  · exfalso
    obtain ⟨α, hαadj⟩ := exists_adj β
    have hαn : α ∈ nbrs β := hαadj
    have hα : vtype α = true := vtype_nbr_of_false hαadj hβ
    have hβn : β ∈ nbrs α := (show (graph (H ⊔ M) H M).Adj β α from hαadj).symm
    have hZV : Zv α ≤ Vn β :=
      le_iSup₂_of_le (f := fun (μ : Geo H M) (_ : μ ∈ nbrs β) => Zv μ) α hαn le_rfl
    have hQβ : Qv β ≤ Subgroup.centralizer (Zv α : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := Subgroup.commutator_mem_commutator (hZV hx) hq
      rw [hK, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hle : stab α ⊓ stab β ≤ Qv α := by
      rw [← hB.prod α β hαadj.symm hα]
      refine le_trans ?_ (centralizer_Zv_eq_Qv_of_bAt hA (hB.crit α hα)).le
      refine sup_le ?_ ?_
      · exact le_inf (pCoreOf_le 2 _) (Qv_le_centralizer_Zv hA α)
      · exact le_inf (Qv_le_stab_of_mem_nbrs hA hαn) hQβ
    exact not_inf_stab_le_Qv hA hα hβn hle
  · obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK
    have hxZ : (x : G) ∈ Zv β := comm_vn_qv_le hB hβ x.2
    have hxz : (x : G) = z := (hzu x hxZ).resolve_left (fun h => hx1 (Subtype.ext h))
    intro w hw
    rcases hzu w hw with rfl | rfl
    · exact one_mem _
    · rw [← hxz]
      exact x.2

omit [Finite G] in
theorem mem_Cv_conj {β : Geo H M} {g c : G} (hg : g ∈ stab β) (hc : c ∈ Cv β) :
    g * c * g⁻¹ ∈ Cv β := by
  refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β hg) c).mp hc.1
  · intro y hy
    have hy' : g⁻¹ * y * g ∈ oTwoRes (stab β) := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes (stab β) ((stab β).inv_mem hg))
        y).mp hy
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = (g * c * g⁻¹) * y := by group

theorem cv_inf_zv_eq (hB : B3Base H M S)
    (hnt : ∀ β : Geo H M, vtype β = false → ¬ Vn β ≤ Cv β) {β α : Geo H M}
    (hβ : vtype β = false) (hαadj : (graph (H ⊔ M) H M).Adj β α) : Cv β ⊓ Zv α = Zv β := by
  have hA := hB.amalgam
  have hαn : α ∈ nbrs β := hαadj
  have hα : vtype α = true := vtype_nbr_of_false hαadj hβ
  have hzle : Zv β ≤ Zv α := zv_le_zv_of_adj hB hβ hαadj
  have hZV : ∀ μ ∈ nbrs β, Zv μ ≤ Vn β := fun μ hμ =>
    le_iSup₂_of_le (f := fun (μ : Geo H M) (_ : μ ∈ nbrs β) => Zv μ) μ hμ le_rfl
  have hZC : Zv β ≤ Cv β := by
    refine le_inf (hzle.trans (hZV α hαn)) ?_
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hB.central β hβ hz).2) y (oTwoRes_le _ hy)
  have hle : Zv β ≤ Cv β ⊓ Zv α := le_inf hZC hzle
  have hcard : Nat.card (Zv α) = 2 * Nat.card (Zv β) := by
    rw [card_zv_true hB hα, hB.card_two β hβ]
  have hdvd1 := Subgroup.card_dvd_of_le hle
  have hdvd2 := Subgroup.card_dvd_of_le (inf_le_right : Cv β ⊓ Zv α ≤ Zv α)
  rw [hB.card_two β hβ] at hdvd1
  rw [card_zv_true hB hα] at hdvd2
  have hcpos : 0 < Nat.card (Cv β ⊓ Zv α : Subgroup G) := Nat.card_pos
  have hcle : Nat.card (Cv β ⊓ Zv α : Subgroup G) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd2
  obtain ⟨k, hk⟩ := hdvd1
  have hk' : Nat.card (Cv β ⊓ Zv α : Subgroup G) = 2 ∨ Nat.card (Cv β ⊓ Zv α : Subgroup G) = 4 := by
    omega
  rcases hk' with h2 | h4
  · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h2, hB.card_two β hβ])).symm
  · exfalso
    have hZα : Zv α ≤ Cv β := by
      have : Cv β ⊓ Zv α = Zv α :=
        Subgroup.eq_of_le_of_card_ge (inf_le_right : Cv β ⊓ Zv α ≤ Zv α)
          (by rw [h4, card_zv_true hB hα])
      exact this ▸ inf_le_left
    have hVC : Vn β ≤ Cv β := by
      refine iSup₂_le fun μ hμ => ?_
      obtain ⟨g, hg, hgα⟩ := stab_transitive_on_nbrs hαn hμ
      intro z hz
      have hz0 : (g : G)⁻¹ * z * (g : G) ∈ Zv α := by
        have h1 : z ∈ Zv (g • α) := by
          rw [hgα]
          exact hz
        rw [Zv_smul] at h1
        exact mem_conjSub.mp h1
      have := mem_Cv_conj hg (hZα hz0)
      simpa [mul_assoc] using this
    exact hnt β hβ hVC

theorem kq_le_qv_of_adj (hB : B3Base H M S) {β α : Geo H M} (hβ : vtype β = false)
    (hαadj : (graph (H ⊔ M) H M).Adj β α) : Kq β ≤ Qv α := by
  have hA := hB.amalgam
  have hαn : α ∈ nbrs β := hαadj
  have hα : vtype α = true := vtype_nbr_of_false hαadj hβ
  have hZV : Zv α ≤ Vn β :=
    le_iSup₂_of_le (f := fun (μ : Geo H M) (_ : μ ∈ nbrs β) => Zv μ) α hαn le_rfl
  rw [← centralizer_Zv_eq_Qv_of_bAt hA (hB.crit α hα)]
  exact le_inf (inf_le_left.trans (Qv_le_stab_of_mem_nbrs hA hαn))
    ((inf_le_right : Kq β ≤ Subgroup.centralizer (Vn β : Set G)).trans
      (Subgroup.centralizer_le hZV))

end F53B3

end CFSG.Quasithin
