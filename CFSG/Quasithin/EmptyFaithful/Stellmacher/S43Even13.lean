module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even13Grp
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseC2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
open scoped commutatorElement
open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace C13

private theorem fix_swap_not_inv : ∀ τ ∈ S5SylF, τ ≠ 1 → τ ^ 2 = 1 → Perm.sign τ ≠ 1 →
    ∃ σ ∈ S5SylF, ∃ w : orth.W, orth.act τ w = w ∧ orth.act τ (orth.act σ w) ≠ orth.act σ w := by
  decide +kernel

variable {α : Geo H M}

theorem relIndex_ne_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : bMin H M = 2) {α' β : Geo H M} (hc : IsCritPair₁ α α') (hβ : β ∈ nbrs α)
    (hβ' : β ∈ nbrs α') : (Zv α' ⊓ Qv α).relIndex (Zv α') ≠ 2 := by
  intro h2
  have he : Even (bMin H M) := by rw [hb]; exact even_two
  have hs' := hs.sit_crit hA he hc
  have hc' := hs.isCritPair₁_symm hA he hc
  have hd : dist α' β < bMin H M := by rw [dist_eq_one_iff_adj.mpr hβ', hb]; norm_num
  obtain ⟨z, hz, -, hzidx, hzle⟩ := hs'.exists_transposition_of_two hA h26 he hc' hβ hd h2
  have hβα : α ∈ nbrs β := nbrs_symm hβ
  have hβα' : α' ∈ nbrs β := nbrs_symm hβ'
  have hZQβ : Zv α' ≤ Qv β := hs'.Zv_le_Qv_of_dist_lt_false hs'.vα hd
  have hzα : z ∈ stab α := Qv_le_stab_of_mem_nbrs hA hβα (hZQβ hz)
  have hzS : z ∈ stab α ⊓ stab β := ⟨hzα, pCoreOf_le 2 _ (hZQβ hz)⟩
  obtain ⟨D⟩ := hs.exists_dict5 hA hβ
  have hcent' := hs.inf_centralizer_Zv_eq hA he hc
  have hcent : ∀ x ∈ Zv α, x * z = z * x → x ∈ Zv α ⊓ Qv α' := by
    intro x hx hxz
    rw [← hcent']
    refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hle : Subgroup.zpowers z ⊔ Qv α ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff.mp hh]; exact hxz
      · exact (Qv_le_centralizer_Zv hA α).trans
          (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx))
    exact (Subgroup.mem_centralizer_iff.mp (hle (hzle hy)) x rfl).symm
  have hnα : Qv α ≤ Subgroup.normalizer ((Zv α ⊓ Qv α' : Subgroup G) : Set G) :=
    le_normalizer_of_conj fun q hq x hx => by
      have h1 : x * q = q * x :=
        Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA α hq) x hx.1
      have h2 : q * x * q⁻¹ = x := by rw [← h1]; group
      rw [h2]; exact hx
  have hnβ : Qv β ≤ Subgroup.normalizer ((Zv α ⊓ Qv α' : Subgroup G) : Set G) :=
    le_normalizer_of_conj fun q hq x hx =>
      ⟨conj_mem_of_normalizes (stab_le_normalizer_Zv hA α)
          (Qv_le_stab_of_mem_nbrs hA hβα hq) hx.1,
        conj_mem_of_normalizes (le_normalizer_pCoreOf 2 (stab α'))
          (Qv_le_stab_of_mem_nbrs hA hβα' hq) hx.2⟩
  have hinv : stab α ⊓ stab β ≤ Subgroup.normalizer ((Zv α ⊓ Qv α' : Subgroup G) : Set G) := by
    rw [← hs.sup_Qv_edge hA h26 hs.vα hβ]
    exact sup_le hnα hnβ
  have hτ := (D.relIndex_centralizer_eq_two_iff ⟨z, hzα⟩).mp hzidx
  rw [isSwap_iff] at hτ
  obtain ⟨h1, h2', h3⟩ := hτ
  have hτS : D.ψ ⟨z, hzα⟩ ∈ S5SylF := (mem_S5Syl_iff _).mp (D.ψ_mem_S5Syl hzS)
  obtain ⟨σ, hσ, w, hw1, hw2⟩ := fix_swap_not_inv _ hτS h1 h2' h3
  have hσS : σ ∈ D.bar (stab α ⊓ stab β) := by rw [D.bar_S]; exact (mem_S5Syl_iff σ).mpr hσ
  obtain ⟨s, hsS, hsσ⟩ := (D.mem_bar_iff σ).mp hσS
  have hfix : D.φ w * z = z * D.φ w := by
    have h := D.act_eq ⟨z, hzα⟩ w
    rw [hw1] at h
    calc D.φ w * z = (z * D.φ w * z⁻¹) * z := by rw [← h]
      _ = z * D.φ w := by group
  have hmem := conj_mem_of_normalizes hinv hsS (hcent _ (D.φ_mem w) hfix)
  rw [← D.act_eq, hsσ, ← hcent'] at hmem
  have hcomm : z * D.φ (orth.act σ w) = D.φ (orth.act σ w) * z :=
    Subgroup.mem_centralizer_iff.mp hmem.2 z hz
  apply hw2
  apply D.inj
  rw [D.act_eq]
  calc z * D.φ (orth.act σ w) * z⁻¹ = D.φ (orth.act σ w) * z * z⁻¹ := by rw [hcomm]
    _ = D.φ (orth.act σ w) := by group

theorem relIndex_eq_four (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : bMin H M = 2) {α' β : Geo H M} (hc : IsCritPair₁ α α') (hβ : β ∈ nbrs α)
    (hβ' : β ∈ nbrs α') : (Zv α ⊓ Qv α').relIndex (Zv α) = 4 := by
  have he : Even (bMin H M) := by rw [hb]; exact even_two
  have hs' := hs.sit_crit hA he hc
  have hc' := hs.isCritPair₁_symm hA he hc
  have hd : dist α' β < bMin H M := by rw [dist_eq_one_iff_adj.mpr hβ', hb]; norm_num
  rw [hs.relIndex_Zv_eq hA he hc]
  rcases hs'.relIndex_Zv_two_or_four hA h26 he hc' hβ hd with h | h
  · exact absurd h (relIndex_ne_two hA h26 hs hb hc hβ hβ')
  · exact h

theorem Zv_inf_Qv_eq_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : bMin H M = 2) {α' β : Geo H M} (hc : IsCritPair₁ α α') (hβ : β ∈ nbrs α)
    (hβ' : β ∈ nbrs α') : Zv α ⊓ Qv α' = Yv β := by
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hle : Yv β ≤ Zv α ⊓ Qv α' :=
    le_inf (Yv_le_Zv (nbrs_symm hβ)) ((Yv_le_Zv (nbrs_symm hβ')).trans (Zv_le_Qv hA α'))
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hs.card_Yv hA h26 hβv]
  have h1 := Subgroup.relIndex_mul_card (Zv α ⊓ Qv α') (Zv α)
  rw [inf_eq_left.mpr (inf_le_left : Zv α ⊓ Qv α' ≤ Zv α), relIndex_eq_four hA h26 hs hb hc hβ hβ',
    hs.card_Zv_false hs.vα] at h1
  omega

theorem comm_mem_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : bMin H M = 2) {α' β : Geo H M} (hc : IsCritPair₁ α α') (hβ : β ∈ nbrs α)
    (hβ' : β ∈ nbrs α') : ∀ a ∈ Zv α, ∀ u ∈ Qv α' ⊓ Qv β, a * u * a⁻¹ * u⁻¹ ∈ Zv α' := by
  intro a ha u hu
  have haα' : a ∈ stab α' := hs.Zv_le_stab_crit hA hc ha
  have huα : u ∈ stab α := Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ) hu.2
  have h1 : a * u * a⁻¹ * u⁻¹ ∈ Zv α ⊓ Qv α' := by
    refine ⟨?_, ?_⟩
    · have h2 : u * a⁻¹ * u⁻¹ ∈ Zv α :=
        conj_mem_of_normalizes (stab_le_normalizer_Zv hA α) huα ((Zv α).inv_mem ha)
      have e : a * u * a⁻¹ * u⁻¹ = a * (u * a⁻¹ * u⁻¹) := by group
      rw [e]
      exact (Zv α).mul_mem ha h2
    · exact (Qv α').mul_mem (conj_mem_of_normalizes (le_normalizer_pCoreOf 2 (stab α')) haα' hu.1)
        ((Qv α').inv_mem hu.1)
  rw [Zv_inf_Qv_eq_Yv hA h26 hs hb hc hβ hβ'] at h1
  exact Yv_le_Zv (nbrs_symm hβ') h1

theorem exists_mem_oTwoRes (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : bMin H M = 2) {α' β : Geo H M} (hc : IsCritPair₁ α α') (hβ : β ∈ nbrs α)
    (hβ' : β ∈ nbrs α') : ∃ z ∈ Zv α, z ∉ Qv α' ∧ z ∈ oTwoRes (stab α') ⊔ Qv α' := by
  have he : Even (bMin H M) := by rw [hb]; exact even_two
  have hs' := hs.sit_crit hA he hc
  have hd : dist α β < bMin H M := by rw [dist_eq_one_iff_adj.mpr hβ, hb]; norm_num
  have hsup := hs.Zv_sup_Qv_eq_of_four hA h26 he hc hβ' hd
    (relIndex_eq_four hA h26 hs hb hc hβ hβ')
  obtain ⟨D⟩ := hs'.exists_dict5 hA hβ'
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hY := hs.Yv_eq_comm_comm hA h26 hβv (nbrs_symm hβ')
  have hσT : (swap 0 2 * swap 1 3 : Perm (Fin 5)) ∈ S5That :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  obtain ⟨x, hx⟩ := D.surj (swap 0 2 * swap 1 3)
  have hxC : (x : G) ∈ (stab α' ⊓ stab β) ⊓ Subgroup.centralizer (Yv β : Set G) := by
    rw [hY]
    exact (D.mem_centralizer_Y_iff x).mpr (by rw [hx]; exact hσT)
  rw [← hsup, sup_comm] at hxC
  obtain ⟨q, hq, z, hz, hxqz⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
    ((hs.Zv_le_stab_crit hA hc).trans (le_normalizer_pCoreOf 2 (stab α')))).mp hxC
  have hzX : z ∈ stab α' := hs.Zv_le_stab_crit hA hc hz
  have hqX : q ∈ stab α' := pCoreOf_le 2 _ hq
  have hψz : D.ψ ⟨z, hzX⟩ = swap 0 2 * swap 1 3 := by
    have h1 : x = ⟨q, hqX⟩ * ⟨z, hzX⟩ := Subtype.ext hxqz
    have h2 : D.ψ ⟨q, hqX⟩ = 1 := (D.ker_iff _).mpr hq
    rw [← hx, h1, map_mul, h2, one_mul]
  refine ⟨z, hz, fun hzQ => ?_, ?_⟩
  · have h1 := (D.ker_iff ⟨z, hzX⟩).mpr hzQ
    rw [hψz] at h1
    exact absurd h1 (by decide)
  · have hσA : (swap 0 2 * swap 1 3 : Perm (Fin 5)) ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    rw [← map_oTwoRes_eq_alt D.surj] at hσA
    obtain ⟨l, hl, hlσ⟩ := hσA
    have hk : ((l⁻¹ * ⟨z, hzX⟩ : ↥(stab α')) : G) ∈ Qv α' :=
      (D.ker_iff _).mp (by rw [map_mul, map_inv, hlσ, hψz, inv_mul_cancel])
    have e : z = (l : G) * ((l⁻¹ * ⟨z, hzX⟩ : ↥(stab α')) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hl) hk

theorem four_le_idx_orth {σ : Perm (Fin 5)} (h1 : σ ≠ 1) (hσ : σ ∈ alternatingGroup (Fin 5)) :
    4 ≤ idx orth σ := by
  rw [Equiv.Perm.mem_alternatingGroup] at hσ
  rw [idx_orth]
  simp only [h1, hσ, ↓reduceIte]
  split_ifs <;> omega

theorem chief_central (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {α' β : Geo H M} (hα' : vtype α' = false) (hβ' : β ∈ nbrs α') {z : G} (hz : z ∈ stab α')
    (hzQ : z ∉ Qv α') (hzL : z ∈ oTwoRes (stab α') ⊔ Qv α')
    (hzc : ∀ a ∈ Subgroup.zpowers z, ∀ u ∈ Qv α' ⊓ Qv β, a * u * a⁻¹ * u⁻¹ ∈ Zv α') :
    ∀ U' U : Subgroup G, IsChiefStep (stab α') (Qv α') U' U → Zv α' ≤ U' →
      IsCentralStep (stab α') U' U := by
  intro U' U hstep hZU'
  have hs' := hs.of_vtype_false hα'
  have hUQ : U ≤ Qv α' := hstep.1.1
  have hU'U : U' ≤ U := hstep.2.2.1.le
  have hsec : secIdx (Subgroup.zpowers z) U' U ≤ 2 := by
    have hle : Qv β ⊓ U ≤ fixSecIn (Subgroup.zpowers z) U' U := fun x hx =>
      Subgroup.subset_closure ⟨hx.2, fun a ha => hZU' (hzc a ha x ⟨hUQ hx.2, hx.1⟩)⟩
    have h2 : (Qv β).relIndex (Qv α') = 2 := hs'.relIndex_Qv_Qv hA h26 hα' hβ'
    unfold secIdx
    calc (fixSecIn (Subgroup.zpowers z) U' U).relIndex U ≤ (Qv β ⊓ U).relIndex U :=
          Subgroup.relIndex_le_of_le_left hle
            (by unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite)
      _ = (Qv β).relIndex U := Subgroup.inf_relIndex_right _ _
      _ ≤ (Qv β).relIndex (Qv α') := Subgroup.relIndex_le_of_le_right hUQ (by rw [h2]; norm_num)
      _ = 2 := h2
  rcases chief_central_or_nat_or_orth (quot_stab_five hA hα') le_rfl hstep with
    hc | ⟨hcs, hnat | horth⟩
  · exact hc
  · exfalso
    have hzc' : z ∉ cSecIn (stab α') U' U := by rw [hcs]; exact hzQ
    have := IsNatSec.four_le_secIdx hnat hU'U hz hzc'
    omega
  · exfalso
    obtain ⟨θ, -, hk, hidx⟩ := IsModelSec.exists_secIdx horth hU'U
    have hker : ∀ (y : G) (hy : y ∈ stab α'), θ ⟨y, hy⟩ = 1 ↔ y ∈ Qv α' := by
      intro y hy
      rw [← MonoidHom.mem_ker, hk, hcs]
      rfl
    have hθ1 : θ ⟨z, hz⟩ ≠ 1 := fun h1 => hzQ ((hker z hz).mp h1)
    have hθA : θ ⟨z, hz⟩ ∈ alternatingGroup (Fin 5) := by
      obtain ⟨l, hl, q, hq, hlq⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
        ((pCoreOf_le 2 (stab α')).trans (le_normalizer_oTwoRes (stab α')))).mp hzL
      have hlX : l ∈ stab α' := oTwoRes_le _ hl
      have hqX : q ∈ stab α' := pCoreOf_le 2 _ hq
      have e : (⟨z, hz⟩ : ↥(stab α')) = ⟨l, hlX⟩ * ⟨q, hqX⟩ := Subtype.ext hlq
      rw [e, map_mul, (hker q hqX).mpr hq, mul_one]
      exact map_oTwoRes_le_alt θ ⟨⟨l, hlX⟩, hl, rfl⟩
    have h4 := four_le_idx_orth hθ1 hθA
    rw [hidx z hz] at hsec
    omega

theorem Qv_eq_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : bMin H M = 2) {α' β : Geo H M} (hc : IsCritPair₁ α α') (hβ : β ∈ nbrs α)
    (hβ' : β ∈ nbrs α') : Qv α' = Zv α' := by
  have he : Even (bMin H M) := by rw [hb]; exact even_two
  have hs' := hs.sit_crit hA he hc
  have hα' : vtype α' = false := hs.vtype_crit hA he hc
  obtain ⟨z, hz, hzQ, hzL⟩ := exists_mem_oTwoRes hA h26 hs hb hc hβ hβ'
  have hzX : z ∈ stab α' := hs.Zv_le_stab_crit hA hc hz
  have hzc : ∀ a ∈ Subgroup.zpowers z, ∀ u ∈ Qv α' ⊓ Qv β, a * u * a⁻¹ * u⁻¹ ∈ Zv α' :=
    fun a ha u hu => comm_mem_Zv hA h26 hs hb hc hβ hβ' a (Subgroup.zpowers_le.mpr hz ha) u hu
  have hcen := chief_central hA h26 hs hα' hβ' hzX hzQ hzL hzc
  have hQ2 : IsPGroup 2 (Qv α') := pCoreOf_isPGroup (r := 2) (stab α')
  have hcomm := comm_oTwoRes_mem_of_central hQ2 (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _)
    (Zv_le_Qv hA α') (stab_le_normalizer_Zv hA α') hcen
  have hbot := inf_centralizer_oTwoRes_eq_bot (pCoreOf_le 2 _) hQ2 (le_normalizer_pCoreOf 2 _)
    (hs'.centerOf_eq_bot hA h26 hα' hβ')
  have hZc : ∀ a ∈ Zv α', ∀ q ∈ Qv α', a * q = q * a := fun a ha q hq =>
    (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α' ha).2 q hq).symm
  have hZ2 : ∀ a ∈ Zv α', a * a = 1 := fun a ha => by
    rw [← pow_two]; exact (isElemAbelian_Zv hA α').2 a ha
  have hab := comm_of_sq_eq_one (sq_eq_one_of_comm hcomm hZc hZ2 hbot)
  obtain ⟨D⟩ := hs'.exists_dict5 hA hβ'
  exact pCoreOf_eq_of_comm D (Zv_le_Qv hA α')
    (fun a ha b hb => comm_of_mem_isElemAbelian (isElemAbelian_Zv hA α') ha hb)
    (stab_le_normalizer_Zv hA α') hcomm hab hbot

theorem false_of_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : bMin H M = 2) : False := by
  obtain ⟨α', hc⟩ := hs.exists_crit_partner hA
  obtain ⟨β, hβ', hd⟩ := hs.exists_nbr_dist hA hc
  have hβ : β ∈ nbrs α := dist_eq_one_iff_adj.mp (by omega)
  have he : Even (bMin H M) := by rw [hb]; exact even_two
  have hs' := hs.sit_crit hA he hc
  have hα' : vtype α' = false := hs.vtype_crit hA he hc
  have hd' : dist α' β < bMin H M := by rw [dist_eq_one_iff_adj.mpr hβ', hb]; norm_num
  apply hs.not_Qv_le_Qv_nbr hA h26 hα' hβ'
  rw [Qv_eq_Zv hA h26 hs hb hc hβ hβ']
  exact hs'.Zv_le_Qv_of_dist_lt_false hα' hd'

end C13

theorem claim13 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (he : Even (bMin H M)) : 4 ≤ bMin H M := by
  have h1 := hs.b1
  obtain ⟨r, hr⟩ := he
  by_contra h
  exact C13.false_of_two hA h26 hs (by omega)

end CFSG.Quasithin.F53.Stellmacher.S43.Even
