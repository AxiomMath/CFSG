module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3Chain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem commutator_iSup_le {ι : Type*} {A : ι → Subgroup G} {B K : Subgroup G}
    (hn : ⨆ i, A i ≤ Subgroup.normalizer (K : Set G)) (h : ∀ i, ⁅A i, B⁆ ≤ K) :
    ⁅⨆ i, A i, B⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  induction ha using Subgroup.iSup_induction' with
  | hp i x hx => exact (Subgroup.commutator_le.mp (h i)) x hx b hb
  | h1 => simp [commutatorElement_def]
  | hmul x y hx hy hxK hyK =>
    have e : ⁅x * y, b⁆ = (x * ⁅y, b⁆ * x⁻¹) * ⁅x, b⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hn hx) _).mp hyK) hxK

theorem VhatData.img_sup {γ : Geo H M} (V : VhatData γ) {X Y : Subgroup G} (hX : X ≤ stab γ)
    (hY : Y ≤ stab γ) : V.img (X ⊔ Y) = V.img X ⊔ V.img Y := by
  unfold VhatData.img
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

omit [Finite G] in
theorem VhatData.img_conjSub_of_mem_Qv {γ : Geo H M} (V : VhatData γ) {X : Subgroup G} {x : G}
    (hx : x ∈ Qv γ) : V.img (conjSub x X) = V.img X := by
  have hxs : x ∈ stab γ := pCoreOf_le 2 _ hx
  have h := V.map_conj_img X ⟨x, hxs⟩
  have h1 : V.ψ ⟨x, hxs⟩ = 1 := (V.ker _).mpr hx
  rw [h1] at h
  rw [← h]
  ext y
  simp

omit [Finite G] in
theorem VhatData.img_eq_bot_of_le {γ : Geo H M} (V : VhatData γ) {X : Subgroup G}
    (hX : X ≤ Qv γ) : V.img X = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨z, hz, rfl⟩
  have := (V.ker z).mpr (hX (Subgroup.mem_subgroupOf.mp hz))
  rw [this]; exact Subgroup.one_mem _

namespace Step3Ctx

variable {α β α' : Geo H M} (C : Step3Ctx H M S α β α')

include C

theorem dist_beta_γ (P : CritPath α β α') : dist β P.γ = bMin H M - 2 := by
  have hb := C.hb6
  have := P.dist_of_le (i := 1) (j := bMin H M - 1) (by omega) (by omega)
  rw [P.p_one] at this
  omega

theorem comm_Zv_Zv_nbrs (P : CritPath α β α') {μ μ' : Geo H M} (hμ : μ ∈ nbrs β)
    (hμ' : μ' ∈ nbrs P.γ) : ⁅Zv μ, Zv μ'⁆ ≤ Zv β := by
  have hb := C.hb6
  by_cases hbot : ⁅Zv μ, Zv μ'⁆ = ⊥
  · rw [hbot]; exact bot_le
  have hvμ : vtype μ = true := vtype_true_of_mem_nbrs_false hμ C.vtype_beta
  have hgen := C.hA.amalgam.gen
  have h1 : dist β μ = 1 := dist_eq_one_iff_adj.mpr hμ
  have h2 : dist P.γ μ' = 1 := dist_eq_one_iff_adj.mpr hμ'
  have hβγ := C.dist_beta_γ P
  have t1 := dist_triangle hgen μ β μ'
  have t2 := dist_triangle hgen β P.γ μ'
  have t3 := dist_triangle hgen β μ' μ
  rw [CosetGeom.dist_comm μ β] at t1
  have hn : ¬ Zv μ ≤ Qv μ' := fun h => hbot (comm_Zv_eq_bot_of_le_Qv C.hA h)
  have hge : bMin H M ≤ dist μ μ' := by
    by_contra hlt
    exact hn (Zv_le_Qv_of_dist_lt_bMin (by omega))
  have hd : dist μ μ' = bMin H M := by omega
  exact (C.crit_comm_eq_Zv_first hvμ hd hbot (ξ := β) (mem_nbrs_comm hμ) (by omega)).le

theorem comm_Vn_Vn_beta_γ (P : CritPath α β α') : ⁅Vn β, Vn P.γ⁆ ≤ Zv β := by
  have hQ : Vn β ≤ stab β := (Vn_le_Qv' C.hb2 β).trans (pCoreOf_le 2 _)
  have hN : Vn β ≤ Subgroup.normalizer (Zv β : Set G) := hQ.trans (stab_le_normalizer_Zv C.hA β)
  have e : Vn β = ⨆ μ : nbrs β, Zv μ.1 := by
    unfold Vn; exact iSup_subtype'
  rw [e] at hN ⊢
  refine commutator_iSup_le hN fun μ => ?_
  rw [Subgroup.commutator_comm]
  have e' : Vn P.γ = ⨆ μ : nbrs P.γ, Zv μ.1 := by
    unfold Vn; exact iSup_subtype'
  have hQ' : Vn P.γ ≤ stab P.γ := (Vn_le_Qv' C.hb2 P.γ).trans (pCoreOf_le 2 _)
  have hN' : Vn P.γ ≤ Subgroup.normalizer (Zv β : Set G) := by
    rw [C.Zv_beta_eq_Zv_γ P]; exact hQ'.trans (stab_le_normalizer_Zv C.hA P.γ)
  rw [e'] at hN' ⊢
  refine commutator_iSup_le hN' fun μ' => ?_
  rw [Subgroup.commutator_comm]
  exact C.comm_Zv_Zv_nbrs P μ.2 μ'.2

theorem Vn_γ_le_Qv_beta (P : CritPath α β α') : Vn P.γ ≤ Qv β := by
  have hb := C.hb6
  refine iSup₂_le fun μ' hμ' => ?_
  have h2 : dist P.γ μ' = 1 := dist_eq_one_iff_adj.mpr hμ'
  have hβγ := C.dist_beta_γ P
  have t := dist_triangle C.hA.amalgam.gen μ' P.γ β
  rw [CosetGeom.dist_comm μ' P.γ, CosetGeom.dist_comm P.γ β] at t
  exact Zv_le_Qv_of_dist_lt_bMin (by omega)

theorem Vn_le_Qv_alpha' {l : Geo H M} (hl : l ∈ nbrs α') : Vn l ≤ Qv α' := by
  have hb := C.hb6
  refine iSup₂_le fun μ hμ => ?_
  have h1 : dist α' l = 1 := dist_eq_one_iff_adj.mpr hl
  have h2 : dist l μ = 1 := dist_eq_one_iff_adj.mpr hμ
  have t := dist_triangle C.hA.amalgam.gen μ l α'
  rw [CosetGeom.dist_comm μ l, CosetGeom.dist_comm l α'] at t
  exact Zv_le_Qv_of_dist_lt_bMin (by
    rw [CosetGeom.dist_comm μ α']
    have := dist_triangle C.hA.amalgam.gen α' l μ
    omega)

theorem Zv_alpha_le_Qv_beta : Zv α ≤ Qv β :=
  Zv_le_Qv_of_dist_lt_bMin (by
    have h : dist α β = 1 := by
      exact dist_eq_one_iff_adj.mpr C.hc.adj
    have := C.hb6; omega)

theorem exists_swap_nbr (P : CritPath α β α') {l l₂ : Geo H M} (hl : l ∈ nbrs α')
    (hl₂ : l₂ ∈ nbrs α') (hlγ : l ≠ P.γ) (hl₂γ : l₂ ≠ P.γ) :
    ∃ g : ↥(H ⊔ M), (g : G) ∈ Zv α ∧ g • l = l₂ := by
  have hb := C.hb6
  by_cases hll : l = l₂
  · exact ⟨1, one_mem _, by simp [hll]⟩
  have hγ : P.γ ∈ nbrs α' := mem_nbrs_comm (P.γ_adj (by omega))
  obtain ⟨x, hx, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp C.hc.not_le
  obtain ⟨-, hxα'⟩ := Zv_le_stab_pair C.hA C.hc C.hcomm
  have hxγ : x ∈ stab P.γ := Zv_le_stab_of_dist_le_bMin C.hA
    (by rw [P.dist_start_γ (by omega)]; omega) hx
  let g : ↥(H ⊔ M) := ⟨x, stab_le α' (hxα' hx)⟩
  have hgγ : g • P.γ = P.γ := smul_eq_of_mem_stab hxγ
  have hgl : g • l ∈ nbrs α' := smul_mem_nbrs (hxα' hx) hl
  have hne : g • l ≠ l := by
    intro h
    exact hxQ (mem_Qv_of_fixes_two_nbrs C.hA C.vtype_alpha' hγ hl (Ne.symm hlγ) (hxα' hx) hxγ
      (mem_stab_of_smul_eq h))
  have hneγ : g • l ≠ P.γ := by
    intro h
    exact hlγ (smul_left_cancel g (h.trans hgγ.symm))
  have hn := eq_of_three_mem_nbrs C.hA C.vtype_alpha' (Ne.symm hlγ) (Ne.symm hl₂γ) hll hγ hl hl₂
  rw [hn] at hgl
  rcases hgl with h | h | h
  · exact absurd h hneγ
  · exact absurd h hne
  · exact ⟨g, hx, h⟩

theorem Wv_alpha'_eq {γ l l₂ : Geo H M} (hγ : γ ∈ nbrs α') (hl : l ∈ nbrs α')
    (hl₂ : l₂ ∈ nbrs α') (hγl : γ ≠ l) (hγl₂ : γ ≠ l₂) (hll₂ : l ≠ l₂) :
    Wv α' = Vn γ ⊔ Vn l ⊔ Vn l₂ := by
  have hn := eq_of_three_mem_nbrs C.hA C.vtype_alpha' hγl hγl₂ hll₂ hγ hl hl₂
  apply le_antisymm
  · rw [C.Wv_eq_iSup_Vn C.vtype_alpha']
    refine iSup_le fun ℓ => ?_
    obtain ⟨ℓ, hvℓ, hd⟩ := ℓ
    obtain ⟨l', hl', hdl'⟩ := exists_adj_dist_eq C.hA.amalgam.gen (α := α') (δ := ℓ) (d := 1)
      (by omega)
    have hl'n : l' ∈ nbrs α' := dist_eq_one_iff_adj.mp hdl'
    have hle : Vn ℓ ≤ Vn l' := by
      rw [C.Vn_eq_Zv hvℓ]
      exact Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm (show l' ∈ nbrs ℓ from hl'))
    refine hle.trans ?_
    rw [hn] at hl'n
    rcases hl'n with rfl | rfl | rfl
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  · exact sup_le (sup_le (C.Vn_le_Wv_of_mem_nbrs C.vtype_alpha' hγ)
      (C.Vn_le_Wv_of_mem_nbrs C.vtype_alpha' hl)) (C.Vn_le_Wv_of_mem_nbrs C.vtype_alpha' hl₂)

theorem img_Vn_eq_img_Wv (P : CritPath α β α') (V : VhatData β) {l : Geo H M}
    (hl : l ∈ nbrs α') (hlγ : l ≠ P.γ) : V.img (Vn l) = V.img (Wv α') := by
  have hb := C.hb6
  have hγ : P.γ ∈ nbrs α' := mem_nbrs_comm (P.γ_adj (by omega))
  obtain ⟨l₂, hl₂, hl₂γ, hl₂l⟩ := exists_third_mem_nbrs C.hA C.vtype_alpha' (Ne.symm hlγ)
  rw [C.Wv_alpha'_eq hγ hl hl₂ (Ne.symm hlγ) (Ne.symm hl₂γ) (Ne.symm hl₂l)]
  have hVγ : Vn P.γ ≤ stab β := (C.Vn_γ_le_Qv_beta P).trans (pCoreOf_le 2 _)
  have hVl := C.Vn_le_stab_beta P hl hlγ
  have hVl₂ := C.Vn_le_stab_beta P hl₂ hl₂γ
  rw [V.img_sup (sup_le hVγ hVl) hVl₂, V.img_sup hVγ hVl,
    V.img_eq_bot_of_le (C.Vn_γ_le_Qv_beta P), bot_sup_eq]
  obtain ⟨g, hg, hgl⟩ := C.exists_swap_nbr P hl hl₂ hlγ hl₂γ
  have e : Vn l₂ = conjSub (g : G) (Vn l) := by rw [← hgl, Vn_smul]
  rw [e, V.img_conjSub_of_mem_Qv (C.Zv_alpha_le_Qv_beta hg), sup_idem]

theorem comm_inter_le (P : CritPath α β α') {l : Geo H M} (hl : l ∈ nbrs α') (hlγ : l ≠ P.γ) :
    ⁅Vn β ⊓ Qv α', Vn l⁆ ≤ Vn β ⊓ Vn l ⊓ Qv α' := by
  have hVl := C.Vn_le_stab_beta P hl hlγ
  have hVlQ := C.Vn_le_Qv_alpha' hl
  have hQl : Qv α' ≤ stab l := Qv_le_stab_of_mem_nbrs C.hA hl
  rw [Subgroup.commutator_le]
  intro y hy v hv
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 : v * y⁻¹ * v⁻¹ ∈ Vn β :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β (hVl hv)) _).mp ((Vn β).inv_mem hy.1)
    have e : ⁅y, v⁆ = y * (v * y⁻¹ * v⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]; exact Subgroup.mul_mem _ hy.1 h1
  · have h1 : y * v * y⁻¹ ∈ Vn l :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn l (hQl hy.2)) _).mp hv
    have e : ⁅y, v⁆ = (y * v * y⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
    rw [e]; exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hv)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy.2 (hVlQ hv))
      (Subgroup.inv_mem _ hy.2)) (Subgroup.inv_mem _ (hVlQ hv))

theorem comm_Zv_alpha_comm_inter (P : CritPath α β α') {l : Geo H M} (hl : l ∈ nbrs α')
    (hlγ : l ≠ P.γ) : ⁅Zv α, ⁅Vn β ⊓ Qv α', Vn l⁆⁆ = ⊥ := by
  have hH := (C.comm_inter_le P hl hlγ).trans (inf_le_left.trans inf_le_left)
  have hZ : Zv α ≤ Vn β := Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm C.hc.adj)
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha h hh
  have hc := isMulCommutative_subgroup_iff.mp (C.isElemAbelian_Vn' β).1 a (hZ ha) h (hH hh)
  rw [Subgroup.mem_bot, commutatorElement_def, hc]
  simp

theorem comm_comm_inter_Qv_le (P : CritPath α β α') {l : Geo H M} (hl : l ∈ nbrs α')
    (hlγ : l ≠ P.γ) : ⁅⁅Vn β ⊓ Qv α', Vn l⁆, Qv l⁆ ≤ Zv l ∧ Zv l ≤ Zv α' := by
  have hH := (C.comm_inter_le P hl hlγ).trans (inf_le_left.trans inf_le_right)
  have hvl := vtype_false_of_mem_nbrs_true hl C.vtype_alpha'
  refine ⟨?_, C.Zv_le_Zv_of_mem_nbrs C.vtype_alpha' hl⟩
  rw [← C.comm_Vn_Qv_eq hvl]
  exact Subgroup.commutator_mono hH le_rfl

theorem not_comm_inter_le_Ctilde (P : CritPath α β α') (V : VhatData β) {l : Geo H M}
    (hl : l ∈ nbrs α') (hlγ : l ≠ P.γ) : ¬ ⁅Vn β ⊓ Qv α', Vn l⁆ ≤ Ctilde β := by
  intro hH
  have hLX : Zv β ≤ Vn β := Zv_le_Vn_self C.hA β
  have := V.norm
  have hB' := C.img_Vn_eq_img_Wv P V hl hlγ
  obtain ⟨h4, -, -, -, -, -, hidx4⟩ := C.chain_symm P V
  have hne : V.img (Wv α') ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at h4; omega
  have hoff := off15_of_faithful V.M5 V.faithful hne (V.exp_img (C.isElemAbelian_Wv α'))
    (by rw [h4, hidx4])
  have hidx : (fixW V.M5.modA5 (V.img (Wv α'))).index = 4 := by
    rw [hoff.1.2.1, h4]
  set Ysub : Subgroup V.M5.W := (((Vn β ⊓ Qv α').subgroupOf (Vn β)).map
    (QuotientGroup.mk' ((Zv β).subgroupOf (Vn β)))).comap V.β with hYsub
  set T : Subgroup V.M5.modA5.W := Ysub.map V.M5.projA5 with hT
  have hY2 : ((Vn β ⊓ Qv α').subgroupOf (Vn β)).index = 2 := C.index_Vn_beta_Qv
  have hd1 := Subgroup.index_map_dvd ((Vn β ⊓ Qv α').subgroupOf (Vn β))
    (f := QuotientGroup.mk' ((Zv β).subgroupOf (Vn β))) (QuotientGroup.mk'_surjective _)
  have hd2 : Ysub.index = (((Vn β ⊓ Qv α').subgroupOf (Vn β)).map
      (QuotientGroup.mk' ((Zv β).subgroupOf (Vn β)))).index :=
    Subgroup.index_comap_of_surjective _ V.secData.surj
  have hd3 := Subgroup.index_map_dvd Ysub V.M5.projA5_surjective
  have hTY : T.index ∣ 2 := by
    rw [← hY2]; rw [hd2] at hd3; exact hd3.trans hd1
  have hTle : T ≤ fixW V.M5.modA5 (V.img (Wv α')) := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨y', hy', hyu⟩ := Subgroup.mem_map.mp hu
    intro σ hσ
    rw [← hB'] at hσ
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hσ
    have hzV : (z : G) ∈ Vn l := Subgroup.mem_subgroupOf.mp hz
    have hyY : (y' : G) ∈ Vn β ⊓ Qv α' := Subgroup.mem_subgroupOf.mp hy'
    have hux : V.β u = QuotientGroup.mk y' := hyu.symm
    obtain ⟨hkx, h1⟩ := V.secData.equiv z u y' hux
    have hxH : (z : G) * y' * (z : G)⁻¹ * (y' : G)⁻¹ ∈ Ctilde β := by
      apply hH
      have h2 := (⁅Vn β ⊓ Qv α', Vn l⁆).inv_mem
        (Subgroup.commutator_mem_commutator hyY hzV)
      have e : ⁅(y' : G), (z : G)⁆⁻¹ = (z : G) * y' * (z : G)⁻¹ * (y' : G)⁻¹ := by
        simp only [commutatorElement_def]; group
      rwa [e] at h2
    have hw : V.β (V.M5.act (V.ψ z) u * u⁻¹) =
        QuotientGroup.mk (⟨(z : G) * y' * (z : G)⁻¹, hkx⟩ * y'⁻¹ : ↥(Vn β)) := by
      rw [map_mul, h1, map_inv, hux, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hwA := (V.mem_fixW_alt_iff hLX hw).mpr (by simpa using hxH)
    have h5 := (V.M5.projA5_eq_one_iff _).mpr hwA
    rw [map_mul] at h5
    rw [V.M5.projA5_act]
    exact (mul_inv_eq_one.mp h5)
  have h4T := Subgroup.index_dvd_of_le hTle
  rw [hidx] at h4T
  have := h4T.trans hTY
  omega

theorem not_comm_inter_le_Zv_beta (P : CritPath α β α') (V : VhatData β) {l : Geo H M}
    (hl : l ∈ nbrs α') (hlγ : l ≠ P.γ) : ¬ ⁅Vn β ⊓ Qv α', Vn l⁆ ≤ Zv β :=
  fun h => C.not_comm_inter_le_Ctilde P V hl hlγ (h.trans (C.Zv_le_Ctilde β))

end Step3Ctx
end F53.Stellmacher
end CFSG.Quasithin
