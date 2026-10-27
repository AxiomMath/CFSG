module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4A6S6
public import CFSG.Quasithin.Background.E2TwoProofA6
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsA6
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54AS
import CFSG.GH74.Generic.BProg.B3.S3T5L3P
import CFSG.Quasithin.Background.SmithC27RLieA6

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
open CFSG.QuasithinUnique.L246C127 CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open Equiv

private theorem w183finG4A6_b45_eq_true :
    ∀ a : Fin 6, E2P.A6.b45 a = true → a = 4 ∨ a = 5 := by
  decide +kernel

private theorem w183finG4A6_innAutOf_le_autS6 {M : Type} [Group M]
    (e : M ≃* alternatingGroup (Fin 6)) : innAutOf M ≤ w183finG4A6AutS6 e := by
  rintro γ ⟨m, rfl⟩
  rw [w183finG4A6_mem_autS6_iff]
  refine ⟨(e m : Equiv.Perm (Fin 6)), fun n => ?_⟩
  rw [MulAut.conj_apply]
  simp

private theorem w183finG4A6_conjNormal_coe {Y : Type} [Group Y] (L : Subgroup Y) [L.Normal]
    (l : ↥L) : MulAut.conjNormal (l : Y) = MulAut.conj l := by
  ext x
  simp [MulAut.conjNormal_apply, MulAut.conj_apply]

private theorem w183finG4A6_parabolic_stable {Y : Type} [Group Y] (L : Subgroup Y) [L.Normal]
    (e : ↥L ≃* alternatingGroup (Fin 6)) {z : Y}
    (hz : z ∈ Subgroup.normalizer
      (((E2P.A6.P2.comap e.toMonoidHom).map L.subtype : Subgroup Y) : Set Y)) :
    E2P.A6.P2.map (MulAut.congr e (MulAut.conjNormal z)).toMonoidHom = E2P.A6.P2 := by
  let Q : Subgroup ↥L := E2P.A6.P2.comap e.toMonoidHom
  let P : Subgroup Y := Q.map L.subtype
  have hz' : P.map (MulAut.conj z).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hz
  have hcomm : L.subtype.comp (MulAut.conjNormal z).toMonoidHom =
      (MulAut.conj z).toMonoidHom.comp L.subtype := by
    ext q
    simp [MulAut.conjNormal_apply, MulAut.conj_apply]
  have hQstab : Q.map (MulAut.conjNormal z).toMonoidHom = Q := by
    have hmap : (Q.map (MulAut.conjNormal z).toMonoidHom).map L.subtype = Q.map L.subtype := by
      rw [Subgroup.map_map, hcomm, ← Subgroup.map_map]
      exact hz'
    have hA := Subgroup.comap_map_eq_self_of_injective L.subtype_injective
      (Q.map (MulAut.conjNormal z).toMonoidHom)
    have hB := Subgroup.comap_map_eq_self_of_injective L.subtype_injective Q
    rw [hmap] at hA
    rw [hB] at hA
    exact hA.symm
  have hQe : Q.map e.toMonoidHom = E2P.A6.P2 :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective E2P.A6.P2
  have hσ : (Q.map e.toMonoidHom).map
      (MulAut.congr e (MulAut.conjNormal z)).toMonoidHom = Q.map e.toMonoidHom := by
    have hσcomp : (MulAut.congr e (MulAut.conjNormal z)).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp (MulAut.conjNormal z).toMonoidHom := by
      ext q
      simp [MulAut.congr]
    rw [Subgroup.map_map, hσcomp, ← Subgroup.map_map, hQstab]
  rwa [hQe] at hσ

theorem w183finG4A6_normalizer_U_le_P2 :
    Subgroup.normalizer ((E2P.A6.U : Subgroup ↥(alternatingGroup (Fin 6))) :
      Set ↥(alternatingGroup (Fin 6))) ≤ E2P.A6.P2 := by
  rw [CFSG.Quasithin.SmithC27.normalizer_eq_of_isSylowTwoOf_alt6 Even6.isSylow_D]
  exact Subgroup.subgroupOf_mono _ E2P.A6.D_le_L2

theorem w183finG4A6_isMaxParabolicMod_P2 :
    IsMaxParabolicMod (⊥ : Subgroup ↥(alternatingGroup (Fin 6))) ⊤ E2P.A6.P2 := by
  refine ⟨bot_le, ?_, ?_, E2P.A6.U, bot_le, le_top, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne le_top fun htop => ?_
    have h24 := E2P.A6.card_P2
    rw [htop, Subgroup.card_top, Even6.card_alt] at h24
    exact absurd h24 (by decide)
  · intro Y hPY _
    have hUY : E2P.A6.U ≤ Y :=
      (Subgroup.subgroupOf_mono _ E2P.A6.D_le_L2).trans hPY.le
    rcases E2P.A6.overgroups Y hUY with h | h | h | h
    · exact absurd (h ▸ hPY) (not_lt_of_ge (Subgroup.subgroupOf_mono _ E2P.A6.D_le_L2))
    · exact absurd (E2P.A6.eq_of_le_card (h ▸ hPY).le E2P.A6.card_P2 E2P.A6.card_P1).symm
        E2P.A6.P_ne
    · exact absurd (h ▸ hPY) (lt_irrefl _)
    · exact h
  · intro s hs
    refine ⟨3, ?_⟩
    have hs8 : s ^ 8 = 1 := by
      have h : (⟨s, hs⟩ : ↥E2P.A6.U) ^ 8 = 1 := by
        have := pow_card_eq_one' (x := (⟨s, hs⟩ : ↥E2P.A6.U))
        rw [E2P.A6.card_U] at this
        simpa using this
      simpa using congrArg Subtype.val h
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, hs8]
    exact Subgroup.mem_bot.mpr rfl
  · rw [Subgroup.relIndex_top_right, Subgroup.index_eq_card_div, E2P.A6.card_U,
      Even6.card_alt]
    norm_num
  · simpa using w183finG4A6_normalizer_U_le_P2

theorem w183finG4A6_isMaxParabolicMod_map {G Y : Type} [Group G] [Group Y] (ι : G →* Y)
    (hι : Function.Injective ι) {P : Subgroup G} (h : IsMaxParabolicMod (⊥ : Subgroup G) ⊤ P) :
    IsMaxParabolicMod (⊥ : Subgroup Y) ι.range (P.map ι) := by
  obtain ⟨_, hPlt, hmax, S, _, hSL, hSpow, hSodd, hSnorm⟩ := h
  refine ⟨bot_le, ?_, ?_, S.map ι, bot_le, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map ι]
    exact (Subgroup.map_lt_map_iff_of_injective (f := ι) hι).mpr hPlt
  · intro Y' hPY' hY'le
    have hPY'' : P < Y'.comap ι := by
      rw [← Subgroup.map_lt_map_iff_of_injective (f := ι) hι]
      rwa [Subgroup.map_comap_eq_self (f := ι) hY'le]
    have hY'' : Y'.comap ι = ⊤ := hmax _ hPY'' le_top
    rw [← Subgroup.map_comap_eq_self (f := ι) hY'le, hY'', MonoidHom.range_eq_map]
  · rw [MonoidHom.range_eq_map ι]
    exact Subgroup.map_mono hSL
  · intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨k, hk⟩ := hSpow s₀ hs₀
    refine ⟨k, ?_⟩
    rw [← map_pow, Subgroup.mem_bot.mp hk, map_one]
    exact Subgroup.mem_bot.mpr rfl
  · rw [MonoidHom.range_eq_map ι,
      Subgroup.relIndex_map_map_of_injective (f := ι) S ⊤ hι]
    exact hSodd
  · intro z hz
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hz.1
    have hg : g ∈ Subgroup.normalizer (S : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hzn : (ι g) ∈ Subgroup.normalizer ((S.map ι : Subgroup Y) : Set Y) := hz.2
      have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hzn
      have hcomm : (MulAut.conj (ι g)).toMonoidHom.comp ι =
          ι.comp (MulAut.conj g).toMonoidHom := by
        ext s
        simp [MulAut.conj_apply, map_mul]
      have hmap2 : (S.map (MulAut.conj g).toMonoidHom).map ι = S.map ι := by
        rw [Subgroup.map_map, ← hcomm, ← Subgroup.map_map]
        exact hmap
      have hA := Subgroup.comap_map_eq_self_of_injective hι (S.map (MulAut.conj g).toMonoidHom)
      have hB := Subgroup.comap_map_eq_self_of_injective hι S
      rw [hmap2] at hA
      rw [hB] at hA
      exact hA.symm
    exact Subgroup.mem_map.mpr ⟨g, hSnorm ⟨Subgroup.mem_top g, hg⟩, rfl⟩

theorem w183finG4A6_gx_mem_P2 : CFSG.QuasithinUnique.Setup.X3E.gx ∈ E2P.A6.P2 := by
  rw [Subgroup.mem_subgroupOf]
  have h1 : (permOf 6 [[0,1],[4,5]] : Perm (Fin 6)) ∈ E2P.A6.L2 :=
    Subgroup.subset_closure (by decide +kernel)
  have h2 : (permOf 6 [[1,2],[4,5]] : Perm (Fin 6)) ∈ E2P.A6.L2 :=
    Subgroup.subset_closure (by decide +kernel)
  have hprod := E2P.A6.L2.mul_mem h1 h2
  have heq : (CFSG.QuasithinUnique.Setup.X3E.gx : Perm (Fin 6)) =
      permOf 6 [[0,1],[4,5]] * permOf 6 [[1,2],[4,5]] := by
    decide +kernel
  rwa [heq]

theorem w183finG4A6_fixedPoint_of_mem_P2 : ∀ x ∈ E2P.A6.P2, x ^ 3 = 1 →
    ∃ i : Fin 6, ((x : alternatingGroup (Fin 6)) : Perm (Fin 6)) i = i := by
  intro x hx hx3
  have hxL2 : (x : Perm (Fin 6)) ∈ E2P.A6.L2 := Subgroup.mem_subgroupOf.mp hx
  have hstab : ∀ i : Fin 6, E2P.A6.b45 ((x : Perm (Fin 6)) i) = E2P.A6.b45 i :=
    E2P.mem_boolStab.mp (E2P.A6.L2_le_boolStab hxL2)
  have hx3' : (x : Perm (Fin 6)) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hx3
  refine ⟨4, ?_⟩
  by_contra hne
  have h5 : (x : Perm (Fin 6)) 4 = 5 := by
    rcases w183finG4A6_b45_eq_true _ (by rw [hstab 4]; rfl) with h | h
    · exact absurd h hne
    · exact h
  have h5' : (x : Perm (Fin 6)) 5 = 4 ∨ (x : Perm (Fin 6)) 5 = 5 :=
    w183finG4A6_b45_eq_true _ (by rw [hstab 5]; rfl)
  have hval : ((x : Perm (Fin 6)) ^ 3) 4 = 5 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ', Equiv.Perm.mul_apply,
      pow_two, Equiv.Perm.mul_apply, h5]
    rcases h5' with h | h
    · rw [h, h5]
    · rw [h, h]
  rw [hx3'] at hval
  exact absurd hval (by decide +kernel)

theorem w183finG4A6_acts_of_not_induced {Y : Type} [Group Y]
    (L : Subgroup Y) [L.Normal] (e : ↥L ≃* alternatingGroup (Fin 6)) (y : Y)
    (h : (MulAut.conjNormal y : MulAut ↥L) ∉ w183finG4A6AutS6 e) :
    ActsOnDynkinMod ⊥ L y := by
  let Q : Subgroup ↥L := E2P.A6.P2.comap e.toMonoidHom
  let P : Subgroup Y := Q.map L.subtype
  have hPmax : IsMaxParabolicMod (⊥ : Subgroup Y) L P := by
    have hP2' : IsMaxParabolicMod (⊥ : Subgroup ↥L) ⊤ Q := by
      have hmap := w183finG4A6_isMaxParabolicMod_map (e.symm.toMonoidHom) e.symm.injective
        (w183finG4A6_isMaxParabolicMod_P2)
      rw [MonoidHom.range_eq_top.mpr e.symm.surjective] at hmap
      rwa [Subgroup.map_equiv_eq_comap_symm' e.symm E2P.A6.P2] at hmap
    have hmap2 := w183finG4A6_isMaxParabolicMod_map L.subtype L.subtype_injective hP2'
    rwa [Subgroup.range_subtype] at hmap2
  refine ⟨?_, P, hPmax, ?_⟩
  · rw [Subgroup.normalizer_eq_top L]
    exact Subgroup.mem_top y
  · intro l hl hconj
    have hz : y⁻¹ * l ∈ Subgroup.normalizer (P : Set Y) :=
      conjSubgroup_eq_iff_mem_normalizer.mp hconj
    apply h
    let σ : MulAut (alternatingGroup (Fin 6)) :=
      MulAut.congr e (MulAut.conjNormal (y⁻¹ * l))
    have hσstab : E2P.A6.P2.map σ.toMonoidHom = E2P.A6.P2 :=
      w183finG4A6_parabolic_stable L e hz
    have hσmem : ∀ p ∈ E2P.A6.P2, σ p ∈ E2P.A6.P2 := by
      intro p hp
      have hmem : σ p ∈ E2P.A6.P2.map σ.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
      rwa [hσstab] at hmem
    have hg : (MulAut.conjNormal (H := L) (y⁻¹ * l) : MulAut ↥L) ∈
        w183finG4A6AutS6 e := by
      rcases mulAut_alt6_cases σ with ⟨π, hπ⟩ | ⟨g₀, hg₀⟩
      · rw [w183finG4A6AutS6, Subgroup.mem_comap, MonoidHom.mem_range]
        exact ⟨π, hπ.symm⟩
      · exfalso
        have hgxP : σ CFSG.QuasithinUnique.Setup.X3E.gx ∈ E2P.A6.P2 :=
          hσmem _ w183finG4A6_gx_mem_P2
        have hgx3 : (σ CFSG.QuasithinUnique.Setup.X3E.gx) ^ 3 = 1 := by
          have h3 : (CFSG.QuasithinUnique.Setup.X3E.gx) ^ 3 = 1 := by
            apply Subtype.ext
            rw [Subgroup.coe_pow, gx_pow_three]
            rfl
          rw [← map_pow, h3, map_one]
        obtain ⟨i, hi⟩ := w183finG4A6_fixedPoint_of_mem_P2 _ hgxP hgx3
        have hno : ∀ j : Fin 6, (c[0,1,2] * c[3,4,5] : Perm (Fin 6)) j ≠ j := by
          decide +kernel
        have hL : (((g₀ * σ CFSG.QuasithinUnique.Setup.X3E.gx * g₀⁻¹ :
            alternatingGroup (Fin 6)) : Perm (Fin 6)) ((g₀ : Perm (Fin 6)) i)) =
            (g₀ : Perm (Fin 6)) i := by
          simp [Subgroup.coe_mul, Subgroup.coe_inv, hi]
        have hR : (c[0,1,2] * c[3,4,5] : Perm (Fin 6)) ((g₀ : Perm (Fin 6)) i) =
            (g₀ : Perm (Fin 6)) i := by
          rwa [hg₀] at hL
        exact hno _ hR
    have hlS : (MulAut.conjNormal (H := L) l : MulAut ↥L) ∈ w183finG4A6AutS6 e := by
      have hcoe' : (MulAut.conjNormal (H := L) l : MulAut ↥L) =
          MulAut.conj (⟨l, hl⟩ : ↥L) :=
        w183finG4A6_conjNormal_coe L ⟨l, hl⟩
      rw [hcoe']
      exact w183finG4A6_innAutOf_le_autS6 e
        (⟨⟨l, hl⟩, rfl⟩ : MulAut.conj (⟨l, hl⟩ : ↥L) ∈ innAutOf ↥L)
    have hy : MulAut.conjNormal (H := L) y =
        MulAut.conjNormal (H := L) l *
          (MulAut.conjNormal (H := L) (y⁻¹ * l))⁻¹ := by
      rw [← map_inv, ← map_mul]
      congr 1
      group
    rw [hy]
    exact Subgroup.mul_mem _ hlS (Subgroup.inv_mem _ hg)

theorem w183finG4A6_acts_of_not_mem_autS6 {M : Type} [Group M]
    (e : M ≃* alternatingGroup (Fin 6)) (γ : MulAut M) (h : γ ∉ w183finG4A6AutS6 e) :
    ActsOnDynkinMod ⊥ (innAutOf M) γ := by
  have hZ : ∀ z : M, (∀ x, z * x = x * z) → z = 1 := fun z hz => by
    have hz' : z ∈ Subgroup.center M := Subgroup.mem_center_iff.2 (fun g => (hz g).symm)
    rw [w183finG4A6_center_eq_bot e, Subgroup.mem_bot] at hz'
    exact hz'
  haveI : (innAutOf M).Normal := innAutOf_normal M
  let eL : ↥(innAutOf M) ≃* alternatingGroup (Fin 6) :=
    (CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ).symm.trans e
  refine w183finG4A6_acts_of_not_induced (innAutOf M) eL γ ?_
  intro hconj
  apply h
  rw [w183finG4A6_mem_autS6_iff] at hconj ⊢
  obtain ⟨π, hπ⟩ := hconj
  have heL1 : ∀ m' : M, eL (CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ m') = e m' := by
    intro m'
    change ((CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ).symm.trans e)
      (CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ m') = e m'
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have heL2 : ∀ m' : M,
      eL ((MulAut.conjNormal γ) (CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ m')) =
        e (γ m') := by
    intro m'
    change e ((CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ).symm
      ((MulAut.conjNormal γ) (CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ m'))) =
        e (γ m')
    rw [CFSG.GH74.Generic.BProg.B3.S3T5L3.conjNormal_innEquiv hZ γ m',
      MulEquiv.symm_apply_apply]
  refine ⟨π, fun m => ?_⟩
  have h2 := hπ (CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ m)
  rw [heL2 m, heL1 m] at h2
  exact h2

end CFSG.LocalAnalysis.WeakClosure81

end
