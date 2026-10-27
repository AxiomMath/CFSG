module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Sylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.GH74.KGroups CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiUnipotent)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (uElt uElt_mul uElt_inv uElt_mem_antiUnipotent antiUnipotentCenter
   antiUnipotentCenter_comm antiSp_ext glMat_uElt minorAut)

@[expose] noncomputable def Usub : Subgroup (MulAut S4) :=
  (antiUnipotent GF4).map (MulAut.conj : S4 →* MulAut S4)

@[expose] noncomputable def Q1sub : Subgroup (MulAut S4) :=
  (radA1 GF4).map (MulAut.conj : S4 →* MulAut S4)

@[expose] noncomputable def Q2sub : Subgroup (MulAut S4) :=
  (radA2 GF4).map (MulAut.conj : S4 →* MulAut S4)

private theorem w183finSp44_rad_card_GF4 : Nat.card GF4 = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem w183finSp44_rad_mem_Pel {x : El} :
    x ∈ Pel ↔ ∃ a ∈ List.range 4, ∃ b ∈ List.range 4, ∃ c ∈ List.range 4,
      ∃ d ∈ List.range 4, ∃ j ∈ List.range 4, (uMat a b c d, j) = x := by
  simp only [Pel, List.mem_flatMap, List.mem_map]

private theorem w183finSp44_rad_validB_uMat :
    ∀ a ∈ List.range 4, ∀ b ∈ List.range 4, ∀ c ∈ List.range 4, ∀ d ∈ List.range 4,
      validB (uMat a b c d, 0) = true := by
  decide +kernel

private theorem w183finSp44_rad_autOf_uMat {a b c d : Nat} (ha : a < 4) (hb : b < 4)
    (hc : c < 4) (hd : d < 4) :
    autOf (uMat a b c d, 0) =
      MulAut.conj (uElt (GF4.ofNat' a) (GF4.ofNat' b) (GF4.ofNat' c) (GF4.ofNat' d)) := by
  have hvalid : validB (uMat a b c d, 0) = true :=
    w183finSp44_rad_validB_uMat a (List.mem_range.mpr ha) b (List.mem_range.mpr hb) c
      (List.mem_range.mpr hc) d (List.mem_range.mpr hd)
  have hauto : autOf (uMat a b c d, 0) =
      MulAut.conj (toS4 (uMat a b c d, 0).1 (validB_symp hvalid)) *
        minorAut GF4 ^ (uMat a b c d, 0).2 := by
    rw [autOf, dif_pos hvalid]
  have hto : toS4 (uMat a b c d, 0).1 (validB_symp hvalid) =
      uElt (GF4.ofNat' a) (GF4.ofNat' b) (GF4.ofNat' c) (GF4.ofNat' d) := by
    apply antiSp_ext
    show ((toS4 (uMat a b c d, 0).1 (validB_symp hvalid) : GL (Fin 4) GF4) :
        Matrix (Fin 4) (Fin 4) GF4) =
      ((uElt (GF4.ofNat' a) (GF4.ofNat' b) (GF4.ofNat' c) (GF4.ofNat' d) : GL (Fin 4) GF4) :
        Matrix (Fin 4) (Fin 4) GF4)
    rw [toS4_val]
    rw [show (uMat a b c d, 0).1 = uMat a b c d from rfl]
    rw [decodeM_uMat ha hb hc hd]
    exact (glMat_uElt (GF4.ofNat' a) (GF4.ofNat' b) (GF4.ofNat' c) (GF4.ofNat' d)).symm
  rw [hauto, show (uMat a b c d, 0).2 = 0 from rfl, pow_zero, mul_one]
  exact congrArg MulAut.conj hto

private theorem w183finSp44_rad_ofNat'_surj (x : GF4) : ∃ n < 4, GF4.ofNat' n = x := by
  obtain ⟨⟨n, hn⟩⟩ := x
  exact ⟨n, hn, by simp [GF4.ofNat', Nat.mod_eq_of_lt hn]⟩

private theorem w183finSp44_rad_conj_injective :
    Function.Injective (MulAut.conj : S4 →* MulAut S4) :=
  conj_injective (K := GF4)

private theorem w183finSp44_rad_conj_mem_radA1 {u x : S4} (hu : u ∈ antiUnipotent GF4)
    (hx : x ∈ radA1 GF4) : u * x * u⁻¹ ∈ radA1 GF4 := by
  obtain ⟨a, b, c, d, rfl⟩ := hu
  obtain ⟨B, C, D, rfl⟩ := hx
  rw [uElt_inv, uElt_mul, uElt_mul]
  have h : a + 0 + a = 0 := by rw [add_zero]; exact CharTwo.add_self_eq_zero a
  rw [h]
  exact ⟨_, _, _, rfl⟩

private theorem w183finSp44_rad_conj_mem_radA2 {u x : S4} (hu : u ∈ antiUnipotent GF4)
    (hx : x ∈ radA2 GF4) : u * x * u⁻¹ ∈ radA2 GF4 := by
  obtain ⟨a, b, c, d, rfl⟩ := hu
  obtain ⟨A, B, C, rfl⟩ := hx
  rw [uElt_inv, uElt_mul, uElt_mul]
  have h : d + 0 + d = 0 := by rw [add_zero]; exact CharTwo.add_self_eq_zero d
  rw [h]
  exact ⟨_, _, _, rfl⟩

private theorem w183finSp44_rad_U_le_normalizer_radA1 :
    antiUnipotent GF4 ≤ Subgroup.normalizer (radA1 GF4 : Set S4) := by
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (radA1_le_antiUnipotent (K := GF4))]
  rw [Subgroup.normal_subgroupOf_iff (radA1_le_antiUnipotent (K := GF4))]
  intro h k hh hk
  exact w183finSp44_rad_conj_mem_radA1 hk hh

private theorem w183finSp44_rad_U_le_normalizer_radA2 :
    antiUnipotent GF4 ≤ Subgroup.normalizer (radA2 GF4 : Set S4) := by
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (radA2_le_antiUnipotent (K := GF4))]
  rw [Subgroup.normal_subgroupOf_iff (radA2_le_antiUnipotent (K := GF4))]
  intro h k hh hk
  exact w183finSp44_rad_conj_mem_radA2 hk hh

private theorem w183finSp44_rad_card_radA1 : Nat.card (radA1 GF4) = 64 := by
  have h := (card_radicals (K := GF4)).2.1
  rw [w183finSp44_rad_card_GF4] at h
  norm_num at h
  exact h

private theorem w183finSp44_rad_card_radA2 : Nat.card (radA2 GF4) = 64 := by
  have h := (card_radicals (K := GF4)).2.2.1
  rw [w183finSp44_rad_card_GF4] at h
  norm_num at h
  exact h

private theorem w183finSp44_rad_card_center : Nat.card (antiUnipotentCenter GF4) = 16 := by
  have h := (card_radicals (K := GF4)).2.2.2
  rw [w183finSp44_rad_card_GF4] at h
  norm_num at h
  exact h

private theorem w183finSp44_rad_center_relIndex_radA1 :
    (antiUnipotentCenter GF4).relIndex (radA1 GF4) = 4 := by
  have hcard := Subgroup.relIndex_mul_card (antiUnipotentCenter GF4) (radA1 GF4)
  have hinf : antiUnipotentCenter GF4 ⊓ radA1 GF4 = antiUnipotentCenter GF4 :=
    inf_eq_left.mpr (antiUnipotentCenter_le_radA1 (K := GF4))
  rw [hinf, w183finSp44_rad_card_center, w183finSp44_rad_card_radA1] at hcard
  omega

private theorem w183finSp44_rad_center_relIndex_radA2 :
    (antiUnipotentCenter GF4).relIndex (radA2 GF4) = 4 := by
  have hcard := Subgroup.relIndex_mul_card (antiUnipotentCenter GF4) (radA2 GF4)
  have hinf : antiUnipotentCenter GF4 ⊓ radA2 GF4 = antiUnipotentCenter GF4 :=
    inf_eq_left.mpr (antiUnipotentCenter_le_radA2 (K := GF4))
  rw [hinf, w183finSp44_rad_card_center, w183finSp44_rad_card_radA2] at hcard
  omega

private theorem w183finSp44_rad_Q1_inf_Q2 :
    Q1sub ⊓ Q2sub = (radA1 GF4 ⊓ radA2 GF4).map (MulAut.conj : S4 →* MulAut S4) := by
  have hinj := w183finSp44_rad_conj_injective
  refine le_antisymm ?_ ?_
  · intro α hα
    rw [Subgroup.mem_inf] at hα
    obtain ⟨hα1, hα2⟩ := hα
    rw [Q1sub] at hα1
    rw [Q2sub] at hα2
    obtain ⟨x, hx, hxα⟩ := Subgroup.mem_map.mp hα1
    obtain ⟨y, hy, hyα⟩ := Subgroup.mem_map.mp hα2
    have hxy : x = y := hinj (by rw [hxα, hyα])
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_inf.mpr ⟨hx, hxy ▸ hy⟩, hxα⟩
  · exact le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)

private theorem w183finSp44_rad_isElemAbelian_comap {E : Subgroup (MulAut S4)}
    (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.comap (MulAut.conj : S4 →* MulAut S4)) := by
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff_of_setLike]
    intro x hx y hy
    apply w183finSp44_rad_conj_injective
    rw [map_mul, map_mul]
    exact (isMulCommutative_iff_of_setLike.mp hE.1) (MulAut.conj x)
      (Subgroup.mem_comap.mp hx) (MulAut.conj y) (Subgroup.mem_comap.mp hy)
  · intro x hx
    apply w183finSp44_rad_conj_injective
    rw [map_pow, map_one]
    exact hE.2 (MulAut.conj x) (Subgroup.mem_comap.mp hx)

theorem Psub_inf_inner : Psub ⊓ innAutOf S4 = Usub := by
  refine le_antisymm ?_ ?_
  · intro α hα
    obtain ⟨x, hx, hx2, rfl⟩ := (mem_Psub_inner_iff α).mp hα
    obtain ⟨a, ha, b, hb, c, hc, d, hd, j, hj, hxj⟩ := w183finSp44_rad_mem_Pel.mp hx
    have hj0 : j = 0 := by
      have h2 : x.2 = j := by rw [← hxj]
      rw [← h2]
      exact hx2
    have hx' : x = (uMat a b c d, 0) := by rw [← hxj, hj0]
    rw [Usub]
    refine Subgroup.mem_map.mpr ⟨uElt (GF4.ofNat' a) (GF4.ofNat' b) (GF4.ofNat' c)
      (GF4.ofNat' d), uElt_mem_antiUnipotent _ _ _ _, ?_⟩
    rw [hx']
    exact (w183finSp44_rad_autOf_uMat (List.mem_range.mp ha) (List.mem_range.mp hb)
      (List.mem_range.mp hc) (List.mem_range.mp hd)).symm
  · intro α hα
    rw [Usub] at hα
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hα
    obtain ⟨a, b, c, d, rfl⟩ := hu
    obtain ⟨a', ha', haeq⟩ := w183finSp44_rad_ofNat'_surj a
    obtain ⟨b', hb', hbeq⟩ := w183finSp44_rad_ofNat'_surj b
    obtain ⟨c', hc', hceq⟩ := w183finSp44_rad_ofNat'_surj c
    obtain ⟨d', hd', hdeq⟩ := w183finSp44_rad_ofNat'_surj d
    refine (mem_Psub_inner_iff (MulAut.conj (uElt a b c d))).mpr
      ⟨(uMat a' b' c' d', 0), ?_, rfl, ?_⟩
    · rw [w183finSp44_rad_mem_Pel]
      exact ⟨a', List.mem_range.mpr ha', b', List.mem_range.mpr hb', c', List.mem_range.mpr hc',
        d', List.mem_range.mpr hd', 0, List.mem_range.mpr (by norm_num), rfl⟩
    · rw [w183finSp44_rad_autOf_uMat ha' hb' hc' hd', haeq, hbeq, hceq, hdeq]

theorem rad_c1 : Q1sub ≤ Psub ⊓ innAutOf S4 := by
  rw [Psub_inf_inner]
  exact Subgroup.map_mono radA1_le_antiUnipotent

theorem rad_c2 : Q2sub ≤ Psub ⊓ innAutOf S4 := by
  rw [Psub_inf_inner]
  exact Subgroup.map_mono radA2_le_antiUnipotent

theorem rad_c3 : Psub ⊓ innAutOf S4 ≤ Q1sub ⊔ Q2sub := by
  rw [Psub_inf_inner]
  change (antiUnipotent GF4).map (MulAut.conj : S4 →* MulAut S4) ≤
    (radA1 GF4).map (MulAut.conj : S4 →* MulAut S4) ⊔
      (radA2 GF4).map (MulAut.conj : S4 →* MulAut S4)
  rw [← Subgroup.map_sup, ← antiUnipotent_eq_radA1_sup_radA2]

theorem rad_c4 : Psub ⊓ innAutOf S4 ≤ Subgroup.normalizer (Q1sub : Set (MulAut S4)) := by
  rw [Psub_inf_inner]
  intro α hα
  rw [Usub] at hα
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hα
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (Subgroup.map (MulAut.conj : S4 →* MulAut S4) (radA1 GF4)).map
      (MulAut.conj (MulAut.conj u)) =
    Subgroup.map (MulAut.conj : S4 →* MulAut S4) (radA1 GF4)
  have hcomp : (↑(MulAut.conj (MulAut.conj u)) : MulAut S4 →* MulAut S4).comp
        (MulAut.conj : S4 →* MulAut S4) =
      (MulAut.conj : S4 →* MulAut S4).comp (↑(MulAut.conj u) : S4 →* S4) := by
    ext x
    simp [MulAut.conj_apply]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (w183finSp44_rad_U_le_normalizer_radA1 hu)]

theorem rad_c5 : Psub ⊓ innAutOf S4 ≤ Subgroup.normalizer (Q2sub : Set (MulAut S4)) := by
  rw [Psub_inf_inner]
  intro α hα
  rw [Usub] at hα
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hα
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (Subgroup.map (MulAut.conj : S4 →* MulAut S4) (radA2 GF4)).map
      (MulAut.conj (MulAut.conj u)) =
    Subgroup.map (MulAut.conj : S4 →* MulAut S4) (radA2 GF4)
  have hcomp : (↑(MulAut.conj (MulAut.conj u)) : MulAut S4 →* MulAut S4).comp
        (MulAut.conj : S4 →* MulAut S4) =
      (MulAut.conj : S4 →* MulAut S4).comp (↑(MulAut.conj u) : S4 →* S4) := by
    ext x
    simp [MulAut.conj_apply]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (w183finSp44_rad_U_le_normalizer_radA2 hu)]

theorem rad_c6 : IsElemAbelian 2 Q1sub := by
  constructor
  · rw [isMulCommutative_iff_of_setLike]
    intro x hx y hy
    rw [Q1sub] at hx hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, radA1_comm ha hb]
  · intro x hx
    rw [Q1sub] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, pow_two, mul_self_of_mem_radA1 ha, map_one]

theorem rad_c7 : IsElemAbelian 2 Q2sub := by
  constructor
  · rw [isMulCommutative_iff_of_setLike]
    intro x hx y hy
    rw [Q2sub] at hx hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, radA2_comm ha hb]
  · intro x hx
    rw [Q2sub] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, pow_two, mul_self_of_mem_radA2 ha, map_one]

theorem rad_c8 : ∀ x ∈ Q1sub ⊓ Q2sub, ∀ s ∈ Psub ⊓ innAutOf S4, x * s = s * x := by
  intro x hx s hs
  rw [w183finSp44_rad_Q1_inf_Q2] at hx
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Psub_inf_inner, Usub] at hs
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hs
  have hzc : z ∈ antiUnipotentCenter GF4 := by
    rw [← radA1_inf_radA2]
    exact hz
  have hzu : z * u = u * z := ((mem_antiUnipotentCenter_iff_central z).mp hzc).2 u hu
  rw [← map_mul, ← map_mul, hzu]

theorem rad_c9 : ∀ E : Subgroup (MulAut S4), E ≤ Psub ⊓ innAutOf S4 → IsElemAbelian 2 E →
    E ≤ Q1sub ∨ E ≤ Q2sub := by
  intro E hE hEel
  have hinj := w183finSp44_rad_conj_injective
  have hEU : E.comap (MulAut.conj : S4 →* MulAut S4) ≤ antiUnipotent GF4 := by
    have h1 : E ≤ Subgroup.map (MulAut.conj : S4 →* MulAut S4) (antiUnipotent GF4) := by
      change E ≤ Usub
      rw [← Psub_inf_inner]
      exact hE
    have h2 : E.comap (MulAut.conj : S4 →* MulAut S4) ≤
        (Subgroup.map (MulAut.conj : S4 →* MulAut S4) (antiUnipotent GF4)).comap
          (MulAut.conj : S4 →* MulAut S4) := Subgroup.comap_mono h1
    rwa [Subgroup.comap_map_eq_self_of_injective hinj] at h2
  have hEel' := w183finSp44_rad_isElemAbelian_comap hEel
  have hEmap : (E.comap (MulAut.conj : S4 →* MulAut S4)).map
      (MulAut.conj : S4 →* MulAut S4) = E :=
    Subgroup.map_comap_eq_self (hE.trans inf_le_right)
  rcases elementary_le_radA1_or_radA2 hEU (fun x hx => by
      have := hEel'.2 x hx
      rwa [pow_two] at this) with h | h
  · left
    rw [← hEmap]
    exact Subgroup.map_mono h
  · right
    rw [← hEmap]
    exact Subgroup.map_mono h

theorem rad_c10 : ∀ E : Subgroup (MulAut S4), E ≤ Q1sub → mOfG E (E ⊓ Q2sub) ≤ 2 := by
  intro E hE
  have hinj := w183finSp44_rad_conj_injective
  have hE0 : E.comap (MulAut.conj : S4 →* MulAut S4) ≤ radA1 GF4 := by
    have h1 : E.comap (MulAut.conj : S4 →* MulAut S4) ≤
        (Subgroup.map (MulAut.conj : S4 →* MulAut S4) (radA1 GF4)).comap
          (MulAut.conj : S4 →* MulAut S4) := Subgroup.comap_mono hE
    rwa [Subgroup.comap_map_eq_self_of_injective hinj] at h1
  have hle : E ≤ (MulAut.conj : S4 →* MulAut S4).range :=
    hE.trans (Subgroup.map_le_range (f := (MulAut.conj : S4 →* MulAut S4)) (radA1 GF4))
  have hEmap : (E.comap (MulAut.conj : S4 →* MulAut S4)).map
      (MulAut.conj : S4 →* MulAut S4) = E := Subgroup.map_comap_eq_self hle
  have hE0'' : E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA2 GF4 =
      E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ antiUnipotentCenter GF4 := by
    rw [← radA1_inf_radA2, ← inf_assoc, inf_eq_left.mpr hE0]
  have hrel1 : (E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA2 GF4).relIndex
      (E.comap (MulAut.conj : S4 →* MulAut S4)) =
      (antiUnipotentCenter GF4).relIndex (E.comap (MulAut.conj : S4 →* MulAut S4)) := by
    rw [hE0'']
    exact Subgroup.inf_relIndex_left _ _
  have hrel2 : (antiUnipotentCenter GF4).relIndex (E.comap (MulAut.conj : S4 →* MulAut S4)) ≤
      (antiUnipotentCenter GF4).relIndex (radA1 GF4) :=
    Subgroup.relIndex_le_of_le_right hE0 (by
      rw [w183finSp44_rad_center_relIndex_radA1]
      norm_num)
  have hrel : (E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA2 GF4).relIndex
      (E.comap (MulAut.conj : S4 →* MulAut S4)) ≤ 4 := by
    rw [hrel1]
    exact hrel2.trans_eq w183finSp44_rad_center_relIndex_radA1
  have hmain : ((E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA2 GF4).map
        (MulAut.conj : S4 →* MulAut S4)).relIndex
        ((E.comap (MulAut.conj : S4 →* MulAut S4)).map (MulAut.conj : S4 →* MulAut S4)) =
      (E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA2 GF4).relIndex
        (E.comap (MulAut.conj : S4 →* MulAut S4)) :=
    Subgroup.relIndex_map_map_of_injective _ _ hinj
  have hinf : E ⊓ Q2sub = (E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA2 GF4).map
      (MulAut.conj : S4 →* MulAut S4) := by
    rw [Subgroup.map_inf _ _ _ hinj, hEmap]
    rfl
  have step1 : (E ⊓ Q2sub).relIndex E =
      ((E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA2 GF4).map
        (MulAut.conj : S4 →* MulAut S4)).relIndex
        ((E.comap (MulAut.conj : S4 →* MulAut S4)).map (MulAut.conj : S4 →* MulAut S4)) := by
    rw [hinf, hEmap]
  calc mOfG E (E ⊓ Q2sub) = Nat.log 2 ((E ⊓ Q2sub).relIndex E) := rfl
    _ = Nat.log 2 (((E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA2 GF4).map
          (MulAut.conj : S4 →* MulAut S4)).relIndex
          ((E.comap (MulAut.conj : S4 →* MulAut S4)).map (MulAut.conj : S4 →* MulAut S4))) := by
        rw [step1]
    _ = Nat.log 2 ((E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA2 GF4).relIndex
          (E.comap (MulAut.conj : S4 →* MulAut S4))) := by rw [hmain]
    _ ≤ Nat.log 2 4 := Nat.log_mono_right hrel
    _ ≤ 2 := by decide

theorem rad_c11 : ∀ E : Subgroup (MulAut S4), E ≤ Q2sub → mOfG E (E ⊓ Q1sub) ≤ 2 := by
  intro E hE
  have hinj := w183finSp44_rad_conj_injective
  have hE0 : E.comap (MulAut.conj : S4 →* MulAut S4) ≤ radA2 GF4 := by
    have h1 : E.comap (MulAut.conj : S4 →* MulAut S4) ≤
        (Subgroup.map (MulAut.conj : S4 →* MulAut S4) (radA2 GF4)).comap
          (MulAut.conj : S4 →* MulAut S4) := Subgroup.comap_mono hE
    rwa [Subgroup.comap_map_eq_self_of_injective hinj] at h1
  have hle : E ≤ (MulAut.conj : S4 →* MulAut S4).range :=
    hE.trans (Subgroup.map_le_range (f := (MulAut.conj : S4 →* MulAut S4)) (radA2 GF4))
  have hEmap : (E.comap (MulAut.conj : S4 →* MulAut S4)).map
      (MulAut.conj : S4 →* MulAut S4) = E := Subgroup.map_comap_eq_self hle
  have hE0'' : E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA1 GF4 =
      E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ antiUnipotentCenter GF4 := by
    rw [← radA1_inf_radA2, ← inf_assoc, inf_eq_left.mpr (inf_le_left.trans hE0)]
  have hrel1 : (E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA1 GF4).relIndex
      (E.comap (MulAut.conj : S4 →* MulAut S4)) =
      (antiUnipotentCenter GF4).relIndex (E.comap (MulAut.conj : S4 →* MulAut S4)) := by
    rw [hE0'']
    exact Subgroup.inf_relIndex_left _ _
  have hrel2 : (antiUnipotentCenter GF4).relIndex (E.comap (MulAut.conj : S4 →* MulAut S4)) ≤
      (antiUnipotentCenter GF4).relIndex (radA2 GF4) :=
    Subgroup.relIndex_le_of_le_right hE0 (by
      rw [w183finSp44_rad_center_relIndex_radA2]
      norm_num)
  have hrel : (E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA1 GF4).relIndex
      (E.comap (MulAut.conj : S4 →* MulAut S4)) ≤ 4 := by
    rw [hrel1]
    exact hrel2.trans_eq w183finSp44_rad_center_relIndex_radA2
  have hmain : ((E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA1 GF4).map
        (MulAut.conj : S4 →* MulAut S4)).relIndex
        ((E.comap (MulAut.conj : S4 →* MulAut S4)).map (MulAut.conj : S4 →* MulAut S4)) =
      (E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA1 GF4).relIndex
        (E.comap (MulAut.conj : S4 →* MulAut S4)) :=
    Subgroup.relIndex_map_map_of_injective _ _ hinj
  have hinf : E ⊓ Q1sub = (E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA1 GF4).map
      (MulAut.conj : S4 →* MulAut S4) := by
    rw [Subgroup.map_inf _ _ _ hinj, hEmap]
    rfl
  have step1 : (E ⊓ Q1sub).relIndex E =
      ((E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA1 GF4).map
        (MulAut.conj : S4 →* MulAut S4)).relIndex
        ((E.comap (MulAut.conj : S4 →* MulAut S4)).map (MulAut.conj : S4 →* MulAut S4)) := by
    rw [hinf, hEmap]
  calc mOfG E (E ⊓ Q1sub) = Nat.log 2 ((E ⊓ Q1sub).relIndex E) := rfl
    _ = Nat.log 2 (((E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA1 GF4).map
          (MulAut.conj : S4 →* MulAut S4)).relIndex
          ((E.comap (MulAut.conj : S4 →* MulAut S4)).map (MulAut.conj : S4 →* MulAut S4))) := by
        rw [step1]
    _ = Nat.log 2 ((E.comap (MulAut.conj : S4 →* MulAut S4) ⊓ radA1 GF4).relIndex
          (E.comap (MulAut.conj : S4 →* MulAut S4))) := by rw [hmain]
    _ ≤ Nat.log 2 4 := Nat.log_mono_right hrel
    _ ≤ 2 := by decide

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
