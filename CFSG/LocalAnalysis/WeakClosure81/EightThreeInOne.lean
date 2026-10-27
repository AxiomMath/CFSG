module

public import CFSG.LocalAnalysis.WeakClosure81.EightThreeInHatK
public import CFSG.LocalAnalysis.WeakClosure81.EightThreeC
public import CFSG.LocalAnalysis.WeakClosure81.EightThreeD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem inf_normalizer_le_normalizer_kGenIn (V H : Subgroup G) :
    H ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (kGenIn V H : Set G) := by
  intro x hx
  obtain ⟨hxH, hxV⟩ := Subgroup.mem_inf.mp hx
  have h1 : conjSubgroup (kGenIn V H) x ≤ kGenIn V H := by
    have hmap : conjSubgroup (kGenIn V H) x =
        ⨆ k ∈ conjClosure V H, conjSubgroup V (k * x) := by
      rw [show conjSubgroup (kGenIn V H) x =
          (kGenIn V H).map (MulAut.conj x⁻¹).toMonoidHom from rfl]
      unfold kGenIn
      rw [Subgroup.map_iSup]
      refine iSup_congr fun k => ?_
      rw [Subgroup.map_iSup]
      refine iSup_congr fun hk => ?_
      exact conjSubgroup_conjSubgroup V k x
    rw [hmap]
    refine iSup₂_le fun k hk => ?_
    have hxN : x ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
      le_normalizer_conjClosure V H hxH
    have hk' : x⁻¹ * k * x ∈ conjClosure V H :=
      (Subgroup.mem_normalizer_iff''.mp hxN k).mp hk
    have hVx : conjSubgroup V x = V := conjSubgroup_eq_iff_mem_normalizer.mpr hxV
    have hconj : conjSubgroup V (k * x) = conjSubgroup V (x⁻¹ * k * x) := by
      have hkx : k * x = x * (x⁻¹ * k * x) := by group
      rw [hkx, ← conjSubgroup_conjSubgroup V x (x⁻¹ * k * x), hVx]
    rw [hconj]
    exact conjSubgroup_le_kGenIn hk'
  exact conjSubgroup_eq_iff_mem_normalizer.mp
    (Subgroup.eq_of_le_of_card_ge h1 (E3.card_conjSubgroup (kGenIn V H) x).ge)

namespace Hyp83

variable {V H T : Subgroup G}

theorem kGenIn_transitive (h : Hyp83 V H T) {k : G} (hk : k ∈ conjClosure V H) :
    ∃ a ∈ kGenIn V H, conjSubgroup V k = conjSubgroup V a := by
  have h' := AmbientH.hyp83 h
  have hOmH' : ∀ W ∈ omegaSet (V.subgroupOf H) (⊤ : Subgroup ↥H)
      (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)), W ≤ ⊤ :=
    fun _ _ => le_top
  have hkH : k ∈ H := conjClosure_le_of_le_H h.le_H hk
  have hkK : (⟨k, hkH⟩ : ↥H) ∈ kSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
      (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)) := by
    rw [AmbientH.kSub_eq h]
    exact Subgroup.mem_subgroupOf.mpr hk
  obtain ⟨â, hâ, heq⟩ := h'.kGen_transitive hOmH'
    (conjSubgroup_mem_omegaOrb (V := V.subgroupOf H) (H := ⊤) (T := T.subgroupOf H) hkK)
  have hâK : (â : G) ∈ kGenIn V H := by
    have hmem : â ∈ (kGenIn V H).subgroupOf H := by
      rwa [← AmbientH.kGen_eq h]
    exact Subgroup.mem_subgroupOf.mp hmem
  refine ⟨(â : G), hâK, ?_⟩
  have hmap := congrArg (Subgroup.map H.subtype) heq
  rwa [map_conjSubgroup_subgroupOf h.le_H hkH,
    map_conjSubgroup_subgroupOf h.le_H (kGenIn_le_H h.le_H hâK)] at hmap

theorem inf_centralizer_kGenIn_eq_bot (h : Hyp83 V H T) :
    V ⊓ Subgroup.centralizer (kGenIn V H : Set G) = ⊥ := by
  have h' := AmbientH.hyp83 h
  have hOmH' : ∀ W ∈ omegaSet (V.subgroupOf H) (⊤ : Subgroup ↥H)
      (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)), W ≤ ⊤ :=
    fun _ _ => le_top
  have hkey := h'.inf_centralizer_kGen_eq_bot hOmH'
  rw [AmbientH.kGen_eq h] at hkey
  refine le_bot_iff.mp fun z hz => ?_
  have hzH : z ∈ H := h.le_H hz.1
  have hzV' : (⟨z, hzH⟩ : ↥H) ∈ V.subgroupOf H := Subgroup.mem_subgroupOf.mpr hz.1
  have hzC' : (⟨z, hzH⟩ : ↥H) ∈
      Subgroup.centralizer ((kGenIn V H).subgroupOf H : Set ↥H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro â hâ
    have hâK : (â : G) ∈ kGenIn V H := Subgroup.mem_subgroupOf.mp hâ
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 (â : G) hâK)
  have hmem : (⟨z, hzH⟩ : ↥H) ∈ (V.subgroupOf H : Subgroup ↥H) ⊓
      Subgroup.centralizer ((kGenIn V H).subgroupOf H : Set ↥H) := ⟨hzV', hzC'⟩
  rw [hkey] at hmem
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)

theorem conjSubgroup_kGenIn_le_centralizer (h : Hyp83 V H T) {x : G} (hx : x ∈ H)
    (hxK : x ∉ Subgroup.normalizer (kGenIn V H : Set G)) :
    conjSubgroup (kGenIn V H) x ≤ Subgroup.centralizer (kGenIn V H : Set G) := by
  have h' := AmbientH.hyp83 h
  have hOmH' : ∀ W ∈ omegaSet (V.subgroupOf H) (⊤ : Subgroup ↥H)
      (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)), W ≤ ⊤ :=
    fun _ _ => le_top
  have hKH : kGenIn V H ≤ H := kGenIn_le_H h.le_H
  have hxn : (⟨x, hx⟩ : ↥H) ∉
      Subgroup.normalizer ((kGenIn V H).subgroupOf H : Set ↥H) := by
    rw [AmbientH.normalizer_eq hKH]
    intro hmem
    exact hxK (Subgroup.mem_subgroupOf.mp hmem)
  have hne : conjSubgroup ((kGenIn V H).subgroupOf H) (⟨x, hx⟩ : ↥H) ≠
      conjSubgroup ((kGenIn V H).subgroupOf H) 1 := by
    intro heq
    exact hxn (by
      simpa using (conjSubgroup_eq_conjSubgroup_iff_mul_inv_mem.mp heq))
  have hne' : conjSubgroup (kGen (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H))
      (⟨x, hx⟩ : ↥H) ≠
      conjSubgroup (kGen (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)) 1 := by
    rw [AmbientH.kGen_eq h]
    exact hne
  have hcomm := h'.commutator_conjSubgroup_kGen_eq_bot hOmH'
    (Subgroup.mem_top (⟨x, hx⟩ : ↥H)) (Subgroup.mem_top 1) hne'
  rw [AmbientH.kGen_eq h, conjSubgroup_one] at hcomm
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hwH : w ∈ H := conjSubgroup_le_of_le hKH hx hw
  have haH : a ∈ H := hKH ha
  have hwK' : (⟨w, hwH⟩ : ↥H) ∈
      conjSubgroup ((kGenIn V H).subgroupOf H) (⟨x, hx⟩ : ↥H) := by
    rw [mem_conjSubgroup_iff]
    exact Subgroup.mem_subgroupOf.mpr (mem_conjSubgroup_iff.mp hw)
  have haK' : (⟨a, haH⟩ : ↥H) ∈ (kGenIn V H).subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr ha
  have hcomm' := Subgroup.mem_centralizer_iff.mp (hle hwK') (⟨a, haH⟩ : ↥H) haK'
  exact congrArg Subtype.val hcomm'

theorem coe_inf_normalizer_kGenIn (h : Hyp83 V H T) :
    ((H ⊓ Subgroup.normalizer (kGenIn V H : Set G) : Subgroup G) : Set G) =
      (kGenIn V H : Set G) * ((H ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G) := by
  have h' := AmbientH.hyp83 h
  have hOmH' : ∀ W ∈ omegaSet (V.subgroupOf H) (⊤ : Subgroup ↥H)
      (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)), W ≤ ⊤ :=
    fun _ _ => le_top
  have hKH : kGenIn V H ≤ H := kGenIn_le_H h.le_H
  have key := h'.coe_inf_normalizer_kGen hOmH'
  rw [AmbientH.kGen_eq h, top_inf_eq, AmbientH.normalizer_eq hKH, top_inf_eq,
    AmbientH.normalizer_eq h.le_H] at key
  ext x
  constructor
  · intro hx
    have hxH : x ∈ H := hx.1
    have hxK : x ∈ Subgroup.normalizer (kGenIn V H : Set G) := hx.2
    have hx' : (⟨x, hxH⟩ : ↥H) ∈
        ((Subgroup.normalizer (kGenIn V H : Set G)).subgroupOf H : Set ↥H) :=
      Subgroup.mem_subgroupOf.mpr hxK
    have hmem := key ▸ hx'
    rw [Set.mem_mul] at hmem
    obtain ⟨â, hâ, mH, hmH, hâm⟩ := hmem
    refine Set.mem_mul.mpr ⟨(â : G), Subgroup.mem_subgroupOf.mp hâ, (mH : G),
      ⟨mH.2, Subgroup.mem_subgroupOf.mp hmH⟩, ?_⟩
    exact congrArg Subtype.val hâm
  · intro hx
    rw [Set.mem_mul] at hx
    obtain ⟨a, ha, m, hm, rfl⟩ := hx
    exact ⟨H.mul_mem (hKH ha) hm.1,
      Subgroup.mul_mem _ (Subgroup.le_normalizer ha)
        (inf_normalizer_le_normalizer_kGenIn V H ⟨hm.1, hm.2⟩)⟩

end Hyp83

end CFSG.LocalAnalysis.WeakClosure81

end
