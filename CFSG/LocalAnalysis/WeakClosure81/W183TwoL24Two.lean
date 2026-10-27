module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoL24Rig
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
import CFSG.LocalAnalysis.WeakClosure81.W183Abs3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsU3)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem w183tp_two_sylow {Y T L₁ L₂ : Subgroup (LGL 2 V)} (hT : IsSylowIn 2 T Y)
    (htwo : Br2TwoComp Y T L₁ L₂) :
    IsSylowIn 2 (T ⊓ L₁) L₁ ∧ IsSylowIn 2 (T ⊓ L₂) L₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (LGL 2 V) :=
    Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
      (fun e f h => LinearEquiv.ext (congrFun h))
  have hsupY : L₁ ⊔ L₂ ≤ Y := sup_le htwo.le₁ htwo.le₂
  have hN : ((L₁ ⊔ L₂).subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hsupY]
    intro y hy
    refine (Subgroup.mem_normalizer_iff_map_conj_eq (H := L₁ ⊔ L₂) (g := y)).mpr ?_
    show Subgroup.map (MulAut.conj y).toMonoidHom (L₁ ⊔ L₂) = L₁ ⊔ L₂
    rcases htwo.perm y hy with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [Subgroup.map_sup,
        show Subgroup.map (MulAut.conj y).toMonoidHom L₁ = L₁ from by simpa [cj] using h₁,
        show Subgroup.map (MulAut.conj y).toMonoidHom L₂ = L₂ from by simpa [cj] using h₂]
    · rw [Subgroup.map_sup,
        show Subgroup.map (MulAut.conj y).toMonoidHom L₁ = L₂ from by simpa [cj] using h₁,
        show Subgroup.map (MulAut.conj y).toMonoidHom L₂ = L₁ from by simpa [cj] using h₂,
        sup_comm]
  have hP : IsSylowIn 2 (T ⊓ (L₁ ⊔ L₂)) (L₁ ⊔ L₂) := hT.inf_normal hsupY hN
  have hcent₂ : L₂ ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact htwo.comm a ha b hb
  have hcent₁ : L₁ ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (htwo.comm a ha b hb).symm
  have hL₁n : (L₁.subgroupOf (L₁ ⊔ L₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer
        (hcent₂.trans (Subgroup.centralizer_le_normalizer (L₁ : Set (LGL 2 V)))))
  have hL₂n : (L₂.subgroupOf (L₁ ⊔ L₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le (hcent₁.trans (Subgroup.centralizer_le_normalizer (L₂ : Set (LGL 2 V))))
        Subgroup.le_normalizer)
  constructor
  · have h' := hP.inf_normal (N := L₁) le_sup_left hL₁n
    have he : T ⊓ (L₁ ⊔ L₂) ⊓ L₁ = T ⊓ L₁ := by
      have h₁' : (L₁ ⊔ L₂) ⊓ L₁ = L₁ := inf_eq_right.2 le_sup_left
      rw [inf_assoc, h₁']
    rwa [he] at h'
  · have h' := hP.inf_normal (N := L₂) le_sup_right hL₂n
    have he : T ⊓ (L₁ ⊔ L₂) ⊓ L₂ = T ⊓ L₂ := by
      have h₂' : (L₁ ⊔ L₂) ⊓ L₂ = L₂ := inf_eq_right.2 le_sup_right
      rw [inf_assoc, h₂']
    rwa [he] at h'

theorem w183tp_two_T_normalizes {Y T L₁ L₂ : Subgroup (LGL 2 V)} (hT : IsSylowIn 2 T Y)
    (htwo : Br2TwoComp Y T L₁ L₂) :
    T ≤ Subgroup.normalizer ((T ⊓ L₁ ⊔ T ⊓ L₂ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := by
  intro t ht
  refine (Subgroup.mem_normalizer_iff_map_conj_eq
    (H := T ⊓ L₁ ⊔ T ⊓ L₂) (g := t)).mpr ?_
  show Subgroup.map (MulAut.conj t).toMonoidHom (T ⊓ L₁ ⊔ T ⊓ L₂) = T ⊓ L₁ ⊔ T ⊓ L₂
  have hTmap : Subgroup.map (MulAut.conj t).toMonoidHom T = T :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := T) (g := t)).mp (Subgroup.le_normalizer ht)
  have hmap : ∀ M N : Subgroup (LGL 2 V),
      Subgroup.map (MulAut.conj t).toMonoidHom M = N →
      Subgroup.map (MulAut.conj t).toMonoidHom (T ⊓ M) = T ⊓ N := by
    intro M N hMN
    rw [Subgroup.map_inf T M (MulAut.conj t).toMonoidHom (MulAut.conj t).injective, hMN, hTmap]
  rcases htwo.perm t (hT.le ht) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [Subgroup.map_sup, hmap L₁ L₁ (by simpa [cj] using h₁),
      hmap L₂ L₂ (by simpa [cj] using h₂)]
  · rw [Subgroup.map_sup, hmap L₁ L₂ (by simpa [cj] using h₁),
      hmap L₂ L₁ (by simpa [cj] using h₂), sup_comm]

theorem w183tp_two_normalizer_ne {Y T L₁ L₂ : Subgroup (LGL 2 V)} (hT : IsSylowIn 2 T Y)
    (htwo : Br2TwoComp Y T L₁ L₂) (hshape₁ : IsL2 ↥L₁ 2 ∨ IsU3 ↥L₁ 2) :
    Y ⊓ Subgroup.normalizer ((T ⊓ L₁ ⊔ T ⊓ L₂ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) ≠ Y := by
  intro h
  haveI : Finite (LGL 2 V) :=
    Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
      (fun e f h => LinearEquiv.ext (congrFun h))
  haveI : IsSimpleGroup ↥L₁ := htwo.simple₁
  obtain ⟨hQ₁, -⟩ := w183tp_two_sylow hT htwo
  have hQn := (w183tp_sylow_not_normal htwo.simple₁ htwo.nonab₁ hshape₁ hQ₁).2
  have hYle : Y ≤ Subgroup.normalizer
      ((T ⊓ L₁ ⊔ T ⊓ L₂ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := h ▸ inf_le_right
  have hQ₁n : T ⊓ L₁ ≤ Subgroup.normalizer ((T ⊓ L₂ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (htwo.comm a (Subgroup.mem_inf.mp ha).2 b (Subgroup.mem_inf.mp hb).2).symm
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (T ⊓ L₁) (T ⊓ L₂) hQ₁n
  have hRL : (T ⊓ L₁ ⊔ T ⊓ L₂ : Subgroup (LGL 2 V)) ⊓ L₁ = T ⊓ L₁ := by
    refine le_antisymm ?_ (le_inf le_sup_left inf_le_right)
    intro x hx
    obtain ⟨hxR, hxL⟩ := Subgroup.mem_inf.mp hx
    change x ∈ ((T ⊓ L₁ ⊔ T ⊓ L₂ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) at hxR
    rw [hcoe, Set.mem_mul] at hxR
    obtain ⟨a, ha, b, hb, rfl⟩ := hxR
    have hbL₁ : b ∈ L₁ := by
      have hb' : b = a⁻¹ * (a * b) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      rw [hb']
      exact L₁.mul_mem (L₁.inv_mem ha.2) hxL
    have hbBot : b ∈ (⊥ : Subgroup (LGL 2 V)) := by
      rw [← w183_inf_eq_bot_of_commute (L₁ := L₁) (L₂ := L₂) htwo.nonab₁ htwo.comm]
      exact ⟨hbL₁, hb.2⟩
    rw [Subgroup.mem_bot.mp hbBot, mul_one]
    exact ha
  apply hQn
  intro l hl q hq
  have hlN : l ∈ Subgroup.normalizer
      ((T ⊓ L₁ ⊔ T ⊓ L₂ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := hYle (htwo.le₁ hl)
  have hmR : l * q * l⁻¹ ∈ T ⊓ L₁ ⊔ T ⊓ L₂ :=
    (Subgroup.mem_normalizer_iff.mp hlN q).mp (Subgroup.mem_sup_left hq)
  have hmL : l * q * l⁻¹ ∈ L₁ :=
    L₁.mul_mem (L₁.mul_mem hl (Subgroup.mem_inf.mp hq).2) (L₁.inv_mem hl)
  exact hRL ▸ (show l * q * l⁻¹ ∈ (T ⊓ L₁ ⊔ T ⊓ L₂) ⊓ L₁ from ⟨hmR, hmL⟩)

theorem w183tp_two_borel_mem {Y T L₁ L₂ : Subgroup (LGL 2 V)} (htwo : Br2TwoComp Y T L₁ L₂)
    {b : LGL 2 V} (hb : b ∈ L₁ ⊓ Subgroup.normalizer ((T ⊓ L₁ : Subgroup (LGL 2 V)) : Set _)) :
    b ∈ Subgroup.normalizer ((T ⊓ L₁ ⊔ T ⊓ L₂ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := by
  refine (Subgroup.mem_normalizer_iff_map_conj_eq
    (H := T ⊓ L₁ ⊔ T ⊓ L₂) (g := b)).mpr ?_
  show Subgroup.map (MulAut.conj b).toMonoidHom (T ⊓ L₁ ⊔ T ⊓ L₂) = T ⊓ L₁ ⊔ T ⊓ L₂
  have hQ₁ : Subgroup.map (MulAut.conj b).toMonoidHom (T ⊓ L₁) = T ⊓ L₁ :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := T ⊓ L₁) (g := b)).mp hb.2
  have hbC : b ∈ Subgroup.centralizer ((T ⊓ L₂ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (htwo.comm b hb.1 q (Subgroup.mem_inf.mp hq).2).symm
  have hQ₂ : Subgroup.map (MulAut.conj b).toMonoidHom (T ⊓ L₂) = T ⊓ L₂ :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := T ⊓ L₂) (g := b)).mp
      (Subgroup.centralizer_le_normalizer _ hbC)
  rw [Subgroup.map_sup, hQ₁, hQ₂]

theorem w183tp_two_borel_mem' {Y T L₁ L₂ : Subgroup (LGL 2 V)} (htwo : Br2TwoComp Y T L₁ L₂)
    {b : LGL 2 V} (hb : b ∈ L₂ ⊓ Subgroup.normalizer ((T ⊓ L₂ : Subgroup (LGL 2 V)) : Set _)) :
    b ∈ Subgroup.normalizer ((T ⊓ L₁ ⊔ T ⊓ L₂ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := by
  refine (Subgroup.mem_normalizer_iff_map_conj_eq
    (H := T ⊓ L₁ ⊔ T ⊓ L₂) (g := b)).mpr ?_
  show Subgroup.map (MulAut.conj b).toMonoidHom (T ⊓ L₁ ⊔ T ⊓ L₂) = T ⊓ L₁ ⊔ T ⊓ L₂
  have hQ₂ : Subgroup.map (MulAut.conj b).toMonoidHom (T ⊓ L₂) = T ⊓ L₂ :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := T ⊓ L₂) (g := b)).mp hb.2
  have hbC : b ∈ Subgroup.centralizer ((T ⊓ L₁ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact htwo.comm q (Subgroup.mem_inf.mp hq).2 b hb.1
  have hQ₁ : Subgroup.map (MulAut.conj b).toMonoidHom (T ⊓ L₁) = T ⊓ L₁ :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := T ⊓ L₁) (g := b)).mp
      (Subgroup.centralizer_le_normalizer _ hbC)
  rw [Subgroup.map_sup, hQ₁, hQ₂]

theorem w183tp_two_no_swap {Y T L₁ L₂ : Subgroup (LGL 2 V)} (hT : IsSylowIn 2 T Y)
    (htwo : Br2TwoComp Y T L₁ L₂) (hshape₁ : IsL2 ↥L₁ 2 ∨ IsU3 ↥L₁ 2) {d : LGL 2 V} (hdY : d ∈ Y)
    (hc : ∀ b ∈ L₁ ⊓ Subgroup.normalizer ((T ⊓ L₁ : Subgroup (LGL 2 V)) : Set _),
      d * b = b * d) :
    d ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) ∧
      d ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) := by
  haveI : Finite (LGL 2 V) :=
    Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
      (fun e f h => LinearEquiv.ext (congrFun h))
  haveI : IsSimpleGroup ↥L₁ := htwo.simple₁
  obtain ⟨hQ₁, -⟩ := w183tp_two_sylow hT htwo
  have hQne : T ⊓ L₁ ≠ ⊥ := (w183tp_sylow_not_normal htwo.simple₁ htwo.nonab₁ hshape₁ hQ₁).1
  obtain ⟨b, hbH, hb1⟩ := (Subgroup.nontrivial_iff_exists_ne_one (T ⊓ L₁)).mp
    ((Subgroup.nontrivial_iff_ne_bot (T ⊓ L₁)).mpr hQne)
  have hbB : b ∈ L₁ ⊓ Subgroup.normalizer ((T ⊓ L₁ : Subgroup (LGL 2 V)) : Set _) :=
    ⟨hbH.2, Subgroup.le_normalizer hbH⟩
  have hcb : d * b = b * d := hc _ hbB
  rcases htwo.perm d hdY with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨(Subgroup.mem_normalizer_iff_map_conj_eq (H := L₁) (g := d)).mpr
        (by simpa [cj] using h₁),
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := L₂) (g := d)).mpr
        (by simpa [cj] using h₂)⟩
  · exfalso
    have hdeq : d * b * d⁻¹ = b := by
      rw [hcb, mul_assoc, mul_inv_cancel, mul_one]
    have hmem : d * b * d⁻¹ ∈ L₁.map (MulAut.conj d).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨b, hbH.2, by simp [MulAut.conj_apply]⟩
    have hbL₂ : b ∈ L₂ := by
      have h1' : L₁.map (MulAut.conj d).toMonoidHom = L₂ := by simpa [cj] using h₁
      exact hdeq ▸ (h1' ▸ hmem)
    have hbot : b ∈ (⊥ : Subgroup (LGL 2 V)) := by
      rw [← w183_inf_eq_bot_of_commute (L₁ := L₁) (L₂ := L₂) htwo.nonab₁ htwo.comm]
      exact ⟨hbH.2, hbL₂⟩
    exact hb1 (Subgroup.mem_bot.mp hbot)

section Certified


theorem w183tp_false_two {Y T L₁ L₂ : Subgroup (LGL 2 V)} {d : LGL 2 V} (hT : IsSylowIn 2 T Y)
    (htwo : Br2TwoComp Y T L₁ L₂) (hshape₁ : IsL2 ↥L₁ 2 ∨ IsU3 ↥L₁ 2)
    (hshape₂ : IsL2 ↥L₂ 2 ∨ IsU3 ↥L₂ 2) (hdY : d ∈ Y) (hd1 : d ≠ 1) (hd2 : d * d = 1)
    (hX : ∀ X : Subgroup (LGL 2 V), X ≤ Y → T ≤ X → X ≠ Y → ∀ x ∈ X, x * d = d * x) :
    False := by
  haveI : Finite (LGL 2 V) :=
    Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
      (fun e f h => LinearEquiv.ext (congrFun h))
  obtain ⟨hQ₁, hQ₂⟩ := w183tp_two_sylow hT htwo
  have hXY : Y ⊓ Subgroup.normalizer
      ((T ⊓ L₁ ⊔ T ⊓ L₂ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) ≤ Y := inf_le_left
  have hTX : T ≤ Y ⊓ Subgroup.normalizer
      ((T ⊓ L₁ ⊔ T ⊓ L₂ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) :=
    le_inf hT.le (w183tp_two_T_normalizes hT htwo)
  have hXne := w183tp_two_normalizer_ne hT htwo hshape₁
  have hc₁ : ∀ b ∈ L₁ ⊓ Subgroup.normalizer ((T ⊓ L₁ : Subgroup (LGL 2 V)) : Set _),
      d * b = b * d := fun b hb =>
    (hX _ hXY hTX hXne b ⟨htwo.le₁ hb.1, w183tp_two_borel_mem htwo hb⟩).symm
  have hc₂ : ∀ b ∈ L₂ ⊓ Subgroup.normalizer ((T ⊓ L₂ : Subgroup (LGL 2 V)) : Set _),
      d * b = b * d := fun b hb =>
    (hX _ hXY hTX hXne b ⟨htwo.le₂ hb.1, w183tp_two_borel_mem' htwo hb⟩).symm
  obtain ⟨hdN₁, hdN₂⟩ := w183tp_two_no_swap hT htwo hshape₁ hdY hc₁
  have hr₁ := w183tp_borel_rigid htwo.simple₁ htwo.nonab₁ hshape₁ hQ₁ hdN₁ hd2 hc₁
  have hr₂ := w183tp_borel_rigid htwo.simple₂ htwo.nonab₂ hshape₂ hQ₂ hdN₂ hd2 hc₂
  exact hd1 (htwo.cent d hdY (fun l hl => (Subgroup.mem_centralizer_iff.mp hr₁ l hl).symm)
    (fun l hl => (Subgroup.mem_centralizer_iff.mp hr₂ l hl).symm))

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
