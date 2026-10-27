module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4B

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

abbrev S134Conj (t : MulAut W) (K : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  K.map (MulAut.conj t).toMonoidHom

structure S134Frame (Y K : Subgroup (MulAut W)) (t : MulAut W) : Prop where
  exp : ∀ w : W, w ^ 2 = 1
  o2 : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥
  comp : IsComponentOf K Y
  mem : t ∈ Y
  ord : orderOf t = 2
  rk_le : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3
  rk_eq : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3
  move : S134Conj t K ≠ K
  l3 : UC22.IsL3 ↥K 1
  nt : ¬ ∀ a ∈ K, ∀ u ∈ commSub ⊤ (Subgroup.zpowers t), (a * (t * a * t⁻¹)) u = u

private def f4a_rel (U : Subgroup W) (x y : W) : Prop := x * y⁻¹ ∈ U

omit [Finite W] in
private theorem f4a_rel_symm {U : Subgroup W} {x y : W} (h : f4a_rel U x y) :
    f4a_rel U y x := by
  simpa [f4a_rel, mul_inv_rev] using U.inv_mem h

omit [Finite W] in
private theorem f4a_rel_trans {U : Subgroup W} {x y z : W} (h1 : f4a_rel U x y)
    (h2 : f4a_rel U y z) : f4a_rel U x z := by
  change x * z⁻¹ ∈ U
  have h : x * z⁻¹ = (x * y⁻¹) * (y * z⁻¹) := by group
  rw [h]
  exact U.mul_mem h1 h2

omit [Finite W] in
private theorem f4a_rel_apply {U : Subgroup W} {g : MulAut W} (hg : ∀ u ∈ U, g u ∈ U)
    {x y : W} (h : f4a_rel U x y) : f4a_rel U (g x) (g y) := by
  change g x * (g y)⁻¹ ∈ U
  rw [← map_inv, ← map_mul]
  exact hg _ h

omit [Finite W] in
private theorem f4a_rel_conj_apply {K : Subgroup (MulAut W)} {U : Subgroup W}
    (hU : StableUnder K U) {t : MulAut W} (htU : ∀ w : W, t w * w⁻¹ ∈ U)
    (htUinv : ∀ w : W, t⁻¹ w * w⁻¹ ∈ U) {b : MulAut W} (hb : b ∈ K) (x : W) :
    f4a_rel U ((t * b * t⁻¹) x) (b x) := by
  change ((t * b * t⁻¹) x) * (b x)⁻¹ ∈ U
  have h1 : t (b (t⁻¹ x)) * (b (t⁻¹ x))⁻¹ ∈ U := htU _
  have h2 : b (t⁻¹ x) * (b x)⁻¹ ∈ U := by
    rw [← map_inv, ← map_mul]
    exact hU b hb _ (htUinv x)
  have heq : ((t * b * t⁻¹) x) * (b x)⁻¹ =
      (t (b (t⁻¹ x)) * (b (t⁻¹ x))⁻¹) * (b (t⁻¹ x) * (b x)⁻¹) := by
    simp only [MulAut.mul_apply]
    group
  rw [heq]
  exact U.mul_mem h1 h2

omit [Finite W] in
theorem S134Frame.mul_self {Y K : Subgroup (MulAut W)} {t : MulAut W} (h : S134Frame Y K t) :
    t * t = 1 := by
  have h2 := pow_orderOf_eq_one t
  rw [h.ord] at h2
  simpa [pow_two] using h2

omit [Finite W] in
theorem S134Frame.isComponent' {Y K : Subgroup (MulAut W)} {t : MulAut W}
    (h : S134Frame Y K t) : IsComponentOf (S134Conj t K) Y :=
  CFSG.LargeExtraspecial.S5.isComponentOf_map_conj h.comp h.mem

theorem S134Frame.comm {Y K : Subgroup (MulAut W)} {t : MulAut W} (h : S134Frame Y K t) :
    ∀ a ∈ K, ∀ b ∈ S134Conj t K, a * b = b * a :=
  fun _ ha _ hb =>
    CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne h.comp h.isComponent' (Ne.symm h.move)
      ha hb

theorem S134Frame.inf_eq_bot {Y K : Subgroup (MulAut W)} {t : MulAut W} (h : S134Frame Y K t) :
    K ⊓ S134Conj t K = ⊥ := by
  have : IsSimpleGroup ↥K := s134b_isSimpleGroup_of_isL3 h.l3
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (s134b_perfect_of_isL3 h.l3)
  have hnc : ¬ IsMulCommutative ↥K := Group.IsPerfect.not_isMulCommutative (G := ↥K)
  have hcenter : Subgroup.center ↥K = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨hyK, hyK'⟩ := hy
  have hz : (⟨y, hyK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h.comm g.1 g.2 y hyK')
  rw [hcenter, Subgroup.mem_bot] at hz
  exact Subtype.ext_iff.mp hz

omit [Finite W] in
theorem S134Frame.perfect {Y K : Subgroup (MulAut W)} {t : MulAut W} (h : S134Frame Y K t) :
    ⁅K, K⁆ = K :=
  s134b_perfect_of_isL3 h.l3

omit [Finite W] in
theorem S134Frame.l3' {Y K : Subgroup (MulAut W)} {t : MulAut W} (h : S134Frame Y K t) :
    UC22.IsL3 ↥(S134Conj t K) 1 :=
  CFSG.Blueprint.LieModel.of_mulEquiv
    (Subgroup.equivMapOfInjective K (MulAut.conj t).toMonoidHom (MulAut.conj t).injective) h.l3

theorem S134Frame.seven_data {Y K : Subgroup (MulAut W)} {t : MulAut W} (h : S134Frame Y K t)
    {x : MulAut W} (hx : x ∈ K) (hx7 : orderOf x = 7) :
    t * x * t⁻¹ ∈ S134Conj t K ∧ orderOf (t * x * t⁻¹) = 7 ∧
      x * (t * x * t⁻¹) = (t * x * t⁻¹) * x ∧ t * (t * x * t⁻¹) * t⁻¹ = x ∧
      t * x * t⁻¹ ∉ Subgroup.zpowers x := by
  have hx'mem : t * x * t⁻¹ ∈ S134Conj t K := by
    rw [S134Conj]
    exact Subgroup.mem_map.mpr ⟨x, hx, by
      show (MulAut.conj t) x = t * x * t⁻¹
      rw [MulAut.conj_apply]⟩
  have hord : orderOf (t * x * t⁻¹) = 7 := by
    have ho := orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective x
    rw [hx7] at ho
    simpa [MulAut.conj_apply] using ho
  have hcomm : x * (t * x * t⁻¹) = (t * x * t⁻¹) * x := h.comm x hx (t * x * t⁻¹) hx'mem
  have hconj : t * (t * x * t⁻¹) * t⁻¹ = x := by
    have ht : t * t = 1 := h.mul_self
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
      _ = x := by rw [ht, htinv, ht]; simp
  have hnotmem : t * x * t⁻¹ ∉ Subgroup.zpowers x := by
    intro hmem
    have hxK : t * x * t⁻¹ ∈ K := (Subgroup.zpowers_le.mpr hx) hmem
    have hbot : t * x * t⁻¹ ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← h.inf_eq_bot]
      exact ⟨hxK, hx'mem⟩
    rw [Subgroup.mem_bot] at hbot
    have hx1 : x = 1 := by
      have hcongr := congrArg (fun g : MulAut W => t⁻¹ * g * t) hbot
      have hLeft : t⁻¹ * (t * x * t⁻¹) * t = x := by group
      rw [hLeft] at hcongr
      simpa using hcongr
    rw [hx1] at hx7
    simp at hx7
  exact ⟨hx'mem, hord, hcomm, hconj, hnotmem⟩

omit [Finite W] in
theorem s134b_commSub_le_of_t_trivial {K : Subgroup (MulAut W)} {t : MulAut W} (ht : t * t = 1)
    (hKK' : ∀ a ∈ K, ∀ b ∈ S134Conj t K, a * b = b * a) (hK : ⁅K, K⁆ = K) {U : Subgroup W}
    (hU : StableUnder K U) (htU : commSub ⊤ (Subgroup.zpowers t) ≤ U) : commSub ⊤ K ≤ U := by
  have _ht : t * t = 1 := ht
  have htU' : ∀ w : W, t w * w⁻¹ ∈ U := fun w =>
    htU (Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, w, Subgroup.mem_top w, rfl⟩)
  have htUinv' : ∀ w : W, t⁻¹ w * w⁻¹ ∈ U := fun w =>
    htU (Subgroup.subset_closure
      ⟨t⁻¹, (Subgroup.zpowers t).inv_mem (Subgroup.mem_zpowers t), w, Subgroup.mem_top w, rfl⟩)
  have hKN : K ≤ centSec ⊤ U := by
    rw [← hK, Subgroup.commutator_def, Subgroup.closure_le]
    rintro g ⟨g1, hg1, g2, hg2, rfl⟩
    have hb' : t * g2 * t⁻¹ ∈ S134Conj t K := by
      rw [S134Conj]
      exact Subgroup.mem_map.mpr ⟨g2, hg2, by
        show (MulAut.conj t) g2 = t * g2 * t⁻¹
        rw [MulAut.conj_apply]⟩
    have hcomm : g1 * (t * g2 * t⁻¹) = (t * g2 * t⁻¹) * g1 := hKK' g1 hg1 _ hb'
    have hc' : g1 * (t * g2 * t⁻¹) * g1⁻¹ * (t * g2 * t⁻¹)⁻¹ = 1 := by
      rw [hcomm]
      group
    refine mem_centSec.mpr ⟨mem_stabSub.mpr fun u => by simp, ?_⟩
    intro w _
    show f4a_rel U (⁅g1, g2⁆ w) w
    have hb'rel : ∀ x : W, f4a_rel U ((t * g2 * t⁻¹) x) (g2 x) :=
      fun x => f4a_rel_conj_apply hU htU' htUinv' hg2 x
    have hb'invrel : ∀ x : W, f4a_rel U ((t * g2 * t⁻¹)⁻¹ x) (g2⁻¹ x) := by
      intro x
      have h := f4a_rel_conj_apply hU htU' htUinv' (K.inv_mem hg2) x
      have heq : (t * g2 * t⁻¹)⁻¹ = t * g2⁻¹ * t⁻¹ := by group
      rw [heq]
      exact h
    have h1 : f4a_rel U (g2⁻¹ w) ((t * g2 * t⁻¹)⁻¹ w) :=
      f4a_rel_symm (hb'invrel w)
    have h2 : f4a_rel U (g1⁻¹ (g2⁻¹ w)) (g1⁻¹ ((t * g2 * t⁻¹)⁻¹ w)) :=
      f4a_rel_apply (hU g1⁻¹ (K.inv_mem hg1)) h1
    have h3 : f4a_rel U (g2 (g1⁻¹ (g2⁻¹ w))) (g2 (g1⁻¹ ((t * g2 * t⁻¹)⁻¹ w))) :=
      f4a_rel_apply (hU g2 hg2) h2
    have h4 : f4a_rel U (g2 (g1⁻¹ ((t * g2 * t⁻¹)⁻¹ w)))
        ((t * g2 * t⁻¹) (g1⁻¹ ((t * g2 * t⁻¹)⁻¹ w))) :=
      f4a_rel_symm (hb'rel (g1⁻¹ ((t * g2 * t⁻¹)⁻¹ w)))
    have h5 := f4a_rel_trans h3 h4
    have h6 : f4a_rel U (g1 (g2 (g1⁻¹ (g2⁻¹ w))))
        (g1 ((t * g2 * t⁻¹) (g1⁻¹ ((t * g2 * t⁻¹)⁻¹ w)))) :=
      f4a_rel_apply (hU g1 hg1) h5
    have h7 : g1 ((t * g2 * t⁻¹) (g1⁻¹ ((t * g2 * t⁻¹)⁻¹ w))) = w := by
      have hw' : (g1 * (t * g2 * t⁻¹) * g1⁻¹ * (t * g2 * t⁻¹)⁻¹) w = w := by
        rw [hc']
        rfl
      simpa only [MulAut.mul_apply] using hw'
    rw [h7] at h6
    rw [commutatorElement_def]
    simpa only [MulAut.mul_apply] using h6
  rw [commSub, Subgroup.closure_le]
  rintro c ⟨x, hx, w, hw, rfl⟩
  exact (mem_centSec.mp (hKN hx)).2 w hw

omit [Finite W] in
theorem s134b_commSub_le_of_normalClosure {K : Subgroup (MulAut W)} (hK : IsSimpleGroup ↥K)
    {x : MulAut W} (hx : x ∈ K) (hx1 : x ≠ 1) {U : Subgroup W} (hU : StableUnder K U)
    (hxU : commSub ⊤ (Subgroup.zpowers x) ≤ U) : commSub ⊤ K ≤ U := by
  have hxU' : ∀ w : W, x w * w⁻¹ ∈ U := fun w =>
    hxU (Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, w, Subgroup.mem_top w, rfl⟩)
  have hxN : x ∈ K ⊓ centSec ⊤ U := by
    rw [Subgroup.mem_inf]
    exact ⟨hx, mem_centSec.mpr ⟨mem_stabSub.mpr fun u => by simp, fun w _ => hxU' w⟩⟩
  have hnormal : ((K ⊓ centSec ⊤ U).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    obtain ⟨hhK, hhC⟩ := hh
    refine ⟨K.mul_mem (K.mul_mem hk hhK) (K.inv_mem hk), ?_⟩
    exact centSec_conj hhC (mem_stabSub.mpr fun u => by simp) (fun z hz => hU k hk z hz)
  have htop : (K ⊓ centSec ⊤ U).subgroupOf K = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ centSec ⊤ U).subgroupOf K) with
      hbot | htop
    · exfalso
      have hxmem : (⟨x, hx⟩ : ↥K) ∈ (K ⊓ centSec ⊤ U).subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr hxN
      rw [hbot, Subgroup.mem_bot] at hxmem
      exact hx1 (Subtype.ext_iff.mp hxmem)
    · exact htop
  have hKN : K ≤ K ⊓ centSec ⊤ U := Subgroup.subgroupOf_eq_top.mp htop
  rw [commSub, Subgroup.closure_le]
  rintro c ⟨y, hy, w, hw, rfl⟩
  exact (mem_centSec.mp (hKN hy).2).2 w hw

omit [Finite W] in
theorem s134b_le_fixV_of_normalClosure {K : Subgroup (MulAut W)} (hK : IsSimpleGroup ↥K)
    {x : MulAut W} (hx : x ∈ K) (hx1 : x ≠ 1) {B : Subgroup W} (hB : StableUnder K B)
    (hxB : B ≤ fixV (Subgroup.zpowers x)) : B ≤ fixV K := by
  have hxN : x ∈ K ⊓ centSub B := by
    rw [Subgroup.mem_inf]
    exact ⟨hx, mem_centSub.mpr fun b hb =>
      (mem_fixV.mp (hxB hb)) x (Subgroup.mem_zpowers x)⟩
  have hnormal : ((K ⊓ centSub B).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    obtain ⟨hhK, hhC⟩ := hh
    refine ⟨K.mul_mem (K.mul_mem hk hhK) (K.inv_mem hk), ?_⟩
    exact mem_centSub.mpr fun b hb => by
      have hb' : k⁻¹ b ∈ B := hB k⁻¹ (K.inv_mem hk) b hb
      calc (k * h * k⁻¹) b = k (h (k⁻¹ b)) := by simp only [MulAut.mul_apply]
        _ = k (k⁻¹ b) := by rw [mem_centSub.mp hhC (k⁻¹ b) hb']
        _ = b := by simp
  have htop : (K ⊓ centSub B).subgroupOf K = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ centSub B).subgroupOf K) with
      hbot | htop
    · exfalso
      have hxmem : (⟨x, hx⟩ : ↥K) ∈ (K ⊓ centSub B).subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr hxN
      rw [hbot, Subgroup.mem_bot] at hxmem
      exact hx1 (Subtype.ext_iff.mp hxmem)
    · exact htop
  have hKN : K ≤ K ⊓ centSub B := Subgroup.subgroupOf_eq_top.mp htop
  intro b hb
  rw [mem_fixV]
  intro g hg
  exact (mem_centSub.mp (hKN hg).2) b hb

end CFSG.LocalAnalysis.WeakClosure81
