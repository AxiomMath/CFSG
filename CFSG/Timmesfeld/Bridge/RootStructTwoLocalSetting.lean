module

public import CFSG.Timmesfeld.Exceptional.KdStructure
public import CFSG.Timmesfeld.Bridge.RootSetsConn20
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.Timmesfeld.Bridge.RootStructWTIProps

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

structure TwoLocalSetting (G : Type*) [Group G] (D : Set G) : Prop where
  hyp : Hyp G D
  sing : ∀ d ∈ D, rootSet D d = {d}
  noLevi : Moufang.NoLevi D
  noPlane : Moufang.ExcNoPlane D

theorem mem_zpowers_iff_of_mul_self {G : Type*} [Group G] {x w : G} (hx : x * x = 1) :
    w ∈ Subgroup.zpowers x ↔ w = 1 ∨ w = x := by
  have hxx : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  constructor
  · intro hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, hxx, one_zpow]
    · right
      rw [zpow_add, zpow_mul, hxx, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem commute_of_mem_closure_pair {G : Type*} [Group G] {a d x y : G} (had : Commute a d)
    (hx : x ∈ Subgroup.closure ({a, d} : Set G)) (hy : y ∈ Subgroup.closure ({a, d} : Set G)) :
    Commute x y := by
  have h1 : Subgroup.closure ({a, d} : Set G) ≤ Subgroup.centralizer ({a, d} : Set G) := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
    exacts [rfl, had.symm.eq, had.eq, rfl]
  have h2 : Subgroup.closure ({a, d} : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 (h1 hy) z hz
  exact Subgroup.mem_centralizer_singleton_iff.1 (h2 hx)

namespace TwoLocalSetting

variable {G : Type*} [Group G] {D : Set G} (S : TwoLocalSetting G D)
include S

theorem root : IsRootInvolutionSet D := S.hyp.root

theorem conj_mem (g : G) {x : G} (hx : x ∈ D) : g * x * g⁻¹ ∈ D :=
  conj_mem_of_isClass S.hyp.isClass g hx

theorem noPolar : Moufang.NoPolar D := by
  have := S.hyp.finite
  exact S.noLevi.noPolar S.hyp.isClass S.hyp.root S.sing S.noPlane

theorem mul_mem_of_commute {x y : G} (hx : x ∈ D) (hy : y ∈ D) (hxy : Commute x y)
    (hne : x ≠ y) : x * y ∈ D :=
  S.noPolar x hx y hy hxy hne

theorem rootGroup_eq {d : G} (hd : d ∈ D) : rootGroup D d = Subgroup.closure {d} := by
  rw [rootGroup, S.sing d hd]

theorem line_eq {a d : G} (ha : a ∈ D) (hd : d ∈ D) :
    rootGroup D a ⊔ rootGroup D d = Subgroup.closure {a, d} := by
  rw [S.rootGroup_eq ha, S.rootGroup_eq hd, ← Subgroup.closure_union, Set.singleton_union]

theorem mem_line_iff {a d u : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hu : u ∈ D) :
    u ∈ rootGroup D a ⊔ rootGroup D d ↔ u = a ∨ u = d ∨ u = a * d := by
  have hD := S.root
  constructor
  · intro huT
    rw [S.rootGroup_eq ha, S.rootGroup_eq hd, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure] at huT
    have hcomm : ∀ p ∈ Subgroup.zpowers a, ∀ q ∈ Subgroup.zpowers d, p * q = q * p := by
      intro p hp q hq
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      exact (had.zpow_zpow i j).eq
    obtain ⟨p, hp, q, hq, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm huT
    rcases (mem_zpowers_iff_of_mul_self (hD.mul_self_eq_one ha)).1 hp with rfl | rfl <;>
      rcases (mem_zpowers_iff_of_mul_self (hD.mul_self_eq_one hd)).1 hq with rfl | rfl
    · have h1 : (1 : G) ∈ D := by simpa using hu
      exact absurd rfl (hD.ne_one h1)
    · exact Or.inr (Or.inl (one_mul q))
    · exact Or.inl (mul_one p)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact Subgroup.mem_sup_left (rootSet_subset_rootGroup D u (mem_rootSet_self ha))
    · exact Subgroup.mem_sup_right (rootSet_subset_rootGroup D u (mem_rootSet_self hd))
    · exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a (mem_rootSet_self ha)))
        (Subgroup.mem_sup_right (rootSet_subset_rootGroup D d (mem_rootSet_self hd)))

theorem commute_of_mem_line {a d x y : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hx : x ∈ rootGroup D a ⊔ rootGroup D d) (hy : y ∈ rootGroup D a ⊔ rootGroup D d) :
    Commute x y := by
  rw [S.line_eq ha hd] at hx hy
  exact commute_of_mem_closure_pair had hx hy

theorem cases {a e f : G} (ha : a ∈ D) (he : e ∈ D) (hf : f ∈ D) (hae : Commute a e)
    (haf : Commute a f) (hea : e ≠ a) (hfa : f ≠ a) :
    f = e ∨ f = a * e ∨ (orderOf (e * f) = 4 ∧ (e * f) ^ 2 = a) :=
  S.noLevi.centralizer_cases S.root (fun g _ hx => S.conj_mem g hx) S.noPolar S.noPlane ha he
    hf hae haf hea hfa

theorem conj_eq_or_of_commute {w g v : G} (hw : w ∈ D) (hg : g ∈ D) (hv : v ∈ D)
    (hwg : Commute w g) (hwv : Commute w v) (hvw : v ≠ w) :
    g * v * g⁻¹ = v ∨ g * v * g⁻¹ = w * v := by
  have hD := S.root
  by_cases hgw : g = w
  · subst hgw
    left
    rw [hwv.eq, mul_inv_cancel_right]
  rcases S.cases hw hv hg hwv hwg hvw hgw with rfl | rfl | ⟨-, hsq⟩
  · left
    rw [mul_inv_cancel_right]
  · left
    have hc : Commute (w * v) v := hwv.mul_left (Commute.refl v)
    rw [hc.eq, mul_inv_cancel_right]
  · right
    have h1 : v * (g * v * g⁻¹) = w := by
      rw [hD.inv_eq hg, ← hsq, sq]
      group
    calc g * v * g⁻¹ = v * (v * (g * v * g⁻¹)) := by
          rw [← mul_assoc, hD.mul_self_eq_one hv, one_mul]
      _ = v * w := by rw [h1]
      _ = w * v := hwv.eq.symm

theorem lineTI {a d : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) : LineTI D a d := by
  have hD := S.root
  set T := rootGroup D a ⊔ rootGroup D d
  intro g hg u hu huT hguT v hv hvT
  obtain ⟨w, hw, hwT, hgw⟩ : ∃ w ∈ D, w ∈ T ∧ Commute g w := by
    by_cases hfix : g * u * g⁻¹ = u
    · exact ⟨u, hu, huT, mul_inv_eq_iff_eq_mul.1 hfix⟩
    · have hu' : g * u * g⁻¹ ∈ D := S.conj_mem g hu
      have hcomm := S.commute_of_mem_line ha hd had huT hguT
      refine ⟨u * (g * u * g⁻¹), S.mul_mem_of_commute hu hu' hcomm (Ne.symm hfix),
        T.mul_mem huT hguT, ?_⟩
      have hgg : g * (g * u * g⁻¹) * g⁻¹ = u := by
        rw [hD.inv_eq hg, ← mul_assoc, ← mul_assoc, hD.mul_self_eq_one hg, one_mul,
          mul_assoc, hD.mul_self_eq_one hg, mul_one]
      have key : g * (u * (g * u * g⁻¹)) * g⁻¹ = u * (g * u * g⁻¹) := by
        calc g * (u * (g * u * g⁻¹)) * g⁻¹ = (g * u * g⁻¹) * (g * (g * u * g⁻¹) * g⁻¹) := by
              group
          _ = (g * u * g⁻¹) * u := by rw [hgg]
          _ = u * (g * u * g⁻¹) := hcomm.eq.symm
      exact mul_inv_eq_iff_eq_mul.1 key
  by_cases hvw : v = w
  · subst hvw
    rw [hgw.eq, mul_inv_cancel_right]
    exact hvT
  rcases S.conj_eq_or_of_commute hw hg hv hgw.symm (S.commute_of_mem_line ha hd had hwT hvT)
    hvw with h | h
  · rw [h]
    exact hvT
  · rw [h]
    exact T.mul_mem hwT hvT

theorem rootClosure : RootClosure D := by
  intro d hd a ha b hb hab
  rw [S.sing d hd] at ha hb
  exact absurd (ha.trans hb.symm) hab

theorem specialClosure : SpecialClosure D := by
  intro d hd e he h4 b hb
  rw [S.sing e he] at hb
  rw [hb]
  exact mem_rootSet_self (S.root.sq_mem hd he h4)

theorem exists_collinear : ∃ a ∈ D, ∃ d ∈ D, Commute a d ∧ a * d ∈ D ∧ d ≠ a := by
  have hD := S.root
  obtain ⟨d₀, hd₀, e₀, he₀, h4⟩ := S.hyp.nondeg
  obtain ⟨hsqD, hcomm, -, hconj⟩ := sq_mem_of_orderOf_eq_four hD hd₀ he₀ h4
  have hmem : d₀ * (d₀ * e₀) ^ 2 ∈ D := by
    rw [← hconj]
    simpa [hD.inv_eq he₀] using S.conj_mem e₀ hd₀
  refine ⟨d₀, hd₀, (d₀ * e₀) ^ 2, hsqD, hcomm, hmem, fun h => hD.ne_one hmem ?_⟩
  rw [h, hD.mul_self_eq_one hd₀]

theorem map_line_eq_iff {a x g : G} (ha : a ∈ D) (hx : x ∈ D) (hax : Commute a x) (hxa : x ≠ a)
    (hg : Commute g a) :
    (rootGroup D a ⊔ rootGroup D x).map (MulAut.conj g).toMonoidHom =
        rootGroup D a ⊔ rootGroup D x ↔ g * x * g⁻¹ = x ∨ g * x * g⁻¹ = a * x := by
  have hD := S.root
  have hga : g * a * g⁻¹ = a := by rw [hg.eq, mul_inv_cancel_right]
  constructor
  · intro hmap
    have hmem : g * x * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D x := by
      rw [← hmap]
      exact ⟨x, Subgroup.mem_sup_right (rootSet_subset_rootGroup D x (mem_rootSet_self hx)),
        rfl⟩
    rcases (S.mem_line_iff ha hx hax (S.conj_mem g hx)).1 hmem with h | h | h
    · refine absurd ?_ hxa
      rw [← hga] at h
      simpa using h
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    rw [S.line_eq ha hx, MonoidHom.map_closure, Set.image_pair]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hga]
    rcases h with h | h
    · rw [h]
    · rw [h]
      refine le_antisymm (Subgroup.closure_le _ |>.2 ?_) (Subgroup.closure_le _ |>.2 ?_)
      · rintro _ (rfl | rfl)
        · exact Subgroup.subset_closure (Set.mem_insert _ _)
        · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
            (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      · rintro y (hy | hy)
        · rw [hy]
          exact Subgroup.subset_closure (Set.mem_insert _ _)
        · rw [hy]
          have hm : a * (a * x) ∈ Subgroup.closure ({a, a * x} : Set G) :=
            Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
              (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
          rwa [← mul_assoc, hD.mul_self_eq_one ha, one_mul] at hm

end TwoLocalSetting

theorem TwoLocalSetting.lineSetting {G : Type} [Group G] {D : Set G} (S : TwoLocalSetting G D) :
    LineSetting G D := by
  obtain ⟨a, ha, d, hd, had, hadD, hda⟩ := S.exists_collinear
  refine ⟨S.hyp, S.rootClosure, S.specialClosure, Moufang.collConnected_of_hyp tim75Thm31 S.hyp,
    a, ha, d, hd, had, hadD, ?_, S.lineTI ha hd had⟩
  rw [S.sing a ha]
  exact hda

end CFSG.Timmesfeld.Bridge
