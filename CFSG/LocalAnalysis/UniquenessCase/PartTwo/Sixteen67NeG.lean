module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeF
public import CFSG.Quasithin.H13.VolIF956Core
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg1667Ne

variable {M V₀ V W₁ W₂ : Subgroup G} {g : G}

private theorem card_image_mul_card_inf {X H N : Subgroup G} [(N.subgroupOf X).Normal]
    (hH : H ≤ X) :
    Nat.card ((H.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) *
      Nat.card ↥(H ⊓ N) = Nat.card H := by
  set φ := (QuotientGroup.mk' (N.subgroupOf X)).comp (H.subgroupOf X).subtype with hφ
  have hrange : φ.range = (H.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hφ1 : ∀ y : ↥(H.subgroupOf X), φ y = 1 ↔ ((y : ↥X) : G) ∈ N := fun y => by
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    rfl
  have hker : Nat.card φ.ker = Nat.card ↥(H ⊓ N) :=
    Nat.card_congr
      { toFun := fun y => ⟨(((y : ↥(H.subgroupOf X)) : ↥X) : G), Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_subgroupOf.mp (y : ↥(H.subgroupOf X)).2, (hφ1 _).mp y.2⟩⟩
        invFun := fun z => ⟨⟨⟨(z : G), hH (Subgroup.mem_inf.mp z.2).1⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp z.2).1⟩,
          (hφ1 _).mpr (Subgroup.mem_inf.mp z.2).2⟩
        left_inv := fun y => rfl
        right_inv := fun z => rfl }
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv] at h1
  rw [mul_comm]
  exact h1

private theorem mem_map_mk'_subgroupOf {X E A : Subgroup G} [(E.subgroupOf X).Normal]
    {q : ↥X ⧸ E.subgroupOf X} :
    q ∈ (A.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)) ↔
      ∃ a ∈ A, ∃ ha : a ∈ X, QuotientGroup.mk' (E.subgroupOf X) ⟨a, ha⟩ = q := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxq⟩
    exact ⟨(x : G), Subgroup.mem_subgroupOf.mp hx, x.2, hxq⟩
  · rintro ⟨a, ha, haX, rfl⟩
    exact ⟨⟨a, haX⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

private theorem mk'_eq_one_iff' {X E : Subgroup G} [(E.subgroupOf X).Normal]
    {x : G} (hx : x ∈ X) :
    QuotientGroup.mk' (E.subgroupOf X) ⟨x, hx⟩ = 1 ↔ x ∈ E := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

private theorem mk'_eq_mk'_of_inv_mul_mem {X E : Subgroup G} [(E.subgroupOf X).Normal]
    {a b : G} (ha : a ∈ X) (hb : b ∈ X) (h : a⁻¹ * b ∈ E) :
    QuotientGroup.mk' (E.subgroupOf X) ⟨a, ha⟩ =
      QuotientGroup.mk' (E.subgroupOf X) ⟨b, hb⟩ := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using h

private theorem map_subgroupOf_eq_bot_of_le {X E A : Subgroup G} [(E.subgroupOf X).Normal]
    (hAE : A ≤ E) :
    (A.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨a, haA, haX, rfl⟩ := mem_map_mk'_subgroupOf.mp hq
  rw [Subgroup.mem_bot]
  exact (mk'_eq_one_iff' haX).mpr (hAE haA)

private theorem zpowers_subgroupOf' {X : Subgroup G} (z : ↥X) :
    (Subgroup.zpowers (z : G)).subgroupOf X = Subgroup.zpowers z := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa using congrArg (Subtype.val) hk⟩

private theorem commutator_mk' {X E : Subgroup G} [(E.subgroupOf X).Normal]
    (a b : G) (ha : a ∈ X) (hb : b ∈ X) (hc : ⁅a, b⁆ ∈ X) :
    QuotientGroup.mk' (E.subgroupOf X) ⟨a, ha⟩ * QuotientGroup.mk' (E.subgroupOf X) ⟨b, hb⟩ *
      (QuotientGroup.mk' (E.subgroupOf X) ⟨a, ha⟩)⁻¹ *
      (QuotientGroup.mk' (E.subgroupOf X) ⟨b, hb⟩)⁻¹ =
      QuotientGroup.mk' (E.subgroupOf X) ⟨⁅a, b⁆, hc⟩ := by
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  rfl

theorem f956Data [((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal]
    (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹)
    {z v i : ↥(V ⊔ conjSubgroup V g)}
    (hz : (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers (z : G))
    (hv : (v : G) ∈ V) (hvU : (v : G) ∉ V ⊓ conjSubgroup M g)
    (hi : (i : G) ∈ conjSubgroup V g) (hiB : (i : G) ∉ conjSubgroup V g ⊓ M) :
    CFSG.Quasithin.H13.VolI.F956Data
      (⊤ : Subgroup (↥(V ⊔ conjSubgroup V g) ⧸
        (V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)))
      ((((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)).subgroupOf
          (V ⊔ conjSubgroup V g)).map
        (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g))))
      (((V ⊓ conjSubgroup M g).subgroupOf (V ⊔ conjSubgroup V g)).map
        (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g))))
      (((conjSubgroup V g ⊓ M).subgroupOf (V ⊔ conjSubgroup V g)).map
        (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g))))
      (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)) z)
      (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)) v)
      (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)) i) := by
  classical
  let X : Subgroup G := V ⊔ conjSubgroup V g
  let E : Subgroup G := V₀ ⊔ conjSubgroup V₀ g
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let B : Subgroup G := conjSubgroup V g ⊓ M
  let N : Subgroup G := U ⊓ B
  haveI hEnorm : (E.subgroupOf X).Normal :=
    show ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal from inferInstance
  change CFSG.Quasithin.H13.VolI.F956Data
    (⊤ : Subgroup (↥X ⧸ E.subgroupOf X))
    ((N.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)))
    ((U.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)))
    ((B.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)))
    (QuotientGroup.mk' (E.subgroupOf X) z)
    (QuotientGroup.mk' (E.subgroupOf X) v)
    (QuotientGroup.mk' (E.subgroupOf X) i)
  have hUX : U ≤ X := inf_le_left.trans le_sup_left
  have hBX : B ≤ X := inf_le_left.trans le_sup_right
  have hNX : N ≤ X := (inf_le_left.trans inf_le_left).trans le_sup_left
  have hV₀X : V₀ ≤ X := (le_sup_left : V₀ ≤ E).trans (E_le_X h)
  have hV₀gX : conjSubgroup V₀ g ≤ X := (le_sup_right : conjSubgroup V₀ g ≤ E).trans (E_le_X h)
  have hz2 : orderOf (z : G) = 2 := by
    rw [← Nat.card_zpowers, ← hz]
    exact card_U_inf_B h hs
  have hzN : (z : G) ∈ N := by
    show (z : G) ∈ (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)
    rw [hz]
    exact Subgroup.mem_zpowers (z : G)
  have hNsub : N.subgroupOf X = Subgroup.zpowers z := by
    rw [show N = (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) from rfl, hz]
    exact zpowers_subgroupOf' z
  have hV₁ : (N.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)) =
      Subgroup.zpowers (QuotientGroup.mk' (E.subgroupOf X) z) := by
    rw [hNsub, MonoidHom.map_zpowers]
  have hNcard : Nat.card ((N.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X))) = 2 := by
    have hcard := card_image_mul_card_inf (X := X) (N := E) (H := N) hNX
    rw [N_inf_E h hs, Subgroup.card_bot, mul_one, card_U_inf_B h hs] at hcard
    exact hcard
  have horder : orderOf (QuotientGroup.mk' (E.subgroupOf X) z) = 2 := by
    rw [← Nat.card_zpowers, ← hV₁]
    exact hNcard
  have hUq : IsElemAbelian 2 ((U.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X))) :=
    ((h.elemAbelian.mono inf_le_left).subgroupOf X).map _
  have hBq : IsElemAbelian 2 ((B.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X))) :=
    (((E3.isElemAbelian_conjSubgroup h.elemAbelian g).mono inf_le_left).subgroupOf X).map _
  have hvX : (v : G) ∈ X := (le_sup_left : V ≤ X) hv
  have hiX : (i : G) ∈ X := (le_sup_right : conjSubgroup V g ≤ X) hi
  refine
    { mem_V₁ := ?_
      z_ne := ?_
      z_comm := ?_
      X_le := le_top
      Y_le := le_top
      v_mem := Subgroup.mem_top _
      i_mem := Subgroup.mem_top _
      V₁_le_X := Subgroup.map_mono (Subgroup.subgroupOf_mono X inf_le_left)
      V₁_le_Y := Subgroup.map_mono (Subgroup.subgroupOf_mono X inf_le_right)
      inf_le := ?_
      card_X := ?_
      card_Y := ?_
      card_V₁ := hNcard
      sq_X := ?_
      sq_Y := ?_
      comm_X := ?_
      comm_Y := ?_
      comm_XY := ?_
      v_X := ?_
      i_Y := ?_
      v_Y := ?_
      i_X := ?_
      v_fix := ?_
      i_fix := ?_
      nonab := ?_ }
  · rw [hV₁]
    intro t
    exact Subgroup.mem_zpowers_iff_of_orderOf_eq_two horder
  · intro hz1
    have hzE : (z : G) ∈ E := (mk'_eq_one_iff' z.2).mp hz1
    have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
      rw [← N_inf_E h hs]
      exact ⟨hzN, hzE⟩
    rw [Subgroup.mem_bot] at hzbot
    rw [hzbot, orderOf_one] at hz2
    omega
  · intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf X) q
    rw [← map_mul, ← map_mul]
    congr 1
    ext
    simp only [Subgroup.coe_mul]
    exact (Subgroup.mem_centralizer_iff.mp
      (CFSG.LocalAnalysis.WeakClosure81.NOf_le_centralizer_L (hyp64 h hs) hzN) x x.2).symm
  · intro q hq
    rw [Subgroup.mem_inf] at hq
    obtain ⟨hqU, hqB⟩ := hq
    obtain ⟨u, huU, huX, rfl⟩ := (mem_map_mk'_subgroupOf).mp hqU
    obtain ⟨b, hbB, hbX, hbq⟩ := (mem_map_mk'_subgroupOf).mp hqB
    have hEub : (u : G)⁻¹ * b ∈ E := by
      have h := QuotientGroup.eq.mp hbq.symm
      rwa [Subgroup.mem_subgroupOf] at h
    obtain ⟨n, hnN, hnE⟩ := exists_mem_N_of_inv_mul_mem_E h hs huU hbB hEub
    have hnX : n ∈ X := hNX hnN
    exact (mem_map_mk'_subgroupOf).mpr ⟨n, hnN, hnX,
      (mk'_eq_mk'_of_inv_mul_mem huX hnX hnE).symm⟩
  · have hcard := card_image_mul_card_inf (X := X) (N := E) (H := U) hUX
    rw [U_inf_E h hs, card_U h hs.1] at hcard
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := V₀)) hcard
  · have hcard := card_image_mul_card_inf (X := X) (N := E) (H := B) hBX
    rw [B_inf_E h hs, E3.card_conjSubgroup, card_B h hs.1] at hcard
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := V₀)) hcard
  · intro a ha
    simpa [pow_two] using hUq.2 a ha
  · intro b hb
    simpa [pow_two] using hBq.2 b hb
  · intro a ha a' ha'
    exact IsElemAbelian.comm hUq ha ha'
  · intro b hb b' hb'
    exact IsElemAbelian.comm hBq hb hb'
  · intro a ha b hb
    obtain ⟨u, huU, huX, rfl⟩ := (mem_map_mk'_subgroupOf).mp ha
    obtain ⟨b', hbB, hbX, rfl⟩ := (mem_map_mk'_subgroupOf).mp hb
    have hcN : ⁅u, b'⁆ ∈ N :=
      commutator_U_B_le h (Subgroup.commutator_mem_commutator huU hbB)
    have hcX : ⁅u, b'⁆ ∈ X := hNX hcN
    rw [commutator_mk' u b' huX hbX hcX]
    exact (mem_map_mk'_subgroupOf).mpr ⟨⁅u, b'⁆, hcN, hcX, rfl⟩
  · intro a ha
    obtain ⟨u, huU, huX, rfl⟩ := (mem_map_mk'_subgroupOf).mp ha
    rw [← map_mul, ← map_mul]
    congr 1
    ext
    simp only [Subgroup.coe_mul]
    exact IsElemAbelian.comm h.elemAbelian hv huU.1
  · intro b hb
    obtain ⟨b', hbB, hbX, rfl⟩ := (mem_map_mk'_subgroupOf).mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    ext
    simp only [Subgroup.coe_mul]
    exact IsElemAbelian.comm (E3.isElemAbelian_conjSubgroup h.elemAbelian g) hi hbB.1
  · intro b hb
    obtain ⟨b', hbB, hbX, rfl⟩ := (mem_map_mk'_subgroupOf).mp hb
    have hcU : ⁅(v : G), b'⁆ ∈ U :=
      commutator_V_B_le h hs.1 (Subgroup.commutator_mem_commutator hv hbB)
    have hcX : ⁅(v : G), b'⁆ ∈ X := hUX hcU
    rw [commutator_mk' (v : G) b' hvX hbX hcX]
    exact (mem_map_mk'_subgroupOf).mpr ⟨⁅(v : G), b'⁆, hcU, hcX, rfl⟩
  · intro a ha
    obtain ⟨u, huU, huX, rfl⟩ := (mem_map_mk'_subgroupOf).mp ha
    have hcB : ⁅(i : G), u⁆ ∈ B :=
      commutator_Vg_U_le h hs.1 (Subgroup.commutator_mem_commutator hi huU)
    have hcX : ⁅(i : G), u⁆ ∈ X := hBX hcB
    rw [commutator_mk' (i : G) u hiX huX hcX]
    exact (mem_map_mk'_subgroupOf).mpr ⟨⁅(i : G), u⁆, hcB, hcX, rfl⟩
  · intro b hb hmem
    obtain ⟨b', hbB, hbX, rfl⟩ := (mem_map_mk'_subgroupOf).mp hb
    have hcU : ⁅(v : G), b'⁆ ∈ U :=
      commutator_V_B_le h hs.1 (Subgroup.commutator_mem_commutator hv hbB)
    have hcX : ⁅(v : G), b'⁆ ∈ X := hUX hcU
    rw [commutator_mk' (v : G) b' hvX hbX hcX] at hmem
    obtain ⟨n, hnN, hnX, hnq⟩ := (mem_map_mk'_subgroupOf).mp hmem
    have hEn : n⁻¹ * ⁅(v : G), b'⁆ ∈ E := by
      have h := QuotientGroup.eq.mp hnq
      rwa [Subgroup.mem_subgroupOf] at h
    have hcEN : ⁅(v : G), b'⁆ ∈ E ⊔ N := by
      have h := (E ⊔ N).mul_mem (Subgroup.mem_sup_right hnN) (Subgroup.mem_sup_left hEn)
      rwa [mul_inv_cancel_left] at h
    have hb'EN : b' ∈ conjSubgroup V₀ g ⊔ N := stepF h hs hv hvU hbB hcEN
    have hV₀N : conjSubgroup V₀ g ⊔ N ≤ X := sup_le hV₀gX hNX
    have hmap : ((conjSubgroup V₀ g ⊔ N).subgroupOf X).map
        (QuotientGroup.mk' (E.subgroupOf X)) =
        (N.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)) := by
      rw [Subgroup.subgroupOf_sup hV₀gX hNX, Subgroup.map_sup,
        map_subgroupOf_eq_bot_of_le (le_sup_right : conjSubgroup V₀ g ≤ E), bot_sup_eq]
    have hb'mem : QuotientGroup.mk' (E.subgroupOf X) ⟨b', hbX⟩ ∈
        ((conjSubgroup V₀ g ⊔ N).subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)) :=
      (mem_map_mk'_subgroupOf).mpr ⟨b', hb'EN, hV₀N hb'EN, rfl⟩
    rwa [hmap] at hb'mem
  · intro a ha hmem
    obtain ⟨u, huU, huX, rfl⟩ := (mem_map_mk'_subgroupOf).mp ha
    have hcB : ⁅(i : G), u⁆ ∈ B :=
      commutator_Vg_U_le h hs.1 (Subgroup.commutator_mem_commutator hi huU)
    have hcX : ⁅(i : G), u⁆ ∈ X := hBX hcB
    rw [commutator_mk' (i : G) u hiX huX hcX] at hmem
    obtain ⟨n, hnN, hnX, hnq⟩ := (mem_map_mk'_subgroupOf).mp hmem
    have hEn : n⁻¹ * ⁅(i : G), u⁆ ∈ E := by
      have h := QuotientGroup.eq.mp hnq
      rwa [Subgroup.mem_subgroupOf] at h
    have hcEN : ⁅(i : G), u⁆ ∈ E ⊔ N := by
      have h := (E ⊔ N).mul_mem (Subgroup.mem_sup_right hnN) (Subgroup.mem_sup_left hEn)
      rwa [mul_inv_cancel_left] at h
    have huEN : u ∈ V₀ ⊔ N := stepF_dual h hs' hi hiB huU hcEN
    have hV₀N : V₀ ⊔ N ≤ X := sup_le hV₀X hNX
    have hmap : ((V₀ ⊔ N).subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)) =
        (N.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)) := by
      rw [Subgroup.subgroupOf_sup hV₀X hNX, Subgroup.map_sup,
        map_subgroupOf_eq_bot_of_le (le_sup_left : V₀ ≤ E), bot_sup_eq]
    have humem : QuotientGroup.mk' (E.subgroupOf X) ⟨u, huX⟩ ∈
        ((V₀ ⊔ N).subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)) :=
      (mem_map_mk'_subgroupOf).mpr ⟨u, huEN, hV₀N huEN, rfl⟩
    rwa [hmap] at humem
  · obtain ⟨u, huU, b, hbB, hub⟩ := exists_not_commute h hs
    have huX : u ∈ X := hUX huU
    have hbX : b ∈ X := hBX hbB
    refine ⟨QuotientGroup.mk' (E.subgroupOf X) ⟨u, huX⟩, ?_,
      QuotientGroup.mk' (E.subgroupOf X) ⟨b, hbX⟩, ?_, ?_⟩
    · exact (mem_map_mk'_subgroupOf).mpr ⟨u, huU, huX, rfl⟩
    · exact (mem_map_mk'_subgroupOf).mpr ⟨b, hbB, hbX, rfl⟩
    · intro hcomm
      have hcN : ⁅u, b⁆ ∈ N :=
        commutator_U_B_le h (Subgroup.commutator_mem_commutator huU hbB)
      have hcX : ⁅u, b⁆ ∈ X := hNX hcN
      have hπ1 : QuotientGroup.mk' (E.subgroupOf X) ⟨⁅u, b⁆, hcX⟩ = 1 := by
        rw [← commutator_mk' u b huX hbX hcX, hcomm]
        group
      have hcE : ⁅u, b⁆ ∈ E := (mk'_eq_one_iff' hcX).mp hπ1
      have hcbot : ⁅u, b⁆ = 1 := by
        have hbot : ⁅u, b⁆ ∈ (⊥ : Subgroup G) := by
          rw [← N_inf_E h hs]
          exact ⟨hcN, hcE⟩
        exact Subgroup.mem_bot.mp hbot
      exact hub (commutatorElement_eq_one_iff_mul_comm.mp hcbot)

theorem exists_f956Data [((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal]
    (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) :
    ∃ z v i : ↥(V ⊔ conjSubgroup V g),
      CFSG.Quasithin.H13.VolI.F956Data
        (⊤ : Subgroup (↥(V ⊔ conjSubgroup V g) ⧸
          (V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)))
        ((((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)).subgroupOf
            (V ⊔ conjSubgroup V g)).map
          (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g))))
        (((V ⊓ conjSubgroup M g).subgroupOf (V ⊔ conjSubgroup V g)).map
          (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g))))
        (((conjSubgroup V g ⊓ M).subgroupOf (V ⊔ conjSubgroup V g)).map
          (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g))))
        (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)) z)
        (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)) v)
        (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)) i) := by
  obtain ⟨z, hz2, hz⟩ := exists_eq_zpowers h hs
  have hzN : z ∈ (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) := by
    rw [hz]
    exact Subgroup.mem_zpowers z
  have hNleV : (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) ≤ V :=
    (inf_le_left : _ ≤ V ⊓ conjSubgroup M g).trans
      (inf_le_left : V ⊓ conjSubgroup M g ≤ V)
  have hzX : z ∈ V ⊔ conjSubgroup V g := (hNleV.trans le_sup_left) hzN
  obtain ⟨v, hv, hvU, -⟩ :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp (relIndex_U h hs.1)
  have hvX : v ∈ V ⊔ conjSubgroup V g := (le_sup_left : V ≤ V ⊔ conjSubgroup V g) hv
  obtain ⟨i, hi, hiB, -⟩ :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp (relIndex_B h hs.1)
  have hiX : i ∈ V ⊔ conjSubgroup V g :=
    (le_sup_right : conjSubgroup V g ≤ V ⊔ conjSubgroup V g) hi
  exact ⟨⟨z, hzX⟩, ⟨v, hvX⟩, ⟨i, hiX⟩,
    f956Data h hs hs' hz hv hvU hi hiB⟩

theorem card_U_quot [((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal]
    (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    Nat.card (((V ⊓ conjSubgroup M g).subgroupOf (V ⊔ conjSubgroup V g)).map
      (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)))) = 8 := by
  have hcard := card_image_mul_card_inf (X := V ⊔ conjSubgroup V g)
    (N := V₀ ⊔ conjSubgroup V₀ g) (H := V ⊓ conjSubgroup M g)
    (inf_le_left.trans le_sup_left)
  rw [U_inf_E h hs, card_U h hs.1] at hcard
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := V₀)) hcard

theorem isElemAbelian_U_quot
    [((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal]
    (h : Cfg1667Ne M V₀ V W₁ W₂) :
    IsElemAbelian 2 (((V ⊓ conjSubgroup M g).subgroupOf (V ⊔ conjSubgroup V g)).map
      (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)))) :=
  ((h.elemAbelian.mono inf_le_left).subgroupOf (V ⊔ conjSubgroup V g)).map _

theorem card_K_quot [((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal]
    (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) :
    Nat.card ((((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M)).subgroupOf
        (V ⊔ conjSubgroup V g)).map
      (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)))) = 32 := by
  obtain ⟨z, v, i, D⟩ := exists_f956Data h hs hs'
  set X : Subgroup G := V ⊔ conjSubgroup V g
  set E : Subgroup G := V₀ ⊔ conjSubgroup V₀ g
  set U : Subgroup G := V ⊓ conjSubgroup M g
  set B : Subgroup G := conjSubgroup V g ⊓ M
  have hUX : U ≤ X := inf_le_left.trans le_sup_left
  have hBX : B ≤ X := inf_le_left.trans le_sup_right
  have hsup : ((U ⊔ B).subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)) =
      ((U.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X))) ⊔
      ((B.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X))) := by
    rw [Subgroup.subgroupOf_sup hUX hBX, Subgroup.map_sup]
  rw [hsup]
  exact D.card_sup

theorem isQ8Sq_K_quot [((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal]
    (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) :
    IsQ8Sq ↥((((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M)).subgroupOf
        (V ⊔ conjSubgroup V g)).map
      (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)))) := by
  obtain ⟨z, v, i, D⟩ := exists_f956Data h hs hs'
  set X : Subgroup G := V ⊔ conjSubgroup V g
  set E : Subgroup G := V₀ ⊔ conjSubgroup V₀ g
  set U : Subgroup G := V ⊓ conjSubgroup M g
  set B : Subgroup G := conjSubgroup V g ⊓ M
  have hUX : U ≤ X := inf_le_left.trans le_sup_left
  have hBX : B ≤ X := inf_le_left.trans le_sup_right
  have hsup : ((U ⊔ B).subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)) =
      ((U.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X))) ⊔
      ((B.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X))) := by
    rw [Subgroup.subgroupOf_sup hUX hBX, Subgroup.map_sup]
  rw [hsup]
  exact D.isQ8Sq

theorem cube_commutator_mem_E (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹)
    {v i : G} (hv : v ∈ V) (hvU : v ∉ V ⊓ conjSubgroup M g) (hi : i ∈ conjSubgroup V g)
    (hiB : i ∉ conjSubgroup V g ⊓ M) {k : G}
    (hk : k ∈ (V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M)) :
    (v * i) ^ 3 * k * ((v * i) ^ 3)⁻¹ * k⁻¹ ∈ V₀ ⊔ conjSubgroup V₀ g := by
  classical
  let X : Subgroup G := V ⊔ conjSubgroup V g
  let E : Subgroup G := V₀ ⊔ conjSubgroup V₀ g
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let B : Subgroup G := conjSubgroup V g ⊓ M
  let N : Subgroup G := U ⊓ B
  haveI hEnorm : (E.subgroupOf X).Normal :=
    show ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal from E_normal h hs hs'
  have hV₀X : V₀ ≤ X := (le_sup_left : V₀ ≤ E).trans (E_le_X h)
  have hV₀gX : conjSubgroup V₀ g ≤ X := (le_sup_right : conjSubgroup V₀ g ≤ E).trans (E_le_X h)
  have hUX : U ≤ X := inf_le_left.trans le_sup_left
  have hBX : B ≤ X := inf_le_left.trans le_sup_right
  have hKX : U ⊔ B ≤ X := sup_le hUX hBX
  obtain ⟨z, hz2, hz⟩ := exists_eq_zpowers h hs
  have hzN : z ∈ N := by
    show z ∈ (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)
    rw [hz]
    exact Subgroup.mem_zpowers z
  have hNleV : (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) ≤ V :=
    (inf_le_left : _ ≤ V ⊓ conjSubgroup M g).trans
      (inf_le_left : V ⊓ conjSubgroup M g ≤ V)
  have hzX : z ∈ X := (hNleV.trans (le_sup_left : V ≤ X)) hzN
  have hvX : v ∈ X := (le_sup_left : V ≤ X) hv
  have hiX : i ∈ X := (le_sup_right : conjSubgroup V g ≤ X) hi
  have hkX : k ∈ X := hKX hk
  have D := f956Data h hs hs' (z := ⟨z, hzX⟩) (v := ⟨v, hvX⟩) (i := ⟨i, hiX⟩)
    hz hv hvU hi hiB
  have hsup : ((U ⊔ B).subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)) =
      ((U.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X))) ⊔
      ((B.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X))) := by
    rw [Subgroup.subgroupOf_sup hUX hBX, Subgroup.map_sup]
  have hkQ : QuotientGroup.mk' (E.subgroupOf X) ⟨k, hkX⟩ ∈
      ((U ⊔ B).subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X)) :=
    ⟨⟨k, hkX⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hkQ' : QuotientGroup.mk' (E.subgroupOf X) ⟨k, hkX⟩ ∈
      ((U.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X))) ⊔
      ((B.subgroupOf X).map (QuotientGroup.mk' (E.subgroupOf X))) := by
    rwa [hsup] at hkQ
  have hcube := D.cube_comm hkQ'
  have hEE : QuotientGroup.mk' (E.subgroupOf X) =
      QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)) := rfl
  rw [← hEE] at hcube
  let x : ↥X := (⟨v, hvX⟩ * ⟨i, hiX⟩) ^ 3 * ⟨k, hkX⟩ *
    ((⟨v, hvX⟩ * ⟨i, hiX⟩) ^ 3)⁻¹ * ⟨k, hkX⟩⁻¹
  change (x : G) ∈ E
  rw [← (mk'_eq_one_iff' x.2)]
  have hconv : QuotientGroup.mk' (E.subgroupOf X) x =
      (QuotientGroup.mk' (E.subgroupOf X) ⟨v, hvX⟩ *
        QuotientGroup.mk' (E.subgroupOf X) ⟨i, hiX⟩) ^ 3 *
        QuotientGroup.mk' (E.subgroupOf X) ⟨k, hkX⟩ *
        ((QuotientGroup.mk' (E.subgroupOf X) ⟨v, hvX⟩ *
          QuotientGroup.mk' (E.subgroupOf X) ⟨i, hiX⟩) ^ 3)⁻¹ *
        (QuotientGroup.mk' (E.subgroupOf X) ⟨k, hkX⟩)⁻¹ := by
    simp only [x, ← map_mul, ← map_inv, ← map_pow]
  rw [hconv, hcube]
  group

end Cfg1667Ne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
