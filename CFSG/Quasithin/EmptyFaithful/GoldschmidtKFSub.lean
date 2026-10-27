module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFEnd
public import CFSG.Quasithin.Background.E2Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.LocalCores CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {Hs : Subgroup G}

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {K : Subgroup G} (hK : CFSG.Assembly.IsElemAbelian p K) :
    CFSG.Assembly.IsElemAbelian p (K.subgroupOf Hs) := CFSG.Open.IsElemAbelian.subgroupOf hK Hs

omit [Finite G] in
theorem card_subgroupOf_of_le {K : Subgroup G} (hK : K ≤ Hs) :
    Nat.card (K.subgroupOf Hs) = Nat.card K :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv

omit [Finite G] in
theorem mem_normalizer_subgroupOf {K : Subgroup G} {g : ↥Hs}
    (hg : (g : G) ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((K.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have := Subgroup.mem_normalizer_iff.mp hg (h : G)
  exact this

theorem endgame_false_sub (hsqtk : SQTKGroup ↥Hs)
    (hlist : ∀ C : Subgroup ↥Hs, IsComponent C → A23List (↥C ⧸ Subgroup.center ↥C))
    (hA : Input15338Rank1) (hZ : Input15338CenterRank) (hIdent : Input15338Ident)
    (hCJ : Input15338NonsolvJ) (hCL : Input15338FinalL34)
    {B : Subgroup G} (hBH : B ≤ Hs) (hB : IsPOnePlusTwo 3 ↥B)
    {Lx : Subgroup G} (hLxH : Lx ≤ Hs) (hqx : CFSG.IsQuasisimple ↥Lx)
    (hLxE : Lx.subgroupOf Hs ≤ layer ↥Hs)
    (hcard : Nat.card (↥Lx ⧸ Subgroup.center ↥Lx) = 168) (hZ1 : Subgroup.center ↥Lx = ⊥)
    {v : G} (hvH : v ∈ Hs) (hv2 : v * v = 1) (hvLx : ∀ l ∈ Lx, v * l = l * v)
    (hnorm : ∀ g ∈ Hs, g * v = v * g → g ∈ Subgroup.normalizer (Lx : Set G))
    {U : Subgroup G} (hUH : U ≤ Hs) (hU4 : Nat.card U = 4)
    (hUel : CFSG.Assembly.IsElemAbelian 2 U)
    (hsolv : ∀ u ∈ U, u ≠ 1 →
      Group.IsSolvable ↥(Subgroup.centralizer ({u} : Set G) ⊓ Hs))
    {y : G} (hyH : y ∈ Hs) (hyN : y ∈ Subgroup.normalizer (U : Set G)) (hy3 : y ^ 3 = 1)
    (hyU : ∃ u ∈ U, y * u * y⁻¹ ≠ u)
    {F : Subgroup G} (hFH : F ≤ Hs) (hFel : CFSG.Assembly.IsElemAbelian 3 F)
    (hF9 : Nat.card F = 9) (hFU : ∀ a ∈ F, ∀ w ∈ U, a * w = w * a)
    (hFnorm : ∀ u ∈ U, u ≠ 1 → ∀ g ∈ Hs, g * u = u * g →
      g ∈ Subgroup.normalizer (F : Set G)) : False := by
  classical
  refine endgame_false hsqtk hlist hA hZ hIdent hCJ hCL (B := B.subgroupOf Hs)
    (isPOnePlusTwo_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBH).symm hB)
    (Lx := Lx.subgroupOf Hs)
    (isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLxH).symm hqx) hLxE
    ?_ ?_ (v := ⟨v, hvH⟩) (Subtype.ext hv2) ?_ ?_ (U := U.subgroupOf Hs) ?_ ?_ ?_
    (y := ⟨y, hyH⟩) ?_ (Subtype.ext (by simpa using hy3)) ?_ (F := F.subgroupOf Hs) ?_ ?_ ?_ ?_
  ·
    let e : (↥(Lx.subgroupOf Hs) ⧸ Subgroup.center ↥(Lx.subgroupOf Hs)) ≃*
        (↥Lx ⧸ Subgroup.center ↥Lx) :=
      QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hLxH)
        (Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hLxH))
    rw [Nat.card_congr e.toEquiv]
    exact hcard
  ·
    have h1 := Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hLxH)
    rw [hZ1] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (Subgroup.subgroupOfEquivOfLe hLxH).injective).mp h1
  · intro l hl
    apply Subtype.ext
    exact hvLx _ hl
  · intro g hg
    exact mem_normalizer_subgroupOf (hnorm g g.2 (congrArg Subtype.val hg))
  · rw [card_subgroupOf_of_le hUH]; exact hU4
  · exact isElemAbelian_subgroupOf hUel
  · intro u hu hu1
    have hu' : (u : G) ∈ U := hu
    have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hs := hsolv u hu' hu1'
    let f : ↥(Subgroup.centralizer ({u} : Set ↥Hs)) →*
        ↥(Subgroup.centralizer ({(u : G)} : Set G) ⊓ Hs) :=
      { toFun := fun g => ⟨(g : ↥Hs), ⟨Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp g.2)),
          (g : ↥Hs).2⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective f := fun a b h =>
      Subtype.ext (Subtype.ext
        (congrArg (fun z : ↥(Subgroup.centralizer ({(u : G)} : Set G) ⊓ Hs) => (z : G)) h))
    exact Group.isSolvable_of_isSolvable_injective hinj
  · exact mem_normalizer_subgroupOf hyN
  · obtain ⟨u, hu, hne⟩ := hyU
    refine ⟨⟨u, hUH hu⟩, hu, fun h => hne ?_⟩
    exact congrArg Subtype.val h
  · exact isElemAbelian_subgroupOf hFel
  · rw [card_subgroupOf_of_le hFH]; exact hF9
  · intro a ha w hw
    exact Subtype.ext (hFU a ha w hw)
  · intro u hu hu1 g hg
    have hu' : (u : G) ∈ U := hu
    have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
    exact mem_normalizer_subgroupOf (hFnorm u hu' hu1' g g.2 (congrArg Subtype.val hg))

end CFSG.Quasithin.SBd19F
