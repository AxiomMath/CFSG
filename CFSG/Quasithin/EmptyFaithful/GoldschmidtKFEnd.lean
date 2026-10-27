module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFEndGame
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFUnique

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.LocalCores CFSG.Open CFSG.Quasithin

theorem endgame_false {H : Type} [Group H] [Finite H] (hsqtk : SQTKGroup H)
    (hlist : ∀ C : Subgroup H, IsComponent C → A23List (↥C ⧸ Subgroup.center ↥C))
    (hA : Input15338Rank1) (hZ : Input15338CenterRank) (hIdent : Input15338Ident)
    (hCJ : Input15338NonsolvJ) (hCL : Input15338FinalL34)
    {B : Subgroup H} (hB : IsPOnePlusTwo 3 ↥B)
    {Lx : Subgroup H} (hqx : CFSG.IsQuasisimple ↥Lx) (hLxE : Lx ≤ layer H)
    (hcard : Nat.card (↥Lx ⧸ Subgroup.center ↥Lx) = 168) (hZ1 : Subgroup.center ↥Lx = ⊥)
    {v : H} (hv2 : v * v = 1) (hvLx : ∀ l ∈ Lx, v * l = l * v)
    (hnorm : ∀ g : H, g * v = v * g → g ∈ Subgroup.normalizer (Lx : Set H))
    {U : Subgroup H} (hU4 : Nat.card U = 4) (hUel : CFSG.Assembly.IsElemAbelian 2 U)
    (hsolv : ∀ u ∈ U, u ≠ 1 → Group.IsSolvable ↥(Subgroup.centralizer ({u} : Set H)))
    {y : H} (hyN : y ∈ Subgroup.normalizer (U : Set H)) (hy3 : y ^ 3 = 1)
    (hyU : ∃ u ∈ U, y * u * y⁻¹ ≠ u)
    {F : Subgroup H} (hFel : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    (hFU : ∀ a ∈ F, ∀ w ∈ U, a * w = w * a)
    (hFnorm : ∀ u ∈ U, u ≠ 1 → ∀ g : H, g * u = u * g →
      g ∈ Subgroup.normalizer (F : Set H)) : False := by
  have hno1 : ∀ C : Subgroup H, IsComponent C → CFSG.Open.pRank 3 C ≠ 1 := fun C hC h1 =>
    no_rankOne_component hsqtk.1 hA hlist hB hC h1
  have huniq : ∀ C C' : Subgroup H, IsComponent C → IsComponent C' → CFSG.Open.pRank 3 C = 2 →
      CFSG.Open.pRank 3 C' = 2 → C = C' := by
    intro C C' hC hC' h2 h2'
    by_contra hne
    exact False_of_two_rankTwo hsqtk hZ hC hC' hne h2 h2'
  have h3 : 3 ∣ (Subgroup.center ↥Lx).index := by
    have : (Subgroup.center ↥Lx).index = 168 := hcard
    rw [this]; norm_num
  obtain ⟨L₂, hL₂, hrk₂, hLxL₂, hnormal⟩ :=
    exists_rankTwo_component hsqtk.1 hno1 huniq hqx hLxE h3
  have : L₂.Normal := hnormal
  have hq₂ := hL₂.1
  have hlist₂ := hlist L₂ hL₂
  obtain ⟨u₀, hu₀, hu₀1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall U).mpr hcon
    rw [this, Subgroup.card_bot] at hU4
    omega
  have hu₀2 : u₀ * u₀ = 1 := by rw [← pow_two]; exact hUel.2 u₀ hu₀
  rcases ident_of_normal hIdent hq₂ hlist₂ hrk₂ hLxL₂ hqx hcard hZ1 hv2 hvLx hnorm with
    h34 | hJ2 | hL37
  · exact false_of_final34 hsqtk hCL hZ hq₂ hrk₂ h34 hU4 hUel hsolv hyN hy3 hyU hFel hF9
      hFU hFnorm
  · exact false_of_nonsolvJ hCJ hq₂ (Or.inl hJ2) hu₀2 (hsolv u₀ hu₀ hu₀1)
  · exact false_of_nonsolvJ hCJ hq₂ (Or.inr hL37) hu₀2 (hsolv u₀ hu₀ hu₀1)

end CFSG.Quasithin.SBd19F
