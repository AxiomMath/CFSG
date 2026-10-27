module

public import CFSG.RankThree.GF2n.Tim79aSec34Invariant
public import CFSG.RankThree.GF2n.Tim79aSec34BraidPair
public import CFSG.RankThree.GF2n.Tim79aSec34KFacts
public import CFSG.RankThree.GF2n.Tim79aSec34SpTransport

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Sec34TorusStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
    Sec23Three V H → CentreClause V H →
    ∃ f : ℕ, 1 ≤ f ∧ 2 ^ f = qBar V H ∧ ∃ h ∈ xOf V H, conjSubgroup h V = V ∧
      (∀ u ∈ V ⊓ wOf V H, h ^ (2 ^ f - 1) * u * (h ^ (2 ^ f - 1))⁻¹ = u) ∧
      (∀ i : ℕ, 0 < i → i < 2 ^ f - 1 → ∀ u ∈ V ⊓ wOf V H,
        h ^ i * u * (h ^ i)⁻¹ = u → u = 1) ∧
      ∀ n ∈ xOf V H, conjSubgroup n V = V →
        ∃ i : ℕ, ∀ u ∈ V ⊓ wOf V H, n * u * n⁻¹ = h ^ i * u * (h ^ i)⁻¹

theorem sec34LineStatement_of_torus (hT : Sec34TorusStatement) : Sec34LineStatement := by
  intro G _ _ M V Q P H hs h3 hcc
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨f, hf, hq, h, hhX, hhV, hord, hreg, hdec⟩ := hT G M V Q P H hs h3 hcc
  have hhH : h ∈ H := xOf_le_H hVH hhX
  have hA2 : ∀ x ∈ V ⊓ wOf V H, x * x = 1 := fun x hx => hc.elemAb.mul_self_eq_one hx.1
  have hAab : ∀ x ∈ V ⊓ wOf V H, ∀ y ∈ V ⊓ wOf V H, x * y = y * x := fun x hx y hy =>
    hc.elemAb.comm hx.1 hy.1
  have hhA : ∀ x ∈ V ⊓ wOf V H, h * x * h⁻¹ ∈ V ⊓ wOf V H := by
    intro x hx
    refine ⟨?_, ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hhH)) x).mp hx.2⟩
    have : h * x * h⁻¹ ∈ conjSubgroup h V := by
      rw [mem_conjSubgroup]
      have e : h⁻¹ * (h * x * h⁻¹) * h = x := by group
      rw [e]; exact hx.1
    rwa [hhV] at this
  obtain ⟨A₁, hA₁le, hcard, hinv⟩ := exists_invariant_subgroup_of_semiregular
    (V ⊓ wOf V H) hA2 hAab hc.V_inf_wOf_ne_bot f hf h hhA hord hreg
  refine ⟨A₁, hA₁le, hcard.trans hq, ?_⟩
  intro n hn hnV
  obtain ⟨i, hi⟩ := hdec n hn hnV
  have hle : conjSubgroup n A₁ ≤ A₁ := by
    intro z hz
    have hx : n⁻¹ * z * n ∈ A₁ := mem_conjSubgroup.mp hz
    have e : z = n * (n⁻¹ * z * n) * n⁻¹ := by group
    rw [e, hi _ (hA₁le hx)]
    exact hinv i _ hx
  exact conjSubgroup_eq_of_le hle

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Sec34CentreTrivialStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
    Sec23Three V H → CentreClause V H → Subgroup.center (Xbar V H) = ⊥

@[expose] def cenX (V H : Subgroup G) : Subgroup ↥(xOf V H) where
  carrier := {x | ∀ u ∈ V ⊓ wOf V H, (x : G) * u * (x : G)⁻¹ = u}
  one_mem' := fun u _ => by simp
  mul_mem' := fun {x y} hx hy u hu => by
    have e : ((x * y : ↥(xOf V H)) : G) * u * ((x * y : ↥(xOf V H)) : G)⁻¹ =
        (x : G) * ((y : G) * u * (y : G)⁻¹) * (x : G)⁻¹ := by
      simp only [Subgroup.coe_mul]; group
    rw [e, hy u hu, hx u hu]
  inv_mem' := fun {x} hx u hu => by
    have h1 := hx u hu
    have e : ((x⁻¹ : ↥(xOf V H)) : G) * u * ((x⁻¹ : ↥(xOf V H)) : G)⁻¹ =
        (x : G)⁻¹ * u * (x : G) := by
      simp only [Subgroup.coe_inv]; group
    rw [e]
    calc (x : G)⁻¹ * u * (x : G) = (x : G)⁻¹ * ((x : G) * u * (x : G)⁻¹) * (x : G) := by rw [h1]
      _ = u := by group

namespace Sec3Setup

variable {M V Q P H : Subgroup G} [Finite G]

theorem mem_wOf_of_xToZ_eq_one (hs : Sec3Setup M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {x : ↥(xOf V H)}
    (hx : xToZ hs.setup.mc.toMinCex.V_le_H x = 1) : (x : G) ∈ wOf V H := by
  have h1 : xToXbar hs.setup.mc.toMinCex.V_le_H x ∈ Subgroup.center (Xbar V H) :=
    (QuotientGroup.eq_one_iff _).mp hx
  rw [hZ, Subgroup.mem_bot] at h1
  have := congrArg Subtype.val h1
  rw [coe_xToXbar] at this
  exact (piBar_eq_one_iff _).1 this

theorem xToZ_eq_one_of_mem_wOf (hs : Sec3Setup M V Q P H) {x : ↥(xOf V H)}
    (hx : (x : G) ∈ wOf V H) : xToZ hs.setup.mc.toMinCex.V_le_H x = 1 := by
  have h1 : piBar V H (Subgroup.inclusion (xOf_le_H hs.setup.mc.toMinCex.V_le_H) x) = 1 :=
    (piBar_eq_one_iff _).2 hx
  have h2 : xToXbar hs.setup.mc.toMinCex.V_le_H x = 1 := Subtype.ext h1
  rw [xToZ_apply, h2, map_one]

theorem mem_cenX_of_mem_wOf (hs : Sec3Setup M V Q P H) {x : ↥(xOf V H)}
    (hx : (x : G) ∈ wOf V H) : x ∈ cenX V H := fun u hu => by
  rw [hs.setup.mc.toMinCex.wOf_comm hx hu.2]; group

theorem mem_cenX_of_centralizer (hs : Sec3Setup M V Q P H) (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hSF : StabFacts (XbarZ V H) (VZ V H)) {x : ↥(xOf V H)}
    (hx : xToZ hs.setup.mc.toMinCex.V_le_H x ∈
      Subgroup.centralizer (VZ V H : Set (XbarZ V H))) : x ∈ cenX V H := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hcl := hSF _ hx
  have hS_le : {y | ∃ g' : XbarZ V H, conjSub (VZ V H) g' ≤
      Subgroup.centralizer (VZ V H : Set (XbarZ V H)) ∧ y ∈ conjSub (VZ V H) g'} ⊆
      ((cenX V H).map (xToZ hVH) : Set (XbarZ V H)) := by
    rintro y ⟨g', hg', hy⟩
    obtain ⟨gg, rfl⟩ := xToZ_surjective hVH g'
    obtain ⟨bb, hbb, hbby⟩ := hs.exists_lift_conj_VZ gg.2 (t := y) hy
    refine ⟨bb, ?_, hbby⟩
    have hcomm := hc.commute_conj_of_commute_tilde (x₁ := 1) (x₂ := gg) (by
      intro a ha b hb
      rw [map_one, conjSubgroup_one] at ha
      exact Subgroup.mem_centralizer_iff.mp (hg' hb) a ha)
    intro u hu
    have h1 := hcomm u (by rw [OneMemClass.coe_one, conjSubgroup_one]; exact hu.1) (bb : G) hbb
    calc (bb : G) * u * (bb : G)⁻¹ = (u * (bb : G)) * (bb : G)⁻¹ := by rw [← h1]
      _ = u := by group
  have hmem : xToZ hVH x ∈ (cenX V H).map (xToZ hVH) :=
    (Subgroup.closure_le _ |>.2 hS_le) hcl
  obtain ⟨x', hx', hxx'⟩ := hmem
  have hker : xToZ hVH (x'⁻¹ * x) = 1 := by rw [map_mul, map_inv, hxx', inv_mul_cancel]
  have hW : ((x'⁻¹ * x : ↥(xOf V H)) : G) ∈ wOf V H := hs.mem_wOf_of_xToZ_eq_one hZ hker
  have hx_eq : x = x' * (x'⁻¹ * x) := by group
  rw [hx_eq]
  exact (cenX V H).mul_mem hx' (hs.mem_cenX_of_mem_wOf hW)

theorem xToZ_mem_normalizer (hs : Sec3Setup M V Q P H) {n : ↥(xOf V H)}
    (hn : conjSubgroup (n : G) V = V) :
    xToZ hs.setup.mc.toMinCex.V_le_H n ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H)) := by
  apply mem_normalizer_of_conjSubgroup_eq
  have := imgZ_conj hs.setup.mc.toMinCex.V_le_H n
  rw [hn, ← VZ_eq_imgZ] at this
  exact this.symm

theorem conjSubgroup_eq_of_xToZ_mem_normalizer (hs : Sec3Setup M V Q P H) {x : ↥(xOf V H)}
    (hx : xToZ hs.setup.mc.toMinCex.V_le_H x ∈
      Subgroup.normalizer (VZ V H : Set (XbarZ V H))) : conjSubgroup (x : G) V = V := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  by_contra hne
  exact hc.conj_VZ_ne hs.setup.data hne (mem_normalizer_iff_conjSubgroup_eq.mp hx)

theorem mul_self_of_mem_conj (hs : Sec3Setup M V Q P H) {y x : G} (hx : x ∈ conjSubgroup y V) :
    x * x = 1 := by
  have h1 := hs.setup.mc.toMinCex.elemAb.mul_self_eq_one (mem_conjSubgroup.mp hx)
  calc x * x = y * ((y⁻¹ * x * y) * (y⁻¹ * x * y)) * y⁻¹ := by group
    _ = 1 := by rw [h1]; group

end Sec3Setup

theorem sec34TorusStatement_of_parts (hCentre : Sec34CentreTrivialStatement)
    :
    Sec34TorusStatement := by
  have hTor := CFSG.RankThree.GF2n.Tim79a.spTorusStatement_of_model
  have hStab := spStabStatement_of_model
  intro G _ _ M V Q P H hs h3 hcc
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hZ := hCentre G M V Q P H hs h3 hcc
  have hSp := Sec3Setup.classicalRootSp_tilde h3
  obtain ⟨f, hf, hq, hT⟩ := id h3
  have hTF := hTor _ _ f (rootClassZ V H) hf hT (VZ_mem_rootClassZ V H)
  have hSF := hStab _ _ hSp
  have hOppMeet := sec34OppMeetStatement_of_sp
  obtain ⟨y₀, hy₀X, u₀, hu₀, w₀, hw₀, hnc⟩ := hc.exists_noncomm_conj hs.setup.data
  have hy₀c : y₀ ∉ Ycomm V H := fun h => hnc (h.2 u₀ hu₀ w₀ hw₀)
  have hnc' := hs.not_commuting_tilde (y := ⟨y₀, hy₀X⟩) hy₀c
  obtain ⟨hK, hKN, hdec, hord, hprod⟩ := hTF.torus _ hnc'
  obtain ⟨hh, hhx⟩ := xToZ_surjective hVH hK
  have hhV : conjSubgroup (hh : G) V = V :=
    hs.conjSubgroup_eq_of_xToZ_mem_normalizer (by rw [hhx]; exact hKN)
  have hhH : (hh : G) ∈ H := xOf_le_H hVH hh.2
  have hpowN : ∀ k : ℕ, (hh : G) ^ k ∈ Subgroup.normalizer (V : Set G) := fun k =>
    Subgroup.pow_mem _ (mem_normalizer_of_conjSubgroup_eq hhV) k
  have hconjA : ∀ (k : ℕ), ∀ u ∈ V ⊓ wOf V H,
      (hh : G) ^ k * u * ((hh : G) ^ k)⁻¹ ∈ V ⊓ wOf V H := by
    intro k u hu
    exact ⟨((Subgroup.mem_normalizer_iff.mp (hpowN k)) u).mp hu.1,
      ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (Subgroup.pow_mem H hhH k))) u).mp
        hu.2⟩
  refine ⟨f, hf, hq, (hh : G), hh.2, hhV, ?_, ?_, ?_⟩
  · intro u hu
    have hpow : xToZ hVH (hh ^ (2 ^ f - 1)) = 1 := by rw [map_pow, hhx]; exact hord
    have hW := hs.mem_wOf_of_xToZ_eq_one hZ hpow
    rw [Subgroup.coe_pow] at hW
    have h1 := hc.wOf_comm hW hu.2
    calc (hh : G) ^ (2 ^ f - 1) * u * ((hh : G) ^ (2 ^ f - 1))⁻¹ =
        (u * (hh : G) ^ (2 ^ f - 1)) * ((hh : G) ^ (2 ^ f - 1))⁻¹ := by rw [h1]
      _ = u := by group
  · intro i hi0 hiq u hu hfix
    by_contra hu1
    obtain ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, ha₁1, ha₂1, hb12, hord₁, hord₂, hpr⟩ :=
      hprod i hi0 hiq
    obtain ⟨α₁, hα₁V, hα₁x⟩ := hs.exists_lift_VZ ha₁
    obtain ⟨α₂, hα₂V, hα₂x⟩ := hs.exists_lift_VZ ha₂
    obtain ⟨β₁, hβ₁U, hβ₁x⟩ := hs.exists_lift_conj_VZ hy₀X hb₁
    obtain ⟨β₂, hβ₂U, hβ₂x⟩ := hs.exists_lift_conj_VZ hy₀X hb₂
    have hα₁W : (α₁ : G) ∉ wOf V H := fun h =>
      ha₁1 (by rw [← hα₁x]; exact hs.xToZ_eq_one_of_mem_wOf h)
    have hα₂W : (α₂ : G) ∉ wOf V H := fun h =>
      ha₂1 (by rw [← hα₂x]; exact hs.xToZ_eq_one_of_mem_wOf h)
    have hsq₁ : a₁ * a₁ = 1 := by
      rw [← hα₁x, ← map_mul]
      have : α₁ * α₁ = 1 := Subtype.ext (hc.elemAb.mul_self_eq_one hα₁V)
      rw [this, map_one]
    have hsq₂ : a₂ * a₂ = 1 := by
      rw [← hα₂x, ← map_mul]
      have : α₂ * α₂ = 1 := Subtype.ext (hc.elemAb.mul_self_eq_one hα₂V)
      rw [this, map_one]
    have hβ₁W : (β₁ : G) ∉ wOf V H := fun h => by
      have hb1 : b₁ = 1 := by rw [← hβ₁x]; exact hs.xToZ_eq_one_of_mem_wOf h
      rw [hb1, mul_one] at hord₁
      have h5 : orderOf a₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq₁)
      rw [hord₁] at h5
      omega
    have hβ₂W : (β₂ : G) ∉ wOf V H := fun h => by
      have hb1 : b₂ = 1 := by rw [← hβ₂x]; exact hs.xToZ_eq_one_of_mem_wOf h
      rw [hb1, mul_one] at hord₂
      have h5 : orderOf a₂ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq₂)
      rw [hord₂] at h5
      omega
    have hbr₁ := hs.pow_three_mem_wOf hy₀X α₁ β₁ hα₁V hα₁W hβ₁U hβ₁W
      (by rw [hα₁x, hβ₁x]; exact hord₁)
    have hbr₂ := hs.pow_three_mem_wOf hy₀X α₂ β₂ hα₂V hα₂W hβ₂U hβ₂W
      (by rw [hα₂x, hβ₂x]; exact hord₂)
    have hker : xToZ hVH ((hh ^ i)⁻¹ * ((α₁ * β₁ * α₁) * (α₂ * β₂ * α₂))) = 1 := by
      rw [map_mul, map_inv, map_pow, hhx, ← hpr]
      simp only [map_mul, hα₁x, hβ₁x, hα₂x, hβ₂x]
      exact inv_mul_cancel _
    have hW := hs.mem_wOf_of_xToZ_eq_one hZ hker
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at hW
    set w : G := ((hh : G) ^ i)⁻¹ * ((α₁ * β₁ * α₁ : G) * (α₂ * β₂ * α₂ : G)) with hw
    have hprod_eq : (α₁ * β₁ * α₁ : G) * (α₂ * β₂ * α₂ : G) = (hh : G) ^ i * w := by
      rw [hw]; group
    have hfix' : ((α₁ : G) * β₁ * α₁) * ((α₂ : G) * β₂ * α₂) * u *
        (((α₁ : G) * β₁ * α₁) * ((α₂ : G) * β₂ * α₂))⁻¹ = u := by
      have h1 := hc.wOf_comm hW hu.2
      rw [hprod_eq]
      calc (hh : G) ^ i * w * u * ((hh : G) ^ i * w)⁻¹ =
          (hh : G) ^ i * (w * u) * w⁻¹ * ((hh : G) ^ i)⁻¹ := by group
        _ = (hh : G) ^ i * (u * w) * w⁻¹ * ((hh : G) ^ i)⁻¹ := by rw [h1]
        _ = (hh : G) ^ i * u * ((hh : G) ^ i)⁻¹ := by group
        _ = u := hfix
    have hbw := hs.braid_pair_semiregular hOppMeet h3 hy₀X hy₀c hα₁V hα₁W hβ₁U hβ₁W hbr₁ hα₂V
      hβ₂U hβ₂W hbr₂ hu hu1 hfix'
    have hxz : xToZ hVH (β₂ * β₁) = 1 := hs.xToZ_eq_one_of_mem_wOf (x := β₂ * β₁) hbw
    rw [map_mul, hβ₁x, hβ₂x] at hxz
    have hb₁sq : b₁ * b₁ = 1 := by
      rw [← hβ₁x, ← map_mul]
      have : β₁ * β₁ = 1 := Subtype.ext (hs.mul_self_of_mem_conj hβ₁U)
      rw [this, map_one]
    exact hb12 (mul_right_cancel (hxz.trans hb₁sq.symm)).symm
  · intro n hn hnV
    set nn : ↥(xOf V H) := ⟨n, hn⟩ with hnn
    have hnN := hs.xToZ_mem_normalizer (n := nn) hnV
    obtain ⟨i, _, hc', hm⟩ := hdec _ hnN
    refine ⟨i, fun u hu => ?_⟩
    have hcc' : nn * (hh ^ i)⁻¹ ∈ cenX V H := by
      apply hs.mem_cenX_of_centralizer hZ hSF
      rw [map_mul, map_inv, map_pow, hhx, hm, mul_inv_cancel_right]
      exact hc'
    have h1 := hcc' _ (hconjA i u hu)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hnn] at h1
    calc n * u * n⁻¹ = (n * ((hh : G) ^ i)⁻¹) * ((hh : G) ^ i * u * ((hh : G) ^ i)⁻¹) *
        (n * ((hh : G) ^ i)⁻¹)⁻¹ := by group
      _ = (hh : G) ^ i * u * ((hh : G) ^ i)⁻¹ := h1

end CFSG.RankThree.GF2n.Tim79a
