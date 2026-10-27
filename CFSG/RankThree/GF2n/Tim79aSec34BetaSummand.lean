module

public import CFSG.RankThree.GF2n.Tim79aSec33Beta
import CFSG.RankThree.GF2n.Tim79a32

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_mem_conjSubgroup_inf_of_invariant {V H W₁ : Subgroup G} {m : G} (hmH : m ∈ H)
    (hmN : m ∈ Subgroup.normalizer (V : Set G)) (hW₁ : ∀ h ∈ H, conjSubgroup h W₁ = W₁)
    {y α : G} (hα : α ∈ conjSubgroup y V ⊓ W₁) :
    m * α * m⁻¹ ∈ conjSubgroup (m * y * m⁻¹) V ⊓ W₁ := by
  obtain ⟨hαV, hαW⟩ := Subgroup.mem_inf.mp hα
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_conjSubgroup]
    have h1 := (Subgroup.mem_normalizer_iff.mp hmN _).mp (mem_conjSubgroup.mp hαV)
    have e : (m * y * m⁻¹)⁻¹ * (m * α * m⁻¹) * (m * y * m⁻¹) = m * (y⁻¹ * α * y) * m⁻¹ := by
      group
    rw [e]
    exact h1
  · have h1 : m * α * m⁻¹ ∈ conjSubgroup m W₁ := by
      rw [mem_conjSubgroup]
      have e : m⁻¹ * (m * α * m⁻¹) * m = α := by group
      rw [e]
      exact hαW
    rwa [hW₁ m hmH] at h1

theorem conj_centralizes_conjSubgroup_inf {V H W₁ : Subgroup G} {m : G} (hmH : m ∈ H)
    (hmN : m ∈ Subgroup.normalizer (V : Set G)) (hW₁ : ∀ h ∈ H, conjSubgroup h W₁ = W₁)
    {s : G} (hs : ∀ y ∈ Ycomm V H, ∀ α ∈ conjSubgroup y V ⊓ W₁, s * α = α * s) :
    ∀ y ∈ Ycomm V H, ∀ α ∈ conjSubgroup y V ⊓ W₁, m * s * m⁻¹ * α = α * (m * s * m⁻¹) := by
  intro y hy α hα
  have hmH' : m⁻¹ ∈ H := H.inv_mem hmH
  have hmN' : m⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hmN
  have h := hs _ (conj_mem_Ycomm hmH' hmN' hy) _
    (conj_mem_conjSubgroup_inf_of_invariant hmH' hmN' hW₁ hα)
  calc m * s * m⁻¹ * α = m * (s * (m⁻¹ * α * m⁻¹⁻¹)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * α * m⁻¹⁻¹) * s) * m⁻¹ := by rw [h]
    _ = α * (m * s * m⁻¹) := by group

theorem exists_ne_one_mem_conjSubgroup_inf {V H W₁ : Subgroup G}
    (hW₁ : ∀ h ∈ H, conjSubgroup h W₁ = W₁) (hVW₁ : V ⊓ W₁ ≠ ⊥) {y : G} (hy : y ∈ H) :
    ∃ a ∈ conjSubgroup y V ⊓ W₁, a ≠ 1 := by
  obtain ⟨a, ha, ha1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hVW₁
  obtain ⟨haV, haW⟩ := Subgroup.mem_inf.mp ha
  have e : y⁻¹ * (y * a * y⁻¹) * y = a := by group
  refine ⟨y * a * y⁻¹, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [mem_conjSubgroup, e]
    exact haV
  · have h1 : y * a * y⁻¹ ∈ conjSubgroup y W₁ := by
      rw [mem_conjSubgroup, e]
      exact haW
    rwa [hW₁ y hy] at h1
  · intro h
    apply ha1
    rw [← e, h]
    group

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem mem_sup_Eof_of_centralizes_inf (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hb : Sec24bTilde V H P) (hX : xOf V H ⊔ cPbar V H P = H)
    (hF : PairFacts (XbarZ V H) (VZ V H)) {W₁ : Subgroup G} (hW₁W : W₁ ≤ wOf V H)
    (hW₁ : ∀ h ∈ H, conjSubgroup h W₁ = W₁) (hVW₁ : V ⊓ W₁ ≠ ⊥) {x : G} (hxP : x ∈ P)
    (hx : ∀ y ∈ Ycomm V H, ∀ α ∈ conjSubgroup y V ⊓ W₁, x * α = α * x) :
    x ∈ V ⊔ Eof V H P := by
  have hVH : V ≤ H := hc.V_le_H
  set S : Subgroup G := P ⊓ xOf V H ⊓
    Subgroup.centralizer {α | ∃ y ∈ Ycomm V H, α ∈ conjSubgroup y V ⊓ W₁} with hSdef
  have memS : ∀ {s : G}, s ∈ S ↔ s ∈ P ∧ s ∈ xOf V H ∧
      ∀ y ∈ Ycomm V H, ∀ α ∈ conjSubgroup y V ⊓ W₁, s * α = α * s := by
    intro s
    rw [hSdef, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, fun y hy α hα => (h3 α ⟨y, hy, hα⟩).symm⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun α ⟨y, hy, hα⟩ => (h3 y hy α hα).symm⟩
  set St : Subgroup (XbarZ V H) := (S.subgroupOf (xOf V H)).map (xToZ hVH)
  have memSt : ∀ {s : G} (hsX : s ∈ xOf V H), s ∈ S → xToZ hVH ⟨s, hsX⟩ ∈ St :=
    fun hsX hs => Subgroup.mem_map.mpr ⟨⟨_, hsX⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  have hQ : Rtilde V H P = pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) := hb
  have hVS : VZ V H ≤ St := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := hc.exists_mem_V_of_mem_VZ hr
    refine memSt _ (memS.mpr ⟨hc.V_le_P hv, le_xOf (V_mem_omegaOf V H) hv,
      fun y hy α hα => ?_⟩)
    obtain ⟨hyX, hyc⟩ := hy
    exact hc.commute_conj_of_commutator_mem_wOf H.one_mem (xOf_le_H hVH hyX)
      (fun a ha b hb => hyc a (by rwa [conjSubgroup_one] at ha) b hb) v
      (by rw [conjSubgroup_one]; exact hv) α (Subgroup.mem_inf.mp hα).1
  have hSQ : St ≤ pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) := by
    rw [← hQ]
    rintro r ⟨s, hs, rfl⟩
    exact hc.xToZ_mem_Rtilde_of_mem_P (memS.mp (Subgroup.mem_subgroupOf.mp hs)).1 s.2
  have hSN : ∀ b ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H)), ∀ r ∈ St,
      b * r * b⁻¹ ∈ St := by
    intro b hbN r hr
    obtain ⟨m, hmN, b', hb'm, rfl⟩ := hc.exists_lift_of_mem_normalizer_VZ hd hbN
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hr
    have hs' := memS.mp (Subgroup.mem_subgroupOf.mp hs)
    have hmX : (m : G) * s * (m : G)⁻¹ ∈ xOf V H :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_xOf V H m.2) s).mp s.2
    rw [projZ_mul_xToZ_mul_inv hVH hb'm s hmX]
    refine memSt hmX (memS.mpr ⟨?_, hmX, conj_centralizes_conjSubgroup_inf m.2 hmN hW₁ hs'.2.2⟩)
    exact (Subgroup.mem_normalizer_iff.mp
      (hc.M_le_normalizer_P (hc.normalizer_eq ▸ hmN)) s).mp hs'.1
  rcases hF.irr St hVS hSQ hSN with hSt | hSt
  ·
    obtain ⟨u, huX, c, hcC, rfl⟩ := hc.exists_xOf_mul_cPbar hX hxP
    have hcP : c ∈ P := (Subgroup.mem_inf.mp hcC).1
    have huP : u ∈ P := by
      have e : u = u * c * c⁻¹ := by group
      rw [e]
      exact P.mul_mem hxP (P.inv_mem hcP)
    have huS : u ∈ S := by
      refine memS.mpr ⟨huP, huX, fun y hy α hα => ?_⟩
      have hcα : c * α = α * c :=
        hc.cPbar_centralizes_wOf hcC α (hW₁W (Subgroup.mem_inf.mp hα).2)
      have hxα := hx y hy α hα
      calc u * α = u * c * α * c⁻¹ := by rw [mul_assoc u c α, hcα]; group
        _ = α * (u * c) * c⁻¹ := by rw [hxα]
        _ = α * u := by group
    have hu := memSt huX huS
    rw [hSt] at hu
    obtain ⟨v, hv, c', hc', rfl⟩ := hc.exists_mul_cPbar_of_xToZ_mem_VZ huP huX hu
    have hcc : c' * c ∈ cPbar V H P := (cPbar V H P).mul_mem hc' hcC
    have hcE : c' * c ∈ Eof V H P :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hcc).1, Subgroup.mem_sup_right hcc⟩
    rw [mul_assoc]
    exact Subgroup.mul_mem_sup hv hcE
  ·
    exfalso
    obtain ⟨g, hgC, hgne, x₀, hx₀, t, ht, hxt⟩ := hF.moves
    obtain ⟨⟨y, hyX⟩, rfl⟩ := xToZ_surjective hVH g
    have hyH : y ∈ H := xOf_le_H hVH hyX
    have hy : y ∈ Ycomm V H := by
      refine ⟨hyX, fun u hu w hw => ?_⟩
      have h := hc.commute_conj_of_commute_tilde (x₁ := 1) (x₂ := ⟨y, hyX⟩) (by
        intro a ha b hb
        rw [map_one, conjSubgroup_one] at ha
        exact Subgroup.mem_centralizer_iff.mp (hgC hb) a ha)
      have huw := h u (by rw [OneMemClass.coe_one, conjSubgroup_one]; exact hu) w hw
      rw [commutatorElement_eq_one_iff_mul_comm.mpr huw]
      exact (wOf V H).one_mem
    have hx₀Q := hx₀
    rw [← hSt] at hx₀
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx₀
    have hs' := memS.mp (Subgroup.mem_subgroupOf.mp hs)
    obtain ⟨a, ha, ha1⟩ := exists_ne_one_mem_conjSubgroup_inf hW₁ hVW₁ hyH
    have hsN : (s : G) ∈ Subgroup.normalizer (conjSubgroup y V : Set G) :=
      Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti y)
        (Subgroup.mem_inf.mp ha).1 ha1 (hs'.2.2 y hy a ha)
    set T : Subgroup (XbarZ V H) := conjSubgroup (xToZ hVH ⟨y, hyX⟩) (VZ V H) with hTdef
    have hT : conjSubgroup (xToZ hVH s) T = T := by
      rw [hTdef, conjSubgroup_conjSubgroup, ← map_mul, ← imgZ_conj hVH, ← imgZ_conj hVH]
      congr 1
      show conjSubgroup ((s : G) * y) V = conjSubgroup y V
      rw [← conjSubgroup_conjSubgroup]
      exact mem_normalizer_iff_conjSubgroup_eq.mp hsN
    have htT : t ∈ T := ht
    have hx₀T : xToZ hVH s * t * (xToZ hVH s)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_iff_conjSubgroup_eq.mpr hT) t).mp htT
    have htN : t ∈ Subgroup.normalizer
        ((pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) : Subgroup (XbarZ V H)) :
          Set (XbarZ V H)) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
        (Subgroup.centralizer_le_normalizer _ (hgC ht))
    have hk : xToZ hVH s * t * (xToZ hVH s)⁻¹ * t⁻¹ ∈
        conjSub (VZ V H) (xToZ hVH ⟨y, hyX⟩) ⊓
          pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) := by
      refine Subgroup.mem_inf.mpr ⟨T.mul_mem hx₀T (T.inv_mem htT), ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp htN _).mp (Subgroup.inv_mem _ hx₀Q)
      have e : xToZ hVH s * t * (xToZ hVH s)⁻¹ * t⁻¹ =
          xToZ hVH s * (t * (xToZ hVH s)⁻¹ * t⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx₀Q h1
    rw [hF.disjoint _ hgC hgne, Subgroup.mem_bot] at hk
    apply hxt
    calc xToZ hVH s * t = (xToZ hVH s * t * (xToZ hVH s)⁻¹ * t⁻¹) * (t * xToZ hVH s) := by
          group
      _ = t * xToZ hVH s := by rw [hk, one_mul]

end MinCex

theorem sec3BetaSummandStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G) (W₁ : Subgroup G),
      Sec3Setup M V Q P H → PairFacts (XbarZ V H) (VZ V H) → W₁ ≤ wOf V H →
      (∀ h ∈ H, conjSubgroup h W₁ = W₁) → V ⊓ W₁ ≠ ⊥ →
      ∀ x ∈ P, (∀ y ∈ Ycomm V H, ∀ α ∈ conjSubgroup y V ⊓ W₁, x * α = α * x) → x ∈ V ⊔ Eof V H P := by
  intro G _ _ M V Q P H W₁ hs hF hW₁W hW₁ hVW₁ x hxP hx
  obtain ⟨-, hX, -⟩ := hs.concl
  exact hs.setup.mc.toMinCex.mem_sup_Eof_of_centralizes_inf hs.setup.data hs.tilde hX hF hW₁W
    hW₁ hVW₁ hxP hx

end CFSG.RankThree.GF2n.Tim79a
