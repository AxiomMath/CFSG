module

public import CFSG.RankThree.GF2n.Tim79aSec33Defs
import CFSG.RankThree.GF2n.Tim79a32
import CFSG.RankThree.GF2n.Tim79aSec24CoreTilde
public import CFSG.RankThree.GF2n.Tim79aSec24Inner

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open scoped commutatorElement

variable {G : Type} [Group G]

theorem xToZ_mul_comm_of_commutator_mem_wOf {V H : Subgroup G} (hVH : V ≤ H)
    {a b : ↥(xOf V H)} (h : ⁅(a : G), (b : G)⁆ ∈ wOf V H) :
    xToZ hVH a * xToZ hVH b = xToZ hVH b * xToZ hVH a := by
  have hX : xToXbar hVH a * xToXbar hVH b = xToXbar hVH b * xToXbar hVH a := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_xToXbar]
    have h1 : piBar V H ⁅Subgroup.inclusion (xOf_le_H hVH) a,
        Subgroup.inclusion (xOf_le_H hVH) b⁆ = 1 := (piBar_eq_one_iff _).2 h
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  simp only [xToZ_apply, ← map_mul, hX]

theorem conj_mem_Ycomm {V H : Subgroup G} {m : G} (hmH : m ∈ H)
    (hmN : m ∈ Subgroup.normalizer (V : Set G)) {y : G} (hy : y ∈ Ycomm V H) :
    m * y * m⁻¹ ∈ Ycomm V H := by
  obtain ⟨hyX, hyc⟩ := hy
  refine ⟨(Subgroup.mem_normalizer_iff.mp (H_le_normalizer_xOf V H hmH) y).mp hyX,
    fun u hu w hw => ?_⟩
  have hu' : m⁻¹ * u * m ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmN) u).mp hu
    simpa using this
  have hw' : m⁻¹ * w * m ∈ conjSubgroup y V := by
    rw [mem_conjSubgroup]
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmN) _).mp
      (mem_conjSubgroup.mp hw)
    have e : y⁻¹ * (m⁻¹ * w * m) * y =
        m⁻¹ * ((m * y * m⁻¹)⁻¹ * w * (m * y * m⁻¹)) * m⁻¹⁻¹ := by group
    rw [e]
    exact h1
  have h3 := hyc _ hu' _ hw'
  have e : ⁅u, w⁆ = m * ⁅m⁻¹ * u * m, m⁻¹ * w * m⁆ * m⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hmH) _).mp h3

theorem conj_mem_Aof {V H : Subgroup G} {m : G} (hmH : m ∈ H)
    (hmN : m ∈ Subgroup.normalizer (V : Set G)) {y α : G} (hα : α ∈ Aof V H y) :
    m * α * m⁻¹ ∈ Aof V H (m * y * m⁻¹) := by
  obtain ⟨hαV, hαW⟩ := Subgroup.mem_inf.mp hα
  refine Subgroup.mem_inf.mpr ⟨?_,
    (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hmH) α).mp hαW⟩
  rw [mem_conjSubgroup]
  have h1 := (Subgroup.mem_normalizer_iff.mp hmN _).mp (mem_conjSubgroup.mp hαV)
  have e : (m * y * m⁻¹)⁻¹ * (m * α * m⁻¹) * (m * y * m⁻¹) = m * (y⁻¹ * α * y) * m⁻¹ := by
    group
  rw [e]
  exact h1

theorem conj_centralizes_Aof {V H : Subgroup G} {m : G} (hmH : m ∈ H)
    (hmN : m ∈ Subgroup.normalizer (V : Set G)) {s : G}
    (hs : ∀ y ∈ Ycomm V H, ∀ α ∈ Aof V H y, s * α = α * s) :
    ∀ y ∈ Ycomm V H, ∀ α ∈ Aof V H y, m * s * m⁻¹ * α = α * (m * s * m⁻¹) := by
  intro y hy α hα
  have hmH' : m⁻¹ ∈ H := H.inv_mem hmH
  have hmN' : m⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hmN
  have h := hs _ (conj_mem_Ycomm hmH' hmN' hy) _ (conj_mem_Aof hmH' hmN' hα)
  calc m * s * m⁻¹ * α = m * (s * (m⁻¹ * α * m⁻¹⁻¹)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * α * m⁻¹⁻¹) * s) * m⁻¹ := by rw [h]
    _ = α * (m * s * m⁻¹) := by group

theorem projZ_mul_xToZ_mul_inv {V H : Subgroup G} (hVH : V ≤ H) {m : ↥H} {b' : Xbar V H}
    (hb' : (b' : Hbar V H) = piBar V H m) (s : ↥(xOf V H))
    (hs : (m : G) * s * (m : G)⁻¹ ∈ xOf V H) :
    projZ V H b' * xToZ hVH s * (projZ V H b')⁻¹ =
      xToZ hVH ⟨(m : G) * s * (m : G)⁻¹, hs⟩ := by
  have e : b' * xToXbar hVH s * b'⁻¹ = xToXbar hVH ⟨(m : G) * s * (m : G)⁻¹, hs⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hb', coe_xToXbar, coe_xToXbar,
      ← map_inv, ← map_mul, ← map_mul]
    exact congrArg (piBar V H) (Subtype.ext rfl)
  rw [xToZ_apply, xToZ_apply, ← e, map_mul, map_mul, map_inv]

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem exists_mul_cPbar_of_xToZ_mem_VZ (hc : MinCex M V Q P H) {y : G} (hyP : y ∈ P)
    (hyX : y ∈ xOf V H) (hπ : xToZ hc.V_le_H ⟨y, hyX⟩ ∈ VZ V H) :
    ∃ v ∈ V, ∃ c ∈ cPbar V H P, y = v * c := by
  have hyH : y ∈ H := hc.PleH hyP
  obtain ⟨u, hu, hur⟩ := Subgroup.mem_map.mp hπ
  have hz : u⁻¹ * xToXbar hc.V_le_H ⟨y, hyX⟩ ∈ Subgroup.center (Xbar V H) := by
    have h1 : projZ V H (u⁻¹ * xToXbar hc.V_le_H ⟨y, hyX⟩) = 1 := by
      rw [map_mul, map_inv, hur, xToZ_apply, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨u', hu'V, hu'u⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hu)
  have hcP : (u' : G)⁻¹ * y ∈ P := P.mul_mem (P.inv_mem (hc.V_le_P hu'V)) hyP
  have hcX : (u' : G)⁻¹ * y ∈ cX V H := by
    refine ⟨H.mul_mem (H.inv_mem u'.2) hyH, fun x hx => ?_⟩
    have hxH : x ∈ H := xOf_le_H hc.V_le_H hx
    have hzc := Subgroup.mem_center_iff.mp hz
      ⟨piBar V H ⟨x, hxH⟩, mem_barOf_iff.mpr ⟨⟨x, hxH⟩, hx, rfl⟩⟩
    have hzc' : piBar V H ⟨x, hxH⟩ * ((u : Hbar V H)⁻¹ * piBar V H ⟨y, hyH⟩) =
        ((u : Hbar V H)⁻¹ * piBar V H ⟨y, hyH⟩) * piBar V H ⟨x, hxH⟩ := congrArg Subtype.val hzc
    have h1 : piBar V H ⁅u'⁻¹ * ⟨y, hyH⟩, (⟨x, hxH⟩ : ↥H)⁆ = 1 := by
      rw [map_commutatorElement, map_mul, map_inv, hu'u, commutatorElement_eq_one_iff_mul_comm]
      exact hzc'.symm
    exact (piBar_eq_one_iff _).1 h1
  exact ⟨(u' : G), hu'V, (u' : G)⁻¹ * y, Subgroup.mem_inf.mpr ⟨hcP, hcX⟩, by group⟩

theorem xToZ_mem_Rtilde_of_mem_P (hc : MinCex M V Q P H) {y : G} (hyP : y ∈ P)
    (hyX : y ∈ xOf V H) : xToZ hc.V_le_H ⟨y, hyX⟩ ∈ Rtilde V H P :=
  ⟨xToXbar hc.V_le_H ⟨y, hyX⟩, mem_Rbar.mpr (mem_barOf_iff.mpr ⟨⟨y, hc.PleH hyP⟩, hyP, rfl⟩),
    rfl⟩

theorem exists_lift_of_mem_normalizer_VZ (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    {b : XbarZ V H} (hb : b ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H))) :
    ∃ m : ↥H, (m : G) ∈ Subgroup.normalizer (V : Set G) ∧
      ∃ b' : Xbar V H, (b' : Hbar V H) = piBar V H m ∧ projZ V H b' = b := by
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Xbar V H)) b
  have hb'b : projZ V H b' = b := hb'
  subst hb'b
  have hN : b' ∈ Subgroup.normalizer (Vy V H : Set (Xbar V H)) :=
    hc.mem_normalizer_Vy_of_tilde hd hb
  rw [normalizer_Vy_eq, Subgroup.mem_subgroupOf] at hN
  have h1 := (Subgroup.mem_inf.mp hN).1
  rw [hc.normalizer_barOf_V] at h1
  obtain ⟨m, hmN, hmb⟩ := mem_barOf_iff.mp h1
  exact ⟨m, hmN, b', hmb.symm, rfl⟩

theorem mem_sup_Eof_of_centralizes_Aof (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hb : Sec24bTilde V H P) (hX : xOf V H ⊔ cPbar V H P = H)
    (hF : PairFacts (XbarZ V H) (VZ V H)) {x : G} (hxP : x ∈ P)
    (hx : ∀ y ∈ Ycomm V H, ∀ α ∈ Aof V H y, x * α = α * x) : x ∈ V ⊔ Eof V H P := by
  have hVH : V ≤ H := hc.V_le_H
  set S : Subgroup G := P ⊓ xOf V H ⊓
    Subgroup.centralizer {α | ∃ y ∈ Ycomm V H, α ∈ Aof V H y} with hSdef
  have memS : ∀ {s : G}, s ∈ S ↔
      s ∈ P ∧ s ∈ xOf V H ∧ ∀ y ∈ Ycomm V H, ∀ α ∈ Aof V H y, s * α = α * s := by
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
    refine memSt hmX (memS.mpr ⟨?_, hmX, conj_centralizes_Aof m.2 hmN hs'.2.2⟩)
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
      have hcα : c * α = α * c := hc.cPbar_centralizes_wOf hcC α (Subgroup.mem_inf.mp hα).2
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
    obtain ⟨a, ha, ha1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left
      (hc.conj_inf_wOf_ne_bot hyH)
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

theorem sec3CenterStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
      RootFacts (XbarZ V H) (VZ V H) →
      ∀ b ∈ P, (∀ x ∈ P, ⁅b, x⁆ ∈ V ⊓ wOf V H) → b ∈ V ⊔ Eof V H P := by
  intro G _ _ M V Q P H hs hF b hbP hb
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  obtain ⟨-, hX, -⟩ := hs.concl
  obtain ⟨u, huX, c, hcC, rfl⟩ := hc.exists_xOf_mul_cPbar hX hbP
  have hcP : c ∈ P := (Subgroup.mem_inf.mp hcC).1
  have huP : u ∈ P := by
    have e : u = u * c * c⁻¹ := by group
    rw [e]
    exact P.mul_mem hbP (P.inv_mem hcP)
  have hcomm : ∀ y ∈ P, ∀ hyX : y ∈ xOf V H,
      xToZ hc.V_le_H ⟨u, huX⟩ * xToZ hc.V_le_H ⟨y, hyX⟩ =
        xToZ hc.V_le_H ⟨y, hyX⟩ * xToZ hc.V_le_H ⟨u, huX⟩ := by
    intro y hyP hyX
    apply xToZ_mul_comm_of_commutator_mem_wOf
    have h1 : ⁅c⁻¹, y⁆ ∈ wOf V H := ((cX V H).inv_mem (Subgroup.mem_inf.mp hcC).2).2 y hyX
    have h2 : ⁅u * c, y⁆ ∈ wOf V H := (hb y hyP).2
    have e : ⁅u, y⁆ = (u * c) * ⁅c⁻¹, y⁆ * (u * c)⁻¹ * ⁅u * c, y⁆ := by
      simp only [commutatorElement_def]; group
    show ⁅u, y⁆ ∈ wOf V H
    rw [e]
    exact (wOf V H).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (H_le_normalizer_wOf V H (hc.PleH hbP)) _).mp h1) h2
  have hR : xToZ hc.V_le_H ⟨u, huX⟩ ∈ Rtilde V H P := hc.xToZ_mem_Rtilde_of_mem_P huP huX
  have hRc : ∀ z ∈ Rtilde V H P,
      xToZ hc.V_le_H ⟨u, huX⟩ * z = z * xToZ hc.V_le_H ⟨u, huX⟩ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hc.exists_mem_P_inf_xOf_of_mem_Rtilde hz
    exact hcomm y hy.1 hy.2
  have hb' : Rtilde V H P = pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) :=
    hs.tilde
  rw [hb'] at hR hRc
  obtain ⟨v, hv, c', hc', rfl⟩ :=
    hc.exists_mul_cPbar_of_xToZ_mem_VZ huP huX (hF.center _ hR hRc)
  have hcc : c' * c ∈ cPbar V H P := (cPbar V H P).mul_mem hc' hcC
  have hcE : c' * c ∈ Eof V H P :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hcc).1, Subgroup.mem_sup_right hcc⟩
  rw [mul_assoc]
  exact Subgroup.mul_mem_sup hv hcE

theorem sec3BetaStatement_holds : Sec3BetaStatement := by
  intro G _ _ M V Q P H hs hF x hxP hx
  obtain ⟨-, hX, -⟩ := hs.concl
  exact hs.setup.mc.toMinCex.mem_sup_Eof_of_centralizes_Aof hs.setup.data hs.tilde hX hF hxP hx

end CFSG.RankThree.GF2n.Tim79a
