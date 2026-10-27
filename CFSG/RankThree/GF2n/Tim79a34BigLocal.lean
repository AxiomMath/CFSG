module

public import CFSG.RankThree.GF2n.Tim79a34BigEnd
import CFSG.RankThree.GF2n.Tim79a34MemberUnique
import CFSG.RankThree.GF2n.Tim79a34IW
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GF2n.Tim79aSec2
public import CFSG.RankThree.GF2n.Tim79aSec34Torus

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}

theorem BigEndHyp.card_V (h : BigEndHyp M V Q P H) : Nat.card ↥V = qBar V H ^ 2 := by
  have h1 := twb_card_barOf_mul (V := V) (H := H) (K := V) h.setup.mc.toMinCex.V_le_H
  rw [h.module] at h1
  rw [← h1]
  simp only [qBar]
  ring

theorem MinCex.conjSubgroup_inf_wOf_le_normalizer (hc : MinCex M V Q P H) {g : G} :
    conjSubgroup g V ⊓ wOf V H ≤
      Subgroup.normalizer ((P ⊓ wOf V H : Subgroup G) : Set G) := by
  intro b hb
  rw [mem_normalizer_iff_conjSubgroup_eq]
  ext p
  rw [mem_conjSubgroup]
  constructor
  · intro hp
    have hqW : b⁻¹ * p * b ∈ wOf V H := (Subgroup.mem_inf.mp hp).2
    have heq : p = b⁻¹ * p * b := by
      calc p = b * (b⁻¹ * p * b) * b⁻¹ := by group
        _ = b⁻¹ * p * b := by rw [hc.wOf_comm hb.2 hqW]; group
    rw [heq]; exact hp
  · intro hp
    have heq : b⁻¹ * p * b = p := by
      rw [hc.wOf_comm ((wOf V H).inv_mem hb.2) (Subgroup.mem_inf.mp hp).2]; group
    rw [heq]; exact hp

theorem BigEndHyp.wOf_inf_centralizer_eq (h : BigEndHyp M V Q P H) :
    wOf V H ⊓ Subgroup.centralizer (V : Set G) = P ⊓ wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hge : P ⊓ wOf V H ≤ wOf V H ⊓ Subgroup.centralizer (V : Set G) := by
    intro p hp
    obtain ⟨hpP, hpW⟩ := Subgroup.mem_inf.mp hp
    exact Subgroup.mem_inf.mpr ⟨hpW,
      Subgroup.mem_centralizer_iff.mpr fun v hv => hc.commute_of_mem_P hpP hv⟩
  refine le_antisymm ?_ hge
  intro x hx
  obtain ⟨hxW, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨g, hgX, u, huV, w, hwU, hnc⟩ := hc.exists_noncomm_conj h.setup.data
  obtain ⟨-, hW, -⟩ := h.concl.1 g hgX ⟨u, huV, w, hwU, hnc⟩
  obtain ⟨p, hp, b, hb, hxb⟩ :=
    exists_mul_of_mem_sup (hc.conjSubgroup_inf_wOf_le_normalizer (g := g)) (hW.symm ▸ hxW)
  have hbC : b ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hpC : p⁻¹ * v = v * p⁻¹ := by
      have hpv : v * p = p * v := hc.commute_of_mem_P hp.1 hv
      calc p⁻¹ * v = p⁻¹ * (v * p) * p⁻¹ := by group
        _ = p⁻¹ * (p * v) * p⁻¹ := by rw [hpv]
        _ = v * p⁻¹ := by group
    have hxv : v * x = x * v := Subgroup.mem_centralizer_iff.mp hxC v hv
    have hb_eq : b = p⁻¹ * x := by rw [hxb]; group
    rw [hb_eq]
    calc v * (p⁻¹ * x) = (v * p⁻¹) * x := by group
      _ = (p⁻¹ * v) * x := by rw [hpC]
      _ = p⁻¹ * (v * x) := by group
      _ = p⁻¹ * (x * v) := by rw [hxv]
      _ = (p⁻¹ * x) * v := by group
  by_cases hb1 : b = 1
  · refine Subgroup.mem_inf.mpr ⟨?_, hxW⟩
    have hxp : x = p := by rw [hxb, hb1, mul_one]
    rw [hxp]; exact hp.1
  · exfalso
    have hconjV : conjSubgroup g⁻¹ (conjSubgroup g V) = V := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have hVN : V ≤ Subgroup.normalizer (conjSubgroup g V : Set G) := by
      intro v hv
      exact Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti g) hb.1 hb1
        (Subgroup.mem_centralizer_iff.mp hbC v hv)
    have hEA : Assembly.IsElemAbelian 2 (conjSubgroup g V) :=
      isElemAbelian_conjSubgroup hc.elemAb g
    have hstep := Tim77.tim77_2_3 (A := conjSubgroup g V) hEA (isTI_conjSubgroup hc.ti g)
      (g := g⁻¹) (by rw [hconjV]; exact hVN)
    rw [hconjV] at hstep
    have hcomm : u * w = w * u := hstep.comm (Subgroup.mem_sup_right huV)
      (Subgroup.mem_sup_left hwU)
    exact hnc (by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
      exact (wOf V H).one_mem)

theorem MinCex.conjSubgroup_eq_of_barOf_eq (hc : MinCex M V Q P H) {x : G} (hx : x ∈ H)
    (hb : barOf V H (conjSubgroup x V) = barOf V H V) : conjSubgroup x V = V := by
  have hmemN : piBar V H ⟨x, hx⟩ ∈
      Subgroup.normalizer ((barOf V H V : Subgroup (Hbar V H)) : Set (Hbar V H)) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_piBar_barOf]
    exact hb
  rw [hc.sec2.normalizer_bar] at hmemN
  obtain ⟨y, hyN, hyx⟩ := mem_barOf_iff.mp hmemN
  have hyx' : piBar V H ⟨x, hx⟩ = piBar V H y := hyx.symm
  have hxW : x * (y : G)⁻¹ ∈ wOf V H := by
    have h1 : piBar V H ((⟨x, hx⟩ : ↥H) * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hyx', mul_inv_cancel]
    exact (piBar_eq_one_iff ((⟨x, hx⟩ : ↥H) * y⁻¹)).mp h1
  have hWN : wOf V H ≤ Subgroup.normalizer (V : Set G) := by
    simpa [conjSubgroup_one] using memberUnique_wOf_le_normalizer hc (g := 1) H.one_mem
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := by
    have h1 : x * (y : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) := hWN hxW
    have h2 : (y : G) ∈ Subgroup.normalizer (V : Set G) := hyN
    have h3 := (Subgroup.normalizer (V : Set G)).mul_mem h1 h2
    simpa [mul_assoc] using h3
  exact mem_normalizer_iff_conjSubgroup_eq.mp hxN

theorem BigEndHyp.isSimpleGroup_xbar (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) : IsSimpleGroup (Xbar V H) := by
  obtain ⟨f, hf, hq, n, hn, Φ, hΦ, -⟩ := h.three
  let Ψ : Xbar V H ≃* XbarZ V H := MulEquiv.ofBijective (projZ V H) (iw_projZ_bijective hZ)
  let e : StatedSp n (GaloisField 2 f) ≃* Xbar V H :=
    (MulEquiv.ofBijective Φ hΦ).trans Ψ.symm
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by rw [hcardF, hq]; exact h.q_big
  have hSp : CFSG.IsQuasisimple (StatedSp n (GaloisField 2 f)) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple n (GaloisField 2 f) (by omega)
      (Or.inl (Or.inr h4))
  have hQ : CFSG.IsQuasisimple (Xbar V H) := CFSG.IsQuasisimple.of_mulEquiv e.symm hSp
  haveI : IsSimpleGroup (XbarZ V H) := hQ.2.1
  exact MulEquiv.isSimpleGroup Ψ

theorem BigEndHyp.mem_wOf_of_commute (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {x : G} (hx : x ∈ xOf V H)
    (hxW : ∀ w ∈ wOf V H, x * w = w * x) : x ∈ wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  haveI hsimple : IsSimpleGroup (Xbar V H) := h.isSimpleGroup_xbar hZ
  set N : Subgroup G := xOf V H ⊓ Subgroup.centralizer (wOf V H : Set G) with hN
  have hxN : x ∈ N :=
    Subgroup.mem_inf.mpr ⟨hx,
      Subgroup.mem_centralizer_iff.mpr fun w hw => (hxW w hw).symm⟩
  have hXN : xOf V H ≤ Subgroup.normalizer (N : Set G) := by
    intro y hy
    exact mem_normalizer_inf (Subgroup.le_normalizer hy)
      (mem_normalizer_centralizer (H_le_normalizer_wOf V H (xOf_le_H hc.V_le_H hy)))
  set K : Subgroup (Xbar V H) := (barOf V H N).subgroupOf (barOf V H (xOf V H)) with hK
  have hKN : K.Normal := by
    rw [hK]
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (barOf_mono inf_le_left)).2 ?_
    intro g hg
    obtain ⟨y, hyX, hyg⟩ := mem_barOf_iff.mp hg
    rw [mem_normalizer_iff_conjSubgroup_eq, ← hyg, conjSubgroup_piBar_barOf,
      mem_normalizer_iff_conjSubgroup_eq.mp (hXN hyX)]
  haveI : K.Normal := hKN
  rcases hsimple.eq_bot_or_eq_top_of_normal K with hbot | htop
  · have hxK : xToXbar hc.V_le_H ⟨x, hx⟩ ∈ K :=
      Subgroup.mem_subgroupOf.mpr
        (mem_barOf_iff.mpr ⟨⟨x, xOf_le_H hc.V_le_H hx⟩, hxN, rfl⟩)
    rw [hbot] at hxK
    have h1 : xToXbar hc.V_le_H ⟨x, hx⟩ = 1 := Subgroup.mem_bot.mp hxK
    exact (piBar_eq_one_iff _).mp (by
      simpa [coe_xToXbar] using
        congrArg (Subtype.val : Xbar V H → Hbar V H) h1)
  · exfalso
    have hcomm : wOf V H ≤ Subgroup.centralizer (xOf V H : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyH : y ∈ H := xOf_le_H hc.V_le_H hy
      have hyK : xToXbar hc.V_le_H ⟨y, hy⟩ ∈ K := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨n, hnN, hny⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hyK)
      have hny' : piBar V H ⟨y, hyH⟩ = piBar V H n := by
        rw [coe_xToXbar] at hny
        exact hny.symm
      have hyn : y * (n : G)⁻¹ ∈ wOf V H := by
        have h1 : piBar V H ((⟨y, hyH⟩ : ↥H) * n⁻¹) = 1 := by
          rw [map_mul, map_inv, hny', mul_inv_cancel]
        exact (piBar_eq_one_iff ((⟨y, hyH⟩ : ↥H) * n⁻¹)).mp h1
      have hnW : (n : G) * w = w * (n : G) :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hnN).2 w hw).symm
      calc y * w = ((y * (n : G)⁻¹) * (n : G)) * w := by group
        _ = (y * (n : G)⁻¹) * ((n : G) * w) := by group
        _ = (y * (n : G)⁻¹) * (w * (n : G)) := by rw [hnW]
        _ = ((y * (n : G)⁻¹) * w) * (n : G) := by group
        _ = (w * (y * (n : G)⁻¹)) * (n : G) := by rw [hc.wOf_comm hyn hw]
        _ = w * y := by group
    have hbot : ⁅wOf V H, xOf V H⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcomm
    rw [hc.commutator_wOf_xOf] at hbot
    exact hc.V_inf_wOf_ne_bot (by rw [hbot, inf_bot_eq])

theorem BigEndHyp.commute_of_bar_centralizes (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {x : G} (hx : x ∈ xOf V H)
    (hxV : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ wOf V H) :
    ∀ a ∈ V ⊓ wOf V H, x * a = a * x := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hs : Sec3Setup M V Q P H := ⟨h.setup, h.tilde, h.concl⟩
  have hSp : ClassicalRootSp (XbarZ V H) (VZ V H) := by
    obtain ⟨f, hf, -, hT⟩ := h.three
    exact ⟨f, rootClassZ V H, hf, hT, VZ_mem_rootClassZ V H⟩
  have hSF : StabFacts (XbarZ V H) (VZ V H) :=
    spStabStatement_of_model (XbarZ V H) (VZ V H) hSp
  have hxcen : xToZ hc.V_le_H ⟨x, hx⟩ ∈
      Subgroup.centralizer (VZ V H : Set (XbarZ V H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨v, hv, rfl⟩ := hc.exists_mem_V_of_mem_VZ hy
    exact (xToZ_mul_comm_of_commutator_mem_wOf hc.V_le_H
      (a := ⟨x, hx⟩) (b := ⟨v, le_xOf (V_mem_omegaOf V H) hv⟩)
      (by simpa [commutatorElement_def] using hxV v hv)).symm
  have hmem : (⟨x, hx⟩ : ↥(xOf V H)) ∈ cenX V H :=
    hs.mem_cenX_of_centralizer hZ hSF hxcen
  intro a ha
  have h1 : x * a * x⁻¹ = a := hmem a ha
  calc x * a = (x * a * x⁻¹) * x := by group
    _ = a * x := by rw [h1]

end CFSG.RankThree.GF2n.Tim79a
