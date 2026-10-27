module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordAux
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelC
import CFSG.LocalAnalysis.StandardType.GGSpFrameRank
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.Assembly
open CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7CKCoordAux_rank_eq_of_iso {lab lab' : LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) (htag' : lab'.tag = .B ∨ lab'.tag = .C)
    (h : GGLabelIso lab lab') : lab.rank = lab'.rank := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · rw [h]
  · exact h.2.2.1
  · obtain ⟨h1, -⟩ := h; rcases htag with hh | hh <;> rw [h1] at hh <;> simp at hh
  · obtain ⟨h1, -⟩ := h; rcases htag with hh | hh <;> rw [h1] at hh <;> simp at hh
  · obtain ⟨h1, -⟩ := h; rcases htag with hh | hh <;> rw [h1] at hh <;> simp at hh
  · obtain ⟨h1, -⟩ := h; rcases htag with hh | hh <;> rw [h1] at hh <;> simp at hh
  · obtain ⟨h1, -⟩ := h; rcases htag with hh | hh <;> rw [h1] at hh <;> simp at hh
  · obtain ⟨-, h2⟩ := h; rcases htag with hh | hh <;> rw [h2] at hh <;> simp at hh

private noncomputable def hdRo7CKCoordAux_quotAut (H : Type) [Group H] :
    MulAut H →* MulAut (H ⧸ Subgroup.center H) where
  toFun α := QuotientGroup.congr (Subgroup.center H) (Subgroup.center H) α
    (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]
  map_mul' := by
    intro α β
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]

private theorem hdRo7CKCoordAux_quotAut_injective (H : Type) [Group H]
    (hperf : commutator H = ⊤) : Function.Injective (hdRo7CKCoordAux_quotAut H) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [eq_bot_iff]
  intro α hα
  rw [MonoidHom.mem_ker] at hα
  have hfix : ∀ g : H, (α g)⁻¹ * g ∈ Subgroup.center H := by
    intro g
    have h1 : QuotientGroup.mk' (Subgroup.center H) (α g) =
        QuotientGroup.mk' (Subgroup.center H) g := by
      have := congrArg (fun f : MulAut (H ⧸ Subgroup.center H) =>
        f (QuotientGroup.mk' (Subgroup.center H) g)) hα
      simpa [hdRo7CKCoordAux_quotAut, QuotientGroup.congr_mk] using this
    rw [QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨w, hw, hwg⟩ := h1
    have : (α g)⁻¹ * g = w := by
      calc (α g)⁻¹ * g = (α g)⁻¹ * (α g * w) := by rw [hwg]
        _ = w := by rw [inv_mul_cancel_left]
    rw [this]
    exact hw
  let z : H →* H :=
    { toFun := fun g => (α g)⁻¹ * g
      map_one' := by simp
      map_mul' := by
        intro a b
        have hza : (α a)⁻¹ * a ∈ Subgroup.center H := hfix a
        have hzb : (α b)⁻¹ * b ∈ Subgroup.center H := hfix b
        have hcomm : (α a)⁻¹ * a * (α b)⁻¹ = (α b)⁻¹ * ((α a)⁻¹ * a) :=
          (Subgroup.mem_center_iff.mp hza (α b)⁻¹).symm
        calc (α (a * b))⁻¹ * (a * b)
            = (α b)⁻¹ * (α a)⁻¹ * (a * b) := by rw [map_mul, mul_inv_rev]
          _ = ((α b)⁻¹ * ((α a)⁻¹ * a)) * b := by group
          _ = (((α a)⁻¹ * a) * (α b)⁻¹) * b := by rw [hcomm]
          _ = ((α a)⁻¹ * a) * ((α b)⁻¹ * b) := by group }
  have hzle : z.range ≤ Subgroup.center H := by
    rintro _ ⟨g, rfl⟩
    exact hfix g
  have hker : commutator H ≤ z.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker]
    have ha := hzle (show z a ∈ z.range from ⟨a, rfl⟩)
    have hb := hzle (show z b ∈ z.range from ⟨b, rfl⟩)
    have hcomm : Commute (z a) (z b) :=
      (Subgroup.mem_center_iff.mp ha (z b)).symm
    rw [map_commutatorElement]
    exact hcomm.commutator_eq
  have hkertop : z.ker = ⊤ := by
    rw [← top_le_iff, ← hperf]
    exact hker
  have hz : z = 1 := by
    ext g
    exact MonoidHom.mem_ker.mp (hkertop ▸ Subgroup.mem_top g)
  ext g
  have hg : z g = 1 := by rw [hz]; rfl
  exact (inv_mul_eq_one.mp hg)

theorem hdRo7CKCoordAux_rankUpper (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowCorank2C p J K) (labK : LargeEvenLabel) (hlab : LargeEvenInLambda2 labK)
    (hKlab : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K)) (htag : labK.tag = .B ∨ labK.tag = .C)
    (hn1 : labK.n = 1) :
    Nat.card ↥Bs ≤ p ^ (labK.rank + 1) := by
  obtain ⟨labJ, labX, hJ2, hX2, hHasJ, hHasX, hp3, htagJ, hnJ, htagX, hnX, hrankJX⟩ := hrow
  have hrankKX : labK.rank = labX.rank :=
    hdRo7CKCoordAux_rank_eq_of_iso htag htagX
      (hRig labK labX (↥K ⧸ Subgroup.center ↥K) hlab hX2 hKlab hHasX)
  have hrankK : labK.rank = labJ.rank + 2 := by rw [hrankKX, hrankJX]
  have hp : p.Prime := hH.1.tableB_facts.1
  have hBs : GGBstar p B Bs := hH.1.2.1
  have hBs_ab : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hcardBs_le : Nat.card ↥Bs ≤ p * Nat.card ↥B := hBs.2.2.1
  have hB_le_Bs : B ≤ Bs := hBs.1
  have hstdPre : LargeEvenStdSubPre p B x L D J := hH.1.2.2.1
  have hD_le_B : D ≤ B := hstdPre.1
  have hDcard : Nat.card ↥D = p ^ 2 := hstdPre.2.2.1
  have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hstdPre.2.2.2.2.2.2
  have hJlayer : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hstdPre.2.2.2.2.1
  have hJcomp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hstdPre.2.2.2.2.2.1
  have hJperf : commutator ↥J = ⊤ := hJcomp.2.2.1
  have hBsN_L : Bs ≤ Subgroup.normalizer (L : Set G) := hH.2.2.1.1.le_normalizer
  have hBs_cent_D : Bs ≤ Subgroup.centralizer (D : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (IsElemAbelian.comm hBs_ab hb (hB_le_Bs (hD_le_B hd))).symm
  have hBsN_J : Bs ≤ Subgroup.normalizer (J : Set G) := by
    rw [hJlayer]
    refine le_normalizer_of_map_conj_le (fun g hg => map_conj_largeEvenLayer_le ?_)
    exact mem_normalizer_inf_centralizer (hBsN_L hg) (hBs_cent_D hg)
  let g : ↥Bs →* MulAut ↥J :=
    (Subgroup.normalizerMonoidHom J).comp (Subgroup.inclusion hBsN_J)
  have hker_le_C : Nat.card ↥g.ker ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
    have hle : g.ker.map Bs.subtype ≤ Bs ⊓ Subgroup.centralizer (J : Set G) := by
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨b.2, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr (fun j hj => ?_)
      have hbj : ((g b) ⟨j, hj⟩ : ↥J) = ⟨j, hj⟩ := by
        have := congrArg (fun f : MulAut ↥J => f ⟨j, hj⟩) hb
        simpa using this
      have hcoe : (((g b) ⟨j, hj⟩ : ↥J) : G) = b * j * b⁻¹ := rfl
      have h1 : b * j * b⁻¹ = j := by
        rw [← hcoe, hbj]
      have h2 : b * j = j * b := by
        have := congrArg (fun z : G => z * (b : G)) h1
        simpa [mul_assoc] using this
      exact h2.symm
    have h1 : Nat.card ↥(g.ker.map Bs.subtype) = Nat.card ↥g.ker :=
      Subgroup.card_map_of_injective Bs.subtype_injective
    rw [← h1]
    refine Nat.card_le_card_of_injective
      (fun z : ↥(g.ker.map Bs.subtype) =>
        (⟨z.1, hle z.2⟩ : ↥(Bs ⊓ Subgroup.centralizer (J : Set G)))) ?_
    intro a b hab
    exact Subtype.ext (congrArg (fun w : ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) => (w : G)) hab)
  have hcard_ker : Nat.card ↥g.ker ≤ p ^ 3 := by
    haveI : IsMulCommutative ↥Bs := hBs_ab.1
    let C : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
    let BsB : Subgroup ↥Bs := B.subgroupOf Bs
    haveI : BsB.Normal := Subgroup.normal_of_comm BsB
    let f : ↥C →* (↥Bs ⧸ BsB) :=
      (QuotientGroup.mk' BsB).comp (Subgroup.inclusion (inf_le_left : C ≤ Bs))
    have hfker : Nat.card ↥f.ker = Nat.card ↥D := by
      have hkerD : f.ker = D.subgroupOf C := by
        ext c
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        constructor
        · intro hc
          rw [hDeq]
          refine ⟨?_, c.2.2⟩
          have h1 := hc
          change QuotientGroup.mk' BsB
            (Subgroup.inclusion (inf_le_left : C ≤ Bs) c) = 1 at h1
          have h2 : (Subgroup.inclusion (inf_le_left : C ≤ Bs) c : ↥Bs) ∈ BsB := by
            rw [← QuotientGroup.ker_mk' BsB]
            exact MonoidHom.mem_ker.mpr h1
          rwa [Subgroup.mem_subgroupOf] at h2
        · intro hc
          rw [hDeq] at hc
          obtain ⟨hcB, hcCGJ⟩ := hc
          show QuotientGroup.mk' BsB
            (Subgroup.inclusion (inf_le_left : C ≤ Bs) c) = 1
          have h2 : (Subgroup.inclusion (inf_le_left : C ≤ Bs) c : ↥Bs) ∈ BsB := by
            rw [Subgroup.mem_subgroupOf]
            exact hcB
          rw [← QuotientGroup.ker_mk' BsB] at h2
          exact MonoidHom.mem_ker.mp h2
      have hDC : D ≤ C := by
        intro d hd
        refine ⟨hB_le_Bs (hD_le_B hd), ?_⟩
        have hd' := hd
        rw [hDeq] at hd'
        exact hd'.2
      rw [hkerD]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv
    have hfrange : Nat.card ↥f.range ≤ p := by
      have h1 : Nat.card ↥f.range ≤ BsB.index := by
        rw [Subgroup.index_eq_card BsB]
        exact Nat.card_le_card_of_injective (fun z : ↥f.range => (z : ↥Bs ⧸ BsB))
          Subtype.coe_injective
      rw [Subgroup.index_eq_card_div BsB] at h1
      have h2 : Nat.card ↥BsB = Nat.card ↥B :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_Bs).toEquiv
      rw [h2] at h1
      exact h1.trans (Nat.div_le_of_le_mul (by rw [mul_comm]; exact hcardBs_le))
    have hcard := Subgroup.card_ker_mul_card_range f
    rw [hfker, hDcard] at hcard
    calc Nat.card ↥g.ker ≤ Nat.card ↥C := hker_le_C
      _ = p ^ 2 * Nat.card ↥f.range := hcard.symm
      _ ≤ p ^ 2 * p := Nat.mul_le_mul_left _ hfrange
      _ = p ^ 3 := by ring
  have hm : 3 ≤ labJ.rank := by
    have h5 := hdRo7CLCoordAux_rank_ge_five hJ2 hnJ htagJ hrankJX
    omega
  have hmodel : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSp labJ.rank 2 labJ.n :=
    hdRo7CLCoordAux_statedClassicalModel_of_hasLabel_BC (f := labJ.n) htagJ hm (by omega) hHasJ
  obtain ⟨-, K', hK'field, hK'fin, hK'card, ⟨θ⟩⟩ := hmodel
  letI : Field K' := hK'field
  letI : Finite K' := hK'fin
  have hK'card2 : Nat.card K' = 2 := by rw [hK'card, hnJ]; norm_num
  haveI : CharP K' 2 :=
    charP_two_of_card (show Nat.card K' = 2 ^ 1 by rw [hK'card2]; norm_num)
  haveI : NeZero labJ.rank := ⟨by omega⟩
  have hPcenter : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K' labJ.rank)) = ⊥ :=
    TableBSymp.center_spProj_eq_bot
  have hcard_range : Nat.card ↥g.range ≤ p ^ labJ.rank := by
    have hgab : IsElemAbelian 3 g.range := by
      refine ⟨?_, ?_⟩
      · rw [isMulCommutative_iff]
        intro a b
        obtain ⟨x, hxeq⟩ := MonoidHom.mem_range.mp a.2
        obtain ⟨y, hyeq⟩ := MonoidHom.mem_range.mp b.2
        apply Subtype.ext
        change a.1 * b.1 = b.1 * a.1
        rw [show a.1 = g x from hxeq.symm, show b.1 = g y from hyeq.symm, ← map_mul, ← map_mul]
        exact congrArg g (hBs_ab.1.is_comm.comm x y)
      · intro a ha
        obtain ⟨x, hxeq⟩ := MonoidHom.mem_range.mp ha
        have hx3 : x ^ 3 = 1 := by
          apply Subtype.ext
          rw [← hp3]
          simpa using hBs_ab.2 x.1 x.2
        rw [show a = g x from hxeq.symm, ← map_pow, hx3, map_one]
    have hΦinj : Function.Injective (hdRo7CKCoordAux_quotAut ↥J) :=
      hdRo7CKCoordAux_quotAut_injective ↥J hJperf
    let Q := ↥J ⧸ Subgroup.center ↥J
    let Φ : MulAut ↥J →* MulAut Q := hdRo7CKCoordAux_quotAut ↥J
    let E : Subgroup (MulAut Q) := g.range.map Φ
    have hEcard : Nat.card ↥E = Nat.card ↥g.range :=
      Subgroup.card_map_of_injective hΦinj
    have hEab : IsElemAbelian 3 E := hgab.map Φ
    let P := LargeEvenProj (LargeEvenSpGroup K' labJ.rank)
    let A : Subgroup (MulAut P) := E.map (MulAut.congr θ).toMonoidHom
    have hAcard : Nat.card ↥A = Nat.card ↥E :=
      Subgroup.card_map_of_injective (MulAut.congr θ).injective
    have hAab : IsElemAbelian 3 A := hEab.map (MulAut.congr θ).toMonoidHom
    have hAle : A ≤ (MulAut.conj : P →* MulAut P).range := by
      rintro x ⟨y, -, rfl⟩
      exact TwoThree.mem_range_conj_sp hK'card2 hm ((MulAut.congr θ) y)
    let A' : Subgroup P := A.comap (MulAut.conj : P →* MulAut P)
    have hconjinj : Function.Injective (MulAut.conj : P →* MulAut P) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [eq_bot_iff]
      intro s hs
      rw [MonoidHom.mem_ker] at hs
      have hc : s ∈ Subgroup.center P := by
        rw [Subgroup.mem_center_iff]
        intro t
        have h1 : s * t * s⁻¹ = t := by
          have := congrArg (fun f : MulAut P => f t) hs
          simpa [MulAut.conj_apply] using this
        have h2 : s * t = t * s := by
          have := congrArg (fun z => z * s) h1
          simpa [mul_assoc] using this
        exact h2.symm
      rw [hPcenter] at hc
      simpa using hc
    have hA'card : Nat.card ↥A' = Nat.card ↥g.range := by
      have h1 : Nat.card ↥A' = Nat.card ↥A := by
        rw [← Subgroup.card_map_of_injective (K := A') hconjinj]
        rw [Subgroup.map_comap_eq_self hAle]
      rw [h1, hAcard, hEcard]
    have hA'ab : IsElemAbelian 3 A' := hAab.comap hconjinj
    have hbound := TwoThree.card_sq_le_sp hK'card2 hA'ab
    have hhalf := TwoThree.card_le_pow_half hA'ab hbound
    rw [hA'card] at hhalf
    rw [hp3]
    convert hhalf using 2
    exact (Nat.mul_div_cancel_left labJ.rank (by norm_num : 0 < 2)).symm
  have hcardBs := Subgroup.card_ker_mul_card_range g
  calc Nat.card ↥Bs = Nat.card ↥g.ker * Nat.card ↥g.range := hcardBs.symm
    _ ≤ p ^ 3 * p ^ labJ.rank := Nat.mul_le_mul hcard_ker hcard_range
    _ = p ^ (labJ.rank + 3) := by rw [mul_comm, ← pow_add]
    _ = p ^ (labK.rank + 1) := by rw [hrankK]

end CFSG.StandardType.HdRo7C

end
