module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixX
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixBase
public import CFSG.LocalAnalysis.StandardType.GGNsq2U62
public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm
import CFSG.LocalAnalysis.StandardType.GGNsq2PairLift
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotAut
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotCover
import CFSG.LocalAnalysis.StandardType.GGNsq2Main
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrSixEdge
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitRankTwo
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitXTransA
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixDel
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixCommon
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixComp
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixNbr
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux
import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
import CFSG.ClassicalGroups.Unitary.SUThreeTwoDiagHom

public section

namespace CFSG.StandardType

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]

theorem Datum.le_of_img_le_of_fix {p : ℕ} {N L Bs Z : Subgroup G} {f : ↥N →* Q}
    (hD : Datum p N f L Bs Z) {J S H : Subgroup G} (hJZ : ∀ j ∈ J, j ∈ Z → j = 1) (hSL : S ≤ L)
    (hSH : S ≤ Subgroup.centralizer (H : Set G)) (hHBs : H ≤ Bs)
    (hHJ : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J)
    (hfix : ∀ z ∈ Z, (∀ h ∈ H, h * z = z * h) → z = 1)
    (himg : img N f S ≤ img N f J) : S ≤ J := by
  intro y hy
  have hyN : y ∈ N := hD.LN (hSL hy)
  obtain ⟨j, hjJ, hfj⟩ := mem_img.1 (himg (mem_img.2 ⟨⟨y, hyN⟩, hy, rfl⟩))
  have hyH : ∀ h ∈ H, h * y = y * h := Subgroup.mem_centralizer_iff.mp (hSH hy)
  have hjH : ∀ h ∈ H, h * (j : G) = (j : G) * h := by
    intro h hh
    have hhN : h ∈ N := hD.BsN (hHBs hh)
    have hconj : h * (j : G) * h⁻¹ ∈ J := hHJ h hh j hjJ
    have hcomm : (⟨h, hhN⟩ : ↥N) * ⟨y, hyN⟩ = ⟨y, hyN⟩ * ⟨h, hhN⟩ := Subtype.ext (hyH h hh)
    have hker : (⟨h, hhN⟩ : ↥N) * j * (⟨h, hhN⟩ : ↥N)⁻¹ * j⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hfj, ← map_mul,
        hcomm, map_mul]
      group
    have hZ : h * (j : G) * h⁻¹ * (j : G)⁻¹ ∈ Z := (hD.mem_ker_iff _).1 hker
    have h1 := hJZ _ (J.mul_mem hconj (J.inv_mem hjJ)) hZ
    calc h * (j : G) = (h * (j : G) * h⁻¹ * (j : G)⁻¹) * (j : G) * h := by group
      _ = (j : G) * h := by rw [h1, one_mul]
  have hker : (⟨y, hyN⟩ : ↥N) * j⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfj, mul_inv_cancel]
  have hZ : y * (j : G)⁻¹ ∈ Z := (hD.mem_ker_iff _).1 hker
  have hcomm : ∀ h ∈ H, h * (y * (j : G)⁻¹) = (y * (j : G)⁻¹) * h := by
    intro h hh
    have hjinv : h * (j : G)⁻¹ = (j : G)⁻¹ * h := by
      have := hjH h hh
      calc h * (j : G)⁻¹ = (j : G)⁻¹ * ((j : G) * h) * (j : G)⁻¹ := by group
        _ = (j : G)⁻¹ * (h * (j : G)) * (j : G)⁻¹ := by rw [this]
        _ = (j : G)⁻¹ * h := by group
    calc h * (y * (j : G)⁻¹) = (h * y) * (j : G)⁻¹ := by group
      _ = (y * h) * (j : G)⁻¹ := by rw [hyH h hh]
      _ = y * (h * (j : G)⁻¹) := by group
      _ = y * ((j : G)⁻¹ * h) := by rw [hjinv]
      _ = (y * (j : G)⁻¹) * h := by group
  have hyj : y = (j : G) := mul_inv_eq_one.mp (hfix _ hZ hcomm)
  rw [hyj]
  exact hjJ

end NsQuot

namespace QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnitSix_perm_mem {B L Bs : Subgroup G} {x : G} {Q : Type} [Group Q] [Finite Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    {ε : Equiv.Perm (Fin 6) ≃* ↥(ggAutomizer (NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs))}
    {hx : x ∈ Subgroup.normalizer (L : Set G)}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hbase : QTwoUnitBase 3 (NsQuot.img (Subgroup.normalizer (L : Set G)) f B)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs) (f ⟨x, hx⟩)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f L) ψ ε)
    {βL : Additive ↥Bs ≃+ DVec 6}
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    (σ : Equiv.Perm (Fin 6)) :
    (MulAut.congr hD.tau).symm ((ε σ : ↥(ggAutomizer _ _)) : MulAut _) ∈ ggAutomizer L Bs ∧
      ∀ s : ↥Bs, βL (Additive.ofMul
        ((MulAut.congr hD.tau).symm ((ε σ : ↥(ggAutomizer _ _)) : MulAut _) s)) =
          dPerm 6 σ (βL (Additive.ofMul s)) := by
  refine ⟨?_, fun s => ?_⟩
  · obtain ⟨r, hr, hrε⟩ := Subgroup.mem_map.1 (hD.automizer_le_map hD.ZL hD.LN (ε σ).2)
    have hr' : (MulAut.congr hD.tau).symm ((ε σ : ↥(ggAutomizer _ _)) : MulAut _) = r := by
      rw [← hrε]
      exact (MulAut.congr hD.tau).symm_apply_apply r
    rw [hr']
    exact hr
  · set r := (MulAut.congr hD.tau).symm ((ε σ : ↥(ggAutomizer _ _)) : MulAut _)
    have hcr : MulAut.congr hD.tau r = ((ε σ : ↥(ggAutomizer _ _)) : MulAut _) :=
      MulEquiv.apply_symm_apply _ _
    have h1 : hD.tau (r s) = ((ε σ : ↥(ggAutomizer _ _)) : MulAut _) (hD.tau s) := by
      rw [← hcr, congr_apply_tau]
    have h2 := congrArg Subtype.val h1
    rw [hD.tau_apply, hbase.perm σ (hD.tau s), hD.tau_apply] at h2
    exact hpermβ σ s (r s) (hD.BsN s.2) (hD.BsN (r s).2) h2

theorem ggQTwoDUnitSix_conj_mem_block (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type}
    [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    {c : Fin 6} {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {s : G} (hs : s ∈ Bs) : ∀ j ∈ J₁, s * j * s⁻¹ ∈ J₁ := by
  have hT : (Finset.univ.erase c).card < 6 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨θ, -, hθr, hθf⟩ := ggQTwoDUnitSix_chart hK hD hψk (Finset.univ.erase c) hT hJ₁L hJ₁Z hJ₁
  have hsN : s ∈ Subgroup.normalizer (L : Set G) := hD.BsN hs
  intro j hj
  rw [← hθr] at hj ⊢
  obtain ⟨X, rfl⟩ := hj
  rw [ggQTwoDUnitSix_chart_conj hK hD (Finset.univ.erase c) hJ₁L hJ₁Z hJ₁ hθr hθf
    (s := ⟨s, hsN⟩) (fun l hl => (Subgroup.mem_normalizer_iff.mp hsN l).mp hl)
    (hind ⟨s, hs⟩ hsN) X]
  exact ⟨_, rfl⟩

omit [Finite G] in
theorem ggQTwoDUnitSix_X_le_centralizer {Bs J₁ : Subgroup G} {βL : Additive ↥Bs ≃+ DVec 6}
    {a c : Fin 6} {b' : ↥Bs} (hb' : βL (Additive.ofMul b') = Pi.single c 1)
    (hb'J : (b' : G) ∈ Subgroup.centralizer (J₁ : Set G)) {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) :
    J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({(b' : G)} : Set G) := by
  have hJ₁c : J₁ ≤ Subgroup.centralizer ({(b' : G)} : Set G) := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hb'J j hj)
  have hgb : g * (b' : G) * g⁻¹ = (b' : G)⁻¹ := by
    have h : α b' = b'⁻¹ := Additive.ofMul.injective (βL.injective (by
      rw [hα, ofMul_inv, map_neg, hb']
      exact ggQTwoDUnitSix_dSign_eq_neg fun k _ hkc => by rw [Pi.single_eq_of_ne hkc]))
    exact (hg b').symm.trans (congrArg Subtype.val h)
  refine sup_le hJ₁c ?_
  calc J₁.map (MulAut.conj g).toMonoidHom
      ≤ (Subgroup.centralizer ({(b' : G)} : Set G)).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hJ₁c
    _ = Subgroup.centralizer ({(b' : G)} : Set G) := by
        rw [ggQTwoDUnitSix_map_centralizer_conj, hgb, ggQTwoDUnitSix_centralizer_inv]

omit [Finite G] in
theorem ggQTwoDUnitSix_fixes_b' {X Bs : Subgroup G} {b' : ↥Bs}
    (hXc : X ≤ Subgroup.centralizer ({(b' : G)} : Set G)) {r : MulAut ↥Bs}
    (hr : r ∈ ggAutomizer X Bs) : r b' = b' := by
  obtain ⟨n, hnX, -, hna⟩ := mem_ggAutomizer_iff.mp hr
  have hcomm : n * (b' : G) = (b' : G) * n := Subgroup.mem_centralizer_singleton_iff.mp (hXc hnX)
  apply Subtype.ext
  rw [hna b', hcomm]
  group

omit [Finite G] in
private theorem map_conj_self {X : Subgroup G} {n : G} (hn : n ∈ X) :
    X.map (MulAut.conj n).toMonoidHom = X := by
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact X.mul_mem (X.mul_mem hn hz) (X.inv_mem hn)
  · intro y hy
    refine ⟨n⁻¹ * y * n, X.mul_mem (X.mul_mem (X.inv_mem hn) hy) hn, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private theorem exists_ne_ne (u v : Fin 6) : ∃ k : Fin 6, k ≠ u ∧ k ≠ v := by
  revert u v
  decide

private theorem exists_ne_ne_ne (u v w : Fin 6) : ∃ k : Fin 6, k ≠ u ∧ k ≠ v ∧ k ≠ w := by
  revert u v w
  decide

private theorem dPerm_single_of_fix {σ : Equiv.Perm (Fin 6)} {k : Fin 6} (hk : σ k = k) :
    dPerm 6 σ (Pi.single k 1) = Pi.single k 1 := by
  rw [← qtwoDB20_dBasis_apply, dPerm_apply, hk]

section Fix


theorem ggQTwoDUnitSix_twoCentral_fix (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type}
    [Group Q] [Finite Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hL : Group.IsPerfect ↥L) (hψr : ψ.range = NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    {t : ↥Bs} {k : Fin 6} (ht : βL (Additive.ofMul t) = Pi.single k 1) :
    ∀ w ∈ twoCentral L, (t : G) * w = w * (t : G) → w = 1 := by
  classical
  intro w hw hcw
  set c : Fin 6 → Kˣ := fun i => ω ^ (βL (Additive.ofMul t) i).val with hc
  have hci : ∀ i, c i = if i = k then ω else 1 := by
    intro i
    rw [hc]
    simp only [ht, Pi.single_apply]
    split_ifs
    · rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
    · rw [show (0 : ZMod 3).val = 0 from rfl, pow_zero]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hunit : ggIsUnitaryMat (p := 2) (f := 1) (qTwoChartTwoThree_diag c) :=
    CFSG.ClassicalGroups.Unitary.SUThreeTwoDiag.conjTr_diagGL_mul_self hK c
  have hdet : Matrix.GeneralLinearGroup.det (qTwoChartTwoThree_diag c) ≠ 1 := by
    intro h
    have h1 := congrArg Units.val h
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h1
    change Matrix.det (Matrix.diagonal fun i => ((c i : Kˣ) : K)) = 1 at h1
    rw [Matrix.det_diagonal, Finset.prod_eq_single k
      (fun i _ hik => by rw [hci, if_neg hik, Units.val_one])
      (fun h => absurd (Finset.mem_univ k) h), hci, if_pos rfl, Units.val_eq_one] at h1
    rw [h1, orderOf_one] at hω
    exact absurd hω (by norm_num)
  have htN : (t : G) ∈ Subgroup.normalizer (L : Set G) := hD.BsN t.2
  let σX : MulAut ↥L := L.normalizerMonoidHom ⟨(t : G), htN⟩
  let τX : MulAut ↥(NsQuot.img _ f L) := (NsQuot.img _ f L).normalizerMonoidHom
    ⟨f ⟨(t : G), htN⟩, hD.f_mem_normalizer_img hD.BsN t.2⟩
  let ψ₀ : Su K 2 1 6 →* ↥(NsQuot.img _ f L) := ψ.codRestrict _ fun u => by
    rw [← hψr]
    exact MonoidHom.mem_range.mpr ⟨u, rfl⟩
  have hψ₀ : Function.Surjective ψ₀ := by
    intro q
    have hq : (q : Q) ∈ ψ.range := by
      rw [hψr]
      exact q.2
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hq
    exact ⟨u, Subtype.ext hu⟩
  have hwL : w ∈ L := twoCentral_le L hw
  have hres := ggU62OuterDiagInput_holds K (by rw [hK]; norm_num) ↥L
    ↥(NsQuot.img _ f L) hD.fL ψ₀ σX τX (qTwoChartTwoThree_diag c) hL hD.fL_surjective
    (fun u hu l' => Subgroup.mem_center_iff.1
      (hD.mem_center_of_mem ((hD.fL_eq_one_iff u).1 hu)) l')
    (fun u hu => by
      obtain ⟨m, hm⟩ := hD.Z2 _ ((hD.fL_eq_one_iff u).1 hu)
      exact ⟨m, Subtype.ext (by simpa using hm)⟩)
    hψ₀
    (fun s hs => hψk (by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact congrArg Subtype.val hs))
    (fun l => Subtype.ext (by
      have e : (⟨((σX l : ↥L) : G), hD.LN (σX l).2⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          ⟨(t : G), htN⟩ * ⟨(l : G), hD.LN l.2⟩ * ⟨(t : G), htN⟩⁻¹ := rfl
      change f ⟨((σX l : ↥L) : G), hD.LN (σX l).2⟩ =
        f ⟨(t : G), htN⟩ * f ⟨(l : G), hD.LN l.2⟩ * (f ⟨(t : G), htN⟩)⁻¹
      rw [e, map_mul, map_mul, map_inv]))
    hunit hdet
    (fun u => by
      obtain ⟨u', hu', hψu'⟩ := hind t htN u
      exact ⟨u', hu', Subtype.ext hψu'.symm⟩)
    ⟨w, hwL⟩ ((hD.fL_eq_one_iff _).2 hw) (Subtype.ext (by
      show (t : G) * w * (t : G)⁻¹ = w
      rw [mul_inv_eq_iff_eq_mul]
      exact hcw))
  exact congrArg Subtype.val hres

theorem ggQTwoDUnitSix_rankOneIn_le {B L Bs : Subgroup G} {x : G} {Q : Type} [Group Q]
    [Finite Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    {ε : Equiv.Perm (Fin 6) ≃* ↥(ggAutomizer (NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs))}
    {hx : x ∈ Subgroup.normalizer (L : Set G)}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hL : Group.IsPerfect ↥L)
    (hbase : QTwoUnitBase 3 (NsQuot.img (Subgroup.normalizer (L : Set G)) f B)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs) (f ⟨x, hx⟩)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f L) ψ ε)
    {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    {c : Fin 6} {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {u v : Fin 6} (huv : u ≠ v) (huc : u ≠ c) (hvc : v ≠ c) :
    ggRankOneIn L Bs ((MulAut.congr hD.tau).symm
      ((ε (Equiv.swap u v) : ↥(ggAutomizer _ _)) : MulAut _)) ≤ J₁ := by
  classical
  obtain ⟨-, hr₀act⟩ := ggQTwoDUnitSix_perm_mem hD hbase hpermβ (Equiv.swap u v)
  set r₀ := (MulAut.congr hD.tau).symm
    ((ε (Equiv.swap u v) : ↥(ggAutomizer _ _)) : MulAut _)
  obtain ⟨k, hku, hkv⟩ := exists_ne_ne u v
  set t : ↥Bs := Additive.toMul (βL.symm (Pi.single k 1)) with htdef
  have ht : βL (Additive.ofMul t) = Pi.single k 1 := by
    rw [htdef, ofMul_toMul, AddEquiv.apply_symm_apply]
  have htH : (t : G) ∈ ggHyperplane Bs r₀ := by
    refine ⟨t, ?_, rfl⟩
    change r₀ t = t
    apply Additive.ofMul.injective
    apply βL.injective
    rw [hr₀act t, ht]
    exact dPerm_single_of_fix (Equiv.swap_apply_of_ne_of_ne hku hkv)
  have hfix : ∀ z ∈ twoCentral L, (∀ h ∈ ggHyperplane Bs r₀, h * z = z * h) → z = 1 :=
    fun z hz hcz => ggQTwoDUnitSix_twoCentral_fix hbase.card_field hD hL hbase.range
      hbase.hyp.ker hω hind ht z hz (hcz _ htH)
  have hcr : MulAut.congr hD.tau r₀ =
      ((ε (Equiv.swap u v) : ↥(ggAutomizer _ _)) : MulAut _) := MulEquiv.apply_symm_apply _ _
  have huvT : ({u, v} : Finset (Fin 6)) ⊆ Finset.univ.erase c := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Finset.mem_erase]
    rcases hy with rfl | rfl
    · exact ⟨huc, Finset.mem_univ _⟩
    · exact ⟨hvc, Finset.mem_univ _⟩
  have himg : NsQuot.img _ f (ggRankOneIn L Bs r₀) ≤ NsQuot.img _ f J₁ := by
    rw [hD.img_rankOneIn hfix, hcr, hbase.rankOne u v huv, ggSuPairBlock_eq_coordBlockSU, hJ₁]
    exact Subgroup.map_mono (ggQTwoDUnitSix_coordBlockSU_mono huvT)
  have hHBs : ggHyperplane Bs r₀ ≤ Bs := Subgroup.map_subtype_le _
  exact hD.le_of_img_le_of_fix hJ₁Z ((ggOTwoPrime_le _).trans inf_le_left)
    ((ggOTwoPrime_le _).trans inf_le_right) hHBs
    (fun h hh => ggQTwoDUnitSix_conj_mem_block hbase.card_field hD hbase.hyp.ker hind hJ₁L hJ₁Z
      hJ₁ (hHBs hh))
    hfix himg

theorem ggQTwoDUnitSix_rankTwoIn_le {B L Bs : Subgroup G} {x : G} {Q : Type} [Group Q]
    [Finite Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    {ε : Equiv.Perm (Fin 6) ≃* ↥(ggAutomizer (NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs))}
    {hx : x ∈ Subgroup.normalizer (L : Set G)}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hL : Group.IsPerfect ↥L)
    (hbase : QTwoUnitBase 3 (NsQuot.img (Subgroup.normalizer (L : Set G)) f B)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs) (f ⟨x, hx⟩)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f L) ψ ε)
    {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    {c : Fin 6} {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {p₀ p₁ p₂ : Fin 6} (h01 : p₀ ≠ p₁) (h12 : p₁ ≠ p₂) (h02 : p₀ ≠ p₂) (h0c : p₀ ≠ c)
    (h1c : p₁ ≠ c) (h2c : p₂ ≠ c) :
    ggRankTwoIn L Bs
      ((MulAut.congr hD.tau).symm ((ε (Equiv.swap p₀ p₁) : ↥(ggAutomizer _ _)) : MulAut _))
      ((MulAut.congr hD.tau).symm ((ε (Equiv.swap p₁ p₂) : ↥(ggAutomizer _ _)) : MulAut _)) ≤
        J₁ := by
  classical
  obtain ⟨-, hr₁act⟩ := ggQTwoDUnitSix_perm_mem hD hbase hpermβ (Equiv.swap p₀ p₁)
  obtain ⟨-, hr₂act⟩ := ggQTwoDUnitSix_perm_mem hD hbase hpermβ (Equiv.swap p₁ p₂)
  set r₁ := (MulAut.congr hD.tau).symm
    ((ε (Equiv.swap p₀ p₁) : ↥(ggAutomizer _ _)) : MulAut _)
  set r₂ := (MulAut.congr hD.tau).symm
    ((ε (Equiv.swap p₁ p₂) : ↥(ggAutomizer _ _)) : MulAut _)
  obtain ⟨k, hk0, hk1, hk2⟩ := exists_ne_ne_ne p₀ p₁ p₂
  set t : ↥Bs := Additive.toMul (βL.symm (Pi.single k 1)) with htdef
  have ht : βL (Additive.ofMul t) = Pi.single k 1 := by
    rw [htdef, ofMul_toMul, AddEquiv.apply_symm_apply]
  have htH : (t : G) ∈ ggHyperplane Bs r₁ ⊓ ggHyperplane Bs r₂ := by
    refine ⟨⟨t, ?_, rfl⟩, ⟨t, ?_, rfl⟩⟩
    · change r₁ t = t
      apply Additive.ofMul.injective
      apply βL.injective
      rw [hr₁act t, ht]
      exact dPerm_single_of_fix (Equiv.swap_apply_of_ne_of_ne hk0 hk1)
    · change r₂ t = t
      apply Additive.ofMul.injective
      apply βL.injective
      rw [hr₂act t, ht]
      exact dPerm_single_of_fix (Equiv.swap_apply_of_ne_of_ne hk1 hk2)
  have hfix : ∀ z ∈ twoCentral L,
      (∀ h ∈ ggHyperplane Bs r₁ ⊓ ggHyperplane Bs r₂, h * z = z * h) → z = 1 :=
    fun z hz hcz => ggQTwoDUnitSix_twoCentral_fix hbase.card_field hD hL hbase.range
      hbase.hyp.ker hω hind ht z hz (hcz _ htH)
  have hcr₁ : MulAut.congr hD.tau r₁ =
      ((ε (Equiv.swap p₀ p₁) : ↥(ggAutomizer _ _)) : MulAut _) := MulEquiv.apply_symm_apply _ _
  have hcr₂ : MulAut.congr hD.tau r₂ =
      ((ε (Equiv.swap p₁ p₂) : ↥(ggAutomizer _ _)) : MulAut _) := MulEquiv.apply_symm_apply _ _
  have hrank := ggQTwoDUnit_rankTwoIn_eq (K := K) hbase.hyp hbase.card_field hbase.diag h01 h12
    h02 (r := MulAut.congr hD.tau r₁) (r' := MulAut.congr hD.tau r₂)
    (fun s => by rw [hcr₁]; simpa only [Equiv.swap_inv] using hbase.perm (Equiv.swap p₀ p₁) s)
    (fun s => by rw [hcr₂]; simpa only [Equiv.swap_inv] using hbase.perm (Equiv.swap p₁ p₂) s)
  rw [hbase.range] at hrank
  have hT : ({p₀, p₁, p₂} : Finset (Fin 6)) ⊆ Finset.univ.erase c := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Finset.mem_erase]
    rcases hy with rfl | rfl | rfl
    · exact ⟨h0c, Finset.mem_univ _⟩
    · exact ⟨h1c, Finset.mem_univ _⟩
    · exact ⟨h2c, Finset.mem_univ _⟩
  have himg : NsQuot.img _ f (ggRankTwoIn L Bs r₁ r₂) ≤ NsQuot.img _ f J₁ := by
    rw [hD.img_rankTwoIn hfix, hrank, hJ₁]
    exact Subgroup.map_mono (ggQTwoDUnitSix_coordBlockSU_mono hT)
  have hHBs : ggHyperplane Bs r₁ ⊓ ggHyperplane Bs r₂ ≤ Bs :=
    inf_le_left.trans (Subgroup.map_subtype_le _)
  exact hD.le_of_img_le_of_fix hJ₁Z ((ggOTwoPrime_le _).trans inf_le_left)
    ((ggOTwoPrime_le _).trans inf_le_right) hHBs
    (fun h hh => ggQTwoDUnitSix_conj_mem_block hbase.card_field hD hbase.hyp.ker hind hJ₁L hJ₁Z
      hJ₁ (hHBs hh))
    hfix himg

end Fix

section Clauses



theorem ggQTwoDUnitSix_X_rankOne (hL1 : GGQTwoL1InputOn fun m => m = 6)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e) {e' : Fin 6 ≃ ι}
    (hM : M = (ggCoxeterMatrixD 6).reindex e')
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs L)
    {Q : Type} [Group Q] [Finite Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q}
    {ψ : Su K 2 1 6 →* Q}
    {ε : Equiv.Perm (Fin 6) ≃* ↥(ggAutomizer (NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs))}
    {hx : x ∈ Subgroup.normalizer (L : Set G)}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hbase : QTwoUnitBase 3 (NsQuot.img (Subgroup.normalizer (L : Set G)) f B)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs) (f ⟨x, hx⟩)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f L) ψ ε)
    {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    (hxBs : x ∈ Bs) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1)
    (hjoin : ∀ w ∈ dEven 6, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
      ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s)))
    (hcox : ∀ (sgn : Bool) (a b : Fin 6), a ≠ b → ∀ r ∈ ggAutomizerJoin L Bs 𝒦,
      (∀ s : ↥Bs, βL (Additive.ofMul (r s)) = dTau 6 sgn a b (βL (Additive.ofMul s))) →
        r ∈ ggCoxRefl M e)
    (hcoxRoot : ∀ r ∈ ggCoxRefl M e, ∃ (sgn : Bool) (a b : Fin 6), a ≠ b ∧ ∀ s : ↥Bs,
      βL (Additive.ofMul (r s)) = dTau 6 sgn a b (βL (Additive.ofMul s)))
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {b' : ↥Bs} (hb' : βL (Additive.ofMul b') = Pi.single c 1)
    (hb'J : (b' : G) ∈ Subgroup.centralizer (J₁ : Set G)) {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) :
    ∀ r ∈ ggAutomizer (J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom) Bs, r ∈ ggCoxRefl M e →
      ggRankOne Bs r = ggRankOneIn (J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom) Bs r := by
  intro r hrA hrC
  classical
  have hK : Nat.card K = 4 := hbase.card_field
  have hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6) := hbase.hyp.ker
  have hL : Group.IsPerfect ↥L := ⟨hmark.1⟩
  have hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs := by
    intro σ q hq
    rw [← hbase.perm σ ⟨q, hq⟩]
    exact (((ε σ : ↥(ggAutomizer _ _)) :
      MulAut ↥(NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)) ⟨q, hq⟩).2
  set X := J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom
  have hXc : X ≤ Subgroup.centralizer ({(b' : G)} : Set G) :=
    ggQTwoDUnitSix_X_le_centralizer hb' hb'J hα hg
  have hrb' : r b' = b' := ggQTwoDUnitSix_fixes_b' hXc hrA
  obtain ⟨sgn, i, j, hij, hact⟩ := hcoxRoot r hrC
  have hsingle : dTau 6 sgn i j (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
    have h1 : βL (Additive.ofMul (r b')) = βL (Additive.ofMul b') := by rw [hrb']
    rw [hact b', hb'] at h1
    exact h1
  obtain ⟨hci, hcj⟩ := qtwoDB20_dTau_fixes_single hij hsingle
  obtain ⟨w, hwEven, hwfix, u, v, huErase, hvErase, huv, hwconj⟩ :=
    qtwoDB20_normal_form_one (by norm_num) hij hci hcj
  obtain ⟨a₀, -, ha₀w⟩ := hjoin w hwEven
  have ha₀X : a₀ ∈ ggAutomizer X Bs :=
    ggQTwoDUnitSix_weyl_X hK hD hψk hε hind hpermβ hxBs hxL hxcoord hac hJ₁L hJ₁Z hJ₁ hb' hb'J
      hα hgN hg hwEven hwfix ha₀w
  obtain ⟨n, hnX, -, hnact⟩ := mem_ggAutomizer_iff.mp ha₀X
  have ha₀w_inv : ∀ s : ↥Bs, βL (Additive.ofMul (a₀⁻¹ s)) = w⁻¹ (βL (Additive.ofMul s)) := by
    intro s
    have h : w (βL (Additive.ofMul (a₀⁻¹ s))) = βL (Additive.ofMul s) := by
      have h' := ha₀w (a₀⁻¹ s)
      rw [MulAut.apply_inv_self] at h'
      exact h'.symm
    rw [← h]
    simp
  let r₀ : MulAut ↥Bs := a₀ * r * a₀⁻¹
  have hr₀_act : ∀ s : ↥Bs, βL (Additive.ofMul (r₀ s)) =
      dTau 6 false u v (βL (Additive.ofMul s)) := by
    intro s
    have h1 : r₀ s = a₀ (r (a₀⁻¹ s)) := by simp only [r₀, MulAut.mul_apply]
    rw [h1, ha₀w (r (a₀⁻¹ s)), hact (a₀⁻¹ s), ha₀w_inv s]
    rw [show dTau 6 false u v = w * dTau 6 sgn i j * w⁻¹ from hwconj.symm]
    rfl
  obtain ⟨he₀L, he₀act⟩ := ggQTwoDUnitSix_perm_mem hD hbase hpermβ (Equiv.swap u v)
  have hr₀_eq : r₀ = (MulAut.congr hD.tau).symm
      ((ε (Equiv.swap u v) : ↥(ggAutomizer _ _)) : MulAut _) := by
    refine MulEquiv.ext fun s => ?_
    apply Additive.ofMul.injective
    apply βL.injective
    rw [hr₀_act s, he₀act s, qtwoDB20_dTau_false]
  have hr₀L : r₀ ∈ ggAutomizer L Bs := by
    rw [hr₀_eq]
    exact he₀L
  have hr₀Cox : r₀ ∈ ggCoxRefl M e :=
    hcox false u v huv r₀ (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀L) hr₀_act
  have huc : u ≠ c := (Finset.mem_erase.mp huErase).1
  have hvc : v ≠ c := (Finset.mem_erase.mp hvErase).1
  have hEq₀ : ggRankOne Bs r₀ = ggRankOneIn X Bs r₀ := by
    obtain ⟨hL1r₀, -⟩ :=
      hL1 G 3 B Bs x L D J 𝒦 ι M e hcfg 6 e' rfl hM L (Or.inl rfl) r₀ hr₀L hr₀Cox
    have hle : ggRankOneIn L Bs r₀ ≤ J₁ := by
      rw [hr₀_eq]
      exact ggQTwoDUnitSix_rankOneIn_le hD hL hbase hω hind hpermβ hJ₁L hJ₁Z hJ₁ huv huc hvc
    have hXle : ggRankOne Bs r₀ ≤ X := by
      rw [hL1r₀]
      exact hle.trans le_sup_left
    have hmono : ggOTwoPrime (X ⊓ Subgroup.centralizer (ggHyperplane Bs r₀ : Set G)) ≤
        ggOTwoPrime (Subgroup.centralizer (ggHyperplane Bs r₀ : Set G)) :=
      LinFusion.ggOTwoPrime_mono inf_le_right
    have hXinf : ggOTwoPrime (Subgroup.centralizer (ggHyperplane Bs r₀ : Set G)) ≤
        X ⊓ Subgroup.centralizer (ggHyperplane Bs r₀ : Set G) := by
      intro y hy
      exact ⟨hXle hy, ggOTwoPrime_le _ hy⟩
    show ggOTwoPrime (Subgroup.centralizer (ggHyperplane Bs r₀ : Set G)) =
      ggOTwoPrime (X ⊓ Subgroup.centralizer (ggHyperplane Bs r₀ : Set G))
    exact le_antisymm (qtwoDB20_oTwoPrime_le_inf hXinf) hmono
  have hnX_inv : n⁻¹ ∈ X := X.inv_mem hnX
  have hnact_inv : ∀ s : ↥Bs, ((a₀⁻¹ s : ↥Bs) : G) = n⁻¹ * (s : G) * n⁻¹⁻¹ := by
    intro s
    have h := hnact (a₀⁻¹ s)
    rw [MulAut.apply_inv_self] at h
    rw [h]
    group
  have hmap := congrArg (Subgroup.map (MulAut.conj n⁻¹).toMonoidHom) hEq₀
  rw [ggRankOne_map_conj hnact_inv r₀, ggRankOneIn_map_conj hnact_inv r₀,
    map_conj_self hnX_inv] at hmap
  have hr_eq : a₀⁻¹ * r₀ * a₀ = r := by
    rw [show r₀ = a₀ * r * a₀⁻¹ from rfl]
    group
  rw [inv_inv] at hmap
  rw [hr_eq] at hmap
  exact hmap

theorem ggQTwoDUnitSix_X_rankTwo (hEA : GGQTwoEdgeAmbientInputOn fun m => m = 6)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e) {e' : Fin 6 ≃ ι}
    (hM : M = (ggCoxeterMatrixD 6).reindex e')
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs L)
    {Q : Type} [Group Q] [Finite Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q}
    {ψ : Su K 2 1 6 →* Q}
    {ε : Equiv.Perm (Fin 6) ≃* ↥(ggAutomizer (NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs))}
    {hx : x ∈ Subgroup.normalizer (L : Set G)}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hbase : QTwoUnitBase 3 (NsQuot.img (Subgroup.normalizer (L : Set G)) f B)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs) (f ⟨x, hx⟩)
      (NsQuot.img (Subgroup.normalizer (L : Set G)) f L) ψ ε)
    {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    (hxBs : x ∈ Bs) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1)
    (hjoin : ∀ w ∈ dEven 6, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
      ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s)))
    (hcox : ∀ (sgn : Bool) (a b : Fin 6), a ≠ b → ∀ r ∈ ggAutomizerJoin L Bs 𝒦,
      (∀ s : ↥Bs, βL (Additive.ofMul (r s)) = dTau 6 sgn a b (βL (Additive.ofMul s))) →
        r ∈ ggCoxRefl M e)
    (hcoxRoot : ∀ r ∈ ggCoxRefl M e, ∃ (sgn : Bool) (a b : Fin 6), a ≠ b ∧ ∀ s : ↥Bs,
      βL (Additive.ofMul (r s)) = dTau 6 sgn a b (βL (Additive.ofMul s)))
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {b' : ↥Bs} (hb' : βL (Additive.ofMul b') = Pi.single c 1)
    (hb'J : (b' : G) ∈ Subgroup.centralizer (J₁ : Set G)) {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) :
    ∀ r ∈ ggAutomizer (J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom) Bs, r ∈ ggCoxRefl M e →
      ∀ r' ∈ ggAutomizer (J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom) Bs, r' ∈ ggCoxRefl M e →
        r * r' ≠ r' * r →
          ggRankTwo Bs r r' = ggRankTwoIn (J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom) Bs r r' := by
  intro r hrA hrC r' hr'A hr'C hnc
  classical
  have hK : Nat.card K = 4 := hbase.card_field
  have hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6) := hbase.hyp.ker
  have hL : Group.IsPerfect ↥L := ⟨hmark.1⟩
  have hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs := by
    intro σ q hq
    rw [← hbase.perm σ ⟨q, hq⟩]
    exact (((ε σ : ↥(ggAutomizer _ _)) :
      MulAut ↥(NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)) ⟨q, hq⟩).2
  set X := J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom
  have hXc : X ≤ Subgroup.centralizer ({(b' : G)} : Set G) :=
    ggQTwoDUnitSix_X_le_centralizer hb' hb'J hα hg
  have hrb' : r b' = b' := ggQTwoDUnitSix_fixes_b' hXc hrA
  have hr'b' : r' b' = b' := ggQTwoDUnitSix_fixes_b' hXc hr'A
  obtain ⟨sgn, i, j, hij, hact⟩ := hcoxRoot r hrC
  obtain ⟨sgn', i', j', hi'j', hact'⟩ := hcoxRoot r' hr'C
  have hfix : dTau 6 sgn i j (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
    have h1 : βL (Additive.ofMul (r b')) = βL (Additive.ofMul b') := by rw [hrb']
    rw [hact b', hb'] at h1
    exact h1
  obtain ⟨hci, hcj⟩ := qtwoDB20_dTau_fixes_single hij hfix
  have hfix' : dTau 6 sgn' i' j' (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
    have h1 : βL (Additive.ofMul (r' b')) = βL (Additive.ofMul b') := by rw [hr'b']
    rw [hact' b', hb'] at h1
    exact h1
  obtain ⟨hci', hcj'⟩ := qtwoDB20_dTau_fixes_single hi'j' hfix'
  have hnc' : dTau 6 sgn i j * dTau 6 sgn' i' j' ≠ dTau 6 sgn' i' j' * dTau 6 sgn i j := by
    intro h
    apply hnc
    refine MulEquiv.ext fun s => ?_
    apply Additive.ofMul.injective
    apply βL.injective
    simp only [MulAut.mul_apply, hact, hact']
    simpa only [LinearEquiv.mul_apply] using
      congrArg (fun T : DVec 6 ≃ₗ[ZMod 3] DVec 6 => T (βL (Additive.ofMul s))) h
  obtain ⟨p₀, p₁, p₂, V', hp1, hp2, hc0, hc1, hc2, hV'mem, hV'fix', hV'conj1, hV'conj2⟩ :=
    qtwoDB20_normal_form_pair_lin (by norm_num) hij hi'j' hci hcj hci' hcj' hnc'
  obtain ⟨a₀, -, ha₀V'⟩ := hjoin V' hV'mem
  have ha₀X : a₀ ∈ ggAutomizer X Bs :=
    ggQTwoDUnitSix_weyl_X hK hD hψk hε hind hpermβ hxBs hxL hxcoord hac hJ₁L hJ₁Z hJ₁ hb' hb'J
      hα hgN hg hV'mem hV'fix' ha₀V'
  obtain ⟨n, hnX, -, hnact⟩ := mem_ggAutomizer_iff.mp ha₀X
  have hainv : ∀ s : ↥Bs, βL (Additive.ofMul (a₀⁻¹ s)) = V'⁻¹ (βL (Additive.ofMul s)) := by
    intro s
    have h := ha₀V' (a₀⁻¹ s)
    rw [show a₀ (a₀⁻¹ s) = s from MulEquiv.apply_symm_apply a₀ s] at h
    calc βL (Additive.ofMul (a₀⁻¹ s))
        = V'⁻¹ (V' (βL (Additive.ofMul (a₀⁻¹ s)))) :=
          (LinearEquiv.symm_apply_apply V' _).symm
      _ = V'⁻¹ (βL (Additive.ofMul s)) := congrArg (fun x => V'⁻¹ x) h.symm
  have hp0p1 : p₀ ≠ p₁ := fun h => by have := congrArg Fin.val h; omega
  have hp1p2 : p₁ ≠ p₂ := fun h => by have := congrArg Fin.val h; omega
  have hp0p2 : p₀ ≠ p₂ := fun h => by have := congrArg Fin.val h; omega
  obtain ⟨heA₁, he₁act⟩ := ggQTwoDUnitSix_perm_mem hD hbase hpermβ (Equiv.swap p₀ p₁)
  obtain ⟨heA₂, he₂act⟩ := ggQTwoDUnitSix_perm_mem hD hbase hpermβ (Equiv.swap p₁ p₂)
  set e₁ := (MulAut.congr hD.tau).symm
    ((ε (Equiv.swap p₀ p₁) : ↥(ggAutomizer _ _)) : MulAut _)
  set e₂ := (MulAut.congr hD.tau).symm
    ((ε (Equiv.swap p₁ p₂) : ↥(ggAutomizer _ _)) : MulAut _)
  have heq1 : a₀ * r * a₀⁻¹ = e₁ := by
    refine MulEquiv.ext fun s => ?_
    apply Additive.ofMul.injective
    apply βL.injective
    have hcomp := congrArg (fun T : DVec 6 ≃ₗ[ZMod 3] DVec 6 =>
      T (βL (Additive.ofMul s))) hV'conj1
    have h1 : βL (Additive.ofMul ((a₀ * r * a₀⁻¹) s)) =
        V' (dTau 6 sgn i j (V'⁻¹ (βL (Additive.ofMul s)))) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, ha₀V', hact, hainv s]
    rw [h1, he₁act s, ← qtwoDB20_dTau_false]
    simpa only [LinearEquiv.mul_apply] using hcomp
  have heq2 : a₀ * r' * a₀⁻¹ = e₂ := by
    refine MulEquiv.ext fun s => ?_
    apply Additive.ofMul.injective
    apply βL.injective
    have hcomp := congrArg (fun T : DVec 6 ≃ₗ[ZMod 3] DVec 6 =>
      T (βL (Additive.ofMul s))) hV'conj2
    have h1 : βL (Additive.ofMul ((a₀ * r' * a₀⁻¹) s)) =
        V' (dTau 6 sgn' i' j' (V'⁻¹ (βL (Additive.ofMul s)))) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, ha₀V', hact', hainv s]
    rw [h1, he₂act s, ← qtwoDB20_dTau_false]
    simpa only [LinearEquiv.mul_apply] using hcomp
  have heC₁ : e₁ ∈ ggCoxRefl M e :=
    hcox false p₀ p₁ hp0p1 e₁ (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) heA₁)
      (fun s => by rw [he₁act s, qtwoDB20_dTau_false])
  have heC₂ : e₂ ∈ ggCoxRefl M e :=
    hcox false p₁ p₂ hp1p2 e₂ (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) heA₂)
      (fun s => by rw [he₂act s, qtwoDB20_dTau_false])
  have henc : e₁ * e₂ ≠ e₂ * e₁ := by
    intro h
    apply hnc
    have hr1 : a₀⁻¹ * e₁ * a₀ = r := by rw [← heq1]; group
    have hr2 : a₀⁻¹ * e₂ * a₀ = r' := by rw [← heq2]; group
    calc r * r' = (a₀⁻¹ * e₁ * a₀) * (a₀⁻¹ * e₂ * a₀) := by rw [hr1, hr2]
      _ = a₀⁻¹ * (e₁ * e₂) * a₀ := by group
      _ = a₀⁻¹ * (e₂ * e₁) * a₀ := by rw [h]
      _ = (a₀⁻¹ * e₂ * a₀) * (a₀⁻¹ * e₁ * a₀) := by group
      _ = r' * r := by rw [hr1, hr2]
  have hEA_L : ggRankTwo Bs e₁ e₂ = ggRankTwoIn L Bs e₁ e₂ :=
    hEA G 3 B Bs x L D J 𝒦 ι M e hcfg 6 e' rfl hM L (Or.inl rfl) e₁ heA₁ heC₁ e₂ heA₂ heC₂ henc
  have hle : ggRankTwoIn L Bs e₁ e₂ ≤ J₁ :=
    ggQTwoDUnitSix_rankTwoIn_le hD hL hbase hω hind hpermβ hJ₁L hJ₁Z hJ₁ hp0p1 hp1p2 hp0p2
      (Ne.symm hc0) (Ne.symm hc1) (Ne.symm hc2)
  have hXle : ggRankTwo Bs e₁ e₂ ≤ X := by
    rw [hEA_L]
    exact hle.trans le_sup_left
  have hmono : ggOTwoPrime (X ⊓ Subgroup.centralizer
      ((ggHyperplane Bs e₁ ⊓ ggHyperplane Bs e₂ : Subgroup G) : Set G)) ≤
      ggOTwoPrime (Subgroup.centralizer
        ((ggHyperplane Bs e₁ ⊓ ggHyperplane Bs e₂ : Subgroup G) : Set G)) :=
    LinFusion.ggOTwoPrime_mono inf_le_right
  have hXinf : ggOTwoPrime (Subgroup.centralizer
      ((ggHyperplane Bs e₁ ⊓ ggHyperplane Bs e₂ : Subgroup G) : Set G)) ≤
      X ⊓ Subgroup.centralizer
        ((ggHyperplane Bs e₁ ⊓ ggHyperplane Bs e₂ : Subgroup G) : Set G) := by
    intro y hy
    exact ⟨hXle hy, ggOTwoPrime_le _ hy⟩
  have hEq₀ : ggRankTwo Bs e₁ e₂ = ggRankTwoIn X Bs e₁ e₂ := by
    show ggOTwoPrime (Subgroup.centralizer
        ((ggHyperplane Bs e₁ ⊓ ggHyperplane Bs e₂ : Subgroup G) : Set G)) =
      ggOTwoPrime (X ⊓ Subgroup.centralizer
        ((ggHyperplane Bs e₁ ⊓ ggHyperplane Bs e₂ : Subgroup G) : Set G))
    exact le_antisymm (qtwoDB20_oTwoPrime_le_inf hXinf) hmono
  have hnX_inv : n⁻¹ ∈ X := X.inv_mem hnX
  have hnact_inv : ∀ s : ↥Bs, ((a₀⁻¹ s : ↥Bs) : G) = n⁻¹ * (s : G) * n⁻¹⁻¹ := by
    intro s
    have h := hnact (a₀⁻¹ s)
    rw [MulAut.apply_inv_self] at h
    rw [h]
    group
  have hmap := congrArg (Subgroup.map (MulAut.conj n⁻¹).toMonoidHom) hEq₀
  rw [ggRankTwo_map_conj hnact_inv e₁ e₂, ggRankTwoIn_map_conj hnact_inv e₁ e₂,
    map_conj_self hnX_inv] at hmap
  have he₁r : a₀⁻¹ * e₁ * a₀ = r := by rw [← heq1]; group
  have he₂r : a₀⁻¹ * e₂ * a₀ = r' := by rw [← heq2]; group
  rw [inv_inv] at hmap
  rw [he₁r, he₂r] at hmap
  exact hmap

end Clauses

end QTwo

end CFSG.StandardType

end
