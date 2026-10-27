module

import CFSG.RankThree.PartTwo.Sec13.RonanStep131bStruct
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesElem
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesLift
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofTypes
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem commutes_of_mem_sup_thetaQuotCentralizer {G : Type} [Group G] [Finite G]
    {A L E : Subgroup G} {c a : G} (hCfg : Cfg G A c L E) (haA : a ∈ A)
    (haLC : a ∈ L ⊔ Sec4.thetaQuotCentralizer L) :
    ∀ x ∈ E ⊓ Sec4.thetaQuotCentralizer L, a * x * a⁻¹ * x⁻¹ = 1 := by
  have hD := hCfg.hD
  have hSL2 := hCfg.hSL
  have hEle := hCfg.hEle
  have hL := hD.mem_thetaComponentsAt
  have hc3 : c ^ 3 = 1 := by rw [← hD.orderOf_eq]; exact pow_orderOf_eq_one c
  have hZ3 : ∀ z ∈ Subgroup.zpowers c, z ^ 3 = 1 := (Item131bProof.isElemAbelian_zpowers hc3).2
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  set θH := aschbacherSolvableCore 3 H with hθH
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData hSL2
  have hL₀ : (Sec12.lBar c L).subgroupOf (lBarA c L A) = D.L₀ :=
    Res2Proof.subgroupOf_lBar_eq_L₀ hD D
  have hLAH : L ⊔ A ≤ H := sup_le (le_normalizer_zpowers_of_mem hL) hD.A_le_normalizer_zpowers
  let ι : (L ⊔ A : Subgroup G) →* H := Subgroup.inclusion hLAH
  let φ : (L ⊔ A : Subgroup G) →* lBarA c L A :=
    ((QuotientGroup.mk' θH).comp ι).codRestrict (lBarA c L A) fun x =>
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
  have hφv : ∀ x : (L ⊔ A : Subgroup G), ((φ x : lBarA c L A) : H ⧸ θH) =
      QuotientGroup.mk' θH ⟨(x : G), hLAH x.2⟩ := fun x => rfl
  have hφL : ∀ (l : G) (hl : l ∈ L), φ ⟨l, Subgroup.mem_sup_left hl⟩ ∈ D.L₀ := by
    intro l hl
    rw [← hL₀]
    exact Subgroup.mem_subgroupOf.mpr ⟨⟨l, le_normalizer_zpowers_of_mem hL hl⟩,
      Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hφC : ∀ z : (L ⊔ A : Subgroup G), (z : G) ∈ Sec4.thetaQuotCentralizer L →
      φ z ∈ Subgroup.centralizer (D.L₀ : Set (lBarA c L A)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [← hL₀] at hw
    obtain ⟨l', hl', hl'w⟩ := Subgroup.mem_subgroupOf.mp hw
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hφv z, ← hl'w]
    exact (Res2Proof.mk_commute_of_mem_thetaQuotCentralizer hL (x := ⟨z, hLAH z.2⟩) (l := l')
      hz (Subgroup.mem_subgroupOf.mp hl')).symm
  obtain ⟨l, hlL, d, hdC, hald⟩ := exists_mul_of_mem_sup
    (fun d hd => (Sec6.mem_thetaQuotCentralizer_iff.mp hd).1) haLC
  have hdeq : d = l⁻¹ * a := by rw [hald]; group
  have hdLA : d ∈ L ⊔ A := by
    rw [hdeq]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left hlL)) (Subgroup.mem_sup_right haA)
  intro x hx
  have hxLA : x ∈ L ⊔ A := (hEle.trans inf_le_left) hx.1
  have h1 : φ ⟨d, hdLA⟩ * φ ⟨x, hxLA⟩ = φ ⟨x, hxLA⟩ * φ ⟨d, hdLA⟩ :=
    D.commute_of_mem_centralizer (hφC ⟨d, hdLA⟩ hdC) (hφC ⟨x, hxLA⟩ hx.2)
  have h2 : φ ⟨l, Subgroup.mem_sup_left hlL⟩ * φ ⟨x, hxLA⟩ =
      φ ⟨x, hxLA⟩ * φ ⟨l, Subgroup.mem_sup_left hlL⟩ :=
    Subgroup.mem_centralizer_iff.mp (hφC ⟨x, hxLA⟩ hx.2) _ (hφL l hlL)
  have ha' : (⟨a, Subgroup.mem_sup_right haA⟩ : (L ⊔ A : Subgroup G)) =
      ⟨l, Subgroup.mem_sup_left hlL⟩ * ⟨d, hdLA⟩ := Subtype.ext hald
  have h3 : φ ⟨a, Subgroup.mem_sup_right haA⟩ * φ ⟨x, hxLA⟩ =
      φ ⟨x, hxLA⟩ * φ ⟨a, Subgroup.mem_sup_right haA⟩ := by
    rw [ha', map_mul, mul_assoc, h1, ← mul_assoc, h2, mul_assoc]
  have h4 : φ (⟨a, Subgroup.mem_sup_right haA⟩ * ⟨x, hxLA⟩ * ⟨a, Subgroup.mem_sup_right haA⟩⁻¹ *
      ⟨x, hxLA⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h3]
    group
  set g' : (L ⊔ A : Subgroup G) := ⟨a, Subgroup.mem_sup_right haA⟩ * ⟨x, hxLA⟩ *
    ⟨a, Subgroup.mem_sup_right haA⟩⁻¹ * ⟨x, hxLA⟩⁻¹ with hg'
  have hg'val : (g' : G) = a * x * a⁻¹ * x⁻¹ := rfl
  have h5 : QuotientGroup.mk' θH ⟨(g' : G), hLAH g'.2⟩ = 1 := by
    rw [← hφv g', h4]
    rfl
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h5
  have hθ3 : ¬ 3 ∣ Nat.card θH :=
    (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.2.1
  have hgmem : a * x * a⁻¹ * x⁻¹ ∈ Subgroup.zpowers c :=
    (struct_holds G A c L E hCfg).2.1 a haA x hx.1
  have hpow : (⟨(g' : G), hLAH g'.2⟩ : H) ^ 3 ^ 1 = 1 := by
    apply Subtype.ext
    simpa [hg'val] using hZ3 _ hgmem
  have hg1 : (⟨(g' : G), hLAH g'.2⟩ : H) = 1 := eq_one_of_mem_of_pow_three_pow hθ3 h5 hpow
  simpa [hg'val] using congrArg Subtype.val hg1

theorem s3_holds : S3 := by
  intro G _ _ A c L E F a b R Y hY hbC _ haLC
  obtain ⟨hD, hSL2, -, hEle, hEe, hE27, hEC, hEL, -⟩ := hY.hCfg
  have hcL : c ∈ L := mem_of_isSLThreePiTwo slTwoCenter hD hSL2
  have hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ResProof.isSLThreePi_of_isSLThreePiTwo hD hSL2
  have hty : Item131bProof.HeisType (L ⧸ aschbacherSolvableCore 3 L) := Or.inl hSL
  obtain ⟨-, hP1, -, -⟩ :=
    Item131bProof.e_facts hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  have hP1a := commutes_of_mem_sup_thetaQuotCentralizer hY.hCfg hY.haA haLC
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := hY.hD.isElemAbelian
  have hnE : ¬ ∀ e ∈ E, a * e = e * a := by
    intro hall
    have hFC : F ≤ Subgroup.centralizer (E : Set G) := by
      calc F = Subgroup.zpowers a ⊔ (E ⊓ F) := hY.hFgen
        _ ≤ Subgroup.centralizer (E : Set G) := by
          refine sup_le (Subgroup.zpowers_le.mpr ?_) (fun y hy => ?_)
          · exact Subgroup.mem_centralizer_iff.mpr fun e he => (hall e he).symm
          · exact Subgroup.mem_centralizer_iff.mpr fun e he => hEcomm e he y hy.1
    have hcommFE : ∀ f ∈ F, ∀ e ∈ E, f * e = e * f := fun f hf e he =>
      (Subgroup.mem_centralizer_iff.mp (hFC hf) e he).symm
    have hel : CFSG.Assembly.IsElemAbelian 3 (F ⊔ E) :=
      CFSG.Open.IsElemAbelian.sup_of_commute hFe hEe hcommFE
    have hFE : F ⊔ E = F := hY.hD.eq_of_le hel le_sup_left
    have hEF : E ≤ F := hFE ▸ le_sup_right
    have h27 : Nat.card (E ⊓ F : Subgroup G) = 27 := by
      rw [inf_eq_left.mpr hEF]
      exact hE27
    rw [hY.hFEcard] at h27
    omega
  set S : Subgroup G := E ⊓ Subgroup.centralizer ({a} : Set G) with hS
  have hP1S : E ⊓ Sec4.thetaQuotCentralizer L ≤ S := by
    intro x hx
    refine ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := hP1a x hx
    have h2 : a * x = x * a := by
      calc a * x = (a * x * a⁻¹ * x⁻¹) * (x * a) := by group
        _ = x * a := by rw [h, one_mul]
    exact h2.symm
  have hbS : b ∈ S := by
    refine ⟨hY.hbE, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (hFe.1.is_comm.comm ⟨b, hY.hD.mem_A⟩ ⟨a, hY.haF⟩)
  have hSE : S ≤ E := inf_le_left
  have hdvd1 : 9 ∣ Nat.card S := hP1 ▸ Subgroup.card_dvd_of_le hP1S
  have hdvd2 : Nat.card S ∣ 27 := hE27 ▸ Subgroup.card_dvd_of_le hSE
  have hne : Nat.card S ≠ 27 := by
    intro h
    apply hnE
    have hSEeq : S = E := Subgroup.eq_of_le_of_card_ge hSE (by rw [h, hE27])
    intro e he
    have hes : e ∈ S := hSEeq ▸ he
    exact (Subgroup.mem_centralizer_singleton_iff.mp hes.2).symm
  have hS9 : Nat.card S = 9 := by
    have hle : Nat.card S ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd2
    have hpos : 0 < Nat.card S := Nat.card_pos
    obtain ⟨m, hm⟩ := hdvd1
    have hm3 : m ≤ 3 := by omega
    interval_cases m
    · omega
    · omega
    · rw [hm] at hdvd2
      omega
    · omega
  have hPeq : E ⊓ Sec4.thetaQuotCentralizer L = S :=
    Subgroup.eq_of_le_of_card_ge hP1S (by rw [hS9, hP1])
  exact hbC (hPeq ▸ hbS)

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
