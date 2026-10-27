module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDCfg
public import CFSG.LocalAnalysis.WeakClosure81.W16QDInputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem w16q_conj_mem_centralizer {A : Subgroup G} {g z : G}
    (hg : g ∈ normalizer (A : Set G)) (hz : z ∈ centralizer (A : Set G)) :
    g * z * g⁻¹ ∈ centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro w hw
  have hgw : g⁻¹ * w * g ∈ A := (Subgroup.mem_normalizer_iff''.mp hg w).1 hw
  calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hz (g⁻¹ * w * g) hgw]
    _ = (g * z * g⁻¹) * w := by group

private theorem w16q_commutator_mul_identity (a c d : G) :
    a * c * a⁻¹ * c⁻¹ =
      (a * (c * d) * a⁻¹ * (c * d)⁻¹) *
        (c * (a * d * a⁻¹ * d⁻¹) * c⁻¹)⁻¹ := by
  have h := commutatorElement_mul_right_eq_mul_conj a c d
  simp only [commutatorElement_def] at h
  rw [h]
  group

namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

theorem mem_M_of_map_mem_normalizer (d : DichCfg M V₀ V U S H φ) {k : ↥(conjClosure V H)}
    (hk : φ k ∈ normalizer ((SevenK.barSub (conjClosure V H) φ V : Subgroup X) : Set X)) :
    (k : G) ∈ M := by
  have hVI : V ⊔ iSub16 V H ≤ S :=
    sup_le d.cfg.cex.V_le_S (d.cfg.iSub16_le_tSub16.trans inf_le_left)
  have hpoint : ∀ v ∈ V, (k : G) * v * (k : G)⁻¹ ∈ V ⊔ iSub16 V H := by
    intro v hv
    have hvK : v ∈ conjClosure V H := le_conjClosure V H hv
    let vK : ↥(conjClosure V H) := ⟨v, hvK⟩
    have hvP : φ vK ∈ SevenK.barSub (conjClosure V H) φ V :=
      Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hv)
    have h1 : φ k * φ vK * (φ k)⁻¹ ∈ SevenK.barSub (conjClosure V H) φ V :=
      (Subgroup.mem_normalizer_iff.mp hk (φ vK)).1 hvP
    have h2 : φ ⟨(k : G) * v * (k : G)⁻¹,
        (conjClosure V H).mul_mem ((conjClosure V H).mul_mem k.2 hvK)
          ((conjClosure V H).inv_mem k.2)⟩ = φ k * φ vK * (φ k)⁻¹ := by
      have heq : (⟨(k : G) * v * (k : G)⁻¹,
          (conjClosure V H).mul_mem ((conjClosure V H).mul_mem k.2 hvK)
            ((conjClosure V H).inv_mem k.2)⟩ : ↥(conjClosure V H)) = k * vK * k⁻¹ := by
        ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, vK]
      rw [heq, map_mul, map_mul, map_inv]
    have h3 : φ ⟨(k : G) * v * (k : G)⁻¹,
        (conjClosure V H).mul_mem ((conjClosure V H).mul_mem k.2 hvK)
          ((conjClosure V H).inv_mem k.2)⟩ ∈ SevenK.barSub (conjClosure V H) φ V := by
      rw [h2]
      exact h1
    exact d.mem_sup_of_map_mem_barSub h3
  have hconj : conjSubgroup V (k : G)⁻¹ ≤ S := by
    have hle : conjSubgroup V (k : G)⁻¹ ≤ V ⊔ iSub16 V H := by
      rw [conjSubgroup]
      refine (Subgroup.map_le_iff_le_comap).2 fun v hv => ?_
      simpa using hpoint v hv
    exact hle.trans hVI
  have hmem : (k : G)⁻¹ ∈ M := Cex16.mem_of_conj_le_S d.cfg.fifteen d.cfg.std d.cfg.cex hconj
  simpa using M.inv_mem hmem

theorem exists_borel_elt [Finite X] (d : DichCfg M V₀ V U S H φ) (hB : Borel166Input)
    (hn : 1 < E3.mQuot V (iSub16 V H))
    (hsh : CFSG.Quasithin.IsSz (E3.mQuot V (iSub16 V H)) X ∨
      IsU3Shape X (E3.mQuot V (iSub16 V H))) :
    ∃ y ∈ conjClosure V H, y ∈ M ∧
      (∀ x ∈ S ⊓ conjClosure V H, y * x * y⁻¹ ∈ S ⊓ conjClosure V H) ∧
      (S ⊓ conjClosure V H ≤ tSub16 V₀ S ∨
        tSub16 V₀ S ⊓ (S ⊓ conjClosure V H) ≤ V ⊔ iSub16 V H) ∧
      (∀ x ∈ S ⊓ conjClosure V H, y * x * y⁻¹ * x⁻¹ ∈ V ⊔ iSub16 V H → x ∈ V ⊔ iSub16 V H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := conjClosure V H
  let I : Subgroup G := iSub16 V H
  let TK : Subgroup G := S ⊓ K
  let T : Subgroup G := tSub16 V₀ S
  let Y : Subgroup X := SevenK.barSub K φ V
  let P : Subgroup X := (TK.subgroupOf K).map φ
  have hVK : V ≤ K := le_conjClosure V H
  have hIK : I ≤ K := d.cfg.iSub16_le_conjClosure
  have hIS : I ≤ S := d.cfg.iSub16_le_tSub16.trans inf_le_left
  have hITK : I ≤ TK := le_inf hIS hIK
  have hVT : V ≤ T := d.cfg.V_le_tSub16
  have hVS : V ≤ S := d.cfg.cex.V_le_S
  have hVTK : V ≤ TK := le_inf hVS hVK
  have hKH : K ≤ H := d.cfg.conjClosure_le_H
  have hSylH : IsSylowIn 2 S H :=
    Cex16.isSylowIn_of_fam d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16
  have hKN : (K.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH]
    exact le_normalizer_conjClosure V H
  have hSylK : IsSylowIn 2 TK K := hSylH.inf_normal hKH hKN
  have hYP : Y ≤ P := by
    show (V.subgroupOf K).map φ ≤ (TK.subgroupOf K).map φ
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono K hVTK)
  have hP2 : IsPGroup 2 P := by
    have hTK2 : IsPGroup 2 ↥TK := hSylH.isPGroup.to_le inf_le_left
    have h2 : IsPGroup 2 ↥(TK.subgroupOf K) :=
      hTK2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    exact h2.map φ
  have hPodd : ¬ 2 ∣ P.index := by
    have hker_le : φ.ker ≤ TK.subgroupOf K := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact hITK ((d.bar.ker_iff x).1 (MonoidHom.mem_ker.mp hx))
    show ¬ 2 ∣ (((S ⊓ K).subgroupOf K).map φ).index
    rw [Subgroup.index_map_eq (f := φ) (H := (S ⊓ K).subgroupOf K) d.bar.surjective hker_le]
    exact hSylK.not_dvd_relIndex
  obtain ⟨hbor, hhY, hhP, _hhodd, hhinv, hhcomm⟩ :=
    hB X Y P (E3.mQuot V I) hn (show Nat.card Y = 2 ^ (E3.mQuot V I) from d.shape.1)
      d.isElemAbelian_barSub hYP hP2 hPodd hsh
  obtain ⟨k₀, hk₀⟩ := d.bar.surjective hbor
  let y : G := (k₀ : G)
  have hyM : y ∈ M := by
    refine d.mem_M_of_map_mem_normalizer (k := k₀) ?_
    rw [hk₀]
    exact hhY
  have hyT : ∀ x ∈ S ⊓ K, y * x * y⁻¹ ∈ S ⊓ K := by
    intro x hx
    have hxK : x ∈ K := hx.2
    let xK : ↥K := ⟨x, hxK⟩
    have hxP : φ xK ∈ P := Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hx)
    have h1 : hbor * φ xK * hbor⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hhP (φ xK)).1 hxP
    have h2 : φ (k₀ * xK * k₀⁻¹) = hbor * φ xK * hbor⁻¹ := by
      rw [map_mul, map_mul, map_inv, hk₀]
    have h3 : φ (k₀ * xK * k₀⁻¹) ∈ P := by
      rw [h2]
      exact h1
    have h4 := d.mem_of_map_mem (A := TK) hITK h3
    simpa only [y, xK, Subgroup.coe_mul, Subgroup.coe_inv] using h4
  have hIN : I ≤ T ⊓ TK := le_inf d.cfg.iSub16_le_tSub16 hITK
  have hVTTK : V ≤ T ⊓ TK := le_inf hVT hVTK
  let P₀ : Subgroup X := ((T ⊓ TK).subgroupOf K).map φ
  have hYP₀ : Y ≤ P₀ := by
    show (V.subgroupOf K).map φ ≤ ((T ⊓ TK).subgroupOf K).map φ
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono K hVTTK)
  have hP₀P : P₀ ≤ P := by
    show ((T ⊓ TK).subgroupOf K).map φ ≤ (TK.subgroupOf K).map φ
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono K inf_le_right)
  have hinvP₀ : ∀ z ∈ P₀, hbor * z * hbor⁻¹ ∈ P₀ := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    have haA : (a : G) ∈ T ⊓ TK := Subgroup.mem_subgroupOf.mp ha
    have haT : (a : G) ∈ T := haA.1
    have haTK : (a : G) ∈ TK := haA.2
    have haT' : (a : G) ∈ S ⊓ centralizer (V₀ : Set G) := haT
    have hconjTK : y * (a : G) * y⁻¹ ∈ TK := hyT (a : G) haTK
    have hconjS : y * (a : G) * y⁻¹ ∈ S := hconjTK.1
    have hconjC : y * (a : G) * y⁻¹ ∈ centralizer (V₀ : Set G) :=
      w16q_conj_mem_centralizer (by rw [d.cfg.cex.hyp.normalizer₀]; exact hyM) haT'.2
    have hconjA : y * (a : G) * y⁻¹ ∈ T ⊓ TK := ⟨⟨hconjS, hconjC⟩, hconjTK⟩
    have hφ : φ (k₀ * a * k₀⁻¹) = hbor * φ a * hbor⁻¹ := by
      rw [map_mul, map_mul, map_inv, hk₀]
    rw [← hφ]
    refine Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr ?_)
    simpa only [y, Subgroup.coe_mul, Subgroup.coe_inv] using hconjA
  have hcase : S ⊓ K ≤ T ∨ T ⊓ (S ⊓ K) ≤ V ⊔ I := by
    rcases hhinv P₀ hYP₀ hP₀P hinvP₀ with hP₀Y | hP₀P'
    · right
      intro x hx
      have hxK : x ∈ K := hx.2.2
      have hxphi : φ ⟨x, hxK⟩ ∈ P₀ :=
        Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hx)
      have hxY : φ ⟨x, hxK⟩ ∈ Y := hP₀Y ▸ hxphi
      exact d.mem_sup_of_map_mem_barSub hxY
    · left
      intro x hx
      have hxK : x ∈ K := hx.2
      have hxP : φ ⟨x, hxK⟩ ∈ P :=
        Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hx)
      have hxphi : φ ⟨x, hxK⟩ ∈ P₀ := by
        rw [hP₀P']
        exact hxP
      exact (d.mem_of_map_mem (A := T ⊓ TK) hIN hxphi).1
  have hbarVI : SevenK.barSub K φ (V ⊔ I) = Y := by
    show ((V ⊔ I).subgroupOf K).map φ = (V.subgroupOf K).map φ
    have hker : I.subgroupOf K = φ.ker := by
      ext a
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact (d.bar.ker_iff a).symm
    rw [Subgroup.subgroupOf_sup hVK hIK, Subgroup.map_sup, hker,
      Subgroup.map_ker_self φ, sup_bot_eq]
  have hcomm : ∀ x ∈ S ⊓ K, y * x * y⁻¹ * x⁻¹ ∈ V ⊔ I → x ∈ V ⊔ I := by
    intro x hx hcommx
    have hxK : x ∈ K := hx.2
    let xK : ↥K := ⟨x, hxK⟩
    have hxP : φ xK ∈ P := Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hx)
    have hcommY : hbor * φ xK * hbor⁻¹ * (φ xK)⁻¹ ∈ Y := by
      have h1 : hbor * φ xK * hbor⁻¹ * (φ xK)⁻¹ = φ (k₀ * xK * k₀⁻¹ * xK⁻¹) := by
        simp only [map_mul, map_inv, hk₀]
      rw [h1, ← hbarVI]
      refine Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr ?_)
      simpa only [y, xK, Subgroup.coe_mul, Subgroup.coe_inv] using hcommx
    exact d.mem_sup_of_map_mem_barSub (hhcomm (φ xK) hxP hcommY)
  exact ⟨y, k₀.2, hyM, hyT, hcase, hcomm⟩

theorem qSub16_le_tSub16_of_borel_elt (d : DichCfg M V₀ V U S H φ) {y : G}
    (hyK : y ∈ conjClosure V H) (hyM : y ∈ M)
    (hyT : ∀ x ∈ S ⊓ conjClosure V H, y * x * y⁻¹ ∈ S ⊓ conjClosure V H)
    (hcase : S ⊓ conjClosure V H ≤ tSub16 V₀ S ∨
      tSub16 V₀ S ⊓ (S ⊓ conjClosure V H) ≤ V ⊔ iSub16 V H)
    (hcomm : ∀ x ∈ S ⊓ conjClosure V H, y * x * y⁻¹ * x⁻¹ ∈ V ⊔ iSub16 V H →
      x ∈ V ⊔ iSub16 V H) :
    qSub16 V₀ V S H ≤ tSub16 V₀ S := by
  rcases hcase with hTK | hinr
  · exact d.qSub16_le_tSub16_of_inf_le hTK
  · intro q hq
    have hqS : q ∈ S :=
      (d.cfg.qSub16_le_pCoreOf.trans
        (Cex16.pCoreOf_le_S d.cfg.one d.cfg.std d.cfg.cex d.cfg.min.fam16)) hq
    have hqKT : q ∈ conjClosure V H ⊔ tSub16 V₀ S :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (conjClosure V H ⊔ tSub16 V₀ S)) hq
    have hTKnorm : tSub16 V₀ S ≤ normalizer (conjClosure V H : Set G) :=
      (((inf_le_left : tSub16 V₀ S ≤ S)).trans d.cfg.min.fam16.1).trans
        (le_normalizer_conjClosure V H)
    have hqmem : q ∈ (conjClosure V H : Set G) * (tSub16 V₀ S : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (conjClosure V H) (tSub16 V₀ S)
        hTKnorm]
      exact hqKT
    rw [Set.mem_mul] at hqmem
    obtain ⟨a, haK, b, hbT, hab⟩ := hqmem
    have hbT' : b ∈ S ⊓ centralizer (V₀ : Set G) := hbT
    have hbS : b ∈ S := hbT'.1
    have hbC : b ∈ centralizer (V₀ : Set G) := hbT'.2
    have haS : a ∈ S := by
      have hqa : a = q * b⁻¹ := by rw [← hab]; group
      rw [hqa]
      exact S.mul_mem hqS (S.inv_mem hbS)
    have haTK : a ∈ S ⊓ conjClosure V H := ⟨haS, haK⟩
    have haM : a ∈ M := d.cfg.cex.S_le_M haS
    have hyN : y ∈ normalizer (V₀ : Set G) := by
      rw [d.cfg.cex.hyp.normalizer₀]
      exact hyM
    have haN : a ∈ normalizer (V₀ : Set G) := by
      rw [d.cfg.cex.hyp.normalizer₀]
      exact haM
    have hcommQ : y * q * y⁻¹ * q⁻¹ ∈ centralizer (V₀ : Set G) :=
      (d.cfg.iSub16_le_tSub16.trans inf_le_right) (d.comm_mem_qSub16 hq hyK)
    have hyb : y * b * y⁻¹ * b⁻¹ ∈ centralizer (V₀ : Set G) :=
      (centralizer (V₀ : Set G)).mul_mem (w16q_conj_mem_centralizer hyN hbC)
        ((centralizer (V₀ : Set G)).inv_mem hbC)
    have hayb : a * (y * b * y⁻¹ * b⁻¹) * a⁻¹ ∈ centralizer (V₀ : Set G) :=
      w16q_conj_mem_centralizer haN hyb
    have hcommA : y * a * y⁻¹ * a⁻¹ ∈ centralizer (V₀ : Set G) := by
      have hident := w16q_commutator_mul_identity y a b
      rw [hab] at hident
      rw [hident]
      exact (centralizer (V₀ : Set G)).mul_mem hcommQ
        ((centralizer (V₀ : Set G)).inv_mem hayb)
    have hcommAS : y * a * y⁻¹ * a⁻¹ ∈ S :=
      S.mul_mem (hyT a haTK).1 (S.inv_mem haS)
    have hcommAK : y * a * y⁻¹ * a⁻¹ ∈ conjClosure V H :=
      (conjClosure V H).mul_mem
        ((conjClosure V H).mul_mem ((conjClosure V H).mul_mem hyK haK)
          ((conjClosure V H).inv_mem hyK))
        ((conjClosure V H).inv_mem haK)
    have hcommAT : y * a * y⁻¹ * a⁻¹ ∈ tSub16 V₀ S := ⟨hcommAS, hcommA⟩
    have hcommATK : y * a * y⁻¹ * a⁻¹ ∈ S ⊓ conjClosure V H := ⟨hcommAS, hcommAK⟩
    have hcommVI : y * a * y⁻¹ * a⁻¹ ∈ V ⊔ iSub16 V H := hinr ⟨hcommAT, hcommATK⟩
    have haVI : a ∈ V ⊔ iSub16 V H := hcomm a haTK hcommVI
    have haT : a ∈ tSub16 V₀ S := (sup_le d.cfg.V_le_tSub16 d.cfg.iSub16_le_tSub16) haVI
    rw [← hab]
    exact (tSub16 V₀ S).mul_mem haT hbT

theorem qSub16_le_tSub16_of_borel [Finite X] (d : DichCfg M V₀ V U S H φ) (hB : Borel166Input)
    (hn : 1 < E3.mQuot V (iSub16 V H))
    (hsh : CFSG.Quasithin.IsSz (E3.mQuot V (iSub16 V H)) X ∨
      IsU3Shape X (E3.mQuot V (iSub16 V H))) :
    qSub16 V₀ V S H ≤ tSub16 V₀ S := by
  obtain ⟨y, hyK, hyM, hyT, hcase, hcomm⟩ := d.exists_borel_elt hB hn hsh
  exact d.qSub16_le_tSub16_of_borel_elt hyK hyM hyT hcase hcomm

end DichCfg

end CFSG.LocalAnalysis.WeakClosure81

end
