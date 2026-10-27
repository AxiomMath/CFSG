module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineU3Fix
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteen
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineU3Hyp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

section Certified


private theorem exists_odd_lift {K : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hsurj : Function.Surjective φ) (hker : IsPGroup 2 φ.ker)
    {X₀ : Subgroup X} (hodd : Odd (Nat.card X₀)) :
    ∃ X₁ : Subgroup G, X₁ ≤ K ∧ Odd (Nat.card X₁) ∧ (X₁.subgroupOf K).map φ = X₀ := by
  classical
  let P : Subgroup ↥K := X₀.comap φ
  let ψP : ↥P →* X := φ.comp P.subtype
  have hψPker : ψP.ker = φ.ker.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rfl
  have hψPrange : ψP.range = X₀ := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact p.2
    · intro hy
      obtain ⟨k, hk⟩ := hsurj y
      refine ⟨⟨k, ?_⟩, hk⟩
      rw [Subgroup.mem_comap, hk]
      exact hy
  have hkerP : IsPGroup 2 ψP.ker := by
    rw [hψPker]
    exact hker.comap_subtype
  obtain ⟨m, hm⟩ := hkerP.exists_card_dvd_pow
  have hindex : ψP.ker.index = Nat.card X₀ := by
    rw [Subgroup.index_ker, hψPrange]
  have hcop : Nat.Coprime (Nat.card ψP.ker) ψP.ker.index := by
    rw [hindex]
    exact (hodd.coprime_two_left.pow_left m).coprime_dvd_left hm
  obtain ⟨X₁'', hcomp⟩ := Subgroup.exists_left_complement'_of_coprime (N := ψP.ker) hcop
  have hcardX₁'' : Nat.card X₁'' = Nat.card X₀ := by
    rw [← hcomp.index_eq_card, hindex]
  have hmap : X₁''.map ψP = X₀ := by
    have hsup : X₁'' ⊔ ψP.ker = ⊤ := hcomp.sup_eq_top
    have hker_map : ψP.ker.map ψP = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨x, hx, rfl⟩
      simpa using (MonoidHom.mem_ker.mp hx)
    have h1 : (X₁'' ⊔ ψP.ker).map ψP = (⊤ : Subgroup ↥P).map ψP :=
      congrArg (Subgroup.map ψP) hsup
    rw [Subgroup.map_sup, hker_map, sup_bot_eq, ← MonoidHom.range_eq_map, hψPrange] at h1
    exact h1
  refine ⟨(X₁''.map P.subtype).map K.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have hcard1 : Nat.card ↥((X₁''.map P.subtype).map K.subtype) =
        Nat.card ↥(X₁''.map P.subtype) :=
      Subgroup.card_map_of_injective (f := K.subtype) Subtype.coe_injective
    have hcard2 : Nat.card ↥(X₁''.map P.subtype) = Nat.card ↥X₁'' :=
      Subgroup.card_map_of_injective (f := P.subtype) Subtype.coe_injective
    rw [hcard1, hcard2, hcardX₁'']
    exact hodd
  · have hsub : ((X₁''.map P.subtype).map K.subtype).subgroupOf K =
        X₁''.map P.subtype := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨h, hh, hhx⟩
        have : h = x := Subtype.ext hhx
        rwa [← this]
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hsub, Subgroup.map_map]
    simpa [ψP] using hmap

theorem IsMinFam16.le_center_of_forall_mem_centralizer (hF₁ : PSUThreeRootFacts)
    (hF₂ : PerfectPSUThreeFact) (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) {n : ℕ}
    (hn : Nat.card ↥(SevenK.barSub (conjClosure V H) φ V) = 2 ^ n)
    (hcase : commutator X = ⊤ ∧ IsPSUGp (X ⧸ Subgroup.center X) 3 n)
    {X₀ : Subgroup X} (hX₀ : X₀ ≤ centralizer (SevenK.barSub (conjClosure V H) φ V : Set X))
    (hodd : Odd (Nat.card ↥X₀))
    (hc : ∀ c : ↥(conjClosure V H), Odd (orderOf c) → φ c ∈ X₀ →
      (c : G) ∈ centralizer (V₀ : Set G)) :
    X₀ ≤ Subgroup.center X := by
  classical
  by_contra hX₀nc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Fam16 M U S H := hH.1
  have hIea : IsElemAbelian 2 (iSub16 V H) := Cex16.isElemAbelian_iSub16 h1 hS h hF
  have hHnormI : H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  obtain ⟨D⟩ := exists_modDataE (J := H) (E := iSub16 V H) hIea hHnormI
  let V' : Subgroup (VG (D.img H)) := UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V)
  let E' : Subgroup (VG (D.img H)) := vHat (D.img H)
  have hHyp : SevenK.Hyp716 V' ⊤ E' := IsMinFam16.hyp716_UAOf_img h1 h5 hS h hH hV D
  obtain ⟨ψ, hψbar, hψproj⟩ :=
    IsMinFam16.exists_isBarMap_kSub_UAOf_img h1 h5 hS h hH hV D
  have hpsk : IsPSUGp (↥(D.img (conjClosure V H)) ⧸
      Subgroup.center ↥(D.img (conjClosure V H))) 3 n :=
    Cex16.isPSUGp_img_conjClosure h1 h5 hS h hF hV hQ D hφ hcase
  have hrk : rk ↥(SevenK.barSub (kSub V' ⊤ E') ψ V') = n :=
    Cex16.rk_barSub_UAOf_img h1 h5 hS h hH hV hQ D hφ hn hψproj
  have hker_eq : φ.ker = (pCoreOf 2 (conjClosure V H)).subgroupOf (conjClosure V H) := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφ.ker_iff k
  have hker_pg : IsPGroup 2 φ.ker := by
    rw [hker_eq]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure V H)).comap_subtype
  obtain ⟨X₁, hX₁K, hX₁odd, hφX₁⟩ :=
    exists_odd_lift (K := conjClosure V H) hφ.surjective hker_pg hodd
  have hV_le_H : V ≤ H := h.V_le_S.trans hH.1.1
  have hK_le_H : conjClosure V H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun h hh z hz =>
      H.mul_mem (H.mul_mem hh (hV_le_H hz)) (H.inv_mem hh)
  have hX₁H : X₁ ≤ H := hX₁K.trans hK_le_H
  have hA : D.img X₁ ≤ D.img H := D.img_mono hX₁H
  let X' : Subgroup (VG (D.img H)) := aHat (D.img H) (D.img X₁)
  have hX'1 : X' ≠ ⊥ := by
    intro hbot
    have hA_bot : D.img X₁ = ⊥ := (aHat_eq_bot_iff (G := D.img H) hA).mp hbot
    have hX₁C : X₁ ≤ centralizer (iSub16 V H : Set G) :=
      D.le_centralizer_of_img_eq_bot hX₁H hA_bot
    have hX₀_le_Z : X₀ ≤ Subgroup.center X := by
      rw [← hφX₁]
      rintro y ⟨k, hk, rfl⟩
      exact Cex16.map_centralizer_iSub16_le_center h1 h5 hS h hF hV hQ hφ hcase k
        (hX₁C hk)
    exact hX₀nc hX₀_le_Z
  have hX'odd : Odd (Nat.card ↥X') := by
    have hcardX' : Nat.card ↥X' = Nat.card ↥(D.img X₁) := by
      change Nat.card ↥(aHat (D.img H) (D.img X₁)) = Nat.card ↥(D.img X₁)
      rw [aHat]
      rw [Subgroup.card_map_of_injective SemidirectProduct.inr_injective]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
    have hdvd : Nat.card ↥(D.img X₁) ∣ Nat.card ↥(X₁.subgroupOf H) :=
      Subgroup.card_map_dvd (X₁.subgroupOf H) D.ρ
    have hX₁sub : Nat.card ↥(X₁.subgroupOf H) = Nat.card ↥X₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₁H).toEquiv
    rw [hcardX']
    exact Odd.of_dvd_nat (hX₁sub.symm ▸ hX₁odd) hdvd
  have hAssump : Assumption131 (D.img H) (D.conjImgFam V) (D.conjImgSpace V₀ V)
      (mRank (D.img V)) := Cex16.assumption131_iSub16 h1 h5 hS h hF hV D
  have hΓV : D.img V ∈ D.conjImgFam V := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
  have hinf : V' ⊓ pCoreOf 2 (⊤ : Subgroup (VG (D.img H))) =
      wHat (D.img H) (D.conjImgSpace V₀ V (D.img V)) :=
    inf_pCoreOf_UAOf hAssump hΓV
  have hVA_eq : D.conjImgSpace V₀ V (D.img V) = D.sp V₀ :=
    Cex16.conjImgSpace_img_eq h1 h5 hS h hF hV D
  have hwHat_le_iSub : wHat (D.img H) (D.conjImgSpace V₀ V (D.img V)) ≤
      iSub V' ⊤ E' := by
    rw [← hinf]
    exact le_iSup₂_of_le V' hHyp.mem le_rfl
  have hiSub_le_pcore : iSub V' ⊤ E' ≤ pCoreOf 2 (⊤ : Subgroup (VG (D.img H))) := by
    unfold iSub
    exact iSup_le fun U => iSup_le fun _ => inf_le_right
  have hV'inf : V' ⊓ iSub V' ⊤ E' = wHat (D.img H) (D.sp V₀) := by
    have h1 : V' ⊓ iSub V' ⊤ E' = V' ⊓ pCoreOf 2 (⊤ : Subgroup (VG (D.img H))) := by
      refine le_antisymm (le_inf inf_le_left (inf_le_right.trans hiSub_le_pcore)) ?_
      exact le_inf inf_le_left (hinf.le.trans hwHat_le_iSub)
    rw [h1, hinf, hVA_eq]
  have hX'cent : ⁅wHat (D.img H) (D.sp V₀), X'⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨w, hw, rfl⟩ := mem_wHat.mp ha
    obtain ⟨v, hv, rfl⟩ := D.mem_sp.mp hw
    change b ∈ aHat (D.img H) (D.img X₁) at hb
    obtain ⟨g, hg, hb_eq⟩ := mem_aHat.mp hb
    obtain ⟨j, hj, hgjρ⟩ := D.mem_img.mp hg
    let xK : ↥(conjClosure V H) := ⟨(j : G), hX₁K hj⟩
    have hoddK : Odd (orderOf xK) := by
      have h1 : orderOf xK = orderOf (⟨(j : G), hj⟩ : ↥X₁) := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      rw [h1]
      exact Odd.of_dvd_nat hX₁odd (orderOf_dvd_natCard _)
    have hφK : φ xK ∈ X₀ := by
      have hmem : xK ∈ X₁.subgroupOf (conjClosure V H) := hj
      have hmap := Subgroup.mem_map_of_mem φ hmem
      rwa [hφX₁] at hmap
    have hcj : (j : G) ∈ centralizer (V₀ : Set G) := hc xK hoddK hφK
    have hfix : (g : LGL 2 D.W) (D.ι v) = D.ι v := by
      rw [← hgjρ, D.ρ_ι j v hv.2]
      have hcv : (j : G) * v * (j : G)⁻¹ = v := by
        rw [(Subgroup.mem_centralizer_iff.mp hcj v hv.1).symm]
        group
      rw [hcv]
    have key := inr_mul_inl_mul_inr_inv (G := D.img H) g (D.ι v)
    rw [hfix] at key
    have hgoal : (SemidirectProduct.inr g : VG (D.img H)) *
        (SemidirectProduct.inl (Multiplicative.ofAdd (D.ι v)) : VG (D.img H)) =
        (SemidirectProduct.inl (Multiplicative.ofAdd (D.ι v)) : VG (D.img H)) *
          (SemidirectProduct.inr g : VG (D.img H)) := by
      calc (SemidirectProduct.inr g : VG (D.img H)) *
            (SemidirectProduct.inl (Multiplicative.ofAdd (D.ι v)) : VG (D.img H))
          = ((SemidirectProduct.inr g : VG (D.img H)) *
              (SemidirectProduct.inl (Multiplicative.ofAdd (D.ι v)) : VG (D.img H)) *
              (SemidirectProduct.inr g : VG (D.img H))⁻¹) *
              (SemidirectProduct.inr g : VG (D.img H)) := by
            group
        _ = (SemidirectProduct.inl (Multiplicative.ofAdd (D.ι v)) : VG (D.img H)) *
              (SemidirectProduct.inr g : VG (D.img H)) := by
            rw [key]
    rw [hb_eq]
    exact hgoal
  have hX'C : ∀ x ∈ X', ∀ v ∈ V', ⁅x, v⁆ ∈ iSub V' ⊤ E' := by
    have hVK : V ≤ conjClosure V H := le_conjClosure V H
    have hρ : ∀ (j : ↥H), (j : G) ∈ X₁ → ∀ (v₀ : ↥H), (v₀ : G) ∈ V →
        D.ρ ⁅j, v₀⁆ = 1 := by
      intro j hj v₀ hv₀
      rw [D.ρ_eq_one_iff]
      have hmemK : ((⁅j, v₀⁆ : ↥H) : G) ∈ conjClosure V H :=
        (conjClosure V H).mul_mem
          ((conjClosure V H).mul_mem
            ((conjClosure V H).mul_mem (hX₁K hj) (hVK hv₀))
            ((conjClosure V H).inv_mem (hX₁K hj)))
          ((conjClosure V H).inv_mem (hVK hv₀))
      let cK : ↥(conjClosure V H) := ⟨((⁅j, v₀⁆ : ↥H) : G), hmemK⟩
      have hφ1 : φ cK = 1 := by
        have hjk : φ (⟨(j : G), hX₁K hj⟩ : ↥(conjClosure V H)) ∈ X₀ := by
          have hmem : (⟨(j : G), hX₁K hj⟩ : ↥(conjClosure V H)) ∈
              X₁.subgroupOf (conjClosure V H) := hj
          have hmap := Subgroup.mem_map_of_mem φ hmem
          rwa [hφX₁] at hmap
        have hvk : φ (⟨(v₀ : G), hVK hv₀⟩ : ↥(conjClosure V H)) ∈
            SevenK.barSub (conjClosure V H) φ V :=
          SevenK.mem_barSub.mpr ⟨⟨(v₀ : G), hVK hv₀⟩, hv₀, rfl⟩
        have hc := Subgroup.mem_centralizer_iff.mp (hX₀ hjk)
          (φ (⟨(v₀ : G), hVK hv₀⟩ : ↥(conjClosure V H))) hvk
        have hce : φ cK = ⁅φ (⟨(j : G), hX₁K hj⟩ : ↥(conjClosure V H)),
            φ (⟨(v₀ : G), hVK hv₀⟩ : ↥(conjClosure V H))⁆ := by
          rw [← map_commutatorElement]
          rfl
        rw [hce, commutatorElement_eq_one_iff_mul_comm]
        exact hc.symm
      exact hQ ((hφ.ker_iff cK).mp hφ1)
    have hcommA : D.img X₁ ≤ Subgroup.centralizer (D.img V : Set (LGL 2 D.W)) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨j, hj, rfl⟩ := D.mem_img.mp hg
      obtain ⟨v₀, hv₀, rfl⟩ := D.mem_img.mp ha
      have h1 : ⁅D.ρ j, D.ρ v₀⁆ = 1 := by
        rw [← map_commutatorElement, hρ j hj v₀ hv₀]
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    have hxcent : X' ≤ Subgroup.centralizer
        (wHat (D.img H) (D.sp V₀) : Set (VG (D.img H))) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hX'cent
    have hxcent' : X' ≤ Subgroup.centralizer
        (wHat (D.img H) (D.conjImgSpace V₀ V (D.img V)) : Set (VG (D.img H))) := by
      rw [hVA_eq]
      exact hxcent
    have hXA : X' ≤ Subgroup.centralizer
        (aHat (D.img H) (D.img V) : Set (VG (D.img H))) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      change x ∈ aHat (D.img H) (D.img X₁) at hx
      obtain ⟨g, hg, rfl⟩ := mem_aHat.mp ha
      obtain ⟨gx, hgx, rfl⟩ := mem_aHat.mp hx
      have hc := Subgroup.mem_centralizer_iff.mp (hcommA hgx) g hg
      have hc' : g * gx = gx * g := Subtype.ext hc
      simpa only [map_mul] using congrArg
        (fun z : ↥(D.img H) => (SemidirectProduct.inr z : VG (D.img H))) hc'
    have hcent_sup : Subgroup.centralizer
        ((wHat (D.img H) (D.conjImgSpace V₀ V (D.img V)) ⊔
          aHat (D.img H) (D.img V) : Subgroup (VG (D.img H))) : Set (VG (D.img H))) =
        Subgroup.centralizer
          (wHat (D.img H) (D.conjImgSpace V₀ V (D.img V)) : Set (VG (D.img H))) ⊓
        Subgroup.centralizer (aHat (D.img H) (D.img V) : Set (VG (D.img H))) := by
      exact le_antisymm
        (le_inf (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right)))
        (Subgroup.le_centralizer_iff.mp (sup_le
          (Subgroup.le_centralizer_iff.mp inf_le_left)
          (Subgroup.le_centralizer_iff.mp inf_le_right)))
    have hV'def : V' = wHat (D.img H) (D.conjImgSpace V₀ V (D.img V)) ⊔
        aHat (D.img H) (D.img V) := rfl
    have hXV : X' ≤ Subgroup.centralizer (V' : Set (VG (D.img H))) := by
      rw [hV'def, hcent_sup]
      exact le_inf hxcent' hXA
    intro x hx v hv
    have hcomm := Subgroup.mem_centralizer_iff.mp (hXV hx) v hv
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm]
    exact (iSub V' ⊤ E').one_mem
  have hX'K : X' ≤ kSub V' ⊤ E' := by
    have hEnorm : (E'.subgroupOf (⊤ : Subgroup (VG (D.img H)))).Normal :=
      (normal_vHat (G := D.img H)).subgroupOf _
    haveI hKsub_normal : (kSub V' ⊤ E').Normal := by
      have h1 := kSub_subgroupOf_normal (V := V') (H := ⊤) (E := E') le_top hEnorm
        (fun _ _ => le_top)
      have h2 : (⊤ : Subgroup (VG (D.img H))) ≤
          Subgroup.normalizer (kSub V' ⊤ E' : Set (VG (D.img H))) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp h1
      exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h2)
    let ρH : ↥H →* ↥(D.img H) :=
      D.ρ.codRestrict (D.img H) fun k => D.mem_img.mpr ⟨k, k.2, rfl⟩
    let ρinr : ↥H →* VG (D.img H) :=
      (SemidirectProduct.inr : ↥(D.img H) →* VG (D.img H)).comp ρH
    let S : Subgroup ↥H := (kSub V' ⊤ E').comap ρinr
    have hV_le : V.subgroupOf H ≤ S := by
      intro z hz
      rw [Subgroup.mem_comap]
      refine le_kSub hHyp.mem (Subgroup.mem_sup_right ?_)
      exact mem_aHat.mpr ⟨ρH z, D.mem_img.mpr ⟨z, Subgroup.mem_subgroupOf.mp hz, rfl⟩, rfl⟩
    have hK_le : conjClosure V H ≤ S.map H.subtype := by
      rw [conjClosure]
      refine (closure_le _).mpr ?_
      rintro x ⟨h, hh, z, hz, rfl⟩
      have hxH : h * z * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh (hV_le_H hz)) (H.inv_mem hh)
      refine Subgroup.mem_map.mpr ⟨⟨h * z * h⁻¹, hxH⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      have hzS : ρinr ⟨z, hV_le_H hz⟩ ∈ kSub V' ⊤ E' := hV_le hz
      have hxz : (⟨h * z * h⁻¹, hxH⟩ : ↥H) =
          ⟨h, hh⟩ * ⟨z, hV_le_H hz⟩ * ⟨h, hh⟩⁻¹ := by
        ext
        simp [mul_assoc]
      rw [hxz, map_mul, map_mul, map_inv]
      exact hKsub_normal.conj_mem _ hzS _
    intro x hx
    change x ∈ aHat (D.img H) (D.img X₁) at hx
    obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hx
    obtain ⟨j, hj, hgj⟩ := D.mem_img.mp hg
    have hmem : (j : G) ∈ S.map H.subtype := hK_le (hX₁K hj)
    obtain ⟨kH, hkH, hkHeq⟩ := Subgroup.mem_map.mp hmem
    rw [Subgroup.mem_comap] at hkH
    have hkHeq' : kH = ⟨(j : G), hX₁H hj⟩ := Subtype.ext (by simpa using hkHeq)
    have hρinr : ρinr kH = (SemidirectProduct.inr g : VG (D.img H)) := by
      rw [hkHeq']
      show (SemidirectProduct.inr (ρH ⟨(j : G), hX₁H hj⟩) : VG (D.img H)) =
        SemidirectProduct.inr g
      congr 1
      apply Subtype.ext
      show D.ρ ⟨(j : G), hX₁H hj⟩ = (g : LGL 2 D.W)
      rw [show (⟨(j : G), hX₁H hj⟩ : ↥H) = j from Subtype.ext rfl]
      exact hgj
    rwa [hρinr] at hkH
  have h716 := seven_sixteen hF₁ hF₂ hHyp hψbar hpsk hrk hX'K hX'1 hX'odd hX'C
  exact h716 (by rw [hV'inf]; exact hX'cent)

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
