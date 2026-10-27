module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepKFacts
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.K412Conjugacy
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

open Equiv in
theorem kf148A10Irred_holds :
    ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* alternatingGroup (Fin 10)) →
      ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
        Sec21.IsIrreducibleOn (Sec4.autIn ⊤ E) := by
  intro X _ _ ⟨φ⟩ E hE hE27 F hF
  set ι : X →* Perm (Fin 10) := (alternatingGroup (Fin 10)).subtype.comp φ.toMonoidHom with hιdef
  have hιinj : Function.Injective ι :=
    (alternatingGroup (Fin 10)).subtype_injective.comp φ.injective
  have hιA : ∀ x : X, ι x ∈ alternatingGroup (Fin 10) := fun x => (φ x).2
  set E' := E.map ι with hE'
  have hE'27 : Nat.card E' = 27 := by
    rw [hE', Subgroup.card_map_of_injective hιinj, hE27]
  have hE'ab : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨g, hg⟩ := KFacts.K412.exists_conj_eq_eTwentySeven hE'27 hE'ab
  set c := (MulAut.conj g).toMonoidHom with hc
  set F₀ : Subgroup X := F.map E.subtype with hF₀
  have hF₀E : F₀ ≤ E := Subgroup.map_subtype_le F
  set U := (F₀.map ι).map c with hU
  have hUE : U ≤ KFacts.KP2.eTwentySeven := by
    rw [← hg, hU, hE']
    exact Subgroup.map_mono (Subgroup.map_mono hF₀E)
  have hN : KFacts.KP2.normAlt ≤ Subgroup.normalizer (U : Set (Perm (Fin 10))) := by
    intro h hh
    obtain ⟨hhN, hhA⟩ := Subgroup.mem_inf.mp hh
    set h' := g⁻¹ * h * g with hh'
    have hh'A : h' ∈ alternatingGroup (Fin 10) := by
      have := (alternatingGroup.normal (α := Fin 10)).conj_mem h hhA g⁻¹
      rwa [inv_inv] at this
    set x : X := φ.symm ⟨h', hh'A⟩ with hxdef
    have hιx : ι x = h' := by
      rw [hιdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hxdef, MulEquiv.apply_symm_apply]
      rfl
    have hcE : ∀ y : Perm (Fin 10), y ∈ E' ↔ g * y * g⁻¹ ∈ KFacts.KP2.eTwentySeven := by
      intro y
      rw [← hg]
      constructor
      · intro hy
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y', hy', hyy⟩
        have : y' = y := by
          have := congrArg (fun z => g⁻¹ * z * g) hyy
          simpa [hc, MulAut.conj_apply, mul_assoc] using this
        rwa [← this]
    have hxN : x ∈ Subgroup.normalizer (E : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have key : ∀ z : X, z ∈ E ↔ ι z ∈ E' := fun z =>
        ⟨fun hz => ⟨z, hz, rfl⟩, fun ⟨w, hw, hwz⟩ => (hιinj hwz) ▸ hw⟩
      rw [key y, key (x * y * x⁻¹), map_mul, map_mul, map_inv, hιx, hcE (ι y),
        hcE (h' * ι y * h'⁻¹)]
      have e1 : g * (h' * ι y * h'⁻¹) * g⁻¹ = h * (g * ι y * g⁻¹) * h⁻¹ := by
        rw [hh']; group
      rw [e1]
      exact Subgroup.mem_normalizer_iff.mp hhN _
    have hψ : E.normalizerMonoidHom ⟨x, hxN⟩ ∈ Sec4.autIn ⊤ E :=
      Sec4.mem_autIn_iff.mpr ⟨x, hxN, Subgroup.mem_top _, rfl⟩
    have hFx := hF _ hψ
    have hxF : ∀ z : X, z ∈ F₀ → x * z * x⁻¹ ∈ F₀ := by
      rintro _ ⟨z, hz, rfl⟩
      have : E.normalizerMonoidHom ⟨x, hxN⟩ z ∈ F := by
        rw [← hFx]
        exact ⟨z, hz, rfl⟩
      exact ⟨_, this, rfl⟩
    have hxF' : ∀ z : X, z ∈ F₀ → x⁻¹ * z * x⁻¹⁻¹ ∈ F₀ := by
      intro z hz
      obtain ⟨⟨w, hwE⟩, hwF, rfl⟩ := hz
      have hinv : (E.normalizerMonoidHom ⟨x, hxN⟩)⁻¹ ⟨w, hwE⟩ ∈ F := by
        have : (⟨w, hwE⟩ : E) ∈ F.map (E.normalizerMonoidHom ⟨x, hxN⟩).toMonoidHom := by
          rw [hFx]; exact hwF
        obtain ⟨v, hv, hvw⟩ := this
        have : (E.normalizerMonoidHom ⟨x, hxN⟩)⁻¹ ⟨w, hwE⟩ = v := by
          rw [← hvw]
          simp
        rw [this]
        exact hv
      refine ⟨_, hinv, ?_⟩
      change ((Subgroup.normalizerMonoidHom E ⟨x, hxN⟩)⁻¹ ⟨w, hwE⟩ : X) = x⁻¹ * w * x⁻¹⁻¹
      rw [← map_inv]
      rfl
    have hcx : ∀ w : X, c (ι (x * w * x⁻¹)) = h * c (ι w) * h⁻¹ := by
      intro w
      have e1 : ι (x * w * x⁻¹) = h' * ι w * h'⁻¹ := by rw [map_mul, map_mul, map_inv, hιx]
      rw [e1]
      simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hh']
      group
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨ι (x * z * x⁻¹), ⟨_, hxF z hz, rfl⟩, hcx z⟩
    · intro hu
      obtain ⟨_, ⟨z, hz, rfl⟩, hzu⟩ := hu
      refine ⟨ι (x⁻¹ * z * x⁻¹⁻¹), ⟨_, hxF' z hz, rfl⟩, ?_⟩
      have e2 := hcx (x⁻¹ * z * x⁻¹⁻¹)
      rw [show x * (x⁻¹ * z * x⁻¹⁻¹) * x⁻¹ = z by group] at e2
      have e3 : c (ι z) = h * u * h⁻¹ := hzu
      rw [e3] at e2
      calc c (ι (x⁻¹ * z * x⁻¹⁻¹)) = h⁻¹ * (h * c (ι (x⁻¹ * z * x⁻¹⁻¹)) * h⁻¹) * h := by group
        _ = h⁻¹ * (h * u * h⁻¹) * h := by rw [← e2]
        _ = u := by group
  rcases KFacts.KP2.eq_bot_or_eq_eTwentySeven hUE hN with hbot | htop
  · left
    rw [hU, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective,
      Subgroup.map_eq_bot_iff_of_injective _ hιinj, hF₀,
      Subgroup.map_eq_bot_iff_of_injective _ E.subtype_injective] at hbot
    exact hbot
  · right
    have h1 : (F₀.map ι).map c = (E.map ι).map c := by rw [← hU, htop, ← hg]
    have h2 : F₀ = E := by
      have := Subgroup.map_injective (MulAut.conj g).injective h1
      exact Subgroup.map_injective hιinj this
    rw [eq_top_iff]
    intro z _
    have hz : (z : X) ∈ F₀ := by rw [h2]; exact z.2
    obtain ⟨w, hw, hwz⟩ := hz
    rwa [← Subtype.ext hwz]

namespace Item148Rank

variable {G : Type} [Group G] [Finite G] {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem mem_img148_centralizer_of_commute148 (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {e : G} (he : e ∈ A) (he3 : e ^ 3 = 1) {U : Subgroup G} (hUY : U ≤ Y)
    {x : ↥(Y ⊔ A) ⧸ ker148 A Y} (hx : x ∈ img148 A Y U)
    (hxe : alpha148 A Y e he * x = x * alpha148 A Y e he) :
    x ∈ img148 A Y (Y ⊓ Subgroup.centralizer ({e} : Set G)) := by
  obtain ⟨j, hjM, hjU, rfl⟩ := mem_img148_iff.mp hx
  set N := pPrimeCoreOf 3 Y with hNdef
  have hB3 : IsPGroup 3 (Subgroup.zpowers e) := by
    refine isPGroup_three_of_pow148 fun b hb => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he3, one_zpow]
  have hBN : Subgroup.zpowers e ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.mpr ((hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)) he)
  have hk : ∀ b ∈ Subgroup.zpowers e, j⁻¹ * (b * j * b⁻¹) ∈ N := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hekM : e ^ k ∈ Y ⊔ A := Subgroup.mem_sup_right (A.zpow_mem he k)
    have hbjM : e ^ k * j * (e ^ k)⁻¹ ∈ Y ⊔ A :=
      (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem hekM hjM) ((Y ⊔ A).inv_mem hekM)
    have hpow : (alpha148 A Y e he) ^ k * QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ =
        QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ * (alpha148 A Y e he) ^ k :=
      (Commute.zpow_left hxe k).eq
    have h1 : QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ =
        QuotientGroup.mk' (ker148 A Y) ⟨e ^ k * j * (e ^ k)⁻¹, hbjM⟩ := by
      have e1 : QuotientGroup.mk' (ker148 A Y) ⟨e ^ k * j * (e ^ k)⁻¹, hbjM⟩ =
          (alpha148 A Y e he) ^ k * QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ *
            ((alpha148 A Y e he) ^ k)⁻¹ := by
        rw [alpha148_eq_mk', ← map_zpow, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e1, hpow, mul_assoc, mul_inv_cancel, mul_one]
    exact mk'_ker148_eq_iff.mp h1
  obtain ⟨y, hy, hyc⟩ := exists_commute_mem_coset148 hB3 (coprime_card_pPrimeCoreOf 3 Y) hBN hk
  have hjY : j ∈ Y := hUY hjU
  have hyY : y ∈ Y := by
    have := Y.mul_mem hjY (pPrimeCoreOf_le 3 Y hy)
    rwa [mul_inv_cancel_left] at this
  refine mem_img148_iff.mpr ⟨y, Subgroup.mem_sup_left hyY, ⟨hyY, ?_⟩, ?_⟩
  · show y ∈ Subgroup.centralizer ({e} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hyc e (Subgroup.mem_zpowers e)).symm
  · exact (mk'_ker148_eq_iff.mpr hy).symm

omit [Finite G] in
theorem isSubnormal_img148_subgroupOf148 {K H J : Subgroup G} (hHM : H ≤ Y ⊔ A) (hKH : K ≤ H)
    (hsn : (K.subgroupOf H).IsSubnormal) (hJH : img148 A Y J ≤ img148 A Y H) :
    ((img148 A Y K).subgroupOf (img148 A Y J)).IsSubnormal := by
  set f : ↥H →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hHM) with hf
  have hrange : f.range = img148 A Y H := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact mem_img148_iff.mpr ⟨h, hHM h.2, h.2, rfl⟩
    · intro hx
      obtain ⟨g, hg, hgH, rfl⟩ := mem_img148_iff.mp hx
      exact ⟨⟨g, hgH⟩, rfl⟩
  have hKmap : (K.subgroupOf H).map f = img148 A Y K := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact mem_img148_iff.mpr ⟨h, hHM h.2, Subgroup.mem_subgroupOf.mp hh, rfl⟩
    · intro hx
      obtain ⟨g, hg, hgK, rfl⟩ := mem_img148_iff.mp hx
      exact ⟨⟨g, hKH hgK⟩, Subgroup.mem_subgroupOf.mpr hgK, rfl⟩
  have hS := hsn.map (MonoidHom.rangeRestrict_surjective f)
  have hJf : img148 A Y J ≤ f.range := hrange ▸ hJH
  have hT := hS.comap (Subgroup.inclusion hJf)
  convert hT using 1
  ext z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, ← hKmap]
  constructor
  · rintro ⟨h, hh, hfh⟩
    refine ⟨h, hh, Subtype.ext ?_⟩
    rw [MonoidHom.coe_rangeRestrict]
    exact hfh
  · rintro ⟨h, hh, hfh⟩
    refine ⟨h, hh, ?_⟩
    have := congrArg Subtype.val hfh
    rw [MonoidHom.coe_rangeRestrict] at this
    exact this

theorem not_forall_commute_of_lift148Ten148 (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {e : G} (he : e ∈ A) (he3 : e ^ 3 = 1) {K J : Subgroup G}
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G))) (hKJ : K ≤ J)
    (hJY : J ≤ Y) (hTen : Lift148Ten A Y K J) :
    ¬ ∀ x ∈ img148 A Y J, alpha148 A Y e he * x = x * alpha148 A Y e he := by
  intro hall
  obtain ⟨⟨φK⟩, ⟨φJ⟩⟩ := hTen
  set H := Y ⊓ Subgroup.centralizer ({e} : Set G) with hH
  have hHM : H ≤ Y ⊔ A := inf_le_left.trans le_sup_left
  have hKH : K ≤ H := le_of_mem_thetaComponentsIn hK
  have hsn : (K.subgroupOf H).IsSubnormal := ((mem_thetaComponentsIn_iff.mp hK).2).2.1
  have hJH : img148 A Y J ≤ img148 A Y H := fun x hx =>
    mem_img148_centralizer_of_commute148 hAY he he3 hJY hx (hall x hx)
  have hKJ' : img148 A Y K ≤ img148 A Y J := img148_mono hKJ
  have hT := isSubnormal_img148_subgroupOf148 hHM hKH hsn hJH
  have : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hsimp : IsSimpleGroup ↥(img148 A Y J) := φJ.isSimpleGroup
  have hcK : Nat.card ↥(img148 A Y K) = 2520 := by
    rw [Nat.card_congr φK.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  have hcJ : Nat.card ↥(img148 A Y J) = 1814400 := by
    rw [Nat.card_congr φJ.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2
  rcases hT.eq_bot_or_top_of_isSimpleGroup hsimp with h | h
  · have hbot : img148 A Y K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hKJ' hx⟩ : ↥(img148 A Y J)) ∈ (img148 A Y K).subgroupOf (img148 A Y J) :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
    rw [hbot, Subgroup.card_bot] at hcK
    norm_num at hcK
  · have heq : img148 A Y K = img148 A Y J := by
      refine le_antisymm hKJ' fun x hx => ?_
      have hx' : (⟨x, hx⟩ : ↥(img148 A Y J)) ∈ (img148 A Y K).subgroupOf (img148 A Y J) := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hx'
    rw [heq, hcJ] at hcK
    norm_num at hcK

theorem img148_le_of_lift148Ten148 (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {e : G} (he : e ∈ A) {K J : Subgroup G}
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G))) (hKJ : K ≤ J)
    (hJY : J ≤ Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hsec : Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G))
    (hTen : Lift148Ten A Y K J) : img148 A Y A ≤ img148 A Y J := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKM : K ≤ Y ⊔ A :=
    ((le_of_mem_thetaComponentsIn hK).trans inf_le_left).trans le_sup_left
  have hnot := not_forall_commute_of_lift148Ten148 hAY he (hA3 e he) hK hKJ hJY hTen
  obtain ⟨-, ⟨φJ⟩⟩ := hTen
  set Jb := img148 A Y J with hJb
  obtain ⟨hZ, hin⟩ := a10_facts148 ↥Jb ⟨φJ⟩
  have hJn : img148 A Y A ≤ Subgroup.normalizer (Jb : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hcen : ∀ z ∈ Jb, (∀ y ∈ Jb, z * y * z⁻¹ = y) → z = 1 := by
    intro z hz hzc
    have hmem : (⟨z, hz⟩ : ↥Jb) ∈ Subgroup.center ↥Jb := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have := hzc w w.2
      change (w : _) * z = z * w
      calc (w : _) * z = z * w * z⁻¹ * z := by rw [this]
        _ = z * w := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hj : ∀ (a : G) (ha : a ∈ A), ∃ j ∈ Jb, ∀ y ∈ Jb,
      alpha148 A Y a ha * y * (alpha148 A Y a ha)⁻¹ = j * y * j⁻¹ := fun a ha =>
    innerOn148_of_pow_three (hJn (alpha148_mem_img148 ha)) (alpha148_pow_three hA3 ha) hin
  have heα : ∀ k : ℤ, (∀ y ∈ Jb, (alpha148 A Y e he) ^ k * y * ((alpha148 A Y e he) ^ k)⁻¹ = y) →
      (alpha148 A Y e he) ^ k = 1 := by
    intro k hk
    have he3 : (alpha148 A Y e he) ^ 3 = 1 := alpha148_pow_three hA3 he
    have hmod : (alpha148 A Y e he) ^ k = (alpha148 A Y e he) ^ (k % 3) := by
      have hk3 : k = k % 3 + 3 * (k / 3) := by omega
      conv_lhs => rw [hk3, zpow_add, zpow_mul]
      rw [show (alpha148 A Y e he) ^ (3 : ℤ) = 1 by rw [zpow_ofNat, he3], one_zpow, mul_one]
    have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases h3 with h0 | h1 | h2
    · rw [hmod, h0, zpow_zero]
    · exfalso
      apply hnot
      intro y hy
      have := hk y hy
      rw [hmod, h1, zpow_one] at this
      calc alpha148 A Y e he * y = alpha148 A Y e he * y * (alpha148 A Y e he)⁻¹ *
            alpha148 A Y e he := by group
        _ = y * alpha148 A Y e he := by rw [this]
    · exfalso
      apply hnot
      intro y hy
      have h2' : ∀ z ∈ Jb, (alpha148 A Y e he) ^ (2 : ℤ) * z *
          ((alpha148 A Y e he) ^ (2 : ℤ))⁻¹ = z := fun z hz => by
        have := hk z hz
        rwa [hmod, h2] at this
      have heq : alpha148 A Y e he =
          (alpha148 A Y e he) ^ (2 : ℤ) * (alpha148 A Y e he) ^ (2 : ℤ) := by
        rw [← zpow_add, show (2 : ℤ) + 2 = 3 + 1 from rfl, zpow_add, zpow_ofNat, he3, one_mul,
          zpow_one]
      have hconj : alpha148 A Y e he * y * (alpha148 A Y e he)⁻¹ = y := by
        calc alpha148 A Y e he * y * (alpha148 A Y e he)⁻¹ =
            ((alpha148 A Y e he) ^ (2 : ℤ) * (alpha148 A Y e he) ^ (2 : ℤ)) * y *
              ((alpha148 A Y e he) ^ (2 : ℤ) * (alpha148 A Y e he) ^ (2 : ℤ))⁻¹ := by
                rw [← heq]
          _ = (alpha148 A Y e he) ^ (2 : ℤ) * ((alpha148 A Y e he) ^ (2 : ℤ) * y *
              ((alpha148 A Y e he) ^ (2 : ℤ))⁻¹) * ((alpha148 A Y e he) ^ (2 : ℤ))⁻¹ := by
                group
          _ = y := by rw [h2' y hy, h2' y hy]
      calc alpha148 A Y e he * y = alpha148 A Y e he * y * (alpha148 A Y e he)⁻¹ *
            alpha148 A Y e he := by group
        _ = y * alpha148 A Y e he := by rw [hconj]
  intro x hx
  obtain ⟨a, haM, haA, rfl⟩ := mem_img148_iff.mp hx
  have hxα : QuotientGroup.mk' (ker148 A Y) ⟨a, haM⟩ = alpha148 A Y a haA := rfl
  rw [hxα]
  obtain ⟨j, hjJ, hjc⟩ := hj a haA
  set α := alpha148 A Y a haA with hαdef
  have hwJ : ∀ y ∈ Jb, (α * j⁻¹) * y * (α * j⁻¹)⁻¹ = y := by
    intro y hy
    have hy' : j⁻¹ * y * j ∈ Jb := Jb.mul_mem (Jb.mul_mem (Jb.inv_mem hjJ) hy) hjJ
    calc (α * j⁻¹) * y * (α * j⁻¹)⁻¹ = α * (j⁻¹ * y * j) * α⁻¹ := by group
      _ = j * (j⁻¹ * y * j) * j⁻¹ := hjc _ hy'
      _ = y := by group
  have hwA : ∀ (b : G) (hb : b ∈ A), alpha148 A Y b hb * (α * j⁻¹) =
      (α * j⁻¹) * alpha148 A Y b hb := by
    intro b hb
    obtain ⟨jb, hjbJ, hjbc⟩ := hj b hb
    have hjj : j * jb = jb * j := by
      have hab : α * alpha148 A Y b hb = alpha148 A Y b hb * α := alpha148_comm hAc haA hb
      have hz : (j * jb) * (jb * j)⁻¹ = 1 := by
        refine hcen _ (Jb.mul_mem (Jb.mul_mem hjJ hjbJ) (Jb.inv_mem (Jb.mul_mem hjbJ hjJ)))
          fun y hy => ?_
        have hy1 : jb⁻¹ * (j⁻¹ * y * j) * jb ∈ Jb := Jb.mul_mem (Jb.mul_mem (Jb.inv_mem hjbJ)
          (Jb.mul_mem (Jb.mul_mem (Jb.inv_mem hjJ) hy) hjJ)) hjbJ
        have hy2 : j⁻¹ * y * j ∈ Jb := Jb.mul_mem (Jb.mul_mem (Jb.inv_mem hjJ) hy) hjJ
        have hy3 : j⁻¹ * (jb⁻¹ * y * jb) * j ∈ Jb := Jb.mul_mem (Jb.mul_mem (Jb.inv_mem hjJ)
          (Jb.mul_mem (Jb.mul_mem (Jb.inv_mem hjbJ) hy) hjbJ)) hjJ
        have hy4 : jb⁻¹ * y * jb ∈ Jb := Jb.mul_mem (Jb.mul_mem (Jb.inv_mem hjbJ) hy) hjbJ
        have e1 : (j * jb) * (jb⁻¹ * (j⁻¹ * y * j) * jb) * (j * jb)⁻¹ = y := by group
        have e2 : α * alpha148 A Y b hb * (jb⁻¹ * (j⁻¹ * y * j) * jb) *
            (α * alpha148 A Y b hb)⁻¹ = y := by
          calc α * alpha148 A Y b hb * (jb⁻¹ * (j⁻¹ * y * j) * jb) *
                (α * alpha148 A Y b hb)⁻¹ =
              α * (alpha148 A Y b hb * (jb⁻¹ * (j⁻¹ * y * j) * jb) *
                (alpha148 A Y b hb)⁻¹) * α⁻¹ := by group
            _ = α * (jb * (jb⁻¹ * (j⁻¹ * y * j) * jb) * jb⁻¹) * α⁻¹ := by rw [hjbc _ hy1]
            _ = α * (j⁻¹ * y * j) * α⁻¹ := by group
            _ = j * (j⁻¹ * y * j) * j⁻¹ := hjc _ hy2
            _ = y := by group
        have e3 : alpha148 A Y b hb * α * (j⁻¹ * (jb⁻¹ * y * jb) * j) *
            (alpha148 A Y b hb * α)⁻¹ = y := by
          calc alpha148 A Y b hb * α * (j⁻¹ * (jb⁻¹ * y * jb) * j) *
                (alpha148 A Y b hb * α)⁻¹ =
              alpha148 A Y b hb * (α * (j⁻¹ * (jb⁻¹ * y * jb) * j) * α⁻¹) *
                (alpha148 A Y b hb)⁻¹ := by group
            _ = alpha148 A Y b hb * (j * (j⁻¹ * (jb⁻¹ * y * jb) * j) * j⁻¹) *
                (alpha148 A Y b hb)⁻¹ := by rw [hjc _ hy3]
            _ = alpha148 A Y b hb * (jb⁻¹ * y * jb) * (alpha148 A Y b hb)⁻¹ := by group
            _ = jb * (jb⁻¹ * y * jb) * jb⁻¹ := hjbc _ hy4
            _ = y := by group
        have hjjb : ∀ z ∈ Jb, (j * jb) * z * (j * jb)⁻¹ = α * alpha148 A Y b hb * z *
            (α * alpha148 A Y b hb)⁻¹ := by
          intro z hz
          have hz1 : jb * z * jb⁻¹ ∈ Jb := Jb.mul_mem (Jb.mul_mem hjbJ hz) (Jb.inv_mem hjbJ)
          calc (j * jb) * z * (j * jb)⁻¹ = j * (jb * z * jb⁻¹) * j⁻¹ := by group
            _ = α * (jb * z * jb⁻¹) * α⁻¹ := (hjc _ hz1).symm
            _ = α * (alpha148 A Y b hb * z * (alpha148 A Y b hb)⁻¹) * α⁻¹ := by
                rw [hjbc _ hz]
            _ = α * alpha148 A Y b hb * z * (α * alpha148 A Y b hb)⁻¹ := by group
        have hjbj : ∀ z ∈ Jb, (jb * j) * z * (jb * j)⁻¹ = alpha148 A Y b hb * α * z *
            (alpha148 A Y b hb * α)⁻¹ := by
          intro z hz
          have hz1 : j * z * j⁻¹ ∈ Jb := Jb.mul_mem (Jb.mul_mem hjJ hz) (Jb.inv_mem hjJ)
          calc (jb * j) * z * (jb * j)⁻¹ = jb * (j * z * j⁻¹) * jb⁻¹ := by group
            _ = alpha148 A Y b hb * (j * z * j⁻¹) * (alpha148 A Y b hb)⁻¹ := (hjbc _ hz1).symm
            _ = alpha148 A Y b hb * (α * z * α⁻¹) * (alpha148 A Y b hb)⁻¹ := by rw [hjc _ hz]
            _ = alpha148 A Y b hb * α * z * (alpha148 A Y b hb * α)⁻¹ := by group
        have hy5 : (jb * j)⁻¹ * y * (jb * j) ∈ Jb :=
          Jb.mul_mem (Jb.mul_mem (Jb.inv_mem (Jb.mul_mem hjbJ hjJ)) hy) (Jb.mul_mem hjbJ hjJ)
        calc (j * jb) * (jb * j)⁻¹ * y * ((j * jb) * (jb * j)⁻¹)⁻¹ =
            (j * jb) * ((jb * j)⁻¹ * y * (jb * j)) * (j * jb)⁻¹ := by group
          _ = α * alpha148 A Y b hb * ((jb * j)⁻¹ * y * (jb * j)) *
              (α * alpha148 A Y b hb)⁻¹ := hjjb _ hy5
          _ = alpha148 A Y b hb * α * ((jb * j)⁻¹ * y * (jb * j)) *
              (alpha148 A Y b hb * α)⁻¹ := by rw [hab]
          _ = (jb * j) * ((jb * j)⁻¹ * y * (jb * j)) * (jb * j)⁻¹ := (hjbj _ hy5).symm
          _ = y := by group
      calc j * jb = (j * jb) * (jb * j)⁻¹ * (jb * j) := by group
        _ = jb * j := by rw [hz, one_mul]
    have hjinv : alpha148 A Y b hb * j⁻¹ * (alpha148 A Y b hb)⁻¹ = j⁻¹ := by
      rw [hjbc _ (Jb.inv_mem hjJ)]
      calc jb * j⁻¹ * jb⁻¹ = j⁻¹ * (j * jb) * j⁻¹ * jb⁻¹ := by group
        _ = j⁻¹ * (jb * j) * j⁻¹ * jb⁻¹ := by rw [hjj]
        _ = j⁻¹ := by group
    have hab : alpha148 A Y b hb * α = α * alpha148 A Y b hb := alpha148_comm hAc hb haA
    calc alpha148 A Y b hb * (α * j⁻¹) = (alpha148 A Y b hb * α) * j⁻¹ := by group
      _ = (α * alpha148 A Y b hb) * j⁻¹ := by rw [hab]
      _ = α * (alpha148 A Y b hb * j⁻¹ * (alpha148 A Y b hb)⁻¹) * alpha148 A Y b hb := by
          group
      _ = (α * j⁻¹) * alpha148 A Y b hb := by rw [hjinv]
  have hw3 : (α * j⁻¹) ^ 3 = 1 := by
    have hαj : α * j = j * α := by
      have := hjc j hjJ
      calc α * j = α * j * α⁻¹ * α := by group
        _ = j * j * j⁻¹ * α := by rw [this]
        _ = j * α := by group
    have hj3 : j ^ 3 = 1 := by
      refine hcen _ (Jb.pow_mem hjJ 3) fun y hy => ?_
      have hc1 : ∀ z ∈ Jb, j * z * j⁻¹ = α * z * α⁻¹ := fun z hz => (hjc z hz).symm
      have hy1 : α * y * α⁻¹ ∈ Jb := hc1 y hy ▸ Jb.mul_mem (Jb.mul_mem hjJ hy) (Jb.inv_mem hjJ)
      have hy2 : α * (α * y * α⁻¹) * α⁻¹ ∈ Jb :=
        hc1 _ hy1 ▸ Jb.mul_mem (Jb.mul_mem hjJ hy1) (Jb.inv_mem hjJ)
      have hα3 : α ^ 3 = 1 := alpha148_pow_three hA3 haA
      calc j ^ 3 * y * (j ^ 3)⁻¹ = j * (j * (j * y * j⁻¹) * j⁻¹) * j⁻¹ := by
            rw [pow_three]; group
        _ = α * (α * (α * y * α⁻¹) * α⁻¹) * α⁻¹ := by rw [hc1 y hy, hc1 _ hy1, hc1 _ hy2]
        _ = α ^ 3 * y * (α ^ 3)⁻¹ := by rw [pow_three]; group
        _ = y := by rw [hα3]; group
    have hcomm : Commute α j⁻¹ := (Commute.inv_right hαj)
    rw [hcomm.mul_pow, alpha148_pow_three hA3 haA, one_mul, inv_pow, hj3, inv_one]
  have hwc : α * j⁻¹ ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨b, hbM, hbA, rfl⟩ := mem_img148_iff.mp hz
    exact hwA b hbA
  have hwAα := mem_img148_of_commute hAF hAY hwc hw3
  obtain ⟨c, hcM, hcA, hcw⟩ := mem_img148_iff.mp hwAα
  have hc' : alpha148 A Y c hcA = α * j⁻¹ := hcw
  have hcK : alpha148 A Y c hcA ∈
      Subgroup.centralizer (img148 A Y K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := hwJ z (img148_mono hKJ hz)
    rw [hc']
    calc z * (α * j⁻¹) = ((α * j⁻¹) * z * (α * j⁻¹)⁻¹) * (α * j⁻¹) := by rw [h1]
      _ = (α * j⁻¹) * z := by group
  have hcsec := mem_sectionCentralizer_of_alpha148 hKM hcA hcK
  rw [hsec] at hcsec
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcsec
  have hck : alpha148 A Y c hcA = (alpha148 A Y e he) ^ k := by
    rw [alpha148_eq_mk', alpha148_eq_mk', ← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hk.symm)
  have hw1 : α * j⁻¹ = 1 := by
    rw [← hc', hck]
    refine heα k fun y hy => ?_
    rw [← hck, hc']
    exact hwJ y hy
  have hαj : α = j := by
    calc α = α * j⁻¹ * j := by group
      _ = j := by rw [hw1, one_mul]
  rw [hαj]
  exact hjJ

theorem isIrreducibleOn_wStar148 (hA : Late.IsE27 A)
    {J : Subgroup G} (hle : img148 A Y A ≤ img148 A Y J)
    (hJ10 : Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 10))) :
    Sec21.IsIrreducibleOn (wStar A) := by
  have hA10 := kf148A10Irred_holds
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  set Q := ↥(Y ⊔ A) ⧸ ker148 A Y
  set Jb := img148 A Y J with hJb
  set Ab := img148 A Y A with hAb
  set E : Subgroup ↥Jb := Ab.subgroupOf Jb with hE
  obtain ⟨hAbE, hAb27⟩ := img148_isE27 (Y := Y) hA
  have hE27 : Nat.card E = 27 := by
    rw [hE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hAb27]
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have h := congrArg Subtype.val (hAbE.1.is_comm.comm
        ⟨((x : ↥Jb) : Q), Subgroup.mem_subgroupOf.mp x.2⟩
        ⟨((y : ↥Jb) : Q), Subgroup.mem_subgroupOf.mp y.2⟩)
      simpa using h
    · apply Subtype.ext
      have h := hAbE.2 ((x : ↥Jb) : Q) (Subgroup.mem_subgroupOf.mp hx)
      simpa using h
  have hirr := hA10 ↥Jb hJ10 E hEab hE27
  set f0 : ↥A →* Q := (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion le_sup_right)
    with hf0
  have hf0A : ∀ a : ↥A, f0 a ∈ Ab := fun a => alpha148_mem_img148 a.2
  set ι : ↥A →* ↥E := (f0.codRestrict Jb fun a => hle (hf0A a)).codRestrict E
    fun a => Subgroup.mem_subgroupOf.mpr (hf0A a) with hι
  have hιval : ∀ a : ↥A, (((ι a : ↥E) : ↥Jb) : Q) = alpha148 A Y a a.2 := fun a => rfl
  have hιinj : Function.Injective ι := by
    intro a b hab
    have h := congrArg (fun z : ↥E => ((z : ↥Jb) : Q)) hab
    simp only [hιval] at h
    exact Subtype.ext (alpha148_injective hA3 a.2 b.2 h)
  have hιsurj : Function.Surjective ι := by
    intro z
    obtain ⟨g, hgM, hgA, hg⟩ := mem_img148_iff.mp (Subgroup.mem_subgroupOf.mp z.2)
    refine ⟨⟨g, hgA⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [hιval]
    exact hg
  intro F hF
  have hF' : ∀ ψ ∈ Sec4.autIn ⊤ E, (F.map ι).map ψ.toMonoidHom = F.map ι := by
    intro ψ hψ
    obtain ⟨x, hxN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hψ
    have hxQ : (x : Q) ∈ Subgroup.normalizer (Ab : Set Q) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have h1 := (Subgroup.mem_normalizer_iff.mp hxN ⟨y, hle hy⟩).mp
          (Subgroup.mem_subgroupOf.mpr hy)
        exact Subgroup.mem_subgroupOf.mp h1
      · intro hy
        have hy' : y ∈ Jb := by
          have h2 : (x : Q)⁻¹ * ((x : Q) * y * (x : Q)⁻¹) * (x : Q) ∈ Jb :=
            Jb.mul_mem (Jb.mul_mem (Jb.inv_mem x.2) (hle hy)) x.2
          rwa [show (x : Q)⁻¹ * ((x : Q) * y * (x : Q)⁻¹) * (x : Q) = y by group] at h2
        have h1 := (Subgroup.mem_normalizer_iff.mp hxN ⟨y, hy'⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hy)
        exact Subgroup.mem_subgroupOf.mp h1
    have hT : IsPGroup 3 ↥(A.subgroupOf (Y ⊔ A)) := by
      refine isPGroup_three_of_pow148 fun b hb => ?_
      exact Subtype.ext (by simpa using hA3 _ (Subgroup.mem_subgroupOf.mp hb))
    have : Fact (IsPGroup 3 ↥(A.subgroupOf (Y ⊔ A))) := ⟨hT⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcop : Nat.Coprime 3 (Nat.card (ker148 A Y)) := by
      rw [ker148, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        ((pPrimeCoreOf_le 3 Y).trans le_sup_left)).toEquiv]
      exact coprime_card_pPrimeCoreOf 3 Y
    have hlift := CFSG.normalizer_map_quotient_eq_map_normalizer 3 (A.subgroupOf (Y ⊔ A))
      (ker148 A Y) inferInstance hcop
    have hxQ' : (x : Q) ∈ ((Subgroup.normalizer
        ((A.subgroupOf (Y ⊔ A) : Subgroup ↥(Y ⊔ A)) : Set ↥(Y ⊔ A))).map
          (QuotientGroup.mk' (ker148 A Y))) := by
      rw [← hlift]
      exact hxQ
    obtain ⟨n, hn, hnx⟩ := hxQ'
    have hw : (n : G) ∈ Subgroup.normalizer (A : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨a, Subgroup.mem_sup_right ha⟩).mp
          (Subgroup.mem_subgroupOf.mpr ha)
        simpa using Subgroup.mem_subgroupOf.mp h1
      · intro ha
        have haM : a ∈ Y ⊔ A := by
          have h2 : (n : G)⁻¹ * ((n : G) * a * (n : G)⁻¹) * (n : G) ∈ Y ⊔ A :=
            (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).inv_mem n.2)
              (Subgroup.mem_sup_right ha)) n.2
          rwa [show (n : G)⁻¹ * ((n : G) * a * (n : G)⁻¹) * (n : G) = a by group] at h2
        have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨a, haM⟩).mpr
          (Subgroup.mem_subgroupOf.mpr (by simpa using ha))
        exact Subgroup.mem_subgroupOf.mp h1
    set φ := A.normalizerMonoidHom ⟨(n : G), hw⟩ with hφ
    have hφW : φ ∈ wStar A := Sec4.mem_autIn_iff.mpr ⟨n, hw, Subgroup.mem_top _, rfl⟩
    have hcomm : ∀ a : ↥A, E.normalizerMonoidHom ⟨x, hxN⟩ (ι a) = ι (φ a) := by
      intro a
      apply Subtype.ext
      apply Subtype.ext
      change (x : Q) * alpha148 A Y a a.2 * (x : Q)⁻¹ =
        alpha148 A Y ((n : G) * a * (n : G)⁻¹) ((Subgroup.mem_normalizer_iff.mp hw _).mp a.2)
      rw [← hnx, alpha148_eq_mk', alpha148_eq_mk', ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hFφ := hF φ hφW
    ext z
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨φ a, ?_, (hcomm a).symm⟩
      rw [← hFφ]
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      have ha' : a ∈ F.map φ.toMonoidHom := by rw [hFφ]; exact ha
      obtain ⟨b, hb, hba⟩ := ha'
      refine ⟨ι b, ⟨b, hb, rfl⟩, ?_⟩
      change E.normalizerMonoidHom ⟨x, hxN⟩ (ι b) = ι a
      rw [hcomm b]
      exact congrArg ι hba
  rcases hirr (F.map ι) hF' with h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective F hιinj).mp h
  · right
    rw [eq_top_iff]
    intro a _
    have : ι a ∈ F.map ι := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨b, hb, hba⟩ := this
    rwa [← hιinj hba]

omit [Finite G] [(ker148 A Y).Normal] in
theorem map_wStar_eq_of_le_normalizer148 {B : Subgroup G}
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G))
    {φ : MulAut ↥A} (hφ : φ ∈ wStar A) :
    (B.subgroupOf A).map φ.toMonoidHom = B.subgroupOf A := by
  obtain ⟨w, hw, -, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
  have hwB := hN hw
  ext z
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hb
    rw [Subgroup.mem_subgroupOf]
    change w * (b : G) * w⁻¹ ∈ B
    exact (Subgroup.mem_normalizer_iff.mp hwB _).mp hb
  · intro hz
    rw [Subgroup.mem_subgroupOf] at hz
    have hzB : w⁻¹ * (z : G) * w⁻¹⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (inv_mem hwB) _).mp hz
    have hzA : w⁻¹ * (z : G) * w⁻¹⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hw) _).mp z.2
    refine ⟨⟨_, hzA⟩, Subgroup.mem_subgroupOf.mpr hzB, Subtype.ext ?_⟩
    change w * (w⁻¹ * (z : G) * w⁻¹⁻¹) * w⁻¹ = z
    group

omit [Finite G] [(ker148 A Y).Normal] in
theorem false_of_isIrreducibleOn_wStar148 (hirr : Sec21.IsIrreducibleOn (wStar A))
    {B : Subgroup G} (hBA : B ≤ A) (hB1 : B ≠ ⊥) (hBA' : B ≠ A)
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G)) : False := by
  rcases hirr (B.subgroupOf A) (fun φ hφ => map_wStar_eq_of_le_normalizer148 hN hφ) with
    h | h
  · exact hB1 (by rwa [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hBA] at h)
  · exact hBA' (le_antisymm hBA (Subgroup.subgroupOf_eq_top.mp h))

omit [(ker148 A Y).Normal] in
theorem false_of_isIrreducibleOn_wStar_of_oThree148 (hirr : Sec21.IsIrreducibleOn (wStar A))
    (hA : IsPGroup 3 ↥A) (hA1 : Nat.card A ≠ 1) (h9 : Nat.card (oThreeWStar A) = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := oThreeWStar A with hP
  have hP3 : IsPGroup 3 ↥P := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  set F : Subgroup ↥A :=
    { carrier := {a | ∀ φ ∈ P, φ a = a}
      mul_mem' := fun {a b} ha hb φ hφ => by rw [map_mul, ha φ hφ, hb φ hφ]
      one_mem' := fun φ _ => map_one φ
      inv_mem' := fun {a} ha φ hφ => by rw [map_inv, ha φ hφ] } with hF
  have hfix : Nat.card ↥A ≡ Nat.card ↑(MulAction.fixedPoints ↥P ↥A) [MOD 3] :=
    hP3.card_modEq_card_fixedPoints ↥A
  have hcardF : Nat.card ↑(MulAction.fixedPoints ↥P ↥A) = Nat.card F := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
    constructor
    · intro h φ hφ
      exact h ⟨φ, hφ⟩
    · intro h φ
      exact h φ.1 φ.2
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hA1 (by rw [hk, pow_zero])
  have h3A : Nat.card ↥A % 3 = 0 := by
    rw [hk]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 hk0)
  have hF3 : Nat.card F % 3 = 0 := by
    rw [← hcardF]
    have := hfix
    unfold Nat.ModEq at this
    omega
  have hFbot : F ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hF3
    norm_num at hF3
  have hFtop : F ≠ ⊤ := by
    intro htop
    have hP1 : P ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at h9
      norm_num at h9
    obtain ⟨φ, hφ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
    apply hφ1
    apply Subtype.ext
    ext a
    have ha : a ∈ F := by rw [htop]; exact Subgroup.mem_top a
    exact congrArg Subtype.val (ha φ φ.2)
  have hFinv : ∀ ψ ∈ wStar A, F.map ψ.toMonoidHom = F := by
    intro ψ hψ
    have hnorm : ∀ φ ∈ P, ψ⁻¹ * φ * ψ ∈ P := by
      intro φ hφ
      obtain ⟨φ', hφ', rfl⟩ := hφ
      refine ⟨⟨ψ, hψ⟩⁻¹ * φ' * ⟨ψ, hψ⟩, ?_, rfl⟩
      have := (CFSG.pCore_normal (p := 3) (G := wStar A)).conj_mem φ' hφ' ⟨ψ, hψ⟩⁻¹
      simpa using this
    have hle : F.map ψ.toMonoidHom ≤ F := by
      rintro _ ⟨a, ha, rfl⟩ φ hφ
      have h1 := ha (ψ⁻¹ * φ * ψ) (hnorm φ hφ)
      have h2 : φ (ψ a) = ψ ((ψ⁻¹ * φ * ψ) a) := by
        simp [MulAut.mul_apply]
      change φ (ψ a) = ψ a
      rw [h2, h1]
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective ψ.injective]
  rcases hirr F hFinv with h | h
  · exact hFbot h
  · exact hFtop h

end Item148Rank

end CFSG.RankThree.PartTwo.Sec14
