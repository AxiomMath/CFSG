module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SmallPermutationKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFieldExtensionFixedKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R52c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Sixteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.Quasithin.Background.E3AParamCard
public import CFSG.Quasithin.Vol2.Ch11SecDGroup
public import CFSG.Quasithin.Background.RonanD37Rank8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAAux
public import CFSG.Permutation.FiveTransitive.SylowPreimageNormalizer
public import CFSG.ClassicalGroups.SL2Sp4SylowNormalizer
public import CFSG.Quasithin.Vol2.Ch11SecEK2C
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.Vol2 CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem aParam_autI_le_one_of_card_four {Z M : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hcard : Nat.card Z = 4) :
    E3.aParam (autI hZ M) ≤ 1 := by
  classical
  have hZexp : ∀ z : IntMod Z hZ, z ^ 2 = 1 := fun z => IntMod.sq_eq_one z
  have hZcard : Nat.card (IntMod Z hZ) = 2 ^ 2 := by
    show Nat.card ↥Z = 2 ^ 2
    rw [hcard]
    norm_num
  refine E3.aParam_le_of_card_le _ ?_
  intro A _ hA2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 A :=
    isPGroup_iff_pow_pow_eq_one.mpr fun a => ⟨1, by
      have h2 : (a : MulAut (IntMod Z hZ)) ^ 2 = 1 := hA2 a a.2
      exact Subtype.ext (by simpa using h2)⟩
  have h := CFSG.RankThree.Coprime.card_le_of_isPGroup_mulAut (p := 2) hZexp hZcard A hQ
  simpa using h

theorem aParam_autI_le_two_of_card_eight {Z M : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hcard : Nat.card Z = 8) :
    E3.aParam (autI hZ M) ≤ 2 := by
  classical
  have hZexp : ∀ z : IntMod Z hZ, z ^ 2 = 1 := fun z => IntMod.sq_eq_one z
  have hZcard : Nat.card (IntMod Z hZ) = 8 := by
    show Nat.card ↥Z = 8
    exact hcard
  refine E3.aParam_le_of_card_le _ ?_
  intro A _ hA2
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have hdiv : ∀ x : A, orderOf x ∣ 2 := fun x =>
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hA2 x x.2))
    exact congrArg Subtype.val (Commute.of_orderOf_dvd_two hdiv ⟨a, ha⟩ ⟨b, hb⟩).eq
  have hAel : IsElemAbelian2 A := ⟨hcommA, hA2⟩
  have h := CFSG.Quasithin.RonanD37.card_le_four_of_card_eight hZexp hZcard hAel
  simpa using h


theorem M_le_normalizer_preTil_fixV
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H) :
    D.M ≤ Subgroup.normalizer (preTil ⊥ V hV (fixV H) : Set G) := by
  classical
  let Z : Subgroup (Vtil ⊥ V hV) := fixV H
  have hMle : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hAn : Mbar D.M ⊥ V hV ≤
      Subgroup.normalizer (H : Set (MulAut (Vtil ⊥ V hV))) :=
    Subgroup.le_normalizer_iff.mpr hHn
  have hstabA : Mbar D.M ⊥ V hV ≤ stabSub Z :=
    CFSG.Quasithin.FixVLat.le_stabSub_fixV_of_le_normalizer hAn
  intro u hu
  have hustab : u ∈ stabTil ⊥ V := hMle hu
  have huα : actTil ⊥ V hV ⟨u, hustab⟩ ∈ Mbar D.M ⊥ V hV :=
    actTil_mem_barSub ⊥ V hV hu hustab
  refine s16c1G_mem_normalizer_of_forall_actTil_mem_imgTil (V := V)
    (U := preTil ⊥ V hV (fixV H)) hV (preTil_le ⊥ V hV (fixV H)) hustab ?_
  intro w hw
  rw [imgTil_preTil] at hw ⊢
  exact (mem_stabSub.mp (hstabA huα) w).mpr hw

theorem centralizer_cClos_le_of_small_fixed_kernel
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    {p : ℕ} (hp37 : p = 3 ∨ p = 7) (hp : p ∈ D.sig)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hZcard : Nat.card (fixV H) = p + 1)
    (hfix : fixV H ≠ ⊥) :
    centralizer (E3.cClos V (D.k + 0) D.T : Set G) ≤ D.M := by
  classical
  let Z : Subgroup (Vtil ⊥ V hV) := fixV H
  have hZne : Z ≠ ⊥ := hfix
  have hZcard' : Nat.card Z = p + 1 := hZcard
  have hMle : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  let α : ↥D.M →* MulAut (Vtil ⊥ V hV) := barHom ⊥ V hV hMle
  have hαrange : α.range = Mbar D.M ⊥ V hV := range_barHom ⊥ V hV hMle
  have hAn : Mbar D.M ⊥ V hV ≤
      Subgroup.normalizer (H : Set (MulAut (Vtil ⊥ V hV))) :=
    Subgroup.le_normalizer_iff.mpr hHn
  have hstabA : Mbar D.M ⊥ V hV ≤ stabSub Z :=
    CFSG.Quasithin.FixVLat.le_stabSub_fixV_of_le_normalizer hAn
  have hpprime : Nat.Prime p := by
    rcases hp37 with rfl | rfl <;> norm_num
  obtain ⟨E, hEab, hEcard⟩ :=
    exists_isElemAbelian_subgroupOf_of_le_pRank (M := D.M) (p := p) (k := 3)
      hpprime (hx.three_le p hp)
  let aE : ↥E →* MulAut (Vtil ⊥ V hV) := α.comp E.subtype
  have hEtoMbar : ∀ e : ↥E, aE e ∈ Mbar D.M ⊥ V hV := by
    intro e
    rw [← hαrange]
    exact MonoidHom.mem_range.mpr ⟨E.subtype e, rfl⟩
  have hEstab : ∀ e : ↥E, aE e ∈ stabSub Z := fun e => hstabA (hEtoMbar e)
  let aEs : ↥E →* ↥(stabSub Z) := aE.codRestrict (stabSub Z) hEstab
  let rE : ↥E →* MulAut Z := (resHom Z).comp aEs
  let φ : ↥E →* Equiv.Perm Z := (MulAut.toPerm Z).comp rE
  have hEexp : ∀ e : ↥E, e ^ p = 1 := by
    intro e
    apply Subtype.ext
    show ((e : ↥D.M) ^ p) = 1
    exact hEab.2 (e : ↥D.M) e.2
  have hsmall :=
    sq_le_card_ker_and_not_isCyclic_of_perm_card_eq_prime_add_one (p := p) hp37
      hEexp (by simpa using hEcard) hZcard' φ
  let B : Subgroup ↥E := φ.ker
  have hBcard : p ^ 2 ≤ Nat.card B := hsmall.1
  have hBnc : ¬ IsCyclic B := hsmall.2
  have hBp : IsPGroup p B := by
    refine isPGroup_iff_pow_pow_eq_one.mpr fun b => ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    simpa using hEexp (b : ↥E)
  let X : Subgroup G := (B.map E.subtype).map D.M.subtype
  have hXp : IsPGroup p X := IsPGroup.map (IsPGroup.map hBp E.subtype) D.M.subtype
  have hXnc : ¬ IsCyclic X := by
    intro hc
    have hc0 : IsCyclic (B.map E.subtype) :=
      (Subgroup.equivMapOfInjective (B.map E.subtype) D.M.subtype
        D.M.subtype_injective).isCyclic.mpr hc
    exact hBnc ((Subgroup.equivMapOfInjective B E.subtype E.subtype_injective).isCyclic.mpr hc0)
  have hXM : X ≤ D.M := Subgroup.map_subtype_le _
  let Zg : Subgroup G := preTil ⊥ V hV Z
  have hZgcard : Nat.card Zg = Nat.card Z := by
    have h := s16c4_card_preTil (V₀ := ⊥) (V := V) hV bot_le (S := Z)
    rw [h, Subgroup.card_bot, one_mul]
  have hZg_ne : Zg ≠ ⊥ := by
    intro h0
    apply hZne
    have hc : Nat.card Z = 1 := by
      rw [← hZgcard, h0, Subgroup.card_bot]
    exact Subgroup.card_eq_one.mp hc
  have hZgV : Zg ≤ V := preTil_le ⊥ V hV Z
  have hZgT : Zg ≤ D.T := hZgV.trans (s15_13A_le_T h)
  have hTnorm : D.T ≤ Subgroup.normalizer (Zg : Set G) := by
    let Z' : Subgroup (Vtil ⊥ V hV) := fixV H
    have hMnorm : D.M ≤ Subgroup.normalizer (preTil ⊥ V hV Z' : Set G) :=
      M_le_normalizer_preTil_fixV D hV h hHn
    exact D.sylowM.le.trans hMnorm
  obtain ⟨z, hzZg, hz1, hzC⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecD.exists_mem_centralizer_ne_one
      D.sylowM.isPGroup hZgT hTnorm hZg_ne
  have hzV : z ∈ V := hZgV hzZg
  have hzZ : mkTil ⊥ V hV (IntMod.mk hV ⟨z, hzV⟩) ∈ Z :=
    (mem_preTil_iff_of_mem ⊥ V hV Z hzV).mp hzZg
  have hXz : X ≤ Subgroup.centralizer ({z} : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hy
    let m : G := ((E.subtype b : ↥D.M) : G)
    have hmM : m ∈ D.M := (E.subtype b).2
    have hmstab : m ∈ stabTil ⊥ V := hMle hmM
    have hbker : φ b = 1 := hb
    have htoPermInj : Function.Injective (MulAut.toPerm Z) := fun a c hac => by
      refine MulEquiv.ext fun w => ?_
      exact congrArg (fun q : Equiv.Perm Z => q w) hac
    have hrb : rE b = 1 := by
      apply htoPermInj
      simpa [φ] using hbker
    have hker : aEs b ∈ (resHom Z).ker := by
      rw [MonoidHom.mem_ker]
      exact hrb
    rw [ker_resHom] at hker
    have hcent : aE b ∈ centSub Z := Subgroup.mem_subgroupOf.mp hker
    have hfixq : aE b (mkTil ⊥ V hV (IntMod.mk hV ⟨z, hzV⟩)) =
        mkTil ⊥ V hV (IntMod.mk hV ⟨z, hzV⟩) :=
      (mem_centSub.mp hcent) _ hzZ
    have hfixq' : barHom ⊥ V hV hMle (E.subtype b)
        (mkTil ⊥ V hV (IntMod.mk hV ⟨z, hzV⟩)) =
        mkTil ⊥ V hV (IntMod.mk hV ⟨z, hzV⟩) := by
      simpa [aE, α] using hfixq
    have hconj : m * z * m⁻¹ = z := by
      have h3' := (barHom_fix_iff ⊥ V hV hMle (E.subtype b)
        (IntMod.mk hV ⟨z, hzV⟩)).mp hfixq'
      have h3'' : m * z * m⁻¹ * z⁻¹ = 1 := by
        rw [Subgroup.mem_bot] at h3'
        simpa [m, IntMod.mk, IntMod.val] using h3'
      exact mul_inv_eq_one.mp h3''
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    calc z * m = (m * z * m⁻¹) * m := by rw [hconj]
      _ = m * z := by group
  have hz2 : ∃ n : ℕ, z ^ (2 ^ n) = 1 := by
    refine ⟨1, ?_⟩
    have hzsq : z ^ 2 = 1 := h.pairFacts.elemAbelian.2 z hzV
    simpa using hzsq
  have hcz : Subgroup.centralizer ({z} : Set G) ≤ D.M :=
    centralizer_le_of_noncyclic D h61 hp hXM hXp hXnc hz1 hz2 hXz
  exact (s16c167_centralizer_cClos_le D (s15_13A_le_T h) ⟨hzV, hzC⟩ (D.k + 0)).trans hcz


theorem centralizer_cClos_le_of_sl2_natural
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    {p : ℕ} (hp37 : p = 3 ∨ p = 7) (hp : p ∈ D.sig)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    (hpK : Nat.card K = p + 1)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    centralizer (E3.cClos V (D.k + 0) D.T : Set G) ≤ D.M := by
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hZcard : Nat.card (fixV H) = p + 1 := by
    rw [(card_fixV_and_card_of_sl2_extension (A := Mbar D.M ⊥ V hV) hW hK hcomm hreal
      hcentral hfix).1, hpK]
  exact centralizer_cClos_le_of_small_fixed_kernel D hx h61 hV h hp37 hp
    hHn hZcard hfix

theorem centralizer_cClos_le_of_sp4_natural
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    {p : ℕ} (hp37 : p = 3 ∨ p = 7) (hp : p ∈ D.sig)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    (hpK : Nat.card K = p + 1)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    centralizer (E3.cClos V (D.k + 0) D.T : Set G) ≤ D.M := by
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hZcard : Nat.card (fixV H) = p + 1 := by
    rw [(card_fixV_and_card_of_sp4_extension (A := Mbar D.M ⊥ V hV) hW hK hcomm hreal
      hcentral hfix).1, hpK]
  exact centralizer_cClos_le_of_small_fixed_kernel D hx h61 hV h hp37 hp
    hHn hZcard hfix

theorem centralizer_cClos_le_of_field_four_natural
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    (hp : 3 ∈ D.sig) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    centralizer (E3.cClos V (D.k + 0) D.T : Set G) ≤ D.M := by
  have hK48 : Nat.card K = 4 ∨ Nat.card K = 8 := Or.inl hK
  have hpK : Nat.card K = 3 + 1 := by rw [hK]
  rcases hreal with hreal | hreal
  · exact centralizer_cClos_le_of_sl2_natural D hx h61 hV h (Or.inl rfl) hp hK48 hpK
      hHn hcomm hreal hcentral hfix
  · exact centralizer_cClos_le_of_sp4_natural D hx h61 hV h (Or.inl rfl) hp hK48 hpK
      hHn hcomm hreal hcentral hfix

theorem centralizer_cClos_le_of_field_eight_natural
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    (hp : 7 ∈ D.sig) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    centralizer (E3.cClos V (D.k + 0) D.T : Set G) ≤ D.M := by
  have hK48 : Nat.card K = 4 ∨ Nat.card K = 8 := Or.inr hK
  have hpK : Nat.card K = 7 + 1 := by rw [hK]
  rcases hreal with hreal | hreal
  · exact centralizer_cClos_le_of_sl2_natural D hx h61 hV h (Or.inr rfl) hp hK48 hpK
      hHn hcomm hreal hcentral hfix
  · exact centralizer_cClos_le_of_sp4_natural D hx h61 hV h (Or.inr rfl) hp hK48 hpK
      hHn hcomm hreal hcentral hfix




theorem inf_centSub_fixV_eq_of_sl2_natural
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHA : H ≤ Mbar D.M ⊥ V hV)
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    Mbar D.M ⊥ V hV ⊓ centSub (fixV H) = H := by
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.inf_centSub_fixV_eq_of_sl2_nat
    hW hHA (Subgroup.le_normalizer_iff.mpr hHn) hK hcomm hreal hcentral hfix

theorem inf_centSub_fixV_eq_of_sp4_natural
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHA : H ≤ Mbar D.M ⊥ V hV)
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    Mbar D.M ⊥ V hV ⊓ centSub (fixV H) = H := by
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.inf_centSub_fixV_eq_of_sp4_nat
    hW hHA (Subgroup.le_normalizer_iff.mpr hHn) hK hcomm hreal hcentral hfix

theorem inf_centSub_fixV_eq_of_field_four_natural
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHA : H ≤ Mbar D.M ⊥ V hV)
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    Mbar D.M ⊥ V hV ⊓ centSub (fixV H) = H := by
  have hK48 : Nat.card K = 4 ∨ Nat.card K = 8 := Or.inl hK
  rcases hreal with hreal | hreal
  · exact inf_centSub_fixV_eq_of_sl2_natural D hV hK48 hHA hHn hcomm hreal hcentral hfix
  · exact inf_centSub_fixV_eq_of_sp4_natural D hV hK48 hHA hHn hcomm hreal hcentral hfix

theorem inf_centSub_fixV_eq_of_field_eight_natural
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHA : H ≤ Mbar D.M ⊥ V hV)
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    Mbar D.M ⊥ V hV ⊓ centSub (fixV H) = H := by
  have hK48 : Nat.card K = 4 ∨ Nat.card K = 8 := Or.inr hK
  rcases hreal with hreal | hreal
  · exact inf_centSub_fixV_eq_of_sl2_natural D hV hK48 hHA hHn hcomm hreal hcentral hfix
  · exact inf_centSub_fixV_eq_of_sp4_natural D hV hK48 hHA hHn hcomm hreal hcentral hfix



theorem commutator_wClos_preTil_fixV_eq_bot
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hsParam : E3.aParam (autI (hV.mono
      (preTil_le ⊥ V hV (fixV H))) D.M) < E3.sParam hV) :
    ⁅E3.wClos V 0 D.T, preTil ⊥ V hV (fixV H)⁆ = ⊥ := by
  let Z : Subgroup (Vtil ⊥ V hV) := fixV H
  let Zg : Subgroup G := preTil ⊥ V hV Z
  have hZgV : Zg ≤ V := preTil_le ⊥ V hV Z
  have hZgEl : IsElemAbelian 2 Zg := hV.mono hZgV
  have hMnorm : D.M ≤ Subgroup.normalizer (Zg : Set G) :=
    M_le_normalizer_preTil_fixV D hV h hHn
  have hSyl : IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D D.sylowM.le
  have hi : 0 < E3.sParam hV - E3.aParam (autI hZgEl D.M) := by
    omega
  exact (CFSG.LocalAnalysis.WeakClosure81.six_eleven_one_generic (V := V) hV
    (H := D.M) (S := D.T) (U := Zg) (Z := Zg) hSyl hMnorm hZgEl le_rfl
    (i := 0) hi).1



theorem aParam_preTil_lt_sParam_of_card_four
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hZcard : Nat.card (fixV H) = 4) (hs : 1 < E3.sParam hV) :
    E3.aParam (autI (hV.mono (preTil_le ⊥ V hV (fixV H))) D.M) < E3.sParam hV := by
  let Z : Subgroup (Vtil ⊥ V hV) := fixV H
  let Zg : Subgroup G := preTil ⊥ V hV Z
  have hZgEl : IsElemAbelian 2 Zg := hV.mono (preTil_le ⊥ V hV Z)
  have hZg4 : Nat.card Zg = 4 := by
    rw [show Zg = preTil ⊥ V hV Z from rfl, s16c4_card_preTil hV bot_le Z,
      Subgroup.card_bot, one_mul]
    exact hZcard
  have hle : E3.aParam (autI hZgEl D.M) ≤ 1 :=
    aParam_autI_le_one_of_card_four hZgEl hZg4
  omega

theorem aParam_preTil_lt_sParam_of_card_eight
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hZcard : Nat.card (fixV H) = 8) (hs : 2 < E3.sParam hV) :
    E3.aParam (autI (hV.mono (preTil_le ⊥ V hV (fixV H))) D.M) < E3.sParam hV := by
  let Z : Subgroup (Vtil ⊥ V hV) := fixV H
  let Zg : Subgroup G := preTil ⊥ V hV Z
  have hZgEl : IsElemAbelian 2 Zg := hV.mono (preTil_le ⊥ V hV Z)
  have hZg8 : Nat.card Zg = 8 := by
    rw [show Zg = preTil ⊥ V hV Z from rfl, s16c4_card_preTil hV bot_le Z,
      Subgroup.card_bot, one_mul]
    exact hZcard
  have hle : E3.aParam (autI hZgEl D.M) ≤ 2 :=
    aParam_autI_le_two_of_card_eight hZgEl hZg8
  omega



theorem wClos_le_preBarSub_centSub_of_commutator
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hcomm : ⁅E3.wClos V 0 D.T, preTil ⊥ V hV (fixV H)⁆ = ⊥) :
    E3.wClos V 0 D.T ≤
      preBarSub D.M ⊥ V hV (centSub (fixV H)) := by
  classical
  let Z : Subgroup (Vtil ⊥ V hV) := fixV H
  let Zg : Subgroup G := preTil ⊥ V hV Z
  intro w hw
  have hwT : w ∈ D.T := E3.wClos_le 0 D.T hw
  have hwM : w ∈ D.M := D.sylowM.le hwT
  have hwstab : w ∈ stabTil ⊥ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀ hwM
  have hwc : w ∈ Subgroup.centralizer (Zg : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hw
  rw [mem_preBarSub]
  refine ⟨hwM, hwstab, ?_⟩
  rw [mem_centSub]
  intro z hz
  have hzimg : z ∈ imgTil ⊥ V hV Zg := by
    rw [show Zg = preTil ⊥ V hV Z from rfl, imgTil_preTil]
    exact hz
  obtain ⟨x, hxZg, hxz⟩ := (mem_imgTil ⊥ V hV Zg z).mp hzimg
  have hxV : x.val ∈ V := preTil_le ⊥ V hV Z hxZg
  have hcommw : w * x.val = x.val * w := by
    rw [Subgroup.mem_centralizer_iff] at hwc
    exact (hwc x.val hxZg).symm
  have hconj : w * x.val * w⁻¹ = x.val := by
    rw [hcommw, mul_assoc, mul_inv_cancel, mul_one]
  have hstab : actStab ⊥ V hV ⟨w, hwstab⟩ x = x := by
    apply IntMod.val_injective
    rw [actStab_apply_val]
    exact hconj
  rw [← hxz, actTil_mk, hstab]





theorem exists_noncyclic_pSubgroup_le_normalizer_of_pair
    {W : Type} [CommGroup W] [Finite W]
    {A H : Subgroup (MulAut W)} (hHA : H ≤ A)
    (U : Sylow 2 H) (UA : Subgroup A)
    (hUA : UA = (U : Subgroup H).map (Subgroup.inclusion hHA))
    {p : ℕ} (hp : p.Prime)
    (C : Subgroup (MulAut W))
    (hCeq : C = A ⊓ Subgroup.centralizer (H : Set (MulAut W)))
    (hCcard : Nat.card C = p)
    (hCmod : modFix C (⊤ : Subgroup W) = ⊥)
    (hfix : fixV H ≠ ⊥)
    (htorus : ∃ d : H,
      d ∈ Subgroup.normalizer ((U : Subgroup H) : Set H) ∧ orderOf d = p) :
    ∃ E : Subgroup A, IsPGroup p E ∧ ¬ IsCyclic E ∧
      E ≤ Subgroup.normalizer (UA : Set A) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc_order⟩ := exists_prime_orderOf_dvd_card' (G := C) p (by rw [hCcard])
  have hcC : (c : MulAut W) ∈ C := c.2
  have hcA : (c : MulAut W) ∈ A := by
    have h : (c : MulAut W) ∈ A ⊓ Subgroup.centralizer (H : Set (MulAut W)) := by
      rw [← hCeq]
      exact hcC
    exact h.1
  have hcHcent : (c : MulAut W) ∈ Subgroup.centralizer (H : Set (MulAut W)) := by
    have h : (c : MulAut W) ∈ A ⊓ Subgroup.centralizer (H : Set (MulAut W)) := by
      rw [← hCeq]
      exact hcC
    exact h.2
  let cA : A := ⟨(c : MulAut W), hcA⟩
  have hc_orderW : orderOf (c : MulAut W) = p := by
    rw [Subgroup.orderOf_coe]
    exact hc_order
  have hcAord : orderOf cA = p := by
    rw [← Subgroup.orderOf_coe cA]
    exact hc_orderW
  obtain ⟨dH, hdN, hdord⟩ := htorus
  let dA : A := ⟨(dH : MulAut W), hHA dH.2⟩
  have hdAord : orderOf dA = p := by
    rw [← Subgroup.orderOf_coe dA]
    show orderOf (dH : MulAut W) = p
    rw [Subgroup.orderOf_coe, hdord]
  have hdAN : dA ∈ Subgroup.normalizer (UA : Set A) := by
    have hdMap : dA ∈ (Subgroup.normalizer ((U : Subgroup H) : Set H)).map
        (Subgroup.inclusion hHA) :=
      Subgroup.mem_map.mpr ⟨dH, hdN, rfl⟩
    rw [hUA]
    exact Subgroup.le_normalizer_map (Subgroup.inclusion hHA) hdMap
  have hcAN : cA ∈ Subgroup.normalizer (UA : Set A) := by
    have hcAcent : cA ∈ Subgroup.centralizer (UA : Set A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [hUA] at hu
      obtain ⟨uH, huH, rfl⟩ := Subgroup.mem_map.mp hu
      apply Subtype.ext
      show (uH : MulAut W) * (c : MulAut W) = (c : MulAut W) * (uH : MulAut W)
      exact Subgroup.mem_centralizer_iff.mp hcHcent (uH : MulAut W) uH.2
    exact Subgroup.centralizer_le_normalizer (UA : Set A) hcAcent
  have hcomm : dA * cA = cA * dA := by
    apply Subtype.ext
    show (dH : MulAut W) * (c : MulAut W) = (c : MulAut W) * (dH : MulAut W)
    exact (Subgroup.mem_centralizer_iff.mp hcHcent (dH : MulAut W) dH.2)
  have hc_notin : cA ∉ Subgroup.zpowers dA := by
    intro hmem
    have hdHsub : dA ∈ H.subgroupOf A := dH.2
    have hcHsub : cA ∈ H.subgroupOf A :=
      (Subgroup.zpowers_le.mpr hdHsub) hmem
    have hcH : (c : MulAut W) ∈ H := Subgroup.mem_subgroupOf.mp hcHsub
    have hzH : Subgroup.zpowers (c : MulAut W) ≤ H := Subgroup.zpowers_le.mpr hcH
    have hzC : Subgroup.zpowers (c : MulAut W) ≤ C :=
      Subgroup.zpowers_le.mpr c.2
    have hcardz : Nat.card (Subgroup.zpowers (c : MulAut W)) = p := by
      rw [Nat.card_zpowers, hc_orderW]
    have heq : Subgroup.zpowers (c : MulAut W) = C :=
      Subgroup.eq_of_le_of_card_ge hzC (by rw [hCcard, hcardz])
    have hCH : C ≤ H := heq ▸ hzH
    have hfixC : fixV C = ⊥ := by
      rw [← hCmod]
      show fixV C = modFix C (⊤ : Subgroup W)
      rw [modFix, CFSG.Quasithin.fixed_eq_inf_fixV, top_inf_eq]
    have hfixH : fixV H = ⊥ := by
      have hle : fixV H ≤ fixV C := CFSG.Quasithin.fixV_anti hCH
      rw [hfixC] at hle
      exact le_bot_iff.mp hle
    exact hfix hfixH
  let E : Subgroup A := Subgroup.closure {dA, cA}
  have hpair := s16c13bcA_pair_group (Γ := A) hp hdAord hcAord hcomm hc_notin
  refine ⟨E, hpair.1, hpair.2, ?_⟩
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · exact hdAN
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hcAN



theorem normalizer_wClos_le_of_scalar_torus
    (D : Data G) (h61 : UC6.R6_1 D)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    {p : ℕ} (hp : p.Prime) (hp_sig : p ∈ D.sig)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHA : H ≤ Mbar D.M ⊥ V hV)
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hCfix : Mbar D.M ⊥ V hV ⊓ centSub (fixV H) = H)
    (hfix : fixV H ≠ ⊥)
    (hCcard : Nat.card ↥(Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV)))) = p)
    (hCmod : modFix (Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))))
        (⊤ : Subgroup (Vtil ⊥ V hV)) = ⊥)
    (htorus : ∀ U : Sylow 2 H, ∃ d : H,
      d ∈ Subgroup.normalizer ((U : Subgroup H) : Set H) ∧ orderOf d = p)
    (hsParam : E3.aParam (autI (hV.mono
      (preTil_le ⊥ V hV (fixV H))) D.M) < E3.sParam hV) :
    Subgroup.normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let W := Vtil ⊥ V hV
  let A : Subgroup (MulAut W) := Mbar D.M ⊥ V hV
  let Z : Subgroup W := fixV H
  let W0 : Subgroup G := E3.wClos V 0 D.T
  have hW0T : W0 ≤ D.T := E3.wClos_le 0 D.T
  have hW0M : W0 ≤ D.M := hW0T.trans D.sylowM.le
  have hW0p : IsPGroup 2 W0 := D.sylowM.isPGroup.to_le hW0T
  have hMe : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  let φ : ↥D.M →* MulAut W := barHom ⊥ V hV hMe
  have hφrange : φ.range = A := range_barHom ⊥ V hV hMe
  let α : ↥D.M →* A := φ.codRestrict A fun x => by
    rw [← hφrange]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hαsurj : Function.Surjective α := by
    intro a
    have ha : (a : MulAut W) ∈ φ.range := by
      rw [hφrange]
      exact a.2
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp ha
    exact ⟨m, Subtype.ext hm⟩
  have hW0Z : W0 ≤ preBarSub D.M ⊥ V hV (centSub Z) :=
    wClos_le_preBarSub_centSub_of_commutator D hV h
      (commutator_wClos_preTil_fixV_eq_bot D hV h hHn hsParam)
  let P : Subgroup ↥D.M := W0.subgroupOf D.M
  have hPp : IsPGroup 2 P := hW0p.comap_subtype
  have hPmap_le_H : P.map φ ≤ H := by
    rintro _ ⟨w, hw, rfl⟩
    have hwW0 : (w : G) ∈ W0 := hw
    have hwM : (w : G) ∈ D.M := hW0M hwW0
    have hwφA : φ w ∈ A := by
      rw [← hφrange]
      exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
    have hwφZ : φ w ∈ centSub Z := by
      obtain ⟨-, ⟨hstab, hcent⟩⟩ :=
        (mem_preBarSub D.M ⊥ V hV (centSub Z)).1 (hW0Z hwW0)
      have hsub : (⟨(w : G), hstab⟩ : stabTil ⊥ V) = Subgroup.inclusion hMe w :=
        Subtype.ext rfl
      rw [hsub] at hcent
      simpa [φ, barHom] using hcent
    rw [← hCfix]
    exact ⟨hwφA, hwφZ⟩
  let J : Subgroup H := (P.map φ).subgroupOf H
  have hJp : IsPGroup 2 J := (hPp.map φ).comap_subtype
  obtain ⟨U, hJU⟩ := hJp.exists_le_sylow
  let ιH : H →* A := Subgroup.inclusion hHA
  let UA : Subgroup A := (U : Subgroup H).map ιH
  have hUAp : IsPGroup 2 UA := U.isPGroup'.map ιH
  have hPα_le_UA : P.map α ≤ UA := by
    rintro _ ⟨w, hw, rfl⟩
    have hwφJ : φ w ∈ (P.map φ) := Subgroup.mem_map_of_mem φ hw
    have hwH : (⟨φ w, hPmap_le_H hwφJ⟩ : H) ∈ (U : Subgroup H) :=
      hJU (Subgroup.mem_subgroupOf.mpr hwφJ)
    refine ⟨⟨φ w, hPmap_le_H hwφJ⟩, hwH, ?_⟩
    exact Subtype.ext rfl
  let K : Subgroup ↥D.M := UA.comap α
  have hPK : P ≤ K := Subgroup.map_le_iff_le_comap.mp hPα_le_UA
  have hPKp : IsPGroup 2 (P.subgroupOf K) := hPp.comap_subtype
  obtain ⟨R, hPR⟩ := hPKp.exists_le_sylow
  let S : Subgroup ↥D.M := CFSG.FiveTransitive.SylowPreimageNormalizer.ambient α UA R
  let Y : Subgroup G := S.map D.M.subtype
  have hSp : IsPGroup 2 S :=
    show IsPGroup 2 ((R : Subgroup K).map K.subtype) from
      (Sylow.isPGroup' R).map K.subtype
  have hYp : IsPGroup 2 Y := hSp.map D.M.subtype
  have hYM : Y ≤ D.M := Subgroup.map_subtype_le S
  have hP_le_S : P ≤ S := by
    have h1 : (P.subgroupOf K).map K.subtype ≤ S := Subgroup.map_mono hPR
    rwa [Subgroup.map_subgroupOf_eq_of_le hPK] at h1
  have hW0_le_Y : W0 ≤ Y := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hW0M]
    exact Subgroup.map_mono hP_le_S
  have hNmap : (Subgroup.normalizer (S : Set ↥D.M)).map α =
      Subgroup.normalizer (UA : Set A) :=
    CFSG.FiveTransitive.SylowPreimageNormalizer.normalizer_map α hαsurj UA hUAp R
  obtain ⟨E, hEp, hEc, hEN⟩ :=
    exists_noncyclic_pSubgroup_le_normalizer_of_pair hHA U UA rfl hp
      (A ⊓ Subgroup.centralizer (H : Set (MulAut W))) rfl hCcard hCmod hfix
      (htorus U)
  let N : Subgroup ↥D.M := Subgroup.normalizer (S : Set ↥D.M)
  let ψ : N →* A := α.comp N.subtype
  have hψrange : ψ.range = Subgroup.normalizer (UA : Set A) := by
    have h1 : ψ.range = N.map α := by
      change (α.comp N.subtype).range = N.map α
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, hNmap]
  have hEsub : E ≤ ψ.range := by
    rw [hψrange]
    exact hEN
  obtain ⟨B, hBp, hBc, hBmap⟩ :=
    exists_noncyclic_pGroup_map_le ψ hp hEsub hEp hEc
  let X : Subgroup G := (B.map N.subtype).map D.M.subtype
  have hXp : IsPGroup p X :=
    IsPGroup.map (IsPGroup.map hBp N.subtype) D.M.subtype
  have hXc : ¬ IsCyclic X := by
    intro hc
    have hc0 : IsCyclic (B.map N.subtype) :=
      (Subgroup.equivMapOfInjective (B.map N.subtype) D.M.subtype
        D.M.subtype_injective).isCyclic.mpr hc
    exact hBc ((Subgroup.equivMapOfInjective B N.subtype
      N.subtype_injective).isCyclic.mpr hc0)
  have hXM : X ≤ D.M := Subgroup.map_subtype_le _
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hy
    have hbN : (b : ↥D.M) ∈ Subgroup.normalizer (S : Set ↥D.M) := b.2
    have hmap : ((b : ↥D.M) : G) ∈
        (Subgroup.normalizer (S : Set ↥D.M)).map D.M.subtype :=
      Subgroup.mem_map.mpr ⟨(b : ↥D.M), hbN, rfl⟩
    simpa [Y] using (Subgroup.le_normalizer_map (f := D.M.subtype) hmap)
  have h315 : Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer (W0 : Set G) :=
    E3.e3_15_normalizer (V := V) (H := D.M) (S := D.T) (Y := Y)
      (TwelveShort.isSylowIn_of_le D D.sylowM.le) hYM hYp hW0_le_Y
  have hXW0 : X ≤ Subgroup.normalizer (W0 : Set G) := hXY.trans h315
  have hW0ne : W0 ≠ ⊥ := by
    have hV2 : IsPGroup 2 V := h.pairFacts.elemAbelian.isPGroup
    have hcard : Nat.card V = 2 ^ rk ↥V := card_eq_two_pow_of_isPGroup hV2
    have hpos : 0 < rk ↥V := by
      by_contra h0
      have hzero : rk ↥V = 0 := Nat.eq_zero_of_not_pos h0
      have h1 : Nat.card V = 1 := by rw [hcard, hzero]; simp
      exact h.pairFacts.ne_bot (Subgroup.card_eq_one.mp h1)
    exact E3.wClos_ne_bot hV (s15_13A_le_T h) (i := 0) hpos
  exact normalizer_le_of_noncyclic D h61 hp_sig hXM hXp hXc hW0ne hW0p hXW0




theorem card_centralizer_eq_of_sl2_natural
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥) :
    Nat.card ↥(Mbar D.M ⊥ V hV ⊓
        Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV)))) = Nat.card K - 1 ∧
      modFix (Mbar D.M ⊥ V hV ⊓
        Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))))
        (⊤ : Subgroup (Vtil ⊥ V hV)) = ⊥ := by
  classical
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  let p : ℕ := Nat.card K - 1
  have hpK : Nat.card K = p + 1 := by
    rcases hK with h4 | h8
    · simp [p, h4]
    · simp [p, h8]
  have hp : p.Prime := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  have hpodd : Odd p := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  have hres := card_centralizer_eq_and_modFix_eq_bot_of_extension
    (W := Vtil ⊥ V hV) (A := Mbar D.M ⊥ V hV) (H := H)
    (K := K) (M := Fin 2 → K) (D := FFModel.nat (StatedSL 2 K))
    (LM := KGNat.linModelNat (StatedSL 2 K))
    hW hreal hcomm hp hpK hpodd hcentral
    (fun T hT => KGNat.commutant_statedSL (n := 2) (by norm_num) T hT)
  simpa [p] using hres

theorem card_centralizer_eq_of_sp4_natural
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥) :
    Nat.card ↥(Mbar D.M ⊥ V hV ⊓
        Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV)))) = Nat.card K - 1 ∧
      modFix (Mbar D.M ⊥ V hV ⊓
        Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))))
        (⊤ : Subgroup (Vtil ⊥ V hV)) = ⊥ := by
  classical
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  let p : ℕ := Nat.card K - 1
  have hpK : Nat.card K = p + 1 := by
    rcases hK with h4 | h8
    · simp [p, h4]
    · simp [p, h8]
  have hp : p.Prime := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  have hpodd : Odd p := by
    rcases hK with h4 | h8
    · norm_num [p, h4]
    · norm_num [p, h8]
  have hres := card_centralizer_eq_and_modFix_eq_bot_of_extension
    (W := Vtil ⊥ V hV) (A := Mbar D.M ⊥ V hV) (H := H)
    (K := K) (M := Fin 2 ⊕ Fin 2 → K) (D := FFModel.nat (StatedSp 2 K))
    (LM := KGNat.linModelNat (StatedSp 2 K))
    hW hreal hcomm hp hpK hpodd hcentral
    (fun T hT => KGNat.commutant_statedSp T hT)
  simpa [p] using hres

theorem torus_exists_of_sl2_natural
    {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H)) :
    ∀ U : Sylow 2 H, ∃ d : H,
      d ∈ Subgroup.normalizer ((U : Subgroup H) : Set H) ∧
        orderOf d = Nat.card K - 1 := by
  classical
  obtain ⟨π, hπ⟩ := hreal
  have hπinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful (StatedSL 2 K)) hπ
  let e : StatedSL 2 K ≃* H := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  intro U
  let Ustd : Sylow 2 (StatedSL 2 K) :=
    U.comapOfInjective e.toMonoidHom e.injective (by simp)
  have hUmap : (Ustd : Subgroup (StatedSL 2 K)).map e.toMonoidHom =
      (U : Subgroup H) := by
    have hUstd : (Ustd : Subgroup (StatedSL 2 K)) = (U : Subgroup H).comap e.toMonoidHom :=
      Sylow.coe_comapOfInjective U e.toMonoidHom e.injective (by simp)
    rw [hUstd]
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective U
  obtain ⟨dstd, hdstdN, hdstdord⟩ :=
    CFSG.ClassicalGroups.exists_orderOf_eq_card_sub_one_mem_normalizer_sylow_sl2 Ustd
  refine ⟨e dstd, ?_, ?_⟩
  · have hdmap : e dstd ∈
        (Subgroup.normalizer (Ustd : Subgroup (StatedSL 2 K))).map e.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨dstd, hdstdN, rfl⟩
    rw [Subgroup.map_equiv_normalizer_eq (Ustd : Subgroup (StatedSL 2 K)) e, hUmap] at hdmap
    exact hdmap
  · rw [MulEquiv.orderOf_eq e dstd]
    exact hdstdord

theorem torus_exists_of_sp4_natural
    {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H)) :
    ∀ U : Sylow 2 H, ∃ d : H,
      d ∈ Subgroup.normalizer ((U : Subgroup H) : Set H) ∧
        orderOf d = Nat.card K - 1 := by
  classical
  obtain ⟨π, hπ⟩ := hreal
  have hπinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful (StatedSp 2 K)) hπ
  let e : StatedSp 2 K ≃* H := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  intro U
  let Ustd : Sylow 2 (StatedSp 2 K) :=
    U.comapOfInjective e.toMonoidHom e.injective (by simp)
  have hUmap : (Ustd : Subgroup (StatedSp 2 K)).map e.toMonoidHom =
      (U : Subgroup H) := by
    have hUstd : (Ustd : Subgroup (StatedSp 2 K)) = (U : Subgroup H).comap e.toMonoidHom :=
      Sylow.coe_comapOfInjective U e.toMonoidHom e.injective (by simp)
    rw [hUstd]
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective U
  obtain ⟨dstd, hdstdN, hdstdord⟩ :=
    CFSG.ClassicalGroups.exists_orderOf_eq_card_sub_one_mem_normalizer_sylow_sp4 Ustd
  refine ⟨e dstd, ?_, ?_⟩
  · have hdmap : e dstd ∈
        (Subgroup.normalizer (Ustd : Subgroup (StatedSp 2 K))).map e.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨dstd, hdstdN, rfl⟩
    rw [Subgroup.map_equiv_normalizer_eq (Ustd : Subgroup (StatedSp 2 K)) e, hUmap] at hdmap
    exact hdmap
  · rw [MulEquiv.orderOf_eq e dstd]
    exact hdstdord



theorem normalizer_wClos_le_of_field_four_natural
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    (hp : 3 ∈ D.sig) (hm : MBarGT D.M ⊥ V 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHA : H ≤ Mbar D.M ⊥ V hV)
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    Subgroup.normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2)
      (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hK48 : Nat.card K = 4 ∨ Nat.card K = 8 := Or.inl hK
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hZcard : Nat.card (fixV H) = 4 := by
    rcases hreal with hreal | hreal
    · rw [(card_fixV_and_card_of_sl2_extension (A := Mbar D.M ⊥ V hV)
        hW hK48 hcomm hreal hcentral hfix).1, hK]
    · rw [(card_fixV_and_card_of_sp4_extension (A := Mbar D.M ⊥ V hV)
        hW hK48 hcomm hreal hcentral hfix).1, hK]
  have hmbar : 1 < mBar D.M ⊥ V h.isElemAbelian := (h.mBarGT_iff_lt_mBar 1).mp hm
  have hs : 1 < E3.sParam hV := by
    have hs' := s16c167_one_lt_sParam D hx h61 h hmbar
    simpa using hs'
  have hsParam := aParam_preTil_lt_sParam_of_card_four D hV hZcard hs
  have hCfix := inf_centSub_fixV_eq_of_field_four_natural D hV hK hHA hHn hcomm hreal
    hcentral hfix
  have hCdata : Nat.card ↥(Mbar D.M ⊥ V hV ⊓
        Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV)))) = 3 ∧
      modFix (Mbar D.M ⊥ V hV ⊓
        Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))))
        (⊤ : Subgroup (Vtil ⊥ V hV)) = ⊥ := by
    rcases hreal with hreal | hreal
    · obtain ⟨hc, hd⟩ := card_centralizer_eq_of_sl2_natural D hV hK48 hcomm hreal hcentral
      exact ⟨by rw [hc, hK], hd⟩
    · obtain ⟨hc, hd⟩ := card_centralizer_eq_of_sp4_natural D hV hK48 hcomm hreal hcentral
      exact ⟨by rw [hc, hK], hd⟩
  have htorP : ∀ U : Sylow 2 H, ∃ d : H,
      d ∈ Subgroup.normalizer ((U : Subgroup H) : Set H) ∧ orderOf d = 3 := by
    intro U
    rcases hreal with hreal | hreal
    · obtain ⟨d, hdN, hdord⟩ := torus_exists_of_sl2_natural (K := K) hreal U
      exact ⟨d, hdN, by rw [hdord, hK]⟩
    · obtain ⟨d, hdN, hdord⟩ := torus_exists_of_sp4_natural (K := K) hreal U
      exact ⟨d, hdN, by rw [hdord, hK]⟩
  exact normalizer_wClos_le_of_scalar_torus D h61 hV h (by norm_num) hp
    hHA hHn hCfix hfix hCdata.1 hCdata.2 htorP hsParam

theorem normalizer_wClos_le_of_field_eight_natural
    (D : Data G) (h61 : UC6.R6_1 D)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    (hp : 7 ∈ D.sig) (hm : MBarGT D.M ⊥ V 2) (h111 : W3Thm111 G)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHA : H ≤ Mbar D.M ⊥ V hV)
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) :
    Subgroup.normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 3)
      (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hK48 : Nat.card K = 4 ∨ Nat.card K = 8 := Or.inr hK
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hZcard : Nat.card (fixV H) = 8 := by
    rcases hreal with hreal | hreal
    · rw [(card_fixV_and_card_of_sl2_extension (A := Mbar D.M ⊥ V hV)
        hW hK48 hcomm hreal hcentral hfix).1, hK]
    · rw [(card_fixV_and_card_of_sp4_extension (A := Mbar D.M ⊥ V hV)
        hW hK48 hcomm hreal hcentral hfix).1, hK]
  have hV1 : InCalV1 D.M D.T V := s16c167_inCalV1_of_bot h
  have hs : 2 < E3.sParam hV := by
    have hs' := TwelveShort.lt_sParam_of_mBarGT D h111 hV1 hm (n := 2) hm
    simpa using hs'
  have hsParam := aParam_preTil_lt_sParam_of_card_eight D hV hZcard hs
  have hCfix := inf_centSub_fixV_eq_of_field_eight_natural D hV hK hHA hHn hcomm hreal
    hcentral hfix
  have hCdata : Nat.card ↥(Mbar D.M ⊥ V hV ⊓
        Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV)))) = 7 ∧
      modFix (Mbar D.M ⊥ V hV ⊓
        Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))))
        (⊤ : Subgroup (Vtil ⊥ V hV)) = ⊥ := by
    rcases hreal with hreal | hreal
    · obtain ⟨hc, hd⟩ := card_centralizer_eq_of_sl2_natural D hV hK48 hcomm hreal hcentral
      exact ⟨by rw [hc, hK], hd⟩
    · obtain ⟨hc, hd⟩ := card_centralizer_eq_of_sp4_natural D hV hK48 hcomm hreal hcentral
      exact ⟨by rw [hc, hK], hd⟩
  have htorP : ∀ U : Sylow 2 H, ∃ d : H,
      d ∈ Subgroup.normalizer ((U : Subgroup H) : Set H) ∧ orderOf d = 7 := by
    intro U
    rcases hreal with hreal | hreal
    · obtain ⟨d, hdN, hdord⟩ := torus_exists_of_sl2_natural (K := K) hreal U
      exact ⟨d, hdN, by rw [hdord, hK]⟩
    · obtain ⟨d, hdN, hdord⟩ := torus_exists_of_sp4_natural (K := K) hreal U
      exact ⟨d, hdN, by rw [hdord, hK]⟩
  exact normalizer_wClos_le_of_scalar_torus D h61 hV h (by norm_num) hp
    hHA hHn hCfix hfix hCdata.1 hCdata.2 htorP hsParam



theorem not_solvable_M_of_sl2_natural
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHA : H ≤ Mbar D.M ⊥ V hV)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H)) :
    ¬ Group.IsSolvable ↥D.M := by
  classical
  intro hsolM
  have : Group.IsSolvable ↥D.M := hsolM
  have hMe : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  let φ : ↥D.M →* MulAut (Vtil ⊥ V hV) := barHom ⊥ V hV hMe
  let α : ↥D.M →* Mbar D.M ⊥ V hV := φ.codRestrict (Mbar D.M ⊥ V hV) fun x => by
    rw [show Mbar D.M ⊥ V hV = φ.range from (range_barHom ⊥ V hV hMe).symm]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hαsurj : Function.Surjective α := by
    intro a
    have ha : (a : MulAut (Vtil ⊥ V hV)) ∈ φ.range := by
      rw [range_barHom ⊥ V hV hMe]
      exact a.2
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp ha
    exact ⟨m, Subtype.ext hm⟩
  have hsolA : Group.IsSolvable ↥(Mbar D.M ⊥ V hV) :=
    Group.isSolvable_of_surjective (f := α) hαsurj
  have hsolH : Group.IsSolvable ↥H :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hHA)
      (Subgroup.inclusion_injective hHA)
  obtain ⟨π, hπ⟩ := hreal
  have hπinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful (StatedSL 2 K)) hπ
  let e : StatedSL 2 K ≃* H := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  have : Group.IsSolvable ↥H := hsolH
  have hsolSL : Group.IsSolvable ↥(StatedSL 2 K) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hsolMat : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_surjective
      (f := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm.toMonoidHom)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm.surjective
  exact CFSG.Quasithin.Vol2.Ch11.SecD.EK2.not_isSolvable_SL2 (F := K) h4 hsolMat

theorem not_solvable_M_of_sp4_natural
    (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHA : H ≤ Mbar D.M ⊥ V hV)
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H)) :
    ¬ Group.IsSolvable ↥D.M := by
  classical
  intro hsolM
  have : Group.IsSolvable ↥D.M := hsolM
  have hMe : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  let φ : ↥D.M →* MulAut (Vtil ⊥ V hV) := barHom ⊥ V hV hMe
  let α : ↥D.M →* Mbar D.M ⊥ V hV := φ.codRestrict (Mbar D.M ⊥ V hV) fun x => by
    rw [show Mbar D.M ⊥ V hV = φ.range from (range_barHom ⊥ V hV hMe).symm]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hαsurj : Function.Surjective α := by
    intro a
    have ha : (a : MulAut (Vtil ⊥ V hV)) ∈ φ.range := by
      rw [range_barHom ⊥ V hV hMe]
      exact a.2
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp ha
    exact ⟨m, Subtype.ext hm⟩
  have hsolA : Group.IsSolvable ↥(Mbar D.M ⊥ V hV) :=
    Group.isSolvable_of_surjective (f := α) hαsurj
  have hsolH : Group.IsSolvable ↥H :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hHA)
      (Subgroup.inclusion_injective hHA)
  obtain ⟨π, hπ⟩ := hreal
  have hπinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful (StatedSp 2 K)) hπ
  let e : StatedSp 2 K ≃* H := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  have : Group.IsSolvable ↥H := hsolH
  let lam0 : Matrix.SpecialLinearGroup (Fin 2) K →* H :=
    e.toMonoidHom.comp
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lam (r := 2) (k := K) 0)
  have hlam0 : Function.Injective lam0 :=
    e.injective.comp (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lam_injective
      (r := 2) (k := K) 0)
  have hsolMat : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_isSolvable_injective (f := lam0) hlam0
  exact CFSG.Quasithin.Vol2.Ch11.SecD.EK2.not_isSolvable_SL2 (F := K) h4 hsolMat



theorem false_of_field_four_natural_extension
    (D : Data G) (hx : DataExt D)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    (hp : 3 ∈ D.sig) (hm : MBarGT D.M ⊥ V 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHA : H ≤ Mbar D.M ⊥ V hV)
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) : False := by
  classical
  have hNorm := normalizer_wClos_le_of_field_four_natural D hx h61 hV h hp hm hK
    hHA hHn hcomm hreal hcentral hfix
  have hCen := centralizer_cClos_le_of_field_four_natural D hx h61 hV h hp hK
    hHn hcomm hreal hcentral hfix
  have hns : ¬ Group.IsSolvable ↥D.M := by
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 :=
      charP_of_card_eq_prime_pow (p := 2) (f := 2)
        (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
    have h4 : 4 ≤ Nat.card K := by rw [hK]
    rcases hreal with hreal | hreal
    · exact not_solvable_M_of_sl2_natural D hV h h4 hHA hreal
    · exact not_solvable_M_of_sp4_natural D hV h h4 hHA hreal
  have hstr := CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hp
  have hk1 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Data.k_eq_one_of_isStronglyPEmbedded D hstr
  have hmk : MBarGT D.M ⊥ V (D.k + 0) := by
    rw [hk1]
    simpa using hm
  have hres := twelve_ten_two D hx h61 h126 h111 h rfl (i := 0) hmk
  rcases hres with hN | hC
  · exact hN hNorm
  · exact hC hCen

theorem false_of_field_eight_natural_extension
    (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D ⊥ V)
    (hp : 7 ∈ D.sig) (hm : MBarGT D.M ⊥ V 2)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {H : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hHA : H ≤ Mbar D.M ⊥ V hV)
    (hHn : ∀ a ∈ Mbar D.M ⊥ V hV, ∀ x ∈ H, a * x * a⁻¹ ∈ H)
    (hcomm : commSub ⊤ H = ⊤)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes H ⊤ (fixV H) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ (fixV H))
    (hcentral : Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (H : Set (MulAut (Vtil ⊥ V hV))) ≠ ⊥)
    (hfix : fixV H ≠ ⊥) : False := by
  classical
  have hNorm := normalizer_wClos_le_of_field_eight_natural D h61 hV h hp hm h111 hK
    hHA hHn hcomm hreal hcentral hfix
  have hCen := centralizer_cClos_le_of_field_eight_natural D hx h61 hV h hp hK
    hHn hcomm hreal hcentral hfix
  have hk2 : D.k ≤ 2 := TwelveSeven.k_le_two D
  have hmk : MBarGT D.M ⊥ V (D.k + 0) :=
    TwelveShort.mBarGT_mono hm (by omega)
  have hres := twelve_ten_two D hx h61 h126 h111 h rfl (i := 0) hmk
  rcases hres with hN | hC
  · exact hN hNorm
  · exact hC hCen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
