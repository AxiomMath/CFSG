module

public import CFSG.LocalAnalysis.StandardType.GGNsq2NbrFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosFinal
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryFiveCover
public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBlock
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseN
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoord
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordC
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotAut
import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeCent
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPerm
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlock
import CFSG.Blueprint.LieModelAPI
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.ClassicalInvolution.Phan.Blocks
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

theorem ggQTwoDUnitSix_quotFrame
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    p = 3 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 4 ∧
      ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (f : ↥(Subgroup.normalizer (L : Set G)) →* Q)
        (ψ : Su K 2 1 6 →* Q),
        NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L) ∧
        ψ.range = NsQuot.img (Subgroup.normalizer (L : Set G)) f L ∧
        GGNSLocalHyp 3 (NsQuot.img (Subgroup.normalizer (L : Set G)) f B)
          (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs) K 1 6 ψ ∧
        GGActsDiagonally (p := 2) (f := 1) ψ
          (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs) ∧
        GGTableBPosSU 3 (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
          (NsQuot.img (Subgroup.normalizer (L : Set G)) f L) K 1 6 ψ := by
  obtain ⟨K, hf, hfin, lab, m', θ, hK, -, hmrank, hSide, hdvd, hperf, -, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore hmark (fun p lab hl => hl.1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := lab.n) hK
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, hn1, hr5⟩ := hSide
  change n = 1 at hn1
  change rank = 5 at hr5
  change m' = rank + 1 at hmrank
  subst hn1
  subst hr5
  obtain rfl : m' = 6 := by omega
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by simpa using hdvd)
  subst hp3
  obtain ⟨Q, _, _, f, ψ, hD, hrange, h', hc⟩ := ggNsq2Member_frame hcfg
    (ggNSPosPD_routeCfg_cent_L hcfg.1.1) hK hdvd (Or.inr rfl) θ hperf hBsN hbs
  have hpos := ggNSDiag_position h' hc
  rw [hrange] at hpos
  exact ⟨rfl, K, hf, hfin, inferInstance, by rw [hK]; norm_num, Q, inferInstance, inferInstance,
    f, ψ, hD, hrange, h', hc, hpos⟩

end CFSG.StandardType.QTwo

namespace CFSG.StandardType.NsQuot

theorem commutator_inf_ker_eq_bot_of_psu5 {E P : Type} [Group E] [Finite E] [Group P] [Finite P]
    [Group.IsPerfect P] (ρ : E →* P) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 ↥ρ.ker)
    (hmod : CFSG.Blueprint.LieModel P .PSU 5 2 1) :
    Group.IsPerfect ↥(commutator E) ∧ commutator E ⊓ ρ.ker = ⊥ ∧
      Function.Surjective (ρ.comp (commutator E).subtype) := by
  have hsurj : Function.Surjective (ρ.comp (commutator E).subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    exact CFSG.ComponentClassification.CentralExtensions.derived_map_eq_top ρ hρ
  have hperf : Group.IsPerfect ↥(commutator E) :=
    CFSG.ComponentClassification.CentralExtensions.derived_perfect ρ hρ hker
  have hker' : (ρ.comp (commutator E).subtype).ker ≤ Subgroup.center ↥(commutator E) := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    have hc' : (c : E) ∈ ρ.ker := hc
    exact Subgroup.mem_center_iff.mp (hker hc') d
  have h2' : IsPGroup 2 ↥(ρ.comp (commutator E).subtype).ker := by
    intro c
    obtain ⟨k, hk⟩ := h2 ⟨((c : ↥(commutator E)) : E), c.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨hbot, -⟩ := CFSG.LocalAnalysis.ComponentInitial.even_unitary_five_prime_field_central_two_cover_trivial
    _ hsurj hker' h2' hmod
  refine ⟨hperf, ?_, hsurj⟩
  rw [eq_bot_iff]
  intro e he
  obtain ⟨heC, heK⟩ := Subgroup.mem_inf.mp he
  have hmem : (⟨e, heC⟩ : ↥(commutator E)) ∈ (ρ.comp (commutator E).subtype).ker := heK
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

theorem Datum.exists_lift_psu5 [Finite Q] (hD : Datum p N f L Bs Z) {P : Subgroup Q}
    (hPL : P ≤ img N f L) [Group.IsPerfect ↥P] (hmod : CFSG.Blueprint.LieModel ↥P .PSU 5 2 1) :
    ∃ J : Subgroup G, J ≤ L ∧ Group.IsPerfect ↥J ∧ img N f J = P ∧ ∀ j ∈ J, j ∈ Z → j = 1 := by
  classical
  let E : Subgroup G := L ⊓ (P.comap f).map N.subtype
  have hEL : E ≤ L := inf_le_left
  have hEN : E ≤ N := hEL.trans hD.LN
  have hEP : ∀ e : ↥E, f (Subgroup.inclusion hEN e) ∈ P := by
    intro e
    obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp e.2).2
    have : Subgroup.inclusion hEN e = n := Subtype.ext hne.symm
    rw [this]
    exact hn
  let ρ : ↥E →* ↥P := (f.comp (Subgroup.inclusion hEN)).codRestrict P hEP
  have hρ : ∀ e : ↥E, ((ρ e : ↥P) : Q) = f (Subgroup.inclusion hEN e) := fun _ => rfl
  have hρsurj : Function.Surjective ρ := by
    intro q
    obtain ⟨u, huL, hu⟩ := mem_img.1 (hPL q.2)
    have huE : (u : G) ∈ E := Subgroup.mem_inf.mpr
      ⟨huL, Subgroup.mem_map.mpr ⟨u, by rw [Subgroup.mem_comap, hu]; exact q.2, rfl⟩⟩
    refine ⟨⟨(u : G), huE⟩, Subtype.ext ?_⟩
    rw [hρ]
    exact hu
  have hρZ : ∀ e : ↥E, e ∈ ρ.ker ↔ (e : G) ∈ Z := by
    intro e
    have h := hD.mem_ker_iff (Subgroup.inclusion hEN e)
    rw [MonoidHom.mem_ker] at h ⊢
    constructor
    · intro he
      exact h.1 (by simpa [hρ] using congrArg Subtype.val he)
    · intro hz
      exact Subtype.ext (by rw [hρ]; exact h.2 hz)
  have hker : ρ.ker ≤ Subgroup.center ↥E := by
    intro e he
    rw [Subgroup.mem_center_iff]
    intro e'
    exact Subtype.ext (hD.Zcent _ ((hρZ e).1 he) _ (hEL e'.2))
  have h2 : IsPGroup 2 ↥ρ.ker := by
    intro e
    obtain ⟨k, hk⟩ := hD.Z2 _ ((hρZ e).1 e.2)
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  have hPmod : CFSG.Blueprint.LieModel ↥P .PSU 5 2 1 := hmod
  obtain ⟨hCperf, hCbot, hCsurj⟩ := commutator_inf_ker_eq_bot_of_psu5 ρ hρsurj hker h2 hPmod
  refine ⟨(commutator ↥E).map E.subtype, (Subgroup.map_subtype_le _).trans hEL, ?_, ?_, ?_⟩
  · exact Group.IsPerfect.ofSurjective (f := (Subgroup.equivMapOfInjective (commutator ↥E)
      E.subtype E.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  · ext q
    constructor
    · intro hq
      obtain ⟨u, huJ, rfl⟩ := mem_img.1 hq
      obtain ⟨c, hc, hcu⟩ := Subgroup.mem_map.mp huJ
      have : u = Subgroup.inclusion hEN c := Subtype.ext hcu.symm
      rw [this]
      exact hEP c
    · intro hq
      obtain ⟨c, hc⟩ := hCsurj ⟨q, hq⟩
      refine mem_img.2 ⟨Subgroup.inclusion hEN c, Subgroup.mem_map.mpr ⟨c, c.2, rfl⟩, ?_⟩
      have := congrArg Subtype.val hc
      simpa [hρ] using this
  · intro j hj hjZ
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hj
    have hcK : c ∈ ρ.ker := (hρZ c).2 hjZ
    have hc1 : c ∈ commutator ↥E ⊓ ρ.ker := Subgroup.mem_inf.mpr ⟨hc, hcK⟩
    rw [hCbot, Subgroup.mem_bot] at hc1
    rw [hc1]
    rfl

open scoped commutatorElement in
theorem Datum.le_of_img_le (hD : Datum p N f L Bs Z) {J J' : Subgroup G} (hJ : J ≤ L)
    (hJ' : J' ≤ L) [Group.IsPerfect ↥J'] (h : img N f J' ≤ img N f J) : J' ≤ J := by
  have hdec : ∀ a ∈ J', ∃ u ∈ J, ∃ z ∈ Z, a = u * z := by
    intro a ha
    have haN : a ∈ N := hD.LN (hJ' ha)
    obtain ⟨u, huJ, hu⟩ := mem_img.1 (h (mem_img.2 ⟨⟨a, haN⟩, ha, rfl⟩))
    refine ⟨u, huJ, (u : G)⁻¹ * a, ?_, by group⟩
    have hk : u⁻¹ * ⟨a, haN⟩ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hu, inv_mul_cancel]
    simpa using (hD.mem_ker_iff _).1 hk
  rw [← Subgroup.isPerfect_iff.mp ‹Group.IsPerfect ↥J'›, Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨u, hu, z, hz, rfl⟩ := hdec a ha
  obtain ⟨v, hv, w, hw, rfl⟩ := hdec b hb
  have hzv : z * v = v * z := (hD.Zcent z hz v (hJ hv)).symm
  have hzw : z * w = w * z := (hD.Zcent z hz w (hD.ZL hw)).symm
  have hwu : w * u⁻¹ = u⁻¹ * w := (hD.Zcent w hw u⁻¹ (L.inv_mem (hJ hu))).symm
  have hcomm : ⁅u * z, v * w⁆ = u * v * u⁻¹ * v⁻¹ := by
    rw [commutatorElement_def]
    calc u * z * (v * w) * (u * z)⁻¹ * (v * w)⁻¹
        = u * (z * v) * w * z⁻¹ * u⁻¹ * w⁻¹ * v⁻¹ := by group
      _ = u * v * (z * w) * z⁻¹ * u⁻¹ * w⁻¹ * v⁻¹ := by rw [hzv]; group
      _ = u * v * (w * u⁻¹) * w⁻¹ * v⁻¹ := by rw [hzw]; group
      _ = u * v * u⁻¹ * v⁻¹ := by rw [hwu]; group
  rw [hcomm]
  exact J.mul_mem (J.mul_mem (J.mul_mem hu hv) (J.inv_mem hu)) (J.inv_mem hv)

theorem Datum.eq_of_img_eq (hD : Datum p N f L Bs Z) {J J' : Subgroup G} (hJ : J ≤ L)
    (hJ' : J' ≤ L) [Group.IsPerfect ↥J] [Group.IsPerfect ↥J'] (h : img N f J = img N f J') :
    J = J' :=
  le_antisymm (hD.le_of_img_le hJ' hJ h.le) (hD.le_of_img_le hJ hJ' h.ge)

theorem Datum.conj_mem_of_img (hD : Datum p N f L Bs Z) {J : Subgroup G} (hJ : J ≤ L)
    [Group.IsPerfect ↥J] (n : ↥N) (hnL : ∀ l ∈ L, (n : G) * l * (n : G)⁻¹ ∈ L)
    (hn : ∀ q ∈ img N f J, f n * q * (f n)⁻¹ ∈ img N f J) :
    ∀ j ∈ J, (n : G) * j * (n : G)⁻¹ ∈ J := by
  let J' : Subgroup G := J.map (MulAut.conj (n : G)).toMonoidHom
  have hJ'L : J' ≤ L := by
    rintro _ ⟨j, hj, rfl⟩
    exact hnL j (hJ hj)
  have hJ'img : img N f J' ≤ img N f J := by
    intro q hq
    obtain ⟨u, ⟨j, hj, hju⟩, rfl⟩ := mem_img.1 hq
    have hjN : j ∈ N := hD.LN (hJ hj)
    have hu : u = n * ⟨j, hjN⟩ * n⁻¹ := Subtype.ext (by simpa using hju.symm)
    rw [hu, map_mul, map_mul, map_inv]
    exact hn _ (mem_img.2 ⟨⟨j, hjN⟩, hj, rfl⟩)
  have : Group.IsPerfect ↥J' := Group.IsPerfect.map _
  have hle := hD.le_of_img_le hJ hJ'L hJ'img
  intro j hj
  exact hle ⟨j, hj, rfl⟩

theorem Datum.commute_of_img (hD : Datum p N f L Bs Z) {J : Subgroup G} (hJ : J ≤ L)
    [Group.IsPerfect ↥J] (hJZ : ∀ j ∈ J, j ∈ Z → j = 1) (n : ↥N)
    (hnL : ∀ l ∈ L, (n : G) * l * (n : G)⁻¹ ∈ L)
    (hn : ∀ q ∈ img N f J, f n * q = q * f n) : ∀ j ∈ J, (n : G) * j = j * (n : G) := by
  have hnorm := hD.conj_mem_of_img hJ n hnL fun q hq => by
    rw [hn q hq, mul_inv_cancel_right]
    exact hq
  intro j hj
  have hjN : j ∈ N := hD.LN (hJ hj)
  have hmem : (n : G) * j * (n : G)⁻¹ * j⁻¹ ∈ J := J.mul_mem (hnorm j hj) (J.inv_mem hj)
  have hker : n * ⟨j, hjN⟩ * n⁻¹ * ⟨j, hjN⟩⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      hn _ (mem_img.2 ⟨⟨j, hjN⟩, hj, rfl⟩), mul_inv_cancel_right, mul_inv_cancel]
  have hZ : (n : G) * j * (n : G)⁻¹ * j⁻¹ ∈ Z := by simpa using (hD.mem_ker_iff _).1 hker
  have h1 := hJZ _ hmem hZ
  calc (n : G) * j = (n : G) * j * (n : G)⁻¹ * j⁻¹ * (j * (n : G)) := by group
    _ = j * (n : G) := by rw [h1, one_mul]

end CFSG.StandardType.NsQuot

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

theorem ggQTwoDUnitSix_blockModel {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) {Q : Type} [Group Q] (ψ : Su K 2 1 6 →* Q)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) (c : Fin 6) :
    Group.IsPerfect ↥((coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ) ∧
      CFSG.Blueprint.LieModel ↥((coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ) .PSU 5 2 1 := by
  classical
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  set S := coordBlockSU K 2 1 (Finset.univ.erase c) with hSdef
  let θ : Su K 2 1 5 →* Su K 2 1 6 :=
    (MulAut.conj (ggPhanNSAPairAux_permElt (f := 1) (Equiv.swap (5 : Fin 6) c))).toMonoidHom.comp
      (blockEmb K 2 1 6 5 0 (by norm_num))
  have hθinj : Function.Injective θ := by
    intro u v huv
    refine blockEmb_injective (K := K) (p := 2) (f := 1) (by norm_num : 0 + 5 ≤ 6) ?_
    have := congrArg (fun w : Su K 2 1 6 =>
      (ggPhanNSAPairAux_permElt (f := 1) (Equiv.swap (5 : Fin 6) c))⁻¹ * w *
        ggPhanNSAPairAux_permElt (f := 1) (Equiv.swap (5 : Fin 6) c)) huv
    simpa [θ, MonoidHom.comp_apply, MulAut.conj_apply, mul_assoc] using this
  have hmap : ∀ c : Fin 6, (Finset.univ.filter fun i : Fin 6 => (i : ℕ) < 5).map
      (Equiv.swap (5 : Fin 6) c).toEmbedding = Finset.univ.erase c := by decide
  have hθrange : θ.range = S := by
    change ((MulAut.conj (ggPhanNSAPairAux_permElt (f := 1)
      (Equiv.swap (5 : Fin 6) c))).toMonoidHom.comp (blockEmb K 2 1 6 5 0 (by norm_num))).range = S
    rw [MonoidHom.range_comp, ggQTwoDUnit_range_blockEmb_zero (k := 5) (by norm_num),
      ggQTwoDUnit_coordBlockSU_conj, hmap]
  have hS : Function.Injective (ψ.comp S.subtype) :=
    ggQTwoDUnit_injective_coordBlockSU hK ψ hψk (by norm_num) (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
      norm_num)
  have hinj : Function.Injective (ψ.comp θ) := by
    intro u v huv
    apply hθinj
    have hu : θ u ∈ S := hθrange ▸ ⟨u, rfl⟩
    have hv : θ v ∈ S := hθrange ▸ ⟨v, rfl⟩
    exact congrArg Subtype.val (hS (a₁ := ⟨θ u, hu⟩) (a₂ := ⟨θ v, hv⟩) huv)
  have hrange : (ψ.comp θ).range = S.map ψ := by rw [MonoidHom.range_comp, hθrange]
  let e₀ : Su K 2 1 5 ≃* ↥(S.map ψ) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (K := K) (p := 2)
    (f := 1) hK'
  refine ⟨?_, ?_⟩
  · have : Group.IsPerfect (Su K 2 1 5) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_SUid hσ (by norm_num) fun h => absurd h (by norm_num)
    exact Group.IsPerfect.ofSurjective (f := e₀.toMonoidHom) e₀.surjective
  · let e₁ : Su K 2 1 5 ≃* ↥(CFSG.Open.StatedSU 5 (2 ^ 1) K) :=
      MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK' 5)
    have hbot : (CFSG.Open.StatedScalars (Fin 5) K).subgroupOf (CFSG.Open.StatedSU 5 (2 ^ 1) K) =
        ⊥ := Subgroup.eq_bot_of_card_eq _ (by
      rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK' (n := 5) (by norm_num)).2.2]
      norm_num)
    let e₂ : ↥(CFSG.Open.StatedSU 5 (2 ^ 1) K) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 5 (2 ^ 1) K) :=
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm
    have hadm : CFSG.Open.StatedLieAdmissible .PSU 5 2 1 :=
      ⟨Nat.prime_two, le_refl 1, by norm_num, fun hc => absurd (Prod.mk.inj hc).1 (by norm_num)⟩
    exact (CFSG.Blueprint.LieModel.classical_iff (by decide)).mpr
      ⟨hadm, K, inferInstance, inferInstance, hK', ⟨(e₀.symm.trans e₁).trans e₂⟩⟩

theorem ggQTwoDUnitSix_block {G : Type} [Group G] [Finite G] {L Bs : Subgroup G} {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) {Q : Type} [Group Q] [Finite Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψ : ψ.range = NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) (c : Fin 6) :
    ∃ J : Subgroup G, J ≤ L ∧ Group.IsPerfect ↥J ∧
      NsQuot.img (Subgroup.normalizer (L : Set G)) f J =
        (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ ∧
      ∀ j ∈ J, j ∈ twoCentral L → j = 1 := by
  obtain ⟨hperf, hmod⟩ := ggQTwoDUnitSix_blockModel hK ψ hψk c
  have hle : (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ ≤
      NsQuot.img (Subgroup.normalizer (L : Set G)) f L := by
    rw [← hψ]
    exact Subgroup.map_le_range ψ _
  have := hperf
  exact hD.exists_lift_psu5 hle hmod

theorem ggQTwoDUnitSix_quotBase
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (e' : Fin 6 ≃ ι) (hM : M = (ggCoxeterMatrixD 6).reindex e')
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    p = 3 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (Q : Type) (_ : Group Q)
      (_ : Finite Q) (f : ↥(Subgroup.normalizer (L : Set G)) →* Q) (ψ : Su K 2 1 6 →* Q)
      (ε : Equiv.Perm (Fin 6) ≃*
        ↥(ggAutomizer (NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
          (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)))
      (hx : x ∈ Subgroup.normalizer (L : Set G)),
      NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L) ∧
      QTwoUnitBase 3 (NsQuot.img (Subgroup.normalizer (L : Set G)) f B)
        (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs) (f ⟨x, hx⟩)
        (NsQuot.img (Subgroup.normalizer (L : Set G)) f L) ψ ε := by
  classical
  obtain ⟨hp3, K, hKf, hKfin, hKchar, hK, Q, hQ, hQfin, f, ψ, hD, hrange, hhyp, hdiag, -⟩ :=
    ggQTwoDUnitSix_quotFrame hcfg.1 hmark
  subst hp3
  obtain ⟨hxBs, hxord, hcent⟩ := ggQTwoDUnit_base_cent hcfg rfl
  have hx : x ∈ Subgroup.normalizer (L : Set G) := hD.BsN hxBs
  have hcardBs : Nat.card ↥Bs = 3 ^ 6 := by
    obtain ⟨β, -⟩ := ggQTwoD_selectedModule hTBF hWI hcfg e' (by norm_num) hM
    calc Nat.card ↥Bs = Nat.card (DVec 6) := Nat.card_congr (Additive.ofMul.trans β.toEquiv)
      _ = 3 ^ 6 := by
        rw [Nat.card_pi]
        simp
  have hcard : Nat.card ↥(NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs) = 3 ^ 6 := by
    rw [hD.card_img le_rfl, hcardBs]
  have hfx3 : (f ⟨x, hx⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa [hxord] using pow_orderOf_eq_one x)
    rw [this, map_one]
  have hfx1 : f ⟨x, hx⟩ ≠ 1 := by
    intro h1
    have hinj := hD.injOn (U := Bs) le_rfl
    have hxU : (⟨x, hx⟩ : ↥(Subgroup.normalizer (L : Set G))) ∈ Bs.subgroupOf _ :=
      Subgroup.mem_subgroupOf.mpr hxBs
    have h := @hinj ⟨⟨x, hx⟩, hxU⟩ 1 (by simpa using h1)
    have hx1 : x = 1 := by
      simpa using congrArg
        (fun u : ↥(Bs.subgroupOf _) => ((u : ↥(Subgroup.normalizer (L : Set G))) : G)) h
    rw [hx1, orderOf_one] at hxord
    exact absurd hxord (by norm_num)
  have hxord' : orderOf (f ⟨x, hx⟩) = 3 := orderOf_eq_prime hfx3 hfx1
  have hxmem : f ⟨x, hx⟩ ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs :=
    NsQuot.mem_img.2 ⟨⟨x, hx⟩, hxBs, rfl⟩
  have hLperf : Group.IsPerfect ↥L := by
    have hS : LargeEvenSStar 3 B x L := hcfg.1.1.1.1.2.2.2.2.2.2.1
    exact Group.isPerfect_def.2 hS.2.2.2.1.2.2.1
  have hcentQ : NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs ⊓
      Subgroup.centralizer (NsQuot.img (Subgroup.normalizer (L : Set G)) f L : Set Q) =
      Subgroup.zpowers (f ⟨x, hx⟩) := by
    have hle : Subgroup.zpowers (f ⟨x, hx⟩) ≤ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs ⊓
        Subgroup.centralizer (NsQuot.img (Subgroup.normalizer (L : Set G)) f L : Set Q) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_inf.2 ⟨hxmem, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      obtain ⟨u, huL, rfl⟩ := NsQuot.mem_img.1 hq
      have hxC : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
        rw [hcent]
        exact Subgroup.mem_zpowers x
      have hcomm : (u : G) * x = x * (u : G) :=
        Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hxC).2 _ huL
      rw [← map_mul, ← map_mul]
      exact congrArg f (Subtype.ext hcomm)
    refine (Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)).symm
    rw [hD.cent hLperf le_rfl, hcent, Nat.card_zpowers, Nat.card_zpowers, hxord, hxord']
  refine ⟨rfl, K, hKf, hKfin, hKchar, Q, hQ, hQfin, f, ψ, ?_⟩
  rw [← hrange] at hcentQ ⊢
  obtain ⟨ε, hε, hrefl⟩ := ggNSDiag_automizer_perm hhyp hdiag
  refine ⟨ε, hx, hD, ⟨rfl, hK, hhyp, rfl, hdiag, hε, hrefl, fun a b hab =>
    ggNSDiag_rankOne_block hhyp hdiag a b hab _ (fun s => by
      have := hε (Equiv.swap a b) s
      rwa [Equiv.swap_inv] at this), hcard, hxmem, hxord', hcentQ,
    ggQTwoDUnit_base_full hK hhyp rfl hdiag hcard hcentQ hxord'⟩⟩

theorem ggQTwoDUnitSix_coords
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (e' : Fin 6 ≃ ι) (hM : M = (ggCoxeterMatrixD 6).reindex e')
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    p = 3 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (Q : Type) (_ : Group Q)
      (_ : Finite Q) (f : ↥(Subgroup.normalizer (L : Set G)) →* Q) (ψ : Su K 2 1 6 →* Q)
      (ε : Equiv.Perm (Fin 6) ≃*
        ↥(ggAutomizer (NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
          (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)))
      (hx : x ∈ Subgroup.normalizer (L : Set G)) (βL : Additive ↥Bs ≃+ DVec 6) (ω : Kˣ),
      NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L) ∧
      QTwoUnitBase 3 (NsQuot.img (Subgroup.normalizer (L : Set G)) f B)
        (NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs) (f ⟨x, hx⟩)
        (NsQuot.img (Subgroup.normalizer (L : Set G)) f L) ψ ε ∧
      orderOf ω = 3 ∧
      (∀ hx' : x ∈ Bs, βL (Additive.ofMul ⟨x, hx'⟩) = fun _ => 1) ∧
      (∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
        qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val)) ∧
      (∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
        (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
        f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
          βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s))) ∧
      (∀ w ∈ dEven 6, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
        ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s))) ∧
      (∀ (sgn : Bool) (a b : Fin 6), a ≠ b → ∀ r ∈ ggAutomizerJoin L Bs 𝒦,
        (∀ s : ↥Bs, βL (Additive.ofMul (r s)) = dTau 6 sgn a b (βL (Additive.ofMul s))) →
          r ∈ ggCoxRefl M e) ∧
      (∀ r ∈ ggCoxRefl M e, ∃ (sgn : Bool) (a b : Fin 6), a ≠ b ∧ ∀ s : ↥Bs,
        βL (Additive.ofMul (r s)) = dTau 6 sgn a b (βL (Additive.ofMul s))) ∧
      (∃ c₀ : Fin 6, ∀ i : Fin 6, (i : ℕ) ≠ 0 → ∃ (sgn : Bool) (a b : Fin 6),
        a ≠ b ∧ a ≠ c₀ ∧ b ≠ c₀ ∧ ∀ s : ↥Bs,
          βL (Additive.ofMul ((((e (M.simple (e' i)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
            s)) = dTau 6 sgn a b (βL (Additive.ofMul s))) := by
  classical
  obtain ⟨hp3, K, hKf, hKfin, hKchar, Q, hQ, hQfin, f, ψ, ε, hx, hD, hbase⟩ :=
    ggQTwoDUnitSix_quotBase hTBF hWI hcfg e' hM hmark
  subst hp3
  obtain ⟨hxBs, hxord, hcent⟩ := ggQTwoDUnit_base_cent hcfg rfl
  have hxL : ∀ l ∈ L, l * x = x * l := by
    have hxC : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hcent]
      exact Subgroup.mem_zpowers x
    exact fun l hl => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxC).2 l hl
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord
    exact absurd hxord (by norm_num)
  let τ := hD.tau
  have hmemA : ∀ σ : Equiv.Perm (Fin 6),
      (MulAut.congr τ).symm ((ε σ : ↥(ggAutomizer _ _)) : MulAut ↥(NsQuot.img _ f Bs)) ∈
        ggAutomizer L Bs := by
    intro σ
    obtain ⟨r, hr, hrε⟩ := Subgroup.mem_map.1
      (hD.automizer_le_map hD.ZL hD.LN (ε σ).2)
    have hr' : (MulAut.congr τ).symm ((ε σ : ↥(ggAutomizer _ _)) : MulAut _) = r := by
      rw [← hrε]
      exact (MulAut.congr τ).symm_apply_apply r
    rw [hr']
    exact hr
  let φ₀ : Equiv.Perm (Fin 6) →* ↥(ggAutomizer L Bs) :=
    ((MulAut.congr τ).symm.toMonoidHom.comp
      ((ggAutomizer _ _).subtype.comp ε.toMonoidHom)).codRestrict (ggAutomizer L Bs) hmemA
  have hφ₀ : ∀ σ : Equiv.Perm (Fin 6), ((φ₀ σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) =
      (MulAut.congr τ).symm ((ε σ : ↥(ggAutomizer _ _)) : MulAut _) := fun _ => rfl
  have hφ₀inj : Function.Injective φ₀ := by
    intro σ σ' h
    apply ε.injective
    apply Subtype.ext
    apply (MulAut.congr τ).symm.injective
    rw [← hφ₀, ← hφ₀, h]
  have hrefl : ∀ a b : Fin 6, a ≠ b →
      GGIsReflection 3 ((φ₀ (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
    intro a b hab
    rw [hφ₀]
    exact (ggIsReflection_congr_iff τ _).1 (by
      rw [MulEquiv.apply_symm_apply]
      exact hbase.refl a b hab)
  obtain ⟨βL, hxcoord, hperm, hjoin, hcox, hcoxRoot, hnode⟩ :=
    ggQTwoDUnit_coords_of_perm hTBF hWI hcfg e' (by norm_num) hM hxBs hxL hx1 φ₀ hφ₀inj hrefl
  let βQ : Additive ↥(NsQuot.img _ f Bs) ≃+ DVec 6 := (MulEquiv.toAdditive τ.symm).trans βL
  have hβQ : ∀ s : ↥Bs, βQ (Additive.ofMul (τ s)) = βL (Additive.ofMul s) := by
    intro s
    change βL (Additive.ofMul (τ.symm (τ s))) = βL (Additive.ofMul s)
    rw [MulEquiv.symm_apply_apply]
  have hβQperm : ∀ (σ : Equiv.Perm (Fin 6)) (q : ↥(NsQuot.img _ f Bs)),
      βQ (Additive.ofMul ((((ε σ : ↥(ggAutomizer _ _)) : MulAut ↥(NsQuot.img _ f Bs))) q)) =
        dPerm 6 σ (βQ (Additive.ofMul q)) := by
    intro σ q
    obtain ⟨s, rfl⟩ := τ.surjective q
    have hεσ : ((ε σ : ↥(ggAutomizer _ _)) : MulAut ↥(NsQuot.img _ f Bs)) =
        MulAut.congr τ ((φ₀ σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
      rw [hφ₀, MulEquiv.apply_symm_apply]
    rw [hεσ, congr_apply_tau, hβQ, hβQ]
    exact hperm σ s
  have hmodel : QTwoOrdModel (NsQuot.img _ f Bs) (NsQuot.img _ f L) ψ :=
    ⟨hbase.range, hbase.hyp.ker, fun b => by
      obtain ⟨g, hg, hgu⟩ := hbase.diag (b : Q) b.2
      exact ⟨g, hg, fun u => by
        obtain ⟨u', hu'1, hu'2⟩ := hgu.2 u
        exact ⟨u', hu'1, hu'2.symm⟩⟩⟩
  obtain ⟨ω, hω, hind⟩ := qtwoDB19_coords_induces (m := 6) (Bs := NsQuot.img _ f Bs)
    (L := NsQuot.img _ f L) (x := f ⟨x, hx⟩) (ψ := ψ) (ε := ε) hbase.card_field hbase.hyp.ker
    (by norm_num) hbase.range hbase.cent hbase.card_bs hbase.x_order
    (fun b => qTwoChartTwoThree_induces_of_ordModel hmodel b) hbase.perm hβQperm
  refine ⟨rfl, K, hKf, hKfin, hKchar, Q, hQ, hQfin, f, ψ, ε, hx, βL, ω, hD, hbase, hω, hxcoord,
    fun s hs => ?_, fun σ s t hs ht hst => ?_, hjoin, hcox, hcoxRoot, hnode⟩
  · have h := hind (τ s)
    rw [hβQ] at h
    exact h
  · have hεs : (((ε σ : ↥(ggAutomizer _ _)) : MulAut ↥(NsQuot.img _ f Bs)) (τ s)) = τ t := by
      apply Subtype.ext
      rw [hbase.perm σ (τ s)]
      exact hst.symm
    have h := hβQperm σ (τ s)
    rw [hεs, hβQ, hβQ] at h
    exact h

end CFSG.StandardType.QTwo

end
