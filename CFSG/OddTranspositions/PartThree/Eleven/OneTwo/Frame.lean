module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Kernel
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.FrameLift
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.SixFiveInputs
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.WidthOne

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open scoped IsMulCommutative

section Frame

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def frameT (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) : G :=
  ((r 0 * r 1 * r 2 : Halpha D hC.alpha) : G)

@[expose] def frameE (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) : G :=
  hC.d * frameT hC r

structure ElevenTwoFrame (hC : HypothesisC D) (S : Sylow 2 G) (T : Sylow 2 (Halpha D hC.alpha))
    (r : Fin 3 → Halpha D hC.alpha) : Prop where
  frame : O4MinusFrame (DstarH hC) (T : Subgroup (Halpha D hC.alpha)) r
  le : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ (S : Subgroup G)
  d_mem : hC.d ∈ (S : Subgroup G)
  inter_eq : (S : Set G) ∩ D = insert hC.d (Set.range fun i => ((r i : Halpha D hC.alpha) : G))

private theorem commute_d_frameT (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) :
    Commute hC.d (frameT hC r) :=
  (Subgroup.mem_centralizer_singleton_iff.mp
    (Halpha_le_centralizer_d hC (r 0 * r 1 * r 2 : Halpha D hC.alpha).2)).symm

private theorem inter_D_eq_minus {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)}
    {r : Fin 3 → Halpha D hC.alpha}
    (hr : O4MinusFrame (DstarH hC) (T : Subgroup (Halpha D hC.alpha)) r)
    (hα : hC.alpha = {hC.d}) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S)
    (hd : hC.d ∈ S) :
    (S : Set G) ∩ D = insert hC.d (Set.range fun i => ((r i : Halpha D hC.alpha) : G)) := by
  classical
  have hD : IsOddTransp D := hC.setup.oddT
  have huD : hC.d ∈ D := hC.hd
  ext x
  constructor
  · rintro ⟨hxS, hxD⟩
    by_cases hxu : x = hC.d
    · exact Or.inl hxu
    · refine Or.inr ?_
      have hcomm : Commute x hC.d :=
        commute_of_mul_mem_of_isPGroup hD hS hxD huD (S.mul_mem hxS hd)
      have hxE : x ∈ DalphaStar D hC.alpha := by
        have hxD' := hxD
        rw [hC.eq_alpha_union] at hxD'
        rcases hxD' with (hxα | hxE) | hxA
        · rw [hα] at hxα
          exact absurd (by simpa using hxα) hxu
        · exact hxE
        · rw [hC.AalphaStar_eq_diff_alpha] at hxA
          exact absurd hcomm hxA.1.2
      have hxH : x ∈ Halpha D hC.alpha := Subgroup.subset_closure hxE
      let Q : Subgroup G := S ⊓ Halpha D hC.alpha
      have hQp : IsPGroup 2 Q := hS.to_le inf_le_left
      have hQH : Q ≤ Halpha D hC.alpha := inf_le_right
      have hTleQ : (T : Subgroup (Halpha D hC.alpha)) ≤
          Q.subgroupOf (Halpha D hC.alpha) := by
        intro t ht
        rw [Subgroup.mem_subgroupOf]
        exact ⟨hTS (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩), t.2⟩
      have hQsp : IsPGroup 2 (Q.subgroupOf (Halpha D hC.alpha)) :=
        hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
      have hTeq : Q.subgroupOf (Halpha D hC.alpha) = T := T.is_maximal' hQsp hTleQ
      have hxQ : x ∈ Q := ⟨hxS, hxH⟩
      have hxT : (⟨x, hxH⟩ : Halpha D hC.alpha) ∈ (T : Subgroup (Halpha D hC.alpha)) := by
        rw [← hTeq]
        exact Subgroup.mem_subgroupOf.mpr hxQ
      have hxint : (⟨x, hxH⟩ : Halpha D hC.alpha) ∈
          (T : Set (Halpha D hC.alpha)) ∩ DstarH hC :=
        ⟨hxT, (mem_DstarH_iff hC).mpr hxE⟩
      obtain ⟨i, hi⟩ := hr.inter_eq ▸ hxint
      exact ⟨i, congrArg Subtype.val hi⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨hd, huD⟩
    · have hwiT : r i ∈ (T : Set (Halpha D hC.alpha)) :=
        (hr.inter_eq ▸ Set.mem_range_self i).1
      have hwiD : ((r i : Halpha D hC.alpha) : G) ∈ D :=
        DalphaStar_subset hC.isBlock_alpha
          ((mem_DstarH_iff hC).mp ((hr.inter_eq ▸ Set.mem_range_self i).2))
      exact ⟨hTS (Subgroup.mem_map.mpr ⟨r i, hwiT, rfl⟩), hwiD⟩

private theorem mulAut_conj_prod_eq_of_image_eq {x : Fin 4 → G}
    (hx : Function.Injective x) (hcomm : ∀ i j, Commute (x i) (x j)) (g : G)
    (himg : MulAut.conj g '' Set.range x = Set.range x) :
    MulAut.conj g (x 0 * x 1 * x 2 * x 3) = x 0 * x 1 * x 2 * x 3 := by
  classical
  have hmem : ∀ i, MulAut.conj g (x i) ∈ Set.range x := by
    intro i
    have : MulAut.conj g (x i) ∈ MulAut.conj g '' Set.range x :=
      Set.mem_image_of_mem (MulAut.conj g) ⟨i, rfl⟩
    rwa [himg] at this
  choose σ hσ using hmem
  have hσinj : Function.Injective σ := by
    intro i j hij
    apply hx
    have : MulAut.conj g (x i) = MulAut.conj g (x j) := by rw [← hσ i, ← hσ j, hij]
    exact (MulAut.conj g).injective this
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hσinj
  let A : Subgroup G := Subgroup.closure (Set.range x)
  have hpair : (Set.range x).Pairwise (Commute) := by
    intro a ha b hb _
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact hcomm i j
  letI : IsMulCommutative A := Subgroup.isMulCommutative_closure hpair
  let z : Fin 4 → A := fun i => ⟨x i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  let E : A := ∏ i, z i
  have hE : (E : G) = x 0 * x 1 * x 2 * x 3 := by
    have h1 : E = z 0 * z 1 * z 2 * z 3 := Fin.prod_univ_four z
    rw [h1]
    simp [z]
  have hfix : MulAut.conj g (E : G) = (E : G) := by
    have h2 : MulAut.conj g (E : G) =
        (z (σ 0) * z (σ 1) * z (σ 2) * z (σ 3) : A) := by
      rw [hE, map_mul, map_mul, map_mul]
      rw [← hσ 0, ← hσ 1, ← hσ 2, ← hσ 3]
      rfl
    have h3 : (z (σ 0) * z (σ 1) * z (σ 2) * z (σ 3) : A) = E := by
      rw [← Fin.prod_univ_four (fun i => z (σ i))]
      exact Fintype.prod_bijective σ hbij (fun i => z (σ i)) z (fun i => rfl)
    rw [h2, h3]
  rw [← hE]
  exact hfix

theorem ElevenTwoHyp.exists_frame {hC : HypothesisC D} (h : ElevenTwoHyp hC) :
    ∃ (S : Sylow 2 G) (T : Sylow 2 (Halpha D hC.alpha)) (r : Fin 3 → Halpha D hC.alpha),
      ElevenTwoFrame hC S T r := by
  classical
  let T : Sylow 2 (Halpha D hC.alpha) := default
  obtain ⟨r, hr⟩ := h.factsH.frame T
  obtain ⟨S, hTS, hdS⟩ := exists_sylow_frame hC T
  refine ⟨S, T, r, hr, hTS, hdS, ?_⟩
  exact inter_D_eq_minus hr h.alpha_eq S.isPGroup' hTS hdS

namespace ElevenTwoFrame

variable {hC : HypothesisC D} {S : Sylow 2 G} {T : Sylow 2 (Halpha D hC.alpha)}
  {r : Fin 3 → Halpha D hC.alpha}

theorem ncard_inter (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    ((S : Set G) ∩ D).ncard = 4 := by
  have hnot : hC.d ∉ Set.range fun i => ((r i : Halpha D hC.alpha) : G) := by
    rintro ⟨i, hi⟩
    exact h.d_not_mem_Halpha (by rw [← hi]; exact (r i).2)
  have hinj : Function.Injective (fun i => ((r i : Halpha D hC.alpha) : G)) :=
    fun i j hij => hF.frame.injective (Subtype.ext hij)
  rw [hF.inter_eq, Set.ncard_insert_of_notMem hnot,
    Set.ncard_range_of_injective hinj, Nat.card_fin]

theorem ncard_inter_sylow (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    (S' : Sylow 2 G) : ((S' : Set G) ∩ D).ncard = 4 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
  have himg : (MulAut.conj g '' (S : Set G)) ∩ D =
      MulAut.conj g '' ((S : Set G) ∩ D) := by
    ext x
    constructor
    · rintro ⟨⟨y, hyS, rfl⟩, hxD⟩
      refine ⟨y, ⟨hyS, ?_⟩, rfl⟩
      have h := hC.setup.normal g⁻¹ (MulAut.conj g y) hxD
      rwa [show g⁻¹ * (MulAut.conj g y) * (g⁻¹)⁻¹ = y by
        simp only [MulAut.conj_apply]; group] at h
    · rintro ⟨y, ⟨hyS, hyD⟩, rfl⟩
      exact ⟨⟨y, hyS, rfl⟩, hC.setup.normal g y hyD⟩
  have hS' : (S' : Set G) = MulAut.conj g '' (S : Set G) := by
    rw [← hg, Sylow.coe_smul]
    rfl
  rw [hS', himg, Set.ncard_image_of_injective _ (MulAut.conj g).injective]
  exact ncard_inter h hF

theorem mem_commSet (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) (i : Fin 3) :
    ((r i : Halpha D hC.alpha) : G) ∈ commSet D hC.d := by
  have hri : r i ∈ DstarH hC := (hF.frame.inter_eq ▸ Set.mem_range_self i).2
  have hDα : ((r i : Halpha D hC.alpha) : G) ∈ DalphaStar D hC.alpha :=
    (mem_DstarH_iff hC).mp hri
  rwa [← h.DalphaStar_eq]

private theorem frameT_mul_self (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    frameT hC r * frameT hC r = 1 := by
  have hr : ∀ i, r i ∈ DstarH hC := fun i => (hF.frame.inter_eq ▸ Set.mem_range_self i).2
  have hsq : ∀ i, r i * r i = 1 := fun i =>
    (DstarH_isOddTransp hC).mul_self_eq_one (hr i)
  have hcomm_a : Commute (r 0) (r 1 * r 2) :=
    (hF.frame.commute 0 1).mul_right (hF.frame.commute 0 2)
  have hcomm_b : Commute (r 1) (r 2) := hF.frame.commute 1 2
  have htH : (r 0 * r 1 * r 2 : Halpha D hC.alpha) * (r 0 * r 1 * r 2) = 1 := by
    have h1 : (r 0 * (r 1 * r 2)) ^ 2 = 1 := by
      rw [hcomm_a.mul_pow 2, hcomm_b.mul_pow 2, pow_two, pow_two, pow_two,
        hsq 0, hsq 1, hsq 2]
      simp
    rw [← pow_two, mul_assoc]
    exact h1
  show ((r 0 * r 1 * r 2 : Halpha D hC.alpha) : G) *
    ((r 0 * r 1 * r 2 : Halpha D hC.alpha) : G) = 1
  rw [← Subgroup.coe_mul, htH]
  rfl

theorem frameT_not_mem (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    frameT hC r ∉ D := by
  intro htD
  apply hF.frame.not_mem
  refine (mem_DstarH_iff hC).mpr ?_
  rw [h.DalphaStar_eq]
  refine ⟨htD, (commute_d_frameT hC r).symm, ?_⟩
  intro heq
  exact h.d_not_mem_Halpha (by
    rw [← heq]
    exact (r 0 * r 1 * r 2 : Halpha D hC.alpha).2)

theorem frameT_ne_one (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    frameT hC r ≠ 1 := by
  intro h1
  have hr0 : r 0 ∈ centSet (DstarH hC) (r 0 * r 1 * r 2) := by
    refine ⟨(hF.frame.inter_eq ▸ Set.mem_range_self 0).2, ?_⟩
    exact ((hF.frame.commute 0 0).mul_right (hF.frame.commute 0 1)).mul_right
      (hF.frame.commute 0 2)
  have hnot := hF.frame.not_mul (r 0) hr0 (r 0) hr0
  apply hnot
  have ht1 : (r 0 * r 1 * r 2 : Halpha D hC.alpha) = 1 := Subtype.ext h1
  have hsq : r 0 * r 0 = 1 :=
    (DstarH_isOddTransp hC).mul_self_eq_one
      ((hF.frame.inter_eq ▸ Set.mem_range_self 0).2)
  rw [hsq, ht1]

theorem frameE_not_mem (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    frameE hC r ∉ D := by
  intro heD
  have hne : frameE hC r ≠ hC.d := by
    intro heq
    apply frameT_ne_one h hF
    have heq' : hC.d * frameT hC r = hC.d := by simpa [frameE] using heq
    exact mul_left_cancel (by rw [heq', mul_one])
  have hcomm : Commute (frameE hC r) hC.d := by
    rw [frameE]
    exact ((Commute.refl hC.d).mul_right (commute_d_frameT hC r)).symm
  have hE : frameE hC r ∈ DalphaStar D hC.alpha := by
    rw [h.DalphaStar_eq]
    exact ⟨heD, hcomm, hne⟩
  have hmemH : frameE hC r ∈ Halpha D hC.alpha := Subgroup.subset_closure hE
  have ht : frameT hC r ∈ Halpha D hC.alpha :=
    (r 0 * r 1 * r 2 : Halpha D hC.alpha).2
  have hd_eq : frameT hC r * frameE hC r = hC.d := by
    rw [frameE]
    calc frameT hC r * (hC.d * frameT hC r)
        = (frameT hC r * hC.d) * frameT hC r := by rw [mul_assoc]
      _ = (hC.d * frameT hC r) * frameT hC r := by
            rw [(commute_d_frameT hC r).symm.eq]
      _ = hC.d * (frameT hC r * frameT hC r) := by rw [mul_assoc]
      _ = hC.d * 1 := by rw [frameT_mul_self h hF]
      _ = hC.d := mul_one _
  exact h.d_not_mem_Halpha (by
    rw [← hd_eq]
    exact (Halpha D hC.alpha).mul_mem ht hmemH)

theorem orderOf_frameE (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    orderOf (frameE hC r) = 2 := by
  apply orderOf_eq_prime (p := 2)
  · rw [frameE, (commute_d_frameT hC r).mul_pow 2]
    rw [show hC.d ^ 2 = 1 from by
          rw [pow_two]; exact hC.setup.oddT.mul_self_eq_one hC.hd,
        show frameT hC r ^ 2 = 1 from by
          rw [pow_two]; exact frameT_mul_self h hF]
    simp
  · intro he1
    apply h.d_not_mem_Halpha
    have ht_eq : frameT hC r = hC.d := by
      have h2 : frameT hC r = hC.d⁻¹ :=
        eq_inv_of_mul_eq_one_right (by simpa [frameE] using he1)
      rwa [inv_eq_of_mul_eq_one_right (hC.setup.oddT.mul_self_eq_one hC.hd)] at h2
    rw [← ht_eq]
    exact (r 0 * r 1 * r 2 : Halpha D hC.alpha).2

theorem normalizer_le (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    Subgroup.normalizer ((S : Set G) ∩ D) ≤ Subgroup.centralizer {frameE hC r} := by
  intro g hg
  let x : Fin 4 → G := ![hC.d, ((r 0 : Halpha D hC.alpha) : G),
    ((r 1 : Halpha D hC.alpha) : G), ((r 2 : Halpha D hC.alpha) : G)]
  have hx0 : x 0 = hC.d := by simp [x]
  have hx1 : x 1 = ((r 0 : Halpha D hC.alpha) : G) := by simp [x]
  have hx2 : x 2 = ((r 1 : Halpha D hC.alpha) : G) := by simp [x]
  have hx3 : x 3 = ((r 2 : Halpha D hC.alpha) : G) := by simp [x]
  have hrange : (S : Set G) ∩ D = Set.range x := by
    rw [hF.inter_eq]
    ext z
    constructor
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨0, by simp [x]⟩
      · exact ⟨i.succ, by fin_cases i <;> simp [x]⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [x]
  have hx_inj : Function.Injective x := by
    have h4 : (Set.range x).ncard = (Set.univ : Set (Fin 4)).ncard := by
      rw [← hrange, ncard_inter h hF, Set.ncard_univ, Nat.card_fin]
    have hinjOn : (Set.univ : Set (Fin 4)).InjOn x :=
      (Set.ncard_image_iff (s := (Set.univ : Set (Fin 4)))).mp (by
        rw [Set.image_univ]
        exact h4)
    simpa using hinjOn
  have hx_mem : ∀ i, x i ∈ (S : Set G) ∩ D := by
    intro i
    rw [hrange]
    exact Set.mem_range_self i
  have hxcomm : ∀ i j, Commute (x i) (x j) := fun i j =>
    commute_of_mul_mem_of_isPGroup hC.setup.oddT S.isPGroup'
      (hx_mem i).2 (hx_mem j).2 (S.mul_mem (hx_mem i).1 (hx_mem j).1)
  have himg : MulAut.conj g '' Set.range x = Set.range x := by
    rw [← hrange]
    exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hg
  have hxe : x 0 * x 1 * x 2 * x 3 = frameE hC r := by
    rw [hx0, hx1, hx2, hx3, frameE, frameT]
    simp only [Subgroup.coe_mul]
    group
  have hfix : MulAut.conj g (frameE hC r) = frameE hC r := by
    rw [← hxe]
    exact mulAut_conj_prod_eq_of_image_eq hx_inj hxcomm g himg
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * frameE hC r = (g * frameE hC r * g⁻¹) * g := by group
    _ = frameE hC r * g := by rw [← MulAut.conj_apply, hfix]

theorem d_mem_centSet (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    hC.d ∈ centSet D (frameE hC r) := by
  refine ⟨hC.hd, ?_⟩
  rw [frameE]
  exact (Commute.refl hC.d).mul_right (commute_d_frameT hC r)

theorem mem_centSet (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) (i : Fin 3) :
    ((r i : Halpha D hC.alpha) : G) ∈ centSet D (frameE hC r) := by
  refine ⟨(mem_commSet h hF i).1, ?_⟩
  have hcomm_d : Commute ((r i : Halpha D hC.alpha) : G) hC.d :=
    (mem_commSet h hF i).2.1
  have htH : Commute (r i) (r 0 * r 1 * r 2 : Halpha D hC.alpha) :=
    ((hF.frame.commute i 0).mul_right (hF.frame.commute i 1)).mul_right
      (hF.frame.commute i 2)
  have hcomm_t : Commute ((r i : Halpha D hC.alpha) : G) (frameT hC r) := by
    have := htH.map (Subgroup.subtype (Halpha D hC.alpha))
    simpa [frameT] using this
  rw [frameE]
  exact hcomm_d.mul_right hcomm_t

theorem frameE_mem_localGroup (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    frameE hC r ∈ localGroup D (frameE hC r) := by
  rw [localGroup, frameE]
  have hu : hC.d ∈ centSet D (hC.d * frameT hC r) := d_mem_centSet h hF
  have h0 := mem_centSet h hF 0
  have h1 := mem_centSet h hF 1
  have h2 := mem_centSet h hF 2
  have ht : frameT hC r ∈ Subgroup.closure (centSet D (hC.d * frameT hC r)) := by
    show ((r 0 * r 1 * r 2 : Halpha D hC.alpha) : G) ∈ _
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure h0) (Subgroup.subset_closure h1))
      (Subgroup.subset_closure h2)
  exact Subgroup.mul_mem _ (Subgroup.subset_closure hu) ht

theorem commute_frameE (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    ∀ x ∈ localGroup D (frameE hC r), Commute x (frameE hC r) := by
  intro x hx
  rw [localGroup] at hx
  refine Subgroup.closure_induction (p := fun x _ => Commute x (frameE hC r))
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    exact hy.2
  · exact Commute.one_left _
  · intro a b _ _ ha hb
    exact ha.mul_left hb
  · intro a _ ha
    exact Commute.inv_left_iff.mpr ha

end ElevenTwoFrame

end Frame

end CFSG.OddTranspositions.PartThree
