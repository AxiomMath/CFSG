module

public import CFSG.RankThree.PartOne.K159.PerfNormalizerFive
import CFSG.RankThree.PartOne.S12.Sec1511Tools
import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas
import CFSG.Milestones.OO_odd_order_solvable
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.RankThree.PartOne.U5E

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K
  CFSG.RankThree.PartOne.U5K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem perfect_le_of_sup_solvable {I C Z : Subgroup G}
    (hIC : ∀ a ∈ I, ∀ b ∈ C, a * b = b * a) (hC : Group.IsSolvable ↥C)
    (hZ : Group.IsPerfect ↥Z) (hZle : Z ≤ I ⊔ C) : Z ≤ I := by
  classical
  have hIM : I ≤ I ⊔ C := le_sup_left
  have hCM : C ≤ I ⊔ C := le_sup_right
  have hCcent : C ≤ Subgroup.centralizer (I : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun a ha => hIC a ha b hb
  have hMN : I ⊔ C ≤ Subgroup.normalizer (I : Set G) :=
    sup_le Subgroup.le_normalizer (hCcent.trans (Subgroup.centralizer_le_normalizer _))
  have hnorm : (I.subgroupOf (I ⊔ C)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIM).2 hMN
  let π : ↥(I ⊔ C) →* ↥(I ⊔ C) ⧸ I.subgroupOf (I ⊔ C) := QuotientGroup.mk' _
  have hsurj : Function.Surjective (π.comp (Subgroup.inclusion hCM)) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨i, hi, d, hd, hyd⟩ := PlaneCommuting.exists_mul_of_mem_sup hIC y.2
    refine ⟨⟨d, hd⟩, ?_⟩
    show QuotientGroup.mk (⟨d, hCM hd⟩ : ↥(I ⊔ C)) = QuotientGroup.mk y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : d⁻¹ * (i * d) = i := by
      have := hIC i hi d⁻¹ (C.inv_mem hd)
      calc d⁻¹ * (i * d) = (d⁻¹ * i) * d := by group
        _ = (i * d⁻¹) * d := by rw [this]
        _ = i := by group
    have h2 : ((⟨d, hCM hd⟩ : ↥(I ⊔ C))⁻¹ * y : ↥(I ⊔ C)) = ⟨i, hIM hi⟩ :=
      Subtype.ext (by simp [hyd, h1])
    rw [h2]
    exact hi
  have := hC
  have : Group.IsSolvable (↥(I ⊔ C) ⧸ I.subgroupOf (I ⊔ C)) :=
    Group.isSolvable_of_surjective (f := π.comp (Subgroup.inclusion hCM)) hsurj
  have hZ' : Group.IsPerfect ↥(Z.subgroupOf (I ⊔ C)) := by
    have := hZ
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hZle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hZle).symm.surjective
  have := hZ'
  have hP : Group.IsPerfect ↥((Z.subgroupOf (I ⊔ C)).map π) := Group.IsPerfect.map π
  have hPs : Group.IsSolvable ↥((Z.subgroupOf (I ⊔ C)).map π) := inferInstance
  have hbot : (Z.subgroupOf (I ⊔ C)).map π = ⊥ := by
    by_contra hne
    have : Nontrivial ↥((Z.subgroupOf (I ⊔ C)).map π) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable _ hPs
  intro z hz
  have hzM : (⟨z, hZle hz⟩ : ↥(I ⊔ C)) ∈ Z.subgroupOf (I ⊔ C) := hz
  have h1 : π ⟨z, hZle hz⟩ ∈ (Z.subgroupOf (I ⊔ C)).map π := ⟨_, hzM, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have h1' : (QuotientGroup.mk (⟨z, hZle hz⟩ : ↥(I ⊔ C)) : ↥(I ⊔ C) ⧸ I.subgroupOf (I ⊔ C)) = 1 :=
    h1
  exact (QuotientGroup.eq_one_iff (N := I.subgroupOf (I ⊔ C)) (⟨z, hZle hz⟩ : ↥(I ⊔ C))).1 h1'

section Odd

variable [Finite G]

theorem odd_card_centralizer_of_coprime {p : ℕ} {A : Subgroup G} {c : G} {L E I : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hcardE : Nat.card ↥E = p ^ 4)
    (hEN : E ≤ Subgroup.normalizer (I : Set G))
    (hcop : ¬ p ∣ Nat.card ↥(Subgroup.centralizer (I : Set G))) :
    Odd (Nat.card ↥(Subgroup.centralizer (I : Set G))) := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p ↥E := h.E_elem
  have hEC : E ≤ Subgroup.normalizer ((Subgroup.centralizer (I : Set G) : Subgroup G) : Set G) :=
    hEN.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup I)
  let φ : ↥E →* MulAut ↥(Subgroup.centralizer (I : Set G)) :=
    (Subgroup.centralizer (I : Set G)).normalizerMonoidHom.comp (Subgroup.inclusion hEC)
  obtain ⟨S, hS⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime p 2
    (IsElementaryAbelian.isPGroup p ↥E) hcop φ
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(Subgroup.centralizer (I : Set G)) := by
    rcases Nat.even_or_odd (Nat.card ↥(Subgroup.centralizer (I : Set G))) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  have hSne : (S : Subgroup ↥(Subgroup.centralizer (I : Set G))) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card S h2
  have hS'ne : (S : Subgroup ↥(Subgroup.centralizer (I : Set G))).map
      (Subgroup.centralizer (I : Set G)).subtype ≠ ⊥ := by
    intro hbot
    apply hSne
    exact Subgroup.map_injective (Subgroup.centralizer (I : Set G)).subtype_injective
      (hbot.trans (Subgroup.map_bot _).symm)
  have hS'2 : IsPGroup 2 ↥((S : Subgroup ↥(Subgroup.centralizer (I : Set G))).map
      (Subgroup.centralizer (I : Set G)).subtype) :=
    S.isPGroup'.map (Subgroup.centralizer (I : Set G)).subtype
  have key : ∀ y : ↥E, ∀ g : G, g ∈ (S : Subgroup ↥(Subgroup.centralizer (I : Set G))).map
      (Subgroup.centralizer (I : Set G)).subtype →
      (y : G) * g * (y : G)⁻¹ ∈ (S : Subgroup ↥(Subgroup.centralizer (I : Set G))).map
        (Subgroup.centralizer (I : Set G)).subtype := by
    intro y g hg
    obtain ⟨s, hs, rfl⟩ := hg
    have hmem : (φ y) s ∈ (S : Subgroup ↥(Subgroup.centralizer (I : Set G))).map
        (φ y).toMonoidHom := ⟨s, hs, rfl⟩
    rw [hS y] at hmem
    refine ⟨(φ y) s, hmem, ?_⟩
    show (((Subgroup.centralizer (I : Set G)).normalizerMonoidHom (Subgroup.inclusion hEC y)) s :
      ↥(Subgroup.centralizer (I : Set G))).1 = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hES : E ≤ Subgroup.normalizer (((S : Subgroup ↥(Subgroup.centralizer (I : Set G))).map
      (Subgroup.centralizer (I : Set G)).subtype : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact key ⟨x, hx⟩ g
    · intro hg
      have := key ⟨x, hx⟩⁻¹ _ hg
      simpa [mul_assoc] using this
  have hrank := Sec1511.rank_le_three h E h.E_elem ⟨_, hS'ne, hS'2, hES⟩
  rw [hcardE] at hrank
  have : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

omit [Finite G] in
theorem centralizer_le_kerG {I : Subgroup G} {f : ℕ}
    (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f) :
    Subgroup.centralizer (I : Set G) ≤ kerG I e := by
  intro z hzC
  have hzN : z ∈ Subgroup.normalizer (I : Set G) := (Subgroup.centralizer_le_normalizer _) hzC
  refine mem_kerG.2 ⟨hzN, ?_⟩
  refine MulEquiv.ext fun w => ?_
  obtain ⟨y, rfl⟩ := e.surjective w
  obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective y
  rw [U5K.U5Act_apply]
  have h1 : I.normalizerMonoidHom ⟨z, hzN⟩ i = i := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have := Subgroup.mem_centralizer_iff.1 hzC i i.2
    show z * (i : G) * z⁻¹ = (i : G)
    rw [← this]
    group
  rw [h1]
  rfl

theorem not_dvd_centralizer_five (hEin : U5EInndiag) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) :
    ¬ p ∣ Nat.card ↥(Subgroup.centralizer (lieGenerated p E : Set G)) := by
  obtain ⟨f, hf, hpf, ⟨e⟩, -⟩ := id hout
  have hp := h15.h12.prime
  have hEI : E ≤ Subgroup.normalizer (lieGenerated p E : Set G) := E_le_lieNormalizer h15
  have hker := U5K.ker_not_dvd_p_of_max hp e h15.h12.E_elem hEI h15.h12.A_le_E h15.h12.E_le
    h15.h12.E_max (fun x hx hxE h => (hEin G p A c L E h15 hF hout f hf e x hx hxE).2 h)
  intro hdvd
  apply hker
  have h6 := Subgroup.card_dvd_of_le (centralizer_le_kerG (G := G) (I := lieGenerated p E) e)
  rw [U5K.card_kerG] at h6
  exact hdvd.trans h6

theorem odd_card_centralizer_lieGenerated_five (hEin : U5EInndiag) {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) :
    Odd (Nat.card ↥(Subgroup.centralizer (lieGenerated p E : Set G))) := by
  obtain ⟨f, hf, hpf, ⟨e⟩, -, hcardE, -⟩ := id hout
  exact odd_card_centralizer_of_coprime h15.h12 hcardE (E_le_lieNormalizer h15)
    (not_dvd_centralizer_five hEin h15 hF hout)

theorem isSolvable_centralizer_lieGenerated_five (hEin : U5EInndiag) {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) :
    Group.IsSolvable ↥(Subgroup.centralizer (lieGenerated p E : Set G)) :=
  CFSG.Milestones.odd_order_solvable (odd_card_centralizer_lieGenerated_five hEin h15 hF hout)

theorem thetaComponents_le_lieGenerated (hEin : U5EInndiag) (hPerf : K159.KFPerfNormalizerFive)
    {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hout : Outcome152Five p E A (lieGenerated p E)) {e : G}
    (hΘ : ∀ Z ∈ thetaComponentsAt p e, Z ≤ lieNormalizer p E) :
    ∀ Z ∈ thetaComponentsAt p e, Z ≤ lieGenerated p E := by
  intro Z hZ
  have hperf : Group.IsPerfect ↥Z := isPerfect_of_mem_thetaComponentsAt hZ
  have hZIC : Z ≤ lieGenerated p E ⊔ Subgroup.centralizer (lieGenerated p E : Set G) :=
    hPerf G p A c L E h15 hF hout Z hperf (hΘ Z hZ)
  have hsol := isSolvable_centralizer_lieGenerated_five hEin h15 hF hout
  exact perfect_le_of_sup_solvable
    (fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb a ha) hsol hperf hZIC

theorem layerInner_of_le {p : ℕ} (hp : p.Prime) {E I : Subgroup G} {e : G}
    (he : e ∈ E) (he1 : e ≠ 1) (hLD : LayerDataW p E I)
    (hQθ : ∀ Q : Subgroup G, Q ≤ I ⊓ Subgroup.centralizer ({e} : Set G) →
      IsComponent (Q.subgroupOf (I ⊓ Subgroup.centralizer ({e} : Set G))) → Q ≤ thetaLayer p e)
    (hZI : ∀ Z ∈ thetaComponentsAt p e, Z ≤ I) :
    (∀ x ∈ E, ∃ l ∈ thetaLayer p e, ∃ c' ∈ Subgroup.centralizer (thetaLayer p e : Set G),
        x = l * c') ∧
      ¬ p ∣ Nat.card ↥(thetaLayer p e ⊓ Subgroup.centralizer (thetaLayer p e : Set G)) := by
  classical
  obtain ⟨ι, Q, hQH, hQc, hperfQ, hQ⟩ := hLD e he he1
  set S : Finset (Subgroup G) := (Set.toFinite (Set.range Q)).toFinset with hS
  have hSmem : ∀ Y, Y ∈ S ↔ ∃ i, Q i = Y := by
    intro Y
    simp [hS]
  have hsup : S.sup id = ⨆ i, Q i := by
    apply le_antisymm
    · exact Finset.sup_le fun Y hY => by
        obtain ⟨i, rfl⟩ := (hSmem Y).1 hY
        exact le_iSup Q i
    · exact iSup_le fun i => Finset.le_sup (f := id) ((hSmem _).2 ⟨i, rfl⟩)
  have hcommS : ∀ Y ∈ S, ∀ Y' ∈ S, Y ≠ Y' → ∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a := by
    intro Y hY Y' hY' hne a ha b hb
    obtain ⟨i, rfl⟩ := (hSmem Y).1 hY
    obtain ⟨j, rfl⟩ := (hSmem Y').1 hY'
    rcases eq_or_commutator_eq_bot_of_components (hQH i) (hQH j) (hQc i) (hQc j) with hij | hij
    · exact absurd hij hne
    · have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hij ha
      exact (Subgroup.mem_centralizer_iff.1 this b hb).symm
  have hinS : ∀ Y ∈ S, ∀ x ∈ E, ∃ y ∈ Y, ∃ c ∈ Subgroup.centralizer (Y : Set G), x = y * c := by
    intro Y hY x hx
    obtain ⟨i, rfl⟩ := (hSmem Y).1 hY
    exact (hQ i).1 x hx
  have hzS : ∀ Y ∈ S, ∀ z ∈ Y ⊓ Subgroup.centralizer (Y : Set G), ¬ p ∣ orderOf z := by
    intro Y hY z hz hdvd
    obtain ⟨i, rfl⟩ := (hSmem Y).1 hY
    exact (hQ i).2 (hdvd.trans (Subgroup.orderOf_dvd_natCard _ hz))
  have hA := K159.inner_finset_sup S hcommS hinS
  have hB := K159.noP_finset_sup hp S hcommS hzS
  set Y₀ : Subgroup G := S.sup id with hY₀
  have hQL : ∀ i, Q i ≤ thetaLayer p e := fun i => hQθ (Q i) (hQH i) (hQc i)
  have hY₀L : Y₀ ≤ thetaLayer p e := by
    rw [hsup]
    exact iSup_le hQL
  have hperfY₀ : ∀ P : Subgroup G, P ≤ I ⊓ Subgroup.centralizer ({e} : Set G) →
      Group.IsPerfect ↥P → P ≤ Y₀ := by
    intro P hPH hPperf
    rw [hsup]
    exact hperfQ P hPH hPperf
  have hLY : thetaLayer p e ≤ Y₀ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨Z, hZ, hxZ⟩
    have hperf := isPerfect_of_mem_thetaComponentsAt hZ
    have hZe : Z ≤ Subgroup.centralizer ({e} : Set G) := (mem_thetaComponentsAt_iff.1 hZ).1
    exact hperfY₀ Z (fun y hy => ⟨hZI Z hZ hy, hZe hy⟩) hperf hxZ
  refine ⟨fun x hx => ?_, fun hdvd => ?_⟩
  · obtain ⟨q, hq, c₀, hc₀, hxqc⟩ := hA x hx
    exact ⟨q, hY₀L hq, c₀, Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hLY) hc₀, hxqc⟩
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hzo⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(thetaLayer p e ⊓ Subgroup.centralizer (thetaLayer p e : Set G))) p hdvd
    have hzL : (z : G) ∈ thetaLayer p e := z.2.1
    have hzC : (z : G) ∈ Subgroup.centralizer (thetaLayer p e : Set G) := z.2.2
    have hzo' : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe]; exact hzo
    have hzY : (z : G) ∈ Y₀ ⊓ Subgroup.centralizer (Y₀ : Set G) :=
      ⟨hLY hzL, Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hY₀L) hzC⟩
    have hdz : p ∣ orderOf (z : G) := by rw [hzo']
    exact hB _ hzY hdz

end Odd

section Five

variable [Finite G]

theorem kfInnLayerFiveP5_of_facts (hMod : KFU5Mod) (hAt : KFU5At) (h5 : U5FiveInndiag)
    (hPerf : K159.KFPerfNormalizerFive) (hComp : K159.KFCompLayerFive) :
    K159.KFInnLayerFiveP5 := by
  intro G _ _ p A c L E h15 hF hout e he he1 _ hΘ _ _
  classical
  have hEin : U5EInndiag := U5K.u5EInndiag_of hMod hAt h5
  have h := h15.h12
  have hp := h.prime
  have hRow : LayerDataW p E (lieGenerated p E) := layerRowFive_of hEin G p A c L E h15 hF hout
  obtain ⟨hinn, hcenter⟩ := layerInner_of_le hp he he1 hRow
    (hComp G p A c L E h15 hF hout e he he1)
    (thetaComponents_le_lieGenerated hEin hPerf h15 hF hout hΘ)
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEpow : ∀ x ∈ E, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx
  refine K159.inf_mul_inf_of_inner hp hEcomm hEpow ?_ hinn hcenter
  intro F hFc hFp hFE hEF
  have hFel : IsElementaryAbelian p ↥F :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hFc a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hFp a a.2) }
  exact (h.E_max_global F hFel hEF).le

theorem kfInnLayerFive_of_schreier' (hS : SchreierFor CFSG.Blueprint.Catalog) (hMod : KFU5Mod)
    (hAt : KFU5At) (h5 : U5FiveInndiag) (hComp : K159.KFCompLayerFive) : KFInnLayerFive :=
  K159.kfInnLayerFive_of_schreier hS hMod hAt h5 hComp
    (kfInnLayerFiveP5_of_facts hMod hAt h5
      (K159.kfPerfNormalizerFive_of_schreier hS hMod hAt h5) hComp)

end Five

end CFSG.RankThree.PartOne.U5E
