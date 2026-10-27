module

public import CFSG.RankThree.PartTwo.Sec11.Item116Holes
public import CFSG.RankThree.PartTwo.Sec11.TwoStarProofStep1
public import CFSG.RankThree.PartTwo.Sec11.TwoStarProofFitting

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

@[expose] def LFAt {G : Type} [Group G] (L : Subgroup G) (c : G) : Prop :=
  ⁅L, inSubgroup twoFitting
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)))⁆ ≤
    inSubgroup (CFSG.pCore 2)
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)))

section Certified


@[expose] def LFAtC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ∀ m : ℕ, 1 < m → IsL2EvenAt L m → LFAt L c

namespace TwoStarProof

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem le_centralizer_of_config (h : ResidueConfig G A c L a R Y d) :
    L ≤ Subgroup.centralizer ({c} : Set G) := by
  obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
  exact Subgroup.map_subtype_le L'

theorem centralizer_le_normalizer_of_config (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  (centralizer_le_normalizer_zpowers c).trans
    (Sec11Std.normalizer_le_normalizer_L h45 (h.toSec11Std hT))

theorem d_mem_L (h : ResidueConfig G A c L a R Y d) : d ∈ L :=
  (show d ∈ A ⊓ L by rw [h.inf_eq_zpowers]; exact Subgroup.mem_zpowers d).2

theorem theta_L_le (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d)
    (hT : A ∉ partTwoT G) :
    inSubgroup (aschbacherSolvableCore 3) L ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hLC := le_centralizer_of_config h
  have hCL := centralizer_le_normalizer_of_config h45 h hT
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hθLC : θL ≤ C := (Sec6.theta_le L).trans hLC
  obtain ⟨-, -, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := C) Nat.prime_three
  have hn : (θL.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hθLC).mpr
      (hCL.trans (Sec6.normalizer_le_normalizer_theta L))
  have hs : Group.IsSolvable (θL.subgroupOf C) := by
    have := isSolvable_inSubgroup_theta L
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hθLC).toMonoidHom) (MulEquiv.injective _)
  have h3 : ¬ 3 ∣ Nat.card (θL.subgroupOf C) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hθLC).toEquiv]
    exact not_three_dvd_card_inSubgroup_theta L
  have hle := hmax _ hn hs h3
  intro x hx
  exact ⟨⟨x, hθLC hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem autHom_d_ne_one (h : ResidueConfig G A c L a R Y d) {m : ℕ}
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.RankThreeEven.projSL 2
      (GaloisField 2 (3 * m))) (hdN : d ∈ Subgroup.normalizer (L : Set G)) :
    autHom L ⟨d, hdN⟩ ≠ 1 := by
  intro h1
  rw [autHom_of_mem hdN (d_mem_L h)] at h1
  have hinj := conj_injective_of_center_eq_bot (center_eq_bot_of_projSL e)
  have h2 : ((⟨d, d_mem_L h⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 :=
    hinj (by rw [h1, map_one])
  rw [QuotientGroup.eq_one_iff] at h2
  have hd3 : d ^ 3 = 1 := h.mem_partTwoF.1.2 d h.d_mem
  have hd1 : d = 1 := eq_one_of_mem_inSubgroup_theta ⟨_, h2, rfl⟩ hd3
  exact h.not_mem_zpowers (hd1 ▸ Subgroup.one_mem _)

theorem autHom_c_eq_one (h : ResidueConfig G A c L a R Y d)
    (hcN : c ∈ Subgroup.normalizer (L : Set G)) : autHom L ⟨c, hcN⟩ = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H w =>
    change Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨c, hcN⟩)
      (w : L ⧸ aschbacherSolvableCore 3 L) = (w : L ⧸ aschbacherSolvableCore 3 L)
    rw [Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    change c * (w : G) * c⁻¹ = w
    have hw : (w : G) * c = c * w :=
      Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_config h w.2)
    rw [← hw, mul_inv_cancel_right]

theorem autHom_not_inner_of_not_mem (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d)
    (hT : A ∉ partTwoT G) {y : G} (hyA : y ∈ A)
    (hyB : y ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (hyN : y ∈ Subgroup.normalizer (L : Set G)) :
    ¬ KFacts.IsInnerAut (autHom L ⟨y, hyN⟩) := by
  intro hin
  have hAe := h.mem_partTwoF.1
  have : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe
  set N := Subgroup.normalizer (L : Set G) with hN
  set I : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
    (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* _).range with hI
  set K : Subgroup G := (I.comap (autHom L)).map N.subtype with hK
  have hCL := centralizer_le_normalizer_of_config h45 h hT
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c h.mem_A)
  have hmemK : ∀ x (hx : x ∈ N), autHom L ⟨x, hx⟩ ∈ I → x ∈ K := fun x hx hi =>
    ⟨⟨x, hx⟩, hi, rfl⟩
  have hcN : c ∈ N := hCL (hAC h.mem_A)
  have hdN : d ∈ N := hCL (hAC h.d_mem)
  have hcK : c ∈ K := hmemK c hcN (by rw [autHom_c_eq_one h hcN]; exact I.one_mem)
  have hdK : d ∈ K := hmemK d hdN (by rw [autHom_of_mem hdN (d_mem_L h)]; exact ⟨_, rfl⟩)
  have hyK : y ∈ K := hmemK y hyN hin
  have hyc : y ∉ Subgroup.zpowers c := fun hyc => hyB (Subgroup.mem_sup_left hyc)
  have hA' := zpowers_sup_sup_eq h.card_eq h.mem_A h.ne_one h.d_mem h.not_mem_zpowers hyA hyB
  have haK : a ∈ K := by
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers y ≤ K :=
      sup_le (sup_le (Subgroup.zpowers_le.mpr hcK) (Subgroup.zpowers_le.mpr hdK))
        (Subgroup.zpowers_le.mpr hyK)
    rw [hA'] at hle
    exact hle h.a_mem
  obtain ⟨⟨a', ha'N⟩, ha'I, ha'eq⟩ := haK
  have ha'a : a' = a := ha'eq
  subst ha'a
  have hout : Sec4.InducesOuterTheta a' L := by
    rcases h.inducesStdKind with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta L h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L h' (by decide)
  obtain ⟨hx, hnot⟩ := hout
  exact hnot ha'I

theorem pCore_d_le_theta (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d)
    (hT : A ∉ partTwoT G) {m : ℕ} (hm : 2 ≤ m)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.RankThreeEven.projSL 2
      (GaloisField 2 (3 * m))) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({d} : Set G)) ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set P := inSubgroup (CFSG.pCore 2) (C ⊓ Subgroup.centralizer ({d} : Set G)) with hP
  have hLC := le_centralizer_of_config h
  have hCL := centralizer_le_normalizer_of_config h45 h hT
  have hdL := d_mem_L h
  have hd3 : d ^ 3 = 1 := h.mem_partTwoF.1.2 d h.d_mem
  have hPC : P ≤ C ⊓ Subgroup.centralizer ({d} : Set G) := SteinbergBY.inSubgroup_pCore_le 2 _
  have hP2 : IsPGroup 2 P := SteinbergBY.isPGroup_inSubgroup_pCore 2 _
  have hPN : P ≤ Subgroup.normalizer (L : Set G) := (hPC.trans inf_le_left).trans hCL
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hCL (hLC hdL)
  have hψ1 : ∀ q (hq : q ∈ P), autHom L ⟨q, hPN hq⟩ = 1 := fun q hq =>
    autHom_eq_one_of_component hm e hdN hd3 (autHom_d_ne_one h e hdN) hP2 hPN
      (hPC.trans inf_le_right)
      (fun z hz hzd => SteinbergBY.le_normalizer_inSubgroup_pCore 2 _
        ⟨hLC hz, Subgroup.mem_centralizer_singleton_iff.mpr hzd.symm⟩) hq
  refine le_theta_of_commutator_mem hLC hCL hdL hd3 hP2 hPC
    (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _) ?_
  intro q hq l hl
  exact theta_L_le h45 h hT (commutator_mem_theta_of_autHom_eq_one (hPN hq) (hψ1 q hq) hl)

theorem commutator_le_theta_of_not_mem (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d)
    (hT : A ∉ partTwoT G) {m : ℕ} (hm : 2 ≤ m)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.RankThreeEven.projSL 2
      (GaloisField 2 (3 * m))) {y : G} (hyA : y ∈ A)
    (hyB : y ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d) :
    ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)), A⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  have hAe := h.mem_partTwoF.1
  have : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set N := Subgroup.normalizer (L : Set G) with hN
  set P := inSubgroup (CFSG.pCore 2) (C ⊓ Subgroup.centralizer ({y} : Set G)) with hP
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hLC := le_centralizer_of_config h
  have hCL := centralizer_le_normalizer_of_config h45 h hT
  have hdL := d_mem_L h
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hAC : A ≤ C := fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c h.mem_A)
  have hPC : P ≤ C ⊓ Subgroup.centralizer ({y} : Set G) := SteinbergBY.inSubgroup_pCore_le 2 _
  have hP2 : IsPGroup 2 P := SteinbergBY.isPGroup_inSubgroup_pCore 2 _
  have hPN : P ≤ N := (hPC.trans inf_le_left).trans hCL
  have hyN : y ∈ N := hCL (hAC hyA)
  have hy3 : y ^ 3 = 1 := hAe.2 y hyA
  have hy1 : autHom L ⟨y, hyN⟩ ≠ 1 := fun h1 =>
    autHom_not_inner_of_not_mem h45 h hT hyA hyB hyN (by rw [h1]; exact Subgroup.one_mem _)
  have hψ1 : ∀ q (hq : q ∈ P), autHom L ⟨q, hPN hq⟩ = 1 := fun q hq =>
    autHom_eq_one_of_component hm e hyN hy3 hy1 hP2 hPN (hPC.trans inf_le_right)
      (fun z hz hzy => SteinbergBY.le_normalizer_inSubgroup_pCore 2 _
        ⟨hLC hz, Subgroup.mem_centralizer_singleton_iff.mpr hzy.symm⟩) hq
  have hyc : y ∉ Subgroup.zpowers c := fun hyc => hyB (Subgroup.mem_sup_left hyc)
  have hdE : d ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers y := by
    intro hd
    have hplane := zpowers_sup_eq_of_mem h.card_eq h.mem_A h.ne_one hyA hyc h.d_mem
      h.not_mem_zpowers hd
    exact hyB (hplane ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hA' := zpowers_sup_sup_eq h.card_eq h.mem_A h.ne_one hyA hyc h.d_mem hdE
  have hNθ : N ≤ Subgroup.normalizer (θL : Set G) := Sec6.normalizer_le_normalizer_theta L
  rw [Subgroup.commutator_le]
  intro q hq x hx
  let T : Subgroup G :=
    { carrier := {x | x ∈ N ∧ q * x * q⁻¹ * x⁻¹ ∈ θL}
      mul_mem' := by
        rintro x₁ x₂ ⟨h₁N, h₁⟩ ⟨h₂N, h₂⟩
        refine ⟨N.mul_mem h₁N h₂N, ?_⟩
        have e₁ : q * (x₁ * x₂) * q⁻¹ * (x₁ * x₂)⁻¹ =
            (q * x₁ * q⁻¹ * x₁⁻¹) * (x₁ * (q * x₂ * q⁻¹ * x₂⁻¹) * x₁⁻¹) := by group
        rw [e₁]
        exact θL.mul_mem h₁ ((Subgroup.mem_normalizer_iff.mp (hNθ h₁N) _).mp h₂)
      one_mem' := ⟨N.one_mem, by simp⟩
      inv_mem' := by
        rintro x₁ ⟨h₁N, h₁⟩
        refine ⟨N.inv_mem h₁N, ?_⟩
        have e₁ : q * x₁⁻¹ * q⁻¹ * x₁⁻¹⁻¹ = x₁⁻¹ * (q * x₁ * q⁻¹ * x₁⁻¹)⁻¹ * x₁⁻¹⁻¹ := by group
        rw [e₁]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hNθ h₁N)) _).mp
          (θL.inv_mem h₁) }
  have hqC : q ∈ C := (hPC hq).1
  have hqy : q * y = y * q := Subgroup.mem_centralizer_singleton_iff.mp (hPC hq).2
  have hcT : c ∈ T := by
    refine ⟨hCL (hAC h.mem_A), ?_⟩
    have hqc : q * c = c * q := Subgroup.mem_centralizer_singleton_iff.mp hqC
    rw [hqc, mul_inv_cancel_right, mul_inv_cancel]
    exact θL.one_mem
  have hyT : y ∈ T := by
    refine ⟨hyN, ?_⟩
    rw [hqy, mul_inv_cancel_right, mul_inv_cancel]
    exact θL.one_mem
  have hdT : d ∈ T :=
    ⟨hCL (hAC h.d_mem), commutator_mem_theta_of_autHom_eq_one (hPN hq) (hψ1 q hq) hdL⟩
  have hAT : A ≤ T := by
    rw [← hA']
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr hcT) (Subgroup.zpowers_le.mpr hyT))
      (Subgroup.zpowers_le.mpr hdT)
  rw [commutatorElement_def]
  exact theta_L_le h45 h hT (hAT hx).2

end TwoStarProof

open TwoStarProof in
theorem twoStarAtC_of_lf (h45 : Sec4.Item4_5) (hLF : LFAtC) : TwoStarAtC := by
  intro G _ _ A c L a R Y d h hT m hm hL2
  obtain ⟨e⟩ := hL2
  have hm2 : 2 ≤ m := hm
  have hLFc := hLF G A c L a R Y d h hT m hm ⟨e⟩
  have hAe := h.mem_partTwoF.1
  have : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe
  have h27 : Nat.card A = 3 ^ 3 := by rw [h.card_eq]; norm_num
  have hdA := h.d_mem
  have hdL := d_mem_L h
  have hclle : ∀ H : Subgroup G, c ∈ H → d ∈ H → a ∈ H → A ≤ H := by
    intro H hc hd ha
    rw [← h.closure_eq, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hc
    · exact hd
    · exact ha
  have hd1 : d ≠ 1 := fun h1 => h.not_mem_zpowers (h1 ▸ Subgroup.one_mem _)
  have hcd9 := SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 h.mem_A h.ne_one hdA
    h.not_mem_zpowers
  have had : a ∉ Subgroup.zpowers d := by
    intro had
    have hle := hclle (Subgroup.zpowers c ⊔ Subgroup.zpowers d) (Subgroup.mem_sup_left
      (Subgroup.mem_zpowers c)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
      (Subgroup.mem_sup_right had)
    have := Subgroup.card_le_of_le hle
    rw [h.card_eq, hcd9] at this
    norm_num at this
  have hV9 := SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 hdA hd1 h.a_mem had
  have hVA : Subgroup.zpowers d ⊔ Subgroup.zpowers a ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hdA) (Subgroup.zpowers_le.mpr h.a_mem)
  have hcV : c ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers a := by
    intro hc
    have hle := hclle _ hc (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    have := Subgroup.card_le_of_le hle
    rw [h.card_eq, hV9] at this
    norm_num at this
  refine twoStarConditionAt_of_theta hAe h.card_eq h.mem_A h.ne_one (by rw [hV9]; norm_num)
    hVA hcV hdA h.not_mem_zpowers ?_ ?_ ?_
  ·
    intro v hv
    have := hLFc (Subgroup.commutator_mem_commutator hdL hv)
    rwa [commutatorElement_def] at this
  ·
    intro y hyA hyc
    by_cases hyB : y ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d
    · have hplane := zpowers_sup_eq_of_mem h.card_eq h.mem_A h.ne_one hdA h.not_mem_zpowers
        hyA hyc hyB
      have hCy : Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) =
          Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) := by
        rw [← CFSG.RankThreeEvenClassification.Helpers.centralizer_join_zpowers,
          ← CFSG.RankThreeEvenClassification.Helpers.centralizer_join_zpowers, hplane]
      rw [hCy]
      have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
        congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
      have hAN : A ≤ Subgroup.normalizer ((inSubgroup (CFSG.pCore 2)
          (Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({d} : Set G))) :
            Set G) := fun u hu => SteinbergBY.le_normalizer_inSubgroup_pCore 2 _
          ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c h.mem_A),
            Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu d hdA)⟩
      exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hAN).trans
        (pCore_d_le_theta h45 h hT hm2 e)
    · exact commutator_le_theta_of_not_mem h45 h hT hm2 e hyA hyB
  ·
    intro u hu
    exact pCore_d_le_theta h45 h hT hm2 e (hu d hdA h.not_mem_zpowers)

end Certified

end CFSG.RankThree.PartTwo.Sec11
