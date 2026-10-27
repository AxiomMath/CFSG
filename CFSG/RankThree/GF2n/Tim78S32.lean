module

public import CFSG.RankThree.GF2n.Tim78P215
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Tim78Normal
public import CFSG.RankThree.GF2n.Tim78S31Steps

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def SigmaComm (V : Subgroup G) : Prop :=
  ∀ R : Subgroup G, IsPGroup 2 R → ∀ g h : G, conjSubgroup g V ≤ R → conjSubgroup h V ≤ R →
    ∀ a ∈ conjSubgroup g V, ∀ b ∈ conjSubgroup h V, a * b = b * a

omit [Finite G] in
theorem sigmaComm_of_elem {V : Subgroup G}
    (h : ∀ R : Subgroup G, IsPGroup 2 R → Assembly.IsElemAbelian 2
      (⨆ g : {g : G // conjSubgroup g V ≤ R}, conjSubgroup (g : G) V)) : SigmaComm V := by
  intro R hR g k hg hk a ha b hb
  have hE := h R hR
  have ha' : a ∈ ⨆ g : {g : G // conjSubgroup g V ≤ R}, conjSubgroup (g : G) V :=
    Subgroup.mem_iSup_of_mem ⟨g, hg⟩ ha
  have hb' : b ∈ ⨆ g : {g : G // conjSubgroup g V ≤ R}, conjSubgroup (g : G) V :=
    Subgroup.mem_iSup_of_mem ⟨k, hk⟩ hb
  exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha'⟩ ⟨b, hb'⟩)

theorem card_omegaOne_le_two_of_isCyclic {C : Subgroup G}
    (hCc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hcyc : IsCyclic C) :
    Nat.card ↥(PartTwo.omegaOneSub C) ≤ 2 := by
  classical
  let _ := Fintype.ofFinite ↥C
  have h1 := IsCyclic.card_pow_eq_one_le (α := ↥C) (n := 2) (by norm_num)
  have hinj : Function.Injective (fun z : ↥(PartTwo.omegaOneSub C) =>
      (⟨⟨z, PartTwo.omegaOneSub_le C z.2⟩, Subtype.ext (by
        rw [Subgroup.coe_pow, sq]
        exact ((mem_omegaOneSub_iff hCc).mp z.2).2)⟩ : {a : ↥C // a ^ 2 = 1})) := by
    intro z z' h
    exact Subtype.ext (congrArg (fun w : {a : ↥C // a ^ 2 = 1} => ((w : ↥C) : G)) h)
  calc Nat.card ↥(PartTwo.omegaOneSub C) ≤ Nat.card {a : ↥C // a ^ 2 = 1} :=
        Nat.card_le_card_of_injective _ hinj
    _ = (Finset.univ.filter fun a : ↥C => a ^ 2 = 1).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 2 := h1

structure S3Hyp (M U : Subgroup G) : Prop where
  max : IsMaximalTwoLocal M
  fstar : generalizedFitting M = pCore 2 M
  le : U ≤ M
  normal : M ≤ Subgroup.normalizer (U : Set G)
  comm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x
  two : IsPGroup 2 U
  ti : IsTI U
  exp : ∀ x ∈ U, x ^ 4 = 1
  ne : PartTwo.omegaOneSub U ≠ U
  card4 : 4 ≤ Nat.card ↥(PartTwo.omegaOneSub U)

namespace S3Hyp

variable {M U : Subgroup G} (H : S3Hyp M U)
include H

omit [Finite G] in
theorem omega_ne_bot : PartTwo.omegaOneSub U ≠ ⊥ := fun h => by
  have := H.card4
  rw [h, Subgroup.card_bot] at this
  omega

omit [Finite G] in
theorem normalizer_eq_of {D : Subgroup G} (hD1 : D ≠ ⊥) (hD2 : IsPGroup 2 D)
    (hMD : M ≤ Subgroup.normalizer (D : Set G)) : Subgroup.normalizer (D : Set G) = M := by
  by_contra hne
  exact H.max.2 _ (lt_of_le_of_ne hMD (Ne.symm hne)) ⟨D, hD1, hD2, rfl⟩

omit [Finite G] in
theorem le_normalizer_omega : M ≤ Subgroup.normalizer (PartTwo.omegaOneSub U : Set G) := by
  intro m hm
  rw [← conjSubgroup_eq_self_iff, ← omegaOneSub_conj H.comm m,
    conjSubgroup_eq_self_iff.mpr (H.normal hm)]

omit [Finite G] in
theorem normalizer_omega_eq : Subgroup.normalizer (PartTwo.omegaOneSub U : Set G) = M :=
  H.normalizer_eq_of H.omega_ne_bot (H.two.to_le (PartTwo.omegaOneSub_le U))
    H.le_normalizer_omega

omit [Finite G] in
theorem normalizer_U_eq : Subgroup.normalizer (U : Set G) = M := by
  have hU1 : U ≠ ⊥ := by
    intro h
    apply H.omega_ne_bot
    rw [eq_bot_iff, ← h]
    exact PartTwo.omegaOneSub_le U
  exact H.normalizer_eq_of hU1 H.two H.normal

omit [Finite G] in
theorem omega_conj_ne (g : G) :
    PartTwo.omegaOneSub (conjSubgroup g U) ≠ conjSubgroup g U := by
  intro h
  apply H.ne
  rw [omegaOneSub_conj H.comm] at h
  ext x
  constructor
  · exact fun hx => PartTwo.omegaOneSub_le U hx
  · intro hx
    have : g * x * g⁻¹ ∈ conjSubgroup g U := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hx
    rw [← h, mem_conjSubgroup, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
    exact this

theorem not_isCyclic_conj (g : G) : ¬ IsCyclic (conjSubgroup g U) := by
  intro hcyc
  have h1 := card_omegaOne_le_two_of_isCyclic (Tim78.comm_conj H.comm g) hcyc
  rw [omegaOneSub_conj H.comm, card_conjSubgroup] at h1
  have := H.card4
  omega

theorem comm_of_le (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hS : SigmaComm (PartTwo.omegaOneSub U)) {g : G} (hgM : conjSubgroup g U ≤ M) {h : G}
    (hhM : conjSubgroup h (PartTwo.omegaOneSub U) ≤ M) :
    ∀ a ∈ conjSubgroup h (PartTwo.omegaOneSub U),
      ∀ c ∈ conjSubgroup g (PartTwo.omegaOneSub U), a * c = c * a := by
  have hCc := Tim78.comm_conj H.comm g
  have hC2 : IsPGroup 2 (conjSubgroup g U) := H.two.map (MulAut.conj g).toMonoidHom
  have hCTI := isTI_conjSubgroup H.ti g
  rcases tim78_2_15 hCen hU H.fstar hgM hCc hC2 (fun k _ => hCTI k) with h1 | h2 | ⟨-, hW⟩
  · exact absurd h1 (H.omega_conj_ne g)
  · exact absurd h2 (H.not_isCyclic_conj g)
  · rw [omegaOneSub_conj H.comm] at hW
    set W := ⨆ (k : G) (_ : k ∈ M), conjSubgroup k (conjSubgroup g (PartTwo.omegaOneSub U))
      with hWdef
    have hMW : M ≤ Subgroup.normalizer (W : Set G) := by
      have e : W = ⨆ k : ↥M, conjSubgroup (k : G) (conjSubgroup g (PartTwo.omegaOneSub U)) := by
        rw [hWdef, iSup_subtype']
      rw [e]
      exact le_normalizer_iSup
    have hW2 : IsPGroup 2 W := fun w =>
      ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hW.2 w w.2)⟩
    have hA2 : IsPGroup 2 (conjSubgroup h (PartTwo.omegaOneSub U)) :=
      (H.two.to_le (PartTwo.omegaOneSub_le U)).map (MulAut.conj h).toMonoidHom
    have hR := IsPGroup.to_sup_of_normal_right' hA2 hW2 (le_trans hhM hMW)
    have hCW : conjSubgroup g (PartTwo.omegaOneSub U) ≤ W := by
      intro c hc
      refine Subgroup.mem_iSup_of_mem (1 : G) (Subgroup.mem_iSup_of_mem M.one_mem ?_)
      rw [conjSubgroup_one]
      exact hc
    exact hS _ hR h g le_sup_left (le_trans hCW le_sup_right)

theorem mem_of_comm {g : G}
    (hcomm : ∀ h : G, conjSubgroup h (PartTwo.omegaOneSub U) ≤ M →
      ∀ a ∈ conjSubgroup h (PartTwo.omegaOneSub U),
        ∀ c ∈ conjSubgroup g (PartTwo.omegaOneSub U), a * c = c * a)
    (hcomm1 : ∀ h : G, conjSubgroup h (PartTwo.omegaOneSub U) ≤ M →
      ∀ a ∈ conjSubgroup h (PartTwo.omegaOneSub U),
        ∀ c ∈ PartTwo.omegaOneSub U, a * c = c * a) : g ∈ M := by
  classical
  set V := PartTwo.omegaOneSub U with hVdef
  have : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  set Sg : Set (Subgroup G) := {D | (∃ k : G, D = conjSubgroup k V) ∧ D ≤ M} with hSg
  have hstep : ∀ D ∈ Sg, conjSubgroup g⁻¹ D ∈ Sg := by
    rintro D ⟨⟨k, rfl⟩, hDM⟩
    refine ⟨⟨g⁻¹ * k, (conjSubgroup_mul _ _ _).symm⟩, fun z hz => ?_⟩
    rw [mem_conjSubgroup, inv_inv] at hz
    have hc := hcomm k hDM _ hz
    have hN : g * z * g⁻¹ ∈ Subgroup.normalizer (conjSubgroup g V : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
        fun c hc' => (hc c hc').symm)
    have hz' : z ∈ Subgroup.normalizer (V : Set G) := by
      rw [← conjSubgroup_eq_self_iff] at hN ⊢
      calc conjSubgroup z V = conjSubgroup g⁻¹ (conjSubgroup (g * z * g⁻¹)
          (conjSubgroup g V)) := by
            rw [← conjSubgroup_mul, ← conjSubgroup_mul]
            congr 1
            group
        _ = V := by rw [hN, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    rw [← H.normalizer_omega_eq]
    exact hz'
  let f : ↥Sg → ↥Sg := fun D => ⟨conjSubgroup g⁻¹ D, hstep D D.2⟩
  have hf : Function.Injective f := by
    intro D D' h
    have h1 : conjSubgroup g⁻¹ (D : Subgroup G) = conjSubgroup g⁻¹ D' := congrArg Subtype.val h
    have h2 := congrArg (conjSubgroup g) h1
    rw [← conjSubgroup_mul, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one,
      conjSubgroup_one] at h2
    exact Subtype.ext h2
  have hsurj := Finite.injective_iff_surjective.mp hf
  have hstep' : ∀ D ∈ Sg, conjSubgroup g D ∈ Sg := fun D hD => by
    obtain ⟨⟨D', hD'⟩, he⟩ := hsurj ⟨D, hD⟩
    have e : conjSubgroup g⁻¹ D' = D := congrArg Subtype.val he
    rw [← e, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    exact hD'
  set R := ⨆ D : ↥Sg, (D : Subgroup G) with hRdef
  have hnormR : ∀ x : G, (∀ D ∈ Sg, conjSubgroup x D ∈ Sg) →
      x ∈ Subgroup.normalizer (R : Set G) := by
    intro x hx
    rw [← conjSubgroup_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_conjSubgroup])
    rw [conjSubgroup, Subgroup.map_le_iff_le_comap]
    refine iSup_le fun D => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup (fun D : ↥Sg => (D : Subgroup G)) ⟨_, hx D D.2⟩
  have hgR : g ∈ Subgroup.normalizer (R : Set G) := hnormR g hstep'
  have hMR : M ≤ Subgroup.normalizer (R : Set G) := fun m hm => hnormR m fun D hD => by
    obtain ⟨⟨k, rfl⟩, hDM⟩ := hD
    refine ⟨⟨m * k, (conjSubgroup_mul _ _ _).symm⟩, fun z hz => ?_⟩
    rw [mem_conjSubgroup] at hz
    rw [show z = m * (m⁻¹ * z * m) * m⁻¹ by group]
    exact M.mul_mem (M.mul_mem hm (hDM hz)) (M.inv_mem hm)
  have hVSg : V ∈ Sg := ⟨⟨1, (conjSubgroup_one V).symm⟩,
    le_trans (PartTwo.omegaOneSub_le U) H.le⟩
  have hVR : V ≤ R := le_iSup (fun D : ↥Sg => (D : Subgroup G)) ⟨V, hVSg⟩
  have hRV : R ≤ Subgroup.normalizer (V : Set G) := by
    refine iSup_le fun D => ?_
    obtain ⟨⟨k, hk⟩, hDM⟩ := D.2
    intro d hd
    refine Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun c hc => ?_)
    rw [hk] at hd hDM
    exact (hcomm1 k hDM d hd c hc).symm
  have hVO : V ≤ inSubgroup (pCore 2) R :=
    le_inSubgroup_pCore hVR hRV (H.two.to_le (PartTwo.omegaOneSub_le U))
  have hO1 : inSubgroup (pCore 2) R ≠ ⊥ := fun h => H.omega_ne_bot (by
    rw [eq_bot_iff, ← h]
    exact hVO)
  have hMO : M ≤ Subgroup.normalizer ((inSubgroup (pCore 2) R : Subgroup G) : Set G) :=
    fun m hm => mem_normalizer_map_subtype_of_characteristic (hMR hm) (pCore 2 R)
  have hNO := H.normalizer_eq_of hO1 (inSubgroup_pCore_two R).1 hMO
  rw [← hNO]
  exact mem_normalizer_map_subtype_of_characteristic hgR (pCore 2 R)

theorem weaklyClosed (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hS : SigmaComm (PartTwo.omegaOneSub U)) {g : G}
    (hg : conjSubgroup g U ≤ Subgroup.centralizer (U : Set G)) : conjSubgroup g U = U := by
  have hgM : conjSubgroup g U ≤ M := by
    rw [← H.normalizer_U_eq]
    exact le_trans hg (Subgroup.centralizer_le_normalizer (U : Set G))
  have h1M : conjSubgroup 1 U ≤ M := by
    rw [conjSubgroup_one]
    exact H.le
  have hmem := H.mem_of_comm (g := g) (fun h hh => H.comm_of_le hCen hU hS hgM hh)
    (fun h hh a ha c hc => H.comm_of_le hCen hU hS h1M hh a ha c (by
      rw [conjSubgroup_one]; exact hc))
  exact conjSubgroup_eq_self_iff.mpr (H.normal hmem)

theorem stronglyClosed (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hS : SigmaComm (PartTwo.omegaOneSub U)) {b g : G} (hb : b ∈ U)
    (hbg : g * b * g⁻¹ ∈ Subgroup.centralizer (U : Set G)) : g * b * g⁻¹ ∈ U := by
  by_cases hb1 : b = 1
  · rw [hb1, mul_one, mul_inv_cancel]
    exact U.one_mem
  have hb' : g * b * g⁻¹ ∈ conjSubgroup g U := by
    rw [mem_conjSubgroup, show g⁻¹ * (g * b * g⁻¹) * g = b by group]
    exact hb
  have hb'1 : g * b * g⁻¹ ≠ 1 := fun h => hb1 (by
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  have hCTI := isTI_conjSubgroup H.ti g
  have hle : conjSubgroup g⁻¹ (conjSubgroup g U) ≤
      Subgroup.normalizer (conjSubgroup g U : Set G) := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    intro x hx
    exact Tim77.mem_normalizer_of_commute_of_isTI hCTI hb' hb'1
      (Subgroup.mem_centralizer_iff.mp hbg x hx)
  have hC1 : conjSubgroup g U ≠ ⊥ := fun h => hb'1 (by
    rw [h, Subgroup.mem_bot] at hb'
    exact hb')
  have hcomm := commute_of_le_normalizer (Tim78.comm_conj H.comm g)
    (H.two.map (MulAut.conj g).toMonoidHom) hC1 hCTI hle
  have hCU : conjSubgroup g U ≤ Subgroup.centralizer (U : Set G) := fun c hc =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => (hcomm c hc u (by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
      exact hu)).symm
  rw [← H.weaklyClosed hCen hU hS hCU]
  exact hb'

end S3Hyp

end CFSG.RankThree.GF2n.Tim78
