module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Alpha
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Shape
import CFSG.LocalAnalysis.WeakClosure81.W183Br1ShapeAux1
import CFSG.LocalAnalysis.WeakClosure81.W18T189FourBridge
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Goldschmidt.Steps.G63Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt Bar2 CoverOf)
open CFSG.Blueprint (LieModel)

private theorem w183_exists_mul_ne_of_isU3_two {X : Type} [Group X] (h : IsU3 X 2) :
    ∃ a b : X, a * b ≠ b * a := by
  have hst : CFSG.Open.StatedClassicalModel X .PSU 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have hcard : Nat.card X = 62400 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_four hst
  have hsimple : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  by_contra hnab
  have hcomm : IsMulCommutative X := IsMulCommutative.of_comm (fun a b => by
    by_contra hab
    exact hnab ⟨a, b, hab⟩)
  letI : IsMulCommutative X := hcomm
  have hp : (Nat.card X).Prime := CommGroup.is_simple_iff_prime_card.mp hsimple
  rw [hcard] at hp
  norm_num at hp

private theorem w183_quasisimple_of_simple {X : Type} [Group X]
    (hs : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple X := by
  have hcenter : Subgroup.center X = ⊥ := w183_center_eq_bot_of_simple hs hnab
  refine ⟨?_, ?_⟩
  · rcases hs.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      haveI := (commutator_eq_bot_iff X).mp h
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (mul_comm a b)
    · exact h
  · have e : X ⧸ Subgroup.center X ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup

private theorem w183_component_cover_of_simple {W : Type} [Group W] {Y L : Subgroup W}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hsimple : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) :
    CFSG.Open.IsComponentOf (L.subgroupOf Y) ⊤ ∧ CoverOf ↥(L.subgroupOf Y) ↥L := by
  haveI := hsimple
  have hqL : CFSG.Open.IsQuasisimple ↥L := w183_quasisimple_of_simple hsimple hnab
  have hqL' : CFSG.Open.IsQuasisimple ↥(L.subgroupOf Y) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY) hqL
  have hsimpleL' : IsSimpleGroup ↥(L.subgroupOf Y) :=
    (Subgroup.subgroupOfEquivOfLe hLY).isSimpleGroup
  have hnabL' : ∃ a b : ↥(L.subgroupOf Y), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨(Subgroup.subgroupOfEquivOfLe hLY).symm a,
      (Subgroup.subgroupOfEquivOfLe hLY).symm b, ?_⟩
    intro h
    exact hab (by simpa using congrArg (Subgroup.subgroupOfEquivOfLe hLY) h)
  have hcenterL' : Subgroup.center ↥(L.subgroupOf Y) = ⊥ :=
    w183_center_eq_bot_of_simple hsimpleL' hnabL'
  refine ⟨⟨le_top, ?_, hqL'⟩, hqL', ⟨?_⟩⟩
  · exact CFSG.Open.IsSubnormal.step le_top (hLn.subgroupOf ⊤)
      (CFSG.Open.IsSubnormal.refl ⊤)
  · exact ((QuotientGroup.quotientMulEquivOfEq hcenterL').trans
      QuotientGroup.quotientBot).trans (Subgroup.subgroupOfEquivOfLe hLY)

private theorem w183_exists_card_four_le_of_mem {X : Type} [Group X] [Finite X]
    {D : Subgroup X} (hel : IsElemAbelian 2 D) (h8 : 8 ≤ Nat.card D) {d : X} (hd : d ∈ D) :
    ∃ A : Subgroup X, A ≤ D ∧ Nat.card A = 4 ∧ d ∈ A := by
  by_cases hd1 : d = 1
  · obtain ⟨B, hBD, hB4⟩ := exists_subgroup_card_four (A := D) hel.isPGroup (by omega)
    exact ⟨B, hBD, hB4, by rw [hd1]; exact B.one_mem⟩
  · have hd2 : d ^ 2 = 1 := hel.2 d hd
    have hcardd : Nat.card (Subgroup.zpowers d) = 2 := by
      rw [Nat.card_zpowers]
      have hdvd : orderOf d ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hd2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hd1
      · exact h
    have hnotle : ¬ D ≤ Subgroup.zpowers d := by
      intro hle
      have hle2 := Subgroup.card_le_of_le hle
      rw [hcardd] at hle2
      omega
    have hnotle' : ¬ (D : Set X) ⊆ (Subgroup.zpowers d : Set X) := fun hle => hnotle hle
    obtain ⟨e, heD, henot⟩ := Set.not_subset.mp hnotle'
    have he1 : e ≠ 1 := fun h => henot (by rw [h]; exact Subgroup.one_mem _)
    have he2 : e ^ 2 = 1 := hel.2 e heD
    have hcomm : e * d = d * e := hel.comm heD hd
    obtain ⟨-, hcardA⟩ :=
      CFSG.Goldschmidt.G63.sup_zpowers_isElemAbelian (p := 2) Nat.prime_two he2 hd2 hd1
        henot hcomm
    exact ⟨Subgroup.zpowers e ⊔ Subgroup.zpowers d,
      sup_le (Subgroup.zpowers_le.mpr heD) (Subgroup.zpowers_le.mpr hd),
      by rw [hcardA]; norm_num,
      Subgroup.mem_sup_right (Subgroup.mem_zpowers d)⟩

@[expose] def FinRk2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal →
    Subgroup.centralizer (L : Set Y) = ⊥ → (IsL2 ↥L 2 ∨ IsL3 ↥L 1) →
      ∀ A : Subgroup Y, IsElemAbelian 2 A → Nat.card A ≤ 4

@[expose] def FinRkU34 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsU3 L 2 → ∀ A : Subgroup L, IsElemAbelian 2 A →
    Nat.card A ≤ 4

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem br1_rank_false_one (hrk : FinRk2) (hU : FinRkU34) (h65f : Asch6_5Four)
    (h : Assumption131 Y Γ VA i) (hLY : L ≤ Y) (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1)
    (hshape : IsL2 ↥L 2 ∨ IsL3 ↥L 1 ∨ IsU3 ↥L 2) {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (h8 : 8 ≤ Nat.card ↥D) : False := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  have hDY : D ≤ Y := h.le_G D hD
  have hel : IsElemAbelian 2 D := h.isElemAb D hD
  obtain ⟨hN, hC⟩ := w183_restrict_normal_cent hLY hLn hcent
  rcases hshape with hL2 | hL3 | hU3
  · have hshape' : IsL2 ↥(L.subgroupOf Y) 2 ∨ IsL3 ↥(L.subgroupOf Y) 1 :=
      Or.inl (LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hL2)
    have hc := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDY).toEquiv
    have h4 := hrk ↥Y (L.subgroupOf Y) hN hC hshape' (D.subgroupOf Y) (hel.subgroupOf Y)
    rw [hc] at h4
    omega
  · have hshape' : IsL2 ↥(L.subgroupOf Y) 2 ∨ IsL3 ↥(L.subgroupOf Y) 1 :=
      Or.inr (LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hL3)
    have hc := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDY).toEquiv
    have h4 := hrk ↥Y (L.subgroupOf Y) hN hC hshape' (D.subgroupOf Y) (hel.subgroupOf Y)
    rw [hc] at h4
    omega
  · have hU3Y : IsU3 ↥(L.subgroupOf Y) 2 :=
      LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hU3
    have hsimple : IsSimpleGroup ↥L :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3
    have hnab : ∃ a b : ↥L, a * b ≠ b * a := w183_exists_mul_ne_of_isU3_two hU3
    have hcomp := w183_component_cover_of_simple hLY hN hsimple hnab
    have hsimple' : IsSimpleGroup ↥(L.subgroupOf Y) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3Y
    have hnab' : ∃ a b : ↥(L.subgroupOf Y), a * b ≠ b * a :=
      w183_exists_mul_ne_of_isU3_two hU3Y
    have hDL : D ≤ L := by
      intro d hd
      obtain ⟨A, hAD, hAcard, hdA⟩ := w183_exists_card_four_le_of_mem hel h8 hd
      have hAY : A ≤ Y := hAD.trans hDY
      have hcardA' : Nat.card ↥(A.subgroupOf Y) = 4 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv, hAcard]
      have helA' : IsElemAbelian 2 (A.subgroupOf Y) := (hel.mono hAD).subgroupOf Y
      have hqA : CFSG.Quasithin.G11.commSpace A
          (CFSG.SignalizerFunctorTheorem.Quadratic.commSub A) = ⊥ :=
        le_bot_iff.mp ((CFSG.Quasithin.G11.commSpace_mono hAD
          (CFSG.SignalizerFunctorTheorem.Quadratic.commSub_mono A D hAD)).trans
            (le_of_eq (h.quadratic D hD)))
      have hquadA : IsQuadraticOn (repOf Y) (A.subgroupOf Y) :=
        isQuadraticOn_lglRep (Y := Y) hqA
      have hAL' : A.subgroupOf Y ⊓
          Subgroup.centralizer ((L.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = ⊥ := by
        rw [hC]; exact inf_bot_eq _
      have hAnorm : A.subgroupOf Y ≤ Subgroup.normalizer (L.subgroupOf Y : Set ↥Y) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr hN]
        exact le_top
      have hodd : Odd (Nat.card ↥(Subgroup.center ↥(L.subgroupOf Y))) := by
        have hcenter : Subgroup.center ↥(L.subgroupOf Y) = ⊥ :=
          w183_center_eq_bot_of_simple hsimple' hnab'
        rw [hcenter, Subgroup.card_bot]
        norm_num
      have hinner := h65f ↥Y (Multiplicative V) (multiplicative_sq_eq_one (W := V)) (repOf Y)
        (repOf_injective Y) (L.subgroupOf Y) (A.subgroupOf Y) hcomp.1 hodd hAnorm hcardA'
        helA' hquadA hAL' (↥L) (inferInstance : Group ↥L) (Or.inr hU3) hcomp.2
      have hAL : A ≤ L := by
        intro a ha
        let aY : ↥Y := ⟨a, hAY ha⟩
        have haY : aY ∈ A.subgroupOf Y := Subgroup.mem_subgroupOf.mpr ha
        obtain ⟨l, hl, hdl⟩ := hinner aY haY
        have hcomm : ∀ l' ∈ L, ((aY * l⁻¹ : ↥Y) : LGL 2 V) * l' =
            l' * ((aY * l⁻¹ : ↥Y) : LGL 2 V) := by
          intro l' hl'
          have hl'' : (⟨l', hLY hl'⟩ : ↥Y) ∈ L.subgroupOf Y :=
            Subgroup.mem_subgroupOf.mpr hl'
          have h := (Subgroup.mem_centralizer_iff.mp hdl) _ hl''
          exact (congrArg (fun z : ↥Y => (z : LGL 2 V)) h).symm
        have hone : ((aY * l⁻¹ : ↥Y) : LGL 2 V) = 1 :=
          hcent _ (Y.mul_mem aY.2 (Y.inv_mem (hLY (Subgroup.mem_subgroupOf.mp hl)))) hcomm
        have haeq : a = (l : LGL 2 V) := by
          refine mul_inv_eq_one.mp ?_
          simpa using hone
        exact haeq ▸ Subgroup.mem_subgroupOf.mp hl
      exact hAL hdA
    have hcardL : Nat.card ↥(D.subgroupOf L) = Nat.card ↥D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
    have hle4 := hU ↥L hU3 (D.subgroupOf L) (hel.subgroupOf L)
    rw [hcardL] at hle4
    omega

theorem br1_rank_false_two (hrk : FinRk2) (htwo : Br2TwoComp Y T L₁ L₂)
    (hshape : IsL2 ↥L₁ 2 ∨ IsL3 ↥L₁ 1) {D : Subgroup (LGL 2 V)} (hDY : D ≤ Y)
    (hDn : D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V))) (hel : IsElemAbelian 2 D)
    (h3 : 3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)))) : False := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  haveI : Finite (alphaQuot Y L₁) := w183_alpha_finite Y L₁
  obtain ⟨hN, hC⟩ := w183_alpha_normal_cent htwo
  obtain ⟨e⟩ := w183_alpha_shape htwo
  have hshape' : IsL2 ↥(alphaL Y L₁) 2 ∨ IsL3 ↥(alphaL Y L₁) 1 := by
    rcases hshape with h | h
    · exact Or.inl (LieModel.of_mulEquiv e h)
    · exact Or.inr (LieModel.of_mulEquiv e h)
  have hDX : D ≤ alphaX Y L₁ := le_inf hDY hDn
  let inc : ↥D →* ↥(alphaX Y L₁) :=
    { toFun := fun d => ⟨d.1, hDX d.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  let φ : ↥D →* alphaQuot Y L₁ := (alphaMk Y L₁).comp inc
  have hker : φ.ker = (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))).subgroupOf D := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      have hx' : (⟨x.1, hDX x.2⟩ : ↥(alphaX Y L₁)) ∈
          (alphaC Y L₁).subgroupOf (alphaX Y L₁) :=
        (QuotientGroup.eq_one_iff (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁))
          ⟨x.1, hDX x.2⟩).mp hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx'
      exact ⟨x.2, hx'.2⟩
    · intro hx
      have hmem : (⟨x.1, hDX x.2⟩ : ↥(alphaX Y L₁)) ∈
          (alphaC Y L₁).subgroupOf (alphaX Y L₁) := by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨(hDX x.2).1, hx.2⟩
      exact (QuotientGroup.eq_one_iff (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁))
        ⟨x.1, hDX x.2⟩).mpr hmem
  have hrange : (D.subgroupOf (alphaX Y L₁)).map (alphaMk Y L₁) = φ.range := by
    ext y
    simp only [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
      exact congrArg (alphaMk Y L₁) (Subtype.ext rfl)
    · rintro ⟨d, rfl⟩
      exact ⟨⟨d.1, hDX d.2⟩, Subgroup.mem_subgroupOf.mpr d.2, rfl⟩
  have hcard : Nat.card ((D.subgroupOf (alphaX Y L₁)).map (alphaMk Y L₁))
      = 2 ^ mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) := by
    rw [hrange]
    have h1 : Nat.card φ.range = φ.ker.index := by
      rw [Subgroup.index_eq_card (H := φ.ker)]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
    rw [hker] at h1
    obtain ⟨n, hn⟩ := IsPGroup.index hel.isPGroup
      ((D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))).subgroupOf D)
    have hmOf : mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) = n := by
      unfold mOf
      rw [hn, Nat.log_pow (by norm_num : 1 < 2)]
    rw [hmOf]
    exact h1.trans hn
  have hge : 8 ≤ Nat.card ((D.subgroupOf (alphaX Y L₁)).map (alphaMk Y L₁)) := by
    rw [hcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) :=
          Nat.pow_le_pow_right (by norm_num) h3
  have hle4 := hrk (alphaQuot Y L₁) (alphaL Y L₁) hN hC hshape'
    ((D.subgroupOf (alphaX Y L₁)).map (alphaMk Y L₁))
    ((hel.subgroupOf (alphaX Y L₁)).map (alphaMk Y L₁))
  omega

end CFSG.LocalAnalysis.WeakClosure81

end
