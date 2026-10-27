module

public import CFSG.RankThree.PartTwo.Sec4.T444.Sec451
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.PartTwo.Sec4.T444.Lift
public import CFSG.RankThree.PartTwo.Sec4.T444.Statement

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

theorem not_three_dvd_orderOf_of_mem {Z : Type*} [Group Z] [Finite Z] {x : Z} {N : Subgroup Z}
    (hx : x ∈ N) (hN : ¬ 3 ∣ Nat.card N) : ¬ 3 ∣ orderOf x := fun h3x =>
  hN (h3x.trans (by rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _))

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G}

theorem not_map_le_map_of_not_le (h : Ctx444 G A M) {H L : Subgroup G} (hAH : A ≤ H)
    (hLH : L ≤ H) (hLM : ¬ L ≤ M) :
    ¬ (L.subgroupOf H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) ≤
      (M.subgroupOf H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) := by
  intro hle
  apply hLM
  set Θ : Subgroup G := (aschbacherSolvableCore 3 H).map H.subtype with hΘ
  have : (aschbacherSolvableCore 3 H).Characteristic := aschbacherSolvableCore_characteristic H
  have hAΘ : A ≤ Subgroup.normalizer (Θ : Set G) := hAH.trans (Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _))
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := by
    rw [hΘ, Subgroup.card_map_of_injective H.subtype_injective]
    exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hΘM : Θ ≤ M := h.le_of_le_normalizer hAΘ hΘ3
  intro l hl
  obtain ⟨m, hm, hme⟩ := hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl :
    (⟨l, hLH hl⟩ : H) ∈ L.subgroupOf H))
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hme
  have hmΘ : ((m⁻¹ * ⟨l, hLH hl⟩ : H) : G) ∈ M := hΘM ⟨_, hme, rfl⟩
  have hmM : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
  have : l = (m : G) * ((m⁻¹ * ⟨l, hLH hl⟩ : H) : G) := by simp
  rw [this]
  exact M.mul_mem hmM hmΘ

theorem nonempty_mulEquiv_map_sup {H L : Subgroup G} (hA : IsPGroup 3 A)
    (hL : L ∈ thetaComponents 3 G) (h3 : 3 ∣ Nat.card L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hAH : A ≤ H) (hLH : L ≤ H)
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) :
    Nonempty ((A ⊔ L).map (starQuot G) ≃*
      ((A ⊔ L).subgroupOf H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) := by
  set W := A ⊔ L with hW
  have hWH : W ≤ H := sup_le hAH hLH
  set f := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hf
  set ψ₁ : W →* G ⧸ CFSG.pPrimeCore 3 G := (starQuot G).comp W.subtype with hψ₁
  set ψ₂ : W →* H ⧸ aschbacherSolvableCore 3 H := f.comp (Subgroup.inclusion hWH) with hψ₂
  have hθL := inf_pPrimeCore_eq_of_mem_thetaComponents hL h3
  have hker₁ : ∀ w : W, ψ₁ w = 1 ↔ (w : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    intro w
    rw [hψ₁, MonoidHom.comp_apply, Subgroup.coe_subtype, starQuot, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ← hθL]
    constructor
    · intro hw
      exact ⟨mem_of_mem_sup_of_not_dvd hA hAL w.2
        (not_three_dvd_orderOf_of_mem hw not_three_dvd_card_pPrimeCore), hw⟩
    · exact fun hw => hw.2
  have hθH3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 H) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hLn : (L.subgroupOf H).Normal := ⟨fun y hy h => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHL h.2) _).mp hy⟩
  have hint := solvable_prime_complement_core_subnormal_intersection Nat.prime_three
    hLn.isSubnormal (G := H)
  set e := Subgroup.subgroupOfEquivOfLe hLH
  have hmap := aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  have hker₂ : ∀ w : W, ψ₂ w = 1 ↔ (w : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    intro w
    rw [hψ₂, MonoidHom.comp_apply, hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hw
      have hw3 : ¬ 3 ∣ orderOf (w : G) := by
        have h1 := not_three_dvd_orderOf_of_mem hw hθH3
        have h2 : orderOf (w : G) = orderOf (Subgroup.inclusion hWH w) :=
          Subgroup.orderOf_coe (Subgroup.inclusion hWH w)
        rwa [h2]
      have hwL : (w : G) ∈ L := mem_of_mem_sup_of_not_dvd hA hAL w.2 hw3
      have hmem : Subgroup.inclusion hWH w ∈ inSubgroup (aschbacherSolvableCore 3)
          (L.subgroupOf H) := by
        rw [hint]
        exact ⟨Subgroup.mem_subgroupOf.mpr hwL, hw⟩
      obtain ⟨t, ht, hte⟩ := hmem
      refine ⟨e t, hmap ▸ Subgroup.mem_map_of_mem _ ht, ?_⟩
      have hte' : ((t : L.subgroupOf H) : H) = Subgroup.inclusion hWH w := hte
      change (((t : L.subgroupOf H) : H) : G) = w
      rw [hte']
      rfl
    · rintro ⟨t, ht, hte⟩
      have ht' : e.symm t ∈ aschbacherSolvableCore 3 (L.subgroupOf H) := by
        have hmap' := aschbacherSolvableCore_map_mulEquiv Nat.prime_three e.symm
        exact hmap' ▸ Subgroup.mem_map_of_mem _ ht
      have hmem : Subgroup.inclusion hWH w ∈ inSubgroup (aschbacherSolvableCore 3)
          (L.subgroupOf H) := ⟨e.symm t, ht', Subtype.ext (by
            change ((t : L) : G) = w
            exact hte)⟩
      rw [hint] at hmem
      exact hmem.2
  have hk : ψ₁.ker = ψ₂.ker := by
    ext w
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker₁, hker₂]
  have hr₁ : ψ₁.range = W.map (starQuot G) := by
    rw [hψ₁, MonoidHom.range_comp, Subgroup.range_subtype]
  have hr₂ : ψ₂.range = (W.subgroupOf H).map f := by
    rw [hψ₂, MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr w.2
    · intro hx
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  exact ⟨((MulEquiv.subgroupCongr hr₁.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivRange ψ₂)))).trans (MulEquiv.subgroupCongr hr₂)⟩

theorem ctx434Core_quotient (h : Ctx444 G A M) {L R : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hLM : ¬ L ≤ M)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hR3 : ¬ 3 ∣ Nat.card R)
    (hs : Group.IsSolvable (A ⊔ R : Subgroup G))
    (hact : ¬ R.map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))) :
    Ctx434Core (↥(A ⊔ R ⊔ L) ⧸ aschbacherSolvableCore 3 ↥(A ⊔ R ⊔ L))
      ((A.subgroupOf (A ⊔ R ⊔ L)).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(A ⊔ R ⊔ L))))
      ((M.subgroupOf (A ⊔ R ⊔ L)).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(A ⊔ R ⊔ L))))
      ((R.subgroupOf (A ⊔ R ⊔ L)).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(A ⊔ R ⊔ L)))) := by
  set H := A ⊔ R ⊔ L with hH
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_sup_le hAL hRL
  have hAH : A ≤ H := le_sup_left.trans le_sup_left
  have hRH : R ≤ H := le_sup_right.trans le_sup_left
  have hLH : L ≤ H := le_sup_right
  have hLn : (L.subgroupOf H).Normal := ⟨fun y hy k => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHL k.2) _).mp hy⟩
  have hL' := mem_thetaComponents_subgroupOf_of_le_normalizer hL hLH hHL
  have hsolv := isSolvable_quotient_subgroupOf hAL hRL hs
  have hlayer := layer_quotient_eq_map hL' hsolv
  set f := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hf
  refine ⟨isE27_map_subgroupOf h.isE27 hAH, gamma_map_subgroupOf_le h.isE27 hAH h.gamma_le,
    (theta_quotient_core_and_ranks (G := H)).1,
    pRank_map_subgroupOf_eq h.isE27 hAH h.le h.pRank_eq,
    map_subgroupOf_mem_invariantPiSubgroups hR3 hRH hAR, ?_, ?_, ?_⟩
  ·
    intro hbot
    apply hact
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have hrθ : (⟨r, hRH hr⟩ : H) ∈ aschbacherSolvableCore 3 H :=
      hbot (Subgroup.mem_subgroupOf.mpr hr)
    have hc := commutator_mem_of_mem_aschbacherSolvableCore hL hLH hHL hrθ hl
    have hcP : r * l * r⁻¹ * l⁻¹ ∈ CFSG.pPrimeCore 3 G := by
      have hθ := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hL.2.1
      rw [hθ] at hc
      exact aschbacherSolvableCore_le_pPrimeCore hc.2
    have h1 : starQuot G (r * l * r⁻¹ * l⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hcP
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  · rw [hlayer]
    exact (isComponent_map_of_mem_thetaComponents Nat.prime_three hL').1
  · rw [hlayer]
    exact not_map_le_map_of_not_le h hAH hLH hLM

theorem isZ3L34OrHeisSL34_of_item4_34Sec (h434 : Item4_34Sec) (h : Ctx444 G A M)
    {L R : Subgroup G} (hL : L ∈ thetaComponents 3 G) (h3 : 3 ∣ Nat.card L) (hLM : ¬ L ≤ M)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hR3 : ¬ 3 ∣ Nat.card R)
    (hs : Group.IsSolvable (A ⊔ R : Subgroup G))
    (hact : ¬ R.map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))) :
    IsZ3L34OrHeisSL34 ((A ⊔ L).map (starQuot G)) := by
  set H := A ⊔ R ⊔ L with hH
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_sup_le hAL hRL
  have hAH : A ≤ H := le_sup_left.trans le_sup_left
  have hLH : L ≤ H := le_sup_right
  have hLn : (L.subgroupOf H).Normal := ⟨fun y hy k => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHL k.2) _).mp hy⟩
  have hL' := mem_thetaComponents_subgroupOf_of_le_normalizer hL hLH hHL
  have hlayer := layer_quotient_eq_map hL' (isSolvable_quotient_subgroupOf hAL hRL hs)
  set f := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hf
  have hcore := ctx434Core_quotient h hL hLM hAL hRL hAR hR3 hs hact
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    rw [hf, QuotientGroup.ker_mk']
    exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  obtain ⟨hZ, -, -⟩ := h434 G h.sectionFourHyp H _ f (QuotientGroup.mk'_surjective _) hker _ _ _
    hcore
  rw [hlayer, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hAH hLH] at hZ
  obtain ⟨e⟩ := nonempty_mulEquiv_map_sup h.isE27.isPGroup hL h3 hAL hAH hLH hHL
  exact IsZ3L34OrHeisSL34.of_mulEquiv e.symm hZ

end CFSG.RankThree.PartTwo.Sec4
