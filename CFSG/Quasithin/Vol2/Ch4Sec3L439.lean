module

public import CFSG.Quasithin.Vol2.Ch4Sec3Ut

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4

@[expose] def Lemma439Fix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CharTwo K →
      C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      Concl438 H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
        omegaOneCenterOf (T ⊓ H) ⊓ Subgroup.centralizer (L : Set G) ≤
          Subgroup.centralizer (K : Set G)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_centralizer_of_mem {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ c ∈ Subgroup.centralizer (X : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using this
    have h1 := hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * x := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨fun hc => key g hg c hc, fun hc => by
    simpa [mul_assoc] using key g⁻¹ (Subgroup.inv_mem _ hg) _ hc⟩

theorem exists_involution_center {S U : Subgroup G} (hS : IsPGroup 2 S) (hUS : U ≤ S)
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    ∃ x ∈ U, (∀ y ∈ S, y * x = x * y) ∧ orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hnormal : (U.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hSU
  have hne : U.subgroupOf S ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUS, h, Subgroup.map_bot]
  have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  set W := U.subgroupOf S ⊓ Subgroup.center ↥S with hWdef
  have hW2 : IsPGroup 2 ↥W := (hS.to_le (le_refl S)).to_subgroup W
  have hntW : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).2 hW
  obtain ⟨k, hk⟩ := hW2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hntW).ne' hk
  have hdvd : 2 ∣ Nat.card ↥W := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨⟨⟨x, hxS⟩, hxW⟩, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨x, hxW.1, fun y hy => ?_, ?_⟩
  · have := Subgroup.mem_center_iff.mp hxW.2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  · rw [← hx, Subgroup.orderOf_mk, Subgroup.orderOf_mk]

theorem lemma439_of (hfix : Lemma439Fix) : Lemma439 := by
  intro G _ _ T M L n I H K t sk hchar h41 h438
  set S := T ⊓ H with hS
  set D := omegaOneCenterOf S ⊓ Subgroup.centralizer (L : Set G) with hD
  have hDK : D ≤ Subgroup.centralizer (K : Set G) := hfix G T M L n I H K t sk hchar h41 h438
  have hS2 : IsPGroup 2 S := sk.base.hyp.sylow.1.to_le inf_le_left
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_left.trans (sk.base.hyp.T_le.trans sk.base.hyp.normal)
  have htL : t ∈ Subgroup.normalizer (L : Set G) :=
    sk.base.hyp.normal (sk.base.hyp.T_le sk.t_mem)
  have hD1 : D = ⊥ := by
    by_contra hD1
    have hD2 : IsPGroup 2 D := hS2.to_le (inf_le_left.trans (omegaOneCenterOf_le S))
    have hSN : S ≤ Subgroup.normalizer (D : Set G) := fun s hs =>
      mem_normalizer_inf (normalizer_le_normalizer_omegaOneCenterOf S (Subgroup.le_normalizer hs))
        (mem_normalizer_centralizer_of_mem (hSL hs))
    have htN : t ∈ Subgroup.normalizer (D : Set G) :=
      mem_normalizer_inf (normalizer_le_normalizer_omegaOneCenterOf S sk.t_normalizer)
        (mem_normalizer_centralizer_of_mem htL)
    have hLN : L ≤ Subgroup.normalizer (D : Set G) :=
      (Subgroup.le_centralizer_iff.mp inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
    have hX : L ⊔ (S ⊔ Subgroup.zpowers t) ≤ Subgroup.normalizer (D : Set G) :=
      _root_.sup_le hLN (_root_.sup_le hSN (Subgroup.zpowers_le.mpr htN))
    have hN := isUniqueM_normalizer_le sk.lemma_4_3_5 hD1 hD2 hX
    have hKN : K ≤ Subgroup.normalizer (D : Set G) :=
      (Subgroup.le_centralizer_iff.mp hDK).trans (Subgroup.centralizer_le_normalizer _)
    exact sk.not_le (le_inf (le_of_mem_cComp sk.cComp) (hKN.trans hN))
  by_contra hne
  have hSK := sk.S_le_normalizer
  have hSN : S ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :
      Set G) := fun s hs =>
    mem_normalizer_inf (Subgroup.le_normalizer hs) (mem_normalizer_centralizer_of_mem (hSK hs))
  obtain ⟨x, hx, hxC, hx2⟩ := exists_involution_center hS2 inf_le_left hSN hne
  have hxD : x ∈ D := by
    refine ⟨mem_omegaOneCenterOf hx.1 hxC ?_, Subgroup.centralizer_le sk.L_le_K hx.2⟩
    rw [← hx2]
    exact pow_orderOf_eq_one x
  rw [hD1, Subgroup.mem_bot] at hxD
  rw [hxD, orderOf_one] at hx2
  exact absurd hx2 (by norm_num)

end CFSG.Quasithin.H13.Ch4
