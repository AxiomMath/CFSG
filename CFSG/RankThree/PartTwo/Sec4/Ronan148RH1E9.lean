module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148RH2
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Core
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SH1

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.RankThree.PartTwo.Sec14.Ronan148R (exists_inner_rep card_le_nine_mul_of_inner
  card_le_three_of_partTwo eq_one_of_mem_centralizer)

section Exclusion

variable {G : Type} [Group G] [Finite G]

theorem false_of_e9Move_of_bound {L A : Subgroup G} {d : G}
    (hZ : Subgroup.center L = ⊥) (hcube : CubeInner L) (hLn : L.Normal)
    (h9 : ∀ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hE9 : ∃ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hmove : E9Move L) (hA : Late.IsE27 A) (hdA : d ∈ A)
    (hdC : d ∉ Subgroup.centralizer (L : Set G))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hX3 : ∀ W : Subgroup G, W ≤ Subgroup.centralizer (L : Set G) →
      CFSG.Assembly.IsElemAbelian 3 W → Nat.card W ≤ 3) : False := by
  have hNL : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact Subgroup.mem_top g
  have hG3 : ∀ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 27 := by
    intro E hE
    have h1 := card_le_nine_mul_of_inner hZ hcube (fun g _ => hNL g) hE h9
    have h2 := hX3 _ inf_le_right (isElemAbelian_mono inf_le_left hE)
    omega
  have hL9 : ∀ E : Subgroup G, E ≤ L → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9 := by
    intro E hEL hE
    have hE' : CFSG.Assembly.IsElemAbelian 3 (E.subgroupOf L) :=
      isElemAbelian_comap L.subtype L.subtype_injective hE
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv]
    exact h9 _ hE'
  have hLE : ∃ E : Subgroup G, E ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    obtain ⟨E, hE, hE9⟩ := hE9
    refine ⟨E.map L.subtype, Subgroup.map_subtype_le E, Ronan148S.isElemAbelian_map _ hE, ?_⟩
    rw [Subgroup.card_map_of_injective L.subtype_injective, hE9]
  obtain ⟨hAL9, -, hsplit⟩ := inner_split hZ hcube (fun g _ => hNL g) hA hG3 hL9 hLE
  have hcAL : ∀ x ∈ A ⊓ L, ∀ y ∈ A ⊓ Subgroup.centralizer (L : Set G), x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2) x
      (Subgroup.mem_inf.mp hx).2
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcAL).2
  have hdmem : d ∈ ((A ⊓ L ⊔ A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    rw [hsplit]
    exact hdA
  rw [hset] at hdmem
  obtain ⟨a₁, ha₁, a₂, ha₂, hda⟩ := Set.mem_mul.mp hdmem
  have ha₁A : a₁ ∈ A := (Subgroup.mem_inf.mp ha₁).1
  have ha₁L : a₁ ∈ L := (Subgroup.mem_inf.mp ha₁).2
  have ha₂C : a₂ ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp ha₂).2
  have ha₁1 : a₁ ≠ 1 := by
    rintro rfl
    apply hdC
    rw [← hda, one_mul]
    exact ha₂C
  set E : Subgroup L := (A ⊓ L).subgroupOf L with hE
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    isElemAbelian_comap L.subtype L.subtype_injective (isElemAbelian_mono inf_le_left hA.1)
  have hEcard : Nat.card E = 9 := by
    rw [hE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv,
      hAL9]
  have hsE : (⟨a₁, ha₁L⟩ : L) ∈ E := ⟨ha₁A, ha₁L⟩
  have hs1 : (⟨a₁, ha₁L⟩ : L) ≠ 1 := fun h => ha₁1 (congrArg Subtype.val h)
  obtain ⟨n, hn, hns⟩ := hmove E hEab hEcard _ hsE hs1
  have hnA : (n : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    mem_normalizer_of_subgroupOf inf_le_right hn
  have hnAA := mem_normalizer_of_split hsplit n.2 hnA
  have hnd := hN hnAA
  apply hns
  rw [← zpowers_subgroupOf ha₁L]
  refine mem_normalizer_subgroupOf (Subgroup.zpowers_le.mpr ha₁L) ?_
  have hmem : (n : G) * d * (n : G)⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp hnd d).mp (Subgroup.mem_zpowers d)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hna₂ : (n : G) * a₂ = a₂ * (n : G) := (Subgroup.mem_centralizer_iff.mp ha₂C) _ n.2
  have ha₁₂ : a₁ * a₂ = a₂ * a₁ := (Subgroup.mem_centralizer_iff.mp ha₂C) _ ha₁L
  have hdk : d ^ k = a₁ ^ k * a₂ ^ k := by
    rw [← hda]
    exact (Commute.mul_zpow ha₁₂ k)
  have hnd' : (n : G) * d * (n : G)⁻¹ = ((n : G) * a₁ * (n : G)⁻¹) * a₂ := by
    rw [← hda]
    calc (n : G) * (a₁ * a₂) * (n : G)⁻¹
        = ((n : G) * a₁ * (n : G)⁻¹) * ((n : G) * a₂ * (n : G)⁻¹) := by group
      _ = ((n : G) * a₁ * (n : G)⁻¹) * a₂ := by rw [hna₂, mul_inv_cancel_right]
  have hv : (a₁ ^ k)⁻¹ * ((n : G) * a₁ * (n : G)⁻¹) = a₂ ^ k * a₂⁻¹ := by
    have h := hk.trans hnd'
    rw [hdk] at h
    calc (a₁ ^ k)⁻¹ * ((n : G) * a₁ * (n : G)⁻¹)
        = (a₁ ^ k)⁻¹ * ((n : G) * a₁ * (n : G)⁻¹ * a₂) * a₂⁻¹ := by group
      _ = (a₁ ^ k)⁻¹ * (a₁ ^ k * a₂ ^ k) * a₂⁻¹ := by rw [h]
      _ = a₂ ^ k * a₂⁻¹ := by group
  have hvL : (a₁ ^ k)⁻¹ * ((n : G) * a₁ * (n : G)⁻¹) ∈ L :=
    L.mul_mem (L.inv_mem (L.zpow_mem ha₁L k)) (L.mul_mem (L.mul_mem n.2 ha₁L) (L.inv_mem n.2))
  have hvC : (a₁ ^ k)⁻¹ * ((n : G) * a₁ * (n : G)⁻¹) ∈ Subgroup.centralizer (L : Set G) := by
    rw [hv]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ ha₂C k) (Subgroup.inv_mem _ ha₂C)
  have hv1 := eq_one_of_mem_centralizer hZ hvL hvC
  have hconj : (n : G) * a₁ * (n : G)⁻¹ = a₁ ^ k := by
    rw [inv_mul_eq_one] at hv1
    exact hv1.symm
  refine mem_normalizer_of_map_le ?_
  rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
  show (n : G) * a₁ * (n : G)⁻¹ ∈ _
  rw [hconj]
  exact Subgroup.zpow_mem_zpowers a₁ k


end Exclusion

section Row


variable {G : Type} [Group G] [Finite G] in
theorem eq_one_of_central_of_isA5Type
    {K' : Subgroup G} (hK'q : IsQuasisimple K')
    (hT : IsA5Type (K' ⧸ CFSG.pCore 2 K')) {x : G} (hxK : x ∈ K')
    (hxc : ∀ k ∈ K', k * x = x * k) (hx3 : x ^ 3 = 1) : x = 1 := by
  set Γ := ↥K'
  have hZ : Subgroup.center (Γ ⧸ CFSG.pCore 2 Γ) = ⊥ := by
    haveI := hT.isSimpleGroup
    haveI : Group.IsPerfect Γ := hK'q.1
    exact center_eq_bot_of_isSimpleGroup_of_isPerfect
  have eT : (⊤ : Subgroup Γ) ≃* Γ := Subgroup.topEquiv
  have hTq : IsQuasisimple (⊤ : Subgroup Γ) := CFSG.LocalCores.isQuasisimple_of_mulEquiv eT.symm hK'q
  have hTZ : Subgroup.center ((⊤ : Subgroup Γ) ⧸ CFSG.pCore 2 (⊤ : Subgroup Γ)) = ⊥ := by
    have e2 := quotPCoreTwoCongr eT
    rw [eq_bot_iff]
    intro z hz
    have hz' : e2 z ∈ Subgroup.center (Γ ⧸ CFSG.pCore 2 Γ) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      obtain ⟨g', rfl⟩ := e2.surjective g
      rw [← map_mul, ← map_mul, hz g']
    rw [hZ, Subgroup.mem_bot] at hz'
    exact (map_eq_one_iff e2 e2.injective).mp hz'
  set xx : Γ := ⟨x, hxK⟩
  have hP : Subgroup.zpowers xx ≤ Subgroup.center Γ := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hxc g g.2)
  have hxx3 : xx ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hx3)
  have hP3 : IsPGroup 3 (Subgroup.zpowers xx) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hxx3, one_zpow]
  have h := inf_eq_bot_of_center_eq_bot hTq hTZ hP hP3
  rw [top_inf_eq] at h
  have : xx = 1 := by
    have hm : xx ∈ Subgroup.zpowers xx := Subgroup.mem_zpowers xx
    rw [h, Subgroup.mem_bot] at hm
    exact hm
  exact congrArg Subtype.val this

theorem row427_of_e9Move
    {S : Type} [Group S] [Finite S]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* S) →
      Subgroup.center L = ⊥)
    (hR : RankTwoData S) (hmove : E9Move S) (hON : ¬ (19 * 31 * 343) ∣ Nat.card S) :
    Row427 S := by
  intro G _ _ hG A hA hEF hθ L hL ⟨e⟩ d hdA hd1 hN hLd K hK htype
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
      (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hAN hdA
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {d}).subtype :=
    ⟨_, rfl⟩
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {d} := hK' ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have hK'd : K' ≤ Subgroup.centralizer {d} := hK'M.trans inf_le_right
  have eK : K ≃* K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  rcases htype with ⟨⟨φ⟩⟩ | ⟨-, hext⟩
  ·
    have hT : IsA5Type (K' ⧸ CFSG.pCore 2 K') := ⟨(quotPCoreTwoCongr eK).symm.trans φ⟩
    have hZ : Subgroup.center ↥L = ⊥ :=
      hZS ↥L (sectionFourHyp_subgroup hG L) hL.1 hZ3 ⟨e⟩
    have eL : ↥L ≃* S := (quotCenterEquivOfEqBot hZ).trans e
    have hcubeL : CubeInner ↥L := cubeInner_of_mulEquiv eL hR.cubeInner
    have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
    obtain ⟨dL, hdLL, hdL3, hrep⟩ := exists_inner_rep hZ hcubeL hdN hd3
    have hcomm : ∀ l ∈ L, l * d = d * l → l * dL = dL * l := by
      intro l hl h
      have h1 : d * l * d⁻¹ = l := by rw [← h]; group
      rw [hrep l hl] at h1
      calc l * dL = dL * l * dL⁻¹ * dL := by rw [h1]
        _ = dL * l := by group
    have hdL1 : dL ≠ 1 := by
      rintro rfl
      apply hLd
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hrep l hl
      simp only [one_mul, inv_one, mul_one] at h1
      calc l * d = d * l * d⁻¹ * d := by rw [h1]
        _ = d * l := by group
    have h60 : 60 ∣ Nat.card K' := by
      obtain ⟨a, ha⟩ := exists_card_eq_sixty_mul hT
      rw [ha]
      exact Dvd.intro _ rfl
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') 2 (dvd_trans (by norm_num) h60)
    obtain ⟨f₀, hf₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') 3 (dvd_trans (by norm_num) h60)
    have hcK : ∀ k ∈ K', k * d = d * k := fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hK'd hk)
    have htL : (t₀ : G) ∈ L := hK'L t₀.2
    have ht2 : orderOf (t₀ : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht₀
    have htdL : (t₀ : G) * dL = dL * t₀ := hcomm _ htL (hcK _ t₀.2)
    have hfL : (f₀ : G) ∈ L := hK'L f₀.2
    have hf3 : (f₀ : G) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hf₀, pow_orderOf_eq_one, Subgroup.coe_one]
    have hfdL : (f₀ : G) * dL = dL * f₀ := hcomm _ hfL (hcK _ f₀.2)
    have hfn : (f₀ : G) ∉ Subgroup.zpowers dL := by
      intro hf
      have hfo : orderOf (f₀ : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hf₀
      have hdLo : orderOf dL = 3 := orderOf_eq_prime hdL3 hdL1
      have hle : Subgroup.zpowers (f₀ : G) ≤ Subgroup.zpowers dL := Subgroup.zpowers_le.mpr hf
      have heq : Subgroup.zpowers (f₀ : G) = Subgroup.zpowers dL :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hfo, hdLo])
      have hdLK : dL ∈ K' := by
        have : dL ∈ Subgroup.zpowers (f₀ : G) := heq ▸ Subgroup.mem_zpowers dL
        exact (Subgroup.zpowers_le.mpr f₀.2) this
      have hc : ∀ k ∈ K', k * dL = dL * k := fun k hk => hcomm k (hK'L hk) (hcK k hk)
      exact hdL1 (eq_one_of_central_of_isA5Type hK'q hT hdLK hc hdL3)
    have hX3 : ∀ W : Subgroup G, W ≤ Subgroup.centralizer (L : Set G) →
        CFSG.Assembly.IsElemAbelian 3 W → Nat.card W ≤ 3 := fun W hW hWe =>
      card_le_three_of_partTwo hEF hZ hdLL hdL3 hdL1 htL ht2 htdL hfL hf3 hfdL hfn hW hWe
    set Nn : Subgroup G := Subgroup.normalizer (L : Set G) with hNn
    have hLN : L ≤ Nn := Subgroup.le_normalizer
    have eLL : ↥(L.subgroupOf Nn) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLN
    have eL' : ↥(L.subgroupOf Nn) ≃* S := eLL.trans eL
    have hZ' : Subgroup.center ↥(L.subgroupOf Nn) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : eLL x ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff] at hx ⊢
        intro g
        obtain ⟨g', rfl⟩ := eLL.surjective g
        rw [← map_mul, ← map_mul, hx g']
      rw [hZ, Subgroup.mem_bot] at hx'
      exact (map_eq_one_iff eLL eLL.injective).mp hx'
    have hcube' : CubeInner ↥(L.subgroupOf Nn) := cubeInner_of_mulEquiv eL' hR.cubeInner
    have h9' : ∀ E : Subgroup ↥(L.subgroupOf Nn), CFSG.Assembly.IsElemAbelian 3 E →
        Nat.card E ≤ 9 := by
      intro E hE
      have := hR.card_le (E.map eL'.toMonoidHom) (Ronan148S.isElemAbelian_map _ hE)
      rwa [Subgroup.card_map_of_injective eL'.injective] at this
    have hE9' : ∃ E : Subgroup ↥(L.subgroupOf Nn), CFSG.Assembly.IsElemAbelian 3 E ∧
        Nat.card E = 9 := by
      obtain ⟨E, hE, hE9⟩ := hR.exists_e9
      exact ⟨E.map eL'.symm.toMonoidHom, Ronan148S.isElemAbelian_map _ hE,
        by rw [Subgroup.card_map_of_injective eL'.symm.injective, hE9]⟩
    have hmove' : E9Move ↥(L.subgroupOf Nn) := hmove.of_mulEquiv eL'
    have hLn' : (L.subgroupOf Nn).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr le_rfl
    have hA'27 : Late.IsE27 (A.subgroupOf Nn) := by
      refine ⟨isElemAbelian_comap Nn.subtype Nn.subtype_injective hA.1, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hA.2]
    have hd'A : (⟨d, hdN⟩ : Nn) ∈ A.subgroupOf Nn := hdA
    have hd'C : (⟨d, hdN⟩ : Nn) ∉ Subgroup.centralizer ((L.subgroupOf Nn : Subgroup Nn) : Set Nn) := by
      intro h
      apply hLd
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := (Subgroup.mem_centralizer_iff.mp h) ⟨l, hLN hl⟩ hl
      exact congrArg Subtype.val h1
    have hN' : Subgroup.normalizer ((A.subgroupOf Nn : Subgroup Nn) : Set Nn) ≤
        Subgroup.normalizer (Subgroup.zpowers (⟨d, hdN⟩ : Nn) : Set Nn) := by
      intro g hg
      have h1 : (g : G) ∈ Subgroup.normalizer (A : Set G) := mem_normalizer_of_subgroupOf hAN hg
      have h2 := hN h1
      rw [← zpowers_subgroupOf hdN]
      exact mem_normalizer_subgroupOf (Subgroup.zpowers_le.mpr hdN) h2
    have hX3' : ∀ W : Subgroup Nn,
        W ≤ Subgroup.centralizer ((L.subgroupOf Nn : Subgroup Nn) : Set Nn) →
        CFSG.Assembly.IsElemAbelian 3 W → Nat.card W ≤ 3 := by
      intro W hW hWe
      have hmap : W.map Nn.subtype ≤ Subgroup.centralizer (L : Set G) := by
        rintro _ ⟨w, hw, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have := (Subgroup.mem_centralizer_iff.mp (hW hw)) ⟨l, hLN hl⟩ hl
        exact congrArg Subtype.val this
      have := hX3 _ hmap (Ronan148S.isElemAbelian_map _ hWe)
      rwa [Subgroup.card_map_of_injective Nn.subtype_injective] at this
    exact false_of_e9Move_of_bound hZ' hcube' hLn' h9' hE9' hmove' hA'27 hd'A hd'C hN' hX3'
  ·
    apply hON
    obtain ⟨N, _, ⟨eN⟩, ⟨eQ⟩⟩ := hext
    have hON' : Nat.card ((K ⧸ CFSG.pCore 2 K) ⧸ N) = 460815505920 := by
      rw [Nat.card_congr eQ.toEquiv, CFSG.Sporadic.ON.card_ON]
    have h1 : 19 * 31 * 343 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hON']
      exact Dvd.dvd.mul_right (by norm_num) _
    have h2 : 19 * 31 * 343 ∣ Nat.card L := by
      refine (h1.trans (Subgroup.card_quotient_dvd_card _)).trans ?_
      rw [Nat.card_congr eK.toEquiv]
      exact Subgroup.card_dvd_of_le hK'L
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L),
      Nat.card_congr e.toEquiv] at h2
    obtain ⟨k, hk⟩ := hZ3.exists_card_eq
    rw [hk] at h2
    exact (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime (19 * 31 * 343) 3)).dvd_of_dvd_mul_right
      h2

theorem rowOf427_of_e9Move
    {X : Type} [Group X] [Finite X]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* X) →
      Subgroup.center L = ⊥)
    (hR : RankTwoData X)
    (hmove : ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* X) → E9Move S)
    (hON : ¬ (19 * 31 * 343) ∣ Nat.card X) : RowOf427 X := by
  intro S _ _ _ _ ⟨eSX⟩
  refine row427_of_e9Move ?_ (RankTwoData.of_mulEquiv eSX hR) (hmove S ⟨eSX⟩) ?_
  · intro L _ _ hS hL hZ3 ⟨e'⟩
    exact hZS L hS hL hZ3 ⟨e'.trans eSX⟩
  · rwa [Nat.card_congr eSX.toEquiv]

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
