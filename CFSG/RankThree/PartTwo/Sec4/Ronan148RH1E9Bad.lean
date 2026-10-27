module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1E9

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.RankThree.PartTwo.Sec14.Ronan148R (exists_inner_rep card_le_nine_mul_of_inner
  card_le_three_of_partTwo eq_one_of_mem_centralizer)

section Def

variable {X Y : Type} [Group X] [Group Y]

@[expose] def E9MoveBad (S : Type) [Group S] : Prop :=
  ∀ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 → ∀ s ∈ E, s ≠ 1 →
    ¬ Good427 (Subgroup.centralizer ({s} : Set S)) →
    ∃ n ∈ Subgroup.normalizer (E : Set S),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S)

theorem E9MoveBad.of_mulEquiv (e : X ≃* Y) (h : E9MoveBad Y) : E9MoveBad X := by
  intro E hE hE9 s hs hs1 hbad
  have hEm : CFSG.Assembly.IsElemAbelian 3 (E.map e.toMonoidHom) := isElemAbelian_map _ hE
  obtain ⟨n, hn, hns⟩ := h (E.map e.toMonoidHom) hEm
    (by rw [Subgroup.card_map_of_injective e.injective, hE9]) (e s) ⟨s, hs, rfl⟩
    (by rw [Ne, map_eq_one_iff _ e.injective]; exact hs1)
    (fun hg => hbad (Good427.of_mulEquiv_centralizer e hg))
  have hN := Subgroup.map_equiv_normalizer_eq E e
  rw [← hN] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  refine ⟨m, hm, fun hm' => hns ?_⟩
  have hZ : (Subgroup.zpowers s).map e.toMonoidHom = Subgroup.zpowers (e s) :=
    MonoidHom.map_zpowers _ s
  rw [← hZ, ← Subgroup.map_equiv_normalizer_eq]
  exact ⟨m, hm', rfl⟩

end Def

section Exclusion

variable {G : Type} [Group G] [Finite G]

theorem centralizer_subgroupOf_eq_of_mul {L : Subgroup G} {a₁ a₂ : G} (ha₁L : a₁ ∈ L)
    (ha₂C : a₂ ∈ Subgroup.centralizer (L : Set G)) :
    (Subgroup.centralizer ({a₁ * a₂} : Set G)).subgroupOf L =
      Subgroup.centralizer ({(⟨a₁, ha₁L⟩ : L)} : Set L) := by
  ext l
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  have hl : (l : G) * a₂ = a₂ * l := (Subgroup.mem_centralizer_iff.mp ha₂C) l l.2
  constructor
  · intro h
    apply Subtype.ext
    show (l : G) * a₁ = a₁ * l
    have h2 : (l : G) * a₁ * a₂ = a₁ * l * a₂ := by
      calc (l : G) * a₁ * a₂ = l * (a₁ * a₂) := mul_assoc _ _ _
        _ = a₁ * a₂ * l := h
        _ = a₁ * (l * a₂) := by rw [mul_assoc, hl]
        _ = a₁ * l * a₂ := (mul_assoc _ _ _).symm
    exact mul_right_cancel h2
  · intro h
    have h' : (l : G) * a₁ = a₁ * l := congrArg Subtype.val h
    calc (l : G) * (a₁ * a₂) = (l * a₁) * a₂ := (mul_assoc _ _ _).symm
      _ = (a₁ * l) * a₂ := by rw [h']
      _ = a₁ * (a₂ * l) := by rw [mul_assoc, hl]
      _ = a₁ * a₂ * l := (mul_assoc _ _ _).symm

theorem false_of_e9MoveBad_of_bound {L A : Subgroup G} {d : G}
    (hZ : Subgroup.center L = ⊥) (hcube : CubeInner L) (hLn : L.Normal)
    (h9 : ∀ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hE9 : ∃ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hmove : E9MoveBad L) (hA : Late.IsE27 A) (hdA : d ∈ A)
    (hdC : d ∉ Subgroup.centralizer (L : Set G))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hX3 : ∀ W : Subgroup G, W ≤ Subgroup.centralizer (L : Set G) →
      CFSG.Assembly.IsElemAbelian 3 W → Nat.card W ≤ 3)
    (hbad : ¬ Good427 ((Subgroup.centralizer ({d} : Set G)).subgroupOf L)) : False := by
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
  have hbad₁ : ¬ Good427 (Subgroup.centralizer ({(⟨a₁, ha₁L⟩ : L)} : Set L)) := by
    rw [← centralizer_subgroupOf_eq_of_mul ha₁L ha₂C, hda]
    exact hbad
  obtain ⟨n, hn, hns⟩ := hmove E hEab hEcard _ hsE hs1 hbad₁
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

theorem row427_of_e9MoveBad
    {S : Type} [Group S] [Finite S]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* S) →
      Subgroup.center L = ⊥)
    (hR : RankTwoData S) (hmove : E9MoveBad S) (hON : ¬ (19 * 31 * 343) ∣ Nat.card S) :
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
  have hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal := by
    rw [hK', Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective _)]
    exact hK.2
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  rcases htype with ⟨⟨φ⟩⟩ | ⟨-, hext⟩
  ·
    have hT : IsA5Type (K' ⧸ CFSG.pCore 2 K') := ⟨(quotPCoreTwoCongr eK).symm.trans φ⟩
    have hbad : ¬ Good427 ((Subgroup.centralizer ({d} : Set G)).subgroupOf L) := by
      intro hgood
      have eKL : K'.subgroupOf L ≃* K' := Subgroup.subgroupOfEquivOfLe hK'L
      refine hgood (K'.subgroupOf L) (fun x hx => ?_)
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv eKL.symm hK'q) ?_ (isA5Type_quot_congr eKL hT)
      · exact Subgroup.mem_subgroupOf.mpr (hK'd (Subgroup.mem_subgroupOf.mp hx))
      · let ψ : (Subgroup.centralizer ({d} : Set G)).subgroupOf L →*
            ↥(L ⊓ Subgroup.centralizer {d}) :=
          { toFun := fun x => ⟨x.1.1, x.1.2, Subgroup.mem_subgroupOf.mp x.2⟩
            map_one' := rfl
            map_mul' := fun _ _ => rfl }
        have heq : (K'.subgroupOf L).subgroupOf
              ((Subgroup.centralizer ({d} : Set G)).subgroupOf L) =
            (K'.subgroupOf (L ⊓ Subgroup.centralizer {d})).comap ψ := by
          ext x
          exact Iff.rfl
        rw [heq]
        exact hK'sn.comap ψ
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
    have hmove' : E9MoveBad ↥(L.subgroupOf Nn) := hmove.of_mulEquiv eL'
    have hLn' : (L.subgroupOf Nn).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr le_rfl
    have hA'27 : Late.IsE27 (A.subgroupOf Nn) := by
      refine ⟨isElemAbelian_comap Nn.subtype Nn.subtype_injective hA.1, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hA.2]
    have hd'A : (⟨d, hdN⟩ : Nn) ∈ A.subgroupOf Nn := hdA
    have hd'C : (⟨d, hdN⟩ : Nn) ∉
        Subgroup.centralizer ((L.subgroupOf Nn : Subgroup Nn) : Set Nn) := by
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
    have hbad' : ¬ Good427 ((Subgroup.centralizer ({(⟨d, hdN⟩ : Nn)} : Set Nn)).subgroupOf
        (L.subgroupOf Nn)) := by
      intro hgood
      apply hbad
      have heq : (Subgroup.centralizer ({d} : Set G)).subgroupOf L =
          ((Subgroup.centralizer ({(⟨d, hdN⟩ : Nn)} : Set Nn)).subgroupOf (L.subgroupOf Nn)).map
            (Subgroup.subgroupOfEquivOfLe hLN).toMonoidHom := by
        ext l
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
        constructor
        · intro hl
          refine ⟨(Subgroup.subgroupOfEquivOfLe hLN).symm l, ?_,
            (Subgroup.subgroupOfEquivOfLe hLN).apply_symm_apply l⟩
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
          exact Subtype.ext hl
        · rintro ⟨x, hx, rfl⟩
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hx
          exact congrArg Subtype.val hx
      rw [heq]
      exact hgood.map_mulEquiv (Subgroup.subgroupOfEquivOfLe hLN)
    exact false_of_e9MoveBad_of_bound hZ' hcube' hLn' h9' hE9' hmove' hA'27 hd'A hd'C hN' hX3'
      hbad'
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
    exact (Nat.Coprime.pow_right k
      (by norm_num : Nat.Coprime (19 * 31 * 343) 3)).dvd_of_dvd_mul_right h2

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
