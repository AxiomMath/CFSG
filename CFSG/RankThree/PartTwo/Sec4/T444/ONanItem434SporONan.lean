module

public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporONanModel
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporJ3_9CoverGroup
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestON
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item416
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.Native.ONTripleUnique

public section

namespace CFSG.RankThree.PartTwo.Sec4

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.LocalCores
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open Item434Alt (quotConj)
open Item434Kit (layerQuot layerQuot_surjective ker_layerQuot)

namespace Item434SporONan9

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem mem_M_of_comm (h : Ctx434Core G A M Q)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3) {a x : G}
    (haA : a ∈ A) (ha : a ∉ Subgroup.centralizer (layer G : Set G)) (hx : x ∈ layer G)
    (hxa : x * a = a * x) : x ∈ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z' : Subgroup G := A ⊓ Subgroup.centralizer (layer G : Set G) with hZ'
  have hZ'e : CFSG.Assembly.IsElemAbelian 3 Z' := Sec5.isElemAbelian_of_le h.isE27.1 inf_le_left
  have hcommA : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  have haZ' : a ∉ Z' := fun hZ => ha hZ.2
  set B : Subgroup G := Z' ⊔ Subgroup.zpowers a with hB
  have hBA : B ≤ A := sup_le inf_le_left (Subgroup.zpowers_le.mpr haA)
  obtain ⟨-, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hZ'e haZ' (h.isE27.1.2 a haA)
    (fun z hz => hcommA z hz.1 a haA)
  have hB9 : 9 ≤ Nat.card B := by
    rw [hB, hBcard, hC3]
  have hBx : B ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun z hz => ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hxa.symm
  have hxN : x ∈ Subgroup.normalizer (B : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (hBx hb)
  exact Item434Kit.normalizer_le h hBA hB9 hxN

end Item434SporONan9

section Families


theorem item434Spor_ONan_9Cover :
    Item434Spor_ONan_9Cover := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9 hZne
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .ONan ≃* Spor .ONan := b
  have hcard : Nat.card (Spor .ONan) = 460815505920 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.ON.card_ON]
  have : Finite (Spor .ONan) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := hc.isQuasisimple.2.1
  have : IsSimpleGroup (Spor .ONan) := e₀.symm.isSimpleGroup
  have hcen : Subgroup.center (Spor .ONan) = ⊥ :=
    Item434Spor.center_eq_bot_of_simple (by rw [hcard]; norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer (Spor .ONan)) := by
    rw [← Nat.card_congr (equivalence b').toEquiv]
    exact inputs47Core_outON
  have eON : layer G ⧸ Subgroup.center (layer G) ≃* NativeSporadic.ON := e₀.trans b'.symm
  have hZ3 : Nat.card (Subgroup.center (layer G)) = 3 := by
    have hdvd : Nat.card (Subgroup.center (layer G)) ∣ 3 :=
      CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.card_center_dvd_three_of_ON
        hc.isQuasisimple hc.isPGroup_center_layer eON
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hZne
    · exact h3
  have hZA := Item434SporJ3.center_layer_le hc hZ3
  have hC3 : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3 := by
    have h1 := hc.card_inf_mul_card_layerStar
    have h9' : Nat.card hc.layerStar = 9 := h9
    rw [h9'] at h1
    omega
  have h9' : Nat.card (A.map (quotConj e₀)) = 9 := by
    rw [Item434Spor.card_map_quotConj hc e₀]
    exact h9
  set P := (A.map (quotConj e₀)).comap (MulAut.conj : Spor .ONan →* MulAut (Spor .ONan))
    with hP
  have hPmap : P.map MulAut.conj = A.map (quotConj e₀) :=
    Item434Kit.map_comap_conj_eq hc e₀ hout
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hcen
  have hP9 : Nat.card P = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, h9']
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    Item434Kit.isElemAbelian_of_map_injective hinj
      (hPmap ▸ Item434Kit.isElemAbelian_map_quotConj hc e₀)
  have : Group.IsPerfect (layer G) := hc.isQuasisimple.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have eK : Subgroup.center (layer G) ≃* Multiplicative (ZMod 3) :=
    mulEquivOfPrimeCardEq (p := 3) hZ3
      (by rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  obtain ⟨e⟩ := CFSG.RankThree.Native.ONTriple.nonempty_equiv_FHat (G := layer G)
    (Subgroup.center (layer G)) eK eON
  let ψ : layer G ≃* CFSG.RankThree.Native.ONTriple.GM :=
    e.trans CFSG.RankThree.Native.ONTriple.modelEquiv
  have hZ'e : CFSG.Assembly.IsElemAbelian 3 (A ⊓ Subgroup.centralizer (layer G : Set G)) :=
    Sec5.isElemAbelian_of_le hc.isE27.1 inf_le_left
  have hcommA : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc' =>
    congrArg Subtype.val (hc.isE27.1.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc'⟩)
  by_cases hAL : A ≤ layer G
  ·
    have hA' := Sporadic.ONTriple416.isE27_comap ψ hAL hc.isE27
    have htop : M.comap (Sporadic.ONTriple416.ι ψ) = ⊤ := by
      refine Item434SporONan9.eq_top_of_cent_E27 hA' (M.comap (Sporadic.ONTriple416.ι ψ))
        fun a' ha' hna' x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      have hxa : Sporadic.ONTriple416.ι ψ x * Sporadic.ONTriple416.ι ψ a' =
          Sporadic.ONTriple416.ι ψ a' * Sporadic.ONTriple416.ι ψ x := by
        rw [← map_mul, ← map_mul, hx]
      have haA : Sporadic.ONTriple416.ι ψ a' ∈ A := ha'
      have hna : Sporadic.ONTriple416.ι ψ a' ∉ Subgroup.centralizer (layer G : Set G) := by
        intro hcent
        have hmem : Sporadic.ONTriple416.ι ψ a' ∈
            layer G ⊓ Subgroup.centralizer (layer G : Set G) := ⟨(ψ.symm a').2, hcent⟩
        rw [CFSG.GroupTheory.inf_centralizer_eq_map_center] at hmem
        obtain ⟨z, hz, hzeq⟩ := hmem
        have hza : ψ.symm a' = z := Subtype.ext hzeq.symm
        apply hna'
        rw [← CFSG.RankThree.Native.ONTriple.center_GM]
        have ha'z : a' = ψ z := by rw [← hza, MulEquiv.apply_symm_apply]
        have hz' : z ∈ Subgroup.center (layer G) := hz
        rw [ha'z, Subgroup.mem_center_iff]
        rw [Subgroup.mem_center_iff] at hz'
        intro g
        obtain ⟨l, rfl⟩ := ψ.surjective g
        rw [← map_mul, ← map_mul, hz' l]
      exact Item434SporONan9.mem_M_of_comm hc hC3 haA hna (ψ.symm x).2 hxa
    exfalso
    apply hc.not_le
    intro l hl
    have h1 : (⟨l, hl⟩ : layer G) = Sporadic.ONTriple416.ι ψ (ψ ⟨l, hl⟩) :=
      (Sporadic.ONTriple416.ι_psi ψ ⟨l, hl⟩).symm
    have h2 : ψ ⟨l, hl⟩ ∈ M.comap (Sporadic.ONTriple416.ι ψ) := by rw [htop]; trivial
    have h3 : Sporadic.ONTriple416.ι ψ (ψ ⟨l, hl⟩) ∈ M := h2
    rw [Sporadic.ONTriple416.ι_psi] at h3
    exact h3
  ·
    exfalso
    set Z' : Subgroup G := A ⊓ Subgroup.centralizer (layer G : Set G) with hZ'
    obtain ⟨a₁, ha₁A, ha₁Z⟩ : ∃ a₁ ∈ A, a₁ ∉ Z' := by
      by_contra hne
      push Not at hne
      have hle : A ≤ Z' := hne
      have := Subgroup.card_le_of_le hle
      rw [hc.isE27.2, hC3] at this
      omega
    have hB₁ := Sec5.isElemAbelian_sup_zpowers hZ'e ha₁Z (hc.isE27.1.2 a₁ ha₁A)
      (fun z hz => hcommA z hz.1 a₁ ha₁A)
    have hB₁A : Z' ⊔ Subgroup.zpowers a₁ ≤ A :=
      sup_le inf_le_left (Subgroup.zpowers_le.mpr ha₁A)
    have hB₁card : Nat.card (Z' ⊔ Subgroup.zpowers a₁ : Subgroup G) = 9 := by
      rw [hB₁.2, hC3]
    obtain ⟨a₂, ha₂A, ha₂B⟩ : ∃ a₂ ∈ A, a₂ ∉ Z' ⊔ Subgroup.zpowers a₁ := by
      by_contra hne
      push Not at hne
      have hle : A ≤ Z' ⊔ Subgroup.zpowers a₁ := hne
      have := Subgroup.card_le_of_le hle
      rw [hc.isE27.2, hB₁card] at this
      omega
    have hB₂ := Sec5.isElemAbelian_sup_zpowers hB₁.1 ha₂B (hc.isE27.1.2 a₂ ha₂A)
      (fun b hb => hcommA b (hB₁A hb) a₂ ha₂A)
    have hB₂A : (Z' ⊔ Subgroup.zpowers a₁) ⊔ Subgroup.zpowers a₂ ≤ A :=
      sup_le hB₁A (Subgroup.zpowers_le.mpr ha₂A)
    have hB₂card :
        Nat.card ((Z' ⊔ Subgroup.zpowers a₁) ⊔ Subgroup.zpowers a₂ : Subgroup G) = 27 := by
      rw [hB₂.2, hB₁card]
    have hAeq : (Z' ⊔ Subgroup.zpowers a₁) ⊔ Subgroup.zpowers a₂ = A :=
      Subgroup.eq_of_le_of_card_ge hB₂A (by rw [hB₂card, hc.isE27.2])
    have hlift : ∀ a ∈ A, ∃ l : layer G, ∃ c ∈ Subgroup.centralizer (layer G : Set G),
        a = c * (l : G) ∧ layerQuot e₀ l ∈ P := by
      intro a ha
      have hmem : quotConj e₀ a ∈ P.map (MulAut.conj : Spor .ONan →* MulAut (Spor .ONan)) := by
        rw [hPmap]
        exact ⟨a, ha, rfl⟩
      obtain ⟨u, hu, hua⟩ := hmem
      obtain ⟨l, hl⟩ := layerQuot_surjective e₀ u
      have h1 : quotConj e₀ (l : G) = MulAut.conj u := by
        rw [Item434Kit.quotConj_eq_conj_layerQuot e₀ l.2]
        exact congrArg _ hl
      refine ⟨l, a * (l : G)⁻¹, ?_, by group, by rw [hl]; exact hu⟩
      rw [← Item434Kit.ker_quotConj hc.isQuasisimple e₀, MonoidHom.mem_ker, map_mul, map_inv, h1,
        ← hua, mul_inv_cancel]
    obtain ⟨l₁, c₁, hc₁, hac₁, hl₁P⟩ := hlift a₁ ha₁A
    obtain ⟨l₂, c₂, hc₂, hac₂, hl₂P⟩ := hlift a₂ ha₂A
    have hT3 : IsPGroup 3 (P.comap (layerQuot e₀)) :=
      (Sec5.isPGroup_of_isElemAbelian hPe).comap_of_ker_isPGroup (layerQuot e₀) (by
        rw [ker_layerQuot]
        exact hc.isPGroup_center_layer)
    have hT3' : IsPGroup 3 ((P.comap (layerQuot e₀)).map ψ.toMonoidHom) := hT3.map _
    have hcl : IsPGroup 3
        (Subgroup.closure ({ψ l₁, ψ l₂} : Set CFSG.RankThree.Native.ONTriple.GM)) :=
      hT3'.to_le (by
        rw [Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact ⟨l₁, hl₁P, rfl⟩
        · exact ⟨l₂, hl₂P, rfl⟩)
    obtain ⟨Hc, hHc27, hHc3, hHcc⟩ := Item434SporONan9.exists_cent_cube hcl
    set Hc' : Subgroup G := Hc.map (Sporadic.ONTriple416.ι ψ) with hHc'
    have hHc'L : Hc' ≤ layer G := by
      rintro _ ⟨y, -, rfl⟩
      exact (ψ.symm y).2
    have hHc'card : 27 ≤ Nat.card Hc' := by
      rw [hHc', Subgroup.card_map_of_injective (Sporadic.ONTriple416.ι_injective ψ)]
      exact hHc27
    have hAL9 : Nat.card (A ⊓ layer G : Subgroup G) ≤ 9 := by
      have hdvd : Nat.card (A ⊓ layer G : Subgroup G) ∣ 3 ^ 3 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ layer G ≤ A)
        rwa [hc.isE27.2] at this
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
      rcases (by omega : k ≤ 2 ∨ k = 3) with hk2 | hk3
      · rw [hk']
        calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
          _ = 9 := by norm_num
      · exfalso
        apply hAL
        have heq : A ⊓ layer G = A :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', hk3, hc.isE27.2]; norm_num)
        calc A = A ⊓ layer G := heq.symm
          _ ≤ layer G := inf_le_right
    obtain ⟨h, hhH, hhA⟩ : ∃ h ∈ Hc', h ∉ A := by
      by_contra hne
      push Not at hne
      have hle : Hc' ≤ A ⊓ layer G := le_inf (fun y hy => hne y hy) hHc'L
      have := Subgroup.card_le_of_le hle
      omega
    obtain ⟨y, hyHc, rfl⟩ := hhH
    have hhL : Sporadic.ONTriple416.ι ψ y ∈ layer G := (ψ.symm y).2
    have hh3 : (Sporadic.ONTriple416.ι ψ y) ^ 3 = 1 := by
      rw [← map_pow, hHc3 y hyHc, map_one]
    set h := Sporadic.ONTriple416.ι ψ y with hh
    have hhl : ∀ l : layer G, ψ l ∈ ({ψ l₁, ψ l₂} : Set CFSG.RankThree.Native.ONTriple.GM) →
        h * (l : G) = (l : G) * h := by
      intro l hl
      have h1 : y * ψ l = ψ l * y := by
        rcases hl with hl | hl
        · rw [hl]; exact (hHcc y hyHc).1
        · rw [Set.mem_singleton_iff] at hl
          rw [hl]; exact (hHcc y hyHc).2
      have h2 := congrArg (Sporadic.ONTriple416.ι ψ) h1
      rw [map_mul, map_mul, Sporadic.ONTriple416.ι_psi] at h2
      exact h2
    have hcent : ∀ c ∈ Subgroup.centralizer (layer G : Set G), h * c = c * h := fun c hc' =>
      Subgroup.mem_centralizer_iff.1 hc' h hhL
    have hcomm₁ : a₁ * h = h * a₁ := by
      rw [hac₁]
      calc c₁ * (l₁ : G) * h = c₁ * ((l₁ : G) * h) := by rw [mul_assoc]
        _ = c₁ * (h * (l₁ : G)) := by rw [← hhl l₁ (Set.mem_insert _ _)]
        _ = c₁ * h * (l₁ : G) := by rw [← mul_assoc]
        _ = h * c₁ * (l₁ : G) := by rw [← hcent c₁ hc₁]
        _ = h * (c₁ * (l₁ : G)) := by rw [mul_assoc]
    have hcomm₂ : a₂ * h = h * a₂ := by
      rw [hac₂]
      calc c₂ * (l₂ : G) * h = c₂ * ((l₂ : G) * h) := by rw [mul_assoc]
        _ = c₂ * (h * (l₂ : G)) := by
          rw [← hhl l₂ (Set.mem_insert_of_mem _ (Set.mem_singleton _))]
        _ = c₂ * h * (l₂ : G) := by rw [← mul_assoc]
        _ = h * c₂ * (l₂ : G) := by rw [← hcent c₂ hc₂]
        _ = h * (c₂ * (l₂ : G)) := by rw [mul_assoc]
    have hAle : A ≤ Subgroup.centralizer ({h} : Set G) := by
      rw [← hAeq]
      refine sup_le (sup_le (fun z hz => ?_) ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcent z hz.2).symm
      · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hcomm₁)
      · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hcomm₂)
    have hcomm : ∀ a ∈ A, a * h = h * a := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.1 (hAle ha)
    obtain ⟨hDe, hDcard⟩ := Sec5.isElemAbelian_sup_zpowers hc.isE27.1 hhA hh3 hcomm
    refine Item434Kit.false_of_le_centralizer hc (B := A) (D := A ⊔ Subgroup.zpowers h) le_rfl
      (by rw [hc.isE27.2]; norm_num) hDe (by rw [hDcard, hc.isE27.2]) ?_
    refine sup_le (fun a ha => ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hcommA b hb a ha
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hcomm b hb

end Families

end CFSG.RankThree.PartTwo.Sec4
