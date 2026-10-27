module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7Mod
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7B412
public import CFSG.Quasithin.Vol2.Ch12Sec9Final1291
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7Red

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

namespace L1297

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_pCoreOf_or_le_sup {N H : Subgroup G} (hs : IsSimpleGroup (↥H ⧸ CFSG.pCore 2 ↥H))
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    N ≤ pCoreOf 2 H ∨ H ≤ N ⊔ pCoreOf 2 H := by
  have hn : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hHN
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hM : ((N.subgroupOf H).map π).Normal := hn.map π (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal ((N.subgroupOf H).map π) with hb | ht
  · left
    intro x hx
    have h1 : (⟨x, hNH hx⟩ : ↥H) ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← hb]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hx)
    rw [hπ, QuotientGroup.ker_mk'] at h1
    exact ⟨⟨x, hNH hx⟩, by rw [SetLike.mem_coe]; exact h1, rfl⟩
  · right
    intro x hx
    have h1 : π ⟨x, hx⟩ ∈ (N.subgroupOf H).map π := by
      rw [ht]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := h1
    have h2 : y⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥H := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥H), MonoidHom.mem_ker, map_mul, map_inv,
        ← hπ, hyx, inv_mul_cancel]
    have h3 : ((y⁻¹ * ⟨x, hx⟩ : ↥H) : G) ∈ pCoreOf 2 H :=
      ⟨y⁻¹ * ⟨x, hx⟩, by rw [SetLike.mem_coe]; exact h2, rfl⟩
    have h4 : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : ↥H) : G) := by
      simp
    rw [h4]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hy))
      (Subgroup.mem_sup_right h3)

omit [Finite G] in
theorem le_normalizer_sup {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun x hx w hw => ?_
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hA hx) a).1 ha)
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hB hx) b).1 hb)
  exact hle hw

theorem normalizer_le_of_sup_le (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {T L V : Subgroup G} (h : Hyp1223 G T L V) {P : Subgroup G} (hP : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) (hLT : L ⊔ T ≤ Subgroup.normalizer (P : Set G)) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hU := lemma_1_2_7_three h.qtke h.simple h.nonabelian h37 h38 h39 h.sylow h.maximal
  rw [h.conjClosure_eq] at hU
  obtain ⟨N, hNmax, hNle⟩ := exists_maxTwoLocal_ge
    (L := Subgroup.normalizer (P : Set G)) ⟨P, hP, hP2, rfl⟩
  rw [← hU.2 N ⟨hNmax, hLT.trans hNle⟩]
  exact hNle

end L1297

open L1297 in
theorem core1297_of (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h1295 : Lemma12_9_5) (h1296 : Lemma12_9_6) (hLat : LatticeFact1297) :
    Core1297 := by
  intro G _ _ T L V n hcx V₁ V₂ K₁ hV₁ hV₂ hV₁₂ hLK hK
  by_contra hY
  have h := hcx.hyp
  have hyp := h.hyp
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨hVT, hTV⟩ := hyp.le_and_normalizes h1222
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hV₂.2.1
  set L₁ := lOne L V₁ with hL₁
  set Y := (K₁ ⊔ T) ⊓ Subgroup.normalizer (V₂ : Set G) with hYdef
  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    le_of_mem_cComp (show K₁ ∈ cComp _ from hK)
  have hK₁n : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G) :=
    normalizer_le_of_lOne_le h1222 h37 h38 h hn hV₁ hLK hK
  have hTK : T ≤ Subgroup.normalizer (K₁ : Set G) := hV₁.2.2.trans hK₁n
  have hL₁L : L₁ ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hL₁V₁ : L₁ ≤ Subgroup.normalizer (V₁ : Set G) := (oTwoUpper_le _).trans inf_le_right
  have hTY : T ≤ Y := le_inf le_sup_right hV₂.2.2
  have hYG₁ : Y ≤ Subgroup.normalizer (V₁ : Set G) := inf_le_left.trans (sup_le hK₁G₁ hV₁.2.2)
  have hY₂ : Y ≤ Subgroup.normalizer (V₂ : Set G) := inf_le_right
  obtain ⟨-, hiso, h3⟩ := h1295 G T L V n hcx V₁ K₁ hV₁ hLK hK
  obtain ⟨-, ⟨hI₂n, -, -, hI₂T⟩, hm3⟩ := h1296 G T L V n hcx V₁ V₂ K₁ hV₁ hV₂ hV₁₂ hLK hK
  have hY3 : CFSG.Open.pRank 3 Y ≤ 1 :=
    (pRank_three_le hV₁2 hV₂4 hV₁₂ (fun v hv => hsq v (hV₂.1 hv)) hYG₁ hY₂).trans hm3
  have hL₁Y : L₁ ⊓ Y = L₁ ⊓ Subgroup.normalizer (V₂ : Set G) := by
    refine le_antisymm (inf_le_inf_left _ inf_le_right) ?_
    exact le_inf inf_le_left (le_inf ((inf_le_left.trans hLK).trans le_sup_left) inf_le_right)
  have hrel := relIndex_lOne_inf_normalizer h hV₁ hV₂ hV₁₂
  have hL₁N₂ : ¬ L₁ ≤ Subgroup.normalizer (V₂ : Set G) := by
    intro h1
    have h2 := Subgroup.relIndex_eq_one.2 (le_inf le_rfl h1 :
      L₁ ≤ L₁ ⊓ Subgroup.normalizer (V₂ : Set G))
    rw [hrel] at h2
    rcases hcx.n45 with rfl | rfl <;> norm_num at h2
  have hL₁T : T ≤ Subgroup.normalizer (L₁ : Set G) := le_normalizer_lOne hyp.normalizes hV₁.2.2
  have hinner : ∀ t ∈ T, ∃ b ∈ L₁, ∀ x ∈ L₁,
      (b⁻¹ * t) * x * (b⁻¹ * t)⁻¹ * x⁻¹ ∈ pCoreOf 2 L₁ := fun t ht =>
    lOne_inner h1222 h hn hV₁ (hyp.normalizes ht) (hTV ht) (hV₁.2.2 ht)
  have hcase : (Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        (L₁ ⊓ Y).relIndex L₁ = 7 ∧
        (Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
          ∃ φ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
            ((L₁.subgroupOf K₁).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁))).map φ.toMonoidHom =
              Subgroup.centralizer ({transvection15} : Set _))) ∨
      (Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
        (L₁ ⊓ Y).relIndex L₁ = 15) := by
    obtain ⟨e⟩ := lOne_quotient_mulEquiv h1222 h hn hV₁
    rw [hL₁Y, hrel]
    rcases hcx.n45 with rfl | rfl
    · exact Or.inl ⟨⟨e⟩, by norm_num, h3 rfl⟩
    · exact Or.inr ⟨⟨e⟩, by norm_num⟩
  have hO₂L₁ : pCoreOf 2 L₁ ≤ Y :=
    (L1296.le_of_isPGroup hyp.sylow (LieType.BorelTits.pCoreOf_isPGroup 2 L₁)
      (hL₁T.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₁))).trans hTY
  obtain ⟨hB3, hYiso, hHiso, hmax⟩ := hLat G (K₁ ⊔ T) K₁ T L₁ Y le_sup_left
    (sup_le Subgroup.le_normalizer hTK)
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right) rfl hiso hLK hL₁T hinner hcase
    hTY inf_le_left hY hY3 hO₂L₁
  have hn4 : n = 4 := by
    rcases hcx.n45 with h4 | h5
    · exact h4
    · exfalso
      obtain ⟨e⟩ := lOne_quotient_mulEquiv h1222 h hn hV₁
      obtain ⟨e'⟩ := hB3
      subst h5
      have h1 := Nat.card_congr (e.symm.trans e').toEquiv
      have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin (5 - 1)) (ZMod 2)) = 20160 :=
        card_sl_four
      rw [h2, card_sl_three] at h1
      norm_num at h1
  subst hn4
  set H := L₁ ⊔ Y with hHdef
  have hYH : Y ≤ H := le_sup_right
  have hL₁H : L₁ ≤ H := le_sup_left
  have hTH : T ≤ H := hTY.trans hYH
  have hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G) := sup_le hL₁V₁ hYG₁
  have hHY : H ⊓ Subgroup.normalizer (V₂ : Set G) ≤ Y := by
    by_contra hne
    have hlt : Y < H ⊓ Subgroup.normalizer (V₂ : Set G) :=
      lt_of_le_of_ne (le_inf hYH hY₂) fun e => hne (e ▸ le_rfl)
    have h1 := hmax.2 _ hlt inf_le_left
    exact hL₁N₂ (hL₁H.trans (h1 ▸ inf_le_right))
  have hHM : ¬ H ≤ Subgroup.normalizer (L : Set G) := by
    intro hHL
    have hHL₁ : H ≤ Subgroup.normalizer (L₁ : Set G) := le_normalizer_lOne hHL hHV₁
    obtain ⟨hsH, -⟩ := isSimpleGroup_and_nonabelian_of_mulEquiv
      (hHiso.elim Or.inl fun h1 => Or.inr (Or.inl h1))
    have hO₂T : pCoreOf 2 H ≤ T :=
      pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH)
    rcases le_pCoreOf_or_le_sup hsH hL₁H hHL₁ with h1 | h1
    · exact hL₁N₂ ((h1.trans hO₂T).trans hV₂.2.2)
    · exact hY (hYH.trans (h1.trans (sup_le_sup_left hO₂T _)))
  have hV₁H : V₁ ≤ H := (hV₁.1.trans hVT).trans hTH
  have hV₁p : IsPGroup 2 V₁ := hT2.to_le (hV₁.1.trans hVT)
  have hV₁ne : V₁ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hV₁2
    norm_num at hV₁2
  have hHz : IsHzOne T L V₁ H := by
    refine ⟨⟨sup_le_sup_left hTY _, fun hb => hV₁ne ?_⟩, hHV₁, hHM⟩
    have h1 := LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV₁H hHV₁ hV₁p
    rw [hb] at h1
    exact le_bot_iff.1 h1
  have hU32 := card_conjClosure_eq h1222 h37 h38 h39 asB4_12_two_holds h hV₁ hV₂ hV₁₂ hHz hYH hHY
    hY₂ hYiso hHiso
  set U := conjClosure V H with hUdef
  have hVU : V ≤ U := le_conjClosure V H
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V H
  have hNVM := normalizer_le_of_hyp1223 h37 h38 h39 hyp hTV (hT2.to_le hVT)
  have hL₁M : L₁ ≤ Subgroup.normalizer (L : Set G) := hL₁L.trans Subgroup.le_normalizer
  have hYV : ¬ Y ≤ Subgroup.normalizer (V : Set G) := fun h1 => hHM (sup_le hL₁M (h1.trans hNVM))
  obtain ⟨y, hyY, hyV⟩ := IsConcreteLE.not_le_iff_exists.1 hYV
  set W := V.map (MulAut.conj y).toMonoidHom with hWdef
  have hWU : W ≤ U := by
    rintro _ ⟨v, hv, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hHU (hYH hyY)) v).1 (hVU hv)
  have hWcard : Nat.card W = Nat.card V :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hWV : ¬ W ≤ V := by
    intro hle
    have heq : W = V := Subgroup.eq_of_le_of_card_ge hle hWcard.ge
    apply hyV
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      rw [← heq]
      exact ⟨v, hv, rfl⟩
    · intro hv
      rw [← heq] at hv
      obtain ⟨v', hv', hvv'⟩ := hv
      have : v' = v := by
        have := congrArg (fun z => y⁻¹ * z * y) hvv'
        simpa [mul_assoc] using this
      rw [← this]
      exact hv'
  have hVWU : V ⊔ W = U := by
    have hle : V ⊔ W ≤ U := sup_le hVU hWU
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := Subgroup.card_dvd_of_le (le_sup_left : V ≤ V ⊔ W)
    have h2 := Subgroup.card_le_of_le hle
    have h3 : Nat.card ↥(V ⊔ W) ≠ Nat.card V := by
      intro e
      exact hWV ((le_sup_right : W ≤ V ⊔ W).trans
        (Subgroup.eq_of_le_of_card_ge (le_sup_left : V ≤ V ⊔ W) e.le).symm.le)
    have h4 : Nat.card V ≤ Nat.card ↥(V ⊔ W) := Subgroup.card_le_of_le le_sup_left
    rw [hU32]
    rw [hU32] at h2
    rw [hcard] at h1 h3 h4
    norm_num at h1 h2 h3 h4 ⊢
    omega
  set I₂ := conjClosure (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
    (Subgroup.normalizer (V₂ : Set G)) with hI₂def
  have hI₂LT : I₂ ≤ L ⊔ T := le_sup_left.trans (hI₂T.le.trans inf_le_left)
  have hI₂V : I₂ ≤ Subgroup.normalizer (V : Set G) :=
    hI₂LT.trans (sup_le hyp.irrPlus.2.2.1 hTV)
  have hI₂W : I₂ ≤ Subgroup.normalizer (W : Set G) := by
    refine le_normalizer_of_conj_mem fun i hi w hw => ?_
    obtain ⟨v, hv, rfl⟩ := hw
    have hi' : y⁻¹ * i * y⁻¹⁻¹ ∈ I₂ :=
      (Subgroup.mem_normalizer_iff.1 (hI₂n (Subgroup.inv_mem _ (hY₂ hyY))) i).1 hi
    have hv' : (y⁻¹ * i * y⁻¹⁻¹) * v * (y⁻¹ * i * y⁻¹⁻¹)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hI₂V hi') v).1 hv
    refine ⟨_, hv', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hI₂U : I₂ ≤ Subgroup.normalizer (U : Set G) := by
    rw [← hVWU]
    exact le_normalizer_sup hI₂V hI₂W
  obtain ⟨g, hgP, hgN⟩ := exist1282g h1222 G T L V 4 h V₁ hV₁
  have hgX : g ∈ (L ⊔ T) ⊓ Subgroup.normalizer (U : Set G) := by
    refine ⟨hgP.1, ?_⟩
    rw [← hI₂T] at hgP
    exact (sup_le hI₂U (hTH.trans hHU)) hgP
  have hLTU : L ⊔ T ≤ Subgroup.normalizer (U : Set G) :=
    (sup_le_of_not_le_normalizer h1222 h hV₁ (X := (L ⊔ T) ⊓ Subgroup.normalizer (U : Set G))
      (le_inf (sup_le_sup_right hL₁L T) (sup_le (hL₁H.trans hHU) (hTH.trans hHU))) inf_le_left
      fun hX => hgN (hX hgX)).trans inf_le_right
  have hA := lemma12_8_4_one h1222 h hV₁ hHz
  have hU2 : IsPGroup 2 U := hT2.to_le hA.G22_three.1
  have hUne : U ≠ ⊥ := by
    intro hb
    apply hV₁ne
    exact le_bot_iff.1 (hb ▸ hV₁.1.trans hVU)
  exact hHM (hHU.trans (normalizer_le_of_sup_le h37 h38 h39 hyp hUne hU2 hLTU))

end CFSG.Quasithin.H13
