module

public import CFSG.RankThree.PartTwo.Sec15.Item155wProofA5
public import CFSG.RankThree.PartTwo.Sec15.Liebeck156J2
import CFSG.RankThree.PartTwo.Sec15.Liebeck156Frat
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofWE

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

private theorem normalizer_le_normalizer_pCoreOf' (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G) := by
  have hmap : ∀ g ∈ Subgroup.normalizer (J : Set G), ∀ x ∈ CFSG.Open.pCoreOf 2 J,
      g * x * g⁻¹ ∈ CFSG.Open.pCoreOf 2 J := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := hx
    let φ : J ≃* J := (MulAut.conj g).subgroupMap J |>.trans
      (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg))
    have hfix := (inferInstance : (pCore 2 ↥J).Characteristic).fixed φ
    have hy' : φ y ∈ pCore 2 ↥J := by
      have : y ∈ (pCore 2 ↥J).comap φ.toMonoidHom := by rw [hfix]; exact hy
      exact Subgroup.mem_comap.mp this
    exact ⟨φ y, hy', rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hmap g hg x hx, fun hx => ?_⟩
  have := hmap g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem pCoreOf_le_pCoreOf_of_item153Main {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h153 : Item153Main A LB) {Y M : Subgroup G} (hY : Y ∈ scriptY0Star A LB)
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) :
    CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, -, -⟩ := h153 Y hY
  rw [h1, Set.mem_singleton_iff] at hM
  subst hM
  set X := oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) with hX
  have hY4 : Y ∈ scriptY4 A LB := hY.1.1
  have hYX : Y ≤ X := by
    have h2 : Y ≤ delta A LB (Subgroup.normalizer (Y : Set G)) := by
      conv_lhs => rw [hY4.2.2.1]
      exact delta_mono Subgroup.le_normalizer
    rw [hY4.2.1]
    exact oPrimeResidualOf_mono 3 h2
  have hXN : X ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.map_subtype_le _).trans (delta_le _)
  have hO : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYX)
      (hXN.trans (normalizer_le_normalizer_pCoreOf' Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
  exact hO.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans Subgroup.le_normalizer)
    (normalizer_le_normalizer_pCoreOf' X)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X))

theorem commutator_mem_pCoreOf_of_data156 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y : Subgroup G} {c₀ : G} {L₀ : Subgroup G} {d : G} {X₁ : Subgroup G}
    (D : Data156 A LB Y c₀ L₀ d X₁) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYX : Y = X₁ ⊔ CFSG.Open.pCoreOf 2 Y) :
    ∀ y ∈ Y, ∀ e ∈ Subgroup.closure ({c₀, d} : Set G),
      y * e * y⁻¹ * e⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
  intro y hy e he
  have heS : e ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁) := by
    rw [D.cent]; exact he
  obtain ⟨heA, hex⟩ := heS
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hXO : CFSG.Open.pCoreOf 2 X₁ ≤ O := Proof155w.pCoreOf_le_pCoreOf_of_eq_sup D.le_x hYX
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have heO : e ∈ Subgroup.normalizer (O : Set G) :=
    normalizer_le_normalizer_pCoreOf' Y (hAY heA)
  have hXN : X₁ ≤ Subgroup.normalizer (O : Set G) := D.le_x.trans hYO
  have hy' : y ∈ ((X₁ ⊔ O : Subgroup G) : Set G) := hYX ▸ hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X₁ O hXN] at hy'
  obtain ⟨x, hx, u, hu, rfl⟩ := hy'
  have hxe : x * e * x⁻¹ * e⁻¹ ∈ O := by
    have h1 := hex x⁻¹ (inv_mem hx)
    have hxN : x ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X₁ : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X₁ hx
    have h2 := (Subgroup.mem_normalizer_iff.mp hxN _).mp h1
    have h3 : x * (e * x⁻¹ * e⁻¹ * x⁻¹⁻¹) * x⁻¹ = x * e * x⁻¹ * e⁻¹ := by group
    rw [h3] at h2
    exact hXO h2
  have hue : u * e * u⁻¹ * e⁻¹ ∈ O := by
    have h1 : e * u⁻¹ * e⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp heO _).mp (inv_mem hu)
    have h2 : u * e * u⁻¹ * e⁻¹ = u * (e * u⁻¹ * e⁻¹) := by group
    rw [h2]
    exact mul_mem hu h1
  have h4 : x * u * e * (x * u)⁻¹ * e⁻¹ =
      x * (u * e * u⁻¹ * e⁻¹) * x⁻¹ * (x * e * x⁻¹ * e⁻¹) := by group
  rw [h4]
  exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hXN hx) _).mp hue) hxe

theorem card_closure_eq_nine_of_data156 {A : Subgroup G}
    {c₀ : G} {L₀ : Subgroup G} (h₀ : Sec14Std G A c₀ L₀) {LB : Subgroup G → Subgroup G}
    {Y X₁ : Subgroup G} {d : G} (D : Data156 A LB Y c₀ L₀ d X₁) :
    Nat.card (Subgroup.closure ({c₀, d} : Set G)) = 9 := by
  have hA : Late.IsE27 A := h₀.isE27
  have hc₀A : c₀ ∈ A := h₀.toSec13Data.mem_A
  have h := Proof152WE.card_closure_pair hA hc₀A D.mem_d
  have hc3 : Nat.card (Subgroup.zpowers c₀) = 3 := h₀.toSec13Data.card_zpowers
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hA.1.2 d D.mem_d) D.ne_d
  have hdc := not_mem_zpowers_of_data156 h₀ D
  have hint : Nat.card (Subgroup.zpowers c₀ ⊓ Subgroup.zpowers d : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers c₀ ⊓ Subgroup.zpowers d : Subgroup G) ∣ 3 :=
      hd3 ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact h1
    · exfalso
      have heq : (Subgroup.zpowers c₀ ⊓ Subgroup.zpowers d : Subgroup G) = Subgroup.zpowers d :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hd3])
      exact hdc ((heq ▸ inf_le_left : Subgroup.zpowers d ≤ Subgroup.zpowers c₀)
        (Subgroup.mem_zpowers d))
  rw [hc3, hd3, hint, mul_one] at h
  exact h

theorem pCoreOf_le_centralizer_of_data156
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142AllS14)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h153 : Item153Main A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hY5 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)))
    {c₀ : G} {L₀ : Subgroup G} {d : G} {X₁ : Subgroup G} (D : Data156 A (lB A) Y c₀ L₀ d X₁)
    (hΩ : omegaA A ≠ {Subgroup.zpowers c₀})
    (hX5 : Nonempty (↥X₁ ⧸ CFSG.pCore 2 ↥X₁ ≃* alternatingGroup (Fin 5)))
    (hYX : Y = X₁ ⊔ CFSG.Open.pCoreOf 2 Y)
    (hfaith : ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
        ∀ (f : G) (Lf : Subgroup G), Subgroup.zpowers f ∈ omegaA A →
          f ∈ Subgroup.closure ({c₀, d} : Set G) → Lf ∈ lA A f →
          Nonempty (↥Lf ⧸ aschbacherSolvableCore 3 ↥Lf ≃* CFSG.Blueprint.NativeSporadic.J2) →
            CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({f} : Set G) ⊓
              Sec4.thetaQuotCentralizer Lf = ⊥) :
    CFSG.Open.pCoreOf 2 Y ≤ Subgroup.centralizer ({d} : Set G) ∧
      CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({c₀} : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  have hA : Late.IsE27 A := h₀.isE27
  have hc₀A : c₀ ∈ A := h₀.toSec13Data.mem_A
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.1.1.1.2
  set M := Subgroup.normalizer (oPrimeResidualOf 3 (delta A (lB A)
    (Subgroup.normalizer (Y : Set G))) : Set G) with hMdef
  have hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [(h153 Y hY).1]; exact Set.mem_singleton _
  have hPM : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 M :=
    pCoreOf_le_pCoreOf_of_item153Main h153 hY hM
  have hXO : CFSG.Open.pCoreOf 2 X₁ ≤ CFSG.Open.pCoreOf 2 Y :=
    Proof155w.pCoreOf_le_pCoreOf_of_eq_sup D.le_x hYX
  have hdc := not_mem_zpowers_of_data156 h₀ D
  have hpt : ∀ e ∈ Subgroup.closure ({c₀, d} : Set G), e ∉ Subgroup.zpowers d →
      ∃ K : Subgroup G, K ≤ X₁ ⊓ ⨆ Le ∈ lA A e, Le ∧ X₁ ≤ K ⊔ CFSG.Open.pCoreOf 2 X₁ ∧
        K ≤ Subgroup.centralizer ({e} : Set G) ∧
        K ≤ Subgroup.centralizer
          ((CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) : Set G) ∧
        CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({e} : Set G) ⊓
          Subgroup.centralizer ({d} : Set G) = ⊥ := by
    intro e he hed
    have heA : e ∈ A := by
      have : Subgroup.closure ({c₀, d} : Set G) ≤ A :=
        (Subgroup.closure_le A).mpr (Set.insert_subset hc₀A (Set.singleton_subset_iff.mpr D.mem_d))
      exact this he
    have he1 : e ≠ 1 := fun h1 => hed (h1 ▸ (Subgroup.zpowers d).one_mem)
    have heF3 : Nat.card (Subgroup.zpowers e) = 3 := by
      rw [Nat.card_zpowers]; exact orderOf_eq_prime (hA.1.2 e heA) he1
    have hFd : Subgroup.zpowers e ≠ Subgroup.zpowers d := fun hF =>
      hed (hF ▸ Subgroup.mem_zpowers e)
    have hFΩ : Subgroup.zpowers e ∈ omegaA A :=
      step156CQOmega_of h134 h48 h₀ Y hY (Or.inl hY5) c₀ L₀ d X₁ D hΩ (Subgroup.zpowers e)
        (Subgroup.zpowers_le.mpr he) heF3 hFd
    obtain ⟨Le, hLe, hJe⟩ := allPointsHJ_of_j2 h134 h48 h₀ D.hj e hFΩ
    obtain ⟨K, hK1, hK2, hK3, hK4⟩ :=
      exists_centralizes_cq_of_point h h142 D hX5 hM hFΩ he hed hLe hJe
      (hfaith M hM e Le hFΩ he hLe hJe)
    refine ⟨K, le_inf (hK1.trans inf_le_left) ((hK1.trans inf_le_right).trans
      (le_iSup₂_of_le Le hLe le_rfl)), hK2,
      (hK1.trans inf_le_right).trans (Sec6.le_centralizer_of_mem_thetaComponentsAt hLe.1),
      hK3, hK4⟩
  have hYd : CFSG.Open.pCoreOf 2 Y ≤ Subgroup.centralizer ({d} : Set G) := by
    refine le_centralizer_of_perfect_of_fix
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
      (isPerfect_of_mem_scriptY4 hY.1.1) (hA.1.2 c₀ hc₀A) (hA.1.2 d D.mem_d)
      (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨c₀, hc₀A⟩ ⟨d, D.mem_d⟩))
      (card_closure_eq_nine_of_data156 h₀ D)
      (normalizer_le_normalizer_pCoreOf' Y (hAY hc₀A))
      (normalizer_le_normalizer_pCoreOf' Y (hAY D.mem_d)) (hAY hc₀A) (hAY D.mem_d)
      (commutator_mem_pCoreOf_of_data156 D hAY hYX) ?_
    intro e he hed
    obtain ⟨K, hK1, hK2, hK3, hK4, -⟩ := hpt e he hed
    refine ⟨K, ((hK1.trans inf_le_left).trans D.le_x).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y), hK3, ?_, ?_⟩
    · calc Y = X₁ ⊔ CFSG.Open.pCoreOf 2 Y := hYX
        _ ≤ (K ⊔ CFSG.Open.pCoreOf 2 X₁) ⊔ CFSG.Open.pCoreOf 2 Y := sup_le_sup_right hK2 _
        _ ≤ K ⊔ CFSG.Open.pCoreOf 2 Y := sup_le (sup_le le_sup_left (hXO.trans le_sup_right))
            le_sup_right
    · exact hK4.trans (Subgroup.centralizer_le (inf_le_inf_right _ hPM))
  refine ⟨hYd, ?_⟩
  have hc₀d : c₀ ∉ Subgroup.zpowers d := by
    intro hc
    apply hdc
    have hle : Subgroup.zpowers c₀ ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hc
    have hc3 : Nat.card (Subgroup.zpowers c₀) = 3 := h₀.toSec13Data.card_zpowers
    have hd3 : Nat.card (Subgroup.zpowers d) = 3 := by
      rw [Nat.card_zpowers]; exact orderOf_eq_prime (hA.1.2 d D.mem_d) D.ne_d
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hc3, hd3])
    exact heq ▸ Subgroup.mem_zpowers d
  obtain ⟨-, -, -, -, -, hbot⟩ := hpt c₀ (Subgroup.subset_closure (Set.mem_insert _ _)) hc₀d
  rw [eq_bot_iff]
  intro x hx
  rw [← hbot]
  exact ⟨⟨hPM hx.1, hx.2⟩, hYd hx.1⟩

@[expose] def Step156CQA5DO2 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} → ¬ L₀ ≤ Subgroup.normalizer (Y : Set G) →
      Nonempty (↥X₁ ⧸ CFSG.pCore 2 ↥X₁ ≃* alternatingGroup (Fin 5)) →
      Y = X₁ ⊔ CFSG.Open.pCoreOf 2 Y →
      CFSG.Open.pCoreOf 2 Y ≤ Subgroup.centralizer ({d} : Set G) →
      CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({c₀} : Set G) = ⊥ →
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) ≠ ⊥

@[expose] noncomputable def Step156CQA5DO2R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156CQA5DO2 A (lB A)

theorem step156CQA5DFaith_of_o2
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142AllS14)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h153 : Item153Main A (lB A)) (hO2 : Step156CQA5DO2 A (lB A)) :
    Step156CQA5DFaith A (lB A) := by
  intro Y hY hY5 c₀ L₀ d X₁ D hΩ hLN hX5 hYX hfaith
  obtain ⟨hd, hc⟩ :=
    pCoreOf_le_centralizer_of_data156 h134 h48 h142 h h153 hY hY5 D hΩ hX5 hYX hfaith
  exact ⟨hd, hO2 Y hY hY5 c₀ L₀ d X₁ D hΩ hLN hX5 hYX hd hc⟩

theorem step156CQA5DFaithR_of_o2
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142AllS14) (h153 : Item153MainR)
    (hO2 : Step156CQA5DO2R) : Step156CQA5DFaithR :=
  fun G _ _ A c L hR => step156CQA5DFaith_of_o2 h134 h48 h142 hR.toSec14Std (h153 G A c L hR)
    (hO2 G A c L hR)

end CFSG.RankThree.PartTwo.Sec15.Liebeck156
