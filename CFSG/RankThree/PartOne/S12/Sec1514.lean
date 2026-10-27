module

public import CFSG.RankThree.PartOne.S12.Sec1512
public import CFSG.RankThree.PartOne.S12.Sec1514Simple
public import CFSG.RankThree.PartOne.S12.Sec1511Tools
public import CFSG.RankThree.PartOne.AUTSL.KF1514P

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace Sec1514

variable {G : Type} [Group G]

theorem not_five_of_eq {p : ℕ} {E A I : Subgroup G} (h : E = A) : ¬ Outcome152Five p E A I := by
  rintro ⟨_, -, -, -, -, -, hne, -⟩
  exact hne h

theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : 5 ≤ p := by
  by_contra hlt
  have h4 : p = 4 := by omega
  exact absurd (h4 ▸ hp) (by norm_num)

end Sec1514

theorem node1512Even_of_inputs (h1511 : Node1511) (hEI : Sec1511.KFEI) : Node1512Even := by
  classical
  intro G _ _ p A c L E h15 hF hout hEA T hT
  by_contra hR
  have hEI' := hEI G p A c L E h15 hF hout (Sec1514.not_five_of_eq hEA)
  obtain ⟨r, hr1, hr4, hLie⟩ := lieRow_of_outcome hout hEA
  have hsimple := isSimpleGroup_of_lieRow hr1 hr4 hLie
  have h := h15.h12
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.three_lt; omega
  have hAI : A ≤ lieGenerated p E := hEA ▸ hEI'
  have hdvd : p ∣ Nat.card ↥(lieGenerated p E) :=
    (dvd_pow_self p (by norm_num : 3 ≠ 0)).trans (h.A_card ▸ Subgroup.card_dvd_of_le hAI)
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup G, R = T ⊓ Subgroup.centralizer (lieGenerated p E : Set G) :=
    ⟨_, rfl⟩
  rw [← hRdef] at hR
  have hR2 : IsPGroup 2 R := hRdef ▸ hT.2.1.to_le inf_le_left
  have hRC : ∀ r ∈ R, ∀ y ∈ lieGenerated p E, y * r = r * y := fun r hr y hy =>
    Subgroup.mem_centralizer_iff.1 (hRdef ▸ hr : r ∈ T ⊓ Subgroup.centralizer (lieGenerated p E : Set G)).2
      y hy
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := by
    intro a ha
    apply Subgroup.centralizer_le_normalizer
    exact Subgroup.mem_centralizer_iff.2 fun r hr => (hRC r hr a (hAI ha)).symm
  have hNR : Subgroup.normalizer (R : Set G) ≤ lieNormalizer p E :=
    Sec15Final.normalizer_le_of_forall_maximal hR hR2 hAR (fun M hM =>
      h1511 G p A c L E h15 hF hout A le_rfl
        (Or.inl ⟨hEA, Nat.le_mul_of_pos_left _ hp.pos⟩) M hM)
  have hIR : lieGenerated p E ≤ Subgroup.normalizer (R : Set G) := by
    intro i hi
    apply Subgroup.centralizer_le_normalizer
    exact Subgroup.mem_centralizer_iff.2 fun r hr => (hRC r hr i hi).symm
  have hI1 : lieGenerated p E ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).1 hsimple.toNontrivial
  exact Sec1512.false_of_normal_in_twoLocal h.setup.2.2.2.1 hR hR2 hIR hNR hI1
    (Sec1512.normal_two_eq_bot_of_simple hsimple hp hp2 hdvd)

theorem node1513_of_inputs (h1511 : Node1511) (hEI : Sec1511.KFEI) (hKF : KF1513) : Node1513 := by
  classical
  intro G _ _ p A c L E h15 hF hout hrow T hT
  by_contra hTI
  have h := h15.h12
  have hp := h.prime
  have hp5 : 5 ≤ p := Sec1514.five_le_of_prime hp h.three_lt
  obtain ⟨r, hr3, hr4, hLie, hEA⟩ : ∃ r, 3 ≤ r ∧ r ≤ 4 ∧ LieRow r p (lieGenerated p E) ∧ E = A := by
    rcases hrow with h3 | h4
    · obtain ⟨f, h1f, hpf, hom, -, hEA, -⟩ := h3
      exact ⟨3, le_rfl, by norm_num, ⟨f, h1f, hpf, hom⟩, hEA⟩
    · obtain ⟨f, h1f, hpf, hom, -, hEA, -⟩ := h4
      exact ⟨4, by norm_num, le_rfl, ⟨f, h1f, hpf, hom⟩, hEA⟩
  have hEI' := hEI G p A c L E h15 hF hout (Sec1514.not_five_of_eq hEA)
  have hsimple := isSimpleGroup_of_lieRow (by omega : 1 ≤ r) hr4 hLie
  have hAI : A ≤ lieGenerated p E := hEA ▸ hEI'
  have hdvd3 : p ^ 3 ∣ Nat.card ↥(lieGenerated p E) := h.A_card ▸ Subgroup.card_dvd_of_le hAI
  have hIC := Sec1512.inf_centralizer_eq_bot_of_simple hsimple hp hdvd3
  have hTC := node1512Even_of_inputs h1511 hEI G p A c L E h15 hF hout hEA T hT
  have hcfg := Sec1512.config_of_inputs hp hp5 hT hTC hIC hAI h.A_elem h.A_card
  obtain ⟨t, htT, ht2, htI, hX1, hX2, hh, hhH, B, hBA, hcard, hB⟩ :=
    hKF r hr3 hr4 G p (lieGenerated p E) (lieGenerated p E ⊔ T) T A hcfg hLie hTI
  have ht1 : t ≠ 1 := fun h1 => htI (h1 ▸ (lieGenerated p E).one_mem)
  obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup G, Z = Subgroup.zpowers t := ⟨_, rfl⟩
  have hZ1 : Z ≠ ⊥ := by
    rw [hZdef]
    exact fun h0 => ht1 (Subgroup.zpowers_eq_bot.1 h0)
  have hZ2 : IsPGroup 2 Z := by
    rw [hZdef]
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one]
  have hBZ : B.map (MulAut.conj hh).toMonoidHom ≤ Subgroup.normalizer (Z : Set G) := fun x hx =>
    hZdef ▸ Sec1512.centralizer_le_normalizer_zpowers (hB hx).2
  have hZN : Subgroup.normalizer (Z : Set G) ≤ lieNormalizer p E :=
    Sec15Final.normalizer_le_of_forall_maximal hZ1 hZ2 hBZ (fun M hM =>
      le_of_conj_maximalTwoLocals (hcfg.H_le_N hhH) le_rfl hM
        (h1511 G p A c L E h15 hF hout B hBA (Or.inl ⟨hEA, hcard⟩)))
  have hXM : lieGenerated p E ⊓ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (Z : Set G) := fun x hx =>
    hZdef ▸ Sec1512.centralizer_le_normalizer_zpowers hx.2
  have hMX : Subgroup.normalizer (Z : Set G) ≤
      Subgroup.normalizer ((lieGenerated p E ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G) := by
    intro m hm
    have hmN : m ∈ lieNormalizer p E := hZN hm
    have hmt : m * t = t * m :=
      Sec1512.mem_centralizer_of_mem_normalizer_zpowers ht2 ht1 (hZdef ▸ hm)
    have hmC : m ∈ Subgroup.centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hmt
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hI' := Subgroup.mem_normalizer_iff.1 hmN y
    constructor
    · rintro ⟨hy1, hy2⟩
      refine ⟨hI'.1 hy1, ?_⟩
      exact (Subgroup.centralizer ({t} : Set G)).mul_mem
        ((Subgroup.centralizer ({t} : Set G)).mul_mem hmC hy2)
        ((Subgroup.centralizer ({t} : Set G)).inv_mem hmC)
    · rintro ⟨hy1, hy2⟩
      refine ⟨hI'.2 hy1, ?_⟩
      have := (Subgroup.centralizer ({t} : Set G)).mul_mem
        ((Subgroup.centralizer ({t} : Set G)).mul_mem
          ((Subgroup.centralizer ({t} : Set G)).inv_mem hmC) hy2) hmC
      simpa [mul_assoc] using this
  exact Sec1512.false_of_normal_in_twoLocal h.setup.2.2.2.1 hZ1 hZ2 hXM hMX hX1 hX2

theorem config1514_of_inputs (h1512 : Node1512Even) (h1513 : Node1513) (hEI : Sec1511.KFEI) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    E = A → ∃ T : Subgroup G, IsSylowOf 2 T (lieNormalizer p E) ∧ ∃ r : ℕ, 1 ≤ r ∧ r ≤ 4 ∧
      Config1514 p (lieGenerated p E) (lieGenerated p E ⊔ T) T A ∧
      LieRow r p (lieGenerated p E) ∧ ((r = 3 ∨ r = 4) → T ≤ lieGenerated p E) := by
  classical
  intro G _ _ p A c L E h15 hF hout hEA
  have h := h15.h12
  have hp := h.prime
  have hp5 : 5 ≤ p := Sec1514.five_le_of_prime hp h.three_lt
  have hEI' := hEI G p A c L E h15 hF hout (Sec1514.not_five_of_eq hEA)
  obtain ⟨r₀, hr₀1, hr₀4, hLie₀⟩ := lieRow_of_outcome hout hEA
  have hsimple := isSimpleGroup_of_lieRow hr₀1 hr₀4 hLie₀
  have hAI : A ≤ lieGenerated p E := hEA ▸ hEI'
  have hdvd3 : p ^ 3 ∣ Nat.card ↥(lieGenerated p E) := h.A_card ▸ Subgroup.card_dvd_of_le hAI
  have hIC := Sec1512.inf_centralizer_eq_bot_of_simple hsimple hp hdvd3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, -⟩ := Sec12Fus.exists_isSylowOf_ge (p := 2) (K := lieNormalizer p E) (X := ⊥)
    bot_le (IsPGroup.of_card (n := 0) (by simp))
  have hTC := h1512 G p A c L E h15 hF hout hEA T hT
  have hcfg := Sec1512.config_of_inputs hp hp5 hT hTC hIC hAI h.A_elem h.A_card
  obtain ⟨r, hr1, hr4, hLie, hT'⟩ : ∃ r, 1 ≤ r ∧ r ≤ 4 ∧ LieRow r p (lieGenerated p E) ∧
      ((r = 3 ∨ r = 4) → T ≤ lieGenerated p E) := by
    have hout' := hout
    rcases hout' with h1 | h2 | h3 | h4 | h5
    · obtain ⟨f, h1f, hpf, hom, -⟩ := h1
      exact ⟨1, le_rfl, by norm_num, ⟨f, h1f, hpf, hom⟩, fun hr => by rcases hr with h | h <;> omega⟩
    · obtain ⟨f, h1f, hpf, hom, -⟩ := h2
      exact ⟨2, by norm_num, by norm_num, ⟨f, h1f, hpf, hom⟩, fun hr => by rcases hr with h | h <;> omega⟩
    · refine ⟨3, by norm_num, by norm_num, ?_, fun _ =>
        h1513 G p A c L E h15 hF hout (Or.inl h3) T hT⟩
      obtain ⟨f, h1f, hpf, hom, -⟩ := h3
      exact ⟨f, h1f, hpf, hom⟩
    · refine ⟨4, by norm_num, le_rfl, ?_, fun _ =>
        h1513 G p A c L E h15 hF hout (Or.inr h4) T hT⟩
      obtain ⟨f, h1f, hpf, hom, -⟩ := h4
      exact ⟨f, h1f, hpf, hom⟩
    · obtain ⟨_, -, -, -, -, -, hne, -⟩ := h5
      exact absurd hEA hne
  exact ⟨T, hT, r, hr1, hr4, hcfg, hLie, hT'⟩

theorem node1514Even'_of_inputs (h1512 : Node1512Even) (h1513 : Node1513) (hEI : Sec1511.KFEI)
    (hKF : AUTSL.KF1514P) : Node1514Even' := by
  classical
  intro G _ _ p A c L E h15 hF hout hEA
  obtain ⟨T, hT, r, hr1, hr4, hcfg, hLie, hT'⟩ := config1514_of_inputs h1512 h1513 hEI G p A c L E h15 hF hout hEA
  obtain ⟨⟨h₁, hh₁, B₁, hB₁A, hcard₁, hB₁⟩, ⟨x, hx, hx1, h₂, hh₂, B₂, hB₂A, hcard₂, hB₂⟩⟩ :=
    hKF r hr1 hr4 G p (lieGenerated p E) (lieGenerated p E ⊔ T) T A hcfg hLie hT'
  exact ⟨T, hT, ⟨h₁, hcfg.H_le_N hh₁, B₁, hB₁A, hB₁.trans (inf_le_inf_right _ le_sup_left), hcard₁⟩,
    ⟨x, hx, hx1, h₂, hcfg.H_le_N hh₂, B₂, hB₂A, hB₂.trans (inf_le_inf_right _ le_sup_left), hcard₂⟩⟩

end CFSG.RankThree.PartOne
