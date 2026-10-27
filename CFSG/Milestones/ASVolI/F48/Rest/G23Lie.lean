module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Stab
public import Certificates.Certificate7765
public import CFSG.Milestones.ASVolI.F48.Id
public import CFSG.Milestones.ASVolI.F48.Rest.Eng
public import CFSG.Milestones.ASVolI.F48.Rest.G23Facts

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.CosetTable CFSG.Quasithin

attribute [local irreducible] burnsideF48t_g23LArr burnsideF48t_g23Tau burnsideF48t_g23GensArr
  burnsideF48t_g23PtsStr

theorem burnsideF48t_identify {p : ℕ} [Fact p.Prime] {X E : Type} [Group X] [Group E]
    {Gp M₁ M₂ : Subgroup E} [Finite ↥Gp] (ε₀ : X ≃* ↥Gp) {S₀ B P₁ P₂ : Subgroup X}
    (hS₀ : ChF.IsSylowOf p S₀ ⊤) (hB : B = ⊤ ⊓ Subgroup.normalizer (S₀ : Set X)) (hne : P₁ ≠ P₂)
    (hmax1 : B ≤ P₁ ∧ P₁ ≤ ⊤ ∧ P₁ ≠ ⊤ ∧ ∀ R : Subgroup X, P₁ < R → R ≤ ⊤ → R = ⊤)
    (hmax2 : B ≤ P₂ ∧ P₂ ≤ ⊤ ∧ P₂ ≠ ⊤ ∧ ∀ R : Subgroup X, P₂ < R → R ≤ ⊤ → R = ⊤)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) :
    ∃ ε : X ≃* ↥Gp, burnsideF48_img ε B = Gp ⊓ (M₁ ⊓ M₂) ∧
      ((burnsideF48_img ε P₁ = Gp ⊓ M₁ ∧ burnsideF48_img ε P₂ = Gp ⊓ M₂) ∨
        (burnsideF48_img ε P₁ = Gp ⊓ M₂ ∧ burnsideF48_img ε P₂ = Gp ⊓ M₁)) := by
  obtain ⟨⟨S, hS, hB'⟩, -, -, hmax'⟩ := hP
  have hS₀img : ChF.IsSylowOf p (burnsideF48_img ε₀ S₀) Gp :=
    burnsideF48_isSylowOf_of_equiv_top ε₀ hS₀
  obtain ⟨g, hg⟩ := burnsideF48_sylow_conj hS hS₀img
  set ε : X ≃* ↥Gp := ε₀.trans (MulAut.conj g) with hε
  have hSimg : burnsideF48_img ε S₀ = S := by
    rw [hε, burnsideF48_img_conj, ← hg]
  have hBimg : burnsideF48_img ε B = Gp ⊓ (M₁ ⊓ M₂) := by
    rw [hB', hB, top_inf_eq, burnsideF48_img_normalizer, hSimg]
  have hkey : ∀ Q : Subgroup X,
      (B ≤ Q ∧ Q ≤ ⊤ ∧ Q ≠ ⊤ ∧ ∀ R : Subgroup X, Q < R → R ≤ ⊤ → R = ⊤) →
      (burnsideF48_img ε Q = Gp ⊓ M₁ ∨ burnsideF48_img ε Q = Gp ⊓ M₂) := by
    rintro Q ⟨hBQ, -, hQtop, hQmax⟩
    refine (hmax' (burnsideF48_img ε Q)).1 ⟨?_, burnsideF48_img_le ε Q, ?_, ?_⟩
    · rw [← hBimg]
      exact (burnsideF48_img_le_iff ε).2 hBQ
    · intro h
      apply hQtop
      apply burnsideF48_img_injective ε
      rw [h, burnsideF48_img_top]
    · intro R hQR hRG
      obtain ⟨R₀, rfl⟩ := burnsideF48_exists_img ε hRG
      have hlt : Q < R₀ := lt_of_le_of_ne ((burnsideF48_img_le_iff ε).1 hQR.le)
        (fun h => hQR.ne (by rw [h]))
      have := hQmax R₀ hlt le_top
      rw [this, burnsideF48_img_top]
  have h1 := hkey P₁ hmax1
  have h2 := hkey P₂ hmax2
  have hne2 : burnsideF48_img ε P₁ ≠ burnsideF48_img ε P₂ := fun h =>
    hne (burnsideF48_img_injective ε h)
  refine ⟨ε, hBimg, ?_⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne2
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne2

abbrev burnsideF48t_g23S1 : Set (Fin 4) := {i | i ≠ 3}

abbrev burnsideF48t_g23S2 : Set (Fin 4) := {i | i ≠ 2}

@[expose] def burnsideF48t_g23KWL : List (List (Fin 4 × Bool)) :=
  [[], burnsideF48t_g23KW.getD 0 [], burnsideF48t_g23KW.getD 1 [],
    burnsideF48t_g23KW.getD 0 [] ++ burnsideF48t_g23KW.getD 1 []]

@[expose] noncomputable def burnsideF48t_g23S0 : Subgroup ↥burnsideF48t_g23X :=
  burnsideF48t_g23S0'.subgroupOf burnsideF48t_g23X

@[expose] noncomputable def burnsideF48t_g23K : Subgroup ↥burnsideF48t_g23X :=
  burnsideF48t_g23K'.subgroupOf burnsideF48t_g23X

section Letters


@[expose] noncomputable def burnsideF48t_g23L (i : Fin 4) : ↥burnsideF48t_g23X :=
  ⟨burnsideF48t_g23σ i, burnsideF48t_g23_σ_mem i.2⟩

theorem burnsideF48t_g23_coe_L (i : Fin 4) :
    ((burnsideF48t_g23L i : ↥burnsideF48t_g23X) : Equiv.Perm (Fin 728)) = burnsideF48t_g23σ i :=
  rfl

theorem burnsideF48t_g23_coe_L' (i : Fin 4) (n : ℕ) (h : (i : ℕ) = n) :
    ((burnsideF48t_g23L i : ↥burnsideF48t_g23X) : Equiv.Perm (Fin 728)) = burnsideF48t_g23σ n := by
  subst h
  rfl

theorem burnsideF48t_g23_coe_L2 :
    ((burnsideF48t_g23L 2 : ↥burnsideF48t_g23X) : Equiv.Perm (Fin 728)) = burnsideF48t_g23σ 2 :=
  burnsideF48t_g23_coe_L' 2 2 rfl

theorem burnsideF48t_g23_coe_L3 :
    ((burnsideF48t_g23L 3 : ↥burnsideF48t_g23X) : Equiv.Perm (Fin 728)) = burnsideF48t_g23σ 3 :=
  burnsideF48t_g23_coe_L' 3 3 rfl

theorem burnsideF48t_g23_coe_ev (w : List (Fin 4 × Bool)) :
    ((burnsideF48s_ev burnsideF48t_g23L w : ↥burnsideF48t_g23X) : Equiv.Perm (Fin 728)) =
      burnsideF48s_ev (fun i : Fin 4 => burnsideF48t_g23σ i) w :=
  (burnsideF48s_ev_map burnsideF48t_g23X.subtype burnsideF48t_g23L w).symm

@[expose] noncomputable def burnsideF48t_g23P1 : Subgroup ↥burnsideF48t_g23X :=
  Subgroup.closure (burnsideF48t_g23L '' burnsideF48t_g23S1)

@[expose] noncomputable def burnsideF48t_g23P2 : Subgroup ↥burnsideF48t_g23X :=
  Subgroup.closure (burnsideF48t_g23L '' burnsideF48t_g23S2)

end Letters

section Sub


theorem burnsideF48t_g23_σ_mem_P1' {i : ℕ} (hi : i < 3) :
    burnsideF48t_g23σ i ∈ burnsideF48t_g23P1' := by
  rw [burnsideF48t_g23_P1'_eq_closure]
  exact Subgroup.subset_closure ⟨⟨i, by rw [burnsideF48t_g23_P1Arr.1]; exact hi⟩, rfl⟩

theorem burnsideF48t_g23_σ_mem_P2' {i : ℕ} (hi : i = 0 ∨ i = 1 ∨ i = 3) :
    burnsideF48t_g23σ i ∈ burnsideF48t_g23P2' := by
  rw [burnsideF48t_g23_P2'_eq_closure]
  rcases hi with rfl | rfl | rfl
  · exact Subgroup.subset_closure ⟨⟨0, by rw [burnsideF48t_g23_P2Arr.1]; norm_num⟩,
      by simp [burnsideF48t_g23P2Idx]⟩
  · exact Subgroup.subset_closure ⟨⟨1, by rw [burnsideF48t_g23_P2Arr.1]; norm_num⟩,
      by simp [burnsideF48t_g23P2Idx]⟩
  · exact Subgroup.subset_closure ⟨⟨2, by rw [burnsideF48t_g23_P2Arr.1]; norm_num⟩,
      by simp [burnsideF48t_g23P2Idx]⟩

theorem burnsideF48t_g23_map_P1 :
    burnsideF48t_g23P1.map burnsideF48t_g23X.subtype = burnsideF48t_g23P1' := by
  rw [burnsideF48t_g23P1, MonoidHom.map_closure, Set.image_image]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi3 : (i : ℕ) < 3 := by
      have h1 := i.2
      have h2 : (i : ℕ) ≠ 3 := fun h => hi (Fin.ext h)
      omega
    simp only [SetLike.mem_coe, burnsideF48t_g23_coe_L]
    exact burnsideF48t_g23_σ_mem_P1' hi3
  · rw [burnsideF48t_g23_P1'_eq_closure, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    have hk : (k : ℕ) < 3 := burnsideF48t_g23_P1Arr.1 ▸ k.2
    refine Subgroup.subset_closure ⟨⟨k, by omega⟩, fun h => ?_, ?_⟩
    · have := congrArg Fin.val h
      simp only at this
      omega
    · simp only [burnsideF48t_g23_coe_L]
      rfl

theorem burnsideF48t_g23_map_P2 :
    burnsideF48t_g23P2.map burnsideF48t_g23X.subtype = burnsideF48t_g23P2' := by
  rw [burnsideF48t_g23P2, MonoidHom.map_closure, Set.image_image]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi3 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 3 := by
      have h1 := i.2
      have h2 : (i : ℕ) ≠ 2 := fun h => hi (Fin.ext h)
      omega
    simp only [SetLike.mem_coe, burnsideF48t_g23_coe_L]
    exact burnsideF48t_g23_σ_mem_P2' hi3
  · rw [burnsideF48t_g23_P2'_eq_closure, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    rcases burnsideF48t_g23_P2Idx_cases k with h | h | h
    · refine Subgroup.subset_closure ⟨0, by decide, ?_⟩
      simp only [Subgroup.coe_subtype, burnsideF48t_g23_coe_L' 0 0 rfl, h]
    · refine Subgroup.subset_closure ⟨1, by decide, ?_⟩
      simp only [Subgroup.coe_subtype, burnsideF48t_g23_coe_L' 1 1 rfl, h]
    · refine Subgroup.subset_closure ⟨3, by decide, ?_⟩
      simp only [Subgroup.coe_subtype, burnsideF48t_g23_coe_L' 3 3 rfl, h]

theorem burnsideF48t_g23_mem_P1 (z : ↥burnsideF48t_g23X) :
    z ∈ burnsideF48t_g23P1 ↔ (z : Equiv.Perm (Fin 728)) ∈ burnsideF48t_g23P1' := by
  rw [← burnsideF48t_g23_map_P1]
  exact (Subgroup.mem_map_iff_mem burnsideF48t_g23X.subtype_injective).symm

theorem burnsideF48t_g23_mem_P2 (z : ↥burnsideF48t_g23X) :
    z ∈ burnsideF48t_g23P2 ↔ (z : Equiv.Perm (Fin 728)) ∈ burnsideF48t_g23P2' := by
  rw [← burnsideF48t_g23_map_P2]
  exact (Subgroup.mem_map_iff_mem burnsideF48t_g23X.subtype_injective).symm

theorem burnsideF48t_g23_mem_P1_iff (z : ↥burnsideF48t_g23X) :
    z ∈ burnsideF48t_g23P1 ↔ (z : Equiv.Perm (Fin 728)) burnsideF48t_g23pA = burnsideF48t_g23pA := by
  rw [burnsideF48t_g23_mem_P1, burnsideF48t_g23_P1'_eq]
  exact ⟨fun h => MulAction.mem_stabilizer_iff.1 h.2,
    fun h => ⟨z.2, MulAction.mem_stabilizer_iff.2 h⟩⟩

theorem burnsideF48t_g23_mem_P2_iff (z : ↥burnsideF48t_g23X) :
    z ∈ burnsideF48t_g23P2 ↔ (z : Equiv.Perm (Fin 728)) burnsideF48t_g23pB = burnsideF48t_g23pB := by
  rw [burnsideF48t_g23_mem_P2, burnsideF48t_g23_P2'_eq]
  exact ⟨fun h => MulAction.mem_stabilizer_iff.1 h.2,
    fun h => ⟨z.2, MulAction.mem_stabilizer_iff.2 h⟩⟩

theorem burnsideF48t_g23_map_B :
    (burnsideF48t_g23P1 ⊓ burnsideF48t_g23P2).map burnsideF48t_g23X.subtype = burnsideF48t_g23B' := by
  rw [Subgroup.map_inf_eq _ _ _ burnsideF48t_g23X.subtype_injective, burnsideF48t_g23_map_P1,
    burnsideF48t_g23_map_P2, burnsideF48t_g23_B'_eq]

theorem burnsideF48t_g23_card_B :
    Nat.card ↥(burnsideF48t_g23P1 ⊓ burnsideF48t_g23P2) = 2916 := by
  rw [← Subgroup.card_map_of_injective burnsideF48t_g23X.subtype_injective, burnsideF48t_g23_map_B,
    burnsideF48t_g23_card_B']

theorem burnsideF48t_g23_card_S0 : Nat.card ↥burnsideF48t_g23S0 = 729 := by
  rw [burnsideF48t_g23S0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    burnsideF48t_g23_S0'_le_X).toEquiv, burnsideF48t_g23_card_S0']

theorem burnsideF48t_g23_K'_le_X :
    burnsideF48t_g23K' ≤ burnsideF48t_g23X := by
  refine burnsideF48t_g23_K'_le_B'.trans ?_
  rw [burnsideF48t_g23_B'_eq]
  exact inf_le_left.trans burnsideF48t_g23_P1'_le_X

theorem burnsideF48t_g23_card_K : Nat.card ↥burnsideF48t_g23K = 4 := by
  rw [burnsideF48t_g23K, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    burnsideF48t_g23_K'_le_X).toEquiv, burnsideF48t_g23_card_K']

theorem burnsideF48t_g23_sylow : ChF.IsSylowOf 3 burnsideF48t_g23S0 ⊤ := by
  have hc : Nat.card ↥burnsideF48t_g23S0 = 3 ^ 6 := by rw [burnsideF48t_g23_card_S0]; norm_num
  refine ⟨le_top, IsPGroup.of_card hc, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.card_mul_index burnsideF48t_g23S0
  rw [hc, burnsideF48t_g23_card_X] at h
  have h2 : burnsideF48t_g23S0.index = 5824 := by omega
  rw [h2]
  decide

theorem burnsideF48t_g23_B_eq : burnsideF48t_g23P1 ⊓ burnsideF48t_g23P2 =
    ⊤ ⊓ Subgroup.normalizer (burnsideF48t_g23S0 : Set ↥burnsideF48t_g23X) := by
  rw [top_inf_eq]
  ext z
  constructor
  · intro hz
    have hzB : (z : Equiv.Perm (Fin 728)) ∈ burnsideF48t_g23B' := by
      rw [burnsideF48t_g23_B'_eq]
      exact ⟨(burnsideF48t_g23_mem_P1 z).1 hz.1, (burnsideF48t_g23_mem_P2 z).1 hz.2⟩
    have hn := burnsideF48t_g23_B'_le_normalizer hzB
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro w
    rw [burnsideF48t_g23S0, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv]
    exact hn w
  · intro hz
    have hn : ∀ s ∈ burnsideF48t_g23S0', (z : Equiv.Perm (Fin 728))⁻¹ * s * z ∈ burnsideF48t_g23S0' := by
      intro s hs
      have hsX : s ∈ burnsideF48t_g23X := burnsideF48t_g23_S0'_le_X hs
      have hz' := Subgroup.inv_mem _ hz
      have h1 := (Subgroup.mem_normalizer_iff.1 hz' ⟨s, hsX⟩).1
        (show (⟨s, hsX⟩ : ↥burnsideF48t_g23X) ∈ burnsideF48t_g23S0 from hs)
      rw [inv_inv, burnsideF48t_g23S0, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv] at h1
      exact h1
    obtain ⟨h0, h364⟩ := burnsideF48t_g23_fix_of_norm z.2 hn
    exact ⟨(burnsideF48t_g23_mem_P1_iff z).2 h0, (burnsideF48t_g23_mem_P2_iff z).2 h364⟩

theorem burnsideF48t_g23_P1_ne_P2 : burnsideF48t_g23P1 ≠ burnsideF48t_g23P2 := by
  intro h
  have h1 : burnsideF48t_g23L 2 ∈ burnsideF48t_g23P1 :=
    Subgroup.subset_closure ⟨2, show (2 : Fin 4) ≠ 3 by decide, rfl⟩
  rw [h, burnsideF48t_g23_mem_P2_iff, burnsideF48t_g23_coe_L2] at h1
  exact burnsideF48t_g23_σ_fix.2.2.2.2.2.2.2 h1

theorem burnsideF48t_g23_L3_not_mem : burnsideF48t_g23L 3 ∉ burnsideF48t_g23P1 := by
  rw [burnsideF48t_g23_mem_P1_iff, burnsideF48t_g23_coe_L3]
  exact burnsideF48t_g23_σ_fix.2.2.2.2.2.2.1

theorem burnsideF48t_g23_L2_not_mem : burnsideF48t_g23L 2 ∉ burnsideF48t_g23P2 := by
  rw [burnsideF48t_g23_mem_P2_iff, burnsideF48t_g23_coe_L2]
  exact burnsideF48t_g23_σ_fix.2.2.2.2.2.2.2

theorem burnsideF48t_g23_P1_max : burnsideF48t_g23P1 ⊓ burnsideF48t_g23P2 ≤ burnsideF48t_g23P1 ∧
    burnsideF48t_g23P1 ≤ ⊤ ∧ burnsideF48t_g23P1 ≠ ⊤ ∧
    ∀ R : Subgroup ↥burnsideF48t_g23X, burnsideF48t_g23P1 < R → R ≤ ⊤ → R = ⊤ := by
  refine ⟨inf_le_left, le_top, fun h => burnsideF48t_g23_L3_not_mem (h ▸ Subgroup.mem_top _),
    fun R hR _ => ?_⟩
  have hlt : burnsideF48t_g23P1' < R.map burnsideF48t_g23X.subtype := by
    rw [← burnsideF48t_g23_map_P1]
    exact (Subgroup.map_lt_map_iff_of_injective burnsideF48t_g23X.subtype_injective).2 hR
  have hRX := burnsideF48t_g23_P1'_max hlt (Subgroup.map_subtype_le R)
  rw [eq_top_iff]
  intro z _
  have hz : (z : Equiv.Perm (Fin 728)) ∈ R.map burnsideF48t_g23X.subtype := by
    rw [hRX]
    exact z.2
  exact (Subgroup.mem_map_iff_mem burnsideF48t_g23X.subtype_injective).1 hz

theorem burnsideF48t_g23_P2_max : burnsideF48t_g23P1 ⊓ burnsideF48t_g23P2 ≤ burnsideF48t_g23P2 ∧
    burnsideF48t_g23P2 ≤ ⊤ ∧ burnsideF48t_g23P2 ≠ ⊤ ∧
    ∀ R : Subgroup ↥burnsideF48t_g23X, burnsideF48t_g23P2 < R → R ≤ ⊤ → R = ⊤ := by
  refine ⟨inf_le_right, le_top, fun h => burnsideF48t_g23_L2_not_mem (h ▸ Subgroup.mem_top _),
    fun R hR _ => ?_⟩
  have hlt : burnsideF48t_g23P2' < R.map burnsideF48t_g23X.subtype := by
    rw [← burnsideF48t_g23_map_P2]
    exact (Subgroup.map_lt_map_iff_of_injective burnsideF48t_g23X.subtype_injective).2 hR
  have hRX := burnsideF48t_g23_P2'_max hlt (Subgroup.map_subtype_le R)
  rw [eq_top_iff]
  intro z _
  have hz : (z : Equiv.Perm (Fin 728)) ∈ R.map burnsideF48t_g23X.subtype := by
    rw [hRX]
    exact z.2
  exact (Subgroup.mem_map_iff_mem burnsideF48t_g23X.subtype_injective).1 hz

end Sub

section Engine


theorem burnsideF48t_g23_rels : ∀ r ∈ burnsideF48t_g23R1 ++ burnsideF48t_g23R2 ++
    [(List.replicate 6 [((2 : Fin 4), true), ((3 : Fin 4), true)]).flatten],
    burnsideF48s_ev (fun i : Fin 4 => burnsideF48t_g23σ i) r = 1 :=
  Certificates.certificate7762.2.2.2.2.2.2.2.2.1

theorem burnsideF48t_g23_comm :
    ¬ (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3 * burnsideF48t_g23κ 0 =
        burnsideF48t_g23κ 0 * (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3)) ∧
    ¬ (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3 * burnsideF48t_g23κ 1 =
        burnsideF48t_g23κ 1 * (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3)) ∧
    ¬ (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3 * (burnsideF48t_g23κ 0 * burnsideF48t_g23κ 1) =
        (burnsideF48t_g23κ 0 * burnsideF48t_g23κ 1) * (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3)) :=
  Certificates.certificate7762.2.2.2.2.2.2.2.2.2.1

theorem burnsideF48t_g23_ev_single (i : Fin 4) :
    burnsideF48s_ev burnsideF48t_g23L [(i, true)] = burnsideF48t_g23L i := by
  simp [burnsideF48s_ev]

theorem burnsideF48t_g23_candRel :
    burnsideF48s_ev burnsideF48t_g23L (burnsideF48s_eCandRel 6 [(2, true)] [(3, true)] []) = 1 := by
  apply Subtype.ext
  rw [burnsideF48t_g23_coe_ev]
  have e : burnsideF48s_eCandRel 6 [((2 : Fin 4), true)] [((3 : Fin 4), true)] [] =
      (List.replicate 6 [((2 : Fin 4), true), ((3 : Fin 4), true)]).flatten := by
    simp [burnsideF48s_eCandRel, burnsideF48s_eInvW]
  rw [e]
  exact burnsideF48t_g23_rels _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem burnsideF48t_g23_tc : Finite (PG 4 burnsideF48t_g23Ws) ∧
    Nat.card (PG 4 burnsideF48t_g23Ws) ≤ Nat.card ↥burnsideF48t_g23X := by
  obtain ⟨f0, d0⟩ := Certificates.certificate7765
  refine ⟨f0, ?_⟩
  rw [burnsideF48t_g23_card_X]
  exact d0

theorem burnsideF48t_g23_facts : burnsideF48t_Facts burnsideF48t_g23L burnsideF48t_g23P1
    burnsideF48t_g23P2 burnsideF48t_g23S1 burnsideF48t_g23S2 burnsideF48t_g23K burnsideF48t_g23R1
    burnsideF48t_g23R2 [[(2, true)]] [[(3, true)]] burnsideF48t_g23KWL 6 where
  hP1 := rfl
  hP2 := rfl
  rel1 := fun r hr => ⟨by
      have h : ∀ r ∈ burnsideF48t_g23R1, ∀ l ∈ r, l.1 ≠ 3 := by decide
      exact h r hr,
    Subtype.ext ((burnsideF48t_g23_coe_ev r).trans (burnsideF48t_g23_rels r
      (List.mem_append_left _ (List.mem_append_left _ hr))))⟩
  rel2 := fun r hr => ⟨by
      have h : ∀ r ∈ burnsideF48t_g23R2, ∀ l ∈ r, l.1 ≠ 2 := by decide
      exact h r hr,
    Subtype.ext ((burnsideF48t_g23_coe_ev r).trans (burnsideF48t_g23_rels r
      (List.mem_append_left _ (List.mem_append_right _ hr))))⟩
  sup := by
    obtain ⟨-, -, -, hmax⟩ := burnsideF48t_g23_P1_max
    refine hmax _ (lt_of_le_of_ne le_sup_left fun h => burnsideF48t_g23_L3_not_mem ?_) le_top
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨3, show (3 : Fin 4) ≠ 2 by decide, rfl⟩)
  K_le := fun z hz => by
    have h1 : (z : Equiv.Perm (Fin 728)) ∈ burnsideF48t_g23K' := hz
    have h2 := burnsideF48t_g23_K'_le_B' h1
    rw [burnsideF48t_g23_B'_eq] at h2
    exact ⟨(burnsideF48t_g23_mem_P1 z).2 h2.1, (burnsideF48t_g23_mem_P2 z).2 h2.2⟩
  KW_let := by
    have h : ∀ w ∈ burnsideF48t_g23KWL, ∀ l ∈ w, l.1 ≠ 3 := by decide
    exact h
  KW_cov := fun c hc => by
    rcases burnsideF48t_g23_K'_cases (show (c : Equiv.Perm (Fin 728)) ∈ burnsideF48t_g23K' from hc)
      with h | h | h | h
    · exact ⟨[], by simp [burnsideF48t_g23KWL], Subtype.ext (by rw [h]; rfl)⟩
    · exact ⟨burnsideF48t_g23KW.getD 0 [], by simp [burnsideF48t_g23KWL],
        Subtype.ext (by rw [burnsideF48t_g23_coe_ev, h]; rfl)⟩
    · exact ⟨burnsideF48t_g23KW.getD 1 [], by simp [burnsideF48t_g23KWL],
        Subtype.ext (by rw [burnsideF48t_g23_coe_ev, h]; rfl)⟩
    · exact ⟨burnsideF48t_g23KW.getD 0 [] ++ burnsideF48t_g23KW.getD 1 [],
        by simp [burnsideF48t_g23KWL],
        Subtype.ext (by rw [burnsideF48t_g23_coe_ev, burnsideF48s_ev_append, h]; rfl)⟩
  XW_let := by decide
  YW_let := by decide
  xred := fun x hx hx2 hxK hxx => by
    refine ⟨[(2, true)], List.mem_singleton_self _, ?_⟩
    rw [burnsideF48t_g23_ev_single]
    show (((burnsideF48t_g23L 2)⁻¹ * x : ↥burnsideF48t_g23X) : Equiv.Perm (Fin 728)) ∈
      burnsideF48t_g23K'
    rw [Subgroup.coe_mul, Subgroup.coe_inv, burnsideF48t_g23_coe_L2]
    refine burnsideF48t_g23_xred ((burnsideF48t_g23_mem_P1 x).1 hx)
      (fun h => hx2 ((burnsideF48t_g23_mem_P2 x).2 h)) (fun k hk => ?_) ?_
    · have := hxK ⟨k, burnsideF48t_g23_K'_le_X hk⟩ hk
      rw [burnsideF48t_g23K, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv] at this
      exact this
    · have := hxx
      rw [burnsideF48t_g23K, Subgroup.mem_subgroupOf, Subgroup.coe_mul] at this
      exact this
  yred := fun y hy hy1 hyK hyy => by
    refine ⟨[(3, true)], List.mem_singleton_self _, ?_⟩
    rw [burnsideF48t_g23_ev_single]
    show (((burnsideF48t_g23L 3)⁻¹ * y : ↥burnsideF48t_g23X) : Equiv.Perm (Fin 728)) ∈
      burnsideF48t_g23K'
    rw [Subgroup.coe_mul, Subgroup.coe_inv, burnsideF48t_g23_coe_L3]
    refine burnsideF48t_g23_yred ((burnsideF48t_g23_mem_P2 y).1 hy)
      (fun h => hy1 ((burnsideF48t_g23_mem_P1 y).2 h)) (fun k hk => ?_) ?_
    · have := hyK ⟨k, burnsideF48t_g23_K'_le_X hk⟩ hk
      rw [burnsideF48t_g23K, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv] at this
      exact this
    · have := hyy
      rw [burnsideF48t_g23K, Subgroup.mem_subgroupOf, Subgroup.coe_mul] at this
      exact this
  cand := fun u hu v hv c hc hcomm => by
    rw [List.mem_singleton] at hu hv
    subst hu
    subst hv
    rw [burnsideF48t_g23_ev_single, burnsideF48t_g23_ev_single] at hcomm
    have hcomm' := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul, burnsideF48t_g23_coe_L2, burnsideF48t_g23_coe_L3,
      burnsideF48t_g23_coe_ev] at hcomm'
    simp only [burnsideF48t_g23KWL, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨burnsideF48t_g23_tc.1, Or.inr ⟨burnsideF48t_g23_tc.2, burnsideF48t_g23_candRel⟩⟩
    · exact absurd hcomm' burnsideF48t_g23_comm.1
    · exact absurd hcomm' burnsideF48t_g23_comm.2.1
    · rw [burnsideF48s_ev_append] at hcomm'
      exact absurd hcomm' burnsideF48t_g23_comm.2.2

theorem burnsideF48t_g23_hconj : ∀ K'' : Subgroup ↥burnsideF48t_g23X,
    K'' ≤ burnsideF48t_g23P1 ⊓ burnsideF48t_g23P2 → Nat.card ↥K'' = Nat.card ↥burnsideF48t_g23K →
    ∃ t ∈ burnsideF48t_g23P1 ⊓ burnsideF48t_g23P2, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ burnsideF48t_g23K := by
  intro K'' hle hcard
  have hKc : Nat.card ↥burnsideF48t_g23K = 4 := burnsideF48t_g23_card_K
  have hsyl : ∀ H : Subgroup ↥burnsideF48t_g23X, H ≤ burnsideF48t_g23P1 ⊓ burnsideF48t_g23P2 →
      Nat.card ↥H = 4 → ChF.IsSylowOf 2 H (burnsideF48t_g23P1 ⊓ burnsideF48t_g23P2) := by
    intro H hH hc
    refine ⟨hH, IsPGroup.of_card (n := 2) (by rw [hc]; norm_num), ?_⟩
    have h := Subgroup.relIndex_mul_card (H := H) (K := burnsideF48t_g23P1 ⊓ burnsideF48t_g23P2)
    rw [inf_eq_left.2 hH, hc, burnsideF48t_g23_card_B] at h
    have h2 : H.relIndex (burnsideF48t_g23P1 ⊓ burnsideF48t_g23P2) = 729 := by omega
    rw [h2]
    decide
  obtain ⟨g, hg⟩ := burnsideF48_sylow_conj (hsyl _ burnsideF48t_g23_facts.K_le hKc)
    (hsyl K'' hle (hcard.trans hKc))
  refine ⟨g, g.2, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · rw [hg]
    exact ⟨z, hz, by simp [MulAut.conj_apply]⟩
  · rw [hg] at hz
    obtain ⟨z', hz', he⟩ := hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at he
    rw [← he]
    exact hz'

end Engine

end CFSG.ASVolI
