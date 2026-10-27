module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs
public import CFSG.Quasithin.Background.E6EightSmall
public import CFSG.Quasithin.Background.E6ElevenComp

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def IsA7Type {Y : Type} [Group Y] (L : Subgroup Y) : Prop :=
  Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 7)) ∧
    (Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3)

@[expose] def AS_I_3_1_three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H P L : Subgroup G), CFSG.SectionRank.IsSQTKCat ↥H →
    P ≤ H → IsPGroup 2 P → Id2519.IsTwoComponentIn L (H ⊓ Subgroup.centralizer (P : Set G)) →
    CFSG.Open.pRank 3 L = 2 →
    ∃ K : Subgroup G, Id2519.IsTwoComponentIn K H ∧ L ≤ K ∧ (K.subgroupOf H).Normal ∧
      CFSG.IsQuasisimple ↥L ∧ CFSG.IsQuasisimple ↥K

@[expose] def E618A7Facts : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L A R : Subgroup Y), IsA7Type L → E68BaseHyp L A R →
    (∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 9) ∧
    (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A ≤ 4 ∧
      ((A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A = 4 →
        L ≤ ⨆ (a : Y) (_ : a ∈ A ∧ a ∉ Subgroup.centralizer (L : Set Y)),
          L ⊓ Subgroup.centralizer ({a} : Set Y))

section Tools

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_mem_center_sylow {H Q L : Subgroup G} (hQ : IsSylowTwoOf Q H)
    (hL : IsComponentIn L H) {v : G} (hvQ : v ∈ Q)
    (hvC : v ∈ Subgroup.centralizer (Q : Set G)) : v ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hvN
  have hvH : v ∈ H := hQ.1 hvQ
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  set L' := CFSG.conjugate L v⁻¹ with hL'def
  have hL' : IsComponentIn L' H := Unc25G2.isComponentIn_conjugate hL (H.inv_mem hvH)
  have hne : L ≠ L' := fun he => hvN ((Subgroup.inv_mem_iff _).1
    (BenderBranch.conjugate_eq_iff_mem_normalizer.1 he.symm))
  have hcomm : ⁅L, L'⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hL hL').resolve_left hne
  have hSL : IsSylowTwoOf (Q ⊓ L) L := isSylowTwoOf_inf_of_subnormal' hQ hL.1 hL.2.2
  have hQL' : Q ⊓ L ≤ L' := by
    rintro x ⟨hxQ, hxL⟩
    rw [hL'def, BenderBranch.mem_conjugate_iff, inv_inv]
    have hc : x * v = v * x := Subgroup.mem_centralizer_iff.1 hvC x hxQ
    have : v⁻¹ * x * v = x := by rw [mul_assoc, hc]; group
    rw [this]
    exact hxL
  have hSC : Q ⊓ L ≤ Subgroup.centralizer (L : Set G) :=
    hQL'.trans (Subgroup.le_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm))
  have hS' : (Q ⊓ L).subgroupOf L ≤ Subgroup.center ↥L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hSC hx) y y.2)
  have hodd : ¬ 2 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    intro h2
    apply hSL.2.2
    have h1 : (Subgroup.center ↥L).index ∣ ((Q ⊓ L).subgroupOf L).index :=
      Subgroup.index_dvd_of_le hS'
    exact h2.trans h1
  have hsol : Group.IsSolvable (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd))
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2.1
  obtain ⟨a, b, hab⟩ := hLq.2.2
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsol a b)

theorem card_inf_centralizer_le_card_center (L : Subgroup G) :
    Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card (Subgroup.center ↥L) := by
  let f : ↥(L ⊓ Subgroup.centralizer (L : Set G)) → Subgroup.center ↥L := fun x =>
    ⟨⟨x, x.2.1⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext
      (Subgroup.mem_centralizer_iff.1 x.2.2 y y.2)⟩
  refine Nat.card_le_card_of_injective f fun a b hab => ?_
  exact Subtype.ext (congrArg (fun z : Subgroup.center ↥L => ((z : ↥L) : G)) hab)

theorem three_le_pRank_of_commuting_E {p : ℕ} [hp : Fact p.Prime] {X L₁ L₂ E₁ E₂ : Subgroup G}
    (c12 : L₁ ≤ Subgroup.centralizer (L₂ : Set G)) (hX₁ : L₁ ≤ X) (hX₂ : L₂ ≤ X)
    (hE₁ : E₁ ≤ L₁) (hE₂ : E₂ ≤ L₂) (hab₁ : IsElemAbelian p E₁) (hab₂ : IsElemAbelian p E₂)
    (hc₁ : Nat.card E₁ = p ^ 2) (hne : ¬ E₂ ≤ E₁) : 3 ≤ CFSG.Open.pRank p X := by
  have hp1 : 1 < p := hp.out.one_lt
  have := hab₁.1
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  obtain ⟨x₁, hx₁E, hx₁1⟩ : ∃ x ∈ E₁, x ≠ 1 := by
    by_contra hall
    push Not at hall
    have h0 : E₁ = ⊥ := (Subgroup.eq_bot_iff_forall E₁).2 hall
    rw [h0, Subgroup.card_bot] at hc₁
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp1
    omega
  have hp₁ : x₁ ^ p = 1 := hab₁.2 x₁ hx₁E
  obtain ⟨x₂, hx₂E, hx₂Z⟩ : ∃ x ∈ E₁, x ∉ Subgroup.zpowers x₁ := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show E₁ ≤ Subgroup.zpowers x₁ from hall)
    rw [Nat.card_zpowers, orderOf_eq_prime hp₁ hx₁1, hc₁] at h1
    have : p < p ^ 2 := by nlinarith
    omega
  have hp₂ : x₂ ^ p = 1 := hab₁.2 x₂ hx₂E
  obtain ⟨x₃, hx₃E, hx₃E₁⟩ : ∃ x ∈ E₂, x ∉ E₁ := by
    by_contra hall
    push Not at hall
    exact hne hall
  have hp₃ : x₃ ^ p = 1 := hab₂.2 x₃ hx₃E
  let F₀ : PUnit.{1} →* G := 1
  have hF₀ : Function.Injective F₀ := fun a b _ => Subsingleton.elim a b
  have hcard₀ : Nat.card PUnit.{1} = p ^ 0 := by simp
  have hx₁r : x₁ ∉ F₀.range := by
    rintro ⟨a, ha⟩
    exact hx₁1 ha.symm
  obtain ⟨F₁, hF₁, hcomm₁, hpow₁, hcard₁, hrep₁⟩ := CFSG.SectionRank.exists_extend
    (fun _ _ => rfl) (fun _ => rfl) hcard₀ F₀ hF₀ hp₁ hx₁r (fun _ => Commute.one_left x₁)
  have hr₁ : ∀ a, F₁ a ∈ Subgroup.zpowers x₁ := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₁ a
    rw [hb]
    exact Subgroup.mul_mem _ (by simp [F₀]) (Subgroup.pow_mem _ (Subgroup.mem_zpowers x₁) n)
  have hZE : Subgroup.zpowers x₁ ≤ E₁ := Subgroup.zpowers_le.2 hx₁E
  have hx₂r : x₂ ∉ F₁.range := by
    rintro ⟨a, ha⟩
    exact hx₂Z (ha ▸ hr₁ a)
  have hc12 : ∀ a, Commute (F₁ a) x₂ := fun a =>
    show Commute (F₁ a) x₂ from hcomm _ (hZE (hr₁ a)) _ hx₂E
  obtain ⟨F₂, hF₂, hcomm₂, hpow₂, hcard₂, hrep₂⟩ :=
    CFSG.SectionRank.exists_extend hcomm₁ hpow₁ hcard₁ F₁ hF₁ hp₂ hx₂r hc12
  have hr₂ : ∀ a, F₂ a ∈ E₁ := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₂ a
    rw [hb]
    exact E₁.mul_mem (hZE (hr₁ b)) (E₁.pow_mem hx₂E n)
  have hx₃r : x₃ ∉ F₂.range := by
    rintro ⟨a, ha⟩
    exact hx₃E₁ (ha ▸ hr₂ a)
  have hc3 : ∀ a, Commute (F₂ a) x₃ := fun a =>
    show Commute (F₂ a) x₃ from
      (Subgroup.mem_centralizer_iff.1 (c12 (hE₁ (hr₂ a))) x₃ (hE₂ hx₃E)).symm
  obtain ⟨F₃, hF₃, hcomm₃, hpow₃, hcard₃, hrep₃⟩ :=
    CFSG.SectionRank.exists_extend hcomm₂ hpow₂ hcard₂ F₂ hF₂ hp₃ hx₃r hc3
  have hrange : F₃.range ≤ X := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, n, hb⟩ := hrep₃ a
    rw [hb]
    exact X.mul_mem (hX₁ (hE₁ (hr₂ b))) (X.pow_mem (hX₂ (hE₂ hx₃E)) n)
  have := CFSG.SectionRank.le_pRank_of_injective hp1 hcomm₃ hpow₃ hcard₃ F₃ hF₃ hrange
  omega

end Tools

end E6

end CFSG.Quasithin
