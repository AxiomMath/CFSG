module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralRestTags
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

namespace StepTwoWeyl

open CFSG.Assembly

section Abstract

variable {A : Type*} [Group A] [Finite A]

theorem exists_avg {p : ℕ} (hp : p.Prime) (hcomm : ∀ a b : A, a * b = b * a)
    (hA : ∀ a : A, a ^ p = 1) (W : Subgroup (MulAut A)) (hW : Nat.Coprime p (Nat.card W)) :
    ∃ π : A →* A, (∀ a, ∀ σ ∈ W, σ (π a) = π a) ∧ (∀ a, (∀ σ ∈ W, σ a = a) → π a = a) ∧
      (∀ a, ∀ σ ∈ W, π (σ a) = π a) ∧
      ∀ a, a * (π a)⁻¹ ∈ Subgroup.closure {u | ∃ w, ∃ σ ∈ W, u = w * (σ w)⁻¹} := by
  classical
  let _ : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  have : Fintype W := Fintype.ofFinite W
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (by rw [Nat.card_eq_fintype_card] at hW; exact hW.symm) hp.one_lt
  have hpow : ∀ a : A, a ^ (Fintype.card W * k) = a := by
    intro a
    rw [← Nat.mod_add_div (Fintype.card W * k) p, hk, pow_add, pow_mul, hA, one_pow, mul_one,
      pow_one]
  let π : A →* A :=
    { toFun := fun a => (∏ σ : W, (σ : MulAut A) a) ^ k
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, Finset.prod_mul_distrib, mul_pow] }
  have hπ : ∀ a, π a = (∏ σ : W, (σ : MulAut A) a) ^ k := fun _ => rfl
  refine ⟨π, fun a σ₀ hσ₀ => ?_, fun a ha => ?_, fun a σ₀ hσ₀ => ?_, fun a => ?_⟩
  · rw [hπ, map_pow, map_prod]
    congr 1
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨σ₀, hσ₀⟩ : W)) _ _ fun σ => rfl
  · rw [hπ, Finset.prod_congr rfl fun σ _ => ha σ.1 σ.2, Finset.prod_const, Finset.card_univ,
      ← pow_mul, hpow]
  · rw [hπ, hπ]
    congr 1
    exact Fintype.prod_equiv (Equiv.mulRight (⟨σ₀, hσ₀⟩ : W)) _ _ fun σ => rfl
  · have e : a * (π a)⁻¹ = (∏ σ : W, a * ((σ : MulAut A) a)⁻¹) ^ k := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_inv_distrib,
        mul_pow, ← pow_mul, hpow, hπ, inv_pow]
    rw [e]
    refine Subgroup.pow_mem _ (Subgroup.prod_mem _ fun σ _ => Subgroup.subset_closure ?_) k
    exact ⟨a, σ, σ.2, rfl⟩

end Abstract

section Index

variable {G : Type} [Group G] [Finite G]

theorem card_le_mul_of_weyl {p : ℕ} (hp : p.Prime) {V L₁ Q : Subgroup G} (hV : IsElemAbelian p V)
    (hVL : V ≤ Subgroup.normalizer (L₁ : Set G)) (hQL : Q ≤ L₁)
    (hQN : Q ≤ Subgroup.normalizer (V : Set G)) (hW : Nat.Coprime p (Nat.card (ggAutomizer Q V)))
    (hC : V ⊓ Subgroup.centralizer (Q : Set G) ≤ Subgroup.centralizer (L₁ : Set G))
    {b : G} (hbV : b ∈ V) (hb1 : b ≠ 1) (hbL : L₁ ≤ Subgroup.centralizer {b})
    (hE : Nat.card ↥(V ⊓ Subgroup.centralizer (L₁ : Set G)) ≤ p ^ 2) :
    Nat.card V ≤ p * Nat.card ↥(V ⊓ (Subgroup.zpowers b ⊔ L₁)) := by
  have hcommV : ∀ a c : V, a * c = c * a := fun a c => by
    have := hV.1
    exact mul_comm' a c
  have hexpV : ∀ a : V, a ^ p = 1 := fun a => Subtype.ext (by
    simpa using hV.2 a a.2)
  obtain ⟨π, hπfix, hπid, -, hπcomm⟩ := exists_avg hp hcommV hexpV (ggAutomizer Q V) hW
  have hcl : Subgroup.closure {u : V | ∃ w, ∃ σ ∈ ggAutomizer Q V, u = w * (σ w)⁻¹} ≤
      L₁.comap V.subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨w, σ, hσ, rfl⟩
    obtain ⟨q, hqQ, -, hq⟩ := mem_ggAutomizer_iff.mp hσ
    change ((w : G) * ((σ w : V) : G)⁻¹) ∈ L₁
    rw [hq w]
    have h1 : (w : G) * q * (w : G)⁻¹ ∈ L₁ :=
      (Subgroup.mem_normalizer_iff.mp (hVL w.2) q).mp (hQL hqQ)
    have e : (w : G) * (q * w * q⁻¹)⁻¹ = (w : G) * q * (w : G)⁻¹ * q⁻¹ := by group
    rw [e]
    exact L₁.mul_mem h1 (L₁.inv_mem (hQL hqQ))
  have hker : ∀ a : V, π a = 1 → (a : G) ∈ L₁ := by
    intro a ha
    have h := hcl (hπcomm a)
    rw [ha, inv_one, mul_one] at h
    exact h
  have hval : ∀ a : V, ((π a : V) : G) ∈ V ⊓ Subgroup.centralizer (L₁ : Set G) := by
    intro a
    refine ⟨(π a).2, hC ⟨(π a).2, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩⟩
    have hqN := hQN hq
    have h := hπfix a _ (ggConjAut_mem_ggAutomizer hq hqN)
    have h' := congrArg Subtype.val h
    change q * ((π a : V) : G) * q⁻¹ = ((π a : V) : G) at h'
    calc q * ((π a : V) : G) = q * ((π a : V) : G) * q⁻¹ * q := by group
      _ = ((π a : V) : G) * q := by rw [h']
  have hbQ : ∀ q ∈ Q, q * b = b * q := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mp (hbL (hQL hq))
  have hπb : π ⟨b, hbV⟩ = ⟨b, hbV⟩ := by
    refine hπid _ fun σ hσ => ?_
    obtain ⟨q, hqQ, -, hq⟩ := mem_ggAutomizer_iff.mp hσ
    refine Subtype.ext ?_
    rw [hq]
    change q * b * q⁻¹ = b
    rw [hbQ q hqQ, mul_assoc, mul_inv_cancel, mul_one]
  set Kk : Subgroup G := π.ker.map V.subtype with hKk
  set Cc : Subgroup G := π.range.map V.subtype with hCc
  have hKkV : Kk ≤ V := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hCcV : Cc ≤ V := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hKkL : Kk ≤ L₁ := by
    rintro _ ⟨a, ha, rfl⟩
    exact hker a ha
  have hCcE : Cc ≤ V ⊓ Subgroup.centralizer (L₁ : Set G) := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hval a
  have hππ : ∀ a, π (π a) = π a := fun a => hπid _ fun σ hσ => hπfix a σ hσ
  have hcommG : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcommV ⟨x, hx⟩ ⟨y, hy⟩)
  have hinf : Cc ⊓ Kk = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨_, ⟨c, rfl⟩, rfl⟩, ⟨a, ha, hax⟩⟩
    have hac : a = π c := V.subtype_injective hax
    have h1 : π c = 1 := by
      rw [← hππ c, ← hac]
      exact ha
    rw [Subgroup.mem_bot, h1, map_one]
  have hVle : V ≤ Cc ⊔ Kk := by
    intro v hv
    have e : v = V.subtype (π ⟨v, hv⟩) * V.subtype (⟨v, hv⟩ * (π ⟨v, hv⟩)⁻¹) := by
      change v = ((π ⟨v, hv⟩ : V) : G) * (v * ((π ⟨v, hv⟩ : V) : G)⁻¹)
      rw [← mul_assoc, hcommG _ (π ⟨v, hv⟩).2 v hv, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    refine Subgroup.mul_mem_sup ⟨_, ⟨_, rfl⟩, rfl⟩ ⟨_, ?_, rfl⟩
    change π (⟨v, hv⟩ * (π ⟨v, hv⟩)⁻¹) = 1
    rw [map_mul, map_inv, hππ, mul_inv_cancel]
  have hcard1 : Nat.card V ≤ Nat.card Cc * Nat.card Kk := by
    rw [← ggSup_card_eq_of_commute (fun x hx y hy => hcommG x (hCcV hx) y (hKkV hy)) hinf]
    exact Subgroup.card_le_of_le hVle
  have hcardC : Nat.card Cc ≤ p ^ 2 := (Subgroup.card_le_of_le hCcE).trans hE
  have : Fact p.Prime := ⟨hp⟩
  have hbo : orderOf b = p := orderOf_eq_prime (hV.2 b hbV) hb1
  have hinf2 : Subgroup.zpowers b ⊓ Kk = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, ⟨a, ha, rfl⟩⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx1
    have hab : a = (⟨b, hbV⟩ : V) ^ n := V.subtype_injective (by
      rw [← hn, map_zpow]
      rfl)
    have h1 : π a = a := by rw [hab, map_zpow, hπb]
    rw [Subgroup.mem_bot]
    change (a : G) = 1
    rw [← h1, (MonoidHom.mem_ker).mp ha]
    rfl
  have hcard2 : Nat.card ↥(Subgroup.zpowers b ⊔ Kk) = p * Nat.card Kk := by
    rw [ggSup_card_eq_of_commute (fun x hx y hy =>
      hcommG x (Subgroup.zpowers_le.mpr hbV hx) y (hKkV hy)) hinf2, Nat.card_zpowers, hbo]
  have hle : Subgroup.zpowers b ⊔ Kk ≤ V ⊓ (Subgroup.zpowers b ⊔ L₁) :=
    sup_le (le_inf (Subgroup.zpowers_le.mpr hbV) le_sup_left)
      (le_inf hKkV (hKkL.trans le_sup_right))
  calc Nat.card V ≤ Nat.card Cc * Nat.card Kk := hcard1
    _ ≤ p ^ 2 * Nat.card Kk := Nat.mul_le_mul_right _ hcardC
    _ = p * (p * Nat.card Kk) := by ring
    _ = p * Nat.card ↥(Subgroup.zpowers b ⊔ Kk) := by rw [hcard2]
    _ ≤ p * Nat.card ↥(V ⊓ (Subgroup.zpowers b ⊔ L₁)) :=
      Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)

end Index

end StepTwoWeyl

section Tags

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank StepTwoWeyl

theorem GGStepTwoPair.card_le_mul_of_weyl {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {b : G} {L₁ Q : Subgroup G}
    (hpair : GGStepTwoPair p B Bs x L D J b L₁) (hBs : IsElemAbelian p Bs)
    (hVL : Bs ≤ Subgroup.normalizer (L₁ : Set G)) (hQL : Q ≤ L₁)
    (hQN : Q ≤ Subgroup.normalizer (Bs : Set G)) (hW : Nat.Coprime p (Nat.card (ggAutomizer Q Bs)))
    (hC : Bs ⊓ Subgroup.centralizer (Q : Set G) ≤ Subgroup.centralizer (L₁ : Set G)) :
    Nat.card Bs ≤ p * Nat.card ↥(Bs ⊓ (Subgroup.zpowers b ⊔ L₁)) :=
  StepTwoWeyl.card_le_mul_of_weyl hp hBs hVL hQL hQN hW hC hpair.1 hpair.2.1 hpair.le_centralizer
    hpair.2.2.2

@[expose] def GGStepTwoExcSplitWeylOn (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ p ∣ ggExcWeylOrder t → p ∣ 2 ^ f - 1 →
      Nat.Coprime p (Nat.card (ggAutomizer (ggG0 p B x L D J) Bs)) ∧
        ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
          Bs ≤ Subgroup.normalizer (L₁ : Set G) ∧ ∃ Q : Subgroup G, Q ≤ L₁ ∧
            Q ≤ Subgroup.normalizer (Bs : Set G) ∧
              Bs ⊓ Subgroup.centralizer (Q : Set G) ≤ Subgroup.centralizer (L₁ : Set G)

@[expose] def GGStepTwoExcIndexNonsplitOn (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ p ∣ ggExcWeylOrder t → ¬ p ∣ 2 ^ f - 1 →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        Nat.card Bs ≤ p * Nat.card ↥(Bs ⊓ (Subgroup.zpowers b ⊔ L₁))

end Tags

end CFSG.StandardType
