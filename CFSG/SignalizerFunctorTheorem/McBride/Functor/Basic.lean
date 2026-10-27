module

public import CFSG.SignalizerFunctorTheorem.McBride.Defs
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.SignalizerFunctorTheorem.ElementaryAbelian

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem centralizer_zpowers_eq_singleton (a : G) :
    Subgroup.centralizer (Subgroup.zpowers a : Set G) = Subgroup.centralizer {a} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem comm_of_mem_of_isMulCommutative {B : Subgroup G} (hB : IsMulCommutative B) {x y : G}
    (hx : x ∈ B) (hy : y ∈ B) : x * y = y * x := by
  have := hB
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩)

theorem zpowers_mem_signalizerFunctorEk_one (hp : p.Prime) (hA : IsElemAbelian p A) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) : Subgroup.zpowers a ∈ signalizerFunctorEk p 1 A := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨Subgroup.zpowers_le.mpr ha, ?_⟩
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_eq_prime (hA.2 a ha) ha1

theorem exists_zpowers_eq_of_mem_signalizerFunctorEk_one (hp : p.Prime)
    {S : Subgroup G} (hS : S ∈ signalizerFunctorEk p 1 A) :
    ∃ a ∈ A, a ≠ 1 ∧ Subgroup.zpowers a = S := by
  have hcard : Nat.card S = p := by rw [hS.2, pow_one]
  have : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have hne : S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    exact hp.one_lt.ne hcard
  obtain ⟨⟨a, haS⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  refine ⟨a, hS.1 haS, ha1', ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haS) ?_
  rw [hcard, Nat.card_zpowers]
  have hdvd : orderOf a ∣ p := hcard ▸ Subgroup.orderOf_dvd_natCard S haS
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) ha1'
  · exact h.ge

theorem IsFunctor.le_of_mem_zpowers (hθ : IsFunctor p A θ) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ Subgroup.zpowers a) (hb1 : b ≠ 1) : θ a ≤ θ b := by
  intro x hx
  refine hθ.balance a ha ha1 b (Subgroup.zpowers_le.mpr ha hb) hb1 ⟨hx, ?_⟩
  have hxa : x ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [centralizer_zpowers_eq_singleton]
    exact hθ.le_centralizer a ha ha1 hx
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb) hxa

theorem IsFunctor.eq_of_zpowers_eq (hθ : IsFunctor p A θ) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) (h : Subgroup.zpowers a = Subgroup.zpowers b) : θ a = θ b :=
  le_antisymm (hθ.le_of_mem_zpowers ha ha1 (h ▸ Subgroup.mem_zpowers b) hb1)
    (hθ.le_of_mem_zpowers hb hb1 (h ▸ Subgroup.mem_zpowers a) ha1)

theorem IsFunctor.inf_centralizer_comm (hθ : IsFunctor p A θ) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) :
    θ a ⊓ Subgroup.centralizer {b} = θ b ⊓ Subgroup.centralizer {a} := by
  refine le_antisymm (le_inf (hθ.balance a ha ha1 b hb hb1) ?_)
    (le_inf (hθ.balance b hb hb1 a ha ha1) ?_)
  · exact inf_le_left.trans (hθ.le_centralizer a ha ha1)
  · exact inf_le_left.trans (hθ.le_centralizer b hb hb1)

theorem mem_thetaOf_iff {B : Subgroup G} {x : G} :
    x ∈ thetaOf θ B ↔ ∀ b ∈ B, b ≠ 1 → x ∈ θ b := by
  simp only [thetaOf, Subgroup.mem_iInf]

theorem le_thetaOf_iff {B X : Subgroup G} :
    X ≤ thetaOf θ B ↔ ∀ b ∈ B, b ≠ 1 → X ≤ θ b := by
  simp only [thetaOf, le_iInf_iff]

theorem thetaOf_le_apply {B : Subgroup G} {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    thetaOf θ B ≤ θ b :=
  le_thetaOf_iff.mp le_rfl b hb hb1

theorem thetaOf_anti {B B' : Subgroup G} (h : B ≤ B') : thetaOf θ B' ≤ thetaOf θ B :=
  le_thetaOf_iff.mpr fun _ hb hb1 => thetaOf_le_apply (h hb) hb1

theorem thetaOf_bot : thetaOf θ (⊥ : Subgroup G) = ⊤ := by
  rw [eq_top_iff, le_thetaOf_iff]
  intro b hb hb1
  exact absurd (Subgroup.mem_bot.mp hb) hb1

theorem IsFunctor.thetaOf_le_centralizer (hθ : IsFunctor p A θ) {B : Subgroup G} (hB : B ≤ A) :
    thetaOf θ B ≤ Subgroup.centralizer (B : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  by_cases hb1 : b = 1
  · rw [hb1, one_mul, mul_one]
  · exact Subgroup.mem_centralizer_iff.mp
      (hθ.le_centralizer b (hB hb) hb1 (thetaOf_le_apply hb hb1 hx)) b rfl

theorem IsFunctor.normalizes_thetaOf (hθ : IsFunctor p A θ) {B : Subgroup G} (hB : B ≤ A) :
    A ≤ Subgroup.normalizer (thetaOf θ B : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  rw [mem_thetaOf_iff] at hy ⊢
  intro b hb hb1
  exact Subgroup.le_normalizer_iff.mp (hθ.normalized b (hB hb) hb1) x hx y (hy b hb hb1)

theorem IsFunctor.coprime_thetaOf (hθ : IsFunctor p A θ) {B : Subgroup G} (hB : B ≤ A)
    (hB1 : B ≠ ⊥) : Nat.Coprime p (Nat.card (thetaOf θ B)) := by
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  exact (hθ.coprime b (hB hb) hb1').of_dvd_right
    (Subgroup.card_dvd_of_le (thetaOf_le_apply hb hb1'))

theorem IsFunctor.disjoint_thetaOf [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hθ : IsFunctor p A θ) {B : Subgroup G} (hB : B ≤ A) (hB1 : B ≠ ⊥) :
    Disjoint (thetaOf θ B) B := by
  have : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p B
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hB)
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hn]
  exact (hθ.coprime_thetaOf hB hB1).symm.pow_right n

theorem IsFunctor.thetaOf_zpowers (hθ : IsFunctor p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    thetaOf θ (Subgroup.zpowers a) = θ a :=
  le_antisymm (thetaOf_le_apply (Subgroup.mem_zpowers a) ha1)
    (le_thetaOf_iff.mpr fun _ hb hb1 => hθ.le_of_mem_zpowers ha ha1 hb hb1)

theorem IsFunctor.inf_centralizer_eq_thetaOf (hθ : IsFunctor p A θ) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {B : Subgroup G} (hB : B ≤ A) :
    θ a ⊓ Subgroup.centralizer (B : Set G) = thetaOf θ (Subgroup.zpowers a ⊔ B) := by
  have hsup : Subgroup.zpowers a ⊔ B ≤ A := sup_le (Subgroup.zpowers_le.mpr ha) hB
  apply le_antisymm
  · intro x hx
    rw [mem_thetaOf_iff]
    intro y hy hy1
    refine hθ.balance a ha ha1 y (hsup hy) hy1 ⟨hx.1, ?_⟩
    have hxa : x ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
      rw [centralizer_zpowers_eq_singleton]
      exact hθ.le_centralizer a ha ha1 hx.1
    have hxs : x ∈ Subgroup.centralizer ((Subgroup.zpowers a ⊔ B : Subgroup G) : Set G) := by
      rw [centralizer_sup]
      exact ⟨hxa, hx.2⟩
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hy) hxs
  · intro x hx
    refine ⟨thetaOf_le_apply (le_sup_left (a := Subgroup.zpowers a) (b := B)
      (Subgroup.mem_zpowers a)) ha1 hx, ?_⟩
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right)
      (hθ.thetaOf_le_centralizer hsup hx)

theorem IsFunctor.inf_centralizer_self (hθ : IsFunctor p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    θ a ⊓ Subgroup.centralizer (A : Set G) = thetaOf θ A := by
  have := hθ.inf_centralizer_eq_thetaOf ha ha1 (le_refl A)
  rwa [sup_eq_right.mpr (Subgroup.zpowers_le.mpr ha)] at this

variable {P : Subgroup G → Prop} {X : Subgroup G}

theorem mem_signalizers_iff : X ∈ signalizers p A θ P ↔
    A ≤ Subgroup.normalizer (X : Set G) ∧ Nat.Coprime p (Nat.card X) ∧
      (∀ a ∈ A, a ≠ 1 → X ⊓ Subgroup.centralizer {a} ≤ θ a) ∧ P X := Iff.rfl

theorem signalizers_mono_class {Q : Subgroup G → Prop} (h : ∀ X, P X → Q X) :
    signalizers p A θ P ⊆ signalizers p A θ Q :=
  fun X hX => ⟨hX.1, hX.2.1, hX.2.2.1, h X hX.2.2.2⟩

theorem signalizers_mono_functor {θ' : G → Subgroup G}
    (h : ∀ a ∈ A, a ≠ 1 → θ a ≤ θ' a) : signalizers p A θ P ⊆ signalizers p A θ' P :=
  fun _ hX => ⟨hX.1, hX.2.1, fun a ha ha1 => (hX.2.2.1 a ha ha1).trans (h a ha ha1),
    hX.2.2.2⟩

theorem mem_signalizers_of_le (hX : X ∈ signalizers p A θ P) {Y : Subgroup G} (hYX : Y ≤ X)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hP : P X → P Y) :
    Y ∈ signalizers p A θ P :=
  ⟨hAY, hX.2.1.of_dvd_right (Subgroup.card_dvd_of_le hYX),
    fun a ha ha1 => (inf_le_inf_right _ hYX).trans (hX.2.2.1 a ha ha1), hP hX.2.2.2⟩

theorem IsFunctor.apply_mem_signalizers (hθ : IsFunctor p A θ) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) (hP : P (θ a)) : θ a ∈ signalizers p A θ P :=
  ⟨hθ.normalized a ha ha1, hθ.coprime a ha ha1,
    fun b hb hb1 => hθ.balance a ha ha1 b hb hb1, hP⟩

theorem IsFunctor.thetaOf_mem_signalizers (hθ : IsFunctor p A θ) {B : Subgroup G} (hB : B ≤ A)
    (hB1 : B ≠ ⊥) (hP : P (thetaOf θ B)) : thetaOf θ B ∈ signalizers p A θ P := by
  refine ⟨hθ.normalizes_thetaOf hB, hθ.coprime_thetaOf hB hB1, fun a ha ha1 => ?_, hP⟩
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  exact (inf_le_inf_right _ (thetaOf_le_apply hb hb1')).trans
    (hθ.balance b (hB hb) hb1' a ha ha1)

theorem inf_centralizer_le_thetaOf (hX : X ∈ signalizers p A θ P) {B : Subgroup G} (hB : B ≤ A) :
    X ⊓ Subgroup.centralizer (B : Set G) ≤ thetaOf θ B := by
  intro x hx
  rw [mem_thetaOf_iff]
  intro b hb hb1
  refine hX.2.2.1 b (hB hb) hb1 ⟨hx.1, ?_⟩
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb) hx.2

theorem inf_centralizer_mem_signalizers (hX : X ∈ signalizers p A θ P) {B : Subgroup G}
    (hB : B ≤ A) (hA : IsMulCommutative A)
    (hmono : ∀ Y, Y ≤ X → A ≤ Subgroup.normalizer (Y : Set G) → P X → P Y) :
    X ⊓ Subgroup.centralizer (B : Set G) ∈ signalizers p A θ P := by
  have hAY : A ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) :
      Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    refine Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer_iff.mp hX.1 x hx y hy.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbx : Commute b x := comm_of_mem_of_isMulCommutative hA (hB hb) hx
    have hby : Commute b y := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 b hb
    exact (hbx.mul_right hby).mul_right hbx.inv_right
  exact ⟨hAY, hX.2.1.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left),
    fun a ha ha1 => (inf_le_inf_right _ inf_le_left).trans (hX.2.2.1 a ha ha1),
    hmono _ inf_le_left hAY hX.2.2.2⟩

@[expose] def thetaSup (A : Subgroup G) (θ : G → Subgroup G) : Subgroup G :=
  ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), θ a

theorem le_thetaSup {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) : θ a ≤ thetaSup A θ :=
  le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl))

theorem thetaSup_le {H : Subgroup G} (h : ∀ a ∈ A, a ≠ 1 → θ a ≤ H) : thetaSup A θ ≤ H :=
  iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => h a ha ha1

theorem thetaSup_mono {B : Subgroup G} (h : B ≤ A) : thetaSup B θ ≤ thetaSup A θ :=
  thetaSup_le fun _ ha ha1 => le_thetaSup (h ha) ha1

theorem IsFunctor.normalizes_thetaSup (hθ : IsFunctor p A θ) :
    A ≤ Subgroup.normalizer (thetaSup A θ : Set G) := by
  refine CFSG.SignalizerFunctor.Helpers.normalizer_iSup_of_le A _ fun a => ?_
  refine CFSG.SignalizerFunctor.Helpers.normalizer_iSup_of_le A _ fun ha => ?_
  refine CFSG.SignalizerFunctor.Helpers.normalizer_iSup_of_le A _ fun ha1 => ?_
  exact hθ.normalized a ha ha1

theorem iSup_inf_centralizer [Finite G] (hp : p.Prime) {B : Subgroup G} (hB : IsElemAbelian p B)
    (hrank : p ^ 2 ≤ Nat.card B) {X : Subgroup G} (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hX : Nat.Coprime p (Nat.card X)) :
    (⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), X ⊓ Subgroup.centralizer {b}) = X := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation p 1 hp B
    X hB hrank hBX hX
  apply le_antisymm
  · exact iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => inf_le_left
  · calc X = ⨆ S ∈ signalizerFunctorEk p 1 B, X ⊓ Subgroup.centralizer (S : Set G) := hgen.symm
      _ ≤ _ := by
        refine iSup_le fun S => iSup_le fun hS => ?_
        obtain ⟨b, hb, hb1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one hp hS
        rw [centralizer_zpowers_eq_singleton]
        exact le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl))

theorem iSup_inf_centralizer_sdiff [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    {E : Subgroup G} (hEA : E ≤ A) (hrank : p ^ 2 * Nat.card E ≤ Nat.card A) {X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hX : Nat.Coprime p (Nat.card X)) :
    (⨆ (b : G) (_ : b ∈ A) (_ : b ∉ E), X ⊓ Subgroup.centralizer {b}) = X := by
  obtain ⟨F, hFA, -, hEF, hsup⟩ := exists_complement_containing hp hA hEA bot_le (inf_bot_eq E)
  have hcard := card_mul_card_complement hA hEA hFA hEF hsup
  have hEpos : 0 < Nat.card E := Nat.card_pos
  have hF2 : p ^ 2 ≤ Nat.card F := by
    refine Nat.le_of_mul_le_mul_left ?_ hEpos
    rw [hcard, mul_comm]
    exact hrank
  have hgen := iSup_inf_centralizer hp (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le
    p hA hFA) hF2 (hFA.trans hAX) hX
  apply le_antisymm
  · exact iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => inf_le_left
  · calc X = ⨆ (b : G) (_ : b ∈ F) (_ : b ≠ 1), X ⊓ Subgroup.centralizer {b} := hgen.symm
      _ ≤ _ := by
        refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
        refine le_iSup_of_le b (le_iSup_of_le (hFA hb) (le_iSup_of_le ?_ le_rfl))
        intro hbE
        exact hb1 (Subgroup.mem_bot.mp (hEF ▸ Subgroup.mem_inf.mpr ⟨hbE, hb⟩))

theorem le_thetaSup_of_mem_signalizers [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    {B : Subgroup G} (hBA : B ≤ A) (hrank : p ^ 2 ≤ Nat.card B)
    (hX : X ∈ signalizers p A θ P) : X ≤ thetaSup B θ := by
  have hB : IsElemAbelian p B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hBA
  calc X = ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), X ⊓ Subgroup.centralizer {b} :=
        (iSup_inf_centralizer hp hB hrank (hBA.trans hX.1) hX.2.1).symm
    _ ≤ thetaSup B θ := by
      refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
      exact (hX.2.2.1 b (hBA hb) hb1).trans (le_thetaSup hb hb1)

theorem sSup_signalizers_eq_thetaSup [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hrank : p ^ 2 ≤ Nat.card A) (hθ : IsFunctor p A θ)
    (hP : ∀ a ∈ A, a ≠ 1 → P (θ a)) : sSup (signalizers p A θ P) = thetaSup A θ :=
  le_antisymm (sSup_le fun _ hX => le_thetaSup_of_mem_signalizers hp hA le_rfl hrank hX)
    (thetaSup_le fun a ha ha1 => le_sSup (hθ.apply_mem_signalizers ha ha1 (hP a ha ha1)))

theorem IsFunctor.apply_eq_iSup_thetaOf [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hrank : p ^ 3 ≤ Nat.card A) (hθ : IsFunctor p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    θ a = ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : Nat.card B = p ^ 2) (_ : a ∈ B), thetaOf θ B := by
  apply le_antisymm
  · have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation p 2 hp A
      (θ a) hA hrank (hθ.normalized a ha ha1) (hθ.coprime a ha ha1)
    calc θ a = ⨆ S ∈ signalizerFunctorEk p 2 A, θ a ⊓ Subgroup.centralizer (S : Set G) :=
          hgen.symm
      _ ≤ _ := by
        refine iSup_le fun S => iSup_le fun hS => ?_
        by_cases haS : a ∈ S
        · have hsup : Subgroup.zpowers a ⊔ S = S := sup_eq_right.mpr (Subgroup.zpowers_le.mpr haS)
          have := hθ.inf_centralizer_eq_thetaOf ha ha1 hS.1
          rw [hsup] at this
          rw [this]
          exact le_iSup_of_le S (le_iSup_of_le hS.1 (le_iSup_of_le hS.2 (le_iSup_of_le haS le_rfl)))
        · obtain ⟨s, hsS, hs1⟩ : ∃ s ∈ S, s ≠ 1 := by
            by_contra hcon
            push Not at hcon
            have hSbot : S = ⊥ := Subgroup.eq_bot_iff_forall S |>.mpr hcon
            have : Nat.card S = 1 := by rw [hSbot, Subgroup.card_bot]
            rw [hS.2] at this
            have hp1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
            omega
          have hsA : s ∈ A := hS.1 hsS
          have hcs : Nat.card (Subgroup.zpowers s) = p := by
            rw [(zpowers_mem_signalizerFunctorEk_one hp hA hsA hs1).2, pow_one]
          have hca : Nat.card (Subgroup.zpowers a) = p := by
            rw [(zpowers_mem_signalizerFunctorEk_one hp hA ha ha1).2, pow_one]
          have hna : ¬ Subgroup.zpowers a ≤ Subgroup.zpowers s := fun h =>
            haS (Subgroup.zpowers_le.mpr hsS (h (Subgroup.mem_zpowers a)))
          have hdisj : Subgroup.zpowers s ⊓ Subgroup.zpowers a = ⊥ :=
            inf_eq_bot_of_not_le hp hca hna
          set B := Subgroup.zpowers s ⊔ Subgroup.zpowers a with hBdef
          have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr hsA) (Subgroup.zpowers_le.mpr ha)
          have hBcard : Nat.card B = p ^ 2 := by
            rw [hBdef, card_sup_of_le_elemAbelian hA (Subgroup.zpowers_le.mpr hsA)
              (Subgroup.zpowers_le.mpr ha) hdisj, hcs, hca, sq]
          have haB : a ∈ B := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
          have hBeq : Subgroup.zpowers a ⊔ B = B := sup_eq_right.mpr (Subgroup.zpowers_le.mpr haB)
          have hthB := hθ.inf_centralizer_eq_thetaOf ha ha1 hBA
          rw [hBeq] at hthB
          have hle : θ a ⊓ Subgroup.centralizer (S : Set G) ≤
              θ a ⊓ Subgroup.centralizer (B : Set G) := by
            intro x hx
            refine ⟨hx.1, ?_⟩
            have hxa : x ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
              rw [centralizer_zpowers_eq_singleton]
              exact hθ.le_centralizer a ha ha1 hx.1
            have hxs : x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set G) :=
              Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (Subgroup.zpowers_le.mpr hsS))
                hx.2
            rw [hBdef, centralizer_sup]
            exact ⟨hxs, hxa⟩
          refine hle.trans (hthB ▸ le_iSup_of_le B (le_iSup_of_le hBA (le_iSup_of_le hBcard
            (le_iSup_of_le haB le_rfl))))
  · exact iSup_le fun B => iSup_le fun hBA => iSup_le fun hBc => iSup_le fun haB =>
      thetaOf_le_apply haB ha1

theorem eq_thetaSup_of_forall_le [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hrank : p ^ 2 ≤ Nat.card A) (hθ : IsFunctor p A θ) (hP : ∀ a ∈ A, a ≠ 1 → P (θ a))
    {W : Subgroup G} (hW : W ∈ signalizers p A θ P)
    (hmax : ∀ X ∈ signalizers p A θ P, X ≤ W) : W = thetaSup A θ :=
  le_antisymm (le_thetaSup_of_mem_signalizers hp hA le_rfl hrank hW)
    (thetaSup_le fun a ha ha1 => hmax _ (hθ.apply_mem_signalizers ha ha1 (hP a ha ha1)))

theorem isCompleteIn_iff_thetaSup_mem [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hrank : p ^ 2 ≤ Nat.card A) (hθ : IsFunctor p A θ) (hP : ∀ a ∈ A, a ≠ 1 → P (θ a)) :
    IsCompleteIn (signalizers p A θ P) ↔ thetaSup A θ ∈ signalizers p A θ P := by
  constructor
  · rintro ⟨W, hW, hmax⟩
    have : W = thetaSup A θ := eq_thetaSup_of_forall_le hp hA hrank hθ hP hW hmax
    exact this ▸ hW
  · exact fun h => ⟨_, h, fun X hX => le_thetaSup_of_mem_signalizers hp hA le_rfl hrank hX⟩

theorem isCompleteIn_iff_exists_apply_le [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hrank : p ^ 2 ≤ Nat.card A) (hθ : IsFunctor p A θ) (hP : ∀ a ∈ A, a ≠ 1 → P (θ a)) :
    IsCompleteIn (signalizers p A θ P) ↔
      ∃ X ∈ signalizers p A θ P, ∀ a ∈ A, a ≠ 1 → θ a ≤ X := by
  constructor
  · rintro ⟨W, hW, hmax⟩
    exact ⟨W, hW, fun a ha ha1 => hmax _ (hθ.apply_mem_signalizers ha ha1 (hP a ha ha1))⟩
  · rintro ⟨X, hX, hle⟩
    refine (isCompleteIn_iff_thetaSup_mem hp hA hrank hθ hP).mpr ?_
    have : thetaSup A θ = X := le_antisymm (thetaSup_le hle)
      (le_thetaSup_of_mem_signalizers hp hA le_rfl hrank hX)
    exact this ▸ hX

theorem isCompleteIn_of_isLocallyCompleteIn [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hθ : IsFunctor p A θ) (hP : ∀ a ∈ A, a ≠ 1 → P (θ a))
    (hloc : IsLocallyCompleteIn (signalizers p A θ P)) (hX : X ∈ signalizers p A θ P)
    (hX1 : X ≠ ⊥) {B : Subgroup G} (hBA : B ≤ A) (hB : p ^ 2 ≤ Nat.card B)
    (hnorm : ∀ b ∈ B, b ≠ 1 → θ b ≤ Subgroup.normalizer (X : Set G)) :
    IsCompleteIn (signalizers p A θ P) := by
  obtain ⟨Y, hY, hYN, hYmax⟩ := hloc X hX hX1
  refine ⟨Y, hY, fun Z hZ => ?_⟩
  refine (le_thetaSup_of_mem_signalizers hp hA hBA hB hZ).trans (thetaSup_le fun b hb hb1 => ?_)
  exact hYmax _ (hθ.apply_mem_signalizers (hBA hb) hb1 (hP b (hBA hb) hb1)) (hnorm b hb hb1)

theorem isCompleteIn_iff_existsUnique_maximal [Finite G] (S : Set (Subgroup G)) :
    IsCompleteIn S ↔ ∃! W, Maximal (· ∈ S) W := by
  constructor
  · rintro ⟨W, hW, hmax⟩
    refine ⟨W, ⟨hW, fun y hy _ => hmax y hy⟩, fun W' hW' => ?_⟩
    exact le_antisymm (hmax W' hW'.1) (hW'.2 hW (hmax W' hW'.1))
  · rintro ⟨W, hW, huniq⟩
    refine ⟨W, hW.1, fun X hX => ?_⟩
    obtain ⟨W', hXW', hW'max⟩ := Finite.exists_le_maximal (p := (· ∈ S)) hX
    exact huniq W' hW'max ▸ hXW'

end CFSG.SignalizerFunctorTheorem.McBride
