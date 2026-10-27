module

public import CFSG.Quasithin.H13.A6S1356Two
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Block

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement Pointwise

@[expose] def InW0 (x : P6) : Prop := x = 1 ∨ x = dv 0 1 ∨ x = dv 1 2 ∨ x = dv 0 2

instance : DecidablePred InW0 := fun x => by unfold InW0; infer_instance

@[expose] def W0sub : Subgroup ↥W4 where
  carrier := {y | InW0 (y : P6)}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => (by
    have key : ∀ a b : P6, InW0 a → InW0 b → InW0 (a * b) := by decide +kernel
    exact key _ _ ha hb)
  inv_mem' := fun {a} ha => (by
    have key : ∀ a : P6, InW0 a → InW0 a⁻¹ := by decide +kernel
    exact key _ ha)

theorem card_W0sub : Nat.card ↥W0sub = 4 := by
  have : Fintype.card {y : ↥W4 // InW0 (y : P6)} = 4 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

@[expose] def NondegWit (a b : P6) : Prop :=
  ∃ σ : Perm (Fin 6), (∀ y : P6, InW0 y → act4f σ y = 1 ∨ act4f σ y = a ∨ act4f σ y = b ∨
    act4f σ y = a * b) ∧ Perm.sign σ = 1

instance (a b : P6) : Decidable (NondegWit a b) := by unfold NondegWit; infer_instance

theorem nondegWit : ∀ a b : P6, PairHyp a b → dot a b = 1 → NondegWit a b := by
  have key : ∀ a : P6, InW4 a → a ≠ 1 → ∀ b : P6, InW4 b → b ≠ 1 → a ≠ b → dot a b = 1 →
      ∃ σ ∈ [1, swap 2 3 * swap 4 5, swap 2 4 * swap 3 4, swap 2 5 * swap 3 5,
        swap 1 2 * swap 2 3, swap 1 2 * swap 2 4 * swap 3 4 * swap 4 5,
        swap 1 2 * swap 2 5 * swap 3 5 * swap 4 5, swap 1 3 * swap 2 4, swap 1 3 * swap 2 5,
        swap 1 4 * swap 2 5 * swap 3 4 * swap 4 5, swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5,
        swap 0 1 * swap 1 2 * swap 2 4 * swap 3 4, swap 0 1 * swap 1 2 * swap 2 5 * swap 3 5,
        swap 0 1 * swap 1 3 * swap 2 4 * swap 4 5, swap 0 1 * swap 1 3 * swap 2 5 * swap 4 5,
        swap 0 1 * swap 1 4 * swap 2 5 * swap 3 4, swap 0 2 * swap 1 3 * swap 2 4 * swap 3 4,
        swap 0 2 * swap 1 3 * swap 2 5 * swap 3 5, swap 0 2 * swap 1 4 * swap 2 5 * swap 3 5,
        swap (0 : Fin 6) 3 * swap 1 4 * swap 2 5 * swap 4 5],
      (∀ y ∈ [1, dv 0 1, dv 1 2, dv 0 2], act4f σ y = 1 ∨ act4f σ y = a ∨ act4f σ y = b ∨
        act4f σ y = a * b) ∧ Perm.sign σ = 1 := by
    set_option synthInstance.maxHeartbeats 1000000 in
    set_option synthInstance.maxSize 4096 in
    decide +kernel
  intro a b ⟨ha, hb, ha1, hb1, hab⟩ hd
  obtain ⟨σ, -, hσ, hs⟩ := key a ha ha1 b hb hb1 hab hd
  refine ⟨σ, fun y hy => hσ y ?_, hs⟩
  rcases hy with rfl | rfl | rfl | rfl <;> simp

theorem D_inv_mul_swap45 : ∀ δ : Perm (Fin 6), InD6 δ → InD6 (δ⁻¹ * swap 4 5) := by
  decide +kernel

theorem sign_inv_mul_swap45 {δ : Perm (Fin 6)} (h : Perm.sign δ ≠ 1) :
    Perm.sign (δ⁻¹ * swap 4 5) = 1 := by
  rw [Perm.sign_mul, Perm.sign_inv, Perm.sign_swap (by decide)]
  rcases Int.units_eq_one_or (Perm.sign δ) with h1 | h1
  · exact absurd h1 h
  · rw [h1]
    decide

@[expose] def Z45 : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ = 1 ∨ σ = swap 4 5}
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (mul_one 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl (swap_mul_self 4 5)
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (swap_inv 4 5)

theorem z45_fix_W0 : ∀ x : P6, InW0 x → act4f 1 x = x ∧ act4f (swap 4 5) x = x := by
  decide +kernel

theorem z45_fix_W2 : ∀ x : P6, InW2 x → act4f 1 x = x ∧ act4f (swap 4 5) x = x := by
  decide +kernel

theorem fix_W0_comm45 : ∀ σ : Perm (Fin 6), σ ^ 4 = 1 → act4f σ (dv 0 1) = dv 0 1 →
    act4f σ (dv 1 2) = dv 1 2 → σ * swap 4 5 = swap 4 5 * σ → σ = 1 ∨ σ = swap 4 5 := by
  decide +kernel

theorem dv_mem_W0 : (InW4 (dv 0 1) ∧ InW0 (dv 0 1)) ∧ (InW4 (dv 1 2) ∧ InW0 (dv 1 2)) := by
  decide

theorem k0_not_mem_Z45 : swap (0 : Fin 6) 1 * swap 2 3 ∉ Z45 := by
  show ¬ (swap (0 : Fin 6) 1 * swap 2 3 = 1 ∨ swap (0 : Fin 6) 1 * swap 2 3 = swap 4 5)
  decide

theorem swap45_ne_one : swap (4 : Fin 6) 5 ≠ 1 := by decide

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

@[expose] noncomputable def W0 : Subgroup G := S.pre W0sub

theorem card_W0 : Nat.card ↥S.W0 = 4 := by rw [W0, S.card_pre, card_W0sub]

theorem W0_le_V : S.W0 ≤ V := Subgroup.map_subtype_le _

theorem W0_ne_bot : S.W0 ≠ ⊥ := by
  intro h
  have := S.card_W0
  rw [h, Subgroup.card_bot] at this
  omega

theorem conjSub_pre_eq {Y : Subgroup ↥W4} (hY : Nat.card ↥(S.pre Y) = 4) {W : Subgroup G}
    (hW : W ≤ V) (hWcard : Nat.card W = 4) {a b : G} (ha : a ∈ W) (hb : b ∈ W)
    (l : ↥(Subgroup.normalizer (V : Set G)))
    (hmap : ∀ y : ↥W4, y ∈ Y → act4f (S.frame.ρ l) (y : P6) = 1 ∨
      act4f (S.frame.ρ l) (y : P6) = (S.frame.ψ ⟨a, hW ha⟩ : P6) ∨
      act4f (S.frame.ρ l) (y : P6) = (S.frame.ψ ⟨b, hW hb⟩ : P6) ∨
      act4f (S.frame.ρ l) (y : P6) =
        (S.frame.ψ ⟨a, hW ha⟩ : P6) * (S.frame.ψ ⟨b, hW hb⟩ : P6)) :
    conjSub (l : G) (S.pre Y) = W := by
  have hinj : ∀ (u v : ↥V), (S.frame.ψ u : P6) = (S.frame.ψ v : P6) → (u : G) = v := by
    intro u v h
    exact congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    rw [mem_conjSub] at hx
    obtain ⟨hyV, hyY⟩ := S.mem_pre.1 hx
    have hxy : x = l * ((l : G)⁻¹ * x * l) * (l : G)⁻¹ := by group
    have hxV : x ∈ V := by
      rw [hxy]
      exact (Subgroup.mem_normalizer_iff.mp l.2 _).mp hyV
    have hψ : (S.frame.ψ ⟨x, hxV⟩ : P6) =
        act4f (S.frame.ρ l) (S.frame.ψ ⟨(l : G)⁻¹ * x * l, hyV⟩ : P6) := by
      have h1 := S.psi_conj l ⟨(l : G)⁻¹ * x * l, hyV⟩
      have e : (⟨x, hxV⟩ : ↥V) = ⟨l * ((l : G)⁻¹ * x * l) * (l : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp l.2 _).mp hyV⟩ := Subtype.ext hxy
      rw [e, h1]
      rfl
    rcases hmap _ hyY with h | h | h | h <;> rw [← hψ] at h
    · have hx1 : x = ((1 : ↥V) : G) := hinj ⟨x, hxV⟩ 1 (by rw [map_one]; exact h)
      rw [hx1]
      exact W.one_mem
    · have hxa : x = a := hinj ⟨x, hxV⟩ ⟨a, hW ha⟩ h
      rw [hxa]
      exact ha
    · have hxb : x = b := hinj ⟨x, hxV⟩ ⟨b, hW hb⟩ h
      rw [hxb]
      exact hb
    · have hxab : x = a * b :=
        hinj ⟨x, hxV⟩ (⟨a, hW ha⟩ * ⟨b, hW hb⟩) (by rw [map_mul]; exact h)
      rw [hxab]
      exact W.mul_mem ha hb
  · rw [hWcard, A5.card_conjSub', hY]

theorem exists_pairHyp {W : Subgroup G} (hW : W ≤ V) (hcardW : Nat.card W = 4) :
    ∃ a, ∃ ha : a ∈ W, ∃ b, ∃ hb : b ∈ W,
      PairHyp (S.frame.ψ ⟨a, hW ha⟩ : P6) (S.frame.ψ ⟨b, hW hb⟩ : P6) := by
  classical
  obtain ⟨a, haW, ha1⟩ : ∃ a ∈ W, a ≠ 1 := by
    by_contra h
    push Not at h
    have : W = ⊥ := (Subgroup.eq_bot_iff_forall W).2 h
    rw [this, Subgroup.card_bot] at hcardW
    omega
  obtain ⟨b, hbW, hb1, hba⟩ : ∃ b ∈ W, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : (W : Set G) ⊆ {1, a} := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (h x hx hx1)
    have : Nat.card W ≤ 2 := by
      calc Nat.card W = Nat.card (W : Set G) := rfl
        _ ≤ Nat.card ({1, a} : Set G) := Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by simp)
    omega
  have hinj : ∀ (u v : ↥V), (S.frame.ψ u : P6) = (S.frame.ψ v : P6) → (u : G) = v := by
    intro u v h
    exact congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
  refine ⟨a, haW, b, hbW, (S.frame.ψ _).2, (S.frame.ψ _).2, fun h => ha1 ?_, fun h => hb1 ?_,
    fun h => hba (hinj _ _ h).symm⟩
  · have := hinj ⟨a, hW haW⟩ 1 (by rw [map_one]; exact h)
    simpa using this
  · have := hinj ⟨b, hW hbW⟩ 1 (by rw [map_one]; exact h)
    simpa using this

theorem exists_L_conjSub_W0 {W : Subgroup G} (hW : W ≤ V) (hWcard : Nat.card W = 4) {a b : G}
    (ha : a ∈ W) (hb : b ∈ W)
    (hpair : PairHyp (S.frame.ψ ⟨a, hW ha⟩ : P6) (S.frame.ψ ⟨b, hW hb⟩ : P6))
    (hdot : dot (S.frame.ψ ⟨a, hW ha⟩ : P6) (S.frame.ψ ⟨b, hW hb⟩ : P6) = 1) :
    ∃ l : ↥(Subgroup.normalizer (V : Set G)), (l : G) ∈ L ∧ conjSub (l : G) S.W0 = W := by
  obtain ⟨σ, hσW, hσs⟩ := nondegWit _ _ hpair hdot
  obtain ⟨l, hlL, hl⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 hσs)
  refine ⟨l, hlL, S.conjSub_pre_eq (Y := W0sub) S.card_W0 hW hWcard ha hb l fun y hy => ?_⟩
  rw [hl]
  exact hσW _ hy

theorem conjAct_eq_of_rho_eq' {x y : ↥(Subgroup.normalizer (V : Set G))}
    (h : S.frame.ρ x = S.frame.ρ y) : conjAct V x = conjAct V y := by
  refine MulEquiv.ext fun v => ?_
  apply S.frame.ψ.injective
  rw [S.frame.equiv, S.frame.equiv, h]

theorem conjAct_eq_one_iff' (x : ↥(Subgroup.normalizer (V : Set G))) :
    conjAct V x = 1 ↔ S.frame.ρ x = 1 := by
  constructor
  · intro h
    have := S.rho_eq_of_conjAct_eq (x := x) (y := 1) (by rw [h, map_one])
    rwa [map_one] at this
  · intro h
    rw [← map_one (conjAct V)]
    exact S.conjAct_eq_of_rho_eq' (by rw [h, map_one])

theorem exists_T_odd (hS6 : ¬ autOn T V ≤ autOn L V) :
    ∃ t : ↥(Subgroup.normalizer (V : Set G)), (t : G) ∈ T ∧ Perm.sign (S.frame.ρ t) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hS6
  rintro _ ⟨t, htT, rfl⟩
  obtain ⟨l, hlL, hl⟩ := (S.frame.image_L (S.frame.ρ t)).2
    (Perm.mem_alternatingGroup.2 (hcon t htT))
  exact ⟨l, hlL, S.conjAct_eq_of_rho_eq' hl⟩

theorem exists_T_45 (hS6 : ¬ autOn T V ≤ autOn L V) :
    ∃ t : ↥(Subgroup.normalizer (V : Set G)), (t : G) ∈ T ∧ S.frame.ρ t = swap 4 5 := by
  obtain ⟨t₀, ht₀T, ht₀⟩ := S.exists_T_odd hS6
  obtain ⟨t₁, ht₁T, ht₁⟩ := S.frame.DA_T _ (D_inv_mul_swap45 _ (S.frame.T_D t₀ ht₀T))
    (Perm.mem_alternatingGroup.2 (sign_inv_mul_swap45 ht₀))
  refine ⟨t₀ * t₁, T.mul_mem ht₀T ht₁T, ?_⟩
  rw [map_mul, ht₁, ← mul_assoc, mul_inv_cancel, one_mul]

@[expose] noncomputable def R45 : Subgroup G :=
  T ⊓ (Z45.comap S.frame.ρ).map (Subgroup.normalizer (V : Set G)).subtype

theorem mem_R45 {x : G} : x ∈ S.R45 ↔
    x ∈ T ∧ ∃ h : x ∈ Subgroup.normalizer (V : Set G), S.frame.ρ ⟨x, h⟩ ∈ Z45 := by
  constructor
  · rintro ⟨hxT, y, hy, rfl⟩
    exact ⟨hxT, y.2, hy⟩
  · rintro ⟨hxT, h, hρ⟩
    exact ⟨hxT, ⟨x, h⟩, hρ, rfl⟩

theorem R45_le_T : S.R45 ≤ T := inf_le_left

theorem mem_R45_of {t : ↥(Subgroup.normalizer (V : Set G))} (ht : (t : G) ∈ T)
    (hρ : S.frame.ρ t ∈ Z45) : (t : G) ∈ S.R45 :=
  S.mem_R45.2 ⟨ht, t.2, hρ⟩

theorem Q_le_R45 : T ⊓ Subgroup.centralizer (V : Set G) ≤ S.R45 := fun _ hx =>
  S.mem_R45.2 ⟨hx.1, S.frame.T_le hx.1, Or.inl ((S.rho_eq_one_iff _).2 hx.2)⟩

theorem mem_centralizer_pre_of_fix {Y : Subgroup ↥W4} (x : ↥(Subgroup.normalizer (V : Set G)))
    (hx : ∀ y : ↥W4, y ∈ Y → act4f (S.frame.ρ x) (y : P6) = (y : P6)) :
    (x : G) ∈ Subgroup.centralizer (S.pre Y : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨hwV, hwY⟩ := S.mem_pre.1 hw
  have h : act4 (S.frame.ρ x) (S.frame.ψ ⟨w, hwV⟩) = S.frame.ψ ⟨w, hwV⟩ :=
    Subtype.ext (hx _ hwY)
  have := (S.conj_eq_iff x ⟨w, hwV⟩).2 h
  calc w * x = x * w * (x : G)⁻¹ * x := by rw [this]
    _ = x * w := by group

theorem R45_le_centralizer_W0 : S.R45 ≤ Subgroup.centralizer (S.W0 : Set G) := by
  intro x hx
  obtain ⟨-, h, hρ⟩ := S.mem_R45.1 hx
  refine S.mem_centralizer_pre_of_fix (Y := W0sub) ⟨x, h⟩ fun y hy => ?_
  rcases hρ with h1 | h1 <;> rw [h1]
  · exact (z45_fix_W0 _ hy).1
  · exact (z45_fix_W0 _ hy).2

theorem R45_le_CTV2 : S.R45 ≤ T ⊓ Subgroup.centralizer (S.V2 : Set G) := by
  intro x hx
  obtain ⟨hxT, h, hρ⟩ := S.mem_R45.1 hx
  refine ⟨hxT, S.mem_centralizer_pre_of_fix (Y := W2sub) ⟨x, h⟩ fun y hy => ?_⟩
  rcases hρ with h1 | h1 <;> rw [h1]
  · exact (z45_fix_W2 _ hy).1
  · exact (z45_fix_W2 _ hy).2

theorem card_R45_lt :
    Nat.card ↥S.R45 < Nat.card ↥(T ⊓ Subgroup.centralizer (S.V2 : Set G)) := by
  obtain ⟨t, htT, ht⟩ := S.frame.DA_T _ gens_DA.1.1 gens_DA.1.2
  have htV2 : (t : G) ∈ Subgroup.centralizer (S.V2 : Set G) :=
    S.mem_centralizer_pre_of_fix (Y := W2sub) t fun y hy => by
      rw [ht]
      exact k0_facts.1 _ hy
  have htR : (t : G) ∉ S.R45 := fun h => by
    obtain ⟨-, _, hρ⟩ := S.mem_R45.1 h
    have hρ' : S.frame.ρ t ∈ Z45 := hρ
    rw [ht] at hρ'
    exact k0_not_mem_Z45 hρ'
  by_contra hcon
  push Not at hcon
  have heq := Subgroup.eq_of_le_of_card_ge S.R45_le_CTV2 hcon
  exact htR (by rw [heq]; exact ⟨htT, htV2⟩)

theorem card_autOn_R45 {t : ↥(Subgroup.normalizer (V : Set G))} (htT : (t : G) ∈ T)
    (hρt : S.frame.ρ t = swap 4 5) : Nat.card ↥(autOn S.R45 V) = 2 := by
  have htR : (t : G) ∈ S.R45 := S.mem_R45_of htT (by rw [hρt]; exact Or.inr rfl)
  have heq : autOn S.R45 V = Subgroup.zpowers (conjAct V t) := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      obtain ⟨-, _, hρ⟩ := S.mem_R45.1 hr
      rcases hρ with h1 | h1
      · rw [(S.conjAct_eq_one_iff' r).2 h1]
        exact Subgroup.one_mem _
      · have h2 : S.frame.ρ r = S.frame.ρ t := by
          rw [hρt]
          exact h1
        rw [S.conjAct_eq_of_rho_eq' h2]
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact ⟨t, htR, rfl⟩
  rw [heq, Nat.card_zpowers]
  apply orderOf_eq_prime
  · have e : conjAct V t ^ 2 = conjAct V (t ^ 2) := (map_pow _ _ _).symm
    rw [e, S.conjAct_eq_one_iff', map_pow, hρt, pow_two, swap_mul_self]
  · rw [Ne, S.conjAct_eq_one_iff', hρt]
    exact swap45_ne_one

theorem normalizer_R45_not_le (h1222 : Stmt12_2_2)
    (hS6 : ¬ autOn T V ≤ autOn L V) {g : G} (hg : conjSub g S.V2 = S.W0) :
    ¬ Subgroup.normalizer (S.R45 : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro hN
  obtain ⟨t, htT, hρt⟩ := S.exists_T_45 hS6
  have htR : (t : G) ∈ S.R45 := S.mem_R45_of htT (by rw [hρt]; exact Or.inr rfl)
  have hR2 : IsPGroup 2 S.R45 := S.h13.sylow.1.to_le S.R45_le_T
  have hPC : conjSub g (T ⊓ Subgroup.centralizer (S.V2 : Set G)) ≤
      Subgroup.centralizer (S.W0 : Set G) := by
    rw [← hg, conjSub_centralizer]
    exact conjSub_mono g inf_le_right
  have hP2 : IsPGroup 2 (conjSub g (T ⊓ Subgroup.centralizer (S.V2 : Set G))) :=
    F7.isPGroup_conjSub (S.h13.sylow.1.to_le inf_le_left)
  have hRP : Nat.card S.R45 <
      Nat.card (conjSub g (T ⊓ Subgroup.centralizer (S.V2 : Set G))) := by
    rw [A5.card_conjSub']
    exact S.card_R45_lt
  obtain ⟨S', hS', hRS'⟩ := A4.exists_isSylowTwoOf_ge S.R45_le_centralizer_W0 hR2
  obtain ⟨x, -, hx⟩ := F7.isSylowTwoOf_exists_conj_le hS' hPC hP2
  have hPS' := (Subgroup.card_le_of_le hx).trans (A5.card_conjSub' x S').le
  have hlt : S.R45 < S' := lt_of_le_of_ne hRS' fun h => by
    rw [h] at hRP
    omega
  obtain ⟨s, hsS', hsR, hsN⟩ := A5.exists_mem_normalizer_not_mem hS'.2.1 hlt
  have hsC : s ∈ Subgroup.centralizer (S.W0 : Set G) := hS'.1 hsS'
  have hsV : s ∈ Subgroup.normalizer (V : Set G) :=
    S.mem_normalizer_V_of_TI h1222 (hN hsN) S.W0_le_V S.W0_ne_bot fun w hw => by
      have := Subgroup.mem_centralizer_iff.mp hsC w hw
      rw [← this, mul_inv_cancel_right]
      exact S.W0_le_V hw
  have hfix : ∀ y : P6, InW4 y → InW0 y → act4f (S.frame.ρ ⟨s, hsV⟩) y = y := by
    intro y hy hy0
    obtain ⟨v, hv⟩ := S.frame.ψ.surjective ⟨y, hy⟩
    have hvW : (v : G) ∈ S.W0 := S.mem_pre.2 ⟨v.2, by rw [hv]; exact hy0⟩
    have h := (S.conj_eq_iff ⟨s, hsV⟩ v).1 (by
      have := Subgroup.mem_centralizer_iff.mp hsC (v : G) hvW
      calc s * (v : G) * s⁻¹ = (v : G) * s * s⁻¹ := by rw [this]
        _ = v := by group)
    rw [hv] at h
    exact congrArg Subtype.val h
  have h4 : (S.frame.ρ ⟨s, hsV⟩) ^ 4 = 1 := by
    obtain ⟨k, hk⟩ := hS'.2.1 ⟨s, hsS'⟩
    refine pow_four_of_pow_two_pow (k := k) ?_
    rw [← map_pow]
    have : (⟨s, hsV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hcomm : S.frame.ρ ⟨s, hsV⟩ * swap 4 5 = swap 4 5 * S.frame.ρ ⟨s, hsV⟩ := by
    have hsts : s * (t : G) * s⁻¹ ∈ S.R45 := (Subgroup.mem_normalizer_iff.mp hsN t).mp htR
    obtain ⟨-, hN', hρ'⟩ := S.mem_R45.1 hsts
    have e : (⟨s * (t : G) * s⁻¹, hN'⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨s, hsV⟩ * t * ⟨s, hsV⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hρt] at hρ'
    rcases hρ' with h1 | h1
    · exfalso
      apply swap45_ne_one
      calc swap (4 : Fin 6) 5 = (S.frame.ρ ⟨s, hsV⟩)⁻¹ * (S.frame.ρ ⟨s, hsV⟩ * swap 4 5 *
            (S.frame.ρ ⟨s, hsV⟩)⁻¹) * S.frame.ρ ⟨s, hsV⟩ := by group
        _ = 1 := by rw [h1, mul_one, inv_mul_cancel]
    · calc S.frame.ρ ⟨s, hsV⟩ * swap 4 5 = S.frame.ρ ⟨s, hsV⟩ * swap 4 5 *
            (S.frame.ρ ⟨s, hsV⟩)⁻¹ * S.frame.ρ ⟨s, hsV⟩ := by group
        _ = swap 4 5 * S.frame.ρ ⟨s, hsV⟩ := by rw [h1]
  have heq := F1.eq_of_isSylowTwoOf_le S.isSylowTwoOf_CTV inf_le_right
    (hS'.2.1.to_le inf_le_left) (le_inf (S.Q_le_R45.trans hRS') inf_le_right)
  rcases fix_W0_comm45 _ h4 (hfix _ dv_mem_W0.1.1 dv_mem_W0.1.2)
      (hfix _ dv_mem_W0.2.1 dv_mem_W0.2.2) hcomm with h1 | h1
  · have hmem : s ∈ S' ⊓ Subgroup.centralizer (V : Set G) := ⟨hsS', (S.rho_eq_one_iff _).1 h1⟩
    rw [← heq] at hmem
    exact hsR (S.Q_le_R45 hmem)
  · have hst : S.frame.ρ (⟨s, hsV⟩ * t⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, hρt, mul_inv_cancel]
    have hmem : s * (t : G)⁻¹ ∈ S' ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨S'.mul_mem hsS' (S'.inv_mem (hRS' htR)), (S.rho_eq_one_iff _).1 hst⟩
    rw [← heq] at hmem
    have := S.R45.mul_mem (S.Q_le_R45 hmem) htR
    rw [inv_mul_cancel_right] at this
    exact hsR this

theorem normalizer_le_M_of_char {R C : Subgroup G} (hRT : R ≤ T) (hC1 : C ≠ ⊥)
    (hCB : C ≤ baum R) (hCchar : (C.subgroupOf (baum R)).Characteristic)
    (hCN : L ⊔ T ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hBR : baum R ≤ R := inf_le_left
  have hC2 : IsPGroup 2 C := S.h13.sylow.1.to_le (hCB.trans (hBR.trans hRT))
  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) := ⟨C, hC1, hC2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM := S.uniqueM.2 M' ⟨hM', hCN.trans hle⟩
  have h2 : Subgroup.normalizer (baum R : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have := hCchar
    have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (C.subgroupOf (baum R))
    rwa [Subgroup.map_subgroupOf_eq_of_le hCB] at this
  rw [← hM]
  exact (normalizer_le_normalizer_baum R).trans (h2.trans hle)

theorem isAltQuotient_L : IsAltQuotient L (oTwoZIn L) 6 := by
  obtain ⟨e⟩ := S.centralQuot
  let π₁ := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let π₂ := QuotientGroup.mk' (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  refine ⟨e.toMonoidHom.comp (π₂.comp π₁),
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)),
    ?_⟩
  ext x
  have key : e (π₂ (π₁ x)) = 1 ↔ π₁ x ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  refine key.trans ⟨fun h => ⟨x, h, rfl⟩, ?_⟩
  rintro ⟨y, hy, hyx⟩
  have : y = x := Subtype.ext hyx
  rwa [← this]

theorem V_le_L_of_irr : V ≤ L := by
  calc V = ⁅V, L⁆ := S.irr.2.2.2.1.symm
    _ ≤ L := by
      rw [Subgroup.commutator_le]
      intro v hv l hl
      have h1 : v * l * v⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (S.T_le_NL (S.V_le_T hv)) l).mp hl
      rw [commutatorElement_def]
      exact L.mul_mem h1 (L.inv_mem hl)

theorem V_le_pCoreOf_L : V ≤ pCoreOf 2 L :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 S.V_le_L_of_irr S.frame.L_le S.isPGroup_V

theorem blockU_eq_V (hL : IsShort2 L) : blockU L = V := by
  have hcomm : ⁅V, L⁆ = V := S.irr.2.2.2.1
  have hle : ⁅V, L⁆ ≤ blockU L := Subgroup.commutator_mono S.V_le_pCoreOf_L le_rfl
  have hne : ⁅V, L⁆ ≠ ⊥ := by
    rw [hcomm]
    exact S.irr.2.1
  have h := L246C127.blockU_le_commutator_of_ne_bot hL S.frame.L_le S.isPGroup_V hle hne
  rw [hcomm] at h hle
  exact le_antisymm h hle

theorem blockZ_eq_bot (hL : IsShort2 L) : blockZ L = ⊥ := by
  show blockU L ⊓ Subgroup.centralizer (L : Set G) = ⊥
  rw [S.blockU_eq_V hL]
  exact S.zv

@[expose] noncomputable def rhoOnL : ↥L →* Perm (Fin 6) :=
  S.frame.ρ.comp (Subgroup.inclusion S.frame.L_le)

theorem rhoOnL_range : S.rhoOnL.range = alternatingGroup (Fin 6) := by
  ext σ
  constructor
  · rintro ⟨l, rfl⟩
    exact (S.frame.image_L _).1 ⟨_, l.2, rfl⟩
  · intro hσ
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 hσ
    exact ⟨⟨g, hgL⟩, hg⟩

theorem card_L_eq : Nat.card ↥L = Nat.card S.rhoOnL.ker * 360 := by
  rw [← nat_card_alt_six, ← S.rhoOnL_range,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange S.rhoOnL).toEquiv, mul_comm]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup S.rhoOnL.ker

theorem pCore_le_ker_rhoOnL :
    CFSG.pCore 2 ↥L ≤ S.rhoOnL.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  exact (S.rho_eq_one_iff _).2 (S.pCoreOf_L_le_centralizer ((mem_pCore_iff _).1 hx))

theorem card_le_of_surj {H : Type*} [Group H] (α : ↥L →* H)
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) : 360 ≤ Nat.card H := by
  have hcardα : Nat.card ↥L = Nat.card α.ker * Nat.card H := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
  have hle : Nat.card α.ker ≤ Nat.card S.rhoOnL.ker :=
    Subgroup.card_le_of_le (hker ▸ S.pCore_le_ker_rhoOnL)
  have hpos : 0 < Nat.card S.rhoOnL.ker := Nat.card_pos
  have h1 := S.card_L_eq
  by_contra hlt
  push Not at hlt
  have h2 : Nat.card α.ker * Nat.card H ≤ Nat.card S.rhoOnL.ker * Nat.card H :=
    Nat.mul_le_mul_right _ hle
  have h3 : Nat.card S.rhoOnL.ker * Nat.card H < Nat.card S.rhoOnL.ker * 360 :=
    (Nat.mul_lt_mul_left hpos).2 hlt
  omega

theorem card_alt_eq_of_surj {m : ℕ} (hm : 5 ≤ m)
    (α : ↥L →* alternatingGroup (Fin m)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) : Nat.card (alternatingGroup (Fin m)) = 360 := by
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hm)
  have hle : α.ker ≤ S.rhoOnL.ker := hker ▸ S.pCore_le_ker_rhoOnL
  have : (S.rhoOnL.ker.map α).Normal := (S.rhoOnL.normal_ker).map α hα
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.rhoOnL.ker.map α) with h | h
  · have heq : α.ker = S.rhoOnL.ker := le_antisymm hle ((Subgroup.map_eq_bot_iff _).1 h)
    have hcardα : Nat.card ↥L = Nat.card α.ker * Nat.card (alternatingGroup (Fin m)) := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv, mul_comm]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
    rw [heq, S.card_L_eq] at hcardα
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hcardα).symm
  · exfalso
    have htop : S.rhoOnL.ker = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      have hx : α x ∈ S.rhoOnL.ker.map α := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := hx
      have h1 : k⁻¹ * x ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
      have := S.rhoOnL.ker.mul_mem hk (hle h1)
      rwa [mul_inv_cancel_left] at this
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L (swap 0 1 * swap 1 2)).2
      (Perm.mem_alternatingGroup.2 (by decide))
    have h2 : (⟨g, hgL⟩ : ↥L) ∈ S.rhoOnL.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at h2
    have h3 : S.rhoOnL ⟨g, hgL⟩ = swap 0 1 * swap 1 2 := hg
    rw [h3] at h2
    exact absurd h2 (by decide)

theorem not_isHatA6Block (h : CFSG.Quasithin.IsHatA6Block L) : False := by
  have h1 := h.2.2.1
  rw [S.blockU_eq_V h.1, S.card_V] at h1
  norm_num at h1

theorem not_isExcA7Block (h : CFSG.Quasithin.IsExcA7Block L) :
    False := by
  obtain ⟨-, ⟨α, hα, hker⟩, -⟩ := h
  have h1 := S.card_alt_eq_of_surj (by norm_num) α hα hker
  rw [nat_card_alternatingGroup, Nat.card_fin] at h1
  revert h1
  decide

theorem not_isChiBlock (h : CFSG.Quasithin.IsChiBlock (L ⊔ T) L) :
    False := by
  obtain ⟨hblk, ⟨n, -, F, _, _, hcard, α, hα, hker, β, hβ, hβker, -⟩ |
    ⟨m, hm, hm3, α, hα, hker, -⟩⟩ := h
  · have hinj : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβker, S.blockZ_eq_bot hblk.1, Subgroup.bot_subgroupOf]
    have hcardU : Nat.card ↥(blockU L) = Fintype.card F ^ 2 := by
      rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβ⟩), Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fin]
    rw [S.blockU_eq_V hblk.1, S.card_V, hcard, ← pow_mul] at hcardU
    have hn : n * 2 = 4 := Nat.pow_right_injective le_rfl (hcardU.symm.trans (by norm_num))
    have hn2 : n = 2 := by omega
    have h360 := S.card_le_of_surj α hα hker
    rw [Matrix.card_SL_field, hcard, hn2] at h360
    norm_num [Fin.prod_univ_two] at h360
  · have h360 := S.card_le_of_surj α hα hker
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin] at h360
    by_cases h5 : m ≤ 5
    · interval_cases m <;> revert h360 <;> decide
    · have h7 : 7 ≤ m := by
        rcases hm with ⟨k, hk⟩
        omega
      have h1 := S.card_alt_eq_of_surj (by omega) α hα hker
      rw [nat_card_alternatingGroup, Nat.card_fin] at h1
      have h2 : Nat.factorial 7 ≤ Nat.factorial m := Nat.factorial_le h7
      have h3 : Nat.factorial 7 = 5040 := rfl
      omega

end Setting4

@[expose] def Input1356TwoS6Block : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ autOn T V ≤ autOn L V → IsBlock2 (L ⊔ T) L →
      CFSG.Quasithin.IsAltBlockType L 6 → ∀ g : G, conjSub g S.V2 ≠ S.W0

end CFSG.Quasithin.H13.A6
