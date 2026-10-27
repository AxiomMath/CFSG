module

public import CFSG.Quasithin.Vol2.Ch3n317
public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

open Equiv

namespace CFSG.Quasithin.Ch3n317A5

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem swap_disjoint_of_commute : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    swap a b ≠ swap c d → swap a b * swap c d = swap c d * swap a b →
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  decide

theorem fourGroup_facts : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    (swap b c * swap c d) * (swap a b * swap c d) * (swap c d * swap b c) =
        swap a c * swap b d ∧
      (swap b c * swap c d) * (swap a c * swap b d) * (swap c d * swap b c) =
        swap a d * swap b c ∧
      swap a b * (swap a c * swap b d) * swap a b * (swap b d * swap a c) =
        swap a b * swap c d ∧
      (swap b c * swap c d) * (swap c d * swap b c) = 1 ∧
      (swap b c * swap c d) ^ 3 = 1 ∧ swap b c * swap c d ≠ 1 ∧
      swap a b * swap c d ≠ 1 ∧ swap a c * swap b d ≠ 1 ∧ swap a d * swap b c ≠ 1 ∧
      swap a b * swap c d ≠ swap a c * swap b d ∧ swap a b * swap c d ≠ swap a d * swap b c ∧
      swap a c * swap b d ≠ swap a d * swap b c := by
  decide +kernel

theorem fourGroup_facts' : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    (swap b c * swap c d) * (swap a d * swap b c) * (swap c d * swap b c) =
      swap a b * swap c d ∧ swap a b * swap c d ≠ 1 := by
  decide +kernel

theorem commute_involution : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    c ≠ d → ∀ h : Perm (Fin 5), Perm.sign h = 1 → h * h = 1 →
      h * (swap a b * swap c d) = (swap a b * swap c d) * h →
      h = 1 ∨ h = swap a b * swap c d ∨ h = swap a c * swap b d ∨ h = swap a d * swap b c := by
  decide +kernel

theorem sq_eq_one_of_pow_four : ∀ h : Perm (Fin 5), Perm.sign h = 1 → h ^ 4 = 1 → h ^ 2 = 1 := by
  decide +kernel

theorem swap_mul_swap_pow_three : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    swap a b * swap c d ≠ swap c d * swap a b →
    (swap a b * swap c d) ^ 3 = 1 ∧ swap a b * swap c d ≠ 1 := by
  decide +kernel

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem perm_four {Q : Subgroup (Perm (Fin 5))} (hQA : Q ≤ alternatingGroup (Fin 5))
    (hQ4 : Nat.card Q = 4) {a b c d : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hgQ : swap a b * swap c d ∈ Q) :
    swap a c * swap b d ∈ Q ∧ swap a d * swap b c ∈ Q ∧
      ∀ h ∈ Q, h = 1 ∨ h = swap a b * swap c d ∨ h = swap a c * swap b d ∨
        h = swap a d * swap b c := by
  classical
  have hsq : ∀ h ∈ Q, h * h = 1 := by
    intro h hh
    have h4 : h ^ 4 = 1 := by
      have := pow_card_eq_one (G := Q) (x := ⟨h, hh⟩)
      rw [← Nat.card_eq_fintype_card, hQ4] at this
      exact congrArg Subtype.val this
    have := sq_eq_one_of_pow_four h (hQA hh) h4
    rwa [sq] at this
  have hcomm : ∀ h ∈ Q, h * (swap a b * swap c d) = (swap a b * swap c d) * h := by
    intro h hh
    have h1 := hsq _ (Q.mul_mem hh hgQ)
    have h2 := hsq h hh
    have h3 := hsq _ hgQ
    calc h * (swap a b * swap c d) = (h * (swap a b * swap c d))⁻¹ :=
          eq_inv_of_mul_eq_one_left h1
      _ = (swap a b * swap c d)⁻¹ * h⁻¹ := mul_inv_rev _ _
      _ = (swap a b * swap c d) * h := by
          rw [inv_eq_of_mul_eq_one_left h3, inv_eq_of_mul_eq_one_left h2]
  have hmem : ∀ h ∈ Q, h = 1 ∨ h = swap a b * swap c d ∨ h = swap a c * swap b d ∨
      h = swap a d * swap b c := fun h hh =>
    commute_involution a b c d hab hac had hbc hbd hcd h (hQA hh) (hsq h hh) (hcomm h hh)
  have hcount : ∀ x y : Perm (Fin 5), (∀ h ∈ Q, h = 1 ∨ h = x ∨ h = y) → Nat.card Q ≤ 3 := by
    intro x y hxy
    have h1 : (Q : Set (Perm (Fin 5))) ⊆ {1, x, y} := fun h hh => by
      rcases hxy h hh with rfl | rfl | rfl <;> simp
    calc Nat.card Q = Set.ncard (Q : Set (Perm (Fin 5))) := (Nat.card_coe_set_eq _).symm
      _ ≤ Set.ncard ({1, x, y} : Set (Perm (Fin 5))) := Set.ncard_le_ncard h1
      _ ≤ 3 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          have := Set.ncard_insert_le x ({y} : Set (Perm (Fin 5)))
          rw [Set.ncard_singleton] at this
          omega
  have hx₁ : swap a c * swap b d ∈ Q := by
    by_contra hx
    have := hcount (swap a b * swap c d) (swap a d * swap b c) fun h hh => by
      rcases hmem h hh with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact absurd (h1 ▸ hh) hx
      · exact Or.inr (Or.inr h1)
    omega
  have hx₂ : swap a d * swap b c ∈ Q := by
    by_contra hx
    have := hcount (swap a b * swap c d) (swap a c * swap b d) fun h hh => by
      rcases hmem h hh with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
      · exact absurd (h1 ▸ hh) hx
    omega
  exact ⟨hx₁, hx₂, hmem⟩

section AltOf

variable {Γ : Type*} [Group Γ] (L : Subgroup Γ) (θ : L ≃* Perm (Fin 5))

@[expose] noncomputable def altOf : Subgroup Γ :=
  (alternatingGroup (Fin 5)).map (L.subtype.comp θ.symm.toMonoidHom)

@[expose] noncomputable def elt (σ : Perm (Fin 5)) : Γ := (θ.symm σ : L)

variable {L θ}

theorem mem_altOf {x : Γ} : x ∈ altOf L θ ↔ ∃ hx : x ∈ L, θ ⟨x, hx⟩ ∈ alternatingGroup (Fin 5) := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨(θ.symm σ).2, ?_⟩
    change θ (θ.symm σ) ∈ _
    rw [MulEquiv.apply_symm_apply]
    exact hσ
  · rintro ⟨hx, hθ⟩
    exact ⟨θ ⟨x, hx⟩, hθ, by simp⟩

theorem altOf_le : altOf L θ ≤ L := fun _ hx => (mem_altOf.mp hx).1

theorem elt_mem (σ : Perm (Fin 5)) : elt L θ σ ∈ L := (θ.symm σ).2

theorem theta_elt (σ : Perm (Fin 5)) : θ ⟨elt L θ σ, elt_mem σ⟩ = σ := by
  change θ (θ.symm σ) = σ
  exact MulEquiv.apply_symm_apply θ σ

theorem elt_mem_altOf {σ : Perm (Fin 5)} (hσ : σ ∈ alternatingGroup (Fin 5)) :
    elt L θ σ ∈ altOf L θ :=
  mem_altOf.mpr ⟨elt_mem σ, by rw [theta_elt]; exact hσ⟩

theorem elt_mul (σ τ : Perm (Fin 5)) : elt L θ (σ * τ) = elt L θ σ * elt L θ τ := by
  simp [elt]

theorem elt_theta {x : Γ} (hx : x ∈ L) : elt L θ (θ ⟨x, hx⟩) = x := by
  simp [elt]

theorem mul_self_mem_altOf {x : Γ} (hx : x ∈ L) : x * x ∈ altOf L θ := by
  refine mem_altOf.mpr ⟨L.mul_mem hx hx, ?_⟩
  have h1 : θ ⟨x * x, L.mul_mem hx hx⟩ = θ ⟨x, hx⟩ * θ ⟨x, hx⟩ := by
    rw [← map_mul]
    rfl
  rw [h1, Perm.mem_alternatingGroup, map_mul]
  rcases Int.units_eq_one_or (Perm.sign (θ ⟨x, hx⟩)) with h | h <;> rw [h] <;> rfl

theorem le_normalizer_altOf : L ≤ Subgroup.normalizer (altOf L θ : Set Γ) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxL, hxA⟩ := mem_altOf.mp hx
    have hm : l * x * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl)
    refine mem_altOf.mpr ⟨hm, ?_⟩
    have h1 : θ ⟨l * x * l⁻¹, hm⟩ = θ ⟨l, hl⟩ * θ ⟨x, hxL⟩ * (θ ⟨l, hl⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1]
    exact (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem _ hxA _
  · intro hx
    obtain ⟨hxL', hxA⟩ := mem_altOf.mp hx
    have hxL : x ∈ L := by
      have : l⁻¹ * (l * x * l⁻¹) * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hxL') hl
      simpa [mul_assoc] using this
    refine mem_altOf.mpr ⟨hxL, ?_⟩
    have h1 : θ ⟨x, hxL⟩ = (θ ⟨l, hl⟩)⁻¹ * θ ⟨l * x * l⁻¹, hxL'⟩ * θ ⟨l, hl⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [mul_assoc]
    rw [h1]
    have := (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem _ hxA (θ ⟨l, hl⟩)⁻¹
    simpa using this

theorem card_altOf : Nat.card (altOf L θ) = 60 := by
  rw [altOf, Subgroup.card_map_of_injective, card_alternatingGroup_five]
  exact L.subtype_injective.comp θ.symm.injective

theorem altOf_le_of_odd {K : Subgroup Γ} [Finite Γ]
    (h : ∀ x ∈ L, Odd (orderOf x) → x ∈ K) : altOf L θ ≤ K := by
  rw [altOf, ← Equiv.Perm.closure_three_cycles_eq_alternating, MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ3 : σ.IsThreeCycle := hσ
  apply h _ (θ.symm σ).2
  have h1 : orderOf ((θ.symm σ : L) : Γ) = orderOf σ := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  change Odd (orderOf ((θ.symm σ : L) : Γ))
  rw [h1, hσ3.orderOf]
  decide

theorem elt_inv (σ : Perm (Fin 5)) : elt L θ σ⁻¹ = (elt L θ σ)⁻¹ := by simp [elt]

theorem orderOf_elt (σ : Perm (Fin 5)) : orderOf (elt L θ σ) = orderOf σ := by
  rw [elt, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]

theorem exists_two_swaps [Finite Γ] {A : Subgroup Γ}
    (h4 : Nat.card (Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ A ∧ (θ ⟨x, hx⟩).IsSwap}) = 4) :
    ∃ a b c d : Fin 5, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      elt L θ (swap a b) ∈ Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ A ∧ (θ ⟨x, hx⟩).IsSwap} ∧
      elt L θ (swap c d) ∈ Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ A ∧ (θ ⟨x, hx⟩).IsSwap} := by
  classical
  set Sw := {x | ∃ hx : x ∈ L, x ∈ A ∧ (θ ⟨x, hx⟩).IsSwap} with hSw
  have hform : ∀ x ∈ Sw, ∃ a b : Fin 5, a ≠ b ∧ x = elt L θ (swap a b) := by
    rintro x ⟨hx, -, a, b, hab, he⟩
    exact ⟨a, b, hab, by rw [← he, elt_theta]⟩
  have hswap2 : ∀ a b : Fin 5, a ≠ b → orderOf (swap a b) = 2 := fun a b hab =>
    Perm.IsSwap.orderOf ⟨a, b, hab, rfl⟩
  obtain ⟨s₁, hs₁⟩ : Sw.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    rw [he, Subgroup.closure_empty, Subgroup.card_bot] at h4
    omega
  obtain ⟨a, b, hab, rfl⟩ := hform _ hs₁
  obtain ⟨s₂, hs₂, hne⟩ : ∃ s₂ ∈ Sw, s₂ ≠ elt L θ (swap a b) := by
    by_contra hall
    push Not at hall
    have hle : Subgroup.closure Sw ≤ Subgroup.zpowers (elt L θ (swap a b)) :=
      (Subgroup.closure_le _).mpr fun x hx => by rw [hall x hx]; exact Subgroup.mem_zpowers _
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_elt, hswap2 a b hab] at h1
    omega
  obtain ⟨c, d, hcd, rfl⟩ := hform _ hs₂
  have hne' : swap a b ≠ swap c d := fun h => hne (by rw [h])
  have hm₁ : elt L θ (swap a b) ∈ Subgroup.closure Sw := Subgroup.subset_closure hs₁
  have hm₂ : elt L θ (swap c d) ∈ Subgroup.closure Sw := Subgroup.subset_closure hs₂
  by_cases hc : swap a b * swap c d = swap c d * swap a b
  · obtain ⟨h1, h2, h3, h4'⟩ := swap_disjoint_of_commute a b c d hab hcd hne' hc
    exact ⟨a, b, c, d, hab, h1, h2, h3, h4', hcd, hm₁, hm₂⟩
  · exfalso
    obtain ⟨h3, h1⟩ := swap_mul_swap_pow_three a b c d hab hcd hc
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (swap a b * swap c d) = 3 := orderOf_eq_prime h3 h1
    have hmem : elt L θ (swap a b * swap c d) ∈ Subgroup.closure Sw := by
      rw [elt_mul]
      exact Subgroup.mul_mem _ hm₁ hm₂
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [orderOf_elt, hord, h4] at hdvd
    norm_num at hdvd

end AltOf

section Component

variable {Γ : Type*} [Group Γ] {L : Subgroup Γ} (θ : L ≃* Perm (Fin 5))

theorem fourGroup_of_card {W : Subgroup Γ} (hWA : W ≤ altOf L θ) (hW4 : Nat.card W = 4)
    {a b c d : Fin 5} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (hg : elt L θ (swap a b * swap c d) ∈ W) :
    elt L θ (swap a c * swap b d) ∈ W ∧ elt L θ (swap a d * swap b c) ∈ W ∧
      ∀ w ∈ W, w = 1 ∨ w = elt L θ (swap a b * swap c d) ∨
        w = elt L θ (swap a c * swap b d) ∨ w = elt L θ (swap a d * swap b c) := by
  classical
  set φ : Perm (Fin 5) →* Γ := L.subtype.comp θ.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := L.subtype_injective.comp θ.symm.injective
  have hφelt : ∀ σ, φ σ = elt L θ σ := fun σ => rfl
  set Q := W.comap φ with hQ
  have hWQ : W = Q.map φ := by
    rw [hQ, Subgroup.map_comap_eq, inf_eq_right.mpr]
    rintro w hw
    obtain ⟨hwL, -⟩ := mem_altOf.mp (hWA hw)
    exact ⟨θ ⟨w, hwL⟩, by simp [hφ]⟩
  have hQ4 : Nat.card Q = 4 := by
    rw [← hW4, hWQ, Subgroup.card_map_of_injective hφinj]
  have hQA : Q ≤ alternatingGroup (Fin 5) := by
    intro σ hσ
    have h1 : φ σ ∈ altOf L θ := hWA hσ
    obtain ⟨hx, hθ⟩ := mem_altOf.mp h1
    have h2 : θ ⟨φ σ, hx⟩ = σ := theta_elt σ
    rwa [h2] at hθ
  have hgQ : swap a b * swap c d ∈ Q := hg
  obtain ⟨hx₁, hx₂, hall⟩ := perm_four hQA hQ4 hab hac had hbc hbd hcd hgQ
  refine ⟨hx₁, hx₂, fun w hw => ?_⟩
  rw [hWQ] at hw
  obtain ⟨σ, hσ, rfl⟩ := hw
  rcases hall σ hσ with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one φ)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

end Component

section Decomp

variable {Γ : Type*} [Group Γ] {I : Finset (Subgroup Γ)} (alt : Subgroup Γ → Subgroup Γ)

theorem exists_mul_of_mem_sup {A B : Subgroup Γ} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {g : Γ} (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let S : Subgroup Γ :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have := hAB a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← this]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have := hAB a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
        rw [mul_inv_rev, ← this] }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hg

theorem card_cases [DecidableEq (Subgroup Γ)] (hIcard : I.card = 1 ∨ I.card = 2) :
    (∃ L, I = {L}) ∨ ∃ L₁ L₂, L₁ ≠ L₂ ∧ I = {L₁, L₂} := by
  rcases hIcard with h | h
  · exact Or.inl (Finset.card_eq_one.mp h)
  · obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.mp h
    exact Or.inr ⟨L₁, L₂, hne, rfl⟩

variable {alt}

theorem odd_mem_iSup_alt [Finite Γ] (hIcard : I.card = 1 ∨ I.card = 2)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hsq : ∀ L ∈ I, ∀ x ∈ L, x * x ∈ alt L) {x : Γ} (hx : x ∈ ⨆ L ∈ I, L)
    (hodd : Odd (orderOf x)) : x ∈ ⨆ L ∈ I, alt L := by
  classical
  have hx2 : x * x ∈ ⨆ L ∈ I, alt L := by
    rcases card_cases hIcard with ⟨L, rfl⟩ | ⟨L₁, L₂, hne, rfl⟩
    · simp only [Finset.iSup_singleton] at hx ⊢
      exact hsq L (Finset.mem_singleton_self L) x hx
    · simp only [Finset.iSup_insert, Finset.iSup_singleton] at hx ⊢
      have h1 : L₁ ∈ ({L₁, L₂} : Finset (Subgroup Γ)) := Finset.mem_insert_self _ _
      have h2 : L₂ ∈ ({L₁, L₂} : Finset (Subgroup Γ)) :=
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup (hcomm L₁ h1 L₂ h2 hne) hx
      have hab := hcomm L₁ h1 L₂ h2 hne a ha b hb
      have e : a * b * (a * b) = (a * a) * (b * b) := by
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hab]
          _ = a * a * (b * b) := by group
      rw [e]
      exact Subgroup.mul_mem_sup (hsq L₁ h1 a ha) (hsq L₂ h2 b hb)
  obtain ⟨k, hk⟩ := hodd
  have e : x = (x * x) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [e]
  exact Subgroup.pow_mem _ hx2 _

theorem sylow_decomp [Finite Γ] (hIcard : I.card = 1 ∨ I.card = 2)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (halt : ∀ L ∈ I, alt L ≤ L ∧ L ≤ Subgroup.normalizer (alt L : Set Γ) ∧
      Nat.card (alt L) = 60)
    {P : Subgroup Γ} (hP : IsSylowTwoOf P (⨆ L ∈ I, alt L)) :
    (∀ L ∈ I, Nat.card ↥(P ⊓ alt L) = 4) ∧ P = ⨆ L ∈ I, (P ⊓ alt L) := by
  classical
  have h60 : (60 : ℕ).factorization 2 = 2 := by
    have h : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hN : ∀ L ∈ I, (⨆ L' ∈ I, alt L') ≤ Subgroup.normalizer (alt L : Set Γ) := by
    intro L hL
    refine iSup₂_le fun L' hL' => ?_
    by_cases hLL : L' = L
    · subst hLL
      exact (halt L' hL').1.trans (halt L' hL').2.1
    · refine ((halt L' hL').1).trans (le_trans ?_ (Subgroup.centralizer_le_normalizer _))
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm L' hL' L hL hLL a ha b ((halt L hL).1 hb)).symm
  have hle : ∀ L ∈ I, alt L ≤ ⨆ L' ∈ I, alt L' := fun L hL =>
    le_iSup₂_of_le (f := fun L' (_ : L' ∈ I) => alt L') L hL le_rfl
  have h4 : ∀ L ∈ I, Nat.card ↥(P ⊓ alt L) = 4 := by
    intro L hL
    have hs := B6.isSylowTwoOf_inf_normal hP (hle L hL) (hN L hL)
    rw [CFSG.QuasithinUnique.IsSylowTwoOf.card_eq hs, CFSG.QuasithinUnique.twoPart,
      (halt L hL).2.2, h60]
    norm_num
  refine ⟨h4, ?_⟩
  rcases card_cases hIcard with ⟨L, rfl⟩ | ⟨L₁, L₂, hne, rfl⟩
  · simp only [Finset.iSup_singleton] at hP ⊢
    exact (inf_eq_left.mpr hP.1).symm
  · simp only [Finset.iSup_insert, Finset.iSup_singleton] at hP ⊢
    have h1 : L₁ ∈ ({L₁, L₂} : Finset (Subgroup Γ)) := Finset.mem_insert_self _ _
    have h2 : L₂ ∈ ({L₁, L₂} : Finset (Subgroup Γ)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hcomm' : ∀ a ∈ alt L₁, ∀ b ∈ alt L₂, a * b = b * a := fun a ha b hb =>
      hcomm L₁ h1 L₂ h2 hne a ((halt L₁ h1).1 ha) b ((halt L₂ h2).1 hb)
    have hind' : alt L₁ ⊓ alt L₂ = ⊥ := by
      have h := hind L₁ h1
      rw [eq_bot_iff] at h ⊢
      intro x hx
      refine h ⟨(halt L₁ h1).1 hx.1, ?_⟩
      refine le_iSup₂_of_le (f := fun L' (_ : L' ∈ ({L₁, L₂} : Finset (Subgroup Γ))) =>
        ⨆ (_ : L' ≠ L₁), L') L₂ h2 ?_ ((halt L₂ h2).1 hx.2)
      exact le_iSup_of_le (Ne.symm hne) le_rfl
    have hA : Nat.card ↥(alt L₁ ⊔ alt L₂) = 3600 := by
      have e := CFSG.Quasithin.B2F.card_sup_mul_card_inf_of_commute hcomm'
      rw [hind', Subgroup.card_bot, mul_one, (halt L₁ h1).2.2, (halt L₂ h2).2.2] at e
      exact e
    have h3600 : (3600 : ℕ).factorization 2 = 4 := by
      have h : (3600 : ℕ) = 2 ^ 4 * 225 := by norm_num
      rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    have hP16 : Nat.card P = 16 := by
      rw [CFSG.QuasithinUnique.IsSylowTwoOf.card_eq hP, CFSG.QuasithinUnique.twoPart, hA,
        h3600]
      norm_num
    have hcommP : ∀ a ∈ P ⊓ alt L₁, ∀ b ∈ P ⊓ alt L₂, a * b = b * a := fun a ha b hb =>
      hcomm' a ha.2 b hb.2
    have hindP : (P ⊓ alt L₁) ⊓ (P ⊓ alt L₂) = ⊥ := by
      rw [eq_bot_iff, ← hind']
      exact inf_le_inf inf_le_right inf_le_right
    have hS : Nat.card ↥((P ⊓ alt L₁) ⊔ (P ⊓ alt L₂)) = 16 := by
      have e := CFSG.Quasithin.B2F.card_sup_mul_card_inf_of_commute hcommP
      rw [hindP, Subgroup.card_bot, mul_one, h4 L₁ h1, h4 L₂ h2] at e
      exact e
    exact (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left)
      (by rw [hP16, hS])).symm

end Decomp

section Components

theorem card_SL_two_pow {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 2 ^ n * (4 ^ n - 1) := by
  have := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Fin.prod_univ_two]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  rw [← Nat.card_eq_fintype_card, hK]
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hpos : 0 < 2 ^ n - 1 := by
    have h := Finite.one_lt_card (α := K)
    rw [hK] at h
    omega
  have h1 : (2 ^ n) ^ 2 - 2 ^ n = 2 ^ n * (2 ^ n - 1) := by rw [Nat.mul_sub_one, sq]
  rw [h1, h4, show (4 ^ n - 1) * (2 ^ n * (2 ^ n - 1)) = 2 ^ n * (4 ^ n - 1) * (2 ^ n - 1) by
    ring, Nat.mul_div_cancel _ hpos]

theorem two_pow_mul_ne_120 (n : ℕ) : 2 ^ n * (4 ^ n - 1) ≠ 120 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h64 : 64 ≤ 4 ^ n := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have : 63 ≤ 4 ^ n - 1 := by omega
    nlinarith

variable {W : Type*} [CommGroup W]

theorem card_conjAut (g : MulAut W) (A : Subgroup (MulAut W)) :
    Nat.card ↥(B1.conjAut g A) = Nat.card ↥A := by
  have e : B1.conjAut g A = A.map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [B1.mem_conjAut, Subgroup.mem_map_equiv]
    simp
  rw [e]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_of_isL2Natural {L : Subgroup (MulAut W)} {C : Subgroup W} {n : ℕ}
    (h : E2.IsL2Natural L C n) : Nat.card ↥L = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨-, F, _, _, hF, e, -⟩ := h
  rw [Nat.card_congr e.toEquiv, card_SL_two_pow (by rw [Nat.card_eq_fintype_card, hF])]

theorem card_of_isA5Module {L : Subgroup (MulAut W)} (h : E2.IsA5Module L) :
    Nat.card ↥L = 120 := by
  obtain ⟨θ, -⟩ := h
  rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

end Components

section Frattini

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        exact ⟨a * (b * a' * b⁻¹), A.mul_mem ha
          ((Subgroup.mem_normalizer_iff.mp (hB hb) a').mp ha'), b * b', B.mul_mem hb hb',
          by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨b⁻¹ * a⁻¹ * b, ?_, b⁻¹, B.inv_mem hb, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (hB (B.inv_mem hb)) a⁻¹).mp (A.inv_mem ha)
        simpa using this }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hg

theorem exists_eq_mul_normalizer {V H T K : Subgroup G} (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (hT : IsSylowTwoOf T H) (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    {z : G} (hzH : z ∈ H)
    (hz : ∀ p ∈ T ⊓ K, ∃ p' ∈ T ⊓ K, p'⁻¹ * (z * p * z⁻¹) ∈ Subgroup.centralizer (V : Set G)) :
    ∃ p ∈ T ⊓ K, ∃ c ∈ Subgroup.centralizer (V : Set G),
      ∃ y ∈ H ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G), z = p * c * y := by
  classical
  set C := Subgroup.centralizer (V : Set G) with hC
  set P := T ⊓ K with hP
  set N₀ := (K ⊓ C) ⊔ P with hN₀
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := B6.le_normalizer_centralizer hHN
  have hHKC : H ≤ Subgroup.normalizer ((K ⊓ C : Subgroup G) : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHK hh, hHC hh⟩
  have hPH : P ≤ H := inf_le_left.trans hT.1
  have hPKC : P ≤ Subgroup.normalizer ((K ⊓ C : Subgroup G) : Set G) := hPH.trans hHKC
  have hN₀H : N₀ ≤ H := sup_le (inf_le_left.trans hKH) hPH
  have hzN₀ : B6.conjSub z N₀ ≤ N₀ := by
    rw [hN₀, (B6.conjSub z).map_sup, B6.conjSub_eq_self (hHKC hzH)]
    refine sup_le le_sup_left ?_
    intro x hx
    rw [B6.mem_conjSub] at hx
    obtain ⟨p', hp', hpc⟩ := hz _ hx
    have hxz : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
    rw [hxz] at hpc
    have hxK : x ∈ K := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hHK hzH) _).mp (hx.2)
      rwa [hxz] at h1
    have e : x = p' * (p'⁻¹ * x) := by group
    rw [e]
    have hp'K : p'⁻¹ * x ∈ K ⊓ C := ⟨K.mul_mem (K.inv_mem hp'.2) hxK, hpc⟩
    exact N₀.mul_mem (le_sup_right (a := K ⊓ C) hp') (le_sup_left (b := P) hp'K)
  have hzN₀' : B6.conjSub z N₀ = N₀ :=
    Subgroup.eq_of_le_of_card_ge hzN₀ (by rw [B6.card_conjSub])
  have hPN₀ : IsSylowTwoOf P N₀ := by
    refine ⟨le_sup_right, hT.2.1.to_le inf_le_left, ?_⟩
    have hKCs : IsSylowTwoOf (T ⊓ (K ⊓ C)) (K ⊓ C) :=
      B6.isSylowTwoOf_inf_normal hT (inf_le_left.trans hKH) hHKC
    have e1 : (P ⊓ (K ⊓ C)).relIndex (K ⊓ C) = P.relIndex (P ⊔ (K ⊓ C)) :=
      B6.relIndex_inf_eq_relIndex_sup hPKC
    have e2 : P ⊓ (K ⊓ C) = T ⊓ (K ⊓ C) := by
      rw [hP, inf_assoc, ← inf_assoc K K C, inf_idem]
    rw [e2, sup_comm] at e1
    intro hd
    apply hKCs.2.2
    change 2 ∣ (T ⊓ (K ⊓ C)).relIndex (K ⊓ C)
    rw [e1]
    exact hd
  have hzP : IsSylowTwoOf (B6.conjSub z P) N₀ := by
    have := B6.isSylowTwoOf_conjSub hPN₀ z
    rwa [hzN₀'] at this
  obtain ⟨n, hnN₀, hn⟩ := B6.isSylowTwoOf_exists_conj hPN₀ hzP
  obtain ⟨c, hc, p, hp, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hPKC hnN₀
  refine ⟨p, hp, p⁻¹ * c * p, ?_, (c * p)⁻¹ * z, ⟨?_, ?_⟩, by group⟩
  · have := (Subgroup.mem_normalizer_iff.mp (hHC (hPH (P.inv_mem hp))) c).mp hc.2
    simpa using this
  · exact H.mul_mem (H.inv_mem (hN₀H (N₀.mul_mem (le_sup_left (b := P) hc)
      (le_sup_right (a := K ⊓ C) hp)))) hzH
  · change (c * p)⁻¹ * z ∈ Subgroup.normalizer (P : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have e : B6.conjSub ((c * p)⁻¹ * z) P = P := by
      rw [B6.conjSub_mul, hn, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
    exact e

end Frattini

section PerComponent

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem fourGroup_le_autI {H T K S M₂ : Subgroup G} {L : Subgroup (MulAut (IntMod V hV))}
    (θ : L ≃* Perm (Fin 5))
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hT : IsSylowTwoOf T H) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hST : S ≤ T)
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) (hTM : T ≤ M₂)
    (hNM : H ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ M₂)
    (hcl : Nat.card (Subgroup.closure
      {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap}) = 4)
    (hclS : Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap} ≤
      autI hV S)
    (hW4 : Nat.card ↥(autI hV (T ⊓ K) ⊓ altOf L θ) = 4)
    (hTA : autI hV T ⊓ altOf L θ ≤ autI hV (T ⊓ K))
    (haltK : altOf L θ ≤ autI hV K)
    (hdec : autI hV (T ⊓ K) ≤ (autI hV (T ⊓ K) ⊓ altOf L θ) ⊔
      (autI hV (T ⊓ K) ⊓ Subgroup.centralizer (L : Set (MulAut (IntMod V hV))))) :
    autI hV (T ⊓ K) ⊓ altOf L θ ≤
      autI hV (⨆ y ∈ M₂ ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G),
        B6.conjSub y (S ⊓ K)) := by
  classical
  set P := T ⊓ K with hP
  set N := ⨆ y ∈ M₂ ⊓ Subgroup.normalizer (P : Set G), B6.conjSub y (S ⊓ K) with hN
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKH.trans hHN
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hHN
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs₁, hs₂⟩ := exists_two_swaps hcl
  have hclT : Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap} ≤
      autI hV T := (Subgroup.closure_le _).mpr fun x hx => hx.2.1
  have hgalt : elt L θ (swap a b * swap c d) ∈ altOf L θ := by
    refine elt_mem_altOf ?_
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    rfl
  have hgW : elt L θ (swap a b * swap c d) ∈ autI hV P ⊓ altOf L θ := by
    refine ⟨hTA ⟨?_, hgalt⟩, hgalt⟩
    rw [elt_mul]
    exact (autI hV T).mul_mem (hclT hs₁) (hclT hs₂)
  obtain ⟨hx₁W, hx₂W, hall⟩ :=
    fourGroup_of_card θ inf_le_right hW4 hab hac had hbc hbd hcd hgW
  obtain ⟨e1, e2, e3, -, -, -, -, -, -, -, -, -⟩ :=
    fourGroup_facts a b c d hab hac had hbc hbd hcd
  obtain ⟨e4, -⟩ := fourGroup_facts' a b c d hab hac had hbc hbd hcd
  obtain ⟨a₀, ha₀S, ha₀⟩ := (mem_autI hV).1 (hclS hs₁)
  obtain ⟨t₁, ht₁P, ht₁⟩ := (mem_autI hV).1 hx₁W.1
  set c₀ : Subgroup.normalizer (V : Set G) := a₀ * t₁ * a₀⁻¹ * t₁⁻¹ with hc₀
  have hs₁inv : (elt L θ (swap a b))⁻¹ = elt L θ (swap a b) := by rw [← elt_inv, swap_inv]
  have hx₁inv : (elt L θ (swap a c * swap b d))⁻¹ = elt L θ (swap b d * swap a c) := by
    rw [← elt_inv, mul_inv_rev, swap_inv, swap_inv]
  have hc₀g : convI hV c₀ = elt L θ (swap a b * swap c d) := by
    rw [hc₀, map_mul, map_mul, map_mul, map_inv, map_inv, ha₀, ht₁, hs₁inv, hx₁inv, ← elt_mul,
      ← elt_mul, ← elt_mul, e3]
  have hc₀SK : (c₀ : G) ∈ S ⊓ K := by
    have ha₀T : (a₀ : G) ∈ T := hST ha₀S
    have hcoe : (c₀ : G) = a₀ * t₁ * (a₀ : G)⁻¹ * (t₁ : G)⁻¹ := rfl
    rw [hcoe]
    constructor
    · have h1 : (t₁ : G) * (a₀ : G)⁻¹ * (t₁ : G)⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hTS ht₁P.1) _).mp (S.inv_mem ha₀S)
      have := S.mul_mem ha₀S h1
      simpa [mul_assoc] using this
    · have h1 : (a₀ : G) * t₁ * (a₀ : G)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hHK (hT.1 ha₀T)) _).mp ht₁P.2
      exact K.mul_mem h1 (K.inv_mem ht₁P.2)
  set ω := elt L θ (swap b c * swap c d) with hω
  have hωalt : ω ∈ altOf L θ := by
    refine elt_mem_altOf ?_
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hbc, Perm.sign_swap hcd]
    rfl
  have hωinv : ω⁻¹ = elt L θ (swap c d * swap b c) := by
    rw [hω, ← elt_inv, mul_inv_rev, swap_inv, swap_inv]
  have hconj : ∀ σ, ω * elt L θ σ * ω⁻¹ =
      elt L θ ((swap b c * swap c d) * σ * (swap c d * swap b c)) := by
    intro σ
    rw [hωinv, hω, ← elt_mul, ← elt_mul]
  have hωP : ∀ q ∈ autI hV P, ω * q * ω⁻¹ ∈ autI hV P := by
    intro q hq
    obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_of_mem_sup (A := autI hV P ⊓ altOf L θ)
      (B := autI hV P ⊓ Subgroup.centralizer (L : Set (MulAut (IntMod V hV))))
      (fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy.2 x (altOf_le hx.2)) (hdec hq)
    have hw'c : ω * w' = w' * ω := Subgroup.mem_centralizer_iff.mp hw'.2 _ (elt_mem _)
    have e : ω * (w * w') * ω⁻¹ = (ω * w * ω⁻¹) * w' := by
      calc ω * (w * w') * ω⁻¹ = ω * w * ω⁻¹ * (ω * w') * ω⁻¹ := by group
        _ = ω * w * ω⁻¹ * (w' * ω) * ω⁻¹ := by rw [hw'c]
        _ = (ω * w * ω⁻¹) * w' := by group
    rw [e]
    refine (autI hV P).mul_mem ?_ hw'.1
    rcases hall w hw with rfl | rfl | rfl | rfl
    · simp
    · rw [hconj, e1]
      exact hx₁W.1
    · rw [hconj, e2]
      exact hx₂W.1
    · rw [hconj, e4]
      exact hgW.1
  obtain ⟨z₀, hz₀K, hz₀⟩ := (mem_autI hV).1 (haltK hωalt)
  have hz : ∀ p ∈ T ⊓ K, ∃ p' ∈ T ⊓ K,
      p'⁻¹ * ((z₀ : G) * p * (z₀ : G)⁻¹) ∈ Subgroup.centralizer (V : Set G) := by
    intro p hp
    have hpN : p ∈ Subgroup.normalizer (V : Set G) := hKN hp.2
    have h1 : convI hV (z₀ * ⟨p, hpN⟩ * z₀⁻¹) ∈ autI hV P := by
      rw [map_mul, map_mul, map_inv, hz₀]
      exact hωP _ (convI_mem_autI hV hp hpN)
    obtain ⟨p', hp', hp'eq⟩ := (mem_autI hV).1 h1
    refine ⟨(p' : G), hp', ?_⟩
    have h2 : convI hV (p'⁻¹ * (z₀ * ⟨p, hpN⟩ * z₀⁻¹)) = 1 := by
      rw [map_mul, map_inv, hp'eq, inv_mul_cancel]
    exact (convI_eq_one_iff hV _).1 h2
  obtain ⟨p, hp, c', hc', y, hy, hz₀eq⟩ :=
    exists_eq_mul_normalizer hHN hT hKH hHK (hKH hz₀K) hz
  have hpN : p ∈ Subgroup.normalizer (V : Set G) := hTN hp.1
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := hHN hy.1
  have hc'N : c' ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hc'
  set z : Subgroup.normalizer (V : Set G) := ⟨p, hpN⟩ * ⟨y, hyN⟩ with hzdef
  have hzω : convI hV z = ω := by
    have e : z₀ = ⟨p, hpN⟩ * ⟨c', hc'N⟩ * ⟨y, hyN⟩ := Subtype.ext hz₀eq
    have hc1 : convI hV ⟨c', hc'N⟩ = 1 := (convI_eq_one_iff hV _).2 hc'
    rw [← hz₀, e, hzdef]
    simp only [map_mul, hc1, mul_one]
  have hzMN : (z : G) ∈ M₂ ⊓ Subgroup.normalizer (P : Set G) :=
    ⟨M₂.mul_mem (hTM hp.1) (hNM hy), Subgroup.mul_mem _ (Subgroup.le_normalizer hp) hy.2⟩
  have hmemN : ∀ u : Subgroup.normalizer (V : Set G),
      (u : G) ∈ M₂ ⊓ Subgroup.normalizer (P : Set G) → convI hV (u * c₀ * u⁻¹) ∈ autI hV N := by
    intro u hu
    refine (mem_autI hV).2 ⟨u * c₀ * u⁻¹, ?_, rfl⟩
    refine le_iSup₂_of_le (f := fun y (_ : y ∈ M₂ ⊓ Subgroup.normalizer (P : Set G)) =>
      B6.conjSub y (S ⊓ K)) (u : G) hu le_rfl ?_
    rw [B6.mem_conjSub]
    have e : (u : G)⁻¹ * ((u * c₀ * u⁻¹ : Subgroup.normalizer (V : Set G)) : G) * u = c₀ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hc₀SK
  have hgN : elt L θ (swap a b * swap c d) ∈ autI hV N := by
    have := hmemN 1 (M₂ ⊓ Subgroup.normalizer (P : Set G)).one_mem
    simpa [hc₀g] using this
  have hx₁N : elt L θ (swap a c * swap b d) ∈ autI hV N := by
    have := hmemN z hzMN
    rwa [map_mul, map_mul, map_inv, hzω, hc₀g, hconj, e1] at this
  have hx₂N : elt L θ (swap a d * swap b c) ∈ autI hV N := by
    have := hmemN (z * z) ⟨M₂.mul_mem hzMN.1 hzMN.1, Subgroup.mul_mem _ hzMN.2 hzMN.2⟩
    have e : ω * ω * elt L θ (swap a b * swap c d) * (ω * ω)⁻¹ =
        ω * (ω * elt L θ (swap a b * swap c d) * ω⁻¹) * ω⁻¹ := by group
    rwa [map_mul, map_mul, map_inv, map_mul, hzω, hc₀g, e, hconj, e1, hconj, e2] at this
  intro w hw
  rcases hall w hw with rfl | rfl | rfl | rfl
  · exact (autI hV N).one_mem
  · exact hgN
  · exact hx₁N
  · exact hx₂N

end PerComponent

section Main

theorem gen317A5_of_e23 (he23 : E2.E23Nonsolvable) : Gen317A5 := by
  intro G _ _ H T M₂ V hmin hsq hchar hV hJ hns hS
  classical
  have hVe : IsElemAbelian 2 V := hV.2.2.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hV.2.1
  set K := twoResidual H with hKdef
  set P := T ⊓ K with hPdef
  set S := baum T with hSdef
  set N := ⨆ y ∈ M₂ ⊓ Subgroup.normalizer (P : Set G), B6.conjSub y (S ⊓ K) with hNdef
  have hTH : T ≤ H := hmin.isSylow.1
  have hKH : K ≤ H := twoResidual_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_twoResidual H
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKH.trans hHN
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTH.trans hHN
  have hPsyl : IsSylowTwoOf P K := B6.isSylowTwoOf_inf_normal hmin.isSylow hKH hHK
  have hHV : ¬ H ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hJ ((B6.thompsonJ_le T).trans (hTH.trans h))
  have hQ : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 H :=
    hmin.inf_centralizer_eq_pCoreOf hV hHV
  have hTP : T ≤ Subgroup.normalizer (P : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hHK (hTH ht)⟩
  have hTS : T ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  obtain ⟨hKJ, I, hIcard, hJI, hcomm, hind, hconj, htype, -, -, h2, h3⟩ :=
    he23 G H T M₂ V hVe hmin hsq hchar hV hJ hns
  have hA5 : ∀ L ∈ I, E2.IsA5Module L := by
    by_contra hall
    push Not at hall
    obtain ⟨L₀, hL₀, hL₀a⟩ := hall
    have hL2 : ∀ L ∈ I, ∃ n : ℕ,
        E2.IsL2Natural L (fixV (autI hVe (twoResidual H))) n := by
      intro L hL
      rcases htype L hL with h | h
      · exact h
      · exfalso
        obtain ⟨t, -, ht⟩ := hconj L hL L₀ hL₀
        rcases htype L₀ hL₀ with ⟨n, hn⟩ | h0
        · have h1 := card_of_isL2Natural hn
          rw [← ht, card_conjAut, card_of_isA5Module h] at h1
          exact two_pow_mul_ne_120 n h1.symm
        · exact hL₀a h0
    exact hS (h2 hL2).2.2.1
  obtain ⟨hSJ, -, hL4⟩ := h3 hA5
  choose θ hθ using fun L (hL : L ∈ I) => (hL4 L hL).2
  have hT2 : IsPGroup 2 T := hmin.isSylow.2.1
  obtain ⟨alt, halt_eq⟩ : ∃ alt : Subgroup (MulAut (IntMod V hVe)) →
      Subgroup (MulAut (IntMod V hVe)), ∀ L (hL : L ∈ I), alt L = altOf L (θ L hL) :=
    ⟨fun L => if hL : L ∈ I then altOf L (θ L hL) else L, fun L hL => dite_eq_left hL⟩
  have hIH : (⨆ L ∈ I, L) ≤ autI hVe H := by
    rw [← hJI]
    exact autI_mono hVe (thompsonJ_le_self H)
  have hLH : ∀ L ∈ I, L ≤ autI hVe H := fun L hL =>
    (le_iSup₂_of_le (f := fun L' (_ : L' ∈ I) => L') L hL le_rfl).trans hIH
  have hAltK : ∀ L ∈ I, alt L ≤ autI hVe K := fun L hL => by
    rw [halt_eq L hL]
    exact altOf_le_of_odd fun x hx hodd => E2.mem_autI_twoResidual_of_odd (hLH L hL hx) hodd
  have hLalt : ∀ L ∈ I, alt L ≤ L ∧ L ≤ Subgroup.normalizer (alt L : Set _) ∧
      Nat.card (alt L) = 60 := fun L hL => by
    rw [halt_eq L hL]
    exact ⟨altOf_le, le_normalizer_altOf, card_altOf⟩
  have hsqL : ∀ L ∈ I, ∀ x ∈ L, x * x ∈ alt L := fun L hL x hx => by
    rw [halt_eq L hL]
    exact mul_self_mem_altOf hx
  have hKD : autI hVe K = ⨆ L ∈ I, alt L := by
    refine le_antisymm ?_ (iSup₂_le hAltK)
    intro φ hφ
    obtain ⟨g, hgK, rfl⟩ := (mem_autI hVe).1 hφ
    have hKD' : K ≤ ((⨆ L ∈ I, alt L).comap (convI hVe)).map
        (Subgroup.normalizer (V : Set G)).subtype := by
      rw [hKdef, F6.twoResidual_eq_oTwoUpper, oTwoUpper, Subgroup.closure_le]
      rintro x ⟨hxH, hxo⟩
      refine ⟨⟨x, hHN hxH⟩, ?_, rfl⟩
      show convI hVe ⟨x, hHN hxH⟩ ∈ ⨆ L ∈ I, alt L
      apply odd_mem_iSup_alt hIcard hcomm hsqL
      · rw [← hJI]
        exact convI_mem_autI hVe (hKJ (F6.mem_twoResidual_of_odd hxH hxo)) _
      · have h1 := orderOf_map_dvd (convI hVe) ⟨x, hHN hxH⟩
        rw [Subgroup.orderOf_mk] at h1
        exact hxo.of_dvd_nat h1
    obtain ⟨n, hn, hng⟩ := hKD' hgK
    have e : n = g := Subtype.ext hng
    rw [← e]
    exact hn
  have hPsylK : IsSylowTwoOf (autI hVe P) (autI hVe K) := B2F.isSylowTwoOf_autI hVe hKN hPsyl
  obtain ⟨hP4, hPdec⟩ := sylow_decomp hIcard hcomm hind hLalt (hKD ▸ hPsylK)
  have hPT : autI hVe P = autI hVe T ⊓ autI hVe K :=
    F1.eq_of_isSylowTwoOf_le hPsylK inf_le_right
      ((B2F.isPGroup_autI hVe hT2 hTN).to_le inf_le_left)
      (le_inf (autI_mono hVe inf_le_left) (autI_mono hVe inf_le_right))
  have hWT : ∀ L ∈ I, autI hVe T ⊓ alt L = autI hVe P ⊓ alt L := fun L hL => by
    rw [hPT, inf_assoc, inf_eq_right.mpr (hAltK L hL)]
  have hXM : H ⊓ Subgroup.normalizer (P : Set G) ≤ M₂ := by
    refine hmin.le_of_lt (le_inf hTH hTP) (lt_of_le_of_ne inf_le_left fun hX => ?_)
    have hHP : H ≤ Subgroup.normalizer (P : Set G) := by
      rw [← hX]
      exact inf_le_right
    have hPO : P ≤ pCoreOf 2 H := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (inf_le_left.trans hTH) hHP (hT2.to_le inf_le_left)
    have hPC : P ≤ Subgroup.centralizer (V : Set G) := by
      refine hPO.trans ?_
      rw [← hQ]
      exact inf_le_right
    obtain ⟨L, hL⟩ : I.Nonempty := Finset.card_pos.mp (by omega)
    have h4 := hP4 L hL
    rw [autI_eq_bot_of_le_centralizer hVe hPC, bot_inf_eq, Subgroup.card_bot] at h4
    omega
  have hdecL : ∀ L ∈ I, autI hVe P ≤ (autI hVe P ⊓ alt L) ⊔
      (autI hVe P ⊓ Subgroup.centralizer (L : Set (MulAut (IntMod V hVe)))) := by
    intro L hL
    refine hPdec.le.trans (iSup₂_le fun L' hL' => ?_)
    by_cases hLL : L' = L
    · rw [hLL]
      exact le_sup_left
    · refine le_sup_of_le_right (le_inf inf_le_left fun u hu => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hcomm L hL L' hL' (Ne.symm hLL) h hh u ((hLalt L' hL').1 hu.2)
  have hWN : ∀ L ∈ I, autI hVe P ⊓ alt L ≤ autI hVe N := by
    intro L hL
    have hcl : Nat.card (Subgroup.closure
        {x | ∃ hx : x ∈ L, x ∈ autI hVe T ∧ (θ L hL ⟨x, hx⟩).IsSwap}) = 4 := by
      rw [← hθ L hL]
      exact (hL4 L hL).1
    have hclS : Subgroup.closure
        {x | ∃ hx : x ∈ L, x ∈ autI hVe T ∧ (θ L hL ⟨x, hx⟩).IsSwap} ≤ autI hVe S := by
      rw [← hθ L hL, show autI hVe S = autI hVe (thompsonJ T) from hSJ]
      exact inf_le_right
    have hW4 := hP4 L hL
    rw [halt_eq L hL] at hW4
    have hTA : autI hVe T ⊓ altOf L (θ L hL) ≤ autI hVe P := by
      rw [← halt_eq L hL, hWT L hL]
      exact inf_le_left
    have haltK : altOf L (θ L hL) ≤ autI hVe K := by
      rw [← halt_eq L hL]
      exact hAltK L hL
    have hdec := hdecL L hL
    rw [halt_eq L hL] at hdec ⊢
    exact fourGroup_le_autI hVe (θ L hL) hHN hmin.isSylow hKH hHK
      (show baum T ≤ T from inf_le_left) hTS ((le_inf hTH hTP).trans hXM) hXM hcl hclS hW4 hTA
      haltK hdec
  have hPN : autI hVe P ≤ autI hVe N := hPdec.le.trans (iSup₂_le hWN)
  have hNP : N ≤ P := iSup₂_le fun u hu =>
    ((B6.conjSub u).monotone (inf_le_inf_right K (show baum T ≤ T from inf_le_left))).trans
      (B6.conjSub_eq_self hu.2).le
  have hPCK : P ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 K := by
    have h1 : P ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 H ⊓ K := by
      rw [← hQ, hPdef, inf_right_comm]
    rw [h1]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun k hk => ?_) ?_
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hk), hHK (hKH hk)⟩
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left
  intro t ht
  have htN : t ∈ Subgroup.normalizer (V : Set G) := hTN ht.1
  obtain ⟨x, hxN, hx⟩ := (mem_autI hVe).1 (hPN (convI_mem_autI hVe ht htN))
  have hxP : (x : G) ∈ P := hNP hxN
  have hxt : (x : G)⁻¹ * t ∈ Subgroup.centralizer (V : Set G) := by
    have h1 : convI hVe (x⁻¹ * ⟨t, htN⟩) = 1 := by rw [map_mul, map_inv, hx, inv_mul_cancel]
    exact (convI_eq_one_iff hVe _).1 h1
  have hxtO : (x : G)⁻¹ * t ∈ pCoreOf 2 K := hPCK ⟨P.mul_mem (P.inv_mem hxP) ht, hxt⟩
  have e : t = (x : G) * ((x : G)⁻¹ * t) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hxN hxtO

theorem as317SylowNonsolvable_of_e23 (he23 : E2.E23Nonsolvable) (hKer : Ker317A5) :
    AS317SylowNonsolvable :=
  as317SylowNonsolvable_of_inputs hKer (gen317A5_of_e23 he23)

end Main

end CFSG.Quasithin.Ch3n317A5
