module

public import CFSG.Quasithin.H13.NQS13410N

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_mul_of {H X : Subgroup G}
    (h : ∀ a ∈ X, ∀ b ∈ X, a ∉ H → b ∉ H → b⁻¹ * a ∈ H) :
    Nat.card ↥X ≤ 2 * Nat.card ↥H := by
  classical
  by_cases hX : X ≤ H
  · have := Subgroup.card_le_of_le hX
    omega
  obtain ⟨a₀, ha₀X, ha₀H⟩ := IsConcreteLE.not_le_iff_exists.1 hX
  let f : ↥X → ↥H × Bool := fun x =>
    if hx : (x : G) ∈ H then (⟨x, hx⟩, false) else (⟨a₀⁻¹ * x, h x x.2 a₀ ha₀X hx ha₀H⟩, true)
  have hf : Function.Injective f := by
    intro x y hxy
    simp only [f] at hxy
    by_cases hx : (x : G) ∈ H <;> by_cases hy : (y : G) ∈ H <;> simp [hx, hy] at hxy
    · exact hxy
    · exact hxy
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  linarith

theorem card_sup_eq_mul {N B : Subgroup G} (hinf : N ⊓ B = ⊥) (hBN : B ≤ normalizer (N : Set G)) :
    Nat.card ↥(N ⊔ B) = Nat.card ↥N * Nat.card ↥B := by
  refine le_antisymm ?_ (card_mul_le_card_sup hinf)
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun ab : ↥N × ↥B => (⟨ab.1 * ab.2, mul_mem (mem_sup_left ab.1.2)
      (mem_sup_right ab.2.2)⟩ : ↥(N ⊔ B))) ?_
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hBN hx
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem exists_compl_copy {K U W I₀ I₁ : Subgroup G} (C : L3Coords K U) [IsMulCommutative ↥W]
    (hUW : U ≤ W) (hI₀W : I₀ ≤ W) (hI₁W : I₁ ≤ W) (hKU : K ≤ normalizer (U : Set G))
    (hKI₀ : K ≤ normalizer (I₀ : Set G)) (hKI₁ : K ≤ normalizer (I₁ : Set G))
    (hinf : I₀ ⊓ I₁ = ⊥) (hsup : I₀ ⊔ I₁ = W) (φ₀ : ↥I₀ ≃* ↥I₁)
    (hφ₀ : ∀ k ∈ K, ∀ (u : ↥I₀) (hu : k * (u : G) * k⁻¹ ∈ I₀),
      ((φ₀ ⟨k * u * k⁻¹, hu⟩ : ↥I₁) : G) = k * (φ₀ u : G) * k⁻¹)
    (hU8 : Nat.card ↥U = 8) (hI8 : Nat.card ↥I₀ = 8) :
    ∃ I : Subgroup G, I ≤ W ∧ K ≤ normalizer (I : Set G) ∧ U ⊓ I = ⊥ ∧ U ⊔ I = W ∧
      ∃ φ : ↥U ≃* ↥I, ∀ k ∈ K, ∀ (u : ↥U) (hu : k * (u : G) * k⁻¹ ∈ U),
        ((φ ⟨k * u * k⁻¹, hu⟩ : ↥I) : G) = k * (φ u : G) * k⁻¹ := by
  classical
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥W) ⟨b, hb⟩)
  have hnorm : ∀ {A B : Subgroup G}, A ≤ W → B ≤ W → B ≤ normalizer (A : Set G) :=
    fun {A B} hA hB => A5.le_normalizer_of_forall_conj_mem fun b hb a ha => by
      rw [hcomm b (hB hb) a (hA ha), mul_inv_cancel_right]
      exact ha
  have hI18 : Nat.card ↥I₁ = 8 := by rw [← Nat.card_congr φ₀.toEquiv, hI8]
  have hW64 : Nat.card ↥W = 64 := by
    rw [← hsup, card_sup_eq_mul hinf (hnorm hI₀W hI₁W), hI8, hI18]
  have hKinf : ∀ {J : Subgroup G}, K ≤ normalizer (J : Set G) →
      K ≤ normalizer ((U ⊓ J : Subgroup G) : Set G) := fun {J} hJ k hk =>
    inf_normalizer_le_normalizer_inf ⟨hKU hk, hJ hk⟩
  have hcase := fun {J : Subgroup G} (hJ : K ≤ normalizer (J : Set G)) =>
    C.eq_bot_or_eq (inf_le_left : U ⊓ J ≤ U) (hKinf hJ)
  have heq : ∀ {J : Subgroup G}, Nat.card ↥J = 8 → U ⊓ J = U → U = J := fun {J} hJ8 h =>
    eq_of_le_of_card_ge (h ▸ inf_le_right) (by rw [hJ8, hU8])
  rcases hcase hKI₀ with h₀ | h₀
  · rcases hcase hKI₁ with h₁ | h₁
    ·
      refine ⟨I₀, hI₀W, hKI₀, h₀, ?_, ?_⟩
      · refine eq_of_le_of_card_ge (sup_le hUW hI₀W) ?_
        rw [card_sup_eq_mul h₀ (hnorm hUW hI₀W), hU8, hI8, hW64]
      have hdec : ∀ u : ↥U, ∃ a : ↥I₀, ∃ b : ↥I₁, (u : G) = a * b := by
        intro u
        obtain ⟨a, ha, b, hb, hab⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer
          (hnorm hI₀W hI₁W) (hsup.symm ▸ hUW u.2 : (u : G) ∈ I₀ ⊔ I₁)
        exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
      choose π₀ π₁ hπ using hdec
      have huniq : ∀ {a a' : ↥I₀} {b b' : ↥I₁}, (a : G) * b = a' * b' → a = a' ∧ b = b' := by
        intro a a' b b' h
        obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul hinf a'.2 a.2 b'.2 b.2 h
        exact ⟨Subtype.ext h1, Subtype.ext h2⟩
      have hmul : ∀ u v : ↥U, π₀ (u * v) = π₀ u * π₀ v := by
        intro u v
        have e : ((π₀ (u * v) : ↥I₀) : G) * (π₁ (u * v) : G) =
            ((π₀ u * π₀ v : ↥I₀) : G) * ((π₁ u * π₁ v : ↥I₁) : G) := by
          rw [← hπ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hπ u, hπ v]
          have := hcomm _ (hI₁W (π₁ u).2) _ (hI₀W (π₀ v).2)
          calc (π₀ u : G) * π₁ u * (π₀ v * π₁ v) = π₀ u * (π₁ u * π₀ v) * π₁ v := by group
            _ = π₀ u * (π₀ v * π₁ u) * π₁ v := by rw [this]
            _ = π₀ u * π₀ v * (π₁ u * π₁ v) := by group
        exact (huniq e).1
      let f : ↥U →* ↥I₀ :=
        { toFun := π₀
          map_one' := by
            have e : ((π₀ 1 : ↥I₀) : G) * (π₁ 1 : G) = ((1 : ↥I₀) : G) * ((1 : ↥I₁) : G) := by
              rw [← hπ]
              simp
            exact (huniq e).1
          map_mul' := hmul }
      have hfinj : Function.Injective f := by
        rw [injective_iff_map_eq_one]
        intro u hu
        have h1 : (u : G) = π₁ u := by
          rw [hπ u]
          have : π₀ u = 1 := hu
          rw [this, Subgroup.coe_one, one_mul]
        have h2 : (u : G) ∈ U ⊓ I₁ := mem_inf.2 ⟨u.2, h1 ▸ (π₁ u).2⟩
        rw [h₁, mem_bot] at h2
        exact Subtype.ext h2
      have hfsurj : Function.Surjective f := by
        have : Fintype ↥U := Fintype.ofFinite _
        have : Fintype ↥I₀ := Fintype.ofFinite _
        refine (Function.Injective.bijective_of_nat_card_le hfinj ?_).2
        rw [hU8, hI8]
      refine ⟨MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩, fun k hk u hu => ?_⟩
      show ((π₀ ⟨k * u * k⁻¹, hu⟩ : ↥I₀) : G) = k * (π₀ u : G) * k⁻¹
      have hka : k * (π₀ u : G) * k⁻¹ ∈ I₀ := (mem_normalizer_iff.mp (hKI₀ hk) _).mp (π₀ u).2
      have hkb : k * (π₁ u : G) * k⁻¹ ∈ I₁ := (mem_normalizer_iff.mp (hKI₁ hk) _).mp (π₁ u).2
      have e : ((π₀ ⟨k * u * k⁻¹, hu⟩ : ↥I₀) : G) * (π₁ ⟨k * u * k⁻¹, hu⟩ : G) =
          ((⟨k * (π₀ u : G) * k⁻¹, hka⟩ : ↥I₀) : G) *
            ((⟨k * (π₁ u : G) * k⁻¹, hkb⟩ : ↥I₁) : G) := by
        rw [← hπ]
        show k * (u : G) * k⁻¹ = k * (π₀ u : G) * k⁻¹ * (k * (π₁ u : G) * k⁻¹)
        rw [hπ u]
        group
      exact congrArg Subtype.val (huniq e).1
    ·
      have hU₁ := heq hI18 h₁
      refine ⟨I₀, hI₀W, hKI₀, ?_, ?_, ?_⟩
      · rw [hU₁, inf_comm, hinf]
      · rw [hU₁, sup_comm, hsup]
      · refine ⟨(MulEquiv.subgroupCongr hU₁).trans φ₀.symm, fun k hk u hu => ?_⟩
        have hu₁ : k * (u : G) * k⁻¹ ∈ I₁ := hU₁ ▸ hu
        set v : ↥I₀ := φ₀.symm ⟨u, hU₁ ▸ u.2⟩ with hv
        have hφv : φ₀ v = ⟨u, hU₁ ▸ u.2⟩ := by rw [hv, MulEquiv.apply_symm_apply]
        have hkv : k * (v : G) * k⁻¹ ∈ I₀ := (mem_normalizer_iff.mp (hKI₀ hk) _).mp v.2
        have h1 := hφ₀ k hk v hkv
        rw [hφv] at h1
        have h2 : φ₀.symm ⟨k * (u : G) * k⁻¹, hu₁⟩ = ⟨k * (v : G) * k⁻¹, hkv⟩ := by
          rw [MulEquiv.symm_apply_eq]
          exact Subtype.ext h1.symm
        show ((φ₀.symm ⟨k * (u : G) * k⁻¹, hu₁⟩ : ↥I₀) : G) =
          k * ((φ₀.symm ⟨u, hU₁ ▸ u.2⟩ : ↥I₀) : G) * k⁻¹
        rw [h2]
  ·
    have hU₀ := heq hI8 h₀
    refine ⟨I₁, hI₁W, hKI₁, ?_, ?_, ?_⟩
    · rw [hU₀, hinf]
    · rw [hU₀, hsup]
    · refine ⟨(MulEquiv.subgroupCongr hU₀).trans φ₀, fun k hk u hu => ?_⟩
      have hu₀ : k * (u : G) * k⁻¹ ∈ I₀ := hU₀ ▸ hu
      show ((φ₀ ⟨k * (u : G) * k⁻¹, hu₀⟩ : ↥I₁) : G) = k * ((φ₀ ⟨u, hU₀ ▸ u.2⟩ : ↥I₁) : G) * k⁻¹
      exact hφ₀ k hk ⟨u, hU₀ ▸ u.2⟩ hu₀

variable {K U I : Subgroup G}

theorem relIndex_mul_card_le_thirtytwo (C : L3Coords K U) (hUI : U ⊓ I = ⊥)
    (hcomm : ∀ a ∈ U ⊔ I, ∀ b ∈ U ⊔ I, a * b = b * a) (hKU : K ≤ normalizer (U : Set G))
    (hKI : K ≤ normalizer (I : Set G)) (φ : ↥U ≃* ↥I)
    (hφ : ∀ k ∈ K, ∀ (u : ↥U) (hu : k * (u : G) * k⁻¹ ∈ U),
      ((φ ⟨k * u * k⁻¹, hu⟩ : ↥I) : G) = k * (φ u : G) * k⁻¹)
    (htop : autOn K U = ⊤) (hU8 : Nat.card ↥U = 8) {A : Subgroup G}
    (hAU : A ≤ normalizer (U : Set G)) (hAW : A ≤ normalizer ((U ⊔ I : Subgroup G) : Set G))
    (hAK : A ≤ normalizer (K : Set G)) {p : L3.Vec} (hp : p ≠ 0)
    (hAE : ∀ a : ↥(normalizer (U : Set G)), (a : G) ∈ A → C.ρ a ∈ L3.AS {0, p})
    (hA : ¬ A ≤ centralizer ((U ⊔ I : Subgroup G) : Set G)) :
    (A ⊓ centralizer ((U ⊔ I : Subgroup G) : Set G)).relIndex A *
      Nat.card ↥((U ⊔ I) ⊓ centralizer (A : Set G)) ≤ 32 := by
  classical
  set W := U ⊔ I with hWdef
  have hIU : I ≤ normalizer (U : Set G) :=
    A5.le_normalizer_of_forall_conj_mem fun i hi u hu => by
      rw [hcomm i (mem_sup_right hi) u (mem_sup_left hu), mul_inv_cancel_right]
      exact hu
  have hUW : U ≤ W := le_sup_left
  have hCWU : centralizer (W : Set G) ≤ centralizer (U : Set G) := centralizer_le hUW
  have hact : ∀ a ∈ A,
      (∀ u : ↥U, ∀ hu : a * (u : G) * a⁻¹ ∈ U, a * (φ u : G) * a⁻¹ = φ ⟨a * u * a⁻¹, hu⟩) ∨
      (∀ u : ↥U, ∀ hu : a * (u : G) * a⁻¹ ∈ U,
        a * (φ u : G) * a⁻¹ = (a * (u : G) * a⁻¹) * φ ⟨a * u * a⁻¹, hu⟩) := by
    intro a ha
    obtain ⟨k, hk, hka, h⟩ :=
      exists_conj_phi C hUI hIU hKU hKI φ hφ htop (hAU ha) (hAW ha) (hAK ha)
    have hφk : ∀ (u : ↥U) (hu : a * (u : G) * a⁻¹ ∈ U),
        ((φ ⟨a * u * a⁻¹, hu⟩ : ↥I) : G) = k * (φ u : G) * k⁻¹ := by
      intro u hu
      have hku : k * (u : G) * k⁻¹ ∈ U := (hka u u.2) ▸ hu
      have e : (⟨a * u * a⁻¹, hu⟩ : ↥U) = ⟨k * u * k⁻¹, hku⟩ := Subtype.ext (hka u u.2)
      rw [e, hφ k hk u hku]
    rcases h with h | h
    · exact Or.inl fun u hu => by rw [h u, hφk u hu]
    · exact Or.inr fun u hu => by rw [h u, hφk u hu, hka u u.2]
  have hCW_of : ∀ a ∈ A, a ∈ centralizer (U : Set G) →
      (∀ u : ↥U, a * (φ u : G) * a⁻¹ = φ u) → a ∈ centralizer (W : Set G) := by
    intro a _ haU h
    have hle : W ≤ centralizer ({a} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun i hi => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.mp haU x hx
      · rw [mem_centralizer_singleton_iff]
        set u : ↥U := φ.symm ⟨i, hi⟩ with hu
        have hφu : (φ u : G) = i := by rw [hu, MulEquiv.apply_symm_apply]
        have h1 := h u
        rw [hφu] at h1
        calc i * a = a * i * a⁻¹ * a := by rw [h1]
          _ = a * i := by group
    exact mem_centralizer_iff.2 fun w hw => mem_centralizer_singleton_iff.mp (hle hw)
  have hfixU : ∀ a ∈ A, a ∈ centralizer (U : Set G) → ∀ u : ↥U, a * (u : G) * a⁻¹ = u :=
    fun a _ haU u => by rw [← mem_centralizer_iff.mp haU u u.2, mul_inv_cancel_right]
  have hrel := relIndex_mul_relIndex (A ⊓ centralizer (W : Set G))
    (A ⊓ centralizer (U : Set G)) A (inf_le_inf_left _ hCWU) inf_le_left
  have hdec : ∀ w ∈ W, ∃ x ∈ U, ∃ y : ↥U, w = x * φ y := by
    intro w hw
    obtain ⟨x, hx, i, hi, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hIU hw
    exact ⟨x, hx, φ.symm ⟨i, hi⟩, by rw [MulEquiv.apply_symm_apply]⟩
  have huniq : ∀ {x x' : G} {y y' : ↥U}, x ∈ U → x' ∈ U → x * (φ y : G) = x' * φ y' →
      x = x' ∧ y = y' := by
    intro x x' y y' hx hx' h
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul hUI hx' hx (φ y').2 (φ y).2 h
    exact ⟨h1, φ.injective (Subtype.ext h2)⟩
  have hU1 : ∀ {x : G} {y : ↥U}, x ∈ U → x * (φ y : G) ∈ U → y = 1 := by
    intro x y hx h
    have h1 : (φ y : G) ∈ U ⊓ I :=
      mem_inf.2 ⟨by simpa using mul_mem (inv_mem hx) h, (φ y).2⟩
    rw [hUI, mem_bot] at h1
    exact φ.injective (Subtype.ext (by rw [h1, map_one, Subgroup.coe_one]))
  have hb := fun h : ¬ A ≤ centralizer (U : Set G) => C.relIndex_mul_card_le hAU hp hAE h
  by_cases hβ : A ⊓ centralizer (U : Set G) ≤ centralizer (W : Set G)
  ·
    have h1 : (A ⊓ centralizer (W : Set G)).relIndex (A ⊓ centralizer (U : Set G)) = 1 :=
      relIndex_eq_one.2 (le_inf inf_le_left hβ)
    rw [h1, one_mul] at hrel
    have hAU' : ¬ A ≤ centralizer (U : Set G) := fun h => hA fun a ha => hβ ⟨ha, h ha⟩
    have hC4 : Nat.card ↥(U ⊓ centralizer (A : Set G)) ≤ 4 := by
      refine card_le_four_of_lt hU8 inf_le_left fun h => hAU' fun a ha => ?_
      rw [mem_centralizer_iff]
      intro u hu
      have hu' : u ∈ U ⊓ centralizer (A : Set G) := by rw [h]; exact hu
      exact (mem_centralizer_iff.mp (mem_inf.1 hu').2 a ha).symm
    set IA : Subgroup G := ((U ⊓ centralizer (A : Set G)).subgroupOf U).map
      (I.subtype.comp φ.toMonoidHom) with hIA
    have hIAI : IA ≤ I := by
      rintro _ ⟨y, -, rfl⟩
      exact (φ y).2
    have hPle : W ⊓ centralizer (A : Set G) ≤ U ⊔ IA := by
      intro w hw
      obtain ⟨hwW, hwA⟩ := mem_inf.1 hw
      obtain ⟨x, hx, y, rfl⟩ := hdec w hwW
      have hyA : (y : G) ∈ centralizer (A : Set G) := mem_centralizer_iff.2 fun a ha => by
        have hay : a * (y : G) * a⁻¹ ∈ U := (mem_normalizer_iff.mp (hAU ha) y).mp y.2
        have hax : a * x * a⁻¹ ∈ U := (mem_normalizer_iff.mp (hAU ha) x).mp hx
        have hfix : a * (x * φ y) * a⁻¹ = x * φ y := by
          rw [mem_centralizer_iff.mp hwA a ha, mul_inv_cancel_right]
        have e : a * (x * (φ y : G)) * a⁻¹ = (a * x * a⁻¹) * (a * (φ y : G) * a⁻¹) := by group
        rw [e] at hfix
        have hy' : (⟨a * (y : G) * a⁻¹, hay⟩ : ↥U) = y := by
          rcases hact a ha with h | h
          · rw [h y hay] at hfix
            exact (huniq hax hx hfix).2
          · rw [h y hay, ← mul_assoc] at hfix
            exact (huniq (mul_mem hax hay) hx hfix).2
        have h2 : a * (y : G) * a⁻¹ = y := congrArg Subtype.val hy'
        calc a * (y : G) = a * y * a⁻¹ * a := by group
          _ = y * a := by rw [h2]
      exact mul_mem (mem_sup_left hx)
        (mem_sup_right ⟨y, mem_subgroupOf.2 (mem_inf.2 ⟨y.2, hyA⟩), rfl⟩)
    have hIAU : IA ≤ normalizer (U : Set G) := hIAI.trans hIU
    have hcardIA : Nat.card ↥IA ≤ Nat.card ↥(U ⊓ centralizer (A : Set G)) := by
      have hinj : Function.Injective (I.subtype.comp φ.toMonoidHom) :=
        I.subtype_injective.comp φ.injective
      rw [hIA, Subgroup.card_map_of_injective hinj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    have hrelIA : U.relIndex (U ⊔ IA) = Nat.card ↥IA := by
      have h2 := relIndex_mul_card U (U ⊔ IA)
      rw [inf_eq_left.2 le_sup_left, card_sup_eq_mul
        (eq_bot_iff.2 fun x hx => by
          rw [← hUI]
          exact mem_inf.2 ⟨(mem_inf.1 hx).1, hIAI (mem_inf.1 hx).2⟩) hIAU] at h2
      have hpos : 0 < Nat.card ↥U := Nat.card_pos
      nlinarith
    have hCWA : Nat.card ↥(W ⊓ centralizer (A : Set G)) ≤
        Nat.card ↥(U ⊓ centralizer (A : Set G)) * Nat.card ↥(U ⊓ centralizer (A : Set G)) := by
      have h2 := relIndex_mul_card U (W ⊓ centralizer (A : Set G))
      have h3 : U.relIndex (W ⊓ centralizer (A : Set G)) ≤ U.relIndex (U ⊔ IA) :=
        relIndex_le_of_le_right hPle (by
          show (U.subgroupOf (U ⊔ IA)).index ≠ 0
          exact Subgroup.index_ne_zero_of_finite)
      have h4 : Nat.card ↥(U ⊓ (W ⊓ centralizer (A : Set G))) ≤
          Nat.card ↥(U ⊓ centralizer (A : Set G)) :=
        Subgroup.card_le_of_le (inf_le_inf_left _ inf_le_right)
      rw [← h2]
      exact Nat.mul_le_mul (h3.trans (hrelIA.le.trans hcardIA)) h4
    rw [← hrel]
    calc (A ⊓ centralizer (U : Set G)).relIndex A * Nat.card ↥(W ⊓ centralizer (A : Set G))
        ≤ (A ⊓ centralizer (U : Set G)).relIndex A *
            (Nat.card ↥(U ⊓ centralizer (A : Set G)) *
              Nat.card ↥(U ⊓ centralizer (A : Set G))) := Nat.mul_le_mul_left _ hCWA
      _ = (A ⊓ centralizer (U : Set G)).relIndex A * Nat.card ↥(U ⊓ centralizer (A : Set G)) *
            Nat.card ↥(U ⊓ centralizer (A : Set G)) := by ring
      _ ≤ 8 * 4 := Nat.mul_le_mul (hb hAU') hC4
  ·
    obtain ⟨a₀, ha₀, ha₀W⟩ := IsConcreteLE.not_le_iff_exists.1 hβ
    obtain ⟨ha₀A, ha₀U⟩ := mem_inf.1 ha₀
    have htype1 : ∀ a ∈ A, a ∈ centralizer (U : Set G) → a ∉ centralizer (W : Set G) →
        ∀ u : ↥U, a * (φ u : G) * a⁻¹ = u * φ u := by
      intro a ha haU haW u
      rcases hact a ha with h | h
      · exfalso
        refine haW (hCW_of a ha haU fun v => ?_)
        rw [h v (by rw [hfixU a ha haU v]; exact v.2)]
        congr 1
        exact congrArg φ (Subtype.ext (hfixU a ha haU v))
      · have hu : a * (u : G) * a⁻¹ ∈ U := by rw [hfixU a ha haU u]; exact u.2
        rw [h u hu]
        have e : (⟨a * (u : G) * a⁻¹, hu⟩ : ↥U) = u := Subtype.ext (hfixU a ha haU u)
        rw [e, hfixU a ha haU u]
    have hCWU' : W ⊓ centralizer (A : Set G) ≤ U ⊓ centralizer (A : Set G) := by
      intro w hw
      obtain ⟨hwW, hwA⟩ := mem_inf.1 hw
      refine mem_inf.2 ⟨?_, hwA⟩
      obtain ⟨x, hx, y, rfl⟩ := hdec w hwW
      have hfix : a₀ * (x * φ y) * a₀⁻¹ = x * φ y := by
        rw [mem_centralizer_iff.mp hwA a₀ ha₀A, mul_inv_cancel_right]
      have e : a₀ * (x * (φ y : G)) * a₀⁻¹ = (a₀ * x * a₀⁻¹) * (a₀ * (φ y : G) * a₀⁻¹) := by
        group
      rw [e, htype1 a₀ ha₀A ha₀U ha₀W y, hfixU a₀ ha₀A ha₀U ⟨x, hx⟩] at hfix
      have hy : (y : G) = 1 := by
        have h2 : (y : G) * φ y = φ y := mul_left_cancel hfix
        exact mul_right_cancel (h2.trans (one_mul _).symm)
      have hy1 : y = 1 := Subtype.ext hy
      rw [hy1, map_one, Subgroup.coe_one, mul_one]
      exact hx
    have h2 : (A ⊓ centralizer (W : Set G)).relIndex (A ⊓ centralizer (U : Set G)) ≤ 2 := by
      have hle := card_le_two_mul_of (H := A ⊓ centralizer (W : Set G))
          (X := A ⊓ centralizer (U : Set G)) fun a ha b hb haW hbW => by
        obtain ⟨haA, haU⟩ := mem_inf.1 ha
        obtain ⟨hbA, hbU⟩ := mem_inf.1 hb
        have haW' : a ∉ centralizer (W : Set G) := fun h => haW (mem_inf.2 ⟨haA, h⟩)
        have hbW' : b ∉ centralizer (W : Set G) := fun h => hbW (mem_inf.2 ⟨hbA, h⟩)
        have hbaA : b⁻¹ * a ∈ A := mul_mem (inv_mem hbA) haA
        have hbaU : b⁻¹ * a ∈ centralizer (U : Set G) := mul_mem (inv_mem hbU) haU
        refine mem_inf.2 ⟨hbaA, hCW_of _ hbaA hbaU fun u => ?_⟩
        have h1 := htype1 a haA haU haW' u
        have h3 := htype1 b hbA hbU hbW' u
        have hbu : b⁻¹ * (u : G) * b = u := by
          have := mem_centralizer_iff.mp (inv_mem hbU) u u.2
          calc b⁻¹ * (u : G) * b = b⁻¹ * u * b⁻¹⁻¹ := by group
            _ = u := by rw [← this, mul_inv_cancel_right]
        have e : (u : G) * (b⁻¹ * (φ u : G) * b) = φ u := by
          calc (u : G) * (b⁻¹ * (φ u : G) * b)
              = (b⁻¹ * (u : G) * b) * (b⁻¹ * (φ u : G) * b) := by rw [hbu]
            _ = b⁻¹ * ((u : G) * φ u) * b := by group
            _ = b⁻¹ * (b * (φ u : G) * b⁻¹) * b := by rw [h3]
            _ = φ u := by group
        have h4 : b⁻¹ * (φ u : G) * b = (u : G)⁻¹ * φ u := eq_inv_mul_of_mul_eq e
        calc b⁻¹ * a * (φ u : G) * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * (φ u : G) * a⁻¹) * b := by group
          _ = b⁻¹ * ((u : G) * φ u) * b := by rw [h1]
          _ = (b⁻¹ * (u : G) * b) * (b⁻¹ * (φ u : G) * b) := by group
          _ = φ u := by rw [hbu, h4]; group
      have h5 := relIndex_mul_card (A ⊓ centralizer (W : Set G)) (A ⊓ centralizer (U : Set G))
      rw [inf_eq_left.2 (inf_le_inf_left A hCWU)] at h5
      have hpos : 0 < Nat.card ↥(A ⊓ centralizer (W : Set G)) := Nat.card_pos
      nlinarith
    rw [← hrel]
    have hCcard : Nat.card ↥(W ⊓ centralizer (A : Set G)) ≤
        Nat.card ↥(U ⊓ centralizer (A : Set G)) := Subgroup.card_le_of_le hCWU'
    by_cases hAU' : A ≤ centralizer (U : Set G)
    · have h1 : (A ⊓ centralizer (U : Set G)).relIndex A = 1 :=
        relIndex_eq_one.2 (le_inf le_rfl hAU')
      have h3 : Nat.card ↥(U ⊓ centralizer (A : Set G)) ≤ 8 := by
        rw [← hU8]
        exact Subgroup.card_le_of_le inf_le_left
      rw [h1, mul_one]
      nlinarith
    · have h3 := hb hAU'
      calc (A ⊓ centralizer (W : Set G)).relIndex (A ⊓ centralizer (U : Set G)) *
            (A ⊓ centralizer (U : Set G)).relIndex A * Nat.card ↥(W ⊓ centralizer (A : Set G))
          ≤ 2 * ((A ⊓ centralizer (U : Set G)).relIndex A *
              Nat.card ↥(U ⊓ centralizer (A : Set G))) := by
            rw [mul_assoc]
            exact Nat.mul_le_mul h2 (Nat.mul_le_mul_left _ hCcard)
        _ ≤ 2 * 8 := Nat.mul_le_mul_left _ h3
        _ ≤ 32 := by norm_num

theorem sixteen_le_relIndex_centralizer (hUI : U ⊓ I = ⊥)
    (hcomm : ∀ a ∈ U ⊔ I, ∀ b ∈ U ⊔ I, a * b = b * a) (hKU : K ≤ normalizer (U : Set G))
    (hKI : K ≤ normalizer (I : Set G)) (φ : ↥U ≃* ↥I)
    (hφ : ∀ k ∈ K, ∀ (u : ↥U) (hu : k * (u : G) * k⁻¹ ∈ U),
      ((φ ⟨k * u * k⁻¹, hu⟩ : ↥I) : G) = k * (φ u : G) * k⁻¹)
    (hW2 : IsPGroup 2 ↥(U ⊔ I)) {y : G} (hyK : y ∈ K) (hy3 : y ^ 3 = 1)
    (hyU : y ∉ centralizer (U : Set G)) :
    16 ≤ (centralizer ({y} : Set G)).relIndex (U ⊔ I) := by
  set W := U ⊔ I with hWdef
  have hIU : I ≤ normalizer (U : Set G) :=
    A5.le_normalizer_of_forall_conj_mem fun i hi u hu => by
      rw [hcomm i (mem_sup_right hi) u (mem_sup_left hu), mul_inv_cancel_right]
      exact hu
  have hWU : W ≤ normalizer (U : Set G) :=
    A5.le_normalizer_of_forall_conj_mem fun w hw u hu => by
      rw [hcomm w hw u (mem_sup_left hu), mul_inv_cancel_right]
      exact hu
  have hyN₀ : y ∈ normalizer (U : Set G) := hKU hyK
  have hyN₁ : y ∈ normalizer (I : Set G) := hKI hyK
  have hyW : y ∈ normalizer (W : Set G) := le_normalizer_sup_of hIU hKU hKI hyK
  have hc₀4 : 4 ≤ (centralizer ({y} : Set G)).relIndex U :=
    U3.four_le_relIndex_centralizer hy3 hyN₀ (hW2.to_le le_sup_left) fun h => hyU
      (mem_centralizer_iff.mpr fun w hw => mem_centralizer_singleton_iff.mp (h hw))
  have h1 := U3.relIndex_centralizer_eq_mul (x := y) (le_sup_left : U ≤ W) hWU
  rcases U3.relIndex_sup_eq_one_or hy3 hW2 le_sup_left hWU hyN₀ hyW with h2 | h2
  · exfalso
    have h3 : W ≤ U ⊔ (W ⊓ centralizer ({y} : Set G)) := relIndex_eq_one.mp h2
    have hyI : ∀ b ∈ I, y * b * y⁻¹ = b := by
      intro b hb
      obtain ⟨a, ha, c, hc, hac⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer
        (inf_le_left.trans hWU) (h3 (mem_sup_right hb))
      have hcy : c * y = y * c := mem_centralizer_singleton_iff.mp (mem_inf.1 hc).2
      have hcy' : c * y⁻¹ = y⁻¹ * c := by
        calc c * y⁻¹ = y⁻¹ * (y * c) * y⁻¹ := by group
          _ = y⁻¹ * (c * y) * y⁻¹ := by rw [← hcy]
          _ = y⁻¹ * c := by group
      have hyb : y * b * y⁻¹ * b⁻¹ ∈ U ⊓ I := by
        refine mem_inf.2 ⟨?_, mul_mem ((mem_normalizer_iff.mp hyN₁ b).mp hb) (inv_mem hb)⟩
        rw [hac]
        have e : y * (a * c) * y⁻¹ * (a * c)⁻¹ = y * a * y⁻¹ * a⁻¹ := by
          calc y * (a * c) * y⁻¹ * (a * c)⁻¹ = y * a * (c * y⁻¹) * c⁻¹ * a⁻¹ := by group
            _ = y * a * (y⁻¹ * c) * c⁻¹ * a⁻¹ := by rw [hcy']
            _ = y * a * y⁻¹ * a⁻¹ := by group
        rw [e]
        exact mul_mem ((mem_normalizer_iff.mp hyN₀ a).mp ha) (inv_mem ha)
      rw [hUI, mem_bot] at hyb
      calc y * b * y⁻¹ = (y * b * y⁻¹ * b⁻¹) * b := by group
        _ = b := by rw [hyb, one_mul]
    apply hyU
    rw [mem_centralizer_iff]
    intro u hu
    have hyu : y * u * y⁻¹ ∈ U := (mem_normalizer_iff.mp hyN₀ u).mp hu
    have h4 := hφ y hyK ⟨u, hu⟩ hyu
    rw [hyI _ (φ ⟨u, hu⟩).2] at h4
    have h5 : (⟨y * u * y⁻¹, hyu⟩ : ↥U) = ⟨u, hu⟩ := φ.injective (Subtype.ext h4)
    have h6 : y * u * y⁻¹ = u := congrArg Subtype.val h5
    calc u * y = y * u * y⁻¹ * y := by rw [h6]
      _ = y * u := by group
  · rw [h1]
    calc 16 = 4 * 4 := by norm_num
      _ ≤ _ := Nat.mul_le_mul h2 hc₀4

end CFSG.Quasithin.H13.NQS134
