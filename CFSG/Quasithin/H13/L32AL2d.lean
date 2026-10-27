module

public import CFSG.Quasithin.H13.L32AL2a
public import CFSG.Quasithin.H13.L32AL2b
public import CFSG.Quasithin.EmptyFaithful.S146zHCls

public section

namespace CFSG.Quasithin.H13.L32A.L2

section Abstract

open CFSG.Quasithin CFSG.Quasithin.B1

variable {V : Type} [CommGroup V] [Finite V]

theorem fix_of_isSimpleGroup {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : 24 < Nat.card X) (ρ : X →* MulAut V) {A : Subgroup V} (hA : Nat.card A = 4)
    (hinv : ∀ x : X, ∀ a ∈ A, ρ x a ∈ A) : ∀ x : X, ∀ a ∈ A, ρ x a = a := by
  classical
  have hiff : ∀ x : X, ∀ a : V, a ∈ A ↔ ρ x a ∈ A := fun x a =>
    ⟨fun h => hinv x a h, fun h => by
      have := hinv x⁻¹ _ h
      rwa [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply] at this⟩
  let f : X →* Equiv.Perm ↥A :=
    { toFun := fun x => (ρ x).toEquiv.subtypeEquiv (hiff x)
      map_one' := by ext a; simp
      map_mul' := fun x y => by ext a; simp }
  have hker : f.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exfalso
      have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp h
      have := Nat.card_le_card_of_injective f hinj
      rw [Nat.card_perm, hA] at this
      have h24 : Nat.factorial 4 = 24 := rfl
      omega
    · exact h
  intro x a ha
  have hx : f x = 1 := by
    have : x ∈ f.ker := hker ▸ Subgroup.mem_top x
    exact this
  have := congrArg (fun e : Equiv.Perm ↥A => (e ⟨a, ha⟩ : V)) hx
  simpa [f] using this

theorem false_of_conj_inv_three (hV : ∀ v : V, v ^ 2 = 1) {Γ : Type} [Group Γ]
    (ρ : Γ →* MulAut V) {τ : Γ} (hτ : IsTransvection (ρ τ)) {N : Subgroup Γ} [Finite ↥N]
    [IsSimpleGroup ↥N] (hN : 24 < Nat.card N) {k₁ k₂ g : Γ} (hk₃ : k₁ ^ 3 = 1)
    (hk₁ : ρ k₁ ≠ 1) (hcomm : ∀ n ∈ N, n * k₁ = k₁ * n)
    (hinv : τ * (g * k₁ * g⁻¹) * τ⁻¹ = (g * k₁ * g⁻¹)⁻¹) (hk₂ : k₂ ∈ N) {P : Subgroup V}
    (hP : P ≠ ⊥) (hsame : ∀ w ∈ P, ρ k₁ w = ρ k₂ w) (hfpf : ∀ w ∈ P, ρ k₁ w = w → w = 1) :
    False := by
  have hτ' : IsTransvection (ρ (g⁻¹ * τ * g)) := by
    simpa only [map_mul, map_inv, inv_inv] using B1.isTransvection_conj hτ (ρ g)⁻¹
  have hinvΓ : (g⁻¹ * τ * g) * k₁ * (g⁻¹ * τ * g)⁻¹ = k₁⁻¹ := by
    have e : (g⁻¹ * τ * g) * k₁ * (g⁻¹ * τ * g)⁻¹ = g⁻¹ * (τ * (g * k₁ * g⁻¹) * τ⁻¹) * g := by
      group
    rw [e, hinv]
    group
  have hinv' : ρ (g⁻¹ * τ * g) * ρ k₁ * (ρ (g⁻¹ * τ * g))⁻¹ = (ρ k₁)⁻¹ := by
    simpa only [map_mul, map_inv] using congrArg ρ hinvΓ
  obtain ⟨ht1, w, hw⟩ := hτ'
  have h3 : (ρ k₁) ^ 3 = 1 := by rw [← map_pow, hk₃, map_one]
  obtain ⟨-, -, hcard, -⟩ :=
    B1.inverted_by_transvection hV hw ht1 (r := 3) (by decide) h3 hk₁ hinv'
  set A := commSub ⊤ (Subgroup.zpowers (ρ k₁)) with hAdef
  have hNA : ∀ n ∈ N, ∀ a ∈ A, ρ n a = a := by
    have hpres : ∀ n : ↥N, ∀ a ∈ A, (ρ.comp N.subtype) n a ∈ A := by
      intro n a ha
      refine B1.commSub_smul_mem (M := ⊤) (M' := ⊤) (Y := Subgroup.zpowers (ρ k₁))
        (Y' := Subgroup.zpowers (ρ k₁)) (ρ n) (fun y hy => ?_) (fun m _ => Subgroup.mem_top _) a ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hc : Commute (ρ n) (ρ k₁) := by
        show ρ n * ρ k₁ = ρ k₁ * ρ n
        simpa only [map_mul] using congrArg ρ (hcomm n n.2)
      rw [(hc.zpow_right j).eq, mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.zpow_mem_zpowers _ j
    intro n hn a ha
    exact fix_of_isSimpleGroup hN (ρ.comp N.subtype) hcard hpres ⟨n, hn⟩ a ha
  have hYodd : Odd (Nat.card (Subgroup.zpowers (ρ k₁))) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)
  obtain ⟨hsup0, -⟩ := B1.coprime_decomp hV hYodd (M := ⊤) (fun _ _ _ _ => trivial)
  have hsup : fixV (Subgroup.zpowers (ρ k₁)) ⊔ A = ⊤ := by simpa using hsup0
  have hc12 : Commute (ρ k₂) (ρ k₁) := by
    show ρ k₂ * ρ k₁ = ρ k₁ * ρ k₂
    simpa only [map_mul] using congrArg ρ (hcomm k₂ hk₂)
  apply hP
  refine eq_bot_of_same_action hV (A := A) (B := fixV (Subgroup.zpowers (ρ k₁)))
    (y₁ := ρ k₁) (y₂ := ρ k₂) h3 (fun b hb => ?_) (fun b hb => hb _ (Subgroup.mem_zpowers _))
    (fun a ha => hNA k₂ hk₂ a ha) (by rw [sup_comm, hsup]; exact le_top) hsame hfpf
  refine B1.fixV_smul_mem (ρ k₂) (fun y hy => ?_) hb
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [(hc12.inv_left.zpow_right j).eq, mul_assoc, inv_mul_cancel, mul_one]
  exact Subgroup.zpow_mem_zpowers _ j

theorem not_isTransvection (hV : ∀ v : V, v ^ 2 = 1) {Γ : Type} [Group Γ] [Finite Γ]
    (ρ : Γ →* MulAut V) (hρ : Function.Injective ρ) {N₁ N₂ : Subgroup Γ}
    (φ₁ : ↥N₁ ≃* alternatingGroup (Fin 5)) (φ₂ : ↥N₂ ≃* alternatingGroup (Fin 5))
    (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hint : ∀ z ∈ N₁, z ∈ N₂ → z = 1)
    (hcen : ∀ c : Γ, c * c = 1 → (∀ a ∈ N₁, c * a = a * c) → (∀ b ∈ N₂, c * b = b * c) → c = 1)
    (hnorm : ∀ c : Γ,
      ((∀ a ∈ N₁, c * a * c⁻¹ ∈ N₁) ∧ ∀ b ∈ N₂, c * b * c⁻¹ ∈ N₂) ∨ ∀ a ∈ N₁, c * a * c⁻¹ ∈ N₂)
    {k₁ k₂ : Γ} (hk₁ : k₁ ∈ N₁) (hk₂ : k₂ ∈ N₂) (hk₁3 : k₁ ^ 3 = 1) (hk₂3 : k₂ ^ 3 = 1)
    {P : Subgroup V} (hP : P ≠ ⊥) (hsame : ∀ w ∈ P, ρ k₁ w = ρ k₂ w)
    (hfpf : ∀ w ∈ P, ρ k₁ w = w → w = 1) (τ : Γ) : ¬ IsTransvection (ρ τ) := by
  intro hτ
  obtain ⟨ht1, w, hw⟩ := hτ
  have hττ : τ * τ = 1 := hρ (by rw [map_mul, B1.tv_sq hV hw ht1, map_one])
  have hA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hs5 : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hN₁s : IsSimpleGroup ↥N₁ := (MulEquiv.isSimpleGroup_congr φ₁).mpr hs5
  have hN₂s : IsSimpleGroup ↥N₂ := (MulEquiv.isSimpleGroup_congr φ₂).mpr hs5
  have hN₁c : 24 < Nat.card ↥N₁ := by rw [Nat.card_congr φ₁.toEquiv, hA5]; norm_num
  have hN₂c : 24 < Nat.card ↥N₂ := by rw [Nat.card_congr φ₂.toEquiv, hA5]; norm_num
  have hfpf₂ : ∀ w ∈ P, ρ k₂ w = w → w = 1 := fun w' hw' h => hfpf w' hw' ((hsame w' hw').trans h)
  have hne : ∀ k : Γ, (∀ w ∈ P, ρ k w = w → w = 1) → ρ k ≠ 1 := by
    intro k hk h1
    apply hP
    rw [eq_bot_iff]
    intro w' hw'
    exact (Subgroup.mem_bot).mpr (hk w' hw' (by rw [h1]; rfl))
  have hρk₁ := hne k₁ hfpf
  have hρk₂ := hne k₂ hfpf₂
  have hsub1 : ∀ (N : Subgroup Γ) (k : Γ) (hk : k ∈ N), ρ k ≠ 1 → (⟨k, hk⟩ : ↥N) ≠ 1 :=
    fun N k hk h e => h (by rw [show k = 1 from congrArg Subtype.val e, map_one])
  have hsub3 : ∀ (N : Subgroup Γ) (k : Γ) (hk : k ∈ N), k ^ 3 = 1 → (⟨k, hk⟩ : ↥N) ^ 3 = 1 :=
    fun N k hk h => Subtype.ext (by simpa using h)
  have five : ∀ x : Γ, x ^ 5 = 1 → x ≠ 1 → τ * x * τ⁻¹ = x⁻¹ → False := fun x hx5 hx1 hinv =>
    false_of_inv_five hV ⟨ht1, w, hw⟩ (x := ρ x) (by rw [← map_pow, hx5, map_one])
      (fun h => hx1 (hρ (h.trans (map_one ρ).symm)))
      (by simpa only [map_mul, map_inv] using congrArg ρ hinv)
  rcases hnorm τ with ⟨h₁, h₂⟩ | hsw
  ·
    have mkσ : ∀ N : Subgroup Γ, (∀ a ∈ N, τ * a * τ⁻¹ ∈ N) →
        ∃ σ : MulAut ↥N, σ * σ = 1 ∧ ∀ a : ↥N, (σ a : Γ) = τ * a * τ⁻¹ := by
      intro N hN
      have key : ∀ a : Γ, τ * (τ * a * τ⁻¹) * τ⁻¹ = a := fun a => by
        calc τ * (τ * a * τ⁻¹) * τ⁻¹ = (τ * τ) * a * (τ * τ)⁻¹ := by group
          _ = a := by rw [hττ]; group
      refine ⟨{ toFun := fun a => ⟨τ * a * τ⁻¹, hN a a.2⟩
                invFun := fun a => ⟨τ * a * τ⁻¹, hN a a.2⟩
                left_inv := fun a => Subtype.ext (key a)
                right_inv := fun a => Subtype.ext (key a)
                map_mul' := fun a b => Subtype.ext (by
                  show τ * (a * b) * τ⁻¹ = τ * a * τ⁻¹ * (τ * b * τ⁻¹)
                  group) }, ?_, fun a => rfl⟩
      exact MulEquiv.ext fun a => Subtype.ext (key a)
    obtain ⟨σ₁, hσ₁, hσ₁a⟩ := mkσ N₁ h₁
    obtain ⟨σ₂, hσ₂, hσ₂a⟩ := mkσ N₂ h₂
    have hinvσ : ∀ (N : Subgroup Γ) (σ : MulAut ↥N), (∀ a : ↥N, (σ a : Γ) = τ * a * τ⁻¹) →
        ∀ x : ↥N, σ x = x⁻¹ → τ * x * τ⁻¹ = (x : Γ)⁻¹ := by
      intro N σ hσa x hx
      rw [← hσa, hx]
      rfl
    have hfive : ∀ (N : Subgroup Γ) (σ : MulAut ↥N), (∀ a : ↥N, (σ a : Γ) = τ * a * τ⁻¹) →
        ∀ x : ↥N, x ^ 5 = 1 → x ≠ 1 → σ x = x⁻¹ → False := by
      intro N σ hσa x hx5 hx1 hx
      refine five x (by simpa using congrArg Subtype.val hx5) (fun h => hx1 (Subtype.ext h))
        (hinvσ N σ hσa x hx)
    have hconj : ∀ (N : Subgroup Γ) (σ : MulAut ↥N), (∀ a : ↥N, (σ a : Γ) = τ * a * τ⁻¹) →
        ∀ g x : ↥N, σ (g * x * g⁻¹) = (g * x * g⁻¹)⁻¹ →
          τ * ((g : Γ) * x * (g : Γ)⁻¹) * τ⁻¹ = ((g : Γ) * x * (g : Γ)⁻¹)⁻¹ := by
      intro N σ hσa g x hx
      simpa using hinvσ N σ hσa _ hx
    have htriv : ∀ (N : Subgroup Γ) (σ : MulAut ↥N), (∀ a : ↥N, (σ a : Γ) = τ * a * τ⁻¹) →
        σ = 1 → ∀ a ∈ N, τ * a = a * τ := by
      intro N σ hσa h1 a ha
      have e := hσa ⟨a, ha⟩
      rw [h1, MulAut.one_apply] at e
      calc τ * a = (τ * a * τ⁻¹) * τ := by group
        _ = a * τ := by rw [← e]
    rcases alt5_involution_cases φ₁ σ₁ hσ₁ with h1 | ⟨x, hx5, hx1, hx⟩ | ⟨-, hodd⟩
    · rcases alt5_involution_cases φ₂ σ₂ hσ₂ with h2 | ⟨x, hx5, hx1, hx⟩ | ⟨-, hodd⟩
      · exact ht1 (by rw [hcen τ hττ (htriv N₁ σ₁ hσ₁a h1) (htriv N₂ σ₂ hσ₂a h2), map_one])
      · exact hfive N₂ σ₂ hσ₂a x hx5 hx1 hx
      · obtain ⟨g, hg⟩ := hodd ⟨k₂, hk₂⟩ (hsub3 N₂ k₂ hk₂ hk₂3) (hsub1 N₂ k₂ hk₂ hρk₂)
        exact false_of_conj_inv_three hV ρ ⟨ht1, w, hw⟩ (N := N₁) hN₁c hk₂3 hρk₂
          (fun n hn => hc n hn k₂ hk₂) (hconj N₂ σ₂ hσ₂a g _ hg) hk₁ hP
          (fun w' hw' => (hsame w' hw').symm) hfpf₂
    · exact hfive N₁ σ₁ hσ₁a x hx5 hx1 hx
    · obtain ⟨g, hg⟩ := hodd ⟨k₁, hk₁⟩ (hsub3 N₁ k₁ hk₁ hk₁3) (hsub1 N₁ k₁ hk₁ hρk₁)
      exact false_of_conj_inv_three hV ρ ⟨ht1, w, hw⟩ (N := N₂) hN₂c hk₁3 hρk₁
        (fun n hn => (hc k₁ hk₁ n hn).symm) (hconj N₁ σ₁ hσ₁a g _ hg) hk₂ hP hsame hfpf
  ·
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨x₁, hx₁⟩ := exists_prime_orderOf_dvd_card' (G := ↥N₁) 5
      (by rw [Nat.card_congr φ₁.toEquiv, hA5]; norm_num)
    have hx₁5 : (x₁ : Γ) ^ 5 = 1 := by
      rw [← Subgroup.orderOf_coe] at hx₁
      rw [← hx₁]
      exact pow_orderOf_eq_one _
    have hx₁1 : (x₁ : Γ) ≠ 1 := by
      intro h
      rw [← Subgroup.orderOf_coe, h, orderOf_one] at hx₁
      omega
    set x₂ := τ * (x₁ : Γ)⁻¹ * τ⁻¹ with hx₂
    have hx₂N : x₂ ∈ N₂ := hsw _ (inv_mem x₁.2)
    have hcx : Commute (x₁ : Γ) x₂ := hc _ x₁.2 _ hx₂N
    refine five ((x₁ : Γ) * x₂) ?_ ?_ ?_
    · rw [hcx.mul_pow, hx₂, conj_pow, inv_pow, hx₁5, inv_one, mul_one, one_mul,
        mul_inv_cancel]
    · intro h
      apply hx₁1
      have e : (x₁ : Γ) = x₂⁻¹ := eq_inv_of_mul_eq_one_left h
      exact hint _ x₁.2 (e ▸ inv_mem hx₂N)
    · have e1 : τ * (x₁ : Γ) * τ⁻¹ = x₂⁻¹ := by rw [hx₂]; group
      have e2 : τ * x₂ * τ⁻¹ = (x₁ : Γ)⁻¹ := by
        rw [hx₂]
        calc τ * (τ * (x₁ : Γ)⁻¹ * τ⁻¹) * τ⁻¹ = (τ * τ) * (x₁ : Γ)⁻¹ * (τ * τ)⁻¹ := by group
          _ = (x₁ : Γ)⁻¹ := by rw [hττ]; group
      calc τ * ((x₁ : Γ) * x₂) * τ⁻¹ = (τ * (x₁ : Γ) * τ⁻¹) * (τ * x₂ * τ⁻¹) := by group
        _ = x₂⁻¹ * (x₁ : Γ)⁻¹ := by rw [e1, e2]
        _ = ((x₁ : Γ) * x₂)⁻¹ := (mul_inv_rev _ _).symm

end Abstract

section Tilde

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin CFSG.Quasithin.C1Pack CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {T V L V₁ H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g : ↥((L ⊔ T) ⊔ H)}

theorem exists_transvection_of_eq (h : HypF98 T V L V₁ V H) (s : F8Setup T V L H γ γ' g)
    (hD : F8.Uγ V H (g : G) = F8.Dγ V V₁ H (g : G)) :
    ∃ y : ↥H, IsTransvection (rhoH h.toHypF91 y) := by
  classical
  obtain ⟨-, hcard, hcomm⟩ := h.lemma_14_5_18_one s hD
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ h.amalgamHypV.le₂]
  have hUγ : conjClosure V H ≤ conjSub (g : G) H := by
    rw [← hstab]
    exact (h.F913_2 s).1.trans ((pCoreOf_le 2 _).trans inf_le_right)
  obtain ⟨x, hx, u', hu', hxu'⟩ : ∃ x ∈ conjClosure V H, ∃ u' ∈ F8.Uγ V H (g : G),
      x * u' * x⁻¹ * u'⁻¹ ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      exact (Subgroup.mem_bot).mpr (hno a ha b hb)
    have hV₁ : V₁ = ⊥ := hcomm.symm.trans hbot
    rw [hV₁, Subgroup.card_bot] at hcard
    omega
  set y : G := (g : G)⁻¹ * x * g with hy
  have hyH : y ∈ H := mem_conjSub.mp (hUγ hx)
  refine ⟨⟨y, hyH⟩, ?_⟩
  have hcommA : ∀ u ∈ conjClosure V H, y * u * y⁻¹ * u⁻¹ ∈ conjSub (g : G)⁻¹ V₁ := by
    intro u hu
    have hu'' : (g : G) * u * (g : G)⁻¹ ∈ F8.Uγ V H (g : G) := mul_mem_conjSub hu
    have h1 : x * ((g : G) * u * (g : G)⁻¹) * x⁻¹ * ((g : G) * u * (g : G)⁻¹)⁻¹ ∈ V₁ := by
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator hx hu''
    rw [mem_conjSub, inv_inv]
    have e : (g : G) * (y * u * y⁻¹ * u⁻¹) * (g : G)⁻¹ =
        x * ((g : G) * u * (g : G)⁻¹) * x⁻¹ * ((g : G) * u * (g : G)⁻¹)⁻¹ := by
      rw [hy]
      group
    rw [e]
    exact h1
  have hA'card : Nat.card (conjSub (g : G)⁻¹ V₁) = 2 :=
    (Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj _))).trans hcard
  have hA'V₁ : conjSub (g : G)⁻¹ V₁ ⊓ V₁ = ⊥ := by
    have h5 := congrArg (conjSub (g : G)⁻¹) (h.F913_5b s)
    rwa [conjSub_inf, conjSub_bot, F8.A₁, conjSub_conjSub_inv] at h5
  set u₀ : G := (g : G)⁻¹ * u' * g with hu₀
  have hu₀U : u₀ ∈ conjClosure V H := by
    have := hu'
    rw [F8.Uγ, mem_conjSub] at this
    exact this
  set a₀ : G := y * u₀ * y⁻¹ * u₀⁻¹ with ha₀
  have ha₀1 : a₀ ≠ 1 := by
    intro e
    apply hxu'
    have : (g : G) * a₀ * (g : G)⁻¹ = x * u' * x⁻¹ * u'⁻¹ := by
      rw [ha₀, hy, hu₀]
      group
    rw [← this, e]
    group
  have ha₀A : a₀ ∈ conjSub (g : G)⁻¹ V₁ := hcommA u₀ hu₀U
  have ha₀U : a₀ ∈ conjClosure V H :=
    (conjClosure V H).mul_mem (conj_mem_UH hyH hu₀U) ((conjClosure V H).inv_mem hu₀U)
  have ha₀V₁ : a₀ ∉ V₁ := fun hv => ha₀1 (by
    have : a₀ ∈ conjSub (g : G)⁻¹ V₁ ⊓ V₁ := ⟨ha₀A, hv⟩
    rw [hA'V₁] at this
    exact Subgroup.mem_bot.mp this)
  have hdich : ∀ u ∈ conjClosure V H, y * u * y⁻¹ * u⁻¹ = 1 ∨ y * u * y⁻¹ * u⁻¹ = a₀ := by
    obtain ⟨c, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(conjSub (g : G)⁻¹ V₁))).mp hA'card
    have ha₀c : (⟨a₀, ha₀A⟩ : ↥(conjSub (g : G)⁻¹ V₁)) = c :=
      huniq _ (fun e => ha₀1 (by simpa using congrArg Subtype.val e))
    intro u hu
    by_cases h1 : y * u * y⁻¹ * u⁻¹ = 1
    · exact Or.inl h1
    · right
      have h2 : (⟨_, hcommA u hu⟩ : ↥(conjSub (g : G)⁻¹ V₁)) = c :=
        huniq _ (fun e => h1 (by simpa using congrArg Subtype.val e))
      exact congrArg Subtype.val (h2.trans ha₀c.symm)
  refine ⟨fun h1 => ?_, clsU h.toHypF91 ha₀U, ?_, fun w => ?_⟩
  ·
    have := congrArg (fun f : MulAut (UMod h.toHypF91) => f (clsU h.toHypF91 hu₀U)) h1
    simp only [MulAut.one_apply] at this
    rw [rhoH_clsU_eq_iff] at this
    exact ha₀V₁ this
  · intro e
    rw [clsU_eq_one_iff] at e
    exact ha₀V₁ e
  · obtain ⟨u, hu, rfl⟩ := exists_clsU h.toHypF91 w
    rw [rhoH_clsU]
    rcases hdich u hu with h1 | h1
    · left
      rw [clsU_eq_iff]
      show (y * u * y⁻¹)⁻¹ * u ∈ V₁
      have e : y * u * y⁻¹ = u := by
        calc y * u * y⁻¹ = (y * u * y⁻¹ * u⁻¹) * u := by group
          _ = u := by rw [h1, one_mul]
      rw [e, inv_mul_cancel]
      exact V₁.one_mem
    · right
      rw [mul_comm (clsU h.toHypF91 hu), clsU_mul]
      apply clsU_congr
      show y * u * y⁻¹ = a₀ * u
      rw [← h1]
      group

end Tilde

end CFSG.Quasithin.H13.L32A.L2
