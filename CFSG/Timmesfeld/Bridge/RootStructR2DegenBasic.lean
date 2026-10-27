module

public import CFSG.Timmesfeld.Bridge.OddLocalRootCore

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped commutatorElement

namespace RootDegen

theorem exists_fixed_of_prime {α : Type*} {S : Set α} [Finite S] {f : α → α}
    (hf : ∀ s ∈ S, f s ∈ S) {p : ℕ} [hp : Fact p.Prime] (hfp : ∀ s ∈ S, f^[p] s = s)
    (hS : ¬ p ∣ Nat.card S) : ∃ s ∈ S, f s = s := by
  classical
  have hiter : ∀ n, ∀ s ∈ S, f^[n] s ∈ S := by
    intro n
    induction n with
    | zero => exact fun s hs => hs
    | succ n ih =>
      intro s hs
      rw [Function.iterate_succ_apply']
      exact hf _ (ih s hs)
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  let σ : Equiv.Perm S :=
    { toFun := fun s => ⟨f s, hf s s.2⟩
      invFun := fun s => ⟨f^[p - 1] s, hiter _ s s.2⟩
      left_inv := fun s => by
        apply Subtype.ext
        change f^[p - 1] (f s) = s
        rw [← Function.iterate_succ_apply f (p - 1) s, Nat.succ_eq_add_one, Nat.sub_add_cancel hp1]
        exact hfp s s.2
      right_inv := fun s => by
        apply Subtype.ext
        change f (f^[p - 1] s) = s
        rw [← Function.iterate_succ_apply' f (p - 1) s, Nat.succ_eq_add_one,
          Nat.sub_add_cancel hp1]
        exact hfp s s.2 }
  have hσpow : ∀ n (s : S), (((σ ^ n) s : S) : α) = f^[n] s := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [pow_succ', Equiv.Perm.mul_apply, Function.iterate_succ_apply', ← ih]
      rfl
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    ext s
    rw [hσpow]
    exact hfp s s.2
  have : Fintype S := Fintype.ofFinite S
  obtain ⟨s, hs⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := p) (n := 1)
    (by rwa [← Nat.card_eq_fintype_card]) hσ
  exact ⟨s, s.2, congrArg Subtype.val hs⟩

theorem commutator_mem_of_sup_eq_normalizer {H : Type*} [Group H] {Q D₀ : Subgroup H}
    (hD₀ : ∀ a ∈ D₀, ∀ b ∈ D₀, Commute a b)
    (hsup : Q ⊔ D₀ = Subgroup.normalizer (Q : Set H)) {n₁ n₂ : H}
    (h₁ : n₁ ∈ Subgroup.normalizer (Q : Set H)) (h₂ : n₂ ∈ Subgroup.normalizer (Q : Set H)) :
    n₁ * n₂ * n₁⁻¹ * n₂⁻¹ ∈ Q := by
  set N := Subgroup.normalizer (Q : Set H) with hN
  have hQN : Q ≤ N := hsup ▸ le_sup_left
  have hDN : D₀ ≤ N := hsup ▸ le_sup_right
  have himg : (D₀.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) = ⊤ := by
    have htop : Q.subgroupOf N ⊔ D₀.subgroupOf N = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hQN hDN, hsup, Subgroup.subgroupOf_self]
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' (Q.subgroupOf N))) htop
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
    have h2 : (Q.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨q, hq, rfl⟩
      exact (QuotientGroup.eq_one_iff q).2 hq
    rw [h2, bot_sup_eq] at h1
    exact h1
  have hcomm : ∀ u v : N ⧸ Q.subgroupOf N, Commute u v := by
    intro u v
    have hu : u ∈ (D₀.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) :=
      himg ▸ Subgroup.mem_top u
    have hv : v ∈ (D₀.subgroupOf N).map (QuotientGroup.mk' (Q.subgroupOf N)) :=
      himg ▸ Subgroup.mem_top v
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    have hab : Commute a b := Subtype.ext (hD₀ _ ha _ hb).eq
    exact hab.map _
  have hmem : (⟨n₁, h₁⟩ : N) * ⟨n₂, h₂⟩ * (⟨n₁, h₁⟩ : N)⁻¹ * (⟨n₂, h₂⟩ : N)⁻¹ ∈
      Q.subgroupOf N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_mul, map_mul,
      map_inv, map_inv, (hcomm (QuotientGroup.mk' (Q.subgroupOf N) ⟨n₁, h₁⟩)
        (QuotientGroup.mk' (Q.subgroupOf N) ⟨n₂, h₂⟩)).eq]
    group
  exact hmem

theorem conj_eq_of_isBender {K : Type} [Group K] [Finite K]
    (hB : CFSG.BenderSuzuki.IsBenderGroup (K ⧸ zStar K)) {E S : Set K}
    (hEn : ∀ g e : K, e ∈ E → g * e * g⁻¹ ∈ E)
    (hinj : ∀ e ∈ E, ∀ f ∈ E,
      QuotientGroup.mk' (zStar K) e = QuotientGroup.mk' (zStar K) f → e = f)
    (hSE : S ⊆ E) (hS2 : ∀ s ∈ S, s * s = 1) (hSc : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {s₀ : K} (hs₀ : s₀ ∈ S) (hs₀Z : s₀ ∉ zStar K) {g₁ g₂ : K}
    (hg₁ : ∀ s ∈ S, g₁ * s * g₁⁻¹ ∈ S) (hg₂ : ∀ s ∈ S, g₂ * s * g₂⁻¹ ∈ S) {s : K}
    (hs : s ∈ S) :
    (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * s * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)⁻¹ = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (zStar K) with hπ
  set P : Subgroup (K ⧸ zStar K) := Subgroup.closure (π '' S) with hP
  have hPc : ∀ u ∈ π '' S, ∀ v ∈ π '' S, Commute u v := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact (hSc u hu v hv).map π
  have hP2 : IsPGroup 2 P := OddLocal.isPGroup_two_of_mul_self fun g hg =>
    OddLocal.mul_self_eq_one_of_mem_closure hPc
      (by rintro _ ⟨u, hu, rfl⟩; rw [← map_mul, hS2 u hu, map_one]) hg
  obtain ⟨Q, hPQ⟩ := hP2.exists_le_sylow
  obtain ⟨q, k, hBB, -⟩ := Asc72.IsBenderGroup.exists_fusionBenderBorel hB
  obtain ⟨hemb, ⟨D₀, hD₀c, -, -, hsup⟩, -⟩ := hBB Q
  set N := Subgroup.normalizer ((Q : Subgroup (K ⧸ zStar K)) : Set (K ⧸ zStar K)) with hN
  have heven : 2 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    rcases n with _ | n
    · exfalso
      rw [pow_zero] at hn
      have hbot := Subgroup.eq_bot_of_card_eq P hn
      have hmem : π s₀ ∈ P := Subgroup.subset_closure ⟨s₀, hs₀, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hs₀Z ((QuotientGroup.eq_one_iff s₀).1 hmem)
    · rw [hn, pow_succ]
      exact dvd_mul_left 2 _
  have hnorm : ∀ {g : K}, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → π g ∈ N := by
    intro g hg
    have hconjP : ∀ y ∈ P, π g * y * (π g)⁻¹ ∈ P := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨u, hu, rfl⟩ := hz
        exact Subgroup.subset_closure ⟨g * u * g⁻¹, hg u hu, by simp [map_mul, map_inv]⟩
      | one => simp
      | mul a b _ _ ha hb =>
        have := P.mul_mem ha hb
        rwa [show π g * a * (π g)⁻¹ * (π g * b * (π g)⁻¹) = π g * (a * b) * (π g)⁻¹ by group]
          at this
      | inv a _ ha =>
        have := P.inv_mem ha
        rwa [show (π g * a * (π g)⁻¹)⁻¹ = π g * a⁻¹ * (π g)⁻¹ by group] at this
    by_contra hgN
    have hodd := hemb.2.2 (π g) hgN
    have hle : P ≤ N ⊓ N.map (MulAut.conj (π g)⁻¹).toMonoidHom := by
      intro y hy
      refine ⟨Subgroup.le_normalizer (hPQ hy), π g * y * (π g)⁻¹,
        Subgroup.le_normalizer (hPQ (hconjP y hy)), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hdvd := Subgroup.card_dvd_of_le hle
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (heven.trans hdvd))
  have hD₀comm : ∀ a ∈ D₀, ∀ b ∈ D₀, Commute a b := by
    intro a ha b hb
    obtain ⟨γ, hγ⟩ := hD₀c.exists_generator
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hγ ⟨a, ha⟩)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hγ ⟨b, hb⟩)
    have h1 : Commute (⟨a, ha⟩ : D₀) ⟨b, hb⟩ := by
      rw [← hm, ← hn]
      exact (Commute.refl γ).zpow_zpow m n
    exact h1.map D₀.subtype
  have hcQ : π (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) ∈ (Q : Subgroup (K ⧸ zStar K)) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutator_mem_of_sup_eq_normalizer hD₀comm hsup (hnorm hg₁) (hnorm hg₂)
  set c := g₁ * g₂ * g₁⁻¹ * g₂⁻¹ with hc
  have hsQ : π s ∈ (Q : Subgroup (K ⧸ zStar K)) := hPQ (Subgroup.subset_closure ⟨s, hs, rfl⟩)
  have hcs : Commute (π s) (π c) :=
    Asc72.IsBenderGroup.commute_of_mul_self_eq_one hB Q hsQ
      (by rw [← map_mul, hS2 s hs, map_one]) _ hcQ
  refine hinj _ (hEn c s (hSE hs)) _ (hSE hs) ?_
  rw [map_mul, map_mul, map_inv, ← hcs.eq, mul_inv_cancel_right]

section SL2

open CFSG.Glauberman.Dickson

variable {F : Type*} [Field F]

theorem splitTorus_conj_mem_lowerUnipotent (a : Fˣ)
    {u : Matrix.SpecialLinearGroup (Fin 2) F} (hu : u ∈ lowerUnipotent F) :
    splitTorusSLHom F a * u * (splitTorusSLHom F a)⁻¹ ∈ lowerUnipotent F := by
  induction hu using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨t, ht⟩ := hg
    apply Subgroup.subset_closure
    refine ⟨(a⁻¹ : F) * t * (a⁻¹ : F), ?_⟩
    rw [← map_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      splitTorusSLHom_coe, splitTorusSLHom_coe, ht]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  | one => simp
  | mul a' b _ _ ha hb =>
    have := Subgroup.mul_mem _ ha hb
    rwa [show splitTorusSLHom F a * a' * (splitTorusSLHom F a)⁻¹ *
        (splitTorusSLHom F a * b * (splitTorusSLHom F a)⁻¹) =
        splitTorusSLHom F a * (a' * b) * (splitTorusSLHom F a)⁻¹ by group] at this
  | inv a' _ ha =>
    have := Subgroup.inv_mem _ ha
    rwa [show (splitTorusSLHom F a * a' * (splitTorusSLHom F a)⁻¹)⁻¹ =
        splitTorusSLHom F a * a'⁻¹ * (splitTorusSLHom F a)⁻¹ by group] at this

theorem splitTorusSLHom_injective : Function.Injective (splitTorusSLHom F) := by
  intro a b hab
  have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 0) hab
  simp only [splitTorusSLHom_coe] at h
  exact Units.ext (by simpa using h)

variable [CharP F 2]

theorem standardSplitWeylSL_eq_conj :
    ∃ g ∈ lowerUnipotent F, ∃ u ∈ upperUnipotent F, u ≠ 1 ∧
      standardSplitWeylSL F = g * u * g⁻¹ := by
  let g : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  let u : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨g, Subgroup.subset_closure ⟨1, rfl⟩, u, Subgroup.subset_closure ⟨1, rfl⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun k : Matrix.SpecialLinearGroup (Fin 2) F =>
      (k : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [u] at h1
  · have hgu : g * u = standardSplitWeylSL F * g := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        standardSplitWeylSL_coe]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [g, u, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, one_add_one_eq_two,
          CharTwo.two_eq_zero]
    rw [hgu, mul_inv_cancel_right]

theorem exists_torus_weyl [Finite F] (hF : 4 ≤ Nat.card F) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ h : Matrix.SpecialLinearGroup (Fin 2) F, orderOf h = p ∧
      (∀ u ∈ lowerUnipotent F, h * u * h⁻¹ ∈ lowerUnipotent F) ∧
      (∀ u ∈ lowerUnipotent F, h⁻¹ * u * h ∈ lowerUnipotent F) ∧
      ∃ g ∈ lowerUnipotent F, ∃ u ∈ upperUnipotent F, u ≠ 1 ∧
        (g * u * g⁻¹) * h * (g * u * g⁻¹)⁻¹ = h⁻¹ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcardU : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  have hk' : Nat.card F = 2 ^ (k : ℕ) := by rw [Nat.card_eq_fintype_card, hk]
  have hodd : Odd (Nat.card F - 1) := by
    rw [hk']
    have hpos : 0 < (k : ℕ) := k.pos
    have : Even (2 ^ (k : ℕ)) := Nat.even_pow.2 ⟨even_two, by omega⟩
    obtain ⟨j, hj⟩ := this
    have h1 : 1 ≤ 2 ^ (k : ℕ) := Nat.one_le_two_pow
    exact ⟨j - 1, by omega⟩
  set p := (Nat.card F - 1).minFac with hp
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ Nat.card F - 1 := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpdvd)
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rw [hcardU]; exact hpdvd)
  refine ⟨p, hpp, hp2, splitTorusSLHom F a, ?_, fun u hu => ?_, fun u hu => ?_, ?_⟩
  · rw [orderOf_injective _ splitTorusSLHom_injective a, ha]
  · exact splitTorus_conj_mem_lowerUnipotent a hu
  · have := splitTorus_conj_mem_lowerUnipotent a⁻¹ hu
    rwa [map_inv, inv_inv] at this
  · obtain ⟨g, hg, u, hu, hu1, hw⟩ := standardSplitWeylSL_eq_conj (F := F)
    refine ⟨g, hg, u, hu, hu1, ?_⟩
    rw [← hw, standardSplitWeylSL_conj, map_inv]

end SL2

end RootDegen

end CFSG.Timmesfeld.Bridge
