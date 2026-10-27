module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModA

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod Equiv
open CFSG.LieType.BorelTits
open scoped commutatorElement

theorem exists_fixed_ne_one {P K : Type} [Group P] [Group K] [Finite K] (hP : IsPGroup 2 P)
    (hK : IsPGroup 2 K) [Nontrivial K] (ρ : P →* MulAut K) :
    ∃ k : K, k ≠ 1 ∧ ∀ p : P, ρ p k = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction P K := MulAction.compHom K ρ
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hK
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : Nat.card K = 1 := by simpa using hn
    exact (Finite.one_lt_card (α := K)).ne' h1
  have hdvd : 2 ∣ Nat.card K := hn ▸ dvd_pow_self 2 hn0
  have h1 : (1 : K) ∈ MulAction.fixedPoints P K := fun p => map_one (ρ p)
  obtain ⟨b, hb, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point K hdvd h1
  exact ⟨b, hne.symm, fun p => hb p⟩

section Abstract

variable {X : Type} [Group X] {A : Type} [CommGroup A]

theorem eq_one_of_fixed_of_cover [Finite A] {ρ : X →* MulAut A} (hA : IsPGroup 2 A)
    {L : Subgroup X} (hLn : ∀ x : X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    {P : Type} [Group P] (hP : IsPGroup 2 P) (σ : P →* X)
    (hcov : ∀ x : X, ∃ l ∈ L, ∃ p : P, x = l * σ p)
    (hX : ∀ a : A, (∀ x : X, ρ x a = a) → a = 1) :
    ∀ a : A, (∀ l ∈ L, ρ l a = a) → a = 1 := by
  intro a ha
  by_contra hne
  let K : Subgroup A :=
    { carrier := {a | ∀ l ∈ L, ρ l a = a}
      one_mem' := fun l _ => map_one _
      mul_mem' := fun {x y} hx hy l hl => by rw [map_mul, hx l hl, hy l hl]
      inv_mem' := fun {x} hx l hl => by rw [map_inv, hx l hl] }
  have hinv : ∀ x : X, ∀ k ∈ K, ρ x k ∈ K := by
    intro x k hk l hl
    have h1 : x⁻¹ * l * x ∈ L := by
      have := hLn x⁻¹ l hl
      simpa using this
    have h2 : ρ l (ρ x k) = ρ x (ρ (x⁻¹ * l * x) k) := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [h2, hk _ h1]
  have : Nontrivial K := ⟨⟨⟨a, ha⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
  have hKp : IsPGroup 2 K := hA.of_injective K.subtype K.subtype_injective
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : P →* MulAut K, ∀ p (k : K), ((ρ' p k : K) : A) = ρ (σ p) k := by
    refine ⟨
      { toFun := fun p =>
          { toFun := fun k => ⟨ρ (σ p) k, hinv _ _ k.2⟩
            invFun := fun k => ⟨ρ (σ p)⁻¹ k, by simpa using hinv (σ p)⁻¹ _ k.2⟩
            left_inv := fun k => by
              apply Subtype.ext
              show ρ (σ p)⁻¹ (ρ (σ p) k) = k
              rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
              rfl
            right_inv := fun k => by
              apply Subtype.ext
              show ρ (σ p) (ρ (σ p)⁻¹ k) = k
              rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
              rfl
            map_mul' := fun x y => by
              apply Subtype.ext
              exact map_mul (ρ (σ p)) (x : A) (y : A) }
        map_one' := by
          ext k
          show ρ (σ 1) k = k
          rw [map_one, map_one]
          rfl
        map_mul' := fun p q => by
          ext k
          show ρ (σ (p * q)) k = ρ (σ p) (ρ (σ q) k)
          rw [map_mul, map_mul]
          rfl }, fun p k => rfl⟩
  obtain ⟨k, hk1, hkfix⟩ := exists_fixed_ne_one hP hKp ρ'
  refine hk1 (Subtype.ext ?_)
  have hkP : ∀ p : P, ρ (σ p) (k : A) = k := fun p => by
    rw [← hρ' p k]
    exact congrArg Subtype.val (hkfix p)
  have := hX k fun x => by
    obtain ⟨l, hl, p, rfl⟩ := hcov x
    rw [map_mul, MulAut.mul_apply, hkP p, k.2 l hl]
  exact this

theorem eq_of_card_le_two [Finite A] {I : Subgroup A} (hI : Nat.card I ≤ 2) {i x : A} (hi : i ∈ I)
    (hi1 : i ≠ 1) (hx : x ∈ I) (hx1 : x ≠ 1) : x = i := by
  by_contra hxi
  have h3 : ({1, i, x} : Set A).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, i, x, hi1.symm, hx1.symm, fun h => hxi h.symm, rfl⟩
  have hsub : ({1, i, x} : Set A) ⊆ (I : Set A) := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact I.one_mem
    · exact hi
    · exact hx
  have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Nat.card_coe_set_eq] at h4
  have h5 : Nat.card (I : Set A) ≤ 2 := hI
  omega

private theorem mul_comm_aux (f x b : A) : f * x * (f * b)⁻¹ = x * b⁻¹ := by
  rw [mul_inv_rev, mul_comm f x, mul_assoc, mul_left_comm f, mul_inv_cancel, mul_one]

theorem fixed_on_of_hom [Finite X] [Finite A] {ρ : X →* MulAut A} {F B : Subgroup A}
    {L P R : Subgroup X} (hLF : ∀ l ∈ L, ∀ a : A, ρ l a * a⁻¹ ∈ F) (hPL : P ≤ L)
    (hPn : ∀ l ∈ L, ∀ t ∈ P, l * t * l⁻¹ ∈ P) (hPF : ∀ t ∈ P, ∀ f ∈ F, ρ t f = f)
    (hR : ∀ r ∈ R, ∀ b ∈ B, ρ r b = b) (hidx : R.relIndex P ≤ 2)
    (hF1 : ∀ f ∈ F, (∀ l ∈ L, ρ l f = f) → f = 1) :
    ∀ t ∈ P, ∀ b ∈ B, ρ t b = b := by
  intro t ht b hb
  have hg : ∀ s s' : X, s ∈ P → s' ∈ P →
      ρ (s * s') b * b⁻¹ = (ρ s' b * b⁻¹) * (ρ s b * b⁻¹) := by
    intro s s' hs hs'
    have h1 : ρ s (ρ s' b) = (ρ s' b * b⁻¹) * ρ s b := by
      have e : ρ s' b = (ρ s' b * b⁻¹) * b := by group
      conv_lhs => rw [e]
      rw [map_mul, hPF s hs _ (hLF s' (hPL hs') b)]
    rw [map_mul, MulAut.mul_apply, h1]
    group
  let g : ↥P →* A :=
    { toFun := fun s => ρ (s : X) b * b⁻¹
      map_one' := by simp
      map_mul' := fun s s' => by
        rw [Subgroup.coe_mul, hg s s' s.2 s'.2, mul_comm] }
  have hker : R.subgroupOf P ≤ g.ker := fun s hs => by
    rw [MonoidHom.mem_ker]
    show ρ (s : X) b * b⁻¹ = 1
    rw [hR s (Subgroup.mem_subgroupOf.mp hs) b hb]
    simp
  have hcard : Nat.card g.range ≤ 2 := by
    rw [← Subgroup.index_ker]
    have hpos : 0 < (R.subgroupOf P).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd hpos (Subgroup.index_dvd_of_le hker)).trans hidx
  by_contra hne
  have hi1 : ρ t b * b⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  have hiI : ρ t b * b⁻¹ ∈ g.range := ⟨⟨t, ht⟩, rfl⟩
  have hfix : ∀ l ∈ L, ρ l (ρ t b * b⁻¹) = ρ t b * b⁻¹ := by
    intro l hl
    have ht' : l * t * l⁻¹ ∈ P := hPn l hl t ht
    have hconj : ρ l (ρ t b * b⁻¹) = ρ (l * t * l⁻¹) b * b⁻¹ := by
      have e1 : ρ l (ρ t b) = ρ (l * t * l⁻¹) (ρ l b) := by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group
      have e2 : ρ l b = (ρ l b * b⁻¹) * b := by group
      rw [map_mul, map_inv, e1]
      conv_lhs => rw [e2]
      rw [map_mul, hPF _ ht' _ (hLF l hl b), mul_comm_aux]
    have hmem : ρ (l * t * l⁻¹) b * b⁻¹ ∈ g.range := ⟨⟨_, ht'⟩, rfl⟩
    rw [hconj]
    have hx1 : ρ (l * t * l⁻¹) b * b⁻¹ ≠ 1 := by
      intro h
      apply hi1
      apply (ρ l).injective
      rw [← hconj] at h
      rw [h, map_one]
    exact eq_of_card_le_two hcard hiI hi1 hmem hx1
  exact hi1 (hF1 _ (hLF t (hPL ht) b) hfix)

theorem fixed_on_of_comm {ρ : X →* MulAut A} {F B : Subgroup A} {L Q : Subgroup X}
    (hLn : ∀ x : X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) (hQn : ∀ x : X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hLF : ∀ l ∈ L, ∀ a : A, ρ l a * a⁻¹ ∈ F) (hQF : ∀ q ∈ Q, ∀ f ∈ F, ρ q f = f)
    (hLB : ∀ t ∈ L ⊓ Q, ∀ b ∈ B, ρ t b = b) (hAB : ∀ a : A, ∃ b ∈ B, ∃ f ∈ F, a = b * f)
    (hC : ∀ a : A, (∀ l ∈ L, ρ l a = a) → a = 1) : ∀ q ∈ Q, ∀ a : A, ρ q a = a := by
  have hP : ∀ t ∈ L ⊓ Q, ∀ a : A, ρ t a = a := by
    intro t ht a
    obtain ⟨b, hb, f, hf, rfl⟩ := hAB a
    rw [map_mul, hLB t ht b hb, hQF t ht.2 f hf]
  have hcomm : ∀ q ∈ Q, ∀ l ∈ L, ∀ a : A, ρ q (ρ l a) = ρ l (ρ q a) := by
    intro q hq l hl a
    have hc : q * l * q⁻¹ * l⁻¹ ∈ L ⊓ Q := by
      refine ⟨L.mul_mem (hLn q l hl) (L.inv_mem hl), ?_⟩
      have e : q * l * q⁻¹ * l⁻¹ = q * (l * q⁻¹ * l⁻¹) := by group
      rw [e]
      exact Q.mul_mem hq (hQn l q⁻¹ (Q.inv_mem hq))
    have e : q * l = (q * l * q⁻¹ * l⁻¹) * (l * q) := by group
    rw [← MulAut.mul_apply, ← map_mul, e, map_mul, MulAut.mul_apply, hP _ hc, map_mul,
      MulAut.mul_apply]
  intro q hq a
  have hga : ∀ l ∈ L, ρ l (ρ q a * a⁻¹) = ρ q a * a⁻¹ := by
    intro l hl
    obtain ⟨f₀, hf₀⟩ : ∃ f₀, f₀ = ρ l a * a⁻¹ := ⟨_, rfl⟩
    have hρl : ρ l a = f₀ * a := by rw [hf₀]; group
    have hf : f₀ ∈ F := hf₀ ▸ hLF l hl a
    rw [map_mul, map_inv, ← hcomm q hq l hl a, hρl, map_mul, hQF q hq f₀ hf, mul_comm_aux]
  exact mul_inv_eq_one.mp (hC _ hga)

@[expose] def cenF (s : Perm (Fin 5)) : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun g => g * s = s * g

private theorem card_cenF_swap : ∀ i j : Fin 5, i ≠ j → (cenF (swap i j)).card = 12 := by
  decide +kernel

private theorem swap_of_cenF : ∀ τ : Perm (Fin 5), τ * τ = 1 → τ ≠ 1 → 12 ≤ (cenF τ).card →
    ∃ i j : Fin 5, i ≠ j ∧ τ = swap i j := by
  decide +kernel

private theorem swap_of_mem_S5SylF : ∀ σ ∈ S5SylF, (∃ i j : Fin 5, i ≠ j ∧ σ = swap i j) →
    σ = swap 0 2 ∨ σ = swap 1 3 := by
  decide +kernel

theorem isSwap_map_of_injective {ι : Perm (Fin 5) →* Perm (Fin 5)} (hι : Function.Injective ι)
    {s : Perm (Fin 5)} (hs : s.IsSwap) : (ι s).IsSwap := by
  obtain ⟨i, j, hij, rfl⟩ := hs
  have h1 : ι (swap i j) * ι (swap i j) = 1 := by
    rw [← map_mul, swap_mul_self, map_one]
  have h2 : ι (swap i j) ≠ 1 := by
    intro h
    have h3 := congrArg (fun f => f i) (hι (h.trans (map_one ι).symm))
    simp only [swap_apply_left, Perm.coe_one, id_eq] at h3
    exact hij h3.symm
  have h3 : 12 ≤ (cenF (ι (swap i j))).card := by
    rw [← card_cenF_swap i j hij]
    refine Finset.card_le_card_of_injOn ι (fun g hg => ?_) (hι.injOn)
    have hg' : g * swap i j = swap i j * g := by simpa [cenF] using hg
    simp only [cenF, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← map_mul, ← map_mul, hg']
  obtain ⟨a, b, hab, e⟩ := swap_of_cenF _ h1 h2 h3
  exact ⟨a, b, hab, e⟩

theorem exists_map_S5That {ι : Perm (Fin 5) →* Perm (Fin 5)} (hι : Function.Injective ι)
    (hD : ∀ σ ∈ S5Syl, ι σ ∈ S5Syl) : S5That ≤ S5That.map ι := by
  have h02 : (swap 0 2 : Perm (Fin 5)) ∈ S5That := Subgroup.subset_closure (by simp)
  have h13 : (swap 1 3 : Perm (Fin 5)) ∈ S5That := Subgroup.subset_closure (by simp)
  have hsyl : S5That ≤ S5Syl := S5That_le_S5Syl
  have ha := swap_of_mem_S5SylF _ ((mem_S5Syl_iff _).mp (hD _ (hsyl h02)))
    (isSwap_map_of_injective hι (⟨0, 2, by decide, rfl⟩ : (swap (0 : Fin 5) 2).IsSwap))
  have hb := swap_of_mem_S5SylF _ ((mem_S5Syl_iff _).mp (hD _ (hsyl h13)))
    (isSwap_map_of_injective hι (⟨1, 3, by decide, rfl⟩ : (swap (1 : Fin 5) 3).IsSwap))
  have hne : ι (swap 0 2) ≠ ι (swap 1 3) := fun h => by
    have h2 := hι h
    exact absurd h2 (by decide)
  have hcl : ({swap 0 2, swap 1 3} : Set (Perm (Fin 5))) ⊆ S5That.map ι := by
    rintro τ (rfl | rfl)
    · rcases ha with ha | ha
      · exact ⟨_, h02, ha⟩
      · rcases hb with hb | hb
        · exact ⟨_, h13, hb⟩
        · exact absurd (ha.trans hb.symm) hne
    · rcases hb with hb | hb
      · rcases ha with ha | ha
        · exact absurd (ha.trans hb.symm) hne
        · exact ⟨_, h02, ha⟩
      · exact ⟨_, h13, hb⟩
  exact (Subgroup.closure_le _).mpr hcl

end Abstract

private theorem orth_fix3 : ∀ w : orth.W, orth.act (swap 0 1 * swap 1 2) w = w →
    orth.act (swap 0 1 * swap 1 3) w = w → orth.act (swap 0 1 * swap 1 4) w = w → w = 1 := by
  decide +kernel

private theorem nat_fix3 : ∀ w : nat.W, nat.act (swap 0 1 * swap 1 2) w = w →
    nat.act (swap 0 1 * swap 1 3) w = w → nat.act (swap 0 1 * swap 1 4) w = w → w = 1 := by
  decide +kernel

private theorem sign_three : Perm.sign (swap (0 : Fin 5) 1 * swap 1 2) = 1 ∧
    Perm.sign (swap (0 : Fin 5) 1 * swap 1 3) = 1 ∧
    Perm.sign (swap (0 : Fin 5) 1 * swap 1 4) = 1 := by decide +kernel

theorem orth_fix_alt : ∀ w : orth.W, (∀ σ ∈ alternatingGroup (Fin 5), orth.act σ w = w) →
    w = 1 := fun w h =>
  orth_fix3 w (h _ (Perm.mem_alternatingGroup.mpr sign_three.1))
    (h _ (Perm.mem_alternatingGroup.mpr sign_three.2.1))
    (h _ (Perm.mem_alternatingGroup.mpr sign_three.2.2))

theorem nat_fix_alt : ∀ w : nat.W, (∀ σ ∈ alternatingGroup (Fin 5), nat.act σ w = w) →
    w = 1 := fun w h =>
  nat_fix3 w (h _ (Perm.mem_alternatingGroup.mpr sign_three.1))
    (h _ (Perm.mem_alternatingGroup.mpr sign_three.2.1))
    (h _ (Perm.mem_alternatingGroup.mpr sign_three.2.2))

theorem card_fixW_orth_S5That : Nat.card (fixW orth S5That) = 4 := by
  have h := profile_orth.2.2.1
  simp only [profile, Prod.mk.injEq] at h
  exact h.2.1

namespace Dict5

variable {G : Type} [Group G] [Finite G] {X S Z : Subgroup G} (D : Dict5 X S Z)

include D in
theorem oTwoRes_le_of_swap {C : Subgroup G} (hCn : X ≤ Subgroup.normalizer (C : Set G)) {k : G}
    (hk : k ∈ C) (hkX : k ∈ X) (hψ : D.ψ ⟨k, hkX⟩ = swap 0 2) : oTwoRes X ≤ C := by
  have hQp : IsPGroup 2 (pCoreOf 2 X) := pCoreOf_isPGroup (r := 2) X
  have hQX : pCoreOf 2 X ≤ X := pCoreOf_le 2 X
  have hτ : (swap 0 2 : Perm (Fin 5)) ∈ D.bar C := (D.mem_bar_iff _).mpr ⟨⟨k, hkX⟩, hk, hψ⟩
  have hconj : ∀ i j : Fin 5, i ≠ j → ∃ g : Perm (Fin 5), g * swap 0 2 * g⁻¹ = swap i j := by
    decide +kernel
  have hswap : ∀ s : Perm (Fin 5), s.IsSwap → s ∈ D.bar C := by
    rintro s ⟨i, j, hij, rfl⟩
    obtain ⟨g, hg⟩ := hconj i j hij
    obtain ⟨y, rfl⟩ := D.surj g
    obtain ⟨c, hc, hcτ⟩ := (D.mem_bar_iff _).mp hτ
    refine (D.mem_bar_iff _).mpr ⟨y * c * y⁻¹, ?_, ?_⟩
    · have := conj_mem_of_normalizes hCn y.2 hc
      simpa using this
    · rw [map_mul, map_mul, map_inv, hcτ, hg]
  have hbarTop : D.bar C = ⊤ := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    exact fun s hs => hswap s hs
  have hcov : ∀ x ∈ X, ∃ c ∈ C, ∃ q ∈ pCoreOf 2 X, x = c * q := by
    intro x hx
    have hx' : D.ψ ⟨x, hx⟩ ∈ D.bar C := by rw [hbarTop]; trivial
    obtain ⟨c, hc, hcψ⟩ := (D.mem_bar_iff _).mp hx'
    refine ⟨c, hc, (c : G)⁻¹ * x, ?_, by group⟩
    have : ((c⁻¹ * ⟨x, hx⟩ : ↥X) : G) ∈ pCoreOf 2 X :=
      (D.ker_iff _).mp (by rw [map_mul, map_inv, hcψ, inv_mul_cancel])
    simpa using this
  exact oTwoRes_le_of_cover hCn hQp hQX hcov

end Dict5

end CFSG.Quasithin.F53.Stellmacher.S43
