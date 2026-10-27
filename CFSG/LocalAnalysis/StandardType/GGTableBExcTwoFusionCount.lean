module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover

namespace TableBExcTwoFusion

open TableBExc

section TorusSet

variable {τ : Tag} {K : Type} [Field K]
  {p : ℕ} [NeZero p] {ζ : Kˣ}

variable (hζ : ζ ^ p = 1) in
@[expose] noncomputable def torusSet (E : Subgroup (adjointGroup τ K)) :
    AddSubgroup (Fin τ.rank → ZMod p) where
  carrier := {x | chevTorus τ ζ hζ (.ofAdd x) ∈ E}
  add_mem' {x y} hx hy := by
    show chevTorus τ ζ hζ (.ofAdd (x + y)) ∈ E
    rw [ofAdd_add, map_mul]
    exact mul_mem hx hy
  zero_mem' := by
    show chevTorus τ ζ hζ (.ofAdd 0) ∈ E
    rw [ofAdd_zero, map_one]
    exact one_mem E
  neg_mem' {x} hx := by
    show chevTorus τ ζ hζ (.ofAdd (-x)) ∈ E
    rw [ofAdd_neg, map_inv]
    exact inv_mem hx

theorem mem_torusSet {hζ : ζ ^ p = 1} {E : Subgroup (adjointGroup τ K)}
    {x : Fin τ.rank → ZMod p} : x ∈ torusSet hζ E ↔ chevTorus τ ζ hζ (.ofAdd x) ∈ E :=
  Iff.rfl

theorem coe_chevTorus_mem_torusGroup (hζ : ζ ^ p = 1) (x : Multiplicative (Fin τ.rank → ZMod p)) :
    ((chevTorus τ ζ hζ x : adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K :=
  (torusCoordHom τ K (chevTorusExp τ ζ hζ x)).2

end TorusSet

section Count

variable {τ : Tag} {K : Type} [Field K]

theorem exists_card_eq_mul_card_torusSet [Finite K] {p : ℕ} [NeZero p] (hp : p.Prime)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {S : Subgroup (WeylGroup τ)} {E : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian p E)
    (hEX : E ≤ weylX τ K S) :
    ∃ A : Subgroup (WeylGroup τ), A ≤ S ∧ IsElemAbelian p A ∧
      Nat.card E = Nat.card A * Nat.card (torusSet hζ E) ∧
      ∀ x ∈ torusSet hζ E, ∀ a ∈ A, torusAct τ p a x = x := by
  have := Fact.mk hp
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  have hφinj := chevTorus_injective hζo hζ hdet
  have hφrange := range_chevTorus_eq_torusPow hζo hζ hdet hV
  obtain ⟨-, hker⟩ := weylQuotientHom_surjective_ker (τ := τ) (K := K)
  have hEM : ∀ e : E, ((e : adjointGroup τ K) : ModGL τ K) ∈ monomialSubgroup τ K :=
    fun e => (mem_weylX.mp (hEX e.2)).1
  let ι : E →* monomialSubgroup τ K :=
    ((adjointGroup τ K).subtype.comp E.subtype).codRestrict _ hEM
  let ψ : E →* WeylGroup τ := (weylQuotientHom τ K).comp ι
  have hψS : ∀ e : E, ψ e ∈ S := fun e => (mem_weylX.mp (hEX e.2)).2
  have hkerH : ∀ e : E, ψ e = 1 → ((e : adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K := by
    intro e he
    have h1 : ι e ∈ (weylQuotientHom τ K).ker := he
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hkerV : ∀ e : E, ψ e = 1 → (e : adjointGroup τ K) ∈ torusPow τ K p := fun e he =>
    ⟨hkerH e he, hE.2 _ e.2⟩
  have hψ1 : ∀ e : E, ((e : adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K → ψ e = 1 := by
    intro e he
    have h1 : ι e ∈ (weylQuotientHom τ K).ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact he
    exact h1
  have hfix : ∀ (e₀ : E) (ω : List (Fin τ.rank)), ψ e₀ = (coxeterSystem τ).wordProd ω →
      ∀ e : E, ψ e = 1 → ∃ x : Fin τ.rank → ZMod p,
        chevTorus τ ζ hζ (.ofAdd x) = (e : adjointGroup τ K) ∧ torusWord τ p ω x = x := by
    intro e₀ ω hω e he
    obtain ⟨x, hx⟩ : (e : adjointGroup τ K) ∈ (chevTorus τ ζ hζ).range := hφrange ▸ hkerV e he
    refine ⟨Multiplicative.toAdd x, by rw [ofAdd_toAdd]; exact hx, ?_⟩
    set n := nWord τ K ω with hn
    have hm := coe_nWord_mem_monomialSubgroup (K := K) ω
    have hρ : weylQuotientHom τ K (ι e₀ * (⟨_, hm⟩ : monomialSubgroup τ K)⁻¹) = 1 := by
      rw [map_mul, map_inv, weylQuotientHom_nWord]
      change ψ e₀ * _ = 1
      rw [hω, mul_inv_cancel]
    have hh : (((e₀ : adjointGroup τ K) * n⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
        torusGroup τ K := by
      have h1 : ι e₀ * (⟨_, hm⟩ : monomialSubgroup τ K)⁻¹ ∈ (weylQuotientHom τ K).ker := hρ
      rw [hker, Subgroup.mem_subgroupOf] at h1
      exact h1
    have hc0 : (e₀ : adjointGroup τ K) * e = e * e₀ := TableB.IsElemAbelian.comm hE e₀.2 e.2
    have hch : ((e₀ : adjointGroup τ K) * n⁻¹) * e = e * ((e₀ : adjointGroup τ K) * n⁻¹) :=
      Subtype.ext (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh)
        (torusGroup_le_diagonalGroup (hkerH e he)))
    have hne : n * (e : adjointGroup τ K) * n⁻¹ = e := by
      set h := (e₀ : adjointGroup τ K) * n⁻¹ with hhdef
      have hn' : n = h⁻¹ * e₀ := by
        rw [hhdef]
        group
      have hc0' : (e₀ : adjointGroup τ K) * e * (e₀ : adjointGroup τ K)⁻¹ = e := by
        rw [hc0]
        group
      have hch' : h⁻¹ * (e : adjointGroup τ K) * h = e := by
        rw [mul_assoc, ← hch]
        group
      rw [hn', mul_inv_rev, inv_inv]
      calc h⁻¹ * (e₀ : adjointGroup τ K) * e * ((e₀ : adjointGroup τ K)⁻¹ * h) =
          h⁻¹ * ((e₀ : adjointGroup τ K) * e * (e₀ : adjointGroup τ K)⁻¹) * h := by group
        _ = h⁻¹ * e * h := by rw [hc0']
        _ = e := hch'
    have hconj := nWord_conj_chevTorus hζ ω (Multiplicative.toAdd x)
    rw [ofAdd_toAdd, hx, hne] at hconj
    exact congrArg Multiplicative.toAdd (hφinj (hconj.symm.trans hx.symm))
  refine ⟨ψ.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, rfl⟩
    exact hψS e
  · have hcommE : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
    have hpowE : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (by simpa using hE.2 _ a.2)
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      show ψ a * ψ b = ψ b * ψ a
      rw [← map_mul, ← map_mul, hcommE]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow, hpowE, map_one]
  ·
    have hcardE := TableB.card_range_mul_card_ker ψ
    let f : torusSet hζ E → ψ.ker := fun x =>
      ⟨⟨chevTorus τ ζ hζ (.ofAdd x.1), x.2⟩, hψ1 _ (coe_chevTorus_mem_torusGroup hζ _)⟩
    have hf : Function.Bijective f := by
      refine ⟨fun x y hxy => ?_, fun e => ?_⟩
      · have h1 := congrArg (fun z : ψ.ker => ((z : E) : adjointGroup τ K)) hxy
        exact Subtype.ext (Multiplicative.ofAdd.injective (hφinj h1))
      · obtain ⟨x, hx⟩ : ((e : E) : adjointGroup τ K) ∈ (chevTorus τ ζ hζ).range :=
          hφrange ▸ hkerV e e.2
        have hxE : Multiplicative.toAdd x ∈ torusSet hζ E := by
          rw [mem_torusSet, ofAdd_toAdd, hx]
          exact (e : E).2
        refine ⟨⟨_, hxE⟩, Subtype.ext (Subtype.ext ?_)⟩
        show chevTorus τ ζ hζ (.ofAdd (Multiplicative.toAdd x)) = _
        rw [ofAdd_toAdd, hx]
    rw [← hcardE, Nat.card_congr (Equiv.ofBijective f hf)]
  · rintro x hx _ ⟨e₀, rfl⟩
    obtain ⟨ω, hω⟩ := (coxeterSystem τ).wordProd_surjective (ψ e₀)
    have he : ψ ⟨chevTorus τ ζ hζ (.ofAdd x), hx⟩ = 1 :=
      hψ1 _ (coe_chevTorus_mem_torusGroup hζ _)
    obtain ⟨y, hy, hy'⟩ := hfix e₀ ω hω.symm ⟨_, hx⟩ he
    have hxy : y = x := Multiplicative.ofAdd.injective (hφinj hy)
    rw [← hω, ← torusWord_eq_torusAct hsymm, ← hxy]
    exact hy'

theorem exists_mem_torusSet_of_le_weylX [Finite K] {p : ℕ} [NeZero p] (hp : p.Prime)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {S : Subgroup (WeylGroup τ)} {T : ℕ}
    {Good : Set (Fin τ.rank → ZMod p)}
    (hS : ∀ A : Subgroup (WeylGroup τ), A ≤ S → IsElemAbelian p A → A ≠ ⊥ →
      Nat.card A * Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ A, torusAct τ p a x = x} < T ∨
        (Nat.card A * Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ A, torusAct τ p a x = x} ≤ T ∧
          ∃ x ∈ Good, ∀ a ∈ A, torusAct τ p a x = x))
    (hGood : ∀ X : AddSubgroup (Fin τ.rank → ZMod p), T ≤ Nat.card X → ∃ x ∈ Good, x ∈ X)
    {E : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian p E) (hEX : E ≤ weylX τ K S)
    (hT : T ≤ Nat.card E) : ∃ x ∈ Good, chevTorus τ ζ hζ (.ofAdd x) ∈ E := by
  obtain ⟨A, hAS, hA, hcard, hfix⟩ :=
    exists_card_eq_mul_card_torusSet hp hdet hV hsymm hζo hζ hE hEX
  by_cases hbot : A = ⊥
  · have h1 : Nat.card A = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [h1, one_mul] at hcard
    exact hGood _ (hcard ▸ hT)
  · set C := {x : Fin τ.rank → ZMod p // ∀ a ∈ A, torusAct τ p a x = x} with hC
    let f : torusSet hζ E → C := fun x => ⟨x.1, hfix x.1 x.2⟩
    have hf : Function.Injective f := fun x y hxy =>
      Subtype.ext (congrArg Subtype.val hxy :)
    have hle : Nat.card (torusSet hζ E) ≤ Nat.card C := Nat.card_le_card_of_injective f hf
    have hApos : 0 < Nat.card A := Nat.card_pos
    rcases hS A hAS hA hbot with hlt | ⟨hle', x, hx, hxA⟩
    · change Nat.card A * Nat.card C < T at hlt
      exfalso
      have : Nat.card A * Nat.card (torusSet hζ E) ≤ Nat.card A * Nat.card C :=
        Nat.mul_le_mul_left _ hle
      omega
    · change Nat.card A * Nat.card C ≤ T at hle'
      have hge : Nat.card C ≤ Nat.card (torusSet hζ E) := by
        by_contra hcon
        have : Nat.card A * Nat.card (torusSet hζ E) < Nat.card A * Nat.card C :=
          Nat.mul_lt_mul_of_pos_left (not_le.mp hcon) hApos
        omega
      obtain ⟨y, hy⟩ := (hf.bijective_of_nat_card_le hge).2 ⟨x, hxA⟩
      have hyx : y.1 = x := congrArg Subtype.val hy
      exact ⟨x, hx, hyx ▸ y.2⟩

end Count

section IndexThree

variable {V : Type*} [AddCommGroup V]

theorem mem_or_mem_of_index_le_three [Finite V] (h3 : ∀ v : V, 3 • v = 0) {X : AddSubgroup V}
    (hX : X.index ≤ 3) (a b : V) :
    a ∈ X ∨ b ∈ X ∨ a + b ∈ X ∨ a - b ∈ X := by
  classical
  have : Finite (V ⧸ X) := Finite.of_surjective _ (QuotientAddGroup.mk'_surjective X)
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨ha, hb, hab, hab'⟩ := hcon
  have hq0 : ∀ x : V, (x : V ⧸ X) = 0 ↔ x ∈ X := fun x => QuotientAddGroup.eq_zero_iff x
  have e1 : (a : V ⧸ X) ≠ 0 := fun h => ha ((hq0 a).1 h)
  have e2 : (b : V ⧸ X) ≠ 0 := fun h => hb ((hq0 b).1 h)
  have e3 : (a : V ⧸ X) + b ≠ 0 := fun h =>
    hab ((hq0 _).1 (by rw [QuotientAddGroup.mk_add]; exact h))
  have e4 : (a : V ⧸ X) - b ≠ 0 := fun h =>
    hab' ((hq0 _).1 (by rw [QuotientAddGroup.mk_sub]; exact h))
  have e5 : (b : V ⧸ X) + b ≠ 0 := fun h => hb (by
    have h2 : b + b ∈ X := (hq0 _).1 (by rw [QuotientAddGroup.mk_add]; exact h)
    have e : b = -(b + b) + 3 • b := by rw [succ_nsmul, two_nsmul]; abel
    rw [e, h3 b, add_zero]
    exact neg_mem h2)
  have e6 : -(b : V ⧸ X) ≠ b := fun h => e5 (by nth_rewrite 2 [← h]; exact add_neg_cancel _)
  let f : Fin 4 → V ⧸ X := ![0, (a : V ⧸ X), -(b : V ⧸ X), (b : V ⧸ X)]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (show (0 : V ⧸ X) = a from hij).symm e1
    · exact absurd (neg_eq_zero.mp (show (0 : V ⧸ X) = -b from hij).symm) e2
    · exact absurd (show (0 : V ⧸ X) = b from hij).symm e2
    · exact absurd (show (a : V ⧸ X) = 0 from hij) e1
    · rfl
    · exact absurd (by rw [show (a : V ⧸ X) = -b from hij, neg_add_cancel]) e3
    · exact absurd (by rw [show (a : V ⧸ X) = b from hij, sub_self]) e4
    · exact absurd (neg_eq_zero.mp (show -(b : V ⧸ X) = 0 from hij)) e2
    · exact absurd (by rw [← show -(b : V ⧸ X) = a from hij, neg_add_cancel]) e3
    · rfl
    · exact absurd (show -(b : V ⧸ X) = b from hij) e6
    · exact absurd (show (b : V ⧸ X) = 0 from hij) e2
    · exact absurd (by rw [← show (b : V ⧸ X) = a from hij, sub_self]) e4
    · exact absurd (show (b : V ⧸ X) = -b from hij).symm e6
    · rfl
  have := Fintype.ofFinite (V ⧸ X)
  have h4 := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Fintype.card_eq_nat_card] at h4
  have : X.index = Nat.card (V ⧸ X) := rfl
  omega

theorem exists_mem_of_index_le_three [Finite V] (h3 : ∀ v : V, 3 • v = 0) {X : AddSubgroup V}
    (hX : X.index ≤ 3) (a b c : V) :
    a ∈ X ∨ b ∈ X ∨ c ∈ X ∨ a + b ∈ X ∨ b + c ∈ X ∨ a + b + c ∈ X := by
  rcases mem_or_mem_of_index_le_three h3 hX a b with h | h | h | hab
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  rcases mem_or_mem_of_index_le_three h3 hX b c with h | h | h | hbc
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
  have e : a + b + c = (a - b) + 2 • (b - c) + 3 • c := by
    rw [two_nsmul, succ_nsmul, two_nsmul]
    abel
  rw [e, h3 c, add_zero]
  exact add_mem hab (nsmul_mem hbc 2)

theorem three_nsmul_eq_zero {r : ℕ} (v : Fin r → ZMod 3) : 3 • v = 0 := by
  funext i
  rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  exact zero_mul _

theorem exists_isRoot_redMod_mem {τ : Tag} {α β γ : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (hαβ : IsRoot τ (α + β)) (hβγ : IsRoot τ (β + γ))
    (hαβγ : IsRoot τ (α + β + γ)) {X : AddSubgroup (Fin τ.rank → ZMod 3)} (hX : X.index ≤ 3) :
    ∃ δ, IsRoot τ δ ∧ redMod τ 3 δ ∈ X := by
  have hadd : ∀ u v : Fin τ.rank → ℤ, redMod τ 3 (u + v) = redMod τ 3 u + redMod τ 3 v :=
    fun u v => funext fun i => by simp [redMod]
  rcases exists_mem_of_index_le_three three_nsmul_eq_zero hX (redMod τ 3 α) (redMod τ 3 β)
    (redMod τ 3 γ) with h | h | h | h | h | h
  · exact ⟨α, hα, h⟩
  · exact ⟨β, hβ, h⟩
  · exact ⟨γ, hγ, h⟩
  · exact ⟨α + β, hαβ, by rw [hadd]; exact h⟩
  · exact ⟨β + γ, hβγ, by rw [hadd]; exact h⟩
  · exact ⟨α + β + γ, hαβγ, by rw [hadd, hadd]; exact h⟩

theorem index_le_three_of_card {r : ℕ} {X : AddSubgroup (Fin r → ZMod 3)}
    (hX : 3 ^ (r - 1) ≤ Nat.card X) (hr : 1 ≤ r) : X.index ≤ 3 := by
  have h := X.index_mul_card
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h
  have hr' : 3 ^ r = 3 * 3 ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hr'] at h
  by_contra hcon
  have : 3 * 3 ^ (r - 1) < X.index * Nat.card X :=
    Nat.mul_lt_mul_of_lt_of_le (not_le.mp hcon) hX Nat.card_pos
  omega

end IndexThree

end TableBExcTwoFusion

end CFSG.StandardType
