module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.LocalAnalysis.StandardType.GGTableBF4ThreeWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
open scoped Pointwise

namespace TableBExc

theorem card_fix_le_of_leftInverse {F : Type*} [Field F] [Fintype F] {r k : ℕ}
    (f : (Fin r → F) →ₗ[F] (Fin r → F)) (R C : Fin k → Fin r) (hC : Function.Injective C)
    (N : Fin k → Fin k → F)
    (hN : ∀ a b : Fin k, ∑ c, N a c * (f (Pi.single (C b) 1) (R c) - if R c = C b then 1 else 0) =
      if a = b then 1 else 0) :
    Nat.card {x : Fin r → F // f x = x} ≤ Fintype.card F ^ (r - k) := by
  classical
  set T : Set (Fin r) := (Set.range C)ᶜ with hT
  let g : {x : Fin r → F // f x = x} → (T → F) := fun x i => x.1 i
  have hinj : Function.Injective g := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    apply Subtype.ext
    set u := x - y with hu
    have hfu : f u = u := by rw [hu, map_sub, hx, hy]
    have hsupp : ∀ i, i ∉ Set.range C → u i = 0 := by
      intro i hi
      have h1 := congrFun hxy ⟨i, hi⟩
      simp only [g] at h1
      rw [hu, Pi.sub_apply, h1, sub_self]
    have hdecomp : u = ∑ b, u (C b) • (Pi.single (C b) 1 : Fin r → F) := by
      funext i
      rw [Finset.sum_apply]
      by_cases hi : i ∈ Set.range C
      · obtain ⟨b, rfl⟩ := hi
        rw [Finset.sum_eq_single b (fun b' _ hb' => by
            rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => hb' (hC h).symm), smul_zero])
          (fun h => absurd (Finset.mem_univ b) h), Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
          mul_one]
      · rw [hsupp i hi]
        refine (Finset.sum_eq_zero fun b _ => ?_).symm
        rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => hi ⟨b, h.symm⟩), smul_zero]
    have hrow : ∀ c : Fin k, ∑ b, (f (Pi.single (C b) 1) (R c) -
        if R c = C b then 1 else 0) * u (C b) = 0 := by
      intro c
      have hfu' : f u (R c) = ∑ b, u (C b) * f (Pi.single (C b) 1) (R c) := by
        conv_lhs => rw [hdecomp]
        rw [map_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_smul, Pi.smul_apply, smul_eq_mul]
      have hu' : u (R c) = ∑ b, u (C b) * (if R c = C b then 1 else 0) := by
        conv_lhs => rw [hdecomp]
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      have h1 : f u (R c) - u (R c) = 0 := by rw [hfu, sub_self]
      rw [hfu', hu', ← Finset.sum_sub_distrib] at h1
      exact (Finset.sum_congr rfl fun b _ => by ring).trans h1
    have hzero : ∀ b, u (C b) = 0 := by
      intro b
      have h1 : ∑ a, (if b = a then (1 : F) else 0) * u (C a) = u (C b) := by simp
      rw [← h1]
      calc ∑ a, (if b = a then (1 : F) else 0) * u (C a)
          = ∑ a, (∑ c, N b c * (f (Pi.single (C a) 1) (R c) -
              if R c = C a then 1 else 0)) * u (C a) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [hN b a]
        _ = ∑ c, N b c * ∑ a, (f (Pi.single (C a) 1) (R c) -
              if R c = C a then 1 else 0) * u (C a) := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
            ring
        _ = 0 := by simp only [hrow, mul_zero, Finset.sum_const_zero]
    have hu0 : u = 0 := by
      rw [hdecomp]
      exact Finset.sum_eq_zero fun b _ => by rw [hzero b, zero_smul]
    rw [hu, sub_eq_zero] at hu0
    exact hu0
  have hcardT : Nat.card T = r - k := by
    rw [hT, Nat.card_coe_set_eq, Set.ncard_compl, ← Nat.card_coe_set_eq,
      Nat.card_range_of_injective hC, Nat.card_fin, Nat.card_fin]
  calc Nat.card {x : Fin r → F // f x = x} ≤ Nat.card (T → F) :=
        Nat.card_le_card_of_injective g hinj
    _ = Fintype.card F ^ (r - k) := by
        rw [Nat.card_fun, hcardT, Nat.card_eq_fintype_card]

section TorusWord

variable (τ : Tag) (p : ℕ)

@[expose] def torusRefl (i : Fin τ.rank) (a : Fin τ.rank → ZMod p) : Fin τ.rank → ZMod p :=
  a - (∑ j, ((τ.cartan j i : ℤ) : ZMod p) * a j) • Pi.single i 1

@[expose] def torusWord (ω : List (Fin τ.rank)) (a : Fin τ.rank → ZMod p) : Fin τ.rank → ZMod p :=
  ω.foldr (torusRefl τ p) a

variable {τ p}

theorem torusRefl_eq (i : Fin τ.rank) (a : Fin τ.rank → ZMod p) :
    torusRefl τ p i a = a - CFSG.RankThree.CentralCover.cartanFunctional τ p i a • Pi.single i 1 := by
  rw [CFSG.RankThree.CentralCover.cartanFunctional_apply]
  rfl

variable (τ p) in
@[expose] noncomputable def torusWordLin (ω : List (Fin τ.rank)) :
    (Fin τ.rank → ZMod p) →ₗ[ZMod p] (Fin τ.rank → ZMod p) :=
  ω.foldr (fun i L => (LinearMap.id - (CFSG.RankThree.CentralCover.cartanFunctional τ p i).smulRight
    (Pi.single i 1 : Fin τ.rank → ZMod p)).comp L) LinearMap.id

theorem torusWordLin_apply (ω : List (Fin τ.rank)) (a : Fin τ.rank → ZMod p) :
    torusWordLin τ p ω a = torusWord τ p ω a := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change ((LinearMap.id - (CFSG.RankThree.CentralCover.cartanFunctional τ p i).smulRight
      (Pi.single i 1 : Fin τ.rank → ZMod p)).comp (torusWordLin τ p ω)) a =
        torusRefl τ p i (torusWord τ p ω a)
    rw [LinearMap.comp_apply, ih, torusRefl_eq, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply]

theorem card_fix_torusWord_le [Fact p.Prime] (ω : List (Fin τ.rank)) {k : ℕ}
    (R C : Fin k → Fin τ.rank) (hC : Function.Injective C) (N : Fin k → Fin k → ZMod p)
    (hN : ∀ a b : Fin k, ∑ c, N a c * (torusWord τ p ω (Pi.single (C b) 1) (R c) -
      if R c = C b then 1 else 0) = if a = b then 1 else 0) :
    Nat.card {x : Fin τ.rank → ZMod p // torusWord τ p ω x = x} ≤ p ^ (τ.rank - k) := by
  have h := card_fix_le_of_leftInverse (torusWordLin τ p ω) R C hC N
    (by simpa only [torusWordLin_apply] using hN)
  simp only [torusWordLin_apply, ZMod.card] at h
  exact h

end TorusWord

section Weyl

variable (τ : Tag) (K : Type) [Field K]

@[expose] noncomputable def nWord (ω : List (Fin τ.rank)) : adjointGroup τ K :=
  (ω.map fun i => (⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup τ K)).prod

variable {τ K}

theorem nWord_cons (i : Fin τ.rank) (ω : List (Fin τ.rank)) :
    nWord τ K (i :: ω) = ⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩ * nWord τ K ω := by
  rw [nWord, List.map_cons, List.prod_cons]
  rfl

theorem coe_nWord (ω : List (Fin τ.rank)) :
    ((nWord τ K ω : adjointGroup τ K) : ModGL τ K) = (ω.map fun i => weylElt τ K i 1).prod := by
  induction ω with
  | nil => rfl
  | cons i ω ih => rw [nWord_cons, Subgroup.coe_mul, ih, List.map_cons, List.prod_cons]

theorem coe_nWord_mem_monomialSubgroup (ω : List (Fin τ.rank)) :
    ((nWord τ K ω : adjointGroup τ K) : ModGL τ K) ∈ monomialSubgroup τ K := by
  rw [coe_nWord]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact weylElt_mem_monomialSubgroup i

theorem nWord_conj_chevTorus {p : ℕ} [NeZero p] {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (ω : List (Fin τ.rank)) (a : Fin τ.rank → ZMod p) :
    nWord τ K ω * chevTorus τ ζ hζ (.ofAdd a) * (nWord τ K ω)⁻¹ =
      chevTorus τ ζ hζ (.ofAdd (torusWord τ p ω a)) := by
  induction ω with
  | nil => simp [nWord, torusWord]
  | cons i ω ih =>
    rw [nWord_cons, mul_inv_rev]
    have e : ∀ x y z : adjointGroup τ K, x * y * z * (y⁻¹ * x⁻¹) = x * (y * z * y⁻¹) * x⁻¹ :=
      fun x y z => by group
    rw [e, ih, weylElt_conj_chevTorus]
    show _ = chevTorus τ ζ hζ (.ofAdd (torusRefl τ p i (torusWord τ p ω a)))
    rw [torusRefl_eq]


theorem weylQuotientHom_nWord (ω : List (Fin τ.rank)) :
    weylQuotientHom τ K ⟨_, coe_nWord_mem_monomialSubgroup ω⟩ = (coxeterSystem τ).wordProd ω := by
  apply weylQuotientHom_eq
  show MapsRootLines ((nWord τ K ω : adjointGroup τ K) : ModGL τ K) _
  rw [coe_nWord]
  exact mapsRootLines_list_prod ω

theorem weylQuotientHom_surjective_ker :
    Function.Surjective (weylQuotientHom τ K) ∧
      (weylQuotientHom τ K).ker = (torusGroup τ K).subgroupOf (monomialSubgroup τ K) := by
  obtain ⟨-, ⟨ρ, hsurj, hmaps, -, -, hker⟩, -⟩ := Weyl_normalizer_quotient τ K
  have hρ : weylQuotientHom τ K = ρ := MonoidHom.ext fun g => weylQuotientHom_eq (hmaps g)
  rw [hρ]
  exact ⟨hsurj, hker⟩

end Weyl

section X

variable (τ : Tag) (K : Type) [Field K]

@[expose] noncomputable def weylX₀ (S : Subgroup (WeylGroup τ)) : Subgroup (monomialSubgroup τ K) :=
  S.comap (weylQuotientHom τ K)

@[expose] noncomputable def weylX (S : Subgroup (WeylGroup τ)) : Subgroup (adjointGroup τ K) :=
  ((weylX₀ τ K S).map (monomialSubgroup τ K).subtype).subgroupOf (adjointGroup τ K)

variable {τ K}

theorem mem_weylX {S : Subgroup (WeylGroup τ)} {g : adjointGroup τ K} :
    g ∈ weylX τ K S ↔ ∃ hg : (g : ModGL τ K) ∈ monomialSubgroup τ K,
      weylQuotientHom τ K ⟨g, hg⟩ ∈ S := by
  rw [weylX, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨m, hm, hmg⟩
    have hg : (g : ModGL τ K) ∈ monomialSubgroup τ K := hmg ▸ m.2
    refine ⟨hg, ?_⟩
    have : m = ⟨g, hg⟩ := Subtype.ext hmg
    rw [← this]
    exact hm
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem card_weylX₀ [Finite K] (S : Subgroup (WeylGroup τ)) :
    Nat.card (weylX₀ τ K S) = Nat.card S * Nat.card (torusGroup τ K) := by
  have : Finite (monomialSubgroup τ K) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (monomialSubgroup_le_adjointGroup' (τ := τ) (K := K)))
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  obtain ⟨hsurj, hker⟩ := weylQuotientHom_surjective_ker (τ := τ) (K := K)
  set ρ := weylQuotientHom τ K with hρdef
  set f : weylX₀ τ K S →* WeylGroup τ := ρ.comp (weylX₀ τ K S).subtype with hf
  have hrange : f.range = S := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hw
      obtain ⟨m, rfl⟩ := hsurj w
      exact ⟨⟨m, hw⟩, rfl⟩
  have hkerle : ρ.ker ≤ weylX₀ τ K S := fun m hm => by
    show ρ m ∈ S
    rw [MonoidHom.mem_ker.mp hm]
    exact one_mem _
  have hfker : f.ker = ρ.ker.subgroupOf (weylX₀ τ K S) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have h1 := TableB.card_range_mul_card_ker f
  rw [hrange, hfker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv,
    hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show torusGroup τ K ≤ monomialSubgroup τ K from le_sup_left)).toEquiv] at h1
  exact h1.symm

theorem card_weylX [Finite K] (S : Subgroup (WeylGroup τ)) :
    Nat.card (weylX τ K S) = Nat.card S * Nat.card (torusGroup τ K) := by
  have hle : (weylX₀ τ K S).map (monomialSubgroup τ K).subtype ≤ adjointGroup τ K :=
    (Subgroup.map_subtype_le _).trans monomialSubgroup_le_adjointGroup'
  rw [weylX, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Subgroup.card_map_of_injective (monomialSubgroup τ K).subtype_injective, card_weylX₀]

theorem index_weylX_eq [Finite K] {S : Subgroup (WeylGroup τ)} {M : ℕ}
    (hC : Nat.card (adjointGroup τ K) = Nat.card S * Nat.card (torusGroup τ K) * M) :
    (weylX τ K S).index = M := by
  have hcard := Subgroup.card_mul_index (weylX τ K S)
  rw [card_weylX, hC] at hcard
  have hpos : 0 < Nat.card S * Nat.card (torusGroup τ K) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos hcard

end X

section Count

variable {τ : Tag} {K : Type} [Field K]

theorem range_chevTorus_eq_torusPow {p : ℕ} [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) :
    (chevTorus τ ζ hζ).range = torusPow τ K p := by
  have hle : (chevTorus τ ζ hζ).range ≤ torusPow τ K p := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(torusCoordHom τ K (chevTorusExp τ ζ hζ x)).2, ?_⟩
    rw [← map_pow, pow_eq_one_of_zmod, map_one]
  have : Finite (torusPow τ K p) := Nat.finite_of_card_ne_zero (by
    rw [hV]
    exact pow_ne_zero _ (NeZero.ne p))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hV, ← Nat.card_congr (MonoidHom.ofInjective (chevTorus_injective hζo hζ hdet)).toEquiv,
    card_multiplicative_fin_zmod]


theorem le_torusPow_or_card_lt_of_le_weylX [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) {S : Subgroup (WeylGroup τ)} {B : ℕ}
    (hS : ∀ s ∈ S, s ≠ 1 → ∃ (k : ℕ) (ω : List (Fin τ.rank)),
      (coxeterSystem τ).wordProd ω = s ^ k ∧
        Nat.card S * Nat.card {x : Fin τ.rank → ZMod p // torusWord τ p ω x = x} < B)
    {E : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian p E) (hEX : E ≤ weylX τ K S) :
    E ≤ torusPow τ K p ∨ Nat.card E < B := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  have : Finite (WeylGroup τ) := Finite.of_surjective _
    (weylQuotientHom_surjective_ker (τ := τ) (K := K)).1
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
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
  have hcardE := TableB.card_range_mul_card_ker ψ
  by_cases hr : ψ.range = ⊥
  · left
    intro e he
    have h1 : ψ ⟨e, he⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hr, Subgroup.mem_bot] at h1
    exact hkerV ⟨e, he⟩ h1
  · right
    obtain ⟨w, hw, hw1⟩ : ∃ w ∈ ψ.range, w ≠ 1 := by
      by_contra hcon
      apply hr
      rw [eq_bot_iff]
      intro w hw
      rw [Subgroup.mem_bot]
      by_contra hw1
      exact hcon ⟨w, hw, hw1⟩
    obtain ⟨e₁, rfl⟩ := hw
    obtain ⟨k, ω, hω, hωB⟩ := hS (ψ e₁) (hψS e₁) hw1
    set e₀ := e₁ ^ k with he₀
    have hω' : ψ e₀ = (coxeterSystem τ).wordProd ω := by rw [he₀, map_pow, hω]
    have hk : Nat.card ψ.ker ≤
        Nat.card {x : Fin τ.rank → ZMod p // torusWord τ p ω x = x} := by
      have hex : ∀ e : ψ.ker, ∃ x : {x : Fin τ.rank → ZMod p // torusWord τ p ω x = x},
          chevTorus τ ζ hζ (.ofAdd x.1) = ((e : E) : adjointGroup τ K) := by
        intro e
        obtain ⟨x, hx, hx'⟩ := hfix e₀ ω hω' e e.2
        exact ⟨⟨x, hx'⟩, hx⟩
      choose g hg using hex
      refine Nat.card_le_card_of_injective g fun a b hab => ?_
      apply Subtype.ext
      apply Subtype.ext
      rw [← hg a, ← hg b, hab]
    have hrS : Nat.card ψ.range ≤ Nat.card S := by
      have hle : ψ.range ≤ S := by
        rintro _ ⟨e, rfl⟩
        exact hψS e
      exact Subgroup.card_le_of_le hle
    calc Nat.card E = Nat.card ψ.range * Nat.card ψ.ker := hcardE.symm
      _ ≤ Nat.card S * Nat.card {x : Fin τ.rank → ZMod p // torusWord τ p ω x = x} :=
        Nat.mul_le_mul hrS hk
      _ < B := hωB

theorem ggExcToralRankInput_of_weylX [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) {S : Subgroup (WeylGroup τ)}
    (hidx : ¬ p ∣ (weylX τ K S).index)
    (hS : ∀ s ∈ S, s ≠ 1 → ∃ (k : ℕ) (ω : List (Fin τ.rank)),
      (coxeterSystem τ).wordProd ω = s ^ k ∧
        Nat.card S * Nat.card {x : Fin τ.rank → ZMod p // torusWord τ p ω x = x} < p ^ τ.rank) :
    GGExcToralRankInput τ K p := by
  intro E hE hcard
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  obtain ⟨g, hg⟩ := TableBF4.exists_conj_le_of_not_dvd_index hp hidx
    (TableB.isPGroup_of_isElemAbelian hE)
  have hcard' : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  refine ⟨g, ?_⟩
  rcases le_torusPow_or_card_lt_of_le_weylX hp hpq hdet hV hS (TableB.isElemAbelian_map hE _) hg
    with h | h
  · exact Subgroup.eq_of_le_of_card_ge h (by rw [hV, hcard']; exact hcard)
  · omega

end Count

section Words

variable {τ : Tag}

@[expose] def wordAct (τ : Tag) (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  ω.foldr (fun i v => reflect τ i v) v

theorem wordProd_smul (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd ω • v = wordAct τ ω v := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul]; rfl
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih]
    exact simple_smul i _

theorem wordProd_replicate (ω : List (Fin τ.rank)) (a : ℕ) :
    (coxeterSystem τ).wordProd (List.replicate a ω).flatten =
      (coxeterSystem τ).wordProd ω ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ, List.flatten_cons, CoxeterSystem.wordProd_append, ih, pow_succ']

theorem orderOf_wordProd_eq {p : ℕ} (hp : p.Prime) (ω : List (Fin τ.rank))
    (hpow : ∀ i : Fin τ.rank, wordAct τ (List.replicate p ω).flatten (Pi.single i 1) = Pi.single i 1)
    (hne : ∃ i : Fin τ.rank, wordAct τ ω (Pi.single i 1) ≠ Pi.single i 1) :
    orderOf ((coxeterSystem τ).wordProd ω) = p := by
  have := Fact.mk hp
  refine orderOf_eq_prime ?_ ?_
  · rw [← wordProd_replicate]
    exact ext_single fun i => by rw [wordProd_smul, one_smul, hpow i]
  · intro h
    obtain ⟨i, hi⟩ := hne
    apply hi
    rw [← wordProd_smul, h, one_smul]

theorem exists_pow_eq_of_mem_zpowers {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {w : G}
    (hw : orderOf w = p) {s : G} (hs : s ∈ Subgroup.zpowers w) (hs1 : s ≠ 1) :
    ∃ k : ℕ, s ^ k = w := by
  have := Fact.mk hp
  have hfin : IsOfFinOrder w := orderOf_pos_iff.mp (hw ▸ hp.pos)
  have hsp : s ^ p = 1 := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hw, pow_orderOf_eq_one,
      one_zpow]
  have hso : orderOf s = p := orderOf_eq_prime hsp hs1
  have hle : Subgroup.zpowers s ≤ Subgroup.zpowers w := Subgroup.zpowers_le.mpr hs
  have heq : Subgroup.zpowers s = Subgroup.zpowers w := by
    have : Finite (Subgroup.zpowers w) := hfin.finite_zpowers
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hso, hw]
  have hws : w ∈ Subgroup.zpowers s := heq ▸ Subgroup.mem_zpowers w
  have hsfin : IsOfFinOrder s := orderOf_pos_iff.mp (hso ▸ hp.pos)
  obtain ⟨k, hk⟩ := (hsfin.mem_powers_iff_mem_zpowers).mpr hws
  exact ⟨k, hk⟩

end Words

section Cyclic

variable {τ : Tag} {K : Type} [Field K]

theorem ggExcToralRankInput_of_cyclic [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) (ω : List (Fin τ.rank))
    (hω : orderOf ((coxeterSystem τ).wordProd ω) = p) {M : ℕ}
    (hC : Nat.card (adjointGroup τ K) = p * Nat.card (torusGroup τ K) * M) (hM : ¬ p ∣ M)
    (hfix : p * Nat.card {x : Fin τ.rank → ZMod p // torusWord τ p ω x = x} < p ^ τ.rank) :
    GGExcToralRankInput τ K p := by
  have hS : Nat.card (Subgroup.zpowers ((coxeterSystem τ).wordProd ω)) = p := by
    rw [Nat.card_zpowers, hω]
  refine ggExcToralRankInput_of_weylX hp hpq hdet hV (S := Subgroup.zpowers
    ((coxeterSystem τ).wordProd ω)) (by rw [index_weylX_eq (by rw [hS]; exact hC)]; exact hM)
    fun s hs hs1 => ?_
  obtain ⟨k, hk⟩ := exists_pow_eq_of_mem_zpowers hp hω hs hs1
  exact ⟨k, ω, hk.symm, by rw [hS]; exact hfix⟩

end Cyclic

end TableBExc

end CFSG.StandardType
