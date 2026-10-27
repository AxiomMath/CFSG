module

public import CFSG.LocalAnalysis.SteinbergSFOneAxisInvariantComplement

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OneAxisOvergroup

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
  OneAxisRadicalStructure OneAxisComplement
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped commutatorElement Matrix Pointwise

section General

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf {A N : Subgroup G} (hAN : A ≤ normalizer (N : Set G)) :
    Nat.card (A ⊔ N : Subgroup G) * Nat.card (A ⊓ N : Subgroup G) = Nat.card A * Nat.card N := by
  have := normal_subgroupOf_of_le_normalizer hAN
  have := normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup G) := by
    rw [← card_map_of_injective A.subtype_injective, subgroupOf_map_subtype, inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem coe_sup_eq_mul_of_swap {H K : Subgroup G}
    (hsw : ∀ k ∈ K, ∀ h ∈ H, ∃ h' ∈ H, ∃ k' ∈ K, k * h = h' * k') :
    ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) := by
  let S : Subgroup G :=
    { carrier := (H : Set G) * (K : Set G)
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        obtain ⟨h', hh', k', hk', e⟩ := hsw k₁ hk₁ h₂ hh₂
        refine ⟨h₁ * h', mul_mem hh₁ hh', k' * k₂, mul_mem hk' hk₂, ?_⟩
        calc h₁ * h' * (k' * k₂) = h₁ * (h' * k') * k₂ := by group
          _ = h₁ * k₁ * (h₂ * k₂) := by rw [← e]; group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        obtain ⟨h', hh', k', hk', e⟩ := hsw k⁻¹ (inv_mem hk) h⁻¹ (inv_mem hh)
        exact ⟨h', hh', k', hk', by rw [mul_inv_rev, e]⟩ }
  have hS : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, one_mem _, mul_one h⟩)
    fun k hk => ⟨1, one_mem _, k, hk, one_mul k⟩
  refine Set.Subset.antisymm (fun x hx => hS hx) ?_
  rintro _ ⟨h, hh, k, hk, rfl⟩
  exact mul_mem (mem_sup_left hh) (mem_sup_right hk)

theorem mem_or_mul_mem {N : Subgroup G} {t : G} (htt : t * t = 1)
    (htN : t ∈ normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ zpowers t) :
    x ∈ N ∨ t * x ∈ N := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr htN)] at hx
  obtain ⟨y, hy, c, hc, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hc
  rcases zpow_eq_one_or_eq htt j with h1 | h1
  · left
    simp only at h1 ⊢
    rw [h1, mul_one]
    exact hy
  · right
    simp only at h1 ⊢
    rw [h1, show t * (y * t) = t * y * t⁻¹ by rw [inv_eq_of_mul_eq_one_right htt, mul_assoc]]
    exact (mem_normalizer_iff.mp htN y).mp hy

theorem inf_zpowers_eq_bot {N : Subgroup G} {t : G} (htt : t * t = 1) (htN : t ∉ N) :
    N ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxN, hxt⟩
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hxt
  rcases zpow_eq_one_or_eq htt j with h | h
  · rw [h]
    exact one_mem _
  · rw [h] at hxN
    exact absurd hxN htN

theorem card_sup_zpowers [Finite G] {N : Subgroup G} {t : G} (htt : t * t = 1)
    (htN : t ∈ normalizer (N : Set G)) (htN' : t ∉ N) :
    Nat.card (N ⊔ zpowers t : Subgroup G) = 2 * Nat.card N ∧
      N.relIndex (N ⊔ zpowers t) = 2 := by
  have ht1 : t ≠ 1 := fun h => htN' (h ▸ one_mem N)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two, htt]) ht1
  have h1 := card_sup_mul_card_inf (zpowers_le.mpr htN)
  rw [inf_comm, inf_zpowers_eq_bot htt htN', card_bot, mul_one, Nat.card_zpowers, hord,
    sup_comm] at h1
  refine ⟨h1, ?_⟩
  have h2 := relIndex_mul_card N (N ⊔ zpowers t)
  rw [inf_of_le_left le_sup_left, h1] at h2
  have hpos : 0 < Nat.card N := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h2])

theorem card_le_two_mul {N D X : Subgroup G} (hN : N.relIndex D = 2) (hXD : X ≤ D) :
    Nat.card X ≤ 2 * Nat.card (N ⊓ X : Subgroup G) := by
  have h1 := relIndex_mul_card N X
  have h2 := relIndex_le_of_le_right hXD (by rw [hN]; norm_num)
  rw [hN] at h2
  calc Nat.card X = N.relIndex X * Nat.card (N ⊓ X : Subgroup G) := h1.symm
    _ ≤ 2 * Nat.card (N ⊓ X : Subgroup G) := Nat.mul_le_mul_right _ h2

theorem mem_map_conj_inv_iff {M : Subgroup G} {g x : G} :
    x ∈ M.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ M := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rwa [show g * (g⁻¹ * m * g) * g⁻¹ = m by group]
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem card_map_conj (M : Subgroup G) (g : G) :
    Nat.card (M.map (MulAut.conj g).toMonoidHom) = Nat.card M :=
  card_map_of_injective (MulAut.conj g).injective

variable [Finite G]

theorem card_le_of_coord {A : Type*} [AddGroup A] [Finite A] {X Y : Subgroup G} (f : G → A)
    (hf : ∀ x ∈ X, ∀ y ∈ X, f (x * y) = f x + f y) (hker : ∀ x ∈ X, f x = 0 → x ∈ Y) :
    Nat.card X ≤ Nat.card (X ⊓ Y : Subgroup G) * Nat.card A ∧
      (Nat.card (X ⊓ Y : Subgroup G) * Nat.card A ≤ Nat.card X → ∀ a : A, ∃ x ∈ X, f x = a) := by
  have hf1 : f 1 = 0 := by
    have := hf 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact (add_eq_left.mp this.symm)
  let F : ↥X →* Multiplicative A :=
    { toFun := fun x => Multiplicative.ofAdd (f x)
      map_one' := by simp [hf1]
      map_mul' := fun x y => by
        rw [coe_mul, hf x x.2 y y.2]
        rfl }
  have hF : ∀ x : X, F x = Multiplicative.ofAdd (f x) := fun _ => rfl
  have hcardX : Nat.card X = Nat.card F.ker * Nat.card F.range := by
    rw [← card_mul_index F.ker, index_ker]
  have hker' : Nat.card F.ker ≤ Nat.card (X ⊓ Y : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun k => (⟨((k : X) : G), (k : X).2, hker _ (k : X).2 ?_⟩ : (X ⊓ Y : Subgroup G))) ?_
    · have h1 : F k = 1 := k.2
      rw [hF] at h1
      exact Multiplicative.ofAdd.injective h1
    · intro k k' h
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  have hrange : Nat.card F.range ≤ Nat.card A := by
    calc Nat.card F.range ≤ Nat.card (Multiplicative A) := card_le_card_group _
      _ = Nat.card A := rfl
  refine ⟨?_, fun hge a => ?_⟩
  · rw [hcardX]
    exact Nat.mul_le_mul hker' hrange
  · have hpos : 0 < Nat.card (X ⊓ Y : Subgroup G) := Nat.card_pos
    have h1 : Nat.card A ≤ Nat.card F.range := by
      have h2 : Nat.card (X ⊓ Y : Subgroup G) * Nat.card A ≤
          Nat.card (X ⊓ Y : Subgroup G) * Nat.card F.range :=
        hge.trans (hcardX ▸ Nat.mul_le_mul_right _ hker')
      exact Nat.le_of_mul_le_mul_left h2 hpos
    have htop : F.range = ⊤ := eq_top_of_card_eq _ (le_antisymm hrange h1 |>.trans rfl)
    obtain ⟨x, hx⟩ := (MonoidHom.range_eq_top.mp htop) (Multiplicative.ofAdd a)
    exact ⟨x, x.2, Multiplicative.ofAdd.injective hx⟩

end General

section Model

variable {K : Type} [Field K]

variable (K) in
@[expose] def weylMat₁ : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

variable (K) in
@[expose] def weylMat₂ : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

theorem weylMat₁_mul_self : weylMat₁ K * weylMat₁ K = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [weylMat₁, Matrix.mul_apply, Fin.sum_univ_four]

theorem weylMat₂_mul_self : weylMat₂ K * weylMat₂ K = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [weylMat₂, Matrix.mul_apply, Fin.sum_univ_four]

theorem weylMat₁_mem : (weylMat₁ K)ᵀ * minorJ K * weylMat₁ K = minorJ K := by
  ext k l
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
  fin_cases k <;> fin_cases l <;> simp [weylMat₁]

theorem weylMat₂_mem : (weylMat₂ K)ᵀ * minorJ K * weylMat₂ K = minorJ K := by
  ext k l
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
  fin_cases k <;> fin_cases l <;> simp [weylMat₂]

variable (K) in
@[expose] def weylElt₁ : antiSp K :=
  ⟨⟨weylMat₁ K, weylMat₁ K, weylMat₁_mul_self, weylMat₁_mul_self⟩, weylMat₁_mem⟩

variable (K) in
@[expose] def weylElt₂ : antiSp K :=
  ⟨⟨weylMat₂ K, weylMat₂ K, weylMat₂_mul_self, weylMat₂_mul_self⟩, weylMat₂_mem⟩

theorem glMat_weylElt₁ : glMat (weylElt₁ K : GL (Fin 4) K) = weylMat₁ K := rfl

theorem glMat_weylElt₂ : glMat (weylElt₂ K : GL (Fin 4) K) = weylMat₂ K := rfl

theorem weylElt₁_mul_self : weylElt₁ K * weylElt₁ K = 1 := antiSp_ext weylMat₁_mul_self

theorem weylElt₂_mul_self : weylElt₂ K * weylElt₂ K = 1 := antiSp_ext weylMat₂_mul_self

theorem diagMat_eq (r s : K) :
    diagMat r s = !![r⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, s, 0; 0, 0, 0, r] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [diagMat]

theorem weylElt₁_conj_axisTorus {δ : antiSp K} (hδ : δ ∈ FullCenterTorus.axisTorus K Axis.one) :
    weylElt₁ K * δ * weylElt₁ K ∈ FullCenterTorus.axisTorus K Axis.one := by
  obtain ⟨r, hr, hδm⟩ := hδ
  refine ⟨r⁻¹, inv_ne_zero hr, ?_⟩
  change weylMat₁ K * glMat (δ : GL (Fin 4) K) * weylMat₁ K = diagMat r⁻¹ r⁻¹⁻¹
  rw [hδm, inv_inv, diagMat_eq, diagMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMat₁, Matrix.mul_apply, Fin.sum_univ_four]

variable [CharP K 2]

theorem weylElt₁_conj (b c d : K) : weylElt₁ K * uElt 0 b c d * weylElt₁ K = uElt 0 b d c := by
  apply antiSp_ext
  change weylMat₁ K * uMat 0 b c d * weylMat₁ K = uMat 0 b d c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMat₁, uMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem weylElt₂_conj (a b c : K) : weylElt₂ K * uElt a b c 0 * weylElt₂ K = uElt b a c 0 := by
  apply antiSp_ext
  change weylMat₂ K * uMat a b c 0 * weylMat₂ K = uMat b a c 0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMat₂, uMat, Matrix.mul_apply, Fin.sum_univ_four]

end Model

section Coord

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {φ : L ≃* antiSp K}

local notation "𝐮[" a ", " b ", " c ", " d "]" => ((φ.symm (uElt a b c d) : L) : G)
local notation "𝐰₁" => ((φ.symm (weylElt₁ K) : L) : G)
local notation "𝐰₂" => ((φ.symm (weylElt₂ K) : L) : G)

theorem u_mul (a b c d A B C D : K) : 𝐮[a, b, c, d] * 𝐮[A, B, C, D] =
    𝐮[a + A, b + B + a * D, c + C + a * B + a * A * D + b * A, d + D] := by
  rw [← coe_mul, ← map_mul, uElt_mul]

theorem u_inv (a b c d : K) : (𝐮[a, b, c, d])⁻¹ = 𝐮[a, b + a * d, c, d] := by
  rw [← coe_inv, ← map_inv, uElt_inv]

theorem u_zero : 𝐮[(0 : K), 0, 0, 0] = 1 := by
  rw [uElt_zero_eq_one, map_one, OneMemClass.coe_one]

theorem u_inj {a b c d A B C D : K} (h : 𝐮[a, b, c, d] = 𝐮[A, B, C, D]) :
    a = A ∧ b = B ∧ c = C ∧ d = D :=
  uElt_inj (φ.symm.injective (Subtype.ext h))

theorem u_mem_P (a b c d : K) : 𝐮[a, b, c, d] ∈ pull φ (antiUnipotent K) :=
  symm_mem_pull.mpr (uElt_mem_antiUnipotent a b c d)

theorem exists_u_eq {x : G} (hx : x ∈ pull φ (antiUnipotent K)) :
    ∃ a b c d : K, 𝐮[a, b, c, d] = x := by
  obtain ⟨y, ⟨a, b, c, d, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hx
  exact ⟨a, b, c, d, rfl⟩

theorem u_mem_A₁_iff {a b c d : K} :
    𝐮[a, b, c, d] ∈ pull φ (rootA K Axis.one) ↔ a = 0 := by
  rw [symm_mem_pull]
  constructor
  · rintro ⟨b', c', d', h⟩
    exact (uElt_inj h).1
  · rintro rfl
    exact ⟨b, c, d, rfl⟩

theorem u_mem_A₂_iff {a b c d : K} :
    𝐮[a, b, c, d] ∈ pull φ (rootA K Axis.two) ↔ d = 0 := by
  rw [symm_mem_pull]
  constructor
  · rintro ⟨a', b', c', h⟩
    exact (uElt_inj h).2.2.2
  · rintro rfl
    exact ⟨a, b, c, rfl⟩

theorem u_mem_Z_iff {a b c d : K} :
    𝐮[a, b, c, d] ∈ pull φ (antiUnipotentCenter K) ↔ a = 0 ∧ d = 0 := by
  rw [symm_mem_pull]
  constructor
  · rintro ⟨b', c', h⟩
    exact ⟨(uElt_inj h).1, (uElt_inj h).2.2.2⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨b, c, rfl⟩

theorem u_mem_U₁_iff {a b c d : K} :
    𝐮[a, b, c, d] ∈ pull φ (rootU K Axis.one) ↔ a = 0 ∧ c = 0 ∧ d = 0 := by
  rw [symm_mem_pull]
  constructor
  · rintro ⟨b', h⟩
    exact ⟨(uElt_inj h).1, (uElt_inj h).2.2.1, (uElt_inj h).2.2.2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨b, rfl⟩

theorem u_mem_U₂_iff {a b c d : K} :
    𝐮[a, b, c, d] ∈ pull φ (rootU K Axis.two) ↔ a = 0 ∧ b = 0 ∧ d = 0 := by
  rw [symm_mem_pull]
  constructor
  · rintro ⟨c', h⟩
    exact ⟨(uElt_inj h).1, (uElt_inj h).2.1, (uElt_inj h).2.2.2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨c, rfl⟩

theorem exists_u_eq_of_A₁ {x : G} (hx : x ∈ pull φ (rootA K Axis.one)) :
    ∃ b c d : K, 𝐮[0, b, c, d] = x := by
  obtain ⟨y, ⟨b, c, d, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hx
  exact ⟨b, c, d, rfl⟩

theorem exists_u_eq_of_A₂ {x : G} (hx : x ∈ pull φ (rootA K Axis.two)) :
    ∃ a b c : K, 𝐮[a, b, c, 0] = x := by
  obtain ⟨y, ⟨a, b, c, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hx
  exact ⟨a, b, c, rfl⟩

theorem exists_u_eq_of_Z {x : G} (hx : x ∈ pull φ (antiUnipotentCenter K)) :
    ∃ b c : K, 𝐮[0, b, c, 0] = x := by
  obtain ⟨y, ⟨b, c, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hx
  exact ⟨b, c, rfl⟩

theorem exists_u_eq_of_U₂ {x : G} (hx : x ∈ pull φ (rootU K Axis.two)) :
    ∃ c : K, 𝐮[0, 0, c, 0] = x := by
  obtain ⟨y, ⟨c, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hx
  exact ⟨c, rfl⟩

omit [CharP K 2] in
theorem w₁_mem : 𝐰₁ ∈ L := (φ.symm _).2

omit [CharP K 2] in
theorem w₂_mem : 𝐰₂ ∈ L := (φ.symm _).2

omit [CharP K 2] in
theorem w₁_inv : 𝐰₁⁻¹ = 𝐰₁ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← coe_mul, ← map_mul, weylElt₁_mul_self, map_one, OneMemClass.coe_one]

omit [CharP K 2] in
theorem w₂_inv : 𝐰₂⁻¹ = 𝐰₂ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← coe_mul, ← map_mul, weylElt₂_mul_self, map_one, OneMemClass.coe_one]

theorem w₁_conj (b c d : K) : 𝐰₁ * 𝐮[0, b, c, d] * 𝐰₁⁻¹ = 𝐮[0, b, d, c] := by
  rw [w₁_inv, ← coe_mul, ← coe_mul, ← map_mul, ← map_mul, weylElt₁_conj]

theorem w₂_conj (a b c : K) : 𝐰₂ * 𝐮[a, b, c, 0] * 𝐰₂⁻¹ = 𝐮[b, a, c, 0] := by
  rw [w₂_inv, ← coe_mul, ← coe_mul, ← map_mul, ← map_mul, weylElt₂_conj]

theorem w₂_conj_inv (a b c : K) : 𝐰₂⁻¹ * 𝐮[a, b, c, 0] * 𝐰₂ = 𝐮[b, a, c, 0] := by
  have := w₂_conj (φ := φ) a b c
  rw [w₂_inv] at this ⊢
  exact this

theorem u_split (a b c : K) : 𝐮[a, b, c, 0] = 𝐮[0, b, c + a * b, 0] * 𝐮[a, 0, 0, 0] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e : uElt (0 : K) b (c + a * b) 0 * uElt a 0 0 0 = uElt a b c 0 := by
    rw [uElt_mul]
    congr 1 <;> first | ring1 | linear_combination (a * b) * h2
  rw [← coe_mul, ← map_mul, e]

omit [CharP K 2] in
theorem w₁_conj_Ja {j : G} (hj : j ∈ pull φ (FullCenterTorus.axisTorus K Axis.one)) :
    𝐰₁ * j * 𝐰₁⁻¹ ∈ pull φ (FullCenterTorus.axisTorus K Axis.one) := by
  obtain ⟨δ, hδ, rfl⟩ := exists_eq_symm_of_mem_pull hj
  rw [w₁_inv, ← coe_mul, ← coe_mul, ← map_mul, ← map_mul]
  exact symm_mem_pull.mpr (weylElt₁_conj_axisTorus hδ)

end Coord

structure OvHyp {G : Type} [Group G] (L : Subgroup G) (K : Type) [Field K] [CharP K 2] (n : ℕ)
    (φ : L ≃* antiSp K) (TG : Subgroup G) (t : G) (M : Subgroup G) : Prop where
  heis : HeisHyp L K n φ TG t
  comp : CompHyp φ t M

namespace OvHyp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G} {M : Subgroup G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐔₁" => pull φ (rootU K Axis.one)
local notation "𝐔₂" => pull φ (rootU K Axis.two)
local notation "𝐀₁" => pull φ (rootA K Axis.one)
local notation "𝐀₂" => pull φ (rootA K Axis.two)
local notation "𝐁₁" => (zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G)
local notation "𝐁₂" => (zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G)
local notation "𝐍₁" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) : Set G)
local notation "𝐍₂" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃₁" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
  Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐃₂" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐉" => pull φ (diagTorus K)
local notation "𝐉ₐ" => pull φ (FullCenterTorus.axisTorus K Axis.one)
set_option quotPrecheck false in
local notation "𝐇" =>
  (M ⊓ centralizer (pull φ (FullCenterTorus.axisTorus K Axis.one) : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₁" => (M ⊔ pull φ (rootA K Axis.one) : Subgroup G)
local notation "𝐮[" a ", " b ", " c ", " d "]" => ((φ.symm (uElt a b c d) : L) : G)
local notation "𝐰₁" => ((φ.symm (weylElt₁ K) : L) : G)

omit [Finite G] [Finite K] in
theorem two (h : OvHyp L K n φ TG t M) : TwoCoreSetup L K n t := h.heis.sec.two

omit [Finite G] [Finite K] in
theorem M_le_D₁ (h : OvHyp L K n φ TG t M) : M ≤ 𝐃₁ := fun _ hm => (h.comp.le_D hm).1

omit [Finite G] [Finite K] in
theorem M_le_D₂ (h : OvHyp L K n φ TG t M) : M ≤ 𝐃₂ := fun _ hm => (h.comp.le_D hm).2

theorem t_mem_N (h : OvHyp L K n φ TG t M) : t ∈ normalizer (M : Set G) :=
  h.comp.t_mem_normalizer h.heis

theorem mem_Z_of_comm (h : OvHyp L K n φ TG t M) {x : G} (hx : x ∈ M) (hxt : x * t = t * x) :
    x ∈ 𝐙 :=
  (h.comp.inf_C h.heis).le ⟨hx, mem_centralizer_singleton_iff.mpr hxt⟩

theorem t_not_mem_M (h : OvHyp L K n φ TG t M) : t ∉ M := fun ht =>
  h.two.t_not_mem (pull_le φ _ (h.mem_Z_of_comm ht rfl))

theorem card_M (h : OvHyp L K n φ TG t M) : Nat.card M = (2 ^ n) ^ 3 := by
  have h1 := (card_sup_zpowers h.two.t_mul_t h.t_mem_N h.t_not_mem_M).1
  rw [h.comp.sup_t, card_D h.heis, h.two.card_K] at h1
  omega

theorem inf_eq_Z (h : OvHyp L K n φ TG t M) {W : Subgroup G} (hWL : W ≤ L) (hZW : 𝐙 ≤ W) :
    M ⊓ W = 𝐙 :=
  le_antisymm (fun _ hx => (h.comp.inf_C h.heis).le ⟨hx.1, h.two.L_le (hWL hx.2)⟩)
    (le_inf h.comp.ZP_le hZW)

theorem comm_M (h : OvHyp L K n φ TG t M) {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    x * y = y * x := by
  have hH := (h.comp.square_map h.heis).1
  rw [← SetLike.mem_coe, ← h.comp.H_mul_U₂ h.heis] at hx hy
  obtain ⟨a, ha, u, hu, rfl⟩ := hx
  obtain ⟨b, hb, v, hv, rfl⟩ := hy
  have hbD := h.comp.le_D (mem_inf.mp hb).1
  have haD := h.comp.le_D (mem_inf.mp ha).1
  have e1 : u * b = b * u := (comm_ZP_of_mem_D h.heis hbD (U₂_le_ZP hu)).symm
  have e2 : v * a = a * v := (comm_ZP_of_mem_D h.heis haD (U₂_le_ZP hv)).symm
  have e3 : u * v = v * u :=
    comm_ZP_of_mem_D h.heis (ZP_le_D h.heis (U₂_le_ZP hu)) (U₂_le_ZP hv)
  have e4 := hH a ha b hb
  calc a * u * (b * v) = a * (u * b) * v := by group
    _ = (a * b) * (u * v) := by rw [e1]; group
    _ = (b * a) * (v * u) := by rw [e4, e3]
    _ = b * (v * a) * u := by rw [e2]; group
    _ = b * v * (a * u) := by group

theorem comm_A₁ (h : OvHyp L K n φ TG t M) {x a : G} (hx : x ∈ 𝐃₁) (ha : a ∈ 𝐀₁) :
    x * a = a * x :=
  (mem_center_map_iff.mp ((center_D₁ h.heis).ge ha)).2 x hx

theorem coe_M₁ (h : OvHyp L K n φ TG t M) :
    ((𝐌₁ : Subgroup G) : Set G) = (M : Set G) * (𝐀₁ : Set G) :=
  coe_mul_of_right_le_normalizer_left M 𝐀₁
    (le_normalizer_of_commute fun _ ha _ hm => (h.comm_A₁ (h.M_le_D₁ hm) ha).symm)

omit [Finite G] [Finite K] in
theorem M₁_le_D₁ (h : OvHyp L K n φ TG t M) : 𝐌₁ ≤ 𝐃₁ := sup_le h.M_le_D₁ (A₁_le_D₁ h.heis)

theorem comm_M₁ (h : OvHyp L K n φ TG t M) {x y : G} (hx : x ∈ 𝐌₁) (hy : y ∈ 𝐌₁) :
    x * y = y * x := by
  rw [← SetLike.mem_coe, h.coe_M₁] at hx hy
  obtain ⟨m, hm, a, ha, rfl⟩ := hx
  obtain ⟨m', hm', a', ha', rfl⟩ := hy
  have e1 := h.comm_M hm hm'
  have e2 : a * m' = m' * a := (h.comm_A₁ (h.M_le_D₁ hm') ha).symm
  have e3 : a' * m = m * a' := (h.comm_A₁ (h.M_le_D₁ hm) ha').symm
  have e4 : a * a' = a' * a := h.comm_A₁ (A₁_le_D₁ h.heis ha) ha'
  calc m * a * (m' * a') = m * (a * m') * a' := by group
    _ = (m * m') * (a * a') := by rw [e2]; group
    _ = (m' * m) * (a' * a) := by rw [e1, e4]
    _ = m' * (m * a') * a := by group
    _ = m' * (a' * m) * a := by rw [e3]
    _ = m' * a' * (m * a) := by group

theorem card_M₁ (h : OvHyp L K n φ TG t M) : Nat.card 𝐌₁ = (2 ^ n) ^ 4 := by
  have h1 := card_sup_mul_card_inf (A := M) (N := 𝐀₁)
    (le_normalizer_of_commute fun _ hm _ ha => h.comm_A₁ (h.M_le_D₁ hm) ha)
  rw [h.inf_eq_Z (pull_le φ _) ZP_le_A₁, h.card_M, card_pull φ (rootA K Axis.one),
    FullCenter.card_rootA, card_pull φ (antiUnipotentCenter K), (card_radicals (K := K)).2.2.2,
    h.two.card_K] at h1
  have hpos : 0 < (2 ^ n) ^ 2 := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1]; ring)

theorem t_not_mem_sup (h : OvHyp L K n φ TG t M) {W : Subgroup G} (hWL : W ≤ L)
    (hWN : W ≤ normalizer (M : Set G)) : t ∉ M ⊔ W := by
  intro ht
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left M W hWN] at ht
  obtain ⟨m, hm, w, hw, hmw⟩ := ht
  have hc : t * w⁻¹ = w⁻¹ * t := h.two.comm (inv_mem (hWL hw))
  have hm' : m = t * w⁻¹ := by rw [← hmw]; group
  have hmt : m * t = t * m := by
    calc m * t = t * w⁻¹ * t := by rw [hm']
      _ = t * (t * w⁻¹) := by rw [mul_assoc, ← hc]
      _ = t * m := by rw [hm']
  exact h.two.t_not_mem (hmw ▸ mul_mem (pull_le φ _ (h.mem_Z_of_comm hm hmt)) (hWL hw))

theorem t_not_mem_M₁ (h : OvHyp L K n φ TG t M) : t ∉ 𝐌₁ :=
  h.t_not_mem_sup (pull_le φ _)
    (le_normalizer_of_commute fun _ ha _ hm => (h.comm_A₁ (h.M_le_D₁ hm) ha).symm)

theorem t_mem_N_M₁ (h : OvHyp L K n φ TG t M) : t ∈ normalizer (𝐌₁ : Set G) :=
  mem_normalizer_of_conj_le fun _ hx => conj_mem_sup
    (fun y hy => (mem_normalizer_iff.mp h.t_mem_N y).mp hy)
    (fun a ha => by rw [h.two.comm (pull_le φ _ ha), mul_inv_cancel_right]; exact ha) hx

theorem M₁_sup_t (h : OvHyp L K n φ TG t M) : 𝐌₁ ⊔ zpowers t = 𝐃₁ := by
  refine le_antisymm (sup_le h.M₁_le_D₁ (zpowers_le.mpr (t_mem_D₁ h.heis))) fun d hd => ?_
  obtain ⟨a, ha, had⟩ := mem_A₁_mul_D h.heis hd
  rw [← h.comp.sup_t] at had
  rw [show d = a * (a⁻¹ * d) by group]
  have hle : M ⊔ zpowers t ≤ 𝐌₁ ⊔ zpowers t := sup_le_sup_right le_sup_left _
  exact mul_mem (mem_sup_left (mem_sup_right ha)) (hle had)

theorem card_D₁ (h : OvHyp L K n φ TG t M) :
    Nat.card 𝐃₁ = 2 * (2 ^ n) ^ 4 ∧ 𝐌₁.relIndex 𝐃₁ = 2 := by
  have h1 := card_sup_zpowers h.two.t_mul_t h.t_mem_N_M₁ h.t_not_mem_M₁
  rw [h.M₁_sup_t, h.card_M₁] at h1
  exact h1

theorem M₁_inf_B₁ (h : OvHyp L K n φ TG t M) : 𝐌₁ ⊓ 𝐁₁ = 𝐀₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right le_sup_right)
  rcases (mem_zpowers_sup_iff h.two.t_mul_t (TwoCoreSetup.comm_pull φ h.two)).mp hx.2 with
    h1 | h1
  · exact h1
  · exfalso
    apply h.t_not_mem_M₁
    rw [show t = (t * x) * x⁻¹ by group]
    exact mul_mem (mem_sup_right h1) (inv_mem hx.1)

theorem mem_A₁_of_comm (h : OvHyp L K n φ TG t M) {x : G} (hx : x ∈ 𝐌₁)
    (hxt : x * t = t * x) : x ∈ 𝐀₁ :=
  h.M₁_inf_B₁.le ⟨hx, h.heis.mem_B₁ (h.M₁_le_D₁ hx) hxt⟩

theorem normal_M₁ (h : OvHyp L K n φ TG t M) : (𝐌₁.subgroupOf 𝐃₁).Normal :=
  (normal_subgroupOf_iff_le_normalizer h.M₁_le_D₁).mpr
    (h.M₁_sup_t ▸ sup_le le_normalizer (zpowers_le.mpr h.t_mem_N_M₁))

theorem eq_M₁ (h : OvHyp L K n φ TG t M) {Y : Subgroup G} (hYD : Y ≤ 𝐃₁)
    (hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) (hY : Nat.card Y = (2 ^ n) ^ 4) : Y = 𝐌₁ := by
  by_cases hle : Y ≤ 𝐌₁
  · exact eq_of_le_of_card_ge hle (by rw [h.card_M₁, hY])
  · exfalso
    obtain ⟨y, hyY, hyM⟩ := Set.not_subset.mp hle
    have hy : t * y ∈ 𝐌₁ := (mem_or_mul_mem h.two.t_mul_t h.t_mem_N_M₁
      (h.M₁_sup_t.ge (hYD hyY))).resolve_left hyM
    have hYA : 𝐌₁ ⊓ Y ≤ 𝐀₁ := by
      rintro x ⟨hxM, hxY⟩
      refine h.mem_A₁_of_comm hxM (mul_right_cancel (b := y) ?_)
      calc x * t * y = x * (t * y) := by group
        _ = t * y * x := h.comm_M₁ hxM hy
        _ = t * (y * x) := by group
        _ = t * (x * y) := by rw [hYc x hxY y hyY]
        _ = t * x * y := by group
    have h1 := card_le_two_mul h.card_D₁.2 hYD
    have h2 : Nat.card (𝐌₁ ⊓ Y : Subgroup G) ≤ (2 ^ n) ^ 3 := by
      have := card_le_of_le hYA
      rwa [card_pull, FullCenter.card_rootA, h.two.card_K] at this
    have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two.two_le
    rw [hY] at h1
    have h3 : 0 < (2 ^ n) ^ 3 := by positivity
    have h4 : (2 ^ n) ^ 4 = 2 ^ n * (2 ^ n) ^ 3 := by ring
    nlinarith

theorem characteristic_M₁ (h : OvHyp L K n φ TG t M) : (𝐌₁.subgroupOf 𝐃₁).Characteristic := by
  rw [characteristic_iff_map_le]
  intro σ
  have hYD : ((𝐌₁.subgroupOf 𝐃₁).map σ.toMonoidHom).map 𝐃₁.subtype ≤ 𝐃₁ := map_subtype_le _
  have hYc : ∀ x ∈ ((𝐌₁.subgroupOf 𝐃₁).map σ.toMonoidHom).map 𝐃₁.subtype,
      ∀ y ∈ ((𝐌₁.subgroupOf 𝐃₁).map σ.toMonoidHom).map 𝐃₁.subtype, x * y = y * x := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hab : a * b = b * a := Subtype.ext (h.comm_M₁ (mem_subgroupOf.mp ha)
      (mem_subgroupOf.mp hb))
    simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, hab]
  have hYcard : Nat.card (((𝐌₁.subgroupOf 𝐃₁).map σ.toMonoidHom).map 𝐃₁.subtype) =
      (2 ^ n) ^ 4 := by
    rw [card_map_of_injective (subtype_injective _),
      card_map_of_injective (f := σ.toMonoidHom) σ.injective,
      Nat.card_congr (subgroupOfEquivOfLe h.M₁_le_D₁).toEquiv, h.card_M₁]
  have hYM := h.eq_M₁ hYD hYc hYcard
  intro x hx
  rw [mem_subgroupOf, ← hYM]
  exact ⟨x, hx, rfl⟩

theorem normalizer_D₁_le (h : OvHyp L K n φ TG t M) :
    normalizer (𝐃₁ : Set G) ≤ normalizer (𝐌₁ : Set G) := by
  intro g hg
  have hYD : 𝐌₁.map (MulAut.conj g).toMonoidHom ≤ 𝐃₁ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hg x).mp (h.M₁_le_D₁ hx)
  have hYc : ∀ x ∈ 𝐌₁.map (MulAut.conj g).toMonoidHom,
      ∀ y ∈ 𝐌₁.map (MulAut.conj g).toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h.comm_M₁ hx hy]
  have hYM := h.eq_M₁ hYD hYc (by rw [card_map_conj, h.card_M₁])
  exact mem_normalizer_of_conj_le fun x hx => hYM ▸ ⟨x, hx, rfl⟩

omit [Finite K] in
theorem w₁_mem_N₁ (h : OvHyp L K n φ TG t M) : 𝐰₁ ∈ 𝐍₁ := by
  rw [h.two.mem_normalizer_zpowers_sup_iff (h.two.L_le (w₁_mem (φ := φ))) (pull_le φ _)]
  refine mem_normalizer_of_conj_le fun a ha => ?_
  obtain ⟨b, c, d, rfl⟩ := exists_u_eq_of_A₁ ha
  rw [w₁_conj]
  exact u_mem_A₁_iff.mpr rfl

theorem w₁_mem_N_M₁ (h : OvHyp L K n φ TG t M) : 𝐰₁ ∈ normalizer (𝐌₁ : Set G) :=
  h.normalizer_D₁_le (le_normalizer_pCore_map h.w₁_mem_N₁)

theorem M₁_inf_Ja (h : OvHyp L K n φ TG t M) : 𝐌₁ ⊓ centralizer (𝐉ₐ : Set G) = 𝐇 := by
  refine le_antisymm (fun x hx => ?_) (inf_le_inf_right _ le_sup_left)
  obtain ⟨hxM, hxc⟩ := mem_inf.mp hx
  refine mem_inf.mpr ⟨?_, hxc⟩
  rw [← SetLike.mem_coe, h.coe_M₁] at hxM
  obtain ⟨m, hm, a, ha, rfl⟩ := hxM
  obtain ⟨b, c, d, rfl⟩ := exists_u_eq_of_A₁ ha
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne (two_lt_card h.heis) (1 : K)
  obtain ⟨δ, -, hδ⟩ := exists_diagTorus (K := K) hr0 (inv_ne_zero hr0)
  have hjJa : ((φ.symm δ : L) : G) ∈ 𝐉ₐ := symm_mem_pull.mpr ⟨r, hr0, hδ⟩
  have hjJ : ((φ.symm δ : L) : G) ∈ 𝐉 := pull_mono φ (FullCenterTorus.axisTorus_le Axis.one) hjJa
  set j : G := ((φ.symm δ : L) : G) with hj
  have hxj : j⁻¹ * (m * 𝐮[0, b, c, d]) * j = m * 𝐮[0, b, c, d] := by
    rw [mul_assoc, ← mem_centralizer_iff.mp hxc j hjJa, inv_mul_cancel_left]
  have hu : j⁻¹ * 𝐮[0, b, c, d] * j = 𝐮[0, b, r ^ 2 * c, r⁻¹ ^ 2 * d] := by
    refine Setup.symm_conj ?_
    rw [diagTorus_conj hr0 (inv_ne_zero hr0) hδ, mul_zero, mul_inv_cancel₀ hr0, one_mul]
  have hm' : j⁻¹ * m * j ∈ M := h.comp.conj_mem hjJ hm
  have key : (j⁻¹ * m * j)⁻¹ * m = 𝐮[0, b, r ^ 2 * c, r⁻¹ ^ 2 * d] * (𝐮[0, b, c, d])⁻¹ := by
    have e : (j⁻¹ * m * j) * 𝐮[0, b, r ^ 2 * c, r⁻¹ ^ 2 * d] = m * 𝐮[0, b, c, d] := by
      rw [← hu, ← hxj]
      group
    calc (j⁻¹ * m * j)⁻¹ * m = (j⁻¹ * m * j)⁻¹ * (m * 𝐮[0, b, c, d]) * (𝐮[0, b, c, d])⁻¹ := by
          group
      _ = (j⁻¹ * m * j)⁻¹ * ((j⁻¹ * m * j) * 𝐮[0, b, r ^ 2 * c, r⁻¹ ^ 2 * d]) *
          (𝐮[0, b, c, d])⁻¹ := by rw [e]
      _ = _ := by group
  have hZ : 𝐮[0, b, r ^ 2 * c, r⁻¹ ^ 2 * d] * (𝐮[0, b, c, d])⁻¹ ∈ 𝐙 := by
    rw [← key, ← h.inf_eq_Z (pull_le φ _) ZP_le_A₁]
    refine mem_inf.mpr ⟨mul_mem (inv_mem hm') hm, ?_⟩
    rw [key, u_inv, u_mul]
    exact u_mem_A₁_iff.mpr (by ring)
  rw [u_inv, u_mul] at hZ
  have hd : (1 + r⁻¹ ^ 2) * d = 0 := by
    have := (u_mem_Z_iff.mp hZ).2
    linear_combination this
  have hr1' : r⁻¹ ≠ 1 := fun e => hr1 (by rw [← inv_inv r, e, inv_one])
  obtain rfl : d = 0 :=
    (mul_eq_zero.mp hd).resolve_left (FullCenterTorus.one_add_ne_zero hr1').2
  exact mul_mem hm (h.comp.ZP_le (u_mem_Z_iff.mpr ⟨rfl, rfl⟩))

theorem w₁_conj_H (h : OvHyp L K n φ TG t M) {x : G} (hx : x ∈ 𝐇) : 𝐰₁ * x * 𝐰₁⁻¹ ∈ 𝐇 := by
  rw [← h.M₁_inf_Ja]
  obtain ⟨hxM, hxc⟩ := mem_inf.mp hx
  refine ⟨(mem_normalizer_iff.mp h.w₁_mem_N_M₁ x).mp (mem_sup_left hxM),
    mem_centralizer_iff.mpr fun j hj => ?_⟩
  have hj' : 𝐰₁⁻¹ * j * 𝐰₁ ∈ 𝐉ₐ := by
    have := w₁_conj_Ja (φ := φ) hj
    rw [w₁_inv] at this ⊢
    exact this
  have e := mem_centralizer_iff.mp hxc _ hj'
  calc j * (𝐰₁ * x * 𝐰₁⁻¹) = 𝐰₁ * ((𝐰₁⁻¹ * j * 𝐰₁) * x) * 𝐰₁⁻¹ := by group
    _ = 𝐰₁ * (x * (𝐰₁⁻¹ * j * 𝐰₁)) * 𝐰₁⁻¹ := by rw [e]
    _ = 𝐰₁ * x * 𝐰₁⁻¹ * j := by group

theorem M_inf_Mw₁ (h : OvHyp L K n φ TG t M) :
    M ⊓ M.map (MulAut.conj 𝐰₁⁻¹).toMonoidHom = 𝐇 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxw⟩ := mem_inf.mp hx
    rw [mem_map_conj_inv_iff] at hxw
    rw [← SetLike.mem_coe, ← h.comp.H_mul_U₂ h.heis] at hxM
    obtain ⟨y, hy, u, hu, rfl⟩ := hxM
    obtain ⟨c, rfl⟩ := exists_u_eq_of_U₂ hu
    have hy' := h.w₁_conj_H hy
    have e : 𝐰₁ * (y * 𝐮[0, 0, c, 0]) * 𝐰₁⁻¹ = (𝐰₁ * y * 𝐰₁⁻¹) * 𝐮[0, 0, 0, c] := by
      rw [← w₁_conj 0 c 0]
      group
    rw [e] at hxw
    have hv : 𝐮[0, 0, 0, c] ∈ M := by
      have := mul_mem (inv_mem (mem_inf.mp hy').1) hxw
      rwa [inv_mul_cancel_left] at this
    have hvZ : 𝐮[0, 0, 0, c] ∈ 𝐙 :=
      (h.inf_eq_Z (pull_le φ _) ZP_le_A₁).le ⟨hv, u_mem_A₁_iff.mpr rfl⟩
    obtain ⟨-, rfl⟩ := u_mem_Z_iff.mp hvZ
    show y * 𝐮[0, 0, 0, 0] ∈ _
    rw [u_zero, mul_one]
    exact hy
  · intro x hx
    exact ⟨(mem_inf.mp hx).1, mem_map_conj_inv_iff.mpr (mem_inf.mp (h.w₁_conj_H hx)).1⟩

theorem mul_Mw₁ (h : OvHyp L K n φ TG t M) :
    (M : Set G) * (M.map (MulAut.conj 𝐰₁⁻¹).toMonoidHom : Set G) = 𝐌₁ := by
  ext x
  constructor
  · rintro ⟨m, hm, y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_map_conj_inv_iff] at hy
    exact mul_mem (mem_sup_left hm) ((mem_normalizer_iff.mp h.w₁_mem_N_M₁ y).mpr (mem_sup_left hy))
  · intro hx
    rw [h.coe_M₁] at hx
    obtain ⟨m, hm, a, ha, rfl⟩ := hx
    obtain ⟨b, c, d, rfl⟩ := exists_u_eq_of_A₁ ha
    refine ⟨m * 𝐮[0, b, c, 0], mul_mem hm (h.comp.ZP_le (u_mem_Z_iff.mpr ⟨rfl, rfl⟩)),
      𝐮[0, 0, 0, d], ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_map_conj_inv_iff, w₁_conj]
      exact h.comp.ZP_le (u_mem_Z_iff.mpr ⟨rfl, rfl⟩)
    · have e : uElt (0 : K) b c 0 * uElt 0 0 0 d = uElt 0 b c d := by
        rw [uElt_mul]
        congr 1 <;> ring
      show m * 𝐮[0, b, c, 0] * 𝐮[0, 0, 0, d] = m * 𝐮[0, b, c, d]
      rw [mul_assoc, ← coe_mul, ← map_mul, e]

theorem sup_Mw₁ (h : OvHyp L K n φ TG t M) :
    M ⊔ M.map (MulAut.conj 𝐰₁⁻¹).toMonoidHom = 𝐌₁ := by
  refine le_antisymm (sup_le le_sup_left fun y hy => ?_) fun x hx => ?_
  · rw [← SetLike.mem_coe, ← h.mul_Mw₁]
    exact ⟨1, one_mem _, y, hy, one_mul y⟩
  · rw [← SetLike.mem_coe, ← h.mul_Mw₁] at hx
    obtain ⟨m, hm, y, hy, rfl⟩ := hx
    exact mul_mem (mem_sup_left hm) (mem_sup_right hy)

section Second

local notation "𝐰₂" => ((φ.symm (weylElt₂ K) : L) : G)
set_option quotPrecheck false in
local notation "𝐌ʷ₂" => (M.map (MulAut.conj ((φ.symm (weylElt₂ K) : L) : G)⁻¹).toMonoidHom :
  Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₂" => (M ⊔ M.map (MulAut.conj ((φ.symm (weylElt₂ K) : L) : G)⁻¹).toMonoidHom :
  Subgroup G)

omit [Finite K] in
theorem w₂_mem_N₂ (h : OvHyp L K n φ TG t M) : 𝐰₂ ∈ 𝐍₂ := by
  rw [h.two.mem_normalizer_zpowers_sup_iff (h.two.L_le (w₂_mem (φ := φ))) (pull_le φ _)]
  refine mem_normalizer_of_conj_le fun a ha => ?_
  obtain ⟨a, b, c, rfl⟩ := exists_u_eq_of_A₂ ha
  rw [w₂_conj]
  exact u_mem_A₂_iff.mpr rfl

omit [Finite G] [Finite K] in
theorem w₂_comm_t (h : OvHyp L K n φ TG t M) : 𝐰₂ * t = t * 𝐰₂ :=
  (h.two.comm (w₂_mem (φ := φ))).symm

omit [Finite G] [Finite K] in
theorem w₂_omega (h : OvHyp L K n φ TG t M) (a b : K) :
    𝐰₂⁻¹ * (t * 𝐮[a, b, 0, 0]) * 𝐰₂ = t * 𝐮[b, a, 0, 0] := by
  have hwt : 𝐰₂⁻¹ * t = t * 𝐰₂⁻¹ := by
    calc 𝐰₂⁻¹ * t = 𝐰₂⁻¹ * (t * 𝐰₂) * 𝐰₂⁻¹ := by group
      _ = 𝐰₂⁻¹ * (𝐰₂ * t) * 𝐰₂⁻¹ := by rw [h.w₂_comm_t]
      _ = t * 𝐰₂⁻¹ := by group
  calc 𝐰₂⁻¹ * (t * 𝐮[a, b, 0, 0]) * 𝐰₂ = (𝐰₂⁻¹ * t) * 𝐮[a, b, 0, 0] * 𝐰₂ := by group
    _ = t * (𝐰₂⁻¹ * 𝐮[a, b, 0, 0] * 𝐰₂) := by rw [hwt]; group
    _ = t * 𝐮[b, a, 0, 0] := by rw [w₂_conj_inv]

omit [Finite G] [Finite K] in
theorem hAct_w₂ (h : OvHyp L K n φ TG t M) {g : G} {x y : K} (hg : HAct φ t g x y 0) :
    HAct φ t (𝐰₂ * g * 𝐰₂⁻¹) y x 0 := by
  rw [hAct_iff] at hg ⊢
  intro a b
  calc 𝐰₂ * g * 𝐰₂⁻¹ * (t * 𝐮[a, b, 0, 0]) * (𝐰₂ * g * 𝐰₂⁻¹)⁻¹ =
        𝐰₂ * (g * (𝐰₂⁻¹ * (t * 𝐮[a, b, 0, 0]) * 𝐰₂) * g⁻¹) * 𝐰₂⁻¹ := by group
    _ = 𝐰₂ * (t * 𝐮[b + x, a + 0 * b + y, 0, 0]) * 𝐰₂⁻¹ := by rw [h.w₂_omega, hg]
    _ = 𝐰₂⁻¹ * (t * 𝐮[b + x, a + 0 * b + y, 0, 0]) * 𝐰₂ := by rw [w₂_inv]
    _ = t * 𝐮[a + y, b + 0 * a + x, 0, 0] := by
        rw [h.w₂_omega]
        congr 4 <;> ring

theorem hAct_of_mem_M (h : OvHyp L K n φ TG t M) {m : G} (hm : m ∈ M) :
    ∃ y : K, HAct φ t m 0 y 0 := by
  obtain ⟨x, y, hxy⟩ := hAct_of_mem_D h.heis.sec (h.M_le_D₂ hm)
  obtain rfl : x = 0 := (h.heis.mem_R_iff (mem_sup_right (h.M_le_D₂ hm)) hxy).mp
    (mem_sup_right (h.M_le_D₁ hm))
  exact ⟨y, hxy⟩

theorem exists_M_hAct (h : OvHyp L K n φ TG t M) (y : K) : ∃ m ∈ M, HAct φ t m 0 y 0 := by
  obtain ⟨m, hm, hmy⟩ := h.comp.exists_kappa_eq h.heis (coordG_mem φ Axis.one y)
  obtain ⟨y', hy'⟩ := h.hAct_of_mem_M (inv_mem hm)
  refine ⟨m⁻¹, inv_mem hm, ?_⟩
  have e1 := (hAct_iff.mp hy') 0 0
  rw [u_zero, mul_one, inv_inv] at e1
  have e2 : m⁻¹ * t * m = t * 𝐮[0, y, 0, 0] := by
    calc m⁻¹ * t * m = t * (t⁻¹ * (m⁻¹ * t * m)) := by group
      _ = t * 𝐮[0, y, 0, 0] := by rw [hmy]; rfl
  have e3 := (u_inj (mul_left_cancel (e1.symm.trans e2))).2.1
  rw [mul_zero, zero_add, zero_add] at e3
  rwa [e3] at hy'

omit [Finite K] in
theorem Mw₂_le_D₂ (h : OvHyp L K n φ TG t M) : 𝐌ʷ₂ ≤ 𝐃₂ := fun y hy =>
  (mem_normalizer_iff.mp (le_normalizer_pCore_map h.w₂_mem_N₂) y).mpr
    (h.M_le_D₂ (mem_map_conj_inv_iff.mp hy))

theorem hAct_of_mem_Mw₂ (h : OvHyp L K n φ TG t M) {x : G} (hx : x ∈ 𝐌ʷ₂) :
    ∃ y : K, HAct φ t x y 0 0 := by
  obtain ⟨y, hy⟩ := h.hAct_of_mem_M (mem_map_conj_inv_iff.mp hx)
  have := h.hAct_w₂ hy
  rw [show 𝐰₂ * (𝐰₂ * x * 𝐰₂⁻¹) * 𝐰₂⁻¹ = 𝐰₂⁻¹⁻¹ * (𝐰₂ * x * 𝐰₂⁻¹) * 𝐰₂⁻¹ by rw [inv_inv],
    show 𝐰₂⁻¹⁻¹ * (𝐰₂ * x * 𝐰₂⁻¹) * 𝐰₂⁻¹ = (𝐰₂⁻¹ * 𝐰₂) * x * (𝐰₂⁻¹ * 𝐰₂) by
      rw [w₂_inv, w₂_inv]; group,
    inv_mul_cancel, one_mul, mul_one] at this
  exact ⟨y, this⟩

theorem M_inf_Mw₂ (h : OvHyp L K n φ TG t M) : M ⊓ 𝐌ʷ₂ = 𝐔₂ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxw⟩ := mem_inf.mp hx
    obtain ⟨y, hy⟩ := h.hAct_of_mem_M hxM
    obtain ⟨y', hy'⟩ := h.hAct_of_mem_Mw₂ hxw
    obtain ⟨-, rfl, -⟩ := HAct.unique h.two hy hy'
    have hxB : x ∈ 𝐁₂ := mem_B₂_of_hAct h.heis (SecondHyp.D_le_N (h.M_le_D₂ hxM)) hy
    have hxZ := h.mem_Z_of_comm hxM (mem_centralizer_singleton_iff.mp (h.heis.sec.B_le_C hxB))
    have hmM : 𝐰₂ * x * 𝐰₂⁻¹ ∈ M := mem_map_conj_inv_iff.mp hxw
    have hmB : 𝐰₂ * x * 𝐰₂⁻¹ ∈ 𝐁₂ := (mem_normalizer_iff.mp h.w₂_mem_N₂ x).mp hxB
    have hmZ := h.mem_Z_of_comm hmM (mem_centralizer_singleton_iff.mp (h.heis.sec.B_le_C hmB))
    obtain ⟨b, c, rfl⟩ := exists_u_eq_of_Z hxZ
    rw [w₂_conj] at hmZ
    obtain ⟨rfl, -⟩ := u_mem_Z_iff.mp hmZ
    exact u_mem_U₂_iff.mpr ⟨rfl, rfl, rfl⟩
  · intro u hu
    refine mem_inf.mpr ⟨h.comp.ZP_le (U₂_le_ZP hu), mem_map_conj_inv_iff.mpr ?_⟩
    obtain ⟨c, rfl⟩ := exists_u_eq_of_U₂ hu
    rw [w₂_conj]
    exact h.comp.ZP_le (U₂_le_ZP hu)

theorem swap_Mw₂ (h : OvHyp L K n φ TG t M) {y : G} (hy : y ∈ 𝐌ʷ₂) {m : G} (hm : m ∈ M) :
    ∃ m' ∈ M, ∃ y' ∈ 𝐌ʷ₂, y * m = m' * y' := by
  have hc : ⁅y, m⁆ ∈ 𝐀₂ := by
    have := commutator_mem_commutator (h.Mw₂_le_D₂ hy) (h.M_le_D₂ hm)
    rwa [(part_three h.heis).1] at this
  obtain ⟨a, b, c, hc'⟩ := exists_u_eq_of_A₂ hc
  have hz : 𝐮[0, b, c + a * b, 0] ∈ M := h.comp.ZP_le (u_mem_Z_iff.mpr ⟨rfl, rfl⟩)
  have hz' : 𝐮[a, 0, 0, 0] ∈ 𝐌ʷ₂ := by
    rw [mem_map_conj_inv_iff, w₂_conj]
    exact h.comp.ZP_le (u_mem_Z_iff.mpr ⟨rfl, rfl⟩)
  have hu : 𝐮[a, 0, 0, 0] * m * (𝐮[a, 0, 0, 0])⁻¹ * m⁻¹ ∈ 𝐔₂ := by
    have := (mem_upperCentralSeries_two_iff.mp ((upper_D₂ h.heis).ge
      (u_mem_A₂_iff.mpr rfl : 𝐮[a, 0, 0, 0] ∈ 𝐀₂))).2 m (h.M_le_D₂ hm)
    rwa [center_D₂ h.heis] at this
  refine ⟨𝐮[0, b, c + a * b, 0] * (𝐮[a, 0, 0, 0] * m * (𝐮[a, 0, 0, 0])⁻¹ * m⁻¹) * m,
    mul_mem (mul_mem hz (h.comp.ZP_le (U₂_le_ZP hu))) hm, 𝐮[a, 0, 0, 0] * y, mul_mem hz' hy, ?_⟩
  have e1 : y * m = ⁅y, m⁆ * m * y := by rw [commutatorElement_def]; group
  rw [e1, ← hc', u_split]
  group

theorem coe_M₂ (h : OvHyp L K n φ TG t M) :
    ((𝐌₂ : Subgroup G) : Set G) = (M : Set G) * (𝐌ʷ₂ : Set G) :=
  coe_sup_eq_mul_of_swap fun _ hy _ hm => h.swap_Mw₂ hy hm

omit [Finite K] in
theorem M₂_le_D₂ (h : OvHyp L K n φ TG t M) : 𝐌₂ ≤ 𝐃₂ := sup_le h.M_le_D₂ h.Mw₂_le_D₂

omit [Finite G] [Finite K] in
theorem A₂_le_M₂ (h : OvHyp L K n φ TG t M) : 𝐀₂ ≤ 𝐌₂ := by
  intro x hx
  obtain ⟨a, b, c, rfl⟩ := exists_u_eq_of_A₂ hx
  rw [u_split]
  refine mul_mem (mem_sup_left (h.comp.ZP_le (u_mem_Z_iff.mpr ⟨rfl, rfl⟩)))
    (mem_sup_right (mem_map_conj_inv_iff.mpr ?_))
  rw [w₂_conj]
  exact h.comp.ZP_le (u_mem_Z_iff.mpr ⟨rfl, rfl⟩)

theorem M₂_inf_B₂ (h : OvHyp L K n φ TG t M) : 𝐌₂ ⊓ 𝐁₂ = 𝐀₂ := by
  refine le_antisymm (fun x hx => ?_) (le_inf h.A₂_le_M₂ le_sup_right)
  obtain ⟨hxM, hxB⟩ := mem_inf.mp hx
  rw [← SetLike.mem_coe, h.coe_M₂] at hxM
  obtain ⟨m, hm, y, hy, rfl⟩ := hxM
  obtain ⟨ym, hym⟩ := h.hAct_of_mem_M hm
  obtain ⟨yy, hyy⟩ := h.hAct_of_mem_Mw₂ hy
  obtain ⟨e1, e2, -⟩ := HAct.unique h.two (hym.mul hyy) (hAct_of_mem_B h.heis.sec hxB)
  obtain rfl : yy = 0 := by simpa using e1
  obtain rfl : ym = 0 := by simpa using e2
  have hmZ : m ∈ 𝐙 := h.mem_Z_of_comm hm (mem_centralizer_singleton_iff.mp (h.heis.sec.B_le_C
    (mem_B₂_of_hAct h.heis (SecondHyp.D_le_N (h.M_le_D₂ hm)) hym)))
  have hyB : y ∈ 𝐁₂ := mem_B₂_of_hAct h.heis (SecondHyp.D_le_N (h.Mw₂_le_D₂ hy)) hyy
  have hmB : 𝐰₂ * y * 𝐰₂⁻¹ ∈ 𝐁₂ := (mem_normalizer_iff.mp h.w₂_mem_N₂ y).mp hyB
  have hmZ' := h.mem_Z_of_comm (mem_map_conj_inv_iff.mp hy)
    (mem_centralizer_singleton_iff.mp (h.heis.sec.B_le_C hmB))
  obtain ⟨b, c, hbc⟩ := exists_u_eq_of_Z hmZ'
  have hy' : y = 𝐰₂⁻¹ * 𝐮[0, b, c, 0] * 𝐰₂ := by rw [hbc]; group
  rw [w₂_conj_inv] at hy'
  rw [hy']
  exact mul_mem (ZP_le_A₂ hmZ) (u_mem_A₂_iff.mpr rfl)

theorem t_not_mem_M₂ (h : OvHyp L K n φ TG t M) : t ∉ 𝐌₂ := fun ht =>
  h.two.t_not_mem (pull_le φ _ (h.M₂_inf_B₂.le ⟨ht, mem_sup_left (mem_zpowers t)⟩))

theorem t_mem_N_M₂ (h : OvHyp L K n φ TG t M) : t ∈ normalizer (𝐌₂ : Set G) := by
  refine mem_normalizer_of_conj_le fun x hx => conj_mem_sup
    (fun y hy => (mem_normalizer_iff.mp h.t_mem_N y).mp hy) (fun y hy => ?_) hx
  rw [mem_map_conj_inv_iff] at hy ⊢
  have e : 𝐰₂ * (t * y * t⁻¹) * 𝐰₂⁻¹ = t * (𝐰₂ * y * 𝐰₂⁻¹) * t⁻¹ := by
    calc 𝐰₂ * (t * y * t⁻¹) * 𝐰₂⁻¹ = (𝐰₂ * t) * y * (𝐰₂ * t)⁻¹ := by group
      _ = (t * 𝐰₂) * y * (t * 𝐰₂)⁻¹ := by rw [h.w₂_comm_t]
      _ = t * (𝐰₂ * y * 𝐰₂⁻¹) * t⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.mp h.t_mem_N _).mp hy

theorem M₂_sup_t (h : OvHyp L K n φ TG t M) : 𝐌₂ ⊔ zpowers t = 𝐃₂ := by
  refine le_antisymm (sup_le h.M₂_le_D₂ (zpowers_le.mpr (t_mem_D₂ h.heis))) fun d hd => ?_
  obtain ⟨x, y, hxy⟩ := hAct_of_mem_D h.heis.sec hd
  obtain ⟨m, hm, hmy⟩ := h.exists_M_hAct y
  obtain ⟨m', hm', hm'x⟩ := h.exists_M_hAct x
  have hy'M : 𝐰₂⁻¹ * m' * 𝐰₂ ∈ 𝐌ʷ₂ := mem_map_conj_inv_iff.mpr (by group; exact hm')
  have hy'act : HAct φ t (𝐰₂⁻¹ * m' * 𝐰₂) x 0 0 := by
    have := h.hAct_w₂ hm'x
    rw [w₂_inv] at this ⊢
    exact this
  have hp : m * (𝐰₂⁻¹ * m' * 𝐰₂) ∈ 𝐌₂ := mul_mem (mem_sup_left hm) (mem_sup_right hy'M)
  have hpact : HAct φ t (m * (𝐰₂⁻¹ * m' * 𝐰₂)) x y 0 :=
    (hmy.mul hy'act).congr (by ring) (by ring) (by ring)
  have hb := inv_mul_mem_B h.heis.sec (SecondHyp.D_le_N hd)
    (SecondHyp.D_le_N (h.M₂_le_D₂ hp)) hxy hpact
  have hBle : 𝐁₂ ≤ 𝐌₂ ⊔ zpowers t := sup_le le_sup_right (h.A₂_le_M₂.trans le_sup_left)
  rw [show d = m * (𝐰₂⁻¹ * m' * 𝐰₂) * ((m * (𝐰₂⁻¹ * m' * 𝐰₂))⁻¹ * d) by group]
  exact mul_mem (mem_sup_left hp) (hBle hb)

theorem card_D₂ (h : OvHyp L K n φ TG t M) : Nat.card 𝐃₂ = 2 * (2 ^ n) ^ 5 := by
  obtain ⟨-, -, -, -, -, hcard, -⟩ := h.heis.sec.exists_mulEquiv
  have h1 := card_eq_card_quotient_mul_card_subgroup (𝐁₂.subgroupOf 𝐃₂)
  rw [hcard, Nat.card_congr (subgroupOfEquivOfLe h.heis.sec.B_le_D).toEquiv,
    card_B (φ := φ) h.two, h.two.card_K] at h1
  rw [h1]
  ring

theorem card_M₂ (h : OvHyp L K n φ TG t M) :
    Nat.card 𝐌₂ = (2 ^ n) ^ 5 ∧ 𝐌₂.relIndex 𝐃₂ = 2 := by
  have h1 := card_sup_zpowers h.two.t_mul_t h.t_mem_N_M₂ h.t_not_mem_M₂
  rw [h.M₂_sup_t, h.card_D₂] at h1
  exact ⟨by omega, h1.2⟩

theorem normal_M₂ (h : OvHyp L K n φ TG t M) : (𝐌₂.subgroupOf 𝐃₂).Normal :=
  (normal_subgroupOf_iff_le_normalizer h.M₂_le_D₂).mpr
    (h.M₂_sup_t ▸ sup_le le_normalizer (zpowers_le.mpr h.t_mem_N_M₂))

theorem M₁_inf_M₂ (h : OvHyp L K n φ TG t M) : 𝐌₁ ⊓ 𝐌₂ = M := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left le_sup_left)
  obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
  have hxD : x ∈ M ⊔ zpowers t :=
    h.comp.sup_t.ge (mem_inf.mpr ⟨h.M₁_le_D₁ hx1, h.M₂_le_D₂ hx2⟩)
  rcases mem_or_mul_mem h.two.t_mul_t h.t_mem_N hxD with h1 | h1
  · exact h1
  · exfalso
    apply h.t_not_mem_M₁
    rw [show t = (t * x) * x⁻¹ by group]
    exact mul_mem (mem_sup_left h1) (inv_mem hx1)

end Second

end OvHyp

end OneAxisOvergroup

end CFSG.LocalAnalysis.SymplecticFourStandard
