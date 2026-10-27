module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModD

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.C13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_one_of_conj_odd {Γ : Type*} [Group Γ] {g u c : Γ} {m k : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hck : c ^ 2 ^ k = 1) (hgc : g * c = c * g) (h : g * u * g⁻¹ = c * u) :
    c = 1 := by
  have hpow : ∀ j : ℕ, g ^ j * u * (g ^ j)⁻¹ = c ^ j * u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcj : g * c ^ j * g⁻¹ = c ^ j := by
        rw [(Commute.pow_right hgc j).eq]; group
      calc g ^ (j + 1) * u * (g ^ (j + 1))⁻¹ = g * (g ^ j * u * (g ^ j)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = (g * c ^ j * g⁻¹) * (g * u * g⁻¹) := by rw [ih]; group
        _ = c ^ (j + 1) * u := by rw [hcj, h, pow_succ, mul_assoc]
  have h1 : c ^ m = 1 := by
    have h2 := hpow m
    rw [hgm, inv_one, one_mul, mul_one] at h2
    calc c ^ m = c ^ m * u * u⁻¹ := by group
      _ = 1 := by rw [← h2, mul_inv_cancel]
  have h2 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
  have hodd : Odd (orderOf c) := Odd.of_dvd_nat hm h2
  have : orderOf c = 1 :=
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)).eq_one_of_dvd h3
  exact orderOf_eq_one_iff.mp this

theorem comm_mem_of_odd {X Z : Subgroup G} (hXZ : X ≤ Subgroup.normalizer (Z : Set G)) {g u : G}
    (hg : g ∈ X) (hu : u ∈ X) {m k : ℕ} (hm : Odd m) (hgm : g ^ m = 1)
    (hck : (g * u * g⁻¹ * u⁻¹) ^ 2 ^ k = 1)
    (hc : g * (g * u * g⁻¹ * u⁻¹) * g⁻¹ * (g * u * g⁻¹ * u⁻¹)⁻¹ ∈ Z) :
    g * u * g⁻¹ * u⁻¹ ∈ Z := by
  have hN : (Z.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXZ
  have hcX : g * u * g⁻¹ * u⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem (X.mul_mem hg hu) (X.inv_mem hg)) (X.inv_mem hu)
  let π : ↥X →* ↥X ⧸ Z.subgroupOf X := QuotientGroup.mk' _
  let g' : ↥X := ⟨g, hg⟩
  let u' : ↥X := ⟨u, hu⟩
  let c' : ↥X := ⟨g * u * g⁻¹ * u⁻¹, hcX⟩
  have hgm' : π g' ^ m = 1 := by
    rw [← map_pow]
    have : g' ^ m = 1 := Subtype.ext (by simpa [g'] using hgm)
    rw [this, map_one]
  have hck' : π c' ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : c' ^ 2 ^ k = 1 := Subtype.ext (by simpa [c'] using hck)
    rw [this, map_one]
  have hgc' : π g' * π c' = π c' * π g' := by
    have h0 : g' * c' * g'⁻¹ * c'⁻¹ ∈ Z.subgroupOf X := hc
    have h1 : π (g' * c' * g'⁻¹ * c'⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h0
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π g' * π c' = (π g' * π c' * (π g')⁻¹ * (π c')⁻¹) * (π c' * π g') := by group
      _ = π c' * π g' := by rw [h1, one_mul]
  have hconj : π g' * π u' * (π g')⁻¹ = π c' * π u' := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [g', u', c', Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have key := eq_one_of_conj_odd hm hgm' hck' hgc' hconj
  exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf X) c').mp key

theorem le_normalizer_of_conj {X N : Subgroup G} (h : ∀ g ∈ X, ∀ x ∈ N, g * x * g⁻¹ ∈ N) :
    X ≤ Subgroup.normalizer (N : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (X.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem comm_oTwoRes_mem_of_central [Finite G] {X Q Z : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQX : Q ≤ X) (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hZQ : Z ≤ Q)
    (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hcen : ∀ U' U : Subgroup G, IsChiefStep X Q U' U → Z ≤ U' → IsCentralStep X U' U) :
    ∀ l ∈ oTwoRes X, ∀ q ∈ Q, l * q * l⁻¹ * q⁻¹ ∈ Z := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
  have hPZ : Z ∈ {U : Subgroup G | IsNormalIn X Q U ∧ Z ≤ U ∧
      ∀ l ∈ oTwoRes X, ∀ u ∈ U, l * u * l⁻¹ * u⁻¹ ∈ Z} :=
    ⟨⟨hZQ, fun g hg x hx => conj_mem_of_normalizes hXZ hg hx⟩, le_rfl,
      fun l hl u hu => Z.mul_mem (conj_mem_of_normalizes hXZ (oTwoRes_le X hl) hu) (Z.inv_mem hu)⟩
  obtain ⟨U', -, hU'max⟩ := Set.toFinite _ |>.exists_le_maximal hPZ
  obtain ⟨⟨hU'Q, hU'n⟩, hZU', hU'L⟩ := hU'max.1
  by_cases hU'eq : U' = Q
  · rw [← hU'eq]; exact hU'L
  exfalso
  have hlt : U' < Q := lt_of_le_of_ne hU'Q hU'eq
  have hQmem : Q ∈ {K : Subgroup G | IsNormalIn X Q K ∧ U' < K} :=
    ⟨⟨le_rfl, fun g hg x hx => conj_mem_of_normalizes hXQ hg hx⟩, hlt⟩
  obtain ⟨U, -, hUmin⟩ := Set.toFinite _ |>.exists_le_minimal hQmem
  obtain ⟨hUn, hU'U⟩ := hUmin.1
  have hstep : IsChiefStep X Q U' U := by
    refine ⟨hUn, ⟨hU'Q, hU'n⟩, hU'U, fun K hK hU'K hKU => ?_⟩
    by_cases h : K = U'
    · exact Or.inl h
    · exact Or.inr (le_antisymm hKU (hUmin.2 ⟨hK, lt_of_le_of_ne hU'K (Ne.symm h)⟩ hKU))
  have hc := hcen U' U hstep hZU'
  obtain ⟨C, hC, -, -⟩ := exists_centralizer_quotient hXZ (le_normalizer_of_conj hUn.2)
  have hLC : oTwoRes X ≤ C := by
    refine (Subgroup.closure_le C).mpr ?_
    rintro g ⟨hgX, m, hm, hgm⟩
    refine (hC g).mpr ⟨hgX, fun u hu => ?_⟩
    have hcU' : g * u * g⁻¹ * u⁻¹ ∈ U' := hc g hgX u hu
    have hgL : g ∈ oTwoRes X := Subgroup.subset_closure ⟨hgX, m, hm, hgm⟩
    obtain ⟨k, hk⟩ := hQ ⟨_, hU'Q hcU'⟩
    have hck : (g * u * g⁻¹ * u⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 := comm_mem_of_odd hXZ hgX (hQX (hUn.1 hu)) hm hgm hck (hU'L g hgL _ hcU')
    have e : ⁅u, g⁆ = (g * u * g⁻¹ * u⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact Z.inv_mem h1
  have hPU : U ∈ {U : Subgroup G | IsNormalIn X Q U ∧ Z ≤ U ∧
      ∀ l ∈ oTwoRes X, ∀ u ∈ U, l * u * l⁻¹ * u⁻¹ ∈ Z} := by
    refine ⟨hUn, hZU'.trans hU'U.le, fun l hl u hu => ?_⟩
    have h1 := ((hC l).mp (hLC hl)).2 u hu
    have e : l * u * l⁻¹ * u⁻¹ = ⁅u, l⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact Z.inv_mem h1
  exact absurd (hU'max.2 hPU hU'U.le) (not_le_of_gt hU'U)

theorem inf_centralizer_oTwoRes_eq_bot [Finite G] {X Q : Subgroup G} (hQX : Q ≤ X)
    (hQ : IsPGroup 2 Q) (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hc : centerOf X = ⊥) :
    Q ⊓ Subgroup.centralizer (oTwoRes X : Set G) = ⊥ := by
  by_contra h
  apply inf_centralizer_ne_bot_of_oTwoRes hQX hQ hXQ h
  rw [eq_bot_iff, ← hc]
  exact fun g hg => ⟨hQX hg.1, hg.2⟩

theorem sq_eq_one_of_comm {L Q Z : Subgroup G}
    (hcomm : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ * q⁻¹ ∈ Z) (hZc : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z)
    (hZ2 : ∀ z ∈ Z, z * z = 1) (hbot : Q ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ∀ q ∈ Q, q * q = 1 := by
  intro q hq
  have hmem : q * q ∈ Q ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨Q.mul_mem hq hq, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hzZ : l * q * l⁻¹ * q⁻¹ ∈ Z := hcomm l hl q hq
    have h1 : l * q * l⁻¹ = (l * q * l⁻¹ * q⁻¹) * q := by group
    have h2 : l * (q * q) * l⁻¹ = q * q := by
      calc l * (q * q) * l⁻¹ = (l * q * l⁻¹) * (l * q * l⁻¹) := by group
        _ = (l * q * l⁻¹ * q⁻¹) * (q * (l * q * l⁻¹ * q⁻¹)) * q := by rw [h1]; group
        _ = (l * q * l⁻¹ * q⁻¹) * ((l * q * l⁻¹ * q⁻¹) * q) * q := by rw [← hZc _ hzZ q hq]
        _ = ((l * q * l⁻¹ * q⁻¹) * (l * q * l⁻¹ * q⁻¹)) * (q * q) := by group
        _ = q * q := by rw [hZ2 _ hzZ, one_mul]
    calc l * (q * q) = l * (q * q) * l⁻¹ * l := by group
      _ = q * q * l := by rw [h2]
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem comm_of_sq_eq_one {Q : Subgroup G} (h : ∀ q ∈ Q, q * q = 1) :
    ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
  intro a ha b hb
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (h _ (Q.mul_mem ha hb))).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

theorem pCoreOf_eq_of_comm [Finite G] {X S Z : Subgroup G} (D : Dict5 X S Z)
    (hZQ : Z ≤ pCoreOf 2 X) (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hZX : X ≤ Subgroup.normalizer (Z : Set G))
    (hcomm : ∀ l ∈ oTwoRes X, ∀ q ∈ pCoreOf 2 X, l * q * l⁻¹ * q⁻¹ ∈ Z)
    (hab : ∀ a ∈ pCoreOf 2 X, ∀ b ∈ pCoreOf 2 X, a * b = b * a)
    (hbot : pCoreOf 2 X ⊓ Subgroup.centralizer (oTwoRes X : Set G) = ⊥) :
    pCoreOf 2 X = Z := by
  refine le_antisymm (fun q hq => ?_) hZQ
  have hfZ : ∀ l ∈ oTwoRes X, l * q * l⁻¹ * q⁻¹ ∈ Z := fun l hl => hcomm l hl q hq
  have hfcoc : ∀ l ∈ oTwoRes X, ∀ l' ∈ oTwoRes X,
      (l * l') * q * (l * l')⁻¹ * q⁻¹ =
        (l * q * l⁻¹ * q⁻¹) * (l * (l' * q * l'⁻¹ * q⁻¹) * l⁻¹) := by
    intro l hl l' hl'
    have h1 : l * (l' * q * l'⁻¹ * q⁻¹) * l⁻¹ ∈ Z :=
      conj_mem_of_normalizes hZX (oTwoRes_le X hl) (hfZ l' hl')
    rw [hZab _ (hfZ l hl) _ h1]
    group
  have hfker : ∀ t ∈ oTwoRes X, t ∈ pCoreOf 2 X → t * q * t⁻¹ * q⁻¹ = 1 := by
    intro t _ htQ
    rw [hab t htQ q hq]
    group
  obtain ⟨z, hzZ, hz⟩ := D.exists_principal (fun g => g * q * g⁻¹ * q⁻¹) hfZ hfcoc hfker
  have hmC : z⁻¹ * q ∈ Subgroup.centralizer (oTwoRes X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : h * q * h⁻¹ * q⁻¹ = h * z * h⁻¹ * z⁻¹ := hz h hh
    have e : h * q * h⁻¹ = (h * z * h⁻¹ * z⁻¹) * q := by
      calc h * q * h⁻¹ = (h * q * h⁻¹ * q⁻¹) * q := by group
        _ = _ := by rw [h1]
    calc h * (z⁻¹ * q) = (h * z⁻¹ * h⁻¹) * (h * q * h⁻¹) * h := by group
      _ = (h * z⁻¹ * h⁻¹) * ((h * z * h⁻¹ * z⁻¹) * q) * h := by rw [e]
      _ = (z⁻¹ * q) * h := by group
  have hm : z⁻¹ * q ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (oTwoRes X : Set G) :=
    ⟨(pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem (hZQ hzZ)) hq, hmC⟩
  rw [hbot, Subgroup.mem_bot] at hm
  rw [← inv_mul_eq_one.mp hm]
  exact hzZ

end CFSG.Quasithin.F53.Stellmacher.S43.Even.C13
