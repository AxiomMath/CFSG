module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Z2D8
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Facts
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421Setting

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace Insp15418

variable {Γ : Type*} [Group Γ]

theorem exists_odd_subgroup_of_central [Finite Γ] {Y N : Subgroup Γ} (hNY : N ≤ Y)
    (hN2 : IsPGroup 2 N) (hidx : ¬ 2 ∣ N.relIndex Y)
    (hcent : ∀ n ∈ N, ∀ y ∈ Y, n * y = y * n) :
    ∃ K₁ : Subgroup Γ, K₁ ≤ Y ∧ Odd (Nat.card K₁) ∧ ∀ y ∈ Y, Odd (orderOf y) → y ∈ K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(N.subgroupOf Y) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNY).symm
  set P : Sylow 2 ↥Y := IsPGroup.toSylow (P := N.subgroupOf Y) hP2 hidx with hPdef
  have hPc : ((P : Subgroup ↥Y) : Subgroup ↥Y) = N.subgroupOf Y := rfl
  have hP : Subgroup.normalizer ((P : Subgroup ↥Y) : Set ↥Y) ≤
      Subgroup.centralizer ((P : Subgroup ↥Y) : Set ↥Y) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ N.subgroupOf Y := hh
    rw [Subgroup.mem_subgroupOf] at hh'
    exact Subtype.ext (hcent _ hh' _ g.2)
  set τ := MonoidHom.transferSylow P hP with hτ
  refine ⟨τ.ker.map Y.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have h := MonoidHom.not_dvd_card_ker_transferSylow P hP
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  · intro y hy ho
    refine ⟨⟨y, hy⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    have h1 : orderOf (τ ⟨y, hy⟩) ∣ orderOf (⟨y, hy⟩ : ↥Y) := orderOf_map_dvd τ _
    obtain ⟨k, hk⟩ := P.isPGroup' (τ ⟨y, hy⟩)
    have h2 : orderOf (τ ⟨y, hy⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have ho' : Odd (orderOf (⟨y, hy⟩ : ↥Y)) := by rwa [Subgroup.orderOf_mk]
    have hcop : Nat.Coprime (2 ^ k) (orderOf (⟨y, hy⟩ : ↥Y)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr ho')
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)

theorem pow_conj_eq {y l c : Γ} (h : y * l * y⁻¹ = c * l) (hc : y * c = c * y) (j : ℕ) :
    y ^ j * l * (y ^ j)⁻¹ = c ^ j * l := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hcj : y * c ^ j = c ^ j * y := (Commute.pow_right hc j).eq
    calc y ^ (j + 1) * l * (y ^ (j + 1))⁻¹ = y * (y ^ j * l * (y ^ j)⁻¹) * y⁻¹ := by group
      _ = y * (c ^ j * l) * y⁻¹ := by rw [ih]
      _ = c ^ j * (y * l * y⁻¹) := by rw [← mul_assoc y, hcj]; group
      _ = c ^ (j + 1) * l := by rw [h]; group

end Insp15418

namespace InspectionData15418

variable {G : Type} [Group G] [Finite G] {I G₁ G₂ S T Z : Subgroup G}
  (d : InspectionData15418 I G₁ G₂ S T Z)
include d

theorem eq_one_of_odd_of_mem {K : Subgroup ↥I} (hK : CFSG.IsComponent K) (hKn : K.Normal)
    {c : ↥I} (hcK : c ∈ K) (hcO : c ∈ CFSG.pPrimeCore 3 ↥I) (ho : Odd (orderOf c)) : c = 1 := by
  obtain ⟨a, m₀, hm₀, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := ↥I)).ne'
  have hcomm : ∀ x ∈ K, ∀ y ∈ CFSG.pPrimeCore 3 ↥I, x * y = y * x := by
    intro x hx y hy
    have hc' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (d.commutator_pPrimeCore_eq_bot hK) hx
    exact (Subgroup.mem_centralizer_iff.mp hc' y hy).symm
  let Q : Subgroup ↥I :=
    { carrier := {x | x ∈ K ∧ x ∈ CFSG.pPrimeCore 3 ↥I ∧ x ^ m₀ = 1}
      mul_mem' := by
        rintro x y ⟨hxK, hxO, hx⟩ ⟨hyK, hyO, hy⟩
        refine ⟨K.mul_mem hxK hyK, (CFSG.pPrimeCore 3 ↥I).mul_mem hxO hyO, ?_⟩
        rw [(Commute.mul_pow (hcomm x hxK y hyO)), hx, hy, one_mul]
      one_mem' := ⟨K.one_mem, (CFSG.pPrimeCore 3 ↥I).one_mem, one_pow _⟩
      inv_mem' := by
        rintro x ⟨hxK, hxO, hx⟩
        exact ⟨K.inv_mem hxK, (CFSG.pPrimeCore 3 ↥I).inv_mem hxO, by rw [inv_pow, hx, inv_one]⟩ }
  have hQn : Q.Normal := by
    constructor
    rintro x ⟨hxK, hxO, hx⟩ g
    refine ⟨hKn.conj_mem x hxK g, (inferInstance : (CFSG.pPrimeCore 3 ↥I).Normal).conj_mem x hxO g,
      ?_⟩
    rw [conj_pow, hx]
    group
  have hQodd : Odd (Nat.card Q) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hq' : (q : ↥I) ^ m₀ = 1 := q.2.2.2
    have : orderOf q ∣ m₀ := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hq'
    rw [hq] at this
    exact (Nat.not_even_iff_odd.mpr hm₀) (even_iff_two_dvd.mpr this)
  have hQbot : Q ≤ fusionOddCore ↥I := le_sSup ⟨hQn, hQodd⟩
  have hO : fusionOddCore ↥I = ⊥ := by
    have h := d.oddCoreIn_eq_bot
    rw [oddCoreIn] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ I.subtype_injective).mp h
  have hcQ : c ∈ Q := by
    refine ⟨hcK, hcO, orderOf_dvd_iff_pow_eq_one.mp ?_⟩
    have h1 : orderOf c ∣ 2 ^ a * m₀ := hcard ▸ orderOf_dvd_natCard c
    exact (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr ho)).dvd_of_dvd_mul_left h1
  have := hQbot hcQ
  rw [hO, Subgroup.mem_bot] at this
  exact this

theorem commute_of_odd {K : Subgroup ↥I} (hK : CFSG.IsComponent K) (hKn : K.Normal) {y l : ↥I}
    (hyK : y ∈ K) (hlK : l ∈ K) (ho : Odd (orderOf y))
    (h : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) l =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) l * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) y) :
    y * l = l * y := by
  set c := y * l * y⁻¹ * l⁻¹ with hcdef
  have hcK : c ∈ K := K.mul_mem (K.mul_mem (K.mul_mem hyK hlK) (K.inv_mem hyK)) (K.inv_mem hlK)
  have hcO : c ∈ CFSG.pPrimeCore 3 ↥I := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) (y * l * y⁻¹ * l⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hcy : y * c = c * y := by
    have hc' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (d.commutator_pPrimeCore_eq_bot hK) hyK
    exact (Subgroup.mem_centralizer_iff.mp hc' c hcO).symm
  have hyl : y * l * y⁻¹ = c * l := by rw [hcdef]; group
  have hpow := Insp15418.pow_conj_eq hyl hcy (orderOf y)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hpow
  have hc1 : c ^ orderOf y = 1 := by
    have := congrArg (· * l⁻¹) hpow
    simpa using this.symm
  have hco : Odd (orderOf c) := ho.of_dvd_nat (orderOf_dvd_of_pow_eq_one hc1)
  have := d.eq_one_of_odd_of_mem hK hKn hcK hcO hco
  rw [hcdef] at this
  calc y * l = (y * l * y⁻¹ * l⁻¹) * l * y := by group
    _ = l * y := by rw [this, one_mul]

omit d in
theorem mem_normalizer_map_subtype {Y : Subgroup ↥I} {k : ↥I}
    (hk : k ∈ Subgroup.normalizer (Y : Set ↥I)) :
    (k : G) ∈ Subgroup.normalizer ((Y.map I.subtype : Subgroup G) : Set G) := by
  refine L15421.mem_normalizer_of_conj_mem ?_
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨k * y * k⁻¹, (Subgroup.mem_normalizer_iff.mp hk y).mp hy, rfl⟩

theorem false_of_caseNine (hN : ComponentIndexTwo15418) (hInv : InvolutionCentralizer15418)
    (hc : ¬ CharTwo I)
    (hD : Nonempty ((↥I ⧸ CFSG.pPrimeCore 3 ↥I) ≃* Equiv.Perm (Fin 7)) ∨
      F6.IsHatSym 7 (↥I ⧸ CFSG.pPrimeCore 3 ↥I) ∨
      ∃ p : ℕ, p.Prime ∧ (p % 24 = 5 ∨ p % 24 = 19) ∧
        F6.IsL2FieldExtCat p (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) with hπ
  obtain ⟨K, hK⟩ := d.exists_isComponent hc
  have hKc := d.isComponent_map_mk hK
  have hidx : (K.map π).index = 2 := by
    refine hN _ ?_ _ hKc
    rcases hD with h | h | ⟨p, -, -, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨p, h⟩))
  have hKn : K.Normal := d.normal_of_index_two hK hidx
  have hZI : ∀ {z : G}, z ∈ Z → z ∈ I := fun hz => d.S_le (d.le hz)
  have hcommO : ∀ k ∈ K, ∀ m ∈ CFSG.pPrimeCore 3 ↥I, k * m = m * k := by
    intro k hk m hm
    have hc' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (d.commutator_pPrimeCore_eq_bot hK) hk
    exact (Subgroup.mem_centralizer_iff.mp hc' m hm).symm
  obtain ⟨z, hzZ, hz1, hzK⟩ : ∃ z : ↥I, (z : G) ∈ Z ∧ z ≠ 1 ∧ π z ∈ K.map π := by
    let f : ↥Z → (↥I ⧸ CFSG.pPrimeCore 3 ↥I) ⧸ K.map π := fun w =>
      ((π ⟨w, hZI w.2⟩ : ↥I ⧸ CFSG.pPrimeCore 3 ↥I) : (↥I ⧸ CFSG.pPrimeCore 3 ↥I) ⧸ K.map π)
    have hlt : Nat.card ((↥I ⧸ CFSG.pPrimeCore 3 ↥I) ⧸ K.map π) < Nat.card ↥Z := by
      rw [← Subgroup.index_eq_card, hidx, d.card]
      norm_num
    have hninj : ¬ Function.Injective f := fun hinj =>
      absurd (Nat.card_le_card_of_injective f hinj) (not_le.mpr hlt)
    obtain ⟨a, b, hfab, hab⟩ := Function.not_injective_iff.mp hninj
    refine ⟨(⟨a, hZI a.2⟩ : ↥I)⁻¹ * ⟨b, hZI b.2⟩, ?_, ?_, ?_⟩
    · simpa using Z.mul_mem (Z.inv_mem a.2) b.2
    · intro h
      apply hab
      rw [inv_mul_eq_one] at h
      have h' := congrArg (fun w : ↥I => (w : G)) h
      exact Subtype.ext h'
    · have := QuotientGroup.eq.mp hfab
      simpa [map_mul, map_inv] using this
  set x := π z with hx
  have hx1 : x ≠ 1 := by
    intro h
    exact hz1 (d.eq_of_mk_eq hK hzZ (by simp) (by rw [← hx, h, map_one]))
  have hx2 : x ^ 2 = 1 := by
    rw [hx, ← map_pow]
    have : z ^ 2 = 1 := Subtype.ext (d.sq_eq_one _ hzZ)
    rw [this, map_one]
  have hD' : Nonempty ((↥I ⧸ CFSG.pPrimeCore 3 ↥I) ≃* Equiv.Perm (Fin 7)) ∨
      F6.IsHatSym 7 (↥I ⧸ CFSG.pPrimeCore 3 ↥I) ∨
      ∃ p : ℕ, 5 ≤ p ∧ F6.IsL2FieldExtCat p (↥I ⧸ CFSG.pPrimeCore 3 ↥I) := by
    rcases hD with h | h | ⟨p, -, hp24, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨p, by omega, h⟩)
  have hY := hInv _ hD' (K.map π) hKc x hzK hx2 hx1
  set Ys := oddCoreIn ((K.map π) ⊓
    Subgroup.centralizer ({x} : Set (↥I ⧸ CFSG.pPrimeCore 3 ↥I))) with hYs
  have hYsle : Ys ≤ (K.map π) ⊓ Subgroup.centralizer ({x} : Set (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) :=
    oddCoreIn_le _
  have hYsN : (K.map π) ⊓ Subgroup.centralizer ({x} : Set (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) ≤
      Subgroup.normalizer (Ys : Set (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) := le_normalizer_oddCoreIn _
  have hYsodd : Odd (Nat.card Ys) := odd_card_oddCoreIn _
  obtain ⟨l, hlK, hlx⟩ := hzK
  have hn : l⁻¹ * z ∈ CFSG.pPrimeCore 3 ↥I := by
    rw [← QuotientGroup.eq_one_iff]
    change π (l⁻¹ * z) = 1
    rw [map_mul, map_inv, hlx, ← hx, inv_mul_cancel]
  have hzl : ∀ k ∈ K, (k * z = z * k ↔ k * l = l * k) := by
    intro k hk
    have hkn := hcommO k hk _ hn
    have hln := hcommO l hlK _ hn
    set n := l⁻¹ * z with hndef
    have hz : z = l * n := by rw [hndef]; group
    constructor
    · intro h
      rw [hz] at h
      have h2 : k * l * n = l * k * n := by
        calc k * l * n = k * (l * n) := mul_assoc _ _ _
          _ = l * n * k := h
          _ = l * (n * k) := mul_assoc _ _ _
          _ = l * (k * n) := by rw [hkn]
          _ = l * k * n := (mul_assoc _ _ _).symm
      exact mul_right_cancel h2
    · intro h
      rw [hz]
      calc k * (l * n) = k * l * n := (mul_assoc _ _ _).symm
        _ = l * k * n := by rw [h]
        _ = l * (k * n) := mul_assoc _ _ _
        _ = l * (n * k) := by rw [hkn]
        _ = l * n * k := (mul_assoc _ _ _).symm
  set Yt := K ⊓ Ys.comap π with hYt
  set N₀ := K ⊓ CFSG.pPrimeCore 3 ↥I with hN₀
  have hN₀Yt : N₀ ≤ Yt := by
    rintro c ⟨hcK, hcO⟩
    refine ⟨hcK, ?_⟩
    change π c ∈ Ys
    have h1 : π c = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hcO
    rw [h1]
    exact Ys.one_mem
  have hN₀2 : IsPGroup 2 ↥N₀ := by
    intro c
    obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
    refine ⟨b, ?_⟩
    have hc' : (c : ↥I) ^ 2 ^ b ∈ N₀ := N₀.pow_mem c.2 _
    have h2b : (2 ^ b : ℕ) ≠ 0 := by positivity
    have ho : Odd (orderOf ((c : ↥I) ^ 2 ^ b)) := by
      rw [orderOf_pow' _ h2b, Subgroup.orderOf_coe, hbm, Nat.gcd_mul_right_left,
        Nat.mul_div_cancel_left _ (by positivity)]
      exact hm
    have := d.eq_one_of_odd_of_mem hK hKn hc'.1 hc'.2 ho
    exact Subtype.ext (by simpa using this)
  have hmap : Yt.map π = Ys := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_right) fun y hy => ?_
    obtain ⟨k, hk, rfl⟩ := (hYsle hy).1
    exact ⟨k, ⟨hk, hy⟩, rfl⟩
  have hidxN : ¬ 2 ∣ N₀.relIndex Yt := by
    have h1 : N₀ ⊓ Yt = π.ker ⊓ Yt := by
      rw [hπ, QuotientGroup.ker_mk']
      ext c
      exact ⟨fun ⟨⟨_, hcO⟩, hcY⟩ => ⟨hcO, hcY⟩, fun ⟨hcO, hcY⟩ => ⟨⟨hcY.1, hcO⟩, hcY⟩⟩
    rw [← Subgroup.inf_relIndex_right, h1, Subgroup.inf_relIndex_right, Subgroup.relIndex_ker, hmap]
    exact hYsodd.not_two_dvd_nat
  have hcentN : ∀ n ∈ N₀, ∀ y ∈ Yt, n * y = y * n := fun n hn y hy =>
    (hcommO y hy.1 n hn.2).symm
  obtain ⟨K₁, -, hK₁odd, hK₁⟩ :=
    Insp15418.exists_odd_subgroup_of_central hN₀Yt hN₀2 hidxN hcentN
  have hYl : ∀ y ∈ Yt, Odd (orderOf y) → y * l = l * y := by
    intro y hy ho
    refine d.commute_of_odd hK hKn hy.1 hlK ho ?_
    have hyc := Subgroup.mem_centralizer_singleton_iff.mp (hYsle hy.2).2
    rw [hlx]
    exact hyc
  set K₀ := oTwoUpper Yt with hK₀
  have hK₀K₁ : K₀ ≤ K₁ := (Subgroup.closure_le _).mpr fun y hy => hK₁ y hy.1 hy.2
  have hK₀odd : Odd (Nat.card K₀) := hK₁odd.of_dvd_nat (Subgroup.card_dvd_of_le hK₀K₁)
  have hK₀l : K₀ ≤ Subgroup.centralizer ({l} : Set ↥I) :=
    (Subgroup.closure_le _).mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hYl y hy.1 hy.2)
  have hK₀K : K₀ ≤ K := (oTwoUpper_le Yt).trans inf_le_left
  have hNK₀ : ∀ k ∈ K, k * l = l * k → k ∈ Subgroup.normalizer (K₀ : Set ↥I) := by
    intro k hk hkl
    refine normalizer_le_normalizer_oTwoUpper Yt (L15421.mem_normalizer_of_conj_mem ?_)
    intro y hy
    refine ⟨K.mul_mem (K.mul_mem hk hy.1) (K.inv_mem hk), ?_⟩
    have hπk : π k ∈ (K.map π) ⊓ Subgroup.centralizer
        ({x} : Set (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) := by
      refine ⟨⟨k, hk, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : π k * π l = π l * π k := by rw [← map_mul, ← map_mul, hkl]
      rw [hlx] at h1
      exact h1
    have := (Subgroup.mem_normalizer_iff.mp (hYsN hπk) (π y)).mp hy.2
    change π (k * y * k⁻¹) ∈ Ys
    rw [map_mul, map_mul, map_inv]
    exact this
  obtain ⟨⟨ys, hys⟩, hys1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hY
  obtain ⟨y₀, hy₀K, hy₀⟩ := (hYsle hys).1
  obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y₀).ne'
  have h2b : (2 ^ b : ℕ) ≠ 0 := by positivity
  have hy₁o : Odd (orderOf (y₀ ^ 2 ^ b)) := by
    rw [orderOf_pow' _ h2b, hbm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hy₁Yt : y₀ ^ 2 ^ b ∈ Yt := by
    refine ⟨K.pow_mem hy₀K _, ?_⟩
    change π (y₀ ^ 2 ^ b) ∈ Ys
    rw [map_pow, hy₀]
    exact Ys.pow_mem hys _
  have hy₁1 : y₀ ^ 2 ^ b ≠ 1 := by
    intro h
    have h1 : ys ^ 2 ^ b = 1 := by rw [← hy₀, ← map_pow, h, map_one]
    have hyso : Odd (orderOf ys) := by
      refine hYsodd.of_dvd_nat ?_
      have := orderOf_dvd_natCard (⟨ys, hys⟩ : Ys)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ b) (orderOf ys) :=
      Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hyso)
    have : orderOf ys = 1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) dvd_rfl
    exact hys1 (Subtype.ext (orderOf_eq_one_iff.mp this))
  have hy₁K₀ : y₀ ^ 2 ^ b ∈ K₀ := mem_oTwoUpper_of_odd hy₁Yt hy₁o
  set X := K₀.map I.subtype with hX
  set H := (K.map I.subtype) ⊓ Subgroup.centralizer ({(z : G)} : Set G) with hH
  have hCz := d.charTwo_centralizer (z : G) hzZ (fun h => hz1 (Subtype.ext h))
  have hHle : H ≤ I ⊓ Subgroup.centralizer ({(z : G)} : Set G) :=
    inf_le_inf_right _ (Subgroup.map_subtype_le K)
  have hHn : (H.subgroupOf (I ⊓ Subgroup.centralizer ({(z : G)} : Set G))).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨⟨n', hn', hnn⟩, hnz⟩ := hn
    refine ⟨⟨⟨(g : G), g.2.1⟩ * n' * ⟨(g : G), g.2.1⟩⁻¹,
      hKn.conj_mem n' hn' ⟨(g : G), g.2.1⟩, ?_⟩, ?_⟩
    · have hnn' : (n' : G) = n := hnn
      simp [hnn']
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2.2 hnz) (Subgroup.inv_mem _ g.2.2)
  have hHc : CharTwo H := CharTwo.of_normal hCz hHle hHn
  have hXH : X ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨y, hK₀K hy, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := (hzl y (hK₀K hy)).mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hK₀l hy))
    exact congrArg Subtype.val h1
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rintro _ ⟨⟨k, hk, rfl⟩, hkz⟩
    have hkz' : k * z = z * k :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hkz)
    exact mem_normalizer_map_subtype (hNK₀ k hk ((hzl k hk).mp hkz'))
  have hXodd : Odd (Nat.card X) := by
    rwa [hX, Subgroup.card_map_of_injective I.subtype_injective]
  have hXbot := hHc.eq_bot_of_odd_card hXH hHX hXodd
  have hmem : ((y₀ ^ 2 ^ b : ↥I) : G) ∈ X := ⟨_, hy₁K₀, rfl⟩
  rw [hXbot, Subgroup.mem_bot] at hmem
  exact hy₁1 (Subtype.ext hmem)

end InspectionData15418

end CFSG.Quasithin.EmptyFaithfulMultiple
