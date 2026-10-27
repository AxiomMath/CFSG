module

public import CFSG.Quasithin.EmptyFaithful.S152FinSmall

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S152Fin

abbrev Wr : Type := Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)

instance instDecidableEqWr : DecidableEq Wr := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    ⟨fun h => RegularWreathProduct.ext h.1 h.2, fun h => by subst h; exact ⟨rfl, rfl⟩⟩

instance instFintypeWr : Fintype Wr :=
  Fintype.ofEquiv _ (RegularWreathProduct.equivProd _ _).symm

theorem card_Wr : Nat.card Wr = 72 := by
  rw [RegularWreathProduct.card]
  have h1 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm]; simp [Nat.factorial]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]; simp
  rw [h1, h2]
  norm_num

theorem multZMod2_cases (q : Multiplicative (ZMod 2)) : q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  revert q; decide

def xWr : Wr := ⟨fun q => if q = 1 then Equiv.swap 0 1 else 1, Multiplicative.ofAdd 1⟩

theorem xWr_sq : xWr ^ 2 = ⟨fun _ => Equiv.swap 0 1, 1⟩ := by
  rw [pow_two]
  apply RegularWreathProduct.ext
  · funext q
    rcases multZMod2_cases q with rfl | rfl
    · simp [xWr, RegularWreathProduct.mul_left]
    · simp [xWr, RegularWreathProduct.mul_left]
  · show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) = 1
    decide

theorem xWr_sq_ne : xWr ^ 2 ≠ 1 := by
  intro h
  rw [xWr_sq] at h
  have := congrArg (fun z : Wr => z.left 1 0) h
  simp at this

theorem xWr_four : xWr ^ 4 = 1 := by
  have : xWr ^ 4 = (xWr ^ 2) ^ 2 := by rw [← pow_mul]
  rw [this, xWr_sq, pow_two]
  apply RegularWreathProduct.ext
  · funext q
    simp [RegularWreathProduct.mul_left]
  · show (1 : Multiplicative (ZMod 2)) * 1 = 1
    simp

theorem card_le_four_of_exp_two {X : Type*} [Group X] [Finite X] (hcard : Nat.card X = 72)
    (x : X) (hx2 : x ^ 2 ≠ 1) (hx4 : x ^ 4 = 1)
    {E : Subgroup X} (hE2 : ∀ a ∈ E, a ^ 2 = 1) : Nat.card E ≤ 4 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 E := by
    intro y
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hE2 y y.2
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  by_contra hlt
  push Not at hlt
  have hdvd : Nat.card E ∣ 72 := hcard ▸ E.card_subgroup_dvd_card
  rw [hn] at hdvd hlt
  have hn3 : n = 3 := by
    have h1 : 3 ≤ n := by
      by_contra h
      push Not at h
      interval_cases n <;> simp at hlt
    have h2' : n ≤ 3 := by
      by_contra h
      push Not at h
      have : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 h
      have : 16 ∣ 72 := dvd_trans (by simpa using this) hdvd
      omega
    omega
  subst hn3
  have hidx : E.index = 9 := by
    have := E.card_mul_index
    rw [hn, hcard] at this
    omega
  let SE : Sylow 2 X := hpg.toSylow (by rw [hidx]; decide)
  have hxpg : IsPGroup 2 (Subgroup.zpowers x) := by
    have hod : orderOf x ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one hx4
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hod
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, hk]
  obtain ⟨S', hS'⟩ := hxpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S' SE
  have hmem : g * x * g⁻¹ ∈ E := by
    have hxS : x ∈ (S' : Subgroup X) := hS' (Subgroup.mem_zpowers x)
    have h3 : g * x * g⁻¹ ∈ ((g • S' : Sylow 2 X) : Subgroup X) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.conj_inv_apply, mul_assoc] using hxS
    rw [hg] at h3
    exact h3
  have := hE2 _ hmem
  apply hx2
  have e : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := conj_pow
  rw [e] at this
  have : x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
  rw [this, ‹g * x ^ 2 * g⁻¹ = 1›]
  group

variable {G : Type} [Group G]

theorem relIndex_centralizer_le_two {M V D : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hV : IsElemAbelian 2 V)
    (hsmall : IsSmallGroup152 ↥(autOn M V)) (hD : D ≤ M) (hDab : IsElemAbelian 2 D) :
    (Subgroup.centralizer (V : Set G)).relIndex D ≤ 2 := by
  have hDN : D ≤ Subgroup.normalizer (V : Set G) := hD.trans hMV
  have hle : autOn D V ≤ autOn M V := autOn_le_autOn V hD
  have h1 := card_autOn_eq_relIndex hDN
  have hab := isElemAbelian2_autOn hV hDab hDN
  have hE : Nat.card ((autOn D V).subgroupOf (autOn M V)) ≤ 2 := by
    refine card_le_two_of_isSmallGroup152 hsmall ?_ ?_
    · intro a ha b hb
      apply Subtype.ext
      exact hab.1 _ ha _ hb
    · intro a ha
      apply Subtype.ext
      exact hab.2 _ ha
  have h2 : Nat.card ((autOn D V).subgroupOf (autOn M V)) = Nat.card (autOn D V) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [Subgroup.inf_relIndex_left] at h1
  omega

theorem relIndex_pCoreOf_le_four {H E : Subgroup G}
    (hH : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)))
    (hEH : E ≤ H) (hE : IsElemAbelian 2 E) : (pCoreOf 2 H).relIndex E ≤ 4 := by
  obtain ⟨ι⟩ := hH
  let f : ↥E →* OTwoQuot H :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)).comp (Subgroup.inclusion hEH)
  have hker : f.ker = (pCoreOf 2 H).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) (Subgroup.inclusion hEH e) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨y, hy, hye⟩
      have : y = Subgroup.inclusion hEH e := Subtype.ext hye
      rwa [this] at hy
  have hidx : (pCoreOf 2 H).relIndex E = Nat.card f.range := by
    rw [← Subgroup.index_ker f, hker]
    rfl
  have hE2 : ∀ e : ↥E, e ^ 2 = 1 := fun e =>
    Subtype.ext (by simpa using F7.isElemAbelian_pow_eq_one hE e.2)
  have hsq : ∀ a ∈ f.range.map ι.toMonoidHom, a ^ 2 = 1 := by
    rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
    show ι (f e) ^ 2 = 1
    rw [← map_pow, ← map_pow, hE2 e, map_one, map_one]
  have hc := card_le_four_of_exp_two (X := Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2))
    card_Wr xWr xWr_sq_ne xWr_four hsq
  rw [Subgroup.card_map_of_injective ι.injective] at hc
  rw [hidx]
  exact hc

end S152Fin

end CFSG.Quasithin
