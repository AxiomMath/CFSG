module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27B
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27P

public section

namespace CFSG.Quasithin.H13.Ch4.T425C27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.SBc17

variable {G : Type} [Group G]

theorem map_eq_one_iff {K : Subgroup G} {S : Type*} [Group S] {α : ↥K →* S}
    (hker : α.ker = CFSG.pCore 2 ↥K) (k : ↥K) : α k = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
  rw [← MonoidHom.mem_ker, hker, C124.pCoreOf_eq_map_pCore]
  constructor
  · intro hk
    exact ⟨k, hk, rfl⟩
  · rintro ⟨y, hy, hye⟩
    rwa [Subtype.ext hye] at hy

theorem alt_commute {K R M V : Subgroup G} (hR : R ≤ Subgroup.normalizer (K : Set G))
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hD : K ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 K) {n : ℕ}
    {α : ↥K →* alternatingGroup (Fin n)} (hker : α.ker = CFSG.pCore 2 ↥K) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (V : Set G)) {σ : Equiv.Perm (Fin n)}
    (hrel : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹)
    (hMK : autOn (M ⊓ K) V = autOn K V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V)))
    {a : G} (haM : a ∈ M ⊓ K) :
    ((α ⟨a, haM.2⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ =
      σ * ((α ⟨a, haM.2⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
  have haK : a ∈ K := haM.2
  have haV : a ∈ Subgroup.normalizer (V : Set G) := hKV haK
  have hmem : conjAct V ⟨a, haV⟩ ∈ autOn (M ⊓ K) V := mem_autOn_iff'.mpr ⟨⟨a, haV⟩, haM, rfl⟩
  rw [hMK] at hmem
  have hcomm : conjAct V ⟨t, htV⟩ * conjAct V ⟨a, haV⟩ = conjAct V ⟨a, haV⟩ * conjAct V ⟨t, htV⟩ :=
    Subgroup.mem_centralizer_iff.mp hmem.2 _ (mem_autOn_iff'.mpr ⟨⟨t, htV⟩, htR, rfl⟩)
  have hta : t * a⁻¹ * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hR htR) a⁻¹).mp (K.inv_mem haK)
  have hw : a * (t * a⁻¹ * t⁻¹) ∈ K := K.mul_mem haK hta
  have hwC : a * (t * a⁻¹ * t⁻¹) ∈ Subgroup.centralizer (V : Set G) := by
    have e : (⟨a * (t * a⁻¹ * t⁻¹), hKV hw⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨a, haV⟩ * (⟨t, htV⟩ * ⟨a, haV⟩⁻¹ * ⟨t, htV⟩⁻¹) := rfl
    refine (conjAct_eq_one_iff' (V := V) ⟨a * (t * a⁻¹ * t⁻¹), hKV hw⟩).mp ?_
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc conjAct V ⟨a, haV⟩ * (conjAct V ⟨t, htV⟩ * (conjAct V ⟨a, haV⟩)⁻¹ *
          (conjAct V ⟨t, htV⟩)⁻¹) = (conjAct V ⟨a, haV⟩ * conjAct V ⟨t, htV⟩) *
            (conjAct V ⟨a, haV⟩)⁻¹ * (conjAct V ⟨t, htV⟩)⁻¹ := by group
      _ = (conjAct V ⟨t, htV⟩ * conjAct V ⟨a, haV⟩) * (conjAct V ⟨a, haV⟩)⁻¹ *
            (conjAct V ⟨t, htV⟩)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  have hα1 : α ⟨a * (t * a⁻¹ * t⁻¹), hw⟩ = 1 := (map_eq_one_iff hker _).mpr (hD ⟨hw, hwC⟩)
  have hsplit : (⟨a * (t * a⁻¹ * t⁻¹), hw⟩ : ↥K) = ⟨a, haK⟩ * ⟨t * a⁻¹ * t⁻¹, hta⟩ := rfl
  rw [hsplit, map_mul] at hα1
  have hrel' := hrel a⁻¹ (K.inv_mem haK) hta
  have hinv : (α ⟨a⁻¹, K.inv_mem haK⟩ : alternatingGroup (Fin n)) = (α ⟨a, haK⟩)⁻¹ := by
    rw [show (⟨a⁻¹, K.inv_mem haK⟩ : ↥K) = (⟨a, haK⟩ : ↥K)⁻¹ from rfl, map_inv]
  rw [hinv] at hrel'
  have h1 := congrArg (fun z : alternatingGroup (Fin n) => (z : Equiv.Perm (Fin n))) hα1
  simp only [Subgroup.coe_mul, Subgroup.coe_one] at h1
  rw [hrel', Subgroup.coe_inv] at h1
  set c : Equiv.Perm (Fin n) := (α ⟨a, haK⟩ : Equiv.Perm (Fin n))
  calc c * σ = (c * (σ * c⁻¹ * σ⁻¹)) * σ * c := by group
    _ = σ * c := by rw [h1]; group

theorem two_le_pRank_three_of_cycles {n : ℕ} {x y : Equiv.Perm (Fin n)}
    (hxs : Equiv.Perm.sign x = 1) (hys : Equiv.Perm.sign y = 1) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) {i : Fin n} (hxi : x i = i)
    (hyi : y i ≠ i) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine A3Facts.two_le_pRank_of_gens (x := ⟨x, hxs⟩) (y := ⟨y, hys⟩) (Subtype.ext hx3)
    (Subtype.ext hy3) (Subtype.ext hxy) (fun h => hx1 (congrArg Subtype.val h)) fun k hk => ?_
  apply hyi
  have h1 : (x ^ k) i = i := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hxi k
  have h2 : x ^ k = y := by simpa using congrArg Subtype.val hk
  rw [← h2]
  exact h1

theorem two_le_pRank_alt {n : ℕ} (h6 : 6 ≤ n) (h8 : n ≤ 8) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) := by
  interval_cases n
  all_goals
    exact two_le_pRank_three_of_cycles (x := List.formPerm [0, 1, 2])
      (y := List.formPerm [3, 4, 5]) (i := 3) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

variable [Finite G]

namespace Ctx

variable {H R M K J : Subgroup G} (c : Ctx H R M K J) (hC27 : ASC27Statement G)
include c hC27

theorem false_of_alt (h : C27Alt H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) : False := by
  obtain ⟨⟨n, α, hn5, hn8, -, ⟨hα, hker, -⟩, t, htR, htV, -, -, σ, hσ, hrel⟩, hMK⟩ := h
  have hs := c.star hC27
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : e z ∈ Subgroup.center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w]
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega),
      Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact e.injective (h1.trans (map_one e).symm)
  have hD := (hs.inf_centralizer_eq hZ).le
  set f : ↥J →* alternatingGroup (Fin n) := α.comp (Subgroup.inclusion c.J_le_K) with hf
  have hcomm : ∀ j : ↥J, ((f j : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ =
      σ * ((f j : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := fun j =>
    alt_commute c.norm hs.K_le_normalizer_V hD hker htR htV hrel hMK (c.J_le j.2)
  have hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card f.range → r = 2 ∨ r = 3 ∨ (r = 5 ∧ 7 ≤ n) := by
    intro r hr hrd
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hrd
    obtain ⟨j, hj⟩ := MonoidHom.mem_range.mp y.2
    by_contra hne
    push Not at hne
    have hr5 : n < r + 2 := by
      have h5 := hr.five_le_of_ne_two_of_ne_three hne.1 hne.2.1
      have h6 : r ≠ 6 := by
        rintro rfl
        norm_num at hr
      by_cases hr5 : r = 5
      · have := hne.2.2 hr5
        omega
      · omega
    have hpow : ((f j : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ^ r = 1 := by
      have h1 : y ^ r = 1 := by
        rw [← hy]
        exact pow_orderOf_eq_one y
      have h2 : (f j) ^ r = 1 := by
        rw [hj]
        exact congrArg Subtype.val h1
      exact congrArg Subtype.val h2
    have h1 := eq_one_of_commute_swap hr hne.1 hr5 hσ hpow (hcomm j)
    have hy1 : y = 1 := Subtype.ext (by rw [← hj]; exact Subtype.ext h1)
    rw [hy1, orderOf_one] at hy
    exact hr.one_lt.ne hy
  have hsolv : Group.IsSolvable f.range → Group.IsSolvable J := by
    intro hR'
    refine isSolvable_of_ker f.rangeRestrict ?_
    rw [MonoidHom.ker_rangeRestrict]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥f.ker := by
      intro z
      have hzO := (map_eq_one_iff hker _).mp (show f (z : ↥J) = 1 from z.2)
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) ⟨_, hzO⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
    have : Group.IsNilpotent ↥f.ker := hp.isNilpotent
    infer_instance
  rcases Nat.lt_or_ge n 7 with hn7 | hn7
  · apply c.nonsolv
    refine hsolv (isSolvable_of_prime_dvd Nat.prime_two Nat.prime_three fun r hr hrd => ?_)
    rcases hprime r hr hrd with h | h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
    · omega
  · have h3 : 3 ∣ Nat.card f.range := by
      by_contra h3
      apply c.nonsolv
      refine hsolv (isSolvable_of_prime_dvd Nat.prime_two Nat.prime_five fun r hr hrd => ?_)
      rcases hprime r hr hrd with h | h | ⟨h, -⟩
      · exact Or.inl h
      · exact absurd (h ▸ hrd) h3
      · exact Or.inr h
    have hle := c.rank 3 Nat.prime_three (by norm_num) (h3.trans (Subgroup.card_range_dvd f))
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hge := two_le_pRank_of_surjective α hα (p := 3) (by norm_num)
      (two_le_pRank_alt (by omega) hn8)
    omega

end Ctx

end CFSG.Quasithin.H13.Ch4.T425C27
