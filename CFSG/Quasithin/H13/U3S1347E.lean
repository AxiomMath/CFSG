module

public import CFSG.Quasithin.H13.U3S1347D

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem mem_pCoreOf_of_mem_oTwoRes {H : Subgroup G}
    (hq : quasithinO2QuotientIso H (Perm (Fin 3))) {x : G} (hx : x ∈ oTwoRes H) {k : ℕ}
    (hxk : x ^ 2 ^ k = 1) : x ∈ pCoreOf 2 H := by
  obtain ⟨φ, -, hker⟩ := hq
  have hA : oTwoRes H ≤ ((Perm.sign.comp φ).ker).map H.subtype := by
    refine (closure_le _).2 fun y hy => ?_
    obtain ⟨hyH, m, hm, hym⟩ := hy
    refine ⟨⟨y, hyH⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
    have hy1 : (⟨y, hyH⟩ : ↥H) ^ m = 1 := Subtype.ext (by simpa using hym)
    have h1 : Perm.sign (φ ⟨y, hyH⟩) ^ m = 1 := by
      rw [← map_pow, ← map_pow, hy1, map_one, map_one]
    obtain ⟨j, rfl⟩ := hm
    rwa [pow_succ, pow_mul, Int.units_sq, one_pow, one_mul] at h1
  obtain ⟨⟨y, hyH⟩, hy, rfl⟩ := hA hx
  rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
  have h3 : ∀ σ : Perm (Fin 3), Perm.sign σ = 1 → σ ^ 3 = 1 := by decide
  have hy2 : (⟨y, hyH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
  have h1 : φ ⟨y, hyH⟩ = 1 :=
    eq_one_of_two_pow_of_cube (by rw [← map_pow, hy2, map_one]) (h3 _ hy)
  exact (map_eq_one_iff_of_ker hker _).1 h1

theorem s1347_inf_T_le_centralizer (S : A6.Setting134 G T L V) {H₁ H₂ H : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) (hH : H ≤ H₁ ⊔ H₂) (hq : quasithinO2QuotientIso H (Perm (Fin 3)))
    (hN : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H : Set G)) :
    oTwoRes H ⊓ T ≤ centralizer (v0Of T H₁ H₂ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := s1347_reduced S hH₀
  intro x hx
  obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨x, hx.2⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hxQ := mem_pCoreOf_of_mem_oTwoRes hq hx.1 hxk
  have hle : oTwoRes H ⊓ pCoreOf 2 H ≤ pCoreOf 2 (oTwoRes H) :=
    le_pCoreOf_of_le_normalizer inf_le_left (fun g hg => mem_normalizer_inf_of
      (le_normalizer hg) (le_normalizer_pCoreOf 2 H (oTwoRes_le H hg)))
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  have hO := pCoreOf_le_pCoreOf ((oTwoRes_le H).trans hH) hN
  exact pCoreOf_le_centralizer_of_reduced' hred (hO (hle ⟨hx.1, hxQ⟩))

theorem s1347_exists_gen (S : A6.Setting134 G T L V) {H₁ H₂ H : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) (hH : H ≤ H₁ ⊔ H₂) (hTH : T ≤ H) (h3 : T.relIndex H = 3)
    (hq : quasithinO2QuotientIso H (Perm (Fin 3)))
    (hidx : Nat.card ↥(quasithinOmegaOneCenter T) = 2 * Nat.card ↥(cZ T H))
    (hN : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H : Set G)) :
    ∃ y ∈ oTwoRes H, y ^ 3 = 1 ∧ y ∉ T ∧ ∀ k ∈ oTwoRes H, ∃ j : ℕ, j < 3 ∧
      ∀ v ∈ v0Of T H₁ H₂, k * v * k⁻¹ = y ^ j * v * (y ^ j)⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := s1347_reduced S hH₀
  have hsyl := A5.isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨y, hyK, hy3, hyT⟩ : ∃ y ∈ oTwoRes H, y ^ 3 = 1 ∧ y ∉ T := by
    by_contra hc
    push Not at hc
    apply s1347_not_le_centralizer_Z S hTH hidx
    refine (closure_le _).2 fun x hx => ?_
    obtain ⟨hxH, m, hm, hxm⟩ := hx
    have hxT := hc x (subset_closure ⟨hxH, m, hm, hxm⟩)
      (pow_three_of_relIndex_three S.h13.sylow.1 hTH h3 hxH hm hxm)
    exact mem_centralizer_iff.2 fun z hz =>
      (mem_centralizer_iff.1 (s134_Z_le_center T hz).2 x hxT).symm
  refine ⟨y, hyK, hy3, hyT, fun k hk => ?_⟩
  have hsup : oTwoRes H ⊔ T = H :=
    le_antisymm (sup_le (oTwoRes_le H) hTH) (le_oTwoRes_sup_of_isSylowTwoOf hsyl)
  have hTK : T ≤ normalizer (oTwoRes H : Set G) := hTH.trans (le_normalizer_oTwoRes H)
  have h3' : (oTwoRes H ⊓ T).relIndex (oTwoRes H) = 3 := by
    rw [← relIndex_sup_eq hTK, hsup, h3]
  have hKy : (oTwoRes H ⊓ T) ⊔ zpowers y = oTwoRes H := by
    rcases eq_or_eq_of_relIndex_three h3' le_sup_left
      (sup_le inf_le_left (zpowers_le.2 hyK)) with e | e
    · exact absurd ((e ▸ mem_sup_right (mem_zpowers y) : y ∈ oTwoRes H ⊓ T).2) hyT
    · exact e
  have e : oTwoRes H ⊓ T = oTwoRes H ⊓ pCoreOf 2 H := by
    refine le_antisymm (fun x hx => ⟨hx.1, ?_⟩)
      (inf_le_inf_left _ (pCoreOf_two_le_of_isSylowTwoOf hsyl))
    obtain ⟨j, hj⟩ := S.h13.sylow.1 ⟨x, hx.2⟩
    exact mem_pCoreOf_of_mem_oTwoRes hq hx.1 (by simpa using congrArg Subtype.val hj)
  have hyN : zpowers y ≤ normalizer ((oTwoRes H ⊓ T : Subgroup G) : Set G) := by
    rw [e]
    exact zpowers_le.2 (mem_normalizer_inf_of (le_normalizer hyK)
      (le_normalizer_pCoreOf 2 H (oTwoRes_le H hyK)))
  rw [← hKy] at hk
  obtain ⟨n, hn, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hyN hk
  obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.2 hb
  refine ⟨j % 3, Nat.mod_lt _ (by norm_num), fun v hv => ?_⟩
  rw [← pow_eq_pow_mod j hy3]
  have hyv : y ^ j * v * (y ^ j)⁻¹ ∈ v0Of T H₁ H₂ :=
    (mem_normalizer_iff.mp (hred.2.1 (hH (oTwoRes_le H (pow_mem hyK j)))) v).mp hv
  have hc : (y ^ j * v * (y ^ j)⁻¹) * n = n * (y ^ j * v * (y ^ j)⁻¹) :=
    mem_centralizer_iff.1 (s1347_inf_T_le_centralizer S hH₀ hH hq hN hn) _ hyv
  calc n * y ^ j * v * (n * y ^ j)⁻¹ = n * (y ^ j * v * (y ^ j)⁻¹) * n⁻¹ := by group
    _ = y ^ j * v * (y ^ j)⁻¹ := by rw [← hc]; group

omit [Finite G] in
theorem s1347_conjClosure_le_centralizer {H₀ H : Subgroup G}
    (hN : H₀ ≤ normalizer (oTwoRes H : Set G)) :
    conjClosure (cZ T H) H₀ ≤ centralizer (oTwoRes H : Set G) := by
  refine conjClosure_le fun h hh z hz => mem_centralizer_iff.2 fun k hk => ?_
  have hk' : h⁻¹ * k * h⁻¹⁻¹ ∈ oTwoRes H := (mem_normalizer_iff.mp (hN (inv_mem hh)) k).mp hk
  have hc : (h⁻¹ * k * h⁻¹⁻¹) * z = z * (h⁻¹ * k * h⁻¹⁻¹) :=
    mem_centralizer_iff.1 hz.2 _ (oTwoRes_le H hk')
  calc k * (h * z * h⁻¹) = h * ((h⁻¹ * k * h⁻¹⁻¹) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * k * h⁻¹⁻¹)) * h⁻¹ := by rw [hc]
    _ = h * z * h⁻¹ * k := by group

omit [Finite G] in
theorem s1347_Z_comm {a b : G} (ha : a ∈ quasithinOmegaOneCenter T)
    (hb : b ∈ quasithinOmegaOneCenter T) : a * b = b * a :=
  mem_centralizer_iff.1 (s134_Z_le_center T hb).2 a (s134_Z_le_center T ha).1

omit [Finite G] in
theorem s1347_V0_eq_sup {H₁ H₂ : Subgroup G}
    (hsup : cZ T H₁ ⊔ cZ T H₂ = quasithinOmegaOneCenter T) :
    v0Of T H₁ H₂ = conjClosure (cZ T H₂) (H₁ ⊔ H₂) ⊔ conjClosure (cZ T H₁) (H₁ ⊔ H₂) := by
  refine le_antisymm (conjClosure_le fun h hh z hz => ?_)
    (sup_le (conjClosure_mono inf_le_left le_rfl) (conjClosure_mono inf_le_left le_rfl))
  rw [← hsup] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer
    (Vol2.Ch11.SecC.le_normalizer_of_commute fun a ha b hb =>
      s1347_Z_comm (mem_inf.1 ha).1 (mem_inf.1 hb).1) hz
  have e : h * (a * b) * h⁻¹ = h * a * h⁻¹ * (h * b * h⁻¹) := by group
  rw [e]
  exact mul_mem (mem_sup_right (mem_conjClosure hh ha)) (mem_sup_left (mem_conjClosure hh hb))

omit [Finite G] in
theorem mem_cZ_of_mem_centralizer {H : Subgroup G} (hH : H ≤ oTwoRes H ⊔ T) {w : G}
    (hwZ : w ∈ quasithinOmegaOneCenter T) (hwK : w ∈ centralizer (oTwoRes H : Set G)) :
    w ∈ cZ T H := by
  refine mem_inf.2 ⟨hwZ, mem_centralizer_iff.2 fun g hg => ?_⟩
  have hle : oTwoRes H ⊔ T ≤ centralizer ({w} : Set G) := sup_le
    (fun k hk => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hwK k hk))
    (fun t ht => mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 (s134_Z_le_center T hwZ).2 t ht))
  exact mem_centralizer_singleton_iff.1 (hle (hH hg))

theorem s1347_inf_centralizer_eq_bot (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂)) (hinf : cZ T H₁ ⊓ cZ T H₂ = ⊥)
    (hN₁ : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₁ : Set G))
    (hN₂ : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₂ : Set G)) :
    v0Of T H₁ H₂ ⊓ centralizer (oTwoRes H₁ : Set G) ⊓ centralizer (oTwoRes H₂ : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := s1347_reduced S hH₀
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hV2 : IsPGroup 2 ↥(v0Of T H₁ H₂) := fun v => ⟨1, Subtype.ext (by
    simpa using hred.2.2.1.2 v v.2)⟩
  have hVT : v0Of T H₁ H₂ ≤ T :=
    (le_pCoreOf_of_le_normalizer hred.1 hred.2.1 hV2).trans
      (pCoreOf_two_le_of_isSylowTwoOf hsyl₀)
  have hWT : v0Of T H₁ H₂ ⊓ centralizer (oTwoRes H₁ : Set G) ⊓
      centralizer (oTwoRes H₂ : Set G) ≤ T := inf_le_left.trans (inf_le_left.trans hVT)
  have hTW : T ≤ normalizer ((v0Of T H₁ H₂ ⊓ centralizer (oTwoRes H₁ : Set G) ⊓
      centralizer (oTwoRes H₂ : Set G) : Subgroup G) : Set G) := fun t ht => by
    have ht0 : t ∈ H₁ ⊔ H₂ := hH₀.1 ht
    exact mem_normalizer_inf_of (mem_normalizer_inf_of (hred.2.1 ht0)
      (mem_normalizer_centralizer_of_mem (hN₁ ht0)))
      (mem_normalizer_centralizer_of_mem (hN₂ ht0))
  by_contra hne
  have : Group.IsNilpotent ↥T := S.h13.sylow.1.isNilpotent
  have : ((v0Of T H₁ H₂ ⊓ centralizer (oTwoRes H₁ : Set G) ⊓
      centralizer (oTwoRes H₂ : Set G)).subgroupOf T).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWT).2 hTW
  have hne' : (v0Of T H₁ H₂ ⊓ centralizer (oTwoRes H₁ : Set G) ⊓
      centralizer (oTwoRes H₂ : Set G)).subgroupOf T ≠ ⊥ := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := ne_bot_iff_exists_ne_one.1 hne
    refine ne_bot_iff_exists_ne_one.2 ⟨⟨⟨w, hWT hw⟩, hw⟩, fun h1 => hw1 ?_⟩
    have h2 : (⟨w, hWT hw⟩ : ↥T) = 1 := congrArg Subtype.val h1
    have h3 : w = 1 := congrArg Subtype.val h2
    exact Subtype.ext h3
  obtain ⟨⟨⟨w, hwT⟩, hwW⟩, hw1⟩ :=
    ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  obtain ⟨hwW', hwc⟩ := mem_inf.1 hwW
  have hwW'' := mem_subgroupOf.1 hwW'
  obtain ⟨⟨hwV, hw₁⟩, hw₂⟩ := hwW''
  have hwZ : w ∈ quasithinOmegaOneCenter T := by
    refine mem_quasithinOmegaOneCenter_iff.2 ⟨hwT, mem_centralizer_iff.2 fun t ht => ?_,
      hred.2.2.1.2 w hwV⟩
    exact congrArg Subtype.val (mem_center_iff.1 hwc ⟨t, ht⟩)
  have hsyl₁ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₁.1
  have hsyl₂ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₂.1
  have hw : w ∈ cZ T H₁ ⊓ cZ T H₂ :=
    ⟨mem_cZ_of_mem_centralizer (le_oTwoRes_sup_of_isSylowTwoOf hsyl₁) hwZ hw₁,
      mem_cZ_of_mem_centralizer (le_oTwoRes_sup_of_isSylowTwoOf hsyl₂) hwZ hw₂⟩
  rw [hinf, mem_bot] at hw
  exact hw1 (by subst hw; rfl)

theorem eq_one_or_eq_of_card_two {X : Subgroup G} (hX : Nat.card X = 2) {z : G} (hz : z ∈ X)
    (hz1 : z ≠ 1) {x : G} (hx : x ∈ X) : x = 1 ∨ x = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := by
    have h := orderOf_dvd_natCard (⟨z, hz⟩ : ↥X)
    rw [hX, Subgroup.orderOf_mk] at h
    exact orderOf_dvd_iff_pow_eq_one.1 h
  have horder : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hle : zpowers z ≤ X := zpowers_le.2 hz
  have heq : zpowers z = X := eq_of_le_of_card_ge hle (by rw [hX, Nat.card_zpowers, horder])
  rw [← heq] at hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have hz2' : z ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hz2]
  rw [zpow_eq_zpow_emod k hz2']
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

omit [Finite G] in
theorem mul_mul_inv_mul_eq_of_comm {a b : G} (hab : a * b = b * a) (ha : a * a = 1)
    (hb : b * b = 1) : a * b * (b * (a * b))⁻¹ = b := by
  have h1 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
  rw [h1, inv_eq_of_mul_eq_one_right ha, mul_assoc, ← hab, ← mul_assoc, ha, one_mul]

theorem s1347_U_structure (S : A6.Setting134 G T L V) {H₁ H₂ Hi Hj : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) (hi : Hi ≤ H₁ ⊔ H₂) (hTi : T ≤ Hi) (h3i : T.relIndex Hi = 3)
    (hqi : quasithinO2QuotientIso Hi (Perm (Fin 3)))
    (hidx : Nat.card ↥(quasithinOmegaOneCenter T) = 2 * Nat.card ↥(cZ T Hi))
    (hc2 : Nat.card ↥(cZ T Hj) = 2)
    (hNi : H₁ ⊔ H₂ ≤ normalizer (oTwoRes Hi : Set G))
    (hNj : H₁ ⊔ H₂ ≤ normalizer (oTwoRes Hj : Set G))
    (hdec : ∀ x ∈ H₁ ⊔ H₂, ∃ a ∈ Hi, ∃ b ∈ Hj, x = a * b)
    (hV0 : v0Of T H₁ H₂ = conjClosure (cZ T Hj) (H₁ ⊔ H₂) ⊔ conjClosure (cZ T Hi) (H₁ ⊔ H₂))
    (hbot : v0Of T H₁ H₂ ⊓ centralizer (oTwoRes Hi : Set G) ⊓
      centralizer (oTwoRes Hj : Set G) = ⊥) :
    ⁅v0Of T H₁ H₂, oTwoRes Hi⁆ = conjClosure (cZ T Hj) (H₁ ⊔ H₂) ∧
      conjClosure (cZ T Hj) (H₁ ⊔ H₂) = v0Of T H₁ H₂ ⊓ centralizer (oTwoRes Hj : Set G) ∧
      Nat.card ↥(conjClosure (cZ T Hj) (H₁ ⊔ H₂)) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := s1347_reduced S hH₀
  have hsyli := A5.isSylowTwoOf_of_le S.h13.sylow hTi
  have hUC : conjClosure (cZ T Hj) (H₁ ⊔ H₂) ≤ centralizer (oTwoRes Hj : Set G) :=
    s1347_conjClosure_le_centralizer hNj
  have hU'C : conjClosure (cZ T Hi) (H₁ ⊔ H₂) ≤ centralizer (oTwoRes Hi : Set G) :=
    s1347_conjClosure_le_centralizer hNi
  have hUN : H₁ ⊔ H₂ ≤ normalizer (conjClosure (cZ T Hj) (H₁ ⊔ H₂) : Set G) :=
    le_normalizer_conjClosure _ _
  have hUV : conjClosure (cZ T Hj) (H₁ ⊔ H₂) ≤ v0Of T H₁ H₂ := hV0 ▸ le_sup_left
  have hU'V : conjClosure (cZ T Hi) (H₁ ⊔ H₂) ≤ v0Of T H₁ H₂ := hV0 ▸ le_sup_right
  have hcomm : ∀ a ∈ v0Of T H₁ H₂, ∀ b ∈ v0Of T H₁ H₂, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hred.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ v ∈ v0Of T H₁ H₂, v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact hred.2.2.1.2 v hv
  have hinvV : ∀ v ∈ v0Of T H₁ H₂, v⁻¹ = v := fun v hv =>
    inv_eq_of_mul_eq_one_right (hsq v hv)
  obtain ⟨⟨z, hz⟩, hz1⟩ := ne_bot_iff_exists_ne_one.1
    ((one_lt_card_iff_ne_bot (H := cZ T Hj)).1 (by omega))
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzV : z ∈ v0Of T H₁ H₂ := s1347_Z_le_V0 (mem_inf.1 hz).1
  have hzU : z ∈ conjClosure (cZ T Hj) (H₁ ⊔ H₂) := le_conjClosure _ _ hz
  obtain ⟨y, hyK, hy3, -, hact⟩ := s1347_exists_gen S hH₀ hi hTi h3i hqi hidx hNi
  have hyH : y ∈ H₁ ⊔ H₂ := hi (oTwoRes_le Hi hyK)
  have hfix : ∀ v ∈ v0Of T H₁ H₂, y * v * y⁻¹ = v → v ∈ centralizer (oTwoRes Hi : Set G) := by
    intro v hv hyv
    refine mem_centralizer_iff.2 fun k hk => ?_
    obtain ⟨j, -, hj⟩ := hact k hk
    have hc : Commute y v := by
      show y * v = v * y
      calc y * v = (y * v * y⁻¹) * y := by group
        _ = v * y := by rw [hyv]
    have hkv := hj v hv
    rw [(hc.pow_left j).eq, mul_inv_cancel_right] at hkv
    calc k * v = (k * v * k⁻¹) * k := by group
      _ = v * k := by rw [hkv]
  have hbot' : ∀ v ∈ conjClosure (cZ T Hj) (H₁ ⊔ H₂), y * v * y⁻¹ = v → v = 1 := by
    intro v hv hyv
    have hmem : v ∈ v0Of T H₁ H₂ ⊓ centralizer (oTwoRes Hi : Set G) ⊓
        centralizer (oTwoRes Hj : Set G) :=
      ⟨⟨hUV hv, hfix v (hUV hv) hyv⟩, hUC hv⟩
    rw [hbot] at hmem
    exact hmem
  have hwU : y * z * y⁻¹ ∈ conjClosure (cZ T Hj) (H₁ ⊔ H₂) :=
    (mem_normalizer_iff.mp (hUN hyH) z).mp hzU
  have hwV := hUV hwU
  have hwz : y * z * y⁻¹ ≠ z := fun h => hz1' (hbot' z hzU h)
  have hw1 : y * z * y⁻¹ ≠ 1 := fun h => hz1' (by
    have : z = y⁻¹ * (y * z * y⁻¹) * y := by group
    rw [this, h]
    group)
  have hywU : y * (y * z * y⁻¹) * y⁻¹ ∈ conjClosure (cZ T Hj) (H₁ ⊔ H₂) :=
    (mem_normalizer_iff.mp (hUN hyH) _).mp hwU
  have hyyw : y * (y * (y * z * y⁻¹) * y⁻¹) * y⁻¹ = z := by
    calc y * (y * (y * z * y⁻¹) * y⁻¹) * y⁻¹ = y * y * y * z * (y * y * y)⁻¹ := by group
      _ = z := by rw [← pow_three', hy3]; group
  have hyw : y * (y * z * y⁻¹) * y⁻¹ = z * (y * z * y⁻¹) := by
    have hp : z * (y * z * y⁻¹) * (y * (y * z * y⁻¹) * y⁻¹) ∈
        conjClosure (cZ T Hj) (H₁ ⊔ H₂) := mul_mem (mul_mem hzU hwU) hywU
    have hpy : y * (z * (y * z * y⁻¹) * (y * (y * z * y⁻¹) * y⁻¹)) * y⁻¹ =
        z * (y * z * y⁻¹) * (y * (y * z * y⁻¹) * y⁻¹) := by
      have e1 : y * (z * (y * z * y⁻¹) * (y * (y * z * y⁻¹) * y⁻¹)) * y⁻¹ =
          (y * z * y⁻¹) * (y * (y * z * y⁻¹) * y⁻¹) *
            (y * (y * (y * z * y⁻¹) * y⁻¹) * y⁻¹) := by group
      rw [e1, hyyw, hcomm _ (mul_mem hwV (hUV hywU)) z hzV, ← mul_assoc]
    have h1 := hbot' _ hp hpy
    have e2 : y * (y * z * y⁻¹) * y⁻¹ = (z * (y * z * y⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [e2, mul_inv_rev, hinvV _ hwV, hinvV _ hzV, hcomm _ hwV z hzV]
  have hzT : ∀ t ∈ T, t * z * t⁻¹ = z := fun t ht => by
    rw [mem_centralizer_iff.1 (s134_Z_le_center T (mem_inf.1 hz).1).2 t ht]
    group
  have hzHj : ∀ b ∈ Hj, b * z * b⁻¹ = z := fun b hb => by
    rw [mem_centralizer_iff.1 (mem_inf.1 hz).2 b hb]
    group
  have hTKi : T ≤ normalizer (oTwoRes Hi : Set G) := hTi.trans (le_normalizer_oTwoRes Hi)
  have hUP : conjClosure (cZ T Hj) (H₁ ⊔ H₂) ≤ zpowers z ⊔ zpowers (y * z * y⁻¹) := by
    refine conjClosure_le fun h hh z' hz' => ?_
    rcases eq_one_or_eq_of_card_two hc2 hz hz1' hz' with h1 | h1
    · rw [h1, mul_one, mul_inv_cancel]
      exact one_mem _
    rw [h1]
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec h hh
    obtain ⟨k, hk, t, ht, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hTKi
      (le_oTwoRes_sup_of_isSylowTwoOf hsyli ha)
    have e : k * t * b * z * (k * t * b)⁻¹ = k * (t * (b * z * b⁻¹) * t⁻¹) * k⁻¹ := by group
    rw [e, hzHj b hb, hzT t ht]
    obtain ⟨j, hj3, hj⟩ := hact k hk
    rw [hj z hzV]
    interval_cases j
    · rw [pow_zero, one_mul, inv_one, mul_one]
      exact mem_sup_left (mem_zpowers z)
    · rw [pow_one]
      exact mem_sup_right (mem_zpowers _)
    · have e2 : y ^ 2 * z * (y ^ 2)⁻¹ = y * (y * z * y⁻¹) * y⁻¹ := by
        rw [pow_two]
        group
      rw [e2, hyw]
      exact mul_mem (mem_sup_left (mem_zpowers z)) (mem_sup_right (mem_zpowers _))
  have hzz : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq z hzV) hz1'
  have hP4 : Nat.card ↥(zpowers z ⊔ zpowers (y * z * y⁻¹)) ≤ 4 := by
    have hww : orderOf (y * z * y⁻¹) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq _ hwV)
    have hN : zpowers (y * z * y⁻¹) ≤ normalizer (zpowers z : Set G) :=
      Vol2.Ch11.SecC.le_normalizer_of_commute fun a ha b hb =>
        hcomm a (zpowers_le.2 hzV ha) b (zpowers_le.2 hwV hb)
    have h2 : (zpowers z ⊓ zpowers (y * z * y⁻¹)).relIndex (zpowers z) ∣
        Nat.card ↥(zpowers z) := relIndex_dvd_card _ _
    rw [Nat.card_zpowers, hzz] at h2
    have h3 := relIndex_mul_card (zpowers (y * z * y⁻¹)) (zpowers z ⊔ zpowers (y * z * y⁻¹))
    rw [inf_eq_left.2 (le_sup_right : zpowers (y * z * y⁻¹) ≤
      zpowers z ⊔ zpowers (y * z * y⁻¹)), relIndex_sup_eq hN] at h3
    have h4 : Nat.card ↥(zpowers (y * z * y⁻¹)) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) hww
    rw [← h3]
    calc _ ≤ 2 * 2 := Nat.mul_le_mul (Nat.le_of_dvd (by norm_num) h2) h4
      _ = 4 := by norm_num
  have hU4 : Nat.card ↥(conjClosure (cZ T Hj) (H₁ ⊔ H₂)) = 4 := by
    have hle4 := (card_le_of_le hUP).trans hP4
    have hdvd : 2 ∣ Nat.card ↥(conjClosure (cZ T Hj) (H₁ ⊔ H₂)) := by
      have := card_dvd_of_le (zpowers_le.2 hzU)
      rwa [Nat.card_zpowers, hzz] at this
    have hne2 : Nat.card ↥(conjClosure (cZ T Hj) (H₁ ⊔ H₂)) ≠ 2 := by
      intro h2
      have heq : zpowers z = conjClosure (cZ T Hj) (H₁ ⊔ H₂) :=
        eq_of_le_of_card_ge (zpowers_le.2 hzU) (by rw [h2, Nat.card_zpowers, hzz])
      have hwz' : y * z * y⁻¹ ∈ zpowers z := by
        rw [heq]
        exact hwU
      rcases eq_one_or_eq_of_card_two (by rw [Nat.card_zpowers, hzz]) (mem_zpowers z) hz1'
        hwz' with h | h
      exacts [hw1 h, hwz h]
    have hpos : 0 < Nat.card ↥(conjClosure (cZ T Hj) (H₁ ⊔ H₂)) := Nat.card_pos
    omega
  have hzinv : z⁻¹ = z := hinvV z hzV
  have hzC : z ∈ ⁅v0Of T H₁ H₂, oTwoRes Hi⁆ := by
    have e : ⁅y * z * y⁻¹, y⁆ = (y * z * y⁻¹) * (y * (y * z * y⁻¹) * y⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hyw, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul, hzinv] at e
    rw [← e]
    exact commutator_mem_commutator hwV hyK
  have hwC : y * z * y⁻¹ ∈ ⁅v0Of T H₁ H₂, oTwoRes Hi⁆ := by
    have e : ⁅z * (y * z * y⁻¹), y⁆ =
        (z * (y * z * y⁻¹)) * ((y * z * y⁻¹) * (y * (y * z * y⁻¹) * y⁻¹))⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hyw, mul_mul_inv_mul_eq_of_comm (hcomm z hzV _ hwV) (hsq z hzV) (hsq _ hwV)] at e
    rw [← e]
    exact commutator_mem_commutator (mul_mem hzV hwV) hyK
  have hUle : conjClosure (cZ T Hj) (H₁ ⊔ H₂) ≤ ⁅v0Of T H₁ H₂, oTwoRes Hi⁆ :=
    hUP.trans (sup_le (zpowers_le.2 hzC) (zpowers_le.2 hwC))
  have hU'N : conjClosure (cZ T Hi) (H₁ ⊔ H₂) ≤
      normalizer (conjClosure (cZ T Hj) (H₁ ⊔ H₂) : Set G) :=
    Vol2.Ch11.SecC.le_normalizer_of_commute fun a ha b hb => hcomm a (hUV ha) b (hU'V hb)
  have hcomU : ⁅v0Of T H₁ H₂, oTwoRes Hi⁆ ≤ conjClosure (cZ T Hj) (H₁ ⊔ H₂) := by
    rw [commutator_le]
    intro v hv k hk
    rw [hV0] at hv
    obtain ⟨u, hu, u', hu', rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hU'N hv
    have hc : k * u' = u' * k := mem_centralizer_iff.1 (hU'C hu') k hk
    have hkU : k * u⁻¹ * k⁻¹ ∈ conjClosure (cZ T Hj) (H₁ ⊔ H₂) :=
      (mem_normalizer_iff.mp (hUN (hi (oTwoRes_le Hi hk))) _).mp (inv_mem hu)
    have e : ⁅u * u', k⁆ = u * (k * u⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      calc u * u' * k * (u * u')⁻¹ * k⁻¹ = u * (u' * k) * u'⁻¹ * u⁻¹ * k⁻¹ := by group
        _ = u * (k * u') * u'⁻¹ * u⁻¹ * k⁻¹ := by rw [hc]
        _ = u * (k * u⁻¹ * k⁻¹) := by group
    rw [e]
    exact mul_mem hu hkU
  have hUeq : conjClosure (cZ T Hj) (H₁ ⊔ H₂) =
      v0Of T H₁ H₂ ⊓ centralizer (oTwoRes Hj : Set G) := by
    refine le_antisymm (le_inf hUV hUC) fun v hv => ?_
    obtain ⟨hvV, hvC⟩ := mem_inf.1 hv
    rw [hV0] at hvV
    obtain ⟨u, hu, u', hu', rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hU'N hvV
    have hu'C : u' ∈ centralizer (oTwoRes Hj : Set G) := by
      have e : u' = u⁻¹ * (u * u') := by group
      rw [e]
      exact mul_mem (inv_mem (hUC hu)) hvC
    have hmem : u' ∈ v0Of T H₁ H₂ ⊓ centralizer (oTwoRes Hi : Set G) ⊓
        centralizer (oTwoRes Hj : Set G) := ⟨⟨hU'V hu', hU'C hu'⟩, hu'C⟩
    rw [hbot, mem_bot] at hmem
    rw [hmem, mul_one]
    exact hu
  exact ⟨le_antisymm hcomU hUle, hUeq, hU4⟩

theorem s1347_V0_of_normal (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂))
    (hsup : cZ T H₁ ⊔ cZ T H₂ = quasithinOmegaOneCenter T) (hinf : cZ T H₁ ⊓ cZ T H₂ = ⊥)
    (hc₁ : Nat.card ↥(cZ T H₁) = 2) (hc₂ : Nat.card ↥(cZ T H₂) = 2)
    (hN₁ : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₁ : Set G))
    (hN₂ : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₂ : Set G)) :
    ⁅v0Of T H₁ H₂, oTwoRes H₁⁆ ⊔ ⁅v0Of T H₁ H₂, oTwoRes H₂⁆ = v0Of T H₁ H₂ ∧
      ⁅v0Of T H₁ H₂, oTwoRes H₁⁆ ⊓ ⁅v0Of T H₁ H₂, oTwoRes H₂⁆ = ⊥ ∧
      ⁅v0Of T H₁ H₂, oTwoRes H₁⁆ = v0Of T H₁ H₂ ⊓ centralizer (oTwoRes H₂ : Set G) ∧
      ⁅v0Of T H₁ H₂, oTwoRes H₂⁆ = v0Of T H₁ H₂ ⊓ centralizer (oTwoRes H₁ : Set G) ∧
      Nat.card ↥⁅v0Of T H₁ H₂, oTwoRes H₁⁆ = 4 ∧ Nat.card ↥⁅v0Of T H₁ H₂, oTwoRes H₂⁆ = 4 := by
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hsyl₁ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₁.1
  have hdec₁ := s1347_mul_of_normal h.inH₂.1 (le_oTwoRes_sup_of_isSylowTwoOf hsyl₁) hN₁
  have hdec₂ : ∀ x ∈ H₁ ⊔ H₂, ∃ a ∈ H₂, ∃ b ∈ H₁, x = a * b := by
    intro x hx
    obtain ⟨a, ha, b, hb, e⟩ := hdec₁ x⁻¹ (inv_mem hx)
    exact ⟨b⁻¹, inv_mem hb, a⁻¹, inv_mem ha, by rw [← mul_inv_rev, ← e, inv_inv]⟩
  have hV0 := s1347_V0_eq_sup hsup
  have hbot := s1347_inf_centralizer_eq_bot S h hH₀ hinf hN₁ hN₂
  obtain ⟨e₁, f₁, c₁⟩ := s1347_U_structure S hH₀ le_sup_left h.inH₁.1 h3₁ h.s3₁ h.index₁ hc₂
    hN₁ hN₂ hdec₁ hV0 hbot
  obtain ⟨e₂, f₂, c₂⟩ := s1347_U_structure S hH₀ le_sup_right h.inH₂.1 h3₂ h.s3₂ h.index₂ hc₁
    hN₂ hN₁ hdec₂ (by rw [hV0, sup_comm]) (by rw [inf_right_comm]; exact hbot)
  refine ⟨?_, ?_, e₁.trans f₁, e₂.trans f₂, by rw [e₁]; exact c₁, by rw [e₂]; exact c₂⟩
  · rw [e₁, e₂, hV0]
  · rw [e₁, f₁, e₂, f₂, eq_bot_iff]
    intro x hx
    rw [← hbot]
    exact ⟨⟨hx.1.1, hx.2.2⟩, hx.1.2⟩

end CFSG.Quasithin.H13.U3
