module

public import CFSG.Quasithin.Vol2.Ch12Sec6L19
public import CFSG.Alternating.Multipliers.Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c S126FE S126N S126L19 Equiv
open scoped IsMulCommutative

namespace S126L19a

theorem pow_mem_block {σ : Perm (Fin 8)} (h : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4))
    (k : ℕ) (i : Fin 8) : (i.val < 4 ↔ ((σ ^ k) i).val < 4) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ← h]
    exact ih

theorem card_block : ∀ i : Fin 8,
    (Finset.univ.filter fun j : Fin 8 => (j.val < 4 ↔ i.val < 4)).card = 4 := by
  decide

theorem exists_pow_fix {σ : Perm (Fin 8)} (h : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4))
    (i : Fin 8) : ∃ ℓ : ℕ, 0 < ℓ ∧ ℓ ≤ 4 ∧ (σ ^ ℓ) i = i := by
  set B := Finset.univ.filter fun j : Fin 8 => (j.val < 4 ↔ i.val < 4) with hB
  have hmaps : Set.MapsTo (fun k : Fin 5 => (σ ^ k.val) i) (Finset.univ : Finset (Fin 5)) B := by
    intro k _
    simp only [hB, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact (pow_mem_block h k.val i).symm
  obtain ⟨a, -, b, -, hab, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by rw [card_block, Finset.card_univ, Fintype.card_fin]; norm_num) hmaps
  have key : ∀ a b : Fin 5, a.val < b.val → (σ ^ a.val) i = (σ ^ b.val) i →
      ∃ ℓ : ℕ, 0 < ℓ ∧ ℓ ≤ 4 ∧ (σ ^ ℓ) i = i := by
    intro a b hlt he
    refine ⟨b.val - a.val, by omega, by omega, ?_⟩
    have hb : b.val = a.val + (b.val - a.val) := by omega
    rw [hb, pow_add, Perm.mul_apply] at he
    exact ((σ ^ a.val).injective he).symm
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hab) with hlt | hlt
  · exact key a b hlt he
  · exact key b a hlt he.symm

theorem pow_twelve_of_block {σ : Perm (Fin 8)} (h : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) :
    σ ^ 12 = 1 := by
  refine Equiv.ext fun i => ?_
  obtain ⟨ℓ, hℓ0, hℓ4, hℓ⟩ := exists_pow_fix h i
  have hdvd : ℓ ∣ 12 := by
    interval_cases ℓ <;> norm_num
  obtain ⟨m, hm⟩ := hdvd
  rw [Perm.one_apply, hm, pow_mul]
  exact Perm.pow_apply_eq_self_of_apply_eq_self hℓ m

theorem pow_24 {σ : Perm (Fin 8)}
    (h : (∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) ∨ (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val))) :
    σ ^ 24 = 1 := by
  rcases h with h | h
  · rw [show 24 = 12 * 2 by norm_num, pow_mul, pow_twelve_of_block h, one_pow]
  · have h2 : ∀ i : Fin 8, (i.val < 4 ↔ ((σ ^ 2) i).val < 4) := by
      intro i
      rw [pow_two, Perm.mul_apply, h i]
      have := h (σ i)
      omega
    rw [show 24 = 2 * 12 by norm_num, pow_mul, pow_twelve_of_block h2]

theorem pow_three_of_odd {σ : Perm (Fin 8)} (h24 : σ ^ 24 = 1) {m : ℕ} (hm : Odd m)
    (h : σ ^ m = 1) : σ ^ 3 = 1 := by
  have h1 : orderOf σ ∣ 24 := orderOf_dvd_of_pow_eq_one h24
  have h2 : Odd (orderOf σ) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h)
  have h3 : orderOf σ ∣ 3 := by
    have hc : Nat.Coprime (orderOf σ) 8 :=
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 h2) |>.coprime_dvd_right (by norm_num)
    exact hc.dvd_of_dvd_mul_left (by simpa [show (24 : ℕ) = 3 * 8 by norm_num] using h1)
  exact orderOf_dvd_iff_pow_eq_one.1 h3

theorem eq_one_of_pow_five {σ : Perm (Fin 8)} (h24 : σ ^ 24 = 1) (h5 : σ ^ 5 = 1) : σ = 1 := by
  have h25 : σ ^ 25 = 1 := by rw [show 25 = 5 * 5 by norm_num, pow_mul, h5, one_pow]
  rw [show 25 = 24 + 1 by norm_num, pow_add, h24, one_mul, pow_one] at h25
  exact h25

variable {G : Type} [Group G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem isPGroup_ker [Finite G] (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    IsPGroup 2 ↥((Subgroup.centralizer (V : Set G)).subgroupOf L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_reduced hyp.normalizes hVT hred
  obtain ⟨φ, hφ, hker⟩ := hH.alt8
  set N := CFSG.pCore 2 ↥L with hN
  have hNK : N ≤ φ.ker := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf]
    apply hO2
    have hx' : x ∈ CFSG.Open.pCore 2 ↥L := by
      exact hx
    exact ⟨x, hx', rfl⟩
  have hNn : N.Normal := CFSG.pCore_normal
  have hq := hyp.quasisimple
  have : Group.IsPerfect (↥L ⧸ N) := hq.1
  let q : ↥L ⧸ N →* ↥(alternatingGroup (Fin 8)) := QuotientGroup.lift N φ hNK
  have hqs : Function.Surjective q := QuotientGroup.lift_surjective_of_surjective _ _ hφ _
  have hqmk : ∀ l : ↥L, q (l : ↥L ⧸ N) = φ l := fun l => rfl
  have hqn : q.ker.Normal := MonoidHom.normal_ker q
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq q.ker with hc | htop
  · have hmap := CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hqs hc
    have hcard : Nat.card ↥q.ker ∣ 2 := by
      have h1 := Subgroup.card_map_dvd (CFSG.RankThree.PerfectCover.hopfMultiplier
        ↥(alternatingGroup (Fin 8))) (CFSG.RankThree.PerfectCover.hopfLift q hqs hc)
      rw [hmap, CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup le_rfl] at h1
      exact h1
    have hp : IsPGroup 2 ↥q.ker := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hcard with h1 | h1
      · exact IsPGroup.of_card (n := 0) (by rw [h1, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [h1, pow_one])
    rintro ⟨k, hk⟩
    have hk' : k ∈ φ.ker := by rw [hker]; exact hk
    obtain ⟨a, ha⟩ := hp ⟨(k : ↥L ⧸ N), by rw [MonoidHom.mem_ker, hqmk]; exact hk'⟩
    have ha' : ((k ^ 2 ^ a : ↥L) : ↥L ⧸ N) = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hkN : k ^ 2 ^ a ∈ N := (QuotientGroup.eq_one_iff _).mp ha'
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hkN⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : (k ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul, hb']
  · exfalso
    have h1 : ∀ s : ↥(alternatingGroup (Fin 8)), s = 1 := by
      intro s
      obtain ⟨y, rfl⟩ := hqs s
      have hy : y ∈ q.ker := htop ▸ Subgroup.mem_top y
      exact hy
    have h2 := h1 ⟨swap 0 1 * swap 1 2, by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide⟩
    have h3 := congrArg (fun s : ↥(alternatingGroup (Fin 8)) => (s : Perm (Fin 8)) 0) h2
    exact absurd h3 (by decide)

@[expose] noncomputable def psi [Finite G] (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    ↥L →* ↥(alternatingGroup (Fin 8)) :=
  (MulEquiv.ofBijective F.π (pi_bijective F hH)).symm.toMonoidHom.comp
    (InternalSec.autOnHom hH.hyp.irrPlus.2.2.1)

theorem pi_psi [Finite G] (F : Frame126 T L V) (hH : Hyp126 G T L V) (l : ↥L) :
    ((F.π (psi F hH l) : ↥(autOn L V)) : MulAut ↥V) =
      conjAct V ⟨(l : G), hH.hyp.irrPlus.2.2.1 l.2⟩ := by
  have h := (MulEquiv.ofBijective F.π (pi_bijective F hH)).apply_symm_apply
    (InternalSec.autOnHom hH.hyp.irrPlus.2.2.1 l)
  have h2 := congrArg (fun a : ↥(autOn L V) => (a : MulAut ↥V)) h
  exact h2

theorem actsAs_psi [Finite G] (F : Frame126 T L V) (hH : Hyp126 G T L V) (l : ↥L) :
    ActsAs F l (psi F hH l) :=
  actsAs_of_pi F (hH.hyp.irrPlus.2.2.1 l.2) _ (pi_psi F hH l).symm

theorem psi_surjective [Finite G] (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    Function.Surjective (psi F hH) :=
  (MulEquiv.ofBijective F.π (pi_bijective F hH)).symm.surjective.comp
    (InternalSec.autOnHom_surjective hH.hyp.irrPlus.2.2.1)

theorem psi_eq_one_iff [Finite G] (F : Frame126 T L V) (hH : Hyp126 G T L V) (l : ↥L) :
    psi F hH l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [← InternalSec.mem_ker_autOnHom hH.hyp.irrPlus.2.2.1]
  change (MulEquiv.ofBijective F.π (pi_bijective F hH)).symm _ = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  rfl

theorem card_eq [Finite G] (F : Frame126 T L V) (hH : Hyp126 G T L V) {Y : Subgroup G}
    (hYL : Y ≤ L) : Nat.card Y = Nat.card ↥((Y.subgroupOf L).map (psi F hH)) *
      Nat.card ↥(Y ⊓ Subgroup.centralizer (V : Set G)) := by
  let f : ↥(Y.subgroupOf L) →* ↥(alternatingGroup (Fin 8)) := (psi F hH).comp (Subgroup.subtype _)
  have hr : f.range = (Y.subgroupOf L).map (psi F hH) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : Nat.card f.ker = Nat.card ↥(Y ⊓ Subgroup.centralizer (V : Set G)) := by
    refine Nat.card_congr ⟨fun x => ⟨((x : ↥(Y.subgroupOf L)) : ↥L), ?_, ?_⟩,
      fun y => ⟨⟨⟨y, hYL y.2.1⟩, y.2.1⟩, ?_⟩, fun x => ?_, fun y => ?_⟩
    · exact (x : ↥(Y.subgroupOf L)).2
    · exact (psi_eq_one_iff F hH _).1 x.2
    · show psi F hH ⟨y, hYL y.2.1⟩ = 1
      exact (psi_eq_one_iff F hH _).2 y.2.2
    · rfl
    · rfl
  have hY : Nat.card ↥(Y.subgroupOf L) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv
  rw [← hY, Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hr, hk]

omit [IsMulCommutative ↥V] in
theorem card_inf_eq_pow [Finite G] (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) {Y : Subgroup G}
    (hYL : Y ≤ L) : ∃ a : ℕ, Nat.card ↥(Y ⊓ Subgroup.centralizer (V : Set G)) = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := isPGroup_ker h1222 hH
  have hp' : IsPGroup 2 ↥(Y ⊓ Subgroup.centralizer (V : Set G)) := by
    rintro ⟨y, hyY, hyC⟩
    obtain ⟨k, hk⟩ := hp ⟨⟨y, hYL hyY⟩, hyC⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥((Subgroup.centralizer (V : Set G)).subgroupOf L) =>
      ((z : ↥L) : G)) hk
    simpa using this
  exact hp'.exists_card_eq

theorem mem_W1 {y : D8} (hy : y ∈ W1) : y = 1 ∨ y = e0123 := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
  clear hy
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    right
    have hx' : (x : PermMod 8) = eset {0, 1, 2, 3} := hx
    rw [QuotientGroup.mk'_apply, e0123]
    congr 1
    exact Subtype.ext hx'
  | one => left; rw [map_one]
  | mul x y _ _ hx hy =>
    have he : e0123 * e0123 = 1 := by
      rw [e0123, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      change (eset {0, 1, 2, 3} * eset {0, 1, 2, 3} : PermMod 8) ∈ Subgroup.zpowers (allOnes 8)
      rw [show (eset {0, 1, 2, 3} * eset {0, 1, 2, 3} : PermMod 8) = 1 by decide]
      exact Subgroup.one_mem _
    rw [map_mul]
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · left; rw [one_mul]
    · right; rw [one_mul]
    · right; rw [mul_one]
    · left; exact he
  | inv x _ hx =>
    rw [map_inv]
    rcases hx with hx | hx
    · left; rw [hx, inv_one]
    · right
      rw [hx, e0123, ← QuotientGroup.mk_inv]
      congr 1
      exact Subtype.ext (by decide)

theorem e0123_mem_W1 : e0123 ∈ W1 :=
  Subgroup.mem_map.2 ⟨⟨eset {0, 1, 2, 3}, e0123_mem⟩, Subgroup.subset_closure rfl, rfl⟩

theorem e0123_ne_one : e0123 ≠ 1 := by
  intro h
  rw [e0123, mk_eq_one_iff] at h
  rcases h with h | h
  · have := congrArg (fun m : ↥(coreMod 8) =>
      (Multiplicative.toAdd (m : PermMod 8) : Fin 8 → ZMod 2) 0) h
    exact absurd this (by decide)
  · have := congrArg (fun m : ↥(coreMod 8) =>
      (Multiplicative.toAdd (m : PermMod 8) : Fin 8 → ZMod 2) 4) h
    exact absurd this (by decide)

theorem blocks_of_eset {σ : Perm (Fin 8)}
    (h : permAct 8 σ (eset {0, 1, 2, 3}) = eset {0, 1, 2, 3} ∨
      permAct 8 σ (eset {0, 1, 2, 3}) = eset {0, 1, 2, 3} * allOnes 8) :
    (∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) ∨ (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val)) := by
  have key : ∀ i : Fin 8, Multiplicative.toAdd (permAct 8 σ (eset {0, 1, 2, 3})) (σ i) =
      if i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) then 1 else 0 := by
    intro i
    rw [permAct_apply, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
    rfl
  rcases h with h | h
  · left
    intro i
    have h1 := key i
    rw [h] at h1
    change (if σ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) then (1 : ZMod 2) else 0) = _ at h1
    rw [← mem_0123, ← mem_0123]
    by_cases ha : i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) <;>
      by_cases hb : σ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) <;> simp_all
  · right
    intro i
    have h1 := key i
    rw [h, toAdd_mul] at h1
    change (if σ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) then (1 : ZMod 2) else 0) + 1 = _ at h1
    have hlt : 4 ≤ (σ i).val ↔ ¬ (σ i).val < 4 := by omega
    rw [← mem_0123, hlt, ← mem_0123]
    by_cases ha : i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) <;>
      by_cases hb : σ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)) <;> simp_all

theorem blocks_of_mem_V1 (F : Frame126 T L V) {x : G}
    (hx1 : x ∈ Subgroup.normalizer (F.V1 : Set G))
    {σ : Perm (Fin 8)} (hσ : ActsAs F x σ) :
    (∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) ∨ (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val)) := by
  obtain ⟨v, hv⟩ := F.β_surj e0123
  have hv1 : (v : G) ∈ F.V1 :=
    Subgroup.mem_map.2 ⟨v, by rw [Subgroup.mem_comap, hv]; exact e0123_mem_W1, rfl⟩
  have hw1 : x * v * x⁻¹ ∈ F.V1 := (Subgroup.mem_normalizer_iff.1 hx1 v).1 hv1
  obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.1 hw1
  have h1 := hσ v w hwv
  rw [hv] at h1
  have h2 : F.β w ∈ W1 := hw
  rw [h1] at h2
  rcases mem_W1 h2 with h3 | h3
  · exfalso
    have : e0123 = 1 := by
      have := congrArg (dAct σ⁻¹) h3
      rwa [dAct_inv_dAct, map_one] at this
    exact e0123_ne_one this
  · apply blocks_of_eset
    rw [e0123, dAct_mk, mk_eq_iff, coreAct_coe] at h3
    exact h3

end S126L19a

end CFSG.Quasithin.H13
