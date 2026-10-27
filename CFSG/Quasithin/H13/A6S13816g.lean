module

public import CFSG.Quasithin.H13.A6S13816f
public import CFSG.Quasithin.H13.A6S13816Sz
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Quasithin.H13.A6HatPlusB

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace SzCase

variable {G : Type} [Group G]

theorem mem_normalizer_of_map_conj_eq {K : Subgroup G} {g h : G}
    (e : K.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj h).toMonoidHom) :
    h⁻¹ * g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 : g * y * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom ↔
      g * y * g⁻¹ ∈ K.map (MulAut.conj h).toMonoidHom := by rw [e]
  rw [A38.mem_map_conj, A38.mem_map_conj] at h1
  have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
  have e2 : h⁻¹ * (g * y * g⁻¹) * h = h⁻¹ * g * y * (h⁻¹ * g)⁻¹ := by group
  rwa [e1, e2] at h1

theorem mem_normalizer_of_ncard_two {H K : Subgroup G}
    (h2 : Set.ncard (conjSubgroupsBy H K) = 2) {x : G} (hx : x ∈ H) (hx3 : x ^ 3 = 1) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hne
  have hne' : K.map (MulAut.conj x).toMonoidHom ≠ K := fun h => hne (A38.map_conj_eq_iff.mp h)
  obtain ⟨a, b, hab, hS⟩ := Set.ncard_eq_two.mp h2
  have hK : K ∈ conjSubgroupsBy H K := ⟨1, H.one_mem, by
    ext y
    simp⟩
  have hKx : K.map (MulAut.conj x).toMonoidHom ∈ conjSubgroupsBy H K := ⟨x, hx, rfl⟩
  have hKx2 : K.map (MulAut.conj (x * x)).toMonoidHom ∈ conjSubgroupsBy H K :=
    ⟨x * x, H.mul_mem hx hx, rfl⟩
  have hmem : ∀ Y ∈ conjSubgroupsBy H K, Y = K ∨ Y = K.map (MulAut.conj x).toMonoidHom := by
    intro Y hY
    rw [hS] at hY hK hKx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY hK hKx
    rcases hK with h1 | h1 <;> rcases hKx with h2 | h2 <;> rcases hY with h3 | h3
    · exact Or.inl (h3.trans h1.symm)
    · exact absurd (h2.trans h1.symm) hne'
    · exact Or.inl (h3.trans h1.symm)
    · exact Or.inr (h3.trans h2.symm)
    · exact Or.inr (h3.trans h2.symm)
    · exact Or.inl (h3.trans h1.symm)
    · exact absurd (h2.trans h1.symm) hne'
    · exact Or.inl (h3.trans h1.symm)
  have hxinv : x⁻¹ = x * x :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_three']; exact hx3)
  rcases hmem _ hKx2 with h | h
  · apply hne
    have h1 : K.map (MulAut.conj (x * x)).toMonoidHom =
        K.map (MulAut.conj (1 : G)).toMonoidHom := by
      rw [h]
      ext y
      simp
    have h2 := mem_normalizer_of_map_conj_eq h1
    rw [inv_one, one_mul, ← hxinv] at h2
    simpa using Subgroup.inv_mem _ h2
  · apply hne
    have h2 := mem_normalizer_of_map_conj_eq h
    have e : x⁻¹ * (x * x) = x := by group
    rwa [e] at h2

theorem not_three_dvd_suzuki_order (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  generalize q ^ 2 = q2 at hq2 ⊢
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h <;> omega
  · omega

theorem not_three_dvd_of_isSz {X : Type} [Group X] {n : ℕ}
    (h : IsSz n X) : ¬ 3 ∣ Nat.card X := by
  obtain ⟨-, a, -, F, _, _, rfl, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF]
  exact not_three_dvd_suzuki_order a

theorem card_sup_dvd_of_comm {Q : Type} [Group Q] [Finite Q] {A B : Subgroup Q}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Nat.card ↥(A ⊔ B) ∣ Nat.card A * Nat.card B := by
  let μ : ↥A × ↥B →* Q :=
    { toFun := fun p => (p.1 : Q) * p.2
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        have h := hAB _ q.1.2 _ p.2.2
        calc (p.1 : Q) * q.1 * (p.2 * q.2) = p.1 * (q.1 * p.2) * q.2 := by group
          _ = p.1 * (p.2 * q.1) * q.2 := by rw [h]
          _ = p.1 * p.2 * (q.1 * q.2) := by group }
  have hrange : μ.range = A ⊔ B := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := L32Comm.exists_mul_of_mem_sup hAB hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← hrange, ← Nat.card_prod]
  exact Subgroup.card_range_dvd μ

theorem centralizes_of_szCent {Q : Type} [Group Q] [Finite Q] (hSzC : SzCent)
    {Ki Tb Lb B : Subgroup Q} {n : ℕ} (hSzi : IsSz n ↥Ki) (hUi : IsSylowTwoOf (Tb ⊓ Ki) Ki)
    (hLKi : Lb ≤ Subgroup.normalizer (Ki : Set Q))
    (hLUi : Lb ≤ Subgroup.normalizer ((Tb ⊓ Ki : Subgroup Q) : Set Q))
    (hKiB : ∀ d ∈ Ki, d ∈ Subgroup.normalizer ((Tb ⊓ Ki : Subgroup Q) : Set Q) → d ∈ B)
    (hBL : B ≤ Subgroup.normalizer (Lb : Set Q)) (hLB : Lb ≤ Subgroup.normalizer (B : Set Q))
    (hLBT : ∀ w ∈ Lb, w ∈ B → w ∈ Tb) :
    ∀ x ∈ Lb, x ^ 3 = 1 → ∀ k ∈ Ki, x * k * x⁻¹ = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx hx3
  have hcomm_d : ∀ d ∈ Ki, d ∈ Subgroup.normalizer ((Tb ⊓ Ki : Subgroup Q) : Set Q) →
      d * x * d⁻¹ * x⁻¹ ∈ Tb ⊓ Ki := by
    intro d hdK hdN
    have hdB := hKiB d hdK hdN
    have hwL : d * x * d⁻¹ * x⁻¹ ∈ Lb :=
      Lb.mul_mem ((Subgroup.mem_normalizer_iff.mp (hBL hdB) x).mp hx) (Lb.inv_mem hx)
    have hwB : d * x * d⁻¹ * x⁻¹ ∈ B := by
      have h1 : x * d⁻¹ * x⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (hLB hx) d⁻¹).mp (B.inv_mem hdB)
      have e : d * x * d⁻¹ * x⁻¹ = d * (x * d⁻¹ * x⁻¹) := by group
      rw [e]
      exact B.mul_mem hdB h1
    have hwK : d * x * d⁻¹ * x⁻¹ ∈ Ki := by
      have h1 : x * d⁻¹ * x⁻¹ ∈ Ki :=
        (Subgroup.mem_normalizer_iff.mp (hLKi hx) d⁻¹).mp (Ki.inv_mem hdK)
      have e : d * x * d⁻¹ * x⁻¹ = d * (x * d⁻¹ * x⁻¹) := by group
      rw [e]
      exact Ki.mul_mem hdK h1
    exact ⟨hLBT _ hwL hwB, hwK⟩
  have hxN : Ki.map (MulAut.conj x).toMonoidHom = Ki := A38.map_conj_eq_iff.mpr (hLKi hx)
  let α : MulAut ↥Ki := ((MulAut.conj x).subgroupMap Ki).trans (MulEquiv.subgroupCongr hxN)
  have hα : ∀ k : ↥Ki, ((α k : ↥Ki) : Q) = x * k * x⁻¹ := fun k => rfl
  have hα3 : α ^ 3 = 1 := by
    ext k
    rw [pow_three', MulAut.mul_apply, MulAut.mul_apply, hα, hα, hα, MulAut.one_apply]
    have e : x * (x * (x * (k : Q) * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * k * (x ^ 3)⁻¹ := by
      rw [pow_three']
      group
    rw [e, hx3, one_mul, inv_one, mul_one]
  have hP : IsPGroup 2 ↥((Tb ⊓ Ki).subgroupOf Ki) :=
    hUi.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hUi.1).symm
  set Sy := hP.toSylow hUi.2.2 with hSy
  have hS1 : ∀ s ∈ (Sy : Subgroup ↥Ki), α s ∈ (Sy : Subgroup ↥Ki) := by
    intro s hs
    have hs' : (s : Q) ∈ Tb ⊓ Ki := Subgroup.mem_subgroupOf.mp hs
    show (α s : ↥Ki) ∈ (Tb ⊓ Ki).subgroupOf Ki
    rw [Subgroup.mem_subgroupOf, hα]
    exact (Subgroup.mem_normalizer_iff.mp (hLUi hx) _).mp hs'
  have hS2 : ∀ b ∈ Subgroup.normalizer ((Sy : Subgroup ↥Ki) : Set ↥Ki),
      α b * b⁻¹ ∈ (Sy : Subgroup ↥Ki) := by
    intro b hb
    have hbN : (b : Q) ∈ Subgroup.normalizer ((Tb ⊓ Ki : Subgroup Q) : Set Q) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      by_cases hh : h ∈ Ki
      · exact Subgroup.mem_normalizer_iff.mp hb ⟨h, hh⟩
      · constructor
        · intro h1
          exact absurd h1.2 hh
        · intro h1
          exfalso
          apply hh
          have h2 : (b : Q)⁻¹ * ((b : Q) * h * (b : Q)⁻¹) * (b : Q) = h := by group
          rw [← h2]
          exact Ki.mul_mem (Ki.mul_mem (Ki.inv_mem b.2) h1.2) b.2
    have h1 := hcomm_d b b.2 hbN
    show α b * b⁻¹ ∈ (Tb ⊓ Ki).subgroupOf Ki
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hα, Subgroup.coe_inv]
    have e : x * (b : Q) * x⁻¹ * (b : Q)⁻¹ = ((b : Q) * x * (b : Q)⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact (Tb ⊓ Ki).inv_mem h1
  have hα1 := hSzC ↥Ki n hSzi α ⟨1, by rw [pow_one]; exact hα3⟩ Sy hS1 hS2
  intro k hk
  have := congrArg (fun β : MulAut ↥Ki => ((β ⟨k, hk⟩ : ↥Ki) : Q)) hα1
  rw [show x * k * x⁻¹ = ((α ⟨k, hk⟩ : ↥Ki) : Q) from (hα ⟨k, hk⟩).symm]
  simpa using this

end SzCase

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem L1_le_closure_cube :
    S.L1 ≤ Subgroup.closure {x : G | x ∈ S.L1 ∧ x ^ 3 = 1} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcube : ∀ x ∈ S.L1, x ^ 3 ∈ pCoreOf 2 S.L1 := fun x hx => by
    by_cases hhat : IsHatA6 L
    · exact S.cube_mem_pCoreOf_L1_hat hhat hx
    · exact S.cube_mem_pCoreOf_L1 hhat hx
  show oTwoRes (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) ≤ _
  rw [oTwoRes, Subgroup.closure_le]
  rintro x ⟨hx, m, hm, hxm⟩
  have hxL1 : x ∈ S.L1 := mem_oTwoRes_of_odd hx hm hxm
  refine Subgroup.subset_closure ⟨hxL1, ?_⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, hcube x hxL1⟩
  have hk' : (x ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : (x ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h1)
  rw [(Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)).gcd_eq_one, Nat.dvd_one,
    orderOf_eq_one_iff] at h
  exact h

theorem L1_le_normalizer_of_ncard_two {H : Subgroup G}
    (hH : H ∈ S.Hz) {K : Subgroup G} (h2 : Set.ncard (conjSubgroupsBy H K) = 2) :
    S.L1 ≤ Subgroup.normalizer (K : Set G) := by
  refine S.L1_le_closure_cube.trans ((Subgroup.closure_le _).mpr ?_)
  rintro x ⟨hx, hx3⟩
  exact SzCase.mem_normalizer_of_ncard_two h2 ((le_sup_left.trans hH.1.1) hx) hx3

theorem isTwoThreeGroup_L1T (h1334 : Stmt13_3_4) (hS : S.Hyp138) :
    IsTwoThreeGroup (S.L1 ⊔ T) := by
  have h23 := (h1334 G T L V S.h13 S.irr).2.2
  refine h23 _ le_sup_right ?_
  refine lt_of_le_of_ne (sup_le_sup_right S.L1_le_L T) fun h => ?_
  have hL : L ≤ S.G1 := le_sup_left.trans (h.symm ▸ S.L1T_le_G1 hS)
  apply S.z_ne_one
  have hz : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨S.z_mem_V, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hL hl)
  rw [S.zv] at hz
  exact hz

theorem inf_G1_le_normalizer_L1 :
    Subgroup.normalizer (L : Set G) ⊓ S.G1 ≤ Subgroup.normalizer (S.L1 : Set G) := by
  refine A5.le_normalizer_oTwoRes_of_le_normalizer (F7.le_normalizer_inf inf_le_left
    ((?_ : Subgroup.normalizer (L : Set G) ⊓ S.G1 ≤ Subgroup.normalizer (fsuV1 T V : Set G)).trans
      Subgroup.le_normalizer))
  intro g hg
  have hgz : g * S.z * g⁻¹ = S.z := by
    have h1 : g ∈ S.G1 := hg.2
    rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
    rw [h1, mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro w
  rw [S.mem_V1_iff, S.mem_V1_iff]
  constructor
  · rintro (h | h)
    · left
      rw [h, mul_one, mul_inv_cancel]
    · right
      rw [h, hgz]
  · rintro (h | h)
    · left
      have : w = g⁻¹ * (g * w * g⁻¹) * g := by group
      rw [this, h]
      group
    · right
      have hgz' : g⁻¹ * S.z * g = S.z := by
        conv_lhs => rw [← hgz]
        group
      have : w = g⁻¹ * (g * w * g⁻¹) * g := by group
      rw [this, h, hgz']

theorem comm_L1_K0_of_Sz
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hSzC : SzCent) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (hne : conjClosure K T ≠ K) {n : ℕ}
    (hSz : IsSz n (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ∀ x ∈ S.L1, ∀ k ∈ conjClosure K T, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hℓH : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hcard2 : Set.ncard (conjSubgroupsBy H K) = 2 := by
    rcases CFSG.Quasithin.lemma_1_2_1_three S.h13.qtke S.h13.simple S.h13.nonabelian h37 h38
      hH.1.2 hK with hn | ⟨h2, -⟩
    · exact absurd (L32Case.conjClosure_eq_of_normal hKH hTH hn) hne
    · exact h2
  have hL1K : S.L1 ≤ Subgroup.normalizer (K : Set G) := S.L1_le_normalizer_of_ncard_two hH hcard2
  have hO₂T : pCoreOf 2 S.L1 ≤ T := by
    have hTs : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow le_top
    have hsup : IsPGroup 2 ↥(T ⊔ pCoreOf 2 S.L1) :=
      hTs.2.1.to_sup_of_normal_right' (pCoreOf_isPGroup 2 S.L1)
        (S.T_le_normalizer_L1.trans (normalizer_le_normalizer_pCoreOf 2 S.L1))
    exact le_sup_right.trans (L2Comm.le_of_isSylowTwoOf hTs le_sup_left le_top hsup)
  have hN₀ : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Kb := (K.subgroupOf H).map π with hKb
  set Tb := (T.subgroupOf H).map π with hTb
  have hKbc : Kb ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := modO2Image_mem_cComp hK
  have hTbs : IsSylowTwoOf Tb ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hTsyl) π hπs
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  obtain ⟨-, hL2'⟩ := h38 _ hQ Kb hKbc
  rcases hL2' Tb hTbs with ⟨hnorm, -, -⟩ | ⟨t, htT, -, hconj, -, hcomm', hinf, hTN, -⟩
  · exact absurd (L32Case.conjClosure_eq_of_normal hKH hTH (normal_of_normal_map_of_mem_cComp
      (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H) (subgroupOf_mem_cComp hK) hnorm)) hne
  obtain ⟨t₀, ht₀, rfl⟩ := htT
  have ht₀T : (t₀ : G) ∈ T := Subgroup.mem_subgroupOf.mp ht₀
  set K₂ := Kb.map (MulAut.conj (π t₀)).toMonoidHom with hK₂
  have hK₂eq : K₂ = ((K.map (MulAut.conj (t₀ : G)).toMonoidHom).subgroupOf H).map π :=
    (modO2Image_conj t₀).symm
  have hL1K' : S.L1 ≤ Subgroup.normalizer ((K.map (MulAut.conj (t₀ : G)).toMonoidHom :
      Subgroup G) : Set G) := by
    intro x hx
    have hx' : (t₀ : G)⁻¹ * x * (t₀ : G) ∈ S.L1 := by
      have := (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 (T.inv_mem ht₀T)) x).mp hx
      simpa using this
    have h1 := hL1K hx'
    rw [← A38.map_conj_eq_iff] at h1 ⊢
    ext y
    rw [A38.mem_map_conj, A38.mem_map_conj, A38.mem_map_conj]
    have h2 : (t₀ : G)⁻¹ * (x⁻¹ * y * x) * (t₀ : G) ∈ K ↔
        ((t₀ : G)⁻¹ * x * (t₀ : G))⁻¹ * ((t₀ : G)⁻¹ * y * (t₀ : G)) *
          ((t₀ : G)⁻¹ * x * (t₀ : G)) ∈ K := by
      constructor <;> intro h <;> convert h using 1 <;> group
    rw [h2, ← A38.mem_map_conj, h1]
  set Lb := (S.L1.subgroupOf H).map π with hLb
  have hLKb : Lb ≤ Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    L32Case.map_le_normalizer_map hL1K π
  have hLK₂ : Lb ≤ Subgroup.normalizer (K₂ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [hK₂eq]
    exact L32Case.map_le_normalizer_map hL1K' π
  have hcomm : ∀ x ∈ Kb, ∀ y ∈ K₂, x * y = y * x :=
    L32Comm.mul_comm_of_commutator_eq_bot hcomm'
  have hcomm2 : ∀ x ∈ K₂, ∀ y ∈ Kb, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hK₂c : K₂ ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := A38.cComp_conj hKbc
  have hU₁ : IsSylowTwoOf (Tb ⊓ Kb) Kb :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hKbc) hTbs
  have hU₂ : IsSylowTwoOf (Tb ⊓ K₂) K₂ :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK₂c) hTbs
  have hK0N1 : Kb ⊔ K₂ ≤ Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    sup_le Subgroup.le_normalizer fun x hx => L2Comm.mem_normalizer_of_comm hcomm le_rfl hx
  have hK0N2 : Kb ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    sup_le (fun x hx => L2Comm.mem_normalizer_of_comm hcomm2 le_rfl hx) Subgroup.le_normalizer
  obtain ⟨e₁⟩ := modO2_mulEquiv hK
  have h3Kb : ¬ 3 ∣ Nat.card Kb := by
    intro h
    apply SzCase.not_three_dvd_of_isSz hSz
    rw [Nat.card_congr e₁.toEquiv]
    exact h
  have h3K₂ : ¬ 3 ∣ Nat.card K₂ := by
    rw [← Nat.card_congr (A38.conjEquiv (π t₀) Kb).toEquiv]
    exact h3Kb
  have h3K0 : ¬ 3 ∣ Nat.card ↥(Kb ⊔ K₂) := fun h => by
    have h1 := h.trans (SzCase.card_sup_dvd_of_comm hcomm)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2
    · exact h3Kb h2
    · exact h3K₂ h2
  set Rb := ((S.L1 ⊔ T).subgroupOf H).map π with hRb
  have hLR : Lb ≤ Rb := Subgroup.map_mono fun x hx => (le_sup_left : S.L1 ≤ S.L1 ⊔ T) hx
  have hTR : Tb ≤ Rb := Subgroup.map_mono fun x hx => (le_sup_right : T ≤ S.L1 ⊔ T) hx
  have hR23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card Rb → p = 2 ∨ p = 3 := by
    intro p hp hpd
    have h1 : Nat.card Rb ∣ Nat.card ↥(S.L1 ⊔ T) := by
      refine (Subgroup.card_map_dvd _ π).trans ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hℓH hTH)).toEquiv]
    exact S.isTwoThreeGroup_L1T h1334 hS p hp (hpd.trans h1)
  have hRK : Rb ⊓ (Kb ⊔ K₂) ≤ Tb := by
    have h2 : IsPGroup 2 ↥(Rb ⊓ (Kb ⊔ K₂)) := by
      intro y
      have hdR : orderOf (y : ↥H ⧸ CFSG.pCore 2 ↥H) ∣ Nat.card Rb := by
        have := orderOf_dvd_natCard (⟨y, y.2.1⟩ : Rb)
        rwa [Subgroup.orderOf_mk] at this
      have hdK : orderOf (y : ↥H ⧸ CFSG.pCore 2 ↥H) ∣ Nat.card ↥(Kb ⊔ K₂) := by
        have := orderOf_dvd_natCard (⟨y, y.2.2⟩ : ↥(Kb ⊔ K₂))
        rwa [Subgroup.orderOf_mk] at this
      have hpow : ∀ p : ℕ, p.Prime → p ∣ orderOf (y : ↥H ⧸ CFSG.pCore 2 ↥H) → p = 2 := by
        intro p hp hpd
        rcases hR23 p hp (hpd.trans hdR) with h | h
        · exact h
        · exact absurd (h ▸ hpd.trans hdK) h3K0
      have hk := Nat.eq_prime_pow_of_unique_prime_dvd
        (orderOf_pos (y : ↥H ⧸ CFSG.pCore 2 ↥H)).ne' (fun {d} hd hdn => hpow d hd hdn)
      exact ⟨_, Subtype.ext (by
        rw [Subgroup.coe_pow, ← hk, pow_orderOf_eq_one, Subgroup.coe_one])⟩
    have hTN' : Tb ≤ Subgroup.normalizer ((Rb ⊓ (Kb ⊔ K₂) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      F7.le_normalizer_inf (hTR.trans Subgroup.le_normalizer) hTN
    have hsup : IsPGroup 2 ↥(Tb ⊔ (Rb ⊓ (Kb ⊔ K₂))) := hTbs.2.1.to_sup_of_normal_right' h2 hTN'
    exact le_sup_right.trans (L2Comm.le_of_isSylowTwoOf hTbs le_sup_left le_top hsup)
  have hLW : Lb ≤ Subgroup.normalizer ((Tb ⊓ (Kb ⊔ K₂) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine A5.le_normalizer_of_forall_conj_mem fun x hx u hu => ?_
    have hxK0 : x ∈ Subgroup.normalizer ((Kb ⊔ K₂ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [← A38.map_conj_eq_iff, Subgroup.map_sup, A38.map_conj_eq_iff.mpr (hLKb hx),
        A38.map_conj_eq_iff.mpr (hLK₂ hx)]
    have h1 : x * u * x⁻¹ ∈ Kb ⊔ K₂ := (Subgroup.mem_normalizer_iff.mp hxK0 u).mp hu.2
    have h2 : x * u * x⁻¹ ∈ Rb :=
      Rb.mul_mem (Rb.mul_mem (hLR hx) (hTR hu.1)) (Rb.inv_mem (hLR hx))
    exact ⟨hRK ⟨h2, h1⟩, h1⟩
  have hLU₁ : Lb ≤ Subgroup.normalizer ((Tb ⊓ Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    intro x hx
    have h1 := F7.mem_normalizer_inf (hLW hx) (hLKb hx)
    have e : Tb ⊓ (Kb ⊔ K₂) ⊓ Kb = Tb ⊓ Kb := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_left : Kb ≤ Kb ⊔ K₂)]
    rwa [e] at h1
  have hLU₂ : Lb ≤ Subgroup.normalizer ((Tb ⊓ K₂ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    intro x hx
    have h1 := F7.mem_normalizer_inf (hLW hx) (hLK₂ hx)
    have e : Tb ⊓ (Kb ⊔ K₂) ⊓ K₂ = Tb ⊓ K₂ := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_right : K₂ ≤ Kb ⊔ K₂)]
    rwa [e] at h1
  set B := (Kb ⊔ K₂) ⊓ Subgroup.normalizer ((Tb ⊓ Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
    Set (↥H ⧸ CFSG.pCore 2 ↥H)) ⊓ Subgroup.normalizer ((Tb ⊓ K₂ :
      Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) with hB
  have hBsol : Group.IsSolvable B := L2Comm.isSolvable_borel hcomm hinf hU₁ hU₂
  have hW : (Tb ⊓ Kb) ⊔ (Tb ⊓ K₂) = Tb ⊓ (Kb ⊔ K₂) := by
    apply le_antisymm
    · exact sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
    · intro u hu
      obtain ⟨k, hk⟩ := L32Comm.exists_pow_of_isPGroup hTbs.2.1 hu.1
      refine L2Comm.mem_sup_of_two_elt hcomm hinf hU₁ hU₂ hu.2 ?_ ?_ hk
      · exact F7.mem_normalizer_inf (Subgroup.le_normalizer hu.1) (hK0N1 hu.2)
      · exact F7.mem_normalizer_inf (Subgroup.le_normalizer hu.1) (hK0N2 hu.2)
  have hTB : Tb ≤ Subgroup.normalizer (B : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine A5.le_normalizer_of_forall_conj_mem fun s hs g hg => ?_
    have hgW : g ∈ Subgroup.normalizer ((Tb ⊓ (Kb ⊔ K₂) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [← hW, ← A38.map_conj_eq_iff, Subgroup.map_sup, A38.map_conj_eq_iff.mpr hg.1.2,
        A38.map_conj_eq_iff.mpr hg.2]
    have hsW : s ∈ Subgroup.normalizer ((Tb ⊓ (Kb ⊔ K₂) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      F7.mem_normalizer_inf (Subgroup.le_normalizer hs) (hTN hs)
    have hsg : s * g * s⁻¹ ∈ Subgroup.normalizer ((Tb ⊓ (Kb ⊔ K₂) :
        Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hsW hgW) (Subgroup.inv_mem _ hsW)
    have hsgK : s * g * s⁻¹ ∈ Kb ⊔ K₂ := (Subgroup.mem_normalizer_iff.mp (hTN hs) g).mp hg.1.1
    refine ⟨⟨hsgK, ?_⟩, ?_⟩
    · have h1 := F7.mem_normalizer_inf hsg (hK0N1 hsgK)
      have e : Tb ⊓ (Kb ⊔ K₂) ⊓ Kb = Tb ⊓ Kb := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_left : Kb ≤ Kb ⊔ K₂)]
      rwa [e] at h1
    · have h1 := F7.mem_normalizer_inf hsg (hK0N2 hsgK)
      have e : Tb ⊓ (Kb ⊔ K₂) ⊓ K₂ = Tb ⊓ K₂ := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : K₂ ≤ Kb ⊔ K₂)]
      rwa [e] at h1
  have hLB : Lb ≤ Subgroup.normalizer (B : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine A5.le_normalizer_of_forall_conj_mem fun x hx g hg => ?_
    have hxK0 : x ∈ Subgroup.normalizer ((Kb ⊔ K₂ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [← A38.map_conj_eq_iff, Subgroup.map_sup, A38.map_conj_eq_iff.mpr (hLKb hx),
        A38.map_conj_eq_iff.mpr (hLK₂ hx)]
    refine ⟨⟨(Subgroup.mem_normalizer_iff.mp hxK0 g).mp hg.1.1, ?_⟩, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLU₁ hx) hg.1.2) (Subgroup.inv_mem _ (hLU₁ hx))
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLU₂ hx) hg.2) (Subgroup.inv_mem _ (hLU₂ hx))
  have hReq : Rb = Lb ⊔ Tb := by
    rw [hRb, Subgroup.subgroupOf_sup hℓH hTH, Subgroup.map_sup]
  have hRB : Rb ≤ Subgroup.normalizer (B : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [hReq]
    exact sup_le hLB hTB
  have hRsol : Group.IsSolvable Rb := by
    have h1 : Group.IsSolvable ↥((S.L1 ⊔ T).subgroupOf H) := by
      have := S.isSolvable_L1T h1334 hS
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe (sup_le hℓH hTH)).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective π _)
  have hYbsol : Group.IsSolvable ↥(B ⊔ Rb) :=
    C126.isSolvable_sup_of_le_normalizer' hRB hBsol hRsol
  set Y := ((B ⊔ Rb).comap π).map H.subtype with hY
  have hkerπ : Group.IsSolvable π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact isSolvable_pCore_two_group ↥H
  have hYsol : Group.IsSolvable Y := by
    have h1 := L2Case.isSolvable_comap π hkerπ hYbsol
    exact Group.isSolvable_of_surjective
      (f := (((B ⊔ Rb).comap π).equivMapOfInjective _ H.subtype_injective).toMonoidHom)
      (MulEquiv.surjective _)
  have hL1TY : S.L1 ⊔ T ≤ Y := by
    intro x hx
    have hxH : x ∈ H := sup_le hℓH hTH hx
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    show π ⟨x, hxH⟩ ∈ B ⊔ Rb
    exact Subgroup.mem_sup_right ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hYG1 : Y ≤ S.G1 := (Subgroup.map_subtype_le _).trans hH.2.1
  have hYM : Y ≤ Subgroup.normalizer (L : Set G) := h13 G T L V S hS Y hL1TY hYG1 hYsol
  set B₀ := (B.comap π).map H.subtype with hB₀
  have hB₀Y : B₀ ≤ Y := Subgroup.map_mono (Subgroup.comap_mono le_sup_left)
  have hB₀L : B₀ ≤ Subgroup.normalizer (S.L1 : Set G) :=
    (le_inf (hB₀Y.trans hYM) ((Subgroup.map_subtype_le _).trans hH.2.1)).trans
      S.inf_G1_le_normalizer_L1
  have hBL : B ≤ Subgroup.normalizer (Lb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    have h1 := L32Case.map_le_normalizer_map hB₀L π
    have e : (B₀.subgroupOf H).map π = B := by
      rw [hB₀, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective,
        Subgroup.map_comap_eq_self_of_surjective hπs]
    rwa [e] at h1
  have h3B : ¬ 3 ∣ Nat.card B := fun h =>
    h3K0 (h.trans (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)))
  have hLBT : ∀ w ∈ Lb, w ∈ B → w ∈ Tb := by
    intro w hwL hwB
    obtain ⟨y, hy, rfl⟩ := hwL
    have hy' : (y : G) ∈ S.L1 := Subgroup.mem_subgroupOf.mp hy
    have hcube : (y : G) ^ 3 ∈ pCoreOf 2 S.L1 := by
      by_cases hhat : IsHatA6 L
      · exact S.cube_mem_pCoreOf_L1_hat hhat hy'
      · exact S.cube_mem_pCoreOf_L1 hhat hy'
    have h1 : π y ^ 3 ∈ Tb := by
      rw [← map_pow]
      exact ⟨y ^ 3, Subgroup.mem_subgroupOf.mpr (by simpa using hO₂T hcube), rfl⟩
    have hcop : Nat.Coprime 3 (orderOf (π y)) := by
      have h2 : orderOf (π y) ∣ Nat.card B := by
        have := orderOf_dvd_natCard (⟨π y, hwB⟩ : B)
        rwa [Subgroup.orderOf_mk] at this
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => h3B (h.trans h2)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Tb.pow_mem h1 m
  have key := fun (Ki : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) (hSzi : IsSz n ↥Ki) hUi hLKi hLUi hKiB =>
    SzCase.centralizes_of_szCent hSzC (B := B) hSzi hUi hLKi hLUi hKiB hBL hLB hLBT
  have hSzKb : IsSz n ↥Kb := isSz_congr e₁ hSz
  have hSzK₂ : IsSz n ↥K₂ := isSz_congr (e₁.trans (A38.conjEquiv (π t₀) Kb)) hSz
  have hKbB : ∀ d ∈ Kb, d ∈ Subgroup.normalizer ((Tb ⊓ Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H)) → d ∈ B := fun d hd hdN =>
    ⟨⟨Subgroup.mem_sup_left hd, hdN⟩, L2Comm.mem_normalizer_of_comm hcomm2 hU₂.1 hd⟩
  have hK₂B : ∀ d ∈ K₂, d ∈ Subgroup.normalizer ((Tb ⊓ K₂ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H)) → d ∈ B := fun d hd hdN =>
    ⟨⟨Subgroup.mem_sup_right hd, L2Comm.mem_normalizer_of_comm hcomm hU₁.1 hd⟩, hdN⟩
  have hcent : ∀ x ∈ Lb, x ^ 3 = 1 → ∀ q ∈ Kb ⊔ K₂, x * q = q * x := by
    intro x hx hx3 q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := L32Comm.exists_mul_of_mem_sup hcomm hq
    have h1 := key Kb hSzKb hU₁ hLKb hLU₁ hKbB x hx hx3 a ha
    have h2 := key K₂ hSzK₂ hU₂ hLK₂ hLU₂ hK₂B x hx hx3 b hb
    calc x * (a * b) = (x * a * x⁻¹) * (x * b * x⁻¹) * x := by group
      _ = a * b * x := by rw [h1, h2]
  set Z := ((Subgroup.centralizer ((Kb ⊔ K₂ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
    Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap π).map H.subtype with hZ
  have hL1Z : S.L1 ≤ Z := by
    refine S.L1_le_closure_cube.trans ((Subgroup.closure_le _).mpr ?_)
    rintro x ⟨hx, hx3⟩
    refine ⟨⟨x, hℓH hx⟩, ?_, rfl⟩
    show π ⟨x, hℓH hx⟩ ∈ Subgroup.centralizer ((Kb ⊔ K₂ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H))
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hxL : π ⟨x, hℓH hx⟩ ∈ Lb := ⟨⟨x, hℓH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hx3' : π ⟨x, hℓH hx⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hℓH hx⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simp [hx3])
      rw [this, map_one]
    exact (hcent _ hxL hx3' q hq).symm
  have hK0 : ∀ k ∈ conjClosure K T, ∀ hk : k ∈ H, π ⟨k, hk⟩ ∈ Kb ⊔ K₂ := by
    have hcc : (conjClosure (K.subgroupOf H) (T.subgroupOf H)).map H.subtype =
        conjClosure K T := by
      rw [A3.map_conjClosure, Subgroup.map_subgroupOf_eq_of_le hKH,
        Subgroup.map_subgroupOf_eq_of_le hTH]
    have hcl : conjClosure (K.subgroupOf H) (T.subgroupOf H) ≤ (Kb ⊔ K₂).comap π := by
      refine conjClosure_le fun s hs k hk => ?_
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      have hs' : π s ∈ Tb := Subgroup.mem_map_of_mem π hs
      have hk' : π k ∈ Kb := Subgroup.mem_map_of_mem π hk
      have hmem : Kb.map (MulAut.conj (π s)).toMonoidHom ∈ conjSubgroupsBy Tb Kb :=
        ⟨π s, hs', rfl⟩
      rw [hconj] at hmem
      have hsk : π s * π k * (π s)⁻¹ ∈ Kb.map (MulAut.conj (π s)).toMonoidHom :=
        ⟨π k, hk', by simp [MulAut.conj_apply]⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · rw [h] at hsk
        exact Subgroup.mem_sup_left hsk
      · rw [h] at hsk
        exact Subgroup.mem_sup_right hsk
    intro k hk hkH
    rw [← hcc] at hk
    obtain ⟨z, hz, hzk⟩ := hk
    have hzk' : z = ⟨k, hkH⟩ := Subtype.ext hzk
    rw [← hzk']
    exact hcl hz
  intro x hx k hk
  have hkH : k ∈ H := (conjClosure_le fun s hs y hy =>
    H.mul_mem (H.mul_mem (hTH hs) (hKH hy)) (H.inv_mem (hTH hs))) hk
  obtain ⟨xz, hxz, hxzx⟩ := hL1Z hx
  have hxH : x ∈ H := hℓH hx
  have hxz' : xz = ⟨x, hxH⟩ := Subtype.ext hxzx
  rw [hxz'] at hxz
  have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hxz) _ (hK0 k hk hkH)
  have h1 : π (⟨x, hxH⟩ * ⟨k, hkH⟩ * ⟨x, hxH⟩⁻¹ * ⟨k, hkH⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  have h3 : (⟨x * k * x⁻¹ * k⁻¹, H.mul_mem (H.mul_mem (H.mul_mem hxH hkH) (H.inv_mem hxH))
      (H.inv_mem hkH)⟩ : ↥H) ∈ (pCoreOf 2 H).subgroupOf H := by
    rw [pCoreOf_subgroupOf_eq]
    exact h2
  exact Subgroup.mem_subgroupOf.mp h3

theorem comm_L1_K_of_Sz_normal
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (hSzC : SzCent) (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKN : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (hSz : IsSz n (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ∀ x ∈ S.L1, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hℓH : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hO₂T : pCoreOf 2 S.L1 ≤ T := by
    have hTs : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow le_top
    have hsup : IsPGroup 2 ↥(T ⊔ pCoreOf 2 S.L1) :=
      hTs.2.1.to_sup_of_normal_right' (pCoreOf_isPGroup 2 S.L1)
        (S.T_le_normalizer_L1.trans (normalizer_le_normalizer_pCoreOf 2 S.L1))
    exact le_sup_right.trans (L2Comm.le_of_isSylowTwoOf hTs le_sup_left le_top hsup)
  have hN₀ : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Kb := (K.subgroupOf H).map π with hKb
  set Tb := (T.subgroupOf H).map π with hTb
  have hKbc : Kb ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := modO2Image_mem_cComp hK
  have hTbs : IsSylowTwoOf Tb ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hTsyl) π hπs
  set Lb := (S.L1.subgroupOf H).map π with hLb
  have hLKb : Lb ≤ Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    L32Case.map_le_normalizer_map (hℓH.trans hKN) π
  have hTKb : Tb ≤ Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    L32Case.map_le_normalizer_map (hTH.trans hKN) π
  have hU₁ : IsSylowTwoOf (Tb ⊓ Kb) Kb :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hKbc) hTbs
  obtain ⟨e₁⟩ := modO2_mulEquiv hK
  have h3Kb : ¬ 3 ∣ Nat.card Kb := by
    intro h
    apply SzCase.not_three_dvd_of_isSz hSz
    rw [Nat.card_congr e₁.toEquiv]
    exact h
  set Rb := ((S.L1 ⊔ T).subgroupOf H).map π with hRb
  have hLR : Lb ≤ Rb := Subgroup.map_mono fun x hx => (le_sup_left : S.L1 ≤ S.L1 ⊔ T) hx
  have hTR : Tb ≤ Rb := Subgroup.map_mono fun x hx => (le_sup_right : T ≤ S.L1 ⊔ T) hx
  have hR23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card Rb → p = 2 ∨ p = 3 := by
    intro p hp hpd
    have h1 : Nat.card Rb ∣ Nat.card ↥(S.L1 ⊔ T) := by
      refine (Subgroup.card_map_dvd _ π).trans ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hℓH hTH)).toEquiv]
    exact S.isTwoThreeGroup_L1T h1334 hS p hp (hpd.trans h1)
  have hRK : Rb ⊓ Kb ≤ Tb := by
    have h2 : IsPGroup 2 ↥(Rb ⊓ Kb) := by
      intro y
      have hdR : orderOf (y : ↥H ⧸ CFSG.pCore 2 ↥H) ∣ Nat.card Rb := by
        have := orderOf_dvd_natCard (⟨y, y.2.1⟩ : Rb)
        rwa [Subgroup.orderOf_mk] at this
      have hdK : orderOf (y : ↥H ⧸ CFSG.pCore 2 ↥H) ∣ Nat.card Kb := by
        have := orderOf_dvd_natCard (⟨y, y.2.2⟩ : Kb)
        rwa [Subgroup.orderOf_mk] at this
      have hpow : ∀ p : ℕ, p.Prime → p ∣ orderOf (y : ↥H ⧸ CFSG.pCore 2 ↥H) → p = 2 := by
        intro p hp hpd
        rcases hR23 p hp (hpd.trans hdR) with h | h
        · exact h
        · exact absurd (h ▸ hpd.trans hdK) h3Kb
      have hk := Nat.eq_prime_pow_of_unique_prime_dvd
        (orderOf_pos (y : ↥H ⧸ CFSG.pCore 2 ↥H)).ne' (fun {d} hd hdn => hpow d hd hdn)
      exact ⟨_, Subtype.ext (by
        rw [Subgroup.coe_pow, ← hk, pow_orderOf_eq_one, Subgroup.coe_one])⟩
    have hTN' : Tb ≤ Subgroup.normalizer ((Rb ⊓ Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      F7.le_normalizer_inf (hTR.trans Subgroup.le_normalizer) hTKb
    have hsup : IsPGroup 2 ↥(Tb ⊔ (Rb ⊓ Kb)) := hTbs.2.1.to_sup_of_normal_right' h2 hTN'
    exact le_sup_right.trans (L2Comm.le_of_isSylowTwoOf hTbs le_sup_left le_top hsup)
  have hLU₁ : Lb ≤ Subgroup.normalizer ((Tb ⊓ Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine A5.le_normalizer_of_forall_conj_mem fun x hx u hu => ?_
    have h1 : x * u * x⁻¹ ∈ Kb := (Subgroup.mem_normalizer_iff.mp (hLKb hx) u).mp hu.2
    have h2 : x * u * x⁻¹ ∈ Rb :=
      Rb.mul_mem (Rb.mul_mem (hLR hx) (hTR hu.1)) (Rb.inv_mem (hLR hx))
    exact ⟨hRK ⟨h2, h1⟩, h1⟩
  have hcomm0 : ∀ x ∈ Kb, ∀ y ∈ (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)), x * y = y * x := by
    intro x _ y hy
    rw [Subgroup.mem_bot.mp hy, mul_one, one_mul]
  have hinf0 : Kb ⊓ (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) = ⊥ := inf_bot_eq _
  have hU0 : IsSylowTwoOf (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ⊥ :=
    ⟨le_rfl, IsPGroup.of_bot, by
      rw [Subgroup.subgroupOf_self, Subgroup.index_top]
      norm_num⟩
  set B := (Kb ⊔ ⊥) ⊓ Subgroup.normalizer ((Tb ⊓ Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
    Set (↥H ⧸ CFSG.pCore 2 ↥H)) ⊓ Subgroup.normalizer (((⊥ :
      Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) with hB
  have hBsol : Group.IsSolvable B := L2Comm.isSolvable_borel hcomm0 hinf0 hU₁ hU0
  have hN0 : ∀ g : ↥H ⧸ CFSG.pCore 2 ↥H, g ∈ Subgroup.normalizer
      (((⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := fun g => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro h1
      have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
      rw [this, h1]
      group
  have hTB : Tb ≤ Subgroup.normalizer (B : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine A5.le_normalizer_of_forall_conj_mem fun s hs g hg => ?_
    have hsU : s ∈ Subgroup.normalizer ((Tb ⊓ Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      F7.mem_normalizer_inf (Subgroup.le_normalizer hs) (hTKb hs)
    refine ⟨⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hsU hg.1.2) (Subgroup.inv_mem _ hsU)⟩,
      hN0 _⟩
    have hgK : g ∈ Kb := by simpa using hg.1.1
    exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hTKb hs) g).mp hgK)
  have hLB : Lb ≤ Subgroup.normalizer (B : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine A5.le_normalizer_of_forall_conj_mem fun x hx g hg => ?_
    refine ⟨⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLU₁ hx) hg.1.2)
      (Subgroup.inv_mem _ (hLU₁ hx))⟩, hN0 _⟩
    have hgK : g ∈ Kb := by simpa using hg.1.1
    exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hLKb hx) g).mp hgK)
  have hReq : Rb = Lb ⊔ Tb := by
    rw [hRb, Subgroup.subgroupOf_sup hℓH hTH, Subgroup.map_sup]
  have hRB : Rb ≤ Subgroup.normalizer (B : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [hReq]
    exact sup_le hLB hTB
  have hRsol : Group.IsSolvable Rb := by
    have h1 : Group.IsSolvable ↥((S.L1 ⊔ T).subgroupOf H) := by
      have := S.isSolvable_L1T h1334 hS
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe (sup_le hℓH hTH)).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective π _)
  have hYbsol : Group.IsSolvable ↥(B ⊔ Rb) :=
    C126.isSolvable_sup_of_le_normalizer' hRB hBsol hRsol
  set Y := ((B ⊔ Rb).comap π).map H.subtype with hY
  have hkerπ : Group.IsSolvable π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact isSolvable_pCore_two_group ↥H
  have hYsol : Group.IsSolvable Y := by
    have h1 := L2Case.isSolvable_comap π hkerπ hYbsol
    exact Group.isSolvable_of_surjective
      (f := (((B ⊔ Rb).comap π).equivMapOfInjective _ H.subtype_injective).toMonoidHom)
      (MulEquiv.surjective _)
  have hL1TY : S.L1 ⊔ T ≤ Y := by
    intro x hx
    have hxH : x ∈ H := sup_le hℓH hTH hx
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    show π ⟨x, hxH⟩ ∈ B ⊔ Rb
    exact Subgroup.mem_sup_right ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hYG1 : Y ≤ S.G1 := (Subgroup.map_subtype_le _).trans hH.2.1
  have hYM : Y ≤ Subgroup.normalizer (L : Set G) := h13 G T L V S hS Y hL1TY hYG1 hYsol
  set B₀ := (B.comap π).map H.subtype with hB₀
  have hB₀Y : B₀ ≤ Y := Subgroup.map_mono (Subgroup.comap_mono le_sup_left)
  have hB₀L : B₀ ≤ Subgroup.normalizer (S.L1 : Set G) :=
    (le_inf (hB₀Y.trans hYM) ((Subgroup.map_subtype_le _).trans hH.2.1)).trans
      S.inf_G1_le_normalizer_L1
  have hBL : B ≤ Subgroup.normalizer (Lb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    have h1 := L32Case.map_le_normalizer_map hB₀L π
    have e : (B₀.subgroupOf H).map π = B := by
      rw [hB₀, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective,
        Subgroup.map_comap_eq_self_of_surjective hπs]
    rwa [e] at h1
  have h3B : ¬ 3 ∣ Nat.card B := fun h => by
    apply h3Kb
    refine h.trans (Subgroup.card_dvd_of_le ?_)
    intro g hg
    simpa using hg.1.1
  have hLBT : ∀ w ∈ Lb, w ∈ B → w ∈ Tb := by
    intro w hwL hwB
    obtain ⟨y, hy, rfl⟩ := hwL
    have hy' : (y : G) ∈ S.L1 := Subgroup.mem_subgroupOf.mp hy
    have hcube : (y : G) ^ 3 ∈ pCoreOf 2 S.L1 := by
      by_cases hhat : IsHatA6 L
      · exact S.cube_mem_pCoreOf_L1_hat hhat hy'
      · exact S.cube_mem_pCoreOf_L1 hhat hy'
    have h1 : π y ^ 3 ∈ Tb := by
      rw [← map_pow]
      exact ⟨y ^ 3, Subgroup.mem_subgroupOf.mpr (by simpa using hO₂T hcube), rfl⟩
    have hcop : Nat.Coprime 3 (orderOf (π y)) := by
      have h2 : orderOf (π y) ∣ Nat.card B := by
        have := orderOf_dvd_natCard (⟨π y, hwB⟩ : B)
        rwa [Subgroup.orderOf_mk] at this
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => h3B (h.trans h2)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Tb.pow_mem h1 m
  have hSzKb : IsSz n ↥Kb := isSz_congr e₁ hSz
  have hKbB : ∀ d ∈ Kb, d ∈ Subgroup.normalizer ((Tb ⊓ Kb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H)) → d ∈ B := fun d hd hdN =>
    ⟨⟨Subgroup.mem_sup_left hd, hdN⟩, hN0 d⟩
  have hcent := SzCase.centralizes_of_szCent hSzC (B := B) hSzKb hU₁ hLKb hLU₁ hKbB hBL hLB hLBT
  set Z := ((Subgroup.centralizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap π).map H.subtype
    with hZ
  have hL1Z : S.L1 ≤ Z := by
    refine S.L1_le_closure_cube.trans ((Subgroup.closure_le _).mpr ?_)
    rintro x ⟨hx, hx3⟩
    refine ⟨⟨x, hℓH hx⟩, ?_, rfl⟩
    show π ⟨x, hℓH hx⟩ ∈ Subgroup.centralizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H))
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hxL : π ⟨x, hℓH hx⟩ ∈ Lb := ⟨⟨x, hℓH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hx3' : π ⟨x, hℓH hx⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hℓH hx⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simp [hx3])
      rw [this, map_one]
    have h1 := hcent _ hxL hx3' q hq
    calc q * π ⟨x, hℓH hx⟩ = π ⟨x, hℓH hx⟩ * q * (π ⟨x, hℓH hx⟩)⁻¹ * π ⟨x, hℓH hx⟩ := by
          rw [h1]
      _ = π ⟨x, hℓH hx⟩ * q := by group
  intro x hx k hk
  have hkH : k ∈ H := hKH hk
  obtain ⟨xz, hxz, hxzx⟩ := hL1Z hx
  have hxH : x ∈ H := hℓH hx
  have hxz' : xz = ⟨x, hxH⟩ := Subtype.ext hxzx
  rw [hxz'] at hxz
  have hkb : π ⟨k, hkH⟩ ∈ Kb := ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hxz) _ hkb
  have h1 : π (⟨x, hxH⟩ * ⟨k, hkH⟩ * ⟨x, hxH⟩⁻¹ * ⟨k, hkH⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  have h3 : (⟨x * k * x⁻¹ * k⁻¹, H.mul_mem (H.mul_mem (H.mul_mem hxH hkH) (H.inv_mem hxH))
      (H.inv_mem hkH)⟩ : ↥H) ∈ (pCoreOf 2 H).subgroupOf H := by
    rw [pCoreOf_subgroupOf_eq]
    exact h2
  exact Subgroup.mem_subgroupOf.mp h3

theorem normal_L1_of_comm (h139 : Stmt13_3_9)
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (hHeq : H = (K ⊔ T) ⊔ S.L1)
    (hcomm : ∀ x ∈ S.L1, ∀ k ∈ conjClosure K T, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) :
    ¬ IsHatA6 L ∧ H ≤ Subgroup.normalizer (S.L1 : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hℓH : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hOT : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le hTsyl
  set X := S.L1 ⊔ pCoreOf 2 H with hX
  have hON : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hmapX : ∀ g : G, g ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) →
      S.L1.map (MulAut.conj g).toMonoidHom ≤ X → g ∈ Subgroup.normalizer (X : Set G) := by
    intro g hgO hgL
    refine A5.le_normalizer_of_forall_conj_mem (X := Subgroup.zpowers g) ?_
      (Subgroup.mem_zpowers g)
    intro g' hg' y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
    have hXg : X.map (MulAut.conj g).toMonoidHom ≤ X := by
      rw [hX, Subgroup.map_sup, A38.map_conj_eq_iff.mpr hgO]
      exact sup_le hgL le_sup_right
    have key : ∀ m : ℕ, ∀ y ∈ X, g ^ m * y * (g ^ m)⁻¹ ∈ X := by
      intro m
      induction m with
      | zero => intro y hy; simpa using hy
      | succ m ih =>
        intro y hy
        have h1 : g * y * g⁻¹ ∈ X := hXg ⟨y, hy, by simp [MulAut.conj_apply]⟩
        have := ih _ h1
        have e : g ^ (m + 1) * y * (g ^ (m + 1))⁻¹ = g ^ m * (g * y * g⁻¹) * (g ^ m)⁻¹ := by
          rw [pow_succ]
          group
        rw [e]
        exact this
    have hfin : ∃ m : ℕ, g ^ j = g ^ m := by
      obtain ⟨m, hm⟩ : ∃ m : ℕ, (j : ℤ) % (orderOf g : ℤ) = m :=
        ⟨((j % (orderOf g : ℤ)).toNat), (Int.toNat_of_nonneg (Int.emod_nonneg _
          (by exact_mod_cast (orderOf_pos g).ne'))).symm⟩
      refine ⟨m, ?_⟩
      rw [← zpow_natCast, ← hm, zpow_mod_orderOf]
    obtain ⟨m, hm⟩ := hfin
    rw [hm]
    exact key m y hy
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := by
    intro k hk
    refine hmapX k (hON (hKH hk)) ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hcomm x⁻¹ (S.L1.inv_mem hx) k (le_conjClosure K T hk)
    have e : (MulAut.conj k).toMonoidHom x = x * (x⁻¹ * k * x⁻¹⁻¹ * k⁻¹) := by
      simp [MulAut.conj_apply]
      group
    rw [e]
    exact X.mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right h1)
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := fun t ht =>
    hmapX t (hON (hTH ht)) ((A38.map_conj_eq_iff.mpr (S.T_le_normalizer_L1 ht)).le.trans
      le_sup_left)
  have hLX : S.L1 ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    hmapX x (hON (hℓH hx)) ((A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer hx)).le.trans
      le_sup_left)
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [hHeq]
    exact sup_le (sup_le hKX hTX) hLX
  set Y := oTwoRes X with hY
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := A5.le_normalizer_oTwoRes_of_le_normalizer hHX
  have hYY : oTwoRes Y = Y := by
    refine le_antisymm (oTwoRes_le _) ?_
    rw [hY, oTwoRes, Subgroup.closure_le]
    rintro y ⟨hy, m, hm, hym⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hy, m, hm, hym⟩, m, hm, hym⟩
  have hYX : Y ≤ X := oTwoRes_le _
  have hXH : X ≤ H := sup_le hℓH (pCoreOf_le 2 H)
  have hXM : X ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (S.L1_le_L.trans Subgroup.le_normalizer) (hOT.trans S.T_le_NL)
  have hYz : Y ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({S.z} : Set G) :=
    le_inf (hYX.trans hXM) ((hYX.trans hXH).trans hH.2.1)
  have hz : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
  have hzL : S.z ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    have h1 : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, h⟩
    rw [S.zv, Subgroup.mem_bot] at h1
    exact S.z_ne_one h1
  have hLY : S.L1 ≤ Y := by
    have h1 : oTwoRes S.L1 = S.L1 := by
      refine le_antisymm (oTwoRes_le _) ?_
      show oTwoRes (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) ≤ _
      rw [oTwoRes, Subgroup.closure_le]
      rintro y ⟨hy, m, hm, hym⟩
      exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hy, m, hm, hym⟩, m, hm, hym⟩
    rw [← h1]
    exact oTwoRes_mono le_sup_left
  obtain ⟨ℓ, c, hℓ, -, hc, hc3, hcO, -⟩ := S.exists_ell
  have hc1 : c ≠ 1 := fun h => hcO (h ▸ Subgroup.one_mem _)
  rcases h139 G T L V H Y S.z S.h13 S.irr S.a6 ⟨hTH, hH.1.2⟩ hH.2.2 hYY (hYX.trans hXH) hHY hz
    hzL hYz with h | ⟨-, hA6, hhat⟩
  · exfalso
    have : c ∈ Y := hLY (hℓ hc)
    rw [h, Subgroup.mem_bot] at this
    exact hc1 this
  · have hnh : ¬ IsHatA6 L := by
      intro hh
      have h1 := hhat hh
      obtain ⟨c₀, hc₀, hc₀3, hc₀O, -⟩ := l0_decomp hh
      have h2 : c₀ ∈ l1plus T L V := h1 ▸ hLY (S.l0_le_L1 hc₀)
      have h3 : c₀ ∈ pCoreOf 2 L := S.hatL1Plus hh ⟨h2, oTwoRes_le _ hc₀⟩
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, h3⟩
      have hk' : c₀ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact hc₀O (by rw [L32Comm.eq_one_of_pow_of_cube hk' hc₀3]; exact Subgroup.one_mem _)
    refine ⟨hnh, ?_⟩
    have hYL : Y = S.L1 := hA6 (S.nonempty_alt6_of_not_hat hnh)
    rw [← hYL]
    exact hHY

end Setting4

@[expose] def Case13816SzPairMod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ¬ IsHatA6 L → ∀ H ∈ S.Hz, ∀ K ∈ cComp H, conjClosure K T ≠ K → H = (K ⊔ T) ⊔ S.L1 →
      H ≤ Subgroup.normalizer (S.L1 : Set G) →
      (∀ x ∈ S.L1, ∀ k ∈ conjClosure K T, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) →
        ¬ ∃ n, IsSz n (↥K ⧸ CFSG.pCore 2 ↥K)

theorem case13816SzPair_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4) (h139 : Stmt13_3_9)
    (h13 : Lem13813) (hSzC : SzCent) (hMod : Case13816SzPairMod) : Case13816SzPair := by
  intro G _ _ T L V S hS H hH K hK hne hHeq ⟨n, hSz⟩
  have hcomm := S.comm_L1_K0_of_Sz h37 h38 h1334 h13 hSzC hS hH hK hne hSz
  obtain ⟨hhat, hn⟩ := S.normal_L1_of_comm h139 hH hK hHeq hcomm
  exact hMod G T L V S hS hhat H hH K hK hne hHeq hn hcomm ⟨n, hSz⟩

@[expose] def Case13816SzNormalMod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ¬ IsHatA6 L → ∀ H ∈ S.Hz, ∀ K ∈ cComp H, H ≤ Subgroup.normalizer (K : Set G) →
      H = (K ⊔ T) ⊔ S.L1 → H ≤ Subgroup.normalizer (S.L1 : Set G) →
      (∀ x ∈ S.L1, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) →
        ¬ ∃ n, IsSz n (↥K ⧸ CFSG.pCore 2 ↥K)

theorem case13816SzNormal_of
    (h1334 : Stmt13_3_4) (h139 : Stmt13_3_9) (h13 : Lem13813) (hSzC : SzCent)
    (hMod : Case13816SzNormalMod) : Case13816SzNormal := by
  intro G _ _ T L V S hS H hH K hK hKN hHeq ⟨n, hSz⟩
  have hcomm := S.comm_L1_K_of_Sz_normal h1334 h13 hSzC hS hH hK hKN hSz
  have hKK : conjClosure K T = K := by
    refine le_antisymm (conjClosure_le fun t ht k hk => ?_) (le_conjClosure K T)
    exact (Subgroup.mem_normalizer_iff.mp (hKN (le_sup_right.trans hH.1.1 ht)) k).mp hk
  have hcomm' : ∀ x ∈ S.L1, ∀ k ∈ conjClosure K T, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    rw [hKK]
    exact hcomm
  obtain ⟨hhat, hn⟩ := S.normal_L1_of_comm h139 hH hK hHeq hcomm'
  exact hMod G T L V S hS hhat H hH K hK hKN hHeq hn hcomm ⟨n, hSz⟩

end CFSG.Quasithin.H13.A6

