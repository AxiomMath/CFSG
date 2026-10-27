module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Mod2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt Theorem614Four)

section CyclicCase

variable {Mg : Type} [Group Mg] [Finite Mg]

@[expose] def conjAutQ_uc6 {Q : Subgroup Mg} {n : Mg} (hn : n ∈ normalizer (Q : Set Mg)) :
    MulAut ↥Q where
  toFun x := ⟨n * x * n⁻¹, (mem_normalizer_iff.1 hn x).1 x.2⟩
  invFun x := ⟨n⁻¹ * x * n, by
    have := (mem_normalizer_iff.1 (inv_mem hn) x).1 x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conj_comm_of_isCyclic_uc6 {Q : Subgroup Mg} (hQ : IsCyclic ↥Q) {n n' : Mg}
    (hn : n ∈ normalizer (Q : Set Mg)) (hn' : n' ∈ normalizer (Q : Set Mg)) :
    ∀ q ∈ Q, n * (n' * q * n'⁻¹) * n⁻¹ = n' * (n * q * n⁻¹) * n'⁻¹ := by
  intro q hq
  have hcomm : conjAutQ_uc6 hn * conjAutQ_uc6 hn' = conjAutQ_uc6 hn' * conjAutQ_uc6 hn := by
    apply (IsCyclic.mulAutMulEquiv ↥Q).injective
    rw [map_mul, map_mul, mul_comm]
  have := congrArg (fun σ : MulAut ↥Q => ((σ ⟨q, hq⟩ : ↥Q) : Mg)) hcomm
  exact this

theorem commutator_centralizes_of_isCyclic_uc6 {Q : Subgroup Mg} (hQ : IsCyclic ↥Q) {n n' : Mg}
    (hn : n ∈ normalizer (Q : Set Mg)) (hn' : n' ∈ normalizer (Q : Set Mg)) :
    ∀ q ∈ Q, (n * n' * n⁻¹ * n'⁻¹) * q = q * (n * n' * n⁻¹ * n'⁻¹) := by
  intro q hq
  have hnn' : n' * n ∈ normalizer (Q : Set Mg) := mul_mem hn' hn
  have hx : (n' * n)⁻¹ * q * (n' * n) ∈ Q := by
    have := (mem_normalizer_iff.1 (inv_mem hnn') q).1 hq
    simpa using this
  have h1 := conj_comm_of_isCyclic_uc6 hQ hn hn' _ hx
  have e1 : n * (n' * ((n' * n)⁻¹ * q * (n' * n)) * n'⁻¹) * n⁻¹ =
      (n * n' * n⁻¹ * n'⁻¹) * q * (n * n' * n⁻¹ * n'⁻¹)⁻¹ := by group
  have e2 : n' * (n * ((n' * n)⁻¹ * q * (n' * n)) * n⁻¹) * n'⁻¹ = q := by group
  rw [e1, e2] at h1
  calc (n * n' * n⁻¹ * n'⁻¹) * q
      = ((n * n' * n⁻¹ * n'⁻¹) * q * (n * n' * n⁻¹ * n'⁻¹)⁻¹) * (n * n' * n⁻¹ * n'⁻¹) := by group
    _ = q * (n * n' * n⁻¹ * n'⁻¹) := by rw [h1]

theorem cyclic_case_uc6 (U : Subgroup Mg) [hU : U.Normal] (P Q Z : Subgroup Mg)
    (hFr : (⊤ : Subgroup Mg) = U ⊔ normalizer (P : Set Mg))
    (hQN : normalizer (P : Set Mg) ≤ normalizer (Q : Set Mg)) (hQc : IsCyclic ↥Q)
    (hZN : Z ≤ normalizer (P : Set Mg)) (hZc : Z ≤ ⁅(⊤ : Subgroup Mg), ⊤⁆)
    {r : ℕ} (hr : 1 < r) (hZr : ∀ z ∈ Z, z ^ r = 1) (hcop : Nat.Coprime r (Nat.card U)) :
    ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z := by
  set N : Subgroup Mg := normalizer (P : Set Mg) with hN
  set N₀ : Subgroup Mg := N ⊓ centralizer (Q : Set Mg) with hN₀
  have hNQ : ∀ n ∈ N, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q := fun n hn q hq =>
    (mem_normalizer_iff.1 (hQN hn) q).1 hq
  have hNN : ⁅N, N⁆ ≤ N₀ := by
    refine Subgroup.commutator_le.2 fun n hn n' hn' => ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn hn') (N.inv_mem hn)) (N.inv_mem hn')
    · show (n * n' * n⁻¹ * n'⁻¹) ∈ centralizer (Q : Set Mg)
      rw [mem_centralizer_iff]
      intro q hq
      exact (commutator_centralizes_of_isCyclic_uc6 hQc (hQN hn) (hQN hn') q hq).symm
  have hTop : ⁅(⊤ : Subgroup Mg), ⊤⁆ ≤ N₀ ⊔ U := by
    set π : Mg →* Mg ⧸ U := QuotientGroup.mk' U with hπ
    have hUbot : U.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
    have h1 : (⊤ : Subgroup Mg).map π = N.map π := by
      conv_lhs => rw [hFr]
      rw [Subgroup.map_sup, hUbot, bot_sup_eq]
    have h2 : Subgroup.map π ⁅(⊤ : Subgroup Mg), ⊤⁆ ≤ N₀.map π := by
      rw [Subgroup.map_commutator, h1, ← Subgroup.map_commutator]
      exact Subgroup.map_mono hNN
    calc ⁅(⊤ : Subgroup Mg), ⊤⁆ ≤ (Subgroup.map π ⁅(⊤ : Subgroup Mg), ⊤⁆).comap π :=
          Subgroup.le_comap_map _ _
      _ ≤ (N₀.map π).comap π := Subgroup.comap_mono h2
      _ = N₀ ⊔ U := by rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk']
  intro z hz q hq
  obtain ⟨n₀, hn₀, u, huU, hz'⟩ := Subgroup.mem_sup_of_normal_right.1 (hTop (hZc hz))
  have hzN : z ∈ N := hZN hz
  have huN : u ∈ N := by
    have : u = n₀⁻¹ * z := by rw [← hz']; group
    rw [this]
    exact N.mul_mem (N.inv_mem hn₀.1) hzN
  have hconj : ∀ x ∈ Q, z * x * z⁻¹ = u * x * u⁻¹ := by
    intro x hx
    have hux : u * x * u⁻¹ ∈ Q := hNQ u huN x hx
    have hc : n₀ * (u * x * u⁻¹) = (u * x * u⁻¹) * n₀ :=
      (mem_centralizer_iff.1 hn₀.2 _ hux).symm
    calc z * x * z⁻¹ = (n₀ * u) * x * (n₀ * u)⁻¹ := by rw [hz']
      _ = n₀ * (u * x * u⁻¹) * n₀⁻¹ := by group
      _ = (u * x * u⁻¹) * n₀ * n₀⁻¹ := by rw [hc]
      _ = u * x * u⁻¹ := by group
  have hpow : ∀ k : ℕ, ∀ x ∈ Q, z ^ k * x * (z ^ k)⁻¹ = u ^ k * x * (u ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x hx; simp
    | succ k ih =>
      intro x hx
      have hux : ∀ j : ℕ, u ^ j * x * (u ^ j)⁻¹ ∈ Q := by
        intro j
        induction j with
        | zero => simpa using hx
        | succ j ihj =>
          have := hNQ u huN _ ihj
          have e : u ^ (j + 1) * x * (u ^ (j + 1))⁻¹ = u * (u ^ j * x * (u ^ j)⁻¹) * u⁻¹ := by
            rw [pow_succ']; group
          rw [e]; exact this
      calc z ^ (k + 1) * x * (z ^ (k + 1))⁻¹ = z * (z ^ k * x * (z ^ k)⁻¹) * z⁻¹ := by
            rw [pow_succ']; group
        _ = z * (u ^ k * x * (u ^ k)⁻¹) * z⁻¹ := by rw [ih x hx]
        _ = u * (u ^ k * x * (u ^ k)⁻¹) * u⁻¹ := hconj _ (hux k)
        _ = u ^ (k + 1) * x * (u ^ (k + 1))⁻¹ := by rw [pow_succ']; group
  have huc : u ^ Nat.card U = 1 := by
    have h : ((⟨u, huU⟩ : ↥U) ^ Nat.card U : ↥U) = 1 := pow_card_eq_one'
    calc u ^ Nat.card U = (((⟨u, huU⟩ : ↥U) ^ Nat.card U : ↥U) : Mg) := rfl
      _ = 1 := by rw [h]; rfl
  have hzc : ∀ x ∈ Q, z ^ Nat.card U * x = x * z ^ Nat.card U := by
    intro x hx
    have := hpow (Nat.card U) x hx
    rw [huc] at this
    simp only [one_mul, inv_one, mul_one] at this
    calc z ^ Nat.card U * x = (z ^ Nat.card U * x * (z ^ Nat.card U)⁻¹) * z ^ Nat.card U := by group
      _ = x * z ^ Nat.card U := by rw [this]
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm hr
  have hzs : z = (z ^ Nat.card U) ^ s := by
    rw [← pow_mul]
    have h3 : Nat.card U * s = r * (Nat.card U * s / r) + 1 := by
      have := Nat.div_add_mod (Nat.card U * s) r
      omega
    rw [h3, pow_add, pow_mul, hZr z hz, one_pow, one_mul, pow_one]
  rw [hzs]
  exact ((Commute.pow_left (show Commute (z ^ Nat.card U) q from hzc q hq) s)).eq

end CyclicCase

section Transport

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_subgroupOf_iff_uc6 {M A : Subgroup G} (hAM : A ≤ M) {g : ↥M} :
    g ∈ normalizer ((A.subgroupOf M : Subgroup ↥M) : Set ↥M) ↔ (g : G) ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h x
    by_cases hx : x ∈ M
    · exact h ⟨x, hx⟩
    · have h1 : x ∉ A := fun hxA => hx (hAM hxA)
      have h2 : (g : G) * x * (g : G)⁻¹ ∉ A := fun hA => hx (by
        have := M.mul_mem (M.mul_mem (M.inv_mem g.2) (hAM hA)) g.2
        simpa [mul_assoc] using this)
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  · intro h x
    exact h (x : G)

theorem moduleData_uc6 (hS : Standing4 G) (S : Setup4 G) :
    CFSG.Open.IsKGroup ↥S.M ∧ IsPGroup 2 (CFSG.pCore 2 ↥S.M) ∧
      centralizer ((CFSG.pCore 2 ↥S.M : Subgroup ↥S.M) : Set ↥S.M) ≤ CFSG.pCore 2 ↥S.M := by
  haveI := hS.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMtop : S.M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab S.maxLocal.1
  refine ⟨hS.kProper.isKGroup S.M hMtop, CFSG.LieType.BorelTits.pCore_isPGroup 2, ?_⟩
  intro x hx
  have h1 := hS.charTwo S.M S.maxLocal.1
  have hxG : (x : G) ∈ S.M ⊓ centralizer (pCoreOf 2 S.M : Set G) := by
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ centralizer (pCoreOf 2 S.M : Set G)
    rw [mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have := mem_centralizer_iff.1 hx q hq
    exact congrArg Subtype.val this
  obtain ⟨q, hq, hqx⟩ := h1 hxG
  have : q = x := Subtype.ext hqx
  exact this ▸ hq

theorem card_fix_le_uc6 (S : Setup4 G) {X : Subgroup G} (hXM : X ≤ S.M)
    (hfix : Nat.card ↥(pCoreOf 2 S.M ⊓ centralizer (X : Set G) : Subgroup G) ≤ 2) :
    Nat.card ↥((CFSG.pCore 2 ↥S.M) ⊓
      centralizer ((X.subgroupOf S.M : Subgroup ↥S.M) : Set ↥S.M)) ≤ 2 := by
  have hle : ((CFSG.pCore 2 ↥S.M) ⊓
      centralizer ((X.subgroupOf S.M : Subgroup ↥S.M) : Set ↥S.M)).map S.M.subtype ≤
      pCoreOf 2 S.M ⊓ centralizer (X : Set G) := by
    rintro _ ⟨x, ⟨hxQ, hxC⟩, rfl⟩
    refine ⟨⟨x, hxQ, rfl⟩, ?_⟩
    show S.M.subtype x ∈ centralizer (X : Set G)
    rw [mem_centralizer_iff]
    intro h hh
    have := mem_centralizer_iff.1 hxC ⟨h, hXM hh⟩ hh
    exact congrArg Subtype.val this
  have := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective S.M.subtype_injective] at this
  exact this.trans hfix

end Transport

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

@[expose] def C627 : Prop := m.Z ≤ ⁅m.M, m.M⁆

theorem U_le_M : m.U ≤ m.M := m.U_le_K.trans m.K_le_M

theorem M_le_normalizer_U : m.M ≤ normalizer (m.U : Set G) := fun _ hg =>
  mem_normalizer_of_forward_uc6 (m.conj_U_le hg)

theorem six28b (hK : UCK.K47) (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h626 : m.C626)
    (h627 : m.C627) : m.C628b := by
  intro p hp hdvdU'
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hpr : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hpr⟩
  have hp2 : p ≠ 2 := ((dataOfSetup4 m.hS m.hU m.S).sig_prime p hp).2
  have hpne : p ≠ m.r := fun h => m.hrσ (h ▸ hp)
  have hdvdU : p ∣ Nat.card m.U := by rw [m.card_U]; exact hdvdU'
  have hZp : IsPGroup m.r m.Z := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact m.card_Z)
  have hZU : m.Z ≤ normalizer (m.U : Set G) := fun z hz => m.K_le_normalizer_U (m.Z_le_K hz)
  have hcopU : ¬ m.r ∣ Nat.card m.U := fun h => m.hr.ne_one (m.coprime_card_U.eq_one_of_dvd h)
  obtain ⟨P, hPsyl, hZP⟩ := exists_invariant_sylow_uc6 (r := m.r) p hZU hZp hcopU
  have hPU : P ≤ m.U := hPsyl.le
  have hPM : P ≤ m.M := hPU.trans m.U_le_M
  have hPp : IsPGroup p P := hPsyl.isPGroup
  have hPbot : P ≠ ⊥ := by
    intro h
    have hc := hPsyl.card_eq
    rw [h, Subgroup.card_bot] at hc
    have hk : (Nat.card m.U).factorization p ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd hpr (Nat.card_pos.ne') hdvdU).ne'
    rcases pow_eq_one_iff.1 hc.symm with h1 | h1
    · exact hpr.ne_one h1
    · exact hk h1
  have hCP : ∀ x ∈ P, (∀ z ∈ m.Z, z * x = x * z) → x = 1 := by
    intro x hxP hxc
    by_contra hx1
    have hxM : x ∈ m.M := hPM hxP
    have hxcen : x ∈ centralizer (m.Z : Set G) := mem_centralizer_iff.2 hxc
    have hxN : x ∈ m.M ⊓ normalizer (m.Z : Set G) :=
      ⟨hxM, Subgroup.centralizer_le_normalizer _ hxcen⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hPp ⟨x, hxP⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.1 (by rw [hk]; rfl))
    have h1 : p ∣ orderOf x := by rw [hk]; exact dvd_pow_self p hk0
    have h2 : orderOf x ∣ Nat.card ↥(m.M ⊓ normalizer (m.Z : Set G)) := by
      have := orderOf_dvd_natCard (⟨x, hxN⟩ : ↥(m.M ⊓ normalizer (m.Z : Set G)))
      rwa [Subgroup.orderOf_mk] at this
    exact h626 p hp (h1.trans h2)
  set Q : Subgroup G := omegaCenter p P with hQ
  have hQP : Q ≤ P := omegaCenter_le p P
  have hQM : Q ≤ m.M := hQP.trans hPM
  have hQab : CFSG.Open.IsElemAbelian p Q := isElemAbelian_omegaCenter p P
  have hQne : Q ≠ ⊥ := omegaCenter_ne_bot hPp hPbot
  have hQZ : m.Z ≤ normalizer (Q : Set G) := fun z hz =>
    normalizer_le_normalizer_omegaCenter p P (hZP hz)
  have hQfix : ∀ q ∈ Q, (∀ z ∈ m.Z, z * q = q * z) → q = 1 := fun q hq hc => hCP q (hQP hq) hc
  obtain ⟨z₁, hz₁⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 m.Z_ne_bot
  have hZgen : m.Z = Subgroup.zpowers (z₁ : G) := by
    have hle : Subgroup.zpowers (z₁ : G) ≤ m.Z := (Subgroup.zpowers_le).2 z₁.2
    have hdvd : orderOf (z₁ : G) ∣ m.r := by
      rw [← m.card_Z]
      have h := orderOf_dvd_natCard z₁
      rwa [← Subgroup.orderOf_coe] at h
    have hne : orderOf (z₁ : G) ≠ 1 := fun h => hz₁ (Subtype.ext (orderOf_eq_one_iff.1 h))
    have hord : orderOf (z₁ : G) = m.r := ((Nat.dvd_prime m.hr).1 hdvd).resolve_left hne
    exact (Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, hord, m.card_Z])).symm
  have hcomm : ⁅m.Z, Q⁆ = Q :=
    commutator_eq_of_fixedPointFree_uc6 hZgen hQab.1 hQZ hQfix
  obtain ⟨hMg, hQ₀, hchar⟩ := moduleData_uc6 m.hS m.S
  haveI hQ₀n : (CFSG.pCore 2 ↥m.M).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hQ' := isElemAbelian_subgroupOf_uc6 hQM hQab
  by_cases hQc : IsCyclic ↥Q
  ·
    haveI hU'n : (m.U.subgroupOf m.M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer m.U_le_M).2 m.M_le_normalizer_U
    have htop : (⊤ : Subgroup ↥m.M).map m.M.subtype = m.M := by
      rw [← MonoidHom.range_eq_map]
      exact Subgroup.range_subtype _
    have hFr : m.M = m.U ⊔ (m.M ⊓ normalizer (P : Set G)) :=
      frattini_of_isSylowOf m.U_le_M m.M_le_normalizer_U hPsyl
    have hNmap : (normalizer ((P.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M)).map
        m.M.subtype = m.M ⊓ normalizer (P : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, (mem_normalizer_subgroupOf_iff_uc6 hPM).1 hy⟩
      · rintro ⟨hxM, hxN⟩
        exact ⟨⟨x, hxM⟩, (mem_normalizer_subgroupOf_iff_uc6 hPM).2 hxN, rfl⟩
    have hFr' : (⊤ : Subgroup ↥m.M) = m.U.subgroupOf m.M ⊔
        normalizer ((P.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M) := by
      apply Subgroup.map_injective m.M.subtype_injective
      rw [htop, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le m.U_le_M, hNmap]
      exact hFr
    have hQN' : normalizer ((P.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M) ≤
        normalizer ((Q.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M) := by
      intro y hy
      exact (mem_normalizer_subgroupOf_iff_uc6 hQM).2
        (normalizer_le_normalizer_omegaCenter p P
          ((mem_normalizer_subgroupOf_iff_uc6 hPM).1 hy))
    have hQc' : IsCyclic ↥(Q.subgroupOf m.M) := by
      haveI := hQc
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQM).symm.toMonoidHom
        (MulEquiv.surjective _)
    have hZN' : m.Z.subgroupOf m.M ≤
        normalizer ((P.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M) := fun z hz =>
      (mem_normalizer_subgroupOf_iff_uc6 hPM).2 (hZP hz)
    have hZc' : m.Z.subgroupOf m.M ≤ ⁅(⊤ : Subgroup ↥m.M), ⊤⁆ := by
      intro z hz
      have hz' : (z : G) ∈ ⁅m.M, m.M⁆ := h627 hz
      have hmap : Subgroup.map m.M.subtype ⁅(⊤ : Subgroup ↥m.M), ⊤⁆ = ⁅m.M, m.M⁆ := by
        rw [Subgroup.map_commutator, htop]
      rw [← hmap] at hz'
      obtain ⟨w, hw, hwz⟩ := hz'
      have : w = z := Subtype.ext hwz
      exact this ▸ hw
    have hZr : ∀ z ∈ m.Z.subgroupOf m.M, z ^ m.r = 1 := by
      intro z hz
      have h1 : (⟨(z : G), hz⟩ : ↥m.Z) ^ Nat.card m.Z = 1 := pow_card_eq_one'
      rw [m.card_Z] at h1
      apply Subtype.ext
      simpa using congrArg Subtype.val h1
    have hcop' : Nat.Coprime m.r (Nat.card (m.U.subgroupOf m.M)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.U_le_M).toEquiv]
      exact m.coprime_card_U
    have hcen := cyclic_case_uc6 (m.U.subgroupOf m.M) (P.subgroupOf m.M) (Q.subgroupOf m.M)
      (m.Z.subgroupOf m.M) hFr' hQN' hQc' hZN' hZc' m.hr.one_lt hZr hcop'
    apply hQne
    rw [eq_bot_iff]
    intro q hq
    rw [Subgroup.mem_bot]
    refine hQfix q hq (fun z hz => ?_)
    have := hcen ⟨z, m.Z_le_M hz⟩ hz ⟨q, hQM hq⟩ hq
    exact congrArg Subtype.val this
  ·
    have hsub : (dataOfSetup4 m.hS m.hU m.S).sig ⊆ (dataOfSetup4 m.hS m.hU m.S).sig1 :=
      fun p hp => ⟨hp, m.hσ1 hp⟩
    have hEM : m.E ≤ m.M := fun x hx => m.R_le_M (m.E_le_R hx)
    have hfixG : Nat.card ↥(pCoreOf 2 m.M ⊓ centralizer (m.Z : Set G) : Subgroup G) ≤ 2 :=
      (h69 hsub m.r m.hr m.d.odd m.E hEM m.d.E_el m.d.E_card m.d.E_gamma m.r m.Z m.hr
        m.Z_le_M m.card_Z (m.hZ.E_le_centralizer.trans (Subgroup.centralizer_le_normalizer _))
        m.hZ.not_normalizer_le m.Z m.Z_le_M hZp le_rfl).1.1
    have hfix' := card_fix_le_uc6 m.S m.Z_le_M hfixG
    have hZ'card : Nat.card (m.Z.subgroupOf m.M) = m.r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.Z_le_M).toEquiv]
      exact m.card_Z
    have hQ'p : IsPGroup p (Q.subgroupOf m.M) := (hPp.to_le hQP).comap_subtype
    have hDQ' : m.Z.subgroupOf m.M ≤
        normalizer ((Q.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M) := fun z hz =>
      (mem_normalizer_subgroupOf_iff_uc6 hQM).2 (hQZ hz)
    have hcomm' : ⁅m.Z.subgroupOf m.M, Q.subgroupOf m.M⁆ = Q.subgroupOf m.M := by
      apply Subgroup.map_injective m.M.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le m.Z_le_M,
        Subgroup.map_subgroupOf_eq_of_le hQM]
      exact hcomm
    have hcyc := k47_transport_two_uc6 hK hMg (CFSG.pCore 2 ↥m.M) hQ₀ hchar hpr m.hr hp2
      m.d.odd hpne (m.Z.subgroupOf m.M) hZ'card hfix' (Q.subgroupOf m.M) hQ'p hQ'.1 hDQ' hcomm'
    exact hQc (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQM).toMonoidHom
      (MulEquiv.surjective _))

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
