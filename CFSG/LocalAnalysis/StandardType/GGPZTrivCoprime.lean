module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosure
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pzt1_maximal_of_normalizer_coprime
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {N P Q : Subgroup G} (hPN : P ≤ Subgroup.normalizer (N : Set G))
    (hcoin : Nat.Coprime p (Nat.card ↥N))
    (hQ : IsPGroup p ↥Q) (hQM : Q ≤ N ⊔ P) (hle : P ≤ Q) :
    Q = P := by
  refine le_antisymm ?_ hle
  intro q hq
  have hqmem : q ∈ (N : Set G) * (P : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N P hPN]
    exact hQM hq
  obtain ⟨n, hnN, r, hrP, hnr⟩ := hqmem
  have hnQ : n ∈ Q := by
    have hqr : q * r⁻¹ ∈ Q := Subgroup.mul_mem Q hq (Subgroup.inv_mem Q (hle hrP))
    have hn_eq : n = q * r⁻¹ := by rw [← hnr]; group
    rwa [hn_eq]
  have hn1 : n = 1 := by
    obtain ⟨k, hk⟩ := hQ ⟨n, hnQ⟩
    have hnpow : n ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd_N : orderOf n ∣ Nat.card ↥N := by
      rw [← Subgroup.orderOf_mk n hnN]
      exact orderOf_dvd_natCard (⟨n, hnN⟩ : ↥N)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hcoin.pow_left k)
      (orderOf_dvd_of_pow_eq_one hnpow) hdvd_N)
  rw [← hnr, hn1]
  simpa using hrP

theorem ggPZ_coprime_lift {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Y : Subgroup G}
    {x : G} (hx : x ^ p = 1) (hx1 : x ≠ 1) (hxY : x ∈ Subgroup.normalizer (Y : Set G))
    (hcomm : (⁅Y, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p Y) :
    ∀ u ∈ Y, ∃ c ∈ Y ⊓ Subgroup.centralizer ({x} : Set G), ∃ n ∈ LargeEvenPPrimeCoreOf p Y,
      u = c * n := by
  intro u hu
  set N : Subgroup G := LargeEvenPPrimeCoreOf p Y
  set P : Subgroup G := Subgroup.zpowers x with hP
  set M : Subgroup G := N ⊔ P with hM
  set x' : G := u⁻¹ * x * u with hx'
  have hxN : x ∈ Subgroup.normalizer (N : Set G) :=
    (ggNormalizer_le_normalizer_pPrimeCoreOf p Y) hxY
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := Subgroup.zpowers_le.mpr hxN
  have hNY : N ≤ Y := Subgroup.map_subtype_le _
  have hcopN : Nat.Coprime p (Nat.card ↥N) := ggPPrimeCoreOf_coprime Y
  have hcomm_mem : ⁅u⁻¹, x⁆ ∈ N :=
    hcomm (Subgroup.commutator_mem_commutator (Y.inv_mem hu) (Subgroup.mem_zpowers x))
  have hx'x : x' * x⁻¹ ∈ N := by
    have h' : ⁅u⁻¹, x⁆ = x' * x⁻¹ := by rw [commutatorElement_def, hx']; group
    rw [h'] at hcomm_mem
    exact hcomm_mem
  have hx'M : x' ∈ M := by
    rw [hM, show x' = (x' * x⁻¹) * x by group]
    exact Subgroup.mul_mem_sup hx'x (Subgroup.mem_zpowers x)
  have hPM : P ≤ M := by rw [hM]; exact le_sup_right
  have hP'M : Subgroup.zpowers x' ≤ M := Subgroup.zpowers_le.mpr hx'M
  have hx'eq : x' = (MulAut.conj u⁻¹) x := by rw [hx', MulAut.conj_apply]; group
  have hx'p : x' ^ p = 1 := by rw [hx'eq, ← map_pow, hx, map_one]
  have hx'ne : x' ≠ 1 := by
    intro h
    have h1 : (MulAut.conj u⁻¹) x = 1 := by rw [← hx'eq, h]
    have h1' : u⁻¹ * x * u = 1 := by simpa [MulAut.conj_apply] using h1
    apply hx1
    calc x = u * (u⁻¹ * x * u) * u⁻¹ := by group
      _ = u * 1 * u⁻¹ := by rw [h1']
      _ = 1 := by group
  have hcardP : Nat.card ↥P = p := by rw [hP, Nat.card_zpowers, orderOf_eq_prime hx hx1]
  have hcardP' : Nat.card ↥(Subgroup.zpowers x') = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx'p hx'ne]
  have hPp : IsPGroup p ↥P := IsPGroup.of_card (n := 1) (by simp [hcardP])
  have hP'p : IsPGroup p ↥(Subgroup.zpowers x') := IsPGroup.of_card (n := 1) (by simp [hcardP'])
  have hPsubp : IsPGroup p ↥(P.subgroupOf M) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  have hP'subp : IsPGroup p ↥((Subgroup.zpowers x').subgroupOf M) :=
    hP'p.of_equiv (Subgroup.subgroupOfEquivOfLe hP'M).symm
  obtain ⟨S, hPS⟩ := hPsubp.exists_le_sylow
  obtain ⟨S', hP'S'⟩ := hP'subp.exists_le_sylow
  have hSmap : (S : Subgroup ↥M).map M.subtype = P :=
    pzt1_maximal_of_normalizer_coprime hPN hcopN (S.isPGroup'.map M.subtype)
      (by rw [← hM]; exact Subgroup.map_subtype_le _)
      (by
        intro r hr
        exact ⟨⟨r, hPM hr⟩, hPS (Subgroup.mem_subgroupOf.mpr hr), rfl⟩)
  have hSle : (S : Subgroup ↥M) ≤ P.subgroupOf M := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have : (y : G) ∈ (S : Subgroup ↥M).map M.subtype := ⟨y, hy, rfl⟩
    rwa [hSmap] at this
  have hSeq : (S : Subgroup ↥M) = P.subgroupOf M := le_antisymm hSle hPS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) S S'
  have hx'S' : (⟨x', hx'M⟩ : ↥M) ∈ (S' : Subgroup ↥M) :=
    hP'S' (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x'))
  rw [← hg, Sylow.coe_subgroup_smul, hSeq] at hx'S'
  obtain ⟨y, hyS, hy⟩ :=
    (Subgroup.mem_smul_pointwise_iff_exists (⟨x', hx'M⟩ : ↥M)
      (MulAut.conj g) (P.subgroupOf M)).mp hx'S'
  have hyP : (y : G) ∈ P := Subgroup.mem_subgroupOf.mp hyS
  have hyconj : (g : G) * (y : G) * (g : G)⁻¹ = x' := by
    have := congrArg Subtype.val hy
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using this
  have hgmem : (g : G) ∈ (N : Set G) * (P : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N P hPN]
    exact g.2
  obtain ⟨n, hnN, r, hrP, hnr⟩ := hgmem
  have hrPz : r ∈ Subgroup.zpowers x := by rw [hP] at hrP; exact hrP
  have hyPz : (y : G) ∈ Subgroup.zpowers x := by rw [hP] at hyP; exact hyP
  have hcomm_ry : r * (y : G) * r⁻¹ = (y : G) := by
    have hc : r * (y : G) = (y : G) * r :=
      congrArg Subtype.val ((Subgroup.zpowers_isMulCommutative x).is_comm.comm
        (⟨r, hrPz⟩ : ↥(Subgroup.zpowers x)) (⟨(y : G), hyPz⟩ : ↥(Subgroup.zpowers x)))
    rw [hc]; group
  have hx'_ny : x' = n * (y : G) * n⁻¹ := by
    rw [← hyconj, ← hnr]
    calc (n * r) * (y : G) * (n * r)⁻¹ = n * (r * (y : G) * r⁻¹) * n⁻¹ := by group
      _ = n * (y : G) * n⁻¹ := by rw [hcomm_ry]
  have hyx_N : (y : G) * x⁻¹ ∈ N := by
    have hxn : x * n * x⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hxN n).mp hnN
    have heq : (y : G) * x⁻¹ = n⁻¹ * (x' * x⁻¹) * (x * n * x⁻¹) := by
      rw [hx'_ny]; group
    rw [heq]
    exact Subgroup.mul_mem N (Subgroup.mul_mem N (Subgroup.inv_mem N hnN) hx'x) hxn
  have hcopPN : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by rw [hcardP]; exact hcopN
  have hdisj : Disjoint N P := (Subgroup.disjoint_of_coprime_natCard hcopPN).symm
  have hyx_P : (y : G) * x⁻¹ ∈ P :=
    Subgroup.mul_mem P hyP (Subgroup.inv_mem P (Subgroup.mem_zpowers x))
  have hyx_one : (y : G) * x⁻¹ = 1 := (Subgroup.disjoint_def.mp hdisj) hyx_N hyx_P
  have hy_eq_x : (y : G) = x := by
    calc (y : G) = ((y : G) * x⁻¹) * x := by group
      _ = x := by rw [hyx_one, one_mul]
  have hn_eq_x : x' = n * x * n⁻¹ := by rw [hx'_ny, hy_eq_x]
  have hc_mem : u * n ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : (u * n)⁻¹ * x * (u * n) = x := by
      calc (u * n)⁻¹ * x * (u * n) = n⁻¹ * (u⁻¹ * x * u) * n := by group
        _ = n⁻¹ * x' * n := by rw [← hx']
        _ = n⁻¹ * (n * x * n⁻¹) * n := by rw [hn_eq_x]
        _ = x := by group
    have h2 : x * (u * n) = (u * n) * x := by
      calc x * (u * n) = (u * n) * ((u * n)⁻¹ * x * (u * n)) := by group
        _ = (u * n) * x := by rw [hc]
    exact h2.symm
  refine ⟨u * n, Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem Y hu (hNY hnN), hc_mem⟩,
    n⁻¹, Subgroup.inv_mem N hnN, ?_⟩
  group

end CFSG.StandardType

end
