module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BGam
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
import CFSG.CGT.Timmesfeld75.Sec3OddSubgroup
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r8100b_eq_one_of_mem_pCore {M : Subgroup G} {x : ↥M} (hx : x ∈ CFSG.pCore 2 ↥M)
    {k : ℕ} (hk : Odd k) (hxk : x ^ k = 1) : x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨x, hx⟩
  have h1 : x ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hc : Nat.Coprime (2 ^ j) k := (Nat.coprime_two_left.2 hk).pow_left j
  have h2 : orderOf x ∣ Nat.gcd (2 ^ j) k :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hxk)
  rw [hc.gcd_eq_one] at h2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h2)

theorem uc22r8100b_barImage_le_normalizer {M P Q : Subgroup G} (h : P ≤ normalizer (Q : Set G)) :
    barImage M P ≤ normalizer (barImage M Q : Set (Bar2 M)) := by
  have key : ∀ x : ↥M, (x : G) ∈ P → ∀ z ∈ barImage M Q,
      uc22p21cPi M x * z * (uc22p21cPi M x)⁻¹ ∈ barImage M Q := by
    intro x hx z hz
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hz
    refine uc22p21c_mem_barImage.2 ⟨x * m * x⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.1 (h hx) m).1 hm
  intro y hy
  obtain ⟨x, hx, rfl⟩ := uc22p21c_mem_barImage.1 hy
  refine Subgroup.mem_normalizer_iff.2 fun z => ⟨key x hx z, fun hz => ?_⟩
  have h1 := key x⁻¹ (P.inv_mem hx) _ hz
  simpa [map_inv, mul_assoc] using h1

theorem uc22r8100b_comm_mem_pCoreOf {M : Subgroup G} {x k : ↥M}
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥M) x * QuotientGroup.mk' (CFSG.pCore 2 ↥M) k =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) k * QuotientGroup.mk' (CFSG.pCore 2 ↥M) x) :
    (x : G) * (k : G) * (x : G)⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 M := by
  refine (CFSG.mem_openPCoreOf_iff (x * k * x⁻¹ * k⁻¹)).2 ((QuotientGroup.eq_one_iff _).1 ?_)
  change uc22p21cPi M (x * k * x⁻¹ * k⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
  group

theorem uc22r8100b_exists_comm_lift {M K₁ K₂ A₀ : Subgroup G} {n m p q : ℕ} (h₁ : K₁ ∈ calC M)
    (h₂ : K₂ ∈ calC M) (hne : K₁ ≠ K₂) (hL₁ : IsL2 (Bar2 K₁) n) (hL₂ : IsL2 (Bar2 K₂) n)
    (hn : n = p * m) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n + 1) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqm : q ∣ 2 ^ m - 1) (hA₀M : A₀ ≤ M) (hA₀ : IsElemAbelian p A₀)
    (hA₀c : Nat.card A₀ = p ^ 4) (hA₀N₁ : A₀ ≤ normalizer (K₁ : Set G))
    (hA₀N₂ : A₀ ≤ normalizer (K₂ : Set G)) {a₁ a₂ : G} (ha₁ : a₁ ∈ K₁) (ha₂ : a₂ ∈ K₂)
    (ha₁o : orderOf a₁ = q) (ha₂o : orderOf a₂ = q) :
    ∃ A : Subgroup G, A ≤ M ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
      ∀ e ∈ zpowers a₁ ⊔ zpowers a₂, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hPn : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hqo : Odd q := hq.odd_of_ne_two hq2
  have hK₁M : K₁ ≤ M := uc22p22a_le_of_isSubnormal h₁.1
  have hK₂M : K₂ ≤ M := uc22p22a_le_of_isSubnormal h₂.1
  have hdisj : Disjoint (A₀.subgroupOf M) (uc22p21cPi M).ker := by
    refine Subgroup.disjoint_def.2 fun {x} hxA hxk => ?_
    have hxp : x ^ p = 1 := Subtype.ext (hA₀.2 (x : G) hxA)
    exact uc22r8100b_eq_one_of_mem_pCore ((QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hxk))
      hpo hxp
  have hA₀el : IsElemAbelian p (barImage M A₀) := (hA₀.subgroupOf M).map (uc22p21cPi M)
  have hA₀card : Nat.card (barImage M A₀) = p ^ 4 := by
    have h1 := UC6S846.card_map_of_disjoint_ker (uc22p21cPi M) (A₀.subgroupOf M) hdisj
    rw [← hA₀c, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀M).toEquiv]
    exact h1
  have hord : ∀ x : ↥M, orderOf x = q → orderOf (uc22p21cPi M x) = q := by
    intro x hx
    have hdvd : orderOf (uc22p21cPi M x) ∣ q := by
      rw [← hx]
      exact orderOf_map_dvd (uc22p21cPi M) x
    rcases (Nat.dvd_prime hq).1 hdvd with h1 | h1
    · exfalso
      have hπx : uc22p21cPi M x = 1 := orderOf_eq_one_iff.1 h1
      have hxq : x ^ q = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      have h2 := uc22r8100b_eq_one_of_mem_pCore ((QuotientGroup.eq_one_iff _).1 hπx) hqo hxq
      rw [h2, orderOf_one] at hx
      exact hq.one_lt.ne hx
    · exact h1
  have hx₁o : orderOf (⟨a₁, hK₁M ha₁⟩ : ↥M) = q :=
    (Subgroup.orderOf_coe (⟨a₁, hK₁M ha₁⟩ : ↥M)).symm.trans ha₁o
  have hx₂o : orderOf (⟨a₂, hK₂M ha₂⟩ : ↥M) = q :=
    (Subgroup.orderOf_coe (⟨a₂, hK₂M ha₂⟩ : ↥M)).symm.trans ha₂o
  obtain ⟨e₁, -⟩ := uc22p22l_barImage_equiv h₁
  obtain ⟨e₂, -⟩ := uc22p22l_barImage_equiv h₂
  obtain ⟨D, hDel, hDc, hDcomm⟩ := uc22r8100b_exists_centralizing_D
    (CFSG.Blueprint.LieModel.of_mulEquiv e₁ hL₁) (CFSG.Blueprint.LieModel.of_mulEquiv e₂ hL₂) hn hp
    hp2 hpn hq hqm (uc22p22l_barImage_commute h₁ h₂ hne) hA₀el hA₀card
    (uc22r8100b_barImage_le_normalizer hA₀N₁) (uc22r8100b_barImage_le_normalizer hA₀N₂)
    (uc22p21c_mem_barImage.2 ⟨⟨a₁, hK₁M ha₁⟩, ha₁, rfl⟩)
    (uc22p21c_mem_barImage.2 ⟨⟨a₂, hK₂M ha₂⟩, ha₂, rfl⟩) (hord _ hx₁o) (hord _ hx₂o)
  obtain ⟨K, hKc, hKD, hKinj⟩ := CFSG.CGT.Timmesfeld75.osg_exists_lift (CFSG.pCore 2 ↥M)
    CFSG.pCore_isPGroup D (by rw [hDc]; exact hpo.pow)
  have hKel : IsElemAbelian p K := by
    refine UC6S846.isElemAbelian_of_disjoint_ker (uc22p21cPi M) K ?_ (hDel.mono ?_)
    · exact Subgroup.disjoint_def.2 fun {x} hxK hxk => hKinj x hxK (MonoidHom.mem_ker.1 hxk)
    · rintro _ ⟨x, hx, rfl⟩
      exact hKD x hx
  refine ⟨K.map M.subtype, Subgroup.map_subtype_le K, hKel.map M.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective M.subtype_injective, hKc, hDc]
  ·
    rintro e he _ ⟨k, hk, rfl⟩
    have hc := hDcomm _ (hKD k hk)
    let P : Subgroup ↥M :=
      (Subgroup.centralizer {uc22p21cPi M k}).comap (uc22p21cPi M)
    have hx₁ : (⟨a₁, hK₁M ha₁⟩ : ↥M) ∈ P := Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hc.1
    have hx₂ : (⟨a₂, hK₂M ha₂⟩ : ↥M) ∈ P := Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hc.2
    have hE : zpowers a₁ ⊔ zpowers a₂ ≤ P.map M.subtype :=
      sup_le (zpowers_le.2 (Subgroup.mem_map.2 ⟨_, hx₁, rfl⟩))
        (zpowers_le.2 (Subgroup.mem_map.2 ⟨_, hx₂, rfl⟩))
    obtain ⟨y, hyP, rfl⟩ := hE he
    exact uc22r8100b_comm_mem_pCoreOf (x := y) (k := k)
      (Subgroup.mem_centralizer_iff.1 hyP _ (Set.mem_singleton _)).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22
