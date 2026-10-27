module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
import CFSG.RankThree.Transfer.Yoshida
import Mathlib.GroupTheory.Transfer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

private lemma wreath_not_comm :
    ¬ ∀ a b : Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3), a * b = b * a := by
  intro h
  have h0 := h (RegularWreathProduct.inl (Multiplicative.ofAdd 1))
    ⟨fun x => if x = 1 then Multiplicative.ofAdd 1 else 1, 1⟩
  have h1 := congrArg (fun w => w.left 1) h0
  revert h1
  decide

private lemma hW_of_comm {Q : Type*} [Group Q] (hc : ∀ a b : Q, a * b = b * a)
    (K : Subgroup Q) [K.Normal] :
    IsEmpty (Q ⧸ K ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) := by
  refine ⟨fun e => wreath_not_comm fun a b => ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (e.symm a)
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (e.symm b)
  have ha : a = e (u : Q ⧸ K) := by rw [hu]; simp
  have hb : b = e (v : Q ⧸ K) := by rw [hv]; simp
  rw [ha, hb, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc u v]

private lemma isPGroup_zmod3 : IsPGroup 3 (Multiplicative (ZMod 3)) := by
  intro g
  exact ⟨1, (by decide : ∀ b : Multiplicative (ZMod 3), b ^ 3 ^ 1 = 1) g⟩

private lemma pow_ne_one_zmod3 {a : Multiplicative (ZMod 3)} (ha : a ≠ 1) {n : ℕ}
    (hn : ¬ 3 ∣ n) : a ^ n ≠ 1 := by
  intro h
  have h3 : a ^ 3 = 1 := (by decide : ∀ b : Multiplicative (ZMod 3), b ^ 3 = 1) a
  have hd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h3p : (3 : ℕ).Prime := Nat.prime_three
  rcases (Nat.dvd_prime h3p).mp hd with h1 | h1
  · exact ha (orderOf_eq_one_iff.mp h1)
  · exact hn (h1 ▸ orderOf_dvd_of_pow_eq_one h)

private lemma exists_hom_normalizer {K : Type} [Group K] [Finite K] (P : Sylow 3 K)
    (ψ : ↥(P : Subgroup K) →* Multiplicative (ZMod 3))
    (hψ : ∀ n ∈ Subgroup.normalizer ((P : Subgroup K) : Set K), ∀ x y : ↥(P : Subgroup K),
      n * (x : K) * n⁻¹ = (y : K) → ψ y = ψ x)
    (x : ↥(P : Subgroup K)) (hx : ψ x ≠ 1) :
    ∃ φ : Subgroup.normalizer ((P : Subgroup K) : Set K) →* Multiplicative (ZMod 3),
      φ ⟨x, Subgroup.le_normalizer x.2⟩ ≠ 1 := by
  classical
  set N := Subgroup.normalizer ((P : Subgroup K) : Set K) with hN
  have hPN : (P : Subgroup K) ≤ N := Subgroup.le_normalizer
  set H : Subgroup N := (P : Subgroup K).subgroupOf N with hH
  haveI : H.FiniteIndex := inferInstance
  let ψ' : H →* Multiplicative (ZMod 3) :=
    ψ.comp (Subgroup.subgroupOfEquivOfLe hPN).toMonoidHom
  refine ⟨MonoidHom.transfer ψ', ?_⟩
  set n0 : N := ⟨x, hPN x.2⟩ with hn0
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers n0) (N ⧸ H))) :=
    Fintype.ofFinite _
  have key := MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot ψ' n0
  have hgen : ∀ (m : ℕ) (g : N) (hy : g⁻¹ * n0 ^ m * g ∈ H),
      ψ' ⟨g⁻¹ * n0 ^ m * g, hy⟩ = ψ x ^ m := by
    intro m g hy
    have h2 := hψ (((g⁻¹ : N)) : K) (g⁻¹).2 (x ^ m)
      ⟨(((g⁻¹ * n0 ^ m * g : N)) : K), hy⟩ (by simp [hn0, mul_assoc])
    rw [map_pow] at h2
    exact h2
  have hterm : ∀ q : Quotient (MulAction.orbitRel (Subgroup.zpowers n0) (N ⧸ H)),
      ψ' ⟨q.out.out⁻¹ * n0 ^ Function.minimalPeriod (n0 • ·) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem H n0 q.out⟩ =
        ψ x ^ Function.minimalPeriod (n0 • ·) q.out := fun q => hgen _ _ _
  have hval : MonoidHom.transfer ψ' n0 = ψ x ^ H.index :=
    calc MonoidHom.transfer ψ' n0 = _ := key
      _ = ∏ q : Quotient (MulAction.orbitRel (Subgroup.zpowers n0) (N ⧸ H)),
          ψ x ^ Function.minimalPeriod (n0 • ·) q.out := Finset.prod_congr rfl fun q _ => hterm q
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
      _ = _ := congrArg _ (Subgroup.index_eq_sum_minimalPeriod H n0).symm
  intro hone
  have hnd := (P.subtype hPN).not_dvd_index
  rw [Sylow.coe_subtype] at hnd
  exact pow_ne_one_zmod3 hx hnd (hval.symm.trans hone)

private lemma not_mem_commutator_sup_oResidual {K : Type} [Group K] [Finite K] (P : Sylow 3 K)
    [IsMulCommutative (P : Subgroup K)] (ψ : ↥(P : Subgroup K) →* Multiplicative (ZMod 3))
    (hψ : ∀ n ∈ Subgroup.normalizer ((P : Subgroup K) : Set K), ∀ x y : ↥(P : Subgroup K),
      n * (x : K) * n⁻¹ = (y : K) → ψ y = ψ x)
    (x : ↥(P : Subgroup K)) (hx : ψ x ≠ 1) :
    (x : K) ∉ commutator K ⊔ CFSG.GH74.GLS.oResidual 3 K := by
  intro hmem
  have hW : ∀ (K' : Subgroup (P : Subgroup K)) [K'.Normal],
      IsEmpty ((↥(P : Subgroup K) ⧸ K') ≃*
        (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) :=
    fun K' _ => hW_of_comm (fun a b => IsMulCommutative.is_comm.comm a b) K'
  have hbij := CFSG.RankThree.Transfer.yoshida_bijective_abelianPQuotientMap P hW
  set N := Subgroup.normalizer ((P : Subgroup K) : Set K) with hN
  set n0 : N := ⟨x, Subgroup.le_normalizer x.2⟩ with hn0
  obtain ⟨φ, hφ⟩ := exists_hom_normalizer P ψ hψ x hx
  have hker : commutator N ⊔ CFSG.GH74.GLS.oResidual 3 N ≤ φ.ker :=
    sup_le (Abelianization.commutator_subset_ker _)
      (CFSG.RankThree.Transfer.oResidual_le_ker_of_isPGroup _ isPGroup_zmod3)
  have h1 : (CFSG.RankThree.Transfer.abelianPQuotientMap 3 N)
      ((n0 : N) : N ⧸ (commutator N ⊔ CFSG.GH74.GLS.oResidual 3 N)) = 1 := by
    rw [CFSG.RankThree.Transfer.abelianPQuotientMap_mk, QuotientGroup.eq_one_iff]
    exact hmem
  have h2 := hbij.1 (h1.trans (map_one _).symm)
  rw [QuotientGroup.eq_one_iff] at h2
  exact hφ (MonoidHom.mem_ker.mp (hker h2))

theorem not_mem_OUp_of_hom [Finite G] (M B : Subgroup G) (hB : IsSylowOf 3 B M)
    (hel : IsElementaryAbelian 3 B) (ψ : ↥B →* Multiplicative (ZMod 3))
    (hψ : ∀ n ∈ M ⊓ Nor B, ∀ x y : ↥B, n * (x : G) * n⁻¹ = (y : G) → ψ y = ψ x)
    (x : ↥B) (hx : ψ x ≠ 1) : (x : G) ∉ OUp 3 M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hBM, hBp, hcop⟩ := hB
  have hp : IsPGroup 3 (B.subgroupOf M) :=
    hBp.of_surjective (Subgroup.subgroupOfEquivOfLe hBM).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hBM).symm.surjective
  have hidx : ¬ 3 ∣ (B.subgroupOf M).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
  let P : Sylow 3 M := hp.toSylow hidx
  have hP : (P : Subgroup M) = B.subgroupOf M := rfl
  haveI : IsMulCommutative (P : Subgroup M) :=
    ⟨⟨fun a b => by
      have := IsMulCommutative.is_comm.comm (⟨(a.1 : G), a.2⟩ : B) ⟨(b.1 : G), b.2⟩
      have h := congrArg Subtype.val this
      exact Subtype.ext (Subtype.ext h)⟩⟩
  let ψ'' : ↥(P : Subgroup M) →* Multiplicative (ZMod 3) :=
    ψ.comp (Subgroup.subgroupOfEquivOfLe hBM).toMonoidHom
  have hψ'' : ∀ n ∈ Subgroup.normalizer ((P : Subgroup M) : Set M), ∀ a b : ↥(P : Subgroup M),
      n * (a : M) * n⁻¹ = (b : M) → ψ'' b = ψ'' a := by
    intro n hn a b hab
    have hnB : (n : G) ∈ Nor B := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have := (Subgroup.mem_normalizer_iff.mp hn) ⟨g, hBM hg⟩
        exact this.mp hg
      · intro hg
        have hgM : g ∈ M := by
          have h1 := M.mul_mem (M.mul_mem (M.inv_mem n.2) (hBM hg)) n.2
          simpa [mul_assoc] using h1
        exact ((Subgroup.mem_normalizer_iff.mp hn) ⟨g, hgM⟩).mpr hg
    exact hψ (n : G) ⟨n.2, hnB⟩ ⟨(a : M), a.2⟩ ⟨(b : M), b.2⟩
      (by simpa using congrArg Subtype.val hab)
  intro hmem
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
  have hyM : y = ⟨(x : G), hBM x.2⟩ := Subtype.ext hyx
  have hS : (Subgroup.normalClosure {g : M | Nat.Coprime 3 (orderOf g)}) ≤
      CFSG.GH74.GLS.oResidual 3 M := by
    apply Subgroup.normalClosure_le_normal
    intro g hg
    exact Subgroup.subset_closure (Nat.coprime_comm.mp hg)
  have hmem' : ((⟨(x : G), hBM x.2⟩ : M)) ∈ commutator M ⊔ CFSG.GH74.GLS.oResidual 3 M :=
    Subgroup.mem_sup_right (hS (hyM ▸ hy))
  exact not_mem_commutator_sup_oResidual P ψ'' hψ'' ⟨⟨(x : G), hBM x.2⟩, x.2⟩ hx hmem'

end CFSG.RankThree.PartTwo.Sec21.FF79
