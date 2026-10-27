module

public import CFSG.RankThree.PartOne.KE.E7FourHI
public import CFSG.RankThree.PartOne.KE.PlaneInner
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.PlaneToral

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)

open scoped Matrix Pointwise MatrixGroups

section Generic

theorem inner_of_isPGroup_of_not_dvd_card_outer {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hOut : ¬ p ∣ Nat.card (Outer C)) (A : Subgroup (MulAut C))
    (hA : IsPGroup p A) : A ≤ (MulAut.conj : C →* MulAut C).range := by
  intro a ha
  obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
  have hk' : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : (QuotientGroup.mk' (inner C) a) ^ p ^ k = 1 := by rw [← map_pow, hk', map_one]
  have h2 : orderOf (QuotientGroup.mk' (inner C) a) ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk' (inner C) a) ∣ Nat.card (Outer C) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) (Nat.card (Outer C)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hOut)
  have h4 : orderOf (QuotientGroup.mk' (inner C) a) = 1 := by
    have h5 := Nat.dvd_gcd h2 h3
    rw [hcop.gcd_eq_one] at h5
    exact Nat.dvd_one.1 h5
  exact (QuotientGroup.eq_one_iff (N := inner C) a).1 (orderOf_eq_one_iff.1 h4)

end Generic

section Outer

theorem card_outer_E7_dvd_two (K : Type) [Field K] [Finite K] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = ℓ) : Nat.card (Outer (adjointGroup .E7 K)) ∣ 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = ℓ := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := by
    exact (RingHom.charP_iff_charP (ZMod.ringEquivOfPrime K hℓ hcard).toRingHom ℓ).1
      (ZMod.charP ℓ)
  obtain ⟨Φ, -, hker, hdvd⟩ := exists_outer_hom_E (K := K) (τ := Tag.E7) (Or.inr (Or.inl rfl))
  have hsub : Subsingleton (RingAut K × Multiplicative (ZMod (exactE Tag.E7))) := by
    have e : ZMod ℓ ≃+* K := ZMod.ringEquivOfPrime K hℓ hcard
    have h1 : Subsingleton (RingAut K) := ⟨fun σ τ => by
      have := RingHom.ext_zmod (σ.toRingHom.comp e.toRingHom) (τ.toRingHom.comp e.toRingHom)
      refine RingEquiv.ext fun x => ?_
      obtain ⟨n, rfl⟩ := e.surjective x
      exact congrArg (fun g : ZMod ℓ →+* K => g n) this⟩
    have h2 : Subsingleton (Multiplicative (ZMod (exactE Tag.E7))) := by
      have : exactE Tag.E7 = 1 := rfl
      rw [this]
      infer_instance
    infer_instance
  have hker' : Φ.ker = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  rw [hker', Subgroup.card_top] at hdvd
  rwa [det_cartan_E7] at hdvd

end Outer

section Plane

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem e7F4_S0_subset_kernel {Fr : L →+* L} {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hΦ : (q : ZMod p) ^ 2 + 1 = 0)
    {b : Fin Tag.E7.rank → Lˣ} (hb : b ∈ fixedCharTuples e7F4W Fr) (hap : ∀ i, b i ^ p = 1) :
    e7F4S0Set ⊆ rootCharKernel b := by
  by_cases hb1 : b = 1
  · subst hb1
    intro α hα
    obtain ⟨l, hl, rfl⟩ := hα
    refine ⟨isRoot_toVec (e7F4_S0_roots l hl), ?_⟩
    exact CTTorus.rootChar_one _
  · rcases e7F4_kernel_structure Fr hFr hp hp3 hΦ hb hap hb1 with h | ⟨cert, hcert, h, -⟩
    · exact h.symm.subset
    · rw [h]
      exact Set.subset_union_left

theorem e7_four_central_of_plane (hD4 : D4TranspositionLayer Tag.E7)
    (F : E7FourFrame K L ℓ f p) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p) :
    ∀ A₀ : Subgroup (adjointGroup .E7 K), Nat.card A₀ = p ^ 2 →
      (∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) → (∀ a ∈ A₀, a ^ p = 1) →
      ∀ x ∈ A₀, x ≠ 1 → ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))),
        V.Normal → Group.IsSolvable V → ∀ v ∈ V, ∀ a ∈ A₀, a * (v : adjointGroup .E7 K) =
          (v : adjointGroup .E7 K) * a := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + 1) p).2 hpf
    simpa using this
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  intro A₀ hcard hcomm hexp x hx hx1 V hVn hVs v hv a ha
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hcard
  obtain ⟨c, hc⟩ := F.hconj A₀ hpg
  have hxp : orderOf x = p := orderOf_eq_prime (hexp x hx) hx1
  have hhx := hc x hx
  obtain ⟨b, hb, hap, hb1, hbh, -⟩ := e7_perx_prelim F hp hxp c hhx
  have hkind : rootCharKernel b = e7F4S0Set ∨ ∃ cert ∈ e7F4Certs,
      rootCharKernel b = e7F4S0Set ∪ classSetL7 e7F4Rows cert.cls := by
    rcases e7F4_kernel_structure (iterateFrobenius L ℓ f) hFr hp hp3 hΦ hb hap hb1 with
      h | ⟨cert, hcert, h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨cert, hcert, h⟩
  obtain ⟨ψ, hψinj, hψ, hψV⟩ := e7_four_perx_central hD4 F hf hK hp hstab hxp c hhx hbh hkind
  by_cases ha1 : a = 1
  · rw [ha1, one_mul, mul_one]
  have hap' : orderOf a = p := orderOf_eq_prime (hexp a ha) ha1
  obtain ⟨b', hb', hapb, hb1', hbh', -⟩ := e7_perx_prelim F hp hap' c (hc a ha)
  have haD : a ∈ Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm a ha x hx)
  set t : ModGL .E7 L := ψ ⟨a, haD⟩ with ht
  have htb : t = rootDiagUnit .E7 b' := by
    rw [ht, hψ, ← hbh']
  have htT : t ∈ torusGroup .E7 L := by
    rw [htb]
    exact rootDiagUnit_mem_torusGroup _
  have hS0 : e7F4S0Set ⊆ rootCharKernel b' := e7F4_S0_subset_kernel hFr hp hp3 hΦ hb' hapb
  have htC : t ∈ Subgroup.centralizer (rootSpan .E7 L e7F4S0Set : Set (ModGL .E7 L)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' : g ∈ Subgroup.centralizer ({rootDiagUnit .E7 b'} : Set (ModGL .E7 L)) :=
      rootSpan_le_centralizer (K := L) b' hS0 hg
    rw [htb]
    exact Subgroup.mem_centralizer_singleton_iff.1 hg'
  have h := hψV V hVn hVs v hv t htT htC
  have h2 : ψ (⟨a, haD⟩ * v) = ψ (v * ⟨a, haD⟩) := by
    rw [map_mul, map_mul, ← ht]
    exact h.symm
  have h3 := congrArg (fun z : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) =>
    (z : adjointGroup .E7 K)) (hψinj h2)
  simpa using h3

theorem planeLocalCoreOdd_E7_four_of_frame (hD4 : D4TranspositionLayer Tag.E7)
    (F : E7FourFrame K L ℓ f p) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p) :
    PlaneLocalCoreOdd p (adjointGroup .E7 K) := by
  classical
  have hC : Subgroup.center (adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
  by_cases hq4 : 4 ≤ Nat.card K
  · exact planeLocalCoreOdd_of_toral_kernels_abstract hp hp3 hC
      (e7_four_solvable hD4 F hf hK hp hp3 hq4 hpf hstab)
      (ordinary_E_outer_derived_subgroup_odd .E7 (Or.inr (Or.inl rfl)) K).1
      (localCoreTrivialOn_noninner_E .E7 (Or.inr (Or.inl rfl)) K hp hp3)
      (e7_four_hI hD4 F hf hK hp hp3 hpf hstab)
  ·
    have hℓ : ℓ.Prime := Fact.out
    have hf1 : f = 1 := by
      by_contra hne
      have hf2 : 2 ≤ f := by omega
      have : ℓ ^ 2 ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf2
      have h4 : 4 ≤ ℓ ^ 2 := by nlinarith [hℓ.two_le]
      omega
    have hKℓ : Nat.card K = ℓ := by rw [hK, hf1, pow_one]
    have hOut : ¬ p ∣ Nat.card (Outer (adjointGroup .E7 K)) := fun h => by
      have := Nat.le_of_dvd two_pos (h.trans (card_outer_E7_dvd_two K hℓ hKℓ))
      omega
    exact planeLocalCoreOdd_of_inner_centralized hp hC
      (fun A hA => inner_of_isPGroup_of_not_dvd_card_outer hp hOut A hA)
      (e7_four_central_of_plane hD4 F hf hK hp hp3 hpf hstab)
      (e7_four_hI hD4 F hf hK hp hp3 hpf hstab)

end Plane

end CFSG.RankThree.PartOne.KE
