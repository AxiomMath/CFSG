module

public import CFSG.RankThree.PartOne.KE6.E8T3Perx
public import CFSG.RankThree.PartOne.KE6.E8T3Frame
public import CFSG.RankThree.PartOne.KE.E8FiveData

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix)
open scoped Matrix MatrixGroups

theorem e8T3_main (hD4 : D4TrialityLayer Tag.E8)
    (hE6 : E6Layer Tag.E8) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (K : Type) [Field K] [Finite K]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) (L : Type) [Field L]
    [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] (n : ModGL .E8 L)
    (hnm : n ∈ monomialSubgroup .E8 L) (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = e8T3We ε) :
    (∀ x : adjointGroup .E8 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V)) ∧
    (∀ B : Subgroup (MulAut (adjointGroup .E8 K)),
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup .E8 K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range →
        ∃ a ∈ A, a ≠ 1 ∧ Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (adjointGroup .E8 K))))))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hT : twistedTorusOf n Φ =
      (fixedCharTuples (weylMatrix (e8T3We ε)) Fr).map (rootDiagUnitHom .E8 L) :=
    e8T3_twistedTorus n hnm hnW Fr
  have hcard : Nat.card (twistedTorusOf n Φ) = (e8T3D ε (Nat.card K)) ^ 4 :=
    natCard_e8T3Torus hε n hnm hnW hFr hℓq
  have hodd : Odd ((e8T3D ε (Nat.card K)) ^ 4) := (e8T3D_odd hε _).pow
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := e8T3_frame hε K hf hK hp hp3 hpf L n hnm hnW
  have hsolv : ∀ x : adjointGroup .E8 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V) := by
    intro x hx V hVn hVs
    have hpg : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨c, hc⟩ := hconj _ hpg
    have hh : g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ :=
      (mem_subtorusImage_iff _ _ _ _).1 (hc x (Subgroup.mem_zpowers x))
    obtain ⟨ψ, hψinj, -, hψV, -⟩ := e8T3_perx hD4 hE6 hε K hf hK hp hp3 hpf L n hnm hnW g0 hg0C
      hg0 hperf hT hx c hh
    have hφT : ∀ v : V, ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))) ∈
        twistedTorusOf n Φ := fun v => hψV V hVn hVs v v.2
    let φ' : V →* twistedTorusOf n Φ := (ψ.comp V.subtype).codRestrict _ hφT
    have hφ'inj : Function.Injective φ' := fun a a' haa =>
      Subtype.ext (hψinj (congrArg Subtype.val haa))
    exact Odd.of_dvd_nat (hcard ▸ hodd) (Subgroup.card_dvd_of_injective φ' hφ'inj)
  refine ⟨hsolv, ?_⟩
  intro B hB A hAB hA hcard' hAin
  have hC : Subgroup.center (adjointGroup .E8 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (adjointGroup .E8 K) :=
    A.comap (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard']
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  let φ : A₀ →* ModGL .E8 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .E8 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      g0⁻¹ * adjEmb .E8 K L (c * (q : adjointGroup .E8 K) * c⁻¹) * g0 := fun q => by
    simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n Φ := fun q => by
    rw [hφ]
    exact (mem_subtorusImage_iff _ _ _ _).1 (hc q q.2)
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E8.rank → Lˣ, φ q = rootDiagUnit .E8 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  set α₀ : Fin Tag.E8.rank → ℤ := Pi.single 0 1 with hα₀def
  have hα₀ : IsRoot .E8 α₀ := isRoot_single .E8 0
  let χ : A₀ →* Lˣ :=
    { toFun := fun q => rootChar (β q) α₀
      map_one' := by rw [hβone]; exact CTTorus.rootChar_one α₀
      map_mul' := fun q q' => by rw [hβmul, CTTorus.rootChar_mul] }
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hχp : ∀ q : A₀, χ q ^ p = 1 := fun q => by
    rw [← map_pow]
    have h1 : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))
        ((q : adjointGroup .E8 K) ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ q.2
    have h2 : (q : adjointGroup .E8 K) ^ p = 1 := hIntinj (h1.trans (map_one _).symm)
    have h3 : q ^ p = 1 := Subtype.ext h2
    rw [h3, map_one]
  obtain ⟨q, hq1, hqχ⟩ := exists_ne_one_ker_of_card_sq hp hA₀card χ hχp
  set x : adjointGroup .E8 K := (q : adjointGroup .E8 K) with hxdef
  have hx1 : x ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hxp : x ^ p = 1 := by
    have h1 : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) (x ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ q.2
    exact hIntinj (h1.trans (map_one _).symm)
  have hx : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxA : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) x ∈ A := q.2
  have hh : g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ := by
    rw [← hφ q]
    exact hφT q
  obtain ⟨ψ, hψinj, hψ, -, hψK⟩ := e8T3_perx hD4 hE6 hε K hf hK hp hp3 hpf L n hnm hnW g0 hg0C
    hg0 hperf hT hx c hh
  have hb : rootDiagUnit .E8 (β q) = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 := by
    rw [← hβ, hφ]
  have hne : α₀ ∈ rootCharKernel (β q) := ⟨hα₀, hqχ⟩
  have hle := hψK (β q) hb ⟨α₀, hne⟩ hB
  refine ⟨MulAut.conj x, hxA, fun h1 => hx1 (hIntinj (by rw [h1, map_one])), ?_⟩
  have hsx := odd_card_inf_range_of_solvable (B := B) hp hC hB (hsolv x hx)
  rwa [inf_eq_left.2 hle] at hsx

end CFSG.RankThree.PartOne.KE6
