module

public import CFSG.RankThree.PartOne.KF.G2Torus
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog

variable {p : ℕ} {K : Type} [Field K]

theorem exists_isPrimitiveRoot_of_dvd_card_sub_one [Finite K] (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hpq
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨z, ?_⟩
  have := IsPrimitiveRoot.orderOf z
  rwa [hz] at this

variable (p K) in
@[expose] noncomputable def tpHom : (Fin Tag.G2.rank → rootsOfUnity p K) →* ModGL .G2 K :=
  (rootDiagUnitHom .G2 K).comp (MonoidHom.compLeft (rootsOfUnity p K).subtype _)

theorem tpHom_apply (b : Fin Tag.G2.rank → rootsOfUnity p K) :
    tpHom p K b = rootDiagUnit .G2 (fun i => ((b i : rootsOfUnity p K) : Kˣ)) := rfl

theorem tpHom_injective
    : Function.Injective (tpHom p K) := by
  intro b b' h
  funext i
  have := congrFun (rootDiagUnit_injective h) i
  exact Subtype.ext this

theorem tpHom_mem_adjointGroup
    (b : Fin Tag.G2.rank → rootsOfUnity p K) :
    tpHom p K b ∈ adjointGroup .G2 K :=
  rootDiagUnit_mem_adjointGroup_g2 _

theorem tpHom_mem_torusGroup
    (b : Fin Tag.G2.rank → rootsOfUnity p K) :
    tpHom p K b ∈ torusGroup .G2 K :=
  rootDiagUnit_mem_torusGroup_g2 _

variable (p K) in
@[expose] noncomputable def tpM
    : (Fin Tag.G2.rank → rootsOfUnity p K) →* ↥(adjointGroup .G2 K) :=
  (tpHom p K).codRestrict _ tpHom_mem_adjointGroup

theorem coe_tpM
    (b : Fin Tag.G2.rank → rootsOfUnity p K) : ((tpM p K b : ↥(adjointGroup .G2 K)) :
    ModGL .G2 K) = tpHom p K b := rfl

theorem tpM_injective
    : Function.Injective (tpM p K) := fun _ _ h =>
  tpHom_injective (congrArg Subtype.val h)

variable (p K) in
@[expose] noncomputable def Tp
    : Subgroup ↥(adjointGroup .G2 K) := (tpM p K).range

theorem tpM_mem_Tp
    (b : Fin Tag.G2.rank → rootsOfUnity p K) : tpM p K b ∈ Tp p K := ⟨b, rfl⟩

theorem Tp_comm
    (s t : ↥(adjointGroup .G2 K)) (hs : s ∈ Tp p K) (ht : t ∈ Tp p K) :
    s * t = t * s := by
  obtain ⟨b, rfl⟩ := hs
  obtain ⟨b', rfl⟩ := ht
  rw [← map_mul, ← map_mul, mul_comm]

theorem Tp_exp
    (t : ↥(adjointGroup .G2 K)) (ht : t ∈ Tp p K) : t ^ p = 1 := by
  obtain ⟨b, rfl⟩ := ht
  rw [← map_pow]
  have : b ^ p = 1 := funext fun i => Subtype.ext (by
    simpa using (mem_rootsOfUnity p _).mp (b i).2)
  rw [this, map_one]

theorem mem_Tp_of_mem_torusGroup
    {t : ↥(adjointGroup .G2 K)}
    (ht : (t : ModGL .G2 K) ∈ torusGroup .G2 K) (htp : t ^ p = 1) : t ∈ Tp p K := by
  obtain ⟨a, ha⟩ := exists_eq_rootDiagUnit_of_mem_torusGroup ht
  have hap : a ^ p = 1 := by
    apply rootDiagUnit_injective (τ := .G2) (K := K)
    have h1 : rootDiagUnit .G2 (a ^ p) = rootDiagUnit .G2 a ^ p :=
      map_pow (rootDiagUnitHom .G2 K) a p
    rw [h1, ← ha, rootDiagUnit_one]
    exact congrArg Subtype.val htp
  have hmem : ∀ i, a i ∈ rootsOfUnity p K := fun i => (mem_rootsOfUnity p _).mpr (by
    simpa using congrFun hap i)
  refine ⟨fun i => ⟨a i, hmem i⟩, Subtype.ext ?_⟩
  exact ha.symm

theorem exists_conj_into_Tp
    [Finite K] (hp : p.Prime) (h5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1)
    (X : Subgroup ↥(adjointGroup .G2 K)) (hX : ∀ x ∈ X, x ^ p = 1) :
    ∃ g : ↥(adjointGroup .G2 K), ∀ x ∈ X, g * x * g⁻¹ ∈ Tp p K := by
  have : Fact p.Prime := ⟨hp⟩
  have hidx := CFSG.RankThree.Chevalley.not_dvd_index_torusGroup_G2 (K := K) hp (by omega) hpq
  have hP : IsPGroup p X := fun x => ⟨1, Subtype.ext (by simpa using hX x.1 x.2)⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.Chevalley.exists_conj_map_le_of_not_dvd_index hidx hP
  refine ⟨g, fun x hx => ?_⟩
  have h1 : g * x * g⁻¹ ∈ (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) :=
    hg ⟨x, hx, rfl⟩
  refine mem_Tp_of_mem_torusGroup (Subgroup.mem_subgroupOf.mp h1) ?_
  have : (g * x * g⁻¹) ^ p = g * x ^ p * g⁻¹ := conj_pow
  rw [this, hX x hx, mul_one, mul_inv_cancel]

end CFSG.RankThree.PartOne.KFU
