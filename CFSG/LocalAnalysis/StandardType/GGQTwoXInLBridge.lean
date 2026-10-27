module

public import CFSG.LocalAnalysis.StandardType.GGPumpupBalance
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

private theorem isComponentOf_map_conj_of_mem_normalizer {G : Type*} [Group G] {K A : Subgroup G}
    (hA : IsComponentOf A K) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    IsComponentOf (A.map (MulAut.conj g).toMonoidHom) K := by
  have hK : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  refine ⟨?_, ?_, ?_⟩
  · rw [← hK]
    exact Subgroup.map_mono hA.1
  · have h := hA.2.1.map (MulAut.conj g).toMonoidHom
    rwa [hK] at h
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (A.equivMapOfInjective _ (MulAut.conj g).injective).symm hA.2.2

theorem ggNbr_of_isComponentOf_ggG0_inf (hLB : GGLBalanceInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGCorFiveTwentyHyp p B Bs x L D J) (hpJ : p ∣ Nat.card J) {z : G} (hzD : z ∈ D)
    (hzx : z ∉ Subgroup.zpowers x) {X : Subgroup G}
    (hX : IsComponentOf X (ggG0 p B x L D J ⊓ Subgroup.centralizer ({z} : Set G)))
    (hJX : J ≤ X) (hxX : x ∉ Subgroup.centralizer (X : Set G)) :
    GGNbr p B x D J z X := by
  have hI : GGThmIHyp p B x L := hS.1.1
  have hBs : GGBstar p B Bs := hS.1.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hS.1.2.2
  let G0 : Subgroup G := ggG0 p B x L D J
  let H0 : Subgroup G := G0 ⊓ Subgroup.centralizer ({z} : Set G)
  have hXH0 : IsComponentOf X H0 := hX
  have hD : D = Subgroup.closure {x, z} := eq_closure_pair_of_mem hI hDJ hzD hzx
  let K : Subgroup G := ggLayerClosure p (Subgroup.centralizer ({z} : Set G)) J
  obtain ⟨hKc, hJK, hxK, hdis⟩ :=
    pumpup_of_stdSub (ggPumpupInput_of_lBalance hLB) hI hDJ hpJ hD
  have hKsub : IsSubnormal (K ⊓ G0) H0 := by
    have h := hKc.2.1.inf G0
    rw [inf_comm (Subgroup.centralizer ({z} : Set G)) G0] at h
    exact h
  have hxB : x ∈ B := hI.2.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hBs.1 hxB
  have hBsG0 : Bs ≤ Subgroup.normalizer (G0 : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hS.2.2.2.2
  have hxG0 : x ∈ Subgroup.normalizer (G0 : Set G) := hBsG0 hxBs
  have hxD : x ∈ D := by
    rw [hD]
    exact Subgroup.subset_closure (Set.mem_insert x {z})
  have hxz : x * z = z * x := by
    exact congrArg Subtype.val (hDJ.1.2.1.1.is_comm.comm ⟨x, hxD⟩ ⟨z, hzD⟩)
  have hxcz : x ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxz
  have hxCzN : x ∈ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G) :=
    Subgroup.le_normalizer hxcz
  have hxH0 : x ∈ Subgroup.normalizer (H0 : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hxG0, hxCzN⟩
  set X' : Subgroup G := X.map (MulAut.conj x).toMonoidHom with hX'def
  have hX'comp : IsComponentOf X' H0 :=
    isComponentOf_map_conj_of_mem_normalizer hX hxH0
  have hxJ : x ∈ Subgroup.centralizer (J : Set G) := by
    have h := hDJ.1.2.2.2.2.2.2 ▸ hxD
    exact h.2
  have hJmap : J.map (MulAut.conj x).toMonoidHom = J :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer (J : Set G) hxJ)
  have hJX' : J ≤ X' := by
    rw [hX'def, ← hJmap]
    exact Subgroup.map_mono hJX
  have hXK : X ≤ K := by
    rcases isComponentOf_le_or_commutator_eq_bot hXH0 hKsub with h | h
    · exact h.trans inf_le_left
    · exfalso
      have hJleG0 : J ≤ G0 :=
        (hDJ.1.2.2.2.2.2.1.1.trans inf_le_left).trans (le_ggG0_left p B x L D J)
      have hJinf : J ≤ K ⊓ G0 := le_inf hJK hJleG0
      have hbot : ⁅J, J⁆ = ⊥ :=
        le_bot_iff.mp ((Subgroup.commutator_mono hJX hJinf).trans_eq h)
      exact commutator_ne_bot_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2 hbot
  have hXX' : X ≤ X' := by
    rcases isComponentOf_le_or_commutator_eq_bot hXH0 hX'comp.2.1 with h | h
    · exact h
    · exfalso
      have hbot : ⁅J, J⁆ = ⊥ :=
        le_bot_iff.mp ((Subgroup.commutator_mono hJX hJX').trans_eq h)
      exact commutator_ne_bot_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2 hbot
  have hX'eq : X' = X := by
    have hcard : Nat.card X' = Nat.card X := by
      rw [hX'def]
      exact Subgroup.card_map_of_injective (MulAut.conj x).injective
    exact (Subgroup.eq_of_le_of_card_ge hXX' (le_of_eq hcard)).symm
  have hxXn : x ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hX'def.symm.trans hX'eq)
  rcases hdis with hN | hO
  ·
    have hKcomp : IsComponentOf K (Subgroup.centralizer ({z} : Set G)) :=
      (isComponentOf_of_isNeighborOf hI.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hDJ hN)).1
    have hKG0 : K ≤ G0 := le_ggG0_of_ggNbr hN
    have hKcompH0 : IsComponentOf K H0 :=
      IsComponentOf.of_le_of_le hKcomp (le_inf hKG0 hKc.1) inf_le_right
    rcases isComponentOf_le_or_commutator_eq_bot hKcompH0 hXH0.2.1 with hKX | hcomm
    · rw [← le_antisymm hKX hXK]
      exact hN
    · exfalso
      have hbot : ⁅X, X⁆ = ⊥ :=
        le_bot_iff.mp ((Subgroup.commutator_mono hXK le_rfl).trans_eq hcomm)
      exact commutator_ne_bot_of_isQuasisimple hX.2.2 hbot
  ·
    exfalso
    have hp : p.Prime := hI.2.2.2.2.2.1.1
    have hpX : p ∣ Nat.card X := hpJ.trans (Subgroup.card_dvd_of_le hJX)
    have hOcop : Nat.Coprime p (Nat.card (LargeEvenPPrimeCoreOf p K)) := by
      let _ : Fact p.Prime := ⟨hp⟩
      rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective K.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hXO : X ≤ Subgroup.normalizer (LargeEvenPPrimeCoreOf p K : Set G) := by
      intro y hy
      exact mem_normalizer_largeEvenPPrimeCoreOf (p := p) (A := K)
        (Subgroup.le_normalizer (hXK hy))
    have hcomm : (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K :=
      (Subgroup.commutator_mono hXK le_rfl).trans hO
    exact hxX (mem_centralizer_of_commutator_le_coprime hp hX.2.2 hpX hOcop hXO hxXn hcomm)

private theorem centralizer_eq_comap_of_ker_le_center {H Q : Type*} [Group H] [Finite H]
    [Group Q] (π : H →* Q) (hker : π.ker ≤ Subgroup.center H) {n : ℕ}
    (hcop : Nat.Coprime n (Nat.card π.ker)) {z : H} (hz : z ^ n = 1) :
    Subgroup.centralizer ({z} : Set H) =
      (Subgroup.centralizer ({π z} : Set Q)).comap π := by
  apply le_antisymm
  · intro h hh
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : q = π z := Set.mem_singleton_iff.mp hq
    subst hq'
    have hzh : z * h = h * z := (Subgroup.mem_centralizer_iff.mp hh) z rfl
    calc π z * π h = π (z * h) := (map_mul π z h).symm
      _ = π (h * z) := by rw [hzh]
      _ = π h * π z := map_mul π h z
  · intro h hh
    rw [Subgroup.mem_comap] at hh
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haz : a = z := Set.mem_singleton_iff.mp ha
    have hcomm : π z * π h = π h * π z :=
      (Subgroup.mem_centralizer_iff.mp hh) (π z) rfl
    have hc_ker : ⁅h, z⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.symm
    have hc_center : ⁅h, z⁆ ∈ Subgroup.center H := hker hc_ker
    have hcz : Commute ⁅h, z⁆ z := by
      rw [commute_iff_eq]
      exact (Subgroup.mem_center_iff.mp hc_center z).symm
    have hceq : h * z * h⁻¹ = ⁅h, z⁆ * z := by
      rw [commutatorElement_def]
      group
    have hceq' : ⁅h, z⁆ = h * z * h⁻¹ * z⁻¹ := by
      rw [commutatorElement_def]
    have ha_z : Commute (h * z * h⁻¹) z := by
      rw [commute_iff_eq, hceq]
      calc (⁅h, z⁆ * z) * z = (z * ⁅h, z⁆) * z := by rw [hcz.eq]
        _ = z * (⁅h, z⁆ * z) := by rw [mul_assoc]
    have hpow_a : ∀ k : ℕ, (h * z * h⁻¹) ^ k = h * z ^ k * h⁻¹ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ, ih, pow_succ]
          group
    have hpow : ∀ k : ℕ, ⁅h, z⁆ ^ k = h * z ^ k * h⁻¹ * (z ^ k)⁻¹ := by
      intro k
      have hcz' : Commute (h * z * h⁻¹) z⁻¹ := ha_z.inv_right
      calc ⁅h, z⁆ ^ k = ((h * z * h⁻¹) * z⁻¹) ^ k := by rw [hceq']
        _ = (h * z * h⁻¹) ^ k * (z⁻¹) ^ k := by rw [hcz'.mul_pow]
        _ = h * z ^ k * h⁻¹ * (z ^ k)⁻¹ := by rw [hpow_a, inv_pow]
    have hcn : ⁅h, z⁆ ^ n = 1 := by
      rw [hpow n, hz]
      simp
    have horder_n : orderOf ⁅h, z⁆ ∣ n := orderOf_dvd_of_pow_eq_one hcn
    have horder_ker : orderOf ⁅h, z⁆ ∣ Nat.card π.ker := by
      simpa [Subgroup.orderOf_mk] using
        orderOf_dvd_natCard (⟨⁅h, z⁆, hc_ker⟩ : π.ker)
    have hgcd : Nat.gcd n (Nat.card π.ker) = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
    have horder_one : orderOf ⁅h, z⁆ = 1 :=
      Nat.dvd_one.mp (hgcd ▸ Nat.dvd_gcd horder_n horder_ker)
    have hc_one : ⁅h, z⁆ = 1 := orderOf_eq_one_iff.mp horder_one
    have hzh : z * h = h * z := by
      have hc_eq_one : h * z * h⁻¹ * z⁻¹ = 1 := by
        rw [← commutatorElement_def]
        exact hc_one
      calc z * h = (h * z * h⁻¹ * z⁻¹) * (z * h) := by rw [hc_eq_one, one_mul]
        _ = h * z := by group
    rw [haz]
    exact hzh

theorem exists_isComponentOf_centralizer_lift {H Q : Type*} [Group H] [Finite H] [Group Q]
    (π : H →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H) {n : ℕ}
    (hcop : Nat.Coprime n (Nat.card π.ker)) {z : H} (hz : z ^ n = 1) {X₀ : Subgroup Q}
    (hX₀ : IsComponentOf X₀ (Subgroup.centralizer ({π z} : Set Q))) :
    ∃ X : Subgroup H, IsComponentOf X (Subgroup.centralizer ({z} : Set H)) ∧ X.map π = X₀ ∧
      ∀ J : Subgroup H, ⁅J, J⁆ = J → J.map π ≤ X₀ → J ≤ X := by
  have hC : Subgroup.centralizer ({z} : Set H) =
      (Subgroup.centralizer ({π z} : Set Q)).comap π :=
    centralizer_eq_comap_of_ker_le_center π hker hcop hz
  let P : Subgroup H := X₀.comap π
  let X : Subgroup H := ⁅P, P⁆
  have hPsub : IsSubnormal P (Subgroup.centralizer ({z} : Set H)) := by
    have h := hX₀.2.1.comap π
    rwa [← hC] at h
  have hPle : P ≤ Subgroup.centralizer ({z} : Set H) := hPsub.le
  have hXleP : X ≤ P := Subgroup.commutator_le_self P
  have hXnormal : (X.subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hXleP]
    intro a p ha hp
    have haP : a ∈ P := hXleP ha
    have hcomm : ⁅p, a⁆ ∈ X := Subgroup.commutator_mem_commutator hp haP
    have hEq : p * a * p⁻¹ = ⁅p, a⁆ * a := by
      rw [commutatorElement_def]
      group
    rw [hEq]
    exact X.mul_mem hcomm ha
  have hXsub : IsSubnormal X (Subgroup.centralizer ({z} : Set H)) :=
    (IsSubnormal.step hXleP hXnormal (IsSubnormal.refl P)).trans hPsub
  have hPmap : P.map π = X₀ := Subgroup.map_comap_eq_self_of_surjective hπ X₀
  have hXmap : X.map π = X₀ := by
    calc X.map π = (⁅P, P⁆).map π := rfl
      _ = ⁅P.map π, P.map π⁆ := Subgroup.map_commutator P P π
      _ = ⁅X₀, X₀⁆ := by rw [hPmap]
      _ = X₀ := commutator_self_eq_of_isQuasisimple hX₀.2.2
  have hP_le_sup : P ≤ X ⊔ π.ker := by
    intro p hp
    have hpX₀ : π p ∈ X₀ := by
      rw [← hPmap]
      exact Subgroup.mem_map_of_mem π hp
    rw [← hXmap] at hpX₀
    obtain ⟨a, ha, hap⟩ := Subgroup.mem_map.mp hpX₀
    have hker : a⁻¹ * p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hap, inv_mul_cancel]
    have hmem : a * (a⁻¹ * p) ∈ X ⊔ π.ker := Subgroup.mul_mem_sup ha hker
    simpa [mul_assoc] using hmem
  have hXperf : ⁅X, X⁆ = X := by
    apply le_antisymm (Subgroup.commutator_le_self X)
    calc X = ⁅P, P⁆ := rfl
      _ ≤ ⁅X ⊔ π.ker, X ⊔ π.ker⁆ := Subgroup.commutator_mono hP_le_sup hP_le_sup
      _ = ⁅X, X⁆ :=
        CFSG.ComponentClassification.CentralExtensions.commutator_sup_central X π.ker hker
  have hXperf' : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.2 hXperf
  let f : ↥X →* ↥X₀ := (π.comp X.subtype).codRestrict X₀ fun x => by
    have hx : π (x : H) ∈ X.map π := Subgroup.mem_map_of_mem π x.2
    rwa [hXmap] at hx
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : Q) ∈ X.map π := hXmap.symm ▸ y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hkerf : f.ker ≤ Subgroup.center ↥X := by
    intro x hx
    have hxker : (x : H) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hx
    have hxcenter : (x : H) ∈ Subgroup.center H := hker hxker
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxcenter (y : H))
  have hXq : CFSG.Open.IsQuasisimple ↥X :=
    @CFSG.ComponentClassification.CentralExtensions.quasisimple_of_surjective
      ↥X ↥X₀ _ _ hXperf' hX₀.2.2 f hf hkerf
  have hXcomp : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({z} : Set H)) :=
    ⟨hXleP.trans hPle, CFSG.Assembly.isSubnormal_iff_open.mp hXsub, hXq⟩
  refine ⟨X, CFSG.Assembly.isComponentOf_iff_open.mpr hXcomp, hXmap, ?_⟩
  intro J hJ hJmap
  have hJP : J ≤ P := Subgroup.map_le_iff_le_comap.mp hJmap
  rw [← hJ]
  exact Subgroup.commutator_mono hJP hJP

end CFSG.StandardType

end
