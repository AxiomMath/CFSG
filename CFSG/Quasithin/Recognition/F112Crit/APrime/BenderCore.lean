module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.BenderVertex
public import CFSG.Quasithin.Background.F7
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenLift
public import CFSG.GroupTheory.CentralExtensionPGroup
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem BenderVertex.pCoreOf_le_pCoreOf {H K : Subgroup G} (hB : BenderVertex H K) :
    pCoreOf 2 K ≤ pCoreOf 2 H :=
  CFSG.Quasithin.F7.pCoreOf_mono_of_le_normalizer hB.le hB.normalizes

private theorem commutator_mem_pCoreOf {H K N : Subgroup G} (hB : BenderVertex H K)
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hQN : pCoreOf 2 H ≤ N)
    (hKN : ¬ K ≤ N) {x : G} (hxH : x ∈ H)
    (hxK : ∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ N) :
    ∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 K := by
  classical
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hB.normalizes hxH
  let φ : MulAut ↥K := K.normalizerMonoidHom ⟨x, hxN⟩
  have hφ : ∀ y : ↥K, ((φ y : ↥K) : G) = x * (y : G) * x⁻¹ :=
    fun y => Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨x, hxN⟩ y
  let MK : Subgroup ↥K := (K ⊓ N).subgroupOf K
  have hMKn : MK.Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    change ((g : G) * (m : G) * (g : G)⁻¹) ∈ K ⊓ N
    refine ⟨?_, ?_⟩
    · exact K.mul_mem (K.mul_mem g.2 hm.1) (K.inv_mem g.2)
    · have hgH : (g : G) ∈ H := hB.le g.2
      have hconj : (g : G) * (m : G) * (g : G)⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hHN hgH) (m : G)).mp hm.2
      simpa using hconj
  let πK : ↥K →* oTwoQuot ↥K := QuotientGroup.mk' (pCore 2 ↥K)
  let Mbar : Subgroup (oTwoQuot ↥K) := MK.map πK
  have hMbarN : Mbar.Normal := hMKn.map πK (QuotientGroup.mk'_surjective (pCore 2 ↥K))
  have hMbar_ne : Mbar ≠ ⊤ := by
    intro htop
    apply hKN
    intro y hy
    have hsup : (pCore 2 ↥K) ⊔ MK = ⊤ := by
      have h := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 ↥K))) htop
      rw [QuotientGroup.comap_map_mk'] at h
      simpa using h
    have hyK : (⟨y, hy⟩ : ↥K) ∈ (pCore 2 ↥K) ⊔ MK := by
      rw [hsup]; exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_left] at hyK
    obtain ⟨q, hq, m, hm, hqm⟩ := hyK
    rw [Subgroup.mem_subgroupOf] at hm
    have hqQ : (q : G) ∈ pCoreOf 2 K :=
      (CFSG.mem_openPCoreOf_iff_open q).mpr hq
    have hqN : (q : G) ∈ N := hQN (BenderVertex.pCoreOf_le_pCoreOf hB hqQ)
    have hmN : (m : G) ∈ N := hm.2
    have hyval : (q : G) * (m : G) = y := by
      simpa using congrArg Subtype.val hqm
    rw [← hyval]
    exact N.mul_mem hqN hmN
  haveI : Mbar.Normal := hMbarN
  have hMbar_center : Mbar ≤ Subgroup.center (oTwoQuot ↥K) :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hB.quasisimple hMbarN).resolve_left hMbar_ne
  have hchar : Subgroup.map φ.toMonoidHom (pCore 2 ↥K) = pCore 2 ↥K :=
    Subgroup.characteristic_iff_map_eq.mp (CFSG.LieType.BorelTits.pCore_characteristic 2) φ
  let α : MulAut (oTwoQuot ↥K) :=
    QuotientGroup.congr (pCore 2 ↥K) (pCore 2 ↥K) φ hchar
  have hα : ∀ y : ↥K, α (πK y) = πK (φ y) :=
    fun y => QuotientGroup.congr_mk (pCore 2 ↥K) (pCore 2 ↥K) φ hchar y
  have hdev : ∀ g : oTwoQuot ↥K, α g * g⁻¹ ∈ Subgroup.center (oTwoQuot ↥K) := by
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥K) g
    have hmemM : πK (y * (φ y)⁻¹) ∈ Mbar := by
      refine Subgroup.mem_map_of_mem πK ?_
      rw [Subgroup.mem_subgroupOf]
      change ((y * (φ y)⁻¹ : ↥K) : G) ∈ K ⊓ N
      refine ⟨K.mul_mem y.2 (K.inv_mem (φ y).2), ?_⟩
      have hcoe : ((y * (φ y)⁻¹ : ↥K) : G) = (y : G) * x * (y : G)⁻¹ * x⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ y]
        group
      rw [hcoe]
      exact hxK (y : G) y.2
    have hval : α (πK y) * (πK y)⁻¹ = (πK (y * (φ y)⁻¹))⁻¹ := by
      have e1 : (πK (y * (φ y)⁻¹))⁻¹ = πK (φ y * y⁻¹) := by
        rw [← map_inv]
        congr 1
        group
      have e2 : πK (φ y) * (πK y)⁻¹ = πK (φ y * y⁻¹) := by
        rw [← map_inv, ← map_mul]
      rw [hα y, e2, e1]
    rw [hval]
    exact Subgroup.inv_mem _ (hMbar_center hmemM)
  have hdev' : ∀ x : oTwoQuot ↥K, x⁻¹ * α x ∈ Subgroup.center (oTwoQuot ↥K) := by
    intro x
    have hc := hdev x
    have hcomm : x⁻¹ * (α x * x⁻¹) = (α x * x⁻¹) * x⁻¹ :=
      Subgroup.mem_center_iff.mp hc x⁻¹
    have hx : x⁻¹ * α x = α x * x⁻¹ := by
      calc x⁻¹ * α x = x⁻¹ * (α x * x⁻¹) * x := by group
        _ = (α x * x⁻¹) * x⁻¹ * x := by rw [hcomm]
        _ = α x * x⁻¹ := by group
    rw [hx]
    exact hc
  have hα1 : α = 1 :=
    CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen.eq_one_of_central_deviation
      hB.quasisimple.1.commutator_eq_top α hdev'
  intro y hy
  let yK : ↥K := ⟨y, hy⟩
  have hfix : πK (φ yK) = πK yK := by
    have h := congrArg (fun e : MulAut (oTwoQuot ↥K) => e (πK yK)) hα1
    simpa [hα yK] using h
  have hmem : yK * (φ yK)⁻¹ ∈ pCore 2 ↥K := by
    refine (QuotientGroup.eq_one_iff (yK * (φ yK)⁻¹)).mp ?_
    change πK (yK * (φ yK)⁻¹) = 1
    rw [map_mul, map_inv, hfix, mul_inv_cancel]
  have hmemG : ((yK * (φ yK)⁻¹ : ↥K) : G) ∈ pCoreOf 2 K :=
    (CFSG.mem_openPCoreOf_iff_open (yK * (φ yK)⁻¹)).mpr hmem
  have hcoe : ((yK * (φ yK)⁻¹ : ↥K) : G) = y * x * y⁻¹ * x⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ yK]
    have hyKval : ((yK : ↥K) : G) = y := rfl
    rw [hyKval]
    group
  rwa [hcoe] at hmemG

theorem BenderVertex.mem_pCoreOf {H K N : Subgroup G} (hB : BenderVertex H K)
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hQN : pCoreOf 2 H ≤ N)
    (hKN : ¬ K ≤ N) {x : G} (hxH : x ∈ H) (hx : ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hxK : ∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ N) : x ∈ pCoreOf 2 H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstep1 : ∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 K :=
    commutator_mem_pCoreOf hB hNH hHN hQN hKN hxH hxK
  have hstep1' : ∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 H :=
    fun y hy => BenderVertex.pCoreOf_le_pCoreOf hB (hstep1 y hy)
  let Y := ↥H
  let QY : Subgroup Y := pCore 2 Y
  let πQ : Y →* Y ⧸ QY := QuotientGroup.mk' QY
  let KY : Subgroup Y := K.subgroupOf H
  let Kbar : Subgroup (Y ⧸ QY) := KY.map πQ
  let Dbar : Subgroup (Y ⧸ QY) := Subgroup.centralizer (Kbar : Set (Y ⧸ QY))
  let xY : Y := ⟨x, hxH⟩
  have hKYn : KY.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hB.le).mpr hB.normalizes
  have hKbarN : Kbar.Normal := hKYn.map πQ (QuotientGroup.mk'_surjective QY)
  haveI : Kbar.Normal := hKbarN
  haveI : Dbar.Normal := Subgroup.normal_centralizer
  have hxbarD : πQ xY ∈ Dbar := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨y, hyKY, rfl⟩ := Subgroup.mem_map.mp hz
    have hmemQ : y * xY * y⁻¹ * xY⁻¹ ∈ QY := by
      rw [← CFSG.mem_openPCoreOf_iff_open]
      have hyK : (y : G) ∈ K := (Subgroup.mem_subgroupOf.mp hyKY)
      have hcoe : ((y * xY * y⁻¹ * xY⁻¹ : Y) : G) =
          (y : G) * x * (y : G)⁻¹ * x⁻¹ := by
        change H.subtype (y * xY * y⁻¹ * xY⁻¹) =
          H.subtype y * x * (H.subtype y)⁻¹ * x⁻¹
        simp only [map_mul, map_inv]
        rfl
      rw [hcoe]
      exact hstep1' (y : G) hyK
    have hQ1 : πQ (y * xY * y⁻¹ * xY⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmemQ
    have hc : πQ y * πQ xY * (πQ y)⁻¹ * (πQ xY)⁻¹ = 1 := by
      have e : πQ y * πQ xY * (πQ y)⁻¹ * (πQ xY)⁻¹ =
          πQ (y * xY * y⁻¹ * xY⁻¹) := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [e, hQ1]
    calc πQ y * πQ xY =
        (πQ y * πQ xY * (πQ y)⁻¹ * (πQ xY)⁻¹) * (πQ xY * πQ y) := by group
      _ = πQ xY * πQ y := by rw [hc, one_mul]

  let ψ : Y →* (Y ⧸ QY) ⧸ Kbar := (QuotientGroup.mk' Kbar).comp πQ
  have hψsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective Kbar).comp (QuotientGroup.mk'_surjective QY)
  have htarget2 : IsPGroup 2 ((Y ⧸ QY) ⧸ Kbar) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro t
    obtain ⟨y, rfl⟩ := hψsurj t
    obtain ⟨k, hk⟩ := hB.two_quot (y : G) y.2
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have hyK : (y ^ 2 ^ k : Y) ∈ KY := by
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((y ^ 2 ^ k : Y) : G) = (y : G) ^ 2 ^ k := by
        change H.subtype (y ^ 2 ^ k) = H.subtype y ^ 2 ^ k
        rw [map_pow]
      rw [hcoe]
      exact hk
    have hmem : πQ (y ^ 2 ^ k) ∈ Kbar := Subgroup.mem_map_of_mem πQ hyK
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  have hDbarNil : Group.IsNilpotent ↥Dbar := by
    let f : ↥Dbar →* (Y ⧸ QY) ⧸ Kbar := (QuotientGroup.mk' Kbar).comp Dbar.subtype
    have hker : f.ker ≤ Subgroup.center ↥Dbar := by
      intro c hc
      rw [MonoidHom.mem_ker] at hc
      have hcK : ((c : ↥Dbar) : Y ⧸ QY) ∈ Kbar :=
        (QuotientGroup.eq_one_iff _).mp hc
      rw [Subgroup.mem_center_iff]
      intro d
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp d.2 _ hcK).symm
    haveI : Group.IsNilpotent ((Y ⧸ QY) ⧸ Kbar) := htarget2.isNilpotent
    exact Subgroup.isNilpotent_of_ker_le_center f hker
  let Pbar : Sylow 2 ↥Dbar := default
  have hPbarN : (Pbar : Subgroup ↥Dbar).Normal :=
    Group.IsNilpotent.sylow_normal hDbarNil 2 Pbar
  have hPbarChar : (Pbar : Subgroup ↥Dbar).Characteristic :=
    Sylow.characteristic_of_normal Pbar hPbarN
  have hPimN : ((Pbar : Subgroup ↥Dbar).map Dbar.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal (H := Dbar) (K := (Pbar : Subgroup ↥Dbar))
  let P : Subgroup Y := ((Pbar : Subgroup ↥Dbar).map Dbar.subtype).comap πQ
  have hPN : P.Normal := hPimN.comap πQ
  have hP2 : IsPGroup 2 ↥P := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro p
    have hpim : πQ (p : Y) ∈ (Pbar : Subgroup ↥Dbar).map Dbar.subtype :=
      Subgroup.mem_comap.mp p.2
    obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.mp hpim
    obtain ⟨k, hk⟩ := (Pbar.isPGroup') ⟨z, hz⟩
    have hzpow : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hpQ : (p : Y) ^ 2 ^ k ∈ QY := by
      have hzval' : (Dbar.subtype z : Y ⧸ QY) = πQ (p : Y) := hzval
      refine (QuotientGroup.eq_one_iff _).mp ?_
      calc πQ ((p : Y) ^ 2 ^ k) = (πQ (p : Y)) ^ 2 ^ k := map_pow πQ _ _
        _ = (Dbar.subtype z) ^ 2 ^ k := by rw [← hzval']
        _ = Dbar.subtype (z ^ 2 ^ k) := map_pow Dbar.subtype _ _
        _ = 1 := by rw [hzpow, map_one]
    obtain ⟨m, hm⟩ :=
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := Y) 2) ⟨(p : Y) ^ 2 ^ k, hpQ⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have hmval : ((p : Y) ^ 2 ^ k) ^ 2 ^ m = 1 := congrArg Subtype.val hm
    calc ((p : Y) ^ 2 ^ (k + m)) = ((p : Y) ^ 2 ^ k) ^ 2 ^ m := by
          rw [pow_add, pow_mul]
      _ = 1 := hmval
  have hPleQ : P ≤ QY := CFSG.LieType.BorelTits.le_pCore 2 hPN hP2
  have hQleP : QY ≤ P := by
    intro q hq
    show πQ q ∈ (Pbar : Subgroup ↥Dbar).map Dbar.subtype
    have hq1 : πQ q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
    rw [hq1]
    exact Subgroup.one_mem _
  have hP_eq : P = QY := le_antisymm hPleQ hQleP
  let xbar : ↥Dbar := ⟨πQ xY, hxbarD⟩
  have hxbar2 : ∃ k : ℕ, xbar ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, Subtype.ext ?_⟩
    have hxYpow : (xY : Y) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      change ((xY : Y) : G) ^ 2 ^ k = ((1 : Y) : G)
      rw [show ((xY : Y) : G) = x from rfl]
      simpa using hk
    calc ((xbar : ↥Dbar) : Y ⧸ QY) ^ 2 ^ k = (πQ xY) ^ 2 ^ k := rfl
      _ = πQ ((xY : Y) ^ 2 ^ k) := by rw [map_pow]
      _ = 1 := by rw [hxYpow, map_one]
  obtain ⟨k, hk⟩ := hxbar2
  have hxbarP : xbar ∈ (Pbar : Subgroup ↥Dbar) :=
    CFSG.GroupTheory.mem_sylow_of_pow_eq_one hPbarN hk
  have hxYP : xY ∈ P :=
    Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem Dbar.subtype hxbarP)
  have hxYQ : xY ∈ QY := by rw [← hP_eq]; exact hxYP
  have hxQ : ((xY : G)) ∈ pCoreOf 2 H := (CFSG.mem_openPCoreOf_iff_open xY).mpr hxYQ
  simpa using hxQ

theorem BenderVertex.mem_pCoreOf_of_mem {H K N : Subgroup G} (hB : BenderVertex H K)
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hQN : pCoreOf 2 H ≤ N)
    (hKN : ¬ K ≤ N) {x : G} (hxN : x ∈ N) (hx : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    x ∈ pCoreOf 2 H := by
  refine BenderVertex.mem_pCoreOf hB hNH hHN hQN hKN (hNH hxN) hx ?_
  intro y hy
  have hyN : y ∈ Subgroup.normalizer (N : Set G) := hHN (hB.le hy)
  exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN x).mp hxN) (N.inv_mem hxN)

theorem BenderVertex.le_pCoreOf {H K N P : Subgroup G} (hB : BenderVertex H K)
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hQN : pCoreOf 2 H ≤ N)
    (hKN : ¬ K ≤ N) (hPN : P ≤ N) (hP : IsPGroup 2 P) : P ≤ pCoreOf 2 H := by
  intro x hxP
  refine BenderVertex.mem_pCoreOf_of_mem hB hNH hHN hQN hKN (hPN hxP) ?_
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem BenderVertex.pCoreOf_eq {H K N : Subgroup G} (hB : BenderVertex H K)
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hQN : pCoreOf 2 H ≤ N)
    (hKN : ¬ K ≤ N) : pCoreOf 2 N = pCoreOf 2 H := by
  refine le_antisymm ?_ ?_
  · exact CFSG.Quasithin.F7.pCoreOf_mono_of_le_normalizer hNH hHN
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQN
      (hNH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

theorem BenderVertex.inf_eq_pCoreOf {H K N T : Subgroup G} (hB : BenderVertex H K)
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hQN : pCoreOf 2 H ≤ N)
    (hKN : ¬ K ≤ N) (hT : IsSylowTwoOf T H) : T ⊓ N = pCoreOf 2 N := by
  have hQeq := BenderVertex.pCoreOf_eq hB hNH hHN hQN hKN
  refine le_antisymm ?_ ?_
  · have hP : IsPGroup 2 ↥(T ⊓ N) := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro x
      obtain ⟨k, hk⟩ := (hT.2.1) ⟨(x : G), x.2.1⟩
      refine ⟨k, Subtype.ext ?_⟩
      have hk' : (x : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      simpa [Subgroup.coe_pow] using hk'
    have hle : T ⊓ N ≤ pCoreOf 2 H :=
      BenderVertex.le_pCoreOf hB hNH hHN hQN hKN inf_le_right hP
    rwa [hQeq]
  · rw [hQeq]
    exact le_inf (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hT) hQN

theorem BenderVertex.mem_pCoreOf_of_centralizer {H K V : Subgroup G} (hB : BenderVertex H K)
    (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hQV : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G))
    (hKV : ¬ K ≤ Subgroup.centralizer (V : Set G)) {x : G} (hxH : x ∈ H)
    (hx : ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hxK : ∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    x ∈ pCoreOf 2 H := by
  refine BenderVertex.mem_pCoreOf hB inf_le_left ?_ (le_inf (pCoreOf_le 2 H) hQV) ?_ hxH hx ?_
  · exact CFSG.Quasithin.F7.le_normalizer_inf Subgroup.le_normalizer
      (hHV.trans (CFSG.Quasithin.F7.normalizer_le_normalizer_centralizer V))
  · rintro h
    exact hKV (fun x hx => (h hx).2)
  · intro y hy
    refine ⟨?_, hxK y hy⟩
    exact H.mul_mem (H.mul_mem (H.mul_mem (hB.le hy) hxH) (H.inv_mem (hB.le hy)))
      (H.inv_mem hxH)

theorem BenderVertex.inf_centralizer_eq {H K V T : Subgroup G} (hB : BenderVertex H K)
    (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hQV : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G))
    (hKV : ¬ K ≤ Subgroup.centralizer (V : Set G)) (hT : IsSylowTwoOf T H) :
    T ⊓ Subgroup.centralizer (V : Set G) =
      pCoreOf 2 (H ⊓ Subgroup.centralizer (V : Set G)) := by
  have h1 : T ⊓ Subgroup.centralizer (V : Set G) =
      T ⊓ (H ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [← inf_assoc, inf_eq_left.mpr hT.1]
  rw [h1]
  exact BenderVertex.inf_eq_pCoreOf hB inf_le_left
    (CFSG.Quasithin.F7.le_normalizer_inf Subgroup.le_normalizer
      (hHV.trans (CFSG.Quasithin.F7.normalizer_le_normalizer_centralizer V)))
    (le_inf (pCoreOf_le 2 H) hQV)
    (by rintro h; exact hKV (fun x hx => (h hx).2)) hT

end CFSG.Quasithin.F112Crit.APrime

end
