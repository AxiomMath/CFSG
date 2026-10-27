module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosure
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.LocalAnalysis.StandardType.GGPZTrivCoprime

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggPZ_eq_mul_core {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H Y J : Subgroup G} {x : G} (hY : LargeEvenPComponent p H Y) (hx : x ^ p = 1) (hx1 : x ≠ 1)
    (hxY : x ∈ Subgroup.normalizer (Y : Set G))
    (hcomm : (⁅Y, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p Y)
    (hJsub : IsSubnormal J (Y ⊓ Subgroup.centralizer ({x} : Set G)))
    (hJq : IsQuasisimple ↥J) (hpJ : p ∣ Nat.card ↥J) :
    ∀ u ∈ Y, ∃ j ∈ J, ∃ n ∈ LargeEvenPPrimeCoreOf p Y, u = j * n := by
  have hYleH : Y ≤ H := hY.1
  set OH : Subgroup G := LargeEvenPPrimeCoreOf p H with hOHdef
  set N : Subgroup G := LargeEvenPPrimeCoreOf p Y with hNdef
  have hN_le_OH : N ≤ OH := by
    rw [hNdef, hOHdef]
    exact ggPPrimeCoreOf_le_of_isSubnormal hY.2.1
  have hN_le_Y : N ≤ Y := by
    rw [hNdef]
    exact Subgroup.map_subtype_le (LargeEvenPPrimeCore p ↥Y)
  have hOHnorm : Y ≤ Subgroup.normalizer (OH : Set G) :=
    hYleH |>.trans
      (Subgroup.le_normalizer.trans (ggNormalizer_le_normalizer_pPrimeCoreOf p H))
  have hME : Y ≤ Subgroup.normalizer ((Y ⊓ OH : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hOHnorm).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcop : Nat.Coprime p (Nat.card ↥(Y ⊓ OH)) :=
    (ggPPrimeCoreOf_coprime H).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  have hYinfOH_le_N : Y ⊓ OH ≤ N := by
    rw [hNdef]
    exact ggLe_pPrimeCoreOf inf_le_left hME hcop
  have hN_eq : N = Y ⊓ OH := le_antisymm (le_inf hN_le_Y hN_le_OH) hYinfOH_le_N
  let mkH : ↥H →* (↥H ⧸ LargeEvenPPrimeCore p ↥H) :=
    QuotientGroup.mk' (LargeEvenPPrimeCore p ↥H)
  let f : ↥Y →* (↥H ⧸ LargeEvenPPrimeCore p ↥H) := mkH.comp (Subgroup.inclusion hYleH)
  let Q : Subgroup (↥H ⧸ LargeEvenPPrimeCore p ↥H) := (Y.subgroupOf H).map mkH
  let Jbar : Subgroup (↥H ⧸ LargeEvenPPrimeCore p ↥H) := (J.subgroupOf Y).map f
  have hQ_eq : (⊤ : Subgroup ↥Y).map f = Q := by
    have h1 : (⊤ : Subgroup ↥Y).map (Subgroup.inclusion hYleH) = Y.subgroupOf H := by
      rw [Subgroup.map_top, Subgroup.inclusion_range hYleH]
    have h2 := Subgroup.map_map (g := mkH) (f := Subgroup.inclusion hYleH)
      (K := (⊤ : Subgroup ↥Y))
    rw [h1] at h2
    exact h2.symm
  have hOH_eq : OH = (LargeEvenPPrimeCore p ↥H).map H.subtype := by
    rw [hOHdef]
    rfl
  have hmem_OH : ∀ y : ↥Y, (y : G) ∈ OH ↔
      Subgroup.inclusion hYleH y ∈ LargeEvenPPrimeCore p ↥H := by
    intro y
    rw [hOH_eq]
    constructor
    · intro hz
      obtain ⟨h, hh, hhq⟩ := Subgroup.mem_map.mp hz
      have hy : Subgroup.inclusion hYleH y = h := Subtype.ext hhq.symm
      rwa [hy]
    · intro hy
      exact Subgroup.mem_map_of_mem H.subtype hy
  have hker : f.ker = N.subgroupOf Y := by
    rw [← MonoidHom.comap_ker mkH (Subgroup.inclusion hYleH), QuotientGroup.ker_mk']
    ext y
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hN_eq, Subgroup.mem_inf, hmem_OH y]
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
  have hT1 := ggPZ_coprime_lift hx hx1 hxY hcomm
  have hCQ : ((Y ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf Y).map f = Q := by
    apply le_antisymm
    · calc ((Y ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf Y).map f
          ≤ (⊤ : Subgroup ↥Y).map f := Subgroup.map_mono le_top
        _ = Q := hQ_eq
    · change (Y.subgroupOf H).map mkH
          ≤ ((Y ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf Y).map f
      rintro x ⟨z, hz, rfl⟩
      have hzy : (z : G) ∈ Y := Subgroup.mem_subgroupOf.mp hz
      obtain ⟨c, hc, n, hn, hcn⟩ := hT1 (z : G) hzy
      have hnN : n ∈ N := by rw [hNdef]; exact hn
      have hnY : n ∈ Y := (hN_eq ▸ hnN).1
      have hnOH : n ∈ OH := (hN_eq ▸ hnN).2
      have hn_ker : mkH ⟨n, hYleH hnY⟩ = 1 := by
        simpa only [mkH, QuotientGroup.mk'_apply] using
          (QuotientGroup.eq_one_iff (N := LargeEvenPPrimeCore p ↥H)
            (⟨n, hYleH hnY⟩ : ↥H)).mpr ((hmem_OH ⟨n, hnY⟩).mp hnOH)
      refine Subgroup.mem_map.mpr ⟨⟨c, hc.1⟩, Subgroup.mem_subgroupOf.mpr hc, ?_⟩
      have hz_eq : z = (⟨c, hYleH hc.1⟩ : ↥H) * ⟨n, hYleH hnY⟩ := by
        apply Subtype.ext
        simpa using hcn
      rw [hz_eq, map_mul, hn_ker, mul_one]
      rfl
  have hJY : J ≤ Y := hJsub.le.trans inf_le_left
  have hJbar_le_Q : Jbar ≤ Q := by
    change (J.subgroupOf Y).map f ≤ (Y.subgroupOf H).map mkH
    rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_map_of_mem mkH (Subgroup.mem_subgroupOf.mpr y.2)
  have hJsubY : IsSubnormal (J.subgroupOf Y)
      ((Y ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf Y) := hJsub.comap Y.subtype
  have hJbar_sub : IsSubnormal Jbar Q := by
    have hmap := hJsubY.map f
    rw [hCQ] at hmap
    exact hmap
  have hJbar_sub_open : CFSG.Open.IsSubnormal Jbar Q :=
    CFSG.Assembly.isSubnormal_iff_open.mp hJbar_sub
  let g : ↥J →* (↥H ⧸ LargeEvenPPrimeCore p ↥H) := f.comp (Subgroup.inclusion hJY)
  have hJbar_eq_range : Jbar = g.range := by
    change (J.subgroupOf Y).map f = g.range
    have h1 : (⊤ : Subgroup ↥J).map (Subgroup.inclusion hJY) = J.subgroupOf Y := by
      rw [Subgroup.map_top, Subgroup.inclusion_range hJY]
    rw [← Subgroup.map_top g, ← h1, Subgroup.map_map]
  have hperf : ⁅Jbar, Jbar⁆ = Jbar := by
    rw [hJbar_eq_range, ← Subgroup.map_top g, ← Subgroup.map_commutator]
    exact congrArg (Subgroup.map g) hJq.1.commutator_eq_top
  have hJnot_le_N : ¬ J ≤ N := by
    intro hle
    have hdvd : p ∣ Nat.card ↥N := hpJ.trans (Subgroup.card_dvd_of_le hle)
    have hcopN : Nat.Coprime p (Nat.card ↥N) := by
      rw [hNdef]
      exact ggPPrimeCoreOf_coprime Y
    have hp1 : p = 1 := Nat.eq_one_of_dvd_coprimes hcopN dvd_rfl hdvd
    exact (Fact.out : Nat.Prime p).ne_one hp1
  have hJbar_ne_bot : Jbar ≠ ⊥ := by
    intro hbot
    apply hJnot_le_N
    intro j hj
    have hmem : f (Subgroup.inclusion hJY ⟨j, hj⟩) ∈ Jbar :=
      Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hj)
    rw [hbot, Subgroup.mem_bot] at hmem
    have hker_mem : Subgroup.inclusion hJY ⟨j, hj⟩ ∈ f.ker := MonoidHom.mem_ker.mpr hmem
    rw [hker, Subgroup.mem_subgroupOf] at hker_mem
    simpa using hker_mem
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJbar_ne_bot
  have hQ : CFSG.Open.IsQuasisimple ↥Q := hY.2.2.1.2.2
  have hJbar_eq_Q : Jbar = Q :=
    CFSG.ClassicalInvolution.eq_of_perfect_subnormal_of_isQuasisimple hQ hJbar_le_Q
      hJbar_sub_open hperf z.2 (fun h => hz1 (Subtype.ext h))
  intro u hu
  have hu_Q : f ⟨u, hu⟩ ∈ Q := by
    rw [← hQ_eq]
    exact Subgroup.mem_map_of_mem f (Subgroup.mem_top (⟨u, hu⟩ : ↥Y))
  have hu_Jbar : f ⟨u, hu⟩ ∈ Jbar := by
    rw [hJbar_eq_Q]
    exact hu_Q
  obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp hu_Jbar
  refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, (y : G)⁻¹ * u, ?_, ?_⟩
  · have hmem_ker : y⁻¹ * ⟨u, hu⟩ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfy, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hmem_ker
    simpa [hNdef] using hmem_ker
  · group

end CFSG.StandardType

end
