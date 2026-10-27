module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48RestZp
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48Tail

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

section Config

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_sup_of_mem_normalizer {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Subgroup G} (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁) {n z : G}
    (hn : n ∈ Subgroup.normalizer (U₁ : Set G))
    (hz : z ∈ ggL48H0 x U₁ ⊓
      Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) :
    n * z * n⁻¹ ∈ (ggL48H0 x U₁ ⊓
      Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) ⊔
        Subgroup.centralizer (U₁ : Set G) := by
  obtain ⟨-, -, hxN, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
  obtain ⟨s, hs2, hexp, ⟨u₀, hu₀, hord⟩, ⟨x', hx'x, hx'⟩, -⟩ := h46.2.1
  have hB₁iff := h46.2.2.2.1
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set C₀ : Subgroup G := Subgroup.centralizer (U₁ : Set G) with hC₀
  set N₀ : Subgroup G := Subgroup.normalizer (U₁ : Set G) with hN₀
  set D₀ : Subgroup G := ggL48H0 x U₁ ⊓ Subgroup.centralizer (B₁ : Set G) with hD₀
  have hNB : N₀ ≤ Subgroup.normalizer (B₁ : Set G) := normalizer_le_normalizer_of_mem_iff hB₁iff
  have hCN : C₀ ≤ N₀ := Subgroup.centralizer_le_normalizer _
  have hx'mem : x' ∈ Subgroup.zpowers x := hx'x ▸ Subgroup.mem_zpowers x'
  have hxmem : x ∈ Subgroup.zpowers x' := hx'x.symm ▸ Subgroup.mem_zpowers x
  have hx'N : x' ∈ N₀ := (Subgroup.zpowers_le.mpr hxN) hx'mem
  have hBs : IsElemAbelian p Bs := hS.1.1.2.1.2.1
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hS.1.1.1.2.2.2.2.2.2.1.2.1
  have hx'Bs : x' ∈ Bs := (Subgroup.zpowers_le.mpr hxBs) hx'mem
  have hx'c : x' ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx'mem
    rw [← hj]
    exact ((Commute.refl x).zpow_left j).eq
  have hx'D : x' ∈ D₀ := ⟨⟨hx'c, hx'N⟩, Subgroup.mem_centralizer_iff.mpr fun b hb =>
    mul_comm_of_isElemAbelian hBs hb.1 hx'Bs⟩
  obtain ⟨g, hgT, u, hu, hup, hgu⟩ := exists_conj_eq_mul_of_mem_normalizer hS h46 hRp hRmax hA
    hs2 hexp hu₀ hord hx'x hx' (N₀.inv_mem hn)
  rw [inv_inv] at hgu
  have hgN : g ∈ N₀ := sup_le hCN (Subgroup.zpowers_le.mpr hx'N) hgT
  have hgY : g ∈ D₀ ⊔ C₀ :=
    sup_le le_sup_right (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hx'D)) hgT
  have hmN : g * n ∈ N₀ := N₀.mul_mem hgN hn
  have hmx : (g * n) * x' * (g * n)⁻¹ = x' * u := by
    rw [← hgu]
    group
  have hz'N : (g * n) * z * (g * n)⁻¹ ∈ N₀ :=
    N₀.mul_mem (N₀.mul_mem hmN hz.1.2) (N₀.inv_mem hmN)
  have hz'B : (g * n) * z * (g * n)⁻¹ ∈ Subgroup.centralizer (B₁ : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (ggNormalizer_le_normalizer_centralizer B₁ (hNB hmN)) z).mp
      hz.2
  have huB : u ∈ B₁ := (hB₁iff u).mpr ⟨hu, hup⟩
  have hzx' : z * x' = x' * z := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx'mem
    rw [← hj]
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hz.1.1) j).eq
  have h1 : (g * n) * z * (g * n)⁻¹ * (x' * u) = (x' * u) * ((g * n) * z * (g * n)⁻¹) := by
    rw [← hmx]
    calc (g * n) * z * (g * n)⁻¹ * ((g * n) * x' * (g * n)⁻¹) = (g * n) * (z * x') * (g * n)⁻¹ := by
          group
      _ = (g * n) * (x' * z) * (g * n)⁻¹ := by rw [hzx']
      _ = (g * n) * x' * (g * n)⁻¹ * ((g * n) * z * (g * n)⁻¹) := by group
  have h2 : u * ((g * n) * z * (g * n)⁻¹) = ((g * n) * z * (g * n)⁻¹) * u :=
    Subgroup.mem_centralizer_iff.mp hz'B u huB
  have h3 : (g * n) * z * (g * n)⁻¹ * x' = x' * ((g * n) * z * (g * n)⁻¹) := by
    calc (g * n) * z * (g * n)⁻¹ * x' = (g * n) * z * (g * n)⁻¹ * (x' * u) * u⁻¹ := by group
      _ = (x' * u) * ((g * n) * z * (g * n)⁻¹) * u⁻¹ := by rw [h1]
      _ = x' * (u * ((g * n) * z * (g * n)⁻¹)) * u⁻¹ := by group
      _ = x' * (((g * n) * z * (g * n)⁻¹) * u) * u⁻¹ := by rw [h2]
      _ = x' * ((g * n) * z * (g * n)⁻¹) := by group
  have hz'x : (g * n) * z * (g * n)⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
    rw [← hk]
    exact (Commute.zpow_right h3 k).eq
  have hz'D : (g * n) * z * (g * n)⁻¹ ∈ D₀ := ⟨⟨hz'x, hz'N⟩, hz'B⟩
  have e : n * z * n⁻¹ = g⁻¹ * ((g * n) * z * (g * n)⁻¹) * g := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgY)
    (Subgroup.mem_sup_left hz'D)) hgY

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_pow_eq_one {p a : ℕ} {w : G} (hw : w ^ p ^ a = 1) :
    IsPGroup p (Subgroup.zpowers w) := by
  rintro ⟨v, hv⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  refine ⟨a, Subtype.ext ?_⟩
  change (w ^ n) ^ p ^ a = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]

theorem commutatorElement_mem_centralizer_of_mem {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Subgroup G} (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁)
    (hcyc : ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁)
    (hcent : x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁) {h z : G}
    (hh : h ∈ ggL48H0 x U₁)
    (hz : z ∈ ggL48H0 x U₁ ⊓
      Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) :
    ⁅h, z⁆ ∈ Subgroup.centralizer (U₁ : Set G) := by
  obtain ⟨hp, hxp, hxN, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  have hab := h46.1
  have hB₁iff := h46.2.2.2.1
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set H₀ := ggL48H0 x U₁ with hH₀
  set C₀ : Subgroup G := Subgroup.centralizer (U₁ : Set G) with hC₀
  set N₀ : Subgroup G := Subgroup.normalizer (U₁ : Set G) with hN₀
  set D₀ : Subgroup G := H₀ ⊓ Subgroup.centralizer (B₁ : Set G) with hD₀
  have hcomm : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hU₁p : IsPGroup p U₁ := hRp.to_le (mem_thompsonAbelianSubgroups_of_forall_eq hA).1
  have hU₁C : U₁ ≤ C₀ := Subgroup.le_centralizer_iff_isMulCommutative.mpr hab
  have hNB : N₀ ≤ Subgroup.normalizer (B₁ : Set G) := normalizer_le_normalizer_of_mem_iff hB₁iff
  have hHN : H₀ ≤ N₀ := inf_le_right
  have hxH : x ∈ H₀ := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hxN⟩
  have hxU₁ : x ∉ U₁ := fun hx => hS.2.2.1.1 ((hB₁iff x).mpr ⟨hx, hxp⟩)
  have hBs : IsElemAbelian p Bs := hS.1.1.2.1.2.1
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hS.1.1.1.2.2.2.2.2.2.1.2.1
  have hxB : x ∈ Subgroup.centralizer (B₁ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun b hb => mul_comm_of_isElemAbelian hBs hb.1 hxBs
  have hDconj : ∀ a ∈ H₀, ∀ c ∈ D₀, a * c * a⁻¹ ∈ D₀ := fun a ha c hc =>
    ⟨H₀.mul_mem (H₀.mul_mem ha hc.1) (H₀.inv_mem ha),
      (Subgroup.mem_normalizer_iff.mp
        (ggNormalizer_le_normalizer_centralizer B₁ (hNB (hHN ha))) c).mp hc.2⟩
  have hkD : ⁅h, z⁆ ∈ D₀ := by
    rw [commutatorElement_def]
    exact D₀.mul_mem (hDconj h hh z hz) (D₀.inv_mem hz)
  have hkH : ⁅h, z⁆ ∈ ⁅H₀, H₀⁆ := Subgroup.commutator_mem_commutator hh hz.1
  by_contra hkC
  obtain ⟨a, m, hm, hkm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos ⁅h, z⁆).ne' p hp.one_lt.ne'
  have hkpa : ⁅h, z⁆ ^ p ^ a ∈ C₀ := by
    refine GGL48.mem_centralizer_of_coprime hab (fun u hu => ?_) hB₁iff
      (hHN (D₀.pow_mem hkD _).1) (D₀.pow_mem hkD _).2 hm ?_
    · obtain ⟨k, hk⟩ := hU₁p ⟨u, hu⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [← pow_mul, ← hkm, pow_orderOf_eq_one]
  have hwC : ⁅h, z⁆ ^ m ∉ C₀ := fun hw => hkC (mem_of_pow_mem_of_coprime
    (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)).symm hw hkpa)
  set w := ⁅h, z⁆ ^ m with hw
  have hwD : w ∈ D₀ := D₀.pow_mem hkD m
  have hwH : w ∈ ⁅H₀, H₀⁆ := Subgroup.pow_mem _ hkH m
  have hwp : w ^ p ^ a = 1 := by
    rw [hw, ← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  have hwxc : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.mp hwD.1.1
  have hwNx : Subgroup.zpowers w ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_left (show Commute x w from hwxc.symm) k).eq
  set Q : Subgroup G := (Subgroup.zpowers w ⊔ Subgroup.zpowers x) ⊔ U₁ with hQ
  have hQp : IsPGroup p Q :=
    IsPGroup.to_sup_of_normal_right' (IsPGroup.to_sup_of_normal_right'
      (isPGroup_zpowers_of_pow_pow_eq_one hwp) (GGL48.isPGroup_zpowers_of_pow_eq_one hxp) hwNx)
      hU₁p (sup_le (Subgroup.zpowers_le.mpr hwD.1.2) (Subgroup.zpowers_le.mpr hxN))
  set T : Subgroup G := Subgroup.centralizer (B₁ : Set G) ⊓ N₀ with hT
  have hU₁B : U₁ ≤ Subgroup.centralizer (B₁ : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm b ((hB₁iff b).mp hb).1 u hu
  have hQT : Q ≤ T := sup_le (sup_le (Subgroup.zpowers_le.mpr ⟨hwD.2, hwD.1.2⟩)
    (Subgroup.zpowers_le.mpr ⟨hxB, hxN⟩)) (le_inf hU₁B Subgroup.le_normalizer)
  have hU := hS.2.2.2.2.2.2.1
  have hUN : U ≤ N₀ :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_of_forall_eq h46.2.2.1)
  have hUT : U ≤ T := le_inf hU.1 hUN
  have hUmax : ∀ Q' : Subgroup G, Q' ≤ T → IsPGroup p Q' → U ≤ Q' → Q' = U :=
    fun Q' hQ'T hQ' hUQ' => hU.2.2.1 Q' (hQ'T.trans inf_le_left) hQ' hUQ'
  obtain ⟨t, ht⟩ := GGL48.exists_conj_mem_of_isPGroup
    (hQp.comap_of_injective T.subtype T.subtype_injective)
    (GGL48.sylowSubgroupOf hU.2.1 hUT hUmax)
  have hconjU : ∀ c ∈ Q, (t : G) * c * (t : G)⁻¹ ∈ U := by
    intro c hc
    have h1 := ht ⟨c, hQT hc⟩ hc
    rw [GGL48.coe_sylowSubgroupOf, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have htN : (t : G) ∈ N₀ := t.2.2
  obtain ⟨g, hgU, hUg⟩ := hcyc
  obtain ⟨j, hgj⟩ := hU.2.1 ⟨g, hgU⟩
  have hgj' : g ^ p ^ j = 1 := by simpa using congrArg Subtype.val hgj
  have hwQ : w ∈ Q := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers w))
  have hxQ : x ∈ Q := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have haU₁ : (t : G) * w * (t : G)⁻¹ ∉ U₁ := fun hU₁w =>
    hwC (hU₁C ((Subgroup.mem_normalizer_iff.mp htN w).mpr hU₁w))
  have hbp : ((t : G) * x * (t : G)⁻¹) ^ p ∈ U₁ := by
    rw [conj_pow, hxp, mul_one, mul_inv_cancel]
    exact U₁.one_mem
  have hmem := GGL48.mem_zpowers_sup_of_not_mem (hUN hgU) hgj' (hUg (hconjU w hwQ))
    (hUg (hconjU x hxQ)) haU₁ hbp
  have hle : Subgroup.zpowers ((t : G) * w * (t : G)⁻¹) ≤ N₀ :=
    Subgroup.zpowers_le.mpr (N₀.mul_mem (N₀.mul_mem htN hwD.1.2) (N₀.inv_mem htN))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hmem
  obtain ⟨v, hv, u, hu, hvu⟩ := hmem
  dsimp only at hvu
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hu' : (t : G)⁻¹ * u * t ∈ U₁ := by
    have := (Subgroup.mem_normalizer_iff.mp (N₀.inv_mem htN) u).mp hu
    simpa using this
  have hx_eq : x = w ^ i * ((t : G)⁻¹ * u * t) := by
    have h1 : ((t : G) * w * (t : G)⁻¹) ^ i = (t : G) * w ^ i * (t : G)⁻¹ := conj_zpow
    calc x = (t : G)⁻¹ * ((t : G) * x * (t : G)⁻¹) * t := by group
      _ = (t : G)⁻¹ * (((t : G) * w * (t : G)⁻¹) ^ i * u) * t := by rw [hvu]
      _ = w ^ i * ((t : G)⁻¹ * u * t) := by rw [h1]; group
  have huH : (t : G)⁻¹ * u * t ∈ H₀ := by
    have e : (t : G)⁻¹ * u * t = (w ^ i)⁻¹ * x := by rw [hx_eq]; group
    rw [e]
    exact H₀.mul_mem (H₀.inv_mem (H₀.zpow_mem hwD.1 i)) hxH
  have hm : w ^ i * ((t : G)⁻¹ * u * t) ∈ ⁅H₀, H₀⁆ ⊔ ggL48U2 x U₁ :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem _ hwH i))
      (Subgroup.mem_sup_right ⟨hu', huH.1⟩)
  rw [← hx_eq] at hm
  exact hcent hm

theorem commutatorElement_mem_centralizer_of_frobenius {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Subgroup G} (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁)
    (hcyc : ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁)
    (hcent : x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁)
    (hind : (ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).relIndex
      (Subgroup.normalizer (U₁ : Set G)) = p)
    (hnorm : ¬ ((ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).subgroupOf
      (Subgroup.normalizer (U₁ : Set G))).Normal) {n v : G}
    (hn : n ∈ Subgroup.normalizer (U₁ : Set G))
    (hv : v ∈ (ggL48H0 x U₁ ⊓
      Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) ⊔
        Subgroup.centralizer (U₁ : Set G)) :
    ⁅n, v⁆ ∈ Subgroup.centralizer (U₁ : Set G) := by
  obtain ⟨hp, -, -, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set H₀ := ggL48H0 x U₁ with hH₀
  set C₀ : Subgroup G := Subgroup.centralizer (U₁ : Set G) with hC₀
  set N₀ : Subgroup G := Subgroup.normalizer (U₁ : Set G) with hN₀
  set D₀ : Subgroup G := H₀ ⊓ Subgroup.centralizer (B₁ : Set G) with hD₀
  have hNC : N₀ ≤ Subgroup.normalizer (C₀ : Set G) := ggNormalizer_le_normalizer_centralizer U₁
  have hHN : H₀ ≤ N₀ := inf_le_right
  have hDN : D₀ ≤ N₀ := fun z hz => hHN hz.1
  have hCN : C₀ ≤ N₀ := Subgroup.centralizer_le_normalizer _
  have hYconj : ∀ m ∈ N₀, ∀ w ∈ D₀ ⊔ C₀, m * w * m⁻¹ ∈ D₀ ⊔ C₀ := by
    intro m hm w hw
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hDN.trans hNC)] at hw
    obtain ⟨z, hz, c, hc, rfl⟩ := hw
    have e : m * (z * c) * m⁻¹ = (m * z * m⁻¹) * (m * c * m⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (conj_mem_sup_of_mem_normalizer hS h46 hRp hRmax hA hm hz)
      (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hNC hm) c).mp hc))
  have hYN : N₀ ≤ Subgroup.normalizer ((D₀ ⊔ C₀ : Subgroup G) : Set G) := fun m hm =>
    Subgroup.mem_normalizer_iff.mpr fun w => ⟨hYconj m hm w, fun hw => by
      have := hYconj m⁻¹ (N₀.inv_mem hm) _ hw
      rwa [show m⁻¹ * (m * w * m⁻¹) * m⁻¹⁻¹ = w by group] at this⟩
  have hcC : ∀ m ∈ N₀, ∀ c ∈ C₀, ⁅m, c⁆ ∈ C₀ := fun m hm c hc => by
    rw [commutatorElement_def]
    exact C₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNC hm) c).mp hc) (C₀.inv_mem hc)
  have hKY : ∀ k ∈ H₀ ⊔ C₀, ∀ w ∈ D₀ ⊔ C₀, ⁅k, w⁆ ∈ C₀ := by
    intro k hk w hw
    have hwN : w ∈ N₀ := sup_le hDN hCN hw
    have h1 : ∀ h ∈ H₀, ⁅w, h⁆ ∈ C₀ := by
      intro h hh
      have hle : D₀ ⊔ C₀ ≤ GGL48.commModSubgroup C₀ h := sup_le
        (fun z hz => GGL48.mem_commModSubgroup.mpr ⟨hNC (hDN hz),
          commutatorElement_mem_centralizer_of_mem hS h46 hRp hRmax hA hcyc hcent hh hz⟩)
        (fun c hc => GGL48.mem_commModSubgroup.mpr ⟨hNC (hCN hc), hcC h (hHN hh) c hc⟩)
      rw [← commutatorElement_inv]
      exact C₀.inv_mem (GGL48.mem_commModSubgroup.mp (hle hw)).2
    have hle : H₀ ⊔ C₀ ≤ GGL48.commModSubgroup C₀ w := sup_le
      (fun h hh => GGL48.mem_commModSubgroup.mpr ⟨hNC (hHN hh), h1 h hh⟩)
      (fun c hc => GGL48.mem_commModSubgroup.mpr ⟨hNC (hCN hc), hcC w hwN c hc⟩)
    rw [← commutatorElement_inv]
    exact C₀.inv_mem (GGL48.mem_commModSubgroup.mp (hle hk)).2
  exact GGL48.forall_commutatorElement_mem_of_relIndex_prime hNC hYN (sup_le hHN hCN) hind hnorm
    hKY n hn v hv

theorem mem_centralizer_of_mem_sup_of_not_dvd {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Subgroup G} (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁)
    (hcop : ¬ p ∣ (ggL48H0 x U₁ ⊓ Subgroup.centralizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)).relIndex (ggL48H0 x U₁))
    {r : G} (hr : r ∈ ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)) {k : ℕ}
    (hrk : r ^ p ^ k = 1) :
    r ∈ Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hp, -, -, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  have hB₁iff := h46.2.2.2.1
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set H₀ := ggL48H0 x U₁ with hH₀
  set C₀ : Subgroup G := Subgroup.centralizer (U₁ : Set G) with hC₀
  set N₀ : Subgroup G := Subgroup.normalizer (U₁ : Set G) with hN₀
  set D₀ : Subgroup G := H₀ ⊓ Subgroup.centralizer (B₁ : Set G) with hD₀
  have hNC : N₀ ≤ Subgroup.normalizer (C₀ : Set G) := ggNormalizer_le_normalizer_centralizer U₁
  have hNB : N₀ ≤ Subgroup.normalizer (B₁ : Set G) := normalizer_le_normalizer_of_mem_iff hB₁iff
  have hHN : H₀ ≤ N₀ := inf_le_right
  have hC₀B : C₀ ≤ Subgroup.centralizer (B₁ : Set G) :=
    Subgroup.centralizer_le fun b hb => ((hB₁iff b).mp hb).1
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hHN.trans hNC)] at hr
  obtain ⟨h, hh, c, hc, rfl⟩ := hr
  have hcB : c ∈ Subgroup.centralizer (B₁ : Set G) := hC₀B hc
  have hstep : ∀ (q b' : G) (j : ℕ),
      q ^ (j + 1) * b' * (q ^ (j + 1))⁻¹ = q * (q ^ j * b' * (q ^ j)⁻¹) * q⁻¹ :=
    fun q b' j => by
      rw [pow_succ', mul_inv_rev]
      simp only [mul_assoc]
  have hiter : ∀ j : ℕ, ∀ b ∈ B₁, (h * c) ^ j * b * ((h * c) ^ j)⁻¹ = h ^ j * b * (h ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro b _; simp
    | succ j ih =>
      intro b hb
      have hjb : h ^ j * b * (h ^ j)⁻¹ ∈ B₁ :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hNB (hHN hh)) j) b).mp hb
      have hcy : c * (h ^ j * b * (h ^ j)⁻¹) * c⁻¹ = h ^ j * b * (h ^ j)⁻¹ := by
        have := Subgroup.mem_centralizer_iff.mp hcB _ hjb
        rw [← this]
        group
      calc (h * c) ^ (j + 1) * b * ((h * c) ^ (j + 1))⁻¹
          = (h * c) * ((h * c) ^ j * b * ((h * c) ^ j)⁻¹) * (h * c)⁻¹ := hstep _ _ _
        _ = (h * c) * (h ^ j * b * (h ^ j)⁻¹) * (h * c)⁻¹ := by rw [ih b hb]
        _ = h * (c * (h ^ j * b * (h ^ j)⁻¹) * c⁻¹) * h⁻¹ := by group
        _ = h * (h ^ j * b * (h ^ j)⁻¹) * h⁻¹ := by rw [hcy]
        _ = h ^ (j + 1) * b * (h ^ (j + 1))⁻¹ := (hstep _ _ _).symm
  have hhk : h ^ p ^ k ∈ Subgroup.centralizer (B₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := hiter (p ^ k) b hb
    rw [hrk, one_mul, inv_one, mul_one] at h1
    calc b * h ^ p ^ k = (h ^ p ^ k * b * (h ^ p ^ k)⁻¹) * h ^ p ^ k := by rw [← h1]
      _ = h ^ p ^ k * b := by group
  have hD₀n : (D₀.subgroupOf H₀).Normal := ⟨fun f hf a => by
    rw [Subgroup.mem_subgroupOf] at hf ⊢
    have ha : (a : G) ∈ Subgroup.normalizer (Subgroup.centralizer (B₁ : Set G) : Set G) :=
      ggNormalizer_le_normalizer_centralizer B₁ (hNB (hHN a.2))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨H₀.mul_mem (H₀.mul_mem a.2 hf.1) (H₀.inv_mem a.2),
      (Subgroup.mem_normalizer_iff.mp ha _).mp hf.2⟩⟩
  have h1 : (⟨h, hh⟩ : H₀) ^ (D₀.subgroupOf H₀).index ∈ D₀.subgroupOf H₀ :=
    Subgroup.pow_index_mem _ _
  have h2 : (⟨h, hh⟩ : H₀) ^ p ^ k ∈ D₀.subgroupOf H₀ := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨H₀.pow_mem hh _, by simpa using hhk⟩
  have hcop' : Nat.Coprime (D₀.subgroupOf H₀).index (p ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hcop).symm
  have h3 := mem_of_pow_mem_of_coprime hcop' h1 h2
  rw [Subgroup.mem_subgroupOf] at h3
  exact Subgroup.mul_mem _ h3.2 hcB

theorem not_mem_commutator_of_frobenius {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Subgroup G} (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hUR : U ≤ R) (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁)
    (hcyc : ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁)
    (hcent : x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁)
    (hind : (ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).relIndex
      (Subgroup.normalizer (U₁ : Set G)) = p)
    (hnorm : ¬ ((ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).subgroupOf
      (Subgroup.normalizer (U₁ : Set G))).Normal)
    (hcop : ¬ p ∣ (ggL48H0 x U₁ ⊓ Subgroup.centralizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)).relIndex (ggL48H0 x U₁)) :
    x ∉ ⁅Subgroup.normalizer (U₁ : Set G), Subgroup.normalizer (U₁ : Set G)⁆ := by
  obtain ⟨hp, hxp, -, ⟨e, he⟩, hpel⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  have hB₁iff := h46.2.2.2.1
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set H₀ := ggL48H0 x U₁ with hH₀
  set C₀ : Subgroup G := Subgroup.centralizer (U₁ : Set G) with hC₀
  set N₀ : Subgroup G := Subgroup.normalizer (U₁ : Set G) with hN₀
  set D₀ : Subgroup G := H₀ ⊓ Subgroup.centralizer (B₁ : Set G) with hD₀
  have hNC : N₀ ≤ Subgroup.normalizer (C₀ : Set G) := ggNormalizer_le_normalizer_centralizer U₁
  have hHN : H₀ ≤ N₀ := inf_le_right
  have hC₀B : C₀ ≤ Subgroup.centralizer (B₁ : Set G) :=
    Subgroup.centralizer_le fun b hb => ((hB₁iff b).mp hb).1
  have hRN : R ≤ N₀ := Subgroup.le_normalizer.trans (normalizer_le_normalizer_of_forall_eq hA)
  have hU := hS.2.2.2.2.2.2.1
  have hUN : U ≤ N₀ :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_of_forall_eq h46.2.2.1)
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hS.1.1.1.2.2.2.2.2.2.1.2.1
  have hxR : x ∈ R := hUR (hU.2.2.2 hxBs)
  have hxU₁ : x ∉ U₁ := fun hx => hS.2.2.1.1 ((hB₁iff x).mpr ⟨hx, hxp⟩)
  have hRC : R ⊓ Subgroup.centralizer (B₁ : Set G) = U :=
    hU.2.2.1 _ inf_le_right (hRp.to_le inf_le_left) (le_inf hUR hU.1)
  have hpow : ∀ r ∈ R, ∃ k : ℕ, r ^ p ^ k = 1 := fun r hr => by
    obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hR₁U : (H₀ ⊔ C₀) ⊓ R ≤ U := by
    intro r hr
    obtain ⟨k, hk⟩ := hpow r hr.2
    rw [← hRC]
    exact ⟨hr.2, mem_centralizer_of_mem_sup_of_not_dvd hS h46 hRp hRmax hA hcop hr.1 hk⟩
  have hR₁ind : ((H₀ ⊔ C₀) ⊓ R).relIndex R ≤ p := by
    rw [Subgroup.inf_relIndex_right, ← hind]
    exact Subgroup.relIndex_le_of_le_right hRN (by rw [hind]; exact hp.ne_zero)
  obtain ⟨g, hgU, hUg⟩ := hcyc
  have hgN : g ∈ N₀ := hUN hgU
  have hUle : U ≤ Subgroup.zpowers 1 ⊔ Subgroup.zpowers g ⊔ U₁ :=
    hUg.trans (sup_le_sup_right le_sup_right _)
  have hkey : ∃ r ∈ N₀, ⁅r, g⁆ ∈ U₁ ∧ R ≤ Subgroup.zpowers r ⊔ Subgroup.zpowers g ⊔ U₁ := by
    have h1 : ⁅(1 : G), g⁆ ∈ U₁ := by
      rw [commutatorElement_one_left]
      exact U₁.one_mem
    by_cases hUK : U ≤ H₀ ⊔ C₀
    · by_cases hRK : R ≤ H₀ ⊔ C₀
      · have hRU : R ≤ U := fun r hr => hR₁U ⟨hRK hr, hr⟩
        exact ⟨1, N₀.one_mem, h1, hRU.trans hUle⟩
      · obtain ⟨r₀, hr₀R, hr₀K⟩ := Set.not_subset.mp hRK
        have hr₀N : r₀ ∈ N₀ := hRN hr₀R
        refine ⟨r₀, hr₀N, ?_, ?_⟩
        ·
          have hgY : g ∈ D₀ ⊔ C₀ := by
            have hg' := hUK hgU
            rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
              (hHN.trans hNC)] at hg'
            obtain ⟨h, hh, c, hc, hhc⟩ := hg'
            have hhB : h ∈ Subgroup.centralizer (B₁ : Set G) := by
              have e' : h = g * c⁻¹ := by rw [← hhc]; group
              rw [e']
              exact Subgroup.mul_mem _ (hU.1 hgU) (Subgroup.inv_mem _ (hC₀B hc))
            rw [← hhc]
            exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hh, hhB⟩) (Subgroup.mem_sup_right hc)
          have hc := commutatorElement_mem_centralizer_of_frobenius hS h46 hRp hRmax hA
            ⟨g, hgU, hUg⟩ hcent hind hnorm hr₀N hgY
          have hcR : ⁅r₀, g⁆ ∈ R := by
            rw [commutatorElement_def]
            exact R.mul_mem (R.mul_mem (R.mul_mem hr₀R (hUR hgU)) (R.inv_mem hr₀R))
              (R.inv_mem (hUR hgU))
          obtain ⟨k, hk⟩ := hpow _ hcR
          exact hpel _ hc k hk
        · have hM : R ≤ Subgroup.zpowers r₀ ⊔ (H₀ ⊔ C₀) ⊓ R :=
            GGL48.le_of_relIndex_le_prime le_sup_right
              (sup_le (Subgroup.zpowers_le.mpr hr₀R) inf_le_right) hRp hR₁ind
              (fun hle => hr₀K (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers r₀))).1)
          exact hM.trans (sup_le (le_sup_left.trans le_sup_left)
            (hR₁U.trans (hUg.trans (sup_le_sup_right le_sup_right _))))
    · have hRU : R ≤ U := GGL48.le_of_relIndex_le_prime hR₁U hUR hRp hR₁ind
        (fun hle => hUK (hle.trans inf_le_left))
      exact ⟨1, N₀.one_mem, h1, hRU.trans hUle⟩
  obtain ⟨r, hrN, hrg, hRle⟩ := hkey
  have hRR : ⁅R, R⁆ ≤ U₁ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact GGL48.commutatorElement_mem_of_mem_sup_sup hrN hgN hrg (hRle ha) (hRle hb)
  have hRC₀ : R ⊓ C₀ ≤ U₁ := fun c hc => by
    obtain ⟨k, hk⟩ := hpow c hc.1
    exact hpel c hc.2 k hk
  have hindR : ¬ p ∣ (R ⊔ C₀).relIndex N₀ := by
    intro hdvd
    let S : Sylow p G := ⟨R, hRp, fun {Q} hQ hRQ => hRmax Q hQ hRQ⟩
    have h1 : (R ⊔ C₀).relIndex N₀ ∣ R.relIndex N₀ := Subgroup.relIndex_dvd_of_le_left N₀ le_sup_left
    have h2 : R.relIndex N₀ * N₀.index = R.index := Subgroup.relIndex_mul_index hRN
    have h3 : p ∣ R.index := h2 ▸ Dvd.dvd.mul_right (hdvd.trans h1) _
    exact S.not_dvd_index h3
  exact GGL48.not_mem_commutator_of_not_dvd_relIndex hRN (Subgroup.centralizer_le_normalizer _)
    hNC hxR hxp (fun n hn => GGL48.conj_mul_inv_mem_centralizer he hn) hindR
    (fun hx => hxU₁ ((sup_le hRR hRC₀) hx))

end Config

end CFSG.StandardType

end
