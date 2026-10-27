module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588E6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.ABGLocalTools
open CFSG.GorensteinWalter (IsComponentOf)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

noncomputable abbrev Xs : Subgroup (MulAut m.Lbar) := m.sig.range

noncomputable abbrev sigX : ↥m.LA →* ↥m.Xs := m.sig.rangeRestrict

@[expose] noncomputable def star (Y : Subgroup G) : Subgroup ↥m.Xs :=
  (Y.subgroupOf m.LA).map m.sigX

theorem sigX_surjective : Function.Surjective m.sigX := m.sig.rangeRestrict_surjective

theorem sigX_mem_star {Y : Subgroup G} {y : ↥m.LA} (hy : (y : G) ∈ Y) : m.sigX y ∈ m.star Y :=
  ⟨y, hy, rfl⟩

theorem star_mono {Y Y' : Subgroup G} (h : Y ≤ Y') : m.star Y ≤ m.star Y' :=
  Subgroup.map_mono fun _ hx => h hx

theorem sigX_eq_one_iff {y : ↥m.LA} : m.sigX y = 1 ↔ m.sig y = 1 := Subtype.ext_iff

theorem LA_ne_top : m.LA ≠ ⊤ := by
  intro h
  apply m.H_ne_top_n588
  rw [eq_top_iff, ← h]
  exact m.LA_le_H

theorem isKGroup_Xs : CFSG.Open.IsKGroup ↥m.Xs :=
  (Dat.standing.kProper.isKGroup m.LA m.LA_ne_top).of_surjective m.sigX m.sigX_surjective

theorem mem_Opp_Xs_of_pow {x : ↥m.Xs} {k : ℕ} (hx : x ^ (m.r ^ k) = 1) :
    x ∈ UC22.Opp m.r (⊤ : Subgroup ↥m.Xs) := by
  apply Subgroup.subset_closure
  refine ⟨mem_top x, ?_⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow m.hr).1 (orderOf_dvd_of_pow_eq_one hx)
  exact ⟨j, hj⟩

theorem Opp_Xs : UC22.Opp m.r (⊤ : Subgroup ↥m.Xs) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := m.sigX_surjective x
  obtain ⟨ℓ, hℓ, a, ha, hy⟩ := m.exists_mul_of_mem_LA y.2
  have hya : y = Subgroup.inclusion m.L_le_LA ⟨ℓ, hℓ⟩ * ⟨a, m.A_le_LA ha⟩ := Subtype.ext hy.symm
  rw [hya, map_mul]
  refine mul_mem ?_ (m.mem_Opp_Xs_of_pow (k := 1) ?_)
  · set f : ↥m.L →* ↥m.Xs := m.sigX.comp (Subgroup.inclusion m.L_le_LA) with hf
    have hT := m.gen_L ((UC22.Opp m.r (⊤ : Subgroup ↥m.Xs)).comap f) fun ℓ ⟨k, hk⟩ => by
      refine m.mem_Opp_Xs_of_pow (k := k) ?_
      rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
    have h1 : (⟨ℓ, hℓ⟩ : ↥m.L) ∈ (UC22.Opp m.r (⊤ : Subgroup ↥m.Xs)).comap f := hT ▸ mem_top _
    exact h1
  · rw [pow_one, ← map_pow]
    have : (⟨a, m.A_le_LA ha⟩ : ↥m.LA) ^ m.r = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact m.isElemAbelian_A.2 a ha)
    rw [this, map_one]

theorem conj_mem_Xs (u : m.Lbar) : MulAut.conj u ∈ m.Xs := by
  induction u using QuotientGroup.induction_on with | H ℓ =>
  exact ⟨Subgroup.inclusion m.L_le_LA ℓ, m.sig_L ℓ⟩

@[expose] noncomputable def innX : m.Lbar →* ↥m.Xs :=
  (MulAut.conj : m.Lbar →* MulAut m.Lbar).codRestrict m.Xs m.conj_mem_Xs

theorem sigX_L (ℓ : ↥m.L) : m.sigX (Subgroup.inclusion m.L_le_LA ℓ) = m.innX (ℓ : m.Lbar) :=
  Subtype.ext (m.sig_L ℓ)

theorem mul_innX_mul_inv (α : ↥m.Xs) (u : m.Lbar) :
    α * m.innX u * α⁻¹ = m.innX ((α : MulAut m.Lbar) u) := by
  apply Subtype.ext
  ext v
  simp [innX, MulAut.conj_apply]

theorem innX_range_normal : m.innX.range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨u, rfl⟩ := hn
  rw [m.mul_innX_mul_inv]
  exact ⟨_, rfl⟩

variable (hKM : UCK.KMult) (hK3 : UCK.KMult3) (h69 : R6_9 Dat)
include hKM hK3 h69

theorem innX_injective (hSch : UCK.KSch) : Function.Injective m.innX := fun _ _ h =>
  m.conj_injective_Lbar hKM hK3 h69 hSch (congrArg Subtype.val h)

theorem pPrimeCore_Xs (hSch : UCK.KSch) : CFSG.pPrimeCore m.r ↥m.Xs = ⊥ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  haveI := m.isSimpleGroup_Lbar_of_inputs hKM hK3 h69 hSch
  set N := CFSG.pPrimeCore m.r ↥m.Xs with hN
  have hinj := m.innX_injective hKM hK3 h69 hSch
  set U : Subgroup m.Lbar := N.comap m.innX with hU
  have hUbot : U = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U with h | h
    · exact h
    · exfalso
      have hle : U.map m.innX ≤ N := Subgroup.map_comap_le _ _
      have h1 := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective hinj, h, Subgroup.card_top] at h1
      have h2 := (m.r_dvd_card_Lbar hKM hK3 h69 hSch).trans h1
      exact (Nat.Prime.coprime_iff_not_dvd m.hr).1 CFSG.pPrimeCore_coprime_card h2
  rw [eq_bot_iff]
  intro α hα
  rw [mem_bot]
  apply Subtype.ext
  ext u
  have h1 : m.innX (((α : MulAut m.Lbar) u) * u⁻¹) ∈ N := by
    rw [map_mul, map_inv, ← m.mul_innX_mul_inv]
    have h2 : m.innX u * α⁻¹ * (m.innX u)⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem _ (N.inv_mem hα) _
    have : α * m.innX u * α⁻¹ * (m.innX u)⁻¹ = α * (m.innX u * α⁻¹ * (m.innX u)⁻¹) := by
      group
    rw [this]
    exact N.mul_mem hα h2
  have h3 : ((α : MulAut m.Lbar) u) * u⁻¹ ∈ U := h1
  rw [hUbot, mem_bot, mul_inv_eq_one] at h3
  exact h3

omit hKM hK3 in
theorem R_le_normalizer_LA : m.R ≤ normalizer ((m.LA : Subgroup G) : Set G) := by
  have h16 := m.hZ.sixteen h69
  have hRA : m.R ≤ normalizer ((m.A : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [mem_centralizer_iff]
    intro a ha
    exact h16.1 a ha x hx
  exact (le_inf ((m.R_le_H h69).trans m.H_le_normalizer_L) hRA).trans
    (Subgroup.inf_normalizer_le_normalizer_sup _ _)

omit hKM hK3 in
theorem R_inf_LA_sylow : IsSylowOf m.r (m.R ⊓ m.LA) m.LA := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hLR : m.L ⊔ m.R ≤ m.H := sup_le m.L_le_H (m.R_le_H h69)
  have hS : IsSylowOf m.r m.R (m.L ⊔ m.R) := (m.R_sylow_H h69).of_le le_sup_right hLR
  have hle : m.LA ≤ m.L ⊔ m.R := sup_le le_sup_left (m.A_le_R.trans le_sup_right)
  have hn : m.L ⊔ m.R ≤ normalizer ((m.LA : Subgroup G) : Set G) :=
    sup_le (m.L_le_LA.trans le_normalizer) (m.R_le_normalizer_LA h69)
  exact hS.inf_of_le_normalizer hle hn

omit hKM hK3 in
theorem star_R_sylow : IsSylowOf m.r (m.star m.R) ⊤ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have h : IsSylowOf m.r ((m.R.subgroupOf m.LA).map m.LA.subtype)
      ((⊤ : Subgroup ↥m.LA).map m.LA.subtype) := by
    rw [Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact m.R_inf_LA_sylow h69
  rw [isSylowOf_map_subtype_iff, isSylowOf_iff] at h
  obtain ⟨-, hP, hnd⟩ := h
  rw [isSylowOf_iff]
  refine ⟨le_top, hP.map _, ?_⟩
  rw [Subgroup.relIndex_top_right]
  rw [Subgroup.relIndex_top_right] at hnd
  exact fun hd => hnd (hd.trans (Subgroup.index_map_dvd _ m.sigX_surjective))

omit hKM hK3 h69 in
theorem star_A_le_star_R : m.star m.A ≤ m.star m.R := m.star_mono m.A_le_R

omit hKM hK3 h69 in
theorem isElemAbelian_star_A : CFSG.Open.IsElemAbelian m.r (m.star m.A) := by
  have hel := m.isElemAbelian_A
  have h : CFSG.Open.IsElemAbelian m.r (m.A.subgroupOf m.LA) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have h1 := hel.1.is_comm.comm (⟨_, a.2⟩ : ↥m.A) ⟨_, b.2⟩
      have h2 : ((a : ↥m.LA) : G) * ((b : ↥m.LA) : G) = ((b : ↥m.LA) : G) * ((a : ↥m.LA) : G) :=
        congrArg Subtype.val h1
      exact h2
    · rw [Subgroup.coe_pow]
      exact hel.2 _ hx
  exact h.map m.sigX

theorem mem_Z_of_sig_eq_one (hSch : UCK.KSch) {y : ↥m.LA} (hyA : (y : G) ∈ m.A)
    (hy : m.sig y = 1) : (y : G) ∈ m.Z :=
  m.mem_Z_of_centralizes_Lbar hKM hK3 h69 hSch hyA fun _ hℓ =>
    m.comm_mem_rCore_of_sig_eq_one hy hℓ

theorem card_star_A (hSch : UCK.KSch) : Nat.card (m.star m.A) = m.r ^ 2 := by
  set f : ↥m.A →* ↥m.Xs := m.sigX.comp (Subgroup.inclusion m.A_le_LA) with hf
  have hrange : f.range = m.star m.A := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact m.sigX_mem_star a.2
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hker : f.ker = m.Z.subgroupOf m.A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact m.mem_Z_of_sig_eq_one hKM hK3 h69 hSch a.2 (m.sigX_eq_one_iff.1 h)
    · intro h
      exact m.sigX_eq_one_iff.2 (m.sig_Z h)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.Z_le_A).toEquiv, m.card_A, m.card_Z] at h1
  have h2 : m.r ^ 3 = m.r ^ 2 * m.r := by ring
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right m.hr.pos h1).symm

omit hKM hK3 in
theorem star_A_comm {b x : ↥m.Xs} (hb : b ∈ m.star m.A) (hx : x ∈ m.star m.R) :
    b * x = x * b := by
  obtain ⟨a, ha, rfl⟩ := hb
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext ((m.hZ.sixteen h69).1 _ ha _ hy)

omit hKM hK3 in
theorem Z_inf_L (hSch : UCK.KSch) (hKM : UCK.KMult) (hK3 : UCK.KMult3) : m.Z ⊓ m.L = ⊥ :=
  inf_eq_bot_of_not_le_of_card_prime m.hr m.card_Z (m.not_Z_le_L_of_inputs hKM hK3 h69 hSch)

theorem mem_star_A_of_pow (hSch : UCK.KSch) {x : ↥m.Xs} (hx : x ∈ m.star m.R)
    (hxr : x ^ m.r = 1) : x ∈ m.star m.A := by
  have h16 := m.hZ.sixteen h69
  obtain ⟨y, hyR, rfl⟩ := hx
  have hyR' : (y : G) ∈ m.R := hyR
  obtain ⟨ℓ, hℓ, a, ha, hy⟩ := m.exists_mul_of_mem_LA y.2
  have hcomm : Commute ℓ a := by
    have hℓR : ℓ ∈ m.R := by
      have : ℓ = (y : G) * a⁻¹ := by rw [← hy]; group
      rw [this]
      exact m.R.mul_mem hyR' (m.R.inv_mem (m.A_le_R ha))
    exact (h16.1 a ha ℓ hℓR).symm
  have hpow : (y : G) ^ m.r = ℓ ^ m.r := by
    rw [← hy, hcomm.mul_pow, m.isElemAbelian_A.2 a ha, mul_one]
  have hk : m.sig (y ^ m.r) = 1 := m.sigX_eq_one_iff.1 (by rw [map_pow]; exact hxr)
  have h1 := m.mem_rCore_sup_Z_of_sig_eq_one hKM hK3 h69 hSch hk
  rw [Subgroup.coe_pow] at h1
  have hZn : m.Z ≤ normalizer ((N588.rCore m.r m.L : Subgroup G) : Set G) :=
    (m.Z_le_A.trans m.A_le_H).trans m.H_le_normalizer_rCoreL
  have h2 : (y : G) ^ m.r ∈ ((N588.rCore m.r m.L ⊔ m.Z : Subgroup G) : Set G) := h1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZn] at h2
  obtain ⟨o, ho, z, hz, hoz⟩ := h2
  have hoz' : o * z = (y : G) ^ m.r := hoz
  have hoR : o ∈ m.R := by
    have : o = (y : G) ^ m.r * z⁻¹ := by rw [← hoz']; group
    rw [this]
    exact m.R.mul_mem (pow_mem hyR' _) (m.R.inv_mem (m.Z_le_A.trans m.A_le_R hz))
  have ho1 := m.eq_one_of_mem_rCore_of_mem_R h69 ho hoR
  rw [ho1, one_mul] at hoz'
  have hyr : (y : G) ^ m.r = 1 := by
    have hmem : (y : G) ^ m.r ∈ m.Z ⊓ m.L := ⟨hoz' ▸ hz, hpow ▸ pow_mem hℓ _⟩
    rw [m.Z_inf_L h69 hSch hKM hK3, mem_bot] at hmem
    exact hmem
  exact m.sigX_mem_star (h16.2 _ hyR' hyr)

omit hKM hK3 h69 in
theorem star_R_le_star_M : m.star m.R ≤ m.star m.M := m.star_mono m.R_le_M

theorem star_M_ne_top (hSch : UCK.KSch) : m.star m.M ≠ ⊤ := by
  intro htop
  apply m.not_L_le_M_of_inputs hKM hK3 h69 hSch
  intro ℓ hℓ
  have h1 : m.sigX (Subgroup.inclusion m.L_le_LA ⟨ℓ, hℓ⟩) ∈ m.star m.M := htop ▸ mem_top _
  obtain ⟨y, hyM, hy⟩ := h1
  have h2 : m.sig (y⁻¹ * Subgroup.inclusion m.L_le_LA ⟨ℓ, hℓ⟩) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact congrArg Subtype.val hy
  have h3 := m.mem_rCore_sup_Z_of_sig_eq_one hKM hK3 h69 hSch h2
  have hOZ : N588.rCore m.r m.L ⊔ m.Z ≤ m.M :=
    sup_le m.rCoreL_le_M (m.Z_le_A.trans (m.A_le_R.trans m.R_le_M))
  have h4 : ((y : G))⁻¹ * ℓ ∈ m.M := hOZ h3
  have : ℓ = (y : G) * ((y : G)⁻¹ * ℓ) := by group
  rw [this]
  exact m.M.mul_mem hyM h4

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
