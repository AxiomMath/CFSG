module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588E5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.ABGLocalTools
open CFSG.GorensteinWalter (IsComponentOf)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

@[expose] noncomputable def LA : Subgroup G := m.L ⊔ m.A

theorem A_le_normalizer_L : m.A ≤ normalizer (m.L : Set G) :=
  m.A_le_H.trans m.H_le_normalizer_L

theorem LA_le_normalizer_L : m.LA ≤ normalizer (m.L : Set G) :=
  sup_le le_normalizer m.A_le_normalizer_L

theorem LA_le_H : m.LA ≤ m.H := sup_le m.L_le_H m.A_le_H

theorem L_le_LA : m.L ≤ m.LA := le_sup_left

theorem A_le_LA : m.A ≤ m.LA := le_sup_right

theorem exists_mul_of_mem_LA {y : G} (hy : y ∈ m.LA) : ∃ ℓ ∈ m.L, ∃ a ∈ m.A, ℓ * a = y := by
  have h : y ∈ ((m.L ⊔ m.A : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left m.L m.A m.A_le_normalizer_L] at h
  obtain ⟨ℓ, hℓ, a, ha, rfl⟩ := h
  exact ⟨ℓ, hℓ, a, ha, rfl⟩

@[expose] noncomputable def sig : ↥m.LA →* MulAut m.Lbar :=
  (N588.autQuot (CFSG.pPrimeCore m.r ↥m.L)).comp
    (m.L.normalizerMonoidHom.comp (Subgroup.inclusion m.LA_le_normalizer_L))

theorem conj_mem_L (y : ↥m.LA) (ℓ : ↥m.L) : (y : G) * ℓ * (y : G)⁻¹ ∈ m.L :=
  (mem_normalizer_iff.1 (m.LA_le_normalizer_L y.2) ℓ).1 ℓ.2

theorem sig_mk (y : ↥m.LA) (ℓ : ↥m.L) :
    m.sig y (ℓ : m.Lbar) = ((⟨(y : G) * ℓ * (y : G)⁻¹, m.conj_mem_L y ℓ⟩ : ↥m.L) : m.Lbar) := by
  show ((m.L.normalizerMonoidHom (Subgroup.inclusion m.LA_le_normalizer_L y) ℓ : ↥m.L) :
    m.Lbar) = _
  congr 1

theorem sig_L (ℓ : ↥m.L) :
    m.sig (Subgroup.inclusion m.L_le_LA ℓ) = MulAut.conj (ℓ : m.Lbar) := by
  ext x
  induction x using QuotientGroup.induction_on with | H x =>
  rw [m.sig_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1

theorem comm_mem_rCore_of_sig_eq_one {y : ↥m.LA} (hy : m.sig y = 1) {ℓ : G} (hℓ : ℓ ∈ m.L) :
    (y : G) * ℓ * (y : G)⁻¹ * ℓ⁻¹ ∈ N588.rCore m.r m.L := by
  have h1 := congrArg (fun f : MulAut m.Lbar => f ((⟨ℓ, hℓ⟩ : ↥m.L) : m.Lbar)) hy
  simp only [MulAut.one_apply] at h1
  rw [m.sig_mk, QuotientGroup.eq] at h1
  have h2 : ((y : G) * ℓ * (y : G)⁻¹)⁻¹ * ℓ ∈ N588.rCore m.r m.L := ⟨_, h1, rfl⟩
  have h3 := (mem_normalizer_iff.1 (N588.le_normalizer_rCore m.r m.L hℓ) _).1 h2
  have h4 := (N588.rCore m.r m.L).inv_mem h3
  have : (ℓ * ((((y : G) * ℓ * (y : G)⁻¹)⁻¹ * ℓ)) * ℓ⁻¹)⁻¹ =
      (y : G) * ℓ * (y : G)⁻¹ * ℓ⁻¹ := by group
  rwa [this] at h4

theorem mem_pPrimeCore_L_iff {w : ↥m.L} :
    w ∈ CFSG.pPrimeCore m.r ↥m.L ↔ (w : G) ∈ N588.rCore m.r m.L :=
  (Subgroup.mem_map_iff_mem m.L.subtype_injective).symm

theorem sig_eq_one_of_comm_mem_rCore {y : ↥m.LA}
    (h : ∀ ℓ ∈ m.L, (y : G) * ℓ * (y : G)⁻¹ * ℓ⁻¹ ∈ N588.rCore m.r m.L) : m.sig y = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with | H x =>
  rw [m.sig_mk, MulAut.one_apply, QuotientGroup.eq, m.mem_pPrimeCore_L_iff]
  have h1 := (mem_normalizer_iff.1 (N588.le_normalizer_rCore m.r m.L (m.L.inv_mem x.2)) _).1
    ((N588.rCore m.r m.L).inv_mem (h x x.2))
  have he : (x : G)⁻¹ * ((y : G) * x * (y : G)⁻¹ * (x : G)⁻¹)⁻¹ * (x : G)⁻¹⁻¹ =
      (((⟨(y : G) * x * (y : G)⁻¹, m.conj_mem_L y x⟩ : ↥m.L)⁻¹ * x : ↥m.L) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [← he]
  exact h1

theorem sig_Z {z : G} (hz : z ∈ m.Z) : m.sig ⟨z, m.A_le_LA (m.Z_le_A hz)⟩ = 1 := by
  refine m.sig_eq_one_of_comm_mem_rCore fun ℓ hℓ => ?_
  have hc : z * ℓ = ℓ * z := mem_centralizer_iff.1 (m.L_le_H hℓ) z hz
  have : z * ℓ * z⁻¹ * ℓ⁻¹ = 1 := by
    rw [hc]
    group
  show z * ℓ * z⁻¹ * ℓ⁻¹ ∈ _
  rw [this]
  exact one_mem _

theorem sig_rCore {o : G} (ho : o ∈ N588.rCore m.r m.L) :
    m.sig ⟨o, m.L_le_LA (N588.rCore_le _ _ ho)⟩ = 1 := by
  obtain ⟨o', ho', rfl⟩ := ho
  have h := m.sig_L o'
  have h1 : ((o' : ↥m.L) : m.Lbar) = 1 := (QuotientGroup.eq_one_iff _).2 ho'
  rw [h1, map_one] at h
  exact h

variable (hKM : UCK.KMult) (hK3 : UCK.KMult3) (h69 : R6_9 Dat)
include hKM hK3 h69

theorem center_Lbar (hSch : UCK.KSch) : center m.Lbar = ⊥ := by
  obtain ⟨K, hK⟩ := m.exists_component h69
  obtain ⟨e⟩ := m.nonempty_mulEquiv_Lbar hKM hK3 h69 hSch hK
  have hc := m.center_component_eq_bot hKM hK3 h69 hK
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ center ↥K := Subgroup.mem_center_iff.2 fun k => by
    obtain ⟨y, rfl⟩ := e.surjective k
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx) y]
  rw [hc, mem_bot] at h1
  exact (mem_bot).2 (e.injective (h1.trans (map_one e).symm))

theorem r_dvd_card_Lbar (hSch : UCK.KSch) : m.r ∣ Nat.card m.Lbar := by
  obtain ⟨K, hK⟩ := m.exists_component h69
  obtain ⟨e⟩ := m.nonempty_mulEquiv_Lbar hKM hK3 h69 hSch hK
  rw [Nat.card_congr e.toEquiv]
  exact m.r_dvd_card_component hK

theorem conj_injective_Lbar (hSch : UCK.KSch) :
    Function.Injective (MulAut.conj : m.Lbar →* MulAut m.Lbar) := by
  rw [← MonoidHom.ker_eq_bot_iff, ← m.center_Lbar hKM hK3 h69 hSch]
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hs t
    have h1 := congrArg (fun e : MulAut m.Lbar => e t) hs
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc t * s = (s * t * s⁻¹) * s := by rw [h1]
      _ = s * t := by group
  · intro hs
    ext t
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← hs t]
    group

@[expose] noncomputable def RbarL : Subgroup m.Lbar :=
  ((m.R ⊓ m.L).subgroupOf m.L).map (QuotientGroup.mk' (CFSG.pPrimeCore m.r ↥m.L))

omit hKM hK3 in
theorem R_inf_L_sylow : IsSylowOf m.r (m.R ⊓ m.L) m.L := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  exact (m.R_sylow_H h69).inf_of_le_normalizer m.L_le_H m.H_le_normalizer_L

omit hKM hK3 in
theorem RbarL_sylow : IsSylowOf m.r m.RbarL ⊤ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have h := m.R_inf_L_sylow h69
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨-, hP, hnd⟩ := h
  refine ⟨le_top, (hP.comap_subtype (K := m.L)).map _, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact fun hd => hnd (hd.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))

omit hKM hK3 in
theorem eq_one_of_mem_rCore_of_mem_R {x : G} (hxO : x ∈ N588.rCore m.r m.L) (hxR : x ∈ m.R) :
    x = 1 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).1 (m.R_sylow_H h69).isPGroup ⟨x, hxR⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : orderOf x ∣ Nat.card (N588.rCore m.r m.L) := by
    have := Subgroup.orderOf_dvd_natCard (N588.rCore m.r m.L) hxO
    exact this
  rw [hk] at h1
  have hcop : Nat.Coprime (m.r ^ k) (Nat.card (N588.rCore m.r m.L)) :=
    Nat.Coprime.pow_left k (N588.coprime_card_rCore m.r m.L)
  rw [Nat.Coprime.eq_one_of_dvd hcop h1] at hk
  exact orderOf_eq_one_iff.1 hk

theorem mem_rCore_sup_Z_of_sig_eq_one (hSch : UCK.KSch) {y : ↥m.LA} (hy : m.sig y = 1) :
    (y : G) ∈ N588.rCore m.r m.L ⊔ m.Z := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have h16 := m.hZ.sixteen h69
  obtain ⟨ℓ, hℓ, a, ha, hy'⟩ := m.exists_mul_of_mem_LA y.2
  set ℓ' : ↥m.L := ⟨ℓ, hℓ⟩ with hℓ'
  set a' : ↥m.LA := ⟨a, m.A_le_LA ha⟩ with ha'
  have hya : y = Subgroup.inclusion m.L_le_LA ℓ' * a' := Subtype.ext hy'.symm
  set u : m.Lbar := ((ℓ' : m.Lbar))⁻¹ with hu
  have hsa : m.sig a' = MulAut.conj u := by
    have h1 : m.sig (Subgroup.inclusion m.L_le_LA ℓ') * m.sig a' = 1 := by
      rw [← map_mul, ← hya, hy]
    rw [hu, map_inv, ← m.sig_L]
    exact eq_inv_of_mul_eq_one_right h1
  have har : a ^ m.r = 1 := m.isElemAbelian_A.2 a ha
  have hur : u ^ m.r = 1 := by
    apply m.conj_injective_Lbar hKM hK3 h69 hSch
    rw [map_pow, ← hsa, ← map_pow, map_one]
    have : a' ^ m.r = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact har)
    rw [this, map_one]
  have hcent : ∀ v ∈ m.RbarL, u * v = v * u := by
    rintro _ ⟨x, hx, rfl⟩
    have hxR : (x : G) ∈ m.R := hx.1
    have hax : a * x = x * a := h16.1 a ha x hxR
    have h1 : m.sig a' (x : m.Lbar) = (x : m.Lbar) := by
      rw [m.sig_mk]
      congr 1
      apply Subtype.ext
      show a * x * a⁻¹ = x
      rw [hax, mul_inv_cancel_right]
    rw [hsa, MulAut.conj_apply] at h1
    show u * (x : m.Lbar) = (x : m.Lbar) * u
    calc u * (x : m.Lbar) = (u * (x : m.Lbar) * u⁻¹) * u := by group
      _ = (x : m.Lbar) * u := by rw [h1]
  have huR : u ∈ m.RbarL := by
    have hS := m.RbarL_sylow h69
    have hup : IsPGroup m.r (zpowers u) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow m.hr).1
        (orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact hur : u ^ (m.r ^ 1) = 1))
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hn : m.RbarL ≤ normalizer ((zpowers u : Subgroup m.Lbar) : Set m.Lbar) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro v hv
      rw [mem_centralizer_iff]
      intro w hw
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
      exact (Commute.zpow_left (hcent v hv) j).eq
    have hP := hup.to_sup_of_normal_left' hS.isPGroup hn
    have heq := hS.eq_of_le le_sup_right le_top hP
    rw [← heq]
    exact mem_sup_left (mem_zpowers u)
  obtain ⟨x, hx, hxu⟩ := huR
  have hxR : (x : G) ∈ m.R := hx.1
  have hxr : (x : G) ^ m.r = 1 := by
    have h1 : ((x ^ m.r : ↥m.L) : m.Lbar) = 1 := by
      rw [QuotientGroup.mk_pow]
      change (QuotientGroup.mk' _ x) ^ m.r = 1
      rw [hxu, hur]
    have h2 : (x ^ m.r : ↥m.L) ∈ CFSG.pPrimeCore m.r ↥m.L := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : (x : G) ^ m.r ∈ N588.rCore m.r m.L := ⟨_, h2, by simp⟩
    exact m.eq_one_of_mem_rCore_of_mem_R h69 h3 (pow_mem hxR _)
  have hxA : (x : G) ∈ m.A := h16.2 x hxR hxr
  have ho : ℓ * x ∈ N588.rCore m.r m.L := by
    have h1 : ((ℓ' * x : ↥m.L) : m.Lbar) = 1 := by
      rw [QuotientGroup.mk_mul]
      change (ℓ' : m.Lbar) * QuotientGroup.mk' _ x = 1
      rw [hxu, hu, mul_inv_cancel]
    exact ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  have hbA : (x : G)⁻¹ * a ∈ m.A := m.A.mul_mem (m.A.inv_mem hxA) ha
  have hb : m.sig ⟨(x : G)⁻¹ * a, m.A_le_LA hbA⟩ = 1 := by
    have he : (⟨(x : G)⁻¹ * a, m.A_le_LA hbA⟩ : ↥m.LA) =
        (⟨ℓ * x, m.L_le_LA (N588.rCore_le _ _ ho)⟩ : ↥m.LA)⁻¹ * y := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hy']
      group
    rw [he, map_mul, map_inv, m.sig_rCore ho, hy, inv_one, mul_one]
  have hbZ : (x : G)⁻¹ * a ∈ m.Z := m.mem_Z_of_centralizes_Lbar hKM hK3 h69 hSch hbA
    fun ℓ hℓ => m.comm_mem_rCore_of_sig_eq_one hb hℓ
  have hyx : (y : G) = (ℓ * x) * ((x : G)⁻¹ * a) := by
    rw [← hy']
    group
  rw [hyx]
  exact mul_mem_sup ho hbZ

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
