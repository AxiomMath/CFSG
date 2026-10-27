module

public import CFSG.Quasithin.Background.SimsE2DihMod
public import CFSG.Quasithin.Background.SimsE213Four

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace Dih

variable {Γ : Type*} [Group Γ]

theorem map_normalizerMonoidHom_subgroupOf {P Z : Subgroup Γ}
    (x : Subgroup.normalizer (P : Set Γ)) (hx : (x : Γ) ∈ Subgroup.normalizer (Z : Set Γ)) :
    (Z.subgroupOf P).map (P.normalizerMonoidHom x : ↥P →* ↥P) = Z.subgroupOf P := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    replace hz : (z : Γ) ∈ Z := hz
    change ((P.normalizerMonoidHom x z : P) : Γ) ∈ Z
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hx z).mp hz
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    refine ⟨(P.normalizerMonoidHom x)⁻¹ y, ?_, ?_⟩
    · change (((P.normalizerMonoidHom x)⁻¹ y : P) : Γ) ∈ Z
      rw [← map_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (Z : Set Γ)).inv_mem hx) y).mp hy
    · change P.normalizerMonoidHom x ((P.normalizerMonoidHom x)⁻¹ y) = y
      rw [MulAut.apply_inv_self]

@[expose] noncomputable def conjSecAut (P Z K : Subgroup Γ) [(Z.subgroupOf P).Normal]
    (hKP : K ≤ Subgroup.normalizer (P : Set Γ)) (hKZ : K ≤ Subgroup.normalizer (Z : Set Γ)) :
    ↥K →* MulAut (↥P ⧸ Z.subgroupOf P) where
  toFun k := QuotientGroup.congr (Z.subgroupOf P) (Z.subgroupOf P)
    (P.normalizerMonoidHom ⟨k, hKP k.2⟩) (map_normalizerMonoidHom_subgroupOf _ (hKZ k.2))
  map_one' := by
    ext q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.congr_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  map_mul' k k' := by
    ext q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul, mul_inv_rev]
    group

variable {P Z K : Subgroup Γ} [(Z.subgroupOf P).Normal]
  {hKP : K ≤ Subgroup.normalizer (P : Set Γ)} {hKZ : K ≤ Subgroup.normalizer (Z : Set Γ)}

theorem conjSecAut_mk (k : K) (y : P) :
    conjSecAut P Z K hKP hKZ k (y : ↥P ⧸ Z.subgroupOf P) =
      ((⟨(k : Γ) * y * (k : Γ)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKP k.2) y).mp y.2⟩ : P) :
        ↥P ⧸ Z.subgroupOf P) :=
  rfl

theorem conjSecAut_eq_one_iff (k : K) :
    conjSecAut P Z K hKP hKZ k = 1 ↔ ∀ y ∈ P, (k : Γ) * y * (k : Γ)⁻¹ * y⁻¹ ∈ Z := by
  constructor
  · intro h1 y hy
    have := DFunLike.congr_fun h1 ((⟨y⁻¹, P.inv_mem hy⟩ : P) : ↥P ⧸ Z.subgroupOf P)
    rw [conjSecAut_mk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
    simpa [mul_assoc] using this
  · intro h
    ext q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [conjSecAut_mk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := h _ (P.inv_mem y.2)
    simpa [mul_assoc] using this

end Dih

open Dih

theorem dihFour_holds : DihFour := by
  intro Γ _ _ H T M V h hc I g hI hg hIV A hA p a hp hp2 ha ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have econj : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  have hgen : I = V ⊔ B6.conjSub g⁻¹ V := econj ▸ hIV
  have hpr : E2.Pair I (T ⊓ I) (M ⊓ I) V g⁻¹ :=
    h.pair_of_member (E213M.noRoot_of_isInIHTV hI) (I.inv_mem hg) hgen
  have hcharI : CharTwo I := by
    have := E2.charTwo_of_charTwo h (hI.1 (I.inv_mem hg)) hc
    rwa [← hgen] at this
  have hodd : Odd (p ^ a) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨hPO, hOJ, -⟩ := hpr.e2_10_six (hpr.relIndex_eq_two_of_dihedral hodd e)
  set B := kerIn (M ⊓ I) I ⊓ V with hBdef
  set P := B ⊔ B6.conjSub g⁻¹ B with hPdef
  set Z := V ⊓ B6.conjSub g⁻¹ V with hZdef
  have hPI : P ≤ I := hpr.P_le_X
  have hZP : Z ≤ P := hpr.inf_conj_le_P
  have hIP : I ≤ Subgroup.normalizer (P : Set Γ) := hpr.le_normalizer_P
  have hIZ : I ≤ Subgroup.normalizer (Z : Set Γ) := hpr.le_normalizer_Z
  haveI : (Z.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).2 (hPI.trans hIZ)
  set ρ := conjSecAut P Z I hIP hIZ with hρ
  have hcomm : ∀ x y : ↥P ⧸ Z.subgroupOf P, x * y = y * x := by
    intro x y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (((x * y)⁻¹ * (y * x) : P) : Γ) =
        (y : Γ)⁻¹ * (x : Γ)⁻¹ * (y : Γ)⁻¹⁻¹ * (x : Γ)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact (hpr.commutator_sq_mem_Z (P.inv_mem y.2) (P.inv_mem x.2)).1
  have hsq : ∀ x : ↥P ⧸ Z.subgroupOf P, x * x = 1 := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, ← pow_two]
    exact (hpr.commutator_sq_mem_Z x.2 x.2).2
  set q := QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) with hq
  have hker : ∀ x : I, q x = 1 → ρ x = 1 := by
    intro x hx
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    have hxP : (x : Γ) ∈ P := by rw [hPO, hOJ]; exact hx
    rw [hρ, conjSecAut_eq_one_iff]
    intro y hy
    exact (hpr.commutator_sq_mem_Z hxP hy).1
  obtain ⟨c, hc'⟩ := QuotientGroup.mk'_surjective ((kerIn (M ⊓ I) I).subgroupOf I)
    (e.symm (DihedralGroup.r 1))
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective ((kerIn (M ⊓ I) I).subgroupOf I)
    (e.symm (DihedralGroup.sr 0))
  rw [← hq] at hc' ht
  have hγfin : ρ c ^ p ^ (a - 1 + 1) = 1 := by
    rw [Nat.sub_add_cancel ha, ← map_pow]
    apply hker
    rw [map_pow, hc', ← map_pow, DihedralGroup.r_one_pow_n, map_one]
  have hγnot : ¬ ρ c ^ p ^ (a - 1) = 1 := by
    intro h1
    rw [← map_pow, hρ, conjSecAut_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := Ch3E213M.isTwo_of_centralizes hpr hcharI (c ^ p ^ (a - 1)).2 h1
    have hn' : (c ^ p ^ (a - 1)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
    have h2 := congrArg (fun x => e (q x)) hn'
    simp only [map_pow, map_one, hc', MulEquiv.apply_symm_apply, ← pow_mul] at h2
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [DihedralGroup.orderOf_r_one] at h3
    have h4 : p ^ (a - 1) * p ∣ p ^ (a - 1) * 2 ^ n := by
      rwa [← pow_succ, Nat.sub_add_cancel ha]
    have h5 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h5))
  have hγ : orderOf (ρ c) = p ^ a := by
    rw [orderOf_eq_prime_pow hγnot hγfin, Nat.sub_add_cancel ha]
  have hτ : ρ t * ρ t = 1 := by
    rw [← map_mul]
    apply hker
    rw [map_mul, ht, ← map_mul, DihedralGroup.sr_mul_sr, sub_self, ← DihedralGroup.one_def,
      map_one]
  have hτγ : ρ t * ρ c * (ρ t)⁻¹ = (ρ c)⁻¹ := by
    have h1 : ρ (t * c * t⁻¹ * c) = 1 := by
      apply hker
      rw [map_mul, map_mul, map_mul, map_inv, hc', ht, ← map_inv, ← map_mul, ← map_mul,
        ← map_mul, DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
        DihedralGroup.r_mul_r, ← map_one e.symm, DihedralGroup.one_def]
      congr 2
      ring
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hmod := two_pow_le_card hcomm hsq hp hp2 ha hγ hτ hτγ
  have hPZ : Nat.card (↥P ⧸ Z.subgroupOf P) = Z.relIndex B ^ 2 := by
    rw [← Ch3E213M.relIndex_P_eq hpr]
    rfl
  rw [hPZ] at hmod
  have hAeq : A = B6.conjSub g⁻¹ B := by rw [hA, econj, hpr.conjSub_kerIn_inf_eq]
  have hAN : A ≤ Subgroup.normalizer (V : Set Γ) := by
    rw [hA]
    exact inf_le_right.trans hpr.pCoreOf_le_normalizer
  have hCA : A ⊓ Subgroup.centralizer (V : Set Γ) = V ⊓ conjSubgroup V g := by
    rw [econj]
    apply le_antisymm
    · rintro x ⟨hxA, hxC⟩
      rw [hAeq] at hxA
      exact hpr.mem_inf_conj_of_comm hxA fun v hv => (Subgroup.mem_centralizer_iff.1 hxC v hv).symm
    · intro z hz
      refine ⟨hAeq ▸ hpr.inf_conj_le_conjSub hz, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
      exact hpr.comm hv hz.1
  have hcard := E213.card_autI_eq_relIndex h hpr hA hAN hCA
  obtain ⟨b, hb⟩ := E213M.exists_relIndex_eq_two_pow
    ((B6.isPGroup_of_isElemAbelian h.elem).to_le inf_le_right) Z
  have hrk : rk ↥(autI h.elem A) = b := by
    unfold rk
    rw [hcard, hb, padicValNat.prime_pow]
  rw [hrk]
  rw [hb, ← pow_mul] at hmod
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hmod
  omega

end CFSG.Quasithin.SimsE2
