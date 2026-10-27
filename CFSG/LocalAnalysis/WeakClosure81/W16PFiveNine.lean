module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIc

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem Cex16.conj_le_centralizer_of_le_S (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) {x : G} (hxS : conjSubgroup V x ≤ S) :
    conjSubgroup V x ≤ centralizer (V : Set G) :=
  (E3.le_wClos ⟨hxS, x, le_rfl, E3.mQuot_self _⟩).trans (h.wClos_le_centralizer h1 hS)

theorem Cex16.mem_of_conj_le_sup (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G)) {k : G} (hk : k ∈ H)
    (hkV : ∀ v ∈ V, k * v * k⁻¹ ∈ V ⊔ pCoreOf 2 (conjClosure V H)) : k ∈ M := by
  have hIV : ∀ i ∈ iSub16 V H, ∀ v ∈ V, i * v * i⁻¹ * v⁻¹ ∈ V₀ := by
    intro i hi v hv
    have hiC : i ∈ F11.CTilde M V₀ V :=
      (h.pCoreOf_le_cTilde h1 hS hF) (h.iSub16_le_pCoreOf hF hi)
    exact (FourteenTwo.mem_cTilde_iff_comm.1 hiC).2.2 v hv
  have hCV : V ⊓ centralizer (iSub16 V H : Set G) = U ⊔ V₀ :=
    h.inf_centralizer_iSub16_eq h1 h5 hS hF hV
  have hUV0_ne : U ⊔ V₀ ≠ V := by
    intro heq
    apply hV
    rw [← heq, ← h.inf_pCoreOf_eq h1 h5 hS hF hV]
    exact inf_le_right
  have hIV_ne : ∃ i ∈ iSub16 V H, ∃ v ∈ V, i * v * i⁻¹ * v⁻¹ ≠ 1 := by
    by_contra hcon
    have hle : V ≤ centralizer (iSub16 V H : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      have h1 : i * v * i⁻¹ * v⁻¹ = 1 := by
        by_contra hne
        exact hcon ⟨i, hi, v, hv, hne⟩
      calc i * v = (i * v * i⁻¹ * v⁻¹) * (v * i) := by group
        _ = 1 * (v * i) := by rw [h1]
        _ = v * i := one_mul _
    exact hUV0_ne (by rw [← hCV, inf_eq_left.mpr hle])
  obtain ⟨i, hi, v, hv, hc1⟩ := hIV_ne
  have hcV₀ : i * v * i⁻¹ * v⁻¹ ∈ V₀ := hIV i hi v hv
  have hki : k * i * k⁻¹ ∈ iSub16 V H := by
    show k * i * k⁻¹ ∈ conjClosure (V ⊓ pCoreOf 2 H) H
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H hk) i).mp hi
  have hVn : V ≤ Subgroup.normalizer (pCoreOf 2 (conjClosure V H) : Set G) :=
    (le_conjClosure V H).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (conjClosure V H))
  have hkv_mem : k * v * k⁻¹ ∈ (V : Set G) * (pCoreOf 2 (conjClosure V H) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right V _ hVn]
    exact hkV v hv
  obtain ⟨v', hv', q, hq, hvq⟩ := hkv_mem
  have hqI : q ∈ centralizer (iSub16 V H : Set G) := hQ hq
  have hcomm_q : q * (k * i * k⁻¹) = (k * i * k⁻¹) * q :=
    (Subgroup.mem_centralizer_iff.mp hqI (k * i * k⁻¹) hki).symm
  have hkey : (k * i * k⁻¹) * (v' * q) * (k * i * k⁻¹)⁻¹ * (v' * q)⁻¹
      = (k * i * k⁻¹) * v' * (k * i * k⁻¹)⁻¹ * v'⁻¹ := by
    have hqa : q * (k * i * k⁻¹)⁻¹ = (k * i * k⁻¹)⁻¹ * q := by
      calc q * (k * i * k⁻¹)⁻¹
          = (k * i * k⁻¹)⁻¹ * ((k * i * k⁻¹) * q) * (k * i * k⁻¹)⁻¹ := by group
        _ = (k * i * k⁻¹)⁻¹ * (q * (k * i * k⁻¹)) * (k * i * k⁻¹)⁻¹ := by rw [← hcomm_q]
        _ = (k * i * k⁻¹)⁻¹ * q := by group
    calc (k * i * k⁻¹) * (v' * q) * (k * i * k⁻¹)⁻¹ * (v' * q)⁻¹
        = (k * i * k⁻¹) * v' * (q * (k * i * k⁻¹)⁻¹ * q⁻¹) * v'⁻¹ := by group
      _ = (k * i * k⁻¹) * v' * (k * i * k⁻¹)⁻¹ * v'⁻¹ := by rw [hqa]; group
  have hkcV₀ : k * (i * v * i⁻¹ * v⁻¹) * k⁻¹ ∈ V₀ := by
    have hconj : k * (i * v * i⁻¹ * v⁻¹) * k⁻¹
        = (k * i * k⁻¹) * (k * v * k⁻¹) * (k * i * k⁻¹)⁻¹ * (k * v * k⁻¹)⁻¹ := by
      group
    rw [hconj, ← hvq, hkey]
    exact hIV (k * i * k⁻¹) hki v' hv'
  by_contra hkM
  have hmem : i * v * i⁻¹ * v⁻¹ ∈ conjSubgroup V₀ k ⊓ V₀ :=
    ⟨mem_conjSubgroup_iff.2 hkcV₀, hcV₀⟩
  rw [h.hyp.conj_inf_eq_bot hkM] at hmem
  exact hc1 (Subgroup.mem_bot.1 hmem)

theorem IsMinFam16.mem_centralizer_of_comm_mem (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G)) {b : G}
    (hbV : b ∈ centralizer (V : Set G))
    (hbK : ∀ k ∈ conjClosure V H, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure V H)) :
    b ∈ centralizer (iSub16 V H : Set G) := by
  have hI := IsMinFam16.iSub16_eq_conjClosure h1 hS h hH hV
  have hbz : ∀ z ∈ V ⊓ pCoreOf 2 H, b * z * b⁻¹ = z := by
    intro z hz
    have hcomm : z * b = b * z := Subgroup.mem_centralizer_iff.mp hbV z hz.1
    rw [← hcomm]; group
  have hgen : ∀ k ∈ conjClosure V H, ∀ z ∈ V ⊓ pCoreOf 2 H,
      b * (k * z * k⁻¹) * b⁻¹ = k * z * k⁻¹ := by
    intro k hk z hz
    have hq : b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure V H) := hbK k hk
    have hqI : b * k * b⁻¹ * k⁻¹ ∈ centralizer (iSub16 V H : Set G) := hQ hq
    have hgenI : k * z * k⁻¹ ∈ iSub16 V H := by
      rw [hI]
      exact mem_conjClosure hk hz
    have hqcomm : (k * z * k⁻¹) * (b * k * b⁻¹ * k⁻¹) =
        (b * k * b⁻¹ * k⁻¹) * (k * z * k⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hqI (k * z * k⁻¹) hgenI
    calc b * (k * z * k⁻¹) * b⁻¹
        = (b * k * b⁻¹) * (b * z * b⁻¹) * (b * k * b⁻¹)⁻¹ := by group
      _ = (b * k * b⁻¹ * k⁻¹) * (k * z * k⁻¹) * (b * k * b⁻¹ * k⁻¹)⁻¹ := by
            rw [hbz z hz]; group
      _ = k * z * k⁻¹ := by rw [← hqcomm]; group
  have hle : iSub16 V H ≤ centralizer ({b} : Set G) := by
    rw [hI]
    refine conjClosure_le fun k hk z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc b * (k * z * k⁻¹) = (b * (k * z * k⁻¹) * b⁻¹) * b := by group
      _ = (k * z * k⁻¹) * b := by rw [hgen k hk z hz]
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) b (Set.mem_singleton b)).symm

theorem mem_centralizer_of_odd_of_mul_conj {W : Subgroup G} {a c : G}
    (ha : a ∈ centralizer (W : Set G)) (hc : c ∈ normalizer (W : Set G))
    (hodd : Odd (orderOf c)) (h2 : ∃ k : ℕ, orderOf (a * c * a⁻¹ * c) = 2 ^ k) :
    c ∈ centralizer (W : Set G) := by
  have haN : a ∈ normalizer (W : Set G) := centralizer_le_normalizer _ ha
  have hc2N : c * c ∈ normalizer (W : Set G) := Subgroup.mul_mem _ hc hc
  have hrN : a * c * a⁻¹ * c ∈ normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ haN hc) (Subgroup.inv_mem _ haN)) hc
  let φ : normalizer (W : Set G) →* MulAut W := normalizerMonoidHom (H := W)
  have hker : φ.ker = (centralizer (W : Set G)).subgroupOf (normalizer (W : Set G)) :=
    normalizerMonoidHom_ker W
  have hphi_a : φ ⟨a, haN⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_subgroupOf.2 ha
  have hphi_c2_eq : φ ⟨c * c, hc2N⟩ = φ ⟨a * c * a⁻¹ * c, hrN⟩ := by
    have e1 : φ ⟨c * c, hc2N⟩ = φ ⟨c, hc⟩ * φ ⟨c, hc⟩ := by
      rw [← map_mul]
      congr 1
    have e2 : φ ⟨a * c * a⁻¹ * c, hrN⟩ = φ ⟨c, hc⟩ * φ ⟨c, hc⟩ := by
      have heq : (⟨a * c * a⁻¹ * c, hrN⟩ : normalizer (W : Set G)) =
          ⟨a, haN⟩ * ⟨c, hc⟩ * ⟨a, haN⟩⁻¹ * ⟨c, hc⟩ := by
        ext
        simp [mul_assoc]
      rw [heq, map_mul, map_mul, map_mul, map_inv, hphi_a]
      simp
    rw [e1, e2]
  obtain ⟨k, hk⟩ := h2
  have hdvd_c : orderOf (φ ⟨c * c, hc2N⟩) ∣ orderOf c := by
    refine orderOf_dvd_iff_pow_eq_one.2 ?_
    have hpow : (⟨c * c, hc2N⟩ : normalizer (W : Set G)) ^ orderOf c = 1 := by
      ext
      show (c * c) ^ orderOf c = 1
      rw [← pow_two c, ← pow_mul, Nat.mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    rw [← map_pow, hpow, map_one]
  have hdvd_r : orderOf (φ ⟨a * c * a⁻¹ * c, hrN⟩) ∣ 2 ^ k := by
    rw [← hk]
    refine orderOf_dvd_iff_pow_eq_one.2 ?_
    have hpow : (⟨a * c * a⁻¹ * c, hrN⟩ : normalizer (W : Set G)) ^
        orderOf (a * c * a⁻¹ * c) = 1 := by
      ext
      simp [pow_orderOf_eq_one]
    rw [← map_pow, hpow, map_one]
  have hcop : Nat.Coprime (orderOf c) (2 ^ k) := (hodd.coprime_two_left.pow_left k).symm
  have hphi_c2 : φ ⟨c * c, hc2N⟩ = 1 := by
    refine orderOf_eq_one_iff.1 ?_
    have hd : orderOf (φ ⟨c * c, hc2N⟩) ∣ Nat.gcd (orderOf c) (2 ^ k) :=
      Nat.dvd_gcd hdvd_c (hphi_c2_eq ▸ hdvd_r)
    rw [show Nat.gcd (orderOf c) (2 ^ k) = 1 from hcop] at hd
    exact Nat.dvd_one.mp hd
  have hcc_cent : c * c ∈ centralizer (W : Set G) := by
    have hm : (⟨c * c, hc2N⟩ : normalizer (W : Set G)) ∈
        (centralizer (W : Set G)).subgroupOf (normalizer (W : Set G)) := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hphi_c2
    exact Subgroup.mem_subgroupOf.mp hm
  have hc_z : c ∈ Subgroup.zpowers (c * c) := by
    have h : c ∈ Subgroup.zpowers (c ^ 2) := by
      rw [mem_zpowers_pow_iff]
      exact hodd.coprime_two_left
    simpa [pow_two] using h
  exact Subgroup.zpowers_le.mpr hcc_cent hc_z

private theorem le_normalizer_centralizer_of_le_normalizer {L Z : Subgroup G}
    (hZL : Z ≤ Subgroup.normalizer (L : Set G)) :
    Z ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) := by
  intro x hx
  have hx' : ∀ y, y ∈ L ↔ x * y * x⁻¹ ∈ L :=
    Subgroup.mem_normalizer_iff.mp (hZL hx)
  have hx'' : ∀ y, y ∈ L → x⁻¹ * y * x ∈ L := by
    intro y hy
    rw [hx']
    simpa [mul_assoc] using hy
  rw [Subgroup.mem_normalizer_iff]
  intro c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    have h1 := hc (x⁻¹ * y * x) (hx'' y hy)
    calc y * (x * c * x⁻¹) = x * ((x⁻¹ * y * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * y * x)) * x⁻¹ := by rw [h1]
      _ = x * c * x⁻¹ * y := by group
  · intro hc y hy
    have h1 := hc (x * y * x⁻¹) ((hx' y).mp hy)
    have h2 : (x * y * x⁻¹) * (x * c * x⁻¹) = x * (y * c) * x⁻¹ := by group
    have h3 : (x * c * x⁻¹) * (x * y * x⁻¹) = x * (c * y) * x⁻¹ := by group
    rw [h2, h3] at h1
    have h4 := congrArg (fun z => x⁻¹ * z * x) h1
    simpa [mul_assoc] using h4

theorem IsMinFam16.mQuot_inf_centralizer_le (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G)) {x : G}
    (hxS : conjSubgroup V x ≤ S)
    (h9 : ∀ a ∈ conjSubgroup V x, ∃ v ∈ V, ∀ k ∈ conjClosure V H,
      (a * v⁻¹) * k * (a * v⁻¹)⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure V H)) :
    E3.mQuot (conjSubgroup V x) (conjSubgroup V x ⊓ centralizer (iSub16 V H : Set G)) ≤
      E3.mQuot V (U ⊔ V₀) := by
  have hF : Fam16 M U S H := hH.1
  have hVCnorm : V ≤ Subgroup.normalizer
      (Subgroup.centralizer (iSub16 V H : Set G) : Set G) :=
    le_normalizer_centralizer_of_le_normalizer
      (h.V_le_S.trans (hF.1.trans (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H)))
  have hAVC : conjSubgroup V x ≤ V ⊔ Subgroup.centralizer (iSub16 V H : Set G) := by
    intro a ha
    obtain ⟨v, hv, hcomm⟩ := h9 a ha
    have haV : a ∈ Subgroup.centralizer (V : Set G) :=
      Cex16.conj_le_centralizer_of_le_S h1 hS h hxS ha
    have hvV : v ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (B2F.isElemAbelian_comm h.hyp.h6.elemAbelian hv hw).symm
    have hav : a * v⁻¹ ∈ Subgroup.centralizer (iSub16 V H : Set G) :=
      IsMinFam16.mem_centralizer_of_comm_mem h1 hS h hH hV hQ
        (Subgroup.mul_mem _ haV (Subgroup.inv_mem _ hvV)) hcomm
    have hmem : (a * v⁻¹) * v ∈ V ⊔ Subgroup.centralizer (iSub16 V H : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right hav) (Subgroup.mem_sup_left hv)
    simpa [mul_assoc] using hmem
  have hrel : (Subgroup.centralizer (iSub16 V H : Set G)).relIndex (conjSubgroup V x) ≤
      (Subgroup.centralizer (iSub16 V H : Set G)).relIndex V := by
    have h1 : (Subgroup.centralizer (iSub16 V H : Set G)).relIndex (conjSubgroup V x) ≤
        (Subgroup.centralizer (iSub16 V H : Set G)).relIndex
          (V ⊔ Subgroup.centralizer (iSub16 V H : Set G)) :=
      Subgroup.relIndex_le_of_le_right hAVC
        (E3.relIndex_ne_zero' (V ⊔ Subgroup.centralizer (iSub16 V H : Set G))
          (Subgroup.centralizer (iSub16 V H : Set G)))
    have h2 : (Subgroup.centralizer (iSub16 V H : Set G)).relIndex
          (V ⊔ Subgroup.centralizer (iSub16 V H : Set G)) =
        (Subgroup.centralizer (iSub16 V H : Set G)).relIndex V := by
      simp only [Subgroup.relIndex, Subgroup.index]
      haveI : ((Subgroup.centralizer (iSub16 V H : Set G)).subgroupOf V).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hVCnorm
      haveI : ((Subgroup.centralizer (iSub16 V H : Set G)).subgroupOf
          (V ⊔ Subgroup.centralizer (iSub16 V H : Set G))).Normal :=
        Subgroup.normal_subgroupOf_sup_of_le_normalizer hVCnorm
      exact (Nat.card_congr
        (QuotientGroup.quotientInfEquivProdNormalizerQuotient V
          (Subgroup.centralizer (iSub16 V H : Set G)) hVCnorm).toEquiv).symm
    omega
  have hrel' : (conjSubgroup V x ⊓ Subgroup.centralizer (iSub16 V H : Set G)).relIndex
        (conjSubgroup V x) ≤
      (V ⊓ Subgroup.centralizer (iSub16 V H : Set G)).relIndex V := by
    rw [Subgroup.inf_relIndex_left (conjSubgroup V x)
          (Subgroup.centralizer (iSub16 V H : Set G)),
        Subgroup.inf_relIndex_left V (Subgroup.centralizer (iSub16 V H : Set G))]
    exact hrel
  have hA2 : IsPGroup 2 (conjSubgroup V x) :=
    IsPGroup.map (p := 2) (H := V) h.hyp.isPGroup (MulAut.conj x⁻¹).toMonoidHom
  have e1 : (conjSubgroup V x ⊓ Subgroup.centralizer (iSub16 V H : Set G)).relIndex
        (conjSubgroup V x) =
      2 ^ E3.mQuot (conjSubgroup V x)
        (conjSubgroup V x ⊓ Subgroup.centralizer (iSub16 V H : Set G)) :=
    E3.relIndex_eq_two_pow hA2 _
  have e2 : (V ⊓ Subgroup.centralizer (iSub16 V H : Set G)).relIndex V =
      2 ^ E3.mQuot V (V ⊓ Subgroup.centralizer (iSub16 V H : Set G)) :=
    E3.relIndex_eq_two_pow h.hyp.isPGroup _
  have hm : E3.mQuot (conjSubgroup V x)
        (conjSubgroup V x ⊓ Subgroup.centralizer (iSub16 V H : Set G)) ≤
      E3.mQuot V (V ⊓ Subgroup.centralizer (iSub16 V H : Set G)) := by
    have h : 2 ^ E3.mQuot (conjSubgroup V x)
          (conjSubgroup V x ⊓ Subgroup.centralizer (iSub16 V H : Set G)) ≤
        2 ^ E3.mQuot V (V ⊓ Subgroup.centralizer (iSub16 V H : Set G)) := by
      rw [← e1, ← e2]
      exact hrel'
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h
  rwa [h.inf_centralizer_iSub16_eq h1 h5 hS hF hV] at hm

end CFSG.LocalAnalysis.WeakClosure81

end
