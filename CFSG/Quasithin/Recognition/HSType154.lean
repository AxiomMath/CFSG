module

public import CFSG.Quasithin.Recognition.HSTypeCtx
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Recognition.HSType154Pack

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique MulAction
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
open HSSetting

theorem normLamS_inv_mul_of_not : ∀ σ τ : Equiv.Perm (Fin 6), σ ∈ stabS → τ ∈ stabS →
    ¬ NormLamS σ → ¬ NormLamS τ → NormLamS (σ⁻¹ * τ) := fun σ τ h1 h2 h3 h4 =>
  Pack154.normLamS_inv_mul_of_not_code σ τ ⟨h1, h3⟩ ⟨h2, h4⟩

theorem mem_lamS_of_normLamS : ∀ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 →
    NormLamS σ → σ ∈ lamS :=
  Pack154.mem_lamS_of_normLamS_code

theorem inv_mul_mem_lamS_of_normLamS : ∀ σ τ : Equiv.Perm (Fin 6), σ ∈ stabS → τ ∈ stabS →
    NormLamS σ → NormLamS τ → σ ∉ lamS → τ ∉ lamS → σ⁻¹ * τ ∈ lamS :=
  fun σ τ h1 h2 h3 h4 h5 h6 => Pack154.inv_mul_mem_lamS_code σ τ ⟨h1, h3, h5⟩ ⟨h2, h4, h6⟩

theorem normLamS_inv : ∀ σ : Equiv.Perm (Fin 6), NormLamS σ → NormLamS σ⁻¹ :=
  Pack154.normLamS_inv_code

theorem inV2m_of_kleinS_fix : ∀ v : SpV,
    (∀ σ : Equiv.Perm (Fin 6), σ ∈ kleinS → actS6 σ v = v) → InV2m v := by
  decide +kernel

theorem kleinS_fix_of_inV2m : ∀ σ : Equiv.Perm (Fin 6), σ ∈ kleinS → ∀ v : SpV, InV2m v →
    actS6 σ v = v := by
  decide +kernel

namespace HSCtx

variable {G : Type} [Group G] [Finite G] (C : HSCtx G)

theorem L1_le_L : C.L1 ≤ C.L := le_sup_left

theorem L2_le_L : C.L2 ≤ C.L := le_sup_right

theorem L_le_normalizer : C.L ≤ Subgroup.normalizer (C.L : Set G) := Subgroup.le_normalizer

theorem mul_mem_NN {a b : G} (ha : a ∈ Subgroup.normalizer (C.M.V2 : Set G))
    (hb : b ∈ Subgroup.normalizer (C.M.V2 : Set G)) (haN : a ∉ C.M.NN) (hbN : b ∉ C.M.NN) :
    a * b ∈ C.M.NN := by
  have hle : C.M.NN ≤ Subgroup.normalizer (C.M.V2 : Set G) := C.M.NN_le_normalizer
  have hidx : (C.M.NN.subgroupOf (Subgroup.normalizer (C.M.V2 : Set G))).index = 2 := by
    have h1 := (C.M.NN.subgroupOf (Subgroup.normalizer (C.M.V2 : Set G))).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      C.M.card_NN C.h C.hsmemH C.hsnotK C.hss C.hg₀,
      C.M.card_normalizer_V2 C.h C.hsmemH C.hsnotK C.hss C.hg₀] at h1
    omega
  have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).mpr
    ⟨fun h' => absurd (Subgroup.mem_subgroupOf.mp h') haN,
      fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hbN⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem i_mem_NN : (C.i : G) ∈ C.M.NN := C.M.mem_pre.mpr ⟨C.i.2, C.hist⟩

theorem conj_mem_L1_iff {n : ↥(hsNB C.z C.s)} (hn : NormLamS (C.M.π n)) (k : G) :
    k ∈ C.L1 ↔ (n : G) * k * (n : G)⁻¹ ∈ C.L1 := by
  refine ⟨fun hk => C.M.conj_mem_L1 hn hk, fun hk => ?_⟩
  have hn' : NormLamS (C.M.π n⁻¹) := by
    rw [map_inv]
    exact normLamS_inv _ hn
  have := C.M.conj_mem_L1 hn' hk
  rwa [Subgroup.coe_inv, inv_inv, show (n : G)⁻¹ * ((n : G) * k * (n : G)⁻¹) * (n : G) = k by
    group] at this

theorem normLamS_of_conj {n : ↥(hsNB C.z C.s)}
    (hn : ∀ k ∈ C.L1, (n : G) * k * (n : G)⁻¹ ∈ C.L1) : NormLamS (C.M.π n) := by
  rw [normLamS_iff]
  intro σ hσ
  obtain ⟨k, hk⟩ := C.M.π_surj σ
  have hkL : (k : G) ∈ C.L1 := C.M.mem_pre.mpr ⟨k.2, show C.M.π k ∈ lamS by rw [hk]; exact hσ⟩
  have hm : (n : G) * k * (n : G)⁻¹ ∈ hsNB C.z C.s :=
    (hsNB C.z C.s).mul_mem ((hsNB C.z C.s).mul_mem n.2 k.2) ((hsNB C.z C.s).inv_mem n.2)
  have h2 := C.M.π_mem_of_mem_pre (hn _ hkL) hm
  have e : (⟨(n : G) * k * (n : G)⁻¹, hm⟩ : ↥(hsNB C.z C.s)) = n * k * n⁻¹ := rfl
  rwa [e, map_mul, map_mul, map_inv, hk] at h2

theorem mem_normalizer_of_swap {c : G} (h1 : ∀ k, k ∈ C.L1 ↔ c * k * c⁻¹ ∈ C.L2)
    (h2 : ∀ k, k ∈ C.L2 ↔ c * k * c⁻¹ ∈ C.L1) : c ∈ Subgroup.normalizer (C.L : Set G) := by
  have hle : C.L ≤ C.L.comap (MulAut.conj c).toMonoidHom := by
    refine sup_le (fun k hk => ?_) (fun k hk => ?_)
    · exact C.L2_le_L ((h1 k).mp hk)
    · exact C.L1_le_L ((h2 k).mp hk)
  exact Subgroup.mem_normalizer_fintype fun k hk => hle hk

theorem exists_c : ∃ c ∈ Subgroup.normalizer (C.M.V2 : Set G), c ∉ C.M.NN ∧
    (∀ k, k ∈ C.L1 ↔ c * k * c⁻¹ ∈ C.L2) ∧ (∀ k, k ∈ C.L2 ↔ c * k * c⁻¹ ∈ C.L1) := by
  obtain ⟨hyN, hyst, hyalt, hyl⟩ := C.M.mem_alt_conj C.h C.hsmemH C.hsnotK C.hss C.hg₀ C.hg
    C.hi2 C.hist C.hil C.hifx C.hin C.hiNL
  have hyNorm : ¬ NormLamS (C.M.π ⟨C.g⁻¹ * C.i * C.g, hyN⟩) := fun hn =>
    hyl (mem_lamS_of_normLamS _ (Equiv.Perm.mem_alternatingGroup.mp hyalt) hn)
  have hgg : C.g * C.g ∈ C.M.NN := C.mul_mem_NN C.hg C.hg C.hgNN C.hgNN
  have hyNN : C.g⁻¹ * C.i * C.g ∈ C.M.NN := C.M.mem_pre.mpr ⟨hyN, hyst⟩
  have hgig : C.g * C.i * C.g ∈ C.M.NN := by
    have := C.M.NN.mul_mem hgg hyNN
    rwa [show C.g * C.g * (C.g⁻¹ * C.i * C.g) = C.g * C.i * C.g by group] at this
  obtain ⟨hggN, hggπ⟩ := C.M.mem_pre.mp hgg
  obtain ⟨hgigN, hgigπ⟩ := C.M.mem_pre.mp hgig
  have hprod : (⟨C.g * C.g, hggN⟩ : ↥(hsNB C.z C.s))⁻¹ * ⟨C.g * C.i * C.g, hgigN⟩ =
      ⟨C.g⁻¹ * C.i * C.g, hyN⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
  have hcases : NormLamS (C.M.π ⟨C.g * C.g, hggN⟩) ∨
      NormLamS (C.M.π ⟨C.g * C.i * C.g, hgigN⟩) := by
    by_contra hc
    rw [not_or] at hc
    apply hyNorm
    rw [← hprod, map_mul, map_inv]
    exact normLamS_inv_mul_of_not _ _ hggπ hgigπ hc.1 hc.2
  have hiNorm := C.conj_mem_L1_iff C.hin
  have hii : (C.i : G)⁻¹ = C.i := inv_eq_of_mul_eq_one_right C.hi2
  rcases hcases with ha | hb
  ·
    have hgg' := C.conj_mem_L1_iff ha
    refine ⟨C.g, C.hg, C.hgNN, fun k => ?_, fun k => ?_⟩
    · rw [mem_map_conj_iff, show C.g⁻¹ * (C.g * k * C.g⁻¹) * C.g = k by group]
    · rw [mem_map_conj_iff, hgg' (C.g⁻¹ * k * C.g)]
      rw [show C.g * C.g * (C.g⁻¹ * k * C.g) * (C.g * C.g)⁻¹ = C.g * k * C.g⁻¹ by group]
  ·
    have hgig' := C.conj_mem_L1_iff hb
    refine ⟨C.g * C.i, (Subgroup.normalizer _).mul_mem C.hg (C.M.NN_le_normalizer C.i_mem_NN),
      fun hm => C.hgNN ?_, fun k => ?_, fun k => ?_⟩
    · have := C.M.NN.mul_mem hm (C.M.NN.inv_mem C.i_mem_NN)
      rwa [mul_inv_cancel_right] at this
    · rw [mem_map_conj_iff, show C.g⁻¹ * (C.g * C.i * k * (C.g * C.i)⁻¹) * C.g =
        (C.i : G) * k * (C.i : G)⁻¹ by group]
      exact hiNorm k
    · rw [mem_map_conj_iff, hgig' (C.g⁻¹ * k * C.g)]
      rw [show C.g * C.i * C.g * (C.g⁻¹ * k * C.g) * (C.g * C.i * C.g)⁻¹ =
        C.g * C.i * k * (C.g * C.i)⁻¹ by group]

theorem mem_V2_iff (y : G) : y ∈ C.M.V2 ↔ y ∈ C.M.R ∧ ∀ r ∈ C.M.R, r * y = y * r := by
  constructor
  · intro hy
    have hyB : y ∈ hsB C.z C.s := C.M.V2_le_hsB hy
    refine ⟨C.M.hsB_le_pre kleinS hyB, fun r hr => ?_⟩
    obtain ⟨hrN, hrπ⟩ := C.M.mem_pre.mp hr
    obtain ⟨v, hv, rfl⟩ := C.M.mem_V2.mp hy
    have h1 := C.M.act' hrN v
    rw [kleinS_fix_of_inV2m _ hrπ v hv] at h1
    calc r * C.M.Φ v = r * C.M.Φ v * r⁻¹ * r := by group
      _ = C.M.Φ v * r := by rw [h1]
  · rintro ⟨hyR, hyc⟩
    have hyB : y ∈ hsB C.z C.s := by
      rw [← C.h.centralizer_hsB C.hsmemH C.hsnotK C.hss C.hg₀]
      exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
        hyc b (C.M.hsB_le_pre kleinS hb)
    obtain ⟨v, rfl⟩ := C.M.surj y hyB
    refine C.M.Φ_mem_V2 (inV2m_of_kleinS_fix v fun σ hσ => ?_)
    obtain ⟨r, hr⟩ := C.M.π_surj σ
    have hrR : (r : G) ∈ C.M.R := C.M.mem_pre.mpr ⟨r.2, show C.M.π r ∈ kleinS by rw [hr]; exact hσ⟩
    have h1 := C.M.act r v
    have h2 : (r : G) * C.M.Φ v * (r : G)⁻¹ = C.M.Φ v := by
      rw [hyc r hrR, mul_inv_cancel_right]
    rw [h2, hr] at h1
    exact C.M.inj h1.symm

theorem card_L :
    Nat.card C.L = 20160 := by
  rw [Nat.card_congr C.Φ.toEquiv]
  exact card_stabilizer_point 0

theorem mem_L_of_mem_NN
    {m : G} (hmNN : m ∈ C.M.NN)
    (hmL : m ∈ Subgroup.normalizer (C.L : Set G)) : m ∈ C.L := by
  obtain ⟨hmN, hmπ⟩ := C.M.mem_pre.mp hmNN
  have hmL1 : ∀ k ∈ C.L1, m * k * m⁻¹ ∈ C.L1 := by
    intro k hk
    have hkL : m * k * m⁻¹ ∈ C.L := (Subgroup.mem_normalizer_iff.mp hmL k).mp (C.L1_le_L hk)
    have hkN : m * k * m⁻¹ ∈ hsNB C.z C.s := (hsNB C.z C.s).mul_mem
      ((hsNB C.z C.s).mul_mem hmN (C.M.L1_le_hsNB hk)) ((hsNB C.z C.s).inv_mem hmN)
    exact C.M.inf_hsNB_le_L1 C.h C.hsmemH C.hsnotK C.hss C.hg₀ C.hg C.hgNN C.Φ C.hΦ1 hkL hkN
  have hnorm := C.normLamS_of_conj (n := ⟨m, hmN⟩) hmL1
  by_cases hml : C.M.π ⟨m, hmN⟩ ∈ lamS
  · exact C.L1_le_L (C.M.mem_pre.mpr ⟨hmN, hml⟩)
  · exfalso
    have hmem := inv_mul_mem_lamS_of_normLamS _ _ hmπ C.hist hnorm C.hin hml C.hil
    have hmiN : m⁻¹ * C.i ∈ hsNB C.z C.s :=
      (hsNB C.z C.s).mul_mem ((hsNB C.z C.s).inv_mem hmN) C.i.2
    have e : (⟨m⁻¹ * C.i, hmiN⟩ : ↥(hsNB C.z C.s)) = (⟨m, hmN⟩ : ↥(hsNB C.z C.s))⁻¹ * C.i :=
      rfl
    have hmi : m⁻¹ * C.i ∈ C.L1 := C.M.mem_pre.mpr ⟨hmiN, by rw [e, map_mul, map_inv]; exact hmem⟩
    apply C.hiNL
    rw [show (C.i : G) = m * (m⁻¹ * C.i) by group]
    exact (Subgroup.normalizer _).mul_mem hmL (C.L_le_normalizer (C.L1_le_L hmi))

theorem normalizer_L_cases
    {c : G} (hcN : c ∈ Subgroup.normalizer (C.M.V2 : Set G))
    (hcNN : c ∉ C.M.NN) (hcL : c ∈ Subgroup.normalizer (C.L : Set G)) {n : G}
    (hn : n ∈ Subgroup.normalizer (C.L : Set G)) : n ∈ C.L ∨ n * c⁻¹ ∈ C.L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRL : C.M.R ≤ C.L := C.M.R_le_L1.trans C.L1_le_L
  have hcardR : Nat.card C.M.R = 64 := by
    show Nat.card ↥(C.M.pre kleinS) = 64
    rw [C.M.card_pre C.h C.hsmemH C.hsnotK C.hss C.hg₀, card_kleinS]
  have hsyl : ∀ P : Subgroup G, P ≤ C.L → Nat.card P = 64 → IsSylowTwoOf P C.L := by
    intro P hPL hP
    refine ⟨hPL, IsPGroup.of_card (n := 6) (by rw [hP]; norm_num), ?_⟩
    have h1 := (P.subgroupOf C.L).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv, hP, C.card_L] at h1
    have h2 : (P.subgroupOf C.L).index = 315 := by omega
    rw [h2]
    decide
  have hR'L : C.M.R.map (MulAut.conj n).toMonoidHom ≤ C.L := by
    rintro _ ⟨r, hr, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hn r).mp (hRL hr)
  have hR'c : Nat.card ↥(C.M.R.map (MulAut.conj n).toMonoidHom) = 64 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hcardR]
  obtain ⟨l, hl, hll⟩ := (hsyl _ hRL hcardR).exists_conj (hsyl _ hR'L hR'c)
  set m := l⁻¹ * n with hm
  have hmL : m ∈ Subgroup.normalizer (C.L : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem (C.L_le_normalizer hl)) hn
  have hmR : ∀ r ∈ C.M.R, m * r * m⁻¹ ∈ C.M.R := by
    intro r hr
    have h1 : n * r * n⁻¹ ∈ C.M.R.map (MulAut.conj l).toMonoidHom := by
      rw [← hll]
      exact ⟨r, hr, rfl⟩
    rw [mem_map_conj_iff] at h1
    rwa [hm, show l⁻¹ * n * r * (l⁻¹ * n)⁻¹ = l⁻¹ * (n * r * n⁻¹) * l by group]
  have hmRN : m ∈ Subgroup.normalizer (C.M.R : Set G) := Subgroup.mem_normalizer_fintype hmR
  have hmV : m ∈ Subgroup.normalizer (C.M.V2 : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨hyR, hyc⟩ := (C.mem_V2_iff y).mp hy
    refine (C.mem_V2_iff _).mpr ⟨hmR y hyR, fun r hr => ?_⟩
    have hr' : m⁻¹ * r * m ∈ C.M.R := by
      have := (Subgroup.mem_normalizer_iff.mp hmRN (m⁻¹ * r * m)).mpr
        (by rwa [show m * (m⁻¹ * r * m) * m⁻¹ = r by group])
      exact this
    have := hyc _ hr'
    calc r * (m * y * m⁻¹) = m * ((m⁻¹ * r * m) * y) * m⁻¹ := by group
      _ = m * (y * (m⁻¹ * r * m)) * m⁻¹ := by rw [this]
      _ = m * y * m⁻¹ * r := by group
  have hnl : n = l * m := by rw [hm]; group
  by_cases hmNN : m ∈ C.M.NN
  · left
    rw [hnl]
    exact C.L.mul_mem hl (C.mem_L_of_mem_NN hmNN hmL)
  · right
    have hc' : m * c⁻¹ ∈ C.M.NN := C.mul_mem_NN hmV ((Subgroup.normalizer _).inv_mem hcN) hmNN
      fun h => hcNN (by simpa using C.M.NN.inv_mem h)
    have hmcL : m * c⁻¹ ∈ Subgroup.normalizer (C.L : Set G) :=
      (Subgroup.normalizer _).mul_mem hmL ((Subgroup.normalizer _).inv_mem hcL)
    rw [hnl, mul_assoc]
    exact C.L.mul_mem hl (C.mem_L_of_mem_NN hc' hmcL)

end HSCtx

end CFSG.Quasithin.HSType
