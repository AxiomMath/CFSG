module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Inputs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S15B
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecOrthNatIff

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits

namespace F53.Stellmacher

open S15

theorem hss15 : Hss15 := by
  intro G _ _ X V hq hVQ hXV hV hCX s hsX hs
  have hQX : pCoreOf 2 X ≤ X := pCoreOf_le 2 X
  have hVX : V ≤ X := hVQ.trans hQX
  have hXVc : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun x hx v hv =>
    (Subgroup.mem_normalizer_iff.mp (hXV hx) v).mp hv
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (isMulCommutative_iff.mp hV.1 ⟨x, hx⟩ ⟨y, hy⟩)
  have hV2 : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← pow_two]; exact hV.2 v hv
  have hQV : ∀ q ∈ pCoreOf 2 X, ∀ v ∈ V, q * v * q⁻¹ = v := by
    intro q hq v hv
    have hq' : q ∈ X ⊓ Subgroup.centralizer (V : Set G) := hCX ▸ hq
    exact conj_eq_iff_comm.mpr (Subgroup.mem_centralizer_iff.mp hq'.2 v hv)
  have hCQ : ∀ x ∈ X, (∀ v ∈ V, x * v * x⁻¹ = v) → x ∈ pCoreOf 2 X := by
    intro x hx hxV
    rw [← hCX]
    exact ⟨hx, Subgroup.mem_centralizer_iff.mpr fun v hv => conj_eq_iff_comm.mp (hxV v hv)⟩
  have hsQ : s ∉ pCoreOf 2 X := by
    intro hsQ'
    have hle : V ≤ V ⊓ Subgroup.centralizer ({s} : Set G) := fun v hv =>
      ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr (conj_eq_iff_comm.mp (hQV s hsQ' v hv))⟩
    have := Subgroup.relIndex_eq_one.mpr hle
    omega
  obtain ⟨d, hdX, hd3, hdQ⟩ : ∃ d ∈ X, d ^ 3 = 1 ∧ d ∉ pCoreOf 2 X := by
    obtain ⟨ι⟩ := hq
    have hcard : Nat.card (OTwoQuot X) = 120 := by
      rw [Nat.card_congr ι.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have h3 : 3 ∣ Nat.card ↥X := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥X)]
      have h120 : Nat.card (↥X ⧸ CFSG.Open.pCore 2 ↥X) = 120 := hcard
      rw [h120]
      exact Dvd.dvd.mul_right (by norm_num) _
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hx' : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
    refine ⟨x, x.2, by rw [← hx']; exact pow_orderOf_eq_one _, fun hxQ => ?_⟩
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 X) ⟨(x : G), hxQ⟩
    have h1 : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hx'] at h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega
  have hdV : ∃ a ∈ V, d * a * d⁻¹ * a⁻¹ ∉ (⊥ : Subgroup G) := by
    by_contra h
    push Not at h
    exact hdQ (hCQ d hdX fun v hv => mul_inv_eq_one.mp (Subgroup.mem_bot.mp (h v hv)))
  obtain ⟨L, N, hstep, x₀, hx₀N, hx₀L⟩ := exists_chiefStep_of_cube hV2 hdX hd3 (Nat.card V) V ⊥
    (by omega) ⟨le_rfl, hXVc⟩ ⟨bot_le, fun g _ x hx => by
      rw [Subgroup.mem_bot] at hx ⊢
      rw [hx]
      group⟩ bot_le hdV
  have hnc : ¬ IsCentralStep X L N := fun h => hx₀L (h d hdX x₀ hx₀N)
  obtain ⟨hcS, hON⟩ := chiefStep_orth_or_nat hq hVQ hstep hnc
  have hLN : L ≤ N := hstep.2.2.1.le
  have hNV : N ≤ V := hstep.1.1
  have hXN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N := hstep.1.2
  have hXL : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L := hstep.2.1.2
  have hXLn : X ≤ Subgroup.normalizer (L : Set G) := normalizer_left hstep
  have hXNn : X ≤ Subgroup.normalizer (N : Set G) := normalizer_right hstep
  obtain ⟨n₀, hn₀N, hn₀L⟩ : ∃ n₀ ∈ N, s * n₀ * s⁻¹ * n₀⁻¹ ∉ L := by
    by_contra h
    push Not at h
    exact hsQ (hcS ▸ (mem_cSecIn_iff hXLn).mpr ⟨hsX, h⟩)
  have h2v := comm_eq_one_or_eq hVc (hXVc s hsX) hs (hNV hn₀N) (fun h => hn₀L (h ▸ L.one_mem))
  have h4a : ∀ v ∈ V, s * v * s⁻¹ * v⁻¹ ∈ N := by
    intro v hv
    rcases h2v v hv with h | h
    · rw [h]; exact N.one_mem
    · rw [h]; exact N.mul_mem (hXN s hsX n₀ hn₀N) (N.inv_mem hn₀N)
  have h4c : ∀ v ∈ V, s * v * s⁻¹ * v⁻¹ ∈ L → s * v * s⁻¹ * v⁻¹ = 1 := by
    intro v hv hL
    rcases h2v v hv with h | h
    · exact h
    · rw [h] at hL; exact absurd hL hn₀L
  have h4b : ∀ l ∈ L, s * l * s⁻¹ = l := fun l hl =>
    mul_inv_eq_one.mp (h4c l (hNV (hLN hl)) (L.mul_mem (hXL s hsX l hl) (L.inv_mem hl)))
  have hsec : secIdx (Subgroup.zpowers s) L N = 2 := by
    have hNLn : N ≤ Subgroup.normalizer (L : Set G) := (hNV.trans hVX).trans hXLn
    have hmem : ∀ x, x ∈ fixSecIn (Subgroup.zpowers s) L N ↔
        x ∈ N ∧ s * x * s⁻¹ * x⁻¹ ∈ L := fun x => mem_fixSecIn_zpowers_iff hNLn (hXLn hsX)
    have hle : V ⊓ Subgroup.centralizer ({s} : Set G) ⊓ N ≤
        fixSecIn (Subgroup.zpowers s) L N := by
      intro x hx
      refine (hmem x).mpr ⟨hx.2, ?_⟩
      have h1 : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hx.1.2
      rw [(conj_eq_iff_comm (a := x) (b := s)).mpr h1, mul_inv_cancel]
      exact L.one_mem
    have hne : ∀ H K : Subgroup G, H.relIndex K ≠ 0 := fun H K =>
      Subgroup.index_ne_zero_of_finite
    have hle2 : (fixSecIn (Subgroup.zpowers s) L N).relIndex N ≤ 2 := by
      calc (fixSecIn (Subgroup.zpowers s) L N).relIndex N
          ≤ (V ⊓ Subgroup.centralizer ({s} : Set G) ⊓ N).relIndex N :=
            Subgroup.relIndex_le_of_le_left hle (hne _ _)
        _ = (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex N :=
            Subgroup.inf_relIndex_right _ _
        _ ≤ (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V :=
            Subgroup.relIndex_le_of_le_right hNV (hne _ _)
        _ = 2 := hs
    have hne1 : (fixSecIn (Subgroup.zpowers s) L N).relIndex N ≠ 1 := fun h =>
      hn₀L ((hmem n₀).mp (Subgroup.relIndex_eq_one.mp h hn₀N)).2
    have hne0 := hne (fixSecIn (Subgroup.zpowers s) L N) N
    unfold secIdx
    omega
  have horth : IsOrthSec X L N := by
    rcases hON with h | h
    · exact h
    · exfalso
      obtain ⟨hn, θ, β, -, hθk, hsd⟩ := h
      have h1 : θ ⟨s, hsX⟩ ≠ 1 := fun h1 => hsQ (hcS ▸ (mem_cSecIn_iff_of_ker hθk hsX).mp h1)
      have h2 := (hsd.secIdx_eq_idx hLN hsX).symm.trans hsec
      have h3 := (transvections _ h1).1
      omega
  obtain ⟨hLNn, θ, β, hθ, hθk, hsd⟩ := id horth
  have hθs : (θ ⟨s, hsX⟩).IsSwap := by
    have h1 : θ ⟨s, hsX⟩ ≠ 1 := fun h1 => hsQ (hcS ▸ (mem_cSecIn_iff_of_ker hθk hsX).mp h1)
    exact (transvections _ h1).2.mp ((hsd.secIdx_eq_idx hLN hsX).symm.trans hsec)
  have hkerQ : ∀ x : ↥X, θ x = 1 → (x : G) ∈ pCoreOf 2 X := fun x hx =>
    hcS ▸ (mem_cSecIn_iff_of_ker hθk x.2).mp hx
  have hgen : ∀ K : Subgroup G, pCoreOf 2 X ≤ K → (∀ x ∈ X, x * s * x⁻¹ ∈ K) → X ≤ K :=
    fun K hQK hK => le_of_conj_swap_mem θ hθ (fun x hx => hQK (hkerQ x hx)) hsX hθs hK
  have hinvV : ∀ y ∈ X, ∀ v ∈ V, y⁻¹ * v * y ∈ V := fun y hy v hv => by
    simpa using hXVc y⁻¹ (X.inv_mem hy) v hv
  have hVN : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ N := by
    have hle := hgen (cSecIn X N V)
      (fun q hq => Subgroup.subset_closure ⟨hQX hq, fun v hv => by
        rw [hQV q hq v hv, mul_inv_cancel]
        exact N.one_mem⟩)
      (fun y hy => Subgroup.subset_closure ⟨X.mul_mem (X.mul_mem hy hsX) (X.inv_mem hy),
        fun v hv => by
          have h1 := hXN y hy _ (h4a _ (hinvV y hy v hv))
          have e : y * (s * (y⁻¹ * v * y) * s⁻¹ * (y⁻¹ * v * y)⁻¹) * y⁻¹ =
              y * s * y⁻¹ * v * (y * s * y⁻¹)⁻¹ * v⁻¹ := by group
          rwa [e] at h1⟩)
    intro x hx v hv
    exact ((mem_cSecIn_iff hXNn).mp (hle hx)).2 v hv
  have hXL' : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ = l := by
    have hle := hgen (Subgroup.centralizer (L : Set G))
      (fun q hq => Subgroup.mem_centralizer_iff.mpr fun l hl =>
        conj_eq_iff_comm.mp (hQV q hq l (hNV (hLN hl))))
      (fun y hy => Subgroup.mem_centralizer_iff.mpr fun l hl => by
        have hl' : y⁻¹ * l * y ∈ L := by simpa using hXL y⁻¹ (X.inv_mem hy) l hl
        have h1 := h4b _ hl'
        apply conj_eq_iff_comm.mp
        calc y * s * y⁻¹ * l * (y * s * y⁻¹)⁻¹ = y * (s * (y⁻¹ * l * y) * s⁻¹) * y⁻¹ := by
              group
          _ = l := by rw [h1]; group)
    intro x hx l hl
    exact conj_eq_iff_comm.mpr (Subgroup.mem_centralizer_iff.mp (hle hx) l hl)
  have hcen : ∀ u ∈ V, (∀ x ∈ X, x * u * x⁻¹ * u⁻¹ ∈ L) → ∀ x ∈ X, x * u * x⁻¹ = u := by
    intro u hu hL
    have hle := hgen (Subgroup.centralizer ({u} : Set G))
      (fun q hq => Subgroup.mem_centralizer_singleton_iff.mpr
        (conj_eq_iff_comm.mp (hQV q hq u hu)).symm)
      (fun y hy => by
        have hu' := hinvV y hy u hu
        have h1 := hXL y⁻¹ (X.inv_mem hy) _
          (hL _ (X.mul_mem (X.mul_mem hy hsX) (X.inv_mem hy)))
        have e : y⁻¹ * (y * s * y⁻¹ * u * (y * s * y⁻¹)⁻¹ * u⁻¹) * y⁻¹⁻¹ =
            s * (y⁻¹ * u * y) * s⁻¹ * (y⁻¹ * u * y)⁻¹ := by group
        rw [e] at h1
        have h2 := h4c _ hu' h1
        have h3 : (y * s * y⁻¹) * u * (y * s * y⁻¹)⁻¹ = u := by
          have e2 : (y * s * y⁻¹) * u * (y * s * y⁻¹)⁻¹ * u⁻¹ =
              y * (s * (y⁻¹ * u * y) * s⁻¹ * (y⁻¹ * u * y)⁻¹) * y⁻¹ := by group
          rw [← mul_inv_eq_one, e2, h2]
          group
        exact Subgroup.mem_centralizer_singleton_iff.mpr (conj_eq_iff_comm.mp h3).symm)
    intro x hx
    exact conj_eq_iff_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
  exact isOrthSec_of_split horth hLN hNV hVX hXVc hVN hXL' (fun x hx => hQV x (hcS ▸ hx)) hcen

end F53.Stellmacher

end CFSG.Quasithin
