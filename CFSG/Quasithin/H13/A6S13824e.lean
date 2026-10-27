module

public import CFSG.Quasithin.H13.A6S13824d
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7B

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace SecHyp

variable {H K X W : Subgroup G} (hs : S.SecHyp H K X W) [IsMulCommutative ↥X]
include hs

omit [Finite G] hs [IsMulCommutative ↥X] in
theorem relIndex_K7 {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    (K ⊓ pCoreOf 2 H).relIndex K = 2520 := by
  have hker : α.ker = (K ⊓ pCoreOf 2 H).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  have h1 := Subgroup.index_ker α
  rw [MonoidHom.range_eq_top.2 hαs, Subgroup.card_top, hker] at h1
  rw [Subgroup.relIndex, h1, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem relIndex_le_index7
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {ρ : ↥H →* Perm (Fin 7)} (hρk : ∀ k : ↥K, ρ (Subgroup.inclusion hs.hKH k) = α k)
    (hρ1 : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) {F : Subgroup G} (hFH : F ≤ H)
    (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H) :
    (F ⊓ pCoreOf 2 H).relIndex F ≤ (centralizerMod W X F).relIndex X := by
  classical
  by_cases hF : F ≤ pCoreOf 2 H
  · rw [Subgroup.relIndex_eq_one.2 (le_inf le_rfl hF)]
    exact Nat.pos_of_ne_zero (relIndex_ne_zero' _ _)
  obtain ⟨r, hr2, hbound, hcard⟩ := hs.card_le_index_pow7 hirr hαs hρk hρ1 hFH hF hFc hFs
  set A := autSec (autOn F X) ⊤ (W.subgroupOf X) with hAdef
  have hA : Nat.card A = (F ⊓ pCoreOf 2 H).relIndex F := hs.card_autSec hFH
  have hi := hs.index_fixV_le hFH
  have h16 := hs.card_ge_sixteen7 hαs hαk
  by_contra hlt
  push Not at hlt
  have hia : (fixV A).index < (F ⊓ pCoreOf 2 H).relIndex F := lt_of_le_of_lt hi hlt
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) := fun y =>
    ⟨1, by rw [pow_one]; exact hs.sec_pow_two y⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE2
  have hidvd : (fixV A).index ∣ 2 ^ n := hn ▸ Subgroup.index_dvd_card _
  obtain ⟨ι, -, hι⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hidvd
  have hAel := hs.isElemAbelian2_autSec hFH hFc hFs
  have hA2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by
    rw [pow_one]
    simpa [pow_two] using hAel.2 _ x.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hA2
  rw [hA] at hm
  rw [hm, hι] at hia
  rw [hm] at hbound
  rw [hn, hι] at hcard
  have hιm : ι < m := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 hia
  have hnι : n ≤ ι * r := by
    rw [← pow_mul] at hcard
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 hcard
  have hmr : m * r ≤ 6 := by
    rw [← pow_mul] at hbound
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 hbound
  have hn4 : 4 ≤ n := by
    rw [hn] at h16
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 (by simpa using h16)
  have hr6 : r ≤ 6 := by nlinarith
  have key : n = 4 ∧ m = 3 := by
    interval_cases r <;> omega
  obtain ⟨rfl, rfl⟩ := key
  have hK2520 : Nat.card (autSec (autOn K X) ⊤ (W.subgroupOf X)) = 2520 := by
    rw [hs.card_autSec hs.hKH, relIndex_K7 hαs hαk]
  have hnorm := L246.C123.normalizer_eq_of_card_2520 hs.sec_pow_two (by rw [hn]; norm_num)
    hK2520
  have hρF : ∀ f (hf : f ∈ F), (ρ ⟨f, hFH hf⟩ : Perm (Fin 7)) ∈ alternatingGroup (Fin 7) := by
    intro f hf
    have hmemN : hs.act ⟨f, hFH hf⟩ ∈
        Subgroup.normalizer (autSec (autOn K X) ⊤ (W.subgroupOf X) : Set _) := by
      rw [Subgroup.mem_normalizer_iff]
      intro ψ
      constructor
      · intro hψ
        obtain ⟨κ, hκ, rfl⟩ := (hs.mem_autSec_iff hs.hKH).1 hψ
        refine (hs.mem_autSec_iff hs.hKH).2 ⟨⟨f, hFH hf⟩ * κ * ⟨f, hFH hf⟩⁻¹, ?_, by
          simp only [map_mul, map_inv]⟩
        exact (Subgroup.mem_normalizer_iff.mp (hs.hKn (hFH hf)) κ).mp hκ
      · intro hψ
        obtain ⟨κ, hκ, hκe⟩ := (hs.mem_autSec_iff hs.hKH).1 hψ
        refine (hs.mem_autSec_iff hs.hKH).2 ⟨⟨f, hFH hf⟩⁻¹ * κ * ⟨f, hFH hf⟩, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hs.hKn (H.inv_mem (hFH hf))) κ).mp hκ
          simpa [mul_assoc] using this
        · rw [map_mul, map_mul, map_inv, hκe]
          group
    rw [hnorm] at hmemN
    obtain ⟨κ, hκ, hκe⟩ := (hs.mem_autSec_iff hs.hKH).1 hmemN
    have hq : ((κ⁻¹ * ⟨f, hFH hf⟩ : ↥H) : G) ∈ pCoreOf 2 H := by
      rw [← hs.act_eq_one_iff, map_mul, map_inv, hκe, inv_mul_cancel]
    have hρe : ρ ⟨f, hFH hf⟩ = ρ κ := by
      have := (hρ1 _).2 hq
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    have := hρk ⟨κ, hκ⟩
    rw [show Subgroup.inclusion hs.hKH ⟨(κ : G), hκ⟩ = κ from Subtype.ext rfl] at this
    rw [hρe, this]
    exact (α ⟨κ, hκ⟩).2
  have hBA : (F.subgroupOf H).map ρ ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨f, hf, rfl⟩
    exact hρF f (Subgroup.mem_subgroupOf.1 hf)
  have hB2 : ∀ b ∈ (F.subgroupOf H).map ρ, b * b = 1 := by
    rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, hρ1]
    simpa using hFs f (Subgroup.mem_subgroupOf.1 hf)
  have hdvd := A7F.card_dvd_four hBA hB2
  rw [card_map_rho hρ1 hFH, hm] at hdvd
  exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)

theorem relIndex_le_two_of_transv7 {α : ↥K →* alternatingGroup (Fin 7)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {ρ : ↥H →* Perm (Fin 7)} (hρk : ∀ k : ↥K, ρ (Subgroup.inclusion hs.hKH k) = α k)
    (hρ1 : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) {F : Subgroup G} (hFH : F ≤ H)
    {z : G} (hz : ∀ f ∈ F, ∀ x ∈ X, f * x * f⁻¹ * x⁻¹ ∈ W ∨ f * x * f⁻¹ * x⁻¹ * z⁻¹ ∈ W) :
    (F ⊓ pCoreOf 2 H).relIndex F ≤ 2 := by
  classical
  let φ : ↥F →* ℤˣ := Perm.sign.comp (ρ.comp (Subgroup.inclusion hFH))
  have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb => by
    have := mul_comm (⟨a, ha⟩ : ↥X) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hker : φ.ker = (F ⊓ pCoreOf 2 H).subgroupOf F := by
    ext f
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hf
      refine ⟨f.2, ?_⟩
      have hA7 : ρ (Subgroup.inclusion hFH f) ∈ alternatingGroup (Fin 7) := hf
      obtain ⟨κ, hκ⟩ := hαs ⟨_, hA7⟩
      have hρe : ρ (Subgroup.inclusion hs.hKH κ) = ρ (Subgroup.inclusion hFH f) := by
        rw [hρk, hκ]
      have hq : (((Subgroup.inclusion hs.hKH κ)⁻¹ * Subgroup.inclusion hFH f : ↥H) : G) ∈
          pCoreOf 2 H := by
        rw [← hρ1, map_mul, map_inv, hρe, inv_mul_cancel]
      have hact := hs.act_eq_of_inv_mul_mem hq
      by_contra hfQ
      have hne : hs.act (Subgroup.inclusion hFH f) ≠ 1 := fun h =>
        hfQ ((hs.act_eq_one_iff _).1 h)
      obtain ⟨x₀, hx₀, hfx₀⟩ : ∃ x ∈ X, (f : G) * x * (f : G)⁻¹ * x⁻¹ ∉ W := by
        by_contra hall
        push Not at hall
        exact hfQ (S.le_pCoreOf_of_triv hs.hS hs.hH hs.hKH hs.hKn hs.hHK hs.hsimp hs.hXH hs.hHX
          hs.hHW hs.hQ hs.hKnt (hFH f.2) hall)
      have hfX : ∀ x ∈ X, (f : G) * x * (f : G)⁻¹ ∈ X := fun x hx =>
        (Subgroup.mem_normalizer_iff.mp (hs.hHX (hFH f.2)) x).mp hx
      have hz₀ := (hz f f.2 x₀ hx₀).resolve_left hfx₀
      have hzX : z ∈ X := by
        have e : z = ((f : G) * x₀ * (f : G)⁻¹ * x₀⁻¹ * z⁻¹)⁻¹ *
            ((f : G) * x₀ * (f : G)⁻¹ * x₀⁻¹) := by group
        rw [e]
        exact X.mul_mem (X.inv_mem (hs.hWX hz₀)) (X.mul_mem (hfX x₀ hx₀) (X.inv_mem hx₀))
      set zb := InternalSec.secMk (W.subgroupOf X) ⟨z, hzX⟩ with hzb
      have htv : IsTransvectionWith (hs.act (Subgroup.inclusion hFH f)) zb := by
        refine ⟨fun h => ?_, fun y => ?_⟩
        · rw [hzb, A6Mod.secMk_eq_one_iff] at h
          apply hfx₀
          have e : (f : G) * x₀ * (f : G)⁻¹ * x₀⁻¹ =
              ((f : G) * x₀ * (f : G)⁻¹ * x₀⁻¹ * z⁻¹) * z := by group
          rw [e]
          exact W.mul_mem hz₀ h
        · obtain ⟨x, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf X) y
          rw [act_secMk]
          rcases hz f f.2 x x.2 with h | h
          · left
            rw [← mul_inv_eq_one, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff]
            simpa only [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv,
              Subgroup.coe_inclusion] using h
          · right
            rw [hzb, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul,
              A6Mod.secMk_eq_one_iff]
            simp only [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv,
              Subgroup.coe_inclusion]
            have e : (f : G) * x * (f : G)⁻¹ * ((x : G) * z)⁻¹ =
                (f : G) * x * (f : G)⁻¹ * (x : G)⁻¹ * z⁻¹ := by
              rw [mul_inv_rev, hXc _ (X.inv_mem hzX) _ (X.inv_mem x.2)]
              group
            rw [e]
            exact h
      rw [← hact] at htv hne
      exact hs.not_transv7 hαs hαk κ htv hne
    · rintro ⟨-, hq⟩
      show Perm.sign (ρ (Subgroup.inclusion hFH f)) = 1
      rw [(hρ1 _).2 hq, map_one]
  have h1 : (F ⊓ pCoreOf 2 H).relIndex F = φ.ker.index := by rw [hker]; rfl
  rw [h1, Subgroup.index_ker]
  calc Nat.card φ.range ≤ Nat.card ℤˣ := Subgroup.card_le_card_group _
    _ = 2 := by rw [Nat.card_eq_fintype_card]; rfl

end SecHyp

end Setting4

end CFSG.Quasithin.H13.A6
