module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22B
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem22

variable {G : Type} [Group G] [Finite G]

theorem card_eq_of_frattini (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hyp : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Concl12_2_20 T L V n)
    (hpre : Pre12_2_21 T L V H P U I h p) (hUO : U ≤ pCoreOf 2 H) (hΦ : frattini ↥P = ⊥) :
    Nat.card P = p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVO := Lem21.not_le_pCoreOf_of_pre hpre
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, hHPT, hPΦ, hhP, hhM, -, -, -, -, -, -, -, hidx,
    -, -⟩ := hpre
  have : Fact p.Prime := ⟨hp⟩
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  have hPM : P ⊓ Subgroup.normalizer (L : Set G) = ⊥ := by
    rw [hPΦ, hΦ, Subgroup.map_bot]
  have : Fact (IsPGroup p ↥P) := ⟨hPp⟩
  have hE : CFSG.IsElementaryAbelian p ↥P := CFSG.frattini_eq_bot_iff_isElementaryAbelian.mp hΦ
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPe : ∀ x ∈ P, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (A := P) x hx
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hmin := Lem7.minParabolic h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hO2 : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hHO : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hUV : U ⊓ V = pCoreOf 2 H ⊓ V :=
    ((Lem21.eq_or_le_of_relIndex_eq_two (inf_le_inf_right V hUO) inf_le_right hidx).resolve_right
      fun hle => hVO (hle.trans inf_le_left)).symm
  have hidx' : (V ⊓ pCoreOf 2 H).relIndex V = 2 := by rw [inf_comm, ← hUV]; exact hidx
  obtain ⟨v, hvV, hvO⟩ := IsConcreteLE.not_le_iff_exists.mp hVO
  have hv2 := hV2 v hvV
  obtain ⟨m, hmv, -, hminv⟩ := exists_inv_conj h331 hyp hHs hsol hp hp2 hPp hPH hPi hHPT hPM
    hPc hVT hTV hidx' hP1 hvV hv2 hvO
  by_contra hne
  have hcard : p ^ 2 ≤ Nat.card P := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hP1 (Subgroup.eq_bot_of_card_eq P hk)
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hne (by rw [hk, pow_one])
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  set R := pCoreOf 2 H with hR
  set A := R ⊓ Subgroup.centralizer (R : Set G) with hA
  have hA2 : IsPGroup 2 ↥A := hO2.to_le inf_le_left
  have hAp : ¬ p ∣ Nat.card A := by
    obtain ⟨k, hk⟩ := hA2.exists_card_eq
    rw [hk]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hHA : H ≤ Subgroup.normalizer (A : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHO hg, B6.le_normalizer_centralizer hHO hg⟩
  have hvH : v ∈ H := hTH (hVT hvV)
  have hcV : ∀ w ∈ A, w * (m * w * m⁻¹)⁻¹ ∈ V := by
    intro w hwA
    obtain ⟨r, hr, rfl⟩ : ∃ r ∈ R, r * v = m := ⟨m * v⁻¹, hmv, by group⟩
    have hvw : v * w * v⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hHA hvH) w).mp hwA
    have hrc : r * (v * w * v⁻¹) * r⁻¹ = v * w * v⁻¹ := by
      have := (Subgroup.mem_centralizer_iff.mp hvw.2) r hr
      rw [this, mul_inv_cancel_right]
    have e : w * (r * v * w * (r * v)⁻¹)⁻¹ = w * v * w⁻¹ * v⁻¹ := by
      have e1 : r * v * w * (r * v)⁻¹ = r * (v * w * v⁻¹) * r⁻¹ := by group
      rw [e1, hrc]
      group
    rw [e]
    have hwV : w * v * w⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hTV (hQT hwA.1)) v).mp hvV
    exact V.mul_mem hwV (V.inv_mem hvV)
  have hVR : V ⊓ R ≠ ⊥ := by
    intro h0
    have h1 := hidx'
    rw [h0, Subgroup.relIndex_bot_left] at h1
    obtain ⟨hn, hcardV, -⟩ := hC
    rw [hcardV] at h1
    rcases hn with rfl | rfl | rfl <;> norm_num at h1
  obtain ⟨z, hzVR, hz1, hzc⟩ := exists_ne_one_mem_centralizer hO2 inf_le_right
    (fun r hr => Subgroup.inf_normalizer_le_normalizer_inf ⟨hTV (hQT hr), hHO (hTH (hQT hr))⟩)
    hVR
  exact false_of_card_le hp hp2 hPc hPe hcard hPM hAp (fun x hx => hHA (hPH hx)) hminv
    (fun w hwA hw1 => hNE _ (hcV w hwA) hw1) ⟨hzVR.2, hzc⟩ (hNE z hzVR.1 hz1)

end Lem22

end CFSG.Quasithin.H13
