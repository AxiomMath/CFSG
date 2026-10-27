module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofLift
public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
public import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie9

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof

open Subgroup CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

namespace L3

theorem modNine_of_dvd {π : Bool} {q : ℕ} (hq : ModThree π q)
    (h : 81 ∣ q ^ 3 * (q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1)) : ModNine π q := by
  cases π
  · change q % 3 = 2 at hq
    change q % 9 = 8
    change 81 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) at h
    obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 2 := ⟨q / 3, by omega⟩
    have h2 : (3 * b + 2) ^ 2 - 1 = 3 * (3 * b + 1) * (b + 1) := Nat.sub_eq_of_eq_add (by ring)
    have e : (3 * b + 2) ^ 3 * (3 * (3 * b + 1) * (b + 1)) * ((3 * b + 2) ^ 3 + 1) =
        27 * ((b + 1) ^ 2 * ((3 * b + 2) ^ 3 * (3 * b + 1) * (3 * b ^ 2 + 3 * b + 1))) := by
      ring
    rw [h2, e, show (81 : ℕ) = 27 * 3 by norm_num, Nat.mul_dvd_mul_iff_left (by norm_num)] at h
    have hU : ¬ 3 ∣ (3 * b + 2) ^ 3 * (3 * b + 1) * (3 * b ^ 2 + 3 * b + 1) := by
      intro h3
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
      · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
        · have := Nat.prime_three.dvd_of_dvd_pow h3
          omega
        · omega
      · omega
    have h1 : 3 ∣ (b + 1) ^ 2 := ((Nat.Prime.dvd_mul Nat.prime_three).mp h).resolve_right hU
    have := Nat.prime_three.dvd_of_dvd_pow h1
    omega
  · change q % 3 = 1 at hq
    change q % 9 = 1
    change 81 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) at h
    obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 1 := ⟨q / 3, by omega⟩
    have h2 : (3 * b + 1) ^ 2 - 1 = 3 * b * (3 * b + 2) := Nat.sub_eq_of_eq_add (by ring)
    have h3 : (3 * b + 1) ^ 3 - 1 = 9 * b * (3 * b ^ 2 + 3 * b + 1) :=
      Nat.sub_eq_of_eq_add (by ring)
    have e : (3 * b + 1) ^ 3 * (3 * b * (3 * b + 2)) * (9 * b * (3 * b ^ 2 + 3 * b + 1)) =
        27 * (b ^ 2 * ((3 * b + 1) ^ 3 * (3 * b + 2) * (3 * b ^ 2 + 3 * b + 1))) := by ring
    rw [h2, h3, e, show (81 : ℕ) = 27 * 3 by norm_num, Nat.mul_dvd_mul_iff_left (by norm_num)]
      at h
    have hU : ¬ 3 ∣ (3 * b + 1) ^ 3 * (3 * b + 2) * (3 * b ^ 2 + 3 * b + 1) := by
      intro h4
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h4 with h4 | h4
      · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h4 with h4 | h4
        · have := Nat.prime_three.dvd_of_dvd_pow h4
          omega
        · omega
      · omega
    have h1 : 3 ∣ b ^ 2 := ((Nat.Prime.dvd_mul Nat.prime_three).mp h).resolve_right hU
    have := Nat.prime_three.dvd_of_dvd_pow h1
    omega

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem realPair_projImage (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : 9 ∣ qSubPi π (p ^ f)) : RealPair (projImage (slPi π 3 (p ^ f) K)) := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  obtain ⟨l, hlT, hl9, -, -, hl3⟩ := Sec19.Step1915WProof.exists_orderNine hK h9
  have hτ : ((l : K) ^ 3) ^ 3 = 1 := by
    rw [← pow_mul, ← Units.val_pow_eq_pow_val, hl9, Units.val_one]
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  have hs : 1 + (l : K) ^ 3 + ((l : K) ^ 3) ^ 2 = 0 := one_add_tau_add_sq hτ hl3
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set S := slPi π 3 (p ^ f) K with hS
  have hc : cycThree ∈ S := cycThree_mem_slPi hπ
  have hw : diagUnits l l (l ^ 7) ∈ S :=
    Sec19.Step1915WProof.diagUnits_mem_slPi hK hlT hlT (pow_mem hlT 7)
      (by rw [← pow_two, ← pow_add]; exact hl9)
  have hF : fourierGL h3 hs ∈ S := fourierGL_mem_slPi hK hq hτ h3 hs
  set x : projImage S := projOf S ⟨cycThree, hc⟩ with hx
  set t : projImage S := projOf S ⟨diagUnits l l (l ^ 7), hw⟩ with ht
  set F : projImage S := projOf S ⟨fourierGL h3 hs, hF⟩ with hFdef
  have hdmem : ProjGenLinGroup.mk (diagTau hτ) ∈ projImage S :=
    ⟨diagTau hτ, diagTau_mem_slPi hπ (fun h => by subst h; exact hq) hτ, rfl⟩
  set d : projImage S := ⟨_, hdmem⟩ with hd
  have hxc : (x : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk cycThree := rfl
  have htc : (t : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagUnits l l (l ^ 7)) := rfl
  have hFc : (F : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (fourierGL h3 hs) := rfl
  have hdc : (d : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ) := rfl
  have hx3 : x ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hxc, ← map_pow, cycThree_pow_three, map_one, Subgroup.coe_one])
  have hcomm : x * t * x⁻¹ * t⁻¹ = d := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv, hxc, htc, hdc]
    exact Sec19.Step1915WProof.mk_commutator_cyc_w hl9 hτ)
  have hd1 : d ≠ 1 := fun h => by
    have h' := congrArg Subtype.val h
    rw [hdc, Subgroup.coe_one] at h'
    exact Sec19.Step1915WProof.mk_diagTau_ne_one hτ hl3 h'
  have hd3 : d ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hdc, ← map_pow, diagTau_pow_three, map_one, Subgroup.coe_one])
  have hdt : d * t = t * d := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hdc, htc, ← map_mul, ← map_mul,
      Sec19.Step1915WProof.diagTau_comm_diagUnits])
  have hdx : d * x = x * d := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hdc, hxc]
    exact mk_diagTau_cycThree hτ)
  have ht9 : t ^ 3 ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, htc, ← map_pow, show (3 : ℕ) ^ 2 = 9 by norm_num,
      Sec19.Step1915WProof.diagUnits_pow', hl9, ← pow_mul,
      show 7 * 9 = 9 * 7 by norm_num, pow_mul, hl9, one_pow,
      Sec19.Step1915WProof.diagUnits_one', map_one, Subgroup.coe_one])
  have hFx : F * x * F⁻¹ = d := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hFc, hxc, hdc]
    exact mk_fourier_cycThree hτ h3 hs)
  have hFd : F * d * F⁻¹ = x⁻¹ := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hFc, hdc, hxc]
    exact mk_fourier_diagTau hτ h3 hs)
  refine ⟨x, t, F ^ 2, hx3, ?_, fun h => hd1 ?_, ?_⟩
  · calc F ^ 2 * x * (F ^ 2)⁻¹ = F * (F * x * F⁻¹) * F⁻¹ := by rw [pow_two]; group
      _ = x⁻¹ := by rw [hFx, hFd]
  · rw [← hcomm, h]
    group
  · exact isPGroup_closure_heis (k := 2) hx3 ht9 (by rw [hcomm]; exact hd3)
      (by rw [hcomm]; exact hdt) (by rw [hcomm]; exact hdx)

end L3

theorem exists_noncentral_L3 {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hL : IsoLThreePi (X ⧸ center X) p e) (h27 : 27 ∣ Nat.card (X ⧸ center X))
    (S : Sylow 3 X) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ t ∈ (S : Subgroup X), s * t ≠ t * s := by
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hL
  have hcard := Sec13.card_projImage_slPi_mul_three hK hq
  have h81 : 81 ∣ (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) *
      cond π ((p ^ e) ^ 3 - 1) ((p ^ e) ^ 3 + 1) := by
    rw [← hcard, ← Nat.card_congr φ.toEquiv, show (81 : ℕ) = 27 * 3 by norm_num]
    exact Nat.mul_dvd_mul_right h27 3
  have h9 : 9 ∣ qSubPi π (p ^ e) :=
    (modNine_iff (Nat.one_le_pow _ _ hK.prime.pos)).mp (L3.modNine_of_dvd hq h81)
  exact exists_noncentral_of_realPair (RealPair.of_mulEquiv (H := X ⧸ center X)
    (H' := projImage (slPi π 3 (p ^ e) K)) φ (L3.realPair_projImage hK hq h9)) S

end CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof
