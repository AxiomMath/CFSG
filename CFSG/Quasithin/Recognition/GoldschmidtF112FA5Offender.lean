module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5ZSub
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5TransvG
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Alpha
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Beta

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace FA5

set_option linter.unusedSectionVars false

namespace Frame

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X Z : Subgroup G} (F : Frame L1 L2 S D X)
include F

theorem exists_ne_one_D : ∃ d ∈ D, d ≠ 1 := by
  by_contra h
  have hbot : D = ⊥ :=
    (Subgroup.eq_bot_iff_forall D).mpr fun d hd => by_contra fun h' => h ⟨d, hd, h'⟩
  have hc : Nat.card D = 1 := by
    rw [hbot]
    simp
  rw [F.D_card] at hc
  omega

omit F in
theorem relIndex_ne_zero' {H K : Subgroup G} : H.relIndex K ≠ 0 := Subgroup.index_ne_zero_of_finite

variable (hZ : ZData L1 L2 S Z)
include hZ

theorem Z1_le_Q2 : Z1 L1 L2 S Z ≤ Q2 L1 L2 S := by
  by_contra hnot
  obtain ⟨a, haZ, haQ⟩ : ∃ a ∈ Z1 L1 L2 S Z, a ∉ Q2 L1 L2 S := by
    by_contra h'
    exact hnot fun a ha => by_contra fun h => h' ⟨a, ha, h⟩
  obtain ⟨φ, hφs, hφ⟩ := F.exists_phi
  have haQ1 : a ∈ Q1 L1 L2 S := F.Z1_le_Q1 hZ haZ
  have haS : a ∈ S := F.Q1_le_S haQ1
  obtain ⟨l, q, hq, hal, hlS, hl1, hl2⟩ := F.exists_involution hφ haS haQ
  have hLV : L2 ≤ Subgroup.normalizer (Z2 L1 L2 S Z : Set G) :=
    (le_sup_left : L2 ≤ P2 L1 L2 S).trans (le_normalizer_conjClosure Z _)
  have hker : ∀ n : ↥L2, φ n = 1 → (n : G) ∈ Subgroup.centralizer (Z2 L1 L2 S Z : Set G) := by
    intro n hn
    have h1 : (n : G) ∈ Q2 L1 L2 S := F.pCore_L2_le_Q2 ((hφ n).mp hn)
    exact Subgroup.mem_centralizer_iff.mpr fun v hv => F.Z2_comm hZ v hv _ h1
  have hidx : (Z2 L1 L2 S Z ⊓ Subgroup.centralizer {(l : G)}).relIndex (Z2 L1 L2 S Z) ≤ 2 := by
    have hsub : Z2 L1 L2 S Z ⊓ Q1 L1 L2 S ≤ Z2 L1 L2 S Z ⊓ Subgroup.centralizer {(l : G)} := by
      rintro z ⟨hzZ2, hzQ1⟩
      refine ⟨hzZ2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hl : (l : G) = a * q⁻¹ := by
        rw [hal]
        group
      have h1 : a * z = z * a := F.Z1_comm hZ a haZ z hzQ1
      have h2 : z * q = q * z := F.Z2_comm hZ z hzZ2 q hq
      have h3 : q⁻¹ * z = z * q⁻¹ := by
        calc q⁻¹ * z = q⁻¹ * (z * q) * q⁻¹ := by group
          _ = q⁻¹ * (q * z) * q⁻¹ := by rw [h2]
          _ = z * q⁻¹ := by group
      rw [hl]
      calc a * q⁻¹ * z = a * (q⁻¹ * z) := by group
        _ = a * (z * q⁻¹) := by rw [h3]
        _ = (a * z) * q⁻¹ := by group
        _ = (z * a) * q⁻¹ := by rw [h1]
        _ = z * (a * q⁻¹) := by group
    have h2 : (Z2 L1 L2 S Z ⊓ Q1 L1 L2 S).relIndex (Z2 L1 L2 S Z) ≤ 2 :=
      F.relIndex_inf_Q1_le_two (fun e he => F.Q2_le_S (F.Z2_le_Q2 hZ he))
        (fun e he => by rw [F.Z2_sq hZ e he]; exact (Q1 L1 L2 S).one_mem)
    exact (Subgroup.relIndex_le_of_le_left hsub relIndex_ne_zero').trans h2
  have hL2cent : L2 ≤ Subgroup.centralizer (Z2 L1 L2 S Z : Set G) :=
    centralizes_of_alt5_transvection (F.Z2_sq hZ) hLV φ hφs hker hl1 hl2 hidx
  have hDZ : ∀ d ∈ D, ∀ z ∈ Z, d * z * d⁻¹ = z := by
    intro d hd z hz
    have hzZ2 : z ∈ Z2 L1 L2 S Z := le_conjClosure Z _ hz
    have h := Subgroup.mem_centralizer_iff.mp (hL2cent (F.D_le hd)) z hzZ2
    calc d * z * d⁻¹ = z * d * d⁻¹ := by rw [← h]
      _ = z := by group
  obtain ⟨d, hdD, hd1⟩ := F.exists_ne_one_D
  refine hnot (conjClosure_le fun p hp z hz => ?_)
  obtain ⟨x, hx, z', hz', hpz⟩ := F.conj_Z_eq hZ hp hz
  rw [hpz]
  have hzQ1 : z' ∈ Q1 L1 L2 S := F.Z_le_Q1 hZ hz'
  have hy : x * z' * x⁻¹ ∈ Q1 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (P1_le_normalizer_Q1 L1 L2 S (F.mem_P1_of_mem_X hx)) z').mp hzQ1
  have hyS : x * z' * x⁻¹ ∈ S := F.Q1_le_S hy
  have hdx : d * x = x * d := ((Subgroup.mem_centralizer_iff.mp (F.D_cent hdD)) x hx).symm
  have hdy : d * (x * z' * x⁻¹) * d⁻¹ = x * z' * x⁻¹ := by
    calc d * (x * z' * x⁻¹) * d⁻¹ = (d * x) * z' * (d * x)⁻¹ := by group
      _ = (x * d) * z' * (x * d)⁻¹ := by rw [hdx]
      _ = x * (d * z' * d⁻¹) * x⁻¹ := by group
      _ = x * z' * x⁻¹ := by rw [hDZ d hdD z' hz']
  refine F.fpf hdD hd1 hyS ?_
  rw [hdy]
  simp

end Frame

end FA5

end CFSG.Quasithin
