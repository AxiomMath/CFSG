module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCFix3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MSetting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MMembers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16c13bc_perm3_comm :
    ∀ κ c : Equiv.Perm (Fin 3), c ^ 3 = 1 → c ≠ 1 → κ * c = c * κ → κ ^ 3 = 1 := by
  decide

private theorem s16c13bc_perm3_conj :
    ∀ κ c : Equiv.Perm (Fin 3), c ^ 3 = 1 → κ * c * κ⁻¹ = c ∨ κ * c * κ⁻¹ = c⁻¹ := by
  decide

private theorem s16c13bc_mem_stabSub_of_map_eq {T : Type*} [CommGroup T] {W : Subgroup T}
    {e : MulAut T} (h : W.map e.toMonoidHom = W) : e ∈ stabSub W := by
  intro u
  constructor
  · intro hu
    have hu' : e u ∈ W.map e.toMonoidHom := by rw [h]; exact hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
    have : w = u := e.injective hwu
    rw [← this]
    exact hw
  · intro hu
    have hu' : e u ∈ W.map e.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rwa [h] at hu'

theorem s16c13bc_case168_2 (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV)
    (hcomm : ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ = ⊥)
    (h2 : Case168_2 D ⊥ V hV L) : Insp1613U D V := by
  have h : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hp3 : (3 : ℕ) ∈ D.sig := by
    rw [h2.2.2]
    exact Set.mem_singleton 3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨L₀, J₀, J₁, F, hLX, hKX, hKL, hK, hdir, hle, hE₀, hE₁, hfam⟩ := s16c2m_setting D hc h2
  obtain ⟨G3, π, -, -, ⟨a, ha⟩, -, hact, -, -, -, -, hcommπ⟩ :=
    s16c2m_members F hKX hKL hK hE₀ hE₁
  have hKL0 : ∀ k ∈ kBar D.M ⊥ V hV L, ∀ l ∈ L₀, k * l = l * k := by
    intro k hk l hl
    have hkcent : k ∈ Subgroup.centralizer (L₀ : Set (MulAut (Vtil ⊥ V hV))) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hdir.1) hk
    exact (Subgroup.mem_centralizer_iff.1 hkcent l hl).symm
  obtain ⟨e⟩ := hK
  have hKcard : Nat.card ↥(kBar D.M ⊥ V hV L) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(kBar D.M ⊥ V hV L)) 3
    (by rw [hKcard]; norm_num)
  have hzo : orderOf (z : MulAut (Vtil ⊥ V hV)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hz
  have hz3 : z ^ 3 = 1 := hz ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    omega
  have hec3 : (e z) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hec1 : e z ≠ 1 := fun h1 => hz1 (e.injective (by rw [h1, map_one]))
  set Z : Subgroup (MulAut (Vtil ⊥ V hV)) := Subgroup.zpowers (z : MulAut (Vtil ⊥ V hV)) with hZ
  have hZM : Z ≤ Mbar D.M ⊥ V hV := Subgroup.zpowers_le.2 (hKX z.2)
  have hZK : Z ≤ kBar D.M ⊥ V hV L := Subgroup.zpowers_le.2 z.2
  have hZcard : Nat.card Z = 3 := by rw [hZ, Nat.card_zpowers, hzo]
  have hZn : ∀ m ∈ Mbar D.M ⊥ V hV, ∀ x ∈ Z, m * x * m⁻¹ ∈ Z := by
    have hkey : ∀ m ∈ Mbar D.M ⊥ V hV, m * (z : MulAut (Vtil ⊥ V hV)) * m⁻¹ ∈ Z := by
      intro m hm
      have hmsup : m ∈ kBar D.M ⊥ V hV L ⊔ L₀ := by
        rw [hdir.2.2]
        exact hm
      obtain ⟨κ, hκ, ℓ, hℓ, rfl⟩ := s16c2m_exists_mul_of_mem_sup hKL0 hmsup
      have hℓz : ℓ * (z : MulAut (Vtil ⊥ V hV)) = (z : MulAut (Vtil ⊥ V hV)) * ℓ :=
        (hKL0 z z.2 ℓ hℓ).symm
      have h1 : κ * ℓ * (z : MulAut (Vtil ⊥ V hV)) * (κ * ℓ)⁻¹ =
          κ * (z : MulAut (Vtil ⊥ V hV)) * κ⁻¹ := by
        calc κ * ℓ * (z : MulAut (Vtil ⊥ V hV)) * (κ * ℓ)⁻¹
            = κ * (ℓ * (z : MulAut (Vtil ⊥ V hV)) * ℓ⁻¹) * κ⁻¹ := by group
          _ = κ * (z : MulAut (Vtil ⊥ V hV)) * κ⁻¹ := by rw [hℓz]; group
      rw [h1]
      have h2' := s16c13bc_perm3_conj (e ⟨κ, hκ⟩) (e z) hec3
      rcases h2' with h3 | h3
      · have h4 : (⟨κ, hκ⟩ : ↥(kBar D.M ⊥ V hV L)) * z * (⟨κ, hκ⟩ : ↥(kBar D.M ⊥ V hV L))⁻¹ = z :=
          e.injective (by simpa using h3)
        have h5 := congrArg (fun y : ↥(kBar D.M ⊥ V hV L) => (y : MulAut (Vtil ⊥ V hV))) h4
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h5
        rw [h5]
        exact Subgroup.mem_zpowers _
      · have h4 : (⟨κ, hκ⟩ : ↥(kBar D.M ⊥ V hV L)) * z * (⟨κ, hκ⟩ : ↥(kBar D.M ⊥ V hV L))⁻¹ =
            z⁻¹ := e.injective (by simpa using h3)
        have h5 := congrArg (fun y : ↥(kBar D.M ⊥ V hV L) => (y : MulAut (Vtil ⊥ V hV))) h4
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h5
        rw [h5]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    intro m hm x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hkey m hm) i
  have hZO : Z ≤ oddBar D.M ⊥ V hV :=
    s16c13bc_le_oddBar hV hZM hZn (hZcard ▸ ⟨1, rfl⟩)
  have hWT : E3.wClos V D.k D.T ≤ D.T := E3.wClos_le_of_forall fun A hA => hA.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(barSub ⊥ V hV (E3.wClos V D.k D.T)) :=
    s15_LP_isPGroup_barSub hV (D.sylowM.isPGroup.to_le hWT)
  have hWM : barSub ⊥ V hV (E3.wClos V D.k D.T) ≤ Mbar D.M ⊥ V hV :=
    barSub_mono ⊥ V hV (hWT.trans D.sylowM.le)
  have hst : barSub ⊥ V hV (E3.wClos V D.k D.T) ≤ stabSub J₀ := by
    intro w hw
    have hwM : w ∈ Mbar D.M ⊥ V hV := hWM hw
    have hzw : (z : MulAut (Vtil ⊥ V hV)) * w = w * (z : MulAut (Vtil ⊥ V hV)) := by
      have h1 : ⁅(z : MulAut (Vtil ⊥ V hV)), w⁆ ∈
          ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ :=
        Subgroup.commutator_mem_commutator (hZO (Subgroup.mem_zpowers _)) hw
      rw [hcomm, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.1 hP2) ⟨w, hw⟩
    have hwpow : w ^ 2 ^ b = 1 := by
      have h1 : orderOf w = 2 ^ b :=
        (Subgroup.orderOf_coe (⟨w, hw⟩ : ↥(barSub ⊥ V hV (E3.wClos V D.k D.T)))).trans hb
      rw [← h1]
      exact pow_orderOf_eq_one w
    have hwsup : w ∈ kBar D.M ⊥ V hV L ⊔ L₀ := by
      rw [hdir.2.2]
      exact hwM
    obtain ⟨κ, hκ, ℓ, hℓ, hκℓ⟩ := s16c2m_exists_mul_of_mem_sup hKL0 hwsup
    have hκℓc : κ * ℓ = ℓ * κ := hKL0 κ hκ ℓ hℓ
    have hℓz : ℓ * (z : MulAut (Vtil ⊥ V hV)) = (z : MulAut (Vtil ⊥ V hV)) * ℓ :=
      (hKL0 z z.2 ℓ hℓ).symm
    have hκz : κ * (z : MulAut (Vtil ⊥ V hV)) = (z : MulAut (Vtil ⊥ V hV)) * κ := by
      have h1 : (z : MulAut (Vtil ⊥ V hV)) * κ * ℓ = κ * (z : MulAut (Vtil ⊥ V hV)) * ℓ := by
        calc (z : MulAut (Vtil ⊥ V hV)) * κ * ℓ = (z : MulAut (Vtil ⊥ V hV)) * w := by
              rw [← hκℓ, mul_assoc]
          _ = w * (z : MulAut (Vtil ⊥ V hV)) := hzw
          _ = κ * (ℓ * (z : MulAut (Vtil ⊥ V hV))) := by rw [← hκℓ, mul_assoc]
          _ = κ * ((z : MulAut (Vtil ⊥ V hV)) * ℓ) := by rw [hℓz]
          _ = κ * (z : MulAut (Vtil ⊥ V hV)) * ℓ := by rw [mul_assoc]
      exact (mul_right_cancel h1).symm
    have hκ3 : κ ^ 3 = 1 := by
      have h1 := s16c13bc_perm3_comm (e ⟨κ, hκ⟩) (e z) hec3 hec1 (by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hκz)
      have h2' : (⟨κ, hκ⟩ : ↥(kBar D.M ⊥ V hV L)) ^ 3 = 1 := by
        apply e.injective
        rw [map_pow, h1, map_one]
      exact congrArg (fun y : ↥(kBar D.M ⊥ V hV L) => (y : MulAut (Vtil ⊥ V hV))) h2'
    have hκ2 : κ ^ 2 ^ b = 1 := by
      have h1 : w ^ 2 ^ b = κ ^ 2 ^ b * ℓ ^ 2 ^ b := by
        rw [← hκℓ]
        exact (Commute.mul_pow (show Commute κ ℓ from hκℓc) _)
      have h2' : κ ^ 2 ^ b = (ℓ ^ 2 ^ b)⁻¹ := by
        rw [hwpow] at h1
        exact eq_inv_of_mul_eq_one_left h1.symm
      have h3 : κ ^ 2 ^ b ∈ kBar D.M ⊥ V hV L ⊓ L₀ :=
        ⟨Subgroup.pow_mem _ hκ _, by rw [h2']; exact L₀.inv_mem (Subgroup.pow_mem _ hℓ _)⟩
      rw [hdir.2.1, Subgroup.mem_bot] at h3
      exact h3
    have hκ1 : κ = 1 := by
      have hcop : Nat.gcd 3 (2 ^ b) = 1 :=
        Nat.Coprime.pow_right b (by norm_num : Nat.Coprime 3 2)
      have h1 := pow_gcd_eq_one.2 ⟨hκ3, hκ2⟩
      rwa [hcop, pow_one] at h1
    have hwL : w ∈ L₀ := by
      rw [← hκℓ, hκ1, one_mul]
      exact hℓ
    have hπ : π ⟨w, hwM⟩ = 1 :=
      hcommπ ⟨w, hwM⟩ (fun k hk => (hKL0 k hk w hwL).symm)
    have hmap : J₀.map w.toMonoidHom = J₀ := by
      have h1 := hact ⟨w, hwM⟩ a
      rw [hπ, Equiv.Perm.one_apply, ha] at h1
      exact h1
    exact s16c13bc_mem_stabSub_of_map_eq hmap
  have hJ0 : J₀ ≠ ⊥ := by
    have h1 := F.irr₀.2.1
    rw [F.fix, inf_bot_eq] at h1
    exact h1.ne'
  obtain ⟨n, hnJ, hn1, hnfix⟩ := s16c13bc_exists_fixed_in D h hJ0 hst
  have hψ : ∃ ψ ∈ lBar ⊥ V hV L, orderOf ψ = 3 ∧ ψ n = n := by
    rcases hfam with ⟨k, hk5, -, -, -, -, hN₀, -⟩ | ⟨m, hm3, -, -, -, hN₀, -, -⟩ |
        ⟨-, -, -, hN₀, -⟩ | ⟨-, -, -, hN₀, -⟩ | ⟨-, -, -, hN₀, -⟩
    · exact s16c13bc_fix3_alt hk5 hN₀ n hnJ hn1
    · exact s16c13bc_fix3_sl hm3 hN₀ n hnJ hn1
    · exact s16c13bc_fix3_sp (by norm_num) hN₀ n hnJ hn1
    · exact s16c13bc_fix3_omegaMinus (by norm_num) le_rfl hN₀ n hnJ hn1
    · exact s16c13bc_fix3_omegaMinus (by norm_num) le_rfl hN₀ n hnJ hn1
  obtain ⟨ψ, hψL, hψo, hψn⟩ := hψ
  have hψ1 : ψ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hψo
    omega
  have hψZ : ψ ∉ Z := by
    intro hψZ
    have hψ' : ψ ∈ kBar D.M ⊥ V hV L ⊓ L₀ := ⟨hZK hψZ, hle hψL⟩
    rw [hdir.2.1, Subgroup.mem_bot] at hψ'
    exact hψ1 hψ'
  exact s16c13bc_insp_of_normal_prime D h hcomm hp3 hZM hZcard hZn hn1 hnfix (hLX hψL) hψo hψZ hψn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
