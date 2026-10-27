module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Gen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3SevenCop
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3SevenFix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3SevenInv
import CFSG.Quasithin.Background.B5Sec
import CFSG.Quasithin.EmptyFaithful.F918C13
import CFSG.Quasithin.Vol2.Ch8Sec2L8211A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {U : Type} [CommGroup U] [Finite U]


private theorem s16h_e3_l3_exists_not_mem {L : Subgroup (MulAut U)} [IsSimpleGroup ↥L]
    {Z X : Subgroup U} {k : ℕ} (hZ : Z ≤ fixV L)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L ⊤ Z k)
    (hXinv : ∀ l ∈ L, ∀ x ∈ X, l x ∈ X) (hZinv : ∀ l ∈ L, ∀ z ∈ Z, l z ∈ Z)
    {γ : MulAut U} (hγL : γ ∈ L) (hγ1 : γ ≠ 1)
    {x₀ : U} (hx₀X : x₀ ∈ X) (hx₀Z : x₀ ∉ Z) :
    ∃ x ∈ X, γ x * x⁻¹ ∉ Z := by
  by_contra h
  have hγmem : γ ∈ L ⊓ centSec X Z := by
    refine Subgroup.mem_inf.mpr ⟨hγL, ?_⟩
    refine ⟨le_stabSub_of_inv hXinv hγL, ?_⟩
    intro x hx
    by_contra hx'
    exact h ⟨x, hx, hx'⟩
  have hnorm := normal_inf_centSec (L := L) hXinv hZinv
  have hne : (L ⊓ centSec X Z).subgroupOf L ≠ ⊥ := by
    intro hbot
    have hmem : (⟨γ, hγL⟩ : ↥L) ∈ (L ⊓ centSec X Z).subgroupOf L := hγmem
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hγ1 (congrArg Subtype.val hmem)
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ centSec X Z).subgroupOf L) with hbot | htop
  · exact hne hbot
  · exact hx₀Z (s16h_e3_l3_mem_of_comm_mem_sum hZ hsum (x := x₀) fun l hl => by
      have hmem : (⟨l, hl⟩ : ↥L) ∈ (L ⊓ centSec X Z).subgroupOf L := by
        rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hmem).2.2 x₀ hx₀X)

theorem s16h_L3_sum_three_seven_quotient {L : Subgroup (MulAut U)}
    (helem : ∀ u : U, u * u = 1)
    (hquasi : CFSG.Open.IsQuasisimple ↥L) (hsl3 : IsSLn ↥L 3 1)
    (hcomm : commSub ⊤ L = ⊤)
    (hsum : ∃ k : ℕ, k ≤ 3 ∧
      SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L ⊤ (fixV L) k)
    {g : MulAut U}
    (hgc : g ∈ Subgroup.centralizer (L : Set (MulAut U)))
    (hg7 : g ^ 7 = 1)
    (hgZ : ∀ z : U, z ∈ fixV L → g z = z)
    (hn : ¬ ∀ u : U, g u * u⁻¹ ∈ fixV L) :
    ∀ u : U, g u * u⁻¹ ∈ fixV L → u ∈ fixV L := by
  classical
  obtain ⟨k, hk3, hsum⟩ := hsum
  let Z : Subgroup U := fixV L
  have hsumN : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L ⊤ (fixV L) k := hsum
  obtain ⟨I, -, -, hsup, hnat⟩ := hsum
  have hgZ' : ∀ z : U, z ∈ Z → g z = z := hgZ
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hbot : (⨆ i : Fin 0, I i) = ⊥ := by simp
    rw [hbot, sup_bot_eq] at hsup
    intro u _
    rw [hsup]
    exact Subgroup.mem_top u
  · let i₀ : Fin k := ⟨0, hkpos⟩
    have hnat₀ : BinaryNaturalSL L (I i₀) Z 3 1 := hnat i₀
    have hcoord : L3Coord L (I i₀) Z := BinaryNaturalSL.toL3Coord hnat₀
    have hpsl : IsPSL 3 2 1 ↥L := s16h_e3_l3_isPSL_of_coord hcoord
    haveI hsimple : IsSimpleGroup ↥L :=
      (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hpsl).2
    obtain ⟨D⟩ := hcoord
    let γ : MulAut U := D.rho L3.x12
    have hγL : γ ∈ L := D.rho_mem L3.x12
    have hx12sq : L3.x12 ^ 2 = 1 := by rw [pow_two]; exact L3.x12_invol.1
    have hγ2 : γ ^ 2 = 1 := by
      show (D.rho L3.x12) ^ 2 = 1
      rw [← map_pow, hx12sq, map_one]
    have hγ1 : γ ≠ 1 := by
      intro h
      have hx : L3.x12 = 1 := D.rho_injective (by
        show D.rho L3.x12 = D.rho 1
        rw [map_one]
        exact h)
      exact L3.x12_invol.2 hx
    have hgl : ∀ l ∈ L, g * l = l * g :=
      fun l hl => (Subgroup.mem_centralizer_iff.mp hgc l hl).symm
    let φ : U →* U :=
      { toFun := fun u => g u * u⁻¹
        map_one' := by simp
        map_mul' := fun u v => by
          simp only [map_mul, mul_inv_rev]
          ac_rfl }
    let A : Subgroup U := Z.comap φ
    let B : Subgroup U := commSub ⊤ (Subgroup.zpowers g) ⊔ Z
    have hZinv : ∀ l ∈ L, ∀ z ∈ Z, l z ∈ Z := by
      intro l hl z hz
      have hz' : z ∈ fixV L := hz
      rw [mem_fixV] at hz'
      show l z ∈ Z
      rw [hz' l hl]
      exact hz
    have hZA : Z ≤ A := by
      intro z hz
      rw [Subgroup.mem_comap]
      change g z * z⁻¹ ∈ Z
      rw [hgZ' z hz, mul_inv_cancel]
      exact Z.one_mem
    have hAinv : ∀ l ∈ L, ∀ a ∈ A, l a ∈ A := by
      intro l hl a ha
      rw [Subgroup.mem_comap] at ha ⊢
      change g a * a⁻¹ ∈ Z at ha
      change g (l a) * (l a)⁻¹ ∈ Z
      have h1 : g (l a) = l (g a) := by
        rw [← MulAut.mul_apply, hgl l hl, MulAut.mul_apply]
      rw [h1]
      have h2 : l (g a) * (l a)⁻¹ = l (g a * a⁻¹) := by rw [map_mul, map_inv]
      rw [h2]
      exact hZinv l hl _ ha
    have hcomm_inv : ∀ l ∈ L, ∀ c ∈ commSub ⊤ (Subgroup.zpowers g),
        l c ∈ commSub ⊤ (Subgroup.zpowers g) := by
      refine CFSG.Quasithin.B1.commSub_invariant_of_commute ?_
        (fun b _ m _ => Subgroup.mem_top m)
      intro y hy b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcomm_bg : Commute g b := (Subgroup.mem_centralizer_iff.mp hgc b hb).symm
      exact (hcomm_bg.zpow_left n).eq
    have hcomm_self : ∀ x ∈ Subgroup.zpowers g, ∀ c ∈ commSub ⊤ (Subgroup.zpowers g),
        x c ∈ commSub ⊤ (Subgroup.zpowers g) := by
      refine CFSG.Quasithin.B1.commSub_invariant_of_commute ?_
        (fun b _ m _ => Subgroup.mem_top m)
      intro y hy b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self (a := g) m n).eq
    have hBinv : ∀ l ∈ L, ∀ b ∈ B, l b ∈ B := by
      intro l hl b hb
      rw [Subgroup.mem_sup] at hb ⊢
      obtain ⟨c, hc, z, hz, rfl⟩ := hb
      exact ⟨l c, hcomm_inv l hl c hc, l z, hZinv l hl z hz, (map_mul l c z).symm⟩
    have hAB : A ⊓ B ≤ Z := by
      intro u hu
      obtain ⟨huA, huB⟩ := Subgroup.mem_inf.mp hu
      rw [Subgroup.mem_comap] at huA
      change g u * u⁻¹ ∈ Z at huA
      exact s16h_e3_l3_seven_inf_le (W := U) (fun w => by rw [pow_two]; exact helem w) hg7
        (fun z hz => hgZ' z hz) huB huA
    intro u₀ hu₀
    by_contra hu₀Z
    have hu₀A : u₀ ∈ A := by
      rw [Subgroup.mem_comap]
      change g u₀ * u₀⁻¹ ∈ Z
      exact hu₀
    obtain ⟨u₁, hu₁⟩ : ∃ u₁, g u₁ * u₁⁻¹ ∉ Z := not_forall.mp hn
    let b₀ : U := g u₁ * u₁⁻¹
    have hb₀B : b₀ ∈ B :=
      Subgroup.mem_sup.mpr ⟨b₀, Subgroup.subset_closure
        ⟨g, Subgroup.mem_zpowers g, u₁, Subgroup.mem_top u₁, rfl⟩, 1, Z.one_mem,
        mul_one b₀⟩
    have hb₀Z : b₀ ∉ Z := hu₁
    obtain ⟨x_A, hx_AX, hx_AZ⟩ :=
      s16h_e3_l3_exists_not_mem (U := U) (L := L) (Z := Z) (X := A) (k := k)
        (le_of_eq rfl) hsumN hAinv hZinv hγL hγ1 hu₀A hu₀Z
    obtain ⟨x_B, hx_BX, hx_BZ⟩ :=
      s16h_e3_l3_exists_not_mem (U := U) (L := L) (Z := Z) (X := B) (k := k)
        (le_of_eq rfl) hsumN hBinv hZinv hγL hγ1 hb₀B hb₀Z
    let Y_A : Subgroup U := commSub A (Subgroup.zpowers γ) ⊔ Z
    let Y_B : Subgroup U := commSub B (Subgroup.zpowers γ) ⊔ Z
    have hYAne : Z ≠ Y_A := by
      intro h
      have hmem : γ x_A * x_A⁻¹ ∈ Y_A :=
        Subgroup.mem_sup.mpr ⟨γ x_A * x_A⁻¹, Subgroup.subset_closure
          ⟨γ, Subgroup.mem_zpowers γ, x_A, hx_AX, rfl⟩, 1, Z.one_mem,
          mul_one (γ x_A * x_A⁻¹)⟩
      rw [← h] at hmem
      exact hx_AZ hmem
    have hYBne : Z ≠ Y_B := by
      intro h
      have hmem : γ x_B * x_B⁻¹ ∈ Y_B :=
        Subgroup.mem_sup.mpr ⟨γ x_B * x_B⁻¹, Subgroup.subset_closure
          ⟨γ, Subgroup.mem_zpowers γ, x_B, hx_BX, rfl⟩, 1, Z.one_mem,
          mul_one (γ x_B * x_B⁻¹)⟩
      rw [← h] at hmem
      exact hx_BZ hmem
    have hrkA : rk ↥Z + 1 ≤ rk ↥Y_A := by
      have hle : Z ≤ Y_A := le_sup_right
      have hlt : rk ↥Z < rk ↥Y_A := by
        by_contra h
        exact hYAne (eq_of_le_of_rk_le (fun w => by rw [pow_two]; exact helem w) hle
          (not_lt.mp h))
      omega
    have hYA_le_A : Y_A ≤ A :=
      sup_le (commSub_le_of_invariant (fun x hx y hy =>
        hAinv x (Subgroup.zpowers_le.mpr hγL hx) y hy)) hZA
    have hYB_le_B : Y_B ≤ B :=
      sup_le (commSub_le_of_invariant (fun x hx y hy =>
        hBinv x (Subgroup.zpowers_le.mpr hγL hx) y hy)) le_sup_right
    have hYinf : Y_A ⊓ Y_B = Z := by
      refine le_antisymm ?_ ?_
      · exact (inf_le_inf hYA_le_A hYB_le_B).trans hAB
      · exact le_inf le_sup_right le_sup_right
    have hYsup_le : Y_A ⊔ Y_B ≤ commSub ⊤ (Subgroup.zpowers γ) ⊔ Z := by
      refine sup_le ?_ ?_
      · exact sup_le ((commSub_mono le_top le_rfl).trans le_sup_left) le_sup_right
      · exact sup_le ((commSub_mono le_top le_rfl).trans le_sup_left) le_sup_right
    have hrk_sup_le : rk ↥(Y_A ⊔ Y_B) ≤ rk ↥Z + k := by
      have h1 := s16h_e3_l3_rk_commSub_invol_le (W := U)
        (fun w => by rw [pow_two]; exact helem w) (L := L) (Z := Z) (k := k)
        (le_of_eq rfl) hsumN hγL hγ2
      exact (rk_mono hYsup_le).trans h1
    have hrkYB : rk ↥Y_B ≤ rk ↥Z + 2 := by
      have h := rk_sup_add_rk_inf Y_A Y_B
      rw [hYinf] at h
      omega
    have hcardSec : Nat.card (Sec Y_B Z) ≤ 4 := by
      have hquot : Nat.card ↥Y_B = Nat.card (Sec Y_B Z) * Nat.card ↥Z := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf Y_B)
        have hcardSub : Nat.card ↥(Z.subgroupOf Y_B) = Nat.card ↥Z :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
        rw [hcardSub] at h
        exact h
      have hcardYB : Nat.card ↥Y_B = 2 ^ rk ↥Y_B :=
        card_eq_two_pow (fun w => by rw [pow_two]; exact helem w) Y_B
      have hcardZ : Nat.card ↥Z = 2 ^ rk ↥Z :=
        card_eq_two_pow (fun w => by rw [pow_two]; exact helem w) Z
      have hle : Nat.card ↥Y_B ≤ Nat.card ↥Z * 4 := by
        rw [hcardYB, hcardZ]
        calc 2 ^ rk ↥Y_B ≤ 2 ^ (rk ↥Z + 2) := Nat.pow_le_pow_right (by norm_num) hrkYB
          _ = 2 ^ rk ↥Z * 4 := by rw [pow_add]; norm_num
      have hmain : Nat.card (Sec Y_B Z) * Nat.card ↥Z ≤ 4 * Nat.card ↥Z := by
        rw [← hquot]
        calc Nat.card ↥Y_B ≤ Nat.card ↥Z * 4 := hle
          _ = 4 * Nat.card ↥Z := by ring
      exact Nat.le_of_mul_le_mul_right hmain (card_subgroup_pos Z)
    have hnotdvd : ¬ 7 ∣ Nat.card (MulAut (Sec Y_B Z)) := by
      intro hdvd
      have h1 : Nat.card (MulAut (Sec Y_B Z)) ∣ Nat.card (Equiv.Perm (Sec Y_B Z)) := by
        have hinj : Function.Injective (MulAut.toPerm (Sec Y_B Z)) := fun a b h => by
          ext x
          exact congrArg (fun p : Equiv.Perm (Sec Y_B Z) => p x) h
        have hcard : Nat.card (MulAut (Sec Y_B Z)) =
            Nat.card ↥((MulAut.toPerm (Sec Y_B Z)).range) :=
          Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
        rw [hcard]
        exact Subgroup.card_subgroup_dvd_card _
      have h2 : Nat.card (Equiv.Perm (Sec Y_B Z)) =
          Nat.factorial (Nat.card (Sec Y_B Z)) := Nat.card_perm
      have h3 : Nat.factorial (Nat.card (Sec Y_B Z)) ∣ 24 := by
        have h := Nat.factorial_dvd_factorial hcardSec
        rw [show (4 : ℕ).factorial = 24 from by decide] at h
        exact h
      have h4 : Nat.card (Equiv.Perm (Sec Y_B Z)) ∣ 24 := by
        rw [h2]
        exact h3
      exact absurd (hdvd.trans (h1.trans h4)) (by decide : ¬ 7 ∣ 24)
    have hstabComm : g ∈ stabSub (commSub ⊤ (Subgroup.zpowers g)) :=
      Subgroup.zpowers_le.mp (le_stabSub_of_inv hcomm_self)
    have hgZstab : g ∈ stabSub Z := centSub_le_stabSub Z (mem_centSub.mpr hgZ')
    have hgstabB : g ∈ stabSub B := CFSG.Quasithin.H13.L8211.sup_mem_stabSub hstabComm hgZstab
    have hgnorm : g ∈ Subgroup.normalizer
        ((Subgroup.zpowers γ : Subgroup (MulAut U)) : Set (MulAut U)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      congr 1
      show g * γ * g⁻¹ = γ
      rw [hgl γ hγL]
      group
    have hgstabComm : g ∈ stabSub (commSub B (Subgroup.zpowers γ)) :=
      CFSG.Quasithin.StabLat.mem_stabSub_commSub hgstabB hgnorm
    have hgYstab : g ∈ stabSub Y_B := CFSG.Quasithin.H13.L8211.sup_mem_stabSub hgstabComm hgZstab
    have hYstab : Subgroup.zpowers g ≤ stabSub Y_B := Subgroup.zpowers_le.mpr hgYstab
    have hZstab : Subgroup.zpowers g ≤ stabSub Z := Subgroup.zpowers_le.mpr hgZstab
    let gbar : MulAut (Sec Y_B Z) :=
      CFSG.Quasithin.B5.secHom (Subgroup.zpowers g) hYstab hZstab
        ⟨g, Subgroup.mem_zpowers g⟩
    have hg7' : gbar ^ 7 = 1 := by
      show (CFSG.Quasithin.B5.secHom (Subgroup.zpowers g) hYstab hZstab
        ⟨g, Subgroup.mem_zpowers g⟩) ^ 7 = 1
      rw [← map_pow]
      have hpow : (⟨g, Subgroup.mem_zpowers g⟩ : ↥(Subgroup.zpowers g)) ^ 7 = 1 := by
        apply Subtype.ext
        simpa using hg7
      rw [hpow, map_one]
    have horder : orderOf gbar = 1 := by
      have hdvd7 : orderOf gbar ∣ 7 := orderOf_dvd_of_pow_eq_one hg7'
      have hdvdAut : orderOf gbar ∣ Nat.card (MulAut (Sec Y_B Z)) := orderOf_dvd_natCard gbar
      rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd7 with h | h
      · exact h
      · exact absurd (h ▸ hdvdAut) hnotdvd
    have hgY : ∀ y ∈ Y_B, g y * y⁻¹ ∈ Z := by
      intro y hy
      have hker : (⟨g, Subgroup.mem_zpowers g⟩ : ↥(Subgroup.zpowers g)) ∈
          (CFSG.Quasithin.B5.secHom (Subgroup.zpowers g) hYstab hZstab).ker := by
        rw [MonoidHom.mem_ker]
        show gbar = 1
        exact orderOf_eq_one_iff.mp horder
      have hcent := (CFSG.Quasithin.B5.mem_ker_secHom (X := Subgroup.zpowers g)
        (hXW := hYstab) (hXU := hZstab) ⟨g, Subgroup.mem_zpowers g⟩).mp hker
      exact hcent.2 y hy
    have hcommBγ_le_Z : commSub B (Subgroup.zpowers γ) ≤ Z := by
      rw [commSub, Subgroup.closure_le]
      rintro c ⟨x, hx, w, hw, rfl⟩
      have hcB : x w * w⁻¹ ∈ B :=
        commSub_le_of_invariant (fun y hy z hz =>
          hBinv y (Subgroup.zpowers_le.mpr hγL hy) z hz)
          (Subgroup.subset_closure ⟨x, hx, w, hw, rfl⟩)
      have hcYB : x w * w⁻¹ ∈ Y_B :=
        Subgroup.mem_sup.mpr ⟨x w * w⁻¹,
          Subgroup.subset_closure ⟨x, hx, w, hw, rfl⟩, 1, Z.one_mem, mul_one (x w * w⁻¹)⟩
      have hgmem : g (x w * w⁻¹) * (x w * w⁻¹)⁻¹ ∈ Z := hgY _ hcYB
      have hcA : x w * w⁻¹ ∈ A := by
        rw [Subgroup.mem_comap]
        change g (x w * w⁻¹) * (x w * w⁻¹)⁻¹ ∈ Z
        exact hgmem
      exact hAB (Subgroup.mem_inf.mpr ⟨hcA, hcB⟩)
    have hYB_eq_Z : Y_B = Z := le_antisymm (sup_le hcommBγ_le_Z le_rfl) le_sup_right
    exact hYBne hYB_eq_Z.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
