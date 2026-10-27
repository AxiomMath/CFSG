module

public import CFSG.Quasithin.H13.GoldschmidtU43EA6Gam
public import CFSG.Quasithin.H13.GoldschmidtU43EA6Cen
public import CFSG.Quasithin.H13.GoldschmidtU43EA6Syl1
public import CFSG.Quasithin.H13.GoldschmidtU43EUas

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem card_sylow_three_of_card_360 {K : Type} [Group K] [Finite K] (h : Nat.card K = 360)
    (P : Sylow 3 K) : Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp P.isPGroup'
  have h1 : Nat.card P * (P : Subgroup K).index = Nat.card K := Subgroup.card_mul_index _
  have h2 : ¬ 3 ∣ (P : Subgroup K).index := P.not_dvd_index
  rw [h, hn] at h1
  have hlt : n < 3 := by
    by_contra hge
    push Not at hge
    have : 3 ^ 3 ∣ 360 := by
      rw [← h1]
      exact Dvd.dvd.mul_right (pow_dvd_pow 3 hge) _
    omega
  interval_cases n
  · exfalso; apply h2; omega
  · exfalso; apply h2; omega
  · rw [hn]; norm_num

theorem A6_pow_nine : ∀ g : alternatingGroup (Fin 6), g ^ 9 = 1 → g ^ 3 = 1 := by
  decide +kernel

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

theorem card_Nbar_of_iso (e : S.Nbar ≃* alternatingGroup (Fin 6)) : Nat.card S.Nbar = 360 :=
  (Nat.card_congr e.toEquiv).trans card_A6

theorem pow_three_of_mem_sylow (e : S.Nbar ≃* alternatingGroup (Fin 6)) (P : Sylow 3 S.Nbar)
    {g : S.Nbar} (hg : g ∈ P) : g ^ 3 = 1 := by
  have h9 : Nat.card P = 9 := card_sylow_three_of_card_360 (S.card_Nbar_of_iso e) P
  have h1 : orderOf (⟨g, hg⟩ : P) ∣ Nat.card P := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, h9] at h1
  have h2 : g ^ 9 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
  have h3 : (e g) ^ 9 = 1 := by rw [← map_pow, h2, map_one]
  have h4 := A6_pow_nine _ h3
  apply e.injective
  rw [map_pow, h4, map_one]

variable (P : Sylow 3 S.Nbar)

theorem card_centralizer_Msyl (e : S.Nbar ≃* alternatingGroup (Fin 6)) {x : G}
    (hx : x ∈ S.preimageNbar (P : Subgroup S.Nbar)) (hxM : x ∉ S.Mg) :
    Nat.card {m : ↥S.Mg // x * m = m * x} ≤ 9 := by
  obtain ⟨r⟩ := S.nonempty_Rho
  obtain ⟨hxN, hxP⟩ := S.mem_preimageNbar.mp hx
  have h3 : S.piN ⟨x, hxN⟩ ^ 3 = 1 := S.pow_three_of_mem_sylow e P hxP
  have h1 : S.piN ⟨x, hxN⟩ ≠ 1 := fun h =>
    hxM ((QuotientGroup.eq_one_iff (⟨x, hxN⟩ : ↥S.Ng)).mp h)
  have hX : S.chiBar r (S.piN ⟨x, hxN⟩) ∈ Lset := S.chiBar_mem_Lset r e _
  have hX3 : S.chiBar r (S.piN ⟨x, hxN⟩) ^ 3 = 1 := by
    rw [← S.chiBar_pow r, h3, S.chiBar_one r]
  have hX1 : S.chiBar r (S.piN ⟨x, hxN⟩) ≠ 1 := fun h => h1 ((S.chiBar_eq_one_iff r _).mp h)
  have h := card_fix_Lset_le hX hX3 hX1
  rw [S.chiBar_piN r] at h
  exact S.card_centralizer_le r ⟨x, hxN⟩ h

theorem card_centralizer2_Msyl (e : S.Nbar ≃* alternatingGroup (Fin 6)) {x y : G}
    (hx : x ∈ S.preimageNbar (P : Subgroup S.Nbar)) (hy : y ∈ S.preimageNbar (P : Subgroup S.Nbar))
    (hxM : x ∉ S.Mg) (hyM : y ∉ S.Mg) (hxy : x⁻¹ * y ∉ S.Mg) (hxxy : (x * x)⁻¹ * y ∉ S.Mg) :
    Nat.card {m : ↥S.Mg // x * m = m * x ∧ y * m = m * y} ≤ 3 := by
  obtain ⟨r⟩ := S.nonempty_Rho
  obtain ⟨hxN, hxP⟩ := S.mem_preimageNbar.mp hx
  obtain ⟨hyN, hyP⟩ := S.mem_preimageNbar.mp hy
  set n₁ : ↥S.Ng := ⟨x, hxN⟩ with hn₁
  set n₂ : ↥S.Ng := ⟨y, hyN⟩ with hn₂
  have h9 : Nat.card P = 9 := card_sylow_three_of_card_360 (S.card_Nbar_of_iso e) P
  have hcomm : S.piN n₁ * S.piN n₂ = S.piN n₂ * S.piN n₁ := by
    have hc : IsMulCommutative ↥(P : Subgroup S.Nbar) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [h9]; norm_num)
    have := hc.is_comm.comm (⟨S.piN n₁, hxP⟩ : ↥(P : Subgroup S.Nbar)) ⟨S.piN n₂, hyP⟩
    exact congrArg Subtype.val this
  have h31 : S.piN n₁ ^ 3 = 1 := S.pow_three_of_mem_sylow e P hxP
  have h32 : S.piN n₂ ^ 3 = 1 := S.pow_three_of_mem_sylow e P hyP
  have hne1 : S.piN n₁ ≠ 1 := fun h => hxM ((QuotientGroup.eq_one_iff n₁).mp h)
  have hne2 : S.piN n₂ ≠ 1 := fun h => hyM ((QuotientGroup.eq_one_iff n₂).mp h)
  have hne12 : S.piN n₂ ≠ S.piN n₁ := by
    intro h
    apply hxy
    have h' : S.piN (n₁⁻¹ * n₂) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (n₁⁻¹ * n₂)).mp h'
  have hne12' : S.piN n₂ ≠ S.piN n₁ * S.piN n₁ := by
    intro h
    apply hxxy
    have h' : S.piN ((n₁ * n₁)⁻¹ * n₂) = 1 := by
      rw [map_mul, map_inv, map_mul, h, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff ((n₁ * n₁)⁻¹ * n₂)).mp h'
  have hX : S.chiBar r (S.piN n₁) ∈ Lset := S.chiBar_mem_Lset r e _
  have hY : S.chiBar r (S.piN n₂) ∈ Lset := S.chiBar_mem_Lset r e _
  have hX3 : S.chiBar r (S.piN n₁) ^ 3 = 1 := by rw [← S.chiBar_pow r, h31, S.chiBar_one r]
  have hY3 : S.chiBar r (S.piN n₂) ^ 3 = 1 := by rw [← S.chiBar_pow r, h32, S.chiBar_one r]
  have hXY : S.chiBar r (S.piN n₁) * S.chiBar r (S.piN n₂) =
      S.chiBar r (S.piN n₂) * S.chiBar r (S.piN n₁) := by
    rw [← S.chiBar_mul r, ← S.chiBar_mul r, hcomm]
  have hX1 : S.chiBar r (S.piN n₁) ≠ 1 := fun h => hne1 ((S.chiBar_eq_one_iff r _).mp h)
  have hY1 : S.chiBar r (S.piN n₂) ≠ 1 := fun h => hne2 ((S.chiBar_eq_one_iff r _).mp h)
  have hYX : S.chiBar r (S.piN n₂) ≠ S.chiBar r (S.piN n₁) := fun h =>
    hne12 (S.chiBar_injective r h)
  have hYX2 : S.chiBar r (S.piN n₂) ≠ S.chiBar r (S.piN n₁) * S.chiBar r (S.piN n₁) := by
    intro h
    apply hne12'
    apply S.chiBar_injective r
    rw [S.chiBar_mul r]
    exact h
  have h := card_fix2_Lset_le hX hY hX3 hY3 hXY hX1 hY1 hYX hYX2
  rw [S.chiBar_piN r, S.chiBar_piN r] at h
  exact S.card_centralizer2_le r n₁ n₂ h

theorem unique_abelian_Msyl (e : S.Nbar ≃* alternatingGroup (Fin 6)) {M' : Subgroup G}
    (hM'S : M' ≤ S.preimageNbar (P : Subgroup S.Nbar)) (hab : ∀ a ∈ M', ∀ b ∈ M', a * b = b * a)
    (hcard : Nat.card M' = 81) : M' = S.Mg := by
  have h9 : Nat.card P = 9 := card_sylow_three_of_card_360 (S.card_Nbar_of_iso e) P
  refine u43_unique_abelian_81 (S.Mg_le_preimageNbar _) ?_ S.card_Mg_eq_81 (n := 9)
    (Or.inr rfl) (by rw [S.card_preimageNbar, h9]) ?_ ?_ hM'S hab hcard
  · intro s hs m hm
    obtain ⟨hsN, -⟩ := S.mem_preimageNbar.mp hs
    exact (S.mem_Ng.mp hsN m).mp hm
  · intro x hx hxM
    exact S.card_centralizer_Msyl P e hx hxM
  · intro x hx hxM y hy hyM hxy hxxy
    exact S.card_centralizer2_Msyl P e hx hy hxM hyM hxy hxxy

end JWSetup

end CFSG.Quasithin.H13.U43
