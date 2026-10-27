module

public import CFSG.Quasithin.Vol2.Ch10SecDBasicZ
public import CFSG.Quasithin.Vol2.Ch1Local

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}



theorem L3.exists_order_three_fix :
    ∀ c : CFSG.Quasithin.L3.Vec, c ≠ 0 → ∃ γ : CFSG.Quasithin.L3.Γ,
      CFSG.Quasithin.L3.act γ c = c ∧ γ ^ 3 = 1 ∧ γ ≠ 1 := by
  decide +kernel

theorem exists_odd_mem_centralizer (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {v : G}
    (hv : v ∈ fsuUL T L I) (hv1 : v ≠ 1) :
    ∃ l ∈ L, Odd (orderOf l) ∧ l * v * l⁻¹ = v ∧
      l ∉ Subgroup.centralizer (fsuUL T L I : Set G) := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  have hβinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (D.ker_β u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  set u : ↥(⊤ : Subgroup ↥(fsuUL T L I)) := ⟨⟨v, hv⟩, trivial⟩
  have hc0 : Multiplicative.toAdd (D.β u) ≠ 0 := by
    intro h0
    apply hv1
    have h1 : D.β u = 1 := Multiplicative.toAdd.injective (by simpa using h0)
    have h2 := hβinj (h1.trans (map_one D.β).symm)
    exact congrArg (fun w : ↥(⊤ : Subgroup ↥(fsuUL T L I)) => ((w : ↥(fsuUL T L I)) : G)) h2
  obtain ⟨γ, hγc, hγ3, hγ1⟩ := L3.exists_order_three_fix _ hc0
  obtain ⟨⟨l, hlN⟩, hlL, hlσ⟩ := D.rho_mem γ
  have hlL' : l ∈ L := Subgroup.mem_subgroupOf.mp hlL
  have hfix : D.rho γ ⟨v, hv⟩ = ⟨v, hv⟩ := by
    have h2 := D.β_rho γ (⟨v, hv⟩ : ↥(fsuUL T L I)) trivial trivial
    rw [show (⟨(⟨v, hv⟩ : ↥(fsuUL T L I)), trivial⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) = u from rfl,
      hγc] at h2
    have h3 : (⟨D.rho γ ⟨v, hv⟩, trivial⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) = u :=
      hβinj (by rw [h2]; simp)
    exact congrArg Subtype.val h3
  have hlv : l * v * l⁻¹ = v := by
    have := congrArg Subtype.val hfix
    rw [← hlσ] at this
    exact this
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
  refine ⟨l ^ 2 ^ k, L.pow_mem hlL' _, ?_, ?_, ?_⟩
  · rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hkm, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
    exact hm
  · have key : ∀ n : ℕ, l ^ n * v * (l ^ n)⁻¹ = v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc l ^ (n + 1) * v * (l ^ (n + 1))⁻¹ = l ^ n * (l * v * l⁻¹) * (l ^ n)⁻¹ := by group
          _ = v := by rw [hlv, ih]
    exact key _
  · intro hC
    have hlkN : l ^ 2 ^ k ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
      (Subgroup.normalizer _).pow_mem hlN _
    have h1 := (conjAct_eq_one_iff ⟨l ^ 2 ^ k, hlkN⟩).mpr hC
    have h2 : conjAct (fsuUL T L I) ⟨l ^ 2 ^ k, hlkN⟩ = D.rho (γ ^ 2 ^ k) := by
      have e : (⟨l ^ 2 ^ k, hlkN⟩ : Subgroup.normalizer (fsuUL T L I : Set G)) =
          ⟨l, hlN⟩ ^ 2 ^ k := Subtype.ext (by simp)
      rw [e, map_pow, hlσ, map_pow]
    rw [h2] at h1
    have h3 : γ ^ 2 ^ k = 1 := D.rho_injective (h1.trans (map_one _).symm)
    have h4 : orderOf γ ∣ 3 := orderOf_dvd_of_pow_eq_one hγ3
    have h5 : orderOf γ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h3
    have h6 : orderOf γ ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h4 h5
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at h6
    exact hγ1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h6))




theorem conjugate_le_centralizer_V1 (h : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate L t ≤ Subgroup.centralizer (fsuUL T L I : Set G) := by
  obtain ⟨_, -, -, hall, -⟩ := h.three
  exact Subgroup.le_centralizer_iff.mp (hall t ht htn).2.2

theorem V2_le_centralizer_L (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ Subgroup.centralizer (L : Set G) := by
  intro x hx
  have hx' : x ∈ CFSG.conjugate ⁅fsuVM T L I, L⁆ t := by
    rw [SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]
    exact hx
  rw [SecA.mem_conjugate_iff] at hx'
  obtain ⟨_, -, -, hall, -⟩ := h.three
  exact mem_centralizer_L_of_conj h37 h38 h ht htn ((hall t ht htn).2.2 hx')

theorem pCoreOf_XzT_le_T1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) : pCoreOf 2 (Xz T L (v₁ * v₂) ⊔ T) ≤ T1 T L := by
  intro s hs
  have hT : IsSylowTwoOf T (Xz T L (v₁ * v₂) ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right
  have hsT : s ∈ T := hT.pCoreOf_le hs
  refine ⟨hsT, ?_⟩
  by_contra hsn
  obtain ⟨ht, htn, hv1, hv11, hv2, -⟩ := hd
  obtain ⟨l, hlL, hlo, hlv, hlC⟩ := exists_odd_mem_centralizer h3 hc hv1.1 hv11
  have hlv2 : l * v₂ = v₂ * l :=
    (Subgroup.mem_centralizer_iff.mp (V2_le_centralizer_L h37 h38 h ht htn hv2.1)) l hlL
  have hlz : l ∈ Subgroup.centralizer ({v₁ * v₂} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hlv1 : l * v₁ = v₁ * l := by
      calc l * v₁ = l * v₁ * l⁻¹ * l := by group
        _ = v₁ * l := by rw [hlv]
    calc l * (v₁ * v₂) = v₁ * (l * v₂) := by rw [← mul_assoc, hlv1, mul_assoc]
      _ = v₁ * v₂ * l := by rw [hlv2, mul_assoc]
  have hlX : l ∈ Xz T L (v₁ * v₂) :=
    mem_oTwoUpper_of_odd ⟨SecA.le_fsuL0 T L hlL, hlz⟩ hlo
  have hlXT : l ∈ Xz T L (v₁ * v₂) ⊔ T := Subgroup.mem_sup_left hlX
  have hy : l * s * l⁻¹ * s⁻¹ ∈ pCoreOf 2 (Xz T L (v₁ * v₂) ⊔ T) := by
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hlXT
    have h1 : l * s * l⁻¹ ∈ pCoreOf 2 (Xz T L (v₁ * v₂) ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp hN s).mp hs
    exact (pCoreOf 2 _).mul_mem h1 ((pCoreOf 2 _).inv_mem hs)
  have hsl : s * l⁻¹ * s⁻¹ ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
    have hsn' : s⁻¹ ∉ Subgroup.normalizer (L : Set G) := by
      intro h'
      apply hsn
      have := (Subgroup.normalizer (L : Set G)).inv_mem h'
      rwa [inv_inv] at this
    have hconj := SecA.conjugate_eq_of_not_mem h37 h38 h ht htn (T.inv_mem hsT) hsn'
    refine conjugate_le_centralizer_V1 h ht htn ?_
    rw [← hconj, SecA.mem_conjugate_iff]
    simpa [mul_assoc] using L.inv_mem hlL
  have hlN : l ∈ Subgroup.normalizer (fsuUL T L I : Set G) := L_le_normalizer_V1 hlL
  have hslN : s * l⁻¹ * s⁻¹ ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
    Subgroup.centralizer_le_normalizer _ hsl
  have hyN : l * s * l⁻¹ * s⁻¹ ∈ Subgroup.normalizer (fsuUL T L I : Set G) := by
    have e : l * s * l⁻¹ * s⁻¹ = l * (s * l⁻¹ * s⁻¹) := by group
    rw [e]
    exact (Subgroup.normalizer _).mul_mem hlN hslN
  have hact : conjAct (fsuUL T L I) ⟨l, hlN⟩ =
      conjAct (fsuUL T L I) ⟨l * s * l⁻¹ * s⁻¹, hyN⟩ := by
    have e : (⟨l * s * l⁻¹ * s⁻¹, hyN⟩ : Subgroup.normalizer (fsuUL T L I : Set G)) =
        ⟨l, hlN⟩ * ⟨s * l⁻¹ * s⁻¹, hslN⟩ := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    rw [e, map_mul, (conjAct_eq_one_iff ⟨_, hslN⟩).mpr hsl, mul_one]
  have hy2 : ∃ k : ℕ, (l * s * l⁻¹ * s⁻¹) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ ⟨_, hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  exact hlC (mem_centralizer_of_orderOf hlN hyN hact hlo hy2)


end CFSG.Quasithin.Vol2.Ch10.SecD
