module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.Quasithin.Background.A318PC4

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG Matrix
open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree Type123)
open CFSG.RankThree.PartTwo.Sec4 (zPi exists_tau exists_scalar_of_mem_zPi coe_scalar_eq_smul
  exists_scalar_of_mk_mul_comm exists_mul_pow_mem_statedScalars_of_irred card_le_nine_of_heis)
open CFSG.Open (StatedScalars)

section Aux

variable {K : Type} [Field K]

private theorem statedScalars_three_eq_center :
    StatedScalars (Fin 3) K = Subgroup.center (GL (Fin 3) K) := by
  rw [StatedScalars, Matrix.GeneralLinearGroup.center_eq_range_scalar]

private theorem mem_statedScalars_iff {g : GL (Fin 3) K} :
    g ∈ StatedScalars (Fin 3) K ↔ ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin 3) c = g :=
  MonoidHom.mem_range

private theorem mem_statedScalars_of_mk_eq_one {g : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk g = 1) : g ∈ StatedScalars (Fin 3) K := by
  rw [statedScalars_three_eq_center]
  exact ProjGenLinGroup.mk_eq_one.mp h

private theorem quot_eq_of_mk_eq {g₁ g₂ : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk g₁ = ProjGenLinGroup.mk g₂) :
    (g₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) =
      (g₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) := by
  obtain ⟨z, hz, rfl⟩ := ProjGenLinGroup.mk_eq_mk_iff'.mp h
  rw [QuotientGroup.eq, inv_mul_cancel_left, statedScalars_three_eq_center]
  exact hz

private theorem quot_comm_of_mk_comm {g₁ g₂ : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk g₁ * ProjGenLinGroup.mk g₂ =
      ProjGenLinGroup.mk g₂ * ProjGenLinGroup.mk g₁) :
    (g₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) * (g₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) =
      (g₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) *
        (g₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  apply quot_eq_of_mk_eq
  rw [map_mul, map_mul]
  exact h

end Aux

section Groups

private theorem comm_of_eq_sup_zpowers {G : Type} [Group G] {a b c : G} (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) (T : Subgroup G)
    (hT : T = Subgroup.zpowers a ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers c) {x z : G}
    (hx : x ∈ T) (hz : z ∈ T) : x * z = z * x := by
  have ha : a ∈ Subgroup.centralizer ({a, b, c} : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rcases hh with rfl | rfl | rfl
    · rfl
    · exact hab.symm
    · exact hac.symm
  have hb : b ∈ Subgroup.centralizer ({a, b, c} : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rcases hh with rfl | rfl | rfl
    · exact hab
    · rfl
    · exact hbc.symm
  have hc : c ∈ Subgroup.centralizer ({a, b, c} : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rcases hh with rfl | rfl | rfl
    · exact hac
    · exact hbc
    · rfl
  have hTS : T ≤ Subgroup.centralizer ({a, b, c} : Set G) := by
    rw [hT]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb))
      (Subgroup.zpowers_le.mpr hc)
  have hcomm : ∀ t ∈ T, ∀ s ∈ T, t * s = s * t := by
    intro t ht s hs
    have key : ∀ g : G, t * g = g * t → g ∈ Subgroup.centralizer ({t} : Set G) := fun g hg =>
      Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]
        exact hg
    have hcen := Subgroup.mem_centralizer_iff.mp (hTS ht)
    have hle : T ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [hT]
      exact sup_le
        (sup_le (Subgroup.zpowers_le.mpr (key a (hcen a (by simp)).symm))
          (Subgroup.zpowers_le.mpr (key b (hcen b (by simp)).symm)))
        (Subgroup.zpowers_le.mpr (key c (hcen c (by simp)).symm))
    exact Subgroup.mem_centralizer_iff.mp (hle hs) t (Set.mem_singleton t)
  exact hcomm x hx z hz

private theorem card_sup_zpowers_eq_nine {G : Type} [Group G] [Finite G] {a b : G}
    (hab : a * b = b * a) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hbn : b ∉ Subgroup.zpowers a) :
    Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) = 9 := by
  have hAcard : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hBcard : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ z ∈ Subgroup.zpowers b, x * z = z * x := by
    intro x hx z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_zpow (show Commute a b from hab) k l).eq
  obtain ⟨hcardeq, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hinf : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers b : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers b : Subgroup G) ∣ 3 := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso
      have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers b = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hBcard])
      have hbmem : b ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := by
        rw [heq]
        exact Subgroup.mem_zpowers b
      exact hbn (Subgroup.mem_inf.mp hbmem).1
  rw [hinf, hAcard, hBcard] at hcardeq
  omega

end Groups

theorem mem_sup_of_commute_type3 {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {y b m : GL (Fin 3) K}
    (hy : Type123 π (p ^ f) K y 3)
    (hb3 : ProjGenLinGroup.mk b ^ 3 = 1)
    (hby : ProjGenLinGroup.mk b * ProjGenLinGroup.mk y =
      ProjGenLinGroup.mk y * ProjGenLinGroup.mk b)
    (hbn : ProjGenLinGroup.mk b ∉ Subgroup.zpowers (ProjGenLinGroup.mk y))
    (hmy : ProjGenLinGroup.mk m * ProjGenLinGroup.mk y =
      ProjGenLinGroup.mk y * ProjGenLinGroup.mk m)
    (hmb : ProjGenLinGroup.mk m * ProjGenLinGroup.mk b =
      ProjGenLinGroup.mk b * ProjGenLinGroup.mk m) :
    ProjGenLinGroup.mk m ∈
      Subgroup.zpowers (ProjGenLinGroup.mk y) ⊔ Subgroup.zpowers (ProjGenLinGroup.mk b) := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  haveI : Finite K := hK.finite
  haveI : Finite (GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) :=
    Finite.of_surjective _ QuotientGroup.mk_surjective
  obtain ⟨-, hy3Z, hirr⟩ : y ∉ zPi π 3 (p ^ f) K ∧ y ^ 3 ∈ zPi π 3 (p ^ f) K ∧
      ∀ W : Submodule K (Fin 3 → K),
        (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := hy
  obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hy3Z
  have hyM : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ξ : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hξ, coe_scalar_eq_smul]
  have hℓ : ∀ μ : K, μ ^ 3 ≠ (ξ : K) :=
    CFSG.Quasithin.A318P.not_cube_of_irreducible hτ hτ1 hyM hirr
  have hy3S : y ^ 3 ∈ StatedScalars (Fin 3) K := mem_statedScalars_iff.mpr ⟨ξ, hξ⟩
  have hyS : y ∉ StatedScalars (Fin 3) K := by
    intro hyS
    obtain ⟨c, hc⟩ := mem_statedScalars_iff.mp hyS
    have hyc : (y : Matrix (Fin 3) (Fin 3) K) = (c : K) • 1 := by
      rw [← hc, coe_scalar_eq_smul]
    have h3eq : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 =
        ((c : K) ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [hyc, smul_pow, one_pow]
    rw [hyM] at h3eq
    have hξc : (ξ : K) = (c : K) ^ 3 := by
      have := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) h3eq
      simpa using this
    exact hℓ (c : K) hξc.symm
  have hyQ : (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ≠ 1 :=
    fun h => hyS ((QuotientGroup.eq_one_iff y).mp h)
  have hy3Q : (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff (y ^ 3)).mpr hy3S
  have hker : StatedScalars (Fin 3) K ≤
      (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).ker := by
    rw [ProjGenLinGroup.ker_mk]
    exact le_of_eq statedScalars_three_eq_center
  obtain ⟨φ, hφ⟩ : ∃ φ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K →* ProjGenLinGroup (Fin 3) K,
      ∀ g : GL (Fin 3) K,
        φ (g : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = ProjGenLinGroup.mk g :=
    ⟨QuotientGroup.lift _ ProjGenLinGroup.mk hker, fun g => rfl⟩
  have hbyQ := quot_comm_of_mk_comm hby
  have hmyQ := quot_comm_of_mk_comm hmy
  have hmbQ := quot_comm_of_mk_comm hmb
  have hbnQ : (b : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∉
      Subgroup.zpowers (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) := by
    intro h
    apply hbn
    have h' := Subgroup.mem_map_of_mem φ h
    rw [MonoidHom.map_zpowers] at h'
    simpa only [hφ] using h'
  have hb1Q : (b : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ≠ 1 := by
    intro h
    apply hbnQ
    rw [h]
    exact Subgroup.one_mem _
  have hb3Q : (b : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff (b ^ 3)).mpr
      (mem_statedScalars_of_mk_eq_one (by rw [map_pow]; exact hb3))
  obtain ⟨c, hc⟩ := exists_scalar_of_mk_mul_comm hbyQ
  have hcne : c ≠ 1 := by
    intro hc1
    subst hc1
    have hcomm : b * y = y * b := by
      have h1 : b * y * b⁻¹ = y := by rw [hc, map_one, one_mul]
      exact mul_inv_eq_iff_eq_mul.mp h1
    have hb3S : b ^ 3 ∈ StatedScalars (Fin 3) K :=
      mem_statedScalars_of_mk_eq_one (by rw [map_pow]; exact hb3)
    obtain ⟨k, hk⟩ := exists_mul_pow_mem_statedScalars_of_irred h3 hτ hτ1 hℓ hyM hcomm hb3S
    have hmk : ProjGenLinGroup.mk (b * y ^ (k : ℕ)) = 1 :=
      ProjGenLinGroup.mk_eq_one.mpr (by rw [← statedScalars_three_eq_center]; exact hk)
    rw [map_mul, map_pow] at hmk
    apply hbn
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-((k : ℕ) : ℤ), ?_⟩
    rw [_root_.zpow_neg, _root_.zpow_natCast]
    exact (eq_inv_of_mul_eq_one_left hmk).symm
  obtain ⟨E, hE⟩ : ∃ E : Subgroup (GL (Fin 3) K ⧸ StatedScalars (Fin 3) K),
      E = Subgroup.zpowers (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ⊔
        Subgroup.zpowers (b : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ⊔
          Subgroup.zpowers (m : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Subgroup (GL (Fin 3) K ⧸ StatedScalars (Fin 3) K),
      D = Subgroup.zpowers (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ⊔
        Subgroup.zpowers (b : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) := ⟨_, rfl⟩
  have hcommE : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    comm_of_eq_sup_zpowers hbyQ.symm hmyQ.symm hmbQ.symm E hE hx hz
  have hyE : (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E := by
    rw [hE]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hbE : (b : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E := by
    rw [hE]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hmE : (m : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E := by
    rw [hE]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hEcard : Nat.card E ≤ 9 :=
    card_le_nine_of_heis h3 E hcommE hbE hyE hcne hc
  have hDcard : Nat.card D = 9 := by
    rw [hD]
    exact card_sup_zpowers_eq_nine hbyQ.symm hy3Q hyQ hb3Q hb1Q hbnQ
  have hDE : D ≤ E := by
    rw [hD, hE]
    exact le_sup_left
  have hEeq : D = E := Subgroup.eq_of_le_of_card_ge hDE (by rw [hDcard]; exact hEcard)
  have hmD : (m : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ D := by
    rw [hEeq]
    exact hmE
  have hfin := Subgroup.mem_map_of_mem φ hmD
  rw [hD, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hfin
  simp only [hφ] at hfin
  exact hfin

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
