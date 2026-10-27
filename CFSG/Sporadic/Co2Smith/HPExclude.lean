module

public import Certificates.Certificate10081

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open CFSG.Certificates.ExtraspecialNF Subgroup
open scoped Matrix

universe u

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] noncomputable def zHP :
    Hprime :=
  mkHP ⟨((⟨z0, z0_mem_Cz⟩ : Cz), (1 : PGcov)), by
    rw [SmithConfig.mem_fibSub, map_one]
    exact cfgCz.rho_E ⟨⟨z0, z0_mem_Cz⟩, z0_mem_E⟩⟩

@[expose] noncomputable def rHP
    (i : Fin 4) : Hprime :=
  hpElt (![1, 0, 2, 0] i) (![0, 2331, 2331, 144] i)

theorem zHP_central
    (g : Hprime) : g * zHP = zHP * g := by
  obtain ⟨⟨⟨h, p⟩, hp⟩, rfl⟩ := QuotientGroup.mk_surjective g
  show mkHP _ * mkHP _ = mkHP _ * mkHP _
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  refine Prod.ext (Subtype.ext ?_) (by simp)
  exact (Subgroup.mem_centralizer_singleton_iff.mp h.2)

@[expose] noncomputable def zFP :
    FibP := ⟨((⟨z0, z0_mem_Cz⟩ : Cz), (1 : PGcov)), by
  rw [SmithConfig.mem_fibSub, map_one]
  exact cfgCz.rho_E ⟨⟨z0, z0_mem_Cz⟩, z0_mem_E⟩⟩

theorem zHP_mk :
    zHP = mkHP zFP := rfl

theorem rHP_one :
    rHP 1 = hpElt 0 2331 := rfl

theorem rHP_two :
    rHP 2 = hpElt 2 2331 := rfl

theorem rHP_three :
    rHP 3 = hpElt 0 144 := rfl

theorem bitVec_zero : bitVec 0 = 0 := by
  funext i
  simp [bitVec]

theorem hpElt_zero_zero :
    hpElt 0 0 = 1 := by
  have h : fpElt 0 0 = 1 := by
    apply Subtype.ext
    refine Prod.ext (Subtype.ext ?_) pLift_zero
    show cElt 0 0 = 1
    rw [cElt, sElt_zero, one_mul, qElt, Nat.zero_div, Nat.zero_mod, bitVec_zero, Nat.cast_zero,
      nf_zero_zero]
  rw [hpElt, h]
  rfl

theorem hpElt_z :
    hpElt 256 0 = zHP := by
  rw [zHP_mk, hpElt]
  congr 1
  apply Subtype.ext
  refine Prod.ext (Subtype.ext ?_) pLift_zero
  show cElt 256 0 = z0
  rw [cElt, sElt_zero, one_mul, qElt, show 256 / 256 = 1 from rfl, show 256 % 256 = 0 from rfl,
    bitVec_zero, Nat.cast_one, nf_one_zero]

theorem zHP_ne_one :
    zHP ≠ 1 := by
  intro h
  rw [← hpElt_z, ← hpElt_zero_zero] at h
  exact absurd (hpElt_injOn (by norm_num) (by norm_num) (by norm_num) (by norm_num) h).1
    (by norm_num)

theorem zHP_sq :
    zHP * zHP = 1 := by
  rw [zHP_mk, ← map_mul]
  have : zFP * zFP = 1 := by
    apply Subtype.ext
    refine Prod.ext (Subtype.ext ?_) (mul_one 1)
    exact seedA_mul_self
  rw [this, map_one]

theorem table_disj : ∀ i j : Fin 4, i ≠ j →
    (![5376, 1152, 448, 96] i ≠ (![5376, 1152, 448, 96] j : ℕ) ∨
      ![5376, 768, 128, 0] i ≠ (![5376, 768, 128, 0] j : ℕ)) := by decide

theorem table_pair : ∀ i j : Fin 4, (![5376, 1152, 448, 96] i : ℕ) = ![5376, 768, 128, 0] j →
    (![5376, 768, 128, 0] i : ℕ) = ![5376, 1152, 448, 96] j → i = 0 := by decide

theorem false_of_census
    {G : Type u} [Group G]
    [Finite G] {z : G} (hG : SmithHyp G z) (φ : centralizer ({z} : Set G) ≃* Hprime) : False := by
  have hE : ∀ {y : Hprime}, y ∈ CFSG.pCore 2 Hprime ↔ ∃ e < 512, hpElt e 0 = y :=
    fun {y} => mem_pCore_Hprime hG.centralizer φ (y := y)
  obtain ⟨hcard, hrep, hE1, hE2, ha2, hb2, hat, hbt, hab⟩ := Certificates.certificate10081
  rw [hpElt_z] at hrep hE2
  have hZ : ∀ i, sqrtCnt zHP (rHP i) = ![5376, 1152, 448, 96] i := fun i => (hrep i _ rfl).2.1
  have hR : ∀ i, sqrtCnt (rHP i) (rHP i) = ![5376, 768, 128, 0] i := fun i => (hrep i _ rfl).2.2.1
  have hzc : ∀ g : Hprime, g * zHP = zHP * g := zHP_central
  have hcls := exists_conj_of_card rHP ![270, 2520, 22680, 120960]
    (by rw [hcard]; rfl) zHP_sq zHP_ne_one hzc (fun i => (hrep i _ rfl).1)
    (fun i => (hrep i _ rfl).2.2.2)
    (fun i j hij => not_conj_of_sqrtCnt hzc (by
      rw [hZ, hZ, hR, hR]
      exact table_disj i j hij))
  refine false_of_classes hG φ zHP rHP (fun y hy hcen => ?_) hcls (fun i j h1 h2 => ?_)
    (hE.mpr ⟨1, by norm_num, rfl⟩) (fun i hi hmem => ?_) (fun a ha b hb => ?_)
    ⟨hpElt 2 0, hE.mpr ⟨2, by norm_num, rfl⟩, hpElt 32 0, hE.mpr ⟨32, by norm_num, rfl⟩,
      ha2, hb2, hat, hbt, hab⟩
  · obtain ⟨e, he, rfl⟩ := hE.mp hy
    rcases hE1 e he fun e' he' => (hcen (hpElt e' 0) (hE.mpr ⟨e', he', rfl⟩)).symm with h | h
    · subst h
      exact Or.inl hpElt_zero_zero
    · subst h
      exact Or.inr hpElt_z
  · rw [hZ, hR] at h1
    rw [hZ, hR] at h2
    exact table_pair i j h1 h2
  · obtain ⟨e, he, he0⟩ := hE.mp hmem
    fin_cases i
    · exact hi rfl
    · exact absurd (hpElt_injOn (n' := 2331) he (by norm_num) (by norm_num) (by norm_num)
        (he0.trans rHP_one)).2 (by norm_num)
    · exact absurd (hpElt_injOn (n' := 2331) he (by norm_num) (by norm_num) (by norm_num)
        (he0.trans rHP_two)).2 (by norm_num)
    · exact absurd (hpElt_injOn (n' := 144) he (by norm_num) (by norm_num) (by norm_num)
        (he0.trans rHP_three)).2 (by norm_num)
  · obtain ⟨e, he, rfl⟩ := hE.mp ha
    obtain ⟨e', he', rfl⟩ := hE.mp hb
    rcases hE2 e e' with h | h
    · left
      rw [h]
      group
    · right
      rw [h, mul_assoc, mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

theorem nonempty_mulEquiv_Cz_of_census
    {G : Type u} [Group G] [Finite G] {z : G} (hG : SmithHyp G z) :
    Nonempty (centralizer ({z} : Set G) ≃* Cz) :=
  (smith_dichotomy hG.centralizer).resolve_right fun ⟨φ⟩ => false_of_census hG φ

end CFSG.Sporadic.Co2Smith
