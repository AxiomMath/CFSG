module

public import CFSG.Quasithin.Vol2.Ch10SecD211B

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem mem_oPrimeResidualOf_of_pow {p : ℕ} (hp : p.Prime) {X : Subgroup G} {x : G}
    (hx : x ∈ X) {k : ℕ} (hk : x ^ p ^ k = 1) : x ∈ oPrimeResidualOf p X := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk)
  exact Subgroup.subset_closure ⟨hx, j, hj⟩

theorem oPrimeResidualOf_le' (p : ℕ) (X : Subgroup G) : oPrimeResidualOf p X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem oPrimeResidualOf_mono' (p : ℕ) {X Y : Subgroup G} (h : X ≤ Y) :
    oPrimeResidualOf p X ≤ oPrimeResidualOf p Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem oPrimeResidualOf_le_of {p : ℕ} {X Y : Subgroup G}
    (h : ∀ x ∈ X, ∀ k : ℕ, orderOf x = p ^ k → x ∈ Y) : oPrimeResidualOf p X ≤ Y :=
  (Subgroup.closure_le Y).mpr fun x hx => h x hx.1 _ hx.2.choose_spec

variable [Finite G] {T L I : Subgroup G}

theorem Vz_le_Gz (h : Hyp10 G T L I) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) :
    Vz v₁ v₂ ≤ Subgroup.centralizer ({v₁ * v₂} : Set G) :=
  conjClosure_le fun _ hg _ he => (Subgroup.centralizer _).mul_mem
    ((Subgroup.centralizer _).mul_mem hg (closure_le_centralizer_z h hd he))
    ((Subgroup.centralizer _).inv_mem hg)

theorem not_exists_pow_commutator (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {s : G} (hsT : s ∈ T)
    (hsn : s ∉ Subgroup.normalizer (L : Set G)) {x : G} (hxL : x ∈ L) (hxo : Odd (orderOf x))
    (hxC : x ∉ Subgroup.centralizer (fsuUL T L I : Set G)) :
    ¬ ∃ k : ℕ, (x * s * x⁻¹ * s⁻¹) ^ 2 ^ k = 1 := by
  intro hy2
  have hsl : s * x⁻¹ * s⁻¹ ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
    have hsn' : s⁻¹ ∉ Subgroup.normalizer (L : Set G) := by
      intro h'
      apply hsn
      have := (Subgroup.normalizer (L : Set G)).inv_mem h'
      rwa [inv_inv] at this
    have hconj := SecA.conjugate_eq_of_not_mem h37 h38 h ht htn (T.inv_mem hsT) hsn'
    refine conjugate_le_centralizer_V1 h ht htn ?_
    rw [← hconj, SecA.mem_conjugate_iff]
    simpa [mul_assoc] using L.inv_mem hxL
  have hxN : x ∈ Subgroup.normalizer (fsuUL T L I : Set G) := L_le_normalizer_V1 hxL
  have hslN : s * x⁻¹ * s⁻¹ ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
    Subgroup.centralizer_le_normalizer _ hsl
  have hyN : x * s * x⁻¹ * s⁻¹ ∈ Subgroup.normalizer (fsuUL T L I : Set G) := by
    have e : x * s * x⁻¹ * s⁻¹ = x * (s * x⁻¹ * s⁻¹) := by group
    rw [e]
    exact (Subgroup.normalizer _).mul_mem hxN hslN
  have hact : conjAct (fsuUL T L I) ⟨x, hxN⟩ =
      conjAct (fsuUL T L I) ⟨x * s * x⁻¹ * s⁻¹, hyN⟩ := by
    have e : (⟨x * s * x⁻¹ * s⁻¹, hyN⟩ : Subgroup.normalizer (fsuUL T L I : Set G)) =
        ⟨x, hxN⟩ * ⟨s * x⁻¹ * s⁻¹, hslN⟩ := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    rw [e, map_mul, (conjAct_eq_one_iff ⟨_, hslN⟩).mpr hsl, mul_one]
  exact hxC (mem_centralizer_of_orderOf hxN hyN hact hxo hy2)

theorem T_le_normalizer_Xz {z : G} (hTz : T ≤ Subgroup.centralizer ({z} : Set G)) :
    T ≤ Subgroup.normalizer (Xz T L z : Set G) := by
  refine le_trans ?_ (normalizer_le_normalizer_oTwoUpper _)
  intro x hx
  refine A4.mem_normalizer_of_conj_mem fun y hy => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (SecA.le_fsuM T L hx) y).mp hy.1
  · have hxz := Subgroup.mem_centralizer_singleton_iff.mp (hTz hx)
    have hyz := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hxz' : x⁻¹ * z = z * x⁻¹ := by
      calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * z) * x⁻¹ := by rw [hxz]
        _ = z * x⁻¹ := by group
    show x * y * x⁻¹ ∈ Subgroup.centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * y * x⁻¹ * z = x * y * (x⁻¹ * z) := by group
      _ = x * (y * z) * x⁻¹ := by rw [hxz']; group
      _ = x * z * y * x⁻¹ := by rw [hyz]; group
      _ = z * (x * y * x⁻¹) := by rw [hxz]; group

end CFSG.Quasithin.Vol2.Ch10.SecD
