module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Transport

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open

theorem flagAt_pCoreOf_le {U X ι F : Type} [Group U] [Group X] [Finite X] [Fintype ι]
    [DecidableEq ι] [Field F] (j : U →* GL ι F) (B : Option ((ι → F) → (ι → F) → F))
    (hodd : OddCenterOf j) (hflag : FlagCentU j B) {K R : Subgroup X}
    (h : FlagAt j B K R) :
    ∀ r ∈ R, r ≠ 1 → pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤
      Subgroup.centralizer (R : Set X) := by
  intro r hr hr1
  obtain ⟨φ, R', W, H, hrange, hker, hmap, hinj, hWH, hv, hB⟩ := h
  obtain ⟨r', hr', hr'eq⟩ : ∃ r' ∈ R', φ r' = r := by
    have : r ∈ R'.map φ := by rw [hmap]; exact hr
    exact Subgroup.mem_map.mp this
  have hr'1 : r' ≠ 1 := by
    intro h1
    apply hr1
    rw [← hr'eq, h1, map_one]
  have hoddker : Odd (Nat.card φ.ker) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hker)
  let M : Subgroup U := (Subgroup.centralizer ({r} : Set X)).comap φ
  have hkM : φ.ker ≤ M := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : φ x = 1 := MonoidHom.mem_ker.mp hx
    rw [hx1]
    exact Subgroup.one_mem _
  have hMmap : M.map φ = K ⊓ Subgroup.centralizer ({r} : Set X) := by
    rw [Subgroup.map_comap_eq, hrange]
  have hmapcore : (pCoreOf 2 M).map φ = pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) := by
    rw [LieKnownR2.map_pCoreOf_eq_of_odd_central_ker hker hoddker hkM, hMmap]
  have hcent_le_M : Subgroup.centralizer ({r'} : Set U) ≤ M := by
    intro m hm
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_centralizer_singleton_iff] at hm ⊢
    rw [← hr'eq, ← map_mul, ← map_mul, hm]
  have hcore_le : pCoreOf 2 M ≤ Subgroup.centralizer ({r'} : Set U) := by
    intro s hs
    have hsM : s ∈ M := GGRootNorm.pCoreOf_le M hs
    have hc_mem : s * r' * s⁻¹ * r'⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have hsC : φ s ∈ Subgroup.centralizer ({r} : Set X) := by
        have := hsM
        rwa [Subgroup.mem_comap] at this
      have hcomm : φ s * r = r * φ s := Subgroup.mem_centralizer_singleton_iff.mp hsC
      simp only [map_mul, map_inv, hr'eq]
      rw [hcomm]
      group
    have hc_center : s * r' * s⁻¹ * r'⁻¹ ∈ Subgroup.center U := hker hc_mem
    have hc_comm : ∀ g : U, g * (s * r' * s⁻¹ * r'⁻¹) = (s * r' * s⁻¹ * r'⁻¹) * g :=
      Subgroup.mem_center_iff.mp hc_center
    obtain ⟨k, hk⟩ :=
      (GGRootNorm.isPGroup_pCoreOf M).exists_orderOf_eq_pow (⟨s, hs⟩ : ↥(pCoreOf 2 M))
    have hk' : orderOf s = 2 ^ k := by
      rw [← Subgroup.orderOf_mk s hs]
      exact hk
    have hpow : ∀ n : ℕ,
        s ^ n * r' * (s ^ n)⁻¹ * r'⁻¹ = (s * r' * s⁻¹ * r'⁻¹) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc s ^ (n + 1) * r' * (s ^ (n + 1))⁻¹ * r'⁻¹
            = s ^ n * (s * r' * s⁻¹) * (s ^ n)⁻¹ * r'⁻¹ := by group
          _ = (s ^ n * (s * r' * s⁻¹ * r'⁻¹)) * r' * (s ^ n)⁻¹ * r'⁻¹ := by group
          _ = (s * r' * s⁻¹ * r'⁻¹) * (s ^ n * r' * (s ^ n)⁻¹ * r'⁻¹) := by
                rw [hc_comm (s ^ n)]
                group
          _ = (s * r' * s⁻¹ * r'⁻¹) * (s * r' * s⁻¹ * r'⁻¹) ^ n := by rw [ih]
          _ = (s * r' * s⁻¹ * r'⁻¹) ^ (n + 1) := by group
    have hcop : (orderOf s).Coprime (Nat.card φ.ker) := by
      rw [hk']
      exact (Nat.Coprime.pow_right k hoddker.coprime_two_right).symm
    have h1 : (s * r' * s⁻¹ * r'⁻¹) ^ orderOf s = 1 := by
      rw [← hpow (orderOf s)]
      simp
    have h2 : (s * r' * s⁻¹ * r'⁻¹) ^ Nat.card φ.ker = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard φ.ker hc_mem)
    have hc_eq : s * r' * s⁻¹ * r'⁻¹ = 1 :=
      (pow_eq_one_iff_of_coprime hcop).mp ⟨h1, h2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc s * r' = (s * r' * s⁻¹ * r'⁻¹) * (r' * s) := by group
      _ = 1 * (r' * s) := by rw [hc_eq]
      _ = r' * s := by simp
  have hcore_le' : pCoreOf 2 M ≤ pCoreOf 2 (Subgroup.centralizer ({r'} : Set U)) :=
    GGRootNorm.le_pCoreOf_of_normalized hcore_le (GGRootNorm.isPGroup_pCoreOf M) (by
      intro m hm t ht
      have hmM : m ∈ M := hcent_le_M hm
      exact (Subgroup.mem_normalizer_iff.mp (GGRootNorm.le_normalizer_pCoreOf M hmM) t).mp ht)
  have hflagr' := hflag R' W H hWH hv hB r' hr' hr'1
  have hcoreR' : pCoreOf 2 M ≤ Subgroup.centralizer (R' : Set U) := hcore_le'.trans hflagr'
  intro x hx
  rw [← hmapcore] at hx
  obtain ⟨s, hs, hxs⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨v, hvR', hyv⟩ : ∃ v ∈ R', φ v = y := by
    have : y ∈ R'.map φ := by rw [hmap]; exact hy
    exact Subgroup.mem_map.mp this
  have hscent : s ∈ Subgroup.centralizer (R' : Set U) := hcoreR' hs
  have hcomm : v * s = s * v := (Subgroup.mem_centralizer_iff.mp hscent) v hvR'
  rw [← hxs, ← hyv, ← map_mul, ← map_mul, hcomm]

end CFSG.StandardType.RCKFlag
