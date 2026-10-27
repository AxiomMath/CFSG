module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

variable {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]

theorem centralizer_quotient_eq (hN : N ≤ Subgroup.center K)
    (hodd : ∀ n ∈ N, Odd (orderOf n)) {t : K} (ht : t * t = 1) :
    Subgroup.centralizer ({(t : K ⧸ N)} : Set (K ⧸ N)) =
      (Subgroup.centralizer ({t} : Set K)).map (QuotientGroup.mk' N) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
    constructor
    · intro h
      refine ⟨k, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : ((k * t * k⁻¹ * t⁻¹ : K) : K ⧸ N) = 1 := by
        have : ((k : K ⧸ N)) * (t : K ⧸ N) = (t : K ⧸ N) * (k : K ⧸ N) := h
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [this]; group
      have hn : k * t * k⁻¹ * t⁻¹ ∈ N := (QuotientGroup.eq_one_iff _).mp h1
      set n := k * t * k⁻¹ * t⁻¹ with hn_def
      have hnc : ∀ g : K, n * g = g * n := fun g => (Subgroup.mem_center_iff.mp (hN hn) g).symm
      have hsq : n * n = 1 := by
        have h2 : (k * t * k⁻¹) * (k * t * k⁻¹) = 1 := by
          calc (k * t * k⁻¹) * (k * t * k⁻¹) = k * (t * t) * k⁻¹ := by group
            _ = 1 := by rw [ht]; group
        have h3 : k * t * k⁻¹ = n * t := by rw [hn_def]; group
        rw [h3] at h2
        calc n * n = n * n * (t * t) := by rw [ht, mul_one]
          _ = (n * t) * (n * t) := by
              calc n * n * (t * t) = n * (n * t) * t := by group
                _ = n * (t * n) * t := by rw [hnc t]
                _ = (n * t) * (n * t) := by group
          _ = 1 := h2
      have hn1 : n = 1 := by
        have hord : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
        have hodd' := hodd n hn
        rcases (Nat.dvd_prime Nat.prime_two).mp hord with h4 | h4
        · exact orderOf_eq_one_iff.mp h4
        · rw [h4] at hodd'
          exact absurd hodd' (by decide)
      have h3 : k * t * k⁻¹ * t⁻¹ = 1 := hn1
      calc k * t = k * t * k⁻¹ * k := by group
        _ = t * k := by
            have : k * t * k⁻¹ = t := by
              calc k * t * k⁻¹ = (k * t * k⁻¹ * t⁻¹) * t := by group
                _ = t := by rw [h3, one_mul]
            rw [this]
    · rintro ⟨c, hc, hck⟩
      have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
      have hck' : ((c : K ⧸ N)) = (k : K ⧸ N) := hck
      rw [← hck', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc']

theorem nonempty_mulEquiv_dihedral_centralizer_quotient (hN : N ≤ Subgroup.center K)
    (hNcard : Nat.card N = 3) {t : K} (ht : t * t = 1)
    (hC : Nat.card (Subgroup.centralizer ({t} : Set K)) = 24)
    {R : Subgroup K} (hR : R ≤ Subgroup.centralizer ({t} : Set K))
    (eR : ↥R ≃* DihedralGroup 4) :
    Nonempty (↥(Subgroup.centralizer ({(t : K ⧸ N)} : Set (K ⧸ N))) ≃* DihedralGroup 4) := by
  classical
  have hodd : ∀ n ∈ N, Odd (orderOf n) := by
    intro n hn
    have hd : orderOf n ∣ 3 := by
      rw [← hNcard]; exact Subgroup.orderOf_dvd_natCard N hn
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h <;> rw [h] <;> decide
  have hcent := centralizer_quotient_eq N hN hodd ht
  set C := Subgroup.centralizer ({t} : Set K) with hCdef
  set π : K →* K ⧸ N := QuotientGroup.mk' N with hπ
  have hNC : N ≤ C := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_center_iff.mp (hN hn) t).symm)
  have hRcard : Nat.card R = 8 := by
    rw [Nat.card_congr eR.toEquiv, DihedralGroup.nat_card]
  have hmapcard : Nat.card (C.map π) = 8 := by
    have h1 : N.relIndex C = Nat.card (C.map π) := by
      rw [← Subgroup.relIndex_ker C π, hπ, QuotientGroup.ker_mk']
    have h2 := (N.subgroupOf C).index_mul_card
    have h3 : Nat.card (N.subgroupOf C) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv
    rw [h3, hNcard, ← Subgroup.relIndex, h1, hC] at h2
    omega
  have hdisj : Disjoint R N :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hRcard, hNcard]; decide)
  set φ : ↥R →* K ⧸ N := π.comp R.subtype with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : (a : K)⁻¹ * (b : K) ∈ N := QuotientGroup.eq.mp hab
    have h2 : (a : K)⁻¹ * (b : K) ∈ R := R.mul_mem (R.inv_mem a.2) b.2
    have h3 : (a : K)⁻¹ * (b : K) = 1 := by
      have := hdisj.le_bot ⟨h2, h1⟩
      simpa using this
    have h4 : (a : K) = b := by
      have := congrArg (fun x => (a : K) * x) h3
      simpa using this.symm
    exact Subtype.ext h4
  have hrange : φ.range = R.map π := by
    ext x
    simp [hφ, MonoidHom.mem_range, Subgroup.mem_map]
  have hle : R.map π ≤ C.map π := Subgroup.map_mono hR
  have hRmap : Nat.card (R.map π) = 8 := by
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm, hRcard]
  have heq : R.map π = C.map π :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hmapcard, hRmap])
  have heq2 : Subgroup.centralizer ({(t : K ⧸ N)} : Set (K ⧸ N)) = φ.range := by
    rw [hcent, hrange, heq]
  exact ⟨(MulEquiv.subgroupCongr heq2).trans ((MonoidHom.ofInjective hφinj).symm.trans eR)⟩

end CFSG.Quasithin.Kleidman.ThreeLocal
