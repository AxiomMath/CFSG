module

public import CFSG.Walter.W67.Section5.MaxClass

public section

namespace CFSG.Walter.W67.Sec65

theorem index_centralizer_upperCentralSeries_two {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q]
    [Finite Q] (hQ : IsPGroup p Q) (x : Q)
    (hx : Nat.card (Subgroup.centralizer ({x} : Set Q)) = p ^ 2) (hQc : p ^ 3 < Nat.card Q) :
    (Subgroup.centralizer ((Subgroup.upperCentralSeries Q 2 : Subgroup Q) : Set Q)).index = p ∧
      x ∉ Subgroup.centralizer ((Subgroup.upperCentralSeries Q 2 : Subgroup Q) : Set Q) := by
  have hp : p.Prime := Fact.out
  have hp1 := hp.one_lt
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  set Z := Subgroup.center Q
  set Z₂ := Subgroup.upperCentralSeries Q 2
  have hmem : ∀ g : Q, g ∈ Z₂ ↔ ∀ y : Q, g * y * g⁻¹ * y⁻¹ ∈ Z := by
    intro g
    have h := Subgroup.mem_upperCentralSeries_succ_iff (G := Q) (n := 1) (x := g)
    rw [Subgroup.upperCentralSeries_one] at h
    exact h
  have hcomm : ∀ g ∈ Z₂, ∀ y : Q, y * g * y⁻¹ * g⁻¹ ∈ Z := by
    intro g hg y
    have h := Z.inv_mem ((hmem g).mp hg y)
    rwa [show (g * y * g⁻¹ * y⁻¹)⁻¹ = y * g * y⁻¹ * g⁻¹ by group] at h
  have hZZ₂ : Z ≤ Z₂ := by
    have h := Subgroup.upperCentralSeries_mono Q (show 1 ≤ 2 by norm_num)
    rwa [Subgroup.upperCentralSeries_one] at h
  have hxZ : x ∉ Z := by
    intro hxZ
    have htop : Subgroup.centralizer ({x} : Set Q) = ⊤ := by
      ext g
      simp only [Subgroup.mem_top, iff_true, Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_center_iff.mp hxZ g
    rw [htop, Subgroup.card_top] at hx
    rw [hx] at hQc
    have : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by norm_num)
    omega
  have hZC : Z ≤ Subgroup.centralizer ({x} : Set Q) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hz x).symm
  have hQnt : Nontrivial Q := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have : 0 < p ^ 3 := pow_pos hp.pos 3
    omega
  have hZcard : Nat.card Z = p := by
    have hdvd : Nat.card Z ∣ p ^ 2 := by
      rw [← hx]
      exact Subgroup.card_dvd_of_le hZC
    obtain ⟨j, hj, hZj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hZ1 : 1 < Nat.card Z := Finite.one_lt_card_iff_nontrivial.mpr hQ.center_nontrivial
    have hj2 : j ≠ 2 := by
      rintro rfl
      apply hxZ
      rw [Subgroup.eq_of_le_of_card_ge hZC (by rw [hx, hZj])]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [hZj, pow_zero] at hZ1
      exact lt_irrefl _ hZ1
    have hj1 : j = 1 := by omega
    rw [hZj, hj1, pow_one]
  have hxZ₂ : x ∉ Z₂ := by
    intro hx2
    have h := MaxClass.card_le_of_commutator_mem_center x ⊤ (fun g _ => hcomm x hx2 g)
    rw [Subgroup.card_top, hx, hZcard, ← pow_succ] at h
    exact absurd hQc (not_lt.mpr h)
  have hZ₂C : Z₂ ⊓ Subgroup.centralizer ({x} : Set Q) = Z := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (le_inf hZZ₂ hZC)
    have hdvd : Nat.card ↥(Z₂ ⊓ Subgroup.centralizer ({x} : Set Q)) ∣ p ^ 2 := by
      rw [← hx]
      exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨j, hj, hKj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hj2 : j ≠ 2 := by
      rintro rfl
      apply hxZ₂
      have heq := Subgroup.eq_of_le_of_card_ge
        (inf_le_right : Z₂ ⊓ Subgroup.centralizer ({x} : Set Q) ≤ _) (by rw [hx, hKj])
      have hxK : x ∈ Z₂ ⊓ Subgroup.centralizer ({x} : Set Q) := by
        rw [heq]
        exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      exact (Subgroup.mem_inf.mp hxK).1
    rw [hKj, hZcard]
    calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p
  have hD : ∀ g ∈ Z₂, g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center Q := fun g hg => (hmem g).mp hg x
  have hZ₂card : Nat.card Z₂ ≤ p ^ 2 := by
    have h1 := Subgroup.card_ker_mul_card_range (MaxClass.commHom x Z₂ hD)
    have hker : Nat.card (MaxClass.commHom x Z₂ hD).ker ≤ Nat.card Z := by
      refine Nat.card_le_card_of_injective (fun g => ⟨((g : Z₂) : Q), ?_⟩) ?_
      · have hg := g.2
        rw [MonoidHom.mem_ker] at hg
        have hg' : ((g : Z₂) : Q) * x * ((g : Z₂) : Q)⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hg
        rw [← hZ₂C]
        refine Subgroup.mem_inf.mpr ⟨(g : Z₂).2, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc ((g : Z₂) : Q) * x
            = (((g : Z₂) : Q) * x * ((g : Z₂) : Q)⁻¹ * x⁻¹) * (x * ((g : Z₂) : Q)) := by group
          _ = x * ((g : Z₂) : Q) := by rw [hg', one_mul]
      · intro a b hab
        have h := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h)
    have hrange : Nat.card (MaxClass.commHom x Z₂ hD).range ≤ Nat.card Z :=
      Subgroup.card_le_card_group _
    rw [← h1]
    calc _ ≤ Nat.card Z * Nat.card Z := Nat.mul_le_mul hker hrange
      _ = p ^ 2 := by rw [hZcard, sq]
  obtain ⟨z, hzZ₂, hzZ⟩ : ∃ z ∈ Z₂, z ∉ Z := by
    have hQZ : IsPGroup p (Q ⧸ Z) := hQ.to_quotient Z
    have : Nontrivial (Q ⧸ Z) := by
      refine nontrivial_of_ne (x : Q ⧸ Z) 1 ?_
      rw [Ne, QuotientGroup.eq_one_iff]
      exact hxZ
    obtain ⟨w, hw, hw1⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp hQZ.center_nontrivial
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective w
    refine ⟨z, ?_, ?_⟩
    · rw [hmem]
      intro y
      apply MaxClass.commutator_mem_center
      exact (Subgroup.mem_center_iff.mp hw (y : Q ⧸ Z)).symm
    · rwa [Ne, QuotientGroup.eq_one_iff] at hw1
  have hsup : Z ⊔ Subgroup.zpowers z = Z₂ := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hZZ₂ (Subgroup.zpowers_le.mpr hzZ₂))
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup (Z ⊔ Subgroup.zpowers z))
    have hk2 : 2 ≤ k := by
      by_contra hlt
      apply hzZ
      have hle : Nat.card ↥(Z ⊔ Subgroup.zpowers z) ≤ Nat.card Z := by
        rw [hk, hZcard]
        calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
          _ = p := pow_one p
      exact (Subgroup.eq_of_le_of_card_ge le_sup_left hle).ge
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    rw [hk]
    calc Nat.card Z₂ ≤ p ^ 2 := hZ₂card
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
  have hcent : Subgroup.centralizer (Z₂ : Set Q) = Subgroup.centralizer ({z} : Set Q) := by
    refine le_antisymm (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzZ₂)) ?_
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have hle : Z₂ ≤ Subgroup.centralizer ({y} : Set Q) := by
      rw [← hsup]
      refine sup_le ?_
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hy.symm))
      intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.mp hc y).symm
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have hidx : (Subgroup.centralizer ({z} : Set Q)).index = p := by
    have h := MaxClass.card_le_of_commutator_mem_center z ⊤ (fun g _ => hcomm z hzZ₂ g)
    rw [Subgroup.card_top, hZcard, ← (Subgroup.centralizer ({z} : Set Q)).card_mul_index] at h
    have hle : (Subgroup.centralizer ({z} : Set Q)).index ≤ p :=
      Nat.le_of_mul_le_mul_left h Nat.card_pos
    have hne : (Subgroup.centralizer ({z} : Set Q)).index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      intro htop
      apply hzZ
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({z} : Set Q) := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    have hdvd : (Subgroup.centralizer ({z} : Set Q)).index ∣ p ^ n := by
      rw [← hn]
      exact Subgroup.index_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rw [hj] at hle hne ⊢
    have hj1 : j ≤ 1 := (Nat.pow_le_pow_iff_right hp1).mp (by rwa [pow_one])
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hne (pow_zero p)
    rw [show j = 1 by omega, pow_one]
  refine ⟨by rw [hcent]; exact hidx, ?_⟩
  rw [hcent, Subgroup.mem_centralizer_singleton_iff]
  intro hxz
  apply hzZ
  rw [← hZ₂C]
  exact Subgroup.mem_inf.mpr ⟨hzZ₂, Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm⟩

end CFSG.Walter.W67.Sec65
