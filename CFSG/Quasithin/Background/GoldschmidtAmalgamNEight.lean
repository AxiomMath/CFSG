module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamNSetup
public import CFSG.Quasithin.Background.F6GoldschmidtListCat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

namespace GoldAmN

variable {D : Type*} [Group D]

theorem isExtensionOf_of_relIndex_two (G M : Subgroup D) (hMG : M ≤ G) (h2 : M.relIndex G = 2)
    {N : Type*} [Group N] (e : ↥M ≃* N) : IsExtensionOf ↥G (Multiplicative (ZMod 2)) N := by
  obtain ⟨φ, hφ, hker⟩ := exists_hom_of_relIndex_two G M h2
  refine ⟨φ, hφ, ?_⟩
  have hker' : φ.ker = M.subgroupOf G := by
    ext g
    exact hker g
  exact ⟨((MulEquiv.subgroupCongr hker').trans (Subgroup.subgroupOfEquivOfLe hMG)).trans e⟩

variable [Finite D] {G₁ G₂ : Subgroup D}

theorem nonempty_mulEquiv_perm_four_left (h : IsGoldschmidtAmalgam G₁ G₂) {x : D}
    (hx : CentThree G₂ x) (hT : Nat.card ↥(G₁ ⊓ G₂) = 8) :
    Nonempty (↥G₁ ≃* Equiv.Perm (Fin 4)) := by
  have hT' := h.toIsGoldschmidtTriple
  have hQ : Nat.card ↥(pCoreOf 2 G₁) = 4 := by
    have := card_inf_eq_two_mul_left hT'
    omega
  have hchar := charTwo_left_of_four_le h hx (by omega)
  refine nonempty_mulEquiv_perm_four G₁ (pCoreOf 2 G₁) (pCoreOf_le 2 G₁)
    (le_normalizer_pCoreOf 2 G₁) hQ (fun v hv => sq_eq_one_of_mem_pCoreOf_left h hx hv) ?_
    (by rw [card_left hT', hT])
  intro g hg hcomm
  exact hchar ⟨hg, Subgroup.mem_centralizer_iff.mpr (fun v hv => (hcomm v hv).symm)⟩

theorem nonempty_mulEquiv_dihedral_four_inf (h : IsGoldschmidtAmalgam G₁ G₂) {x : D}
    (hx : CentThree G₂ x) (hT : Nat.card ↥(G₁ ⊓ G₂) = 8) :
    Nonempty (↥(G₁ ⊓ G₂) ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_perm_four_left h hx hT
  exact nonempty_mulEquiv_dihedral_four G₁ (G₁ ⊓ G₂) inf_le_left e hT

theorem nonempty_mulEquiv_dihedral_twelve_right (h : IsGoldschmidtAmalgam G₁ G₂) {x : D}
    (hx : CentThree G₂ x) (hT : Nat.card ↥(G₁ ⊓ G₂) = 8) {y : D} (hy : y ∈ pCoreOf 2 G₂)
    (hy4 : orderOf y = 4) : Nonempty (↥G₂ ≃* DihedralGroup 12) := by
  have hT' := h.toIsGoldschmidtTriple
  have hQ₁ : Nat.card ↥(pCoreOf 2 G₁) = 4 := by
    have := card_inf_eq_two_mul_left hT'
    omega
  have hQ₂ : Nat.card ↥(pCoreOf 2 G₂) = 4 := by
    have := card_inf_eq_two_mul_right hT'
    omega
  have hchar := charTwo_left_of_four_le h hx (by omega)
  have hne := pCoreOf_ne_of_card_ne h (by omega)
  have hQ₂y : pCoreOf 2 G₂ = Subgroup.zpowers y := by
    refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hy) ?_).symm
    rw [hQ₂, Nat.card_zpowers, hy4]
  obtain ⟨a, haQ₁, haQ₂⟩ := exists_mem_not_mem_of_ne_of_card_eq hne (by rw [hQ₁, hQ₂])
  have haT : a ∈ G₁ ⊓ G₂ := pCoreOf_le_inf_left hT' haQ₁
  have ha2 : a ^ 2 = 1 := sq_eq_one_of_mem_pCoreOf_left h hx haQ₁
  have hay_mem : a * y * a⁻¹ ∈ pCoreOf 2 G₂ :=
    (Subgroup.mem_normalizer_iff.mp (inf_le_normalizer_right haT) y).mp hy
  have hay_ne : a * y * a⁻¹ ≠ y := by
    intro heq
    have hcomm : y * a = a * y := by
      calc y * a = (a * y * a⁻¹) * a := by rw [heq]
        _ = a * y := by group
    have hsup := sup_zpowers_eq_of_relIndex_two (inf_le_left : pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ≤ _)
      (relIndex_inf_pCoreOf_left hT' hne) haQ₁ (fun hh => haQ₂ hh.2)
    have hle : pCoreOf 2 G₁ ≤ Subgroup.centralizer ({y} : Set D) := by
      rw [← hsup]
      refine sup_le ?_ ?_
      · intro r hr
        rw [hQ₂y] at hr
        have hr2 := hr.2
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr2
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ((Commute.refl z).zpow_right k).eq
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hcomm
    have hyT : y ∈ G₁ := (pCoreOf_le_inf_right hT' hy).1
    have hyQ₁ : y ∈ pCoreOf 2 G₁ := by
      refine hchar ⟨hyT, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro v hv
      have := (Subgroup.mem_centralizer_iff.mp (hle hv)) y (Set.mem_singleton y)
      exact this.symm
    have hy2 := sq_eq_one_of_mem_pCoreOf_left h hx hyQ₁
    have : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    rw [hy4] at this
    omega
  have hord : orderOf (a * y * a⁻¹) = 4 := by
    rw [← hy4]
    exact orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective y
  have hay : a * y * a⁻¹ = y⁻¹ := by
    rcases eq_or_eq_inv_of_orderOf_four hy4 (hQ₂y ▸ hay_mem) hord with h1 | h1
    · exact absurd h1 hay_ne
    · exact h1
  have haG₂ : a ∈ G₂ := haT.2
  have hxy : x * y = y * x := hx.centralizes y hy
  have hax : a * x * a⁻¹ = x⁻¹ :=
    hx.inverts a haG₂ haQ₂ (by rw [ha2]; exact (pCoreOf 2 G₂).one_mem)
  have hcard : Nat.card ↥G₂ = 6 * orderOf y := by rw [card_right hT', hT, hy4]
  have := nonempty_mulEquiv_dihedral_vertex G₂ h.quotient₂ hx.mem hy haG₂ hx.order hxy haQ₂ ha2 hax
    hay hcard
  rw [hy4] at this
  exact this

theorem isExtensionOf_right_of_klein (h : IsGoldschmidtAmalgam G₁ G₂) {x : D}
    (hx : CentThree G₂ x) (hT : Nat.card ↥(G₁ ⊓ G₂) = 8)
    (hexp : ∀ y ∈ pCoreOf 2 G₂, y ^ 2 = 1) :
    IsExtensionOf ↥G₂ (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT' := h.toIsGoldschmidtTriple
  have hQ₂ : Nat.card ↥(pCoreOf 2 G₂) = 4 := by
    have := card_inf_eq_two_mul_right hT'
    omega
  have hXcard : Nat.card ↥(Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx.order]
  have hXG : Subgroup.zpowers x ≤ G₂ := (Subgroup.zpowers_le).mpr hx.mem
  have hQG : pCoreOf 2 G₂ ≤ G₂ := pCoreOf_le 2 G₂
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ pCoreOf 2 G₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((show Commute x b from hx.centralizes b hb).zpow_left k).eq
  have hdisj : Subgroup.zpowers x ⊓ pCoreOf 2 G₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz.1
    have hx3 : x ^ 3 = 1 := by rw [← hx.order]; exact pow_orderOf_eq_one x
    have h3 : (x ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [hx3]
    exact eq_one_of_mem_of_pow_three (pCoreOf_isPGroup 2 G₂) hz.2 h3
  have hMle : Subgroup.zpowers x ⊔ pCoreOf 2 G₂ ≤ G₂ := sup_le hXG hQG
  obtain ⟨e₀⟩ := nonempty_mulEquiv_prod_of_sup_eq (Subgroup.zpowers x ⊔ pCoreOf 2 G₂)
    (Subgroup.zpowers x) (pCoreOf 2 G₂) le_sup_left le_sup_right rfl hcomm hdisj
  obtain ⟨eK⟩ := nonempty_mulEquiv_klein_subgroup (pCoreOf 2 G₂) hQ₂
    (fun v hv => hexp v hv)
  have eX : ↥(Subgroup.zpowers x) ≃* Multiplicative (ZMod 3) :=
    mulEquivOfPrimeCardEq hXcard (by simp)
  have hMcard : Nat.card ↥(Subgroup.zpowers x ⊔ pCoreOf 2 G₂) = 12 := by
    rw [Nat.card_congr e₀.toEquiv, Nat.card_prod, hXcard, hQ₂]
  have h2 : (Subgroup.zpowers x ⊔ pCoreOf 2 G₂).relIndex G₂ = 2 := by
    have := Subgroup.relIndex_mul_card (H := Subgroup.zpowers x ⊔ pCoreOf 2 G₂) (K := G₂)
    rw [inf_eq_left.mpr hMle, hMcard, card_right hT', hT] at this
    omega
  exact isExtensionOf_of_relIndex_two G₂ _ hMle h2 (e₀.trans (MulEquiv.prodCongr eX eK))

theorem isGoldCaseCat_of_card_eight (h : IsGoldschmidtAmalgam G₁ G₂) {x : D}
    (hx : CentThree G₂ x) (hT : Nat.card ↥(G₁ ⊓ G₂) = 8) : IsGoldCaseCat G₁ G₂ := by
  obtain ⟨e₁⟩ := nonempty_mulEquiv_perm_four_left h hx hT
  have hD8 := nonempty_mulEquiv_dihedral_four_inf h hx hT
  by_cases hcyc : ∃ y ∈ pCoreOf 2 G₂, orderOf y = 4
  · obtain ⟨y, hy, hy4⟩ := hcyc
    have hD24 := nonempty_mulEquiv_dihedral_twelve_right h hx hT hy hy4
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hD24, ?_, ⟨e₁⟩⟩)))
    rw [inf_comm]
    exact hD8
  · push Not at hcyc
    have hT' := h.toIsGoldschmidtTriple
    have hQ₂ : Nat.card ↥(pCoreOf 2 G₂) = 4 := by
      have := card_inf_eq_two_mul_right hT'
      omega
    have hexp : ∀ y ∈ pCoreOf 2 G₂, y ^ 2 = 1 := by
      intro y hy
      have hdvd : orderOf y ∣ 4 := by
        have := orderOf_dvd_natCard (⟨y, hy⟩ : pCoreOf 2 G₂)
        rwa [Subgroup.orderOf_mk, hQ₂] at this
      have hne4 := hcyc y hy
      have : orderOf y ∣ 2 := by
        have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h4] at hdvd
        obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
        interval_cases i
        · simp [hio]
        · simp [hio]
        · exact absurd (by simpa using hio) hne4
      exact orderOf_dvd_iff_pow_eq_one.mp this
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨e₁⟩, hD8,
      isExtensionOf_right_of_klein h hx hT hexp⟩))))

end GoldAmN

end F6

end CFSG.Quasithin
