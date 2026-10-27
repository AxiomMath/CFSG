module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamNSetup
public import CFSG.Quasithin.Background.F6GoldschmidtList

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

namespace GoldAmN

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem exists_central_involution (h : IsGoldschmidtAmalgam G₁ G₂) {x : D} (hx : CentThree G₂ x)
    (hT : Nat.card ↥(G₁ ⊓ G₂) = 16) :
    ∃ ε : D, ε ∈ pCoreOf 2 G₁ ∧ ε ≠ 1 ∧ ε ^ 2 = 1 ∧ (∀ g ∈ G₁, g * ε * g⁻¹ = ε) ∧
      ε ∉ pCoreOf 2 G₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' := h.toIsGoldschmidtTriple
  have hQ₁ : Nat.card ↥(pCoreOf 2 G₁) = 8 := by
    have := card_inf_eq_two_mul_left hT'
    omega
  have hchar := charTwo_left_of_four_le h hx (by omega)
  have hexp : ∀ q ∈ pCoreOf 2 G₁, q ^ 2 = 1 := fun q hq => sq_eq_one_of_mem_pCoreOf_left h hx hq
  have habel : ∀ a ∈ pCoreOf 2 G₁, ∀ b ∈ pCoreOf 2 G₁, a * b = b * a := fun a ha b hb =>
    mul_comm_of_sq_eq_one (hexp a ha) (hexp b hb) (hexp _ ((pCoreOf 2 G₁).mul_mem ha hb))
  obtain ⟨x₁, hx₁G, hx₁3⟩ := exists_orderOf_eq_three_left hT'
  have hx₁norm : ∀ q ∈ pCoreOf 2 G₁, x₁ * q * x₁⁻¹ ∈ pCoreOf 2 G₁ := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₁ hx₁G) q).mp hq
  have hnc : ¬ ∀ v ∈ pCoreOf 2 G₁, x₁ * v = v * x₁ := by
    intro hall
    have : x₁ ∈ pCoreOf 2 G₁ := hchar ⟨hx₁G, Subgroup.mem_centralizer_iff.mpr
      (fun v hv => (hall v hv).symm)⟩
    exact not_mem_of_isPGroup_two (pCoreOf_isPGroup 2 G₁) hx₁3 this
  have hF := card_inf_centralizer_eq_two (pCoreOf 2 G₁) hQ₁ hx₁3 hx₁norm hnc
  obtain ⟨ε, hεF, hε1⟩ := exists_ne_one_of_card_two hF
  have hεQ : ε ∈ pCoreOf 2 G₁ := hεF.1
  have hεx : x₁ * ε * x₁⁻¹ = ε := by
    have := (Subgroup.mem_centralizer_iff.mp hεF.2) x₁ (Set.mem_singleton x₁)
    rw [this]; group
  have hε2 : ε ^ 2 = 1 := hexp ε hεQ
  have hcentral : ∀ g ∈ G₁, g * ε * g⁻¹ = ε := by
    intro g hg
    have hv : g * ε * g⁻¹ ∈ pCoreOf 2 G₁ :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₁ hg) ε).mp hεQ
    have hyv : (g * x₁ * g⁻¹) * (g * ε * g⁻¹) * (g * x₁ * g⁻¹)⁻¹ = g * ε * g⁻¹ := by
      calc (g * x₁ * g⁻¹) * (g * ε * g⁻¹) * (g * x₁ * g⁻¹)⁻¹
          = g * (x₁ * ε * x₁⁻¹) * g⁻¹ := by group
        _ = g * ε * g⁻¹ := by rw [hεx]
    have hfix : x₁ * (g * ε * g⁻¹) * x₁⁻¹ = g * ε * g⁻¹ := by
      have key : ∀ y v : D, v ∈ pCoreOf 2 G₁ → y * v * y⁻¹ = v →
          (x₁⁻¹ * y ∈ pCoreOf 2 G₁ ∨ x₁ * y ∈ pCoreOf 2 G₁) → x₁ * v * x₁⁻¹ = v := by
        intro y v hvQ hyv' hq
        rcases hq with hq | hq
        · have hqv : (x₁⁻¹ * y) * v = v * (x₁⁻¹ * y) := habel _ hq _ hvQ
          have hqvq : (x₁⁻¹ * y) * v * (x₁⁻¹ * y)⁻¹ = v := by rw [hqv]; group
          calc x₁ * v * x₁⁻¹ = x₁ * ((x₁⁻¹ * y) * v * (x₁⁻¹ * y)⁻¹) * x₁⁻¹ := by rw [hqvq]
            _ = y * v * y⁻¹ := by group
            _ = v := hyv'
        · have hqv : (x₁ * y) * v = v * (x₁ * y) := habel _ hq _ hvQ
          have hqvq : (x₁ * y) * v * (x₁ * y)⁻¹ = v := by rw [hqv]; group
          have h3 : x₁⁻¹ * v * x₁ = v := by
            calc x₁⁻¹ * v * x₁ = x₁⁻¹ * ((x₁ * y) * v * (x₁ * y)⁻¹) * x₁ := by rw [hqvq]
              _ = y * v * y⁻¹ := by group
              _ = v := hyv'
          calc x₁ * v * x₁⁻¹ = x₁ * (x₁⁻¹ * v * x₁) * x₁⁻¹ := by rw [h3]
            _ = v := by group
      exact key (g * x₁ * g⁻¹) (g * ε * g⁻¹) hv hyv
        (conj_order_three_mem G₁ h.quotient₁ hx₁G hg hx₁3)
    have hvF : g * ε * g⁻¹ ∈ pCoreOf 2 G₁ ⊓ Subgroup.centralizer ({x₁} : Set D) :=
      ⟨hv, Subgroup.mem_centralizer_iff.mpr (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        calc z * (g * ε * g⁻¹) = (z * (g * ε * g⁻¹) * z⁻¹) * z := by group
          _ = (g * ε * g⁻¹) * z := by rw [hfix])⟩
    have hv1 : g * ε * g⁻¹ ≠ 1 := by
      intro h1
      apply hε1
      have := congrArg (fun z => g⁻¹ * z * g) h1
      simpa [mul_assoc] using this
    rcases eq_one_or_eq_of_card_two hF hεF hε1 hvF with h1 | h1
    · exact absurd h1 hv1
    · exact h1
  have hεQ₂ : ε ∉ pCoreOf 2 G₂ := by
    intro hmem
    have hle : Subgroup.zpowers ε ≤ pCoreOf 2 G₂ := (Subgroup.zpowers_le).mpr hmem
    have hfixz : ∀ g ∈ G₁, ∀ z ∈ Subgroup.zpowers ε, g * z * g⁻¹ = z := by
      intro g hg z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← conj_zpow, hcentral g hg]
    have hnorm : G₁ ≤ Subgroup.normalizer (Subgroup.zpowers ε : Set D) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz; rw [hfixz g hg z hz]; exact hz
      · intro hz
        have hz' : g * z * g⁻¹ ∈ Subgroup.zpowers ε := hz
        have h4 := hfixz g⁻¹ (G₁.inv_mem hg) _ hz'
        rw [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h4
        rw [← h4] at hz'
        exact hz'
    have hbot := eq_bot_of_le_pCoreOf_right h hx hle hnorm
    have : ε ∈ (⊥ : Subgroup D) := by rw [← hbot]; exact Subgroup.mem_zpowers ε
    exact hε1 (Subgroup.mem_bot.mp this)
  exact ⟨ε, hεQ, hε1, hε2, hcentral, hεQ₂⟩

theorem exists_normal_complement_perm_four (h : IsGoldschmidtAmalgam G₁ G₂) {x : D}
    (hx : CentThree G₂ x) (hT : Nat.card ↥(G₁ ⊓ G₂) = 16) {ε : D}
    (hεQ₁ : ε ∈ pCoreOf 2 G₁) (hε2 : ε ^ 2 = 1) (hεc : ∀ g ∈ G₁, g * ε * g⁻¹ = ε)
    (hεQ₂ : ε ∉ pCoreOf 2 G₂) :
    ∃ K : Subgroup D, K ≤ G₁ ∧ ε ∉ K ∧ K.relIndex G₁ = 2 ∧
      Nonempty (↥K ≃* Equiv.Perm (Fin 4)) := by
  have hT' := h.toIsGoldschmidtTriple
  have hQ₁ : Nat.card ↥(pCoreOf 2 G₁) = 8 := by
    have := card_inf_eq_two_mul_left hT'
    omega
  have hchar := charTwo_left_of_four_le h hx (by omega)
  have hεT : ε ∈ G₁ ⊓ G₂ := pCoreOf_le_inf_left hT' hεQ₁
  have hεcomm : ∀ g ∈ G₁, g * ε = ε * g := fun g hg => by
    have := hεc g hg
    calc g * ε = g * ε * g⁻¹ * g := by group
      _ = ε * g := by rw [this]
  have hodd : Odd ((G₁ ⊓ G₂).relIndex G₁) := by rw [hT'.relIndex_inf_left]; decide
  obtain ⟨K, hKG, hKnorm, hεK, hKidx, hKq⟩ := exists_normal_index_two_not_mem G₁ (G₁ ⊓ G₂)
    (pCoreOf 2 G₂) inf_le_left hodd (relIndex_pCoreOf_right hT') hεT hεQ₂ hεcomm hε2
  refine ⟨K, hKG, hεK, hKidx, ?_⟩
  have hK24 : Nat.card ↥K = 24 := by
    have := Subgroup.relIndex_mul_card (H := K) (K := G₁)
    rw [inf_eq_left.mpr hKG, hKidx, card_left hT', hT] at this
    omega
  have hQ₁G : pCoreOf 2 G₁ ≤ G₁ := pCoreOf_le 2 G₁
  have hKQ : K.relIndex (pCoreOf 2 G₁) = 2 := by
    have hle : K.relIndex (pCoreOf 2 G₁) ≤ K.relIndex G₁ :=
      Subgroup.relIndex_le_of_le_right hQ₁G (by rw [hKidx]; norm_num)
    rw [hKidx] at hle
    have hne1 : K.relIndex (pCoreOf 2 G₁) ≠ 1 := fun h1 =>
      hεK ((Subgroup.relIndex_eq_one.mp h1) hεQ₁)
    have hpos : K.relIndex (pCoreOf 2 G₁) ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_dvd_card (H := K) (K := pCoreOf 2 G₁)
      rw [h0] at this
      exact Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd this)
    omega
  have hV4 : Nat.card ↥(pCoreOf 2 G₁ ⊓ K) = 4 := by
    have := Subgroup.relIndex_mul_card (H := K) (K := pCoreOf 2 G₁)
    rw [hKQ, inf_comm, hQ₁] at this
    omega
  refine nonempty_mulEquiv_perm_four K (pCoreOf 2 G₁ ⊓ K) inf_le_right ?_ hV4
    (fun v hv => sq_eq_one_of_mem_pCoreOf_left h hx hv.1) ?_ hK24
  · exact fun g hg => mem_normalizer_inf (le_normalizer_pCoreOf 2 G₁ (hKG hg))
      (Subgroup.le_normalizer hg)
  · intro g hg hcomm
    have hgG : g ∈ G₁ := hKG hg
    have hcommQ : ∀ q ∈ pCoreOf 2 G₁, g * q = q * g := by
      intro q hq
      by_cases hqK : q ∈ K
      · exact hcomm q ⟨hq, hqK⟩
      · have hεq : ε * q ∈ K := hKq q (hQ₁G hq) hqK
        have hεqV : ε * q ∈ pCoreOf 2 G₁ ⊓ K := ⟨(pCoreOf 2 G₁).mul_mem hεQ₁ hq, hεq⟩
        have h1 := hcomm _ hεqV
        have h2 := hεcomm g hgG
        calc g * q = ε⁻¹ * (ε * g * q) := by group
          _ = ε⁻¹ * (g * ε * q) := by rw [h2]
          _ = ε⁻¹ * (g * (ε * q)) := by rw [mul_assoc]
          _ = ε⁻¹ * ((ε * q) * g) := by rw [h1]
          _ = q * g := by group
    exact ⟨hchar ⟨hgG, Subgroup.mem_centralizer_iff.mpr (fun q hq => (hcommQ q hq).symm)⟩, hg⟩

theorem perm3_center_trivial : ∀ a : Equiv.Perm (Fin 3), (∀ c : Equiv.Perm (Fin 3), a * c = c * a) →
    a = 1 := by
  decide +kernel

theorem isGoldCaseV_of_card_sixteen (h : IsGoldschmidtAmalgam G₁ G₂) {x : D}
    (hx : CentThree G₂ x) (hT : Nat.card ↥(G₁ ⊓ G₂) = 16) : IsGoldCaseV G₁ G₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT' := h.toIsGoldschmidtTriple
  obtain ⟨ε, hεQ₁, hε1, hε2, hεc, hεQ₂⟩ := exists_central_involution h hx hT
  obtain ⟨K, hKG, hεK, hKidx, ⟨eK⟩⟩ :=
    exists_normal_complement_perm_four h hx hT hεQ₁ hε2 hεc hεQ₂
  have hεT : ε ∈ G₁ ⊓ G₂ := pCoreOf_le_inf_left hT' hεQ₁
  have hεG₁ : ε ∈ G₁ := hεT.1
  have hεG₂ : ε ∈ G₂ := hεT.2
  have hεcomm : ∀ g ∈ G₁, g * ε = ε * g := fun g hg => by
    have := hεc g hg
    calc g * ε = g * ε * g⁻¹ * g := by group
      _ = ε * g := by rw [this]
  have hzε : ∀ z ∈ Subgroup.zpowers ε, z = 1 ∨ z = ε := fun z hz =>
    eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hε2 hz
  have hεord : orderOf ε = 2 := orderOf_eq_prime hε2 hε1
  have hZcard : Nat.card ↥(Subgroup.zpowers ε) = 2 := by rw [Nat.card_zpowers, hεord]
  have eZ : ↥(Subgroup.zpowers ε) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hZcard (by simp)
  have hZcomm : ∀ a ∈ Subgroup.zpowers ε, ∀ b ∈ G₁, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((show Commute ε b from (hεcomm b hb).symm).zpow_left k).eq
  have hnotbot : ∀ B : Subgroup D, ε ∉ B → Subgroup.zpowers ε ⊓ B = ⊥ := by
    intro B hB
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    rw [Subgroup.mem_bot]
    rcases hzε z hz1 with h0 | h0
    · exact h0
    · exact absurd (h0 ▸ hz2) hB
  have hKε : K ⊔ Subgroup.zpowers ε = G₁ := sup_zpowers_eq_of_relIndex_two hKG hKidx hεG₁ hεK
  obtain ⟨e₁⟩ := nonempty_mulEquiv_prod_of_sup_eq G₁ (Subgroup.zpowers ε) K
    ((Subgroup.zpowers_le).mpr hεG₁) hKG (by rw [sup_comm]; exact hKε)
    (fun a ha b hb => hZcomm a ha b (hKG hb)) (hnotbot K hεK)
  have hKT : K.relIndex (G₁ ⊓ G₂) = 2 := by
    have hle : K.relIndex (G₁ ⊓ G₂) ≤ K.relIndex G₁ :=
      Subgroup.relIndex_le_of_le_right inf_le_left (by rw [hKidx]; norm_num)
    rw [hKidx] at hle
    have hne1 : K.relIndex (G₁ ⊓ G₂) ≠ 1 := fun h1 =>
      hεK ((Subgroup.relIndex_eq_one.mp h1) hεT)
    have hpos : K.relIndex (G₁ ⊓ G₂) ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_dvd_card (H := K) (K := G₁ ⊓ G₂)
      rw [h0] at this
      exact Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd this)
    omega
  have hA8 : Nat.card ↥(K ⊓ (G₁ ⊓ G₂)) = 8 := by
    have := Subgroup.relIndex_mul_card (H := K) (K := G₁ ⊓ G₂)
    rw [hKT, hT] at this
    omega
  have hAT : (K ⊓ (G₁ ⊓ G₂)).relIndex (G₁ ⊓ G₂) = 2 := by
    rw [Subgroup.inf_relIndex_right]; exact hKT
  have hTsup : (K ⊓ (G₁ ⊓ G₂)) ⊔ Subgroup.zpowers ε = G₁ ⊓ G₂ :=
    sup_zpowers_eq_of_relIndex_two inf_le_right hAT hεT (fun hh => hεK hh.1)
  have hεA : ε ∉ K ⊓ (G₁ ⊓ G₂) := fun hh => hεK hh.1
  obtain ⟨eT⟩ := nonempty_mulEquiv_prod_of_sup_eq (G₁ ⊓ G₂) (Subgroup.zpowers ε)
    (K ⊓ (G₁ ⊓ G₂)) ((Subgroup.zpowers_le).mpr hεT) inf_le_right (by rw [sup_comm]; exact hTsup)
    (fun a ha b hb => hZcomm a ha b hb.2.1) (hnotbot _ hεA)
  obtain ⟨eD⟩ := nonempty_mulEquiv_dihedral_four K (K ⊓ (G₁ ⊓ G₂)) inf_le_left eK hA8
  have hQ₂T := pCoreOf_le_inf_right hT'
  have hQ₂8 : Nat.card ↥(pCoreOf 2 G₂) = 8 := by
    have := card_inf_eq_two_mul_right hT'
    omega
  obtain ⟨eQ⟩ := nonempty_mulEquiv_of_complements (G₁ ⊓ G₂) (Subgroup.zpowers ε)
    (pCoreOf 2 G₂) (K ⊓ (G₁ ⊓ G₂)) ((Subgroup.zpowers_le).mpr hεT) hQ₂T inf_le_right
    (fun t ht => le_normalizer_zpowers_of_central G₁ hεcomm ht.1)
    (by rw [inf_comm]; exact hnotbot _ hεQ₂) (by rw [inf_comm]; exact hnotbot _ hεA)
    (by rw [hT, hQ₂8, hZcard]) (by rw [hT, hA8, hZcard])
  have hεx : ε * x * ε⁻¹ = x⁻¹ := hx.inverts ε hεG₂ hεQ₂ (by rw [hε2]; exact one_mem _)
  have hXG : Subgroup.zpowers x ≤ G₂ := (Subgroup.zpowers_le).mpr hx.mem
  have hZG : Subgroup.zpowers ε ≤ G₂ := (Subgroup.zpowers_le).mpr hεG₂
  have hA₂G : Subgroup.zpowers ε ⊔ Subgroup.zpowers x ≤ G₂ := sup_le hZG hXG
  have hεnorm : Subgroup.zpowers ε ≤ Subgroup.normalizer (Subgroup.zpowers x : Set D) :=
    (Subgroup.zpowers_le).mpr (mem_normalizer_zpowers_of_conj_inv hεx hε2)
  have hXcard : Nat.card ↥(Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx.order]
  have hA₂6 : Nat.card ↥(Subgroup.zpowers ε ⊔ Subgroup.zpowers x) = 6 := by
    have hle := card_sup_le_of_le_normalizer (Subgroup.zpowers ε) (Subgroup.zpowers x) hεnorm
    rw [hZcard, hXcard] at hle
    have h2 : 2 ∣ Nat.card ↥(Subgroup.zpowers ε ⊔ Subgroup.zpowers x) := by
      rw [← hZcard]; exact Subgroup.card_dvd_of_le le_sup_left
    have h3 : 3 ∣ Nat.card ↥(Subgroup.zpowers ε ⊔ Subgroup.zpowers x) := by
      rw [← hXcard]; exact Subgroup.card_dvd_of_le le_sup_right
    have := Nat.card_pos (α := ↥(Subgroup.zpowers ε ⊔ Subgroup.zpowers x))
    omega
  obtain ⟨eA⟩ := nonempty_mulEquiv_perm_three_of_mem (Subgroup.zpowers ε ⊔ Subgroup.zpowers x)
    (x := x) (ε := ε) (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers ε)) hx.order hε2 hεx hA₂6
  have hA₂comm : ∀ a ∈ Subgroup.zpowers ε ⊔ Subgroup.zpowers x, ∀ b ∈ pCoreOf 2 G₂,
      a * b = b * a := by
    intro a ha b hb
    have hle : Subgroup.zpowers ε ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({b} : Set D) := by
      refine sup_le ((Subgroup.zpowers_le).mpr ?_) ((Subgroup.zpowers_le).mpr ?_)
      · refine Subgroup.mem_centralizer_iff.mpr (fun z hz => ?_)
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hεcomm z (hQ₂T hb).1
      · refine Subgroup.mem_centralizer_iff.mpr (fun z hz => ?_)
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (hx.centralizes z hb).symm
    exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) b (Set.mem_singleton b)).symm
  have hdisj₂ : (Subgroup.zpowers ε ⊔ Subgroup.zpowers x) ⊓ pCoreOf 2 G₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwA, hwQ⟩
    rw [Subgroup.mem_bot]
    let w' : ↥(Subgroup.zpowers ε ⊔ Subgroup.zpowers x) := ⟨w, hwA⟩
    have hcen : ∀ b : ↥(Subgroup.zpowers ε ⊔ Subgroup.zpowers x), w' * b = b * w' :=
      fun b => Subtype.ext ((hA₂comm b b.2 w hwQ).symm)
    have h1 : eA w' = 1 := by
      refine perm3_center_trivial _ (fun c => ?_)
      obtain ⟨b, rfl⟩ := eA.surjective c
      rw [← map_mul, ← map_mul, hcen b]
    have : w' = 1 := eA.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  have hTQ : pCoreOf 2 G₂ ⊔ Subgroup.zpowers ε = G₁ ⊓ G₂ :=
    sup_zpowers_eq_of_relIndex_two hQ₂T (relIndex_pCoreOf_right hT') hεT hεQ₂
  have hsup₂ : (Subgroup.zpowers ε ⊔ Subgroup.zpowers x) ⊔ pCoreOf 2 G₂ = G₂ := by
    refine le_antisymm (sup_le hA₂G (pCoreOf_le 2 G₂)) ?_
    calc G₂ = G₁ ⊓ G₂ ⊔ Subgroup.zpowers x := (inf_sup_zpowers_eq_right hT' hx.mem hx.order).symm
      _ = (Subgroup.zpowers ε ⊔ pCoreOf 2 G₂) ⊔ Subgroup.zpowers x := by
        rw [sup_comm (Subgroup.zpowers ε), hTQ]
      _ ≤ (Subgroup.zpowers ε ⊔ Subgroup.zpowers x) ⊔ pCoreOf 2 G₂ := by
        refine sup_le (sup_le ?_ ?_) ?_
        · exact le_sup_of_le_left le_sup_left
        · exact le_sup_right
        · exact le_sup_of_le_left le_sup_right
  obtain ⟨e₂⟩ := nonempty_mulEquiv_prod_of_sup_eq G₂ (Subgroup.zpowers ε ⊔ Subgroup.zpowers x)
    (pCoreOf 2 G₂) hA₂G (pCoreOf_le 2 G₂) hsup₂ hA₂comm hdisj₂
  exact ⟨⟨e₁.trans (MulEquiv.prodCongr eZ eK)⟩, ⟨eT.trans (MulEquiv.prodCongr eZ eD)⟩,
    ⟨e₂.trans (MulEquiv.prodCongr eA (eQ.trans eD))⟩⟩

end GoldAmN

end F6

end CFSG.Quasithin
