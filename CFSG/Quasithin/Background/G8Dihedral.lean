module

public import CFSG.Quasithin.Background.G8DihedralBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

namespace G8

theorem le_normalizer_of_commute {A D : Subgroup G} (h : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a) :
    A ≤ Subgroup.normalizer (D : Set G) := by
  intro a ha
  refine mem_normalizer_of_conj_mem (fun d hd => ?_) (fun d hd => ?_)
  · rw [h a ha d hd]; simpa using hd
  · have := h a⁻¹ (A.inv_mem ha) d hd
    rw [this]; simpa using hd

section Finite

variable [Finite G]

theorem exists_dihedral_factor {a : G} (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) {Z : Subgroup G}
    (hZodd : Odd (Nat.card Z)) (hZa : ∀ z ∈ Z, a * z * a⁻¹ ∈ Z)
    (hnt : ∃ z ∈ Z, a * z * a⁻¹ ≠ z) :
    ∃ (h : G) (p : ℕ), h ∈ Z ∧ p.Prime ∧ Odd p ∧ orderOf h = p ∧
      Nonempty (↥(Subgroup.zpowers h ⊔ Subgroup.zpowers a) ≃* DihedralGroup p) := by
  obtain ⟨h, hZ, hp, hinv⟩ := exists_inverted_prime ha2 hZodd hZa hnt
  refine ⟨h, orderOf h, hZ, hp, ?_, rfl, ?_⟩
  · exact hZodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Z hZ)
  · have hane : a ∉ Subgroup.zpowers h := by
      intro hmem
      have haZ : a ∈ Z := (Subgroup.zpowers_le.mpr hZ) hmem
      have hord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
      have := hZodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Z haZ)
      rw [hord] at this
      exact absurd this (by decide)
    exact dihedral_equiv_of_inverting rfl ha2 hinv hane

theorem g8_6_aux : ∀ (n : ℕ) (X A : Subgroup G), Group.IsNilpotent X → Odd (Nat.card X) →
    IsElemAbelian 2 A → A ≤ Subgroup.normalizer (X : Set G) →
    A ⊓ Subgroup.centralizer (X : Set G) = ⊥ → Nat.card A = 2 ^ (n + 1) →
    ∃ (ι : Type) (_ : Fintype ι) (Hs : ι → Subgroup G) (p : ι → ℕ),
      Fintype.card ι = n + 1 ∧ DFam Hs p ∧ A ≤ ⨆ i, Hs i ∧ (∀ i, Hs i ≤ X ⊔ A) ∧
        ∀ i, ∃ h ∈ X, h ∈ Hs i ∧ orderOf h = p i := by
  intro n
  induction n with
  | zero =>
    intro X A hXn hXodd hA hAX hfaith hcard
    have hcard2 : Nat.card A = 2 := by simpa using hcard
    have hAne : A ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hcard2
      omega
    obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have ha2 : a ^ 2 = 1 := hA.2 a haA
    have hnt : ∃ z ∈ X, a * z * a⁻¹ ≠ z := by
      by_contra hcon
      push Not at hcon
      have : a ∈ A ⊓ Subgroup.centralizer (X : Set G) := by
        refine ⟨haA, ?_⟩
        show a ∈ Subgroup.centralizer (X : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        calc z * a = a * z * a⁻¹ * a := by rw [hcon z hz]
          _ = a * z := by group
      rw [hfaith, Subgroup.mem_bot] at this
      exact ha1' this
    obtain ⟨h, p, hZ, hp, hodd, hord, ⟨e⟩⟩ := exists_dihedral_factor ha1' ha2 hXodd
      (fun z hz => (Subgroup.mem_normalizer_iff.mp (hAX haA) z).mp hz) hnt
    refine ⟨Unit, inferInstance, fun _ => Subgroup.zpowers h ⊔ Subgroup.zpowers a, fun _ => p,
      by simp, DFam.single hp hodd e, ?_, ?_, ?_⟩
    · have hz : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr haA
      have hcz : Nat.card (Subgroup.zpowers a) = 2 := by
        rw [Nat.card_zpowers]; exact orderOf_eq_prime ha2 ha1'
      have hAz : A ≤ Subgroup.zpowers a :=
        (Subgroup.eq_of_le_of_card_ge hz (by rw [hcz, hcard2])).ge
      refine hAz.trans ?_
      simp only [iSup_const]
      exact le_sup_right
    · intro i
      exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hZ))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right haA))
    · intro i
      exact ⟨h, hZ, Subgroup.mem_sup_left (Subgroup.mem_zpowers h), hord⟩
  | succ n ih =>
    intro X A hXn hXodd hA hAX hfaith hcard
    have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
      commute_of_isElemAbelian hA ha ha'
    have hXs : Group.IsSolvable X := by
      have := hXn
      infer_instance
    obtain ⟨B, hBA, hBcard⟩ : ∃ B : Subgroup G, B ≤ A ∧ Nat.card B = 2 ^ (n + 1) := by
      have hdvd : 2 ^ (n + 1) ∣ Nat.card A := by
        rw [hcard]; exact pow_dvd_pow 2 (Nat.le_succ _)
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 2 hdvd
      exact ⟨K.map A.subtype, Subgroup.map_subtype_le K, by
        rw [Subgroup.card_map_of_injective A.subtype_injective]; exact hK⟩
    have hBfaith : B ⊓ Subgroup.centralizer (X : Set G) = ⊥ :=
      le_bot_iff.mp (hfaith ▸ inf_le_inf_right _ hBA)
    obtain ⟨D, hDc, -, hDeq⟩ := g8_2_aux hXs hXodd (n + 1) A B hA hAX hBA hBcard hBfaith
    obtain ⟨-, hDA, hBD, hsup⟩ := hDc
    have hcardD : Nat.card D = 2 := by
      have h1 := card_eq_mul_of_complement hAcomm ⟨hBA, hDA, hBD, hsup⟩
      rw [hcard, hBcard] at h1
      have hpos : 0 < 2 ^ (n + 1) := by positivity
      have h2 : 2 ^ (n + 1) * 2 = 2 ^ (n + 1) * Nat.card D := by rw [← h1]; ring
      exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm
    have hDne : D ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hcardD
      omega
    obtain ⟨⟨a, haD⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have haA : a ∈ A := hDA haD
    have ha2 : a ^ 2 = 1 := hA.2 a haA
    have hDz : Subgroup.zpowers a = D := by
      have hz : Subgroup.zpowers a ≤ D := Subgroup.zpowers_le.mpr haD
      have hcz : Nat.card (Subgroup.zpowers a) = 2 := by
        rw [Nat.card_zpowers]; exact orderOf_eq_prime ha2 ha1'
      exact Subgroup.eq_of_le_of_card_ge hz (by rw [hcz, hcardD])
    set X' := X ⊓ Subgroup.centralizer (D : Set G) with hX'
    have hX'X : X' ≤ X := inf_le_left
    have hX'nil : Group.IsNilpotent X' := by
      have := hXn
      exact (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hX'X)).mp inferInstance
    have hX'odd : Odd (Nat.card X') := hXodd.of_dvd_nat (Subgroup.card_dvd_of_le hX'X)
    have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
      le_normalizer_of_commute fun a ha d hd => hAcomm a ha d (hDA hd)
    have hAX' : A ≤ Subgroup.normalizer (X' : Set G) := by
      have key : ∀ g ∈ A, ∀ x ∈ X', g * x * g⁻¹ ∈ X' := by
        intro g hg x hx
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hAX hg) x).mp hx.1,
          (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer D (hAD hg)) x).mp
            hx.2⟩
      intro g hg
      exact mem_normalizer_of_conj_mem (key g hg) (fun x hx => by
        simpa using key g⁻¹ (A.inv_mem hg) x hx)
    have hDX' : D ≤ Subgroup.centralizer (X' : Set G) := by
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp hx.2 d hd).symm
    have hDfaithX : D ⊓ Subgroup.centralizer (X : Set G) = ⊥ :=
      le_bot_iff.mp (hfaith ▸ inf_le_inf_right _ hDA)
    obtain ⟨B₁, hDc₁, hDf⟩ := g8_5_aux hXn hXodd hA hAX hDA hX'X hAX' hDX' hDfaithX
    obtain ⟨-, hB₁A, hDB₁, hsup₁⟩ := hDc₁
    have hB₁card : Nat.card B₁ = 2 ^ (n + 1) := by
      have h1 := card_eq_mul_of_complement hAcomm ⟨hDA, hB₁A, hDB₁, hsup₁⟩
      rw [hcard, hcardD] at h1
      have h2 : 2 * 2 ^ (n + 1) = 2 * Nat.card B₁ := by rw [← h1]; ring
      exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h2).symm
    have hB₁faith : B₁ ⊓ Subgroup.centralizer (X' : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have h1 : y ∈ D := by
        rw [hDeq]
        exact ⟨hB₁A hy.1, hy.2⟩
      have : y ∈ D ⊓ B₁ := ⟨h1, hy.1⟩
      rw [hDB₁, Subgroup.mem_bot] at this
      exact this
    obtain ⟨ι, hι, Hs', p', hcardι, hDF, hB₁le, hHs'le, hodd'⟩ :=
      ih X' B₁ hX'nil hX'odd (isElemAbelian_mono hA hB₁A) (hB₁A.trans hAX') hB₁faith hB₁card
    set W := B₁ ⊔ X' with hW
    set Z := X ⊓ Subgroup.centralizer (W : Set G) with hZ
    have haW : a ∈ Subgroup.centralizer (W : Set G) := by
      rw [hW, centralizer_sup]
      refine ⟨?_, ?_⟩
      · show a ∈ Subgroup.centralizer (B₁ : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact hAcomm b (hB₁A hb) a haA
      · show a ∈ Subgroup.centralizer (X' : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (Subgroup.mem_centralizer_iff.mp hx.2 a haD).symm
    have hZX : Z ≤ X := inf_le_left
    have hZodd : Odd (Nat.card Z) := hXodd.of_dvd_nat (Subgroup.card_dvd_of_le hZX)
    have hZa : ∀ z ∈ Z, a * z * a⁻¹ ∈ Z := by
      intro z hz
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hAX haA) z).mp hz.1, ?_⟩
      show a * z * a⁻¹ ∈ Subgroup.centralizer (W : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwa : w * a = a * w := (Subgroup.mem_centralizer_iff.mp haW w hw).symm ▸ rfl
      have hwz : w * z = z * w := Subgroup.mem_centralizer_iff.mp hz.2 w hw
      have h1 : Commute w a := hwa
      have h2 : Commute w z := hwz
      exact ((h1.mul_right h2).mul_right h1.inv_right).eq
    have hnt : ∃ z ∈ Z, a * z * a⁻¹ ≠ z := by
      by_contra hcon
      push Not at hcon
      have : a ∈ D ⊓ Subgroup.centralizer (Z : Set G) := by
        refine ⟨haD, ?_⟩
        show a ∈ Subgroup.centralizer (Z : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        calc z * a = a * z * a⁻¹ * a := by rw [hcon z hz]
          _ = a * z := by group
      rw [hDf, Subgroup.mem_bot] at this
      exact ha1' this
    obtain ⟨h, p, hZh, hp, hodd, hord, ⟨e⟩⟩ := exists_dihedral_factor ha1' ha2 hZodd hZa hnt
    set K := Subgroup.zpowers h ⊔ Subgroup.zpowers a with hK
    have hKW : K ≤ Subgroup.centralizer (W : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr hZh.2) (Subgroup.zpowers_le.mpr haW)
    have hHs'W : ∀ i, Hs' i ≤ W := fun i => by
      rw [hW, sup_comm]; exact hHs'le i
    have hcomm : ∀ (i : ι) (u : Unit), ∀ x ∈ Hs' i, ∀ y ∈ (fun _ : Unit => K) u, x * y = y * x :=
      fun i _ x hx y hy => Subgroup.mem_centralizer_iff.mp (hKW hy) x (hHs'W i hx)
    have hdis : Disjoint (⨆ i, Hs' i) (⨆ _ : Unit, K) := by
      rw [iSup_const, Subgroup.disjoint_def]
      intro t ht htK
      have htW : t ∈ W := (iSup_le hHs'W : (⨆ i, Hs' i) ≤ W) ht
      exact eq_one_of_central_dihedral hp hodd e htK (fun s hs =>
        (Subgroup.mem_centralizer_iff.mp (hKW hs) t htW).symm)
    refine ⟨ι ⊕ Unit, inferInstance, Sum.elim Hs' (fun _ => K), Sum.elim p' (fun _ => p), ?_,
      DFam.sumElim hDF (DFam.single hp hodd e) hcomm hdis, ?_, ?_, ?_⟩
    · rw [Fintype.card_sum, hcardι, Fintype.card_unit]
    · have hDK : D ≤ K := by
        rw [← hDz]
        exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
      have hle : A ≤ (⨆ i, Hs' i) ⊔ K := by
        rw [← hsup₁]
        exact sup_le (le_sup_of_le_right hDK) (le_sup_of_le_left hB₁le)
      simpa only [iSup_sum, Sum.elim_inl, Sum.elim_inr, iSup_const] using hle
    · rintro (i | u)
      · exact (hHs'le i).trans (sup_le_sup hX'X hB₁A)
      · exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (hZX hZh)))
          (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right haA))
    · rintro (i | u)
      · obtain ⟨h', hh', hmem, hord'⟩ := hodd' i
        exact ⟨h', hX'X hh', hmem, hord'⟩
      · exact ⟨h, hZX hZh, Subgroup.mem_sup_left (Subgroup.mem_zpowers h), hord⟩

omit [Finite G] in
theorem prime_orderOf_eq_of_mem_pGroup {p : ℕ} [Fact p.Prime] {Y : Subgroup G}
    (hY : IsPGroup p Y) {h : G} (hh : h ∈ Y) {q : ℕ} (hq : orderOf h = q) (hqp : q.Prime) :
    q = p := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hY ⟨h, hh⟩
  have : orderOf h = p ^ k := by rw [← Subgroup.orderOf_mk h hh]; exact hk
  rw [hq] at this
  exact ((Nat.Prime.pow_eq_iff hqp).mp this.symm).1.symm

theorem g8_7_aux {X A Y : Subgroup G} {m k : ℕ} (hXn : Group.IsNilpotent X)
    (hXodd : Odd (Nat.card X)) (hA : IsElemAbelian 2 A) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hfaith : A ⊓ Subgroup.centralizer (X : Set G) = ⊥) (hYX : Y ≤ X)
    (hYA : A ≤ Subgroup.normalizer (Y : Set G)) (hcardA : Nat.card A = 2 ^ (m + 1 + (k + 1)))
    (hcardB : Nat.card (A ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) = 2 ^ (m + 1)) :
    ∃ D : Subgroup G, IsSubgroupComplementIn A (A ⊓ Subgroup.centralizer (Y : Set G)) D ∧
      ∃ (ι₁ ι₂ : Type) (_ : Fintype ι₁) (_ : Fintype ι₂) (H₁ : ι₁ → Subgroup G)
        (H₂ : ι₂ → Subgroup G) (p₁ : ι₁ → ℕ) (p₂ : ι₂ → ℕ),
        Fintype.card ι₁ = m + 1 ∧ Fintype.card ι₂ = k + 1 ∧
        DFam (Sum.elim H₁ H₂) (Sum.elim p₁ p₂) ∧
        (A ⊓ Subgroup.centralizer (Y : Set G) ≤ ⨆ i, H₁ i) ∧
        (∀ i, H₁ i ≤ (A ⊓ Subgroup.centralizer (Y : Set G)) ⊔
          (X ⊓ Subgroup.centralizer ((D ⊔ Y : Subgroup G) : Set G))) ∧
        (∀ i, ∃ h ∈ X ⊓ Subgroup.centralizer ((D ⊔ Y : Subgroup G) : Set G), h ∈ H₁ i ∧
          orderOf h = p₁ i) ∧
        (D ≤ ⨆ j, H₂ j) ∧ (∀ j, H₂ j ≤ Y ⊔ D) ∧ (∀ j, ∃ h ∈ Y, h ∈ H₂ j ∧ orderOf h = p₂ j) := by
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    commute_of_isElemAbelian hA ha ha'
  set B := A ⊓ Subgroup.centralizer (Y : Set G) with hB
  have hBA : B ≤ A := inf_le_left
  have hBY : B ≤ Subgroup.centralizer (Y : Set G) := inf_le_right
  have hBfaith : B ⊓ Subgroup.centralizer (X : Set G) = ⊥ :=
    le_bot_iff.mp (hfaith ▸ inf_le_inf_right _ hBA)
  obtain ⟨D, hDc, hDf⟩ := g8_5_aux hXn hXodd hA hAX hBA hYX hYA hBY hBfaith
  obtain ⟨-, hDA, hBD, hsup⟩ := hDc
  have hcardD : Nat.card D = 2 ^ (k + 1) := by
    have h1 := card_eq_mul_of_complement hAcomm ⟨hBA, hDA, hBD, hsup⟩
    rw [hcardA, hcardB] at h1
    have hpos : 0 < 2 ^ (m + 1) := by positivity
    have h2 : 2 ^ (m + 1) * 2 ^ (k + 1) = 2 ^ (m + 1) * Nat.card D := by
      rw [← h1, ← pow_add]
    exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm
  set Z := X ⊓ Subgroup.centralizer ((D ⊔ Y : Subgroup G) : Set G) with hZ
  have hZX : Z ≤ X := inf_le_left
  have hZn : Group.IsNilpotent Z := by
    have := hXn
    exact (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hZX)).mp inferInstance
  have hZodd : Odd (Nat.card Z) := hXodd.of_dvd_nat (Subgroup.card_dvd_of_le hZX)
  have hBDY : ∀ g ∈ B, g ∈ Subgroup.centralizer ((D ⊔ Y : Subgroup G) : Set G) := by
    intro g hg
    rw [centralizer_sup]
    refine ⟨?_, hBY hg⟩
    show g ∈ Subgroup.centralizer (D : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hAcomm g (hBA hg) d (hDA hd)).symm
  have hBZ : B ≤ Subgroup.normalizer (Z : Set G) := by
    have key : ∀ g ∈ B, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
      intro g hg z hz
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hAX (hBA hg)) z).mp hz.1, ?_⟩
      show g * z * g⁻¹ ∈ Subgroup.centralizer ((D ⊔ Y : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 : Commute w g := (Subgroup.mem_centralizer_iff.mp (hBDY g hg) w hw)
      have h2 : Commute w z := Subgroup.mem_centralizer_iff.mp hz.2 w hw
      exact ((h1.mul_right h2).mul_right h1.inv_right).eq
    intro g hg
    exact mem_normalizer_of_conj_mem (key g hg) (fun z hz => by
      simpa using key g⁻¹ (B.inv_mem hg) z hz)
  obtain ⟨m', hm'⟩ : ∃ m', m = m' := ⟨m, rfl⟩
  obtain ⟨ι₁, hι₁, H₁, p₁, hcard₁, hDF₁, hBle, hle₁, hodd₁⟩ :=
    g8_6_aux m Z B hZn hZodd (isElemAbelian_mono hA hBA) hBZ hDf hcardB
  have hYn : Group.IsNilpotent Y := by
    have := hXn
    exact (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hYX)).mp inferInstance
  have hYodd : Odd (Nat.card Y) := hXodd.of_dvd_nat (Subgroup.card_dvd_of_le hYX)
  have hDfaithY : D ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 : y ∈ B := ⟨hDA hy.1, hy.2⟩
    have : y ∈ B ⊓ D := ⟨h1, hy.1⟩
    rw [hBD, Subgroup.mem_bot] at this
    exact this
  obtain ⟨ι₂, hι₂, H₂, p₂, hcard₂, hDF₂, hDle, hle₂, hodd₂⟩ :=
    g8_6_aux k Y D hYn hYodd (isElemAbelian_mono hA hDA) (hDA.trans hYA) hDfaithY hcardD
  have hYD : Y ⊔ D ≤ Subgroup.centralizer ((Z ⊔ B : Subgroup G) : Set G) := by
    rw [centralizer_sup]
    refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have := Subgroup.mem_centralizer_iff.mp hz.2 y
        (Subgroup.mem_sup_right hy : y ∈ D ⊔ Y)
      exact this.symm
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp (hBY hb) y hy).symm
    · intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have := Subgroup.mem_centralizer_iff.mp hz.2 d (Subgroup.mem_sup_left hd : d ∈ D ⊔ Y)
      exact this.symm
    · intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hAcomm b (hBA hb) d (hDA hd)
  have hcomm : ∀ i j, ∀ x ∈ H₁ i, ∀ y ∈ H₂ j, x * y = y * x := by
    intro i j x hx y hy
    have hx' : x ∈ Z ⊔ B := hle₁ i hx
    exact Subgroup.mem_centralizer_iff.mp (hYD (hle₂ j hy)) x hx'
  have hdis : Disjoint (⨆ i, H₁ i) (⨆ j, H₂ j) := by
    rw [Subgroup.disjoint_def]
    intro t ht₁ ht₂
    have hcomm' : ∀ s ∈ ⨆ i, H₁ i, s * t = t * s := fun s hs =>
      iSup_commute (fun i j x hx y hy => hcomm i j x hx y hy) s hs t ht₂
    exact hDF₁.center t ht₁ hcomm'
  refine ⟨D, ⟨hBA, hDA, hBD, hsup⟩, ι₁, ι₂, hι₁, hι₂, H₁, H₂, p₁, p₂, hcard₁, hcard₂,
    DFam.sumElim hDF₁ hDF₂ hcomm hdis, hBle, ?_, ?_, hDle, hle₂, hodd₂⟩
  · intro i
    have := hle₁ i
    rwa [sup_comm] at this
  · intro i
    obtain ⟨h, hhZ, hmem, hord⟩ := hodd₁ i
    exact ⟨h, hhZ, hmem, hord⟩

theorem g8_8_aux {X A : Subgroup G} {p n : ℕ} [Fact p.Prime] (hXn : Group.IsNilpotent X)
    (hXodd : Odd (Nat.card X)) (hA : IsElemAbelian 2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hfaith : A ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (hcard : Nat.card A = 2 ^ (n + 1)) (hnt : ¬ A ≤ Subgroup.centralizer (pCoreOf p X : Set G)) :
    ∃ (ι : Type) (_ : Fintype ι) (Hs : ι → Subgroup G) (q : ι → ℕ),
      Fintype.card ι = n + 1 ∧ DFam Hs q ∧ A ≤ ⨆ i, Hs i ∧ (∀ i, Hs i ≤ X ⊔ A) ∧ ∃ i, q i = p := by
  set Y := pCoreOf p X with hY
  have hYX : Y ≤ X := pCoreOf_le p X
  have hYp : IsPGroup p Y := pCoreOf_isPGroup p X
  have hYA : A ≤ Subgroup.normalizer (Y : Set G) :=
    fun a ha => normalizer_le_normalizer_pCoreOf p X (hAX ha)
  have hYn : Group.IsNilpotent Y := by
    have := hXn
    exact (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hYX)).mp inferInstance
  have hYodd : Odd (Nat.card Y) := hXodd.of_dvd_nat (Subgroup.card_dvd_of_le hYX)
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    commute_of_isElemAbelian hA ha ha'
  set B := A ⊓ Subgroup.centralizer (Y : Set G) with hB
  have hBA : B ≤ A := inf_le_left
  have hBne : B ≠ A := by
    intro h
    apply hnt
    rw [← h]
    exact inf_le_right
  obtain ⟨m, hm⟩ := ((isPGroup_of_isElemAbelian hA).to_le hBA).exists_card_eq
  have hmn : m < n + 1 := by
    by_contra hge
    push Not at hge
    have : Nat.card A ≤ Nat.card B := by
      rw [hcard, hm]; exact Nat.pow_le_pow_right (by norm_num) hge
    exact hBne (Subgroup.eq_of_le_of_card_ge hBA this)
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  ·
    have hBbot : B = ⊥ := Subgroup.card_eq_one.mp (by rw [hm, hm0]; rfl)
    obtain ⟨ι, hι, Hs, q, hcardι, hDF, hAle, hle, hodd⟩ :=
      g8_6_aux n Y A hYn hYodd hA hYA hBbot hcard
    have hι' : Nonempty ι := by
      rw [← Fintype.card_pos_iff, hcardι]; exact Nat.succ_pos n
    obtain ⟨i₀⟩ := hι'
    refine ⟨ι, hι, Hs, q, hcardι, hDF, hAle, fun i => (hle i).trans (sup_le_sup hYX le_rfl), i₀, ?_⟩
    obtain ⟨h, hhY, -, hord⟩ := hodd i₀
    exact prime_orderOf_eq_of_mem_pGroup hYp hhY hord (hDF.prime i₀)
  ·
    obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    obtain ⟨k', hk'⟩ : ∃ k', n = m' + 1 + k' := ⟨n - (m' + 1), by omega⟩
    have hcardA' : Nat.card A = 2 ^ (m' + 1 + (k' + 1)) := by
      rw [hcard]; congr 1; omega
    obtain ⟨D, hDc, ι₁, ι₂, hι₁, hι₂, H₁, H₂, p₁, p₂, hc₁, hc₂, hDF, hBle, hle₁, hodd₁, hDle,
      hle₂, hodd₂⟩ := g8_7_aux hXn hXodd hA hAX hfaith hYX hYA hcardA' hm
    obtain ⟨-, hDA, hBD, hsup⟩ := hDc
    have hι₂' : Nonempty ι₂ := by
      rw [← Fintype.card_pos_iff, hc₂]; exact Nat.succ_pos k'
    obtain ⟨j₀⟩ := hι₂'
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim H₁ H₂, Sum.elim p₁ p₂, ?_, hDF, ?_, ?_,
      Sum.inr j₀, ?_⟩
    · rw [Fintype.card_sum, hc₁, hc₂]; omega
    · rw [iSup_sum, ← hsup]
      exact sup_le_sup hBle hDle
    · rintro (i | j)
      · exact (hle₁ i).trans (sup_le (hBA.trans le_sup_right)
          (inf_le_left.trans le_sup_left))
      · exact (hle₂ j).trans (sup_le (hYX.trans le_sup_left) (hDA.trans le_sup_right))
    · obtain ⟨h, hhY, -, hord⟩ := hodd₂ j₀
      exact prime_orderOf_eq_of_mem_pGroup hYp hhY hord (hDF.prime (Sum.inr j₀))

end Finite

end G8

section Finite

variable [Finite G]

theorem g8_6 {X P A : Subgroup G} (h : G81 X P A) {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card A = 2 ^ n) (hfaith : A ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    ∃ (Hs : Fin n → Subgroup G) (p : Fin n → ℕ), IsDihedralFamily Hs p ∧ A ≤ ⨆ i, Hs i ∧
      (⨆ i, Hs i) ≤ X ⊔ A ∧ ∀ i, ∃ x ∈ X, x ∈ Hs i ∧ orderOf x = p i := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  obtain ⟨ι, hι, Hs, p, hcardι, hDF, hAle, hle, hodd⟩ := G8.g8_6_aux n' X A h.nilpotent h.odd
    h.elemAbelian (h.le_pGroup.trans h.le_normalizer) hfaith hcard
  let e : Fin (n' + 1) ≃ ι := (Fintype.equivFinOfCardEq hcardι).symm
  refine ⟨Hs ∘ e, p ∘ e, (hDF.comp_equiv e).toIsDihedralFamily, ?_, ?_, fun i => hodd (e i)⟩
  · have : (⨆ i, (Hs ∘ e) i) = ⨆ i, Hs i := Equiv.iSup_comp (g := Hs) e
    rw [this]; exact hAle
  · exact iSup_le fun i => hle (e i)

theorem g8_7 {X P A Y : Subgroup G} (h : G81 X P A) {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hfaith : A ⊓ Subgroup.centralizer (X : Set G) = ⊥) (hYX : Y ≤ X)
    (hYA : A ≤ Subgroup.normalizer (Y : Set G)) (hcardA : Nat.card A = 2 ^ (m + k))
    (hcardB : Nat.card (A ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) = 2 ^ m) :
    ∃ D : Subgroup G, IsSubgroupComplementIn A (A ⊓ Subgroup.centralizer (Y : Set G)) D ∧
      ∃ (Hs : Fin (m + k) → Subgroup G) (p : Fin (m + k) → ℕ), IsDihedralFamily Hs p ∧
        (A ⊓ Subgroup.centralizer (Y : Set G) ≤ ⨆ i : Fin m, Hs (Fin.castAdd k i)) ∧
        ((⨆ i : Fin m, Hs (Fin.castAdd k i)) ≤ (A ⊓ Subgroup.centralizer (Y : Set G)) ⊔
          (X ⊓ Subgroup.centralizer ((D ⊔ Y : Subgroup G) : Set G))) ∧
        (D ≤ ⨆ j : Fin k, Hs (Fin.natAdd m j)) ∧ ((⨆ j : Fin k, Hs (Fin.natAdd m j)) ≤ Y ⊔ D) ∧
        (∀ i : Fin m, ∃ x ∈ X, x ∈ Hs (Fin.castAdd k i) ∧ orderOf x = p (Fin.castAdd k i)) ∧
        (∀ j : Fin k, ∃ x ∈ Y, x ∈ Hs (Fin.natAdd m j) ∧ orderOf x = p (Fin.natAdd m j)) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm.ne'
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
  obtain ⟨D, hDc, ι₁, ι₂, hι₁, hι₂, H₁, H₂, p₁, p₂, hc₁, hc₂, hDF, hBle, hle₁, hodd₁, hDle,
    hle₂, hodd₂⟩ := G8.g8_7_aux h.nilpotent h.odd h.elemAbelian
    (h.le_pGroup.trans h.le_normalizer) hfaith hYX hYA hcardA hcardB
  let e₁ : Fin (m' + 1) ≃ ι₁ := (Fintype.equivFinOfCardEq hc₁).symm
  let e₂ : Fin (k' + 1) ≃ ι₂ := (Fintype.equivFinOfCardEq hc₂).symm
  let E : Fin (m' + 1 + (k' + 1)) ≃ ι₁ ⊕ ι₂ :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr e₁ e₂)
  have hE₁ : ∀ i, E (Fin.castAdd (k' + 1) i) = Sum.inl (e₁ i) := by intro i; simp [E]
  have hE₂ : ∀ j, E (Fin.natAdd (m' + 1) j) = Sum.inr (e₂ j) := by intro j; simp [E]
  have hI₁ : (⨆ i : Fin (m' + 1), (Sum.elim H₁ H₂ ∘ E) (Fin.castAdd (k' + 1) i)) = ⨆ i, H₁ i := by
    simp only [Function.comp_apply, hE₁, Sum.elim_inl]
    exact Equiv.iSup_comp (g := H₁) e₁
  have hI₂ : (⨆ j : Fin (k' + 1), (Sum.elim H₁ H₂ ∘ E) (Fin.natAdd (m' + 1) j)) = ⨆ j, H₂ j := by
    simp only [Function.comp_apply, hE₂, Sum.elim_inr]
    exact Equiv.iSup_comp (g := H₂) e₂
  refine ⟨D, hDc, Sum.elim H₁ H₂ ∘ E, Sum.elim p₁ p₂ ∘ E,
    (hDF.comp_equiv E).toIsDihedralFamily, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hI₁]; exact hBle
  · rw [hI₁]
    exact iSup_le fun i => hle₁ i
  · rw [hI₂]; exact hDle
  · rw [hI₂]; exact iSup_le hle₂
  · intro i
    obtain ⟨x, hx, hmem, hord⟩ := hodd₁ (e₁ i)
    refine ⟨x, hx.1, ?_, ?_⟩
    · show x ∈ (Sum.elim H₁ H₂) (E (Fin.castAdd (k' + 1) i))
      rw [hE₁]; exact hmem
    · show orderOf x = (Sum.elim p₁ p₂) (E (Fin.castAdd (k' + 1) i))
      rw [hE₁]; exact hord
  · intro j
    obtain ⟨x, hx, hmem, hord⟩ := hodd₂ (e₂ j)
    refine ⟨x, hx, ?_, ?_⟩
    · show x ∈ (Sum.elim H₁ H₂) (E (Fin.natAdd (m' + 1) j))
      rw [hE₂]; exact hmem
    · show orderOf x = (Sum.elim p₁ p₂) (E (Fin.natAdd (m' + 1) j))
      rw [hE₂]; exact hord

theorem g8_8 {X P A : Subgroup G} (h : G81 X P A) {p n : ℕ} (hp : p.Prime)
    (hcard : Nat.card A = 2 ^ n) (hfaith : A ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (hnt : ¬ A ≤ Subgroup.centralizer (pCoreOf p X : Set G)) :
    ∃ (Hs : Fin n → Subgroup G) (q : Fin n → ℕ), IsDihedralFamily Hs q ∧ A ≤ ⨆ i, Hs i ∧
      (⨆ i, Hs i) ≤ X ⊔ A ∧ ∀ i : Fin n, i.val = 0 → q i = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : n ≠ 0 := by
    rintro rfl
    apply hnt
    have : A = ⊥ := Subgroup.card_eq_one.mp (by simpa using hcard)
    rw [this]; exact bot_le
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  obtain ⟨ι, hι, Hs, q, hcardι, hDF, hAle, hle, i₀, hi₀⟩ := G8.g8_8_aux h.nilpotent h.odd
    h.elemAbelian (h.le_pGroup.trans h.le_normalizer) hfaith hcard hnt
  let e₀ : Fin (n' + 1) ≃ ι := (Fintype.equivFinOfCardEq hcardι).symm
  let e : Fin (n' + 1) ≃ ι := (Equiv.swap (0 : Fin (n' + 1)) (e₀.symm i₀)).trans e₀
  have he0 : e 0 = i₀ := by simp [e]
  refine ⟨Hs ∘ e, q ∘ e, (hDF.comp_equiv e).toIsDihedralFamily, ?_, ?_, ?_⟩
  · have : (⨆ i, (Hs ∘ e) i) = ⨆ i, Hs i := Equiv.iSup_comp (g := Hs) e
    rw [this]; exact hAle
  · exact iSup_le fun i => hle (e i)
  · intro i hi
    have : i = 0 := Fin.ext hi
    subst this
    simp [he0, hi₀]

end Finite

end CFSG.Quasithin
