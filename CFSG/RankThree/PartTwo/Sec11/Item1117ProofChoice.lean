module

public import CFSG.RankThree.PartTwo.Sec11.DataExistsG
public import CFSG.RankThree.PartTwo.KFacts.KS44Transport

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1117Proof

section Std


variable {G : Type} [Group G] [Finite G]

theorem inducesStdKind_of_map_conj {Y : Subgroup G} {c k : G} (hkc : k * c = c * k)
    {κ : KFacts.AutKind}
    (hf : KFacts.InducesStdKind (Y.map (MulAut.conj k).toMonoidHom) c κ) :
    KFacts.InducesStdKind Y c κ := by
  set φ := (MulAut.conj k).toMonoidHom with hφ
  have hφc : φ c = c := by
    rw [hφ]
    change k * c * k⁻¹ = c
    rw [hkc, mul_inv_cancel_right]
  have hcN' := hf.mem_normalizer
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hcN' ⊢
    apply Subgroup.map_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective
    change (Y.map (MulAut.conj c).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      Y.map (MulAut.conj k).toMonoidHom
    rw [map_conj_map_conj, hkc, ← map_conj_map_conj]
    exact hcN'
  refine KFacts.InducesStdKind.of_map φ Y
    (fun l => KFacts.thetaQuotMap_iff_of_injective φ (MulAut.conj k).injective Y l) hcN ?_
  rw [hφc]
  exact hf

variable {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}

theorem exists_choice_g_not_field (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h119 : Item119) (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hA : A = Subgroup.closure {c, a, d}) (hnf : ¬ KFacts.InducesStdKind Y c .field) :
    ∃ (a' : G) (Y' : Subgroup G) (g : G), Sec11Std G A c L a' R Y' ∧ a' ∈ A ∧
      a' ∉ Subgroup.closure ({c, d} : Set G) ∧ (∃ k : ℕ, g ^ 3 ^ k = 1) ∧
      g ∈ Y' ⊓ Subgroup.normalizer (A : Set G) ∧ g ∈ Subgroup.normalizer (R : Set G) ∧
      g ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
      g * c * g⁻¹ ∈ Subgroup.closure {c, d} ∧ ¬ KFacts.InducesStdKind Y' c .field := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := h.mem_A
  have haA := h.a_mem
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hdA : d ∈ A := hdAL.1
  obtain ⟨-, hacd, hd1⟩ := h.not_mem_facts hdL hA
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) h.ne_one
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hexp d hdA) hd1
  obtain ⟨-, -, -, -, hdK⟩ := basic_facts_of_conj h45 h hdL hA haA hacd
  have hdY : d ∈ Y := h.sec11K_le hdK
  have hYC := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe haA h.a_ne_one Y
      h.mem_thetaComponentsAt_Y
  have hWd : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    (h117 G A c L a R Y h d hdL (Subgroup.zpowers d) (Subgroup.zpowers_le.mpr hdA)
      (by rw [Nat.card_zpowers, hd3])).mpr rfl
  have hcad : c ∉ Subgroup.closure ({a, d} : Set G) := by
    intro hc
    have hle : A ≤ Subgroup.closure ({a, d} : Set G) := by
      rw [hA, Subgroup.closure_le]
      rintro z (rfl | rfl | rfl)
      · exact hc
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm a haA d hdA) (hexp a haA) (hexp d hdA)
    rw [h.card_eq] at h1
    omega
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hd
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      rintro z (rfl | rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hd
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hcomm c hcA a haA) (hexp c hcA) (hexp a haA)
    rw [h.card_eq] at h1
    omega
  obtain ⟨-, hacY⟩ := h.autIn_facts h119 h45 hdL hA
  obtain ⟨g₁, t, hg₁Y, hg₁A, htY, htA, ⟨k₁, hk₁⟩, hg₁cube, hg₁ne, hinv⟩ :=
    h.exists_g_t h119 h45 hdL hA
  have hg₁a : g₁ * a = a * g₁ := Subgroup.mem_centralizer_singleton_iff.mp (hYC hg₁Y)
  have hta : t * a = a * t := Subgroup.mem_centralizer_singleton_iff.mp (hYC htY)
  have hg₁d : g₁ * d = d * g₁ := Sec12.commute_of_conj_mem_zpowers hd3
    ((Subgroup.mem_normalizer_iff.mp (hWd hg₁A) d).mp (Subgroup.mem_zpowers d)) hk₁
  have hu := ActOnA.conj_mul_inv_mem_zpowers hcomm hexp hA hacd hcad hg₁A htA hg₁a hg₁d hta
    (hWd htA) hg₁cube hinv hg₁Y htY hAY hdY hacY
  have hne : g₁ * c * g₁⁻¹ ≠ c := by
    intro he
    obtain ⟨z, hz, hz'⟩ := hg₁ne
    apply hz'
    have hgc : g₁ * c = c * g₁ := mul_inv_eq_iff_eq_mul.mp he
    have hle : A ≤ Subgroup.centralizer ({g₁} : Set G) := by
      rw [hA, Subgroup.closure_le]
      rintro w (rfl | rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hgc.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hg₁a.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hg₁d.symm
    have hzg := Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
    rw [← hzg, mul_inv_cancel_right]
  set D := Subgroup.closure ({c, d} : Set G) with hD
  have hcD : c ∈ D := Subgroup.subset_closure (by simp)
  have hdD : d ∈ D := Subgroup.subset_closure (by simp)
  have hgcD : g₁ * c * g₁⁻¹ ∈ D := by
    have e : g₁ * c * g₁⁻¹ = (g₁ * c * g₁⁻¹ * c⁻¹) * c := by group
    rw [e]
    exact D.mul_mem (Subgroup.zpowers_le.mpr hdD hu) hcD
  have hgcH : g₁ * c * g₁⁻¹ ∉ Subgroup.zpowers c := by
    intro hmem
    obtain ⟨β, hβ⟩ := Subgroup.mem_zpowers_iff.mp hu
    have huc : d ^ β ∈ Subgroup.zpowers c := by
      rw [hβ]
      exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
    by_cases h3 : (3 : ℤ) ∣ β
    · apply hne
      have h1 : g₁ * c * g₁⁻¹ * c⁻¹ = 1 := by
        rw [← hβ, ActOnA.zpow_eq_one_of_dvd (hexp d hdA) h3]
      calc g₁ * c * g₁⁻¹ = (g₁ * c * g₁⁻¹ * c⁻¹) * c := by group
        _ = c := by rw [h1, one_mul]
    · exact hdc (ActOnA.mem_of_zpow_mem (hexp d hdA) huc h3)
  have hR3 : IsPGroup 3 R := h.isSylowOf.isPGroup
  have hRH := h.isSylowOf.le
  have hRW : R ≤ Subgroup.normalizer (A : Set G) := by
    have hA113 := (h113 G A c L a R Y h).1
    intro r hr
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [SetLike.mem_coe, hA113] at hz ⊢
    have hle : Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} ≤
        (Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}).comap (MulAut.conj r).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro y ⟨hyR, hy3⟩
      refine Subgroup.subset_closure ⟨R.mul_mem (R.mul_mem hr hyR) (R.inv_mem hr), ?_⟩
      change (r * y * r⁻¹) ^ 3 = 1
      rw [conj_pow, hy3, mul_one, mul_inv_cancel]
    exact hle hz
  have hRCD : R ≤ Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer (D : Set G) := by
    intro y hy
    refine ⟨hRW hy, ChooseG.mem_centralizer_of_le ?_⟩
    obtain ⟨k, hk⟩ := hR3 ⟨y, hy⟩
    have hyk : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [hD, Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Sec12.commute_of_conj_mem_zpowers hc3
        ((Subgroup.mem_normalizer_iff.mp (hRH hy) _).mp (Subgroup.mem_zpowers _)) hyk).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Sec12.commute_of_conj_mem_zpowers hd3
        ((Subgroup.mem_normalizer_iff.mp (hWd (hRW hy)) _).mp (Subgroup.mem_zpowers _)) hyk).symm
  have hRsyl : IsSylowOf 3 R (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G)) := by
    have := h.isSylowOf_inf
    rwa [inf_of_le_left hRW] at this
  have hCK : Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer (D : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) := by
    intro z hz
    refine ⟨?_, hz.1⟩
    have hzc : z * c = c * z := (Subgroup.mem_centralizer_iff.mp hz.2 c hcD).symm
    have hzC : z ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzc
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at hzC
    exact Subgroup.centralizer_le_normalizer _ hzC
  have hg₁D : g₁ ∈ Subgroup.normalizer (D : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have hle : D ≤ D.comap (MulAut.conj g₁).toMonoidHom := by
      rw [hD, Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact hgcD
      · change g₁ * w * g₁⁻¹ ∈ D
        rw [hg₁d, mul_inv_cancel_right]
        exact hdD
    exact hle hz
  obtain ⟨k, hkC, hkR⟩ :=
    ChooseG.exists_conj_mem_normalizer hg₁A hg₁D ⟨k₁, hk₁⟩ hRCD hRsyl hCK
  have hkW : k ∈ Subgroup.normalizer (A : Set G) := hkC.1
  have hkD : ∀ e ∈ D, k * e * k⁻¹ = e := fun e he => by
    have hek := Subgroup.mem_centralizer_iff.mp hkC.2 e he
    rw [← hek, mul_inv_cancel_right]
  have hkD' : ∀ e ∈ D, k⁻¹ * e * k = e := fun e he => by
    calc k⁻¹ * e * k = k⁻¹ * (k * e * k⁻¹) * k := by rw [hkD e he]
      _ = e := by group
  have hkL : k⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    h.normalizer_le_normalizer_L h45 (inv_mem (hCK hkC).1)
  set φ := MulAut.conj k⁻¹ with hφ
  have hφapp : ∀ x, φ x = k⁻¹ * x * k := fun x => by rw [hφ, MulAut.conj_apply, inv_inv]
  have ha'A : φ a ∈ A := by
    rw [hφapp]
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hkW) a).mp haA
    rwa [inv_inv] at this
  have ha'cd : φ a ∉ D := by
    intro hm
    apply hacd
    have e : a = k * φ a * k⁻¹ := by rw [hφapp]; group
    rw [e, hkD _ hm]
    exact hm
  have hY' : Y.map φ.toMonoidHom ∈ thetaComponentsAt 3 (φ a) :=
    map_mem_thetaComponentsAt φ h.mem_thetaComponentsAt_Y
  have hKY' : sec11K L (φ a) ≤ Y.map φ.toMonoidHom := by
    rw [ChooseG.sec11K_map_conj hkL]
    exact Subgroup.map_mono h.sec11K_le
  have hstd' := h.change_a h45 hdL hA ha'A ha'cd hY' hKY'
  have hgc' : φ g₁ * c * (φ g₁)⁻¹ = g₁ * c * g₁⁻¹ := by
    rw [hφapp]
    calc k⁻¹ * g₁ * k * c * (k⁻¹ * g₁ * k)⁻¹ = k⁻¹ * (g₁ * (k * c * k⁻¹) * g₁⁻¹) * k := by
          group
      _ = k⁻¹ * (g₁ * c * g₁⁻¹) * k := by rw [hkD c hcD]
      _ = g₁ * c * g₁⁻¹ := hkD' _ hgcD
  refine ⟨φ a, Y.map φ.toMonoidHom, φ g₁, hstd', ha'A, ha'cd,
    ⟨k₁, by rw [← map_pow, hk₁, map_one]⟩, ⟨⟨g₁, hg₁Y, rfl⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hφapp]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem hkW) hg₁A) hkW
  · rw [hφapp]
    exact hkR
  · intro hH
    apply hgcH
    have := (Subgroup.mem_normalizer_iff.mp hH c).mp (Subgroup.mem_zpowers c)
    rwa [hgc'] at this
  · rw [hgc']
    exact hgcD
  ·
    have hkc : k⁻¹ * c = c * k⁻¹ := by
      calc k⁻¹ * c = k⁻¹ * c * k * k⁻¹ := by group
        _ = c * k⁻¹ := by rw [hkD' c hcD]
    exact fun hf => hnf (inducesStdKind_of_map_conj hkc hf)

end Std

end Item1117Proof

end CFSG.RankThree.PartTwo.Sec11
