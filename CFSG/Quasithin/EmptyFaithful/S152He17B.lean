module

public import CFSG.Quasithin.EmptyFaithful.S152He11C
public import CFSG.Quasithin.EmptyFaithful.S152He16C

public section

namespace CFSG.Quasithin.He17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
  CFSG.Quasithin.He16
open scoped commutatorElement Pointwise

theorem not_card_twenty {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] (hX : Nat.card X = 60)
    (H : Subgroup X) : Nat.card H ≠ 20 := by
  intro hH
  have hidx : H.index = 3 := by
    have := Subgroup.card_mul_index H
    rw [hH, hX] at this
    omega
  let φ : X →* Equiv.Perm (X ⧸ H) := MulAction.toPermHom X (X ⧸ H)
  have hcard : Nat.card (X ⧸ H) = 3 := by rw [← Subgroup.index_eq_card]; exact hidx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h
    have h1 := Nat.card_le_card_of_injective φ hinj
    rw [hX, Nat.card_perm, hcard] at h1
    norm_num [Nat.factorial] at h1
  · have hHt : H = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have h1 : g ∈ φ.ker := h ▸ Subgroup.mem_top g
      rw [MonoidHom.mem_ker] at h1
      have h2 : φ g ((1 : X) : X ⧸ H) = ((1 : X) : X ⧸ H) := by rw [h1]; rfl
      have h3 : ((g : X) : X ⧸ H) = ((1 : X) : X ⧸ H) := by
        simpa [φ] using h2
      have h4 := QuotientGroup.eq.mp h3
      simpa using H.inv_mem h4
    rw [hHt, Subgroup.card_top, hX] at hH
    omega

theorem false_of_simple_sixty {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] (hX : Nat.card X = 60)
    {Y U : Subgroup X} (hU2 : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index)
    (hYU : U ≤ Subgroup.normalizer (Y : Set X)) (hY5 : ∃ a : ℕ, Nat.card Y = 5 * 2 ^ a) : False := by
  have hU4 : Nat.card U = 4 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hU2
    have h1 := Subgroup.card_mul_index U
    rw [hn, hX] at h1
    rcases Nat.lt_trichotomy n 2 with hlt | heq | hgt
    · exfalso
      interval_cases n <;> omega
    · rw [hn, heq]; norm_num
    · exfalso
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have : 2 ^ (m + 3) * U.index = 8 * (2 ^ m * U.index) := by ring
      omega
  obtain ⟨a, ha⟩ := hY5
  have h5 : 5 ∣ Nat.card (Y ⊔ U : Subgroup X) := by
    have h1 : Nat.card Y ∣ Nat.card (Y ⊔ U : Subgroup X) := Subgroup.card_dvd_of_le le_sup_left
    exact (ha ▸ dvd_mul_right 5 (2 ^ a) : 5 ∣ Nat.card Y).trans h1
  have h4 : 4 ∣ Nat.card (Y ⊔ U : Subgroup X) := by
    have h1 : Nat.card U ∣ Nat.card (Y ⊔ U : Subgroup X) := Subgroup.card_dvd_of_le le_sup_right
    exact (hU4 ▸ h1)
  have h20 : 5 * 4 ∣ Nat.card (Y ⊔ U : Subgroup X) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h5 h4
  have h60 : Nat.card (Y ⊔ U : Subgroup X) ∣ 60 := hX ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk⟩ := h20
  have hk3 : k ∣ 3 := by
    rw [hk] at h60
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 20) (by simpa using h60)
  rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with hk1 | hk3'
  · exact not_card_twenty hX (Y ⊔ U) (by omega)
  · have hHtop : (Y ⊔ U : Subgroup X) = ⊤ :=
      (Subgroup.card_eq_iff_eq_top (Y ⊔ U)).mp (by omega)
    have hYn : Y.Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      rw [eq_top_iff]
      intro x _
      have : x ∈ (Y ⊔ U : Subgroup X) := hHtop ▸ Subgroup.mem_top x
      exact (sup_le Subgroup.le_normalizer hYU) this
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with h | h
    · rw [h, Subgroup.card_bot] at ha
      have : 0 < 2 ^ a := by positivity
      omega
    · rw [h, Subgroup.card_top, hX] at ha
      have h4a : a < 4 := by
        by_contra hge
        have : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases a <;> omega

variable {G : Type} [Group G] [Finite G]

theorem card_modO2Image_Y {H Y : Subgroup G} (hYH : Y ≤ H) (hY5 : (pCoreOf 2 Y).relIndex Y = 5) :
    ∃ a : ℕ, Nat.card (modO2Image H Y) = 5 * 2 ^ a := by
  obtain ⟨ψ, hψ, hker⟩ := exists_modO2_surjection_of_le' hYH
  have h1 := Subgroup.card_ker_mul_card_range ψ
  rw [MonoidHom.range_eq_top.mpr hψ, Subgroup.card_top] at h1
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hker
  have hmul := Subgroup.relIndex_mul_card (H := pCoreOf 2 Y) (K := Y)
  rw [hY5, inf_eq_left.mpr (pCoreOf_le 2 _)] at hmul
  obtain ⟨c, hc⟩ := (IsPGroup.iff_card).1 (pCoreOf_isPGroup 2 Y)
  rw [hc] at hmul
  rw [hb, ← hmul] at h1
  have hd1 : 5 ∣ Nat.card (modO2Image H Y) := by
    have : 5 ∣ 2 ^ b * Nat.card (modO2Image H Y) := h1 ▸ Dvd.intro _ rfl
    exact (Nat.Coprime.pow_right b (by norm_num : Nat.Coprime 5 2)).dvd_of_dvd_mul_left this
  obtain ⟨d, hd⟩ := hd1
  have hdd : d ∣ 2 ^ c := by
    have h2 : 5 * d ∣ 5 * 2 ^ c := by
      rw [← hd]
      exact Dvd.intro_left _ h1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdd
  exact ⟨e, by rw [hd, he]⟩

omit [Finite G] in
theorem modO2Image_le_normalizer {H S Y : Subgroup G} (hSY : S ≤ Subgroup.normalizer (Y : Set G)) :
    modO2Image H S ≤ Subgroup.normalizer (modO2Image H Y : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  intro u hu
  obtain ⟨x, hxH, hxS, rfl⟩ := mem_modO2Image_iff.mp hu
  exact mk_mem_normalizer_modO2Image hxH (hSY hxS)

theorem false_of_chi0 {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5}
    (c : Ctx15204 T Mc M H K₁ K₂ π) {Lc : Subgroup G} (tail : Tail15204 c Lc)
    (hYL : yOf152 T Mc M ≤ Lc) (hχ : IsChi0Block (g0Of T Mc M K₁) Lc) : False := by
  have hLG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp tail.comp
  have hB : K₁ ∈ lFamily (sOf T K₁) :=
    cComp_mem_of_le c.wr.comp₁ le_sup_left (sup_le c.wr.le₁ (S_le_T.trans c.hT.1))
  have hKL : K₁ = Lc := He11.input15204A314_holds G (g0Of T Mc M K₁) (sOf T K₁) K₁ Lc
    tail.hyp.sqtk tail.sylow tail.comp hχ hB tail.le c.quot_K₁
  subst hKL
  obtain ⟨e₂⟩ := modO2_mulEquiv tail.comp
  obtain ⟨e₄⟩ := c.quot_K₁
  let e : ↥(modO2Image (g0Of T Mc M K₁) K₁) ≃* alternatingGroup (Fin 5) :=
    e₂.symm.trans ((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K₁ 2)).trans e₄)
  have : IsSimpleGroup ↥(modO2Image (g0Of T Mc M K₁) K₁) :=
    e.isSimpleGroup (H := alternatingGroup (Fin 5))
  have hcard : Nat.card ↥(modO2Image (g0Of T Mc M K₁) K₁) = 60 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  set L' := modO2Image (g0Of T Mc M K₁) K₁ with hL'
  have hYG : yOf152 T Mc M ≤ g0Of T Mc M K₁ := hYL.trans hLG
  have hYhat : modO2Image (g0Of T Mc M K₁) (yOf152 T Mc M) ≤ L' :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ hYL)
  have hsyl := isSylowTwoOf_modO2Image_inf (S := sOf T K₁) (L := K₁) tail.sylow tail.normal
  have hSN : modO2Image (g0Of T Mc M K₁) (sOf T K₁) ≤
      Subgroup.normalizer (modO2Image (g0Of T Mc M K₁) (yOf152 T Mc M) : Set _) :=
    modO2Image_le_normalizer c.S_le_normalizer_Y
  obtain ⟨a, ha⟩ := card_modO2Image_Y hYG c.y.relIndex_five
  refine false_of_simple_sixty hcard (Y := (modO2Image (g0Of T Mc M K₁) (yOf152 T Mc M)).subgroupOf L')
    (U := (modO2Image (g0Of T Mc M K₁) (sOf T K₁) ⊓ L').subgroupOf L')
    (hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm) hsyl.2.2 ?_ ⟨a, ?_⟩
  · intro q hq
    exact Subgroup.le_normalizer_comap L'.subtype (hSN (Subgroup.mem_inf.mp hq).1)
  · rw [← ha]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYhat).toEquiv

end CFSG.Quasithin.He17
