module

public import CFSG.Quasithin.Vol2.Ch1Sec3L42Cases
public import CFSG.Quasithin.Vol2.Ch1Sec3L42L5X
public import CFSG.Quasithin.Vol2.Ch1Sec3L42M24
public import CFSG.Quasithin.Vol2.Ch1Sec3L42J4Sub
public import CFSG.Quasithin.Vol2.Ch1EightFourMain

public section

namespace CFSG.Quasithin.L139L42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_le {X : Type*} [Group X] [Finite X] {H : Subgroup X} {y : X}
    (h : ∀ x ∈ H, y * x * y⁻¹ ∈ H) : y ∈ Subgroup.normalizer (H : Set X) := by
  have hle : H.map (MulAut.conj y).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj y).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective])
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨x', hx', hxx⟩ := hx
  have : x' = x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxx
    have := congrArg (fun z => y⁻¹ * z * y) hxx
    simpa [mul_assoc] using this
  rwa [← this]

@[expose] noncomputable def barHom {H L : Subgroup G} (hLH : L ≤ H) : ↥L →* ↥(modO2Image H L) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hLH)).codRestrict _
    fun x => ⟨Subgroup.inclusion hLH x, by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact x.2, rfl⟩

omit [Finite G] in
theorem barHom_surjective {H L : Subgroup G} (hLH : L ≤ H) :
    Function.Surjective (barHom hLH) := by
  rintro ⟨_, ⟨y, hy, rfl⟩⟩
  exact ⟨⟨y, hy⟩, rfl⟩

theorem mem_pCoreOf_of_bar {H L : Subgroup G} (hLH : L ≤ H) {w : G} (hw : w ∈ L)
    (h : ((⟨w, hLH hw⟩ : ↥H) : ModO2 H) ∈ pCoreOf 2 (modO2Image H L)) : w ∈ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := barHom hLH with hρ
  have hker : IsPGroup 2 ρ.ker := by
    intro x
    have hx : Subgroup.inclusion hLH (x : ↥L) ∈ CFSG.pCore 2 ↥H := by
      have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
      change QuotientGroup.mk' (CFSG.pCore 2 ↥H) (Subgroup.inclusion hLH (x : ↥L)) = 1 at h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => ((z : ↥H) : G)) hk
    simpa using this
  set D := (CFSG.Open.pCore 2 ↥(modO2Image H L)).comap ρ with hD
  have hDn : D.Normal := (CFSG.LieType.BorelTits.pCore_normal 2).comap ρ
  have hDp : IsPGroup 2 D :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(modO2Image H L)) 2).comap_of_ker_isPGroup ρ
      hker
  have hDle := CFSG.LieType.BorelTits.le_pCore 2 hDn hDp
  have hwD : (⟨w, hw⟩ : ↥L) ∈ D := by
    obtain ⟨y, hy, hyw⟩ := h
    show ρ ⟨w, hw⟩ ∈ CFSG.Open.pCore 2 ↥(modO2Image H L)
    have : ρ ⟨w, hw⟩ = y := Subtype.ext hyw.symm
    rw [this]
    exact hy
  exact ⟨⟨w, hw⟩, hDle hwD, rfl⟩

theorem inner_of_bar {H L : Subgroup G} (hLH : L ≤ H) {t : G} (htH : t ∈ H)
    (htL : t ∈ Subgroup.normalizer (L : Set G))
    (h : ∃ b ∈ modO2Image H L, ∀ x ∈ modO2Image H L,
      ((⟨t, htH⟩ : ↥H) * x * ((⟨t, htH⟩ : ↥H) : ModO2 H)⁻¹)⁻¹ * (b * x * b⁻¹) ∈
        pCoreOf 2 (modO2Image H L)) :
    ∃ ℓ ∈ L, ∀ x ∈ L, (t * x * t⁻¹)⁻¹ * (ℓ * x * ℓ⁻¹) ∈ pCoreOf 2 L := by
  obtain ⟨_, ⟨ℓ₀, hℓ₀, rfl⟩, hb⟩ := h
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hℓ₀
  refine ⟨ℓ₀, hℓ₀, fun x hx => ?_⟩
  have htx : t * x * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htL x).mp hx
  have hw : (t * x * t⁻¹)⁻¹ * ((ℓ₀ : G) * x * (ℓ₀ : G)⁻¹) ∈ L :=
    mul_mem (inv_mem htx) (mul_mem (mul_mem hℓ₀ hx) (inv_mem hℓ₀))
  refine mem_pCoreOf_of_bar hLH hw ?_
  have h1 := hb ((⟨x, hLH hx⟩ : ↥H) : ModO2 H) ⟨⟨x, hLH hx⟩, by
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact hx, rfl⟩
  have e0 : (⟨(t * x * t⁻¹)⁻¹ * ((ℓ₀ : G) * x * (ℓ₀ : G)⁻¹), hLH hw⟩ : ↥H) =
      ((⟨t, htH⟩ : ↥H) * ⟨x, hLH hx⟩ * (⟨t, htH⟩ : ↥H)⁻¹)⁻¹ * (ℓ₀ * ⟨x, hLH hx⟩ * ℓ₀⁻¹) := by
    ext
    simp
  rw [e0]
  change (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
    (((⟨t, htH⟩ : ↥H) * ⟨x, hLH hx⟩ * (⟨t, htH⟩ : ↥H)⁻¹)⁻¹ * (ℓ₀ * ⟨x, hLH hx⟩ * ℓ₀⁻¹)) ∈ _
  rw [map_mul, map_inv, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact h1

theorem lemma139L42Inner_of
    (h37 : A37ForSQTK) (h312 : A312ForSQTK) (hJ4 : FactJ4L42Inner) : H13.Lemma139L42Inner := by
  intro G _ _ hQ hs hnab T L Y _ hL hY hLY hne hL4 t htT htL
  have htY : t ∈ Subgroup.normalizer (Y : Set G) :=
    (lemma_1_2_8_one_le hQ hs hnab h37 hL hY hLY ⟨htT, htL⟩).2
  set H := Y ⊔ T with hH
  have hS : IsSylowTwoOf T H := ⟨le_sup_right, hY.1, hY.2.2.1⟩
  have hYc : Y ∈ cComp H := cComp_of_isLocal hY
  have hLH : L ≤ H := hLY.trans le_sup_left
  have htH : t ∈ H := (le_sup_right : T ≤ Y ⊔ T) htT
  have hBK : modO2Image H L ≤ modO2Image H Y := Subgroup.map_mono (fun x hx => hLY hx)
  obtain ⟨eL⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hLH
  have hL4' : IsPSL 4 2 1 (ModO2 (modO2Image H L)) := IsPSL.of_mulEquiv eL hL4
  set g : ModO2 H := ((⟨t, htH⟩ : ↥H) : ModO2 H) with hg
  have hnorm : ∀ {M : Subgroup G}, t ∈ Subgroup.normalizer (M : Set G) →
      g ∈ Subgroup.normalizer ((modO2Image H M : Subgroup (ModO2 H)) : Set (ModO2 H)) := by
    intro M hM
    refine mem_normalizer_of_conj_le ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
    refine ⟨⟨t, htH⟩ * y * (⟨t, htH⟩ : ↥H)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      simpa using (Subgroup.mem_normalizer_iff.mp hM _).mp hy
    · rw [map_mul, map_mul, map_inv]
      rfl
  have hgK := hnorm htY
  have hgB := hnorm htL
  refine inner_of_bar hLH htH htL ?_
  rcases lemma_1_2_4_list hQ hs hnab h312 hY.2.2.2 hS hLH (mem_lFamily_of_isLocal hL) hYc hLY with
    heq | hcase | hnq
  · exact absurd (Ch1Four.eq_of_modO2Image_eq hL hY hLY heq) hne
  · rcases cases_of_psl42 hL4' hcase with ⟨hK5, P, hP, hB⟩ | ⟨hB, hK24⟩ | hJ
    · exact exists_inner_l5_sub hK5 hP hB hL4' hgK hgB
    · exact exists_inner_m24_sub hK24 hBK hB hgK hgB
    · exact exists_inner_j4_sub hJ4 hJ hBK hL4' hgK hgB
  · exfalso
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL.2.1.2.1
    have hperf : Group.IsPerfect ↥(modO2Image H L) :=
      Group.IsPerfect.ofSurjective (f := barHom hLH) (barHom_surjective hLH)
    exact false_of_nonquasi_psl42 hBK hperf hL4' hnq

end CFSG.Quasithin.L139L42
