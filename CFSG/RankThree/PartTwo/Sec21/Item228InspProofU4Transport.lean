module

public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofU4Model
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228InspProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor d8Comb_four d8Comb2_four exists_conj_into_d8Tor_su
  exists_d8ctx d8Vec_mem_SU permGL_mem_SU)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (mapL embedOf mapL_le mapL_mono card_mapL mapL_sup
  mapL_inj mapL_perfectResidual_inf perfectResidualEquiv)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly (IsElemAbelian)

section Transport

variable {G G' : Type} [Group G] [Group G'] {Y : Subgroup G} {Y' : Subgroup G'} (e : Y ≃* Y')

theorem mapL_self : mapL e Y = Y' := by
  apply le_antisymm (mapL_le e Y)
  intro x hx
  refine ⟨e.symm ⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr (e.symm ⟨x, hx⟩).2, ?_⟩
  simp [embedOf]

theorem embedOf_mem_mapL {Z : Subgroup G} {y : Y} (hy : (y : G) ∈ Z) : embedOf e y ∈ mapL e Z :=
  ⟨y, hy, rfl⟩

theorem commutator_eq_bot_of_mapL {Z₁ Z₂ : Subgroup G} (h₁ : Z₁ ≤ Y) (h₂ : Z₂ ≤ Y)
    (h : ⁅mapL e Z₁, mapL e Z₂⁆ = ⊥) : ⁅Z₁, Z₂⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h ⊢
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hc := Subgroup.mem_centralizer_iff.mp (h (embedOf_mem_mapL e (y := ⟨x, h₁ hx⟩) hx))
    (embedOf e ⟨y, h₂ hy⟩) (embedOf_mem_mapL e (y := ⟨y, h₂ hy⟩) hy)
  rw [← map_mul, ← map_mul] at hc
  exact congrArg Subtype.val (U4Lines.embedOf_injective e hc)

theorem mapL_map_conj {Z : Subgroup G} (hZ : Z ≤ Y) (y : Y) :
    mapL e (Z.map (MulAut.conj (y : G)).toMonoidHom) =
      (mapL e Z).map (MulAut.conj (embedOf e y)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨z, ⟨w, hw, hwz⟩, rfl⟩
    change (y : G) * w * (y : G)⁻¹ = (z : G) at hwz
    refine ⟨embedOf e ⟨w, hZ hw⟩, embedOf_mem_mapL e hw, ?_⟩
    change embedOf e y * embedOf e ⟨w, hZ hw⟩ * (embedOf e y)⁻¹ = embedOf e z
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hwz)
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨y * w * y⁻¹, ⟨w, hw, by simp [MulAut.conj_apply]⟩, ?_⟩
    change embedOf e (y * w * y⁻¹) = embedOf e y * embedOf e w * (embedOf e y)⁻¹
    rw [map_mul, map_mul, map_inv]

theorem mem_normalizer_of_map_conj_eq {H : Type} [Group H] {Z : Subgroup H} {g : H}
    (h : Z.map (MulAut.conj g).toMonoidHom = Z) : g ∈ Subgroup.normalizer (Z : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨x', hx', hxx⟩ := hx
    change g * x' * g⁻¹ = g * x * g⁻¹ at hxx
    have : x' = x := by simpa using hxx
    rwa [← this]

end Transport

section Automizer

variable {G : Type} [Group G]

theorem mem_normalizer_of_mem_normalizer_subgroupOf {X T : Subgroup G} (hTX : T ≤ X) {y : X}
    (hy : y ∈ Subgroup.normalizer ((T.subgroupOf X : Subgroup X) : Set X)) :
    (y : G) ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    have h := (Subgroup.mem_normalizer_iff.mp hy ⟨t, hTX ht⟩).mp
      (Subgroup.mem_subgroupOf.mpr ht)
    exact Subgroup.mem_subgroupOf.mp h
  · intro ht
    have htX : t ∈ X := by
      have h1 : (y : G) * t * (y : G)⁻¹ ∈ X := hTX ht
      have : t = (y : G)⁻¹ * ((y : G) * t * (y : G)⁻¹) * (y : G) := by group
      rw [this]
      exact X.mul_mem (X.mul_mem (X.inv_mem y.2) h1) y.2
    have h := (Subgroup.mem_normalizer_iff.mp hy ⟨t, htX⟩).mpr
      (Subgroup.mem_subgroupOf.mpr ht)
    exact Subgroup.mem_subgroupOf.mp h

theorem mem_normalizer_subgroupOf_of_mem {X T : Subgroup G} {x : G} (hxX : x ∈ X)
    (hx : x ∈ Subgroup.normalizer (T : Set G)) :
    (⟨x, hxX⟩ : X) ∈ Subgroup.normalizer ((T.subgroupOf X : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp hx t

theorem nonempty_starOf_mulEquiv_torusImage {X T : Subgroup G} (hTX : T ≤ X) :
    Nonempty (starOf T X ≃* PartOne.torusImage (T.subgroupOf X) ⊤) := by
  set T' : Subgroup X := T.subgroupOf X with hT'
  set N' := Subgroup.normalizer ((T' : Subgroup X) : Set X) with hN'
  set f₁ : N' →* MulAut T' := T'.normalizerMonoidHom with hf₁
  set g₀ : N' →* Subgroup.normalizer (T : Set G) :=
    (X.subtype.comp N'.subtype).codRestrict _
      (fun y => mem_normalizer_of_mem_normalizer_subgroupOf hTX y.2) with hg₀
  set f₂ : N' →* MulAut T := T.normalizerMonoidHom.comp g₀ with hf₂
  have hr₁ : f₁.range = PartOne.torusImage T' ⊤ := by
    rw [PartOne.torusImage, Subgroup.top_subgroupOf, ← MonoidHom.range_eq_map]
  have hr₂ : f₂.range = starOf T X := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      exact ⟨g₀ y, Subgroup.mem_subgroupOf.mpr ((y : X).2), rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
      exact ⟨⟨⟨x, hxX⟩, mem_normalizer_subgroupOf_of_mem hxX x.2⟩, rfl⟩
  have hker : f₁.ker = f₂.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have hf₁y : ∀ t : T', (((f₁ y t : T') : X) : G) =
        (((y : N') : X) : G) * ((t : X) : G) * (((y : N') : X) : G)⁻¹ := fun t => rfl
    have hf₂y : ∀ t : T, ((f₂ y t : T) : G) =
        (((y : N') : X) : G) * (t : G) * (((y : N') : X) : G)⁻¹ := fun t => rfl
    constructor
    · intro h
      ext t
      rw [hf₂y, MulAut.one_apply]
      have := congrArg (fun σ : MulAut T' => (((σ ⟨⟨t, hTX t.2⟩, t.2⟩ : T') : X) : G)) h
      simpa [hf₁y] using this
    · intro h
      ext t
      rw [MulAut.one_apply, hf₁y]
      have := congrArg (fun σ : MulAut T => ((σ ⟨((t : X) : G), t.2⟩ : T) : G)) h
      simpa [hf₂y] using this
  obtain ⟨e⟩ := Item223PrintProof.nonempty_range_mulEquiv_of_ker_eq f₁ f₂ hker
  exact ⟨(MulEquiv.subgroupCongr hr₂).symm.trans (e.symm.trans (MulEquiv.subgroupCongr hr₁))⟩

end Automizer

theorem exists_primitiveRoot_three_of_dvd {K : Type} [Field K] [Finite K]
    (hdvd : 3 ∣ Nat.card K - 1) : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd' : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd'
  refine ⟨z, ?_⟩
  have := IsPrimitiveRoot.orderOf z
  rwa [hz] at this

theorem u4EvenTorus : U4EvenTorus := by
  intro G _ _ X T k hk0 hke ⟨eX⟩ hTX hTe hT9
  set F := GaloisField 2 (2 * k) with hFdef
  have hF : Nat.card F = (2 ^ k) ^ 2 := U4Lines.card_galoisField_two_mul k hk0
  set σ : F ≃+* F := unitaryInvolution F 2 k with hσdef
  obtain ⟨e₀⟩ := U4Lines.nonempty_projSU_mulEquiv_SU k hk0
  set e : X ≃* SU σ 4 := eX.trans e₀ with hedef
  set T₁ : Subgroup (SU σ 4) := (T.subgroupOf X).map e.toMonoidHom with hT₁
  have hT₁3 : ∀ x ∈ T₁, x ^ 3 = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow]
    have : t ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hTe.2 _ (Subgroup.mem_subgroupOf.mp ht))
    rw [this, map_one]
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_su (n := 4) (Or.inl rfl) d8Comb_four hF
    Nat.prime_three (by norm_num) (three_dvd_two_pow_sub_one hke) T₁ hT₁3
  set e' : X ≃* SU σ 4 := e.trans (MulAut.conj g) with he'def
  have he'apply : ∀ y : X, e' y = g * e y * g⁻¹ := fun y => rfl
  have hdvd : 3 ∣ Nat.card F - 1 := by
    rw [hF]
    have h1 : 2 ^ k - 1 ∣ (2 ^ k) ^ 2 - 1 := by simpa using Nat.sub_dvd_pow_sub_pow (2 ^ k) 1 2
    exact (three_dvd_two_pow_sub_one hke).trans h1
  have hζ := exists_primitiveRoot_three_of_dvd hdvd
  have hσfix : ∀ u : rootsOfUnity 3 F, σ ((u : Fˣ) : F) = (u : Fˣ) :=
    U4Lines.unitaryInvolution_rootsOfUnity hke
  have hT4 : ∀ v : D8Mod 3 F, (CFSG.RankThree.PartOne.KFU.diagU
      (CFSG.RankThree.PartOne.KFU.d8Vec 4 v) : GL (Fin 4) F) ∈ SU σ 4 :=
    fun v => d8Vec_mem_SU (Or.inl rfl) d8Comb_four σ hσfix v
  have hP4 : ∀ τ : Equiv.Perm (Fin 4), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (CFSG.RankThree.PartOne.KFU.permGL τ : GL (Fin 4) F) ∈ SU σ 4 :=
    fun τ hτ => permGL_mem_SU σ τ hτ
  obtain ⟨SM⟩ := exists_d8ctx d8Comb_four d8Comb2_four Nat.prime_three (by norm_num) hζ
    (SU σ 4) hT4 hP4
  have hT0card : Nat.card ((d8Tor 3 F 4).subgroupOf (SU σ 4)) = 3 ^ 2 :=
    SM.card_F (by norm_num) hζ
  have hT0le : d8Tor 3 F 4 ≤ SU σ 4 := by
    rintro _ ⟨v, rfl⟩
    exact hT4 v
  have hT0card' : Nat.card (d8Tor 3 F 4) = 3 ^ 2 := by
    rw [← hT0card]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT0le).toEquiv).symm
  have hmapT : mapL e' T = d8Tor 3 F 4 := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hT0card', card_mapL e' hTX, hT9])
    rintro _ ⟨t, ht, rfl⟩
    have h1 := hg (e t) ⟨t, ht, rfl⟩
    exact Subgroup.mem_subgroupOf.mp h1
  have hmapT' : (T.subgroupOf X).map e'.toMonoidHom = (d8Tor 3 F 4).subgroupOf (SU σ 4) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hmapT ▸ ⟨t, ht, rfl⟩)
    · intro hx
      have hx' : (x : GL (Fin 4) F) ∈ mapL e' T := by
        rw [hmapT]
        exact Subgroup.mem_subgroupOf.mp hx
      obtain ⟨t, ht, hxt⟩ := hx'
      refine ⟨t, ht, ?_⟩
      exact Subtype.ext hxt
  have hline : ∀ ℓ : Subgroup G, ℓ ≤ T → mapL e' ℓ ≤ d8Tor 3 F 4 := fun ℓ hℓ =>
    hmapT ▸ mapL_mono e' hℓ
  have hperf : ∀ ℓ : Subgroup G, ℓ ≤ X →
      mapL e' (perfCent X ℓ) = perfCent (SU σ 4) (mapL e' ℓ) := fun ℓ hℓ =>
    mapL_perfectResidual_inf e' hℓ
  have hperfX : ∀ ℓ : Subgroup G, perfCent X ℓ ≤ X := fun ℓ =>
    (Subgroup.map_subtype_le _).trans inf_le_left
  obtain ⟨hlinesM, hpairsM⟩ := model_U4 hk0 hke hF
  refine ⟨?_, fun ℓ hℓ h3 => ?_, fun ℓ₁ ℓ₂ c₁ c₂ h₁ h₂ hc₁ hc₂ h₁3 h₂3 hc₁3 hc₂3 hne hc₁S hc₂S =>
    ?_⟩
  ·
    obtain ⟨φ₁⟩ := nonempty_starOf_mulEquiv_torusImage hTX
    obtain ⟨φ₂⟩ := Sec4.Res417Six.nonempty_autIn_mulEquiv_of_map_eq e' hmapT'
    rw [Sec4.Res417Six.autIn_eq_torusImage] at φ₂
    exact ⟨φ₁.trans (φ₂.trans (SM.weylEquiv Nat.prime_three (by norm_num) hζ))⟩
  ·
    have hℓX := hℓ.trans hTX
    rcases hlinesM (mapL e' ℓ) (hline ℓ hℓ) (by rw [card_mapL e' hℓX, h3]) with h | h
    · obtain ⟨f⟩ := h
      exact Or.inl ⟨(perfectResidualEquiv e' hℓX).trans f⟩
    · obtain ⟨f⟩ := h
      exact Or.inr ⟨(perfectResidualEquiv e' hℓX).trans f⟩
  ·
    have h₁X := h₁.trans hTX
    have h₂X := h₂.trans hTX
    have hc₁X := hc₁.trans hTX
    have hc₂X := hc₂.trans hTX
    obtain ⟨hM1, hM2⟩ := hpairsM (mapL e' ℓ₁) (mapL e' ℓ₂) (mapL e' c₁) (mapL e' c₂)
      (hline ℓ₁ h₁) (hline ℓ₂ h₂) (hline c₁ hc₁) (hline c₂ hc₂)
      (by rw [card_mapL e' h₁X, h₁3]) (by rw [card_mapL e' h₂X, h₂3])
      (by rw [card_mapL e' hc₁X, hc₁3]) (by rw [card_mapL e' hc₂X, hc₂3])
      (fun h => hne (mapL_inj e' h₁X h₂X h))
      (by rw [← hperf ℓ₁ h₁X]; exact mapL_mono e' hc₁S)
      (by rw [← hperf ℓ₂ h₂X]; exact mapL_mono e' hc₂S)
    have hsupX : ∀ ℓ ℓ' : Subgroup G, ℓ ≤ X → ℓ' ≤ X →
        perfCent (SU σ 4) (mapL e' ℓ) ⊔ perfCent (SU σ 4) (mapL e' ℓ') = SU σ 4 →
        perfCent X ℓ ⊔ perfCent X ℓ' = X := by
      intro ℓ ℓ' hℓ hℓ' h
      refine mapL_inj e' (sup_le (hperfX ℓ) (hperfX ℓ')) le_rfl ?_
      rw [mapL_sup e' (hperfX ℓ) (hperfX ℓ'), hperf ℓ hℓ, hperf ℓ' hℓ', h, mapL_self]
    refine ⟨fun hc => ?_, fun hc => hsupX ℓ₁ ℓ₂ h₁X h₂X (hM2 fun h => hc
      (mapL_inj e' hc₁X h₂X h))⟩
    obtain ⟨hc₂ℓ₁, hcase⟩ := hM1 (by rw [hc])
    refine ⟨mapL_inj e' hc₂X h₁X hc₂ℓ₁, ?_⟩
    rcases hcase with hcomm | ⟨hY, ⟨f₁⟩, ⟨f₂⟩, w, hwSU, hwN, hw₁, hw₂⟩
    · left
      refine commutator_eq_bot_of_mapL e' (hperfX ℓ₁) (hperfX ℓ₂) ?_
      rw [hperf ℓ₁ h₁X, hperf ℓ₂ h₂X]
      exact hcomm
    · right
      refine ⟨hsupX ℓ₁ ℓ₂ h₁X h₂X hY, ⟨(perfectResidualEquiv e' h₁X).trans f₁⟩,
        ⟨(perfectResidualEquiv e' h₂X).trans f₂⟩, ?_⟩
      set y : X := e'.symm ⟨w, hwSU⟩ with hydef
      have hyw : embedOf e' y = w := by simp [U4Lines.embedOf, hydef]
      have hconj : ∀ Z : Subgroup G, Z ≤ X →
          mapL e' (Z.map (MulAut.conj (y : G)).toMonoidHom) =
            (mapL e' Z).map (MulAut.conj w).toMonoidHom := fun Z hZ => by
        rw [mapL_map_conj e' hZ y, hyw]
      have hmapX : ∀ Z : Subgroup G, Z ≤ X → Z.map (MulAut.conj (y : G)).toMonoidHom ≤ X := by
        rintro Z hZ _ ⟨z, hz, rfl⟩
        exact X.mul_mem (X.mul_mem y.2 (hZ hz)) (X.inv_mem y.2)
      refine ⟨y, y.2, ?_, ?_, ?_⟩
      · refine mem_normalizer_of_map_conj_eq (mapL_inj e' (hmapX T hTX) hTX ?_)
        rw [hconj T hTX, hmapT]
        exact Item228InspProof.map_conj_self hwN
      · exact mapL_inj e' (hmapX ℓ₁ h₁X) h₂X (by rw [hconj ℓ₁ h₁X]; exact hw₁)
      · exact mapL_inj e' (hmapX ℓ₂ h₂X) h₁X (by rw [hconj ℓ₂ h₂X]; exact hw₂)

end CFSG.RankThree.PartTwo.Sec21.Item228InspProof
