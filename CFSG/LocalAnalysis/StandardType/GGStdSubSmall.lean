module

public import CFSG.LocalAnalysis.StandardType.GGFieldNbrTableB
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGStdSubTwoTorus (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ∀ a ∈ A, a ≠ 1 → IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) →
        (∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)) →
        ∃ U : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ LargeEvenLayer (ggFix a) ∧
          (∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U) ∧
          ∃ t ∈ LargeEvenLayer (ggFix a), t ^ p = 1 ∧ (∀ a' ∈ A, a' t = t) ∧
            t ∈ Subgroup.normalizer (U : Set L') ∧
            ∃ j ∈ LargeEvenLayer (ggFix a), t * j ≠ j * t

section Config

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_not_mem_zpowers {p : ℕ} (hp : p.Prime) {D : Subgroup G}
    (hcard : Nat.card D = p ^ 2) {x : G} (hxp : x ^ p = 1) (hx1 : x ≠ 1) :
    ∃ d ∈ D, d ∉ Subgroup.zpowers x := by
  have := Fact.mk hp
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hle : D ≤ Subgroup.zpowers x := fun d hd => h d hd
  have h1 := Subgroup.card_le_of_le hle
  rw [hcard, Nat.card_zpowers, orderOf_eq_prime hxp hx1] at h1
  have h2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at h2
  omega

theorem eq_sup_zpowers_of_card {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) {x d : G} (hxD : x ∈ D) (hx1 : x ≠ 1) (hdD : d ∈ D)
    (hdx : d ∉ Subgroup.zpowers x) : D = Subgroup.zpowers x ⊔ Subgroup.zpowers d := by
  have := Fact.mk hp
  have hxp : x ^ p = 1 := hD.2 x hxD
  have hdp : d ^ p = 1 := hD.2 d hdD
  have hd1 : d ≠ 1 := fun h => hdx (h ▸ one_mem _)
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers d ≤ D :=
    sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr hdD)
  have hN : Subgroup.zpowers d ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro y hy
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact IsElemAbelian.comm hD (Subgroup.zpowers_le.mpr hxD hz) (Subgroup.zpowers_le.mpr hdD hy)
  have hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers d) := by
    have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers d : Subgroup G) ∣ p := by
      have := Subgroup.card_dvd_of_le
        (inf_le_right : Subgroup.zpowers x ⊓ Subgroup.zpowers d ≤ _)
      rwa [Nat.card_zpowers, orderOf_eq_prime hdp hd1] at this
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · rw [disjoint_iff]
      exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      apply hdx
      have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers d = Subgroup.zpowers d :=
        Subgroup.eq_of_le_of_card_ge inf_le_right
          (by rw [h1, Nat.card_zpowers, orderOf_eq_prime hdp hd1])
      have hmem : d ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers d := by
        rw [heq]
        exact Subgroup.mem_zpowers _
      exact hmem.1
  have hc : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers d : Subgroup G) = p ^ 2 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj,
      Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hxp hx1, orderOf_eq_prime hdp hd1, sq]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hcard])).symm

theorem ggStdSubInputs_of_twoTorus {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hM : LargeEvenMarking L fun _ R _ I _ θ => (B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorus p r R I) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D ∧
      ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G) := by
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hcfg.1
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have hBs : GGBstar p B Bs := hcfg.2.1
  obtain ⟨hDB, hDe, hDcard, hxD, hJdef, hJcomp, hDC⟩ := hcfg.2.2.1
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨hBN, h3⟩, r, hlift, htt⟩ := largeEvenRawDatum_exists hraw
  set γ := ggGamma L hBN with hγ
  have hBp : ∀ b : B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hS.1.1.2 b b.2)
  have hBc : ∀ a b : B, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hS.1.1 a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBN b, ggBeta_mem L θ hBN h3 b, fun l => ggBeta_ggQuotHom L hBN θ b l⟩
  have hcA := card_range_ggGamma_mul L hBN hp hS
  have hcβ := card_range_ggBeta_mul L θ hp hS hL hBN
  have hAβ : Nat.card γ.range = Nat.card (ggBeta L θ hBN).range :=
    Nat.eq_of_mul_eq_mul_right hp.pos (hcA.trans hcβ.symm)
  have hr : p ^ r ≤ Nat.card γ.range := by
    rw [hAβ]
    exact pow_le_card_range_ggBeta hp hS hL θ hBN hlift
  have h3' : p ^ 3 ≤ Nat.card γ.range := by
    have h4 := pow_four_le_card_of_bmax hp hS.1 hβ.2.2.2
    rw [← hcA, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  obtain ⟨d, hdD, hdx⟩ := exists_mem_not_mem_zpowers hp hDcard (hS.1.1.2 x hS.2.1) hS.2.2.1
  have hD : D = Subgroup.zpowers x ⊔ Subgroup.zpowers d :=
    eq_sup_zpowers_of_card hp hDe hDcard hxD hS.2.2.1 hdD hdx
  set d₀ : B := ⟨d, hDB hdD⟩ with hd₀
  set a := γ d₀ with ha
  have hfix : (ggFix a).map L.subtype = L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hD, inf_centralizer_sup_zpowers hLx]
    exact map_ggFix_ggGamma L hBN d₀
  have hJE : J = (LargeEvenLayer (ggFix a)).map L.subtype := by
    rw [hJdef, ← hfix, largeEvenLayer_map_of_injective _ L.subtype_injective]
  have hEcomp : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) := by
    have h1 := isComponentOf_comap_of_injective L.subtype L.subtype_injective
      (K' := J) (C := ggFix a) (by rw [hfix]; exact hJcomp)
    have h2 : J.comap L.subtype = LargeEvenLayer (ggFix a) := by
      rw [hJE, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    rw [← h2]
    exact h1.1
  have ha1 : a ≠ 1 := by
    intro h
    rw [ha, ggGamma_eq_one_iff] at h
    apply hdx
    rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
    exact ⟨hDB hdD, h⟩
  have hcentA : ∀ a' ∈ γ.range,
      ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a) := by
    rintro _ ⟨b, rfl⟩
    constructor
    · intro hb
      have hbJ : (b : G) ∈ B ⊓ Subgroup.centralizer (J : Set G) := by
        refine ⟨b.2, ?_⟩
        show (b : G) ∈ Subgroup.centralizer (J : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [hJE] at hg
        obtain ⟨j, hj, rfl⟩ := hg
        have h1 := congrArg Subtype.val (hb j hj)
        rw [ggGamma_coe] at h1
        calc (j : G) * b = b * j * (b : G)⁻¹ * b := by rw [h1]
          _ = b * j := by group
      rw [← hDC] at hbJ
      set H := (Subgroup.zpowers a).comap γ with hH
      have hxH : (⟨x, hS.2.1⟩ : B) ∈ H := by
        change γ ⟨x, hS.2.1⟩ ∈ Subgroup.zpowers a
        rw [(ggGamma_eq_one_iff L hBN _).mpr (mem_centralizer_of_le_centralizer hLx)]
        exact one_mem _
      have hdH : d₀ ∈ H := Subgroup.mem_zpowers a
      have hDH : D ≤ H.map B.subtype := by
        rw [hD]
        exact sup_le (Subgroup.zpowers_le.mpr ⟨_, hxH, rfl⟩)
          (Subgroup.zpowers_le.mpr ⟨_, hdH, rfl⟩)
      obtain ⟨b', hb'H, hb'⟩ := hDH hbJ
      have hbb : b' = b := Subtype.ext hb'
      rw [← hbb]
      exact hb'H
    · intro hmem j hj
      have hj1 : a j = j := mem_ggFix.mp (hEcomp.1 hj)
      have hstab : a ∈ MulAction.stabilizer (MulAut L) j :=
        MulAction.mem_stabilizer_iff.mpr (by rw [MulAut.smul_def]; exact hj1)
      have h1 := MulAction.mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr hstab) hmem)
      rwa [MulAut.smul_def] at h1
  obtain ⟨U, hU, hU2, hUE, hAU, t, htE, htp, htA, htU, j, hjE, htj⟩ :=
    htt L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA hAI hr
      h3' a ⟨d₀, rfl⟩ ha1 hEcomp hcentA
  set T := U.map L.subtype with hTdef
  have hT1 : T ≠ ⊥ := by
    rw [Ne, hTdef, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
    exact hU
  have hT2 : IsPGroup 2 T := hU2.map _
  have hTJ : T ≤ J := hJE ▸ Subgroup.map_mono hUE
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨u, hu, rfl⟩
    exact ⟨γ ⟨b, hb⟩ u, hAU _ ⟨⟨b, hb⟩, rfl⟩ u hu, ggGamma_coe L hBN ⟨b, hb⟩ u⟩
  refine ⟨ggStdSubBstarCentralizer_of_twoSubgroup hcfg ⟨T, hT1, hT2, hTJ, hBT⟩, ?_⟩
  have ht'J : (t : G) ∈ J := hJE ▸ ⟨t, htE, rfl⟩
  have ht'p : (t : G) ^ p = 1 := by
    rw [← Subgroup.coe_pow, htp, Subgroup.coe_one]
  have ht'B : ∀ b ∈ B, ∀ c ∈ Subgroup.zpowers (t : G), b * c = c * b := by
    intro b hb c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have h1 : b * (t : G) = (t : G) * b := by
      have h2 := congrArg Subtype.val (htA _ ⟨⟨b, hb⟩, rfl⟩)
      rw [ggGamma_coe] at h2
      calc b * (t : G) = b * (t : G) * b⁻¹ * b := by group
        _ = (t : G) * b := by rw [h2]
    exact (Commute.zpow_right h1 k)
  have hE : IsElemAbelian p (B ⊔ Subgroup.zpowers (t : G)) :=
    isElemAbelian_sup hS.1.1 (isElemAbelian_zpowers ht'p) ht'B
  have htN : (t : G) ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.le_normalizer_map L.subtype ⟨t, htU, rfl⟩
  have hEN : B ⊔ Subgroup.zpowers (t : G) ≤ Subgroup.normalizer (T : Set G) :=
    sup_le hBT (Subgroup.zpowers_le.mpr htN)
  have hcard := card_le_of_twoLocal hp ⟨T, hT1, hT2, rfl⟩ hEN hE
  rw [← hS.1.2.1] at hcard
  have hBE := Subgroup.eq_of_le_of_card_ge (le_sup_left : B ≤ B ⊔ Subgroup.zpowers (t : G)) hcard
  have htB : (t : G) ∈ B := hBE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (t : G))
  refine ⟨t, ⟨hBs.1 htB, ht'J⟩, fun hC => htj ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.mp hC (j : G) (hJE ▸ ⟨j, hjE, rfl⟩)
  exact Subtype.ext h1.symm

end Config

@[expose] def GGStdSubSmallInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J →
    LargeEvenMarking L (fun lab _ _ I _ θ => S p lab ∧ LargeEvenSplit p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
    Nat.card (Bs ⊓ J : Subgroup G) < p ^ 3 →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D ∧
        ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G)

theorem ggStdSubSmallInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorus p r R I) :
    GGStdSubSmallInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM _
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  exact ggStdSubInputs_of_twoTorus hcfg
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩) hM')

theorem GGStdSubSmallInputOn.or {S T : ℕ → LargeEvenLabel → Prop} (hS : GGStdSubSmallInputOn S)
    (hT : GGStdSubSmallInputOn T) : GGStdSubSmallInputOn fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B Bs x L D J hcfg hM hsm
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, hST, -⟩ := largeEvenRawDatum_exists hraw
  rcases hST with h | h
  · exact hS G p B Bs x L D J hcfg ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩ hsm
  · exact hT G p B Bs x L D J hcfg ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩ hsm

theorem ggStdSubSmallInput_of_cover {S : ℕ → LargeEvenLabel → Prop}
    (hS : GGStdSubSmallInputOn S)
    (hcov : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab) :
    GGStdSubSmallInput := by
  intro G _ _ p B Bs x L D J hcfg hsm
  obtain ⟨hperf, lab, hlab, hraw⟩ := hcfg.1.2.2.2.2.2.2.2.1
  exact hS G p B Bs x L D J hcfg ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, hcov p lab hlab hP.1, hP⟩) hraw⟩ hsm

end CFSG.StandardType

end
