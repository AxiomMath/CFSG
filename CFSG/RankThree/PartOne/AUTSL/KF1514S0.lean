module

public import CFSG.RankThree.PartOne.AUTSL.KF1514P
public import CFSG.RankThree.PartOne.AUTSL.KF1514Model
public import CFSG.RankThree.PartOne.S12.Sec1514Five

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace AUTSL

section Defs

variable {G : Type} [Group G]

@[expose] def Cl1 (p : ℕ) (I K T A₀ : Subgroup G) : Prop :=
  ∃ h ∈ K, ∃ B : Subgroup G, B ≤ A₀ ∧ Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
    B.map (MulAut.conj h).toMonoidHom ≤ I ⊓ Subgroup.normalizer (pushingUpS T : Set G)

@[expose] def Cl2 (p : ℕ) (I K T A₀ : Subgroup G) : Prop :=
  ∃ x ∈ omegaOneCenterIn T, x ≠ 1 ∧ ∃ h ∈ K, ∃ B : Subgroup G, B ≤ A₀ ∧
    Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
    B.map (MulAut.conj h).toMonoidHom ≤ I ⊓ Subgroup.centralizer ({x} : Set G)

@[expose] def MCl1 {Â : Type} [Group Â] (p : ℕ) (R A Tt : Subgroup Â) : Prop :=
  ∃ h ∈ R, ∃ B : Subgroup Â, B ≤ A ∧ Nat.card ↥A ≤ p * Nat.card ↥B ∧
    B.map (MulAut.conj h).toMonoidHom ≤ Subgroup.normalizer (pushingUpS Tt : Set Â)

@[expose] def MCl2 {Â : Type} [Group Â] (p : ℕ) (R A Tt : Subgroup Â) : Prop :=
  ∃ x ∈ omegaOneCenterIn Tt, x ≠ 1 ∧ ∃ h ∈ R, ∃ B : Subgroup Â, B ≤ A ∧
    Nat.card ↥A ≤ p * Nat.card ↥B ∧
    B.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer ({x} : Set Â)


@[expose] def KF1514PAutGen (L : Type) [Group L] (p : ℕ) : Prop :=
  ∀ H A₀ : Subgroup (MulAut L), (MulAut.conj : L →* MulAut L).range ≤ H →
    A₀ ≤ (MulAut.conj : L →* MulAut L).range → IsElementaryAbelian p ↥A₀ →
    Nat.card ↥A₀ = p ^ 3 →
    ∃ T : Subgroup (MulAut L), IsSylowOf 2 T H ∧
      (∃ B : Subgroup (MulAut L), B ≤ A₀ ∧ Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
        B ≤ Subgroup.normalizer (pushingUpS T : Set (MulAut L))) ∧
      (∃ x ∈ omegaOneCenterIn T, x ≠ 1 ∧ ∃ B : Subgroup (MulAut L), B ≤ A₀ ∧
        Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧ B ≤ Subgroup.centralizer ({x} : Set (MulAut L)))

@[expose] def KF1514PAut (r : ℕ) : Prop :=
  match r with
  | 1 => ∀ (p f : ℕ), p.Prime → 5 ≤ p → 1 ≤ f → p ∣ 2 ^ f - 1 →
      KF1514PAutGen ↥(projSL 4 (GaloisField 2 f)) p
  | 2 => ∀ (p f : ℕ), p.Prime → 5 ≤ p → 1 ≤ f → p ∣ 2 ^ f - 1 →
      KF1514PAutGen ↥(projSp 3 (GaloisField 2 f)) p
  | _ => True

end Defs

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_isSylowOf {p : ℕ} [Fact p.Prime] {P P' K : Subgroup G}
    (hP : IsSylowOf p P K) (hP' : IsSylowOf p P' K) :
    ∃ x ∈ K, P' = P.map (MulAut.conj x).toMonoidHom := by
  have h1 : CFSG.ABGLocalTools.IsSylowOf p P K := CFSG.ABGLocalTools.isSylowOf_iff.2 hP
  have h2 : CFSG.ABGLocalTools.IsSylowOf p P' K := CFSG.ABGLocalTools.isSylowOf_iff.2 hP'
  obtain ⟨Q, rfl⟩ := h1
  obtain ⟨Q', rfl⟩ := h2
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨d, d.2, ?_⟩
  rw [← hd, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩

end Sylow

section Conj

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_eq_of_mem {I K : Subgroup G} (hKN : K ≤ Subgroup.normalizer (I : Set G)) {g : G}
    (hg : g ∈ K) : I.map (MulAut.conj g).toMonoidHom = I :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (hKN hg)

theorem cl1_of_conj {p : ℕ} {I K T T' A₀ : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (I : Set G)) {g : G} (hg : g ∈ K)
    (hT : T = T'.map (MulAut.conj g).toMonoidHom) (h : Cl1 p I K T' A₀) : Cl1 p I K T A₀ := by
  obtain ⟨h₀, hh₀, B, hBA, hcard, hBle⟩ := h
  refine ⟨g * h₀, K.mul_mem hg hh₀, B, hBA, hcard, ?_⟩
  have e1 : B.map (MulAut.conj (g * h₀)).toMonoidHom =
      (B.map (MulAut.conj h₀).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hS : pushingUpS T = (pushingUpS T').map (MulAut.conj g).toMonoidHom := by
    rw [hT]
    exact (U5K.map_pushingUpS (MulAut.conj g).toMonoidHom
      (Sec1514Five.injective_conj_comp g T')).symm
  rw [e1]
  calc (B.map (MulAut.conj h₀).toMonoidHom).map (MulAut.conj g).toMonoidHom
      ≤ (I ⊓ Subgroup.normalizer (pushingUpS T' : Set G)).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hBle
    _ = I.map (MulAut.conj g).toMonoidHom ⊓
        (Subgroup.normalizer (pushingUpS T' : Set G)).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_inf _ _ _ (MulAut.conj g).injective
    _ = I ⊓ Subgroup.normalizer (pushingUpS T : Set G) := by
        rw [map_conj_eq_of_mem hKN hg, hS]
        congr 1
        exact Subgroup.map_normalizer_eq_of_bijective (pushingUpS T')
          (MulAut.conj g).bijective

omit [Finite G] in
theorem cl2_of_conj {p : ℕ} {I K T T' A₀ : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (I : Set G)) {g : G} (hg : g ∈ K)
    (hT : T = T'.map (MulAut.conj g).toMonoidHom) (h : Cl2 p I K T' A₀) : Cl2 p I K T A₀ := by
  obtain ⟨x', hx', hx'1, h₀, hh₀, B, hBA, hcard, hBle⟩ := h
  have hΩ : omegaOneCenterIn T = (omegaOneCenterIn T').map (MulAut.conj g).toMonoidHom := by
    rw [hT]
    exact (Sec1514Five.map_omegaOneCenterIn (MulAut.conj g).toMonoidHom
      (Sec1514Five.injective_conj_comp g T')).symm
  refine ⟨g * x' * g⁻¹, ?_, ?_, g * h₀, K.mul_mem hg hh₀, B, hBA, hcard, ?_⟩
  · rw [hΩ]
    exact ⟨x', hx', rfl⟩
  · intro h1
    apply hx'1
    have : x' = g⁻¹ * (g * x' * g⁻¹) * g := by group
    rw [this, h1]
    group
  · have e1 : B.map (MulAut.conj (g * h₀)).toMonoidHom =
        (B.map (MulAut.conj h₀).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [mul_assoc]
    rw [e1]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨hyI, hyc⟩ := Subgroup.mem_inf.1 (hBle hy)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have : (MulAut.conj g).toMonoidHom y ∈ I.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hyI
      rwa [map_conj_eq_of_mem hKN hg] at this
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have := Subgroup.mem_centralizer_iff.1 hyc x' rfl
      show g * x' * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x' * g⁻¹)
      calc g * x' * g⁻¹ * (g * y * g⁻¹) = g * (x' * y) * g⁻¹ := by group
        _ = g * (y * x') * g⁻¹ := by rw [this]
        _ = g * y * g⁻¹ * (g * x' * g⁻¹) := by group

end Conj

section Model

variable {G Â : Type} [Group G] [Group Â] {K : Subgroup G} (ρ : ↥K →* Â)

theorem faithful_of_injective (hρ : Function.Injective ρ) {T : Subgroup G} :
    ∀ t ∈ T, ∀ ht : t ∈ K, ρ ⟨t, ht⟩ = 1 → t = 1 := fun _ _ _ h =>
  congrArg Subtype.val (hρ (h.trans (map_one ρ).symm))

theorem mem_normalizer_of_rm (hρ : Function.Injective ρ) {S : Subgroup G} (hSK : S ≤ K) {y : G}
    (hy : y ∈ K) (h : ρ ⟨y, hy⟩ ∈ Subgroup.normalizer (U5K.rm K ρ S : Set Â)) :
    y ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  have hy' := Subgroup.mem_normalizer_iff.1 h
  constructor
  · intro hs
    have hsK : s ∈ K := hSK hs
    have hmem : ρ ⟨s, hsK⟩ ∈ U5K.rm K ρ S := U5K.mem_rm.2 ⟨s, hsK, hs, rfl⟩
    have h1 := (hy' _).1 hmem
    obtain ⟨t, htK, htS, ht⟩ := U5K.mem_rm.1 h1
    have h3 : (⟨t, htK⟩ : ↥K) = ⟨y, hy⟩ * ⟨s, hsK⟩ * ⟨y, hy⟩⁻¹ :=
      hρ (by rw [ht, map_mul, map_mul, map_inv])
    have h2 : t = y * s * y⁻¹ := congrArg Subtype.val h3
    rwa [← h2]
  · intro hs
    have hsK : s ∈ K := by
      have h4 : y * s * y⁻¹ ∈ K := hSK hs
      have := K.mul_mem (K.mul_mem (K.inv_mem hy) h4) hy
      simpa [mul_assoc] using this
    have hmem : ρ ⟨y, hy⟩ * ρ ⟨s, hsK⟩ * (ρ ⟨y, hy⟩)⁻¹ ∈ U5K.rm K ρ S := by
      have h4 : y * s * y⁻¹ ∈ K := hSK hs
      refine U5K.mem_rm.2 ⟨y * s * y⁻¹, h4, hs, ?_⟩
      have : (⟨y * s * y⁻¹, h4⟩ : ↥K) = ⟨y, hy⟩ * ⟨s, hsK⟩ * ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
    have h5 := (hy' _).2 hmem
    obtain ⟨t, htK, htS, ht⟩ := U5K.mem_rm.1 h5
    have h6 : (⟨t, htK⟩ : ↥K) = ⟨s, hsK⟩ := hρ ht
    have h7 : t = s := congrArg Subtype.val h6
    rwa [h7] at htS

theorem commute_of_map_commute (hρ : Function.Injective ρ) {x z : G} (hx : x ∈ K) (hz : z ∈ K)
    (h : ρ ⟨z, hz⟩ * ρ ⟨x, hx⟩ = ρ ⟨x, hx⟩ * ρ ⟨z, hz⟩) : z * x = x * z := by
  have h' : ρ (⟨z, hz⟩ * ⟨x, hx⟩) = ρ (⟨x, hx⟩ * ⟨z, hz⟩) := by
    rw [map_mul, map_mul]
    exact h
  exact congrArg Subtype.val (hρ h')


theorem card_lift (hρ : Function.Injective ρ) {B : Subgroup Â} (hB : B ≤ ρ.range) :
    Nat.card ((B.comap ρ).map K.subtype) = Nat.card B := by
  rw [Subgroup.card_map_of_injective K.subtype_injective,
    ← Subgroup.card_map_of_injective hρ (K := B.comap ρ), Subgroup.map_comap_eq,
    inf_eq_right.mpr hB]

section Clauses

variable [Finite G] {p : ℕ} {I T A₀ : Subgroup G}

theorem clauses_of_model (hIK : I ≤ K) (hKN : K ≤ Subgroup.normalizer (I : Set G))
    (hT : IsSylowOf 2 T K) (hA : A₀ ≤ I) (hρ : Function.Injective ρ)
    (h1 : MCl1 p ρ.range (U5K.rm K ρ A₀) (U5K.rm K ρ T))
    (h2 : MCl2 p ρ.range (U5K.rm K ρ A₀) (U5K.rm K ρ T)) :
    Cl1 p I K T A₀ ∧ Cl2 p I K T A₀ := by
  have hTK : T ≤ K := hT.1
  have hAK : A₀ ≤ K := hA.trans hIK
  have hfaith : ∀ t ∈ T, ∀ ht : t ∈ K, ρ ⟨t, ht⟩ = 1 → t = 1 := faithful_of_injective ρ hρ
  have hS : U5K.rm K ρ (pushingUpS T) = pushingUpS (U5K.rm K ρ T) :=
    (U5K.rm_pushingUpS hTK hfaith).1
  have hΩ : U5K.rm K ρ (omegaOneCenterIn T) = omegaOneCenterIn (U5K.rm K ρ T) :=
    Sec1514Five.rm_omegaOneCenterIn hTK hfaith
  have hSK : pushingUpS T ≤ K := (U5K.pushingUpS_le T).trans hTK
  have hcardA : Nat.card (U5K.rm K ρ A₀) = Nat.card A₀ :=
    U5K.card_rm hAK (U5K.injective_comp_subtype (faithful_of_injective ρ hρ))
  have hlift : ∀ Bt : Subgroup Â, Bt ≤ U5K.rm K ρ A₀ →
      ((Bt.comap ρ).map K.subtype ≤ A₀ ∧
        Nat.card ((Bt.comap ρ).map K.subtype) = Nat.card Bt ∧
        ∀ b ∈ (Bt.comap ρ).map K.subtype, ∃ hb : b ∈ K, ρ ⟨b, hb⟩ ∈ Bt) := by
    intro Bt hBt
    refine ⟨?_, card_lift ρ hρ (hBt.trans (U5K.rm_le_range _)), ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨a, haK, haA, ha⟩ := U5K.mem_rm.1 (hBt hy)
      have : (⟨a, haK⟩ : ↥K) = y := hρ ha
      subst this
      exact haA
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
  constructor
  · obtain ⟨ht, hht, Bt, hBtA, hcard, hBtn⟩ := h1
    obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hht
    obtain ⟨hBA, hBcard, hBmem⟩ := hlift Bt hBtA
    refine ⟨(h : G), h.2, (Bt.comap ρ).map K.subtype, hBA, ?_, ?_⟩
    · rw [hBcard, ← hcardA]
      exact hcard
    · intro z hz
      obtain ⟨b, hb, rfl⟩ := hz
      obtain ⟨hbK, hbBt⟩ := hBmem b hb
      have hbI : b ∈ I := hlift Bt hBtA |>.1 hb |> hA
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have : (MulAut.conj (h : G)).toMonoidHom b ∈ I.map (MulAut.conj (h : G)).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hbI
        rwa [map_conj_eq_of_mem hKN h.2] at this
      · have hzK : (h : G) * b * (h : G)⁻¹ ∈ K :=
          K.mul_mem (K.mul_mem h.2 hbK) (K.inv_mem h.2)
        refine mem_normalizer_of_rm ρ hρ hSK hzK ?_
        change ρ ⟨(h : G) * b * (h : G)⁻¹, hzK⟩ ∈ _
        have hmem := hBtn (Subgroup.mem_map_of_mem _ hbBt :
          (MulAut.conj (ρ h)).toMonoidHom (ρ ⟨b, hbK⟩) ∈ Bt.map (MulAut.conj (ρ h)).toMonoidHom)
        rw [← hS] at hmem
        have e : ρ ⟨(h : G) * b * (h : G)⁻¹, hzK⟩ =
            (MulAut.conj (ρ h)).toMonoidHom (ρ ⟨b, hbK⟩) := by
          have : (⟨(h : G) * b * (h : G)⁻¹, hzK⟩ : ↥K) = h * ⟨b, hbK⟩ * h⁻¹ := rfl
          rw [this, map_mul, map_mul, map_inv]
          rfl
        rw [e]
        exact hmem
  · obtain ⟨xt, hxt, hxt1, ht, hht, Bt, hBtA, hcard, hBtc⟩ := h2
    obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hht
    rw [← hΩ] at hxt
    obtain ⟨x, hxK, hxΩ, rfl⟩ := U5K.mem_rm.1 hxt
    obtain ⟨hBA, hBcard, hBmem⟩ := hlift Bt hBtA
    refine ⟨x, hxΩ, ?_, (h : G), h.2, (Bt.comap ρ).map K.subtype, hBA, ?_, ?_⟩
    · intro hx1
      subst hx1
      exact hxt1 (map_one ρ)
    · rw [hBcard, ← hcardA]
      exact hcard
    · intro z hz
      obtain ⟨b, hb, rfl⟩ := hz
      obtain ⟨hbK, hbBt⟩ := hBmem b hb
      have hbI : b ∈ I := hlift Bt hBtA |>.1 hb |> hA
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have : (MulAut.conj (h : G)).toMonoidHom b ∈ I.map (MulAut.conj (h : G)).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hbI
        rwa [map_conj_eq_of_mem hKN h.2] at this
      · have hzK : (h : G) * b * (h : G)⁻¹ ∈ K :=
          K.mul_mem (K.mul_mem h.2 hbK) (K.inv_mem h.2)
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        have hmem := Subgroup.mem_centralizer_iff.1 (hBtc (Subgroup.mem_map_of_mem _ hbBt :
          (MulAut.conj (ρ h)).toMonoidHom (ρ ⟨b, hbK⟩) ∈ Bt.map (MulAut.conj (ρ h)).toMonoidHom))
          (ρ ⟨w, hxK⟩) rfl
        have e : ρ ⟨(h : G) * b * (h : G)⁻¹, hzK⟩ =
            (MulAut.conj (ρ h)).toMonoidHom (ρ ⟨b, hbK⟩) := by
          have : (⟨(h : G) * b * (h : G)⁻¹, hzK⟩ : ↥K) = h * ⟨b, hbK⟩ * h⁻¹ := rfl
          rw [this, map_mul, map_mul, map_inv]
          rfl
        have := commute_of_map_commute ρ hρ hxK hzK (by rw [e]; exact hmem.symm)
        exact this.symm

end Clauses

end Model

section Rows

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Cl1.mono {p : ℕ} {I K K' T A₀ : Subgroup G} (hK : K ≤ K') (h : Cl1 p I K T A₀) :
    Cl1 p I K' T A₀ := by
  obtain ⟨h₀, hh₀, B, hB⟩ := h
  exact ⟨h₀, hK hh₀, B, hB⟩

omit [Finite G] in
theorem Cl2.mono {p : ℕ} {I K K' T A₀ : Subgroup G} (hK : K ≤ K') (h : Cl2 p I K T A₀) :
    Cl2 p I K' T A₀ := by
  obtain ⟨x, hx, hx1, h₀, hh₀, B, hB⟩ := h
  exact ⟨x, hx, hx1, h₀, hK hh₀, B, hB⟩

omit [Finite G] in
theorem isSylowOf_of_le_left {T I H : Subgroup G} (hT : IsSylowOf 2 T H) (hTI : T ≤ I)
    (hIH : I ≤ H) : IsSylowOf 2 T I := by
  refine ⟨hTI, hT.2.1, fun h => hT.2.2 (h.trans ?_)⟩
  exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex T I H hTI hIH)

theorem cl_of_model_rows34 {r p f : ℕ} {I H T A₀ : Subgroup G} (h : KF1514PModel r)
    (hcfg : Config1514 p I H T A₀) (hTI : T ≤ I) (hf : 1 ≤ f) (hcong : ModelCong r p f)
    {b c : GaloisField 2 f} (hirr : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0)
    (e : I ≃* OmegaMinusModel f b c) : Cl1 p I H T A₀ ∧ Cl2 p I H T A₀ := by
  have hsyl : IsSylowOf 2 T I := isSylowOf_of_le_left hcfg.sylow hTI hcfg.le_H
  have hAI : A₀ ≤ I := hcfg.A_le
  let ρ : ↥I →* OmegaMinusModel f b c := e.toMonoidHom
  have hρ : Function.Injective ρ := e.injective
  have hrange : ρ.range = ⊤ := MonoidHom.range_eq_top.2 e.surjective
  have hU : IsSylowOf 2 (U5K.rm I ρ T) (⊤ : Subgroup (OmegaMinusModel f b c)) := by
    have := U5K.isSylowOf_rm (ρ := ρ) hsyl
    rwa [hrange] at this
  have hfaith := faithful_of_injective ρ hρ (T := A₀)
  have hel : IsElementaryAbelian p ↥(U5K.rm I ρ A₀) := U5K.isElementaryAbelian_rm hcfg.A_elem
  have hcard : Nat.card ↥(U5K.rm I ρ A₀) = p ^ 3 := by
    rw [U5K.card_rm hAI (U5K.injective_comp_subtype hfaith), hcfg.A_card]
  obtain ⟨⟨h1, B1, hB1, hc1, hn1⟩, ⟨x, hx, hx1, h2, B2, hB2, hc2, hn2⟩⟩ :=
    h p f b c hcfg.prime hcfg.five_le hf hcong hirr _ _ hU hel hcard
  have hmem : ∀ g : OmegaMinusModel f b c, g ∈ ρ.range := fun g => by
    rw [hrange]; exact Subgroup.mem_top g
  have := clauses_of_model ρ le_rfl Subgroup.le_normalizer hsyl hAI hρ
    ⟨h1, hmem h1, B1, hB1, hc1, hn1⟩ ⟨x, hx, hx1, h2, hmem h2, B2, hB2, hc2, hn2⟩
  exact ⟨this.1.mono hcfg.le_H, this.2.mono hcfg.le_H⟩

theorem kf1514PRow_of_model {r : ℕ} (hr : r = 3 ∨ r = 4) (h : KF1514PModel r) :
    KF1514PRow r := by
  intro G _ _ p I H T A₀ hcfg hLie hTI
  have hTI' : T ≤ I := hTI hr
  rcases hr with rfl | rfl
  · obtain ⟨f, hf, hpf, b, c, hirr, ⟨e⟩⟩ := hLie
    exact cl_of_model_rows34 (r := 3) h hcfg hTI' hf hpf hirr e
  · obtain ⟨f, hf, hpf, b, c, hirr, ⟨e⟩⟩ := hLie
    exact cl_of_model_rows34 (r := 4) h hcfg hTI' hf hpf hirr e

end Rows

section Aut

variable {G : Type} [Group G] {L : Type} [Group L] {I H : Subgroup G}

noncomputable def actModel (hHN : H ≤ Subgroup.normalizer (I : Set G)) (e : ↥I ≃* L) :
    ↥H →* MulAut L :=
  (MulAut.congr e).toMonoidHom.comp (I.normalizerMonoidHom.comp (Subgroup.inclusion hHN))

theorem actModel_apply (hHN : H ≤ Subgroup.normalizer (I : Set G)) (e : ↥I ≃* L) (h : ↥H)
    (i : ↥I) :
    actModel hHN e h (e i) = e (I.normalizerMonoidHom ⟨(h : G), hHN h.2⟩ i) := by
  simp only [actModel, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem actModel_of_mem (hHN : H ≤ Subgroup.normalizer (I : Set G)) (hIH : I ≤ H) (e : ↥I ≃* L)
    (i : ↥I) : actModel hHN e ⟨(i : G), hIH i.2⟩ = MulAut.conj (e i) := by
  ext z
  obtain ⟨w, rfl⟩ := e.surjective z
  rw [actModel_apply]
  have : I.normalizerMonoidHom ⟨(i : G), hHN (hIH i.2)⟩ w = i * w * i⁻¹ := rfl
  rw [this]
  simp [MulAut.conj_apply]

theorem actModel_injective (hHN : H ≤ Subgroup.normalizer (I : Set G))
    (hC : H ⊓ Subgroup.centralizer (I : Set G) = ⊥) (e : ↥I ≃* L) :
    Function.Injective (actModel hHN e) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro h hh
  rw [MonoidHom.mem_ker] at hh
  have h1 : (I.normalizerMonoidHom.comp (Subgroup.inclusion hHN)) h = 1 := by
    apply (MulAut.congr e).injective
    exact hh.trans (map_one _).symm
  have h2 : Subgroup.inclusion hHN h ∈ I.normalizerMonoidHom.ker := h1
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
  have h3 : (h : G) ∈ H ⊓ Subgroup.centralizer (I : Set G) := ⟨h.2, h2⟩
  rw [hC, Subgroup.mem_bot] at h3
  exact (Subgroup.mem_bot).2 (Subtype.ext h3)

end Aut

section Rows12

variable {G : Type} [Group G] [Finite G] {L : Type} [Group L]

omit [Finite G] in
theorem map_conj_one' {Â : Type} [Group Â] (B : Subgroup Â) :
    B.map (MulAut.conj (1 : Â)).toMonoidHom = B := by
  have : (MulAut.conj (1 : Â)).toMonoidHom = MonoidHom.id Â := by
    ext y
    simp
  rw [this, Subgroup.map_id]

theorem cl_of_autGen {p : ℕ} {I H T A₀ : Subgroup G} (hcfg : Config1514 p I H T A₀)
    (e : ↥I ≃* L) (hgen : KF1514PAutGen L p) : Cl1 p I H T A₀ ∧ Cl2 p I H T A₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := actModel hcfg.H_le_N e with hρdef
  have hρ : Function.Injective ρ := actModel_injective hcfg.H_le_N hcfg.faithful e
  have hAH : A₀ ≤ H := hcfg.A_le.trans hcfg.le_H
  have hfaith := faithful_of_injective ρ hρ (T := A₀)
  have hAinn : U5K.rm H ρ A₀ ≤ (MulAut.conj : L →* MulAut L).range := by
    intro a ha
    obtain ⟨x, hxH, hxA, rfl⟩ := U5K.mem_rm.1 ha
    have hxI : x ∈ I := hcfg.A_le hxA
    exact ⟨e ⟨x, hxI⟩, (actModel_of_mem hcfg.H_le_N hcfg.le_H e ⟨x, hxI⟩).symm⟩
  have hInn : (MulAut.conj : L →* MulAut L).range ≤ ρ.range := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨i, rfl⟩ := e.surjective z
    exact ⟨⟨i, hcfg.le_H i.2⟩, actModel_of_mem hcfg.H_le_N hcfg.le_H e i⟩
  have hcard : Nat.card ↥(U5K.rm H ρ A₀) = p ^ 3 := by
    rw [U5K.card_rm hAH (U5K.injective_comp_subtype hfaith), hcfg.A_card]
  obtain ⟨Tt, hTt, ⟨B1, hB1, hc1, hn1⟩, ⟨x, hx, hx1, B2, hB2, hc2, hn2⟩⟩ :=
    hgen ρ.range (U5K.rm H ρ A₀) hInn hAinn (U5K.isElementaryAbelian_rm hcfg.A_elem) hcard
  obtain ⟨T'', hT'', rfl⟩ := Sec1514Five.exists_isSylowOf_rm_eq (N := H) (ρ := ρ) hTt
  have hcl := clauses_of_model ρ hcfg.le_H hcfg.H_le_N hT'' hcfg.A_le hρ
    ⟨1, one_mem _, B1, hB1, hc1, by rw [map_conj_one']; exact hn1⟩
    ⟨x, hx, hx1, 1, one_mem _, B2, hB2, hc2, by rw [map_conj_one']; exact hn2⟩
  obtain ⟨g, hg, hgT⟩ := exists_conj_isSylowOf hT'' hcfg.sylow
  exact ⟨cl1_of_conj hcfg.H_le_N hg hgT hcl.1, cl2_of_conj hcfg.H_le_N hg hgT hcl.2⟩

theorem kf1514PRow_of_aut {r : ℕ} (hr : r = 1 ∨ r = 2) (h : KF1514PAut r) : KF1514PRow r := by
  intro G _ _ p I H T A₀ hcfg hLie _
  rcases hr with rfl | rfl
  · obtain ⟨f, hf, hpf, ⟨e⟩⟩ := hLie
    exact cl_of_autGen hcfg e (h p f hcfg.prime hcfg.five_le hf hpf)
  · obtain ⟨f, hf, hpf, ⟨e⟩⟩ := hLie
    exact cl_of_autGen hcfg e (h p f hcfg.prime hcfg.five_le hf hpf)

end Rows12

theorem kf1514P_of_rows (h1 : KF1514PAut 1) (h2 : KF1514PAut 2) (h3 : KF1514PModel 3)
    (h4 : KF1514PModel 4) : KF1514P := by
  intro r hr1 hr4
  interval_cases r
  · exact kf1514PRow_of_aut (Or.inl rfl) h1
  · exact kf1514PRow_of_aut (Or.inr rfl) h2
  · exact kf1514PRow_of_model (Or.inl rfl) h3
  · exact kf1514PRow_of_model (Or.inr rfl) h4

end AUTSL

end CFSG.RankThree.PartOne
