module

public import CFSG.Milestones.ASVolI.C31.J4KWChar2

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

@[expose] def burnsideJ4KW_MaxNonParabolicP0 : Prop :=
  ∀ R : Subgroup J, IsPGroup 2 ↥R → R ≠ ⊥ → R ≤ P0 →
    (∀ S : Subgroup J, IsPGroup 2 ↥S → S ≤ Subgroup.normalizer (R : Set J) →
      Nat.card ↥S ≤ Nat.card ↥(P0 ⊓ Subgroup.normalizer (R : Set J))) →
    (∀ Y : Subgroup J, IsPGroup 2 ↥Y → Y ≠ ⊥ →
      Subgroup.normalizer (R : Set J) ≤ Subgroup.normalizer (Y : Set J) →
      Subgroup.normalizer (Y : Set J) = Subgroup.normalizer (R : Set J)) →
    (∀ Y : Subgroup J, IsPGroup 2 ↥Y →
      Subgroup.normalizer (R : Set J) ≤ Subgroup.normalizer (Y : Set J) → Y ≤ R) →
    Subgroup.centralizer (R : Set J) ≤ R →
    (∀ g : J, ¬ P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (R : Set J)) →
    ∃ g : J, Subgroup.normalizer (R : Set J) ≤ CFSG.Quasithin.KGJ4.M4.map (MulAut.conj g).toMonoidHom

theorem burnsideJ4KW_mem_map_conj {X : Subgroup J} {c x : J} :
    x ∈ X.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨c⁻¹ * x * c, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem burnsideJ4KW_map_conj_map_conj (X : Subgroup J) (c c' : J) :
    (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c').toMonoidHom =
      X.map (MulAut.conj (c' * c)).toMonoidHom := by
  ext x
  rw [burnsideJ4KW_mem_map_conj, burnsideJ4KW_mem_map_conj, burnsideJ4KW_mem_map_conj]
  have e : c⁻¹ * (c'⁻¹ * x * c') * c = (c' * c)⁻¹ * x * (c' * c) := by group
  rw [e]

theorem burnsideJ4KW_map_conj_inv_map_conj (X : Subgroup J) (c : J) :
    (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = X := by
  rw [burnsideJ4KW_map_conj_map_conj, inv_mul_cancel]
  ext x
  rw [burnsideJ4KW_mem_map_conj]
  simp

theorem burnsideJ4KW_map_conj_le_iff {X Y : Subgroup J} (c : J) :
    X.map (MulAut.conj c).toMonoidHom ≤ Y.map (MulAut.conj c).toMonoidHom ↔ X ≤ Y := by
  constructor
  · intro h
    have h2 := Subgroup.map_mono (f := (MulAut.conj c⁻¹).toMonoidHom) h
    rwa [burnsideJ4KW_map_conj_inv_map_conj, burnsideJ4KW_map_conj_inv_map_conj] at h2
  · exact Subgroup.map_mono

theorem burnsideJ4KW_normalizer_map_conj (X : Subgroup J) (c : J) :
    Subgroup.normalizer ((X.map (MulAut.conj c).toMonoidHom : Subgroup J) : Set J) =
      (Subgroup.normalizer (X : Set J)).map (MulAut.conj c).toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq X (MulAut.conj c)).symm

theorem burnsideJ4KW_map_conj_ne_bot {X : Subgroup J} (hX : X ≠ ⊥) (c : J) :
    X.map (MulAut.conj c).toMonoidHom ≠ ⊥ := by
  intro h
  apply hX
  rw [← burnsideJ4KW_map_conj_inv_map_conj X c, h, Subgroup.map_bot]

theorem burnsideJ4KW_card_map_conj (X : Subgroup J) (c : J) :
    Nat.card ↥(X.map (MulAut.conj c).toMonoidHom) = Nat.card ↥X := by
  have hinj : Function.Injective ((MulAut.conj c).toMonoidHom : J →* J) := by
    intro x y hxy
    have h1 : c * x * c⁻¹ = c * y * c⁻¹ := hxy
    simpa using h1
  exact Subgroup.card_map_of_injective hinj

theorem burnsideJ4KW_exists_conj_P0
    (P : Sylow 2 J) :
    ∃ g : J, (P : Subgroup J) = P0.map (MulAut.conj g).toMonoidHom := by
  have hF := j4Facts
  have hcard : Nat.card ↥P0 = 2 ^ (Nat.card ↥J).factorization 2 := by
    rw [card_P0 hF.mat hF, card_J_factorization hF]
  let P0S : Sylow 2 J := Sylow.ofCard P0 hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J P0S P
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

theorem burnsideJ4KW_maxNonParabolicCore_of_P0
    (h : burnsideJ4KW_MaxNonParabolicP0) : burnsideJ4KW_MaxNonParabolicCore := by
  intro R hR2 hRne hmax hO2 hcent hnp
  set L := Subgroup.normalizer (R : Set J) with hLdef
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := ↥L)
  set S' : Subgroup J := (S : Subgroup ↥L).map L.subtype with hS'def
  have hS'2 : IsPGroup 2 ↥S' := S.isPGroup'.map _
  have hS'L : S' ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨P, hSP⟩ := hS'2.exists_le_sylow
  obtain ⟨g, hg⟩ := burnsideJ4KW_exists_conj_P0 P
  have hRS' : R ≤ S' := by
    haveI hn : (Subgroup.comap L.subtype R).Normal :=
      burnsideJ4KW_subgroupOf_normal Subgroup.le_normalizer le_rfl
    have hRS : R.subgroupOf L ≤ (S : Subgroup ↥L) :=
      IsPGroup.le_sylow_of_normal (hR2.comap_subtype (K := L)) S
    intro x hx
    exact ⟨⟨x, Subgroup.le_normalizer hx⟩, hRS (show x ∈ R from hx), rfl⟩
  set R' := R.map (MulAut.conj g⁻¹).toMonoidHom with hR'def
  have hRR' : R = R'.map (MulAut.conj g).toMonoidHom := by
    rw [hR'def, burnsideJ4KW_map_conj_map_conj, mul_inv_cancel]
    ext x
    simp [MulAut.conj_apply]
  have hNR' : Subgroup.normalizer (R' : Set J) = L.map (MulAut.conj g⁻¹).toMonoidHom :=
    burnsideJ4KW_normalizer_map_conj R g⁻¹
  have hNR : L = (Subgroup.normalizer (R' : Set J)).map (MulAut.conj g).toMonoidHom := by
    rw [hNR', burnsideJ4KW_map_conj_map_conj, mul_inv_cancel]
    ext x
    simp [MulAut.conj_apply]
  have hSP0 : S'.map (MulAut.conj g⁻¹).toMonoidHom ≤ P0 := by
    have h1 : S' ≤ P0.map (MulAut.conj g).toMonoidHom := hg ▸ hSP
    have h2 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h1
    rwa [burnsideJ4KW_map_conj_inv_map_conj] at h2
  have hR'P0 : R' ≤ P0 := (Subgroup.map_mono hRS').trans hSP0
  have hSyl : ∀ S2 : Subgroup J, IsPGroup 2 ↥S2 → S2 ≤ Subgroup.normalizer (R' : Set J) →
      Nat.card ↥S2 ≤ Nat.card ↥(P0 ⊓ Subgroup.normalizer (R' : Set J)) := by
    intro S2 hS2 hS2N
    set S3 := S2.map (MulAut.conj g).toMonoidHom with hS3def
    have hS3L : S3 ≤ L := by
      rw [hNR]
      exact Subgroup.map_mono hS2N
    have hS32 : IsPGroup 2 ↥(S3.subgroupOf L) := (hS2.map _).comap_subtype
    obtain ⟨Q, hQ⟩ := hS32.exists_le_sylow
    have hc1 : Nat.card ↥S2 = Nat.card ↥(S3.subgroupOf L) := by
      rw [← burnsideJ4KW_card_map_conj S2 g, ← hS3def]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS3L).toEquiv).symm
    have hc2 : Nat.card ↥(S3.subgroupOf L) ≤ Nat.card ↥(Q : Subgroup ↥L) :=
      Subgroup.card_le_of_le hQ
    have hc3 : Nat.card ↥(Q : Subgroup ↥L) = Nat.card ↥(S : Subgroup ↥L) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    have hc4 : Nat.card ↥(S : Subgroup ↥L) = Nat.card ↥S' :=
      (Subgroup.card_map_of_injective L.subtype_injective).symm
    have hc5 : Nat.card ↥S' ≤ Nat.card ↥(P0 ⊓ Subgroup.normalizer (R' : Set J)) := by
      rw [← burnsideJ4KW_card_map_conj S' g⁻¹]
      refine Subgroup.card_le_of_le (le_inf hSP0 ?_)
      rw [hNR']
      exact Subgroup.map_mono hS'L
    omega
  have hmax' : ∀ Y : Subgroup J, IsPGroup 2 ↥Y → Y ≠ ⊥ →
      Subgroup.normalizer (R' : Set J) ≤ Subgroup.normalizer (Y : Set J) →
      Subgroup.normalizer (Y : Set J) = Subgroup.normalizer (R' : Set J) := by
    intro Y hY hYne hRY
    set Y' := Y.map (MulAut.conj g).toMonoidHom with hY'def
    have hNY' : Subgroup.normalizer (Y' : Set J) =
        (Subgroup.normalizer (Y : Set J)).map (MulAut.conj g).toMonoidHom :=
      burnsideJ4KW_normalizer_map_conj Y g
    have h1 : L ≤ Subgroup.normalizer (Y' : Set J) := by
      rw [hNY', hNR]
      exact Subgroup.map_mono hRY
    have h2 := hmax Y' (hY.map _) (burnsideJ4KW_map_conj_ne_bot hYne g) h1
    have h3 : (Subgroup.normalizer (Y : Set J)).map (MulAut.conj g).toMonoidHom =
        (Subgroup.normalizer (R' : Set J)).map (MulAut.conj g).toMonoidHom := by
      rw [← hNY', h2, hNR]
    have h4 := congrArg (fun K : Subgroup J => K.map (MulAut.conj g⁻¹).toMonoidHom) h3
    simpa only [burnsideJ4KW_map_conj_inv_map_conj] using h4
  have hO2' : ∀ Y : Subgroup J, IsPGroup 2 ↥Y →
      Subgroup.normalizer (R' : Set J) ≤ Subgroup.normalizer (Y : Set J) → Y ≤ R' := by
    intro Y hY hRY
    have hNY' : Subgroup.normalizer ((Y.map (MulAut.conj g).toMonoidHom : Subgroup J) : Set J) =
        (Subgroup.normalizer (Y : Set J)).map (MulAut.conj g).toMonoidHom :=
      burnsideJ4KW_normalizer_map_conj Y g
    have h1 : L ≤ Subgroup.normalizer ((Y.map (MulAut.conj g).toMonoidHom : Subgroup J) : Set J) := by
      rw [hNY', hNR]
      exact Subgroup.map_mono hRY
    have h2 := hO2 _ (hY.map _) h1
    rw [hRR', burnsideJ4KW_map_conj_le_iff] at h2
    exact h2
  have hcent' : Subgroup.centralizer (R' : Set J) ≤ R' := by
    intro c hc
    rw [hR'def, burnsideJ4KW_mem_map_conj, inv_inv]
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : g⁻¹ * r * g ∈ R' := by
      rw [hR'def, burnsideJ4KW_mem_map_conj, inv_inv]
      simpa [mul_assoc] using hr
    have := Subgroup.mem_centralizer_iff.1 hc _ hr'
    calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * r := by group
  have hnp' : ∀ h : J, ¬ P0.map (MulAut.conj h).toMonoidHom ≤ Subgroup.normalizer (R' : Set J) := by
    intro k hk
    apply hnp (g * k)
    have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hk
    rw [burnsideJ4KW_map_conj_map_conj, ← hNR] at h1
    exact h1
  obtain ⟨k, hk⟩ := h R' (hR2.map _) (burnsideJ4KW_map_conj_ne_bot hRne g⁻¹) hR'P0 hSyl hmax'
    hO2' hcent' hnp'
  refine ⟨g * k, ?_⟩
  rw [hNR]
  have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hk
  rwa [burnsideJ4KW_map_conj_map_conj] at h1

theorem burnsideJ4KW_core_of_maxNonParabolicP0
    (h : burnsideJ4KW_MaxNonParabolicP0) : burnsideC31_J4KWCore :=
  burnsideJ4KW_core_of_maxNonParabolicCore (burnsideJ4KW_maxNonParabolicCore_of_P0 h)

end CFSG.ASVolI
