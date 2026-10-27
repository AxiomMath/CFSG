module

public import CFSG.Quasithin.EmptyFaithful.S152He9L
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def piOf (H : Subgroup G) (φ : OTwoQuot H ≃* W5) : ↥H →* W5 :=
  φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))

theorem piOf_surj (H : Subgroup G) (φ : OTwoQuot H ≃* W5) : Function.Surjective (piOf H φ) :=
  φ.surjective.comp (QuotientGroup.mk'_surjective _)

theorem piOf_ker (H : Subgroup G) (φ : OTwoQuot H ≃* W5) :
    (piOf H φ).ker = CFSG.Open.pCore 2 ↥H := by
  ext x
  simp [piOf, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]

theorem piOf_wrData (H : Subgroup G) (φ : OTwoQuot H ≃* W5) : WrData (piOf H φ) := by
  refine ⟨piOf_surj H φ, ?_⟩
  rw [piOf_ker]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.pCore_isPGroup 2

structure WrH (H T K₁ K₂ : Subgroup G) (π : ↥H →* W5) : Prop where
  data : WrData π
  ker_eq : π.ker = CFSG.Open.pCore 2 ↥H
  T_le : (T.subgroupOf H).map π ≤ W5.Sw
  comp₁ : K₁ ∈ cComp H
  comp₂ : K₂ ∈ cComp H
  map₁ : (K₁.subgroupOf H).map π = W5.A1
  map₂ : (K₂.subgroupOf H).map π = W5.A2

theorem exists_wrH {T H : Subgroup G} (hT : IsSylowTwoOf T H)
    (e : Nonempty (OTwoQuot H ≃* W5)) :
    ∃ (π : ↥H →* W5) (K₁ K₂ : Subgroup G), WrH H T K₁ K₂ π := by
  obtain ⟨φ⟩ := e
  have hT2' : IsPGroup 2 (T.subgroupOf H) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  have hTi' : ¬ 2 ∣ (T.subgroupOf H).index := hT.2.2
  obtain ⟨g, hg⟩ := W5.exists_conj_le_Sw (P := (T.subgroupOf H).map (piOf H φ))
    (hT2'.map (piOf H φ)) (map_sylow_odd (piOf_wrData H φ) hTi')
  let π : ↥H →* W5 := (MulAut.conj g).toMonoidHom.comp (piOf H φ)
  have hker : π.ker = (piOf H φ).ker := by
    ext x
    simp [π, MonoidHom.mem_ker]
  have hπ : WrData π := by
    refine ⟨(MulAut.conj g).surjective.comp (piOf_surj H φ), ?_⟩
    rw [hker]
    exact (piOf_wrData H φ).ker2
  obtain ⟨K₁', K₂', h1, h2, m1, m2⟩ := exists_components hπ
  refine ⟨π, K₁'.map H.subtype, K₂'.map H.subtype, hπ, hker.trans (piOf_ker H φ), ?_,
    map_subtype_mem_cComp h1,
    map_subtype_mem_cComp h2, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hg _ ⟨x, hx, rfl⟩
  · have : (K₁'.map H.subtype).subgroupOf H = K₁' :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective K₁'
    rw [this]
    exact m1
  · have : (K₂'.map H.subtype).subgroupOf H = K₂' :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective K₂'
    rw [this]
    exact m2

theorem mem_normalizer_subtype_iff {H K : Subgroup G} (hKH : K ≤ H) {g : G} (hg : g ∈ H) :
    g ∈ Subgroup.normalizer (K : Set G) ↔
      (⟨g, hg⟩ : ↥H) ∈ Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hn x
    have := hn (x : G)
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hn y
    constructor
    · intro hy
      have hyH : y ∈ H := hKH hy
      have := (hn ⟨y, hyH⟩).1 (by simpa [Subgroup.mem_subgroupOf] using hy)
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hy
      have h1 : g * y * g⁻¹ ∈ H := hKH hy
      have hyH : y ∈ H := by
        have : g⁻¹ * (g * y * g⁻¹) * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) h1) hg
        simpa [mul_assoc] using this
      have := (hn ⟨y, hyH⟩).2 (by simpa [Subgroup.mem_subgroupOf] using hy)
      simpa [Subgroup.mem_subgroupOf] using this

namespace WrH

variable {H T K₁ K₂ : Subgroup G} {π : ↥H →* W5}

theorem le₁ (h : WrH H T K₁ K₂ π) : K₁ ≤ H := le_of_mem_cComp h.comp₁

theorem le₂ (h : WrH H T K₁ K₂ π) : K₂ ≤ H := le_of_mem_cComp h.comp₂

theorem comp₁' (h : WrH H T K₁ K₂ π) : K₁.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) :=
  subgroupOf_mem_cComp h.comp₁

theorem comp₂' (h : WrH H T K₁ K₂ π) : K₂.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) :=
  subgroupOf_mem_cComp h.comp₂

theorem mem_normalizer₁ (h : WrH H T K₁ K₂ π) {g : G} (hg : g ∈ H) :
    g ∈ Subgroup.normalizer (K₁ : Set G) ↔ π ⟨g, hg⟩ ∈ W5.base := by
  rw [mem_normalizer_subtype_iff h.le₁ hg]
  exact mem_normalizer_iff_K1 h.data h.comp₁' h.map₁ _

omit [Finite G] in
theorem map_conj_subtype {K : Subgroup G} (hKH : K ≤ H) {g : G} (hg : g ∈ H) :
    K.map (MulAut.conj g).toMonoidHom =
      (K.subgroupOf H).map (H.subtype.comp (MulAut.conj (⟨g, hg⟩ : ↥H)).toMonoidHom) := by
  calc K.map (MulAut.conj g).toMonoidHom
      = ((K.subgroupOf H).map H.subtype).map (MulAut.conj g).toMonoidHom := by
        rw [Subgroup.map_subgroupOf_eq_of_le hKH]
    _ = (K.subgroupOf H).map ((MulAut.conj g).toMonoidHom.comp H.subtype) := by
        rw [Subgroup.map_map]
    _ = _ := by
        congr 1

theorem conj_eq₁ (h : WrH H T K₁ K₂ π) {g : G} (hg : g ∈ H) (hπ : π ⟨g, hg⟩ ∉ W5.base) :
    K₁.map (MulAut.conj g).toMonoidHom = K₂ := by
  have := conj_eq_of_not_mem_base h.data h.comp₁' h.comp₂' h.map₁ h.map₂ hπ
  have h2 := congrArg (Subgroup.map H.subtype) this
  rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le h.le₂] at h2
  rw [map_conj_subtype h.le₁ hg]
  exact h2

theorem sup_eq (h : WrH H T K₁ K₂ π) (hT : IsSylowTwoOf T H) : K₁ ⊔ K₂ ⊔ T = H := by
  have hT2' : IsPGroup 2 (T.subgroupOf H) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  have h1 := sup_eq_top h.data h.map₁ h.map₂ hT2' hT.2.2
  have h2 := congrArg (Subgroup.map H.subtype) h1
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le h.le₁,
    Subgroup.map_subgroupOf_eq_of_le h.le₂, Subgroup.map_subgroupOf_eq_of_le hT.1,
    Subgroup.map_top, Subgroup.range_subtype] at h2
  exact h2

theorem inf_normalizer_subgroupOf (h : WrH H T K₁ K₂ π) (hTH : T ≤ H) :
    (T ⊓ Subgroup.normalizer (K₁ : Set G)).subgroupOf H =
      T.subgroupOf H ⊓ Subgroup.normalizer ((K₁.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have := mem_normalizer_subtype_iff h.le₁ x.2
  simp only [Subtype.coe_eta] at this
  rw [this]

theorem normalizer_subgroupOf (h : WrH H T K₁ K₂ π) :
    (H ⊓ Subgroup.normalizer (K₁ : Set G)).subgroupOf H =
      Subgroup.normalizer ((K₁.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have := mem_normalizer_subtype_iff h.le₁ x.2
  simp only [Subtype.coe_eta] at this
  rw [this]
  exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩

theorem relIndex_S (h : WrH H T K₁ K₂ π) (hT : IsSylowTwoOf T H) :
    (T ⊓ Subgroup.normalizer (K₁ : Set G)).relIndex T = 2 := by
  have hT2' : IsPGroup 2 (T.subgroupOf H) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  rw [← Subgroup.relIndex_subgroupOf hT.1, inf_normalizer_subgroupOf h hT.1]
  exact relIndex_inf_normalizer h.data h.comp₁' h.map₁ hT2' hT.2.2

theorem isSylow_S (h : WrH H T K₁ K₂ π) (hT : IsSylowTwoOf T H) :
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (K₁ : Set G)) (H ⊓ Subgroup.normalizer (K₁ : Set G)) := by
  have hT2' : IsPGroup 2 (T.subgroupOf H) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  refine ⟨inf_le_inf_right _ hT.1, hT.2.1.to_inf_left, ?_⟩
  have hle : H ⊓ Subgroup.normalizer (K₁ : Set G) ≤ H := inf_le_left
  have := Subgroup.relIndex_subgroupOf (H := T ⊓ Subgroup.normalizer (K₁ : Set G))
    (K := H ⊓ Subgroup.normalizer (K₁ : Set G)) (L := H) hle
  unfold Subgroup.relIndex at this
  rw [inf_normalizer_subgroupOf h hT.1, normalizer_subgroupOf h] at this
  show ¬ 2 ∣ ((T ⊓ Subgroup.normalizer (K₁ : Set G)).subgroupOf (H ⊓ Subgroup.normalizer (K₁ : Set G))).index
  rw [← this]
  exact relIndex_inf_normalizer_odd h.data h.comp₁' h.map₁ hT2' hT.2.2

@[expose] noncomputable def psi₁ (h : WrH H T K₁ K₂ π) : ↥K₁ →* ↥W5.A1 :=
  (π.comp (Subgroup.inclusion h.le₁)).codRestrict W5.A1 (fun x => by
    rw [← h.map₁]
    exact ⟨Subgroup.inclusion h.le₁ x, x.2, rfl⟩)

theorem psi₁_surj (h : WrH H T K₁ K₂ π) : Function.Surjective (psi₁ h) := by
  intro a
  have ha : (a : W5) ∈ (K₁.subgroupOf H).map π := by rw [h.map₁]; exact a.2
  obtain ⟨y, hy, hya⟩ := ha
  refine ⟨⟨(y : G), hy⟩, Subtype.ext ?_⟩
  show π (Subgroup.inclusion h.le₁ ⟨(y : G), hy⟩) = a
  rw [show Subgroup.inclusion h.le₁ ⟨(y : G), hy⟩ = y from rfl]
  exact hya

theorem psi₁_ker (h : WrH H T K₁ K₂ π) : (psi₁ h).ker = CFSG.Open.pCore 2 ↥K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  ·
    have : (psi₁ h).ker.Normal := (psi₁ h).normal_ker
    refine CFSG.LieType.BorelTits.le_pCore 2 this ?_
    intro x
    have hx : π (Subgroup.inclusion h.le₁ (x : ↥K₁)) = 1 := by
      have := x.2
      rw [MonoidHom.mem_ker] at this
      simpa [psi₁, Subtype.ext_iff] using this
    have hmem : Subgroup.inclusion h.le₁ (x : ↥K₁) ∈ CFSG.Open.pCore 2 ↥H := by
      rw [← h.ker_eq]; exact hx
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥H))
      ⟨_, hmem⟩
    refine ⟨k, ?_⟩
    have h1 : (Subgroup.inclusion h.le₁ ((x : ↥K₁))) ^ 2 ^ k = 1 := by
      have := congrArg (fun y : ↥(CFSG.Open.pCore 2 ↥H) => (y : ↥H)) hk
      simpa using this
    have h2 : ((x : ↥K₁)) ^ 2 ^ k = 1 := by
      apply Subgroup.inclusion_injective h.le₁
      rw [map_pow, map_one]
      exact h1
    exact Subtype.ext (by simpa using h2)
  · intro z hz
    have hn : (CFSG.Open.pCore 2 ↥K₁).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have hmap : (CFSG.Open.pCore 2 ↥K₁).map (psi₁ h) = ⊥ := by
      have := (hn.map (psi₁ h) (psi₁_surj h))
      rcases (W5.A1_simple).eq_bot_or_eq_top_of_normal ((CFSG.Open.pCore 2 ↥K₁).map (psi₁ h)) with h0 | h0
      · exact h0
      · exfalso
        have hp : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥K₁).map (psi₁ h)) :=
          (CFSG.LieType.BorelTits.pCore_isPGroup 2 : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥K₁)).map _
        rw [h0] at hp
        have hp' : IsPGroup 2 ↥W5.A1 := hp.of_equiv Subgroup.topEquiv
        obtain ⟨n, hn2⟩ := hp'.exists_card_eq
        rw [W5.card_A1] at hn2
        have h3 : 3 ∣ 2 ^ n := by rw [← hn2]; norm_num
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
        omega
    have : psi₁ h z = 1 := by
      have hz' : psi₁ h z ∈ (CFSG.Open.pCore 2 ↥K₁).map (psi₁ h) := ⟨z, hz, rfl⟩
      rw [hmap] at hz'
      exact hz'
    exact this

theorem nonempty_oTwoQuot₁ (h : WrH H T K₁ K₂ π) : Nonempty (OTwoQuot K₁ ≃* ↥W5.A5) := by
  have e1 : (↥K₁ ⧸ CFSG.Open.pCore 2 ↥K₁) ≃* (↥K₁ ⧸ (psi₁ h).ker) :=
    QuotientGroup.quotientMulEquivOfEq (psi₁_ker h).symm
  exact ⟨e1.trans ((QuotientGroup.quotientKerEquivOfSurjective _ (psi₁_surj h)).trans
    W5.A1equiv.symm)⟩

end WrH

end CFSG.Quasithin.He9
