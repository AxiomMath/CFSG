module

public import CFSG.LocalAnalysis.StandardType.GGTwoSignalizerRadical

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.LieType.BorelTits

section Good

variable {G : Type*} [Group G]

@[expose] def GGOppRadGood (G₀ Q : Subgroup G) : Prop :=
  ∃ V₀ ∈ ggOppositeRadicals G₀ Q, Q ⊔ V₀ = G₀ ∧
    ∀ V ∈ ggOppositeRadicals G₀ Q, ∃ u ∈ Q, V = V₀.map (MulAut.conj u).toMonoidHom

theorem ggOppRadGood_iff {G₀ Q : Subgroup G} :
    GGOppRadGood G₀ Q ↔ ∃ V₀ : Subgroup G,
      pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (V₀ : Set G)) = V₀ ∧ Nat.card V₀ = Nat.card Q ∧
        V₀ ⊓ (G₀ ⊓ Subgroup.normalizer (Q : Set G)) = ⊥ ∧ Q ⊔ V₀ = G₀ ∧
        ∀ V : Subgroup G, pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (V : Set G)) = V →
          Nat.card V = Nat.card Q → V ⊓ (G₀ ⊓ Subgroup.normalizer (Q : Set G)) = ⊥ →
          ∃ u ∈ Q, V = V₀.map (MulAut.conj u).toMonoidHom :=
  ⟨fun ⟨V₀, ⟨h₁, h₂, h₃⟩, h₄, h₅⟩ => ⟨V₀, h₁, h₂, h₃, h₄, fun V a b c => h₅ V ⟨a, b, c⟩⟩,
    fun ⟨V₀, h₁, h₂, h₃, h₄, h₅⟩ => ⟨V₀, ⟨h₁, h₂, h₃⟩, h₄, fun V ⟨a, b, c⟩ => h₅ V a b c⟩⟩

theorem GGOppRadGood.count [Finite G] {G₀ Q : Subgroup G} (hQ : GGRadicalTwo G₀ Q)
    (h : GGOppRadGood G₀ Q) :
    (∃ k : ℕ, Nat.card (ggOppositeRadicals G₀ Q) = 2 ^ k) ∧
      ∀ V ∈ ggOppositeRadicals G₀ Q, Q ⊔ V = G₀ := by
  obtain ⟨V₀, hV₀, hgen, hconj⟩ := h
  exact GGTwoSig.count_of_conj hQ hV₀ hgen hconj

theorem GGOppRadGood.countNormal [Finite G] {G₀ Q : Subgroup G} (hQ : GGRadicalTwo G₀ Q)
    (h : GGOppRadGood G₀ Q) :
    (∃ k : ℕ, Nat.card (ggOppositeRadicals G₀ Q) = 2 ^ k) ∧
      ∀ V ∈ ggOppositeRadicals G₀ Q, G₀ ≤ Subgroup.normalizer ((Q ⊔ V : Subgroup G) : Set G) := by
  obtain ⟨hc, hg⟩ := h.count hQ
  exact ⟨hc, fun V hV => by rw [hg V hV]; exact Subgroup.le_normalizer⟩

theorem pCoreOf_inf_normalizer_map_conj (p : ℕ) {G₀ V : Subgroup G}
    (hV : pCoreOf p (G₀ ⊓ Subgroup.normalizer (V : Set G)) = V) {g : G}
    (hg : g ∈ Subgroup.normalizer (G₀ : Set G)) :
    pCoreOf p (G₀ ⊓ Subgroup.normalizer
        ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) =
      V.map (MulAut.conj g).toMonoidHom := by
  have h1 : G₀ ⊓ Subgroup.normalizer ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (G₀ ⊓ Subgroup.normalizer (V : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [GGTwoSig.map_conj_inf, GGTwoSig.map_conj_normalizer, GGTwoSig.map_conj_eq hg]
  rw [h1, pCoreOf_map_mulEquiv p (MulAut.conj g), hV]

theorem map_conj_opposite (p : ℕ) {G₀ Q V : Subgroup G}
    (hV : pCoreOf p (G₀ ⊓ Subgroup.normalizer (V : Set G)) = V) (hVc : Nat.card V = Nat.card Q)
    (hVb : V ⊓ (G₀ ⊓ Subgroup.normalizer (Q : Set G)) = ⊥) {g : G}
    (hg : g ∈ Subgroup.normalizer (G₀ : Set G)) :
    pCoreOf p (G₀ ⊓ Subgroup.normalizer
        ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) =
        V.map (MulAut.conj g).toMonoidHom ∧
      Nat.card (V.map (MulAut.conj g).toMonoidHom) =
        Nat.card (Q.map (MulAut.conj g).toMonoidHom) ∧
      V.map (MulAut.conj g).toMonoidHom ⊓ (G₀ ⊓ Subgroup.normalizer
        ((Q.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) = ⊥ := by
  refine ⟨pCoreOf_inf_normalizer_map_conj p hV hg, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hVc]
  · have h1 : G₀ ⊓ Subgroup.normalizer ((Q.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
        (G₀ ⊓ Subgroup.normalizer (Q : Set G)).map (MulAut.conj g).toMonoidHom := by
      rw [GGTwoSig.map_conj_inf, GGTwoSig.map_conj_eq hg, GGTwoSig.map_conj_normalizer]
    rw [h1, ← GGTwoSig.map_conj_inf, hVb, Subgroup.map_bot]

theorem map_conj_mem_ggOppositeRadicals {G₀ Q V : Subgroup G}
    (hV : V ∈ ggOppositeRadicals G₀ Q) {g : G} (hg : g ∈ Subgroup.normalizer (G₀ : Set G)) :
    V.map (MulAut.conj g).toMonoidHom ∈
      ggOppositeRadicals G₀ (Q.map (MulAut.conj g).toMonoidHom) :=
  map_conj_opposite 2 hV.1 hV.2.1 hV.2.2 hg

theorem exists_opposite_map_conj (p : ℕ) {G₀ Q : Subgroup G}
    (h : ∃ V₀ : Subgroup G, pCoreOf p (G₀ ⊓ Subgroup.normalizer (V₀ : Set G)) = V₀ ∧
      Nat.card V₀ = Nat.card Q ∧ V₀ ⊓ (G₀ ⊓ Subgroup.normalizer (Q : Set G)) = ⊥ ∧
      Q ⊔ V₀ = G₀ ∧
      ∀ V : Subgroup G, pCoreOf p (G₀ ⊓ Subgroup.normalizer (V : Set G)) = V →
        Nat.card V = Nat.card Q → V ⊓ (G₀ ⊓ Subgroup.normalizer (Q : Set G)) = ⊥ →
        ∃ u ∈ Q, V = V₀.map (MulAut.conj u).toMonoidHom)
    {g : G} (hg : g ∈ Subgroup.normalizer (G₀ : Set G)) :
    ∃ V₀ : Subgroup G, pCoreOf p (G₀ ⊓ Subgroup.normalizer (V₀ : Set G)) = V₀ ∧
      Nat.card V₀ = Nat.card (Q.map (MulAut.conj g).toMonoidHom) ∧
      V₀ ⊓ (G₀ ⊓ Subgroup.normalizer
        ((Q.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) = ⊥ ∧
      Q.map (MulAut.conj g).toMonoidHom ⊔ V₀ = G₀ ∧
      ∀ V : Subgroup G, pCoreOf p (G₀ ⊓ Subgroup.normalizer (V : Set G)) = V →
        Nat.card V = Nat.card (Q.map (MulAut.conj g).toMonoidHom) →
        V ⊓ (G₀ ⊓ Subgroup.normalizer
          ((Q.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) = ⊥ →
        ∃ u ∈ Q.map (MulAut.conj g).toMonoidHom, V = V₀.map (MulAut.conj u).toMonoidHom := by
  obtain ⟨V₀, hrad, hcard, hbot, hgen, hconj⟩ := h
  obtain ⟨hrad', hcard', hbot'⟩ := map_conj_opposite p hrad hcard hbot hg
  refine ⟨V₀.map (MulAut.conj g).toMonoidHom, hrad', hcard', hbot', ?_,
    fun V hVrad hVcard hVbot => ?_⟩
  · rw [← Subgroup.map_sup, hgen, GGTwoSig.map_conj_eq hg]
  · obtain ⟨hVrad', hVcard', hVbot'⟩ := map_conj_opposite p hVrad hVcard hVbot (inv_mem hg)
    rw [← GGTwoSig.map_conj_mul, inv_mul_cancel, GGTwoSig.map_conj_one] at hVcard' hVbot'
    obtain ⟨u, hu, huV⟩ := hconj _ hVrad' hVcard' hVbot'
    refine ⟨g * u * g⁻¹, ⟨u, hu, rfl⟩, ?_⟩
    calc V = (V.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
          rw [← GGTwoSig.map_conj_mul, mul_inv_cancel, GGTwoSig.map_conj_one]
      _ = (V₀.map (MulAut.conj u).toMonoidHom).map (MulAut.conj g).toMonoidHom := by rw [huV]
      _ = (V₀.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (g * u * g⁻¹)).toMonoidHom := by
          rw [← GGTwoSig.map_conj_mul, ← GGTwoSig.map_conj_mul]
          congr 2
          group

theorem GGOppRadGood.map_conj {G₀ Q : Subgroup G} (h : GGOppRadGood G₀ Q) {g : G}
    (hg : g ∈ Subgroup.normalizer (G₀ : Set G)) :
    GGOppRadGood G₀ (Q.map (MulAut.conj g).toMonoidHom) :=
  ggOppRadGood_iff.mpr (exists_opposite_map_conj 2 (ggOppRadGood_iff.mp h) hg)

end Good

namespace GGOppRad

section Transfer

variable {H : Type*} [Group H] [Finite H] {G : Type*} [Group G] (ψ : H →* G)

omit [Finite H] in
theorem map_map_conj (A : Subgroup H) (h : H) :
    (A.map (MulAut.conj h).toMonoidHom).map ψ = (A.map ψ).map (MulAut.conj (ψ h)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

omit [Finite H] in
theorem ker_inf_eq_bot_of_isPGroup (p : ℕ) (hinv : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1)
    {X : Subgroup H} (hX : IsPGroup p X) : ψ.ker ⊓ X = ⊥ := by
  have key : ∀ (e : ℕ) (z : H), z ∈ ψ.ker → z ^ (p ^ e) = 1 → z = 1 := by
    intro e
    induction e with
    | zero => intro z _ hz; simpa using hz
    | succ e ih =>
      intro z hz hze
      have h2 : (z ^ p) ^ (p ^ e) = 1 := by rw [← pow_mul, ← pow_succ']; exact hze
      exact hinv z hz (ih (z ^ p) (pow_mem hz p) h2)
  refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => ?_
  obtain ⟨e, he⟩ := hX ⟨z, hz.2⟩
  exact key e z hz.1 (by simpa using congrArg Subtype.val he)

omit [Finite H] in
theorem ker_inf_eq_bot (hinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1) {X : Subgroup H}
    (hX : IsPGroup 2 X) : ψ.ker ⊓ X = ⊥ :=
  ker_inf_eq_bot_of_isPGroup ψ 2 hinv hX

omit [Finite H] in
theorem card_map_eq_of_isPGroup (p : ℕ) (hinv : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1)
    {X : Subgroup H} (hX : IsPGroup p X) : Nat.card (X.map ψ) = Nat.card X := by
  have hinj : Function.Injective (ψ.comp X.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : H) ∈ ψ.ker ⊓ X := ⟨hx, x.2⟩
    rw [ker_inf_eq_bot_of_isPGroup ψ p hinv hX, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (Subtype.ext hx')
  have hr : (ψ.comp X.subtype).range = X.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

omit [Finite H] in
theorem card_map_eq (hinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1) {X : Subgroup H}
    (hX : IsPGroup 2 X) : Nat.card (X.map ψ) = Nat.card X :=
  card_map_eq_of_isPGroup ψ 2 hinv hX

@[expose] noncomputable def liftTwo (X : Subgroup G) : Subgroup H :=
  pCoreOf 2 (X.comap ψ)

theorem isPGroup_liftTwo (X : Subgroup G) : IsPGroup 2 (liftTwo ψ X) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  pCoreOf_isPGroup 2 _

theorem le_pCoreOf_comap (p : ℕ) [Fact p.Prime] [Finite G] (hker : ψ.ker ≤ Subgroup.center H)
    {X : Subgroup G} (hX : IsPGroup p X) {Y : Subgroup H} (hYX : Y ≤ X.comap ψ)
    (hY : IsPGroup p Y) : Y ≤ pCoreOf p (X.comap ψ) := by
  let f : X.comap ψ →* X := (ψ.comp (X.comap ψ).subtype).codRestrict X fun x => x.2
  have hf : f.ker ≤ Subgroup.center (X.comap ψ) := by
    intro x hx
    have hx' : (x : H) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    refine Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_
    exact Subgroup.mem_center_iff.mp (hker hx') y
  have : Group.IsNilpotent X := hX.isNilpotent
  have : Group.IsNilpotent (X.comap ψ) := Subgroup.isNilpotent_of_ker_le_center f hf
  have hY' : IsPGroup p (Y.subgroupOf (X.comap ψ)) := hY.comap_subtype
  obtain ⟨S, hS⟩ := hY'.exists_le_sylow
  have hSn : (S : Subgroup (X.comap ψ)).Normal :=
    Sylow.normal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent S
  have hSle : (S : Subgroup (X.comap ψ)) ≤ pCore p (X.comap ψ) := le_pCore p hSn S.isPGroup'
  intro y hy
  exact ⟨⟨y, hYX hy⟩, hSle (hS (Subgroup.mem_subgroupOf.mpr hy)), rfl⟩

theorem le_liftTwo [Finite G] (hker : ψ.ker ≤ Subgroup.center H) {X : Subgroup G}
    (hX : IsPGroup 2 X) {Y : Subgroup H} (hYX : Y ≤ X.comap ψ) (hY : IsPGroup 2 Y) :
    Y ≤ liftTwo ψ X :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  le_pCoreOf_comap ψ 2 hker hX hYX hY

theorem map_pCoreOf_comap (p : ℕ) [Fact p.Prime] [Finite G] (hker : ψ.ker ≤ Subgroup.center H)
    {X : Subgroup G} (hX : IsPGroup p X) (hXr : X ≤ ψ.range) :
    (pCoreOf p (X.comap ψ)).map ψ = X := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr (pCoreOf_le p _)) ?_
  let f : X.comap ψ →* X := (ψ.comp (X.comap ψ).subtype).codRestrict X fun x => x.2
  have hfs : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨h, rfl⟩ := hXr hx
    exact ⟨⟨h, hx⟩, rfl⟩
  obtain ⟨P⟩ : Nonempty (Sylow p (X.comap ψ)) := inferInstance
  have hPtop : (⊤ : Subgroup X) = (P.mapSurjective hfs : Subgroup X) :=
    (P.mapSurjective hfs).is_maximal' (hX.of_equiv Subgroup.topEquiv.symm) le_top
  have hPle : (P : Subgroup (X.comap ψ)).map (X.comap ψ).subtype ≤ pCoreOf p (X.comap ψ) :=
    le_pCoreOf_comap ψ p hker hX (Subgroup.map_subtype_le _) (P.isPGroup'.map _)
  intro x hx
  have hmem : (⟨x, hx⟩ : X) ∈ (P.mapSurjective hfs : Subgroup X) := hPtop ▸ Subgroup.mem_top _
  rw [Sylow.coe_mapSurjective] at hmem
  obtain ⟨p', hp', hpx⟩ := hmem
  exact ⟨p', hPle ⟨p', hp', rfl⟩, congrArg Subtype.val hpx⟩

theorem map_liftTwo [Finite G] (hker : ψ.ker ≤ Subgroup.center H) {X : Subgroup G}
    (hX : IsPGroup 2 X) (hXr : X ≤ ψ.range) : (liftTwo ψ X).map ψ = X :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  map_pCoreOf_comap ψ 2 hker hX hXr

theorem pCoreOf_comap_map (p : ℕ) [Fact p.Prime] [Finite G] (hker : ψ.ker ≤ Subgroup.center H)
    (hinv : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1) {Y : Subgroup H} (hY : IsPGroup p Y) :
    pCoreOf p ((Y.map ψ).comap ψ) = Y := by
  have hle : Y ≤ pCoreOf p ((Y.map ψ).comap ψ) :=
    le_pCoreOf_comap ψ p hker (hY.map ψ) (Subgroup.le_comap_map ψ Y) hY
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [← card_map_eq_of_isPGroup ψ p hinv (pCoreOf_isPGroup p _),
    map_pCoreOf_comap ψ p hker (hY.map ψ) (Subgroup.map_le_range ψ Y),
    card_map_eq_of_isPGroup ψ p hinv hY]

theorem liftTwo_map [Finite G] (hker : ψ.ker ≤ Subgroup.center H)
    (hinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1) {Y : Subgroup H} (hY : IsPGroup 2 Y) :
    liftTwo ψ (Y.map ψ) = Y :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  pCoreOf_comap_map ψ 2 hker hinv hY

omit [Finite H] in
theorem mem_normalizer_comap {X : Subgroup G} {h : H}
    (hh : ψ h ∈ Subgroup.normalizer (X : Set G)) :
    h ∈ Subgroup.normalizer ((X.comap ψ : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_comap, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp hh (ψ x)

theorem normalizer_pCoreOf_comap (p : ℕ) [Fact p.Prime] [Finite G]
    (hker : ψ.ker ≤ Subgroup.center H) {X : Subgroup G} (hX : IsPGroup p X) (hXr : X ≤ ψ.range) :
    Subgroup.normalizer (pCoreOf p (X.comap ψ) : Set H) =
      (ψ.range ⊓ Subgroup.normalizer (X : Set G)).comap ψ := by
  ext h
  constructor
  · intro hh
    refine ⟨MonoidHom.mem_range.mpr ⟨h, rfl⟩, ?_⟩
    apply GGTwoSig.mem_normalizer_of_map_conj_eq
    rw [← map_pCoreOf_comap ψ p hker hX hXr, ← map_map_conj, GGTwoSig.map_conj_eq hh]
  · rintro ⟨-, hh⟩
    exact normalizer_le_normalizer_pCoreOf p _ (mem_normalizer_comap ψ hh)

theorem normalizer_liftTwo [Finite G] (hker : ψ.ker ≤ Subgroup.center H) {X : Subgroup G}
    (hX : IsPGroup 2 X) (hXr : X ≤ ψ.range) :
    (⊤ : Subgroup H) ⊓ Subgroup.normalizer (liftTwo ψ X : Set H) =
      (ψ.range ⊓ Subgroup.normalizer (X : Set G)).comap ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [top_inf_eq]
  exact normalizer_pCoreOf_comap ψ 2 hker hX hXr

theorem pCoreOf_normalizer_pCoreOf_comap (p : ℕ) [Fact p.Prime] [Finite G]
    (hker : ψ.ker ≤ Subgroup.center H) {X : Subgroup G}
    (hX : pCoreOf p (ψ.range ⊓ Subgroup.normalizer (X : Set G)) = X) :
    pCoreOf p (Subgroup.normalizer (pCoreOf p (X.comap ψ) : Set H)) = pCoreOf p (X.comap ψ) := by
  have hXp : IsPGroup p X := by
    rw [← hX]
    exact pCoreOf_isPGroup p _
  have hXr : X ≤ ψ.range := hX.symm.le.trans ((pCoreOf_le p _).trans inf_le_left)
  have hN := normalizer_pCoreOf_comap ψ p hker hXp hXr
  refine le_antisymm ?_ (le_pCoreOf_normalizer p _ (pCoreOf_isPGroup p _))
  have hRp : IsPGroup p (pCoreOf p (Subgroup.normalizer (pCoreOf p (X.comap ψ) : Set H))) :=
    pCoreOf_isPGroup p _
  have hRN : pCoreOf p (Subgroup.normalizer (pCoreOf p (X.comap ψ) : Set H)) ≤
      (ψ.range ⊓ Subgroup.normalizer (X : Set G)).comap ψ := hN ▸ pCoreOf_le p _
  have hmapR : (pCoreOf p (Subgroup.normalizer (pCoreOf p (X.comap ψ) : Set H))).map ψ ≤ X := by
    refine (le_pCoreOf_of_le_normalizer p (Subgroup.map_le_iff_le_comap.mpr hRN) ?_
      (hRp.map ψ)).trans (le_of_eq hX)
    rintro y ⟨⟨h, rfl⟩, hyN⟩
    have hh : h ∈ Subgroup.normalizer (pCoreOf p (X.comap ψ) : Set H) := by
      rw [hN]
      exact ⟨MonoidHom.mem_range.mpr ⟨h, rfl⟩, hyN⟩
    apply GGTwoSig.mem_normalizer_of_map_conj_eq
    rw [← map_map_conj, GGTwoSig.map_conj_eq (le_normalizer_pCoreOf p _ hh)]
  exact le_pCoreOf_comap ψ p hker hXp (Subgroup.map_le_iff_le_comap.mp hmapR) hRp

theorem radicalTwo_liftTwo [Finite G] (hker : ψ.ker ≤ Subgroup.center H) {X : Subgroup G}
    (hX : GGRadicalTwo ψ.range X) : GGRadicalTwo ⊤ (liftTwo ψ X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  show pCoreOf 2 ((⊤ : Subgroup H) ⊓ Subgroup.normalizer (liftTwo ψ X : Set H)) = liftTwo ψ X
  rw [top_inf_eq]
  exact pCoreOf_normalizer_pCoreOf_comap ψ 2 hker hX

theorem pCoreOf_range_inf_normalizer_of_comap (p : ℕ) [Fact p.Prime] [Finite G]
    (hker : ψ.ker ≤ Subgroup.center H) {X : Subgroup G} (hXp : IsPGroup p X)
    (hXr : X ≤ ψ.range)
    (hL : pCoreOf p (Subgroup.normalizer (pCoreOf p (X.comap ψ) : Set H)) =
      pCoreOf p (X.comap ψ)) :
    pCoreOf p (ψ.range ⊓ Subgroup.normalizer (X : Set G)) = X := by
  have hN := normalizer_pCoreOf_comap ψ p hker hXp hXr
  refine le_antisymm ?_
    (le_pCoreOf_of_le_normalizer p (le_inf hXr Subgroup.le_normalizer) inf_le_right hXp)
  have hYp : IsPGroup p (pCoreOf p (ψ.range ⊓ Subgroup.normalizer (X : Set G))) :=
    pCoreOf_isPGroup p _
  have hYle : pCoreOf p (ψ.range ⊓ Subgroup.normalizer (X : Set G)) ≤
      ψ.range ⊓ Subgroup.normalizer (X : Set G) := pCoreOf_le p _
  have hYr := hYle.trans inf_le_left
  have hLY : pCoreOf p ((pCoreOf p (ψ.range ⊓ Subgroup.normalizer (X : Set G))).comap ψ) ≤
      pCoreOf p (Subgroup.normalizer (pCoreOf p (X.comap ψ) : Set H)) := by
    refine le_pCoreOf_of_le_normalizer p ?_ (fun h hh => ?_) (pCoreOf_isPGroup p _)
    · rw [hN]
      exact (pCoreOf_le p _).trans (Subgroup.comap_mono hYle)
    · rw [hN] at hh
      exact normalizer_le_normalizer_pCoreOf p _
        (mem_normalizer_comap ψ (le_normalizer_pCoreOf p _ hh))
  rw [hL] at hLY
  calc pCoreOf p (ψ.range ⊓ Subgroup.normalizer (X : Set G))
      = (pCoreOf p ((pCoreOf p (ψ.range ⊓ Subgroup.normalizer (X : Set G))).comap ψ)).map ψ :=
        (map_pCoreOf_comap ψ p hker hYp hYr).symm
    _ ≤ (pCoreOf p (X.comap ψ)).map ψ := Subgroup.map_mono hLY
    _ = X := map_pCoreOf_comap ψ p hker hXp hXr

theorem radicalTwo_of_liftTwo [Finite G] (hker : ψ.ker ≤ Subgroup.center H) {X : Subgroup G}
    (hX2 : IsPGroup 2 X) (hXr : X ≤ ψ.range) (hL : GGRadicalTwo ⊤ (liftTwo ψ X)) :
    GGRadicalTwo ψ.range X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL' : pCoreOf 2 ((⊤ : Subgroup H) ⊓ Subgroup.normalizer (liftTwo ψ X : Set H)) =
      liftTwo ψ X := hL
  rw [top_inf_eq] at hL'
  exact pCoreOf_range_inf_normalizer_of_comap ψ 2 hker hX2 hXr hL'

theorem exists_opposite_of_lift (p : ℕ) [Fact p.Prime] [Finite G]
    (hker : ψ.ker ≤ Subgroup.center H) (hinv : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1)
    (hH : ∀ Q : Subgroup H, Q ≠ ⊥ → pCoreOf p (Subgroup.normalizer (Q : Set H)) = Q →
      ∃ V₀ : Subgroup H, pCoreOf p (Subgroup.normalizer (V₀ : Set H)) = V₀ ∧
        Nat.card V₀ = Nat.card Q ∧ V₀ ⊓ Subgroup.normalizer (Q : Set H) = ⊥ ∧ Q ⊔ V₀ = ⊤ ∧
        ∀ V : Subgroup H, pCoreOf p (Subgroup.normalizer (V : Set H)) = V →
          Nat.card V = Nat.card Q → V ⊓ Subgroup.normalizer (Q : Set H) = ⊥ →
          ∃ u ∈ Q, V = V₀.map (MulAut.conj u).toMonoidHom)
    {Q : Subgroup G} (hQne : Q ≠ ⊥)
    (hQ : pCoreOf p (ψ.range ⊓ Subgroup.normalizer (Q : Set G)) = Q) :
    ∃ V₀ : Subgroup G, pCoreOf p (ψ.range ⊓ Subgroup.normalizer (V₀ : Set G)) = V₀ ∧
      Nat.card V₀ = Nat.card Q ∧ V₀ ⊓ (ψ.range ⊓ Subgroup.normalizer (Q : Set G)) = ⊥ ∧
      Q ⊔ V₀ = ψ.range ∧
      ∀ V : Subgroup G, pCoreOf p (ψ.range ⊓ Subgroup.normalizer (V : Set G)) = V →
        Nat.card V = Nat.card Q → V ⊓ (ψ.range ⊓ Subgroup.normalizer (Q : Set G)) = ⊥ →
        ∃ u ∈ Q, V = V₀.map (MulAut.conj u).toMonoidHom := by
  have hQp : IsPGroup p Q := by
    rw [← hQ]
    exact pCoreOf_isPGroup p _
  have hQr : Q ≤ ψ.range := hQ.symm.le.trans ((pCoreOf_le p _).trans inf_le_left)
  have hLmap : (pCoreOf p (Q.comap ψ)).map ψ = Q := map_pCoreOf_comap ψ p hker hQp hQr
  have hL := pCoreOf_normalizer_pCoreOf_comap ψ p hker hQ
  have hLne : pCoreOf p (Q.comap ψ) ≠ ⊥ := fun h => hQne (by rw [← hLmap, h, Subgroup.map_bot])
  have hN := normalizer_pCoreOf_comap ψ p hker hQp hQr
  have hcardQ : Nat.card Q = Nat.card (pCoreOf p (Q.comap ψ)) := by
    rw [← card_map_eq_of_isPGroup ψ p hinv (pCoreOf_isPGroup p _), hLmap]
  obtain ⟨W₀, hW₀rad, hW₀card, hW₀bot, hgen, hconj⟩ := hH _ hLne hL
  have hW₀p : IsPGroup p W₀ := by
    rw [← hW₀rad]
    exact pCoreOf_isPGroup p _
  refine ⟨W₀.map ψ, ?_, ?_, ?_, ?_, fun V hVrad hVcard hVbot => ?_⟩
  · refine pCoreOf_range_inf_normalizer_of_comap ψ p hker (hW₀p.map ψ)
      (Subgroup.map_le_range ψ W₀) ?_
    rw [pCoreOf_comap_map ψ p hker hinv hW₀p]
    exact hW₀rad
  · rw [card_map_eq_of_isPGroup ψ p hinv hW₀p, hW₀card, hcardQ]
  · have h1 : W₀ ⊓ (ψ.range ⊓ Subgroup.normalizer (Q : Set G)).comap ψ = ⊥ := by
      rw [← hN]
      exact hW₀bot
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨hyW, hyN⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hyW
    have hw' : w ∈ W₀ ⊓ (ψ.range ⊓ Subgroup.normalizer (Q : Set G)).comap ψ :=
      Subgroup.mem_inf.mpr ⟨hw, Subgroup.mem_comap.mpr (by rw [hwy]; exact hyN)⟩
    rw [h1, Subgroup.mem_bot] at hw'
    rw [← hwy, hw', map_one]
    exact Subgroup.one_mem _
  · rw [← hLmap, ← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map]
  · have hVp : IsPGroup p V := by
      rw [← hVrad]
      exact pCoreOf_isPGroup p _
    have hVr : V ≤ ψ.range := hVrad.symm.le.trans ((pCoreOf_le p _).trans inf_le_left)
    have hWmap : (pCoreOf p (V.comap ψ)).map ψ = V := map_pCoreOf_comap ψ p hker hVp hVr
    have hWp : IsPGroup p (pCoreOf p (V.comap ψ)) := pCoreOf_isPGroup p _
    have hWcard : Nat.card (pCoreOf p (V.comap ψ)) = Nat.card (pCoreOf p (Q.comap ψ)) := by
      rw [← card_map_eq_of_isPGroup ψ p hinv hWp, hWmap, hVcard, hcardQ]
    have hWbot : pCoreOf p (V.comap ψ) ⊓
        Subgroup.normalizer (pCoreOf p (Q.comap ψ) : Set H) = ⊥ := by
      have hZp : IsPGroup p ((pCoreOf p (V.comap ψ) ⊓
          Subgroup.normalizer (pCoreOf p (Q.comap ψ) : Set H) : Subgroup H)) :=
        hWp.to_le inf_le_left
      have hZmap : (pCoreOf p (V.comap ψ) ⊓
          Subgroup.normalizer (pCoreOf p (Q.comap ψ) : Set H)).map ψ ≤
          V ⊓ (ψ.range ⊓ Subgroup.normalizer (Q : Set G)) := by
        refine le_inf ((Subgroup.map_mono inf_le_left).trans hWmap.le) ?_
        rw [Subgroup.map_le_iff_le_comap, ← hN]
        exact inf_le_right
      rw [hVbot, le_bot_iff, Subgroup.map_eq_bot_iff] at hZmap
      have := ker_inf_eq_bot_of_isPGroup ψ p hinv hZp
      rwa [inf_eq_right.mpr hZmap] at this
    obtain ⟨u, hu, huW⟩ :=
      hconj _ (pCoreOf_normalizer_pCoreOf_comap ψ p hker hVrad) hWcard hWbot
    refine ⟨ψ u, hLmap ▸ Subgroup.mem_map_of_mem ψ hu, ?_⟩
    rw [← hWmap, huW, map_map_conj]

theorem GGOppRadGood.of_lift [Finite G] (hker : ψ.ker ≤ Subgroup.center H)
    (hinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1)
    (hH : ∀ Q : Subgroup H, Q ≠ ⊥ → GGRadicalTwo ⊤ Q → GGOppRadGood ⊤ Q)
    {Q : Subgroup G} (hQne : Q ≠ ⊥) (hQ : GGRadicalTwo ψ.range Q) :
    GGOppRadGood ψ.range Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ggOppRadGood_iff.mpr (exists_opposite_of_lift ψ 2 hker hinv (fun Q' hQ'ne hQ' => ?_)
    hQne hQ)
  have hQ'' : GGRadicalTwo ⊤ Q' := by
    show pCoreOf 2 ((⊤ : Subgroup H) ⊓ Subgroup.normalizer (Q' : Set H)) = Q'
    rw [top_inf_eq]
    exact hQ'
  have h := ggOppRadGood_iff.mp (hH Q' hQ'ne hQ'')
  simpa only [top_inf_eq] using h

end Transfer

end GGOppRad

end CFSG.StandardType
