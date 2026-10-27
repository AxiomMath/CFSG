module

public import CFSG.Quasithin.Vol2.KGFact1297Rank
public import CFSG.Quasithin.Vol2.KGFact1296Id
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma6One

public section

namespace CFSG.Quasithin.H13.KG1297

open CFSG.Open CFSG.Quasithin.H13.KG1296

variable {G : Type} [Group G]

theorem exists_actBar_eq [Finite G] {X K S B : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hBK : B ≤ K)
    (hSB : S ≤ Subgroup.normalizer (B : Set G))
    (hinn : ∀ s ∈ S, ∃ b ∈ B, ∀ x ∈ B, (b⁻¹ * s) * x * (b⁻¹ * s)⁻¹ * x⁻¹ ∈ pCoreOf 2 B)
    (hInn : InnClosed (barOf K B)) (s : ↥X) (hsS : (s : G) ∈ S) :
    ∃ b : ↥X, (b : G) ∈ B ∧
      (actBar K).comp (Subgroup.inclusion hXN) s = (actBar K).comp (Subgroup.inclusion hXN) b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : ↥X →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) := (actBar K).comp (Subgroup.inclusion hXN)
    with hφ
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set Bb := barOf K B with hBb
  obtain ⟨b, hb, hc⟩ := hinn s hsS
  have hbK : b ∈ K := hBK hb
  have hbX : b ∈ X := hKX hbK
  set c : ↥X := (⟨b, hbX⟩ : ↥X)⁻¹ * s with hcdef
  have hc' : (c : G) = b⁻¹ * s := rfl
  have hcN : (c : G) ∈ Subgroup.normalizer (B : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hb)) (hSB hsS)
  set α := φ c with hα
  have hαmk : ∀ y (hy : y ∈ K), α (π ⟨y, hy⟩) =
      π ⟨(c : G) * y * (c : G)⁻¹, (hXN c.2 y).1 hy⟩ := fun y hy => rfl
  have h1 : ∀ x ∈ Bb, α x ∈ Bb := by
    rintro _ ⟨⟨y, hyK⟩, hyB, rfl⟩
    rw [hαmk]
    exact ⟨_, (Subgroup.mem_normalizer_iff.1 hcN y).1 hyB, rfl⟩
  have hO2 : ∀ z (hz : z ∈ pCoreOf 2 B),
      π ⟨z, hBK (CFSG.LieType.BorelTits.pCoreOf_le 2 B hz)⟩ ∈ pCoreOf 2 Bb := by
    intro z hz
    set W := ((pCoreOf 2 B).subgroupOf K).map π with hW
    have hWB : W ≤ Bb := Subgroup.map_mono (Subgroup.subgroupOf_mono K
      (CFSG.LieType.BorelTits.pCoreOf_le 2 B))
    have hWn : Bb ≤ Subgroup.normalizer (W : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
      refine le_normalizer_of_forall ?_
      rintro _ ⟨⟨y, hyK⟩, hyB, rfl⟩ _ ⟨⟨w, hwK⟩, hwB, rfl⟩
      refine ⟨⟨y * w * y⁻¹, K.mul_mem (K.mul_mem hyK hwK) (K.inv_mem hyK)⟩, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B
          hyB) w).1 hwB
      · show π ⟨y * w * y⁻¹, _⟩ = π ⟨y, hyK⟩ * π ⟨w, hwK⟩ * (π ⟨y, hyK⟩)⁻¹
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
    have hW2 : IsPGroup 2 W := by
      have h2 : IsPGroup 2 ((pCoreOf 2 B).subgroupOf K) :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B).comap_subtype
      exact h2.map π
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWB hWn hW2 ⟨⟨z, _⟩, hz, rfl⟩
  have h2 : ∀ x ∈ Bb, α x * x⁻¹ ∈ pCoreOf 2 Bb := by
    rintro _ ⟨⟨y, hyK⟩, hyB, rfl⟩
    rw [hαmk, ← map_inv, ← map_mul]
    have := hO2 _ (hc y hyB)
    convert this using 2
  obtain ⟨β, hβ, hαβ⟩ := hInn α h1 h2
  obtain ⟨⟨b', hb'K⟩, hb'B, rfl⟩ := hβ
  refine ⟨⟨b, hbX⟩ * ⟨b', hKX hb'K⟩, B.mul_mem hb (Subgroup.mem_subgroupOf.1 hb'B), ?_⟩
  have hs : s = ⟨b, hbX⟩ * c := by rw [hcdef, mul_inv_cancel_left]
  calc φ s = φ (⟨b, hbX⟩ * c) := by rw [← hs]
    _ = φ ⟨b, hbX⟩ * α := map_mul _ _ _
    _ = φ ⟨b, hbX⟩ * φ ⟨b', hKX hb'K⟩ := by
      rw [hαβ]
      exact congrArg _ (actBar_of_mem (⟨b', hXN (hKX hb'K)⟩ : ↥(Subgroup.normalizer (K : Set G)))
        hb'K).symm
    _ = φ (⟨b, hbX⟩ * ⟨b', hKX hb'K⟩) := (map_mul _ _ _).symm

theorem exists_psi [Finite G] {X K S B : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKS : K ⊔ S = X) (hBK : B ≤ K)
    (hSB : S ≤ Subgroup.normalizer (B : Set G))
    (hinn : ∀ s ∈ S, ∃ b ∈ B, ∀ x ∈ B, (b⁻¹ * s) * x * (b⁻¹ * s)⁻¹ * x⁻¹ ∈ pCoreOf 2 B)
    (hInn : InnClosed (barOf K B)) (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    ∃ ψ : ↥X →* (↥K ⧸ CFSG.pCore 2 ↥K),
      (∀ k (hk : k ∈ K), ψ ⟨k, hKX hk⟩ = QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hk⟩) ∧
      (∀ x : ↥X, ψ x = 1 ↔ (x : G) ∈ centralizerMod (pCoreOf 2 K) X K) ∧
      (∀ s : ↥X, (s : G) ∈ S → ∃ b : ↥X, (b : G) ∈ B ∧ ψ s = ψ b) := by
  set φ : ↥X →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) := (actBar K).comp (Subgroup.inclusion hXN)
    with hφ
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hconj : Function.Injective
      (MulAut.conj : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have hw := congrArg (fun f : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) => f w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at hw
      calc w * z = (z * w * z⁻¹) * z := by rw [hw]
        _ = z * w := by group
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hzc
  have hφK : ∀ k (hk : k ∈ K), φ ⟨k, hKX hk⟩ = MulAut.conj (π ⟨k, hk⟩) := fun k hk =>
    actBar_of_mem _ hk
  have hSX : S ≤ X := hKS ▸ le_sup_right
  have hrange : φ.range ≤
      (MulAut.conj : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K)).range := by
    have htop : K.subgroupOf X ⊔ S.subgroupOf X = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKX hSX, hKS, Subgroup.subgroupOf_self]
    rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, sup_le_iff]
    constructor
    · rintro _ ⟨⟨k, hkX⟩, hk, rfl⟩
      exact ⟨π ⟨k, hk⟩, (hφK k hk).symm⟩
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨b, hbB, hsb⟩ := exists_actBar_eq hKX hXN hBK hSB hinn hInn s hs
      refine ⟨π ⟨b, hBK hbB⟩, ?_⟩
      rw [hsb]
      exact (hφK b (hBK hbB)).symm
  set e := MonoidHom.ofInjective hconj with he
  set ψ : ↥X →* (↥K ⧸ CFSG.pCore 2 ↥K) :=
    e.symm.toMonoidHom.comp (φ.codRestrict _ fun x => hrange ⟨x, rfl⟩) with hψ
  have hconjψ : ∀ x, MulAut.conj (ψ x) = φ x := by
    intro x
    have h : ((e (ψ x) : ↥(MonoidHom.range _)) : MulAut (↥K ⧸ CFSG.pCore 2 ↥K)) =
        MulAut.conj (ψ x) := MonoidHom.ofInjective_apply hconj
    rw [← h]
    show ((e (e.symm ⟨φ x, _⟩) : ↥(MonoidHom.range _)) : MulAut _) = φ x
    rw [MulEquiv.apply_symm_apply]
  refine ⟨ψ, fun k hk => hconj ?_, fun x => ?_, fun s hs => ?_⟩
  · rw [hconjψ, hφK]
  · rw [← hconj.eq_iff, map_one, hconjψ, hφ, MonoidHom.comp_apply]
    exact (mem_centralizerMod_iff hXN x.2).symm
  · obtain ⟨b, hbB, hsb⟩ := exists_actBar_eq hKX hXN hBK hSB hinn hInn s hs
    exact ⟨b, hbB, hconj (by rw [hconjψ, hconjψ, hsb])⟩

section Transfer

variable {X : Subgroup G} {M : Type} [Group M] (ρ : ↥X →* M)

theorem modO2_img [Finite G] (hker : IsPGroup 2 ρ.ker) {H : Subgroup G} (hHX : H ≤ X) :
    Nonempty (ModO2 H ≃* ModO2 ((H.subgroupOf X).map ρ)) := by
  set f : ↥H →* ↥((H.subgroupOf X).map ρ) := (ρ.subgroupMap (H.subgroupOf X)).comp
    (Subgroup.subgroupOfEquivOfLe hHX).symm.toMonoidHom with hf
  refine nonempty_modO2_equiv f ((MonoidHom.subgroupMap_surjective _ _).comp
    (Subgroup.subgroupOfEquivOfLe hHX).symm.surjective) ?_
  intro x
  have hx : ρ ((Subgroup.subgroupOfEquivOfLe hHX).symm x) = 1 := congrArg Subtype.val x.2
  obtain ⟨k, hk⟩ := hker ⟨_, hx⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun z : ↥ρ.ker => ((z : ↥X) : G)) hk
  simpa using this

theorem img_sup {B Y : Subgroup G} (hBX : B ≤ X) (hYX : Y ≤ X) :
    ((B ⊔ Y).subgroupOf X).map ρ = (B.subgroupOf X).map ρ ⊔ (Y.subgroupOf X).map ρ := by
  rw [Subgroup.subgroupOf_sup hBX hYX, Subgroup.map_sup]

theorem le_sup_of_img_le {B S Y : Subgroup G} (hkerS : ∀ x : ↥X, ρ x = 1 → (x : G) ∈ S)
    (hYX : Y ≤ X) (h : (Y.subgroupOf X).map ρ ≤ (B.subgroupOf X).map ρ) : Y ≤ B ⊔ S := by
  intro y hy
  obtain ⟨b, hb, hby⟩ := h ⟨⟨y, hYX hy⟩, hy, rfl⟩
  have h1 : ρ (b⁻¹ * ⟨y, hYX hy⟩) = 1 := by rw [map_mul, map_inv, hby, inv_mul_cancel]
  have h2 := hkerS _ h1
  have e : y = (b : G) * ((b⁻¹ * ⟨y, hYX hy⟩ : ↥X) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right h2)

theorem comap_img {Y : Subgroup G} (hkerY : ∀ x : ↥X, ρ x = 1 → (x : G) ∈ Y) :
    ((Y.subgroupOf X).map ρ).comap ρ = Y.subgroupOf X := by
  rw [Subgroup.comap_map_eq, sup_eq_left]
  intro x hx
  exact hkerY x hx

theorem relIndex_img {B Y : Subgroup G} (hkerY : ∀ x : ↥X, ρ x = 1 → (x : G) ∈ Y)
    (hBX : B ≤ X) :
    (B ⊓ Y).relIndex B =
      ((B.subgroupOf X).map ρ ⊓ (Y.subgroupOf X).map ρ).relIndex ((B.subgroupOf X).map ρ) := by
  rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left, ← Subgroup.relIndex_comap,
    comap_img ρ hkerY, Subgroup.relIndex_subgroupOf hBX]

end Transfer

section Transfer2

variable {X : Subgroup G} {M : Type} [Group M] (ρ : ↥X →* M)

theorem noE9_img [Finite G] [Finite M] (hker : IsPGroup 2 ρ.ker) {Y : Subgroup G} (hYX : Y ≤ X)
    (hY : CFSG.Open.pRank 3 Y ≤ 1) : NoE9 ((Y.subgroupOf X).map ρ) := by
  have hrange : (ρ.comp (Subgroup.inclusion hYX)).range = (Y.subgroupOf X).map ρ := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion hYX y, y.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hrange]
  refine noE9_of_pRank _ (fun y => ?_) hY
  obtain ⟨k, hk⟩ := hker ⟨Subgroup.inclusion hYX y, y.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun z : ↥ρ.ker => ((z : ↥X) : G)) hk
  simpa using this

theorem le_of_img_le {H₁ H₂ : Subgroup G} (hH₁ : H₁ ≤ X)
    (hker : ∀ x : ↥X, ρ x = 1 → (x : G) ∈ H₂)
    (hle : (H₁.subgroupOf X).map ρ ≤ (H₂.subgroupOf X).map ρ) : H₁ ≤ H₂ := by
  intro h hh
  obtain ⟨x₂, hx₂, hρ⟩ := hle ⟨⟨h, hH₁ hh⟩, hh, rfl⟩
  have h1 : ρ (x₂⁻¹ * ⟨h, hH₁ hh⟩) = 1 := by rw [map_mul, map_inv, hρ, inv_mul_cancel]
  have := H₂.mul_mem hx₂ (hker _ h1)
  simpa using this

theorem isMax_of_img {B Y : Subgroup G} (hkerY : ∀ x : ↥X, ρ x = 1 → (x : G) ∈ Y)
    (hBX : B ≤ X) (hYX : Y ≤ X)
    (h : IsMaxSubgroupIn ((B.subgroupOf X).map ρ ⊔ (Y.subgroupOf X).map ρ)
      ((Y.subgroupOf X).map ρ)) : IsMaxSubgroupIn (B ⊔ Y) Y := by
  obtain ⟨hlt, hmax⟩ := h
  have himgsup := img_sup ρ hBX hYX
  refine ⟨lt_of_le_of_ne le_sup_right fun heq => hlt.ne ?_, fun K' hYK hK' => ?_⟩
  · rw [← himgsup, ← heq]
  · have hK'X : K' ≤ X := hK'.trans (sup_le hBX hYX)
    have hkerK : ∀ x : ↥X, ρ x = 1 → (x : G) ∈ K' := fun x hx => hYK.le (hkerY x hx)
    have h1 : (Y.subgroupOf X).map ρ < (K'.subgroupOf X).map ρ := by
      refine lt_of_le_of_ne (Subgroup.map_mono (Subgroup.subgroupOf_mono X hYK.le)) fun heq => ?_
      exact hYK.not_ge (le_of_img_le ρ hK'X hkerY heq.symm.le)
    have h2 : (K'.subgroupOf X).map ρ ≤ (B.subgroupOf X).map ρ ⊔ (Y.subgroupOf X).map ρ := by
      rw [← himgsup]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono X hK')
    have h3 := hmax _ h1 h2
    refine le_antisymm hK' (le_of_img_le ρ (sup_le hBX hYX) hkerK ?_)
    rw [himgsup, ← h3]

end Transfer2

section Lattice

variable {M : Type} [Group M]

@[expose] def LatOut (B Y : Subgroup M) (m : ℕ) : Prop :=
  m = 3 ∧ Nonempty (ModO2 Y ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    (Nonempty (ModO2 (B ⊔ Y) ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (ModO2 (B ⊔ Y) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) ∧
    IsMaxSubgroupIn (B ⊔ Y) Y

@[expose] def LatHyp (B : Subgroup M) (m : ℕ) : Prop :=
  ∀ (T : Sylow 2 M) (Y : Subgroup M), (T : Subgroup M) ≤ B → (T : Subgroup M) ≤ Y → ¬ Y ≤ B →
    NoE9 Y → (B ⊓ Y).relIndex B = 2 ^ m - 1 → LatOut B Y m

variable {M' : Type} [Group M']

theorem noE9_map (e : M ≃* M') {Y : Subgroup M} (h : NoE9 Y) : NoE9 (Y.map e.toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ ha3 hb3 hab ha1
  simp only [MulEquiv.coe_toMonoidHom] at ha3 hb3 hab ha1 ⊢
  have hb' := h a ha b hb (e.injective (by rw [map_pow, ha3, map_one]))
    (e.injective (by rw [map_pow, hb3, map_one])) (e.injective (by rw [map_mul, map_mul, hab]))
    (fun h1 => ha1 (by rw [h1, map_one]))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb'
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← map_zpow, hk]⟩

theorem LatOut.of_map (e : M ≃* M') {B Y : Subgroup M} {m : ℕ}
    (h : LatOut (B.map e.toMonoidHom) (Y.map e.toMonoidHom) m) : LatOut B Y m := by
  obtain ⟨hm, ⟨eY⟩, hBY, hmax⟩ := h
  have hsup : (B ⊔ Y).map e.toMonoidHom = B.map e.toMonoidHom ⊔ Y.map e.toMonoidHom :=
    Subgroup.map_sup _ _ _
  refine ⟨hm, ?_, ?_, ?_⟩
  · obtain ⟨e1⟩ := nonempty_modO2_map e Y
    exact ⟨e1.trans eY⟩
  · obtain ⟨e2⟩ := nonempty_modO2_map e (B ⊔ Y)
    rw [hsup] at e2
    rcases hBY with ⟨⟨e3⟩⟩ | ⟨⟨e3⟩⟩
    · exact Or.inl ⟨e2.trans e3⟩
    · exact Or.inr ⟨e2.trans e3⟩
  · obtain ⟨hlt, hmx⟩ := hmax
    have hinj : Function.Injective (Subgroup.map e.toMonoidHom) :=
      Subgroup.map_injective e.injective
    refine ⟨lt_of_le_of_ne le_sup_right fun heq => hlt.ne (by rw [← hsup, ← heq]), ?_⟩
    intro K hYK hK
    have h1 : Y.map e.toMonoidHom < K.map e.toMonoidHom :=
      lt_of_le_of_ne (Subgroup.map_mono hYK.le) fun heq => hYK.ne (hinj heq)
    have h2 : K.map e.toMonoidHom ≤ B.map e.toMonoidHom ⊔ Y.map e.toMonoidHom := by
      rw [← hsup]
      exact Subgroup.map_mono hK
    exact hinj ((hmx _ h1 h2).trans hsup.symm)

theorem LatHyp.of_map [Finite M] (e : M ≃* M') {B : Subgroup M} {m : ℕ}
    (h : LatHyp (B.map e.toMonoidHom) m) : LatHyp B m := by
  intro T Y hTB hTY hYB hY hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective (e.toMonoidHom : M → M') := e.surjective
  have hinj : Function.Injective (e.toMonoidHom : M → M') := e.injective
  refine LatOut.of_map e (h (T.mapSurjective hsurj) (Y.map e.toMonoidHom) ?_ ?_ ?_
    (noE9_map e hY) ?_)
  · rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hTB
  · rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hTY
  · rwa [Subgroup.map_le_map_iff_of_injective hinj]
  · rw [← Subgroup.map_inf_eq _ _ _ hinj, Subgroup.relIndex_map_map_of_injective _ _ hinj, hidx]

end Lattice

theorem reduction [Finite G] {X K S B Y : Subgroup G} {m : ℕ} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hS : QuasithinUnique.IsSylowTwoOf S X)
    (hKS : K ⊔ S = X) (hBK : B ≤ K) (hSB : S ≤ Subgroup.normalizer (B : Set G))
    (hinn : ∀ s ∈ S, ∃ b ∈ B, ∀ x ∈ B, (b⁻¹ * s) * x * (b⁻¹ * s)⁻¹ * x⁻¹ ∈ pCoreOf 2 B)
    (hSY : S ≤ Y) (hYX : Y ≤ X) (hYB : ¬ Y ≤ B ⊔ S) (hY3 : CFSG.Open.pRank 3 Y ≤ 1)
    (hidx : (B ⊓ Y).relIndex B = 2 ^ m - 1) (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hnab : ∃ a b : ↥K ⧸ CFSG.pCore 2 ↥K, a * b ≠ b * a)
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) (hInn : InnClosed (barOf K B))
    (hLat : LatHyp (barOf K B) m) : LatOut B Y m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψK, hψker, hψS⟩ := exists_psi hKX hXN hKS hBK hSB hinn hInn hZ
  set D := centralizerMod (pCoreOf 2 K) X K with hDdef
  obtain ⟨hSX, hS2, hSodd⟩ := hS
  have hD2 : IsPGroup 2 D := by
    have := L1296.isPGroup_centralizerMod hS2 (hSX.trans hXN) hs hnab
    rwa [hKS] at this
  have hDX : D ≤ X := fun x hx => hx.1
  have hDS : D ≤ S := by
    have hDn : (D.subgroupOf X).Normal := by
      have : D.subgroupOf X = ψ.ker := by
        ext x
        rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hψker]
      rw [this]
      infer_instance
    let S₀ : Sylow 2 ↥X := hS2.comap_subtype.toSylow hSodd
    have : (Subgroup.comap X.subtype D).Normal := hDn
    have h := IsPGroup.le_sylow_of_normal hD2.comap_subtype S₀
    intro d hd
    exact h (show (⟨d, hDX hd⟩ : ↥X) ∈ D.subgroupOf X from hd)
  have hkerS : ∀ x : ↥X, ψ x = 1 → (x : G) ∈ S := fun x hx => hDS ((hψker x).1 hx)
  have hkerY : ∀ x : ↥X, ψ x = 1 → (x : G) ∈ Y := fun x hx => hSY (hkerS x hx)
  have hker2 : IsPGroup 2 ψ.ker := by
    intro x
    obtain ⟨k, hk⟩ := hD2 ⟨_, (hψker x).1 x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hBX : B ≤ X := hBK.trans hKX
  have hBb : (B.subgroupOf X).map ψ = barOf K B := by
    ext z
    constructor
    · rintro ⟨⟨b, hbX⟩, hb, rfl⟩
      exact ⟨⟨b, hBK hb⟩, hb, (hψK b (hBK hb)).symm⟩
    · rintro ⟨⟨b, hbK⟩, hb, rfl⟩
      exact ⟨⟨b, hKX hbK⟩, hb, hψK b hbK⟩
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) z
    exact ⟨⟨k, hKX k.2⟩, hψK k k.2⟩
  let S₀ : Sylow 2 ↥X := hS2.comap_subtype.toSylow hSodd
  set T : Sylow 2 (↥K ⧸ CFSG.pCore 2 ↥K) := S₀.mapSurjective hψsurj with hT
  have hTcoe : (T : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) = (S.subgroupOf X).map ψ := by
    rw [hT, Sylow.coe_mapSurjective]
    rfl
  set Yb := (Y.subgroupOf X).map ψ with hYb
  have hTB : (T : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ≤ barOf K B := by
    rw [hTcoe]
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨b, hb, hsb⟩ := hψS s hs
    rw [hsb, ← hBb]
    exact ⟨b, hb, rfl⟩
  have hTY : (T : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ≤ Yb := by
    rw [hTcoe]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono X hSY)
  have hYbB : ¬ Yb ≤ barOf K B := by
    intro h
    exact hYB (le_sup_of_img_le ψ hkerS hYX (hBb ▸ h))
  have hidx' : (barOf K B ⊓ Yb).relIndex (barOf K B) = 2 ^ m - 1 := by
    rw [← hBb, ← relIndex_img ψ hkerY hBX]
    exact hidx
  obtain ⟨hm, ⟨eY⟩, hBY, hmax⟩ := hLat T Yb hTB hTY hYbB (noE9_img ψ hker2 hYX hY3) hidx'
  have hsup := img_sup ψ hBX hYX
  rw [hBb] at hsup
  refine ⟨hm, ?_, ?_, ?_⟩
  · obtain ⟨e1⟩ := modO2_img ψ hker2 hYX
    exact ⟨e1.trans eY⟩
  · obtain ⟨e2⟩ := modO2_img ψ hker2 (sup_le hBX hYX)
    rw [hsup] at e2
    rcases hBY with ⟨⟨e3⟩⟩ | ⟨⟨e3⟩⟩
    · exact Or.inl ⟨e2.trans e3⟩
    · exact Or.inr ⟨e2.trans e3⟩
  · exact isMax_of_img ψ hkerY hBX hYX (by rw [hBb]; exact hmax)

end CFSG.Quasithin.H13.KG1297
