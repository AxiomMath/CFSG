module

public import CFSG.RankThree.PartOne.S12.Sec15Lemmas
public import CFSG.RankThree.PartOne.S12.Sec154Fin
public import CFSG.RankThree.PartOne.S12.Sec154Linear
public import CFSG.RankThree.PartOne.S12.Sec1322

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def KF154Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∃ W₀ : Subgroup (MulAut E), Weyl154 p E W₀

namespace Sec154

open Equiv Sec1322Fin Sec154Fin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

@[expose] def embed {p : ℕ} {E : Subgroup G} {H : Type} [Group H]
    (eX : reflectionGroup p E ≃* H) : H →* MulAut E :=
  (reflectionGroup p E).subtype.comp eX.symm.toMonoidHom

@[expose] def dSet {p : ℕ} {E : Subgroup G} {H : Type} [Group H]
    (eX : reflectionGroup p E ≃* H) : Set H :=
  {g | embed eX g ∈ reflectionSet p E}

section transport

variable {p : ℕ} {E : Subgroup G} {H : Type} [Group H] (eX : reflectionGroup p E ≃* H)

omit [Finite G] in
theorem embed_apply (g : H) :
    embed eX g = ((eX.symm g : ↥(reflectionGroup p E)) : MulAut E) := rfl

omit [Finite G] in
theorem embed_injective : Function.Injective (embed eX) :=
  Subtype.val_injective.comp eX.symm.injective

omit [Finite G] in
theorem embed_mem (g : H) : embed eX g ∈ reflectionGroup p E := (eX.symm g).2

omit [Finite G] in
theorem embed_surj {y : MulAut E} (hy : y ∈ reflectionGroup p E) : ∃ g, embed eX g = y :=
  ⟨eX ⟨y, hy⟩, by simp [embed_apply]⟩

theorem dSet_conj (hp : p.Prime) :
    ∀ g x : H, x ∈ dSet eX → g * x * g⁻¹ ∈ dSet eX := by
  intro g x hx
  show embed eX (g * x * g⁻¹) ∈ reflectionSet p E
  rw [map_mul, map_mul, map_inv]
  obtain ⟨w, hw, hlift⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E (embed_mem eX g))
  rw [← hlift]
  exact conj_mem_reflectionSet hp hx hw

omit [Finite G] in
theorem dSet_invol :
    ∀ x ∈ dSet eX, x * x = 1 ∧ x ≠ 1 := by
  intro x hx
  obtain ⟨hord, -⟩ := hx.1
  have hsq : embed eX x * embed eX x = 1 := by
    have h5 := pow_orderOf_eq_one (embed eX x)
    rw [hord, pow_two] at h5
    exact h5
  refine ⟨embed_injective eX (by rw [map_mul, hsq, map_one]), ?_⟩
  rintro rfl
  rw [map_one, orderOf_one] at hord
  omega

omit [Finite G] in
theorem dSet_gen : Subgroup.closure (dSet eX) = ⊤ := by
  have h1 : Subgroup.closure (((↑) : ↥(reflectionGroup p E) → MulAut E) ⁻¹'
      reflectionSet p E) = ⊤ := Subgroup.closure_closure_coe_preimage
  have h2 : dSet eX = eX '' (((↑) : ↥(reflectionGroup p E) → MulAut E) ⁻¹' reflectionSet p E) := by
    ext g
    constructor
    · intro hg
      exact ⟨eX.symm g, hg, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      show embed eX (eX x) ∈ reflectionSet p E
      simpa [embed_apply] using hx
  have h3 := MonoidHom.map_closure eX.toMonoidHom
    (((↑) : ↥(reflectionGroup p E) → MulAut E) ⁻¹' reflectionSet p E)
  rw [h1, Subgroup.map_top_of_surjective _ eX.surjective] at h3
  rw [h2]
  exact h3.symm

end transport

@[expose] def conjX {p : ℕ} (hp : p.Prime) {E : Subgroup G} {g : MulAut E} (hg : g ∈ torusWeyl E) :
    ↥(reflectionGroup p E) ≃* ↥(reflectionGroup p E) where
  toFun x := ⟨g * x * g⁻¹, Sec1322.conj_mem_reflectionGroup hp hg x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by
    have := Sec1322.conj_mem_reflectionGroup hp ((torusWeyl E).inv_mem hg) x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjX_coe {p : ℕ} (hp : p.Prime) {E : Subgroup G} {g : MulAut E} (hg : g ∈ torusWeyl E)
    (x : ↥(reflectionGroup p E)) : ((conjX hp hg x : ↥(reflectionGroup p E)) : MulAut E) =
      g * x * g⁻¹ := rfl

theorem pCore_conjX {p : ℕ} (hp : p.Prime) {E : Subgroup G} {g : MulAut E}
    (hg : g ∈ torusWeyl E) {x : ↥(reflectionGroup p E)} (hx : x ∈ CFSG.pCore 2 ↥(reflectionGroup p E)) :
    conjX hp hg x ∈ CFSG.pCore 2 ↥(reflectionGroup p E) := by
  have := CFSG.pCore_map_iso (p := 2) (conjX hp hg)
  rw [← this]
  exact Subgroup.mem_map_of_mem _ hx

theorem node154_core {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) {H : Type} [Group H]
    (eX : reflectionGroup p E ≃* H) {K : Subgroup H} (hK : CFSG.pCore 2 H = K)
    (ψ : Perm (Fin 4) →* H) (hψ : Function.Injective ψ)
    (hψD : ∀ x : H, (x ∈ dSet eX ∧ x ∉ K) ↔ ∃ τ : Perm (Fin 4), τ.IsSwap ∧ ψ τ = x) :
    ∃ W₀ : Subgroup (MulAut E), Weyl154 p E W₀ := by
  classical
  have hp := h.prime
  set T : Set (MulAut E) := {t : MulAut E | t ∈ reflectionSet p E ∧
      t ∉ (CFSG.pCore 2 ↥(reflectionGroup p E)).map (reflectionGroup p E).subtype} with hTdef
  set φ : Perm (Fin 4) →* MulAut E := (embed eX).comp ψ with hφdef
  have hφinj : Function.Injective φ := (embed_injective eX).comp hψ
  have hmapK : (CFSG.pCore 2 ↥(reflectionGroup p E)).map eX.toMonoidHom = K := by
    rw [CFSG.pCore_map_iso, hK]
  have hmem : ∀ y : ↥(reflectionGroup p E), y ∈ CFSG.pCore 2 ↥(reflectionGroup p E) ↔ eX y ∈ K := by
    intro y
    rw [← hmapK, Subgroup.mem_map_equiv]
    simp
  have hTφ : ∀ t, t ∈ T ↔ ∃ τ : Perm (Fin 4), τ.IsSwap ∧ φ τ = t := by
    intro t
    constructor
    · rintro ⟨htD, htn⟩
      have htX : t ∈ reflectionGroup p E := Subgroup.subset_closure htD
      have hemb : embed eX (eX ⟨t, htX⟩) = t := by simp [embed_apply]
      have hxD : eX ⟨t, htX⟩ ∈ dSet eX := by
        show embed eX (eX ⟨t, htX⟩) ∈ reflectionSet p E
        rw [hemb]
        exact htD
      have hxK : eX ⟨t, htX⟩ ∉ K := by
        intro hxK
        apply htn
        exact ⟨⟨t, htX⟩, (hmem _).2 hxK, rfl⟩
      obtain ⟨τ, hτ, hτx⟩ := (hψD _).1 ⟨hxD, hxK⟩
      refine ⟨τ, hτ, ?_⟩
      show embed eX (ψ τ) = t
      rw [hτx, hemb]
    · rintro ⟨τ, hτ, rfl⟩
      obtain ⟨hxD, hxK⟩ := (hψD (ψ τ)).2 ⟨τ, hτ, rfl⟩
      refine ⟨hxD, ?_⟩
      rintro ⟨y, hy, hyt⟩
      apply hxK
      have h1 : y = eX.symm (ψ τ) := Subtype.ext hyt
      have h2 : eX y = ψ τ := by rw [h1]; simp
      rw [← h2]
      exact (hmem y).1 hy
  have hTW : T ⊆ torusWeyl E := fun t ht => Sec1322.reflectionSet_subset_torusWeyl t ht.1
  have hTconj : ∀ g ∈ torusWeyl E, ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro g hg t ht
    obtain ⟨htD, htn⟩ := ht
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hw, rfl⟩ := Sec1322.exists_lift hg
      exact conj_mem_reflectionSet hp htD hw
    · rintro ⟨y, hy, hyeq⟩
      apply htn
      have htX : t ∈ reflectionGroup p E := Subgroup.subset_closure htD
      refine ⟨⟨t, htX⟩, ?_, rfl⟩
      have h1 := pCore_conjX hp ((torusWeyl E).inv_mem hg) hy
      have h2 : conjX hp ((torusWeyl E).inv_mem hg) y = ⟨t, htX⟩ := by
        apply Subtype.ext
        rw [conjX_coe]
        have : (y : MulAut E) = g * t * g⁻¹ := hyeq
        rw [this]
        group
      rwa [h2] at h1
  have hT : ∀ t ∈ T, Nat.card (autMoved E t) = p := fun t ht => ht.1.1.2
  have hirr : ∀ B : Subgroup E, (∀ w ∈ torusWeyl E, ∀ b ∈ B, w b ∈ B) → B = ⊥ ∨ B = ⊤ := by
    intro B hB
    have hinv : torusInvariant E ⊤ (B.map E.subtype) := by
      intro w hw b hb
      have hwN : w ∈ Subgroup.normalizer (E : Set G) := (Subgroup.mem_inf.1 hw).2
      obtain ⟨b', hb', rfl⟩ := hb
      have hg : conjAut E w hwN ∈ torusWeyl E := ⟨⟨w, hwN⟩, rfl⟩
      exact ⟨conjAut E w hwN b', hB _ hg b' hb', Equivariance.coe_conjAut hwN b'⟩
    rcases hF13.irreducible _ (Subgroup.map_subtype_le B) hinv with h0 | h1
    · left
      rw [eq_bot_iff]
      intro b hb
      have : (b : G) ∈ B.map E.subtype := ⟨b, hb, rfl⟩
      rw [h0] at this
      exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 this))
    · right
      rw [eq_top_iff]
      intro e _
      have : (e : G) ∈ B.map E.subtype := by
        rw [h1]
        exact e.2
      obtain ⟨b, hb, hbe⟩ := this
      rwa [← Subtype.ext hbe]
  have hE : ∀ a b : ↥E, a * b = b * a := fun a b => h.E_elem.is_comm.comm a b
  obtain ⟨hsplit, hinf, hscal⟩ := weyl_split hp hE (n := 4) (by norm_num) φ hφinj hTφ hTW hTconj
    hT hirr sym4_conj_surjective sym4_center
  have hrange : φ.range = Subgroup.closure T := range_eq_closure φ hTφ
  refine ⟨φ.range, hrange, ?_, Or.inl ⟨(MonoidHom.ofInjective hφinj).symm⟩, hsplit, hinf, hscal⟩
  rintro _ ⟨τ, rfl⟩
  exact embed_mem eX (ψ τ)

theorem classes_gp {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A)
    (eX : reflectionGroup p E ≃* Gp) :
    (∀ x, x ∈ dSet eX ↔ isT x ∨ isV' x) ∨ (∀ x, x ∈ dSet eX ↔ isT' x ∨ isV' x) := by
  classical
  have hp := h.prime
  have hcardE : Nat.card E = p ^ 3 := by
    rw [hEA]
    exact h.A_card
  have hφinj := embed_injective eX
  have hφX := embed_mem eX
  have hφsurj : ∀ y ∈ reflectionGroup p E, ∃ g, embed eX g = y := fun y hy => embed_surj eX hy
  set zM : MulAut E := embed eX z0 with hzM
  have hzX : zM ∈ reflectionGroup p E := hφX z0
  have hz2 : zM * zM = 1 := by rw [hzM, ← map_mul, (Sec1322.z0_props).1, map_one]
  have hz1 : zM ≠ 1 := fun h1 => (Sec1322.z0_props).2.1 (hφinj (h1.trans (map_one _).symm))
  have hcen : ∀ y ∈ reflectionGroup p E, y * zM = zM * y := by
    intro y hy
    obtain ⟨g, rfl⟩ := hφsurj y hy
    rw [hzM, ← map_mul, ← map_mul, (Sec1322.z0_props).2.2 g]
  have huniq : ∀ y ∈ reflectionGroup p E, y * y = 1 → y ≠ 1 →
      (∀ x ∈ reflectionGroup p E, x * y = y * x) → y = zM := by
    intro y hy hy2 hy1 hyc
    obtain ⟨g, rfl⟩ := hφsurj y hy
    have hg : g = z0 :=
      Sec1322.central_unique g (hφinj (by rw [map_mul, hy2, map_one]))
        (fun hg => hy1 (by rw [hg, map_one]))
        (fun γ => hφinj (by rw [map_mul, map_mul]; exact hyc (embed eX γ) (hφX γ)))
    rw [hg]
  have hzinv : ∀ e : E, zM e = e⁻¹ := Sec1322.inverts_of_central h hF13 hzX hz2 hz1 hcen huniq
  let Rset : Set Gp := {g | IsAutReflection p E (embed eX g)}
  have hinvφ : ∀ g : Gp, embed eX g⁻¹ = (embed eX g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])
  have hRc : ∀ g x, x ∈ Rset → g * x * g⁻¹ ∈ Rset := by
    intro g x hx
    show IsAutReflection p E (embed eX (g * x * g⁻¹))
    rw [map_mul, map_mul, hinvφ g]
    exact isAutReflection_conj (embed eX g) (embed eX x) hx
  have hDR : dSet eX ⊆ Rset := fun x hx => hx.1
  have hRi : ∀ x ∈ Rset, x * x = 1 ∧ x ≠ 1 ∧ x ≠ z0 := by
    intro x hx
    have hord : orderOf (embed eX x) = 2 := hx.1
    have hsq : embed eX x * embed eX x = 1 := by
      have h5 := pow_orderOf_eq_one (embed eX x)
      rw [hord, pow_two] at h5
      exact h5
    refine ⟨hφinj (by rw [map_mul, hsq, map_one]), ?_, ?_⟩
    · rintro rfl
      rw [map_one, orderOf_one] at hord
      omega
    · rintro rfl
      exact Sec1322.not_isAutReflection_of_inverts h hcardE hzinv hx
  have hdich : ∀ x : Gp, x * x = 1 → x ≠ 1 → x ≠ z0 → (x ∈ Rset ↔ z0 * x ∉ Rset) := by
    intro x hx2 hx1 hxz
    have := Sec1322.reflection_dichotomy h hcardE hzinv (x := embed eX x)
      (by rw [← map_mul, hx2, map_one]) (fun h1 => hx1 (hφinj (h1.trans (map_one _).symm)))
      (fun h1 => hxz (hφinj h1))
    show IsAutReflection p E (embed eX x) ↔ ¬ IsAutReflection p E (embed eX (z0 * x))
    rw [map_mul]
    exact this
  obtain ⟨-, hcl, -⟩ := chain_of_reflection_set hRc (dSet_conj eX hp) hDR hRi hdich (dSet_gen eX)
  exact hcl

theorem node154_of_nodes (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h125 : Node125)
    (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129) (hFive : KF154Five) :
    Node154 := by
  intro G _ _ p A c L E h hF12 hout
  by_cases hT : Outcome152Five p E A (lieGenerated p E)
  · exact hFive G p A c L E h hF12 hT
  · have hF13 := Sec13Facts.of_nodes hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h125 h126
      h127 h128 h129 h.h12 hT
    have hp := h.h12.prime
    rcases hout with ⟨f, -, -, -, ⟨eX⟩, hEA, -⟩ | ⟨f, -, -, -, ⟨eX⟩, hEA, -⟩ |
        ⟨f, -, -, -, ⟨eX⟩, hEA, -⟩ | ⟨f, -, -, -, ⟨eX⟩, hEA, -⟩ | h5
    · obtain ⟨ψ, hψ, hψD⟩ := swapClass_s4 (dSet_conj eX hp) (dSet_invol eX) (dSet_gen eX)
      exact node154_core h.h12 hF13 eX pCore_s4 ψ hψ hψD
    · obtain ⟨ψ, hψ, hψD⟩ := swapClass_gp (classes_gp h.h12 hF13 hEA eX)
      exact node154_core h.h12 hF13 eX pCore_gp ψ hψ hψD
    · obtain ⟨ψ, hψ, hψD⟩ := swapClass_gp (classes_gp h.h12 hF13 hEA eX)
      exact node154_core h.h12 hF13 eX pCore_gp ψ hψ hψD
    · obtain ⟨ψ, hψ, hψD⟩ := swapClass_gp (classes_gp h.h12 hF13 hEA eX)
      exact node154_core h.h12 hF13 eX pCore_gp ψ hψ hψD
    · exact absurd h5 hT

end Sec154

end CFSG.RankThree.PartOne
