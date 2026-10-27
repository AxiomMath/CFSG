module

public import CFSG.RankThree.GF2n.Stroth80.Sec717Layers
import CFSG.RankThree.GF2n.Stroth80.Sec717QLayersProof

public section

namespace CFSG.RankThree.GF2n.Stroth80.S717LN

variable {K E X : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Group X]
  {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V Nb Rb : Subgroup X}
  {T : Submodule K E}

@[expose] def deltaP (B : LinearMap.BilinForm K E) (φ : X →* (E ≃ₗ[K] E)) (T : Submodule K E)
    (x : X) : ↥(B.orthogonal T) →ₗ[K] E :=
  (opm (φ x)).comp (B.orthogonal T).subtype

theorem deltaP_apply (x : X) (w : ↥(B.orthogonal T)) :
    deltaP B φ T x w = opm (φ x) (w : E) := rfl

theorem deltaP_one : deltaP B φ T 1 = 0 := by
  refine LinearMap.ext fun w => ?_
  rw [deltaP_apply, map_one, LinearMap.zero_apply, opm_apply]
  simp

theorem deltaP_mul (D : Sec717LayerData B φ V Nb Rb T) {x y : X} (hx : x ∈ Nb) (hy : y ∈ Nb) :
    deltaP B φ T (x * y) = deltaP B φ T x + deltaP B φ T y := by
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.add_apply, deltaP_apply, deltaP_apply, deltaP_apply, map_mul, opm_mul,
    (D.Nb_low x hx).bot _ ((D.Nb_low y hy).mid _ w.2), add_zero]

theorem deltaP_eq_zero_iff (D : Sec717LayerData B φ V Nb Rb T) {x : X}
    (hx : x ∈ Nb) : deltaP B φ T x = 0 ↔ x ∈ V := by
  constructor
  · intro h
    refine D.mem_of_eqOn_zero hx fun w hw => ?_
    have h1 := LinearMap.congr_fun h ⟨w, hw⟩
    rwa [deltaP_apply, LinearMap.zero_apply] at h1
  · intro hxV
    refine LinearMap.ext fun w => ?_
    rw [deltaP_apply, LinearMap.zero_apply]
    exact (D.V_corner x hxV).mid _ w.2

@[expose] def resP (D : Sec717LayerData B φ V Nb Rb T) {g : X} (hg : g ∈ Rb) :
    ↥(B.orthogonal T) →ₗ[K] ↥(B.orthogonal T) :=
  (φ g : E →ₗ[K] E).restrict fun w hw => D.Rb_P g hg w hw

theorem resP_apply (D : Sec717LayerData B φ V Nb Rb T) {g : X} (hg : g ∈ Rb)
    (w : ↥(B.orthogonal T)) : (resP D hg w : E) = φ g (w : E) := rfl

theorem deltaP_conj (D : Sec717LayerData B φ V Nb Rb T) {r : X} (hr : r ∈ Rb) (x : X) :
    deltaP B φ T (r * x * r⁻¹) =
      (φ r : E →ₗ[K] E) ∘ₗ deltaP B φ T x ∘ₗ resP D (Rb.inv_mem hr) := by
  refine LinearMap.ext fun w => ?_
  rw [deltaP_apply, opm_conj, LinearMap.comp_apply, LinearMap.comp_apply, deltaP_apply,
    resP_apply]
  rfl

theorem deltaP_conj_of_mem_Nb (D : Sec717LayerData B φ V Nb Rb T) {n x : X} (hn : n ∈ Nb)
    (hx : x ∈ Nb) : deltaP B φ T (n * x * n⁻¹) = deltaP B φ T x := by
  refine LinearMap.ext fun w => ?_
  rw [deltaP_apply, deltaP_apply, opm_conj]
  have e1 : φ n⁻¹ (w : E) = (w : E) + opm (φ n⁻¹) (w : E) := by
    rw [opm_apply]
    abel
  rw [e1, map_add, (D.Nb_low x hx).bot _ ((D.Nb_low _ (Nb.inv_mem hn)).mid _ w.2), add_zero]
  have h2 := (D.Nb_low n hn).bot _ ((D.Nb_low x hx).mid _ w.2)
  rw [opm_apply, sub_eq_zero] at h2
  exact h2

variable {L : Subgroup X}

@[expose] def deltaSub (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w) :
    Submodule K (↥(B.orthogonal T) →ₗ[K] E) where
  carrier := {f | ∃ l ∈ L, deltaP B φ T l = f}
  add_mem' := by
    rintro _ _ ⟨l, hl, rfl⟩ ⟨l', hl', rfl⟩
    exact ⟨l * l', L.mul_mem hl hl', deltaP_mul D (hLN hl) (hLN hl')⟩
  zero_mem' := ⟨1, L.one_mem, deltaP_one⟩
  smul_mem' := by
    rintro c _ ⟨l, hl, rfl⟩
    obtain ⟨l', hl', h⟩ := hΔ l hl c
    exact ⟨l', hl', LinearMap.ext fun w => h w w.2⟩

theorem mem_deltaSub (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w)
    {l : X} (hl : l ∈ L) : deltaP B φ T l ∈ deltaSub D hLN hΔ := ⟨l, hl, rfl⟩

@[expose] def deltaHom (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w) :
    ↥L →* Multiplicative ↥(deltaSub D hLN hΔ) where
  toFun l := Multiplicative.ofAdd ⟨deltaP B φ T l, mem_deltaSub D hLN hΔ l.2⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact deltaP_one
  map_mul' l l' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact deltaP_mul D (hLN l.2) (hLN l'.2)

theorem deltaHom_coe (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w)
    (l : ↥L) :
    ((Multiplicative.toAdd (deltaHom D hLN hΔ l) : ↥(deltaSub D hLN hΔ)) :
      ↥(B.orthogonal T) →ₗ[K] E) = deltaP B φ T l := rfl

theorem deltaHom_surjective (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w) :
    Function.Surjective (deltaHom D hLN hΔ) := by
  intro f
  obtain ⟨l, hl, hlf⟩ := (Multiplicative.toAdd f).2
  refine ⟨⟨l, hl⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  exact Subtype.ext hlf

theorem deltaHom_eq_one_iff (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w)
    (l : ↥L) : deltaHom D hLN hΔ l = 1 ↔ (l : X) ∈ V := by
  rw [← deltaP_eq_zero_iff D (hLN l.2)]
  constructor
  · intro h
    have h1 := congrArg (fun f => ((Multiplicative.toAdd f : ↥(deltaSub D hLN hΔ)) :
      ↥(B.orthogonal T) →ₗ[K] E)) h
    exact h1
  · intro h
    apply Multiplicative.toAdd.injective
    exact Subtype.ext h

theorem card_deltaSub_mul [Finite X] (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hVL : V ≤ L)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w) :
    Nat.card ↥(deltaSub D hLN hΔ) * Nat.card V = Nat.card L := by
  have hker : (deltaHom D hLN hΔ).ker = V.subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact deltaHom_eq_one_iff D hLN hΔ l
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (deltaHom D hLN hΔ).ker
  have h2 : Nat.card (↥L ⧸ (deltaHom D hLN hΔ).ker) = Nat.card ↥(deltaSub D hLN hΔ) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (deltaHom_surjective D hLN hΔ)).toEquiv]
    rfl
  have h3 : Nat.card (deltaHom D hLN hΔ).ker = Nat.card V := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv
  rw [h1, h2, h3]

@[expose] def conjL (D : Sec717LayerData B φ V Nb Rb T) {r : X} (hr : r ∈ Rb) :
    (↥(B.orthogonal T) →ₗ[K] E) →ₗ[K] (↥(B.orthogonal T) →ₗ[K] E) where
  toFun f := (φ r : E →ₗ[K] E) ∘ₗ f ∘ₗ resP D (Rb.inv_mem hr)
  map_add' f g := by
    refine LinearMap.ext fun w => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' c f := by
    refine LinearMap.ext fun w => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

theorem conjL_apply (D : Sec717LayerData B φ V Nb Rb T) {r : X} (hr : r ∈ Rb)
    (f : ↥(B.orthogonal T) →ₗ[K] E) (w : ↥(B.orthogonal T)) :
    conjL D hr f w = φ r (f (resP D (Rb.inv_mem hr) w)) := rfl

theorem conjL_deltaP (D : Sec717LayerData B φ V Nb Rb T) {r : X} (hr : r ∈ Rb) (x : X) :
    conjL D hr (deltaP B φ T x) = deltaP B φ T (r * x * r⁻¹) :=
  (deltaP_conj D hr x).symm

theorem conjL_mul (D : Sec717LayerData B φ V Nb Rb T) {r s : X} (hr : r ∈ Rb) (hs : s ∈ Rb)
    (f : ↥(B.orthogonal T) →ₗ[K] E) :
    conjL D (Rb.mul_mem hr hs) f = conjL D hr (conjL D hs f) := by
  refine LinearMap.ext fun w => ?_
  have e : resP D (Rb.inv_mem (Rb.mul_mem hr hs)) w =
      resP D (Rb.inv_mem hs) (resP D (Rb.inv_mem hr) w) := by
    apply Subtype.ext
    rw [resP_apply, resP_apply, resP_apply, mul_inv_rev, map_mul, LinearEquiv.mul_apply]
  rw [conjL_apply, conjL_apply, conjL_apply, e, map_mul, LinearEquiv.mul_apply]

theorem conjL_one (D : Sec717LayerData B φ V Nb Rb T) (f : ↥(B.orthogonal T) →ₗ[K] E) :
    conjL D Rb.one_mem f = f := by
  refine LinearMap.ext fun w => ?_
  have e : resP D (Rb.inv_mem Rb.one_mem) w = w := by
    apply Subtype.ext
    rw [resP_apply, inv_one, map_one]
    rfl
  rw [conjL_apply, e, map_one]
  rfl

theorem conjL_mem (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hRL : ∀ r ∈ Rb, ∀ l ∈ L, r * l * r⁻¹ ∈ L)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w)
    {r : X} (hr : r ∈ Rb) {f : ↥(B.orthogonal T) →ₗ[K] E} (hf : f ∈ deltaSub D hLN hΔ) :
    conjL D hr f ∈ deltaSub D hLN hΔ := by
  obtain ⟨l, hl, rfl⟩ := hf
  rw [conjL_deltaP]
  exact mem_deltaSub D hLN hΔ (hRL r hr l hl)

@[expose] def deltaRepLin (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hRL : ∀ r ∈ Rb, ∀ l ∈ L, r * l * r⁻¹ ∈ L)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w)
    {r : X} (hr : r ∈ Rb) : ↥(deltaSub D hLN hΔ) →ₗ[K] ↥(deltaSub D hLN hΔ) :=
  (conjL D hr).restrict fun _ hf => conjL_mem D hLN hRL hΔ hr hf

@[expose] def deltaRep (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hRL : ∀ r ∈ Rb, ∀ l ∈ L, r * l * r⁻¹ ∈ L)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w) :
    ↥Rb →* (↥(deltaSub D hLN hΔ) ≃ₗ[K] ↥(deltaSub D hLN hΔ)) where
  toFun r := LinearEquiv.ofLinear (deltaRepLin D hLN hRL hΔ r.2)
    (deltaRepLin D hLN hRL hΔ (Rb.inv_mem r.2))
    (LinearMap.ext fun f => Subtype.ext (by
      show conjL D r.2 (conjL D (Rb.inv_mem r.2) f) = f
      rw [← conjL_mul]
      simp only [mul_inv_cancel]
      exact conjL_one D f))
    (LinearMap.ext fun f => Subtype.ext (by
      show conjL D (Rb.inv_mem r.2) (conjL D r.2 f) = f
      rw [← conjL_mul]
      simp only [inv_mul_cancel]
      exact conjL_one D f))
  map_one' := LinearEquiv.ext fun f => Subtype.ext (conjL_one D f)
  map_mul' r s := LinearEquiv.ext fun f => Subtype.ext (conjL_mul D r.2 s.2 f)

theorem deltaRep_coe (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hRL : ∀ r ∈ Rb, ∀ l ∈ L, r * l * r⁻¹ ∈ L)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w)
    (r : ↥Rb) (f : ↥(deltaSub D hLN hΔ)) :
    ((deltaRep D hLN hRL hΔ r f : ↥(deltaSub D hLN hΔ)) : ↥(B.orthogonal T) →ₗ[K] E) =
      conjL D r.2 f := rfl

theorem deltaRep_deltaHom (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hRL : ∀ r ∈ Rb, ∀ l ∈ L, r * l * r⁻¹ ∈ L)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w)
    (r : ↥Rb) (l l' : ↥L) (h : (l' : X) = (r : X) * l * (r : X)⁻¹) :
    Multiplicative.toAdd (deltaHom D hLN hΔ l') =
      deltaRep D hLN hRL hΔ r (Multiplicative.toAdd (deltaHom D hLN hΔ l)) := by
  apply Subtype.ext
  rw [deltaRep_coe, deltaHom_coe, deltaHom_coe, conjL_deltaP, h]

theorem deltaRep_eq_one_of_mem (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb)
    (hRL : ∀ r ∈ Rb, ∀ l ∈ L, r * l * r⁻¹ ∈ L)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w)
    (r : ↥Rb) (hr : (r : X) ∈ Nb) : deltaRep D hLN hRL hΔ r = 1 := by
  refine LinearEquiv.ext fun f => Subtype.ext ?_
  obtain ⟨l, hl, hlf⟩ := f.2
  rw [deltaRep_coe]
  change conjL D r.2 (f : ↥(B.orthogonal T) →ₗ[K] E) = (f : ↥(B.orthogonal T) →ₗ[K] E)
  rw [← hlf, conjL_deltaP, deltaP_conj_of_mem_Nb D hr (hLN hl)]

theorem deltaRep_eq_one_iff (D : Sec717LayerData B φ V Nb Rb T) (hLN : L ≤ Nb) (hVL : V ≤ L)
    (hNR : Nb ≤ Rb) (hRL : ∀ r ∈ Rb, ∀ l ∈ L, r * l * r⁻¹ ∈ L)
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w)
    (hsimple : ∀ S : Subgroup X, Nb ≤ S → S ≤ Rb → (∀ r ∈ Rb, ∀ s ∈ S, r * s * r⁻¹ ∈ S) →
      S = Nb ∨ S = Rb)
    (hinvL : ∀ A : Subgroup X, V ≤ A → A ≤ L → (∀ r ∈ Rb, ∀ a ∈ A, r * a * r⁻¹ ∈ A) →
      A = V ∨ A = L)
    (hdim : 2 ≤ Module.finrank K ↥(deltaSub D hLN hΔ)) (r : ↥Rb) :
    deltaRep D hLN hRL hΔ r = 1 ↔ (r : X) ∈ Nb := by
  classical
  refine ⟨fun h1 => ?_, deltaRep_eq_one_of_mem D hLN hRL hΔ r⟩
  set R₁ : Subgroup X := (deltaRep D hLN hRL hΔ).ker.map Rb.subtype with hR₁
  have hmemR₁ : ∀ x : ↥Rb, (x : X) ∈ R₁ ↔ deltaRep D hLN hRL hΔ x = 1 := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hNR₁ : Nb ≤ R₁ := fun n hn =>
    (hmemR₁ ⟨n, hNR hn⟩).mpr (deltaRep_eq_one_of_mem D hLN hRL hΔ _ hn)
  have hR₁R : R₁ ≤ Rb := Subgroup.map_subtype_le _
  have hR₁n : ∀ g ∈ Rb, ∀ x ∈ R₁, g * x * g⁻¹ ∈ R₁ := by
    intro g hg x hx
    have hxR := hR₁R hx
    have h2 := (hmemR₁ ⟨x, hxR⟩).mp hx
    have h3 : deltaRep D hLN hRL hΔ (⟨g, hg⟩ * ⟨x, hxR⟩ * (⟨g, hg⟩ : ↥Rb)⁻¹) = 1 := by
      rw [map_mul, map_mul, h2, mul_one, map_inv, mul_inv_cancel]
    exact (hmemR₁ _).mpr h3
  rcases hsimple R₁ hNR₁ hR₁R hR₁n with h | h
  · rw [← h]
    exact (hmemR₁ r).mpr h1
  exfalso
  have hall : ∀ x : ↥Rb, deltaRep D hLN hRL hΔ x = 1 := fun x =>
    (hmemR₁ x).mp (by rw [h]; exact x.2)
  have hpos : 0 < Module.finrank K ↥(deltaSub D hLN hΔ) := by omega
  haveI : Nontrivial ↥(deltaSub D hLN hΔ) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨f₀, hf₀⟩ := exists_ne (0 : ↥(deltaSub D hLN hΔ))
  set P : Submodule K ↥(deltaSub D hLN hΔ) := K ∙ f₀ with hP
  have hPtop : P ≠ ⊤ := by
    intro hP1
    have h2 : Module.finrank K ↥P = 1 := finrank_span_singleton hf₀
    rw [hP1, finrank_top] at h2
    omega
  set A' : Subgroup ↥L :=
    (AddSubgroup.toSubgroup P.toAddSubgroup).comap (deltaHom D hLN hΔ) with hA'
  have hmemA' : ∀ l : ↥L, l ∈ A' ↔ Multiplicative.toAdd (deltaHom D hLN hΔ l) ∈ P := fun _ =>
    Iff.rfl
  set A : Subgroup X := A'.map L.subtype with hA
  have hmemA : ∀ l : ↥L, (l : X) ∈ A ↔ l ∈ A' := by
    intro l
    constructor
    · rintro ⟨y, hy, hyl⟩
      have : y = l := Subtype.ext hyl
      rw [← this]
      exact hy
    · intro hl
      exact ⟨l, hl, rfl⟩
  have hVA : V ≤ A := by
    intro v hv
    refine (hmemA ⟨v, hVL hv⟩).mpr ((hmemA' _).mpr ?_)
    rw [(deltaHom_eq_one_iff D hLN hΔ ⟨v, hVL hv⟩).mpr hv]
    exact P.zero_mem
  have hAL : A ≤ L := Subgroup.map_subtype_le _
  have hAinv : ∀ g ∈ Rb, ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    intro g hg a ha
    have haL := hAL ha
    have hgaL := hRL g hg a haL
    have h2 := deltaRep_deltaHom D hLN hRL hΔ ⟨g, hg⟩ ⟨a, haL⟩ ⟨g * a * g⁻¹, hgaL⟩ rfl
    rw [hall, LinearEquiv.coe_one, id] at h2
    refine (hmemA ⟨_, hgaL⟩).mpr ((hmemA' _).mpr ?_)
    rw [h2]
    exact (hmemA' _).mp ((hmemA ⟨a, haL⟩).mp ha)
  rcases hinvL A hVA hAL hAinv with h2 | h2
  ·
    obtain ⟨l, hl⟩ := deltaHom_surjective D hLN hΔ (Multiplicative.ofAdd f₀)
    have hlA : (l : X) ∈ A := (hmemA l).mpr ((hmemA' l).mpr (by
      rw [hl]
      exact Submodule.mem_span_singleton_self f₀))
    rw [h2] at hlA
    have h3 := (deltaHom_eq_one_iff D hLN hΔ l).mpr hlA
    rw [hl] at h3
    exact hf₀ (by simpa using h3)
  ·
    apply hPtop
    rw [eq_top_iff]
    intro g _
    obtain ⟨l, hl⟩ := deltaHom_surjective D hLN hΔ (Multiplicative.ofAdd g)
    have hlA : (l : X) ∈ A := by
      rw [h2]
      exact l.2
    have h3 := (hmemA' l).mp ((hmemA l).mp hlA)
    rw [hl] at h3
    exact h3

end CFSG.RankThree.GF2n.Stroth80.S717LN
