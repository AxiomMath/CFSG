module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitTop
public import CFSG.Quasithin.MS93.S45Pair

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

section Elem

theorem burnsideC1b_mul_self_mem_of_isSum {F : Type} [Field F] [CharP F 2] {A V Z : Subgroup G}
    {α : ↥A →* ↥(StatedSL 3 F)} {dual : Bool} {k : ℕ}
    (hV : IsSumOfNaturalModulesVia A V Z α dual k) {v : G} (hv : v ∈ V) : v * v ∈ Z := by
  obtain ⟨-, -, β, -, hβk, -⟩ := hV
  have h1 : (⟨v, hv⟩ : ↥V) * ⟨v, hv⟩ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    funext i j
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  rw [hβk, Subgroup.mem_subgroupOf] at h1
  exact h1

end Elem

section Quot

variable {A W : Subgroup G}

theorem burnsideC1b_mk_eq_one_iff [(W.subgroupOf A).Normal] (x : ↥A) :
    QuotientGroup.mk' (W.subgroupOf A) x = 1 ↔ (x : G) ∈ W := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem burnsideC1b_mk_eq_mk_iff [(W.subgroupOf A).Normal] (x y : ↥A) :
    QuotientGroup.mk' (W.subgroupOf A) x = QuotientGroup.mk' (W.subgroupOf A) y ↔
      ((x : G))⁻¹ * y ∈ W := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

theorem burnsideC1b_exists_of_mem_map [(W.subgroupOf A).Normal] {V : Subgroup G}
    {y : ↥A ⧸ W.subgroupOf A} (hy : y ∈ (V.subgroupOf A).map (QuotientGroup.mk' _)) :
    ∃ x : ↥A, (x : G) ∈ V ∧ QuotientGroup.mk' (W.subgroupOf A) x = y := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩

theorem burnsideC1b_mk_mem_map [(W.subgroupOf A).Normal] {V : Subgroup G} {x : ↥A}
    (hx : (x : G) ∈ V) :
    QuotientGroup.mk' (W.subgroupOf A) x ∈ (V.subgroupOf A).map (QuotientGroup.mk' _) :=
  Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem burnsideC1b_mem_of_mk_mem_map [(W.subgroupOf A).Normal] {V : Subgroup G} (hWV : W ≤ V)
    {x : ↥A} (hx : QuotientGroup.mk' (W.subgroupOf A) x ∈ (V.subgroupOf A).map (QuotientGroup.mk' _)) :
    (x : G) ∈ V := by
  obtain ⟨y, hyV, hyx⟩ := burnsideC1b_exists_of_mem_map hx
  have h := (burnsideC1b_mk_eq_mk_iff y x).mp hyx
  have e : (x : G) = y * (((y : G))⁻¹ * x) := by group
  rw [e]
  exact V.mul_mem hyV (hWV h)

theorem burnsideC1b_isSum_quot {F : Type} [Field F] [(W.subgroupOf A).Normal] {V Z : Subgroup G}
    {α : ↥A →* ↥(StatedSL 3 F)} (hWα : W.subgroupOf A ≤ α.ker) {dual : Bool} {k : ℕ}
    (hV : IsSumOfNaturalModulesVia A V Z α dual k) (hVA : V ≤ A) (hWZ : W ≤ Z) :
    IsSumOfNaturalModulesVia (⊤ : Subgroup (↥A ⧸ W.subgroupOf A))
      ((V.subgroupOf A).map (QuotientGroup.mk' _)) ((Z.subgroupOf A).map (QuotientGroup.mk' _))
      ((QuotientGroup.lift (W.subgroupOf A) α hWα).comp
        (⊤ : Subgroup (↥A ⧸ W.subgroupOf A)).subtype) dual k := by
  obtain ⟨hAV, hZV, β, hβs, hβk, hβe⟩ := hV
  set π := QuotientGroup.mk' (W.subgroupOf A) with hπ
  set V₁ := V.subgroupOf A with hV₁
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hV₁n : V₁.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVA).mpr hAV
  set πV := π.subgroupMap V₁ with hπV
  have hπVs : Function.Surjective πV := π.subgroupMap_surjective V₁
  set e := Subgroup.subgroupOfEquivOfLe hVA with he
  set f : ↥V₁ →* Multiplicative (Fin k → Fin 3 → F) := β.comp e.toMonoidHom with hf
  have hfe : ∀ x : ↥V₁, f x = β (e x) := fun _ => rfl
  have hecoe : ∀ x : ↥V₁, ((e x : ↥V) : G) = ((x : ↥A) : G) := fun _ => rfl
  have hker : πV.ker ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : π (x : ↥A) = 1 := by
      have := congrArg Subtype.val hx
      simpa [hπV] using this
    have h2 : ((x : ↥A) : G) ∈ W := (burnsideC1b_mk_eq_one_iff (x : ↥A)).mp h1
    have h3 : e x ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf, hecoe]
      exact hWZ h2
    exact h3
  set β' := (πV.liftOfSurjective hπVs) ⟨f, hker⟩ with hβ'
  have hβ'πV : ∀ x : ↥V₁, β' (πV x) = f x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  refine ⟨?_, ?_, β', ?_, ?_, ?_⟩
  ·
    have hn : ((V.subgroupOf A).map π).Normal := hV₁n.map π hπs
    intro g _
    exact Subgroup.le_normalizer_of_normal (H := (V.subgroupOf A).map π) (Subgroup.mem_top g)
  · exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hZV (Subgroup.mem_subgroupOf.mp hx))
  ·
    intro t
    obtain ⟨v, rfl⟩ := hβs t
    refine ⟨πV (e.symm v), ?_⟩
    rw [hβ'πV, hfe, MulEquiv.apply_symm_apply]
  ·
    ext y
    obtain ⟨x, rfl⟩ := hπVs y
    rw [MonoidHom.mem_ker, hβ'πV, hfe, ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, hecoe]
    constructor
    · intro hxZ
      exact Subgroup.mem_map.mpr ⟨(x : ↥A), Subgroup.mem_subgroupOf.mpr hxZ, rfl⟩
    · intro hy
      exact burnsideC1b_mem_of_mk_mem_map hWZ hy
  ·
    intro a' u' v' huv i
    obtain ⟨a, ha⟩ := hπs (a' : ↥A ⧸ W.subgroupOf A)
    obtain ⟨u, rfl⟩ := hπVs u'
    have hau : a * (u : ↥A) * a⁻¹ ∈ V₁ := hV₁n.conj_mem _ u.2 a
    set w : ↥V₁ := ⟨a * (u : ↥A) * a⁻¹, hau⟩ with hw
    have hwv : πV w = v' := by
      apply Subtype.ext
      show π (a * (u : ↥A) * a⁻¹) = (v' : ↥A ⧸ W.subgroupOf A)
      rw [huv, map_mul, map_mul, map_inv, ha]
      rfl
    rw [← hwv, hβ'πV, hβ'πV, hfe, hfe]
    have hα' : (((QuotientGroup.lift (W.subgroupOf A) α hWα).comp
        (⊤ : Subgroup (↥A ⧸ W.subgroupOf A)).subtype) a') = α a := by
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← ha]
      rfl
    rw [hα']
    exact hβe a (e u) (e w) (by rw [hecoe, hecoe]; rfl) i

end Quot

theorem burnsideC1b_exists_complement_sec {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : 4 ≤ Fintype.card F) {A V Z W : Subgroup G} {α : ↥A →* ↥(StatedSL 3 F)}
    (hα : Function.Surjective α) {dual : Bool} {k : ℕ}
    (hV : IsSumOfNaturalModulesVia A V Z α dual k) (hVA : V ≤ A)
    (hWZ : W ≤ Z) (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hWα : ∀ a : ↥A, (a : G) ∈ W → α a = 1)
    (hVV : ∀ x ∈ V, ∀ y ∈ V, x * y * x⁻¹ * y⁻¹ ∈ W) (hV2 : ∀ x ∈ V, x * x ∈ W)
    (hZW : ∀ a ∈ A, ∀ z ∈ Z, a * z * a⁻¹ * z⁻¹ ∈ W)
    (hker : ∀ a : ↥A, α a = 1 → ∀ v ∈ V, (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ W) :
    ∃ X : Subgroup G, W ≤ X ∧ X ≤ V ∧ A ≤ Subgroup.normalizer (X : Set G) ∧
      X ⊓ Z = W ∧ X ⊔ Z = V := by
  have hZV : Z ≤ V := hV.2.1
  have hWA : W ≤ A := hWZ.trans (hZV.trans hVA)
  haveI hN : (W.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWA).mpr hAW
  set π := QuotientGroup.mk' (W.subgroupOf A) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hWα' : W.subgroupOf A ≤ α.ker := fun x hx =>
    MonoidHom.mem_ker.mpr (hWα x (Subgroup.mem_subgroupOf.mp hx))
  set ᾱ := (QuotientGroup.lift (W.subgroupOf A) α hWα').comp
    (⊤ : Subgroup (↥A ⧸ W.subgroupOf A)).subtype with hᾱ
  have hᾱapp : ∀ a : ↥A, ᾱ ⟨π a, Subgroup.mem_top _⟩ = α a := fun a => rfl
  have hᾱs : Function.Surjective ᾱ := by
    intro t
    obtain ⟨a, rfl⟩ := hα t
    exact ⟨⟨π a, Subgroup.mem_top _⟩, hᾱapp a⟩
  set V' := (V.subgroupOf A).map π with hV'
  set Z' := (Z.subgroupOf A).map π with hZ'
  have hV'' := burnsideC1b_isSum_quot hWα' hV hVA hWZ
  have hab : ∀ x ∈ V', ∀ y ∈ V', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := burnsideC1b_exists_of_mem_map hx
    obtain ⟨y₀, hy₀, rfl⟩ := burnsideC1b_exists_of_mem_map hy
    have h1 : π (x₀ * y₀ * x₀⁻¹ * y₀⁻¹) = 1 :=
      (burnsideC1b_mk_eq_one_iff _).mpr (by simpa using hVV _ hx₀ _ hy₀)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : π x₀ * π y₀ * (π x₀)⁻¹ = π y₀ := mul_inv_eq_one.mp h1
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hsq : ∀ x ∈ V', x * x = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := burnsideC1b_exists_of_mem_map hx
    rw [← map_mul]
    exact (burnsideC1b_mk_eq_one_iff _).mpr (by simpa using hV2 _ hx₀)
  have hZW' : ∀ a ∈ (⊤ : Subgroup (↥A ⧸ W.subgroupOf A)), ∀ z ∈ Z',
      a * z * a⁻¹ * z⁻¹ ∈ (⊥ : Subgroup (↥A ⧸ W.subgroupOf A)) := by
    intro a _ z hz
    obtain ⟨a₀, rfl⟩ := hπs a
    obtain ⟨z₀, hz₀, rfl⟩ := burnsideC1b_exists_of_mem_map hz
    rw [Subgroup.mem_bot, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact (burnsideC1b_mk_eq_one_iff _).mpr (by simpa using hZW _ a₀.2 _ hz₀)
  have hker' : ∀ a : ↥(⊤ : Subgroup (↥A ⧸ W.subgroupOf A)), ᾱ a = 1 → ∀ v ∈ V',
      (a : ↥A ⧸ W.subgroupOf A) * v * (a : ↥A ⧸ W.subgroupOf A)⁻¹ * v⁻¹ ∈
        (⊥ : Subgroup (↥A ⧸ W.subgroupOf A)) := by
    intro a ha v hv
    obtain ⟨a₀, ha₀e⟩ := hπs (a : ↥A ⧸ W.subgroupOf A)
    have haa : a = ⟨π a₀, Subgroup.mem_top _⟩ := Subtype.ext ha₀e.symm
    obtain ⟨v₀, hv₀, rfl⟩ := burnsideC1b_exists_of_mem_map hv
    have ha₀ : α a₀ = 1 := (hᾱapp a₀).symm.trans (haa ▸ ha)
    rw [← ha₀e]
    rw [Subgroup.mem_bot, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact (burnsideC1b_mk_eq_one_iff _).mpr (by simpa using hker a₀ ha₀ _ hv₀)
  obtain ⟨X', -, hX'V, hX'n, hX'Z, hX'sup⟩ :=
    OrdinaryProofs.H1SL3.exists_complement_of_isSum hF hᾱs hV'' hab hsq bot_le
      (fun _ _ => Subgroup.mem_normalizer_iff.mpr fun x => by simp) hZW' hker'
  refine ⟨(X'.comap π).map A.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    refine ⟨⟨w, hWA hw⟩, ?_, rfl⟩
    show π ⟨w, hWA hw⟩ ∈ X'
    rw [(burnsideC1b_mk_eq_one_iff _).mpr hw]
    exact X'.one_mem
  · rintro _ ⟨x, hx, rfl⟩
    exact burnsideC1b_mem_of_mk_mem_map (hWZ.trans hZV) (hX'V hx)
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ (b : ↥A) (y : G), y ∈ (X'.comap π).map A.subtype →
        (b : G) * y * (b : G)⁻¹ ∈ (X'.comap π).map A.subtype := by
      rintro b _ ⟨y, hy, rfl⟩
      refine ⟨b * y * b⁻¹, ?_, rfl⟩
      show π (b * y * b⁻¹) ∈ X'
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hX'n (Subgroup.mem_top (π b))) _).mp hy
    refine ⟨key ⟨g, hg⟩ x, fun hx => ?_⟩
    have := key ⟨g, hg⟩⁻¹ _ hx
    simpa [mul_assoc] using this
  · refine le_antisymm ?_ (le_inf ?_ hWZ)
    · rintro _ ⟨⟨x, hx, rfl⟩, hxZ⟩
      have h1 : π x ∈ X' ⊓ Z' := ⟨hx, burnsideC1b_mk_mem_map hxZ⟩
      rw [hX'Z, Subgroup.mem_bot] at h1
      exact (burnsideC1b_mk_eq_one_iff x).mp h1
    · intro w hw
      refine ⟨⟨w, hWA hw⟩, ?_, rfl⟩
      show π ⟨w, hWA hw⟩ ∈ X'
      rw [(burnsideC1b_mk_eq_one_iff _).mpr hw]
      exact X'.one_mem
  · refine le_antisymm (sup_le ?_ hZV) ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact burnsideC1b_mem_of_mk_mem_map (hWZ.trans hZV) (hX'V hx)
    · intro v hv
      have hv' : π ⟨v, hVA hv⟩ ∈ X' ⊔ Z' := by
        rw [hX'sup]
        exact burnsideC1b_mk_mem_map hv
      have hX'nor : X'.Normal :=
        ⟨fun x hx g => (Subgroup.mem_normalizer_iff.mp (hX'n (Subgroup.mem_top g)) x).mp hx⟩
      rw [← SetLike.mem_coe, Subgroup.normal_mul X' Z'] at hv'
      obtain ⟨x', hx', z', hz', hxz⟩ := Set.mem_mul.mp hv'
      obtain ⟨z₀, hz₀, rfl⟩ := burnsideC1b_exists_of_mem_map hz'
      set y : ↥A := ⟨v, hVA hv⟩ * z₀⁻¹ with hy
      have hyX : π y ∈ X' := by
        rw [hy, map_mul, map_inv, ← hxz, mul_inv_cancel_right]
        exact hx'
      have e : v = (y : G) * z₀ := by rw [hy]; simp
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨y, hyX, rfl⟩) (Subgroup.mem_sup_right hz₀)

theorem burnsideC1b_commutator_mem_sec {F : Type} [Field F] {A V₁ Z₁ V₂ Z₂ W Y : Subgroup G}
    {α : ↥A →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) {dual : Bool}
    (h₁ : IsSumOfNaturalModulesVia A V₁ Z₁ α dual 1)
    (h₂ : IsSumOfNaturalModulesVia A V₂ Z₂ α dual 1)
    (hV₁A : V₁ ≤ A) (hV₂A : V₂ ≤ A) (hWZ₁ : W ≤ Z₁) (hWZ₂ : W ≤ Z₂)
    (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hWα : ∀ a : ↥A, (a : G) ∈ W → α a = 1) (hYA : Y ≤ A)
    (hY : ∀ x ∈ V₁, ∀ v ∈ V₂, ⁅x, v⁆ ∈ Y)
    (hYc : ∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ ∈ W)
    (hZ₁ : ∀ z ∈ Z₁, ∀ v ∈ V₂, ⁅z, v⁆ ∈ W) (hZ₂ : ∀ x ∈ V₁, ∀ z ∈ Z₂, ⁅x, z⁆ ∈ W) :
    ∀ x ∈ V₁, ∀ v ∈ V₂, ⁅x, v⁆ ∈ W := by
  have hWA : W ≤ A := hWZ₁.trans (h₁.2.1.trans hV₁A)
  haveI hN : (W.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWA).mpr hAW
  set π := QuotientGroup.mk' (W.subgroupOf A) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hWα' : W.subgroupOf A ≤ α.ker := fun x hx =>
    MonoidHom.mem_ker.mpr (hWα x (Subgroup.mem_subgroupOf.mp hx))
  set ᾱ := (QuotientGroup.lift (W.subgroupOf A) α hWα').comp
    (⊤ : Subgroup (↥A ⧸ W.subgroupOf A)).subtype with hᾱ
  have hᾱs : Function.Surjective ᾱ := by
    intro t
    obtain ⟨a, rfl⟩ := hα t
    exact ⟨⟨π a, Subgroup.mem_top _⟩, rfl⟩
  have h₁' := burnsideC1b_isSum_quot hWα' h₁ hV₁A hWZ₁
  have h₂' := burnsideC1b_isSum_quot hWα' h₂ hV₂A hWZ₂
  have hcomm : ∀ x y : ↥A, ⁅π x, π y⁆ = π ⁅x, y⁆ := fun x y => (map_commutatorElement π x y).symm
  have hcoe : ∀ x y : ↥A, ((⁅x, y⁆ : ↥A) : G) = ⁅(x : G), (y : G)⁆ := fun x y => by
    simp [commutatorElement_def]
  have hbot := CFSG.Quasithin.MS93.S45.commutator_eq_bot_of_isSum hᾱs h₁' h₂' ?_ ?_ ?_
  · intro x hx v hv
    have h1 : ⁅π ⟨x, hV₁A hx⟩, π ⟨v, hV₂A hv⟩⁆ ∈
        ⁅(V₁.subgroupOf A).map π, (V₂.subgroupOf A).map π⁆ :=
      Subgroup.commutator_mem_commutator (burnsideC1b_mk_mem_map hx) (burnsideC1b_mk_mem_map hv)
    rw [hbot, Subgroup.mem_bot, hcomm, burnsideC1b_mk_eq_one_iff, hcoe] at h1
    exact h1
  · intro x hx v hv g _
    obtain ⟨x₀, hx₀, rfl⟩ := burnsideC1b_exists_of_mem_map hx
    obtain ⟨v₀, hv₀, rfl⟩ := burnsideC1b_exists_of_mem_map hv
    obtain ⟨g₀, rfl⟩ := hπs g
    have hyY : ((⁅x₀, v₀⁆ : ↥A) : G) ∈ Y := by rw [hcoe]; exact hY _ hx₀ _ hv₀
    have h1 : π (g₀ * ⁅x₀, v₀⁆ * g₀⁻¹ * ⁅x₀, v₀⁆⁻¹) = 1 :=
      (burnsideC1b_mk_eq_one_iff _).mpr (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inv]
        exact hYc _ g₀.2 _ hyY)
    rw [hcomm]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : π g₀ * π ⁅x₀, v₀⁆ * (π g₀)⁻¹ = π ⁅x₀, v₀⁆ := mul_inv_eq_one.mp h1
    calc π g₀ * π ⁅x₀, v₀⁆ = π g₀ * π ⁅x₀, v₀⁆ * (π g₀)⁻¹ * π g₀ := by group
      _ = π ⁅x₀, v₀⁆ * π g₀ := by rw [h2]
  · intro z hz v hv
    obtain ⟨z₀, hz₀, rfl⟩ := burnsideC1b_exists_of_mem_map hz
    obtain ⟨v₀, hv₀, rfl⟩ := burnsideC1b_exists_of_mem_map hv
    rw [hcomm, burnsideC1b_mk_eq_one_iff, hcoe]
    exact hZ₁ _ hz₀ _ hv₀
  · intro x hx z hz
    obtain ⟨x₀, hx₀, rfl⟩ := burnsideC1b_exists_of_mem_map hx
    obtain ⟨z₀, hz₀, rfl⟩ := burnsideC1b_exists_of_mem_map hz
    rw [hcomm, burnsideC1b_mk_eq_one_iff, hcoe]
    exact hZ₂ _ hx₀ _ hz₀

end CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support
