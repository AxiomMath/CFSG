module

public import CFSG.Quasithin.Background.F9Five
public import CFSG.Quasithin.Background.F9Linear
public import CFSG.Quasithin.Background.F9Dihedral
public import CFSG.Quasithin.Background.A1a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

section Tilde

variable {V₁ H : Subgroup G}

@[expose] def toTilde (hH : H ≤ Subgroup.normalizer (V₁ : Set G)) :
    ↥H →* SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁ :=
  (secMk (Subgroup.normalizer (V₁ : Set G)) V₁).comp (Subgroup.inclusion hH)

theorem toTilde_eq_one_iff (hH : H ≤ Subgroup.normalizer (V₁ : Set G)) {x : ↥H} :
    toTilde hH x = 1 ↔ (x : G) ∈ V₁ := secMk_eq_one_iff

theorem toTilde_comm_iff (hH : H ≤ Subgroup.normalizer (V₁ : Set G)) {x y : ↥H} :
    toTilde hH x * toTilde hH y = toTilde hH y * toTilde hH x ↔
      (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ V₁ :=
  ⟨fun h => commutator_mem_of_secMk_commute (x := Subgroup.inclusion hH x)
      (y := Subgroup.inclusion hH y) h,
    fun h => secMk_comm_of_commutator_mem (x := Subgroup.inclusion hH x)
      (y := Subgroup.inclusion hH y) h⟩

theorem mem_tildeOf_iff (hH : H ≤ Subgroup.normalizer (V₁ : Set G)) {X : Subgroup G}
    (hXH : X ≤ H) {y : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁} :
    y ∈ tildeOf V₁ X ↔ ∃ x : ↥H, (x : G) ∈ X ∧ toTilde hH x = y := by
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hy
    exact ⟨⟨x, hXH hx⟩, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact mem_secImg.mpr ⟨Subgroup.inclusion hH x, hx, rfl⟩

theorem tildeOf_sup {X Y : Subgroup G} (hX : X ≤ Subgroup.normalizer (V₁ : Set G))
    (hY : Y ≤ Subgroup.normalizer (V₁ : Set G)) :
    tildeOf V₁ (X ⊔ Y) = tildeOf V₁ X ⊔ tildeOf V₁ Y := by
  unfold tildeOf secImg
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem tildeOf_inf {X Y : Subgroup G} (hV₁X : V₁ ≤ X) :
    tildeOf V₁ (X ⊓ Y) = tildeOf V₁ X ⊓ tildeOf V₁ Y := by
  refine le_antisymm (le_inf (secImg_mono inf_le_left) (secImg_mono inf_le_right)) ?_
  rintro y ⟨hy1, hy2⟩
  obtain ⟨x₁, hx₁, rfl⟩ := mem_secImg.mp hy1
  obtain ⟨x₂, hx₂, hx₂e⟩ := mem_secImg.mp hy2
  have h1 : (x₁ : G)⁻¹ * x₂ ∈ V₁ := secMk_eq_secMk_iff.mp hx₂e.symm
  have h2 : (x₂ : G) ∈ X := by
    have := X.mul_mem hx₁ (hV₁X h1)
    simpa using this
  refine mem_secImg.mpr ⟨x₂, ⟨h2, hx₂⟩, hx₂e⟩

theorem tildeOf_conjSub {X : Subgroup G} {k : G} (hk : k ∈ Subgroup.normalizer (V₁ : Set G)) :
    tildeOf V₁ (conjSub k X) =
      conjSub (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨k, hk⟩) (tildeOf V₁ X) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := mem_secImg.mp hy
    rw [mem_conjSub] at hz
    rw [mem_conjSub]
    have e : (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨k, hk⟩)⁻¹ *
        secMk (Subgroup.normalizer (V₁ : Set G)) V₁ z *
        secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨k, hk⟩ =
        secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (⟨k, hk⟩⁻¹ * z * ⟨k, hk⟩) := by
      simp [map_mul, map_inv]
    rw [e]
    exact secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (X := X)
      (x := ⟨k, hk⟩⁻¹ * z * ⟨k, hk⟩) (by simpa using hz)
  · intro hy
    rw [mem_conjSub] at hy
    obtain ⟨x, hx, hxe⟩ := mem_secImg.mp hy
    refine mem_secImg.mpr ⟨⟨k, hk⟩ * x * ⟨k, hk⟩⁻¹, ?_, ?_⟩
    · rw [mem_conjSub]
      simpa [mul_assoc] using hx
    · simp only [map_mul, map_inv, hxe]
      group

end Tilde

structure F95FiveConclusion (V₁ Vp V H : Subgroup G) (g : G) : Prop where
  normalizes : V ⊔ conjSub g⁻¹ V ≤
    Subgroup.normalizer ((Vp ⊔ conjSub g⁻¹ Vp : Subgroup G) : Set G)
  faithful : centralizerMod V₁ (V ⊔ conjSub g⁻¹ V) (Vp ⊔ conjSub g⁻¹ Vp) =
    (V ⊔ conjSub g⁻¹ V) ⊓ pCoreOf 2 H
  tilde_UH_sup : tildeOf V₁ (conjClosure Vp H) = tildeOf V₁ (Vp ⊔ conjSub g⁻¹ Vp) ⊔
    tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub g⁻¹ V))
  tilde_UH_inf : tildeOf V₁ (Vp ⊔ conjSub g⁻¹ Vp) ⊓
    tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub g⁻¹ V)) = ⊥
  tilde_UI_sup : tildeOf V₁ (Vp ⊔ conjSub g⁻¹ Vp) = tildeOf V₁ Vp ⊔ tildeOf V₁ (conjSub g⁻¹ Vp)
  tilde_Vp_inf : tildeOf V₁ Vp ⊓ tildeOf V₁ (conjSub g⁻¹ Vp) = ⊥
  tilde_Vp_eq_commutator : tildeOf V₁ Vp = tildeOf V₁ ⁅Vp ⊔ conjSub g⁻¹ Vp, V⁆
  tilde_Vp_eq_centralizer : tildeOf V₁ Vp =
    tildeOf V₁ (centralizerMod V₁ (Vp ⊔ conjSub g⁻¹ Vp) V)
  UI_eq : (V ⊔ conjSub g⁻¹ V) ⊓ pCoreOf 2 H = Vp ⊔ conjSub g⁻¹ Vp

section Fin

variable [Finite G]

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

omit [Finite G] in
theorem conjSub_inv_le_H (h : HypF91 T V L V₁ Vp H) {g : G} (hg : g ∈ H) :
    conjSub g⁻¹ V ≤ H := by
  intro y hy
  rw [mem_conjSub, inv_inv] at hy
  have := H.mul_mem (H.mul_mem (H.inv_mem hg) (h.V_le_H hy)) hg
  simpa [mul_assoc] using this

theorem F95_D_eq (h : HypF91 T V L V₁ Vp H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    {g : G} (hg : g ∈ H)
    (hI : ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H) :
    centralizerMod V₁ Vp (conjSub g⁻¹ V) = V₁ := by
  have hVgH : conjSub g⁻¹ V ≤ H := h.conjSub_inv_le_H hg
  set Vg := conjSub g⁻¹ V with hVg
  set D := centralizerMod V₁ Vp Vg with hD
  have hDVp : D ≤ Vp := centralizerMod_le_left _ _ _
  have hDV : D ≤ V := hDVp.trans h.Vp_le_V
  have hV₁D : V₁ ≤ D := by
    intro v hv
    refine ⟨h.V₁_le_Vp hv, Subgroup.le_normalizer hv, fun y hy => ?_⟩
    have hc := Subgroup.mem_centralizer_iff.mp (h.H_le_centralizer (hVgH hy)) v hv
    have e : v * y * v⁻¹ * y⁻¹ = 1 := by rw [hc]; group
    rw [e]
    exact V₁.one_mem
  by_contra hne
  have hlt : V₁ < D := lt_of_le_of_ne hV₁D (Ne.symm hne)
  let X : Subgroup G := centralizerMod V₁ H D
  have hVX : V ≤ X := fun v hv =>
    ⟨h.V_le_H hv, h.V_le_normalizer_V₁ hv, fun u hu => by
      have hc := isElemAbelian_comm h.elemAbelian hv (hDV hu)
      have e : v * u * v⁻¹ * u⁻¹ = 1 := by rw [hc]; group
      rw [e]
      exact V₁.one_mem⟩
  have hVgX : Vg ≤ X := fun y hy =>
    ⟨hVgH hy, h.H_normalizes_V₁ (hVgH hy), fun u hu => by
      have h1 := V₁.inv_mem (hu.2.2 y hy)
      have e : (u * y * u⁻¹ * y⁻¹)⁻¹ = y * u * y⁻¹ * u⁻¹ := by group
      rwa [e] at h1⟩
  have hIX : V ⊔ Vg ≤ X := sup_le hVX hVgX
  have hIH : V ⊔ Vg ≤ H := sup_le h.V_le_H hVgH
  have hconj : ∀ x ∈ V ⊔ Vg, conjSub x D = D := by
    intro x hx
    have hle : conjSub x D ≤ D := by
      intro z hz
      rw [mem_conjSub] at hz
      have h1 : x * (x⁻¹ * z * x) * x⁻¹ * (x⁻¹ * z * x)⁻¹ ∈ V₁ := (hIX hx).2.2 _ hz
      have h3 : z = (x * (x⁻¹ * z * x) * x⁻¹ * (x⁻¹ * z * x)⁻¹) * (x⁻¹ * z * x) := by group
      have h4 := D.mul_mem (hV₁D h1) hz
      rw [← h3] at h4
      exact h4
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  have hall : ∀ x ∈ V ⊔ Vg, IsPGroup 2 ↥(V ⊔ conjSub x⁻¹ V) := by
    intro x hx
    refine hyp5 x (hIH hx) (lt_of_lt_of_le hlt (le_inf hDV ?_))
    calc D = conjSub x⁻¹ D := (hconj x⁻¹ ((V ⊔ Vg).inv_mem hx)).symm
      _ ≤ conjSub x⁻¹ V := conjSub_mono _ hDV
  set I : Subgroup G := V ⊔ Vg with hIdef
  have hVI : V ≤ I := le_sup_left
  have hX2 : IsPGroup 2 ↥(V.subgroupOf I) :=
    h.isPGroup_V.of_equiv (Subgroup.subgroupOfEquivOfLe hVI).symm
  rcases baer_suzuki_subgroup (G := ↥I) (p := 2) (X := V.subgroupOf I) hX2 with hle | ⟨g', hg'⟩
  ·
    have hVP : V ≤ pCoreOf 2 I := fun v hv =>
      ⟨⟨v, hVI hv⟩, hle (show (⟨v, hVI hv⟩ : ↥I) ∈ V.subgroupOf I from hv), rfl⟩
    have hVg2 : IsPGroup 2 Vg := F7.isPGroup_conjSub h.isPGroup_V
    have hVgN : Vg ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
      (le_sup_right : Vg ≤ I).trans (le_normalizer_pCoreOf 2 I)
    have hPVg : IsPGroup 2 ↥(pCoreOf 2 I ⊔ Vg) :=
      (pCoreOf_isPGroup 2 I).to_sup_of_normal_left' hVg2 hVgN
    have hIPVg : I ≤ pCoreOf 2 I ⊔ Vg := sup_le (hVP.trans le_sup_left) le_sup_right
    refine hI fun x hx => ?_
    obtain ⟨n, hn⟩ := hPVg ⟨x, hIPVg hx⟩
    refine ⟨n, ?_⟩
    have : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    rw [this]
    exact (pCoreOf 2 H).one_mem
  ·
    apply hg'
    set Y : Subgroup ↥I := V.subgroupOf I ⊔ conjSubgroup (V.subgroupOf I) g' with hY
    have hmap : Y.map I.subtype = V ⊔ conjSub (g' : G)⁻¹ V := by
      rw [hY, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hVI]
      congr 1
      ext y
      rw [mem_conjSub, inv_inv]
      constructor
      · rintro ⟨y', hy', rfl⟩
        have h1 := Subgroup.mem_subgroupOf.mp (mem_conjSubgroup_iff.mp hy')
        simpa using h1
      · intro hy
        have hyI : y ∈ I := by
          have := I.mul_mem (I.mul_mem (I.inv_mem g'.2) (hVI hy)) g'.2
          simpa [mul_assoc] using this
        refine ⟨⟨y, hyI⟩, mem_conjSubgroup_iff.mpr (Subgroup.mem_subgroupOf.mpr ?_), rfl⟩
        simpa using hy
    have h2 : IsPGroup 2 ↥(Y.map I.subtype) := by
      rw [hmap]
      exact hall g' g'.2
    exact h2.of_equiv (Y.equivMapOfInjective I.subtype I.subtype_injective).symm

theorem toTilde_comm_Q (h : HypF91 T V L V₁ Vp H) {q u : ↥H} (hq : (q : G) ∈ pCoreOf 2 H)
    (hu : (u : G) ∈ conjClosure Vp H) :
    toTilde h.H_normalizes_V₁ q * toTilde h.H_normalizes_V₁ u =
      toTilde h.H_normalizes_V₁ u * toTilde h.H_normalizes_V₁ q := by
  rw [toTilde_comm_iff]
  have h1 := V₁.inv_mem (h.commutator_conjClosure_le _ hu _ hq)
  have e : ((u : G) * q * (u : G)⁻¹ * (q : G)⁻¹)⁻¹ = (q : G) * u * (q : G)⁻¹ * (u : G)⁻¹ := by
    group
  rwa [e] at h1

omit [Finite G] in
theorem commutator_mem_conjClosure {Vp H : Subgroup G} {x z : G} (hx : x ∈ conjClosure Vp H)
    (hz : z ∈ H) : x * z * x⁻¹ * z⁻¹ ∈ conjClosure Vp H := by
  have h1 : z * x⁻¹ * z⁻¹ ∈ conjClosure Vp H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H hz) x⁻¹).mp
      ((conjClosure Vp H).inv_mem hx)
  have e : x * z * x⁻¹ * z⁻¹ = x * (z * x⁻¹ * z⁻¹) := by group
  rw [e]
  exact (conjClosure Vp H).mul_mem hx h1

theorem commSub_toTilde (h : HypF91 T V L V₁ Vp H) {Z X : Subgroup G} {z : G} (hZH : Z ≤ H)
    (hXU : X ≤ conjClosure Vp H) (hz : z ∈ Z) (hzz : z * z = 1)
    (hZ : ∀ w ∈ Z, w ∈ pCoreOf 2 H ∨ w * z ∈ pCoreOf 2 H) :
    F9Lin.commSub (toTilde h.H_normalizes_V₁ ⟨z, hZH hz⟩) (tildeOf V₁ X) =
      tildeOf V₁ ⁅X, Z⁆ := by
  have hH := h.H_normalizes_V₁
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hXH : X ≤ H := hXU.trans (hUQ.trans (pCoreOf_le 2 H))
  have hXZH : ⁅X, Z⁆ ≤ H := Subgroup.commutator_le_of_le hXH hZH
  apply le_antisymm
  · rw [F9Lin.commSub, Subgroup.closure_le]
    rintro c ⟨e, he, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_tildeOf_iff hH hXH).mp he
    refine (mem_tildeOf_iff hH hXZH).mpr ⟨⟨z, hZH hz⟩ * x * ⟨z, hZH hz⟩⁻¹ * x⁻¹, ?_, ?_⟩
    · have h1 : ((x : G) * z * (x : G)⁻¹ * z⁻¹)⁻¹ ∈ ⁅X, Z⁆ :=
        Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hx hz)
      have e' : ((x : G) * z * (x : G)⁻¹ * z⁻¹)⁻¹ = z * x * z⁻¹ * (x : G)⁻¹ := by group
      rw [e'] at h1
      exact h1
    · simp [map_mul, map_inv]
  · set C := F9Lin.commSub (toTilde hH ⟨z, hZH hz⟩) (tildeOf V₁ X) with hC
    let M : Subgroup G := (C.comap (toTilde hH)).map H.subtype
    have hgen : ⁅X, Z⁆ ≤ M := by
      refine Subgroup.commutator_le.mpr fun x hx w hw => ?_
      have hxH : x ∈ H := hXH hx
      have hwH : w ∈ H := hZH hw
      refine ⟨⟨x, hxH⟩ * ⟨w, hwH⟩ * ⟨x, hxH⟩⁻¹ * ⟨w, hwH⟩⁻¹, ?_, rfl⟩
      show toTilde hH (⟨x, hxH⟩ * ⟨w, hwH⟩ * ⟨x, hxH⟩⁻¹ * ⟨w, hwH⟩⁻¹) ∈ C
      rcases hZ w hw with hwQ | hwQ
      · have h1 : x * w * x⁻¹ * w⁻¹ ∈ V₁ := h.commutator_conjClosure_le x (hXU hx) w hwQ
        have : toTilde hH (⟨x, hxH⟩ * ⟨w, hwH⟩ * ⟨x, hxH⟩⁻¹ * ⟨w, hwH⟩⁻¹) = 1 :=
          (toTilde_eq_one_iff hH).mpr h1
        rw [this]
        exact C.one_mem
      · set q : ↥H := ⟨w * z, H.mul_mem hwH (hZH hz)⟩ with hq
        have hwq : (⟨w, hwH⟩ : ↥H) = q * ⟨z, hZH hz⟩ := by
          apply Subtype.ext
          show w = w * z * z
          rw [mul_assoc, hzz, mul_one]
        have hxq : toTilde hH q * toTilde hH ⟨x, hxH⟩ = toTilde hH ⟨x, hxH⟩ * toTilde hH q :=
          h.toTilde_comm_Q hwQ (hXU hx)
        set κ : ↥H := ⟨x, hxH⟩ * ⟨z, hZH hz⟩ * ⟨x, hxH⟩⁻¹ * ⟨z, hZH hz⟩⁻¹ with hκ
        have hκG : (κ : G) = x * z * x⁻¹ * z⁻¹ := rfl
        have hxz : (κ : G) ∈ conjClosure Vp H := by
          rw [hκG]; exact commutator_mem_conjClosure (hXU hx) (hZH hz)
        have hqc : toTilde hH q * toTilde hH κ = toTilde hH κ * toTilde hH q :=
          h.toTilde_comm_Q hwQ hxz
        set a := toTilde hH ⟨x, hxH⟩ with ha
        set b := toTilde hH q with hb
        set c := toTilde hH ⟨z, hZH hz⟩ with hc
        have hcomm0 : toTilde hH κ = a * c * a⁻¹ * c⁻¹ := by
          simp only [hκ, map_mul, map_inv, ha, hc]
        rw [hcomm0] at hqc
        have hgoal : toTilde hH (⟨x, hxH⟩ * ⟨w, hwH⟩ * ⟨x, hxH⟩⁻¹ * ⟨w, hwH⟩⁻¹) =
            (c * a * c⁻¹ * a⁻¹)⁻¹ := by
          rw [hwq]
          simp only [map_mul, map_inv]
          change a * (b * c) * a⁻¹ * (b * c)⁻¹ = _
          calc a * (b * c) * a⁻¹ * (b * c)⁻¹ = a * b * c * a⁻¹ * c⁻¹ * b⁻¹ := by group
            _ = b * a * c * a⁻¹ * c⁻¹ * b⁻¹ := by rw [← hxq]
            _ = b * (a * c * a⁻¹ * c⁻¹) * b⁻¹ := by group
            _ = (a * c * a⁻¹ * c⁻¹) * b * b⁻¹ := by rw [hqc]
            _ = a * c * a⁻¹ * c⁻¹ := by group
            _ = (c * a * c⁻¹ * a⁻¹)⁻¹ := by group
        rw [hgoal]
        refine C.inv_mem (Subgroup.subset_closure ⟨a, ?_, ?_⟩)
        · exact (mem_tildeOf_iff hH hXH).mpr ⟨⟨x, hxH⟩, hx, rfl⟩
        · rfl
    intro y hy
    obtain ⟨w', hw', rfl⟩ := (mem_tildeOf_iff hH hXZH).mp hy
    obtain ⟨m, hm, hmw⟩ := hgen hw'
    have : m = w' := Subtype.ext hmw
    rw [← this]
    exact hm

theorem fixSub_toTilde (h : HypF91 T V L V₁ Vp H) {Z X : Subgroup G} {z : G} (hZH : Z ≤ H)
    (hXU : X ≤ conjClosure Vp H) (hz : z ∈ Z) (hzz : z * z = 1)
    (hZ : ∀ w ∈ Z, w ∈ pCoreOf 2 H ∨ w * z ∈ pCoreOf 2 H) :
    F9Lin.fixSub (toTilde h.H_normalizes_V₁ ⟨z, hZH hz⟩) (tildeOf V₁ X) =
      tildeOf V₁ (centralizerMod V₁ X Z) := by
  have hH := h.H_normalizes_V₁
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hXH : X ≤ H := hXU.trans (hUQ.trans (pCoreOf_le 2 H))
  have hcH : centralizerMod V₁ X Z ≤ H := (centralizerMod_le_left _ _ _).trans hXH
  ext c
  rw [F9Lin.mem_fixSub]
  constructor
  · rintro ⟨hc, hfix⟩
    obtain ⟨x, hx, rfl⟩ := (mem_tildeOf_iff hH hXH).mp hc
    refine (mem_tildeOf_iff hH hcH).mpr ⟨x, ⟨hx, hH x.2, ?_⟩, rfl⟩
    intro w hw
    have hwH : w ∈ H := hZH hw
    have hzx : toTilde hH ⟨z, hZH hz⟩ * toTilde hH x = toTilde hH x * toTilde hH ⟨z, hZH hz⟩ := by
      calc toTilde hH ⟨z, hZH hz⟩ * toTilde hH x
          = (toTilde hH ⟨z, hZH hz⟩ * toTilde hH x * (toTilde hH ⟨z, hZH hz⟩)⁻¹) *
            toTilde hH ⟨z, hZH hz⟩ := by group
        _ = toTilde hH x * toTilde hH ⟨z, hZH hz⟩ := by rw [hfix]
    have hxw : toTilde hH x * toTilde hH ⟨w, hwH⟩ = toTilde hH ⟨w, hwH⟩ * toTilde hH x := by
      rcases hZ w hw with hwQ | hwQ
      · exact (h.toTilde_comm_Q (q := ⟨w, hwH⟩) hwQ (hXU hx)).symm
      · set q : ↥H := ⟨w * z, H.mul_mem hwH (hZH hz)⟩ with hq
        have hwq : (⟨w, hwH⟩ : ↥H) = q * ⟨z, hZH hz⟩ := by
          apply Subtype.ext
          show w = w * z * z
          rw [mul_assoc, hzz, mul_one]
        have hxq : toTilde hH q * toTilde hH x = toTilde hH x * toTilde hH q :=
          h.toTilde_comm_Q hwQ (hXU hx)
        rw [hwq, map_mul]
        calc toTilde hH x * (toTilde hH q * toTilde hH ⟨z, hZH hz⟩)
            = (toTilde hH x * toTilde hH q) * toTilde hH ⟨z, hZH hz⟩ := by rw [mul_assoc]
          _ = (toTilde hH q * toTilde hH x) * toTilde hH ⟨z, hZH hz⟩ := by rw [hxq]
          _ = toTilde hH q * (toTilde hH x * toTilde hH ⟨z, hZH hz⟩) := by rw [mul_assoc]
          _ = toTilde hH q * (toTilde hH ⟨z, hZH hz⟩ * toTilde hH x) := by rw [← hzx]
          _ = toTilde hH q * toTilde hH ⟨z, hZH hz⟩ * toTilde hH x := by rw [mul_assoc]
    exact (toTilde_comm_iff hH).mp hxw
  · intro hc
    refine ⟨secImg_mono (centralizerMod_le_left _ _ _) hc, ?_⟩
    obtain ⟨x, hx, rfl⟩ := (mem_tildeOf_iff hH hcH).mp hc
    have hcomm := (toTilde_comm_iff hH (x := x) (y := ⟨z, hZH hz⟩)).mpr (hx.2.2 z hz)
    calc toTilde hH ⟨z, hZH hz⟩ * toTilde hH x * (toTilde hH ⟨z, hZH hz⟩)⁻¹
        = toTilde hH x * toTilde hH ⟨z, hZH hz⟩ * (toTilde hH ⟨z, hZH hz⟩)⁻¹ := by
          rw [← hcomm]
      _ = toTilde hH x := by group

theorem exists_a₀ (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H) :
    ∃ a₀ ∈ V, a₀ * a₀ = 1 ∧ (∀ w ∈ V, w ∈ pCoreOf 2 H ∨ w * a₀ ∈ pCoreOf 2 H) ∧
      a₀ ∉ pCoreOf 2 H := by
  obtain ⟨hVp, -⟩ := h.F95_1 hidx hV
  have hVpQ : Vp ≤ pCoreOf 2 H := hVp ▸ inf_le_right
  obtain ⟨a, haV, ha⟩ := Subgroup.relIndex_dvd_two_iff.mp (hidx ▸ dvd_refl (2 : ℕ) :
    Vp.relIndex V ∣ 2)
  refine ⟨a, haV, ?_, fun w hw => ?_, fun haQ => hV fun b hb => ?_⟩
  · have := isElemAbelian_pow_eq_one h.elemAbelian haV
    rwa [pow_two] at this
  · rcases ha w hw with hwa | hwp
    · exact Or.inr (hVpQ hwa)
    · exact Or.inl (hVpQ hwp)
  · rcases ha b hb with hba | hbp
    · have := (pCoreOf 2 H).mul_mem (hVpQ hba) ((pCoreOf 2 H).inv_mem haQ)
      simpa using this
    · exact hVpQ hbp

theorem F95_conj_aux (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H) {k : G} (hk : k ∈ H) :
    ⁅conjClosure Vp H, conjSub k⁻¹ V⁆ ⊔ V₁ = conjSub k⁻¹ Vp ∧
      ⁅conjClosure Vp H, conjSub k⁻¹ V⁆ ≤ conjSub k⁻¹ Vp := by
  obtain ⟨hM, hUV, -⟩ := h.F95_2_aux hidx hV
  have hkU : conjSub k⁻¹ (conjClosure Vp H) = conjClosure Vp H :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Vp H (H.inv_mem hk))
  have hkV₁ : conjSub k⁻¹ V₁ = V₁ :=
    F7.conjSub_eq_of_mem_normalizer (h.H_normalizes_V₁ (H.inv_mem hk))
  have hc : conjSub k⁻¹ ⁅conjClosure Vp H, V⁆ = ⁅conjClosure Vp H, conjSub k⁻¹ V⁆ := by
    rw [← conjSub_commutator, hkU]
  refine ⟨?_, ?_⟩
  · calc ⁅conjClosure Vp H, conjSub k⁻¹ V⁆ ⊔ V₁
        = conjSub k⁻¹ ⁅conjClosure Vp H, V⁆ ⊔ conjSub k⁻¹ V₁ := by rw [hc, hkV₁]
      _ = conjSub k⁻¹ (⁅conjClosure Vp H, V⁆ ⊔ V₁) := (conjSub_sup _ _ _).symm
      _ = conjSub k⁻¹ Vp := by rw [hM]
  · rw [← hc]
    exact conjSub_mono _ hUV

end HypF91

omit [Finite G] in
theorem centralizerMod_sup_right {V₁ X A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V₁ : Set G)) (hB : B ≤ Subgroup.normalizer (V₁ : Set G)) :
    centralizerMod V₁ X (A ⊔ B) = centralizerMod V₁ X A ⊓ centralizerMod V₁ X B := by
  refine le_antisymm (le_inf (centralizerMod_anti_right X le_sup_left)
    (centralizerMod_anti_right X le_sup_right)) ?_
  rintro x ⟨⟨hxX, hxN, hxA⟩, ⟨-, -, hxB⟩⟩
  let Cx : Subgroup G :=
    { carrier := {y | y ∈ Subgroup.normalizer (V₁ : Set G) ∧ x * y * x⁻¹ * y⁻¹ ∈ V₁}
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁N, hy₁⟩ ⟨hy₂N, hy₂⟩
        refine ⟨Subgroup.mul_mem _ hy₁N hy₂N, ?_⟩
        have h1 : y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹ ∈ V₁ :=
          (Subgroup.mem_normalizer_iff.mp hy₁N _).mp hy₂
        have e : x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ =
            (x * y₁ * x⁻¹ * y₁⁻¹) * (y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
        rw [e]
        exact V₁.mul_mem hy₁ h1
      inv_mem' := by
        rintro y ⟨hyN, hy⟩
        refine ⟨Subgroup.inv_mem _ hyN, ?_⟩
        have h1 : y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ ∈ V₁ :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) _).mp (V₁.inv_mem hy)
        have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e]
        exact h1 }
  have hAC : A ≤ Cx := fun y hy => ⟨hA hy, hxA y hy⟩
  have hBC : B ≤ Cx := fun y hy => ⟨hB hy, hxB y hy⟩
  have hsup : A ⊔ B ≤ Cx := sup_le hAC hBC
  exact ⟨hxX, hxN, fun y hy => (hsup hy).2⟩

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

omit [Finite G] in
theorem conjSub_inv_le_U {Vp H : Subgroup G} {g : G} (hg : g ∈ H) {X : Subgroup G}
    (hX : X ≤ conjClosure Vp H) : conjSub g⁻¹ X ≤ conjClosure Vp H := by
  intro y hy
  rw [mem_conjSub, inv_inv] at hy
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H (H.inv_mem hg)) _).mp
    (hX hy)
  simpa [mul_assoc] using this

theorem F95_five_core (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    {g : G} (hg : g ∈ H)
    (hI : ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H) :
    tildeOf V₁ Vp ⊓ tildeOf V₁ (conjSub g⁻¹ Vp) = ⊥ ∧
      tildeOf V₁ Vp = tildeOf V₁ ⁅Vp ⊔ conjSub g⁻¹ Vp, V⁆ ∧
      tildeOf V₁ Vp = tildeOf V₁ (centralizerMod V₁ (Vp ⊔ conjSub g⁻¹ Vp) V) ∧
      tildeOf V₁ (conjClosure Vp H) = tildeOf V₁ (Vp ⊔ conjSub g⁻¹ Vp) ⊔
        tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub g⁻¹ V)) ∧
      tildeOf V₁ (Vp ⊔ conjSub g⁻¹ Vp) ⊓
        tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub g⁻¹ V)) = ⊥ := by
  have hH := h.H_normalizes_V₁
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hUH : conjClosure Vp H ≤ H := hUQ.trans (pCoreOf_le 2 H)
  obtain ⟨a₀, ha₀V, ha₀₀, hZV, -⟩ := h.exists_a₀ hidx hV
  have hVgH : conjSub g⁻¹ V ≤ H := h.conjSub_inv_le_H hg
  have hVp_le_V : Vp ≤ V := h.Vp_le_V
  have hVpU : Vp ≤ conjClosure Vp H := le_conjClosure Vp H
  have hVpgU : conjSub g⁻¹ Vp ≤ conjClosure Vp H := conjSub_inv_le_U hg hVpU
  have hV₁Vpg : V₁ ≤ conjSub g⁻¹ Vp := by
    have : conjSub g⁻¹ V₁ = V₁ := F7.conjSub_eq_of_mem_normalizer (hH (H.inv_mem hg))
    rw [← this]
    exact conjSub_mono _ h.V₁_le_Vp
  have hV₁U : V₁ ≤ conjClosure Vp H := h.V₁_le_Vp.trans hVpU
  set b₀ : G := g⁻¹ * a₀ * g with hb₀
  have hb₀V : b₀ ∈ conjSub g⁻¹ V := by
    rw [mem_conjSub, inv_inv]
    have : g * b₀ * g⁻¹ = a₀ := by rw [hb₀]; group
    rw [this]
    exact ha₀V
  have hb₀₀ : b₀ * b₀ = 1 := by
    have : b₀ * b₀ = g⁻¹ * (a₀ * a₀) * g := by rw [hb₀]; group
    rw [this, ha₀₀]; group
  have hZg : ∀ w ∈ conjSub g⁻¹ V, w ∈ pCoreOf 2 H ∨ w * b₀ ∈ pCoreOf 2 H := by
    intro w hw
    rw [mem_conjSub, inv_inv] at hw
    rcases hZV _ hw with h1 | h1
    · exact Or.inl ((Subgroup.mem_normalizer_iff.mp (hQn hg) w).mpr h1)
    · refine Or.inr ((Subgroup.mem_normalizer_iff.mp (hQn hg) (w * b₀)).mpr ?_)
      have : g * (w * b₀) * g⁻¹ = (g * w * g⁻¹) * a₀ := by rw [hb₀]; group
      rw [this]
      exact h1
  have hI' : ¬ ∀ x ∈ V ⊔ conjSub (g⁻¹)⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H := by
    intro hall
    apply hI
    intro z hz
    have hzm : g * z * g⁻¹ ∈ V ⊔ conjSub (g⁻¹)⁻¹ V := by
      rw [inv_inv]
      have hmem : g * z * g⁻¹ ∈ conjSub g (V ⊔ conjSub g⁻¹ V) := by
        rw [mem_conjSub]
        have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
        rw [e]; exact hz
      rw [conjSub_sup, conjSub_inv_conjSub, sup_comm] at hmem
      exact hmem
    obtain ⟨n, hn⟩ := hall _ hzm
    refine ⟨n, ?_⟩
    have e : (g * z * g⁻¹) ^ 2 ^ n = g * z ^ 2 ^ n * g⁻¹ := conj_pow
    rw [e] at hn
    exact (Subgroup.mem_normalizer_iff.mp (hQn hg) _).mpr hn
  have hVpN : Vp ≤ Subgroup.normalizer (V₁ : Set G) := hVpU.trans (hUH.trans hH)
  have hVpgN : conjSub g⁻¹ Vp ≤ Subgroup.normalizer (V₁ : Set G) := hVpgU.trans (hUH.trans hH)
  have hV₁g : conjSub g⁻¹ V₁ = V₁ := F7.conjSub_eq_of_mem_normalizer (hH (H.inv_mem hg))
  obtain ⟨x, hx⟩ : ∃ x : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁,
      x = toTilde hH ⟨a₀, h.V_le_H ha₀V⟩ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁,
      y = toTilde hH ⟨b₀, hVgH hb₀V⟩ := ⟨_, rfl⟩
  have hR1x : F9Lin.commSub x (tildeOf V₁ (conjClosure Vp H)) = tildeOf V₁ Vp := by
    rw [hx, h.commSub_toTilde h.V_le_H le_rfl ha₀V ha₀₀ hZV]
    exact (h.F95_2 hidx hV).2
  obtain ⟨hMg, hUVg⟩ := h.F95_conj_aux hidx hV hg
  have hR1y : F9Lin.commSub y (tildeOf V₁ (conjClosure Vp H)) = tildeOf V₁ (conjSub g⁻¹ Vp) := by
    rw [hy, h.commSub_toTilde hVgH le_rfl hb₀V hb₀₀ hZg]
    have e := tildeOf_sup_self (V₁ := V₁) (X := ⁅conjClosure Vp H, conjSub g⁻¹ V⁆)
      (hUVg.trans hVpgN)
    rw [hMg] at e
    exact e.symm
  have hR2x : F9Lin.fixSub x (tildeOf V₁ (conjClosure Vp H)) =
      tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) V) := by
    rw [hx]; exact h.fixSub_toTilde h.V_le_H le_rfl ha₀V ha₀₀ hZV
  have hR2y : F9Lin.fixSub y (tildeOf V₁ (conjClosure Vp H)) =
      tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (conjSub g⁻¹ V)) := by
    rw [hy]; exact h.fixSub_toTilde hVgH le_rfl hb₀V hb₀₀ hZg
  have hD : centralizerMod V₁ Vp (conjSub g⁻¹ V) = V₁ := h.F95_D_eq hyp5 hg hI
  have hD' : centralizerMod V₁ (conjSub g⁻¹ Vp) V = V₁ := by
    have h1 := h.F95_D_eq hyp5 (H.inv_mem hg) hI'
    rw [inv_inv] at h1
    have h2 := congrArg (conjSub g⁻¹) h1
    rw [conjSub_centralizerMod, hV₁g, conjSub_conjSub_inv] at h2
    exact h2
  have hA : F9Lin.commSub x (tildeOf V₁ (conjClosure Vp H)) ⊓
      F9Lin.fixSub y (tildeOf V₁ (conjClosure Vp H)) = ⊥ := by
    rw [hR1x, hR2y, ← tildeOf_inf h.V₁_le_Vp]
    have e : Vp ⊓ centralizerMod V₁ (conjClosure Vp H) (conjSub g⁻¹ V) =
        centralizerMod V₁ Vp (conjSub g⁻¹ V) := by
      ext z
      constructor
      · rintro ⟨hz1, hz2⟩
        exact ⟨hz1, hz2.2⟩
      · intro hz
        exact ⟨hz.1, hVpU hz.1, hz.2⟩
    rw [e, hD]
    exact tildeOf_eq_bot_of_le le_rfl
  have hB : F9Lin.commSub y (tildeOf V₁ (conjClosure Vp H)) ⊓
      F9Lin.fixSub x (tildeOf V₁ (conjClosure Vp H)) = ⊥ := by
    rw [hR1y, hR2x, ← tildeOf_inf hV₁Vpg]
    have e : conjSub g⁻¹ Vp ⊓ centralizerMod V₁ (conjClosure Vp H) V =
        centralizerMod V₁ (conjSub g⁻¹ Vp) V := by
      ext z
      constructor
      · rintro ⟨hz1, hz2⟩
        exact ⟨hz1, hz2.2⟩
      · intro hz
        exact ⟨hz.1, hVpgU hz.1, hz.2⟩
    rw [e, hD']
    exact tildeOf_eq_bot_of_le le_rfl
  have hC : Nat.card (F9Lin.commSub x (tildeOf V₁ (conjClosure Vp H))) =
      Nat.card (F9Lin.commSub y (tildeOf V₁ (conjClosure Vp H))) := by
    rw [hR1x, hR1y, tildeOf_conjSub (hH (H.inv_mem hg))]
    exact (card_conjSub _ _).symm
  have hS : ∀ a ∈ tildeOf V₁ (conjClosure Vp H), ∀ b ∈ tildeOf V₁ (conjClosure Vp H),
      a * b = b * a := fun a ha b hb => isElemAbelian_comm h.isElemAbelian_tilde ha hb
  have hS2 : ∀ a ∈ tildeOf V₁ (conjClosure Vp H), a * a = 1 := fun a ha => by
    have := isElemAbelian_pow_eq_one h.isElemAbelian_tilde ha
    rwa [pow_two] at this
  have hxN : x ∈ Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) : Set _) := by
    rw [hx]
    exact secMk_mem_normalizer_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (X := conjClosure Vp H) (a := Subgroup.inclusion hH ⟨a₀, h.V_le_H ha₀V⟩)
      (le_normalizer_conjClosure Vp H (h.V_le_H ha₀V))
  have hyN : y ∈ Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) : Set _) := by
    rw [hy]
    exact secMk_mem_normalizer_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (X := conjClosure Vp H) (a := Subgroup.inclusion hH ⟨b₀, hVgH hb₀V⟩)
      (le_normalizer_conjClosure Vp H (hVgH hb₀V))
  have hxx1 : x * x = 1 := by
    have : (⟨a₀, h.V_le_H ha₀V⟩ : ↥H) * ⟨a₀, h.V_le_H ha₀V⟩ = 1 := Subtype.ext ha₀₀
    rw [hx, ← map_mul, this, map_one]
  have hyy1 : y * y = 1 := by
    have : (⟨b₀, hVgH hb₀V⟩ : ↥H) * ⟨b₀, hVgH hb₀V⟩ = 1 := Subtype.ext hb₀₀
    rw [hy, ← map_mul, this, map_one]
  have hxx : ∀ e ∈ tildeOf V₁ (conjClosure Vp H), x * x * e * (x * x)⁻¹ = e := fun e _ => by
    rw [hxx1]; simp
  have hyy : ∀ e ∈ tildeOf V₁ (conjClosure Vp H), y * y * e * (y * y)⁻¹ = e := fun e _ => by
    rw [hyy1]; simp
  obtain ⟨c1, c2, c3, c4, c5⟩ :=
    F9Lin.two_involutions_sub hS hS2 hxN hyN hxx hyy hA hB hC
  rw [hR1x, hR1y] at c1 c2 c3 c4 c5
  have hP12 : tildeOf V₁ Vp ⊔ tildeOf V₁ (conjSub g⁻¹ Vp) = tildeOf V₁ (Vp ⊔ conjSub g⁻¹ Vp) :=
    (tildeOf_sup hVpN hVpgN).symm
  have hV₁UI : V₁ ≤ Vp ⊔ conjSub g⁻¹ Vp := h.V₁_le_Vp.trans le_sup_left
  have hUIU : Vp ⊔ conjSub g⁻¹ Vp ≤ conjClosure Vp H := sup_le hVpU hVpgU
  rw [hP12] at c2 c3 c4 c5
  have hR1UI : F9Lin.commSub x (tildeOf V₁ (Vp ⊔ conjSub g⁻¹ Vp)) =
      tildeOf V₁ ⁅Vp ⊔ conjSub g⁻¹ Vp, V⁆ := by
    rw [hx]; exact h.commSub_toTilde h.V_le_H hUIU ha₀V ha₀₀ hZV
  have hVN : V ≤ Subgroup.normalizer (V₁ : Set G) := h.V_le_normalizer_V₁
  have hVgN : conjSub g⁻¹ V ≤ Subgroup.normalizer (V₁ : Set G) := hVgH.trans hH
  have hcmV : V₁ ≤ centralizerMod V₁ (conjClosure Vp H) V := by
    intro v hv
    refine ⟨hV₁U hv, Subgroup.le_normalizer hv, fun y hy => ?_⟩
    have hc := Subgroup.mem_centralizer_iff.mp (h.H_le_centralizer (h.V_le_H hy)) v hv
    have e : v * y * v⁻¹ * y⁻¹ = 1 := by rw [hc]; group
    rw [e]
    exact V₁.one_mem
  rw [hR2x, inf_comm, ← tildeOf_inf hV₁UI] at c2
  have e2 : (Vp ⊔ conjSub g⁻¹ Vp) ⊓ centralizerMod V₁ (conjClosure Vp H) V =
      centralizerMod V₁ (Vp ⊔ conjSub g⁻¹ Vp) V := by
    ext z
    constructor
    · rintro ⟨hz1, hz2⟩
      exact ⟨hz1, hz2.2⟩
    · intro hz
      exact ⟨hz.1, hUIU hz.1, hz.2⟩
  rw [e2] at c2
  rw [hR2x, hR2y, ← tildeOf_inf hcmV, ← centralizerMod_sup_right hVN hVgN] at c4 c5
  exact ⟨c1, c3.symm.trans hR1UI, c2.symm, c4.symm, c5⟩

theorem le_normalizer_sup_of_comm {Z A B : Subgroup G}
    (hZA : Z ≤ Subgroup.normalizer (A : Set G))
    (hc : ∀ z ∈ Z, ∀ y ∈ B, z * y * z⁻¹ * y⁻¹ ∈ A) :
    Z ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro z hz
  apply mem_normalizer_of_conjSub_eq
  have hle : conjSub z (A ⊔ B) ≤ A ⊔ B := by
    rw [conjSub_sup, F7.conjSub_eq_of_mem_normalizer (hZA hz)]
    refine sup_le le_sup_left fun e he => ?_
    rw [mem_conjSub] at he
    have h1 : z * (z⁻¹ * e * z) * z⁻¹ * (z⁻¹ * e * z)⁻¹ ∈ A := hc z hz _ he
    have h2 : e = (z * (z⁻¹ * e * z) * z⁻¹ * (z⁻¹ * e * z)⁻¹) * (z⁻¹ * e * z) := by group
    rw [h2]
    exact Subgroup.mul_mem_sup h1 he
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])

theorem F95_I_normalizes (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H) {g : G} (hg : g ∈ H) :
    V ⊔ conjSub g⁻¹ V ≤ Subgroup.normalizer ((Vp ⊔ conjSub g⁻¹ Vp : Subgroup G) : Set G) := by
  obtain ⟨-, hUV, -⟩ := h.F95_2_aux hidx hV
  obtain ⟨-, hUVg⟩ := h.F95_conj_aux hidx hV hg
  have hVpU : Vp ≤ conjClosure Vp H := le_conjClosure Vp H
  have hVpgU : conjSub g⁻¹ Vp ≤ conjClosure Vp H := conjSub_inv_le_U hg hVpU
  refine sup_le ?_ ?_
  · refine le_normalizer_sup_of_comm
      (HypF91.le_normalizer_of_isElemAbelian_le h.elemAbelian h.Vp_le_V) fun v hv y hy => ?_
    have h1 : y * v * y⁻¹ * v⁻¹ ∈ ⁅conjClosure Vp H, V⁆ :=
      Subgroup.commutator_mem_commutator (hVpgU hy) hv
    have h2 := Vp.inv_mem (hUV h1)
    have e : (y * v * y⁻¹ * v⁻¹)⁻¹ = v * y * v⁻¹ * y⁻¹ := by group
    rwa [e] at h2
  · have hVgN : conjSub g⁻¹ V ≤ Subgroup.normalizer (conjSub g⁻¹ Vp : Set G) := by
      have h1 := conjSub_mono g⁻¹ (HypF91.le_normalizer_of_isElemAbelian_le h.elemAbelian
        h.Vp_le_V)
      rwa [← conjSub_normalizer] at h1
    have := le_normalizer_sup_of_comm (A := conjSub g⁻¹ Vp) (B := Vp) hVgN fun w hw y hy => by
      have h1 : y * w * y⁻¹ * w⁻¹ ∈ ⁅conjClosure Vp H, conjSub g⁻¹ V⁆ :=
        Subgroup.commutator_mem_commutator (hVpU hy) hw
      have h2 := (conjSub g⁻¹ Vp).inv_mem (hUVg h1)
      have e : (y * w * y⁻¹ * w⁻¹)⁻¹ = w * y * w⁻¹ * y⁻¹ := by group
      rwa [e] at h2
    rwa [sup_comm] at this

theorem F95_UI_eq (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H) {g : G} (hg : g ∈ H) :
    (V ⊔ conjSub g⁻¹ V) ⊓ pCoreOf 2 H = Vp ⊔ conjSub g⁻¹ Vp := by
  obtain ⟨hVp, -⟩ := h.F95_1 hidx hV
  obtain ⟨a, haV, haa, hZV, haQ⟩ := h.exists_a₀ hidx hV
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hVpQ : Vp ≤ pCoreOf 2 H := hVp ▸ inf_le_right
  have hmemVp : ∀ x ∈ V, x ∈ pCoreOf 2 H → x ∈ Vp := fun x hxV hxQ => by
    rw [hVp]
    exact ⟨hxV, hxQ⟩
  have hVgH : conjSub g⁻¹ V ≤ H := h.conjSub_inv_le_H hg
  have hIH : V ⊔ conjSub g⁻¹ V ≤ H := sup_le h.V_le_H hVgH
  have hVpgQ : conjSub g⁻¹ Vp ≤ pCoreOf 2 H := by
    intro y hy
    rw [mem_conjSub, inv_inv] at hy
    have := (Subgroup.mem_normalizer_iff.mp (hQn (H.inv_mem hg)) _).mp (hVpQ hy)
    simpa [mul_assoc] using this
  have hUIQ : Vp ⊔ conjSub g⁻¹ Vp ≤ pCoreOf 2 H := sup_le hVpQ hVpgQ
  have hIN := h.F95_I_normalizes hidx hV hg
  refine le_antisymm ?_ (le_inf (sup_le_sup h.Vp_le_V (conjSub_mono _ h.Vp_le_V)) hUIQ)
  set b : G := g⁻¹ * a * g with hb
  have hbb : b * b = 1 := by
    calc b * b = g⁻¹ * (a * a) * g := by rw [hb]; group
      _ = 1 := by rw [haa]; group
  have hbV : b ∈ conjSub g⁻¹ V := by
    rw [mem_conjSub, inv_inv]
    have : g * b * g⁻¹ = a := by rw [hb]; group
    rw [this]
    exact haV
  have hbQ : b ∉ pCoreOf 2 H := by
    intro hbQ
    apply haQ
    have := (Subgroup.mem_normalizer_iff.mp (hQn hg) b).mp hbQ
    have e : g * b * g⁻¹ = a := by rw [hb]; group
    rwa [e] at this
  set W : Subgroup G := Subgroup.closure ({a, b} : Set G) with hW
  have haW : a ∈ W := Subgroup.subset_closure (Set.mem_insert a {b})
  have hbW : b ∈ W := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have hWI : W ≤ V ⊔ conjSub g⁻¹ V := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    rcases hx with rfl | hx
    · exact Subgroup.mem_sup_left haV
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.mem_sup_right hbV
  have hWN : W ≤ Subgroup.normalizer ((Vp ⊔ conjSub g⁻¹ Vp : Subgroup G) : Set G) :=
    hWI.trans hIN
  have hVle : V ≤ (Vp ⊔ conjSub g⁻¹ Vp) ⊔ W := by
    intro v hv
    rcases hZV v hv with hvQ | hvaQ
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hmemVp v hv hvQ))
    · have hva : v * a ∈ Vp := hmemVp _ (V.mul_mem hv haV) hvaQ
      have e : v = (v * a) * a := by rw [mul_assoc, haa, mul_one]
      rw [e]
      exact (((Vp ⊔ conjSub g⁻¹ Vp) ⊔ W)).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hva))
        (Subgroup.mem_sup_right haW)
  have hVgle : conjSub g⁻¹ V ≤ (Vp ⊔ conjSub g⁻¹ Vp) ⊔ W := by
    intro y hy
    have hv : g * y * g⁻¹ ∈ V := by
      rw [mem_conjSub, inv_inv] at hy
      exact hy
    rcases hZV _ hv with hvQ | hvaQ
    · have hyVp : y ∈ conjSub g⁻¹ Vp := by
        rw [mem_conjSub, inv_inv]
        exact hmemVp _ hv hvQ
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hyVp)
    · have hva : g * y * g⁻¹ * a ∈ Vp := hmemVp _ (V.mul_mem hv haV) hvaQ
      have h1 : g⁻¹ * (g * y * g⁻¹ * a) * g ∈ conjSub g⁻¹ Vp := by
        rw [mem_conjSub, inv_inv]
        have : g * (g⁻¹ * (g * y * g⁻¹ * a) * g) * g⁻¹ = g * y * g⁻¹ * a := by group
        rw [this]
        exact hva
      have e : (g⁻¹ * (g * y * g⁻¹ * a) * g) * b = y := by
        have e1 : (g⁻¹ * (g * y * g⁻¹ * a) * g) * (g⁻¹ * a * g) = y * g⁻¹ * (a * a) * g := by
          group
        rw [hb, e1, haa]
        group
      have := ((Vp ⊔ conjSub g⁻¹ Vp) ⊔ W).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right h1))
        (Subgroup.mem_sup_right hbW)
      rwa [e] at this
  have hIle : V ⊔ conjSub g⁻¹ V ≤ (Vp ⊔ conjSub g⁻¹ Vp) ⊔ W := sup_le hVle hVgle
  intro x hx
  obtain ⟨hxI, hxQ⟩ := hx
  have hxUW : x ∈ (↑((Vp ⊔ conjSub g⁻¹ Vp) ⊔ W : Subgroup G) : Set G) := hIle hxI
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (Vp ⊔ conjSub g⁻¹ Vp) W hWN] at hxUW
  obtain ⟨ν, hν, w, hw, hνw⟩ := Set.mem_mul.mp hxUW
  have hwQ : w ∈ pCoreOf 2 H := by
    have : w = ν⁻¹ * x := by rw [← hνw]; group
    rw [this]
    exact (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem (hUIQ hν)) hxQ
  suffices hwVp : w ∈ Vp by
    rw [← hνw]
    exact (Vp ⊔ conjSub g⁻¹ Vp).mul_mem hν (Subgroup.mem_sup_left hwVp)
  obtain ⟨k, hk⟩ := F9Dihedral.mem_closure_pair haa hbb hw
  rcases hk with hk | hk
  ·
    subst hk
    obtain ⟨s, hs⟩ := F9Dihedral.exists_conj_eq_mul_zpow haa hbb k
    have hjW : (a * b) ^ s ∈ W := zpow_mem (W.mul_mem haW hbW) s
    have hjH : (a * b) ^ s ∈ H := hIH (hWI hjW)
    have hkk : ∃ kk ∈ H, kk⁻¹ * a * kk = a * (a * b) ^ k := by
      rcases hs with hs | hs
      · exact ⟨(a * b) ^ s, hjH, hs⟩
      · refine ⟨g * (a * b) ^ s, H.mul_mem hg hjH, ?_⟩
        calc (g * (a * b) ^ s)⁻¹ * a * (g * (a * b) ^ s)
            = ((a * b) ^ s)⁻¹ * (g⁻¹ * a * g) * (a * b) ^ s := by group
          _ = a * (a * b) ^ k := hs
    obtain ⟨kk, hkkH, hkke⟩ := hkk
    have hconj : conjSub kk⁻¹ V ≤ pCoreOf 2 H ⊔ V := by
      intro y hy
      have hv : kk * y * kk⁻¹ ∈ V := by
        rw [mem_conjSub, inv_inv] at hy
        exact hy
      rcases hZV _ hv with hvQ | hvaQ
      · have : y ∈ pCoreOf 2 H := by
          have := (Subgroup.mem_normalizer_iff.mp (hQn (H.inv_mem hkkH)) _).mp hvQ
          simpa [mul_assoc] using this
        exact Subgroup.mem_sup_left this
      · have hq : kk⁻¹ * (kk * y * kk⁻¹ * a) * kk ∈ pCoreOf 2 H := by
          have := (Subgroup.mem_normalizer_iff.mp (hQn (H.inv_mem hkkH)) _).mp hvaQ
          simpa [mul_assoc] using this
        have e : (kk⁻¹ * (kk * y * kk⁻¹ * a) * kk) * (kk⁻¹ * a * kk) = y := by
          have e1 : (kk⁻¹ * (kk * y * kk⁻¹ * a) * kk) * (kk⁻¹ * a * kk) =
              y * kk⁻¹ * (a * a) * kk := by group
          rw [e1, haa]
          group
        have hkkmem : kk⁻¹ * a * kk ∈ pCoreOf 2 H ⊔ V := by
          rw [hkke]
          exact (pCoreOf 2 H ⊔ V).mul_mem (Subgroup.mem_sup_right haV)
            (Subgroup.mem_sup_left hwQ)
        have := (pCoreOf 2 H ⊔ V).mul_mem (Subgroup.mem_sup_left hq) hkkmem
        rwa [e] at this
    have hVk := h.F95_4 hidx hV hkkH hconj
    have haw : a * (a * b) ^ k ∈ V := by
      have h1 : kk⁻¹ * a * kk ∈ conjSub kk⁻¹ V := by
        rw [mem_conjSub, inv_inv]
        have : kk * (kk⁻¹ * a * kk) * kk⁻¹ = a := by group
        rw [this]
        exact haV
      rw [hVk] at h1
      rwa [hkke] at h1
    have hwV : (a * b) ^ k ∈ V := by
      have := V.mul_mem (V.inv_mem haV) haw
      simpa using this
    exact hmemVp _ hwV hwQ
  ·
    exfalso
    subst hk
    have hNorm : ((pCoreOf 2 H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hQn
    have haH : a ∈ H := h.V_le_H haV
    have hbH : b ∈ H := hVgH hbV
    refine F9Dihedral.zpow_mul_mul_notMem (N := (pCoreOf 2 H).subgroupOf H)
      (a := (⟨a, haH⟩ : ↥H)) (b := (⟨b, hbH⟩ : ↥H)) ?_ ?_ ?_ ?_ k ?_
    · show a * a ∈ pCoreOf 2 H
      rw [haa]
      exact Subgroup.one_mem _
    · show b * b ∈ pCoreOf 2 H
      rw [hbb]
      exact Subgroup.one_mem _
    · exact haQ
    · exact hbQ
    · rw [Subgroup.mem_subgroupOf]
      push_cast
      exact hwQ

theorem F95_faithful (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    {g : G} (hg : g ∈ H)
    (hI : ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H) :
    centralizerMod V₁ (V ⊔ conjSub g⁻¹ V) (Vp ⊔ conjSub g⁻¹ Vp) =
      (V ⊔ conjSub g⁻¹ V) ⊓ pCoreOf 2 H := by
  obtain ⟨-, -, -, c4, -⟩ := h.F95_five_core hidx hV hyp5 hg hI
  have hH := h.H_normalizes_V₁
  have hUH : conjClosure Vp H ≤ H := h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hVpU : Vp ≤ conjClosure Vp H := le_conjClosure Vp H
  have hUIU : Vp ⊔ conjSub g⁻¹ Vp ≤ conjClosure Vp H := sup_le hVpU (conjSub_inv_le_U hg hVpU)
  have hIH : V ⊔ conjSub g⁻¹ V ≤ H := sup_le h.V_le_H (h.conjSub_inv_le_H hg)
  have hCH : centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub g⁻¹ V) ≤ H :=
    fun y hy => hUH hy.1
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxI, hxN, hxc⟩
    have hxH : x ∈ H := hIH hxI
    refine ⟨hxI, ?_⟩
    rw [h.pCoreOf_eq_centralizerMod]
    refine ⟨hxH, hxN, fun u hu => ?_⟩
    have hle : tildeOf V₁ (conjClosure Vp H) ≤
        Subgroup.centralizer ({toTilde hH ⟨x, hxH⟩} :
          Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) := by
      rw [c4]
      refine sup_le (fun y' hy' => ?_) (fun y' hy' => ?_)
      · obtain ⟨y, hy, rfl⟩ := (mem_tildeOf_iff hH (hUIU.trans hUH)).mp hy'
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (toTilde_comm_iff hH).mpr (hxc y hy)
      · obtain ⟨y, hy, rfl⟩ := (mem_tildeOf_iff hH hCH).mp hy'
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        refine (toTilde_comm_iff hH).mpr ?_
        have h1 := V₁.inv_mem (hy.2.2 x hxI)
        have e : ((y : G) * x * (y : G)⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * (y : G)⁻¹ := by group
        rwa [e] at h1
    have hu' : toTilde hH ⟨u, hUH hu⟩ ∈ tildeOf V₁ (conjClosure Vp H) :=
      (mem_tildeOf_iff hH hUH).mpr ⟨⟨u, hUH hu⟩, hu, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hle hu') _ (Set.mem_singleton _)
    exact (toTilde_comm_iff hH).mp this
  · rintro x ⟨hxI, hxQ⟩
    rw [h.pCoreOf_eq_centralizerMod] at hxQ
    obtain ⟨-, hxN, hxc⟩ := hxQ
    exact ⟨hxI, hxN, fun u hu => hxc u (hUIU hu)⟩

theorem F95_5 (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2) (hV : ¬ V ≤ pCoreOf 2 H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    {g : G} (hg : g ∈ H)
    (hI : ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H) :
    F95FiveConclusion V₁ Vp V H g := by
  obtain ⟨c1, c3, c2, c4, c5⟩ := h.F95_five_core hidx hV hyp5 hg hI
  have hH := h.H_normalizes_V₁
  have hVpN : Vp ≤ Subgroup.normalizer (V₁ : Set G) := h.Vp_le_V.trans (h.V_le_H.trans hH)
  have hVpgN : conjSub g⁻¹ Vp ≤ Subgroup.normalizer (V₁ : Set G) :=
    (conjSub_mono _ h.Vp_le_V).trans ((h.conjSub_inv_le_H hg).trans hH)
  exact ⟨h.F95_I_normalizes hidx hV hg, h.F95_faithful hidx hV hyp5 hg hI, c4, c5,
    tildeOf_sup hVpN hVpgN, c1, c3, c2, h.F95_UI_eq hidx hV hg⟩

end HypF91

end Fin

end CFSG.Quasithin
