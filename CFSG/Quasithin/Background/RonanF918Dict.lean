module

public import CFSG.Quasithin.Background.F918P5
public import CFSG.Quasithin.Background.RonanF918Hat
import CFSG.Quasithin.Background.F918C8
import CFSG.Quasithin.Background.F918C9

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

section Defs

variable {G : Type} [Group G]

abbrev GtOf (V₁ : Subgroup G) : Type := SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁

@[expose] noncomputable def CcOf (V₁ Ug K₀ : Subgroup G) : Subgroup (GtOf V₁) :=
  tildeOf V₁ Ug ⊓ Subgroup.centralizer (tildeOf V₁ K₀ : Set (GtOf V₁))

abbrev GhOf (V₁ Ug K₀ : Subgroup G) : Type :=
  SecQuot (Subgroup.normalizer (CcOf V₁ Ug K₀ : Set (GtOf V₁))) (CcOf V₁ Ug K₀)

@[expose] noncomputable def hatOf (V₁ Ug K₀ X : Subgroup G) : Subgroup (GhOf V₁ Ug K₀) :=
  secImg (Subgroup.normalizer (CcOf V₁ Ug K₀ : Set (GtOf V₁))) (CcOf V₁ Ug K₀) (tildeOf V₁ X)

@[expose] noncomputable def hat' (V₁ Vp H K T X : Subgroup G) :
    Subgroup (GhOf V₁ (conjClosure Vp H) (conjClosure K T)) :=
  hatOf V₁ (conjClosure Vp H) (conjClosure K T) X

@[expose] def ModIso {X : Type} [Group X] (K A₁ A₂ : Subgroup X) : Prop :=
  K ≤ Subgroup.normalizer (A₁ : Set X) ∧ K ≤ Subgroup.normalizer (A₂ : Set X) ∧
    ∃ φ : ↥A₁ ≃* ↥A₂, ∀ k ∈ K, ∀ a a' : ↥A₁, (a' : X) = k * a * k⁻¹ →
      (φ a' : X) = k * (φ a : X) * k⁻¹

@[expose] def HomHat (V₁ Vp H K T I : Subgroup G) : Prop :=
  ∀ S : Subgroup (GhOf V₁ (conjClosure Vp H) (conjClosure K T)),
    S ≤ hat' V₁ Vp H K T (conjClosure I T) → hat' V₁ Vp H K T (conjClosure K T) ≤
      Subgroup.normalizer (S : Set _) →
      ModIso (hat' V₁ Vp H K T (conjClosure K T)) S (hat' V₁ Vp H K T I) →
      S ≤ hat' V₁ Vp H K T I

end Defs

section Dict

variable {G : Type} [Group G]

theorem tilde_mem_normalizer_CcOf {G : Type} [Group G] {V₁ Ug K₀ : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (V₁ : Set G)) (hxU : x ∈ Subgroup.normalizer (Ug : Set G))
    (hxK : x ∈ Subgroup.normalizer (K₀ : Set G)) :
    secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hxN⟩ ∈
      Subgroup.normalizer (CcOf V₁ Ug K₀ : Set (GtOf V₁)) := by
  have h1 := secMk_mem_normalizer_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
    (X := Ug) (a := ⟨x, hxN⟩) hxU
  have h2 := secMk_mem_normalizer_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
    (X := K₀) (a := ⟨x, hxN⟩) hxK
  have h3 := CFSG.Quasithin.RonanF918.mem_normalizer_centralizer_of_mem_normalizer h2
  rw [Subgroup.mem_normalizer_iff] at h1 h3 ⊢
  intro c
  constructor
  · intro hc
    exact ⟨(h1 c).mp hc.1, (h3 c).mp hc.2⟩
  · intro hc
    exact ⟨(h1 c).mpr hc.1, (h3 c).mpr hc.2⟩

theorem tildeUg_le_normalizer_CcOf {G : Type} [Group G] {V₁ Ug K₀ : Subgroup G}
    (hU : IsElemAbelian 2 (tildeOf V₁ Ug)) :
    tildeOf V₁ Ug ≤ Subgroup.normalizer (CcOf V₁ Ug K₀ : Set (GtOf V₁)) := by
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro c
  have hcomm : ∀ d ∈ CcOf V₁ Ug K₀, u * d = d * u := fun d hd => isElemAbelian_comm hU hu hd.1
  constructor
  · intro hc
    have : u * c * u⁻¹ = c := by rw [hcomm c hc]; group
    rw [this]; exact hc
  · intro hc
    have h1 : u * (u * c * u⁻¹) = (u * c * u⁻¹) * u := hcomm _ hc
    have : u * c * u⁻¹ = c := by
      have h2 : u * c = c * u := by
        calc u * c = u⁻¹ * (u * (u * c * u⁻¹)) * u := by group
          _ = u⁻¹ * ((u * c * u⁻¹) * u) * u := by rw [h1]
          _ = c * u := by group
      rw [h2]; group
    rw [← this]; exact hc

theorem hatOf_le_normalizer {G : Type} [Group G] {V₁ Ug K₀ X Y : Subgroup G}
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    hatOf V₁ Ug K₀ X ≤ Subgroup.normalizer (hatOf V₁ Ug K₀ Y : Set (GhOf V₁ Ug K₀)) :=
  secImg_le_normalizer_secImg (secImg_le_normalizer_secImg hXY)

theorem hatOf_conjSub {G : Type} [Group G] {V₁ Ug K₀ : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (V₁ : Set G)) (hxU : x ∈ Subgroup.normalizer (Ug : Set G))
    (hxK : x ∈ Subgroup.normalizer (K₀ : Set G)) (Y : Subgroup G) :
    hatOf V₁ Ug K₀ (conjSub x Y) =
      (hatOf V₁ Ug K₀ Y).map (MulAut.conj (secMk
        (Subgroup.normalizer (CcOf V₁ Ug K₀ : Set (GtOf V₁))) (CcOf V₁ Ug K₀)
        ⟨secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hxN⟩,
          tilde_mem_normalizer_CcOf hxN hxU hxK⟩)).toMonoidHom := by
  have h1 : tildeOf V₁ (conjSub x Y) =
      (tildeOf V₁ Y).map (MulAut.conj (secMk (Subgroup.normalizer (V₁ : Set G)) V₁
        ⟨x, hxN⟩)).toMonoidHom :=
    CFSG.Quasithin.RonanF918.secImg_conjSub (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hxN⟩ Y
  unfold hatOf
  rw [h1]
  exact CFSG.Quasithin.RonanF918.secImg_conjSub
    (Subgroup.normalizer (CcOf V₁ Ug K₀ : Set (GtOf V₁))) (CcOf V₁ Ug K₀)
    ⟨secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hxN⟩,
      tilde_mem_normalizer_CcOf hxN hxU hxK⟩ (tildeOf V₁ Y)

theorem hat_commute {G : Type} [Group G] [Finite G]
    {T V L V₁ Vp H K : Subgroup G} (h : HypF918 T V L V₁ Vp H K) {Y : Subgroup G}
    (hY : Y ≤ conjClosure Vp H)
    (z₀ : ↥(Subgroup.normalizer (CcOf V₁ (conjClosure Vp H) (conjClosure K T) : Set (GtOf V₁))))
    (hz₀ : ∃ q ∈ pCoreOf 2 H, ∃ hqN : q ∈ Subgroup.normalizer (V₁ : Set G),
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨q, hqN⟩ = (z₀ : GtOf V₁))
    {y : GhOf V₁ (conjClosure Vp H) (conjClosure K T)} (hy : y ∈ hat' V₁ Vp H K T Y) :
    secMk _ _ z₀ * y = y * secMk _ _ z₀ := by
  have h1 := h.toHypF98.toHypF91
  obtain ⟨q, hq, hqN, hqz⟩ := hz₀
  obtain ⟨z, hz, rfl⟩ := mem_secImg.mp hy
  obtain ⟨u₁, hu₁, huz⟩ := mem_secImg.mp hz
  have hqc : (q : G) ∈ centralizerMod V₁ H (conjClosure Vp H) := by
    rw [← h1.pCoreOf_eq_centralizerMod]; exact hq
  have hcomm : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨q, hqN⟩ *
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ u₁ =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ u₁ *
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨q, hqN⟩ :=
    secMk_comm_of_commutator_mem (x := ⟨q, hqN⟩) (y := u₁) (hqc.2.2 u₁ (hY hu₁))
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show (z₀ : GtOf V₁) * (z : GtOf V₁) = (z : GtOf V₁) * (z₀ : GtOf V₁)
  rw [← hqz, ← huz]
  exact hcomm

theorem le_of_hat_le {G : Type} [Group G] [Finite G]
    {T V L V₁ Vp H K : Subgroup G} (h : HypF918 T V L V₁ Vp H K) {I J : Subgroup G}
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hJU : J ≤ conjClosure Vp H)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G))
    (hJcomm : J ≤ ⁅J, conjClosure K T⁆ ⊔ V₁)
    (hle : hat' V₁ Vp H K T J ≤ hat' V₁ Vp H K T I) : J ≤ I := by
  have h1 := h.toHypF98.toHypF91
  have hUN : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
    h1.conjClosure_Vp_le_pCoreOf.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans
      h1.H_normalizes_V₁)
  have hK₀N : conjClosure K T ≤ Subgroup.normalizer (V₁ : Set G) :=
    h.K₀_le_H.trans h1.H_normalizes_V₁
  have hUel : IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)) := h1.isElemAbelian_tilde
  have hcomm_le : ⁅J, conjClosure K T⁆ ≤ I := by
    rw [Subgroup.commutator_le]
    intro j hj k hk
    have hjN : j ∈ Subgroup.normalizer (V₁ : Set G) := hUN (hJU hj)
    have hkN : k ∈ Subgroup.normalizer (V₁ : Set G) := hK₀N hk
    let j₁ : ↥(Subgroup.normalizer (V₁ : Set G)) := ⟨j, hjN⟩
    let k₁ : ↥(Subgroup.normalizer (V₁ : Set G)) := ⟨k, hkN⟩
    have hzNC := tildeUg_le_normalizer_CcOf (K₀ := conjClosure K T) hUel
      (secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (X := conjClosure Vp H)
        (x := j₁) (hJU hj))
    have hmem : secMk _ _ (⟨secMk (Subgroup.normalizer (V₁ : Set G)) V₁ j₁, hzNC⟩ :
        ↥(Subgroup.normalizer (CcOf V₁ (conjClosure Vp H) (conjClosure K T) : Set (GtOf V₁)))) ∈
        hat' V₁ Vp H K T J :=
      mem_secImg.mpr ⟨⟨_, hzNC⟩, secMk_mem_secImg hj, rfl⟩
    obtain ⟨w, hwI, hwz⟩ := mem_secImg.mp (hle hmem)
    have hcc := secMk_eq_secMk_iff.mp hwz
    obtain ⟨i₁, hi₁, hiw⟩ := mem_secImg.mp hwI
    set c : GtOf V₁ := (w : GtOf V₁)⁻¹ * secMk (Subgroup.normalizer (V₁ : Set G)) V₁ j₁ with hc
    have hjc : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ j₁ =
        secMk (Subgroup.normalizer (V₁ : Set G)) V₁ i₁ * c := by rw [hc, hiw]; group
    have hcCc : c ∈ CcOf V₁ (conjClosure Vp H) (conjClosure K T) := hcc
    have hcb : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ k₁ * c =
        c * secMk (Subgroup.normalizer (V₁ : Set G)) V₁ k₁ :=
      Subgroup.mem_centralizer_iff.mp hcCc.2 _ (secMk_mem_secImg hk)
    have hca : c * secMk (Subgroup.normalizer (V₁ : Set G)) V₁ i₁ =
        secMk (Subgroup.normalizer (V₁ : Set G)) V₁ i₁ * c :=
      isElemAbelian_comm hUel hcCc.1 (secMk_mem_secImg (hIU hi₁))
    have key : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (i₁ * k₁ * i₁⁻¹ * k₁⁻¹) =
        secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (j₁ * k₁ * j₁⁻¹ * k₁⁻¹) := by
      simp only [map_mul, map_inv]
      rw [hjc]
      set a := secMk (Subgroup.normalizer (V₁ : Set G)) V₁ i₁
      set b := secMk (Subgroup.normalizer (V₁ : Set G)) V₁ k₁
      calc a * b * a⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := rfl
        _ = (a * c) * b * (a * c)⁻¹ * b⁻¹ := by
          have e1 : (a * c) * b * (a * c)⁻¹ * b⁻¹ = a * (c * b) * c⁻¹ * a⁻¹ * b⁻¹ := by group
          rw [e1, ← hcb]; group
    have hv := secMk_eq_secMk_iff.mp key
    have hIk : k * (i₁ : G)⁻¹ * k⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp (hKI hk) _).mp (I.inv_mem hi₁)
    have hY : (i₁ : G) * k * (i₁ : G)⁻¹ * k⁻¹ ∈ I := by
      have : (i₁ : G) * k * (i₁ : G)⁻¹ * k⁻¹ = (i₁ : G) * (k * (i₁ : G)⁻¹ * k⁻¹) := by group
      rw [this]; exact I.mul_mem hi₁ hIk
    have hX : (j : G) * k * j⁻¹ * k⁻¹ ∈ I := by
      have e : (j : G) * k * j⁻¹ * k⁻¹ = ((i₁ : G) * k * (i₁ : G)⁻¹ * k⁻¹) *
          (((i₁ : G) * k * (i₁ : G)⁻¹ * k⁻¹)⁻¹ * (j * k * j⁻¹ * k⁻¹)) := by group
      rw [e]
      refine I.mul_mem hY (hV₁I ?_)
      simpa using hv
    simpa [commutatorElement_def] using hX
  exact hJcomm.trans (sup_le hcomm_le hV₁I)

theorem conjSub_le_comm {G : Type} [Group G] {V₁ I K₀ : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (V₁ : Set G)) (hxK : x ∈ Subgroup.normalizer (K₀ : Set G))
    (hIN : I ≤ Subgroup.normalizer (V₁ : Set G))
    (hcomm : tildeOf V₁ ⁅I, K₀⁆ = tildeOf V₁ I) :
    conjSub x I ≤ ⁅conjSub x I, K₀⁆ ⊔ V₁ := by
  intro j hj
  have hi : x⁻¹ * j * x ∈ I := mem_conjSub.mp hj
  have hiN : x⁻¹ * j * x ∈ Subgroup.normalizer (V₁ : Set G) := hIN hi
  have hit : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x⁻¹ * j * x, hiN⟩ ∈
      tildeOf V₁ ⁅I, K₀⁆ := by
    rw [hcomm]; exact secMk_mem_secImg hi
  obtain ⟨c₁, hc₁, hc₁i⟩ := mem_secImg.mp hit
  have hv : (c₁ : G)⁻¹ * (x⁻¹ * j * x) ∈ V₁ := secMk_eq_secMk_iff.mp hc₁i
  have e : j = (x * (c₁ : G) * x⁻¹) * (x * ((c₁ : G)⁻¹ * (x⁻¹ * j * x)) * x⁻¹) := by group
  rw [e]
  refine Subgroup.mul_mem_sup ?_ ?_
  · have h1 : x * (c₁ : G) * x⁻¹ ∈ conjSub x ⁅I, K₀⁆ := mul_mem_conjSub hc₁
    rw [← conjSub_commutator, F7.conjSub_eq_of_mem_normalizer hxK] at h1
    exact h1
  · exact (Subgroup.mem_normalizer_iff.mp hxN _).mp hv

theorem conjSub_le_of_hom {G : Type} [Group G] [Finite G]
    {T V L V₁ Vp H K I : Subgroup G} (h : HypF918 T V L V₁ Vp H K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hIrr : IsIrrPlusTilde V₁ (conjClosure K T) I)
    (hhom : ∀ S : Subgroup (GhOf V₁ (conjClosure Vp H) (conjClosure K T)),
      S ≤ hat' V₁ Vp H K T (conjClosure I T) →
      hat' V₁ Vp H K T (conjClosure K T) ≤
        Subgroup.normalizer (S : Set (GhOf V₁ (conjClosure Vp H) (conjClosure K T))) →
      ModIso (hat' V₁ Vp H K T (conjClosure K T)) S (hat' V₁ Vp H K T I) →
      S ≤ hat' V₁ Vp H K T I)
    {x : G} (hxT : x ∈ T)
    (hcxi : ∀ k ∈ conjClosure K T, x⁻¹ * k * x * k⁻¹ ∈ pCoreOf 2 H) :
    conjSub x I ≤ I := by
  have h1 := h.toHypF98.toHypF91
  have hxH : x ∈ H := h.T_le_H hxT
  have hxN : x ∈ Subgroup.normalizer (V₁ : Set G) := h1.H_normalizes_V₁ hxH
  have hxU : x ∈ Subgroup.normalizer (conjClosure Vp H : Set G) :=
    le_normalizer_conjClosure Vp H hxH
  have hxK : x ∈ Subgroup.normalizer (conjClosure K T : Set G) := le_normalizer_conjClosure K T hxT
  have hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G) := hIrr.1
  have hIN : I ≤ Subgroup.normalizer (V₁ : Set G) :=
    hIU.trans (h1.conjClosure_Vp_le_pCoreOf.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans
      h1.H_normalizes_V₁))
  have hxNC := tilde_mem_normalizer_CcOf (Ug := conjClosure Vp H) (K₀ := conjClosure K T)
    hxN hxU hxK
  set xb : GhOf V₁ (conjClosure Vp H) (conjClosure K T) :=
    secMk (Subgroup.normalizer (CcOf V₁ (conjClosure Vp H) (conjClosure K T) : Set (GtOf V₁)))
      (CcOf V₁ (conjClosure Vp H) (conjClosure K T))
      ⟨secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hxN⟩, hxNC⟩ with hxb
  have hJhat : hat' V₁ Vp H K T (conjSub x I) =
      (hat' V₁ Vp H K T I).map (MulAut.conj xb).toMonoidHom :=
    hatOf_conjSub hxN hxU hxK I
  have hJU : conjSub x I ≤ conjClosure Vp H := by
    intro y hy
    have := (Subgroup.mem_normalizer_iff.mp hxU _).mp (hIU (mem_conjSub.mp hy))
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rwa [e] at this
  have hJT : conjSub x I ≤ conjClosure I T := by
    intro y hy
    have := mem_conjClosure hxT (mem_conjSub.mp hy)
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rwa [e] at this
  have hKJ : conjClosure K T ≤ Subgroup.normalizer (conjSub x I : Set G) := by
    intro k hk
    apply mem_normalizer_of_conjSub_eq
    have hk' : x⁻¹ * k * x ∈ conjClosure K T := (Subgroup.mem_normalizer_iff''.mp hxK k).mp hk
    have e : k = x * (x⁻¹ * k * x) * x⁻¹ := by group
    calc conjSub k (conjSub x I) = conjSub (k * x) I := (conjSub_mul k x I).symm
      _ = conjSub (x * (x⁻¹ * k * x)) I := by congr 1; group
      _ = conjSub x (conjSub (x⁻¹ * k * x) I) := conjSub_mul x _ I
      _ = conjSub x I := by rw [F7.conjSub_eq_of_mem_normalizer (hKI hk')]
  have hS1 : hat' V₁ Vp H K T (conjSub x I) ≤ hat' V₁ Vp H K T (conjClosure I T) :=
    secImg_mono (secImg_mono hJT)
  have hS2 := hatOf_le_normalizer (V₁ := V₁) (Ug := conjClosure Vp H)
    (K₀ := conjClosure K T) hKJ
  have hS3 := hatOf_le_normalizer (V₁ := V₁) (Ug := conjClosure Vp H)
    (K₀ := conjClosure K T) hKI
  refine le_of_hat_le h hV₁I hIU hJU hKI (conjSub_le_comm hxN hxK hIN hIrr.2.1) ?_
  refine hhom _ hS1 hS2 ?_
  unfold ModIso
  refine ⟨hS2, hS3, ?_⟩
  let φ : ↥(hat' V₁ Vp H K T (conjSub x I)) ≃* ↥(hat' V₁ Vp H K T I) :=
    { toFun := fun s => ⟨xb⁻¹ * (s : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * xb, by
        have hs : (s : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) ∈
            (hat' V₁ Vp H K T I).map (MulAut.conj xb).toMonoidHom := by
          rw [← hJhat]; exact s.2
        obtain ⟨a, ha, hae⟩ := hs
        have : xb⁻¹ * (s : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * xb = a := by
          rw [← hae]; simp [MulAut.conj_apply, mul_assoc]
        rw [this]; exact ha⟩
      invFun := fun a => ⟨xb * (a : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * xb⁻¹, by
        rw [hJhat]
        exact ⟨a, a.2, by simp [MulAut.conj_apply]⟩⟩
      left_inv := fun s => by
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := fun a => by
        apply Subtype.ext
        simp [mul_assoc]
      map_mul' := fun a b => by
        apply Subtype.ext
        simp [mul_assoc] }
  refine ⟨φ, fun k hk a a' haa => ?_⟩
  obtain ⟨w, hw, hkw⟩ := mem_secImg.mp hk
  obtain ⟨k₁, hk₁, hk₁w⟩ := mem_secImg.mp hw
  have hcm := hcxi (k₁ : G) hk₁
  let cm₁ : ↥(Subgroup.normalizer (V₁ : Set G)) := ⟨x, hxN⟩⁻¹ * k₁ * ⟨x, hxN⟩ * k₁⁻¹
  have hcm₁ : (cm₁ : G) ∈ pCoreOf 2 H := by simpa [cm₁] using hcm
  have hcmH : (cm₁ : G) ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hcm₁
  have hcmNC := tilde_mem_normalizer_CcOf (Ug := conjClosure Vp H) (K₀ := conjClosure K T)
    cm₁.2 (le_normalizer_conjClosure Vp H hcmH) (h.K₀_normal hcmH)
  set e : GhOf V₁ (conjClosure Vp H) (conjClosure K T) :=
    secMk _ _ (⟨secMk (Subgroup.normalizer (V₁ : Set G)) V₁ cm₁, hcmNC⟩ :
      ↥(Subgroup.normalizer (CcOf V₁ (conjClosure Vp H) (conjClosure K T) : Set (GtOf V₁)))) with he
  have hrel : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (⟨x, hxN⟩⁻¹ * k₁ * ⟨x, hxN⟩) =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ cm₁ *
        secMk (Subgroup.normalizer (V₁ : Set G)) V₁ k₁ := by
    have : cm₁ * k₁ = ⟨x, hxN⟩⁻¹ * k₁ * ⟨x, hxN⟩ := by simp [cm₁, mul_assoc]
    rw [← map_mul, this]
  have hr : xb⁻¹ * k * xb = e * k := by
    rw [← hkw, hxb, he, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hxN⟩)⁻¹ * (w : GtOf V₁) *
        secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hxN⟩ =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ cm₁ * (w : GtOf V₁)
    rw [← hk₁w]
    simp only [map_mul, map_inv] at hrel
    exact hrel
  have hecomm : ∀ y ∈ hat' V₁ Vp H K T I, e * y = y * e := fun y hy =>
    hat_commute h hIU _ ⟨(cm₁ : G), hcm₁, cm₁.2, rfl⟩ hy
  show xb⁻¹ * (a' : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * xb =
    k * (xb⁻¹ * (a : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * xb) * k⁻¹
  have hb : xb⁻¹ * (a : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * xb ∈
      hat' V₁ Vp H K T I := (φ a).2
  have hkb : k * (xb⁻¹ * (a : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * xb) * k⁻¹ ∈
      hat' V₁ Vp H K T I := (Subgroup.mem_normalizer_iff.mp (hS3 hk) _).mp hb
  have hec := hecomm _ hkb
  calc xb⁻¹ * (a' : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * xb
      = (xb⁻¹ * k * xb) * (xb⁻¹ * (a : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * xb) *
          (xb⁻¹ * k * xb)⁻¹ := by rw [haa]; group
    _ = (e * k) * (xb⁻¹ * (a : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * xb) * (e * k)⁻¹ := by
        rw [hr]
    _ = e * (k * (xb⁻¹ * (a : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * xb) * k⁻¹) * e⁻¹ := by
        group
    _ = k * (xb⁻¹ * (a : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * xb) * k⁻¹ := by
        rw [hec]; group

theorem o2inv_of_homHat {G : Type} [Group G] [Finite G]
    {T V L V₁ Vp H K I : Subgroup G} (h : HypF918 T V L V₁ Vp H K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hIrr : IsIrrPlusTilde V₁ (conjClosure K T) I) (hhom : HomHat V₁ Vp H K T I) :
    pCoreOf 2 (conjClosure K T ⊔ T) ≤ Subgroup.normalizer (I : Set G) := by
  have h1 := h.toHypF98.toHypF91
  have hSyl : IsSylowTwoOf T (conjClosure K T ⊔ T) :=
    isSylowTwoOf_mono_right h1.sylow_H le_sup_right h.K₀T_le_H
  have hQ : ∀ y ∈ pCoreOf 2 (conjClosure K T ⊔ T), ∀ k ∈ conjClosure K T,
      y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    intro y hy k hk
    have hyT : y ∈ T := isSylowTwoOf_pCoreOf_le hSyl hy
    have hkKT : k ∈ conjClosure K T ⊔ T := Subgroup.mem_sup_left hk
    have hkP : k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure K T ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hkKT) y⁻¹).mp
        ((pCoreOf 2 (conjClosure K T ⊔ T)).inv_mem hy)
    have hcP : y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure K T ⊔ T) := by
      have e : y * k * y⁻¹ * k⁻¹ = y * (k * y⁻¹ * k⁻¹) := by group
      rw [e]; exact Subgroup.mul_mem _ hy hkP
    have hcK : y * k * y⁻¹ * k⁻¹ ∈ conjClosure K T :=
      (conjClosure K T).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure K T hyT) k).mp hk)
        ((conjClosure K T).inv_mem hk)
    have hEK : pCoreOf 2 (conjClosure K T ⊔ T) ⊓ conjClosure K T ≤ conjClosure K T := inf_le_right
    have hKE : conjClosure K T ≤ Subgroup.normalizer
        ((pCoreOf 2 (conjClosure K T ⊔ T) ⊓ conjClosure K T : Subgroup G) : Set G) := by
      intro k' hk'
      rw [Subgroup.mem_normalizer_iff]
      intro e
      have h2 := Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
          (Subgroup.mem_sup_left hk' : k' ∈ conjClosure K T ⊔ T)) e
      have h3 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk' :
        k' ∈ Subgroup.normalizer (conjClosure K T : Set G)) e
      exact ⟨fun he => ⟨h2.mp he.1, h3.mp he.2⟩, fun he => ⟨h2.mpr he.1, h3.mpr he.2⟩⟩
    have hall : ∀ e ∈ pCoreOf 2 (conjClosure K T ⊔ T) ⊓ conjClosure K T,
        ∃ n : ℕ, e ^ 2 ^ n ∈ pCoreOf 2 H := by
      intro e he
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure K T ⊔ T)
        ⟨e, he.1⟩
      refine ⟨n, ?_⟩
      have : e ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      rw [this]; exact Subgroup.one_mem _
    exact h.F918_1.2.2.2 _ hEK hKE hall ⟨hcP, hcK⟩
  intro x hx
  have hxT : x ∈ T := isSylowTwoOf_pCoreOf_le hSyl hx
  have hle : conjSub x I ≤ I := by
    refine conjSub_le_of_hom h hV₁I hIU hIrr hhom hxT fun k hk => ?_
    have := hQ x⁻¹ ((pCoreOf 2 (conjClosure K T ⊔ T)).inv_mem hx) k hk
    simpa using this
  apply mem_normalizer_of_conjSub_eq
  exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge

section ExistsI

open scoped Pointwise

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem tildeIH_le_normalizer_CcOf (h : HypF918 T V L V₁ Vp H K)
    (hIU : I ≤ conjClosure Vp H) :
    tildeOf V₁ (conjClosure I H) ≤
      Subgroup.normalizer (CcOf V₁ (conjClosure Vp H) (conjClosure K T) : Set (GtOf V₁)) :=
  le_trans (secImg_mono (conjClosure_le_conjClosure_U hIU le_rfl))
    (tildeUg_le_normalizer_CcOf (K₀ := conjClosure K T)
      h.toHypF98.toHypF91.isElemAbelian_tilde)

@[expose] noncomputable def thetaMap (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    ↥(tildeOf V₁ (conjClosure I H)) →* GhOf V₁ (conjClosure Vp H) (conjClosure K T) :=
  (secMk (Subgroup.normalizer (CcOf V₁ (conjClosure Vp H) (conjClosure K T) : Set (GtOf V₁)))
      (CcOf V₁ (conjClosure Vp H) (conjClosure K T))).comp
    (Subgroup.inclusion (tildeIH_le_normalizer_CcOf h hIU))

theorem thetaMap_eq_one_iff (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (u : ↥(tildeOf V₁ (conjClosure I H))) :
    thetaMap h hIU u = 1 ↔
      (u : GtOf V₁) ∈ CcOf V₁ (conjClosure Vp H) (conjClosure K T) :=
  secMk_eq_one_iff

theorem hat_eq_map_theta (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    {X : Subgroup G} (hX : X ≤ conjClosure I H) :
    hat' V₁ Vp H K T X = (subM V₁ (conjClosure I H) X).map (thetaMap h hIU) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := mem_secImg.mp hy
    exact ⟨⟨z.1, secImg_mono hX hz⟩, hz, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact mem_secImg.mpr ⟨Subgroup.inclusion (tildeIH_le_normalizer_CcOf h hIU) u,
      mem_subM_iff.mp hu, rfl⟩

@[expose] noncomputable def kbarOf (h : HypF918 T V L V₁ Vp H K) {x : G} (hx : x ∈ H) :
    GhOf V₁ (conjClosure Vp H) (conjClosure K T) :=
  secMk (Subgroup.normalizer (CcOf V₁ (conjClosure Vp H) (conjClosure K T) : Set (GtOf V₁)))
    (CcOf V₁ (conjClosure Vp H) (conjClosure K T))
    ⟨secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, h.H_le_normalizer_V₁ hx⟩,
      tilde_mem_normalizer_CcOf (h.H_le_normalizer_V₁ hx)
        (le_normalizer_conjClosure Vp H hx) (h.K₀_normal hx)⟩

theorem kbarOf_mem_hat (h : HypF918 T V L V₁ Vp H K) {x : G} (hx : x ∈ conjClosure K T) :
    kbarOf h (h.K₀_le_H hx) ∈ hat' V₁ Vp H K T (conjClosure K T) :=
  mem_secImg.mpr ⟨⟨secMk (Subgroup.normalizer (V₁ : Set G)) V₁
      ⟨x, h.H_le_normalizer_V₁ (h.K₀_le_H hx)⟩,
    tilde_mem_normalizer_CcOf (h.H_le_normalizer_V₁ (h.K₀_le_H hx))
      (le_normalizer_conjClosure Vp H (h.K₀_le_H hx)) (h.K₀_normal (h.K₀_le_H hx))⟩,
    secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (X := conjClosure K T)
      (x := ⟨x, h.H_le_normalizer_V₁ (h.K₀_le_H hx)⟩) hx, rfl⟩

theorem thetaMap_actH (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {x : G}
    (hx : x ∈ H) (u : ↥(tildeOf V₁ (conjClosure I H))) :
    thetaMap h hIU (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨x, hx⟩ u) =
      kbarOf h hx * thetaMap h hIU u * (kbarOf h hx)⁻¹ := by
  unfold thetaMap kbarOf
  simp only [MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem isIrr_of_iso {A : Type*} [Group A] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction A Q] {L L' : Subgroup Q} (hL' : XMod.IsIrr A L')
    (hinv : XMod.IsInv A L) (hiso : XMod.Iso A L L') : XMod.IsIrr A L := by
  obtain ⟨φ, hφ⟩ := hiso
  refine ⟨hinv, ?_, fun J hJ _ hJL => ?_⟩
  · refine bot_lt_iff_ne_bot.2 fun hbot => ?_
    have hL'bot : L' = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨l, hl⟩ := φ.surjective ⟨y, hy⟩
      have : (l : Q) ∈ (⊥ : Subgroup Q) := by rw [← hbot]; exact l.2
      have hl1 : l = 1 := Subtype.ext (by simpa using this)
      have : y = 1 := by
        have h1 := congrArg Subtype.val hl
        rw [hl1, map_one] at h1
        simpa using h1.symm
      rw [this]; exact Subgroup.one_mem _
    exact hL'.2.1.ne' hL'bot
  · set J' : Subgroup Q := ((J.subgroupOf L).map φ.toMonoidHom).map L'.subtype with hJ'
    have hJ'inv : XMod.IsInv A J' := by
      intro a y hy
      obtain ⟨_, ⟨j, hj, rfl⟩, rfl⟩ := hy
      have hjJ : (j : Q) ∈ J := hj
      have haj : a • (j : Q) ∈ J := hJ a _ hjJ
      have hajL : a • (j : Q) ∈ L := hinv a _ j.2
      have h1 := hφ a j ⟨a • (j : Q), hajL⟩ rfl
      refine ⟨φ ⟨a • (j : Q), hajL⟩, ⟨⟨a • (j : Q), hajL⟩, haj, rfl⟩, ?_⟩
      exact h1.symm
    have hJ'le : J' ≤ L' := by
      rintro _ ⟨w, _, rfl⟩
      exact w.2
    rcases hL'.2.2 J' hJ'inv bot_le hJ'le with h0 | hfull
    · left
      rw [eq_bot_iff]
      intro j hj
      have hjL : j ∈ L := hJL hj
      have : (φ ⟨j, hjL⟩ : Q) ∈ J' := ⟨_, ⟨⟨j, hjL⟩, hj, rfl⟩, rfl⟩
      rw [h0] at this
      have h1 : φ ⟨j, hjL⟩ = 1 := Subtype.ext (by simpa using this)
      have h2 : (⟨j, hjL⟩ : ↥L) = 1 := by
        apply φ.injective
        rw [h1, map_one]
      have : j = 1 := congrArg Subtype.val h2
      rw [this]; exact Subgroup.one_mem _
    · right
      refine le_antisymm hJL fun l hl => ?_
      have hlL' : (φ ⟨l, hl⟩ : Q) ∈ J' := by rw [hfull]; exact (φ ⟨l, hl⟩).2
      obtain ⟨w, ⟨l₀, hl₀, hl₀eq⟩, hwy⟩ := hlL'
      have h1 : φ l₀ = φ ⟨l, hl⟩ := Subtype.ext ((congrArg Subtype.val hl₀eq).trans hwy)
      have h2 : l₀ = ⟨l, hl⟩ := φ.injective h1
      have : (l₀ : Q) ∈ J := hl₀
      rwa [h2] at this

theorem exists_equivMap_of_injOn {Q₁ Q₂ : Type*} [Group Q₁] [Group Q₂] (θ : Q₁ →* Q₂)
    {S L : Subgroup Q₁} (hinj : ∀ x ∈ S, ∀ y ∈ S, θ x = θ y → x = y) (hL : L ≤ S) :
    ∃ e : ↥L ≃* ↥(L.map θ), ∀ x : ↥L, ((e x : ↥(L.map θ)) : Q₂) = θ (x : Q₁) := by
  refine ⟨MulEquiv.ofBijective (θ.subgroupMap L) ⟨fun x y hxy => ?_, θ.subgroupMap_surjective L⟩,
    fun x => rfl⟩
  apply Subtype.ext
  exact hinj _ (hL x.2) _ (hL y.2) (congrArg Subtype.val hxy)

theorem modFix_le_ker_thetaMap [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (W : Subgroup ↥(tildeOf V₁ (conjClosure I H))) :
    modFix (autIH V₁ I H (conjClosure K T)) W ≤ (thetaMap h hIU).ker := by
  intro c hc
  rw [MonoidHom.mem_ker, thetaMap_eq_one_iff]
  refine ⟨secImg_mono (conjClosure_le_conjClosure_U hIU le_rfl) c.2, ?_⟩
  show (c : GtOf V₁) ∈ Subgroup.centralizer (tildeOf V₁ (conjClosure K T) : Set (GtOf V₁))
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  obtain ⟨k₁, hk₁, rfl⟩ := mem_secImg.mp hs
  have hkH : (k₁ : G) ∈ H := h.K₀_le_H hk₁
  have ha : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨(k₁ : G), hkH⟩ ∈
      autIH V₁ I H (conjClosure K T) := by
    rw [autIH_eq_map h h.K₀_le_H]
    exact ⟨⟨k₁, hkH⟩, Subgroup.mem_subgroupOf.mpr hk₁, rfl⟩
  have hc2 : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨(k₁ : G), hkH⟩
      (c : ↥(tildeOf V₁ (conjClosure I H))) = c := hc.2 ⟨_, ha⟩
  have hc3 := congrArg (fun y : ↥(tildeOf V₁ (conjClosure I H)) => (y : GtOf V₁)) hc2
  simp only [actH_apply_coe] at hc3
  calc secMk (Subgroup.normalizer (V₁ : Set G)) V₁ k₁ * (c : GtOf V₁)
      = secMk (Subgroup.normalizer (V₁ : Set G)) V₁ k₁ * (c : GtOf V₁) *
          (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ k₁)⁻¹ *
          secMk (Subgroup.normalizer (V₁ : Set G)) V₁ k₁ := by group
    _ = (c : GtOf V₁) * secMk (Subgroup.normalizer (V₁ : Set G)) V₁ k₁ := by
      rw [hc3]

@[expose] noncomputable def thetaB [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (W : Subgroup ↥(tildeOf V₁ (conjClosure I H))) :
    (↥(tildeOf V₁ (conjClosure I H)) ⧸ modFix (autIH V₁ I H (conjClosure K T)) W) →*
      GhOf V₁ (conjClosure Vp H) (conjClosure K T) :=
  QuotientGroup.lift _ (thetaMap h hIU) (modFix_le_ker_thetaMap h hIU W)

theorem thetaB_mk [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (W : Subgroup ↥(tildeOf V₁ (conjClosure I H))) (u : ↥(tildeOf V₁ (conjClosure I H))) :
    thetaB h hIU W (QuotientGroup.mk u) = thetaMap h hIU u := rfl

theorem thetaB_hact [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (W : Subgroup ↥(tildeOf V₁ (conjClosure I H)))
    (a : ↥(autIH V₁ I H (conjClosure K T))) :
    ∃ kb ∈ hat' V₁ Vp H K T (conjClosure K T),
      ∀ q : ↥(tildeOf V₁ (conjClosure I H)) ⧸ modFix (autIH V₁ I H (conjClosure K T)) W,
        thetaB h hIU W (a • q) = kb * thetaB h hIU W q * kb⁻¹ := by
  obtain ⟨x, hx, hxa⟩ : (a : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈
      ((conjClosure K T).subgroupOf H).map
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
    rw [← autIH_eq_map h h.K₀_le_H]
    exact a.2
  have hx' : (x : G) ∈ conjClosure K T := Subgroup.mem_subgroupOf.mp hx
  refine ⟨kbarOf h x.2, kbarOf_mem_hat h hx', fun q => ?_⟩
  refine QuotientGroup.induction_on q fun u => ?_
  rw [XMod.smul_quotMk, thetaB_mk, thetaB_mk]
  have : (a : MulAut ↥(tildeOf V₁ (conjClosure I H))) u =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x u := by rw [← hxa]
  show thetaMap h hIU ((a : MulAut ↥(tildeOf V₁ (conjClosure I H))) u) = _
  rw [this]
  exact thetaMap_actH h hIU x.2 u

theorem thetaB_hact' [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (W : Subgroup ↥(tildeOf V₁ (conjClosure I H))) :
    ∀ kb ∈ hat' V₁ Vp H K T (conjClosure K T), ∃ a : ↥(autIH V₁ I H (conjClosure K T)),
      ∀ q : ↥(tildeOf V₁ (conjClosure I H)) ⧸ modFix (autIH V₁ I H (conjClosure K T)) W,
        thetaB h hIU W (a • q) = kb * thetaB h hIU W q * kb⁻¹ := by
  intro kb hkb
  obtain ⟨z, hz, rfl⟩ := mem_secImg.mp hkb
  obtain ⟨k₁, hk₁, hk₁z⟩ := mem_secImg.mp hz
  have hkH : (k₁ : G) ∈ H := h.K₀_le_H hk₁
  have hmem : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨(k₁ : G), hkH⟩ ∈
      autIH V₁ I H (conjClosure K T) := by
    rw [autIH_eq_map h h.K₀_le_H]
    exact ⟨⟨k₁, hkH⟩, Subgroup.mem_subgroupOf.mpr hk₁, rfl⟩
  refine ⟨⟨_, hmem⟩, fun q => ?_⟩
  refine QuotientGroup.induction_on q fun u => ?_
  rw [XMod.smul_quotMk, thetaB_mk, thetaB_mk]
  have e : kbarOf h hkH = secMk _ _ z := by
    unfold kbarOf
    congr 1
    apply Subtype.ext
    exact hk₁z
  show thetaMap h hIU (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨(k₁ : G), hkH⟩ u) = _
  rw [thetaMap_actH h hIU hkH u, e]

theorem thetaB_injOn [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (W : Subgroup ↥(tildeOf V₁ (conjClosure I H))) :
    ∀ x ∈ tilde (autIH V₁ I H (conjClosure K T)) W W,
      ∀ y ∈ tilde (autIH V₁ I H (conjClosure K T)) W W,
        thetaB h hIU W x = thetaB h hIU W y → x = y := by
  have hinj : ∀ x ∈ tilde (autIH V₁ I H (conjClosure K T)) W W, thetaB h hIU W x = 1 → x = 1 := by
    intro x hx h1
    obtain ⟨w, hw, rfl⟩ := mem_tilde_iff.mp hx
    have h2 : thetaMap h hIU w = 1 := h1
    rw [thetaMap_eq_one_iff] at h2
    have hwfix : w ∈ modFix (autIH V₁ I H (conjClosure K T)) W := by
      refine ⟨hw, fun a => ?_⟩
      obtain ⟨x, hx, hxa⟩ : (a : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈
          ((conjClosure K T).subgroupOf H).map
            (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
        rw [← autIH_eq_map h h.K₀_le_H]
        exact a.2
      have hx' : (x : G) ∈ conjClosure K T := Subgroup.mem_subgroupOf.mp hx
      show (a : MulAut ↥(tildeOf V₁ (conjClosure I H))) w = w
      rw [← hxa]
      apply Subtype.ext
      rw [actH_apply_coe]
      have hcomm := Subgroup.mem_centralizer_iff.mp h2.2
        (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, h.H_le_normalizer_V₁ x.2⟩)
        (secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
          (X := conjClosure K T) (x := ⟨x, h.H_le_normalizer_V₁ x.2⟩) hx')
      calc secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, h.H_le_normalizer_V₁ x.2⟩ *
            (w : GtOf V₁) * (secMk (Subgroup.normalizer (V₁ : Set G)) V₁
              ⟨x, h.H_le_normalizer_V₁ x.2⟩)⁻¹
          = (w : GtOf V₁) * secMk (Subgroup.normalizer (V₁ : Set G)) V₁
              ⟨x, h.H_le_normalizer_V₁ x.2⟩ * (secMk (Subgroup.normalizer (V₁ : Set G)) V₁
              ⟨x, h.H_le_normalizer_V₁ x.2⟩)⁻¹ := by rw [hcomm]
        _ = (w : GtOf V₁) := by group
    exact (QuotientGroup.eq_one_iff w).2 hwfix
  intro x hx y hy hxy
  have : x * y⁻¹ = 1 := hinj _
    ((tilde (autIH V₁ I H (conjClosure K T)) W W).mul_mem hx
      ((tilde (autIH V₁ I H (conjClosure K T)) W W).inv_mem hy))
    (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
  exact mul_inv_eq_one.mp this

theorem map_tilde_thetaB [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (W J : Subgroup ↥(tildeOf V₁ (conjClosure I H))) :
    (tilde (autIH V₁ I H (conjClosure K T)) W J).map (thetaB h hIU W) = J.map (thetaMap h hIU) := by
  unfold tilde
  rw [Subgroup.map_map]
  rfl

noncomputable abbrev wOf (V₁ I H T : Subgroup G) [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] :
    Subgroup ↥(tildeOf V₁ (conjClosure I H)) :=
  orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)

theorem wOf_eq [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) :
    wOf V₁ I H T = subM V₁ (conjClosure I H) (conjClosure I T) := by
  apply le_antisymm
  · show (⨆ t ∈ autIH V₁ I H T, (subM V₁ (conjClosure I H) I).map t.toMonoidHom) ≤ _
    refine iSup₂_le fun t ht => ?_
    rw [autIH_eq_map h h.T_le_H] at ht
    obtain ⟨x, hx, rfl⟩ := ht
    have hxT : (x : G) ∈ T := Subgroup.mem_subgroupOf.mp hx
    rw [map_actH_subM h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
      (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) x]
    intro w hw
    refine secImg_mono (fun y hy => ?_) (mem_subM_iff.mp hw)
    have := mem_conjClosure hxT (mem_conjSub.mp hy)
    have e : (x : G) * ((x : G)⁻¹ * y * (x : G)) * (x : G)⁻¹ = y := by group
    rwa [e] at this
  · have := subM_conjClosure_le_orbSup h.H_le_normalizer_V₁
      (h.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) h.T_le_H hV₁I
    show _ ≤ orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)
    rw [autIH_eq_map h h.T_le_H]
    exact this

theorem isModInv_wOf [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K)
    (hIinv : IsModInv (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)) :
    IsModInv (autIH V₁ I H (conjClosure K T)) (wOf V₁ I H T) := by
  show IsModInv _ (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I))
  rw [orbSup_eq_biSup_smul]
  exact XMod.isInv_iSup fun y => XMod.isInv_iSup fun hy =>
    isModInv_smul (autIH_T_le_normalizer h I hy) hIinv

theorem hat_IT_eq [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) :
    hat' V₁ Vp H K T (conjClosure I T) =
      (tilde (autIH V₁ I H (conjClosure K T)) (wOf V₁ I H T) (wOf V₁ I H T)).map
        (thetaB h hIU (wOf V₁ I H T)) := by
  rw [map_tilde_thetaB, hat_eq_map_theta h hIU (conjClosure_mono le_rfl h.T_le_H),
    ← wOf_eq h hV₁I hIU]

theorem hat_I_eq [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    hat' V₁ Vp H K T I =
      (tilde (autIH V₁ I H (conjClosure K T)) (wOf V₁ I H T) (subM V₁ (conjClosure I H) I)).map
        (thetaB h hIU (wOf V₁ I H T)) := by
  rw [map_tilde_thetaB, hat_eq_map_theta h hIU (le_conjClosure I H)]

theorem hom_of_isIrrPlusTildeT (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTildeT h hIU) :
    HomHat V₁ Vp H K T I := by
  unfold HomHat
  intro S hSle hKS hiso
  haveI := factElem h hIU
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  obtain ⟨hIP, hHC⟩ := hirr'
  set A := autIH V₁ I H (conjClosure K T) with hA
  set Itil := subM V₁ (conjClosure I H) I with hItil
  set W := wOf V₁ I H T with hW
  set θb := thetaB h hIU W with hθb
  have hact := thetaB_hact h hIU W
  have hinj' := thetaB_injOn h hIU W
  have hIinv : IsModInv A Itil := hIP.2.1
  have hWinv : IsModInv A W := isModInv_wOf h hIinv
  have hIW : Itil ≤ W := hIP.1
  have hWsup : W = ⨆ y ∈ autIH V₁ I H T, y • Itil := orbSup_eq_biSup_smul _ Itil
  have hatIT := hat_IT_eq h hV₁I hIU
  have hatI := hat_I_eq h hIU
  let S₀ : Subgroup (↥(tildeOf V₁ (conjClosure I H)) ⧸ modFix A W) :=
    S.comap θb ⊓ tilde A W W
  have hS₀map : S₀.map θb = S := by
    ext s'
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq.1
    · intro hs
      have hs' : s' ∈ (tilde A W W).map θb := by rw [← hatIT]; exact hSle hs
      obtain ⟨q, hq, rfl⟩ := hs'
      exact ⟨q, ⟨hs, hq⟩, rfl⟩
  have hS₀inv : XMod.IsInv ↥A S₀ := by
    intro a q hq
    obtain ⟨kb, hkb, hk⟩ := hact a
    refine ⟨?_, isInv_tilde (W := W) hWinv a q hq.2⟩
    show θb (a • q) ∈ S
    rw [hk q]
    exact (Subgroup.mem_normalizer_iff.mp (hKS hkb) _).mp hq.1
  obtain ⟨hKS', hKI', φ, hφ⟩ := hiso
  obtain ⟨e₁, he₁⟩ := exists_equivMap_of_injOn θb hinj' (L := S₀) (inf_le_right : S₀ ≤ tilde A W W)
  obtain ⟨e₂, he₂⟩ := exists_equivMap_of_injOn θb hinj' (L := tilde A W Itil)
    (tilde_mono hIW : tilde A W Itil ≤ tilde A W W)
  let φ₀ : ↥S₀ ≃* ↥(tilde A W Itil) :=
    e₁.trans ((MulEquiv.subgroupCongr hS₀map).trans (φ.trans
      ((MulEquiv.subgroupCongr hatI).trans e₂.symm)))
  have hφ₀ : ∀ l : ↥S₀, θb ((φ₀ l : ↥(tilde A W Itil)) : _) =
      ((φ (MulEquiv.subgroupCongr hS₀map (e₁ l)) : ↥(hat' V₁ Vp H K T I)) :
        GhOf V₁ (conjClosure Vp H) (conjClosure K T)) := by
    intro l
    have h1 := he₂ (e₂.symm (MulEquiv.subgroupCongr hatI (φ (MulEquiv.subgroupCongr hS₀map (e₁ l)))))
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hφ₀' : ∀ l : ↥S₀, ((MulEquiv.subgroupCongr hS₀map (e₁ l) : ↥S) :
      GhOf V₁ (conjClosure Vp H) (conjClosure K T)) = θb (l : _) := fun l => he₁ l
  have hIsoS₀ : XMod.Iso ↥A S₀ (tilde A W Itil) := by
    refine ⟨φ₀, fun a l l' hll' => ?_⟩
    obtain ⟨kb, hkb, hk⟩ := hact a
    have hθl' : θb (l' : _) = kb * θb (l : _) * kb⁻¹ := by rw [← hll', hk]
    have hmul : ((MulEquiv.subgroupCongr hS₀map (e₁ l') : ↥S) :
        GhOf V₁ (conjClosure Vp H) (conjClosure K T)) =
        kb * ((MulEquiv.subgroupCongr hS₀map (e₁ l) : ↥S) :
          GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * kb⁻¹ := by
      rw [hφ₀', hφ₀', hθl']
    have hφmul := hφ kb hkb _ _ hmul
    apply hinj'
    · exact isInv_tilde (W := W) hWinv a _ (tilde_mono hIW (φ₀ l).2)
    · exact tilde_mono hIW (φ₀ l').2
    · rw [hk, hφ₀, hφ₀, hφmul]
  have hS₀irr : XMod.IsIrr ↥A S₀ := isIrr_of_iso (isIrr_tilde hIP).1 hS₀inv hIsoS₀
  have hHC3 := hHC.2.2 S₀ ?_ hS₀irr hIsoS₀
  · intro s' hs
    rw [← hS₀map] at hs
    obtain ⟨q, hq, rfl⟩ := hs
    rw [hatI]
    exact ⟨q, hHC3 hq, rfl⟩
  · rw [← hWsup]
    exact inf_le_right

theorem commOf_eq_of_tildeOf_commutator [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G))
    (hcomm : tildeOf V₁ ⁅I, conjClosure K T⁆ = tildeOf V₁ I) :
    XMod.commOf ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I) =
      subM V₁ (conjClosure I H) I := by
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hinv := isInv_subM_of_normalizer h.H_le_normalizer_V₁ hIHN hIH h.K₀_le_H hV₁I
    (le_conjClosure I H) hKI
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro c ⟨a, l, hl, rfl⟩
    exact Subgroup.mul_mem _ (hinv a l hl) (Subgroup.inv_mem _ hl)
  · intro w hw
    obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde w
    have hw' : w = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
    have haI : (a : G) ∈ I := (modMk_mem_subM_iff hIHN hV₁I haIH).mp (hw' ▸ hw)
    have hmem : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ a ∈ tildeOf V₁ ⁅I, conjClosure K T⁆ := by
      rw [hcomm]; exact secMk_mem_secImg haI
    obtain ⟨c, hc, hca⟩ := mem_secImg.mp hmem
    have key : ∀ x ∈ ⁅I, conjClosure K T⁆, ∃ hx : x ∈ conjClosure I H,
        modMk hIHN x hx ∈ XMod.commOf ↥(autIH V₁ I H (conjClosure K T))
          (subM V₁ (conjClosure I H) I) := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, hi, k, hk, rfl⟩ := hx
        have hkH : k ∈ H := h.K₀_le_H hk
        have hiIH : i ∈ conjClosure I H := le_conjClosure I H hi
        have hkiIH : k * i * k⁻¹ ∈ conjClosure I H :=
          (Subgroup.mem_normalizer_iff.mp (hIH hkH) i).mp hiIH
        have hxIH : ⁅i, k⁆ ∈ conjClosure I H := by
          have e : ⁅i, k⁆ = (k * i * k⁻¹ * i⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
          rw [e]
          exact (conjClosure I H).inv_mem ((conjClosure I H).mul_mem hkiIH
            ((conjClosure I H).inv_mem hiIH))
        refine ⟨hxIH, ?_⟩
        have ha : actH h.H_le_normalizer_V₁ hIH ⟨k, hkH⟩ ∈ autIH V₁ I H (conjClosure K T) := by
          rw [autIH_eq_map h h.K₀_le_H]
          exact ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
        have hil : modMk hIHN i hiIH ∈ subM V₁ (conjClosure I H) I :=
          (modMk_mem_subM_iff hIHN hV₁I hiIH).mpr hi
        have hgen : (actH h.H_le_normalizer_V₁ hIH ⟨k, hkH⟩ (modMk hIHN i hiIH)) *
            (modMk hIHN i hiIH)⁻¹ ∈ XMod.commOf ↥(autIH V₁ I H (conjClosure K T))
              (subM V₁ (conjClosure I H) I) :=
          Subgroup.subset_closure ⟨⟨_, ha⟩, _, hil, rfl⟩
        have e : modMk hIHN ⁅i, k⁆ hxIH =
            ((actH h.H_le_normalizer_V₁ hIH ⟨k, hkH⟩ (modMk hIHN i hiIH)) *
              (modMk hIHN i hiIH)⁻¹)⁻¹ := by
          rw [actH_modMk h.H_le_normalizer_V₁ hIHN hIH ⟨k, hkH⟩ hiIH, ← modMk_inv hIHN hiIH,
            ← modMk_mul hIHN hkiIH ((conjClosure I H).inv_mem hiIH),
            ← modMk_inv hIHN ((conjClosure I H).mul_mem hkiIH ((conjClosure I H).inv_mem hiIH))]
          congr 1
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.inv_mem _ hgen
      | one => exact ⟨(conjClosure I H).one_mem, by rw [modMk_one]; exact Subgroup.one_mem _⟩
      | mul x y hx hy ihx ihy =>
        obtain ⟨hxIH, hxm⟩ := ihx
        obtain ⟨hyIH, hym⟩ := ihy
        refine ⟨(conjClosure I H).mul_mem hxIH hyIH, ?_⟩
        rw [modMk_mul hIHN hxIH hyIH]
        exact Subgroup.mul_mem _ hxm hym
      | inv x hx ih =>
        obtain ⟨hxIH, hxm⟩ := ih
        refine ⟨(conjClosure I H).inv_mem hxIH, ?_⟩
        rw [modMk_inv hIHN hxIH]
        exact Subgroup.inv_mem _ hxm
    obtain ⟨hcIH, hcm⟩ := key (c : G) hc
    have hcw : modMk hIHN (c : G) hcIH = w := by
      rw [hw']
      exact Subtype.ext hca
    rw [← hcw]
    exact hcm

theorem isIrrPlus_subM_of_isIrrPlusTilde [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hIrr : IsIrrPlusTilde V₁ (conjClosure K T) I) :
    XMod.IsIrrPlus ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I) := by
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hinv := isInv_subM_of_normalizer h.H_le_normalizer_V₁ hIHN hIH h.K₀_le_H hV₁I
    (le_conjClosure I H) hIrr.1
  refine ⟨hinv, commOf_eq_of_tildeOf_commutator h hV₁I hIU hIrr.1 hIrr.2.1, ?_⟩
  have hC := subM_centralizerMod h.H_le_normalizer_V₁ hIHN hIH h.K₀_le_H hV₁I (le_conjClosure I H)
  rw [← hC]
  have hV₁C := le_centralizerMod (V₁ := V₁) (H := H) h.H_le_normalizer_V₁ h.K₀_le_H hV₁I
  have hCI : centralizerMod V₁ I (conjClosure K T) ≤ conjClosure I H :=
    (centralizerMod_le_left _ _ _).trans (le_conjClosure I H)
  refine ⟨?_, fun J hJinv hCJ hJI => ?_⟩
  · refine lt_of_le_of_ne ((subM_le_iff hIHN hV₁C hV₁I hCI).2 (centralizerMod_le_left _ _ _))
      fun heq => ?_
    have := subM_inj hIHN hV₁C hV₁I hCI (le_conjClosure I H) heq
    exact (ne_of_lt hIrr.2.2.1) this
  · obtain ⟨J', hV₁J', hJ'IH, rfl⟩ := exists_subM_eq (le_trans hV₁I (le_conjClosure I H)) J
    have hJ'I : J' ≤ I := (subM_le_iff hIHN hV₁J' hV₁I hJ'IH).1 hJI
    have hCJ' : centralizerMod V₁ I (conjClosure K T) ≤ J' :=
      (subM_le_iff hIHN hV₁C hV₁J' hCI).1 hCJ
    have hKJ : conjClosure K T ≤ Subgroup.normalizer (J' : Set G) := by
      intro k hk
      have hkH : k ∈ H := h.K₀_le_H hk
      have hmem : actH h.H_le_normalizer_V₁ hIH ⟨k, hkH⟩ ∈ autIH V₁ I H (conjClosure K T) := by
        rw [autIH_eq_map h h.K₀_le_H]
        exact ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      have hstab : actH h.H_le_normalizer_V₁ hIH ⟨k, hkH⟩ ∈ stabSub (subM V₁ (conjClosure I H) J') := by
        intro u
        constructor
        · intro hu
          have := hJinv ⟨(actH h.H_le_normalizer_V₁ hIH ⟨k, hkH⟩)⁻¹, inv_mem hmem⟩ _ hu
          simpa using this
        · intro hu
          exact hJinv ⟨actH h.H_le_normalizer_V₁ hIH ⟨k, hkH⟩, hmem⟩ u hu
      exact (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ hIHN hIH hV₁J' hJ'IH ⟨k, hkH⟩).mp hstab
    rcases hIrr.2.2.2 J' hV₁J' hJ'I hKJ hCJ' with hJ | hJ
    · exact Or.inl (by rw [hJ])
    · exact Or.inr (by rw [hJ])

theorem hat_le_normalizer_map_thetaB [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (W : Subgroup ↥(tildeOf V₁ (conjClosure I H)))
    {P : Subgroup (↥(tildeOf V₁ (conjClosure I H)) ⧸ modFix (autIH V₁ I H (conjClosure K T)) W)}
    (hP : XMod.IsInv ↥(autIH V₁ I H (conjClosure K T)) P) :
    hat' V₁ Vp H K T (conjClosure K T) ≤
      Subgroup.normalizer ((P.map (thetaB h hIU W) : Subgroup (GhOf V₁ (conjClosure Vp H)
        (conjClosure K T))) : Set (GhOf V₁ (conjClosure Vp H) (conjClosure K T))) := by
  have hconj : ∀ kb ∈ hat' V₁ Vp H K T (conjClosure K T), ∀ s ∈ P.map (thetaB h hIU W),
      kb * s * kb⁻¹ ∈ P.map (thetaB h hIU W) := by
    intro kb hkb s hs
    obtain ⟨a, hk⟩ := thetaB_hact' h hIU W kb hkb
    obtain ⟨q, hq, rfl⟩ := hs
    rw [← hk q]
    exact ⟨a • q, hP a q hq, rfl⟩
  intro kb hkb
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨fun hs => hconj kb hkb s hs, fun hs => ?_⟩
  have := hconj kb⁻¹ ((hat' V₁ Vp H K T (conjClosure K T)).inv_mem hkb) _ hs
  simpa [mul_assoc] using this

theorem isIrrPlusTildeT_of_homHat (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) (hIrr : IsIrrPlusTilde V₁ (conjClosure K T) I)
    (hhom : HomHat V₁ Vp H K T I) : IsIrrPlusTildeT h hIU := by
  haveI := factElem h hIU
  have hIP : XMod.IsIrrPlus ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I) :=
    isIrrPlus_subM_of_isIrrPlusTilde h hV₁I hIU hIrr
  show subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
    (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T)
  set A := autIH V₁ I H (conjClosure K T) with hA
  set Itil := subM V₁ (conjClosure I H) I with hItil
  set W := wOf V₁ I H T with hW
  have hIW : Itil ≤ W := le_orbSup _ _
  have hWsup : W = ⨆ y ∈ autIH V₁ I H T, y • Itil := orbSup_eq_biSup_smul _ Itil
  have hIPW : Itil ∈ IrrPlus A W := ⟨hIW, hIP⟩
  refine ⟨hIPW, ?_⟩
  rw [← hWsup]
  refine ⟨(isIrr_tilde hIPW).1, tilde_mono hIW, fun L' hL'le hL'irr hL'iso => ?_⟩
  have hinj' := thetaB_injOn h hIU W
  have hatIT := hat_IT_eq h hV₁I hIU
  have hatI := hat_I_eq h hIU
  set θb := thetaB h hIU W with hθb
  have hSle : L'.map θb ≤ hat' V₁ Vp H K T (conjClosure I T) := by
    rw [hatIT]; exact Subgroup.map_mono hL'le
  have hKS := hat_le_normalizer_map_thetaB h hIU W hL'irr.1
  have hKIhat : hat' V₁ Vp H K T (conjClosure K T) ≤
      Subgroup.normalizer ((hat' V₁ Vp H K T I : Subgroup (GhOf V₁ (conjClosure Vp H)
        (conjClosure K T))) : Set (GhOf V₁ (conjClosure Vp H) (conjClosure K T))) := by
    rw [hatI]
    exact hat_le_normalizer_map_thetaB h hIU W (isInv_tilde (W := W) hIP.1)
  obtain ⟨φm, hφm⟩ := hL'iso
  obtain ⟨e₁, he₁⟩ := exists_equivMap_of_injOn θb hinj' (L := L') hL'le
  obtain ⟨e₂, he₂⟩ := exists_equivMap_of_injOn θb hinj' (L := tilde A W Itil)
    (tilde_mono hIW : tilde A W Itil ≤ tilde A W W)
  let φ : ↥(L'.map θb) ≃* ↥(hat' V₁ Vp H K T I) :=
    e₁.symm.trans (φm.trans (e₂.trans (MulEquiv.subgroupCongr hatI.symm)))
  have hφval : ∀ s : ↥(L'.map θb), ((φ s : ↥(hat' V₁ Vp H K T I)) :
      GhOf V₁ (conjClosure Vp H) (conjClosure K T)) =
      θb ((φm (e₁.symm s) : ↥(tilde A W Itil)) : _) := fun s => he₂ _
  have hφeq : ∀ k ∈ hat' V₁ Vp H K T (conjClosure K T), ∀ a a' : ↥(L'.map θb),
      (a' : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) = k * a * k⁻¹ →
      ((φ a' : ↥(hat' V₁ Vp H K T I)) : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) =
        k * ((φ a : ↥(hat' V₁ Vp H K T I)) : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) * k⁻¹ := by
    intro k hk a a' haa
    obtain ⟨α, hα⟩ := thetaB_hact' h hIU W k hk
    have hal : (a : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) = θb ((e₁.symm a : ↥L') : _) := by
      have := he₁ (e₁.symm a)
      rw [MulEquiv.apply_symm_apply] at this
      exact this
    have hal' : (a' : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) =
        θb ((e₁.symm a' : ↥L') : _) := by
      have := he₁ (e₁.symm a')
      rw [MulEquiv.apply_symm_apply] at this
      exact this
    have hαl : α • ((e₁.symm a : ↥L') :
        ↥(tildeOf V₁ (conjClosure I H)) ⧸ modFix A W) =
        ((e₁.symm a' : ↥L') : ↥(tildeOf V₁ (conjClosure I H)) ⧸ modFix A W) := by
      apply hinj'
      · exact hL'le (hL'irr.1 α _ (e₁.symm a).2)
      · exact hL'le (e₁.symm a').2
      · rw [hα, ← hal, ← hal', haa]
    have h2 := hφm α (e₁.symm a) (e₁.symm a') hαl
    rw [hφval a', hφval a, ← h2, hα]
  unfold HomHat at hhom
  have hS := hhom (L'.map θb) hSle hKS ⟨hKS, hKIhat, φ, hφeq⟩
  intro q hq
  have h1 : θb q ∈ L'.map θb := ⟨q, hq, rfl⟩
  have h2 := hS h1
  rw [hatI] at h2
  obtain ⟨q'', hq'', hqq⟩ := h2
  have h3 : q'' = q := hinj' q'' (tilde_mono hIW hq'') q (hL'le hq) hqq
  rw [← h3]
  exact hq''

end ExistsI

end Dict

end CFSG.Quasithin.RonanF918
