module

public import CFSG.Quasithin.Background.RonanF918FiveDL
public import CFSG.Quasithin.Background.F918C8

public section

namespace CFSG.Quasithin.RonanF918

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.RonanD321.SL2Model
open scoped Pointwise commutatorElement Matrix

structure MultDataU {G : Type} [Group G] (V₁ Vp H K T I : Subgroup G) (F : Type) [Field F] where
  coordinates : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆) →*
    Multiplicative (Matrix (Fin 2) (Fin 2) F)
  coordinates_surjective : Function.Surjective coordinates
  coordinates_kernel : ∀ vector, coordinates vector = 1 ↔
    (vector : G) ∈ centralizerMod V₁ (V₁ ⊔ ⁅conjClosure I H, K⁆) (conjClosure K T)
  markedComponent : ↥K →* ↥(StatedSL 2 F)
  markedComponent_surjective : Function.Surjective markedComponent
  markedComponent_kernel : ∀ element, markedComponent element = 1 ↔
    (element : G) ∈ pCoreOf 2 H
  component_equivariance : ∀ element : ↥K, ∀ vector transported : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆),
    (transported : G) = element * vector * element⁻¹ →
    coordinates transported = Multiplicative.ofAdd
      (((markedComponent element : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        Multiplicative.toAdd (coordinates vector))
  centralizer_normalizes : centralizerMod (pCoreOf 2 H) H (conjClosure K T) ≤
    Subgroup.normalizer ((V₁ ⊔ ⁅conjClosure I H, K⁆ : Subgroup G) : Set G)
  normalizer_normalizes : H ⊓ Subgroup.normalizer (K : Set G) ≤
    Subgroup.normalizer ((V₁ ⊔ ⁅conjClosure I H, K⁆ : Subgroup G) : Set G)
  multiplicity : ↥(centralizerMod (pCoreOf 2 H) H (conjClosure K T)) →*
    Matrix.GeneralLinearGroup (Fin 2) F
  multiplicity_equivariance :
    ∀ element : ↥(centralizerMod (pCoreOf 2 H) H (conjClosure K T)),
      ∀ vector transported : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆),
        (transported : G) = element * vector * element⁻¹ →
        coordinates transported = multOpU F (multiplicity element) (coordinates vector)
  multiplicity_kernel :
    ∀ element : ↥(centralizerMod (pCoreOf 2 H) H (conjClosure K T)),
      multiplicity element = 1 ↔
        ∀ vector transported : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆),
          (transported : G) = element * vector * element⁻¹ →
            coordinates transported = coordinates vector
  normalizerAction : ↥(H ⊓ Subgroup.normalizer (K : Set G)) →*
    MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F))
  normalizer_equivariance : ∀ element : ↥(H ⊓ Subgroup.normalizer (K : Set G)),
    ∀ vector transported : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆),
      (transported : G) = element * vector * element⁻¹ →
        coordinates transported = normalizerAction element (coordinates vector)
  fieldAction : ↥(H ⊓ Subgroup.normalizer (K : Set G)) →* (F ≃+* F)
  semilinear : ∀ element scalar matrix,
    normalizerAction element (Multiplicative.ofAdd (scalar • matrix)) =
      Multiplicative.ofAdd (fieldAction element scalar •
        Multiplicative.toAdd (normalizerAction element (Multiplicative.ofAdd matrix)))
  commutant_transport : ∀ element : ↥(H ⊓ Subgroup.normalizer (K : Set G)),
    ∀ matrix : Matrix.GeneralLinearGroup (Fin 2) F,
      ∃ transported : Matrix.GeneralLinearGroup (Fin 2) F,
        ∀ vector, normalizerAction element (multOpU F matrix vector) =
          multOpU F transported (normalizerAction element vector)
  actual_image_transport : ∀ element : ↥(H ⊓ Subgroup.normalizer (K : Set G)),
    ∀ matrix ∈ multiplicity.range,
      ∃ transported ∈ multiplicity.range,
        ∀ vector, normalizerAction element (multOpU F matrix vector) =
          multOpU F transported (normalizerAction element vector)
  full_commutant : ∀ operator : MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F)),
    (∀ (scalar : F) (matrix : Matrix (Fin 2) (Fin 2) F),
      operator (Multiplicative.ofAdd (scalar • matrix)) =
      Multiplicative.ofAdd (scalar • Multiplicative.toAdd (operator (Multiplicative.ofAdd matrix)))) →
    (∀ element : ↥(StatedSL 2 F), ∀ matrix,
      operator (Multiplicative.ofAdd
        (((element : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * matrix)) =
      Multiplicative.ofAdd
        (((element : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Multiplicative.toAdd (operator (Multiplicative.ofAdd matrix)))) →
    ∃ uniqueMatrix : Matrix.GeneralLinearGroup (Fin 2) F,
      (∀ vector, operator vector = multOpU F uniqueMatrix vector) ∧
      ∀ otherMatrix, (∀ vector, operator vector = multOpU F otherMatrix vector) →
        otherMatrix = uniqueMatrix

@[expose] def MultCasesU {G : Type} [Group G] {V₁ Vp H K T I : Subgroup G} {F : Type} [Field F]
    (data : MultDataU V₁ Vp H K T I F) : Prop :=
  (∃ line : Submodule F (Fin 2 → F), multLineFixedU F data.multiplicity.range line ∧
    ∃ J : Subgroup G, V₁ ≤ J ∧ J ≤ V₁ ⊔ ⁅conjClosure I H, K⁆ ∧ IsIrrPlusTilde V₁ K J ∧
      J = V₁ ⊔ ⁅((multLineModuleU F line).comap data.coordinates).map
        (V₁ ⊔ ⁅conjClosure I H, K⁆).subtype, K⁆ ∧
      centralizerMod (pCoreOf 2 H) H (conjClosure K T) ≤ Subgroup.normalizer (J : Set G) ∧
      ∀ element : ↥(H ⊓ Subgroup.normalizer (K : Set G)),
        (∀ vector ∈ multLineModuleU F line,
          data.normalizerAction element vector ∈ multLineModuleU F line) →
        (element : G) ∈ Subgroup.normalizer (J : Set G)) ∨
  (∀ line : Submodule F (Fin 2 → F), Module.finrank F line = 1 →
    ¬ multLineFixedU F data.multiplicity.range line)

section Coordinates

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

omit [Finite G] in
theorem commutator_le_conjClosure_K (h : HypF918 T V L V₁ Vp H K) :
    ⁅conjClosure I H, K⁆ ≤ conjClosure I H := by
  rw [Subgroup.commutator_comm]
  exact Subgroup.le_normalizer_iff_commutator_le_right.mp
    ((le_of_mem_cComp h.K_cComp).trans (le_normalizer_conjClosure I H))

omit [Finite G] in
theorem Jg_le_conjClosure (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I) :
    V₁ ⊔ ⁅conjClosure I H, K⁆ ≤ conjClosure I H :=
  sup_le (hV₁I.trans (le_conjClosure I H)) (commutator_le_conjClosure_K h)

variable [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem subM_Jg_eq_commV (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    subM V₁ (conjClosure I H) (V₁ ⊔ ⁅conjClosure I H, K⁆) = commV (autIH V₁ I H K) := by
  rw [commV_autIH_eq_subM h hIU (le_of_mem_cComp h.K_cComp)]
  unfold subM
  rw [sup_comm, tildeOf_sup_self ((commutator_le_conjClosure_K h).trans
    (h.conjClosure_le_normalizer_V₁ hIU))]

theorem modMk_mem_commV_iff (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    {x : G} (hx : x ∈ conjClosure I H) :
    modMk (h.conjClosure_le_normalizer_V₁ hIU) x hx ∈ commV (autIH V₁ I H K) ↔
      x ∈ V₁ ⊔ ⁅conjClosure I H, K⁆ := by
  rw [← subM_Jg_eq_commV h hIU]
  exact modMk_mem_subM_iff (h.conjClosure_le_normalizer_V₁ hIU) le_sup_left hx

theorem Jg_le_normalizer (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I) :
    V₁ ⊔ ⁅conjClosure I H, K⁆ ≤ Subgroup.normalizer (V₁ : Set G) :=
  (Jg_le_conjClosure h hV₁I).trans (h.conjClosure_le_normalizer_V₁ hIU)

@[expose] noncomputable def Jt (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hV₁I : V₁ ≤ I) :
    ↥(V₁ ⊔ ⁅conjClosure I H, K⁆) →* ↥(commV (autIH V₁ I H K)) :=
  (((secMk (Subgroup.normalizer (V₁ : Set G)) V₁).comp
      (Subgroup.inclusion (Jg_le_normalizer h hIU hV₁I))).codRestrict (tildeOf V₁ (conjClosure I H))
    (fun x => secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (X := conjClosure I H) (x := ⟨(x : G), Jg_le_normalizer h hIU hV₁I x.2⟩)
      (Jg_le_conjClosure h hV₁I x.2))).codRestrict (commV (autIH V₁ I H K))
    (fun x => (modMk_mem_commV_iff h hIU (Jg_le_conjClosure h hV₁I x.2)).mpr x.2)

theorem Jt_coe (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I)
    (x : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆)) :
    ((Jt h hIU hV₁I x : ↥(commV (autIH V₁ I H K))) : ↥(tildeOf V₁ (conjClosure I H))) =
      modMk (h.conjClosure_le_normalizer_V₁ hIU) (x : G) (Jg_le_conjClosure h hV₁I x.2) := rfl

theorem Jt_surjective (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hV₁I : V₁ ≤ I) : Function.Surjective (Jt h hIU hV₁I) := by
  intro u
  obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde (u : ↥(tildeOf V₁ (conjClosure I H)))
  have hw' : (u : ↥(tildeOf V₁ (conjClosure I H))) =
      modMk (h.conjClosure_le_normalizer_V₁ hIU) (a : G) haIH := Subtype.ext hau.symm
  have haJ : (a : G) ∈ V₁ ⊔ ⁅conjClosure I H, K⁆ :=
    (modMk_mem_commV_iff h hIU haIH).mp (by rw [← hw']; exact u.2)
  exact ⟨⟨a, haJ⟩, Subtype.ext hw'.symm⟩

theorem modMk_mem_fixV_iff (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I)
    {x : G} (hx : x ∈ V₁ ⊔ ⁅conjClosure I H, K⁆) :
    modMk (h.conjClosure_le_normalizer_V₁ hIU) x (Jg_le_conjClosure h hV₁I hx) ∈
        fixV (autIH V₁ I H (conjClosure K T)) ↔
      x ∈ centralizerMod V₁ (V₁ ⊔ ⁅conjClosure I H, K⁆) (conjClosure K T) := by
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hxIH := Jg_le_conjClosure h hV₁I hx
  have hV₁C := le_centralizerMod h.H_le_normalizer_V₁ h.K₀_le_H
    (le_sup_left : V₁ ≤ V₁ ⊔ ⁅conjClosure I H, K⁆)
  have hsub := subM_centralizerMod h.H_le_normalizer_V₁ hIHN hIH h.K₀_le_H
    (le_sup_left : V₁ ≤ V₁ ⊔ ⁅conjClosure I H, K⁆) (Jg_le_conjClosure h hV₁I)
  rw [← modMk_mem_subM_iff hIHN hV₁C hxIH, hsub]
  constructor
  · intro hfix
    refine ⟨(modMk_mem_subM_iff hIHN le_sup_left hxIH).mpr hx, fun a => ?_⟩
    exact hfix a a.2
  · rintro ⟨-, hfix⟩ a ha
    exact hfix ⟨a, ha⟩

omit [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] in
theorem modMk_congr {IH : Subgroup G} (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {a b : G}
    (hab : a = b) (ha : a ∈ IH) (hb : b ∈ IH) : modMk hIHN a ha = modMk hIHN b hb := by
  subst hab
  rfl

theorem actH_mem_NLM (h : HypF918 T V L V₁ Vp H K) {x : G} (hxH : x ∈ H)
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) :
    actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨x, hxH⟩ ∈
      NLM (autIH V₁ I H K) (autIH V₁ I H (conjClosure K T)) :=
  ⟨actH_mem_normalizer_autIH h (le_of_mem_cComp h.K_cComp) hxH hxK,
    actH_mem_normalizer_autIH h h.K₀_le_H hxH (h.K₀_normal hxH)⟩

@[expose] noncomputable def gHom (h : HypF918 T V L V₁ Vp H K) :
    ↥(H ⊓ Subgroup.normalizer (K : Set G)) →*
      ↥(NLM (autIH V₁ I H K) (autIH V₁ I H (conjClosure K T))) :=
  ((actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)).comp
    (Subgroup.inclusion (inf_le_left : H ⊓ Subgroup.normalizer (K : Set G) ≤ H))).codRestrict _
    (fun x => actH_mem_NLM h x.2.1 x.2.2)

theorem Jt_conj (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I) (x : ↥H)
    (v w : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆)) (hw : (w : G) = (x : G) * v * (x : G)⁻¹) :
    ((Jt h hIU hV₁I w : ↥(commV (autIH V₁ I H K))) : ↥(tildeOf V₁ (conjClosure I H))) =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x
        ((Jt h hIU hV₁I v : ↥(commV (autIH V₁ I H K))) : ↥(tildeOf V₁ (conjClosure I H))) := by
  rw [Jt_coe, Jt_coe, actH_modMk h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
    (le_normalizer_conjClosure I H) x (Jg_le_conjClosure h hV₁I v.2)]
  exact modMk_congr _ hw _ _

theorem autIH_K_le_K₀ (I : Subgroup G) (hKH : K ≤ H) (T : Subgroup G) :
    autIH V₁ I H K ≤ autIH V₁ I H (conjClosure K T) :=
  CFSG.Quasithin.AutOn.autOn_mono (secImg_mono (le_conjClosure K T))

theorem conj_mem_centralizerMod_K₀ (h : HypF918 T V L V₁ Vp H K) {x y : G} (hxH : x ∈ H)
    (hy : y ∈ centralizerMod (pCoreOf 2 H) H (conjClosure K T)) :
    x * y * x⁻¹ ∈ centralizerMod (pCoreOf 2 H) H (conjClosure K T) := by
  have hPH : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hyH : y ∈ H := centralizerMod_le_left _ _ _ hy
  refine ⟨H.mul_mem (H.mul_mem hxH hyH) (H.inv_mem hxH),
    hPH (H.mul_mem (H.mul_mem hxH hyH) (H.inv_mem hxH)), fun k hk => ?_⟩
  have hk' : x⁻¹ * k * x⁻¹⁻¹ ∈ conjClosure K T :=
    (Subgroup.mem_normalizer_iff.mp (h.K₀_normal (H.inv_mem hxH)) k).mp hk
  have h1 := hy.2.2 _ hk'
  have h2 : x * (y * (x⁻¹ * k * x⁻¹⁻¹) * y⁻¹ * (x⁻¹ * k * x⁻¹⁻¹)⁻¹) * x⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (hPH hxH) _).mp h1
  have e : x * y * x⁻¹ * k * (x * y * x⁻¹)⁻¹ * k⁻¹ =
      x * (y * (x⁻¹ * k * x⁻¹⁻¹) * y⁻¹ * (x⁻¹ * k * x⁻¹⁻¹)⁻¹) * x⁻¹ := by group
  rw [e]
  exact h2

variable [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem bq_Jt_conj (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I)
    {F : Type} [Field F] (D : CoordData (autIH V₁ I H K) (autIH V₁ I H (conjClosure K T)) F)
    (g : ↥(NLM (autIH V₁ I H K) (autIH V₁ I H (conjClosure K T)))) (x : ↥H)
    (hg : (g : MulAut ↥(tildeOf V₁ (conjClosure I H))) =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x)
    (v w : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆)) (hw : (w : G) = (x : G) * v * (x : G)⁻¹) :
    D.bq (Jt h hIU hV₁I w) = psi D g (D.bq (Jt h hIU hV₁I v)) := by
  rw [psi_apply, psi0_apply]
  congr 1
  apply Subtype.ext
  rw [gU_coe, hg]
  exact Jt_conj h hIU hV₁I x v w hw

omit [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] in
theorem mem_normalizer_sup' {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← A38.map_conj_eq_iff, Subgroup.map_sup, A38.map_conj_eq_iff.mpr hA, A38.map_conj_eq_iff.mpr hB]

omit [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] in
theorem N_le_normalizer_Jg (h : HypF918 T V L V₁ Vp H K) :
    H ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((V₁ ⊔ ⁅conjClosure I H, K⁆ : Subgroup G) : Set G) := by
  intro x hx
  have hxV₁ : x ∈ Subgroup.normalizer (V₁ : Set G) := h.H_le_normalizer_V₁ hx.1
  have hcomm : x ∈ Subgroup.normalizer ((⁅conjClosure I H, K⁆ : Subgroup G) : Set G) :=
    F9.le_normalizer_commutator_of_le (X := H ⊓ Subgroup.normalizer (K : Set G))
      (A := conjClosure I H) (B := K) (fun y hy => le_normalizer_conjClosure I H hy.1)
      (fun y hy => hy.2) hx
  exact mem_normalizer_sup' hxV₁ hcomm

theorem C_le_normalizer_Jg (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I)
    (hCent : ∀ (x : G) (hxC : x ∈ centralizerMod (pCoreOf 2 H) H (conjClosure K T)),
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          ⟨x, centralizerMod_le_left _ _ _ hxC⟩ ∈
        Subgroup.centralizer ((autIH V₁ I H (conjClosure K T) : Subgroup _) : Set _)) :
    centralizerMod (pCoreOf 2 H) H (conjClosure K T) ≤
      Subgroup.normalizer ((V₁ ⊔ ⁅conjClosure I H, K⁆ : Subgroup G) : Set G) := by
  intro x hxC
  have hxH := centralizerMod_le_left _ _ _ hxC
  have hmemN := centralizer_le_NLM (autIH_K_le_K₀ (V₁ := V₁) I (le_of_mem_cComp h.K_cComp) T)
    (hCent x hxC)
  have hst : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨x, hxH⟩ ∈
      stabSub (commV (autIH V₁ I H K)) :=
    CFSG.Quasithin.FixVLat.mem_stabSub_commV_of_mem_normalizer hmemN.1
  rw [← subM_Jg_eq_commV h hIU] at hst
  exact (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
    (le_normalizer_conjClosure I H) le_sup_left (Jg_le_conjClosure h hV₁I) ⟨x, hxH⟩).mp hst

@[expose] noncomputable def piEquiv {F : Type} [Field F] {Lc Mp : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure I H)))}
    (D : CoordData Lc Mp F) : ↥(StatedSL 2 F) ≃* ↥Lc :=
  MulEquiv.ofBijective D.pi ⟨D.pi_inj, D.pi_surj⟩

theorem bq_Jt_comp (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I)
    {F : Type} [Field F] (D : CoordData (autIH V₁ I H K) (autIH V₁ I H (conjClosure K T)) F)
    (k : ↥K) (v w : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆)) (hw : (w : G) = (k : G) * v * (k : G)⁻¹) :
    D.bq (Jt h hIU hV₁I w) = Multiplicative.ofAdd
      (slm ((piEquiv D).symm (toAutI h I k)) * Multiplicative.toAdd (D.bq (Jt h hIU hV₁I v))) := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  set γ := (piEquiv D).symm (toAutI h I k) with hγ
  have hπ : D.pi γ = toAutI h I k := (piEquiv D).apply_symm_apply _
  have hcoe : ((D.pi γ : ↥(autIH V₁ I H K)) : MulAut ↥(tildeOf V₁ (conjClosure I H))) =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨(k : G), hKH k.2⟩ := by
    rw [hπ]
    rfl
  have hJ := Jt_conj h hIU hV₁I ⟨(k : G), hKH k.2⟩ v w hw
  have hmem : ((D.pi γ : ↥(autIH V₁ I H K)) : MulAut ↥(tildeOf V₁ (conjClosure I H)))
      ((Jt h hIU hV₁I v : ↥(commV (autIH V₁ I H K))) : ↥(tildeOf V₁ (conjClosure I H))) ∈
      commV (autIH V₁ I H K) := by
    rw [hcoe, ← hJ]
    exact (Jt h hIU hV₁I w).2
  have h1 := D.bq_equiv γ (Jt h hIU hV₁I v) hmem
  rw [← h1]
  congr 1
  apply Subtype.ext
  exact hJ.trans (congrArg (fun φ : MulAut ↥(tildeOf V₁ (conjClosure I H)) =>
    φ ((Jt h hIU hV₁I v : ↥(commV (autIH V₁ I H K))) : ↥(tildeOf V₁ (conjClosure I H)))) hcoe).symm

@[expose] noncomputable def cHom (h : HypF918 T V L V₁ Vp H K)
    (hCent : ∀ (x : G) (hxC : x ∈ centralizerMod (pCoreOf 2 H) H (conjClosure K T)),
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          ⟨x, centralizerMod_le_left _ _ _ hxC⟩ ∈
        Subgroup.centralizer ((autIH V₁ I H (conjClosure K T) :
          Subgroup (MulAut ↥(tildeOf V₁ (conjClosure I H)))) :
          Set (MulAut ↥(tildeOf V₁ (conjClosure I H))))) :
    ↥(centralizerMod (pCoreOf 2 H) H (conjClosure K T)) →*
      ↥(Subgroup.centralizer ((autIH V₁ I H (conjClosure K T) :
        Subgroup (MulAut ↥(tildeOf V₁ (conjClosure I H)))) :
        Set (MulAut ↥(tildeOf V₁ (conjClosure I H))))) :=
  ((actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)).comp
    (Subgroup.inclusion (centralizerMod_le_left (pCoreOf 2 H) H (conjClosure K T)))).codRestrict _
    (fun x => hCent x x.2)

@[expose] noncomputable def multData (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hV₁I : V₁ ≤ I) {F : Type} [Field F] [Finite F]
    (D : CoordData (autIH V₁ I H K) (autIH V₁ I H (conjClosure K T)) F)
    (hCent : ∀ (x : G) (hxC : x ∈ centralizerMod (pCoreOf 2 H) H (conjClosure K T)),
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          ⟨x, centralizerMod_le_left _ _ _ hxC⟩ ∈
        Subgroup.centralizer ((autIH V₁ I H (conjClosure K T) : Subgroup _) : Set _))
    (hKer : ∀ (k : G) (hk : k ∈ K),
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
        ⟨k, le_of_mem_cComp h.K_cComp hk⟩ = 1 → k ∈ pCoreOf 2 H) :
    MultDataU V₁ Vp H K T I F := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hLMp : autIH V₁ I H K ≤ autIH V₁ I H (conjClosure K T) := autIH_K_le_K₀ (V₁ := V₁) I hKH T
  have hmex := exists_mult D hLMp
  let m := Classical.choose hmex
  have hm := Classical.choose_spec hmex
  have hsex := exists_fieldHom D
  let s := Classical.choose hsex
  have hs := Classical.choose_spec hsex
  have hCN := C_le_normalizer_Jg h hIU hV₁I hCent
  have heqC : ∀ (x : ↥(centralizerMod (pCoreOf 2 H) H (conjClosure K T)))
      (v w : ↥(V₁ ⊔ ⁅conjClosure I H, K⁆)), (w : G) = (x : G) * v * (x : G)⁻¹ →
      D.bq (Jt h hIU hV₁I w) = multOpU F (m (cHom h hCent x)) (D.bq (Jt h hIU hV₁I v)) := by
    intro x v w hw
    rw [← hm]
    exact bq_Jt_conj h hIU hV₁I D (Subgroup.inclusion (centralizer_le_NLM hLMp) (cHom h hCent x))
      ⟨(x : G), centralizerMod_le_left _ _ _ x.2⟩ rfl v w hw
  exact
    { coordinates := D.bq.comp (Jt h hIU hV₁I)
      coordinates_surjective := D.bq_surj.comp (Jt_surjective h hIU hV₁I)
      coordinates_kernel := fun v => by
        show D.bq (Jt h hIU hV₁I v) = 1 ↔ _
        rw [D.bq_ker, Jt_coe]
        exact modMk_mem_fixV_iff h hIU hV₁I v.2
      markedComponent := (piEquiv D).symm.toMonoidHom.comp (toAutI h I)
      markedComponent_surjective := (piEquiv D).symm.surjective.comp (toAutI_surjective h I)
      markedComponent_kernel := fun k => by
        show (piEquiv D).symm (toAutI h I k) = 1 ↔ _
        rw [MulEquiv.map_eq_one_iff, toAutI_eq_one_iff]
        constructor
        · intro hk1
          exact hKer (k : G) k.2 hk1
        · intro hkP
          exact h.actH_eq_one_of_mem_pCoreOf hIU (x := Subgroup.inclusion hKH k) hkP
      component_equivariance := fun k v w hw => bq_Jt_comp h hIU hV₁I D k v w hw
      centralizer_normalizes := hCN
      normalizer_normalizes := N_le_normalizer_Jg h
      multiplicity := m.comp (cHom h hCent)
      multiplicity_equivariance := fun x v w hw => heqC x v w hw
      multiplicity_kernel := fun x => by
        constructor
        · intro hx1 v w hw
          have h1 := heqC x v w hw
          have hx1' : m (cHom h hCent x) = 1 := hx1
          rw [hx1', multOpU_one] at h1
          exact h1
        · intro hall
          obtain ⟨v, hv⟩ := (D.bq_surj.comp (Jt_surjective h hIU hV₁I)) (Multiplicative.ofAdd 1)
          have hwmem : (x : G) * (v : G) * (x : G)⁻¹ ∈ V₁ ⊔ ⁅conjClosure I H, K⁆ :=
            (Subgroup.mem_normalizer_iff.mp (hCN x.2) _).mp v.2
          have e1 := heqC x v ⟨_, hwmem⟩ rfl
          have e2 := hall v ⟨_, hwmem⟩ rfl
          have hv' : D.bq (Jt h hIU hV₁I v) = Multiplicative.ofAdd 1 := hv
          have e3 := e1.symm.trans e2
          show m (cHom h hCent x) = 1
          have hB : multOpU F (m (cHom h hCent x)) (Multiplicative.ofAdd 1) = Multiplicative.ofAdd 1 := by
            rw [← hv']
            exact e3
          unfold multOpU at hB
          rw [toAdd_ofAdd, Matrix.one_mul] at hB
          have hT := Multiplicative.ofAdd.injective hB
          apply Units.ext
          rw [Units.val_one]
          exact Matrix.transpose_eq_one.mp hT
      normalizerAction := (psi D).comp (gHom h)
      normalizer_equivariance := fun x v w hw =>
        bq_Jt_conj h hIU hV₁I D (gHom h x) ⟨(x : G), x.2.1⟩ rfl v w hw
      fieldAction := s.comp (gHom h)
      semilinear := fun x c X => by
        apply Multiplicative.toAdd.injective
        rw [toAdd_ofAdd]
        exact hs (gHom h x) c X
      commutant_transport := fun x B => psi_conj_rmul D (gHom h x) B
      actual_image_transport := fun x B hB => by
        obtain ⟨y, rfl⟩ := hB
        have hz := conj_mem_centralizerMod_K₀ h x.2.1 y.2
        refine ⟨m (cHom h hCent ⟨(x : G) * (y : G) * (x : G)⁻¹, hz⟩), ⟨⟨_, hz⟩, rfl⟩, fun Y => ?_⟩
        show (psi D (gHom h x)) (multOpU F (m (cHom h hCent y)) Y) =
          multOpU F (m (cHom h hCent ⟨(x : G) * (y : G) * (x : G)⁻¹, hz⟩)) ((psi D (gHom h x)) Y)
        rw [← hm (cHom h hCent y) Y,
          ← hm (cHom h hCent ⟨(x : G) * (y : G) * (x : G)⁻¹, hz⟩) ((psi D (gHom h x)) Y),
          ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
        congr 2
        apply Subtype.ext
        show actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨(x : G), x.2.1⟩ *
            actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
              ⟨(y : G), centralizerMod_le_left _ _ _ y.2⟩ =
          actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
              ⟨(x : G) * (y : G) * (x : G)⁻¹, centralizerMod_le_left _ _ _ hz⟩ *
            actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨(x : G), x.2.1⟩
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        show (x : G) * (y : G) = (x : G) * (y : G) * (x : G)⁻¹ * (x : G)
        group
      full_commutant := fun op hlin hcomm => fullCommutantU F op hlin hcomm }

end Coordinates

end CFSG.Quasithin.RonanF918
