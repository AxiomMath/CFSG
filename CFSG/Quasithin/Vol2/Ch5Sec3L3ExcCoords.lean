module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3Semi

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F1
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.SL2Semilinear
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.QuasithinUnique.Fin257.L3

section General

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] [Finite F]

noncomputable def V1Coords.ofEmbedding {X B Li Vi Vj Z : Subgroup G}
    {R R' : Subgroup (projectiveSL 3 F)} (Rc : RadCoords R R')
    (b : ↥(Subgroup.normalizer (R : Set (projectiveSL 3 F))) →* G) (hb : Function.Injective b)
    (hXb : ∀ g ∈ X, ∃ m, b m = g)
    (hVi : subImg b R = Vi) (hVj : subImg b R' = Vj)
    (hZ : subImg b (centerOf (projUnitriangular 3 F)) = Z)
    (hR'N : R' ≤ Subgroup.normalizer (R : Set (projectiveSL 3 F)))
    (hUN : Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) ≤ Subgroup.normalizer (R : Set (projectiveSL 3 F)))
    (hbX : ∀ m, b m ∈ X) (hXL : X ≤ Subgroup.normalizer (Li : Set G)) (hVjL : Vj ≤ Li)
    (hB : ∀ (d : projectiveSL 3 F) (hd : d ∈ Subgroup.normalizer (R : Set (projectiveSL 3 F))),
      d ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)) → b ⟨d, hd⟩ ∈ B) :
    V1Coords X B Li Vi Vj Z F where
  ι p := b ⟨Rc.co p, Subgroup.le_normalizer (Rc.co_mem p)⟩
  mem p := by
    rw [← hVi]
    exact mem_subImg_of_mem b _ (Rc.co_mem p)
  add p q := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext (Rc.co_add p q)
  inj p q h := Rc.co_inj (congrArg Subtype.val (hb h))
  surj v hv := by
    rw [← hVi] at hv
    obtain ⟨x, hx, hxR, rfl⟩ := mem_subImg.mp hv
    obtain ⟨p, rfl⟩ := Rc.co_surj x hxR
    exact ⟨p, rfl⟩
  center v := by
    rw [← hZ, mem_subImg]
    constructor
    · rintro ⟨x, hx, hxZ, rfl⟩
      obtain ⟨c, rfl⟩ := (Rc.center x).mp hxZ
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨_, Subgroup.le_normalizer (Rc.co_mem (0, c)), (Rc.center _).mpr ⟨c, rfl⟩, rfl⟩
  lin g hg := by
    obtain ⟨m, rfl⟩ := hXb g hg
    obtain ⟨α, β, γ, δ, hlin⟩ := Rc.lin m.1 m.2
    refine ⟨α, β, γ, δ, fun u v => ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    exact Subtype.ext (hlin u v)
  xe β := b ⟨Rc.s * Rc.y β * Rc.s⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ Rc.s_mem
    (hR'N (Rc.y_mem β))) (Subgroup.inv_mem _ Rc.s_mem)⟩
  xe_mem β := by
    have e : b ⟨Rc.s * Rc.y β * Rc.s⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ Rc.s_mem
        (hR'N (Rc.y_mem β))) (Subgroup.inv_mem _ Rc.s_mem)⟩ =
        b ⟨Rc.s, Rc.s_mem⟩ * b ⟨Rc.y β, hR'N (Rc.y_mem β)⟩ * (b ⟨Rc.s, Rc.s_mem⟩)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [e]
    have hyV : b ⟨Rc.y β, hR'N (Rc.y_mem β)⟩ ∈ Vj := by
      rw [← hVj]
      exact mem_subImg_of_mem b _ (Rc.y_mem β)
    exact (Subgroup.mem_normalizer_iff.mp (hXL (hbX _)) _).mp (hVjL hyV)
  xe_act β p := by
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    obtain ⟨u, v⟩ := p
    have h1 : Rc.s⁻¹ * Rc.co (u, v) * Rc.s = Rc.co (v, u) := by
      have := Rc.s_swap v u
      rw [← this]
      group
    show Rc.s * Rc.y β * Rc.s⁻¹ * Rc.co (u, v) * (Rc.s * Rc.y β * Rc.s⁻¹)⁻¹ = Rc.co (tvX β (u, v))
    calc Rc.s * Rc.y β * Rc.s⁻¹ * Rc.co (u, v) * (Rc.s * Rc.y β * Rc.s⁻¹)⁻¹ =
          Rc.s * (Rc.y β * (Rc.s⁻¹ * Rc.co (u, v) * Rc.s) * (Rc.y β)⁻¹) * Rc.s⁻¹ := by group
      _ = Rc.s * Rc.co (tvY β (v, u)) * Rc.s⁻¹ := by rw [h1, Rc.y_act]
      _ = Rc.co (tvX β (u, v)) := by rw [tvY_apply, tvX_apply, Rc.s_swap]
  ye β := b ⟨Rc.y β, hR'N (Rc.y_mem β)⟩
  ye_mem β := by
    rw [← hVj]
    exact mem_subImg_of_mem b _ (Rc.y_mem β)
  ye_act β p := by
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    exact Subtype.ext (Rc.y_act β p)
  tor t := by
    obtain ⟨d, hdU, hd⟩ := Rc.tor t
    refine ⟨b ⟨d, hUN hdU⟩, hB d (hUN hdU) hdU, fun u v => ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    exact Subtype.ext (hd u v)

end General

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2]

namespace L3Model

noncomputable abbrev b₂ (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F) :
    ↥(Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F))) →* G :=
  (sec53G2 M L H D).subtype.comp (isoφ2 Mo.iso).symm.toMonoidHom

omit [Finite G] [Finite F] in
theorem b₂_injective (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F) :
    Function.Injective Mo.b₂ :=
  (sec53G2 M L H D).subtype_injective.comp (isoφ2 Mo.iso).symm.injective

omit [Finite G] [Finite F] in
theorem mem_subImg_b₂ (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    {Y : Subgroup (projectiveSL 3 F)} {x : G} :
    x ∈ subImg Mo.b₂ Y ↔ ∃ h : x ∈ sec53G2 M L H D,
      ((isoφ2 Mo.iso ⟨x, h⟩ : ↥(Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)))) :
        projectiveSL 3 F) ∈ Y := by
  rw [mem_subImg]
  constructor
  · rintro ⟨y, hy, hyY, rfl⟩
    refine ⟨((isoφ2 Mo.iso).symm ⟨y, hy⟩).2, ?_⟩
    have h3 : isoφ2 Mo.iso ⟨Mo.b₂ ⟨y, hy⟩, ((isoφ2 Mo.iso).symm ⟨y, hy⟩).2⟩ = ⟨y, hy⟩ :=
      (isoφ2 Mo.iso).apply_symm_apply ⟨y, hy⟩
    rw [h3]
    exact hyY
  · rintro ⟨h, hY⟩
    refine ⟨_, (isoφ2 Mo.iso ⟨x, h⟩).2, hY, ?_⟩
    show (((isoφ2 Mo.iso).symm (isoφ2 Mo.iso ⟨x, h⟩) : ↥(sec53G2 M L H D)) : G) = x
    rw [MulEquiv.symm_apply_apply]

omit [Finite G] [Finite F] in
theorem exists_b₂_eq (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F) {g : G}
    (hg : g ∈ sec53G2 M L H D) : ∃ m, Mo.b₂ m = g :=
  ⟨isoφ2 Mo.iso ⟨g, hg⟩, by
    show (((isoφ2 Mo.iso).symm (isoφ2 Mo.iso ⟨g, hg⟩) : ↥(sec53G2 M L H D)) : G) = g
    rw [MulEquiv.symm_apply_apply]⟩

omit [Finite G] [Finite F] in
theorem exists_b₁_eq (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F) {g : G}
    (hg : g ∈ sec53G1 M L H B) : ∃ m, Mo.b₁ m = g :=
  ⟨isoφ1 Mo.iso ⟨g, hg⟩, by
    show (((isoφ1 Mo.iso).symm (isoφ1 Mo.iso ⟨g, hg⟩) : ↥(sec53G1 M L H B)) : G) = g
    rw [MulEquiv.symm_apply_apply]⟩

omit [Finite G] [Finite F] in
theorem b₁_eq_b₂ (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    {d : projectiveSL 3 F} (h1 : d ∈ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)))
    (h2 : d ∈ Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F))) :
    Mo.b₁ ⟨d, h1⟩ = Mo.b₂ ⟨d, h2⟩ := by
  have hG₁ : Mo.b₁ ⟨d, h1⟩ ∈ sec53G1 M L H B := ((isoφ1 Mo.iso).symm _).2
  have hd : isoφ1 Mo.iso ⟨Mo.b₁ ⟨d, h1⟩, hG₁⟩ = ⟨d, h1⟩ := (isoφ1 Mo.iso).apply_symm_apply _
  have hG₂ : Mo.b₁ ⟨d, h1⟩ ∈ sec53G2 M L H D :=
    Mo.mem_G2_of_mem_normalizer ⟨_, hG₁⟩ (by rw [hd]; exact h2)
  have hag := Mo.coe_iso_agree _ hG₁ hG₂
  rw [hd] at hag
  have h3 : isoφ2 Mo.iso ⟨Mo.b₁ ⟨d, h1⟩, hG₂⟩ = ⟨d, h2⟩ := Subtype.ext hag.symm
  show _ = (((isoφ2 Mo.iso).symm ⟨d, h2⟩ : ↥(sec53G2 M L H D)) : G)
  rw [← h3, MulEquiv.symm_apply_apply]

theorem subImg_R₂_b₂ (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f) :
    subImg Mo.b₂ Mo.R₂ = pCoreOf 2 (oTwoUpper H) := by
  ext x
  rw [mem_subImg_b₂]
  constructor
  · rintro ⟨h, hR⟩
    exact (Mo.mem_pCoreOf_K_iff hyp hty ⟨x, h⟩).mpr hR
  · intro hx
    have h : x ∈ sec53G2 M L H D :=
      (le_sup_right : oTwoUpper H ≤ sec53G2 M L H D) (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx)
    exact ⟨h, (Mo.mem_pCoreOf_K_iff hyp hty ⟨x, h⟩).mp hx⟩

theorem subImg_R₁_b₂ (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    subImg Mo.b₂ Mo.R₁ = pCoreOf 2 L := by
  have hRN : Mo.R₁ ≤ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) ⊓
      Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)) := by
    rw [normalizer_inf_normalizer Mo.data]
    exact Mo.data.borel.le₁.trans Subgroup.le_normalizer
  ext x
  rw [mem_subImg_b₂]
  constructor
  · rintro ⟨h, hR⟩
    have h1 := Mo.mem_G1_of_mem_normalizer ⟨x, h⟩ (Subgroup.mem_inf.mp (hRN hR)).1
    refine (Mo.mem_pCoreOf_L_iff hyp ⟨x, h1⟩).mpr ?_
    rw [Mo.coe_iso_agree x h1 h]
    exact hR
  · intro hx
    have h1 : x ∈ sec53G1 M L H B :=
      (le_sup_left.trans le_sup_left : L ≤ sec53G1 M L H B)
        (CFSG.LieType.BorelTits.pCoreOf_le 2 L hx)
    have hR := (Mo.mem_pCoreOf_L_iff hyp ⟨x, h1⟩).mp hx
    have h2 := Mo.mem_G2_of_mem_normalizer ⟨x, h1⟩ (Subgroup.mem_inf.mp (hRN hR)).2
    refine ⟨h2, ?_⟩
    rw [← Mo.coe_iso_agree x h1 h2]
    exact hR

omit [Finite F] in
theorem subImg_U_b₂ (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F) (h527 : Stmt5_2_7)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    subImg Mo.b₂ (projUnitriangular 3 F) = sec53S T L := by
  rw [← Mo.subImg_U h527 hyp]
  have hUN : projUnitriangular 3 F ≤ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) ⊓
      Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)) := by
    rw [normalizer_inf_normalizer Mo.data]
    exact Subgroup.le_normalizer
  ext x
  rw [mem_subImg, mem_subImg]
  constructor
  · rintro ⟨y, hy, hyU, rfl⟩
    exact ⟨y, (Subgroup.mem_inf.mp (hUN hyU)).1, hyU, Mo.b₁_eq_b₂ _ _⟩
  · rintro ⟨y, hy, hyU, rfl⟩
    exact ⟨y, (Subgroup.mem_inf.mp (hUN hyU)).2, hyU, (Mo.b₁_eq_b₂ _ _).symm⟩

omit [Finite F] in
theorem subImg_Z_b₂ (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F) (h527 : Stmt5_2_7)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    subImg Mo.b₂ (centerOf (projUnitriangular 3 F)) = sec53ZS T L := by
  have hU : projUnitriangular 3 F ≤ Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)) :=
    Subgroup.le_normalizer.trans Mo.data.borel.lt₂.le
  rw [← subImg_centerOf Mo.b₂_injective hU, Mo.subImg_U_b₂ h527 hyp]

end L3Model

theorem sec53S_le_K (h527 : Stmt5_2_7) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    sec53S T L ≤ oTwoUpper H := by
  obtain ⟨-, ⟨-, -, -, hST, hSK, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [show sec53S T L = T ⊓ L from rfl, ← hST, hSK]
  exact inf_le_right

theorem exists_sCoords (h527 : Stmt5_2_7) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (hf : 2 ≤ f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ f ∧
      ∃ (C₁ : V1Coords (sec53G1 M L H B) (sec53G1 M L H B ⊓ sec53G2 M L H D) L (pCoreOf 2 L)
          (pCoreOf 2 (oTwoUpper H)) (sec53ZS T L) F)
        (C₂ : V1Coords (sec53G2 M L H D) (sec53G1 M L H B ⊓ sec53G2 M L H D) (oTwoUpper H)
          (pCoreOf 2 (oTwoUpper H)) (pCoreOf 2 L) (sec53ZS T L) F),
        (∀ c, C₁.ι (0, c) = C₂.ι (0, c)) ∧ (∀ β, C₁.ye β = C₂.ι (β, 0)) ∧
          ∀ β, C₂.ye β = C₁.ι (β, 0) := by
  obtain ⟨F, hFf, hFfin, hFchar, hFcard, ⟨Mo⟩⟩ := exists_l3Model hty hf
  refine ⟨F, hFf, hFfin, hFchar, hFcard, ?_⟩
  obtain ⟨Rc₁, Rc₂, h0, hy₁, hy₂⟩ : ∃ (Rc₁ : RadCoords Mo.R₁ Mo.R₂) (Rc₂ : RadCoords Mo.R₂ Mo.R₁),
      (∀ c, Rc₁.co (0, c) = Rc₂.co (0, c)) ∧ (∀ β, Rc₁.y β = Rc₂.co (β, 0)) ∧
        ∀ β, Rc₂.y β = Rc₁.co (β, 0) := by
    rcases Mo.radicals with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      refine ⟨radCoords_V1, radCoords_V2, fun c => ?_, fun β => ?_, fun β => ?_⟩
      · rw [radCoords_V1_co, radCoords_V2_co, xP_zero, yP_zero]
      · rw [radCoords_V1_y, radCoords_V2_co, wP_zero, mul_one]
      · rw [radCoords_V2_y, radCoords_V1_co, wP_zero, mul_one]
    · rw [h1, h2]
      refine ⟨radCoords_V2, radCoords_V1, fun c => ?_, fun β => ?_, fun β => ?_⟩
      · rw [radCoords_V1_co, radCoords_V2_co, xP_zero, yP_zero]
      · rw [radCoords_V2_y, radCoords_V1_co, wP_zero, mul_one]
      · rw [radCoords_V1_y, radCoords_V2_co, wP_zero, mul_one]
  have hUN₁ : Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) ≤ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) :=
    Mo.data.borel.lt₁.le
  have hUN₂ : Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) ≤ Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)) :=
    Mo.data.borel.lt₂.le
  have hR₂N : Mo.R₂ ≤ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) :=
    Mo.data.borel.le₂.trans (Subgroup.le_normalizer.trans hUN₁)
  have hR₁N : Mo.R₁ ≤ Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)) :=
    Mo.data.borel.le₁.trans (Subgroup.le_normalizer.trans hUN₂)
  have hsup := sup_sec53 h527 hyp hty hf
  have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L :=
    (le_sup_right.trans hsup.le).trans (inf_le_right : sec53S T L ≤ L)
  have hV₁K : pCoreOf 2 L ≤ oTwoUpper H :=
    (le_sup_left.trans hsup.le).trans (sec53S_le_K h527 hyp)
  have hU12 : ∀ d, d ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) → d ∈ Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) ∧
        d ∈ Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)) := fun d hd => ⟨hUN₁ hd, hUN₂ hd⟩
  let C₁ := V1Coords.ofEmbedding (X := sec53G1 M L H B) (B := sec53G1 M L H B ⊓ sec53G2 M L H D)
    (Li := L) (Z := sec53ZS T L) Rc₁ Mo.b₁ Mo.b₁_injective (fun g hg => Mo.exists_b₁_eq hg)
    (Mo.subImg_R₁ hyp) (Mo.subImg_R₂ hyp hty) (Mo.subImg_Z h527 hyp) hR₂N hUN₁
    (fun m => ((isoφ1 Mo.iso).symm m).2) (G1_le_normalizer hyp) hV₂L (fun d hd hdU => by
      have hG₁ : Mo.b₁ ⟨d, hd⟩ ∈ sec53G1 M L H B := ((isoφ1 Mo.iso).symm _).2
      have h1 : isoφ1 Mo.iso ⟨Mo.b₁ ⟨d, hd⟩, hG₁⟩ = ⟨d, hd⟩ := (isoφ1 Mo.iso).apply_symm_apply _
      exact Subgroup.mem_inf.mpr ⟨hG₁, Mo.mem_G2_of_mem_normalizer ⟨_, hG₁⟩ (by
        rw [h1]; exact (hU12 d hdU).2)⟩)
  let C₂ := V1Coords.ofEmbedding (X := sec53G2 M L H D) (B := sec53G1 M L H B ⊓ sec53G2 M L H D)
    (Li := oTwoUpper H) (Z := sec53ZS T L) Rc₂ Mo.b₂ Mo.b₂_injective
    (fun g hg => Mo.exists_b₂_eq hg) (Mo.subImg_R₂_b₂ hyp hty) (Mo.subImg_R₁_b₂ hyp)
    (Mo.subImg_Z_b₂ h527 hyp) hR₁N hUN₂ (fun m => ((isoφ2 Mo.iso).symm m).2)
    (G2_le_normalizer hyp) hV₁K (fun d hd hdU => by
      have hG₂ : Mo.b₂ ⟨d, hd⟩ ∈ sec53G2 M L H D := ((isoφ2 Mo.iso).symm _).2
      have h1 : isoφ2 Mo.iso ⟨Mo.b₂ ⟨d, hd⟩, hG₂⟩ = ⟨d, hd⟩ := (isoφ2 Mo.iso).apply_symm_apply _
      exact Subgroup.mem_inf.mpr ⟨Mo.mem_G1_of_mem_normalizer ⟨_, hG₂⟩ (by
        rw [h1]; exact (hU12 d hdU).1), hG₂⟩)
  refine ⟨C₁, C₂, fun c => ?_, fun β => ?_, fun β => ?_⟩
  · show Mo.b₁ ⟨Rc₁.co (0, c), _⟩ = Mo.b₂ ⟨Rc₂.co (0, c), _⟩
    have hU : Rc₁.co (0, c) ∈ Subgroup.normalizer ((projUnitriangular 3 F :
        Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
      have := (Rc₁.center (Rc₁.co (0, c))).mpr ⟨c, rfl⟩
      exact Subgroup.le_normalizer (Subgroup.mem_inf.mp this).1
    have e : (⟨Rc₂.co (0, c), Subgroup.le_normalizer (Rc₂.co_mem (0, c))⟩ :
        ↥(Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)))) = ⟨Rc₁.co (0, c), hUN₂ hU⟩ :=
      Subtype.ext (h0 c).symm
    rw [e]
    exact Mo.b₁_eq_b₂ _ _
  · show Mo.b₁ ⟨Rc₁.y β, _⟩ = Mo.b₂ ⟨Rc₂.co (β, 0), _⟩
    have hU : Rc₁.y β ∈ Subgroup.normalizer ((projUnitriangular 3 F :
        Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) :=
      Subgroup.le_normalizer (Mo.data.borel.le₂ (Rc₁.y_mem β))
    have e : (⟨Rc₂.co (β, 0), Subgroup.le_normalizer (Rc₂.co_mem (β, 0))⟩ :
        ↥(Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)))) = ⟨Rc₁.y β, hUN₂ hU⟩ :=
      Subtype.ext (hy₁ β).symm
    rw [e]
    exact Mo.b₁_eq_b₂ _ _
  · show Mo.b₂ ⟨Rc₂.y β, _⟩ = Mo.b₁ ⟨Rc₁.co (β, 0), _⟩
    have hU : Rc₂.y β ∈ Subgroup.normalizer ((projUnitriangular 3 F :
        Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) :=
      Subgroup.le_normalizer (Mo.data.borel.le₁ (Rc₂.y_mem β))
    have e : (⟨Rc₁.co (β, 0), Subgroup.le_normalizer (Rc₁.co_mem (β, 0))⟩ :
        ↥(Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)))) = ⟨Rc₂.y β, hUN₁ hU⟩ :=
      Subtype.ext (hy₂ β).symm
    rw [e]
    exact (Mo.b₁_eq_b₂ _ _).symm

end CFSG.Quasithin.H13.Sec53L3
