module

public import CFSG.Quasithin.MS93.S37Q1N
public import CFSG.Quasithin.MS93.S37LSym

public section

namespace CFSG.Quasithin.MS93.S37L

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.Quasithin.MS93.S37
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  (C : Cfg M T L F)

theorem rhoIm_le_T0bar {X : Subgroup G} (hX : X ≤ T1 M T L) : C.rhoIm X ≤ C.T0bar := by
  intro g hg
  obtain ⟨x, hxK, hx, rfl⟩ := (C.mem_rhoIm).1 hg
  exact ⟨⟨x, hX hx⟩, rfl⟩

theorem rhoIm_T1 : C.rhoIm (T1 M T L) = C.T0bar := by
  refine le_antisymm (rhoIm_le_T0bar C le_rfl) ?_
  rintro _ ⟨t, rfl⟩
  exact (C.mem_rhoIm).2 ⟨t, T1_le_sup t.2, t.2, rfl⟩

section CaseII

variable (hT : C.T0bar = Q₁ F) (θ : MulAut ↥(T1 M T L))
include hT

theorem ln₀_le_fixSp : ln₀ F ≤ fixSp (C.rhoIm (Ut M T L θ)) := by
  have h := fixSp_antitone (rhoIm_le_T0bar C (tImage_le θ (Uq M T L)))
  rwa [hT, fixSp_Q₁] at h

omit hT in
theorem relIndex_eq_of_line (hcrit : ¬ Uq M T L ≤ Qt M θ)
    (hII : IsLine (fixSp (C.rhoIm (Ut M T L θ)))) :
    (pCoreOf 2 M).relIndex (Ut M T L θ) = Nat.card F ^ 2 := by
  have hV := C.card_V4_eq C.pCore_le_T1 T1_le_T θ (tImage_le θ _)
  rw [C.relIndex_Qt_eq C.pCore_le_T1 θ, C.partner_relIndex_eq θ hcrit, MSP.card_V4,
    MSP.card_fixSp, hII.1] at hV
  have hq : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos 2
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [← hV]
  ring

theorem fixSp_inv_eq_ln₀ (hcrit : ¬ Uq M T L ≤ Qt M θ)
    (hII : IsLine (fixSp (C.rhoIm (Ut M T L θ)))) :
    fixSp (C.rhoIm (Ut M T L θ⁻¹)) = ln₀ F := by
  have hq1 : 1 < Nat.card F := by have := C.q_ge_four; omega
  have hV := C.card_V4_eq C.pCore_le_T1 T1_le_T θ⁻¹ (tImage_le θ⁻¹ _)
  rw [C.relIndex_Qt_eq C.pCore_le_T1 θ⁻¹, inv_inv, relIndex_eq_of_line C θ hcrit hII,
    MSP.card_V4, MSP.card_fixSp] at hV
  have h4 : Nat.card F ^ 4 = Nat.card F ^ 2 * Nat.card F ^ 2 := by ring
  rw [h4] at hV
  have h2 := Nat.eq_of_mul_eq_mul_left (pow_pos Nat.card_pos 2) hV
  have hrank : Module.finrank F ↥(fixSp (C.rhoIm (Ut M T L θ⁻¹))) = 2 :=
    (Nat.pow_right_injective hq1 h2).symm
  refine (Submodule.eq_of_le_of_finrank_eq (ln₀_le_fixSp C hT θ⁻¹) ?_).symm
  rw [hrank, isLine_ln₀.1]

theorem fixSp_eq_ln₀_of_line (hII : IsLine (fixSp (C.rhoIm (Ut M T L θ)))) :
    fixSp (C.rhoIm (Ut M T L θ)) = ln₀ F := by
  refine (Submodule.eq_of_le_of_finrank_eq (ln₀_le_fixSp C hT θ) ?_).symm
  rw [hII.1, isLine_ln₀.1]

theorem mem_center_of_mem_Ut (hcrit : ¬ Uq M T L ≤ Qt M θ)
    (hII : IsLine (fixSp (C.rhoIm (Ut M T L θ)))) {z : G} (hz : z ∈ Ut M T L θ)
    (hzQ : z ∈ pCoreOf 2 M) {t : G} (ht : t ∈ T1 M T L) : t * z = z * t := by
  obtain ⟨u, huT, hu, rfl⟩ := mem_tImage.1 hz
  have huQ : u ∈ Qt M θ⁻¹ := by
    have h1 : ((θ ⟨u, huT⟩ : ↥(T1 M T L)) : G) ∈ pCoreOf 2 M := hzQ
    refine mem_tImage.2 ⟨_, (θ ⟨u, huT⟩).2, h1, ?_⟩
    rw [MulAut.inv_apply_self]
  rw [C.Qt_eq C.pCore_le_T1 T1_le_T] at huQ
  have hfix : C.N.co ⟨u, hu⟩ ∈ fixSp (C.rhoIm (Ut M T L θ⁻¹)) :=
    (C.co_mem_fixSp_iff ((tImage_le θ⁻¹ _).trans T1_le_sup) ⟨u, hu⟩).2 huQ.2
  rw [fixSp_inv_eq_ln₀ C hT θ hcrit hII, ← fixSp_Q₁, ← hT, ← rhoIm_T1 C] at hfix
  have hc := (C.co_mem_fixSp_iff T1_le_sup ⟨u, hu⟩).1 hfix
  have e : (θ⁻¹ ⟨t, ht⟩ : ↥(T1 M T L)) * ⟨u, huT⟩ = ⟨u, huT⟩ * θ⁻¹ ⟨t, ht⟩ :=
    Subtype.ext (Subgroup.mem_centralizer_iff.1 hc _ (θ⁻¹ ⟨t, ht⟩).2)
  have := congrArg (fun s => ((θ s : ↥(T1 M T L)) : G)) e
  simpa only [map_mul, Subgroup.coe_mul, MulAut.apply_inv_self] using this

end CaseII

theorem conj_mem_Qt_of_fix (θ : MulAut ↥(T1 M T L))
    (hfixE : fixSp (C.rhoIm (Ut M T L θ)) = ln₀ F) {g : G} (hg : g ∈ L) {x : G}
    (hx : x ∈ Ut M T L θ) (hxK : x ∈ L ⊔ pCoreOf 2 M)
    (hcomm : C.α ⟨g, hg⟩ * C.rho ⟨x, hxK⟩ * (C.α ⟨g, hg⟩)⁻¹ = C.rho ⟨x, hxK⟩)
    (hrk : ∀ v : V4 F, mat (C.rho ⟨x, hxK⟩) *ᵥ v = v → v ∈ ln₀ F) :
    g * x * g⁻¹ ∈ Qt M θ := by
  have hxT : x ∈ T1 M T L := tImage_le θ _ hx
  obtain ⟨s, hs, q, hq, rfl⟩ := C.exists_mul_of_mem_T1 hxT
  have hgM : g ∈ M := C.h.L_le hg
  have hsL : s ∈ L := hs.2
  have hsK : s ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_sup_left hsL
  have hρs : C.rho ⟨s * q, hxK⟩ = C.α ⟨s, hsL⟩ := C.rho_mul hsL hq hxK
  have hu₁ : s⁻¹ * g * s * g⁻¹ ∈ Uq M T L := by
    rw [← C.inf_pCore_eq_Uq]
    have hL : s⁻¹ * g * s * g⁻¹ ∈ L := L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hsL) hg) hsL)
      (L.inv_mem hg)
    refine ⟨hL, ?_⟩
    have hK : s⁻¹ * g * s * g⁻¹ ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_sup_left hL
    show s⁻¹ * g * s * g⁻¹ ∈ pCoreOf 2 M
    refine (C.rho_eq_one_iff ⟨_, hK⟩).1 ?_
    rw [C.rho_of_mem_L hL]
    have e : (⟨s⁻¹ * g * s * g⁻¹, hL⟩ : ↥L) =
        (⟨s, hsL⟩ : ↥L)⁻¹ * ⟨g, hg⟩ * ⟨s, hsL⟩ * (⟨g, hg⟩ : ↥L)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hρs]
    calc (C.rho ⟨s * q, hxK⟩)⁻¹ * C.α ⟨g, hg⟩ * C.rho ⟨s * q, hxK⟩ * (C.α ⟨g, hg⟩)⁻¹
        = (C.rho ⟨s * q, hxK⟩)⁻¹ *
          (C.α ⟨g, hg⟩ * C.rho ⟨s * q, hxK⟩ * (C.α ⟨g, hg⟩)⁻¹) := by group
      _ = 1 := by rw [hcomm, inv_mul_cancel]
  have hu₂ : q⁻¹ * g * q * g⁻¹ ∈ Uq M T L := by
    have := comm_mem_Uq C.hVU (inv_mem hq) hg
    simpa [commutatorElement_def] using this
  set x := s * q with hxdef
  have hy : x⁻¹ * (g * x * g⁻¹) ∈ Uq M T L := by
    have e : x⁻¹ * (g * x * g⁻¹) = (q⁻¹ * (s⁻¹ * g * s * g⁻¹) * q) * (q⁻¹ * g * q * g⁻¹) := by
      rw [hxdef]
      group
    rw [e]
    refine (Uq M T L).mul_mem ?_ hu₂
    have := (Subgroup.mem_normalizer_iff.1 (C.hMU (M.inv_mem (pCoreOf_le' M hq)))
      (s⁻¹ * g * s * g⁻¹)).1 hu₁
    simpa using this
  set y := x⁻¹ * (g * x * g⁻¹) with hydef
  have hx2 : x * x = 1 := by rw [← sq]; exact C.Ut_sq θ hx
  have hy2 : y * y = 1 := by rw [← sq]; exact Sp4L.uq_sq C.h hy
  have hxy2 : (x * y) * (x * y) = 1 := by
    have e : x * y = g * x * g⁻¹ := by rw [hydef]; group
    rw [e]
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2, mul_one, mul_inv_cancel]
  have hxy : x * y * x⁻¹ = y := by
    have hxi : x⁻¹ = x := by rw [inv_eq_iff_mul_eq_one]; exact hx2
    have hyi : y⁻¹ = y := by rw [inv_eq_iff_mul_eq_one]; exact hy2
    calc x * y * x⁻¹ = (x * y * x * y) * y⁻¹ := by rw [hxi]; group
      _ = y := by rw [show x * y * x * y = (x * y) * (x * y) by group, hxy2, one_mul, hyi]
  have hco : C.N.co ⟨y, hy⟩ ∈ ln₀ F := by
    refine hrk _ ?_
    rw [← C.co_conj ⟨x, hxK⟩ (u := ⟨y, hy⟩) (v := ⟨y, hy⟩) hxy.symm]
  rw [← hfixE] at hco
  have hyc := (C.co_mem_fixSp_iff ((tImage_le θ _).trans T1_le_sup) ⟨y, hy⟩).1 hco
  have hyQt : y ∈ Qt M θ := by
    rw [C.Qt_eq C.pCore_le_T1 T1_le_T]
    exact ⟨C.Uq_le_T1 hy, hyc⟩
  have hxQt : x ∈ Qt M θ := tImage_mono' θ C.Uq_le_pCore hx
  have e : g * x * g⁻¹ = x * y := by rw [hydef]; group
  rw [e]
  exact (Qt M θ).mul_mem hxQt hyQt

theorem rhoIm_mono {X Y : Subgroup G} (h : X ≤ Y) : C.rhoIm X ≤ C.rhoIm Y := by
  intro g hg
  obtain ⟨x, hxK, hx, rfl⟩ := (C.mem_rhoIm).1 hg
  exact (C.mem_rhoIm).2 ⟨x, hxK, h hx, rfl⟩

theorem conj_mem_T1 (hT : C.T0bar = Q₁ F) {l : G} (hl : l ∈ L ⊔ pCoreOf 2 M)
    (hlP : C.rho ⟨l, hl⟩ ∈ P₁ F) {t : G} (ht : t ∈ T1 M T L) : l * t * l⁻¹ ∈ T1 M T L := by
  have htK : t ∈ L ⊔ pCoreOf 2 M := T1_le_sup ht
  have hK : l * t * l⁻¹ ∈ L ⊔ pCoreOf 2 M :=
    (L ⊔ pCoreOf 2 M).mul_mem ((L ⊔ pCoreOf 2 M).mul_mem hl htK) ((L ⊔ pCoreOf 2 M).inv_mem hl)
  refine C.mem_T1_of_rho_mem (x := ⟨_, hK⟩) ?_
  rw [C.rho_conj_eq hl htK hK, hT]
  have hρt : C.rho ⟨t, htK⟩ ∈ Q₁ F := by
    rw [← hT]
    exact ⟨⟨t, ht⟩, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 (P₁_le_normalizer_Q₁ hlP) _).1 hρt

theorem exists_caseI_of_caseII (hT : C.T0bar = Q₁ F) (θ : MulAut ↥(T1 M T L))
    (hcrit : ¬ Uq M T L ≤ Qt M θ) (hII : IsLine (fixSp (C.rhoIm (Ut M T L θ))))
    (hN : C.rhoIm (Qt M θ) = C.rhoIm (Ut M T L θ)) :
    ∃ φ : MulAut ↥(T1 M T L), ¬ Uq M T L ≤ Qt M φ ∧
      ∃ p : Submodule F (V4 F), IsPoint p ∧ C.rhoIm (Ut M T L φ) = xPoint p := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hUθT : Ut M T L θ ≤ T1 M T L := tImage_le θ _
  have hEQ : C.rhoIm (Ut M T L θ) ≤ Q₁ F := hT ▸ rhoIm_le_T0bar C hUθT
  have hcardE : Nat.card ↥(C.rhoIm (Ut M T L θ)) = Nat.card F ^ 2 := by
    rw [C.card_rhoIm (hUθT.trans T1_le_sup), relIndex_eq_of_line C θ hcrit hII]
  have hq2 : 2 < Nat.card F := by have := C.q_ge_four; omega
  obtain ⟨A, e, heE, hrk, hfix, e', he'E, hn⟩ := exists_leviFix hq2 hEQ hcardE
  have hfixE := fixSp_eq_ln₀_of_line C hT θ hII
  set g := C.lift (levHom₁ A) with hgdef
  have hgL : g ∈ L := C.lift_mem _
  have hgK : g ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_sup_left hgL
  have hαg : C.α ⟨g, hgL⟩ = levHom₁ A := C.alpha_lift _
  have hρg : C.rho ⟨g, hgK⟩ = levHom₁ A := by rw [C.rho_of_mem_L hgL, hαg]
  have hgP : C.rho ⟨g, hgK⟩ ∈ P₁ F := by rw [hρg]; exact lev₁_le_P₁ ⟨A, rfl⟩
  have hgiK : g⁻¹ ∈ L ⊔ pCoreOf 2 M := (L ⊔ pCoreOf 2 M).inv_mem hgK
  have hgiP : C.rho ⟨g⁻¹, hgiK⟩ ∈ P₁ F := by
    have e1 : (⟨g⁻¹, hgiK⟩ : ↥(L ⊔ pCoreOf 2 M)) = (⟨g, hgK⟩)⁻¹ := rfl
    rw [e1, map_inv]
    exact (P₁ F).inv_mem hgP
  have hgN : g ∈ Subgroup.normalizer (T1 M T L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨conj_mem_T1 C hT hgK hgP, fun ht => ?_⟩
    have := conj_mem_T1 C hT hgiK hgiP ht
    simpa [mul_assoc] using this
  set cg := (T1 M T L).normalizerMonoidHom ⟨g, hgN⟩ with hcg
  set φ := θ⁻¹ * (cg * θ) with hφ
  set U₂ := (Ut M T L θ).map (MulAut.conj g).toMonoidHom with hU₂
  have hU₂T : U₂ ≤ T1 M T L := by
    rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hgN z).1 (hUθT hz)
  have hUφ : Ut M T L φ = tImage θ⁻¹ U₂ := by
    rw [hφ, Ut, tImage_mul, tImage_normalizer_mul]
  have hθφ : tImage θ (Ut M T L φ) = U₂ := by rw [hUφ, tImage_tImage_inv' θ hU₂T]
  obtain ⟨x, hxK, hx, hρx⟩ := (C.mem_rhoIm).1 heE
  have hxg : g * x * g⁻¹ ∈ Qt M θ :=
    conj_mem_Qt_of_fix C θ hfixE hgL hx hxK (by rw [hαg, hρx, hfix]) (by rw [hρx]; exact hrk)
  have hcritφ : ¬ Uq M T L ≤ Qt M φ := by
    intro h
    rw [C.le_Qt_iff C.pCore_le_T1 T1_le_T φ] at h
    have h2 : U₂ ≤ Qt M θ := by
      rw [← hθφ]
      exact tImage_mono' θ h
    apply hn
    have h3 : C.rhoIm U₂ ≤ C.rhoIm (Ut M T L θ) := by
      rw [← hN]
      exact rhoIm_mono C h2
    apply h3
    rw [hU₂, C.rhoIm_map_conj (hUθT.trans T1_le_sup) hgK, hρg]
    exact Subgroup.mem_map_of_mem _ he'E
  have hpU₂ : (pCoreOf 2 M).relIndex U₂ = Nat.card F ^ 2 := by
    have hpc : (pCoreOf 2 M).map (MulAut.conj g).toMonoidHom = pCoreOf 2 M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (le_normalizer_pCoreOf M (C.h.L_le hgL))
    rw [hU₂, ← hpc, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
      relIndex_eq_of_line C θ hcrit hII]
  have hle : pCoreOf 2 M ⊓ U₂ ≤ Qt M θ ⊓ U₂ := by
    rintro w ⟨hwQ, hwU₂⟩
    refine ⟨?_, hwU₂⟩
    obtain ⟨z, hz, rfl⟩ := hwU₂
    have hzQ : z ∈ pCoreOf 2 M := by
      have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf M
        (C.h.L_le (L.inv_mem hgL))) _).1 hwQ
      simpa [mul_assoc] using this
    rw [C.Qt_eq C.pCore_le_T1 T1_le_T]
    refine ⟨hU₂T ⟨z, hz, rfl⟩, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
    have htT := hUθT ht
    have hgt : g⁻¹ * t * g ∈ T1 M T L := by
      have := conj_mem_T1 C hT hgiK hgiP htT
      simpa using this
    have hc := mem_center_of_mem_Ut C hT θ hcrit hII hz hzQ hgt
    show t * (g * z * g⁻¹) = g * z * g⁻¹ * t
    calc t * (g * z * g⁻¹) = g * ((g⁻¹ * t * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * t := by group
  have hlt' : pCoreOf 2 M ⊓ U₂ < Qt M θ ⊓ U₂ := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have hxU₂ : g * x * g⁻¹ ∈ U₂ := ⟨x, hx, rfl⟩
    have hmem : g * x * g⁻¹ ∈ pCoreOf 2 M ⊓ U₂ := by rw [heq]; exact ⟨hxg, hxU₂⟩
    have hK' : g * x * g⁻¹ ∈ L ⊔ pCoreOf 2 M :=
      (L ⊔ pCoreOf 2 M).mul_mem ((L ⊔ pCoreOf 2 M).mul_mem hgK hxK) hgiK
    have h1 := (C.rho_eq_one_iff ⟨_, hK'⟩).2 hmem.1
    rw [C.rho_conj_eq hgK hxK hK', hρg, hρx, hfix] at h1
    have hf : f₁ F ∈ ln₀ F := hrk _ (by rw [h1, mat_one, Matrix.one_mulVec])
    simp [mem_ln₀, f₁] at hf
  have hlt : (pCoreOf 2 M).relIndex (Ut M T L φ) < Nat.card F ^ 2 := by
    have e1 : (pCoreOf 2 M).relIndex (Ut M T L φ) = (Qt M θ).relIndex U₂ := by
      rw [← relIndex_tImage θ C.pCore_le_T1 (tImage_le φ _), hθφ]
    rw [e1, ← hpU₂]
    have c1 := Subgroup.relIndex_mul_card (Qt M θ) U₂
    have c2 := Subgroup.relIndex_mul_card (pCoreOf 2 M) U₂
    have c3 := Subgroup.card_lt_of_lt hlt'
    have hpos : 0 < (Qt M θ).relIndex U₂ := Cfg.relIndex_pos' _ _
    by_contra hge
    push Not at hge
    have : (pCoreOf 2 M).relIndex U₂ * Nat.card ↥(pCoreOf 2 M ⊓ U₂) <
        (Qt M θ).relIndex U₂ * Nat.card ↥(Qt M θ ⊓ U₂) :=
      Nat.mul_lt_mul_of_le_of_lt hge c3 hpos
    omega
  rcases C.partner_cases φ hcritφ with ⟨p, hp, hpE⟩ | ⟨hII', -⟩
  · exact ⟨φ, hcritφ, p, hp, hpE⟩
  · exact absurd (relIndex_eq_of_line C φ hcritφ hII') (ne_of_lt hlt)

end CFSG.Quasithin.MS93.S37L
