module

public import CFSG.Quasithin.Vol2.Ch12Sec1Case4CountPf
public import CFSG.Quasithin.Vol2.Ch3Sec3Case4CountGenW
public import CFSG.Quasithin.Vol2.KGFactH91C

public section

namespace CFSG.Quasithin.H13.Sec1214

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix CFSG.LieType.BorelTits
open CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open CFSG.Quasithin.H13.L3321 (SL4)
open CFSG.Quasithin.H13.Case4Count (mem_liftPre_iff)
open scoped Pointwise

theorem notCase4Min_holds :
    ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ T₀ : Subgroup G) (v : G),
      Setting T L V V₁ V₂ v T₀ →
      ¬ CFSG.Quasithin.C134Case4Min (Sec1216Lv.lv L v ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)))
        (T ⊓ Subgroup.normalizer (V₁ : Set G)) (Sec1216Lv.lv L v) := by
  intro G _ _ T L V V₁ V₂ T₀ v c h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := c.S.ctx.hVe.1
  set T₁ := T ⊓ Subgroup.normalizer (V₁ : Set G) with hT₁
  obtain ⟨ι⟩ := c.S.ctx.hyp.iso
  have hρk : c.S.C₁.ρ.ker = CFSG.pCore 2 ↥L := c.S.C₁.ker_eq (by norm_num) ι
  have hρs : Function.Surjective c.S.C₁.ρ := c.S.C₁.ρ_surj
  obtain ⟨t₀, ht₀, ht₀V⟩ := Sec121Swap.exists_mem_not_normalizer c.S.ctx.hyp c.S.ctx.hTL
  obtain ⟨hwU, hw1, hwT⟩ := c.conj_v_mem ht₀ ht₀V
  have hwV₂ : t₀ * v * t₀⁻¹ ∈ V₂ := hwU.1
  have hx₀ : c.S.C₁.E v ≠ 0 := c.S.x₀_ne
  have hf : c.S.C₂.E (t₀ * v * t₀⁻¹) ≠ 0 := fun h0 => hw1 (c.S.C₂.eq_one_of_E hwV₂ h0)
  have hxf : c.S.C₁.E v ⬝ᵥ c.S.C₂.E (t₀ * v * t₀⁻¹) = 0 := hwU.2
  obtain ⟨m, hm0, hm3⟩ := exists_adapted hx₀ hf hxf
  set α : ↥L →* SL4 := (MulAut.conj m⁻¹).toMonoidHom.comp c.S.C₁.ρ with hα
  have hαs : Function.Surjective α := by
    rw [hα, MonoidHom.coe_comp]
    exact (MulEquiv.surjective _).comp hρs
  have hαk : α.ker = CFSG.pCore 2 ↥L := by
    rw [hα, MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _), hρk]
  have hαm : ∀ l : ↥L, ((α l : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      ((m⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        ((c.S.C₁.ρ l : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
          ((m : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := fun l => by
    show ((m⁻¹ * c.S.C₁.ρ l * m⁻¹⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = _
    rw [inv_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hmm : ((m⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      ((m : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hmm' : ((m : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      ((m⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hcv : ∀ l : ↥L, (l : G) ∈ Subgroup.centralizer ({v} : Set G) ↔ α l ∈ FLc.QI 4 {1} := by
    intro l
    rw [c.S.mem_centralizer_iff, VecStab.mem_vecStab, ← mulVec_e0_iff, hαm,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hm0]
    constructor
    · intro h
      rw [h, ← hm0, Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]
    · intro h
      calc ((c.S.C₁.ρ l : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c.S.C₁.E v
          = (((m : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
              ((m⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2))) *ᵥ
              (((c.S.C₁.ρ l : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c.S.C₁.E v) := by
            rw [hmm', Matrix.one_mulVec]
        _ = ((m : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
              (((m⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
                (((c.S.C₁.ρ l : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c.S.C₁.E v)) :=
            (Matrix.mulVec_mulVec _ _ _).symm
        _ = c.S.C₁.E v := by rw [h, hm0]
  have hcw : ∀ l : ↥L, (l : G) ∈ Subgroup.centralizer ({t₀ * v * t₀⁻¹} : Set G) ↔
      α l ∈ FLc.QI 4 {3} := by
    intro l
    rw [c.mem_centralizer_iff₂ hwV₂, c.S.hd l, ← transpose_mulVec_e3_iff, hαm]
    have hgr : ((slGraphAut 4 (ZMod 2) (c.S.C₁.ρ l) : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        (((c.S.C₁.ρ l)⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ :=
      Matrix.SpecialLinearGroup.coe_transpose _
    have hinvT : ∀ y : Fin 4 → ZMod 2, ((m⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ
        (((m : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ y) = y := fun y => by
      rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hmm', Matrix.transpose_one,
        Matrix.one_mulVec]
    rw [hgr, inv_transpose_mulVec_iff, Matrix.transpose_mul, Matrix.transpose_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hm3, hinvT]
    constructor
    · intro h
      rw [h]
    · intro h
      have h2 := congrArg (fun y => ((m⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ y) h
      rwa [hinvT, hinvT] at h2
  have hLC1 : L ⊓ Subgroup.centralizer ({v} : Set G) = liftPre α (FLc.QI 4 {1}) := by
    ext x
    constructor
    · rintro ⟨hxL, hxv⟩
      exact mem_liftPre_iff.mpr ⟨hxL, (hcv ⟨x, hxL⟩).mp hxv⟩
    · intro hx
      obtain ⟨hxL, hxQ⟩ := mem_liftPre_iff.mp hx
      exact ⟨hxL, (hcv ⟨x, hxL⟩).mpr hxQ⟩
  have hLC3 : L ⊓ Subgroup.centralizer ({t₀ * v * t₀⁻¹} : Set G) =
      liftPre α (FLc.QI 4 {3}) := by
    ext x
    constructor
    · rintro ⟨hxL, hxv⟩
      exact mem_liftPre_iff.mpr ⟨hxL, (hcw ⟨x, hxL⟩).mp hxv⟩
    · intro hx
      obtain ⟨hxL, hxQ⟩ := mem_liftPre_iff.mp hx
      exact ⟨hxL, (hcw ⟨x, hxL⟩).mpr hxQ⟩
  have hY1 : Sec1216Lv.lv L v = liftCore α (FLc.QI 4 {1}) := by
    rw [Sec1216Lv.lv, hLC1]
    rfl
  have hmapC : (L ⊓ Subgroup.centralizer ({v} : Set G)).map (MulAut.conj t₀).toMonoidHom =
      L ⊓ Subgroup.centralizer ({t₀ * v * t₀⁻¹} : Set G) := by
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have htL := c.S.ctx.hTL ht₀
    constructor
    · rintro ⟨hxL, hxv⟩
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp htL _).mp hxL
        simpa [mul_assoc] using this
      · have hxv' : t₀⁻¹ * x * t₀ ∈ Subgroup.centralizer ({v} : Set G) := hxv
        rw [Subgroup.mem_centralizer_singleton_iff] at hxv'
        show x ∈ Subgroup.centralizer ({t₀ * v * t₀⁻¹} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc x * (t₀ * v * t₀⁻¹) = t₀ * ((t₀⁻¹ * x * t₀) * v) * t₀⁻¹ := by group
          _ = t₀ * (v * (t₀⁻¹ * x * t₀)) * t₀⁻¹ := by rw [hxv']
          _ = t₀ * v * t₀⁻¹ * x := by group
    · rintro ⟨hxL, hxw⟩
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem htL) _).mp hxL
        simpa [mul_assoc] using this
      · have hxw' : x ∈ Subgroup.centralizer ({t₀ * v * t₀⁻¹} : Set G) := hxw
        rw [Subgroup.mem_centralizer_singleton_iff] at hxw'
        show t₀⁻¹ * x * t₀ ∈ Subgroup.centralizer ({v} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc t₀⁻¹ * x * t₀ * v = t₀⁻¹ * (x * (t₀ * v * t₀⁻¹)) * t₀ := by group
          _ = t₀⁻¹ * ((t₀ * v * t₀⁻¹) * x) * t₀ := by rw [hxw']
          _ = v * (t₀⁻¹ * x * t₀) := by group
  have hY3 : (liftCore α (FLc.QI 4 {1})).map (MulAut.conj t₀).toMonoidHom =
      liftCore α (FLc.QI 4 {3}) := by
    rw [← hY1, Sec1216Lv.lv, map_perfectCore, hmapC, hLC3]
    rfl
  have hKG : KGH91.Setting G T L V V₁ V₂ 4 := ⟨c.S.ctx.hyp, c.S.C₁, c.S.C₂, c.S.hd⟩
  have hD : Case4Count.Data G T L T₁ α := by
    refine ⟨c.S.ctx.hTL, c.S.ctx.hyp.sylow.1, hαs, hαk, inf_le_left, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hOL := setup121Q_holds G T L V V₁ V₂ 4 c.S.ctx.hyp c.S.ctx.hTL
      rw [qL, hOL]
      exact inf_le_inf_left _ ((Subgroup.centralizer_le (by exact_mod_cast c.S.ctx.V₁_le)).trans
        (Subgroup.centralizer_le_normalizer _))
    · intro t ht
      have htL := c.S.ctx.hTL ht.1
      have ht₂ : t ∈ Subgroup.normalizer (V₂ : Set G) :=
        OperatorJH.mem_normalizer_of_conj_mem_of fun x hx => c.S.ctx.conj_V₂ htL ht.2 hx
      obtain ⟨l, hl, hlV⟩ := hKG.exists_eq_conj htL ht.2 ht₂
      refine ⟨l, hl, l⁻¹ * t, ?_, by group⟩
      refine Case4Count.mem_qL_of_central c.S.ctx.hTL c.S.ctx.hyp.sylow.1 hρs hρk
        ((L ⊔ T).mul_mem (Subgroup.mem_sup_left (L.inv_mem hl)) (Subgroup.mem_sup_right ht.1))
        fun x hx => ?_
      have hcV : ∀ a ∈ V, (l⁻¹ * t) * a * (l⁻¹ * t)⁻¹ = a := fun a ha => by
        have e : (l⁻¹ * t) * a * (l⁻¹ * t)⁻¹ = l⁻¹ * (t * a * t⁻¹) * l := by group
        rw [e, hlV a ha]
        group
      have hcVinv : ∀ a ∈ V, (l⁻¹ * t)⁻¹ * a * (l⁻¹ * t) = a := fun a ha => by
        have h1 := hcV a ha
        calc (l⁻¹ * t)⁻¹ * a * (l⁻¹ * t) =
            (l⁻¹ * t)⁻¹ * ((l⁻¹ * t) * a * (l⁻¹ * t)⁻¹) * (l⁻¹ * t) := by rw [h1]
          _ = a := by group
      have hcL : l⁻¹ * t ∈ Subgroup.normalizer (L : Set G) :=
        (Subgroup.normalizer _).mul_mem (Subgroup.le_normalizer (L.inv_mem hl)) htL
      have hmem : (l⁻¹ * t) * x * (l⁻¹ * t)⁻¹ * x⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.mp hcL x).mp hx) (L.inv_mem hx)
      have hfix : ∀ a ∈ V₁, ((⟨_, hmem⟩ : ↥L) : G) * a * ((⟨_, hmem⟩ : ↥L) : G)⁻¹ = a := by
        intro a ha
        have hxa : x⁻¹ * a * x⁻¹⁻¹ ∈ V₁ :=
          (Subgroup.mem_normalizer_iff.mp (c.S.ctx.hyp.norm₁ (L.inv_mem hx)) a).mp ha
        have hxaV : x⁻¹ * a * x ∈ V := by
          have := c.S.ctx.V₁_le hxa
          simpa using this
        show (l⁻¹ * t) * x * (l⁻¹ * t)⁻¹ * x⁻¹ * a * ((l⁻¹ * t) * x * (l⁻¹ * t)⁻¹ * x⁻¹)⁻¹ = a
        have e : (l⁻¹ * t) * x * (l⁻¹ * t)⁻¹ * x⁻¹ * a * ((l⁻¹ * t) * x * (l⁻¹ * t)⁻¹ * x⁻¹)⁻¹ =
            (l⁻¹ * t) * (x * ((l⁻¹ * t)⁻¹ * (x⁻¹ * a * x) * (l⁻¹ * t)) * x⁻¹) * (l⁻¹ * t)⁻¹ := by
          group
        rw [e, hcVinv _ hxaV]
        have e2 : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
        rw [e2, hcV a (c.S.ctx.V₁_le ha)]
      have h1 := rho_eq_one c.S.C₁ hfix
      have h2 : (⟨_, hmem⟩ : ↥L) ∈ c.S.C₁.ρ.ker := h1
      rw [hρk, Lem3328.mem_pCore_iff] at h2
      exact h2
    · intro l hl
      exact (hcv l).mp (c.S.ctx.T₁_le hl)
    · intro l hl
      refine (hcw l).mp ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hwT l hl
      calc (l : G) * (t₀ * v * t₀⁻¹) =
          ((l : G) * (t₀ * v * t₀⁻¹) * (l : G)⁻¹) * l := by group
        _ = t₀ * v * t₀⁻¹ * (l : G) := by rw [this]
    · rw [← hY1]
      exact c.S.T₁_le_normalizer_lv
    · have h1 : T₁ ≤ Subgroup.normalizer (Sec1216Lv.lv L (t₀ * v * t₀⁻¹) : Set G) :=
        Sec1216Lv.le_normalizer_lv c.S.ctx.T₁_le_NL fun s hs => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have := hwT s hs
          calc s * (t₀ * v * t₀⁻¹) = (s * (t₀ * v * t₀⁻¹) * s⁻¹) * s := by group
            _ = t₀ * v * t₀⁻¹ * s := by rw [this]
      have h2 : Sec1216Lv.lv L (t₀ * v * t₀⁻¹) = liftCore α (FLc.QI 4 {3}) := by
        rw [Sec1216Lv.lv, hLC3]
        rfl
      rwa [h2] at h1
  rw [hY1] at h4
  exact hD.not_case4MinW ht₀ (c.T_le_normalizer_T₁ ht₀) hY3 h4

end CFSG.Quasithin.H13.Sec1214
