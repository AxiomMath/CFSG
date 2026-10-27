module

public import CFSG.Quasithin.MS93.S4A43XG
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section DualCount

private noncomputable abbrev f2HomCommGroup (P : Type*) [MulOneClass P] :
    CommGroup (P →* Multiplicative (ZMod 2)) :=
  MonoidHom.instCommGroup

attribute [local instance] f2HomCommGroup

private noncomputable def evalHom {P : Type*} [Group P]
    (R : Subgroup (P →* Multiplicative (ZMod 2))) : P →* DualGrp ↥R where
  toFun v :=
    { toFun := fun f => (f : P →* Multiplicative (ZMod 2)) v
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  map_one' := by
    refine DualGrp.ext fun f => ?_
    exact map_one (f : P →* Multiplicative (ZMod 2))
  map_mul' a b := by
    refine DualGrp.ext fun f => ?_
    exact map_mul (f : P →* Multiplicative (ZMod 2)) a b

private theorem index_le_card_of_forall {P : Type*} [Group P] [Finite P]
    (R : Subgroup (P →* Multiplicative (ZMod 2))) {K : Subgroup P}
    (hK : ∀ v, v ∈ K ↔ ∀ f ∈ R, f v = 1) : K.index ≤ Nat.card ↥R := by
  have hker : (evalHom R).ker = K := by
    ext v
    rw [MonoidHom.mem_ker, hK]
    constructor
    · intro hv f hf
      exact DFunLike.congr_fun hv ⟨f, hf⟩
    · intro hv
      exact DualGrp.ext fun f => hv f.1 f.2
  have : Finite (P →* Multiplicative (ZMod 2)) :=
    Finite.of_injective _ DFunLike.coe_injective
  have hsq : ∀ f : ↥R, f ^ 2 = 1 := fun f => by
    have h2 : ∀ m : Multiplicative (ZMod 2), m ^ 2 = 1 := by decide
    apply Subtype.ext
    refine MonoidHom.ext fun v => ?_
    exact h2 _
  rw [← hker, Subgroup.index_ker, ← card_dualGrp hsq]
  exact Subgroup.card_le_card_group _

end DualCount

section Index

variable {G : Type} [Group G] {K V Z : Subgroup G} {F : Type} [Field F]
  {φ : ↥K →* ↥(StatedSL 3 F)}

private theorem relIndex_eq_of_isSum' (h : IsSumOfNaturalModulesVia K V Z φ false 1) :
    Z.relIndex V = Nat.card F ^ 3 := by
  have hker : (secHom h).ker = Z.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, secHom_apply, ofAdd_eq_one, secVec_eq_zero_iff,
      Subgroup.mem_subgroupOf]
  have hsurj : Function.Surjective (secHom h) := by
    intro y
    obtain ⟨v, hv⟩ := secVec_surjective h (Multiplicative.toAdd y)
    exact ⟨v, by rw [secHom_apply, hv]; rfl⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
    Subgroup.card_top]
  change Nat.card (Fin 3 → F) = _
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

end Index

section Vcirc

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)

theorem stab_le_normalizer_vcirc_sup_zm (μ : Vtx (puAmalgam h.le)) :
    stab (puAmalgam h.le) μ ≤ Subgroup.normalizer ((Vcirc h.le L μ ⊔ ZM (puAmalgam h.le) μ :
      Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) :=
  (le_inf (le_normalizer_commutator (stab_le_normalizer_vv h μ) (stab_le_normalizer_ltil h μ))
    (stab_le_normalizer_zm _ μ)).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)

end Vcirc

namespace Ctx43

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx43 h φ)
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem commutator_vv_stab_le {μ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) :
    ⁅Vv 𝔛 μ, stab 𝔛 μ⁆ ≤ Vcirc h.le L μ ⊔ ZM 𝔛 μ := by
  have hn := stab_le_normalizer_vcirc_sup_zm h μ
  rw [stab_eq_ltil_sup_qv h c.full hμ, Subgroup.commutator_comm]
  refine S4A.commutator_sup_le_of ?_ ?_ ((ltil_le_stab h μ).trans hn) ((qv_le_stab _ μ).trans hn)
  · rw [Subgroup.commutator_comm]
    exact le_sup_left
  · rw [Subgroup.commutator_comm]
    exact (c.commutator_vv_qv_le_zm hμ).trans le_sup_right

theorem false_of_commutator_vcirc_eq_bot {μ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) {Y : Subgroup 𝔘}
    (hYQ : Y ≤ Qv 𝔛 μ) (hY : Y.relIndex (Qv 𝔛 μ) ≤ Fintype.card F ^ 2)
    (hc : ⁅Vcirc h.le L μ, Y⁆ = ⊥) : False := by
  obtain ⟨μ', hs⟩ := c.star_at hμ
  have hb6 := c.b6
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  obtain ⟨F', _, _, ψ', hcard, hsurj, hnat, -, -, -, -⟩ :=
    isC1_normal h c.full c.hb hμ (c.isC1 hμ)
  set P : Subgroup 𝔘 := ⁅Vv 𝔛 μ, stab 𝔛 μ⁆ ⊔ ZM 𝔛 μ with hP
  set K : Subgroup 𝔘 := ⁅Vv 𝔛 μ, Qv 𝔛 μ⁆ ⊔ ZM 𝔛 μ with hK
  have hVQZ : ⁅Vv 𝔛 μ, Qv 𝔛 μ⁆ ≤ ZM 𝔛 μ := c.commutator_vv_qv_le_zm hμ
  have hKZ : K = ZM 𝔛 μ := le_antisymm (sup_le hVQZ le_rfl) le_sup_right
  have hVn := stab_le_normalizer_vv h μ
  have hVs : Vv 𝔛 μ ≤ stab 𝔛 μ := (vv_le_qv h c.hb hμ).trans (qv_le_stab _ μ)
  have hPV : P ≤ Vv 𝔛 μ :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hVn) (zm_le_vv h hμ)
  have hPs : P ≤ stab 𝔛 μ := hPV.trans hVs
  have hPle : P ≤ Vcirc h.le L μ ⊔ ZM 𝔛 μ := sup_le (c.commutator_vv_stab_le hμ) le_sup_right
  have hVcP : Vcirc h.le L μ ≤ P :=
    (Subgroup.commutator_mono le_rfl (ltil_le_stab h μ)).trans le_sup_left
  have hPY : ⁅P, Y⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine (Subgroup.commutator_mono hPle le_rfl).trans ?_
    have hbot : ∀ S : Subgroup 𝔘, S ≤ Subgroup.normalizer ((⊥ : Subgroup 𝔘) : Set 𝔘) := by
      intro S
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
    refine S4A.commutator_sup_le_of hc.le ?_ (hbot _) (hbot _)
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((zm_le_centralizer_qv _ h.hyp20 hμ).trans (Subgroup.centralizer_le hYQ))).le
  have hmem : ∀ v ∈ P, ∀ t ∈ Qv 𝔛 μ, ⁅v, t⁆ ∈ Zloc h.le L μ := fun v hv t ht =>
    c.commutator_vv_qv_le_zloc hμ (Subgroup.commutator_mem_commutator (hPV hv) ht)
  have hcen : ∀ x ∈ Zloc h.le L μ, ∀ g ∈ stab 𝔛 μ, g * x * g⁻¹ = x := fun x hx g hg => by
    rw [((mem_stabCenter_iff_comm _).mp (c.zloc_le_stabCenter hμ hx)).2 g hg,
      mul_inv_cancel_right]
  have hZloc : Zloc h.le L μ ≤ ZM 𝔛 μ := by
    rw [Zloc, h.puTrans_Zq hμ, xm_eq_zm h c.full hμ]
    exact inf_le_left
  have hEab := isElemAbelian_zm _ h.hyp20 h.critDist_pos hμ
  obtain ⟨v₀, hv₀, t₀, ht₀, hne⟩ :
      ∃ v₀ ∈ Vcirc h.le L μ, ∃ t₀ ∈ Qv 𝔛 μ, ⁅v₀, t₀⁆ ≠ 1 := by
    by_contra hall
    push Not at hall
    have hH : Hloc h.le L μ = ⊥ := by
      rw [Hloc, eq_bot_iff, Subgroup.commutator_le]
      intro v hv t ht
      rw [hall v hv t ht]
      exact Subgroup.one_mem _
    have hHq := (c.c431B μ μ' hs).2.1
    rw [hH, Subgroup.card_bot] at hHq
    nlinarith
  let iE : CommGroup ↥(Zloc h.le L μ) :=
    { (inferInstance : Group ↥(Zloc h.le L μ)) with
      mul_comm := fun a b => by
        have := hEab.1.is_comm.comm ⟨a, hZloc a.2⟩ ⟨b, hZloc b.2⟩
        exact Subtype.ext (show (a : 𝔘) * b = b * a from congrArg Subtype.val this) }
  have hE2 : ∀ e : ↥(Zloc h.le L μ), e ^ 2 = 1 := fun e =>
    Subtype.ext (by simpa using hEab.2 e (hZloc e.2))
  obtain ⟨χ, hχ⟩ := exists_dualChar_ne_one hE2
    (x := ⟨⁅v₀, t₀⁆, hmem v₀ (hVcP hv₀) t₀ ht₀⟩)
    (fun h1 => hne (congrArg Subtype.val h1))
  have hcomm_mul_left : ∀ (v w : ↥P) (t : ↥(Qv 𝔛 μ)),
      ⁅((v * w : ↥P) : 𝔘), (t : 𝔘)⁆ = ⁅(w : 𝔘), (t : 𝔘)⁆ * ⁅(v : 𝔘), (t : 𝔘)⁆ := by
    intro v w t
    rw [Subgroup.coe_mul, commutatorElement_mul_left_eq,
      hcen _ (hmem w w.2 t t.2) v (hPs v.2)]
  have hcomm_mul_right : ∀ (v : ↥P) (t s : ↥(Qv 𝔛 μ)),
      ⁅(v : 𝔘), ((t * s : ↥(Qv 𝔛 μ)) : 𝔘)⁆ = ⁅(v : 𝔘), (t : 𝔘)⁆ * ⁅(v : 𝔘), (s : 𝔘)⁆ := by
    intro v t s
    have e : ⁅(v : 𝔘), ((t * s : ↥(Qv 𝔛 μ)) : 𝔘)⁆ =
        ⁅(v : 𝔘), (t : 𝔘)⁆ * ((t : 𝔘) * ⁅(v : 𝔘), (s : 𝔘)⁆ * (t : 𝔘)⁻¹) := by
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group
    rw [e, hcen _ (hmem v v.2 s s.2) t (qv_le_stab _ μ t.2)]
  let θ : ↥(Qv 𝔛 μ) → (↥P →* Multiplicative (ZMod 2)) := fun t =>
    { toFun := fun v => χ ⟨⁅(v : 𝔘), (t : 𝔘)⁆, hmem v v.2 t t.2⟩
      map_one' := by
        have : (⟨⁅((1 : ↥P) : 𝔘), (t : 𝔘)⁆, hmem 1 (1 : ↥P).2 t t.2⟩ :
            ↥(Zloc h.le L μ)) = 1 := Subtype.ext (by simp)
        rw [this, map_one]
      map_mul' := fun v w => by
        have : (⟨⁅((v * w : ↥P) : 𝔘), (t : 𝔘)⁆, hmem _ (v * w).2 t t.2⟩ :
            ↥(Zloc h.le L μ)) = ⟨_, hmem w w.2 t t.2⟩ * ⟨_, hmem v v.2 t t.2⟩ :=
          Subtype.ext (hcomm_mul_left v w t)
        rw [this, map_mul, mul_comm] }
  have hθ : ∀ t v, θ t v = χ ⟨⁅(v : 𝔘), (t : 𝔘)⁆, hmem v v.2 t t.2⟩ := fun _ _ => rfl
  let Θ : ↥(Qv 𝔛 μ) →* (↥P →* Multiplicative (ZMod 2)) :=
    { toFun := θ
      map_one' := by
        refine MonoidHom.ext fun v => ?_
        rw [hθ]
        have : (⟨⁅(v : 𝔘), ((1 : ↥(Qv 𝔛 μ)) : 𝔘)⁆, hmem v v.2 1 (1 : ↥(Qv 𝔛 μ)).2⟩ :
            ↥(Zloc h.le L μ)) = 1 := Subtype.ext (by simp)
        rw [this, map_one]
        rfl
      map_mul' := fun t s => by
        refine MonoidHom.ext fun v => ?_
        rw [MonoidHom.mul_apply, hθ, hθ, hθ]
        have : (⟨⁅(v : 𝔘), ((t * s : ↥(Qv 𝔛 μ)) : 𝔘)⁆, hmem v v.2 _ (t * s).2⟩ :
            ↥(Zloc h.le L μ)) = ⟨_, hmem v v.2 t t.2⟩ * ⟨_, hmem v v.2 s s.2⟩ :=
          Subtype.ext (hcomm_mul_right v t s)
        rw [this, map_mul] }
  have hΘ : ∀ t v, Θ t v = χ ⟨⁅(v : 𝔘), (t : 𝔘)⁆, hmem v v.2 t t.2⟩ := fun _ _ => rfl
  have hfinQ : Finite ↥(Qv 𝔛 μ) := by
    have hρ := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
    have := finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hρ]; exact hμ)
    exact Finite.of_injective _ (Subgroup.inclusion_injective (qv_le_qv _ h.hyp20 hμ hρ))
  have hR : Nat.card ↥Θ.range ≤ Fintype.card F ^ 2 := by
    rw [← Subgroup.index_ker]
    refine le_trans ?_ hY
    have hle : Y.subgroupOf (Qv 𝔛 μ) ≤ Θ.ker := by
      intro y hy
      rw [Subgroup.mem_subgroupOf] at hy
      rw [MonoidHom.mem_ker]
      refine MonoidHom.ext fun v => ?_
      rw [hΘ]
      have : (⟨⁅(v : 𝔘), (y : 𝔘)⁆, hmem v v.2 y y.2⟩ : ↥(Zloc h.le L μ)) = 1 := by
        refine Subtype.ext ?_
        have := Subgroup.commutator_mem_commutator v.2 hy
        rw [hPY] at this
        exact this
      rw [this, map_one]
      rfl
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hle)
  have hKP : K ≤ P := hKZ ▸ le_sup_right
  have hKA : ∀ v : ↥P, (v : 𝔘) ∈ K → ∀ t, Θ t v = 1 := by
    intro v hv t
    rw [hΘ]
    have : (⟨⁅(v : 𝔘), (t : 𝔘)⁆, hmem v v.2 t t.2⟩ : ↥(Zloc h.le L μ)) = 1 := by
      refine Subtype.ext ?_
      rw [hKZ] at hv
      have := Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h.hyp20 hμ hv) t t.2
      change ⁅(v : 𝔘), (t : 𝔘)⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact this.symm
    rw [this, map_one]
  have hv₀A : ¬ ∀ t, Θ t ⟨v₀, hVcP hv₀⟩ = 1 := fun hall => hχ (hall ⟨t₀, ht₀⟩)
  have hker : ∀ v : ↥P, v ∈ K.subgroupOf P ↔ ∀ f ∈ Θ.range, f v = 1 := by
    intro v
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro hv _ ⟨t, rfl⟩
      exact hKA v hv t
    · intro hv
      have hvA : ∀ t, Θ t v = 1 := fun t => hv _ ⟨t, rfl⟩
      by_contra hvK
      apply hv₀A
      let S : AddSubgroup (Fin 3 → F') :=
        { carrier := {x | ∃ w : ↥P, (∀ t, Θ t w = 1) ∧ secVec hnat w = x}
          add_mem' := by
            rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
            refine ⟨w * w', fun t => ?_, secVec_mul hnat w w'⟩
            rw [map_mul, hw t, hw' t, one_mul]
          zero_mem' := ⟨1, fun t => map_one _, by
            have := secVec_mul hnat 1 1
            rw [mul_one] at this
            simpa using this⟩
          neg_mem' := by
            rintro _ ⟨w, hw, rfl⟩
            exact ⟨w⁻¹, fun t => by rw [map_inv, hw t, inv_one], secVec_inv hnat w⟩ }
      have hSinv : ∀ (g : SL3 F'), ∀ x ∈ S,
          ((g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ x ∈ S := by
        rintro g _ ⟨w, hw, rfl⟩
        obtain ⟨a, rfl⟩ := toSL3_surjective hsurj g
        have hwa : (a : 𝔘) * w * (a : 𝔘)⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp (hnat.1 a.2) w).mp w.2
        refine ⟨⟨_, hwa⟩, fun t => ?_, (secVec_conj hnat a w ⟨_, hwa⟩ rfl)⟩
        have hta : (a : 𝔘)⁻¹ * t * (a : 𝔘) ∈ Qv 𝔛 μ := by
          have := (Subgroup.mem_normalizer_iff.mp
            (stab_le_normalizer_qv _ μ (Subgroup.inv_mem _ a.2)) t).mp t.2
          simpa using this
        have h1 := hw ⟨_, hta⟩
        rw [hΘ] at h1 ⊢
        have e : ⁅(a : 𝔘) * w * (a : 𝔘)⁻¹, (t : 𝔘)⁆ = ⁅(w : 𝔘), (a : 𝔘)⁻¹ * t * (a : 𝔘)⁆ := by
          have e1 : ⁅(a : 𝔘) * w * (a : 𝔘)⁻¹, (t : 𝔘)⁆ =
              (a : 𝔘) * ⁅(w : 𝔘), (a : 𝔘)⁻¹ * t * (a : 𝔘)⁆ * (a : 𝔘)⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [e1, hcen _ (hmem w w.2 _ hta) a a.2]
        have : (⟨⁅(a : 𝔘) * w * (a : 𝔘)⁻¹, (t : 𝔘)⁆, hmem _ hwa t t.2⟩ :
            ↥(Zloc h.le L μ)) = ⟨⁅(w : 𝔘), (a : 𝔘)⁻¹ * t * (a : 𝔘)⁆, hmem w w.2 _ hta⟩ :=
          Subtype.ext e
        rw [this]
        exact h1
      have hx₁ : secVec hnat v ∈ S := ⟨v, hvA, rfl⟩
      have hx₁0 : secVec hnat v ≠ 0 := fun h0 => hvK ((secVec_eq_zero_iff hnat v).mp h0)
      by_cases h0 : secVec hnat ⟨v₀, hVcP hv₀⟩ = 0
      · exact hKA _ ((secVec_eq_zero_iff hnat _).mp h0)
      obtain ⟨w, hw, hwv⟩ := mem_of_forall_mulVec_mem hSinv hx₁ hx₁0 h0
      have hdiff : secVec hnat (⟨v₀, hVcP hv₀⟩ * w⁻¹) = 0 := by
        rw [secVec_mul, secVec_inv, hwv, add_neg_cancel]
      have hk := hKA _ ((secVec_eq_zero_iff hnat _).mp hdiff)
      intro t
      have e : (⟨v₀, hVcP hv₀⟩ : ↥P) = (⟨v₀, hVcP hv₀⟩ * w⁻¹) * w := by group
      rw [e, map_mul, hk t, hw t, one_mul]
  have hfinP : Finite ↥P := by
    have hρ := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
    have := finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hρ]; exact hμ)
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      ((hPV.trans (vv_le_qv h c.hb hμ)).trans (qv_le_qv _ h.hyp20 hμ hρ)))
  have h3 := index_le_card_of_forall Θ.range hker
  rw [← Subgroup.relIndex, relIndex_eq_of_isSum' hnat, Nat.card_eq_fintype_card, hcard] at h3
  have := h3.trans hR
  have hq2 : Fintype.card F ^ 2 < Fintype.card F ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
  omega

private theorem uloc_inf_dloc' (μ : Vtx 𝔛) : Uloc h.le L μ ⊓ Dloc h.le L μ = ⊥ := by
  have hUD : Uq M T L ⊓ Dq M L = ⊥ := by
    rw [h.Uq_inf_Dq, ← h.Uq_inf_Zq, inf_comm]
    exact c.via.2.2.2.1
  rw [Uloc, Dloc, ← puTrans_inf, hUD, puTrans, Subgroup.bot_subgroupOf, transN_bot]

theorem card_uloc {μ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) :
    Nat.card ↥(Uloc h.le L μ) = Fintype.card F ^ 3 := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hμ
  rw [← Subgroup.relIndex_bot_left, relIndex_eq_of_isSum' hψ, Nat.card_eq_fintype_card]

theorem mem_nablaSet_of_mem_nablaSet {α μ : Vtx 𝔛} (hα : IsMVtx 𝔛 α)
    (hd : (puAmalgam h.le).treeGraph.dist α μ = 2) (hαμ : α ∈ nablaSet h.le L μ) :
    μ ∈ nablaSet h.le L α := by
  obtain ⟨α', hs⟩ := c.star_at hα
  have hb6 := c.b6
  refine ⟨hd, fun hZB => ?_⟩
  have hαρ : 𝔄 α (geo 𝔛 α μ 1) := adj_geo_one _ (by omega)
  have hρμ : 𝔄 (geo 𝔛 α μ 1) μ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := μ) (i := 1) (by omega)
    rwa [show geo 𝔛 α μ (1 + 1) = μ from geo_of_le _ (by omega)] at this
  set ρ := geo 𝔛 α μ 1 with hρ
  have hρH : ¬ IsMVtx 𝔛 ρ := by rw [← isMVtx_iff_of_adj _ hαρ]; exact hα
  have hμM : IsMVtx 𝔛 μ := by have := isMVtx_iff_of_adj _ hρμ; tauto
  rw [zv_of_isMVtx _ hμM] at hZB
  have hρgeo : geo 𝔛 μ α 1 = ρ :=
    (eq_geo_one _ hρμ.symm (by rw [dist_eq_one_of_adj _ hαρ.symm, tdist_comm, hd])).symm
  have hZV : ZM 𝔛 μ ≤ Vv 𝔛 α := by rw [← zv_of_isMVtx _ hμM]; exact zv_le_vv h hd.le
  have hNn : stab 𝔛 α ≤ Subgroup.normalizer ((ZM 𝔛 μ ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘) := by
    rw [stab_eq_ltil_sup_qv h c.full hα]
    refine sup_le ?_ ?_
    · exact le_normalizer_sup_of_comm_le ((ltil_le_stab h _).trans (stab_le_normalizer_zm _ _))
        (((Subgroup.commutator_mono hZB le_rfl).trans (commutator_bloc_le h c.hb hα)).trans
          le_sup_right)
    · exact le_normalizer_sup_of_comm_le ((qv_le_stab _ _).trans (stab_le_normalizer_zm _ _))
        (((Subgroup.commutator_mono hZV le_rfl).trans (c.commutator_vv_qv_le_zm hα)).trans
          le_sup_right)
  set Y : Subgroup 𝔘 :=
    Qv 𝔛 α ⊓ Subgroup.centralizer ((ZM 𝔛 μ ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘) with hYdef
  have hYn : stab 𝔛 α ≤ Subgroup.normalizer (Y : Set 𝔘) :=
    (le_inf (stab_le_normalizer_qv _ α)
      (hNn.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer _))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf)
  have hQαρ : Qv 𝔛 α ≤ Qv 𝔛 ρ := qv_le_qv _ h.hyp20 hα hαρ
  have hYμ : Y ≤ Qv 𝔛 μ := by
    rw [← c.cent μ ρ hμM hρμ.symm]
    exact le_inf (inf_le_left.trans hQαρ) (inf_le_right.trans
      (Subgroup.centralizer_le (le_sup_left : ZM 𝔛 μ ≤ ZM 𝔛 μ ⊔ ZM 𝔛 α)))
  have hQQY : Qv 𝔛 α ⊓ Qv 𝔛 μ ≤ Y := by
    refine le_inf inf_le_left ?_
    rw [Subgroup.le_centralizer_iff]
    exact sup_le ((zm_le_centralizer_qv _ h.hyp20 hμM).trans (Subgroup.centralizer_le inf_le_right))
      ((zm_le_centralizer_qv _ h.hyp20 hα).trans (Subgroup.centralizer_le inf_le_left))
  have hfinρ := finite_qv _ h.hyp20 hρH
  have hYi : Y.relIndex (Qv 𝔛 μ) ≤ Fintype.card F ^ 2 := by
    have hQμρ : Qv 𝔛 μ ≤ Qv 𝔛 ρ := qv_le_qv _ h.hyp20 hμM hρμ.symm
    have hfinμ : Finite ↥(Qv 𝔛 μ) := Finite.of_injective _ (Subgroup.inclusion_injective hQμρ)
    refine (Subgroup.relIndex_le_of_le_left hQQY ?_).trans ?_
    · rw [Subgroup.inf_relIndex_right]
      exact Subgroup.index_ne_zero_of_finite
    · rw [Subgroup.inf_relIndex_right, ← c.relIndex_qv hα hαρ]
      exact Subgroup.relIndex_le_of_le_right hQμρ Subgroup.index_ne_zero_of_finite
  have hi := c.concl437_i hs hd hαμ
  have hVcμ : Vcirc h.le L μ ≤ Vv 𝔛 μ := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((ltil_le_stab h μ).trans (stab_le_normalizer_vv h μ))
  have hVcα : Vcirc h.le L α ≤ Vv 𝔛 α := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((ltil_le_stab h α).trans (stab_le_normalizer_vv h α))
  have hVcαn : stab 𝔛 α ≤ Subgroup.normalizer (Vcirc h.le L α : Set 𝔘) :=
    le_normalizer_commutator (stab_le_normalizer_vv h α) (stab_le_normalizer_ltil h α)
  have hVcμn : stab 𝔛 μ ≤ Subgroup.normalizer (Vcirc h.le L μ : Set 𝔘) :=
    le_normalizer_commutator (stab_le_normalizer_vv h μ) (stab_le_normalizer_ltil h μ)
  have hQαμ : Qv 𝔛 α ≤ stab 𝔛 μ := hQαρ.trans (qv_le_stab_of_adj _ hρμ)
  have hWn : stab 𝔛 α ≤
      Subgroup.normalizer ((Vcirc h.le L μ ⊔ Vcirc h.le L α : Subgroup 𝔘) : Set 𝔘) := by
    rw [stab_eq_ltil_sup_qv h c.full hα]
    refine sup_le ?_ ?_
    · exact le_normalizer_sup_of_comm_le ((ltil_le_stab h α).trans hVcαn)
        ((Subgroup.commutator_mono hVcμ le_rfl).trans (hi.2.trans le_sup_right))
    · exact (le_inf (hQαμ.trans hVcμn) ((qv_le_stab _ α).trans hVcαn)).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  set X : Subgroup 𝔘 := ⁅Vcirc h.le L μ ⊔ Vcirc h.le L α, Y⁆ with hXdef
  have hXn : stab 𝔛 α ≤ Subgroup.normalizer (X : Set 𝔘) := le_normalizer_commutator hWn hYn
  have hHμ := (c.concl432 hμM).2 α hαμ
  rw [hρgeo] at hHμ
  have hHμU : Hloc h.le L μ ≤ Uloc h.le L α := hHμ.1 ▸ hHμ.2 ▸ c.usup_le_uloc hα hαρ
  have hHαD : Hloc h.le L α ≤ Dloc h.le L α :=
    (Subgroup.commutator_mono hVcα le_rfl).trans (c.concl432 hα).1
  have hHαZ : Hloc h.le L α ≤ ZM 𝔛 α :=
    (Subgroup.commutator_mono hVcα le_rfl).trans (c.commutator_vv_qv_le_zm hα)
  have hHZ : Hloc h.le L μ ⊔ Hloc h.le L α ≤ ZM 𝔛 α :=
    sup_le (hHμU.trans (uloc_le_zm h c.full hα)) hHαZ
  have hQαn : Qv 𝔛 α ≤ Subgroup.normalizer
      ((Hloc h.le L μ ⊔ Hloc h.le L α : Subgroup 𝔘) : Set 𝔘) :=
    le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp
      (hHZ.trans (zm_le_centralizer_qv _ h.hyp20 hα)))
  have hVμα : Vv 𝔛 μ ≤ Qv 𝔛 α :=
    vv_le_qv_of_dist h hμM (by rw [tdist_comm, hd]; omega)
  have hXH : X ≤ Hloc h.le L μ ⊔ Hloc h.le L α := by
    refine S4A.commutator_sup_le_of ?_ ?_ ((hVcμ.trans hVμα).trans hQαn)
      ((hVcα.trans (vv_le_qv h c.hb hα)).trans hQαn)
    · exact (Subgroup.commutator_mono le_rfl hYμ).trans le_sup_left
    · exact (Subgroup.commutator_mono le_rfl inf_le_left).trans le_sup_right
  have hDn : stab 𝔛 α ≤ Subgroup.normalizer (Dloc h.le L α : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) α
  have hUn : stab 𝔛 α ≤ Subgroup.normalizer (Uloc h.le L α : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α
  have hUs : Uloc h.le L α ≤ stab 𝔛 α := puTrans_le_stab h.le _ α
  have hUD := c.uloc_inf_dloc' α
  have hdec : ∀ x ∈ X, ∃ a ∈ Hloc h.le L μ, ∃ d ∈ Dloc h.le L α, a * d = x := by
    intro x hx
    have hx' : x ∈ ((Hloc h.le L μ ⊔ Dloc h.le L α : Subgroup 𝔘) : Set 𝔘) :=
      sup_le_sup_left hHαD _ (hXH hx)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((hHμU.trans hUs).trans hDn)] at hx'
    obtain ⟨a, ha, d, hd', rfl⟩ := hx'
    exact ⟨a, ha, d, hd', rfl⟩
  have hN' : (X ⊔ Dloc h.le L α) ⊓ Uloc h.le L α ≤ Hloc h.le L μ := by
    rintro x ⟨hxXD, hxU⟩
    have hx' : x ∈ ((Hloc h.le L μ ⊔ Dloc h.le L α : Subgroup 𝔘) : Set 𝔘) :=
      sup_le (hXH.trans (sup_le_sup_left hHαD _)) le_sup_right hxXD
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((hHμU.trans hUs).trans hDn)] at hx'
    obtain ⟨a, ha, d, hd', rfl⟩ := hx'
    have hdU : d ∈ Uloc h.le L α := by
      have : d = a⁻¹ * (a * d) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hHμU ha)) hxU
    have hd1 : d = 1 := by
      have : d ∈ Uloc h.le L α ⊓ Dloc h.le L α := ⟨hdU, hd'⟩
      rwa [hUD, Subgroup.mem_bot] at this
    change a * d ∈ _
    rw [hd1, mul_one]
    exact ha
  have hN'n : stab 𝔛 α ≤ Subgroup.normalizer
      (((X ⊔ Dloc h.le L α) ⊓ Uloc h.le L α : Subgroup 𝔘) : Set 𝔘) :=
    (le_inf ((le_inf hXn hDn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)) hUn).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hN'bot : (X ⊔ Dloc h.le L α) ⊓ Uloc h.le L α = ⊥ := by
    rcases c.eq_bot_or_eq_uloc hα inf_le_right hN'n with hb | hb
    · exact hb
    · exfalso
      have hle : Uloc h.le L α ≤ Usup 𝔛 α ρ := hb ▸ (hN'.trans (hHμ.1 ▸ hHμ.2 ▸ le_rfl))
      have hfinU : Finite ↥(Usup 𝔛 α ρ) := Finite.of_injective _ (Subgroup.inclusion_injective
        ((c.usup_le_zh hα hαρ).trans (zh_le_qv _ _)))
      have h1 := Subgroup.card_le_of_le hle
      rw [c.card_uloc hα, c.card_usup hα hαρ] at h1
      have hq : 1 < Fintype.card F := Fintype.one_lt_card
      have : Fintype.card F ^ 2 < Fintype.card F ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
      omega
  have hXD : X ≤ Dloc h.le L α := by
    intro x hx
    obtain ⟨a, ha, d, hd', rfl⟩ := hdec x hx
    have ha1 : a = 1 := by
      have : a ∈ (X ⊔ Dloc h.le L α) ⊓ Uloc h.le L α := by
        refine ⟨?_, hHμU ha⟩
        have : a = (a * d) * d⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
          (Subgroup.mem_sup_right (Subgroup.inv_mem _ hd'))
      rwa [hN'bot, Subgroup.mem_bot] at this
    rw [ha1, one_mul]
    exact hd'
  refine c.false_of_commutator_vcirc_eq_bot hμM hYμ hYi ?_
  rw [eq_bot_iff, ← hUD]
  refine le_inf ?_ ?_
  · exact (Subgroup.commutator_mono le_rfl hYμ).trans hHμU
  · exact (Subgroup.commutator_mono le_sup_left le_rfl).trans hXD

theorem nabla_symm {α μ : Vtx 𝔛} (hα : IsMVtx 𝔛 α)
    (hd : (puAmalgam h.le).treeGraph.dist α μ = 2) :
    μ ∈ nablaSet h.le L α ↔ α ∈ nablaSet h.le L μ := by
  have hμM : IsMVtx 𝔛 μ := by
    have := (even_dist_iff (puAmalgam h.le) α μ).mp (by rw [hd]; decide)
    tauto
  exact ⟨fun hμα => c.mem_nablaSet_of_mem_nablaSet hμM (by rw [tdist_comm, hd]) hμα,
    fun hαμ => c.mem_nablaSet_of_mem_nablaSet hα hd hαμ⟩

end Ctx43

end CFSG.Quasithin.MS93.S4A
