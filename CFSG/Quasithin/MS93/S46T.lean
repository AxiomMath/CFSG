module

public import CFSG.Quasithin.MS93.S46Stmt9
public import CFSG.Quasithin.MS93.S46Stmt12
public import CFSG.Quasithin.MS93.S46Rec
public import CFSG.Quasithin.MS93.S4AL3
public import CFSG.Quasithin.MS93.S46I464Lin
public import CFSG.Quasithin.MS93.S46I465
public import CFSG.Quasithin.MS93.S46LastAbs
public import CFSG.Quasithin.MS93.S4AFMain

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement Matrix

section Aux

variable {𝔾 : Type} [Group 𝔾]

private theorem le_normalizer_centerOf (V : Subgroup 𝔾) :
    V ≤ Subgroup.normalizer (centerOf V : Set 𝔾) := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro b
  have key : ∀ c ∈ centerOf V, ∀ u ∈ V, u * c * u⁻¹ = c := fun c hc u hu => by
    rw [Subgroup.mem_centralizer_iff.mp hc.2 u hu, mul_inv_cancel_right]
  constructor
  · intro hb
    rw [key b hb v hv]
    exact hb
  · intro hb
    have e : b = v⁻¹ * (v * b * v⁻¹) * v⁻¹⁻¹ := by group
    rw [e, key _ hb _ (V.inv_mem hv)]
    exact hb

private theorem relIndex_sup_eq {H N : Subgroup 𝔾} (h : H ≤ Subgroup.normalizer (N : Set 𝔾)) :
    N.relIndex (H ⊔ N) = N.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv.symm

variable {F : Type} [Field F]

theorem relIndex_eq_of_isSum [Finite F] {L V K : Subgroup 𝔾} {α : ↥L →* ↥(StatedSL 3 F)}
    {dual : Bool} (h : IsSumOfNaturalModulesVia L V K α dual 1) :
    K.relIndex V = Nat.card F ^ 3 := by
  set N := NatSec.ofIsSum h
  have hker : N.β.ker = K.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact N.ker v
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr N.surj,
    Subgroup.card_top, card_natMod]

theorem eq_zero_of_forall_dualMat_mulVec {c : Fin 3 → F}
    (h : ∀ g : SL3 F, dualMat g *ᵥ c = c) : c = 0 := by
  funext i
  obtain ⟨j, hij⟩ : ∃ j : Fin 3, i ≠ j := ⟨i + 1, by fin_cases i <;> decide⟩
  have h1 := congrFun (h (rootElt i j 1)) j
  rw [dualMat_rootElt_mulVec hij, Pi.add_apply, Pi.single_eq_same] at h1
  simpa using h1

theorem mem_z_of_forall_commutator_mem {K W Z Lt : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
    (hd : IsSumOfNaturalModulesVia K W Z ψ true 1)
    (hLt : ∀ g : SL3 F, ∃ l : ↥K, (l : 𝔾) ∈ Lt ∧ toSL3 ψ l = g) {x : 𝔾} (hx : x ∈ W)
    (hxl : ∀ l ∈ Lt, ⁅x, l⁆ ∈ Z) : x ∈ Z := by
  set N := NatSec.ofIsSum hd
  rw [← N.coord_eq_zero_iff hx]
  refine eq_zero_of_forall_dualMat_mulVec fun g => ?_
  obtain ⟨l, hl, rfl⟩ := hLt g
  have hlx : (l : 𝔾) * x⁻¹ * (l : 𝔾)⁻¹ ∈ W := N.conj_mem l (W.inv_mem hx)
  have e : ⁅x, (l : 𝔾)⁆ = x * ((l : 𝔾) * x⁻¹ * (l : 𝔾)⁻¹) := by
    simp only [commutatorElement_def]
    group
  have h0 := (N.coord_eq_zero_iff (W.mul_mem hx hlx)).mpr (e ▸ hxl l hl)
  rw [N.coord_mul hx hlx, N.coord_conj l (W.inv_mem hx), N.coord_inv hx, natAct_true,
    Matrix.mulVec_neg] at h0
  exact (add_neg_eq_zero.mp h0).symm

theorem natImage_conjSL {K : Subgroup 𝔾} (s : SL3 F) (φ : ↥K →* ↥(StatedSL 3 F))
    (A : Subgroup 𝔾) :
    natImage (conjSL s φ) A = (natImage φ A).map (MulAut.conj s).toMonoidHom := by
  rw [natImage, natImage, Subgroup.map_map]
  refine congrArg (Subgroup.map · _) (MonoidHom.ext fun a => ?_)
  rw [toSL3_conjSL]
  rfl

theorem eq_top_of_normal_of_le {D : Subgroup (SL3 F)}
    (hD : ∀ s : SL3 F, ∀ d ∈ D, s * d * s⁻¹ ∈ D) (hle : rootGroup 1 0 ⊔ rootGroup 2 0 ≤ D) :
    D = ⊤ := by
  have hcyc : ∀ (i j : Fin 3) (c : F), rootElt i j c ∈ D → rootElt (i + 1) (j + 1) c ∈ D :=
    fun i j c h => cyc_conj_rootElt i j c ▸ hD cyc _ h
  have h10 : ∀ c : F, rootElt 1 0 c ∈ D := fun c => hle (Subgroup.mem_sup_left ⟨c, rfl⟩)
  have h20 : ∀ c : F, rootElt 2 0 c ∈ D := fun c => hle (Subgroup.mem_sup_right ⟨c, rfl⟩)
  have h21 : ∀ c : F, rootElt 2 1 c ∈ D := fun c => hcyc 1 0 c (h10 c)
  have h02 : ∀ c : F, rootElt 0 2 c ∈ D := fun c => hcyc 2 1 c (h21 c)
  have h01 : ∀ c : F, rootElt 0 1 c ∈ D := fun c => hcyc 2 0 c (h20 c)
  have h12 : ∀ c : F, rootElt 1 2 c ∈ D := fun c => hcyc 0 1 c (h01 c)
  refine eq_top_of_rootElt_mem fun i j c hij => ?_
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact h01 c
    | exact h02 c
    | exact h10 c
    | exact h12 c
    | exact h20 c
    | exact h21 c

end Aux

section Cent

variable {𝔾 : Type} [Group 𝔾]

private def centMod (K W Z : Subgroup 𝔾) (hKZ : K ≤ Subgroup.normalizer (Z : Set 𝔾)) :
    Subgroup 𝔾 where
  carrier := {g | g ∈ K ∧ ∀ w ∈ W, ⁅w, g⁆ ∈ Z}
  one_mem' := ⟨K.one_mem, fun w _ => by rw [commutatorElement_one_right]; exact Z.one_mem⟩
  mul_mem' := fun {g g'} hg hg' => ⟨K.mul_mem hg.1 hg'.1, fun w hw => by
    rw [commutatorElement_mul_right_conj]
    exact Z.mul_mem (hg.2 w hw) ((Subgroup.mem_normalizer_iff.mp (hKZ hg.1) _).mp (hg'.2 w hw))⟩
  inv_mem' := fun {g} hg => ⟨K.inv_mem hg.1, fun w hw => by
    have e : ⁅w, g⁻¹⁆ = g⁻¹ * ⁅w, g⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKZ (K.inv_mem hg.1)) _).mp (Z.inv_mem (hg.2 w hw))⟩

end Cent

namespace LastHyp

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F] [Fintype F]
  {K Q Lt U Z0 Z V : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
  (h : LastHyp K Q Lt U Z0 Z V ψ)
include h

omit [Fintype F] in
theorem commutator_mem_of_natImage {N T : Subgroup 𝔾}
    (hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)) (hTK : T ≤ K)
    (hT : natImage ψ T = rootGroup 1 0 ⊔ rootGroup 2 0) (hNQ : ⁅N, Q⁆ ≤ Z) (hNT : ⁅N, T⁆ ≤ Z)
    {x : 𝔾} (hx : x ∈ N) {l : 𝔾} (hl : l ∈ Lt) : ⁅x, l⁆ ∈ Z := by
  have hTC : T ≤ centMod K N Z h.zN := fun g hg =>
    ⟨hTK hg, fun w hw => hNT (Subgroup.commutator_mem_commutator hw hg)⟩
  have hQC : Q ≤ centMod K N Z h.zN := fun g hg =>
    ⟨h.qK hg, fun w hw => hNQ (Subgroup.commutator_mem_commutator hw hg)⟩
  have hCn : ∀ k ∈ K, ∀ g ∈ centMod K N Z h.zN, k * g * k⁻¹ ∈ centMod K N Z h.zN := by
    intro k hk g hg
    refine ⟨K.mul_mem (K.mul_mem hk hg.1) (K.inv_mem hk), fun w hw => ?_⟩
    have hw' : k⁻¹ * w * k⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hk)) w).mp hw
    have e : ⁅w, k * g * k⁻¹⁆ = k * ⁅k⁻¹ * w * k⁻¹⁻¹, g⁆ * k⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (h.zN hk) _).mp (hg.2 _ hw')
  have hD : natImage ψ (centMod K N Z h.zN) = ⊤ := by
    refine eq_top_of_normal_of_le (fun s d hd => ?_) ?_
    · obtain ⟨k, rfl⟩ := toSL3_surjective h.surj s
      obtain ⟨g, hgC, rfl⟩ := mem_natImage.mp hd
      exact mem_natImage.mpr ⟨k * g * k⁻¹, hCn k k.2 g hgC, by simp⟩
    · rw [← hT]
      intro g hg
      obtain ⟨t, htT, rfl⟩ := mem_natImage.mp hg
      exact mem_natImage.mpr ⟨t, hTC htT, rfl⟩
  have hlK : l ∈ K := h.ltK hl
  obtain ⟨g, hgC, hg⟩ := mem_natImage.mp (hD ▸ Subgroup.mem_top (toSL3 ψ ⟨l, hlK⟩))
  have hq : ((g⁻¹ * ⟨l, hlK⟩ : ↥K) : 𝔾) ∈ Q := by
    rw [← h.ker]
    rw [map_mul, map_inv, hg, inv_mul_cancel]
  have hlC : l ∈ centMod K N Z h.zN := by
    have e : l = (g : 𝔾) * ((g⁻¹ * ⟨l, hlK⟩ : ↥K) : 𝔾) := by simp
    rw [e]
    exact Subgroup.mul_mem _ hgC (hQC hq)
  exact hlC.2 x hx

theorem layers_inf_sup {V₀ V₁ B : Subgroup 𝔾} (h₀ : LastLayer K Q U Z V ψ V₀)
    (h₁ : LastLayer K Q U Z V ψ V₁) (hB : ∀ x ∈ B, ∀ l ∈ Lt, ⁅x, l⁆ ∈ Z) (hinf : V₀ ⊓ V₁ ≤ B)
    (hBV : B ≤ V) (hVB : V ≤ Subgroup.normalizer (B : Set 𝔾))
    (hidx : B.relIndex V ≤ Nat.card F ^ 6) : V₀ ⊓ V₁ = Z ∧ V ≤ V₀ ⊔ V₁ ⊔ B := by
  have := h.fin
  have hfix₀ : ∀ {x : 𝔾}, x ∈ V₀ → (∀ l ∈ Lt, ⁅x, l⁆ ∈ Z) → x ∈ Z := fun hx hxl =>
    mem_z_of_forall_commutator_mem h₀.dual h.exists_lt_toSL3_eq hx hxl
  have hfix₁ : ∀ {x : 𝔾}, x ∈ V₁ → (∀ l ∈ Lt, ⁅x, l⁆ ∈ Z) → x ∈ Z := fun hx hxl =>
    mem_z_of_forall_commutator_mem h₁.dual h.exists_lt_toSL3_eq hx hxl
  have hZ₀ : Z ≤ V₀ := h₀.zW
  have hZ₁ : Z ≤ V₁ := h₁.zW
  have hI : V₀ ⊓ V₁ = Z :=
    le_antisymm (fun x hx => hfix₀ hx.1 (hB x (hinf hx))) (le_inf hZ₀ hZ₁)
  refine ⟨hI, ?_⟩
  have hV₀K : V₀ ≤ K := h₀.le.trans h.vK
  have hV₁K : V₁ ≤ K := h₁.le.trans h.vK
  have hSB : (V₀ ⊔ V₁) ⊓ B ≤ Z := by
    rintro x ⟨hxS, hxB⟩
    obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := exists_mul_eq_of_mem_sup_of_conj
      (fun b hb a ha => (Subgroup.mem_normalizer_iff.mp (h₀.dual.1 (hV₁K hb)) a).mp ha) hxS
    have hv₀Z : v₀ ∈ Z := hfix₀ hv₀ fun l hl => by
      have hx := hB _ hxB l hl
      rw [commutatorElement_mul_left_conj] at hx
      have ha : ⁅v₀, l⁆ ∈ V₀ :=
        h₀.commutator_lt_le h (Subgroup.commutator_mem_commutator hv₀ hl)
      have hb : ⁅v₁, l⁆ ∈ V₁ :=
        h₁.commutator_lt_le h (Subgroup.commutator_mem_commutator hv₁ hl)
      have hc : ⁅v₀, ⁅v₁, l⁆⁆ ∈ Z :=
        h.vv (Subgroup.commutator_mem_commutator (h₀.le hv₀) (h₁.le hb))
      have hba : ⁅v₁, l⁆ * ⁅v₀, l⁆ ∈ Z := by
        have e : ⁅v₁, l⁆ * ⁅v₀, l⁆ =
            ⁅v₀, ⁅v₁, l⁆⁆⁻¹ * (v₀ * ⁅v₁, l⁆ * v₀⁻¹ * ⁅v₀, l⁆) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Z.mul_mem (Z.inv_mem hc) hx
      have haV₁ : ⁅v₀, l⁆ ∈ V₁ := by
        have e : ⁅v₀, l⁆ = ⁅v₁, l⁆⁻¹ * (⁅v₁, l⁆ * ⁅v₀, l⁆) := by group
        rw [e]
        exact V₁.mul_mem (V₁.inv_mem hb) (hZ₁ hba)
      exact hI ▸ (⟨ha, haV₁⟩ : ⁅v₀, l⁆ ∈ V₀ ⊓ V₁)
    exact hfix₁ (V₁.mul_mem (hZ₁ hv₀Z) hv₁) (hB _ hxB)
  have hSV : V₀ ⊔ V₁ ≤ V := sup_le h₀.le h₁.le
  have hVK : V ≤ K := h.vK
  have : Finite ↥V := Finite.of_injective _ (Subgroup.inclusion_injective hVK)
  have : Finite ↥(V₀ ⊔ V₁) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (hSV.trans hVK))
  have hS : Z.relIndex (V₀ ⊔ V₁) = Nat.card F ^ 6 := by
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hZ₁ le_sup_right, relIndex_eq_of_isSum h₁.dual,
      relIndex_sup_eq (hV₀K.trans h₁.dual.1), ← Subgroup.inf_relIndex_left, hI,
      relIndex_eq_of_isSum h₀.dual]
    ring
  have hge : Nat.card F ^ 6 ≤ B.relIndex (V₀ ⊔ V₁) := by
    rw [← Subgroup.inf_relIndex_right, ← hS]
    exact Subgroup.relIndex_le_of_le_left (by rw [inf_comm]; exact hSB)
      (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : B ≤ V₀ ⊔ V₁ ⊔ B)
    (sup_le hSV hBV)
  rw [relIndex_sup_eq (hSV.trans hVB)] at hmul
  have hr0 : (V₀ ⊔ V₁ ⊔ B).relIndex V ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hpos : 0 < Nat.card F ^ 6 := pow_pos Nat.card_pos 6
  have h1 : Nat.card F ^ 6 * (V₀ ⊔ V₁ ⊔ B).relIndex V ≤ Nat.card F ^ 6 * 1 := by
    calc Nat.card F ^ 6 * (V₀ ⊔ V₁ ⊔ B).relIndex V
        ≤ B.relIndex (V₀ ⊔ V₁) * (V₀ ⊔ V₁ ⊔ B).relIndex V := Nat.mul_le_mul_right _ hge
      _ = B.relIndex V := hmul
      _ ≤ Nat.card F ^ 6 * 1 := by rw [mul_one]; exact hidx
  have h2 := Nat.le_of_mul_le_mul_left h1 hpos
  exact Subgroup.relIndex_eq_one.mp (by omega)

end LastHyp

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem exists_coord_qv (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {α β : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) :
    ∃ ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab _ α) (Uloc c.pu.le L α) ⊥ ψ false 1 ∧
      natImage ψ (Qv (puAmalgam c.pu.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0 := by
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  obtain ⟨ψ₀, hψ₀s, hψ₀⟩ := exists_natural_Uloc h hφ hα
  have hβK : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hβH : ¬ IsMVtx (puAmalgam h.le) β := by have := isMVtx_iff_of_adj _ hαβ; tauto
  have hEp : IsPGroup 2 (natImage ψ₀ (Qv (puAmalgam h.le) β)) :=
    isPGroup_natImage (isPGroup_qv _ h.hyp20 hβH) hβK
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hEp
  have hψ₁ := isSumOfNaturalModulesVia_conjSL hψ₀ x
  set E := natImage (conjSL x ψ₀) (Qv (puAmalgam h.le) β) with hE
  have hEs : E ≤ sStar := by rw [hE, natImage_conjSL]; exact hx
  have hcard : Nat.card E = Nat.card F ^ 2 := by
    rw [hE, card_natImage_eq_relIndex h hφ hα hψ₁ hβK,
      h466a G M T L F φ ⟨h, hmin, hb4, hφ⟩ α β hα hαβ, Nat.card_eq_fintype_card]
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hU := (h465 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α β hα hαβ).1
  rw [usup_eq_commutator_uloc h hfull hα hαβ, I464.card_commutator_eq_pow hψ₁ hβK,
    ← Nat.card_eq_fintype_card] at hU
  have hcomm : Module.finrank F (commN E) = 2 := Nat.pow_right_injective hq2 hU
  have hfix : commN E ≤ fixN E := by
    refine I464.commN_le_fixN_of_commutator_le_centralizer hψ₁ hβK ?_
    have h1 := h464 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α β hα hαβ
    rw [usup_eq_commutator_uloc h hfull hα hαβ] at h1
    exact h1.trans (zh_le_centralizer _ β)
  have hf2 : 2 ≤ Module.finrank F (fixN E) := hcomm ▸ Submodule.finrank_mono hfix
  have hf3 : Module.finrank F (fixN E) ≤ 2 := by
    have h1 := card_le_pow_finrank E
    rw [hcard, hcomm] at h1
    by_contra hcon
    rw [show (3 - Module.finrank F (fixN E)) * 2 = 0 by omega, pow_zero] at h1
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hfc : Nat.card (fixN E) = Nat.card F ^ 2 := by
    rw [card_fixN, show Module.finrank F (fixN E) = 2 by omega]
  have hEq : E = qLn := QjAux.eq_qLn_of_card hEs hcard hfc
  refine ⟨conjSL cyc (conjSL x ψ₀), conjSL_surjective (conjSL_surjective hψ₀s),
    isSumOfNaturalModulesVia_conjSL hψ₁ cyc, ?_⟩
  rw [natImage_conjSL, ← hE, hEq, ← ML3.map_transposeInv_qPt, map_transposeInv_qPt_eq]

theorem lastHyp_of (h463 : I463) (h465 : I465) (h466b : I466b) (h467 : I467)
    (c : Hyp46 M T L φ) {α : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx _ α)
    {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψU : IsSumOfNaturalModulesVia (stab _ α) (Uloc c.pu.le L α) ⊥ ψ false 1)
    (hQL : ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ ≤ Vv _ α) :
    LastHyp (stab _ α) (Qv _ α) (Ltil c.pu.le L α) (Uloc c.pu.le L α) (Zloc c.pu.le L α)
      (ZM _ α) (Vv _ α) ψ := by
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨β, hαβ⟩ := exists_adj (puAmalgam h.le) α
  have hVV := (h463 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α hα).2
  have hVQ := (h465 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α β hα hαβ).2.2
  have hne : ⁅Vv (puAmalgam h.le) α, Vv _ α⁆ ≠ ⊥ := by
    intro hbot
    apply h466b G M T L F φ ⟨h, hmin, hb4, hφ⟩ α hα
    rw [hbot]
    exact bot_le
  have hBL : ⁅centerOf (Vv (puAmalgam h.le) α), Ltil h.le L α⁆ ≤ ZM _ α := by
    rw [← h467 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α hα, Subgroup.commutator_le]
    intro x hx l hl
    exact ((mem_bloc_iff h hb hα).mp hx).2 l hl
  exact
    { fin := finite_stab h hα
      surj := hψs
      nat := hψU
      ker := toSL3_eq_one_iff_mem_qv h hφ hα hψU
      qK := qv_le_stab _ α
      ltK := ltil_le_stab h α
      ltN := stab_le_normalizer_ltil h α
      sup := (stab_eq_ltil_sup_qv h hfull hα).le
      perf := ltil_perfect h hα
      zN := stab_le_normalizer_zm _ α
      zEq := zm_eq_uloc_sup_zloc h hfull hα
      z0c := zloc_le_centralizer_stab h hfull hα
      zq := zm_le_centralizer_qv _ h.hyp20 hα
      z2 := fun z hz => sq_eq_one_of_mem_zv h hfull (ρ := α) (by rwa [zv_of_isMVtx _ hα])
      vq := vv_le_qv h hb hα
      vN := stab_le_normalizer_vv h α
      zv := zm_le_vv h hα
      vv := hVV
      vqc := hVQ
      vne := hne
      bl := hBL
      ql := hQL }

theorem exists_lastLayer_cfg (h14 : MS14AS) (hSQ : SQTKQuot) (h465 : I465) (h467 : I467)
    (h469 : I469Cfg M T L φ) (c : Hyp46 M T L φ) {α β γ : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx _ α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (hβγ : (puAmalgam c.pu.le).treeGraph.Adj β γ)
    (hZγ : ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α)
    {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)}
    (hLH : LastHyp (stab _ α) (Qv _ α) (Ltil c.pu.le L α) (Uloc c.pu.le L α) (Zloc c.pu.le L α)
      (ZM _ α) (Vv _ α) ψ)
    (hT : natImage ψ (Qv (puAmalgam c.pu.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0)
    {N : Subgroup (puAmalgam c.pu.le).Universal}
    (hNn : stab (puAmalgam c.pu.le) α ≤
      Subgroup.normalizer (N : Set (puAmalgam c.pu.le).Universal))
    (hZN : ZM (puAmalgam c.pu.le) α ≤ N) (hN : N ≤ Vv _ α ⊓ Qv _ γ)
    (hNB : ¬ N ≤ Bloc c.pu.le L α) :
    ∃ W, W ≤ N ∧ LastLayer (stab _ α) (Qv _ α) (Uloc c.pu.le L α) (ZM _ α) (Vv _ α) ψ W := by
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  have h20 := h.hyp20
  have hC := centHyp_of_gen23 h hfull
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  obtain ⟨n, hn⟩ := hφ.1
  have hKα := finite_stab h hα
  have hγ : IsMVtx (puAmalgam h.le) γ := by
    have h1 := isMVtx_iff_of_adj _ hαβ
    have h2 := isMVtx_iff_of_adj _ hβγ
    tauto
  have hαγ : α ≠ γ := by
    rintro rfl
    exact hZγ (zm_le_bloc h hb hα)
  have hdαγ : (puAmalgam h.le).treeGraph.dist α γ = 2 := dist_eq_two_of_adj_adj _ hαβ hβγ hαγ
  have hdγα : (puAmalgam h.le).treeGraph.dist γ α = 2 := by rw [tdist_comm]; exact hdαγ
  have hNV : N ≤ Vv _ α := hN.trans inf_le_left
  have hNQγ : N ≤ Qv _ γ := hN.trans inf_le_right
  obtain ⟨-, -, -, h9⟩ := h469 ⟨h, hmin, hb4, hφ⟩ α β hα hαβ
  obtain ⟨-, hUU, hZαγ⟩ := h9 γ hβγ hZγ
  obtain ⟨-, -, -, h9'⟩ := h469 ⟨h, hmin, hb4, hφ⟩ γ β hγ hβγ.symm
  obtain ⟨hTγ, -, -⟩ := h9' α hαβ.symm hZαγ
  have hβK : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hβKγ : Qv (puAmalgam h.le) β ≤ stab _ γ := qv_le_stab_of_adj _ hβγ
  have hQαβ : Qv (puAmalgam h.le) α ≤ Qv _ β := qv_le_qv _ h20 hα hαβ
  have hQγβ : Qv (puAmalgam h.le) γ ≤ Qv _ β := qv_le_qv _ h20 hγ hβγ.symm
  have hVγβ : Vv (puAmalgam h.le) γ ≤ Qv _ β := (vv_le_qv h hb hγ).trans hQγβ
  have hZγα : ZM (puAmalgam h.le) γ ≤ Qv _ α := zm_le_qv_of_dist_le_three hb4 hγ (by omega)
  have hZγK : ZM (puAmalgam h.le) γ ≤ stab _ α := hZγα.trans (qv_le_stab _ α)
  have hZαK : ZM (puAmalgam h.le) α ≤ stab _ α := hLH.zK
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hZnγ := stab_le_normalizer_zm (puAmalgam h.le) γ
  set Y := ZM (puAmalgam h.le) γ ⊔ ZM _ α with hY
  have hYK : Y ≤ stab _ α := sup_le hZγK hZαK
  have hYZ : (ZM (puAmalgam h.le) α).relIndex Y ≤ Fintype.card F := by
    rw [hY, relIndex_sup_eq (hZγK.trans hZn)]
    have hq := (h465 G M T L F φ ⟨h, hmin, hb4, hφ⟩ γ β hγ hβγ.symm).2.1
    rw [← hq]
    exact Subgroup.relIndex_le_of_le_left (zh_le_zm _ hαβ)
      (by rw [hq]; exact Fintype.card_ne_zero)
  have hYT : ⁅Y, Qv (puAmalgam h.le) β⁆ ≤ ZM _ α := by
    refine commutator_sup_le_of_le_normalizer hZn hZγK hZαK ?_ ?_
    · have e : ⁅ZM (puAmalgam h.le) γ, Qv _ β⁆ = Usup _ γ β := by rw [Usup, zv_of_isMVtx _ hγ]
      rw [e, hUU, Usup, zv_of_isMVtx _ hα]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hβK.trans hZn)
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hβK.trans hZn)
  have hNTY : ⁅N, Qv (puAmalgam h.le) β⁆ ≤ Y := by
    rw [Subgroup.commutator_comm, ← hTγ]
    have hYn : Qv (puAmalgam h.le) β ≤ Subgroup.normalizer (Y : Set _) :=
      CFSG.LieType.Steinberg.le_normalizer_sup (hβKγ.trans hZnγ) (hβK.trans hZn)
    refine commutator_sup_le_of_le_normalizer hYn hVγβ hQαβ ?_ ?_
    · have h1 := (h465 G M T L F φ ⟨h, hmin, hb4, hφ⟩ γ β hγ hβγ.symm).2.2
      exact ((Subgroup.commutator_mono le_rfl hNQγ).trans h1).trans le_sup_left
    · rw [Subgroup.commutator_comm]
      exact ((Subgroup.commutator_mono hNV le_rfl).trans hLH.vqc).trans le_sup_right
  have hNTZ : ¬ ⁅N, Qv (puAmalgam h.le) β⁆ ≤ ZM _ α := by
    intro hle
    apply hNB
    intro x hx
    rw [mem_bloc_iff h hb hα]
    exact ⟨hNV hx, fun l hl => hLH.commutator_mem_of_natImage hNn hβK hT
      ((Subgroup.commutator_mono hNV le_rfl).trans hLH.vqc) hle hx hl⟩
  obtain ⟨N₀, hN₀N, -, hd⟩ := exists_dual_layer h14 hSQ (sqtkGroup_SL3_of_sqtkQuot h hSQ hφ) hn
    hLH.surj hLH.nat hLH.ker hLH.zEq hLH.z0c hNn hZN (hNV.trans hLH.vK)
    ((Subgroup.commutator_mono hNV hNV).trans hLH.vv)
    ((Subgroup.commutator_mono hNV le_rfl).trans hLH.vqc)
    (fun x hx => hLH.vv (sq_mem_commutator_vv h hb0 (hNV hx))) hQαβ hβK hT le_sup_right hYK
    hYZ hYT hNTY hNTZ
  obtain ⟨α', hc, hgeo⟩ : ∃ α', IsCritical (puAmalgam h.le) α α' ∧
      geo (puAmalgam h.le) α α' 2 = γ := by
    by_contra hno
    have hgen : critGen (puAmalgam h.le) α γ = ⊥ :=
      le_bot_iff.mp (iSup₂_le fun δ hδ => (hno ⟨δ, hδ⟩).elim)
    have hVQ : Vv (puAmalgam h.le) γ ≤ Qv _ α := by
      have := vv_le_critGen_sup h20 hC hb4 hγ hdαγ
      rwa [hgen, bot_sup_eq] at this
    apply hZαγ
    rw [h467 G M T L F φ ⟨h, hmin, hb4, hφ⟩ γ hγ]
    have hZV : ZM (puAmalgam h.le) α ≤ Vv _ γ :=
      le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
        (puAmalgam h.le).treeGraph.dist γ ρ ≤ 2}) => Zv _ ρ) α (by simp [hdγα])
        (zv_of_isMVtx _ hα).ge
    exact le_inf hZV
      ((zm_le_centralizer_qv _ h20 hα).trans (Subgroup.centralizer_le hVQ))
  set δ := geo (puAmalgam h.le) α α' 3 with hδ
  have hα' : IsMVtx (puAmalgam h.le) α' := hc.isMVtx_right _ h20
  have hγδ : (puAmalgam h.le).treeGraph.Adj γ δ := by
    have := adj_geo_crit hb4 hc (i := 2) (by omega)
    rwa [hgeo] at this
  have hδα' : (puAmalgam h.le).treeGraph.Adj δ α' := by
    have := adj_geo_crit hb4 hc (i := 3) (by omega)
    rwa [geo_four hb4 hc] at this
  have hZα'K : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h20 hb0 hc
  have hZαδ : ZM (puAmalgam h.le) α ≤ Qv _ δ := zm_le_qv_geo hb4 hc (by omega)
  have hQγδ : Qv (puAmalgam h.le) γ ≤ Qv _ δ := qv_le_qv _ h20 hγ hγδ
  set P := Usup (puAmalgam h.le) α' δ with hP
  have hPeq : P = ⁅ZM (puAmalgam h.le) α', Qv _ δ⁆ := by rw [hP, Usup, zv_of_isMVtx _ hα']
  have hPZ : P ≤ ZM (puAmalgam h.le) α' := by
    rw [hPeq]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hδα').trans (stab_le_normalizer_zm _ α'))
  have hPK : P ≤ stab _ α := hPZ.trans hZα'K
  have hcardP : Nat.card P = Fintype.card F ^ 2 :=
    (h465 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α' δ hα' hδα'.symm).1
  have hRU := critR_eq_commutator_uloc h hφ hc
  have hRle : critR (puAmalgam h.le) α α' ≤ Uloc h.le L α := hRU.1 ▸ hRU.2
  have hRP : critR (puAmalgam h.le) α α' ≤ P := by
    rw [hPeq, critR, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hZαδ
  have htype := crit_type h hφ hC hc
  have hRq : Fintype.card F ≤ Nat.card (critR (puAmalgam h.le) α α') := by
    rcases htype with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2, -⟩ <;> rw [h2]
    exact Nat.le_self_pow (by norm_num) _
  have hAq : Fintype.card F ≤ (Qv (puAmalgam h.le) α).relIndex (ZM _ α') := by
    rw [← relIndex_zm_comm h hφ hC hc]
    rcases htype with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -, -⟩ <;> rw [h1]
    exact Nat.le_self_pow (by norm_num) _
  have hZα'c : ∀ a ∈ ZM (puAmalgam h.le) α', ∀ b ∈ ZM (puAmalgam h.le) α', ⁅a, b⁆ = 1 := by
    intro a ha b hb'
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp ((zm_le_centralizer_qv _ h20 hα') hb') a
      ((CFSG.Quasithin.MS93.zm_le_vv h hα').trans (vv_le_qv h hb hα') ha)
  refine ⟨N₀, hN₀N, hN₀N.trans hNV, hd, ZM _ α', hZα'K, fun a ha => ?_, fun a ha b hb' => ?_,
    hAq, ?_⟩
  · rw [sq_eq_one_of_mem_zv h hfull (ρ := α') (by rwa [zv_of_isMVtx _ hα'])]
    exact one_mem _
  · rw [hZα'c a ha b hb']
    exact one_mem _
  · have hWA : ⁅N₀, ZM (puAmalgam h.le) α'⁆ ≤ P := by
      rw [hPeq, Subgroup.commutator_comm]
      exact Subgroup.commutator_mono le_rfl ((hN₀N.trans hNQγ).trans hQγδ)
    have : Finite ↥(P ⊔ Uloc h.le L α) :=
      Finite.of_injective _ (Subgroup.inclusion_injective (sup_le hPK hLH.uK))
    have : Finite ↥P := Finite.of_injective _ (Subgroup.inclusion_injective hPK)
    have h1 := Subgroup.relIndex_mul_card (critR (puAmalgam h.le) α α') P
    rw [inf_of_le_left hRP, hcardP] at h1
    have : Finite ↥(critR (puAmalgam h.le) α α') :=
      Finite.of_injective _ (Subgroup.inclusion_injective (hRle.trans hLH.uK))
    have hR0 : 0 < Nat.card (critR (puAmalgam h.le) α α') := Nat.card_pos
    calc (Uloc h.le L α).relIndex (⁅N₀, ZM _ α'⁆ ⊔ Uloc h.le L α)
        ≤ (Uloc h.le L α).relIndex (P ⊔ Uloc h.le L α) :=
          Subgroup.relIndex_le_of_le_right (sup_le_sup_right hWA _)
            (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
      _ = (Uloc h.le L α).relIndex P := relIndex_sup_eq (hPK.trans hLH.nat.1)
      _ ≤ (critR (puAmalgam h.le) α α').relIndex P :=
          Subgroup.relIndex_le_of_le_left hRle
            (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
      _ ≤ Fintype.card F := by
          by_contra hlt'
          have hlt := not_le.mp hlt'
          have h2 : Fintype.card F * Fintype.card F <
              (critR (puAmalgam h.le) α α').relIndex P * Nat.card (critR (puAmalgam h.le) α α') :=
            Nat.mul_lt_mul_of_lt_of_le hlt hRq hR0
          rw [h1, sq] at h2
          exact lt_irrefl _ h2

end Vertex

theorem i46tCfg_of (h14 : MS14AS) (hSQ : SQTKQuot) (h463 : I463) (h464 : I464) (h465 : I465)
    (h466a : I466a) (h466b : I466b) (h467 : I467) {G : Type} [Group G] [Finite G]
    {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (h469 : I469Cfg M T L φ) (h4612 : I4612Cfg M T L φ) : I46TCfg M T L φ := by
  intro c α hα
  obtain ⟨β, γ, ρ, hαβ, hβγ, hβρ, hZγ, hZρ, Nγ, Nρ, hγn, hγZ, hγV, hγB, hρn, hρZ, hρV, hρB,
    hinf, hidx⟩ := h4612 c α hα
  obtain ⟨ψ, hψs, hψU, hψT⟩ := exists_coord_qv h464 h465 h466a c hα hαβ
  obtain ⟨hQL, -, -, -⟩ := h469 c α β hα hαβ
  have hLH := lastHyp_of h463 h465 h466b h467 c hα hψs hψU hQL
  obtain ⟨V₀, hV₀N, hV₀⟩ := exists_lastLayer_cfg h14 hSQ h465 h467 h469 c hα hαβ hβγ hZγ hLH hψT
    hγn hγZ hγV hγB
  obtain ⟨V₁, hV₁N, hV₁⟩ := exists_lastLayer_cfg h14 hSQ h465 h467 h469 c hα hαβ hβρ hZρ hLH hψT
    hρn hρZ hρV hρB
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  obtain ⟨hI, hS⟩ := hLH.layers_inf_sup hV₀ hV₁ (B := Bloc c.pu.le L α)
    (fun x hx l hl => ((mem_bloc_iff c.pu hb hα).mp hx).2 l hl)
    ((inf_le_inf hV₀N hV₁N).trans hinf) (bloc_le_vv c.pu α)
    (by rw [h467 G M T L F φ c α hα]; exact le_normalizer_centerOf _)
    (by rwa [Nat.card_eq_fintype_card])
  refine ⟨ψ, hψs, hψU, hQL, V₀, V₁, hV₀, hV₁, hI, ?_⟩
  rw [← h467 G M T L F φ c α hα]
  exact hS

theorem i46t_of (h14 : MS14AS) (hSQ : SQTKQuot) (h463 : I463) (h464 : I464) (h465 : I465)
    (h466a : I466a) (h466b : I466b) (h467 : I467) (h469 : I469) (h4612 : I4612) : I46T :=
  fun G _ _ M T L F _ _ φ => i46tCfg_of h14 hSQ h463 h464 h465 h466a h466b h467
    (h469 G M T L F φ) (h4612 G M T L F φ)

end CFSG.Quasithin.MS93.S46
