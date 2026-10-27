module

public import CFSG.Quasithin.MS93.S36SpLine

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93.MSP
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S36
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}

omit [Finite G] in
theorem tImage_of_characteristic (ψ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T)
    (hc : (K.subgroupOf T).Characteristic) : tImage ψ K = K := by
  rw [tImage_eq_map, Subgroup.characteristic_iff_map_eq.1 hc ψ,
    Subgroup.map_subgroupOf_eq_of_le hK]

omit [Finite G] in
theorem tImage_omegaOneCenterOf (ψ : MulAut ↥T) :
    tImage ψ (omegaOneCenterOf T) = omegaOneCenterOf T :=
  tImage_of_characteristic ψ (PU.omegaOneCenterOf_le T)
    (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T)

theorem commutator_Z0q_T_le (h : PUHyp M T L) : ⁅Z0q M T, T⁆ ≤ Uq M T L := by
  rw [S33.commutator_Z0q_eq h le_rfl]
  exact commutator_le_left_of_le_normalizer (h.le.trans (le_normalizer_Uq h.le_normalizer))

theorem Dq_inf_Uq_le (h : PUHyp M T L) : Dq M L ⊓ Uq M T L ≤ Uq M T L ⊓ Zq M L :=
  fun _ hx => ⟨hx.2, h.Uq_le_Xq hx.2, hx.1.2⟩

variable (d : SpFrame h) (χ : MulAut ↥T) (v : V4 d.F)

@[expose] noncomputable def Kc : Subgroup G := tImage χ (Dq M L) ⊓ d.pre (d.F ∙ v)

@[expose] noncomputable def Yc : Subgroup G where
  carrier := {y | y ∈ Z0q M T ⊓ tImage χ (pCoreOf 2 M) ∧
    ∀ x ∈ tImage χ (pCoreOf 2 M), ⁅y, x⁆ ∈ Kc d χ v}
  one_mem' := ⟨Subgroup.one_mem _, fun x _ => by
    rw [commutatorElement_one_left]
    exact Subgroup.one_mem _⟩
  mul_mem' := by
    rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
    refine ⟨Subgroup.mul_mem _ hy₁ hy₂, fun x hx => ?_⟩
    have hk : ⁅y₂, x⁆ ∈ Z0q M T :=
      Uq_le_Z0q h.L_le (d.pre_le _ (h₂ x hx).2)
    have hcomm : y₁ * ⁅y₂, x⁆ * y₁⁻¹ = ⁅y₂, x⁆ := by
      rw [A4.mul_comm_of_mem_omegaOneCenterOf (h.Z0q_le_Xq hy₁.1) (h.Z0q_le_Xq hk),
        mul_inv_cancel_right]
    have e : ⁅y₁ * y₂, x⁆ = (y₁ * ⁅y₂, x⁆ * y₁⁻¹) * ⁅y₁, x⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, hcomm]
    exact Subgroup.mul_mem _ (h₂ x hx) (h₁ x hx)
  inv_mem' := by
    rintro y ⟨hy, h₁⟩
    refine ⟨Subgroup.inv_mem _ hy, fun x hx => ?_⟩
    have hk : ⁅y, x⁆ ∈ Z0q M T := Uq_le_Z0q h.L_le (d.pre_le _ (h₁ x hx).2)
    have hcomm : y⁻¹ * ⁅y, x⁆⁻¹ * y⁻¹⁻¹ = ⁅y, x⁆⁻¹ := by
      rw [A4.mul_comm_of_mem_omegaOneCenterOf (h.Z0q_le_Xq (Subgroup.inv_mem _ hy.1))
        (h.Z0q_le_Xq (Subgroup.inv_mem _ hk)), inv_inv, inv_mul_cancel_right]
    have e : ⁅y⁻¹, x⁆ = y⁻¹ * ⁅y, x⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, hcomm]
    exact Subgroup.inv_mem _ (h₁ x hx)

variable {d χ v}

theorem Yc_le : Yc d χ v ≤ Z0q M T ⊓ tImage χ (pCoreOf 2 M) := fun _ hy => hy.1

theorem commutator_Yc_le : ⁅Yc d χ v, tImage χ (pCoreOf 2 M)⁆ ≤ Kc d χ v := by
  rw [Subgroup.commutator_le]
  exact fun y hy x hx => hy.2 x hx

theorem Kc_le_Uq : Kc d χ v ≤ Uq M T L := fun _ hk => d.pre_le _ hk.2

theorem Kc_le_tImage_Dq : Kc d χ v ≤ tImage χ (Dq M L) := fun _ hk => hk.1

namespace PairHyp

variable {d : SpFrame h} {χ : MulAut ↥T} (hp : PairHyp d χ)

omit hp in
theorem pre_eq_sup {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v)
    (hE : ∀ e ∈ tImage χ (Z0q M T), ∃ g, ActsMat d.vec e g) :
    d.pre (d.F ∙ v) = ⁅Uq M T L, tImage χ (Z0q M T)⁆ ⊔ (Uq M T L ⊓ Zq M L) := by
  refine le_antisymm (fun u hu => ?_) (sup_le ?_ (d.C_le_pre _))
  · obtain ⟨huU, hvec⟩ := d.mem_pre.1 hu
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hvec
    obtain ⟨w, hw⟩ := exists_form_eq_one hx.ne
    obtain ⟨u₁, hu₁⟩ := d.surj (Multiplicative.ofAdd w)
    obtain ⟨e, he, heg⟩ := hx.all b
    have heM : e ∈ M := tImage_le_M h χ _ he
    set c : G := e * u₁ * e⁻¹ * (u₁ : G)⁻¹ with hc
    have hcU : c ∈ Uq M T L := mul_mem (conj_mem (d.normU heM) u₁) (inv_mem u₁.2)
    have hcvec := d.toAdd_vec_comm heM heg u₁
    rw [hu₁, toAdd_ofAdd, transv_mulVec, hw, mul_one, add_sub_cancel_left] at hcvec
    have hcE : c ∈ ⁅Uq M T L, tImage χ (Z0q M T)⁆ := by
      rw [Subgroup.commutator_comm]
      have := Subgroup.commutator_mem_commutator he u₁.2
      rwa [commutatorElement_def] at this
    have hrU : u * c⁻¹ ∈ Uq M T L := mul_mem huU (inv_mem hcU)
    have hrC : u * c⁻¹ ∈ Uq M T L ⊓ Zq M L := by
      refine ⟨hrU, (d.ker ⟨_, hrU⟩).1 ?_⟩
      have e : (⟨u * c⁻¹, hrU⟩ : ↥(Uq M T L)) = ⟨u, huU⟩ * (⟨c, hcU⟩ : ↥(Uq M T L))⁻¹ := rfl
      apply Multiplicative.toAdd.injective
      rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, hcvec, ← hb, add_neg_cancel]
      rfl
    have hu' : u = (u * c⁻¹) * c := by group
    rw [hu', sup_comm]
    exact Subgroup.mul_mem_sup hrC hcE
  · rw [Subgroup.commutator_le]
    intro u hu e he
    obtain ⟨g, hg⟩ := hE e he
    obtain ⟨c, rfl⟩ := hx.mem e he g hg
    have heM := tImage_le_M h χ _ he
    have h1 : e * u⁻¹ * e⁻¹ ∈ Uq M T L := conj_mem (d.normU heM) ⟨u⁻¹, inv_mem hu⟩
    have hwU : ⁅u, e⁆ ∈ Uq M T L := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact mul_mem hu (by simpa [mul_assoc] using h1)
    refine d.mem_pre.2 ⟨hwU, ?_⟩
    have e1 : (⟨⁅u, e⁆, hwU⟩ : ↥(Uq M T L)) = ⟨u, hu⟩ * ⟨e * u⁻¹ * e⁻¹, h1⟩ :=
      Subtype.ext (by simp [commutatorElement_def, mul_assoc])
    have e2 : (⟨u⁻¹, inv_mem hu⟩ : ↥(Uq M T L)) = (⟨u, hu⟩ : ↥(Uq M T L))⁻¹ := rfl
    rw [e1, map_mul, toAdd_mul, hg ⟨u⁻¹, inv_mem hu⟩ ⟨_, h1⟩ rfl, e2, map_inv, toAdd_inv,
      Matrix.mulVec_neg, transv_mulVec, neg_add, ← add_assoc, add_neg_cancel, zero_add]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))

omit hp in
theorem le_normalizer_Kc {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v)
    (hE : ∀ e ∈ tImage χ (Z0q M T), ∃ g, ActsMat d.vec e g) :
    T ≤ Subgroup.normalizer (Kc d χ v : Set G) := by
  have hTU : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  rw [Kc, pre_eq_sup hx hE]
  refine le_normalizer_inf (le_normalizer_tImage χ (h.le.trans (le_normalizer_Dq h.le_normalizer)))
    (le_normalizer_sup (le_normalizer_commutator hTU
      (le_normalizer_tImage χ (h.le.trans (le_normalizer_Z0q M T))))
      (h.le.trans (le_normalizer_inf (le_normalizer_Uq h.le_normalizer)
        (le_normalizer_Zq h.le_normalizer))))

omit hp in
theorem le_normalizer_Yc {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v)
    (hE : ∀ e ∈ tImage χ (Z0q M T), ∃ g, ActsMat d.vec e g) :
    T ≤ Subgroup.normalizer (Yc d χ v : Set G) := by
  have hZP : T ≤ Subgroup.normalizer ((Z0q M T ⊓ tImage χ (pCoreOf 2 M) : Subgroup G) : Set G) :=
    le_normalizer_inf (h.le.trans (le_normalizer_Z0q M T))
      (le_normalizer_tImage χ (h.le.trans (le_normalizer_pCoreOf M)))
  have hP : T ≤ Subgroup.normalizer (tImage χ (pCoreOf 2 M) : Set G) :=
    le_normalizer_tImage χ (h.le.trans (le_normalizer_pCoreOf M))
  have hK := le_normalizer_Kc hx hE
  have key : ∀ t ∈ T, ∀ y ∈ Yc d χ v, t * y * t⁻¹ ∈ Yc d χ v := by
    intro t ht y hy
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hZP ht) y).1 hy.1, fun x hx' => ?_⟩
    have hx'' : t⁻¹ * x * t⁻¹⁻¹ ∈ tImage χ (pCoreOf 2 M) :=
      (Subgroup.mem_normalizer_iff.1 (hP (inv_mem ht)) x).1 hx'
    have e : ⁅t * y * t⁻¹, x⁆ = t * ⁅y, t⁻¹ * x * t⁻¹⁻¹⁆ * t⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hK ht) _).1 (hy.2 _ hx'')
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key t ht y, fun hy => ?_⟩
  have := key t⁻¹ (inv_mem ht) _ hy
  simpa [mul_assoc] using this

omit hp in
theorem omegaOneCenterOf_le_Yc {v : V4 d.F} :
    omegaOneCenterOf T ≤ Yc d χ v := by
  intro ω hω
  have hωZ : ω ∈ Z0q M T := omegaOneCenterOf_le_Z0q M T h.le hω
  have hωP : ω ∈ tImage χ (pCoreOf 2 M) := by
    rw [← tImage_omegaOneCenterOf χ] at hω
    exact S36SP.tImage_mono χ (fun y hy => h.Z0q_le_pCoreOf (omegaOneCenterOf_le_Z0q M T h.le hy))
      hω
  refine ⟨⟨hωZ, hωP⟩, fun x hx => ?_⟩
  have hc : ω * x = x * ω := by
    have := (PU.omegaOneCenterOf_le_centerOf T hω).2
    exact (Subgroup.mem_centralizer_iff.1 this x (tImage_le χ _ hx)).symm
  rw [commutatorElement_eq_one_iff_mul_comm.2 hc]
  exact Subgroup.one_mem _

include hp in
theorem exists_pre_le_Yc {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v) :
    ∃ l : Submodule d.F (V4 d.F), IsLine l ∧ d.pre l ≤ Yc d χ v ∧
      ∀ c : d.F, ∃ k : ↥(Uq M T L), (k : G) ∈ Kc d χ v ∧
        Multiplicative.toAdd (d.vec k) = c • v := by
  have hE := hp.actsMat_E
  have hP := actsMat_P hx
  have hPM : tImage χ (pCoreOf 2 M) ≤ M := tImage_le_M h χ _
  obtain ⟨l, hl, hvl, hL1, hL3, g, hgH, w, hwl, hgw⟩ := hp.exists_line hx (hPM := hPM) (hP := hP)
  have hl_perp : l ≤ perp (d.F ∙ v) := hl.le_perp.trans (perp_antitone hvl)
  have hK : ∀ u ∈ d.pre l, ∀ x ∈ tImage χ (pCoreOf 2 M), ⁅u, x⁆ ∈ Kc d χ v := by
    intro u hu x hxP
    refine ⟨hL1 u hu x hxP, ?_⟩
    obtain ⟨huU, hvec⟩ := d.mem_pre.1 hu
    obtain ⟨g', hg'⟩ := hP x hxP
    have hxM := hPM hxP
    have h1 : x * u⁻¹ * x⁻¹ ∈ Uq M T L := conj_mem (d.normU hxM) ⟨u⁻¹, inv_mem huU⟩
    have hwU : ⁅u, x⁆ ∈ Uq M T L := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact mul_mem huU (by simpa [mul_assoc] using h1)
    refine d.mem_pre.2 ⟨hwU, ?_⟩
    have e1 : (⟨⁅u, x⁆, hwU⟩ : ↥(Uq M T L)) = ⟨u, huU⟩ * ⟨x * u⁻¹ * x⁻¹, h1⟩ :=
      Subtype.ext (by simp [commutatorElement_def, mul_assoc])
    have e2 : (⟨u⁻¹, inv_mem huU⟩ : ↥(Uq M T L)) = (⟨u, huU⟩ : ↥(Uq M T L))⁻¹ := rfl
    rw [e1, map_mul, toAdd_mul, hg' ⟨u⁻¹, inv_mem huU⟩ ⟨_, h1⟩ rfl, e2, map_inv, toAdd_inv,
      Matrix.mulVec_neg, ← sub_eq_add_neg, ← neg_sub]
    exact Submodule.neg_mem _ (hL3 g' (d.actsMat_mem_img hPM hP hxP hg') _ hvec)
  refine ⟨l, hl, fun u hu => ⟨⟨Uq_le_Z0q h.L_le (d.pre_le _ hu),
    pre_perp_le hx hE (d.pre_mono hl_perp hu)⟩, hK u hu⟩, fun c => ?_⟩
  obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.1 (hL3 g hgH w hwl)
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_smul, eq_comm, sub_eq_zero] at hν
    exact hgw hν
  obtain ⟨x, hxP, hxg⟩ := (d.mem_img hPM hP).1 hgH
  obtain ⟨u₂, hu₂⟩ := d.surj (Multiplicative.ofAdd ((c * ν⁻¹) • w))
  have hu₂l : (u₂ : G) ∈ d.pre l := by
    rw [d.mem_pre_coe, hu₂, toAdd_ofAdd]
    exact Submodule.smul_mem _ _ hwl
  have hxM := hPM hxP
  refine ⟨⟨_, mul_mem (conj_mem (d.normU hxM) u₂) (inv_mem u₂.2)⟩, ?_, ?_⟩
  · have := Subgroup.inv_mem _ (hK _ hu₂l x hxP)
    have e : ⁅(u₂ : G), x⁆⁻¹ = x * u₂ * x⁻¹ * (u₂ : G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at this
  · rw [d.toAdd_vec_comm hxM hxg u₂, hu₂, toAdd_ofAdd, Matrix.mulVec_smul, ← smul_sub, ← hν,
      smul_smul, mul_assoc, inv_mul_cancel₀ hν0, mul_one]

omit hp in
theorem commutator_Uq_tImage_le (h : PUHyp M T L) (χ : MulAut ↥T) :
    ⁅Uq M T L, tImage χ (Z0q M T)⁆ ≤ tImage χ (Uq M T L) := by
  have hUT : Uq M T L ≤ T := (Uq_le_Z0q h.L_le).trans (Z0q_le_T h)
  calc ⁅Uq M T L, tImage χ (Z0q M T)⁆ ≤ ⁅tImage χ (Z0q M T), T⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mono le_rfl hUT
    _ = tImage χ ⁅Z0q M T, T⁆ := by
        rw [tImage_commutator χ (Z0q_le_T h) le_rfl, tImage_self]
    _ ≤ tImage χ (Uq M T L) := S36SP.tImage_mono χ (commutator_Z0q_T_le h)

omit hp in
theorem tImage_inv_commutator_Uq (h : PUHyp M T L) (χ : MulAut ↥T) :
    tImage χ⁻¹ ⁅Uq M T L, tImage χ (Z0q M T)⁆ = ⁅Uq M T L, tImage χ⁻¹ (Z0q M T)⁆ := by
  have hUT : Uq M T L ≤ T := (Uq_le_Z0q h.L_le).trans (Z0q_le_T h)
  have hZT := Z0q_le_T h
  rw [tImage_commutator χ⁻¹ hUT (tImage_le _ _), tImage_inv_tImage χ hZT,
    Subgroup.commutator_comm, S33.commutator_Z0q_eq h (tImage_le _ _), Subgroup.commutator_comm]
  have h1 : ⁅tImage χ⁻¹ (Z0q M T), Uq M T L⁆ = ⁅tImage χ⁻¹ (Uq M T L), Uq M T L⁆ := by
    have h2 := congrArg (tImage χ⁻¹) (S33.commutator_Z0q_eq h (tImage_le χ (Uq M T L)))
    rwa [tImage_commutator χ⁻¹ hZT (tImage_le _ _), tImage_commutator χ⁻¹ hUT (tImage_le _ _),
      tImage_inv_tImage χ hUT] at h2
  rw [← h1, Subgroup.commutator_comm]

theorem eq_zero_or_eq_one_of_card_two {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (c : F) : c = 0 ∨ c = 1 := by
  classical
  by_contra hc
  push Not at hc
  have hle : ({0, 1, c} : Finset F).card ≤ Fintype.card F := Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem, Finset.card_pair hc.2.symm] at hle
  · omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, hc.1.symm⟩

include hp in
theorem Kc_eq (hk : 2 ≤ d.k) {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v) :
    Kc d χ v = tImage χ (Uq M T L ⊓ Zq M L) ∧ Nat.card ↥(Uq M T L ⊓ Zq M L) = 2 ^ d.k ∧
      tImage χ (Uq M T L ⊓ Zq M L) ≤ Uq M T L ∧
      Uq M T L ⊓ Zq M L ⊓ tImage χ (Uq M T L ⊓ Zq M L) = ⊥ := by
  have hE := hp.actsMat_E
  have hCT : Uq M T L ⊓ Zq M L ≤ T := inf_le_left.trans ((Uq_le_Z0q h.L_le).trans (Z0q_le_T h))
  have hCle : Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, tImage χ (Z0q M T)⁆ := by
    rw [Subgroup.commutator_comm]
    exact d.rad hk v hx.ne _ (tImage_le_M h χ _) hx.all
  have hKle : Kc d χ v ≤ tImage χ (Uq M T L ⊓ Zq M L) := by
    intro k hk'
    have h1 : k ∈ ⁅Uq M T L, tImage χ (Z0q M T)⁆ := by
      have h2 := hk'.2
      rwa [pre_eq_sup hx hE, sup_eq_left.2 hCle] at h2
    have h3 : k ∈ tImage χ (Dq M L ⊓ Uq M T L) := by
      rw [tImage_inf]
      exact ⟨hk'.1, commutator_Uq_tImage_le h χ h1⟩
    exact S36SP.tImage_mono χ (Dq_inf_Uq_le h) h3
  obtain ⟨-, -, -, hfill⟩ := hp.exists_pre_le_Yc hx
  choose kf hkf hkv using hfill
  have hinj : Function.Injective fun c : d.F => (⟨kf c, hkf c⟩ : ↥(Kc d χ v)) := by
    intro c₁ c₂ heq
    have h0 := congrArg Subtype.val heq
    simp only at h0
    have h1 : kf c₁ = kf c₂ := Subtype.ext h0
    have h2 := hkv c₁
    rw [h1, hkv c₂] at h2
    exact smul_left_injective d.F hx.ne h2.symm
  have hq : 2 ^ d.k ≤ Nat.card ↥(Kc d χ v) := by
    rw [← d.card_F]
    exact Nat.card_le_card_of_injective _ hinj
  have hKC : Nat.card ↥(Kc d χ v) ≤ Nat.card ↥(Uq M T L ⊓ Zq M L) := by
    rw [← card_tImage χ hCT]
    exact Subgroup.card_le_of_le hKle
  have hcard : Nat.card ↥(Uq M T L ⊓ Zq M L) = 2 ^ d.k := le_antisymm d.card_C (hq.trans hKC)
  have hKeq : Kc d χ v = tImage χ (Uq M T L ⊓ Zq M L) :=
    Subgroup.eq_of_le_of_card_ge hKle (by rw [card_tImage χ hCT, hcard]; exact hq)
  refine ⟨hKeq, hcard, hKeq ▸ Kc_le_Uq, ?_⟩
  rw [← hKeq]
  set ψ : ↥(Kc d χ v) →* Multiplicative (V4 d.F) := d.vec.comp (Subgroup.inclusion Kc_le_Uq)
    with hψ
  have hrange : 2 ^ d.k ≤ Nat.card ψ.range := by
    rw [← d.card_F]
    refine Nat.card_le_card_of_injective (fun c => (⟨ψ ⟨kf c, hkf c⟩, ⟨_, rfl⟩⟩ : ↥ψ.range))
      fun c₁ c₂ heq => ?_
    have h1 := congrArg (fun x : ↥ψ.range => Multiplicative.toAdd (x : Multiplicative (V4 d.F))) heq
    have e : ∀ c, ψ ⟨kf c, hkf c⟩ = d.vec (kf c) := fun c => rfl
    simp only [e, hkv] at h1
    exact smul_left_injective d.F hx.ne h1
  have hKcard : Nat.card ↥(Kc d χ v) ≤ 2 ^ d.k := by
    rw [hKeq, card_tImage χ hCT, hcard]
  have hmul : Nat.card ψ.ker * Nat.card ψ.range = Nat.card ↥(Kc d χ v) := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker : Nat.card ψ.ker ≤ 1 := by
    by_contra hc
    push Not at hc
    have h1 : 2 * Nat.card ψ.range ≤ Nat.card ψ.ker * Nat.card ψ.range :=
      Nat.mul_le_mul_right _ hc
    have hpos : 0 < 2 ^ d.k := by positivity
    omega
  have hbot : ψ.ker = ⊥ := (Subgroup.card_le_one_iff_eq_bot _).1 hker
  rw [eq_bot_iff]
  rintro x ⟨hxC, hxK⟩
  have hmem : (⟨x, hxK⟩ : ↥(Kc d χ v)) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    exact (d.ker ⟨x, Kc_le_Uq hxK⟩).2 hxC.2
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)

include hp in
theorem Kc_two (hk : d.k = 1) {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v) :
    Kc d χ v ≤ Subgroup.centralizer (T : Set G) ∧ Uq M T L ⊓ Zq M L ⊓ Kc d χ v = ⊥ ∧
      Nat.card ↥(Uq M T L ⊓ Zq M L) = 2 := by
  have hE := hp.actsMat_E
  have hF2 : Fintype.card d.F = 2 := by rw [d.card, hk, pow_one]
  have h01 := eq_zero_or_eq_one_of_card_two hF2
  have hT : ∀ t ∈ T, ∃ g, ActsMat d.vec t g ∧ mat g *ᵥ v = v := by
    intro t ht
    have htM := h.le ht
    obtain ⟨f, hfb, hfn, hf⟩ := d.exists_add htM
    obtain ⟨g, hg⟩ := d.exists_actsMat htM (pow_eq_one_of_mem_T h ht) hfb hfn hf fun c w => by
      rcases h01 c with rfl | rfl
      · rw [zero_smul, zero_smul, map_zero]
      · rw [one_smul, one_smul]
    refine ⟨g, hg, ?_⟩
    obtain ⟨e, he, het⟩ := hx.all 1
    have heM := tImage_le_M h χ _ he
    have hte : t * e * t⁻¹ ∈ tImage χ (Z0q M T) :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_tImage χ (h.le.trans (le_normalizer_Z0q M T))
        ht) e).1 he
    have h1 : ActsMat d.vec (t * e * t⁻¹) (g * transv v 1 * g⁻¹) :=
      actsMat_mul (inv_mem (d.normU htM)) (actsMat_mul (d.normU heM) hg het) (actsMat_inv hg)
    rw [transv_conj] at h1
    obtain ⟨c, hc⟩ := hx.mem _ hte _ h1
    rcases h01 c with rfl | rfl
    · exfalso
      rw [transv_zero] at hc
      obtain ⟨w, hw⟩ := exists_form_eq_one hx.ne
      have h2 := congrArg (fun x : Sp4 d.F => mat x *ᵥ (mat g *ᵥ w)) hc
      simp only [transv_mulVec, form_mat, hw, mul_one, one_smul, mat_one, Matrix.one_mulVec,
        add_eq_left] at h2
      exact hx.ne (mulVec_mat_injective g (show mat g *ᵥ v = mat g *ᵥ 0 by
        rw [h2, Matrix.mulVec_zero]))
    · exact (transv_eq_transv_iff hx.ne).1 hc
  have hpre : d.pre (d.F ∙ v) ≤ Subgroup.centralizer (T : Set G) := by
    intro u hu
    obtain ⟨huU, hvec⟩ := d.mem_pre.1 hu
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hvec
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨g, hg, hgv⟩ := hT t ht
    have htM := h.le ht
    have h1 := hg ⟨u, huU⟩ ⟨_, conj_mem (d.normU htM) ⟨u, huU⟩⟩ rfl
    rw [← hb, Matrix.mulVec_smul, hgv, hb] at h1
    have h2 := d.lift t htM g hg ⟨u, huU⟩ ((d.ker ⟨_, mul_mem (conj_mem (d.normU htM)
      ⟨u, huU⟩) (inv_mem huU)⟩).1 (by
        have e : (⟨t * u * t⁻¹ * u⁻¹, mul_mem (conj_mem (d.normU htM) ⟨u, huU⟩) (inv_mem huU)⟩ :
            ↥(Uq M T L)) = ⟨_, conj_mem (d.normU htM) ⟨u, huU⟩⟩ * (⟨u, huU⟩ : ↥(Uq M T L))⁻¹ := rfl
        apply Multiplicative.toAdd.injective
        rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, h1, add_neg_cancel]
        rfl))
    calc t * u = t * u * t⁻¹ * t := by group
      _ = u * t := by rw [h2]
  have hKT : Kc d χ v ≤ Subgroup.centralizer (T : Set G) := fun k hk' => hpre hk'.2
  obtain ⟨-, -, -, hfill⟩ := hp.exists_pre_le_Yc hx
  obtain ⟨k₁, hk₁K, hk₁v⟩ := hfill 1
  have hCK : ¬ Uq M T L ⊓ Zq M L ≤ Kc d χ v := by
    intro hle
    have hpreK : d.pre (d.F ∙ v) ≤ Kc d χ v := by
      intro u hu
      obtain ⟨huU, hvec⟩ := d.mem_pre.1 hu
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hvec
      rcases h01 b with rfl | rfl
      · rw [zero_smul, eq_comm] at hb
        refine hle ⟨huU, (d.ker ⟨u, huU⟩).1 ?_⟩
        apply Multiplicative.toAdd.injective
        rw [hb]
        rfl
      · have hr1 : u * (k₁ : G)⁻¹ ∈ Uq M T L := mul_mem huU (inv_mem k₁.2)
        have hr : u * (k₁ : G)⁻¹ ∈ Uq M T L ⊓ Zq M L := by
          refine ⟨hr1, (d.ker ⟨_, hr1⟩).1 ?_⟩
          have e : (⟨u * (k₁ : G)⁻¹, hr1⟩ : ↥(Uq M T L)) = ⟨u, huU⟩ * k₁⁻¹ := rfl
          apply Multiplicative.toAdd.injective
          rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, ← hb, hk₁v, add_neg_cancel]
          rfl
        have := Subgroup.mul_mem _ (hle hr) hk₁K
        rwa [inv_mul_cancel_right] at this
    have h1 : ⁅Uq M T L, tImage χ (Z0q M T)⁆ ≤ tImage χ (Dq M L) := by
      have := (le_sup_left.trans (pre_eq_sup hx hE).ge).trans hpreK
      exact this.trans (fun k hk' => hk'.1)
    have hUT : Uq M T L ≤ T := (Uq_le_Z0q h.L_le).trans (Z0q_le_T h)
    have h2 : ⁅Uq M T L, tImage χ⁻¹ (Z0q M T)⁆ ≤ Dq M L := by
      rw [← tImage_inv_commutator_Uq h χ]
      have hDT : Dq M L ≤ T := inf_le_left.trans h.pCore_le
      have := S36SP.tImage_mono χ⁻¹ h1
      rwa [tImage_inv_tImage χ hDT] at this
    have h3 : ⁅Uq M T L, tImage χ⁻¹ (Z0q M T)⁆ ≤ Uq M T L ⊓ Zq M L := by
      refine fun x hx' => Dq_inf_Uq_le h ⟨h2 hx', ?_⟩
      exact commutator_le_left_of_le_normalizer
        ((tImage_le _ _).trans (h.le.trans (le_normalizer_Uq h.le_normalizer))) hx'
    apply hp.not_tImage_inv_le
    intro y hy
    refine mem_pCoreOf_of_mem_trivW h (tImage_le _ _ hy) ⟨tImage_le_M h χ⁻¹ _ hy, fun u hu => ?_⟩
    have := h3 (Subgroup.commutator_mem_commutator hu hy)
    have e : y * u * y⁻¹ * u⁻¹ = ⁅u, y⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact ((Uq M T L ⊓ Zq M L).inv_mem this).2
  have hCne : Uq M T L ⊓ Zq M L ≠ ⊥ := fun hb => hCK (hb ▸ bot_le)
  have hC2 : Nat.card ↥(Uq M T L ⊓ Zq M L) = 2 := by
    have h1 := d.card_C
    rw [hk, pow_one] at h1
    have h2 := (Subgroup.one_lt_card_iff_ne_bot _).2 hCne
    omega
  refine ⟨hKT, ?_, hC2⟩
  by_contra hne
  apply hCK
  have h1 := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have h2 : Uq M T L ⊓ Zq M L ⊓ Kc d χ v = Uq M T L ⊓ Zq M L :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  rw [← h2]
  exact inf_le_right

end PairHyp

end CFSG.Quasithin.MS93.S36SP
