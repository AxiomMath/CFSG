module

public import CFSG.Quasithin.Vol2.Ch11SecA11SL2
public import CFSG.Milestones.ASVolI.B610.NatFacts
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.Quasithin.Background.B610TwoGen

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem burnsideB610_eq_top_of_perfect {P : Type*} [Group P] [Finite P]
    (hP : commutator P = ⊤) {N : Subgroup P} [N.Normal]
    (hN : ∀ x : P, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect P := Group.isPerfect_def.mpr hP
  have h2 : IsPGroup 2 (P ⧸ N) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hN x
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have hnil : Group.IsNilpotent (P ⧸ N) := h2.isNilpotent
  have hsolv : Group.IsSolvable (P ⧸ N) := inferInstance
  haveI := hperf
  by_contra hne
  have hnt : Nontrivial (P ⧸ N) := by
    obtain ⟨x, hx⟩ : ∃ x : P, x ∉ N := by
      by_contra h
      push Not at h
      exact hne (eq_top_iff.mpr fun x _ => h x)
    exact ⟨⟨(x : P ⧸ N), 1, fun h => hx ((QuotientGroup.eq_one_iff x).mp h)⟩⟩
  exact Group.IsPerfect.not_isSolvable (P ⧸ N) hsolv

variable {G : Type} [Group G] {L V : Subgroup G} {F : Type} [Field F]

theorem burnsideB610_le_twoResidual_sup [Finite G] [Finite F] (D : NatData L V F)
    (h4 : ∃ s : Finset F, s.card = 4) :
    L ≤ twoResidual L ⊔ (L ⊓ Subgroup.centralizer (V : Set G)) := by
  set N : Subgroup ↥(StatedSL 2 F) := ((twoResidual L).subgroupOf L).map D.α with hN
  have hKn : ((twoResidual L).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidual_le L)]
    exact le_normalizer_twoResidual L
  have hNn : N.Normal := Subgroup.Normal.map hKn D.α D.surj
  have hpow : ∀ x : ↥(StatedSL 2 F), ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
    intro x
    obtain ⟨l, rfl⟩ := D.surj x
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient L l l.2
    exact ⟨k, ⟨l ^ 2 ^ k, Subgroup.mem_subgroupOf.mpr (by simpa using hk), map_pow _ _ _⟩⟩
  have hNtop : N = ⊤ := burnsideB610_eq_top_of_perfect (burnsideB610_statedSL_perfect h4) hpow
  intro l hl
  have hmem : D.α ⟨l, hl⟩ ∈ N := by rw [hNtop]; exact Subgroup.mem_top _
  obtain ⟨k, hk, he⟩ := hmem
  have hker : k⁻¹ * ⟨l, hl⟩ ∈ D.α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  rw [D.ker, Subgroup.mem_subgroupOf] at hker
  have e : l = (k : G) * ((k⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hk) hker

theorem burnsideB610_fixV_natImage :
    fixV (CFSG.Quasithin.H.natImage (StatedSL 2 F)) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  set u : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  set l : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have key : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) F,
      (γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd v) = Multiplicative.toAdd v := by
    intro γ
    have h1 := hv (CFSG.Quasithin.H.natAut (StatedSL 2 F) (specialLinearGroupEquivStatedSL 2 F γ))
      ⟨_, rfl⟩
    have h2 := CFSG.Quasithin.H.toAddMap_natAut (StatedSL 2 F)
      (specialLinearGroupEquivStatedSL 2 F γ) (Multiplicative.toAdd v)
    have h3 : CFSG.Quasithin.H.toAddMap
        (CFSG.Quasithin.H.natAut (StatedSL 2 F) (specialLinearGroupEquivStatedSL 2 F γ))
        (Multiplicative.toAdd v) = Multiplicative.toAdd v := by
      show Multiplicative.toAdd ((CFSG.Quasithin.H.natAut (StatedSL 2 F)
        (specialLinearGroupEquivStatedSL 2 F γ)) (Multiplicative.ofAdd (Multiplicative.toAdd v))) = _
      rw [ofAdd_toAdd, h1]
    rw [h3] at h2
    exact h2.symm
  have hu := key u
  have hl := key l
  set w := Multiplicative.toAdd v with hw
  have hu1 := congrFun hu 0
  have hl1 := congrFun hl 1
  simp [u, l, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hu1 hl1
  have hw0 : w = 0 := by
    funext j
    fin_cases j
    · simpa using hl1
    · simpa using hu1
  rw [Subgroup.mem_bot]
  have : v = Multiplicative.ofAdd w := by rw [hw, ofAdd_toAdd]
  rw [this, hw0]
  rfl

theorem burnsideB610_fixV_img_twoResidual [Finite G] [Finite F] (D : NatData L V F)
    (h4 : ∃ s : Finset F, s.card = 4) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {K : Subgroup G} (hK : twoResidual L ≤ K) : fixV (D.img K) = ⊥ := by
  rw [eq_bot_iff, ← burnsideB610_fixV_natImage (F := F)]
  intro v hv φ hφ
  obtain ⟨γ, rfl⟩ := hφ
  obtain ⟨l, rfl⟩ := D.surj γ
  have hl := burnsideB610_le_twoResidual_sup D h4 l.2
  have hCn : twoResidual L ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (twoResidual_le L hg),
      B6.le_normalizer_centralizer hLV (twoResidual_le L hg)⟩
  have hl' : (l : G) ∈ ((twoResidual L ⊔ (L ⊓ Subgroup.centralizer (V : Set G)) : Subgroup G) :
      Set G) := hl
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCn] at hl'
  obtain ⟨k, hk, c, hc, hkc⟩ := hl'
  have hkL : k ∈ L := twoResidual_le L hk
  set k' : ↥(nLV L V) := ⟨k, Subgroup.le_normalizer hkL, hLV hkL⟩ with hk'
  set c' : ↥(nLV L V) := ⟨c, Subgroup.le_normalizer hc.1, hLV hc.1⟩ with hc'
  have hact : CFSG.Quasithin.H.natAut (StatedSL 2 F) (D.α l) = D.act k' * D.act c' := by
    rw [← D.act_of_mem hLV l, ← map_mul]
    congr 1
    exact Subtype.ext hkc.symm
  rw [hact, D.act_eq_one hLV c' hc.2, mul_one]
  exact hv _ ⟨k', Subgroup.mem_subgroupOf.mpr (hK hk), rfl⟩

theorem burnsideB610_mem_centralizer_of_act_eq_one (D : NatData L V F)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {l : G} (hl : l ∈ L)
    (h : D.act ⟨l, Subgroup.le_normalizer hl, hLV hl⟩ = 1) :
    l ∈ Subgroup.centralizer (V : Set G) := by
  rw [D.act_of_mem hLV ⟨l, hl⟩] at h
  have h3 : D.α ⟨l, hl⟩ = 1 := by
    apply H.natAut_injective (StatedSL 2 F)
    rw [h, map_one]
  have h4 : (⟨l, hl⟩ : ↥L) ∈ D.α.ker := h3
  rw [D.ker, Subgroup.mem_subgroupOf] at h4
  exact h4.2

theorem burnsideB610_gen [Finite G] [Finite F] [CharP F 2] (D : NatData L V F)
    (h4 : ∃ s : Finset F, s.card = 4) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {P : Subgroup G} (hPL : P ≤ L)
    (hP2 : IsPGroup 2 P) (hPc : Nat.card (D.img P) = Nat.card F) :
    ∃ k ∈ twoResidual L, autI hV L ≤ autI hV P ⊔ autI hV (cjSub k P) := by
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := hPL.trans hLV
  have hPnLV : P ≤ nLV L V := fun x hx => ⟨Subgroup.le_normalizer (hPL hx), hPV hx⟩
  have hcard1 := card_autI_mul_card_inf hV hPV
  have hker : ∀ a : ↥(nLV L V), (a : G) ∈ P → D.act a = 1 →
      (a : G) ∈ Subgroup.centralizer (V : Set G) := fun a haP h =>
    burnsideB610_mem_centralizer_of_act_eq_one D hLV (hPL haP) h
  have hcard2 : Nat.card (D.img P) * Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card P := by
    set f : ↥(P.subgroupOf (nLV L V)) →* MulAut (CFSG.Quasithin.H.StdMod (Fin 2) F) :=
      D.act.comp (P.subgroupOf (nLV L V)).subtype with hf
    have e1 := Subgroup.card_ker_mul_card_range f
    have hr : f.range = D.img P := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    have hc : Nat.card ↥(P.subgroupOf (nLV L V)) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPnLV).toEquiv
    set ι : ↥(P.subgroupOf (nLV L V)) →* G :=
      (nLV L V).subtype.comp (P.subgroupOf (nLV L V)).subtype with hι
    have hιinj : Function.Injective ι := (nLV L V).subtype_injective.comp Subtype.val_injective
    have hk : f.ker.map ι = P ⊓ Subgroup.centralizer (V : Set G) := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨Subgroup.mem_subgroupOf.mp x.2, hker _ (Subgroup.mem_subgroupOf.mp x.2) hx⟩
      · rintro ⟨hgP, hgC⟩
        exact ⟨⟨⟨g, hPnLV hgP⟩, Subgroup.mem_subgroupOf.mpr hgP⟩, D.act_eq_one hLV _ hgC, rfl⟩
    have e2 : Nat.card f.ker = Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) := by
      rw [← hk, Subgroup.card_map_of_injective hιinj]
    rw [← hr, ← e2, ← hc, mul_comm]
    exact e1
  have hcard : Nat.card (autI hV P) = Nat.card F := by
    have hpos : 0 < Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
    rw [← hPc]
    exact Nat.eq_of_mul_eq_mul_right hpos (hcard1.trans hcard2.symm)
  obtain ⟨ℓ, hℓ, hgen⟩ := D.exists_conj_gen hV hLV (autI_mono hV hPL)
    (B2F.isPGroup_autI hV hP2 hPV) hcard
  have hl := burnsideB610_le_twoResidual_sup D h4 hℓ
  have hCn : twoResidual L ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (twoResidual_le L hg),
      B6.le_normalizer_centralizer hLV (twoResidual_le L hg)⟩
  have hl' : ℓ ∈ ((twoResidual L ⊔ (L ⊓ Subgroup.centralizer (V : Set G)) : Subgroup G) :
      Set G) := hl
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCn] at hl'
  obtain ⟨k, hk, c, hc, rfl⟩ := hl'
  have hkV : k ∈ Subgroup.normalizer (V : Set G) := hLV (twoResidual_le L hk)
  have hcV : c ∈ Subgroup.normalizer (V : Set G) := hLV hc.1
  refine ⟨k, hk, ?_⟩
  have hconv : convI hV ⟨k * c, hLV hℓ⟩ = convI hV ⟨k, hkV⟩ := by
    have h1 : convI hV ⟨c, hcV⟩ = 1 := (convI_eq_one_iff hV _).2 hc.2
    have h2 : (⟨k * c, hLV hℓ⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨k, hkV⟩ * ⟨c, hcV⟩ := rfl
    rw [h2, map_mul, h1, mul_one]
  rw [hconv] at hgen
  rw [← autI_cjSub hV hkV P]
  have he : B1.conjAut (convI hV ⟨k, hkV⟩) (autI hV P) =
      (autI hV P).map (MulAut.conj (convI hV ⟨k, hkV⟩)).toMonoidHom := by
    ext x
    rw [B1.mem_conjAut, Subgroup.mem_map_equiv]
    simp
  rw [he] at hgen
  exact hgen

theorem burnsideB610_isQuasisimple_autI (D : NatData L V F) (h4 : ∃ s : Finset F, s.card = 4)
    (hV : IsElemAbelian 2 V) (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    CFSG.Open.IsQuasisimple ↥(autI hV L) := by
  obtain ⟨ψ, hψi, hψr⟩ := D.exists_psi hV hLV
  have hq := CFSG.Quasithin.Vol2.Ch11.SecA.isQuasisimple_SL2 h4
  have hq' : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(autI hV L) :=
    (MonoidHom.ofInjective hψi).trans (MulEquiv.subgroupCongr hψr)
  exact hq'.of_mulEquiv e.symm

end CFSG.Quasithin.B610T
