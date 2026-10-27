module

public import CFSG.Quasithin.Vol2.Ch4Sec2W4213
public import CFSG.Quasithin.Vol2.Ch4Sec4W4414Z
public import CFSG.Quasithin.Background.C2Nine

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp4_2_3 (G : Type) [Group G] [Finite G] (T M L Mm I : Subgroup G) : Prop
    extends Hyp4_2_1 G T M L where
  sigma : IsSigma M (conjClosure L T) Mm
  conjT : ∀ t ∈ T, ∃ m ∈ Mm, CFSG.conjugate L t = CFSG.conjugate L m
  conjMm : ∀ m ∈ Mm, ∃ t ∈ T, CFSG.conjugate L m = CFSG.conjugate L t
  gammaStar : IsGammaStar M (conjClosure L T) Mm I
  R_le : pCoreOf 2 I ≤
    T ⊓ centralizerSection M (conjClosure L T) (pCoreOf 2 (conjClosure L T))

@[expose] def Thm4_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H : Subgroup G), Hyp4_2_3 G T M L Mm I →
    InM I H → H ≠ M → ¬ oTwoFstarIn H ≤ M

namespace Hyp4_2_1

variable {T M L : Subgroup G} (h : Hyp4_2_1 G T M L)
include h

theorem pCoreOf_le_pCoreOf_conjClosure (h37 : A37ForSQTK) (h39 : A39ForSQTK) :
    pCoreOf 2 L ≤ pCoreOf 2 (conjClosure L T) :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans (le_conjClosure L T))
    ((conjClosure_le_normalizer_of_hyp421 h h37 h39).trans
      (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)

theorem centralizerSection_le_normalizer (h37 : A37ForSQTK) (h39 : A39ForSQTK) :
    centralizerSection M (conjClosure L T) (pCoreOf 2 (conjClosure L T)) ≤
      Subgroup.normalizer (L : Set G) := by
  intro q hqC
  set Mp := conjClosure L T with hMp
  set Q := pCoreOf 2 Mp with hQ
  have hLc : L ∈ cComp M := h.mem_cComp h37 h39
  have hO2M : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal h.maxTwoLocal.1
  have hLMp : L ≤ Mp := le_conjClosure L T
  have hqM : q ∈ M := hqC.1
  have hLq := map_conj_mem_cComp hLc hqM
  by_contra hqN
  have he : L.map (MulAut.conj q).toMonoidHom ≠ L := fun h' =>
    hqN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h')
  have hc := (lemma_1_2_1_two h.qtke h.simple h.nonabelian h37 hO2M hLc hLq (Ne.symm he)).1
  have hO2LQ : pCoreOf 2 L ≤ Q := h.pCoreOf_le_pCoreOf_conjClosure h37 h39
  have hLqMp : L.map (MulAut.conj q).toMonoidHom ≤ Mp := by
    rintro _ ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hqC.2.1 l).mp (hLMp hl)
  have hLQ : ∀ l ∈ L, l ∈ ((L.map (MulAut.conj q).toMonoidHom : Subgroup G) : Set G) *
      (Q : Set G) := by
    intro l hl
    refine ⟨q * l * q⁻¹, ⟨l, hl, rfl⟩, (q * l * q⁻¹)⁻¹ * l, ?_, by group⟩
    have h1 := hqC.2.2.2 l⁻¹ (Mp.inv_mem (hLMp hl))
    have h2 := Q.inv_mem h1
    have e : (l⁻¹ * q * l⁻¹⁻¹ * q⁻¹)⁻¹ = (q * l * q⁻¹)⁻¹ * l := by group
    rwa [e] at h2
  have hLL : ⁅L, L⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨x, hx, y, hy, rfl⟩ := hLQ b hb
    have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine Q.mul_mem (hO2LQ ((hc.trans inf_le_left) (Subgroup.commutator_mem_commutator ha hx)))
      ?_
    have h1 : ⁅a, y⁆ ∈ Q := by
      rw [commutatorElement_def]
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mp (hLMp ha)) y).mp hy
      exact Q.mul_mem this (Q.inv_mem hy)
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mp (hLqMp hx)) _).mp h1
  have hLle : L ≤ Q := calc L = ⁅L, L⁆ := h.perfect.symm
    _ ≤ Q := hLL
  exact ne_bot_of_mem_cComp hLc (eq_bot_of_commutator_eq_self_of_isPGroup_two
    h.perfect ((pCoreOf_isPGroup 2 Mp).to_le hLle))

theorem pCoreOf_sup_le_centralizerSection :
    pCoreOf 2 (L ⊔ T) ≤ centralizerSection M (conjClosure L T) (pCoreOf 2 (conjClosure L T)) := by
  set Mp := conjClosure L T with hMp
  set Rp := pCoreOf 2 (L ⊔ T) with hRp
  have hMpLT : Mp ≤ L ⊔ T := CFSG.Quasithin.conjClosure_le fun t ht l hl =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer
      (Subgroup.mem_sup_right ht : t ∈ L ⊔ T)) l).mp (Subgroup.mem_sup_left hl)
  have hLTMp : L ⊔ T ≤ Subgroup.normalizer (Mp : Set G) :=
    _root_.sup_le ((le_conjClosure L T).trans Subgroup.le_normalizer)
      (CFSG.Quasithin.le_normalizer_conjClosure L T)
  have hRpMp : Rp ≤ Subgroup.normalizer (Mp : Set G) := (pCoreOf_le 2 _).trans hLTMp
  have hMpRp : Mp ≤ Subgroup.normalizer (Rp : Set G) := hMpLT.trans (le_normalizer_pCoreOf 2 _)
  refine (le_centralizerSection_iff (pCoreOf_le 2 Mp)).mpr ⟨(pCoreOf_le 2 _).trans h.sup_le, ?_⟩
  have hc1 : ⁅Mp, Rp⁆ ≤ Mp := Subgroup.le_normalizer_iff_commutator_le_left.mp hRpMp
  have hc2 : ⁅Mp, Rp⁆ ≤ Rp := Subgroup.le_normalizer_iff_commutator_le_right.mp hMpRp
  refine (le_inf hc1 hc2).trans (le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((pCoreOf_isPGroup 2 _).to_le inf_le_right))
  exact fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm) (hMpRp hm)

theorem conjClosure_le_inf_sup (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {I : Subgroup G} (hIM : I ≤ M)
    (hLI : (L : Set G) ⊆ (I : Set G) * (pCoreOf 2 (L ⊔ T) : Set G))
    (hTI : ∀ t ∈ T, ∃ i ∈ I, CFSG.conjugate L t = CFSG.conjugate L i) :
    conjClosure L T ≤ (I ⊓ conjClosure L T) ⊔ pCoreOf 2 (conjClosure L T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Mp := conjClosure L T with hMp
  set Rp := pCoreOf 2 (L ⊔ T) with hRpdef
  set Q := pCoreOf 2 Mp with hQ
  have hLT : L ⊔ T ≤ Subgroup.normalizer (Rp : Set G) := le_normalizer_pCoreOf 2 _
  have hRpL : Rp ≤ Subgroup.normalizer (L : Set G) :=
    h.pCoreOf_sup_le_centralizerSection.trans (h.centralizerSection_le_normalizer h37 h39)
  set Y := L ⊔ Rp with hY
  have hYLT : Y ≤ L ⊔ T := _root_.sup_le le_sup_left (pCoreOf_le 2 _)
  have hYRp : Y ≤ Subgroup.normalizer (Rp : Set G) := hYLT.trans hLT
  have hYL : Y ≤ Subgroup.normalizer (L : Set G) := _root_.sup_le Subgroup.le_normalizer hRpL
  have h1 : L ≤ (I ⊓ Y) ⊔ Rp := by
    intro l hl
    obtain ⟨i, hi, r, hr, hir⟩ := hLI hl
    have hiY : i ∈ Y := by
      have e : i = l * r⁻¹ := by rw [← hir]; group
      rw [e]
      exact Y.mul_mem (Subgroup.mem_sup_left hl) (Y.inv_mem (Subgroup.mem_sup_right hr))
    rw [← hir]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hi, hiY⟩) (Subgroup.mem_sup_right hr)
  have h2 : oTwoUpper Y ≤ oTwoUpper (Y ⊓ (I ⊓ Y)) ⊔ Rp :=
    oTwoUpper_le_sup_of_le_sup (_root_.sup_le h1 le_sup_right) (inf_le_right.trans hYRp)
      le_sup_right
  rw [inf_eq_right.mpr inf_le_right] at h2
  have h3 : oTwoUpper Y ≤ L := by
    refine oTwoUpper_le_of_pow_mem fun y hy => ?_
    obtain ⟨r, hr, l, hl, rfl⟩ := (mem_sup_of_le_normalizer hRpL).mp
      (show y ∈ Rp ⊔ L by rwa [sup_comm])
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 (L ⊔ T))) ⟨r, hr⟩
    refine ⟨k, ?_⟩
    have hlr : r * l * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hRpL hr) l).mp hl
    obtain ⟨x', hx', he⟩ := A4.exists_pow_mul_eq hlr (hRpL hr) (2 ^ k)
    have e : r * l = r * l * r⁻¹ * r := by group
    have hrk : r ^ 2 ^ k = 1 := by
      have := pow_orderOf_eq_one (⟨r, hr⟩ : ↥Rp)
      rw [hk] at this
      exact congrArg Subtype.val this
    rw [e, he, hrk, mul_one]
    exact hx'
  have hLp : oTwoUpper L = L := C2Nine.oTwoUpper_eq_of_perfect h.perfect
  set J := oTwoUpper (I ⊓ Y) with hJ
  have h4 : L ≤ J ⊔ Rp := calc L = oTwoUpper L := hLp.symm
    _ ≤ oTwoUpper Y := oTwoUpper_mono le_sup_left
    _ ≤ J ⊔ Rp := h2
  have hJL : J ≤ L := (oTwoUpper_mono inf_le_right).trans h3
  have hJI : J ≤ I := (oTwoUpper_le _).trans inf_le_left
  have hJRp : J ≤ Subgroup.normalizer (Rp : Set G) :=
    ((oTwoUpper_le _).trans inf_le_right).trans hYRp
  have h6 : Rp ⊓ L ≤ pCoreOf 2 L :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun x hx => mem_normalizer_inf ((le_sup_left.trans hLT) hx) (Subgroup.le_normalizer hx))
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
  have hL : ∀ l ∈ L, ∃ a ∈ I ⊓ L, ∃ b ∈ pCoreOf 2 L, l = a * b := by
    intro l hl
    obtain ⟨j, hj, r, hr, hjr⟩ := (mem_sup_of_le_normalizer hJRp).mp (h4 hl)
    have hrL : r ∈ L := by
      have := L.mul_mem (L.inv_mem (hJL hj)) hl
      rw [← hjr] at this
      simpa using this
    exact ⟨j, ⟨hJI hj, hJL hj⟩, r, h6 ⟨hr, hrL⟩, hjr.symm⟩
  have hO2 : pCoreOf 2 L ≤ Q := h.pCoreOf_le_pCoreOf_conjClosure h37 h39
  have hMN : M ≤ Subgroup.normalizer (Mp : Set G) := h.le_normalizer_conjClosure h37 h38 h39
  refine CFSG.Quasithin.conjClosure_le fun t ht l hl => ?_
  obtain ⟨i, hi, hti⟩ := hTI t⁻¹ (T.inv_mem ht)
  have hmem : t * l * t⁻¹ ∈ CFSG.conjugate L t⁻¹ := by
    refine ⟨l, hl, ?_⟩
    simp [MulAut.conj_apply]
  rw [hti] at hmem
  obtain ⟨l', hl', hl'e⟩ := hmem
  replace hl'e : i⁻¹ * l' * i = t * l * t⁻¹ := by simpa [MulAut.conj_apply] using hl'e
  obtain ⟨a, ha, b, hb, rfl⟩ := hL l' hl'
  have hiN := hMN (hIM hi)
  have hiQ := (normalizer_le_normalizer_pCoreOf 2 Mp) hiN
  have hbQ : i⁻¹ * b * i ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hiQ) b).mp (hO2 hb)
    simpa using this
  have haMp : i⁻¹ * a * i ∈ Mp := by
    have hab : i⁻¹ * (a * b) * i * (i⁻¹ * b * i)⁻¹ = i⁻¹ * a * i := by group
    rw [← hab, hl'e]
    exact Mp.mul_mem (mem_conjClosure ht hl) (Mp.inv_mem ((pCoreOf_le 2 Mp) hbQ))
  have haI : i⁻¹ * a * i ∈ I := I.mul_mem (I.mul_mem (I.inv_mem hi) ha.1) hi
  rw [← hl'e]
  have e : i⁻¹ * (a * b) * i = (i⁻¹ * a * i) * (i⁻¹ * b * i) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨haI, haMp⟩) (Subgroup.mem_sup_right hbQ)

theorem isSigma_4212 {I : Subgroup G} (hIM : I ≤ M) :
    IsSigma M (conjClosure L T) (conjClosure L T ⊔
      centralizerSection M (conjClosure L T) (pCoreOf 2 (conjClosure L T)) ⊔ I) :=
  ⟨_root_.sup_le (_root_.sup_le (CFSG.Quasithin.conjClosure_le fun t ht l hl => by
      exact M.mul_mem (M.mul_mem (h.T_le ht) (h.L_le hl)) (M.inv_mem (h.T_le ht)))
    (centralizerSection_le_left _ _ _)) hIM, le_sup_left⟩

theorem isIota_4212 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {I : Subgroup G} (hIM : I ≤ M)
    (hLI : (L : Set G) ⊆ (I : Set G) * (pCoreOf 2 (L ⊔ T) : Set G))
    (hTI : ∀ t ∈ T, ∃ i ∈ I, CFSG.conjugate L t = CFSG.conjugate L i)
    (hI : pCoreOf 2 I ≠ ⊥) :
    IsIota M (conjClosure L T) (conjClosure L T ⊔
      centralizerSection M (conjClosure L T) (pCoreOf 2 (conjClosure L T)) ⊔ I) I := by
  set Mp := conjClosure L T with hMp
  set C := centralizerSection M Mp (pCoreOf 2 Mp) with hC
  have hMpM : Mp ≤ M := (le_sup_left.trans le_sup_left).trans (h.isSigma_4212 hIM).1
  have hle := h.conjClosure_le_inf_sup h37 h38 h39 hIM hLI hTI
  have hMpIC : Mp ≤ I ⊔ C :=
    hle.trans (sup_le_sup inf_le_left (pCoreOf_le_centralizerSection hMpM))
  refine ⟨le_sup_right,
    le_antisymm (_root_.sup_le le_sup_right (le_sup_right.trans le_sup_left)) ?_,
    hle.trans (sup_le_sup_right inf_le_left _), hI⟩
  exact _root_.sup_le (_root_.sup_le hMpIC le_sup_right) le_sup_left

theorem isGamma_4212 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {I : Subgroup G} (hIM : I ≤ M)
    (hLI : (L : Set G) ⊆ (I : Set G) * (pCoreOf 2 (L ⊔ T) : Set G))
    (hTI : ∀ t ∈ T, ∃ i ∈ I, CFSG.conjugate L t = CFSG.conjugate L i)
    (hI : pCoreOf 2 I ≠ ⊥) (hU : ¬ IsUniqueM I M) :
    IsGamma M (conjClosure L T) (conjClosure L T ⊔
      centralizerSection M (conjClosure L T) (pCoreOf 2 (conjClosure L T)) ⊔ I) I :=
  ⟨h.isIota_4212 h37 h38 h39 hIM hLI hTI hI,
    exists_inH_not_le_of_not_isUniqueM h.maxTwoLocal hIM hU⟩

end Hyp4_2_1

theorem exists_isGammaStar_ordLE {M Mp Mm I : Subgroup G} (hI : IsGamma M Mp Mm I) :
    ∃ I₁ : Subgroup G, IsGammaStar M Mp Mm I₁ ∧ OrdLE Mp I I₁ := by
  classical
  let S : Set (Subgroup G) := {I₁ | IsGamma M Mp Mm I₁ ∧ OrdLE Mp I I₁}
  have hIS : I ∈ S := ⟨hI, le_rfl, le_rfl⟩
  obtain ⟨I₁, hI₁, hmax⟩ := Set.Finite.exists_maximalFor
    (fun J => Nat.card ↥(pCoreOf 2 J)) S (Set.toFinite S) ⟨I, hIS⟩
  refine ⟨I₁, ⟨hI₁.1, fun I₂ hI₂ hle hlt => ?_⟩, hI₁.2⟩
  have hI₂S : I₂ ∈ S := ⟨hI₂, hI₁.2.1.trans hle.1, hI₁.2.2.trans hle.2⟩
  have hcard : Nat.card ↥(pCoreOf 2 I₁) < Nat.card ↥(pCoreOf 2 I₂) :=
    Subgroup.card_lt_of_lt hlt
  exact absurd (hmax hI₂S hcard.le) (not_le.mpr hcard)

section Conj

variable {M Mp Mm : Subgroup G} {c : G}

omit [Finite G] in
theorem pCoreOf_map_conj (X : Subgroup G) (c : G) :
    pCoreOf 2 (X.map (MulAut.conj c).toMonoidHom) =
      (pCoreOf 2 X).map (MulAut.conj c).toMonoidHom :=
  CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj c) X

omit [Finite G] in
theorem map_conj_le_map_conj_iff {X Y : Subgroup G} (c : G) :
    X.map (MulAut.conj c).toMonoidHom ≤ Y.map (MulAut.conj c).toMonoidHom ↔ X ≤ Y :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj c).injective

omit [Finite G] in
theorem le_map_conj_iff {X Y : Subgroup G} (c : G) :
    X ≤ Y.map (MulAut.conj c).toMonoidHom ↔ X.map (MulAut.conj c⁻¹).toMonoidHom ≤ Y := by
  rw [← map_conj_le_map_conj_iff c⁻¹, map_conj_inv_map_conj]

omit [Finite G] in
theorem isIota_map_conj (hcMm : c ∈ Subgroup.normalizer (Mm : Set G))
    (hcMp : c ∈ Subgroup.normalizer (Mp : Set G))
    (hcC : c ∈ Subgroup.normalizer (centralizerSection M Mp (pCoreOf 2 Mp) : Set G))
    {I : Subgroup G} (hI : IsIota M Mp Mm I) :
    IsIota M Mp Mm (I.map (MulAut.conj c).toMonoidHom) := by
  have hcQ : c ∈ Subgroup.normalizer (pCoreOf 2 Mp : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 Mp hcMp
  refine ⟨(map_conj_mono hI.1 c).trans (map_conj_le_of_mem_normalizer hcMm), ?_, ?_, ?_⟩
  · rw [← map_conj_eq_of_mem_normalizer hcC, ← Subgroup.map_sup, hI.2.1,
      map_conj_eq_of_mem_normalizer hcMm]
  · have := map_conj_mono hI.2.2.1 c
    rwa [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hcMp,
      map_conj_eq_of_mem_normalizer hcQ] at this
  · rw [pCoreOf_map_conj, Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c).injective]
    exact hI.2.2.2

omit [Finite G] in
theorem isGamma_map_conj (hcM : c ∈ M) (hcMm : c ∈ Subgroup.normalizer (Mm : Set G))
    (hcMp : c ∈ Subgroup.normalizer (Mp : Set G))
    (hcC : c ∈ Subgroup.normalizer (centralizerSection M Mp (pCoreOf 2 Mp) : Set G))
    {I : Subgroup G} (hI : IsGamma M Mp Mm I) :
    IsGamma M Mp Mm (I.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨H, hH, hHM⟩ := hI.2
  refine ⟨isIota_map_conj hcMm hcMp hcC hI.1, H.map (MulAut.conj c).toMonoidHom,
    ⟨map_conj_mono hH.1 c, ?_⟩, fun hle => hHM ?_⟩
  · rw [pCoreOf_map_conj, Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c).injective]
    exact hH.2
  · rw [← map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hcM),
      map_conj_le_map_conj_iff] at hle
    exact hle

omit [Finite G] in
theorem isGammaStar_map_conj (hcM : c ∈ M) (hcMm : c ∈ Subgroup.normalizer (Mm : Set G))
    (hcMp : c ∈ Subgroup.normalizer (Mp : Set G))
    (hcC : c ∈ Subgroup.normalizer (centralizerSection M Mp (pCoreOf 2 Mp) : Set G))
    {I : Subgroup G} (hI : IsGammaStar M Mp Mm I) :
    IsGammaStar M Mp Mm (I.map (MulAut.conj c).toMonoidHom) := by
  refine ⟨isGamma_map_conj hcM hcMm hcMp hcC hI.1, fun I₂ hI₂ hle hlt => ?_⟩
  have hinv := fun {X : Subgroup G} (hX : c ∈ Subgroup.normalizer (X : Set G)) =>
    Subgroup.inv_mem _ hX
  set I₃ := I₂.map (MulAut.conj c⁻¹).toMonoidHom with hI₃
  have hI₃G : IsGamma M Mp Mm I₃ :=
    isGamma_map_conj (M.inv_mem hcM) (hinv hcMm) (hinv hcMp) (hinv hcC) hI₂
  have hMpc : Mp.map (MulAut.conj c⁻¹).toMonoidHom = Mp :=
    map_conj_eq_of_mem_normalizer (hinv hcMp)
  have e1 : pCoreOf 2 I = (pCoreOf 2 (I.map (MulAut.conj c).toMonoidHom)).map
      (MulAut.conj c⁻¹).toMonoidHom := by
    rw [pCoreOf_map_conj, map_conj_inv_map_conj]
  have e2 : pCoreOf 2 I₃ = (pCoreOf 2 I₂).map (MulAut.conj c⁻¹).toMonoidHom := pCoreOf_map_conj _ _
  refine hI.2 I₃ hI₃G ⟨?_, ?_⟩ ?_
  · rw [e2, e1]
    exact map_conj_mono hle.1 c⁻¹
  · have h1 := map_conj_mono hle.2 c⁻¹
    rw [Subgroup.map_inf_eq _ _ (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective,
      Subgroup.map_inf_eq _ _ (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective,
      map_conj_inv_map_conj, hMpc] at h1
    exact h1
  · rw [e2, e1]
    exact (Subgroup.map_lt_map_iff_of_injective (MulAut.conj c⁻¹).injective).mpr hlt

end Conj

omit [Finite G] in
theorem conjugate_mul_eq_of_mem_normalizer {L : Subgroup G} {t g : G}
    (hg : t * g * t⁻¹ ∈ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate L (t * g) = CFSG.conjugate L t := by
  have hcc : CFSG.conjugate (CFSG.conjugate L (t * g * t⁻¹)) t =
      CFSG.conjugate L ((t * g * t⁻¹) * t) := by
    simp only [CFSG.conjugate, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have e : t * g = (t * g * t⁻¹) * t := by group
  rw [e, ← hcc]
  congr 1
  exact map_conj_eq_of_mem_normalizer (Subgroup.inv_mem _ hg)


namespace Hyp4_2_1

variable {T M L : Subgroup G} (h : Hyp4_2_1 G T M L)
include h

theorem exists_conjugate_eq (h37 : A37ForSQTK) (h39 : A39ForSQTK) {I : Subgroup G}
    (hTI : ∀ t ∈ T, ∃ i ∈ I, CFSG.conjugate L t = CFSG.conjugate L i)
    (hIT : ∀ i ∈ I, ∃ t ∈ T, CFSG.conjugate L i = CFSG.conjugate L t) {m : G}
    (hm : m ∈ conjClosure L T ⊔
      centralizerSection M (conjClosure L T) (pCoreOf 2 (conjClosure L T)) ⊔ I) :
    ∃ t ∈ T, CFSG.conjugate L m = CFSG.conjugate L t := by
  set Mp := conjClosure L T with hMp
  set C := centralizerSection M Mp (pCoreOf 2 Mp) with hC
  have hMpN : Mp ≤ Subgroup.normalizer (L : Set G) := conjClosure_le_normalizer_of_hyp421 h h37 h39
  have hCN : C ≤ Subgroup.normalizer (L : Set G) := h.centralizerSection_le_normalizer h37 h39
  have hTMp : T ≤ Subgroup.normalizer (Mp : Set G) := CFSG.Quasithin.le_normalizer_conjClosure L T
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := fun t ht =>
    le_normalizer_centralizerSection M Mp ⟨h.T_le ht, hTMp ht⟩
  have conjugate_conjugate : ∀ (a b : G),
      CFSG.conjugate (CFSG.conjugate L a) b = CFSG.conjugate L (a * b) := by
    intro a b
    simp only [CFSG.conjugate, Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  let P : G → Prop := fun g => ∀ t ∈ T, ∃ t' ∈ T, CFSG.conjugate L (t * g) = CFSG.conjugate L t'
  have hgen : ∀ x ∈ (Mp : Set G) ∪ C ∪ I, P x := by
    rintro x ((hx | hx) | hx) t ht
    · refine ⟨t, ht, conjugate_mul_eq_of_mem_normalizer (hMpN ?_)⟩
      exact (Subgroup.mem_normalizer_iff.mp (hTMp ht) x).mp hx
    · refine ⟨t, ht, conjugate_mul_eq_of_mem_normalizer (hCN ?_)⟩
      exact (Subgroup.mem_normalizer_iff.mp (hTC ht) x).mp hx
    · obtain ⟨i, hi, hti⟩ := hTI t ht
      obtain ⟨t', ht', he⟩ := hIT (i * x) (I.mul_mem hi hx)
      refine ⟨t', ht', ?_⟩
      rw [← conjugate_conjugate, hti, conjugate_conjugate, he]
  have hMm : Mp ⊔ C ⊔ I = Subgroup.closure ((Mp : Set G) ∪ C ∪ I) := by
    rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
      Subgroup.closure_eq]
  rw [hMm] at hm
  have hP : P m := by
    induction hm using Subgroup.closure_induction'' with
    | mem x hx => exact hgen x hx
    | inv_mem x hx =>
      refine hgen x⁻¹ ?_
      rcases hx with (hx | hx) | hx
      · exact Or.inl (Or.inl (Mp.inv_mem hx))
      · exact Or.inl (Or.inr (C.inv_mem hx))
      · exact Or.inr (I.inv_mem hx)
    | one => exact fun t ht => ⟨t, ht, by rw [mul_one]⟩
    | mul x y _ _ hx hy =>
      intro t ht
      obtain ⟨t', ht', he⟩ := hx t ht
      obtain ⟨t'', ht'', he'⟩ := hy t' ht'
      refine ⟨t'', ht'', ?_⟩
      rw [← mul_assoc, ← conjugate_conjugate, he, conjugate_conjugate, he']
  obtain ⟨t, ht, he⟩ := hP 1 T.one_mem
  exact ⟨t, ht, by rwa [one_mul] at he⟩

end Hyp4_2_1

theorem stmt4_2_13FF_of_hyp4_2_3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmain : ∀ (G : Type) [Group G] [Finite G] (T M L Mm I : Subgroup G),
      Hyp4_2_3 G T M L Mm I →
        (Concl443TwoI G T M L ⁅reducedAggregate (L ⊔ T), L⁆ ∧
          IrrCase4213 G L ⁅reducedAggregate (L ⊔ T), L⁆) ∨
          Orth4213 G M L ⁅reducedAggregate (L ⊔ T), L⁆) :
    Stmt4_2_13FF := by
  intro G _ _ T M L I hs hnab hK hT hM hTM hL hLf hLM hq hIM hLI hTI hIT hI
  by_cases hU : IsUniqueM I M
  · exact Or.inl hU
  right
  have h : Hyp4_2_1 G T M L := ⟨hs, hnab, hK, hT, hM, hTM, hL, hLf, hLM, hq⟩
  set Mp := conjClosure L T with hMp
  set C := centralizerSection M Mp (pCoreOf 2 Mp) with hC
  set Mm := Mp ⊔ C ⊔ I with hMm
  have h41 := lemma_4_2_2 h37 h38 h39 h
  have hS : IsSigma M Mp Mm := h.isSigma_4212 hIM
  obtain ⟨I₁, hI₁, -⟩ := exists_isGammaStar_ordLE (h.isGamma_4212 h37 h38 h39 hIM hLI hTI hI hU)
  have hTsyl : IsSylowTwoOf (T ⊓ C) C :=
    isSylowTwoOf_inf_centralizerSection (isSylowTwoOf_of_le h.sylow
      (le_inf h.T_le (CFSG.Quasithin.le_normalizer_conjClosure L T)))
  obtain ⟨c, hcC, hcle⟩ := exists_conj_le_of_isSylowTwoOf hTsyl
    (lemma_4_1_4_one h41 hS hI₁.1.1) (pCoreOf_isPGroup 2 I₁)
  have hcM : c ∈ M := centralizerSection_le_left _ _ _ hcC
  have hcMp : c ∈ Subgroup.normalizer (Mp : Set G) := hcC.2.1
  have hcMm : c ∈ Subgroup.normalizer (Mm : Set G) :=
    Subgroup.le_normalizer ((le_sup_right.trans le_sup_left : C ≤ Mm) hcC)
  have hcCN : c ∈ Subgroup.normalizer (C : Set G) := Subgroup.le_normalizer hcC
  have hI₂ := isGammaStar_map_conj hcM hcMm hcMp hcCN hI₁
  have hcj : cjSub c (pCoreOf 2 I₁) = (pCoreOf 2 I₁).map (MulAut.conj c).toMonoidHom := by
    ext x
    rw [mem_cjSub, mem_map_conj_iff]
  refine hmain G T M L Mm (I₁.map (MulAut.conj c).toMonoidHom)
    ⟨h, hS, fun t ht => ?_, fun m hm => h.exists_conjugate_eq h37 h39 hTI hIT hm, hI₂, ?_⟩
  · obtain ⟨i, hi, he⟩ := hTI t ht
    exact ⟨i, (le_sup_right : I ≤ Mp ⊔ C ⊔ I) hi, he⟩
  · rw [pCoreOf_map_conj, ← hcj]
    exact hcle

end CFSG.Quasithin.H13.Ch4
