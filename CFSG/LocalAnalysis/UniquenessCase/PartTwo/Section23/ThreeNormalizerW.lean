module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeCaseB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeNormalCoreTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

namespace Ctx23L

private theorem isSylowIn_T_inf_normalizer (c : Ctx23L D Ch) :
    IsSylowIn 2 D.T ((c.L0 ⊔ D.T) ⊓ Subgroup.normalizer (D.U : Set G)) := by
  have hSylH : IsSylowIn 2 D.T (c.L0 ⊔ D.T) := TwelveShort.isSylowIn_of_le D le_sup_right
  have hTN : D.T ≤ Subgroup.normalizer (D.U : Set G) := by
    rw [normalizer_eq_of_inCalV D (uc22p22e_inCalV_U D)]
    exact D.sylowM.le
  exact E6.isSylowIn_of_le hSylH (le_inf le_sup_right hTN) inf_le_left

private theorem conjSubgroup_le_of_le {H X : Subgroup G} (hXH : X ≤ H) {h : G} (hh : h ∈ H) :
    conjSubgroup X h ≤ H := by
  intro y hy
  rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hy
  rw [← show (h : G)⁻¹ * (h * y * h⁻¹) * h = y by group]
  exact H.mul_mem (H.mul_mem (H.inv_mem hh) (hXH hy)) hh

private theorem le_closure_iUnion_conj (H X : Subgroup G) :
    X ≤ Subgroup.closure (⋃ h : ↥H, (conjSubgroup X (h : G) : Set G)) := by
  intro x hx
  refine Subgroup.subset_closure ?_
  refine Set.mem_iUnion.mpr ⟨(1 : ↥H), ?_⟩
  change x ∈ conjSubgroup X (1 : G)
  rwa [CFSG.Quasithin.conjSubgroup_one]

private theorem closure_iUnion_conj_le {H M X : Subgroup G}
    (hconj : ∀ h ∈ H, conjSubgroup X h ≤ M) :
    Subgroup.closure (⋃ h : ↥H, (conjSubgroup X (h : G) : Set G)) ≤ M := by
  refine (Subgroup.closure_le M).mpr ?_
  intro y hy
  rw [Set.mem_iUnion] at hy
  obtain ⟨h, hy⟩ := hy
  exact hconj h h.2 hy

private theorem conjSubgroup_closure_eq (S : Set G) (h0 : G) :
    conjSubgroup (Subgroup.closure S) h0 =
      Subgroup.closure ((MulAut.conj (h0 : G)⁻¹).toMonoidHom '' S) := by
  change (Subgroup.closure S).map (MulAut.conj (h0 : G)⁻¹).toMonoidHom = _
  exact MonoidHom.map_closure _ S

private theorem conjSubgroup_closure_iUnion_le (H X : Subgroup G) {h0 : G} (hh0 : h0 ∈ H) :
    conjSubgroup (Subgroup.closure (⋃ h : ↥H, (conjSubgroup X (h : G) : Set G))) h0 ≤
      Subgroup.closure (⋃ h : ↥H, (conjSubgroup X (h : G) : Set G)) := by
  set S : Set G := ⋃ h : ↥H, (conjSubgroup X (h : G) : Set G) with hS
  rw [conjSubgroup_closure_eq S h0]
  refine (Subgroup.closure_le (Subgroup.closure S)).mpr ?_
  rintro z ⟨y, hyS, rfl⟩
  change (MulAut.conj (h0 : G)⁻¹) y ∈ Subgroup.closure S
  rw [MulAut.conj_apply]
  refine Subgroup.subset_closure ?_
  rw [hS, Set.mem_iUnion] at hyS ⊢
  obtain ⟨h, hy⟩ := hyS
  refine ⟨(h * ⟨h0, hh0⟩ : ↥H), ?_⟩
  refine (CFSG.Quasithin.mem_conjSubgroup_iff).mpr ?_
  have hy' : (h : G) * y * (h : G)⁻¹ ∈ X := by
    simpa using (CFSG.Quasithin.mem_conjSubgroup_iff.mp hy)
  have he : (((h * ⟨h0, hh0⟩ : ↥H)) : G) * (h0⁻¹ * y * (h0⁻¹)⁻¹) *
      (((h * ⟨h0, hh0⟩ : ↥H)) : G)⁻¹ = (h : G) * y * (h : G)⁻¹ := by
    push_cast
    group
  rw [he]
  exact hy'

private theorem le_conjSubgroup_closure_iUnion (H X : Subgroup G) {h0 : G} (hh0 : h0 ∈ H) :
    Subgroup.closure (⋃ h : ↥H, (conjSubgroup X (h : G) : Set G)) ≤
      conjSubgroup (Subgroup.closure (⋃ h : ↥H, (conjSubgroup X (h : G) : Set G))) h0 := by
  set S : Set G := ⋃ h : ↥H, (conjSubgroup X (h : G) : Set G) with hS
  rw [conjSubgroup_closure_eq S h0]
  refine (Subgroup.closure_le
    (Subgroup.closure ((MulAut.conj (h0 : G)⁻¹).toMonoidHom '' S))).mpr ?_
  intro y hyS
  refine Subgroup.subset_closure ?_
  refine ⟨(MulAut.conj (h0 : G)) y, ?_, ?_⟩
  · change (MulAut.conj (h0 : G)) y ∈ S
    rw [MulAut.conj_apply]
    rw [hS, Set.mem_iUnion] at hyS ⊢
    obtain ⟨h, hy⟩ := hyS
    refine ⟨(h * ⟨(h0 : G)⁻¹, H.inv_mem hh0⟩ : ↥H), ?_⟩
    refine (CFSG.Quasithin.mem_conjSubgroup_iff).mpr ?_
    have hy' : (h : G) * y * (h : G)⁻¹ ∈ X := by
      simpa using (CFSG.Quasithin.mem_conjSubgroup_iff.mp hy)
    have he : (((h * ⟨(h0 : G)⁻¹, H.inv_mem hh0⟩ : ↥H)) : G) * (h0 * y * h0⁻¹) *
        (((h * ⟨(h0 : G)⁻¹, H.inv_mem hh0⟩ : ↥H)) : G)⁻¹ =
        (h : G) * y * (h : G)⁻¹ := by
      push_cast
      group
    rw [he]
    exact hy'
  · change (MulAut.conj (h0 : G)⁻¹) ((MulAut.conj (h0 : G)) y) = y
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group

private theorem normalizer_closure_iUnion_conj (H X : Subgroup G) :
    H ≤ Subgroup.normalizer
      (Subgroup.closure (⋃ h : ↥H, (conjSubgroup X (h : G) : Set G)) : Set G) := by
  intro h0 hh0
  refine CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp ?_
  exact le_antisymm (conjSubgroup_closure_iUnion_le H X hh0)
    (le_conjSubgroup_closure_iUnion H X hh0)

private theorem twoElements_closure_iUnion_conj (H X : Subgroup G)
    (hX2 : ∀ x ∈ X, x ^ 2 = 1) :
    ∀ y ∈ ⋃ h : ↥H, (conjSubgroup X (h : G) : Set G), ∃ n : ℕ, y ^ (2 ^ n) = 1 := by
  intro y hy
  rw [Set.mem_iUnion] at hy
  obtain ⟨h, hy⟩ := hy
  have hyX : (h : G) * y * (h : G)⁻¹ ∈ X := by
    simpa using (CFSG.Quasithin.mem_conjSubgroup_iff.mp hy)
  have hsq : ((h : G) * y * (h : G)⁻¹) ^ 2 = 1 := by simpa using hX2 _ hyX
  have h1 : (MulAut.conj (h : G)) (y ^ 2) = 1 := by
    rw [map_pow, MulAut.conj_apply]
    exact hsq
  rw [MulAut.conj_apply] at h1
  have h2 := congrArg (fun z : G => (h : G)⁻¹ * z * (h : G)) h1
  refine ⟨1, ?_⟩
  simpa [mul_assoc] using h2

private theorem le_pCoreOf_of_forall_conj_le (c : Ctx23L D Ch)
    (h2010 : S20_10 D) (h207 : S20_7 D) (h1930 : H1930 D)
    {X : Subgroup G} (hXH : X ≤ c.L0 ⊔ D.T)
    (hconj : ∀ h ∈ c.L0 ⊔ D.T, conjSubgroup X h ≤ D.M)
    (hX2 : ∀ x ∈ X, x ^ 2 = 1) :
    X ≤ CFSG.Open.pCoreOf 2 (c.L0 ⊔ D.T) := by
  set H : Subgroup G := c.L0 ⊔ D.T with hH
  set S : Set G := ⋃ h : ↥H, (conjSubgroup X (h : G) : Set G) with hS
  set R : Subgroup G := Subgroup.closure S with hR
  have hXR : X ≤ R := by
    rw [hR]
    exact le_closure_iUnion_conj H X
  have hRH : R ≤ H := by
    rw [hR]
    exact closure_iUnion_conj_le fun h hh => conjSubgroup_le_of_le hXH hh
  have hRM : R ≤ D.M := by
    rw [hR]
    exact closure_iUnion_conj_le fun h hh => hconj h (by simpa [hH] using hh)
  have hRn : (R.subgroupOf H).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mpr ?_
    rw [hR]
    exact normalizer_closure_iUnion_conj H X
  have hgen : ∃ S' : Set G, (∀ x ∈ S', ∃ n : ℕ, x ^ (2 ^ n) = 1) ∧
      R = Subgroup.closure S' :=
    ⟨S, twoElements_closure_iUnion_conj H X hX2, hR⟩
  exact hXR.trans (le_pCore_of_normal c h2010 h207 h1930 hRH hRn hRM hgen)

private theorem lt_rk_of_mem_gammaSet {V A : Subgroup G} {g : G} {i k : ℕ}
    (hAg : A ≤ conjSubgroup V g) (hmq : E3.mQuot (conjSubgroup V g) A = i)
    (hi : k + i < rk ↥V) : k < rk ↥A := by
  have hbotA : E3.mQuot A ⊥ = rk ↥A := E3.mQuot_bot_eq_rk A
  have hbotV : E3.mQuot (conjSubgroup V g) ⊥ = rk ↥(conjSubgroup V g) :=
    E3.mQuot_bot_eq_rk _
  have hadd : E3.mQuot (conjSubgroup V g) ⊥ =
      E3.mQuot A ⊥ + E3.mQuot (conjSubgroup V g) A :=
    E3.mQuot_add (show (⊥ : Subgroup G) ≤ A from bot_le) hAg
  have hcard : rk ↥(conjSubgroup V g) = rk ↥V := by
    unfold rk
    rw [E3.card_conjSubgroup]
  rw [hbotA, hbotV, hmq, hcard] at hadd
  omega

private theorem gammaSet_le_pCoreOf (c : Ctx23L D Ch)
    (h2010 : S20_10 D) (h207 : S20_7 D) (h1930 : H1930 D)
    (hH0 : CFSG.LocalAnalysis.WeakClosure81.IsCalH0 D.U (c.L0 ⊔ D.T))
    {k : ℕ} (hW : IsElemAbelian 2 (W23_1 c))
    (ha : aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k) (i : ℕ)
    (hi : k + i < rk ↥D.U) :
    ∀ A ∈ E3.gammaSet D.U i D.T, A ≤ CFSG.Open.pCoreOf 2 (c.L0 ⊔ D.T) := by
  intro A hA
  obtain ⟨hAT, g, hAg, hmg⟩ := hA
  have hUel : IsElemAbelian 2 D.U :=
    (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).2
  let X : Subgroup G := conjSubgroup D.U g ⊓ (c.L0 ⊔ D.T)
  have hXel : IsElemAbelian 2 X :=
    CFSG.Quasithin.B2F.isElemAbelian_mono inf_le_left
      (E3.isElemAbelian_conjSubgroup hUel g)
  have hAX : A ≤ X := le_inf hAg (hAT.trans le_sup_right)
  have hkrkA : k < rk ↥A := lt_rk_of_mem_gammaSet hAg hmg hi
  have hXQ : X ≤ CFSG.Open.pCoreOf 2 (c.L0 ⊔ D.T) := by
    rcases CFSG.LocalAnalysis.WeakClosure81.eight_four_one (V := D.U) (H := c.L0 ⊔ D.T)
      (T := D.T) hUel c.hTI (U_ne_bot c) hH0 (isSylowIn_T_inf_normalizer c) g with
      ⟨-, hcase⟩ | ⟨hdisj, hfixb⟩
    · have hconj : ∀ h ∈ c.L0 ⊔ D.T, conjSubgroup X h ≤ D.M := by
        intro h hh
        have h1 := hcase h hh
        rwa [normalizer_eq_of_inCalV D (uc22p22e_inCalV_U D)] at h1
      exact le_pCoreOf_of_forall_conj_le c h2010 h207 h1930 inf_le_right hconj hXel.2
    · exfalso
      have hdisj' : X ⊓ Subgroup.centralizer (W23_1 c : Set G) = ⊥ := by
        simpa [eSub_U_eq_W23_1 c] using hdisj
      have hfix' : ∀ u ∈ X, u ≠ 1 →
          W23_1 c ⊓ Subgroup.centralizer (X : Set G) =
            W23_1 c ⊓ Subgroup.centralizer ({u} : Set G) := fun u hu hu1 => by
        rw [← eSub_U_eq_W23_1 c]
        exact hfixb u hu hu1
      have hbound : rk ↥X ≤ k :=
        (le_aBar_W23_1 c hW hXel inf_le_right hdisj' hfix').trans ha
      have hle : rk ↥A ≤ rk ↥X := rk_mono hAX
      omega
  exact hAX.trans hXQ

theorem L0T_le_normalizer_wClos (c : Ctx23L D Ch)
    (h2010 : S20_10 D) (h207 : S20_7 D) (h1930 : H1930 D)
    (hH0 : CFSG.LocalAnalysis.WeakClosure81.IsCalH0 D.U (c.L0 ⊔ D.T))
    {k : ℕ} (hW : IsElemAbelian 2 (W23_1 c))
    (ha : aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k) (i : ℕ) (hi : k + i < rk ↥D.U) :
    c.L0 ⊔ D.T ≤ Subgroup.normalizer (E3.wClos D.U i D.T : Set G) := by
  have hHn : c.L0 ⊔ D.T ≤ Subgroup.normalizer
      (CFSG.Open.pCoreOf 2 (c.L0 ⊔ D.T) : Set G) := fun h hh =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) (c.L0 ⊔ D.T) hh
  have hQT : CFSG.Open.pCoreOf 2 (c.L0 ⊔ D.T) ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (TwelveShort.isSylowIn_of_le D le_sup_right)
  rw [wClos_eq_of_gammaSet_le (V := D.U) (Q := CFSG.Open.pCoreOf 2 (c.L0 ⊔ D.T))
    (T := D.T) (i := i) (gammaSet_le_pCoreOf c h2010 h207 h1930 hH0 hW ha i hi) hQT]
  exact hHn.trans (E3.normalizer_le_normalizer_wClos (V := D.U) (i := i) _)

theorem L0T_le_normalizer_wClos_zero (c : Ctx23L D Ch)
    (h2010 : S20_10 D) (h207 : S20_7 D) (h1930 : H1930 D)
    (hH0 : CFSG.LocalAnalysis.WeakClosure81.IsCalH0 D.U (c.L0 ⊔ D.T))
    {k : ℕ} (hW : IsElemAbelian 2 (W23_1 c))
    (ha : aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k) (hk : k < rk ↥D.U) :
    c.L0 ⊔ D.T ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) :=
  L0T_le_normalizer_wClos c h2010 h207 h1930 hH0 hW ha 0 (by simpa using hk)

theorem L0T_le_normalizer_wClos_one (c : Ctx23L D Ch)
    (h2010 : S20_10 D) (h207 : S20_7 D) (h1930 : H1930 D)
    (hH0 : CFSG.LocalAnalysis.WeakClosure81.IsCalH0 D.U (c.L0 ⊔ D.T))
    {k : ℕ} (hW : IsElemAbelian 2 (W23_1 c))
    (ha : aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k) (hk : 2 * k ≤ rk ↥D.U) (hk2 : 2 ≤ k) :
    c.L0 ⊔ D.T ≤ Subgroup.normalizer (E3.wClos D.U 1 D.T : Set G) :=
  L0T_le_normalizer_wClos c h2010 h207 h1930 hH0 hW ha 1 (by omega)

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
