module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourOrestLK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mQuot_ne_zero_19 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) {A J : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hJ : JChoice19 D L K J) (hJA : ¬ ⁅J, A⁆ ≤ pCoreOf 2 D.M) :
    E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) ≠ 0 := by
  classical
  intro hzero
  obtain ⟨hAT, -, -, -⟩ := hA
  have hA2 : IsPGroup 2 A := D.sylowM.isPGroup.to_le hAT
  have hAeq : A ⊓ pCoreOf 2 (J ⊔ D.T) = A :=
    (E3.mQuot_eq_zero_iff hA2 inf_le_left).mp hzero
  have hAQ : A ≤ pCoreOf 2 (J ⊔ D.T) := hAeq ▸ inf_le_right
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hJdata : J ≤ D.M ∧ (J.subgroupOf D.M).Normal := by
    rcases hJ with ⟨hJL | hJK, hLN⟩ | ⟨hJX, -⟩
    · subst hJL
      exact ⟨hLM, hLN⟩
    · subst hJK
      exact ⟨hKM, normal_right_of_normal_left_19 h hLN⟩
    · obtain rfl : J = S17.Lp D 5 := by rw [hJX, h.hLK]
      exact ⟨S17.Lp_le_M D 5, s13_Lp_normal D.M 5⟩
  have hO2J : pCoreOf 2 J ≤ pCoreOf 2 D.M :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hJdata.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hJdata.1).mp hJdata.2)
  have hJQ : J ⊓ pCoreOf 2 (J ⊔ D.T) ≤ pCoreOf 2 J :=
    CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 le_sup_left
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
    hAT.trans (D.sylowM.le.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hJdata.1).mp hJdata.2))
  have hJN : J ≤ Subgroup.normalizer (pCoreOf 2 (J ⊔ D.T) : Set G) :=
    (le_sup_left : J ≤ J ⊔ D.T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (J ⊔ D.T))
  have h1 : ⁅J, A⁆ ≤ J := CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hAJ
  have h2 : ⁅J, pCoreOf 2 (J ⊔ D.T)⁆ ≤ pCoreOf 2 (J ⊔ D.T) := by
    rw [Subgroup.commutator_comm]
    exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hJN
  have hcomm : ⁅J, A⁆ ≤ J ⊓ pCoreOf 2 (J ⊔ D.T) :=
    le_inf h1 ((Subgroup.commutator_mono le_rfl hAQ).trans h2)
  exact hJA ((hcomm.trans hJQ).trans hO2J)

theorem sup_ne_left_right_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) : L ⊔ K ≠ L ∧ L ⊔ K ≠ K := by
  classical
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hKc : K ∈ calC D.M := h.hK
  have hnot2 : ∀ X : Subgroup G, IsPGroup 2 X → ¬ 5 ∣ Nat.card (Bar2 X) := by
    intro X hX h5
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥X)).mp hX
    have hdvd : Nat.card (Bar2 X) ∣ Nat.card X := Subgroup.card_quotient_dvd_card _
    rw [hn] at hdvd
    exact absurd (Nat.prime_five.dvd_of_dvd_pow (h5.trans hdvd)) (by norm_num)
  have hKLcomm : ⁅K, L⁆ = ⁅L, K⁆ := Subgroup.commutator_comm K L
  constructor
  · intro heq
    have hKL : K ≤ L := heq ▸ le_sup_right
    have h1 : ⁅K, K⁆ ≤ pCoreOf 2 K := by
      have h2 : ⁅K, K⁆ ≤ ⁅K, L⁆ := Subgroup.commutator_mono le_rfl hKL
      rw [hKLcomm] at h2
      exact h2.trans ((calC_commutator_le_of_ne hLc hKc h.hne.symm).trans inf_le_right)
    rw [hKc.2.1] at h1
    exact hnot2 K ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le h1)
      (by rw [card_bar2_of_isAlt_five h.hKshape]; norm_num)
  · intro heq
    have hLK : L ≤ K := heq ▸ le_sup_left
    have h1 : ⁅L, L⁆ ≤ pCoreOf 2 L :=
      (Subgroup.commutator_mono le_rfl hLK).trans
        ((calC_commutator_le_of_ne hLc hKc h.hne.symm).trans inf_le_left)
    rw [hLc.2.1] at h1
    exact hnot2 L ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le h1)
      (prime_dvd_bar2 Nat.prime_five (by norm_num) (h.p_eq ▸ h.hyp.hL.2))

theorem commutator_le_pCoreOf_of_rhoL_eq_one_19 {X A : Subgroup G} (hXalt : IsAlt (Bar2 X) 5)
    (hXA : A ≤ Subgroup.normalizer (X : Set G))
    (htriv : ∀ a : ↥A, UC6S846.rhoL X (Subgroup.inclusion hXA a) = 1) :
    ⁅X, A⁆ ≤ pCoreOf 2 X := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have hxaX : ⁅x, a⁆ ∈ X := by
    have h1 : a * x⁻¹ * a⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hXA ha) x⁻¹).mp (X.inv_mem hx)
    simpa [commutatorElement_def, mul_assoc] using X.mul_mem hx h1
  refine UC22.F09.mem_pCoreOf_of_rhoL_eq_one hXalt hxaX ?_
  have h1 : (⟨⁅x, a⁆, Subgroup.le_normalizer hxaX⟩ : ↥(normalizer (X : Set G))) =
      (⟨x, Subgroup.le_normalizer hx⟩ : ↥(normalizer (X : Set G))) *
        (⟨a, hXA ha⟩ : ↥(normalizer (X : Set G))) *
        (⟨x, Subgroup.le_normalizer hx⟩ : ↥(normalizer (X : Set G)))⁻¹ *
        (⟨a, hXA ha⟩ : ↥(normalizer (X : Set G)))⁻¹ :=
    Subtype.ext (by simp [commutatorElement_def, mul_assoc])
  have htr : UC6S846.rhoL X (Subgroup.inclusion hXA ⟨a, ha⟩) = 1 := htriv ⟨a, ha⟩
  rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv]
  have htr' : UC6S846.rhoL X ⟨a, hXA ha⟩ = 1 := htr
  rw [htr']
  group

theorem exists_twoSided_19 {L K : Subgroup G} {A : Subgroup G}
    (hAL : A ≤ normalizer (L : Set G))
    (hAK : A ≤ normalizer (K : Set G)) (hLalt : IsAlt (Bar2 L) 5)
    (hKalt : IsAlt (Bar2 K) 5) (hLA : ¬ ⁅L, A⁆ ≤ pCoreOf 2 L)
    (hKA : ¬ ⁅K, A⁆ ≤ pCoreOf 2 K) :
    ∃ d : ↥A, UC6S846.rhoL L (Subgroup.inclusion hAL d) ≠ 1 ∧
      UC6S846.rhoL K (Subgroup.inclusion hAK d) ≠ 1 := by
  classical
  let fL : ↥A →* MulAut (Bar2 L) := (UC6S846.rhoL L).comp (Subgroup.inclusion hAL)
  let fK : ↥A →* MulAut (Bar2 K) := (UC6S846.rhoL K).comp (Subgroup.inclusion hAK)
  change ∃ d : ↥A, fL d ≠ 1 ∧ fK d ≠ 1
  by_contra hcon
  have hone : ∀ d : ↥A, fL d = 1 ∨ fK d = 1 := by
    intro d
    by_cases h1 : fL d = 1
    · exact Or.inl h1
    · exact Or.inr (by by_contra h2; exact hcon ⟨d, h1, h2⟩)
  have hexL : ∃ s : ↥A, fL s ≠ 1 := by
    by_contra h
    exact hLA (commutator_le_pCoreOf_of_rhoL_eq_one_19 hLalt hAL
      (fun a => by by_contra h1; exact h ⟨a, h1⟩))
  obtain ⟨s, hs⟩ := hexL
  have hexK : ∃ t : ↥A, fK t ≠ 1 := by
    by_contra h
    exact hKA (commutator_le_pCoreOf_of_rhoL_eq_one_19 hKalt hAK
      (fun a => by by_contra h1; exact h ⟨a, h1⟩))
  obtain ⟨t, ht⟩ := hexK
  have hKs : fK s = 1 := (hone s).resolve_left hs
  have hLt : fL t = 1 := (hone t).resolve_right ht
  have hst : fK (s * t) ≠ 1 := by
    rw [map_mul, hKs, one_mul]
    exact ht
  exact hcon ⟨s * t, by rw [map_mul, hLt, mul_one]; exact hs, hst⟩

theorem false_of_twoSided_mem_of_isAlt_19 {D : Data G}
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (hm : 4 < mSub V₀) {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hLalt : IsAlt (Bar2 L) 5)
    (hZ : A ⊓ centerOf (E3.wClos V₀ 2 (pCoreOf 2 (L ⊔ K ⊔ D.T))) ≠ ⊥)
    {d : G} (hd : d ∈ A) (hdNL : d ∈ normalizer (L : Set G))
    (hdNK : d ∈ normalizer (K : Set G))
    (hdL : UC6S846.rhoL L ⟨d, hdNL⟩ ≠ 1) (hdK : UC6S846.rhoL K ⟨d, hdNK⟩ ≠ 1) : False := by
  classical
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have hd2 : d ^ 2 = 1 := hAel.2 d hd
  have hAO : ¬ A ≤ pCoreOf 2 (L ⊔ K ⊔ D.T) := fun hle =>
    hdL (UC6S846.rhoL_eq_one_of_mem_pCoreOf (le_sup_left.trans le_sup_left) hdNL (hle hd))
  obtain ⟨e5L⟩ := hLalt
  obtain ⟨e5K⟩ := h.hKshape
  set eeL : MulAut (Bar2 L) ≃* Equiv.Perm (Fin 5) :=
    (MulAut.congr e5L).trans CFSG.Quasithin.L139A5.autA5.symm with heeL
  set eeK : MulAut (Bar2 K) ≃* Equiv.Perm (Fin 5) :=
    (MulAut.congr e5K).trans CFSG.Quasithin.L139A5.autA5.symm with heeK
  have hα2 : UC6S846.rhoL L ⟨d, hdNL⟩ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    have h1 : (⟨d, hdNL⟩ : ↥(normalizer (L : Set G))) * ⟨d, hdNL⟩ = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hd2
    rw [h1, map_one]
  have hβ2 : UC6S846.rhoL K ⟨d, hdNK⟩ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    have h1 : (⟨d, hdNK⟩ : ↥(normalizer (K : Set G))) * ⟨d, hdNK⟩ = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hd2
    rw [h1, map_one]
  have hαp2 : eeL (UC6S846.rhoL L ⟨d, hdNL⟩) ^ 2 = 1 := by
    rw [← map_pow, hα2, map_one]
  have hαp1 : eeL (UC6S846.rhoL L ⟨d, hdNL⟩) ≠ 1 := fun hh =>
    hdL (eeL.injective (by rw [hh, map_one]))
  have hβp2 : eeK (UC6S846.rhoL K ⟨d, hdNK⟩) ^ 2 = 1 := by
    rw [← map_pow, hβ2, map_one]
  have hβp1 : eeK (UC6S846.rhoL K ⟨d, hdNK⟩) ≠ 1 := fun hh =>
    hdK (eeK.injective (by rw [hh, map_one]))
  obtain ⟨xp, hxpalt, hxp3⟩ :=
    (perm5_invol_conj_orders (eeL (UC6S846.rhoL L ⟨d, hdNL⟩)) hαp2 hαp1).1
  obtain ⟨yp, hypalt, hyp2⟩ :=
    (perm5_invol_conj_orders (eeK (UC6S846.rhoL K ⟨d, hdNK⟩)) hβp2 hβp1).2
  obtain ⟨xL, hxL⟩ := exists_rhoL_eq_19 e5L ⟨xp, hxpalt⟩⁻¹
  obtain ⟨xK, hxK⟩ := exists_rhoL_eq_19 e5K ⟨yp, hypalt⟩⁻¹
  have hxL' : eeL (UC6S846.rhoL L ⟨(xL : G), Subgroup.le_normalizer xL.2⟩) = xp⁻¹ := hxL
  have hxK' : eeK (UC6S846.rhoL K ⟨(xK : G), Subgroup.le_normalizer xK.2⟩) = yp⁻¹ := hxK
  have hKN : K ≤ normalizer (L : Set G) := calC_le_normalizer_of_ne h.hyp.hL.1 h.hK h.hne.symm
  have hLN : L ≤ normalizer (K : Set G) := calC_le_normalizer_of_ne h.hK h.hyp.hL.1 h.hne
  set x : G := (xL : G) * (xK : G) with hxdef
  have hxNL : x ∈ normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer xL.2) (hKN xK.2)
  have hxNK : x ∈ normalizer (K : Set G) :=
    Subgroup.mul_mem _ (hLN xL.2) (Subgroup.le_normalizer xK.2)
  have hxH : x ∈ L ⊔ K ⊔ D.T := by
    rw [hxdef]
    exact Subgroup.mem_sup_left ((L ⊔ K).mul_mem (Subgroup.mem_sup_left xL.2)
      (Subgroup.mem_sup_right xK.2))
  set e : G := x⁻¹ * d * x with hedef
  have heA : e ∈ conjSubgroup A x := by
    rw [mem_conjSubgroup_iff]
    show x * (x⁻¹ * d * x) * x⁻¹ ∈ A
    rw [show x * (x⁻¹ * d * x) * x⁻¹ = d by group]
    exact hd
  have heNL : e ∈ normalizer (L : Set G) := by
    rw [hedef]
    exact (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).inv_mem hxNL) hdNL) hxNL
  have heNK : e ∈ normalizer (K : Set G) := by
    rw [hedef]
    exact (normalizer (K : Set G)).mul_mem ((normalizer (K : Set G)).mul_mem
      ((normalizer (K : Set G)).inv_mem hxNK) hdNK) hxNK
  have hdeNL : d * e ∈ normalizer (L : Set G) := (normalizer (L : Set G)).mul_mem hdNL heNL
  have hdeNK : d * e ∈ normalizer (K : Set G) := (normalizer (K : Set G)).mul_mem hdNK heNK
  have hρLx : UC6S846.rhoL L (⟨x, hxNL⟩ : ↥(normalizer (L : Set G))) =
      UC6S846.rhoL L (⟨(xL : G), Subgroup.le_normalizer xL.2⟩ :
        ↥(normalizer (L : Set G))) := by
    have hxsplit : (⟨x, hxNL⟩ : ↥(normalizer (L : Set G))) =
        (⟨(xL : G), Subgroup.le_normalizer xL.2⟩ : ↥(normalizer (L : Set G))) *
          (⟨(xK : G), hKN xK.2⟩ : ↥(normalizer (L : Set G))) :=
      Subtype.ext (by simp [hxdef])
    rw [hxsplit, map_mul,
      UC22.R8107Out.rhoL_eq_one_of_mem h.hyp.hL.1 h.hK h.hne.symm xK.2 (hKN xK.2), mul_one]
  have hρKx : UC6S846.rhoL K (⟨x, hxNK⟩ : ↥(normalizer (K : Set G))) =
      UC6S846.rhoL K (⟨(xK : G), Subgroup.le_normalizer xK.2⟩ :
        ↥(normalizer (K : Set G))) := by
    have hxsplit : (⟨x, hxNK⟩ : ↥(normalizer (K : Set G))) =
        (⟨(xL : G), hLN xL.2⟩ : ↥(normalizer (K : Set G))) *
          (⟨(xK : G), Subgroup.le_normalizer xK.2⟩ : ↥(normalizer (K : Set G))) :=
      Subtype.ext (by simp [hxdef])
    rw [hxsplit, map_mul,
      UC22.R8107Out.rhoL_eq_one_of_mem h.hK h.hyp.hL.1 h.hne xL.2 (hLN xL.2), one_mul]
  have hdeL : (⟨d * e, hdeNL⟩ : ↥(normalizer (L : Set G))) =
      (⟨d, hdNL⟩ : ↥(normalizer (L : Set G))) *
        ((⟨x, hxNL⟩ : ↥(normalizer (L : Set G)))⁻¹ *
          (⟨d, hdNL⟩ : ↥(normalizer (L : Set G))) * ⟨x, hxNL⟩) :=
    Subtype.ext (by simp [hedef, mul_assoc])
  have hdeK : (⟨d * e, hdeNK⟩ : ↥(normalizer (K : Set G))) =
      (⟨d, hdNK⟩ : ↥(normalizer (K : Set G))) *
        ((⟨x, hxNK⟩ : ↥(normalizer (K : Set G)))⁻¹ *
          (⟨d, hdNK⟩ : ↥(normalizer (K : Set G))) * ⟨x, hxNK⟩) :=
    Subtype.ext (by simp [hedef, mul_assoc])
  have horde3 : orderOf (eeL (UC6S846.rhoL L ⟨d * e, hdeNL⟩)) = 3 := by
    have h1 : eeL (UC6S846.rhoL L ⟨d * e, hdeNL⟩) =
        eeL (UC6S846.rhoL L ⟨d, hdNL⟩) *
          ((eeL (UC6S846.rhoL L ⟨(xL : G), Subgroup.le_normalizer xL.2⟩))⁻¹ *
            eeL (UC6S846.rhoL L ⟨d, hdNL⟩) *
            eeL (UC6S846.rhoL L ⟨(xL : G), Subgroup.le_normalizer xL.2⟩)) := by
      rw [hdeL]
      simp only [map_mul, map_inv, hρLx]
    rw [h1, hxL', inv_inv]
    exact hxp3
  have horde2 : orderOf (eeK (UC6S846.rhoL K ⟨d * e, hdeNK⟩)) = 2 := by
    have h1 : eeK (UC6S846.rhoL K ⟨d * e, hdeNK⟩) =
        eeK (UC6S846.rhoL K ⟨d, hdNK⟩) *
          ((eeK (UC6S846.rhoL K ⟨(xK : G), Subgroup.le_normalizer xK.2⟩))⁻¹ *
            eeK (UC6S846.rhoL K ⟨d, hdNK⟩) *
            eeK (UC6S846.rhoL K ⟨(xK : G), Subgroup.le_normalizer xK.2⟩)) := by
      rw [hdeK]
      simp only [map_mul, map_inv, hρKx]
    rw [h1, hxK', inv_inv]
    exact hyp2
  have h3dvd : 3 ∣ orderOf (d * e) := by
    have h1 : orderOf (UC6S846.rhoL L ⟨d * e, hdeNL⟩) = 3 :=
      (MulEquiv.orderOf_eq eeL (UC6S846.rhoL L ⟨d * e, hdeNL⟩)).symm.trans horde3
    have h2 : orderOf (UC6S846.rhoL L ⟨d * e, hdeNL⟩) ∣
        orderOf (⟨d * e, hdeNL⟩ : ↥(normalizer (L : Set G))) :=
      orderOf_map_dvd (UC6S846.rhoL L) _
    rw [← Subgroup.orderOf_coe (⟨d * e, hdeNL⟩ : ↥(normalizer (L : Set G))), h1] at h2
    exact h2
  have h2dvd : 2 ∣ orderOf (d * e) := by
    have h1 : orderOf (UC6S846.rhoL K ⟨d * e, hdeNK⟩) = 2 :=
      (MulEquiv.orderOf_eq eeK (UC6S846.rhoL K ⟨d * e, hdeNK⟩)).symm.trans horde2
    have h2 : orderOf (UC6S846.rhoL K ⟨d * e, hdeNK⟩) ∣
        orderOf (⟨d * e, hdeNK⟩ : ↥(normalizer (K : Set G))) :=
      orderOf_map_dvd (UC6S846.rhoL K) _
    rw [← Subgroup.orderOf_coe (⟨d * e, hdeNK⟩ : ↥(normalizer (K : Set G))), h1] at h2
    exact h2
  exact false_of_two_three_dvd_orderOf_19 (H := L ⊔ K ⊔ D.T)
    (Q := pCoreOf 2 (L ⊔ K ⊔ D.T)) (A := A) h.hyp.hyp125 hm
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ K ⊔ D.T)) hAgamma hAO hZ hxH hd heA
    h2dvd h3dvd

theorem false_of_twoSided_mem_19 {D : Data G}
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (hm : 4 < mSub V₀) {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hLn : ¬ (L.subgroupOf D.M).Normal)
    (hZ : A ⊓ centerOf (E3.wClos V₀ 2 (pCoreOf 2 (L ⊔ K ⊔ D.T))) ≠ ⊥)
    {d : G} (hd : d ∈ A) (hdNL : d ∈ normalizer (L : Set G))
    (hdNK : d ∈ normalizer (K : Set G))
    (hdL : UC6S846.rhoL L ⟨d, hdNL⟩ ≠ 1) (hdK : UC6S846.rhoL K ⟨d, hdNK⟩ ≠ 1) : False :=
  false_of_twoSided_mem_of_isAlt_19 h hm hA (isAlt_bar2_left_19 h hLn) hZ hd hdNL hdNK hdL hdK

theorem false_of_twoSided_19 {D : Data G} {V₀ V : Subgroup G}
    {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLn : ¬ (L.subgroupOf D.M).Normal)
    (hAL : A ≤ normalizer (L : Set G)) (hAK : A ≤ normalizer (K : Set G))
    (hZ : A ⊓ centerOf (E3.wClos V₀ 2 (pCoreOf 2 (L ⊔ K ⊔ D.T))) ≠ ⊥)
    (d : G) (hd : d ∈ A) (hdL : UC6S846.rhoL L ⟨d, hAL hd⟩ ≠ 1)
    (hdK : UC6S846.rhoL K ⟨d, hAK hd⟩ ≠ 1) : False :=
  false_of_twoSided_mem_19 h hm hA hLn hZ hd (hAL hd) (hAK hd) hdL hdK

theorem pin_one_twoSided_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLn : ¬ (L.subgroupOf D.M).Normal)
    (hq : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) = 1)
    (hAL : A ≤ normalizer (L : Set G)) (hLA : ¬ ⁅L, A⁆ ≤ pCoreOf 2 L)
    (hKA : ¬ ⁅K, A⁆ ≤ pCoreOf 2 K) : False := by
  classical
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hAK : A ≤ normalizer (K : Set G) := fun a ha =>
    mem_normalizer_right_19 h (hAM ha) (hAL ha) h.hne.symm
  have hLalt : IsAlt (Bar2 L) 5 := isAlt_bar2_left_19 h hLn
  have h5sig : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5sig
  let X : Subgroup G := L ⊔ K ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 X
  have hXle : X ≤ D.M := sup_le (sup_le hLM hKM) D.sylowM.le
  have hQH : Q ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hHQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hTsyl : IsSylowIn 2 D.T X := TwelveShort.isSylowIn_of_le D le_sup_right
  have hQT : Q ≤ D.T := CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow le_sup_right
    D.sylowM.isPGroup hTsyl.2.2
  have hAH : A ≤ X := fun a ha => Subgroup.mem_sup_right (hAT ha)
  have hC2 : E3.cClos V₀ 2 D.T ≤ X :=
    fun x hx => Subgroup.mem_sup_right (Subgroup.mem_inf.mp hx).1
  have hAMO : ¬ A ≤ pCoreOf 2 D.M := by
    intro hle
    apply hLA
    have h1 : ⁅L, A⁆ ≤ L := CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hAL
    have h2 : ⁅L, pCoreOf 2 D.M⁆ ≤ pCoreOf 2 D.M := by
      rw [Subgroup.commutator_comm]
      exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer
        (hLM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
    exact (le_inf h1 ((Subgroup.commutator_mono le_rfl hle).trans h2)).trans
      (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLM)
  have hAQ : ¬ A ≤ Q := by
    intro hle
    apply hLA
    have hLX : L ≤ X := le_sup_left.trans le_sup_left
    have h1 : ⁅L, A⁆ ≤ L := CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hAL
    have h2 : ⁅L, Q⁆ ≤ Q := by
      rw [Subgroup.commutator_comm]
      exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer
        (hLX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
    exact (le_inf h1 ((Subgroup.commutator_mono le_rfl hle).trans h2)).trans
      (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLX)
  have hP5 : ∀ N : Subgroup G, N ≤ X → X ≤ Subgroup.normalizer (N : Set G) →
      ¬ N ≤ Q → 5 ∣ Nat.card N := by
    intro N hNX hXN hNQ
    have h5L : 5 ∣ Nat.card L := (h.p_eq ▸ h.hyp.hL.2 : 5 ∈ piSet L).2
    have hLKle : L ⊔ K ≤ N := sup_le_of_normal_LKT_19 h hLn hNX hXN hNQ
    exact h5L.trans (Subgroup.card_dvd_of_le (le_sup_left.trans hLKle))
  have hqle : E3.mQuot A (A ⊓ Q) ≤ 2 := by rw [show E3.mQuot A (A ⊓ Q) = 1 from hq]; norm_num
  have hZ : A ⊓ centerOf (E3.wClos V₀ 2 Q) ≠ ⊥ :=
    inf_centerOf_wClos_two_ne_bot_19 h.hyp.hyp125 hm hsp hN2 hXle hQH hHQ hQT hAH hAgamma
      hAMO hAQ hqle hC2 hP5
  obtain ⟨d, hdL, hdK⟩ := exists_twoSided_19 hAL hAK hLalt h.hKshape hLA hKA
  exact false_of_twoSided_19 h hm hAgamma hLn hAL hAK hZ (d : G) d.2 hdL hdK

theorem sup_inf_normalizer_eq_19 {D : Data G} {J : Subgroup G} (hJM : J ≤ D.M)
    (hJn : (J.subgroupOf D.M).Normal) :
    J ⊔ (D.T ⊓ normalizer (J : Set G)) = J ⊔ D.T := by
  have hTN : D.T ≤ Subgroup.normalizer (J : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJM).mp hJn)
  rw [inf_eq_left.mpr hTN]

theorem pin_two_of_isAlt_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A J : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hJ : (J = L ∨ J = K) ∧ (L.subgroupOf D.M).Normal)
    (hJalt : IsAlt (Bar2 J) 5) (hJA : ¬ ⁅J, A⁆ ≤ pCoreOf 2 D.M)
    (hq : E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) = 2) :
    ∃ g : G, InCalO 2 D.M ⊥ V₀ g ∧ ¬ InCalO 1 D.M ⊥ V₀ g := by
  classical
  have hAMem : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hJM : J ≤ D.M := by
    rcases hJ.1 with rfl | rfl
    · exact hLM
    · exact hKM
  have hJn : (J.subgroupOf D.M).Normal := by
    rcases hJ.1 with rfl | rfl
    · exact hJ.2
    · exact normal_right_of_normal_left_19 h hJ.2
  have hTN : D.T ≤ Subgroup.normalizer (J : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJM).mp hJn)
  have hAM : ¬ A ≤ pCoreOf 2 D.M := by
    intro hle
    apply hJA
    have hJN : J ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
      hJM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
    have hcalc : ⁅J, pCoreOf 2 D.M⁆ ≤ pCoreOf 2 D.M := by
      rw [Subgroup.commutator_comm]
      exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hJN
    exact (Subgroup.commutator_mono le_rfl hle).trans hcalc
  have hAF : A ≤ Subgroup.normalizer (J : Set G) := hAT.trans hTN
  have hCF : E3.cClos V₀ 2 D.T ≤ Subgroup.normalizer (J : Set G) :=
    (show E3.cClos V₀ 2 D.T ≤ D.T from fun x hx => (Subgroup.mem_inf.mp hx).1).trans hTN
  have hqF : E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ (D.T ⊓ normalizer (J : Set G)))) = 2 := by
    rw [sup_inf_normalizer_eq_19 hJM hJn]
    exact hq
  exact exists_inCalO_of_proj_two_19 D hSg h hm hN2 hAMem hAM hJ.1 hJalt hAF hCF hqF

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
