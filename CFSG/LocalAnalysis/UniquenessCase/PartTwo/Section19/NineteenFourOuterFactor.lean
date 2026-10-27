module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourP
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846Ker
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107OutOmega
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09n
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEightF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_pCoreOf_of_mem_inner {D : Data G} {X : Subgroup G}
    (hA5 : IsAlt (Bar2 X) 5) (hTX : D.T ≤ normalizer (X : Set G)) {a : G} (haT : a ∈ D.T)
    (haN : a ∈ normalizer (X : Set G))
    (hin : UC6S846.rhoL X ⟨a, haN⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X)) :
    a ∈ X ⊔ pCoreOf 2 (X ⊔ D.T) := by
  classical
  obtain ⟨fbar, hfbar⟩ := hin
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) fbar
  set x : G := a * (f : G)⁻¹ with hxdef
  have hxH : x ∈ X ⊔ D.T := by
    have h1 : a ∈ X ⊔ D.T := Subgroup.mem_sup_right haT
    have h2 : (f : G)⁻¹ ∈ X ⊔ D.T := Subgroup.mem_sup_left (X.inv_mem f.2)
    simpa [hxdef] using (X ⊔ D.T).mul_mem h1 h2
  have hxN : x ∈ normalizer (X : Set G) := by
    have h2 : (f : G)⁻¹ ∈ normalizer (X : Set G) :=
      Subgroup.inv_mem _ (Subgroup.le_normalizer f.2)
    simpa [hxdef] using Subgroup.mul_mem _ haN h2
  have hφ : UC6S846.rhoL X ⟨x, hxN⟩ = 1 := by
    have hsub : (⟨x, hxN⟩ : ↥(normalizer (X : Set G))) =
        ⟨a, haN⟩ * (⟨(f : G), Subgroup.le_normalizer f.2⟩)⁻¹ := by
      apply Subtype.ext
      simp [hxdef]
    have hstep : UC6S846.rhoL X (⟨a, haN⟩ *
        (⟨(f : G), Subgroup.le_normalizer f.2⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hfbar, UC6S846.rhoL_inner X (f : G) f.2]
      have hff : (QuotientGroup.mk (⟨(f : G), f.2⟩ : ↥X) : Bar2 X) = fbar := by
        rw [show (⟨(f : G), f.2⟩ : ↥X) = f from Subtype.ext rfl]
        exact hf
      rw [hff]
      exact mul_inv_cancel _
    rw [hsub]
    exact hstep
  have hxQ : x ∈ pCoreOf 2 (X ⊔ D.T) := UC6S846.mem_pCoreOf_sup_of_rhoL_eq_one
    D.sylowM.isPGroup hTX (fun y hy _ hρ => UC22.F09.mem_pCoreOf_of_rhoL_eq_one hA5 hy hρ)
    hxH hxN hφ
  have haeq : a = x * (f : G) := by simp [hxdef]
  rw [haeq]
  exact (X ⊔ pCoreOf 2 (X ⊔ D.T)).mul_mem (Subgroup.mem_sup_right hxQ)
    (Subgroup.mem_sup_left f.2)

theorem normal_right_of_normal_left_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (hLn : (L.subgroupOf D.M).Normal) :
    (K.subgroupOf D.M).Normal := by
  rcases dichotomy_19 h with ⟨-, x, hxM, hKx⟩ | ⟨-, -, hKn⟩
  · exfalso
    have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
    have hxN : x⁻¹ ∈ normalizer (L : Set G) :=
      Subgroup.inv_mem _ ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn hxM)
    have hLx : conjSubgroup L x = L := by
      have := Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
      exact this
    exact h.hne (hKx.trans hLx)
  · exact hKn

theorem mem_normalizer_right_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) {t : G} (htM : t ∈ D.M)
    (htL : t ∈ normalizer (L : Set G)) (hne : L ≠ K) :
    t ∈ normalizer (K : Set G) := by
  rcases permutesPair_of_ctx19_one h t htM with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
  · exfalso
    have hLmap : L.map (MulAut.conj t).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htL
    exact hne (hLmap.symm.trans h1)

theorem mem_pCoreOf_of_rhoL_sup_eq_one {D : Data G} {L K : Subgroup G}
    (hLc : L ∈ calC D.M) (hKc : K ∈ calC D.M) (hne : L ≠ K)
    (hA5L : IsAlt (Bar2 L) 5) (hA5K : IsAlt (Bar2 K) 5) {y : G} (hyJ : y ∈ L ⊔ K)
    (hyN : y ∈ normalizer ((L ⊔ K : Subgroup G) : Set G))
    (hρy : UC6S846.rhoL (L ⊔ K) ⟨y, hyN⟩ = 1) : y ∈ pCoreOf 2 (L ⊔ K) := by
  classical
  have hKL : K ≤ normalizer (L : Set G) := calC_le_normalizer_of_ne hLc hKc hne
  have hLK : L ≤ normalizer (K : Set G) := calC_le_normalizer_of_ne hKc hLc hne.symm
  have hJN : L ⊔ K ≤ normalizer (L : Set G) ⊓ normalizer (K : Set G) :=
    sup_le (le_inf Subgroup.le_normalizer hLK) (le_inf hKL Subgroup.le_normalizer)
  have hO2L : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ K) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_left
      (sup_le Subgroup.le_normalizer hKL)
  have hO2K : pCoreOf 2 K ≤ pCoreOf 2 (L ⊔ K) := by
    have h' := CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (X := K) (H := K ⊔ L)
      le_sup_left (sup_le Subgroup.le_normalizer hLK)
    simpa only [sup_comm] using h'
  have hsupO2L : pCoreOf 2 (L ⊔ K) ⊓ L ≤ pCoreOf 2 L := by
    have h' := CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (X := L) (H := L ⊔ K) le_sup_left
    rwa [inf_comm] at h'
  have hsupO2K : pCoreOf 2 (L ⊔ K) ⊓ K ≤ pCoreOf 2 K := by
    have h' := CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (X := K) (H := L ⊔ K) le_sup_right
    rwa [inf_comm] at h'
  have hactJ : ∀ z ∈ L ⊔ K, y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 (L ⊔ K) := by
    intro z hz
    exact (UC6S846.rhoL_fix_iff (L ⊔ K) ⟨y, hyN⟩ ⟨z, hz⟩).1 (by rw [hρy]; rfl)
  have hyNL : y ∈ normalizer (L : Set G) := hJN hyJ |>.1
  have hyNK : y ∈ normalizer (K : Set G) := hJN hyJ |>.2
  have hcommL : ∀ z ∈ L, y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 L := by
    intro z hz
    have h1 : y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 (L ⊔ K) := hactJ z ((le_sup_left : L ≤ L ⊔ K) hz)
    have h2 : y * z * y⁻¹ * z⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hyNL z).mp hz) (L.inv_mem hz)
    exact hsupO2L (Subgroup.mem_inf.mpr ⟨h1, h2⟩)
  have hcommK : ∀ z ∈ K, y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 K := by
    intro z hz
    have h1 : y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 (L ⊔ K) := hactJ z ((le_sup_right : K ≤ L ⊔ K) hz)
    have h2 : y * z * y⁻¹ * z⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp hyNK z).mp hz) (K.inv_mem hz)
    exact hsupO2K (Subgroup.mem_inf.mpr ⟨h1, h2⟩)
  have hρLy : UC6S846.rhoL L ⟨y, hyNL⟩ = 1 := by
    apply MulEquiv.ext
    intro zbar
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) zbar
    rw [MulAut.one_apply]
    exact (UC6S846.rhoL_fix_iff L ⟨y, hyNL⟩ z).2 (hcommL (z : G) z.2)
  have hρKy : UC6S846.rhoL K ⟨y, hyNK⟩ = 1 := by
    apply MulEquiv.ext
    intro zbar
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) zbar
    rw [MulAut.one_apply]
    exact (UC6S846.rhoL_fix_iff K ⟨y, hyNK⟩ z).2 (hcommK (z : G) z.2)
  have hyJ' : y ∈ (L : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L K hKL]
    exact hyJ
  obtain ⟨l, hl, k, hk, hlk⟩ := hyJ'
  have hlk' : y = l * k := hlk.symm
  have hρLl : UC6S846.rhoL L ⟨l, Subgroup.le_normalizer hl⟩ = 1 := by
    have hsub : (⟨y, hyNL⟩ : ↥(normalizer (L : Set G))) =
        ⟨l, Subgroup.le_normalizer hl⟩ * ⟨k, hKL hk⟩ := by
      apply Subtype.ext
      exact hlk'
    have h1 : UC6S846.rhoL L ⟨l, Subgroup.le_normalizer hl⟩ *
        UC6S846.rhoL L ⟨k, hKL hk⟩ = 1 := by
      rw [← map_mul, ← hsub]
      exact hρLy
    rw [UC22.R8107Out.rhoL_eq_one_of_mem hLc hKc hne hk (hKL hk)] at h1
    simpa using h1
  have hρKk : UC6S846.rhoL K ⟨k, Subgroup.le_normalizer hk⟩ = 1 := by
    have hsub : (⟨y, hyNK⟩ : ↥(normalizer (K : Set G))) =
        ⟨l, hLK hl⟩ * ⟨k, Subgroup.le_normalizer hk⟩ := by
      apply Subtype.ext
      exact hlk'
    have h1 : UC6S846.rhoL K ⟨l, hLK hl⟩ *
        UC6S846.rhoL K ⟨k, Subgroup.le_normalizer hk⟩ = 1 := by
      rw [← map_mul, ← hsub]
      exact hρKy
    rw [UC22.R8107Out.rhoL_eq_one_of_mem hKc hLc hne.symm hl (hLK hl)] at h1
    simpa using h1
  have hlO2 : l ∈ pCoreOf 2 L :=
    UC22.F09.mem_pCoreOf_of_rhoL_eq_one hA5L hl hρLl
  have hkO2 : k ∈ pCoreOf 2 K :=
    UC22.F09.mem_pCoreOf_of_rhoL_eq_one hA5K hk hρKk
  rw [hlk']
  exact (pCoreOf 2 (L ⊔ K)).mul_mem (hO2L hlO2) (hO2K hkO2)

theorem mem_sup_pCoreOf_of_mem_inner_pair {D : Data G} {L K : Subgroup G}
    (hLc : L ∈ calC D.M) (hKc : K ∈ calC D.M) (hne : L ≠ K)
    (hA5L : IsAlt (Bar2 L) 5) (hA5K : IsAlt (Bar2 K) 5)
    (hKL : K ≤ normalizer (L : Set G)) (hLK : L ≤ normalizer (K : Set G))
    (hTX : D.T ≤ normalizer ((L ⊔ K : Subgroup G) : Set G))
    {a : G} (haT : a ∈ D.T) (haL : a ∈ normalizer (L : Set G))
    (haK : a ∈ normalizer (K : Set G))
    (hinL : UC6S846.rhoL L ⟨a, haL⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))
    (hinK : UC6S846.rhoL K ⟨a, haK⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K)) :
    a ∈ (L ⊔ K) ⊔ pCoreOf 2 ((L ⊔ K) ⊔ D.T) := by
  classical
  obtain ⟨fLbar, hfLbar⟩ := hinL
  obtain ⟨fL, hfL⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) fLbar
  obtain ⟨fKbar, hfKbar⟩ := hinK
  obtain ⟨fK, hfK⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) fKbar
  set x : G := a * (fL * fK : G)⁻¹ with hxdef
  have hfLJ : (fL : G) ∈ L ⊔ K := (le_sup_left : L ≤ L ⊔ K) fL.2
  have hfKJ : (fK : G) ∈ L ⊔ K := (le_sup_right : K ≤ L ⊔ K) fK.2
  have hxH : x ∈ (L ⊔ K) ⊔ D.T := by
    have h1 : a ∈ (L ⊔ K) ⊔ D.T := Subgroup.mem_sup_right haT
    have h2 : (fL * fK : G)⁻¹ ∈ (L ⊔ K) ⊔ D.T :=
      Subgroup.mem_sup_left ((L ⊔ K).inv_mem ((L ⊔ K).mul_mem hfLJ hfKJ))
    simpa [hxdef] using ((L ⊔ K) ⊔ D.T).mul_mem h1 h2
  have hxL : x ∈ normalizer (L : Set G) := by
    have h2 : (fL * fK : G)⁻¹ ∈ normalizer (L : Set G) :=
      Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer fL.2) (hKL fK.2))
    simpa [hxdef] using Subgroup.mul_mem _ haL h2
  have hxK : x ∈ normalizer (K : Set G) := by
    have h2 : (fL * fK : G)⁻¹ ∈ normalizer (K : Set G) :=
      Subgroup.inv_mem _ (Subgroup.mul_mem _ (hLK fL.2) (Subgroup.le_normalizer fK.2))
    simpa [hxdef] using Subgroup.mul_mem _ haK h2
  have hxN : x ∈ normalizer ((L ⊔ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup L K ⟨hxL, hxK⟩
  have hρLx : UC6S846.rhoL L ⟨x, hxL⟩ = 1 := by
    have hsub : (⟨x, hxL⟩ : ↥(normalizer (L : Set G))) =
        ⟨a, haL⟩ * (⟨fL, Subgroup.le_normalizer fL.2⟩ * ⟨fK, hKL fK.2⟩)⁻¹ := by
      apply Subtype.ext
      simp [hxdef]
    have hstep : UC6S846.rhoL L (⟨a, haL⟩ *
        (⟨fL, Subgroup.le_normalizer fL.2⟩ * ⟨fK, hKL fK.2⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, ← hfLbar,
        UC6S846.rhoL_inner L (fL : G) fL.2,
        UC22.R8107Out.rhoL_eq_one_of_mem hLc hKc hne fK.2 (hKL fK.2)]
      have hff : (QuotientGroup.mk (⟨(fL : G), fL.2⟩ : ↥L) : Bar2 L) = fLbar := by
        rw [show (⟨(fL : G), fL.2⟩ : ↥L) = fL from Subtype.ext rfl]
        exact hfL
      rw [hff, mul_one, mul_inv_cancel]
    rw [hsub]
    exact hstep
  have hρKx : UC6S846.rhoL K ⟨x, hxK⟩ = 1 := by
    have hsub : (⟨x, hxK⟩ : ↥(normalizer (K : Set G))) =
        ⟨a, haK⟩ * (⟨fL, hLK fL.2⟩ * ⟨fK, Subgroup.le_normalizer fK.2⟩)⁻¹ := by
      apply Subtype.ext
      simp [hxdef]
    have hstep : UC6S846.rhoL K (⟨a, haK⟩ *
        (⟨fL, hLK fL.2⟩ * ⟨fK, Subgroup.le_normalizer fK.2⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, ← hfKbar,
        UC22.R8107Out.rhoL_eq_one_of_mem hKc hLc hne.symm fL.2 (hLK fL.2),
        UC6S846.rhoL_inner K (fK : G) fK.2]
      have hff : (QuotientGroup.mk (⟨(fK : G), fK.2⟩ : ↥K) : Bar2 K) = fKbar := by
        rw [show (⟨(fK : G), fK.2⟩ : ↥K) = fK from Subtype.ext rfl]
        exact hfK
      rw [hff, one_mul, mul_inv_cancel]
    rw [hsub]
    exact hstep
  have hcommL : ∀ z ∈ L, x * z * x⁻¹ * z⁻¹ ∈ pCoreOf 2 L := by
    intro z hz
    exact (UC6S846.rhoL_fix_iff L ⟨x, hxL⟩ ⟨z, hz⟩).1 (by rw [hρLx]; rfl)
  have hcommK : ∀ z ∈ K, x * z * x⁻¹ * z⁻¹ ∈ pCoreOf 2 K := by
    intro z hz
    exact (UC6S846.rhoL_fix_iff K ⟨x, hxK⟩ ⟨z, hz⟩).1 (by rw [hρKx]; rfl)
  have hO2L : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ K) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_left
      (sup_le Subgroup.le_normalizer hKL)
  have hO2K : pCoreOf 2 K ≤ pCoreOf 2 (L ⊔ K) := by
    have h' := CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (X := K) (H := K ⊔ L)
      le_sup_left (sup_le Subgroup.le_normalizer hLK)
    simpa only [sup_comm] using h'
  have hcommJ : ∀ z ∈ L ⊔ K, x * z * x⁻¹ * z⁻¹ ∈ pCoreOf 2 (L ⊔ K) := by
    intro z hz
    have hz' : z ∈ (L : Set G) * (K : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L K hKL]
      exact hz
    obtain ⟨l, hl, k, hk, rfl⟩ := hz'
    have h1 : x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (L ⊔ K) := hO2L (hcommL l hl)
    have h2 : l * (x * k * x⁻¹ * k⁻¹) * l⁻¹ ∈ pCoreOf 2 (L ⊔ K) := by
      have hxk : x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K := hcommK k hk
      have hlN : l ∈ normalizer (pCoreOf 2 K : Set G) :=
        (hLK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)) hl
      exact hO2K ((Subgroup.mem_normalizer_iff.mp hlN _).mp hxk)
    have hprod := (pCoreOf 2 (L ⊔ K)).mul_mem h1 h2
    convert hprod using 1
    group
  have hρx : UC6S846.rhoL (L ⊔ K) ⟨x, hxN⟩ = 1 := by
    apply MulEquiv.ext
    intro zbar
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(L ⊔ K)) zbar
    rw [MulAut.one_apply]
    exact (UC6S846.rhoL_fix_iff (L ⊔ K) ⟨x, hxN⟩ z).2 (hcommJ (z : G) z.2)
  have hxQ : x ∈ pCoreOf 2 ((L ⊔ K) ⊔ D.T) := UC6S846.mem_pCoreOf_sup_of_rhoL_eq_one
    D.sylowM.isPGroup hTX
    (fun y hy hyN hρ => mem_pCoreOf_of_rhoL_sup_eq_one hLc hKc hne hA5L hA5K hy hyN hρ)
    hxH hxN hρx
  have haeq : a = x * (fL * fK : G) := by
    rw [hxdef]
    group
  rw [haeq]
  refine ((L ⊔ K) ⊔ pCoreOf 2 ((L ⊔ K) ⊔ D.T)).mul_mem (Subgroup.mem_sup_right hxQ) ?_
  exact Subgroup.mem_sup_left ((L ⊔ K).mul_mem hfLJ hfKJ)

theorem outer_factor_19_4 {D : Data G} {V₀ V : Subgroup G}
    {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {A J : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hJ : JChoice19 D L K J)
    (hA5 : ¬ (J = L ∧ IsU3 (Bar2 L) 2))
    (hout : ¬ A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T))
    (hτ : E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (L : Set G)) :
    D.T ≤ normalizer (J : Set G) ∧
    ∃ (a : G), a ∈ A ∧ ∃ (F : Subgroup G), (F = L ∨ F = K) ∧ F ≤ J ∧ IsAlt (Bar2 F) 5 ∧
      E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (F : Set G) ∧
      pCoreOf 2 F ≤ pCoreOf 2 (J ⊔ D.T) ∧ A ≤ E1.tauOf (J ⊔ D.T) D.T A ∧
      ∃ (haN : a ∈ normalizer (F : Set G)),
        UC6S846.rhoL F ⟨a, haN⟩ ∉
          CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 F) := by
  classical
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hKc : K ∈ calC D.M := h.hK
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hLc.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le hKc.1
  have hne : L ≠ K := h.hne.symm
  obtain ⟨hAT, g, hAg, -⟩ := hA
  have hAelem : IsElemAbelian 2 A :=
    E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ g |>.mono hAg
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAelem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hTJ : D.T ≤ normalizer (J : Set G) := by
    rcases hJ with ⟨rfl | rfl, hLn⟩ | ⟨rfl, hLnn⟩
    · exact hTM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn)
    · exact hTM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp
        (normal_right_of_normal_left_19 h hLn))
    · intro t ht
      rcases permutesPair_of_ctx19_one h t (hTM ht) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
        calc (L ⊔ K).map (MulAut.conj t).toMonoidHom
            = L.map (MulAut.conj t).toMonoidHom ⊔ K.map (MulAut.conj t).toMonoidHom :=
              Subgroup.map_sup ..
          _ = L ⊔ K := by rw [h1, h2]
      · refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
        calc (L ⊔ K).map (MulAut.conj t).toMonoidHom
            = L.map (MulAut.conj t).toMonoidHom ⊔ K.map (MulAut.conj t).toMonoidHom :=
              Subgroup.map_sup ..
          _ = K ⊔ L := by rw [h1, h2]
          _ = L ⊔ K := sup_comm K L
  have hTH : D.T ≤ normalizer ((J ⊔ D.T : Subgroup G) : Set G) :=
    (le_inf hTJ Subgroup.le_normalizer).trans (Subgroup.inf_normalizer_le_normalizer_sup J D.T)
  have hTJQ : J ⊔ D.T ≤ normalizer (J : Set G) := sup_le Subgroup.le_normalizer hTJ
  have hQN : pCoreOf 2 (J ⊔ D.T) ≤ normalizer (J : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (J ⊔ D.T)).trans hTJQ
  have hQle : pCoreOf 2 (J ⊔ D.T) ≤ D.T :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowIn (TwelveShort.isSylowIn_of_le D le_sup_right)
  have hAQ : A ≤ normalizer (pCoreOf 2 (J ⊔ D.T) : Set G) :=
    (hAT.trans hTH).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (J ⊔ D.T))
  have hAτ : A ≤ E1.tauOf (J ⊔ D.T) D.T A := by
    intro x hx
    refine ⟨hAT hx, hAQ hx, ?_⟩
    intro y hy
    have hxy : x * y = y * x := hcomm x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by rw [hxy]; group
    rw [commutatorElement_def, h1]
    exact (pCoreOf 2 (J ⊔ D.T)).one_mem
  have houtJ : ∃ x ∈ A, x ∉ J ⊔ pCoreOf 2 (J ⊔ D.T) := by
    by_contra hc
    have hc' : ∀ x ∈ A, x ∈ J ⊔ pCoreOf 2 (J ⊔ D.T) := by
      intro x hx
      by_contra h
      exact hc ⟨x, hx, h⟩
    apply hout
    intro x hx
    have hxJQ : x ∈ J ⊔ pCoreOf 2 (J ⊔ D.T) := hc' x hx
    have hxT : x ∈ D.T := hAT hx
    have hxmul : x ∈ (J : Set G) * (pCoreOf 2 (J ⊔ D.T) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left J (pCoreOf 2 (J ⊔ D.T)) hQN]
      exact hxJQ
    obtain ⟨j, hj, q, hq, hjq⟩ := hxmul
    have hjT : j ∈ D.T := by
      have hjeq : j = x * q⁻¹ := by rw [← hjq]; group
      rw [hjeq]
      exact D.T.mul_mem hxT (D.T.inv_mem (hQle hq))
    have : j * q ∈ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T) :=
      Subgroup.mul_mem_sup ⟨hjT, hj⟩ hq
    exact hjq ▸ this
  obtain ⟨a, haA, haJQ⟩ := houtJ
  have haT : a ∈ D.T := hAT haA
  have hAL : A ≤ normalizer (L : Set G) := hAτ.trans hτ
  rcases hJ with ⟨hJL | hJK, hLn⟩ | ⟨hJsup, hLnn⟩
  ·
    have hU3 : ¬ IsU3 (Bar2 L) 2 := fun hU => hA5 ⟨hJL, hU⟩
    have hL2 : IsL2 (Bar2 L) 2 := h.shape.resolve_right hU3
    have hAlt : IsAlt (Bar2 L) 5 :=
      CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model (Bar2 L) hL2
    have hNL : D.T ≤ normalizer (L : Set G) :=
      hTM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn)
    have haN : a ∈ normalizer (L : Set G) := hτ (hAτ haA)
    have hcore : pCoreOf 2 L ≤ pCoreOf 2 (J ⊔ D.T) := by
      rw [hJL]
      exact CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (X := L) (H := L ⊔ D.T)
        le_sup_left (sup_le Subgroup.le_normalizer hNL)
    refine ⟨hTJ, a, haA, L, Or.inl rfl, hJL.symm.le, hAlt, hτ, hcore, hAτ, haN, fun hin => haJQ ?_⟩
    rw [hJL]
    exact mem_sup_pCoreOf_of_mem_inner hAlt hNL haT haN hin
  ·
    have hKn : (K.subgroupOf D.M).Normal := normal_right_of_normal_left_19 h hLn
    have hNK : D.T ≤ normalizer (K : Set G) :=
      hTM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn)
    have haN : a ∈ normalizer (K : Set G) := hNK haT
    have hAlt : IsAlt (Bar2 K) 5 := h.hKshape
    have hτK : E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (K : Set G) := by
      rw [hJK]
      exact (E1.tauOf_le (K ⊔ D.T) D.T A).trans hNK
    have hcore : pCoreOf 2 K ≤ pCoreOf 2 (J ⊔ D.T) := by
      rw [hJK]
      exact CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (X := K) (H := K ⊔ D.T)
        le_sup_left (sup_le Subgroup.le_normalizer hNK)
    refine ⟨hTJ, a, haA, K, Or.inr rfl, hJK.symm.le, hAlt, hτK, hcore, hAτ, haN, fun hin => haJQ ?_⟩
    rw [hJK]
    exact mem_sup_pCoreOf_of_mem_inner hAlt hNK haT haN hin
  ·
    have hKL : K ≤ normalizer (L : Set G) := calC_le_normalizer_of_ne hLc hKc hne
    have hLK : L ≤ normalizer (K : Set G) := calC_le_normalizer_of_ne hKc hLc hne.symm
    have hKx : ∃ x ∈ D.M, K = conjSubgroup L x := by
      rcases dichotomy_19 h with ⟨-, x, hxM, hKx⟩ | ⟨-, hLn', -⟩
      · exact ⟨x, hxM, hKx⟩
      · exact absurd hLn' hLnn
    obtain ⟨y, hyM, hKy⟩ := hKx
    have hAltL : IsAlt (Bar2 L) 5 := by
      have h1 : IsAlt (Bar2 (conjSubgroup L y)) 5 := hKy ▸ h.hKshape
      obtain ⟨e⟩ := UC22.uc22p20d_bar2_conj y⁻¹ L
      obtain ⟨e5⟩ := h1
      exact ⟨e.trans e5⟩
    have haNK : a ∈ normalizer (K : Set G) :=
      mem_normalizer_right_19 h (hTM haT) (hτ (hAτ haA)) hne
    have hTJ' : D.T ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := hJsup ▸ hTJ
    have hτK : E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (K : Set G) := by
      rw [hJsup]
      intro t ht
      have htT : t ∈ D.T := (E1.tauOf_le _ _ _) ht
      exact mem_normalizer_right_19 h (hTM htT) (hτ (hJsup ▸ ht)) hne
    have hτL : E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (L : Set G) := hτ
    by_cases hinL : UC6S846.rhoL L ⟨a, hτ (hAτ haA)⟩ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L)
    · by_cases hinK : UC6S846.rhoL K ⟨a, haNK⟩ ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K)
      · refine absurd ?_ haJQ
        rw [hJsup]
        exact mem_sup_pCoreOf_of_mem_inner_pair hLc hKc hne hAltL h.hKshape hKL hLK
          hTJ' haT (hτ (hAτ haA)) haNK hinL hinK
      · have hcore : pCoreOf 2 K ≤ pCoreOf 2 (J ⊔ D.T) := by
          rw [hJsup]
          refine (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (X := K) (H := L ⊔ K)
            le_sup_right (sup_le hLK Subgroup.le_normalizer)).trans ?_
          exact CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (X := L ⊔ K)
            (H := L ⊔ K ⊔ D.T) le_sup_left (sup_le Subgroup.le_normalizer hTJ')
        exact ⟨hTJ, a, haA, K, Or.inr rfl, (le_sup_right : K ≤ L ⊔ K).trans hJsup.symm.le,
          h.hKshape, hτK, hcore, hAτ, haNK, hinK⟩
    · have hcore : pCoreOf 2 L ≤ pCoreOf 2 (J ⊔ D.T) := by
        rw [hJsup]
        refine (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (X := L) (H := L ⊔ K)
          le_sup_left (sup_le Subgroup.le_normalizer hKL)).trans ?_
        exact CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (X := L ⊔ K)
          (H := L ⊔ K ⊔ D.T) le_sup_left (sup_le Subgroup.le_normalizer hTJ')
      exact ⟨hTJ, a, haA, L, Or.inl rfl, (le_sup_left : L ≤ L ⊔ K).trans hJsup.symm.le, hAltL,
        hτL, hcore, hAτ, hτ (hAτ haA), hinL⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
