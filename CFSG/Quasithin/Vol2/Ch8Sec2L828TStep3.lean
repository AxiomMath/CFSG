module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCore5
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TRho
public import CFSG.Quasithin.Vol2.Ch8Sec2L828SGL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open CFSG.Quasithin.H13.L828T
open scoped IsMulCommutative commutatorElement

section Step3

variable {G : Type} [Group G] [Finite G]

theorem s828_five_dprime (hMB2 : MB2_828) (hcard : Mathieu.StmtH13Card)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hrow : Case8_2 T L I) (c : S828Ctx T L I H h k) :
    ∀ x : G, x ^ 5 = 1 →
      x ∈ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) →
      x ∈ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) →
      (∀ y ∈ ch82I (fsuV T I) h, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (ch82I (fsuV T I) h)) →
      (∀ y ∈ ch82LU L (ch82U (fsuV T I) h),
        x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h))) →
      ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), x * p * x⁻¹ * p⁻¹ ∈ ch82U (fsuV T I) h := by
  intro x hx5 hxP hxU hI hLU
  refine s828_core5 hMB2 hcard hrow c hxP hxU ⟨1, by simpa using hx5⟩ ?_ ?_
  · intro w hw p hp
    exact c.hO2P _ (hLU w hw) p hp
  · intro w hw p hp
    exact c.hP2 _ (hI w hw) p hp

theorem s828_embed_gl2 {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) (K : Type) [Field K]
    (κ : ↥(commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
        ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
          Set (MulAut ↥(fsuV T I)))) ≃+* K) :
    ∃ f : E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) →*
        Matrix.GeneralLinearGroup (Fin 2) K, Function.Injective f := by
  classical
  set Ih := ch82I (fsuV T I) h with hIh
  set P := pCoreOf 2 Ih with hPdef
  have hIN2 := s828_I_norm_PU c
  obtain ⟨ρ, -, -, -, hker, -, hcomm⟩ := s828_rho c
  let ρI : ↥Ih →* AddMonoid.End (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) ×
      QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) :=
    ρ.comp (Subgroup.inclusion hIN2)
  have hρcomm : ∀ i : ↥Ih, ∀ γ ∈ indSet ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I))),
      ρI i * diagEnd γ = diagEnd γ * ρI i := fun i γ hγ =>
    hcomm (Subgroup.inclusion hIN2 i) i.2 γ hγ
  have hρker : ∀ i : ↥Ih, ρI i = 1 ↔ (i : G) ∈ P := by
    intro i
    show ρ (Subgroup.inclusion hIN2 i) = 1 ↔ _
    rw [hker]
    constructor
    · intro hh
      exact c.hfaith i i.2 hh
    · intro hi p hp
      exact c.hP2 _ hi p hp
  obtain ⟨f, hf⟩ := exists_hom_gl2
    (indSet ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I)))) K κ ρI hρcomm
  have hkerI : kerIn (fsuM T L ⊓ Ih) Ih = P := by
    obtain ⟨-, -, -, -, -, -, -, hkerI, -⟩ := id c.hC
    exact hkerI
  have hfP : ∀ i : ↥Ih, f i = 1 ↔ (i : G) ∈ P := fun i => (hf i).trans (hρker i)
  have hker2 : (kerIn (fsuM T L ⊓ Ih) Ih).subgroupOf Ih ≤ f.ker := by
    intro i hi
    rw [Subgroup.mem_subgroupOf, hkerI] at hi
    exact (hfP i).mpr hi
  refine ⟨QuotientGroup.lift _ f hker2, ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MonoidHom.mem_ker, QuotientGroup.lift_mk] at hq
  have hi : (i : G) ∈ P := (hfP i).mp hq
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hkerI]
  exact hi

theorem s828_dihedral_bound (hMB2 : MB2_828) (hcard : Mathieu.StmtH13Card)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) (m : ℕ) (hm : Odd m) (hm1 : 1 < m)
    (eI : E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
      DihedralGroup m) :
    (((∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M24Code T L I) → m = 3 ∨ m = 5) ∧
      (Row711M22Code T L I → m = 3) := by
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · obtain ⟨K, hKf, hKfin, hK4, ⟨κ⟩⟩ := s828_mb2_field4_G hMB2 hcard c hr
    obtain ⟨f, hf⟩ := s828_embed_gl2 c K κ
    exact CFSG.Quasithin.H13.L828SGL2.stmt_b K hK4 m hm hm1
      (f.comp eI.symm.toMonoidHom) (hf.comp eI.symm.injective)
  · obtain ⟨K, hKf, hKfin, hK2, ⟨κ⟩⟩ := s828_mb2_field2_G hMB2 hcard c hr
    obtain ⟨f, hf⟩ := s828_embed_gl2 c K κ
    exact CFSG.Quasithin.H13.L828SGL2.stmt_c K hK2 m hm hm1
      (f.comp eI.symm.toMonoidHom) (hf.comp eI.symm.injective)

theorem s828_clause3 (hMB2 : MB2_828) (hcard : Mathieu.StmtH13Card)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hrow : Case8_2 T L I) (c : S828Ctx T L I H h k) :
    (k = 1 ∧ Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
        DihedralGroup 3)) ∨
      IsPSL 2 2 k (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) ∨
      (((∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M24Code T L I) ∧ k = 1 ∧
        Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
          DihedralGroup 5)) := by
  have hk2 := s828_k_le_two hrow c.hC5
  obtain ⟨-, -, -, -, -, -, -, -, -, hdisj, -⟩ := id c.hC
  rcases hdisj with ⟨hk1, m, hmo, hm1, ⟨eI⟩⟩ | hP | hSz
  · have hb := s828_dihedral_bound hMB2 hcard c m hmo hm1 eI
    rcases hrow with ⟨n, hr⟩ | hr | hr | hr
    · rcases hb.1 (Or.inl ⟨n, hr⟩) with rfl | rfl
      · exact Or.inl ⟨hk1, ⟨eI⟩⟩
      · exact Or.inr (Or.inr ⟨Or.inl ⟨n, hr⟩, hk1, ⟨eI⟩⟩)
    · have := hb.2 hr
      subst this
      exact Or.inl ⟨hk1, ⟨eI⟩⟩
    · rcases hb.1 (Or.inr hr) with rfl | rfl
      · exact Or.inl ⟨hk1, ⟨eI⟩⟩
      · exact Or.inr (Or.inr ⟨Or.inr hr, hk1, ⟨eI⟩⟩)
    · exfalso
      have : (k : ℕ∞) = 2 := c.hC5.1.symm.trans (c.hC5.2.2.2.2.2.2.1 hr).1
      have : k = 2 := by exact_mod_cast this
      omega
  · exact Or.inr (Or.inl hP)
  · exfalso
    obtain ⟨-, a, ha, -, -, -, he, -⟩ := hSz
    omega

end Step3

end CFSG.Quasithin.H13
