module

public import CFSG.RankThree.GF2n.Stroth80.QuadIso
public import CFSG.RankThree.GF2n.Stroth80.QuadWitt
public import CFSG.ClassicalGroups.StrothPlaneLemmas

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem no_plane_partition_sub {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (U : Submodule K E) (hU : Module.finrank K U = 3)
    (ℓ : E → Submodule K E) (hle : ∀ x ∈ U, x ≠ 0 → ℓ x ≤ U)
    (hdim : ∀ x ∈ U, x ≠ 0 → Module.finrank K (ℓ x) = 2)
    (hmem : ∀ x ∈ U, x ≠ 0 → x ∈ ℓ x)
    (heq : ∀ x ∈ U, x ≠ 0 → ∀ z ∈ ℓ x, z ≠ 0 → ℓ z = ℓ x) : False := by
  have hUb : U ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hU
    omega
  obtain ⟨x, hxU, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUb
  obtain ⟨y, hyU, hy⟩ : ∃ y ∈ U, y ∉ ℓ x := by
    by_contra! h
    have hUle : U ≤ ℓ x := by
      intro z hz
      exact h z hz
    have h2 : Module.finrank K (ℓ x) = 2 := hdim x hxU hx
    have h3 : Module.finrank K U ≤ Module.finrank K (ℓ x) := Submodule.finrank_mono hUle
    omega
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (ℓ x).zero_mem
  have hxU' : ℓ x ≤ U := hle x hxU hx
  have hyU' : ℓ y ≤ U := hle y hyU hy0
  have hsup : ℓ x ⊔ ℓ y ≤ U := sup_le hxU' hyU'
  have hle3 : Module.finrank K ↥(ℓ x ⊔ ℓ y) ≤ Module.finrank K U := Submodule.finrank_mono hsup
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (ℓ x) (ℓ y)
  rw [hdim x hxU hx, hdim y hyU hy0] at hsum
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := ℓ x ⊓ ℓ y) (by
    intro h
    rw [h, finrank_bot] at hsum
    omega)
  have h1 : ℓ w = ℓ x := heq x hxU hx w (Submodule.mem_inf.mp hw).1 hw0
  have h2 : ℓ w = ℓ y := heq y hyU hy0 w (Submodule.mem_inf.mp hw).2 hw0
  have hyx : ℓ y = ℓ x := h2.symm.trans h1
  apply hy
  rw [← hyx]
  exact hmem y hyU hy0

open CFSG.RankThree.GF2n

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

structure RootGeom (M₀ : Tim79.QuadModel QF V K γ) where
  R : Set M₀.E
  D : M₀.E → Submodule K M₀.E
  Λ : M₀.E → Set (M₀.E →ₗ[K] M₀.E)
  R_ne : ∀ x ∈ R, x ≠ 0
  R_smul : ∀ x ∈ R, ∀ c : K, c ≠ 0 → c • x ∈ R
  R_sing : ∀ x ∈ R, M₀.Qf x = 0
  R_span : Submodule.span K R = ⊤
  D_sing : ∀ x ∈ R, ∀ d ∈ D x, M₀.Qf d = 0
  mem_D : ∀ x ∈ R, x ∈ D x
  D_smul : ∀ x ∈ R, ∀ c : K, c ≠ 0 → D (c • x) = D x
  D_symm : ∀ x ∈ R, ∀ y ∈ R, M₀.B x y = 0 → y ∈ D x → x ∈ D y
  far_exists : ∀ x ∈ R, ∃ y ∈ R, M₀.B x y = 0 ∧ y ∉ D x
  near_line : ∀ x ∈ R, ∀ y ∈ R, M₀.B x y = 0 → y ∈ D x → ∀ κ : K, y + κ • x ≠ 0 →
    y + κ • x ∈ R
  far_line : ∀ x ∈ R, ∀ y ∈ R, M₀.B x y = 0 → y ∉ D x → ∀ κ : K, y + κ • x ∈ R
  eich : ∀ x ∈ R, ∃ f : Module.Dual K M₀.E, f x = 0 ∧
    ∀ y ∈ R, M₀.B x y = 0 → f y = 0 → y ∈ D x
  Λ_fix : ∀ x ∈ R, ∀ r ∈ Λ x, r x = x
  Λ_iso : ∀ x ∈ R, ∀ r ∈ Λ x, ∀ e, M₀.Qf (r e) = M₀.Qf e
  Λ_R : ∀ x ∈ R, ∀ r ∈ Λ x, ∀ y ∈ R, r y ∈ R
  Λ_D : ∀ x ∈ R, ∀ r ∈ Λ x, ∀ y, M₀.B x y = 0 → r y - y ∈ D x
  Fdim : ∀ x ∈ R, ∃ f : M₀.E, ∀ y, M₀.B x y = 0 →
    (∀ r ∈ Λ x, r y - y ∈ Submodule.span K {x}) → y ∈ D x ⊔ Submodule.span K {f}

namespace RootGeom

variable {M₀ : Tim79.QuadModel QF V K γ} (P : RootGeom M₀)

theorem plane_mem {x y : M₀.E} (hx : x ∈ P.R) (hy : y ∈ P.R) (hxy : M₀.B x y = 0) (α β : K)
    (hne : α • x + β • y ≠ 0) : α • x + β • y ∈ P.R := by
  by_cases hβ : β = 0
  · subst hβ
    have hα : α ≠ 0 := by
      rintro rfl
      exact hne (by simp)
    simpa using P.R_smul x hx α hα
  · have e : α • x + β • y = β • (y + (α / β) • x) := by
      rw [smul_add, smul_smul, mul_div_cancel₀ _ hβ, add_comm]
    have hne' : y + (α / β) • x ≠ 0 := by
      intro h0
      apply hne
      rw [e, h0, smul_zero]
    rw [e]
    refine P.R_smul _ ?_ β hβ
    by_cases hyD : y ∈ P.D x
    · exact P.near_line x hx y hy hxy hyD _ hne'
    · exact P.far_line x hx y hy hxy hyD _

open scoped _root_.Classical in
@[expose] noncomputable def Nsub (x : M₀.E) : Submodule K M₀.E :=
  if hx : x ∈ P.R then
    { carrier := {y | y ∈ P.D x ∧ (y = 0 ∨ y ∈ P.R)}
      add_mem' := by
        rintro a b ⟨haD, haR⟩ ⟨hbD, hbR⟩
        refine ⟨(P.D x).add_mem haD hbD, ?_⟩
        rcases haR with rfl | haR
        · simpa using hbR
        rcases hbR with rfl | hbR
        · simpa using Or.inr haR
        by_cases hab : a + b = 0
        · exact Or.inl hab
        · refine Or.inr ?_
          have hB : M₀.B a b = 0 := by
            have h := M₀.Qf_add a b
            rw [P.D_sing x hx _ ((P.D x).add_mem haD hbD), P.D_sing x hx a haD,
              P.D_sing x hx b hbD] at h
            simpa using h.symm
          simpa using P.plane_mem haR hbR hB 1 1 (by simpa using hab)
      zero_mem' := ⟨(P.D x).zero_mem, Or.inl rfl⟩
      smul_mem' := by
        rintro c a ⟨haD, haR⟩
        refine ⟨(P.D x).smul_mem c haD, ?_⟩
        rcases haR with rfl | haR
        · exact Or.inl (smul_zero c)
        · by_cases hc : c = 0
          · exact Or.inl (by rw [hc, zero_smul])
          · exact Or.inr (P.R_smul a haR c hc) }
  else ⊥

theorem mem_Nsub {x : M₀.E} (hx : x ∈ P.R) {y : M₀.E} :
    y ∈ P.Nsub x ↔ y ∈ P.D x ∧ (y = 0 ∨ y ∈ P.R) := by
  simp only [Nsub, hx, dite_true]
  exact Iff.rfl

theorem far_hom {x y : M₀.E} (hx : x ∈ P.R) (hy : y ∈ P.R) (hxy : M₀.B x y = 0)
    (hyD : y ∉ P.D x) (a b a' b' : K) (hdet : a * b' - b * a' ≠ 0)
    (hu : a • x + b • y ∈ P.R) (hw : a' • x + b' • y ∈ P.R) :
    a' • x + b' • y ∉ P.D (a • x + b • y) := by
  intro hw'
  have huD : a • x + b • y ∈ P.D (a • x + b • y) := P.mem_D _ hu
  have hdx : (a * b' - b * a') • x ∈ P.D (a • x + b • y) := by
    have h : (a * b' - b * a') • x = b' • (a • x + b • y) - b • (a' • x + b' • y) := by
      module
    rw [h]
    exact (P.D (a • x + b • y)).sub_mem ((P.D (a • x + b • y)).smul_mem b' huD)
      ((P.D (a • x + b • y)).smul_mem b hw')
  have hdy : (a * b' - b * a') • y ∈ P.D (a • x + b • y) := by
    have h : (a * b' - b * a') • y = a • (a' • x + b' • y) - a' • (a • x + b • y) := by
      module
    rw [h]
    exact (P.D (a • x + b • y)).sub_mem ((P.D (a • x + b • y)).smul_mem a hw')
      ((P.D (a • x + b • y)).smul_mem a' huD)
  have hxD : x ∈ P.D (a • x + b • y) := by
    have h := (P.D (a • x + b • y)).smul_mem (a * b' - b * a')⁻¹ hdx
    rwa [smul_smul, inv_mul_cancel₀ hdet, one_smul] at h
  have hyD' : y ∈ P.D (a • x + b • y) := by
    have h := (P.D (a • x + b • y)).smul_mem (a * b' - b * a')⁻¹ hdy
    rwa [smul_smul, inv_mul_cancel₀ hdet, one_smul] at h
  have hByx : M₀.B y x = 0 := by
    rw [Tim79.QuadModel.B_comm y x, hxy, neg_zero]
  have hBux : M₀.B (a • x + b • y) x = 0 := by
    simp [hByx, M₀.alt x]
  have huDx : a • x + b • y ∈ P.D x := P.D_symm _ hu x hx hBux hxD
  by_cases hb : b = 0
  ·
    have ha : a ≠ 0 := fun ha => hdet (by simp [ha, hb])
    rw [hb, zero_smul, add_zero, P.D_smul x hx a ha] at hyD'
    exact hyD hyD'
  · have haD : a • x ∈ P.D x := (P.D x).smul_mem a (P.mem_D x hx)
    have hbyD : b • y ∈ P.D x := by
      have h : b • y = (a • x + b • y) - a • x := by
        module
      rw [h]
      exact (P.D x).sub_mem huDx haD
    apply hyD
    have h := (P.D x).smul_mem b⁻¹ hbyD
    rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at h

theorem B_eq_zero_of_mem_D {x : M₀.E} (hx : x ∈ P.R) {u v : M₀.E} (hu : u ∈ P.D x)
    (hv : v ∈ P.D x) : M₀.B u v = 0 := by
  have h := M₀.Qf_add u v
  rw [P.D_sing x hx _ ((P.D x).add_mem hu hv), P.D_sing x hx u hu, P.D_sing x hx v hv] at h
  simpa using h.symm

theorem finrank_Nsub_le {x : M₀.E} (hx : x ∈ P.R) : Module.finrank K (P.Nsub x) ≤ 2 := by
  have hfin : Module.Finite K M₀.E := M₀.fin
  by_contra hlt
  have h3 : 2 < Module.finrank K (P.Nsub x) := not_le.mp hlt
  obtain ⟨e, he, hBxe⟩ : ∃ e ∈ P.R, M₀.B x e ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ e ∈ P.R, M₀.B x e = 0 := by
      intro e he
      by_contra h'
      exact hcon ⟨e, he, h'⟩
    have hsub : Submodule.span K P.R ≤ LinearMap.ker (M₀.B x) :=
      Submodule.span_le.mpr (by
        intro e he
        exact LinearMap.mem_ker.mpr (hcon' e he))
    have hall : ∀ w, M₀.B x w = 0 := by
      intro w
      have hw : w ∈ Submodule.span K P.R := by
        rw [P.R_span]
        exact Submodule.mem_top
      exact LinearMap.mem_ker.mp (hsub hw)
    exact P.R_ne x hx (M₀.nondeg x hall)
  obtain ⟨f, -, hf⟩ := P.eich e he
  have hK : Module.finrank K (K × K) < Module.finrank K (P.Nsub x) := by
    rw [Module.finrank_prod, Module.finrank_self]
    omega
  have hker : LinearMap.ker (LinearMap.prod (LinearMap.comp (M₀.B e) (P.Nsub x).subtype)
      (LinearMap.comp f (P.Nsub x).subtype)) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hK
  obtain ⟨y, hyk, hy0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hgy := LinearMap.mem_ker.mp hyk
  have hBy : M₀.B e (y : M₀.E) = 0 := by
    have h1 := congrArg Prod.fst hgy
    simpa using h1
  have hfy : f (y : M₀.E) = 0 := by
    have h2 := congrArg Prod.snd hgy
    simpa using h2
  obtain ⟨hyD, hy'⟩ := (P.mem_Nsub hx).mp y.2
  have hy0' : (y : M₀.E) ≠ 0 := fun h => hy0 (Submodule.coe_eq_zero.mp h)
  have hyR : (y : M₀.E) ∈ P.R := hy'.resolve_left hy0'
  have hyDe : (y : M₀.E) ∈ P.D e := hf _ hyR hBy hfy
  have heDy : e ∈ P.D (y : M₀.E) := P.D_symm e he _ hyR hBy hyDe
  have hBxy : M₀.B x (y : M₀.E) = 0 := B_eq_zero_of_mem_D P hx (P.mem_D x hx) hyD
  have hxDy : x ∈ P.D (y : M₀.E) := P.D_symm x hx _ hyR hBxy hyD
  exact hBxe (B_eq_zero_of_mem_D P hyR hxDy heDy)

theorem Nsub_smul {x : M₀.E} (hx : x ∈ P.R) (c : K) (hc : c ≠ 0) :
    P.Nsub (c • x) = P.Nsub x := by
  ext y
  rw [P.mem_Nsub (P.R_smul x hx c hc), P.mem_Nsub hx, P.D_smul x hx c hc]

theorem no_rootPlane3 (U : Submodule K M₀.E) (hU : Module.finrank K U = 3)
    (hUs : ∀ u ∈ U, M₀.Qf u = 0) (hUR : ∀ u ∈ U, u ≠ 0 → u ∈ P.R) : False := by
  haveI : Module.Finite K M₀.E := M₀.fin
  have hBU : ∀ u ∈ U, ∀ v ∈ U, M₀.B u v = 0 := by
    intro u hu v hv
    have h := M₀.Qf_add u v
    rw [hUs _ (U.add_mem hu hv), hUs u hu, hUs v hv] at h
    simpa using h.symm
  have hdim_le : ∀ x ∈ U, x ≠ 0 → Module.finrank K ↥(P.Nsub x ⊓ U) ≤ 2 := by
    intro x hxU hx0
    exact le_trans (Submodule.finrank_mono (inf_le_left : P.Nsub x ⊓ U ≤ P.Nsub x))
      (P.finrank_Nsub_le (hUR x hxU hx0))
  have hdim_ge : ∀ x ∈ U, x ≠ 0 → 2 ≤ Module.finrank K ↥(P.Nsub x ⊓ U) := by
    intro x hxU hx0
    have hxR : x ∈ P.R := hUR x hxU hx0
    obtain ⟨fx, -, hfx⟩ := P.eich x hxR
    have hrange : Module.finrank K (LinearMap.range (LinearMap.comp fx U.subtype)) ≤ 1 := by
      have h1 := Submodule.finrank_le (LinearMap.range (LinearMap.comp fx U.subtype))
      rw [Module.finrank_self] at h1
      exact h1
    have hrn : Module.finrank K (LinearMap.range (LinearMap.comp fx U.subtype)) +
        Module.finrank K (LinearMap.ker (LinearMap.comp fx U.subtype)) = Module.finrank K U :=
      LinearMap.finrank_range_add_finrank_ker _
    have hker : 2 ≤ Module.finrank K (LinearMap.ker (LinearMap.comp fx U.subtype)) := by
      omega
    have hsub : (LinearMap.ker (LinearMap.comp fx U.subtype)).map U.subtype ≤
        P.Nsub x ⊓ U := by
      rintro v ⟨u, hu, rfl⟩
      have hfu : fx (u : M₀.E) = 0 := by simpa using LinearMap.mem_ker.mp hu
      have huU : (u : M₀.E) ∈ U := u.2
      show (u : M₀.E) ∈ P.Nsub x ⊓ U
      refine Submodule.mem_inf.mpr ⟨(P.mem_Nsub hxR).mpr ⟨?_, ?_⟩, huU⟩
      · by_cases hu0 : (u : M₀.E) = 0
        · rw [hu0]
          exact (P.D x).zero_mem
        · exact hfx _ (hUR _ huU hu0) (hBU x hxU _ huU) hfu
      · by_cases hu0 : (u : M₀.E) = 0
        · exact Or.inl hu0
        · exact Or.inr (hUR _ huU hu0)
    have hmap : Module.finrank K ((LinearMap.ker (LinearMap.comp fx U.subtype)).map U.subtype) =
        Module.finrank K (LinearMap.ker (LinearMap.comp fx U.subtype)) :=
      Submodule.finrank_map_subtype_eq U (LinearMap.ker (LinearMap.comp fx U.subtype))
    exact le_trans hker (le_trans (le_of_eq hmap.symm) (Submodule.finrank_mono hsub))
  have hdim : ∀ x ∈ U, x ≠ 0 → Module.finrank K ↥(P.Nsub x ⊓ U) = 2 :=
    fun x hxU hx0 => le_antisymm (hdim_le x hxU hx0) (hdim_ge x hxU hx0)
  have hmem : ∀ x ∈ U, x ≠ 0 → x ∈ P.Nsub x ⊓ U := fun x hxU hx0 =>
    Submodule.mem_inf.mpr ⟨(P.mem_Nsub (hUR x hxU hx0)).mpr
      ⟨P.mem_D x (hUR x hxU hx0), Or.inr (hUR x hxU hx0)⟩, hxU⟩
  have hle : ∀ x ∈ U, x ≠ 0 → P.Nsub x ⊓ U ≤ U := fun _ _ _ => inf_le_right
  have hplane : ∀ x ∈ U, x ≠ 0 → ∀ z ∈ P.Nsub x ⊓ U, (¬ ∃ c : K, z = c • x) →
      ∀ w ∈ P.Nsub x ⊓ U, ∃ α β : K, w = α • x + β • z := by
    intro x hxU hx0 z hzW hzx w hwW
    have hxW : x ∈ P.Nsub x ⊓ U := hmem x hxU hx0
    have hli : LinearIndependent K ![x, z] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        have hs : s • x = 0 := by rwa [zero_smul, add_zero] at hst
        exact ⟨(smul_eq_zero.mp hs).resolve_right hx0, rfl⟩
      · exfalso
        apply hzx
        refine ⟨-s / t, ?_⟩
        have h5 : t • z = -(s • x) := eq_neg_iff_add_eq_zero.mpr (by rwa [add_comm])
        calc z = t⁻¹ • (t • z) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = t⁻¹ • (-(s • x)) := by rw [h5]
          _ = (-s / t) • x := by
            rw [smul_neg, smul_smul, ← neg_smul]
            congr 1
            ring
    have hdimS : Module.finrank K (Submodule.span K (Set.range ![x, z])) = 2 := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    have hSle : Submodule.span K (Set.range ![x, z]) ≤ P.Nsub x ⊓ U := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hxW
      · exact hzW
    have hdimW : Module.finrank K ↥(P.Nsub x ⊓ U) = 2 := hdim x hxU hx0
    have hSeq : Submodule.span K (Set.range ![x, z]) = P.Nsub x ⊓ U :=
      Submodule.eq_of_le_of_finrank_le hSle (le_of_eq (hdimW.trans hdimS.symm))
    have hwS : w ∈ Submodule.span K (Set.range ![x, z]) := by
      rw [hSeq]
      exact hwW
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hwS
    rw [Fin.sum_univ_two] at hc
    exact ⟨c 0, c 1, by simpa using hc.symm⟩
  have heq : ∀ x ∈ U, x ≠ 0 → ∀ z ∈ P.Nsub x ⊓ U, z ≠ 0 → P.Nsub z ⊓ U = P.Nsub x ⊓ U := by
    intro x hxU hx0 z hzW hz0
    have hxR : x ∈ P.R := hUR x hxU hx0
    obtain ⟨hzN, hzU⟩ := Submodule.mem_inf.mp hzW
    have hzR : z ∈ P.R := hUR z hzU hz0
    by_cases hzx : ∃ c : K, z = c • x
    · obtain ⟨c, rfl⟩ := hzx
      have hc : c ≠ 0 := by
        rintro rfl
        exact hz0 (by simp)
      rw [P.Nsub_smul hxR c hc]
    · have hWle : P.Nsub x ⊓ U ≤ P.Nsub z ⊓ U := by
        intro w hw
        obtain ⟨hwN, hwU⟩ := Submodule.mem_inf.mp hw
        obtain ⟨-, hw0⟩ := (P.mem_Nsub hxR).mp hwN
        refine Submodule.mem_inf.mpr ⟨(P.mem_Nsub hzR).mpr ⟨?_, hw0⟩, hwU⟩
        by_contra hwDz
        have hw0' : w ≠ 0 := by
          rintro rfl
          exact hwDz (P.D z).zero_mem
        have hwR : w ∈ P.R := hw0.resolve_left hw0'
        obtain ⟨α, β, hab⟩ := hplane x hxU hx0 z hzW hzx w hw
        have hα : α ≠ 0 := by
          rintro rfl
          apply hwDz
          rw [hab, zero_smul, zero_add]
          exact (P.D z).smul_mem β (P.mem_D z hzR)
        have hzw : M₀.B z w = 0 := hBU z hzU w hwU
        have hxeq : (-(β * α⁻¹)) • z + α⁻¹ • w = x := by
          rw [hab, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hα, one_smul]
          module
        have hu : (-(β * α⁻¹)) • z + α⁻¹ • w ∈ P.R := by
          rw [hxeq]
          exact hxR
        have hv : (1 : K) • z + (0 : K) • w ∈ P.R := by
          rw [one_smul, zero_smul, add_zero]
          exact hzR
        have hdet : -(β * α⁻¹) * (0 : K) - α⁻¹ * (1 : K) ≠ 0 := by
          simp [hα]
        have key := P.far_hom hzR hwR hzw hwDz (-(β * α⁻¹)) α⁻¹ 1 0 hdet hu hv
        rw [hxeq, one_smul, zero_smul, add_zero] at key
        exact key ((P.mem_Nsub hxR).mp hzN).1
      have hfin : Module.finrank K ↥(P.Nsub z ⊓ U) ≤ Module.finrank K ↥(P.Nsub x ⊓ U) :=
        le_of_eq ((hdim z hzU hz0).trans (hdim x hxU hx0).symm)
      exact (Submodule.eq_of_le_of_finrank_le hWle hfin).symm
  exact no_plane_partition_sub U hU (fun y => P.Nsub y ⊓ U) hle hdim hmem heq

theorem no_three_space
    (hP : ∀ U : Submodule K M₀.E, Module.finrank K U = 3 → (∀ u ∈ U, M₀.Qf u = 0) →
      (∀ u ∈ U, u ≠ 0 → u ∈ P.R) → False)
    {x y z : M₀.E} (hx : x ∈ P.R) (hy : y ∈ P.R) (hz : z ∈ P.R)
    (hxy : M₀.B x y = 0) (hxz : M₀.B x z = 0) (hyz : M₀.B y z = 0)
    (hyx : y ∉ Submodule.span K {x})
    (hzxy : z ∉ Submodule.span K {x} ⊔ Submodule.span K {y}) : False := by
  have hx0 : x ≠ 0 := P.R_ne x hx
  have hy0 : y ≠ 0 := P.R_ne y hy
  have hz0 : z ≠ 0 := P.R_ne z hz
  have hd1 : Disjoint (Submodule.span K {x}) (Submodule.span K {y}) :=
    (Submodule.disjoint_span_singleton' hy0).mpr hyx
  have hd2 : Disjoint (Submodule.span K {x} ⊔ Submodule.span K {y}) (Submodule.span K {z}) :=
    (Submodule.disjoint_span_singleton' hz0).mpr hzxy
  have hfS : Module.finrank K ↥(Submodule.span K {x} ⊔ Submodule.span K {y}) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {x})
      (Submodule.span K {y})
    rw [disjoint_iff.mp hd1, finrank_bot, finrank_span_singleton hx0,
      finrank_span_singleton hy0] at h
    omega
  have hfU : Module.finrank K ↥(Submodule.span K {x} ⊔ Submodule.span K {y} ⊔
      Submodule.span K {z}) = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span K {x} ⊔ Submodule.span K {y}) (Submodule.span K {z})
    rw [disjoint_iff.mp hd2, finrank_bot, finrank_span_singleton hz0, hfS] at h
    omega
  have hdec : ∀ u ∈ (Submodule.span K {x} ⊔ Submodule.span K {y} ⊔ Submodule.span K {z}),
      ∃ a b c : K, u = a • x + b • y + c • z := by
    intro u hu
    obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hs
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hq
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    exact ⟨a, b, c, rfl⟩
  have hQ : ∀ a b c : K, M₀.Qf (a • x + b • y + c • z) = 0 := by
    intro a b c
    have hB1 : M₀.B (a • x + b • y) (c • z) = 0 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hxz, hyz,
        smul_zero, add_zero]
    have hB2 : M₀.B (a • x) (b • y) = 0 := by
      simp only [map_smul, LinearMap.smul_apply, hxy, smul_zero]
    rw [M₀.Qf_add, M₀.Qf_add, hB1, hB2]
    simp [M₀.Qf_smul, P.R_sing x hx, P.R_sing y hy, P.R_sing z hz]
  have hQU : ∀ u ∈ (Submodule.span K {x} ⊔ Submodule.span K {y} ⊔ Submodule.span K {z}),
      M₀.Qf u = 0 := by
    intro u hu
    obtain ⟨a, b, c, rfl⟩ := hdec u hu
    exact hQ a b c
  have hnzU : ∀ u ∈ (Submodule.span K {x} ⊔ Submodule.span K {y} ⊔ Submodule.span K {z}),
      u ≠ 0 → u ∈ P.R := by
    intro u hu hu0
    obtain ⟨a, b, c, rfl⟩ := hdec u hu
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, add_zero] at hu0 ⊢
      exact P.plane_mem hx hy hxy a b hu0
    · have hw0 : b • y + c • z ≠ 0 := by
        intro hw
        apply hzxy
        have hcz : c • z = -(b • y) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hw
        have hcz_mem : c • z ∈ Submodule.span K {y} := by
          rw [hcz]
          exact Submodule.neg_mem _ (Submodule.smul_mem _ b (Submodule.mem_span_singleton_self y))
        have hzy : z ∈ Submodule.span K {y} := by
          have h := Submodule.smul_mem (Submodule.span K {y}) c⁻¹ hcz_mem
          rwa [inv_smul_smul₀ hc] at h
        exact Submodule.mem_sup_right hzy
      have hwR : b • y + c • z ∈ P.R := P.plane_mem hy hz hyz b c hw0
      have hxw : M₀.B x (b • y + c • z) = 0 := by
        simp only [map_add, map_smul, hxy, hxz, smul_zero, add_zero]
      rw [add_assoc] at hu0 ⊢
      have h1 := P.plane_mem hx hwR hxw a 1 (by rwa [one_smul])
      rwa [one_smul] at h1
  exact hP _ hfU hQU hnzU

theorem far_in_F
    (hthree : ∀ {x y z : M₀.E}, x ∈ P.R → y ∈ P.R → z ∈ P.R → M₀.B x y = 0 → M₀.B x z = 0 →
      M₀.B y z = 0 → y ∉ Submodule.span K {x} →
      z ∉ Submodule.span K {x} ⊔ Submodule.span K {y} → False)
    {x y : M₀.E} (hx : x ∈ P.R) (hy : y ∈ P.R) (hxy : M₀.B x y = 0) (hyD : y ∉ P.D x) :
    ∀ r ∈ P.Λ x, r y - y ∈ Submodule.span K {x} := by
  have hspan : Submodule.span K {x} ≤ P.D x :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (P.mem_D x hx))
  intro r hr
  have hdD : r y - y ∈ P.D x := P.Λ_D x hx r hr y hxy
  have hry : r y ∈ P.R := P.Λ_R x hx r hr y hy
  have hBxry : M₀.B x (r y) = 0 := by
    have h1 := CFSG.RankThree.GF2n.Tim79.QuadModel.B_iso (T := r) (P.Λ_iso x hx r hr) x y
    rw [P.Λ_fix x hx r hr, hxy] at h1
    exact h1
  have hByry : M₀.B y (r y) = 0 := by
    have hdQ : M₀.Qf (r y - y) = 0 := P.D_sing x hx _ hdD
    have hQ1 : M₀.Qf (r y) = 0 := (P.Λ_iso x hx r hr y).trans (P.R_sing y hy)
    have hQy : M₀.Qf y = 0 := P.R_sing y hy
    have e1 : y + (r y - y) = r y := by abel
    have h2 := M₀.Qf_add y (r y - y)
    rw [e1] at h2
    have hB' : M₀.B y (r y - y) = 0 := by
      linear_combination -h2 + hQ1 - hQy - hdQ
    have hadd : M₀.B y (y + (r y - y)) = M₀.B y y + M₀.B y (r y - y) :=
      map_add (M₀.B y) y (r y - y)
    rw [e1] at hadd
    linear_combination hadd + M₀.alt y + hB'
  by_cases hcase : r y ∈ Submodule.span K {x} ⊔ Submodule.span K {y}
  · have hyS : y ∈ Submodule.span K {x} ⊔ Submodule.span K {y} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
    have hdS : r y - y ∈ Submodule.span K {x} ⊔ Submodule.span K {y} :=
      Submodule.sub_mem _ hcase hyS
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hdS
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hbyD : b • y ∈ P.D x := by
      have h1 : b • y = (r y - y) - a • x := by
        rw [← huv]
        abel
      rw [h1]
      exact (P.D x).sub_mem hdD ((P.D x).smul_mem a (P.mem_D x hx))
    have hb : b = 0 := by
      by_contra hb
      apply hyD
      have h2 := (P.D x).smul_mem b⁻¹ hbyD
      rwa [inv_smul_smul₀ hb] at h2
    subst hb
    rw [zero_smul, add_zero] at huv
    exact Submodule.mem_span_singleton.mpr ⟨a, huv⟩
  · have hyx : y ∉ Submodule.span K {x} := fun h => hyD (hspan h)
    exact (hthree hx hy hry hxy hBxry hByry hyx hcase).elim

theorem far_mem_plane
    (hthree : ∀ {x y z : M₀.E}, x ∈ P.R → y ∈ P.R → z ∈ P.R → M₀.B x y = 0 → M₀.B x z = 0 →
      M₀.B y z = 0 → y ∉ Submodule.span K {x} →
      z ∉ Submodule.span K {x} ⊔ Submodule.span K {y} → False)
    {x c c' : M₀.E} (hx : x ∈ P.R) (hc : c ∈ P.R) (hxc : M₀.B x c = 0) (hcD : c ∉ P.D x)
    (hc' : c' ∈ P.R) (hxc' : M₀.B x c' = 0) (hc'D : c' ∉ P.D x) :
    c' ∈ Submodule.span K {x} ⊔ Submodule.span K {c} := by
  have hspan : Submodule.span K {x} ≤ P.D x :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (P.mem_D x hx))
  obtain ⟨f, hf⟩ := P.Fdim x hx
  have hcS : c ∈ P.D x ⊔ Submodule.span K {f} :=
    hf c hxc (P.far_in_F hthree hx hc hxc hcD)
  have hc'S : c' ∈ P.D x ⊔ Submodule.span K {f} :=
    hf c' hxc' (P.far_in_F hthree hx hc' hxc' hc'D)
  have hcc' : M₀.B c c' = 0 := by
    have h := CFSG.ClassicalGroups.polar_eq_zero_of_mem_sup_span M₀.toQuadraticForm (P.D x)
      (fun d hd => (M₀.toQuadraticForm_apply d).trans (P.D_sing x hx d hd)) hcS hc'S hcD hc'D
      ((M₀.toQuadraticForm_apply c).trans (P.R_sing c hc))
      ((M₀.toQuadraticForm_apply c').trans (P.R_sing c' hc'))
    exact (M₀.polar_toQuadraticForm c c').symm.trans h
  by_contra hcon
  exact hthree hx hc hc' hxc hxc' hcc' (fun h => hcD (hspan h)) hcon

theorem exists_root_not_orth {x : M₀.E} (hx : x ≠ 0) : ∃ y ∈ P.R, M₀.B x y ≠ 0 := by
  by_contra hcon
  have hcon' : ∀ e ∈ P.R, M₀.B x e = 0 := by
    intro e he
    by_contra h'
    exact hcon ⟨e, he, h'⟩
  have hsub : Submodule.span K P.R ≤ LinearMap.ker (M₀.B x) :=
    Submodule.span_le.mpr (by
      intro e he
      exact LinearMap.mem_ker.mpr (hcon' e he))
  have hall : ∀ w, M₀.B x w = 0 := by
    intro w
    have hw : w ∈ Submodule.span K P.R := by
      rw [P.R_span]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp (hsub hw)
  exact hx (M₀.nondeg x hall)

theorem false_of_Nsub_trivial
    (hF : ∀ {x c c' : M₀.E}, x ∈ P.R → c ∈ P.R → M₀.B x c = 0 → c ∉ P.D x → c' ∈ P.R →
      M₀.B x c' = 0 → c' ∉ P.D x → c' ∈ Submodule.span K {x} ⊔ Submodule.span K {c})
    (hne : ∃ x, x ∈ P.R)
    (htriv : ∀ x ∈ P.R, P.Nsub x ≤ Submodule.span K {x}) : False := by
  have hsymm0 : ∀ e f : M₀.E, M₀.B e f = 0 → M₀.B f e = 0 := by
    intro e f h
    rw [Tim79.QuadModel.B_comm f e, h, neg_zero]
  obtain ⟨x, hx⟩ := hne
  obtain ⟨c, hc, hBxc, hcD⟩ := P.far_exists x hx
  obtain ⟨y, hy, hBxy⟩ := P.exists_root_not_orth (P.R_ne x hx)
  have hBcx : M₀.B c x = 0 := hsymm0 x c hBxc
  obtain ⟨α, hα⟩ : ∃ α : K, M₀.B y x = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : K, M₀.B y c = β := ⟨_, rfl⟩
  have hα0 : α ≠ 0 := by
    intro h0
    apply hBxy
    have h1 := Tim79.QuadModel.B_comm y x
    rw [hα, h0] at h1
    exact neg_eq_zero.mp h1.symm
  obtain ⟨z, hzdef⟩ : ∃ z : M₀.E, z = α • c - β • x := ⟨_, rfl⟩
  have hBxz : M₀.B x z = 0 := by
    rw [hzdef, map_sub, map_smul, map_smul, hBxc, M₀.alt x, smul_zero, smul_zero, sub_zero]
  have hBzx : M₀.B z x = 0 := hsymm0 x z hBxz
  have hByz : M₀.B y z = 0 := by
    rw [hzdef, map_sub, map_smul, map_smul, hβ, hα, smul_eq_mul, smul_eq_mul]
    ring
  have hBzy : M₀.B z y = 0 := hsymm0 y z hByz
  have hzne : z ≠ 0 := by
    intro h0
    rw [hzdef, sub_eq_zero] at h0
    have h1 : α • c ∈ P.D x := by
      rw [h0]
      exact (P.D x).smul_mem β (P.mem_D x hx)
    have h3 := (P.D x).smul_mem α⁻¹ h1
    rw [smul_smul, inv_mul_cancel₀ hα0, one_smul] at h3
    exact hcD h3
  have hne' : α • c + (-β) • x ≠ 0 := by
    rw [neg_smul, ← sub_eq_add_neg, ← hzdef]
    exact hzne
  have hzR : z ∈ P.R := by
    have h1 := P.plane_mem hc hx hBcx α (-β) hne'
    rw [neg_smul, ← sub_eq_add_neg, ← hzdef] at h1
    exact h1
  have hzD : z ∉ P.D x := by
    intro h
    apply hcD
    have h2 : α • c = z + β • x := by
      rw [hzdef, sub_add_cancel]
    have h1 : α • c ∈ P.D x := by
      rw [h2]
      exact (P.D x).add_mem h ((P.D x).smul_mem β (P.mem_D x hx))
    have h3 := (P.D x).smul_mem α⁻¹ h1
    rw [smul_smul, inv_mul_cancel₀ hα0, one_smul] at h3
    exact h3
  have hxDz : x ∉ P.D z := fun h => hzD (P.D_symm z hzR x hx hBzx h)
  by_cases hyDz : y ∈ P.D z
  ·
    have hmem : y ∈ P.Nsub z := (P.mem_Nsub hzR).mpr ⟨hyDz, Or.inr hy⟩
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (htriv z hzR hmem)
    apply hBxy
    rw [← ht, map_smul, hBxz, smul_zero]
  ·
    have hsup := hF hzR hx hBzx hxDz hy hBzy hyDz
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hsup
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hw
    apply hBxy
    rw [← huw, ← ht, ← hs, map_add, map_smul, map_smul, hBxz, M₀.alt x]
    simp

theorem span_singleton_le_of_mem {p : Submodule K M₀.E} {v : M₀.E} (h : v ∈ p) :
    Submodule.span K {v} ≤ p :=
  Submodule.span_le.mpr (Set.singleton_subset_iff.mpr h)

theorem finrank_span_pair {a b : M₀.E} (ha : a ≠ 0) (hb : b ∉ Submodule.span K {a}) :
    Module.finrank K ↥(Submodule.span K {a} ⊔ Submodule.span K {b}) = 2 := by
  haveI : Module.Finite K M₀.E := M₀.fin
  have hb0 : b ≠ 0 := fun h => hb (by rw [h]; exact Submodule.zero_mem _)
  have hd : Disjoint (Submodule.span K {a}) (Submodule.span K {b}) :=
    (Submodule.disjoint_span_singleton' hb0).mpr hb
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {a})
    (Submodule.span K {b})
  rw [disjoint_iff.mp hd, finrank_bot, finrank_span_singleton ha,
    finrank_span_singleton hb0] at h
  omega

theorem span_sup_eq_Nsub (hH : ∀ w ∈ P.R, Module.finrank K (P.Nsub w) ≤ 2) {x z : M₀.E}
    (hx : x ∈ P.R) (hzN : z ∈ P.Nsub x) (hzx : z ∉ Submodule.span K {x}) :
    Submodule.span K {x} ⊔ Submodule.span K {z} = P.Nsub x := by
  haveI : Module.Finite K M₀.E := M₀.fin
  have hxN : x ∈ P.Nsub x := (P.mem_Nsub hx).mpr ⟨P.mem_D x hx, Or.inr hx⟩
  have hle : Submodule.span K {x} ⊔ Submodule.span K {z} ≤ P.Nsub x :=
    sup_le (span_singleton_le_of_mem hxN) (span_singleton_le_of_mem hzN)
  have h1 := finrank_span_pair (P.R_ne x hx) hzx
  have h2 := hH x hx
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

theorem false_of_Nsub_big
    (hH : ∀ x ∈ P.R, Module.finrank K (P.Nsub x) ≤ 2)
    (hthree : ∀ {x y z : M₀.E}, x ∈ P.R → y ∈ P.R → z ∈ P.R → M₀.B x y = 0 → M₀.B x z = 0 →
      M₀.B y z = 0 → y ∉ Submodule.span K {x} →
      z ∉ Submodule.span K {x} ⊔ Submodule.span K {y} → False)
    (hF : ∀ {x c c' : M₀.E}, x ∈ P.R → c ∈ P.R → M₀.B x c = 0 → c ∉ P.D x → c' ∈ P.R →
      M₀.B x c' = 0 → c' ∉ P.D x → c' ∈ Submodule.span K {x} ⊔ Submodule.span K {c})
    (hdim : 5 ≤ Module.finrank K M₀.E)
    {x : M₀.E} (hx : x ∈ P.R) (hbig : ¬ P.Nsub x ≤ Submodule.span K {x}) : False := by
  haveI : Module.Finite K M₀.E := M₀.fin
  have hx0 : x ≠ 0 := P.R_ne x hx
  have hxN : x ∈ P.Nsub x := (P.mem_Nsub hx).mpr ⟨P.mem_D x hx, Or.inr hx⟩
  obtain ⟨z₀, hz₀N, hz₀⟩ := SetLike.not_le_iff_exists.mp hbig
  obtain ⟨c, hcR, hxc, hcD⟩ := P.far_exists x hx
  have hcx : M₀.B c x = 0 := by
    rw [Tim79.QuadModel.B_comm c x, hxc, neg_zero]
  have hcN : c ∈ P.Nsub c := (P.mem_Nsub hcR).mpr ⟨P.mem_D c hcR, Or.inr hcR⟩
  have hxDc : x ∉ P.D c := fun h => hcD (P.D_symm c hcR x hx hcx h)
  have hmain : ∀ y ∈ P.R, y ∈ P.Nsub x ⊔ P.Nsub c := by
    intro y hy
    by_cases hxy : M₀.B x y = 0
    · by_cases hyD : y ∈ P.D x
      · exact Submodule.mem_sup_left ((P.mem_Nsub hx).mpr ⟨hyD, Or.inr hy⟩)
      · have hsp := hF hx hcR hxc hcD hy hxy hyD
        exact sup_le_sup (span_singleton_le_of_mem hxN) (span_singleton_le_of_mem hcN) hsp
    ·
      have hα : M₀.B y x ≠ 0 := by
        rw [Tim79.QuadModel.B_comm y x]
        exact neg_ne_zero.mpr hxy
      obtain ⟨z, hzdef⟩ : ∃ z : M₀.E, z = M₀.B y x • z₀ - M₀.B y z₀ • x := ⟨_, rfl⟩
      have hzN : z ∈ P.Nsub x := by
        rw [hzdef]
        exact (P.Nsub x).sub_mem ((P.Nsub x).smul_mem _ hz₀N) ((P.Nsub x).smul_mem _ hxN)
      have hBy_z : M₀.B y z = 0 := by
        rw [hzdef]
        simp only [map_sub, map_smul, smul_eq_mul]
        ring
      have hzx : z ∉ Submodule.span K {x} := by
        intro hzs
        apply hz₀
        have h1 : M₀.B y x • z₀ = z + M₀.B y z₀ • x := by
          rw [hzdef, sub_add_cancel]
        have h2 : M₀.B y x • z₀ ∈ Submodule.span K {x} := by
          rw [h1]
          exact Submodule.add_mem _ hzs
            (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
        have h3 := Submodule.smul_mem (Submodule.span K {x}) (M₀.B y x)⁻¹ h2
        rwa [smul_smul, inv_mul_cancel₀ hα, one_smul] at h3
      have hzR : z ∈ P.R := by
        rcases ((P.mem_Nsub hx).mp hzN).2 with h | h
        · exact (hzx (by rw [h]; exact Submodule.zero_mem _)).elim
        · exact h
      have hzD : z ∈ P.D x := ((P.mem_Nsub hx).mp hzN).1
      have hBxz : M₀.B x z = 0 := B_eq_zero_of_mem_D P hx (P.mem_D x hx) hzD
      have hsupD : Submodule.span K {x} ⊔ Submodule.span K {z} ≤ P.D x :=
        sup_le (span_singleton_le_of_mem (P.mem_D x hx)) (span_singleton_le_of_mem hzD)
      have hxDz : x ∈ P.D z := P.D_symm x hx z hzR hBxz hzD
      have hNz : P.Nsub z = P.Nsub x := by
        have e1 := span_sup_eq_Nsub P hH hx hzN hzx
        have hxNz : x ∈ P.Nsub z := (P.mem_Nsub hzR).mpr ⟨hxDz, Or.inr hx⟩
        have hzNz : z ∈ P.Nsub z := (P.mem_Nsub hzR).mpr ⟨P.mem_D z hzR, Or.inr hzR⟩
        have hle : Submodule.span K {x} ⊔ Submodule.span K {z} ≤ P.Nsub z :=
          sup_le (span_singleton_le_of_mem hxNz) (span_singleton_le_of_mem hzNz)
        have e2 : Submodule.span K {x} ⊔ Submodule.span K {z} = P.Nsub z := by
          apply Submodule.eq_of_le_of_finrank_le hle
          have h1 := finrank_span_pair hx0 hzx
          have h2 := hH z hzR
          omega
        exact e2.symm.trans e1
      have hyDz : y ∉ P.D z := by
        intro hyDz
        have hyNz : y ∈ P.Nsub z := (P.mem_Nsub hzR).mpr ⟨hyDz, Or.inr hy⟩
        rw [hNz] at hyNz
        exact hxy (B_eq_zero_of_mem_D P hx (P.mem_D x hx) ((P.mem_Nsub hx).mp hyNz).1)
      have hzy : M₀.B z y = 0 := by
        rw [Tim79.QuadModel.B_comm z y, hBy_z, neg_zero]
      have hzc : M₀.B z c ≠ 0 := by
        intro h0
        exact hthree hx hzR hcR hBxz hxc h0 hzx (fun h => hcD (hsupD h))
      have hcz : M₀.B c z ≠ 0 := by
        rw [Tim79.QuadModel.B_comm c z]
        exact neg_ne_zero.mpr hzc
      obtain ⟨u, hudef⟩ : ∃ u : M₀.E, u = M₀.B c z • y - M₀.B c y • z := ⟨_, rfl⟩
      have hu_eq : (-(M₀.B c y)) • z + M₀.B c z • y = u := by
        rw [hudef]
        module
      have hne : (-(M₀.B c y)) • z + M₀.B c z • y ≠ 0 := by
        intro h0
        apply hyDz
        have h1 : M₀.B c z • y = M₀.B c y • z := by
          rw [neg_smul] at h0
          exact (neg_add_eq_zero.mp h0).symm
        have h2 : y = (M₀.B c z)⁻¹ • (M₀.B c y • z) := by
          rw [← h1, smul_smul, inv_mul_cancel₀ hcz, one_smul]
        rw [h2]
        exact (P.D z).smul_mem _ ((P.D z).smul_mem _ (P.mem_D z hzR))
      have hu0 : u ≠ 0 := by
        rw [← hu_eq]
        exact hne
      have huR : u ∈ P.R := by
        rw [← hu_eq]
        exact P.plane_mem hzR hy hzy _ _ hne
      have hcu : M₀.B c u = 0 := by
        rw [hudef]
        simp only [map_sub, map_smul, smul_eq_mul]
        ring
      have hzu : M₀.B z u = 0 := by
        rw [hudef]
        simp [hzy, M₀.alt]
      have hy_eq : ((M₀.B c z)⁻¹ * M₀.B c y) • z + (M₀.B c z)⁻¹ • u = y := by
        rw [hudef, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hcz, one_smul]
        abel
      have hux : u ∉ Submodule.span K {x} := by
        intro hus
        obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hus
        have ht0 : t ≠ 0 := by
          intro h0
          apply hu0
          rw [← ht, h0, zero_smul]
        have hxeq : (-(t⁻¹ * M₀.B c y)) • z + (t⁻¹ * M₀.B c z) • y = x := by
          have e1 : (-(t⁻¹ * M₀.B c y)) • z + (t⁻¹ * M₀.B c z) • y = t⁻¹ • u := by
            rw [hudef]
            module
          rw [e1, ← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
        have hfar := P.far_hom hzR hy hzy hyDz 1 0 (-(t⁻¹ * M₀.B c y)) (t⁻¹ * M₀.B c z)
          (by rw [one_mul, zero_mul, sub_zero]; exact mul_ne_zero (inv_ne_zero ht0) hcz)
          (by rw [one_smul, zero_smul, add_zero]; exact hzR)
          (by rw [hxeq]; exact hx)
        rw [one_smul, zero_smul, add_zero, hxeq] at hfar
        exact hfar hxDz
      have huDc : u ∈ P.D c := by
        by_contra huDc
        have hu_span : u ∈ Submodule.span K {c} ⊔ Submodule.span K {x} :=
          hF hcR hx hcx hxDc huR hcu huDc
        obtain ⟨s, hs, w, hw, hsum⟩ := Submodule.mem_sup.mp hu_span
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
        obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hw
        have hxu : M₀.B x u = 0 := by
          rw [← hsum]
          simp [hxc, M₀.alt]
        have huNot : u ∉ Submodule.span K {x} ⊔ Submodule.span K {z} := by
          intro hus
          apply hux
          have huDx : u ∈ P.D x := hsupD hus
          have haD : a • c ∈ P.D x := by
            rw [eq_sub_of_add_eq hsum]
            exact (P.D x).sub_mem huDx ((P.D x).smul_mem b (P.mem_D x hx))
          have ha : a = 0 := by
            by_contra ha
            apply hcD
            have h2 := (P.D x).smul_mem a⁻¹ haD
            rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2
          rw [← hsum, ha, zero_smul, zero_add]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
        exact hthree hx hzR huR hBxz hxu hzu hzx huNot
      have huNc : u ∈ P.Nsub c := (P.mem_Nsub hcR).mpr ⟨huDc, Or.inr huR⟩
      have hzpart : ((M₀.B c z)⁻¹ * M₀.B c y) • z ∈ P.Nsub x := (P.Nsub x).smul_mem _ hzN
      have hupart : (M₀.B c z)⁻¹ • u ∈ P.Nsub c := (P.Nsub c).smul_mem _ huNc
      have hsum2 : ((M₀.B c z)⁻¹ * M₀.B c y) • z + (M₀.B c z)⁻¹ • u ∈ P.Nsub x ⊔ P.Nsub c :=
        Submodule.add_mem _ (Submodule.mem_sup_left hzpart) (Submodule.mem_sup_right hupart)
      rw [hy_eq] at hsum2
      exact hsum2
  have hTop : (⊤ : Submodule K M₀.E) ≤ P.Nsub x ⊔ P.Nsub c := by
    rw [← P.R_span]
    exact Submodule.span_le.mpr (fun y hy => hmain y hy)
  have hfin4 : Module.finrank K (⊤ : Submodule K M₀.E) ≤
      Module.finrank K ↥(P.Nsub x ⊔ P.Nsub c) := Submodule.finrank_mono hTop
  have hsum4 := Submodule.finrank_sup_add_finrank_inf_eq (P.Nsub x) (P.Nsub c)
  rw [finrank_top] at hfin4
  have h1 := hH x hx
  have h2 := hH c hcR
  omega

include P in
theorem false_of_dim (hdim : 6 ≤ Module.finrank K M₀.E) : False := by
  have hH : ∀ x ∈ P.R, Module.finrank K (P.Nsub x) ≤ 2 := fun x hx => P.finrank_Nsub_le hx
  have hthree : ∀ {x y z : M₀.E}, x ∈ P.R → y ∈ P.R → z ∈ P.R → M₀.B x y = 0 → M₀.B x z = 0 →
      M₀.B y z = 0 → y ∉ Submodule.span K {x} →
      z ∉ Submodule.span K {x} ⊔ Submodule.span K {y} → False :=
    fun hx hy hz hxy hxz hyz hyx hzxy =>
      P.no_three_space (fun U h3 hs hR => P.no_rootPlane3 U h3 hs hR) hx hy hz hxy hxz hyz hyx
        hzxy
  have hF : ∀ {x c c' : M₀.E}, x ∈ P.R → c ∈ P.R → M₀.B x c = 0 → c ∉ P.D x → c' ∈ P.R →
      M₀.B x c' = 0 → c' ∉ P.D x → c' ∈ Submodule.span K {x} ⊔ Submodule.span K {c} :=
    fun hx hc hxc hcD hc' hxc' hc'D => P.far_mem_plane hthree hx hc hxc hcD hc' hxc' hc'D
  have hne : ∃ x, x ∈ P.R := by
    by_contra hcon
    push Not at hcon
    have h0 : P.R = ∅ := Set.eq_empty_of_forall_notMem hcon
    have h1 := P.R_span
    rw [h0, Submodule.span_empty] at h1
    have h2 := congrArg (fun S : Submodule K M₀.E => Module.finrank K S) h1
    simp only [finrank_bot, finrank_top] at h2
    omega
  by_cases htriv : ∀ x ∈ P.R, P.Nsub x ≤ Submodule.span K {x}
  · exact P.false_of_Nsub_trivial hF hne htriv
  · push Not at htriv
    obtain ⟨x, hx, hbig⟩ := htriv
    exact P.false_of_Nsub_big hH hthree hF (by omega) hx hbig

end RootGeom

end CFSG.RankThree.GF2n.Stroth80
