module

public import CFSG.Milestones.ASVolI.C31.J4NP.Prop12

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open CFSG.Quasithin.J4Loc (omegaZ)

theorem burnsideJ4NP_centralizer_map_conj {G : Type*} [Group G] (X : Subgroup G) (c : G) :
    Subgroup.centralizer ((X.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.centralizer (X : Set G)).map (MulAut.conj c).toMonoidHom := by
  ext y
  rw [burnsideJ4NP_mem_map_conj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have h1 := h (c * x * c⁻¹) (burnsideJ4NP_mem_map_conj.mpr (by simpa [mul_assoc] using hx))
    calc x * (c⁻¹ * y * c) = c⁻¹ * ((c * x * c⁻¹) * y) * c := by group
      _ = c⁻¹ * (y * (c * x * c⁻¹)) * c := by rw [h1]
      _ = c⁻¹ * y * c * x := by group
  · intro h x hx
    have h1 := h _ (burnsideJ4NP_mem_map_conj.mp hx)
    calc x * y = c * ((c⁻¹ * x * c) * (c⁻¹ * y * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y * c) * (c⁻¹ * x * c)) * c⁻¹ := by rw [h1]
      _ = y * x := by group

theorem burnsideJ4NP_omegaZ_map_conj {G : Type*} [Group G] (N : Subgroup G) (c : G) :
    omegaZ (N.map (MulAut.conj c).toMonoidHom) = (omegaZ N).map (MulAut.conj c).toMonoidHom := by
  ext y
  rw [burnsideJ4NP_mem_map_conj, CFSG.Quasithin.J4Loc.mem_omegaZ,
    CFSG.Quasithin.J4Loc.mem_omegaZ, burnsideJ4NP_mem_map_conj]
  constructor
  · rintro ⟨hyN, hyc, hys⟩
    refine ⟨hyN, fun x hx => ?_, ?_⟩
    · have h1 := hyc (c * x * c⁻¹) (by rw [burnsideJ4NP_mem_map_conj]; simpa [mul_assoc] using hx)
      calc c⁻¹ * y * c * x = c⁻¹ * (y * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * y) * c := by rw [h1]
        _ = x * (c⁻¹ * y * c) := by group
    · calc c⁻¹ * y * c * (c⁻¹ * y * c) = c⁻¹ * (y * y) * c := by group
        _ = 1 := by rw [hys]; group
  · rintro ⟨hyN, hyc, hys⟩
    refine ⟨hyN, fun x hx => ?_, ?_⟩
    · rw [burnsideJ4NP_mem_map_conj] at hx
      have h1 := hyc _ hx
      calc y * x = c * ((c⁻¹ * y * c) * (c⁻¹ * x * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * x * c) * (c⁻¹ * y * c)) * c⁻¹ := by rw [h1]
        _ = x * y := by group
    · calc y * y = c * ((c⁻¹ * y * c) * (c⁻¹ * y * c)) * c⁻¹ := by group
        _ = 1 := by rw [hys]; group

theorem burnsideJ4NP_pCoreOf_map_conj (K : Subgroup J) (c : J) :
    CFSG.Open.pCoreOf 2 (K.map (MulAut.conj c).toMonoidHom) =
      (CFSG.Open.pCoreOf 2 K).map (MulAut.conj c).toMonoidHom := by
  have key : ∀ (K : Subgroup J) (c : J), (CFSG.Open.pCoreOf 2 K).map (MulAut.conj c).toMonoidHom ≤
      CFSG.Open.pCoreOf 2 (K.map (MulAut.conj c).toMonoidHom) := by
    intro K c
    apply burnsideJ4KW_le_pCoreOf ((burnsideJ4KW_isPGroup_pCoreOf K).map _)
    · exact Subgroup.map_mono (Subgroup.map_subtype_le _)
    · rw [burnsideJ4NP_normalizer_map_conj]
      exact Subgroup.map_mono (burnsideJ4KW_le_normalizer_pCoreOf K)
  apply le_antisymm _ (key K c)
  have h1 := Subgroup.map_mono (f := (MulAut.conj c).toMonoidHom)
    (key (K.map (MulAut.conj c).toMonoidHom) c⁻¹)
  rwa [burnsideJ4NP_map_conj_inv_map_conj, burnsideJ4KW_map_conj_map_conj, mul_inv_cancel,
    show ∀ X : Subgroup J, X.map (MulAut.conj (1 : J)).toMonoidHom = X from fun X => by
      ext x; rw [burnsideJ4NP_mem_map_conj]; simp] at h1

theorem burnsideJ4NP_Is2A_conj {x : J} (c : J) :
    burnsideJ4NP_Is2A (c * x * c⁻¹) ↔ burnsideJ4NP_Is2A x := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨c⁻¹ * g, by rw [show x = c⁻¹ * (c * x * c⁻¹) * c by group, hg]; group⟩
  · rintro ⟨g, rfl⟩
    exact ⟨c * g, by group⟩

theorem burnsideJ4NP_closure2A_map_conj (A : Subgroup J) (c : J) :
    Subgroup.closure {x | x ∈ A.map (MulAut.conj c).toMonoidHom ∧ burnsideJ4NP_Is2A x} =
      (Subgroup.closure {x | x ∈ A ∧ burnsideJ4NP_Is2A x}).map (MulAut.conj c).toMonoidHom := by
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hyA, hy2⟩
    rw [burnsideJ4NP_mem_map_conj] at hyA
    refine ⟨c⁻¹ * y * c, ⟨hyA, ?_⟩, ?_⟩
    · have := (burnsideJ4NP_Is2A_conj c⁻¹).mpr hy2
      simpa [mul_assoc] using this
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨x, ⟨hxA, hx2⟩, rfl⟩
    refine ⟨⟨x, hxA, rfl⟩, ?_⟩
    exact (burnsideJ4NP_Is2A_conj c).mpr hx2

theorem burnsideJ4NP_survivor
    {R : Subgroup J}
    (hR : burnsideJ4NP_Hyp R) {A A₀ : Subgroup J} {c : J} (hAZ : A ≤ omegaZ R)
    (hWA : burnsideJ4NP_W R ≤ A) (hA : A = A₀.map (MulAut.conj c).toMonoidHom) :
    let W₀ := Subgroup.closure {x | x ∈ A₀ ∧ burnsideJ4NP_Is2A x}
    let R₀ := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (W₀ : Set J))
    R = R₀.map (MulAut.conj c).toMonoidHom ∧
      burnsideJ4NP_W R = W₀.map (MulAut.conj c).toMonoidHom ∧
      IsPGroup 2 ↥R₀ ∧ Subgroup.centralizer (R₀ : Set J) ≤ R₀ ∧ W₀ ≤ A₀ ∧ A₀ ≤ omegaZ R₀ ∧
      Subgroup.normalizer (W₀ : Set J) = Subgroup.normalizer (R₀ : Set J) ∧
      ∀ g : J, ¬ P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (W₀ : Set J) := by
  intro W₀ R₀
  have hW : burnsideJ4NP_W R = W₀.map (MulAut.conj c).toMonoidHom := by
    rw [burnsideJ4NP_W_eq_closure hAZ hWA, hA, burnsideJ4NP_closure2A_map_conj]
  have hRR : R = R₀.map (MulAut.conj c).toMonoidHom := by
    rw [burnsideJ4NP_R_eq_pCore_W hR, hW, burnsideJ4NP_centralizer_map_conj,
      burnsideJ4NP_pCoreOf_map_conj]
  have back : ∀ X : Subgroup J, (X.map (MulAut.conj c).toMonoidHom).map
      (MulAut.conj c⁻¹).toMonoidHom = X := fun X => burnsideJ4NP_map_conj_inv_map_conj X c
  have hR₀ : R₀ = R.map (MulAut.conj c⁻¹).toMonoidHom := by rw [hRR, back]
  have hW₀ : W₀ = (burnsideJ4NP_W R).map (MulAut.conj c⁻¹).toMonoidHom := by rw [hW, back]
  have hA₀ : A₀ = A.map (MulAut.conj c⁻¹).toMonoidHom := by rw [hA, back]
  refine ⟨hRR, hW, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact burnsideJ4KW_isPGroup_pCoreOf _
  · rw [hR₀, burnsideJ4NP_centralizer_map_conj]
    exact Subgroup.map_mono hR.cent
  · rw [hW₀, hA₀]
    exact Subgroup.map_mono hWA
  · rw [hA₀, hR₀, burnsideJ4NP_omegaZ_map_conj]
    exact Subgroup.map_mono hAZ
  · rw [hW₀, hR₀, burnsideJ4NP_normalizer_map_conj, burnsideJ4NP_normalizer_map_conj,
      burnsideJ4NP_normalizer_W hR]
  · intro g hg
    apply burnsideJ4NP_normalizer_W_no_sylow hR (c * g)
    have h1 := Subgroup.map_mono (f := (MulAut.conj c).toMonoidHom) hg
    rw [burnsideJ4KW_map_conj_map_conj] at h1
    have hN : (Subgroup.normalizer (W₀ : Set J)).map (MulAut.conj c).toMonoidHom =
        Subgroup.normalizer (burnsideJ4NP_W R : Set J) := by
      rw [← burnsideJ4NP_normalizer_map_conj, ← hW]
    rwa [hN] at h1

end CFSG.ASVolI
