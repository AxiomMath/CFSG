module

public import CFSG.Quasithin.Vol2.Ch1Unique

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isTwoLocal_map_conj {M : Subgroup G} (hM : IsTwoLocal M) (g : G) :
    IsTwoLocal (M.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨P, hP, hP2, rfl⟩ := hM
  refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, hP2.map _, ?_⟩
  · intro h
    exact hP ((Subgroup.map_eq_bot_iff_of_injective P (MulAut.conj g).injective).mp h)
  · exact Subgroup.map_normalizer_eq_of_bijective P (MulAut.conj g).bijective

omit [Finite G] in
theorem map_conj_map_conj_inv (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = K := by
  ext x
  rw [A38.mem_map_conj, A38.mem_map_conj]
  simp [mul_assoc]

omit [Finite G] in
theorem quasithinIsMaxTwoLocal_map_conj {M : Subgroup G} (hM : quasithinIsMaxTwoLocal M) (g : G) :
    quasithinIsMaxTwoLocal (M.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨isTwoLocal_map_conj hM.1 g, fun H hH hMH => ?_⟩
  have hH' : IsTwoLocal (H.map (MulAut.conj g⁻¹).toMonoidHom) := isTwoLocal_map_conj hH g⁻¹
  have hMH' : M ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hMH
    rwa [map_conj_map_conj_inv] at this
  have h1 := hM.2 _ hH' hMH'
  have h3 := map_conj_map_conj_inv H g⁻¹
  rw [inv_inv] at h3
  rw [← h1]
  exact h3.symm

theorem normalizer_eq_of_quasithinIsMaxTwoLocal {M : Subgroup G} (hM : quasithinIsMaxTwoLocal M) :
    Subgroup.normalizer (M : Set G) = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Subgroup.normalizer (pCoreOf 2 M : Set G) = M :=
    hM.2 _ ⟨pCoreOf 2 M, pCoreOf_ne_bot_of_isTwoLocal hM.1, pCoreOf_isPGroup 2 M, rfl⟩
      (le_normalizer_pCoreOf 2 M)
  refine le_antisymm ?_ Subgroup.le_normalizer
  exact (normalizer_le_normalizer_pCoreOf 2 M).trans h1.le

theorem lemma_1_2_7_four (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {T L : Subgroup G} (hT : quasithinIsSylowTwo T) (hL : quasithinIsMaximalLocal T L) {g : G}
    (hg : g ∉ Subgroup.normalizer (conjClosure L T : Set G)) :
    (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (conjClosure L T : Set G)) ⊓
      conjSubgroup (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (conjClosure L T : Set G)) g
        = ⊥ := by
  by_contra hne
  set Z := quasithinOmegaOneCenter T with hZ
  set L₀ := conjClosure L T with hL₀
  set C := Z ⊓ Subgroup.centralizer (L₀ : Set G) with hC
  set Z₀ := C ⊓ conjSubgroup C g with hZ₀
  have hU := lemma_1_2_7_three hK hs hnab h37 h38 h39 hT hL
  have hZT : Z ≤ T ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hZ, quasithinOmegaOneCenter, Subgroup.closure_le]
    exact fun x hx => hx.1
  have hZ2 : IsPGroup 2 Z := fun z =>
    ⟨1, Subtype.ext (by simpa using sq_eq_one_of_mem_omegaOneCenter T z.2)⟩
  have hZ₀2 : IsPGroup 2 Z₀ := hZ2.to_le (inf_le_left.trans inf_le_left)
  have hCT : C ≤ Subgroup.centralizer (T : Set G) := inf_le_left.trans (hZT.trans inf_le_right)
  have hLTC : L₀ ⊔ T ≤ Subgroup.centralizer (C : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mpr inf_le_right) (Subgroup.le_centralizer_iff.mpr hCT)
  have hLTZ : L₀ ⊔ T ≤ Subgroup.centralizer (Z₀ : Set G) :=
    hLTC.trans (Subgroup.centralizer_le inf_le_left)
  have hconj : conjSubgroup (L₀ ⊔ T) g ≤ Subgroup.centralizer (Z₀ : Set G) := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : g * z * g⁻¹ ∈ C := mem_conjSubgroup_iff.mp hz.2
    have h1 := Subgroup.mem_centralizer_iff.mp (hLTC hx) _ hz'
    have h2 : g * (z * x) * g⁻¹ = g * (x * z) * g⁻¹ := by
      calc g * (z * x) * g⁻¹ = (g * z * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * z * g⁻¹) := h1
        _ = g * (x * z) * g⁻¹ := by group
    simpa using h2
  have hloc : IsTwoLocal (Subgroup.normalizer (Z₀ : Set G)) := ⟨Z₀, hne, hZ₀2, rfl⟩
  obtain ⟨M₂, hM₂, hle⟩ := exists_maxTwoLocal_ge hloc
  have hcen : Subgroup.centralizer (Z₀ : Set G) ≤ M₂ :=
    (Subgroup.centralizer_le_normalizer _).trans hle
  have hLT₁ : L ⊔ T ≤ L₀ ⊔ T := sup_le_sup (le_conjClosure L T) le_rfl
  have hM₂in : InM (L ⊔ T) M₂ := ⟨hM₂, (hLT₁.trans hLTZ).trans hcen⟩
  have hM₂eq : M₂ = Subgroup.normalizer (L₀ : Set G) := hU.2 M₂ hM₂in
  have hLTg : L ⊔ T ≤ M₂.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    rw [A38.mem_map_conj]
    refine hcen (hconj ?_)
    rw [mem_conjSubgroup_iff]
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [this]
    exact hLT₁ hx
  have hM₃ := quasithinIsMaxTwoLocal_map_conj hM₂ g
  have hM₃eq : M₂.map (MulAut.conj g).toMonoidHom = Subgroup.normalizer (L₀ : Set G) :=
    hU.2 _ ⟨hM₃, hLTg⟩
  have hgM : g ∈ Subgroup.normalizer (M₂ : Set G) :=
    A38.map_conj_eq_iff.mp (hM₃eq.trans hM₂eq.symm)
  rw [normalizer_eq_of_quasithinIsMaxTwoLocal hM₂, hM₂eq] at hgM
  exact hg hgM

end CFSG.Quasithin
