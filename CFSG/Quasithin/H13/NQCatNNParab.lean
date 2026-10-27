module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNC
public import CFSG.Quasithin.H13.NQCatSLkDual
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.NQCat.NNParab

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique

section Core

variable {k : ℕ}

theorem core (hk : k = 4 ∨ k = 5) {m : ℕ} (hm : m = 3 ∨ m = 4)
    {P D : Subgroup (SpecialLinearGroup (Fin k) (ZMod 2))}
    (hBP : upperTriangular k (ZMod 2) ≤ P) (hDP : D ≤ P)
    (hPD : P ≤ Subgroup.normalizer (D : Set (SpecialLinearGroup (Fin k) (ZMod 2))))
    (π : ↥D →* SpecialLinearGroup (Fin m) (ZMod 2)) (hπ : Function.Surjective π)
    (α : MulAut (SpecialLinearGroup (Fin k) (ZMod 2))) (hαP : P.map α.toMonoidHom = P)
    (hαD : ∀ d ∈ D, α d ∈ D) (hαD' : ∀ d, α d ∈ D → d ∈ D)
    (hni : ¬ ∃ z : SpecialLinearGroup (Fin m) (ZMod 2),
      ∀ d : ↥D, π ⟨α d, hαD d d.2⟩ = z * π d * z⁻¹) :
    (¬ ∃ x : SpecialLinearGroup (Fin k) (ZMod 2), ∀ y, α y = x * y * x⁻¹) ∧
      ((k = 5 ∧ m = 3) ∨ (k = 4 ∧ m = 4 ∧ P = ⊤)) := by
  have hcuts : ∀ A : Subgroup (SpecialLinearGroup (Fin k) (ZMod 2)),
      ∀ i ∈ borelOvergroupCuts A, 1 ≤ i ∧ i < k := fun A i ⟨hi, hik, _⟩ => ⟨hi, hik⟩
  have hout : ¬ ∃ x : SpecialLinearGroup (Fin k) (ZMod 2), ∀ y, α y = x * y * x⁻¹ := by
    rintro ⟨x, hx⟩
    set Q := P ⊔ Subgroup.zpowers x with hQ
    have hBQ : upperTriangular k (ZMod 2) ≤ Q := hBP.trans le_sup_left
    have hQeq := (borel_overgroups Q hBQ).1
    have hxN : x ∈ Subgroup.normalizer (D : Set (SpecialLinearGroup (Fin k) (ZMod 2))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [← hx]
      exact ⟨hαD h, hαD' h⟩
    have hQN : Q ≤ Subgroup.normalizer (D : Set (SpecialLinearGroup (Fin k) (ZMod 2))) :=
      sup_le hPD ((Subgroup.zpowers_le).2 hxN)
    have hDQ : D ≤ Q := hDP.trans le_sup_left
    rw [hQeq] at hQN hDQ
    obtain ⟨a, -, -, -, -, hinner⟩ :=
      SLk.exists_block hk (hcuts Q) hDQ hQN hm π hπ
    have hxQ : x ∈ flagStabilizer k (ZMod 2) (borelOvergroupCuts Q) :=
      hQeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    obtain ⟨z, hz⟩ := hinner x hxQ
    refine hni ⟨z, fun d => ?_⟩
    rw [← hz d]
    congr 1
    exact Subtype.ext (hx d)
  refine ⟨hout, ?_⟩
  have hPeq := (borel_overgroups P hBP).1
  set J := borelOvergroupCuts P with hJdef
  have hJ := hcuts P
  have hDQ : D ≤ flagStabilizer k (ZMod 2) J := hPeq ▸ hDP
  have hQN : flagStabilizer k (ZMod 2) J ≤
      Subgroup.normalizer (D : Set (SpecialLinearGroup (Fin k) (ZMod 2))) := hPeq ▸ hPD
  obtain ⟨a, ham, ha, ham', hJa, -⟩ := SLk.exists_block hk hJ hDQ hQN hm π hπ
  have hstab : ∀ i : ℕ, 1 ≤ i → i < k → k ≠ 2 * i → J = {i} → False := by
    intro i hi hik hk2 hJi
    apply hout
    refine SLk.inner_of_map_stabilizer (by omega) α hi hik hk2 ?_
    rw [← flagStabilizer_singleton, ← hJi, ← hPeq]
    exact hαP
  rcases hk with rfl | rfl <;> rcases hm with rfl | rfl
  ·
    exfalso
    have ha1 : a = 0 ∨ a = 1 := by omega
    rcases ha1 with rfl | rfl
    · refine hstab 3 (by norm_num) (by norm_num) (by norm_num) (Set.ext fun i => ?_)
      rw [Set.mem_singleton_iff]
      constructor
      · intro hi
        have := hJ i hi
        have := hJa i hi
        omega
      · rintro rfl
        rcases ham' with h | h
        · omega
        · exact h
    · refine hstab 1 (by norm_num) (by norm_num) (by norm_num) (Set.ext fun i => ?_)
      rw [Set.mem_singleton_iff]
      constructor
      · intro hi
        have := hJ i hi
        have := hJa i hi
        omega
      · rintro rfl
        rcases ha with h | h
        · omega
        · exact h
  ·
    refine Or.inr ⟨rfl, rfl, ?_⟩
    have hJe : J = ∅ := by
      ext i
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hi
      have := hJ i hi
      have := hJa i hi
      omega
    rw [hPeq, hJe, flagStabilizer_empty]
  ·
    exact Or.inl ⟨rfl, rfl⟩
  ·
    exfalso
    have ha1 : a = 0 ∨ a = 1 := by omega
    rcases ha1 with rfl | rfl
    · refine hstab 4 (by norm_num) (by norm_num) (by norm_num) (Set.ext fun i => ?_)
      rw [Set.mem_singleton_iff]
      constructor
      · intro hi
        have := hJ i hi
        have := hJa i hi
        omega
      · rintro rfl
        rcases ham' with h | h
        · omega
        · exact h
    · refine hstab 1 (by norm_num) (by norm_num) (by norm_num) (Set.ext fun i => ?_)
      rw [Set.mem_singleton_iff]
      constructor
      · intro hi
        have := hJ i hi
        have := hJa i hi
        omega
      · rintro rfl
        rcases ha with h | h
        · omega
        · exact h

end Core

section Main

theorem lem1211NNParab_holds : Lem1211NNParab := by
  intro Y _ _ X P D k m t hk hm hX hP _ hDP hPD π hπ _ htX htP htD hni
  obtain ⟨hPX, S, hS, hSP⟩ := hP
  have hDX : D ≤ X := hDP.trans hPX
  obtain ⟨e₀⟩ := hX
  let e : ↥X ≃* SpecialLinearGroup (Fin k) (ZMod 2) :=
    e₀.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL k (ZMod 2)).symm
  have hS' : IsSylowTwoOf ((S.subgroupOf X).map e.toMonoidHom) ⊤ := by
    have hU := Setup.X6.isSylowTwoOf_subgroupOf_top hS
    refine ⟨le_top, hU.2.1.map _, ?_⟩
    have h1 := hU.2.2
    rw [show ((S.subgroupOf X).subgroupOf ⊤).index = (S.subgroupOf X).index from
      Subgroup.relIndex_top_right _] at h1
    rw [show (((S.subgroupOf X).map e.toMonoidHom).subgroupOf ⊤).index =
        ((S.subgroupOf X).map e.toMonoidHom).index from Subgroup.relIndex_top_right _,
      MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact h1
  have hU : IsSylowTwoOf (unitriangular k (ZMod 2)) ⊤ :=
    SzN2.isSylowTwoOf_unitriangular (by omega)
  obtain ⟨g, -, hg⟩ := hS'.exists_conj hU
  let θ : ↥X ≃* SpecialLinearGroup (Fin k) (ZMod 2) := e.trans (MulAut.conj g)
  have hθS : (S.subgroupOf X).map θ.toMonoidHom = unitriangular k (ZMod 2) := by
    rw [hg, Subgroup.map_map]
    rfl
  let ct : ↥X ≃* ↥X :=
    { toFun := fun y => ⟨t * y * t⁻¹, (Subgroup.mem_normalizer_iff.mp htX y).mp y.2⟩
      invFun := fun y => ⟨t⁻¹ * y * t, by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem htX) y).mp y.2
        simpa using this⟩
      left_inv := fun y => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group)
      map_mul' := fun y z => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let α : MulAut (SpecialLinearGroup (Fin k) (ZMod 2)) := θ.symm.trans (ct.trans θ)
  have hα : ∀ y : ↥X, α (θ y) = θ (ct y) := fun y => by simp [α]
  set P' := (P.subgroupOf X).map θ.toMonoidHom with hP'
  set D' := (D.subgroupOf X).map θ.toMonoidHom with hD'
  have hBP' : upperTriangular k (ZMod 2) ≤ P' := by
    rw [← normalizer_unitriangular, ← hθS, ← Subgroup.map_equiv_normalizer_eq,
      ← Subgroup.subgroupOf_normalizer_eq hS.1]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hSP ⟨y.2, hy⟩, rfl⟩
  have hDP' : D' ≤ P' := Subgroup.map_mono fun y hy => hDP hy
  have hPD' : P' ≤ Subgroup.normalizer (D' : Set (SpecialLinearGroup (Fin k) (ZMod 2))) := by
    rw [hD', ← Subgroup.map_equiv_normalizer_eq, ← Subgroup.subgroupOf_normalizer_eq hDX]
    exact Subgroup.map_mono fun y hy => hPD hy
  have hct : ∀ {H : Subgroup Y}, t ∈ Subgroup.normalizer (H : Set Y) →
      ∀ y : ↥X, (y : Y) ∈ H ↔ ((ct y : ↥X) : Y) ∈ H := fun hH y =>
    Subgroup.mem_normalizer_iff.mp hH y
  have hαP : P'.map α.toMonoidHom = P' := by
    ext b
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨ct y, ?_, (hα y).symm⟩
      exact (hct htP y).1 hy
    · rintro ⟨y, hy, rfl⟩
      refine ⟨θ (ct.symm y), ⟨ct.symm y, ?_, rfl⟩, ?_⟩
      · show ((ct.symm y : ↥X) : Y) ∈ P
        rw [hct htP, MulEquiv.apply_symm_apply]
        exact hy
      · rw [MulEquiv.coe_toMonoidHom, hα, MulEquiv.apply_symm_apply]
        rfl
  have hαD : ∀ d ∈ D', α d ∈ D' := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hα]
    exact ⟨ct y, (hct htD y).1 hy, rfl⟩
  have hαD' : ∀ d, α d ∈ D' → d ∈ D' := by
    intro d hd
    obtain ⟨y, rfl⟩ := θ.surjective d
    rw [hα] at hd
    obtain ⟨y', hy', hyy'⟩ := hd
    have : y' = ct y := θ.injective hyy'
    subst this
    exact ⟨y, (hct htD y).2 hy', rfl⟩
  let ψ : ↥D ≃* ↥D' := (Subgroup.subgroupOfEquivOfLe hDX).symm.trans
    ((D.subgroupOf X).equivMapOfInjective θ.toMonoidHom θ.injective)
  have hψ : ∀ d : ↥D, ((ψ d : ↥D') : SpecialLinearGroup (Fin k) (ZMod 2)) = θ ⟨d, hDX d.2⟩ :=
    fun d => rfl
  let π' : ↥D' →* SpecialLinearGroup (Fin m) (ZMod 2) := π.comp ψ.symm.toMonoidHom
  have hπ' : Function.Surjective π' := hπ.comp ψ.symm.surjective
  have hni' : ¬ ∃ z : SpecialLinearGroup (Fin m) (ZMod 2),
      ∀ d : ↥D', π' ⟨α d, hαD d d.2⟩ = z * π' d * z⁻¹ := by
    rintro ⟨z, hz⟩
    refine hni ⟨z, fun d => ?_⟩
    have h1 := hz (ψ d)
    have h2 : (⟨α (ψ d), hαD _ (ψ d).2⟩ : ↥D') =
        ψ ⟨t * d * t⁻¹, (Subgroup.mem_normalizer_iff.mp htD d).mp d.2⟩ := by
      apply Subtype.ext
      show α ((ψ d : ↥D') : SpecialLinearGroup (Fin k) (ZMod 2)) =
        ((ψ ⟨t * d * t⁻¹, (Subgroup.mem_normalizer_iff.mp htD d).mp d.2⟩ : ↥D') :
          SpecialLinearGroup (Fin k) (ZMod 2))
      rw [hψ, hψ, hα]
      rfl
    have e1 : ∀ x : ↥D, π' (ψ x) = π x := fun x => by
      simp only [π', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rw [h2, e1, e1] at h1
    exact h1
  obtain ⟨hout, hcases⟩ := core hk hm hBP' hDP' hPD' π' hπ' α hαP hαD hαD' hni'
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl, htop⟩
  · refine Or.inl ⟨rfl, rfl, ?_⟩
    rintro ⟨x, hx, hxy⟩
    refine hout ⟨θ ⟨x, hx⟩, fun b => ?_⟩
    obtain ⟨y, rfl⟩ := θ.surjective b
    rw [hα, ← map_inv, ← map_mul, ← map_mul]
    refine congrArg θ (Subtype.ext ?_)
    show t * (y : Y) * t⁻¹ = x * (y : Y) * x⁻¹
    exact hxy y y.2
  · refine Or.inr ⟨rfl, rfl, le_antisymm hPX fun x hx => ?_⟩
    have h1 : θ ⟨x, hx⟩ ∈ P' := htop ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = ⟨x, hx⟩ := θ.injective hyx
    rw [this] at hy
    exact hy

end Main

end CFSG.Quasithin.H13.NQCat.NNParab
