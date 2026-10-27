module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Defs
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAAct

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem map_cenS_mulEquiv (φ : G ≃* G') (S : Subgroup G) :
    (CenS S).map φ.toMonoidHom = CenS (S.map φ.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h _ hs
    obtain ⟨s, hs', rfl⟩ := Subgroup.mem_map.mp hs
    have := congrArg φ (h s hs')
    simpa using this
  · intro h s hs
    apply φ.injective
    simpa using h (φ s) (Subgroup.mem_map_of_mem _ hs)

theorem map_cen_mulEquiv (φ : G ≃* G') (x : G) :
    (Cen x).map φ.toMonoidHom = Cen (φ x) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg φ h
    simpa using this
  · intro h
    apply φ.injective
    simpa using h

theorem map_nor_mulEquiv (φ : G ≃* G') (S : Subgroup G) :
    (Nor S).map φ.toMonoidHom = Nor (S.map φ.toMonoidHom) := by
  exact Subgroup.map_equiv_normalizer_eq S φ

theorem mem_layer_quot_iff {A B : Type*} [Group A] [Group B] (e : A ≃* B) (x : A) :
    ((x : A ⧸ pPrimeCore 3 A) ∈ layer (A ⧸ pPrimeCore 3 A)) ↔
      (((e x : B) : B ⧸ pPrimeCore 3 B) ∈ layer (B ⧸ pPrimeCore 3 B)) := by
  let q : (A ⧸ pPrimeCore 3 A) ≃* (B ⧸ pPrimeCore 3 B) :=
    QuotientGroup.congr _ _ e (pPrimeCore_map_iso 3 e)
  have hq : q (x : A ⧸ pPrimeCore 3 A) = ((e x : B) : B ⧸ pPrimeCore 3 B) := rfl
  rw [← hq]
  have h := WholeGroup.layer_map_mulEquiv q
  constructor
  · intro hx
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hx
  · intro hx
    rw [← h] at hx
    exact (Subgroup.mem_map_iff_mem q.injective).mp hx

theorem map_oppE_mulEquiv (φ : G ≃* G') (S : Subgroup G) :
    (OppE 3 S).map φ.toMonoidHom = OppE 3 (S.map φ.toMonoidHom) := by
  ext y
  obtain ⟨x, rfl⟩ := φ.surjective y
  have e1 : φ x ∈ (OppE 3 S).map φ.toMonoidHom ↔ x ∈ OppE 3 S :=
    Subgroup.mem_map_iff_mem φ.injective
  rw [e1, mem_OppE, mem_OppE]
  constructor
  · rintro ⟨h, hx⟩
    refine ⟨Subgroup.mem_map_of_mem _ h, ?_⟩
    exact (mem_layer_quot_iff (φ.subgroupMap S) ⟨x, h⟩).mp hx
  · rintro ⟨h, hx⟩
    refine ⟨(Subgroup.mem_map_iff_mem φ.injective).mp h, ?_⟩
    exact (mem_layer_quot_iff (φ.subgroupMap S)
      ⟨x, (Subgroup.mem_map_iff_mem φ.injective).mp h⟩).mpr hx

theorem map_oUpp_group (p : ℕ) {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.normalClosure {g : A | ∃ k : ℕ, g ^ (p ^ k) = 1}).map e.toMonoidHom =
      Subgroup.normalClosure {g : B | ∃ k : ℕ, g ^ (p ^ k) = 1} := by
  rw [Subgroup.map_normalClosure _ _ e.surjective]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hk, map_one]⟩
  · rintro ⟨k, hk⟩
    refine ⟨e.symm y, ⟨k, ?_⟩, by simp⟩
    apply e.injective
    rw [map_pow, map_one, MulEquiv.apply_symm_apply, hk]

theorem map_oUpp_mulEquiv (p : ℕ) (φ : G ≃* G') (S : Subgroup G) :
    (OUpp p S).map φ.toMonoidHom = OUpp p (S.map φ.toMonoidHom) := by
  unfold OUpp inSubgroup
  have h : ((Subgroup.normalClosure {g : S | ∃ k : ℕ, g ^ (p ^ k) = 1}).map S.subtype).map
      φ.toMonoidHom = ((Subgroup.normalClosure {g : S | ∃ k : ℕ, g ^ (p ^ k) = 1}).map
        (S.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom).map
          (S.map φ.toMonoidHom).subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [h, map_oUpp_group p (S.equivMapOfInjective φ.toMonoidHom φ.injective)]

theorem isLnq_map_mulEquiv (φ : G ≃* G') {n p f : ℕ} {S : Subgroup G} (h : IsLnq n p f S) :
    IsLnq n p f (S.map φ.toMonoidHom) :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv (φ.subgroupMap S) h

noncomputable def layerQuotEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    ↥(layer (A ⧸ pPrimeCore 3 A)) ≃* ↥(layer (B ⧸ pPrimeCore 3 B)) :=
  let q : (A ⧸ pPrimeCore 3 A) ≃* (B ⧸ pPrimeCore 3 B) :=
    QuotientGroup.congr _ _ e (pPrimeCore_map_iso 3 e)
  (q.subgroupMap (layer _)).trans (MulEquiv.subgroupCongr (WholeGroup.layer_map_mulEquiv q))

theorem isLnq_layerQuot {N N' : Type} [Group N] [Group N'] (e : N ≃* N') {n p f : ℕ}
    (h : IsLnq n p f (⊤ : Subgroup ↥(layer (N ⧸ pPrimeCore 3 N)))) :
    IsLnq n p f (⊤ : Subgroup ↥(layer (N' ⧸ pPrimeCore 3 N'))) :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
    (((Subgroup.topEquiv (G := ↥(layer (N ⧸ pPrimeCore 3 N)))).trans
      (layerQuotEquiv e)).trans (Subgroup.topEquiv (G := ↥(layer (N' ⧸ pPrimeCore 3 N')))).symm)
    h

end Transport

section Main

variable {G : Type} [Group G]

theorem sec35_conj_oppE (g : G) (U : Subgroup G) :
    conjBy g (OppE 3 (CenS U)) = OppE 3 (CenS (conjBy g U)) := by
  have h1 := map_oppE_mulEquiv (MulAut.conj g) (CenS U)
  rw [map_cenS_mulEquiv (MulAut.conj g) U] at h1
  exact h1

theorem sec35_conj_P {b g : G} (hg : g ∈ Cen b) {U : Subgroup G} (hP : FF79Sec35P b U) :
    FF79Sec35P b (conjBy g U) := by
  obtain ⟨⟨hE, hc⟩, hb, hL, hK⟩ := hP
  let φ : G ≃* G := MulAut.conj g
  have hφb : φ b = b := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    show g * b * g⁻¹ = b
    rw [this]
    group
  have hcen : (Cen b).map φ.toMonoidHom = Cen b := by
    rw [map_cen_mulEquiv, hφb]
  have hCS : (CenS U).map φ.toMonoidHom = CenS (conjBy g U) := map_cenS_mulEquiv φ U
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · haveI := hE
    exact IsElementaryAbelian.map φ.toMonoidHom
  · rw [show conjBy g U = U.map φ.toMonoidHom from rfl,
      Subgroup.card_map_of_injective φ.injective, hc]
  · have h : φ b ∈ (Nor U).map φ.toMonoidHom := Subgroup.mem_map_of_mem _ hb
    rw [map_nor_mulEquiv, hφb] at h
    exact h
  · exact isLnq_layerQuot ((φ.subgroupMap (CenS U)).trans (MulEquiv.subgroupCongr hCS)) hL
  · have h1 := isLnq_map_mulEquiv φ hK
    have h2 : (OUpp 2 (OppE 3 (CenS U) ⊓ Cen b)).map φ.toMonoidHom =
        OUpp 2 (OppE 3 (CenS (conjBy g U)) ⊓ Cen b) := by
      rw [map_oUpp_mulEquiv, Subgroup.map_inf_eq _ _ _ φ.injective, map_oppE_mulEquiv, hCS, hcen]
    rw [h2] at h1
    exact h1

end Main

end CFSG.RankThree.PartTwo.Sec21.FF79
