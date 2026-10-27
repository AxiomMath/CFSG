module

public import CFSG.Quasithin.EmptyFaithful.SzC4S8DCard

public section

namespace CFSG.Quasithin.SzC4S8D

open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.SzC4S8C

section Centre

variable {G : Type} [Group G] {A V Z W : Subgroup G} {F : Type} [Field F] [Fintype F]
  {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)} {α : ↥A →* ↥Γ}

theorem conj_mem_centralizer_of_mem_normalizer {S : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (hc : c ∈ Subgroup.centralizer (S : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
  have key := hc _ hs'
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * s := by group

theorem conj_mem_centerOf_of_mem_normalizer {O : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (O : Set G)) (hc : c ∈ centerOf O) :
    g * c * g⁻¹ ∈ centerOf O :=
  ⟨(Subgroup.mem_normalizer_iff.mp hg c).mp hc.1, conj_mem_centralizer_of_mem_normalizer hg hc.2⟩

theorem centerOf_le_of_abelian (hF : Fintype.card F = 2)
    (h : IsSumOfNaturalModulesVia A V Z α true 2) (g : ↥A)
    (hg : moduleAct true (α g : Matrix.GeneralLinearGroup (Fin 3) F) = cmF hF)
    (hZc : Z ≤ centerOf V) (hZW : Z ≤ W) (hWV : W ≤ V)
    (hgW : ∀ x ∈ W, (g : G) * x * (g : G)⁻¹ ∈ W)
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hWc : ¬ W ≤ centerOf V) :
    centerOf V ≤ Z := by
  set R := centerOf V with hR
  have hRV : R ≤ V := inf_le_left
  have hgR : ∀ x ∈ R, (g : G) * x * (g : G)⁻¹ ∈ R := fun x hx =>
    conj_mem_centerOf_of_mem_normalizer (h.1 g.2) hx
  have hRcomm : ∀ r ∈ R, ∀ v ∈ V, r * v = v * r := fun r hr v hv =>
    (Subgroup.mem_centralizer_iff.mp hr.2 v hv).symm
  have hV64 := relIndex_dual_two_top hF h
  have hmul := Subgroup.relIndex_mul_relIndex Z R V hZc hRV
  rw [hV64] at hmul
  rcases relIndex_dual_two hF h g hg hRV hgR with h1 | h8 | h64
  · exact Subgroup.relIndex_eq_one.mp h1
  · exfalso
    rw [h8] at hmul
    have hSR : R ≤ W ⊔ R := le_sup_right
    have hZS : Z ≤ W ⊔ R := hZW.trans le_sup_left
    have hSV : W ⊔ R ≤ V := sup_le hWV hRV
    have hgS : ∀ x ∈ W ⊔ R, (g : G) * x * (g : G)⁻¹ ∈ W ⊔ R := by
      have hle : W ⊔ R ≤ Subgroup.comap (MulAut.conj (g : G)).toMonoidHom (W ⊔ R) :=
        sup_le (fun x hx => Subgroup.mem_sup_left (hgW x hx))
          (fun x hx => Subgroup.mem_sup_right (hgR x hx))
      exact fun x hx => hle hx
    have hmulS := Subgroup.relIndex_mul_relIndex Z (W ⊔ R) V hZS hSV
    have hmulRS := Subgroup.relIndex_mul_relIndex Z R (W ⊔ R) hZc hSR
    rw [hV64] at hmulS
    rw [h8] at hmulRS
    rcases relIndex_dual_two hF h g hg hSV hgS with s1 | s8 | s64
    · omega
    · have hRS : R.relIndex (W ⊔ R) = 1 := by omega
      exact hWc (le_sup_left.trans (Subgroup.relIndex_eq_one.mp hRS))
    · rw [s64] at hmulS
      have hSV1 : (W ⊔ R).relIndex V = 1 := by omega
      have hVS : V ≤ W ⊔ R := Subgroup.relIndex_eq_one.mp hSV1
      have ha : ∀ w ∈ W, W ⊔ R ≤ Subgroup.centralizer ({w} : Set G) := by
        intro w hw
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hWab w hw x hx
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact (hRcomm x hx w (hWV hw)).symm
      have hb : ∀ s ∈ W ⊔ R, W ⊔ R ≤ Subgroup.centralizer ({s} : Set G) := by
        intro s hs
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          have := Subgroup.mem_centralizer_iff.mp (ha x hx hs) x (Set.mem_singleton x)
          exact this.symm
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact (hRcomm x hx s (hSV hs)).symm
      have hVR : V ≤ R := fun u hu =>
        ⟨hu, Subgroup.mem_centralizer_iff.mpr fun v hv => by
          have := Subgroup.mem_centralizer_iff.mp (hb u (hVS hu) (hVS hv)) u (Set.mem_singleton u)
          exact this.symm⟩
      have hRV1 : R.relIndex V = 1 := Subgroup.relIndex_eq_one.mpr hVR
      omega
  · exfalso
    rw [h64] at hmul
    have hRV1 : R.relIndex V = 1 := by omega
    exact hWc (hWV.trans (Subgroup.relIndex_eq_one.mp hRV1))

end Centre

end CFSG.Quasithin.SzC4S8D
