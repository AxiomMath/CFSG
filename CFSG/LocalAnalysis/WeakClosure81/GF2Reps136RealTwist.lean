module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem realizes_twist (D : FFModel) {L : Subgroup (MulAut W)} {U Z : Subgroup W} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) (h : D.Realizes L U Z) :
    D.Realizes L (U.map g.toMonoidHom) (Z.map g.toMonoidHom) := by
  obtain ⟨π, hπ⟩ := h
  have hconj : ∀ x : MulAut W, x ∈ L → g * x * g⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hconjinv : ∀ x : MulAut W, x ∈ L → g⁻¹ * x * g ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
  let π' : D.Gam →* ↥L :=
    { toFun := fun γ => ⟨g * (π γ : MulAut W) * g⁻¹, hconj _ (π γ).2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hπ'val : ∀ γ : D.Gam, ((π' γ : ↥L) : MulAut W) = g * (π γ : MulAut W) * g⁻¹ :=
    fun γ => rfl
  refine ⟨π', ?_⟩
  obtain ⟨hπs, hZU, hkersec, hUinv, hZinv, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hπ
  refine ⟨?_, Subgroup.map_mono hZU, hkersec, ?_, ?_, hsec, hkerinv, ?_⟩
  · intro x
    have hxg : g⁻¹ * (x : MulAut W) * g ∈ L := hconjinv _ x.2
    obtain ⟨γ, hγ⟩ := hπs ⟨g⁻¹ * (x : MulAut W) * g, hxg⟩
    exact ⟨γ, by ext; rw [hπ'val, congrArg Subtype.val hγ]; group⟩
  · intro h u hu
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
    exact Subgroup.mem_map.2 ⟨(g⁻¹ * (h : MulAut W) * g) u',
      hUinv ⟨g⁻¹ * (h : MulAut W) * g, hconjinv _ h.2⟩ u' hu',
      by simp [MulAut.mul_apply]⟩
  · intro h z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
    exact Subgroup.mem_map.2 ⟨(g⁻¹ * (h : MulAut W) * g) z',
      hZinv ⟨g⁻¹ * (h : MulAut W) * g, hconjinv _ h.2⟩ z' hz',
      by simp [MulAut.mul_apply]⟩
  · have hpre : ∀ x : ↥(U.map g.toMonoidHom), g⁻¹ (x : W) ∈ U := by
      intro x
      obtain ⟨u, hu, hx⟩ := Subgroup.mem_map.1 x.2
      rw [← hx]; simpa using hu
    let β' : ↥(U.map g.toMonoidHom) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
      { toFun := fun x => β ⟨g⁻¹ (x : W), hpre x⟩
        map_one' := by
          change β (⟨g⁻¹ (1 : W), hpre 1⟩ : ↥U) = 1
          rw [show (⟨g⁻¹ (1 : W), hpre 1⟩ : ↥U) = 1 from Subtype.ext (by simp)]
          exact map_one β
        map_mul' := fun x y => by
          change β (⟨g⁻¹ ((x : W) * (y : W)), hpre (x * y)⟩ : ↥U) =
            β (⟨g⁻¹ (x : W), hpre x⟩ : ↥U) * β (⟨g⁻¹ (y : W), hpre y⟩ : ↥U)
          rw [← map_mul]
          congr 1
          ext
          simp [map_mul] }
    refine ⟨β', ?_, ?_, ?_⟩
    · intro q
      obtain ⟨u, hu⟩ := hβs q
      refine ⟨⟨g (u : W), Subgroup.mem_map.2 ⟨u, u.2, rfl⟩⟩, ?_⟩
      have hβval : β' ⟨g (u : W), Subgroup.mem_map.2 ⟨u, u.2, rfl⟩⟩ =
          β (⟨g⁻¹ (g (u : W)),
            hpre ⟨g (u : W), Subgroup.mem_map.2 ⟨u, u.2, rfl⟩⟩⟩ : ↥U) := rfl
      rw [hβval]
      have hval : (⟨g⁻¹ (g (u : W)),
          hpre ⟨g (u : W), Subgroup.mem_map.2 ⟨u, u.2, rfl⟩⟩⟩ : ↥U) = u :=
        Subtype.ext (by simp)
      rw [hval]
      exact hu
    · intro x
      have hβval : β' x = β (⟨g⁻¹ (x : W), hpre x⟩ : ↥U) := rfl
      rw [hβval, hβk]
      constructor
      · intro hz
        exact Subgroup.mem_map.2 ⟨g⁻¹ (x : W), hz, by simp⟩
      · intro hx
        change g⁻¹ (x : W) ∈ Z
        obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx
        rw [show g⁻¹ (x : W) = z by rw [← hzx]; simp]
        exact hz
    · intro γ x m hu hm hβx
      have hpre' : ((π γ : ↥L) : MulAut W) (g⁻¹ (x : W)) ∈ U := by
        have hx' : g⁻¹ (((π' γ : ↥L) : MulAut W) (x : W)) ∈ U :=
          hpre ⟨((π' γ : ↥L) : MulAut W) (x : W), hu⟩
        rw [hπ'val γ] at hx'
        simpa [MulAut.mul_apply] using hx'
      have hβx' : β (⟨g⁻¹ (x : W), hpre x⟩ : ↥U) = QuotientGroup.mk m := hβx
      have h1 := hβe γ (⟨g⁻¹ (x : W), hpre x⟩ : ↥U) m hpre' hm hβx'
      have hβval : β' (⟨((π' γ : ↥L) : MulAut W) (x : W), hu⟩ :
            ↥(U.map g.toMonoidHom)) =
          β (⟨g⁻¹ (((π' γ : ↥L) : MulAut W) (x : W)),
            hpre ⟨((π' γ : ↥L) : MulAut W) (x : W), hu⟩⟩ : ↥U) := rfl
      have hβeq : β (⟨g⁻¹ (((π' γ : ↥L) : MulAut W) (x : W)),
            hpre ⟨((π' γ : ↥L) : MulAut W) (x : W), hu⟩⟩ : ↥U) =
          β (⟨((π γ : ↥L) : MulAut W) (g⁻¹ (x : W)), hpre'⟩ : ↥U) := by
        apply congrArg β
        apply Subtype.ext
        change g⁻¹ (((π' γ : ↥L) : MulAut W) (x : W)) =
          ((π γ : ↥L) : MulAut W) (g⁻¹ (x : W))
        rw [hπ'val γ]
        simp [MulAut.mul_apply]
      rw [hβval, hβeq]
      exact h1

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
