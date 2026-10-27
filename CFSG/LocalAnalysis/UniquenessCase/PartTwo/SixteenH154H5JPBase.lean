module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

private theorem s16jp_comm_ident {V : Type} [CommGroup V] (p q s c : V) :
    (p * q * s⁻¹)⁻¹ * (q * s⁻¹ * c) = (p * c⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem s16jp_commSub_stable {L : Subgroup (MulAut W)} {Y : Subgroup W}
    (hY : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) :
    ∀ l ∈ L, ∀ y ∈ commSub Y L, l y ∈ commSub Y L := by
  intro l hl r hr
  induction hr using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hc
    refine Subgroup.subset_closure ⟨l * x * l⁻¹, L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl),
      l w, hY l hl w hw, ?_⟩
    simp [MulAut.mul_apply]
  | one => simpa using (commSub Y L).one_mem
  | mul a b ha hb iha ihb => simpa [map_mul] using (commSub Y L).mul_mem iha ihb
  | inv a ha ih => simpa [map_inv] using (commSub Y L).inv_mem ih

theorem s16jp_commSub_commSub {L : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L)
    {Y : Subgroup W} (hY : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) :
    commSub (commSub Y L) L = commSub Y L := by
  haveI : Group.IsPerfect ↥L := hperf
  apply le_antisymm
  · exact commSub_le_of_invariant fun l hl r hr => s16jp_commSub_stable hY l hl r hr
  · refine (Subgroup.closure_le (commSub (commSub Y L) L)).mpr ?_
    rintro _ ⟨x, hx, s, hs, rfl⟩
    set R := commSub Y L with hR
    set E := commSub R L with hE
    let Ψ : ↥L →* W ⧸ E :=
      { toFun := fun y => QuotientGroup.mk (((y : MulAut W) s) * s⁻¹)
        map_one' := by simp
        map_mul' := fun y z => by
          show (QuotientGroup.mk ((((y * z : ↥L)) : MulAut W) s * s⁻¹) : W ⧸ E) =
            QuotientGroup.mk (((y : MulAut W) s) * s⁻¹) *
              QuotientGroup.mk (((z : MulAut W) s) * s⁻¹)
          rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
          have hc : ((z : MulAut W) s * s⁻¹ : W) ∈ R :=
            Subgroup.subset_closure ⟨z, z.2, s, hs, rfl⟩
          have hgen : ((y : MulAut W) ((z : MulAut W) s * s⁻¹)) *
              ((z : MulAut W) s * s⁻¹)⁻¹ ∈ E :=
            Subgroup.subset_closure ⟨y, y.2, _, hc, rfl⟩
          have e0 : (((y * z : ↥L)) : MulAut W) s = (y : MulAut W) ((z : MulAut W) s) :=
            rfl
          have e1 : (((y * z : ↥L)) : MulAut W) s =
              (y : MulAut W) ((z : MulAut W) s * s⁻¹) * (y : MulAut W) s := by
            rw [e0, map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one]
          rw [e1, s16jp_comm_ident]
          exact E.inv_mem hgen }
    have hker : Ψ.ker = ⊤ := by
      have := Abelianization.commutator_subset_ker Ψ
      rw [Group.IsPerfect.commutator_eq_top] at this
      exact top_le_iff.mp this
    have h1 : Ψ ⟨x, hx⟩ = 1 := by
      have : (⟨x, hx⟩ : ↥L) ∈ Ψ.ker := hker ▸ Subgroup.mem_top _
      exact this
    exact (QuotientGroup.eq_one_iff _).mp h1

theorem s16jp_realizes_restrict_sub {D : FFModel} {H : Subgroup (MulAut W)}
    {I Z Y : Subgroup W} (hYI : Y ≤ I) (hY : ∀ h ∈ H, ∀ y ∈ Y, h y ∈ Y) (hYZ : Y ⊔ Z = I)
    (h : D.Realizes H I Z) : D.Realizes H Y (Z ⊓ Y) := by
  obtain ⟨π, hπs, hZI, hker, hI, hZinv, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  let β' : ↥Y →* ↥D.sec ⧸ D.ker.subgroupOf D.sec := β.comp (Subgroup.inclusion hYI)
  have hβ'coe : ∀ y : ↥Y, β' y = β (Subgroup.inclusion hYI y) := fun y => rfl
  refine ⟨π, hπs, inf_le_right, hker, ?_, ?_, hsec, hkerinv, β', ?_, ?_, ?_⟩
  · intro h u hu
    exact hY h h.2 u hu
  · intro h z hz
    exact ⟨hZinv h z hz.1, hY h h.2 z hz.2⟩
  · intro x
    obtain ⟨u, hu⟩ := hβs x
    have hmem : (u : W) ∈ Y ⊔ Z := by rw [hYZ]; exact u.2
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hmem
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [hβ'coe]
    have hz1 : β ⟨z, hZI hz⟩ = 1 := (hβk ⟨z, hZI hz⟩).mpr hz
    have hprod : u = Subgroup.inclusion hYI ⟨y, hy⟩ * ⟨z, hZI hz⟩ := by
      apply Subtype.ext
      simpa [Subgroup.coe_inclusion] using hyz.symm
    calc β (Subgroup.inclusion hYI ⟨y, hy⟩)
        = β (Subgroup.inclusion hYI ⟨y, hy⟩) * β ⟨z, hZI hz⟩ := by rw [hz1, mul_one]
      _ = β (Subgroup.inclusion hYI ⟨y, hy⟩ * ⟨z, hZI hz⟩) := (map_mul β _ _).symm
      _ = β u := by rw [hprod]
      _ = x := hu
  · intro u
    rw [hβ'coe, hβk (Subgroup.inclusion hYI u)]
    constructor
    · intro h1
      exact ⟨h1, u.2⟩
    · intro h1
      exact h1.1
  · intro γ u m hu hm hbu
    have hbu' : β (Subgroup.inclusion hYI u) = QuotientGroup.mk m := by
      simpa [hβ'coe] using hbu
    have h1 := hβe γ (Subgroup.inclusion hYI u) m (hYI hu) hm hbu'
    rw [hβ'coe]
    rw [show Subgroup.inclusion hYI (⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ : ↥Y) =
        (⟨((π γ : ↥H) : MulAut W) (u : W), hYI hu⟩ : ↥I) from rfl]
    exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
