module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAut
public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum

public section

namespace CFSG.Quasithin.H13.Sec53F.BA

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

variable {Y : Type} [Group Y]

theorem conj_mem_autStab {P : Subgroup Y} {p : Y} (hp : p ∈ P) :
    (MulAut.conj p : MulAut Y) ∈ autStab P := fun x => by
  rw [MulAut.conj_apply]
  constructor
  · intro hx
    exact P.mul_mem (P.mul_mem hp hx) (P.inv_mem hp)
  · intro hx
    have := P.mul_mem (P.mul_mem (P.inv_mem hp) hx) hp
    simpa [mul_assoc] using this

theorem map_conj_le_N1 (A : LieAmalgamExt Y) :
    A.P1.map (MulAut.conj : Y →* MulAut Y) ≤ A.N1 := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨A.inn_le ⟨p, rfl⟩, conj_mem_autStab hp⟩

theorem perfectCore_map_inj {Y' : Type} [Group Y'] (Φ : Y →* Y') (hΦ : Function.Injective Φ)
    (X : Subgroup Y) : perfectCore (X.map Φ) = (perfectCore X).map Φ := by
  unfold perfectCore
  rw [Subgroup.map_iInf Φ hΦ]
  congr 1
  funext n
  exact (map_derivedSeriesOf Φ X n).symm

omit [Group Y] in
theorem comm_conj_aut' {Y' : Type} [Group Y'] (φ : MulAut Y') (g h : Y') :
    MulAut.conj h * (MulAut.conj g * φ) * (MulAut.conj h)⁻¹ * (MulAut.conj g * φ)⁻¹ =
      MulAut.conj (h * g * (φ h)⁻¹ * g⁻¹) := by
  have e1 : MulAut.conj h * (MulAut.conj g * φ) * (MulAut.conj h)⁻¹ * (MulAut.conj g * φ)⁻¹ =
      MulAut.conj h * MulAut.conj g * (φ * (MulAut.conj h)⁻¹ * φ⁻¹) * (MulAut.conj g)⁻¹ := by
    group
  have e2 : φ * (MulAut.conj h)⁻¹ * φ⁻¹ = MulAut.conj (φ h)⁻¹ := by
    have h1 : φ * MulAut.conj h⁻¹ * φ⁻¹ = MulAut.conj (φ h⁻¹) := by
      ext z
      simp [MulAut.mul_apply]
    rw [← map_inv (MulAut.conj : Y' →* MulAut Y') h, h1, map_inv φ h]
  rw [e1, e2]
  simp only [map_mul, map_inv]


theorem lieAut_of_borelAutData [Finite Y] {U H : Subgroup Y} {F : Subgroup (MulAut Y)}
    (D : BorelAutData U H F) (A : LieAmalgamExt Y) (hTD : A.TD = U)
    (hP : A.P1 ⊓ A.P2 ≤ Subgroup.normalizer (U : Set Y)) (hUP : U ≤ perfectCore A.P1) :
    Group.IsSolvable ↥(A.N1 ⊓ A.N2) ∧ pCoreOf 2 (A.N1 ⊓ A.N2) ≤ perfectCore A.N1 := by
  have hBP1 : Subgroup.normalizer (U : Set Y) ≤ A.P1 := by
    rw [← hTD]
    exact ((A.yam.2.2 A.P1).mpr (Or.inl rfl)).2
  have hBP2 : Subgroup.normalizer (U : Set Y) ≤ A.P2 := by
    rw [← hTD]
    exact ((A.yam.2.2 A.P2).mpr (Or.inr rfl)).2
  have hB : A.P1 ⊓ A.P2 = Subgroup.normalizer (U : Set Y) :=
    le_antisymm hP (le_inf hBP1 hBP2)
  have hBβ : ∀ β ∈ A.N1 ⊓ A.N2, ∀ x, β x ∈ Subgroup.normalizer (U : Set Y) ↔
      x ∈ Subgroup.normalizer (U : Set Y) := by
    intro β hβ x
    rw [← hB, Subgroup.mem_inf, Subgroup.mem_inf]
    have h1 := hβ.1.2 x
    have h2 := hβ.2.2 x
    constructor
    · rintro ⟨a, b⟩
      exact ⟨h1.mpr a, h2.mpr b⟩
    · rintro ⟨a, b⟩
      exact ⟨h1.mp a, h2.mp b⟩
  have hUp : IsPGroup 2 ↥U := D.sylow.2.1
  have hstab : ∀ β ∈ A.N1 ⊓ A.N2, ∀ x, β x ∈ U ↔ x ∈ U := by
    intro β hβ x
    constructor
    · intro hx
      have hxB' : x ∈ Subgroup.normalizer (U : Set Y) :=
        (hBβ β hβ x).mp (Subgroup.le_normalizer hx)
      obtain ⟨a, ha⟩ := hUp ⟨β x, hx⟩
      have h1 : (β x) ^ 2 ^ a = 1 := congrArg Subtype.val ha
      have h2 : x ^ 2 ^ a = 1 := by
        apply β.injective
        rw [map_pow, map_one]
        exact h1
      exact D.mem_U_of_pow x hxB' h2
    · intro hx
      have hxB := (hBβ β hβ x).mpr (Subgroup.le_normalizer hx)
      obtain ⟨a, ha⟩ := hUp ⟨x, hx⟩
      have h1 : x ^ 2 ^ a = 1 := congrArg Subtype.val ha
      have h2 : (β x) ^ 2 ^ a = 1 := by rw [← map_pow, h1, map_one]
      exact D.mem_U_of_pow (β x) hxB h2
  have hnf : ∀ β ∈ A.N1 ⊓ A.N2, ∃ g ∈ Subgroup.normalizer (U : Set Y), ∃ σ ∈ F,
      β = MulAut.conj g * σ := fun β hβ => D.normal_form β (hstab β hβ)
  have hinj := D.conj_injective
  have hconjσ : ∀ σ : MulAut Y, ∀ g : Y, σ * MulAut.conj g * σ⁻¹ = MulAut.conj (σ g) := by
    intro σ g
    ext z
    simp [MulAut.mul_apply, MulAut.conj_apply]
  set inn : Subgroup (MulAut Y) :=
    (Subgroup.normalizer (U : Set Y)).map (MulAut.conj : Y →* MulAut Y) with hinn
  have hBs : Group.IsSolvable ↥(Subgroup.normalizer (U : Set Y)) := D.isSolvable_B
  have hinnS : Group.IsSolvable ↥inn :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective (Subgroup.normalizer (U : Set Y)) _
        hinj).symm.toMonoidHom)
      (Subgroup.equivMapOfInjective (Subgroup.normalizer (U : Set Y)) _ hinj).symm.injective
  have hFs : Group.IsSolvable ↥F :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (D.F_comm a a.2 b b.2)
  have hFn : F ≤ Subgroup.normalizer (inn : Set (MulAut Y)) := by
    intro σ hσ
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [hconjσ]
      exact ⟨σ g, (D.F_B σ hσ g).mpr hg, rfl⟩
    · rintro ⟨g, hg, hga⟩
      have hae : a = σ⁻¹ * MulAut.conj g * σ⁻¹⁻¹ := by
        rw [hga]
        group
      rw [hae, hconjσ]
      exact ⟨σ⁻¹ g, (D.F_B σ⁻¹ (F.inv_mem hσ) g).mpr hg, rfl⟩
  have hW : Group.IsSolvable ↥(inn ⊔ F) := A3.isSolvable_sup_of_le_normalizer hFn
  have hle : A.N1 ⊓ A.N2 ≤ inn ⊔ F := by
    intro β hβ
    obtain ⟨g, hg, σ, hσ, rfl⟩ := hnf β hβ
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨g, hg, rfl⟩) (Subgroup.mem_sup_right hσ)
  refine ⟨Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle), ?_⟩
  have hRn : A.N1 ⊓ A.N2 ≤ Subgroup.normalizer (pCoreOf 2 (A.N1 ⊓ A.N2) : Set (MulAut Y)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hR2 : IsPGroup 2 (pCoreOf 2 (A.N1 ⊓ A.N2)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  intro β hβR
  have hβN : β ∈ A.N1 ⊓ A.N2 := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hβR
  obtain ⟨g, hg, σ, hσ, hβσ⟩ := hnf β hβN
  obtain ⟨b, hb⟩ := hR2 ⟨β, hβR⟩
  have hβb : β ^ 2 ^ b = 1 := congrArg Subtype.val hb
  have hσ1 : σ = 1 := by
    apply D.F_faithful σ hσ
    intro h hh
    have hhB : h ∈ Subgroup.normalizer (U : Set Y) := D.H_le hh
    have hc : (MulAut.conj h : MulAut Y) ∈ A.N1 ⊓ A.N2 :=
      ⟨⟨A.inn_le ⟨h, rfl⟩, conj_mem_autStab (hBP1 hhB)⟩,
        ⟨A.inn_le ⟨h, rfl⟩, conj_mem_autStab (hBP2 hhB)⟩⟩
    have hγ : MulAut.conj h * β * (MulAut.conj h)⁻¹ * β⁻¹ ∈ pCoreOf 2 (A.N1 ⊓ A.N2) := by
      have := (Subgroup.mem_normalizer_iff.mp (hRn hc) β).mp hβR
      exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ hβR)
    rw [hβσ, comm_conj_aut'] at hγ
    obtain ⟨a, ha⟩ := hR2 ⟨_, hγ⟩
    have hxa : (h * g * (σ h)⁻¹ * g⁻¹) ^ 2 ^ a = 1 := by
      apply hinj
      rw [map_pow, map_one]
      exact congrArg Subtype.val ha
    have hσh : σ h ∈ H := D.F_H σ hσ h hh
    have hx : h * g * (σ h)⁻¹ * g⁻¹ ∈ Subgroup.normalizer (U : Set Y) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hhB hg)
        (Subgroup.inv_mem _ (D.H_le hσh))) (Subgroup.inv_mem _ hg)
    have hxU := D.mem_U_of_pow _ hx hxa
    set π := QuotientGroup.mk' (U.subgroupOf (Subgroup.normalizer (U : Set Y))) with hπ
    have e1 : π ⟨_, hx⟩ = 1 := (BorelAutData.mk_eq_one_iff U _).mpr hxU
    have e2 : (⟨h * g * (σ h)⁻¹ * g⁻¹, hx⟩ : ↥(Subgroup.normalizer (U : Set Y))) =
        ⟨h, hhB⟩ * ⟨g, hg⟩ * ⟨σ h, D.H_le hσh⟩⁻¹ * ⟨g, hg⟩⁻¹ := rfl
    rw [e2, map_mul, map_mul, map_mul, map_inv, map_inv] at e1
    have e3 : π ⟨h, hhB⟩ * (π ⟨σ h, D.H_le hσh⟩)⁻¹ = 1 := by
      have : π ⟨h, hhB⟩ * π ⟨g, hg⟩ * (π ⟨σ h, D.H_le hσh⟩)⁻¹ * (π ⟨g, hg⟩)⁻¹ =
          π ⟨h, hhB⟩ * (π ⟨σ h, D.H_le hσh⟩)⁻¹ := by
        rw [mul_assoc (π ⟨h, hhB⟩), D.quot_comm (π ⟨g, hg⟩) (π ⟨σ h, D.H_le hσh⟩)⁻¹,
          ← mul_assoc, mul_assoc (π ⟨h, hhB⟩ * _), mul_inv_cancel, mul_one]
      rw [← this]
      exact e1
    have e4 := mul_inv_eq_one.mp e3
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at e4
    have hU1 : h⁻¹ * σ h ∈ U := e4
    have := D.U_inf_H _ hU1 (H.mul_mem (H.inv_mem hh) hσh)
    exact (inv_mul_eq_one.mp this).symm
  rw [hσ1, mul_one] at hβσ
  rw [hβσ] at hβb
  have hgb : g ^ 2 ^ b = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact hβb
  have hgU : g ∈ U := D.mem_U_of_pow g hg hgb
  have hmem : β ∈ (perfectCore A.P1).map (MulAut.conj : Y →* MulAut Y) :=
    ⟨g, hUP hgU, hβσ.symm⟩
  rw [← perfectCore_map_inj (MulAut.conj : Y →* MulAut Y) hinj A.P1] at hmem
  exact perfectCore_mono (map_conj_le_N1 A) hmem

end CFSG.Quasithin.H13.Sec53F.BA
