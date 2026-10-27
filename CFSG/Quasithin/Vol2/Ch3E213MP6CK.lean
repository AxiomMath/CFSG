module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CJ
public import CFSG.Quasithin.Vol2.Ch3E213MP6A
public import CFSG.Quasithin.Vol2.Ch3E213MP6AC
public import CFSG.Quasithin.Vol2.Ch3E213MP6CG
public import CFSG.Quasithin.Vol2.Ch3E213MP6CH

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6 CFSG.Timmesfeld
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat uElt antiUnipotent antiUnipotentCenter antiSp_ext uMat_inj glMat_uElt minorAut)
open CFSG.Quasithin.SteinbergBS (rootLong rootShort)

variable {G : Type} [Group G] [Finite G]

theorem exists_sp4Member_of_subfieldSp
    {H T M V K : Subgroup G}
    (hS : Setting H T M V K) (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)))
    {k : Type} [Field k] [Finite k] [CharP k 2] (D : Sp4Data H T M V K k)
    {F₀ : Subfield k} {c g : antiSp k} (hc : IsUpper c)
    (hgY : g ∈ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom)
    (hY : coordIn D.θ V ⊔ (coordIn D.θ V).map (MulAut.conj g).toMonoidHom =
      (subfieldSp F₀).map (MulAut.conj c).toMonoidHom) :
    ∃ g' : G, Sp4Member H T M V g' ↥F₀ := by
  set Y := (subfieldSp F₀).map (MulAut.conj c).toMonoidHom with hYdef
  set eY : ↥Y ≃* antiSp ↥F₀ := ((subfieldSp F₀).equivMapOfInjective _
    (MulAut.conj c).injective).symm.trans (subfieldSpEquiv F₀).symm with heY
  have hexact : OddCoverExact ↥Y := oddCoverExact_of_mulEquiv_antiSp eY
  obtain ⟨g', hg', hpair, hc2, hne, hker, ⟨φ, hφs, hφk⟩, hVB⟩ :=
    exists_coord_member hS hB D hgY hY (isSylowOf_inf_antiUnipotent hc)
      (kerIn_inf_normalizer_eq_bot hc) (pCore_eq_bot hc) (pCore_inf_normalizer hc) hexact
  have hWle : coordIn D.θ V ≤ Y ⊓ antiUnipotentCenter k :=
    le_inf (hY ▸ le_sup_left) D.V_le_center
  have hWcard : Nat.card (coordIn D.θ V) ≤ Nat.card F₀ ^ 2 :=
    (Subgroup.card_le_of_le hWle).trans (card_inf_center_le hc)
  refine ⟨g', hg', hpair, hc2, hne, hker, ⟨eY.toMonoidHom.comp φ, eY.surjective.comp hφs, ?_⟩,
    hVB.trans hWcard⟩
  have hk : (eY.toMonoidHom.comp φ).ker = φ.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  rw [hk, hφk]

theorem uElt_long_eq_one {k : Type} [Field k] [CharP k 2] {t : k}
    (h : (uElt 0 0 t 0 : antiSp k) = 1) : t = 0 := by
  have h1 := congrArg (fun x : antiSp k => glMat (x : GL (Fin 4) k) 0 3) h
  simpa [glMat_uElt, CFSG.ComponentClassification.UnbalancedCatalog.SpChain.uMat] using h1

theorem exists_sp4Member_of_transv
    (hIrr : IrrStatement) (hG41 : FactSp4TransvW)
    {H T M V K : Subgroup G} (hS : Setting H T M V K)
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)))
    {k : Type} [Field k] [Finite k] [CharP k 2] {n : ℕ} (hk : Nat.card k = 2 ^ n)
    (D : Sp4Data H T M V K k) (hl : coordIn D.θ V ⊓ rootLong k ≠ ⊥) :
    ∃ (g : G) (F₀ : Subfield k), Sp4Member H T M V g ↥F₀ := by
  obtain ⟨⟨x, hxW, t, rfl⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hl
  have ht : t ≠ 0 := by
    rintro rfl
    apply hx1
    apply Subtype.ext
    exact CFSG.QuasithinUnique.Setup.X7b.uElt_zero_eq_one
  obtain ⟨-, -, h, j, -, -, -, -, hsw⟩ := D.swap
  have h1 : (MulAut.conj h * minorAut k ^ j) (uElt 0 0 t 0) ∈
      coordIn D.θ V ⊓ rootShort k := by
    rw [← hsw]
    exact ⟨_, ⟨hxW, t, rfl⟩, rfl⟩
  obtain ⟨b, hb⟩ := h1.2
  have hbne : b ≠ 0 := by
    rintro rfl
    have h2 : (MulAut.conj h * minorAut k ^ j) (uElt 0 0 t 0) =
        (MulAut.conj h * minorAut k ^ j) 1 := by
      rw [hb, map_one]
      exact CFSG.QuasithinUnique.Setup.X7b.uElt_zero_eq_one
    exact ht (uElt_long_eq_one ((MulAut.conj h * minorAut k ^ j).injective h2))
  have hsb : uElt 0 b 0 0 ∈ coordIn D.θ V := hb ▸ h1.1
  have hsp : SpansCenter (coordIn D.θ V) := by
    intro α β hαβ hWl
    obtain ⟨τ, hτ⟩ := hWl hxW
    obtain ⟨τ', hτ'⟩ := hWl hsb
    have e1 := uMat_inj (congrArg (fun y : antiSp k => glMat (y : GL (Fin 4) k)) hτ)
    have e2 := uMat_inj (congrArg (fun y : antiSp k => glMat (y : GL (Fin 4) k)) hτ')
    have hτ0 : τ ≠ 0 := by
      rintro rfl
      exact ht (by simpa using e1.2.2.1)
    have hτ'0 : τ' ≠ 0 := by
      rintro rfl
      exact hbne (by simpa using e2.2.1)
    have hβ : β = 0 := (mul_eq_zero.1 e1.2.1.symm).resolve_left hτ0
    have hα : α = 0 := (mul_eq_zero.1 e2.2.2.1.symm).resolve_left hτ'0
    rcases hαβ with h | h
    · exact h hα
    · exact h hβ
  obtain ⟨F₀, c, g, hc, hgY, hY⟩ :=
    exists_subfieldSp_member hIrr hG41 hk D.V_le_center hsp ht hbne hxW hsb
  obtain ⟨g', hg'⟩ := exists_sp4Member_of_subfieldSp hS hB D hc hgY hY
  exact ⟨g', F₀, hg'⟩

theorem pkgSp4Transv
    (hIrr : IrrStatement) (hG41 : FactSp4TransvW) :
    PkgSp4Transv := by
  intro G _ _ H T M V K hS _ _ hB k _ _ _ n _ hk D hl
  obtain ⟨g, F₀, hg⟩ := exists_sp4Member_of_transv hIrr hG41 hS hB hk D hl
  exact e213Concl_of_sp4Member hg

end CFSG.Quasithin.Ch3E213M
