module

public import CFSG.Quasithin.MS93.S468Red
public import CFSG.Quasithin.MS93.S46R468Pt

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix Pointwise

section Count

variable {𝔾 : Type*} [Group 𝔾]

theorem relIndex_le_card_of_commutator_mem {A Q P : Subgroup 𝔾} [Finite ↥P] {y : 𝔾}
    (hQy : ∀ q ∈ Q, q * y = y * q) (hAP : ∀ a ∈ A, ⁅y, a⁆ ∈ P)
    (hAQ : ∀ a ∈ A, a * y = y * a → a ∈ Q) : Q.relIndex A ≤ Nat.card ↥P := by
  have hwd : ∀ a b : ↥A, (a : 𝔾)⁻¹ * b ∈ Q → ⁅y, (a : 𝔾)⁆ = ⁅y, (b : 𝔾)⁆ := by
    intro a b hab
    have hc : ((a : 𝔾)⁻¹ * b) * y⁻¹ = y⁻¹ * ((a : 𝔾)⁻¹ * b) :=
      (Commute.inv_right (hQy _ hab)).eq
    have key : ⁅y, (a : 𝔾) * ((a : 𝔾)⁻¹ * b)⁆ = ⁅y, (a : 𝔾)⁆ := by
      calc ⁅y, (a : 𝔾) * ((a : 𝔾)⁻¹ * b)⁆
          = y * a * (((a : 𝔾)⁻¹ * b) * y⁻¹) * ((a : 𝔾)⁻¹ * b)⁻¹ * (a : 𝔾)⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = y * a * (y⁻¹ * ((a : 𝔾)⁻¹ * b)) * ((a : 𝔾)⁻¹ * b)⁻¹ * (a : 𝔾)⁻¹ := by rw [hc]
        _ = ⁅y, (a : 𝔾)⁆ := by simp only [commutatorElement_def]; group
    rw [← key, mul_inv_cancel_left]
  have hconj : ∀ c : 𝔾, c * y * c⁻¹ = (y⁻¹ * ⁅y, c⁆)⁻¹ := fun c => by
    simp only [commutatorElement_def]; group
  let f : ↥A ⧸ Q.subgroupOf A → ↥P :=
    Quotient.lift (fun a : ↥A => (⟨⁅y, (a : 𝔾)⁆, hAP a a.2⟩ : ↥P)) fun a b hab =>
      Subtype.ext (hwd a b (by
        have := QuotientGroup.leftRel_apply.mp hab
        rwa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at this))
  have hf : Function.Injective f := by
    intro qa qb hab
    induction qa using QuotientGroup.induction_on with
    | H a =>
      induction qb using QuotientGroup.induction_on with
      | H b =>
        have h1 : ⁅y, (a : 𝔾)⁆ = ⁅y, (b : 𝔾)⁆ := congrArg Subtype.val hab
        have h2 : (a : 𝔾) * y * (a : 𝔾)⁻¹ = (b : 𝔾) * y * (b : 𝔾)⁻¹ := by
          rw [hconj, hconj, h1]
        have h3 : ((b : 𝔾)⁻¹ * a) * y = y * ((b : 𝔾)⁻¹ * a) := by
          calc ((b : 𝔾)⁻¹ * a) * y = (b : 𝔾)⁻¹ * ((a : 𝔾) * y * (a : 𝔾)⁻¹) * a := by group
            _ = (b : 𝔾)⁻¹ * ((b : 𝔾) * y * (b : 𝔾)⁻¹) * a := by rw [h2]
            _ = y * ((b : 𝔾)⁻¹ * a) := by group
        have h4 : (b : 𝔾)⁻¹ * a ∈ Q := hAQ _ (A.mul_mem (A.inv_mem b.2) a.2) h3
        refine QuotientGroup.eq.2 ?_
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
        have h5 := Q.inv_mem h4
        rwa [mul_inv_rev, inv_inv] at h5
  exact Nat.card_le_card_of_injective f hf

end Count

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem card_of_isPtOn (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) : Nat.card ↥P = Fintype.card F := by
  obtain ⟨β', hxβ', hne, rfl⟩ := hP
  exact card_usup_inf_usup h464 h465 c hx hxβ hxβ' (Ne.symm hne)

theorem relIndex_qv_le_of_commutator_mem (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {x ρ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxρ : (puAmalgam c.pu.le).treeGraph.Adj x ρ) {P A : Subgroup (puAmalgam c.pu.le).Universal}
    [Finite ↥P] (hA : A ≤ Qv (puAmalgam c.pu.le) ρ)
    (hAP : ∀ a ∈ A, ∀ z ∈ ZM (puAmalgam c.pu.le) x, ⁅z, a⁆ ∈ P) :
    (Qv (puAmalgam c.pu.le) x).relIndex A ≤ Nat.card ↥P := by
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  obtain ⟨y, hy, hyρ⟩ : ∃ y ∈ ZM (puAmalgam c.pu.le) x, y ∉ ZH (puAmalgam c.pu.le) ρ := by
    by_contra hno
    have h1 : (ZH (puAmalgam c.pu.le) ρ).relIndex (ZM _ x) = 1 :=
      Subgroup.relIndex_eq_one.mpr fun y hy => by_contra fun hn => hno ⟨y, hy, hn⟩
    have h2 := (h465 G M T L F φ c x ρ hx hxρ).2.1
    have : 2 ≤ Fintype.card F := Fintype.one_lt_card
    omega
  refine relIndex_le_card_of_commutator_mem (y := y) (fun q hq => ?_) (fun a ha => hAP a ha y hy)
    fun a ha hay => mem_qv_of_commute c.pu c.via h464' hsq h466 hx hxρ hy hyρ (hA ha) hay
  exact Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ c.pu.hyp20 hx hy) q hq

theorem ptQ_le_normalizer_qv (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x ℓ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hPℓ : P ≤ Usup (puAmalgam c.pu.le) x ℓ) :
    ptQ (puAmalgam c.pu.le) x P ≤
      Subgroup.normalizer (Qv (puAmalgam c.pu.le) ℓ : Set (puAmalgam c.pu.le).Universal) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.pu c.via hx
  intro g hg
  have hgs : g ∈ stab (puAmalgam c.pu.le) x := (mem_ptQ.mp hg).1
  refine I466b.mem_normalizer_qv_of_toSL3 c.pu c.via h464' hsq h466 hx hxℓ hψ (g := ⟨g, hgs⟩)
    fun p hp => ?_
  obtain ⟨u, rfl⟩ := natVec_surjective hψ p
  have hm := mem_usup_iff c.pu c.via h464' hsq hx hxℓ hψ
  have hmem : ⁅(u : (puAmalgam c.pu.le).Universal), g⁆ ∈ Uloc c.pu.le L x :=
    S468.commutator_mem_uloc c.pu hψ u ⟨g, hgs⟩
  have hcP : ⁅(u : (puAmalgam c.pu.le).Universal), g⁆ ∈ P :=
    (mem_ptQ.mp hg).2.2 u (uloc_le_zm c.pu hfull hx u.2)
  have hc := (hm ⟨_, hmem⟩).mp (hPℓ hcP)
  rw [natVec_commutator hψ ⟨g, hgs⟩ u ⟨_, hmem⟩ rfl] at hc
  have e : ((toSL3 ψ ⟨g, hgs⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ u =
      natVec hψ u - (natVec hψ u -
        ((toSL3 ψ ⟨g, hgs⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ u) := by abel
  rw [e]
  exact Submodule.sub_mem _ hp hc

theorem ptQ_le_normalizer_vv (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x ℓ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hPℓ : P ≤ Usup (puAmalgam c.pu.le) x ℓ) :
    ptQ (puAmalgam c.pu.le) x P ≤
      Subgroup.normalizer (Vv (puAmalgam c.pu.le) ℓ : Set (puAmalgam c.pu.le).Universal) :=
  (ptQ_le_normalizer_qv h464 h465 h466a c hx hxℓ hPℓ).trans
    (normalizer_qv_le_normalizer_vv c.pu ((isMVtx_iff_of_adj _ hxℓ).mp hx))

theorem qv_inf_qv_le_qv (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x ρ ρ' : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxρ : (puAmalgam c.pu.le).treeGraph.Adj x ρ) (hxρ' : (puAmalgam c.pu.le).treeGraph.Adj x ρ')
    (hne : Usup (puAmalgam c.pu.le) x ρ ≠ Usup _ x ρ') :
    Qv (puAmalgam c.pu.le) ρ ⊓ Qv _ ρ' ≤ Qv _ x := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.pu c.via hx
  have hW2 := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxρ hψ).1
  have hW'2 := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxρ' hψ).1
  have hne' : fixN (natImage ψ (Qv (puAmalgam c.pu.le) ρ)) ≠ fixN (natImage ψ (Qv _ ρ')) :=
    fun heq => hne ((S45.eq_iff_of_natVec_iff hψ (usup_le_uloc' c.pu hfull hx hxρ)
      (usup_le_uloc' c.pu hfull hx hxρ') (mem_usup_iff c.pu c.via h464' hsq hx hxρ hψ)
      (mem_usup_iff c.pu c.via h464' hsq hx hxρ' hψ)).mpr heq)
  obtain ⟨v, hv', hv⟩ : ∃ v ∈ fixN (natImage ψ (Qv (puAmalgam c.pu.le) ρ')),
      v ∉ fixN (natImage ψ (Qv (puAmalgam c.pu.le) ρ)) := by
    by_contra hno
    refine hne' (Submodule.eq_of_le_of_finrank_eq (fun v hv => ?_) (by rw [hW2, hW'2])).symm
    by_contra hvW
    exact hno ⟨v, hv, hvW⟩
  intro t ht
  have hts : t ∈ stab (puAmalgam c.pu.le) x := qv_le_stab_of_adj _ hxρ.symm ht.1
  have hA : toSL3 ψ ⟨t, hts⟩ ∈ I466b.axisGroup (fixN (natImage ψ (Qv (puAmalgam c.pu.le) ρ))) := by
    rw [← I466b.natImage_qv_eq_axisGroup c.pu c.via h464' hsq h466 hx hxρ hψ]
    exact mem_natImage.mpr ⟨_, ht.1, rfl⟩
  have hA' : toSL3 ψ ⟨t, hts⟩ ∈
      I466b.axisGroup (fixN (natImage ψ (Qv (puAmalgam c.pu.le) ρ'))) := by
    rw [← I466b.natImage_qv_eq_axisGroup c.pu c.via h464' hsq h466 hx hxρ' hψ]
    exact mem_natImage.mpr ⟨_, ht.2, rfl⟩
  exact (toSL3_eq_one_iff_mem_qv c.pu c.via hx hψ _).mp
    (eq_one_of_mem_axisGroup hW2 hA hv (hA'.1 v hv'))

end CFSG.Quasithin.MS93.S46R
