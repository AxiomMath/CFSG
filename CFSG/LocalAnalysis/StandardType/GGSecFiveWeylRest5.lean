module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyFourDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Pure

variable {G : Type} [Group G] [Finite G]

theorem card_le_pow_mul_card_of_weylOfType {p : ℕ} {Bs : Subgroup G} {ι : Type} [Fintype ι]
    {M : CoxeterMatrix ι} {A : Subgroup (MulAut ↥Bs)} (hW : GGWeylOfType p M A)
    (F₀ : Subgroup ↥Bs) (hfix : ∀ b : ↥Bs, (∀ ψ ∈ A, ψ b = b) → b ∈ F₀) :
    Nat.card Bs ≤ p ^ Fintype.card ι * Nat.card F₀ := by
  obtain ⟨e, he⟩ := hW
  let φ : ι → MulAut ↥Bs := fun i => ((e (M.simple i) : ↥A) : MulAut ↥Bs)
  let F : ι → Subgroup ↥Bs := fun i =>
    { carrier := {b | φ i b = b}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        exact map_one (φ i)
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  let I : Subgroup ↥Bs := ⨅ i, F i
  have hFcard : ∀ i, Nat.card (F i) * p = Nat.card ↥Bs := fun i => (he i).2
  have hFpos : ∀ i, 0 < Nat.card (F i) := fun i => by
    haveI : Nonempty ↥(F i) := ⟨⟨1, by simp [F]⟩⟩
    exact Nat.card_pos
  have hindex : ∀ i, (F i).index = p := fun i => by
    have h1 : Nat.card (F i) * (F i).index = Nat.card ↥Bs := Subgroup.card_mul_index (F i)
    exact Nat.mul_left_cancel (hFpos i) (by rw [h1, hFcard i])
  have hsub : I ≤ F₀ := by
    intro b hb
    refine hfix b ?_
    let f : M.Group →* MulAut ↥Bs := A.subtype.comp e.toMonoidHom
    have hbfix : ∀ i, φ i b = b := fun i => by
      simpa [F] using Subgroup.mem_iInf.mp hb i
    have hHsimple : ∀ i, M.simple i ∈
        (MulAction.stabilizer (MulAut ↥Bs) b).comap f := by
      intro i
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
      simpa [f, MulAut.smul_def] using hbfix i
    have htop : (MulAction.stabilizer (MulAut ↥Bs) b).comap f = ⊤ := by
      rw [eq_top_iff, ← M.toCoxeterSystem.subgroup_closure_range_simple]
      exact (Subgroup.closure_le _).mpr (by rintro x ⟨i, rfl⟩; exact hHsimple i)
    intro ψ hψ
    have hmem : e.symm ⟨ψ, hψ⟩ ∈ (MulAction.stabilizer (MulAut ↥Bs) b).comap f := by
      rw [htop]; exact Subgroup.mem_top _
    have hfixb : f (e.symm ⟨ψ, hψ⟩) • b = b :=
      MulAction.mem_stabilizer_iff.mp (Subgroup.mem_comap.mp hmem)
    simpa [f, MulAut.smul_def] using hfixb
  calc Nat.card Bs = Nat.card I * I.index :=
        (Subgroup.card_mul_index I).symm
    _ ≤ Nat.card F₀ * ∏ i, (F i).index :=
        Nat.mul_le_mul (Subgroup.card_le_of_le hsub) (Subgroup.index_iInf_le F)
    _ = Nat.card F₀ * p ^ Fintype.card ι := by
        rw [Finset.prod_congr rfl (fun i _ => hindex i), Finset.prod_const, Finset.card_univ]
    _ = p ^ Fintype.card ι * Nat.card F₀ := Nat.mul_comm _ _

theorem ggConfig_bstar_facts {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) :
    p.Prime ∧ IsElemAbelian p Bs ∧ x ∈ Bs ∧ p ^ 4 ≤ Nat.card Bs := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  refine ⟨hp, hcfg.2.1.2.1, hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1, ?_⟩
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
    _ = Nat.card B := hBc.symm
    _ ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1

theorem card_le_of_le_zpowers {p : ℕ} (hp : p.Prime) {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    {x : G} (hx : x ∈ Bs) (F₀ : Subgroup ↥Bs) (hF₀ : ∀ b ∈ F₀, (b : G) ∈ Subgroup.zpowers x) :
    Nat.card F₀ ≤ p := by
  have hxp : x ^ p = 1 := hBs.2 x hx
  have hcard : Nat.card (Subgroup.zpowers x) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hxp
  let f : F₀ → Subgroup.zpowers x := fun b => ⟨(b : G), hF₀ b b.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    show ((a : ↥Bs) : G) = ((b : ↥Bs) : G)
    exact congrArg (fun z : Subgroup.zpowers x => (z : G)) hab
  exact (Nat.card_le_card_of_injective f hf).trans hcard

end Pure

section Input

@[expose] def GGSecFiveWeylRest5 : Prop :=
  GGSecFiveWeylAInput ∧ GGSecFiveWeylBRestInput ∧ GGSecFiveWeylDInput ∧ GGSecFiveWeylEInput ∧
    GGSecFiveWeylF4Input

theorem ggSecFiveWeylG2Input_of_tbfix (hT : GGTBFixInput) : GGSecFiveWeylG2Input := by
  intro G _ _ p B Bs x L D J hR hWC hAt
  obtain ⟨y, K, hnbr, hW⟩ := hAt
  exfalso
  obtain ⟨hp, hBs, hxBs, h4⟩ := ggConfig_bstar_facts hR.1
  have hfix := hT G p B Bs x L D J hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 y K hnbr
    (hWC y K hnbr) (Or.inr hWC)
  let F₀ : Subgroup ↥Bs := (Subgroup.zpowers x).subgroupOf Bs
  have h1 : Nat.card Bs ≤ p ^ 2 * Nat.card F₀ := by
    have h := card_le_pow_mul_card_of_weylOfType hW F₀
      (fun b hb => hfix b (fun φ hφ => hb φ (Subgroup.mem_sup_left hφ)))
    simpa [Fintype.card_fin] using h
  have h2 : Nat.card F₀ ≤ p := by
    refine card_le_of_le_zpowers hp hBs hxBs F₀ (fun b hb => ?_)
    exact Subgroup.mem_subgroupOf.mp hb
  have h3 : Nat.card Bs ≤ p ^ 3 := by
    calc Nat.card Bs ≤ p ^ 2 * Nat.card F₀ := h1
      _ ≤ p ^ 2 * p := Nat.mul_le_mul_left _ h2
      _ = p ^ 3 := by ring
  exact absurd (h4.trans h3)
    (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 3 < 4)))

theorem ggSecFiveWeylRest4_of_rest5 (h : GGSecFiveWeylRest5) (hT : GGTBFixInput) :
    GGSecFiveWeylRest4 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, ggSecFiveWeylG2Input_of_tbfix hT⟩

end Input

end CFSG.StandardType

end
