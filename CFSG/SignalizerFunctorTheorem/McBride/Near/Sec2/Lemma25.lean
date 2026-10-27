module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.GlaubermanUniv
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ]

section Auxiliary

omit [Finite Γ] in
private theorem admits_cenIn {A G : Subgroup Γ} [IsMulCommutative A] (hAG : Admits A G)
    {S : Set Γ} (hS : S ⊆ A) : Admits A (cenIn G S) := by
  rw [Admits, Subgroup.le_normalizer_iff]
  intro a ha k hk
  obtain ⟨hkG, hkS⟩ := Subgroup.mem_inf.mp hk
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hAG ha) k).mp hkG
  · rw [Subgroup.mem_centralizer_iff] at hkS ⊢
    intro s hs
    have hsa : Commute s a := setLike_mul_comm (hS hs) ha
    have hsk : Commute s k := hkS s hs
    exact (hsa.mul_right hsk).mul_right hsa.inv_right

omit [Finite Γ] in
private theorem isMulCommutative_of_le {X Y : Subgroup Γ} [IsMulCommutative Y] (h : X ≤ Y) :
    IsMulCommutative X :=
  .of_setLike_mul_comm fun _ ha _ hb => setLike_mul_comm (h ha) (h hb)

omit [Finite Γ] in
private theorem isMulCommutative_sup {X Y : Subgroup Γ} [IsMulCommutative X] [IsMulCommutative Y]
    (h : X ≤ Subgroup.centralizer (Y : Set Γ)) : IsMulCommutative ↥(X ⊔ Y) := by
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  have hYX : Y ≤ Subgroup.centralizer (X : Set Γ) := Subgroup.le_centralizer_iff.mpr h
  refine sup_le ?_ ?_
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer X) hYX
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le h (Subgroup.le_centralizer Y)

private theorem exists_ne_one_mem_inf_hyperplanes {p : ℕ} (hp : p.Prime) {A B₁ B₂ : Subgroup Γ}
    (hrank : p ^ 3 ≤ Nat.card A) (h₁ : B₁ ∈ Coprime.hyperplanes p A)
    (h₂ : B₂ ∈ Coprime.hyperplanes p A) : ∃ c ∈ B₁ ⊓ B₂, c ≠ 1 := by
  have hrel : ∀ B ∈ Coprime.hyperplanes p A, B.relIndex A = p := by
    intro B hB
    have h1 := Subgroup.relIndex_mul_card (H := B) (K := A)
    rw [inf_of_le_left hB.1, hB.2] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  by_contra hcon
  push Not at hcon
  have hbot : B₁ ⊓ B₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
  have h3 := Subgroup.relIndex_mul_card (H := B₁ ⊓ B₂) (K := A)
  have h4 := Subgroup.relIndex_inf_le (H := B₁) (K := B₂) (L := A)
  rw [hrel B₁ h₁, hrel B₂ h₂] at h4
  have hbotA : B₁ ⊓ B₂ ⊓ A = ⊥ := by rw [hbot]; simp
  rw [hbotA, Subgroup.card_bot, mul_one] at h3
  have h5 : p ^ 3 ≤ p * p := hrank.trans (h3 ▸ h4)
  have hp2 := hp.two_le
  nlinarith [Nat.mul_le_mul_right (p * p) hp2]

omit [Finite Γ] in
private theorem admits_commutator {A G : Subgroup Γ} (hAG : Admits A G) : Admits A ⁅G, G⁆ := by
  intro a ha
  have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAG ha)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator, h]

omit [Finite Γ] in
private theorem admits_sup {A X Y : Subgroup Γ} (hX : Admits A X) (hY : Admits A Y) :
    Admits A (X ⊔ Y) :=
  (le_inf hX hY).trans (Subgroup.inf_normalizer_le_normalizer_sup X Y)

omit [Finite Γ] in
private theorem commutator_ne_self {G : Subgroup Γ} [Group.IsSolvable G] (hG : G ≠ ⊥) :
    ⁅G, G⁆ ≠ G := by
  intro h
  have : Nontrivial G := (Subgroup.nontrivial_iff_ne_bot G).mpr hG
  refine (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne ?_
  apply Subgroup.map_injective G.subtype_injective
  rw [Subgroup.map_subtype_commutator, h, Subgroup.map_top, G.range_subtype]

private theorem isSolvable_of_centralizers {p : ℕ} (hp : p.Prime) {A G : Subgroup Γ}
    (hA : IsElemAbelian p A) (hrank : p ^ 3 ≤ Nat.card A) (hAG : Admits A G)
    (hcop : Nat.Coprime p (Nat.card G))
    (habel : ∀ a ∈ A, a ≠ 1 → IsMulCommutative (cenIn G {a} : Subgroup Γ)) :
    Group.IsSolvable G := by
  have := hA.1
  have hθ : IsSolvableSignalizerFunctor p A (fun a => cenIn G {a}) :=
    { le_centralizer := fun a _ _ => inf_le_right
      coprime := fun a _ _ => hcop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      invariant := fun a ha _ x hx => Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (admits_cenIn hAG (Set.singleton_subset_iff.mpr ha) hx)
      balance := fun a _ _ b _ _ x hx => ⟨hx.1.1, hx.2⟩
      solvable := fun a ha ha1 => by have := habel a ha ha1; infer_instance }
  obtain ⟨-, hsol, -⟩ := glauberman_solvable_signalizer_functor_univ p hp A hA.1 hA.2
    (pow_dvd_card_of_isElemAbelian hp hA hrank) (fun a => cenIn G {a}) hθ
  have hrank2 : p ^ 2 ≤ Nat.card A := (Nat.pow_le_pow_right hp.pos (by norm_num)).trans hrank
  have hW : (⨆ (a : Γ) (_ : a ∈ A) (_ : a ≠ 1), cenIn G {a}) = G :=
    iSup_centralizer_nonidentity hp hA hrank2 hAG hcop
  rwa [hW] at hsol

private theorem isMulCommutative_aux {p : ℕ} (hp : p.Prime) {A : Subgroup Γ}
    (hA : IsElemAbelian p A) (hrank : p ^ 3 ≤ Nat.card A) :
    ∀ (n : ℕ) (G : Subgroup Γ), Nat.card G = n → Admits A G → Nat.Coprime p (Nat.card G) →
      (∀ a ∈ A, a ≠ 1 → IsMulCommutative (cenIn G {a} : Subgroup Γ)) →
        IsMulCommutative G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn hAG hcop habel
  have := hA.1
  have hpA : p ≤ Nat.card A := (Nat.le_self_pow (by norm_num) p).trans hrank
  by_cases hG : G = ⊥
  · rw [hG]
    infer_instance
  have hsol : Group.IsSolvable G := isSolvable_of_centralizers hp hA hrank hAG hcop habel
  let S : Set (Subgroup Γ) := {N | N ≤ G ∧ N ≠ G ∧ ⁅G, G⁆ ≤ N ∧ Admits A N}
  have hmemS : ⁅G, G⁆ ∈ S :=
    ⟨Subgroup.commutator_le_self G, commutator_ne_self hG, le_rfl, admits_commutator hAG⟩
  obtain ⟨M, hMS, hMmax⟩ :=
    Set.exists_max_image S (fun N => Nat.card N) (Set.toFinite S) ⟨_, hmemS⟩
  obtain ⟨hMG, hMne, hcommM, hAM⟩ := hMS
  have hMlt : Nat.card M < n := by
    rw [← hn]
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hMG) fun h => hMne ?_
    exact Subgroup.eq_of_le_of_card_ge hMG h.ge
  have hcopM : Nat.Coprime p (Nat.card M) :=
    hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hMG)
  have habelM : ∀ a ∈ A, a ≠ 1 → IsMulCommutative (cenIn M {a} : Subgroup Γ) := by
    intro a ha ha1
    have := habel a ha ha1
    exact isMulCommutative_of_le (X := cenIn M {a}) (Y := cenIn G {a})
      (inf_le_inf_right _ hMG)
  have hMabel : IsMulCommutative M := ih _ hMlt M rfl hAM hcopM habelM
  obtain ⟨A₀, hA₀, hnot⟩ : ∃ A₀ ∈ Coprime.hyperplanes p A,
      ¬ (G ⊓ Subgroup.centralizer (A₀ : Set Γ)) ≤ M := by
    by_contra hcon
    push Not at hcon
    refine hMne (le_antisymm hMG ?_)
    rw [← iSup_centralizer_hyperplanes hp hA hpA hAG hcop]
    exact iSup₂_le fun B hB => hcon B hB
  have hAX : Admits A (G ⊓ Subgroup.centralizer (A₀ : Set Γ)) :=
    admits_cenIn hAG (SetLike.coe_subset_coe.mpr hA₀.1)
  have hXabel : IsMulCommutative ↥(G ⊓ Subgroup.centralizer (A₀ : Set Γ)) := by
    obtain ⟨c, hc, hc1⟩ := exists_ne_one_mem_inf_hyperplanes hp hrank hA₀ hA₀
    have hcA₀ : c ∈ A₀ := (Subgroup.mem_inf.mp hc).1
    have := habel c (hA₀.1 hcA₀) hc1
    exact isMulCommutative_of_le (X := G ⊓ Subgroup.centralizer (A₀ : Set Γ)) (Y := cenIn G {c})
      (inf_le_inf_left G (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA₀)))
  have hXM : G ⊓ Subgroup.centralizer (A₀ : Set Γ) ≤ Subgroup.centralizer (M : Set Γ) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hM : M ≤ Subgroup.centralizer ({x} : Set Γ) := by
      rw [← iSup_centralizer_hyperplanes hp hA hpA hAM hcopM]
      refine iSup₂_le fun B hB => ?_
      obtain ⟨c, hc, hc1⟩ := exists_ne_one_mem_inf_hyperplanes hp hrank hA₀ hB
      obtain ⟨hcA₀, hcB⟩ := Subgroup.mem_inf.mp hc
      have := habel c (hA₀.1 hcA₀) hc1
      intro y hy
      obtain ⟨hyM, hyB⟩ := Subgroup.mem_inf.mp hy
      have hxc : x ∈ cenIn G {c} := Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_inf.mp hx).1, Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 c hcA₀).symm⟩
      have hyc : y ∈ cenIn G {c} := Subgroup.mem_inf.mpr
        ⟨hMG hyM, Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hyB c hcB).symm⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (setLike_mul_comm hyc hxc)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hM hm)
  have hjoin : (G ⊓ Subgroup.centralizer (A₀ : Set Γ)) ⊔ M = G := by
    by_contra hne
    have hN : (G ⊓ Subgroup.centralizer (A₀ : Set Γ)) ⊔ M ∈ S :=
      ⟨sup_le inf_le_left hMG, hne, hcommM.trans le_sup_right, admits_sup hAX hAM⟩
    have heq : M = (G ⊓ Subgroup.centralizer (A₀ : Set Γ)) ⊔ M :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (hMmax _ hN)
    exact hnot (le_sup_left.trans heq.symm.le)
  have := isMulCommutative_sup hXM
  rwa [hjoin] at this

end Auxiliary

theorem isMulCommutative_of_centralizers {p : ℕ} (hp : p.Prime) {A G : Subgroup Γ}
    (hA : IsElemAbelian p A) (hrank : p ^ 3 ≤ Nat.card A) (hAG : Admits A G)
    (hcop : Nat.Coprime p (Nat.card G))
    (habel : ∀ a ∈ A, a ≠ 1 → IsMulCommutative (cenIn G {a} : Subgroup Γ)) :
    IsMulCommutative G :=
  isMulCommutative_aux hp hA hrank _ G rfl hAG hcop habel

end CFSG.SignalizerFunctorTheorem.McBride.Near
