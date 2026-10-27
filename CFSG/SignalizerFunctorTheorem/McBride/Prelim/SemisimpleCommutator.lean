module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable (simpleComponents)
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

private theorem not_map_conj_le_centralizer {J M : Subgroup G} {m : G} (hm : m ∈ M)
    (hJ : ¬ J ≤ Subgroup.centralizer (M : Set G)) :
    ¬ J.map (MulAut.conj m).toMonoidHom ≤ Subgroup.centralizer (M : Set G) := by
  intro hle
  refine hJ fun x hx => Subgroup.mem_centralizer_iff.mpr fun n hn => ?_
  have h1 := Subgroup.mem_centralizer_iff.mp (hle ⟨x, hx, rfl⟩) (m * n * m⁻¹)
    (mul_mem (mul_mem hm hn) (inv_mem hm))
  have h2 : m * (n * x) * m⁻¹ = m * (x * n) * m⁻¹ :=
    calc m * (n * x) * m⁻¹ = m * n * m⁻¹ * (m * x * m⁻¹) := by group
      _ = m * x * m⁻¹ * (m * n * m⁻¹) := h1
      _ = m * (x * n) * m⁻¹ := by group
  simpa using h2

private theorem le_of_inf_ne_bot_of_le_normalizer {J N : Subgroup G} [IsSimpleGroup J]
    (hJN : J ≤ Subgroup.normalizer (N : Set G)) (hne : J ⊓ N ≠ ⊥) : J ≤ N := by
  have hD : ((J ⊓ N).subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro u v hu hv
    obtain ⟨huJ, huN⟩ := Subgroup.mem_inf.mp hu
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hv huJ) (inv_mem hv),
      (Subgroup.mem_normalizer_iff.mp (hJN hv) u).mp huN⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((J ⊓ N).subgroupOf J) with h | h
  · refine absurd (eq_bot_iff.mpr fun x hx => ?_) hne
    have hx' : (⟨x, (Subgroup.mem_inf.mp hx).1⟩ : J) ∈ (J ⊓ N).subgroupOf J := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · intro x hx
    have hmem : (⟨x, hx⟩ : J) ∈ (J ⊓ N).subgroupOf J := by rw [h]; trivial
    exact (Subgroup.mem_inf.mp hmem).2

private theorem commutator_le_sSup_not_centralized [Finite G] {K M : Subgroup G}
    (hK : IsSemisimple K) (hM : M ≤ Subgroup.normalizer (K : Set G)) :
    ⁅K, M⁆ ≤ sSup {J | J ∈ lcal K ∧ ¬ J ≤ Subgroup.centralizer (M : Set G)} := by
  have hS : IsDirectProduct (lcal K) K := hK.isDirectProduct_lcal
  set S₁ : Set (Subgroup G) :=
    {J | J ∈ lcal K ∧ ¬ J ≤ Subgroup.centralizer (M : Set G)} with hS₁
  set S₂ : Set (Subgroup G) := {J | J ∈ lcal K ∧ J ≤ Subgroup.centralizer (M : Set G)} with hS₂
  have hsup : sSup S₁ ⊔ sSup S₂ = K := by
    rw [← sSup_union, ← hS.sSup_eq]
    congr 1
    ext J
    by_cases h : J ≤ Subgroup.centralizer (M : Set G) <;> simp [hS₁, hS₂, h]
  have hLJ : ∀ J ∈ S₁, ∀ L ∈ S₂, ∀ x ∈ J, ∀ y ∈ L, x * y = y * x := fun J hJ L hL x hx y hy =>
    (hS.commute J hJ.1 L hL.1 (fun h => hJ.2 (h ▸ hL.2)) x hx y hy).eq
  have hcomm : ∀ x ∈ sSup S₁, ∀ y ∈ sSup S₂, Commute x y := by
    intro x hx y hy
    have h2 : ∀ J ∈ S₁, sSup S₂ ≤ Subgroup.centralizer (J : Set G) := fun J hJ =>
      sSup_le fun L hL y hy =>
        Subgroup.mem_centralizer_iff.mpr fun x hx => hLJ J hJ L hL x hx y hy
    have h1 : sSup S₁ ≤ Subgroup.centralizer ((sSup S₂ : Subgroup G) : Set G) := by
      refine sSup_le fun J hJ x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact (Subgroup.mem_centralizer_iff.mp (h2 J hJ hy) x hx).symm
    exact (Subgroup.mem_centralizer_iff.mp (h1 hx) y hy).symm
  have h2 : sSup S₂ ≤ Subgroup.centralizer (M : Set G) := sSup_le fun J hJ => hJ.2
  have h1 : ∀ m ∈ M, ∀ y ∈ sSup S₁, m * y * m⁻¹ ∈ sSup S₁ := by
    intro m hm y hy
    have : sSup S₁ ≤ (sSup S₁).comap (MulAut.conj m).toMonoidHom := by
      refine sSup_le fun J hJ z hz => ?_
      have hJm : J.map (MulAut.conj m).toMonoidHom ∈ S₁ :=
        ⟨map_conj_mem_lcal hJ.1 (hM hm), not_map_conj_le_centralizer hm hJ.2⟩
      exact le_sSup hJm ⟨z, hz, rfl⟩
    exact this hy
  refine Subgroup.commutator_le.mpr fun k hk m hm => ?_
  rw [← hsup] at hk
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hk
  have hk₂m : Commute k₂ m := (Subgroup.mem_centralizer_iff.mp (h2 hk₂) m hm).symm
  have hcomm_eq : ⁅k₁ * k₂, m⁆ = k₁ * (m * k₁⁻¹ * m⁻¹) := by
    rw [commutatorElement_mul_left_eq_conj_mul, hk₂m.commutator_eq]
    simp [commutatorElement_def, mul_assoc]
  rw [hcomm_eq]
  exact mul_mem hk₁ (h1 m hm _ (inv_mem hk₁))

private theorem le_commutator_of_not_le_centralizer [Finite G] {K M J : Subgroup G}
    (hK : IsSemisimple K) (hM : M ≤ Subgroup.normalizer (K : Set G)) (hJ : J ∈ lcal K)
    (hJM : ¬ J ≤ Subgroup.centralizer (M : Set G)) : J ≤ ⁅K, M⁆ := by
  have hS : IsDirectProduct (lcal K) K := hK.isDirectProduct_lcal
  have hJc : J ∈ simpleComponents K := by rw [← hK.lcal_eq]; exact hJ
  obtain ⟨hJK, -, hJs, a, ha, b, hb, hab⟩ := hJc
  have hKN : K ≤ Subgroup.normalizer (⁅K, M⁆ : Subgroup G) :=
    Subgroup.normalizer_commutator_ge_left K M
  obtain ⟨j, hjJ, hj⟩ := IsConcreteLE.not_le_iff_exists.mp hJM
  obtain ⟨m, hmM, hm⟩ : ∃ m ∈ M, m * j ≠ j * m := by
    rw [Subgroup.mem_centralizer_iff] at hj
    push Not at hj
    exact hj
  have hJ' : J.map (MulAut.conj m).toMonoidHom ∈ lcal K := map_conj_mem_lcal hJ (hM hmM)
  have hj'' : m * j⁻¹ * m⁻¹ ∈ J.map (MulAut.conj m).toMonoidHom := ⟨j⁻¹, inv_mem hjJ, rfl⟩
  have hcN : ⁅j, m⁆ ∈ ⁅K, M⁆ := Subgroup.commutator_mem_commutator (hJK hjJ) hmM
  have hc1 : ⁅j, m⁆ ≠ 1 := fun h => hm (commutatorElement_eq_one_iff_mul_comm.mp h).symm
  have hjj : ⁅j, m⁆ = j * (m * j⁻¹ * m⁻¹) := by simp [commutatorElement_def, mul_assoc]
  have hj1 : j ≠ 1 := by
    rintro rfl
    exact hm (by simp)
  have hZ : Subgroup.center ↥J = ⊥ :=
    CFSG.SignalizerFunctorTheorem.Diagonal.center_eq_bot
      ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hne : J ⊓ ⁅K, M⁆ ≠ ⊥ := by
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ J ⊓ ⁅K, M⁆, z ≠ 1 := by
      by_cases hJJ : J.map (MulAut.conj m).toMonoidHom = J
      · refine ⟨⁅j, m⁆, Subgroup.mem_inf.mpr ⟨?_, hcN⟩, hc1⟩
        rw [hjj]
        exact mul_mem hjJ (hJJ ▸ hj'')
      · obtain ⟨x, hxJ, hx⟩ : ∃ x ∈ J, x * j ≠ j * x := by
          by_contra hcon
          push Not at hcon
          have hmem : (⟨j, hjJ⟩ : J) ∈ Subgroup.center J :=
            Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hcon y y.2)
          rw [hZ, Subgroup.mem_bot] at hmem
          exact hj1 (congrArg Subtype.val hmem)
        have hcomm : Commute x (m * j⁻¹ * m⁻¹) :=
          hS.commute J hJ _ hJ' (Ne.symm hJJ) x hxJ _ hj''
        have hkey : ⁅x, ⁅j, m⁆⁆ = ⁅x, j⁆ := by
          rw [hjj, commutatorElement_mul_right_eq_mul_conj, hcomm.commutator_eq]
          simp
        refine ⟨⁅x, j⁆, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, fun h => hx ?_⟩
        · exact mul_mem (mul_mem (mul_mem hxJ hjJ) (inv_mem hxJ)) (inv_mem hjJ)
        · rw [← hkey]
          exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN (hJK hxJ)) _).mp hcN) (inv_mem hcN)
        · exact commutatorElement_eq_one_iff_mul_comm.mp h
    intro h
    rw [h, Subgroup.mem_bot] at hz
    exact hz1 hz
  exact le_of_inf_ne_bot_of_le_normalizer (hJK.trans hKN) hne

theorem commutator_eq_sSup_not_centralized [Finite G] {K M : Subgroup G} (hK : IsSemisimple K)
    (hM : M ≤ Subgroup.normalizer (K : Set G)) :
    ⁅K, M⁆ = sSup {J | J ∈ lcal K ∧ ¬ J ≤ Subgroup.centralizer (M : Set G)} := by
  refine le_antisymm (commutator_le_sSup_not_centralized hK hM) (sSup_le fun J hJ => ?_)
  exact le_commutator_of_not_le_centralizer hK hM hJ.1 hJ.2

end CFSG.SignalizerFunctorTheorem.McBride
