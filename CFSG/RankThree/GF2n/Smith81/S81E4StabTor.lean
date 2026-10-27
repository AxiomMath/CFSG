module

public import CFSG.RankThree.GF2n.Smith81.S81KNormGrp

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.D6X


variable {K : Type} [Field K]

@[expose] def TLam (K : Type) [Field K] : Subgroup (e7Data_valid.minGroup K) :=
  ⨆ (i : Fin (Tag.rank .E7)) (_ : 1 ≤ i.val), e7Data_valid.torus K i

private theorem tLam_le_lamG [CharP K 2] : TLam K ≤ D6X.LamG K := by
  refine iSup₂_le fun i hi x hx => ?_
  obtain ⟨s, rfl⟩ := (e7Data_valid.mem_torus K).1 hx
  exact D6Normalizer.hm_mem_LamG i hi s

set_option maxRecDepth 20000 in
private theorem eq_theta_of_node1_check : ∀ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ →
    γ node1 = 2 → ∀ j, γ j = theta j := by
  refine (forall_isRoot_iff fun γ => γ node1 = 2 → ∀ j, γ j = theta j).2 ?_
  decide +kernel

theorem not_isRoot_add_theta {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) :
    ¬ IsRoot .E7 (β + theta) ∧ β + theta ≠ 0 := by
  have h1 : (β + theta) node1 = 2 := by
    rw [Pi.add_apply, (perp_iff.1 hβ).2, zero_add]
    decide
  refine ⟨fun hr => ?_, fun h0 => by rw [h0] at h1; exact absurd h1 (by decide)⟩
  have he : β + theta = theta := funext (eq_theta_of_node1_check _ hr h1)
  have hβ0 : β = 0 := by simpa using he
  exact (perp_iff.1 hβ).1.ne_zero hβ0

theorem lamG_commute_xm_theta {g : e7Data_valid.minGroup K} (hg : g ∈ LamG K) (d : K) :
    g * e7Data_valid.xm K theta d = e7Data_valid.xm K theta d * g := by
  have key : Lam K ≤ Subgroup.centralizer {e7Data_valid.xu K theta d} := by
    rw [Lam, Subgroup.closure_le]
    rintro _ ⟨β, hβ, c, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    obtain ⟨hnot, hne⟩ := not_isRoot_add_theta hβ
    have hcomm := (e7Data_valid.commutator_xm K hβ.1 isRoot_theta hne).2 hnot c d
    rw [commutatorElement_eq_one_iff_mul_comm] at hcomm
    exact (congrArg Subtype.val hcomm).symm
  exact Subtype.ext
    (Subgroup.mem_centralizer_iff.1 (key (mem_LamG.1 hg)) _ (Set.mem_singleton _)).symm

theorem exists_hm_node1_mul_of_mem_tor {t : e7Data_valid.minGroup K} (ht : t ∈ Tor K) :
    ∃ s : Kˣ, ∃ l ∈ TLam K, t = e7Data_valid.hm K node1 s * l := by
  refine Subgroup.iSup_induction (fun i => e7Data_valid.torus K i)
    (C := fun t => ∃ s : Kˣ, ∃ l ∈ TLam K, t = e7Data_valid.hm K node1 s * l) ht ?_ ?_ ?_
  · intro i x hx
    obtain ⟨s, rfl⟩ := (e7Data_valid.mem_torus K).1 hx
    by_cases hi : i = node1
    · subst hi
      exact ⟨s, 1, one_mem _, (mul_one _).symm⟩
    · have hi1 : 1 ≤ i.val := by
        have : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      exact ⟨1, _, Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem hi1
        (e7Data_valid.hm_mem_torus K i s)), by rw [e7Data_valid.hm_one, one_mul]⟩
  · exact ⟨1, 1, one_mem _, by rw [e7Data_valid.hm_one, one_mul]⟩
  · rintro x y ⟨s, l, hl, rfl⟩ ⟨s', l', hl', rfl⟩
    have key : TLam K ≤ Subgroup.centralizer {e7Data_valid.hm K node1 s'} :=
      iSup₂_le fun i _ x hx => Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (e7Data_valid.torus_commute K node1 i (e7Data_valid.hm_mem_torus K node1 s') hx).eq
    have hc : l * e7Data_valid.hm K node1 s' = e7Data_valid.hm K node1 s' * l :=
      (Subgroup.mem_centralizer_iff.1 (key hl) _ (Set.mem_singleton _)).symm
    refine ⟨s * s', l * l', mul_mem hl hl', ?_⟩
    have e : e7Data_valid.hm K node1 s * l * (e7Data_valid.hm K node1 s' * l') =
        e7Data_valid.hm K node1 s * (l * e7Data_valid.hm K node1 s') * l' := by
      simp only [mul_assoc]
    rw [e, hc, e7Data_valid.hm_mul]
    simp only [mul_assoc]

theorem mem_tLam_of_mem_tor_of_mem_lamG [CharP K 2] {t : e7Data_valid.minGroup K}
    (ht : t ∈ Tor K) (hl : t ∈ LamG K) : t ∈ TLam K := by
  obtain ⟨s, l, hlT, rfl⟩ := exists_hm_node1_mul_of_mem_tor ht
  have h1 := lamG_commute_xm_theta hl 1
  have h2 := lamG_commute_xm_theta (tLam_le_lamG hlT) 1
  have h3 : e7Data_valid.hm K node1 s * e7Data_valid.xm K theta 1 *
      (e7Data_valid.hm K node1 s)⁻¹ = e7Data_valid.xm K theta 1 := by
    rw [mul_inv_eq_iff_eq_mul]
    apply mul_right_cancel (b := l)
    rw [mul_assoc, ← h2, ← mul_assoc, h1, mul_assoc]
  rw [e7Data_valid.hm_conj_xm K isRoot_theta node1 s 1] at h3
  have h5 : MinData.toWeight theta node1 = 1 := by decide
  have h4 := e7Data_valid.xm_injective K isRoot_theta h3
  simp only [h5, zpow_one, mul_one] at h4
  have hs : s = 1 := Units.ext h4
  rw [hs, e7Data_valid.hm_one, one_mul]
  exact hlT

end CFSG.RankThree.GF2n.Smith81.D6Spin
