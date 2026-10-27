module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Smear
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Glauberman

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma212

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A B G : Subgroup Γ}

namespace GoodB

variable (H : Hyp p A G) (hB : GoodB A B G)

include H hB

theorem kOf_inf_centralizer_le_iSup_smear :
    kOf G ⊓ Subgroup.centralizer (B : Set Γ) ≤ ⨆ J ∈ lcal G, smear J B := by
  classical
  have hK := H.hK
  have hfin : Finite ↥(lcal G) := (Set.toFinite (lcal G)).to_subtype
  let e : Fin (Nat.card ↥(lcal G)) ≃ ↥(lcal G) := (Finite.equivFin ↥(lcal G)).symm
  let K' : Fin (Nat.card ↥(lcal G)) → Subgroup Γ := fun i => orbitClosure (e i).1 A
  have hinv : ∀ i, B ≤ Subgroup.normalizer (K' i : Set Γ) := fun i =>
    hB.le.trans (le_normalizer_orbitClosure _ A)
  have hperm : ∀ i j, (K' i : Set Γ) * K' j = K' j * K' i := by
    intro i j
    by_cases hij : ∃ a ∈ A, (e j).1 = (e i).1.map (MulAut.conj a).toMonoidHom
    · obtain ⟨a, ha, h⟩ := hij
      have : K' j = K' i := by
        show orbitClosure (e j).1 A = orbitClosure (e i).1 A
        rw [h, orbitClosure_map_conj_of_mem _ ha]
      rw [this]
    · push Not at hij
      have hd : Disjoint {K | ∃ a ∈ A, K = (e i).1.map (MulAut.conj a).toMonoidHom}
          {K | ∃ a ∈ A, K = (e j).1.map (MulAut.conj a).toMonoidHom} := by
        refine Set.disjoint_left.mpr ?_
        rintro K ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
        refine hij (b⁻¹ * a) (mul_mem (inv_mem hb) ha) ?_
        calc (e j).1
            = ((e j).1.map (MulAut.conj b).toMonoidHom).map (MulAut.conj b⁻¹).toMonoidHom :=
              (map_conj_map_conj_inv _ b).symm
          _ = ((e i).1.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b⁻¹).toMonoidHom := by
              rw [← hab]
          _ = (e i).1.map (MulAut.conj (b⁻¹ * a)).toMonoidHom := Thm210.map_conj_map_conj _ a b⁻¹
      have hs : ∀ k, {K | ∃ a ∈ A, K = (e k).1.map (MulAut.conj a).toMonoidHom} ⊆ lcal G := by
        rintro k K ⟨a, ha, rfl⟩
        exact H.A_perm_lcal ha (e k).2
      have hc : ∀ x ∈ K' i, ∀ y ∈ K' j, Commute x y := by
        intro x hx y hy
        have hx' : x ∈ sSup {K | ∃ a ∈ A, K = (e i).1.map (MulAut.conj a).toMonoidHom} := by
          rw [← orbitClosure_eq_sSup]
          exact hx
        have hy' : y ∈ sSup {K | ∃ a ∈ A, K = (e j).1.map (MulAut.conj a).toMonoidHom} := by
          rw [← orbitClosure_eq_sSup]
          exact hy
        exact commute_sSup_sSup hK hd (hs i) (hs j) x hx' y hy'
      ext z
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact ⟨y, hy, x, hx, (hc x hx y hy).eq.symm⟩
      · rintro ⟨y, hy, x, hx, rfl⟩
        exact ⟨x, hx, y, hy, (hc x hx y hy).eq⟩
  have hgen : ⨆ i, K' i = kOf G := by
    refine le_antisymm (iSup_le fun i =>
      orbitClosure_le_of_normalizer (hK.le (e i).2) H.A_le_normalizer) ?_
    rw [← hK.sSup_eq]
    refine sSup_le fun J hJ => ?_
    refine le_iSup_of_le (e.symm ⟨J, hJ⟩) ?_
    have : (e (e.symm ⟨J, hJ⟩)).1 = J := by rw [Equiv.apply_symm_apply]
    show J ≤ orbitClosure (e (e.symm ⟨J, hJ⟩)).1 A
    rw [this]
    exact le_orbitClosure J A
  have hp : IsPGroup p B := H.isPGroup.to_le hB.le
  have hcop : Nat.Coprime p (Nat.card (kOf G)) :=
    H.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (kOf_le G))
  rw [centralizer_eq_iSup_centralizer H.near.prime hp hcop K' hinv hperm hgen]
  refine iSup_le fun i => ?_
  have : K' i ⊓ Subgroup.centralizer (B : Set Γ) = smear (e i).1 B :=
    (smear_eq H hB (e i).2).symm
  rw [this]
  exact le_iSup₂_of_le (e i).1 (e i).2 le_rfl

theorem exists_smear_le_of_normal {N : Subgroup Γ}
    (hNM : N ≤ kOf G ⊓ Subgroup.centralizer (B : Set Γ))
    (hnorm : kOf G ⊓ Subgroup.centralizer (B : Set Γ) ≤ Subgroup.normalizer (N : Set Γ))
    (hN : N ≠ ⊥) : ∃ J ∈ lcal G, smear J B ≤ N := by
  have hK := H.hK
  obtain ⟨⟨n, hn⟩, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN
  have hnM := hNM hn
  have hnK : n ∈ kOf G := hnM.1
  obtain ⟨J, hJ, hc⟩ : ∃ J, ∃ hJ : J ∈ lcal G, hK.coord hJ ⟨n, hnK⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hn1
    have h1 : (⟨n, hnK⟩ : ↥(kOf G)) = 1 :=
      hK.ext_coord fun J hJ => by rw [map_one]; exact hcon J hJ
    have h2 : n = 1 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hJs : IsSimpleGroup ↥J := (mem_lcal_iff.mp hJ).2.2.1
  have hJnc : ∃ x y : ↥J, x * y ≠ y * x :=
    exists_mul_ne_of_not_isMulCommutative (mem_lcal_iff.mp hJ).2.2.2
  set c : ↥J := hK.coord hJ ⟨n, hnK⟩ with hcdef
  obtain ⟨y, hy⟩ : ∃ y : ↥J, c * y ≠ y * c := by
    by_contra hcon
    push Not at hcon
    have hmem : c ∈ Subgroup.center ↥J := Subgroup.mem_center_iff.mpr fun z => (hcon z).symm
    rw [Diagonal.center_eq_bot hJnc, Subgroup.mem_bot] at hmem
    exact hc hmem
  have hyP : (y : Γ) ∈ projIn (lcal G) J (smear J B) := by
    rw [projIn_smear H hB hJ]
    exact y.2
  obtain ⟨xk, hxk, hxky⟩ := (hK.mem_projIn_iff hJ).mp hyP
  have hxkc : hK.coord hJ xk = y := Subtype.ext hxky
  have hxM := smear_le H hB hJ hxk
  have hnorm' := hnorm hxM
  set z : Γ := n * (xk : Γ) * n⁻¹ * (xk : Γ)⁻¹ with hzdef
  have hzN : z ∈ N := by
    have h1 : (xk : Γ) * n⁻¹ * (xk : Γ)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp hnorm' n⁻¹).mp (inv_mem hn)
    have : z = n * ((xk : Γ) * n⁻¹ * (xk : Γ)⁻¹) := by rw [hzdef]; group
    rw [this]
    exact mul_mem hn h1
  have hzM : z ∈ kOf G ⊓ Subgroup.centralizer (B : Set Γ) :=
    mul_mem (mul_mem (mul_mem hnM hxM) (inv_mem hnM)) (inv_mem hxM)
  have hzK : z ∈ kOf G := hzM.1
  have hzk : (⟨z, hzK⟩ : ↥(kOf G)) = ⟨n, hnK⟩ * xk * ⟨n, hnK⟩⁻¹ * xk⁻¹ := rfl
  have hzorb : z ∈ orbitClosure J A := by
    refine mem_orbitClosure_of_coord H hzK fun J' hJ' hne => ?_
    have hx1 : hK.coord hJ' xk = 1 := by
      rw [hK.coord_eq_one_iff hJ']
      exact smear_le_sSup H hB hJ hne hxk
    rw [hzk]
    simp only [map_mul, map_inv, hx1]
    simp
  have hzS : z ∈ smear J B := by
    rw [smear_eq H hB hJ]
    exact Subgroup.mem_inf.mpr ⟨hzorb, hzM.2⟩
  have hz1 : z ≠ 1 := by
    intro hz
    have h1 : (⟨z, hzK⟩ : ↥(kOf G)) = 1 := Subtype.ext hz
    have h2 := congrArg (hK.coord hJ) h1
    rw [hzk] at h2
    simp only [map_mul, map_inv, hxkc, map_one] at h2
    apply hy
    have : c * y * c⁻¹ * y⁻¹ = 1 := h2
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  refine ⟨J, hJ, ?_⟩
  have := isSimpleGroup_smear H hB hJ
  have hnormal : ((N ⊓ smear J B).subgroupOf (smear J B)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem hk hh.2) (inv_mem hk)⟩
    exact (Subgroup.mem_normalizer_iff.mp (hnorm (smear_le H hB hJ hk)) h).mp hh.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ smear J B).subgroupOf (smear J B)) with
    h | h
  · exfalso
    have hzmem : (⟨z, hzS⟩ : ↥(smear J B)) ∈ (N ⊓ smear J B).subgroupOf (smear J B) :=
      Subgroup.mem_inf.mpr ⟨hzN, hzS⟩
    rw [h, Subgroup.mem_bot] at hzmem
    exact hz1 (congrArg Subtype.val hzmem)
  · intro s hs
    have : (⟨s, hs⟩ : ↥(smear J B)) ∈ (N ⊓ smear J B).subgroupOf (smear J B) := by
      rw [h]
      trivial
    exact (Subgroup.mem_inf.mp this).1

end GoodB

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma212
