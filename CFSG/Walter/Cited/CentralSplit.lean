module

public import CFSG.Walter.ReeOrder.JT.Defs
public import CFSG.StronglyEmbedded.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14

public section

namespace CFSG.Walter.Suzuki

open scoped MatrixGroups

theorem pow_index_eq_one_of_mem_center {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    (hH : IsMulCommutative H) {z : G} (hzc : z ∈ Subgroup.center G) (hz : z ∈ commutator G) :
    z ^ H.index = 1 := by
  let : CommGroup H := { (inferInstance : Group H) with mul_comm := hH.is_comm.comm }
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hk : z ^ k ∈ Subgroup.center G := pow_mem hzc k
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp hk g₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id H) z key
  have h2 : (MonoidHom.id H).transfer z = 1 :=
    Abelianization.commutator_subset_ker ((MonoidHom.id H).transfer) hz
  rw [h2] at h1
  exact (congrArg Subtype.val h1).symm

variable {M : Type*} [Group M] [Finite M] (O : Subgroup M) [O.Normal]

theorem commutator_inf_eq_bot (hO : Odd (Nat.card O)) (hcen : O ≤ Subgroup.center M)
    (hcyc : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ R : Sylow p (M ⧸ O), IsCyclic R) :
    commutator M ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzc, hzO⟩
  rw [Subgroup.mem_bot]
  by_contra hz1
  have hord1 : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hord1
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (orderOf z) := hO.of_dvd_nat (O.orderOf_dvd_natCard hzO)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
  set w := z ^ (orderOf z / p) with hwdef
  have hw : orderOf w = p := orderOf_pow_orderOf_div (orderOf_pos z).ne' hpd
  have hwc : w ∈ commutator M := pow_mem hzc _
  have hwO : w ∈ O := pow_mem hzO _
  obtain ⟨R⟩ : Nonempty (Sylow p (M ⧸ O)) := inferInstance
  set H := (R : Subgroup (M ⧸ O)).comap (QuotientGroup.mk' O) with hH
  have hHab : IsMulCommutative H := by
    have := hcyc p hp2 R
    let f : H →* (R : Subgroup (M ⧸ O)) :=
      ((QuotientGroup.mk' O).comp H.subtype).codRestrict (R : Subgroup (M ⧸ O)) fun h => h.2
    refine f.isMulCommutative_of_isCyclic_of_ker_le_center fun h hh => ?_
    have hhO : (h : M) ∈ O := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hh)
      exact (QuotientGroup.eq_one_iff (h : M)).mp this
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcen hhO) g)
  have hidx : H.index = (R : Subgroup (M ⧸ O)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective O)
  have h1 := pow_index_eq_one_of_mem_center hHab (hcen hwO) hwc
  have h2 : p ∣ H.index := hw ▸ orderOf_dvd_of_pow_eq_one h1
  rw [hidx] at h2
  exact R.not_dvd_index h2

theorem card_psl24 : Nat.card PSL(2, GaloisField 2 2) = 60 := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have : CharP (GaloisField 2 2) 2 := inferInstance
  have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (K := GaloisField 2 2) (CharTwo.neg_eq 1)
  have hcard := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center
    (K := GaloisField 2 2)
  rw [hK, hcenter] at hcard
  norm_num at hcard
  exact hcard

theorem nonempty_mulEquiv_psl24 {X : Type*} [Group X] [Finite X]
    [IsSimpleGroup X]
    (hX : Nat.card X = 60) : Nonempty (X ≃* PSL(2, GaloisField 2 2)) := by
  have : IsSimpleGroup PSL(2, GaloisField 2 2) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 2 (by norm_num)]; norm_num)
  obtain ⟨e₁⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five hX
  obtain ⟨e₂⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five card_psl24
  exact ⟨e₁.trans e₂.symm⟩

theorem commutator_eq_top_of_card_sixty {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : Nat.card X = 60) : commutator X = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · exfalso
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    let : CommGroup X :=
      { (inferInstance : Group X) with
        mul_comm := fun a b =>
          (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top b)) a (Subgroup.mem_top a)) }
    have hp := IsSimpleGroup.prime_card (α := X)
    rw [hX] at hp
    norm_num at hp
  · exact h

theorem isCyclic_sylow_of_card_sixty {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 60)
    (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (R : Sylow p X) : IsCyclic R := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp R.isPGroup'
  have hdvd : p ^ k ∣ 60 := hk ▸ hX ▸ Subgroup.card_subgroup_dvd_card _
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have hsq : p ^ 2 ∣ 60 := (pow_dvd_pow p (by omega)).trans hdvd
    have hle : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) hsq
    have hp7 : p ≤ 7 := by nlinarith
    have hp1 := hp.out.two_le
    interval_cases p <;> first | exact hp2 rfl | norm_num at hsq
  interval_cases k
  · have : Subsingleton (R : Subgroup X) :=
      (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
    infer_instance
  · exact isCyclic_of_prime_card (p := p) (by simpa using hk)

theorem exists_isInternalDirectProduct (hO : Odd (Nat.card O))
    (hcen : O ≤ Subgroup.center M)
    [IsSimpleGroup (M ⧸ O)] (hcard : Nat.card (M ⧸ O) = 60) :
    ∃ L : Subgroup M, Nonempty (L ≃* PSL(2, GaloisField 2 2)) ∧
      CFSG.Walter.JT.IsInternalDirectProduct L O ⊤ := by
  set π := QuotientGroup.mk' O with hπ
  have hdisj : commutator M ⊓ O = ⊥ := commutator_inf_eq_bot O hO hcen fun p _ hp2 R =>
    isCyclic_sylow_of_card_sixty hcard p hp2 R
  have hmap : (commutator M).map π = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective O), ← commutator_def]
    exact commutator_eq_top_of_card_sixty hcard
  have hsup : commutator M ⊔ O = ⊤ := by
    have h := Subgroup.comap_map_eq π (commutator M)
    rw [hmap, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h
    exact h.symm
  refine ⟨commutator M, ?_, hsup, disjoint_iff.mpr hdisj, ?_⟩
  ·
    let f : commutator M →* M ⧸ O := π.comp (commutator M).subtype
    have hinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hxO : (x : M) ∈ O := (QuotientGroup.eq_one_iff (x : M)).mp (MonoidHom.mem_ker.mp hx)
      have : (x : M) ∈ commutator M ⊓ O := ⟨x.2, hxO⟩
      rw [hdisj, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (Subtype.ext this)
    have hsurj : Function.Surjective f := by
      intro y
      have hy : y ∈ (commutator M).map π := hmap ▸ Subgroup.mem_top y
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨e⟩ := nonempty_mulEquiv_psl24 hcard
    exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).trans e⟩
  · intro l _
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    exact (Subgroup.mem_center_iff.mp (hcen ho) l).symm

end CFSG.Walter.Suzuki
