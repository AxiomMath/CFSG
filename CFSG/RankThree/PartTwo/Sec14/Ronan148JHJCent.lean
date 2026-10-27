module

public import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
public import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofTripleA6

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree.PartTwo

theorem exists_sylow_three_le_centralizer_of_card {X : Type} [Group X] [Finite X] {z : X}
    (hz3 : z ^ 3 = 1) (hXcard : Nat.card X = 604800)
    (h27 : 3 ^ 3 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set X))) :
    ∃ P : Sylow 3 X, z ∈ (P : Subgroup X) ∧
      (P : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := by
  have hzC : z ∈ Subgroup.centralizer ({z} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨w, hw⟩ : ∃ w : ↥(Subgroup.centralizer ({z} : Set X)), (w : X) = z :=
    ⟨⟨z, hzC⟩, rfl⟩
  have hw3 : w ^ 3 = 1 := by
    apply Subtype.ext
    simpa [hw] using hz3
  have hwP : IsPGroup 3 (Subgroup.zpowers w) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hw3
  obtain ⟨S, hS⟩ := hwP.exists_le_sylow
  have hwS : w ∈ (S : Subgroup ↥(Subgroup.centralizer ({z} : Set X))) :=
    hS (Subgroup.mem_zpowers w)
  obtain ⟨T, hT⟩ : ∃ T : Subgroup X,
      T = (S : Subgroup ↥(Subgroup.centralizer ({z} : Set X))).map
        (Subgroup.centralizer ({z} : Set X)).subtype := ⟨_, rfl⟩
  have hTP : IsPGroup 3 T := by
    rw [hT]
    exact S.isPGroup'.map (Subgroup.centralizer ({z} : Set X)).subtype
  have hTle : T ≤ Subgroup.centralizer ({z} : Set X) := by
    rw [hT]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hzT : z ∈ T := by
    rw [hT]
    exact Subgroup.mem_map.mpr ⟨w, hwS, hw⟩
  have hTcard : 3 ^ 3 ∣ Nat.card ↥T := by
    rw [hT, Subgroup.card_map_of_injective (Subgroup.centralizer ({z} : Set X)).subtype_injective]
    exact S.pow_dvd_card_of_pow_dvd_card h27
  have hTindex : ¬ 3 ∣ T.index := by
    intro h3
    have hdvd := mul_dvd_mul h3 hTcard
    rw [T.index_mul_card, hXcard] at hdvd
    norm_num at hdvd
  exact ⟨hTP.toSylow hTindex, hzT, hTle⟩

theorem inf_centralizer_facts_of_j2
    {Γ : Type} [Group Γ] [Finite Γ] {J : Subgroup Γ}
    (φ : ↥J ≃* CFSG.Blueprint.NativeSporadic.J2) {z : Γ} (hzJ : z ∈ J) (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1)
    (h27 : 27 ∣ Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set Γ))) :
    Sec4.IsTripleCover ↥(J ⊓ Subgroup.centralizer ({z} : Set Γ)) (alternatingGroup (Fin 6)) ∧
      Group.IsPerfect ↥(J ⊓ Subgroup.centralizer ({z} : Set Γ)) ∧
      Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set Γ)) = 1080 ∧
      ∀ g ∈ J ⊓ Subgroup.centralizer ({z} : Set Γ),
        (∀ h ∈ J ⊓ Subgroup.centralizer ({z} : Set Γ), g * h = h * g) →
          g ∈ Subgroup.zpowers z := by
  have hX : Nonempty (↥J ≃* CFSG.Blueprint.NativeSporadic.J2) := ⟨φ⟩
  have hJcard : Nat.card ↥J = 604800 := CFSG.RankThree.PartTwo.KFacts.KS14.card_eq_of_j2 hX
  obtain ⟨z', hz'⟩ : ∃ z' : ↥J, (z' : Γ) = z := ⟨⟨z, hzJ⟩, rfl⟩
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    have h2 : ((z' : ↥J) : Γ) = ((1 : ↥J) : Γ) := congrArg Subtype.val h
    rw [hz'] at h2
    simpa using h2
  have hz'3 : z' ^ 3 = 1 := by
    apply Subtype.ext
    simpa [hz'] using hz3
  have hmap : (Subgroup.centralizer ({z'} : Set ↥J)).map J.subtype =
      J ⊓ Subgroup.centralizer ({z} : Set Γ) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxz : (x : Γ) * z = z * (x : Γ) := by
        have h2 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx)
        simpa [hz'] using h2
      exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr hxz⟩
    · intro hg
      obtain ⟨hgJ, hgC⟩ := Subgroup.mem_inf.mp hg
      have hcomm' : (⟨g, hgJ⟩ : ↥J) * z' = z' * ⟨g, hgJ⟩ := by
        apply Subtype.ext
        show g * (z' : Γ) = (z' : Γ) * g
        rw [hz']
        exact Subgroup.mem_centralizer_singleton_iff.mp hgC
      exact Subgroup.mem_map.mpr
        ⟨⟨g, hgJ⟩, Subgroup.mem_centralizer_singleton_iff.mpr hcomm', rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ↥(Subgroup.centralizer ({z'} : Set ↥J)) ≃*
      ↥(J ⊓ Subgroup.centralizer ({z} : Set Γ)),
      ∀ x, ((e x : ↥(J ⊓ Subgroup.centralizer ({z} : Set Γ))) : Γ) = ((x : ↥J) : Γ) :=
    ⟨(Subgroup.equivMapOfInjective (Subgroup.centralizer ({z'} : Set ↥J)) J.subtype
        J.subtype_injective).trans (MulEquiv.subgroupCongr hmap), fun x => rfl⟩
  have hCJc : Nat.card ↥(Subgroup.centralizer ({z'} : Set ↥J)) =
      Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set Γ)) :=
    Nat.card_congr e.toEquiv
  have h27' : 3 ^ 3 ∣ Nat.card ↥(Subgroup.centralizer ({z'} : Set ↥J)) := by
    rw [hCJc, show (3 : ℕ) ^ 3 = 27 by norm_num]
    exact h27
  obtain ⟨P, hzP, hPC⟩ :=
    exists_sylow_three_le_centralizer_of_card (X := ↥J) hz'3 hJcard h27'
  have hz : ∃ P' : Sylow 3 ↥J, z' ∈ (P' : Subgroup ↥J) ∧
      (P' : Subgroup ↥J) ≤ Subgroup.centralizer ({z'} : Set ↥J) := ⟨P, hzP, hPC⟩
  have hC3 := CFSG.RankThree.PartTwo.KFacts.KS14.Native.j2_centralizer_isTripleCover hX hz'1 hz
  have hperf := CFSG.RankThree.PartTwo.KFacts.KS14.Native.j2_centralizer_isPerfect hX hz'1 hz
  have hcen := CFSG.RankThree.PartTwo.KFacts.KS14.Native.j2_center_centralizer hX hz'1 hz
  refine ⟨CFSG.RankThree.PartTwo.KFacts.KS14.isTripleCover_congr e hC3, ?_, ?_, ?_⟩
  · haveI : Group.IsPerfect ↥(Subgroup.centralizer ({z'} : Set ↥J)) := hperf
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · rw [← hCJc]
    exact CFSG.RankThree.PartTwo.Sec19.Item19Res4Proof.card_eq_of_isTripleA6
      (show CFSG.RankThree.PartTwo.Sec19.IsTripleA6 (Subgroup.centralizer ({z'} : Set ↥J))
        from hC3)
  · intro g hg hcomm
    obtain ⟨g', hg'⟩ : ∃ g' : ↥(Subgroup.centralizer ({z'} : Set ↥J)), e g' = ⟨g, hg⟩ :=
      ⟨e.symm ⟨g, hg⟩, e.apply_symm_apply _⟩
    have hgcen : g' ∈ Subgroup.center ↥(Subgroup.centralizer ({z'} : Set ↥J)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.injective
      apply Subtype.ext
      rw [map_mul, map_mul, hg']
      show ((e y : ↥(J ⊓ Subgroup.centralizer ({z} : Set Γ))) : Γ) * g =
        g * ((e y : ↥(J ⊓ Subgroup.centralizer ({z} : Set Γ))) : Γ)
      exact (hcomm _ (e y).2).symm
    rw [hcen, Subgroup.mem_subgroupOf] at hgcen
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgcen
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 : ((e g' : ↥(J ⊓ Subgroup.centralizer ({z} : Set Γ))) : Γ) = g :=
      congrArg Subtype.val hg'
    have h2 := he g'
    have h3 : ((z' ^ k : ↥J) : Γ) = ((g' : ↥J) : Γ) := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow, hz'] at h3
    exact h3.trans (h2.symm.trans h1)

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
