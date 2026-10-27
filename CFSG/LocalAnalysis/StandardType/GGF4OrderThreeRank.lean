module

public import CFSG.LocalAnalysis.StandardType.GGF4OrderThreeLabel
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyEvenSymplectic
import CFSG.RankThree.PartTwo.Sec21.HeringFFLLiftP
import CFSG.LocalAnalysis.StandardType.GGKGAF4Holds
import CFSG.LocalAnalysis.StandardType.GGLayerCycMInput
import CFSG.Mathlib.GroupTheory.InnerElemAbelian

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem one_le_fieldExp_of_ggHasLabel {H : Type} [Group H] {f : ℕ}
    (hH : GGHasLabel ⟨.F4, 0, f⟩ (H ⧸ Subgroup.center H)) : 1 ≤ f := by
  have hHraw : LargeEvenRawDatum ⟨.F4, 0, f⟩
      (fun R _ _ _ => Nonempty (H ⧸ Subgroup.center H ≃* R)) := hH
  dsimp only [LargeEvenRawDatum] at hHraw
  obtain ⟨K, hKfld, hKfin, hKcard, -⟩ := hHraw
  have h2 : 1 < Nat.card K := @Finite.one_lt_card K hKfin (@Field.toNontrivial K hKfld)
  rw [hKcard] at h2
  rcases Nat.eq_zero_or_pos f with hf | hf
  · rw [hf, pow_zero] at h2
    omega
  · exact hf

private theorem ggF4OrderThree_conj_ne_one {H : Type} [Group H] [Finite H] {z : H}
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center H)) :
    (MulAut.conj z : MulAut H) ≠ 1 := by
  intro hconj
  have hzc : z ∈ Subgroup.center H :=
    CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt.mem_center_of_conj_eq_one hconj
  let zc : ↥(Subgroup.center H) := ⟨z, hzc⟩
  have hzc3 : zc ^ 3 = 1 := Subtype.ext hz3
  have hzc1 : zc ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hord : orderOf zc = 3 := orderOf_eq_prime hzc3 hzc1
  exact hZ (hord ▸ orderOf_dvd_natCard zc)

private theorem ggF4OrderThree_conj_action {H R : Type} [Group H] [Finite H]
    [Group.IsPerfect H] {f : ℕ} [Group R] {I : Set (MulAut R)}
    (hcent : CFSG.StandardType.KGA.GGF4CentAt 3 f R I)
    (hI : ∀ r : R, MulAut.conj r ∈ I)
    (ψ : H →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center H)
    {z g : H} (hz3 : z ^ 3 = 1) (hg : g ∈ Subgroup.centralizer ({z} : Set H))
    {J : Subgroup H} (hJc : IsComponentOf J (Subgroup.centralizer ({z} : Set H)))
    (he1 : (MulAut.conj z : MulAut H) ≠ 1)
    (hlabel : GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J)) :
    ∃ x ∈ J, ∀ y ∈ J, g * y * g⁻¹ = x * y * x⁻¹ := by
  have he3 : (MulAut.conj z : MulAut H) ^ 3 = 1 := by
    rw [← map_pow, hz3, map_one]
  have hcomm : Commute (MulAut.conj z : MulAut H) (MulAut.conj g) :=
    Commute.map (Commute.symm (Subgroup.mem_centralizer_singleton_iff.mp hg)) MulAut.conj
  have hφe : ∃ φ ∈ I, ∀ l : H, φ (ψ l) = ψ ((MulAut.conj z) l) := by
    refine ⟨MulAut.conj (ψ z), hI (ψ z), fun l => ?_⟩
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hφa : ∃ φ ∈ I, ∀ l : H, φ (ψ l) = ψ ((MulAut.conj g) l) := by
    refine ⟨MulAut.conj (ψ g), hI (ψ g), fun l => ?_⟩
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hfix : ggFixSub (MulAut.conj z) = Subgroup.centralizer ({z} : Set H) := by
    ext x
    rw [mem_ggFixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
    constructor
    · intro h
      have h' : z * x = x * z := by
        calc z * x = (z * x * z⁻¹) * z := by group
          _ = x * z := by rw [h]
      exact h'.symm
    · intro h
      calc z * x * z⁻¹ = x * z * z⁻¹ := by rw [← h]
        _ = x := by group
  have hJcomp : IsComponentOf J (ggFixSub (MulAut.conj z)) := by
    rw [hfix]
    exact hJc
  have hres := hcent H ψ hψ hker (Group.IsPerfect.commutator_eq_top)
    (MulAut.conj z) (MulAut.conj g) he3 he1 hcomm hφe hφa J hJcomp hlabel
  obtain ⟨j, hj, hjy⟩ := hres.2
  exact ⟨j, hj, fun y hy => by simpa [MulAut.conj_apply] using hjy y hy⟩

private theorem ggF4OrderThree_inner_of_data {H : Type} [Group H] [Finite H]
    [Group.IsPerfect H] {f : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hcent : CFSG.StandardType.KGA.GGF4CentAt 3 f R I)
    (hI : ∀ r : R, MulAut.conj r ∈ I)
    (e : H ⧸ Subgroup.center H ≃* R) {z g : H} (hz3 : z ^ 3 = 1)
    (hg : g ∈ Subgroup.centralizer ({z} : Set H)) {J : Subgroup H}
    (hJc : IsComponentOf J (Subgroup.centralizer ({z} : Set H)))
    (he1 : (MulAut.conj z : MulAut H) ≠ 1)
    (hlabel : GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J)) :
    ∃ x ∈ J, ∀ y ∈ J, g * y * g⁻¹ = x * y * x⁻¹ := by
  have hψ : Function.Surjective
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))).ker ≤
      Subgroup.center H := by
    have hker_eq : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))).ker =
        Subgroup.center H := by
      rw [← MonoidHom.comap_ker, MonoidHom.ker_eq_bot e.toMonoidHom e.injective,
        MonoidHom.comap_bot, QuotientGroup.ker_mk']
    exact hker_eq.le
  exact ggF4OrderThree_conj_action hcent hI
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))) hψ hker hz3 hg hJc he1 hlabel

private theorem exists_elemAbelian_of_equiv_sp_proj {X K : Type} [Group X] [Finite X]
    [Field K] [CharP K 2] [Fact (Nat.Prime 3)]
    (e : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSpGroup K 3))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center X)) :
    ∃ A : Subgroup X, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 := by
  obtain ⟨E, hEel, hEcard⟩ :=
    CFSG.QuasithinUnique.Setup.Family.even_symplectic_three_rank (K := K) 3
  have hEab : IsElemAbelian 3 E := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hEel
  have hEcomap : IsElemAbelian 3 (E.comap e.toMonoidHom) := hEab.comap e.injective
  have hcard : Nat.card (E.comap e.toMonoidHom) = Nat.card E := by
    have h := Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
      (K := E.comap e.toMonoidHom)
    rw [Subgroup.map_comap_eq_self_of_surjective e.surjective] at h
    exact h.symm
  obtain ⟨A, hA, hAcard⟩ :=
    CFSG.RankThree.PartTwo.Sec21.exists_elemAbelian_of_quotient
      (Subgroup.center X) hZ hEcomap
  exact ⟨A, hA, hAcard.trans (hcard.trans hEcard)⟩

private theorem card_map_eq_of_center_coprime [Fact (Nat.Prime 3)]
    {H R : Type} [Group H] [Finite H] [Group R] {π : H →* R} {B : Subgroup H}
    (hπker : π.ker = Subgroup.center H) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center H))
    (hB : IsElemAbelian 3 B) : Nat.card (B.map π) = Nat.card B := by
  obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hB).exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card (Subgroup.center H)) := by
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ)
  have hinf : B ⊓ Subgroup.center H = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hπinj : Function.Injective (π.domRestrict B) := by
    intro b b' hbb'
    change π (b : H) = π (b' : H) at hbb'
    apply Subtype.ext
    have hmul : π ((b : H)⁻¹ * (b' : H)) = 1 := by
      rw [map_mul, map_inv, hbb', inv_mul_cancel]
    have hmem : (b : H)⁻¹ * (b' : H) ∈ Subgroup.center H := by
      rw [← hπker]
      exact MonoidHom.mem_ker.mpr hmul
    have hmemB : (b : H)⁻¹ * (b' : H) ∈ B := B.mul_mem (B.inv_mem b.2) b'.2
    have hbot : (b : H)⁻¹ * (b' : H) ∈ (⊥ : Subgroup H) := by
      rw [← hinf]
      exact ⟨hmemB, hmem⟩
    exact inv_mul_eq_one.mp (by simpa using hbot)
  have h := Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv
  rw [MonoidHom.domRestrict_range] at h
  exact h.symm

theorem exists_elemAbelian_of_ggHasLabel_C_three
    {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) {f : ℕ} (hXl : GGHasLabel ⟨.C, 3, f⟩ (X ⧸ Subgroup.center X)) :
    ¬ 3 ∣ Nat.card (Subgroup.center X) ∧
      ∃ A : Subgroup X, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 := by
  dsimp only [GGHasLabel, LargeEvenRawDatum] at hXl
  obtain ⟨K, hKfld, hKfin, hKcard, ⟨e⟩⟩ := hXl
  have hCharP : CharP K 2 := @charP_two_of_card K hKfld hKfin f hKcard
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center X) :=
    letI : Field K := hKfld
    letI : Finite K := hKfin
    letI : CharP K 2 := hCharP
    by
      have hψ : Function.Surjective
          (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))) :=
        e.surjective.comp (QuotientGroup.mk'_surjective _)
      have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker ≤
          Subgroup.center X := by
        intro x hx
        have hx1 : e (QuotientGroup.mk' (Subgroup.center X) x) = 1 :=
          MonoidHom.mem_ker.mp hx
        have hq1 : QuotientGroup.mk' (Subgroup.center X) x = 1 :=
          e.injective (by simpa using hx1)
        exact (QuotientGroup.eq_one_iff x).mp hq1
      exact ggCenterPrime_sp (K := K) (m := 3) Nat.prime_three (by norm_num)
        X (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))) hψ hker hX
  exact ⟨hZ3,
    letI : Field K := hKfld
    letI : CharP K 2 := hCharP
    exists_elemAbelian_of_equiv_sp_proj e hZ3⟩


theorem card_le_pow_four_of_ggHasLabel_F4 {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {f : ℕ} (hH : GGHasLabel ⟨.F4, 0, f⟩ (H ⧸ Subgroup.center H)) {B : Subgroup H}
    (hB : IsElemAbelian 3 B) : Nat.card B ≤ 3 ^ 4 := by
  obtain ⟨K, hKfld, hKfin, hKcard, π, hπsurj, hπker⟩ :=
    exists_surjective_adjointGroupF4_of_ggHasLabel hH
  have hCharP : CharP K 2 := @charP_two_of_card K hKfld hKfin f hKcard
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center H) :=
    not_three_dvd_card_center_of_ggHasLabel_F4 hH
  have hcardmap : Nat.card (B.map π) = Nat.card B :=
    card_map_eq_of_center_coprime hπker hZ hB
  have hEab : IsElemAbelian 3 (B.map π) := CFSG.Open.IsElemAbelian.map hB π
  have hd : 3 ∣ Nat.card K ^ 2 - 1 := by
    rw [hKcard]
    have h4 : (2 ^ f) ^ 2 = 4 ^ f := by
      calc (2 ^ f) ^ 2 = 2 ^ (f * 2) := (pow_mul 2 f 2).symm
        _ = 2 ^ (2 * f) := by rw [Nat.mul_comm]
        _ = (2 ^ 2) ^ f := pow_mul 2 2 f
        _ = 4 ^ f := by norm_num
    rw [h4]
    simpa using Nat.sub_one_dvd_pow_sub_one 4 f
  have hle : Nat.card (B.map π) ≤ 3 ^ 4 :=
    letI : Field K := hKfld
    letI : Finite K := hKfin
    letI : CharP K 2 := hCharP
    ExcFieldAutCentRankF4.card_le_pow_four Nat.prime_three (by norm_num) hd hEab
  calc Nat.card B = Nat.card (B.map π) := hcardmap.symm
    _ ≤ 3 ^ 4 := hle


theorem ggF4OrderThree_inner {H : Type} [Group H] [Finite H] [Group.IsPerfect H] {f : ℕ}
    (hH : GGHasLabel ⟨.F4, 0, f⟩ (H ⧸ Subgroup.center H)) {z : H} (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1) {J : Subgroup H}
    (hJ : J = LargeEvenLayer (Subgroup.centralizer ({z} : Set H)))
    (hJc : IsComponentOf J (Subgroup.centralizer ({z} : Set H))) {g : H}
    (hg : g ∈ Subgroup.centralizer ({z} : Set H)) :
    ∃ x ∈ J, ∀ y ∈ J, g * y * g⁻¹ = x * y * x⁻¹ := by
  have hf1 : 1 ≤ f := one_le_fieldExp_of_ggHasLabel hH
  have hH4 : GGHasLabel ⟨.F4, 4, f⟩ (H ⧸ Subgroup.center H) := hH
  have hraw := (CFSG.StandardType.KGA.ggF4C3CentInputStrong_holds 3 Nat.prime_three
    (by norm_num) f hf1)
    (fun (R : Type) [Group R] (_ : Set (MulAut R)) (_ : Set (MulAut R)) =>
      Nonempty (H ⧸ Subgroup.center H ≃* R)) hH4
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hKfld, _, _, ⟨e⟩, hcent⟩ := hraw
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center H) :=
    not_three_dvd_card_center_of_ggHasLabel_F4 hH
  have he1 : (MulAut.conj z : MulAut H) ≠ 1 :=
    ggF4OrderThree_conj_ne_one hz1 hz3 hZ
  have hlabel : GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J) :=
    ggF4OrderThree_layer_label hH hz1 hz3 hJ hJc
  have hI : ∀ r : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false),
      MulAut.conj r ∈ LargeEvenChevIDImage LargeEvenCartanF4 K
        (LargeEvenChevH LargeEvenCartanF4 K false) :=
    letI : Field K := hKfld
    fun r => conj_mem_largeEvenChevIDImage LargeEvenCartanF4 K
      (LargeEvenChevH LargeEvenCartanF4 K false) r
  exact ggF4OrderThree_inner_of_data hcent hI e hz3 hg hJc he1 hlabel

theorem ggF4OrderThree_card_le {H : Type} [Group H] [Finite H] [Group.IsPerfect H] {f : ℕ}
    (hH : GGHasLabel ⟨.F4, 0, f⟩ (H ⧸ Subgroup.center H)) {z : H} (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1) {J : Subgroup H}
    (hJ : J = LargeEvenLayer (Subgroup.centralizer ({z} : Set H)))
    (hJc : IsComponentOf J (Subgroup.centralizer ({z} : Set H))) {E : Subgroup H}
    (hEz : E ≤ Subgroup.centralizer ({z} : Set H)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 * Nat.card (E ⊓ J : Subgroup H) := by
  have hlabel : GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J) :=
    ggF4OrderThree_layer_label hH hz1 hz3 hJ hJc
  have hJperf : commutator ↥J = ⊤ := hJc.2.2.1
  have hC := exists_elemAbelian_of_ggHasLabel_C_three (X := ↥J) hJperf hlabel
  obtain ⟨hZJ, A, hA, hAcard⟩ := hC
  have hAel : IsElemAbelian 3 (A.map J.subtype) :=
    CFSG.Open.IsElemAbelian.map hA J.subtype
  have hAcard' : Nat.card (A.map J.subtype) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (f := J.subtype) J.subtype_injective]
    exact hAcard
  have hm : ∀ B : Subgroup H, IsMulCommutative B → (∀ b ∈ B, b ^ 3 = 1) →
      Nat.card B ≤ 3 ^ (3 + 1) := by
    intro B hBc hBp
    exact card_le_pow_four_of_ggHasLabel_F4 hH ⟨hBc, hBp⟩
  have hinn : ∀ e ∈ E, ∃ x ∈ J, ∀ y ∈ J, e * y * e⁻¹ = x * y * x⁻¹ := by
    intro e he
    exact ggF4OrderThree_inner hH hz1 hz3 hJ hJc (hEz he)
  exact CFSG.card_le_mul_card_inf_of_forall_inner (G := H) (J := J) (E := E)
    (p := 3) (k := 3) hZJ (Subgroup.map_subtype_le A) hAel.1 hAel.2
    hAcard'.ge hm hE.1 hE.2 hinn

theorem ggF4OrderThreeLayer_holds : GGF4OrderThreeLayer :=
  fun _ _ _ _ _ _ hH _ hz1 hz3 _ hJ hJc =>
    ⟨ggF4OrderThree_layer_label hH hz1 hz3 hJ hJc,
      fun _ hEz hE => ggF4OrderThree_card_le hH hz1 hz3 hJ hJc hEz hE⟩

end CFSG.StandardType

end
