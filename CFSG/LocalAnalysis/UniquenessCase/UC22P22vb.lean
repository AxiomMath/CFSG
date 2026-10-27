module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront05
import CFSG.GroupTheory.WielandtProductFinal
import CFSG.GH74.BNPair.Lemma3013

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

section Core

variable {G : Type} [Group G]

private theorem uc22p22vb_exists_mul_of_mem_sup {H K : Subgroup G}
    (h : (H : Set G) * K = K * H) {g : G} (hg : g ∈ H ⊔ K) : ∃ a ∈ H, ∃ b ∈ K, g = a * b := by
  let S : Subgroup G :=
    { carrier := (H : Set G) * K
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        have hbc : b * c ∈ (K : Set G) * H := ⟨b, hb, c, hc, rfl⟩
        rw [← h] at hbc
        obtain ⟨c', hc', b', hb', hcb⟩ := hbc
        have hcb : c' * b' = b * c := hcb
        refine ⟨a * c', H.mul_mem ha hc', b' * d, K.mul_mem hb' hd, ?_⟩
        calc a * c' * (b' * d) = a * (c' * b') * d := by group
          _ = a * (b * c) * d := by rw [hcb]
          _ = a * b * (c * d) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have hba : b⁻¹ * a⁻¹ ∈ (K : Set G) * H := ⟨b⁻¹, K.inv_mem hb, a⁻¹, H.inv_mem ha, rfl⟩
        rw [← h] at hba
        show (a * b)⁻¹ ∈ (H : Set G) * K
        rw [_root_.mul_inv_rev]
        exact hba }
  have hle : H ⊔ K ≤ S := sup_le (fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩)
    (fun x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := hle hg
  exact ⟨a, ha, b, hb, hab.symm⟩

variable [Finite G]

private theorem uc22p22vb_card_eq {T B : Subgroup G} (hT : IsPGroup 2 T)
    (hBodd : Odd (Nat.card B)) (hBT : ∀ g : G, ∃ b ∈ B, ∃ t ∈ T, g = b * t) :
    Nat.card G = Nat.card B * Nat.card T := by
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card T) :=
    hk ▸ (Nat.coprime_two_left.2 hBodd).symm.pow_right k
  have hcompl : B.IsComplement' T := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      (disjoint_of_coprime_natCard hcop) ?_
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨b, hb, t, ht, rfl⟩ := hBT g
    exact Set.mul_mem_mul hb ht
  exact hcompl.card_mul_card.symm

private theorem uc22p22vb_pCore_le {T B : Subgroup G} (hT : IsPGroup 2 T)
    (hBodd : Odd (Nat.card B)) (hBT : ∀ g : G, ∃ b ∈ B, ∃ t ∈ T, g = b * t) :
    CFSG.pCore 2 G ≤ T := by
  have hidx : T.index = Nat.card B := by
    have h1 := Subgroup.card_mul_index T
    rw [uc22p22vb_card_eq hT hBodd hBT, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have h2 : ¬ 2 ∣ T.index := by
    rw [hidx, ← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.2 hBodd
  exact CFSG.pCore_isPGroup.le_sylow_of_normal (hT.toSylow h2)

omit [Finite G] in
private theorem uc22p22vb_pCore_quotient : CFSG.pCore 2 (G ⧸ CFSG.pCore 2 G) = ⊥ := by
  set N : Subgroup G := CFSG.pCore 2 G
  set K : Subgroup G := (CFSG.pCore 2 (G ⧸ N)).comap (QuotientGroup.mk' N)
  have hKp : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := G ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := G) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

private theorem uc22p22vb_fitting_odd (hO : CFSG.pCore 2 G = ⊥) :
    Odd (Nat.card (CFSG.fittingSubgroup G)) := by
  set F := CFSG.fittingSubgroup G
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥F) := inferInstance
  have hle : (P : Subgroup ↥F).map F.subtype ≤ CFSG.pCore 2 G :=
    Sylow.map_le_pCore CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent 2 P
  rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective] at hle
  have hc := Sylow.card_eq_multiplicity P
  rw [hle, Subgroup.card_bot] at hc
  have hF0 : Nat.card ↥F ≠ 0 := Nat.card_pos.ne'
  have hv : (Nat.card ↥F).factorization 2 = 0 :=
    Nat.pow_right_injective (le_refl 2) (hc.symm.trans (pow_zero 2).symm)
  have hnd : ¬ 2 ∣ Nat.card ↥F := fun h2 =>
    absurd ((Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hF0).1 h2) (by omega)
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hnd)

private theorem uc22p22vb_normal {T B : Subgroup G} (hT : IsPGroup 2 T)
    (hBab : IsMulCommutative B) (hBodd : Odd (Nat.card B))
    (hBT : ∀ g : G, ∃ b ∈ B, ∃ t ∈ T, g = b * t) : (CFSG.pCore 2 G ⊔ B).Normal := by
  classical
  set R : Subgroup G := CFSG.pCore 2 G
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card T) :=
    hk ▸ (Nat.coprime_two_left.2 hBodd).symm.pow_right k
  have hsolv : Group.IsSolvable G :=
    CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product B T inferInstance hT.isNilpotent
      hcop hBT
  haveI : Group.IsSolvable (G ⧸ R) := inferInstance
  let π : G →* G ⧸ R := QuotientGroup.mk' R
  set Fq : Subgroup (G ⧸ R) := CFSG.fittingSubgroup (G ⧸ R)
  have hFodd : Odd (Nat.card Fq) := uc22p22vb_fitting_odd uc22p22vb_pCore_quotient
  set Bb : Subgroup (G ⧸ R) := B.map π with hBb
  have hBbodd : Odd (Nat.card Bb) := Odd.of_dvd_nat hBodd (Subgroup.card_map_dvd B π)
  have hidx : Bb.index ∣ 2 ^ k := by
    have h1 : Bb.index ∣ B.index := Subgroup.index_map_dvd B (QuotientGroup.mk'_surjective R)
    have h2 : B.index = Nat.card T := by
      have h3 := Subgroup.card_mul_index B
      rw [uc22p22vb_card_eq hT hBodd hBT] at h3
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
    rw [h2, hk] at h1
    exact h1
  have hFB : Fq ≤ Bb := by
    haveI : Fq.Normal := CFSG.fittingSubgroup_normal
    set S : Subgroup (G ⧸ R) := Fq ⊔ Bb
    have hBS : Bb ≤ S := le_sup_right
    have h1 : Fq.relIndex S = Fq.relIndex Bb := Subgroup.relIndex_sup_left Bb Fq
    have h2 : Odd (Fq.relIndex S) := h1 ▸ Odd.of_dvd_nat hBbodd (Subgroup.relIndex_dvd_card Fq Bb)
    have h3 : Fq.relIndex S * Nat.card Fq = Nat.card S := by
      have := Subgroup.relIndex_mul_card Fq S
      rwa [inf_of_le_left le_sup_left] at this
    have h4 : Odd (Nat.card S) := h3 ▸ h2.mul hFodd
    have h5 : Bb.relIndex S * Nat.card Bb = Nat.card S := by
      have := Subgroup.relIndex_mul_card Bb S
      rwa [inf_of_le_left hBS] at this
    have h6 : Odd (Bb.relIndex S) := Odd.of_dvd_nat h4 (Dvd.intro _ h5)
    have h7 : Bb.relIndex S ∣ 2 ^ k := (Subgroup.relIndex_dvd_index_of_le hBS).trans hidx
    have h8 : Bb.relIndex S = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.2 h6).pow_right k) h7
    exact le_sup_left.trans (Subgroup.relIndex_eq_one.1 h8)
  have hBC : Bb ≤ Subgroup.centralizer (Fq : Set (G ⧸ R)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b₁, hb₁, rfl⟩ := hx
    obtain ⟨b₂, hb₂, rfl⟩ := hFB hy
    have := hBab.is_comm.comm (⟨b₁, hb₁⟩ : B) ⟨b₂, hb₂⟩
    rw [← map_mul, ← map_mul]
    exact congrArg (fun z : B => π z) this.symm
  have hBF : Bb ≤ Fq :=
    hBC.trans (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance)
  have hEq : Fq = Bb := le_antisymm hFB hBF
  have hcomap : Fq.comap π = B ⊔ R := by
    rw [hEq, hBb, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hnorm : (Fq.comap π).Normal := CFSG.fittingSubgroup_normal.comap π
  rwa [hcomap, sup_comm] at hnorm

private theorem uc22p22vb_conj {T B : Subgroup G} (hT : IsPGroup 2 T)
    (hBab : IsMulCommutative B) (hBodd : Odd (Nat.card B))
    (hBT : ∀ g : G, ∃ b ∈ B, ∃ t ∈ T, g = b * t) :
    ∀ t ∈ T, ∃ r ∈ CFSG.pCore 2 G, ∃ n ∈ T ⊓ Subgroup.normalizer (B : Set G), t = r * n := by
  intro t ht
  set R : Subgroup G := CFSG.pCore 2 G
  haveI : (R ⊔ B).Normal := uc22p22vb_normal hT hBab hBodd hBT
  have hRT : R ≤ T := uc22p22vb_pCore_le hT hBodd hBT
  have hRp : IsPGroup 2 R := CFSG.pCore_isPGroup
  set Y : Subgroup G := B.map (MulAut.conj t) with hY
  have hYcard : Nat.card Y = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hYR : R ⊔ Y = R ⊔ B := by
    have h1 : (R ⊔ B).map (MulAut.conj t) = R ⊔ B := Subgroup.Normal.map_conj_eq (R ⊔ B) t
    rwa [Subgroup.map_sup, Subgroup.Normal.map_conj_eq R t] at h1
  obtain ⟨a, ha⟩ := hRp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card R) (Nat.card B) :=
    ha ▸ (Nat.coprime_two_left.2 hBodd).pow_left a
  obtain ⟨e, he, hconj⟩ := CFSG.GH74.BNPair.exists_conj_of_complements (p := 2) hRp
    (fun h => (Nat.not_even_iff_odd.2 hBodd) (even_iff_two_dvd.2 h))
    (disjoint_of_coprime_natCard hcop) (disjoint_of_coprime_natCard (hYcard ▸ hcop)) hYR
  have hn : e * t ∈ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : B.map (MulAut.conj (e * t)) = Y.map (MulAut.conj e).toMonoidHom := by
      rw [hY, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [h1]
    exact hconj
  exact ⟨e⁻¹, R.inv_mem he, e * t, Subgroup.mem_inf.2 ⟨T.mul_mem (hRT he) ht, hn⟩, by group⟩

private theorem uc22p22vb_le_commutator_sup {P X : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hsolv : Group.IsSolvable ↥P)
    (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    P ≤ ⁅P, X⁆ ⊔ (P ⊓ Subgroup.centralizer (X : Set G)) := by
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := ↥X) (G := ↥P) hsolv hcop
  have hcommMap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hfixEq : CFSG.fixedPointSubgroup ↥X ↥P =
      (P ⊓ Subgroup.centralizer (X : Set G)).subgroupOf P := by
    simpa [CFSG.subgroupCentralizerIn] using
      CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn P X hXP
  intro x hx
  have htop : (⟨x, hx⟩ : ↥P) ∈ CFSG.fixedPointSubgroup ↥X ↥P ⊔
      CFSG.commutatorAction (A := ↥X) (G := ↥P) := by
    rw [hsup]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem P.subtype htop
  rw [Subgroup.map_sup, hcommMap, hfixEq, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hmap
  rw [sup_comm]
  exact hmap

private theorem uc22p22vb_comm_decomp {B : Subgroup G} (hBodd : Odd (Nat.card B)) :
    ∀ r ∈ CFSG.pCore 2 G, ∃ s ∈ ⁅CFSG.pCore 2 G, B⁆,
      ∃ c ∈ CFSG.pCore 2 G ⊓ Subgroup.centralizer (B : Set G), r = s * c := by
  intro r hr
  set R : Subgroup G := CFSG.pCore 2 G
  have hRp : IsPGroup 2 R := CFSG.pCore_isPGroup
  have hsolv : Group.IsSolvable ↥R := by
    haveI := hRp.isNilpotent
    infer_instance
  obtain ⟨a, ha⟩ := hRp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card R) :=
    ha ▸ (Nat.coprime_two_left.2 hBodd).symm.pow_right a
  have h1 := uc22p22vb_le_commutator_sup (Subgroup.le_normalizer_of_normal) hsolv hcop hr
  have h2 : R ⊓ Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer ((⁅R, B⁆ : Subgroup G) : Set G) :=
    inf_le_left.trans (Subgroup.normalizer_commutator_ge_left R B)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ h2] at h1
  obtain ⟨s, hs, c, hc, hsc⟩ := h1
  exact ⟨s, hs, c, hc, hsc.symm⟩

private theorem uc22p22vb_core {T B : Subgroup G} (hT : IsPGroup 2 T)
    (hBab : IsMulCommutative B) (hBodd : Odd (Nat.card B))
    (hBT : ∀ g : G, ∃ b ∈ B, ∃ t ∈ T, g = b * t) :
    (CFSG.pCore 2 G ⊔ B).Normal ∧ ∀ t ∈ T, ∃ s ∈ ⁅CFSG.pCore 2 G, B⁆,
      ∃ n ∈ T ⊓ Subgroup.normalizer (B : Set G), t = s * n := by
  refine ⟨uc22p22vb_normal hT hBab hBodd hBT, fun t ht => ?_⟩
  obtain ⟨r, hr, n, hn, rfl⟩ := uc22p22vb_conj hT hBab hBodd hBT t ht
  obtain ⟨s, hs, c, hc, rfl⟩ := uc22p22vb_comm_decomp hBodd r hr
  have hcT : c ∈ T := uc22p22vb_pCore_le hT hBodd hBT (Subgroup.mem_inf.1 hc).1
  have hcN : c ∈ Subgroup.normalizer (B : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.1 hc).2
  obtain ⟨hnT, hnN⟩ := Subgroup.mem_inf.1 hn
  exact ⟨s, hs, c * n, Subgroup.mem_inf.2 ⟨T.mul_mem hcT hnT, Subgroup.mul_mem _ hcN hnN⟩,
    mul_assoc _ _ _⟩

end Core

theorem uc22p22vb_five_six {H : Type} [Group H] [Finite H] (T B : Subgroup H) (hT : IsPGroup 2 T)
    (hBab : IsMulCommutative B) (hBodd : Odd (Nat.card B)) (hperm : Permutes B T) :
    ((pCoreOf 2 (B ⊔ T) ⊔ B).subgroupOf (B ⊔ T)).Normal ∧
      ∀ t ∈ T, ∃ s ∈ F05.sOf T B B, ∃ n ∈ T ⊓ Subgroup.normalizer (B : Set H), t = s * n := by
  set X : Subgroup H := B ⊔ T
  have hBX : B ≤ X := le_sup_left
  have hTX : T ≤ X := le_sup_right
  have hB' : (B.subgroupOf X).map X.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBX
  have hT' : IsPGroup 2 (T.subgroupOf X) := hT.comap_subtype
  have hBodd' : Odd (Nat.card (B.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv]
    exact hBodd
  have hBab' : IsMulCommutative (B.subgroupOf X) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (by
      have := congrArg Subtype.val (hBab.is_comm.comm (⟨a.1, a.2⟩ : B) ⟨b.1, b.2⟩)
      simpa using this))⟩⟩
  have hBT' : ∀ g : X, ∃ b ∈ B.subgroupOf X, ∃ t ∈ T.subgroupOf X, g = b * t := by
    intro g
    obtain ⟨b, hb, t, ht, hg⟩ := uc22p22vb_exists_mul_of_mem_sup hperm g.2
    exact ⟨⟨b, hBX hb⟩, hb, ⟨t, hTX ht⟩, ht, Subtype.ext hg⟩
  obtain ⟨hnorm, hconj⟩ := uc22p22vb_core hT' hBab' hBodd' hBT'
  refine ⟨?_, fun t ht => ?_⟩
  · have h1 : (pCoreOf 2 X ⊔ B).subgroupOf X = CFSG.pCore 2 X ⊔ B.subgroupOf X := by
      have h2 : pCoreOf 2 X ⊔ B = (CFSG.pCore 2 X ⊔ B.subgroupOf X).map X.subtype := by
        rw [Subgroup.map_sup, hB']
        rfl
      rw [h2]
      exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rwa [h1]
  · obtain ⟨s, hs, n, hn, hsn⟩ := hconj ⟨t, hTX ht⟩ ht
    refine ⟨(s : H), ?_, (n : H), ?_, congrArg Subtype.val hsn⟩
    · have h2 := Subgroup.mem_map_of_mem X.subtype hs
      rw [Subgroup.map_commutator, hB'] at h2
      exact h2
    · obtain ⟨hnT, hnN⟩ := Subgroup.mem_inf.1 hn
      refine Subgroup.mem_inf.2 ⟨hnT, ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro h
      by_cases hhX : h ∈ X
      · exact Subgroup.mem_normalizer_iff.1 hnN ⟨h, hhX⟩
      · refine ⟨fun hb => absurd (hBX hb) hhX, fun hb => absurd ?_ hhX⟩
        have h3 : (n : H)⁻¹ * ((n : H) * h * (n : H)⁻¹) * (n : H) ∈ X :=
          X.mul_mem (X.mul_mem (X.inv_mem n.2) (hBX hb)) n.2
        simpa [mul_assoc] using h3

end CFSG.LocalAnalysis.UniquenessCase.UC22
