module

public import CFSG.RankThree.PartTwo.Sec20.OneFrontierCleanStatements
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofTheta
import CFSG.RankThree.PartTwo.Sec18.Rem187
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofKlein
import CFSG.RankThree.PartTwo.Sec4.T444.Step452
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

namespace Res5

variable {G : Type} [Group G] [Finite G]

theorem mem_pCore_of_isSimpleGroup {M K : Subgroup G} (hKM : K ≤ M)
    (hMK : M ≤ Subgroup.normalizer (K : Set G))
    (hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hperf : Group.IsPerfect ↥K) :
    ∀ r ∈ Sec4.oTwoP 3 ↥M, r ∈ K.subgroupOf M → r ∈ CFSG.pCore 2 ↥M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := Sec4.oTwoP 3 ↥M with hR
  set K' := K.subgroupOf M with hK'
  have hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK
  have hRn : R.Normal := Subgroup.Normal.comap inferInstance _
  set ι : ↥K →* ↥M := Subgroup.inclusion hKM with hι
  have hιinj : Function.Injective ι := Subgroup.inclusion_injective hKM
  set J := (R ⊓ K').comap ι with hJ
  have hJn : J.Normal := Subgroup.Normal.comap inferInstance ι
  have hRsol : Group.IsSolvable ↥R := Sec4.isSolvable_oTwoP 3
  have hJsol : Group.IsSolvable ↥J := by
    let f : ↥J →* ↥R := (ι.comp J.subtype).codRestrict R fun x => x.2.1
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply hιinj
      exact congrArg Subtype.val hxy
    exact Group.isSolvable_of_isSolvable_injective hf
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hJbn : (J.map π).Normal := Subgroup.Normal.map hJn π (QuotientGroup.mk'_surjective _)
  have hJbsol : Group.IsSolvable ↥(J.map π) := by
    let f : ↥J →* ↥(J.map π) := (π.comp J.subtype).codRestrict _ fun x => ⟨x, x.2, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    exact Group.isSolvable_of_surjective hf
  have hJb : J.map π = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.map π) with h | h
    · exact h
    · exfalso
      have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := Group.IsPerfect.ofSurjective
        (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K))
      have hsol : Group.IsSolvable (↥K ⧸ CFSG.pCore 2 ↥K) := by
        rw [h] at hJbsol
        exact Group.isSolvable_of_surjective
          (f := (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)).subtype)
          (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
      have : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K) := hsimple.toNontrivial
      exact Group.IsPerfect.not_isSolvable (↥K ⧸ CFSG.pCore 2 ↥K) hsol
  have hJO : J ≤ CFSG.pCore 2 ↥K := by
    intro x hx
    have : π x ∈ J.map π := ⟨x, hx, rfl⟩
    rw [hJb, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  have hOKM : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKM)
      (hMK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  intro r hr hrK
  have hk' : r = ι ⟨(r : G), hrK⟩ := rfl
  have hJmem : (⟨(r : G), hrK⟩ : ↥K) ∈ J := by
    show ι _ ∈ R ⊓ K'
    rw [← hk']
    exact ⟨hr, hrK⟩
  have h1 := (Sec18.mem_pCore_iff_mem_pCoreOf _).mp (hJO hJmem)
  rw [Sec18.mem_pCore_iff_mem_pCoreOf]
  exact hOKM h1

theorem conj_mem_centralizer_of_normal {X : Type*} [Group X] {Q : Subgroup X} (hQ : Q.Normal)
    {z : X} (hz : ∀ q ∈ Q, z * q = q * z) (g : X) :
    ∀ q ∈ Q, (g * z * g⁻¹) * q = q * (g * z * g⁻¹) := by
  intro q hq
  have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ Q := hQ.conj_mem q hq g⁻¹
  have h1 := hz _ hq'
  calc (g * z * g⁻¹) * q = g * (z * (g⁻¹ * q * g⁻¹⁻¹)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * q * g⁻¹⁻¹) * z) * g⁻¹ := by rw [h1]
    _ = q * (g * z * g⁻¹) := by group

theorem exists_conj_eq_of_hyp201One (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) {y z : G} (hy : y ∈ A ⊓ L)
    (hy1 : y ≠ 1) (hz : z ∈ A ⊓ L) (hz1 : z ≠ 1) :
    ∃ n ∈ L, n ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧ n * y * n⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := nonempty_quotient_of_hyp201One h184 h
  set O := CFSG.pCore 2 ↥L with hO
  set π := QuotientGroup.mk' O with hπ
  set S := (A ⊓ L).subgroupOf L with hS
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) :=
    (isSylowOf_three_inf_of_hyp201One h1812 h184 h).isPGroup
  have hS3 : IsPGroup 3 S := hB3.comap_subtype
  have hinj : Set.InjOn π (S : Set ↥L) := by
    intro u hu v hv huv
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at huv
    have hmem : u⁻¹ * v ∈ S ⊓ O := ⟨S.mul_mem (S.inv_mem hu) hv, huv⟩
    rw [Subgroup.eq_bot_of_card_eq _ (card_inf_eq_one_of_isPGroup hS3 CFSG.pCore_isPGroup),
      Subgroup.mem_bot] at hmem
    exact eq_of_inv_mul_eq_one hmem
  set χ := φ.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with hχ
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hE : Nat.card ((S.map π).map χ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective χ.injective]
    exact card_map_inf_of_hyp201One h1812 h184 h
  have hyS : (⟨y, hy.2⟩ : ↥L) ∈ S := hy
  have hzS : (⟨z, hz.2⟩ : ↥L) ∈ S := hz
  have hne : ∀ x : ↥L, x ∈ S → (x : G) ≠ 1 → χ (π x) ≠ 1 := by
    intro x hxS hx1 hχx
    rw [MulEquiv.map_eq_one_iff] at hχx
    apply hx1
    have hx := hinj hxS (one_mem _) (hχx.trans (map_one _).symm)
    rw [hx]
    rfl
  obtain ⟨n', hn', hn'e⟩ := KFacts.L34.exists_mem_normalizer_conj_eq_of_card_eq_nine hk hE
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hyS)) (hne _ hyS hy1)
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hzS)) (hne _ hzS hz1)
  have hn'' : χ.symm n' ∈ Subgroup.normalizer ((S.map π : Subgroup (↥L ⧸ O)) : Set (↥L ⧸ O)) := by
    have h1 : n' ∈ (Subgroup.normalizer ((S.map π : Subgroup (↥L ⧸ O)) : Set (↥L ⧸ O))).map
        χ.toMonoidHom := by
      rw [Subgroup.map_equiv_normalizer_eq]
      exact hn'
    obtain ⟨m, hm, hmn⟩ := h1
    rw [← hmn]
    simpa using hm
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective O (χ.symm n')
  have hxN : QuotientGroup.mk' O x ∈ Subgroup.normalizer
      ((S.map π : Subgroup (↥L ⧸ O)) : Set (↥L ⧸ O)) := by
    rw [hx]
    exact hn''
  obtain ⟨w, hw, m, hmB, hxwm⟩ := exists_mul_of_mk_mem_normalizer inf_le_right hB3 hxN
  refine ⟨(m : G), m.2, hmB, ?_⟩
  have hwB : π w ∈ S.map π := by
    have h1 : (S ⊔ O).map π = S.map π := by
      rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff O).mpr (by rw [QuotientGroup.ker_mk']),
        sup_bot_eq]
    rw [← h1]
    exact Subgroup.mem_map_of_mem π hw
  have hcomm : ∀ a ∈ S.map π, ∀ b ∈ S.map π, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hab : a * b = b * a := Subtype.ext (by
      have := congrArg Subtype.val
        (h.1.mem_partTwoE.1.1.is_comm.comm ⟨(a : G), ha.1⟩ ⟨(b : G), hb.1⟩)
      simpa using this)
    rw [← map_mul, ← map_mul, hab]
  have hmy : m * ⟨y, hy.2⟩ * m⁻¹ ∈ S := by
    rw [hS, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp hmB y).mp hy
  have hn : n' = χ (π x) := by
    rw [hπ, hx, MulEquiv.apply_symm_apply]
  have heq : π (m * ⟨y, hy.2⟩ * m⁻¹) = π ⟨z, hz.2⟩ := by
    have h2 : χ (π x * π ⟨y, hy.2⟩ * (π x)⁻¹) = χ (π ⟨z, hz.2⟩) := by
      rw [map_mul, map_mul, map_inv, ← hn]
      exact hn'e
    have h3 := χ.injective h2
    rw [hxwm, map_mul] at h3
    have h5 : π w * π ⟨z, hz.2⟩ = π ⟨z, hz.2⟩ * π w :=
      hcomm _ hwB _ (Subgroup.mem_map_of_mem π hzS)
    rw [map_mul, map_mul, map_inv]
    calc π m * π ⟨y, hy.2⟩ * (π m)⁻¹
        = (π w)⁻¹ * (π w * π m * π ⟨y, hy.2⟩ * (π w * π m)⁻¹) * π w := by group
      _ = (π w)⁻¹ * π ⟨z, hz.2⟩ * π w := by rw [h3]
      _ = (π w)⁻¹ * (π w * π ⟨z, hz.2⟩) := by rw [mul_assoc, ← h5]
      _ = π ⟨z, hz.2⟩ := by group
  have := hinj hmy hzS heq
  simpa using congrArg Subtype.val this

end Res5

theorem item203One1_of_items
    (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1) (h185 : Sec18.Item185)
    (h189 : Sec18.Item189) : Item203One1 := by
  intro G _ _ A M L N c h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H, hH18, hH187, hL, -⟩ := exists_sec18H_of_hyp201One h
  set B := A ⊓ L with hBdef
  set K := normalClosureIn M c with hKdef
  have hAM : A ≤ M := le_of_hyp201 h.1
  have hBM : B ≤ M := inf_le_left.trans hAM
  have hcA : c ∈ A := mem_of_hyp201 h.1
  have hcM : c ∈ M := hAM hcA
  have hA := isE27_of_mem_partTwoE h.1.mem_partTwoE
  have hB9 : Nat.card B = 9 := card_inf_of_hyp201One h1812 h184 h
  have hNB : Subgroup.normalizer (B : Set G) ≤ M := normalizer_inf_le_of_hyp201One h hB9
  have hB3 : IsPGroup 3 B := (isSylowOf_three_inf_of_hyp201One h1812 h184 h).isPGroup
  have h185' : B ≤ (Sec4.oTwoP 3 ↥M).map M.subtype := by
    have := h185 G A M H c hH18
    rw [← hL] at this
    exact this
  obtain ⟨⟨hKC, -⟩, -, hcase⟩ := h189 G A M H c hH18 hH187
  have hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases hcase with ⟨n, -, ⟨e⟩, -⟩ | ⟨n, hn, hn0, ⟨e⟩, -⟩
    · have : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
          (GaloisField 2 n)) :=
        CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
      exact (e.trans (KFacts.L34.projSLEquivProjectiveSL 3 _)).isSimpleGroup
    · have : IsSimpleGroup ↥(projSL 2 (GaloisField 2 n)) :=
        Sec11.LSSolvableProof.isSimpleGroup_projSL (by obtain ⟨k, hk⟩ := hn; omega)
      exact e.isSimpleGroup
  have hKperf : Group.IsPerfect ↥K := isPerfect_of_mem_oTwoComponentsIn hKC
  have hKM : K ≤ M := by
    rw [hKdef, normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    exact M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm)
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hK1 : K ≠ ⊥ := Sec18.ne_bot_of_mem_oTwoComponentsIn hKC
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hK1
    rw [eq_bot_iff, hKdef, normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨m, -, rfl⟩
    simp
  have hc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  set P2 := CFSG.pCore 2 ↥M with hP2
  set π := QuotientGroup.mk' P2 with hπ
  set Q := CFSG.pCore 3 (↥M ⧸ P2) with hQ
  set B' := B.subgroupOf M with hB'
  set Bs := B'.map π with hBs
  set c' : ↥M := ⟨c, hcM⟩ with hc'
  have hQn : Q.Normal := CFSG.pCore_normal
  have hQ3 : IsPGroup 3 Q := CFSG.pCore_isPGroup
  have hP22 : IsPGroup 2 P2 := CFSG.pCore_isPGroup
  have hP23 : ¬ 3 ∣ Nat.card P2 := by
    obtain ⟨k, hk⟩ := hP22.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hB'R : B' ≤ Sec4.oTwoP 3 ↥M := by
    intro b hb
    obtain ⟨b', hb', hbb'⟩ := h185' hb
    have : b' = b := Subtype.ext hbb'
    rw [← this]
    exact hb'
  have hBsQ : Bs ≤ Q := Subgroup.map_le_iff_le_comap.mpr hB'R
  have hB'3 : IsPGroup 3 B' := hB3.comap_subtype
  have hinj : Set.InjOn π (B' : Set ↥M) := by
    intro u hu v hv huv
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at huv
    have hmem : u⁻¹ * v ∈ B' ⊓ P2 := ⟨B'.mul_mem (B'.inv_mem hu) hv, huv⟩
    rw [Subgroup.eq_bot_of_card_eq _ (card_inf_eq_one_of_isPGroup hB'3 hP22),
      Subgroup.mem_bot] at hmem
    exact eq_of_inv_mul_eq_one hmem
  have hBs9 : Nat.card Bs = 9 := by
    rw [hBs, Sec13.card_map_eq_of_injOn _ hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv, hB9]
  have hBsel : CFSG.Assembly.IsElemAbelian 3 Bs := by
    have hB'el : CFSG.Assembly.IsElemAbelian 3 B' := by
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · simpa using congrArg Subtype.val (hA.1.1.is_comm.comm ⟨((a : ↥M) : G), a.2.1⟩
          ⟨((b : ↥M) : G), b.2.1⟩)
      · simpa using hA.1.2 _ hx.1
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π B' hB'el
  have hRK := Res5.mem_pCore_of_isSimpleGroup hKM hMK hsimple hKperf
  have hc'K : c' ∈ K.subgroupOf M := self_mem_normalClosureIn M c
  have hK'n : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK
  have hRn : (Sec4.oTwoP 3 ↥M).Normal := Subgroup.Normal.comap inferInstance _
  have hcQ : ∀ q ∈ Q, π c' * q = q * π c' := by
    intro q hq
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective P2 q
    have hr : r ∈ Sec4.oTwoP 3 ↥M := hq
    have hcomm : ⁅c', r⁆ ∈ CFSG.pCore 2 ↥M := by
      refine hRK _ ?_ ?_
      · rw [commutatorElement_def]
        exact (Sec4.oTwoP 3 ↥M).mul_mem (hRn.conj_mem _ hr c') ((Sec4.oTwoP 3 ↥M).inv_mem hr)
      · rw [commutatorElement_def, show c' * r * c'⁻¹ * r⁻¹ = c' * (r * c'⁻¹ * r⁻¹) by group]
        exact (K.subgroupOf M).mul_mem hc'K (hK'n.conj_mem _ ((K.subgroupOf M).inv_mem hc'K) r)
    have h1 : π ⁅c', r⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : π c' * π r = π r * π c' := by
      calc π c' * π r = (π c' * π r * (π c')⁻¹ * (π r)⁻¹) * (π r * π c') := by group
        _ = π r * π c' := by rw [h1, one_mul]
    exact h2
  have hcnQ : π c' ∉ Q := by
    intro hq
    have hr : c' ∈ Sec4.oTwoP 3 ↥M := hq
    have hP := hRK c' hr hc'K
    obtain ⟨k, hk⟩ := hP22 ⟨c', hP⟩
    have h2 : c ^ 2 ^ k = 1 := by
      have := congrArg (fun x : ↥P2 => ((x : ↥M) : G)) hk
      simpa [hc'] using this
    have h3 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
    rw [hc] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hπc3 : (π c') ^ 3 = 1 := by
    rw [← map_pow]
    have : c' ^ 3 = 1 := Subtype.ext (by simpa [hc'] using hc3)
    rw [this, map_one]
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ P2)) ≤ 3 := by
    rw [Res5.pRank_top_quotient_eq P2 hP23,
      ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3 (by norm_num) M]
    obtain ⟨P, hP, hP2', hMP⟩ := h.1.mem_scriptM.1.1
    exact (Sec18.pRank_le_localRank_of_isTwoLocal Nat.prime_three ⟨P, hP, hP2', hMP⟩).trans
      h.1.toTheoremFourHyp.localRank_three.le
  have hkey : ∀ z ∈ Q, (∀ q ∈ Q, z * q = q * z) → z ^ 3 = 1 → z ∈ Bs := by
    intro z hzQ hzc hz3
    by_contra hzB
    obtain ⟨hE1, hE1c⟩ := Sec5.isElemAbelian_sup_zpowers hBsel hzB hz3
      (fun a ha => (hzc a (hBsQ ha)).symm)
    have hE1Q : Bs ⊔ Subgroup.zpowers z ≤ Q := sup_le hBsQ (Subgroup.zpowers_le.mpr hzQ)
    have hcE1 : π c' ∉ Bs ⊔ Subgroup.zpowers z := fun h' => hcnQ (hE1Q h')
    obtain ⟨hE2, hE2c⟩ := Sec5.isElemAbelian_sup_zpowers hE1 hcE1 hπc3
      (fun a ha => (hcQ a (hE1Q ha)).symm)
    have hcard : Nat.card ((Bs ⊔ Subgroup.zpowers z) ⊔ Subgroup.zpowers (π c') :
        Subgroup (↥M ⧸ P2)) = 3 ^ 4 := by
      rw [hE2c, hE1c, hBs9]
      norm_num
    have := CFSG.SectionRank.le_pRank (by norm_num) (le_top : ((Bs ⊔ Subgroup.zpowers z) ⊔
      Subgroup.zpowers (π c') : Subgroup (↥M ⧸ P2)) ≤ ⊤) hE2 hcard
    omega
  have hQnt : Nontrivial ↥Q := by
    obtain ⟨x, hx, hx1⟩ : ∃ x ∈ Bs, x ≠ 1 := by
      by_contra hno
      push Not at hno
      have : Bs = ⊥ := (Subgroup.eq_bot_iff_forall Bs).mpr hno
      rw [this, Subgroup.card_bot] at hBs9
      omega
    exact ⟨⟨⟨x, hBsQ hx⟩, 1, fun h' => hx1 (congrArg Subtype.val h')⟩⟩
  have hZnt : Nontrivial ↥(Subgroup.center ↥Q) := hQ3.center_nontrivial
  have hZ3 : IsPGroup 3 ↥(Subgroup.center ↥Q) := hQ3.to_subgroup _
  have h3dvd : 3 ∣ Nat.card ↥(Subgroup.center ↥Q) := by
    obtain ⟨m, hm⟩ := hZ3.exists_card_eq
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' (by simpa using hm)
    rw [hm]
    exact dvd_pow_self 3 hm0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥Q)) 3 h3dvd
  set z₀ : ↥M ⧸ P2 := ((w : ↥Q) : ↥M ⧸ P2) with hz₀
  have hz₀Q : z₀ ∈ Q := (w : ↥Q).2
  have hz₀c : ∀ q ∈ Q, z₀ * q = q * z₀ := by
    intro q hq
    have := Subgroup.mem_center_iff.mp w.2 ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  have hz₀3 : z₀ ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one w
    rw [hw] at h1
    have := congrArg (fun x : ↥(Subgroup.center ↥Q) => ((x : ↥Q) : ↥M ⧸ P2)) h1
    simpa [hz₀] using this
  have hz₀1 : z₀ ≠ 1 := by
    intro h1
    have : w = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hw
    omega
  obtain ⟨b₀, hb₀B, hb₀z⟩ := hkey z₀ hz₀Q hz₀c hz₀3
  have hb₀1 : (b₀ : G) ≠ 1 := by
    intro h1
    apply hz₀1
    rw [← hb₀z, show b₀ = 1 from Subtype.ext h1, map_one]
  have hBsZ : ∀ x ∈ Bs, ∀ q ∈ Q, x * q = q * x := by
    rintro _ ⟨b, hbB, rfl⟩
    by_cases hb1 : (b : G) = 1
    · have : b = 1 := Subtype.ext hb1
      intro q _
      rw [this, map_one, one_mul, mul_one]
    obtain ⟨n, -, hnB, hnb⟩ := Res5.exists_conj_eq_of_hyp201One h1812 h184 h hb₀B hb₀1 hbB hb1
    have hnM : n ∈ M := hNB hnB
    have hconj : π ⟨n, hnM⟩ * z₀ * (π ⟨n, hnM⟩)⁻¹ = π b := by
      rw [← hb₀z, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simpa using hnb)
    rw [← hconj]
    exact Res5.conj_mem_centralizer_of_normal hQn hz₀c _
  have hBsn : Bs.Normal := by
    refine ⟨fun x hx g => ?_⟩
    refine hkey _ (hQn.conj_mem x (hBsQ hx) g)
      (Res5.conj_mem_centralizer_of_normal hQn (hBsZ x hx) g) ?_
    rw [conj_pow, hBsel.2 x hx, mul_one, mul_inv_cancel]
  have hCn : (Bs.comap π).Normal := Subgroup.Normal.comap hBsn π
  have hC : (Bs.comap π).map M.subtype = B ⊔ CFSG.Open.pCoreOf 2 M := by
    rw [hBs, Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hBM, hP2]
    rfl
  intro m hm
  rw [← hC]
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, hCn.conj_mem y hy ⟨m, hm⟩, rfl⟩

end CFSG.RankThree.PartTwo.Sec20
