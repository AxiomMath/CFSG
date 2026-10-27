module

public import CFSG.RankThree.GF2n.Tim81.Sec4.FrobBound
public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec42Cond
public import CFSG.RankThree.GF2n.Tim81.Sec4.SL2Borel
public import CFSG.RankThree.GF2n.Tim81.Sec4.SzWeaklyClosed
public import CFSG.RankThree.GF2n.Tim81.Sec4.CentralTIBasic
public import CFSG.CGT.Timmesfeld75.Sec213
public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.RankThree.GF2n.Tim81.Sec4
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

theorem IsL2OrSzGroup.isConj_of_sq_eq_one
    {X : Type} [Group X] (hX : IsL2OrSzGroup X) {x y : X}
    (hx : x * x = 1) (hx1 : x ≠ 1) (hy : y * y = 1) (hy1 : y ≠ 1) : IsConj x y := by
  rcases hX with ⟨F, hField, hFintype, hCharP, -, ⟨e⟩⟩ |
    ⟨a, F, hField, hFintype, hCharP, -, hcard, ⟨e⟩⟩
  · letI := hField
    letI := hFintype
    letI := hCharP
    suffices h : IsConj (e x) (e y) by simpa using e.symm.toMonoidHom.map_isConj h
    have hx' : e x * e x = 1 := by rw [← map_mul, hx, map_one]
    have hx1' : e x ≠ 1 := fun h => hx1 (e.injective (by rw [h, map_one]))
    have hy' : e y * e y = 1 := by rw [← map_mul, hy, map_one]
    have hy1' : e y ≠ 1 := fun h => hy1 (e.injective (by rw [h, map_one]))
    exact isConj_of_mul_self_eq_one hx' hx1' hy' hy1'
  · letI := hField
    letI := hFintype
    letI := hCharP
    suffices h : IsConj (e x) (e y) by simpa using e.symm.toMonoidHom.map_isConj h
    have hx' : e x * e x = 1 := by rw [← map_mul, hx, map_one]
    have hx1' : e x ≠ 1 := fun h => hx1 (e.injective (by rw [h, map_one]))
    have hy' : e y * e y = 1 := by rw [← map_mul, hy, map_one]
    have hy1' : e y ≠ 1 := fun h => hy1 (e.injective (by rw [h, map_one]))
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [Nat.card_eq_fintype_card]; exact hcard
    have hxo : orderOf (e x) = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1'
    have hyo : orderOf (e y) = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1'
    exact CFSG.QuasithinUnique.Setup.Family.suzuki_involutions_conjugate (a := a) (K := F)
      hK (e x) (e y) hxo hyo

private theorem map_sq_eq_one {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {S : Subgroup X}
    (h : ∀ x ∈ S, x * x = 1) : ∀ x ∈ S.map e.toMonoidHom, x * x = 1 := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
  rw [← map_mul, h z hz, map_one]

namespace RootHyp

private theorem weaklyClosed_imgK_self (h : RootHyp M V) (hPH : Pc M V ≤ H) :
    ∀ g : HBar V H, conjSubgroup g (imgK V H (Pc M V)) ≤
        Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) →
      conjSubgroup g (imgK V H (Pc M V)) = imgK V H (Pc M V) := by
  intro g hg
  obtain ⟨z, rfl⟩ := piK_surjective V H g
  rw [← imgK_conjSubgroup z.2 hPH] at hg ⊢
  exact weaklyClosed_imgK h hPH z.2 hg

private theorem exists_frobeniusComplement_pullback {X : Type} [Group X]
    (e : HBar V H ≃* X) (D : Subgroup X)
    (hDle : D ≤ Subgroup.normalizer
      (((imgK V H (Pc M V)).map e.toMonoidHom) : Set X))
    (hDcard : Nat.card D = Nat.card ((imgK V H (Pc M V)).map e.toMonoidHom) - 1)
    (hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hDfpf : ∀ d ∈ D, d ≠ 1 → ∀ x ∈ (imgK V H (Pc M V)).map e.toMonoidHom,
      d * x * d⁻¹ = x → x = 1) :
    ∃ R : Subgroup (HBar V H), R ≤ Subgroup.normalizer
        (imgK V H (Pc M V) : Set (HBar V H)) ∧
      Nat.card R = Nat.card (imgK V H (Pc M V)) - 1 ∧
      (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧
      (∀ r ∈ R, r ≠ 1 → ∀ x ∈ imgK V H (Pc M V), r * x * r⁻¹ = x → x = 1) := by
  refine ⟨D.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hconv : e.symm.toMonoidHom d * x * (e.symm.toMonoidHom d)⁻¹ =
        e.symm (d * e x * d⁻¹) := by
      conv_lhs => rw [← e.symm_apply_apply x]
      simp
    have key : ∀ y : HBar V H, y ∈ imgK V H (Pc M V) ↔
        e y ∈ (imgK V H (Pc M V)).map e.toMonoidHom := by
      intro y
      rw [Subgroup.mem_map_equiv]
      simp
    rw [key x, hconv, key (e.symm (d * e x * d⁻¹)), e.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff.mp (hDle hd) (e x)
  · have h1 : Nat.card ↥(D.map e.symm.toMonoidHom) = Nat.card ↥D :=
      Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective
    have h2 : Nat.card ↥((imgK V H (Pc M V)).map e.toMonoidHom) =
        Nat.card ↥(imgK V H (Pc M V)) :=
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    rw [h1, hDcard, h2]
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hDcomm a' ha' b' hb']
  · intro r hr hr1 x hx hfix
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hr
    have hd1 : d ≠ 1 := fun h => hr1 (by rw [h, map_one])
    have hx' : e x ∈ (imgK V H (Pc M V)).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hx
    have hfix' : d * e x * d⁻¹ = e x := by
      have h := congrArg e hfix
      simpa using h
    exact e.injective (by rw [hDfpf d hd hd1 (e x) hx' hfix', map_one])

theorem exists_frobeniusComplement_imgK
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) (hL : IsL2OrSz V H) :
    ∃ R : Subgroup (HBar V H), R ≤ Subgroup.normalizer
        (imgK V H (Pc M V) : Set (HBar V H)) ∧
      Nat.card R = Nat.card (imgK V H (Pc M V)) - 1 ∧
      (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧
      (∀ r ∈ R, r ≠ 1 → ∀ x ∈ imgK V H (Pc M V), r * x * r⁻¹ = x → x = 1) := by
  classical
  have hE := isElemAbelian_imgK h hPH hVH
  have hsq : ∀ x ∈ imgK V H (Pc M V), x * x = 1 := fun x hx => by
    simpa [pow_two] using hE.2 x hx
  have hTp : IsPGroup 2 (imgK V H (Pc M V)) := isPGroup_two_of_isElemAbelian hE
  have hne : imgK V H (Pc M V) ≠ ⊥ := (imgK_ne_bot_and_ne_of_sup h hPH hH hnM).1
  have hwc := weaklyClosed_imgK_self h hPH
  rcases hL with ⟨F, hField, hFintype, hCharP, -, ⟨e⟩⟩ |
    ⟨a, F, hField, hFintype, hCharP, -, hcard, ⟨e⟩⟩
  · letI := hField
    letI := hFintype
    letI := hCharP
    have hTp' : IsPGroup 2 ((imgK V H (Pc M V)).map e.toMonoidHom) := hTp.map e.toMonoidHom
    have hTne' : (imgK V H (Pc M V)).map e.toMonoidHom ≠ ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ e.injective).not.mpr hne
    have hTwc' := CentralTI.weaklyClosed_map_mulEquiv e hwc
    obtain ⟨D, hDle, hDcard, hDcomm, hDfpf⟩ := exists_frobeniusComplement hTp' hTne' hTwc'
    exact exists_frobeniusComplement_pullback e D hDle hDcard hDcomm hDfpf
  · letI := hField
    letI := hFintype
    letI := hCharP
    have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [Nat.card_eq_fintype_card]; exact hcard
    have hTp' : IsPGroup 2 ((imgK V H (Pc M V)).map e.toMonoidHom) := hTp.map e.toMonoidHom
    have hTne' : (imgK V H (Pc M V)).map e.toMonoidHom ≠ ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ e.injective).not.mpr hne
    have hsq' := map_sq_eq_one e hsq
    have hTwc' := CentralTI.weaklyClosed_map_mulEquiv e hwc
    obtain ⟨D, hDle, hDcard, hDcomm, hDfpf⟩ :=
      exists_frobeniusComplement_sz hK hTp' hTne' hsq' hTwc'
    exact exists_frobeniusComplement_pullback e D hDle hDcard hDcomm hDfpf

theorem card_Pc_inf_kOf_le_of_isL2OrSz
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) (hL : IsL2OrSz V H) :
    Nat.card ↥(Pc M V ⊓ kOf V H) ≤ Nat.card (imgK V H (Pc M V)) * Nat.card V := by
  obtain ⟨R, hRN, hRcard, hRc, hfrob⟩ := exists_frobeniusComplement_imgK h hPH hVH hH hnM hL
  exact card_Pc_inf_kOf_le h hPH hVH hH hnM hK hab hRN hRcard hRc hfrob

private theorem exists_swap_imgK_sl2
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hyH : y ∈ H)
    (hTne : imgK V H (Pc M V) ≠ ⊥)
    (hne : imgK V H (Pc M V) ≠ imgK V H (conjSubgroup y (Pc M V)))
    {F : Type} [Field F] [Fintype F] [CharP F 2] (e : HBar V H ≃* SL(2, F)) :
    ∃ t : HBar V H, t * t = 1 ∧ t ≠ 1 ∧
      conjSubgroup t (imgK V H (Pc M V)) = imgK V H (conjSubgroup y (Pc M V)) ∧
      conjSubgroup t (imgK V H (conjSubgroup y (Pc M V))) = imgK V H (Pc M V) := by
  classical
  have hTp : IsPGroup 2 (imgK V H (Pc M V)) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_imgK h hPH hVH)
  have hwc := weaklyClosed_imgK_self h hPH
  set g : HBar V H := piK V H ⟨y, hyH⟩ with hg
  have hT'eq : imgK V H (conjSubgroup y (Pc M V)) = conjSubgroup g (imgK V H (Pc M V)) := by
    rw [hg]
    exact imgK_conjSubgroup hyH hPH
  have hne' : imgK V H (Pc M V) ≠ conjSubgroup g (imgK V H (Pc M V)) := by
    rw [← hT'eq]
    exact hne
  set T : Subgroup SL(2, F) := (imgK V H (Pc M V)).map e.toMonoidHom with hTdef
  have hTpe : IsPGroup 2 T := hTp.map e.toMonoidHom
  have hTnee : T ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ e.injective).not.mpr hTne
  have hTwe := CentralTI.weaklyClosed_map_mulEquiv e hwc
  have hT'eqe : (imgK V H (conjSubgroup y (Pc M V))).map e.toMonoidHom =
      conjSubgroup (e g) T := by
    rw [hT'eq, map_conjSubgroup_mulEquiv e, hTdef]
  have hT'pe : IsPGroup 2 (conjSubgroup (e g) T) :=
    hTpe.map (MulAut.conj (e g)).toMonoidHom
  have hT'nee : conjSubgroup (e g) T ≠ ⊥ := by
    rw [← hT'eqe, hT'eq]
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).not.mpr
      ((conjSubgroup_eq_bot_iff (g := g)).not.mpr hTne)
  have hT'wee := CentralTI.weaklyClosed_map_mulEquiv (MulAut.conj (e g)) hTwe
  have hne'' : T ≠ conjSubgroup (e g) T := by
    intro hEq
    apply hne'
    have h1 : imgK V H (Pc M V) = conjSubgroup g (imgK V H (Pc M V)) := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [map_conjSubgroup_mulEquiv e]
      simpa [hTdef] using hEq
    exact h1
  obtain ⟨s, hss, hs1, hswap1, hswap2⟩ :=
    exists_involution_conj_eq_of_weaklyClosed_ne hTpe hTnee hTwe hT'pe hT'nee hT'wee hne''
  refine ⟨e.symm s, ?_, ?_, ?_, ?_⟩
  · apply e.injective
    simpa using hss
  · intro h1
    exact hs1 (by rw [← e.apply_symm_apply s, h1, map_one])
  · refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
    rw [map_conjSubgroup_mulEquiv e, e.apply_symm_apply, hT'eqe]
    exact hswap1
  · refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
    rw [map_conjSubgroup_mulEquiv e, e.apply_symm_apply, hT'eqe]
    exact hswap2

private theorem exists_swap_imgK_sz
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hyH : y ∈ H)
    (hTne : imgK V H (Pc M V) ≠ ⊥)
    (hne : imgK V H (Pc M V) ≠ imgK V H (conjSubgroup y (Pc M V)))
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hcard : Fintype.card F = 2 ^ (2 * a + 1))
    (e : HBar V H ≃* CFSG.Blueprint.suzukiGroup a F) :
    ∃ t : HBar V H, t * t = 1 ∧ t ≠ 1 ∧
      conjSubgroup t (imgK V H (Pc M V)) = imgK V H (conjSubgroup y (Pc M V)) ∧
      conjSubgroup t (imgK V H (conjSubgroup y (Pc M V))) = imgK V H (Pc M V) := by
  classical
  have hTp : IsPGroup 2 (imgK V H (Pc M V)) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_imgK h hPH hVH)
  have hsq : ∀ x ∈ imgK V H (Pc M V), x * x = 1 := fun x hx => by
    simpa [pow_two] using (isElemAbelian_imgK h hPH hVH).2 x hx
  have hwc := weaklyClosed_imgK_self h hPH
  set g : HBar V H := piK V H ⟨y, hyH⟩ with hg
  have hT'eq : imgK V H (conjSubgroup y (Pc M V)) = conjSubgroup g (imgK V H (Pc M V)) := by
    rw [hg]
    exact imgK_conjSubgroup hyH hPH
  have hne' : imgK V H (Pc M V) ≠ conjSubgroup g (imgK V H (Pc M V)) := by
    rw [← hT'eq]
    exact hne
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [Nat.card_eq_fintype_card]; exact hcard
  set T : Subgroup ↥(CFSG.Blueprint.suzukiGroup a F) :=
    (imgK V H (Pc M V)).map e.toMonoidHom with hTdef
  have hTpe : IsPGroup 2 T := hTp.map e.toMonoidHom
  have hTsq : ∀ x ∈ T, x * x = 1 := map_sq_eq_one e hsq
  have hTnee : T ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ e.injective).not.mpr hTne
  have hTwe := CentralTI.weaklyClosed_map_mulEquiv e hwc
  have hT'eqe : (imgK V H (conjSubgroup y (Pc M V))).map e.toMonoidHom =
      conjSubgroup (e g) T := by
    rw [hT'eq, map_conjSubgroup_mulEquiv e, hTdef]
  have hT'pe : IsPGroup 2 (conjSubgroup (e g) T) :=
    hTpe.map (MulAut.conj (e g)).toMonoidHom
  have hT'sq : ∀ x ∈ conjSubgroup (e g) T, x * x = 1 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    simpa using hTsq z hz
  have hT'nee : conjSubgroup (e g) T ≠ ⊥ := by
    rw [← hT'eqe, hT'eq]
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).not.mpr
      ((conjSubgroup_eq_bot_iff (g := g)).not.mpr hTne)
  have hT'wee := CentralTI.weaklyClosed_map_mulEquiv (MulAut.conj (e g)) hTwe
  have hne'' : T ≠ conjSubgroup (e g) T := by
    intro hEq
    apply hne'
    have h1 : imgK V H (Pc M V) = conjSubgroup g (imgK V H (Pc M V)) := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [map_conjSubgroup_mulEquiv e]
      simpa [hTdef] using hEq
    exact h1
  obtain ⟨s, hss, hs1, hswap1, hswap2⟩ :=
    exists_involution_conj_eq_of_weaklyClosed_ne_sz hK hTpe hTnee hTsq hTwe hT'pe hT'nee
      hT'sq hT'wee hne''
  refine ⟨e.symm s, ?_, ?_, ?_, ?_⟩
  · apply e.injective
    simpa using hss
  · intro h1
    exact hs1 (by rw [← e.apply_symm_apply s, h1, map_one])
  · refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
    rw [map_conjSubgroup_mulEquiv e, e.apply_symm_apply, hT'eqe]
    exact hswap1
  · refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
    rw [map_conjSubgroup_mulEquiv e, e.apply_symm_apply, hT'eqe]
    exact hswap2

private theorem exists_swap_imgK (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hyH : y ∈ H)
    (hTne : imgK V H (Pc M V) ≠ ⊥)
    (hne : imgK V H (Pc M V) ≠ imgK V H (conjSubgroup y (Pc M V))) (hL : IsL2OrSz V H) :
    ∃ t : HBar V H, t * t = 1 ∧ t ≠ 1 ∧
      conjSubgroup t (imgK V H (Pc M V)) = imgK V H (conjSubgroup y (Pc M V)) ∧
      conjSubgroup t (imgK V H (conjSubgroup y (Pc M V))) = imgK V H (Pc M V) := by
  classical
  rcases hL with ⟨F, hField, hFintype, hCharP, -, ⟨e⟩⟩ |
    ⟨a, F, hField, hFintype, hCharP, -, hcard, ⟨e⟩⟩
  · letI := hField
    letI := hFintype
    letI := hCharP
    exact exists_swap_imgK_sl2 h hPH hVH hyH hTne hne e
  · letI := hField
    letI := hFintype
    letI := hCharP
    exact exists_swap_imgK_sz h hPH hVH hyH hTne hne hcard e

private theorem exists_swap_of_isL2OrSz_aux
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) (hL : IsL2OrSz V H) :
    ∃ t ∈ H, t ∉ kOf V H ∧ t * t ∈ kOf V H ∧
      conjSubgroup t (Pc M V) = conjSubgroup h₀ (Pc M V) := by
  classical
  obtain ⟨y, hyH, hPy, -, -⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hne0 := imgK_ne_bot_and_ne_of_sup h hPH hH hnM
  have hne : imgK V H (Pc M V) ≠ imgK V H (conjSubgroup y (Pc M V)) := by
    rw [← hPy]
    exact hne0.2
  obtain ⟨tbar, htt, ht1, hconj1, -⟩ := exists_swap_imgK h hPH hVH hyH hne0.1 hne hL
  obtain ⟨tH, htpi⟩ := piK_surjective V H tbar
  set t : G := (tH : G) with ht
  have htH : t ∈ H := tH.2
  have hpi : piK V H ⟨t, htH⟩ = tbar := htpi
  have hsqK : t * t ∈ kOf V H := by
    refine (piK_eq_one_iff (V := V) (H := H) ⟨t * t, H.mul_mem htH htH⟩).mp ?_
    rw [show (⟨t * t, H.mul_mem htH htH⟩ : ↥H) = ⟨t, htH⟩ * ⟨t, htH⟩ from Subtype.ext rfl,
      map_mul, hpi, htt]
  have himg : imgK V H (conjSubgroup t (Pc M V)) =
      imgK V H (conjSubgroup y (Pc M V)) := by
    rw [imgK_conjSubgroup htH hPH, hpi, hconj1]
  have hsup : conjSubgroup t (Pc M V) ⊔ kOf V H = conjSubgroup y (Pc M V) ⊔ kOf V H :=
    (imgK_eq_iff_sup_kOf_eq (conjSubgroup_le_of_le_of_mem hPH htH)
      (conjSubgroup_le_of_le_of_mem hPH hyH)).mp himg
  have hKconj : conjSubgroup y⁻¹ (kOf V H) = kOf V H :=
    conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H (H.inv_mem hyH))
  have hmap_sup : ∀ (z : G) (A B : Subgroup G),
      conjSubgroup z (A ⊔ B) = conjSubgroup z A ⊔ conjSubgroup z B :=
    fun z A B => CFSG.CGT.Timmesfeld75.conjSubgroup_sup z A B
  have hsup' : conjSubgroup (y⁻¹ * t) (Pc M V) ⊔ kOf V H = Pc M V ⊔ kOf V H := by
    have h1 : conjSubgroup y⁻¹ (conjSubgroup t (Pc M V) ⊔ kOf V H) =
        conjSubgroup (y⁻¹ * t) (Pc M V) ⊔ kOf V H := by
      rw [hmap_sup, hKconj, conjSubgroup_conjSubgroup]
    have h2 : conjSubgroup y⁻¹ (conjSubgroup y (Pc M V) ⊔ kOf V H) =
        Pc M V ⊔ kOf V H := by
      rw [hmap_sup, hKconj, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    rw [← h1, ← h2, hsup]
  have hmemy : y⁻¹ * t ∈ H := H.mul_mem (H.inv_mem hyH) htH
  obtain ⟨-, hPy't, -⟩ :=
    RootHyp.conjSubgroup_eq_self_of_sup_conj_Pc_eq (M := M) (V := V) (H := H)
      (y := y⁻¹ * t) h hPH hmemy hsup'
  have ht_eq : conjSubgroup t (Pc M V) = conjSubgroup h₀ (Pc M V) := by
    have h1 : conjSubgroup t (Pc M V) = conjSubgroup y (Pc M V) := by
      rw [show t = y * (y⁻¹ * t) from (mul_inv_cancel_left y t).symm,
        ← conjSubgroup_conjSubgroup, hPy't]
    rw [h1, hPy]
  refine ⟨t, htH, ?_, hsqK, ht_eq⟩
  intro hKt
  exact ht1 (by rw [← hpi, (piK_eq_one_iff _).mpr hKt])

theorem exists_swap_of_isL2OrSz (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) (hL : IsL2OrSz V H) :
    ∃ t ∈ H, t ∉ kOf V H ∧ t * t ∈ kOf V H ∧
      conjSubgroup t (Pc M V) = conjSubgroup h₀ (Pc M V) ∧
      conjSubgroup t (conjSubgroup h₀ (Pc M V)) = Pc M V := by
  classical
  obtain ⟨t, htH, htK, hsqK, ht_eq⟩ :=
    exists_swap_of_isL2OrSz_aux h hPH hVH hH hnM hL
  have hPP : conjSubgroup (t * t) (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc (kOf_le_M h hsqK))
  refine ⟨t, htH, htK, hsqK, ht_eq, ?_⟩
  calc conjSubgroup t (conjSubgroup h₀ (Pc M V))
      = conjSubgroup t (conjSubgroup t (Pc M V)) := by rw [ht_eq]
    _ = conjSubgroup (t * t) (Pc M V) := conjSubgroup_conjSubgroup t t _
    _ = Pc M V := hPP

theorem imgK_map_sl2 (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) :
    (∀ a ∈ (imgK V H (Pc M V)).map ψ.toMonoidHom, a * a = 1) ∧
      Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = Fintype.card F ∧
      ∃ a b : SL(2, F),
        (imgK V H (Pc M V)).map ψ.toMonoidHom = conjSubgroup a (utri F) ∧
        (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom =
          conjSubgroup b (utri F) ∧
        conjSubgroup a (utri F) ≠ conjSubgroup b (utri F) := by
  classical
  have hE := isElemAbelian_imgK h hPH hVH
  have hsq : ∀ x ∈ imgK V H (Pc M V), x * x = 1 := fun x hx => by
    simpa [pow_two] using hE.2 x hx
  have hTp : IsPGroup 2 (imgK V H (Pc M V)) := isPGroup_two_of_isElemAbelian hE
  have hne := imgK_ne_bot_and_ne_of_sup h hPH hH hnM
  have hwc := weaklyClosed_imgK_self h hPH
  obtain ⟨y, hyH, hPy, -, -⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  set T : Subgroup SL(2, F) := (imgK V H (Pc M V)).map ψ.toMonoidHom with hTdef
  have hTp' : IsPGroup 2 T := hTp.map ψ.toMonoidHom
  have hTne : T ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).not.mpr hne.1
  have hTwc := CentralTI.weaklyClosed_map_mulEquiv ψ hwc
  have hcard' := card_eq_of_weaklyClosed hTp' hTne hTwc
  obtain ⟨a, ha⟩ := exists_conj_eq_utri hTp' hTne hTwc
  rw [hTdef] at ha
  have hconj : (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom =
      conjSubgroup (ψ (piK V H ⟨y, hyH⟩) * a) (utri F) := by
    rw [hPy, imgK_conjSubgroup hyH hPH, map_conjSubgroup_mulEquiv ψ, ha,
      conjSubgroup_conjSubgroup]
  have hne' : conjSubgroup a (utri F) ≠ conjSubgroup (ψ (piK V H ⟨y, hyH⟩) * a) (utri F) := by
    intro hEq
    have h1 : (imgK V H (Pc M V)).map ψ.toMonoidHom =
        (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom := by
      rw [ha, hconj, hEq]
    exact hne.2 (Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective h1)
  refine ⟨map_sq_eq_one ψ hsq, hcard'.1, a, ψ (piK V H ⟨y, hyH⟩) * a, ha, hconj, hne'⟩

theorem imgK_map_sz (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ (2 * a + 1)) (ψ : HBar V H ≃* CFSG.Blueprint.suzukiGroup a F) :
    Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = 2 ^ (2 * a + 1) ∧
      ∃ x y : CFSG.Blueprint.suzukiGroup a F,
        (imgK V H (Pc M V)).map ψ.toMonoidHom = conjSubgroup x (Sec2.szZ a F) ∧
        (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom =
          conjSubgroup y (Sec2.szZ a F) ∧
        conjSubgroup x (Sec2.szZ a F) ≠ conjSubgroup y (Sec2.szZ a F) := by
  classical
  have hE := isElemAbelian_imgK h hPH hVH
  have hsq : ∀ x ∈ imgK V H (Pc M V), x * x = 1 := fun x hx => by
    simpa [pow_two] using hE.2 x hx
  have hTp : IsPGroup 2 (imgK V H (Pc M V)) := isPGroup_two_of_isElemAbelian hE
  have hne := imgK_ne_bot_and_ne_of_sup h hPH hH hnM
  have hwc := weaklyClosed_imgK_self h hPH
  obtain ⟨y, hyH, hPy, -, -⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [Nat.card_eq_fintype_card]; exact hF
  set T : Subgroup ↥(CFSG.Blueprint.suzukiGroup a F) :=
    (imgK V H (Pc M V)).map ψ.toMonoidHom with hTdef
  have hTp' : IsPGroup 2 T := hTp.map ψ.toMonoidHom
  have hTsq : ∀ x ∈ T, x * x = 1 := map_sq_eq_one ψ hsq
  have hTne : T ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).not.mpr hne.1
  have hTwc := CentralTI.weaklyClosed_map_mulEquiv ψ hwc
  obtain ⟨x, hx, hcardx⟩ := exists_conj_eq_szZ hK hTp' hTne hTsq hTwc
  rw [hTdef] at hx
  have hconj : (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom =
      conjSubgroup (ψ (piK V H ⟨y, hyH⟩) * x) (Sec2.szZ a F) := by
    rw [hPy, imgK_conjSubgroup hyH hPH, map_conjSubgroup_mulEquiv ψ, hx, conjSubgroup_conjSubgroup]
  have hne' : conjSubgroup x (Sec2.szZ a F) ≠
      conjSubgroup (ψ (piK V H ⟨y, hyH⟩) * x) (Sec2.szZ a F) := by
    intro hEq
    have h1 : (imgK V H (Pc M V)).map ψ.toMonoidHom =
        (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom := by
      rw [hx, hconj, hEq]
    exact hne.2 (Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective h1)
  exact ⟨hcardx, x, ψ (piK V H ⟨y, hyH⟩) * x, hx, hconj, hne'⟩

end RootHyp

end CFSG.RankThree.GF2n.Tim81
