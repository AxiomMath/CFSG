module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem kfPar_eq_one {S : Type} [Group S] {e : S} (h3 : e ^ 3 = 1) {k : ℕ}
    (hk : e ^ 2 ^ k = 1) : e = 1 := by
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk)
    (orderOf_dvd_of_pow_eq_one h3))

private theorem kfPar_pow_odd_inverts {S : Type} [Group S] {s : S} {D : Subgroup S}
    (hs : ∀ d ∈ D, s * d * s⁻¹ = d⁻¹) {m : ℕ} (hm : Odd m) :
    ∀ d ∈ D, s ^ m * d * (s ^ m)⁻¹ = d⁻¹ := by
  have h2 : ∀ d ∈ D, s ^ 2 * d * (s ^ 2)⁻¹ = d := by
    intro d hd
    have h1 := hs d hd
    have h1' := hs d⁻¹ (D.inv_mem hd)
    rw [inv_inv] at h1'
    calc s ^ 2 * d * (s ^ 2)⁻¹ = s * (s * d * s⁻¹) * s⁻¹ := by rw [pow_two]; group
      _ = s * d⁻¹ * s⁻¹ := by rw [h1]
      _ = d := h1'
  have key : ∀ j : ℕ, ∀ d ∈ D, s ^ (2 * j + 1) * d * (s ^ (2 * j + 1))⁻¹ = d⁻¹ := by
    intro j
    induction j with
    | zero => intro d hd; simpa using hs d hd
    | succ j ih =>
      intro d hd
      have e1 : s ^ (2 * (j + 1) + 1) = s ^ 2 * s ^ (2 * j + 1) := by
        rw [← pow_add]; congr 1; ring
      rw [e1]
      generalize s ^ (2 * j + 1) = u at ih ⊢
      calc s ^ 2 * u * d * (s ^ 2 * u)⁻¹ = s ^ 2 * (u * d * u⁻¹) * (s ^ 2)⁻¹ := by group
        _ = s ^ 2 * d⁻¹ * (s ^ 2)⁻¹ := by rw [ih d hd]
        _ = (s ^ 2 * d * (s ^ 2)⁻¹)⁻¹ := by group
        _ = d⁻¹ := by rw [h2 d hd]
  obtain ⟨j, rfl⟩ := hm
  exact key j

private theorem kfPar_solvable_oTwoP (Y : Type) [Group Y] [Finite Y] :
    Group.IsSolvable ↥(Sec4.oTwoP 3 Y) := by
  haveI : Group.IsNilpotent ↥(CFSG.pCore 2 Y) := CFSG.pCore_isNilpotent
  haveI : Group.IsNilpotent ↥(CFSG.pCore 3 (Y ⧸ CFSG.pCore 2 Y)) := CFSG.pCore_isNilpotent
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (Sec4.pCore_two_le_oTwoP 3 Y))
    (((QuotientGroup.mk' (CFSG.pCore 2 Y)).comp (Sec4.oTwoP 3 Y).subtype).codRestrict
      (CFSG.pCore 3 (Y ⧸ CFSG.pCore 2 Y)) (fun x => Subgroup.mem_comap.1 x.2)) ?_
  intro x hx
  have hx1 : QuotientGroup.mk' (CFSG.pCore 2 Y) (x : Y) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  exact MonoidHom.mem_range.2 ⟨⟨x.1, (QuotientGroup.eq_one_iff (x : Y)).1 hx1⟩, Subtype.ext rfl⟩

private theorem kfPar_solvable_oTwoP_sup {Y : Type} [Group Y] [Finite Y] (C : Subgroup Y)
    (hC : IsPGroup 2 C) : Group.IsSolvable ↥(Sec4.oTwoP 3 Y ⊔ C) := by
  haveI hOn : (Sec4.oTwoP 3 Y).Normal := by
    unfold Sec4.oTwoP
    infer_instance
  haveI := kfPar_solvable_oTwoP Y
  haveI : Group.IsNilpotent ↥C := hC.isNilpotent
  have hle : Sec4.oTwoP 3 Y ≤ Sec4.oTwoP 3 Y ⊔ C := le_sup_left
  have hCle : C ≤ Sec4.oTwoP 3 Y ⊔ C := le_sup_right
  haveI hsol1 : Group.IsSolvable ↥((Sec4.oTwoP 3 Y).subgroupOf (Sec4.oTwoP 3 Y ⊔ C)) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).symm.surjective
  haveI hsol2 : Group.IsSolvable (↥(Sec4.oTwoP 3 Y ⊔ C) ⧸
      (Sec4.oTwoP 3 Y).subgroupOf (Sec4.oTwoP 3 Y ⊔ C)) := by
    refine Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' _).comp (Subgroup.inclusion hCle)) ?_
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 s.2
    refine ⟨⟨z, hz⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show z⁻¹ * (s : Y) ∈ Sec4.oTwoP 3 Y
    rw [← hyz, ← mul_assoc]
    simpa using hOn.conj_mem y hy z⁻¹
  exact Group.isSolvable_of_subgroup_quotient
    ((Sec4.oTwoP 3 Y).subgroupOf (Sec4.oTwoP 3 Y ⊔ C))

private theorem kfPar_solvable_comap_conj {X : Type} [Group X] (S : Subgroup (MulAut X))
    [Group.IsSolvable ↥S] : Group.IsSolvable ↥(S.comap (MulAut.conj : X →* MulAut X)) := by
  have hcent : ∀ x : X, MulAut.conj x = 1 → ∀ y : X, x * y = y * x := by
    intro x hx y
    have h1 := DFunLike.congr_fun hx y
    rw [MulAut.conj_apply, MulAut.one_apply] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  let ψ : ↥(S.comap (MulAut.conj : X →* MulAut X)) →* ↥S :=
    ((MulAut.conj : X →* MulAut X).comp
      (S.comap (MulAut.conj : X →* MulAut X)).subtype).codRestrict S
      (fun x => Subgroup.mem_comap.1 x.2)
  haveI : Group.IsSolvable ↥ψ.ker := by
    apply Group.isSolvable_of_comm
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    have ha : MulAut.conj (a : ↥(S.comap (MulAut.conj : X →* MulAut X))).1 = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 a.2)
    exact hcent (a : ↥(S.comap (MulAut.conj : X →* MulAut X))).1 ha
      (b : ↥(S.comap (MulAut.conj : X →* MulAut X))).1
  exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ
    (fun x hx => MonoidHom.mem_range.2 ⟨⟨x, hx⟩, rfl⟩)

private theorem kfPar_solvable_map_subtype {X : Type} [Group X] (H : Subgroup X)
    (T : Subgroup ↥H) [Group.IsSolvable ↥T] : Group.IsSolvable ↥(T.map H.subtype) :=
  Group.isSolvable_of_surjective
    (f := (Subgroup.equivMapOfInjective T H.subtype H.subtype_injective).toMonoidHom)
    (Subgroup.equivMapOfInjective T H.subtype H.subtype_injective).surjective

private theorem kfPar_isSylow_top_of_sylow {X : Type} [Group X] [Finite X] (T : Sylow 2 X) :
    IsSylowOf 2 (T : Subgroup X) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  exact ⟨le_top, T.isPGroup', by rw [Subgroup.relIndex_top_right]; exact T.not_dvd_index⟩

private theorem kfPar_not_two_dvd_index {X : Type} [Group X] [Finite X] {P T : Subgroup X}
    (hT : IsSylowOf 2 T ⊤) (hTP : T ≤ P) : ¬ 2 ∣ P.index := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hT
  obtain ⟨-, -, hTdvd⟩ := hT
  intro h2
  apply hTdvd
  rw [← Subgroup.relIndex_mul_relIndex T P ⊤ hTP le_top, Subgroup.relIndex_top_right]
  exact Dvd.dvd.mul_left h2 _

private theorem kfPar_isSylow_top_of_odd_index {X : Type} [Group X] [Finite X] {P Q : Subgroup X}
    (hodd : ¬ 2 ∣ P.index) (hQ : IsSylowOf 2 Q P) : IsSylowOf 2 Q ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hQ ⊢
  obtain ⟨hQP, hQ2, hQdvd⟩ := hQ
  refine ⟨le_top, hQ2, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex Q P ⊤ hQP le_top, Subgroup.relIndex_top_right]
  intro h
  rcases (Nat.prime_two.dvd_mul).1 h with h1 | h1
  · exact hQdvd h1
  · exact hodd h1

private theorem kfPar_isPGroup_zpowers {X : Type} [Group X] [Finite X] {z : X} {k : ℕ}
    (hz : z ^ 2 ^ k = 1) : IsPGroup 2 (Subgroup.zpowers z) :=
  IsPGroup.of_card_dvd_pow (n := k) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hz)

private theorem kfPar_exists_sylow_containing {X : Type} [Group X] [Finite X] {P : Subgroup X}
    {z : X} (hz : z ∈ P) (hpz : IsPGroup 2 (Subgroup.zpowers z)) :
    ∃ Q : Subgroup X, IsSylowOf 2 Q P ∧ z ∈ Q := by
  have hA : IsPGroup 2 ((Subgroup.zpowers z).subgroupOf P) := by
    rw [← Subgroup.comap_subtype]
    exact hpz.comap_subtype
  obtain ⟨Q', hQ'⟩ := IsPGroup.exists_le_sylow hA
  refine ⟨(Q' : Subgroup P).map P.subtype, ⟨Q', rfl⟩, ?_⟩
  exact Subgroup.mem_map.2
    ⟨⟨z, hz⟩, hQ' (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers z)), rfl⟩

private theorem kfPar_isSylow_top_of_parabolic {X : Type} [Group X] [Finite X] {P : Subgroup X}
    (hP : ParabolicShape X P) {Q : Subgroup X} (hQ : IsSylowOf 2 Q P) : IsSylowOf 2 Q ⊤ := by
  unfold ParabolicShape at hP
  rcases hP with ⟨-, hprop⟩ | ⟨⟨hXA⟩, hext⟩
  · unfold IsProperParabolic at hprop
    obtain ⟨-, T, hTN⟩ := hprop
    have hTP : (T : Subgroup X) ≤ P := le_trans Subgroup.le_normalizer hTN
    exact kfPar_isSylow_top_of_odd_index
      (kfPar_not_two_dvd_index (kfPar_isSylow_top_of_sylow T) hTP) hQ
  · have hext' : ∃ K : Subgroup ↥P, ∃ _ : K.Normal,
        Nonempty (K ≃* Multiplicative (Fin 4 → ZMod 2)) ∧
          Nonempty (↥P ⧸ K ≃* Equiv.Perm (Fin 5)) := hext
    obtain ⟨K, hKn, ⟨eK⟩, ⟨eQ⟩⟩ := hext'
    have hK : Nat.card K = 16 := by
      rw [Nat.card_congr eK.toEquiv]
      show Nat.card (Fin 4 → ZMod 2) = 16
      simp [Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card]
    have hQ' : Nat.card (↥P ⧸ K) = 120 := by
      rw [Nat.card_congr eQ.toEquiv, Nat.card_perm]
      simp [Nat.factorial]
    have hPcard : Nat.card P = 1920 := by
      have h1 := Subgroup.card_mul_index (H := K)
      have h2 : K.index = 120 := hQ'
      rw [hK, h2] at h1
      omega
    have hXcard : Nat.card X = 1814400 := by
      rw [Nat.card_congr hXA.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hidx : P.index = 945 := by
      have h1 := Subgroup.card_mul_index (H := P)
      rw [hPcard, hXcard] at h1
      omega
    exact kfPar_isSylow_top_of_odd_index (by rw [hidx]; norm_num) hQ

private theorem kfPar_exists_solv_overgroup {G' : Type} [Group G'] [Finite G']
    {H CQ D : Subgroup G'} (hCQH : CQ ≤ H) (hC2 : IsPGroup 2 CQ)
    (hDO : D ≤ (Sec4.oTwoP 3 ↥H).map H.subtype) :
    ∃ S : Subgroup G', S ≤ H ∧ Group.IsSolvable ↥S ∧ CQ ≤ S ∧ D ≤ S := by
  have hC : IsPGroup 2 (CQ.subgroupOf H) := by
    rw [← Subgroup.comap_subtype]
    exact hC2.comap_subtype
  haveI := kfPar_solvable_oTwoP_sup (CQ.subgroupOf H) hC
  refine ⟨(Sec4.oTwoP 3 ↥H ⊔ CQ.subgroupOf H).map H.subtype, Subgroup.map_subtype_le _,
    kfPar_solvable_map_subtype H _, ?_, ?_⟩
  · intro c hc
    exact Subgroup.mem_map.2
      ⟨⟨c, hCQH hc⟩, Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hc), rfl⟩
  · intro d hd
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hDO hd)
    exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_sup_left hx, rfl⟩

private theorem kfPar_normalizes {X : Type} [Group X]
    (h : ∀ T D : Subgroup X, IsSylowOf 2 T ⊤ → T ≤ D → Group.IsSolvable ↥D →
      D ≤ Subgroup.normalizer (T : Set X))
    {P Q : Subgroup X} (hQ : IsSylowOf 2 Q ⊤) (hQP : Q ≤ P)
    {S : Subgroup (MulAut X)} (hSP : S ≤ P.map (MulAut.conj : X →* MulAut X))
    [Group.IsSolvable ↥S] (hQS : Q.map (MulAut.conj : X →* MulAut X) ≤ S)
    {e : MulAut X} (he : e ∈ S) :
    ∀ c ∈ Q.map (MulAut.conj : X →* MulAut X),
      e * c * e⁻¹ ∈ Q.map (MulAut.conj : X →* MulAut X) := by
  have hDX : Q ≤ S.comap (MulAut.conj : X →* MulAut X) := fun q hq =>
    Subgroup.mem_comap.2 (hQS (Subgroup.mem_map_of_mem _ hq))
  have hN := h Q _ hQ hDX (kfPar_solvable_comap_conj S)
  obtain ⟨y, hyP, hye⟩ := Subgroup.mem_map.1 (hSP he)
  have hyD : y ∈ S.comap (MulAut.conj : X →* MulAut X) :=
    Subgroup.mem_comap.2 (by rw [hye]; exact he)
  have hyq : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.1 (hN hyD) q).1 hq
  intro c hc
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hc
  rw [← hye]
  have hid : MulAut.conj y * MulAut.conj q * (MulAut.conj y)⁻¹ =
      MulAut.conj (y * q * y⁻¹) := by
    simp only [map_mul, map_inv]
  rw [hid]
  exact Subgroup.mem_map_of_mem _ (hyq q hq)

private theorem kfPar_noInv_core {X : Type} [Group X] [Finite X]
    (h : ∀ T D : Subgroup X, IsSylowOf 2 T ⊤ → T ≤ D → Group.IsSolvable ↥D →
      D ≤ Subgroup.normalizer (T : Set X))
    {P : Subgroup X} (hP : ParabolicShape X P) {D : Subgroup (MulAut X)}
    (hD3 : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hDH : D ≤ P.map (MulAut.conj : X →* MulAut X))
    (hDO : D ≤ (Sec4.oTwoP 3 ↥(P.map (MulAut.conj : X →* MulAut X))).map
      (P.map (MulAut.conj : X →* MulAut X)).subtype)
    {z : X} (hzP : z ∈ P) {k : ℕ} (hzk : z ^ 2 ^ k = 1)
    (hz : ∀ d ∈ D, MulAut.conj z * d * (MulAut.conj z)⁻¹ = d⁻¹) : False := by
  obtain ⟨Q, hQP, hzQ⟩ := kfPar_exists_sylow_containing hzP (kfPar_isPGroup_zpowers hzk)
  have hQ2 : IsSylowOf 2 Q ⊤ := kfPar_isSylow_top_of_parabolic hP hQP
  have hQle : Q ≤ P := hQP.le
  have hCH : Q.map (MulAut.conj : X →* MulAut X) ≤ P.map (MulAut.conj : X →* MulAut X) :=
    Subgroup.map_mono hQle
  have hCQ2 : IsPGroup 2 (Q.map (MulAut.conj : X →* MulAut X)) := hQP.isPGroup.map _
  obtain ⟨S, hSP, hSsolv, hCS, hDS⟩ := kfPar_exists_solv_overgroup hCH hCQ2 hDO
  obtain ⟨e, heD, he1⟩ : ∃ e ∈ D, e ≠ 1 := by
    have hD1 : D ≠ ⊥ := by
      intro hb
      rw [hb] at hD9
      simp at hD9
    obtain ⟨⟨e, he⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD1
    exact ⟨e, he, fun h1 => hne (Subtype.ext h1)⟩
  have hnorm := kfPar_normalizes h hQ2 hQle hSP hCS (hDS heD)
  have hzCQ : MulAut.conj z ∈ Q.map (MulAut.conj : X →* MulAut X) :=
    Subgroup.mem_map_of_mem _ hzQ
  have hconj : MulAut.conj z * e * (MulAut.conj z)⁻¹ = e⁻¹ := hz e heD
  have hee : e⁻¹ * e⁻¹ ∈ Q.map (MulAut.conj : X →* MulAut X) := by
    have h1 : e⁻¹ * e⁻¹ = MulAut.conj z * (e * (MulAut.conj z)⁻¹ * e⁻¹) := by
      calc e⁻¹ * e⁻¹ = (MulAut.conj z * e * (MulAut.conj z)⁻¹) * e⁻¹ := by rw [hconj]
        _ = MulAut.conj z * (e * (MulAut.conj z)⁻¹ * e⁻¹) := by group
    rw [h1]
    exact (Q.map (MulAut.conj : X →* MulAut X)).mul_mem hzCQ
      (hnorm _ ((Q.map (MulAut.conj : X →* MulAut X)).inv_mem hzCQ))
  have heCQ : e ∈ Q.map (MulAut.conj : X →* MulAut X) := by
    have h2 : e⁻¹ * e⁻¹ * e ^ 3 = e := by group
    rw [hD3.2 e heD, mul_one] at h2
    rw [← h2]
    exact hee
  obtain ⟨j, hj⟩ := isPGroup_iff_pow_pow_eq_one.1 hCQ2 ⟨e, heCQ⟩
  have hj' : e ^ 2 ^ j = 1 := congrArg Subtype.val hj
  exact he1 (kfPar_eq_one (hD3.2 e heD) hj')

private theorem kfPar_noInv_of_inverts {X : Type} [Group X] [Finite X]
    (h : ∀ T D : Subgroup X, IsSylowOf 2 T ⊤ → T ≤ D → Group.IsSolvable ↥D →
      D ≤ Subgroup.normalizer (T : Set X))
    {P : Subgroup X} (hP : ParabolicShape X P) {D : Subgroup (MulAut X)}
    (hD3 : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hDH : D ≤ P.map (MulAut.conj : X →* MulAut X))
    (hDO : D ≤ (Sec4.oTwoP 3 ↥(P.map (MulAut.conj : X →* MulAut X))).map
      (P.map (MulAut.conj : X →* MulAut X)).subtype)
    {w : X} (hwP : w ∈ P)
    (hw : ∀ d ∈ D, MulAut.conj w * d * (MulAut.conj w)⁻¹ = d⁻¹) : False := by
  obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  have hzk : (w ^ m) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm m, ← hk, pow_orderOf_eq_one]
  refine kfPar_noInv_core h hP hD3 hD9 hDH hDO (pow_mem hwP m) hzk ?_
  intro d hd
  rw [map_pow]
  exact kfPar_pow_odd_inverts hw hm d hd

theorem noInverting_of_solvOver {X : Type} [Group X] [Finite X]
    (h : ∀ T D : Subgroup X, IsSylowOf 2 T ⊤ → T ≤ D → Group.IsSolvable ↥D →
      D ≤ Subgroup.normalizer (T : Set X)) :
    NoInvertingInParabolic X ∧ NoSquareInvertingInParabolic X := by
  unfold NoInvertingInParabolic NoSquareInvertingInParabolic
  refine ⟨fun P D hP hDH hD3 hD9 hDO t htP _ hinv => ?_,
    fun P D hP hDH hD3 hD9 hDO t htP _ hinv => ?_⟩
  · obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.1 htP
    exact kfPar_noInv_of_inverts h hP hD3 hD9 hDH hDO hyP hinv
  · obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.1 htP
    exact kfPar_noInv_of_inverts h hP hD3 hD9 hDH hDO (pow_mem hyP 2)
      (fun d hd => by rw [map_pow]; exact hinv d hd)

end CFSG.RankThree.PartTwo.Late
