module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Assembly.OrderReductions.StrongEmbedding

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7

private theorem k1566l7_fusion27_of_transvection {H : Type*} [Group H] [Finite H]
    {V : Subgroup H} {u z : H} (hVc : IsMulCommutative ↥V) (hVcard : Nat.card V = 9)
    (hzV : z ∈ V) (huV : u ∈ Subgroup.normalizer (V : Set H)) (hu3 : u ^ 3 ∈ V)
    (hmove : u * z * u⁻¹ ≠ z) : Fusion27 z := by
  classical
  set R : Subgroup H := V ⊔ Subgroup.zpowers u with hRdef
  have hVR : V ≤ R := le_sup_left
  have hzR : z ∈ R := hVR hzV
  have huR : u ∈ R := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hRnorm : R ≤ Subgroup.normalizer (V : Set H) := by
    rw [hRdef]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr huV)
  have hN : (V.subgroupOf R).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hVR]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp (hRnorm hk) h).mp hh
  have huVn : u ∉ V := by
    intro huV'
    have hcomm : u * z = z * u :=
      congrArg Subtype.val (hVc.is_comm.comm ⟨u, huV'⟩ ⟨z, hzV⟩)
    exact hmove (by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one])
  let mk := QuotientGroup.mk' (V.subgroupOf R)
  let q : R ⧸ V.subgroupOf R := mk ⟨u, huR⟩
  have hq3 : q ^ 3 = 1 := by
    change mk (⟨u, huR⟩ ^ 3) = 1
    rw [show (⟨u, huR⟩ : R) ^ 3 = ⟨u ^ 3, hVR hu3⟩ from Subtype.ext rfl]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hu3)
  have hq1 : q ≠ 1 := by
    intro h
    exact huVn (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hgen : Subgroup.zpowers q = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf R) x
    change mk r ∈ Subgroup.zpowers q
    have hzp : (Subgroup.zpowers u).subgroupOf R = Subgroup.zpowers (⟨u, huR⟩ : R) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext hk⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, congrArg Subtype.val hk⟩
    have htop : (⊤ : Subgroup ↥R) = V.subgroupOf R ⊔ Subgroup.zpowers (⟨u, huR⟩ : R) := by
      have h1 : (V ⊔ Subgroup.zpowers u).subgroupOf R =
          V.subgroupOf R ⊔ (Subgroup.zpowers u).subgroupOf R :=
        Subgroup.subgroupOf_sup le_sup_left (Subgroup.zpowers_le.mpr huR)
      rw [← hzp, ← h1, ← hRdef, Subgroup.subgroupOf_self]
    have hle : V.subgroupOf R ⊔ Subgroup.zpowers (⟨u, huR⟩ : R) ≤
        Subgroup.comap mk (Subgroup.zpowers q) := by
      refine sup_le ?_ ?_
      · intro v hv
        exact Subgroup.mem_comap.mpr (by
          have hv1 : mk v = 1 := (QuotientGroup.eq_one_iff _).mpr hv
          rw [hv1]
          exact Subgroup.one_mem _)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_comap.mpr (Subgroup.mem_zpowers q))
    exact Subgroup.mem_comap.mp (hle (htop ▸ Subgroup.mem_top r))
  have hquot : Nat.card (R ⧸ V.subgroupOf R) = 3 := by
    rw [← Subgroup.card_top (G := R ⧸ V.subgroupOf R), ← hgen, Nat.card_zpowers]
    exact orderOf_eq_prime hq3 hq1
  have hcardV : Nat.card (V.subgroupOf R) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVR).toEquiv, hVcard]
  have hcardR : Nat.card R = 27 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf R), hquot, hcardV]
  refine ⟨R, hcardR, hzR, ?_⟩
  intro hzcenter
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hzcenter
  have hzu : z * u = u * z := by
    have hcv : (c : H) = z := hcz
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc (⟨u, huR⟩ : R))
    simp only [Subgroup.coe_mul] at h
    rw [hcv] at h
    exact h.symm
  exact hmove (by rw [hzu.symm, mul_assoc, mul_inv_cancel, mul_one])

private theorem k1566l7b_outside_moves_of_transvection
    {H : Type*} [Group H] [Finite H] {Q T V : Subgroup H} {y : H}
    (hTQ : T ≤ Q) (hTnorm : (T.subgroupOf Q).Normal)
    (hTcomm : IsMulCommutative ↥T) (hVT : V ≤ T)
    (hQ : Q = T ⊔ Subgroup.zpowers y) (hy3 : orderOf y = 3)
    (hmove : ∃ v ∈ V, y * v * y⁻¹ ≠ v) :
    ∀ g ∈ Q, g ∉ T → ∃ v ∈ V, g * v * g⁻¹ ≠ v := by
  have hnormQ : Q ≤ Subgroup.normalizer (T : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTQ).mp hTnorm
  have hnorm : ∀ q ∈ Q, ∀ t ∈ T, q * t * q⁻¹ ∈ T := fun q hq t ht =>
    (Subgroup.mem_normalizer_iff.mp (hnormQ hq) t).mp ht
  have hyQ : y ∈ Q := by
    rw [hQ]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hyNorm : Subgroup.zpowers y ≤ Subgroup.normalizer (T : Set H) :=
    Subgroup.zpowers_le.mpr (hnormQ hyQ)
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers y) T hyNorm
  intro g hgQ hgT
  have hg'' : g ∈ (↑(Subgroup.zpowers y ⊔ T) : Set H) := by
    rw [sup_comm, ← hQ]; exact hgQ
  rw [hcoe] at hg''
  obtain ⟨s, hs, t, ht, hst⟩ := hg''
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hgT (by rw [← hst]; simpa using ht)
  have htv : ∀ v ∈ V, t * v * t⁻¹ = v := by
    intro v hv
    have hcomm : t * v = v * t :=
      congrArg Subtype.val (hTcomm.is_comm.comm ⟨t, ht⟩ ⟨v, hVT hv⟩)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hkey : (∀ v ∈ V, g * v * g⁻¹ = v) → ∀ v ∈ V, s * v * s⁻¹ = v := by
    intro hgv v hv
    have h1 : g * v * g⁻¹ = s * (t * v * t⁻¹) * s⁻¹ := by rw [← hst]; group
    rw [hgv v hv, htv v hv] at h1
    exact h1.symm
  by_contra hcon
  push Not at hcon
  have hsv : ∀ v ∈ V, s * v * s⁻¹ = v := fun v hv => hkey hcon v hv
  have hsC : s ∈ Subgroup.centralizer (V : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    calc v * s = (s * v * s⁻¹) * s := by rw [hsv v hv]
      _ = s * v := by group
  have hcard_y : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, hy3]
  have hs_dvd : orderOf s ∣ 3 := by
    rw [← hcard_y]
    exact Subgroup.orderOf_dvd_natCard _ hs
  have hs_ord : orderOf s = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hs_dvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hs1
    · exact h
  have hcard_s : Nat.card (Subgroup.zpowers s) = 3 := by
    rw [Nat.card_zpowers, hs_ord]
  have hle_sy : Subgroup.zpowers s ≤ Subgroup.zpowers y := by
    rw [Subgroup.zpowers_le, ← hk]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) k
  have heq : Subgroup.zpowers s = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge hle_sy (by rw [hcard_s, hcard_y])
  have hyC : y ∈ Subgroup.centralizer (V : Set H) := by
    refine Subgroup.zpowers_le.mpr hsC ?_
    rw [heq]; exact Subgroup.mem_zpowers y
  obtain ⟨v, hv, hvne⟩ := hmove
  exact hvne (by
    have hyv : y * v = v * y := (Subgroup.mem_centralizer_iff.mp hyC v hv).symm
    rw [hyv, mul_assoc, mul_inv_cancel, mul_one])

private theorem card_mult_zmod_pow_three_l7a {e : ℕ} (he : 1 ≤ e) :
    Nat.card {x : Multiplicative (ZMod (3 ^ e)) // x ^ 3 = 1} = 3 := by
  have hker : Nat.card {a : ZMod (3 ^ e) // 3 • a = 0} = 3 := by
    have h := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod (3 ^ e)) 3
    rw [Nat.card_zmod] at h
    have hgcd : (3 ^ e).gcd 3 = 3 := by
      simpa only [pow_one] using Nat.gcd_eq_right (pow_dvd_pow 3 he)
    rw [hgcd] at h
    simpa only [AddSubgroup.mem_mk, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] using h
  let f : {x : Multiplicative (ZMod (3 ^ e)) // x ^ 3 = 1} ≃
      {a : ZMod (3 ^ e) // 3 • a = 0} :=
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, by
        have hx := congrArg Multiplicative.toAdd x.2
        rw [toAdd_pow] at hx
        simpa using hx⟩
      invFun := fun a => ⟨Multiplicative.ofAdd a.1, by
        have ha := congrArg Multiplicative.ofAdd a.2
        rw [ofAdd_nsmul] at ha
        simpa using ha⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro a; ext; simp }
  rw [Nat.card_congr f, hker]

private theorem card_V_l7a {H : Type*} [Group H] {T V : Subgroup H} {e1 e2 : ℕ}
    (he1 : 1 ≤ e1) (he2 : 1 ≤ e2)
    (hT : Nonempty ((Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))) ≃* ↥T))
    (hV : ∀ t, t ∈ V ↔ t ∈ T ∧ t ^ 3 = 1) :
    Nat.card V = 9 := by
  obtain ⟨e⟩ := hT
  let α := Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))
  let f : V ≃ {x : α // x.1 ^ 3 = 1 ∧ x.2 ^ 3 = 1} :=
    { toFun := fun v => by
        have hv := (hV v.1).mp v.2
        exact ⟨e.symm ⟨v.1, hv.1⟩, by
          have hpow : (⟨v.1, hv.1⟩ : T) ^ 3 = 1 := by
            ext
            simpa using hv.2
          have h : (e.symm ⟨v.1, hv.1⟩) ^ 3 = 1 := by
            rw [← map_pow, hpow, map_one]
          exact ⟨by simpa using congrArg Prod.fst h,
            by simpa using congrArg Prod.snd h⟩⟩
      invFun := fun x => by
        exact ⟨e x.1, by
          rw [hV]
          refine ⟨(e x.1).2, ?_⟩
          have hx : x.1 ^ 3 = 1 := Prod.ext x.2.1 x.2.2
          have h := congrArg e hx
          simpa using congrArg (fun t : T => (t : H)) h⟩
      left_inv := by
        intro v
        apply Subtype.ext
        simp only [MulEquiv.apply_symm_apply, Subtype.coe_mk]
      right_inv := by
        intro x
        apply Subtype.ext
        change e.symm (e x.1) = x.1
        rw [MulEquiv.symm_apply_apply] }
  have h1 : Nat.card V = Nat.card {x : α // x.1 ^ 3 = 1 ∧ x.2 ^ 3 = 1} :=
    Nat.card_congr f
  have h2 : Nat.card {x : α // x.1 ^ 3 = 1 ∧ x.2 ^ 3 = 1} =
      Nat.card {a : Multiplicative (ZMod (3 ^ e1)) // a ^ 3 = 1} *
      Nat.card {b : Multiplicative (ZMod (3 ^ e2)) // b ^ 3 = 1} := by
    rw [Nat.card_congr (Equiv.subtypeProdEquivProd
      (p := fun a : Multiplicative (ZMod (3 ^ e1)) => a ^ 3 = 1)
      (q := fun b : Multiplicative (ZMod (3 ^ e2)) => b ^ 3 = 1)), Nat.card_prod]
  have h3 : Nat.card {a : Multiplicative (ZMod (3 ^ e1)) // a ^ 3 = 1} = 3 :=
    card_mult_zmod_pow_three_l7a he1
  have h4 : Nat.card {b : Multiplicative (ZMod (3 ^ e2)) // b ^ 3 = 1} = 3 :=
    card_mult_zmod_pow_three_l7a he2
  rw [h1, h2, h3, h4]

private theorem card_T_l7a {H : Type*} [Group H] {T : Subgroup H} {e1 e2 : ℕ}
    (hT : Nonempty ((Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))) ≃* ↥T)) :
    Nat.card T = 3 ^ (e1 + e2) := by
  obtain ⟨e⟩ := hT
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod]
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd]
  rw [Nat.card_zmod, Nat.card_zmod, ← pow_add]

private theorem isMulCommutative_T_l7a {H : Type*} [Group H] {T : Subgroup H} {e1 e2 : ℕ}
    (hT : Nonempty ((Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))) ≃* ↥T)) :
    IsMulCommutative ↥T := by
  obtain ⟨e⟩ := hT
  refine IsMulCommutative.of_comm ?_
  intro a b
  have h : e.symm a * e.symm b = e.symm b * e.symm a := mul_comm _ _
  simpa using congrArg e h

private theorem normalizes_T_l7a {H : Type*} [Group H] [Finite H] {T : Subgroup H} {y : H}
    (hyT : ∀ t ∈ T, y * t * y⁻¹ ∈ T) :
    Subgroup.zpowers y ≤ Subgroup.normalizer (T : Set H) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hyT x
  · intro hx
    let φ : MulAut H := MulAut.conj y
    have hmap : T.map φ.toMonoidHom ≤ T := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
      dsimp [φ]
      simpa [MulAut.conj_apply] using hyT s hs
    have hcard : Nat.card (T.map φ.toMonoidHom) = Nat.card T :=
      Subgroup.card_map_of_injective φ.injective
    have heq : T.map φ.toMonoidHom = T :=
      Subgroup.eq_of_le_of_card_ge hmap (by rw [hcard])
    have hmap_symm : T.map φ.symm.toMonoidHom = T := by
      conv_lhs => rw [← heq]
      rw [Subgroup.map_map]
      simp
    have hx'' : x ∈ T.map φ.symm.toMonoidHom := by
      rw [Subgroup.mem_map]
      exact ⟨φ x, hx, by simp⟩
    rwa [hmap_symm] at hx''

private theorem y_not_mem_T_l7a {H : Type*} [Group H] {T V : Subgroup H} {y : H}
    (hTc : IsMulCommutative ↥T) (hVT : V ≤ T)
    (hmove : ∃ v ∈ V, y * v * y⁻¹ ≠ v) : y ∉ T := by
  intro hy
  obtain ⟨v, hvV, hvne⟩ := hmove
  have hvT : v ∈ T := hVT hvV
  have hcomm : y * v = v * y :=
    congrArg Subtype.val (hTc.is_comm.comm ⟨y, hy⟩ ⟨v, hvT⟩)
  exact hvne (by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one])

private theorem disjoint_T_zpowers_l7a {H : Type*} [Group H] [Finite H]
    {T : Subgroup H} {y : H} (hy3 : orderOf y = 3) (hyT : y ∉ T) :
    Disjoint T (Subgroup.zpowers y) := by
  rw [disjoint_iff_inf_le]
  let K := T ⊓ Subgroup.zpowers y
  have hKle : K ≤ Subgroup.zpowers y := inf_le_right
  have hcard_y : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, hy3]
  have hdvd : Nat.card K ∣ 3 := by
    rw [← hcard_y]
    exact Subgroup.card_dvd_of_le hKle
  have hbot : K = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : K = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge hKle (by rw [h3, hcard_y])
      have hyK : y ∈ K := by
        rw [heq]
        exact Subgroup.mem_zpowers y
      exact hyT (Subgroup.mem_inf.mp hyK).1
  change K ≤ ⊥
  rw [hbot]

private theorem card_Q_l7a {H : Type*} [Group H] {Q T : Subgroup H} {y : H} {e1 e2 : ℕ}
    (hT : Nonempty ((Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))) ≃* ↥T))
    (hy3 : orderOf y = 3) (hyNorm : Subgroup.zpowers y ≤ Subgroup.normalizer (T : Set H))
    (hdisj : Disjoint T (Subgroup.zpowers y)) (hQ : Q = T ⊔ Subgroup.zpowers y) :
    Nat.card Q = 3 ^ (e1 + e2) * 3 := by
  rw [hQ]
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer T
    (Subgroup.zpowers y) hyNorm hdisj]
  rw [card_T_l7a hT, Nat.card_zpowers, hy3]

private theorem isPGroup_Q_l7a {H : Type*} [Group H] [Finite H] {Q : Subgroup H} {e1 e2 : ℕ}
    (hcardQ : Nat.card Q = 3 ^ (e1 + e2) * 3) : IsPGroup 3 Q := by
  exact IsPGroup.of_card (n := e1 + e2 + 1) (by rw [hcardQ, pow_succ])

private theorem not_dvd_index_l7a {H : Type*} [Group H] [Finite H] {Q : Subgroup H} {e1 e2 : ℕ}
    (hcardQ : Nat.card Q = 3 ^ (e1 + e2) * 3)
    (hcard : padicValNat 3 (Nat.card H) = e1 + e2 + 1) :
    ¬ 3 ∣ Q.index := by
  have hcardH_ne_zero : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hcardQ_ne_zero : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hindex_ne_zero : Q.index ≠ 0 := by
    intro h
    have h1 : Nat.card Q * Q.index = Nat.card H := Subgroup.card_mul_index Q
    rw [h, mul_zero] at h1
    exact hcardH_ne_zero h1.symm
  have hpadic_mul : padicValNat 3 (Nat.card H) =
      padicValNat 3 (Nat.card Q) + padicValNat 3 Q.index := by
    rw [← Subgroup.card_mul_index Q, padicValNat.mul hcardQ_ne_zero hindex_ne_zero]
  have hcardQ' : Nat.card Q = 3 ^ (e1 + e2 + 1) := by
    rw [hcardQ, pow_succ]
  have hpadic_Q : padicValNat 3 (Nat.card Q) = e1 + e2 + 1 := by
    rw [hcardQ', padicValNat.prime_pow]
  have hpadic_index : padicValNat 3 Q.index = 0 := by
    have h1 : e1 + e2 + 1 = (e1 + e2 + 1) + padicValNat 3 Q.index := by
      conv_lhs => rw [← hcard]
      rw [hpadic_mul, hpadic_Q]
    omega
  intro hdvd
  have h := (padicValNat.eq_zero_iff (p := 3) (n := Q.index)).mp hpadic_index
  rcases h with h1 | h2 | h3
  · norm_num at h1
  · exact hindex_ne_zero h2
  · exact h3 hdvd

private theorem le_of_eq_sup_l7a {H : Type*} [Group H] {Q T : Subgroup H} {y : H}
    (hQ : Q = T ⊔ Subgroup.zpowers y) : T ≤ Q := by
  rw [hQ]
  exact le_sup_left

private theorem normal_subgroupOf_of_eq_sup_l7a {H : Type*} [Group H] {Q T : Subgroup H} {y : H}
    (hQ : Q = T ⊔ Subgroup.zpowers y)
    (hyNorm : Subgroup.zpowers y ≤ Subgroup.normalizer (T : Set H)) :
    (T.subgroupOf Q).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_eq_sup_l7a hQ)]
  rw [hQ]
  exact sup_le Subgroup.le_normalizer hyNorm

private theorem le_of_mem_iff_l7a {H : Type*} [Group H] {T V : Subgroup H}
    (hV : ∀ t, t ∈ V ↔ t ∈ T ∧ t ^ 3 = 1) : V ≤ T := by
  intro v hv
  exact (hV v).mp hv |>.1

private theorem isElemAbelian_V_l7a {H : Type*} [Group H] {T V : Subgroup H}
    (hTc : IsMulCommutative ↥T) (hVT : V ≤ T)
    (hV : ∀ t, t ∈ V ↔ t ∈ T ∧ t ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 V := by
  refine ⟨?_, ?_⟩
  · refine IsMulCommutative.of_comm ?_
    intro a b
    apply Subtype.ext
    have haT : (a : H) ∈ T := hVT a.2
    have hbT : (b : H) ∈ T := hVT b.2
    have hcomm : (⟨(a : H), haT⟩ : T) * ⟨(b : H), hbT⟩ =
        ⟨(b : H), hbT⟩ * ⟨(a : H), haT⟩ :=
      hTc.is_comm.comm _ _
    simpa using congrArg Subtype.val hcomm
  · intro x hx
    exact (hV x).mp hx |>.2

private theorem mem_of_pow_three_l7a {H : Type*} [Group H] {T V : Subgroup H}
    (hV : ∀ t, t ∈ V ↔ t ∈ T ∧ t ^ 3 = 1) :
    ∀ t ∈ T, t ^ 3 = 1 → t ∈ V := by
  intro t ht ht3
  exact (hV t).mpr ⟨ht, ht3⟩

private theorem sq_eq_zero_of_isNilpotent_l7a {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : Module.finrank F V = 2) {N : Module.End F V}
    (hN : IsNilpotent N) : N ^ 2 = 0 := by
  have h := (LinearMap.isNilpotent_iff_charpoly N).1 hN
  rw [hV] at h
  have h2 := LinearMap.aeval_self_charpoly N
  rw [h] at h2
  simpa using h2

private theorem sq_sub_one_eq_zero_l7a {A : Type*} [AddCommGroup A] [Module (ZMod 3) A]
    [Finite A] (hA : Nat.card A = 9) (f : A →ₗ[ZMod 3] A) (hf : f ^ 3 = 1) :
    (f - 1) ^ 2 = 0 := by
  let _ : Fintype A := Fintype.ofFinite A
  have hfin : Module.finrank (ZMod 3) A = 2 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 3) (V := A)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_zmod] at h
    rw [hA] at h
    have h' : 3 ^ Module.finrank (ZMod 3) A = 3 ^ 2 := by
      rw [← h]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 1 < 3) h'
  have hAne : Nontrivial A := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hA]
    norm_num
  obtain ⟨x, hx⟩ := exists_ne (0 : A)
  have htor : ∃ x : A, Ideal.torsionOf (ZMod 3) A x = ⊥ :=
    ⟨x, (Ideal.torsionOf_eq_bot_iff_of_noZeroSMulDivisors (ZMod 3) x).2 hx⟩
  let _ : CharP (Module.End (ZMod 3) A) 3 :=
    Module.charP_end (R := ZMod 3) (M := A) (p := 3) htor
  have h3 : (f - 1) ^ 3 = 0 := by
    have hcomm : Commute f (1 : Module.End (ZMod 3) A) := Commute.one_right f
    have h := sub_pow_char_of_commute (R := Module.End (ZMod 3) A) (p := 3) hcomm
    rw [hf, one_pow] at h
    simpa using h
  have hnil : IsNilpotent (f - 1) := ⟨3, h3⟩
  exact sq_eq_zero_of_isNilpotent_l7a hfin hnil

private theorem conj_mem_V_l7a {H : Type*} [Group H] {T V : Subgroup H} {y t : H}
    (hV : ∀ x, x ∈ V ↔ x ∈ T ∧ x ^ 3 = 1)
    (hyT : ∀ x ∈ T, y * x * y⁻¹ ∈ T)
    (htV : t ∈ V) : y * t * y⁻¹ ∈ V := by
  have htT : t ∈ T := (hV t).mp htV |>.1
  have ht3 : t ^ 3 = 1 := (hV t).mp htV |>.2
  rw [hV]
  refine ⟨hyT t htT, ?_⟩
  have h3 : (y * t * y⁻¹) ^ 3 = y * t ^ 3 * y⁻¹ := by
    rw [pow_three, pow_three]
    group
  rw [h3]
  simp [ht3]

private theorem conj_three_l7a {H : Type*} [Group H] {y : H} (hy3 : y ^ 3 = 1) (a : H) :
    y * (y * (y * a * y⁻¹) * y⁻¹) * y⁻¹ = a := by
  have h : y * (y * (y * a * y⁻¹) * y⁻¹) * y⁻¹ = y ^ 3 * a * (y ^ 3)⁻¹ := by
    simp only [pow_three]
    group
  rw [h, hy3, one_mul, inv_one, mul_one]

private theorem conj_fixes_commutator_l7a {H : Type*} [Group H] [Finite H]
    {T V : Subgroup H} {y : H}
    (hVcomm : IsMulCommutative ↥V)
    (hV : ∀ t, t ∈ V ↔ t ∈ T ∧ t ^ 3 = 1)
    (hyT : ∀ t ∈ T, y * t * y⁻¹ ∈ T)
    (hy3 : orderOf y = 3)
    (hVcard : Nat.card V = 9) :
    ∀ v ∈ V, y * (y * v * y⁻¹ * v⁻¹) * y⁻¹ = y * v * y⁻¹ * v⁻¹ := by
  intro v hv
  let _ : IsMulCommutative ↥V := hVcomm
  let _ : CommGroup ↥V := IsMulCommutative.instCommGroup
  let A := Additive ↥V
  let f_add : A →+ A := AddMonoidHom.mk'
    (fun a => Additive.ofMul ⟨y * (Additive.toMul a).1 * y⁻¹,
      conj_mem_V_l7a hV hyT (Additive.toMul a).2⟩)
    (fun a b => by
      apply Additive.toMul.injective
      ext
      conv_lhs => rw [toMul_add]
      conv_rhs => rw [toMul_add]
      simp only [toMul_ofMul, Subtype.coe_mk, Subgroup.coe_mul]
      group)
  let _ : Module (ZMod 3) A := AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    apply Subtype.ext
    exact (hV (Additive.toMul x).1).mp (Additive.toMul x).2 |>.2)
  let f : A →ₗ[ZMod 3] A := f_add.toZModLinearMap 3
  have hf : f ^ 3 = 1 := by
    apply LinearMap.ext
    intro a
    change f (f (f a)) = a
    simp only [f, AddMonoidHom.coe_toZModLinearMap, f_add, AddMonoidHom.mk'_apply, toMul_ofMul]
    apply Additive.toMul.injective
    simp only [toMul_ofMul]
    apply Subtype.ext
    exact conj_three_l7a (by rw [← orderOf_dvd_iff_pow_eq_one, hy3]) _
  have hsq : (f - 1) ^ 2 = 0 :=
    sq_sub_one_eq_zero_l7a (A := A)
      (by rw [Nat.card_congr (Additive.toMul : A ≃ ↥V), hVcard]) f hf
  have h := congrArg (fun g : A →ₗ[ZMod 3] A => g (Additive.ofMul ⟨v, hv⟩)) hsq
  have h' := congrArg Additive.toMul h
  simp only [pow_two, sub_eq_add_neg] at h'
  have h'' := congrArg Subtype.val h'
  change y * (y * v * y⁻¹ * v⁻¹) * y⁻¹ * (y * v * y⁻¹ * v⁻¹)⁻¹ = 1 at h''
  exact mul_inv_eq_one.mp h''

theorem sd3_of_torus {H : Type*} [Group H] [Finite H] {Q T V : Subgroup H} {y : H} {e1 e2 : ℕ}
    (he1 : 1 ≤ e1) (he2 : 1 ≤ e2)
    (hT : Nonempty ((Multiplicative (ZMod (3 ^ e1)) × Multiplicative (ZMod (3 ^ e2))) ≃* ↥T))
    (hV : ∀ t, t ∈ V ↔ t ∈ T ∧ t ^ 3 = 1) (hyT : ∀ t ∈ T, y * t * y⁻¹ ∈ T)
    (hy3 : orderOf y = 3) (hmove : ∃ v ∈ V, y * v * y⁻¹ ≠ v)
    (hcard : padicValNat 3 (Nat.card H) = e1 + e2 + 1) (hQ : Q = T ⊔ Subgroup.zpowers y) :
    SD3 H Q T V y e1 e2 := by
  have hTc : IsMulCommutative ↥T := isMulCommutative_T_l7a hT
  have hyNorm : Subgroup.zpowers y ≤ Subgroup.normalizer (T : Set H) :=
    normalizes_T_l7a hyT
  have hVT : V ≤ T := le_of_mem_iff_l7a hV
  have hyT' : y ∉ T := y_not_mem_T_l7a hTc hVT hmove
  have hdisj : Disjoint T (Subgroup.zpowers y) := disjoint_T_zpowers_l7a hy3 hyT'
  have hcardQ : Nat.card Q = 3 ^ (e1 + e2) * 3 :=
    card_Q_l7a hT hy3 hyNorm hdisj hQ
  have hVcard : Nat.card V = 9 := card_V_l7a he1 he2 hT hV
  have hVcomm : IsMulCommutative ↥V := (isElemAbelian_V_l7a hTc hVT hV).1
  refine ⟨isPGroup_Q_l7a hcardQ, not_dvd_index_l7a hcardQ hcard, le_of_eq_sup_l7a hQ,
    normal_subgroupOf_of_eq_sup_l7a hQ hyNorm, hTc, hVT, isElemAbelian_V_l7a hTc hVT hV,
    mem_of_pow_three_l7a hV, hQ, ?_, hmove, ?_, hVcard, hy3, hT⟩
  · intro v hv
    have h1 : y * v * y⁻¹ ∈ V := conj_mem_V_l7a hV hyT hv
    exact ⟨V.mul_mem h1 (V.inv_mem hv),
      conj_fixes_commutator_l7a hVcomm hV hyT hy3 hVcard v hv⟩
  · exact k1566l7b_outside_moves_of_transvection (le_of_eq_sup_l7a hQ)
      (normal_subgroupOf_of_eq_sup_l7a hQ hyNorm) hTc hVT hQ hy3 hmove

@[expose] def MovingE9 {G : Type*} [Group G] (M W : Subgroup G) : Prop :=
  W ≤ M ∧ IsMulCommutative ↥W ∧ Nat.card W = 9 ∧ (∀ w ∈ W, w ^ 3 = 1) ∧
    ∀ w ∈ W, w ≠ 1 → ∃ g ∈ M, (∀ v ∈ W, g * v * g⁻¹ ∈ W) ∧ g ^ 3 ∈ W ∧ g * w * g⁻¹ ≠ w

private theorem commute_of_coprime_pow_l7a2 {G : Type*} [Group G] {u w : G} {n : ℕ}
    (hn : ¬ 3 ∣ n) (hn3 : Commute (u ^ n) w) (h3 : Commute (u ^ 3) w) : Commute u w := by
  have hcop : Nat.Coprime n 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hn).symm
  have hg : Nat.gcd n 3 = 1 := hcop.gcd_eq_one
  have hbez : (Nat.gcdA n 3 : ℤ) * n + (Nat.gcdB n 3 : ℤ) * 3 = 1 := by
    have h := Nat.gcd_eq_gcd_ab (x := n) (y := 3)
    rw [hg] at h
    rw [mul_comm (n : ℤ) (Nat.gcdA n 3), mul_comm ((3 : ℕ) : ℤ) (Nat.gcdB n 3)] at h
    exact h.symm
  have h1 : Commute (u ^ ((Nat.gcdA n 3 : ℤ) * n)) w := by
    have h := hn3.zpow_left (Nat.gcdA n 3 : ℤ)
    rw [← zpow_natCast] at h
    rw [← zpow_mul'] at h
    simpa using h
  have h2 : Commute (u ^ ((Nat.gcdB n 3 : ℤ) * 3)) w := by
    have h := h3.zpow_left (Nat.gcdB n 3 : ℤ)
    rw [← zpow_natCast] at h
    rw [← zpow_mul'] at h
    simpa using h
  have hmul : Commute (u ^ ((Nat.gcdA n 3 : ℤ) * n) * u ^ ((Nat.gcdB n 3 : ℤ) * 3)) w :=
    h1.mul_left h2
  rw [← zpow_add, hbez, zpow_one] at hmul
  exact hmul

private theorem pow_conj_mem_T_l7a2 {G : Type*} [Group G] {T : Subgroup G} {u : G}
    (huT : ∀ t ∈ T, u * t * u⁻¹ ∈ T) :
    ∀ k : ℕ, ∀ t ∈ T, u ^ k * t * (u ^ k)⁻¹ ∈ T := by
  intro k
  induction k with
  | zero =>
    intro t ht
    simpa using ht
  | succ k ih =>
    intro t ht
    have h1 : u ^ k * (u * t * u⁻¹) * (u ^ k)⁻¹ ∈ T := ih (u * t * u⁻¹) (huT t ht)
    have h2 : u ^ k * (u * t * u⁻¹) * (u ^ k)⁻¹ =
        u ^ (k + 1) * t * (u ^ (k + 1))⁻¹ := by
      rw [pow_succ']
      group
    rw [h2] at h1
    exact h1

private theorem pow_cube_mem_W_l7a2 {G : Type*} [Group G] {T W : Subgroup G} {d n : ℕ}
    (hd : ∀ t ∈ T, t ^ d = 1) (hW : ∀ t, t ∈ W ↔ t ∈ T ∧ t ^ 3 = 1)
    {u : G} (hu3 : u ^ 3 ∈ T) (hdn : d ∣ 3 * n) :
    (u ^ n) ^ 3 ∈ W := by
  have hmemT : (u ^ n) ^ 3 ∈ T := by
    rw [← pow_mul, mul_comm n 3, pow_mul]
    exact Subgroup.pow_mem T hu3 n
  have hg3 : (u ^ n) ^ 3 = (u ^ 3) ^ n := by
    rw [← pow_mul, mul_comm n 3, pow_mul]
  have hone : (u ^ 3) ^ (3 * n) = 1 := by
    have horder : orderOf (u ^ 3) ∣ d := orderOf_dvd_of_pow_eq_one (hd (u ^ 3) hu3)
    exact (orderOf_dvd_iff_pow_eq_one).mp (horder.trans hdn)
  have hpow3 : ((u ^ n) ^ 3) ^ 3 = 1 := by
    rw [hg3, ← pow_mul, mul_comm n 3]
    exact hone
  rw [hW]
  exact ⟨hmemT, hpow3⟩

private theorem pow_moves_of_moves_l7a2 {G : Type*} [Group G] {T : Subgroup G}
    (hTc : IsMulCommutative ↥T) {u w : G} {n : ℕ} (hn : ¬ 3 ∣ n)
    (hu3 : u ^ 3 ∈ T) (hwT : w ∈ T) (humove : u * w * u⁻¹ ≠ w) :
    u ^ n * w * (u ^ n)⁻¹ ≠ w := by
  intro hconj
  have hcomm : Commute (u ^ n) w := by
    show u ^ n * w = w * u ^ n
    calc u ^ n * w = (u ^ n * w * (u ^ n)⁻¹) * u ^ n := by group
      _ = w * u ^ n := by rw [hconj]
  have hcomm3 : Commute (u ^ 3) w := by
    show u ^ 3 * w = w * u ^ 3
    have h := hTc.is_comm.comm ⟨u ^ 3, hu3⟩ ⟨w, hwT⟩
    simpa using congrArg Subtype.val h
  have hcommu : Commute u w := commute_of_coprime_pow_l7a2 hn hcomm hcomm3
  apply humove
  have heq : u * w = w * u := hcommu
  rw [heq]
  group

private theorem exists_moving_pow_l7a2 {G : Type*} [Group G] {M T W : Subgroup G} {d : ℕ}
    (hTc : IsMulCommutative ↥T) (hd : ∀ t ∈ T, t ^ d = 1) (hd9 : ¬ 9 ∣ d)
    (hW : ∀ t, t ∈ W ↔ t ∈ T ∧ t ^ 3 = 1)
    {u w : G} (huM : u ∈ M) (huT : ∀ t ∈ T, u * t * u⁻¹ ∈ T) (hu3 : u ^ 3 ∈ T)
    (hwW : w ∈ W) (humove : u * w * u⁻¹ ≠ w) :
    ∃ g ∈ M, (∀ v ∈ W, g * v * g⁻¹ ∈ W) ∧ g ^ 3 ∈ W ∧ g * w * g⁻¹ ≠ w := by
  have hwT : w ∈ T := ((hW w).mp hwW).1
  obtain ⟨n, hn, hdn⟩ : ∃ n, ¬ 3 ∣ n ∧ d ∣ 3 * n := by
    by_cases h3d : 3 ∣ d
    · obtain ⟨k, hk⟩ := h3d
      refine ⟨k, ?_, ?_⟩
      · intro h3k
        apply hd9
        obtain ⟨m, hm⟩ := h3k
        rw [hk, hm]
        exact ⟨m, by ring⟩
      · rw [hk]
    · exact ⟨d, h3d, dvd_mul_left d 3⟩
  let g : G := u ^ n
  have hgM : g ∈ M := Subgroup.pow_mem M huM n
  have hgW : ∀ v ∈ W, g * v * g⁻¹ ∈ W := by
    intro v hv
    have hvT : v ∈ T := ((hW v).mp hv).1
    have hv3 : v ^ 3 = 1 := ((hW v).mp hv).2
    have hmemT : u ^ n * v * (u ^ n)⁻¹ ∈ T := pow_conj_mem_T_l7a2 huT n v hvT
    have hpow3 : (u ^ n * v * (u ^ n)⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hv3, mul_one]
      group
    rw [hW]
    exact ⟨hmemT, hpow3⟩
  have hg3 : g ^ 3 ∈ W := by
    change (u ^ n) ^ 3 ∈ W
    exact pow_cube_mem_W_l7a2 hd hW hu3 hdn
  have hgm : g * w * g⁻¹ ≠ w := by
    change u ^ n * w * (u ^ n)⁻¹ ≠ w
    exact pow_moves_of_moves_l7a2 hTc hn hu3 hwT humove
  exact ⟨g, hgM, hgW, hg3, hgm⟩

theorem movingE9_of_cover {G : Type*} [Group G] {M T W : Subgroup G} {d : ℕ} (hTM : T ≤ M)
    (hTc : IsMulCommutative ↥T) (hd : ∀ t ∈ T, t ^ d = 1) (hd9 : ¬ 9 ∣ d)
    (hW : ∀ t, t ∈ W ↔ t ∈ T ∧ t ^ 3 = 1) (hW9 : Nat.card W = 9) {u₁ u₂ : G} (hu₁M : u₁ ∈ M)
    (hu₂M : u₂ ∈ M) (hu₁T : ∀ t ∈ T, u₁ * t * u₁⁻¹ ∈ T) (hu₂T : ∀ t ∈ T, u₂ * t * u₂⁻¹ ∈ T)
    (hu₁3 : u₁ ^ 3 ∈ T) (hu₂3 : u₂ ^ 3 ∈ T)
    (hcover : ∀ w ∈ W, w ≠ 1 → u₁ * w * u₁⁻¹ ≠ w ∨ u₂ * w * u₂⁻¹ ≠ w) :
    MovingE9 M W := by
  have hWT : W ≤ T := fun w hw => ((hW w).mp hw).1
  have hWM : W ≤ M := hWT.trans hTM
  have hWc : IsMulCommutative ↥W := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    have ha : (a : G) ∈ T := hWT a.2
    have hb : (b : G) ∈ T := hWT b.2
    have hcomm := hTc.is_comm.comm ⟨(a : G), ha⟩ ⟨(b : G), hb⟩
    simpa using congrArg Subtype.val hcomm
  have hW3 : ∀ w ∈ W, w ^ 3 = 1 := fun w hw => ((hW w).mp hw).2
  have hmv : ∀ w ∈ W, w ≠ 1 → ∃ g ∈ M,
      (∀ v ∈ W, g * v * g⁻¹ ∈ W) ∧ g ^ 3 ∈ W ∧ g * w * g⁻¹ ≠ w := by
    intro w hwW hw1
    rcases hcover w hwW hw1 with hu1 | hu2
    · exact exists_moving_pow_l7a2 hTc hd hd9 hW hu₁M hu₁T hu₁3 hwW hu1
    · exact exists_moving_pow_l7a2 hTc hd hd9 hW hu₂M hu₂T hu₂3 hwW hu2
  exact ⟨hWM, hWc, hW9, hW3, hmv⟩

theorem MovingE9.comap {H G : Type*} [Group H] [Group G] {ι : H →* G} (hι : Function.Injective ι)
    {M W : Subgroup G} (hM : M ≤ ι.range) (h : MovingE9 M W) : MovingE9 ⊤ (W.comap ι) := by
  obtain ⟨hWM, hWc, hW9, hW3, hWmv⟩ := h
  refine ⟨le_top, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    apply hι
    simp only [Subgroup.coe_mul, map_mul]
    exact congrArg Subtype.val (hWc.is_comm.comm ⟨ι a.1, Subgroup.mem_comap.mp a.2⟩
      ⟨ι b.1, Subgroup.mem_comap.mp b.2⟩)
  · rw [← Subgroup.card_map_of_injective (f := ι) (K := W.comap ι) hι]
    rw [Subgroup.map_comap_eq_self (f := ι) (hWM.trans hM)]
    exact hW9
  · intro w hw
    apply hι
    rw [map_pow, map_one]
    exact hW3 (ι w) (Subgroup.mem_comap.mp hw)
  · intro w hw hw1
    have hwW : ι w ∈ W := Subgroup.mem_comap.mp hw
    have hw1W : ι w ≠ 1 := by
      intro h
      apply hw1
      apply hι
      rw [map_one]
      exact h
    obtain ⟨g, hgM, hgW, hg3, hgm⟩ := hWmv (ι w) hwW hw1W
    obtain ⟨g', hg'⟩ := hM hgM
    refine ⟨g', trivial, ?_, ?_, ?_⟩
    · intro v hv
      rw [Subgroup.mem_comap]
      rw [map_mul, map_mul, map_inv, hg']
      exact hgW (ι v) (Subgroup.mem_comap.mp hv)
    · rw [Subgroup.mem_comap]
      rw [map_pow, hg']
      exact hg3
    · intro h
      apply hgm
      simpa only [map_mul, map_inv, hg'] using congrArg ι h

private theorem card_centralizer_le_l7a2 {H : Type*} [Group H] [Finite H] {V : Subgroup H} {y : H}
    (hV9 : Nat.card V = 9) (hmv : ∃ v ∈ V, y * v * y⁻¹ ≠ v) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set H)) ≤ 3 := by
  set C := V ⊓ Subgroup.centralizer ({y} : Set H) with hC
  have hle : C ≤ V := inf_le_left
  have hdvd : Nat.card C ∣ 3 ^ 2 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [hV9, show (9 : ℕ) = 3 ^ 2 by norm_num] at h
  have hne : C ≠ V := by
    intro hEq
    obtain ⟨v, hv, hvne⟩ := hmv
    have hvC : v ∈ C := by
      rw [hEq]
      exact hv
    have hcomm : v * y = y * v :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hvC).2
    exact hvne (by rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one])
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hk2 : k ≠ 2 := by
    intro h2
    apply hne
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard, h2, hV9]
    norm_num
  have hk1 : k ≤ 1 := by omega
  rw [hcard]
  calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 3 := by norm_num

private theorem mem_of_le_centralizer_l7a2 {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    {y z : H} (hV9 : Nat.card V = 9) (hmv : ∃ v ∈ V, y * v * y⁻¹ ≠ v)
    (hzV : z ∈ V) (hyz : y * z * y⁻¹ = z)
    {S : Subgroup H} (hS : S ≤ V ⊓ Subgroup.centralizer ({y} : Set H))
    (hS3 : 3 ≤ Nat.card S) : z ∈ S := by
  set C := V ⊓ Subgroup.centralizer ({y} : Set H) with hC
  have hC3 : Nat.card C ≤ 3 := card_centralizer_le_l7a2 hV9 hmv
  have hdvd : Nat.card S ∣ Nat.card C := Subgroup.card_dvd_of_le hS
  have hSle : Nat.card S ≤ Nat.card C := Nat.le_of_dvd Nat.card_pos hdvd
  have hSeq : S = C := by
    apply Subgroup.eq_of_le_of_card_ge hS
    omega
  have hzC : z ∈ C := by
    refine ⟨hzV, ?_⟩
    have hyz' : y * z = z * y := by
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = z * y := by rw [hyz]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hyz'.symm
  rw [hSeq]
  exact hzC

private theorem gen_quotient_l7a2 {H : Type*} [Group H] [Finite H] {Q T : Subgroup H} {y : H}
    [(T.subgroupOf Q).Normal] (hTQ : T ≤ Q) (hQ : Q = T ⊔ Subgroup.zpowers y) (hyQ : y ∈ Q) :
    Subgroup.zpowers (QuotientGroup.mk' (T.subgroupOf Q) ⟨y, hyQ⟩) = ⊤ := by
  let N := T.subgroupOf Q
  let mk := QuotientGroup.mk' N
  let q : Q ⧸ N := mk ⟨y, hyQ⟩
  have hqgen : Subgroup.zpowers q = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective N x
    change mk r ∈ Subgroup.zpowers q
    have hzp : (Subgroup.zpowers y).subgroupOf Q = Subgroup.zpowers (⟨y, hyQ⟩ : Q) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext hk⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, congrArg Subtype.val hk⟩
    have htop : (⊤ : Subgroup Q) = N ⊔ Subgroup.zpowers (⟨y, hyQ⟩ : Q) := by
      have h1 : (T ⊔ Subgroup.zpowers y).subgroupOf Q =
          T.subgroupOf Q ⊔ (Subgroup.zpowers y).subgroupOf Q :=
        Subgroup.subgroupOf_sup hTQ (Subgroup.zpowers_le.mpr hyQ)
      rw [← hzp, ← h1, ← hQ, Subgroup.subgroupOf_self]
    have hle : N ⊔ Subgroup.zpowers (⟨y, hyQ⟩ : Q) ≤
        Subgroup.comap mk (Subgroup.zpowers q) := by
      refine sup_le ?_ ?_
      · intro v hv
        exact Subgroup.mem_comap.mpr (by
          have hv1 : mk v = 1 := (QuotientGroup.eq_one_iff _).mpr hv
          rw [hv1]
          exact Subgroup.one_mem _)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_comap.mpr (Subgroup.mem_zpowers q))
    exact Subgroup.mem_comap.mp (hle (htop ▸ Subgroup.mem_top r))
  simpa only [N, mk, q] using hqgen

private theorem card_le_three_mul_inf_l7a2 {H : Type*} [Group H] [Finite H]
    {Q T : Subgroup H} {y : H} [(T.subgroupOf Q).Normal]
    (hTQ : T ≤ Q) (hQ : Q = T ⊔ Subgroup.zpowers y) (hy3 : orderOf y = 3) :
    ∀ W' : Subgroup H, W' ≤ Q → Nat.card W' ≤ 3 * Nat.card ↥(W' ⊓ T) := by
  intro W' hW'Q
  have hyQ : y ∈ Q := by
    rw [hQ]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  let N := T.subgroupOf Q
  let mk := QuotientGroup.mk' N
  let q : Q ⧸ N := mk ⟨y, hyQ⟩
  have hq3 : q ^ 3 = 1 := by
    change mk (⟨y, hyQ⟩ ^ 3) = 1
    rw [show (⟨y, hyQ⟩ : Q) ^ 3 = 1 from Subtype.ext (by
      rw [← hy3]
      exact pow_orderOf_eq_one y)]
    exact map_one mk
  have hqgen : Subgroup.zpowers q = ⊤ := gen_quotient_l7a2 hTQ hQ hyQ
  have hquot : Nat.card (Q ⧸ N) ∣ 3 := by
    have h1 : Nat.card (Q ⧸ N) = orderOf q := by
      rw [← Subgroup.card_top (G := Q ⧸ N), ← hqgen, Nat.card_zpowers]
    rw [h1]
    exact orderOf_dvd_of_pow_eq_one hq3
  let f' : ↥W' →* Q ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hW'Q)
  have hker : f'.ker = (W' ⊓ T).subgroupOf W' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      change (QuotientGroup.mk' N) (Subgroup.inclusion hW'Q x) = 1 at hx
      have hxN : (Subgroup.inclusion hW'Q x : Q) ∈ N :=
        (QuotientGroup.eq_one_iff _).mp hx
      have hxT : (x : H) ∈ T := by
        simpa using Subgroup.mem_subgroupOf.mp hxN
      exact ⟨x.2, hxT⟩
    · rintro ⟨-, hxT⟩
      have hxN : (Subgroup.inclusion hW'Q x : Q) ∈ N := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hxT
      exact (QuotientGroup.eq_one_iff _).mpr hxN
  have hcardker : Nat.card ↥((W' ⊓ T).subgroupOf W') = Nat.card ↥(W' ⊓ T) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card ↥f'.range ≤ 3 := by
    have h1 : Nat.card ↥f'.range ∣ Nat.card (Q ⧸ N) := Subgroup.card_subgroup_dvd_card _
    have h3 : Nat.card ↥f'.range ∣ 3 := h1.trans hquot
    exact Nat.le_of_dvd (by norm_num) h3
  have hmain := Subgroup.card_ker_mul_card_range f'
  rw [hker, hcardker] at hmain
  rw [← hmain, Nat.mul_comm 3 (Nat.card ↥(W' ⊓ T))]
  exact Nat.mul_le_mul_left _ hrange

private theorem centralizer_of_outside_l7a2 {H : Type*} [Group H] [Finite H]
    {Q T : Subgroup H} {y g s : H}
    (hTQ : T ≤ Q) (hTn : (T.subgroupOf Q).Normal) (hTc : IsMulCommutative ↥T)
    (hQ : Q = T ⊔ Subgroup.zpowers y) (hy3 : orderOf y = 3)
    (hgQ : g ∈ Q) (hgT : g ∉ T) (hsT : s ∈ T)
    (hgs : g * s = s * g) : s * y = y * s := by
  have hnormQ : Q ≤ Subgroup.normalizer (T : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTQ).mp hTn
  have hyQ : y ∈ Q := by
    rw [hQ]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hyNorm : Subgroup.zpowers y ≤ Subgroup.normalizer (T : Set H) :=
    Subgroup.zpowers_le.mpr (hnormQ hyQ)
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers y) T hyNorm
  have hg'' : g ∈ (↑(Subgroup.zpowers y ⊔ T) : Set H) := by
    rw [sup_comm, ← hQ]; exact hgQ
  rw [hcoe] at hg''
  obtain ⟨s', hs', t, ht, hst⟩ := hg''
  have hts : t * s = s * t :=
    congrArg Subtype.val (hTc.is_comm.comm ⟨t, ht⟩ ⟨s, hsT⟩)
  have hs's : s' * s = s * s' := by
    rw [← hst] at hgs
    rw [mul_assoc, hts, ← mul_assoc, ← mul_assoc] at hgs
    exact mul_right_cancel hgs
  have hs'1 : s' ≠ 1 := by
    rintro rfl
    exact hgT (by rw [← hst]; simpa using ht)
  have hcard_y : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, hy3]
  have hs'_dvd : orderOf s' ∣ 3 := by
    rw [← hcard_y]
    exact Subgroup.orderOf_dvd_natCard _ hs'
  have hs'_ord : orderOf s' = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hs'_dvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hs'1
    · exact h
  have hcard_s' : Nat.card (Subgroup.zpowers s') = 3 := by
    rw [Nat.card_zpowers, hs'_ord]
  have hle_s'y : Subgroup.zpowers s' ≤ Subgroup.zpowers y :=
    Subgroup.zpowers_le.mpr hs'
  have heq : Subgroup.zpowers s' = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge hle_s'y (by rw [hcard_s', hcard_y])
  have hy_mem : y ∈ Subgroup.zpowers s' := by
    rw [heq]; exact Subgroup.mem_zpowers y
  have hs'_cent : s' ∈ Subgroup.centralizer ({s} : Set H) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hs's
  have hle_cent : Subgroup.zpowers s' ≤ Subgroup.centralizer ({s} : Set H) :=
    Subgroup.zpowers_le.mpr hs'_cent
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle_cent hy_mem)).symm

private theorem mem_of_e9_le_l7a2 {H : Type*} [Group H] [Finite H] {Q T V : Subgroup H}
    {y z : H} [hTn : (T.subgroupOf Q).Normal] (hTQ : T ≤ Q) (hTc : IsMulCommutative ↥T)
    (hV3 : ∀ t ∈ T, t ^ 3 = 1 → t ∈ V)
    (hQ : Q = T ⊔ Subgroup.zpowers y) (hy3 : orderOf y = 3) (hV9 : Nat.card V = 9)
    (hmv : ∃ v ∈ V, y * v * y⁻¹ ≠ v) (hzV : z ∈ V) (hyz : y * z * y⁻¹ = z)
    {W' : Subgroup H} (hW'Q : W' ≤ Q) (hW'c : IsMulCommutative ↥W')
    (hW'9 : Nat.card W' = 9) (hW'3 : ∀ w ∈ W', w ^ 3 = 1) : z ∈ W' := by
  by_cases hWT : W' ≤ T
  · have hWV : W' ≤ V := fun w hw => hV3 w (hWT hw) (hW'3 w hw)
    have hEq : W' = V := Subgroup.eq_of_le_of_card_ge hWV (by rw [hW'9, hV9])
    exact hEq ▸ hzV
  · obtain ⟨g, hgW', hgT⟩ : ∃ g ∈ W', g ∉ T := by
      by_contra h
      apply hWT
      intro w hw
      by_contra hwT
      exact h ⟨w, hw, hwT⟩
    have hSV : W' ⊓ T ≤ V := fun s hs => hV3 s hs.2 (hW'3 s hs.1)
    have hSC : W' ⊓ T ≤ Subgroup.centralizer ({y} : Set H) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hgs : g * s = s * g :=
        congrArg Subtype.val (hW'c.is_comm.comm ⟨g, hgW'⟩ ⟨s, hs.1⟩)
      exact centralizer_of_outside_l7a2 hTQ hTn hTc hQ hy3 (hW'Q hgW') hgT hs.2 hgs
    have hS3 : 3 ≤ Nat.card ↥(W' ⊓ T) := by
      have h := card_le_three_mul_inf_l7a2 hTQ hQ hy3 W' hW'Q
      rw [hW'9] at h
      omega
    have hmem := mem_of_le_centralizer_l7a2 hV9 hmv hzV hyz
      (fun s hs => ⟨hSV hs, hSC hs⟩) hS3
    exact hmem.1

private theorem exists_conj_le_l7a2 {H : Type*} [Group H] [Finite H] {Q W : Subgroup H}
    (hQp : IsPGroup 3 Q) (hQi : ¬ 3 ∣ Q.index) (hWp : IsPGroup 3 W) :
    ∃ c : H, W.map (MulAut.conj c).toMonoidHom ≤ Q := by
  have : Fact (Nat.Prime 3) := Nat.fact_prime_three
  let Qs : Sylow 3 H := hQp.toSylow hQi
  obtain ⟨S, hWS⟩ := IsPGroup.exists_le_sylow hWp
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H Qs S
  have hc' : (c • Qs : Subgroup H) = S :=
    congrArg (fun P : Sylow 3 H => (P : Subgroup H)) hc
  have hmem : ∀ w ∈ W, c⁻¹ * w * c ∈ Q := by
    intro w hw
    have hwS : w ∈ S := hWS hw
    have hwS' : w ∈ (c • (Qs : Subgroup H)) := by
      rw [hc']
      exact hwS
    change w ∈ Subgroup.map (MulAut.conj c).toMonoidHom (Qs : Subgroup H) at hwS'
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hwS'
    have hqeq' : c * q * c⁻¹ = w := by
      simpa [MulAut.conj_apply] using hqeq
    have hmemq : c⁻¹ * w * c = q := by
      rw [← hqeq']
      group
    rw [hmemq]
    exact hq
  refine ⟨c⁻¹, ?_⟩
  intro x hx
  obtain ⟨w, hw, hxw⟩ := Subgroup.mem_map.mp hx
  rw [← hxw]
  change (MulAut.conj c⁻¹) w ∈ Q
  rw [MulAut.conj_apply, inv_inv]
  exact hmem w hw

private theorem mem_normalizer_of_maps_l7a2 {H : Type*} [Group H] {W' : Subgroup H} {u : H}
    [Finite ↥W'] (h : ∀ v ∈ W', u * v * u⁻¹ ∈ W') :
    u ∈ Subgroup.normalizer (W' : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => h x hx
  · intro hx
    let f : ↥W' → ↥W' := fun v => ⟨u * v * u⁻¹, h v v.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have h1 : u * (a : H) * u⁻¹ = u * (b : H) * u⁻¹ := congrArg Subtype.val hab
      exact mul_left_cancel (mul_right_cancel h1)
    have hsurj : Function.Surjective f := (Finite.injective_iff_surjective).mp hf
    obtain ⟨v, hv⟩ := hsurj ⟨u * x * u⁻¹, hx⟩
    have hv' : u * v * u⁻¹ = u * x * u⁻¹ := congrArg Subtype.val hv
    have hxv : v = x := mul_left_cancel (mul_right_cancel hv')
    rw [← hxv]
    exact v.2

theorem fusion27_of_movingE9 {H : Type*} [Group H] [Finite H] {Q T V W : Subgroup H} {y : H}
    {e1 e2 : ℕ} (hSD : SD3 H Q T V y e1 e2) (hW : MovingE9 ⊤ W) :
    ∀ z ∈ V, z ≠ 1 → y * z * y⁻¹ = z → Fusion27 z := by
  obtain ⟨hQp, hQi, hTQ, hTn, hTc, -, hVe, hV3, hQ, htr, hmv, hout, hV9, hy3, hT⟩ := hSD
  have hWcopy := hW
  obtain ⟨-, -, hW9, hW3, hmvW⟩ := hWcopy
  intro z hzV hz1 hyz
  have hWp : IsPGroup 3 W := IsPGroup.of_card (n := 2) (by rw [hW9]; norm_num)
  obtain ⟨c, hc⟩ := exists_conj_le_l7a2 hQp hQi hWp
  have hsymm : (MulAut.conj c⁻¹).symm = MulAut.conj c := by
    ext x
    rw [MulAut.conj_symm_apply, MulAut.conj_apply]
    group
  have hcomp : W.comap (MulAut.conj c⁻¹).toMonoidHom =
      W.map (MulAut.conj c).toMonoidHom := by
    change W.comap (↑(MulAut.conj c⁻¹) : H →* H) = W.map (↑(MulAut.conj c) : H →* H)
    rw [Subgroup.comap_equiv_eq_map_symm (MulAut.conj c⁻¹) W, hsymm]
  have hrange : (MulAut.conj c⁻¹).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (MulAut.conj c⁻¹).surjective
  have hMe : MovingE9 ⊤ (W.map (MulAut.conj c).toMonoidHom) := by
    have h := MovingE9.comap (H := H) (G := H) (ι := (MulAut.conj c⁻¹).toMonoidHom)
      (MulAut.conj c⁻¹).injective (M := ⊤) (W := W) (by rw [hrange]) hW
    rwa [hcomp] at h
  obtain ⟨-, hW'c, hW'9, hW'3, hmvW'⟩ := hMe
  have hzW' : z ∈ W.map (MulAut.conj c).toMonoidHom :=
    mem_of_e9_le_l7a2 (hTn := hTn) hTQ hTc hV3 hQ hy3 hV9 hmv hzV hyz hc hW'c hW'9 hW'3
  obtain ⟨u, -, huW', hu3W', humove⟩ := hmvW' z hzW' hz1
  exact k1566l7_fusion27_of_transvection hW'c hW'9 hzW'
    (mem_normalizer_of_maps_l7a2 huW') hu3W' humove

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7
