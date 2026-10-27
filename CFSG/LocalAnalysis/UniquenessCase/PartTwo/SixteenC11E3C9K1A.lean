module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9CentA
public import CFSG.GroupTheory.SupCommute
public import CFSG.Quasithin.H13.AS91Sec8Prod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped Pointwise

private theorem s1611e3_mem_centSub_zpowers_iff {W : Type} [CommGroup W] (l : MulAut W)
    (w : W) : l ∈ centSub (Subgroup.zpowers w) ↔ l w = w := by
  refine ⟨fun h => h w (Subgroup.mem_zpowers w), fun h u hu => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [map_zpow, h]

theorem s1611e3_c9k1_sq_normalizes {W : Type} [Group W] [Finite W]
    {Lb Lp Mb : Subgroup (MulAut W)} {x : MulAut W}
    (hxMb : x ∈ Mb)
    (hLp : Lp = Lb.map (MulAut.conj x).toMonoidHom)
    (hcls : Set.ncard {Y : Subgroup (MulAut W) |
      ∃ φ ∈ Mb, Y = Lb.map (MulAut.conj φ).toMonoidHom} = 2)
    (hne : Lb ≠ ⊥) (hinf : Lb ⊓ Lp = ⊥) :
    Lb.map (MulAut.conj (x * x)).toMonoidHom = Lb := by
  have hLb_ne_Lp : Lb ≠ Lp := by
    intro heq
    exact hne (by rw [← hinf, ← heq, inf_idem])
  have hS_eq : {Y : Subgroup (MulAut W) |
      ∃ φ ∈ Mb, Y = Lb.map (MulAut.conj φ).toMonoidHom} = {Lb, Lp} := by
    have hsub : ({Lb, Lp} : Set (Subgroup (MulAut W))) ⊆
        {Y : Subgroup (MulAut W) |
          ∃ φ ∈ Mb, Y = Lb.map (MulAut.conj φ).toMonoidHom} := by
      intro Y hY
      rcases hY with rfl | rfl
      · have h1 : (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) := by
          ext y; simp [MulAut.conj_apply]
        exact ⟨1, Mb.one_mem, by rw [h1, Subgroup.map_id]⟩
      · exact ⟨x, hxMb, hLp⟩
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcls, Set.ncard_pair hLb_ne_Lp])).symm
  have hLb_x2 : Lb.map (MulAut.conj (x * x)).toMonoidHom = Lb ∨
      Lb.map (MulAut.conj (x * x)).toMonoidHom = Lp := by
    have hmem : Lb.map (MulAut.conj (x * x)).toMonoidHom ∈
        {Y : Subgroup (MulAut W) |
          ∃ φ ∈ Mb, Y = Lb.map (MulAut.conj φ).toMonoidHom} :=
      ⟨x * x, Mb.mul_mem hxMb hxMb, rfl⟩
    rw [hS_eq] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  rcases hLb_x2 with h | h
  · exact h
  · exfalso
    have hconj2 : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj (x * x)).toMonoidHom := by
      have h1 : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          (MulAut.conj x * MulAut.conj x).toMonoidHom := by ext y; rfl
      rw [h1, ← map_mul (MulAut.conj) x x]
    have hLp_g : Lp.map (MulAut.conj x).toMonoidHom =
        Lb.map (MulAut.conj (x * x)).toMonoidHom := by
      rw [hLp, Subgroup.map_map, hconj2]
    have hLp_g_eq : Lp.map (MulAut.conj x).toMonoidHom = Lp := hLp_g.trans h
    have h2 : (Lb.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        Lb.map (MulAut.conj x).toMonoidHom := by
      rw [← hLp]
      exact hLp_g_eq
    have hLbeq : Lb.map (MulAut.conj x).toMonoidHom = Lb :=
      Subgroup.map_injective (MulAut.conj x).injective h2
    exact hLb_ne_Lp (hLp.trans hLbeq).symm

theorem s1611e3_c9k1_engine {W : Type} [CommGroup W] [Finite W]
    {L Q T : Subgroup (MulAut W)} {A B : Subgroup W} {x : MulAut W}
    (hLQ : ∀ a ∈ L, ∀ b ∈ Q, a * b = b * a)
    (hinfLQ : L ⊓ Q = ⊥)
    (hTp : IsPGroup 2 ↥T)
    (hxT : x ∈ T)
    (hTnorm : ∀ t ∈ T, ∀ y ∈ L ⊔ Q, t * y * t⁻¹ ∈ L ⊔ Q)
    (hAinv : ∀ a ∈ L, ∀ u ∈ A, a u ∈ A)
    (hBinv : ∀ b ∈ Q, ∀ u ∈ B, b u ∈ B)
    (hB : B = A.map x.toMonoidHom)
    (hAsup : A ⊔ B = ⊤)
    (hAinf : A ⊓ B = ⊥)
    (hxB : B.map x.toMonoidHom = A)
    (hfixB : ∀ b ∈ Q, ∀ a ∈ A, b a = a)
    (hfixA : ∀ a ∈ L, ∀ b ∈ B, a b = b)
    (hcardTE : Nat.card ↥(T ⊓ (L ⊔ Q)) = 64)
    (hstabA : ∀ w ∈ A ⊓ fixV (T ⊓ L), w ≠ 1 →
      Nat.card ↥(L ⊓ centSub (Subgroup.zpowers w)) = 24)
    (hstabB : ∀ w ∈ B ⊓ fixV (T ⊓ Q), w ≠ 1 →
      Nat.card ↥(Q ⊓ centSub (Subgroup.zpowers w)) = 24)
    (hcardW : 2 ∣ Nat.card W) :
    ∃ X : Subgroup (MulAut W), X ≤ L ⊔ Q ∧ IsPGroup 3 ↥X ∧ ¬ IsCyclic ↥X ∧
      (∀ y ∈ X, y ^ 3 = 1) ∧ Permutes X T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hvP, hvne⟩ := hTp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := W) hcardW (a := (1 : W))
    (MulAction.mem_fixedPoints.mpr fun m => map_one (m : MulAut W))
  have hvfix : v ∈ fixV T := mem_fixV.mpr fun t ht => MulAction.mem_fixedPoints.mp hvP ⟨t, ht⟩
  have hv1 : v ≠ 1 := fun h => hvne h.symm
  obtain ⟨w, hwA, w', hw'B, hwv⟩ :=
    Subgroup.mem_sup.1 (by rw [hAsup]; exact Subgroup.mem_top v)
  have hxv : x v = v := (mem_fixV.1 hvfix) x hxT
  have hxwB : x w ∈ B := by
    rw [hB]; exact Subgroup.mem_map_of_mem x.toMonoidHom hwA
  have hxw'A : x w' ∈ A := by
    have h : x w' ∈ B.map x.toMonoidHom := Subgroup.mem_map_of_mem x.toMonoidHom hw'B
    rwa [hxB] at h
  have hmulx : x w * x w' = w' * w := by
    have h1 : x (w * w') = w * w' := by rw [hwv]; exact hxv
    rw [map_mul] at h1
    rw [h1]
    exact mul_comm w w'
  have hswap : x w = w' ∧ x w' = w :=
    s1611e3_eq_of_mul_eq_mul_of_inf_bot (by rw [inf_comm]; exact hAinf)
      hxwB hxw'A hw'B hwA hmulx
  have hw1 : w ≠ 1 := by
    intro hw
    have hw'1 : w' = 1 := by rw [← hswap.1, hw, map_one]
    exact hv1 (by rw [← hwv, hw, hw'1, mul_one])
  have hw'1 : w' ≠ 1 := by
    intro hw'
    have hw1' : w = 1 := by rw [← hswap.2, hw', map_one]
    exact hv1 (by rw [← hwv, hw1', hw', mul_one])
  have hwfix : w ∈ fixV (T ⊓ L) := by
    rw [mem_fixV]
    intro t ht
    have htv : t v = v := (mem_fixV.1 hvfix) t ht.1
    have htw' : t w' = w' := hfixA t ht.2 w' hw'B
    have h1 : t w * w' = w * w' := by
      calc t w * w' = t w * t w' := by rw [htw']
        _ = t (w * w') := by rw [map_mul]
        _ = t v := by rw [hwv]
        _ = v := htv
        _ = w * w' := hwv.symm
    exact mul_right_cancel h1
  have hw'fix : w' ∈ fixV (T ⊓ Q) := by
    rw [mem_fixV]
    intro u hu
    have huv : u v = v := (mem_fixV.1 hvfix) u hu.1
    have huw : u w = w := hfixB u hu.2 w hwA
    have huw'B : u w' ∈ B := hBinv u hu.2 w' hw'B
    have h1 : w * u w' = w * w' := by
      calc w * u w' = u w * u w' := by rw [huw]
        _ = u (w * w') := by rw [map_mul]
        _ = u v := by rw [hwv]
        _ = v := huv
        _ = w * w' := hwv.symm
    exact mul_left_cancel h1
  let P : Subgroup (MulAut W) := L ⊓ centSub (Subgroup.zpowers w)
  let P' : Subgroup (MulAut W) := Q ⊓ centSub (Subgroup.zpowers w')
  let N : Subgroup (MulAut W) := P ⊔ P'
  have hPcard : Nat.card ↥P = 24 := hstabA w (Subgroup.mem_inf.2 ⟨hwA, hwfix⟩) hw1
  have hP'card : Nat.card ↥P' = 24 := hstabB w' (Subgroup.mem_inf.2 ⟨hw'B, hw'fix⟩) hw'1
  have hPP'comm : ∀ a ∈ P, ∀ b ∈ P', a * b = b * a :=
    fun a ha b hb => hLQ a (Subgroup.mem_inf.1 ha).1 b (Subgroup.mem_inf.1 hb).1
  have hPP'inf : P ⊓ P' = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyP, hyP'⟩ := Subgroup.mem_inf.1 hy
    have hyL : y ∈ L := (Subgroup.mem_inf.1 hyP).1
    have hyQ : y ∈ Q := (Subgroup.mem_inf.1 hyP').1
    have hmem : y ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hinfLQ]; exact ⟨hyL, hyQ⟩
    simpa using hmem
  have hNcard : Nat.card ↥N = 24 * 24 := by
    show Nat.card ↥(P ⊔ P') = 24 * 24
    rw [CFSG.card_sup_eq_mul_of_commute P P' (fun a ha b hb => hPP'comm a ha b hb) hPP'inf,
      hPcard, hP'card]
  have hNleE : N ≤ L ⊔ Q :=
    sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
  have hNfix : N ≤ centSub (Subgroup.zpowers v) := by
    intro y hy
    rw [s1611e3_mem_centSub_zpowers_iff]
    obtain ⟨a, haP, b, hbP', hyab⟩ :=
      s1611e3_exists_mul_of_mem_sup_of_commute
        (fun a ha b hb => hPP'comm a ha b hb) hy
    have haL : a ∈ L := (Subgroup.mem_inf.1 haP).1
    have hbQ : b ∈ Q := (Subgroup.mem_inf.1 hbP').1
    have haw : a w = w := (s1611e3_mem_centSub_zpowers_iff a w).mp (Subgroup.mem_inf.1 haP).2
    have hbw' : b w' = w' :=
      (s1611e3_mem_centSub_zpowers_iff b w').mp (Subgroup.mem_inf.1 hbP').2
    have haw' : a w' = w' := hfixA a haL w' hw'B
    have hbw : b w = w := hfixB b hbQ w hwA
    have hav : a v = v := by rw [← hwv, map_mul, haw, haw']
    have hbv : b v = v := by rw [← hwv, map_mul, hbw, hbw']
    rw [← hyab, MulAut.mul_apply, hbv, hav]
  have hENleN : (L ⊔ Q) ⊓ centSub (Subgroup.zpowers v) ≤ N := by
    intro y hy
    obtain ⟨hyLQ, hyfix⟩ := Subgroup.mem_inf.1 hy
    have hyv : y v = v := (s1611e3_mem_centSub_zpowers_iff y v).mp hyfix
    obtain ⟨a, haL, b, hbQ, hyab⟩ := s1611e3_exists_mul_of_mem_sup_of_commute hLQ hyLQ
    have hawA : a w ∈ A := hAinv a haL w hwA
    have hbw'B : b w' ∈ B := hBinv b hbQ w' hw'B
    have hbw : b w = w := hfixB b hbQ w hwA
    have haw' : a w' = w' := hfixA a haL w' hw'B
    have hsplit : a w * b w' = w * w' := by
      have h : a (b v) = v := by rw [← MulAut.mul_apply, hyab]; exact hyv
      rw [← hwv] at h
      rw [map_mul, map_mul, hbw, hfixA a haL (b w') hbw'B] at h
      exact h
    obtain ⟨haw, hbw'⟩ :=
      s1611e3_eq_of_mul_eq_mul_of_inf_bot hAinf hawA hbw'B hwA hw'B hsplit
    have haP : a ∈ P :=
      Subgroup.mem_inf.2 ⟨haL, (s1611e3_mem_centSub_zpowers_iff a w).mpr haw⟩
    have hbP' : b ∈ P' :=
      Subgroup.mem_inf.2 ⟨hbQ, (s1611e3_mem_centSub_zpowers_iff b w').mpr hbw'⟩
    rw [← hyab]
    exact Subgroup.mul_mem_sup haP hbP'
  have hNeq : N = (L ⊔ Q) ⊓ centSub (Subgroup.zpowers v) :=
    le_antisymm (le_inf hNleE hNfix) hENleN
  have hNT : ∀ t ∈ T, ∀ y ∈ N, t * y * t⁻¹ ∈ N := by
    intro t ht y hy
    rw [hNeq] at hy ⊢
    obtain ⟨hyE, hyfix⟩ := Subgroup.mem_inf.1 hy
    have hyv : y v = v := (s1611e3_mem_centSub_zpowers_iff y v).mp hyfix
    refine Subgroup.mem_inf.2 ⟨hTnorm t ht y hyE, ?_⟩
    rw [s1611e3_mem_centSub_zpowers_iff]
    have htv : t v = v := (mem_fixV.1 hvfix) t ht
    have htinv : t⁻¹ v = v := (mem_fixV.1 hvfix) t⁻¹ (T.inv_mem ht)
    show (t * y * t⁻¹) v = v
    rw [MulAut.mul_apply, MulAut.mul_apply, htinv, hyv, htv]
  have hTN : (T : Set (MulAut W)) * (N : Set (MulAut W)) =
      (N : Set (MulAut W)) * (T : Set (MulAut W)) := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_mul] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact Set.mem_mul.mpr ⟨a * b * a⁻¹, hNT a ha b hb, a, ha, by group⟩
    · intro hx
      rw [Set.mem_mul] at hx
      obtain ⟨b, hb, a, ha, rfl⟩ := hx
      exact Set.mem_mul.mpr ⟨a, ha, a⁻¹ * b * a, hNT a⁻¹ (T.inv_mem ha) b hb, by group⟩
  have hNTeq : N ⊓ T = T ⊓ (L ⊔ Q) := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨hyN, hyT⟩
      exact ⟨hyT, hNleE hyN⟩
    · rintro y ⟨hyT, hyE⟩
      have hyv : y v = v := (mem_fixV.1 hvfix) y hyT
      refine ⟨?_, hyT⟩
      rw [hNeq]
      exact ⟨hyE, (s1611e3_mem_centSub_zpowers_iff y v).mpr hyv⟩
  have hNTinf : Nat.card ↥(N ⊓ T) = 64 := by
    rw [hNTeq, hcardTE]
  have hNTset : Nat.card ((N : Set (MulAut W)) * (T : Set (MulAut W))) =
      9 * Nat.card ↥T := by
    have h := CFSG.Quasithin.H13.AS91.card_mul_set_mul_card_inf N T
    rw [hNcard, hNTinf] at h
    omega
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3P : 3 ∣ Nat.card ↥P := by rw [hPcard]; norm_num
  have h3P' : 3 ∣ Nat.card ↥P' := by rw [hP'card]; norm_num
  obtain ⟨gP, hgP⟩ := exists_prime_orderOf_dvd_card' 3 h3P
  obtain ⟨gP', hgP'⟩ := exists_prime_orderOf_dvd_card' 3 h3P'
  let X₃ : Subgroup (MulAut W) := (Subgroup.zpowers gP).map P.subtype
  let X₃' : Subgroup (MulAut W) := (Subgroup.zpowers gP').map P'.subtype
  let X : Subgroup (MulAut W) := X₃ ⊔ X₃'
  have hX₃le : X₃ ≤ P := Subgroup.map_subtype_le _
  have hX₃'le : X₃' ≤ P' := Subgroup.map_subtype_le _
  have hX₃card : Nat.card ↥X₃ = 3 := by
    rw [Subgroup.card_map_of_injective (f := P.subtype) P.subtype_injective, Nat.card_zpowers,
      hgP]
  have hX₃'card : Nat.card ↥X₃' = 3 := by
    rw [Subgroup.card_map_of_injective (f := P'.subtype) P'.subtype_injective, Nat.card_zpowers,
      hgP']
  have hXinf : X₃ ⊓ X₃' = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy₃, hy₃'⟩ := Subgroup.mem_inf.1 hy
    have hyL : y ∈ L := (hX₃le.trans inf_le_left) hy₃
    have hyQ : y ∈ Q := (hX₃'le.trans inf_le_left) hy₃'
    have hmem : y ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hinfLQ]; exact ⟨hyL, hyQ⟩
    simpa using hmem
  have hXcomm : ∀ a ∈ X₃, ∀ b ∈ X₃', a * b = b * a :=
    fun a ha b hb => hLQ a ((hX₃le.trans inf_le_left) ha) b ((hX₃'le.trans inf_le_left) hb)
  have hXcard : Nat.card ↥X = 9 := by
    show Nat.card ↥(X₃ ⊔ X₃') = 9
    rw [CFSG.card_sup_eq_mul_of_commute X₃ X₃'
      (fun a ha b hb => hXcomm a ha b hb) hXinf, hX₃card, hX₃'card]
  have hXexp : ∀ y ∈ X, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨a, ha, b, hb, hyab⟩ :=
      s1611e3_exists_mul_of_mem_sup_of_commute (fun a ha b hb => hXcomm a ha b hb) hy
    have ha3 : a ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := ↥X₃) (x := ⟨a, ha⟩)
      rw [hX₃card] at h
      simpa using congrArg Subtype.val h
    have hb3 : b ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := ↥X₃') (x := ⟨b, hb⟩)
      rw [hX₃'card] at h
      simpa using congrArg Subtype.val h
    rw [← hyab, Commute.mul_pow (hXcomm a ha b hb) 3, ha3, hb3, one_mul]
  have hXp : IsPGroup 3 ↥X :=
    IsPGroup.of_card (n := 2) (by rw [hXcard]; norm_num)
  have hXnc : ¬ IsCyclic ↥X := by
    intro hcyc
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
    have hord : orderOf g = 9 := by
      have h1 : Nat.card (Subgroup.zpowers g) = Nat.card ↥X := by
        rw [hg, Subgroup.card_top]
      rw [Nat.card_zpowers, hXcard] at h1
      exact h1
    have hg3 : g ^ 3 = 1 :=
      Subtype.ext (by simpa using hXexp (g : MulAut W) g.2)
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hg3
    have hle : orderOf g ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hXN : X ≤ N :=
    sup_le (hX₃le.trans le_sup_left) (hX₃'le.trans le_sup_right)
  have hXTinf : X ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyX, hyT⟩ := Subgroup.mem_inf.1 hy
    have h1 : Nat.card ↥(X ⊓ T) ∣ 64 := by
      have hle : X ⊓ T ≤ N ⊓ T := fun z hz => ⟨hXN hz.1, hz.2⟩
      rw [← hNTinf]
      exact Subgroup.card_dvd_of_le hle
    have h2 : Nat.card ↥(X ⊓ T) ∣ 9 := by
      have hle : X ⊓ T ≤ X := inf_le_left
      rw [← hXcard]
      exact Subgroup.card_dvd_of_le hle
    have hc1 : Nat.card ↥(X ⊓ T) = 1 := by
      have h3 : Nat.card ↥(X ⊓ T) ∣ Nat.gcd 64 9 := Nat.dvd_gcd h1 h2
      rw [show Nat.gcd 64 9 = 1 by norm_num] at h3
      exact Nat.dvd_one.mp h3
    have : y ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← Subgroup.card_eq_one.mp hc1]
      exact hy
    simpa using this
  have hXTset : Nat.card ((X : Set (MulAut W)) * (T : Set (MulAut W))) =
      9 * Nat.card ↥T := by
    have h := CFSG.Quasithin.H13.AS91.card_mul_set_mul_card_inf X T
    rw [hXTinf, hXcard, Subgroup.card_bot, mul_one] at h
    simpa using h
  have hXT_eq : (X : Set (MulAut W)) * (T : Set (MulAut W)) =
      (N : Set (MulAut W)) * (T : Set (MulAut W)) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · intro y hy
      rw [Set.mem_mul] at hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      exact Set.mem_mul.mpr ⟨a, hXN ha, b, hb, rfl⟩
    · have hNTn : ((N : Set (MulAut W)) * (T : Set (MulAut W))).ncard = 9 * Nat.card ↥T := by
        simpa [Nat.card_coe_set_eq] using hNTset
      have hXTn : ((X : Set (MulAut W)) * (T : Set (MulAut W))).ncard = 9 * Nat.card ↥T := by
        simpa [Nat.card_coe_set_eq] using hXTset
      rw [hNTn, hXTn]
  have hTX_eq : (T : Set (MulAut W)) * (X : Set (MulAut W)) =
      (N : Set (MulAut W)) * (T : Set (MulAut W)) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · intro y hy
      rw [Set.mem_mul] at hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      have hmem : a * b ∈ (T : Set (MulAut W)) * (N : Set (MulAut W)) :=
        Set.mem_mul.mpr ⟨a, ha, b, hXN hb, rfl⟩
      rwa [hTN] at hmem
    · have hTXn : ((T : Set (MulAut W)) * (X : Set (MulAut W))).ncard = 9 * Nat.card ↥T := by
        change Nat.card ((T : Set (MulAut W)) * (X : Set (MulAut W))) = 9 * Nat.card ↥T
        have h := CFSG.Quasithin.H13.AS91.card_mul_set_mul_card_inf T X
        rw [inf_comm, hXTinf, hXcard, Subgroup.card_bot, mul_one] at h
        omega
      have hNTn : ((N : Set (MulAut W)) * (T : Set (MulAut W))).ncard = 9 * Nat.card ↥T := by
        simpa [Nat.card_coe_set_eq] using hNTset
      rw [hNTn, hTXn]
  refine ⟨X, hXN.trans hNleE, hXp, hXnc, hXexp, ?_⟩
  show (X : Set (MulAut W)) * (T : Set (MulAut W)) =
    (T : Set (MulAut W)) * (X : Set (MulAut W))
  rw [hXT_eq, hTX_eq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
