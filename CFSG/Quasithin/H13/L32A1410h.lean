module

public import CFSG.Quasithin.H13.L32NLem144Ba
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13.Q1410

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L144B L128P
open scoped IsKleinFour

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}

omit [Finite G] in
theorem T_le_normalizer_I2 : T ≤ Subgroup.normalizer (i128 T L V (fsuV1 T V) : Set G) :=
  le_p128.trans (le_normalizer_conjClosure _ _)

omit [Finite G] in
theorem U_le_I2 : fsuU T V ≤ i128 T L V (fsuV1 T V) := le_conjClosure _ _

omit [Finite G] in
theorem comm_of_conj_eq {y v : G} (h : y * v * y⁻¹ = v) : v * y = y * v := by
  calc v * y = y * v * y⁻¹ * y := by rw [h]
    _ = y * v := by group

omit [Finite G] in
theorem omegaOneCenter_le_centralizer (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hz => (Subgroup.mem_inf.mp hz.1).2

omit [Finite G] in
theorem isKleinFour_of_card_four' {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

variable (h12213 : Stmt12_2_13) (B : Base G T L V V₂ g)
include h12213 B

theorem I2_le_normalizer_V2 : i128 T L V (fsuV1 T V) ≤ Subgroup.normalizer (V₂ : Set G) :=
  (i128_le_p128 B.h1222 h12213 B.s1282).trans (p128_le_normalizer le_rfl B.s1282.v2)

theorem oTwoUpper_le_I2 : oTwoUpper (p128 T L V) ≤ i128 T L V (fsuV1 T V) := by
  rw [i128_eq_sup B.h1222 h12213 B.s1282]; exact le_sup_left

theorem not_I2_le_H : ¬ i128 T L V (fsuV1 T V) ≤ l32nH T V := by
  intro h
  obtain ⟨k, hk, hkN⟩ := exists_not_mem_normalizer B.h1222 B.s1282
  exact hkN (h (oTwoUpper_le_I2 h12213 B hk))

theorem V2_le_conjClosure : V₂ ≤ conjClosure (fsuV1 T V) (i128 T L V (fsuV1 T V)) := by
  have hs := B.s1282
  have hV₁2 : Nat.card (fsuV1 T V) = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨a, ha, ha1, b, hb, hbV₁⟩ := exists_gens hV₁2 hV₂4
  obtain ⟨k, hk, hka, hkb, -⟩ :=
    exists_rotation_mem B.h1222 hs.hyp hs.v1 hs.v2 hs.le ha ha1 hb hbV₁
  have hkI := oTwoUpper_le_I2 h12213 B hk
  intro v hv
  rcases eq_of_mem_four hs.le hV₁2 hV₂4 ha ha1 hbV₁ hb hv with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact le_conjClosure _ _ ha
  · rw [← hka]; exact mem_conjClosure hkI ha
  · rw [← hkb, ← hka, show k * (k * a * k⁻¹) * k⁻¹ = (k * k) * a * (k * k)⁻¹ by group]
    exact mem_conjClosure ((i128 T L V (fsuV1 T V)).mul_mem hkI hkI) ha

omit h12213 in
theorem exists_transvection_U {a c : G} (ha : a ∈ fsuV1 T V) (ha1 : a ≠ 1) (hc : c ∈ V₂)
    (hcV : c ∉ fsuV1 T V) : ∃ l ∈ fsuU T V, l * a * l⁻¹ = a ∧ l * c * l⁻¹ = a * c := by
  obtain ⟨_, S⟩ := B.set14
  have hcU := B.V2U hc
  obtain ⟨l, hl, hlc⟩ : ∃ l ∈ fsuU T V, l * c ≠ c * l := by
    by_contra hcon
    push Not at hcon
    apply hcV
    rw [← B.zU]
    exact Subgroup.mem_inf.mpr ⟨hcU, Subgroup.mem_centralizer_iff.mpr fun h hh => hcon h hh⟩
  have hZ : l * c * l⁻¹ * c⁻¹ ∈ fsuV1 T V := by
    rw [← B.zU]; exact B.comm_center l hl c hcU
  have hne : l * c * l⁻¹ * c⁻¹ ≠ 1 := fun h => hlc (by
    calc l * c = (l * c * l⁻¹ * c⁻¹) * (c * l) := by group
      _ = c * l := by rw [h, one_mul])
  have haZ : a ∈ centerOf (fsuU T V) := by rw [B.zU]; exact ha
  refine ⟨l, hl, ?_, ?_⟩
  · have := Subgroup.mem_centralizer_iff.mp haZ.2 l hl
    rw [this, mul_inv_cancel_right]
  · rcases S.eq_of_mem_V1 ha ha1 hZ with h | h
    · exact absurd h hne
    · calc l * c * l⁻¹ = (l * c * l⁻¹ * c⁻¹) * c := by group
        _ = a * c := by rw [h]

theorem autOn_I2 : autOn (i128 T L V (fsuV1 T V)) V₂ = ⊤ := by
  have hs := B.s1282
  obtain ⟨-, hsq, hab⟩ := hs.hyp.card_sq
  have hV₁2 : Nat.card (fsuV1 T V) = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨a, ha, ha1, b, hb, hbV₁⟩ := exists_gens hV₁2 hV₂4
  obtain ⟨k, hk, hka, hkb, -⟩ :=
    exists_rotation_mem B.h1222 hs.hyp hs.v1 hs.v2 hs.le ha ha1 hb hbV₁
  obtain ⟨l, hl, hla, hlb⟩ := exists_transvection_U B ha ha1 hb hbV₁
  have haV : a ∈ V := hs.v1.1 ha
  have hbV : b ∈ V := hs.v2.1 hb
  have hb2 : b * b = 1 := by rw [← pow_two]; exact hsq b hbV
  have haV₂ : a ∈ V₂ := hs.le ha
  have hb1 : b ≠ 1 := fun e => hbV₁ (e ▸ (fsuV1 T V).one_mem)
  have hsel : ∀ {y : G}, y ∈ V₂ → y ≠ 1 → y = a ∨ y = b ∨ y = a * b := fun hy hy1 => by
    rcases eq_of_mem_four hs.le hV₁2 hV₂4 ha ha1 hbV₁ hb hy with e | e | e | e
    · exact absurd e hy1
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  rw [eq_top_iff]
  intro α _
  have hne1 : ∀ (v : ↥V₂), (v : G) ≠ 1 → ((α v : ↥V₂) : G) ≠ 1 := fun v hv e => hv (by
    have : α v = 1 := Subtype.ext e
    rw [← map_one α] at this
    exact congrArg Subtype.val (α.injective this))
  have hne : ((α ⟨a, haV₂⟩ : ↥V₂) : G) ≠ ((α ⟨b, hb⟩ : ↥V₂) : G) := fun e => hbV₁ (by
    have h1 := congrArg Subtype.val (α.injective (Subtype.ext e))
    simp only at h1
    rw [← h1]
    exact ha)
  obtain ⟨p, hp, hpa, hpb⟩ := exists_conj_pair (X := i128 T L V (fsuV1 T V))
    (oTwoUpper_le_I2 h12213 B hk) (U_le_I2 hl) hka hkb hla hlb (hab a haV b hbV) hb2
    (hsel (α ⟨a, haV₂⟩).2 (hne1 _ ha1)) (hsel (α ⟨b, hb⟩).2 (hne1 _ hb1)) hne
  have hpN : p ∈ Subgroup.normalizer (V₂ : Set G) := I2_le_normalizer_V2 h12213 B hp
  refine ⟨⟨p, hpN⟩, hp, ?_⟩
  refine MulEquiv.ext fun v => Subtype.ext ?_
  rw [conjAct_coe_apply]
  rcases eq_of_mem_four hs.le hV₁2 hV₂4 ha ha1 hbV₁ hb v.2 with e | e | e | e
  · have hv : v = 1 := Subtype.ext e
    rw [hv, map_one]
    simp
  · have hv : v = ⟨a, haV₂⟩ := Subtype.ext e
    rw [hv]
    exact hpa
  · have hv : v = ⟨b, hb⟩ := Subtype.ext e
    rw [hv]
    exact hpb
  · have hv : v = ⟨a, haV₂⟩ * ⟨b, hb⟩ := Subtype.ext e
    rw [hv, map_mul]
    show p * (a * b) * p⁻¹ = ((α ⟨a, haV₂⟩ : ↥V₂) : G) * ((α ⟨b, hb⟩ : ↥V₂) : G)
    rw [← hpa, ← hpb]
    group

theorem card_oTwoQuot_I2 : Nat.card (OTwoQuot (i128 T L V (fsuV1 T V))) = 6 := by
  have hs := B.s1282
  obtain ⟨-, hsq, -⟩ := hs.hyp.card_sq
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  have : IsKleinFour ↥V₂ := isKleinFour_of_card_four' hV₂4 fun x => Subtype.ext (by
    simpa using hsq x (hs.v2.1 x.2))
  have h1 := card_autOn_eq_relIndex (I2_le_normalizer_V2 h12213 B)
  rw [autOn_I2 h12213 B, Subgroup.card_top, kleinFour_automorphism_card,
    i128_inf_centralizer B.h1222 h12213 hs] at h1
  have hsub : (pCoreOf 2 (i128 T L V (fsuV1 T V))).subgroupOf (i128 T L V (fsuV1 T V)) =
      CFSG.Open.pCore 2 ↥(i128 T L V (fsuV1 T V)) := map_subtype_subgroupOf' _
  show (CFSG.Open.pCore 2 ↥(i128 T L V (fsuV1 T V))).index = 6
  rw [← hsub]
  exact h1.symm

theorem nonempty_oTwoQuot_I2 :
    Nonempty (OTwoQuot (i128 T L V (fsuV1 T V)) ≃* Equiv.Perm (Fin 3)) := by
  have hs := B.s1282
  have hV₁2 : Nat.card (fsuV1 T V) = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨a, ha, ha1, b, hb, hbV₁⟩ := exists_gens hV₁2 hV₂4
  obtain ⟨k, hk, hka, hkb, -⟩ :=
    exists_rotation_mem B.h1222 hs.hyp hs.v1 hs.v2 hs.le ha ha1 hb hbV₁
  obtain ⟨l, hl, hla, hlb⟩ := exists_transvection_U B ha ha1 hb hbV₁
  have hkI := oTwoUpper_le_I2 h12213 B hk
  have hlI := U_le_I2 (L := L) hl
  let π := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(i128 T L V (fsuV1 T V)))
  refine CFSG.GH74.M12.Hyp.nonempty_mulEquiv_perm_three_of_card_six
    (card_oTwoQuot_I2 h12213 B) (π ⟨k, hkI⟩) (π ⟨l, hlI⟩) fun hc => ?_
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hc
  have hcmem : (k * l)⁻¹ * (l * k) ∈ pCoreOf 2 (i128 T L V (fsuV1 T V)) := ⟨_, hc, rfl⟩
  have hcC := ((i128_inf_centralizer B.h1222 h12213 hs).ge hcmem).2
  have hfix := Subgroup.mem_centralizer_iff.mp hcC a (hs.le ha)
  have hca : ((k * l)⁻¹ * (l * k)) * a * ((k * l)⁻¹ * (l * k))⁻¹ = a := by
    rw [← hfix]
    group
  have e1 : (k * l) * a * (k * l)⁻¹ = b := by
    calc (k * l) * a * (k * l)⁻¹ = k * (l * a * l⁻¹) * k⁻¹ := by group
      _ = b := by rw [hla, hka]
  have e2 : (l * k) * a * (l * k)⁻¹ = a * b := by
    calc (l * k) * a * (l * k)⁻¹ = l * (k * a * k⁻¹) * l⁻¹ := by group
      _ = a * b := by rw [hka, hlb]
  have e3 : a * b = b := by
    calc a * b = (l * k) * a * (l * k)⁻¹ := e2.symm
      _ = (k * l) * (((k * l)⁻¹ * (l * k)) * a * ((k * l)⁻¹ * (l * k))⁻¹) * (k * l)⁻¹ := by
          group
      _ = b := by rw [hca, e1]
  exact ha1 (by
    calc a = (a * b) * b⁻¹ := by group
      _ = b * b⁻¹ := by rw [e3]
      _ = 1 := by group)

omit h12213 in
theorem isSylowTwoOf_I2 :
    IsSylowTwoOf (T ⊓ i128 T L V (fsuV1 T V)) (i128 T L V (fsuV1 T V)) :=
  A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo B.hyp.fsu.sylow le_sup_right)
    le_sup_left (sup_le Subgroup.le_normalizer T_le_normalizer_I2)

theorem borelOf_I2_le : borelOf (i128 T L V (fsuV1 T V)) T ≤ T := by
  have hs := B.s1282
  obtain ⟨-, hsq, hab⟩ := hs.hyp.card_sq
  have hV₁2 : Nat.card (fsuV1 T V) = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨a, ha, ha1, c, hc, hcV₁⟩ := exists_gens hV₁2 hV₂4
  obtain ⟨l, hl, hla, hlc⟩ := exists_transvection_U B ha ha1 hc hcV₁
  have haV : a ∈ V := hs.v1.1 ha
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hsq a haV
  have hO2 : pCoreOf 2 (i128 T L V (fsuV1 T V)) ≤ T :=
    pCoreOf_le_of_le_normalizer B.hyp.fsu.sylow T_le_normalizer_I2
  have hcent : ∀ y ∈ i128 T L V (fsuV1 T V), y * a * y⁻¹ = a → y * c * y⁻¹ = c → y ∈ T := by
    intro y hy hya hyc
    apply hO2
    rw [← i128_inf_centralizer B.h1222 h12213 hs]
    refine Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    rcases eq_of_mem_four hs.le hV₁2 hV₂4 ha ha1 hcV₁ hc hv with rfl | rfl | rfl | rfl
    · simp
    · exact comm_of_conj_eq hya
    · exact comm_of_conj_eq hyc
    · calc a * c * y = a * (c * y) := by group
        _ = a * (y * c) := by rw [comm_of_conj_eq hyc]
        _ = (a * y) * c := by group
        _ = (y * a) * c := by rw [comm_of_conj_eq hya]
        _ = y * (a * c) := by group
  intro x hx
  obtain ⟨hxI, hxN⟩ := Subgroup.mem_inf.mp hx
  have hxV₂ := I2_le_normalizer_V2 h12213 B hxI
  have hlT : l ∈ T := B.UT hl
  have hw : x⁻¹ * l * x ∈ T := by
    have hlTI : l ∈ T ⊓ i128 T L V (fsuV1 T V) := Subgroup.mem_inf.mpr ⟨hlT, U_le_I2 hl⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) l).mp hlTI
    rw [inv_inv] at this
    exact (Subgroup.mem_inf.mp this).1
  have hTa : (x⁻¹ * l * x) * a = a * (x⁻¹ * l * x) :=
    Subgroup.mem_centralizer_iff.mp
      (omegaOneCenter_le_centralizer T (Subgroup.mem_inf.mp ha).2) _ hw
  have hla' : l * (x * a * x⁻¹) * l⁻¹ = x * a * x⁻¹ := by
    calc l * (x * a * x⁻¹) * l⁻¹ = x * ((x⁻¹ * l * x) * a) * x⁻¹ * l⁻¹ := by group
      _ = x * (a * (x⁻¹ * l * x)) * x⁻¹ * l⁻¹ := by rw [hTa]
      _ = x * a * x⁻¹ := by group
  have ha'V : x * a * x⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hxV₂ a).mp (hs.le ha)
  have ha'1 : x * a * x⁻¹ ≠ 1 := fun h => ha1 (by
    calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group)
  have hxa : x * a * x⁻¹ = a := by
    rcases eq_of_mem_four hs.le hV₁2 hV₂4 ha ha1 hcV₁ hc ha'V with h | h | h | h
    · exact absurd h ha'1
    · exact h
    · exfalso
      rw [h, hlc] at hla'
      exact ha1 (by
        calc a = a * c * c⁻¹ := by group
          _ = c * c⁻¹ := by rw [hla']
          _ = 1 := by group)
    · exfalso
      have hl_ac : l * (a * c) * l⁻¹ = c := by
        calc l * (a * c) * l⁻¹ = (l * a * l⁻¹) * (l * c * l⁻¹) := by group
          _ = a * (a * c) := by rw [hla, hlc]
          _ = c := by rw [← mul_assoc, ha2, one_mul]
      rw [h, hl_ac] at hla'
      exact ha1 (by
        calc a = a * c * c⁻¹ := by group
          _ = c * c⁻¹ := by rw [← hla']
          _ = 1 := by group)
  have hc'V : x * c * x⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hxV₂ c).mp hc
  rcases eq_of_mem_four hs.le hV₁2 hV₂4 ha ha1 hcV₁ hc hc'V with h | h | h | h
  · exfalso
    have hc1 : c = 1 := by
      calc c = x⁻¹ * (x * c * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    exact hcV₁ (by rw [hc1]; exact one_mem _)
  · exfalso
    have hca : c = a := by
      calc c = x⁻¹ * (x * c * x⁻¹) * x := by group
        _ = x⁻¹ * (x * a * x⁻¹) * x := by rw [h, hxa]
        _ = a := by group
    exact hcV₁ (by rw [hca]; exact ha)
  · exact hcent x hxI hxa h
  · have hy : l⁻¹ * x ∈ i128 T L V (fsuV1 T V) :=
      (i128 T L V (fsuV1 T V)).mul_mem ((i128 T L V (fsuV1 T V)).inv_mem (U_le_I2 hl)) hxI
    have hlinv_a : l⁻¹ * a * l = a := by
      calc l⁻¹ * a * l = l⁻¹ * (l * a * l⁻¹) * l := by rw [hla]
        _ = a := by group
    have hlinv_c : l⁻¹ * (a * c) * l = c := by
      calc l⁻¹ * (a * c) * l = l⁻¹ * (l * c * l⁻¹) * l := by rw [hlc]
        _ = c := by group
    have hya : (l⁻¹ * x) * a * (l⁻¹ * x)⁻¹ = a := by
      calc (l⁻¹ * x) * a * (l⁻¹ * x)⁻¹ = l⁻¹ * (x * a * x⁻¹) * l := by group
        _ = a := by rw [hxa, hlinv_a]
    have hyc : (l⁻¹ * x) * c * (l⁻¹ * x)⁻¹ = c := by
      calc (l⁻¹ * x) * c * (l⁻¹ * x)⁻¹ = l⁻¹ * (x * c * x⁻¹) * l := by group
        _ = c := by rw [h, hlinv_c]
    rw [show x = l * (l⁻¹ * x) by group]
    exact T.mul_mem hlT (hcent _ hy hya hyc)

end CFSG.Quasithin.H13.Q1410

end
