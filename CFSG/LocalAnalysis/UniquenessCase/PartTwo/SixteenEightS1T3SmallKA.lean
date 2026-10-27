module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Kbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Par

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16t3_le_normalizer_of_comm {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) : H ≤ Subgroup.normalizer K := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro k
  have hconj : ∀ m ∈ K, h * m * h⁻¹ = m := by
    intro m hm
    rw [hcomm h hh m hm, mul_assoc, mul_inv_cancel, mul_one]
  constructor
  · intro hk
    rw [hconj k hk]
    exact hk
  · intro hk
    have h1 : h * (h * k * h⁻¹) * h⁻¹ = h * k * h⁻¹ := hconj (h * k * h⁻¹) hk
    have h2 : h * k * h⁻¹ = k := by
      have := congrArg (fun z => h⁻¹ * z * h) h1
      simpa [mul_assoc] using this
    rw [← h2]
    exact hk

private theorem s16t3_mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  have hnorm : H ≤ Subgroup.normalizer K := s16t3_le_normalizer_of_comm hcomm
  haveI : (K.subgroupOf (H ⊔ K)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hnorm Subgroup.le_normalizer)
  have hx' : (⟨x, hx⟩ : ↥(H ⊔ K)) ∈ H.subgroupOf (H ⊔ K) ⊔ K.subgroupOf (H ⊔ K) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := H.subgroupOf (H ⊔ K))
      (t := K.subgroupOf (H ⊔ K)) (x := ⟨x, hx⟩)).1 hx'
  exact ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, (z : G), Subgroup.mem_subgroupOf.mp hz,
    by simpa using congrArg Subtype.val hyz⟩

private theorem s16t3_card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G]
    {H K : Subgroup G} (h : H ≤ Subgroup.normalizer K) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  haveI : (K.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h
  haveI : (K.subgroupOf (H ⊔ K)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H K h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf H)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf (H ⊔ K))
  have h3 : Nat.card (K.subgroupOf H) = Nat.card (H ⊓ K : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (K.subgroupOf (H ⊔ K)) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

private theorem s16t3_card_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K :=
  s16t3_card_sup_mul_card_inf_of_le_normalizer (s16t3_le_normalizer_of_comm hcomm)

private theorem s16t3_smul_eq_self_of_stableUnder {X : Subgroup (MulAut W)} {I : Subgroup W}
    (h : StableUnder X I) {x : MulAut W} (hx : x ∈ X) : x • I = I := by
  refine le_antisymm ?_ ?_
  · intro u hu
    obtain ⟨v, hv, hvx⟩ := (Subgroup.mem_smul_pointwise_iff_exists u x I).1 hu
    rw [← hvx]
    exact h x hx v hv
  · intro v hv
    refine (Subgroup.mem_smul_pointwise_iff_exists v x I).2 ⟨x⁻¹ • v, ?_, ?_⟩
    · rw [MulAut.smul_def]
      exact h x⁻¹ (X.inv_mem hx) v hv
    · simp

private theorem s16t3_map_mem_irrSet_of_mem {A L : Subgroup (MulAut W)}
    (hA : A ≤ Subgroup.normalizer (L : Set (MulAut W))) {g : MulAut W} (hg : g ∈ A)
    {I : Subgroup W} (hI : I ∈ irrSet L) : I.map g.toMonoidHom ∈ irrSet L :=
  CFSG.LocalAnalysis.WeakClosure81.map_mem_irrSet
    (fun x hx => (Subgroup.mem_normalizer_iff.1 (hA hg) x).1 hx)
    (fun x hx => by
      have := (Subgroup.mem_normalizer_iff.1 (hA (A.inv_mem hg)) x).1 hx
      simpa using this) hI

private theorem s16t3_K0_trans {A L T N : Subgroup (MulAut W)} (h : ThreeNat A L T)
    (hNA : N ≤ A) (hNfix : ∀ a ∈ N, ∀ I ∈ irrSet L, I.map a.toMonoidHom = I)
    (hNcomm : ∀ n ∈ N, ∀ k ∈ s1t3KBar A L, n * k = k * n)
    (hNKsup : N ⊔ s1t3KBar A L = A) :
    ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ k ∈ s1t3KBar A L, I₂ = I₁.map k.toMonoidHom := by
  have hNnorm : N ≤ Subgroup.normalizer (s1t3KBar A L : Set (MulAut W)) :=
    s16t3_le_normalizer_of_comm hNcomm
  have hK0A : s1t3KBar A L ≤ A := inf_le_left
  have hA_norm_K0 : A ≤ Subgroup.normalizer (s1t3KBar A L : Set (MulAut W)) :=
    calc A = N ⊔ s1t3KBar A L := hNKsup.symm
      _ ≤ Subgroup.normalizer (s1t3KBar A L : Set (MulAut W)) :=
          sup_le hNnorm Subgroup.le_normalizer
  have hK0NA : ((s1t3KBar A L).subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK0A).2 hA_norm_K0
  intro I₁ hI₁ I₂ hI₂
  obtain ⟨g, hgA, hg⟩ := h.trans I₁ hI₁ I₂ hI₂
  have hgA' : g ∈ A := hgA.1
  haveI : ((s1t3KBar A L).subgroupOf A).Normal := hK0NA
  have hsupA : N.subgroupOf A ⊔ (s1t3KBar A L).subgroupOf A = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNA hK0A, hNKsup, Subgroup.subgroupOf_self]
  have hmem : (⟨g, hgA'⟩ : ↥A) ∈ N.subgroupOf A ⊔ (s1t3KBar A L).subgroupOf A := by
    rw [hsupA]
    trivial
  obtain ⟨n, hn, k, hk, hnk⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := N.subgroupOf A)
      (t := (s1t3KBar A L).subgroupOf A) (x := ⟨g, hgA'⟩)).1 hmem
  have hnN : (n : MulAut W) ∈ N := Subgroup.mem_subgroupOf.mp hn
  have hkK0 : (k : MulAut W) ∈ s1t3KBar A L := Subgroup.mem_subgroupOf.mp hk
  have hnk' : (n : MulAut W) * (k : MulAut W) = g := by
    have := congrArg Subtype.val hnk
    simpa using this
  refine ⟨(k : MulAut W), hkK0, ?_⟩
  rw [hg, ← hnk']
  have hIk : I₁.map (k : MulAut W).toMonoidHom ∈ irrSet L :=
    s16t3_map_mem_irrSet_of_mem h.normal k.2 hI₁
  have h1 : I₁.map ((n : MulAut W) * (k : MulAut W)).toMonoidHom =
      (I₁.map (k : MulAut W).toMonoidHom).map (n : MulAut W).toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [h1, hNfix (n : MulAut W) hnN (I₁.map (k : MulAut W).toMonoidHom) hIk]

private theorem s16t3_K0_stab {A L T : Subgroup (MulAut W)} (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) (hK : Nat.card ↥(s1t3KBar A L) = 168)
    (hK0trans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ k ∈ s1t3KBar A L, I₂ = I₁.map k.toMonoidHom) :
    ∃ Stab : Subgroup (MulAut W), Stab ≤ s1t3KBar A L ∧
      Nat.card ↥Stab = 24 ∧ T ⊓ s1t3KBar A L ≤ Stab := by
  have hodd : Odd (Nat.card ↥(irrSet L)) := by rw [h7]; norm_num
  obtain ⟨I0, hI0, hI0stableT⟩ := s16t3_exists_stable_irr h hodd
  have hI0stable : StableUnder (T ⊓ s1t3KBar A L) I0 :=
    fun x hx u hu => hI0stableT x hx.1 u hu
  letI : MulAction ↥(s1t3KBar A L) (Subgroup W) :=
    MulAction.compHom (Subgroup W) (Subgroup.subtype (s1t3KBar A L))
  let StabSub : Subgroup ↥(s1t3KBar A L) := MulAction.stabilizer ↥(s1t3KBar A L) I0
  let Stab : Subgroup (MulAut W) := StabSub.map (s1t3KBar A L).subtype
  have horbit : MulAction.orbit ↥(s1t3KBar A L) I0 = irrSet L := by
    ext I
    constructor
    · rintro ⟨k, rfl⟩
      change (k : ↥(s1t3KBar A L)) • I0 ∈ irrSet L
      have hk : (k : MulAut W) ∈ A := (Subgroup.mem_inf.1 k.2).1
      rw [MulAction.compHom_smul_def, Subgroup.pointwise_smul_def]
      exact s16t3_map_mem_irrSet_of_mem h.normal hk hI0
    · intro hI
      obtain ⟨k, hkK0, hkI⟩ := hK0trans I0 hI0 I hI
      refine ⟨⟨k, hkK0⟩, ?_⟩
      change (⟨k, hkK0⟩ : ↥(s1t3KBar A L)) • I0 = I
      rw [MulAction.compHom_smul_def, Subgroup.pointwise_smul_def]
      exact hkI.symm
  have hstab_card : Nat.card ↥Stab = 24 := by
    haveI : Fintype ↥(s1t3KBar A L) := Fintype.ofFinite _
    haveI : Fintype (MulAction.orbit ↥(s1t3KBar A L) I0) := Fintype.ofFinite _
    haveI : Fintype (MulAction.stabilizer ↥(s1t3KBar A L) I0) := Fintype.ofFinite _
    have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (G := ↥(s1t3KBar A L)) I0
    have hOS' : Nat.card (MulAction.orbit ↥(s1t3KBar A L) I0) *
        Nat.card (MulAction.stabilizer ↥(s1t3KBar A L) I0) =
        Nat.card ↥(s1t3KBar A L) := by
      simpa only [Nat.card_eq_fintype_card] using hOS
    have h1 : Nat.card (MulAction.orbit ↥(s1t3KBar A L) I0) = 7 := by rw [horbit, h7]
    have h2 : Nat.card (MulAction.stabilizer ↥(s1t3KBar A L) I0) = 24 := by
      have h := hOS'
      rw [h1, hK] at h
      omega
    rw [show Stab = (MulAction.stabilizer ↥(s1t3KBar A L) I0).map
        (s1t3KBar A L).subtype from rfl,
      Subgroup.card_map_of_injective (s1t3KBar A L).subtype_injective]
    exact h2
  refine ⟨Stab, Subgroup.map_subtype_le _, hstab_card, ?_⟩
  intro x hx
  have hxK0 : x ∈ s1t3KBar A L := hx.2
  have hxsmul : (⟨x, hxK0⟩ : ↥(s1t3KBar A L)) • I0 = I0 := by
    show (x : MulAut W) • I0 = I0
    exact s16t3_smul_eq_self_of_stableUnder hI0stable hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hxK0⟩, hxsmul, rfl⟩

private theorem s16t3_T_eq {N A L T : Subgroup (MulAut W)} (h : ThreeNat A L T)
    (hNA : N ≤ A) (hNcomm : ∀ n ∈ N, ∀ k ∈ s1t3KBar A L, n * k = k * n)
    (hNKbot : N ⊓ s1t3KBar A L = ⊥) (hNKsup : N ⊔ s1t3KBar A L = A)
    (hK : Nat.card ↥(s1t3KBar A L) = 168) :
    T = (T ⊓ N) ⊔ (T ⊓ s1t3KBar A L) ∧ Nat.card ↥(T ⊓ s1t3KBar A L) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK0A : s1t3KBar A L ≤ A := inf_le_left
  have hNnorm : N ≤ Subgroup.normalizer (s1t3KBar A L : Set (MulAut W)) :=
    s16t3_le_normalizer_of_comm hNcomm
  have hK0normN : s1t3KBar A L ≤ Subgroup.normalizer (N : Set (MulAut W)) :=
    s16t3_le_normalizer_of_comm fun k hk n hn => (hNcomm n hn k hk).symm
  have hA_norm_K0 : A ≤ Subgroup.normalizer (s1t3KBar A L : Set (MulAut W)) :=
    calc A = N ⊔ s1t3KBar A L := hNKsup.symm
      _ ≤ Subgroup.normalizer (s1t3KBar A L : Set (MulAut W)) :=
          sup_le hNnorm Subgroup.le_normalizer
  have hA_norm_N : A ≤ Subgroup.normalizer (N : Set (MulAut W)) :=
    calc A = N ⊔ s1t3KBar A L := hNKsup.symm
      _ ≤ Subgroup.normalizer (N : Set (MulAut W)) :=
          sup_le Subgroup.le_normalizer hK0normN
  have hTK0syl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ s1t3KBar A L) (s1t3KBar A L) :=
    h.sylow.inf_of_le_normalizer hK0A hA_norm_K0
  have hTN_syl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ N) N :=
    h.sylow.inf_of_le_normalizer hNA hA_norm_N
  have hTK0card : Nat.card ↥(T ⊓ s1t3KBar A L) = 8 := by
    rw [hTK0syl.card_eq, hK]
    have h168 : 168 = 2 ^ 3 * 21 := by norm_num
    rw [h168, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hcommTN : ∀ x ∈ (T ⊓ N : Subgroup (MulAut W)),
      ∀ y ∈ (T ⊓ s1t3KBar A L : Subgroup (MulAut W)), x * y = y * x :=
    fun x hx y hy => hNcomm x hx.2 y hy.2
  have hinfTN : (T ⊓ N) ⊓ (T ⊓ s1t3KBar A L) = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    have hmem : x ∈ N ⊓ s1t3KBar A L := ⟨hx1.2, hx2.2⟩
    rw [hNKbot] at hmem
    simpa using hmem
  have hcardsupTN : Nat.card ↥((T ⊓ N) ⊔ (T ⊓ s1t3KBar A L)) =
      Nat.card ↥(T ⊓ N) * Nat.card ↥(T ⊓ s1t3KBar A L) := by
    have h := s16t3_card_sup_of_commute hcommTN
    rw [hinfTN, Subgroup.card_bot, mul_one] at h
    exact h
  have hA : Nat.card ↥A = Nat.card ↥N * Nat.card ↥(s1t3KBar A L) := by
    have h := s16t3_card_sup_mul_card_inf_of_le_normalizer (H := N) (K := s1t3KBar A L) hNnorm
    rw [hNKbot, Subgroup.card_bot, mul_one, hNKsup] at h
    exact h
  have hcardT : Nat.card ↥T = Nat.card ↥((T ⊓ N) ⊔ (T ⊓ s1t3KBar A L)) := by
    rw [hcardsupTN, hTN_syl.card_eq, hTK0syl.card_eq, h.sylow.card_eq, hA,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, pow_add]
  exact ⟨(Subgroup.eq_of_le_of_card_ge (H := (T ⊓ N) ⊔ (T ⊓ s1t3KBar A L)) (K := T)
    (sup_le inf_le_left inf_le_left) (le_of_eq hcardT)).symm, hTK0card⟩

theorem s16t3_kBar_of_parab {A L T : Subgroup (MulAut W)} (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) (hK : Nat.card ↥(s1t3KBar A L) = 168)
    {a : ℕ} (hP : T3Parab L T a) :
    ∃ J : Subgroup (MulAut W), T ≤ J ∧ J ≤ L ⊔ s1t3KBar A L ⊔ T ∧
      Nat.card ↥J = 3 ^ (a + 1) * Nat.card ↥T ∧
      ∀ x ∈ J, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1 := by
  classical
  obtain ⟨N, hNA, hLN, hNfix, hNcomm, hNKbot, hNKsup, -⟩ := h.structure_of_seven h7
  have hK0trans := s16t3_K0_trans h hNA hNfix hNcomm hNKsup
  obtain ⟨Stab, hStabK0, hstab_card, hTK0Stab⟩ := s16t3_K0_stab h h7 hK hK0trans
  obtain ⟨hT_eq, hTK0card⟩ := s16t3_T_eq h hNA hNcomm hNKbot hNKsup hK
  obtain ⟨JL, hTJL, hJLLT, hJLcard, hJLexp⟩ := hP
  have hT_le_NK : T ≤ N ⊔ (T ⊓ s1t3KBar A L) :=
    hT_eq.le.trans (sup_le (fun x hx => Subgroup.mem_sup_left hx.2)
      (fun x hx => Subgroup.mem_sup_right hx))
  have hJL_le : JL ≤ N ⊔ (T ⊓ s1t3KBar A L) :=
    hJLLT.trans (sup_le (fun x hx => Subgroup.mem_sup_left (hLN hx)) hT_le_NK)
  have hTK0JL : T ⊓ s1t3KBar A L ≤ JL := fun x hx => hTJL hx.1
  have hJL_eq : JL = (JL ⊓ N) ⊔ (T ⊓ s1t3KBar A L) := by
    refine le_antisymm ?_ (sup_le inf_le_left hTK0JL)
    intro x hx
    obtain ⟨n, hn, t, ht, hnt⟩ := s16t3_mem_sup_of_commute
      (H := N) (K := T ⊓ s1t3KBar A L) (fun a ha b hb => hNcomm a ha b hb.2) (hJL_le hx)
    have hnJL : n ∈ JL := by
      have hn_eq : n = x * t⁻¹ := by rw [← hnt]; group
      rw [hn_eq]
      exact JL.mul_mem hx (JL.inv_mem (hTK0JL ht))
    rw [← hnt]
    exact Subgroup.mul_mem_sup ⟨hnJL, hn⟩ ht
  refine ⟨(JL ⊓ N) ⊔ Stab, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hcomp : t ∈ (T ⊓ N) ⊔ (T ⊓ s1t3KBar A L) := by rw [← hT_eq]; exact ht
    obtain ⟨x, hx, y, hy, hxy⟩ := s16t3_mem_sup_of_commute
      (H := T ⊓ N) (K := T ⊓ s1t3KBar A L)
      (fun p hp q hq => hNcomm p hp.2 q hq.2) hcomp
    have hx' : x ∈ JL ⊓ N := ⟨hTJL hx.1, hx.2⟩
    have hy' : y ∈ Stab := hTK0Stab hy
    rw [← hxy]
    exact Subgroup.mul_mem_sup hx' hy'
  · refine sup_le ?_ ?_
    · have h2 : L ⊔ T ≤ (L ⊔ s1t3KBar A L) ⊔ T :=
        sup_le (fun x hx => Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))
          (fun x hx => Subgroup.mem_sup_right hx)
      exact inf_le_left.trans (hJLLT.trans h2)
    · exact hStabK0.trans (fun x hx => Subgroup.mem_sup_left (Subgroup.mem_sup_right hx))
  · have hcommJ : ∀ x ∈ (JL ⊓ N : Subgroup (MulAut W)), ∀ y ∈ Stab, x * y = y * x :=
      fun x hx y hy => hNcomm x hx.2 y (hStabK0 hy)
    have hinfJ : (JL ⊓ N) ⊓ Stab = ⊥ := by
      refine le_bot_iff.1 fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
      have hmem : x ∈ N ⊓ s1t3KBar A L := ⟨hx1.2, hStabK0 hx2⟩
      rw [hNKbot] at hmem
      simpa using hmem
    have hcardJ := s16t3_card_sup_of_commute hcommJ
    rw [hinfJ, Subgroup.card_bot, mul_one, hstab_card] at hcardJ
    have hcomm' : ∀ x ∈ (JL ⊓ N : Subgroup (MulAut W)),
        ∀ y ∈ (T ⊓ s1t3KBar A L : Subgroup (MulAut W)), x * y = y * x :=
      fun x hx y hy => hNcomm x hx.2 y hy.2
    have hinf' : (JL ⊓ N) ⊓ (T ⊓ s1t3KBar A L) = ⊥ := by
      refine le_bot_iff.1 fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
      have hmem : x ∈ N ⊓ s1t3KBar A L := ⟨hx1.2, hx2.2⟩
      rw [hNKbot] at hmem
      simpa using hmem
    have hcardJL := s16t3_card_sup_of_commute hcomm'
    rw [hinf', Subgroup.card_bot, mul_one, hTK0card, ← hJL_eq, hJLcard] at hcardJL
    have hcardT := s16t3_card_sup_of_commute
      (H := T ⊓ N) (K := T ⊓ s1t3KBar A L) (fun x hx y hy => hNcomm x hx.2 y hy.2)
    have hinfT : (T ⊓ N) ⊓ (T ⊓ s1t3KBar A L) = ⊥ := by
      refine le_bot_iff.1 fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
      have hmem : x ∈ N ⊓ s1t3KBar A L := ⟨hx1.2, hx2.2⟩
      rw [hNKbot] at hmem
      simpa using hmem
    rw [hinfT, Subgroup.card_bot, mul_one, hTK0card, ← hT_eq] at hcardT
    have hcancel : Nat.card ↥(JL ⊓ N) = 3 ^ a * Nat.card ↥(T ⊓ N) := by
      have h : Nat.card ↥(JL ⊓ N) * 8 = (3 ^ a * Nat.card ↥(T ⊓ N)) * 8 := by
        rw [← hcardJL, hcardT]
        ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 8) h
    rw [hcardJ, hcancel, hcardT, pow_succ]
    ring
  · intro x hx n hxn
    obtain ⟨p, hp, q, hq, hpq⟩ := s16t3_mem_sup_of_commute
      (H := JL ⊓ N) (K := Stab) (fun a ha b hb => hNcomm a ha.2 b (hStabK0 hb)) hx
    have hcomm_pq : p * q = q * p := hNcomm p hp.2 q (hStabK0 hq)
    have hxn' : (p * q) ^ 3 ^ n = 1 := by rw [hpq]; exact hxn
    have hpow : p ^ 3 ^ n * q ^ 3 ^ n = 1 := by
      rw [← (show Commute p q from hcomm_pq).mul_pow]
      exact hxn'
    have hpinv : p ^ 3 ^ n = (q ^ 3 ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    have hp1 : p ^ 3 ^ n = 1 := by
      have hmem : p ^ 3 ^ n ∈ N ⊓ s1t3KBar A L := by
        refine ⟨N.pow_mem hp.2 _, ?_⟩
        rw [hpinv]
        exact (s1t3KBar A L).inv_mem ((s1t3KBar A L).pow_mem (hStabK0 hq) _)
      rw [hNKbot] at hmem
      simpa using hmem
    have hq1 : q ^ 3 ^ n = 1 := by
      have := hpow
      rw [hp1, one_mul] at this
      exact this
    have hp3 : p ^ 3 = 1 := hJLexp p hp.1 n hp1
    have hq3 : q ^ 3 = 1 := by
      have hord : orderOf q ∣ 3 ^ n := orderOf_dvd_iff_pow_eq_one.2 hq1
      have h24 : orderOf q ∣ 24 := by
        rw [← hstab_card]
        exact Subgroup.orderOf_dvd_natCard Stab hq
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hord
      have hm1 : m ≤ 1 := by
        by_contra hlt
        have h2 : 2 ≤ m := by omega
        have hdvd : 3 ^ 2 ∣ 3 ^ m := Nat.pow_dvd_pow 3 h2
        have h9 : (9 : ℕ) ∣ 24 := by
          have := hdvd.trans (hm ▸ h24)
          simpa using this
        obtain ⟨c, hc⟩ := h9
        omega
      have hord3 : orderOf q ∣ 3 := by
        rw [hm]
        interval_cases m <;> norm_num
      exact orderOf_dvd_iff_pow_eq_one.1 hord3
    rw [← hpq, (show Commute p q from hcomm_pq).mul_pow, hp3, hq3, mul_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
