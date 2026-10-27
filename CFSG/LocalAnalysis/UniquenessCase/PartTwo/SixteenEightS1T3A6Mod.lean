module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3CardSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarPt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A6Trans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A67Cyc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A6ModA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem ThreeNat.exists_J_alt6 (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
    (e : ↥L ≃* alternatingGroup (Fin 6)) (hK : Nat.card ↥(s1t3KBar A L) = 168) :
    ∃ J : Subgroup (MulAut W), J ≤ A ∧ T ≤ J ∧ (∃ x : ℕ, Nat.card ↥J = 2 ^ x * 3 ^ 2) ∧
      ∀ g ∈ J, IsPGroup 3 (Subgroup.zpowers g) →
        ∃ (n : ↥L) (k : MulAut W), (n : MulAut W) * k = g ∧ k ∈ s1t3KBar A L ∧
          (((e n : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)).cycleType = 0 ∨
            ((e n : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)).cycleType = {3} ∨
            ((e n : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)).cycleType = {3, 3}) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N, hNA, hLleN, hNfix, hNcomm, hNKbot, hNKsup, -⟩ := h.structure_of_seven h7
  let K : Subgroup (MulAut W) := s1t3KBar A L
  have hKA : K ≤ A := inf_le_left
  have hNnormA : (N.subgroupOf A).Normal :=
    s16t3_a6mod_normal_of_sup_of_commute hNA hNKsup hNcomm
  have hKnormA : (K.subgroupOf A).Normal := by
    refine s16t3_a6mod_normal_of_sup_of_commute (N := K) (K := N) (A := A) hKA ?_ ?_
    · rw [sup_comm]; exact hNKsup
    · intro k hk n hn; exact (hNcomm n hn k hk).symm
  have hA_normN : A ≤ Subgroup.normalizer (N : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mp hNnormA
  have hA_normK : A ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKA).mp hKnormA
  have hTNsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ N) N :=
    h.sylow.inf_of_le_normalizer hNA hA_normN
  have hTKsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K :=
    h.sylow.inf_of_le_normalizer hKA hA_normK
  have hNnorm_L : N ≤ Subgroup.normalizer (L : Set (MulAut W)) := hNA.trans h.normal
  have hLNnorm : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLleN).mpr hNnorm_L
  have hcardL : Nat.card ↥L = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hAcard : Nat.card ↥A = Nat.card ↥N * Nat.card ↥K := by
    have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute N K hNcomm).1
    rw [hNKsup, hNKbot, Subgroup.card_bot, mul_one] at h
    exact h
  have hdvd := h.card_dvd_of_seven h7
  have hN_dvd : Nat.card ↥N ∣ 2 * Nat.card ↥L := by
    have hdvd' : Nat.card ↥N * Nat.card ↥K ∣ 336 * Nat.card ↥L := by
      rwa [hAcard] at hdvd
    rw [hK] at hdvd'
    have h' : Nat.card ↥N * 168 ∣ 168 * (2 * Nat.card ↥L) := by
      rwa [show (336 : ℕ) = 168 * 2 by norm_num, mul_assoc] at hdvd'
    rw [mul_comm (Nat.card ↥N) 168] at h'
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 168)).1 h'
  have hN_dvd720 : Nat.card ↥N ∣ 720 := by
    rw [hcardL] at hN_dvd
    norm_num at hN_dvd
    exact hN_dvd
  have hLNcard : Nat.card ↥N = Nat.card ↥L * L.relIndex N := by
    rw [← (L.subgroupOf N).card_mul_index, Subgroup.relIndex,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLleN).toEquiv]
  have h360 : 360 ∣ Nat.card ↥N := by
    rw [hcardL] at hLNcard
    exact ⟨L.relIndex N, hLNcard⟩
  have hcardN : Nat.card ↥N = 360 ∨ Nat.card ↥N = 720 := by
    obtain ⟨p, hp⟩ := h360
    have hp_dvd : p ∣ 2 := by
      have h : 360 * p ∣ 360 * 2 := by
        rw [← hp]
        simpa using hN_dvd720
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 360)).1 h
    rcases (Nat.dvd_prime Nat.prime_two).1 hp_dvd with hp1 | hp2
    · left; rw [hp, hp1, mul_one]
    · right
      calc Nat.card ↥N = 360 * p := hp
        _ = 360 * 2 := by rw [hp2]
        _ = 720 := by norm_num
  have hrel : L.relIndex N ≤ 2 := by
    rw [hcardL] at hLNcard
    rcases hcardN with hN | hN <;> rw [hN] at hLNcard <;> omega
  obtain ⟨I₀, hI₀, -, J₂, hJ₂le, hT₂le, -, hJ₂card, -⟩ :=
    h.exists_point_stabilizer h7 hK
  have hL : UC22.IsAlt ↥L 6 := ⟨e⟩
  have hI₀nat : SumOfNatShape L I₀ (I₀ ⊓ fixV L) 1 := h.natural_of_mem_irrSet hI₀
  have hnat := s16t3_alt6_natural h.quasi hL hI₀nat
  let U : Type := s16t3_U L I₀
  have hcardU : Nat.card U = 16 := by
    have hbase := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((I₀ ⊓ fixV L).subgroupOf I₀)
    have hZ : Nat.card ↥((I₀ ⊓ fixV L).subgroupOf I₀) = Nat.card ↥(I₀ ⊓ fixV L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hZ] at hbase
    have hcancel : Nat.card U * Nat.card ↥(I₀ ⊓ fixV L) =
        16 * Nat.card ↥(I₀ ⊓ fixV L) := by
      rw [← hbase, hnat.1]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcancel
  let inclN : ↥N →* ↥A :=
    { toFun := fun n => ⟨(n : MulAut W), hNA n.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let inclNT : ↥(T ⊓ N) →* ↥N :=
    { toFun := fun t => ⟨(t : MulAut W), t.2.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let actN : ↥N →* MulAut U := (s16t3_sectionHom h h7 hI₀).comp inclN
  let actT : ↥(T ⊓ N) →* MulAut U := actN.comp inclNT
  letI : MulAction ↥N U := MulAction.compHom U actN
  letI : MulAction ↥(T ⊓ N) U := MulAction.compHom U actT
  have h2dvdU : 2 ∣ Nat.card U := by rw [hcardU]; norm_num
  have h1fix : (1 : U) ∈ MulAction.fixedPoints ↥(T ⊓ N) U := by
    rw [MulAction.mem_fixedPoints]
    intro t
    change actT t (1 : U) = 1
    exact map_one (actT t)
  obtain ⟨u, hufix, hu1⟩ :=
    (hTNsyl.isPGroup).exists_fixed_point_of_prime_dvd_card_of_fixed_point U h2dvdU h1fix
  let J₁sub : Subgroup ↥N := MulAction.stabilizer ↥N u
  let J₁ : Subgroup (MulAut W) := J₁sub.map N.subtype
  have hJ₁le : J₁ ≤ N := Subgroup.map_subtype_le _
  have hJ₁card_eq : Nat.card ↥J₁ = Nat.card ↥J₁sub :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hTleJ₁ : T ⊓ N ≤ J₁ := by
    intro x hx
    refine Subgroup.mem_map.2 ⟨⟨x, hx.2⟩, ?_, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change (⟨x, hx⟩ : ↥(T ⊓ N)) • u = u
    exact MulAction.mem_fixedPoints.1 hufix ⟨x, hx⟩
  haveI : Fintype ↥N := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbit ↥N u) := Fintype.ofFinite _
  haveI : Fintype ↥J₁sub := Fintype.ofFinite _
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥N) u
  have hOS' : Nat.card (MulAction.orbit ↥N u) * Nat.card ↥J₁sub = Nat.card ↥N := by
    simpa only [J₁sub, Nat.card_eq_fintype_card] using hOS
  have horbit : MulAction.orbit ↥N u = {v : U | v ≠ 1} := by
    ext v
    constructor
    · rintro ⟨n, rfl⟩ h
      have h' : actN n u = actN n 1 := by
        rw [map_one]
        simpa only [MulAction.compHom_smul_def, MulAut.smul_def] using h
      exact hu1 ((actN n).injective h').symm
    · intro hv
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
      obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective u
      have hx₀not : (x₀ : W) ∉ fixV L := by
        intro hfix
        apply hu1
        have h1 : (x₀ : U) = 1 :=
          (QuotientGroup.eq_one_iff x₀).2
            (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨x₀.2, hfix⟩))
        rw [← h1]
        exact hx₀
      have hxnot : (x : W) ∉ fixV L := by
        intro hfix
        apply hv
        exact (QuotientGroup.eq_one_iff x).2
          (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨x.2, hfix⟩))
      obtain ⟨l, hl, hfixl⟩ := hnat.2 x₀ x₀.2 hx₀not x x.2 hxnot
      let n : ↥N := ⟨l, hLleN hl⟩
      refine ⟨n, ?_⟩
      change actN n u = QuotientGroup.mk x
      have hlxI : (n : MulAut W) x₀ ∈ I₀ := hI₀.2.2.1 l hl x₀ x₀.2
      have hact : actN n u = QuotientGroup.mk (⟨l x₀, hlxI⟩ : ↥I₀) := by
        rw [← hx₀]
        exact s16t3_sectionHom_l h h7 hI₀ hl x₀ hlxI
      rw [hact, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf]
      exact ⟨I₀.mul_mem hlxI (I₀.inv_mem x.2), hfixl⟩
  have hsub : Nat.card {v : U // v ≠ 1} = 15 := by
    haveI : Fintype U := Fintype.ofFinite _
    haveI : Fintype {v : U // v = 1} := Fintype.ofFinite _
    haveI : Fintype {v : U // v ≠ 1} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun v : U => v = 1),
      Fintype.card_subtype_eq (1 : U), ← Nat.card_eq_fintype_card, hcardU]
  have hcardOrbit : Nat.card (MulAction.orbit ↥N u) = 15 := by
    have he : MulAction.orbit ↥N u ≃ {v : U // v ≠ 1} :=
      Equiv.subtypeEquivRight (fun v => by simp [horbit])
    rw [Nat.card_congr he, hsub]
  have hJ₁card : Nat.card ↥J₁ = 3 * Nat.card ↥(T ⊓ N) := by
    have hOS15 : 15 * Nat.card ↥J₁sub = Nat.card ↥N := by
      have h := hOS
      have ho : Fintype.card (MulAction.orbit ↥N u) = 15 := by
        rw [← Nat.card_eq_fintype_card]
        exact hcardOrbit
      rw [ho] at h
      simpa [J₁sub, Nat.card_eq_fintype_card] using h
    have hN_eq : Nat.card ↥N = 15 * (3 * Nat.card ↥(T ⊓ N)) := by
      rcases hcardN with hN | hN
      · have hT : Nat.card ↥(T ⊓ N) = 8 := by
          rw [hTNsyl.card_eq, hN, show (360 : ℕ) = 2 ^ 3 * 45 by norm_num,
            Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
            Nat.factorization_pow_self Nat.prime_two,
            Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 45)]
          norm_num
        rw [hN, hT]
      · have hT : Nat.card ↥(T ⊓ N) = 16 := by
          rw [hTNsyl.card_eq, hN, show (720 : ℕ) = 2 ^ 4 * 45 by norm_num,
            Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
            Nat.factorization_pow_self Nat.prime_two,
            Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 45)]
          norm_num
        rw [hN, hT]
    have h15 : 15 * Nat.card ↥J₁sub = 15 * (3 * Nat.card ↥(T ⊓ N)) := by
      rw [hOS15, hN_eq]
    rw [hJ₁card_eq]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : (0 : ℕ) < 15) h15
  have hTcardT : Nat.card ↥T = Nat.card ↥(T ⊓ N) * Nat.card ↥(T ⊓ K) := by
    have hA := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute N K hNcomm).1
    rw [hNKsup, hNKbot, Subgroup.card_bot, mul_one] at hA
    rw [h.sylow.card_eq, hA, Nat.factorization_mul (Nat.card_pos (α := ↥N)).ne'
        (Nat.card_pos (α := ↥K)).ne', Finsupp.add_apply, pow_add,
      (hTNsyl.card_eq).symm, (hTKsyl.card_eq).symm]
  have hTleJ : T ≤ J₁ ⊔ J₂ := by
    have hcomm : ∀ h ∈ T ⊓ N, ∀ k ∈ T ⊓ K, h * k = k * h :=
      fun h hh k hk => hNcomm h hh.2 k hk.2
    have hcardprod : Nat.card ↥((T ⊓ N) ⊔ (T ⊓ K)) =
        Nat.card ↥(T ⊓ N) * Nat.card ↥(T ⊓ K) := by
      have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute (T ⊓ N) (T ⊓ K) hcomm).1
      have hinf : (T ⊓ N) ⊓ (T ⊓ K) = ⊥ := by
        apply le_antisymm _ bot_le
        rw [← hNKbot]
        exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
      rw [hinf, Subgroup.card_bot, mul_one] at h
      exact h
    have hle : (T ⊓ N) ⊔ (T ⊓ K) ≤ T := sup_le inf_le_left inf_le_left
    have heq : (T ⊓ N) ⊔ (T ⊓ K) = T :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardprod, hTcardT])
    rw [← heq]
    exact sup_le_sup hTleJ₁ hT₂le
  refine ⟨J₁ ⊔ J₂, sup_le (hJ₁le.trans hNA) (hJ₂le.trans hKA), hTleJ, ?_, ?_⟩
  · have hcomm : ∀ h ∈ J₁, ∀ k ∈ J₂, h * k = k * h :=
      fun h hh k hk => hNcomm h (hJ₁le hh) k (hJ₂le hk)
    have hcardJ : Nat.card ↥(J₁ ⊔ J₂) = 9 * Nat.card ↥T := by
      have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute J₁ J₂ hcomm).1
      have hinf : J₁ ⊓ J₂ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        have hxN : x ∈ N := hJ₁le hx.1
        have hxK : x ∈ K := hJ₂le hx.2
        have : x ∈ (⊥ : Subgroup (MulAut W)) := by rw [← hNKbot]; exact ⟨hxN, hxK⟩
        simpa using this
      rw [hinf, Subgroup.card_bot, mul_one] at h
      rw [h, hJ₁card, hJ₂card, hTcardT]
      ring
    obtain ⟨m, hm⟩ := h.sylow.isPGroup.exists_card_eq
    refine ⟨m, ?_⟩
    rw [hcardJ, hm]
    ring
  · intro g hg hg3
    have hcomm : ∀ h ∈ J₁, ∀ k ∈ J₂, h * k = k * h :=
      fun h hh k hk => hNcomm h (hJ₁le hh) k (hJ₂le hk)
    obtain ⟨j₁, hj₁, j₂, hj₂, hgjk⟩ :=
      s16t3_a6mod_exists_mul_of_mem_sup_of_commute hcomm hg
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 3) (G := Subgroup.zpowers g)).1 hg3
    have horder : orderOf g = 3 ^ m := by rw [← Nat.card_zpowers]; exact hm
    have hgpow : g ^ 3 ^ m = 1 := (orderOf_dvd_iff_pow_eq_one).1 (by rw [horder])
    have hcommg : Commute j₁ j₂ := hcomm j₁ hj₁ j₂ hj₂
    have hj₁pow : j₁ ^ 3 ^ m = 1 := by
      have h1 : (j₁ * j₂) ^ 3 ^ m = 1 := by rw [hgjk]; exact hgpow
      rw [hcommg.mul_pow] at h1
      have h2 : j₁ ^ 3 ^ m = (j₂ ^ 3 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hmemN : j₁ ^ 3 ^ m ∈ N := hJ₁le (J₁.pow_mem hj₁ _)
      have hmemK : (j₂ ^ 3 ^ m)⁻¹ ∈ K := K.inv_mem (hJ₂le (J₂.pow_mem hj₂ _))
      have hbot : j₁ ^ 3 ^ m ∈ (⊥ : Subgroup (MulAut W)) := by
        rw [← hNKbot]; exact ⟨hmemN, h2 ▸ hmemK⟩
      simpa using hbot
    have hoddj : Odd (orderOf j₁) := by
      have hdvd : orderOf j₁ ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hj₁pow
      exact Nat.not_even_iff_odd.1 fun he =>
        (by norm_num : ¬ (2 : ℕ) ∣ 3)
          (Nat.prime_two.dvd_of_dvd_pow (even_iff_two_dvd.mp he |>.trans hdvd))
    have hj₁L : j₁ ∈ L :=
      s16t3_a6mod_mem_of_odd_order_of_relIndex_le_two hLNnorm hrel (hJ₁le hj₁) hoddj
    refine ⟨⟨j₁, hj₁L⟩, j₂, hgjk, hJ₂le hj₂, ?_⟩
    have hdvd : orderOf ((e ⟨j₁, hj₁L⟩ : alternatingGroup (Fin 6)) :
        Equiv.Perm (Fin 6)) ∣ 3 ^ m := by
      apply orderOf_dvd_of_pow_eq_one
      have h1 : (⟨j₁, hj₁L⟩ : ↥L) ^ 3 ^ m = 1 := Subtype.ext hj₁pow
      calc ((e ⟨j₁, hj₁L⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ^ 3 ^ m
          = ((e (⟨j₁, hj₁L⟩ ^ 3 ^ m) : alternatingGroup (Fin 6)) :
              Equiv.Perm (Fin 6)) := by
            rw [map_pow, ← Subgroup.coe_pow]
        _ = 1 := by rw [h1, map_one]; rfl
    exact s16t3_cycleType_of_isPGroup_three (n := 6) (by norm_num)
      ((e ⟨j₁, hj₁L⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) (by
        rw [IsPGroup.iff_card]
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
        exact ⟨k, by rw [Nat.card_zpowers]; exact hk⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
