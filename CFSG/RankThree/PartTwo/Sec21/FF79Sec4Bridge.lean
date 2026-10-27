module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma44Beta
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma44
import CFSG.RankThree.PartTwo.Sec15.Liebeck155KFacts
import CFSG.GF2Type.Smith1979.CaseIIExclL52
import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
import CFSG.CharacterTheory.Wreathed.FullDefectCanonicalStructure
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

private lemma br_mem_of_two_pow_mem {J' : Subgroup G} :
    ∀ (n : ℕ) (a : G) (m : ℕ), Odd m → a ^ m = 1 → a ^ (2 ^ n) ∈ J' → a ∈ J' := by
  intro n
  induction n with
  | zero => intro a m _ _ h; simpa using h
  | succ n ih =>
    intro a m hm ha h
    have h2 : a ^ 2 ∈ J' := by
      refine ih (a ^ 2) m hm ?_ ?_
      · rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]
      · rwa [← pow_mul, ← pow_succ']
    obtain ⟨k, hk⟩ := exists_pow_eq_pow_two_mul ha hm 1
    rw [pow_one, pow_mul] at hk
    rw [hk]
    exact J'.pow_mem h2 k

private lemma br_mem_J_of_two_power {x : G} {X J' : Subgroup G} (hx : x ^ 3 = 1)
    (hXc : X ≤ Cen x) (hJc : J' ≤ Cen x) (hXodd : Odd (Nat.card X))
    (hXJ : ∀ u ∈ X, ∀ v ∈ J', u * v = v * u) {g : G}
    (hg : ∃ i : ℤ, ∃ u ∈ X, ∃ v ∈ J', g = x ^ i * u * v) {n : ℕ} (hn : g ^ (2 ^ n) = 1) :
    g ∈ J' := by
  obtain ⟨i, u, hu, v, hv, rfl⟩ := hg
  have hxu : Commute x u := (Subgroup.mem_centralizer_singleton_iff.mp (hXc hu)).symm
  have hxv : Commute x v := (Subgroup.mem_centralizer_singleton_iff.mp (hJc hv)).symm
  have huv : Commute u v := hXJ u hu v hv
  have hau : Commute (x ^ i) u := hxu.zpow_left i
  have hav : Commute (x ^ i * u) v := (hxv.zpow_left i).mul_left huv
  set m := 3 * Nat.card X with hm
  have hmodd : Odd m := (by decide : Odd 3).mul hXodd
  have hxm : (x ^ i) ^ m = 1 := by
    have : x ^ m = 1 := by rw [hm, pow_mul, hx, one_pow]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, this, one_zpow]
  have hum : u ^ m = 1 := by
    have : u ^ Nat.card X = 1 := by
      have := pow_card_eq_one' (x := (⟨u, hu⟩ : X))
      exact congrArg Subtype.val this
    rw [hm, mul_comm, pow_mul, this, one_pow]
  have ham : (x ^ i * u) ^ m = 1 := by rw [hau.mul_pow, hxm, hum, one_mul]
  have h1 : (x ^ i * u) ^ (2 ^ n) ∈ J' := by
    have h2 : (x ^ i * u) ^ (2 ^ n) * v ^ (2 ^ n) = 1 := by rw [← hav.mul_pow]; exact hn
    have : (x ^ i * u) ^ (2 ^ n) = (v ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [this]
    exact J'.inv_mem (J'.pow_mem hv _)
  exact J'.mul_mem (br_mem_of_two_pow_mem n _ m hmodd ham h1) hv

private theorem br_Opp_conj_mem {p : ℕ} {H : Subgroup G} {g z : G} (hg : g ∈ H)
    (hz : z ∈ Opp p H) : g * z * g⁻¹ ∈ Opp p H := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * z' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  exact (CFSG.pPrimeCore_normal (p := p) (G := H)).conj_mem z' hz' ⟨g, hg⟩

private theorem br_Opp_le (p : ℕ) (H : Subgroup G) : Opp p H ≤ H := Subgroup.map_subtype_le _

private theorem br_Lay_le (H : Subgroup G) : Lay H ≤ H := Subgroup.map_subtype_le _

private theorem br_mem_cen {x g : G} (h : x * g = g * x) : g ∈ Cen x :=
  Subgroup.mem_centralizer_singleton_iff.mpr h.symm

private theorem br_cen_comm {x g : G} (hg : g ∈ Cen x) : x * g = g * x :=
  (Subgroup.mem_centralizer_singleton_iff.mp hg).symm

private theorem br_mem_sup_of_comm {A H : Subgroup G} (hc : ∀ a ∈ A, ∀ h ∈ H, a * h = h * a)
    {g : G} (hg : g ∈ A ⊔ H) : ∃ a ∈ A, ∃ h ∈ H, g = a * h := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ h ∈ H, g = a * h}
      mul_mem' := by
        rintro _ _ ⟨a, ha, h, hh, rfl⟩ ⟨a', ha', h', hh', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', h * h', H.mul_mem hh hh', ?_⟩
        have := hc a' ha' h hh
        calc a * h * (a' * h') = a * (h * a') * h' := by simp only [mul_assoc]
          _ = a * (a' * h) * h' := by rw [this]
          _ = a * a' * (h * h') := by simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, H.one_mem, (one_mul 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, h, hh, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, h⁻¹, H.inv_mem hh, ?_⟩
        have : Commute a h := hc a ha h hh
        rw [mul_inv_rev]
        exact ((this.inv_inv).symm.eq)  }
  have hle : A ⊔ H ≤ S := by
    refine sup_le (fun a ha => ⟨a, ha, 1, H.one_mem, (mul_one a).symm⟩)
      (fun h hh => ⟨1, A.one_mem, h, hh, (one_mul h).symm⟩)
  exact hle hg

variable [Finite G]

private theorem br_facts {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) :
    b ^ 3 = 1 ∧ b₁ ^ 3 = 1 ∧ b₂ ^ 3 = 1 ∧ b * b₁ = b₁ * b ∧ b * b₂ = b₂ * b ∧
      b₁ * b₂ = b₂ * b₁ ∧ b₁ ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEl, -⟩ := h4.mono.1
  haveI := hEl
  have hBeq := h4.mono.2.1
  have hbB : b ∈ B := hBeq ▸ Subgroup.subset_closure (by simp)
  have hb₁B : b₁ ∈ B := (Subgroup.mem_inf.mp h4.hb₁).1
  have hb₂B : b₂ ∈ B := (Subgroup.mem_inf.mp h4.hb₂).1
  have hB3 : ∀ g ∈ B, g ^ 3 = 1 := fun g hg =>
    elemPow_eq_one_of_isElementaryAbelian (A := B) g hg
  have hcomm : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hEl.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  obtain ⟨-, -, -, -, -, ⟨c, -, hc1, hc2, hc3⟩⟩ := h4.mono
  obtain ⟨-, -, -, hK1, -, -⟩ := sec4_facts h4
  refine ⟨hB3 b hbB, hB3 b₁ hb₁B, hB3 b₂ hb₂B, hcomm _ hbB _ hb₁B, hcomm _ hbB _ hb₂B,
    hcomm _ hb₁B _ hb₂B, ?_⟩
  intro h
  apply hK1
  rw [← hc2, h]
  simp

private structure BaseDec (b : G) (J : Subgroup G) : Prop where
  hJc : J ≤ Cen b
  hXc : Opp 3 (Cen b) ≤ Cen b
  odd : Odd (Nat.card (Opp 3 (Cen b)))
  comm : ∀ u ∈ Opp 3 (Cen b), ∀ v ∈ J, u * v = v * u
  dec : ∀ g ∈ Cen b, ∃ i : ℤ, ∃ u ∈ Opp 3 (Cen b), ∃ v ∈ J, g = b ^ i * u * v
  Jnorm : ∀ c ∈ Cen b, ∀ j ∈ J, c * j * c⁻¹ ∈ J

private theorem br_Jnorm {b : G} {J : Subgroup G} (hstd : FFStandardJ b J) {b₁ : G}
    (hb₁J : b₁ ∈ J) (hb₁o : orderOf b₁ = 3) :
    ∀ c ∈ Cen b, ∀ j ∈ J, c * j * c⁻¹ ∈ J := by
  intro c hc j hj
  let φ : ↥(Cen b) ≃* ↥(Cen b) := MulAut.conj (⟨c, hc⟩ : ↥(Cen b))
  have hcomp : CFSG.IsComponent (J.subgroupOf (Cen b)) := hstd.2.1
  have hcomp' := CFSG.LocalCores.isComponent_map_mulEquiv φ hcomp
  have hb₁C : b₁ ∈ Cen b := hstd.1 hb₁J
  have hmem : (⟨b₁, hb₁C⟩ : ↥(Cen b)) ∈ J.subgroupOf (Cen b) := hb₁J
  have hdvd : 3 ∣ Nat.card (J.subgroupOf (Cen b)) := by
    have := Subgroup.orderOf_dvd_natCard (J.subgroupOf (Cen b)) hmem
    rwa [Subgroup.orderOf_mk, hb₁o] at this
  have hdvd' : 3 ∣ Nat.card ((J.subgroupOf (Cen b)).map φ.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective φ.injective]
  have heq := hstd.2.2 _ hcomp' hdvd'
  have hjC : j ∈ Cen b := hstd.1 hj
  have hjK : (⟨j, hjC⟩ : ↥(Cen b)) ∈ J.subgroupOf (Cen b) := hj
  have : φ ⟨j, hjC⟩ ∈ (J.subgroupOf (Cen b)).map φ.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨_, hjK, rfl⟩
  rw [heq] at this
  exact this

private theorem br_baseDec {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂)
    (h41 : Odd (Nat.card (Opp 3 (Cen b))))
    (h43 : setMul3 (Subgroup.zpowers b) (Opp 3 (Cen b)) J = Cen b ∧
      Nat.card (Cen b) = 3 * Nat.card (Opp 3 (Cen b)) * Nat.card J) : BaseDec b J := by
  obtain ⟨hset, hcard⟩ := h43
  have hJc : J ≤ Cen b := h4.hyp.std.1
  have hXc : Opp 3 (Cen b) ≤ Cen b := br_Opp_le 3 _
  obtain ⟨-, hb₁3, -, -, -, -, hb₁1⟩ := br_facts h4
  have hb₁o : orderOf b₁ = 3 := orderOf_eq_prime hb₁3 hb₁1
  have hJn := br_Jnorm h4.hyp.std h4.hb₁.2 hb₁o
  have hbo : orderOf b = 3 := h4.hyp.ord
  have hbc : Subgroup.zpowers b ≤ Cen b := by
    rw [Subgroup.zpowers_le]; exact br_mem_cen rfl
  have hdec : ∀ g ∈ Cen b, ∃ i : ℤ, ∃ u ∈ Opp 3 (Cen b), ∃ v ∈ J, g = b ^ i * u * v := by
    intro g hg
    have : g ∈ setMul3 (Subgroup.zpowers b) (Opp 3 (Cen b)) J := by rw [hset]; exact hg
    obtain ⟨h, hh, u, hu, v, hv, rfl⟩ := this
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ⟨i, u, hu, v, hv, rfl⟩
  let f : ↥(Subgroup.zpowers b) × ↥(Opp 3 (Cen b)) × ↥J → ↥(Cen b) := fun p =>
    ⟨(p.1 : G) * p.2.1 * p.2.2, (Cen b).mul_mem ((Cen b).mul_mem (hbc p.1.2) (hXc p.2.1.2))
      (hJc p.2.2.2)⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨i, u, hu, v, hv, rfl⟩ := hdec g hg
    exact ⟨(⟨b ^ i, Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i⟩, ⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  have hcd : Nat.card (↥(Subgroup.zpowers b) × ↥(Opp 3 (Cen b)) × ↥J) ≤ Nat.card ↥(Cen b) := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_zpowers, hbo, hcard, mul_assoc]
  have hbij := hsurj.bijective_of_nat_card_le hcd
  have hinter : ∀ z ∈ Opp 3 (Cen b), z ∈ J → z = 1 := by
    intro z hzX hzJ
    have := hbij.1 (a₁ := ((1 : ↥(Subgroup.zpowers b)), (⟨z, hzX⟩ : ↥(Opp 3 (Cen b))),
      (1 : ↥J))) (a₂ := ((1 : ↥(Subgroup.zpowers b)), (1 : ↥(Opp 3 (Cen b))), (⟨z, hzJ⟩ : ↥J)))
      (Subtype.ext (by simp [f]))
    have h2 := congrArg (fun p => ((p.2.1 : ↥(Opp 3 (Cen b))) : G)) this
    simpa using h2
  have hcomm : ∀ u ∈ Opp 3 (Cen b), ∀ v ∈ J, u * v = v * u := by
    intro u hu v hv
    have h1 : u * v * u⁻¹ ∈ J := hJn u (hXc hu) v hv |> fun h => by simpa using h
    have h2 : v * u⁻¹ * v⁻¹ ∈ Opp 3 (Cen b) := by
      have := br_Opp_conj_mem (hJc hv) ((Opp 3 (Cen b)).inv_mem hu)
      exact this
    have h3 : u * v * u⁻¹ * v⁻¹ ∈ J := J.mul_mem h1 (J.inv_mem hv)
    have h4' : u * v * u⁻¹ * v⁻¹ ∈ Opp 3 (Cen b) := by
      have := (Opp 3 (Cen b)).mul_mem hu h2
      simpa [mul_assoc] using this
    have := hinter _ h4' h3
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  exact ⟨hJc, hXc, h41, hcomm, hdec, hJn⟩

private theorem br_le_J_of_simple {b : G} {J : Subgroup G} (hb3 : b ^ 3 = 1) (hd : BaseDec b J)
    {K : Subgroup G} (hK : K ≤ Cen b) [IsSimpleGroup K] (hev : Even (Nat.card K)) : K ≤ J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.mp hev)
  have h2J : ∀ g ∈ Cen b, g ^ 2 = 1 → g ∈ J := fun g hg h2 =>
    br_mem_J_of_two_power (X := Opp 3 (Cen b)) hb3 hd.hXc hd.hJc hd.odd hd.comm (hd.dec g hg)
      (n := 1) (by simpa using h2)
  have htJ : (t : G) ∈ J := by
    refine h2J t (hK t.2) ?_
    have : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
    simpa using congrArg Subtype.val this
  let N : Subgroup K := J.subgroupOf K
  haveI : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hd.Jnorm g (hK g.2) n hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    have h1 : t ∈ N := htJ
    rw [h, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at ht
    omega
  · intro k hk
    have : (⟨k, hk⟩ : K) ∈ N := by rw [h]; exact Subgroup.mem_top _
    exact this

private theorem br_cen_iff (φ : G ≃* G) (x y : G) : y ∈ Cen x ↔ φ y ∈ Cen (φ x) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← map_mul, ← map_mul]
  exact φ.injective.eq_iff.symm

private theorem br_map_cen (φ : G ≃* G) (x : G) :
    (Cen x).map φ.toMonoidHom = Cen (φ x) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  have := br_cen_iff φ x (φ.symm y)
  rw [MulEquiv.apply_symm_apply] at this
  exact this

private theorem br_transport_L5 (φ : G ≃* G) {x b z : G} (h : FF79CentL5 x b z) :
    FF79CentL5 (φ x) (φ b) (φ z) := by
  obtain ⟨X, J', hXc, hJc, hodd, ⟨e⟩, hXJ, hdec, hbJ, hzJ, h7⟩ := h.exists_decomp
  refine ⟨X.map φ.toMonoidHom, J'.map φ.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (br_cen_iff φ x u).mp (hXc hu)
  · rintro _ ⟨u, hu, rfl⟩
    exact (br_cen_iff φ x u).mp (hJc hu)
  · rwa [Subgroup.card_map_of_injective φ.injective]
  · exact ⟨(Subgroup.equivMapOfInjective J' φ.toMonoidHom φ.injective).symm.trans e⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hXJ u hu v hv]
  · intro g hg
    have hg' : φ.symm g ∈ Cen x := by
      have := (br_cen_iff φ x (φ.symm g)).mpr
      rw [MulEquiv.apply_symm_apply] at this
      exact this hg
    obtain ⟨i, u, hu, v, hv, hge⟩ := hdec _ hg'
    refine ⟨i, φ u, ⟨u, hu, rfl⟩, φ v, ⟨v, hv, rfl⟩, ?_⟩
    have := congrArg φ hge
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_zpow] at this
    exact this
  · exact ⟨b, hbJ, rfl⟩
  · exact ⟨z, hzJ, rfl⟩
  · have : (J'.map φ.toMonoidHom) ⊓ Cen (φ b) = (J' ⊓ Cen b).map φ.toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ φ.injective, br_map_cen]
    rw [this, Subgroup.card_map_of_injective φ.injective]
    exact h7

private theorem br_transport_A5L3 (φ : G ≃* G) {x b w : G} (h : FF79CentA5L3 x b w) :
    FF79CentA5L3 (φ x) (φ b) (φ w) := by
  obtain ⟨X, K, L, hXc, hKc, hLc, hodd, ⟨eK⟩, ⟨eL⟩, hXK, hXL, hKL, hdec, hwK, hbL⟩ :=
    h.exists_decomp
  refine ⟨X.map φ.toMonoidHom, K.map φ.toMonoidHom, L.map φ.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (br_cen_iff φ x u).mp (hXc hu)
  · rintro _ ⟨u, hu, rfl⟩
    exact (br_cen_iff φ x u).mp (hKc hu)
  · rintro _ ⟨u, hu, rfl⟩
    exact (br_cen_iff φ x u).mp (hLc hu)
  · rwa [Subgroup.card_map_of_injective φ.injective]
  · exact ⟨(Subgroup.equivMapOfInjective K φ.toMonoidHom φ.injective).symm.trans eK⟩
  · exact ⟨(Subgroup.equivMapOfInjective L φ.toMonoidHom φ.injective).symm.trans eL⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hXK u hu v hv]
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hXL u hu v hv]
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hKL u hu v hv]
  · intro g hg
    have hg' : φ.symm g ∈ Cen x := by
      have := (br_cen_iff φ x (φ.symm g)).mpr
      rw [MulEquiv.apply_symm_apply] at this
      exact this hg
    obtain ⟨i, u, hu, k, hk, l, hl, hge⟩ := hdec _ hg'
    refine ⟨i, φ u, ⟨u, hu, rfl⟩, φ k, ⟨k, hk, rfl⟩, φ l, ⟨l, hl, rfl⟩, ?_⟩
    have := congrArg φ hge
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_mul, map_zpow] at this
    exact this
  · exact ⟨w, hwK, rfl⟩
  · exact ⟨b, hbL, rfl⟩

private theorem br_comm_opp_lay (H : Subgroup G) (hodd : Odd (Nat.card (Opp 3 H))) :
    ∀ u ∈ Opp 3 H, ∀ z ∈ Lay H, u * z = z * u := by
  have hcard : Nat.card (pPrimeCore 3 ↥H) = Nat.card (Opp 3 H) :=
    (Subgroup.card_map_of_injective H.subtype_injective).symm
  have hsolv : Group.IsSolvable (pPrimeCore 3 ↥H) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (by rw [hcard]; exact hodd)
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hsolv
    (CFSG.pPrimeCore_normal (p := 3) (G := ↥H)).isSubnormal).2
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro u hu z hz
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hle hw) r hr)

private theorem br_burnside {b : G} {B : Subgroup G} (hB : IsSylowOf 3 B (Cen b)) (hbB : b ∈ B)
    (hBc : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u) :
    ∀ c ∈ CenS B, ∃ n ∈ Opp 3 (CenS B), ∃ p ∈ B, c = n * p := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hBp, hBi⟩ := hB
  have hBC : B ≤ CenS B := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr (fun v hv => hBc v hv u hu)
  have hCb : CenS B ≤ Cen b := Subgroup.centralizer_le (by simpa using hbB)
  have hP0p : IsPGroup 3 (B.subgroupOf (CenS B)) := hBp.comap_subtype
  have hdvd : B.relIndex (CenS B) ∣ B.relIndex (Cen b) :=
    ⟨(CenS B).relIndex (Cen b), (Subgroup.relIndex_mul_relIndex B (CenS B) (Cen b) hBC hCb).symm⟩
  have hidx : ¬ 3 ∣ (B.subgroupOf (CenS B)).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (Nat.Coprime.coprime_dvd_right hdvd hBi)
  let P : Sylow 3 ↥(CenS B) := hP0p.toSylow hidx
  have hPc : (P : Subgroup ↥(CenS B)) ≤ Subgroup.center ↥(CenS B) := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp q.2 p (Subgroup.mem_subgroupOf.mp hp)).symm
  have hcomp := CFSG.FullDefectCanonical.pPrimeCore_isComplement_of_central P hPc
  intro c hc
  obtain ⟨⟨⟨n, hn⟩, ⟨p, hp⟩⟩, hx, -⟩ := hcomp.existsUnique (⟨c, hc⟩ : ↥(CenS B))
  refine ⟨n, Subgroup.mem_map.mpr ⟨n, hn, rfl⟩, p, Subgroup.mem_subgroupOf.mp hp, ?_⟩
  exact (congrArg Subtype.val hx).symm

private theorem br_mono {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) :
    (∃ ψ : G ≃* G, ψ b = b⁻¹ ∧ ψ b₁ = b₁ ∧ ψ b₂ = b₂) ∧
    (∃ ψ : G ≃* G, ψ b = b₁ ∧ ψ b₁ = b ∧ ψ b₂ = b₂) ∧
    (∃ ψ : G ≃* G, ψ b = b₁ ∧ ψ b₁ = b₂ ∧ ψ b₂ = b) := by
  obtain ⟨-, -, -, ⟨n₀, -, h0⟩, ⟨n₁, -, h1⟩, ⟨n₂, -, h2⟩⟩ := h4.mono
  exact ⟨⟨MulAut.conj n₀, by simpa using h0⟩, ⟨MulAut.conj n₁, by simpa using h1⟩,
    ⟨MulAut.conj n₂, by simpa using h2⟩⟩

private theorem br_Bcomm {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) :
    ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
  congrArg Subtype.val (h4.mono.1.1.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)

private theorem br_gen {z b₁ b₂ : G} (h1 : z * (b₁ * b₂) = (b₁ * b₂) * z)
    (h2 : z * (b₁ ^ 2 * b₂) = (b₁ ^ 2 * b₂) * z) : z * b₁ = b₁ * z ∧ z * b₂ = b₂ * z := by
  have c1 : Commute z (b₁ * b₂) := h1
  have c2 : Commute z (b₁ ^ 2 * b₂) := h2
  have e1 : b₁ = (b₁ ^ 2 * b₂) * (b₁ * b₂)⁻¹ := by group
  have d1 : Commute z b₁ := by rw [e1]; exact c2.mul_right c1.inv_right
  refine ⟨d1.eq, ?_⟩
  have e2 : b₂ = b₁⁻¹ * (b₁ * b₂) := by group
  have d2 : Commute z b₂ := by rw [e2]; exact d1.inv_right.mul_right c1
  exact d2.eq

private theorem br_swap {a q : G} (h : a * q = q * a) (y : G) : a * (q * y) = q * (a * y) := by
  rw [← mul_assoc, h, mul_assoc]

private theorem br_centβ {b b₁ b₂ : G} {J B : Subgroup G} (h4 : FF79Sec4 b J B b₁ b₂)
    (hd : BaseDec b J) {H K L : Subgroup G} (hHle : H ≤ Cen (b₁ * b₂))
    (hsup : Subgroup.zpowers (b₁ * b₂) ⊔ H = Cen (b₁ * b₂)) (hKH : K ≤ H) (hLH : L ≤ H)
    (hK : IsLnq 2 2 2 K) (hL : IsLnq 3 2 1 L) (hbL : b ∈ L) (hγK : b₁ ^ 2 * b₂ ∈ K)
    (hLay : Lay H = K ⊔ L) (hKL : K ≤ CenS L)
    (hdecH : setMul (H ⊓ CenS (Subgroup.closure ({b, b₁ ^ 2 * b₂} : Set G))) (Lay H) = H)
    (hOpp : Opp 3 H = Opp 3 (Cen b)) (hOpp' : Opp 3 (CenS B) = Opp 3 H) :
    FF79CentA5L3 (b₁ * b₂) b (b₁ ^ 2 * b₂) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eK⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Liebeck155.nonempty_mulEquiv_alt5_of_statedClassicalModel hK
  obtain ⟨eL⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two hL
  set β := b₁ * b₂ with hβ
  set γ := b₁ ^ 2 * b₂ with hγ
  have hBeq := h4.mono.2.1
  have hBc := br_Bcomm h4
  have hbB : b ∈ B := hBeq ▸ Subgroup.subset_closure (by simp)
  have hb₁B : b₁ ∈ B := (Subgroup.mem_inf.mp h4.hb₁).1
  have hb₂B : b₂ ∈ B := (Subgroup.mem_inf.mp h4.hb₂).1
  have hβB : β ∈ B := B.mul_mem hb₁B hb₂B
  have hγB : γ ∈ B := B.mul_mem (B.pow_mem hb₁B 2) hb₂B
  have hXodd : Odd (Nat.card (Opp 3 H)) := by rw [hOpp]; exact hd.odd
  have hcommX := br_comm_opp_lay H hXodd
  have hKlay : K ≤ Lay H := hLay ▸ le_sup_left
  have hLlay : L ≤ Lay H := hLay ▸ le_sup_right
  have hXH : Opp 3 H ≤ H := br_Opp_le 3 H
  have hβc : ∀ y ∈ H, β * y = y * β := fun y hy => br_cen_comm (hHle hy)
  refine ⟨⟨Opp 3 H, K, L, hXH.trans hHle, (hKH.trans hHle), (hLH.trans hHle), hXodd,
    ⟨eK⟩, ⟨eL⟩, ?_, ?_, ?_, ?_, hγK, hbL⟩⟩
  · intro u hu v hv; exact hcommX u hu v (hKlay hv)
  · intro u hu v hv; exact hcommX u hu v (hLlay hv)
  · intro u hu v hv; exact (Subgroup.mem_centralizer_iff.mp (hKL hu) v hv).symm
  · intro g hg
    rw [← hsup] at hg
    obtain ⟨a, ha, h, hh, rfl⟩ := br_mem_sup_of_comm (A := Subgroup.zpowers β) (H := H)
      (fun a ha h hh => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact ((show Commute β h from hβc h hh).zpow_left i).eq) hg
    obtain ⟨i₀, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hh' : h ∈ setMul (H ⊓ CenS (Subgroup.closure ({b, γ} : Set G))) (Lay H) := by
      rw [hdecH]; exact hh
    obtain ⟨c, hc, e, he, rfl⟩ := hh'
    rw [hLay] at he
    obtain ⟨k, hk, l, hl, rfl⟩ := br_mem_sup_of_comm
      (fun u hu v hv => (Subgroup.mem_centralizer_iff.mp (hKL hu) v hv).symm) he
    obtain ⟨hcH, hcC⟩ := Subgroup.mem_inf.mp hc
    have hcb : c * b = b * c :=
      (Subgroup.mem_centralizer_iff.mp hcC b (Subgroup.subset_closure (by simp))).symm
    have hcγ : c * γ = γ * c :=
      (Subgroup.mem_centralizer_iff.mp hcC γ (Subgroup.subset_closure (by simp))).symm
    have hcβ : c * β = β * c := (hβc c hcH).symm
    obtain ⟨hcb₁, hcb₂⟩ := br_gen hcβ hcγ
    have hcB : c ∈ CenS B := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have : B ≤ Cen c := by
        rw [hBeq, Subgroup.closure_le]
        rintro y (rfl | rfl | rfl)
        · exact br_mem_cen hcb
        · exact br_mem_cen hcb₁
        · exact br_mem_cen hcb₂
      exact (br_cen_comm (this hx)).symm
    obtain ⟨n, hn, p, hp, rfl⟩ := br_burnside h4.sylB hbB hBc c hcB
    rw [hOpp'] at hn
    have hb₁S : b₁ ∈ Subgroup.zpowers β ⊔ Subgroup.zpowers γ := by
      have e1 : b₁ = γ * β⁻¹ := by rw [hγ, hβ]; group
      rw [e1]
      exact (Subgroup.zpowers β ⊔ Subgroup.zpowers γ).mul_mem
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        ((Subgroup.zpowers β ⊔ Subgroup.zpowers γ).inv_mem
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
    have hb₂S : b₂ ∈ Subgroup.zpowers β ⊔ Subgroup.zpowers γ := by
      have e2 : b₂ = b₁⁻¹ * β := by rw [hβ]; group
      rw [e2]
      exact (Subgroup.zpowers β ⊔ Subgroup.zpowers γ).mul_mem
        ((Subgroup.zpowers β ⊔ Subgroup.zpowers γ).inv_mem hb₁S)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    have hBS : B ≤ (Subgroup.zpowers b ⊔ Subgroup.zpowers β) ⊔ Subgroup.zpowers γ := by
      rw [hBeq, Subgroup.closure_le]
      have h1 : Subgroup.zpowers β ⊔ Subgroup.zpowers γ ≤
          (Subgroup.zpowers b ⊔ Subgroup.zpowers β) ⊔ Subgroup.zpowers γ :=
        sup_le (le_sup_right.trans le_sup_left) le_sup_right
      rintro y (rfl | rfl | rfl)
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      · exact h1 hb₁S
      · exact h1 hb₂S
    have hzb : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hbB
    have hzβ : Subgroup.zpowers β ≤ B := Subgroup.zpowers_le.mpr hβB
    have hzγ : Subgroup.zpowers γ ≤ B := Subgroup.zpowers_le.mpr hγB
    obtain ⟨a', ha', z, hz, rfl⟩ := br_mem_sup_of_comm
      (fun a ha h hh => hBc a ((sup_le hzb hzβ) ha) h (hzγ hh)) (hBS hp)
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := br_mem_sup_of_comm
      (fun a ha h hh => hBc a (hzb ha) h (hzβ hh)) ha'
    obtain ⟨i₁, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₁
    obtain ⟨i₂, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₂
    obtain ⟨i₃, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨i₀ + i₂, n, hn, γ ^ i₃ * k, K.mul_mem (K.zpow_mem hγK _) hk,
      b ^ i₁ * l, L.mul_mem (L.zpow_mem hbL _) hl, ?_⟩
    have hnH : n ∈ H := hXH hn
    have hAH : b ^ i₁ ∈ H := hLH (L.zpow_mem hbL _)
    have hQN : n * β ^ i₂ = β ^ i₂ * n := ((show Commute β n from hβc n hnH).zpow_left i₂).symm.eq
    have hQA : b ^ i₁ * β ^ i₂ = β ^ i₂ * b ^ i₁ :=
      ((show Commute β (b ^ i₁) from hβc _ hAH).zpow_left i₂).symm.eq
    have hAΓ : b ^ i₁ * γ ^ i₃ = γ ^ i₃ * b ^ i₁ :=
      Subgroup.mem_centralizer_iff.mp (hKL (K.zpow_mem hγK i₃)) _ (L.zpow_mem hbL i₁)
    have hAk : b ^ i₁ * k = k * b ^ i₁ :=
      Subgroup.mem_centralizer_iff.mp (hKL hk) _ (L.zpow_mem hbL i₁)
    rw [zpow_add]
    simp only [mul_assoc]
    rw [br_swap hQA, br_swap hQN, br_swap hAΓ, br_swap hAk]

private theorem br_baseL5 {b b₁ b₂ : G} {J B : Subgroup G} (h4 : FF79Sec4 b J B b₁ b₂)
    (hd : BaseDec b J) (hJ5 : IsLnq 5 2 1 J) {H L : Subgroup G} (hLH : L ≤ H)
    (hHle : H ≤ Cen (b₁ * b₂)) (hLγ : L ≤ Cen (b₁ ^ 2 * b₂)) (hL : IsLnq 3 2 1 L) :
    FF79CentL5 b b₁ b₂ := by
  obtain ⟨hb3, -, -, -, -, -, -⟩ := br_facts h4
  obtain ⟨eJ⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two hJ5
  obtain ⟨eL⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two hL
  obtain ⟨-, ⟨ψ₁, h1b, h1b₁, h1b₂⟩, ⟨ψ₂, h2b, h2b₁, h2b₂⟩⟩ := br_mono h4
  let φ : G ≃* G := (ψ₂.trans ψ₁).trans ψ₂.symm
  have hs₁ : ψ₂.symm b = b₂ := (MulEquiv.symm_apply_eq _).mpr h2b₂.symm
  have hs₂ : ψ₂.symm b₂ = b₁ := (MulEquiv.symm_apply_eq _).mpr h2b₁.symm
  have hs₃ : ψ₂.symm b₁ = b := (MulEquiv.symm_apply_eq _).mpr h2b.symm
  have hφb : φ b = b₂ := by
    show ψ₂.symm (ψ₁ (ψ₂ b)) = b₂
    rw [h2b, h1b₁]; exact hs₁
  have hφb₁ : φ b₁ = b₁ := by
    show ψ₂.symm (ψ₁ (ψ₂ b₁)) = b₁
    rw [h2b₁, h1b₂]; exact hs₂
  have hφb₂ : φ b₂ = b := by
    show ψ₂.symm (ψ₁ (ψ₂ b₂)) = b
    rw [h2b₂, h1b]; exact hs₃
  have hLc : ∀ z ∈ L, z * (b₁ * b₂) = (b₁ * b₂) * z ∧ z * (b₁ ^ 2 * b₂) = (b₁ ^ 2 * b₂) * z :=
    fun z hz => ⟨(br_cen_comm (hHle (hLH hz))).symm, (br_cen_comm (hLγ hz)).symm⟩
  have hL₁ : L ≤ Cen b₁ := fun z hz => br_mem_cen (br_gen (hLc z hz).1 (hLc z hz).2).1.symm
  have hL₂ : L ≤ Cen b₂ := fun z hz => br_mem_cen (br_gen (hLc z hz).1 (hLc z hz).2).2.symm
  have hL'b : L.map φ.toMonoidHom ≤ Cen b := by
    have := br_map_cen φ b₂
    rw [hφb₂] at this
    rw [← this]; exact Subgroup.map_mono hL₂
  have hL'b₁ : L.map φ.toMonoidHom ≤ Cen b₁ := by
    have := br_map_cen φ b₁
    rw [hφb₁] at this
    rw [← this]; exact Subgroup.map_mono hL₁
  let eL' : ↥(L.map φ.toMonoidHom) ≃* GL (Fin 3) (ZMod 2) :=
    (Subgroup.equivMapOfInjective L φ.toMonoidHom φ.injective).symm.trans eL
  haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  haveI : IsSimpleGroup ↥(L.map φ.toMonoidHom) := eL'.isSimpleGroup
  have hcard : Nat.card ↥(L.map φ.toMonoidHom) = 168 :=
    (Nat.card_congr eL'.toEquiv).trans CFSG.ComponentClassification.GHarris.card_GL32_gh
  have hev : Even (Nat.card ↥(L.map φ.toMonoidHom)) := by rw [hcard]; decide
  have hL'J := br_le_J_of_simple hb3 hd hL'b hev
  have hdvd := Subgroup.card_dvd_of_le (le_inf hL'J hL'b₁)
  rw [hcard] at hdvd
  exact ⟨⟨Opp 3 (Cen b), J, hd.hXc, hd.hJc, hd.odd, ⟨eJ⟩, hd.comm, hd.dec, h4.hb₁.2, h4.hb₂.2,
    dvd_trans (by norm_num) hdvd⟩⟩

theorem ff79_KleJ_of (h41 : FF79_4_1) (h43 : FF79_4_3) : FF79_KleJ := by
  intro G _ _ b J B b₁ b₂ h4 K hK ⟨eK⟩
  haveI : IsSimpleGroup K := eK.isSimpleGroup
  have hd := br_baseDec h4 (h41 G b J B b₁ b₂ h4) (h43 G b J B b₁ b₂ h4).2
  have hev : Even (Nat.card K) := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  exact br_le_J_of_simple (br_facts h4).1 hd hK hev

theorem ff79_4_3Str_of (h41 : FF79_4_1) (h42 : FF79_4_2) (h43 : FF79_4_3) (hJ5 : FF79_JL5) :
    FF79_4_3Str := by
  intro G _ _ b J B b₁ b₂ h4
  have hd := br_baseDec h4 (h41 G b J B b₁ b₂ h4) (h43 G b J B b₁ b₂ h4).2
  have hJ5' := hJ5 G b J h4.hyp
  have h := h42 G b J B b₁ b₂ h4
  dsimp only at h
  obtain ⟨⟨hsup, -⟩, -, hK, hL, hbL, hγK, hLay, -, hKL, hdecH, hOpp', hOpp⟩ := h
  obtain ⟨-, hb₁3, -, -, -, -, -⟩ := br_facts h4
  have hHle : OUp 3 (Cen (b₁ * b₂)) ≤ Cen (b₁ * b₂) := Subgroup.map_subtype_le _
  have hKH : Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen b) ≤ OUp 3 (Cen (b₁ * b₂)) :=
    (br_Lay_le _).trans inf_le_left
  have hLH : Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ ^ 2 * b₂)) ≤ OUp 3 (Cen (b₁ * b₂)) :=
    (br_Lay_le _).trans inf_le_left
  have hLγ : Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ ^ 2 * b₂)) ≤ Cen (b₁ ^ 2 * b₂) :=
    (br_Lay_le _).trans inf_le_right
  have hbase := br_baseL5 h4 hd hJ5' hLH hHle hLγ hL
  have hβ := br_centβ h4 hd hHle hsup hKH hLH hK hL hbL hγK hLay hKL hdecH hOpp hOpp'
  obtain ⟨⟨ψ₀, h0b, h0b₁, h0b₂⟩, ⟨ψ₁, h1b, h1b₁, h1b₂⟩, ⟨ψ₂, h2b, h2b₁, h2b₂⟩⟩ := br_mono h4
  have cent₁ : FF79CentL5 b₁ b b₂ := by
    have := br_transport_L5 ψ₁ hbase
    rwa [h1b, h1b₁, h1b₂] at this
  have cent₂ : FF79CentL5 b₂ b b₁ := by
    have := br_transport_L5 (ψ₂.trans ψ₂) hbase
    have e1 : (ψ₂.trans ψ₂) b = b₂ := by
      show ψ₂ (ψ₂ b) = b₂; rw [h2b, h2b₁]
    have e2 : (ψ₂.trans ψ₂) b₁ = b := by
      show ψ₂ (ψ₂ b₁) = b; rw [h2b₁, h2b₂]
    have e3 : (ψ₂.trans ψ₂) b₂ = b₁ := by
      show ψ₂ (ψ₂ b₂) = b₁; rw [h2b₂, h2b]
    rwa [e1, e2, e3] at this
  have centγ : FF79CentA5L3 (b₁ ^ 2 * b₂) b (b₁ * b₂) := by
    let φ : G ≃* G := (ψ₁.symm.trans ψ₀).trans ψ₁
    have hs₁ : ψ₁.symm b = b₁ := (MulEquiv.symm_apply_eq _).mpr h1b₁.symm
    have hs₂ : ψ₁.symm b₁ = b := (MulEquiv.symm_apply_eq _).mpr h1b.symm
    have hs₃ : ψ₁.symm b₂ = b₂ := (MulEquiv.symm_apply_eq _).mpr h1b₂.symm
    have e0 : φ b = b := by
      show ψ₁ (ψ₀ (ψ₁.symm b)) = b
      rw [hs₁, h0b₁, h1b₁]
    have e1 : φ b₁ = b₁⁻¹ := by
      show ψ₁ (ψ₀ (ψ₁.symm b₁)) = b₁⁻¹
      rw [hs₂, h0b, map_inv, h1b]
    have e2 : φ b₂ = b₂ := by
      show ψ₁ (ψ₀ (ψ₁.symm b₂)) = b₂
      rw [hs₃, h0b₂, h1b₂]
    have hsq : b₁ ^ 2 = b₁⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hb₁3)
    have hsq' : (b₁⁻¹) ^ 2 = b₁ := by
      rw [← hsq, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hb₁3, one_mul, pow_one]
    have eβ : φ (b₁ * b₂) = b₁ ^ 2 * b₂ := by rw [map_mul, e1, e2, hsq]
    have eγ : φ (b₁ ^ 2 * b₂) = b₁ * b₂ := by rw [map_mul, map_pow, e1, e2, hsq']
    have := br_transport_A5L3 φ hβ
    rwa [eβ, e0, eγ] at this
  obtain ⟨eJ⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two hJ5'
  exact ⟨⟨eJ⟩, cent₁, cent₂, hβ, centγ⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
