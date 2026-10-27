module

public import CFSG.Quasithin.EmptyFaithful.SBc17In
public import CFSG.Quasithin.EmptyFaithful.SBc16GQuot
public import CFSG.Quasithin.EmptyFaithful.S146P12
public import CFSG.Quasithin.EmptyFaithful.SBc13JM5Quasi
public import CFSG.Quasithin.Vol2.Ch1Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem mem_of_odd_of_mem_sup {N P : Subgroup G} (hP : IsPGroup 2 P)
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) {g : G} (hg : g ∈ N ⊔ P)
    (hodd : Odd (orderOf g)) : g ∈ N := by
  have hup : oTwoUpper (N ⊔ P) ≤ N :=
    Der6A.oTwoUpper_le_of_normal_sup le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hPN)) hP le_sup_right le_rfl
  exact hup (mem_oTwoUpper_of_odd hg hodd)

omit [Finite G] in
theorem normalizer_le_normalizer_innerSub (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (innerSub J : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (J : Set G), ∀ k ∈ innerSub J, g * k * g⁻¹ ∈ innerSub J := by
    intro g hg k hk
    obtain ⟨j, hj, c, hc, rfl⟩ := mem_innerSub_iff.mp hk
    have e : g * (j * c) * g⁻¹ = (g * j * g⁻¹) * (g * c * g⁻¹) := by group
    rw [e]
    exact mul_mem (mem_innerSub_of_mem_J ((Subgroup.mem_normalizer_iff.mp hg j).mp hj))
      (mem_innerSub_of_mem_cMod ((Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_cMod J hg) c).mp hc))
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => key g hg k hk, fun hk => ?_⟩
  have h := key g⁻¹ (inv_mem hg) _ hk
  simpa [mul_assoc] using h

theorem exists_mul_of_sup_eq_top_of_comm {V : Type*} [Group V] (hc : ∀ a b : V, a * b = b * a)
    {A B : Subgroup V} (hsup : A ⊔ B = ⊤) (v : V) : ∃ a ∈ A, ∃ b ∈ B, a * b = v := by
  let : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hv : v ∈ A ⊔ B := by
    rw [hsup]
    exact Subgroup.mem_top v
  exact Subgroup.mem_sup.mp hv

theorem le_of_mem_of_card_eq_prime {V : Type*} [Group V] [Finite V] {A D : Subgroup V} {q : ℕ}
    (hq : q.Prime) (hA : Nat.card A = q) {a : V} (haA : a ∈ A) (haD : a ∈ D) (ha1 : a ≠ 1) :
    A ≤ D := by
  have hle : A ⊓ D ≤ A := inf_le_left
  have hne : A ⊓ D ≠ ⊥ := by
    intro hbot
    have : a ∈ A ⊓ D := ⟨haA, haD⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact ha1 this
  have hcard : Nat.card ↥(A ⊓ D) ∣ q := by
    rw [← hA]
    exact Subgroup.card_dvd_of_le hle
  have hq' : Nat.card ↥(A ⊓ D) = q := by
    rcases (Nat.dvd_prime hq).mp hcard with h1 | h5
    · exact absurd (Subgroup.card_eq_one.mp h1) hne
    · exact h5
  have heq : A ⊓ D = A := Subgroup.eq_of_le_of_card_ge hle (by rw [hq', hA])
  exact heq ▸ inf_le_right

omit [Finite G] in
theorem inv_mul_mem_pCoreOf_of_mk_eq {K : Subgroup G} {x y : ↥K}
    (h : (QuotientGroup.mk x : OTwoQuot K) = QuotientGroup.mk y) :
    (x : G)⁻¹ * (y : G) ∈ pCoreOf 2 K := by
  refine (mk_eq_one_iff_mem_pCoreOf (x⁻¹ * y)).mp ?_
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, inv_mul_cancel]

theorem card_imageOTwoQuot_K_five {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t) :
    Nat.card ↥(imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁)) = 5 := by
  have := SBc16.card_imageOTwoQuot_K hred hdec
  rwa [hp5] at this

theorem pow_five_eq_one_of_odd (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t) {y : G}
    (hy : y ∈ oTwoUpper H) (hodd : Odd (orderOf y)) : y ^ 5 = 1 := by
  have hcomm := SBc16.mul_comm_OTwoQuot_K S hp5 hred hdec
  have hsup := SBc16.imageOTwoQuot_sup_eq_top S hred hdec
  have hV₁card := card_imageOTwoQuot_K_five hp5 hred hdec
  have hV₂card := card_imageOTwoQuot_K_five hp5 hred hdec.swap
  have hexp : ∀ v : OTwoQuot (oTwoUpper H), v ^ 5 = 1 := by
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_sup_eq_top_of_comm hcomm hsup v
    have ha5 : a ^ 5 = 1 := by
      have := pow_card_eq_one' (G := imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁)) (x := ⟨a, ha⟩)
      rw [hV₁card] at this
      exact congrArg Subtype.val this
    have hb5 : b ^ 5 = 1 := by
      have := pow_card_eq_one' (G := imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂)) (x := ⟨b, hb⟩)
      rw [hV₂card] at this
      exact congrArg Subtype.val this
    rw [(show Commute a b from hcomm a b).mul_pow, ha5, hb5, one_mul]
  have hy5 : y ^ 5 ∈ pCoreOf 2 (oTwoUpper H) := by
    refine (mk_eq_one_iff_mem_pCoreOf (⟨y, hy⟩ ^ 5 : ↥(oTwoUpper H))).mp ?_
    rw [QuotientGroup.mk_pow]
    exact hexp _
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (oTwoUpper H) ⟨y ^ 5, hy5⟩
  have hk' : (y ^ 5) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hd : orderOf (y ^ 5) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hd' : orderOf (y ^ 5) ∣ orderOf y := orderOf_pow_dvd 5
  have hcop : Nat.Coprime (2 ^ k) (orderOf y) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd hd')

theorem inf_innerSub_le_sup (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t) {J : Subgroup G}
    (hK₂ : oTwoUpper H₂ ≤ innerSub J) (hKJ : oTwoUpper H ≤ Subgroup.normalizer (J : Set G))
    (hout : ¬ oTwoUpper H₁ ⊔ oTwoUpper H₂ ≤ innerSub J) :
    oTwoUpper H ⊓ innerSub J ≤ oTwoUpper H₂ ⊔ pCoreOf 2 (oTwoUpper H) := by
  have hKX : oTwoUpper H = oTwoUpper H₁ ⊔ oTwoUpper H₂ := hdec.oTwoUpper_eq S hred
  have hK₁K : oTwoUpper H₁ ≤ oTwoUpper H := hKX ▸ le_sup_left
  set K := oTwoUpper H with hK
  set O := pCoreOf 2 K with hO
  have hON : O ≤ Subgroup.normalizer (innerSub J : Set G) := fun o ho =>
    normalizer_le_normalizer_innerSub J (hKJ (pCoreOf_le 2 K ho))
  have hcomm := SBc16.mul_comm_OTwoQuot_K S hp5 hred hdec
  have hsup := SBc16.imageOTwoQuot_sup_eq_top S hred hdec
  have hV₁card := card_imageOTwoQuot_K_five hp5 hred hdec
  set D := imageOTwoQuot K (innerSub J) with hD
  have hV₂D : imageOTwoQuot K (oTwoUpper H₂) ≤ D := by
    intro v hv
    obtain ⟨x, hxK, hx, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
    exact mem_imageOTwoQuot_iff.mpr ⟨x, hxK, hK₂ hx, rfl⟩
  have hV₁D : ¬ imageOTwoQuot K (oTwoUpper H₁) ≤ D := by
    intro hle
    refine hout (sup_le ?_ hK₂)
    have hgen : oTwoUpper H₁ ≤ Subgroup.closure {x | x ∈ oTwoUpper H₁ ∧ orderOf x = 5} :=
      hdec.oTwoUpper_le_closure_five hp5 le_rfl
    refine hgen.trans ((Subgroup.closure_le _).mpr fun x hx => ?_)
    obtain ⟨hxK₁, hx5⟩ := hx
    have hxK : x ∈ K := hK₁K hxK₁
    have hxV : (QuotientGroup.mk ⟨x, hxK⟩ : OTwoQuot K) ∈ imageOTwoQuot K (oTwoUpper H₁) :=
      mem_imageOTwoQuot_iff.mpr ⟨x, hxK, hxK₁, rfl⟩
    obtain ⟨w, hwK, hw, hwx⟩ := mem_imageOTwoQuot_iff.mp (hle hxV)
    have h2 : w⁻¹ * x ∈ O := inv_mul_mem_pCoreOf_of_mk_eq hwx
    have hmem : w * (w⁻¹ * x) ∈ innerSub J ⊔ O :=
      mul_mem (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right h2)
    rw [mul_inv_cancel_left] at hmem
    exact mem_of_odd_of_mem_sup (pCoreOf_isPGroup 2 K) hON hmem
      (by rw [hx5]; exact ⟨2, by norm_num⟩)
  intro y hy
  obtain ⟨hyK, hyJ⟩ := hy
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_sup_eq_top_of_comm hcomm hsup
    (QuotientGroup.mk ⟨y, hyK⟩ : OTwoQuot K)
  have hyD : (QuotientGroup.mk ⟨y, hyK⟩ : OTwoQuot K) ∈ D :=
    mem_imageOTwoQuot_iff.mpr ⟨y, hyK, hyJ, rfl⟩
  have haD : a ∈ D := by
    have e : a = (QuotientGroup.mk ⟨y, hyK⟩ : OTwoQuot K) * b⁻¹ := by
      rw [← hab, mul_inv_cancel_right]
    rw [e]
    exact D.mul_mem hyD (D.inv_mem (hV₂D hb))
  have ha1 : a = 1 := by
    by_contra ha1
    exact hV₁D (le_of_mem_of_card_eq_prime (by norm_num) hV₁card ha haD ha1)
  rw [ha1, one_mul] at hab
  rw [hab] at hb
  obtain ⟨x, hxK, hxK₂, hxy⟩ := mem_imageOTwoQuot_iff.mp hb
  have h2 : x⁻¹ * y ∈ O := inv_mul_mem_pCoreOf_of_mk_eq hxy
  have hmem : x * (x⁻¹ * y) ∈ oTwoUpper H₂ ⊔ O :=
    mul_mem (Subgroup.mem_sup_left hxK₂) (Subgroup.mem_sup_right h2)
  rwa [mul_inv_cancel_left] at hmem

theorem not_orderOf_five_of_mem_inf (h36 : A36ForSQTK) (S : Setting146 G T M) {PQ : Subgroup G}
    (hp5 : p = 5) (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    {J : Subgroup G} (hX : SQTKGroup ↥(g2_14615 (oTwoUpper H₂)))
    (hJc : J ∈ cComp (g2_14615 (oTwoUpper H₂)))
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hK₂N : oTwoUpper H₂ ≤ Subgroup.normalizer (J : Set G))
    (hK₂c : ⁅J, oTwoUpper H₂⁆ ≤ pCoreOf 2 J) (hKJ : oTwoUpper H ≤ Subgroup.normalizer (J : Set G))
    (hout : ¬ oTwoUpper H₁ ⊔ oTwoUpper H₂ ≤ innerSub J) {y : G} (hy : y ∈ oTwoUpper H ⊓ J) :
    orderOf y ≠ 5 := by
  intro hy5
  have hK₂c' : oTwoUpper H₂ ≤ cMod J := fun k hk =>
    mem_cMod.mpr ⟨hK₂N hk, fun x hx => hK₂c (Subgroup.commutator_mem_commutator hx hk)⟩
  have hyin : y ∈ oTwoUpper H₂ ⊔ pCoreOf 2 (oTwoUpper H) :=
    inf_innerSub_le_sup S hp5 hred hdec (hK₂c'.trans le_sup_right) hKJ hout
      ⟨hy.1, mem_innerSub_of_mem_J hy.2⟩
  have hON : pCoreOf 2 (oTwoUpper H) ≤ Subgroup.normalizer (cMod J : Set G) := fun o ho =>
    normalizer_le_normalizer_cMod J (hKJ (pCoreOf_le 2 _ ho))
  have hycM : y ∈ cMod J :=
    mem_of_odd_of_mem_sup (pCoreOf_isPGroup 2 (oTwoUpper H)) hON (sup_le_sup_right hK₂c' _ hyin)
      (by rw [hy5]; exact ⟨2, by norm_num⟩)
  exact SBc13.not_mem_of_commutes hX (h36 _ (SQTKHyp.of_sqtkGroup _ hX)) hJc hJq hy5
    (fun x hx => (mem_cMod.mp hycM).2 x hx) hy.2

set_option linter.unusedVariables false in
theorem isPGroup_oTwoUpper_inf_of_not_innerSub (h36 : A36ForSQTK) (S : Setting146 G T M)
    {PQ : Subgroup G} (hp5 : p = 5) (hred : IsRedCE T M H PQ p)
    (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H) {J : Subgroup G}
    (hX : SQTKGroup ↥(g2_14615 (oTwoUpper H₂))) (hJc : J ∈ cComp (g2_14615 (oTwoUpper H₂)))
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hK₂N : oTwoUpper H₂ ≤ Subgroup.normalizer (J : Set G))
    (hK₂c : ⁅J, oTwoUpper H₂⁆ ≤ pCoreOf 2 J) (hKJ : oTwoUpper H ≤ Subgroup.normalizer (J : Set G))
    (hout : ¬ oTwoUpper H₁ ⊔ oTwoUpper H₂ ≤ innerSub J) :
    IsPGroup 2 ↥(oTwoUpper H ⊓ J) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro x
  have hx : (x : G) ∈ oTwoUpper H ⊓ J := x.2
  obtain ⟨a, m, hm, hxe⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : G)).ne'
  have hx'mem : (x : G) ^ 2 ^ a ∈ oTwoUpper H ⊓ J := pow_mem hx _
  have hx'm : ((x : G) ^ 2 ^ a) ^ m = 1 := by
    rw [← pow_mul, ← hxe]
    exact pow_orderOf_eq_one _
  have hodd : Odd (orderOf ((x : G) ^ 2 ^ a)) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hx'm)
  have h5 : ((x : G) ^ 2 ^ a) ^ 5 = 1 := pow_five_eq_one_of_odd S hp5 hred hdec hx'mem.1 hodd
  have h1 : (x : G) ^ 2 ^ a = 1 := by
    by_contra hne
    exact not_orderOf_five_of_mem_inf h36 S hp5 hred hdec hX hJc hJq hK₂N hK₂c hKJ hout hx'mem
      (orderOf_eq_prime h5 hne)
  exact ⟨a, Subtype.ext (by simpa using h1)⟩

end SBc17

end CFSG.Quasithin
