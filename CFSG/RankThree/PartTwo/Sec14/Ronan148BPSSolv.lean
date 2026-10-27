module

public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.GroupTheory.ThompsonAxB
import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS

open CFSG CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
open CFSG.FiveTransitive.CharacteristicAutomorphism (restrict quotient restrict_apply_val
  quotient_apply_mk)

@[expose] def fixSub {B H : Type*} [Group B] [Group H] (σ : B →* MulAut H) : Subgroup H where
  carrier := {h | ∀ b, σ b h = h}
  mul_mem' := fun {x y} hx hy b => by rw [map_mul, hx b, hy b]
  one_mem' := fun b => map_one (σ b)
  inv_mem' := fun {x} hx b => by rw [map_inv, hx b]

theorem mem_fixSub {B H : Type*} [Group B] [Group H] {σ : B →* MulAut H} {h : H} :
    h ∈ fixSub σ ↔ ∀ b, σ b h = h :=
  Iff.rfl

theorem eq_one_of_mem_pGroup_of_coprime {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S T : Subgroup G} (hS : IsPGroup p S) (hT : Nat.Coprime p (Nat.card T)) {x : G} (hxS : x ∈ S)
    (hxT : x ∈ T) : x = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨x, hxS⟩
  have hk' : x ^ p ^ k = 1 := congrArg Subtype.val hk
  have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ Nat.card T := Subgroup.orderOf_dvd_natCard T hxT
  have hcop : Nat.Coprime (p ^ k) (Nat.card T) := Nat.Coprime.pow_left k hT
  have : orderOf x ∣ Nat.gcd (p ^ k) (Nat.card T) := Nat.dvd_gcd h1 h2
  rw [hcop] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

theorem map_le_centralizer_pCore {B H : Type*} [Group B] [Group H] [Finite B] [Finite H]
    (hB : IsPGroup 3 B) (σ : B →* MulAut H) (N : Subgroup H) [N.Characteristic]
    (hN3 : ¬ 3 ∣ Nat.card N) {Q K : Subgroup H}
    (hQK : Q ≤ K) (hKfix : K ≤ fixSub σ)
    (hKn : fixSub σ ≤ Subgroup.normalizer (K : Set H)) (hK3 : Nat.Coprime 3 (Nat.card K)) :
    Q.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer (CFSG.pCore 3 (H ⧸ N) : Set (H ⧸ N)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set mk : H →* H ⧸ N := QuotientGroup.mk' N with hmk
  set Hs := H ⧸ N
  set σs : B →* MulAut Hs := (quotient N).comp σ with hσs
  have hσs_mk : ∀ b (x : H), σs b (mk x) = mk (σ b x) := fun b x => quotient_apply_mk N (σ b) x
  have hmk_eq : ∀ x y : H, mk x = mk y ↔ x * y⁻¹ ∈ N := fun x y => by
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem,
      div_eq_mul_inv]
  set R := CFSG.pCore 3 Hs with hR
  have hRp : IsPGroup 3 R := CFSG.pCore_isPGroup
  set Qs : Subgroup Hs := Q.map mk with hQs
  have hQs3 : ¬ 3 ∣ Nat.card Qs := by
    intro h
    have h1 : Nat.card Qs ∣ Nat.card Q := Subgroup.card_map_dvd _ _
    have h2 : Nat.card Q ∣ Nat.card K := Subgroup.card_dvd_of_le hQK
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hK3 (h.trans (h1.trans h2))
  set β : B →* MulAut R := (restrict R).comp σs with hβ
  set α : Qs →* MulAut R := (restrict R).comp (MulAut.conj.comp Qs.subtype) with hα
  have hαapp : ∀ (a : Qs) (r : R), ((α a r : R) : Hs) = (a : Hs) * r * (a : Hs)⁻¹ :=
    fun a r => rfl
  have hσQs : ∀ (b : B) (a : Qs), σs b (a : Hs) = a := by
    intro b a
    obtain ⟨q, hq, hqa⟩ := a.2
    rw [← hqa, hσs_mk, hKfix (hQK hq) b]
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    intro a b
    ext r
    change (a : Hs) * σs b r * (a : Hs)⁻¹ = σs b ((a : Hs) * r * (a : Hs)⁻¹)
    rw [map_mul, map_mul, map_inv, hσQs b a]
  have hfix : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    intro a r hr
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (r : Hs)
    have hrfix : ∀ b, σs b (r : Hs) = r := fun b => congrArg Subtype.val (hr b)
    obtain ⟨c, hcg, hcfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hB σ N
      hN3 g).1 (by
      intro b x hx
      have hxg : mk x = mk g := (hmk_eq x g).mpr hx
      have hσx : mk (σ b x) = mk g := by
        rw [← hσs_mk, hxg]
        change σs b (QuotientGroup.mk' N g) = QuotientGroup.mk' N g
        rw [hg, hrfix b]
      exact (hmk_eq _ _).mp hσx)
    have hcr : mk c = (r : Hs) := by
      rw [← hg]
      exact (hmk_eq c g).mpr hcg
    have hcF : c ∈ fixSub σ := hcfix
    obtain ⟨q, hq, hqa⟩ := a.2
    have hqK : q ∈ K := hQK hq
    have hcomK : c * q * c⁻¹ * q⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKn hcF) q).mp hqK) (K.inv_mem hqK)
    have hcomR : mk (c * q * c⁻¹ * q⁻¹) ∈ R := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcr]
      have h1 : (r : Hs) * (mk q * (r : Hs)⁻¹ * (mk q)⁻¹) ∈ R :=
        R.mul_mem r.2 ((inferInstance : R.Normal).conj_mem _ (R.inv_mem r.2) _)
      simpa [mul_assoc] using h1
    have hKs3 : Nat.Coprime 3 (Nat.card (K.map mk)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) hK3
    have h1 : mk (c * q * c⁻¹ * q⁻¹) = 1 :=
      eq_one_of_mem_pGroup_of_coprime hRp hKs3 hcomR (Subgroup.mem_map_of_mem mk hcomK)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcr] at h1
    apply Subtype.ext
    rw [hαapp, ← hqa]
    have h2 : (r : Hs) * mk q = mk q * r := by
      calc (r : Hs) * mk q = (r : Hs) * mk q * (r : Hs)⁻¹ * (mk q)⁻¹ * (mk q * r) := by group
        _ = mk q * r := by rw [h1, one_mul]
    calc mk q * (r : Hs) * (mk q)⁻¹ = (r : Hs) * mk q * (mk q)⁻¹ := by rw [h2]
      _ = r := by group
  have hAB := CFSG.GroupTheory.thompson_A_times_B (p := 3) (R := R) (A := Qs) (B := B) hRp hQs3 hB
    α β hcomm hfix
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have := congrArg (fun φ : MulAut R => ((φ ⟨r, hr⟩ : R) : Hs)) (hAB ⟨x, hx⟩)
  simp only [hαapp, MulAut.one_apply] at this
  calc r * x = x * r * x⁻¹ * x := by rw [this]
    _ = x * r := by group

theorem le_pPrimeCore_of_solvable {B H : Type*} [Group B] [Group H] [Finite B] [Finite H]
    (hB : IsPGroup 3 B) (σ : B →* MulAut H)
    (hsol : Group.IsSolvable (H ⧸ CFSG.pPrimeCore 3 H)) {Q K : Subgroup H}
    (hQK : Q ≤ K) (hKfix : K ≤ fixSub σ)
    (hKn : fixSub σ ≤ Subgroup.normalizer (K : Set H)) (hK3 : Nat.Coprime 3 (Nat.card K)) :
    Q ≤ CFSG.pPrimeCore 3 H := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pPrimeCore 3 H with hO
  have hcop : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hcent := map_le_centralizer_pCore hB σ O hcop hQK hKfix hKn hK3
  have hcore : CFSG.pPrimeCore 3 (H ⧸ O) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hCR := CFSG.centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hsol hcore
  have hQs3 : Nat.Coprime 3 (Nat.card (Q.map (QuotientGroup.mk' O))) :=
    Nat.Coprime.coprime_dvd_right
      ((Subgroup.card_map_dvd _ _).trans (Subgroup.card_dvd_of_le hQK)) hK3
  intro x hx
  have hxQs : QuotientGroup.mk' O x ∈ Q.map (QuotientGroup.mk' O) := Subgroup.mem_map_of_mem _ hx
  have h1 : QuotientGroup.mk' O x = 1 :=
    eq_one_of_mem_pGroup_of_coprime CFSG.pCore_isPGroup hQs3 (hCR (hcent hxQs)) hxQs
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem le_pPrimeCoreOf_of_hom_solvable {Γ : Type} [Group Γ] [Finite Γ] {W B Q : Subgroup Γ}
    (hB : IsPGroup 3 B) (hBW : B ≤ Subgroup.normalizer (W : Set Γ)) (hQW : Q ≤ W)
    (hQO : Q ≤ pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (B : Set Γ)))
    {M : Type*} [Group M] (f : ↥W →* M) (hM : Group.IsSolvable f.range)
    (hker : Nat.Coprime 3 (Nat.card f.ker)) : Q ≤ pPrimeCoreOf 3 W := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ : ↥B →* MulAut ↥W := W.normalizerMonoidHom.comp (Subgroup.inclusion hBW) with hσ
  have hσapp : ∀ (b : ↥B) (w : ↥W), ((σ b w : ↥W) : Γ) = (b : Γ) * w * (b : Γ)⁻¹ :=
    fun b w => rfl
  set C := W ⊓ Subgroup.centralizer (B : Set Γ) with hC
  set K : Subgroup ↥W := (pPrimeCoreOf 3 C).subgroupOf W with hK
  have hOC : pPrimeCoreOf 3 C ≤ C := pPrimeCoreOf_le 3 C
  have hOW : pPrimeCoreOf 3 C ≤ W := hOC.trans inf_le_left
  have hmemfix : ∀ w : ↥W, w ∈ fixSub σ ↔ (w : Γ) ∈ Subgroup.centralizer (B : Set Γ) := by
    intro w
    rw [mem_fixSub, Subgroup.mem_centralizer_iff]
    constructor
    · intro h b hb
      have := congrArg Subtype.val (h ⟨b, hb⟩)
      rw [hσapp] at this
      calc b * (w : Γ) = b * w * b⁻¹ * b := by group
        _ = w * b := by rw [this]
    · intro h b
      apply Subtype.ext
      rw [hσapp, h b b.2]
      group
  have hQK : Q.subgroupOf W ≤ K := fun q hq => Subgroup.mem_subgroupOf.mpr (hQO hq)
  have hKfix : K ≤ fixSub σ := fun k hk => (hmemfix k).mpr (hOC (Subgroup.mem_subgroupOf.mp hk)).2
  have hKn : fixSub σ ≤ Subgroup.normalizer (K : Set ↥W) := by
    intro w hw
    have hwC : (w : Γ) ∈ C := ⟨w.2, (hmemfix w).mp hw⟩
    rw [Subgroup.mem_normalizer_iff]
    intro k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := Subgroup.mem_normalizer_iff.mp (le_normalizer_pPrimeCoreOf 3 C hwC) (k : Γ)
    simpa using this
  have hK3 : Nat.Coprime 3 (Nat.card K) := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOW).toEquiv]
    exact coprime_card_pPrimeCoreOf 3 C
  have hkerO : f.ker ≤ CFSG.pPrimeCore 3 ↥W := le_sSup ⟨inferInstance, hker⟩
  have hsol' : Group.IsSolvable (↥W ⧸ CFSG.pPrimeCore 3 ↥W) := by
    have : Group.IsSolvable (↥W ⧸ f.ker) :=
      Group.isSolvable_of_surjective (f := (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom)
        (QuotientGroup.quotientKerEquivRange f).symm.surjective
    refine Group.isSolvable_of_surjective
      (f := QuotientGroup.map f.ker (CFSG.pPrimeCore 3 ↥W) (MonoidHom.id _) hkerO) ?_
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(h : ↥W ⧸ f.ker), rfl⟩
  have h := le_pPrimeCore_of_solvable (hB.of_equiv (MulEquiv.refl _)) σ hsol' hQK hKfix hKn hK3
  intro q hq
  exact ⟨⟨q, hQW hq⟩, h (Subgroup.mem_subgroupOf.mpr hq), rfl⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS
