module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltEquiv
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.CGT.Foote82.T66.MC2Perm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique (evenWeight)
open CFSG.RankThree.PartTwo (altHeart evenWeightPerm evenWeightOnes)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct altAct_mk altAct_mul
  evenWeightPerm_pairEW exists_forall_eq_of_mem_evenWeightOnes)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (pairEW pairEW_apply
  exists_ne_four perm_eq_one_of_altHeart_fixed)

private theorem s16e_twoAR_altHeart_add_self {n : ℕ} (a : altHeart n) : a + a = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [← QuotientAddGroup.mk_add]
  have : x + x = 0 :=
    Subtype.ext (funext fun _ => (show ∀ c : ZMod 2, c + c = 0 by decide) _)
  rw [this, QuotientAddGroup.mk_zero]

private theorem s16e_twoAR_altHeart_add_comm {n : ℕ} (a b : altHeart n) : a + b = b + a := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add, add_comm]

private noncomputable instance s16e_twoAR_altHeartAddCommGroup {n : ℕ} :
    AddCommGroup (altHeart n) :=
  { (inferInstance : AddGroup (altHeart n)) with
    add_comm := s16e_twoAR_altHeart_add_comm }

theorem s16e_two_alt_comm_rk_ge {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {J : Subgroup W} {n : ℕ} (hn5 : 5 ≤ n) (h : AlternatingNatural H J ⊥ n) {x : MulAut W}
    (hx : x ∈ H) (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) :
    2 ≤ rk ↥(commSub J (Subgroup.zpowers x)) := by
  classical
  have hn : 0 < n := by omega
  obtain ⟨π, ψ, hπ, hψ⟩ := s16c167_altNatural_equiv hn h
  have hJinv : ∀ h' : ↥H, ∀ u ∈ J, (h' : MulAut W) u ∈ J := by
    obtain ⟨π₀, -, -, -, hJinv, -⟩ := h
    exact hJinv
  obtain ⟨γ, hγ⟩ := hπ ⟨x, hx⟩
  have hγval : ((π γ : ↥H) : MulAut W) = x := by rw [hγ]
  have hγ1 : γ ≠ 1 := by
    intro h1
    have hx' : (⟨x, hx⟩ : ↥H) = 1 := by rw [← hγ, h1, map_one]
    exact hx1 (Subtype.ext_iff.mp hx')
  let σ : Equiv.Perm (Fin n) := γ
  have hσA : σ ∈ alternatingGroup (Fin n) := γ.2
  have hσ1 : σ ≠ 1 := fun hs => hγ1 (Subtype.ext hs)
  have hψx : ∀ (u : ↥J) (hu : x (u : W) ∈ J),
      ψ ⟨x (u : W), hu⟩ =
        Multiplicative.ofAdd (altAct σ (Multiplicative.toAdd (ψ u))) := by
    intro u hu
    have hu' : ((π γ : ↥H) : MulAut W) (u : W) ∈ J := by rw [hγval]; exact hu
    have hh := hψ γ u hu'
    have hsub : (⟨x (u : W), hu⟩ : ↥J) =
        ⟨((π γ : ↥H) : MulAut W) (u : W), hu'⟩ := by
      refine Subtype.ext ?_
      show x (u : W) = ((π γ : ↥H) : MulAut W) (u : W)
      rw [hγval]
    rw [hsub]
    exact hh
  have hψcomm : ∀ (u : ↥J) (hu : x (u : W) ∈ J),
      ψ ⟨x (u : W) * (u : W)⁻¹, J.mul_mem hu (J.inv_mem u.2)⟩ =
        Multiplicative.ofAdd (altAct σ (Multiplicative.toAdd (ψ u)) +
          Multiplicative.toAdd (ψ u)) := by
    intro u hu
    have h1 : ψ ⟨x (u : W), hu⟩ =
        Multiplicative.ofAdd (altAct σ (Multiplicative.toAdd (ψ u))) := hψx u hu
    have h2 : (⟨x (u : W) * (u : W)⁻¹, J.mul_mem hu (J.inv_mem u.2)⟩ : ↥J) =
        ⟨x (u : W), hu⟩ * u⁻¹ := Subtype.ext rfl
    rw [h2, map_mul, map_inv, h1]
    rw [show (ψ u)⁻¹ = Multiplicative.ofAdd (-(Multiplicative.toAdd (ψ u))) from by
      rw [← ofAdd_toAdd ((ψ u)⁻¹), toAdd_inv]]
    rw [← ofAdd_add]
    congr 1
    have hneg : -Multiplicative.toAdd (ψ u) = Multiplicative.toAdd (ψ u) := by
      have hh := s16e_twoAR_altHeart_add_self (Multiplicative.toAdd (ψ u))
      have h2' : Multiplicative.toAdd (ψ u) + -Multiplicative.toAdd (ψ u) =
          Multiplicative.toAdd (ψ u) + Multiplicative.toAdd (ψ u) := by
        rw [add_neg_cancel, hh]
      exact add_left_cancel h2'
    rw [hneg]
  have hfix : ∀ v : altHeart n, altAct (σ * σ) v = v := by
    intro v
    obtain ⟨u, hu⟩ := ψ.surjective (Multiplicative.ofAdd v)
    have hu2 : x (u : W) ∈ J := hJinv ⟨x, hx⟩ (u : W) u.2
    have h1 : ψ ⟨x (u : W), hu2⟩ = Multiplicative.ofAdd (altAct σ v) := by
      have hh := hψx u hu2
      rwa [hu, toAdd_ofAdd] at hh
    have hu3 : x (x (u : W)) ∈ J := hJinv ⟨x, hx⟩ (x (u : W)) hu2
    have hx2u : x (x (u : W)) = (u : W) := by
      have hh : (x ^ 2) (u : W) = (u : W) := by rw [hx2]; rfl
      simpa [pow_two, MulAut.mul_apply] using hh
    have h2 : ψ u = Multiplicative.ofAdd (altAct σ (altAct σ v)) := by
      have hh := hψx ⟨x (u : W), hu2⟩ hu3
      rw [show (⟨x (x (u : W)), hu3⟩ : ↥J) = u from Subtype.ext hx2u] at hh
      simp only [h1, toAdd_ofAdd] at hh
      exact hh
    have hvv : v = altAct σ (altAct σ v) := by
      have hh := congrArg Multiplicative.toAdd (hu.symm.trans h2)
      simpa using hh
    rw [altAct_mul]
    exact hvv.symm
  have hσ2 : σ * σ = 1 := by
    refine perm_eq_one_of_altHeart_fixed hn5 (σ * σ) fun y => ?_
    have hh := hfix (QuotientAddGroup.mk y : altHeart n)
    rw [altAct_mk] at hh
    exact hh
  have hσord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  have h4supp : 4 ≤ σ.support.card := CFSG.CGT.Foote82.MC2.four_le_card_support hσord hσA
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < σ.support.card)
    exact ⟨i, Equiv.Perm.mem_support.mp hi⟩
  let j : Fin n := σ i
  have hji : j ≠ i := fun h => hi h
  have hσj : σ j = i := by
    show σ (σ i) = i
    rw [← Equiv.Perm.mul_apply, hσ2, Equiv.Perm.one_apply]
  have hjsupp : j ∈ σ.support := by
    rw [Equiv.Perm.mem_support, hσj]
    exact hji.symm
  have hkexists : ∃ k, k ∈ σ.support ∧ k ≠ i ∧ k ≠ j := by
    have h1 : (σ.support.erase i).card = σ.support.card - 1 :=
      Finset.card_erase_of_mem (Equiv.Perm.mem_support.mpr hi)
    have hjmem : j ∈ σ.support.erase i := Finset.mem_erase.mpr ⟨hji, hjsupp⟩
    have h2 : ((σ.support.erase i).erase j).card = (σ.support.erase i).card - 1 :=
      Finset.card_erase_of_mem hjmem
    have hpos : 0 < ((σ.support.erase i).erase j).card := by omega
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
    exact ⟨k, (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2,
      (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1, (Finset.mem_erase.mp hk).1⟩
  obtain ⟨k, hksupp, hki, hkj⟩ := hkexists
  have hσkne : σ k ≠ k := Equiv.Perm.mem_support.mp hksupp
  let l : Fin n := σ k
  have hσl : σ l = k := by
    show σ (σ k) = k
    rw [← Equiv.Perm.mul_apply, hσ2, Equiv.Perm.one_apply]
  have hkl : k ≠ l := fun h => hσkne h.symm
  have hij : i ≠ j := hji.symm
  have hik : i ≠ k := hki.symm
  have hil : i ≠ l := by
    intro h
    have h1 : σ k = σ j := by rw [show σ k = l from rfl, h.symm, hσj]
    exact hkj (σ.injective h1)
  have hjk : j ≠ k := hkj.symm
  have hjl : j ≠ l := by
    intro h
    have h1 : σ k = σ i := by rw [show σ k = l from rfl, h.symm, show j = σ i from rfl]
    exact hik (σ.injective h1).symm
  obtain ⟨p, hpi, hpj, hpk, hpl⟩ := exists_ne_four hn5 i j k l
  let u₁ : evenWeight n := pairEW i k
  let u₂ : evenWeight n := pairEW i p
  let v₁ : altHeart n := (u₁ : altHeart n)
  let v₂ : altHeart n := (u₂ : altHeart n)
  let F₁ : evenWeight n := evenWeightPerm σ u₁ + u₁
  let F₂ : evenWeight n := evenWeightPerm σ u₂ + u₂
  have hF₁eq : F₁ = pairEW j l + pairEW i k := by
    show evenWeightPerm σ (pairEW i k) + pairEW i k = pairEW j l + pairEW i k
    rw [evenWeightPerm_pairEW]
  have hF₂eq : F₂ = pairEW j (σ p) + pairEW i p := by
    show evenWeightPerm σ (pairEW i p) + pairEW i p = pairEW j (σ p) + pairEW i p
    rw [evenWeightPerm_pairEW]
  have hF₁i : (F₁ : Fin n → ZMod 2) i = 1 := by
    rw [hF₁eq, AddSubgroup.coe_add, Pi.add_apply, pairEW_apply, pairEW_apply,
      if_neg hij, if_neg hil, if_pos rfl, if_neg hik]
    norm_num
  have hF₁k : (F₁ : Fin n → ZMod 2) k = 1 := by
    rw [hF₁eq, AddSubgroup.coe_add, Pi.add_apply, pairEW_apply, pairEW_apply,
      if_neg hkj, if_neg hkl, if_neg hki, if_pos rfl]
    norm_num
  have hF₁p : (F₁ : Fin n → ZMod 2) p = 0 := by
    rw [hF₁eq, AddSubgroup.coe_add, Pi.add_apply, pairEW_apply, pairEW_apply,
      if_neg hpj, if_neg hpl, if_neg hpi, if_neg hpk]
    norm_num
  have hσpi : i ≠ σ p := by
    intro h
    have h1 : σ (σ p) = σ i := by rw [h]
    rw [show σ (σ p) = p from by
      rw [← Equiv.Perm.mul_apply, hσ2, Equiv.Perm.one_apply],
      show σ i = j from rfl] at h1
    exact hpj h1
  have hσpk : k ≠ σ p := by
    intro h
    have h1 : σ (σ p) = σ k := by rw [h]
    rw [show σ (σ p) = p from by
      rw [← Equiv.Perm.mul_apply, hσ2, Equiv.Perm.one_apply],
      show σ k = l from rfl] at h1
    exact hpl h1
  have hF₂i : (F₂ : Fin n → ZMod 2) i = 1 := by
    rw [hF₂eq, AddSubgroup.coe_add, Pi.add_apply, pairEW_apply, pairEW_apply,
      if_neg hij, if_neg hσpi, if_pos rfl, if_neg hpi.symm]
    norm_num
  have hF₂k : (F₂ : Fin n → ZMod 2) k = 0 := by
    rw [hF₂eq, AddSubgroup.coe_add, Pi.add_apply, pairEW_apply, pairEW_apply,
      if_neg hkj, if_neg hσpk, if_neg hki, if_neg hpk.symm]
    norm_num
  have hF₁F₂i : ((F₁ + F₂ : evenWeight n) : Fin n → ZMod 2) i = 0 := by
    rw [AddSubgroup.coe_add, Pi.add_apply, hF₁i, hF₂i]
    exact CharTwo.add_self_eq_zero (1 : ZMod 2)
  have hF₁F₂k : ((F₁ + F₂ : evenWeight n) : Fin n → ZMod 2) k = 1 := by
    rw [AddSubgroup.coe_add, Pi.add_apply, hF₁k, hF₂k]
    exact add_zero (1 : ZMod 2)
  let f₁ : altHeart n := altAct σ v₁ + v₁
  let f₂ : altHeart n := altAct σ v₂ + v₂
  have hf₁ : (F₁ : altHeart n) = f₁ := by
    show (QuotientAddGroup.mk (evenWeightPerm σ u₁ + u₁) : altHeart n) =
      altAct σ v₁ + v₁
    rw [QuotientAddGroup.mk_add, ← altAct_mk]
  have hf₂ : (F₂ : altHeart n) = f₂ := by
    show (QuotientAddGroup.mk (evenWeightPerm σ u₂ + u₂) : altHeart n) =
      altAct σ v₂ + v₂
    rw [QuotientAddGroup.mk_add, ← altAct_mk]
  have hf₁f₂eq : f₁ + f₂ = (F₁ + F₂ : altHeart n) := by
    rw [← hf₁, ← hf₂, ← QuotientAddGroup.mk_add]
  have hf₁0 : f₁ ≠ 0 := by
    intro h
    have hF : (F₁ : altHeart n) = 0 := by rw [hf₁]; exact h
    have hmem : F₁ ∈ evenWeightOnes n := (QuotientAddGroup.eq_zero_iff _).1 hF
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hmem
    have h1 := hc i
    have h2 := hc p
    rw [hF₁i] at h1
    rw [hF₁p] at h2
    exact one_ne_zero (h1.trans h2.symm)
  have hf₂0 : f₂ ≠ 0 := by
    intro h
    have hF : (F₂ : altHeart n) = 0 := by rw [hf₂]; exact h
    have hmem : F₂ ∈ evenWeightOnes n := (QuotientAddGroup.eq_zero_iff _).1 hF
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hmem
    have h1 := hc i
    have h2 := hc k
    rw [hF₂i] at h1
    rw [hF₂k] at h2
    exact one_ne_zero (h1.trans h2.symm)
  have hf₁f₂0 : f₁ + f₂ ≠ 0 := by
    intro h
    have hF : (F₁ + F₂ : altHeart n) = 0 := by rw [← hf₁f₂eq]; exact h
    have hmem : F₁ + F₂ ∈ evenWeightOnes n := (QuotientAddGroup.eq_zero_iff _).1 hF
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hmem
    have h1 := hc i
    have h2 := hc k
    rw [hF₁F₂i] at h1
    rw [hF₁F₂k] at h2
    exact zero_ne_one (h1.trans h2.symm)
  have hf₁f₂ : f₁ ≠ f₂ := fun h => hf₁f₂0 (by rw [h, s16e_twoAR_altHeart_add_self])
  have hJexp : ∀ u : ↥J, u ^ 2 = 1 := by
    intro u
    apply ψ.injective
    rw [map_pow, map_one, ← ofAdd_toAdd ((ψ u) ^ 2)]
    rw [show Multiplicative.toAdd ((ψ u) ^ 2) = 0 from by
      rw [pow_two, toAdd_mul, s16e_twoAR_altHeart_add_self]]
    rfl
  let A : Subgroup W := commSub J (Subgroup.zpowers x)
  have hAJ : A ≤ J := commSub_le_of_invariant fun y hy w hw =>
    hJinv ⟨y, (Subgroup.zpowers_le.mpr hx) hy⟩ w hw
  let w₁ : ↥J := ψ.symm (Multiplicative.ofAdd v₁)
  let w₂ : ↥J := ψ.symm (Multiplicative.ofAdd v₂)
  have hw₁ : ψ w₁ = Multiplicative.ofAdd v₁ := ψ.apply_symm_apply _
  have hw₂ : ψ w₂ = Multiplicative.ofAdd v₂ := ψ.apply_symm_apply _
  have hw₁J : x (w₁ : W) ∈ J := hJinv ⟨x, hx⟩ (w₁ : W) w₁.2
  have hw₂J : x (w₂ : W) ∈ J := hJinv ⟨x, hx⟩ (w₂ : W) w₂.2
  let a : W := x (w₁ : W) * (w₁ : W)⁻¹
  let b : W := x (w₂ : W) * (w₂ : W)⁻¹
  have haA : a ∈ A := Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, (w₁ : W), w₁.2, rfl⟩
  have hbA : b ∈ A := Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, (w₂ : W), w₂.2, rfl⟩
  let ΨA : ↥A →* Multiplicative (altHeart n) :=
    ψ.toMonoidHom.comp (Subgroup.inclusion hAJ)
  have hΨ1 : ΨA ⟨1, A.one_mem⟩ = Multiplicative.ofAdd (0 : altHeart n) := by
    show ψ ⟨(1 : W), hAJ A.one_mem⟩ = Multiplicative.ofAdd 0
    rw [show (⟨(1 : W), hAJ A.one_mem⟩ : ↥J) = 1 from Subtype.ext rfl, map_one]
    rfl
  have hΨa : ΨA ⟨a, haA⟩ = Multiplicative.ofAdd f₁ := by
    have h := hψcomm w₁ hw₁J
    have hvv : Multiplicative.toAdd (ψ w₁) = v₁ := by
      rw [hw₁, toAdd_ofAdd]
    rw [hvv] at h
    calc ΨA ⟨a, haA⟩ = ψ ⟨a, hAJ haA⟩ := rfl
      _ = ψ ⟨x (w₁ : W) * (w₁ : W)⁻¹, J.mul_mem hw₁J (J.inv_mem w₁.2)⟩ := by
            rw [show (⟨a, hAJ haA⟩ : ↥J) =
              ⟨x (w₁ : W) * (w₁ : W)⁻¹, J.mul_mem hw₁J (J.inv_mem w₁.2)⟩ from
              Subtype.ext rfl]
      _ = Multiplicative.ofAdd f₁ := h
  have hΨb : ΨA ⟨b, hbA⟩ = Multiplicative.ofAdd f₂ := by
    have h := hψcomm w₂ hw₂J
    have hvv : Multiplicative.toAdd (ψ w₂) = v₂ := by
      rw [hw₂, toAdd_ofAdd]
    rw [hvv] at h
    calc ΨA ⟨b, hbA⟩ = ψ ⟨b, hAJ hbA⟩ := rfl
      _ = ψ ⟨x (w₂ : W) * (w₂ : W)⁻¹, J.mul_mem hw₂J (J.inv_mem w₂.2)⟩ := by
            rw [show (⟨b, hAJ hbA⟩ : ↥J) =
              ⟨x (w₂ : W) * (w₂ : W)⁻¹, J.mul_mem hw₂J (J.inv_mem w₂.2)⟩ from
              Subtype.ext rfl]
      _ = Multiplicative.ofAdd f₂ := h
  have hΨab : ΨA ⟨a * b, A.mul_mem haA hbA⟩ = Multiplicative.ofAdd (f₁ + f₂) := by
    calc ΨA ⟨a * b, A.mul_mem haA hbA⟩ = ΨA (⟨a, haA⟩ * ⟨b, hbA⟩) := rfl
      _ = ΨA ⟨a, haA⟩ * ΨA ⟨b, hbA⟩ := map_mul ΨA _ _
      _ = Multiplicative.ofAdd (f₁ + f₂) := by
            rw [hΨa, hΨb, ← ofAdd_add]
  have hofAdd_ne : ∀ {s t : altHeart n}, s ≠ t →
      Multiplicative.ofAdd s ≠ Multiplicative.ofAdd t := by
    intro s t hst h
    exact hst (by simpa using congrArg Multiplicative.toAdd h)
  have ha1 : a ≠ 1 := by
    intro h
    have h1 : (⟨a, haA⟩ : ↥A) = ⟨1, A.one_mem⟩ := Subtype.ext h
    have h2 := congrArg ΨA h1
    rw [hΨa, hΨ1] at h2
    exact hofAdd_ne hf₁0 h2
  have hb1 : b ≠ 1 := by
    intro h
    have h1 : (⟨b, hbA⟩ : ↥A) = ⟨1, A.one_mem⟩ := Subtype.ext h
    have h2 := congrArg ΨA h1
    rw [hΨb, hΨ1] at h2
    exact hofAdd_ne hf₂0 h2
  have hab1 : a * b ≠ 1 := by
    intro h
    have h1 : (⟨a * b, A.mul_mem haA hbA⟩ : ↥A) = ⟨1, A.one_mem⟩ := Subtype.ext h
    have h2 := congrArg ΨA h1
    rw [hΨab, hΨ1] at h2
    exact hofAdd_ne hf₁f₂0 h2
  have hab : a ≠ b := by
    intro h
    have h1 : (⟨a, haA⟩ : ↥A) = ⟨b, hbA⟩ := Subtype.ext h
    have h2 := congrArg ΨA h1
    rw [hΨa, hΨb] at h2
    exact hofAdd_ne hf₁f₂ h2
  have h1ab : a ≠ a * b := by
    intro h
    have h1 : (⟨a, haA⟩ : ↥A) = ⟨a * b, A.mul_mem haA hbA⟩ := Subtype.ext h
    have h2 := congrArg ΨA h1
    rw [hΨa, hΨab] at h2
    have h3 : f₁ = f₁ + f₂ := by simpa using congrArg Multiplicative.toAdd h2
    have hz : f₂ = 0 := by
      have h4 : f₁ + 0 = f₁ + f₂ := by rw [add_zero]; exact h3
      exact (add_left_cancel h4).symm
    exact hf₂0 hz
  have h2ab : b ≠ a * b := by
    intro h
    have h1 : (⟨b, hbA⟩ : ↥A) = ⟨a * b, A.mul_mem haA hbA⟩ := Subtype.ext h
    have h2 := congrArg ΨA h1
    rw [hΨb, hΨab] at h2
    have h3 : f₂ = f₁ + f₂ := by simpa using congrArg Multiplicative.toAdd h2
    have hz : f₁ = 0 := by
      have h4 : f₂ + 0 = f₂ + f₁ := by rw [add_zero, add_comm]; exact h3
      exact (add_left_cancel h4).symm
    exact hf₁0 hz
  have hAcard4 : 4 ≤ Nat.card ↥A := by
    letI : Fintype ↥A := Fintype.ofFinite _
    have e1 : (⟨1, A.one_mem⟩ : ↥A) ≠ ⟨a, haA⟩ :=
      fun h => ha1 (Subtype.ext_iff.mp h).symm
    have e2 : (⟨1, A.one_mem⟩ : ↥A) ≠ ⟨b, hbA⟩ :=
      fun h => hb1 (Subtype.ext_iff.mp h).symm
    have e3 : (⟨1, A.one_mem⟩ : ↥A) ≠ ⟨a * b, A.mul_mem haA hbA⟩ :=
      fun h => hab1 (Subtype.ext_iff.mp h).symm
    have e4 : (⟨a, haA⟩ : ↥A) ≠ ⟨b, hbA⟩ := fun h => hab (Subtype.ext_iff.mp h)
    have e5 : (⟨a, haA⟩ : ↥A) ≠ ⟨a * b, A.mul_mem haA hbA⟩ :=
      fun h => h1ab (Subtype.ext_iff.mp h)
    have e6 : (⟨b, hbA⟩ : ↥A) ≠ ⟨a * b, A.mul_mem haA hbA⟩ :=
      fun h => h2ab (Subtype.ext_iff.mp h)
    have hS : ({⟨1, A.one_mem⟩, ⟨a, haA⟩, ⟨b, hbA⟩,
        ⟨a * b, A.mul_mem haA hbA⟩} : Finset ↥A).card = 4 :=
      Finset.card_eq_four.mpr
        ⟨⟨1, A.one_mem⟩, ⟨a, haA⟩, ⟨b, hbA⟩, ⟨a * b, A.mul_mem haA hbA⟩,
          e1, e2, e3, e4, e5, e6, rfl⟩
    have hle : 4 ≤ (Finset.univ : Finset ↥A).card := by
      rw [← hS]
      exact Finset.card_le_card (Finset.subset_univ _)
    simpa [Nat.card_eq_fintype_card] using hle
  have hAexp : ∀ y : ↥A, y ^ 2 = 1 := by
    intro y
    apply Subtype.ext
    have hh := hJexp ⟨(y : W), hAJ y.2⟩
    simpa using congrArg Subtype.val hh
  have hAp : IsPGroup 2 ↥A := isPGroup_two_of_sq_eq_one hAexp
  have hAcard : Nat.card ↥A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hAp
  have hpow : 2 ^ 2 ≤ 2 ^ rk ↥A := by
    rw [← hAcard]
    simpa using hAcard4
  exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num : 1 < 2)).mp hpow

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
