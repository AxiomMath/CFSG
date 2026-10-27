module

public import CFSG.Quasithin.Vol2.Ch12Sec6L20

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126N Equiv

namespace S126L20a

theorem coreAct_pe (σ : Perm (Fin 8)) (a b : Fin 8) : coreAct 8 σ (pe a b) = pe (σ a) (σ b) :=
  Subtype.ext (by rw [coreAct_coe]; exact B5FinS8.permAct_pv σ a b)

theorem dAct_pe (σ : Perm (Fin 8)) (a b : Fin 8) :
    dAct σ (QuotientGroup.mk (pe a b)) = QuotientGroup.mk (pe (σ a) (σ b)) := by
  rw [dAct_mk, coreAct_pe]

theorem pe_comm (a b : Fin 8) : pe a b = pe b a :=
  Subtype.ext (congrArg Multiplicative.ofAdd (add_comm _ _))

theorem toAdd_pe (a b : Fin 8) :
    Multiplicative.toAdd ((pe a b : ↥(coreMod 8)) : PermMod 8) = B5FinS8.pv a b := rfl

theorem wt_pv2_chk : ∀ a b c d : Fin 8, [a, b, c, d].Nodup →
    (Finset.univ.filter fun i => (B5FinS8.pv a b + B5FinS8.pv c d) i ≠ 0).card = 4 := by
  decide +kernel

theorem wt_pv2 (a b c d : Fin 8) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    (Finset.univ.filter fun i => (B5FinS8.pv a b + B5FinS8.pv c d) i ≠ 0).card = 4 :=
  wt_pv2_chk a b c d (by simp [hab, hac, had, hbc, hbd, hcd])

theorem mem_pv2 (a b c d : Fin 8) :
    Multiplicative.ofAdd (B5FinS8.pv a b + B5FinS8.pv c d) ∈ coreMod 8 := by
  rw [mem_coreMod]
  simp only [toAdd_ofAdd, Pi.add_apply]
  rw [Finset.sum_add_distrib, B5FinS8.sum_pv, B5FinS8.sum_pv, add_zero]

theorem pv_sub_pv : ∀ i j k : Fin 8, B5FinS8.pv i k - B5FinS8.pv j k = B5FinS8.pv i j := by
  decide +kernel

theorem zmod2_six : ∀ p q r s t u : ZMod 2,
    (p + r) + (q + s) + ((p + t) + (q + u)) = (r + t) + (s + u) := by
  decide

theorem mk_ne_one {m : ↥(coreMod 8)} (h : wt (m : PermMod 8) = 2 ∨ wt (m : PermMod 8) = 4) :
    (QuotientGroup.mk m : D8) ≠ 1 := by
  intro h1
  rcases (mk_eq_one_iff m).1 h1 with rfl | rfl
  · rw [Subgroup.coe_one, wt_one] at h
    omega
  · change wt (allOnes 8) = 2 ∨ wt (allOnes 8) = 4 at h
    rw [wt_allOnes] at h
    omega

theorem D8_comm (y y' : D8) : y * y' = y' * y :=
  iota_inj (by rw [map_mul, map_mul, mul_comm])

theorem pe_mul_inv_coreAct (σ : Perm (Fin 8)) (i k : Fin 8) (hk : σ k = k) :
    pe i k * (coreAct 8 σ (pe i k))⁻¹ = pe i (σ i) := by
  rw [coreAct_pe, hk]
  apply Subtype.ext
  change Multiplicative.ofAdd (B5FinS8.pv i k) * (Multiplicative.ofAdd (B5FinS8.pv (σ i) k))⁻¹ =
    Multiplicative.ofAdd (B5FinS8.pv i (σ i))
  rw [← ofAdd_neg, ← ofAdd_add, ← sub_eq_add_neg, pv_sub_pv]

theorem wt_pe {a b : Fin 8} (h : a ≠ b) : wt ((pe a b : ↥(coreMod 8)) : PermMod 8) = 2 :=
  wt_pv a b h

theorem nonsing_comm (σ : Perm (Fin 8)) {i k : Fin 8} (hk : σ k = k) (hi : σ i ≠ i) :
    IsNonsing ((QuotientGroup.mk (pe i k) : D8) * (dAct σ (QuotientGroup.mk (pe i k)))⁻¹) := by
  rw [dAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, pe_mul_inv_coreAct σ i k hk]
  exact ⟨_, rfl, wt_pe hi.symm⟩

theorem exists_moved {σ : Perm (Fin 8)} (h1 : σ ≠ 1) : ∃ i, σ i ≠ i := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  exact h1 (Equiv.ext hc)

theorem exists_not_mem (s : Finset (Fin 8)) (h : s.card < 8) : ∃ x : Fin 8, x ∉ s := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  have : (Finset.univ : Finset (Fin 8)) ⊆ s := fun x _ => hc x
  have h2 := Finset.card_le_card this
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega

theorem card_lt_filter (σ : Perm (Fin 8)) (hfpf : ∀ i, σ i ≠ i) (hinv : ∀ i, σ (σ i) = i) :
    (Finset.univ.filter fun i => i < σ i).card = 4 := by
  set S := Finset.univ.filter fun i => i < σ i with hS
  have h1 : Sᶜ = S.map σ.toEmbedding := by
    ext i
    simp only [hS, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro h
      refine ⟨σ i, ?_, hinv i⟩
      rw [hinv i]
      have := hfpf i
      exact lt_of_le_of_ne (not_lt.1 h) this
    · rintro ⟨j, hj, rfl⟩
      rw [hinv j]
      exact not_lt.2 hj.le
  have h2 := Finset.card_add_card_compl S
  rw [h1, Finset.card_map, Fintype.card_fin] at h2
  omega

theorem eset_mem_of_card {S : Finset (Fin 8)} (h : S.card = 4) : eset S ∈ coreMod 8 := by
  rw [mem_coreMod]
  change ∑ i, (if i ∈ S then (1 : ZMod 2) else 0) = 0
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, h]
  decide

theorem exists_mul_inv_coreAct_eq_eOm (σ : Perm (Fin 8)) (hfpf : ∀ i, σ i ≠ i)
    (hinv : ∀ i, σ (σ i) = i) : ∃ m : ↥(coreMod 8), m * (coreAct 8 σ m)⁻¹ = eOm := by
  set S := Finset.univ.filter fun i => i < σ i with hS
  have hm := eset_mem_of_card (card_lt_filter σ hfpf hinv)
  refine ⟨⟨eset S, hm⟩, ?_⟩
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  have hσi : σ⁻¹ i = σ i := by
    rw [Perm.inv_eq_iff_eq, hinv]
  have key : σ i ∈ S ↔ i ∉ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, hinv i]
    constructor
    · exact fun h h' => absurd (h.trans h') (lt_irrefl _)
    · intro h
      exact lt_of_le_of_ne (not_lt.1 h) (hfpf i)
  rw [Subgroup.coe_mul, Subgroup.coe_inv, coreAct_coe, toAdd_mul, toAdd_inv, Pi.add_apply,
    Pi.neg_apply, permAct_apply, hσi]
  change (if i ∈ S then (1 : ZMod 2) else 0) + -(if σ i ∈ S then (1 : ZMod 2) else 0) = 1
  by_cases h : i ∈ S
  · have h' : σ i ∉ S := fun h' => (key.1 h') h
    simp only [h, h', ite_true, ite_false]
    decide
  · have h' : σ i ∈ S := key.2 h
    simp only [h, h', ite_true, ite_false]
    decide

@[expose] noncomputable def fix1 (σ : Perm (Fin 8)) : Subgroup D8 where
  carrier := {y | dAct σ y = y}
  one_mem' := map_one (dAct σ)
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_fix1 {σ : Perm (Fin 8)} {y : D8} : y ∈ fix1 σ ↔ dAct σ y = y := Iff.rfl

@[expose] noncomputable def theta (σ : Perm (Fin 8)) : D8 →* D8 where
  toFun y := y * dAct σ y
  map_one' := by rw [map_one, one_mul]
  map_mul' y y' := by
    rw [map_mul]
    calc y * y' * (dAct σ y * dAct σ y') = y * (y' * dAct σ y) * dAct σ y' := by
          simp only [mul_assoc]
      _ = y * (dAct σ y * y') * dAct σ y' := by rw [D8_comm y']
      _ = y * dAct σ y * (y' * dAct σ y') := by simp only [mul_assoc]

theorem theta_apply (σ : Perm (Fin 8)) (y : D8) : theta σ y = y * dAct σ y := rfl

theorem ker_theta (σ : Perm (Fin 8)) : (theta σ).ker = fix1 σ := by
  ext y
  rw [MonoidHom.mem_ker, theta_apply, mem_fix1]
  constructor
  · intro h
    calc dAct σ y = y * y * dAct σ y := by rw [S126L20.mul_self_eq_one, one_mul]
      _ = y * (y * dAct σ y) := by rw [mul_assoc]
      _ = y := by rw [h, mul_one]
  · intro h
    rw [h, S126L20.mul_self_eq_one]

theorem pe_mk_mul (a b c d : Fin 8) :
    (QuotientGroup.mk (pe a b) : D8) * QuotientGroup.mk (pe c d) =
      QuotientGroup.mk (⟨Multiplicative.ofAdd (B5FinS8.pv a b + B5FinS8.pv c d),
        mem_pv2 a b c d⟩ : ↥(coreMod 8)) := by
  rw [← QuotientGroup.mk_mul]
  rfl

theorem pe_mk_ne_one {a b c d : Fin 8} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    (QuotientGroup.mk (pe a b) : D8) * QuotientGroup.mk (pe c d) ≠ 1 := by
  rw [pe_mk_mul]
  exact mk_ne_one (Or.inr (wt_pv2 a b c d hab hac had hbc hbd hcd))

theorem pe_mk_ne {a b c d : Fin 8} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    (QuotientGroup.mk (pe a b) : D8) ≠ QuotientGroup.mk (pe c d) := by
  intro h
  apply pe_mk_ne_one hab hac had hbc hbd hcd
  rw [h, S126L20.mul_self_eq_one]

theorem card_eq_pow_of_le {H : Subgroup D8} : ∃ k : ℕ, Nat.card H = 2 ^ k := by
  have h := Subgroup.card_subgroup_dvd_card H
  rw [S126L20.card_D8_eq, show (64 : ℕ) = 2 ^ 6 by norm_num] at h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  exact ⟨k, hk⟩

theorem card_fix1_le {σ : Perm (Fin 8)} (hfpf : ∀ i, σ i ≠ i) (hinv : ∀ i, σ (σ i) = i) :
    Nat.card (fix1 σ) ≤ 16 := by
  set a : Fin 8 := 0
  set b := σ a with hb
  obtain ⟨c, hc⟩ := exists_not_mem {a, b} (lt_of_le_of_lt Finset.card_le_two (by norm_num))
  set d := σ c with hd
  obtain ⟨e, he⟩ := exists_not_mem {a, b, c, d}
    (lt_of_le_of_lt Finset.card_le_four (by norm_num))
  set f := σ e with hf
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc he
  obtain ⟨hca, hcb⟩ := hc
  obtain ⟨hea, heb, hec, hed⟩ := he
  have hba : b ≠ a := hfpf a
  have hdc : d ≠ c := hfpf c
  have hda : d ≠ a := fun h => hcb (by rw [hb, ← h, hd, hinv])
  have hdb : d ≠ b := fun h => hca (σ.injective h)
  have hfe : f ≠ e := hfpf e
  have hfa : f ≠ a := fun h => heb (by rw [hb, ← h, hf, hinv])
  have hfb : f ≠ b := fun h => hea (σ.injective h)
  have hfc : f ≠ c := fun h => hed (by rw [hd, ← h, hf, hinv])
  have hfd : f ≠ d := fun h => hec (σ.injective h)
  have h1 : theta σ (QuotientGroup.mk (pe a c)) =
      QuotientGroup.mk (pe a c) * QuotientGroup.mk (pe b d) := by
    rw [theta_apply, dAct_pe]
  have h2 : theta σ (QuotientGroup.mk (pe a e)) =
      QuotientGroup.mk (pe a e) * QuotientGroup.mk (pe b f) := by
    rw [theta_apply, dAct_pe]
  have n1 : theta σ (QuotientGroup.mk (pe a c)) ≠ 1 := by
    rw [h1]
    exact pe_mk_ne_one (Ne.symm hca) (Ne.symm hba) (Ne.symm hda) hcb (Ne.symm hdc) (Ne.symm hdb)
  have n2 : theta σ (QuotientGroup.mk (pe a e)) ≠ 1 := by
    rw [h2]
    exact pe_mk_ne_one (Ne.symm hea) (Ne.symm hba) (Ne.symm hfa) heb (Ne.symm hfe) (Ne.symm hfb)
  have n12 : theta σ (QuotientGroup.mk (pe a c)) ≠ theta σ (QuotientGroup.mk (pe a e)) := by
    intro h
    have h3 : theta σ (QuotientGroup.mk (pe a c)) * theta σ (QuotientGroup.mk (pe a e)) = 1 := by
      rw [h, S126L20.mul_self_eq_one]
    rw [h1, h2, pe_mk_mul, pe_mk_mul, ← QuotientGroup.mk_mul] at h3
    have e1 : ((⟨Multiplicative.ofAdd (B5FinS8.pv a c + B5FinS8.pv b d), mem_pv2 a c b d⟩ :
        ↥(coreMod 8)) *
        ⟨Multiplicative.ofAdd (B5FinS8.pv a e + B5FinS8.pv b f), mem_pv2 a e b f⟩ : ↥(coreMod 8)) =
        (⟨Multiplicative.ofAdd (B5FinS8.pv c e + B5FinS8.pv d f), mem_pv2 c e d f⟩) := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      funext i
      change (B5FinS8.pv a c + B5FinS8.pv b d) i + (B5FinS8.pv a e + B5FinS8.pv b f) i =
        (B5FinS8.pv c e + B5FinS8.pv d f) i
      simp only [B5FinS8.pv, Pi.add_apply]
      exact zmod2_six _ _ _ _ _ _
    rw [e1] at h3
    refine mk_ne_one ?_ h3
    exact Or.inr (wt_pv2 c e d f (Ne.symm hec) (Ne.symm hdc) (Ne.symm hfc) hed (Ne.symm hfe)
      (Ne.symm hfd))
  have hR : 3 ≤ Nat.card (theta σ).range := by
    classical
    have hsub : ({1, theta σ (QuotientGroup.mk (pe a c)), theta σ (QuotientGroup.mk (pe a e))} :
        Finset D8) ⊆ ((theta σ).range : Set D8).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Set.mem_toFinset]
      rcases hx with rfl | rfl | rfl
      · exact (theta σ).range.one_mem
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨n1.symm, n2.symm⟩),
      Finset.card_insert_of_notMem (by simpa using n12), Finset.card_singleton] at h3
    have h4 : ((theta σ).range : Set D8).toFinset.card = Nat.card (theta σ).range := by
      rw [← Nat.card_eq_card_toFinset]
      rfl
    omega
  have hcard : Nat.card D8 = Nat.card (theta σ).range * Nat.card (theta σ).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (theta σ).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (theta σ)).toEquiv]
  rw [ker_theta, S126L20.card_D8_eq] at hcard
  obtain ⟨k, hk⟩ := card_eq_pow_of_le (H := (theta σ).range)
  obtain ⟨m, hm⟩ := card_eq_pow_of_le (H := fix1 σ)
  rw [hk, hm, ← pow_add, show (64 : ℕ) = 2 ^ 6 by norm_num] at hcard
  have hkm := Nat.pow_right_injective (le_refl 2) hcard
  rw [hk] at hR
  have hk2 : 2 ≤ k := by
    by_contra hc
    interval_cases k <;> simp at hR
  rw [hm]
  calc 2 ^ m ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 16 := by norm_num

theorem card_le_eight_of_fpf {B : Subgroup (Perm (Fin 8))}
    (hB : ∀ σ ∈ B, σ ≠ 1 → ∀ i, σ i ≠ i) : Nat.card B ≤ 8 := by
  have hinj : Function.Injective fun σ : ↥B => (σ : Perm (Fin 8)) 0 := by
    intro σ τ h
    by_contra hne
    have h1 : (τ : Perm (Fin 8))⁻¹ * σ ≠ 1 := fun h' => hne (Subtype.ext (by
      have := inv_mul_eq_one.1 h'
      exact this.symm))
    apply hB _ (B.mul_mem (B.inv_mem τ.2) σ.2) h1 0
    change (τ : Perm (Fin 8))⁻¹ ((σ : Perm (Fin 8)) 0) = 0
    simp only at h
    rw [h, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_fin] at h

theorem card_fixD_le_eight {B : Subgroup (Perm (Fin 8))}
    (hB : ∀ σ ∈ B, σ ≠ 1 → ∀ i, σ i ≠ i) (hinv : ∀ σ ∈ B, σ * σ = 1) {σ₁ σ₂ : Perm (Fin 8)}
    (h₁ : σ₁ ∈ B) (h₂ : σ₂ ∈ B) (h₁1 : σ₁ ≠ 1) (h₂1 : σ₂ ≠ 1) (h12 : σ₁ ≠ σ₂) :
    Nat.card (fixD B) ≤ 8 := by
  have hinv' : ∀ σ ∈ B, ∀ i, σ (σ i) = i := fun σ hσ i => by
    rw [← Perm.mul_apply, hinv σ hσ, Perm.one_apply]
  set a : Fin 8 := 0
  have ha1 : σ₁ a ≠ a := hB σ₁ h₁ h₁1 a
  have ha2 : σ₂ a ≠ a := hB σ₂ h₂ h₂1 a
  have ha12 : σ₂ a ≠ σ₁ a := by
    intro h
    have h3 : σ₁⁻¹ * σ₂ ≠ 1 := fun h' => h12 (inv_mul_eq_one.1 h')
    apply hB _ (B.mul_mem (B.inv_mem h₁) h₂) h3 a
    rw [Perm.mul_apply, h, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
  have hb1 : σ₂ (σ₁ a) ≠ a := by
    intro h
    have h3 : σ₂ * σ₁ ≠ 1 := by
      intro h'
      apply h12
      calc σ₁ = σ₂ * σ₁ * σ₁ := by rw [h', one_mul]
        _ = σ₂ := by rw [mul_assoc, hinv σ₁ h₁, mul_one]
    exact hB _ (B.mul_mem h₂ h₁) h3 a (by rw [Perm.mul_apply, h])
  have hb2 : σ₂ (σ₁ a) ≠ σ₁ a := hB σ₂ h₂ h₂1 (σ₁ a)
  have hb3 : σ₂ (σ₁ a) ≠ σ₂ a := fun h => ha1 (σ₂.injective h)
  set x : D8 := QuotientGroup.mk (pe a (σ₁ a)) with hx
  have hx1 : x ∈ fix1 σ₁ := by
    rw [mem_fix1, hx, dAct_pe, hinv' σ₁ h₁, pe_comm]
  have hx2 : x ∉ fix1 σ₂ := by
    rw [mem_fix1, hx, dAct_pe]
    exact pe_mk_ne (Ne.symm hb3) ha2 ha12 hb1 hb2 (Ne.symm ha1)
  have hle : fixD B ≤ fix1 σ₁ ⊓ fix1 σ₂ := fun y hy =>
    ⟨(mem_fixD.1 hy) σ₁ h₁, (mem_fixD.1 hy) σ₂ h₂⟩
  have hlt : fix1 σ₁ ⊓ fix1 σ₂ ≠ fix1 σ₁ := fun h => hx2 (by
    rw [← h] at hx1
    exact hx1.2)
  have h16 := card_fix1_le (hB σ₁ h₁ h₁1) (hinv' σ₁ h₁)
  have hdvd := Subgroup.card_dvd_of_le (inf_le_left : fix1 σ₁ ⊓ fix1 σ₂ ≤ fix1 σ₁)
  have hne : Nat.card ↥(fix1 σ₁ ⊓ fix1 σ₂) ≠ Nat.card (fix1 σ₁) := fun h =>
    hlt (Subgroup.eq_of_le_of_card_ge inf_le_left h.ge)
  obtain ⟨q, hq⟩ := hdvd
  have hq2 : 2 ≤ q := by
    by_contra hc
    interval_cases q
    · rw [mul_zero] at hq
      exact absurd hq (Nat.card_pos (α := fix1 σ₁)).ne'
    · rw [mul_one] at hq
      exact absurd hq.symm hne
  calc Nat.card (fixD B) ≤ Nat.card ↥(fix1 σ₁ ⊓ fix1 σ₂) := Subgroup.card_le_of_le hle
    _ ≤ 8 := by nlinarith

end S126L20a

end CFSG.Quasithin.H13
