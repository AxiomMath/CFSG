module

public import CFSG.Quasithin.Vol2.Ch11SecO6K

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.Quasithin
open scoped IsMulCommutative

variable {X : Type} [Group X] [Finite X] (r : ℕ) [Fact r.Prime]

theorem linV_conj_ofMul (z : X) (d : ↥(CFSG.pCore r X)) :
    linV r (MulAut.conj z)
        (Additive.ofMul (d : ↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X))) =
      Additive.ofMul ((⟨z * d * z⁻¹, Subgroup.Normal.conj_mem CFSG.pCore_normal _ d.2 z⟩ :
        ↥(CFSG.pCore r X)) : ↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) := by
  rw [linV_ofMul, autV_mk]
  rfl

theorem exists_zpow_of_comm
    (hV : Nat.card (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) ≤ r ^ 2)
    (hab : ∀ d ∈ CFSG.pCore r X, ∀ e ∈ CFSG.pCore r X, d * e = e * d)
    (hHC : ∀ u ∈ CFSG.pCore r X, u ∉ frattiniIn (CFSG.pCore r X) → ∀ b : ℤ, u ^ b = 1 →
      ∀ e ∈ CFSG.pCore r X, e ^ b = 1)
    (hna : ∃ x y : X, ¬ ActsTriviallyOnFrattiniQuotient (CFSG.pCore r X) (x * y * x⁻¹ * y⁻¹))
    {σ : MulAut X} (hσ : ∀ x : X, ∀ d ∈ CFSG.pCore r X, σ (x * d * x⁻¹) = x * σ d * x⁻¹) :
    ∃ a : ℤ, ∀ d ∈ CFSG.pCore r X, σ d = d ^ a := by
  set P := CFSG.pCore r X with hPdef
  have hconj : ∀ z : X, ∀ d ∈ P, z * d * z⁻¹ ∈ P := fun z d hd =>
    Subgroup.Normal.conj_mem CFSG.pCore_normal d hd z
  have hLmul : ∀ a b : X, linV r (MulAut.conj (a * b)) =
      linV r (MulAut.conj a) * linV r (MulAut.conj b) := fun a b => by
    rw [map_mul, linV_mul]
  have hL1 : linV r (MulAut.conj (1 : X)) = 1 := by rw [map_one, linV_one]
  obtain ⟨x, y, hxy⟩ := hna
  have hne : linV r (MulAut.conj x) * linV r (MulAut.conj y) ≠
      linV r (MulAut.conj y) * linV r (MulAut.conj x) := by
    intro h
    apply hxy
    rw [actsTrivially_iff, actsScalar_iff_linV, Nat.cast_one, one_smul, hLmul, hLmul, hLmul, h]
    calc linV r (MulAut.conj y) * linV r (MulAut.conj x) * linV r (MulAut.conj x⁻¹) *
          linV r (MulAut.conj y⁻¹)
        = linV r (MulAut.conj y) * linV r (MulAut.conj (x * x⁻¹)) *
          linV r (MulAut.conj y⁻¹) := by rw [hLmul x, mul_assoc (linV r (MulAut.conj y))]
      _ = 1 := by rw [mul_inv_cancel, hL1, mul_one, ← hLmul, mul_inv_cancel, hL1]
  obtain ⟨vb, hv⟩ : ∃ vb, LinearIndependent (ZMod r) ![vb, linV r (MulAut.conj x) vb] := by
    by_contra hall
    push Not at hall
    obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hall
    apply hne
    rw [hc, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hspan : Submodule.span (ZMod r) (Set.range ![vb, linV r (MulAut.conj x) vb]) = ⊤ := by
    have h2 := hv.fintype_card_le_finrank
    rw [Fintype.card_fin] at h2
    refine hv.span_eq_top_of_card_eq_finrank' ?_
    rw [Fintype.card_fin]
    exact le_antisymm h2 (finrank_le_two r hV)
  obtain ⟨v₀, hv₀⟩ := QuotientGroup.mk_surjective (Additive.toMul vb)
  have hvb : vb = Additive.ofMul ((v₀ : ↥P ⧸ frattini ↥P)) := by rw [hv₀]; rfl
  have hvP : (v₀ : X) ∈ P := v₀.2
  have hwP : x * v₀ * x⁻¹ ∈ P := hconj x _ hvP
  have hLv : linV r (MulAut.conj x) vb =
      Additive.ofMul ((⟨x * v₀ * x⁻¹, hwP⟩ : ↥P) : ↥P ⧸ frattini ↥P) := by
    rw [hvb]
    exact linV_conj_ofMul r x v₀
  have hsmul : ∀ (q : ↥P ⧸ frattini ↥P) (c : ZMod r),
      c • Additive.ofMul q = Additive.ofMul (q ^ c.val) := by
    intro q c
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul]
    exact (ofMul_pow c.val q).symm
  have hgen : ∀ d (hd : d ∈ P), ∃ m n : ℕ,
      (v₀ ^ m * (⟨x * v₀ * x⁻¹, hwP⟩ : ↥P) ^ n)⁻¹ * ⟨d, hd⟩ ∈ frattini ↥P := by
    intro d hd
    have hmem : Additive.ofMul ((⟨d, hd⟩ : ↥P) : ↥P ⧸ frattini ↥P) ∈
        Submodule.span (ZMod r) (Set.range ![vb, linV r (MulAut.conj x) vb]) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod r)).mp hmem
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
    rw [hLv, hvb, hsmul, hsmul, ← ofMul_mul] at hc
    have hc' := Additive.ofMul.injective hc
    refine ⟨(c 0).val, (c 1).val, ?_⟩
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul,
      QuotientGroup.eq] at hc'
    exact hc'
  set v : X := (v₀ : X) with hvdef
  set w : X := x * v * x⁻¹ with hwdef
  set H := Subgroup.closure ({v, w} : Set X) with hHdef
  have hvH : v ∈ H := Subgroup.subset_closure (Set.mem_insert v _)
  have hwH : w ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem v rfl)
  have : Fact (IsPGroup r ↥P) := ⟨CFSG.pCore_isPGroup⟩
  have hPH : ∀ d ∈ P, d ∈ H := by
    have hsup : H.subgroupOf P ⊔ frattini ↥P = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨d, hd⟩ -
      obtain ⟨m, n, hmn⟩ := hgen d hd
      have e : (⟨d, hd⟩ : ↥P) = (v₀ ^ m * (⟨w, hwP⟩ : ↥P) ^ n) *
          ((v₀ ^ m * (⟨w, hwP⟩ : ↥P) ^ n)⁻¹ * ⟨d, hd⟩) := by group
      rw [e]
      refine Subgroup.mul_mem_sup ?_ hmn
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, SubgroupClass.coe_pow,
        SubgroupClass.coe_pow]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hvH m) (Subgroup.pow_mem _ hwH n)
    have htop := CFSG.lemma_1_7_a (R := ↥P) (p := r) _ hsup
    intro d hd
    have h1 : (⟨d, hd⟩ : ↥P) ∈ H.subgroupOf P := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp h1
  have hvw : Commute v w := hab v hvP w hwP
  obtain ⟨a, b, hσv⟩ := exists_zpow_of_mem_closure_pair hvw (hPH _ (map_mem_pCore r σ hvP))
  let K : Subgroup X :=
    { carrier := {d | d ∈ P ∧ σ d = d ^ a * (x * d * x⁻¹) ^ b}
      mul_mem' := fun {d e} hd he => by
        obtain ⟨hdP, hd⟩ := hd
        obtain ⟨heP, he⟩ := he
        refine ⟨mul_mem hdP heP, ?_⟩
        have hD := hconj x d hdP
        have hE := hconj x e heP
        have c1 : Commute d e := hab d hdP e heP
        have c2 : Commute (x * d * x⁻¹) (x * e * x⁻¹) := hab _ hD _ hE
        have c3 : Commute (e ^ a) ((x * d * x⁻¹) ^ b) := Commute.zpow_zpow (hab e heP _ hD) a b
        rw [map_mul, hd, he, c1.mul_zpow,
          show x * (d * e) * x⁻¹ = (x * d * x⁻¹) * (x * e * x⁻¹) by group, c2.mul_zpow]
        calc d ^ a * (x * d * x⁻¹) ^ b * (e ^ a * (x * e * x⁻¹) ^ b)
            = d ^ a * ((x * d * x⁻¹) ^ b * e ^ a) * (x * e * x⁻¹) ^ b := by group
          _ = d ^ a * (e ^ a * (x * d * x⁻¹) ^ b) * (x * e * x⁻¹) ^ b := by rw [← c3.eq]
          _ = d ^ a * e ^ a * ((x * d * x⁻¹) ^ b * (x * e * x⁻¹) ^ b) := by group
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := fun {d} hd => by
        obtain ⟨hdP, hd⟩ := hd
        refine ⟨inv_mem hdP, ?_⟩
        have c3 : Commute (d ^ a) ((x * d * x⁻¹) ^ b) :=
          Commute.zpow_zpow (hab d hdP _ (hconj x d hdP)) a b
        rw [map_inv, hd, mul_inv_rev, show x * d⁻¹ * x⁻¹ = (x * d * x⁻¹)⁻¹ by group, inv_zpow,
          inv_zpow]
        exact c3.inv_inv.eq.symm }
  have hvK : v ∈ K := ⟨hvP, hσv⟩
  have hwK : w ∈ K := by
    refine ⟨hwP, ?_⟩
    have hσw : σ w = x * σ v * x⁻¹ := hσ x v hvP
    have e1 : w ^ a = x * v ^ a * x⁻¹ := conj_zpow
    have e2 : (x * w * x⁻¹) ^ b = x * w ^ b * x⁻¹ := conj_zpow
    rw [hσw, hσv, e1, e2]
    group
  have hPK : ∀ d ∈ P, d ∈ K := by
    have hHK : H ≤ K := by
      rw [hHdef, Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | hz
      · exact hvK
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hwK
    exact fun d hd => hHK (hPH d hd)
  have hσP : ∀ d ∈ P, σ d = d ^ a * (x * d * x⁻¹) ^ b := fun d hd => (hPK d hd).2
  obtain ⟨eb, heb⟩ : ∃ eb, (linV r (MulAut.conj x) * linV r (MulAut.conj y)) eb ≠
      (linV r (MulAut.conj y) * linV r (MulAut.conj x)) eb := by
    by_contra hall
    push Not at hall
    exact hne (LinearMap.ext hall)
  obtain ⟨d₀, hd₀⟩ := QuotientGroup.mk_surjective (Additive.toMul eb)
  have heb' : eb = Additive.ofMul ((d₀ : ↥P ⧸ frattini ↥P)) := by rw [hd₀]; rfl
  have hdP : (d₀ : X) ∈ P := d₀.2
  have hyd := hconj y _ hdP
  have hxd := hconj x _ hdP
  have hpP : x * (y * d₀ * y⁻¹) * x⁻¹ ∈ P := hconj x _ hyd
  have hqP : y * (x * d₀ * x⁻¹) * y⁻¹ ∈ P := hconj y _ hxd
  have hpq : (x * (y * d₀ * y⁻¹) * x⁻¹) ^ b = (y * (x * d₀ * x⁻¹) * y⁻¹) ^ b := by
    have h1 := hσ y _ hdP
    rw [hσP _ hyd, hσP _ hdP] at h1
    have e1 : (y * (d₀ : X) * y⁻¹) ^ a = y * (d₀ : X) ^ a * y⁻¹ := conj_zpow
    have e2 : (y * (x * (d₀ : X) * x⁻¹) * y⁻¹) ^ b = y * (x * (d₀ : X) * x⁻¹) ^ b * y⁻¹ :=
      conj_zpow
    have h2 : y * ((d₀ : X) ^ a * (x * d₀ * x⁻¹) ^ b) * y⁻¹ =
        (y * d₀ * y⁻¹) ^ a * (y * (x * d₀ * x⁻¹) * y⁻¹) ^ b := by
      rw [e1, e2]
      group
    rw [h2] at h1
    exact mul_left_cancel h1
  have hu : (x * (y * d₀ * y⁻¹) * x⁻¹)⁻¹ * (y * (x * d₀ * x⁻¹) * y⁻¹) ∉ frattiniIn P := by
    intro hu
    apply heb
    have hu2 : (⟨_, hpP⟩ : ↥P)⁻¹ * ⟨_, hqP⟩ ∈ frattini ↥P := by
      obtain ⟨z, hz, hze⟩ := hu
      have e : z = (⟨_, hpP⟩ : ↥P)⁻¹ * ⟨_, hqP⟩ := Subtype.ext hze
      rw [← e]
      exact hz
    have hpq' := QuotientGroup.eq.mpr hu2
    rw [heb', Module.End.mul_apply, Module.End.mul_apply, linV_conj_ofMul r y d₀,
      linV_conj_ofMul r x, linV_conj_ofMul r x d₀, linV_conj_ofMul r y]
    exact congrArg Additive.ofMul hpq'
  have hall := hHC _ (mul_mem (inv_mem hpP) hqP) hu b (by
    have c : Commute (x * (y * d₀ * y⁻¹) * x⁻¹)⁻¹ (y * (x * d₀ * x⁻¹) * y⁻¹) :=
      Commute.inv_left (hab _ hpP _ hqP)
    rw [c.mul_zpow, inv_zpow, hpq, inv_mul_cancel])
  refine ⟨a, fun d hd => ?_⟩
  rw [hσP d hd, hall _ (hconj x d hd), mul_one]

end CFSG.Quasithin.Vol2.Ch11.O6
