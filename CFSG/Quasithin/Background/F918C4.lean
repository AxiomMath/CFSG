module

public import CFSG.Quasithin.Background.F918C2

public section

namespace CFSG.Quasithin

open Equiv Equiv.Perm CFSG.Assembly.LowTwoRank

namespace A6Twist

theorem order3_types : ∀ y : Perm (Fin 6), y ^ 3 = 1 → y ≠ 1 →
    ((∃ a b : Fin 6, a ≠ b ∧ y a = a ∧ y b = b) ∨ ∀ a : Fin 6, y a ≠ a) := by
  decide +kernel

def y3a : Perm (Fin 6) := swap 0 1 * swap 1 2

def y3b : Perm (Fin 6) := swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5)

theorem conj3a : ∀ y : Perm (Fin 6), y ^ 3 = 1 → y ≠ 1 →
    (∃ a b : Fin 6, a ≠ b ∧ y a = a ∧ y b = b) →
    ∃ c : Perm (Fin 6), sign c = 1 ∧ c * y3a * c⁻¹ = y := by
  decide +kernel

theorem conj3b : ∀ y : Perm (Fin 6), y ^ 3 = 1 → y ≠ 1 → (∀ a : Fin 6, y a ≠ a) →
    ∃ c : Perm (Fin 6), sign c = 1 ∧ c * y3b * c⁻¹ = y := by
  decide +kernel

theorem fixfree_vec : ∀ y : Perm (Fin 6), y ^ 3 = 1 → y ≠ 1 → (∀ a : Fin 6, y a ≠ a) →
    ∀ m : Fin 6 → ZMod 2, ∑ i, m i = 0 →
      ((fun i => m (y⁻¹ i)) + m = 0 ∨ (fun i => m (y⁻¹ i)) + m = fun _ => 1) →
        (m = 0 ∨ m = fun _ => 1) := by
  decide +kernel

theorem faithful_D6 : ∀ y : Perm (Fin 6),
    (∀ m : Fin 6 → ZMod 2, ∑ i, m i = 0 →
      ((fun i => m (y⁻¹ i)) + m = 0 ∨ (fun i => m (y⁻¹ i)) + m = fun _ => 1)) → y = 1 := by
  decide +kernel

section Module

open G6

variable {W : Type} [CommGroup W]

private theorem zpow_eq_one_or_self {M : Type*} [CommGroup M] {a : M} (hsq : a * a = 1) (k : ℤ) :
    a ^ k = 1 ∨ a ^ k = a := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hsq
  induction k using Int.induction_on with
  | zero => left; simp
  | succ n ih =>
    rw [zpow_add_one]
    rcases ih with h1 | h1
    · right; rw [h1, one_mul]
    · left; rw [h1, hsq]
  | pred n ih =>
    rw [zpow_sub_one, hinv]
    rcases ih with h1 | h1
    · right; rw [h1, one_mul]
    · left; rw [h1, hsq]

private theorem mem_ker_iff {m : PermMod 6} :
    m ∈ Subgroup.zpowers (allOnes 6) ↔ m = 1 ∨ m = allOnes 6 := by
  have hsq : allOnes 6 * allOnes 6 = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    show (1 : ZMod 2) + 1 = 0
    decide
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    exact zpow_eq_one_or_self hsq k
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

def FixesNonzero (V Z : Subgroup W) (x : MulAut W) : Prop :=
  ∃ v ∈ V, v ∉ Z ∧ x v * v⁻¹ ∈ Z

theorem fixesNonzero_conj {V Z : Subgroup W} {x τ : MulAut W} (hV : V.map τ.toMonoidHom = V)
    (hZ : Z.map τ.toMonoidHom = Z) (h : FixesNonzero V Z x) : FixesNonzero V Z (τ * x * τ⁻¹) := by
  obtain ⟨v, hvV, hvZ, hx⟩ := h
  refine ⟨τ v, ?_, ?_, ?_⟩
  · have : τ v ∈ V.map τ.toMonoidHom := ⟨v, hvV, rfl⟩
    rwa [hV] at this
  · intro h
    have h1 : τ v ∈ Z.map τ.toMonoidHom := by rwa [hZ]
    obtain ⟨w, hw, hwv⟩ := h1
    have : w = v := τ.injective hwv
    exact hvZ (this ▸ hw)
  · have : τ (x v * v⁻¹) ∈ Z.map τ.toMonoidHom := ⟨_, hx, rfl⟩
    rw [hZ] at this
    simpa [MulAut.mul_apply] using this

private theorem neg_eq_self_fun (f : Fin 6 → ZMod 2) : -f = f := by
  funext i
  have : ∀ x : ZMod 2, -x = x := by decide
  exact this _

theorem mk_eq_iff (m m' : ↥(coreMod 6)) :
    (QuotientGroup.mk m : ↥(coreMod 6) ⧸
        ((Subgroup.zpowers (allOnes 6) ⊓ coreMod 6).subgroupOf (coreMod 6))) = QuotientGroup.mk m' ↔
      (Multiplicative.toAdd (m : PermMod 6) + Multiplicative.toAdd (m' : PermMod 6) = 0 ∨
        Multiplicative.toAdd (m : PermMod 6) + Multiplicative.toAdd (m' : PermMod 6) = fun _ => 1) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hmem : ((m⁻¹ * m' : ↥(coreMod 6)) : PermMod 6) ∈ Subgroup.zpowers (allOnes 6) ⊓ coreMod 6 ↔
      ((m⁻¹ * m' : ↥(coreMod 6)) : PermMod 6) ∈ Subgroup.zpowers (allOnes 6) :=
    ⟨fun h => h.1, fun h => ⟨h, (m⁻¹ * m' : ↥(coreMod 6)).2⟩⟩
  rw [hmem, mem_ker_iff]
  have e : ((m⁻¹ * m' : ↥(coreMod 6)) : PermMod 6) = (m : PermMod 6)⁻¹ * (m' : PermMod 6) := rfl
  rw [e]
  constructor
  · rintro (h | h)
    · left
      have := congrArg Multiplicative.toAdd h
      rw [toAdd_mul, toAdd_inv, toAdd_one, neg_eq_self_fun] at this
      exact this
    · right
      have := congrArg Multiplicative.toAdd h
      rw [toAdd_mul, toAdd_inv, neg_eq_self_fun] at this
      exact this
  · rintro (h | h)
    · left
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, toAdd_one, neg_eq_self_fun]
      exact h
    · right
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, neg_eq_self_fun]
      exact h

def pairVec (a b : Fin 6) : PermMod 6 := Multiplicative.ofAdd (Pi.single a 1 + Pi.single b 1)

theorem pairVec_mem_core (a b : Fin 6) : pairVec a b ∈ coreMod 6 := by
  rw [mem_coreMod]
  have : ∑ i, (Pi.single a (1 : ZMod 2) + Pi.single b (1 : ZMod 2) : Fin 6 → ZMod 2) i = 0 := by
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_pi_single', Finset.mem_univ, ite_true]
    decide
  simpa [pairVec] using this

theorem permAct_pairVec {y : Perm (Fin 6)} {a b : Fin 6} (ha : y a = a) (hb : y b = b) :
    permAct 6 y (pairVec a b) = pairVec a b := by
  apply Multiplicative.toAdd.injective
  funext i
  have h1 : (y⁻¹ i = a) ↔ (i = a) := by rw [Equiv.Perm.inv_eq_iff_eq, ha]
  have h2 : (y⁻¹ i = b) ↔ (i = b) := by rw [Equiv.Perm.inv_eq_iff_eq, hb]
  simp only [permAct_apply, pairVec, toAdd_ofAdd, Pi.add_apply, Pi.single_apply, h1, h2]

theorem pairVec_ne_one {a b : Fin 6} (h : a ≠ b) : pairVec a b ≠ 1 := by
  intro h1
  have := congrFun (congrArg Multiplicative.toAdd h1) a
  simp [pairVec, h] at this

theorem pairVec_ne_allOnes (a b : Fin 6) : pairVec a b ≠ allOnes 6 := by
  have hc : ∀ a b : Fin 6, ∃ c : Fin 6, c ≠ a ∧ c ≠ b := by decide
  obtain ⟨c, hca, hcb⟩ := hc a b
  intro h1
  have := congrFun (congrArg Multiplicative.toAdd h1) c
  simp [pairVec, allOnes, hca, hcb] at this

theorem map_symm_eq {V : Subgroup W} {τ : MulAut W} (h : V.map τ.toMonoidHom = V) :
    V.map (τ⁻¹).toMonoidHom = V := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have h1 : v ∈ V.map τ.toMonoidHom := by rwa [h]
    obtain ⟨u, hu, rfl⟩ := h1
    simpa using hu
  · intro hw
    have h1 : τ w ∈ V.map τ.toMonoidHom := ⟨w, hw, rfl⟩
    rw [h] at h1
    exact ⟨τ w, h1, by simp⟩

variable {L : Subgroup (MulAut W)} {V Z : Subgroup W} {π : ↥(alternatingGroup (Fin 6)) →* ↥L}

theorem toAdd_act (y : ↥(alternatingGroup (Fin 6))) (z : (FFModel.altDn 6).Amb) :
    Multiplicative.toAdd ((FFModel.altDn 6).act y z) =
      fun i => Multiplicative.toAdd z ((y : Perm (Fin 6))⁻¹ i) := rfl

theorem pi_injective (hπ : (FFModel.altDn 6).RealizesVia L V Z π) : Function.Injective π := by
  obtain ⟨-, -, -, hVinv, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  rw [injective_iff_map_eq_one]
  intro y hy
  have key : ∀ M : Fin 6 → ZMod 2, ∑ i, M i = 0 →
      ((fun i => M ((y : Perm (Fin 6))⁻¹ i)) + M = 0 ∨
        (fun i => M ((y : Perm (Fin 6))⁻¹ i)) + M = fun _ => 1) := by
    intro M hM
    set m : ↥(FFModel.altDn 6).sec := ⟨Multiplicative.ofAdd M, hM⟩ with hm
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
    have huV : ((π y : ↥L) : MulAut W) (u : W) ∈ V := hVinv (π y) u u.2
    have hm' : (FFModel.altDn 6).act y (m : (FFModel.altDn 6).Amb) ∈ (FFModel.altDn 6).sec :=
      permAct_mem_coreMod (y : Perm (Fin 6)) m.2
    have h1 := hβe y u m huV hm' hu
    have e : (⟨((π y : ↥L) : MulAut W) (u : W), huV⟩ : ↥V) = u := by
      apply Subtype.ext
      show ((π y : ↥L) : MulAut W) (u : W) = (u : W)
      have hy' : (π y : ↥L) = 1 := hy
      rw [hy']
      rfl
    have h1' := hu.symm.trans ((congrArg β e.symm).trans h1)
    have h2 := (mk_eq_iff m ⟨(FFModel.altDn 6).act y (m : (FFModel.altDn 6).Amb), hm'⟩).1 h1'
    have h2' : (M + fun i => M ((y : Perm (Fin 6))⁻¹ i)) = 0 ∨
        (M + fun i => M ((y : Perm (Fin 6))⁻¹ i)) = fun _ => 1 := h2
    rcases h2' with h | h
    · left; rw [add_comm]; exact h
    · right; rw [add_comm]; exact h
  exact Subtype.ext (faithful_D6 _ (fun M hM => by simpa using key M hM))

theorem fixesNonzero_of_two_fixed (hπ : (FFModel.altDn 6).RealizesVia L V Z π)
    {y : ↥(alternatingGroup (Fin 6))} {a b : Fin 6} (hab : a ≠ b) (ha : (y : Perm (Fin 6)) a = a)
    (hb : (y : Perm (Fin 6)) b = b) : FixesNonzero V Z ((π y : ↥L) : MulAut W) := by
  obtain ⟨-, -, -, hVinv, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  set m : ↥(FFModel.altDn 6).sec := ⟨pairVec a b, pairVec_mem_core a b⟩ with hm
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
  have huV : ((π y : ↥L) : MulAut W) (u : W) ∈ V := hVinv (π y) u u.2
  have hm' : (FFModel.altDn 6).act y (m : (FFModel.altDn 6).Amb) ∈ (FFModel.altDn 6).sec :=
    permAct_mem_coreMod (y : Perm (Fin 6)) m.2
  have h1 := hβe y u m huV hm' hu
  have e : (⟨(FFModel.altDn 6).act y (m : (FFModel.altDn 6).Amb), hm'⟩ : ↥(FFModel.altDn 6).sec) = m :=
    Subtype.ext (permAct_pairVec ha hb)
  have h1' : β ⟨((π y : ↥L) : MulAut W) (u : W), huV⟩ = β u :=
    h1.trans ((congrArg QuotientGroup.mk e).trans hu.symm)
  refine ⟨(u : W), u.2, fun huZ => ?_, ?_⟩
  · have h2 : β u = 1 := (hβk u).2 huZ
    rw [hu, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    have h3 : pairVec a b ∈ Subgroup.zpowers (allOnes 6) := h2.1
    rcases mem_ker_iff.1 h3 with h4 | h4
    · exact pairVec_ne_one hab h4
    · exact pairVec_ne_allOnes a b h4
  · have h2 : β (⟨((π y : ↥L) : MulAut W) (u : W), huV⟩ * u⁻¹) = 1 := by
      rw [map_mul, map_inv, h1', mul_inv_cancel]
    exact (hβk _).1 h2

theorem not_fixesNonzero_of_fixedfree (hπ : (FFModel.altDn 6).RealizesVia L V Z π)
    {y : ↥(alternatingGroup (Fin 6))} (h3 : (y : Perm (Fin 6)) ^ 3 = 1) (h1 : (y : Perm (Fin 6)) ≠ 1)
    (hfree : ∀ a : Fin 6, (y : Perm (Fin 6)) a ≠ a) : ¬ FixesNonzero V Z ((π y : ↥L) : MulAut W) := by
  obtain ⟨-, -, -, hVinv, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  rintro ⟨v, hvV, hvZ, hz⟩
  set v' : ↥V := ⟨v, hvV⟩ with hv'
  obtain ⟨m, hmv⟩ := QuotientGroup.mk_surjective (β v')
  have huV : ((π y : ↥L) : MulAut W) v ∈ V := hVinv (π y) v' hvV
  have hm' : (FFModel.altDn 6).act y (m : (FFModel.altDn 6).Amb) ∈ (FFModel.altDn 6).sec :=
    permAct_mem_coreMod (y : Perm (Fin 6)) m.2
  have h1' := hβe y v' m huV hm' hmv.symm
  have hz' : (⟨((π y : ↥L) : MulAut W) v * v⁻¹, V.mul_mem huV (V.inv_mem hvV)⟩ : ↥V) ∈
      β.ker := by
    rw [MonoidHom.mem_ker, hβk]
    exact hz
  have h2 : β ⟨((π y : ↥L) : MulAut W) v, huV⟩ = β v' := by
    have e : (⟨((π y : ↥L) : MulAut W) v, huV⟩ : ↥V) =
        ⟨((π y : ↥L) : MulAut W) v * v⁻¹, V.mul_mem huV (V.inv_mem hvV)⟩ * v' :=
      Subtype.ext (by simp [hv'])
    rw [e, map_mul, MonoidHom.mem_ker.1 hz', one_mul]
  have h1'' := hmv.trans (h2.symm.trans h1')
  have h3' := (mk_eq_iff m ⟨(FFModel.altDn 6).act y (m : (FFModel.altDn 6).Amb), hm'⟩).1 h1''
  have h4 := fixfree_vec (y : Perm (Fin 6)) h3 h1 hfree (Multiplicative.toAdd (m.1 : PermMod 6)) m.2
    (h3'.imp (fun h => (add_comm _ _).trans h) (fun h => (add_comm _ _).trans h))
  apply hvZ
  apply (hβk v').1
  rw [← hmv, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine ⟨mem_ker_iff.2 ?_, m.2⟩
  rcases h4 with h5 | h5
  · left
    exact Multiplicative.toAdd.injective h5
  · right
    exact Multiplicative.toAdd.injective h5

theorem alt6_class_stable (hnat : AlternatingNatural L V Z 6) {σ : MulAut W}
    (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) (hσV : V.map σ.toMonoidHom = V)
    (hσZ : Z.map σ.toMonoidHom = Z) :
    ∀ x ∈ L, x ^ 3 = 1 → ∃ l ∈ L, l * x * l⁻¹ = σ * x * σ⁻¹ := by
  obtain ⟨π, hπ⟩ : ∃ π : ↥(alternatingGroup (Fin 6)) →* ↥L,
      (FFModel.altDn 6).RealizesVia L V Z π := hnat
  have hinj := pi_injective hπ
  have hsurj : Function.Surjective π := hπ.1
  intro x hx hx3
  by_cases hx1 : x = 1
  · exact ⟨1, L.one_mem, by simp [hx1]⟩
  have hx'L : σ * x * σ⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hσ x).1 hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  obtain ⟨y', hy'⟩ := hsurj ⟨σ * x * σ⁻¹, hx'L⟩
  have hxe : ((π y : ↥L) : MulAut W) = x := congrArg Subtype.val hy
  have hxe' : ((π y' : ↥L) : MulAut W) = σ * x * σ⁻¹ := congrArg Subtype.val hy'
  have hx'3 : (σ * x * σ⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; simp
  have hx'1 : σ * x * σ⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have := congrArg (fun z => σ⁻¹ * z * σ) h
    simpa [mul_assoc] using this
  have hy3 : y ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    apply Subtype.ext
    simpa [hxe] using hx3
  have hy'3 : y' ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    apply Subtype.ext
    simpa [hxe'] using hx'3
  have hy1 : (y : Perm (Fin 6)) ≠ 1 := by
    intro h
    apply hx1
    have h1 : y = 1 := Subtype.ext h
    rw [← hxe, h1, map_one]
    rfl
  have hy'1 : (y' : Perm (Fin 6)) ≠ 1 := by
    intro h
    apply hx'1
    have h1 : y' = 1 := Subtype.ext h
    rw [← hxe', h1, map_one]
    rfl
  have hy3p : (y : Perm (Fin 6)) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
  have hy'3p : (y' : Perm (Fin 6)) ^ 3 = 1 := by simpa using congrArg Subtype.val hy'3
  have hfn : FixesNonzero V Z x → FixesNonzero V Z (σ * x * σ⁻¹) := fixesNonzero_conj hσV hσZ
  have hfn' : FixesNonzero V Z (σ * x * σ⁻¹) → FixesNonzero V Z x := by
    intro h
    have := fixesNonzero_conj (τ := σ⁻¹) (map_symm_eq hσV) (map_symm_eq hσZ) h
    simpa [mul_assoc] using this
  have hpos : ∀ (z : ↥(alternatingGroup (Fin 6))) (x₀ : MulAut W), ((π z : ↥L) : MulAut W) = x₀ →
      (∃ a b : Fin 6, a ≠ b ∧ (z : Perm (Fin 6)) a = a ∧ (z : Perm (Fin 6)) b = b) →
      FixesNonzero V Z x₀ := by
    rintro z x₀ rfl ⟨a, b, hab, ha, hb⟩
    exact fixesNonzero_of_two_fixed hπ hab ha hb
  have hneg : ∀ (z : ↥(alternatingGroup (Fin 6))) (x₀ : MulAut W), ((π z : ↥L) : MulAut W) = x₀ →
      (z : Perm (Fin 6)) ^ 3 = 1 → (z : Perm (Fin 6)) ≠ 1 → (∀ a : Fin 6, (z : Perm (Fin 6)) a ≠ a) →
      ¬ FixesNonzero V Z x₀ := by
    rintro z x₀ rfl h3 h1 hfree
    exact not_fixesNonzero_of_fixedfree hπ h3 h1 hfree
  have hconj : ∃ c : Perm (Fin 6), sign c = 1 ∧ c * (y : Perm (Fin 6)) * c⁻¹ = (y' : Perm (Fin 6)) := by
    rcases order3_types _ hy3p hy1 with h1 | h1
    · have hfx : FixesNonzero V Z x := hpos y x hxe h1
      rcases order3_types _ hy'3p hy'1 with h2 | h2
      · obtain ⟨c₁, hc₁, hc₁e⟩ := conj3a _ hy3p hy1 h1
        obtain ⟨c₂, hc₂, hc₂e⟩ := conj3a _ hy'3p hy'1 h2
        refine ⟨c₂ * c₁⁻¹, by simp [hc₁, hc₂], ?_⟩
        rw [← hc₁e, ← hc₂e]
        group
      · exact absurd (hfn hfx) (hneg y' _ hxe' hy'3p hy'1 h2)
    · have hnx : ¬ FixesNonzero V Z x := hneg y x hxe hy3p hy1 h1
      rcases order3_types _ hy'3p hy'1 with h2 | h2
      · exact absurd (hfn' (hpos y' _ hxe' h2)) hnx
      · obtain ⟨c₁, hc₁, hc₁e⟩ := conj3b _ hy3p hy1 h1
        obtain ⟨c₂, hc₂, hc₂e⟩ := conj3b _ hy'3p hy'1 h2
        refine ⟨c₂ * c₁⁻¹, by simp [hc₁, hc₂], ?_⟩
        rw [← hc₁e, ← hc₂e]
        group
  obtain ⟨c, hc, hcy⟩ := hconj
  have hcA : c ∈ alternatingGroup (Fin 6) := Equiv.Perm.mem_alternatingGroup.2 hc
  refine ⟨((π ⟨c, hcA⟩ : ↥L) : MulAut W), (π ⟨c, hcA⟩).2, ?_⟩
  have hyy : (⟨c, hcA⟩ : ↥(alternatingGroup (Fin 6))) * y * (⟨c, hcA⟩ : ↥(alternatingGroup (Fin 6)))⁻¹ = y' :=
    Subtype.ext hcy
  have := congrArg (fun z : ↥L => (z : MulAut W)) (congrArg π hyy)
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at this
  rw [hxe, hxe'] at this
  exact this

theorem map_fixV_eq {σ : MulAut W} (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    (fixV L).map σ.toMonoidHom = fixV L := by
  have hσ' : ∀ x ∈ L, σ⁻¹ * x * σ ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hσ (σ⁻¹ * x * σ)).2 (by simpa [mul_assoc] using hx)
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩ x hx
    have := hv (σ⁻¹ * x * σ) (hσ' x hx)
    calc x (σ v) = σ ((σ⁻¹ * x * σ) v) := by simp [MulAut.mul_apply]
      _ = σ v := by rw [this]
  · intro hw
    refine ⟨σ⁻¹ w, fun x hx => ?_, by simp⟩
    have h1 := hw (σ * x * σ⁻¹) ((Subgroup.mem_normalizer_iff.1 hσ x).1 hx)
    calc x (σ⁻¹ w) = σ⁻¹ ((σ * x * σ⁻¹) w) := by simp [MulAut.mul_apply]
      _ = σ⁻¹ w := by rw [h1]

theorem map_inf_fixV_eq {σ : MulAut W} (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hσV : V.map σ.toMonoidHom = V) : (V ⊓ fixV L).map σ.toMonoidHom = V ⊓ fixV L := by
  rw [Subgroup.map_inf V (fixV L) σ.toMonoidHom σ.injective, hσV, map_fixV_eq hσ]

theorem inner_of_stable_nat3 (hnat : BinaryNaturalSL L V Z 3 1) {σ : MulAut W}
    (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) (hσV : V.map σ.toMonoidHom = V)
    (hσZ : Z.map σ.toMonoidHom = Z) :
    ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹) := by
  obtain ⟨F, hF, hFfin, hcard, π, hπ⟩ := hnat
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have hσL : ∀ x ∈ L, σ * x * σ⁻¹ ∈ L := fun x hx => (Subgroup.mem_normalizer_iff.1 hσ x).1 hx
  exact exists_inner_of_twist_sl3 hF2 hπ hσL hσV.symm hσZ.symm
    (B5.secIsoL_refl (fun x hx w hw => hπ.2.2.2.1 ⟨x, hx⟩ w hw)
      (fun x hx w hw => hπ.2.2.2.2.1 ⟨x, hx⟩ w hw) hπ.2.1)

end Module

end A6Twist

end CFSG.Quasithin
