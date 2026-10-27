module

public import CFSG.Quasithin.Recognition.SzVBA5Loc
public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.Setting

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Kleidman.VBOdd (prim_of_setting exists_mul_of_mem_sup
  mem_kerAct_of_mem_pCoreOf)

section Perm

theorem fin_five_even_fix_sq_or_cube :
    ∀ (τ : Equiv.Perm (Fin 5)) (i : Fin 5), τ i = i → Equiv.Perm.sign τ = 1 →
      τ ^ 2 = 1 ∨ τ ^ 3 = 1 := by
  decide +kernel

theorem perm_sq_eq_one_of_even_fix_pow_two {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Nat.card Ω = 5) (o : Ω) (σ : Equiv.Perm Ω) (ho : σ o = o)
    (hs : Equiv.Perm.sign σ = 1) {m : ℕ} (hm : σ ^ 2 ^ m = 1) : σ ^ 2 = 1 := by
  have hc : Fintype.card Ω = 5 := by rw [← Nat.card_eq_fintype_card]; exact hΩ
  let e : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hc
  let φ : Equiv.Perm Ω ≃* Equiv.Perm (Fin 5) := e.permCongrHom
  have hφ : ∀ (p : Equiv.Perm Ω) (x : Ω), φ p (e x) = e (p x) := by
    intro p x
    simp [φ, Equiv.permCongr_apply]
  have hsign : Equiv.Perm.sign (φ σ) = 1 := by
    rw [← hs]
    exact Equiv.Perm.sign_permCongr e σ
  have hfix : φ σ (e o) = e o := by rw [hφ, ho]
  have hpow : φ σ ^ 2 ^ m = 1 := by rw [← map_pow, hm, map_one]
  apply φ.injective
  rw [map_pow, map_one]
  rcases fin_five_even_fix_sq_or_cube (φ σ) (e o) hfix hsign with h2 | h3
  · exact h2
  · have hg : φ σ ^ Nat.gcd 3 (2 ^ m) = 1 := pow_gcd_eq_one.mpr ⟨h3, hpow⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right m (by decide : Nat.Coprime 3 2)),
      pow_one] at hg
    rw [hg, one_pow]

end Perm

section Setting

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem sign_toPermHom_eq_one_of_setting (h : R1SettingLegacyBare K1 L2 S Zs)
    (hA5 : S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S))
    [Fintype (ConjSet (K1 ⊔ S) (conjClosure Zs L2))]
    [DecidableEq (ConjSet (K1 ⊔ S) (conjClosure Zs L2))] (x : ↥(K1 ⊔ S)) :
    Equiv.Perm.sign
      (MulAction.toPermHom ↥(K1 ⊔ S) (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) x) = 1 := by
  have hK1P : K1 ≤ K1 ⊔ S := le_sup_left
  have : Group.IsPerfect ↥K1 := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp h.cComp_mem)
  set ρ := MulAction.toPermHom ↥(K1 ⊔ S) (ConjSet (K1 ⊔ S) (conjClosure Zs L2))
  obtain ⟨k0, hk0, q, hq, hxe⟩ := exists_mul_of_mem_sup h hA5 x.2
  have hxab : x = (⟨k0, hK1P hk0⟩ : ↥(K1 ⊔ S)) *
      (⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq⟩ : ↥(K1 ⊔ S)) := Subtype.ext hxe
  have hb : (⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq⟩ : ↥(K1 ⊔ S)) ∈
      kerAct (K1 ⊔ S) (conjClosure Zs L2) := mem_kerAct_of_mem_pCoreOf h hq
  have hρb : ρ ⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq⟩ = 1 := hb
  have hρx : ρ x = ρ ⟨k0, hK1P hk0⟩ := by rw [hxab, map_mul, hρb, mul_one]
  let φ : ↥K1 →* ℤˣ := Equiv.Perm.sign.comp (ρ.comp (Subgroup.inclusion hK1P))
  have hφ : φ ⟨k0, hk0⟩ = 1 := by
    have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    have hsub : Subsingleton φ.range := inferInstance
    have := congrArg Subtype.val (Subsingleton.elim (⟨φ ⟨k0, hk0⟩, ⟨_, rfl⟩⟩ : φ.range) 1)
    simpa using this
  rw [hρx]
  exact hφ

theorem T_sq_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 2 (OTwoQuot K1))
    (hA5 : S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S)) :
    ∀ x : ↥(K1 ⊔ S), (x : G) ∈ S → x * x ∈ kerAct (K1 ⊔ S) (conjClosure Zs L2) := by
  classical
  intro x hxS
  have : Fintype (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) := Fintype.ofFinite _
  set ρ := MulAction.toPermHom ↥(K1 ⊔ S) (ConjSet (K1 ⊔ S) (conjClosure Zs L2))
  have hF := l24Facts_of_setting rankOneListedFacts h hL
  have hbase : ρ x (ConjSet.base (K1 ⊔ S) (conjClosure Zs L2)) =
      ConjSet.base (K1 ⊔ S) (conjClosure Zs L2) := by
    apply Subtype.ext
    show conjSub (x : G) (conjClosure Zs L2) = conjClosure Zs L2
    exact OddAux.conjSub_eq_of_mem_normalizer' (hF.S_le_normalizer hxS)
  obtain ⟨m, hm⟩ := hF.S_pGroup ⟨(x : G), hxS⟩
  have hxm : x ^ 2 ^ m = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hm
  have hρm : ρ x ^ 2 ^ m = 1 := by rw [← map_pow, hxm, map_one]
  have hsq : ρ x ^ 2 = 1 :=
    perm_sq_eq_one_of_even_fix_pow_two hF.card_five _ (ρ x) hbase
      (sign_toPermHom_eq_one_of_setting h hA5 x) hρm
  have hker : ρ (x * x) = 1 := by rw [map_mul, ← pow_two, hsq]
  exact hker

theorem perfect_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hA5 : S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S)) :
    K1 ⊔ S ≤ ⁅K1 ⊔ S, K1 ⊔ S⁆ ⊔ pCoreOf 2 (K1 ⊔ S) := by
  have hK1P : K1 ≤ K1 ⊔ S := le_sup_left
  have hperf : ⁅K1, K1⁆ = K1 := perfect_of_mem_cComp h.cComp_mem
  have h1 : K1 ≤ ⁅K1 ⊔ S, K1 ⊔ S⁆ :=
    hperf.symm.le.trans (Subgroup.commutator_mono hK1P hK1P)
  have hle : K1 ⊔ S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S) := sup_le le_sup_left hA5
  exact hle.trans (sup_le_sup_right h1 _)

theorem a5Facts_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 2 (OTwoQuot K1))
    (hA5 : S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S))
    (hab : IsElemAbelian 2 (conjClosure (conjClosure Zs L2) (K1 ⊔ S))) {z : G}
    (hK : KleinData (K1 ⊔ S) (conjClosure Zs L2) z) :
    A5Facts (K1 ⊔ S) S (conjClosure Zs L2) z :=
  let p := prim_of_setting h hL hA5 hab hK
  { klein := p.klein
    l24 := p.l24
    abel := p.abel
    ker_le := p.ker_le
    inv_one_fixed := p.inv_one_fixed
    T_sq := T_sq_of_setting h hL hA5
    perfect := perfect_of_setting h hA5 }

end Setting

end CFSG.Quasithin.SzVB
