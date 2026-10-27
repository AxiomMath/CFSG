module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigCls
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigCombAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16c11_big_exists_threeCycle_fix {n : ℕ} (hn : 9 ≤ n) (q r : (FFModel.symDn n).Mod) :
    ∃ c : Equiv.Perm (Fin n), c ∈ alternatingGroup (Fin n) ∧ orderOf c = 3 ∧
      (FFModel.symDn_isActionModel n).modAct c q = q ∧
      (FFModel.symDn_isActionModel n).modAct c r = r := by
  classical
  obtain ⟨x, hx, hq⟩ := s16c11BigCls_surjective n q
  obtain ⟨y, hy, hr⟩ := s16c11BigCls_surjective n r
  have hcard : Fintype.card (ZMod 2 × ZMod 2) * 2 < Fintype.card (Fin n) := by
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]
    omega
  obtain ⟨p, hp⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (f := fun i : Fin n => (x i, y i)) (n := 2) hcard
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hp
  have ha' : (x a, y a) = p := by simpa using ha
  have hb' : (x b, y b) = p := by simpa using hb
  have hc' : (x c, y c) = p := by simpa using hc
  have xab : x a = x b := congrArg Prod.fst (ha'.trans hb'.symm)
  have xac : x a = x c := congrArg Prod.fst (ha'.trans hc'.symm)
  have yab : y a = y b := congrArg Prod.snd (ha'.trans hb'.symm)
  have yac : y a = y c := congrArg Prod.snd (ha'.trans hc'.symm)
  set c₀ : Equiv.Perm (Fin n) := Equiv.swap a b * Equiv.swap a c with hc0def
  have h3 : Equiv.Perm.IsThreeCycle c₀ := by
    rw [hc0def]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hc0_a : c₀ a = c := by
    rw [hc0def, Equiv.Perm.mul_apply, Equiv.swap_apply_left a c,
      Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  have hc0_b : c₀ b = a := by
    rw [hc0def, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab.symm hbc,
      Equiv.swap_apply_right a b]
  have hc0_c : c₀ c = b := by
    rw [hc0def, Equiv.Perm.mul_apply, Equiv.swap_apply_right a c, Equiv.swap_apply_left a b]
  have hc0_of_ne : ∀ i, i ≠ a → i ≠ b → i ≠ c → c₀ i = i := by
    intro i hia hib hic
    rw [hc0def, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hia hic,
      Equiv.swap_apply_of_ne_of_ne hia hib]
  have hc0inv_a : c₀⁻¹ a = b := by
    have h : c₀.symm (c₀ b) = c₀.symm a := congrArg c₀.symm hc0_b
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  have hc0inv_b : c₀⁻¹ b = c := by
    have h : c₀.symm (c₀ c) = c₀.symm b := congrArg c₀.symm hc0_c
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  have hc0inv_c : c₀⁻¹ c = a := by
    have h : c₀.symm (c₀ a) = c₀.symm c := congrArg c₀.symm hc0_a
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  have hc0inv_of_ne : ∀ i, i ≠ a → i ≠ b → i ≠ c → c₀⁻¹ i = i := by
    intro i hia hib hic
    calc c₀⁻¹ i = c₀⁻¹ (c₀ i) := by rw [hc0_of_ne i hia hib hic]
      _ = i := Equiv.symm_apply_apply c₀ i
  have const_fix : ∀ z : Fin n → ZMod 2, z a = z b → z a = z c →
      ∀ i, z (c₀⁻¹ i) = z i := by
    intro z zab zac i
    by_cases hia : i = a
    · subst hia
      rw [hc0inv_a]
      exact zab.symm
    by_cases hib : i = b
    · subst hib
      rw [hc0inv_b]
      exact zac.symm.trans zab
    by_cases hic : i = c
    · subst hic
      rw [hc0inv_c]
      exact zac
    · rw [hc0inv_of_ne i hia hib hic]
  have hxfix : (fun i => x (c₀⁻¹ i)) = x := funext (const_fix x xab xac)
  have hyfix : (fun i => y (c₀⁻¹ i)) = y := funext (const_fix y yab yac)
  have hx' : ∑ i, x (c₀⁻¹ i) = 0 := by rw [hxfix, hx]
  have hy' : ∑ i, y (c₀⁻¹ i) = 0 := by rw [hyfix, hy]
  refine ⟨c₀, h3.mem_alternatingGroup, h3.orderOf, ?_, ?_⟩
  · rw [hq, s16c11BigCls_modAct (hx' := hx')]
    show QuotientGroup.mk (⟨Multiplicative.ofAdd (fun i => x (c₀⁻¹ i)), hx'⟩ :
        ↥(G6.coreMod n)) =
      QuotientGroup.mk (⟨Multiplicative.ofAdd x, hx⟩ : ↥(G6.coreMod n))
    exact congrArg QuotientGroup.mk (Subtype.ext (congrArg Multiplicative.ofAdd hxfix))
  · rw [hr, s16c11BigCls_modAct (hx' := hy')]
    show QuotientGroup.mk (⟨Multiplicative.ofAdd (fun i => y (c₀⁻¹ i)), hy'⟩ :
        ↥(G6.coreMod n)) =
      QuotientGroup.mk (⟨Multiplicative.ofAdd y, hy⟩ : ↥(G6.coreMod n))
    exact congrArg QuotientGroup.mk (Subtype.ext (congrArg Multiplicative.ofAdd hyfix))

theorem s16c11_big_pRank_le {A : Type} [Group A] [Finite A] {K L₀ X : Subgroup A}
    (hI : IsInternalDirect K L₀ X) (hK : IsSym ↥K 3) {n : ℕ} (hS : IsSym ↥L₀ n) :
    CFSG.Open.pRank 2 X ≤ 1 + n / 2 := by
  classical
  have hcomm : ∀ k ∈ K, ∀ l ∈ L₀, l * k = k * l := by
    intro k hk l hl
    have hle : K ≤ Subgroup.centralizer (L₀ : Set A) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hI.1
    exact (Subgroup.mem_centralizer_iff.mp (hle hk)) l hl
  have hcomm' : ∀ k : ↥K, ∀ l : ↥L₀, Commute (K.subtype k) (L₀.subtype l) :=
    fun k l => (hcomm k k.2 l l.2).symm
  let π : ↥K × ↥L₀ →* A := MonoidHom.noncommCoprod K.subtype L₀.subtype hcomm'
  have hdisj : Disjoint K.subtype.range L₀.subtype.range := by
    rw [disjoint_iff, Subgroup.range_subtype, Subgroup.range_subtype, hI.2.1]
  have hπinj : Function.Injective π :=
    (MonoidHom.noncommCoprod_injective K.subtype L₀.subtype hcomm').mpr
      ⟨K.subtype_injective, L₀.subtype_injective, hdisj⟩
  have hπrange : π.range = X := by
    change (MonoidHom.noncommCoprod K.subtype L₀.subtype hcomm').range = X
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype, hI.2.2]
  have hmem : ∀ p : ↥K × ↥L₀, π p ∈ X := fun p =>
    hI.2.2 ▸ Subgroup.mul_mem_sup (p.1.2) (p.2.2)
  let ψ : ↥K × ↥L₀ →* ↥X := π.codRestrict X hmem
  have hψinj : Function.Injective ψ :=
    (MonoidHom.injective_codRestrict π X hmem).mpr hπinj
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : A) ∈ π.range := hπrange ▸ y.2
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hy
    exact ⟨p, Subtype.ext hp⟩
  let e : ↥K × ↥L₀ ≃* ↥X := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, hEX, hEab, hEcard⟩
  obtain ⟨-, hEsq0⟩ := hEab
  have hEsq : ∀ x : ↥E, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    simpa using hEsq0 x.val x.2
  let incl : ↥E →* ↥X := Subgroup.inclusion hEX
  let g : ↥E →* ↥K × ↥L₀ := e.symm.toMonoidHom.comp incl
  have hginj : Function.Injective g :=
    e.symm.injective.comp (Subgroup.inclusion_injective hEX)
  let gK : ↥E →* ↥K := (MonoidHom.fst ↥K ↥L₀).comp g
  let gL : ↥E →* ↥L₀ := (MonoidHom.snd ↥K ↥L₀).comp g
  have hgK_sq : ∀ y ∈ gK.range, y ^ 2 = 1 := by
    rintro y ⟨x, rfl⟩
    rw [← map_pow, hEsq x, map_one]
  have hgL_sq : ∀ y ∈ gL.range, y ^ 2 = 1 := by
    rintro y ⟨x, rfl⟩
    rw [← map_pow, hEsq x, map_one]
  let Φ : ↥E → gK.range × gL.range := fun x =>
    (⟨gK x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩, ⟨gL x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩)
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    have h1 : gK x = gK y := congrArg (fun z => (z.1 : ↥K)) hxy
    have h2 : gL x = gL y := congrArg (fun z => (z.2 : ↥L₀)) hxy
    exact hginj (Prod.ext h1 h2)
  have hle : Nat.card ↥E ≤ Nat.card (gK.range × gL.range) :=
    Nat.card_le_card_of_injective Φ hΦinj
  rw [Nat.card_prod] at hle
  obtain ⟨eK⟩ := hK
  obtain ⟨eL⟩ := hS
  have hboundK : Nat.card gK.range ≤ 2 := by
    have h := s16c11_big_comba_card_le_of_perm eK gK.range hgK_sq
    simpa using h
  have hboundL : Nat.card gL.range ≤ 2 ^ (n / 2) := by
    have h := s16c11_big_comba_card_le_of_perm eL gL.range hgL_sq
    simpa using h
  have hcardE : Nat.card ↥E ≤ 2 * 2 ^ (n / 2) :=
    hle.trans (Nat.mul_le_mul hboundK hboundL)
  have hpow : 2 * 2 ^ (n / 2) = 2 ^ (1 + n / 2) := by rw [pow_add, pow_one]
  have h2k : 2 ^ k ≤ 2 ^ (1 + n / 2) := by
    rw [← hEcard]
    exact hpow ▸ hcardE
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2k

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
