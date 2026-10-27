module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6FrameCore
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveWeylFaithful
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

namespace TwE6TB

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private noncomputable def e6Perm (p : ℕ) [NeZero p] :
    WeylGroup TwistTag.E6.tag →* Equiv.Perm (Fin TwistTag.E6.tag.rank → ZMod p) :=
  TableBExc.torusPerm TwistTag.E6.tag p

private lemma e6Perm_apply (p : ℕ) [NeZero p] (w : WeylGroup TwistTag.E6.tag)
    (s : Fin TwistTag.E6.tag.rank → ZMod p) :
    e6Perm p w s = TableBExc.torusAct TwistTag.E6.tag p w s :=
  TableBExc.torusPerm_apply w s

private lemma e6Perm_mul (p : ℕ) [NeZero p] (w w' : WeylGroup TwistTag.E6.tag)
    (s : Fin TwistTag.E6.tag.rank → ZMod p) :
    e6Perm p (w * w') s = e6Perm p w (e6Perm p w' s) := by
  rw [map_mul, Equiv.Perm.mul_apply]

private lemma e6Perm_smul (p : ℕ) [NeZero p] (w : WeylGroup TwistTag.E6.tag) (c : ZMod p)
    (s : Fin TwistTag.E6.tag.rank → ZMod p) :
    e6Perm p w (c • s) = c • e6Perm p w s := by
  rw [e6Perm_apply, e6Perm_apply]
  exact NoOffE8Five.torusAct_smul w c s

private lemma frameActs_mul {p : ℕ} [NeZero p] {R : Type} [Group R]
    {t : Multiplicative (Fin 6 → ZMod p) →* R} {γ γ' : MulAut R}
    {π π' : Equiv.Perm (Fin TwistTag.E6.tag.rank → ZMod p)}
    (h : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      γ (t (Multiplicative.ofAdd s)) = t (Multiplicative.ofAdd (π s)))
    (h' : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      γ' (t (Multiplicative.ofAdd s)) = t (Multiplicative.ofAdd (π' s))) :
    ∀ s : Fin TwistTag.E6.tag.rank → ZMod p, (γ * γ') (t (Multiplicative.ofAdd s)) =
      t (Multiplicative.ofAdd ((π * π') s)) := by
  intro s
  rw [MulAut.mul_apply, Equiv.Perm.mul_apply, h', h]

private lemma frameActs_inv {p : ℕ} [NeZero p] {R : Type} [Group R]
    {t : Multiplicative (Fin 6 → ZMod p) →* R} {γ : MulAut R}
    {π : Equiv.Perm (Fin TwistTag.E6.tag.rank → ZMod p)}
    (h : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      γ (t (Multiplicative.ofAdd s)) = t (Multiplicative.ofAdd (π s))) :
    ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      γ⁻¹ (t (Multiplicative.ofAdd s)) = t (Multiplicative.ofAdd (π⁻¹ s)) := by
  intro s
  apply γ.injective
  rw [MulAut.apply_inv_self, h, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

theorem frame_representative {p : ℕ} [Fact p.Prime] [NeZero p] {R : Type} [Group R]
    {I : Set (MulAut R)} (hinn : ∀ ρ : R, MulAut.conj ρ ∈ I)
    (h : GGTwE6FramePackageSF p R I) {f : MulAut R} {k : ℕ} (hf : f ^ p ^ k = 1)
    {E : Subgroup R} (hE : IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E)
    (hSC : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ r : R, ∀ e ∈ E, MulAut.conj r (f e) = e := by
  obtain ⟨t, m, hFrame⟩ := h
  refine frame_conj_fix hFrame f ?_ hE h4 hSC
  intro a b hstab
  let δ : MulAut R := MulAut.conj a * f * MulAut.conj b
  change ∃ w : WeylGroup TwistTag.E6.tag, ∀ s : Fin 6 → ZMod p,
    δ (t (Multiplicative.ofAdd s)) =
      t (Multiplicative.ofAdd (TableBExc.torusAct TwistTag.E6.tag p w s))
  unfold GGTwE6FrameAt at hFrame
  obtain ⟨_, _, _, hAut, hInnerDiag⟩ := hFrame
  let Act : Subgroup (MulAut R) :=
    { carrier := {γ | ∃ w : WeylGroup TwistTag.E6.tag,
        ∀ s : Fin TwistTag.E6.tag.rank → ZMod p, γ (t (Multiplicative.ofAdd s)) =
          t (Multiplicative.ofAdd (e6Perm p w s))}
      one_mem' := ⟨1, by
        intro s
        rw [map_one, MulAut.one_apply, Equiv.Perm.one_apply]⟩
      mul_mem' := by
        rintro γ γ' ⟨w, hγ⟩ ⟨w', hγ'⟩
        exact ⟨w * w', by
          intro s
          rw [map_mul]
          exact frameActs_mul hγ hγ' s⟩
      inv_mem' := by
        rintro γ ⟨w, hγ⟩
        exact ⟨w⁻¹, by
          intro s
          rw [map_inv]
          exact frameActs_inv hγ s⟩ }
  obtain ⟨w, c, hc, hδw⟩ := hAut δ hstab
  have hδw' : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      δ (t (Multiplicative.ofAdd s)) = t (Multiplicative.ofAdd (c • e6Perm p w s)) := by
    intro s
    rw [hδw s, e6Perm_apply]
  have hpow : ∀ n : ℕ, ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      (δ ^ n) (t (Multiplicative.ofAdd s)) =
        t (Multiplicative.ofAdd (c ^ n • e6Perm p (w ^ n) s)) := by
    intro n
    induction n with
    | zero =>
      intro s
      simp only [pow_zero, MulAut.one_apply, map_one, Equiv.Perm.one_apply, one_smul]
    | succ n ih =>
      intro s
      rw [pow_succ', MulAut.mul_apply, ih s, hδw' (c ^ n • e6Perm p (w ^ n) s)]
      rw [e6Perm_smul, smul_smul, ← e6Perm_mul]
      rw [pow_succ', pow_succ']
  have hc_pow : c ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hc
  have h1 : δ ^ (p - 1) ∈ Act := by
    refine ⟨w ^ (p - 1), ?_⟩
    intro s
    rw [hpow (p - 1) s, hc_pow, one_smul]
  have hstab_pow : ∀ n : ℕ, ∀ x ∈ t.range, (δ ^ n) x ∈ t.range := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply]
      exact ih _ (hstab x hx)
  have hδN : δ ^ p ^ k ∈ (MulAut.conj : R →* MulAut R).range := by
    let q : MulAut R →* MulAut R ⧸ (MulAut.conj : R →* MulAut R).range :=
      QuotientGroup.mk' _
    have hqa : q (MulAut.conj a) = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (MulAut.conj a)).mpr ⟨a, rfl⟩
    have hqb : q (MulAut.conj b) = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (MulAut.conj b)).mpr ⟨b, rfl⟩
    have hδq : q δ = q f := by
      change q (MulAut.conj a * f * MulAut.conj b) = q f
      rw [map_mul, map_mul, hqa, hqb, one_mul, mul_one]
    have hqpow : q (δ ^ p ^ k) = 1 := by
      rw [map_pow, hδq, ← map_pow, hf, map_one]
    exact (QuotientGroup.eq_one_iff (δ ^ p ^ k)).mp hqpow
  rw [MonoidHom.mem_range] at hδN
  obtain ⟨ρ, hρ⟩ := hδN
  have hI : δ ^ p ^ k ∈ I := hρ ▸ hinn ρ
  obtain ⟨w'', hw''⟩ := hInnerDiag (δ ^ p ^ k) hI (hstab_pow (p ^ k))
  have h2 : δ ^ p ^ k ∈ Act := ⟨w'', by
    intro s
    rw [hw'' s, e6Perm_apply]⟩
  have hcop : Nat.Coprime (p - 1) (p ^ k) := by
    have hp1 : Nat.Coprime 1 p := (Nat.coprime_one_left_iff p).mpr trivial
    have hp' : Nat.Coprime (p - 1) p :=
      (Nat.coprime_self_sub_left (m := 1) (n := p)
        (le_of_lt (Fact.out : p.Prime).one_lt)).mpr hp1
    exact hp'.pow_right k
  obtain ⟨u, v, huv⟩ :
      ∃ u v : ℤ, ((p - 1 : ℕ) : ℤ) * u + ((p ^ k : ℕ) : ℤ) * v = 1 := by
    have hbez := Nat.gcd_eq_gcd_ab (p - 1) (p ^ k)
    rw [hcop.gcd_eq_one] at hbez
    exact ⟨Nat.gcdA (p - 1) (p ^ k), Nat.gcdB (p - 1) (p ^ k), hbez.symm⟩
  have hδ : δ ∈ Act := by
    have hbez : (δ ^ (p - 1)) ^ u * (δ ^ (p ^ k)) ^ v = δ := by
      rw [← zpow_natCast δ (p - 1), ← zpow_natCast δ (p ^ k),
        ← zpow_mul, ← zpow_mul, ← zpow_add, huv, zpow_one]
    rw [← hbez]
    exact Act.mul_mem (Act.zpow_mem h1 u) (Act.zpow_mem h2 v)
  obtain ⟨w', hw'⟩ := hδ
  refine ⟨w', fun s => ?_⟩
  exact (hw' s).trans (congrArg (fun x => t (Multiplicative.ofAdd x)) (e6Perm_apply p w' s))

end TwE6TB

end CFSG.StandardType
