module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylow

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover

namespace TableBExc

section Act

variable (τ : Tag) (p : ℕ)

@[expose] def redMod (v : Fin τ.rank → ℤ) : Fin τ.rank → ZMod p := fun i => (v i : ZMod p)

@[expose] def liftMod (x : Fin τ.rank → ZMod p) : Fin τ.rank → ℤ := fun i => ((x i).val : ℤ)

@[expose] noncomputable def torusAct (w : WeylGroup τ) (x : Fin τ.rank → ZMod p) : Fin τ.rank → ZMod p :=
  redMod τ p (w • liftMod τ p x)

variable {τ p}

theorem redMod_liftMod [NeZero p] (x : Fin τ.rank → ZMod p) : redMod τ p (liftMod τ p x) = x := by
  funext i
  simp [redMod, liftMod]

theorem redMod_sub (v v' : Fin τ.rank → ℤ) :
    redMod τ p (v - v') = redMod τ p v - redMod τ p v' := by
  funext i
  simp [redMod]

theorem redMod_smul_eq (w : WeylGroup τ) {v v' : Fin τ.rank → ℤ}
    (h : redMod τ p v = redMod τ p v') : redMod τ p (w • v) = redMod τ p (w • v') := by
  have hd : ∀ i, (p : ℤ) ∣ (v - v') i := fun i => by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrFun ((redMod_sub v v').trans (sub_eq_zero.mpr h)) i
    simpa [redMod] using this
  choose z hz using hd
  have hvz : v - v' = (p : ℤ) • z := funext fun i => by rw [hz i, Pi.smul_apply, smul_eq_mul]
  have h1 : w • v - w • v' = (p : ℤ) • (w • z) := by
    rw [← smul_sub, hvz, smul_def, smul_def, map_zsmul]
  rw [← sub_eq_zero, ← redMod_sub, h1]
  funext i
  simp [redMod]

theorem torusAct_one [NeZero p] (x : Fin τ.rank → ZMod p) : torusAct τ p 1 x = x := by
  rw [torusAct, one_smul, redMod_liftMod]

theorem torusAct_mul [NeZero p] (w w' : WeylGroup τ) (x : Fin τ.rank → ZMod p) :
    torusAct τ p (w * w') x = torusAct τ p w (torusAct τ p w' x) := by
  rw [torusAct, torusAct, torusAct, mul_smul]
  exact redMod_smul_eq w (redMod_liftMod _).symm

variable (τ p) in
@[expose] noncomputable def torusPerm [NeZero p] : WeylGroup τ →* Equiv.Perm (Fin τ.rank → ZMod p) where
  toFun w :=
    { toFun := torusAct τ p w
      invFun := torusAct τ p w⁻¹
      left_inv x := by rw [← torusAct_mul, inv_mul_cancel, torusAct_one]
      right_inv x := by rw [← torusAct_mul, mul_inv_cancel, torusAct_one] }
  map_one' := Equiv.ext fun x => torusAct_one x
  map_mul' w w' := Equiv.ext fun x => torusAct_mul w w' x

theorem torusPerm_apply [NeZero p] (w : WeylGroup τ) (x : Fin τ.rank → ZMod p) :
    torusPerm τ p w x = torusAct τ p w x :=
  rfl

theorem torusRefl_eq_torusAct [NeZero p] (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (i : Fin τ.rank) (a : Fin τ.rank → ZMod p) :
    torusRefl τ p i a = torusAct τ p (simple τ i) a := by
  rw [torusAct, simple_smul]
  funext k
  simp only [torusRefl, redMod, liftMod, reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [ZMod.natCast_zmod_val]
  congr 2
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm, ZMod.natCast_zmod_val]
  · by_cases hk : k = i
    · subst hk
      simp
    · simp [hk]

theorem torusWord_eq_torusAct [NeZero p] (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (ω : List (Fin τ.rank)) (a : Fin τ.rank → ZMod p) :
    torusWord τ p ω a = torusAct τ p ((coxeterSystem τ).wordProd ω) a := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, torusAct_one]; rfl
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, torusAct_mul, ← ih, ← torusRefl_eq_torusAct hsymm]
    rfl

end Act

section Count

variable {τ : Tag} {K : Type} [Field K]

theorem card_le_mul_card_fix_of_le_weylX [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    {S : Subgroup (WeylGroup τ)} {E : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian p E)
    (hEX : E ≤ weylX τ K S) :
    ∃ A : Subgroup (WeylGroup τ), A ≤ S ∧ IsElemAbelian p A ∧ (A = ⊥ → E ≤ torusPow τ K p) ∧
      Nat.card E ≤
        Nat.card A * Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ A, torusAct τ p a x = x} := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hφinj := chevTorus_injective hζo hζ hdet
  have hφrange := range_chevTorus_eq_torusPow hζo hζ hdet hV
  obtain ⟨-, hker⟩ := weylQuotientHom_surjective_ker (τ := τ) (K := K)
  have hEM : ∀ e : E, ((e : adjointGroup τ K) : ModGL τ K) ∈ monomialSubgroup τ K :=
    fun e => (mem_weylX.mp (hEX e.2)).1
  let ι : E →* monomialSubgroup τ K :=
    ((adjointGroup τ K).subtype.comp E.subtype).codRestrict _ hEM
  let ψ : E →* WeylGroup τ := (weylQuotientHom τ K).comp ι
  have hψS : ∀ e : E, ψ e ∈ S := fun e => (mem_weylX.mp (hEX e.2)).2
  have hkerH : ∀ e : E, ψ e = 1 → ((e : adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K := by
    intro e he
    have h1 : ι e ∈ (weylQuotientHom τ K).ker := he
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hkerV : ∀ e : E, ψ e = 1 → (e : adjointGroup τ K) ∈ torusPow τ K p := fun e he =>
    ⟨hkerH e he, hE.2 _ e.2⟩
  have hfix : ∀ (e₀ : E) (ω : List (Fin τ.rank)), ψ e₀ = (coxeterSystem τ).wordProd ω →
      ∀ e : E, ψ e = 1 → ∃ x : Fin τ.rank → ZMod p,
        chevTorus τ ζ hζ (.ofAdd x) = (e : adjointGroup τ K) ∧ torusWord τ p ω x = x := by
    intro e₀ ω hω e he
    obtain ⟨x, hx⟩ : (e : adjointGroup τ K) ∈ (chevTorus τ ζ hζ).range := hφrange ▸ hkerV e he
    refine ⟨Multiplicative.toAdd x, by rw [ofAdd_toAdd]; exact hx, ?_⟩
    set n := nWord τ K ω with hn
    have hm := coe_nWord_mem_monomialSubgroup (K := K) ω
    have hρ : weylQuotientHom τ K (ι e₀ * (⟨_, hm⟩ : monomialSubgroup τ K)⁻¹) = 1 := by
      rw [map_mul, map_inv, weylQuotientHom_nWord]
      change ψ e₀ * _ = 1
      rw [hω, mul_inv_cancel]
    have hh : (((e₀ : adjointGroup τ K) * n⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
        torusGroup τ K := by
      have h1 : ι e₀ * (⟨_, hm⟩ : monomialSubgroup τ K)⁻¹ ∈ (weylQuotientHom τ K).ker := hρ
      rw [hker, Subgroup.mem_subgroupOf] at h1
      exact h1
    have hc0 : (e₀ : adjointGroup τ K) * e = e * e₀ := TableB.IsElemAbelian.comm hE e₀.2 e.2
    have hch : ((e₀ : adjointGroup τ K) * n⁻¹) * e = e * ((e₀ : adjointGroup τ K) * n⁻¹) :=
      Subtype.ext (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh)
        (torusGroup_le_diagonalGroup (hkerH e he)))
    have hne : n * (e : adjointGroup τ K) * n⁻¹ = e := by
      set h := (e₀ : adjointGroup τ K) * n⁻¹ with hhdef
      have hn' : n = h⁻¹ * e₀ := by
        rw [hhdef]
        group
      have hc0' : (e₀ : adjointGroup τ K) * e * (e₀ : adjointGroup τ K)⁻¹ = e := by
        rw [hc0]
        group
      have hch' : h⁻¹ * (e : adjointGroup τ K) * h = e := by
        rw [mul_assoc, ← hch]
        group
      rw [hn', mul_inv_rev, inv_inv]
      calc h⁻¹ * (e₀ : adjointGroup τ K) * e * ((e₀ : adjointGroup τ K)⁻¹ * h) =
          h⁻¹ * ((e₀ : adjointGroup τ K) * e * (e₀ : adjointGroup τ K)⁻¹) * h := by group
        _ = h⁻¹ * e * h := by rw [hc0']
        _ = e := hch'
    have hconj := nWord_conj_chevTorus hζ ω (Multiplicative.toAdd x)
    rw [ofAdd_toAdd, hx, hne] at hconj
    exact congrArg Multiplicative.toAdd (hφinj (hconj.symm.trans hx.symm))
  refine ⟨ψ.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, rfl⟩
    exact hψS e
  · have hcommE : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
    have hpowE : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (by simpa using hE.2 _ a.2)
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      show ψ a * ψ b = ψ b * ψ a
      rw [← map_mul, ← map_mul, hcommE]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow, hpowE, map_one]
  · intro hr e he
    have h1 : ψ ⟨e, he⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hr, Subgroup.mem_bot] at h1
    exact hkerV ⟨e, he⟩ h1
  · have hcardE := TableB.card_range_mul_card_ker ψ
    have hk : Nat.card ψ.ker ≤
        Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ ψ.range, torusAct τ p a x = x} := by
      have hex : ∀ e : ψ.ker, ∃ x : {x : Fin τ.rank → ZMod p //
          ∀ a ∈ ψ.range, torusAct τ p a x = x},
          chevTorus τ ζ hζ (.ofAdd x.1) = ((e : E) : adjointGroup τ K) := by
        intro e
        obtain ⟨x, hx⟩ : ((e : E) : adjointGroup τ K) ∈ (chevTorus τ ζ hζ).range :=
          hφrange ▸ hkerV e e.2
        refine ⟨⟨Multiplicative.toAdd x, ?_⟩, by rw [ofAdd_toAdd]; exact hx⟩
        rintro _ ⟨e₀, rfl⟩
        obtain ⟨ω, hω⟩ := (coxeterSystem τ).wordProd_surjective (ψ e₀)
        obtain ⟨y, hy, hy'⟩ := hfix e₀ ω hω.symm e e.2
        have hxy : y = Multiplicative.toAdd x :=
          congrArg Multiplicative.toAdd (hφinj (hy.trans hx.symm))
        rw [← hω, ← torusWord_eq_torusAct hsymm, ← hxy]
        exact hy'
      choose g hg using hex
      refine Nat.card_le_card_of_injective g fun a b hab => ?_
      apply Subtype.ext
      apply Subtype.ext
      rw [← hg a, ← hg b, hab]
    calc Nat.card E = Nat.card ψ.range * Nat.card ψ.ker := hcardE.symm
      _ ≤ _ := Nat.mul_le_mul_left _ hk

theorem ggExcToralRankInput_of_noOffender [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    {S : Subgroup (WeylGroup τ)} (hidx : ¬ p ∣ (weylX τ K S).index)
    (hS : ∀ A : Subgroup (WeylGroup τ), A ≤ S → IsElemAbelian p A → A ≠ ⊥ →
      Nat.card A * Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ A, torusAct τ p a x = x} <
        p ^ τ.rank) :
    GGExcToralRankInput τ K p := by
  intro E hE hcard
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  obtain ⟨g, hg⟩ := TableBF4.exists_conj_le_of_not_dvd_index hp hidx
    (TableB.isPGroup_of_isElemAbelian hE)
  have hcard' : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  refine ⟨g, ?_⟩
  obtain ⟨A, hAS, hA, hA1, hEA⟩ := card_le_mul_card_fix_of_le_weylX hp hpq hdet hV hsymm
    (TableB.isElemAbelian_map hE _) hg
  by_cases hbot : A = ⊥
  · exact Subgroup.eq_of_le_of_card_ge (hA1 hbot) (by rw [hV, hcard']; exact hcard)
  · have := hS A hAS hA hbot
    omega

end Count

end TableBExc

end CFSG.StandardType
