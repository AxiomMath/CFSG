module
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Gen
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Pair
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Pieces
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1PiecesPos
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Fork
public import CFSG.GH74.L5U5.ModelsPairsUnitary
public import CFSG.ClassicalInvolution.Phan.StandardPair
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Signs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux2
public import Mathlib.FieldTheory.Finite.GaloisField

public section
namespace CFSG.StandardType
open Multiplicative

theorem omPlusRefl_apply_eq_one_iff {p r : ℕ} (x : OmPlusIdx r)
    (f : Fin r → Multiplicative (ZMod p)) (k : Fin r) :
    omPlusRefl p x f k = 1 ↔ f (Equiv.swap x.1.1.1 x.1.1.2 k) = 1 := by
  rcases x with ⟨⟨⟨a, b⟩, hab⟩, s⟩
  cases s
  · simp [omPlusRefl, SpCoord.permAut_apply, Equiv.swap_inv]
  · simp only [omPlusRefl, Bool.cond_true, MulAut.mul_apply,
      SpCoord.sgnAut_apply, SpCoord.permAut_apply, Equiv.swap_inv]
    by_cases hka : k = a
    · subst k
      simp [ne_of_lt hab]
    · by_cases hkb : k = b
      · subst k
        simp [ne_of_lt hab, (ne_of_lt hab).symm]
      · simp [Function.update_apply, hka, hkb]

theorem omPlusRefl_swap_commute {p r : ℕ} (hp : p.Prime) (x y : OmPlusIdx r)
    (hcomm : omPlusRefl p x * omPlusRefl p y = omPlusRefl p y * omPlusRefl p x) :
    Equiv.swap x.1.1.1 x.1.1.2 * Equiv.swap y.1.1.1 y.1.1.2 =
      Equiv.swap y.1.1.1 y.1.1.2 * Equiv.swap x.1.1.1 x.1.1.2 := by
  classical
  apply Equiv.ext
  intro k
  by_contra hne
  let u := Equiv.swap x.1.1.1 x.1.1.2
  let v := Equiv.swap y.1.1.1 y.1.1.2
  let f : Fin r → Multiplicative (ZMod p) := Pi.mulSingle (u (v k)) (ofAdd 1)
  have h := congrArg (fun w : MulAut (Fin r → Multiplicative (ZMod p)) => w f k) hcomm
  have h1 : ((omPlusRefl p x * omPlusRefl p y) f) k = 1 ↔
      f (v (u k)) = 1 := by
    change omPlusRefl p x (omPlusRefl p y f) k = 1 ↔ _
    rw [omPlusRefl_apply_eq_one_iff, omPlusRefl_apply_eq_one_iff]
  have h2 : ((omPlusRefl p y * omPlusRefl p x) f) k = 1 ↔
      f (u (v k)) = 1 := by
    change omPlusRefl p y (omPlusRefl p x f) k = 1 ↔ _
    rw [omPlusRefl_apply_eq_one_iff, omPlusRefl_apply_eq_one_iff]
  have hf1 : f (v (u k)) = 1 := by
    change u (v k) ≠ v (u k) at hne
    simp [f, Ne.symm hne]
  have hf2 := h2.mp (h ▸ h1.mpr hf1)
  have hp1 : (1 : ZMod p) ≠ 0 := by
    have : Fact p.Prime := ⟨hp⟩
    exact one_ne_zero
  exact hp1 (by simpa [f] using hf2)

theorem omPlusRefl_commute_supports {p r : ℕ} (hp : p.Prime) (x y : OmPlusIdx r)
    (hcomm : omPlusRefl p x * omPlusRefl p y = omPlusRefl p y * omPlusRefl p x) :
    x.1 = y.1 ∨ Disjoint ({x.1.1.1, x.1.1.2} : Finset (Fin r))
      {y.1.1.1, y.1.1.2} := by
  classical
  rcases x with ⟨⟨⟨a, b⟩, hab⟩, s⟩
  rcases y with ⟨⟨⟨c, d⟩, hcd⟩, t⟩
  have hc := omPlusRefl_swap_commute hp (⟨⟨(a,b),hab⟩,s⟩) (⟨⟨(c,d),hcd⟩,t⟩) hcomm
  have habne := ne_of_lt hab
  have hcdne := ne_of_lt hcd
  by_cases hac : a = c
  · subst c
    by_cases hbd : b = d
    · subst d; exact Or.inl rfl
    · have h := congrArg (fun w : Equiv.Perm (Fin r) => w a) hc
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne, habne.symm,
         hcdne.symm, hbd, (Ne.symm hbd)] at h
  by_cases had : a = d
  · subst d
    have hbc : b ≠ c := by exact ne_of_gt (hcd.trans hab)
    have h := congrArg (fun w : Equiv.Perm (Fin r) => w a) hc
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne, habne.symm,
      hcdne, hbc, (Ne.symm hbc)] at h
  by_cases hbc : b = c
  · subst c
    have had' : a ≠ d := ne_of_lt (hab.trans hcd)
    have h := congrArg (fun w : Equiv.Perm (Fin r) => w b) hc
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne, habne,
       hcdne.symm, had', had'.symm] at h
  by_cases hbd : b = d
  · subst d
    have h := congrArg (fun w : Equiv.Perm (Fin r) => w b) hc
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne, habne,
      hcdne, hac, (Ne.symm hac)] at h
  exact Or.inr (by simp [Finset.disjoint_left, hac, had, hbc, hbd])


theorem omPlusRefl_apply_coord {p r : ℕ} (x : OmPlusIdx r)
    (f : Fin r → Multiplicative (ZMod p)) (k : Fin r) :
    omPlusRefl p x f k =
      if k = x.1.1.1 then cond x.2 (f x.1.1.2)⁻¹ (f x.1.1.2)
      else if k = x.1.1.2 then cond x.2 (f x.1.1.1)⁻¹ (f x.1.1.1)
      else f k := by
  rcases x with ⟨⟨⟨a, b⟩, hab⟩, s⟩
  cases s <;>
    simp only [omPlusRefl, Bool.cond_false, Bool.cond_true, MulAut.mul_apply,
      SpCoord.sgnAut_apply, SpCoord.permAut_apply, Equiv.swap_inv]
  all_goals
    by_cases hka : k = a
    · subst k
      simp [ne_of_lt hab]
    · by_cases hkb : k = b
      · subst k
        simp [ne_of_lt hab, (ne_of_lt hab).symm]
      · simp [Function.update_apply, hka, hkb,
          Equiv.swap_apply_of_ne_of_ne hka hkb]

theorem omPlusRefl_commute_of_supports {p r : ℕ} (x y : OmPlusIdx r)
    (hsupp : x.1 = y.1 ∨ Disjoint ({x.1.1.1, x.1.1.2} : Finset (Fin r))
      {y.1.1.1, y.1.1.2}) :
    omPlusRefl p x * omPlusRefl p y = omPlusRefl p y * omPlusRefl p x := by
  classical
  rcases x with ⟨⟨⟨a, b⟩, hab⟩, s⟩
  rcases y with ⟨⟨⟨c, d⟩, hcd⟩, t⟩
  have habne : a ≠ b := ne_of_lt hab
  have hcdne : c ≠ d := ne_of_lt hcd
  rcases hsupp with heq | hdisj
  · have heq' : (a, b) = (c, d) := congrArg Subtype.val heq
    have hac := congrArg Prod.fst heq'
    have hbd := congrArg Prod.snd heq'
    dsimp at hac hbd
    subst c; subst d
    cases s <;> cases t <;> ext f k
    all_goals
      by_cases hka : k = a
      · subst k
        simp [MulAut.mul_apply, omPlusRefl_apply_coord, habne.symm]
      · by_cases hkb : k = b
        · subst k
          simp [MulAut.mul_apply, omPlusRefl_apply_coord, habne.symm]
        · simp [MulAut.mul_apply, omPlusRefl_apply_coord, hka, hkb]
  · have hcross : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
      simpa [Finset.disjoint_left, and_assoc] using hdisj
    obtain ⟨hac, had, hbc, hbd⟩ := hcross
    ext f k
    by_cases hka : k = a
    · subst k
      simp [MulAut.mul_apply, omPlusRefl_apply_coord,
        hac, had, hbc, hbd]
    · by_cases hkb : k = b
      · subst k
        simp [MulAut.mul_apply, omPlusRefl_apply_coord, habne.symm,
          hac, had, hbc, hbd]
      · by_cases hkc : k = c
        · subst k
          simp [MulAut.mul_apply, omPlusRefl_apply_coord,
                Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd]
        · by_cases hkd : k = d
          · subst k
            simp [MulAut.mul_apply, omPlusRefl_apply_coord, hcdne.symm,
                  Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd]
          · simp [MulAut.mul_apply, omPlusRefl_apply_coord, hka, hkb, hkc, hkd]

theorem omPlusRefl_commute_iff_supports {p r : ℕ} (hp : p.Prime) (x y : OmPlusIdx r) :
    omPlusRefl p x * omPlusRefl p y = omPlusRefl p y * omPlusRefl p x ↔
      x.1 = y.1 ∨ Disjoint ({x.1.1.1, x.1.1.2} : Finset (Fin r))
        {y.1.1.1, y.1.1.2} :=
  ⟨omPlusRefl_commute_supports hp x y, omPlusRefl_commute_of_supports x y⟩

namespace OrthTorus
open CFSG.ClassicalInvolution.Phan
open CFSG.RankThree.Classical2 (orthDerived)
variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p r : ℕ} [Fact p.Prime]
  {A : Subgroup (V ≃ₗ[K] V)}

omit [Finite K] in
theorem TBJOmData.fixes_outside_signed_rankOne (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (i j : Fin r) (s : Bool) {x : V ≃ₗ[K] V}
    (hx : x ∈ if s then Δ.rankOnePos i j else Δ.rankOne i j)
    (k : Fin r) (hki : k ≠ i) (hkj : k ≠ j) (u : V) (hu : u ∈ Δ.F.U k) :
    x u = u := by
  cases s
  · change x ∈ Δ.rankOne i j at hx
    rw [TBJOmData.rankOne, ggOTwoPrime] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨⟨hyC, _⟩, m, hym⟩ := hy
      exact Δ.centralizer_two_fix hp2 hfix i j hyC hym k hki hkj u hu
    | one => rfl
    | mul y z hy hz ihy ihz =>
      change y (z u) = u
      rw [ihz, ihy]
    | inv y hy ih =>
      simpa using congrArg (fun z => y⁻¹ z) ih.symm
  · change x ∈ Δ.rankOnePos i j at hx
    rw [TBJOmData.rankOnePos, ggOTwoPrime] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨⟨hyC, _⟩, m, hym⟩ := hy
      exact Δ.centralizerPos_two_fix hp2 hfix i j hyC hym k hki hkj u hu
    | one => rfl
    | mul y z hy hz ihy ihz =>
      change y (z u) = u
      rw [ihz, ihy]
    | inv y hy ih =>
      simpa using congrArg (fun z => y⁻¹ z) ih.symm

theorem TBJOmData.commute_signed_rankOne_of_disjoint (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (a b c d : Fin r) (s t : Bool)
    (hdisj : Disjoint ({a, b} : Finset (Fin r)) {c, d}) :
    ∀ x ∈ (if s then Δ.rankOnePos a b else Δ.rankOne a b),
    ∀ y ∈ (if t then Δ.rankOnePos c d else Δ.rankOne c d), x * y = y * x := by
  intro x hx y hy
  have hxΩ : x ∈ orthDerived Q := by
    cases s
    · exact Δ.rankOne_le a b hx
    · exact Δ.rankOnePos_le a b hx
  have hyΩ : y ∈ orthDerived Q := by
    cases t
    · exact Δ.rankOne_le c d hy
    · exact Δ.rankOnePos_le c d hy
  apply Δ.commute_of_fixes_outside hfix hdisj hxΩ hyΩ
  · intro k hk u hu
    have hk' : k ≠ a ∧ k ≠ b := by simpa using hk
    exact Δ.fixes_outside_signed_rankOne hp2 hfix a b s hx k hk'.1 hk'.2 u hu
  · intro k hk u hu
    have hk' : k ≠ c ∧ k ≠ d := by simpa using hk
    exact Δ.fixes_outside_signed_rankOne hp2 hfix c d t hy k hk'.1 hk'.2 u hu

theorem TBJOmData.commute_signed_rankOne_of_refl_commute (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hAΩ : A ≤ orthDerived Q)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (x y : OmPlusIdx r) (hxy : x ≠ y)
    (hcomm : omPlusRefl p x * omPlusRefl p y = omPlusRefl p y * omPlusRefl p x) :
    ∀ u ∈ (if x.2 then Δ.rankOnePos x.1.1.1 x.1.1.2 else Δ.rankOne x.1.1.1 x.1.1.2),
    ∀ v ∈ (if y.2 then Δ.rankOnePos y.1.1.1 y.1.1.2 else Δ.rankOne y.1.1.1 y.1.1.2),
      u * v = v * u := by
  classical
  have hsupp := omPlusRefl_commute_supports (Fact.out : p.Prime) x y hcomm
  rcases x with ⟨⟨⟨a, b⟩, hab⟩, s⟩
  rcases y with ⟨⟨⟨c, d⟩, hcd⟩, t⟩
  rcases hsupp with heq | hdisj
  · have heq' : (a, b) = (c, d) := congrArg Subtype.val heq
    have hac := congrArg Prod.fst heq'
    have hbd := congrArg Prod.snd heq'
    dsimp at hac hbd
    subst c; subst d
    cases s <;> cases t
    · exact False.elim (hxy rfl)
    · exact tbjOm_rankOne_commute_rankOnePos hp2 hAΩ Δ hfix a b (ne_of_lt hab)
    · intro u hu v hv
      exact (tbjOm_rankOne_commute_rankOnePos hp2 hAΩ Δ hfix a b (ne_of_lt hab) v hv u hu).symm
    · exact False.elim (hxy rfl)
  · exact Δ.commute_signed_rankOne_of_disjoint hp2 hfix a b c d s t hdisj

theorem TBJOmData.pair_signed_le (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hAΩ : A ≤ orthDerived Q) (hr : 3 ≤ r)
    (hpq : p ∣ Nat.card K + 1)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (f : ℕ) (hf : Nat.card K = 2 ^ f)
    (K' : Type) [Field K'] [Finite K'] [CharP K' 2]
    (hK' : Nat.card K' = (2 ^ f) ^ 2)
    {a b c : Fin r} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (s t : Bool) :
    ∃ W : Subgroup (V ≃ₗ[K] V), W ≤ orthDerived Q ⊓ Subgroup.centralizer
        (((if s then Δ.reflFixedPos a b else Δ.reflFixed a b) ⊓
          (if t then Δ.reflFixedPos b c else Δ.reflFixed b c) :
          Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) ∧
      UnitaryBlockStandardPair K' 2 f W
        (if s then Δ.rankOnePos a b else Δ.rankOne a b)
        (if t then Δ.rankOnePos b c else Δ.rankOne b c) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hbase := tbjOm_pair_model_le hp2 hAΩ Δ hr hpq hfix f hf K' hK'
  have hconj : ∀ (W H H' : Subgroup (V ≃ₗ[K] V)) (w : V ≃ₗ[K] V),
      W ≤ orthDerived Q ⊓ Subgroup.centralizer (H : Set (V ≃ₗ[K] V)) →
      w ∈ orthDerived Q → H.map (MulAut.conj w).toMonoidHom = H' →
      W.map (MulAut.conj w).toMonoidHom ≤
        orthDerived Q ⊓ Subgroup.centralizer (H' : Set (V ≃ₗ[K] V)) := by
    intro W H H' w hW hw hH
    apply le_inf
    · rintro _ ⟨z, hz, rfl⟩
      change w * z * w⁻¹ ∈ orthDerived Q
      exact (orthDerived Q).mul_mem ((orthDerived Q).mul_mem hw (hW hz).1)
        ((orthDerived Q).inv_mem hw)
    · rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [← hH] at hh
      obtain ⟨u, hu, rfl⟩ := hh
      have hcomm := (Subgroup.mem_centralizer_iff.mp (hW hz).2) u hu
      simpa only [map_mul] using congrArg (MulAut.conj w).toMonoidHom hcomm
  have hmixed : ∀ {a b c : Fin r}, a ≠ b → b ≠ c → a ≠ c →
      ∃ W : Subgroup (V ≃ₗ[K] V), W ≤ orthDerived Q ⊓ Subgroup.centralizer
          ((Δ.reflFixed a b ⊓ Δ.reflFixedPos b c : Subgroup (V ≃ₗ[K] V)) :
            Set (V ≃ₗ[K] V)) ∧
        UnitaryBlockStandardPair K' 2 f W (Δ.rankOne a b) (Δ.rankOnePos b c) := by
    intro a b c hab hbc hac
    obtain ⟨W, hWΩ, hW⟩ := hbase a b c hab hbc hac
    obtain ⟨w, hwΩ, _, hwconj⟩ := Δ.dinvMove a b hab
    have hU := Δ.rankOne_map_dinv_self hab w hwΩ hwconj
    have hwconj' : ∀ g, w * Δ.τ g * w⁻¹ = Δ.τ (NbrOrth.dinv b a g) := by
      intro g
      rw [hwconj]
      congr 1
      funext l
      simp only [OrthNs.dinv_apply_eq, if_neg hab, if_neg hab.symm, or_comm]
    have hV := Δ.rankOne_map_dinv (i := c) (j := b) (k := a)
      hbc.symm hab.symm hac.symm w hwΩ hwconj'
    rw [Δ.rankOne_comm_index c b, Δ.rankOnePos_comm_index c b] at hV
    have hH₀ := Δ.reflFixed_map_dinv_self hab w hwconj
    have hH₁ := Δ.reflFixed_map_dinv (i := c) (j := b) (k := a)
      hbc.symm hab.symm hac.symm w hwconj'
    rw [Δ.reflFixed_comm_index c b, Δ.reflFixedPos_comm_index c b] at hH₁
    have hH : (Δ.reflFixed a b ⊓ Δ.reflFixed b c).map
        (MulAut.conj w).toMonoidHom = Δ.reflFixed a b ⊓ Δ.reflFixedPos b c := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj w).injective, hH₀, hH₁]
    have hpair := CFSG.GH74.L5U5.unitaryBlockStandardPair_map' hW
      (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
    rw [hU, hV] at hpair
    exact ⟨W.map (MulAut.conj w).toMonoidHom, hconj W _ _ w hWΩ hwΩ hH, hpair⟩
  cases s <;> cases t
  · exact hbase a b c hab hbc hac
  · exact hmixed hab hbc hac
  · obtain ⟨W, hWΩ, hW⟩ := hmixed hbc.symm hab.symm hac.symm
    rw [Δ.rankOne_comm_index c b, Δ.rankOnePos_comm_index b a] at hW
    rw [Δ.reflFixed_comm_index c b, Δ.reflFixedPos_comm_index b a,
      inf_comm (Δ.reflFixed b c)] at hWΩ
    exact ⟨W, hWΩ, CFSG.ClassicalInvolution.Models.OrthogonalPairs.unitaryBlockStandardPair_swap hW⟩
  · obtain ⟨W, hWΩ, hW⟩ := hbase a b c hab hbc hac
    obtain ⟨w, hwΩ, _, hwconj⟩ := Δ.dinvMove a c hac
    have hU := Δ.rankOne_map_dinv (i := b) (j := a) (k := c)
      hab.symm hac hbc w hwΩ hwconj
    rw [Δ.rankOne_comm_index b a, Δ.rankOnePos_comm_index b a] at hU
    have hwconj' : ∀ g, w * Δ.τ g * w⁻¹ = Δ.τ (NbrOrth.dinv c a g) := by
      intro g
      rw [hwconj]
      congr 1
      funext l
      simp only [OrthNs.dinv_apply_eq, if_neg hac, if_neg hac.symm, or_comm]
    have hV := Δ.rankOne_map_dinv (i := b) (j := c) (k := a)
      hbc hac.symm hab.symm w hwΩ hwconj'
    have hH₀ := Δ.reflFixed_map_dinv (i := b) (j := a) (k := c)
      hab.symm hac hbc w hwconj
    rw [Δ.reflFixed_comm_index b a, Δ.reflFixedPos_comm_index b a] at hH₀
    have hH₁ := Δ.reflFixed_map_dinv (i := b) (j := c) (k := a)
      hbc hac.symm hab.symm w hwconj'
    have hH : (Δ.reflFixed a b ⊓ Δ.reflFixed b c).map
        (MulAut.conj w).toMonoidHom = Δ.reflFixedPos a b ⊓ Δ.reflFixedPos b c := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj w).injective, hH₀, hH₁]
    have hpair := CFSG.GH74.L5U5.unitaryBlockStandardPair_map' hW
      (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
    rw [hU, hV] at hpair
    exact ⟨W.map (MulAut.conj w).toMonoidHom, hconj W _ _ w hWΩ hwΩ hH, hpair⟩

theorem TBJOmData.pair_signed_rankOne_of_refl_not_commute (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hAΩ : A ≤ orthDerived Q) (hr : 3 ≤ r)
    (hpq : p ∣ Nat.card K + 1)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (f : ℕ) (hf : Nat.card K = 2 ^ f)
    (K' : Type) [Field K'] [Finite K'] [CharP K' 2]
    (hK' : Nat.card K' = (2 ^ f) ^ 2)
    (x y : OmPlusIdx r)
    (hcomm : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x) :
    ∃ W : Subgroup (V ≃ₗ[K] V), W ≤ orthDerived Q ⊓ Subgroup.centralizer
        (((if x.2 then Δ.reflFixedPos x.1.1.1 x.1.1.2 else Δ.reflFixed x.1.1.1 x.1.1.2) ⊓
          (if y.2 then Δ.reflFixedPos y.1.1.1 y.1.1.2 else Δ.reflFixed y.1.1.1 y.1.1.2) :
          Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) ∧ UnitaryBlockStandardPair K' 2 f W
      (if x.2 then Δ.rankOnePos x.1.1.1 x.1.1.2 else Δ.rankOne x.1.1.1 x.1.1.2)
      (if y.2 then Δ.rankOnePos y.1.1.1 y.1.1.2 else Δ.rankOne y.1.1.1 y.1.1.2) := by
  classical
  have hmodel := fun {a b c : Fin r} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) =>
    Δ.pair_signed_le hp2 hAΩ hr hpq hfix f hf K' hK' hab hbc hac
  have hneq : x.1 ≠ y.1 := fun h => hcomm (omPlusRefl_commute_of_supports x y (Or.inl h))
  have hndisj : ¬Disjoint ({x.1.1.1, x.1.1.2} : Finset (Fin r))
      {y.1.1.1, y.1.1.2} := fun h => hcomm (omPlusRefl_commute_of_supports x y (Or.inr h))
  rcases x with ⟨⟨⟨a, b⟩, hab⟩, s⟩
  rcases y with ⟨⟨⟨c, d⟩, hcd⟩, t⟩
  have habne : a ≠ b := ne_of_lt hab
  have hcdne : c ≠ d := ne_of_lt hcd
  by_cases hac : a = c
  · subst c
    have hbd : b ≠ d := by intro h; subst d; exact hneq rfl
    obtain ⟨W, hWΩ, hW⟩ := hmodel habne.symm hcdne hbd s t
    rw [Δ.rankOne_comm_index b a, Δ.rankOnePos_comm_index b a] at hW
    rw [Δ.reflFixed_comm_index b a, Δ.reflFixedPos_comm_index b a] at hWΩ
    exact ⟨W, hWΩ, hW⟩
  by_cases had : a = d
  · subst d
    have hbc : b ≠ c := ne_of_gt (hcd.trans hab)
    obtain ⟨W, hWΩ, hW⟩ := hmodel habne.symm hcdne.symm hbc s t
    rw [Δ.rankOne_comm_index b a, Δ.rankOnePos_comm_index b a,
      Δ.rankOne_comm_index a c, Δ.rankOnePos_comm_index a c] at hW
    rw [Δ.reflFixed_comm_index b a, Δ.reflFixedPos_comm_index b a,
      Δ.reflFixed_comm_index a c, Δ.reflFixedPos_comm_index a c] at hWΩ
    exact ⟨W, hWΩ, hW⟩
  by_cases hbc : b = c
  · subst c
    obtain ⟨W, hWΩ, hW⟩ := hmodel habne hcdne had s t
    exact ⟨W, hWΩ, hW⟩
  by_cases hbd : b = d
  · subst d
    obtain ⟨W, hWΩ, hW⟩ := hmodel habne hcdne.symm hac s t
    rw [Δ.rankOne_comm_index b c, Δ.rankOnePos_comm_index b c] at hW
    rw [Δ.reflFixed_comm_index b c, Δ.reflFixedPos_comm_index b c] at hWΩ
    exact ⟨W, hWΩ, hW⟩
  exact False.elim (hndisj (by simp [Finset.disjoint_left, hac, had, hbc, hbd]))

theorem TBJOmData.pair_signed_rankOne_forall_fields (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hAΩ : A ≤ orthDerived Q) (hr : 3 ≤ r)
    (hpq : p ∣ Nat.card K + 1)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (f : ℕ) (hf : Nat.card K = 2 ^ f) (x y : OmPlusIdx r)
    (hcomm : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x) :
    ∃ W : Subgroup (V ≃ₗ[K] V), W ≤ orthDerived Q ⊓ Subgroup.centralizer
        (((if x.2 then Δ.reflFixedPos x.1.1.1 x.1.1.2 else Δ.reflFixed x.1.1.1 x.1.1.2) ⊓
          (if y.2 then Δ.reflFixedPos y.1.1.1 y.1.1.2 else Δ.reflFixed y.1.1.1 y.1.1.2) :
          Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) ∧
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f' : ℕ),
        Nat.card F = (2 ^ f') ^ 2 →
        Nat.card ↥(if x.2 then Δ.rankOnePos x.1.1.1 x.1.1.2
          else Δ.rankOne x.1.1.1 x.1.1.2) = 2 ^ f' * ((2 ^ f') ^ 2 - 1) →
        UnitaryBlockStandardPair F 2 f' W
          (if x.2 then Δ.rankOnePos x.1.1.1 x.1.1.2 else Δ.rankOne x.1.1.1 x.1.1.2)
          (if y.2 then Δ.rankOnePos y.1.1.1 y.1.1.2 else Δ.rankOne y.1.1.1 y.1.1.2) := by
  have hf0 : f ≠ 0 := by
    intro h
    have hc := Finite.one_lt_card (α := K)
    rw [hf, h] at hc
    norm_num at hc
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have : NeZero (2 * f) := ⟨Nat.mul_ne_zero (by decide) hf0⟩
  let F₀ := GaloisField 2 (2 * f)
  have hF₀ : Nat.card F₀ = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (NeZero.ne (2 * f)), Nat.mul_comm 2 f, pow_mul]
  obtain ⟨W, hWΩ, hW⟩ :=
    Δ.pair_signed_rankOne_of_refl_not_commute hp2 hAΩ hr hpq hfix f hf F₀ hF₀ x y hcomm
  refine ⟨W, hWΩ, ?_⟩
  intro F _ _ _ f' hF hU
  exact ggPhanNSAPairAux_stdPair_of_card hF₀ hF hW hU
end OrthTorus
end CFSG.StandardType
end
