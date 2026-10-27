module

public import CFSG.Quasithin.Background.F918Z4d
public import CFSG.Quasithin.Background.F918Z4bDef
public import CFSG.Quasithin.Background.F918Z6Symm

public section

namespace CFSG.Quasithin

namespace Z7a

variable {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)}

theorem z37_of_swap {s t : MulAut V} (hZ : Z37 D X G T' s) (htT : t ∈ T') (ht2 : t * t = 1)
    (htX : D.map (MulAut.conj t).toMonoidHom = X) : Z37 D X G T' t where
  exp := hZ.exp
  nontrivial := hZ.nontrivial
  simple := hZ.simple
  nonab := hZ.nonab
  typeD := hZ.typeD
  sqtkD := hZ.sqtkD
  comm := hZ.comm
  swapDX := htX.symm
  swapXD := by
    rw [← htX, map_conj_map_conj_z6, ht2, Z4d.map_conj_one]
  s_mem := htT
  DX_le := hZ.DX_le
  G_eq := hZ.G_eq
  DX_norm := hZ.DX_norm
  T_perm := hZ.T_perm
  T_sylow := hZ.T_sylow
  irr := hZ.irr
  qhat := hZ.qhat

theorem rk_inf_normalizer_le {t : MulAut V} (hZ : Z37 D X G T' t)
    {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) (htA : t ∈ A) {m : ℕ}
    (hAut : AutRankLe ↥D m) : rk ↥(A ⊓ Subgroup.normalizer (D : Set (MulAut V))) ≤ m := by
  set N : Subgroup (MulAut V) := Subgroup.normalizer (D : Set (MulAut V)) with hN
  let ψ : ↥(A ⊓ N) →* MulAut ↥D := D.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hker : Subgroup.inclusion inf_le_right a ∈ D.normalizerMonoidHom.ker :=
      MonoidHom.mem_ker.mpr ha
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff] at hker
    have haA : (a : MulAut V) ∈ A := a.2.1
    have ha2 : (a : MulAut V) * a = 1 := by
      have := hA.2 a haA
      rwa [pow_two] at this
    have hD : ∀ y ∈ D, (a : MulAut V) * y = y * a := fun y hy => (hker y hy).symm
    have hat : (a : MulAut V) * t = t * a := hA.1 a haA t htA
    have hX : ∀ x ∈ X, (a : MulAut V) * x = x * a := by
      intro x hx
      rw [hZ.swapDX] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have h1 : Commute (a : MulAut V) t := hat
      have h2 : Commute (a : MulAut V) y := hD y hy
      exact (h1.mul_right h2).mul_right h1.inv_right
    exact Subtype.ext (Z4d.eq_one_of_commutes hZ ha2 hD hX)
  have hel : IsElemAb2 (⊤ : Subgroup ↥(A ⊓ N)) := by
    refine ⟨fun a _ b _ => Subtype.ext (hA.1 a a.2.1 b b.2.1), fun a _ => Subtype.ext ?_⟩
    exact hA.2 a a.2.1
  have h1 : rk ((⊤ : Subgroup ↥(A ⊓ N)).map ψ) ≤ m := hAut _ (hel.map ψ)
  have h2 : rk ((⊤ : Subgroup ↥(A ⊓ N)).map ψ) = rk ↥(A ⊓ N) := by
    unfold rk
    rw [Nat.card_congr (Subgroup.equivMapOfInjective ⊤ ψ hψ).toEquiv.symm]
    exact congrArg _ (Nat.card_congr Subgroup.topEquiv.toEquiv)
  rwa [h2] at h1

theorem le_two_mul_add_one_of_swap {t : MulAut V} (hZ : Z37 D X G T' t) (ht2 : t * t = 1)
    {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) (htA : t ∈ A)
    (hperm : ∀ a ∈ A, D.map (MulAut.conj a).toMonoidHom = D ∨
      D.map (MulAut.conj a).toMonoidHom = X)
    (hAV : rkIdx (fixV A) ≤ 2 * rk A) {m : ℕ} (hm : 1 ≤ m) (hAut : AutRankLe ↥D m) {B : ℕ}
    (hB : B ≤ rkIdx (fixV (Subgroup.zpowers t))) : B ≤ 2 * m + 1 := by
  have hrk : rk A = rk ↥(A ⊓ Subgroup.normalizer (D : Set (MulAut V))) + 1 :=
    Z4d.rk_eq_rk_normalizer_add_one hZ ht2 hA htA hperm
  have hle : rk ↥(A ⊓ Subgroup.normalizer (D : Set (MulAut V))) ≤ m :=
    rk_inf_normalizer_le hZ hA htA hAut
  by_cases hex : ∃ a ∈ A ⊓ Subgroup.normalizer (D : Set (MulAut V)), a ≠ 1
  · obtain ⟨a, ha, ha1⟩ := hex
    have haD : D.map (MulAut.conj a).toMonoidHom = D :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ha.2
    have := Z4d.rkIdx_fixV_succ_le_of_swap hZ ht2 hA htA ha.1 haD ha1
    omega
  · push Not at hex
    have hbot : A ⊓ Subgroup.normalizer (D : Set (MulAut V)) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr hex
    have h0 : rk ↥(A ⊓ Subgroup.normalizer (D : Set (MulAut V))) = 0 := by
      rw [hbot]
      exact rk_bot
    have hfix : fixV A ≤ fixV (Subgroup.zpowers t) := fun w hw =>
      Z4d.mem_fixV_zpowers_iff.2 (hw t htA)
    have := rkIdx_anti hfix
    omega

end Z7a

end CFSG.Quasithin
