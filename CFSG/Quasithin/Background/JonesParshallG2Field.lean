module

public import CFSG.Quasithin.Background.JonesParshallG2TwoH1
public import CFSG.Quasithin.Background.JonesParshallG2Derived
public import Certificates.Certificate17028
public import Certificates.Certificate8952
public import Certificates.Certificate8953

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit CFSG.Open

section RingEquiv

variable {F F' : Type} [Field F] [Field F'] (e : F ≃+* F')

@[expose] def zornMap (x : quasithinZorn F) : quasithinZorn F' :=
  (e x.1, fun i => e (x.2.1 i), fun i => e (x.2.2.1 i), e x.2.2.2)

theorem zornMap_symm_apply (x : quasithinZorn F) : zornMap e.symm (zornMap e x) = x := by
  simp [zornMap]

theorem zornMap_apply_symm (y : quasithinZorn F') : zornMap e (zornMap e.symm y) = y := by
  simp [zornMap]

theorem zornMap_add (x y : quasithinZorn F) : zornMap e (x + y) = zornMap e x + zornMap e y := by
  simp only [zornMap, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, Prod.mk_add_mk]
  rfl

theorem zornMap_smul (c : F) (x : quasithinZorn F) : zornMap e (c • x) = e c • zornMap e x := by
  simp only [zornMap, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul,
    Prod.smul_mk]
  rfl

theorem zornMap_one : zornMap e (cayleyOne F) = cayleyOne F' := by
  simp only [zornMap, cayleyOne, map_one, Pi.zero_apply, map_zero]
  rfl

theorem zornMap_mul (x y : quasithinZorn F) :
    zornMap e (cayleyMul x y) = cayleyMul (zornMap e x) (zornMap e y) := by
  simp only [zornMap, cayleyMul, quasithinCross, Fin.sum_univ_three, map_add, map_mul,
    Prod.mk.injEq]
  refine ⟨trivial, ?_, ?_, trivial⟩ <;> funext i <;> fin_cases i <;> simp

theorem cayleyTr_zornMap (x : quasithinZorn F) : cayleyTr (zornMap e x) = e (cayleyTr x) := by
  simp [zornMap, cayleyTr]

theorem cayleyNorm_zornMap (x : quasithinZorn F) :
    cayleyNorm (zornMap e x) = e (cayleyNorm x) := by
  simp [zornMap, cayleyNorm, Fin.sum_univ_three]

@[expose] def zornConjFun (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) :
    quasithinZorn F' ≃ₗ[F'] quasithinZorn F' where
  toFun y := zornMap e (g (zornMap e.symm y))
  invFun y := zornMap e (g.symm (zornMap e.symm y))
  map_add' y y' := by rw [zornMap_add, map_add, zornMap_add]
  map_smul' c y := by
    rw [zornMap_smul, map_smul, zornMap_smul, RingEquiv.apply_symm_apply, RingHom.id_apply]
  left_inv y := by
    simp only [zornMap_symm_apply, LinearEquiv.symm_apply_apply, zornMap_apply_symm]
  right_inv y := by
    simp only [zornMap_symm_apply, LinearEquiv.apply_symm_apply, zornMap_apply_symm]

@[expose] def zornConj :
    (quasithinZorn F ≃ₗ[F] quasithinZorn F) ≃* (quasithinZorn F' ≃ₗ[F'] quasithinZorn F') where
  toFun := zornConjFun e
  invFun := zornConjFun e.symm
  left_inv g := LinearEquiv.ext fun x => by
    change zornMap e.symm (zornMap e (g (zornMap e.symm (zornMap e x)))) = g x
    rw [zornMap_symm_apply, zornMap_symm_apply]
  right_inv g := LinearEquiv.ext fun y => by
    change zornMap e (zornMap e.symm (g (zornMap e (zornMap e.symm y)))) = g y
    rw [zornMap_apply_symm, zornMap_apply_symm]
  map_mul' g h := LinearEquiv.ext fun y => by
    change zornMap e (g (h (zornMap e.symm y))) =
      zornMap e (g (zornMap e.symm (zornMap e (h (zornMap e.symm y)))))
    rw [zornMap_symm_apply]

theorem zornConj_apply (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) (y : quasithinZorn F') :
    zornConj e g y = zornMap e (g (zornMap e.symm y)) := rfl

theorem zornConj_mem {g : quasithinZorn F ≃ₗ[F] quasithinZorn F} (hg : g ∈ cayleyGroup F) :
    zornConj e g ∈ cayleyGroup F' := by
  obtain ⟨h1, hm, ht, hn⟩ := hg
  refine ⟨?_, fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · rw [zornConj_apply, zornMap_one e.symm, h1, zornMap_one]
  · rw [zornConj_apply, zornMap_mul e.symm, hm, zornMap_mul, ← zornConj_apply, ← zornConj_apply]
  · rw [zornConj_apply, cayleyTr_zornMap, ht, cayleyTr_zornMap, RingEquiv.apply_symm_apply]
  · rw [zornConj_apply, cayleyNorm_zornMap, hn, cayleyNorm_zornMap, RingEquiv.apply_symm_apply]

theorem map_cayleyGroup :
    (cayleyGroup F).map (zornConj e : (quasithinZorn F ≃ₗ[F] quasithinZorn F) →*
      (quasithinZorn F' ≃ₗ[F'] quasithinZorn F')) = cayleyGroup F' := by
  ext g'
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact zornConj_mem e hg
  · intro hg'
    exact ⟨(zornConj e).symm g', zornConj_mem e.symm hg', MulEquiv.apply_symm_apply _ _⟩

theorem map_cayley_commutator :
    (⁅cayleyGroup F, cayleyGroup F⁆).map (zornConj e : (quasithinZorn F ≃ₗ[F] quasithinZorn F) →*
      (quasithinZorn F' ≃ₗ[F'] quasithinZorn F')) = ⁅cayleyGroup F', cayleyGroup F'⁆ := by
  rw [Subgroup.map_commutator, map_cayleyGroup]

theorem zornMap_symm_zI (w : Ix3 → F) :
    zornMap e.symm (zI fun i => e (w i)) = zI w := by
  rw [q6_eta w, zI_q6]
  simp only [zornMap, zI, zmk, map_zero, Prod.mk.injEq]
  refine ⟨trivial, ?_, ?_, trivial⟩ <;> funext i <;> fin_cases i <;> simp [q6]

theorem zP_zornMap (x : quasithinZorn F) : zP (zornMap e x) = fun i => e (zP x i) := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

theorem g2Act_zornConj [CharP F 2] [CharP F' 2] (g : ↥(cayleyGroup F)) (w : Ix3 → F) :
    (RingEquiv.piCongrRight fun _ : Ix3 => e) (g2Act g w) =
      g2Act ⟨zornConj e g, zornConj_mem e g.2⟩ ((RingEquiv.piCongrRight fun _ : Ix3 => e) w) := by
  change (fun i => e (g2Act g w i)) = zP (zornMap e ((g : quasithinZorn F ≃ₗ[F] quasithinZorn F)
    (zornMap e.symm (zI fun i => e (w i)))))
  rw [zornMap_symm_zI, zP_zornMap]
  rfl

end RingEquiv

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_G2Derived_two
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {ρ : Representation (ZMod 2) Γ W} (h : Explicit.G2Natural ρ F .derived) :
    Module.finrank (ZMod 2) (H1 ρ) = 1 := by
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  obtain ⟨θ, β, hβ⟩ := G2Natural.intertwiner h
  set e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hF).symm
  let θ' : Γ ≃* ↥subG2 := θ.trans (((zornConj e).subgroupMap _).trans
    (MulEquiv.subgroupCongr ((map_cayley_commutator e).trans g2Two_commutator_eq)))
  let β' : W ≃+ (Ix3 → ZMod 2) := β.trans (RingEquiv.piCongrRight fun _ : Ix3 => e).toAddEquiv
  have hβ' : ∀ γ w, β' (ρ γ w) = muK (θ' γ) (β' w) := fun γ w => by
    change (RingEquiv.piCongrRight fun _ : Ix3 => e) (β (ρ γ w)) =
      muK (θ' γ) ((RingEquiv.piCongrRight fun _ : Ix3 => e) (β w))
    rw [hβ, g2Act_zornConj]
    rfl
  have : Finite Γ := Finite.of_equiv _ θ'.toEquiv.symm
  have : Finite W := Finite.of_equiv _ β'.toEquiv.symm
  apply finrank_H1_of_card
  rw [card_H1_eq_of_card ρ hβ' card_Z1A_K, pow_one]

theorem finrank_H1_G2Derived
    {F : Type} [Field F] [Fintype F] {a : ℕ}
    (hF : Fintype.card F = 2 ^ a) (ha : 0 < a) {ρ : Representation (ZMod 2) Γ W}
    (h : Explicit.G2Natural ρ F .derived) : Module.finrank (ZMod 2) (H1 ρ) = a := by
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  rcases Nat.lt_or_ge 1 a with h1 | h1
  · exact finrank_H1_G2Derived_of_one_lt hF h1 h
  · have ha1 : a = 1 := le_antisymm h1 ha
    subst ha1
    exact finrank_H1_G2Derived_two (by rw [hF, pow_one]) h

end CFSG.Quasithin.JonesParshall
