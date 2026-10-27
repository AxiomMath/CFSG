module

public import CFSG.Quasithin.Background.RonanH44Orth
public import CFSG.Quasithin.Background.RonanH46Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3
  CFSG.Quasithin.SteinbergCB Matrix CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private def ozConjSemi {F F' : Type} [Field F] [Field F'] (ψ : F ≃+* F')
    (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) : (Fin 4 → F') ≃ₗ[F'] (Fin 4 → F') where
  toFun x := fun i => ψ (g (fun j => ψ.symm (x j)) i)
  invFun x := fun i => ψ (g.symm (fun j => ψ.symm (x j)) i)
  map_add' x y := by
    have hv : (fun j => ψ.symm (x j + y j)) =
        (fun j => ψ.symm (x j)) + (fun j => ψ.symm (y j)) := by
      funext j
      simp
    funext i
    show ψ (g (fun j => ψ.symm (x j + y j)) i) =
      ψ (g (fun j => ψ.symm (x j)) i) + ψ (g (fun j => ψ.symm (y j)) i)
    rw [hv, LinearEquiv.map_add, Pi.add_apply, map_add]
  map_smul' c x := by
    have hv : (fun j => ψ.symm (c • x j)) = ψ.symm c • (fun j => ψ.symm (x j)) := by
      funext j
      simp [smul_eq_mul]
    funext i
    show ψ (g (fun j => ψ.symm (c • x j)) i) = c • ψ (g (fun j => ψ.symm (x j)) i)
    rw [hv, LinearEquiv.map_smul]
    simp [smul_eq_mul]
  left_inv x := by
    have hv : (fun j => ψ.symm (ψ (g (fun k => ψ.symm (x k)) j))) =
        g (fun k => ψ.symm (x k)) := by
      funext j
      simp
    funext i
    show ψ (g.symm (fun j => ψ.symm (ψ (g (fun k => ψ.symm (x k)) j))) i) = x i
    rw [hv, LinearEquiv.symm_apply_apply]
    simp
  right_inv x := by
    have hv : (fun j => ψ.symm (ψ (g.symm (fun k => ψ.symm (x k)) j))) =
        g.symm (fun k => ψ.symm (x k)) := by
      funext j
      simp
    funext i
    show ψ (g (fun j => ψ.symm (ψ (g.symm (fun k => ψ.symm (x k)) j))) i) = x i
    rw [hv, LinearEquiv.apply_symm_apply]
    simp

private theorem ozConjSemi_apply {F F' : Type} [Field F] [Field F'] (ψ : F ≃+* F')
    (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (x : Fin 4 → F') :
    ozConjSemi ψ g x = fun i => ψ (g (fun j => ψ.symm (x j)) i) :=
  rfl

private def ozConjHom {F F' : Type} [Field F] [Field F'] (ψ : F ≃+* F') :
    ((Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) →* ((Fin 4 → F') ≃ₗ[F'] (Fin 4 → F')) where
  toFun g := ozConjSemi ψ g
  map_one' := by
    apply LinearEquiv.ext
    intro x
    funext i
    simp [ozConjSemi_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    funext i
    simp [ozConjSemi_apply]

private theorem ozConjSemi_ozConjSemi_symm {F F' : Type} [Field F] [Field F'] (ψ : F ≃+* F')
    (g : (Fin 4 → F') ≃ₗ[F'] (Fin 4 → F')) : ozConjSemi ψ (ozConjSemi ψ.symm g) = g := by
  apply LinearEquiv.ext
  intro x
  funext i
  simp [ozConjSemi_apply]

private theorem ozConjSemi_mem {F F' : Type} [Field F] [Field F'] (ψ : F ≃+* F')
    {Q : (Fin 4 → F) → F} {Q' : (Fin 4 → F') → F'}
    (hQ : ∀ x : Fin 4 → F, Q' (fun i => ψ (x i)) = ψ (Q x))
    {g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)} (hg : g ∈ CFSG.Quasithin.H11Proof.isometryGroup F Q) :
    ozConjSemi ψ g ∈ CFSG.Quasithin.H11Proof.isometryGroup F' Q' := by
  have hg' : ∀ y : Fin 4 → F, Q (g y) = Q y := hg
  show ∀ x' : Fin 4 → F', Q' (ozConjSemi ψ g x') = Q' x'
  intro x'
  obtain ⟨y, rfl⟩ : ∃ y : Fin 4 → F, x' = fun i => ψ (y i) :=
    ⟨fun j => ψ.symm (x' j), by funext i; simp⟩
  have hconj : ozConjSemi ψ g (fun i => ψ (y i)) = fun i => ψ (g y i) := by
    funext i
    simp [ozConjSemi_apply]
  rw [hconj, hQ (g y), hQ y, hg' y]

private theorem ozMap_conjHom {F F' : Type} [Field F] [Field F'] (ψ : F ≃+* F')
    {Q : (Fin 4 → F) → F} {Q' : (Fin 4 → F') → F'}
    (hQ : ∀ x : Fin 4 → F, Q' (fun i => ψ (x i)) = ψ (Q x)) :
    (CFSG.Quasithin.H11Proof.isometryGroup F Q).map (ozConjHom ψ) =
      CFSG.Quasithin.H11Proof.isometryGroup F' Q' := by
  have hQ' : ∀ y : Fin 4 → F', Q (fun i => ψ.symm (y i)) = ψ.symm (Q' y) := by
    intro y
    have h0 : (fun i => ψ (ψ.symm (y i))) = y := by
      funext i
      simp
    have h1 := hQ (fun i => ψ.symm (y i))
    rw [h0] at h1
    rw [h1, RingEquiv.symm_apply_apply]
  ext x'
  constructor
  · intro hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
    exact ozConjSemi_mem ψ hQ hg
  · intro hx
    exact Subgroup.mem_map.2 ⟨ozConjSemi ψ.symm x', ozConjSemi_mem ψ.symm hQ' hx,
      ozConjSemi_ozConjSemi_symm ψ x'⟩

private theorem ozCongr_comp_linToMulAut {F F' : Type} [Field F] [Field F'] (ψ : F ≃+* F') :
    (MulAut.congr (AddEquiv.toMultiplicative
        (AddEquiv.piCongrRight (fun _ : Fin 4 => ψ.toAddEquiv)))).toMonoidHom.comp
      (CFSG.Quasithin.H11Proof.linToMulAut F (Fin 4 → F)) =
    (CFSG.Quasithin.H11Proof.linToMulAut F' (Fin 4 → F')).comp (ozConjHom ψ) :=
  MonoidHom.ext fun g => MulEquiv.ext fun y => rfl

theorem map_omegaFour_ringEquiv {F F' : Type} [Field F] [Field F'] (ψ : F ≃+* F')
    (Q : (Fin 4 → F) → F) (Q' : (Fin 4 → F') → F')
    (hQ : ∀ x : Fin 4 → F, Q' (fun i => ψ (x i)) = ψ (Q x)) :
    (CFSG.Quasithin.H11Proof.omegaFour F Q).map
        (MulAut.congr (AddEquiv.toMultiplicative
          (AddEquiv.piCongrRight (fun _ : Fin 4 => ψ.toAddEquiv)))).toMonoidHom =
      CFSG.Quasithin.H11Proof.omegaFour F' Q' := by
  unfold CFSG.Quasithin.H11Proof.omegaFour
  rw [← ozMap_conjHom ψ hQ, ← Subgroup.map_commutator, Subgroup.map_map, Subgroup.map_map,
    ozCongr_comp_linToMulAut ψ]

theorem inducesOn_map_equiv {V : Type*} [CommGroup V] {A A' : Type*} [CommGroup A] [CommGroup A']
    (e : A ≃* A') {G : Subgroup (MulAut V)} {U Z : Subgroup V} {Γ : Subgroup (MulAut A)}
    (h : InducesOnR G U Z A Γ) :
    InducesOnR G U Z A' (Γ.map (MulAut.congr e).toMonoidHom) := by
  obtain ⟨hZU, hGU, hGZ, β, hsurj, hker, hΓ, hΓ'⟩ := h
  refine ⟨hZU, hGU, hGZ, e.toMonoidHom.comp β, e.surjective.comp hsurj, ?_, ?_, ?_⟩
  · intro u
    show e (β u) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact hker u
  · intro g hg
    obtain ⟨γ, hγ, hγβ⟩ := hΓ g hg
    refine ⟨MulAut.congr e γ, Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩, fun u u' huu' => ?_⟩
    show e (β u') = e (γ (e.symm (e (β u))))
    rw [e.symm_apply_apply, hγβ u u' huu']
  · intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
    obtain ⟨g, hg, hgβ⟩ := hΓ' γ hγ
    refine ⟨g, hg, fun u u' huu' => ?_⟩
    show e (β u') = e (γ (e.symm (e (β u))))
    rw [e.symm_apply_apply, hgβ u u' huu']

theorem exists_ringEquiv_zmod2 {F : Type} [Field F] (hF : Nat.card F = 2) :
    Nonempty (F ≃+* ZMod 2) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  exact ⟨(ZMod.ringEquivOfPrime F Nat.prime_two (by rw [← Nat.card_eq_fintype_card, hF])).symm⟩

theorem inducesOn_of_nineOrth {n : ℕ} {F : Type} [Field F] {scalar : F →+* K} {a : F}
    {S : Subgroup (HMod n K)} {G : Subgroup (MulAut (HMod n K))} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hS : S = blkW n K) (hG : G = LW hK)
    (h : NineOrthBlk scalar a S G) :
    InducesOnR G S ⊥ (Multiplicative (Fin 4 → F))
      (CFSG.Quasithin.H11Proof.omegaFour F (CFSG.Quasithin.H11Proof.orthMinus F a)) := by
  subst hS hG
  obtain ⟨coordinates, -, -, hG1, hG2⟩ := h
  refine ⟨bot_le, ?_, fun g _ z hz => ?_, coordinates.toMonoidHom, coordinates.surjective,
    ?_, ?_, ?_⟩
  · intro g hg u hu
    obtain ⟨g₀, hg₀, rfl⟩ := mem_LW hg
    exact (hermBlk_rho hn hK ⟨hg₀.1, hg₀.2.1⟩ hu).1
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro u
    show coordinates u = 1 ↔ (u : HMod n K) ∈ (⊥ : Subgroup (HMod n K))
    rw [Subgroup.mem_bot]
    constructor
    · intro hu
      have hu1 : u = 1 := coordinates.injective (hu.trans (map_one coordinates).symm)
      simp [hu1]
    · intro hu
      have hu1 : u = 1 := Subtype.ext hu
      simp [hu1]
  · intro g hg
    obtain ⟨γ, hγ, hγ'⟩ := hG1 g hg
    exact ⟨γ, hγ, fun u u' huu' => hγ' u u' huu'⟩
  · intro γ hγ
    obtain ⟨g, hg, hg'⟩ := hG2 γ hγ
    exact ⟨g, hg, fun u u' huu' => hg' u u' huu'⟩

theorem part2a (hK : Nat.card K = (2 ^ 1) ^ 2) :
    InducesOnR (LW hK) (blkW 1 K) ⊥ (Multiplicative (Fin 4 → ZMod 2))
      (CFSG.Quasithin.H11Proof.omegaFour (ZMod 2)
        (CFSG.Quasithin.H11Proof.orthMinus (ZMod 2) 1)) := by
  obtain ⟨F, hFi, hcard, scalar, a, -, hpoly, hNine⟩ :=
    nineOrth_exists (n := 1) (S := blkW 1 K) (G := LW hK) le_rfl hK rfl rfl
  obtain ⟨ψ⟩ := exists_ringEquiv_zmod2 (F := F) (by rw [hcard, pow_one])
  have ha0 : a ≠ 0 := fun h0 => hpoly 0 (by simp [h0])
  have hψ0 : ψ a ≠ 0 := fun h0 => ha0 (ψ.injective (by rw [h0, map_zero]))
  have ha : ψ a = 1 := by
    have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact key _ hψ0
  have hQ : ∀ x : Fin 4 → F,
      CFSG.Quasithin.H11Proof.orthMinus (ZMod 2) (ψ a) (fun i => ψ (x i)) =
        ψ (CFSG.Quasithin.H11Proof.orthMinus F a x) := by
    intro x
    simp only [CFSG.Quasithin.H11Proof.orthMinus, map_add, map_mul, map_pow]
  have h := inducesOn_map_equiv
    (AddEquiv.toMultiplicative (AddEquiv.piCongrRight (fun _ : Fin 4 => ψ.toAddEquiv)))
    (inducesOn_of_nineOrth (S := blkW 1 K) (G := LW hK) le_rfl hK rfl rfl hNine)
  have key := map_omegaFour_ringEquiv ψ (CFSG.Quasithin.H11Proof.orthMinus F a)
    (CFSG.Quasithin.H11Proof.orthMinus (ZMod 2) (ψ a)) hQ
  rw [ha] at key
  rw [← key]
  exact h

end CFSG.Quasithin.RonanH46
