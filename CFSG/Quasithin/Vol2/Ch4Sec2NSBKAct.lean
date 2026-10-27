module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKSD
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKCtil
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBCrit

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k n j : ℕ}

theorem exists_K_action_of_R (hIH : I ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hn : 0 < n) (hj : 0 < j) (D : StdData G T L I K m k n j) (r : G)
    (hr : r ∈ pCoreOf 2 I) :
    ∃ x : ↥K, (x : G)⁻¹ * r ∈ pCoreOf 2 (K ⊔ pCoreOf 2 I) ∧
      ∀ z z' : ↥(uZero I K), (z' : G) = r * z * r⁻¹ → ∀ i : Fin j,
        Multiplicative.toAdd (D.β z') i =
          ((D.α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
            (Multiplicative.toAdd (D.β z) i) := by
  classical
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    (pCoreOf_le 2 I).trans (hIH.trans hHK)
  have hrK : r ∈ Subgroup.normalizer (K : Set G) := hRK hr
  have hnormU : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (uZero I K : Set G) :=
    le_normalizer_uZero hIH hHK
  have hrU : r ∈ Subgroup.normalizer (uZero I K : Set G) := hnormU (Subgroup.mem_sup_right hr)
  have hrU' : r⁻¹ ∈ Subgroup.normalizer (uZero I K : Set G) := Subgroup.inv_mem _ hrU
  let crK : ↥K →* ↥K :=
    { toFun := fun x => ⟨r * x * r⁻¹, (Subgroup.mem_normalizer_iff.mp hrK _).mp x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp [mul_assoc] }
  let cr : ↥(uZero I K) → ↥(uZero I K) := fun z =>
    ⟨r * z * r⁻¹, (Subgroup.mem_normalizer_iff.mp hrU _).mp z.2⟩
  let cr' : ↥(uZero I K) → ↥(uZero I K) := fun z =>
    ⟨r⁻¹ * z * r⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp hrU' _).mp z.2⟩
  have hcrcr' : ∀ z, cr' (cr z) = z := fun z => Subtype.ext (by simp [cr, cr', mul_assoc])
  have hcr'cr : ∀ z, cr (cr' z) = z := fun z => Subtype.ext (by simp [cr, cr', mul_assoc])
  have hcrmul : ∀ z z', cr (z * z') = cr z * cr z' := fun z z' =>
    Subtype.ext (by simp [cr, mul_assoc])
  have hcr'mul : ∀ z z', cr' (z * z') = cr' z * cr' z' := fun z z' =>
    Subtype.ext (by simp [cr', mul_assoc])
  let eβ : ↥(uZero I K) ≃* Multiplicative (Fin j → Fin n → ZMod 2) :=
    MulEquiv.ofBijective D.β D.bij
  let Φ : (Fin j → Fin n → ZMod 2) ≃+ (Fin j → Fin n → ZMod 2) :=
    { toFun := fun t => Multiplicative.toAdd (eβ (cr (eβ.symm (Multiplicative.ofAdd t))))
      invFun := fun t => Multiplicative.toAdd (eβ (cr' (eβ.symm (Multiplicative.ofAdd t))))
      left_inv := fun t => by
        simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply, hcrcr', MulEquiv.apply_symm_apply,
          toAdd_ofAdd]
      right_inv := fun t => by
        simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply, hcr'cr, MulEquiv.apply_symm_apply,
          toAdd_ofAdd]
      map_add' := fun t t' => by
        simp only [ofAdd_add, map_mul, hcrmul, toAdd_mul] }
  have hΦ : ∀ (x : ↥K) (u : Fin j → Fin n → ZMod 2) (i : Fin j),
      Φ (fun j' => ((D.α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (u j'))
        i = (((D.α.comp crK) x : GL (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Φ u i) := by
    intro x u i
    set z : ↥(uZero I K) := eβ.symm (Multiplicative.ofAdd u) with hz
    have hxU : (x : G) ∈ Subgroup.normalizer (uZero I K : Set G) :=
      hnormU (Subgroup.mem_sup_left x.2)
    set z₂ : ↥(uZero I K) :=
      ⟨(x : G) * z * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hxU _).mp z.2⟩ with hz₂
    have hβz : D.β z = Multiplicative.ofAdd u := eβ.apply_symm_apply _
    have hz₂β : eβ z₂ = Multiplicative.ofAdd (fun j' =>
        ((D.α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (u j')) := by
      apply Multiplicative.toAdd.injective
      funext i'
      have h := D.equi x z z₂ rfl i'
      rw [hβz] at h
      exact h
    have hz₂' : eβ.symm (Multiplicative.ofAdd (fun j' =>
        ((D.α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (u j'))) = z₂ := by
      rw [← hz₂β]
      exact eβ.symm_apply_apply _
    have hconj : ((cr z₂ : ↥(uZero I K)) : G) =
        (crK x : G) * ((cr z : ↥(uZero I K)) : G) * (crK x : G)⁻¹ := by
      simp only [cr, crK, hz₂, MonoidHom.coe_mk, OneHom.coe_mk]
      group
    have h := D.equi (crK x) (cr z) (cr z₂) hconj i
    show Multiplicative.toAdd (eβ (cr (eβ.symm (Multiplicative.ofAdd (fun j' =>
        ((D.α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (u j')))))) i = _
    rw [hz₂']
    exact h
  obtain ⟨P, hP⟩ := natural_twist hn hj D.α (D.α.comp crK) D.surj Φ hΦ
  obtain ⟨x₀, hx₀⟩ := D.surj P
  set y : G := (x₀ : G)⁻¹ * r with hy
  have hyX : y ∈ K ⊔ pCoreOf 2 I :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (K.inv_mem x₀.2)) (Subgroup.mem_sup_right hr)
  have hycomm : ∀ k' ∈ K, y * k' * y⁻¹ * k'⁻¹ ∈ pCoreOf 2 K := by
    intro k' hk'
    set kk : ↥K := ⟨k', hk'⟩ with hkk
    set kk2 : ↥K := x₀⁻¹ * crK kk * x₀ with hkk2
    have hkk2G : (kk2 : G) = y * k' * y⁻¹ := by
      simp only [hkk2, crK, hy, hkk, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul,
        InvMemClass.coe_inv]
      group
    have hα1 : D.α (kk2 * kk⁻¹) = 1 := by
      have h' : D.α (crK kk) = P * D.α kk * P⁻¹ := hP kk
      rw [hkk2, map_mul, map_mul, map_mul, map_inv, map_inv, h', hx₀]
      group
    have hmem : kk2 * kk⁻¹ ∈ CFSG.pCore 2 ↥K := by
      rw [← D.ker_eq]
      exact hα1
    have h1 : ((kk2 * kk⁻¹ : ↥K) : G) ∈ pCoreOf 2 K := by
      rw [CFSG.Quasithin.C2A3Orbits.pCoreOf_eq_map_pCore]
      exact ⟨_, hmem, rfl⟩
    have h2 : ((kk2 * kk⁻¹ : ↥K) : G) = y * k' * y⁻¹ * k'⁻¹ := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hkk2G, hkk]
    rw [← h2]
    exact h1
  have hyO : y ∈ pCoreOf 2 (K ⊔ pCoreOf 2 I) :=
    le_pCoreOf_of_commutes_mod (pCoreOf_isPGroup 2 I) hRK D.α D.surj D.ker_eq y hyX hycomm
  have hyU : ∀ z : ↥(uZero I K), y * (z : G) = (z : G) * y := by
    intro z
    have hΩ : K ≤ Subgroup.normalizer
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 I)) : Set G) :=
      (le_sup_left.trans (le_normalizer_pCoreOf 2 (K ⊔ pCoreOf 2 I))).trans
        (normalizer_le_normalizer_omegaOneCenterOf _)
    have hzΩ : (z : G) ∈ omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 I)) :=
      (commutator_le_left_of_le_normalizer hΩ) z.2
    exact Subgroup.mem_centralizer_iff.mp
      (centerOf_le_centralizer _ (omegaOneCenterOf_le_centerOf _ hzΩ)) y hyO
  refine ⟨x₀, hyO, fun z z' hz' i => ?_⟩
  have hzz : (z' : G) = (x₀ : G) * (z : G) * (x₀ : G)⁻¹ := by
    calc (z' : G) = r * z * r⁻¹ := hz'
      _ = (x₀ : G) * (y * (z : G) * y⁻¹) * (x₀ : G)⁻¹ := by simp only [hy]; group
      _ = (x₀ : G) * (z : G) * (x₀ : G)⁻¹ := by rw [hyU z, mul_inv_cancel_right]
  exact D.equi x₀ z z' hzz i

end CFSG.Quasithin.H13.Ch4.NSB
