module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSUPosition
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenGen
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrameCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Open CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.ClassicalPosition CFSG.StandardType.TableCRes Matrix Multiplicative

private theorem ker_le_center_comp_mulEquiv_s6chn {H X P : Type*} [Group H] [Group X] [Group P]
    (e : H ≃* X) {φ : X →* P} (hφ : φ.ker ≤ Subgroup.center X) :
    (φ.comp e.toMonoidHom).ker ≤ Subgroup.center H := by
  intro z hz
  have hzc : e z ∈ Subgroup.center X := hφ hz
  rw [Subgroup.mem_center_iff] at hzc ⊢
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  exact hzc (e y)

private theorem exists_inv_lift_s6chn {G H : Type*} [Group G] [Group H] {Bs : Subgroup G}
    {p : ℕ} (hBs : IsMulCommutative ↥Bs) (ψ : H →* G) (ℓ : ↥Bs →* H)
    (hℓ : ∀ (b : ↥Bs) u, (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹))
    (hpow : ∀ b, ℓ b ^ p = 1) :
    ∃ ℓp : ↥Bs →* H, (∀ b, ℓp b = ℓ b⁻¹) ∧ (∀ b, ℓp b ^ p = 1) ∧
      ∀ (b : ↥Bs) u, (b : G) * ψ u * (b : G)⁻¹ = ψ (ℓp b * u * (ℓp b)⁻¹) := by
  let ℓp : ↥Bs →* H :=
    { toFun := fun b => ℓ b⁻¹
      map_one' := by simp
      map_mul' := fun b c => by
        change ℓ ((b * c)⁻¹) = ℓ b⁻¹ * ℓ c⁻¹
        rw [_root_.mul_inv_rev, ← map_mul]
        exact congrArg ℓ (isMulCommutative_iff.mp hBs _ _) }
  refine ⟨ℓp, ?_, ?_, ?_⟩
  · intro b
    rfl
  · intro b
    exact hpow b⁻¹
  · intro b u
    change (b : G) * ψ u * (b : G)⁻¹ = ψ (ℓ b⁻¹ * u * (ℓ b⁻¹)⁻¹)
    simpa only [Subgroup.coe_inv, inv_inv] using hℓ b⁻¹ u

private theorem isElemAbelian_range_comp_s6chn {B H X : Type*} [Group B] [Group H] [Group X]
    {p : ℕ} (e : H ≃* X) (hcomm : IsMulCommutative B) (ℓp : B →* X)
    (hpow : ∀ b, ℓp b ^ p = 1) :
    IsElemAbelian p (e.symm.toMonoidHom.comp ℓp).range := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · rintro ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨b, rfl⟩ := hu
    obtain ⟨c, rfl⟩ := hv
    apply Subtype.ext
    let ℓh := e.symm.toMonoidHom.comp ℓp
    change ℓh b * ℓh c = ℓh c * ℓh b
    rw [← map_mul, ← map_mul]
    exact congrArg ℓh (isMulCommutative_iff.mp hcomm b c)
  · rintro u ⟨b, rfl⟩
    change e.symm (ℓp b) ^ p = 1
    rw [← map_pow, hpow b, map_one]

private theorem card_range_comp_symm_s6chn {B H X : Type*} [Group B] [Group H] [Group X]
    {p r : ℕ} (e : H ≃* X) {ℓ ℓp : B →* H} (hℓp : ∀ b, ℓp b = ℓ b⁻¹)
    (hrank : p ^ r ≤ Nat.card ℓ.range) :
    p ^ r ≤ Nat.card (e.toMonoidHom.comp ℓp).range := by
  have hrange : ℓp.range = ℓ.range := by
    ext u
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b⁻¹, (hℓp b).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b⁻¹, by simp [hℓp]⟩
  rw [MonoidHom.range_comp, Subgroup.card_map_of_injective e.injective, hrange]
  exact hrank

private theorem exists_toral_coord_s6chn {B H : Type*} [Group B] [Group H] {p : ℕ}
    (τ : Multiplicative (Fin 3 → ZMod p) →* H) (hτinj : Function.Injective τ)
    (ℓ' : B →* H)
    (hg : ∀ x ∈ ℓ'.range, ∃ t : Fin 3 → ZMod p, τ (ofAdd t) = x) :
    ∃ T : B →* (Fin 3 → Multiplicative (ZMod p)),
      ∀ b, τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)) = ℓ' b := by
  have hex : ∀ b : B, ∃ t : Fin 3 → ZMod p, τ (ofAdd t) = ℓ' b := by
    intro b
    exact hg (ℓ' b) ⟨b, rfl⟩
  choose t ht using hex
  let v : B →* Multiplicative (Fin 3 → ZMod p) := MonoidHom.mk'
    (fun b => ofAdd (t b)) (fun b c => hτinj (by
      rw [map_mul, ht, ht, ht, map_mul]))
  let eP := MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)
  refine ⟨eP.toMonoidHom.comp v, ?_⟩
  intro b
  change τ (eP.symm (eP (ofAdd (t b)))) = ℓ' b
  rw [eP.symm_apply_apply]
  exact ht b

private theorem exists_hyp_chart_s6chn {G X H : Type*} [Group G] [Group X] [Group H]
    {Bs : Subgroup G} {p : ℕ} (ψ : X →* G) (e : H ≃* X) (g : H) {K : Subgroup G}
    (hker : ψ.ker ≤ Subgroup.center X) (hrange : ψ.range = K)
    (ℓp : ↥Bs →* X)
    (hℓp : ∀ (b : ↥Bs) u, (b : G) * ψ u * (b : G)⁻¹ = ψ (ℓp b * u * (ℓp b)⁻¹))
    (τ : Multiplicative (Fin 3 → ZMod p) →* H)
    (T : ↥Bs →* (Fin 3 → Multiplicative (ZMod p)))
    (hTrel : ∀ b, τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)) =
      ((MulAut.conj g).toMonoidHom.comp (e.symm.toMonoidHom.comp ℓp)) b) :
    ∃ κ : H →* G,
      (∃ k : X, κ = (ψ.comp (MulAut.conj k).toMonoidHom).comp e.toMonoidHom) ∧
      κ.ker ≤ Subgroup.center H ∧ κ.range = K ∧
      ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
        κ (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)) * u *
          (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)))⁻¹) := by
  let κ : H →* G := (ψ.comp e.toMonoidHom).comp (MulAut.conj g⁻¹).toMonoidHom
  have hκker : κ.ker ≤ Subgroup.center H :=
    ker_le_center_comp_mulEquiv_s6chn ((MulAut.conj g⁻¹).trans e) hker
  have hκrange : κ.range = K := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj g⁻¹).surjective,
      Subgroup.map_top, MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective,
      Subgroup.map_top]
    exact hrange
  have hTact : ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
      κ (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)) * u *
        (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)))⁻¹) := by
    intro b u
    rw [hTrel]
    change (b : G) * ψ (e (g⁻¹ * u * g⁻¹⁻¹)) * (b : G)⁻¹ =
      ψ (e (g⁻¹ * ((g * e.symm (ℓp b) * g⁻¹) * u *
        (g * e.symm (ℓp b) * g⁻¹)⁻¹) * g⁻¹⁻¹))
    rw [hℓp]
    congr 1
    simp only [map_mul, map_inv, e.apply_symm_apply, inv_inv]
    group
  refine ⟨κ, ⟨e g⁻¹, ?_⟩, hκker, hκrange, hTact⟩
  ext u
  change ψ (e (g⁻¹ * u * g⁻¹⁻¹)) = ψ (e g⁻¹ * e u * (e g⁻¹)⁻¹)
  simp only [map_mul, map_inv]

private theorem ker_coord_eq_ker_s6chn {B H X : Type*} [Group B] [Group H] [Group X]
    {p : ℕ} (e : H ≃* X) (g : H) (ℓ ℓp : B →* X)
    (hℓp : ∀ b, ℓp b = ℓ b⁻¹)
    (τ : Multiplicative (Fin 3 → ZMod p) →* H) (hτinj : Function.Injective τ)
    (T : B →* (Fin 3 → Multiplicative (ZMod p)))
    (hTrel : ∀ b, τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)) =
      ((MulAut.conj g).toMonoidHom.comp (e.symm.toMonoidHom.comp ℓp)) b) :
    T.ker = ℓ.ker := by
  ext b
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  have h1 : T b = 1 ↔
      ((MulAut.conj g).toMonoidHom.comp (e.symm.toMonoidHom.comp ℓp)) b = 1 := by
    constructor
    · intro hb
      rw [← hTrel, hb, map_one, map_one]
    · intro hb
      have hv : (MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b) = 1 :=
        hτinj (by rw [hTrel, hb, map_one])
      exact (MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm.injective
        (by rw [hv, map_one])
  rw [h1]
  let A := (MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom
  have hAinj : Function.Injective A := (MulAut.conj g).injective.comp e.symm.injective
  change A (ℓp b) = 1 ↔ ℓ b = 1
  rw [hℓp b, ← map_one A, hAinj.eq_iff]
  simp

private theorem surjective_toral_coord_s6chn {G H : Type} [Group G] [Finite G] [Group H]
    {p n : ℕ} [Fact p.Prime] [NeZero p] {Bs K : Subgroup G} {i0 : Fin n}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (hn : n = 4) (hp2 : p ≠ 2)
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (κ : H →* G) (τ : Multiplicative (Fin 3 → ZMod p) →* H)
    (T : ↥Bs →* (Fin 3 → Multiplicative (ZMod p)))
    (hκrange : κ.range = K)
    (hTact : ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
      κ (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)) * u *
        (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)))⁻¹)) :
    Function.Surjective T := by
  have hcardBs : Nat.card ↥Bs = p ^ 4 := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_fun, Nat.card_fin, hn,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p :=
    ggSecFiveBPermSpK_card_inf_centralizer_le hp2 hA
  let eP := MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)
  let D : (Fin 3 → Multiplicative (ZMod p)) →* H := τ.comp eP.symm.toMonoidHom
  have hTact' : ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
      κ (D (T b) * u * (D (T b))⁻¹) := by
    intro b u
    exact hTact b u
  exact ggSecFiveBPermSpK_toralHom_surjective (r := 2) hcardBs hcent
    (ggSecFiveBPermSpK_toralHom_ker_mem (D := D) hκrange hTact')

private theorem exists_lift_data_s6chn {G : Type} [Group G] [Finite G] {p f : ℕ}
    {Bs K : Subgroup G}
    (ψ : SU (unitaryInvolution (PSUF f) 2 (f + 1)) 6 →* G)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ (f + 1) - 1)
    (hBs : IsElemAbelian p Bs) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (Unitary.rootDatum (card_PSUF f) 6) ψ b)
    (hcard : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card ↥Bs)
    (h4 : p ^ 4 ≤ Nat.card ↥Bs)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (PSUF f) 2 (f + 1)) 6))
    (hrange : ψ.range = K) :
    ∃ (ℓ : ↥Bs →* SU (unitaryInvolution (PSUF f) 2 (f + 1)) 6)
      (ℓp : ↥Bs →* SU (unitaryInvolution (PSUF f) 2 (f + 1)) 6),
      (∀ b, ℓp b = ℓ b⁻¹) ∧ (∀ b, ℓp b ^ p = 1) ∧
      (∀ (b : ↥Bs) u, (b : G) * ψ u * (b : G)⁻¹ = ψ (ℓp b * u * (ℓp b)⁻¹)) ∧
      ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (ψ.range : Set G) ∧
      p ^ 3 ≤ Nat.card ℓ.range := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let ψn : SU (unitaryInvolution (PSUF f) 2 (f + 1)) 6 →* G := ψ
  have hrangeN : ψn.range = K := hrange
  have hN' : Bs ≤ Subgroup.normalizer (ψn.range : Set G) := by
    rw [hrangeN]
    exact hN
  have hcard' : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψn.range : Set G)) ≤
      Nat.card ↥Bs := by
    rw [hrangeN]
    exact hcard
  have hadm : StatedLieAdmissible .PSU 6 2 (f + 1) :=
    ⟨Nat.prime_two, by omega, by norm_num, by simp⟩
  have hpq' : ¬ p ∣ 2 ^ (f + 1) + 1 :=
    not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  obtain ⟨ℓ, hℓ, hkerℓ, hpowℓ, hrankℓ⟩ := exists_unitary_lift_kernel_rank
    ψn hker hadm hp hp2 Bs hBs hN' hdiag h4 hpq' hcard'
  obtain ⟨ℓp, hℓp_eq, hpowp, hℓp⟩ := exists_inv_lift_s6chn hBs.1 ψn ℓ hℓ hpowℓ
  exact ⟨ℓ, ℓp, hℓp_eq, hpowp, hℓp, hkerℓ, hrankℓ⟩

private theorem toralHom_aux_s6chn {G : Type} [Group G] [Finite G] {p n f : ℕ}
    {Bs K : Subgroup G} {i0 : Fin n}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (hn : n = 4)
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {ψ₀ : (ggU .PSU 6 (f + 1)).K →* G}
    (hloc : GGKGPosLocalHypTw p Bs K .PSU 6 (f + 1) ψ₀) (hrange : ψ₀.range = K) :
    ∃ h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))),
      ∃ ζ : GaloisField 2 (2 * (f + 1)), IsPrimitiveRoot ζ p ∧ h.bar ζ = ζ ∧
      ∃ τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0,
        (∀ t, (((τ (ofAdd t) : hypSU h 3 0) : GL (HypIndex 3 0) (GaloisField 2 (2 * (f + 1)))) :
          Matrix (HypIndex 3 0) (HypIndex 3 0) (GaloisField 2 (2 * (f + 1)))) =
            diagonal (hypEntries ζ t)) ∧
      ∃ κ : hypSU h 3 0 →* G,
        (∃ k : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6,
          κ = (ψ₀.comp (MulAut.conj k).toMonoidHom).comp
            (SuSplitRootGen.hypSUEquiv h (by decide)).toMonoidHom) ∧
        κ.ker ≤ Subgroup.center (hypSU h 3 0) ∧ κ.range = K ∧
      ∃ T : ↥Bs →* (Fin 3 → Multiplicative (ZMod p)),
        Function.Surjective T ∧ T.ker.map Bs.subtype =
          Bs ⊓ Subgroup.centralizer (K : Set G) ∧
        ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
          κ (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)) * u *
            (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)))⁻¹) := by
  obtain ⟨⟨hp, hp2, -, hpq⟩, ⟨hker, -⟩, ⟨hBs, hN, -⟩, hdiag, hcard, h4⟩ := hloc
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ℓ, ℓp, hℓp_eq, hpowp, hℓp, hkerℓ, hrankℓ⟩ :=
    exists_lift_data_s6chn ψ₀ hp hp2 hpq hBs hN hdiag hcard h4 hker hrange
  let h : UnitaryFieldData 2 (f + 1) (PSUF f) :=
    TableBU.unitaryFieldData_of_card (card_PSUF f) (by omega)
  let eH : hypSU h 3 0 ≃* SU (unitaryInvolution (PSUF f) 2 (f + 1)) 6 :=
    SuSplitRootGen.hypSUEquiv h (by decide)
  let ψn : SU (unitaryInvolution (PSUF f) 2 (f + 1)) 6 →* G := ψ₀
  have hrangeN : ψn.range = K := hrange
  let ℓh := eH.symm.toMonoidHom.comp ℓp
  let E : Subgroup (hypSU h 3 0) := ℓh.range
  have hE : IsElemAbelian p E := isElemAbelian_range_comp_s6chn eH hBs.1 ℓp hpowp
  have hcardE : p ^ 3 ≤ Nat.card E := card_range_comp_symm_s6chn eH.symm hℓp_eq hrankℓ
  obtain ⟨ζu, hζu⟩ := RelA5.exists_zeta_muSplit (card_PSUF f) hpq
  let ζ : PSUF f := (ζu : (PSUF f)ˣ)
  have hζ : IsPrimitiveRoot ζ p := RelA5.isPrimitiveRoot_coe hζu
  have hbar : h.bar ζ = ζ := RelA5.bar_eq_of_mem_muSplit h ζu.2
  obtain ⟨τ, hτ⟩ := exists_hypTorusHom (r := 3) h hp hζ hbar
  have hτinj : Function.Injective τ := hypTorusHom_injective h hp hζ τ hτ
  obtain ⟨g, hg⟩ := exists_conj_hypEntries h hp hp2 hpq hζ (by decide) E hE hcardE
  let ℓ' := (MulAut.conj g).toMonoidHom.comp ℓh
  have hg' : ∀ x ∈ ℓ'.range, ∃ t : Fin 3 → ZMod p, τ (ofAdd t) = x := by
    rintro x ⟨b, rfl⟩
    obtain ⟨t, ht⟩ := hg (ℓh b) ⟨b, rfl⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact (hτ t).trans ht.symm
  obtain ⟨T, hTrel⟩ := exists_toral_coord_s6chn τ hτinj ℓ' hg'
  obtain ⟨κ, ⟨k, hκk⟩, hκker, hκrange, hTact⟩ :=
    exists_hyp_chart_s6chn ψn eH g hker hrange ℓp hℓp τ T hTrel
  have hkerT : T.ker = ℓ.ker :=
    ker_coord_eq_ker_s6chn eH g ℓ ℓp hℓp_eq τ hτinj T hTrel
  have hkerEq : T.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (K : Set G) := by
    rw [hkerT, hkerℓ, hrangeN]
  have hTsurj : Function.Surjective T :=
    surjective_toral_coord_s6chn eta hn hp2 hA κ τ T hκrange hTact
  exact ⟨h, ζ, hζ, hbar, τ, hτ, κ, ⟨k, hκk⟩, hκker, hκrange,
    T, hTsurj, hkerEq, hTact⟩

theorem ggSecFiveBPermSU_exists_toralHom_of_centralImage {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hMp : GGInnerDiagMpInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n a : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {K : Subgroup G} {i0 : Fin n}
    (hn : n = 4) (ha : 2 ≤ a) (hpa : p ∣ 2 ^ a - 1) (hK : K ∈ 𝒦)
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {ψ₀ : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G}
    (hker : ψ₀.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6))
    (hrange : ψ₀.range = K) :
    ∃ h : UnitaryFieldData 2 a (GaloisField 2 (2 * a)),
      ∃ ζ : GaloisField 2 (2 * a), IsPrimitiveRoot ζ p ∧ h.bar ζ = ζ ∧
      ∃ τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0,
        (∀ t, (((τ (ofAdd t) : hypSU h 3 0) : GL (HypIndex 3 0) (GaloisField 2 (2 * a))) :
          Matrix (HypIndex 3 0) (HypIndex 3 0) (GaloisField 2 (2 * a))) =
            diagonal (hypEntries ζ t)) ∧
      ∃ κ : hypSU h 3 0 →* G,
        (∃ k : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6,
          κ = (ψ₀.comp (MulAut.conj k).toMonoidHom).comp
            (SuSplitRootGen.hypSUEquiv h (by decide)).toMonoidHom) ∧
        κ.ker ≤ Subgroup.center (hypSU h 3 0) ∧ κ.range = K ∧
      ∃ T : ↥Bs →* (Fin 3 → Multiplicative (ZMod p)),
        Function.Surjective T ∧ T.ker.map Bs.subtype =
          Bs ⊓ Subgroup.centralizer (K : Set G) ∧
        ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
          κ (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)) * u *
            (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)))⁻¹) := by
  obtain ⟨f, rfl⟩ : ∃ f, a = f + 1 := ⟨a - 1, by omega⟩
  let a := f + 1
  have hloc : GGKGPosLocalHypTw p Bs K .PSU 6 a ψ₀ :=
    ggSecFiveBPermSU_localHyp_of_centralImage hMp hR eta hn ha hpa hK hA hker hrange
  exact toralHom_aux_s6chn eta hn hA hloc hrange

end CFSG.StandardType

end
