module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConj
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneWeyl

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.LieType.Universal.Symplectic CFSG.StandardType.SpJoin
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

structure IsPlaneTorusLift {G : Type} [Group G] (p : ℕ) (Bs X : Subgroup G) {n : ℕ} {F : Type}
    [Field F] (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F)
    (φ : StatedSp n F →* G) : Prop where
  zeta_inv : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹
  injective : Function.Injective φ
  range_eq : φ.range = X
  torus_injective : Function.Injective (φ.comp (spPlaneTorus n ζ))
  torus_range : (φ.comp (spPlaneTorus n ζ)).range = Bs ⊓ X
  weyl_mem : ∀ k, φ (weylRep n F k) ∈ Subgroup.normalizer (Bs : Set G)

theorem exists_plane_torus_lift {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] (h2 : (2 : F) = 0) {n : ℕ}
    (φ' : StatedSp n F →* G) (hinj : Function.Injective φ') {B Bs : Subgroup G}
    (hBs : GGBstar p B Bs) (hNK : Bs ≤ Subgroup.normalizer (φ'.range : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ φ'.range, ∀ y ∈ φ'.range, b * y * b⁻¹ = x * y * x⁻¹)
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (φ'.range : Set G)) ≤ p)
    (hrank : p ^ (n + 1) ≤ Nat.card Bs) :
    ∃ (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F) (φ : StatedSp n F →* G),
      IsPlaneTorusLift p Bs φ'.range ζ φ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let X : Subgroup G := φ'.range
  haveI : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2
  have hZ : Subgroup.center X = ⊥ := by
    have hZsp : Subgroup.center (StatedSp n F) = ⊥ := by
      rw [CFSG.LieType.Universal.Symplectic.center_eq,
        CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
    have he := Subgroup.map_center_eq (MonoidHom.ofInjective hinj)
    rw [hZsp, Subgroup.map_bot] at he
    exact he.symm
  have hsplit := ggBstar_split_of_inner (X := X) hBs hZ hNK hinner
  have hcard_split := card_ggBstar_split (X := X) hBs hZ hNK hinner
  have hcardX : p ^ n ≤ Nat.card ↥(Bs ⊓ X) := by
    have hle : p ^ n * p ≤ Nat.card ↥(Bs ⊓ X) * p := by
      calc p ^ n * p = p ^ (n + 1) := by rw [← pow_succ]
        _ ≤ Nat.card Bs := hrank
        _ = Nat.card ↥(Bs ⊓ X) *
              Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := hcard_split
        _ ≤ Nat.card ↥(Bs ⊓ X) * p := Nat.mul_le_mul_left _ hcent
    exact Nat.le_of_mul_le_mul_right hle hp.pos
  let E' : Subgroup (StatedSp n F) := (Bs ⊓ X).comap φ'
  have hE'map : E'.map φ' = Bs ⊓ X := by
    show ((Bs ⊓ X).comap φ').map φ' = Bs ⊓ X
    exact Subgroup.map_comap_eq_self inf_le_right
  have hcardE' : Nat.card E' = Nat.card ↥(Bs ⊓ X) := by
    rw [← hE'map]
    exact (Subgroup.card_map_of_injective (K := E') hinj).symm
  have hE'ab : IsElemAbelian p E' :=
    IsElemAbelian.comap (hBs.2.1.mono inf_le_left) hinj
  have hcardE'ge : p ^ n ≤ Nat.card E' := by
    rw [hcardE']
    exact hcardX
  obtain ⟨ζ, hζinv, hζ⟩ := exists_spPlaneConj h2 hp hp2
  obtain ⟨c, hc⟩ := hζ n E' hE'ab hcardE'ge
  let τ : (Fin n → Multiplicative (ZMod p)) →* StatedSp n F := spPlaneTorus n ζ
  let T : Subgroup (StatedSp n F) := τ.range
  have hcardV : Nat.card (Fin n → Multiplicative (ZMod p)) = p ^ n := by
    rw [Nat.card_fun, Nat.card_fin]
    congr 1
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod]
  have hcardT : p ^ n ≤ Nat.card T := by
    have : Nat.card (E'.map (MulAut.conj c).toMonoidHom) = Nat.card E' :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    rw [hc] at this
    rw [this]
    exact hcardE'ge
  have hτinj : Function.Injective τ := by
    have hsurj : Function.Surjective τ.rangeRestrict := MonoidHom.rangeRestrict_surjective τ
    have hbij : Function.Bijective τ.rangeRestrict :=
      hsurj.bijective_of_nat_card_le (by rw [hcardV]; exact hcardT)
    intro a b hab
    apply hbij.1
    apply Subtype.ext
    exact hab
  let ψ : StatedSp n F →* StatedSp n F := (MulAut.conj c⁻¹).toMonoidHom
  let φ : StatedSp n F →* G := φ'.comp ψ
  have hψinj : Function.Injective ψ := (MulAut.conj c⁻¹).injective
  have hφinj : Function.Injective φ := hinj.comp hψinj
  have hφrange : φ.range = φ'.range := by
    show (φ'.comp ψ).range = φ'.range
    rw [MonoidHom.range_comp]
    have hψtop : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr (MulAut.conj c⁻¹).surjective
    rw [hψtop, ← MonoidHom.range_eq_map]
  have hTψ : T.map ψ = E' := by
    show Subgroup.map ψ ((spPlaneTorus n ζ).range) = E'
    rw [← hc, Subgroup.map_map]
    have hcomp : ψ.comp (MulAut.conj c).toMonoidHom = MonoidHom.id (StatedSp n F) := by
      refine MonoidHom.ext fun y => ?_
      show (MulAut.conj c⁻¹).toMonoidHom ((MulAut.conj c).toMonoidHom y) = y
      rw [show MulAut.conj c⁻¹ = (MulAut.conj c)⁻¹ from
        map_inv (MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)) c]
      exact MulEquiv.symm_apply_apply (MulAut.conj c) y
    rw [hcomp, Subgroup.map_id]
  have hTmap : T.map φ = Bs ⊓ X := by
    show T.map (φ'.comp ψ) = Bs ⊓ X
    rw [← Subgroup.map_map (K := T) (g := φ') (f := ψ), hTψ, hE'map]
  have htorus : (φ.comp τ).range = Bs ⊓ X := by
    rw [MonoidHom.range_comp]
    exact hTmap
  have hweyl : ∀ k, φ (weylRep n F k) ∈ Subgroup.normalizer (Bs : Set G) := by
    intro k
    let u : G := φ (weylRep n F k)
    have huX : u ∈ X := by
      have h : u ∈ φ.range := MonoidHom.mem_range.mpr ⟨weylRep n F k, rfl⟩
      rwa [hφrange] at h
    have huu : u * u = 1 := by
      show φ (weylRep n F k) * φ (weylRep n F k) = 1
      rw [← map_mul, spWeylRep_mul_self n h2 k, map_one]
    have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
    have hconjX : ∀ y ∈ Bs ⊓ X, u * y * u⁻¹ ∈ Bs ⊓ X := by
      intro y hy
      rw [← hTmap] at hy ⊢
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_map.mpr ⟨weylRep n F k * t * (weylRep n F k)⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_set_normalizer_iff.mp
          (weylRep_mem_normalizer_spPlaneTorus h2 ζ hζinv k) t).mp ht
      · show φ (weylRep n F k * t * (weylRep n F k)⁻¹) = u * φ t * u⁻¹
        simp only [u, map_mul, map_inv]
    have hcentr : ∀ c' ∈ Subgroup.centralizer (X : Set G), u * c' * u⁻¹ = c' := by
      intro c' hc'
      have hcomm : u * c' = c' * u := Subgroup.mem_centralizer_iff.mp hc' u huX
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hforward : ∀ y ∈ Bs, u * y * u⁻¹ ∈ Bs := by
      intro y hy
      obtain ⟨x, hx, c', hc', rfl⟩ := hsplit y hy
      have hx' := hconjX x hx
      have hc'' := hcentr c' hc'.2
      have h1 : u * (x * c') * u⁻¹ = (u * x * u⁻¹) * (u * c' * u⁻¹) := by group
      rw [h1, hc'']
      exact Bs.mul_mem hx'.1 hc'.1
    rw [Subgroup.mem_set_normalizer_iff]
    intro b
    constructor
    · exact hforward b
    · intro hb
      have hb' := hforward (u * b * u⁻¹) hb
      have hb_eq : u * (u * b * u⁻¹) * u⁻¹ = b := by
        rw [hinv]
        calc u * (u * b * u) * u = (u * u) * b * (u * u) := by group
          _ = b := by rw [huu]; group
      rwa [hb_eq] at hb'
  exact ⟨ζ, φ, ⟨hζinv, hφinj, hφrange, hφinj.comp hτinj, htorus, hweyl⟩⟩

theorem exists_plane_torus_lift_of_range {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] (h2 : (2 : F) = 0) {n : ℕ}
    (φ' : StatedSp n F →* G) (hinj : Function.Injective φ') {B Bs X : Subgroup G}
    (hBs : GGBstar p B Bs) (hrange : φ'.range = X) (hNK : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    (hrank : p ^ (n + 1) ≤ Nat.card Bs) :
    ∃ (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F) (φ : StatedSp n F →* G),
      IsPlaneTorusLift p Bs X ζ φ := by
  subst hrange
  exact exists_plane_torus_lift hp hp2 h2 φ' hinj hBs hNK hinner hcent hrank

end CFSG.StandardType
