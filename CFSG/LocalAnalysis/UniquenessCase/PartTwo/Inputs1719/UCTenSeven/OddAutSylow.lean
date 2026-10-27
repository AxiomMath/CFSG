module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAction
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitDihedralAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def AutSylowAt (X : Type) [Group X] (p : ℕ) : Prop :=
  ∀ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ → ∀ α : MulAut X, α ^ p = 1 →
    S.map α.toMonoidHom = S → ∀ x ∈ S, α x = x

@[expose] def NormSylowAt (X : Type) [Group X] (p : ℕ) : Prop :=
  ∀ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ → ∀ y ∈ normalizer (S : Set X),
    y ^ p ∈ centralizer (S : Set X) → y ∈ centralizer (S : Set X)

@[expose] def NormSylowIn (X : Type) [Group X] (D : Subgroup (MulAut X)) (p : ℕ) : Prop :=
  ∀ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ → ∀ α ∈ D, S.map α.toMonoidHom = S →
    (∀ x ∈ S, (α ^ p) x = x) → ∀ x ∈ S, α x = x

@[expose] def FixesSylowOutside (X : Type) [Group X] (D : Subgroup (MulAut X)) (p : ℕ) :
    Prop :=
  ∀ α : MulAut X, α ^ p = 1 → α ∉ D →
    ∃ S₀ : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S₀ ⊤ ∧ ∀ x ∈ S₀, α x = x

private theorem isSylowOf_top_maximal {G : Type*} [Group G] {p : ℕ} {S : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p S ⊤) :
    IsPGroup p S ∧ ∀ T : Subgroup G, IsPGroup p T → S ≤ T → T = S := by
  obtain ⟨Q, hQ⟩ := h
  refine ⟨?_, ?_⟩
  · have hQp := Q.isPGroup'.map (⊤ : Subgroup G).subtype
    rwa [hQ] at hQp
  · intro T hT hST
    have hT' : IsPGroup p (T.subgroupOf (⊤ : Subgroup G)) := hT.comap_subtype
    have hle : (Q : Subgroup ↥(⊤ : Subgroup G)) ≤ T.subgroupOf (⊤ : Subgroup G) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      apply hST
      rw [← hQ]
      exact Subgroup.mem_map_of_mem _ hx
    have hQeq : T.subgroupOf (⊤ : Subgroup G) = Q := Q.is_maximal' hT' hle
    calc T = (T.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
      _ = (Q : Subgroup ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype := by rw [hQeq]
      _ = S := hQ

private theorem isSylowOf_map_mulEquiv_top {G H : Type*} [Group G] [Group H] {p : ℕ}
    (e : G ≃* H) {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf p S ⊤) :
    CFSG.ABGLocalTools.IsSylowOf p (S.map e.toMonoidHom) ⊤ := by
  obtain ⟨hP, hmax⟩ := isSylowOf_top_maximal hS
  refine ⟨Sylow.mk ((S.map e.toMonoidHom).subgroupOf ⊤) ?_ ?_, ?_⟩
  · exact (hP.map e.toMonoidHom).comap_subtype
  · intro R hR hle
    have hRle : R ≤ (S.map e.toMonoidHom).subgroupOf ⊤ := by
      intro y hy
      rw [Subgroup.mem_subgroupOf]
      have hT : IsPGroup p ((R.map (⊤ : Subgroup H).subtype).map e.symm.toMonoidHom) :=
        (hR.map (⊤ : Subgroup H).subtype).map e.symm.toMonoidHom
      have hST : S ≤ (R.map (⊤ : Subgroup H).subtype).map e.symm.toMonoidHom := by
        intro s hs
        have hsm : e s ∈ S.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom hs
        have hmem : (⟨e s, Subgroup.mem_top _⟩ : (⊤ : Subgroup H)) ∈ R := hle hsm
        have hmem' : e s ∈ R.map (⊤ : Subgroup H).subtype := Subgroup.mem_map_of_mem _ hmem
        have := Subgroup.mem_map_of_mem e.symm.toMonoidHom hmem'
        simpa using this
      have heq := hmax _ hT hST
      have hyR : (y : H) ∈ R.map (⊤ : Subgroup H).subtype := Subgroup.mem_map_of_mem _ hy
      have hy' : e.symm (y : H) ∈ (R.map (⊤ : Subgroup H).subtype).map e.symm.toMonoidHom :=
        Subgroup.mem_map_of_mem _ hyR
      rw [heq] at hy'
      have := Subgroup.mem_map_of_mem e.toMonoidHom hy'
      simpa using this
    exact le_antisymm hRle hle
  · change ((S.map e.toMonoidHom).subgroupOf ⊤).map (⊤ : Subgroup H).subtype = S.map e.toMonoidHom
    rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]

theorem autSylowAt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}
    (h : AutSylowAt Y p) : AutSylowAt X p := by
  intro S hS α hα hαS x hx
  let S' : Subgroup Y := S.map e.toMonoidHom
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 S' ⊤ := isSylowOf_map_mulEquiv_top e hS
  let α' : MulAut Y := MulAut.congr e α
  have hα' : α' ^ p = 1 := by
    rw [show α' ^ p = MulAut.congr e (α ^ p) by rw [map_pow], hα, map_one]
  have hα'S : S'.map α'.toMonoidHom = S' := by
    dsimp only [S', α']
    rw [Subgroup.map_map]
    rw [show (MulAut.congr e α).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp α.toMonoidHom by
      ext z
      simp [MulAut.congr_apply]]
    rw [← Subgroup.map_map, hαS]
  have hpoint := h S' hS' α' hα' hα'S (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)
  apply e.injective
  simpa [α', MulAut.congr_apply] using hpoint

theorem normSylowAt_of_normSylowIn {X : Type} [Group X] {p : ℕ} {D : Subgroup (MulAut X)}
    (hD : inner X ≤ D) (h : NormSylowIn X D p) : NormSylowAt X p := by
  intro S hS y hy hyp
  let α : MulAut X := MulAut.conj y
  have hαD : α ∈ D := hD (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
  have hαS : S.map α.toMonoidHom = S := Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
  have hfix : ∀ x ∈ S, (α ^ p) x = x := by
    intro x hx
    have hcomm := (Subgroup.mem_centralizer_iff.mp hyp) x hx
    have hαconj : α ^ p = MulAut.conj (y ^ p) := by
      rw [show α = MulAut.conj y from rfl, ← map_pow]
    rw [hαconj, MulAut.conj_apply, ← hcomm]
    group
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' := h S hS α hαD hαS hfix x hx
  rw [show α = MulAut.conj y from rfl, MulAut.conj_apply] at hx'
  calc x * y = (y * x * y⁻¹) * y := by rw [hx']
    _ = y * x := by group

theorem normSylowIn_inner_of_normSylowAt {X : Type} [Group X] {p : ℕ}
    (h : NormSylowAt X p) : NormSylowIn X (inner X) p := by
  intro S hS α hα hαS hfix x hx
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp
    (show α ∈ (MulAut.conj : X →* MulAut X).range from hα)
  have hyN : y ∈ normalizer (S : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hαS
  have hyp : y ^ p ∈ centralizer (S : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := hfix s hs
    rw [← map_pow, MulAut.conj_apply] at h
    calc s * y ^ p = (y ^ p * s * (y ^ p)⁻¹) * y ^ p := by rw [h]
      _ = y ^ p * s := by group
  have hyC := h S hS y hyN hyp
  have hcomm := (Subgroup.mem_centralizer_iff.mp hyC) x hx
  rw [MulAut.conj_apply, ← hcomm]
  group

theorem autSylowAt_of_normSylowIn {X : Type} [Group X] [Finite X] {p : ℕ}
    {D : Subgroup (MulAut X)} (hD : inner X ≤ D) (hN : NormSylowIn X D p)
    (hF : FixesSylowOutside X D p) : AutSylowAt X p := by
  intro S hS α hα hαS
  by_cases hαD : α ∈ D
  · exact hN S hS α hαD hαS (fun x _ => by rw [hα]; rfl)
  · obtain ⟨S₀, hS₀, hfix⟩ := hF α hα hαD
    have hN' := normSylowAt_of_normSylowIn hD hN
    exact fixes_of_fixes_isSylowOf hS hS₀
      (fun y hy hyp => hN' S hS y hy hyp) hα hαS hfix

theorem mulAut_eq_one_of_pow_prime_of_card_lt {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hQ : Nat.card Q < p) {σ : MulAut Q} (hσ : σ ^ p = 1) : σ = 1 := by
  have hdvd : orderOf σ ∣ p := orderOf_dvd_of_pow_eq_one hσ
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp1
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    have hpdvd : p ∣ Nat.card (MulAut Q) := hp1 ▸ orderOf_dvd_natCard σ
    have hinj : Function.Injective (MulAut.toPerm Q) := by
      intro f g hfg
      exact MulEquiv.ext (fun z => congrArg (fun e : Equiv.Perm Q => e z) hfg)
    have hbij : Function.Bijective
        (fun a : MulAut Q => (⟨MulAut.toPerm Q a, ⟨a, rfl⟩⟩ : ↥(MulAut.toPerm Q).range)) := by
      constructor
      · intro a b hab
        exact hinj (Subtype.ext_iff.mp hab)
      · intro r
        obtain ⟨a, ha⟩ := r.2
        exact ⟨a, Subtype.ext ha⟩
    have hcard : Nat.card (MulAut Q) = Nat.card ↥(MulAut.toPerm Q).range :=
      Nat.card_eq_of_bijective _ hbij
    have hdvd2 : Nat.card (MulAut Q) ∣ Nat.card (Equiv.Perm Q) := by
      rw [hcard]
      exact Subgroup.card_subgroup_dvd_card _
    have hdvd3 : p ∣ (Nat.card Q).factorial := by
      rw [← Nat.card_perm]
      exact hpdvd.trans hdvd2
    have hpQ : p ≤ Nat.card Q := (Nat.Prime.dvd_factorial hp).mp hdvd3
    omega

theorem autSylowAt_of_sylow_mulAut {X : Type} [Group X] {p : ℕ}
    (h : ∀ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ → ∀ σ : MulAut ↥S, σ ^ p = 1 →
      σ = 1) : AutSylowAt X p := by
  intro S hS α hα hαS x hx
  let σ : MulAut ↥S := (α.subgroupMap S).trans (MulEquiv.subgroupCongr hαS)
  have hσcoe : ∀ s : ↥S, ((σ s : ↥S) : X) = α (s : X) := by
    intro s
    have h := MulEquiv.coe_subgroupMap_apply α S s
    have h2 := MulEquiv.subgroupCongr_apply hαS ((MulEquiv.subgroupMap α S) s)
    calc (((MulEquiv.subgroupCongr hαS) ((MulEquiv.subgroupMap α S) s) : ↥S) : X)
        = (((MulEquiv.subgroupMap α S) s : ↥(S.map (MulEquiv.toMonoidHom α))) : X) := h2
      _ = α (s : X) := h
  have hcoe : ∀ (k : ℕ) (s : ↥S), (((σ ^ k) s : ↥S) : X) = ((α ^ k) (s : X)) := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ k ih =>
        intro s
        have h1 : ((σ ^ (k + 1)) s : ↥S) = σ ((σ ^ k) s) := by
          rw [pow_succ', MulAut.mul_apply]
        have h2 : ((α ^ (k + 1)) (s : X)) = α ((α ^ k) (s : X)) := by
          rw [pow_succ', MulAut.mul_apply]
        rw [h1, hσcoe, ih, ← h2]
  have hσp : σ ^ p = 1 := by
    ext s
    rw [hcoe p s, hα]
    simp
  have hσ1 := h S hS σ hσp
  have hx' : ((σ ⟨x, hx⟩ : ↥S) : X) = α x := by
    have := hcoe 1 ⟨x, hx⟩
    simpa using this
  rw [← hx', hσ1]
  rfl

theorem autSylowAt_psl_two {X : Type} [Group X] [Finite X] {r f : ℕ} (hr2 : r ≠ 2)
    (hadm : CFSG.Open.StatedLieAdmissible .PSL 2 r f) (hX : CFSG.Blueprint.LieModel X .PSL 2 r f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : AutSylowAt X p := by
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  let : Field K := hKfield
  have : Finite K := hKfin
  refine autSylowAt_of_mulEquiv e ?_
  have hr : r.Prime := hadm.1
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨r, f, hr, hr.odd_of_ne_two hr2, hadm.2.1, hKcard⟩
  have hD := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply autSylowAt_of_sylow_mulAut
  intro S hS σ hσ
  let e2 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 K ≃*
      CFSG.GorensteinWalter.PSL2 K :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).symm
  let S' : Subgroup (CFSG.GorensteinWalter.PSL2 K) := S.map e2.toMonoidHom
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 S' ⊤ :=
    isSylowOf_map_mulEquiv_top e2 hS
  have hS'iff := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := S') (K := ⊤)).mp hS'
  let Q : Sylow 2 (CFSG.GorensteinWalter.PSL2 K) :=
    hS'iff.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hS'iff.2.2)
  have hQcoe : (Q : Subgroup (CFSG.GorensteinWalter.PSL2 K)) = S' := IsPGroup.toSylow_coe _ _
  obtain ⟨m, hm, ⟨d⟩⟩ := hD Q
  let φ : ↥S ≃* ↥Q :=
    (MulEquiv.subgroupMap e2 S).trans (MulEquiv.subgroupCongr hQcoe.symm)
  let σ' : MulAut (DihedralGroup (2 ^ m)) :=
    MulAut.congr d (MulAut.congr φ σ)
  have hσ'p : σ' ^ p = 1 := by
    dsimp only [σ']
    rw [← map_pow, ← map_pow, hσ, map_one]
    exact map_one (MulAut.congr d)
  by_cases hm2 : 2 ≤ m
  · have h := CFSG.ComponentClassification.HarrisLit.dihedral_mulAut_eq_one_of_odd hm2 σ'
      (hp.odd_of_ne_two (by omega)) hσ'p
    have h1 : MulAut.congr φ σ = 1 := by
      apply (MulAut.congr d).injective
      rw [show (MulAut.congr d) 1 = 1 from map_one _]
      exact h
    exact (MulAut.congr φ).injective (h1.trans (map_one _).symm)
  · have hm1 : m = 1 := by omega
    have hcardQ : Nat.card ↥Q = 4 := by
      change Nat.card ↥(Q : Subgroup (CFSG.GorensteinWalter.PSL2 K)) = 4
      rw [Nat.card_congr d.toEquiv, hm1, DihedralGroup.nat_card]
      norm_num
    have hcardS : Nat.card ↥S = 4 := by
      rw [← hcardQ]
      exact Nat.card_congr φ.toEquiv
    have hlt : Nat.card ↥S < p := by omega
    exact mulAut_eq_one_of_pow_prime_of_card_lt hp hlt hσ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
