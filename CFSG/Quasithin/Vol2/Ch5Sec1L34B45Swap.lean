module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34B45Model

public section

namespace CFSG.Quasithin.H13.B45L34

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer
  CFSG.Quasithin
open CFSG.Quasithin.H.L3Nine (HMod rho mat mat_injective mat_rho)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

theorem card_fix_map_conj {M X : Type*} [Group M] [Mul X] (ρ : M →* MulAut X) (R : Subgroup M)
    (x : M) :
    Nat.card {v : X // ∀ y ∈ R.map (MulAut.conj x).toMonoidHom, ρ y v = v} =
      Nat.card {v : X // ∀ y ∈ R, ρ y v = v} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (ρ x)⁻¹.toEquiv fun v => ?_)
  have key : ∀ y : M, ρ (x * y * x⁻¹) v = ρ x (ρ y ((ρ x)⁻¹ v)) := by
    intro y
    rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply]
  constructor
  · intro h y hy
    have h1 := h (x * y * x⁻¹) ⟨y, hy, rfl⟩
    rw [key] at h1
    have h2 := congrArg (fun w => (ρ x)⁻¹ w) h1
    simpa using h2
  · rintro h _ ⟨y, hy, rfl⟩
    show ρ (x * y * x⁻¹) v = v
    have h1 : ρ y ((ρ x)⁻¹ v) = (ρ x)⁻¹ v := h y hy
    rw [key, h1]
    simp

variable {F : Type} [Field F] [Fintype F] [CharP F 2] (hK : Nat.card F = (2 ^ 1) ^ 2)
include hK

omit [Fintype F] [CharP F 2] hK in
theorem alpha0Aut_proj_rad [Finite F] [CharP F 2] (hk : Nat.card F = 4) (b c : F) :
    KGL34P.alpha0Aut hk (proj 3 F (KGL34P.rad b c)) = proj 3 F (rad2 (b ^ 2) (c ^ 2)) := by
  have hinv : (KGL34P.rad b c)⁻¹ = KGL34P.rad b c := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [KGL34P.rad_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, KGL34P.rad_zero]
  show LinearThreeFourOuter.nf (frobeniusEquiv F 2) KGL34P.w0GL 1 1 (proj 3 F (KGL34P.rad b c)) = _
  rw [KGL34P.alpha0_proj]
  congr 1
  apply Subtype.ext
  ext i j
  rw [KGL34P.alpha0_matrix, hinv, KGL34P.coe_rad, coe_rad2]
  fin_cases i <;> fin_cases j <;> simp [frobenius_def, Fin.rev]

theorem card_fix_radP_le :
    Nat.card {X : HMod 1 F // ∀ x ∈ KGL34P.radP, rhoP hK x X = X} ≤ 2 := by
  refine le_trans ?_ (card_fix_rad_le hK)
  refine Nat.card_le_card_of_injective (fun X => ⟨X.1, fun b c => ?_⟩) ?_
  · have h := X.2 (proj 3 F (KGL34P.rad b c)) (KGL34P.mem_radP.mpr ⟨b, c, rfl⟩)
    rwa [rhoP_proj] at h
  · intro X Y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'

theorem four_le_card_fix_alpha0 (hk : Nat.card F = 4) :
    4 ≤ Nat.card {X : HMod 1 F //
      ∀ x ∈ KGL34P.radP.map (KGL34P.alpha0Aut hk).toMonoidHom, rhoP hK x X = X} := by
  refine le_trans (four_le_card_fix_rad2 hK) ?_
  refine Nat.card_le_card_of_injective (fun X => ⟨X.1, ?_⟩) ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, c, rfl⟩ := KGL34P.mem_radP.mp hx
    show rhoP hK (KGL34P.alpha0Aut hk (proj 3 F (KGL34P.rad b c))) X.1 = X.1
    rw [alpha0Aut_proj_rad hk, rhoP_proj]
    exact X.2 _ _
  · intro X Y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'


omit [Fintype F] hK in
theorem exists_eq_map_conj_projUnitriangular [Finite F] {S : Subgroup (projectiveSL 3 F)}
    (hS : IsSylowTwoOf S ⊤) :
    ∃ x : projectiveSL 3 F, S = (projUnitriangular 3 F).map (MulAut.conj x).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := hS.2.1
  have hSi : ¬ 2 ∣ S.index := by
    have := hS.2.2
    change ¬ 2 ∣ S.relIndex ⊤ at this
    rwa [Subgroup.relIndex_top_right] at this
  let PS : Sylow 2 (projectiveSL 3 F) := hS2.toSylow hSi
  obtain ⟨PU, hPU⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 F) PU PS
  refine ⟨g, ?_⟩
  have hPS : (PS : Subgroup (projectiveSL 3 F)) = S := rfl
  rw [← hPS, ← hg, Sylow.coe_subgroup_smul, hPU]
  ext y
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem map_eq_of_intertwine {β : MulAut (projectiveSL 3 F)} (τ : HMod 1 F ≃ HMod 1 F)
    (hτ : ∀ y X, τ (rhoP hK y X) = rhoP hK (β y) (τ X)) {S Q : Subgroup (projectiveSL 3 F)}
    (hS : IsSylowTwoOf S ⊤) (hβS : S.map β.toMonoidHom = S) (hQS : Q ≤ S)
    (hQ : CFSG.Open.IsElemAbelian 2 Q) (hQc : Nat.card Q = 16) :
    Q.map β.toMonoidHom = Q := by
  have hk : Nat.card F = 4 := by rw [hK]; norm_num
  obtain ⟨x, hx⟩ := exists_eq_map_conj_projUnitriangular hS
  let fx : Subgroup (projectiveSL 3 F) → ℕ := fun R =>
    Nat.card {X : HMod 1 F // ∀ y ∈ R, rhoP hK y X = X}
  have hfβ : ∀ R : Subgroup (projectiveSL 3 F), fx (R.map β.toMonoidHom) = fx R := by
    intro R
    refine (Nat.card_congr (Equiv.subtypeEquiv τ fun X => ?_)).symm
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      show rhoP hK (β y) (τ X) = τ X
      rw [← hτ, h y hy]
    · intro h y hy
      apply τ.injective
      rw [hτ]
      exact h _ ⟨y, hy, rfl⟩
  have hconj : ∀ R : Subgroup (projectiveSL 3 F),
      fx R = fx (R.map (MulAut.conj x⁻¹).toMonoidHom) := by
    intro R
    have h1 : R = (R.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.map_map]
      conv_lhs => rw [← Subgroup.map_id R]
      congr 1
      ext y
      simp
    show Nat.card _ = Nat.card _
    conv_lhs => rw [h1]
    exact card_fix_map_conj (rhoP hK) _ x
  have hU : ∀ R : Subgroup (projectiveSL 3 F), R ≤ S →
      R.map (MulAut.conj x⁻¹).toMonoidHom ≤ projUnitriangular 3 F := by
    intro R hRS
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hRS hy
    rw [hx] at h1
    obtain ⟨u, hu, rfl⟩ := h1
    have e : (MulAut.conj x⁻¹).toMonoidHom ((MulAut.conj x).toMonoidHom u) = u := by
      show (MulAut.conj x⁻¹) ((MulAut.conj x) u) = u
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [e]
    exact hu
  have hE : ∀ R : Subgroup (projectiveSL 3 F), R ≤ S → CFSG.Open.IsElemAbelian 2 R →
      Nat.card R = 16 → R.map (MulAut.conj x⁻¹).toMonoidHom = KGL34P.radP ∨
        R.map (MulAut.conj x⁻¹).toMonoidHom =
          KGL34P.radP.map (KGL34P.alpha0Aut hk).toMonoidHom := by
    intro R hRS hR hRc
    refine KGL34P.eq_radP_or_of_isElemAbelian hk (hU R hRS)
      (H13.isElemAbelian_map_mulEquiv _ hR) ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hRc]
  have hβQS : Q.map β.toMonoidHom ≤ S := by
    rw [← hβS]
    exact Subgroup.map_mono hQS
  have hβQc : Nat.card (Q.map β.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective β.injective, hQc]
  have hrad := card_fix_radP_le hK
  have hal := four_le_card_fix_alpha0 hK hk
  have hfQ := hfβ Q
  have h0 := hconj Q
  have h1 := hconj (Q.map β.toMonoidHom)
  rcases hE Q hQS hQ hQc with e0 | e0 <;>
    rcases hE _ hβQS (H13.isElemAbelian_map_mulEquiv β hQ) hβQc with e1 | e1
  · exact Subgroup.map_injective (MulAut.conj x⁻¹).injective (e1.trans e0.symm)
  · exfalso
    rw [e0] at h0
    rw [e1] at h1
    have : fx KGL34P.radP = fx (KGL34P.radP.map (KGL34P.alpha0Aut hk).toMonoidHom) := by
      rw [← h0, ← h1, hfQ]
    have h2 : fx KGL34P.radP ≤ 2 := hrad
    have h3 : 4 ≤ fx (KGL34P.radP.map (KGL34P.alpha0Aut hk).toMonoidHom) := hal
    omega
  · exfalso
    rw [e0] at h0
    rw [e1] at h1
    have : fx KGL34P.radP = fx (KGL34P.radP.map (KGL34P.alpha0Aut hk).toMonoidHom) := by
      rw [← h0, ← h1, hfQ]
    have h2 : fx KGL34P.radP ≤ 2 := hrad
    have h3 : 4 ≤ fx (KGL34P.radP.map (KGL34P.alpha0Aut hk).toMonoidHom) := hal
    omega
  · exact Subgroup.map_injective (MulAut.conj x⁻¹).injective (e1.trans e0.symm)

end CFSG.Quasithin.H13.B45L34

namespace CFSG.Quasithin.H13.B45L34

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer
  CFSG.Quasithin
open CFSG.Quasithin.H.L3Nine (HMod)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem isElemAbelian_comap_of_injective {M N : Type*} [Group M] [Group N] {f : M →* N}
    (hf : Function.Injective f) {E : Subgroup N} (hE : CFSG.Open.IsElemAbelian 2 E) :
    CFSG.Open.IsElemAbelian 2 (E.comap f) := by
  obtain ⟨hc, hx⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx' => hf (by rw [map_pow, map_one]; exact hx _ hx')⟩
  apply Subtype.ext
  apply hf
  have h1 := hc.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩
  have h2 := congrArg Subtype.val h1
  simpa [map_mul] using h2

theorem mem_normalizer_of_qhatOf_le_two
    {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L)
    (hZ : Subgroup.center ↥L = ⊥)
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 2)
    (hq : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) {S Q : Subgroup (MulAut V)} (hS : IsSylowTwoOf S L)
    (hQS : Q ≤ S) (hQ : CFSG.Open.IsElemAbelian 2 Q) (hQc : Nat.card Q = 16) {g : MulAut V}
    (hg : g ∈ G) (hgS : g ∈ Subgroup.normalizer (S : Set (MulAut V))) :
    g ∈ Subgroup.normalizer (Q : Set (MulAut V)) := by
  obtain ⟨F, _, _, _, hK, e, Φ, hΦ⟩ := exists_herm_model hV hHyp hZ hmodel hq
  have hgL : g ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    B42L2.le_normalizer_of_b4Hyp hHyp hg
  set e' : projectiveSL 3 F →* MulAut V := L.subtype.comp e.toMonoidHom with he'
  have he'i : Function.Injective e' := Subtype.val_injective.comp e.injective
  have he'r : e'.range = L := by
    rw [he', MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmapcomap : ∀ R : Subgroup (MulAut V), R ≤ L → (R.comap e').map e' = R := fun R hR => by
    rw [Subgroup.map_comap_eq, he'r]
    exact inf_eq_right.mpr hR
  let cg : MulAut ↥L := L.normalizerMonoidHom ⟨g, hgL⟩
  let β : MulAut (projectiveSL 3 F) := (e.trans cg).trans e.symm
  have hβ : ∀ y, e' (β y) = g * e' y * g⁻¹ := fun y => by
    show (((e (e.symm (cg (e y)))) : ↥L) : MulAut V) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hβs : ∀ y, e' (β.symm y) = g⁻¹ * e' y * g := fun y => by
    have h1 := hβ (β.symm y)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    group
  let τ : HMod 1 F ≃ HMod 1 F := (Φ.symm.toEquiv.trans g.toEquiv).trans Φ.toEquiv
  have hτ : ∀ y X, τ (rhoP hK y X) = rhoP hK (β y) (τ X) := by
    intro y X
    have h0 : rhoP hK y X = Φ (((e y : ↥L) : MulAut V) (Φ.symm X)) := by
      rw [hΦ, MulEquiv.apply_symm_apply]
    show Φ (g (Φ.symm (rhoP hK y X))) = rhoP hK (β y) (Φ (g (Φ.symm X)))
    rw [h0, MulEquiv.symm_apply_apply, ← hΦ]
    have h1 : ((e (β y) : ↥L) : MulAut V) = g * ((e y : ↥L) : MulAut V) * g⁻¹ := hβ y
    rw [h1]
    simp [MulAut.mul_apply]
  have hSL : S ≤ L := hS.1
  have hQL : Q ≤ L := hQS.trans hSL
  have hS' : IsSylowTwoOf (S.comap e') ⊤ := by
    refine ⟨le_top, hS.2.1.comap_of_injective e' he'i, ?_⟩
    have h1 : ((S.comap e').subgroupOf ⊤).index = (S.comap e').index := by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    rw [h1, Subgroup.index_comap, he'r]
    exact hS.2.2
  have hβS : (S.comap e').map β.toMonoidHom = S.comap e' := by
    ext z
    rw [Subgroup.mem_map_equiv, Subgroup.mem_comap, Subgroup.mem_comap]
    show e' (β.symm z) ∈ S ↔ e' z ∈ S
    rw [hβs]
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgS) (e' z))
    rw [inv_inv] at h1
    exact h1.symm
  have hQS' : Q.comap e' ≤ S.comap e' := Subgroup.comap_mono hQS
  have hQ' : CFSG.Open.IsElemAbelian 2 (Q.comap e') := isElemAbelian_comap_of_injective he'i hQ
  have hQc' : Nat.card (Q.comap e') = 16 := by
    rw [← hQc]
    conv_rhs => rw [← hmapcomap Q hQL]
    rw [Subgroup.card_map_of_injective he'i]
  have key := map_eq_of_intertwine hK τ hτ hS' hβS hQS' hQ' hQc'
  have hmem : ∀ y, β y ∈ Q.comap e' ↔ y ∈ Q.comap e' := fun y => by
    constructor
    · intro h
      rw [← key] at h
      obtain ⟨y', hy', hyy'⟩ := h
      have : y' = y := β.injective hyy'
      rwa [← this]
    · intro h
      rw [← key]
      exact ⟨y, h, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq'
    obtain ⟨y, -, rfl⟩ := he'r ▸ hQL hq'
    have h1 : y ∈ Q.comap e' := hq'
    have h2 := (hmem y).mpr h1
    rw [Subgroup.mem_comap, hβ] at h2
    exact h2
  · intro hq'
    have hqL : q ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgL) _).mp (hQL hq')
      simpa [mul_assoc] using h1
    obtain ⟨y, -, rfl⟩ := he'r ▸ hqL
    have h1 : β y ∈ Q.comap e' := by
      rw [Subgroup.mem_comap, hβ]
      exact hq'
    exact (hmem y).mp h1

end CFSG.Quasithin.H13.B45L34
