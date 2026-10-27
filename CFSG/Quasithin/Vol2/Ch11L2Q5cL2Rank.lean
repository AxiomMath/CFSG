module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts36K
public import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.Quasithin.Vol2.Ch10SecALiftSyl
public import CFSG.Quasithin.Vol2.KGNatG2Order

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipSL_mulVec unipSL_mul_self
  exists_conj_unip)

variable {U : Type} [CommGroup U]

theorem apply_mul_inv_fixed (hU : ∀ u : U, u ^ 2 = 1) {r : MulAut U} (hr : r * r = 1) (w : U) :
    r (r w * w⁻¹) = r w * w⁻¹ := by
  have hinv : ∀ x : U, x⁻¹ = x := fun x => by
    rw [inv_eq_iff_mul_eq_one, ← sq, hU]
  have hrr : r (r w) = w := by
    have := congrArg (fun φ : MulAut U => φ w) hr
    simpa [MulAut.mul_apply] using this
  rw [map_mul, map_inv, hrr, hinv (r w), hinv w, mul_comm]

theorem sl2_inv_mulVec_mulVec {K : Type} [Field K] (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (v : Fin 2 → K) :
    ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
      ((A : Matrix (Fin 2) (Fin 2) K).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem sl2_mulVec_inv_mulVec {K : Type} [Field K] (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (v : Fin 2 → K) :
    (A : Matrix (Fin 2) (Fin 2) K).mulVec
      (((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem exists_adapted_coord {Gm R : Subgroup (MulAut U)} {W C : Subgroup U} {e : ℕ} (he : 1 ≤ e)
    (hR : IsSylowTwoOf R Gm) (hnat : BinaryNaturalSL Gm W C 2 e) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ e ∧
      ∃ (φ : Matrix.SpecialLinearGroup (Fin 2) K →* ↥Gm) (Fh : ↥W →* Multiplicative (Fin 2 → K)),
        Function.Bijective φ ∧ Function.Surjective Fh ∧ (∀ u : ↥W, Fh u = 1 ↔ (u : U) ∈ C) ∧
        (∀ g : ↥Gm, ∀ u ∈ W, (g : MulAut U) u ∈ W) ∧
        (∀ (p : Matrix.SpecialLinearGroup (Fin 2) K) (u : ↥W)
            (hu : ((φ p : ↥Gm) : MulAut U) u ∈ W),
          Multiplicative.toAdd (Fh ⟨((φ p : ↥Gm) : MulAut U) u, hu⟩) =
            (p : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (Fh u))) ∧
        ∀ p : Matrix.SpecialLinearGroup (Fin 2) K,
          ((φ p : ↥Gm) : MulAut U) ∈ R ↔ ∃ b : K, p = unipSL b := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := hnat
  have : CharP K 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hK
  have hπi : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  have hπs : Function.Surjective π := hπ.1
  have hWG : ∀ g : ↥Gm, ∀ u ∈ W, (g : MulAut U) u ∈ W := hπ.2.2.2.1
  obtain ⟨f, hfs, hfk, hfe⟩ := G64.RealizesVia.exists_secMap rfl hπ
  let F₀ : ↥W →* Multiplicative (Fin 2 → K) :=
    { toFun := fun u => ((f u).val : Multiplicative (Fin 2 → K))
      map_one' := by
        show ((f 1).val : Multiplicative (Fin 2 → K)) = 1
        rw [map_one]
        rfl
      map_mul' := fun x y => by
        show ((f (x * y)).val : Multiplicative (Fin 2 → K)) = _
        rw [map_mul]
        rfl }
  have hF₀ : ∀ u : ↥W, F₀ u = ((f u).val : Multiplicative (Fin 2 → K)) := fun u => rfl
  have hF₀s : Function.Surjective F₀ := by
    intro m
    obtain ⟨u, hu⟩ := hfs ⟨m, trivial⟩
    refine ⟨u, ?_⟩
    rw [hF₀, hu]
  have hF₀k : ∀ u : ↥W, F₀ u = 1 ↔ (u : U) ∈ C := by
    intro u
    rw [← hfk u, hF₀]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  set e₀ := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K with he₀
  set φ₀ : Matrix.SpecialLinearGroup (Fin 2) K →* ↥Gm := π.comp e₀.toMonoidHom with hφ₀
  have hφ₀i : Function.Injective φ₀ := hπi.comp e₀.injective
  have hφ₀s : Function.Surjective φ₀ := hπs.comp e₀.surjective
  have hF₀e : ∀ (p : Matrix.SpecialLinearGroup (Fin 2) K) (u : ↥W)
      (hu : ((φ₀ p : ↥Gm) : MulAut U) u ∈ W),
      Multiplicative.toAdd (F₀ ⟨((φ₀ p : ↥Gm) : MulAut U) u, hu⟩) =
        (p : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (F₀ u)) := by
    intro p u hu
    have h1 := hfe (e₀ p) u hu
    rw [hF₀, hF₀, show ((f ⟨((φ₀ p : ↥Gm) : MulAut U) u, hu⟩).val :
      Multiplicative (Fin 2 → K)) = _ from h1]
    rfl
  set R' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := (R.subgroupOf Gm).comap φ₀ with hR'
  have hR'2 : IsPGroup 2 R' :=
    (hR.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hR.1).symm).comap_of_injective φ₀ hφ₀i
  have hR'idx : ¬ 2 ∣ R'.index := by
    rw [hR', Subgroup.index_comap_of_surjective _ hφ₀s]
    exact hR.2.2
  obtain ⟨g, hgR, hRg⟩ := exists_conj_unip hK hR'2 hR'idx
  set φ : Matrix.SpecialLinearGroup (Fin 2) K →* ↥Gm :=
    φ₀.comp (MulAut.conj g⁻¹).toMonoidHom with hφ
  have hφapp : ∀ p, φ p = φ₀ (g⁻¹ * p * g) := fun p => by
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  let Mg : Multiplicative (Fin 2 → K) →* Multiplicative (Fin 2 → K) :=
    { toFun := fun v => Multiplicative.ofAdd
        ((g : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd v))
      map_one' := by
        apply Multiplicative.toAdd.injective
        simp
      map_mul' := fun a b => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_add] }
  have hMg : ∀ v, Multiplicative.toAdd (Mg v) =
      (g : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd v) := fun v => rfl
  have hMgi : Function.Injective Mg := by
    intro a b hab
    have h := congrArg (fun m => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd m)) hab
    simp only [hMg, sl2_inv_mulVec_mulVec] at h
    exact Multiplicative.toAdd.injective h
  have hMgs : Function.Surjective Mg := by
    intro v
    refine ⟨Multiplicative.ofAdd (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd v)), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hMg, toAdd_ofAdd, sl2_mulVec_inv_mulVec]
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, φ, Mg.comp F₀, ?_, hMgs.comp hF₀s,
    fun u => ?_, hWG, fun p u hu => ?_, fun p => ?_⟩
  · refine ⟨hφ₀i.comp (MulAut.conj g⁻¹).injective, hφ₀s.comp (MulAut.conj g⁻¹).surjective⟩
  · rw [MonoidHom.comp_apply, ← hF₀k u]
    exact ⟨fun h => hMgi (h.trans (map_one Mg).symm), fun h => by rw [h, map_one]⟩
  · have hu' : ((φ₀ (g⁻¹ * p * g) : ↥Gm) : MulAut U) u ∈ W := by rw [← hφapp]; exact hu
    have hsub : (⟨((φ p : ↥Gm) : MulAut U) u, hu⟩ : ↥W) =
        ⟨((φ₀ (g⁻¹ * p * g) : ↥Gm) : MulAut U) u, hu'⟩ :=
      Subtype.ext (show ((φ p : ↥Gm) : MulAut U) u =
        ((φ₀ (g⁻¹ * p * g) : ↥Gm) : MulAut U) u by rw [hφapp])
    show Multiplicative.toAdd (Mg (F₀ ⟨((φ p : ↥Gm) : MulAut U) u, hu⟩)) =
      (p : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (Mg (F₀ u)))
    rw [hsub, hMg, hMg, hF₀e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      show g * (g⁻¹ * p * g) = p * g by group]
  · rw [hφapp]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := hgR (g⁻¹ * p * g) h
      exact ⟨b, by rw [← hb]; group⟩
    · rintro ⟨b, rfl⟩
      exact hRg b

theorem natural_sylow_fix (hU : ∀ u : U, u ^ 2 = 1) {Gm R : Subgroup (MulAut U)}
    {W C : Subgroup U} {e : ℕ} (he : 1 ≤ e) (hCG : ∀ g ∈ Gm, ∀ c ∈ C, g c = c)
    (hR : IsSylowTwoOf R Gm) (hnat : BinaryNaturalSL Gm W C 2 e) :
    (∀ w ∈ W, (∀ r ∈ R, r w * w⁻¹ ∈ C) → w ∈ fixV R) ∧
      ((W ⊓ fixV R).subgroupOf W).index = 2 ^ e := by
  obtain ⟨K, _, _, _, hK, φ, Fh, ⟨hφi, hφs⟩, hFs, hFk, hWG, hFe, hφR⟩ :=
    exists_adapted_coord he hR hnat
  have hsq : ∀ b : K, unipSL b * unipSL b = 1 := unipSL_mul_self
  let ℓh : Multiplicative K →* Multiplicative (Fin 2 → K) :=
    { toFun := fun a => Multiplicative.ofAdd ![Multiplicative.toAdd a, 0]
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i <;> simp
      map_mul' := fun a b => by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i <;> simp }
  set ℓ := ℓh.range with hℓ
  have hmemℓ : ∀ v : Fin 2 → K, Multiplicative.ofAdd v ∈ ℓ ↔ v 1 = 0 := by
    intro v
    constructor
    · rintro ⟨a, ha⟩
      have := congrFun (congrArg Multiplicative.toAdd ha) 1
      simpa [ℓh] using this.symm
    · intro hv
      refine ⟨Multiplicative.ofAdd (v 0), ?_⟩
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i <;> simp [ℓh, hv]
  have hmodC : ∀ u : ↥W, (∀ r ∈ R, r (u : U) * (u : U)⁻¹ ∈ C) →
      Multiplicative.toAdd (Fh u) 1 = 0 := by
    intro u hu
    have hr : ((φ (unipSL 1) : ↥Gm) : MulAut U) ∈ R := (hφR _).mpr ⟨1, rfl⟩
    have hc := hu _ hr
    have h1 : Fh ⟨((φ (unipSL 1) : ↥Gm) : MulAut U) u, hWG _ u u.2⟩ = Fh u := by
      have hmem : (⟨((φ (unipSL 1) : ↥Gm) : MulAut U) u * (u : U)⁻¹,
          W.mul_mem (hWG _ u u.2) (W.inv_mem u.2)⟩ : ↥W) =
          ⟨((φ (unipSL 1) : ↥Gm) : MulAut U) u, hWG _ u u.2⟩ * u⁻¹ := rfl
      have h2 := (hFk ⟨((φ (unipSL 1) : ↥Gm) : MulAut U) u * (u : U)⁻¹,
        W.mul_mem (hWG _ u u.2) (W.inv_mem u.2)⟩).mpr hc
      rw [hmem, map_mul, map_inv, mul_inv_eq_one] at h2
      exact h2
    have h3 := hFe (unipSL 1) u (hWG _ u u.2)
    rw [h1, coe_unipSL, unipSL_mulVec, one_mul] at h3
    have h4 := congrFun h3 0
    simp only [Matrix.cons_val_zero] at h4
    linear_combination -h4
  have h1 : ∀ w ∈ W, (∀ r ∈ R, r w * w⁻¹ ∈ C) → w ∈ fixV R := by
    intro w hw hwC r hr
    obtain ⟨p, hp⟩ := hφs ⟨r, hR.1 hr⟩
    have hrp : r = ((φ p : ↥Gm) : MulAut U) := by rw [hp]
    obtain ⟨b, rfl⟩ := (hφR p).mp (hrp ▸ hr)
    by_cases hb : b = 0
    · rw [hrp, hb, Vol2.Ch10.SecA.unipSL_zero, map_one]
      rfl
    have hw1 := hmodC ⟨w, hw⟩ hwC
    obtain ⟨w', hw'⟩ := hFs (Multiplicative.ofAdd
      ![0, Multiplicative.toAdd (Fh ⟨w, hw⟩) 0 / b])
    set c : U := (w : U)⁻¹ * (r (w' : U) * (w' : U)⁻¹) with hcdef
    have hrw' : r (w' : U) ∈ W := by rw [hrp]; exact hWG _ w' w'.2
    have hcC : c ∈ C := by
      have hmem : (⟨c, W.mul_mem (W.inv_mem hw) (W.mul_mem hrw' (W.inv_mem w'.2))⟩ : ↥W) =
          (⟨w, hw⟩ : ↥W)⁻¹ * (⟨r (w' : U), hrw'⟩ * w'⁻¹) := rfl
      apply (hFk ⟨c, _⟩).mp
      rw [hmem, map_mul, map_inv, map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      have hrw'' : (⟨r (w' : U), hrw'⟩ : ↥W) =
          ⟨((φ (unipSL b) : ↥Gm) : MulAut U) w', hWG _ w' w'.2⟩ :=
        Subtype.ext (show r (w' : U) = ((φ (unipSL b) : ↥Gm) : MulAut U) w' by rw [hrp])
      rw [hrw'']
      simp only [toAdd_mul, toAdd_inv, toAdd_one]
      rw [hFe, hw', toAdd_ofAdd, coe_unipSL, unipSL_mulVec]
      funext i
      fin_cases i
      · simp [mul_div_cancel₀ _ hb]
      · simp [hw1]
    have hwc : (w : U) = r (w' : U) * (w' : U)⁻¹ * c⁻¹ := by
      rw [hcdef]
      group
    have hrr : r * r = 1 := by
      rw [hrp, ← Subgroup.coe_mul, ← map_mul, hsq b, map_one]
      rfl
    have hrc : r c = c := hCG r (hR.1 hr) c hcC
    rw [hwc, map_mul, map_inv, hrc, apply_mul_inv_fixed hU hrr]
  refine ⟨h1, ?_⟩
  have hcomap : (W ⊓ fixV R).subgroupOf W = ℓ.comap Fh := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, ← ofAdd_toAdd (Fh u), hmemℓ]
    constructor
    · rintro ⟨-, hu⟩
      exact hmodC u fun r hr => by rw [hu r hr, mul_inv_cancel]; exact C.one_mem
    · intro hu
      refine ⟨u.2, h1 u u.2 fun r hr => ?_⟩
      obtain ⟨p, hp⟩ := hφs ⟨r, hR.1 hr⟩
      have hrp : r = ((φ p : ↥Gm) : MulAut U) := by rw [hp]
      obtain ⟨b, rfl⟩ := (hφR p).mp (hrp ▸ hr)
      have hru : r (u : U) ∈ W := by rw [hrp]; exact hWG _ u u.2
      have hmem : (⟨r (u : U) * (u : U)⁻¹, W.mul_mem hru (W.inv_mem u.2)⟩ : ↥W) =
          ⟨r (u : U), hru⟩ * u⁻¹ := rfl
      apply (hFk ⟨_, W.mul_mem hru (W.inv_mem u.2)⟩).mp
      rw [hmem, map_mul, map_inv, mul_inv_eq_one]
      apply Multiplicative.toAdd.injective
      have hru' : (⟨r (u : U), hru⟩ : ↥W) =
          ⟨((φ (unipSL b) : ↥Gm) : MulAut U) u, hWG _ u u.2⟩ :=
        Subtype.ext (show r (u : U) = ((φ (unipSL b) : ↥Gm) : MulAut U) u by rw [hrp])
      rw [hru', hFe, coe_unipSL, unipSL_mulVec, hu, mul_zero, add_zero]
      funext i
      fin_cases i
      · rfl
      · exact hu.symm
  rw [hcomap, Subgroup.index_comap_of_surjective _ hFs]
  have hℓi : Function.Injective ℓh := by
    intro a b hab
    have h := congrFun (congrArg Multiplicative.toAdd hab) 0
    simpa [ℓh] using h
  have hcardℓ : Nat.card ℓ = 2 ^ e := by
    rw [hℓ, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hℓi, Subgroup.card_top]
    rw [Nat.card_congr Multiplicative.toAdd]
    exact hK
  have hcardN : Nat.card (Multiplicative (Fin 2 → K)) = 2 ^ e * 2 ^ e := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, hK]
    ring
  have h3 := ℓ.index_mul_card
  rw [hcardℓ, hcardN] at h3
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h3

omit [CommGroup U] in
theorem map_inf_map_of_ker_le {Q : Type*} [Group U] [Group Q] (f : U →* Q) {X Y : Subgroup U}
    (hX : f.ker ≤ X) : X.map f ⊓ Y.map f = (X ⊓ Y).map f := by
  refine le_antisymm ?_ (Subgroup.map_inf_le _ _ _)
  rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
  refine ⟨y, ⟨?_, hy⟩, hxy⟩
  have hk : x⁻¹ * y ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have := X.mul_mem hx (hX hk)
  rwa [mul_inv_cancel_left] at this

theorem factL2NatRank_holds : FactL2NatRank := by
  intro U _ _ hU Gm R e he _ hR s W hCW hind hsup hnat
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := fixV Gm with hCdef
  have hCG : ∀ g ∈ Gm, ∀ c ∈ C, g c = c := fun g hg c hc => hc g hg
  have hper := fun i => natural_sylow_fix hU (by omega : 1 ≤ e) hCG hR (hnat i)
  have hCR : C ≤ fixV R := fun c hc r hr => hc r (hR.1 hr)
  have hWG : ∀ i, ∀ g ∈ Gm, ∀ u ∈ W i, g u ∈ W i := by
    intro i g hg u hu
    obtain ⟨K, _, _, -, π, hπ⟩ := hnat i
    exact hπ.2.2.2.1 ⟨g, hg⟩ u hu
  set q : U →* U ⧸ C := QuotientGroup.mk' C with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective C
  have hqk : q.ker = C := QuotientGroup.ker_mk' C
  have hmapC : C.map q = ⊥ := by rw [Subgroup.map_eq_bot_iff, hqk]
  have hmemq : ∀ {X : Subgroup U}, C ≤ X → ∀ x : U, q x ∈ X.map q ↔ x ∈ X := by
    intro X hX x
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, hqk, sup_eq_left.mpr hX]
  set Wb : Fin s → Subgroup (U ⧸ C) := fun i => (W i).map q with hWb
  set Pb : Fin s → Subgroup (U ⧸ C) := fun i => (W i ⊓ fixV R).map q with hPb
  have hPW : ∀ i, Pb i ≤ Wb i := fun i => Subgroup.map_mono inf_le_left
  have hindb : iSupIndep Wb := by
    intro i
    rw [disjoint_iff]
    have h1 : (⨆ (j : Fin s) (_ : j ≠ i), Wb j) =
        (C ⊔ ⨆ (j : Fin s) (_ : j ≠ i), W j).map q := by
      rw [Subgroup.map_sup, hmapC, bot_sup_eq, Subgroup.map_iSup]
      congr 1
      funext j
      rw [Subgroup.map_iSup]
    rw [h1, map_inf_map_of_ker_le q (by rw [hqk]; exact hCW i), hind i, hmapC]
  have hsupb : (⨆ i, Wb i) = ⊤ := by
    have h1 := congrArg (Subgroup.map q) hsup
    rwa [Subgroup.map_sup, hmapC, bot_sup_eq, Subgroup.map_iSup,
      Subgroup.map_top_of_surjective q hqs] at h1
  have hcommW : Pairwise fun i j : Fin s => ∀ x y : U ⧸ C, x ∈ Wb i → y ∈ Wb j →
      Commute x y := fun _ _ _ x y _ _ => Commute.all x y
  have hcommP : Pairwise fun i j : Fin s => ∀ x y : U ⧸ C, x ∈ Pb i → y ∈ Pb j →
      Commute x y := fun _ _ _ x y _ _ => Commute.all x y
  set Φ := Subgroup.noncommPiCoprod hcommW with hΦ
  set ΦP := Subgroup.noncommPiCoprod hcommP with hΦP
  have hΦi : Function.Injective Φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hindb
  have hΦPi : Function.Injective ΦP :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (hindb.mono hPW)
  have hΦs : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range, hsupb]
  have hΦapp : ∀ y : (i : Fin s) → ↥(Wb i), Φ y = ∏ i, (y i : U ⧸ C) := by
    intro y
    rw [hΦ, Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]
  have hfix : (fixV R).map q = ⨆ i, Pb i := by
    refine le_antisymm ?_ (iSup_le fun i => Subgroup.map_mono inf_le_right)
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨y, hy⟩ := hΦs (q u)
    have hyi : ∀ i, ∃ w ∈ W i, q w = (y i : U ⧸ C) := fun i => (y i).2
    choose w hwW hwq using hyi
    have hprod : q (∏ i, w i) = q u := by
      rw [map_prod, ← hy, hΦapp]
      exact Finset.prod_congr rfl fun i _ => hwq i
    have hmod : ∀ i, ∀ r ∈ R, r (w i) * (w i)⁻¹ ∈ C := by
      intro i r hr
      have hrW : ∀ j, r (w j) * (w j)⁻¹ ∈ W j := fun j =>
        (W j).mul_mem (hWG j r (hR.1 hr) _ (hwW j)) ((W j).inv_mem (hwW j))
      set y' : (j : Fin s) → ↥(Wb j) := fun j =>
        ⟨q (r (w j) * (w j)⁻¹), Subgroup.mem_map_of_mem q (hrW j)⟩ with hy'
      have hy'1 : Φ y' = 1 := by
        rw [hΦapp]
        have : (∏ j, (y' j : U ⧸ C)) = q (r (∏ j, w j) * (∏ j, w j)⁻¹) := by
          rw [map_mul, map_inv, map_prod, map_prod, map_prod, ← Finset.prod_inv_distrib,
            ← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun j _ => by
            show q (r (w j) * (w j)⁻¹) = _
            rw [map_mul, map_inv]
        rw [this]
        have hc : (∏ j, w j) * u⁻¹ ∈ C := by
          rw [← hqk, MonoidHom.mem_ker, map_mul, map_inv, hprod, mul_inv_cancel]
        obtain ⟨c, hcC, hcu⟩ : ∃ c ∈ C, (∏ j, w j) = c * u :=
          ⟨_, hc, by rw [inv_mul_cancel_right]⟩
        rw [hcu, map_mul r c u, hu r hr, hCG r (hR.1 hr) c hcC, mul_inv_cancel, map_one]
      have hy'eq : y' = 1 := hΦi (hy'1.trans (map_one Φ).symm)
      have := congrArg (fun z : (j : Fin s) → ↥(Wb j) => ((z i : ↥(Wb i)) : U ⧸ C)) hy'eq
      simp only [hy', Pi.one_apply, OneMemClass.coe_one] at this
      rw [← hqk, MonoidHom.mem_ker]
      exact this
    have hwP : ∀ i, q (w i) ∈ Pb i := fun i =>
      Subgroup.mem_map_of_mem q ⟨hwW i, (hper i).1 _ (hwW i) (hmod i)⟩
    rw [← hprod, map_prod]
    exact Subgroup.prod_mem _ fun i _ => Subgroup.mem_iSup_of_mem i (hwP i)
  have hcardQ : Nat.card (U ⧸ C) = ∏ i, Nat.card (Wb i) := by
    rw [← Nat.card_congr (MulEquiv.ofBijective Φ ⟨hΦi, hΦs⟩).toEquiv, Nat.card_pi]
  have hcardP : Nat.card ↥(⨆ i, Pb i) = ∏ i, Nat.card (Pb i) := by
    rw [← Subgroup.noncommPiCoprod_range (hcomm := hcommP),
      ← Nat.card_congr (MonoidHom.ofInjective hΦPi).toEquiv, Nat.card_pi]
  have hrel : ∀ i, Nat.card (Wb i) = 2 ^ e * Nat.card (Pb i) := by
    intro i
    have h1 := (Pb i).relIndex_mul_card (K := Wb i)
    rw [inf_eq_left.mpr (hPW i)] at h1
    rw [← h1]
    congr 1
    rw [Subgroup.relIndex, ← (hper i).2]
    set ρ : ↥(W i) →* ↥(Wb i) := q.subgroupMap (W i) with hρ
    have hρs : Function.Surjective ρ := MonoidHom.subgroupMap_surjective _ _
    rw [← Subgroup.index_comap_of_surjective _ hρs]
    congr 1
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show q (x : U) ∈ Pb i ↔ (x : U) ∈ W i ⊓ fixV R
    exact hmemq (le_inf (hCW i) hCR) x
  have hidx : (fixV R).index = (2 ^ e) ^ s := by
    rw [← Subgroup.index_map_eq (H := fixV R) hqs (by rw [hqk]; exact hCR), hfix]
    have h1 := (⨆ i, Pb i).index_mul_card
    rw [hcardP, hcardQ, Finset.prod_congr rfl fun i _ => hrel i, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    have hpos : 0 < ∏ i, Nat.card (Pb i) :=
      Finset.prod_pos fun i _ => Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  rw [rkIdx, hidx, ← pow_mul, padicValNat.prime_pow, mul_comm]

end CFSG.Quasithin.Vol2.Ch11.SecB
