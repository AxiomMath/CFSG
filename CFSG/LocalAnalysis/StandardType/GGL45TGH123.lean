module

public import CFSG.LocalAnalysis.StandardType.GGL45TGCent
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA Matrix
open GGL45TA (diagGL coe_diagGL scalar_mem_center pow_prime_pow_eq_one)
open GGL45TA.LinSetting (torusVec_pow)

variable {d : ℕ} {k : Type} [Field k] {D : GData d k}

theorem projMk_ker_le (h : D.H) (hh : h ∈ (LargeEvenProjMk D.H).ker) :
    (h : GL (Fin d) k) ∈ LargeEvenScalars (Fin d) k := by
  rw [QuotientGroup.ker_mk'] at hh
  exact Subgroup.mem_subgroupOf.mp hh

theorem implements_injective_of_surj {K : Type} [Group K] {π : D.H →* K}
    (hπ : Function.Surjective π) {a b : MulAut K} {x : GL (Fin d) k} (hxA : x ∈ D.A)
    (ha : Implements π a x) (hb : Implements π b x) : a = b := by
  ext y
  obtain ⟨h0, rfl⟩ := hπ y
  let m : D.H := ⟨x * h0 * x⁻¹, D.conj_mem x hxA h0 h0.2⟩
  rw [ha h0 m rfl, hb h0 m rfl]

@[expose] noncomputable def conjH (A : GL (Fin d) k) (hA : A ∈ D.A) : D.H →* D.H where
  toFun h := ⟨A * h * A⁻¹, D.conj_mem A hA h h.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjH (A : GL (Fin d) k) (hA : A ∈ D.A) (h : D.H) :
    ((conjH A hA h : D.H) : GL (Fin d) k) = A * h * A⁻¹ := rfl

theorem implements_of_mod_center {K : Type} [Group K] {π : D.H →* K} {α : MulAut K}
    {A : GL (Fin d) k} (hA : A ∈ D.A)
    (h : ∀ y : D.H, ((α (π y))⁻¹ * π (conjH A hA y)) ∈ Subgroup.center K) :
    Implements π α A := by
  haveI hperf : Group.IsPerfect D.H := (Subgroup.isPerfect_iff (H := D.H)).mpr D.perf
  let χ : D.H →* K :=
    { toFun := fun y => (α (π y))⁻¹ * π (conjH A hA y)
      map_one' := by simp
      map_mul' := fun a b => by
        have hb := Subgroup.mem_center_iff.mp (h a)
        simp only [map_mul, _root_.mul_inv_rev]
        calc (α (π b))⁻¹ * (α (π a))⁻¹ * (π (conjH A hA a) * π (conjH A hA b))
            = (α (π b))⁻¹ * ((α (π a))⁻¹ * π (conjH A hA a)) * π (conjH A hA b) := by group
          _ = (α (π b))⁻¹ * (α (π b) * ((α (π a))⁻¹ * π (conjH A hA a))) *
                (α (π b))⁻¹ * π (conjH A hA b) := by
              rw [hb (α (π b))]; group
          _ = (α (π a))⁻¹ * π (conjH A hA a) * ((α (π b))⁻¹ * π (conjH A hA b)) := by group }
  have hχ : ∀ y, χ y = 1 := by
    intro y
    have hy : y ∈ commutator D.H := Group.IsPerfect.mem_commutator
    have hle : commutator D.H ≤ χ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have hca := Subgroup.mem_center_iff.mp (h a)
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (hca (χ b)).symm
    exact hle hy
  intro y y' hy'
  have h1 : (α (π y))⁻¹ * π (conjH A hA y) = 1 := hχ y
  have h2 : conjH A hA y = y' := Subtype.ext (by rw [coe_conjH, hy'])
  rw [h2] at h1
  exact (inv_mul_eq_one.mp h1)

theorem torusVec_pElt {p : ℕ} (i j : Fin d) {u : kˣ} (hu : GGL45IsPElt p u) (l : Fin d) :
    GGL45IsPElt p (NbrLangTypeA.torusVec i j u l) := by
  obtain ⟨a, ha⟩ := hu
  refine ⟨a, ?_⟩
  rw [NbrLangTypeA.torusVec_apply, mul_pow]
  split_ifs <;> simp [ha]

namespace GSetting

variable [Finite k] {K : Type} [Group K] {p q₀ : ℕ} {ψ : MulAut K} {E : Subgroup (MulAut K)}

theorem inducedAut_implements (S : GSetting p q₀ d k D K ψ E)
    {θ : K ⧸ Subgroup.center K ≃* LargeEvenProj D.H}
    (hθ : ∀ h, θ (S.π h : K ⧸ Subgroup.center K) = LargeEvenProjMk D.H h) {e : MulAut K}
    {x : GL (Fin d) k} (hx : Implements S.π e x) :
    Implements (LargeEvenProjMk D.H) (ggInducedAut θ e) x := by
  intro h h' hh'
  rw [← hθ, ggInducedAut_apply, hx h h' hh', hθ]

theorem inducedAut_semilin (S : GSetting p q₀ d k D K ψ E)
    {θ : K ⧸ Subgroup.center K ≃* LargeEvenProj D.H}
    (hθ : ∀ h, θ (S.π h : K ⧸ Subgroup.center K) = LargeEvenProjMk D.H h) :
    SemilinImpl (LargeEvenProjMk D.H) (ggInducedAut θ ψ) 1 S.τ := by
  intro h h' hh'
  rw [← hθ, ggInducedAut_apply, S.ψ_impl h h' hh', hθ]

theorem comm_lifts_of_commR (S : GSetting p q₀ d k D K ψ E)
    {θ : K ⧸ Subgroup.center K ≃* LargeEvenProj D.H}
    (hθ : ∀ h, θ (S.π h : K ⧸ Subgroup.center K) = LargeEvenProjMk D.H h) {u : MulAut _}
    {A : GL (Fin d) k} (hAA : A ∈ D.A) (hA : Implements (LargeEvenProjMk D.H) u A)
    (hu : ∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) :
    ∀ y, S.IsLift y → A * y = y * A := by
  have hscal : ∀ y, S.IsLift y → A * y * A⁻¹ * y⁻¹ ∈ LargeEvenScalars (Fin d) k := by
    rintro y ⟨hyA, -, e, he, hye⟩
    have hyR := S.inducedAut_implements hθ hye
    have h1 := hA.mul hyA hyR
    have h2 := hyR.mul hAA hA
    rw [hu e he] at h1
    obtain ⟨c, hc⟩ := implements_unique projMk_ker_le (D.A.mul_mem hAA hyA)
      (D.A.mul_mem hyA hAA) h1 h2
    have hcen := Subgroup.mem_center_iff.mp (scalar_mem_center (d := d) (k := k) ⟨c, rfl⟩)
    have hAy : A * y = y * A * Matrix.GeneralLinearGroup.scalar (Fin d) c := by
      rw [hc]; group
    refine ⟨c, ?_⟩
    rw [hAy]
    have hconj : y * A * Matrix.GeneralLinearGroup.scalar (Fin d) c * (y * A)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin d) c := by
      rw [hcen (y * A), mul_inv_cancel_right]
    rw [_root_.mul_inv_rev, ← mul_assoc] at hconj
    exact hconj.symm
  intro y hy
  exact S.commute_of_comm_scalar hscal hy

theorem comm_lifts_of_fixed (S : GSetting p q₀ d k D K ψ E) {y : D.H}
    (hy : ∀ e ∈ E, e (S.π y) = S.π y) : ∀ x, S.IsLift x → (y : GL (Fin d) k) * x = x * y := by
  have hscal : ∀ x, S.IsLift x →
      (y : GL (Fin d) k) * x * (y : GL (Fin d) k)⁻¹ * x⁻¹ ∈ LargeEvenScalars (Fin d) k := by
    rintro x ⟨hxA, -, e, he, hxe⟩
    let m : D.H := ⟨x * y * x⁻¹, D.conj_mem x hxA y y.2⟩
    have h1 : S.π m = S.π y := (hxe y m rfl).symm.trans (hy e he)
    have h2 : m * y⁻¹ ∈ S.π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := S.ker_le _ h2
    have h4 : ((m * y⁻¹ : D.H) : GL (Fin d) k) = (y * x * y⁻¹ * x⁻¹ : GL (Fin d) k)⁻¹ := by
      simp only [m, Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [h4] at h3
    simpa using (LargeEvenScalars (Fin d) k).inv_mem h3
  intro x hx
  exact S.commute_of_comm_scalar hscal hx

theorem ker_trivial_of_three (S : GSetting p q₀ d k D K ψ E) (hd : d = 3) :
    ∀ h ∈ S.π.ker, h = 1 := by
  classical
  intro h hh
  by_contra hne
  obtain ⟨z, hz⟩ := S.ker_le h hh
  have hd1 : 1 ≤ d := by omega
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hne (Subtype.ext (by rw [← hz, map_one]; rfl))
  have hz3 : z ^ 3 = 1 := by
    have hdet : ((h : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).det = 1 := D.det_one h h.2
    rw [← hz, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, hd] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  have hzprim : IsPrimitiveRoot z 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hz3 hz1)
  have hcen : ∀ κ ∈ Subgroup.center K, κ = 1 := by
    intro κ hκ
    obtain ⟨y, rfl⟩ := S.surj κ
    have hy : (y : GL (Fin d) k) ∈ LargeEvenScalars (Fin d) k := by
      refine mem_scalars_of_conj_eq S.ker_le (D.le_A y.2) fun h₁ h₂ hh₂ => ?_
      have h₂eq : h₂ = y * h₁ * y⁻¹ := Subtype.ext (by rw [hh₂]; rfl)
      rw [h₂eq, map_mul, map_mul, map_inv, ← Subgroup.mem_center_iff.mp hκ (S.π h₁),
        mul_inv_cancel_right]
    obtain ⟨w, hw⟩ := hy
    have hw3 : w ^ 3 = 1 := by
      have hdet : ((y : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).det = 1 := D.det_one y y.2
      rw [← hw, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hd] at hdet
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
    obtain ⟨i, -, hi⟩ := hzprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 w).mpr hw3)
    have hyh : y = h ^ i := Subtype.ext (by
      rw [Subgroup.coe_pow, ← hw, ← hz, ← map_pow, hi])
    rw [hyh, map_pow, hh, one_pow]
  have hcard : Nat.card (Subgroup.center K) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext (by rw [hcen a a.2, hcen b b.2])⟩,
      ⟨1⟩⟩
  have hp := S.a2 hd
  rw [hcard] at hp
  exact S.hp.one_lt.ne' (Nat.dvd_one.mp hp)

theorem torusH123 (S : GSetting p q₀ d k D K ψ E) {S_I : Set (GL (Fin d) k)}
    (hSI : S_I ⊆ (D.A : Set (GL (Fin d) k))) {θ : K ⧸ Subgroup.center K ≃* LargeEvenProj D.H}
    (hθ : ∀ h, θ (S.π h : K ⧸ Subgroup.center K) = LargeEvenProjMk D.H h) :
    GGL45TorusH123 p (LargeEvenMatConjImage (LargeEvenProjMk D.H) S_I) θ ψ E := by
  classical
  obtain ⟨s, m, k', hs2, hqm, hpm, hpk', hq₀⟩ := S.exists_pval
  have hπRsurj : Function.Surjective (LargeEvenProjMk D.H) :=
    QuotientGroup.mk'_surjective _
  have hexp : ∀ A : GL (Fin d) k, (∀ x, S.IsLift x → A * x = x * A) → ∀ a : ℕ,
      A ^ p ^ a ∈ LargeEvenScalars (Fin d) k → A ^ p ^ s ∈ LargeEvenScalars (Fin d) k := by
    intro A hA a ha
    let q := QuotientGroup.mk' (LargeEvenScalars (Fin d) k)
    have h1 : q A ^ p ^ a = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ha
    have h2 : q A ^ (p ^ s * m) = 1 := by
      rw [← map_pow, ← hqm, S.pow_card_sub_one_of_comm_lifts hA, map_one]
    have h3 := pow_prime_pow_eq_one S.hp h1 h2 hpm
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3
  refine ⟨s, hs2, (q₀ : ℤ), k', hpk', by rw [hq₀], ?_, ?_, ?_⟩
  ·
    refine ⟨fun u v hu hv => ?_, fun u hu => ?_⟩
    · obtain ⟨⟨A, hAS, hA0⟩, huE, -⟩ := hu
      obtain ⟨⟨B, hBS, hB0⟩, hvE, -⟩ := hv
      have hAA : A ∈ D.A := hSI hAS
      have hBA : B ∈ D.A := hSI hBS
      have hA : Implements (LargeEvenProjMk D.H) u A := hA0
      have hB : Implements (LargeEvenProjMk D.H) v B := hB0
      have hAc := S.comm_lifts_of_commR hθ hAA hA huE
      have hBc := S.comm_lifts_of_commR hθ hBA hB hvE
      have hAB := S.comm_of_comm_lifts hAc hBc
      have h1 := hA.mul hBA hB
      have h2 := hB.mul hAA hA
      rw [← hAB] at h2
      exact implements_injective_of_surj hπRsurj (D.A.mul_mem hAA hBA) h1 h2
    · obtain ⟨⟨A, hAS, hA0⟩, huE, a, hua⟩ := hu
      have hAA : A ∈ D.A := hSI hAS
      have hA : Implements (LargeEvenProjMk D.H) u A := hA0
      have hAc := S.comm_lifts_of_commR hθ hAA hA huE
      have hAa : A ^ p ^ a ∈ LargeEvenScalars (Fin d) k := by
        have h := hA.pow hAA (p ^ a)
        rw [hua] at h
        exact mem_scalars_of_implements_one projMk_ker_le (D.A.pow_mem hAA _) h
      have hAs := hexp A hAc a hAa
      refine ⟨implements_injective_of_surj hπRsurj (D.A.pow_mem hAA _) (hA.pow hAA _)
        (implements_one_of_scalar hAs), ?_⟩
      have hf := (S.inducedAut_semilin hθ).conj D.A.one_mem hAA hA
      rw [one_mul, inv_one, mul_one, S.map_tau_of_comm_lifts hAc] at hf
      rw [zpow_natCast]
      exact implements_injective_of_surj hπRsurj (D.A.pow_mem hAA _) hf (hA.pow hAA q₀)
  ·
    have hS : ∀ h : K, GGL45InS p E h → ∃ y : D.H, S.π y = h ∧
        ∀ x, S.IsLift x → (y : GL (Fin d) k) * x = x * y := by
      intro h hh
      obtain ⟨y, rfl⟩ := S.surj h
      exact ⟨y, rfl, S.comm_lifts_of_fixed hh.2⟩
    refine ⟨fun h t hh ht => ?_, fun h hh => ?_, fun α hα hαE h hh => ?_⟩
    · obtain ⟨y, rfl, hy⟩ := hS h hh
      obtain ⟨y', rfl, hy'⟩ := hS t ht
      have h1 : y * y' = y' * y := Subtype.ext (by
        simp only [Subgroup.coe_mul]; exact S.comm_of_comm_lifts hy hy')
      rw [← map_mul, h1, map_mul]
    · obtain ⟨y, rfl, hy⟩ := hS h hh
      refine ⟨?_, ?_⟩
      · obtain ⟨a, ha⟩ := hh.1
        have h2 : S.π y ^ (p ^ s * m) = 1 := by
          rw [← hqm, ← map_pow]
          have : y ^ (Nat.card k - 1) = 1 := Subtype.ext (by
            rw [Subgroup.coe_pow, Subgroup.coe_one]; exact S.pow_card_sub_one_of_comm_lifts hy)
          rw [this, map_one]
        exact pow_prime_pow_eq_one S.hp ha h2 hpm
      · rw [zpow_natCast, ← map_pow]
        exact S.ψ_impl y (y ^ q₀) (by
          rw [one_mul, inv_one, mul_one, Subgroup.coe_pow, S.map_tau_of_comm_lifts hy])
    · obtain ⟨y, rfl, hy⟩ := hS h hh
      have hαI := (ggL45_inducesIn_iff θ _ α).mp hα
      obtain ⟨A, hAS, hA0⟩ := hαI
      have hAA : A ∈ D.A := hSI hAS
      have hA : Implements (LargeEvenProjMk D.H) (ggInducedAut θ α) A := hA0
      have hαcomm : ∀ e ∈ E, ggInducedAut θ α * ggInducedAut θ e =
          ggInducedAut θ e * ggInducedAut θ α := fun e he => by
        rw [← map_mul, ← map_mul, hαE e he]
      have hAc := S.comm_lifts_of_commR hθ hAA hA hαcomm
      have hαK : Implements S.π α A := by
        refine implements_of_mod_center hAA fun y₁ => ?_
        have h1 : θ ((α (S.π y₁) : K) : K ⧸ Subgroup.center K) =
            θ ((S.π (conjH A hAA y₁) : K) : K ⧸ Subgroup.center K) := by
          rw [← ggInducedAut_apply, hθ, hθ]
          exact hA y₁ (conjH A hAA y₁) rfl
        have h2 := θ.injective h1
        rw [QuotientGroup.eq] at h2
        exact h2
      have hAy : A * (y : GL (Fin d) k) = y * A := S.comm_of_comm_lifts hAc hy
      exact hαK y y (by rw [hAy, mul_inv_cancel_right])
  ·
    have hd3 := S.three_le
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
    have hgm : orderOf (g ^ m) = p ^ s := by
      have hm0 : m ≠ 0 := fun h0 => hpm (h0 ▸ dvd_zero p)
      rw [orderOf_pow_of_dvd hm0 (by rw [hg, Nat.card_units, hqm]; exact dvd_mul_left m _), hg,
        Nat.card_units, hqm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    set ζ := g ^ m with hζ
    set ζp := ζ ^ p ^ (s - 1) with hζp
    have hζpord : orderOf ζp = p := by
      rw [hζp, orderOf_pow_of_dvd (pow_ne_zero _ S.hp.ne_zero)
        (by rw [hgm]; exact pow_dvd_pow p (Nat.sub_le s 1)), hgm,
        Nat.pow_div (Nat.sub_le s 1) S.hp.pos, Nat.sub_sub_self (by omega), pow_one]
    have hζp1 : ζp ≠ 1 := fun h => by
      rw [h, orderOf_one] at hζpord
      exact S.hp.one_lt.ne hζpord
    have hζs : ζ ^ p ^ s = 1 := by rw [← hgm]; exact pow_orderOf_eq_one ζ
    have hζpE : GGL45IsPElt p ζ := ⟨s, hζs⟩
    obtain ⟨P, hPτ, hdiagL, -, hPH⟩ := S.exists_frame
    let T : Fin d → Fin d → ∀ u : kˣ, GGL45IsPElt p u → D.H := fun i j u hu =>
      ⟨P⁻¹ * diagGL d (NbrLangTypeA.torusVec i j u) * P,
        hPH _ (NbrLangTypeA.prod_torusVec i j u) (torusVec_pElt i j hu)⟩
    have hpow' : ∀ {u : kˣ} (hu : GGL45IsPElt p u) (n : ℕ), GGL45IsPElt p (u ^ n) := by
      rintro u ⟨a, ha⟩ n
      exact ⟨a, by rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]⟩
    have hTpow : ∀ i j u (hu : GGL45IsPElt p u) (n : ℕ),
        (T i j u hu) ^ n = T i j (u ^ n) (hpow' hu n) := by
      intro i j u hu n
      apply Subtype.ext
      simp only [T, Subgroup.coe_pow]
      rw [show P⁻¹ * diagGL d (NbrLangTypeA.torusVec i j u) * P =
        P⁻¹ * diagGL d (NbrLangTypeA.torusVec i j u) * P⁻¹⁻¹ by rw [inv_inv], conj_pow,
        ← map_pow, inv_inv, torusVec_pow]
    have hTcomm : ∀ i j u hu, ∀ x, S.IsLift x →
        x * (T i j u hu : GL (Fin d) k) = (T i j u hu) * x := by
      intro i j u hu x hx
      obtain ⟨t, -, ht⟩ := hdiagL x hx
      have hx' : x = P⁻¹ * diagGL d t * P := by rw [← ht]; group
      have hst : diagGL d t * diagGL d (NbrLangTypeA.torusVec i j u) =
          diagGL d (NbrLangTypeA.torusVec i j u) * diagGL d t := by
        rw [← map_mul, ← map_mul, mul_comm]
      simp only [T]
      rw [hx']
      calc P⁻¹ * diagGL d t * P * (P⁻¹ * diagGL d (NbrLangTypeA.torusVec i j u) * P)
          = P⁻¹ * (diagGL d t * diagGL d (NbrLangTypeA.torusVec i j u)) * P := by group
        _ = P⁻¹ * (diagGL d (NbrLangTypeA.torusVec i j u) * diagGL d t) * P := by rw [hst]
        _ = _ := by group
    have hTfix : ∀ i j u hu, ∀ e ∈ E, e (S.π (T i j u hu)) = S.π (T i j u hu) := by
      intro i j u hu e he
      obtain ⟨x, hxA, hxp, hxe⟩ := S.exists_lift he
      exact hxe _ _ (by rw [hTcomm i j u hu x ⟨hxA, hxp, e, he, hxe⟩, mul_inv_cancel_right])
    have hT1 : ∀ i j (h1 : GGL45IsPElt p (1 : kˣ)), T i j 1 h1 = 1 := fun i j h1 =>
      Subtype.ext (by
        simp only [T, NbrLangTypeA.torusVec_one, map_one, mul_one, inv_mul_cancel,
          OneMemClass.coe_one])
    have hTcongr : ∀ i j (u v : kˣ) (hu : GGL45IsPElt p u) (hv : GGL45IsPElt p v), u = v →
        T i j u hu = T i j v hv := by
      rintro i j u v hu hv rfl
      rfl
    have hTinS : ∀ i j, GGL45InS p E (S.π (T i j ζ hζpE)) := fun i j => ⟨⟨s, by
        rw [← map_pow, hTpow i j ζ hζpE (p ^ s),
          hTcongr i j _ 1 (hpow' hζpE (p ^ s)) ⟨0, by simp⟩ hζs, hT1 i j ⟨0, by simp⟩, map_one]⟩,
      hTfix i j ζ hζpE⟩
    have hconst : ∀ (v : Fin d → kˣ) (c : kˣ),
        P⁻¹ * diagGL d v * P = Matrix.GeneralLinearGroup.scalar (Fin d) c → ∀ l, v l = c := by
      intro v c hvc l
      have hcen := Subgroup.mem_center_iff.mp (scalar_mem_center (d := d) (k := k) ⟨c, rfl⟩)
      have h1 : diagGL d v = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
        calc diagGL d v = P * (P⁻¹ * diagGL d v * P) * P⁻¹ := by group
          _ = P * Matrix.GeneralLinearGroup.scalar (Fin d) c * P⁻¹ := by rw [hvc]
          _ = Matrix.GeneralLinearGroup.scalar (Fin d) c := by rw [hcen P, mul_inv_cancel_right]
      have h2 := congrArg (fun g : GL (Fin d) k => (g : Matrix (Fin d) (Fin d) k) l l) h1
      simp only [coe_diagGL, diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
        scalar_apply] at h2
      exact Units.ext h2
    have hcenK : ∀ y : D.H, S.π y ∈ Subgroup.center K →
        (y : GL (Fin d) k) ∈ LargeEvenScalars (Fin d) k := by
      intro y hy
      refine mem_scalars_of_conj_eq S.ker_le (D.le_A y.2) fun h₁ h₂ hh₂ => ?_
      have h₂eq : h₂ = y * h₁ * y⁻¹ := Subtype.ext (by rw [hh₂]; rfl)
      rw [h₂eq, map_mul, map_mul, map_inv, ← Subgroup.mem_center_iff.mp hy (S.π h₁),
        mul_inv_cancel_right]
    have hd0 : 0 < d := by omega
    let i₀ : Fin d := ⟨0, by omega⟩
    let i₁ : Fin d := ⟨1, by omega⟩
    let i₂ : Fin d := ⟨2, by omega⟩
    have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
    have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
    have hζpE' : GGL45IsPElt p ζp := hpow' hζpE _
    have hpow1 : ∀ i j, (S.π (T i j ζ hζpE)) ^ p ^ (s - 1) = S.π (T i j ζp hζpE') := fun i j => by
      rw [← map_pow, hTpow i j ζ hζpE]
    have hnotcen : S.π (T i₀ i₁ ζp hζpE') ∉ Subgroup.center K := by
      intro hc
      obtain ⟨c, hc⟩ := hcenK _ hc
      have h1 := hconst _ c hc.symm
      have h2 := h1 i₀
      have h3 := h1 i₂
      rw [NbrLangTypeA.torusVec_apply] at h2 h3
      simp only [if_true, h01, if_false, mul_one, Ne.symm h02, Ne.symm h12, one_mul] at h2 h3
      exact hζp1 (h2.trans h3.symm)
    refine ⟨⟨S.π (T i₀ i₁ ζ hζpE), hTinS i₀ i₁, by rw [hpow1]; exact hnotcen⟩,
      S.π (T i₀ i₁ ζp hζpE'), S.π (T i₁ i₂ ζp hζpE'), ⟨_, hTinS i₀ i₁, (hpow1 i₀ i₁).symm⟩,
      ⟨_, hTinS i₁ i₂, (hpow1 i₁ i₂).symm⟩, hnotcen, fun a b hab => ?_⟩
    have hker : (T i₀ i₁ ζp hζpE') ^ a * (T i₁ i₂ ζp hζpE') ^ b ∈ S.π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_pow, map_pow, hab]
    obtain ⟨c, hc⟩ := S.ker_le _ hker
    have hval : ((T i₀ i₁ ζp hζpE' ^ a * T i₁ i₂ ζp hζpE' ^ b : D.H) : GL (Fin d) k) =
        P⁻¹ * diagGL d (NbrLangTypeA.torusVec i₀ i₁ (ζp ^ a) *
          NbrLangTypeA.torusVec i₁ i₂ (ζp ^ b)) * P := by
      rw [hTpow i₀ i₁ ζp hζpE' a, hTpow i₁ i₂ ζp hζpE' b, Subgroup.coe_mul, map_mul]
      simp only [T]
      group
    rw [hval] at hc
    have hconst' := hconst _ c hc.symm
    have hc1 : c = 1 := by
      rcases Nat.lt_or_ge d 4 with hd4 | hd4
      · have hd : d = 3 := by omega
        have h1 := S.ker_trivial_of_three hd _ hker
        have h2 : ((T i₀ i₁ ζp hζpE' ^ a * T i₁ i₂ ζp hζpE' ^ b : D.H) :
            GL (Fin d) k) = 1 := by rw [h1]; rfl
        rw [hval] at h2
        have h3 := hconst _ 1 (by rw [h2, map_one]) i₀
        rw [hconst' i₀] at h3
        exact h3
      · let i₃ : Fin d := ⟨3, by omega⟩
        have h1 := hconst' i₃
        rw [Pi.mul_apply, NbrLangTypeA.torusVec_apply, NbrLangTypeA.torusVec_apply] at h1
        have h30 : i₃ ≠ i₀ := by simp [i₃, i₀, Fin.ext_iff]
        have h31 : i₃ ≠ i₁ := by simp [i₃, i₁, Fin.ext_iff]
        have h32 : i₃ ≠ i₂ := by simp [i₃, i₂, Fin.ext_iff]
        simp only [h30, h31, h32, if_false, mul_one] at h1
        exact h1.symm
    have hA := hconst' i₀
    have hB := hconst' i₂
    rw [hc1, Pi.mul_apply, NbrLangTypeA.torusVec_apply, NbrLangTypeA.torusVec_apply] at hA hB
    simp only [if_true, h01, if_false, mul_one, h02, Ne.symm h02, Ne.symm h12, one_mul] at hA hB
    have hord : orderOf ζp = p := hζpord
    constructor
    · rw [← hord]; exact orderOf_dvd_of_pow_eq_one hA
    · rw [← hord]; exact orderOf_dvd_of_pow_eq_one (inv_eq_one.mp hB)

end GSetting

end CFSG.StandardType.GGL45TG
