module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOne3Defs
public import CFSG.LocalAnalysis.StandardType.GGKD2Spec1615
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6NoAct
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.Sporadic.Th.Max3.Core

public section

namespace CFSG.StandardType

open CFSG.Assembly

private lemma ltrkd5c3_induced_unique {R L' : Type} [Group R] [Group L'] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) {c : MulAut L'} {φ₁ φ₂ : MulAut R}
    (h₁ : ∀ l : L', φ₁ (ψ l) = ψ (c l)) (h₂ : ∀ l : L', φ₂ (ψ l) = ψ (c l)) : φ₁ = φ₂ := by
  ext r
  obtain ⟨l, rfl⟩ := hψ r
  rw [h₁, h₂]

private lemma ltrkd5c3_congr_apply_theta {G H : Type} [Group G] [Group H] (theta : G ≃* H)
    (φ : MulAut G) (r : G) : (MulAut.congr theta φ) (theta r) = theta (φ r) := by
  simp [MulAut.congr_apply]

private lemma ltrkd5c3_odd_relIndex_inndiagU {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K) (hn : 1 ≤ n) {d : ℕ}
    (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ n = 2)) (hd1 : 1 ≤ d) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Odd ((MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))).range.relIndex
      (InndiagSU.inndiagU h hd1)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_prime_form_full_semilinear_realization
      h (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := K) (n := d))
      hd hq
  rw [InndiagSU.range_conj_eq_comap_inner h hd1, InndiagSU.inndiagU, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective
      (MulAut.congr (InndiagSU.projEquiv h hd1)).surjective]
  refine Odd.of_dvd_nat ?_ hcard
  have : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
  exact this.add_one

theorem ggSU6NoParabolicKnown3_of_strong (h : S2MathAs3_1615.StrongKD2) :
    ∀ f : ℕ, 3 ∣ 2 ^ f + 1 →
      LargeEvenLabelAll (⟨.twA, 5, f⟩ : LargeEvenLabel) fun R _ I _ => GGSU6NoParabolicAt3 I := by
  intro f hf
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf0 | hfpos
    · subst hf0; norm_num at hf
    · exact hfpos
  have hmem : LargeEvenInLambda2 (⟨.twA, 5, f⟩ : LargeEvenLabel) :=
    ⟨hf1, by norm_num, fun h => absurd h (by norm_num)⟩
  refine LargeEvenLabelAll.mono (fun R _ I _ hs => ?_) (h ⟨.twA, 5, f⟩ hmem)
  intro L' _ _ ψ hψsurj hψker hψcomm e J a hsetup A hAab hAcard heA haA hAind hAJ
  intro V hVne hV2 hVI hnorm
  classical
  obtain ⟨-, hmodel⟩ := hs L' ψ hψsurj hψker hψcomm e J a hsetup
  obtain ⟨k, hkfield, hkfinite, hkdata, theta, alpha, halpha, hfieldtype, htrans⟩ := hmodel
  letI := hkfield
  letI := hkfinite
  let χ : A → MulAut R := fun c => (hAind c.1 c.2).choose
  have hχmem : ∀ c : A, χ c ∈ I := fun c => (hAind c.1 c.2).choose_spec.1
  have hχspec : ∀ c : A, ∀ l : L', χ c (ψ l) = ψ (c.1 l) :=
    fun c => (hAind c.1 c.2).choose_spec.2
  have hχone : χ 1 = 1 := by
    apply ltrkd5c3_induced_unique ψ hψsurj (c := (1 : MulAut L'))
    · intro l; simpa using hχspec 1 l
    · intro l; simp
  have hχmul : ∀ c d : A, χ (c * d) = χ c * χ d := by
    intro c d
    apply ltrkd5c3_induced_unique ψ hψsurj (c := ((c * d : A) : MulAut L'))
    · intro l; exact hχspec (c * d) l
    · intro l
      simp only [MulAut.mul_apply]
      rw [hχspec d l, hχspec c (d.1 l)]
      rfl
  let χhom : A →* MulAut R := { toFun := χ, map_one' := hχone, map_mul' := hχmul }
  let Ab : Subgroup (MulAut R) := Subgroup.map χhom ⊤
  have hAb_mem : ∀ φ : MulAut R, φ ∈ Ab ↔ ∃ c : A, χhom c = φ := by
    intro φ
    change φ ∈ Subgroup.map χhom ⊤ ↔ ∃ c : A, χhom c = φ
    rw [Subgroup.mem_map]
    refine ⟨?_, ?_⟩
    · rintro ⟨y, -, hy⟩; exact ⟨y, hy⟩
    · rintro ⟨c, hc⟩; exact ⟨c, trivial, hc⟩
  have hχker : ∀ k : A, χ k = 1 → k = 1 := by
    intro k hk
    have hpoint : ∀ x : L', k.1 x = x := by
      intro x
      exact USixTwo.fix_of_perfect (π := ψ) hψker (X := ⊤) (a' := k.1)
        (by rw [← commutator_def]; exact hψcomm)
        (fun y _ => by simp [MonoidHom.mem_ker, ← hχspec k y, hk]) x trivial
    exact Subtype.ext (by ext x; simpa using hpoint x)
  have hχinj : Function.Injective χhom := by
    intro c d hcd
    have h1 : χhom (c * d⁻¹) = 1 := by rw [map_mul, hcd, map_inv, mul_inv_cancel]
    have hk := hχker (c * d⁻¹) h1
    rwa [mul_inv_eq_one] at hk
  have hAbI : ∀ φ ∈ Ab, φ ∈ I := by
    intro φ hφ
    obtain ⟨c, hc⟩ := (hAb_mem φ).mp hφ
    rw [← hc]
    exact hχmem c
  have hAbab : CFSG.Open.IsElemAbelian 3 Ab := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      obtain ⟨c, hc⟩ := (hAb_mem x.1).mp x.2
      obtain ⟨d, hd⟩ := (hAb_mem y.1).mp y.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc, ← hd, ← map_mul, ← map_mul]
      congr 1
      exact hAab.1.is_comm.comm c d
    · intro x hx
      obtain ⟨c, hc⟩ := (hAb_mem x).mp hx
      rw [← hc, ← map_pow]
      have hc3 : c ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hAab.2 c.1 c.2
      rw [hc3, map_one]
  have hAbcardA : Nat.card Ab = Nat.card A := by
    change Nat.card ↥(Subgroup.map χhom ⊤) = Nat.card ↥A
    rw [Subgroup.card_map_of_injective hχinj, Subgroup.card_top]
  have hK4 : Nat.card k = (2 ^ 1) ^ 2 := by rw [hkdata.card]; norm_num
  let R' : Type := LargeEvenProj (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 k 6)
  let Phi : MulAut R →* MulAut R' := (MulAut.congr theta).toMonoidHom
  have hPhi_inj : Function.Injective Phi := by
    intro a b hab
    exact (MulAut.congr theta).injective hab
  let Ab' : Subgroup (MulAut R') := Subgroup.map Phi Ab
  let V' : Subgroup (MulAut R') := Subgroup.map Phi V
  have hI_inndiag : ∀ φ ∈ I, Phi φ ∈ InndiagSU.inndiagU (d := 6) hkdata (by norm_num) := by
    intro φ hφ
    obtain ⟨beta, hbeta, hbetarel⟩ := htrans φ hφ
    have hEq : Phi φ = beta := by
      ext r'
      obtain ⟨r, rfl⟩ := theta.surjective r'
      change (MulAut.congr theta φ) (theta r) = beta (theta r)
      rw [ltrkd5c3_congr_apply_theta theta φ r, hbetarel r]
    rw [hEq]
    exact hbeta
  have hAb'_inndiag : Ab' ≤ InndiagSU.inndiagU (d := 6) hkdata (by norm_num) := by
    intro φ' hφ'
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hφ'
    exact hI_inndiag φ (hAbI φ hφ)
  have hAb'ab : CFSG.Open.IsElemAbelian 3 Ab' := CFSG.Open.IsElemAbelian.map hAbab Phi
  have hAb'card : 3 ^ 3 ≤ Nat.card Ab' := by
    have hcard : Nat.card Ab' = Nat.card Ab := by
      change Nat.card ↥(Subgroup.map Phi Ab) = Nat.card ↥Ab
      rw [Subgroup.card_map_of_injective hPhi_inj]
    have hcard' : Nat.card Ab' = 3 ^ 3 := by rw [hcard, hAbcardA, hAcard]
    exact hcard'.ge
  have hφe_eq : Phi (χhom ⟨e, heA⟩) = alpha := by
    ext r'
    obtain ⟨r, rfl⟩ := theta.surjective r'
    obtain ⟨l, rfl⟩ := hψsurj r
    change (MulAut.congr theta (χhom ⟨e, heA⟩)) (theta (ψ l)) = alpha (theta (ψ l))
    rw [ltrkd5c3_congr_apply_theta theta (χhom ⟨e, heA⟩) (ψ l)]
    change theta (χ ⟨e, heA⟩ (ψ l)) = alpha (theta (ψ l))
    rw [hχspec ⟨e, heA⟩ l, halpha l]
  have hfield_type : ∃ a ∈ Ab', CFSG.LocalAnalysis.GLTheoremA.T171Sh.FieldType hkdata a :=
    ⟨alpha, by
      rw [← hφe_eq]
      exact Subgroup.mem_map.mpr
        ⟨χhom ⟨e, heA⟩, (hAb_mem _).mpr ⟨⟨e, heA⟩, rfl⟩, rfl⟩, hfieldtype⟩
  have hV'2 : IsPGroup 2 V' := IsPGroup.map hV2 Phi
  have hV'ne : V' ≠ ⊥ := by
    intro h0
    apply hVne
    rw [Subgroup.eq_bot_iff_forall]
    intro v hv
    have hmem : Phi v ∈ V' := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact hPhi_inj (by rw [hmem, map_one])
  have hV'conj : ∀ φ ∈ Ab', ∀ v ∈ V', φ * v * φ⁻¹ ∈ V' := by
    intro φ' hφ' v' hv'
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hφ'
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hv'
    obtain ⟨c, hc⟩ := (hAb_mem φ).mp hφ
    have hmem : χhom c * v * (χhom c)⁻¹ ∈ V :=
      hnorm c.1 c.2 (χhom c) (hχspec c) v hv
    rw [← hc, ← map_mul, ← map_inv, ← map_mul]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  have hodd :=
    ltrkd5c3_odd_relIndex_inndiagU (n := 1) (d := 6) hkdata (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hK4
  have hV'I : V' ≤ InndiagSU.inndiagU (d := 6) hkdata (by norm_num) := by
    intro v' hv'
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hv'
    have hcl : Subgroup.closure I ≤
        (InndiagSU.inndiagU (d := 6) hkdata (by norm_num)).comap Phi :=
      (Subgroup.closure_le _).mpr (fun φ hφ => hI_inndiag φ hφ)
    exact hcl (hVI hv)
  have hV'inn : V' ≤ (MulAut.conj : R' →* MulAut R').range := by
    intro v hv
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hV'2 ⟨v, hv⟩
    rw [Subgroup.orderOf_mk] at hj
    exact mem_range_conj_of_pow_two_pow (D := InndiagSU.inndiagU (d := 6) hkdata (by norm_num))
      hodd (hV'I hv) (by rw [← hj]; exact pow_orderOf_eq_one v)
  have hR'center : Subgroup.center R' = ⊥ :=
    TableBUE.center_proj_eq_bot (d := 6) (n := 1) (K := k) hK4 (by norm_num) (by norm_num)
  have hconj_inj : Function.Injective (MulAut.conj : R' →* MulAut R') := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : x ∈ Subgroup.center R' := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hh := congrFun (congrArg DFunLike.coe hx) g
      simp only [MulAut.conj_apply, MulAut.one_apply] at hh
      rw [mul_inv_eq_iff_eq_mul] at hh
      exact hh.symm
    rw [hR'center] at hx'
    simpa using hx'
  let V₀ : Subgroup R' := V'.comap (MulAut.conj : R' →* MulAut R')
  have hV0map : Subgroup.map (MulAut.conj : R' →* MulAut R') V₀ = V' :=
    Subgroup.map_comap_eq_self hV'inn
  have hV0ne : V₀ ≠ ⊥ := by
    intro h0
    exact hV'ne (by rw [← hV0map, h0, Subgroup.map_bot])
  let conjV : V₀ →* V' :=
    { toFun := fun x => ⟨(MulAut.conj : R' →* MulAut R') x.1, Subgroup.mem_comap.mp x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have hconjV_inj : Function.Injective conjV := by
    intro x y hxy
    apply Subtype.ext
    apply hconj_inj
    exact congrArg Subtype.val hxy
  have hV02 : IsPGroup 2 V₀ := IsPGroup.of_injective hV'2 conjV hconjV_inj
  have hV0norm : ∀ φ ∈ Ab', ∀ v ∈ V₀, φ v ∈ V₀ := by
    intro φ hφ v hv
    rw [Subgroup.mem_comap]
    have hmem : φ * (MulAut.conj : R' →* MulAut R') v * φ⁻¹ ∈ V' :=
      hV'conj φ hφ ((MulAut.conj : R' →* MulAut R') v) (Subgroup.mem_comap.mp hv)
    have hconj_eq : (MulAut.conj : R' →* MulAut R') (φ v) =
        φ * (MulAut.conj : R' →* MulAut R') v * φ⁻¹ := by
      ext g
      simp [MulAut.mul_apply, map_mul]
    rw [hconj_eq]
    exact hmem
  exact hV0ne (CFSG.LocalAnalysis.GLTheoremA.T171Sh.u6NoActModel_holds 1 k hkdata (by norm_num)
    Ab' hAb'ab hAb'_inndiag hAb'card hfield_type V₀ hV02 hV0norm)

end CFSG.StandardType

end
