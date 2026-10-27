module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitRank
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace OrdPNS

section Roots

variable {K : Type*} [Field K] [Finite K] {ℓ : ℕ}

theorem eq_one_of_pow_eq_one (hℓ : ℓ.Prime) (hK : ¬ ℓ ∣ Nat.card K - 1) {x : K}
    (hx : x ^ ℓ = 1) : x = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hℓ.ne_zero] at hx
    exact zero_ne_one hx
  have h1 : x ^ (Nat.card K - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one x hx0
  have hcop : ℓ.gcd (Nat.card K - 1) = 1 := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hK
  have h2 := pow_gcd_eq_one.mpr ⟨hx, h1⟩
  rwa [hcop, pow_one] at h2

theorem exists_pow_eq (hℓ : ℓ.Prime) (hK : ¬ ℓ ∣ Nat.card K - 1) (c : Kˣ) :
    ∃ μ : Kˣ, μ ^ ℓ = c := by
  have : Finite Kˣ := instFiniteUnits
  have hinj : Function.Injective fun μ : Kˣ => μ ^ ℓ := by
    intro μ ν hμν
    have hμν' : μ ^ ℓ = ν ^ ℓ := hμν
    have h1 : ((μ / ν : Kˣ) : K) ^ ℓ = 1 := by
      rw [← Units.val_pow_eq_pow_val, div_pow, hμν', div_self', Units.val_one]
    have h2 := eq_one_of_pow_eq_one hℓ hK h1
    exact div_eq_one.mp (Units.ext h2)
  exact Finite.injective_iff_surjective.mp hinj c

theorem det_eq_one_of_pow_eq_one {n : ℕ} (hℓ : ℓ.Prime) (hK : ¬ ℓ ∣ Nat.card K - 1)
    {x : Matrix (Fin n) (Fin n) K} (hx : x ^ ℓ = 1) : x.det = 1 :=
  eq_one_of_pow_eq_one hℓ hK (by rw [← det_pow, hx, det_one])

end Roots

section Gen

variable {K : Type} [Field K] [Finite K] {n ℓ : ℕ}

theorem exists_elemAbelian_of_set (hℓ : ℓ.Prime) (hK : ¬ ℓ ∣ Nat.card K - 1)
    (S : Set (GL (Fin n) K)) (hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y) (hSp : ∀ x ∈ S, x ^ ℓ = 1) :
    ∃ F : Subgroup (Matrix.SpecialLinearGroup (Fin n) K), IsElemAbelian ℓ F ∧
      Nat.card S ≤ Nat.card F ∧
      (∀ u ∈ F, u ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) → u = 1) ∧
      (∀ X : GL (Fin n) K, (∀ x ∈ S, Commute x X) →
        ∀ u ∈ F, Commute (Matrix.SpecialLinearGroup.toGL u) X) ∧
      (∀ σ : K →+* K, (∀ x ∈ S, GeneralLinearGroup.map σ x = x) →
        ∀ u ∈ F, Matrix.SpecialLinearGroup.map σ u = u) := by
  set C := Subgroup.closure S with hC
  have hCc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
    have hcomm := Subgroup.isMulCommutative_closure (k := S) fun x hx y hy _ => hSc x hx y hy
    exact fun x hx y hy => congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hCp : ∀ x ∈ C, x ^ ℓ = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hSp x hx
    | one => exact one_pow ℓ
    | mul x y hx hy ihx ihy => rw [(Commute.mul_pow (hCc x hx y hy) ℓ), ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  have hCdet : ∀ x ∈ C, x ∈ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
    intro x hx
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [GeneralLinearGroup.val_det_apply, Units.val_one]
    refine det_eq_one_of_pow_eq_one hℓ hK ?_
    rw [← Units.val_pow_eq_pow_val, hCp x hx, Units.val_one]
  set F := C.comap (Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K) with hF
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K) :=
    Matrix.SpecialLinearGroup.toGL_injective
  refine ⟨F, ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun u hu => hinj ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hCc _ a.2 _ b.2
  · rw [map_pow, hCp _ hu, map_one]
  ·
    have hιF : ∀ x : S, ∃ u : Matrix.SpecialLinearGroup (Fin n) K,
        Matrix.SpecialLinearGroup.toGL u = x.1 := fun x => hCdet x.1 (Subgroup.subset_closure x.2)
    choose ι hι using hιF
    let ι' : S → F := fun x => ⟨ι x, by
      change Matrix.SpecialLinearGroup.toGL (ι x) ∈ C
      rw [hι]
      exact Subgroup.subset_closure x.2⟩
    have hι' : Function.Injective ι' := fun x y hxy => Subtype.ext (by
      have h1 := congrArg (fun u : F =>
        Matrix.SpecialLinearGroup.toGL (u : Matrix.SpecialLinearGroup (Fin n) K)) hxy
      simp only [ι', hι] at h1
      exact h1)
    exact Nat.card_le_card_of_injective ι' hι'
  ·
    intro u hu hz
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    have hup := hCp _ hu
    ext i j
    have hr1 : r = 1 := by
      refine eq_one_of_pow_eq_one hℓ hK ?_
      have h1 := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) i i) hup
      simp only [Units.val_pow_eq_pow_val, Units.val_one, one_apply_eq] at h1
      have h2 : ((Matrix.SpecialLinearGroup.toGL u : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = scalar (Fin n) r := hr.symm
      rw [h2, ← map_pow, scalar_apply, diagonal_apply_eq] at h1
      exact h1
    rw [← hr, hr1, map_one]
    rfl
  ·
    intro X hX u hu
    have hle : C ≤ Subgroup.centralizer {X} := by
      rw [hC, Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hX x hx).eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hu)
  ·
    intro σ hσ u hu
    have hle : C ≤ MonoidHom.eqLocus (GeneralLinearGroup.map σ) (MonoidHom.id _) := by
      rw [hC, Subgroup.closure_le]
      intro x hx
      exact hσ x hx
    refine hinj ?_
    have h1 : Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map σ u) =
        GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL u) := by
      ext i j
      rfl
    rw [h1]
    exact hle hu

end Gen

section Sylow

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {Bs G₀ : Subgroup G}
  {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}

theorem exists_conj_mem_centralizer_of_card (hS : GGSixFusionSetting p Bs G₀ Δ t n f ψ)
    {E : Subgroup G} (hEM : E ≤ Subgroup.normalizer (G₀ : Set G)) (hE : IsElemAbelian p E)
    (hcard : Nat.card Bs ≤ Nat.card E) {y : G} (hy : ∀ x ∈ E, y * x = x * y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact p.Prime := ⟨hS.prime⟩
  obtain ⟨P, hBsP, hPM, huniq⟩ := hS.exists_sylow
  have hEp : IsPGroup p (E.subgroupOf (Subgroup.normalizer (G₀ : Set G))) := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hx : ((x : Subgroup.normalizer (G₀ : Set G)) : G) ∈ E := Subgroup.mem_subgroupOf.mp x.2
    simpa using hE.2 _ hx
  obtain ⟨Q, hQ⟩ := hEp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (Subgroup.normalizer (G₀ : Set G)) (P.subtype hPM) Q
  have hconj : ∀ x ∈ E, (c : G)⁻¹ * x * c ∈ (P : Subgroup G) := by
    intro x hx
    have hxQ : (⟨x, hEM hx⟩ : Subgroup.normalizer (G₀ : Set G)) ∈ (Q : Subgroup _) :=
      hQ (Subgroup.mem_subgroupOf.mpr hx)
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hxQ
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hxQ
  set E' := E.map (MulAut.conj (c : G)⁻¹).toMonoidHom with hE'
  have hE'P : E' ≤ (P : Subgroup G) := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hconj x hx
  have hE'el : IsElemAbelian p E' := isElemAbelian_map_hom hE _
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj _).injective
  have heq : E' = Bs := huniq E' hE'P hE'el
    (le_antisymm (hS.card_le_card_bstar hE'el) (hE'card ▸ hcard))
  refine ⟨c, c.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  rw [← heq] at hb
  obtain ⟨x, hx, rfl⟩ := hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have h1 := hy x hx
  calc (c : G)⁻¹ * x * c * ((c : G)⁻¹ * y * c) = (c : G)⁻¹ * (x * y) * c := by group
    _ = (c : G)⁻¹ * (y * x) * c := by rw [h1]
    _ = (c : G)⁻¹ * y * c * ((c : G)⁻¹ * x * c) := by group

end Sylow

section Bound

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {m f : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}

omit [Finite F] in
theorem natCast_ne_zero_of_charTwo (hp : p.Prime) (hp2 : p ≠ 2) : (p : F) ≠ 0 := by
  intro h0
  have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h0
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm

omit [Finite G] in
theorem card_bstar_le
    (hS : GGSixFusionSetting p Bs G₀ (SpecialLinear.rootDatum m F) .PSL (m + 1) f ψ)
    (hpF : ¬ p ∣ Nat.card F - 1) : Nat.card Bs ≤ p ^ ((m + 1) / ordQ F p) := by
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hm : 2 ≤ m := hrank
  have hp := hS.prime
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hpK : (p : F) ≠ 0 := natCast_ne_zero_of_charTwo hp hS.ne_two
  have hN : ∀ b : Bs, ∃ N : GL (Fin (m + 1)) F, N ^ p = 1 ∧
      ∀ u, (b : G)⁻¹ * ψ u * b = ψ (InnerDiagA.conjSL N u) := by
    intro b
    obtain ⟨A, hA⟩ := RootPlaneA.exists_gl_of_psiInnerDiag hm hker (hS.innerDiag b b.2)
    exact OrdPRest.exists_pow_eq_one hker hA (hS.elem.2 b b.2) fun c _ => exists_pow_eq hp hpF c
  choose N hNp hNact using hN
  have hNinj : Function.Injective N := by
    intro b c hbc
    have hmem : (c : G) * (b : G)⁻¹ ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      have h1 : (c : G)⁻¹ * ψ u * c = (b : G)⁻¹ * ψ u * b := by rw [hNact, hNact, hbc]
      calc ψ u * ((c : G) * (b : G)⁻¹) = (c : G) * ((c : G)⁻¹ * ψ u * c) * (b : G)⁻¹ := by group
        _ = (c : G) * ((b : G)⁻¹ * ψ u * b) * (b : G)⁻¹ := by rw [h1]
        _ = (c : G) * (b : G)⁻¹ * ψ u := by group
    rw [hCψ, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact Subtype.ext hmem.symm
  have hact : ∀ (x y : Bs) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F),
      ((x : G) * y)⁻¹ * ψ u * ((x : G) * y) = ψ (InnerDiagA.conjSL (N y * N x) u) := by
    intro x y u
    rw [RootPlaneA.conjSL_mul, ← hNact y, ← hNact x]
    group
  have hNcomm : ∀ b c : Bs, N b * N c = N c * N b := by
    intro b c
    have hbc : (b : G) * c = c * b := TableB.IsElemAbelian.comm hS.elem b.2 c.2
    have h2 : conjAut (m + 1) F (N c * N b) = conjAut (m + 1) F (N b * N c) :=
      RootPlaneA.conjAut_eq_of_psi_eq hker fun u => by rw [← hact b c u, ← hact c b u, hbc]
    have h3 : conjAut (m + 1) F ((N b * N c)⁻¹ * (N c * N b)) = 1 := by
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    have h4 := AutPSL.mem_center_of_conjAut_eq_one (by omega) h3
    rw [GeneralLinearGroup.center_eq_range_scalar] at h4
    obtain ⟨l, hl⟩ := h4
    have hcb : N c * N b = N b * N c * GeneralLinearGroup.scalar (Fin (m + 1)) l := by
      rw [hl, mul_inv_cancel_left]
    have h5 : (N b)⁻¹ * N c * N b = N c * GeneralLinearGroup.scalar (Fin (m + 1)) l := by
      rw [mul_assoc, hcb, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
    have h6 : GeneralLinearGroup.scalar (Fin (m + 1)) (l ^ p) = 1 := by
      have h7 : ((N b)⁻¹ * N c * N b) ^ p =
          (N c * GeneralLinearGroup.scalar (Fin (m + 1)) l) ^ p := by rw [h5]
      have hconjp : ((N b)⁻¹ * N c * N b) ^ p = (N b)⁻¹ * N c ^ p * N b := by
        have := _root_.conj_pow (a := (N b)⁻¹) (b := N c) (i := p)
        rwa [inv_inv] at this
      rw [hconjp, hNp, mul_one, inv_mul_cancel,
        (TypeA.PGLTor.commute_scalar l (N c)).symm.mul_pow, hNp, one_mul, ← map_pow] at h7
      exact h7.symm
    have hl1 : l = 1 := by
      have h8 : l ^ p = 1 := TypeA.PGLTor.scalar_injective (by rw [h6, map_one])
      exact Units.ext (eq_one_of_pow_eq_one hp hpF (by rw [← Units.val_pow_eq_pow_val, h8,
        Units.val_one]))
    rw [hcb, hl1, map_one, mul_one]
  have h := card_le_pow_ordQ_matrix (K := F) (n := m + 1) hp hpK
    (Set.range fun b : Bs => ((N b : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (by
      rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
      change ((N b : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (N c : GL _ F) =
        (N c : GL (Fin (m + 1)) F) * (N b : GL (Fin (m + 1)) F)
      rw [← Units.val_mul, ← Units.val_mul, hNcomm])
    (by
      rintro _ ⟨b, rfl⟩
      rw [← Units.val_pow_eq_pow_val, hNp, Units.val_one])
  have hinj : Function.Injective fun b : Bs =>
      ((N b : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
    Units.val_injective.comp hNinj
  rwa [Nat.card_range_of_injective hinj] at h

end Bound

end OrdPNS

end CFSG.StandardType
