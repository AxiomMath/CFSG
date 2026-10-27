module

public import CFSG.RankThree.PartOne.N143X.RankHelpers
public import CFSG.RankThree.PartOne.KEXC.ReeModel
public import CFSG.RankThree.PartOne.KEXC.Torsion
public import CFSG.RankThree.PartOne.KLR.SectorOrder
public import CFSG.RankThree.PartOne.KF.F4Sylow
public import CFSG.RankThree.PartOne.KE.CTCasesF4
public import CFSG.RankThree.PartOne.KE.CTMain
public import CFSG.RankThree.Chevalley.SteinbergCFF4CyclotomicSix
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicFourTorus
public import CFSG.RankThree.PartOne.KEXC.TorusParam
public import CFSG.RankThree.PartOne.KF.G2Torus

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.LargeReeOrder

namespace CFSG.RankThree.PartOne.N143X

section Split

variable {p a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem card_le_sq_of_reeSplit
    (h : F4Param p a K) (E : Subgroup ↥(ReeTag.F4.reeGamma K a)) (hE : ∀ x ∈ E, x ^ p = 1) :
    Nat.card E ≤ p ^ 2 := by
  classical
  have : NeZero p := ⟨h.prime.ne_zero⟩
  obtain ⟨g, hg⟩ := exists_conj_into_Tp4 h E hE
  have hex : ∀ x : E, ∃ b, tp4M h b = g * (x : ↥(ReeTag.F4.reeGamma K a)) * g⁻¹ :=
    fun x => MonoidHom.mem_range.1 (hg x x.2)
  choose φ hφ using hex
  have hφinj : Function.Injective φ := fun x y hxy => by
    have h1 : g * (x : ↥(ReeTag.F4.reeGamma K a)) * g⁻¹ =
        g * (y : ↥(ReeTag.F4.reeGamma K a)) * g⁻¹ := by rw [← hφ x, ← hφ y, hxy]
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hR : Nat.card (rootsOfUnity p K) ≤ p := card_rootsOfUnity K p
  calc Nat.card E ≤ Nat.card (Fin 2 → rootsOfUnity p K) := Nat.card_le_card_of_injective φ hφinj
    _ = Nat.card (rootsOfUnity p K) ^ 2 := by rw [Nat.card_fun]; simp
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hR 2

end Split

section Sector

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]
  (D : ReeFrameData K L a)

theorem card_le_sq_of_sector {w : WeylGroup ReeTag.F4.tag} {m : ℕ} (hmodd : Odd m)
    {U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ} (hP : ParamData a L D.F w m U) {p : ℕ}
    (hp : p.Prime) (hSyl : p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ m ^ 2)
    {E : Subgroup (ReeTag.F4.reeGamma K a)} (hE : ∀ x ∈ E, x ^ p = 1) :
    Nat.card E ≤ p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Φ, hΦinj, hΦ, -, hΦF⟩ := hP.param
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  have hnadj : n ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w
  obtain ⟨h, hh⟩ := D.lang ⟨n, hnadj⟩
  have hFh : D.F h = h * ⟨n, hnadj⟩ := by
    rw [hh]
    group
  set g₀ : ModGL ReeTag.F4.tag L := (h : ModGL ReeTag.F4.tag L) with hg₀
  have hg₀adj : g₀ ∈ adjointGroup ReeTag.F4.tag L := h.2
  have hFg₀ : Fext D.F g₀ = g₀ * n := by
    rw [Fext_of_mem D.F hg₀adj]
    have : (⟨g₀, hg₀adj⟩ : adjointGroup ReeTag.F4.tag L) = h := rfl
    rw [this, hFh]
    rfl
  have hΦrange : Φ.range ≤ twistedFixed D.F n := by
    rintro _ ⟨z, rfl⟩
    exact hΦF z
  obtain ⟨T, hTmem, -, hTcard⟩ := exists_twisted_embedding D hg₀adj hFg₀ Φ.range hΦrange
  have hTdvd : p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ Nat.card T := by
    rw [hTcard, card_range_of_odd hmodd Φ hΦinj]
    exact hSyl
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨c, hc⟩ := exists_conj_le_of_card_dvd T hTdvd (isPGroup_of_pow_eq_one hE)
  let ψ : ReeTag.F4.reeGamma K a →* ModGL ReeTag.F4.tag L :=
    ((MulAut.conj g₀⁻¹).toMonoidHom.comp (thetaGamma L a)).comp (MulAut.conj c).toMonoidHom
  have hψ : ∀ x, ψ x = g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ := fun x => by
    simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := by
    intro d₁ d₂ h12
    rw [hψ, hψ] at h12
    have h1 := mul_left_cancel (mul_right_cancel h12)
    exact mul_left_cancel (mul_right_cancel (thetaGamma_injective L h1))
  have hψΦ : ∀ x ∈ E, ψ x ∈ Φ.range := fun x hx => by
    rw [hψ]
    exact (hTmem _).1 (hc x hx)
  have hex : ∀ x : E, ∃ z, Φ z = ψ x := fun x => hψΦ x x.2
  choose z hz using hex
  let φ : E → (Fin 2 → Lˣ) := fun x => ![((z x).1 : Lˣ), ((z x).2 : Lˣ)]
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : (z x).1 = (z y).1 := Subtype.ext (congrFun hxy 0)
    have h2 : (z x).2 = (z y).2 := Subtype.ext (congrFun hxy 1)
    have hzz : z x = z y := Prod.ext h1 h2
    exact Subtype.ext (hψinj ((hz x).symm.trans ((congrArg Φ hzz).trans (hz y))))
  refine card_le_sq_of_injective_fun hp.pos φ hφ fun x k => ?_
  have h1 : Φ (z x ^ p) = 1 := by
    rw [map_pow, hz x, ← map_pow, hE x x.2, map_one]
  have h2 : z x ^ p = 1 := hΦinj (h1.trans (map_one Φ).symm)
  fin_cases k
  · exact congrArg (fun y => (y.1 : Lˣ)) h2
  · exact congrArg (fun y => (y.2 : Lˣ)) h2

end Sector

section Ambient

theorem card_le_sq_of_F4_phiSix
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1) {E : Subgroup ↥(adjointGroup .F4 K)}
    (hE : ∀ x ∈ E, x ^ p = 1) : Nat.card E ≤ p ^ 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  obtain ⟨-, -, -, ⟨g, hg, hgn⟩, hmain⟩ := F4_cyclotomic_six_torus_and_surviving_A2_kernels K
    (AlgebraicClosure K) F hF _ rfl
  set Γ := conjEntrywiseImage K g⁻¹ with hΓ
  set T₀ := torusGroup .F4 (AlgebraicClosure K) ⊓ Γ with hT₀
  set T := T₀.map (MulAut.conj g).toMonoidHom with hT
  obtain ⟨-, ⟨eT⟩, -, -, hp', -⟩ := hmain g hg hgn Γ T₀ T rfl rfl rfl
  obtain ⟨-, hconj, -⟩ := hp' p hp hp3 hpd
  obtain ⟨c, hc⟩ := hconj E (isPGroup_of_pow_eq_one hE)
  let ι : ↥(adjointGroup .F4 K) →* ModGL .F4 (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup .F4 K).subtype
  let φ : ↥(adjointGroup .F4 K) →* ModGL .F4 (AlgebraicClosure K) :=
    ι.comp (MulAut.conj c).toMonoidHom
  have hφ : Function.Injective φ :=
    (((baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp
      Subtype.val_injective)).comp (MulAut.conj c).injective
  have hEt : ∀ x ∈ E, φ x ∈ T := fun x hx => hc ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact card_le_sq_of_map_into_prod φ hφ T
    ((Subgroup.equivMapOfInjective T₀ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans eT) hp.pos hE hEt

theorem card_le_sq_of_F4_phiFour
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 + 1) {E : Subgroup ↥(adjointGroup .F4 K)}
    (hE : ∀ x ∈ E, x ^ p = 1) : Nat.card E ≤ p ^ 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  obtain ⟨⟨g, hg, hgn⟩, hmain⟩ := F4_cyclotomic_four_torus_and_regular_prime_centralizers K
    (AlgebraicClosure K) F hF _ rfl
  set Γ := conjEntrywiseImage K g⁻¹ with hΓ
  set T₀ := torusGroup .F4 (AlgebraicClosure K) ⊓ Γ with hT₀
  set T := T₀.map (MulAut.conj g).toMonoidHom with hT
  obtain ⟨-, ⟨eT⟩, -, hp', -⟩ := hmain g hg hgn Γ T₀ T rfl rfl rfl
  obtain ⟨-, hconj, -⟩ := hp' p hp hp3 hpd
  obtain ⟨c, hc⟩ := hconj E (isPGroup_of_pow_eq_one hE)
  let ι : ↥(adjointGroup .F4 K) →* ModGL .F4 (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup .F4 K).subtype
  let φ : ↥(adjointGroup .F4 K) →* ModGL .F4 (AlgebraicClosure K) :=
    ι.comp (MulAut.conj c).toMonoidHom
  have hφ : Function.Injective φ :=
    (((baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp
      Subtype.val_injective)).comp (MulAut.conj c).injective
  have hEt : ∀ x ∈ E, φ x ∈ T := fun x hx => hc ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact card_le_sq_of_map_into_prod φ hφ T
    ((Subgroup.equivMapOfInjective T₀ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans eT) hp.pos hE hEt

theorem false_of_pow_three_F4_twelve
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 4 - Nat.card K ^ 2 + 1) {E : Subgroup ↥(adjointGroup .F4 K)}
    (hE : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 3) : False := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have h24 : Nat.card K ^ 2 ≤ Nat.card K ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hphi : (exhaustionPhi 12).eval (Nat.card K : ℤ) =
      ((Nat.card K ^ 4 - Nat.card K ^ 2 + 1 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_sub h24]
    push_cast
    simp [exhaustionPhi]
  have hpf : (p : ℤ) ∣ (exhaustionPhi 12).eval (Nat.card K : ℤ) := by
    rw [hphi]
    exact_mod_cast hpd
  obtain ⟨T, -, -, -, -, hcyc, -, -⟩ :=
    (F4_twelve_cyclic_sylow cyclic_torus_prime_centralizers_F4 K hp hp3 hpf).2.2
  have : IsCyclic E := hcyc E (isPGroup_of_pow_eq_one hE)
  exact false_of_pow_three_of_isCyclic hp hE hcard

end Ambient

theorem odd_mPhi2' (a : ℕ) : Odd (mPhi2 a) := by
  unfold mPhi2
  exact Even.add_one (Nat.even_pow.2 ⟨even_two, by omega⟩)

theorem false_of_pow_three_ree
    {X : Type} [Group X] [Finite X] {f : ℕ} (hX : ReeTitsModel X .twistedF4 2 f)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) {E : Subgroup X} (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) : False := by
  classical
  have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_gamma_of_model hX
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  set E' : Subgroup ↥(ReeTag.F4.reeGamma K a) := E.map e.toMonoidHom with hE'def
  have hE' : ∀ x ∈ E', x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change (e y) ^ p = 1
    rw [← map_pow, hE y hy, map_one]
  have hcard' : Nat.card E' = p ^ 3 := by
    rw [hE'def, Subgroup.card_map_of_injective e.injective, hcard]
  have hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a) := by
    have : p ∣ Nat.card E' := by rw [hcard']; exact dvd_pow_self p (by norm_num)
    exact this.trans (Subgroup.card_subgroup_dvd_card E')
  have hle : ReeTag.F4.reeGamma K a ≤ adjointGroup .F4 K := Subgroup.map_subtype_le _
  let i : ↥(ReeTag.F4.reeGamma K a) →* ↥(adjointGroup .F4 K) := Subgroup.inclusion hle
  have hi : Function.Injective i := fun x y h => by
    have h' : (i x : ModGL .F4 K) = (i y : ModGL .F4 K) := congrArg Subtype.val h
    exact Subtype.ext h'
  set E₀ : Subgroup ↥(adjointGroup .F4 K) := E'.map i with hE₀def
  have hE₀ : ∀ x ∈ E₀, x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change (i y) ^ p = 1
    rw [← map_pow, hE' y hy, map_one]
  have hcard₀ : Nat.card E₀ = p ^ 3 := by
    rw [hE₀def, Subgroup.card_map_of_injective hi, hcard']
  rcases (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK').2 p hp (by omega)
    hdvd with h1 | h2 | h3 | h4 | h5
  ·
    have hD : F4Param p a K := ⟨hp, by omega, hK', h1⟩
    have := card_le_sq_of_reeSplit hD E' hE'
    omega
  ·
    obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK'
    have : CharP (AlgebraicClosure K) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
    have := card_le_sq_of_sector D (odd_mPhi2' a) (torusParam_phi2 D.isFrob) hp
      (pow_factorization_card_reeGamma_dvd_phi2 hK' hp (by omega) h2) hE'
    omega
  ·
    have := card_le_sq_of_F4_phiFour K hp (by omega) (by rw [hK']; exact h3) hE₀
    omega
  ·
    have := card_le_sq_of_F4_phiSix K hp (by omega) (by rw [hK']; exact h4) hE₀
    omega
  ·
    exact false_of_pow_three_F4_twelve K hp (by omega) (by rw [hK']; exact h5) hE₀ hcard₀

end CFSG.RankThree.PartOne.N143X
