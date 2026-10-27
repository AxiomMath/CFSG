module

public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiIdent
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.KFacts.K72L3Omega
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open Matrix

section Field

variable {K : Type} [Field K]

theorem frobGL_cycThree (σ : K ≃+* K) : frobGL σ (cycThree : GL (Fin 3) K) = cycThree :=
  CFSG.RankThree.PartTwo.Sec12.KS128Move.frobGL_cycThree σ

theorem frobGL_torusHom (σ : K ≃+* K) (a b : Kˣ) :
    frobGL σ (torusHom (a, b)) = torusHom (Units.map (σ : K →* K) a, Units.map (σ : K →* K) b) := by
  apply Units.ext
  rw [coe_frobGL, coe_torusHom, coe_torusHom, diagonal_map (map_zero σ)]
  congr 1
  funext i
  fin_cases i <;> simp

theorem frobGL_eq_of_mem_cycTorus {σ : K ≃+* K} {μ : Kˣ} (hσμ : σ (μ : K) = μ) {g : GL (Fin 3) K}
    (hg : g ∈ (Subgroup.zpowers (cycThree : GL (Fin 3) K) ⊔ torusPow μ : Subgroup _)) :
    frobGL σ g = g := by
  have hμ : Units.map (σ : K →* K) μ = μ := Units.ext (by rw [Units.coe_map]; exact hσμ)
  have hle : Subgroup.zpowers μ ≤ (Units.map (σ : K →* K)).eqLocus (MonoidHom.id Kˣ) :=
    Subgroup.zpowers_le.mpr hμ
  have hP : (Subgroup.zpowers (cycThree : GL (Fin 3) K) ⊔ torusPow μ : Subgroup _) ≤
      (frobGL σ).eqLocus (MonoidHom.id _) := by
    refine sup_le (Subgroup.zpowers_le.mpr (frobGL_cycThree σ)) ?_
    rintro _ ⟨⟨a, b⟩, hab, rfl⟩
    obtain ⟨ha, hb⟩ := Subgroup.mem_prod.mp hab
    change frobGL σ (torusHom (a, b)) = torusHom (a, b)
    rw [frobGL_torusHom]
    congr 2
    · exact hle ha
    · exact hle hb
  exact hP hg

theorem pow_apply_eq_of_apply_eq {X : Type*} [Group X] {α : MulAut X} {x : X} (h : α x = x)
    (k : ℕ) : (α ^ k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, MulAut.mul_apply, h, ih]

end Field

theorem mem_zpowers_of_fixed_slPi {X : Type} [Group X] [Finite X] {π : Bool} {p f : ℕ}
    {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (e : X ≃* slPi π 3 (p ^ f) K) {α : MulAut X} {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {H : GL (Fin 3) K} (hH : H ∈ glPi π 3 (p ^ f) K)
    (hα : ∀ s : slPi π 3 (p ^ f) K, ((MulAut.congr e α s : slPi π 3 (p ^ f) K) :
      GL (Fin 3) K) = H * frobGL σ (H⁻¹ * s * H) * H⁻¹)
    {C : Subgroup X} (hC : ∀ y, y ∈ C ↔ α y = y) {T : Subgroup X}
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 T C) {ζ : MulAut X} (hζ : ζ ^ 3 = 1)
    (hfix : ∀ t ∈ T, ζ t = t) : ζ ∈ Subgroup.zpowers α := by
  have := hK.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨ω, hω3, hω1⟩ := exists_tau hK hq
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    apply hω1
    have h := hω3
    rw [pow_succ, h2, one_mul] at h
    exact h
  have hσω : σ ω = ω := by
    have hinv : ω⁻¹ = ω ^ 2 :=
      (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hω3)).symm
    have hsum : ω + ω⁻¹ = -1 := by
      rw [hinv]
      linear_combination one_add_tau_add_sq hω3 hω1
    exact ringAut_fixed_of_add_inv (ringAut_apply_three hσ) hω0 hω2
      (by rw [hsum, map_neg, map_one])
  set ωu : Kˣ := Units.mk0 ω hω0 with hωu
  have hωuK : (ωu : K) = ω := rfl
  have hωu3 : ωu ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hωuK, hω3, Units.val_one])
  have hωu1 : ωu ≠ 1 := fun h => hω1 (by rw [← hωuK, h, Units.val_one])
  have hωu2 : ωu ^ 2 ≠ 1 := fun h => hω2 (by
    rw [← hωuK, ← Units.val_pow_eq_pow_val, h, Units.val_one])
  have hωT : ωu ∈ rootsOfUnity (qSubPi π (p ^ f)) K := mem_rootsOfUnity_qSubPi_of_pow_three hq hωu3
  have hP₀M := cycTorus_le_slPi hK hωT
  set α' := MulAut.congr e α with hα'
  set P : Subgroup (GL (Fin 3) K) :=
    (Subgroup.zpowers (cycThree : GL (Fin 3) K) ⊔ torusPow ωu : Subgroup _).map
      (MulAut.conj H).toMonoidHom with hPdef
  have hPp : IsPGroup 3 P := (isPGroup_cycTorus (k := 1) (by rw [pow_one]; exact hωu3)).map _
  have hPM : P ≤ slPi π 3 (p ^ f) K := by
    rintro _ ⟨g, hg, rfl⟩
    exact conj_mem_slPi hπ hH (hP₀M hg)
  have hα'fix : ∀ m : slPi π 3 (p ^ f) K, (m : GL (Fin 3) K) ∈ P → α' m = m := by
    rintro m ⟨g, hg, hgm⟩
    apply Subtype.ext
    rw [hα m, ← hgm]
    change H * frobGL σ (H⁻¹ * (H * g * H⁻¹) * H) * H⁻¹ = H * g * H⁻¹
    rw [show H⁻¹ * (H * g * H⁻¹) * H = g by group, frobGL_eq_of_mem_cycTorus hσω hg]
  have hα'e : ∀ y : X, α' (e y) = e (α y) := fun y => by
    rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  set PX : Subgroup X := (P.subgroupOf (slPi π 3 (p ^ f) K)).map e.symm.toMonoidHom with hPXdef
  have hPXp : IsPGroup 3 PX := (hPp.comap_of_injective _ Subtype.val_injective).map _
  have hPXC : PX ≤ C := by
    rintro _ ⟨m, hm, rfl⟩
    rw [hC]
    apply e.injective
    change e (α (e.symm m)) = e (e.symm m)
    rw [← hα'e, MulEquiv.apply_symm_apply]
    exact hα'fix m hm
  have hPC : IsPGroup 3 (PX.subgroupOf C) := hPXp.comap_of_injective _ Subtype.val_injective
  obtain ⟨Q, hQ⟩ := hT
  obtain ⟨x, hx⟩ := exists_conj_mem_sylow Q hPC
  have hfixX : ∀ m : slPi π 3 (p ^ f) K, (m : GL (Fin 3) K) ∈ P →
      ζ ((x : X) * e.symm m * (x : X)⁻¹) = (x : X) * e.symm m * (x : X)⁻¹ := by
    intro m hm
    have hmX : e.symm m ∈ PX := ⟨m, hm, rfl⟩
    have h1 := hx ⟨e.symm m, hPXC hmX⟩ hmX
    have h2 : (x : X) * e.symm m * (x : X)⁻¹ ∈ T := by
      rw [← hQ]
      exact ⟨_, h1, rfl⟩
    exact hfix _ h2
  set c : slPi π 3 (p ^ f) K := e (x : X) with hcdef
  have hαc : α' c = c := by
    rw [hcdef, hα'e, (hC _).mp x.2]
  set ζ' := MulAut.congr e ζ with hζ'
  have hζ'fix : ∀ m : slPi π 3 (p ^ f) K, (m : GL (Fin 3) K) ∈ P →
      ζ' (c * m * c⁻¹) = c * m * c⁻¹ := by
    intro m hm
    have h2 : c * m * c⁻¹ = e ((x : X) * e.symm m * (x : X)⁻¹) := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [h2, hζ', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hfixX m hm]
  have hα'fix' : ∀ m : slPi π 3 (p ^ f) K, (m : GL (Fin 3) K) ∈ P →
      α' (c * m * c⁻¹) = c * m * c⁻¹ := by
    intro m hm
    rw [map_mul, map_mul, map_inv, hαc, hα'fix m hm]
  set s₁ : slPi π 3 (p ^ f) K := ⟨H * torusHom (ωu, ωu⁻¹) * H⁻¹,
    hPM ⟨_, torusHom_inv_mem_cycTorus ωu, rfl⟩⟩ with hs₁def
  set s₂ : slPi π 3 (p ^ f) K := ⟨H * cycThree * H⁻¹, hPM ⟨_, cycThree_mem_cycTorus ωu, rfl⟩⟩
    with hs₂def
  have hs₁P : (s₁ : GL (Fin 3) K) ∈ P := ⟨_, torusHom_inv_mem_cycTorus ωu, rfl⟩
  have hs₂P : (s₂ : GL (Fin 3) K) ∈ P := ⟨_, cycThree_mem_cycTorus ωu, rfl⟩
  have hζ'3 : ζ' ^ 3 = 1 := by rw [hζ', ← map_pow, hζ, map_one]
  obtain ⟨τ, hτ, g, hg⟩ := exists_semiAct_of_pow_three_eq_one hK hq2 hζ'3
  obtain ⟨i, hi⟩ : ∃ i : ℕ, τ * σ ^ i = 1 := by
    rcases hτ with rfl | hτ3
    · exact ⟨0, by rw [pow_zero, mul_one]⟩
    · obtain ⟨i, hi⟩ := exists_pow_mul_eq_one_of_orderOf_eq_three hσ hτ3
      exact ⟨i, by rw [eq_inv_of_mul_eq_one_right hi, inv_mul_cancel]⟩
  obtain ⟨gi, hgi⟩ := (semiAct_of_conj_frob hα).pow i
  have hprod := hg.mul hgi
  rw [hi] at hprod
  have hone : ζ' * α' ^ i = 1 := eq_one_of_semiAct_one_of_fixed hprod hωu1 hωu2
    ((c : GL (Fin 3) K) * H) (s₁ := c * s₁ * c⁻¹) (s₂ := c * s₂ * c⁻¹)
    (by
      change (c : GL (Fin 3) K) * (H * torusHom (ωu, ωu⁻¹) * H⁻¹) * (c : GL (Fin 3) K)⁻¹ = _
      group)
    (by
      change (c : GL (Fin 3) K) * (H * cycThree * H⁻¹) * (c : GL (Fin 3) K)⁻¹ = _
      group)
    (by rw [MulAut.mul_apply, pow_apply_eq_of_apply_eq (hα'fix' s₁ hs₁P) i, hζ'fix s₁ hs₁P])
    (by rw [MulAut.mul_apply, pow_apply_eq_of_apply_eq (hα'fix' s₂ hs₂P) i, hζ'fix s₂ hs₂P])
  have hζeq : ζ = (α ^ i)⁻¹ := (MulAut.congr e).injective (by
    rw [map_inv, map_pow]
    exact eq_inv_of_mul_eq_one_left hone)
  rw [hζeq]
  exact inv_mem (pow_mem (Subgroup.mem_zpowers α) i)

theorem mem_zpowers_of_forall_sylow_barCentralizer_fixed {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hL : Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n))) {a : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    (ha : InducesStdKind L a .field ∨ InducesStdKind L a .graphField)
    {T : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 T (Sec8.barCentralizer (Subgroup.zpowers a) L))
    {ζ : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hζ : ζ ^ 3 = 1)
    (hfix : ∀ t ∈ T, ζ t = t) :
    ζ ∈ Subgroup.zpowers (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩)) := by
  have hn3 : 3 ≤ 3 * n := by omega
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  set α := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩) with hαdef
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact ha3)
    rw [hαdef, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hC : ∀ y, y ∈ Sec8.barCentralizer (Subgroup.zpowers a) L ↔ α y = y :=
    fun y => mem_barCentralizer_zpowers_iff haN y
  have hind : ∀ {M : Type} [Group M] (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* M)
      (hx : a ∈ Subgroup.normalizer (L : Set G)), inducedAutHom L e₁ ⟨a, hx⟩ =
        MulAut.congr e₁ α := fun e₁ hx => inducedAutHom_apply L e₁ _
  rcases hL with ⟨K₀, _, _, ⟨hK₀, hq₀, ⟨e₀⟩⟩ | ⟨hK₀, hq₀, ⟨e₀⟩⟩⟩
  ·
    have hIso : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (3 * n) ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K) :=
      ⟨K₀, inferInstance, inferInstance, hK₀, ⟨e₀⟩⟩
    have haF : InducesStdKind L a .field :=
      ha.resolve_right (not_inducesStdKind_graphField_of_isoSLThree hn3 hq₀ hIso ha3)
    obtain ⟨K, _, _, hK, e₁, hxN, hk⟩ := inducesKindSL_of_inducesStdKind hn3 hq₀ hIso haF
    have hD := (stdPinnedPSL_separated (n := 3) (K := K) le_rfl).not_mem_inndiag_of_hasKind hk
      (by decide) (by decide)
    set ψ := slPiTrueEquiv (2 ^ (3 * n)) K with hψ
    set e := e₁.trans ψ.symm with he
    have heψ : e.trans ψ = e₁ := by
      ext y
      simp [he]
    have hα' : MulAut.congr ψ (MulAut.congr e α) = inducedAutHom L e₁ ⟨a, hxN⟩ := by
      rw [← congr_trans, heψ, hind]
    have hα'3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
    obtain ⟨σ, hσ, H, hH⟩ := exists_field_of_descendAut_not_mem hα'3 (by rw [hα']; exact hD)
    have hPi : PiField true 2 (3 * n) K := ⟨Nat.prime_two, by omega, hK⟩
    exact mem_zpowers_of_fixed_slPi hPi hq₀ hq2 e hσ (mem_glPi_true _ H) hH hC hT hζ hfix
  ·
    have hIso : Sec8.IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) :=
      ⟨K₀, inferInstance, inferInstance, hK₀, ⟨e₀⟩⟩
    have hm3 : 3 ∣ 2 ^ (3 * n) + 1 := by
      generalize 2 ^ (3 * n) = t at hq₀ ⊢
      omega
    have haF : InducesStdKind L a .field :=
      ha.resolve_right (not_inducesStdKind_graphField_of_isoSUThree hn3 hm3 hIso)
    obtain ⟨K, _, h, hq, e₁, hxN, hk⟩ := inducesKindSU3_of_inducesStdKind hn3 hm3 hIso haF
    have hD := (stdPinnedPSU3_separated h).not_mem_inndiag_of_hasKind hk (by decide) (by decide)
    set ψ := slPiFalseEquiv 2 (3 * n) K with hψ
    set e := e₁.trans ψ.symm with he
    have heψ : e.trans ψ = e₁ := by
      ext y
      simp [he]
    have hα' : MulAut.congr ψ (MulAut.congr e α) = inducedAutHom L e₁ ⟨a, hxN⟩ := by
      rw [← congr_trans, heψ, hind]
    have hα'3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
    obtain ⟨σ, hσ, H, hHmem, hH⟩ := exists_field_of_psuConj_not_mem h hq hα'3
      (by rw [hα']; exact hD)
    have hPi : PiField false 2 (3 * n) K :=
      ⟨Nat.prime_two, by omega, by rw [h.card]; change _ = (2 ^ (3 * n)) ^ 2; ring⟩
    exact mem_zpowers_of_fixed_slPi hPi hq₀ hq2 e hσ hHmem hH hC hT hζ hfix

end CFSG.RankThree.PartTwo.KFacts
