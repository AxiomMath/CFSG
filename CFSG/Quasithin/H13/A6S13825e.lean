module

public import CFSG.Quasithin.H13.A6S13825y
public import CFSG.Quasithin.H13.A6S13825c
public import CFSG.Quasithin.H13.A6S13822c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification
open scoped IsMulCommutative

namespace L4Ind

theorem mem_flag_iff (g : SL4) : g ∈ flagStabilizer 4 (ZMod 2) {2} ↔ InQ2 (g : M4) := by
  rw [mem_flagStabilizer]
  have hfs : ∀ v : V4, v ∈ flagSpace 4 (ZMod 2) 2 ↔ InL0 v := by
    intro v
    rw [mem_flagSpace]
    constructor
    · intro h
      exact ⟨h 2 (by norm_num), h 3 (by norm_num)⟩
    · rintro ⟨h2, h3⟩ j hj
      fin_cases j
      · exact absurd hj (by norm_num)
      · exact absurd hj (by norm_num)
      · exact h2
      · exact h3
  constructor
  · intro h
    have hW := h 2 (Set.mem_singleton 2)
    rw [mem_stabilizer] at hW
    rw [inQ2_iff]
    refine ⟨?_, ?_⟩
    · rw [← hfs, ← hW]
      exact Submodule.mem_map_of_mem ((hfs e0).2 (by decide))
    · rw [← hfs, ← hW]
      exact Submodule.mem_map_of_mem ((hfs e1).2 (by decide))
  · intro hg i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    rw [mem_stabilizer]
    have hle : ∀ v : V4, InL0 v → InL0 ((g : M4) *ᵥ v) := by
      intro v hv
      rcases inL0_cases v hv with rfl | rfl | rfl | rfl
      · rw [mulVec_zero]; decide
      · exact ((inQ2_iff _).1 hg).1
      · exact ((inQ2_iff _).1 hg).2
      · rw [mulVec_add]
        obtain ⟨⟨a, b⟩, c, d⟩ := (inQ2_iff _).1 hg
        exact ⟨by rw [Pi.add_apply, a, c, add_zero], by rw [Pi.add_apply, b, d, add_zero]⟩
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, hfs] at hv
      rw [Matrix.mulVecLin_apply, hfs]
      exact hle v hv
    · intro w hw
      rw [hfs] at hw
      let f : {v : V4 // InL0 v} → {v : V4 // InL0 v} := fun v => ⟨(g : M4) *ᵥ v, hle v v.2⟩
      have hinj : Function.Injective f := by
        intro v v' h
        apply Subtype.ext
        have h' := congrArg (fun x : {v : V4 // InL0 v} => ((g⁻¹ : SL4) : M4) *ᵥ (x : V4)) h
        simp only [f] at h'
        rwa [inv_mulVec_mulVec, inv_mulVec_mulVec] at h'
      obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨w, hw⟩
      refine ⟨v, (hfs v).2 v.2, ?_⟩
      exact congrArg Subtype.val hv

abbrev w0M : M4 := !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

@[expose] def w0 : SL4 := mkSL w0M w0M (by decide)

theorem w0_entry (m : M4) (i j : Fin 4) : (w0M * mᵀ * w0M) i j = m (Fin.rev j) (Fin.rev i) := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Fin.rev, Matrix.vecMul, dotProduct]

theorem inQ2_w0 (m : M4) : InQ2 (w0M * mᵀ * w0M) ↔ InQ2 m := by
  simp only [InQ2, w0_entry]
  constructor
  · rintro ⟨a, b, c, d⟩
    exact ⟨d, b, c, a⟩
  · rintro ⟨a, b, c, d⟩
    exact ⟨d, b, c, a⟩

theorem inQ2_inv {g : SL4} (hg : InQ2 (g : M4)) : InQ2 ((g⁻¹ : SL4) : M4) :=
  (mem_flag_iff _).1 (Subgroup.inv_mem _ ((mem_flag_iff g).2 hg))

@[expose] def mulVecEquiv (A : GL (Fin 4) (ZMod 2)) : V4 ≃+ V4 where
  toFun v := (A : M4) *ᵥ v
  invFun v := ((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4) *ᵥ v
  left_inv v := by
    simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  right_inv v := by
    simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  map_add' v v' := mulVec_add _ _ _

@[expose] def tauW : MulAut SL4 := MulAut.conj w0 * CatalogueBGraphForm.slGraphAut 4 (ZMod 2)

theorem tauW_matrix (g : SL4) : ((tauW g : SL4) : M4) = w0M * (((g⁻¹ : SL4) : M4))ᵀ * w0M := by
  rw [tauW, MulAut.mul_apply, MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, w0, coe_mkSL_inv]
  rfl

theorem inQ2_tauW (g : SL4) : InQ2 ((tauW g : SL4) : M4) ↔ InQ2 (g : M4) := by
  rw [tauW_matrix, inQ2_w0]
  exact ⟨fun h => by simpa using inQ2_inv h, inQ2_inv⟩

theorem w0_mul_self : w0M * w0M = 1 := by
  decide

theorem w0_transpose : w0Mᵀ = w0M := by
  decide

theorem tauW_tauW (g : SL4) : tauW (tauW g) = g := by
  apply Subtype.ext
  rw [tauW_matrix, ← map_inv, tauW_matrix, inv_inv, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, w0_transpose]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, w0_mul_self, Matrix.one_mul, Matrix.mul_assoc,
    w0_mul_self, Matrix.mul_one]

theorem tauW_mem_unitriangular {u : SL4} (hu : u ∈ unitriangular 4 (ZMod 2)) :
    tauW u ∈ unitriangular 4 (ZMod 2) := by
  have hu' := Subgroup.inv_mem _ hu
  rw [mem_unitriangular] at hu' ⊢
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [tauW_matrix, w0_entry]
    exact hu'.1 _ _ (Fin.rev_lt_rev.mpr hji)
  · rw [tauW_matrix, w0_entry]
    exact hu'.2 _

theorem nat_coords {M : Type} [CommGroup M] [Module (ZMod 2) (Additive M)]
    {X : Subgroup (MulAut M)} (e' : ↥X ≃* SL4) {κ : B42Ln.G4 ≃* B42Ln.G4}
    {β : Additive M ≃ₗ[ZMod 2] V4}
    (hβ : ∀ g w, β (B42Ln.repOf4 (B42Ln.phiOf4 (e'.trans B42Ln.E4)) g w) =
      B42Ln.natRep4 (κ g) (β w)) :
    ∃ (τ' : MulAut SL4) (βA : Additive M ≃+ V4),
      (∀ g : SL4, InQ2 ((τ' g : SL4) : M4) ↔ InQ2 (g : M4)) ∧
      (∀ u ∈ unitriangular 4 (ZMod 2), ∃ u' ∈ unitriangular 4 (ZMod 2), τ' u' = u) ∧
      ∀ (x : ↥X) (w : M), βA (Additive.ofMul ((x : MulAut M) w)) =
        ((τ' (e' x) : SL4) : M4) *ᵥ βA (Additive.ofMul w) := by
  have hphi : ∀ x : ↥X, B42Ln.phiOf4 (e'.trans B42Ln.E4) x = e' x := fun x => by
    simp [B42Ln.phiOf4]
  have hβ' : ∀ (x : ↥X) (w : M), β (Additive.ofMul ((x : MulAut M) w)) =
      ((κ (e' x) : SL4) : M4) *ᵥ β (Additive.ofMul w) := by
    intro x w
    have h1 := hβ (B42Ln.phiOf4 (e'.trans B42Ln.E4) x) (Additive.ofMul w)
    rw [B42Ln.repOf4_apply_iso, B42Ln.natRep4_apply, hphi] at h1
    exact h1
  rcases G11.P4GL.aut_SL_cases (by norm_num : 3 ≤ 4) κ with ⟨A, rfl⟩ | ⟨A, rfl⟩
  · refine ⟨1, β.toAddEquiv.trans (mulVecEquiv A⁻¹), fun g => Iff.rfl,
      fun u hu => ⟨u, hu, rfl⟩, fun x w => ?_⟩
    have hκ : ((CatalogueBHigherLinearAction.slConjugation 4 (ZMod 2) A (e' x) : SL4) : M4) =
        (A : M4) * ((e' x : SL4) : M4) * ((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4) := by
      have := congrArg Units.val
        (CatalogueBHigherLinearAction.toGL_slConjugation 4 (ZMod 2) A (e' x))
      rw [Units.val_mul, Units.val_mul] at this
      exact this
    show ((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4) *ᵥ β (Additive.ofMul ((x : MulAut M) w)) =
      ((e' x : SL4) : M4) *ᵥ (((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4) *ᵥ β (Additive.ofMul w))
    rw [hβ', hκ, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  · refine ⟨tauW, (β.toAddEquiv.trans (mulVecEquiv A⁻¹)).trans
      (mulVecEquiv (Matrix.SpecialLinearGroup.toGL w0)), inQ2_tauW,
      fun u hu => ⟨tauW u, tauW_mem_unitriangular hu, tauW_tauW u⟩, fun x w => ?_⟩
    have hκ : ((CatalogueBHigherLinearAction.slConjugation 4 (ZMod 2) A
        (CatalogueBGraphForm.slGraphAut 4 (ZMod 2) (e' x)) : SL4) : M4) =
        (A : M4) * ((((e' x)⁻¹ : SL4) : M4))ᵀ * ((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4) := by
      have := congrArg Units.val (CatalogueBHigherLinearAction.toGL_slConjugation 4 (ZMod 2) A
        (CatalogueBGraphForm.slGraphAut 4 (ZMod 2) (e' x)))
      rw [Units.val_mul, Units.val_mul] at this
      exact this
    show w0M *ᵥ (((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4) *ᵥ β (Additive.ofMul ((x : MulAut M) w))) =
      ((tauW (e' x) : SL4) : M4) *ᵥ (w0M *ᵥ (((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4) *ᵥ
        β (Additive.ofMul w)))
    rw [hβ', MulAut.mul_apply, hκ, tauW_matrix, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec,
      mulVec_mulVec]
    refine congrArg (· *ᵥ β (Additive.ofMul w)) ?_
    have hw : w0M * w0M = 1 := by decide
    rw [show w0M * (((e' x)⁻¹ : SL4) : M4)ᵀ * w0M * w0M * ((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4) =
      w0M * (((e' x)⁻¹ : SL4) : M4)ᵀ * (w0M * w0M) * ((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4) by
        simp only [Matrix.mul_assoc], hw, Matrix.mul_one]
    rw [show w0M * ((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4) * ((A : M4) *
      (((e' x)⁻¹ : SL4) : M4)ᵀ * ((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4)) =
      w0M * (((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4) * (A : M4)) *
        (((e' x)⁻¹ : SL4) : M4)ᵀ * ((A⁻¹ : GL (Fin 4) (ZMod 2)) : M4) by
          simp only [Matrix.mul_assoc],
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end L4Ind

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

open L4Ind in
open scoped commutatorElement in
open L13825 in
theorem top_coords (hA21 : AsA21SQTKSection) (h21 : Lem13821)
    (h16 : Lem13816) (h1334 : Stmt13_3_4) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : IsPSL 4 2 1 ↥(S.KSt H K)) (hhat : IsHatA6 L)
    (hTK : T ≤ K ⊔ pCoreOf 2 H)
    (hnt : ∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V))
    [IsMulCommutative ↥(conjClosure S.V3 H)] {W : Subgroup G} (hV₁W : fsuV1 T V ≤ W)
    (hWU : W < conjClosure S.V3 H) (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H) :
    ∃ (ρ : ↥H →* SL4) (β : ↥(conjClosure S.V3 H) →* Multiplicative V4),
      Function.Surjective ρ ∧ (∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) ∧
      (∀ h : ↥H, (h : G) ∈ S.L1 ⊔ T → InQ2 (ρ h : M4)) ∧
      (∀ q : SL4, InQ2 (q : M4) → ∃ h : ↥H, (h : G) ∈ S.L1 ⊔ T ∧ ρ h = q) ∧
      (∀ u ∈ unitriangular 4 (ZMod 2), ∃ h : ↥H, (h : G) ∈ T ∧ ρ h = u) ∧
      Function.Surjective β ∧ (∀ u, β u = 1 ↔ (u : G) ∈ W) ∧
      ∀ (h : ↥H) (u v : ↥(conjClosure S.V3 H)), (v : G) = h * u * h⁻¹ →
        Multiplicative.toAdd (β v) = (ρ h : M4) *ᵥ Multiplicative.toAdd (β u) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := conjClosure S.V3 H with hU
  have hF98 := hS.hF H hH
  have hF := hF98.toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have h21' := h21 G T L V S hS H hH K hK
  have hKT : K ⊔ T = H := h21'.2.2.1.1
  have hKnH : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure S.V3 H
  have hHUW : H ≤ Subgroup.normalizer ((U ⊓ W : Subgroup G) : Set G) := fun _ hh =>
    F7.mem_normalizer_inf (hHU hh) (hHW hh)
  have hWU' : W ≤ U := hWU.le
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := (L13825.isElemAbelian_UH hS hH).2
  have hW2 : ∀ w : Sec (⊤ : Subgroup ↥U) (W.subgroupOf U), w ^ 2 = 1 :=
    L13825.sec_sq_eq_one hU2
  set σ := A6Mod.secAct hHU hHUW with hσ
  set X := autSec (autOn H U) ⊤ (W.subgroupOf U) with hX
  have hσX : ∀ h : ↥H, σ h ∈ X := fun h => (A6Mod.mem_autSec_iff hHU hHUW le_rfl).2 ⟨h, h.2, rfl⟩
  obtain ⟨e₀⟩ := FLc.nonempty_equiv_SLt_of_isPSL hKn
  have hsl : IsSimpleGroup (SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) (by norm_num)
  have hsimp : IsSimpleGroup ↥(S.KSt H K) := e₀.isSimpleGroup
  have hKnt : ∃ k ∈ K, ∃ x ∈ U, k * x * k⁻¹ * x⁻¹ ∉ W := by
    by_contra hcon
    push Not at hcon
    apply hWU.not_ge
    have hc : ⁅U, K⁆ = U := h21'.2.2.2
    rw [← hc, Subgroup.commutator_le]
    intro x hx k hk
    have e : ⁅x, k⁆ = (k * x * k⁻¹ * x⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact W.inv_mem (hcon k hk x hx)
  have hfaith : ∀ h ∈ H, (∀ u ∈ U, h * u * h⁻¹ * u⁻¹ ∈ W) → h ∈ pCoreOf 2 H :=
    fun h hh htriv => S.mem_pCoreOf_of_trivial hS hH hKH hKnH hKT.symm hsimp le_rfl hV₁W hHU
      hHW hKnt hh htriv
  have hker : ∀ x : ↥H, σ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Mod.secAct_eq_one_iff]
    refine ⟨hfaith x x.2, fun hx u hu => ?_⟩
    rw [hF.pCoreOf_eq_centralizerMod] at hx
    exact hV₁W (hx.2.2 u hu)
  have hHKQ : ∀ h ∈ H, ∃ q ∈ pCoreOf 2 H, ∃ k ∈ K, h = q * k := by
    intro h hh
    have hle : K ⊔ T ≤ pCoreOf 2 H ⊔ K :=
      sup_le le_sup_right (hTK.trans (le_of_eq (sup_comm _ _)))
    have hh' : h ∈ K ⊔ T := by rw [hKT]; exact hh
    exact (F1.mem_sup_iff_exists_mul_of_normalizes
      (hKH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))).mp (hle hh')
  obtain ⟨ψ₀, hψ₀⟩ := exists_mapEquiv (S1549C.starHom hF) σ
    (fun x => by rw [S1549C.starHom_eq_one_iff hF, hker]) (K.subgroupOf H)
  have hKX : (K.subgroupOf H).map σ = X := by
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨h, -, rfl⟩ := hy
      exact hσX h
    · obtain ⟨h, -, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHUW le_rfl).1 hy
      obtain ⟨q, hq, k, hk, hqk⟩ := hHKQ h h.2
      refine ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
      have e : h = ⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 H hq⟩ * ⟨k, hKH hk⟩ :=
        Subtype.ext hqk
      rw [e, map_mul, (hker ⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 H hq⟩).2 hq, one_mul]
  have hKst : S.KSt H K = (K.subgroupOf H).map (S1549C.starHom hF) := S.kst_eq hF hKH
  set ψ : ↥(S.KSt H K) ≃* ↥X :=
    (MulEquiv.subgroupCongr hKst).trans (ψ₀.trans (MulEquiv.subgroupCongr hKX)) with hψ
  have hstarK : ∀ h : ↥H, S1549C.starHom hF h ∈ S.KSt H K := by
    intro h
    obtain ⟨q, hq, k, hk, hqk⟩ := hHKQ h h.2
    rw [hKst]
    refine ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
    have e : h = ⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 H hq⟩ * ⟨k, hKH hk⟩ :=
      Subtype.ext hqk
    rw [e, map_mul,
      (S1549C.starHom_eq_one_iff hF ⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 H hq⟩).2 hq, one_mul]
  have hψσ : ∀ h : ↥H, ψ ⟨S1549C.starHom hF h, hstarK h⟩ = ⟨σ h, hσX h⟩ := by
    intro h
    obtain ⟨q, hq, k, hk, hqk⟩ := hHKQ h h.2
    have e : h = ⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 H hq⟩ * ⟨k, hKH hk⟩ :=
      Subtype.ext hqk
    have h1 : S1549C.starHom hF h = S1549C.starHom hF ⟨k, hKH hk⟩ := by
      rw [e, map_mul,
        (S1549C.starHom_eq_one_iff hF ⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 H hq⟩).2 hq,
        one_mul]
    have h2 : σ h = σ ⟨k, hKH hk⟩ := by
      rw [e, map_mul, (hker ⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 H hq⟩).2 hq, one_mul]
    apply Subtype.ext
    have h3 := congrArg Subtype.val (hψ₀ ⟨k, hKH hk⟩ (Subgroup.mem_subgroupOf.mpr hk))
    simp only [hψ, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply] at h3 ⊢
    rw [h2, ← h3]
    congr 2
    exact Subtype.ext h1
  obtain ⟨e, heT, heL⟩ := exists_std_equiv_hat h21 h16 h1334 hS hH hK hKn hhat hTK
  set e' : ↥X ≃* SpecialLinearGroup (Fin 4) (ZMod 2) := ψ.symm.trans e with he'
  have he'σ : ∀ h : ↥H, e' ⟨σ h, hσX h⟩ = e ⟨S1549C.starHom hF h, hstarK h⟩ := by
    intro h
    rw [he', MulEquiv.trans_apply, ← hψσ h, MulEquiv.symm_apply_apply]
  have hTst : ∀ t (ht : t ∈ T), S1549C.starHom hF ⟨t, hTH ht⟩ ∈ S.KSt H T := fun t ht => by
    rw [S.kst_eq hF hTH]
    exact ⟨⟨t, hTH ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hL1st : ∀ x (hx : x ∈ S.L1), S1549C.starHom hF ⟨x, hL1H hx⟩ ∈ S.KSt H S.L1 :=
    fun x hx => by
      rw [S.kst_eq hF hL1H]
      exact ⟨⟨x, hL1H hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hU1 : ∀ u ∈ unitriangular 4 (ZMod 2), ∃ t, ∃ ht : t ∈ T,
      e' ⟨σ ⟨t, hTH ht⟩, hσX _⟩ = u := by
    intro u hu
    rw [← heT] at hu
    obtain ⟨y, hy, rfl⟩ := hu
    have hy' : (y : MulAut _) ∈ S.KSt H T := hy
    rw [S.kst_eq hF hTH] at hy'
    obtain ⟨t', ht', hyt⟩ := hy'
    have ht'T : (t' : G) ∈ T := Subgroup.mem_subgroupOf.mp ht'
    refine ⟨t', ht'T, ?_⟩
    rw [he'σ ⟨t', hTH ht'T⟩]
    exact congrArg e (Subtype.ext hyt)
  have hQ2 : ∀ x (hx : x ∈ S.L1), e' ⟨σ ⟨x, hL1H hx⟩, hσX _⟩ ∈ flagStabilizer 4 (ZMod 2) {2} := by
    intro x hx
    rw [← heL, he'σ]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (hL1st x hx)), rfl⟩
  have hsX : IsSimpleGroup ↥X := e'.isSimpleGroup
  obtain ⟨a₀, b₀, hab₀⟩ :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_nonabelian_of_card_two (Nat.card_zmod 2)
      (by norm_num : 3 ≤ 4)
  have hncX : ∃ a b : ↥X, a * b ≠ b * a := ⟨e'.symm a₀, e'.symm b₀, fun h => hab₀ (by
    have := congrArg e' h
    simpa using this)⟩
  have hcardX : Nat.card ↥X = 20160 := by
    rw [Nat.card_congr e'.toEquiv, card_SL_eq (by norm_num), Nat.card_zmod]
    decide
  have hnot2 : ¬ IsPGroup 2 ↥X := by
    intro hp
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hcardX] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 20160)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hZ : Subgroup.center ↥X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hncX
      have ha : a ∈ Subgroup.center ↥X := by rw [h]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hperf : Group.IsPerfect ↥X := He7.isPerfect_of_simple_noncomm hncX
  have hq : CFSG.IsQuasisimple ↥X := LRed5.isQuasisimple_of_simple_nonabelian hperf hncX
  have hSQ : SQTKGroup ↥X := S.sqtkGroup_autSec hA21 hH hHUW le_rfl hq
  have hirr : ∀ Z : Subgroup (Sec (⊤ : Subgroup ↥U) (W.subgroupOf U)),
      (∀ l ∈ X, ∀ z ∈ Z, l z ∈ Z) → Z = ⊥ ∨ Z = ⊤ := by
    intro Z hZX
    set W' : Subgroup G := (Z.comap (InternalSec.secMk (W.subgroupOf U))).map U.subtype
      with hW'
    have hmemW' : ∀ u (hu : u ∈ U), u ∈ W' ↔ InternalSec.secMk (W.subgroupOf U) ⟨u, hu⟩ ∈ Z :=
      fun u hu => ⟨fun ⟨y, hy, hyu⟩ => by
        have : y = ⟨u, hu⟩ := Subtype.ext hyu
        rw [← this]
        exact hy, fun h => ⟨⟨u, hu⟩, h, rfl⟩⟩
    have hWW' : W ≤ W' := fun w hw => (hmemW' w (hWU' hw)).2 (by
      rw [(A6Mod.secMk_eq_one_iff _).2 hw]
      exact Z.one_mem)
    have hW'U : W' ≤ U := Subgroup.map_subtype_le _
    have hconj : ∀ h : ↥H, ∀ u (hu : u ∈ U),
        InternalSec.secMk (W.subgroupOf U) ⟨(h : G) * u * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHU h.2) u).mp hu⟩ =
          σ h (InternalSec.secMk (W.subgroupOf U) ⟨u, hu⟩) := by
      intro h u hu
      rw [hσ, A6Mod.secAct_secMk]
      congr 1
    have hHW' : H ≤ Subgroup.normalizer (W' : Set G) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        have huU := hW'U hu
        have hc := (Subgroup.mem_normalizer_iff.mp (hHU hh) u).mp huU
        rw [hmemW' _ hc, hconj ⟨h, hh⟩ u huU]
        exact hZX _ (hσX _) _ ((hmemW' u huU).1 hu)
      · intro hu
        have hc := hW'U hu
        have huU : u ∈ U := (Subgroup.mem_normalizer_iff.mp (hHU hh) u).mpr hc
        rw [hmemW' _ huU]
        have h1 := (hmemW' _ hc).1 hu
        rw [hconj ⟨h, hh⟩ u huU] at h1
        have h2 := hZX _ (X.inv_mem (hσX ⟨h, hh⟩)) _ h1
        rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h2
    rcases hmax W' hWW' hW'U hHW' with h | h
    · left
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨⟨u, hu⟩, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf U) z
      have hu' : u ∈ W' := (hmemW' u hu).2 hz
      rw [h] at hu'
      rw [Subgroup.mem_bot]
      exact (A6Mod.secMk_eq_one_iff _).2 hu'
    · right
      rw [eq_top_iff]
      intro z _
      obtain ⟨⟨u, hu⟩, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf U) z
      exact (hmemW' u hu).1 (h ▸ hu)
  have hntop : (⊤ : Subgroup (Sec (⊤ : Subgroup ↥U) (W.subgroupOf U))) ≠ ⊥ := by
    intro h
    apply S.v2_not_mem hH hV₁W hWU hHW
    rw [← A6Mod.secMk_eq_one_iff (C := W) ⟨S.v2, S.v2_mem_UH H⟩, ← Subgroup.mem_bot, ← h]
    exact Subgroup.mem_top _
  have hb4 : B4Hyp X X := He7.b4Hyp_of_simple hsX hncX hnot2 hSQ hirr hntop
  obtain ⟨γ, γ', g, s, -, -, hpos, hle, -⟩ := S.case2_data hS hH hnt
  have hQ := S.mem_Qset_sec hS hH s hpos hle hV₁W hWU' hHW hfaith
  have hqhat : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ) :=
    (qhatOf_le_qOf X).trans (by exact_mod_cast qOf_le_two_of_mem_Qset hQ)
  have hType : B42TypeL42 ↥X := by
    refine ⟨hZ, ?_, ?_⟩
    · obtain ⟨hadm, F, hF1, hF2, hF3, ⟨f⟩⟩ := hKn
      exact ⟨hadm, F, hF1, hF2, hF3, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
        QuotientGroup.quotientBot).trans (ψ.symm.trans f)⟩⟩
    · exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
        ((e'.trans (FLc.slEquivGLt 4)).trans
          CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm)⟩
  have hq1 := asB45L42_holds _ hW2 X X hb4 hType hqhat
  obtain ⟨A, hA2, -, hAr⟩ := kq_le_iff.1 hq1
  obtain ⟨B, -, hB, -⟩ := exists_offender_rAV_le hW2 hA2 hAr
  let _ : Module (ZMod 2) (Additive (Sec (⊤ : Subgroup ↥U) (W.subgroupOf U))) :=
    B42Ln.zmod2Mod hW2
  set e'' : ↥X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) := e'.trans B42Ln.E4 with he''
  rcases B42Ln.l4Model_of_offender hb4 hZ e'' hB with htriv | ⟨κ, β, hβ⟩ | ⟨β, hβ⟩
  · exact (B42Ln.not_trivial4 e'' htriv).elim
  ·
    obtain ⟨τ', βA, hτ', hτU, hβA⟩ := nat_coords e' hβ
    have hsec : ∀ (h : ↥H) (u v : ↥U), (v : G) = h * u * h⁻¹ →
        InternalSec.secMk (W.subgroupOf U) v = σ h (InternalSec.secMk (W.subgroupOf U) u) := by
      intro h u v hv
      rw [hσ, A6Mod.secAct_secMk]
      congr 1
      apply Subtype.ext
      simp only [Setup.rho_apply_coe, hv, Subgroup.coe_inv]
    set σX : ↥H →* ↥X := σ.codRestrict X hσX with hσXdef
    set ρ₀ : ↥H →* SL4 := e'.toMonoidHom.comp σX with hρ₀def
    have hρ₀ : ∀ h, ρ₀ h = e' ⟨σ h, hσX h⟩ := fun h => rfl
    have hρ₀s : Function.Surjective ρ₀ := by
      intro q
      obtain ⟨h, -, hh⟩ := (A6Mod.mem_autSec_iff hHU hHUW le_rfl).1 (e'.symm q).2
      refine ⟨h, ?_⟩
      rw [hρ₀]
      have : (⟨σ h, hσX h⟩ : ↥X) = e'.symm q := Subtype.ext hh
      rw [this, MulEquiv.apply_symm_apply]
    have hρ₀k : ∀ h : ↥H, ρ₀ h = 1 ↔ (h : G) ∈ pCoreOf 2 H := by
      intro h
      rw [hρ₀, ← hker, map_eq_one_iff _ e'.injective]
      exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
    have hKL : S.KSt H (S.L1 ⊔ T) = S.KSt H S.L1 ⊔ S.KSt H T := S.kst_sup hF hL1H hTH
    have hρ₀Q : ∀ h : ↥H, (h : G) ∈ S.L1 ⊔ T → InQ2 (ρ₀ h : M4) := by
      intro h hh
      rw [← mem_flag_iff, hρ₀, he'σ, ← heL, mem_toSL, MulEquiv.symm_apply_apply, ← hKL,
        S.kst_eq hF (sup_le hL1H hTH)]
      exact ⟨h, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
    have hρ₀Q' : ∀ q : SL4, InQ2 (q : M4) → ∃ h : ↥H, (h : G) ∈ S.L1 ⊔ T ∧ ρ₀ h = q := by
      intro q hq
      rw [← mem_flag_iff, ← heL, mem_toSL, ← hKL, S.kst_eq hF (sup_le hL1H hTH)] at hq
      obtain ⟨h, hh, hhe⟩ := hq
      refine ⟨h, Subgroup.mem_subgroupOf.mp hh, ?_⟩
      rw [hρ₀, he'σ]
      have : (⟨S1549C.starHom hF h, hstarK h⟩ : ↥(S.KSt H K)) = e.symm q := Subtype.ext hhe
      rw [this, MulEquiv.apply_symm_apply]
    set ρ : ↥H →* SL4 := τ'.toMonoidHom.comp ρ₀ with hρdef
    have hρ : ∀ h, ρ h = τ' (ρ₀ h) := fun h => rfl
    let βG : ↥U →* Multiplicative V4 :=
      { toFun := fun u => Multiplicative.ofAdd (βA (Additive.ofMul
          (InternalSec.secMk (W.subgroupOf U) u)))
        map_one' := by simp
        map_mul' := fun u v => by
          simp only [map_mul, ofMul_mul, map_add, ofAdd_add] }
    refine ⟨ρ, βG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q
      obtain ⟨h, hh⟩ := hρ₀s (τ'.symm q)
      exact ⟨h, by rw [hρ, hh, MulEquiv.apply_symm_apply]⟩
    · intro h
      rw [hρ, map_eq_one_iff _ τ'.injective]
      exact hρ₀k h
    · intro h hh
      rw [hρ]
      exact (hτ' _).2 (hρ₀Q h hh)
    · intro q hq
      have hq' : InQ2 ((τ'.symm q : SL4) : M4) := by
        rw [← hτ', MulEquiv.apply_symm_apply]
        exact hq
      obtain ⟨h, hh, hhe⟩ := hρ₀Q' _ hq'
      exact ⟨h, hh, by rw [hρ, hhe, MulEquiv.apply_symm_apply]⟩
    · intro u hu
      obtain ⟨u', hu', hτu⟩ := hτU u hu
      obtain ⟨t, ht, hte⟩ := hU1 u' hu'
      exact ⟨⟨t, hTH ht⟩, ht, by rw [hρ, hρ₀, hte, hτu]⟩
    · intro y
      obtain ⟨w, hw⟩ := InternalSec.secMk_surjective (W.subgroupOf U)
        (Additive.toMul (βA.symm (Multiplicative.toAdd y)))
      refine ⟨w, ?_⟩
      show Multiplicative.ofAdd _ = y
      rw [hw, ofMul_toMul, AddEquiv.apply_symm_apply]
      rfl
    · intro u
      show Multiplicative.ofAdd _ = 1 ↔ _
      rw [← A6Mod.secMk_eq_one_iff (C := W) u]
      constructor
      · intro h1
        have h2 : βA (Additive.ofMul (InternalSec.secMk (W.subgroupOf U) u)) = 0 :=
          Multiplicative.ofAdd.injective h1
        have h3 : Additive.ofMul (InternalSec.secMk (W.subgroupOf U) u) = 0 :=
          βA.injective (h2.trans βA.map_zero.symm)
        exact Additive.ofMul.injective h3
      · intro h1
        rw [h1]
        simp
    · intro h u v hv
      show βA (Additive.ofMul (InternalSec.secMk (W.subgroupOf U) v)) =
        (ρ h : M4) *ᵥ βA (Additive.ofMul (InternalSec.secMk (W.subgroupOf U) u))
      rw [hsec h u v hv, hρ, hρ₀]
      exact hβA ⟨σ h, hσX h⟩ _
  ·
    exfalso
    obtain ⟨g₀, hgL, hg⟩ := S.exists_g012
    refine false_of_wedge e' hβ (v := InternalSec.secMk (W.subgroupOf U) ⟨S.v2, S.v2_mem_UH H⟩)
      ?_ (fun i => ?_) (hσX ⟨g₀, hL1H hgL⟩) (hQ2 g₀ hgL) ?_
    · intro h1
      exact S.v2_not_mem hH hV₁W hWU hHW
        ((A6Mod.secMk_eq_one_iff (U := U) (C := W) ⟨S.v2, S.v2_mem_UH H⟩).1 h1)
    · obtain ⟨t, ht, hte⟩ := hU1 _ (x4_mem_unitriangular i)
      refine ⟨⟨σ ⟨t, hTH ht⟩, hσX _⟩, hte, ?_⟩
      show σ ⟨t, hTH ht⟩ _ = _
      rw [hσ, A6Mod.secAct_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
        A6Mod.secMk_eq_one_iff]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
      exact hV₁W (S.comm_T_v2 ht)
    · intro h2
      apply S.comm_v2_not_mem hH hV₁W hWU hHW hgL hg
      rw [hσ, A6Mod.secAct_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
        A6Mod.secMk_eq_one_iff] at h2
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe] using h2

end Setting4

end CFSG.Quasithin.H13.A6
