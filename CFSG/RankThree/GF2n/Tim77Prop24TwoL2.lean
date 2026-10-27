module

public import CFSG.RankThree.GF2n.Tim77Prop24TwoD
public import CFSG.RankThree.GF2n.NaturalDecomp
public import CFSG.CGT.Timmesfeld75.L2Pair

public section

open scoped IsMulCommutative

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.RankOne Matrix
open scoped MatrixGroups

theorem utri_eq_upperUnipotent (F : Type) [Field F] : utri F = upperUnipotent F := by
  ext g
  rw [mem_utri_iff, mem_upperUnipotent_iff F]
  have e : ∀ s : F, utriElt s = upperElt F s := fun s =>
    sl2_ext (by simp [utriElt_apply_00, upperElt]) (by simp [utriElt_apply_01, upperElt])
      (by simp [utriElt_apply_10, upperElt]) (by simp [utriElt_apply_11, upperElt])
  simp only [e]

variable {G : Type} [Group G] [Finite G]

namespace Prop24Setup

variable {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
include S

theorem exists_sl2_equiv [(M.subgroupOf (A ⊔ Ab)).Normal] {f : ℕ} (hf : 2 ≤ f)
    (e : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* PSL(2, GaloisField 2 f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (e' : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* SL(2, F)), Nat.card F = 2 ^ f ∧
      ((A.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)))).map
        e'.toMonoidHom = upperUnipotent F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := S.strongWC_image
  have hT0 := S.image_ne_bot
  obtain ⟨P, hTP⟩ := (isPGroup_of_strongWC hS).exists_le_sylow
  have hL2 := IsL2Pair.of_psl_sylow (by omega : f ≠ 0) ⟨e⟩ P
  have hTeq := hL2.eq_of_isWC hTP hT0 hS.isWC
  rw [← hTeq] at hL2
  obtain ⟨F, hF, hFin, hchar, e', hcard, hmap⟩ := hL2
  exact ⟨F, hF, hFin, hchar, e', hcard, by rw [hmap, utri_eq_upperUnipotent]⟩

theorem conj_mul_inv_mem_L {y m : G} (hy : y ∈ A) (hm : m ∈ M) : y * m * y⁻¹ * m⁻¹ ∈ L := by
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hm
  have hc := S.commutator_mem_L hy hlb
  have hyl : y * l = l * y := S.comm_A hy (S.L_le hl)
  have hlc : l * (y * lb * y⁻¹ * lb⁻¹) = (y * lb * y⁻¹ * lb⁻¹) * l :=
    S.comm_A (S.L_le hl) (S.L_le hc)
  have e : y * (l * lb) * y⁻¹ * (l * lb)⁻¹ = y * lb * y⁻¹ * lb⁻¹ := by
    calc y * (l * lb) * y⁻¹ * (l * lb)⁻¹ = (y * l) * lb * y⁻¹ * lb⁻¹ * l⁻¹ := by group
      _ = l * (y * lb * y⁻¹ * lb⁻¹) * l⁻¹ := by rw [hyl]; group
      _ = y * lb * y⁻¹ * lb⁻¹ := by rw [hlc, mul_inv_cancel_right]
  rw [e]
  exact hc

theorem tim77_2_4_two_psl [(M.subgroupOf (A ⊔ Ab)).Normal] {f : ℕ} (hf : 2 ≤ f)
    (e : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* PSL(2, GaloisField 2 f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (ψ : ↥(A ⊔ Ab) →* SL(2, F)),
      Nat.card F = 2 ^ f ∧ Function.Surjective ψ ∧ ψ.ker = M.subgroupOf (A ⊔ Ab) ∧
      ∃ s : Finset (Subgroup G), s.SupIndep id ∧ s.sup id = M ∧
        ∀ W ∈ s, W ≤ M ∧ A ⊔ Ab ≤ Subgroup.normalizer (W : Set G) ∧ W ≠ ⊥ ∧
          (∀ U : Subgroup G, U ≤ W → A ⊔ Ab ≤ Subgroup.normalizer (U : Set G) →
            U = ⊥ ∨ U = W) ∧
          ∃ θ : (Fin 2 → F) → G, (∀ v v', θ (v + v') = θ v * θ v') ∧ Function.Injective θ ∧
            Set.range θ = W ∧ ∀ (x : ↥(A ⊔ Ab)) (v : Fin 2 → F),
              θ ((ψ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = x * θ v * x⁻¹ := by
  classical
  have := S.isCommutative_M
  let : Module (ZMod 2) (Additive ↥M) := AddCommGroup.zmodModule fun v => by
    rw [two_nsmul]
    exact Additive.toMul.injective (Subtype.ext (S.mem_M_sq v.toMul.2))
  obtain ⟨F, hF, hFin, hchar, e', hcard, hmap⟩ := S.exists_sl2_equiv hf e
  have hXN : A ⊔ Ab ≤ Subgroup.normalizer (M : Set G) := S.sup_le_normalizer_M
  set ψ : ↥(A ⊔ Ab) →* SL(2, F) :=
    e'.toMonoidHom.comp (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))) with hψ
  have hψs : Function.Surjective ψ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψk : ψ.ker = M.subgroupOf (A ⊔ Ab) := by
    ext x
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, mk_eq_one_iff, Subgroup.mem_subgroupOf]
  set φ₀ : ↥(A ⊔ Ab) →* Module.End (ZMod 2) (Additive ↥M) :=
    (conjEndHom M).comp (Subgroup.inclusion hXN) with hφ₀
  have hφ₀x : ∀ (x : ↥(A ⊔ Ab)) (v : Additive ↥M),
      ((φ₀ x v).toMul : G) = (x : G) * (v.toMul : G) * (x : G)⁻¹ := fun _ _ => rfl
  have hker : M.subgroupOf (A ⊔ Ab) ≤ φ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine LinearMap.ext fun v => Additive.toMul.injective (Subtype.ext ?_)
    rw [hφ₀x, S.comm_M (Subgroup.mem_subgroupOf.mp hx) v.toMul.2, mul_inv_cancel_right]
    rfl
  set ρ : SL(2, F) →* Module.End (ZMod 2) (Additive ↥M) :=
    (QuotientGroup.lift (M.subgroupOf (A ⊔ Ab)) φ₀ hker).comp e'.symm.toMonoidHom with hρ
  let : DistribMulAction SL(2, F) (Additive ↥M) := DistribMulAction.compHom _ ρ
  have hsmul : ∀ (x : ↥(A ⊔ Ab)) (v : Additive ↥M), ψ x • v = φ₀ x v := by
    intro x v
    show ρ (ψ x) v = φ₀ x v
    rw [hρ, hψ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, QuotientGroup.mk'_apply,
      QuotientGroup.lift_mk]
  have hsub : ∀ v w : Additive ↥M,
      (((v - w).toMul : ↥M) : G) = ((v.toMul : ↥M) : G) * ((w.toMul : ↥M) : G)⁻¹ := fun v w => by
    rw [toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
  have hsmul' : ∀ (g : SL(2, F)) (v : Additive ↥M), ∃ x : ↥(A ⊔ Ab), ψ x = g ∧
      g • v = φ₀ x v := fun g v => by
    obtain ⟨x, rfl⟩ := hψs g
    exact ⟨x, rfl, hsmul x v⟩
  have hupper : ∀ g ∈ upperUnipotent F, ∃ y : ↥(A ⊔ Ab), (y : G) ∈ A ∧ ψ y = g := by
    intro g hg
    rw [← hmap] at hg
    obtain ⟨t, ⟨y, hy, rfl⟩, rfl⟩ := hg
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  obtain ⟨a, ha, haL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨b, hb, hbL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  set a' : ↥(A ⊔ Ab) := ⟨a, Subgroup.mem_sup_left ha⟩
  set b' : ↥(A ⊔ Ab) := ⟨b, Subgroup.mem_sup_right hb⟩
  have hfixφ : ∀ (x : ↥(A ⊔ Ab)) (v : Additive ↥M), φ₀ x v = v →
      (x : G) * (v.toMul : G) = (v.toMul : G) * x := fun x v h => by
    have h' := congrArg (fun w : Additive ↥M => ((w.toMul : ↥M) : G)) h
    simp only [hφ₀x] at h'
    calc (x : G) * (v.toMul : G) = (x : G) * v.toMul * (x : G)⁻¹ * x := by group
      _ = (v.toMul : G) * x := by rw [h']
  have hfix : ∀ v : Additive ↥M, (∀ g : SL(2, F), g • v = v) → v = 0 := by
    intro v hv
    have h1 := hfixφ a' v (by rw [← hsmul]; exact hv _)
    have h2 := hfixφ b' v (by rw [← hsmul]; exact hv _)
    exact Additive.toMul.injective (Subtype.ext
      (S.eq_one_of_commute ha haL hb hbL v.toMul.2 h1 h2))
  have hcomA : ∀ (y : ↥(A ⊔ Ab)), (y : G) ∈ A → ∀ v : Additive ↥M, ((v.toMul : ↥M) : G) ∈ L →
      φ₀ y v = v := fun y hy v hv => by
    refine Additive.toMul.injective (Subtype.ext ?_)
    rw [hφ₀x, S.comm_A hy (S.L_le hv), mul_inv_cancel_right]
  have hquad : ∀ g ∈ upperUnipotent F, ∀ g' ∈ upperUnipotent F, ∀ v : Additive ↥M,
      g' • (g • v - v) = g • v - v := by
    intro g hg g' hg' v
    obtain ⟨y, hy, rfl⟩ := hupper g hg
    obtain ⟨y', hy', rfl⟩ := hupper g' hg'
    rw [hsmul, hsmul]
    apply hcomA y' hy'
    rw [hsub, hφ₀x]
    exact S.conj_mul_inv_mem_L hy v.toMul.2
  set Lsub : AddSubgroup (Additive ↥M) := Subgroup.toAddSubgroup (L.subgroupOf M) with hLsub
  have hLw : ∀ w ∈ Lsub, ∀ g ∈ upperUnipotent F, g • w = w := by
    intro w hw g hg
    obtain ⟨y, hy, rfl⟩ := hupper g hg
    rw [hsmul]
    exact hcomA y hy w (Subgroup.mem_subgroupOf.mp hw)
  have hgen : ∀ U : AddSubgroup (Additive ↥M), (∀ g : SL(2, F), ∀ v ∈ U, g • v ∈ U) →
      Lsub ≤ U → U = ⊤ := by
    intro U hU hLU
    have hUL : ∀ m : ↥M, (m : G) ∈ L → Additive.ofMul m ∈ U := fun m hm =>
      hLU (Subgroup.mem_subgroupOf.mpr hm)
    have hULb : ∀ m : ↥M, (m : G) ∈ Lb → Additive.ofMul m ∈ U := by
      intro m hm
      obtain ⟨n, hn, hnm⟩ := S.symm.exists_commutator_eq hb hbL hm
      have hnM : n ∈ M := S.L_le_M hn
      have h1 : Additive.ofMul (⟨n, hnM⟩ : ↥M) ∈ U := hUL ⟨n, hnM⟩ hn
      have h2 := hU (ψ b') _ h1
      rw [hsmul] at h2
      have h3 : φ₀ b' (Additive.ofMul ⟨n, hnM⟩) - Additive.ofMul ⟨n, hnM⟩ = Additive.ofMul m := by
        refine Additive.toMul.injective (Subtype.ext ?_)
        rw [hsub, hφ₀x]
        exact hnm
      rw [← h3]
      exact U.sub_mem h2 h1
    rw [eq_top_iff]
    intro v _
    obtain ⟨l, hl, lb, hlb, he⟩ := S.exists_mul_of_mem_M v.toMul.2
    have hv : v = Additive.ofMul ⟨l, S.L_le_M hl⟩ + Additive.ofMul ⟨lb, S.Lb_le_M hlb⟩ :=
      Additive.toMul.injective (Subtype.ext he)
    rw [hv]
    exact U.add_mem (hUL _ hl) (hULb _ hlb)
  obtain ⟨s₀, hs₀, hs₀top, hs₀P⟩ := exists_supIndep_natural hfix hquad hLw hgen
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : AddSubgroup (Additive ↥M) → Subgroup G,
      ∀ W, Φ W = (Subgroup.toAddSubgroup.symm W).map M.subtype := ⟨_, fun _ => rfl⟩
  have hΦmem : ∀ (W : AddSubgroup (Additive ↥M)) (g : G),
      g ∈ Φ W ↔ ∃ h : g ∈ M, Additive.ofMul (⟨g, h⟩ : ↥M) ∈ W := by
    intro W g
    constructor
    · rw [hΦ]
      rintro ⟨m, hm, rfl⟩
      exact ⟨m.2, hm⟩
    · rintro ⟨h, hg⟩
      rw [hΦ]
      exact ⟨⟨g, h⟩, hg, rfl⟩
  have hΦinv : ∀ W : AddSubgroup (Additive ↥M), (∀ g : SL(2, F), ∀ v ∈ W, g • v ∈ W) →
      A ⊔ Ab ≤ Subgroup.normalizer ((Φ W : Subgroup G) : Set G) := by
    intro W hW x hx
    rw [hΦ, mem_normalizer_map_iff (hXN hx)]
    intro m hm
    have := hW (ψ ⟨x, hx⟩) (Additive.ofMul m) hm
    rw [hsmul] at this
    exact this
  refine ⟨F, hF, hFin, hchar, ψ, hcard, hψs, hψk, s₀.image Φ,
    supIndep_image_of_lattice_hom hs₀ Φ ?_ ?_ ?_, ?_, ?_⟩
  · intro x y
    rw [hΦ, hΦ, hΦ, OrderIso.map_sup, Subgroup.map_sup]
  · intro x y
    rw [hΦ, hΦ, hΦ, OrderIso.map_inf, Subgroup.map_inf_eq _ _ _ M.subtype_injective]
  · rw [hΦ, OrderIso.map_bot, Subgroup.map_bot]
  · rw [sup_image_of_sup_hom s₀ Φ
      (fun x y => by rw [hΦ, hΦ, hΦ, OrderIso.map_sup, Subgroup.map_sup])
      (by rw [hΦ, OrderIso.map_bot, Subgroup.map_bot]), hs₀top, hΦ, OrderIso.map_top,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  intro W hW
  obtain ⟨W₀, hW₀, rfl⟩ := Finset.mem_image.mp hW
  obtain ⟨hW₀inv, hW₀0, hW₀irr, θ, hθinj, hθrange, hθ⟩ := hs₀P W₀ hW₀
  refine ⟨by rw [hΦ]; exact Subgroup.map_subtype_le _, hΦinv W₀ hW₀inv, ?_, ?_, ?_⟩
  · intro h
    apply hW₀0
    have h' : Subgroup.toAddSubgroup.symm W₀ = ⊥ := by
      rwa [hΦ, ← Subgroup.map_bot M.subtype, (Subgroup.map_injective M.subtype_injective).eq_iff]
        at h
    rw [← OrderIso.apply_symm_apply Subgroup.toAddSubgroup W₀, h', OrderIso.map_bot]
  · intro U hUW hUX
    have hUM : U ≤ M := hUW.trans (by rw [hΦ]; exact Subgroup.map_subtype_le _)
    set U₀ : AddSubgroup (Additive ↥M) := Subgroup.toAddSubgroup (U.comap M.subtype) with hU₀
    have hU₀W : U₀ ≤ W₀ := by
      intro v hv
      have : ((v.toMul : ↥M) : G) ∈ Φ W₀ := hUW hv
      obtain ⟨h, hv'⟩ := (hΦmem W₀ _).mp this
      exact hv'
    have hU₀inv : ∀ g : SL(2, F), ∀ v ∈ U₀, g • v ∈ U₀ := by
      intro g v hv
      obtain ⟨x, -, hgx⟩ := hsmul' g v
      rw [hgx]
      show ((φ₀ x v).toMul : G) ∈ U
      rw [hφ₀x]
      exact (Subgroup.mem_normalizer_iff.mp (hUX x.2) _).mp hv
    have hUe : Φ U₀ = U := by
      rw [hΦ, hU₀, OrderIso.symm_apply_apply, Subgroup.map_comap_eq, Subgroup.range_subtype,
        inf_of_le_right hUM]
    rcases hW₀irr U₀ hU₀W hU₀inv with h | h
    · left
      rw [← hUe, h, hΦ, OrderIso.map_bot, Subgroup.map_bot]
    · right
      rw [← hUe, h]
  · refine ⟨fun v => (((θ v).toMul : ↥M) : G), fun v v' => ?_, ?_, ?_, ?_⟩
    · show (((θ (v + v')).toMul : ↥M) : G) = (((θ v).toMul : ↥M) : G) * (((θ v').toMul : ↥M) : G)
      rw [map_add, toMul_add, Subgroup.coe_mul]
    · intro v v' h
      exact hθinj (Additive.toMul.injective (Subtype.ext h))
    · ext g
      rw [SetLike.mem_coe, hΦmem]
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨(θ v).toMul.2, by rw [← hθrange]; exact ⟨v, rfl⟩⟩
      · rintro ⟨h, hg⟩
        rw [← hθrange] at hg
        obtain ⟨v, hv⟩ := hg
        refine ⟨v, ?_⟩
        show (((θ v).toMul : ↥M) : G) = g
        rw [hv]
        rfl
    · intro x v
      show (((θ ((ψ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v)).toMul : ↥M) : G) =
        (x : G) * (((θ v).toMul : ↥M) : G) * (x : G)⁻¹
      rw [hθ, hsmul]
      exact hφ₀x x (θ v)

end Prop24Setup

end CFSG.RankThree.GF2n.Tim77
