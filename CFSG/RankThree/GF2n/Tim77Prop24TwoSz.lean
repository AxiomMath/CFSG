module

public import CFSG.RankThree.GF2n.BenderTwoTrans
public import CFSG.RankThree.GF2n.SzExplicit
public import CFSG.RankThree.GF2n.NaturalDecomp
public import CFSG.RankThree.GF2n.Tim77Prop24TwoD

public section

open scoped IsMulCommutative

namespace CFSG.RankThree.GF2n

open CFSG.Open Matrix

@[expose] def MartineauSzInput : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) ↥(Sz a) V),
    (∃ g : ↥(Sz a), orderOf g = 5 ∧ ∀ v, ρ g v = v → v = 0) →
    ∃ s : Finset (Submodule (ZMod 2) V), s.SupIndep id ∧ s.sup id = ⊤ ∧
      ∀ W ∈ s, ∃ θ : (Fin 4 → GaloisField 2 (2 * a + 1)) →+ V, Function.Injective θ ∧
        θ.range = W.toAddSubgroup ∧
        ∀ (g : ↥(Sz a)) (v : Fin 4 → GaloisField 2 (2 * a + 1)),
          θ (((g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
            Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ v) = ρ g (θ v)

namespace Tim77

open CFSG.CGT.Timmesfeld75 CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

namespace Prop24Setup

variable {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
include S

theorem eq_one_of_commute_mul {a b m : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab)
    (hbL : b ∉ Lb) (hm : m ∈ M) (hmc : (a * b) * m = m * (a * b)) : m = 1 := by
  have haa : a * a = 1 := S.sq_A ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  set C : Subgroup G := M ⊓ Subgroup.centralizer ({a * b} : Set G) with hC
  have hCe : Assembly.IsElemAbelian 2 C :=
    ⟨⟨⟨fun u v => Subtype.ext (S.comm_M u.2.1 v.2.1)⟩⟩, fun u hu => S.isElemAbelian_M.2 u hu.1⟩
  have hinv : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [hainv, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right haa,
      inv_eq_of_mul_eq_one_right (S.sq_Ab hb), ← mul_assoc, haa, one_mul]
  have haN : a ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have key : ∀ z : G, z ∈ C → a * z * a⁻¹ ∈ C := by
      intro z hz
      obtain ⟨hzM, hzc⟩ := Subgroup.mem_inf.mp hz
      rw [Subgroup.mem_centralizer_singleton_iff] at hzc
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (S.A_le_normalizer_M ha) z).mp
        hzM, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hz' : z * (a * (a * b) * a⁻¹) = (a * (a * b) * a⁻¹) * z := by
        rw [hinv]
        calc z * (a * b)⁻¹ = (a * b)⁻¹ * ((a * b) * z) * (a * b)⁻¹ := by group
          _ = (a * b)⁻¹ * (z * (a * b)) * (a * b)⁻¹ := by rw [hzc]
          _ = (a * b)⁻¹ * z := by group
      calc a * z * a⁻¹ * (a * b) = a * (z * (a⁻¹ * (a * b) * a)) * a⁻¹ := by group
        _ = a * (z * (a * (a * b) * a⁻¹)) * a⁻¹ := by rw [hainv]
        _ = a * ((a * (a * b) * a⁻¹) * z) * a⁻¹ := by rw [hz']
        _ = a * (a⁻¹ * (a * b) * a * z) * a⁻¹ := by rw [hainv]
        _ = a * b * (a * z * a⁻¹) := by group
    constructor
    · exact key y
    · intro hy
      have := key _ hy
      rwa [show a * (a * y * a⁻¹) * a⁻¹ = (a * a) * y * (a * a)⁻¹ by group, haa, one_mul,
        inv_one, mul_one] at this
  by_contra hm1
  have hC1 : C ≠ ⊥ := fun h => hm1 (by
    have : m ∈ C := Subgroup.mem_inf.mpr ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr hmc.symm⟩
    rwa [h, Subgroup.mem_bot] at this)
  obtain ⟨y, hy, hy1, hay⟩ := exists_ne_one_commute hCe hC1 haN haa
  obtain ⟨hyM, hyc⟩ := Subgroup.mem_inf.mp hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hyc
  apply hy1
  refine S.eq_one_of_commute ha haL hb hbL hyM hay ?_
  calc b * y = a⁻¹ * ((a * b) * y) := by group
    _ = a⁻¹ * (y * (a * b)) := by rw [hyc]
    _ = a⁻¹ * (y * a) * b := by group
    _ = a⁻¹ * (a * y) * b := by rw [hay]
    _ = y * b := by group

theorem tim77_2_4_two_sz [(M.subgroupOf (A ⊔ Ab)).Normal] (hMart : MartineauSzInput) {a : ℕ}
    (ha : 1 ≤ a) (e : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* ↥(Sz a)) :
    ∃ ψ : ↥(A ⊔ Ab) →* GL (Fin 4) (GaloisField 2 (2 * a + 1)),
      ψ.range = Sz a ∧ ψ.ker = M.subgroupOf (A ⊔ Ab) ∧
      ∃ s : Finset (Subgroup G), s.SupIndep id ∧ s.sup id = M ∧
        ∀ W ∈ s, W ≤ M ∧ A ⊔ Ab ≤ Subgroup.normalizer (W : Set G) ∧ W ≠ ⊥ ∧
          (∀ U : Subgroup G, U ≤ W → A ⊔ Ab ≤ Subgroup.normalizer (U : Set G) →
            U = ⊥ ∨ U = W) ∧
          ∃ θ : (Fin 4 → GaloisField 2 (2 * a + 1)) → G, (∀ v v', θ (v + v') = θ v * θ v') ∧
            Function.Injective θ ∧ Set.range θ = W ∧ ∀ (x : ↥(A ⊔ Ab))
              (v : Fin 4 → GaloisField 2 (2 * a + 1)),
              θ (((ψ x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
                Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ v) = x * θ v * x⁻¹ := by
  classical
  have := S.isCommutative_M
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Module (ZMod 2) (Additive ↥M) := AddCommGroup.zmodModule fun v => by
    rw [two_nsmul]
    exact Additive.toMul.injective (Subtype.ext (S.mem_M_sq v.toMul.2))
  have hXN : A ⊔ Ab ≤ Subgroup.normalizer (M : Set G) := S.sup_le_normalizer_M
  have hπs : Function.Surjective (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))) :=
    QuotientGroup.mk'_surjective _
  set ψ : ↥(A ⊔ Ab) →* GL (Fin 4) (GaloisField 2 (2 * a + 1)) :=
    (Sz a).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))))
    with hψ
  have hψr : ψ.range = Sz a := by
    rw [hψ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (e.surjective.comp hπs),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hψk : ψ.ker = M.subgroupOf (A ⊔ Ab) := by
    ext x
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      OneMemClass.coe_eq_one, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, mk_eq_one_iff,
      Subgroup.mem_subgroupOf]
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
  set ρ : Representation (ZMod 2) ↥(Sz a) (Additive ↥M) :=
    (QuotientGroup.lift (M.subgroupOf (A ⊔ Ab)) φ₀ hker).comp e.symm.toMonoidHom with hρ
  have hρx : ∀ (x : ↥(A ⊔ Ab)), ρ (e (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) x)) = φ₀ x := by
    intro x
    rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
  have hρs : ∀ g : ↥(Sz a), ∃ x : ↥(A ⊔ Ab), e (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) x) = g :=
    fun g => (e.surjective.comp hπs) g
  have hBT : BenderType (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab)) (2 * a + 1) 2 1 :=
    .suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hS := S.strongWC_image
  have hT0 := S.image_ne_bot
  obtain ⟨x₀, hx₀⟩ := S.exists_image_conj
  obtain ⟨b₀, hb₀, hb₀L⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have hb₀mem : QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) ⟨b₀, Subgroup.mem_sup_right hb₀⟩ ∈
      (Ab.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))) :=
    ⟨_, hb₀, rfl⟩
  have hS' : StrongWC ((Ab.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)))) :=
    by rw [hx₀]; exact GF2n.StrongWC.conj hS _
  have hT0' : (Ab.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))) ≠ ⊥ :=
    fun h => (S.mk_not_mem_image hb₀ hb₀L) (by
      rw [h, Subgroup.mem_bot] at hb₀mem
      rw [hb₀mem]
      exact Subgroup.one_mem _)
  have hne : (A.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))) ≠
      (Ab.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))) :=
    fun h => S.mk_not_mem_image hb₀ hb₀L (h ▸ hb₀mem)
  have hwu : e.symm (SzExplicit.w a) * e.symm (SzExplicit.w a) = 1 := by
    rw [← map_mul, SzExplicit.w_mul_self, map_one]
  have huu : e.symm (SzExplicit.u a) * e.symm (SzExplicit.u a) = 1 := by
    rw [← map_mul, SzExplicit.u_mul_self, map_one]
  have hord5 : orderOf (e.symm (SzExplicit.w a) * e.symm (SzExplicit.u a)) = 5 := by
    rw [← map_mul, MulEquiv.orderOf_eq, SzExplicit.orderOf_w_mul_u]
  obtain ⟨t, ht, s', hs', hts⟩ := exists_mul_orderOf_eq hBT hS hT0 hS' hT0' hne hwu huu
    (by rw [hord5]; decide)
    (fun h => by rw [h, orderOf_one] at hord5; exact absurd hord5 (by decide))
  rw [hord5] at hts
  obtain ⟨a₁, ha₁, rfl⟩ := ht
  obtain ⟨b₁, hb₁, rfl⟩ := hs'
  have hsq : ∀ (z : ↥(A ⊔ Ab)), (z : G) * z = 1 →
      QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) z * QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) z =
        1 := fun z hz => by
    rw [← map_mul, show z * z = 1 from Subtype.ext hz, map_one]
  have hnot5 : ∀ y : ↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab), y * y = 1 → orderOf y ≠ 5 := by
    intro y hy h5
    have := orderOf_dvd_of_pow_eq_one (show y ^ 2 = 1 by rw [sq]; exact hy)
    rw [h5] at this
    exact absurd this (by decide)
  have ha₁L : (a₁ : G) ∉ L := fun h => hnot5 _ (hsq b₁ (S.sq_Ab (Subgroup.mem_subgroupOf.mp hb₁)))
    (by rwa [(mk_eq_one_iff a₁).mpr (S.L_le_M h), one_mul] at hts)
  have hb₁L : (b₁ : G) ∉ Lb := fun h => hnot5 _ (hsq a₁ (S.sq_A (Subgroup.mem_subgroupOf.mp ha₁)))
    (by rwa [(mk_eq_one_iff b₁).mpr (S.Lb_le_M h), mul_one] at hts)
  have hfpf : ∀ v, ρ (e (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) a₁ *
      QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) b₁)) v = v → v = 0 := by
    intro v hv
    rw [← map_mul, hρx] at hv
    have h' := congrArg (fun w : Additive ↥M => ((w.toMul : ↥M) : G)) hv
    simp only [hφ₀x, Subgroup.coe_mul] at h'
    have hc : ((a₁ : G) * b₁) * (v.toMul : G) = (v.toMul : G) * ((a₁ : G) * b₁) := by
      calc ((a₁ : G) * b₁) * (v.toMul : G) =
          (a₁ : G) * b₁ * v.toMul * ((a₁ : G) * b₁)⁻¹ * ((a₁ : G) * b₁) := by group
        _ = (v.toMul : G) * ((a₁ : G) * b₁) := by rw [h']
    exact Additive.toMul.injective (Subtype.ext (S.eq_one_of_commute_mul
      (Subgroup.mem_subgroupOf.mp ha₁) ha₁L (Subgroup.mem_subgroupOf.mp hb₁) hb₁L v.toMul.2 hc))
  obtain ⟨s₀, hs₀, hs₀top, hs₀nat⟩ := hMart a ha (Additive ↥M) ρ ⟨_, by
    rw [MulEquiv.orderOf_eq, hts], hfpf⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Submodule (ZMod 2) (Additive ↥M) → Subgroup G,
      ∀ W, Φ W = (Subgroup.toAddSubgroup.symm ((AddSubgroup.toZModSubmodule 2).symm W)).map
        M.subtype := ⟨_, fun _ => rfl⟩
  have hΦmem : ∀ (W : Submodule (ZMod 2) (Additive ↥M)) (g : G),
      g ∈ Φ W ↔ ∃ h : g ∈ M, Additive.ofMul (⟨g, h⟩ : ↥M) ∈ W := by
    intro W g
    rw [hΦ]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m.2, hm⟩
    · rintro ⟨h, hg⟩
      exact ⟨⟨g, h⟩, hg, rfl⟩
  have hsup : ∀ x y, Φ (x ⊔ y) = Φ x ⊔ Φ y := fun x y => by
    rw [hΦ, hΦ, hΦ, OrderIso.map_sup, OrderIso.map_sup, Subgroup.map_sup]
  have hbot : Φ ⊥ = ⊥ := by rw [hΦ, OrderIso.map_bot, OrderIso.map_bot, Subgroup.map_bot]
  refine ⟨ψ, hψr, hψk, s₀.image Φ, supIndep_image_of_lattice_hom hs₀ Φ hsup (fun x y => by
    rw [hΦ, hΦ, hΦ, OrderIso.map_inf, OrderIso.map_inf,
      Subgroup.map_inf_eq _ _ _ M.subtype_injective]) hbot, ?_, ?_⟩
  · rw [sup_image_of_sup_hom s₀ Φ hsup hbot, hs₀top, hΦ, OrderIso.map_top, OrderIso.map_top,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  intro W hW
  obtain ⟨W₀, hW₀, rfl⟩ := Finset.mem_image.mp hW
  obtain ⟨θ, hθinj, hθrange, hθ⟩ := hs₀nat W₀ hW₀
  have hθmem : ∀ w : Additive ↥M, w ∈ W₀ ↔ ∃ v, θ v = w := fun w => by
    rw [← Submodule.mem_toAddSubgroup, ← hθrange]
    rfl
  have hinv : ∀ x : ↥(A ⊔ Ab), ∀ w ∈ W₀, φ₀ x w ∈ W₀ := by
    intro x w hw
    obtain ⟨v, rfl⟩ := (hθmem w).mp hw
    rw [← hρx, ← hθ]
    exact (hθmem _).mpr ⟨_, rfl⟩
  have hXW : A ⊔ Ab ≤ Subgroup.normalizer ((Φ W₀ : Subgroup G) : Set G) := by
    intro x hx
    rw [hΦ, mem_normalizer_map_iff (hXN hx)]
    intro m hm
    exact hinv ⟨x, hx⟩ (Additive.ofMul m) hm
  refine ⟨by rw [hΦ]; exact Subgroup.map_subtype_le _, hXW, ?_, ?_, ?_⟩
  ·
    intro h
    have h1 : θ (Pi.single 0 1) ∈ W₀ := (hθmem _).mpr ⟨_, rfl⟩
    have h2 : (((θ (Pi.single 0 1)).toMul : ↥M) : G) ∈ Φ W₀ :=
      (hΦmem W₀ _).mpr ⟨(θ (Pi.single 0 1)).toMul.2, h1⟩
    rw [h, Subgroup.mem_bot] at h2
    have h3 : θ (Pi.single 0 1) = θ 0 := by
      rw [map_zero]
      exact Additive.toMul.injective (Subtype.ext h2)
    have := congrFun (hθinj h3) 0
    simp at this
  ·
    intro U hUW hUX
    set V₀ : AddSubgroup (Fin 4 → GaloisField 2 (2 * a + 1)) :=
      (Subgroup.toAddSubgroup (U.comap M.subtype)).comap θ with hV₀
    have hmemV : ∀ v, v ∈ V₀ ↔ (((θ v).toMul : ↥M) : G) ∈ U := fun v => Iff.rfl
    have hV₀inv : ∀ g ∈ Sz a, ∀ v ∈ V₀, ((g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ v ∈ V₀ := by
      intro g hg v hv
      obtain ⟨x, hx⟩ := hρs ⟨g, hg⟩
      rw [hmemV]
      have e1 := hθ ⟨g, hg⟩ v
      rw [show (((⟨g, hg⟩ : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) = (g : Matrix _ _ _) from rfl] at e1
      rw [e1, ← hx, hρx, hφ₀x]
      exact (Subgroup.mem_normalizer_iff.mp (hUX x.2) _).mp ((hmemV v).mp hv)
    rcases SzExplicit.eq_bot_or_eq_top_of_sz a hV₀inv with h | h
    · left
      rw [eq_bot_iff]
      intro g hg
      obtain ⟨hgM, hgW⟩ := (hΦmem W₀ g).mp (hUW hg)
      obtain ⟨v, hv⟩ := (hθmem _).mp hgW
      have hvV : v ∈ V₀ := by
        rw [hmemV, hv]
        exact hg
      rw [h, AddSubgroup.mem_bot] at hvV
      rw [hvV, map_zero] at hv
      rw [Subgroup.mem_bot]
      have := congrArg (fun w : Additive ↥M => ((w.toMul : ↥M) : G)) hv
      simpa using this.symm
    · right
      refine le_antisymm hUW fun g hg => ?_
      obtain ⟨hgM, hgW⟩ := (hΦmem W₀ g).mp hg
      obtain ⟨v, hv⟩ := (hθmem _).mp hgW
      have hvV : v ∈ V₀ := h ▸ AddSubgroup.mem_top v
      rw [hmemV, hv] at hvV
      exact hvV
  ·
    refine ⟨fun v => (((θ v).toMul : ↥M) : G), fun v v' => ?_, ?_, ?_, ?_⟩
    · show (((θ (v + v')).toMul : ↥M) : G) = (((θ v).toMul : ↥M) : G) * (((θ v').toMul : ↥M) : G)
      rw [map_add, toMul_add, Subgroup.coe_mul]
    · intro v v' h
      exact hθinj (Additive.toMul.injective (Subtype.ext h))
    · ext g
      rw [SetLike.mem_coe, hΦmem]
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨(θ v).toMul.2, (hθmem _).mpr ⟨v, rfl⟩⟩
      · rintro ⟨h, hg⟩
        obtain ⟨v, hv⟩ := (hθmem _).mp hg
        refine ⟨v, ?_⟩
        show (((θ v).toMul : ↥M) : G) = g
        rw [hv]
        rfl
    · intro x v
      show (((θ (((ψ x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ v)).toMul : ↥M) : G) =
        (x : G) * (((θ v).toMul : ↥M) : G) * (x : G)⁻¹
      have e1 := hθ (e (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) x)) v
      rw [hρx] at e1
      rw [show ((ψ x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) =
          (((e (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)) x) : ↥(Sz a)) :
            GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
            Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) from rfl, e1]
      exact hφ₀x x (θ v)


end Prop24Setup

end Tim77

end CFSG.RankThree.GF2n
