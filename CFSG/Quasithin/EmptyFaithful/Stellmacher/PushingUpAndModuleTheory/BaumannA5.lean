module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannSec
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannA5Id
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannA5Max

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin
  CFSG.Quasithin.F53Mod CFSG.Fischer Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def natXiEquiv : (Fin 4 → ZMod 2) ≃+ (Fin 2 → F4) where
  toFun := natXi
  invFun := natXiInv
  left_inv := natXiInv_natXi
  right_inv := natXi_natXiInv
  map_add' := natXi_add

theorem baumann_c_a5 {X P Z : Subgroup G} (h : PushHyp X P Z)
    (hq : Nonempty (OTwoQuot X ≃* ↥(alternatingGroup (Fin 5))))
    (hN : IsNatSecA5 X (zZero X Z) Z) (hnc : NoCharNormal P X) : BaumannC X Z := by
  obtain ⟨e⟩ := hq
  obtain ⟨hnorm, θ, β, hθs, hθk, hsd⟩ := hN
  have hPX : P ≤ X := h.sylow.1
  have hs := isSec_zZero h
  obtain ⟨φ, hφs, hφk⟩ := exists_hom_of_quot e
  have hle : φ.ker ≤ θ.ker := fun x hx =>
    (mem_cSecIn_iff_of_ker_hom hθk x.2).mpr (core_le_cSecIn h _ ((hφk x).mp hx))
  have hker' : θ.ker ≤ φ.ker := ker_le_of_surjective hφs hθs hle
  have hker : ∀ x : ↥X, θ x = 1 ↔ (x : G) ∈ pCoreOf 2 X := fun x =>
    ⟨fun hx => (hφk x).mp (hker' hx), fun hx => hle ((hφk x).mpr hx)⟩
  set θ' : ↥X →* Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp θ with hθ'
  have hsign : ∀ g : ↥X, Perm.sign (θ' g) = 1 := fun g =>
    Equiv.Perm.mem_alternatingGroup.mp (θ g).2
  let e1 : nat.W ≃* hs.W := MulEquiv.ofBijective (β : nat.W →* hs.W) ⟨hsd.inj, hsd.surj⟩
  let xiMul : nat.W ≃* Multiplicative (Fin 2 → F4) :=
    (AddEquiv.toMultiplicative natXiEquiv :
      Multiplicative (Fin 4 → ZMod 2) ≃* Multiplicative (Fin 2 → F4))
  let c : hs.W ≃* Multiplicative (Fin 2 → F4) := e1.symm.trans xiMul
  have hcβ : ∀ u : nat.W, c (β u) = xiMul u := fun u => by
    show xiMul (e1.symm (β u)) = xiMul u
    rw [show β u = e1 u from rfl, MulEquiv.symm_apply_apply]
  have hconj : ∀ (g : ↥X) (u : nat.W), hs.conjHom g (β u) = β (nat.act (θ' g) u) := by
    intro g u
    obtain ⟨x, hx⟩ := hs.proj_surjective (β u)
    obtain ⟨hkx, h1⟩ := hsd.equiv g u x hx.symm
    rw [← hx, IsSec.conjHom_mk, h1]
    rfl
  have hcoord : ∀ (g : ↥X) (w : Fin 2 → F4), coordActHom c (hs.conjHom g) w =
      natPermF4 (θ' g) w := by
    intro g w
    have h1 : c.symm (Multiplicative.ofAdd w) = β (xiMul.symm (Multiplicative.ofAdd w)) := by
      apply c.injective
      rw [MulEquiv.apply_symm_apply, hcβ, MulEquiv.apply_symm_apply]
    rw [coordActHom_apply, h1, hconj, hcβ]
    rfl
  have ha : ∀ g : ↥X, ∃ A : Matrix.SpecialLinearGroup (Fin 2) F4,
      (coordActHom c).comp hs.conjHom g = slPerm F4 A := by
    intro g
    obtain ⟨hdet, hmul⟩ := natMatF4_spec (θ' g) (hsign g)
    refine ⟨(⟨natMatF4 (θ' g), hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) F4), ?_⟩
    ext w : 1
    show coordActHom c (hs.conjHom g) w = _
    rw [hcoord]
    exact hmul w
  obtain ⟨α, hα⟩ := exists_hom_sl2 ((coordActHom c).comp hs.conjHom) ha
  have hαθ : ∀ g : ↥X, α g = 1 ↔ θ g = 1 := by
    intro g
    constructor
    · intro hg
      have h1 : ∀ w, natPermF4 (θ' g) w = w := by
        intro w
        have := congrArg (fun f : Perm (Fin 2 → F4) => f w) (hα g)
        simp only [MonoidHom.comp_apply] at this
        rw [hg, map_one] at this
        rw [← hcoord g w]
        exact this
      have h2 : ∀ c0, natAct (θ' g) c0 = c0 := by
        intro c0
        have := h1 (natXi c0)
        unfold natPermF4 at this
        rw [natXiInv_natXi] at this
        calc natAct (θ' g) c0 = natXiInv (natXi (natAct (θ' g) c0)) := (natXiInv_natXi _).symm
          _ = natXiInv (natXi c0) := by rw [this]
          _ = c0 := natXiInv_natXi _
      have h3 : θ' g = 1 := natAct_faithful_alt _ (hsign g) h2
      exact Subtype.ext h3
    · intro hg
      apply slPerm_injective (k := F4)
      rw [← hα g]
      have h3 : θ' g = 1 := by simp [hθ', hg]
      ext w : 1
      show coordActHom c (hs.conjHom g) w = _
      rw [hcoord, h3]
      rw [map_one, Equiv.Perm.coe_one, id_eq]
      unfold natPermF4
      rw [natAct_one, natXi_natXiInv]
  have hαker : α.ker = θ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hαθ]
  have hαs : Function.Surjective α := by
    rw [← MonoidHom.range_eq_top]
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [← Subgroup.index_ker, hαker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hθs,
      Subgroup.card_top, card_specialLinear_F4]
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hR2 : IsPGroup 2 (P.subgroupOf X) := (isSylowTwoOf_top_subgroupOf h.sylow).2.1
  have hker_le : θ.ker ≤ P.subgroupOf X := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (h.core_le ((hker x).mp hx))
  have hcardA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hcardB : Nat.card ((P.subgroupOf X).map θ) = 4 := by
    have hB2 : IsPGroup 2 ((P.subgroupOf X).map θ) := hR2.map θ
    have hidx : ((P.subgroupOf X).map θ).index = (P.subgroupOf X).index :=
      Subgroup.index_map_eq _ hθs hker_le
    have hodd : ¬ 2 ∣ (P.subgroupOf X).index := h.sylow.2.2
    have h1 := Subgroup.card_mul_index ((P.subgroupOf X).map θ)
    rw [hidx, hcardA] at h1
    obtain ⟨k, hk⟩ := hB2.exists_card_eq
    rw [hk] at h1
    have hk5 : k ≤ 5 := by
      by_contra hk6
      have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < (P.subgroupOf X).index := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at h1)
      nlinarith
    interval_cases k
    · omega
    · exfalso; apply hodd; omega
    · rw [hk]; norm_num
    all_goals omega
  have hP : P ≠ ⊥ := by
    rintro rfl
    have : Nat.card (((⊥ : Subgroup G).subgroupOf X).map θ) = 1 := by
      rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
      simp
    omega
  exact baumannC_of_coords h hP hnc
    (exists_unique_max_of_quotient_a5 (P.subgroupOf X) θ hθs hker_le hcardB) c α hα hαs
    (fun g => by rw [hαθ, hker])

theorem baumannA5_holds (G : Type) [Group G] [Finite G] : BaumannA5 G :=
  fun _ _ _ h hq hN hnc => baumann_c_a5 h hq hN hnc

end CFSG.Quasithin.F53Push
