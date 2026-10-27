module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannSetting
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannBridge
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecBase
import CFSG.GroupTheory.ElementaryAbelianTransport

public section
namespace CFSG.Quasithin.F53Push
open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin CFSG.Quasithin.F53Mod
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]

theorem isSec_zZero {X P Z : Subgroup G} (h : PushHyp X P Z) : IsSec X (zZero X Z) Z where
  le := inf_le_left
  normN := h.normal
  normL := h.le_normalizer_Z0
  comm := fun x hx y hy => by
    have : x * y = y * x := (h.elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩ |> congrArg Subtype.val)
    have e : x * y * x⁻¹ * y⁻¹ = 1 := by rw [this]; group
    rw [e]; exact (zZero X Z).one_mem
  sq := fun x hx => by
    have := h.elemAbelian.2 x hx
    rw [this]; exact (zZero X Z).one_mem

theorem eq_one_of_odd_orderOf_of_mem_pCoreOf {X : Subgroup G} {x : G} (hx : x ∈ pCoreOf 2 X)
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X))
    ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at hodd
  have : k = 0 := by
    by_contra hk0
    have : Even (2 ^ k) := (Nat.even_pow.mpr ⟨even_two, hk0⟩)
    exact (Nat.not_even_iff_odd.mpr hodd) this
  rw [this, pow_zero, orderOf_eq_one_iff] at hk
  exact hk

theorem eq_one_of_odd_of_acts_trivially {X P Z : Subgroup G} (h : PushHyp X P Z) {x : G}
    (hxX : x ∈ X) (hx : Odd (orderOf x))
    (hact : ∀ z ∈ Z, x * z * x⁻¹ * z⁻¹ ∈ zZero X Z) : x = 1 := by
  have hxL : x ∈ pResidualOf 2 X := by
    rw [← oTwoUpper_eq_pResidualOf]
    exact Subgroup.subset_closure ⟨hxX, hx⟩
  have hZ0 : zZero X Z ≤ Z := inf_le_left
  have hcop : Nat.Coprime (orderOf x) (Nat.card ↥(zZero X Z)) := by
    have h2 : IsPGroup 2 ↥(zZero X Z) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le (hZ0.trans h.le_core)
    obtain ⟨m, hm⟩ := h2.exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hx)
  have hxU : ∀ u ∈ zZero X Z, x * u * x⁻¹ * u⁻¹ ∈ (⊥ : Subgroup G) := by
    intro u hu
    have hc : x * u = u * x := Subgroup.mem_centralizer_iff.mp hu.2 x hxL
    rw [Subgroup.mem_bot]
    have : x * u * x⁻¹ * u⁻¹ = 1 := by
      rw [hc]; group
    exact this
  have key := coprime_conj_mem (Q := Z) (U := zZero X Z) (W := ⊥) (x := x) hZ0 bot_le
    (fun q hq w hw => by
      rw [Subgroup.mem_bot] at hw
      rw [hw]; simp) hxU hact hcop
  have hcen : x ∈ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := key z hz
    rw [Subgroup.mem_bot] at this
    calc z * x = (x * z * x⁻¹ * z⁻¹) * (z * x) := by rw [this, one_mul]
      _ = x * z := by group
  exact eq_one_of_odd_orderOf_of_mem_pCoreOf (h.mem_core_of_centralizes hxX hcen) hx


theorem mem_ker_conjHom_iff {X P Z : Subgroup G} (h : PushHyp X P Z) (g : ↥X) :
    (isSec_zZero h).conjHom g = 1 ↔ ∀ x ∈ Z, (g : G) * x * (g : G)⁻¹ * x⁻¹ ∈ zZero X Z := by
  have hs := isSec_zZero h
  constructor
  · intro hg x hx
    have h1 := congrArg (fun f => f (hs.proj ⟨x, hx⟩)) hg
    simp only [IsSec.conjHom_mk, MulAut.one_apply] at h1
    rw [IsSec.proj_eq_proj_iff] at h1
    have hxa : (g : G) * x * (g : G)⁻¹ ∈ Z := hs.conj_mem_N g ⟨x, hx⟩
    have hc : Commute ((g : G) * x * (g : G)⁻¹) x :=
      congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨_, hxa⟩ ⟨x, hx⟩)
    have e1 : (g : G) * x * (g : G)⁻¹ * x⁻¹ = (((g : G) * x * (g : G)⁻¹)⁻¹ * x)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      exact hc.inv_right.eq
    rw [e1]
    exact (zZero X Z).inv_mem (by simpa [IsSec.conjN] using h1)
  · intro hg
    exact hs.conjHom_eq_one fun x hx => hg x hx


theorem exists_pow_eq_one_of_mem_ker {X P Z : Subgroup G} (h : PushHyp X P Z) {x : ↥X}
    (hx : (isSec_zZero h).conjHom x = 1) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, ?_⟩
  set y : ↥X := x ^ 2 ^ k with hy
  have hyk : (isSec_zZero h).conjHom y = 1 := by rw [hy, map_pow, hx, one_pow]
  have hyord : orderOf y = m := by
    rw [hy, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hord ▸ dvd_mul_right _ _), hord,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hy1 : (y : G) = 1 := by
    refine eq_one_of_odd_of_acts_trivially h y.2 ?_ ((mem_ker_conjHom_iff h y).mp hyk)
    rw [Subgroup.orderOf_coe, hyord]
    exact hm
  exact Subtype.ext (by simpa using hy1)


section Coord

variable {W : Type} [Group W] {B : Type} [AddCommGroup B]

@[expose] def coordAct (c : W ≃* Multiplicative B) (a : MulAut W) : Equiv.Perm B :=
  Multiplicative.toAdd.symm.trans ((c.symm.trans (a.trans c)).toEquiv.trans Multiplicative.toAdd)

theorem coordAct_apply (c : W ≃* Multiplicative B) (a : MulAut W) (b : B) :
    coordAct c a b = Multiplicative.toAdd (c (a (c.symm (Multiplicative.ofAdd b)))) := rfl

theorem coordAct_add (c : W ≃* Multiplicative B) (a : MulAut W) (x y : B) :
    coordAct c a (x + y) = coordAct c a x + coordAct c a y := by
  simp only [coordAct_apply]
  rw [show Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y from rfl,
    map_mul, map_mul, map_mul]
  rfl

@[expose] def coordActHom (c : W ≃* Multiplicative B) : MulAut W →* Equiv.Perm B where
  toFun := coordAct c
  map_one' := by
    ext b
    simp [coordAct_apply]
  map_mul' a a' := by
    ext b
    simp [coordAct_apply]

theorem coordActHom_apply (c : W ≃* Multiplicative B) (a : MulAut W) (b : B) :
    coordActHom c a b = Multiplicative.toAdd (c (a (c.symm (Multiplicative.ofAdd b)))) := rfl

end Coord

theorem exists_hom_sl2 {Γ : Type*} [Group Γ] {F : Type*} [Field F]
    (a : Γ →* Equiv.Perm (Fin 2 → F))
    (h : ∀ g, ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, a g = slPerm F A) :
    ∃ α : Γ →* Matrix.SpecialLinearGroup (Fin 2) F, ∀ g, a g = slPerm F (α g) := by
  choose A hA using h
  refine ⟨
    { toFun := A
      map_one' := ?_
      map_mul' := ?_ }, hA⟩
  · apply slPerm_injective (k := F)
    rw [← hA, map_one, map_one]
  · intro g g'
    apply slPerm_injective (k := F)
    rw [map_mul, ← hA, ← hA, ← hA, map_mul]


omit [Finite G] in
theorem mem_centralizer_subgroupOf_iff {B X : Subgroup G} (hBX : B ≤ X) (x : ↥X) :
    x ∈ Subgroup.centralizer ((B.subgroupOf X : Subgroup X) : Set X) ↔
      (x : G) ∈ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h b hb
    exact congrArg Subtype.val (h ⟨b, hBX hb⟩ hb)
  · intro h b hb
    exact Subtype.ext (h b hb)

omit [Finite G] in
theorem isSylowTwoOf_top_subgroupOf {X P : Subgroup G} (hP : IsSylowTwoOf P X) :
    IsSylowTwoOf (P.subgroupOf X) (⊤ : Subgroup ↥X) := by
  refine ⟨le_top, hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm, ?_⟩
  show ¬ 2 ∣ (P.subgroupOf X).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact hP.2.2

omit [Finite G] in
theorem isElemAbelian_subgroupOf {X Z : Subgroup G} (hZ : IsElemAbelian 2 Z) :
    IsElemAbelian 2 (Z.subgroupOf X) := CFSG.Open.IsElemAbelian.subgroupOf hZ X

theorem mem_centralizer_oddOrder_iff {X : Subgroup G} (v : ↥X) :
    v ∈ Subgroup.centralizer
      ((CFSG.QuasithinUnique.Setup.oddOrderSubgroup (⊤ : Subgroup ↥X) : Subgroup ↥X) : Set ↥X) ↔
      (v : G) ∈ Subgroup.centralizer (pResidualOf 2 X : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hv l hl
    rw [← oTwoUpper_eq_pResidualOf] at hl
    obtain ⟨hlX, hlL⟩ := mem_oddOrderSubgroup_top_of_mem_oTwoUpper hl
    exact congrArg Subtype.val (hv _ hlL)
  · intro hv l hl
    have hle : CFSG.QuasithinUnique.Setup.oddOrderSubgroup (⊤ : Subgroup ↥X) ≤
        Subgroup.centralizer {v} := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨-, hu⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have huL : (u : G) ∈ pResidualOf 2 X := by
        rw [← oTwoUpper_eq_pResidualOf]
        exact Subgroup.subset_closure ⟨u.2, by simpa [Subgroup.orderOf_coe] using hu⟩
      exact Subtype.ext (hv _ huL)
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hl)
    exact this


omit [Finite G] in
theorem not_normal_subgroupOf {X P : Subgroup G} (hP : P ≠ ⊥) (hPX : P ≤ X)
    (hnc : NoCharNormal P X) : ¬ (P.subgroupOf X).Normal := by
  intro hn
  refine hnc P le_rfl hP ?_ ?_
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPX).mp hn


theorem baumannC_of_coords {X P Z : Subgroup G} (h : PushHyp X P Z) (hP : P ≠ ⊥)
    (hnc : NoCharNormal P X)
    (hM : ∃ M : Subgroup ↥X, P.subgroupOf X ≤ M ∧ M < ⊤ ∧
      ∀ Y : Subgroup ↥X, P.subgroupOf X ≤ Y → Y < ⊤ → Y ≤ M)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (c : (isSec_zZero h).W ≃* Multiplicative (Fin 2 → F))
    (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hα : ∀ g, coordActHom c ((isSec_zZero h).conjHom g) = slPerm F (α g))
    (hαs : Function.Surjective α) (hαk : ∀ g : ↥X, α g = 1 ↔ (g : G) ∈ pCoreOf 2 X) :
    BaumannC X Z := by
  obtain ⟨M, hRM, hlt, hmax⟩ := hM
  have hPX : P ≤ X := h.sylow.1
  have hZX : Z ≤ X := h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  have hs := isSec_zZero h
  let β : ↥(Z.subgroupOf X) →* Multiplicative (Fin 2 → F) :=
    c.toMonoidHom.comp (hs.proj.comp (Subgroup.subgroupOfEquivOfLe hZX).toMonoidHom)
  have hβ : ∀ v : ↥(Z.subgroupOf X),
      β v = c (hs.proj ⟨(v : ↥X).1, Subgroup.mem_subgroupOf.mp v.2⟩) := fun v => rfl
  obtain ⟨ρ, -, hset⟩ := exists_natQuotSetting_of_sl2' (R := P.subgroupOf X) (M := M)
    (V := Z.subgroupOf X) (isSylowTwoOf_top_subgroupOf h.sylow)
    (not_normal_subgroupOf hP hPX hnc) hRM hlt hmax
    (isElemAbelian_subgroupOf h.elemAbelian)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hZX).mpr h.normal)
    α hαs (by
      ext g
      rw [MonoidHom.mem_ker, hαk, mem_centralizer_subgroupOf_iff hZX]
      constructor
      · intro hg
        exact h.core_le_centralizer hg
      · intro hg
        exact h.mem_core_of_centralizes g.2 hg)
    β (by
      intro w
      obtain ⟨p, hp⟩ := c.surjective w
      obtain ⟨x, rfl⟩ := hs.proj_surjective p
      exact ⟨(Subgroup.subgroupOfEquivOfLe hZX).symm x, by rw [hβ]; exact hp⟩)
    (by
      intro g v v' hv'
      have h1 := hα g
      have hv'G : (v' : G) = (g : G) * (v : G) * (g : G)⁻¹ := by
        have := congrArg (fun y : ↥X => (y : G)) hv'
        simpa using this
      have key : hs.conjHom g (hs.proj ⟨(v : ↥X).1, Subgroup.mem_subgroupOf.mp v.2⟩) =
          hs.proj ⟨(v' : ↥X).1, Subgroup.mem_subgroupOf.mp v'.2⟩ := by
        rw [IsSec.conjHom_mk]
        congr 1
        exact Subtype.ext hv'G.symm
      have h3 : ((α g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
          (Multiplicative.toAdd (β v)) = slPerm F (α g) (Multiplicative.toAdd (β v)) := rfl
      rw [h3, ← h1]
      show Multiplicative.toAdd (β v') = Multiplicative.toAdd (c (hs.conjHom g
        (c.symm (Multiplicative.ofAdd (Multiplicative.toAdd (β v))))))
      rw [hβ v, hβ v']
      simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply]
      rw [key])
    (by
      ext v
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centralizer_oddOrder_iff]
      rw [hβ v]
      rw [MulEquiv.map_eq_one_iff, hs.proj_eq_one_iff]
      constructor
      · intro hv
        exact hv.2
      · intro hv
        exact ⟨Subgroup.mem_subgroupOf.mp v.2, hv⟩)
  exact baumannC_of_natQuotSetting h hnc hset

end CFSG.Quasithin.F53Push
