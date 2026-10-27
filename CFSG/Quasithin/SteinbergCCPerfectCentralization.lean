module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Quasithin.Background.A1cModuleUnits

public section

namespace CFSG.Quasithin.SteinbergCC

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_normalizer_of_conj_mem {K S : Subgroup G} (h : ∀ g ∈ K, ∀ s ∈ S, g * s * g⁻¹ ∈ S) :
    K ≤ normalizer (S : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro s
  refine ⟨h g hg s, fun hs => ?_⟩
  have h1 := h g⁻¹ (inv_mem hg) _ hs
  rwa [show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s by group] at h1

theorem conj_mem_commutator {H₁ H₂ : Subgroup G} {g : G} (h₁ : ∀ x ∈ H₁, g * x * g⁻¹ ∈ H₁)
    (h₂ : ∀ x ∈ H₂, g * x * g⁻¹ ∈ H₂) {z : G} (hz : z ∈ ⁅H₁, H₂⁆) : g * z * g⁻¹ ∈ ⁅H₁, H₂⁆ := by
  have hle : ∀ {L : Subgroup G}, (∀ x ∈ L, g * x * g⁻¹ ∈ L) →
      L.map (MulAut.conj g).toMonoidHom ≤ L := by
    rintro L hL _ ⟨x, hx, rfl⟩
    exact hL x hx
  have hmem : g * z * g⁻¹ ∈ (⁅H₁, H₂⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom :=
    ⟨z, hz, rfl⟩
  rw [map_commutator] at hmem
  exact commutator_mono (hle h₁) (hle h₂) hmem

theorem commutator_le_of_perfect_mod {P A N K : Subgroup G} (hPK : P ≤ K) (hAK : A ≤ K)
    (hN : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hP : Group.IsPerfect P)
    (h : ⁅⁅P, A⁆, P⁆ ≤ N) : ⁅P, A⁆ ≤ N := by
  have : (N.subgroupOf K).Normal := ⟨fun n hn k => by
    rw [mem_subgroupOf] at hn ⊢
    exact hN k k.2 n hn⟩
  have hmap : ∀ {L : Subgroup G}, L ≤ K → (L.subgroupOf K).map K.subtype = L := fun hL => by
    rw [subgroupOf_map_subtype, inf_of_le_left hL]
  have hinj : Function.Injective fun L : Subgroup K => L.map K.subtype :=
    map_injective (subtype_injective K)
  let f := QuotientGroup.mk' (N.subgroupOf K)
  have hPK' : ⁅P.subgroupOf K, P.subgroupOf K⁆ = P.subgroupOf K := hinj (by
    change (⁅P.subgroupOf K, P.subgroupOf K⁆).map K.subtype = (P.subgroupOf K).map K.subtype
    rw [map_commutator, hmap hPK, isPerfect_iff.mp hP])
  have hPf : Group.IsPerfect ((P.subgroupOf K).map f) := by
    rw [isPerfect_iff, ← map_commutator, hPK']
  have h3 : ⁅⁅P.subgroupOf K, A.subgroupOf K⁆, P.subgroupOf K⁆ ≤ f.ker := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    rw [mem_subgroupOf]
    have hz' : (z : G) ∈ (⁅⁅P.subgroupOf K, A.subgroupOf K⁆, P.subgroupOf K⁆).map K.subtype :=
      ⟨z, hz, rfl⟩
    rw [map_commutator, map_commutator, hmap hPK, hmap hAK] at hz'
    exact h hz'
  have h4 : ⁅⁅(P.subgroupOf K).map f, (A.subgroupOf K).map f⁆, (P.subgroupOf K).map f⁆ = ⊥ := by
    rw [← map_commutator, ← map_commutator, Subgroup.map_eq_bot_iff]
    exact h3
  have h5 := CFSG.LocalCores.perfect_double_commutator hPf h4
  rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h5
  intro z hz
  rw [← hmap hPK, ← hmap hAK, ← map_commutator] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact mem_subgroupOf.mp (h5 hw)

theorem perfect_normalizer_centralization_through_irreducible_core_commutator {p : ℕ}
    (_hp : p.Prime) {H : Type*} [Group H] [Finite H] {X Y Q : Subgroup H}
    (hX : Group.IsPerfect X) (hY : Group.IsPerfect Y) (hYX : Y ≤ normalizer (X : Set H))
    (hQX : Q ≤ X) (hQn : (Q.subgroupOf X).Normal) (hYQ : Y ≤ normalizer (Q : Set H))
    (hU : IsElementaryAbelian p (⁅Q, X⁆ : Subgroup H)) (hUZ : ⁅Q, X⁆ ≤ (center Q).map Q.subtype)
    (hne : ¬ ⁅Q, X⁆ ≤ centralizer (X : Set H))
    (hirr : ∀ M : Subgroup H, ⁅Q, X⁆ ⊓ centralizer (X : Set H) ≤ M → M ≤ ⁅Q, X⁆ →
      (∀ x ∈ X, ∀ m ∈ M, x * m * x⁻¹ ∈ M) →
        M = ⁅Q, X⁆ ⊓ centralizer (X : Set H) ∨ M = ⁅Q, X⁆)
    (hXY : ⁅X, Y⁆ ≤ Q) : ⁅X, Y⁆ = ⊥ := by
  classical
  obtain ⟨U, hUdef⟩ : ∃ U, ⁅Q, X⁆ = U := ⟨_, rfl⟩
  rw [hUdef] at hU hUZ hne hirr
  have hQn' : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := fun x hx q hq => by
    have h := hQn.conj_mem ⟨q, hQX hq⟩ (mem_subgroupOf.mpr hq) ⟨x, hx⟩
    rw [mem_subgroupOf] at h
    exact h
  have hXX : ∀ x ∈ X, ∀ z ∈ X, x * z * x⁻¹ ∈ X := fun x hx z hz =>
    mul_mem (mul_mem hx hz) (inv_mem hx)
  have hYXc : ∀ y ∈ Y, ∀ z ∈ X, y * z * y⁻¹ ∈ X := fun y hy z hz =>
    (mem_normalizer_iff.mp (hYX hy) z).mp hz
  have hYQc : ∀ y ∈ Y, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := fun y hy q hq =>
    (mem_normalizer_iff.mp (hYQ hy) q).mp hq
  have hXU : ∀ x ∈ X, ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun x hx u hu => by
    rw [← hUdef] at hu ⊢
    exact conj_mem_commutator (hQn' x hx) (hXX x hx) hu
  have hYU : ∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ ∈ U := fun y hy u hu => by
    rw [← hUdef] at hu ⊢
    exact conj_mem_commutator (hYQc y hy) (hYXc y hy) hu
  have hUZ' : ∀ u ∈ U, ∀ q ∈ Q, u * q = q * u := by
    intro u hu q hq
    obtain ⟨c, hc, rfl⟩ := hUZ hu
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨q, hq⟩).symm
  have hUX : ⁅U, X⁆ = U := by
    have hWU : ⁅U, X⁆ ≤ U := by
      rw [commutator_le]
      intro u hu x hx
      rw [commutatorElement_def, mul_assoc u, mul_assoc u]
      exact mul_mem hu (hXU x hx _ (inv_mem hu))
    refine le_antisymm hWU ?_
    have h := commutator_le_of_perfect_mod (P := X) (A := Q) (N := ⁅U, X⁆) (K := X) le_rfl hQX
      (fun k hk n hn => conj_mem_commutator (hXU k hk) (hXX k hk) hn) hX
      (by rw [commutator_comm X Q, hUdef])
    rwa [commutator_comm X Q, hUdef] at h
  have hcomm : ∀ x ∈ X, ∀ y ∈ Y, ∀ u ∈ U,
      y * (x * u * x⁻¹) * y⁻¹ = x * (y * u * y⁻¹) * x⁻¹ := by
    intro x hx y hy u hu
    have hcv := hUZ' _ (hYU y hy _ (hXU x hx u hu)) _ (hXY (commutator_mem_commutator hx hy))
    have e : x * (y * u * y⁻¹) * x⁻¹ = ⁅x, y⁆ * (y * (x * u * x⁻¹) * y⁻¹) * ⁅x, y⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e, ← hcv, mul_inv_cancel_right]
  have hstep2 : ∀ u ∈ U, ∀ y ∈ Y, ⁅y, u⁆ ∈ centralizer (X : Set H) := by
    let _ : CommGroup U := { (inferInstance : Group U) with
      mul_comm := fun a b => hU.toIsMulCommutative.is_comm.comm a b }
    have hXN : X ≤ normalizer (U : Set H) := le_normalizer_of_conj_mem hXU
    have hYN : Y ≤ normalizer (U : Set H) := le_normalizer_of_conj_mem hYU
    let _ : MulDistribMulAction X U := MulDistribMulAction.compHom U (inclusion hXN)
    have hsmul : ∀ (x : X) (u : U), ((x • u : U) : H) = (x : H) * u * (x : H)⁻¹ :=
      fun _ _ => rfl
    have hfix : ∀ u : U,
        u ∈ XMod.fixed X (⊤ : Subgroup U) ↔ (u : H) ∈ centralizer (X : Set H) := by
      intro u
      rw [XMod.mem_fixed, mem_centralizer_iff]
      constructor
      · rintro ⟨-, h⟩ x hx
        have h1 : x * (u : H) * x⁻¹ = u := congrArg Subtype.val (h ⟨x, hx⟩)
        calc x * (u : H) = x * u * x⁻¹ * x := by group
          _ = u * x := by rw [h1]
      · intro h
        refine ⟨trivial, fun x => Subtype.ext ?_⟩
        rw [hsmul, h x x.2, mul_inv_cancel_right]
    have hirr' : XMod.IsIrrSec X (XMod.fixed X (⊤ : Subgroup U)) ⊤ := by
      refine ⟨lt_of_le_of_ne le_top fun h => hne fun u hu => ?_, fun J hJ hCJ _ => ?_⟩
      · have hu' : (⟨u, hu⟩ : U) ∈ XMod.fixed X (⊤ : Subgroup U) := by
          rw [h]
          exact mem_top _
        exact (hfix _).mp hu'
      · have hM := hirr (J.map U.subtype) (fun c hc => ⟨⟨c, hc.1⟩, hCJ ((hfix _).mpr hc.2), rfl⟩)
          (map_subtype_le J) (by
            rintro x hx _ ⟨j, hj, rfl⟩
            exact ⟨(⟨x, hx⟩ : X) • j, hJ ⟨x, hx⟩ j hj, rfl⟩)
        rcases hM with hM | hM
        · left
          refine le_antisymm (fun j hj => (hfix j).mpr ?_) hCJ
          have hj' : (j : H) ∈ J.map U.subtype := ⟨j, hj, rfl⟩
          rw [hM] at hj'
          exact hj'.2
        · right
          refine eq_top_iff.mpr fun u _ => ?_
          have hu : (u : H) ∈ J.map U.subtype := by
            rw [hM]
            exact u.2
          obtain ⟨j, hj, hju⟩ := hu
          rwa [Subtype.ext hju] at hj
    have hsimple := XMod.isIrrSec_quotient hirr'
    let β : Y →* MulAut U := U.normalizerMonoidHom.comp (inclusion hYN)
    have hβ : ∀ (y : Y) (u : U), ((β y u : U) : H) = (y : H) * u * (y : H)⁻¹ :=
      fun _ _ => rfl
    have hβeq : ∀ y, β y ∈ XMod.eqvAut X U := by
      intro y x u
      apply Subtype.ext
      rw [hβ, hsmul, hsmul, hβ]
      exact hcomm x x.2 y y.2 u u.2
    let β' := β.codRestrict _ hβeq
    let g : Y →* XMod.eqvAut X (U ⧸ XMod.fixed X (⊤ : Subgroup U)) :=
      { toFun := fun y => ⟨XMod.quotAut (β' y), fun a q => by
          refine QuotientGroup.induction_on q fun x => ?_
          rw [XMod.smul_quotMk, XMod.quotAut_mk, XMod.quotAut_mk, XMod.smul_quotMk]
          exact congrArg QuotientGroup.mk ((β' y).2 a x)⟩
        map_one' := Subtype.ext (MulEquiv.ext fun q => QuotientGroup.induction_on q fun x => by
          change XMod.quotAut (β' 1) (QuotientGroup.mk x) = QuotientGroup.mk x
          rw [XMod.quotAut_mk, map_one]
          rfl)
        map_mul' := fun y y' => Subtype.ext (MulEquiv.ext fun q =>
          QuotientGroup.induction_on q fun x => by
            change XMod.quotAut (β' (y * y')) (QuotientGroup.mk x) =
              XMod.quotAut (β' y) (XMod.quotAut (β' y') (QuotientGroup.mk x))
            rw [XMod.quotAut_mk, XMod.quotAut_mk, XMod.quotAut_mk, map_mul]
            rfl) }
    have hg : ∀ y, g y = 1 := by
      have : Group.IsPerfect Y := hY
      have : IsCyclic g.range := XMod.isCyclic_of_injective_eqvEnd hsimple
        ((XMod.toEqvEnd X _).comp g.range.subtype)
        (XMod.toEqvEnd_injective.comp (subtype_injective _))
      have : Group.IsPerfect g.range := Group.IsPerfect.range g
      have : Subsingleton g.range := Group.IsPerfect.subsingleton_of_isMulCommutative
      intro y
      exact congrArg Subtype.val (Subsingleton.elim (g.rangeRestrict y) 1)
    intro u hu y hy
    have h1 := congrArg (fun z : XMod.eqvAut X (U ⧸ XMod.fixed X (⊤ : Subgroup U)) =>
      z.1 (QuotientGroup.mk (⟨u⁻¹, inv_mem hu⟩ : U))) (hg ⟨y, hy⟩)
    change XMod.quotAut (β' ⟨y, hy⟩) (QuotientGroup.mk (⟨u⁻¹, inv_mem hu⟩ : U)) =
      QuotientGroup.mk (⟨u⁻¹, inv_mem hu⟩ : U) at h1
    rw [XMod.quotAut_mk, QuotientGroup.eq] at h1
    have h2 := (hfix _).mp h1
    have e : ((((β ⟨y, hy⟩ : MulAut U) (⟨u⁻¹, inv_mem hu⟩ : U))⁻¹ * ⟨u⁻¹, inv_mem hu⟩ : U) : H) =
        ⁅y, u⁆ := by
      change (y * u⁻¹ * y⁻¹)⁻¹ * u⁻¹ = ⁅y, u⁆
      rw [commutatorElement_def]
      group
    rw [← e]
    exact h2
  have hUY : ⁅U, Y⁆ = ⊥ := by
    have h1 : ⁅⁅U, Y⁆, X⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer, commutator_le]
      intro u hu y hy
      rw [← commutatorElement_inv]
      exact inv_mem (hstep2 u hu y hy)
    have h2 : ⁅⁅Y, X⁆, U⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer, commutator_comm]
      intro z hz
      rw [mem_centralizer_iff]
      intro u hu
      exact hUZ' u hu z (hXY hz)
    have h3 := commutator_commutator_eq_bot_of_rotate (H₁ := X) (H₂ := U) (H₃ := Y) h1 h2
    rwa [commutator_comm X U, hUX] at h3
  have hXYU : ⁅X, Y⁆ ≤ U := by
    have hKN : X ⊔ Y ≤ normalizer (U : Set H) :=
      sup_le (le_normalizer_of_conj_mem hXU) (le_normalizer_of_conj_mem hYU)
    refine commutator_le_of_perfect_mod (K := X ⊔ Y) le_sup_left le_sup_right
      (fun k hk n hn => (mem_normalizer_iff.mp (hKN hk) n).mp hn) hX ?_
    rw [← hUdef]
    exact commutator_mono hXY le_rfl
  have h5 : ⁅⁅Y, X⁆, Y⁆ = ⊥ := by
    rw [eq_bot_iff, ← hUY]
    exact commutator_mono (by rw [commutator_comm]; exact hXYU) le_rfl
  rw [commutator_comm]
  exact CFSG.LocalCores.perfect_double_commutator hY h5

end CFSG.Quasithin.SteinbergCC
