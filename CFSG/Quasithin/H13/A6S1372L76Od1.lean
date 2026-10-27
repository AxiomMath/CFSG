module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.A6S1372L76L
public import CFSG.Quasithin.H13.A6S13812
public import CFSG.Quasithin.H13.A6Set14

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace A6L76Od

variable {V : Type*} [CommGroup V]

theorem commV_le_commV_commV {Y : Subgroup (MulAut V)} (hY : Group.IsPerfect ↥Y) :
    commV Y ≤ Subgroup.closure {w | ∃ y ∈ Y, ∃ u ∈ commV Y, y u * u⁻¹ = w} := by
  set U := commV Y with hU
  set U₂ := Subgroup.closure {w | ∃ y ∈ Y, ∃ u ∈ commV Y, y u * u⁻¹ = w} with hU₂
  have hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U := fun y hy u hu => by
    have h1 : y u * u⁻¹ ∈ U := Subgroup.subset_closure ⟨y, hy, u, rfl⟩
    have e : y u = (y u * u⁻¹) * u := by group
    rw [e]
    exact U.mul_mem h1 hu
  have hU₂U : U₂ ≤ U := (Subgroup.closure_le _).2 fun w ⟨y, hy, u, hu, hw⟩ => by
    rw [← hw]
    exact U.mul_mem (hYU y hy u hu) (U.inv_mem hu)
  refine (Subgroup.closure_le _).2 ?_
  rintro w ⟨y₀, hy₀, v, rfl⟩
  let f : ↥Y →* ↥U ⧸ U₂.subgroupOf U :=
    { toFun := fun y => QuotientGroup.mk
        (⟨(y : MulAut V) v * v⁻¹, Subgroup.subset_closure ⟨y, y.2, v, rfl⟩⟩ : ↥U)
      map_one' := by
        rw [← QuotientGroup.mk_one]
        congr 1
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        have hg : (b : MulAut V) v * v⁻¹ ∈ U := Subgroup.subset_closure ⟨b, b.2, v, rfl⟩
        have hag : (a : MulAut V) ((b : MulAut V) v * v⁻¹) ∈ U := hYU a a.2 _ hg
        have e1 : (⟨((a * b : ↥Y) : MulAut V) v * v⁻¹, Subgroup.subset_closure
            ⟨a * b, (a * b).2, v, rfl⟩⟩ : ↥U) = ⟨(a : MulAut V) ((b : MulAut V) v * v⁻¹), hag⟩ *
              ⟨(a : MulAut V) v * v⁻¹, Subgroup.subset_closure ⟨a, a.2, v, rfl⟩⟩ :=
          Subtype.ext (by
            simp only [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
            group)
        have e2 : (QuotientGroup.mk ⟨(a : MulAut V) ((b : MulAut V) v * v⁻¹), hag⟩ :
            ↥U ⧸ U₂.subgroupOf U) = QuotientGroup.mk ⟨_, hg⟩ := by
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          have h1 := U₂.inv_mem (Subgroup.subset_closure ⟨a, a.2, _, hg, rfl⟩ :
            (a : MulAut V) ((b : MulAut V) v * v⁻¹) * ((b : MulAut V) v * v⁻¹)⁻¹ ∈ U₂)
          rw [mul_inv_rev, inv_inv, mul_comm] at h1
          simpa using h1
        show QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
        rw [e1, QuotientGroup.mk_mul, e2, mul_comm] }
  have hf : f ⟨y₀, hy₀⟩ = 1 := by
    have htop : commutator ↥Y = ⊤ := Group.isPerfect_def.1 hY
    have hle : commutator ↥Y ≤ f.ker := Abelianization.commutator_subset_ker f
    rw [htop] at hle
    exact hle (Subgroup.mem_top _)
  have h2 := (QuotientGroup.eq_one_iff _).1 hf
  rw [Subgroup.mem_subgroupOf] at h2
  exact h2

theorem fix_commV_of_trivial {Y : Subgroup (MulAut V)} (hY : Group.IsPerfect ↥Y) {a : MulAut V}
    (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) (haY' : ∀ y ∈ Y, a⁻¹ * y * a ∈ Y)
    (hfaith : ∀ y ∈ Y, (∀ u ∈ commV Y, y u * u⁻¹ ∈ fixV Y) → y = 1)
    (ha : ∀ u ∈ commV Y, a u * u⁻¹ ∈ fixV Y) :
    ∀ w : V, ∀ y ∈ Y, y (a w * w⁻¹) = a w * w⁻¹ := by
  set U := commV Y with hU
  have hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U := fun y hy u hu => by
    have h1 : y u * u⁻¹ ∈ U := Subgroup.subset_closure ⟨y, hy, u, rfl⟩
    have e : y u = (y u * u⁻¹) * u := by group
    rw [e]
    exact U.mul_mem h1 hu
  have hφU : ∀ φ : MulAut V, (∀ y ∈ Y, φ * y * φ⁻¹ ∈ Y) → ∀ u ∈ U, φ u ∈ U := by
    intro φ hφ u hu
    induction hu using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨y, hy, w, rfl⟩ := hg
      have e : φ (y w * w⁻¹) = (φ * y * φ⁻¹) (φ w) * (φ w)⁻¹ := by
        simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
          MulEquiv.symm_apply_apply]
      rw [e]
      exact Subgroup.subset_closure ⟨_, hφ y hy, φ w, rfl⟩
    | one => rw [map_one]; exact U.one_mem
    | mul g g' _ _ hg hg' => rw [map_mul]; exact U.mul_mem hg hg'
    | inv g _ hg => rw [map_inv]; exact U.inv_mem hg
  have haF : ∀ c ∈ fixV Y, a c ∈ fixV Y := fun c hc y hy => by
    have h1 : (a⁻¹ * y * a) c = c := hc _ (haY' y hy)
    calc y (a c) = a ((a⁻¹ * y * a) c) := by
          simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
      _ = a c := by rw [h1]
  have ha' : ∀ u ∈ U, a⁻¹ u * u⁻¹ ∈ fixV Y := fun u hu => by
    have hu' : a⁻¹ u ∈ U := hφU a⁻¹ (fun y hy => by simpa using haY' y hy) u hu
    have h1 := ha _ hu'
    have e : a (a⁻¹ u) = u := by simp [MulAut.inv_apply]
    rw [e] at h1
    have e2 : a⁻¹ u * u⁻¹ = (u * (a⁻¹ u)⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
    rw [e2]
    exact Subgroup.inv_mem _ h1
  have hcomm : ∀ y ∈ Y, a * y = y * a := by
    intro y hy
    have hy' : a * y * a⁻¹ * y⁻¹ ∈ Y := Y.mul_mem (haY y hy) (Y.inv_mem hy)
    have h1 : a * y * a⁻¹ * y⁻¹ = 1 := by
      refine hfaith _ hy' fun u hu => ?_
      have hu1 : y⁻¹ u ∈ U := hYU _ (Y.inv_mem hy) u hu
      have hc1 := ha' _ hu1
      have hc1y : y (a⁻¹ (y⁻¹ u) * (y⁻¹ u)⁻¹) = a⁻¹ (y⁻¹ u) * (y⁻¹ u)⁻¹ := hc1 y hy
      have hc2 := ha u hu
      have e : (a * y * a⁻¹ * y⁻¹) u * u⁻¹ =
          a (a⁻¹ (y⁻¹ u) * (y⁻¹ u)⁻¹) * (a u * u⁻¹) := by
        have e1 : (a * y * a⁻¹ * y⁻¹) u = a (y (a⁻¹ (y⁻¹ u))) := rfl
        have e2 : y (a⁻¹ (y⁻¹ u)) = (a⁻¹ (y⁻¹ u) * (y⁻¹ u)⁻¹) * u := by
          have e3 : a⁻¹ (y⁻¹ u) = (a⁻¹ (y⁻¹ u) * (y⁻¹ u)⁻¹) * y⁻¹ u := by group
          calc y (a⁻¹ (y⁻¹ u)) = y ((a⁻¹ (y⁻¹ u) * (y⁻¹ u)⁻¹) * y⁻¹ u) := congrArg y e3
            _ = (a⁻¹ (y⁻¹ u) * (y⁻¹ u)⁻¹) * u := by
              rw [map_mul, hc1y, MulAut.apply_inv_self]
        rw [e1, e2, map_mul]
        group
      rw [e]
      exact Subgroup.mul_mem _ (haF _ hc1) hc2
    calc a * y = (a * y * a⁻¹ * y⁻¹) * (y * a) := by group
      _ = y * a := by rw [h1, one_mul]
  have hfixU : ∀ u ∈ U, a u = u := by
    have hδ : ∀ g ∈ Subgroup.closure {w | ∃ y ∈ Y, ∃ u ∈ commV Y, y u * u⁻¹ = w}, a g = g := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem w hw =>
        obtain ⟨y, hy, u, hu, rfl⟩ := hw
        have hc := ha u hu
        have hcy : y (a u * u⁻¹) = a u * u⁻¹ := hc y hy
        have e1 : a (y u) = y (a u) := by
          rw [← MulAut.mul_apply, hcomm y hy, MulAut.mul_apply]
        have e2 : y (a u) = y (a u * u⁻¹) * y u := by rw [map_mul, map_inv]; group
        rw [map_mul, map_inv, e1, e2, hcy, mul_inv_eq_iff_eq_mul]
        ac_rfl
      | one => exact map_one a
      | mul g g' _ _ hg hg' => rw [map_mul, hg, hg']
      | inv g _ hg => rw [map_inv, hg]
    exact fun u hu => hδ u (commV_le_commV_commV hY hu)
  intro w y hy
  have hg : y w * w⁻¹ ∈ U := Subgroup.subset_closure ⟨y, hy, w, rfl⟩
  calc y (a w * w⁻¹) = y (a w) * (y w)⁻¹ := by rw [map_mul, map_inv]
    _ = a (y w) * (y w)⁻¹ := by rw [← MulAut.mul_apply, ← hcomm y hy, MulAut.mul_apply]
    _ = a w * w⁻¹ := by
      have e : y w = (y w * w⁻¹) * w := by group
      have h2 : a (y w) = (y w * w⁻¹) * a w := by
        calc a (y w) = a ((y w * w⁻¹) * w) := congrArg a e
          _ = (y w * w⁻¹) * a w := by rw [map_mul, hfixU _ hg]
      rw [h2, mul_inv_eq_iff_eq_mul]
      ac_rfl

end A6L76Od

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem V3_le_commutator_of_plus {X : Subgroup G} (P : S14.PlusData S X) :
    S.V3 ≤ ⁅S.V3, X⁆ := by
  intro x hx
  obtain ⟨hxV, hx3⟩ := S.mem_pre.1 hx
  obtain ⟨y, hy, y', hy', he⟩ := W3_commDec _ ⟨(S.frame.ψ ⟨x, hxV⟩).2, hx3⟩
  obtain ⟨g, hgX, hg⟩ := P.three (swap 0 1 * swap 1 2) (by decide +kernel)
  obtain ⟨g', hg'X, hg'⟩ := P.three (swap 1 2 * swap 2 3) (by decide +kernel)
  obtain ⟨v, hv⟩ := S.frame.ψ.surjective ⟨y, hy.1⟩
  obtain ⟨v', hv'⟩ := S.frame.ψ.surjective ⟨y', hy'.1⟩
  have hv3 : (v : G) ∈ S.V3 := S.mem_pre.2 ⟨v.2, by
    have e : S.frame.ψ ⟨(v : G), v.2⟩ = ⟨y, hy.1⟩ := hv
    rw [e]
    exact hy.2⟩
  have hv'3 : (v' : G) ∈ S.V3 := S.mem_pre.2 ⟨v'.2, by
    have e : S.frame.ψ ⟨(v' : G), v'.2⟩ = ⟨y', hy'.1⟩ := hv'
    rw [e]
    exact hy'.2⟩
  obtain ⟨h1, hψ1⟩ := S.psi_commutator v g
  obtain ⟨h2, hψ2⟩ := S.psi_commutator v' g'
  have hx_eq : x = ((v : G) * g * (v : G)⁻¹ * (g : G)⁻¹) *
      ((v' : G) * g' * (v' : G)⁻¹ * (g' : G)⁻¹) := by
    have : (⟨x, hxV⟩ : ↥V) = ⟨_, h1⟩ * ⟨_, h2⟩ := by
      apply S.frame.ψ.injective
      rw [map_mul, hψ1, hψ2, hg, hg', hv, hv']
      exact Subtype.ext he
    exact congrArg Subtype.val this
  rw [hx_eq]
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hv3 hgX)
    (Subgroup.commutator_mem_commutator hv'3 hg'X)

theorem le_centralizer_V3_of_mem_V1 {K : Subgroup G} (hKp : ⁅K, K⁆ = K) (hKG : K ≤ S.G1)
    (hK : ∀ v ∈ S.V3, ∀ k ∈ K, k * v * k⁻¹ * v⁻¹ ∈ fsuV1 T V) :
    K ≤ Subgroup.centralizer (S.V3 : Set G) := by
  intro k₀ hk₀
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hz : ∀ k ∈ K, ∀ c ∈ Subgroup.zpowers S.z, k * c = c * k := by
    intro k hk c hc
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    have h1 : k ∈ Subgroup.centralizer ({S.z} : Set G) := hKG hk
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    exact ((Commute.zpow_left h1.symm m).eq).symm
  have hK' : ∀ k ∈ K, k * v * k⁻¹ * v⁻¹ ∈ Subgroup.zpowers S.z := fun k hk => by
    rw [← S.V1_eq]
    exact hK v hv k hk
  let f : ↥K →* ↥(Subgroup.zpowers S.z) :=
    { toFun := fun k => ⟨(k : G) * v * (k : G)⁻¹ * v⁻¹, hK' k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := hK' b b.2
        have h1 : (a : G) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) * (a : G)⁻¹ =
            (b : G) * v * (b : G)⁻¹ * v⁻¹ := by
          rw [hz a a.2 _ hb, mul_inv_cancel_right]
        show ((a * b : ↥K) : G) * v * ((a * b : ↥K) : G)⁻¹ * v⁻¹ =
          ((a : G) * v * (a : G)⁻¹ * v⁻¹) * ((b : G) * v * (b : G)⁻¹ * v⁻¹)
        rw [Subgroup.coe_mul]
        calc (a : G) * b * v * ((a : G) * b)⁻¹ * v⁻¹
            = (a : G) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) * (a : G)⁻¹ *
                ((a : G) * v * (a : G)⁻¹ * v⁻¹) := by group
          _ = ((b : G) * v * (b : G)⁻¹ * v⁻¹) * ((a : G) * v * (a : G)⁻¹ * v⁻¹) := by rw [h1]
          _ = ((a : G) * v * (a : G)⁻¹ * v⁻¹) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) :=
            setLike_mul_comm hb (hK' a a.2) }
  have htop : commutator ↥K = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hKp)
  have hle : commutator ↥K ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [htop] at hle
  have h1 : f ⟨k₀, hk₀⟩ = 1 := hle (Subgroup.mem_top _)
  have h2 : k₀ * v * k₀⁻¹ * v⁻¹ = 1 := congrArg Subtype.val h1
  calc v * k₀ = (k₀ * v * k₀⁻¹ * v⁻¹)⁻¹ * (k₀ * v) := by group
    _ = k₀ * v := by rw [h2, inv_one, one_mul]

section Tilde

variable {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
  {K : Subgroup G} (hK : K ∈ cComp H)
  {Kt : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))}
  (hKt : Kt = autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
  {X : Subgroup G} (hXH : X ≤ H)
include hH hK hKt

theorem conj_mem_V1_of_trivial
    (hXn : ∀ x (hx : x ∈ X), ∀ y ∈ Kt, A6Mod.secAct (le_normalizer_conjClosure S.V3 H)
      (S.le_normalizer_UV1 hH) ⟨x, hXH hx⟩ * y * (A6Mod.secAct (le_normalizer_conjClosure S.V3 H)
        (S.le_normalizer_UV1 hH) ⟨x, hXH hx⟩)⁻¹ ∈ Kt)
    (hV3 : S.V3 ≤ ⁅S.V3, X⁆)
    (hfaith : ∀ y ∈ Kt, (∀ u ∈ commV Kt, y u * u⁻¹ ∈ fixV Kt) → y = 1)
    (hX : ∀ x (hx : x ∈ X), ∀ u ∈ commV Kt, A6Mod.secAct (le_normalizer_conjClosure S.V3 H)
      (S.le_normalizer_UV1 hH) ⟨x, hXH hx⟩ u * u⁻¹ ∈ fixV Kt) :
    ∀ v ∈ S.V3, ∀ k ∈ K, k * v * k⁻¹ * v⁻¹ ∈ fsuV1 T V := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  subst hKt
  have hcen : ∀ x (hx : x ∈ X), ∀ w, A6Mod.secAct hHU hHV ⟨x, hXH hx⟩ w * w⁻¹ ∈
      fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
    intro x hx w
    refine A6L76Od.fix_commV_of_trivial (S.isPerfect_tilde hH hK) (hXn x hx) (fun y hy => ?_)
      hfaith (hX x hx) w
    have e : (A6Mod.secAct hHU hHV ⟨x, hXH hx⟩)⁻¹ =
        A6Mod.secAct hHU hHV ⟨x⁻¹, hXH (X.inv_mem hx)⟩ := by
      rw [← map_inv]
      rfl
    have h1 := hXn x⁻¹ (X.inv_mem hx) y hy
    rw [← e, inv_inv] at h1
    exact h1
  have hF : ⁅S.V3, X⁆ ≤ ((fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))).comap
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))).map
          (conjClosure S.V3 H).subtype := by
    rw [Subgroup.commutator_le]
    intro v hv x hx
    have hvU : v ∈ conjClosure S.V3 H := le_conjClosure _ _ hv
    have hc : ⁅v, x⁆ ∈ conjClosure S.V3 H := by
      rw [commutatorElement_def, show v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) by group]
      exact (conjClosure S.V3 H).mul_mem hvU ((Subgroup.mem_normalizer_iff.mp
        (hHU (hXH hx)) _).mp ((conjClosure S.V3 H).inv_mem hvU))
    refine ⟨⟨_, hc⟩, ?_, rfl⟩
    show InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨_, hc⟩ ∈
      fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
    have e : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨_, hc⟩ =
        (A6Mod.secAct hHU hHV ⟨x, hXH hx⟩ (InternalSec.secMk _ ⟨v, hvU⟩) *
          (InternalSec.secMk _ ⟨v, hvU⟩)⁻¹)⁻¹ := by
      rw [A6Mod.secAct_secMk, ← map_inv, ← map_mul, ← map_inv]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_inv, Subgroup.coe_mul, Setup.rho_apply_coe, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.inv_mem _ (hcen x hx _)
  intro v hv k hk
  obtain ⟨u, hu, huv⟩ := hF (hV3 hv)
  have hu' : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u ∈
      fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := hu
  have huv' : (u : G) = v := huv
  subst huv'
  have hk' : A6Mod.secAct hHU hHV ⟨k, hKH hk⟩ ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :=
    (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨⟨k, hKH hk⟩, hk, rfl⟩
  have h1 : A6Mod.secAct hHU hHV ⟨k, hKH hk⟩
      (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
        InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u := hu' _ hk'
  have h2 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
      (Setup.rho (conjClosure S.V3 H) H hHU ⟨k, hKH hk⟩ u * u⁻¹) = 1 := by
    rw [map_mul, map_inv, ← A6Mod.secAct_secMk hHU hHV, h1, mul_inv_cancel]
  rw [A6Mod.secMk_eq_one_iff, Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] at h2
  exact h2

theorem false_of_trivial_on_UK (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15)
    (hXn : ∀ x (hx : x ∈ X), ∀ y ∈ Kt, A6Mod.secAct (le_normalizer_conjClosure S.V3 H)
      (S.le_normalizer_UV1 hH) ⟨x, hXH hx⟩ * y * (A6Mod.secAct (le_normalizer_conjClosure S.V3 H)
        (S.le_normalizer_UV1 hH) ⟨x, hXH hx⟩)⁻¹ ∈ Kt)
    (hV3 : S.V3 ≤ ⁅S.V3, X⁆)
    (hfaith : ∀ y ∈ Kt, (∀ u ∈ commV Kt, y u * u⁻¹ ∈ fixV Kt) → y = 1)
    (hX : ∀ x (hx : x ∈ X), ∀ u ∈ commV Kt, A6Mod.secAct (le_normalizer_conjClosure S.V3 H)
      (S.le_normalizer_UV1 hH) ⟨x, hXH hx⟩ u * u⁻¹ ∈ fixV Kt) : False := by
  have hKG : K ≤ S.G1 := (le_of_mem_cComp hK).trans hH.2.1
  have hKC := le_centralizer_V3_of_mem_V1 (perfect_of_mem_cComp hK) hKG
    (conj_mem_V1_of_trivial hH hK hKt hXH hXn hV3 hfaith hX)
  exact (S.lem13812_one h139 h37 h38 hH hK).1
    (hKC.trans ((S.centralizer_V3_le h13315).trans S.NV_le_M))

end Tilde

end Setting4

end CFSG.Quasithin.H13.A6
