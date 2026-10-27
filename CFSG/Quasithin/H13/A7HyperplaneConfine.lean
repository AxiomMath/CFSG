module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Quasithin.H13.A7SharedSolvableOvergroup

public section

namespace CFSG.Quasithin.H13.A7

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem mem_conjugate_iff_mem {V : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate V g ↔ g * x * g⁻¹ ∈ V := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    have e : g * (MulAut.conj g⁻¹).toMonoidHom v * g⁻¹ = v := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hv
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem conjugate_conjugate_eq_conjugate_mul (V : Subgroup G) (g h : G) :
    CFSG.conjugate (CFSG.conjugate V g) h = CFSG.conjugate V (g * h) := by
  ext x
  rw [mem_conjugate_iff_mem, mem_conjugate_iff_mem, mem_conjugate_iff_mem]
  constructor <;> intro hx <;> convert hx using 1 <;> group

theorem relIndex_conjugate_conjugate (B C : Subgroup G) (h : G) :
    (CFSG.conjugate B h).relIndex (CFSG.conjugate C h) = B.relIndex C :=
  relIndex_map_map_of_injective _ _ (MulAut.conj h⁻¹).injective

theorem mem_normalizer_conjugateJoin {V T : Subgroup G} {h : G}
    (hh : ∀ g, CFSG.conjugate V g ≤ T →
      CFSG.conjugate V (g * h) ≤ T ∧ CFSG.conjugate V (g * h⁻¹) ≤ T) :
    h ∈ normalizer ((⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g :
      Subgroup G) : Set G) := by
  set W : Subgroup G := ⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g with hW
  have key : ∀ k : G, (∀ g, CFSG.conjugate V g ≤ T → CFSG.conjugate V (g * k) ≤ T) →
      ∀ x ∈ W, k⁻¹ * x * k ∈ W := by
    intro k hk x hx
    have hle : W ≤ W.comap (MulAut.conj k⁻¹).toMonoidHom := by
      refine iSup₂_le fun g hg => ?_
      rw [← map_le_iff_le_comap]
      show CFSG.conjugate (CFSG.conjugate V g) k ≤ W
      rw [conjugate_conjugate_eq_conjugate_mul]
      exact le_iSup₂_of_le (f := fun g (_ : CFSG.conjugate V g ≤ T) => CFSG.conjugate V g)
        (g * k) (hk g hg) le_rfl
    have h1 := hle hx
    rw [mem_comap] at h1
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h1
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    simpa only [inv_inv] using key h⁻¹ (fun g hg => (hh g hg).2) x hx
  · intro hx
    have h1 := key h (fun g hg => (hh g hg).1) _ hx
    rwa [show h⁻¹ * (h * x * h⁻¹) * h = x by group] at h1

theorem mem_normalizer_conjugateJoin_of {V T N : Subgroup G} {h : G} (hNT : N ≤ T)
    (hVN : ∀ g, CFSG.conjugate V g ≤ T → CFSG.conjugate V g ≤ N)
    (hh : h ∈ normalizer (N : Set G)) :
    h ∈ normalizer ((⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g :
      Subgroup G) : Set G) := by
  have hconj : ∀ k ∈ normalizer (N : Set G), ∀ g, CFSG.conjugate V g ≤ T →
      CFSG.conjugate V (g * k) ≤ T := by
    intro k hk g hg x hx
    rw [← conjugate_conjugate_eq_conjugate_mul, mem_conjugate_iff_mem] at hx
    have h1 := hVN g hg hx
    have h2 := (mem_normalizer_iff.1 (inv_mem hk) (k * x * k⁻¹)).1 h1
    rw [show k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x by group] at h2
    exact hNT h2
  exact mem_normalizer_conjugateJoin fun g hg =>
    ⟨hconj h hh g hg, hconj h⁻¹ (inv_mem hh) g hg⟩

theorem A7_hyperplane_conjugates_confine_solvable_Sylow_overgroups [Finite G] (T : Sylow 2 G)
    {V : Subgroup G} (_hV1 : V ≠ ⊥) (_hVT : V ≤ T) (hV : IsElementaryAbelian 2 V)
    {M : Subgroup G}
    (hWM : normalizer ((⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g :
      Subgroup G) : Set G) ≤ M)
    (hCM : centralizer (V : Set G) ≤ M)
    (hhyp : ∀ (g : G) (B : Subgroup G), B ≤ CFSG.conjugate V g ⊓ T →
      B.relIndex (CFSG.conjugate V g) ≤ 2 → ⁅V, CFSG.conjugate V g⁆ = ⊥)
    (H₀ : Subgroup G) (hTH₀ : (T : Subgroup G) ≤ H₀) (hH₀ : Group.IsSolvable H₀) : H₀ ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : (T : Subgroup G) ≤ M := fun t ht =>
    hWM (mem_normalizer_conjugateJoin_of le_rfl (fun _ hg => hg) (le_normalizer ht))
  by_contra hbad
  set bad : Set (Subgroup G) :=
    {H | (T : Subgroup G) ≤ H ∧ Group.IsSolvable H ∧ ¬ H ≤ M} with hbaddef
  obtain ⟨H, hHmin⟩ := (Set.toFinite bad).exists_minimal ⟨H₀, hTH₀, hH₀, hbad⟩
  obtain ⟨hTH, hHs, hHM⟩ := hHmin.1
  have hsmall : ∀ K : Subgroup G, (T : Subgroup G) ≤ K → K < H → K ≤ M := by
    intro K hTK hKH
    by_contra hKM
    have hKs : Group.IsSolvable K :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKH.le)
        (Subgroup.inclusion_injective hKH.le)
    exact hKH.not_ge (hHmin.2 ⟨hTK, hKs, hKM⟩ hKH.le)
  set TH : Sylow 2 H := T.subtype hTH with hTHdef
  have hTHcoe : (TH : Subgroup H) = (T : Subgroup G).subgroupOf H := rfl
  set X : Subgroup H := M.subgroupOf H with hXdef
  have hXtop : X ≠ ⊤ := fun h => hHM (subgroupOf_eq_top.1 h)
  have hTX : (TH : Subgroup H) ≤ X := by
    rw [hTHcoe]
    intro t ht
    exact hTM ht
  have hle : ∀ Y : Subgroup H, (TH : Subgroup H) ≤ Y → Y ≠ ⊤ → Y ≤ X := by
    intro Y hTY hY y hy
    have hTY' : (T : Subgroup G) ≤ Y.map H.subtype := by
      intro t ht
      exact ⟨⟨t, hTH ht⟩, hTY (by rw [hTHcoe, mem_subgroupOf]; exact ht), rfl⟩
    have hYH : Y.map H.subtype < H := by
      refine lt_of_le_of_ne (map_subtype_le Y) fun h => hY ?_
      rw [eq_top_iff]
      intro z _
      have : (z : G) ∈ Y.map H.subtype := by rw [h]; exact z.2
      obtain ⟨w, hw, hwz⟩ := this
      rwa [show w = z from Subtype.ext hwz] at hw
    exact hsmall _ hTY' hYH ⟨y, hy, rfl⟩
  have hcoatom : IsCoatom X := by
    refine ⟨hXtop, fun Y hXY => ?_⟩
    by_contra hY
    exact hXY.not_ge (hle Y (hTX.trans hXY.le) hY)
  have huniq : ∀ Y : Subgroup H, IsCoatom Y → (TH : Subgroup H) ≤ Y → Y = X := fun Y hY hTY =>
    ((hY.le_iff.1 (hle Y hTY hY.1)).resolve_left hXtop).symm
  have hTn : ¬ (TH : Subgroup H).Normal := by
    intro hn
    apply hHM
    intro h hh
    apply hWM
    refine mem_normalizer_conjugateJoin_of le_rfl (fun _ hg => hg) ?_
    exact (normal_subgroupOf_iff_le_normalizer hTH).1 (hTHcoe ▸ hn) hh
  obtain ⟨p, hp, hp2, P, -, hPn, hPp, -, hPSbot, -, hfaith, -, hXbar, -⟩ :=
    A7_solvable_unique_Sylow_overgroup_structure hHs TH hTn hcoatom hTX huniq
  set R := CFSG.pCore 2 H with hRdef
  set π := QuotientGroup.mk' R with hπ
  set S := (TH : Subgroup H).map π with hS
  set Φ := (frattini P).map P.subtype with hΦ
  have hRT : R ≤ (TH : Subgroup H) := CFSG.pCore_isPGroup.le_sylow_of_normal TH
  obtain ⟨g, hgT, hgR⟩ : ∃ g : G, CFSG.conjugate V g ≤ T ∧
      ¬ CFSG.conjugate V g ≤ R.map H.subtype := by
    by_contra hcon
    push Not at hcon
    apply hHM
    intro h hh
    apply hWM
    refine mem_normalizer_conjugateJoin_of ?_ hcon ?_
    · rintro _ ⟨y, hy, rfl⟩
      have h1 := hRT hy
      rw [hTHcoe, mem_subgroupOf] at h1
      exact h1
    · have hn : ((R.map H.subtype).subgroupOf H).Normal := by
        rw [show (R.map H.subtype).subgroupOf H = R from
          comap_map_eq_self_of_injective H.subtype_injective R]
        infer_instance
      exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le R)).1 hn hh
  set A := CFSG.conjugate V g with hAdef
  have hAH : A ≤ H := hgT.trans hTH
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hV.toIsMulCommutative.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    have := hV
    exact elemPow_eq_one_of_isElementaryAbelian v hv
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hVcomm v hv w hw]
  have hA2 : ∀ x ∈ A, x ^ 2 = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_pow, hV2 v hv, map_one]
  set Abar : Subgroup (H ⧸ R) := (A.subgroupOf H).map π with hAbardef
  have hAbarS : Abar ≤ S := by
    rw [hS, hTHcoe]
    exact map_mono fun x hx => hgT hx
  have hAbar1 : Abar ≠ ⊥ := by
    intro h
    apply hgR
    intro x hx
    have hx' : (⟨x, hAH hx⟩ : H) ∈ A.subgroupOf H := hx
    have h1 : π ⟨x, hAH hx⟩ ∈ Abar := mem_map_of_mem π hx'
    rw [h, mem_bot] at h1
    have hker : (⟨x, hAH hx⟩ : H) ∈ R := by
      rwa [← QuotientGroup.ker_mk' R, MonoidHom.mem_ker]
    exact ⟨_, hker, rfl⟩
  have hAbarEA : IsElementaryAbelian 2 Abar :=
    { toIsMulCommutative := ⟨⟨fun a b => by
        obtain ⟨x, hx, hxa⟩ := mem_map.1 a.2
        obtain ⟨y, hy, hyb⟩ := mem_map.1 b.2
        apply Subtype.ext
        rw [coe_mul, coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul,
          show x * y = y * x from Subtype.ext (hAcomm _ hx _ hy)]⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        obtain ⟨x, hx, hxa⟩ := mem_map.1 a.2
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, ← hxa, ← map_pow,
          show x ^ 2 = 1 from Subtype.ext (by simpa using hA2 _ hx), map_one]
        rfl }
  have := hAbarEA
  have : Nontrivial Abar := (nontrivial_iff_ne_bot Abar).2 hAbar1
  have hPodd : ¬ 2 ∣ Nat.card P := by
    intro h2
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hPp
    rw [hk] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have := hPn
  let : MulDistribMulAction Abar P :=
    MulDistribMulAction.compHom P ((MulAut.conjNormal (H := P)).comp Abar.subtype)
  have hsmul : ∀ (a : Abar) (x : P),
      ((a • x : P) : H ⧸ R) = (a : H ⧸ R) * x * (a : H ⧸ R)⁻¹ :=
    fun a x => MulAut.conjNormal_apply (a : H ⧸ R) x
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := Abar) (H := P)
    hPodd
  obtain ⟨B, hB2, q, hq, a, hqa⟩ : ∃ B : Subgroup Abar, B.index = 2 ∧
      ∃ q ∈ fixedPointSubgroup B P, ∃ a : Abar, (a • q) * q⁻¹ ∉ frattini P := by
    by_contra hcon
    push Not at hcon
    have hΦn : (frattini P).Normal := inferInstance
    let C : Subgroup P :=
      { carrier := {x | ∀ a : Abar, (a • x) * x⁻¹ ∈ frattini P}
        mul_mem' := fun {x y} hx hy a => by
          have e : (a • (x * y)) * (x * y)⁻¹ =
              ((a • x) * x⁻¹) * (x * ((a • y) * y⁻¹) * x⁻¹) := by
            rw [smul_mul']
            group
          rw [e]
          exact mul_mem (hx a) (hΦn.conj_mem _ (hy a) x)
        one_mem' := fun a => by simp
        inv_mem' := fun {x} hx a => by
          have e : (a • x⁻¹) * x⁻¹⁻¹ = x⁻¹ * ((a • x) * x⁻¹)⁻¹ * x⁻¹⁻¹ := by
            rw [smul_inv']
            group
          rw [e]
          exact hΦn.conj_mem _ (inv_mem (hx a)) x⁻¹ }
    have hC : (⊤ : Subgroup P) ≤ C := by
      rw [← hgen]
      exact iSup₂_le fun B hB q hq a => hcon B hB q hq a
    apply hAbar1
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    refine hfaith y (hAbarS hy) fun x hx => ?_
    have h1 := hC (mem_top ⟨x, hx⟩) ⟨y, hy⟩
    refine mem_map.2 ⟨_, h1, ?_⟩
    rw [Subgroup.subtype_apply, Subgroup.coe_mul, hsmul, Subgroup.coe_inv]
  obtain ⟨a₀, ha₀, ha₀a⟩ := mem_map.1 a.2
  obtain ⟨j, hj⟩ := QuotientGroup.mk'_surjective R (q : H ⧸ R)
  have ha₀A : (a₀ : G) ∈ A := ha₀
  set K : Subgroup H := (B.map Abar.subtype).comap π with hKdef
  set B₀ : Subgroup G := A ⊓ K.map H.subtype with hB₀def
  have hconjT : CFSG.conjugate B₀ (j : G)⁻¹ ≤ T := by
    intro x hx
    rw [mem_conjugate_iff_mem, inv_inv] at hx
    obtain ⟨hxA, y, hyK, hyx⟩ := mem_inf.1 hx
    obtain ⟨β, hβB, hβ⟩ := mem_map.1 (mem_comap.1 hyK)
    have hqβ : (q : H ⧸ R) * β * (q : H ⧸ R)⁻¹ = β := by
      have h1 : ((⟨β, hβB⟩ : B) • q : P) = q := hq ⟨β, hβB⟩
      have h2 : ((β • q : P) : H ⧸ R) = q := congrArg Subtype.val h1
      rw [hsmul] at h2
      calc (q : H ⧸ R) * β * (q : H ⧸ R)⁻¹
          = (β : H ⧸ R) * q * (β : H ⧸ R)⁻¹ * β * (q : H ⧸ R)⁻¹ := by rw [h2]
        _ = β := by group
    have hy : π (j * y * j⁻¹) = π y := by
      rw [map_mul, map_mul, map_inv, hj, ← hβ]
      exact hqβ
    have hyx' : (y : G) = (j : G)⁻¹ * x * j := hyx
    have hyT : y ∈ (TH : Subgroup H) := by
      rw [hTHcoe, mem_subgroupOf, hyx']
      exact hgT hxA
    have hjyT : j * y * j⁻¹ ∈ (TH : Subgroup H) := by
      have h1 : (j * y * j⁻¹)⁻¹ * y ∈ R := by
        rw [← QuotientGroup.ker_mk' R, MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
      have h2 := mul_mem hyT (inv_mem (hRT h1))
      rwa [show y * ((j * y * j⁻¹)⁻¹ * y)⁻¹ = j * y * j⁻¹ by group] at h2
    rw [hTHcoe, mem_subgroupOf] at hjyT
    have hxe : ((j * y * j⁻¹ : H) : G) = x := by
      rw [coe_mul, coe_mul, coe_inv, hyx']
      group
    rwa [hxe] at hjyT
  have hconjA : CFSG.conjugate B₀ (j : G)⁻¹ ≤ CFSG.conjugate V (g * (j : G)⁻¹) := by
    rw [← conjugate_conjugate_eq_conjugate_mul]
    exact map_mono inf_le_left
  have hindex :
      (CFSG.conjugate B₀ (j : G)⁻¹).relIndex (CFSG.conjugate V (g * (j : G)⁻¹)) ≤ 2 := by
    rw [← conjugate_conjugate_eq_conjugate_mul, relIndex_conjugate_conjugate, hB₀def,
      inf_relIndex_left, ← relIndex_subgroupOf hAH,
      show (K.map H.subtype).subgroupOf H = K from
        comap_map_eq_self_of_injective H.subtype_injective K,
      hKdef, relIndex_comap, ← hAbardef]
    rw [Subgroup.relIndex, show (B.map Abar.subtype).subgroupOf Abar = B from
      comap_map_eq_self_of_injective Abar.subtype_injective B, hB2]
  have hcomm := hhyp (g * (j : G)⁻¹) _ (le_inf hconjA hconjT) hindex
  have hconjM : CFSG.conjugate V (g * (j : G)⁻¹) ≤ M := by
    intro y hy
    apply hCM
    rw [mem_centralizer_iff]
    intro v hv
    have h1 := commutator_mem_commutator hv hy
    rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  set x : H := a₀ * j * a₀⁻¹ * j⁻¹ with hxdef
  have hxM : x ∈ X := by
    rw [hXdef, mem_subgroupOf]
    have h1 : (j : G) * (a₀ : G)⁻¹ * (j : G)⁻¹ ∈ CFSG.conjugate V (g * (j : G)⁻¹) := by
      rw [← conjugate_conjugate_eq_conjugate_mul, mem_conjugate_iff_mem, inv_inv]
      rw [show (j : G)⁻¹ * ((j : G) * (a₀ : G)⁻¹ * (j : G)⁻¹) * (j : G) = (a₀ : G)⁻¹ by group]
      exact inv_mem ha₀A
    have h2 := mul_mem (hTM (hgT ha₀A)) (hconjM h1)
    rw [show (x : G) = (a₀ : G) * ((j : G) * (a₀ : G)⁻¹ * (j : G)⁻¹) by
      rw [hxdef]; simp only [coe_mul, coe_inv]; group]
    exact h2
  have hπx : π x = (a : H ⧸ R) * q * (a : H ⧸ R)⁻¹ * (q : H ⧸ R)⁻¹ := by
    rw [hxdef, map_mul, map_mul, map_mul, map_inv, map_inv, hj, ha₀a]
  have hπxP : π x ∈ P := by
    rw [hπx]
    exact mul_mem (hPn.conj_mem _ q.2 _) (inv_mem q.2)
  have hπxΦ : π x ∈ Φ := by
    have hΦn : Φ.Normal := normal_map_frattini
    have h1 : π x ∈ ((Φ ⊔ S : Subgroup (H ⧸ R)) : Set (H ⧸ R)) := by
      rw [← hXbar]
      exact mem_map_of_mem π hxM
    rw [normal_mul] at h1
    obtain ⟨f, hf, s, hs, hfs⟩ := h1
    have hfs' : f * s = π x := hfs
    have hfP : f ∈ P := map_subtype_le _ hf
    have hsP : s ∈ P := by
      have h2 := mul_mem (inv_mem hfP) hπxP
      rwa [← hfs', inv_mul_cancel_left] at h2
    have hs1 : s = 1 := by
      have h2 : s ∈ P ⊓ S := mem_inf.2 ⟨hsP, hs⟩
      rwa [hPSbot, mem_bot] at h2
    rw [← hfs', hs1, mul_one]
    exact hf
  obtain ⟨z, hz, hzx⟩ := mem_map.1 hπxΦ
  apply hqa
  have hze : (a • q) * q⁻¹ = z := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hsmul, Subgroup.coe_inv, ← hπx]
    exact hzx.symm
  rw [hze]
  exact hz

end CFSG.Quasithin.H13.A7
