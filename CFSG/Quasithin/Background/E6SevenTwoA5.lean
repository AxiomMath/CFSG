module

public import CFSG.Quasithin.Background.E6TenBlock
public import CFSG.Quasithin.EmptyFaithful.ModFA5Blk
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCSplit
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC CFSG.QuasithinUnique.A5.Delta5
open Equiv

variable {G : Type} [Group G] [Finite G]

@[expose] def kleinGenA : Fin 5 → Perm (Fin 5) :=
  ![swap 1 2 * swap 3 4, swap 0 2 * swap 3 4, swap 0 1 * swap 3 4, swap 0 1 * swap 2 4,
    swap 0 1 * swap 2 3]

@[expose] def kleinGenB : Fin 5 → Perm (Fin 5) :=
  ![swap 1 3 * swap 2 4, swap 0 3 * swap 2 4, swap 0 3 * swap 1 4, swap 0 2 * swap 1 4,
    swap 0 2 * swap 1 3]

@[expose] def kleinFix (p : Fin 5) : Fin 5 → ZMod 2 := fun i => if i = p then 0 else 1

theorem kleinGen_props : ∀ p : Fin 5,
    (kleinGenA p * kleinGenA p = 1 ∧ Perm.sign (kleinGenA p) = 1 ∧ kleinGenA p p = p) ∧
      (kleinGenB p * kleinGenB p = 1 ∧ Perm.sign (kleinGenB p) = 1 ∧ kleinGenB p p = p) := by
  decide +kernel

theorem fix_kleinGen : ∀ p : Fin 5, ∀ v : Fin 5 → ZMod 2, isEven v →
    pact (kleinGenA p) v = v → pact (kleinGenB p) v = v → v = 0 ∨ v = kleinFix p := by
  decide +kernel

theorem kleinGenA_mem (p : Fin 5) : kleinGenA p ∈ ModF.klein p := by
  simp only [ModF.klein, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (kleinGen_props p).1

theorem kleinGenB_mem (p : Fin 5) : kleinGenB p ∈ ModF.klein p := by
  simp only [ModF.klein, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (kleinGen_props p).2

theorem isSylowTwoOf_inf_of_isBlock2 {K L Q : Subgroup G} (hQ : IsSylowTwoOf Q K)
    (hL : IsBlock2 K L) : IsSylowTwoOf (Q ⊓ L) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (Q.subgroupOf K) :=
    hQ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm
  set S : Sylow 2 K := hQ2.toSylow hQ.2.2 with hSdef
  have hS : (S : Subgroup K).map K.subtype = Q := by
    change (Q.subgroupOf K).map K.subtype = Q
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQ.1]
  obtain ⟨P', hP'⟩ := exists_sylow_map_eq_inf_of_subnormal S hL.2.2
  let e : (L.subgroupOf K) ≃* L := Subgroup.subgroupOfEquivOfLe hL.2.1
  have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  set P : Sylow 2 L := P'.mapSurjective he with hPdef
  have hPmap : (P : Subgroup L).map L.subtype = Q ⊓ L := by
    rw [hPdef, Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : L.subtype.comp e.toMonoidHom = K.subtype.comp (L.subgroupOf K).subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, hP', Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective, hS,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hL.2.1]
  rw [← hPmap]
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map L.subtype, ?_⟩
  change ¬ 2 ∣ (((P : Subgroup L).map L.subtype).comap L.subtype).index
  rw [Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  exact P.not_dvd_index

theorem relIndex_le_two_of_congr {V D : Subgroup G}
    (htwo : ∀ v₁ ∈ V, ∀ v₂ ∈ V, v₁ ∉ D → v₂ ∉ D → v₁⁻¹ * v₂ ∈ D) :
    (V ⊓ D).relIndex V ≤ 2 := by
  set C := V ⊓ D with hCdef
  by_cases hVC : V ≤ D
  · have hCV : C = V := inf_eq_left.2 hVC
    rw [hCV, Subgroup.relIndex_self]
    norm_num
  obtain ⟨v₀, hv₀, hv₀C⟩ := Set.not_subset.1 hVC
  have hsurj : Function.Surjective (fun p : Bool × ↥C =>
      (⟨if p.1 then v₀ * p.2 else p.2, by
        rcases p with ⟨b, x⟩
        cases b
        · exact x.2.1
        · exact V.mul_mem hv₀ x.2.1⟩ : ↥V)) := by
    rintro ⟨v, hv⟩
    by_cases hvC : v ∈ D
    · exact ⟨(false, ⟨v, hv, hvC⟩), rfl⟩
    · refine ⟨(true, ⟨v₀⁻¹ * v, V.mul_mem (V.inv_mem hv₀) hv, htwo v₀ hv₀ v hv hv₀C hvC⟩), ?_⟩
      apply Subtype.ext
      show v₀ * (v₀⁻¹ * v) = v
      group
  have hcard := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hcard
  have h1 := Subgroup.relIndex_mul_card C V
  rw [inf_eq_left.2 (inf_le_left : C ≤ V)] at h1
  have hpos : 0 < Nat.card C := Nat.card_pos
  have h2 : C.relIndex V * Nat.card C ≤ 2 * Nat.card C := by rw [h1]; exact hcard
  exact Nat.le_of_mul_le_mul_right h2 hpos

theorem comm_blockQ_of_alt5 {L : Subgroup G} (hL : IsShort2 L) (h5 : IsAltType L 5) {q n : G}
    (hqC : ∀ u ∈ blockU L, q * u = u * q) (hbb1 : ∀ ℓ ∈ L, q * ℓ * q⁻¹ * ℓ⁻¹ ∈ blockU L)
    (hn : n ∈ blockQ L) : q * n = n * q := by
  have hnL : n ∈ L := C1.blockQ_le L hn
  set e : G := q * n * q⁻¹ * n⁻¹ with he
  have heU : e ∈ blockU L := hbb1 n hnL
  have hcent : ∀ ℓ ∈ L, ℓ * e * ℓ⁻¹ = e := by
    intro ℓ hℓ
    set c : G := q * ℓ * q⁻¹ * ℓ⁻¹ with hc
    have hcU : c ∈ blockU L := hbb1 ℓ hℓ
    set m : G := ℓ * n * ℓ⁻¹ with hm
    have hmQ : m ∈ blockQ L := conj_mem_blockQ hℓ hn
    set w : G := ℓ * e * ℓ⁻¹ with hw
    have hwU : w ∈ blockU L := conj_mem_blockU hℓ heU
    set u₁ : G := ℓ * n * ℓ⁻¹ * n⁻¹ with hu₁
    have hu₁U : u₁ ∈ blockU L := C1.commutator_mem_blockU' hℓ hn
    have h1 : q * ℓ * q⁻¹ = c * ℓ := by rw [hc]; group
    have h2 : q * n * q⁻¹ = e * n := by rw [he]; group
    have hcw : c * w = w * c := blockU_comm_blockU hL hcU hwU
    have hcm : c * m = m * c := C1.blockU_comm hL c hcU m hmQ
    have h3 : q * m * q⁻¹ = w * m := by
      calc q * m * q⁻¹ = (q * ℓ * q⁻¹) * (q * n * q⁻¹) * (q * ℓ * q⁻¹)⁻¹ := by rw [hm]; group
        _ = (c * ℓ) * (e * n) * (c * ℓ)⁻¹ := by rw [h1, h2]
        _ = c * (ℓ * e * ℓ⁻¹) * (ℓ * n * ℓ⁻¹) * c⁻¹ := by group
        _ = c * w * m * c⁻¹ := rfl
        _ = w * m := by
          rw [hcw, mul_assoc w c m, hcm]; group
    have hmu : m = u₁ * n := by rw [hm, hu₁]; group
    have hq1 : q * u₁ * q⁻¹ = u₁ := by rw [hqC u₁ hu₁U]; group
    have h4 : q * m * q⁻¹ = u₁ * e * n := by
      calc q * m * q⁻¹ = (q * u₁ * q⁻¹) * (q * n * q⁻¹) := by rw [hmu]; group
        _ = u₁ * (e * n) := by rw [hq1, h2]
        _ = u₁ * e * n := by group
    have h5' : w * (u₁ * n) = u₁ * e * n := by rw [← hmu, ← h3, h4]
    have h6 : w * u₁ = u₁ * e := by
      have := h5'
      rw [← mul_assoc] at this
      exact mul_right_cancel this
    have hwu : w * u₁ = u₁ * w := blockU_comm_blockU hL hwU hu₁U
    rw [hwu] at h6
    exact mul_left_cancel h6
  have hZ : e ∈ blockZ L := ⟨heU, Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => by
    have := hcent ℓ hℓ
    calc ℓ * e = (ℓ * e * ℓ⁻¹) * ℓ := by group
      _ = e * ℓ := by rw [this]⟩
  have hZ1 : e = 1 := by
    have := hZ
    rw [blockZ_eq_bot_of_alt5 hL h5] at this
    exact this
  have : q * n * q⁻¹ * n⁻¹ = 1 := hZ1
  calc q * n = (q * n * q⁻¹ * n⁻¹) * (n * q) := by group
    _ = n * q := by rw [this, one_mul]

theorem exists_inner_of_alt5 {L : Subgroup G} (hL : IsShort2 L) (h5 : IsAltType L 5) {q : G}
    (hqC : ∀ u ∈ blockU L, q * u = u * q) (hbb1 : ∀ ℓ ∈ L, q * ℓ * q⁻¹ * ℓ⁻¹ ∈ blockU L) :
    ∃ u ∈ blockU L, ∀ ℓ ∈ L, q * ℓ * q⁻¹ = u * ℓ * u⁻¹ := by
  classical
  obtain ⟨P⟩ := nonempty_a5pi hL h5
  let cU : ↥L → ↥(blockU L) := fun γ => ⟨q * γ * q⁻¹ * (γ : G)⁻¹, hbb1 γ γ.2⟩
  let ρ : ↥L →* Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp P.α
  let W : ↥L → (Fin 5 → ZMod 2) := fun γ => (Multiplicative.toAdd (P.β (cU γ))).1
  have hcU_mul : ∀ a b : ↥L, cU (a * b) = cU a *
      ⟨(a : G) * (cU b : G) * (a : G)⁻¹, conj_mem_blockU a.2 (cU b).2⟩ := by
    intro a b
    apply Subtype.ext
    show q * ((a : G) * b) * q⁻¹ * ((a : G) * b)⁻¹ =
      (q * a * q⁻¹ * (a : G)⁻¹) * ((a : G) * (q * b * q⁻¹ * (b : G)⁻¹) * (a : G)⁻¹)
    group
  have hπρ : ∀ a : ↥L, P.π ⟨(a : G), Subgroup.le_normalizer a.2⟩ = ρ a := fun a =>
    P.hπα (a : G) a.2
  have hW : ∀ a b : ↥L, W (a * b) = W a + pact (ρ a) (W b) := by
    intro a b
    have h1 : P.β (cU (a * b)) = P.β (cU a) *
        P.β ⟨(a : G) * (cU b : G) * (a : G)⁻¹, conj_mem_blockU a.2 (cU b).2⟩ := by
      rw [hcU_mul, map_mul]
    have h2 := P.hcomp ⟨(a : G), Subgroup.le_normalizer a.2⟩ (cU b)
      ⟨(a : G) * (cU b : G) * (a : G)⁻¹, conj_mem_blockU a.2 (cU b).2⟩ rfl
    rw [hπρ a] at h2
    show (Multiplicative.toAdd (P.β (cU (a * b)))).1 =
      (Multiplicative.toAdd (P.β (cU a))).1 + pact (ρ a) (Multiplicative.toAdd (P.β (cU b))).1
    rw [h1, toAdd_mul, h2]
    rfl
  have hρ : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∃ γ, ρ γ = σ := by
    intro σ hσ
    obtain ⟨γ, hγ⟩ := P.hα (⟨σ, Equiv.Perm.mem_alternatingGroup.2 hσ⟩ : alternatingGroup (Fin 5))
    exact ⟨γ, by simp only [ρ, MonoidHom.comp_apply, hγ]; rfl⟩
  have hρev : ∀ γ, Perm.sign (ρ γ) = 1 := fun γ => Equiv.Perm.mem_alternatingGroup.1 (P.α γ).2
  have hker : ∀ k, ρ k = 1 → W k = 0 := by
    intro k hk
    have hαk : P.α k = 1 := Subtype.ext hk
    have hk' : k ∈ P.α.ker := hαk
    rw [P.hαk] at hk'
    have hkQ : (k : G) ∈ blockQ L := (mem_pCore_iff_mem_blockQ k).1 hk'
    have hcomm := comm_blockQ_of_alt5 hL h5 hqC hbb1 hkQ
    have hc1 : cU k = 1 := by
      apply Subtype.ext
      show q * (k : G) * q⁻¹ * (k : G)⁻¹ = 1
      rw [hcomm]; group
    show (Multiplicative.toAdd (P.β (cU k))).1 = 0
    rw [hc1, map_one]
    rfl
  obtain ⟨w₀, hw₀, hcob⟩ := cocycle_coboundary ρ hρ hρev W hW hker
  have hw₀' : w₀ ∈ evenWeight 5 := (mem_evenWeight_iff w₀).2 hw₀
  set u₀ : ↥(blockU L) := P.β.symm (Multiplicative.ofAdd ⟨w₀, hw₀'⟩) with hu₀
  have hβu₀ : P.β u₀ = Multiplicative.ofAdd ⟨w₀, hw₀'⟩ := by rw [hu₀]; simp
  refine ⟨(u₀ : G)⁻¹, (blockU L).inv_mem u₀.2, fun γ hγ => ?_⟩
  set g : ↥L := ⟨γ, hγ⟩ with hg
  have hvanish : u₀ * cU g * ⟨(g : G) * (u₀ : G) * (g : G)⁻¹, conj_mem_blockU hγ u₀.2⟩⁻¹ = 1 := by
    apply P.β.injective
    rw [map_mul, map_mul, map_inv, map_one]
    apply Multiplicative.toAdd.injective
    have h2 := P.hcomp ⟨(g : G), Subgroup.le_normalizer g.2⟩ u₀
      ⟨(g : G) * (u₀ : G) * (g : G)⁻¹, conj_mem_blockU hγ u₀.2⟩ rfl
    rw [hπρ g, hβu₀] at h2
    rw [toAdd_mul, toAdd_mul, toAdd_inv, h2, hβu₀]
    apply Subtype.ext
    funext i
    have hc := congrFun (hcob g) i
    simp only [Pi.add_apply] at hc
    show w₀ i + W g i + -(pact (ρ g) w₀ i) = 0
    rw [hc]
    generalize w₀ i = a
    generalize pact (ρ g) w₀ i = b
    revert a b
    decide
  have hX' : (u₀ : G) * (q * (γ : G) * q⁻¹ * (γ : G)⁻¹) *
      ((γ : G) * (u₀ : G) * (γ : G)⁻¹)⁻¹ = 1 := congrArg Subtype.val hvanish
  have h' : (u₀ : G) * q * γ * q⁻¹ * (u₀ : G)⁻¹ * (γ : G)⁻¹ = 1 := by
    rw [← hX']; group
  have h'' : (u₀ : G) * q * γ * q⁻¹ * (u₀ : G)⁻¹ = γ := mul_inv_eq_one.1 h'
  calc q * γ * q⁻¹ = (u₀ : G)⁻¹ * ((u₀ : G) * q * γ * q⁻¹ * (u₀ : G)⁻¹) * (u₀ : G) := by group
    _ = (u₀ : G)⁻¹ * γ * ((u₀ : G)⁻¹)⁻¹ := by rw [h'', inv_inv]

theorem relIndex_le_two_of_alt5 {K L Q V : Subgroup G} (hK : CharTwo K) (hL : IsBlock2 K L)
    (h5 : IsAltType L 5) (hQ : IsSylowTwoOf Q K) (hVQ : V ≤ Q)
    (hQV : Q ≤ Subgroup.centralizer (V : Set G)) :
    (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLs : IsShort2 L := hL.1
  obtain ⟨P⟩ := nonempty_a5pi hLs h5
  have hOQ : blockQ L ≤ Q :=
    (Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hL.2.1 hL.2.2).trans
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hQ)
  have hUQ : blockU L ≤ Q := (C1.blockU_le_blockQ hLs).trans hOQ
  have hTL : IsSylowTwoOf (Q ⊓ L) L := isSylowTwoOf_inf_of_isBlock2 hQ hL
  have hVc : ∀ v ∈ V, ∀ x ∈ Q, v * x = x * v := fun v hv x hx =>
    Subgroup.mem_centralizer_iff.1 (hQV hx) v hv
  have hVN : ∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G) := fun v hv =>
    mem_normalizer_of_commute_sylow hK hL hTL (hQ.1 (hVQ hv)) fun x hx => hVc v hv x hx.1
  have hbb1 : ∀ v ∈ V, ∀ ℓ ∈ L, v * ℓ * v⁻¹ * ℓ⁻¹ ∈ blockU L := by
    intro v hv
    refine C1.commutator_mem_blockU_of_mem_blockQ hLs fun ℓ hℓ => ?_
    have hπv : P.π ⟨v, hVN v hv⟩ = 1 := (P.hker _).2 fun u hu => by
      show v * u * v⁻¹ = u
      rw [hVc v hv u (hUQ hu), mul_inv_cancel_right]
    have hcL : v * ℓ * v⁻¹ * ℓ⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hVN v hv) ℓ).1 hℓ) (L.inv_mem hℓ)
    have hα1 : P.α ⟨_, hcL⟩ = 1 := by
      apply Subtype.ext
      rw [← P.hπα _ hcL]
      have e : (⟨v * ℓ * v⁻¹ * ℓ⁻¹, Subgroup.le_normalizer hcL⟩ :
          ↥(Subgroup.normalizer (L : Set G))) =
          ⟨v, hVN v hv⟩ * ⟨ℓ, Subgroup.le_normalizer hℓ⟩ * (⟨v, hVN v hv⟩)⁻¹ *
            (⟨ℓ, Subgroup.le_normalizer hℓ⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hπv]
      simp
    have hk : (⟨_, hcL⟩ : ↥L) ∈ CFSG.pCore 2 L := by rw [← P.hαk]; exact hα1
    exact (mem_pCore_iff_mem_blockQ _).1 hk
  have hinner : ∀ v ∈ V, ∃ u ∈ blockU L, ∀ ℓ ∈ L, v * ℓ * v⁻¹ = u * ℓ * u⁻¹ := fun v hv =>
    exists_inner_of_alt5 hLs h5 (fun u hu => hVc v hv u (hUQ hu)) (hbb1 v hv)
  have hkerQ : ∀ x : ↥L, P.α x = 1 → (x : G) ∈ Q := fun x hx => by
    have hk : x ∈ CFSG.pCore 2 L := by rw [← P.hαk]; exact hx
    exact hOQ ((mem_pCore_iff_mem_blockQ x).1 hk)
  obtain ⟨p, hp⟩ := ModF.exists_fixed (α := P.α) hTL
  have hgen : ∀ g ∈ ModF.klein p, ∃ t ∈ Q ⊓ L, ∃ htL : t ∈ L,
      ((P.α ⟨t, htL⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = g := by
    intro g hg
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 ((ModF.imgS_eq_klein P.hα hkerQ hTL hp g).2 hg)
    exact ⟨x, Subgroup.mem_subgroupOf.1 hx, x.2, hxg⟩
  have hfix : ∀ u : ↥(blockU L), (∀ t ∈ Q ⊓ L, t * u = u * t) →
      u = 1 ∨ (Multiplicative.toAdd (P.β u)).1 = kleinFix p := by
    intro u hu
    have hfixg : ∀ g ∈ ModF.klein p, pact g (Multiplicative.toAdd (P.β u)).1 =
        (Multiplicative.toAdd (P.β u)).1 := by
      intro g hg
      obtain ⟨t, htQL, htL, hαt⟩ := hgen g hg
      have h1 := P.hcomp ⟨t, Subgroup.le_normalizer htL⟩ u u
        (by rw [hu t htQL, mul_inv_cancel_right])
      rw [P.hπα t htL, hαt] at h1
      exact (congrArg Subtype.val h1).symm
    have hev : isEven (Multiplicative.toAdd (P.β u)).1 :=
      (mem_evenWeight_iff _).1 (Multiplicative.toAdd (P.β u)).2
    rcases fix_kleinGen p _ hev (hfixg _ (kleinGenA_mem p)) (hfixg _ (kleinGenB_mem p)) with
      h0 | h1
    · left
      apply P.β.injective
      rw [map_one]
      apply Multiplicative.toAdd.injective
      exact Subtype.ext h0
    · exact Or.inr h1
  refine relIndex_le_two_of_congr fun v₁ hv₁ v₂ hv₂ hn₁ hn₂ => ?_
  obtain ⟨a, ha, hal⟩ := hinner v₁ hv₁
  obtain ⟨b, hb, hbl⟩ := hinner v₂ hv₂
  have hcen : ∀ {w x : G}, w ∈ V → (∀ ℓ ∈ L, w * ℓ * w⁻¹ = x * ℓ * x⁻¹) →
      ∀ t ∈ Q ⊓ L, t * x = x * t := by
    intro w x hw hxl t ht
    have h1 := hxl t ht.2
    have h2 : w * t * w⁻¹ = t := by rw [hVc w hw t ht.1, mul_inv_cancel_right]
    rw [h2] at h1
    calc t * x = (x * t * x⁻¹) * x := by rw [← h1]
      _ = x * t := by group
  have hne1 : ∀ {w x : G}, w ∉ Subgroup.centralizer (L : Set G) →
      (∀ ℓ ∈ L, w * ℓ * w⁻¹ = x * ℓ * x⁻¹) → x ≠ 1 := by
    intro w x hw hxl hx1
    apply hw
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := hxl l hl
    rw [hx1] at this
    simp only [one_mul, inv_one, mul_one] at this
    calc l * w = (w * l * w⁻¹) * w := by rw [this]
      _ = w * l := by group
  rcases hfix ⟨a, ha⟩ (hcen hv₁ hal) with h | ha'
  · exact absurd (congrArg Subtype.val h) (hne1 hn₁ hal)
  rcases hfix ⟨b, hb⟩ (hcen hv₂ hbl) with h | hb'
  · exact absurd (congrArg Subtype.val h) (hne1 hn₂ hbl)
  have hab : a = b := by
    have h1 : P.β ⟨a, ha⟩ = P.β ⟨b, hb⟩ :=
      Multiplicative.toAdd.injective (Subtype.ext (ha'.trans hb'.symm))
    exact congrArg Subtype.val (P.β.injective h1)
  subst hab
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := hal l hl
  have h2 := hbl l hl
  calc l * (v₁⁻¹ * v₂) = v₁⁻¹ * (v₁ * l * v₁⁻¹) * v₂ := by group
    _ = v₁⁻¹ * (v₂ * l * v₂⁻¹) * v₂ := by rw [h1, h2]
    _ = v₁⁻¹ * v₂ * l := by group

end E6
end CFSG.Quasithin
