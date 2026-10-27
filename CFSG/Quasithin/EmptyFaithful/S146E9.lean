module

public import CFSG.Quasithin.EmptyFaithful.S146E7
public import CFSG.Quasithin.EmptyFaithful.S146E8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section YOne

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.card_rhoImage (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) :
    Nat.card (((T ⊓ K).subgroupOf K).map c.hSec.rho) = 8 := by
  have hKS : IsSylowTwoOf (T ⊓ K) K := S.isSylowTwoOf_inf c.hKc
  have hOT : pCoreOf 2 K ≤ T ⊓ K := S.pCoreOf_le_inf c.hKc
  set D : Subgroup ↥K := (T ⊓ K).subgroupOf K with hD
  have hsurj : Function.Surjective c.hSec.rho := fun σ =>
    c.hSec.exists_rho_eq c.hsimple c.hQ' c.h168 σ
  have hker : c.hSec.rho.ker ≤ D := by
    intro k hk
    have h1 := c.hSec.mem_centralizerMod_of_rho_eq_one (MonoidHom.mem_ker.mp hk)
    exact Subgroup.mem_subgroupOf.mpr (hOT (c.hSec.centralizerMod_le c.hsimple c.hQ' h1))
  have hidx : (D.map c.hSec.rho).index = D.index := Subgroup.index_map_eq D hsurj hker
  have hodd : ¬ 2 ∣ (D.map c.hSec.rho).index := by
    rw [hidx]
    exact hKS.2.2
  have hp : IsPGroup 2 (D.map c.hSec.rho) := (hKS.2.1.comap_subtype (K := K)).map _
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hel := c.hSec.isElemAbelian_tilde
  have hcard : Nat.card (MulAut ↥(tildeOf Zz U₁)) = 168 :=
    card_mulAut_of_card_eight (fun a b => Subtype.ext (isElemAbelian_comm hel a.2 b.2))
      (fun a => Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel a.2))
      c.hSec.card_tilde
  have hmul := Subgroup.card_mul_index (D.map c.hSec.rho)
  rw [hn, hcard] at hmul
  rw [hn]
  exact two_pow_eq_eight_of (Or.inl rfl) hmul hodd

theorem FCtx.inv_mul_mem_of_decomp (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {v : G}
    (hv : v ∈ VZ T M) (hvZ : v ∉ Zz) {y₁ r : G} (hy₁ : y₁ ∈ U₁) (hr : r ∈ uxOf T M U₂)
    (hvyr : v = y₁ * r) : u⁻¹ * y₁ ∈ Zz := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hZX : Zz ≤ uxOf T M U₂ := c.hZU₂.trans le_sup_left
  have hUXU : uxOf T M U₂ ≤ uOfL22 T M := sup_le c.hU₂U (cuOf_le T M)
  have hUZ : U₁ ≤ Subgroup.normalizer (Zz : Set G) := c.hSec.norm
  have hy₁Z : y₁ ∉ Zz := by
    intro hz
    have hvX : v ∈ uxOf T M U₂ := by
      rw [hvyr]
      exact (uxOf T M U₂).mul_mem (hZX hz) hr
    have hU := c.uOfL22_le_uxOf_of_mem S hv hvZ hvX
    exact c.huZ (c.inf_uxOf_le S ⟨c.huU, hU (c.hU₁U c.huU)⟩)
  have hT₀ : ∀ t ∈ tZero T u, t * y₁ * t⁻¹ * y₁⁻¹ ∈ Zz := by
    intro t ht
    have htT : t ∈ T := ht.1
    have htH₂ : t ∈ centralizerMod Zz (mcOf T) (Subgroup.zpowers u) :=
      centralizerMod_mono_left _ hTH ht
    have htU₁ : t ∈ Subgroup.normalizer (U₁ : Set G) :=
      c.hSec.mem_normalizer_of_mem_centralizerMod c.hKn c.huU c.huZ htH₂
    have htUX : t ∈ Subgroup.normalizer ((uxOf T M U₂ : Subgroup G) : Set G) :=
      c.mem_normalizer_of_mem S (c.le_normalizer_uxOf S) hZX hUXU (hTH htT) htU₁
    have hz : t * v * t⁻¹ * v⁻¹ ∈ Zz := S.commutator_VZ_mem (hTM htT) (hTH htT) hv
    have hα : t * y₁ * t⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp htU₁ y₁).mp hy₁
    have hρ : t * r * t⁻¹ ∈ uxOf T M U₂ := (Subgroup.mem_normalizer_iff.mp htUX r).mp hr
    set α := t * y₁ * t⁻¹ with hαdef
    set ρ' := t * r * t⁻¹ with hρdef
    have hcomm : (ρ' * r⁻¹) * y₁⁻¹ = y₁⁻¹ * (ρ' * r⁻¹) :=
      S.comm_of_mem_conjClosure
        ((uOfL22 T M).mul_mem (hUXU hρ) ((uOfL22 T M).inv_mem (hUXU hr)))
        ((uOfL22 T M).inv_mem (c.hU₁U hy₁))
    have e2 : (α * y₁⁻¹) * (ρ' * r⁻¹) = t * v * t⁻¹ * v⁻¹ := by
      calc (α * y₁⁻¹) * (ρ' * r⁻¹) = α * ((y₁⁻¹ * (ρ' * r⁻¹))) := by group
        _ = α * ((ρ' * r⁻¹) * y₁⁻¹) := by rw [hcomm]
        _ = t * v * t⁻¹ * v⁻¹ := by rw [hvyr, hαdef, hρdef]; group
    have ha : α * y₁⁻¹ ∈ uxOf T M U₂ := by
      have e3 : α * y₁⁻¹ = (t * v * t⁻¹ * v⁻¹) * (ρ' * r⁻¹)⁻¹ := by
        rw [← e2]; group
      rw [e3]
      exact (uxOf T M U₂).mul_mem (hZX hz)
        ((uxOf T M U₂).inv_mem ((uxOf T M U₂).mul_mem hρ ((uxOf T M U₂).inv_mem hr)))
    exact c.inf_uxOf_le S ⟨U₁.mul_mem hα (U₁.inv_mem hy₁), ha⟩
  by_contra hne
  have hel := c.hSec.isElemAbelian_tilde
  have hcommW : ∀ a b : ↥(tildeOf Zz U₁), a * b = b * a :=
    fun a b => Subtype.ext (isElemAbelian_comm hel a.2 b.2)
  have hsqW : ∀ a : ↥(tildeOf Zz U₁), a ^ 2 = 1 := fun a =>
    Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel a.2)
  have hw₁ : tildeElt hUZ y₁ hy₁ ≠ 1 := by
    intro h
    apply hy₁Z
    have h1 := congrArg
      (fun w : ↥(tildeOf Zz U₁) =>
        (w : SecQuot (Subgroup.normalizer (Zz : Set G)) Zz)) h
    exact secMk_eq_one_iff.mp (by simpa [tildeElt] using h1)
  have hw₂ : tildeElt hUZ u c.huU ≠ 1 := by
    intro h
    apply c.huZ
    have h1 := congrArg
      (fun w : ↥(tildeOf Zz U₁) =>
        (w : SecQuot (Subgroup.normalizer (Zz : Set G)) Zz)) h
    exact secMk_eq_one_iff.mp (by simpa [tildeElt] using h1)
  have hw12 : tildeElt hUZ y₁ hy₁ ≠ tildeElt hUZ u c.huU := by
    intro h
    apply hne
    have h1 := congrArg
      (fun w : ↥(tildeOf Zz U₁) =>
        (w : SecQuot (Subgroup.normalizer (Zz : Set G)) Zz)) h
    have h2 := secMk_eq_secMk_iff.mp (by simpa [tildeElt] using h1)
    have h3 := (quasithinOmegaOneCenter T).inv_mem h2
    simpa using h3
  refine L3Stab.false_of_fix_two hcommW hsqW c.hSec.card_tilde _ (c.card_rhoImage S) hw₁ hw₂ hw12 ?_
  intro σ hσ
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hσ
  have hkTK : (k : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hk
  have hk₀ : (k : G) ∈ tZero T u := c.hTU₁ ⟨hkTK.1, c.hSec.KU k.2⟩
  refine ⟨?_, ?_⟩
  · exact (secRho_apply_tildeElt_iff c.hSec.KZ c.hSec.KU hUZ k y₁ hy₁).mpr (hT₀ k hk₀)
  · exact (secRho_apply_tildeElt_iff c.hSec.KZ c.hSec.KU hUZ k u c.huU).mpr
      (hk₀.2.2 u (Subgroup.mem_zpowers u))

end YOne

end CFSG.Quasithin
