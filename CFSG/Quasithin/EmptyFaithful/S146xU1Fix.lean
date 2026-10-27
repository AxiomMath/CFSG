module

public import CFSG.Quasithin.EmptyFaithful.S146xThreeA
public import CFSG.Quasithin.EmptyFaithful.S146E9
public import CFSG.Quasithin.EmptyFaithful.S146Six2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section FixLemma

variable {G : Type} [Group G] [Finite G] {T M K U₁ : Subgroup G} {u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem Setting146.card_rho_image_inf (S : Setting146 G T M) (hK : K ∈ cComp (mcOf T))
    (hSec : Sec8 K Zz U₁) (hsimple : IsSimpleGroup (KBar K))
    (hQ' : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Zz)
    (h168 : (pCoreOf 2 K).relIndex K = 168) :
    Nat.card (((T ⊓ K).subgroupOf K).map hSec.rho) = 8 := by
  have hKS : IsSylowTwoOf (T ⊓ K) K := S.isSylowTwoOf_inf hK
  have hOT : pCoreOf 2 K ≤ T ⊓ K := S.pCoreOf_le_inf hK
  set D : Subgroup ↥K := (T ⊓ K).subgroupOf K with hD
  have hsurj : Function.Surjective hSec.rho := fun σ => hSec.exists_rho_eq hsimple hQ' h168 σ
  have hker : hSec.rho.ker ≤ D := by
    intro k hk
    have h1 := hSec.mem_centralizerMod_of_rho_eq_one (MonoidHom.mem_ker.mp hk)
    exact Subgroup.mem_subgroupOf.mpr (hOT (hSec.centralizerMod_le hsimple hQ' h1))
  have hidx : (D.map hSec.rho).index = D.index := Subgroup.index_map_eq D hsurj hker
  have hodd : ¬ 2 ∣ (D.map hSec.rho).index := by
    rw [hidx]
    exact hKS.2.2
  have hp : IsPGroup 2 (D.map hSec.rho) := (hKS.2.1.comap_subtype (K := K)).map _
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hel := hSec.isElemAbelian_tilde
  have hcard : Nat.card (MulAut ↥(tildeOf Zz U₁)) = 168 :=
    card_mulAut_of_card_eight (fun a b => Subtype.ext (isElemAbelian_comm hel a.2 b.2))
      (fun a => Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel a.2))
      hSec.card_tilde
  have hmul := Subgroup.card_mul_index (D.map hSec.rho)
  rw [hn, hcard] at hmul
  rw [hn]
  exact two_pow_eq_eight_of (Or.inl rfl) hmul hodd

theorem Setting146.eq_or_eq_of_fixed (S : Setting146 G T M) (hK : K ∈ cComp (mcOf T))
    (hSec : Sec8 K Zz U₁) (hsimple : IsSimpleGroup (KBar K))
    (hQ' : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Zz)
    (h168 : (pCoreOf 2 K).relIndex K = 168) (huU : u ∈ U₁) (huZ : u ∉ Zz)
    (hfix : ∀ p ∈ T ⊓ K, p * u * p⁻¹ * u⁻¹ ∈ Zz) {a : G} (haU : a ∈ U₁)
    (ha : ∀ p ∈ T ⊓ K, p * a * p⁻¹ * a⁻¹ ∈ Zz) : a ∈ Zz ∨ u⁻¹ * a ∈ Zz := by
  by_contra hcon
  push Not at hcon
  obtain ⟨haZ, hua⟩ := hcon
  have hUZ : U₁ ≤ Subgroup.normalizer (Zz : Set G) := hSec.norm
  have hel := hSec.isElemAbelian_tilde
  have hcommW : ∀ a b : ↥(tildeOf Zz U₁), a * b = b * a :=
    fun a b => Subtype.ext (isElemAbelian_comm hel a.2 b.2)
  have hsqW : ∀ a : ↥(tildeOf Zz U₁), a ^ 2 = 1 := fun a =>
    Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel a.2)
  have hw₁ : tildeElt hUZ a haU ≠ 1 := by
    intro h
    apply haZ
    have h1 := congrArg
      (fun w : ↥(tildeOf Zz U₁) =>
        (w : SecQuot (Subgroup.normalizer (Zz : Set G)) Zz)) h
    exact secMk_eq_one_iff.mp (by simpa [tildeElt] using h1)
  have hw₂ : tildeElt hUZ u huU ≠ 1 := by
    intro h
    apply huZ
    have h1 := congrArg
      (fun w : ↥(tildeOf Zz U₁) =>
        (w : SecQuot (Subgroup.normalizer (Zz : Set G)) Zz)) h
    exact secMk_eq_one_iff.mp (by simpa [tildeElt] using h1)
  have hw12 : tildeElt hUZ a haU ≠ tildeElt hUZ u huU := by
    intro h
    apply hua
    have h1 := congrArg
      (fun w : ↥(tildeOf Zz U₁) =>
        (w : SecQuot (Subgroup.normalizer (Zz : Set G)) Zz)) h
    have h2 := secMk_eq_secMk_iff.mp (by simpa [tildeElt] using h1)
    have h3 := (quasithinOmegaOneCenter T).inv_mem h2
    simpa using h3
  refine L3Stab.false_of_fix_two hcommW hsqW hSec.card_tilde _
    (S.card_rho_image_inf hK hSec hsimple hQ' h168) hw₁ hw₂ hw12 ?_
  intro σ hσ
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hσ
  have hkTK : (k : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hk
  refine ⟨?_, ?_⟩
  · exact (secRho_apply_tildeElt_iff hSec.KZ hSec.KU hUZ k a haU).mpr (ha k hkTK)
  · exact (secRho_apply_tildeElt_iff hSec.KZ hSec.KU hUZ k u huU).mpr (hfix k hkTK)

end FixLemma

section NormalCase

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem Setting146.conj_mem_classes (S : Setting146 G T M) (hK : K ∈ cComp (mcOf T))
    (hSec : Sec8 K Zz U₁) (hsimple : IsSimpleGroup (KBar K))
    (hQ' : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Zz)
    (h168 : (pCoreOf 2 K).relIndex K = 168) (hU₁U : U₁ ≤ uOfL22 T M) (hU₂U : U₂ ≤ uOfL22 T M)
    (hsup : ⁅uOfL22 T M, K⁆ ⊔ Zz = U₁ ⊔ U₂) (hU₂ : U₂ = conjSub s U₁) (hZU₂ : Zz ≤ U₂)
    (hinf : U₁ ⊓ U₂ ≤ Zz) (hsT : s ∈ T) (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hTK : ∀ t ∈ T, t ∈ Subgroup.normalizer (K : Set G)) (huU : u ∈ U₁) (huZ : u ∉ Zz)
    (hfix : ∀ p ∈ T ⊓ K, p * u * p⁻¹ * u⁻¹ ∈ Zz) {t : G} (htT : t ∈ T) :
    t * u * t⁻¹ * u⁻¹ ∈ Zz ∨ (s * u * s⁻¹)⁻¹ * (t * u * t⁻¹) ∈ Zz ∨
      (u * (s * u * s⁻¹))⁻¹ * (t * u * t⁻¹) ∈ Zz := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _
  have hZU : Zz ≤ uOfL22 T M := hSec.le.trans hU₁U
  have htU : t ∈ Subgroup.normalizer (uOfL22 T M : Set G) := hHU (hTH htT)
  have hsU : s ∈ Subgroup.normalizer (uOfL22 T M : Set G) := hHU (hTH hsT)
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hTK t htT
  have htZ : t ∈ Subgroup.normalizer (Zz : Set G) := S.normalizer_Z.ge (hTH htT)
  have hsZ : s ∈ Subgroup.normalizer (Zz : Set G) := S.normalizer_Z.ge (hTH hsT)
  have hUc : ∀ {x y : G}, x ∈ uOfL22 T M → y ∈ uOfL22 T M → x * y = y * x :=
    fun hx hy => S.comm_of_mem_conjClosure hx hy
  have hKU₂ : K ≤ Subgroup.normalizer (U₂ : Set G) := by
    rw [hU₂]
    exact le_normalizer_conjSub hsK hSec.KU
  have hcomm_eq : conjSub t ⁅uOfL22 T M, K⁆ = ⁅uOfL22 T M, K⁆ := by
    rw [← conjSub_commutator, F7.conjSub_eq_of_mem_normalizer htU,
      F7.conjSub_eq_of_mem_normalizer htK]
  have hVN : t ∈ Subgroup.normalizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
    rw [← hsup]
    refine mem_normalizer_of_conjSub_eq ?_
    rw [conjSub_sup, hcomm_eq, F7.conjSub_eq_of_mem_normalizer htZ]
  have hxV : t * u * t⁻¹ ∈ U₁ ⊔ U₂ := by
    have h1 : t * u * t⁻¹ ∈ conjSub t (U₁ ⊔ U₂) := mul_mem_conjSub (Subgroup.mem_sup_left huU)
    rwa [F7.conjSub_eq_of_mem_normalizer hVN] at h1
  have hN₁₂ : U₁ ≤ Subgroup.normalizer (U₂ : Set G) :=
    le_normalizer_of_forall_commute fun x hx y hy => hUc (hU₁U hx) (hU₂U hy)
  have hxV' : t * u * t⁻¹ ∈ ((U₁ ⊔ U₂ : Subgroup G) : Set G) := hxV
  rw [Subgroup.coe_mul_of_left_le_normalizer_right U₁ U₂ hN₁₂] at hxV'
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hxV'
  have hPx : ∀ p ∈ T ⊓ K, p * (t * u * t⁻¹) * p⁻¹ * (t * u * t⁻¹)⁻¹ ∈ Zz := by
    intro p hp
    have hq : t⁻¹ * p * t ∈ T ⊓ K := by
      refine ⟨T.mul_mem (T.mul_mem (T.inv_mem htT) hp.1) htT, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htK) p).mp hp.2
      simpa [mul_assoc] using this
    have hc := hfix _ hq
    have hconj := (Subgroup.mem_normalizer_iff.mp htZ _).mp hc
    have e : t * ((t⁻¹ * p * t) * u * (t⁻¹ * p * t)⁻¹ * u⁻¹) * t⁻¹ =
        p * (t * u * t⁻¹) * p⁻¹ * (t * u * t⁻¹)⁻¹ := by group
    rwa [e] at hconj
  have hPab : ∀ p ∈ T ⊓ K, p * a * p⁻¹ * a⁻¹ ∈ Zz ∧ p * b * p⁻¹ * b⁻¹ ∈ Zz := by
    intro p hp
    have hpK : p ∈ K := hp.2
    have hpU : p ∈ Subgroup.normalizer (uOfL22 T M : Set G) := hHU (hTH hp.1)
    have hα : p * a * p⁻¹ * a⁻¹ ∈ U₁ :=
      U₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (hSec.KU hpK) a).mp ha) (U₁.inv_mem ha)
    have hβ : p * b * p⁻¹ * b⁻¹ ∈ U₂ :=
      U₂.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKU₂ hpK) b).mp hb) (U₂.inv_mem hb)
    have hαU := hU₁U hα
    have hβU := hU₂U hβ
    have haU := hU₁U ha
    have hbU := hU₂U hb
    have hx := hPx p hp
    rw [← hab] at hx
    have hcomm : (p * b * p⁻¹ * b⁻¹) * a⁻¹ = a⁻¹ * (p * b * p⁻¹ * b⁻¹) :=
      hUc hβU ((uOfL22 T M).inv_mem haU)
    have e : p * (a * b) * p⁻¹ * (a * b)⁻¹ = (p * a * p⁻¹ * a⁻¹) * (p * b * p⁻¹ * b⁻¹) := by
      calc p * (a * b) * p⁻¹ * (a * b)⁻¹ = (p * a * p⁻¹) * ((p * b * p⁻¹ * b⁻¹) * a⁻¹) := by group
        _ = (p * a * p⁻¹) * (a⁻¹ * (p * b * p⁻¹ * b⁻¹)) := by rw [hcomm]
        _ = (p * a * p⁻¹ * a⁻¹) * (p * b * p⁻¹ * b⁻¹) := by group
    rw [e] at hx
    have hα2 : p * a * p⁻¹ * a⁻¹ ∈ U₂ := by
      have : p * a * p⁻¹ * a⁻¹ = ((p * a * p⁻¹ * a⁻¹) * (p * b * p⁻¹ * b⁻¹)) *
          (p * b * p⁻¹ * b⁻¹)⁻¹ := by group
      rw [this]
      exact U₂.mul_mem (hZU₂ hx) (U₂.inv_mem hβ)
    have hαZ : p * a * p⁻¹ * a⁻¹ ∈ Zz := hinf ⟨hα, hα2⟩
    refine ⟨hαZ, ?_⟩
    have : p * b * p⁻¹ * b⁻¹ = (p * a * p⁻¹ * a⁻¹)⁻¹ *
        ((p * a * p⁻¹ * a⁻¹) * (p * b * p⁻¹ * b⁻¹)) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hαZ) hx
  have ha' : a ∈ Zz ∨ u⁻¹ * a ∈ Zz :=
    S.eq_or_eq_of_fixed hK hSec hsimple hQ' h168 huU huZ hfix ha (fun p hp => (hPab p hp).1)
  have hb1 : s⁻¹ * b * s ∈ U₁ := mem_conjSub.mp (hU₂ ▸ hb)
  have hb'fix : ∀ p ∈ T ⊓ K, p * (s⁻¹ * b * s) * p⁻¹ * (s⁻¹ * b * s)⁻¹ ∈ Zz := by
    intro p hp
    have hq : s * p * s⁻¹ ∈ T ⊓ K := by
      refine ⟨T.mul_mem (T.mul_mem hsT hp.1) (T.inv_mem hsT), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp hsK p).mp hp.2
    have h := (hPab _ hq).2
    have hconj := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsZ) _).mp h
    have e : s⁻¹ * ((s * p * s⁻¹) * b * (s * p * s⁻¹)⁻¹ * b⁻¹) * s⁻¹⁻¹ =
        p * (s⁻¹ * b * s) * p⁻¹ * (s⁻¹ * b * s)⁻¹ := by group
    rwa [e] at hconj
  have hb' : s⁻¹ * b * s ∈ Zz ∨ u⁻¹ * (s⁻¹ * b * s) ∈ Zz :=
    S.eq_or_eq_of_fixed hK hSec hsimple hQ' h168 huU huZ hfix hb1 hb'fix
  have hb'' : b ∈ Zz ∨ (s * u * s⁻¹)⁻¹ * b ∈ Zz := by
    rcases hb' with h | h
    · left
      have := (Subgroup.mem_normalizer_iff.mp hsZ _).mp h
      simpa [mul_assoc] using this
    · right
      have := (Subgroup.mem_normalizer_iff.mp hsZ _).mp h
      have e : s * (u⁻¹ * (s⁻¹ * b * s)) * s⁻¹ = (s * u * s⁻¹)⁻¹ * b := by group
      rwa [e] at this
  have huZ' : ∀ {x : G}, x ∈ Zz → t * x * t⁻¹ ∈ Zz := fun hx =>
    (Subgroup.mem_normalizer_iff.mp htZ _).mp hx
  have hxZ : t * u * t⁻¹ ∉ Zz := by
    intro h
    apply huZ
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htZ) _).mp h
    simpa [mul_assoc] using this
  have hsuU : s * u * s⁻¹ ∈ uOfL22 T M := by
    have h1 : s * u * s⁻¹ ∈ conjSub s (uOfL22 T M) := mul_mem_conjSub (hU₁U huU)
    rwa [F7.conjSub_eq_of_mem_normalizer hsU] at h1
  have huU' : u ∈ uOfL22 T M := hU₁U huU
  have haU' : a ∈ uOfL22 T M := hU₁U ha
  have hbU' : b ∈ uOfL22 T M := hU₂U hb
  rcases ha' with ha1 | ha2
  · rcases hb'' with hb1' | hb2
    · exact absurd (hab ▸ Subgroup.mul_mem _ ha1 hb1') hxZ
    · right; left
      rw [← hab]
      have hc : (s * u * s⁻¹)⁻¹ * a = a * (s * u * s⁻¹)⁻¹ :=
        hUc ((uOfL22 T M).inv_mem hsuU) haU'
      have e : (s * u * s⁻¹)⁻¹ * (a * b) = a * ((s * u * s⁻¹)⁻¹ * b) := by
        calc (s * u * s⁻¹)⁻¹ * (a * b) = ((s * u * s⁻¹)⁻¹ * a) * b := by group
          _ = (a * (s * u * s⁻¹)⁻¹) * b := by rw [hc]
          _ = a * ((s * u * s⁻¹)⁻¹ * b) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha1 hb2
  · rcases hb'' with hb1' | hb2
    · left
      rw [← hab]
      have hc : a * u⁻¹ = u⁻¹ * a := hUc haU' ((uOfL22 T M).inv_mem huU')
      have hc2 : b * u⁻¹ = u⁻¹ * b := hUc hbU' ((uOfL22 T M).inv_mem huU')
      have e : a * b * u⁻¹ = (u⁻¹ * a) * b := by
        calc a * b * u⁻¹ = a * (b * u⁻¹) := by group
          _ = a * (u⁻¹ * b) := by rw [hc2]
          _ = (a * u⁻¹) * b := by group
          _ = (u⁻¹ * a) * b := by rw [hc]
      rw [e]
      exact Subgroup.mul_mem _ ha2 hb1'
    · right; right
      rw [← hab]
      have hc : (s * u * s⁻¹)⁻¹ * (u⁻¹ * a) = (u⁻¹ * a) * (s * u * s⁻¹)⁻¹ :=
        hUc ((uOfL22 T M).inv_mem hsuU)
          ((uOfL22 T M).mul_mem ((uOfL22 T M).inv_mem huU') haU')
      have e : (u * (s * u * s⁻¹))⁻¹ * (a * b) = (u⁻¹ * a) * ((s * u * s⁻¹)⁻¹ * b) := by
        calc (u * (s * u * s⁻¹))⁻¹ * (a * b)
            = ((s * u * s⁻¹)⁻¹ * (u⁻¹ * a)) * b := by group
          _ = ((u⁻¹ * a) * (s * u * s⁻¹)⁻¹) * b := by rw [hc]
          _ = (u⁻¹ * a) * ((s * u * s⁻¹)⁻¹ * b) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha2 hb2

end NormalCase

end CFSG.Quasithin
