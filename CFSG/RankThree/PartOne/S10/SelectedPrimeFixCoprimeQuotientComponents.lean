module

public import CFSG.RankThree.PartOne.S10.SemisimpleContract
public import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
import CFSG.RankThree.GroupTheory.SteinbergBKComponentOrbitLocalRank
import CFSG.RankThree.PartOne.S10.CoprimeTransitiveSemisimpleSectionOrbit
import CFSG.RankThree.PerfectCover.CentralQuotientPrimeSupport

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.LocalCores

namespace SelectedPrimeCoprime

theorem exists_semisimple_quotient {B : Type} [Group B] [Finite B] (hB : layer B = ⊤) :
    ∃ ρ : B →* (∀ K : ComponentIndex B, ↥K.1 ⧸ center ↥K.1), Function.Surjective ρ ∧
      (∀ b, ρ b = 1 ↔ b ∈ center B) ∧
      ∀ (K : ComponentIndex B) (b : B),
        ρ b ∈ coordSubgroup (fun K : ComponentIndex B => ↥K.1 ⧸ center ↥K.1) K ↔
          b ∈ K.1 ⊔ center B := by
  classical
  let Φ := layerCentralQuotientEquiv B
  let eB : B ≃* ↥(layer B) := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hB.symm)
  have heB : ∀ b : B, ((eB b : ↥(layer B)) : B) = b := fun b => rfl
  let ρ : B →* (∀ K : ComponentIndex B, ↥K.1 ⧸ center ↥K.1) :=
    (Φ.symm : _ →* _).comp ((QuotientGroup.mk' (center ↥(layer B))).comp eB.toMonoidHom)
  have hρ : ∀ b : B, Φ (ρ b) = (eB b : ↥(layer B) ⧸ center ↥(layer B)) := fun b => by
    simp [ρ]
  have hcenter : ∀ b : B, eB b ∈ center ↥(layer B) ↔ b ∈ center B := fun b => by
    rw [← Subgroup.map_center_eq eB]
    exact Subgroup.mem_map_iff_mem (f := eB.toMonoidHom) eB.injective
  refine ⟨ρ, ?_, ?_, ?_⟩
  · exact Φ.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp eB.surjective)
  · intro b
    rw [← hcenter, ← QuotientGroup.eq_one_iff, ← hρ, Φ.map_eq_one_iff]
  · intro K b
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t
      have ht' : Pi.mulSingle K (k : ↥K.1 ⧸ center ↥K.1) = ρ b := ht
      have h1 := layerCentralQuotientEquiv_mulSingle K k
      rw [ht', hρ] at h1
      have h2 := QuotientGroup.eq.mp h1
      have h3 : b⁻¹ * (k : B) ∈ center B := by
        rw [← hcenter, map_mul, map_inv]
        exact h2
      have hb : b = (k : B) * (b⁻¹ * (k : B))⁻¹ := by group
      rw [hb]
      exact Subgroup.mul_mem_sup k.2 (Subgroup.inv_mem _ h3)
    · intro hb
      obtain ⟨k, hk, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
      refine ⟨(⟨k, hk⟩ : ↥K.1), ?_⟩
      apply Φ.injective
      change Φ (Pi.mulSingle K ((⟨k, hk⟩ : ↥K.1) : ↥K.1 ⧸ center ↥K.1)) = _
      rw [layerCentralQuotientEquiv_mulSingle, hρ]
      refine QuotientGroup.eq.mpr ?_
      have hzc : eB z ∈ center ↥(layer B) := (hcenter z).mpr hz
      convert hzc using 1
      exact Subtype.ext (by simp [heB])

theorem iSup_subgroupOf_eq_top {Q : Type*} [Group Q] (B : Subgroup Q) (O : Set (Subgroup Q))
    (hgen : ⨆ L ∈ O, L = B) : ⨆ L ∈ O, L.subgroupOf B = ⊤ := by
  have hLB : ∀ L ∈ O, L ≤ B := fun L hL => hgen ▸ le_iSup₂ (f := fun L (_ : L ∈ O) => L) L hL
  apply Subgroup.map_injective B.subtype_injective
  have h1 : ∀ L ∈ O, (L.subgroupOf B).map B.subtype = L := fun L hL => by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hLB L hL)]
  calc (⨆ L ∈ O, L.subgroupOf B).map B.subtype = ⨆ L ∈ O, (L.subgroupOf B).map B.subtype := by
        simp only [Subgroup.map_iSup]
    _ = ⨆ L ∈ O, L := iSup_congr fun L => iSup_congr fun hL => h1 L hL
    _ = B := hgen
    _ = (⊤ : Subgroup B).map B.subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem layer_eq_top_and_component_eq {Q : Type*} [Group Q] [Finite Q] (B : Subgroup Q)
    (O : Set (Subgroup Q)) (hO : ∀ L ∈ O, IsComponent L) (hgen : ⨆ L ∈ O, L = B) :
    layer ↥B = ⊤ ∧ ∀ K : Subgroup ↥B, IsComponent K → ∃ L ∈ O, K = L.subgroupOf B := by
  have hLB : ∀ L ∈ O, L ≤ B := fun L hL => hgen ▸ le_iSup₂ (f := fun L (_ : L ∈ O) => L) L hL
  have hcomp : ∀ L ∈ O, IsComponent (L.subgroupOf B) := fun L hL =>
    component_overgroup (hO L hL) (hLB L hL)
  have hgenB := iSup_subgroupOf_eq_top B O hgen
  refine ⟨eq_top_iff.mpr (hgenB ▸ iSup₂_le fun L hL => component_le_layer (hcomp L hL)), ?_⟩
  intro K hK
  by_contra hne
  push Not at hne
  have hcentral : K ≤ center ↥B := by
    have hle : (⨆ L ∈ O, L.subgroupOf B) ≤ centralizer (K : Set ↥B) := by
      refine iSup₂_le fun L hL => ?_
      rcases distinct_components_commute hK (hcomp L hL) with h | h
      · exact absurd h (hne L hL)
      · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact h
    rw [hgenB] at hle
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    exact (mem_centralizer_iff.mp (hle (mem_top g)) k hk).symm
  have hKbot : K = ⊥ := by
    have h1 : ⁅K, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcentral.trans (Subgroup.center_le_centralizer _))
    exact (Subgroup.isPerfect_iff.mp hK.1.1).symm.trans h1
  have := isQuasisimple_nontrivial hK.1
  exact (Subgroup.nontrivial_iff_ne_bot K).mp this hKbot

theorem exists_odd_prime_dvd_card {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card S := by
  by_contra hno
  have hpow : ∃ k : ℕ, Nat.card S = 2 ^ k :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {r} hr hrd => by
      by_contra hr2
      exact hno ⟨r, hr, hr2, hrd⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2grp : IsPGroup 2 S := by
    obtain ⟨k, hk⟩ := hpow
    exact IsPGroup.of_card (n := k) hk
  have := h2grp.isNilpotent
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)

end SelectedPrimeCoprime

open SelectedPrimeCoprime

theorem selected_prime_elements_fix_coprime_quotient_components :
    SelectedPrimeElementsFixCoprimeQuotientComponents := by
  intro G _ _ he p hp hp3 N _ hpN x hxk L hL hpL
  classical
  by_contra hnorm
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  set xb : G ⧸ N := (x : G ⧸ N) with hxb
  have hxbk : ∃ k : ℕ, orderOf xb = p ^ k := by
    obtain ⟨k, hk⟩ := hxk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (hk ▸ orderOf_map_dvd (QuotientGroup.mk' N) x)
    exact ⟨j, hj⟩
  have hmove : L.map (MulAut.conj xb).toMonoidHom ≠ L := fun h =>
    hnorm (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hsimple : IsSimpleGroup (L ⧸ center L) := hL.1.2.1
  have hnonab : ∃ a b : L ⧸ center L, a * b ≠ b * a := hL.1.2.2
  obtain ⟨q, hq, hq2, hqdvd⟩ := exists_odd_prime_dvd_card hnonab
  have heven : Even (Nat.card (L ⧸ center L)) :=
    (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnonab).1
  have h2q : 2 * q ∣ Nat.card (L ⧸ center L) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes Nat.prime_two hq).mpr hq2.symm)
      (even_iff_two_dvd.mp heven) hqdvd
  obtain ⟨-, hpd, -⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBK.component_orbit_ambient_local_rank_witness
      hp hxbk hL hmove hq h2q (d := (conjOrbit xb L).ncard) rfl
  set O : Set (Subgroup (G ⧸ N)) := conjOrbit xb L with hO
  set B : Subgroup (G ⧸ N) := conjOrbitJoin xb L with hB
  have hOmem : ∀ L' ∈ O, ∃ n : ℤ, L' = L.map (MulAut.conj (xb ^ n)).toMonoidHom :=
    fun L' ⟨n, hn⟩ => ⟨n, hn.symm⟩
  have hOcomp : ∀ L' ∈ O, IsComponent L' ∧ Nat.card L' = Nat.card L ∧
      Nat.card (L' ⧸ center L') = Nat.card (L ⧸ center L) := by
    intro L' hL'
    obtain ⟨n, rfl⟩ := hOmem L' hL'
    let e := L.equivMapOfInjective (MulAut.conj (xb ^ n)).toMonoidHom
      (MulAut.conj (xb ^ n)).injective
    refine ⟨isComponent_map_mulEquiv (MulAut.conj (xb ^ n)) hL, (Nat.card_congr e.toEquiv).symm,
      ?_⟩
    have hc := Subgroup.map_center_eq e
    exact (Nat.card_congr (QuotientGroup.congr _ _ e hc).toEquiv).symm
  have hgen : ⨆ L' ∈ O, L' = B := by
    rw [hO, hB, conjOrbit, conjOrbitJoin]
    exact iSup_range (g := fun L' => L')
  have hLB : ∀ L' ∈ O, L' ≤ B := fun L' hL' =>
    hgen ▸ le_iSup₂ (f := fun L' (_ : L' ∈ O) => L') L' hL'
  have hxB : xb ∈ normalizer (B : Set (G ⧸ N)) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    have h1 : ∀ n : ℤ, (L.map (MulAut.conj (xb ^ n)).toMonoidHom).map
        (MulAut.conj xb).toMonoidHom = L.map (MulAut.conj (xb ^ (n + 1))).toMonoidHom := by
      intro n
      rw [Subgroup.map_map]
      congr 1
      refine MonoidHom.ext fun y => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    change B.map (MulAut.conj xb).toMonoidHom = B
    rw [hB, conjOrbitJoin, Subgroup.map_iSup]
    simp_rw [h1]
    exact (Equiv.addRight (1 : ℤ)).iSup_comp
      (g := fun n => L.map (MulAut.conj (xb ^ n)).toMonoidHom)
  set H : Subgroup G := B.comap (QuotientGroup.mk' N) with hH
  have hxH : x ∈ normalizer (H : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h1 := Subgroup.mem_normalizer_iff.mp hxB (QuotientGroup.mk' N g)
    rw [hH, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact h1
  obtain ⟨hlayer, hcompB⟩ :=
    layer_eq_top_and_component_eq B O (fun L' hL' => (hOcomp L' hL').1) hgen
  have : Group.IsPerfect ↥L := hL.1.1
  have hpL' : ¬ p ∣ Nat.card L :=
    CFSG.RankThree.PerfectCover.perfect_central_quotient_prime_support hp hpL
  have hpB : ¬ p ∣ Nat.card B := by
    have hdvd : Nat.card (layer ↥B) ∣ Nat.card (∀ K : ComponentIndex ↥B, ↥K.1) :=
      Subgroup.card_dvd_of_surjective (layerMulOnto_surjective (G := ↥B))
    rw [hlayer, Subgroup.card_top, Nat.card_pi] at hdvd
    intro hp'
    obtain ⟨K, -, hK⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp (hp'.trans hdvd)
    obtain ⟨L', hL', hKL'⟩ := hcompB K.1 K.2
    rw [hKL', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hLB L' hL')).toEquiv,
      (hOcomp L' hL').2.1] at hK
    exact hpL' hK
  have hNH : N ≤ H := fun n hn => by
    have h1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [hH, Subgroup.mem_comap, h1]
    exact B.one_mem
  let πB : ↥H →* ↥B := (QuotientGroup.mk' N).subgroupComap B
  have hπBs : Function.Surjective πB :=
    (QuotientGroup.mk' N).subgroupComap_surjective B (QuotientGroup.mk'_surjective N)
  have hpH : ¬ p ∣ Nat.card H := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup πB.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective πB hπBs).toEquiv] at h1
    have hker : πB.ker = N.subgroupOf H := by
      ext h
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
      exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv] at h1
    intro hdvd
    rw [h1] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact hpB h
    · exact hpN h
  obtain ⟨ρ, hρs, hρker, hρcoord⟩ := exists_semisimple_quotient hlayer
  let π : ↥H →* ∀ K : ComponentIndex ↥B, ↥K.1 ⧸ center ↥K.1 := ρ.comp πB
  have hπs : Function.Surjective π := hρs.comp hπBs
  set α : MulAut ↥H := H.normalizerMonoidHom ⟨x, hxH⟩ with hα
  set β : MulAut ↥B := B.normalizerMonoidHom ⟨xb, hxB⟩ with hβ
  have hαc : ∀ (n : ℕ) (h : ↥H), (((α ^ n) h : ↥H) : G) = x ^ n * (h : G) * (x ^ n)⁻¹ := by
    intro n h
    rw [hα, ← map_pow, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_pow]
  have hβc : ∀ (n : ℕ) (b : ↥B),
      (((β ^ n) b : ↥B) : G ⧸ N) = xb ^ n * (b : G ⧸ N) * (xb ^ n)⁻¹ := by
    intro n b
    rw [hβ, ← map_pow, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_pow]
  have hπβ : ∀ (n : ℕ) (h : ↥H), πB ((α ^ n) h) = (β ^ n) (πB h) := by
    intro n h
    apply Subtype.ext
    rw [hβc]
    change QuotientGroup.mk' N (((α ^ n) h : ↥H) : G) = _
    rw [hαc, map_mul, map_mul, map_inv, map_pow]
    rfl
  have hker : ∀ h : ↥H, π h = 1 → π (α h) = 1 := by
    intro h hh
    have h1 : πB h ∈ center ↥B := (hρker _).mp hh
    have h2 : πB (α h) ∈ center ↥B := by
      have h3 := hπβ 1 h
      rw [pow_one, pow_one] at h3
      rw [h3, ← Subgroup.map_center_eq β]
      exact Subgroup.mem_map_of_mem _ h1
    exact (hρker _).mpr h2
  have hconjmap : ∀ (g h' : G ⧸ N) (L' : Subgroup (G ⧸ N)),
      (L'.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h').toMonoidHom =
        L'.map (MulAut.conj (h' * g)).toMonoidHom := by
    intro g h' L'
    rw [Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun y => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hKmap : ∀ (n : ℕ) (L' : Subgroup (G ⧸ N)), L' ≤ B →
      (L'.subgroupOf B).map (β ^ n).toMonoidHom =
        (L'.map (MulAut.conj (xb ^ n)).toMonoidHom).subgroupOf B := by
    intro n L' hL'B
    ext b
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨b', hb', rfl⟩
      change (((β ^ n) b' : ↥B) : G ⧸ N) ∈ _
      rw [hβc]
      exact ⟨(b' : G ⧸ N), hb', rfl⟩
    · rintro ⟨l, hl, hlb⟩
      refine ⟨⟨l, hL'B hl⟩, hl, Subtype.ext ?_⟩
      change (((β ^ n) ⟨l, hL'B hl⟩ : ↥B) : G ⧸ N) = _
      rw [hβc]
      exact hlb
  have hZmap : ∀ n : ℕ, (center ↥B).map (β ^ n).toMonoidHom = center ↥B := fun n =>
    Subgroup.map_center_eq (β ^ n)
  have htrans : ∀ K K' : ComponentIndex ↥B, ∃ n : ℕ, ∀ h : ↥H,
      π h ∈ coordSubgroup (fun K : ComponentIndex ↥B => ↥K.1 ⧸ center ↥K.1) K ↔
        π ((α ^ n) h) ∈ coordSubgroup (fun K : ComponentIndex ↥B => ↥K.1 ⧸ center ↥K.1) K' := by
    intro K K'
    obtain ⟨L₁, hL₁, hK₁⟩ := hcompB K.1 K.2
    obtain ⟨L₂, hL₂, hK₂⟩ := hcompB K'.1 K'.2
    obtain ⟨a, ha⟩ := hOmem L₁ hL₁
    obtain ⟨b, hb⟩ := hOmem L₂ hL₂
    have hord : (orderOf xb : ℤ) ≠ 0 := by exact_mod_cast (orderOf_pos xb).ne'
    set n : ℕ := ((b - a) % (orderOf xb : ℤ)).toNat with hn
    have hn' : (n : ℤ) = (b - a) % (orderOf xb : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hord)
    have hxn : xb ^ (n : ℤ) * xb ^ a = xb ^ b := by
      rw [hn', zpow_mod_orderOf, ← zpow_add, sub_add_cancel]
    have hL12 : L₁.map (MulAut.conj (xb ^ n)).toMonoidHom = L₂ := by
      rw [ha, hb, hconjmap, ← zpow_natCast, hxn]
    have hK'eq : K'.1 = K.1.map (β ^ n).toMonoidHom := by
      rw [hK₁, hK₂, hKmap n L₁ (hLB L₁ hL₁), hL12]
    refine ⟨n, fun h => ?_⟩
    rw [show π h = ρ (πB h) from rfl, show π ((α ^ n) h) = ρ (πB ((α ^ n) h)) from rfl,
      hρcoord K (πB h), hρcoord K' (πB ((α ^ n) h)), hπβ n h, hK'eq]
    have hsup : K.1.map (β ^ n).toMonoidHom ⊔ center ↥B =
        (K.1 ⊔ center ↥B).map (β ^ n).toMonoidHom := by
      rw [Subgroup.map_sup, hZmap]
    rw [hsup]
    exact (Subgroup.mem_map_iff_mem (f := (β ^ n).toMonoidHom) (β ^ n).injective).symm
  have : ∀ K : ComponentIndex ↥B, IsSimpleGroup (↥K.1 ⧸ center ↥K.1) := fun K => K.2.1.2.1
  have hnonabK : ∀ K : ComponentIndex ↥B, ∃ a b : ↥K.1 ⧸ center ↥K.1, a * b ≠ b * a :=
    fun K => K.2.1.2.2
  have hevenK : ∀ K : ComponentIndex ↥B, Even (Nat.card (↥K.1 ⧸ center ↥K.1)) := fun K =>
    (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even (hnonabK K)).1
  have hLO : L ∈ O := ⟨0, Subgroup.ext fun y => by simp⟩
  have : Nonempty (ComponentIndex ↥B) :=
    ⟨⟨L.subgroupOf B, component_overgroup hL (hLB L hLO)⟩⟩
  have hcard := coprime_transitive_semisimple_section_orbit_bound G 3 he p hp hp2 x hxk H hxH
    hpH (ComponentIndex ↥B) (fun K => ↥K.1 ⧸ center ↥K.1) hnonabK hevenK π hπs hker htrans
  have hinj : Function.Injective (fun L' : O => (⟨L'.1.subgroupOf B,
      component_overgroup (hOcomp L'.1 L'.2).1 (hLB L'.1 L'.2)⟩ : ComponentIndex ↥B)) := by
    intro L₁ L₂ h
    have h' : L₁.1.subgroupOf B = L₂.1.subgroupOf B := congrArg Subtype.val h
    apply Subtype.ext
    have h'' := congrArg (Subgroup.map B.subtype) h'
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hLB _ L₁.2), inf_eq_left.mpr (hLB _ L₂.2)] at h''
  have hOle : O.ncard ≤ Fintype.card (ComponentIndex ↥B) := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective _ hinj
  omega

end CFSG.RankThree.PartOne
