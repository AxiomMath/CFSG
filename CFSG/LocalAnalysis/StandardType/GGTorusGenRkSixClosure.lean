module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkSixWeyl
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkSixTorus
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkGen
public import CFSG.LieType.CentralExt.CoprimeLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private theorem exists_pElt_mem_of_map_eq {p : ℕ} (hp : p.Prime)
    {Γ : Type} [Group Γ] [Finite Γ] (H : Subgroup Γ)
    {G' : Type} [Group G'] (π : Γ →* G') {x : Γ} (hxH : x ∈ H) {u : G'}
    (hu : π x = u) (hup : ∃ b : ℕ, orderOf u = p ^ b) :
    ∃ y ∈ H, π y = u ∧ ∃ k : ℕ, orderOf y = p ^ k := by
  classical
  obtain ⟨b, hb⟩ := hup
  have hN : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨e, n', hn'p, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
  have hcop : p.Coprime n' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hn'p
  have hc' : (p ^ b).Coprime n' := (hcop.symm.pow_right b).symm
  obtain ⟨t, ht1, ht0⟩ := Nat.chineseRemainder hc' 1 0
  have hu_pow : u ^ (p ^ b) = 1 := by rw [← hb]; exact pow_orderOf_eq_one u
  refine ⟨x ^ t, H.pow_mem hxH t, ?_, ?_⟩
  · rw [map_pow, hu, pow_eq_pow_of_modEq ht1 hu_pow, pow_one]
  · obtain ⟨q, hq⟩ := Nat.modEq_zero_iff_dvd.mp ht0
    have hxN : x ^ (p ^ e * n') = 1 := by rw [← hord, pow_orderOf_eq_one]
    have hxe : (x ^ t) ^ p ^ e = 1 := by
      calc (x ^ t) ^ p ^ e = x ^ (t * p ^ e) := by rw [pow_mul]
        _ = x ^ (n' * q * p ^ e) := by rw [hq]
        _ = x ^ (q * (p ^ e * n')) := by congr 1; ring
        _ = (x ^ (p ^ e * n')) ^ q := by rw [← pow_mul]; congr 1; ring
        _ = 1 := by rw [hxN, one_pow]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hxe)
    exact ⟨k, hk⟩

private theorem not_dvd_card_of_two_power {Γ : Type} [Group Γ] [Finite Γ]
    {Z : Subgroup Γ} (hZ : ∀ z : Γ, z ∈ Z ↔ z ∈ Subgroup.center Γ ∧ ∃ k : ℕ, z ^ 2 ^ k = 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card Z := by
  have hZ2 : IsPGroup 2 Z := by
    rw [IsPGroup.iff_orderOf]
    intro z
    obtain ⟨k, hk⟩ := (hZ (z : Γ)).mp z.2 |>.2
    obtain ⟨m, hm⟩ := CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_pow_eq_one (p := 2) hk
    exact ⟨m, by rw [← Subgroup.orderOf_coe, hm]⟩
  obtain ⟨m, hm⟩ := hZ2.exists_card_eq
  rw [hm]
  intro hdvd
  have hpd2 : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpd2)

theorem mem_closure_conj_pLift_six_one
    {p : ℕ} {K : Type} [Field K]
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hpos : GGTableBPosition p L' E I θ hE) (hp : p.Prime)
    (hp2 : p ≠ 2) (Z : Subgroup L') [Z.Normal]
    (hZ : ∀ z : L', z ∈ Z ↔ z ∈ Subgroup.center L' ∧ ∃ k : ℕ, z ^ 2 ^ k = 1)
    {φ : ↥(unitarySU 2 1 K 6) →* L' ⧸ Z} (hφ : UnitTB.Model φ)
    (hdiag : ∀ e : E, ∃ (t : Fin 6 → K) (D : GL (Fin 6) K)
        (hD : D ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K))),
        (D : Matrix (Fin 6) (Fin 6) K) = diagonal t ∧
        ∀ (s : ↥(unitarySU 2 1 K 6)) (l : L'), (QuotientGroup.mk l : L' ⧸ Z) = φ s →
          (QuotientGroup.mk (L'.normalizerMonoidHom ⟨e, hE e.2⟩ l) : L' ⧸ Z) =
            φ (conjN D hD s))
    (I₀ : Finset (Fin 6)) (hI₀ : 2 ≤ I₀.card)
    (S : Subgroup M)
    (hS : S = Subgroup.closure {ℓ : M | ∃ ℓ' : L', (ℓ' : M) = ℓ ∧ (∃ k : ℕ, orderOf ℓ' = p ^ k) ∧
      ∃ x ∈ TableBUE.blockSU (K := K) (n := 1) I₀,
        (∃ v : Fin 6 → K, ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal v) ∧
        (QuotientGroup.mk ℓ' : L' ⧸ Z) = φ x})
    (c : L') (hcp : ∃ k : ℕ, orderOf c = p ^ k) (s : ↥(unitarySU 2 1 K 6))
    (hs : ∃ v : Fin 6 → K, ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal v)
    (hsp : ∃ k : ℕ, s ^ p ^ k = 1) (hc : (QuotientGroup.mk c : L' ⧸ Z) = φ s) :
    (c : M) ∈ Subgroup.closure (⋃ n ∈ {n : M | n ∈ Subgroup.normalizer (E : Set M) ∧
        ∃ (σ : Equiv.Perm (Fin 6)) (n' : L'), (n' : M) = n ∧
          (QuotientGroup.mk n' : L' ⧸ Z) = φ (permSU hφ.field σ)},
      (fun x => n * x * n⁻¹) '' (S : Set M)) := by
  classical
  let π : L' →* L' ⧸ Z := QuotientGroup.mk' Z
  let W : Set M := {n : M | n ∈ Subgroup.normalizer (E : Set M) ∧
      ∃ (σ : Equiv.Perm (Fin 6)) (n' : L'), (n' : M) = n ∧
        (QuotientGroup.mk n' : L' ⧸ Z) = φ (permSU hφ.field σ)}
  let G : Subgroup M := Subgroup.closure (⋃ n ∈ W, (fun x : M => n * x * n⁻¹) '' (S : Set M))
  change (c : M) ∈ G
  let Gen : Set ↥(unitarySU 2 1 K 6) :=
    {x | x ∈ TableBUE.blockSU (K := K) (n := 1) I₀ ∧
      (∃ v : Fin 6 → K, ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal v) ∧
      ∃ k : ℕ, x ^ p ^ k = 1}
  have hGen_mem : ∀ x : ↥(unitarySU 2 1 K 6), x ∈ Gen ↔
      x ∈ TableBUE.blockSU (K := K) (n := 1) I₀ ∧
        (∃ v : Fin 6 → K, ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal v) ∧
        ∃ k : ℕ, x ^ p ^ k = 1 := fun _ => Iff.rfl
  let C : Subgroup ↥(unitarySU 2 1 K 6) :=
    Subgroup.closure (⋃ σ : Equiv.Perm (Fin 6),
      (fun x : ↥(unitarySU 2 1 K 6) => permSU hφ.field σ * x * (permSU hφ.field σ)⁻¹) '' Gen)
  have hsC : s ∈ C := diag_pElt_mem_closure_permConj hφ.field I₀ hI₀ s hs hsp
  have key : ∀ x ∈ C, ∃ c' : L', π c' = φ x ∧ (c' : M) ∈ G := by
    intro x hx
    refine Subgroup.closure_induction (p := fun s _ => ∃ c' : L', π c' = φ s ∧ (c' : M) ∈ G)
      ?_ ?_ ?_ ?_ hx
    ·
      intro y hy
      rw [Set.mem_iUnion] at hy
      obtain ⟨σ, hy⟩ := hy
      rw [Set.mem_image] at hy
      obtain ⟨d, hdGen, hdy⟩ := hy
      rw [← hdy]
      obtain ⟨hdblock, hddiag, hdpow⟩ := (hGen_mem d).mp hdGen
      obtain ⟨nσ, hnσ_eq, hnσ_norm⟩ :=
        exists_lift_mem_normalizer_six_one hpos hp Z hZ hp2 hφ hdiag σ
      have hnσ_eq' : π nσ = φ (permSU hφ.field σ) := hnσ_eq
      have hφd_pow : ∃ b : ℕ, orderOf (φ d) = p ^ b := by
        obtain ⟨k, hk⟩ := hdpow
        have hdvd : orderOf d ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
        have hdvd' : orderOf (φ d) ∣ p ^ k := (orderOf_map_dvd φ d).trans hdvd
        obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1 hdvd'
        exact ⟨b, hb⟩
      obtain ⟨y0, hy0⟩ := QuotientGroup.mk'_surjective Z (φ d)
      obtain ⟨ℓ, -, hℓ_eq, hℓ_pow⟩ :=
        exists_pElt_mem_of_map_eq hp ⊤ (QuotientGroup.mk' Z) (Subgroup.mem_top y0) hy0 hφd_pow
      have hℓ_gen : (ℓ : M) ∈ {ℓ : M | ∃ ℓ' : L', (ℓ' : M) = ℓ ∧
          (∃ k : ℕ, orderOf ℓ' = p ^ k) ∧
          ∃ x ∈ TableBUE.blockSU (K := K) (n := 1) I₀,
            (∃ v : Fin 6 → K, ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal v) ∧
            (QuotientGroup.mk ℓ' : L' ⧸ Z) = φ x} :=
        ⟨ℓ, rfl, hℓ_pow, d, hdblock, hddiag, hℓ_eq⟩
      have hℓS : (ℓ : M) ∈ S := by rw [hS]; exact Subgroup.subset_closure hℓ_gen
      have hnσW : (nσ : M) ∈ W := ⟨hnσ_norm, σ, nσ, rfl, hnσ_eq⟩
      refine ⟨nσ * ℓ * nσ⁻¹, ?_, ?_⟩
      · rw [map_mul, map_mul, map_inv, hnσ_eq', hℓ_eq, map_mul, map_mul, map_inv]
      · change L'.subtype (nσ * ℓ * nσ⁻¹) ∈ G
        rw [map_mul, map_mul, map_inv]
        refine Subgroup.subset_closure ?_
        simp only [Set.mem_iUnion, Set.mem_image]
        exact ⟨(nσ : M), hnσW, (ℓ : M), hℓS, rfl⟩
    ·
      refine ⟨1, ?_, Subgroup.one_mem _⟩
      rw [map_one, map_one]
    ·
      intro x y hx hy ihx ihy
      obtain ⟨cx, hcx, hcxG⟩ := ihx
      obtain ⟨cy, hcy, hcyG⟩ := ihy
      refine ⟨cx * cy, ?_, ?_⟩
      · rw [map_mul, hcx, hcy, map_mul]
      · change L'.subtype (cx * cy) ∈ G
        rw [map_mul]
        exact G.mul_mem hcxG hcyG
    ·
      intro x hx ihx
      obtain ⟨cx, hcx, hcxG⟩ := ihx
      refine ⟨cx⁻¹, ?_, ?_⟩
      · rw [map_inv, hcx, map_inv]
      · change L'.subtype cx⁻¹ ∈ G
        rw [map_inv]
        exact G.inv_mem hcxG
  obtain ⟨c', hc'_eq, hc'G⟩ := key s hsC
  have hφs_pow : ∃ b : ℕ, orderOf (φ s) = p ^ b := by
    obtain ⟨k, hk⟩ := hsp
    have hdvd : orderOf s ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    have hdvd' : orderOf (φ s) ∣ p ^ k := (orderOf_map_dvd φ s).trans hdvd
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1 hdvd'
    exact ⟨b, hb⟩
  let H' : Subgroup L' := G.comap L'.subtype
  have hc'H : c' ∈ H' := Subgroup.mem_comap.mpr hc'G
  obtain ⟨y, hyH, hy_eq, hypow⟩ :=
    exists_pElt_mem_of_map_eq hp H' (QuotientGroup.mk' Z) hc'H hc'_eq hφs_pow
  have hyG : (y : M) ∈ G := Subgroup.mem_comap.mp hyH
  have hy_eq' : (QuotientGroup.mk y : L' ⧸ Z) = φ s := by
    rw [← QuotientGroup.mk'_apply]
    exact hy_eq
  haveI : Fact p.Prime := ⟨hp⟩
  have hker : (QuotientGroup.mk' Z).ker = Z := QuotientGroup.ker_mk' Z
  have hcen : (QuotientGroup.mk' Z).ker ≤ Subgroup.center L' := by
    rw [hker]
    intro z hz
    exact (hZ z).mp hz |>.1
  have hC : ¬ p ∣ Nat.card (QuotientGroup.mk' Z).ker := by
    rw [hker]
    exact not_dvd_card_of_two_power hZ hp hp2
  have hcy : (QuotientGroup.mk' Z) c = (QuotientGroup.mk' Z) y := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hc, hy_eq']
  have hcy_eq : c = y := CFSG.LieType.CentralExt.eq_of_pElement hcen hC hcy hcp hypow
  rw [hcy_eq]
  exact hyG

end CFSG.StandardType
