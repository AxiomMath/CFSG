module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma105
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma312

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: quotient-lift core

This module collects the generic quotient and regular-action facts used to
lift the regular normal subgroup from Lemma 10.3 back to `N_X(P)`.  None of
the declarations assumes a conclusion of Lemma 11.5.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise IsMulCommutative commutatorElement

universe u v

/-- If an involution centralizes an odd normal subgroup, then centralizing
its image modulo that subgroup already means centralizing the involution
itself. -/
public theorem lemma115_centralizer_comap_quotient_eq
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (hKodd : Odd (Nat.card K))
    {u0 : G} (hu : IsInvolution u0)
    (hKcent : K ≤ Subgroup.centralizer ({u0} : Set G)) :
    (Subgroup.centralizer
        ({QuotientGroup.mk' K u0} : Set (G ⧸ K))).comap
      (QuotientGroup.mk' K) =
        Subgroup.centralizer ({u0} : Set G) :=
  centralizer_comap_quotient_eq_of_odd_kernel K hKodd hu hKcent

/-- The affine factorization in the odd-kernel quotient lifts without an
extra centralizer error term. -/
public theorem lemma115_quotient_factorization_lift
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (hKodd : Odd (Nat.card K))
    {u0 : G} (hu : IsInvolution u0)
    (hKcent : K ≤ Subgroup.centralizer ({u0} : Set G))
    (Qbar : Subgroup (G ⧸ K))
    (hfactor : Qbar ⊔
      Subgroup.centralizer
        ({QuotientGroup.mk' K u0} : Set (G ⧸ K)) = ⊤) :
    Qbar.comap (QuotientGroup.mk' K) ⊔
        Subgroup.centralizer ({u0} : Set G) = ⊤ := by
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let Cbar : Subgroup (G ⧸ K) :=
    Subgroup.centralizer ({q u0} : Set (G ⧸ K))
  have hCcomap : Cbar.comap q =
      Subgroup.centralizer ({u0} : Set G) := by
    simpa [q, Cbar] using
      lemma115_centralizer_comap_quotient_eq K hKodd hu hKcent
  calc
    Qbar.comap q ⊔ Subgroup.centralizer ({u0} : Set G) =
        Qbar.comap q ⊔ Cbar.comap q := by rw [hCcomap]
    _ = (Qbar ⊔ Cbar).comap q :=
      Subgroup.comap_sup_eq q Qbar Cbar (QuotientGroup.mk'_surjective K)
    _ = ⊤ := by
      have htop : Qbar ⊔ Cbar = ⊤ := by
        simpa [Cbar, q] using hfactor
      rw [htop]
      simp

/-- Cardinality of the full preimage of a quotient subgroup. -/
public theorem lemma115_card_quotient_subgroup_comap
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (Qbar : Subgroup (G ⧸ K)) :
    Nat.card (Qbar.comap (QuotientGroup.mk' K)) =
      Nat.card K * Nat.card Qbar := by
  change Nat.card ((Qbar.comap (QuotientGroup.mk' K) : Set G)) =
    Nat.card K * Nat.card Qbar
  rw [Nat.card_coe_set_eq]
  simpa [Subgroup.mem_comap] using
    (QuotientGroup.card_preimage_mk K (Qbar : Set (G ⧸ K)))

/-- A quotient subgroup of odd order over an odd kernel has an
involution-invariant Sylow subgroup at every odd prime. -/
public theorem lemma115_exists_invariant_sylow_in_quotient_preimage
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (hKodd : Odd (Nat.card K))
    {u0 : G} (hu : IsInvolution u0)
    (Qbar : Subgroup (G ⧸ K)) (hQbarNormal : Qbar.Normal)
    (hQbarOdd : Odd (Nat.card Qbar))
    {f : ℕ} (hf : f.Prime) :
    ∃ Q : Subgroup G,
      theorem4bIsSylowSubgroupOf f Q
          (Qbar.comap (QuotientGroup.mk' K)) ∧
        Q ≤ Qbar.comap (QuotientGroup.mk' K) ∧
        u0 ∈ Subgroup.normalizer (Q : Set G) := by
  let H : Subgroup G := Qbar.comap (QuotientGroup.mk' K)
  have hHnormal : H.Normal :=
    hQbarNormal.comap (QuotientGroup.mk' K)
  have hHodd : Odd (Nat.card H) := by
    rw [show Nat.card H = Nat.card K * Nat.card Qbar by
      simpa [H] using lemma115_card_quotient_subgroup_comap K Qbar]
    exact hKodd.mul hQbarOdd
  have huNormH : u0 ∈ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hHnormal]
    trivial
  have hbotp : IsPGroup f (⊥ : Subgroup G) := by
    apply IsPGroup.of_card (n := 0)
    simp
  have huNormBot : u0 ∈
      Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (by infer_instance)]
    trivial
  obtain ⟨Q, hQsyl, _hbotQ, huNormQ⟩ :=
    theorem4b_exists_invariant_sylow_containing
      hHodd hu huNormH hf hbotp bot_le huNormBot
  have hQH : Q ≤ H := by
    rcases hQsyl with ⟨S, rfl⟩
    exact Subgroup.map_subtype_le (S : Subgroup H)
  exact ⟨Q, by simpa [H] using hQsyl,
    by simpa [H] using hQH, huNormQ⟩

/-- A Sylow subgroup of the full preimage maps onto the quotient subgroup
which is itself a group at that prime. -/
public theorem lemma115_sylow_preimage_map_eq_quotient_subgroup
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal]
    (Qbar : Subgroup (G ⧸ K)) {f : ℕ} (hf : f.Prime)
    (hQbarf : IsPGroup f Qbar)
    (Q : Subgroup G)
    (hQsyl : theorem4bIsSylowSubgroupOf f Q
      (Qbar.comap (QuotientGroup.mk' K))) :
    Q.map (QuotientGroup.mk' K) = Qbar := by
  classical
  letI : Fact f.Prime := ⟨hf⟩
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let H : Subgroup G := Qbar.comap q
  let phi : H →* Qbar :=
    (q.comp H.subtype).codRestrict Qbar (by
      intro x
      exact x.property)
  have hphiSurj : Function.Surjective phi := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective K (y : G ⧸ K)
    let xH : H := ⟨x, by
      change q x ∈ Qbar
      rw [show q x = (y : G ⧸ K) by simpa [q] using hx]
      exact y.property⟩
    refine ⟨xH, ?_⟩
    apply Subtype.ext
    exact hx
  rcases hQsyl with ⟨S, hQeq⟩
  let Sbar : Sylow f Qbar := S.mapSurjective hphiSurj
  have hSbarTop : (Sbar : Subgroup Qbar) = ⊤ := by
    exact (Sbar.is_maximal' (hQbarf.to_subgroup (⊤ : Subgroup Qbar)) le_top).symm
  have hmapPhi : (S : Subgroup H).map phi = ⊤ := by
    simpa [Sbar, Sylow.coe_mapSurjective] using hSbarTop
  have hQH : Q ≤ H := by
    rw [hQeq]
    exact Subgroup.map_subtype_le (S : Subgroup H)
  apply le_antisymm
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨s, hsQ, rfl⟩
    simpa [H, q] using hQH hsQ
  · intro y hyQbar
    let ybar : Qbar := ⟨y, hyQbar⟩
    have hyTop : ybar ∈ (⊤ : Subgroup Qbar) := trivial
    rw [← hmapPhi] at hyTop
    rcases Subgroup.mem_map.mp hyTop with ⟨s, hsS, hsy⟩
    have hsQ : (s : G) ∈ Q := by
      rw [hQeq]
      exact Subgroup.mem_map.mpr ⟨s, hsS, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(s : G), hsQ, ?_⟩
    exact congrArg Subtype.val hsy

/-- The quotient Sylow lift remains disjoint from an odd kernel and is
inverted elementwise by the selected involution. -/
public theorem lemma115_exists_invariant_inverted_sylow_lift
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (hKodd : Odd (Nat.card K))
    {p f : ℕ} (hp : p.Prime) (hf : f.Prime) (hpf : p ≠ f)
    (hKp : IsPGroup p K)
    {u0 : G} (hu : IsInvolution u0)
    (Qbar : Subgroup (G ⧸ K)) (hQbarNormal : Qbar.Normal)
    (hQbarOdd : Odd (Nat.card Qbar))
    (hQbarf : IsPGroup f Qbar)
    (hQbarInv : ∀ q : G ⧸ K, q ∈ Qbar →
      rightConjugateElem q (QuotientGroup.mk' K u0) = q⁻¹) :
    ∃ Q : Subgroup G,
      theorem4bIsSylowSubgroupOf f Q
          (Qbar.comap (QuotientGroup.mk' K)) ∧
        Q.map (QuotientGroup.mk' K) = Qbar ∧
        u0 ∈ Subgroup.normalizer (Q : Set G) ∧
        Disjoint Q K ∧
        (∀ q : G, q ∈ Q → rightConjugateElem q u0 = q⁻¹) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact f.Prime := ⟨hf⟩
  obtain ⟨Q, hQsyl, _hQH, huNormQ⟩ :=
    lemma115_exists_invariant_sylow_in_quotient_preimage
      K hKodd hu Qbar hQbarNormal hQbarOdd hf
  have hQmap : Q.map (QuotientGroup.mk' K) = Qbar :=
    lemma115_sylow_preimage_map_eq_quotient_subgroup
      K Qbar hf hQbarf Q hQsyl
  have hQf : IsPGroup f Q := by
    rcases hQsyl with ⟨S, rfl⟩
    exact S.isPGroup'.map
      (Qbar.comap (QuotientGroup.mk' K)).subtype
  have hdisj : Disjoint Q K :=
    IsPGroup.disjoint_of_ne f p (Ne.symm hpf) Q K hQf hKp
  have huInvQ : ∀ q : G, q ∈ Q →
      rightConjugateElem q u0 = q⁻¹ := by
    intro q hqQ
    let qc : G := rightConjugateElem q u0
    have hqcQ : qc ∈ Q := by
      dsimp [qc, rightConjugateElem]
      simpa [hu.inv_eq_self] using
        (Subgroup.mem_normalizer_iff.mp huNormQ q).mp hqQ
    have hqbar : QuotientGroup.mk' K q ∈ Qbar := by
      rw [← hQmap]
      exact Subgroup.mem_map_of_mem (QuotientGroup.mk' K) hqQ
    have hmapqc : QuotientGroup.mk' K qc =
        (QuotientGroup.mk' K q)⁻¹ := by
      simpa [qc, rightConjugateElem] using
        hQbarInv (QuotientGroup.mk' K q) hqbar
    have hcK : qc * q ∈ K := by
      apply (QuotientGroup.eq_one_iff (N := K) (x := qc * q)).mp
      change QuotientGroup.mk' K qc * QuotientGroup.mk' K q = 1
      rw [hmapqc]
      exact inv_mul_cancel (QuotientGroup.mk' K q)
    have hcQ : qc * q ∈ Q := Q.mul_mem hqcQ hqQ
    have hcOne : qc * q = 1 :=
      Subgroup.disjoint_def.mp hdisj hcQ hcK
    exact eq_inv_of_mul_eq_one_left hcOne
  exact ⟨Q, hQsyl, hQmap, huNormQ, hdisj, huInvQ⟩

/-- An odd subgroup inverted by an involution centralizes every normal
subgroup fixed elementwise by that involution. -/
public theorem lemma115_inverted_odd_subgroup_centralizes_fixed_normal_subgroup
    {G : Type u} [Group G] [Finite G]
    (K Q : Subgroup G) [K.Normal] (hQodd : Odd (Nat.card Q))
    {u0 : G} (hu : IsInvolution u0)
    (hKcent : K ≤ Subgroup.centralizer ({u0} : Set G))
    (hQinv : ∀ q : G, q ∈ Q →
      rightConjugateElem q u0 = q⁻¹) :
    Q ≤ Subgroup.centralizer (K : Set G) := by
  have huu : u0 * u0 = 1 := by
    simpa [pow_two] using hu.sq_eq_one
  have hKfix : ∀ {k : G}, k ∈ K →
      rightConjugateElem k u0 = k := by
    intro k hk
    have hku : k * u0 = u0 * k :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKcent hk)
    change u0⁻¹ * k * u0 = k
    rw [hu.inv_eq_self]
    calc
      u0 * k * u0 = k * (u0 * u0) := by rw [← hku]; group
      _ = k := by rw [huu, mul_one]
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨rQ, hrQ⟩ :=
    hQodd.coprime_two_right.pow_left_bijective.surjective
      (⟨q, hq⟩ : Q)
  let r : G := rQ
  have hr : r ∈ Q := rQ.property
  have hrSq : r ^ 2 = q := congrArg Subtype.val hrQ
  have hxK : r⁻¹ * k * r ∈ K := by
    simpa [r] using
      (show K.Normal from inferInstance).conj_mem k hk (r⁻¹)
  have hconj :
      rightConjugateElem (r⁻¹ * k * r) u0 = r * k * r⁻¹ := by
    calc
      rightConjugateElem (r⁻¹ * k * r) u0 =
          (rightConjugateElem r u0)⁻¹ *
            rightConjugateElem k u0 * rightConjugateElem r u0 := by
              simp [rightConjugateElem, mul_assoc]
      _ = r * k * r⁻¹ := by rw [hQinv r hr, hKfix hk]; simp
  have heq : r⁻¹ * k * r = r * k * r⁻¹ := by
    calc
      r⁻¹ * k * r = rightConjugateElem (r⁻¹ * k * r) u0 :=
        (hKfix hxK).symm
      _ = r * k * r⁻¹ := hconj
  symm
  calc
    q * k = r ^ 2 * k := by rw [hrSq]
    _ = r * (r * k * r⁻¹) * r := by simp [pow_two, mul_assoc]
    _ = r * (r⁻¹ * k * r) * r := by rw [← heq]
    _ = k * r ^ 2 := by simp [pow_two, mul_assoc]
    _ = k * q := by rw [hrSq]

/-- In a product of a fixed odd normal subgroup and an inverted odd subgroup,
the elements inverted by the involution are exactly the lifted subgroup. -/
public theorem lemma115_antiFixed_eq_odd_lift
    {G : Type u} [Group G] [Finite G]
    (K Q : Subgroup G) [K.Normal] (hKodd : Odd (Nat.card K))
    {u0 : G} (hu : IsInvolution u0)
    (hKcent : K ≤ Subgroup.centralizer ({u0} : Set G))
    (hQinv : ∀ q : G, q ∈ Q →
      rightConjugateElem q u0 = q⁻¹)
    (hQKcent : Q ≤ Subgroup.centralizer (K : Set G)) :
    ∀ x : G, x ∈ K ⊔ Q →
      (rightConjugateElem x u0 = x⁻¹ ↔ x ∈ Q) := by
  have huu : u0 * u0 = 1 := by
    simpa [pow_two] using hu.sq_eq_one
  have hKfix : ∀ {k : G}, k ∈ K →
      rightConjugateElem k u0 = k := by
    intro k hk
    have hku : k * u0 = u0 * k :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKcent hk)
    change u0⁻¹ * k * u0 = k
    rw [hu.inv_eq_self]
    calc
      u0 * k * u0 = k * (u0 * u0) := by rw [← hku]; group
      _ = k := by rw [huu, mul_one]
  intro x hx
  constructor
  · intro hanti
    rcases Subgroup.mem_sup_of_normal_left.mp hx with
      ⟨k, hk, q, hq, hprod⟩
    have hxprod : x = k * q := hprod.symm
    have hqk : q * k = k * q := (hQKcent hq k hk).symm
    have hqinvkinv : q⁻¹ * k⁻¹ = k⁻¹ * q⁻¹ := by
      have h := congrArg (fun z : G => z⁻¹) hqk
      simpa [mul_inv_rev] using h.symm
    have hleft : rightConjugateElem (k * q) u0 = k * q⁻¹ := by
      calc
        rightConjugateElem (k * q) u0 =
            rightConjugateElem k u0 * rightConjugateElem q u0 := by
              simp [rightConjugateElem, mul_assoc]
        _ = k * q⁻¹ := by rw [hKfix hk, hQinv q hq]
    have hkeq : k * q⁻¹ = k⁻¹ * q⁻¹ := by
      calc
        k * q⁻¹ = rightConjugateElem (k * q) u0 := hleft.symm
        _ = (k * q)⁻¹ := by rw [← hxprod, hanti]
        _ = q⁻¹ * k⁻¹ := by simp [mul_inv_rev]
        _ = k⁻¹ * q⁻¹ := hqinvkinv
    have hkEqInv : k = k⁻¹ := by
      exact mul_right_cancel hkeq
    have hkSq : k ^ 2 = 1 := by
      calc
        k ^ 2 = k * k := pow_two k
        _ = k * k⁻¹ := congrArg (fun z : G => k * z) hkEqInv
        _ = 1 := mul_inv_cancel k
    have hkOne : k = 1 := by
      let kK : K := ⟨k, hk⟩
      have hkSqK : kK ^ 2 = (1 : K) ^ 2 := by
        apply Subtype.ext
        simpa [hkSq]
      have hkKone : kK = 1 :=
        hKodd.coprime_two_right.pow_left_bijective.injective hkSqK
      exact congrArg Subtype.val hkKone
    rw [hxprod, hkOne, one_mul]
    exact hq
  · intro hq
    exact hQinv x hq

/-- A normal ambient subgroup's anti-fixed subgroup is normalized by the
centralizer of the acting element. -/
public theorem lemma115_centralizer_le_normalizer_of_antiFixed_subgroup
    {G : Type u} [Group G] [Finite G]
    (H Q : Subgroup G) [H.Normal] {u0 : G}
    (hQH : Q ≤ H)
    (hanti : ∀ x : G, x ∈ H →
      (rightConjugateElem x u0 = x⁻¹ ↔ x ∈ Q)) :
    Subgroup.centralizer ({u0} : Set G) ≤
      Subgroup.normalizer (Q : Set G) := by
  let C : Subgroup G := Subgroup.centralizer ({u0} : Set G)
  apply subgroup_le_normalizer_of_conj_mem Q C
  intro c q hq
  have hcu : (c : G) * u0 = u0 * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp c.property
  have hcfix : rightConjugateElem (c : G) u0 = (c : G) := by
    dsimp [rightConjugateElem]
    calc
      u0⁻¹ * (c : G) * u0 = u0⁻¹ * ((c : G) * u0) := by
        rw [mul_assoc]
      _ = u0⁻¹ * (u0 * (c : G)) := by rw [hcu]
      _ = (c : G) := by simp
  have hqH : q ∈ H := hQH hq
  have hconjH : (c : G) * q * (c : G)⁻¹ ∈ H :=
    (show H.Normal from inferInstance).conj_mem q hqH (c : G)
  apply (hanti ((c : G) * q * (c : G)⁻¹) hconjH).mp
  calc
    rightConjugateElem ((c : G) * q * (c : G)⁻¹) u0 =
        rightConjugateElem (c : G) u0 *
          rightConjugateElem q u0 *
            (rightConjugateElem (c : G) u0)⁻¹ := by
              simp [rightConjugateElem, mul_assoc]
    _ = (c : G) * q⁻¹ * (c : G)⁻¹ := by
      rw [hcfix, (hanti q hqH).mpr hq]
    _ = ((c : G) * q * (c : G)⁻¹)⁻¹ := by group

/-- The quotient factorization and the odd fixed-kernel lift make the lifted
subgroup normal in the ambient group and recover the source factorization. -/
public theorem lemma115_odd_lift_normal_factorization
    {G : Type u} [Group G] [Finite G]
    (K Q : Subgroup G) [K.Normal] (hKodd : Odd (Nat.card K))
    (Qbar : Subgroup (G ⧸ K)) (hQbarNormal : Qbar.Normal)
    {u0 : G} (hu : IsInvolution u0)
    (hKcent : K ≤ Subgroup.centralizer ({u0} : Set G))
    (hQmap : Q.map (QuotientGroup.mk' K) = Qbar)
    (hQodd : Odd (Nat.card Q))
    (hQinv : ∀ q : G, q ∈ Q →
      rightConjugateElem q u0 = q⁻¹)
    (hfactor : Qbar ⊔
      Subgroup.centralizer
        ({QuotientGroup.mk' K u0} : Set (G ⧸ K)) = ⊤) :
    Q.Normal ∧
      Q ⊔ Subgroup.centralizer ({u0} : Set G) = ⊤ ∧
      (∀ x : G, x ∈ Qbar.comap (QuotientGroup.mk' K) →
        (rightConjugateElem x u0 = x⁻¹ ↔ x ∈ Q)) := by
  let H : Subgroup G := Qbar.comap (QuotientGroup.mk' K)
  have hHnormal : H.Normal := hQbarNormal.comap (QuotientGroup.mk' K)
  have hQH : Q ≤ H := by
    intro q hq
    change QuotientGroup.mk' K q ∈ Qbar
    rw [← hQmap]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' K) hq
  have hHeq : H = K ⊔ Q := by
    calc
      H = (Q.map (QuotientGroup.mk' K)).comap
          (QuotientGroup.mk' K) := by simp [H, hQmap]
      _ = K ⊔ Q := QuotientGroup.comap_map_mk' K Q
  have hQKcent : Q ≤ Subgroup.centralizer (K : Set G) :=
    lemma115_inverted_odd_subgroup_centralizes_fixed_normal_subgroup
      K Q hQodd hu hKcent hQinv
  have hanti : ∀ x : G, x ∈ H →
      (rightConjugateElem x u0 = x⁻¹ ↔ x ∈ Q) := by
    intro x hx
    rw [hHeq] at hx
    exact lemma115_antiFixed_eq_odd_lift K Q hKodd hu hKcent hQinv hQKcent x hx
  have hfactorLift : H ⊔ Subgroup.centralizer ({u0} : Set G) = ⊤ := by
    simpa [H] using lemma115_quotient_factorization_lift K
      hKodd hu hKcent Qbar hfactor
  have hKnorm : K ≤ Subgroup.normalizer (Q : Set G) := by
    have hKcentQ : K ≤ Subgroup.centralizer (Q : Set G) :=
      (Subgroup.le_centralizer_iff (H := Q) (K := K)).mp hQKcent
    exact hKcentQ.trans (centralizer_le_normalizer Q)
  have hHnorm : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hHeq]
    exact sup_le hKnorm Subgroup.le_normalizer
  have hCnorm : Subgroup.centralizer ({u0} : Set G) ≤
      Subgroup.normalizer (Q : Set G) :=
    lemma115_centralizer_le_normalizer_of_antiFixed_subgroup
      H Q hQH hanti
  have hnormTop : Subgroup.normalizer (Q : Set G) = ⊤ := by
    apply top_unique
    rw [← hfactorLift]
    exact sup_le hHnorm hCnorm
  have hQnormal : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hnormTop
  have hQfactor : Q ⊔ Subgroup.centralizer ({u0} : Set G) = ⊤ := by
    have hKleQC : K ≤ Q ⊔ Subgroup.centralizer ({u0} : Set G) :=
      hKcent.trans le_sup_right
    calc
      Q ⊔ Subgroup.centralizer ({u0} : Set G) =
          K ⊔ (Q ⊔ Subgroup.centralizer ({u0} : Set G)) :=
        (sup_eq_right.mpr hKleQC).symm
      _ = (K ⊔ Q) ⊔ Subgroup.centralizer ({u0} : Set G) :=
        (sup_assoc K Q (Subgroup.centralizer ({u0} : Set G))).symm
      _ = H ⊔ Subgroup.centralizer ({u0} : Set G) := by rw [hHeq]
      _ = ⊤ := hfactorLift
  exact ⟨hQnormal, hQfactor, hanti⟩

/-- In the lifted product, the commutator with the involution is precisely
the inverted odd factor. -/
public theorem lemma115_commutator_odd_lift_eq
    {G : Type u} [Group G] [Finite G]
    (K Q : Subgroup G) [K.Normal] [Q.Normal]
    (hQodd : Odd (Nat.card Q)) {u0 : G} (hu : IsInvolution u0)
    (hKcent : K ≤ Subgroup.centralizer ({u0} : Set G))
    (hQinv : ∀ q : G, q ∈ Q →
      rightConjugateElem q u0 = q⁻¹) :
    ⁅K ⊔ Q, Subgroup.zpowers u0⁆ = Q := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx z hz
    apply (QuotientGroup.eq_one_iff (N := Q) (x := ⁅x, z⁆)).mp
    change QuotientGroup.mk' Q ⁅x, z⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_commute.mpr
    rcases Subgroup.mem_sup_of_normal_left.mp hx with
      ⟨k, hk, q, hq, hprod⟩
    have hku : Commute k u0 :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKcent hk)
    have hmapq : QuotientGroup.mk' Q q = 1 := by
      simpa [QuotientGroup.mk'_apply] using
        (QuotientGroup.eq_one_iff (N := Q) q).mpr hq
    have hmapx : QuotientGroup.mk' Q x = QuotientGroup.mk' Q k := by
      calc
        QuotientGroup.mk' Q x = QuotientGroup.mk' Q (k * q) :=
          congrArg (QuotientGroup.mk' Q) hprod.symm
        _ = QuotientGroup.mk' Q k * QuotientGroup.mk' Q q := by
          rw [map_mul]
        _ = QuotientGroup.mk' Q k * 1 := by rw [hmapq]
        _ = QuotientGroup.mk' Q k := by simp
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    rw [hmapx, map_zpow]
    exact (hku.map (QuotientGroup.mk' Q)).zpow_right n
  · intro q hq
    obtain ⟨rQ, hrQ⟩ :=
      hQodd.coprime_two_right.pow_left_bijective.surjective
        (⟨q, hq⟩ : Q)
    let r : G := rQ
    have hr : r ∈ Q := rQ.property
    have hrSq : r ^ 2 = q := congrArg Subtype.val hrQ
    have hconj : u0 * r * u0 = r⁻¹ := by
      simpa [rightConjugateElem, hu.inv_eq_self] using hQinv r hr
    have hconjInv : u0 * r⁻¹ * u0 = r := by
      have h := congrArg (fun y : G => y⁻¹) hconj
      simpa [mul_inv_rev, hu.inv_eq_self, mul_assoc] using h
    have hcommEq : ⁅r, u0⁆ = r ^ 2 := by
      calc
        ⁅r, u0⁆ = r * u0 * r⁻¹ * u0⁻¹ :=
          commutatorElement_def r u0
        _ = r * u0 * r⁻¹ * u0 := by rw [hu.inv_eq_self]
        _ = r * (u0 * r⁻¹ * u0) := by group
        _ = r ^ 2 := by rw [hconjInv]; simp [pow_two]
    have hc : ⁅r, u0⁆ ∈ ⁅K ⊔ Q, Subgroup.zpowers u0⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_sup_right hr)
        (Subgroup.mem_zpowers u0)
    rw [hcommEq, hrSq] at hc
    exact hc

/-- A regular normal commutative subgroup is inverted by an involution with a
unique fixed point. -/
public theorem lemma115_regular_normal_inverted_by_unique_fixed_involution
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    [FaithfulSMul G Omega]
    (Q : Subgroup G) (hQnormal : Q.Normal)
    (hQcomm : IsMulCommutative Q)
    (hQregular : ∀ omega : Omega,
      MulAction.stabilizer Q omega = ⊥)
    {u0 : G} (hu : IsInvolution u0) (alpha : Omega)
    (hualpha : u0 • alpha = alpha)
    (huunique : ∀ omega : Omega,
      u0 • omega = omega → omega = alpha) :
    ∀ q : G, q ∈ Q → rightConjugateElem q u0 = q⁻¹ := by
  classical
  letI : Q.Normal := hQnormal
  letI : IsMulCommutative Q := hQcomm
  have hconj_fixed_one {q : G} (hq : q ∈ Q)
      (hqu : rightConjugateElem q u0 = q) : q = 1 := by
    let qQ : Q := ⟨q, hq⟩
    change u0⁻¹ * q * u0 = q at hqu
    have hcomm : Commute q u0 := by
      rw [commute_iff_eq]
      calc
        q * u0 = u0 * (u0⁻¹ * q * u0) := by group
        _ = u0 * q := by rw [hqu]
    have hfix : u0 • (qQ • alpha) = qQ • alpha := by
      change u0 • (q • alpha) = q • alpha
      calc
        u0 • (q • alpha) = (u0 * q) • alpha := by rw [mul_smul]
        _ = (q * u0) • alpha := by rw [hcomm.eq]
        _ = q • (u0 • alpha) := by rw [mul_smul]
        _ = q • alpha := by rw [hualpha]
    have hqfix : qQ • alpha = alpha := huunique (qQ • alpha) hfix
    have hqstab : qQ ∈ MulAction.stabilizer Q alpha := hqfix
    rw [hQregular alpha] at hqstab
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hqstab)
  intro q hq
  let qu : G := rightConjugateElem q u0
  have hquQ : qu ∈ Q := by
    dsimp [qu, rightConjugateElem]
    simpa [hu.inv_eq_self] using hQnormal.conj_mem q hq u0
  have htwice : rightConjugateElem qu u0 = q := by
    have huu : u0 * u0 = 1 := by
      simpa [pow_two] using hu.sq_eq_one
    dsimp [qu, rightConjugateElem]
    rw [hu.inv_eq_self]
    calc
      u0 * (u0 * q * u0) * u0 =
          (u0 * u0) * q * (u0 * u0) := by group
      _ = q := by rw [huu]; simp
  have hcomm : q * qu = qu * q :=
    congrArg Subtype.val
      (mul_comm (⟨q, hq⟩ : Q) (⟨qu, hquQ⟩ : Q))
  have hprod_fixed : rightConjugateElem (q * qu) u0 = q * qu := by
    calc
      rightConjugateElem (q * qu) u0 =
          rightConjugateElem q u0 * rightConjugateElem qu u0 := by
            simp [rightConjugateElem, mul_assoc]
      _ = qu * q := by rw [htwice]
      _ = q * qu := hcomm.symm
  have hprod_one : q * qu = 1 :=
    hconj_fixed_one (Q.mul_mem hq hquQ) hprod_fixed
  calc
    rightConjugateElem q u0 = qu := rfl
    _ = q⁻¹ * (q * qu) := by group
    _ = q⁻¹ := by rw [hprod_one]; simp

end CFSG.BenderSuzuki
