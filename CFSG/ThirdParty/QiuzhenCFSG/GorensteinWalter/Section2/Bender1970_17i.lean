module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarCommute
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent

namespace CFSG
end CFSG
open CFSG

set_option maxHeartbeats 400000

/-!
# Bender (1970), Statement 1.7(i)

The final proof of (i) is assembled from the shared F*-subnormal helpers in
`GorensteinWalter.Section2.FStarSubnormal` and the registered residual
commutator-assembly bridge currently being proved by the owner of
`GorensteinWalter.Section2.FStarCommute` (task `gw4`).
-/

noncomputable section

open scoped Pointwise commutatorElement BigOperators

namespace CFSG.GorensteinWalter

universe u v

/-! ## Local q-core helpers used by the residual assembly -/

/-- A subnormal `p`-subgroup of `B` lies in `O_p(B)`. -/
private theorem le_qCoreOf_of_isSubnormal_isPGroup_local
    {G : Type u} [Group G] [Finite G]
    (B S : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hSB : S ≤ B) (hS : (S.subgroupOf B).IsSubnormal) (hSp : IsPGroup p S) :
    S ≤ qCoreOf B p := by
  rcases (Subgroup.IsSubnormal.isSubnormal_iff (G := ↥B) (H := S.subgroupOf B)).1 hS with
    ⟨n, f, hmono, hnorm, hf0, hfn⟩
  have hmain : ∀ i : ℕ, i ≤ n → S ≤ qCoreOf ((f i).map B.subtype) p := by
    intro i hi
    induction i with
    | zero =>
      have hK0 : (f 0).map B.subtype = S := by
        rw [hf0]
        exact Subgroup.map_subgroupOf_eq_of_le hSB
      have hSleK : S ≤ (f 0).map B.subtype := by rw [hK0]
      have hSnorm : IsNormalIn S ((f 0).map B.subtype) := by
        rw [hK0]
        refine ⟨le_rfl, ?_⟩
        intro a ha x hx
        exact S.mul_mem (S.mul_mem ha hx) (S.inv_mem ha)
      exact le_qCoreOf_of_normal_isPGroup ((f 0).map B.subtype) S p hSleK (by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hSleK]
        exact le_normalizer_of_isNormalIn hSnorm) hSp
    | succ i ih =>
      have hKi : IsNormalIn ((f i).map B.subtype) ((f (i + 1)).map B.subtype) := by
        refine ⟨Subgroup.map_mono (f := B.subtype) (hmono (Nat.le_succ i)), ?_⟩
        intro b hb x hx
        rcases (Subgroup.mem_map).1 hx with ⟨x0, hx0, rfl⟩
        rcases (Subgroup.mem_map).1 hb with ⟨b0, hb0, rfl⟩
        have hconj : b0 * x0 * b0⁻¹ ∈ f i :=
          (Subgroup.normal_subgroupOf_iff (hmono (Nat.le_succ i))).mp (hnorm i)
            x0 b0 hx0 hb0
        exact Subgroup.mem_map.mpr ⟨b0 * x0 * b0⁻¹, hconj, by simp [mul_assoc]⟩
      have hQleK : S ≤ qCoreOf ((f i).map B.subtype) p :=
        ih (Nat.le_of_succ_le hi)
      have hQleN : qCoreOf ((f i).map B.subtype) p ≤ qCoreOf ((f (i + 1)).map B.subtype) p := by
        exact qCoreOf_le_qCoreOf_of_isNormalIn
          ((f i).map B.subtype) ((f (i + 1)).map B.subtype) p hKi
      exact hQleK.trans hQleN
  have hSleB : S ≤ qCoreOf B p := by
    have h := hmain n (le_rfl)
    have htop : (⊤ : Subgroup (↥B)).map B.subtype = B := by
      simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := B))
    rw [hfn] at h
    simpa [htop] using h
  exact hSleB

/-- `O_q(A) ≤ O^s(F*(A))` for distinct primes. -/
private theorem qCoreOf_le_pResidualOf_of_ne_local
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p s : ℕ) (hp : p.Prime) (hs : s.Prime) (hne : p ≠ s) :
    qCoreOf A p ≤ pResidualOf (generalizedFittingSubgroupOf A) s := by
  let H : Subgroup G := generalizedFittingSubgroupOf A
  intro x hx
  have hxH : x ∈ H :=
    (fstar_qCoreOf_le_fittingSubgroupOf A p hp).trans le_sup_left hx
  let xQ : ↥(qCoreOf A p) := ⟨x, hx⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact s.Prime := ⟨hs⟩
  rcases (IsPGroup.iff_orderOf.mp (qCoreOf_isPGroup A p)) xQ with ⟨k, hk⟩
  have hpndvd : ¬ p ∣ s := by
    intro hdiv
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hs).mp hdiv)
  have hcopPow : Nat.Coprime s (p ^ k) := hp.coprime_pow_of_not_dvd hpndvd
  have hord : orderOf x = orderOf xQ :=
    (orderOf_injective (qCoreOf A p).subtype (qCoreOf A p).subtype_injective xQ)
  have hcop : Nat.Coprime s (orderOf x) := by
    rw [hord, hk]
    exact hcopPow
  exact fstar_mem_pResidualOf_of_order_coprime H s hs hxH hcop

/-- `O^p(H) ≤ O^p(K)` when `H ≤ K`. -/
private theorem pResidualOf_mono_local
    {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} (hHK : H ≤ K) (p : ℕ) (hp : p.Prime) :
    pResidualOf H p ≤ pResidualOf K p := by
  intro x hx
  rcases (Subgroup.mem_map).1 hx with ⟨hH, hhH, hxeq⟩
  subst hxeq
  have hxK : (hH : G) ∈ K := hHK hH.2
  refine Subgroup.mem_map.mpr ⟨⟨(hH : G), hxK⟩, ?_, rfl⟩
  rw [Subgroup.mem_sInf]
  intro N hN
  rcases hN with ⟨hNnorm, n, hn⟩
  let L : Subgroup G := N.map K.subtype
  let M : Subgroup G := H ⊓ L
  have hMleH : M ≤ H := inf_le_left
  have hML : M ≤ L := inf_le_right
  have hNmap : IsNormalIn L K := by
    refine ⟨Subgroup.map_subtype_le N, ?_⟩
    intro k hk z hz
    rcases (Subgroup.mem_map).1 hz with ⟨n, hnN, rfl⟩
    have hmemK : k * (n : G) * k⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem hk (n : ↥K).2) (K.inv_mem hk)
    refine Subgroup.mem_map.mpr ⟨⟨k * (n : G) * k⁻¹, hmemK⟩, ?_, rfl⟩
    exact hNnorm.conj_mem n hnN ⟨k, hk⟩
  have hMnorm : (M.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMleH]
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact ⟨H.mul_mem (H.mul_mem hh hy.1) (H.inv_mem hh),
        hNmap.2 h (hHK hh) y hy.2⟩
    · intro hy
      have hyH : y ∈ H := by
        have h' := H.mul_mem (H.mul_mem (H.inv_mem hh) hy.1) hh
        simpa [mul_assoc] using h'
      have hyL : y ∈ L := by
        have h' := hNmap.2 h⁻¹ (hHK (H.inv_mem hh)) (h * y * h⁻¹) hy.2
        simpa [mul_assoc] using h'
      exact ⟨hyH, hyL⟩
  have hMindex : ∃ m : ℕ, (M.subgroupOf H).index = p ^ m := by
    let H0 : Subgroup (↥K) := H.subgroupOf K
    have hNrel : (N.subgroupOf H0).index ∣ N.index := by
      have hle1 : N ≤ H0 ⊔ N := le_sup_right
      have hdiv : (N.subgroupOf (H0 ⊔ N)).index ∣ N.index :=
        (Subgroup.relIndex_dvd_index_of_le hle1)
      have hsup : (N.subgroupOf H0).index = (N.subgroupOf (H0 ⊔ N)).index := by
        exact (Subgroup.relIndex_sup_right (H := H0) (K := N)).symm
      rwa [hsup]
    have hmap : (M.subgroupOf H).index = (N.subgroupOf H0).index := by
      have h := Subgroup.relIndex_map_map_of_injective (G := ↥K) (G' := G)
        (f := K.subtype) (H := N) (K := H0) K.subtype_injective
      have hmapH : (H0.map K.subtype) = H := Subgroup.map_subgroupOf_eq_of_le hHK
      have hMsub : (L.subgroupOf H) = M.subgroupOf H := by
        ext y
        simp [M, L]
      rw [hmapH] at h
      simpa [Subgroup.relIndex, ← hMsub] using h
    rw [hmap]
    have hpdiv : p.Prime := hp
    rcases (Nat.dvd_prime_pow hpdiv).mp (hNrel.trans (by rw [hn])) with ⟨m, _hm, hm⟩
    exact ⟨m, hm⟩
  have hResM : pResidualOf H p ≤ M := by
    let : Fact p.Prime := ⟨hp⟩
    have hQ : IsPGroup p (H ⧸ (M.subgroupOf H)) := by
      rcases hMindex with ⟨m, hm⟩
      refine IsPGroup.of_card (n := m) ?_
      rw [← hm]
      exact (Subgroup.index_eq_card (M.subgroupOf H)).symm
    exact fstar_pResidualOf_le_of_quotient_isPGroup H M p hp hMleH hMnorm hQ
  have hxM : (hH : G) ∈ M := hResM (Subgroup.mem_map.mpr ⟨hH, hhH, rfl⟩)
  have hxL : (hH : G) ∈ L := hML hxM
  rcases (Subgroup.mem_map).1 hxL with ⟨k, hkN, hk⟩
  have hkN' : (⟨(hH : G), hxK⟩ : ↥K) ∈ N := by
    convert hkN using 1
    ext
    exact hk.symm
  exact hkN'

/-- `O_q(A) ≤ O^p(F(A))` for distinct primes. -/
private theorem qCoreOf_le_pResidualOf_fitting_of_ne_local
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) :
    qCoreOf A q ≤ pResidualOf (fittingSubgroupOf A) p := by
  let F : Subgroup G := fittingSubgroupOf A
  intro x hx
  have hxF : x ∈ F := fstar_qCoreOf_le_fittingSubgroupOf A q hq hx
  let xQ : ↥(qCoreOf A q) := ⟨x, hx⟩
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hp⟩
  rcases (IsPGroup.iff_orderOf.mp (qCoreOf_isPGroup A q)) xQ with ⟨k, hk⟩
  have hqndvd : ¬ q ∣ p := by
    intro hdiv
    exact hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdiv)
  have hcopPow : Nat.Coprime p (q ^ k) := hq.coprime_pow_of_not_dvd hqndvd
  have hord : orderOf x = orderOf xQ :=
    (orderOf_injective (qCoreOf A q).subtype (qCoreOf A q).subtype_injective xQ)
  have hcop : Nat.Coprime p (orderOf x) := by
    rw [hord, hk]
    exact hcopPow
  exact fstar_mem_pResidualOf_of_order_coprime F p hp hxF hcop

/-- A join of finitely many normal `p`-subgroups is a `p`-group. -/
private theorem isPGroup_iSup_of_normal_local
    {G : Type u} [Group G] {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime]
    (X : ι → Subgroup G)
    (hX : ∀ i, IsPGroup p (X i))
    (hN : ∀ i, IsNormalIn (X i) (⨆ i, X i)) :
    IsPGroup p (↥(⨆ i, X i : Subgroup G)) := by
  classical
  have hmain : ∀ t : Finset ι, IsPGroup p (↥(⨆ i ∈ t, X i : Subgroup G)) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      have hbot : (⨆ i ∈ (∅ : Finset ι), X i) = (⊥ : Subgroup G) := by
        simp
      exact hbot ▸ (IsPGroup.of_bot : IsPGroup p (⊥ : Subgroup G))
    | insert a t ha ih =>
      let S : Subgroup G := ⨆ i ∈ t, X i
      have hSle : S ≤ ⨆ i, X i := by
        exact iSup_le (fun i => iSup_le (fun hi => le_iSup X i))
      have hSleN : S ≤ Subgroup.normalizer (X a : Set G) :=
        hSle.trans (le_normalizer_of_isNormalIn (hN a))
      have hSp : IsPGroup p S := ih
      have hXap : IsPGroup p (X a) := hX a
      have hsup : IsPGroup p (↥(S ⊔ X a : Subgroup G)) :=
        IsPGroup.to_sup_of_normal_right' hSp hXap hSleN
      rw [Finset.iSup_insert, sup_comm]
      exact hsup
  have huniv : (⨆ i ∈ (Finset.univ : Finset ι), X i) = (⨆ i, X i) := by
    simp
  exact huniv ▸ hmain Finset.univ

/-- The join of subgroups normal in `B` is normal in `B`. -/
private theorem isNormalIn_iSup_local
    {G : Type u} [Group G] {ι : Type*} (X : ι → Subgroup G) (B : Subgroup G)
    (h : ∀ i : ι, IsNormalIn (X i) B) :
    IsNormalIn (⨆ i : ι, X i) B := by
  refine ⟨?_, ?_⟩
  · exact iSup_le (fun i => (h i).1)
  · intro b hb x hx
    rw [Subgroup.iSup_eq_closure] at hx
    refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases (Set.mem_iUnion).1 hy with ⟨i, hyi⟩
      exact (le_iSup (f := fun i : ι => X i) i) ((h i).2 b hb y hyi)
    · intro y hy
      rcases (Set.mem_iUnion).1 hy with ⟨i, hyi⟩
      exact (le_iSup (f := fun i : ι => X i) i) ((h i).2 b hb y⁻¹ ((X i).inv_mem hyi))
    · simpa using (⨆ i : ι, X i).one_mem
    · intro y z _ _ hyP hzP
      simpa [mul_assoc, mul_left_comm, mul_right_comm] using (⨆ i : ι, X i).mul_mem hyP hzP

/-- `subgroupOf` distributes over an `iSup` when all terms are contained in
the intermediate subgroup. -/
private theorem subgroupOf_iSup_of_le_local
    {G : Type u} [Group G] {ι : Type v}
    {H : ι → Subgroup G} {N : Subgroup G} (hH : ∀ i, H i ≤ N) :
    (⨆ i, H i).subgroupOf N = ⨆ i, (H i).subgroupOf N := by
  classical
  apply le_antisymm
  · have hRHS_coe : (⨆ i, (H i).subgroupOf N).map N.subtype = ⨆ i, H i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr (fun i => Subgroup.map_subgroupOf_eq_of_le (hH i))
    intro x hx
    have hxG : (x : G) ∈ (⨆ i, (H i).subgroupOf N).map N.subtype := by
      rwa [hRHS_coe]
    rcases (Subgroup.mem_map).1 hxG with ⟨y, hy, hxy⟩
    have hyx : (y : ↥N) = x := N.subtype_injective hxy
    simpa [hyx] using hy
  · exact iSup_le (fun i => Subgroup.subgroupOf_mono N (le_iSup H i))

/-- If `H ≤ K` are normal and `G/H` is a `p`-group, then `G/K` is a
`p`-group. -/
private theorem isPGroup_quotient_of_le_normal_local
    {G : Type u} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) [hH : H.Normal] [hK : K.Normal] {p : ℕ} [Fact p.Prime]
    (hQ : IsPGroup p (G ⧸ H)) : IsPGroup p (G ⧸ K) := by
  let f : G ⧸ H →* G ⧸ K := QuotientGroup.map H K (MonoidHom.id G) hHK
  have hsurj : Function.Surjective f := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    exact ⟨QuotientGroup.mk' H g, rfl⟩
  exact hQ.of_surjective f hsurj

/-- `O^p(F(A))` is the join of the q-cores of `A` for `q ≠ p`. -/
private theorem pResidualOf_fitting_eq_iSup_qCoreOf_of_ne_local
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) :
    pResidualOf (fittingSubgroupOf A) p =
      ⨆ q : {q : ℕ // q.Prime ∧ q ≠ p}, qCoreOf A q.1 := by
  let F : Subgroup G := fittingSubgroupOf A
  let J : Subgroup G := ⨆ q : {q : ℕ // q.Prime ∧ q ≠ p}, qCoreOf A q.1
  let : Fact p.Prime := ⟨hp⟩
  have hFleA : F ≤ A := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  have hJleF : J ≤ F := by
    refine iSup_le ?_
    intro q
    exact fstar_qCoreOf_le_fittingSubgroupOf A q.1 q.2.1
  have hJnormF : IsNormalIn J F := by
    refine isNormalIn_iSup_local (fun q : {q : ℕ // q.Prime ∧ q ≠ p} => qCoreOf A q.1) F ?_
    intro q
    refine ⟨fstar_qCoreOf_le_fittingSubgroupOf A q.1 q.2.1, ?_⟩
    intro f hf x hx
    exact (qCoreOf_normal_in A q.1).2 f (hFleA hf) x hx
  have hJnorm : (J.subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJleF]
    exact le_normalizer_of_isNormalIn hJnormF
  apply le_antisymm
  · let π : F →* F ⧸ J.subgroupOf F := QuotientGroup.mk' (J.subgroupOf F)
    let ι := ↥((Nat.card (↥A)).primeFactors.attach)
    let Q : ι → Subgroup G := fun i => qCoreOf A i.1.1
    have hQF : ∀ i : ι, Q i ≤ F := fun i => fstar_qCoreOf_le_fittingSubgroupOf A i.1.1
      (Nat.prime_of_mem_primeFactors i.1.2)
    let Y : ι → Subgroup (F ⧸ J.subgroupOf F) :=
      fun i => ((Q i).subgroupOf F).map π
    have hYp : ∀ i : ι, IsPGroup p (Y i) := by
      intro i
      by_cases hpi : i.1.1 = p
      · have hQp : IsPGroup p ((Q i).subgroupOf F) :=
          by
            have hQp0 : IsPGroup i.1.1 ((qCoreOf A i.1.1).subgroupOf F) :=
              (qCoreOf_isPGroup A i.1.1).of_equiv
                (Subgroup.subgroupOfEquivOfLe (hQF i)).symm
            have hQp' : IsPGroup p ((qCoreOf A i.1.1).subgroupOf F) := hpi ▸ hQp0
            simpa [Q] using hQp'
        exact IsPGroup.map hQp π
      · have hQJ : Q i ≤ J := le_iSup (f := fun q : {q : ℕ // q.Prime ∧ q ≠ p} => qCoreOf A q.1)
          ⟨i.1.1, Nat.prime_of_mem_primeFactors i.1.2, hpi⟩
        have himage : Y i = ⊥ := by
          apply (Subgroup.map_eq_bot_iff (H := (Q i).subgroupOf F) (f := π)).2
          intro x hx
          have hxG : (x : G) ∈ Q i := (Subgroup.mem_subgroupOf).mp hx
          have hxJ : (x : G) ∈ J := hQJ hxG
          have hx' : (x : F) ∈ J.subgroupOf F := by
            rw [Subgroup.mem_subgroupOf]
            exact hxJ
          exact (QuotientGroup.eq_one_iff (N := J.subgroupOf F) (x := x)).2 hx'
        rw [himage]
        exact IsPGroup.of_bot
    have hQnormF : ∀ i : ι, ((Q i).subgroupOf F).Normal := by
      intro i
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hQF i)]
      exact le_normalizer_of_isNormalIn
        (show IsNormalIn (Q i) F from by
          refine ⟨hQF i, ?_⟩
          intro f hf x hx
          exact (qCoreOf_normal_in A i.1.1).2 f (hFleA hf) x hx)
    have hYnorm : ∀ i : ι, (Y i).Normal := by
      intro i
      exact (hQnormF i).map π (QuotientGroup.mk'_surjective (J.subgroupOf F))
    have hYnorm' : ∀ i : ι, IsNormalIn (Y i) (⨆ i, Y i) := by
      intro i
      refine ⟨le_iSup (f := Y) i, ?_⟩
      intro x hx y hy
      exact (hYnorm i).conj_mem y hy x
    have hYsup : IsPGroup p (↥(⨆ i, Y i : Subgroup (F ⧸ J.subgroupOf F))) :=
      isPGroup_iSup_of_normal_local Y hYp hYnorm'
    have hYtop : (⨆ i, Y i) = ⊤ := by
      have hmap : (⨆ i, Y i) = ((⨆ i, Q i).subgroupOf F).map π := by
        simp [Y]
        rw [← Subgroup.map_iSup]
        rw [← subgroupOf_iSup_of_le_local hQF]
      have hF : (⨆ i, Q i) = F := (fittingSubgroupOf_eq_iSup_qCoreOf A).symm
      have htop : ((⨆ i, Q i).subgroupOf F) = (⊤ : Subgroup F) := by
        rw [hF, Subgroup.subgroupOf_self]
      rw [hmap, htop]
      exact Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective (J.subgroupOf F))
    have hQquot : IsPGroup p (F ⧸ J.subgroupOf F) := by
      have hQtop : IsPGroup p ↥(⊤ : Subgroup (F ⧸ J.subgroupOf F)) := by
        exact hYtop ▸ hYsup
      exact hQtop.of_equiv (Subgroup.topEquiv (G := F ⧸ J.subgroupOf F))
    exact fstar_pResidualOf_le_of_quotient_isPGroup F J p hp hJleF hJnorm hQquot
  · refine iSup_le ?_
    intro q
    exact qCoreOf_le_pResidualOf_fitting_of_ne_local A p q.1 hp q.2.1 q.2.2

/-- The image of `H` in `X/N` is a `p`-group whenever it is a quotient of
`H/O^p(H)`. -/
private theorem isPGroup_quotientMap_of_le_residual_local
    {G : Type u} [Group G] [Finite G]
    {X H R : Subgroup G} (p : ℕ) (hp : p.Prime)
    (hHX : H ≤ X) (hRH : R ≤ H)
    (N : Subgroup (↥X)) [N.Normal]
    (hRN : ∀ r : G, ∀ hr : r ∈ R,
      (⟨r, hHX (hRH hr)⟩ : ↥X) ∈ N)
    (hRnormal : (R.subgroupOf H).Normal)
    (hQ : IsPGroup p (H ⧸ (R.subgroupOf H))) :
    IsPGroup p (((H.subgroupOf X) : Subgroup (↥X)).map
      (QuotientGroup.mk' N)) := by
  classical
  let π : ↥X →* ↥X ⧸ N := QuotientGroup.mk' N
  let φ : H →* ↥X := Subgroup.inclusion hHX
  let φq : H ⧸ (R.subgroupOf H) →* ↥X ⧸ N :=
    QuotientGroup.map (R.subgroupOf H) N φ (by
      intro r hr
      change φ r ∈ N
      exact hRN r (Subgroup.mem_subgroupOf.mp hr))
  have hrange : φq.range = ((H.subgroupOf X) : Subgroup (↥X)).map π := by
    ext y
    constructor
    · intro hy
      rcases (MonoidHom.mem_range).1 hy with ⟨x, rfl⟩
      refine Quotient.inductionOn' x ?_
      intro h
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hHX h,
        Subgroup.mem_subgroupOf.mpr h.2, by
          simpa [φq, φ, π] using
            (QuotientGroup.map_mk (N := R.subgroupOf H) (M := N) φ
              (by intro r hr; exact hRN r (Subgroup.mem_subgroupOf.mp hr)) h).symm⟩
    · intro hy
      rw [MonoidHom.mem_range]
      rcases (Subgroup.mem_map).1 hy with ⟨hX, hhX, rfl⟩
      have hinc : Subgroup.inclusion hHX ⟨hX.1,
          (Subgroup.mem_subgroupOf).mp hhX⟩ = hX := by
        ext
        rfl
      refine ⟨QuotientGroup.mk' (R.subgroupOf H) ⟨hX.1,
        (Subgroup.mem_subgroupOf).mp hhX⟩, ?_⟩
      simpa [φq, φ, π, hinc] using
        (QuotientGroup.map_mk (N := R.subgroupOf H) (M := N) φ
          (by intro r hr; exact hRN r (Subgroup.mem_subgroupOf.mp hr))
          ⟨hX.1, (Subgroup.mem_subgroupOf).mp hhX⟩).symm
  have hsurj : Function.Surjective φq.rangeRestrict := φq.rangeRestrict_surjective
  have hφq : IsPGroup p φq.range := hQ.of_surjective φq.rangeRestrict hsurj
  rw [← hrange]
  exact hφq

/-- The `p`-residual of a join of two subgroups normal in the join lies in
the join of the residuals. -/
private theorem pResidualOf_sup_le_local
    {G : Type u} [Group G] [Finite G]
    (F E : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hF : IsNormalIn F (F ⊔ E)) (hE : IsNormalIn E (F ⊔ E)) :
    pResidualOf (F ⊔ E) p ≤ pResidualOf F p ⊔ pResidualOf E p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let X : Subgroup G := F ⊔ E
  let RF : Subgroup G := pResidualOf F p
  let RE : Subgroup G := pResidualOf E p
  let N : Subgroup G := RF ⊔ RE
  have hRFX : RF ≤ X := (pResidualOf_le F p).trans le_sup_left
  have hREX : RE ≤ X := (pResidualOf_le E p).trans le_sup_right
  have hNX : N ≤ X := sup_le hRFX hREX
  have hRFn : IsNormalIn RF X := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (F := F) (K := (RF.subgroupOf F))
      (fstar_pResidualOf_subgroupOf_characteristic F p) hF
    have hmap : (RF.subgroupOf F).map F.subtype = RF :=
      Subgroup.map_subgroupOf_eq_of_le (pResidualOf_le F p)
    simpa [RF, hmap] using h
  have hREn : IsNormalIn RE X := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (F := E) (K := (RE.subgroupOf E))
      (fstar_pResidualOf_subgroupOf_characteristic E p) hE
    have hmap : (RE.subgroupOf E).map E.subtype = RE :=
      Subgroup.map_subgroupOf_eq_of_le (pResidualOf_le E p)
    simpa [RE, hmap] using h
  have hNnorm : (N.subgroupOf X).Normal := by
    have hNn : IsNormalIn N X := by
      let Y : Fin 2 → Subgroup G := ![RE, RF]
      have hY : ∀ i : Fin 2, IsNormalIn (Y i) X := by
        intro i
        fin_cases i <;> simp [Y] <;> assumption
      have hYsup : (⨆ i : Fin 2, Y i) = N := by
        apply le_antisymm
        · refine iSup_le ?_
          intro i
          fin_cases i <;> simp [Y, N]
        · exact sup_le (le_iSup (f := Y) 1) (le_iSup (f := Y) 0)
      simpa [hYsup] using (isNormalIn_iSup_local Y X hY)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNX]
    exact le_normalizer_of_isNormalIn hNn
  let π : ↥X →* (↥X ⧸ N.subgroupOf X) := QuotientGroup.mk' (N.subgroupOf X)
  let Fbar : Subgroup (↥X ⧸ N.subgroupOf X) := (F.subgroupOf X).map π
  let Ebar : Subgroup (↥X ⧸ N.subgroupOf X) := (E.subgroupOf X).map π
  have hFbar : IsPGroup p Fbar := by
    refine isPGroup_quotientMap_of_le_residual_local (X := X) (H := F)
      (R := RF) p hp le_sup_left (pResidualOf_le F p) (N.subgroupOf X) ?_ ?_
      (fstar_isPGroup_quotient_pResidualOf F p hp)
    · intro r hr
      rw [Subgroup.mem_subgroupOf]
      exact (le_sup_left : RF ≤ N) hr
    · exact fstar_pResidualOf_subgroupOf_normal F p
  have hEbar : IsPGroup p Ebar := by
    refine isPGroup_quotientMap_of_le_residual_local (X := X) (H := E)
      (R := RE) p hp le_sup_right (pResidualOf_le E p) (N.subgroupOf X) ?_ ?_
      (fstar_isPGroup_quotient_pResidualOf E p hp)
    · intro r hr
      rw [Subgroup.mem_subgroupOf]
      exact (le_sup_right : RE ≤ N) hr
    · exact fstar_pResidualOf_subgroupOf_normal E p
  have hFsubX : (F.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact le_normalizer_of_isNormalIn hF
  have hEsubX : (E.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
    exact le_normalizer_of_isNormalIn hE
  have : (F.subgroupOf X).Normal := hFsubX
  have : (E.subgroupOf X).Normal := hEsubX
  have hFbarN : Fbar.Normal := (inferInstance : (F.subgroupOf X).Normal).map π
    (QuotientGroup.mk'_surjective (N.subgroupOf X))
  have hEbarN : Ebar.Normal := (inferInstance : (E.subgroupOf X).Normal).map π
    (QuotientGroup.mk'_surjective (N.subgroupOf X))
  let Ybar : Fin 2 → Subgroup (↥X ⧸ N.subgroupOf X) := ![Ebar, Fbar]
  have hYbar : ∀ i : Fin 2, IsPGroup p (Ybar i) := by
    intro i
    fin_cases i <;> simp [Ybar] <;> assumption
  have hYbarN : ∀ i : Fin 2,
      IsNormalIn (Ybar i) (⨆ i : Fin 2, Ybar i) := by
    intro i
    refine ⟨le_iSup (f := Ybar) i, ?_⟩
    intro x hx y hy
    fin_cases i
    · exact hEbarN.conj_mem y hy x
    · exact hFbarN.conj_mem y hy x
  have hQtop : IsPGroup p ↥(⨆ i : Fin 2, Ybar i) :=
    isPGroup_iSup_of_normal_local Ybar hYbar hYbarN
  have hFsupE : (⨆ i : Fin 2, Ybar i) = ⊤ := by
    have hsub : (F.subgroupOf X) ⊔ (E.subgroupOf X) = (F ⊔ E).subgroupOf X := by
      let Y : Fin 2 → Subgroup G := ![F, E]
      have hYle : ∀ i : Fin 2, Y i ≤ X := by
        intro i
        fin_cases i
        · simpa [Y, X] using (le_sup_left : F ≤ F ⊔ E)
        · simpa [Y, X] using (le_sup_right : E ≤ F ⊔ E)
      have h := subgroupOf_iSup_of_le_local (H := Y) (N := X) hYle
      have hYsup : (⨆ i : Fin 2, Y i) = F ⊔ E := by
        apply le_antisymm
        · refine iSup_le ?_
          intro i
          fin_cases i <;> simp [Y]
        · exact sup_le (le_iSup (f := Y) 0) (le_iSup (f := Y) 1)
      have hYsubsup : (⨆ i : Fin 2, (Y i).subgroupOf X) =
          F.subgroupOf X ⊔ E.subgroupOf X := by
        apply le_antisymm
        · refine iSup_le ?_
          intro i
          fin_cases i <;> simp [Y]
        · exact sup_le (le_iSup (fun i : Fin 2 => (Y i).subgroupOf X) 0)
            (le_iSup (fun i : Fin 2 => (Y i).subgroupOf X) 1)
      have hR : (F ⊔ E).subgroupOf X = F.subgroupOf X ⊔ E.subgroupOf X := by
        rw [← hYsup, h]
        exact hYsubsup
      exact hR.symm
    have hsubX : (F ⊔ E).subgroupOf X = (⊤ : Subgroup (↥X)) := by
      rw [Subgroup.subgroupOf_self]
    have hYbarSup : (⨆ i : Fin 2, Ybar i) = Ebar ⊔ Fbar := by
      apply le_antisymm
      · refine iSup_le ?_
        intro i
        fin_cases i <;> simp [Ybar]
      · exact sup_le (le_iSup (f := Ybar) 0) (le_iSup (f := Ybar) 1)
    calc
      ⨆ i : Fin 2, Ybar i = Ebar ⊔ Fbar := hYbarSup
      _ = Fbar ⊔ Ebar := by rw [sup_comm]
      _ = ((F.subgroupOf X) ⊔ (E.subgroupOf X)).map π := by
        simp [Fbar, Ebar, Subgroup.map_sup]
      _ = ((F ⊔ E).subgroupOf X).map π := by rw [hsub]
      _ = (⊤ : Subgroup (↥X)).map π := by rw [hsubX]
      _ = ⊤ := Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective (N.subgroupOf X))
  have hQ : IsPGroup p (↥X ⧸ N.subgroupOf X) := by
    have hQtop' : IsPGroup p ↥(⊤ : Subgroup (↥X ⧸ N.subgroupOf X)) :=
      hFsupE ▸ hQtop
    exact hQtop'.of_equiv (Subgroup.topEquiv (G := ↥X ⧸ N.subgroupOf X))
  exact fstar_pResidualOf_le_of_quotient_isPGroup X N p hp hNX hNnorm hQ

/-- Generation lemma for `O^p(F*(A))`: it is generated by `O^p(S)` and the
q-cores of `A` for `q ≠ p`. -/
private theorem pResidualOf_generalizedFitting_le_generation_local
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (p : ℕ) (hp : p.Prime) :
    pResidualOf (generalizedFittingSubgroupOf A) p ≤
      pResidualOf S p ⊔
        (⨆ q : {q : ℕ // q.Prime ∧ q ≠ p}, qCoreOf A q.1) := by
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let X : Subgroup G := generalizedFittingSubgroupOf A
  let J : Subgroup G := ⨆ q : {q : ℕ // q.Prime ∧ q ≠ p}, qCoreOf A q.1
  have hE : E ≤ S := fstar_componentLayer_le_selfCentralizingSubnormal A S
    hSF hSsub hCS
  have hFnormX : IsNormalIn F X := by
    refine ⟨le_sup_left, ?_⟩
    intro x hx f hf
    exact (fittingSubgroupOf_isNormalIn A).2 x (by
      have hXleA : X ≤ A := fstar_generalizedFittingSubgroupOf_le A
      exact hXleA hx) f hf
  have hEnormX : IsNormalIn E X := by
    refine ⟨le_sup_right, ?_⟩
    intro x hx e he
    exact (fstar_componentLayerOf_isNormalIn A).2 x (by
      have hXleA : X ≤ A := fstar_generalizedFittingSubgroupOf_le A
      exact hXleA hx) e he
  have hResSup : pResidualOf (F ⊔ E) p ≤ pResidualOf F p ⊔ pResidualOf E p :=
    pResidualOf_sup_le_local F E p hp hFnormX hEnormX
  have hResF : pResidualOf F p = J := by
    simpa [F, J] using (pResidualOf_fitting_eq_iSup_qCoreOf_of_ne_local A p hp)
  have hResE : pResidualOf E p ≤ pResidualOf S p :=
    pResidualOf_mono_local hE p hp
  have hMain : pResidualOf X p ≤ J ⊔ pResidualOf S p := by
    calc
      pResidualOf X p = pResidualOf (F ⊔ E) p := by
        simp [X, F, E, generalizedFittingSubgroupOf]
      _ ≤ pResidualOf F p ⊔ pResidualOf E p := hResSup
      _ = J ⊔ pResidualOf E p := by rw [hResF]
      _ ≤ J ⊔ pResidualOf S p := sup_le_sup_left hResE J
  simpa [J, sup_comm] using hMain

/-!
## Residual commutator assembly (paper-faithful two-conjunct form)

The previous three-conjunct statement included `F*(B) ≤ A`, which is false
in general (A₅: A = S₃, S = C₃, B = A₄).  The paper's 1.7 proof has only
the two consequences below; the `F*(B) ≤ A` step belongs to the (iii)-case
with the Sbar hypotheses.
-/

/-! ## Local infrastructure: layer centralizes normalized nilpotent subgroups -/

/-- Quasisimplicity is invariant under a group isomorphism. -/
private theorem isQuasisimple_mulEquiv_local
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : IsQuasisimple G) :
    IsQuasisimple H := by
  have hNontriv : Nontrivial H := by
    let : Nontrivial G := hG.1
    exact e.toEquiv.injective.nontrivial
  have hPerf : Group.IsPerfect H := by
    let : Group.IsPerfect G := (Group.isPerfect_def).2 hG.2.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.toEquiv.surjective
  have he : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact (Subgroup.centerCongr e ⟨y, hy⟩).2
    · intro x hx
      refine ⟨e.symm x, ?_, ?_⟩
      · exact ((Subgroup.centerCongr e).symm ⟨x, hx⟩).2
      · exact e.apply_symm_apply x
  have hSimple : IsSimpleGroup (H ⧸ Subgroup.center H) := by
    exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e he)).mp hG.2.2
  exact ⟨hNontriv, (Group.isPerfect_def).1 hPerf, hSimple⟩

/-- A component of `G` contained in `H` is a component of `H`. -/
private theorem isComponentOf_subgroupOf_local
    {G : Type u} [Group G] {K H : Subgroup G}
    (hK : IsComponentOf K (⊤ : Subgroup G))
    (hKH : K ≤ H) :
    IsComponentOf (K.subgroupOf H) (⊤ : Subgroup H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    trivial
  · have hKsn : K.IsSubnormal := by
      have h' : ((K.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).IsSubnormal :=
        hK.2.1.map (f := (⊤ : Subgroup G).subtype)
          (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
      rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : K ≤ (⊤ : Subgroup G))] at h'
    have hmap' : ((K.subgroupOf H).subgroupOf (⊤ : Subgroup H)).map
        (⊤ : Subgroup H).subtype = K.subgroupOf H :=
      Subgroup.map_subgroupOf_eq_of_le (le_top : K.subgroupOf H ≤ (⊤ : Subgroup H))
    have hsnmap : (((K.subgroupOf H).subgroupOf (⊤ : Subgroup H)).map
        (⊤ : Subgroup H).subtype).IsSubnormal := by
      rw [hmap']
      exact hKsn.subgroupOf
    have hsnc : (Subgroup.comap (⊤ : Subgroup H).subtype
        (Subgroup.map (⊤ : Subgroup H).subtype
          ((K.subgroupOf H).subgroupOf (⊤ : Subgroup H)))).IsSubnormal :=
      Subgroup.IsSubnormal.comap (f := (⊤ : Subgroup H).subtype) hsnmap
    have hc' : Subgroup.comap (⊤ : Subgroup H).subtype
          (Subgroup.map (⊤ : Subgroup H).subtype
            ((K.subgroupOf H).subgroupOf (⊤ : Subgroup H))) =
        (K.subgroupOf H).subgroupOf (⊤ : Subgroup H) := by
      rw [hmap']
      apply le_antisymm
      · intro x hx
        exact (Subgroup.mem_subgroupOf).mpr ((Subgroup.mem_comap).mp hx)
      · intro x hx
        apply (Subgroup.mem_comap).mpr
        exact (Subgroup.mem_subgroupOf).mp hx
    simpa [hc'] using hsnc
  · exact isQuasisimple_mulEquiv_local (Subgroup.subgroupOfEquivOfLe hKH).symm hK.2.2

/-- `subgroupOf` reflects containment. -/
private theorem subgroupOf_le_subgroupOf_iff_of_le_local
    {G : Type u} [Group G] {A B H : Subgroup G}
    (hAH : A ≤ H) (_hBH : B ≤ H) :
    A.subgroupOf H ≤ B.subgroupOf H ↔ A ≤ B := by
  constructor
  · intro hle x hx
    have hm : (A.subgroupOf H).map H.subtype ≤ (B.subgroupOf H).map H.subtype :=
      Subgroup.map_mono (f := H.subtype) hle
    have hx' : H.subtype ⟨x, hAH hx⟩ ∈ (A.subgroupOf H).map H.subtype := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact ⟨hx, hAH hx⟩
    have hy : H.subtype ⟨x, hAH hx⟩ ∈ (B.subgroupOf H).map H.subtype := hm hx'
    rcases Subgroup.mem_map.mp hy with ⟨y, hyB, hxy⟩
    have hyx : (y : ↥H).1 = x := by
      have hyx' : y = (⟨x, hAH hx⟩ : ↥H) := H.subtype_injective hxy
      simpa using (congrArg (fun z : ↥H => (z : ↥H).1) hyx')
    have hy1 : (y : ↥H).1 ∈ B := (Subgroup.mem_subgroupOf).mp hyB
    simpa [hyx] using hy1
  · intro hle
    exact Subgroup.subgroupOf_mono H hle

/-- Restriction commutes with double `subgroupOf`, through the canonical
equivalence between `H.subgroupOf A` and `H`. -/
private theorem map_subgroupOf_subgroupOf_eq_local
    {G : Type u} [Group G] {E A H : Subgroup G}
    (hEH : E ≤ H) (hHA : H ≤ A) :
    ((E.subgroupOf A).subgroupOf (H.subgroupOf A)).map
      (Subgroup.subgroupOfEquivOfLe hHA).toMonoidHom = E.subgroupOf H := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyE : (y.1 : G) ∈ E := by
      have hy1 := (Subgroup.mem_subgroupOf).mp hy
      exact (Subgroup.mem_subgroupOf).mp hy1
    exact (Subgroup.mem_subgroupOf).mpr hyE
  · intro hx
    have hxE : (x : G) ∈ E := (Subgroup.mem_subgroupOf).mp hx
    refine Subgroup.mem_map.mpr ⟨?_, ?_, ?_⟩
    · exact ⟨⟨x, hHA (hEH hxE)⟩, by
        change (x : G) ∈ H
        exact hEH hxE⟩
    · rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf]
      exact hxE
    · apply Subtype.ext
      rfl

/-- A component of `A` which is contained in `H ≤ A` is a component of `H`. -/
private theorem isComponentOf_subgroupOf_of_isComponentOf_local
    {G : Type u} [Group G] {A H E : Subgroup G}
    (hE : IsComponentOf E A) (hEH : E ≤ H) (hHA : H ≤ A) :
    IsComponentOf (E.subgroupOf H) (⊤ : Subgroup H) := by
  have hE0 : IsComponentOf (E.subgroupOf A) (⊤ : Subgroup (↥A)) :=
    fstar_isComponentOf_subgroupOf_top hE
  let HA : Subgroup (↥A) := H.subgroupOf A
  let e : HA ≃* H := Subgroup.subgroupOfEquivOfLe hHA
  have hE0HA : IsComponentOf ((E.subgroupOf A).subgroupOf HA) (⊤ : Subgroup (↥HA)) := by
    apply isComponentOf_subgroupOf_local (G := ↥A) hE0
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hx
    exact hEH hx
  have hmap : ((E.subgroupOf A).subgroupOf HA).map e.toMonoidHom = E.subgroupOf H :=
    map_subgroupOf_subgroupOf_eq_local hEH hHA
  have hEcompH : IsComponentOf (((E.subgroupOf A).subgroupOf HA).map e.toMonoidHom)
      (⊤ : Subgroup H) := by
    refine ⟨le_top, ?_, ?_⟩
    · have hsub0 : (((E.subgroupOf A).subgroupOf HA).subgroupOf
          (⊤ : Subgroup (↥HA))).map (⊤ : Subgroup (↥HA)).subtype =
          (E.subgroupOf A).subgroupOf HA :=
        Subgroup.map_subgroupOf_eq_of_le
          (le_top : (E.subgroupOf A).subgroupOf HA ≤ (⊤ : Subgroup (↥HA)))
      have hKsnHA : ((E.subgroupOf A).subgroupOf HA).IsSubnormal := by
        have hmap := hE0HA.2.1.map (f := (⊤ : Subgroup (↥HA)).subtype)
          (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
        rwa [hsub0] at hmap
      have hsub : (((E.subgroupOf A).subgroupOf HA).map e.toMonoidHom).IsSubnormal :=
        hKsnHA.map (f := e.toMonoidHom) e.surjective
      exact hsub.subgroupOf
    · exact isQuasisimple_mulEquiv_local
        (Subgroup.equivMapOfInjective ((E.subgroupOf A).subgroupOf HA)
          e.toMonoidHom e.injective) hE0HA.2.2
  rwa [hmap] at hEcompH

/-- Restriction of a normalizer-containment to `subgroupOf A`. -/
private theorem subgroup_normalizer_of_le_normalizer_local
    {G : Type u} [Group G] {H S A : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (S : Set G)) :
    H.subgroupOf A ≤ Subgroup.normalizer ((S.subgroupOf A : Subgroup (↥A)) : Set (↥A)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxH : (x : G) ∈ H := (Subgroup.mem_subgroupOf).mp hx
  have hxN : (x : G) ∈ Subgroup.normalizer (S : Set G) := hH hxH
  rw [Subgroup.mem_normalizer_iff] at hxN
  constructor
  · intro hy
    simpa [Subgroup.mem_subgroupOf] using (hxN (y : G)).1 hy
  · intro hy
    simpa [Subgroup.mem_subgroupOf] using (hxN (y : G)).2 hy

/-- A finite nilpotent group is generated by its `p`-core and its `p'`-core. -/
private theorem nilpotent_top_le_pCore_sup_pPrimeCore_local
    {Q : Type u} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (hQnil : Group.IsNilpotent Q) :
    (⊤ : Subgroup Q) ≤ pCore p Q ⊔ pPrimeCore p Q := by
  classical
  have : Group.IsNilpotent Q := hQnil
  have hnilTop : Group.IsNilpotent (↥(⊤ : Subgroup Q)) := by
    exact Group.nilpotent_of_mulEquiv
      (G := Q) (G' := ↥(⊤ : Subgroup Q))
      (Subgroup.topEquiv.symm : Q ≃* ↥(⊤ : Subgroup Q))
  have hTop_le_iSup :
      (⊤ : Subgroup Q) ≤
        ⨆ q : (Nat.card Q).primeFactors.attach, pCore q.1 Q :=
    normal_nilpotent_le_sup_pCore
      (G := Q) (N := (⊤ : Subgroup Q)) (hN := inferInstance) hnilTop
  refine hTop_le_iSup.trans (iSup_le fun q => ?_)
  by_cases hqp : q.1 = p
  · subst hqp
    exact le_sup_left
  · have hqprime : Nat.Prime q.1 :=
      Nat.prime_of_mem_primeFactors q.1.2
    let : Fact (Nat.Prime q.1) := ⟨hqprime⟩
    obtain ⟨n, hn⟩ :=
      (pCore_isPGroup (G := Q) (p := q.1)).exists_card_eq
    have hcop : Nat.Coprime p (Nat.card (pCore q.1 Q)) := by
      rw [hn]
      have hpq : p ≠ q.1 := fun hpq => hqp hpq.symm
      exact
        ((Nat.coprime_primes (Fact.out : Nat.Prime p) hqprime).2 hpq).pow_right n
    exact
      (le_sSup (show pCore q.1 Q ∈
        {K : Subgroup Q | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
          ⟨inferInstance, hcop⟩)).trans le_sup_right

/-- A component centralizes any nilpotent subgroup it normalizes. -/
private theorem component_centralizes_normalized_nilpotent_local
    {G : Type u} [Group G] [Finite G]
    {A E S : Subgroup G} (hE : IsComponentOf E A)
    (hEN : E ≤ Subgroup.normalizer (S : Set G))
    (hSA : S ≤ A)
    (hS : Group.IsNilpotent S) :
    ⁅E, S⁆ = ⊥ := by
  let H : Subgroup G := E ⊔ S
  have hEH : E ≤ H := le_sup_left
  have hSH : S ≤ H := le_sup_right
  have hHA : H ≤ A := sup_le hE.1 hSA
  let HA : Subgroup (↥A) := H.subgroupOf A
  let SA : Subgroup (↥A) := S.subgroupOf A
  let K1 : Subgroup (↥HA) := (E.subgroupOf A).subgroupOf HA
  let S1 : Subgroup (↥HA) := SA.subgroupOf HA
  let e : HA ≃* H := Subgroup.subgroupOfEquivOfLe hHA
  have hE0 : IsComponentOf (E.subgroupOf A) (⊤ : Subgroup (↥A)) :=
    fstar_isComponentOf_subgroupOf_top hE
  have hE0HA : IsComponentOf K1 (⊤ : Subgroup (↥HA)) := by
    apply isComponentOf_subgroupOf_local (G := ↥A) hE0
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hx
    exact hEH hx
  have hHleN : H ≤ Subgroup.normalizer (S : Set G) := sup_le hEN S.le_normalizer
  have hHAleN : HA ≤ Subgroup.normalizer (SA : Set (↥A)) :=
    subgroup_normalizer_of_le_normalizer_local hHleN
  have hS1normal : S1.Normal := by
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := HA) (N := SA) hHAleN
  rcases component_le_or_commutator_eq_bot (G := (↥HA)) hE0HA hS1normal.isSubnormal with
    hle | hcomm
  · exfalso
    have hK1map : K1.map e.toMonoidHom = E.subgroupOf H :=
      map_subgroupOf_subgroupOf_eq_local hEH hHA
    have hS1map : S1.map e.toMonoidHom = S.subgroupOf H :=
      map_subgroupOf_subgroupOf_eq_local hSH hHA
    have hmaple : K1.map e.toMonoidHom ≤ S1.map e.toMonoidHom :=
      Subgroup.map_mono (f := e.toMonoidHom) hle
    have hES : E ≤ S := by
      rw [hK1map, hS1map] at hmaple
      exact (subgroupOf_le_subgroupOf_iff_of_le_local hEH hSH).mp hmaple
    have hEnil : Group.IsNilpotent E := by
      have hrc : ∃ n, S.lowerCentralSeries n = ⊥ :=
        (Subgroup.isNilpotent_iff_lowerCentralSeries (S := S)).mp hS
      rcases hrc with ⟨n, hSbot⟩
      have hEm : E.lowerCentralSeries n ≤ S.lowerCentralSeries n :=
        Subgroup.lowerCentralSeries_mono (n := n) hES
      have hEbot : E.lowerCentralSeries n = ⊥ := by
        rw [hSbot] at hEm
        exact le_bot_iff.mp hEm
      exact (Subgroup.isNilpotent_iff_lowerCentralSeries (S := E)).mpr ⟨n, hEbot⟩
    exact not_isNilpotent_of_isQuasisimple E hE.2.2 hEnil
  · have hK1map : K1.map e.toMonoidHom = E.subgroupOf H :=
      map_subgroupOf_subgroupOf_eq_local hEH hHA
    have hS1map : S1.map e.toMonoidHom = S.subgroupOf H :=
      map_subgroupOf_subgroupOf_eq_local hSH hHA
    have hmapcomm : (⁅K1, S1⁆).map e.toMonoidHom = ⊥ := by
      rw [hcomm]
      exact Subgroup.map_bot e.toMonoidHom
    have hcommH : ⁅K1.map e.toMonoidHom, S1.map e.toMonoidHom⁆ = ⊥ := by
      rw [← Subgroup.map_commutator (H₁ := K1) (H₂ := S1) (f := e.toMonoidHom)]
      exact hmapcomm
    have hcomm' : ⁅E.subgroupOf H, S.subgroupOf H⁆ = ⊥ := by
      rw [hK1map, hS1map] at hcommH
      exact hcommH
    exact (fstar_commutator_subgroupOf_eq_bot_iff_of_le (A := E) (B := S) (H := H)
      hEH hSH).mp hcomm'

/-- The layer `E(A)` centralizes any nilpotent subgroup `X ≤ A` that it
normalizes. -/
private theorem layer_centralizes_normalized_nilpotent_local
    {G : Type u} [Group G] [Finite G]
    (A X : Subgroup G)
    (hEN : componentLayerOf A ≤ Subgroup.normalizer (X : Set G))
    (hXA : X ≤ A)
    (hX : Group.IsNilpotent X) :
    ⁅componentLayerOf A, X⁆ = ⊥ := by
  have hE : componentLayerOf A ≤ Subgroup.centralizer (X : Set G) := by
    rw [componentLayerOf]
    refine sSup_le ?_
    intro E hE
    have hcomm : ⁅E, X⁆ = ⊥ :=
      component_centralizes_normalized_nilpotent_local (A := A) (E := E) (S := X)
        hE ((le_sSup (s := {E' : Subgroup G | IsComponentOf E' A}) hE).trans hEN) hXA hX
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := E) (H₂ := X)).1 hcomm
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer
    (H₁ := componentLayerOf A) (H₂ := X)).2 hE

/-! ## Local infrastructure: `O_{p'}(F(A))` and the `p`/`p'` commutator -/

/-- The ambient `p'`-core of `F(A)`. -/
private def pPrimeCoreOfFitting {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) : Subgroup G :=
  (pPrimeCore p (↥(fittingSubgroupOf A))).map (fittingSubgroupOf A).subtype

/-- `O^p(F(A)) ≤ O_{p'}(F(A))`. -/
private theorem pResidualOf_fitting_le_pPrimeCore_local
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) :
    pResidualOf (fittingSubgroupOf A) p ≤ pPrimeCoreOfFitting A p := by
  classical
  let F : Subgroup G := fittingSubgroupOf A
  let N : Subgroup G := (pPrimeCore p (↥F)).map F.subtype
  have hNleF : N ≤ F := Subgroup.map_subtype_le (H := F) (pPrimeCore p (↥F))
  have hNsub : N.subgroupOf F = pPrimeCore p (↥F) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rcases (Subgroup.mem_map).1 hx with ⟨y, hy, hxy⟩
      have hyx : y = x := F.subtype_injective hxy
      simpa [hyx] using hy
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hNnormF : (N.subgroupOf F).Normal := by
    rw [hNsub]
    exact pPrimeCore_normal
  have hFnil : Group.IsNilpotent (↥F) := by
    let e : fittingSubgroup (↥A) ≃* ↥F :=
      Subgroup.equivMapOfInjective (fittingSubgroup (↥A)) A.subtype A.subtype_injective
    exact Group.nilpotent_of_mulEquiv e
  let : Fact p.Prime := ⟨hp⟩
  have hQ : IsPGroup p (↥F ⧸ N.subgroupOf F) := by
    have hdecomp : (⊤ : Subgroup (↥F)) ≤ (pCore p (↥F) ⊔ pPrimeCore p (↥F) : Subgroup (↥F)) :=
      nilpotent_top_le_pCore_sup_pPrimeCore_local (Q := ↥F) (p := p) hFnil
    have htop : pCore p (↥F) ⊔ pPrimeCore p (↥F) = ⊤ := le_antisymm le_top hdecomp
    let π : (↥F) →* ↥F ⧸ N.subgroupOf F := QuotientGroup.mk' (N.subgroupOf F)
    have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective (N.subgroupOf F)
    have hP : IsPGroup p ((pCore p (↥F)).map π) :=
      IsPGroup.map (pCore_isPGroup (p := p) (G := ↥F)) π
    have hPtop : (pCore p (↥F)).map π = ⊤ := by
      apply le_antisymm le_top
      intro q hq
      rcases hsurj q with ⟨x, rfl⟩
      have hx : x ∈ pCore p (↥F) ⊔ pPrimeCore p (↥F) := by
        rw [htop]
        trivial
      rcases (Subgroup.mem_sup_of_normal_left (s := pPrimeCore p (↥F))
        (t := pCore p (↥F))).1 (by simpa [sup_comm] using hx) with ⟨b, hb, a, ha, hxeq⟩
      have hbN : (b : ↥F) ∈ N.subgroupOf F := by
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
      have hqeq : π x = π a := by
        apply (QuotientGroup.eq_iff_div_mem (N := N.subgroupOf F) (x := x) (y := a)).2
        have hx' : x * (a : ↥F)⁻¹ = b := by
          calc
            x * (a : ↥F)⁻¹ = (b * a) * (a : ↥F)⁻¹ := by rw [← hxeq]
            _ = b := by group
        rw [div_eq_mul_inv]
        rw [hx']
        exact hbN
      have haP : a ∈ pCore p (↥F) := ha
      exact hqeq ▸ Subgroup.mem_map.mpr ⟨a, haP, rfl⟩
    have hQ' : IsPGroup p (⊤ : Subgroup (↥F ⧸ N.subgroupOf F)) := hPtop ▸ hP
    exact hQ'.of_equiv (Subgroup.topEquiv (G := ↥F ⧸ N.subgroupOf F))
  simpa [pPrimeCoreOfFitting, N] using
    fstar_pResidualOf_le_of_quotient_isPGroup F N p hp hNleF hNnormF hQ

/-- For `H ≤ F(A)`, `O^p(H) ≤ O_{p'}(F(A))`. -/
private theorem pResidualOf_le_pPrimeCore_of_le_fitting_local
    {G : Type u} [Group G] [Finite G]
    (A H : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hHF : H ≤ fittingSubgroupOf A) :
    pResidualOf H p ≤ pPrimeCoreOfFitting A p := by
  exact (pResidualOf_mono_local hHF p hp).trans
    (pResidualOf_fitting_le_pPrimeCore_local A p hp)

/-- A `p`-subgroup `X ≤ A` commutes with every subgroup `Y` of
`O_{p'}(F(A))` that normalizes `X`. -/
private theorem commutator_le_of_le_pPrimeCore_of_normalizes_local
    {G : Type u} [Group G] [Finite G]
    (A X Y : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hXp : IsPGroup p X)
    (hXA : X ≤ A)
    (hYX : Y ≤ Subgroup.normalizer (X : Set G))
    (hY : Y ≤ pPrimeCoreOfFitting A p) :
    ⁅X, Y⁆ = ⊥ := by
  classical
  let N : Subgroup G := pPrimeCoreOfFitting A p
  let F : Subgroup G := fittingSubgroupOf A
  have hNleA : N ≤ A := by
    dsimp [N, pPrimeCoreOfFitting, F]
    exact (Subgroup.map_subtype_le (H := fittingSubgroupOf A) (pPrimeCore p (↥(fittingSubgroupOf A)))).trans (by
      intro x hx
      rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
      exact f.2)
  have hNnormA : IsNormalIn N A := by
    dsimp [N, pPrimeCoreOfFitting, F]
    exact map_characteristic_isNormalIn_of_isNormalIn (H := fittingSubgroupOf A) (N := A)
      (K := pPrimeCore p (↥(fittingSubgroupOf A)))
      (pPrimeCore_characteristic (p := p) (G := ↥(fittingSubgroupOf A)))
      (fittingSubgroupOf_isNormalIn A)
  have hXinterN : X ⊓ N = ⊥ := by
    apply le_bot_iff.mp
    intro g hg
    have hgX : g ∈ X := hg.1
    have hgN : g ∈ N := hg.2
    let gX : ↥X := ⟨g, hgX⟩
    let gN : ↥N := ⟨g, hgN⟩
    let : Fact p.Prime := ⟨hp⟩
    rcases (IsPGroup.iff_orderOf.mp hXp) gX with ⟨k, hk⟩
    have hord : orderOf g = p ^ k := by
      have h' : orderOf gX = p ^ k := hk
      simpa [gX] using h'
    have hcopN : Nat.Coprime p (Nat.card (↥N)) := by
      have hcard : Nat.card (↥N) = Nat.card (↥(pPrimeCore p (↥F))) := by
        dsimp [N, pPrimeCoreOfFitting, F]
        exact Subgroup.card_map_of_injective (fittingSubgroupOf A).subtype_injective
      rw [hcard]
      exact pPrimeCore_coprime_card (p := p) (G := ↥(fittingSubgroupOf A))
    have hgorder_dvd : orderOf g ∣ Nat.card (↥N) := by
      have hdvd : orderOf gN ∣ Nat.card (↥N) := by
        let : Fintype (↥N) := Fintype.ofFinite (↥N)
        simpa [Nat.card_eq_fintype_card] using (orderOf_dvd_card (G := ↥N) (x := gN))
      have hordN : orderOf gN = orderOf g := by
        simpa [gN] using (orderOf_injective N.subtype N.subtype_injective gN)
      simpa [gN, hordN] using hdvd
    have hcop : Nat.Coprime (orderOf g) (Nat.card (↥N)) := by
      rw [hord]
      exact hcopN.pow_left k
    have horder1 : orderOf g = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hgorder_dvd
    exact (orderOf_eq_one_iff.mp horder1)
  refine (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := X) (H₂ := Y)).2 ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxN : x ∈ A := hXA hx
  have hyY : y ∈ Y := hy
  have hxyX : ⁅x, y⁆ ∈ X := by
    have hyx : y * x⁻¹ * y⁻¹ ∈ X := by
      have hxinv : x⁻¹ ∈ X := X.inv_mem hx
      exact (Subgroup.mem_normalizer_iff.mp (hYX hyY) x⁻¹).1 hxinv
    have hxy : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      change x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹)
      group
    rw [hxy]
    exact X.mul_mem hx hyx
  have hxyN : ⁅x, y⁆ ∈ N := by
    have hxyx : x * y * x⁻¹ ∈ N := hNnormA.2 x hxN y (hY hyY)
    have hyinv : y⁻¹ ∈ N := N.inv_mem (hY hyY)
    have hxy : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by
      change x * y * x⁻¹ * y⁻¹ = (x * y * x⁻¹) * y⁻¹
      group
    rw [hxy]
    exact N.mul_mem hxyx hyinv
  have hxy1 : ⁅x, y⁆ = (1 : G) := by
    have hmem : ⁅x, y⁆ ∈ X ⊓ N := Subgroup.mem_inf.mpr ⟨hxyX, hxyN⟩
    have hbot : X ⊓ N ≤ ⊥ := le_of_eq hXinterN
    have hz : ⁅x, y⁆ ∈ (⊥ : Subgroup G) := hbot hmem
    exact Subgroup.mem_bot.mp hz
  exact ((commutatorElement_eq_one_iff_mul_comm (g₁ := x) (g₂ := y)).mp hxy1).symm

/-! ## Local infrastructure: the `S = (F(A) ∩ S) · E(A)` decomposition -/

/-- `S = (F(A) ∩ S) · E(A)` under the 1.7 hypotheses. -/
private theorem S_eq_sup_local
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S) :
    S = (fittingSubgroupOf A ⊓ S) ⊔ componentLayerOf A := by
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  have hE : E ≤ S := fstar_componentLayer_le_selfCentralizingSubnormal A S hSF hSsub hCS
  have hEF : E ≤ Subgroup.centralizer (F : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := E) (H₂ := F)).1
      (layer_centralizes_fitting A)
  apply le_antisymm
  · intro s hs
    have hsX : s ∈ F ⊔ E := by
      simpa [F, E, generalizedFittingSubgroupOf] using hSF hs
    rcases mem_sup_decompose_of_centralizes (F := F) (E := E) hsX hEF with
      ⟨f, hf, e, he, hseq⟩
    have heS : e ∈ S := hE he
    have hfS : f ∈ S := by
      have hse : s * (e : G)⁻¹ ∈ S := S.mul_mem hs (S.inv_mem heS)
      have hfeq : f = s * (e : G)⁻¹ := by
        rw [hseq]
        group
      rwa [hfeq]
    have hfF : f ∈ F ⊓ S := Subgroup.mem_inf.mpr ⟨hf, hfS⟩
    have hfSup : f ∈ (F ⊓ S) ⊔ E := (Subgroup.mem_sup_left (S := F ⊓ S) (T := E)) hfF
    have heSup : e ∈ (F ⊓ S) ⊔ E := (Subgroup.mem_sup_right (S := F ⊓ S) (T := E)) he
    have hseq' : s = f * e := hseq
    exact hseq' ▸ ((F ⊓ S) ⊔ E).mul_mem hfSup heSup
  · exact sup_le inf_le_right hE

/-- `O^p(S) ≤ O^p(F(A) ∩ S) ⊔ O^p(E(A))` under the 1.7 hypotheses. -/
private theorem pResidualOf_S_le_sup_local
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (p : ℕ) (hp : p.Prime) :
    pResidualOf S p ≤
      pResidualOf (fittingSubgroupOf A ⊓ S) p ⊔ pResidualOf (componentLayerOf A) p := by
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  have hSeq : S = (F ⊓ S) ⊔ E := S_eq_sup_local A S hSF hSsub hCS
  have hSleA : S ≤ A := hSF.trans (fstar_generalizedFittingSubgroupOf_le A)
  have hFnormS : IsNormalIn (F ⊓ S) S := by
    refine ⟨inf_le_right, ?_⟩
    intro s hs x hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (fittingSubgroupOf_isNormalIn A).2 s (hSleA hs) x hx.1
    · exact S.mul_mem (S.mul_mem hs hx.2) (S.inv_mem hs)
  have hE : E ≤ S := fstar_componentLayer_le_selfCentralizingSubnormal A S hSF hSsub hCS
  have hEnormS : IsNormalIn E S := by
    refine ⟨hE, ?_⟩
    intro s hs e he
    exact (fstar_componentLayerOf_isNormalIn A).2 s (hSleA hs) e he
  have hFnormJ : IsNormalIn (F ⊓ S) ((F ⊓ S) ⊔ E) := hSeq ▸ hFnormS
  have hEnormJ : IsNormalIn E ((F ⊓ S) ⊔ E) := hSeq ▸ hEnormS
  have hres : pResidualOf S p ≤ pResidualOf (F ⊓ S) p ⊔ pResidualOf E p := by
    calc
      pResidualOf S p = pResidualOf ((F ⊓ S) ⊔ E) p := by rw [← hSeq]
      _ ≤ pResidualOf (F ⊓ S) p ⊔ pResidualOf E p :=
        pResidualOf_sup_le_local (F ⊓ S) E p hp hFnormJ hEnormJ
  simpa [F, E] using hres

/-- The paper's "obvious" step: `[O_p(B) ∩ A, O^p(S)] = 1` for every prime
`p`, under the 1.7 hypotheses. -/
private theorem commutator_qCoreOf_B_inf_A_pResidualOf_S_local
    {G : Type u} [Group G] [Finite G]
    (A S B : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (hSB : S ≤ B)
    (p : ℕ) (hp : p.Prime) :
    ⁅qCoreOf B p ⊓ A, pResidualOf S p⁆ = ⊥ := by
  classical
  let X : Subgroup G := qCoreOf B p ⊓ A
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let R : Subgroup G := pResidualOf S p
  let RS : Subgroup G := pResidualOf (F ⊓ S) p
  let RE : Subgroup G := pResidualOf E p
  have hXp : IsPGroup p X := by
    dsimp [X]
    exact IsPGroup.to_inf_left (qCoreOf_isPGroup B p)
  have hXA : X ≤ A := by
    dsimp [X]
    exact inf_le_right
  have hSleA : S ≤ A := hSF.trans (fstar_generalizedFittingSubgroupOf_le A)
  let : Fact p.Prime := ⟨hp⟩
  have hXnil : Group.IsNilpotent X := hXp.isNilpotent
  have hE : E ≤ S := fstar_componentLayer_le_selfCentralizingSubnormal A S hSF hSsub hCS
  have hENX : E ≤ Subgroup.normalizer (X : Set G) := by
    have hEsubB : E ≤ B := hE.trans hSB
    have hEnormOB : E ≤ Subgroup.normalizer (qCoreOf B p : Set G) :=
      hEsubB.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in B p))
    have hEnormA : E ≤ Subgroup.normalizer (A : Set G) := by
      exact hE.trans (hSleA.trans A.le_normalizer)
    intro e he
    exact (Subgroup.inf_normalizer_le_normalizer_inf
      (H := qCoreOf B p) (K := A))
      (Subgroup.mem_inf.mpr ⟨hEnormOB he, hEnormA he⟩)
  have hXR : ⁅X, R⁆ = ⊥ := by
    have hRle : R ≤ RS ⊔ RE := pResidualOf_S_le_sup_local A S hSF hSsub hCS p hp
    have hXRS : ⁅X, RS⁆ = ⊥ := by
      have hRSleF : RS ≤ F := (pResidualOf_le (F ⊓ S) p).trans inf_le_left
      have hRSleN : RS ≤ pPrimeCoreOfFitting A p :=
        pResidualOf_le_pPrimeCore_of_le_fitting_local A (F ⊓ S) p hp
          (by
            intro x hx
            exact (Subgroup.mem_inf.mp hx).1)
      have hRSnX : RS ≤ Subgroup.normalizer (X : Set G) := by
        have hRSleS : RS ≤ S := (pResidualOf_le (F ⊓ S) p).trans inf_le_right
        have hfwd : ∀ r : G, r ∈ RS → ∀ x : G, x ∈ X → r * x * r⁻¹ ∈ X := by
          intro r hr x hx
          have hrB : r ∈ B := hRSleS.trans hSB hr
          have hxnOB : r * (x : G) * r⁻¹ ∈ qCoreOf B p :=
            (qCoreOf_normal_in B p).2 r hrB x hx.1
          have hxnA : r * (x : G) * r⁻¹ ∈ A :=
            A.mul_mem (A.mul_mem (hSleA (hRSleS hr)) hx.2) (A.inv_mem (hSleA (hRSleS hr)))
          exact Subgroup.mem_inf.mpr ⟨hxnOB, hxnA⟩
        intro r hr
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · exact hfwd r hr x
        · intro hx
          have hrinv : r⁻¹ ∈ RS := RS.inv_mem hr
          have hx' : r⁻¹ * (r * x * r⁻¹) * (r⁻¹)⁻¹ ∈ X :=
            hfwd r⁻¹ hrinv (r * x * r⁻¹) hx
          simpa [mul_assoc] using hx'
      exact commutator_le_of_le_pPrimeCore_of_normalizes_local A X RS p hp
        hXp hXA hRSnX hRSleN
    have hXRE : ⁅X, RE⁆ = ⊥ := by
      have hREleE : RE ≤ E := pResidualOf_le E p
      have hcomm : ⁅E, X⁆ = ⊥ :=
        layer_centralizes_normalized_nilpotent_local A X hENX hXA hXnil
      have hXcE : X ≤ Subgroup.centralizer (E : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := X) (H₂ := E)).1
          (Subgroup.commutator_comm (H₁ := E) (H₂ := X) ▸ hcomm)
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := X) (H₂ := RE)).2
        (hXcE.trans (Subgroup.centralizer_le (show (RE : Set G) ⊆ (E : Set G) from hREleE)))
    -- `X` centralizes `RS ⊔ RE`, hence `R`
    have hXcSup : X ≤ Subgroup.centralizer ((RS ⊔ RE : Subgroup G) : Set G) := by
      intro x hx
      have hxRS : x ∈ Subgroup.centralizer (RS : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := X) (H₂ := RS)).1 hXRS hx
      have hxRE : x ∈ Subgroup.centralizer (RE : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := X) (H₂ := RE)).1 hXRE hx
      exact fstar_centralizer_of_centralizes_join (F := RS) (E := RE) hxRS hxRE
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := X) (H₂ := R)).2
      (hXcSup.trans (Subgroup.centralizer_le
        (show (R : Set G) ⊆ ((RS ⊔ RE : Subgroup G) : Set G) from hRle)))
  simpa [X, R] using hXR

/-! ## Local infrastructure: the residual-commutator assembly -/

/-- A normal `p`-subgroup of `L` commutes with a normal `p'`-subgroup of
`L`. -/
private theorem commutator_eq_bot_of_normal_pgroup_pPrime_local
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) (p : ℕ) (hp : p.Prime)
    (P K : Subgroup G)
    (hPL : P ≤ L) (hPnorm : IsNormalIn P L) (hPp : IsPGroup p P)
    (hKL : K ≤ L) (hKnorm : IsNormalIn K L)
    (hKcop : Nat.Coprime p (Nat.card K)) :
    ⁅P, K⁆ = ⊥ := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hPle : P ≤ qCoreOf L p :=
    le_qCoreOf_of_normal_isPGroup L P p hPL (by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPL]
      exact le_normalizer_of_isNormalIn hPnorm) hPp
  have hKle : K ≤ (pPrimeCore p (↥L)).map L.subtype := by
    have hKnorm' : (K.subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKL]
      exact le_normalizer_of_isNormalIn hKnorm
    have hcard : Nat.card (K.subgroupOf L) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv
    have hcop' : Nat.Coprime p (Nat.card (K.subgroupOf L)) := by
      rwa [hcard]
    have hsub : K.subgroupOf L ≤ pPrimeCore p (↥L) := le_sSup ⟨hKnorm', hcop'⟩
    have hmap := Subgroup.map_mono (f := L.subtype) hsub
    have hmapK : (K.subgroupOf L).map L.subtype = K :=
      Subgroup.map_subgroupOf_eq_of_le hKL
    simpa [hmapK] using hmap
  have hcentK : K ≤ Subgroup.centralizer ((qCoreOf L p : Subgroup G) : Set G) := by
    exact hKle.trans (pPrimeCore_map_le_centralizer_pCore_map (p := p) L)
  have hPcentK : P ≤ Subgroup.centralizer (K : Set G) := by
    intro x hx y hy
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hcentK hy)) x (hPle hx)
    exact hcomm.symm
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := P) (H₂ := K)).mpr hPcentK

/-- Bender 1.1(iv), normal case: a `p`-group acting on a solvable `p'`-group
centralizes it once it centralizes a normal subgroup whose centralizer is
self-centralizing.  This is the Lean copy of Gagen's Lemma 2.2 normal case. -/
private theorem centralizes_of_normal_selfCentralizing_coprime_local
    {G : Type u} [Group G] [Finite G]
    (P K K₁ : Subgroup G)
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hK1_le_K : K₁ ≤ K)
    (hK1N : (K₁.subgroupOf K).Normal)
    (hPK₁ : P ≤ Subgroup.centralizer (K₁ : Set G))
    (hself : K ⊓ Subgroup.centralizer (K₁ : Set G) ≤ K₁)
    (hcop : Nat.Coprime (Nat.card P) (Nat.card K))
    (hsolv : Group.IsSolvable K) :
    P ≤ Subgroup.centralizer (K : Set G) := by
  classical
  have h1 : ⁅⁅P, K₁⁆, K⁆ = ⊥ := by
    have hPK1_bot : ⁅P, K₁⁆ = ⊥ :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hPK₁
    simp [hPK1_bot]
  have hK1K_le : ⁅K₁, K⁆ ≤ K₁ := by
    exact (Subgroup.le_normalizer_iff_commutator_le_left (H := K) (K := K₁)).1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hK1_le_K).1 hK1N)
  have hK1P_bot : ⁅K₁, P⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hPK₁
  have h2 : ⁅⁅K₁, K⁆, P⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hK1K_le le_rfl).trans (by simpa [hK1P_bot])
  have hKPK1_bot : ⁅⁅K, P⁆, K₁⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := P) (H₃ := K₁) h1 h2
  have hKP_le_K : ⁅K, P⁆ ≤ K := (Subgroup.le_normalizer_iff_commutator_le_left).1 hPK
  have hKP_cent : ⁅K, P⁆ ≤ Subgroup.centralizer (K₁ : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hKPK1_bot
  have hKP_le_K1 : ⁅K, P⁆ ≤ K₁ := (le_inf hKP_le_K hKP_cent).trans hself
  have hKPP_bot : ⁅⁅K, P⁆, P⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hKP_le_K1 le_rfl).trans (by simpa [hK1P_bot])
  let : P.Normalizes K := ⟨hPK⟩
  let : MulDistribMulAction (↥P) (↥K) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P K hPK
  let C : Subgroup (↥K) := commutatorAction (A := ↥P) (G := ↥K)
  have hCmap : C.map K.subtype = ⁅K, P⁆ := by
    simpa [C] using (commutatorAction_subgroup_conj_map_eq_commutator K P hPK)
  have hcomm₂_map_le :
      (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype ≤ ⁅⁅K, P⁆, P⁆ := by
    let S : Set (↥K) := {x : ↥K | ∃ a : ↥P, ∃ g : ↥K, g ∈ C ∧ x = g⁻¹ * (a • g)}
    calc
      (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype = (Subgroup.closure S).map K.subtype := by
        rfl
      _ = Subgroup.closure (K.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := K.subtype) S)
      _ ≤ ⁅⁅K, P⁆, P⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅K, P⁆, P⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, g, hgC, rfl⟩
        have hgKP : (g : G) ∈ ⁅K, P⁆ := by
          rw [← hCmap]
          exact Subgroup.mem_map_of_mem K.subtype hgC
        have hgen : ⁅((g : ↥K) : G)⁻¹, (a : G)⁆ ∈ ⁅⁅K, P⁆, P⁆ :=
          Subgroup.commutator_mem_commutator (H₁ := ⁅K, P⁆) (H₂ := P)
            (Subgroup.inv_mem (H := ⁅K, P⁆) hgKP) a.2
        simpa [commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc] using hgen
  have hcomm₂_bot : commutatorAction₂ (A := ↥P) (G := ↥K) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective
      (H := commutatorAction₂ (A := ↥P) (G := ↥K)) (f := K.subtype) K.subtype_injective).1
    exact le_antisymm (hcomm₂_map_le.trans (by simpa [hKPP_bot])) bot_le
  have htriv : ActsTrivially (A := ↥P) (G := ↥K) :=
    actsTrivially_of_commutatorAction₂_eq_bot_of_solvable_coprime
      (G := ↥K) (A := ↥P) hsolv hcop hcomm₂_bot
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  let a : ↥P := ⟨p, hp⟩
  let kK : ↥K := ⟨k, hk⟩
  have htrivK : a • kK = kK := htriv a kK
  have hsmulK : ↑(a • kK) = p * k * p⁻¹ := by
    simpa [a, kK] using
      (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe P K (a := a) (k := kK))
  have hconj : p * k * p⁻¹ = k :=
    hsmulK.trans (congrArg Subtype.val htrivK)
  calc
    k * p = (p * k * p⁻¹) * p := by rw [hconj]
    _ = p * k := by group

/-- Bender 1.1(iv), subnormal case (Gagen's Lemma 2.2): the normal-case
lemma is pushed down a subnormal chain by induction on the order of `K`. -/
private theorem centralizes_of_subnormal_selfCentralizing_coprime_local
    {G : Type u} [Group G] [Finite G]
    (P K K₁ : Subgroup G)
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hK1_le_K : K₁ ≤ K)
    (hsub : (K₁.subgroupOf K).IsSubnormal)
    (hPK₁ : P ≤ Subgroup.centralizer (K₁ : Set G))
    (hself : K ⊓ Subgroup.centralizer (K₁ : Set G) ≤ K₁)
    (hcop : Nat.Coprime (Nat.card P) (Nat.card K))
    (hsolv : Group.IsSolvable K) :
    P ≤ Subgroup.centralizer (K : Set G) := by
  classical
  have hmain : ∀ (n : ℕ) (K' : Subgroup G), Nat.card (↥K') = n →
      P ≤ Subgroup.normalizer (K' : Set G) →
      ∀ (H' : Subgroup (↥K')), H'.IsSubnormal →
        P ≤ Subgroup.centralizer (H'.map K'.subtype : Set G) →
        K' ⊓ Subgroup.centralizer (H'.map K'.subtype : Set G) ≤ H'.map K'.subtype →
          Nat.Coprime (Nat.card P) (Nat.card K') → Group.IsSolvable (↥K') →
            P ≤ Subgroup.centralizer (K' : Set G) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K' hcard hPK' H' hHsn hPH hself' hcop' hsolv'
      by_cases hnorm : H'.Normal
      · have hmap_le : H'.map K'.subtype ≤ K' := Subgroup.map_subtype_le (H := K') H'
        have hNnorm : ((H'.map K'.subtype).subgroupOf K').Normal := by
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer hmap_le]
          intro y hy
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨h, hh, rfl⟩
            exact Subgroup.mem_map.mpr
              ⟨⟨y, hy⟩ * h * (⟨y, hy⟩ : ↥K')⁻¹, hnorm.conj_mem h hh ⟨y, hy⟩, by simp⟩
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨h, hh, hx'⟩
            have hh' : (⟨y, hy⟩ : ↥K')⁻¹ * h * (⟨y, hy⟩ : ↥K') ∈ H' := by
              simpa using (hnorm.conj_mem h hh (⟨y, hy⟩ : ↥K')⁻¹)
            have hxeq : x = (((⟨y, hy⟩ : ↥K')⁻¹ * h * (⟨y, hy⟩ : ↥K') : ↥K') : G) := by
              calc
                x = y⁻¹ * (y * x * y⁻¹) * y := by group
                _ = y⁻¹ * (h : G) * y := by rw [← hx']; rw [Subgroup.subtype_apply]
                _ = (((⟨y, hy⟩ : ↥K')⁻¹ * h * (⟨y, hy⟩ : ↥K') : ↥K') : G) := by rfl
            exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩⁻¹ * h * ⟨y, hy⟩, hh', hxeq.symm⟩
        exact centralizes_of_normal_selfCentralizing_coprime_local P K' (H'.map K'.subtype)
          hPK' hmap_le hNnorm hPH hself' hcop' hsolv'
      · let H₀ : Subgroup (↥K') := H'
        let N0 : Subgroup (↥K') := Subgroup.normalClosure (H' : Set (↥K'))
        let N : Subgroup G := N0.map K'.subtype
        have hN_le_K' : N ≤ K' := Subgroup.map_subtype_le (H := K') N0
        have hH_le_N0 : H' ≤ N0 := Subgroup.le_normalClosure (H := H')
        have hHmap_le_N : H'.map K'.subtype ≤ N :=
          Subgroup.map_mono (f := K'.subtype) hH_le_N0
        have hH_ne_top : H' ≠ ⊤ := by
          intro hHtop
          apply hnorm
          rw [hHtop]
          infer_instance
        obtain ⟨m, f, hfmono, hfnorm, hf0, hftop⟩ := Subgroup.IsSubnormal.exists_chain hHsn
        have htop_exists : ∃ i : ℕ, i ≤ m ∧ f i = ⊤ := ⟨m, le_rfl, hftop⟩
        let k := Nat.find htop_exists
        have hk_le_m : k ≤ m := (Nat.find_spec htop_exists).1
        have hfk_top : f k = ⊤ := (Nat.find_spec htop_exists).2
        have hkmin : ∀ j, j < k → f j ≠ ⊤ := by
          intro j hj hfj
          have hk_le_j : k ≤ j :=
            Nat.find_min' htop_exists ⟨Nat.le_trans (Nat.le_of_lt hj) hk_le_m, hfj⟩
          exact (Nat.lt_irrefl k) (lt_of_le_of_lt hk_le_j hj)
        have hk_pos : 0 < k := by
          by_contra hk0
          have hk_eq : k = 0 := Nat.eq_zero_of_not_pos hk0
          have hf0top : f 0 = ⊤ := by simpa [hk_eq] using hfk_top
          have hHtop : H' = ⊤ := by
            rw [hf0] at hf0top
            exact hf0top
          exact hH_ne_top hHtop
        have hfkm1_lt_top : f (k - 1) < ⊤ := by
          refine lt_of_le_of_ne le_top ?_
          intro hfkm1top
          exact (hkmin (k - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hk_pos.ne') (by norm_num))) hfkm1top
        have hH_le_fkm1 : H' ≤ f (k - 1) := by
          rw [← hf0]
          exact hfmono (Nat.zero_le (k - 1))
        have hfkm1_normal : (f (k - 1)).Normal := by
          have hstep : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
          have hfn : ((f (k - 1)).subgroupOf (f k)).Normal := by
            have hfn0 : ((f (k - 1)).subgroupOf (f (k - 1 + 1))).Normal := hfnorm (k - 1)
            rw [hstep] at hfn0
            exact hfn0
          have hfn' : ((f (k - 1)).subgroupOf (⊤ : Subgroup (↥K'))).Normal := by
            rw [hfk_top] at hfn
            exact hfn
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top] at hfn'
          rw [← Subgroup.normalizer_eq_top_iff]
          exact top_le_iff.mp hfn'
        have hN0_le_fkm1 : N0 ≤ f (k - 1) := by
          exact Subgroup.normalClosure_le_normal (s := (H' : Set (↥K')))
            (N := f (k - 1)) (by intro x hx; exact hH_le_fkm1 hx)
        have hN0_lt_top : N0 < ⊤ := lt_of_le_of_lt hN0_le_fkm1 hfkm1_lt_top
        have hN0_ne_top : N0 ≠ ⊤ := hN0_lt_top.ne
        have hN_lt_K' : N < K' := by
          refine lt_of_le_of_ne hN_le_K' ?_
          intro hNeq
          have hcardN0 : Nat.card (↥N0) < Nat.card (↥K') := by
            have hidx : 1 < N0.index := by
              exact Subgroup.one_lt_index_of_ne_top hN0_ne_top
            have hlt : Nat.card (↥N0) < Nat.card (↥N0) * N0.index :=
              lt_mul_of_one_lt_right Nat.card_pos hidx
            have hcard : Nat.card (↥K') = Nat.card (↥N0) * N0.index :=
              (N0.card_mul_index).symm
            rw [hcard]
            exact hlt
          have hcardN : Nat.card (↥N) = Nat.card (↥N0) := by
            exact Nat.card_congr
              ((Subgroup.equivMapOfInjective N0 K'.subtype K'.subtype_injective).toEquiv.symm)
          have hcardNlt : Nat.card (↥N) < Nat.card (↥K') := by
            rw [hcardN]
            exact hcardN0
          have hcardN' : Nat.card (↥N) = Nat.card (↥K') := by rw [hNeq]
          exact (ne_of_lt hcardNlt) hcardN'
        have hN_inv (q : G) (hqP : q ∈ P) (n : ↥K') (hn : n ∈ N0) :
            q * (n : G) * q⁻¹ ∈ N := by
          refine Subgroup.closure_induction
            (k := Group.conjugatesOfSet (H' : Set (↥K')))
            (p := fun x _ => (q : G) * (x : G) * (q : G)⁻¹ ∈ N) ?mem ?one ?mul ?inv hn
          · intro x hx
            rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨a, ha, hconj⟩
            rcases isConj_iff.mp hconj with ⟨c, hc⟩
            have hpc : (q : G) * (c : G) * (q : G)⁻¹ ∈ K' :=
              ((Subgroup.mem_normalizer_iff (H := K') (g := q)).1 (hPK' hqP) (c : G)).1 c.2
            let c' : ↥K' := ⟨(q : G) * (c : G) * (q : G)⁻¹, hpc⟩
            have hhfix : (q : G) * (a : G) * (q : G)⁻¹ = (a : G) := by
              have hcomm : (a : G) * (q : G) = (q : G) * (a : G) :=
                (Subgroup.mem_centralizer_iff (g := q)
                  (s := (H'.map K'.subtype : Set G))).1 (hPH hqP) (a : G)
                  (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
              calc
                (q : G) * (a : G) * (q : G)⁻¹ = (a : G) * (q : G) * (q : G)⁻¹ := by rw [hcomm]
                _ = (a : G) := by group
            have hgen : q * (x : G) * q⁻¹ =
                (((c' : ↥K') * a * (c' : ↥K')⁻¹ : ↥K') : G) := by
              calc
                q * (x : G) * q⁻¹ = q * ((c * a * c⁻¹ : ↥K') : G) * q⁻¹ := by
                  rw [← hc]
                _ = (q * (c : G) * q⁻¹) * (q * (a : G) * q⁻¹) * (q * (c : G)⁻¹ * q⁻¹) := by
                  simp [Subgroup.coe_mul, Subgroup.coe_inv]
                _ = (q * (c : G) * q⁻¹) * (a : G) * (q * (c : G)⁻¹ * q⁻¹) := by rw [hhfix]
                _ = (((c' : ↥K') * a * (c' : ↥K')⁻¹ : ↥K') : G) := by
                  simp [c', Subgroup.coe_mul]
                  group
            have hmem : (c' : ↥K') * a * (c' : ↥K')⁻¹ ∈
                Group.conjugatesOfSet (H' : Set (↥K')) := by
              exact Group.conj_mem_conjugatesOfSet (G := ↥K') (s := (H' : Set (↥K')))
                (x := a) (c := c') (Group.subset_conjugatesOfSet ha)
            have hN0mem : (c' : ↥K') * a * (c' : ↥K')⁻¹ ∈ N0 :=
              Subgroup.conjugatesOfSet_subset_normalClosure hmem
            exact Subgroup.mem_map.mpr ⟨(c' : ↥K') * a * (c' : ↥K')⁻¹, hN0mem, by simpa [hgen]⟩
          · simp [N]
          · intro x y _hx _hy ihx ihy
            have hxy : q * ((x * y : ↥K') : G) * q⁻¹ =
                (q * (x : G) * q⁻¹) * (q * (y : G) * q⁻¹) := by
              rw [Subgroup.coe_mul]
              group
            rw [hxy]
            exact N.mul_mem ihx ihy
          · intro x _hx ihx
            have hxinv : q * ((x : ↥K')⁻¹ : G) * q⁻¹ = (q * (x : G) * q⁻¹)⁻¹ := by
              group
            change q * ((x : ↥K')⁻¹ : G) * q⁻¹ ∈ N
            rw [hxinv]
            exact N.inv_mem ihx
        have hPKN : P ≤ Subgroup.normalizer (N : Set G) := by
          intro q hq
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨n, hn, rfl⟩
            exact hN_inv q hq n hn
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨n, hn, hx'⟩
            have hqinvP : q⁻¹ ∈ P := P.inv_mem hq
            have hn' : q⁻¹ * (n : G) * q ∈ N := by
              simpa using (hN_inv q⁻¹ hqinvP n hn)
            have hxeq : x = q⁻¹ * (n : G) * q := by
              calc
                x = q⁻¹ * (q * x * q⁻¹) * q := by group
                _ = q⁻¹ * (n : G) * q := by rw [← hx']; rw [Subgroup.subtype_apply]
            rwa [hxeq]
        have hsubN0 : (H'.subgroupOf N0).IsSubnormal := by
          simpa [Subgroup.mem_subgroupOf] using
            (Subgroup.IsSubnormal.comap N0.subtype hHsn)
        let e0 : ↥N0 ≃* ↥N := Subgroup.equivMapOfInjective N0 K'.subtype K'.subtype_injective
        let H0 : Subgroup (↥N) := (H'.subgroupOf N0).map e0.toMonoidHom
        have hH0sn : H0.IsSubnormal := Subgroup.IsSubnormal.map e0.surjective hsubN0
        have hH0map : H0.map N.subtype = H'.map K'.subtype := by
          calc
            H0.map N.subtype = (H'.subgroupOf N0).map (N.subtype.comp e0.toMonoidHom) := by
              simp [H0, Subgroup.map_map]
            _ = (H'.subgroupOf N0).map (K'.subtype.comp N0.subtype) := by
              apply congrArg (fun f : ↥N0 →* G => (H'.subgroupOf N0).map f)
              ext x
              change (N.subtype (e0 x) : G) = (K'.subtype (N0.subtype x) : G)
              rfl
            _ = ((H'.subgroupOf N0).map N0.subtype).map K'.subtype := by
              rw [Subgroup.map_map]
            _ = H'.map K'.subtype := by
              simp [Subgroup.map_subgroupOf_eq_of_le hH_le_N0]
        have hPH0 : P ≤ Subgroup.centralizer (H0.map N.subtype : Set G) := by
          rw [hH0map]
          exact hPH
        have hself0 : N ⊓ Subgroup.centralizer (H0.map N.subtype : Set G) ≤ H0.map N.subtype := by
          rw [hH0map]
          intro x hx
          rcases hx with ⟨hxN, hxCent⟩
          exact hself' ⟨hN_le_K' hxN, hxCent⟩
        have hcopN : Nat.Coprime (Nat.card P) (Nat.card N) :=
          Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hN_le_K') hcop'
        have hsolvN : Group.IsSolvable (↥N) := by
          let : Group.IsSolvable (↥K') := hsolv'
          have hsub_solv : Group.IsSolvable (↥(N.subgroupOf K')) := inferInstance
          have hmapN : (N.subgroupOf K').map K'.subtype = N :=
            Subgroup.map_subgroupOf_eq_of_le hN_le_K'
          have eN : ↥(N.subgroupOf K') ≃* ↥((N.subgroupOf K').map K'.subtype) :=
            Subgroup.equivMapOfInjective (N.subgroupOf K') K'.subtype K'.subtype_injective
          have hsolvMap : Group.IsSolvable (↥((N.subgroupOf K').map K'.subtype)) :=
            Group.isSolvable_of_surjective (f := eN.toMonoidHom) eN.surjective
          exact by
            rw [hmapN] at hsolvMap
            exact hsolvMap
        have hNcard_lt : Nat.card (↥N) < n := by
          have hlt' : Nat.card (↥N) < Nat.card (↥K') := by
            have hN0card : Nat.card (↥N0) < Nat.card (↥K') := by
              have hidx : 1 < N0.index := Subgroup.one_lt_index_of_ne_top hN0_ne_top
              have hlt : Nat.card (↥N0) < Nat.card (↥N0) * N0.index :=
                lt_mul_of_one_lt_right Nat.card_pos hidx
              have hcardK' : Nat.card (↥K') = Nat.card (↥N0) * N0.index :=
                (N0.card_mul_index).symm
              rw [hcardK']
              exact hlt
            have hcardN : Nat.card (↥N) = Nat.card (↥N0) := by
              exact Nat.card_congr
                ((Subgroup.equivMapOfInjective N0 K'.subtype K'.subtype_injective).toEquiv.symm)
            rw [hcardN]
            exact hN0card
          rw [← hcard]
          exact hlt'
        have hPKN_concl : P ≤ Subgroup.centralizer (N : Set G) :=
          ih (Nat.card (↥N)) hNcard_lt N rfl hPKN H0 hH0sn hPH0 hself0 hcopN hsolvN
        have hN_normal : (N.subgroupOf K').Normal := by
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_K']
          intro y hy
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨n, hn, rfl⟩
            have hconjN0 : (⟨y, hy⟩ : ↥K') * n * (⟨y, hy⟩ : ↥K')⁻¹ ∈ N0 :=
              (inferInstance : N0.Normal).conj_mem n hn ⟨y, hy⟩
            exact Subgroup.mem_map.mpr
              ⟨⟨y, hy⟩ * n * (⟨y, hy⟩ : ↥K')⁻¹, hconjN0, by simp⟩
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨n, hn, hx'⟩
            have hconjN0 : (⟨y, hy⟩ : ↥K')⁻¹ * n * (⟨y, hy⟩ : ↥K') ∈ N0 := by
              simpa using ((inferInstance : N0.Normal).conj_mem n hn (⟨y, hy⟩ : ↥K')⁻¹)
            have hxeq : x = (((⟨y, hy⟩ : ↥K')⁻¹ * n * (⟨y, hy⟩ : ↥K') : ↥K') : G) := by
              calc
                x = y⁻¹ * (y * x * y⁻¹) * y := by group
                _ = y⁻¹ * (n : G) * y := by rw [← hx']; rw [Subgroup.subtype_apply]
                _ = (((⟨y, hy⟩ : ↥K')⁻¹ * n * (⟨y, hy⟩ : ↥K') : ↥K') : G) := by rfl
            exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩⁻¹ * n * ⟨y, hy⟩, hconjN0, hxeq.symm⟩
        have hselfN : K' ⊓ Subgroup.centralizer (N : Set G) ≤ N := by
          intro x hx
          rcases hx with ⟨hxK', hxCent⟩
          have hxCentH : x ∈ Subgroup.centralizer (H'.map K'.subtype : Set G) :=
            (Subgroup.centralizer_le (show (H'.map K'.subtype : Set G) ⊆ (N : Set G) from
              hHmap_le_N)) hxCent
          exact hHmap_le_N (hself' ⟨hxK', hxCentH⟩)
        exact centralizes_of_normal_selfCentralizing_coprime_local P K' N
          hPK' hN_le_K' hN_normal hPKN_concl hselfN hcop' hsolv'
  exact hmain (Nat.card (↥K)) K rfl hPK (K₁.subgroupOf K) hsub
    (by rw [Subgroup.map_subgroupOf_eq_of_le hK1_le_K]; exact hPK₁)
    (by rw [Subgroup.map_subgroupOf_eq_of_le hK1_le_K]; exact hself) hcop hsolv

/-- A subgroup centralizing two subgroups centralizes their join. -/
private lemma le_centralizer_of_centralizes_sup_local
    {G : Type u} [Group G] (C X Y : Subgroup G)
    (hX : C ≤ Subgroup.centralizer ((X : Subgroup G) : Set G))
    (hY : C ≤ Subgroup.centralizer ((Y : Subgroup G) : Set G)) :
    C ≤ Subgroup.centralizer ((X ⊔ Y : Subgroup G) : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hyX | hyY
    · exact (Subgroup.mem_centralizer_iff.mp (hX hc)) y hyX
    · exact (Subgroup.mem_centralizer_iff.mp (hY hc)) y hyY
  · intro y hy
    rcases hy with hyX | hyY
    · exact (Subgroup.mem_centralizer_iff.mp (hX hc)) y⁻¹ ((X.inv_mem) hyX)
    · exact (Subgroup.mem_centralizer_iff.mp (hY hc)) y⁻¹ ((Y.inv_mem) hyY)
  · simp
  · intro a b _ha _hb hca hcb
    calc
      (a * b) * c = a * (b * c) := by group
      _ = a * (c * b) := by rw [hcb]
      _ = (a * c) * b := by group
      _ = (c * a) * b := by rw [hca]
      _ = c * (a * b) := by group

/-- `O_q(S) ≤ O^p(S)` for distinct primes `q ≠ p`. -/
private theorem qCoreOf_le_pResidualOf_of_ne_local_S
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) :
    qCoreOf S q ≤ pResidualOf S p := by
  intro x hx
  have hxS : x ∈ S := qCoreOf_le S q hx
  let xQ : ↥(qCoreOf S q) := ⟨x, hx⟩
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hp⟩
  rcases (IsPGroup.iff_orderOf.mp (qCoreOf_isPGroup S q)) xQ with ⟨k, hk⟩
  have hcop : Nat.Coprime p (q ^ k) := by
    exact (Nat.coprime_primes hp hq).2 hne.symm |>.pow_right k
  have hord : orderOf x = orderOf xQ :=
    (orderOf_injective (qCoreOf S q).subtype (qCoreOf S q).subtype_injective xQ)
  have hcop' : Nat.Coprime p (orderOf x) := by
    rw [hord, hk]
    exact hcop
  exact fstar_mem_pResidualOf_of_order_coprime S p hp hxS hcop'

/-! ## Nilpotent-core helpers for the fixed-point and cross-commutator steps -/

/-- Any `p`-subgroup of a nilpotent subgroup lies in the `p`-core. -/
private theorem pSubgroup_le_qCoreOf_of_nilpotent_local
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hHnil : Group.IsNilpotent H) {K : Subgroup G}
    (hKH : K ≤ H) (hKp : IsPGroup p K) :
    K ≤ qCoreOf H p := by
  let K' : Subgroup (↥H) := K.subgroupOf H
  have hK'p : IsPGroup p K' :=
    hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hKH).symm
  obtain ⟨S, hKleS⟩ := IsPGroup.exists_le_sylow (G := ↥H) (p := p) hK'p
  have hSnormal : (S : Subgroup (↥H)).Normal :=
    Group.IsNilpotent.sylow_normal (p := p) hHnil S
  have hK'leP : K' ≤ pCore p (↥H) :=
    hKleS.trans (le_sSup ⟨hSnormal, S.isPGroup'⟩)
  have hmap := Subgroup.map_mono (f := H.subtype) hK'leP
  have hK'eq : K'.map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  change K ≤ (pCore p (↥H)).map H.subtype
  simpa [qCoreOf, hK'eq] using hmap

/-- An element of the `p'`-core has order coprime to `p`. -/
private lemma orderOf_coprime_of_mem_pPrimeCore_map_local
    {G : Type u} [Group G] [Finite G] {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    {z : G} (hz : z ∈ (pPrimeCore p (↥H)).map H.subtype) :
    Nat.Coprime p (orderOf z) := by
  rcases (Subgroup.mem_map).1 hz with ⟨u, hu, rfl⟩
  have hdvd : orderOf (u : G) ∣ Nat.card (pPrimeCore p (↥H)) :=
    by
      simpa [Subgroup.orderOf_coe] using
        (Subgroup.orderOf_dvd_natCard (pPrimeCore p (↥H)) hu)
  exact (pPrimeCore_coprime_card (G := ↥H) (p := p)).of_dvd_right hdvd

/-- An element of a nilpotent subgroup whose order is coprime to `p` lies
in the `p'`-core. -/
private theorem element_mem_pPrimeCore_of_order_coprime_of_nilpotent_local
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hHnil : Group.IsNilpotent H) {x : G} (hxH : x ∈ H)
    (hcop : Nat.Coprime p (orderOf x)) :
    x ∈ (pPrimeCore p (↥H)).map H.subtype := by
  classical
  let Q : Subgroup G := qCoreOf H p
  let QQ : Subgroup G := (pPrimeCore p (↥H)).map H.subtype
  have htop : (⊤ : Subgroup (↥H)) ≤ pCore p (↥H) ⊔ pPrimeCore p (↥H) :=
    nilpotent_top_le_pCore_sup_pPrimeCore (Q := ↥H) (p := p) hHnil
  have hxmem : (⟨x, hxH⟩ : ↥H) ∈ pCore p (↥H) ⊔ pPrimeCore p (↥H) := htop trivial
  have hxsup : x ∈ Q ⊔ QQ := by
    have hmap_eq :
        ((pCore p (↥H) ⊔ pPrimeCore p (↥H)) : Subgroup (↥H)).map H.subtype =
          Q ⊔ QQ := by
      rw [Subgroup.map_sup]
      rfl
    rw [← hmap_eq]
    exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hxmem, rfl⟩
  have hEF : QQ ≤ Subgroup.centralizer (Q : Set G) :=
    pPrimeCore_map_le_centralizer_pCore_map (p := p) H
  rcases mem_sup_decompose_of_centralizes (F := Q) (E := QQ) hxsup hEF with
    ⟨xq, hxq, xq', hxq', hxeq⟩
  have hxq_xq'_comm : Commute xq xq' := by
    exact (Subgroup.mem_centralizer_iff.mp (hEF hxq')) xq hxq
  have hcop_xq' : Nat.Coprime p (orderOf xq') :=
    orderOf_coprime_of_mem_pPrimeCore_map_local (H := H) (p := p) hxq'
  have hord_xq_pow : ∃ k : ℕ, orderOf xq = p ^ k := by
    rcases (IsPGroup.iff_orderOf.mp (qCoreOf_isPGroup H p)) ⟨xq, hxq⟩ with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [Subgroup.orderOf_coe] using hk
  rcases hord_xq_pow with ⟨k, hk⟩
  have hcop_xq_xq' : (orderOf xq).Coprime (orderOf xq') := by
    rw [hk]
    exact hcop_xq'.pow_left k
  have hord_eq : orderOf x = orderOf xq * orderOf xq' := by
    calc
      orderOf x = orderOf (xq * xq') := by rw [hxeq]
      _ = orderOf xq * orderOf xq' :=
        hxq_xq'_comm.orderOf_mul_eq_mul_orderOf_of_coprime hcop_xq_xq'
  have hdvd_xq : orderOf xq ∣ orderOf x := by
    rw [hord_eq]
    exact dvd_mul_right (orderOf xq) (orderOf xq')
  have hcop_xq : Nat.Coprime p (orderOf xq) := hcop.of_dvd_right hdvd_xq
  have hk0 : k = 0 := by
    by_contra hk0
    have hdvd : p ∣ p ^ k := by
      simpa using (pow_dvd_pow p (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hk0)))
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1
      (by rwa [hk] at hcop_xq) hdvd
  have hxq_one : xq = 1 := by
    have h : orderOf xq = 1 := by rw [hk, hk0]; simp
    exact orderOf_eq_one_iff.mp h
  have hx_eq : x = xq' := by rw [hxeq, hxq_one, one_mul]
  exact hx_eq ▸ hxq'

/-- `C_G(O_q(S)) ∩ O_q(A) ≤ O_q(S)`: fixed points of `O_q(S)` in `O_q(A)`
lie in `O_q(S)` (Gagen, Theorem 12.4 step (ii)). -/
private theorem qCoreOf_centralizer_le_qCoreOf_local
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (q : ℕ) (hq : q.Prime) :
    qCoreOf A q ⊓ Subgroup.centralizer ((qCoreOf S q : Subgroup G) : Set G) ≤
      qCoreOf S q := by
  classical
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let QS : Subgroup G := qCoreOf S q
  let QF : Subgroup G := qCoreOf F q
  let P : Subgroup G := (pPrimeCore q (↥F)).map F.subtype
  let : Fact q.Prime := ⟨hq⟩
  have hFnil : Group.IsNilpotent F := fittingSubgroupOf_isNilpotent A
  have hFcE : F ≤ Subgroup.centralizer (E : Set G) := by
    have hcomm : ⁅F, E⁆ = ⊥ := Subgroup.commutator_comm E F ▸ layer_centralizes_fitting A
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := F) (H₂ := E)).1 hcomm
  have hxQF : ∀ x : G, x ∈ qCoreOf A q → x ∈ QF :=
    fstar_qCoreOf_le_qCoreOf_fittingSubgroupOf A q hq
  have hQFcP : QF ≤ Subgroup.centralizer (P : Set G) := by
    have hPcQ : P ≤ Subgroup.centralizer (QF : Set G) :=
      pPrimeCore_map_le_centralizer_pCore_map (p := q) F
    have hQcP : ⁅QF, P⁆ = ⊥ := by
      apply bot_unique
      rw [← Subgroup.commutator_comm P QF]
      exact le_of_eq
        ((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := P) (H₂ := QF)).2 hPcQ)
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := QF) (H₂ := P)).1 hQcP
  have hFinterSnil : Group.IsNilpotent (↥(F ⊓ S)) := by
    let : Group.IsNilpotent (↥F) := hFnil
    have hInst : Group.IsNilpotent (↥((F ⊓ S).subgroupOf F)) := by
      infer_instance
    exact Group.nilpotent_of_mulEquiv
      (G := ↥((F ⊓ S).subgroupOf F)) (G' := ↥(F ⊓ S))
      (Subgroup.subgroupOfEquivOfLe (H := F ⊓ S) (K := F)
        (show F ⊓ S ≤ F from inf_le_left)) (_h := hInst)
  have hQSs : ∀ z : G, z ∈ qCoreOf (F ⊓ S) q → z ∈ QS := by
    intro z hz
    have hzS : z ∈ S := (qCoreOf_le (F ⊓ S) q hz).2
    have hFinterSnorm : IsNormalIn (F ⊓ S) S := by
      refine ⟨inf_le_right, ?_⟩
      intro s hs z hz
      have hsA : s ∈ A := hSF.trans (fstar_generalizedFittingSubgroupOf_le A) hs
      have hz'F : s * z * s⁻¹ ∈ F :=
        (fittingSubgroupOf_isNormalIn A).2 s hsA z hz.1
      have hz'S : s * z * s⁻¹ ∈ S :=
        S.mul_mem (S.mul_mem hs hz.2) (S.inv_mem hs)
      exact Subgroup.mem_inf.mpr ⟨hz'F, hz'S⟩
    have hnorm : IsNormalIn (qCoreOf (F ⊓ S) q) S := by
      simpa [qCoreOf] using
        (fstar_characteristic_subgroupOf_map_normal_in (F := F ⊓ S)
          (K := pCore q (↥(F ⊓ S))) (pCore_characteristic (p := q)) hFinterSnorm)
    have hQSle : qCoreOf (F ⊓ S) q ≤ S := fun z hz => (qCoreOf_le (F ⊓ S) q hz).2
    exact le_qCoreOf_of_normal_isPGroup S (qCoreOf (F ⊓ S) q) q hQSle (by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQSle]
      exact le_normalizer_of_isNormalIn hnorm) (qCoreOf_isPGroup (F ⊓ S) q) hz
  intro x hx
  rcases Subgroup.mem_inf.mp hx with ⟨hxA, hxcent⟩
  have hxF : x ∈ F := fstar_qCoreOf_le_fittingSubgroupOf A q hq hxA
  have hxcentP : x ∈ Subgroup.centralizer (P : Set G) := hQFcP (hxQF x hxA)
  have hxS : x ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyFSE : y ∈ (F ⊓ S) ⊔ E := by
      rw [← S_eq_sup_local A S hSF hSsub hCS]
      exact hy
    rw [Subgroup.sup_eq_closure] at hyFSE
    have hgen : ∀ z : G, z ∈ ((F ⊓ S : Subgroup G) : Set G) ∪ (E : Set G) →
        z * x = x * z := by
      intro z hz
      rcases hz with hzF | hzE
      · have hzFS : z ∈ F ⊓ S := hzF
        have htop :
            (⊤ : Subgroup (↥(F ⊓ S))) ≤
              pCore q (↥(F ⊓ S)) ⊔ pPrimeCore q (↥(F ⊓ S)) :=
          nilpotent_top_le_pCore_sup_pPrimeCore (Q := ↥(F ⊓ S)) (p := q) hFinterSnil
        have hzmem : (⟨z, hzFS⟩ : ↥(F ⊓ S)) ∈
            pCore q (↥(F ⊓ S)) ⊔ pPrimeCore q (↥(F ⊓ S)) := htop trivial
        have hzsup :
            z ∈ qCoreOf (F ⊓ S) q ⊔
              (pPrimeCore q (↥(F ⊓ S))).map (F ⊓ S).subtype := by
          have hmap_eq :
              ((pCore q (↥(F ⊓ S)) ⊔ pPrimeCore q (↥(F ⊓ S))) :
                  Subgroup (↥(F ⊓ S))).map (F ⊓ S).subtype =
                qCoreOf (F ⊓ S) q ⊔
                  (pPrimeCore q (↥(F ⊓ S))).map (F ⊓ S).subtype := by
            rw [Subgroup.map_sup]
            rfl
          rw [← hmap_eq]
          exact Subgroup.mem_map.mpr ⟨⟨z, hzFS⟩, hzmem, rfl⟩
        have hEF' :
            (pPrimeCore q (↥(F ⊓ S))).map (F ⊓ S).subtype ≤
              Subgroup.centralizer ((qCoreOf (F ⊓ S) q : Subgroup G) : Set G) :=
          pPrimeCore_map_le_centralizer_pCore_map (p := q) (F ⊓ S)
        rcases mem_sup_decompose_of_centralizes
            (F := qCoreOf (F ⊓ S) q)
            (E := (pPrimeCore q (↥(F ⊓ S))).map (F ⊓ S).subtype) hzsup hEF' with
          ⟨zq, hzq, zq', hzq', hzeq⟩
        have hxzq : zq * x = x * zq :=
          (Subgroup.mem_centralizer_iff.mp hxcent) zq (hQSs zq hzq)
        have hzq'F : zq' ∈ F := by
          exact (Subgroup.map_subtype_le (H := F ⊓ S)
            (K := pPrimeCore q (↥(F ⊓ S)))).trans inf_le_left hzq'
        have hzq'cop : Nat.Coprime q (orderOf zq') :=
          orderOf_coprime_of_mem_pPrimeCore_map_local (H := F ⊓ S) (p := q) hzq'
        have hzq'P : zq' ∈ P :=
          element_mem_pPrimeCore_of_order_coprime_of_nilpotent_local (H := F) (p := q)
            hFnil hzq'F hzq'cop
        have hxzq' : zq' * x = x * zq' :=
          (Subgroup.mem_centralizer_iff.mp hxcentP) zq' hzq'P
        calc
          z * x = (zq * zq') * x := by rw [hzeq]
          _ = zq * (zq' * x) := by group
          _ = zq * (x * zq') := by rw [hxzq']
          _ = (zq * x) * zq' := by group
          _ = (x * zq) * zq' := by rw [hxzq]
          _ = x * (zq * zq') := by group
          _ = x * z := by rw [hzeq]
      · exact (Subgroup.mem_centralizer_iff.mp (hFcE hxF)) z hzE
    refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ hyFSE
    · intro z hz
      calc
        z⁻¹ * x = z⁻¹ * (x * z * z⁻¹) := by group
        _ = z⁻¹ * (z * x * z⁻¹) := by rw [hgen z hz]
        _ = x * z⁻¹ := by group
    · simp
    · intro a b _ha _hb hab hba
      calc
        (a * b) * x = a * (b * x) := by group
        _ = a * (x * b) := by rw [hba]
        _ = (a * x) * b := by group
        _ = (x * a) * b := by rw [hab]
        _ = x * (a * b) := by group
  have hxSF : x ∈ generalizedFittingSubgroupOf A ⊓
      Subgroup.centralizer (S : Set G) :=
    Subgroup.mem_inf.mpr ⟨(le_sup_left : F ≤ generalizedFittingSubgroupOf A) hxF, hxS⟩
  have hxS' : x ∈ S := hCS hxSF
  let T : Subgroup G := qCoreOf A q ⊓ S
  have hTleS : T ≤ S := inf_le_right
  have hTnorm : IsNormalIn T S := by
    refine ⟨inf_le_right, ?_⟩
    intro s hs t ht
    have hsA : s ∈ A := hSF.trans (fstar_generalizedFittingSubgroupOf_le A) hs
    have ht' : s * t * s⁻¹ ∈ qCoreOf A q :=
      (qCoreOf_normal_in A q).2 s hsA t ht.1
    have ht'' : s * t * s⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem hs ht.2) (S.inv_mem hs)
    exact Subgroup.mem_inf.mpr ⟨ht', ht''⟩
  have hTq : IsPGroup q T := IsPGroup.to_inf_left (qCoreOf_isPGroup A q)
  exact le_qCoreOf_of_normal_isPGroup S T q hTleS (by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTleS]
    exact le_normalizer_of_isNormalIn hTnorm) hTq
    (Subgroup.mem_inf.mpr ⟨hxA, hxS'⟩)

/-! ## The `(i)`-assembly: `O_p(B) ∩ A = 1` for `p ∉ π(F(A))` -/

/-- `O_p(F(A)) = 1` when `p ∉ π(F(A))`. -/
private theorem qCoreOf_fitting_eq_bot_of_not_mem_primesOfOrder_local
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hpnF : p ∉ primesOfOrder (fittingSubgroupOf A)) :
    qCoreOf (fittingSubgroupOf A) p = ⊥ := by
  let F : Subgroup G := fittingSubgroupOf A
  apply le_bot_iff.mp
  intro x hx
  have hxF : x ∈ F := qCoreOf_le F p hx
  by_contra hx1
  have hxne : x ≠ 1 := hx1
  let xQ : ↥(qCoreOf F p) := ⟨x, hx⟩
  let : Fact p.Prime := ⟨hp⟩
  rcases (IsPGroup.iff_orderOf.mp (qCoreOf_isPGroup F p)) xQ with ⟨k, hk⟩
  have hordG : orderOf x = orderOf xQ := (Subgroup.orderOf_coe xQ)
  have hkpos : 0 < k := by
    by_contra hk0
    have hx1' : x = 1 := by
      have hord1 : orderOf x = 1 := by
        have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
        rw [hordG, hk, hk0']
        simp
      exact orderOf_eq_one_iff.mp hord1
    exact hxne hx1'
  have horder : orderOf x = p ^ k := by rw [hordG, hk]
  have hdvd : p ∣ Nat.card (↥F) := by
    have hpdvd : p ∣ orderOf x := by
      rw [horder]
      simpa using (pow_dvd_pow p (Nat.succ_le_iff.mpr hkpos))
    exact hpdvd.trans (Subgroup.orderOf_dvd_natCard F hxF)
  exact hpnF (by
    simpa [primesOfOrder, F] using
      (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩))

/-- `O_p(A) = 1` when `p ∉ π(F(A))`. -/
private theorem qCoreOf_eq_bot_of_not_mem_primesOfOrder_local
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hpnF : p ∉ primesOfOrder (fittingSubgroupOf A)) :
    qCoreOf A p = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxle : x ∈ qCoreOf (fittingSubgroupOf A) p :=
    fstar_qCoreOf_le_qCoreOf_fittingSubgroupOf A p hp hx
  exact Subgroup.mem_bot.mp
    (by
      have hbot : qCoreOf (fittingSubgroupOf A) p = ⊥ :=
        qCoreOf_fitting_eq_bot_of_not_mem_primesOfOrder_local A p hp hpnF
      simpa [hbot] using hxle)

/-- A perfect subgroup of `H` lies in `O^p(H)`. -/
public theorem perfect_le_pResidualOf_local
    {G : Type u} [Group G] [Finite G]
    (H K : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hKH : K ≤ H) (hKperf : Group.IsPerfect K) :
    K ≤ pResidualOf H p := by
  classical
  let N : Subgroup G := pResidualOf H p
  let : Fact p.Prime := ⟨hp⟩
  have hNnorm : (N.subgroupOf H).Normal :=
    fstar_pResidualOf_subgroupOf_normal H p
  let π : K →* H ⧸ N.subgroupOf H :=
    (QuotientGroup.mk' (N.subgroupOf H)).comp (Subgroup.inclusion hKH)
  have hπperf : Group.IsPerfect (π.range) := by
    let : Group.IsPerfect (↥K) := hKperf
    exact Group.IsPerfect.range (G := ↥K) (f := π)
  have hπp : IsPGroup p (π.range) := by
    have hQ : IsPGroup p (H ⧸ N.subgroupOf H) :=
      fstar_isPGroup_quotient_pResidualOf H p hp
    exact hQ.to_subgroup π.range
  have hπrange_bot : π.range = ⊥ := by
    by_contra hne
    have : Nontrivial (↥π.range) :=
      (Subgroup.nontrivial_iff_ne_bot (H := π.range)).mpr hne
    have : Group.IsPerfect (↥π.range) := hπperf
    have hnil : Group.IsNilpotent (↥π.range) := hπp.isNilpotent
    exact (Group.IsPerfect.not_isNilpotent (G := ↥π.range)) hnil
  intro k hk
  have hπ1 : π ⟨k, hk⟩ = 1 := by
    have hmem : π ⟨k, hk⟩ ∈ π.range := ⟨⟨k, hk⟩, rfl⟩
    exact Subgroup.mem_bot.mp (by simpa [hπrange_bot] using hmem)
  have hkN : (⟨k, hKH hk⟩ : ↥H) ∈ N.subgroupOf H :=
    (QuotientGroup.eq_one_iff (N := N.subgroupOf H) (x := ⟨k, hKH hk⟩)).1 hπ1
  exact (Subgroup.mem_subgroupOf).1 hkN

/-- The component layer of `A` lies in `O^p(S)` whenever it lies in `S`
(a perfect subgroup of `S`, so it survives in the perfect quotient
`S/O^p(S)`, which is a `p`-group and hence trivial). -/
private theorem componentLayer_le_pResidualOf_local
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G) (hES : componentLayerOf A ≤ S)
    (p : ℕ) (hp : p.Prime) :
    componentLayerOf A ≤ pResidualOf S p := by
  rw [componentLayerOf]
  refine sSup_le ?_
  intro E hEcomp
  have hEperf : Group.IsPerfect E := (Group.isPerfect_def).2 hEcomp.2.2.2.1
  exact perfect_le_pResidualOf_local S E p hp
    ((le_sSup (s := {E' : Subgroup G | IsComponentOf E' A}) (a := E) hEcomp).trans hES)
    hEperf

/-! ## Transfer of the F*-self-centralizing facts to the subgroup `A` -/

private theorem isSubnormal_of_isComponentOf_top_local
    {G : Type u} [Group G] {K : Subgroup G}
    (hK : IsComponentOf K (⊤ : Subgroup G)) :
    K.IsSubnormal := by
  have h' : ((K.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).IsSubnormal :=
    hK.2.1.map (f := (⊤ : Subgroup G).subtype)
      (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
  rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : K ≤ (⊤ : Subgroup G))] at h'

private theorem isComponentOf_of_isComponentOf_top_map_local
    {G : Type u} [Group G] {B : Subgroup G} {E : Subgroup (↥B)}
    (hE : IsComponentOf E (⊤ : Subgroup (↥B))) :
    IsComponentOf (E.map B.subtype) B := by
  refine ⟨Subgroup.map_subtype_le E, ?_, ?_⟩
  · have hEsub : E.IsSubnormal := isSubnormal_of_isComponentOf_top_local hE
    have hEq : (E.map B.subtype).subgroupOf B = E := by
      apply le_antisymm
      · intro y hy
        rw [Subgroup.mem_subgroupOf] at hy
        rcases (Subgroup.mem_map).1 hy with ⟨x, hx, hxy⟩
        have hyx : x = y := B.subtype_injective (by simpa using hxy)
        simpa [hyx] using hx
      · intro y hy
        rw [Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_map).mpr ⟨y, hy, rfl⟩
    simpa [hEq] using hEsub
  · exact isQuasisimple_mulEquiv_local
      (Subgroup.equivMapOfInjective E B.subtype B.subtype_injective) hE.2.2

/-- The component layer is preserved by the subgroup embedding:
`E(⊤_{B})` maps onto `E(B)`. -/
private theorem componentLayer_top_map_eq_componentLayerOf_local
    {G : Type u} [Group G] (B : Subgroup G) :
    (componentLayerOf (⊤ : Subgroup (↥B))).map B.subtype = componentLayerOf B := by
  apply le_antisymm
  · refine (Subgroup.map_le_iff_le_comap).2 ?_
    change sSup {E : Subgroup (↥B) | IsComponentOf E (⊤ : Subgroup (↥B))} ≤
      Subgroup.comap B.subtype (componentLayerOf B)
    refine sSup_le ?_
    intro E hE
    intro y hy
    rw [Subgroup.mem_comap]
    exact le_sSup (s := {E' : Subgroup G | IsComponentOf E' B})
      (a := E.map B.subtype)
      (isComponentOf_of_isComponentOf_top_map_local hE)
      (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  · change sSup {E : Subgroup G | IsComponentOf E B} ≤
      Subgroup.map B.subtype
        (sSup {E : Subgroup (↥B) | IsComponentOf E (⊤ : Subgroup (↥B))})
    refine sSup_le ?_
    intro E hE
    intro y hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hE.1 hy⟩,
        Subgroup.mem_sSup_of_mem
          (fstar_isComponentOf_subgroupOf_top hE)
          (by
            rw [Subgroup.mem_subgroupOf]
            exact hy),
        rfl⟩

/-- The image of the Fitting subgroup under a surjective homomorphism lies
in the Fitting subgroup of the target. -/
private theorem map_fittingSubgroup_le_of_surjective_local
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) :
    (fittingSubgroup G).map f ≤ fittingSubgroup H := by
  have hmap_normal : ((fittingSubgroup G).map f).Normal :=
    Subgroup.Normal.map (H := fittingSubgroup G) inferInstance f hf
  have hmap_nil : Group.IsNilpotent ↥((fittingSubgroup G).map f) := by
    have : Group.IsNilpotent ↥(fittingSubgroup G) := by infer_instance
    let ψ : fittingSubgroup G →* ↥((fittingSubgroup G).map f) :=
      { toFun := fun g => ⟨f g, Subgroup.mem_map.mpr ⟨g.1, g.2, rfl⟩⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp [map_mul] }
    have hψsurj : Function.Surjective ψ := by
      intro x
      rcases (Subgroup.mem_map).1 x.2 with ⟨g, hg, hx⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      apply Subtype.ext
      exact hx
    exact Group.nilpotent_of_surjective ψ hψsurj
  exact le_sSup ⟨hmap_normal, hmap_nil⟩

/-- The Fitting subgroup commutes with a group isomorphism. -/
private theorem map_fittingSubgroup_of_mulEquiv_local
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) :
    (fittingSubgroup G).map e.toMonoidHom = fittingSubgroup H := by
  apply le_antisymm
  · exact map_fittingSubgroup_le_of_surjective_local e.toMonoidHom e.surjective
  · have hback : (fittingSubgroup H).map e.symm.toMonoidHom ≤ fittingSubgroup G :=
      map_fittingSubgroup_le_of_surjective_local e.symm.toMonoidHom e.symm.surjective
    have hmap : ((fittingSubgroup H).map e.symm.toMonoidHom).map e.toMonoidHom ≤
        (fittingSubgroup G).map e.toMonoidHom :=
      Subgroup.map_mono (f := e.toMonoidHom) hback
    have hleft : ((fittingSubgroup H).map e.symm.toMonoidHom).map e.toMonoidHom =
        fittingSubgroup H := by
      rw [Subgroup.map_map]
      have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]
    rw [hleft] at hmap
    exact hmap

/-- `F*(⊤_{B})` maps onto `F*(B)`. -/
private theorem map_generalizedFittingSubgroupOf_top_subtype_local
    {G : Type u} [Group G] [Finite G] (B : Subgroup G) :
    (generalizedFittingSubgroupOf (⊤ : Subgroup (↥B))).map B.subtype =
      generalizedFittingSubgroupOf B := by
  rw [generalizedFittingSubgroupOf, generalizedFittingSubgroupOf, Subgroup.map_sup]
  rw [componentLayer_top_map_eq_componentLayerOf_local B]
  have : Finite (↥(⊤ : Subgroup (↥B))) :=
    Finite.of_equiv (↥B) (Subgroup.topEquiv (G := ↥B)).toEquiv.symm
  change Subgroup.map B.subtype ((fittingSubgroup (↥(⊤ : Subgroup (↥B)))).map
      (⊤ : Subgroup (↥B)).subtype) ⊔ componentLayerOf B =
    Subgroup.map B.subtype (fittingSubgroup (↥B)) ⊔ componentLayerOf B
  have hTopSubtype :
      (⊤ : Subgroup (↥B)).subtype =
        (Subgroup.topEquiv (G := ↥B)).toMonoidHom := by
    ext x
    rfl
  rw [hTopSubtype]
  rw [map_fittingSubgroup_of_mulEquiv_local (Subgroup.topEquiv (G := ↥B))]

/-- `C_G(F*(B)) ∩ B ≤ F*(B)`: the generalized Fitting subgroup is
self-centralizing inside any subgroup `B`. -/
private theorem centralizer_intersection_fstar_le_fstar_local
    {G : Type u} [Group G] [Finite G] (B : Subgroup G) :
    Subgroup.centralizer ((generalizedFittingSubgroupOf B : Set G)) ⊓ B ≤
      generalizedFittingSubgroupOf B := by
  let Y : Subgroup (↥B) := generalizedFittingSubgroupOf (⊤ : Subgroup (↥B))
  have hYcent : Subgroup.centralizer (Y : Set (↥B)) ≤ Y :=
    fstar_self_centralizing (G := ↥B)
  intro x hx
  rcases hx with ⟨hxC, hxB⟩
  let b : ↥B := ⟨x, hxB⟩
  have hbcent : b ∈ Subgroup.centralizer (Y : Set (↥B)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyG : (y : G) ∈ generalizedFittingSubgroupOf B := by
      rw [← map_generalizedFittingSubgroupOf_top_subtype_local B]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hxy := (Subgroup.mem_centralizer_iff.mp hxC) (y : G) hyG
    apply Subtype.ext
    exact hxy
  have hbY : b ∈ Y := hYcent hbcent
  have hxY : x ∈ Y.map B.subtype :=
    Subgroup.mem_map.mpr ⟨b, hbY, rfl⟩
  rwa [map_generalizedFittingSubgroupOf_top_subtype_local B] at hxY

/-- The center of `F*(A)` lies in `F(A)`. -/
private theorem center_generalizedFitting_le_fittingSubgroupOf_local
    {G : Type u} [Group G] [Finite G] (A : Subgroup G) :
    (Subgroup.center (↥(generalizedFittingSubgroupOf A))).map
      (generalizedFittingSubgroupOf A).subtype ≤ fittingSubgroupOf A := by
  let X : Subgroup G := generalizedFittingSubgroupOf A
  let Z : Subgroup G := (Subgroup.center (↥X)).map X.subtype
  have hZX : Z ≤ X := Subgroup.map_subtype_le (Subgroup.center (↥X))
  have hZnorm : IsNormalIn Z A := by
    simpa [Z, X] using
      (fstar_characteristic_subgroupOf_map_normal_in (F := X)
        (K := Subgroup.center (↥X)) (by infer_instance)
        (fstar_generalizedFittingSubgroupOf_isNormalIn A))
  have hZEcomm : IsMulCommutative (↥Z) := by
    dsimp [Z]
    infer_instance
  have hZnil : Group.IsNilpotent Z := by
    refine ⟨1, ?_⟩
    rw [Subgroup.upperCentralSeries_one_eq_top_iff]
    exact hZEcomm
  exact le_fittingSubgroupOf_of_isNormalIn_nilpotent (L := A) (N := Z)
    (hZX.trans (fstar_generalizedFittingSubgroupOf_le A)) hZnorm hZnil

/-! ## The `(ii)`-assembly: nilpotent-core and Fitting-subgroup helpers -/

/-- A `p'`-element of a nilpotent subgroup centralizes every `p`-subgroup
of that subgroup. -/
private theorem pPrime_element_centralizes_pSubgroup_of_nilpotent_local
    {G : Type u} [Group G] [Finite G]
    {H P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hHnil : Group.IsNilpotent H) (hPH : P ≤ H) (hPp : IsPGroup p P)
    {z : G} (hzH : z ∈ H) (hzcop : Nat.Coprime p (orderOf z)) :
    z ∈ Subgroup.centralizer (P : Set G) := by
  have hzPP : z ∈ (pPrimeCore p (↥H)).map H.subtype :=
    element_mem_pPrimeCore_of_order_coprime_of_nilpotent_local (H := H) (p := p)
      hHnil hzH hzcop
  have hPleC : P ≤ qCoreOf H p :=
    pSubgroup_le_qCoreOf_of_nilpotent_local (H := H) (p := p) hHnil hPH hPp
  have hPPc : (pPrimeCore p (↥H)).map H.subtype ≤
      Subgroup.centralizer ((qCoreOf H p : Subgroup G) : Set G) :=
    pPrimeCore_map_le_centralizer_pCore_map (p := p) H
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact (Subgroup.mem_centralizer_iff.mp (hPPc hzPP)) t (hPleC ht)

/-- An element of a nilpotent subgroup splits into its `p`-part and
`p'`-part (both in the cyclic subgroup generated by the element). -/
private theorem mem_pCore_pPrimeCore_decompose_local
    {G : Type u} [Group G] [Finite G] {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hHnil : Group.IsNilpotent H) {x : G} (hxH : x ∈ H) :
    ∃ xₚ xₚ' : G,
      x = xₚ * xₚ' ∧ xₚ ∈ qCoreOf H p ∧
        xₚ' ∈ (pPrimeCore p (↥H)).map H.subtype ∧ Commute xₚ xₚ' := by
  classical
  let Q : Subgroup G := qCoreOf H p
  let QQ : Subgroup G := (pPrimeCore p (↥H)).map H.subtype
  have htop : (⊤ : Subgroup (↥H)) ≤ pCore p (↥H) ⊔ pPrimeCore p (↥H) :=
    nilpotent_top_le_pCore_sup_pPrimeCore (Q := ↥H) (p := p) hHnil
  have hxmem : (⟨x, hxH⟩ : ↥H) ∈ pCore p (↥H) ⊔ pPrimeCore p (↥H) := htop trivial
  have hxsup : x ∈ Q ⊔ QQ := by
    have hmap_eq :
        ((pCore p (↥H) ⊔ pPrimeCore p (↥H)) : Subgroup (↥H)).map H.subtype =
          Q ⊔ QQ := by
      rw [Subgroup.map_sup]
      rfl
    rw [← hmap_eq]
    exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hxmem, rfl⟩
  have hEF : QQ ≤ Subgroup.centralizer (Q : Set G) :=
    pPrimeCore_map_le_centralizer_pCore_map (p := p) H
  rcases mem_sup_decompose_of_centralizes (F := Q) (E := QQ) hxsup hEF with
    ⟨xₚ, hxₚ, xₚ', hxₚ', hxeq⟩
  refine ⟨xₚ, xₚ', hxeq, hxₚ, hxₚ', ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp (hEF hxₚ')) xₚ hxₚ

/-- The Fitting subgroup of a subnormal subgroup lies in the Fitting
subgroup of the ambient subgroup. -/
private theorem fittingSubgroupOf_le_fittingSubgroupOf_of_subnormal_local
    {G : Type u} [Group G] [Finite G]
    {A S : Subgroup G} (hSA : S ≤ A) (hSsub : (S.subgroupOf A).IsSubnormal) :
    fittingSubgroupOf S ≤ fittingSubgroupOf A := by
  classical
  rcases (Subgroup.IsSubnormal.isSubnormal_iff (G := ↥A) (H := S.subgroupOf A)).1 hSsub with
    ⟨n, f, hmono, hnorm, hf0, hfn⟩
  have hmain : ∀ i : ℕ, i ≤ n →
      fittingSubgroupOf S ≤ fittingSubgroupOf ((f i).map A.subtype) := by
    intro i hi
    induction i with
    | zero =>
      have hK0 : (f 0).map A.subtype = S := by
        rw [hf0]
        exact Subgroup.map_subgroupOf_eq_of_le hSA
      rw [hK0]
    | succ i ih =>
      let Ni : Subgroup G := (f i).map A.subtype
      let Nip : Subgroup G := (f (i + 1)).map A.subtype
      have hNiNip : IsNormalIn Ni Nip := by
        refine ⟨Subgroup.map_mono (f := A.subtype) (hmono (Nat.le_succ i)), ?_⟩
        intro a ha x hx
        rcases (Subgroup.mem_map).1 hx with ⟨x0, hx0, rfl⟩
        rcases (Subgroup.mem_map).1 ha with ⟨a0, ha0, rfl⟩
        have hconj : a0 * x0 * a0⁻¹ ∈ f i :=
          (Subgroup.normal_subgroupOf_iff (hmono (Nat.le_succ i))).mp (hnorm i)
            x0 a0 hx0 ha0
        exact Subgroup.mem_map.mpr ⟨a0 * x0 * a0⁻¹, hconj, by simp [mul_assoc]⟩
      have hFnorm : IsNormalIn (fittingSubgroupOf Ni) Nip := by
        simpa [fittingSubgroupOf, Ni] using
          (fstar_characteristic_subgroupOf_map_normal_in (F := Ni)
            (K := fittingSubgroup ↥Ni) (by infer_instance) hNiNip)
      have hFleF' : fittingSubgroupOf Ni ≤ fittingSubgroupOf Nip :=
        le_fittingSubgroupOf_of_isNormalIn_nilpotent (L := Nip) (N := fittingSubgroupOf Ni)
          (fun x hx => hNiNip.1 ((Subgroup.map_subtype_le (H := Ni)
            (K := fittingSubgroup ↥Ni)) hx)) hFnorm (fittingSubgroupOf_isNilpotent Ni)
      exact (ih (Nat.le_of_succ_le hi)).trans hFleF'
  have htop : (f n).map A.subtype = A := by
    rw [hfn]
    ext x
    simp
  exact (hmain n (le_rfl : n ≤ n)).trans (le_of_eq (by rw [htop]))

/-- A subnormal nilpotent subgroup lies in the Fitting subgroup. -/
private theorem le_fittingSubgroupOf_of_isSubnormal_nilpotent_local
    {G : Type u} [Group G] [Finite G]
    {A N : Subgroup G} (hNA : N ≤ A)
    (hNsub : (N.subgroupOf A).IsSubnormal) (hNnil : Group.IsNilpotent N) :
    N ≤ fittingSubgroupOf A := by
  have htop : fittingSubgroupOf N = N := by
    unfold fittingSubgroupOf
    rw [fitting_eq_top_of_nilpotent (↥N)]
    simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype N)
  exact (le_of_eq htop.symm).trans
    (fittingSubgroupOf_le_fittingSubgroupOf_of_subnormal_local hNA hNsub)

/-- `F(S) = F(A) ∩ S` for `S` subnormal in `F*(A)` (Gagen 10.4(a)). -/
private theorem fittingSubgroupOf_eq_inf_of_subnormal_local
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal) :
    fittingSubgroupOf S = fittingSubgroupOf A ⊓ S := by
  classical
  let F : Subgroup G := fittingSubgroupOf A
  have hSleA : S ≤ A := hSF.trans (fstar_generalizedFittingSubgroupOf_le A)
  have hSsubA : (S.subgroupOf A).IsSubnormal :=
    fstar_isSubnormal_subgroupOf_of_subnormal_subgroupOf_normal (S := S)
      (X := generalizedFittingSubgroupOf A) (A := A) hSF hSsub
      (fstar_generalizedFittingSubgroupOf_le A) (fstar_generalizedFittingSubgroupOf_isNormalIn A)
  have hFSleFA : fittingSubgroupOf S ≤ F :=
    fittingSubgroupOf_le_fittingSubgroupOf_of_subnormal_local hSleA hSsubA
  have hFSleS : fittingSubgroupOf S ≤ S := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  have hKleS : F ⊓ S ≤ S := inf_le_right
  have hKnorm : IsNormalIn (F ⊓ S) S := by
    refine ⟨inf_le_right, ?_⟩
    intro s hs z hz
    have hsA : s ∈ A := hSleA hs
    have hz'F : s * z * s⁻¹ ∈ F :=
      (fittingSubgroupOf_isNormalIn A).2 s hsA z hz.1
    have hz'S : s * z * s⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem hs hz.2) (S.inv_mem hs)
    exact Subgroup.mem_inf.mpr ⟨hz'F, hz'S⟩
  have hKnil : Group.IsNilpotent (↥(F ⊓ S)) := by
    let : Group.IsNilpotent (↥F) := fittingSubgroupOf_isNilpotent A
    have hInst : Group.IsNilpotent (↥((F ⊓ S).subgroupOf F)) := by
      infer_instance
    exact Group.nilpotent_of_mulEquiv
      (G := ↥((F ⊓ S).subgroupOf F)) (G' := ↥(F ⊓ S))
      (Subgroup.subgroupOfEquivOfLe (H := F ⊓ S) (K := F)
        (show F ⊓ S ≤ F from inf_le_left)) (_h := hInst)
  have hKleFS : F ⊓ S ≤ fittingSubgroupOf S :=
    le_fittingSubgroupOf_of_isNormalIn_nilpotent (L := S) (N := F ⊓ S)
      hKleS hKnorm hKnil
  apply le_antisymm
  · exact le_inf hFSleFA hFSleS
  · exact hKleFS

/-- `⟨g⟩` is commutative. -/
private theorem isMulCommutative_zpowers_local {G : Type u} [Group G] (g : G) :
    IsMulCommutative (↥(Subgroup.zpowers g)) := by
  exact ⟨⟨fun a b => by
    rcases (Subgroup.mem_zpowers_iff).1 a.2 with ⟨n, hn⟩
    rcases (Subgroup.mem_zpowers_iff).1 b.2 with ⟨m, hm⟩
    apply Subtype.ext
    change (a : G) * (b : G) = (b : G) * (a : G)
    rw [← hn, ← hm]
    calc
      g ^ n * g ^ m = g ^ (n + m) := by rw [zpow_add]
      _ = g ^ (m + n) := by rw [add_comm]
      _ = g ^ m * g ^ n := by rw [zpow_add]⟩⟩

/-- `⟨g⟩` is nilpotent. -/
private theorem isNilpotent_zpowers_local {G : Type u} [Group G] (g : G) :
    Group.IsNilpotent (Subgroup.zpowers g) := by
  refine ⟨1, ?_⟩
  rw [Subgroup.upperCentralSeries_one_eq_top_iff]
  exact isMulCommutative_zpowers_local g

/-- The center of the component layer of `A` lies in `F(A)`. -/
private theorem center_componentLayer_le_fittingSubgroupOf_local
    {G : Type u} [Group G] [Finite G] (A : Subgroup G) :
    (Subgroup.center (↥(componentLayerOf A))).map (componentLayerOf A).subtype ≤
      fittingSubgroupOf A := by
  let E : Subgroup G := componentLayerOf A
  let Z : Subgroup G := (Subgroup.center (↥E)).map E.subtype
  have hZE : Z ≤ E := Subgroup.map_subtype_le (Subgroup.center (↥E))
  have hZnorm : IsNormalIn Z A := by
    simpa [Z, E] using
      (fstar_characteristic_subgroupOf_map_normal_in (F := E)
        (K := Subgroup.center (↥E)) (by infer_instance)
        (fstar_componentLayerOf_isNormalIn A))
  have hZcomm : IsMulCommutative (↥Z) := by
    dsimp [Z]
    infer_instance
  have hZnil : Group.IsNilpotent Z := by
    refine ⟨1, ?_⟩
    rw [Subgroup.upperCentralSeries_one_eq_top_iff]
    exact hZcomm
  exact le_fittingSubgroupOf_of_isNormalIn_nilpotent (L := A) (N := Z)
    ((hZE.trans (le_sup_right : E ≤ generalizedFittingSubgroupOf A)).trans
      (fstar_generalizedFittingSubgroupOf_le A)) hZnorm hZnil

/-- The center of the component layer of `A` lies in the center of `F(A)`. -/
private theorem center_componentLayer_le_center_fitting_local
    {G : Type u} [Group G] [Finite G] (A : Subgroup G) :
    (Subgroup.center (↥(componentLayerOf A))).map (componentLayerOf A).subtype ≤
      (Subgroup.center (↥(fittingSubgroupOf A))).map (fittingSubgroupOf A).subtype := by
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  have hZcF : (Subgroup.center (↥E)).map E.subtype ≤ Subgroup.centralizer (F : Set G) := by
    have hFE : ⁅F, E⁆ = ⊥ := Subgroup.commutator_comm E F ▸ layer_centralizes_fitting A
    have hFcE : F ≤ Subgroup.centralizer (E : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := F) (H₂ := E)).1 hFE
    intro z hz
    rcases (Subgroup.mem_map).1 hz with ⟨z0, hz0, rfl⟩
    have hzE : (z0 : G) ∈ E := z0.2
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hFcE hy)) (z0 : G) hzE).symm
  intro z hz
  rcases (Subgroup.mem_map).1 hz with ⟨z0, hz0, rfl⟩
  have hzF : (z0 : G) ∈ F :=
    center_componentLayer_le_fittingSubgroupOf_local A
      (Subgroup.mem_map.mpr ⟨z0, hz0, rfl⟩)
  have hzZ' : (⟨(z0 : G), hzF⟩ : ↥F) ∈ Subgroup.center (↥F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp
      (hZcF (Subgroup.mem_map.mpr ⟨z0, hz0, rfl⟩))) y.1 y.2
  exact Subgroup.mem_map.mpr ⟨⟨(z0 : G), hzF⟩, hzZ', rfl⟩

/-- `F(A) ∩ E(A) = Z(E(A))`. -/
private theorem inf_fitting_componentLayer_eq_center_componentLayer_local
    {G : Type u} [Group G] [Finite G] (A : Subgroup G) :
    fittingSubgroupOf A ⊓ componentLayerOf A =
      (Subgroup.center (↥(componentLayerOf A))).map (componentLayerOf A).subtype := by
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let Z : Subgroup G := (Subgroup.center (↥E)).map E.subtype
  have hFE : ⁅F, E⁆ = ⊥ := Subgroup.commutator_comm E F ▸ layer_centralizes_fitting A
  have hFcE : F ≤ Subgroup.centralizer (E : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := F) (H₂ := E)).1 hFE
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨hxF, hxE⟩
    have hxZ' : (⟨x, hxE⟩ : ↥E) ∈ Subgroup.center (↥E) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hFcE hxF)) y.1 y.2
    exact Subgroup.mem_map.mpr ⟨⟨x, hxE⟩, hxZ', rfl⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨z, hz, rfl⟩
    exact Subgroup.mem_inf.mpr
      ⟨center_componentLayer_le_fittingSubgroupOf_local A
        (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩), z.2⟩

/-- Every `p'`-element of `S` centralizes `O_p(S)` (Gagen 12.4(v), first
claim): `S = F(S)·E(A)`, the `p'`-element's `F`-part has trivial `p`-part
after cancellation with its `E`-part, and both parts centralize `O_p(S)`. -/
private theorem pPrime_element_centralizes_qCoreOf_S_local
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (p : ℕ) (hp : p.Prime) :
    ∀ s : G, s ∈ S → Nat.Coprime p (orderOf s) →
      s ∈ Subgroup.centralizer ((qCoreOf S p : Subgroup G) : Set G) := by
  classical
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let P : Subgroup G := qCoreOf S p
  let : Fact p.Prime := ⟨hp⟩
  have hFnil : Group.IsNilpotent F := fittingSubgroupOf_isNilpotent A
  have hFS_eq : fittingSubgroupOf S = F ⊓ S :=
    fittingSubgroupOf_eq_inf_of_subnormal_local A S hSF hSsub
  have hPleFS : P ≤ fittingSubgroupOf S :=
    le_fittingSubgroupOf_of_isNormalIn_nilpotent (L := S) (N := P)
      (qCoreOf_le S p) (qCoreOf_normal_in S p) (qCoreOf_isPGroup S p).isNilpotent
  have hPleF : P ≤ F := (hPleFS.trans (le_of_eq hFS_eq)).trans inf_le_left
  have hFcE : F ≤ Subgroup.centralizer (E : Set G) := by
    have hcomm : ⁅F, E⁆ = ⊥ := Subgroup.commutator_comm E F ▸ layer_centralizes_fitting A
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := F) (H₂ := E)).1 hcomm
  have hEcF : E ≤ Subgroup.centralizer (F : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := E) (H₂ := F)).1
      (layer_centralizes_fitting A)
  have hEcP : E ≤ Subgroup.centralizer (P : Set G) :=
    hEcF.trans (Subgroup.centralizer_le (show (P : Set G) ⊆ (F : Set G) from hPleF))
  have hZEcP : (Subgroup.center (↥E)).map E.subtype ≤
      Subgroup.centralizer (P : Set G) := by
    have hZcF : (Subgroup.center (↥E)).map E.subtype ≤
        Subgroup.centralizer (F : Set G) := by
      have hZF : (Subgroup.center (↥E)).map E.subtype ≤
          (Subgroup.center (↥F)).map F.subtype :=
        center_componentLayer_le_center_fitting_local A
      intro z hz
      rcases (Subgroup.mem_map).1 (hZF hz) with ⟨zF, hzF, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzF) ⟨y, hy⟩)
    exact hZcF.trans (Subgroup.centralizer_le (show (P : Set G) ⊆ (F : Set G) from hPleF))
  have hEF' : E ≤ Subgroup.centralizer ((F ⊓ S : Subgroup G) : Set G) :=
    hEcF.trans (Subgroup.centralizer_le
      (show ((F ⊓ S : Subgroup G) : Set G) ⊆ (F : Set G) from inf_le_left))
  intro s hs hscop
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have hsFSE : s ∈ (F ⊓ S) ⊔ E := by
    rw [← S_eq_sup_local A S hSF hSsub hCS]
    exact hs
  rcases mem_sup_decompose_of_centralizes (F := F ⊓ S) (E := E) hsFSE hEF' with
    ⟨f, hf, e, he, hseq⟩
  have hfe_comm : Commute f e :=
    (Subgroup.mem_centralizer_iff.mp (hEF' he)) f hf
  let Hf : Subgroup G := Subgroup.zpowers f
  let He : Subgroup G := Subgroup.zpowers e
  have hHf_le : Hf ≤ F ⊓ S := Subgroup.zpowers_le.mpr hf
  have hHe_le : He ≤ E := Subgroup.zpowers_le.mpr he
  rcases mem_pCore_pPrimeCore_decompose_local (H := Hf) (p := p)
      (isNilpotent_zpowers_local f) (Subgroup.mem_zpowers f) with
    ⟨fₚ, fₚ', hfeq, hfₚHf, hfₚ'Hf, hfₚₚ'_comm⟩
  rcases mem_pCore_pPrimeCore_decompose_local (H := He) (p := p)
      (isNilpotent_zpowers_local e) (Subgroup.mem_zpowers e) with
    ⟨eₚ, eₚ', heeq, heₚHe, heₚ'He, heₚₚ'_comm⟩
  have hHf_c_He : Hf ≤ Subgroup.centralizer (He : Set G) := by
    have hfce : f ∈ Subgroup.centralizer (He : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases (Subgroup.mem_zpowers_iff).1 hy with ⟨n, rfl⟩
      exact (hfe_comm.zpow_right n).symm
    simpa [Hf] using (Subgroup.zpowers_le.mpr hfce)
  have hfₚHf' : fₚ ∈ Hf := qCoreOf_le Hf p hfₚHf
  have hfₚ'Hf' : fₚ' ∈ Hf :=
    Subgroup.map_subtype_le (H := Hf) (K := pPrimeCore p (↥Hf)) hfₚ'Hf
  have heₚHe' : eₚ ∈ He := qCoreOf_le He p heₚHe
  have heₚ'He' : eₚ' ∈ He :=
    Subgroup.map_subtype_le (H := He) (K := pPrimeCore p (↥He)) heₚ'He
  have hfₚ_eₚ : Commute fₚ eₚ :=
    ((Subgroup.mem_centralizer_iff.mp (hHf_c_He hfₚHf')) eₚ heₚHe').symm
  have hfₚ_eₚ' : Commute fₚ eₚ' :=
    ((Subgroup.mem_centralizer_iff.mp (hHf_c_He hfₚHf')) eₚ' heₚ'He').symm
  have hfₚ'_eₚ : Commute fₚ' eₚ :=
    ((Subgroup.mem_centralizer_iff.mp (hHf_c_He hfₚ'Hf')) eₚ heₚHe').symm
  have hfₚ'_eₚ' : Commute fₚ' eₚ' :=
    ((Subgroup.mem_centralizer_iff.mp (hHf_c_He hfₚ'Hf')) eₚ' heₚ'He').symm
  have hsxeq : fₚ * eₚ * (fₚ' * eₚ') = s := by
    calc
      fₚ * eₚ * (fₚ' * eₚ') = fₚ * (eₚ * fₚ') * eₚ' := by group
      _ = fₚ * (fₚ' * eₚ) * eₚ' := by rw [← hfₚ'_eₚ]
      _ = (fₚ * fₚ') * (eₚ * eₚ') := by group
      _ = f * e := by rw [← hfeq, ← heeq]
      _ = s := by rw [← hseq]
  have hxy_comm : Commute (fₚ * eₚ) (fₚ' * eₚ') := by
    calc
      (fₚ * eₚ) * (fₚ' * eₚ') = fₚ * (eₚ * fₚ') * eₚ' := by group
      _ = fₚ * (fₚ' * eₚ) * eₚ' := by rw [← hfₚ'_eₚ]
      _ = (fₚ * fₚ') * (eₚ * eₚ') := by group
      _ = (fₚ' * fₚ) * (eₚ' * eₚ) := by rw [hfₚₚ'_comm, heₚₚ'_comm]
      _ = (fₚ' * eₚ') * (fₚ * eₚ) := by
        calc
          (fₚ' * fₚ) * (eₚ' * eₚ) = fₚ' * (fₚ * eₚ') * eₚ := by group
          _ = fₚ' * (eₚ' * fₚ) * eₚ := by rw [hfₚ_eₚ']
          _ = (fₚ' * eₚ') * (fₚ * eₚ) := by group
  have hfₚ_pow : ∃ k : ℕ, orderOf fₚ = p ^ k := by
    rcases (IsPGroup.iff_orderOf.mp (qCoreOf_isPGroup Hf p)) ⟨fₚ, hfₚHf⟩ with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [Subgroup.orderOf_coe] using hk
  have heₚ_pow : ∃ k : ℕ, orderOf eₚ = p ^ k := by
    rcases (IsPGroup.iff_orderOf.mp (qCoreOf_isPGroup He p)) ⟨eₚ, heₚHe⟩ with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [Subgroup.orderOf_coe] using hk
  have hx_pow : ∃ k : ℕ, orderOf (fₚ * eₚ) = p ^ k := by
    rcases hfₚ_pow with ⟨k1, hk1⟩
    rcases heₚ_pow with ⟨k2, hk2⟩
    have hdvd : orderOf (fₚ * eₚ) ∣ p ^ k1 * p ^ k2 := by
      have h := hfₚ_eₚ.orderOf_mul_dvd_lcm
      have hlcm : (orderOf fₚ).lcm (orderOf eₚ) ∣ p ^ k1 * p ^ k2 := by
        rw [hk1, hk2]
        exact Nat.lcm_dvd (dvd_mul_right (p ^ k1) (p ^ k2))
          (dvd_mul_left (p ^ k2) (p ^ k1))
      exact h.trans hlcm
    have hdvd' : orderOf (fₚ * eₚ) ∣ p ^ (k1 + k2) := by
      simpa [pow_add] using hdvd
    rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).mp hdvd' with ⟨k, _hk, hk⟩
    exact ⟨k, hk⟩
  have hfₚ'_cop : Nat.Coprime p (orderOf fₚ') :=
    orderOf_coprime_of_mem_pPrimeCore_map_local (H := Hf) (p := p) hfₚ'Hf
  have heₚ'_cop : Nat.Coprime p (orderOf eₚ') :=
    orderOf_coprime_of_mem_pPrimeCore_map_local (H := He) (p := p) heₚ'He
  have hy_p' : Nat.Coprime p (orderOf (fₚ' * eₚ')) := by
    have hdvd : orderOf (fₚ' * eₚ') ∣ orderOf fₚ' * orderOf eₚ' := by
      have h := hfₚ'_eₚ'.orderOf_mul_dvd_lcm
      exact h.trans (Nat.lcm_dvd (dvd_mul_right (orderOf fₚ') (orderOf eₚ'))
        (dvd_mul_left (orderOf eₚ') (orderOf fₚ')))
    exact (hfₚ'_cop.mul_right heₚ'_cop).of_dvd_right hdvd
  have hxy_cop : (orderOf (fₚ * eₚ)).Coprime (orderOf (fₚ' * eₚ')) := by
    rcases hx_pow with ⟨k, hk⟩
    rw [hk]
    exact hy_p'.pow_left k
  have hqord : orderOf s = orderOf (fₚ * eₚ) * orderOf (fₚ' * eₚ') := by
    have h := hxy_comm.orderOf_mul_eq_mul_orderOf_of_coprime hxy_cop
    rwa [← hsxeq]
  have hx_dvd : orderOf (fₚ * eₚ) ∣ orderOf s := by
    rw [hqord]
    exact dvd_mul_right (orderOf (fₚ * eₚ)) (orderOf (fₚ' * eₚ'))
  have hcop_x : Nat.Coprime p (orderOf (fₚ * eₚ)) := hscop.of_dvd_right hx_dvd
  have hx_one : fₚ * eₚ = 1 := by
    rcases hx_pow with ⟨k, hk⟩
    have hk0 : k = 0 := by
      by_contra hk0
      have hdvd : p ∣ p ^ k := by
        simpa using (pow_dvd_pow p (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hk0)))
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1
        (by rwa [hk] at hcop_x) hdvd
    have hord1 : orderOf (fₚ * eₚ) = 1 := by rw [hk, hk0]; simp
    exact orderOf_eq_one_iff.mp hord1
  have hfₚ_c_P : fₚ ∈ Subgroup.centralizer (P : Set G) := by
    have hfₚ_inv : fₚ = eₚ⁻¹ := eq_inv_of_mul_eq_one_left hx_one
    have hfₚFE : fₚ ∈ F ⊓ E := by
      refine Subgroup.mem_inf.mpr ⟨hHf_le hfₚHf' |>.1, ?_⟩
      rw [hfₚ_inv]
      exact E.inv_mem (hHe_le heₚHe')
    have hfₚZ : fₚ ∈ (Subgroup.center (↥E)).map E.subtype := by
      rw [← inf_fitting_componentLayer_eq_center_componentLayer_local A]
      exact hfₚFE
    exact hZEcP hfₚZ
  have heₚ_c_P : eₚ ∈ Subgroup.centralizer (P : Set G) := by
    have h := (Subgroup.centralizer (P : Set G)).inv_mem hfₚ_c_P
    simpa [eq_inv_of_mul_eq_one_right hx_one] using h
  have hfₚ'_c_P : fₚ' ∈ Subgroup.centralizer (P : Set G) :=
    pPrime_element_centralizes_pSubgroup_of_nilpotent_local (H := F) (P := P) (p := p)
      hFnil hPleF (qCoreOf_isPGroup S p) (hHf_le hfₚ'Hf' |>.1) hfₚ'_cop
  have heₚ'_c_P : eₚ' ∈ Subgroup.centralizer (P : Set G) :=
    hEcP (hHe_le heₚ'He')
  have ht_fₚ : t * fₚ = fₚ * t :=
    (Subgroup.mem_centralizer_iff.mp hfₚ_c_P) t ht
  have ht_eₚ : t * eₚ = eₚ * t :=
    (Subgroup.mem_centralizer_iff.mp heₚ_c_P) t ht
  have ht_fₚ' : t * fₚ' = fₚ' * t :=
    (Subgroup.mem_centralizer_iff.mp hfₚ'_c_P) t ht
  have ht_eₚ' : t * eₚ' = eₚ' * t :=
    (Subgroup.mem_centralizer_iff.mp heₚ'_c_P) t ht
  calc
    t * s = t * (fₚ * eₚ * (fₚ' * eₚ')) := by rw [hsxeq]
    _ = (fₚ * eₚ * (fₚ' * eₚ')) * t := by
      calc
        t * (fₚ * eₚ * (fₚ' * eₚ')) = (t * fₚ) * eₚ * (fₚ' * eₚ') := by group
        _ = (fₚ * t) * eₚ * (fₚ' * eₚ') := by rw [ht_fₚ]
        _ = fₚ * (t * eₚ) * (fₚ' * eₚ') := by group
        _ = fₚ * (eₚ * t) * (fₚ' * eₚ') := by rw [ht_eₚ]
        _ = (fₚ * eₚ) * t * (fₚ' * eₚ') := by group
        _ = (fₚ * eₚ) * (t * fₚ') * eₚ' := by group
        _ = (fₚ * eₚ) * (fₚ' * t) * eₚ' := by rw [ht_fₚ']
        _ = (fₚ * eₚ) * fₚ' * (t * eₚ') := by group
        _ = (fₚ * eₚ) * fₚ' * (eₚ' * t) := by rw [ht_eₚ']
        _ = (fₚ * eₚ * (fₚ' * eₚ')) * t := by group
    _ = s * t := by rw [hsxeq]

/-! ## The cross-commutator and the `(i)`-conjunct -/

/-- Gagen 12.4, scan steps (iv)+(v): for `p ∈ π(F(A))`, `O^p(S)`
centralizes `O_p(B)`.  Step (iv) gives `O_p(B) ∩ C_G(O_p(S)) ≤ O_p(B) ∩ A`;
the Thompson lemma 1.1 then upgrades the already-known
`[O_p(B) ∩ A, O^p(S)] = 1` to `[O_p(B), O^p(S)] = 1`. -/
private theorem pResidualOf_S_centralizes_qCoreOf_B_local
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B)
    (p : ℕ) (hp : p.Prime) (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    Centralizes (pResidualOf S p) (qCoreOf B p) := by
  classical
  let P : Subgroup G := qCoreOf S p
  let K : Subgroup G := pResidualOf S p
  let R : Subgroup G := qCoreOf B p
  let : Fact p.Prime := ⟨hp⟩
  have hKres : pResidualOf K p = K := by
    simpa [K] using fstar_pResidualOf_idempotent S p hp
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := by
    exact (pResidualOf_le S p).trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in S p))
  have hcop : ∀ Q : Subgroup (↥K), Nat.Coprime p (Nat.card (↥Q)) →
      Centralizes (Q.map K.subtype) P := by
    intro Q hQ
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨q, hq, rfl⟩
    have hxS : (q : G) ∈ S := (pResidualOf_le S p) q.2
    have hxord : Nat.Coprime p (orderOf (q : G)) := by
      have hdvd : orderOf (q : G) ∣ Nat.card (↥Q) := by
        simpa using (Subgroup.orderOf_dvd_natCard Q hq)
      exact hQ.of_dvd_right hdvd
    exact pPrime_element_centralizes_qCoreOf_S_local A S hSF hSsub hCS p hp
      (q : G) hxS hxord
  have hPK : ⁅P, K⁆ = ⊥ := by
    have hcent : Centralizes K P :=
      centralizes_of_pResidualOf_eq_self_of_coprime_subgroups K P p hp hKres hKP hcop
    rw [← Subgroup.commutator_comm K P]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := P)).mpr hcent
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (qCoreOf_le S p).trans (hSB.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in B p)))
  have hKR : K ≤ Subgroup.normalizer (R : Set G) :=
    (pResidualOf_le S p).trans (hSB.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in B p)))
  have hCBK : ⁅R ⊓ Subgroup.centralizer (P : Set G), K⁆ = ⊥ := by
    apply bot_unique
    have hiv : R ⊓ Subgroup.centralizer (P : Set G) ≤ R ⊓ A :=
      inf_le_inf (le_rfl : R ≤ R) (bender1970_1_7_centralizer_qCoreOf_S_le_A
        hsimple A hA S hSF hSsub hCS p hp hpF)
    exact (Subgroup.commutator_mono hiv le_rfl).trans (le_of_eq
      (commutator_qCoreOf_B_inf_A_pResidualOf_S_local A S B hSF hSsub hCS hSB p hp))
  have hthom : Centralizes K R :=
    bender1970_1_1_thompson p hp P K R (qCoreOf_isPGroup S p) (qCoreOf_isPGroup B p)
      hKres hPR hKR hPK hCBK
  simpa [K, R] using hthom

/-- Gagen 12.4, scan step (vi): `F(A)_{p'} ∩ C_G(F(S)_{p'}) ≤ F(S)_{p'}`.
An element of the `p'`-part of `F(A)` centralizes the `p`-part and
`p'`-part of `F(S)` (the former by coprime commutation inside the nilpotent
`F(A)`, the latter by hypothesis), centralizes `E(A)`, and therefore
centralizes `S = (F(A) ∩ S)E(A)`; the self-centralizing hypothesis puts it
in `S`, and `F(S) = F(A) ∩ S` puts it in `F(S)_{p'}`. -/
private theorem pPrimeCore_fitting_centralizer_le_fitting_pPrimeCore_local
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (p : ℕ) (hp : p.Prime) :
    (pPrimeCore p (↥(fittingSubgroupOf A))).map (fittingSubgroupOf A).subtype ⊓
      Subgroup.centralizer
        (((pPrimeCore p (↥(fittingSubgroupOf A ⊓ S))).map
            (fittingSubgroupOf A ⊓ S).subtype :
            Subgroup G) : Set G) ≤
      (pPrimeCore p (↥(fittingSubgroupOf A ⊓ S))).map (fittingSubgroupOf A ⊓ S).subtype := by
  classical
  let F : Subgroup G := fittingSubgroupOf A
  let PA : Subgroup G := (pPrimeCore p (↥F)).map F.subtype
  let PS : Subgroup G := (pPrimeCore p (↥(F ⊓ S))).map (F ⊓ S).subtype
  let E : Subgroup G := componentLayerOf A
  let : Fact p.Prime := ⟨hp⟩
  have hFnil : Group.IsNilpotent F := fittingSubgroupOf_isNilpotent A
  have hFS_eq : fittingSubgroupOf S = F ⊓ S :=
    fittingSubgroupOf_eq_inf_of_subnormal_local A S hSF hSsub
  have hFinterSnil : Group.IsNilpotent (↥(F ⊓ S)) := by
    let : Group.IsNilpotent (↥F) := hFnil
    have hInst : Group.IsNilpotent (↥((F ⊓ S).subgroupOf F)) := by
      infer_instance
    exact Group.nilpotent_of_mulEquiv
      (G := ↥((F ⊓ S).subgroupOf F)) (G' := ↥(F ⊓ S))
      (Subgroup.subgroupOfEquivOfLe (H := F ⊓ S) (K := F)
        (show F ⊓ S ≤ F from inf_le_left))
  have hFinterSnorm : IsNormalIn (F ⊓ S) S := by
    refine ⟨inf_le_right, ?_⟩
    intro s hs z hz
    have hsA : s ∈ A := hSF.trans (fstar_generalizedFittingSubgroupOf_le A) hs
    have hz'F : s * z * s⁻¹ ∈ F :=
      (fittingSubgroupOf_isNormalIn A).2 s hsA z hz.1
    have hz'S : s * z * s⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem hs hz.2) (S.inv_mem hs)
    exact Subgroup.mem_inf.mpr ⟨hz'F, hz'S⟩
  have hQSs : ∀ z : G, z ∈ qCoreOf (F ⊓ S) p → z ∈ qCoreOf S p := by
    intro z hz
    have hzS : z ∈ S := (qCoreOf_le (F ⊓ S) p hz).2
    have hnorm : IsNormalIn (qCoreOf (F ⊓ S) p) S := by
      simpa [qCoreOf] using
        (fstar_characteristic_subgroupOf_map_normal_in (F := F ⊓ S)
          (K := pCore p (↥(F ⊓ S))) (pCore_characteristic (p := p)) hFinterSnorm)
    have hQSle : qCoreOf (F ⊓ S) p ≤ S := fun z hz => (qCoreOf_le (F ⊓ S) p hz).2
    exact le_qCoreOf_of_normal_isPGroup S (qCoreOf (F ⊓ S) p) p hQSle (by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQSle]
      exact le_normalizer_of_isNormalIn hnorm) (qCoreOf_isPGroup (F ⊓ S) p) hz
  have hPleFS : qCoreOf S p ≤ fittingSubgroupOf S :=
    le_fittingSubgroupOf_of_isNormalIn_nilpotent (L := S) (N := qCoreOf S p)
      (qCoreOf_le S p) (qCoreOf_normal_in S p) (qCoreOf_isPGroup S p).isNilpotent
  have hPleF : qCoreOf S p ≤ F :=
    (hPleFS.trans (le_of_eq hFS_eq)).trans inf_le_left
  have hFcE : F ≤ Subgroup.centralizer (E : Set G) := by
    have hcomm : ⁅F, E⁆ = ⊥ := Subgroup.commutator_comm E F ▸ layer_centralizes_fitting A
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := F) (H₂ := E)).1 hcomm
  have hEcF : E ≤ Subgroup.centralizer (F : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := E) (H₂ := F)).1
      (layer_centralizes_fitting A)
  have hEF' : E ≤ Subgroup.centralizer ((F ⊓ S : Subgroup G) : Set G) :=
    hEcF.trans (Subgroup.centralizer_le
      (show ((F ⊓ S : Subgroup G) : Set G) ⊆ (F : Set G) from inf_le_left))
  intro x hx
  rcases Subgroup.mem_inf.mp hx with ⟨hxPA, hxcent⟩
  have hxF : x ∈ F := Subgroup.map_subtype_le (H := F) (pPrimeCore p (↥F)) hxPA
  have hxcop : Nat.Coprime p (orderOf x) :=
    orderOf_coprime_of_mem_pPrimeCore_map_local (H := F) (p := p) hxPA
  have hxcentP : x ∈ Subgroup.centralizer ((qCoreOf S p : Subgroup G) : Set G) :=
    pPrime_element_centralizes_pSubgroup_of_nilpotent_local (H := F) (P := qCoreOf S p)
      (p := p) hFnil hPleF (qCoreOf_isPGroup S p) hxF hxcop
  have hxcentE : x ∈ Subgroup.centralizer (E : Set G) := hFcE hxF
  have hxcentS : x ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyFSE : y ∈ (F ⊓ S) ⊔ E := by
      rw [← S_eq_sup_local A S hSF hSsub hCS]
      exact hy
    rcases mem_sup_decompose_of_centralizes (F := F ⊓ S) (E := E) hyFSE hEF' with
      ⟨z, hz, e, he, hzeq⟩
    have hze_comm : Commute z e :=
      (Subgroup.mem_centralizer_iff.mp (hEF' he)) z hz
    rcases mem_pCore_pPrimeCore_decompose_local (H := F ⊓ S) (p := p) hFinterSnil hz with
      ⟨zₚ, zₚ', hzeq', hzₚQ, hzₚ'PS, hzₚzₚ'_comm⟩
    have hxzₚ : zₚ * x = x * zₚ :=
      (Subgroup.mem_centralizer_iff.mp hxcentP) zₚ (hQSs zₚ hzₚQ)
    have hzₚ'FS : zₚ' ∈ PS := hzₚ'PS
    have hxzₚ' : zₚ' * x = x * zₚ' :=
      (Subgroup.mem_centralizer_iff.mp hxcent) zₚ' hzₚ'FS
    have hxz : z * x = x * z := by
      calc
        z * x = (zₚ * zₚ') * x := by rw [hzeq']
        _ = zₚ * (zₚ' * x) := by group
        _ = zₚ * (x * zₚ') := by rw [hxzₚ']
        _ = (zₚ * x) * zₚ' := by group
        _ = (x * zₚ) * zₚ' := by rw [hxzₚ]
        _ = x * (zₚ * zₚ') := by group
        _ = x * z := by rw [hzeq']
    have hxe : e * x = x * e :=
      (Subgroup.mem_centralizer_iff.mp hxcentE) e he
    calc
      y * x = (z * e) * x := by rw [hzeq]
      _ = z * (e * x) := by group
      _ = z * (x * e) := by rw [hxe]
      _ = (z * x) * e := by group
      _ = (x * z) * e := by rw [hxz]
      _ = x * (z * e) := by group
      _ = x * y := by rw [hzeq]
  have hxSF : x ∈ generalizedFittingSubgroupOf A ⊓
      Subgroup.centralizer (S : Set G) :=
    Subgroup.mem_inf.mpr ⟨(le_sup_left : F ≤ generalizedFittingSubgroupOf A) hxF, hxcentS⟩
  have hxS' : x ∈ S := hCS hxSF
  have hxFS : x ∈ F ⊓ S := Subgroup.mem_inf.mpr ⟨hxF, hxS'⟩
  exact element_mem_pPrimeCore_of_order_coprime_of_nilpotent_local
    (H := F ⊓ S) (p := p) hFinterSnil hxFS hxcop

/-- The paper's step (iii): `[O_p(B) ∩ A, O_q(A)] = 1` for `p ≠ q`, via the
Thompson lemma applied to the action of `(O_p(B) ∩ A)·O_q(S)` on `O_q(A)`. -/
private theorem commutator_qCoreOf_B_inf_A_qCoreOf_A_of_ne_local
    {G : Type u} [Group G] [Finite G]
    (A S B : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (hSB : S ≤ B)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ⁅qCoreOf B p ⊓ A, qCoreOf A q⁆ = ⊥ := by
  classical
  let X : Subgroup G := qCoreOf B p ⊓ A
  let P : Subgroup G := qCoreOf S q
  let BO : Subgroup G := qCoreOf A q
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hXp : IsPGroup p X := IsPGroup.to_inf_left (qCoreOf_isPGroup B p)
  have hXA : X ≤ A := inf_le_right
  have hPA : P ≤ A :=
    (qCoreOf_le S q).trans (hSF.trans (fstar_generalizedFittingSubgroupOf_le A))
  have hXres : pResidualOf X q = X := by
    apply le_antisymm
    · exact pResidualOf_le X q
    · intro x hx
      have hxord : Nat.Coprime q (orderOf x) := by
        have hordG : orderOf x = orderOf (⟨x, hx⟩ : ↥X) :=
          (Subgroup.orderOf_coe ⟨x, hx⟩)
        rcases (IsPGroup.iff_orderOf.mp hXp) ⟨x, hx⟩ with ⟨k, hk⟩
        have hcop : Nat.Coprime q (p ^ k) :=
          ((Nat.coprime_primes hq hp).2 hne.symm).pow_right k
        rw [hordG, hk]
        exact hcop
      exact fstar_mem_pResidualOf_of_order_coprime X q hq hx hxord
  have hPB : P ≤ Subgroup.normalizer (BO : Set G) :=
    hPA.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in A q))
  have hXB : X ≤ Subgroup.normalizer (BO : Set G) :=
    hXA.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in A q))
  have hPX : ⁅P, X⁆ = ⊥ := by
    apply bot_unique
    rw [← Subgroup.commutator_comm X P]
    have hPleO : P ≤ pResidualOf S p :=
      qCoreOf_le_pResidualOf_of_ne_local_S S p q hp hq hne.symm
    have hXcO : ⁅X, pResidualOf S p⁆ = ⊥ :=
      commutator_qCoreOf_B_inf_A_pResidualOf_S_local A S B hSF hSsub hCS hSB p hp
    exact (Subgroup.commutator_mono le_rfl hPleO).trans (le_of_eq hXcO)
  have hCBK : ⁅BO ⊓ Subgroup.centralizer (P : Set G), X⁆ = ⊥ := by
    apply bot_unique
    have hfixed : BO ⊓ Subgroup.centralizer (P : Set G) ≤ P :=
      qCoreOf_centralizer_le_qCoreOf_local A S hSF hSsub hCS q hq
    exact (Subgroup.commutator_mono hfixed le_rfl).trans (le_of_eq hPX)
  have hthom : Centralizes X BO :=
    bender1970_1_1_thompson q hq P X BO (qCoreOf_isPGroup S q) (qCoreOf_isPGroup A q)
      hXres hPB hXB hPX hCBK
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := X) (H₂ := BO)).2 hthom

set_option maxHeartbeats 800000 in
/-- Statement 1.7(i): `O_q(B) ∩ A = 1` for `q ∉ π(F(A))`. -/
private theorem qCoreOf_B_inf_A_eq_bot_of_not_mem_primes_local
    {G : Type u} [Group G] [Finite G]
    (A S B : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (hSB : S ≤ B)
    (p : ℕ) (hp : p.Prime) (hpnF : p ∉ primesOfOrder (fittingSubgroupOf A)) :
    qCoreOf B p ⊓ A = ⊥ := by
  classical
  let X : Subgroup G := qCoreOf B p ⊓ A
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let : Fact p.Prime := ⟨hp⟩
  have hXp : IsPGroup p X := IsPGroup.to_inf_left (qCoreOf_isPGroup B p)
  have hXA : X ≤ A := inf_le_right
  have hES : E ≤ S := fstar_componentLayer_le_selfCentralizingSubnormal A S hSF hSsub hCS
  have hXcF : X ≤ Subgroup.centralizer (F : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyF' : y ∈ fittingSubgroupOf A := hy
    rw [fstar_fittingSubgroupOf_eq_iSup_qCoreOf A] at hyF'
    rw [Subgroup.iSup_eq_closure] at hyF'
    have hgen : ∀ z : G,
        z ∈ ⋃ q : (Nat.card (↥A)).primeFactors.attach, (qCoreOf A q.1.1 : Set G) →
          z * x = x * z := by
      intro z hz
      rcases (Set.mem_iUnion).1 hz with ⟨q, hzq⟩
      by_cases hqp : q.1.1 = p
      · have hObot : qCoreOf A p = ⊥ :=
          qCoreOf_eq_bot_of_not_mem_primesOfOrder_local A p hp hpnF
        have hzq' : z ∈ qCoreOf A p := by simpa [hqp] using hzq
        have hz1 : z = 1 := Subgroup.mem_bot.mp (by simpa [hObot] using hzq')
        simp [hz1]
      · have hcomm : ⁅X, qCoreOf A q.1.1⁆ = ⊥ :=
          commutator_qCoreOf_B_inf_A_qCoreOf_A_of_ne_local A S B hSF hSsub hCS hSB
            p q.1.1 hp (Nat.prime_of_mem_primeFactors q.1.2) (by
              intro h
              exact hqp h.symm)
        have hXc : X ≤ Subgroup.centralizer ((qCoreOf A q.1.1 : Subgroup G) : Set G) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer
            (H₁ := X) (H₂ := qCoreOf A q.1.1)).1 hcomm
        exact (Subgroup.mem_centralizer_iff.mp (hXc hx)) z hzq
    refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ hyF'
    · intro z hz
      calc
        z⁻¹ * x = z⁻¹ * (x * z * z⁻¹) := by group
        _ = z⁻¹ * (z * x * z⁻¹) := by rw [hgen z hz]
        _ = x * z⁻¹ := by group
    · simp
    · intro a b _ _ hab hba
      calc
        (a * b) * x = a * (b * x) := by group
        _ = a * (x * b) := by rw [hba]
        _ = (a * x) * b := by group
        _ = (x * a) * b := by rw [hab]
        _ = x * (a * b) := by group
  have hXcE : X ≤ Subgroup.centralizer (E : Set G) := by
    have hEres : E ≤ pResidualOf S p := componentLayer_le_pResidualOf_local A S hES p hp
    have hXcRes : X ≤ Subgroup.centralizer ((pResidualOf S p : Subgroup G) : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := X) (H₂ := pResidualOf S p)).1
        (commutator_qCoreOf_B_inf_A_pResidualOf_S_local A S B hSF hSsub hCS hSB p hp)
    exact hXcRes.trans (Subgroup.centralizer_le
      (show (E : Set G) ⊆ (pResidualOf S p : Set G) from hEres))
  have hXcFstar : X ≤ Subgroup.centralizer ((generalizedFittingSubgroupOf A : Set G)) := by
    intro x hx
    simpa [generalizedFittingSubgroupOf, F, E] using
      (fstar_centralizer_of_centralizes_join (F := F) (E := E) (hXcF hx) (hXcE hx))
  have hXleFstar : X ≤ generalizedFittingSubgroupOf A := by
    intro x hx
    exact centralizer_intersection_fstar_le_fstar_local A ⟨hXcFstar hx, hXA hx⟩
  have hXleZ : X ≤ (Subgroup.center (↥(generalizedFittingSubgroupOf A))).map
      (generalizedFittingSubgroupOf A).subtype := by
    intro x hx
    have hxZ' : (⟨x, hXleFstar hx⟩ : ↥(generalizedFittingSubgroupOf A)) ∈
        Subgroup.center (↥(generalizedFittingSubgroupOf A)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hXcFstar hx)) y.1 y.2
    exact Subgroup.mem_map.mpr ⟨⟨x, hXleFstar hx⟩, hxZ', rfl⟩
  have hXleF : X ≤ F :=
    hXleZ.trans (center_generalizedFitting_le_fittingSubgroupOf_local A)
  have hXbot : X = ⊥ := by
    have hObot : qCoreOf F p = ⊥ :=
      qCoreOf_fitting_eq_bot_of_not_mem_primesOfOrder_local A p hp hpnF
    have hXleP : X ≤ qCoreOf F p :=
      pSubgroup_le_qCoreOf_of_nilpotent_local (H := F) (p := p)
        (fittingSubgroupOf_isNilpotent A) hXleF hXp
    apply le_bot_iff.mp
    exact hXleP.trans (le_of_eq hObot)
  simpa [X] using hXbot

/-- The centralizer of a nontrivial subgroup normal in the maximal
subgroup `A` is contained in `A`: otherwise `A` and the centralizer
generate `G`, making the subgroup normal in the simple group `G`. -/
private theorem centralizer_normal_le_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    {N : Subgroup G} (hNA : N ≤ A) (hN : IsNormalIn N A) (hNne : N ≠ ⊥) :
    Subgroup.centralizer (N : Set G) ≤ A := by
  classical
  let C : Subgroup G := Subgroup.centralizer (N : Set G)
  by_contra hnot
  have hlt : A < A ⊔ C := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hEq
    apply hnot
    intro x hx
    exact hEq ▸ (le_sup_right : C ≤ A ⊔ C) hx
  have htop : A ⊔ C = ⊤ := hA.2 (A ⊔ C) hlt
  have hA_norm : A ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_of_isNormalIn hN
  have hC_norm : C ≤ Subgroup.normalizer (N : Set G) := by
    intro c hc
    exact Subgroup.centralizer_le_normalizer (N : Set G) hc
  have hsup_norm : A ⊔ C ≤ Subgroup.normalizer (N : Set G) :=
    sup_le hA_norm hC_norm
  have hNnorm : N.Normal := by
    have htopN : Subgroup.normalizer (N : Set G) = ⊤ :=
      le_antisymm le_top (by simpa [htop] using hsup_norm)
    exact (Subgroup.normalizer_eq_top_iff).mp htopN
  rcases (haveI := hNnorm; hsimple.eq_bot_or_eq_top_of_normal N) with hbot | htopN
  · exact hNne hbot
  · have hAtop : A = ⊤ := by
      apply le_antisymm le_top
      intro x hx
      exact hNA (by simpa [htopN] using hx)
    exact hA.1 hAtop

/-- The center of `O_{p'}(F(A))` is contained in every subnormal
self-centralizing `S ≤ F*(A)`: it is central in `F(A)`, hence in `S` by the
usual Fitting-center transfer. -/
private theorem center_pPrimeCore_fitting_le_selfCentralizingSubnormal_local
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (p : ℕ) (hp : p.Prime) :
    (Subgroup.center (↥(pPrimeCoreOfFitting A p))).map
        (pPrimeCoreOfFitting A p).subtype ≤ S := by
  classical
  let F : Subgroup G := fittingSubgroupOf A
  let PFA : Subgroup G := pPrimeCoreOfFitting A p
  let Z : Subgroup G := (Subgroup.center (↥PFA)).map PFA.subtype
  let : Fact p.Prime := ⟨hp⟩
  have hFnil : Group.IsNilpotent F := fittingSubgroupOf_isNilpotent A
  have hPFA_le_F : PFA ≤ F := by
    dsimp [PFA, pPrimeCoreOfFitting, F]
    exact Subgroup.map_subtype_le (H := fittingSubgroupOf A) (pPrimeCore p (↥(fittingSubgroupOf A)))
  have hPFAcC : PFA ≤ Subgroup.centralizer ((qCoreOf F p : Subgroup G) : Set G) := by
    have hmap :
        (pPrimeCore p (↥F)).map F.subtype ≤
          Subgroup.centralizer ((qCoreOf F p : Subgroup G) : Set G) :=
      pPrimeCore_map_le_centralizer_pCore_map (p := p) F
    simpa [PFA, pPrimeCoreOfFitting, F] using hmap
  have hZ_le_centerF : Z ≤ (Subgroup.center (↥F)).map F.subtype := by
    intro z hz
    rcases (Subgroup.mem_map).1 hz with ⟨zP, hzP, rfl⟩
    have hzF : (zP : G) ∈ F := hPFA_le_F zP.2
    have hzcentP : (zP : ↥PFA) ∈ Subgroup.center (↥PFA) := hzP
    have hzmem : (⟨(zP : G), hzF⟩ : ↥F) ∈ Subgroup.center (↥F) := by
      rw [Subgroup.mem_center_iff]
      intro f
      apply Subtype.ext
      have hfF : (f : G) ∈ F := f.2
      rcases mem_pCore_pPrimeCore_decompose_local (H := F) (p := p) hFnil hfF with
        ⟨fₚ, fₚ', hfeq, hfₚQ, hfₚ'P, hfₚfₚ'_comm⟩
      have hzfₚ : fₚ * (zP : G) = (zP : G) * fₚ :=
        (Subgroup.mem_centralizer_iff.mp (hPFAcC zP.2)) fₚ hfₚQ
      have hzfₚ' : fₚ' * (zP : G) = (zP : G) * fₚ' := by
        have hz_comm := (Subgroup.mem_center_iff.mp hzcentP) ⟨fₚ', hfₚ'P⟩
        exact congrArg Subtype.val hz_comm
      calc
        (f : G) * (zP : G) = (fₚ * fₚ') * (zP : G) := by rw [hfeq]
        _ = fₚ * (fₚ' * (zP : G)) := by group
        _ = fₚ * ((zP : G) * fₚ') := by rw [hzfₚ']
        _ = (fₚ * (zP : G)) * fₚ' := by group
        _ = ((zP : G) * fₚ) * fₚ' := by rw [hzfₚ]
        _ = (zP : G) * (fₚ * fₚ') := by group
        _ = (zP : G) * (f : G) := by rw [hfeq]
    exact Subgroup.mem_map.mpr ⟨⟨(zP : G), hzF⟩, hzmem, rfl⟩
  exact hZ_le_centerF.trans (fstar_centerFitting_le_selfCentralizingSubnormal A S
    hSF hSsub hCS)

/-- If `O^p(F*(A)) ≠ 1`, then `O_p(B) ≤ A`: either the `p'`-part of
`F(A)` is nontrivial, in which case its center is a nontrivial normal
subgroup of `A` centralized by `O_p(B)`, or `F(A)` is a `p`-group and the
layer `E(A)` plays that role. -/
private theorem qCoreOf_B_le_A_of_pResidual_ne_bot_local
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B)
    (p : ℕ) (hp : p.Prime) (hpF : p ∈ primesOfOrder (fittingSubgroupOf A))
    (hRes : pResidualOf (generalizedFittingSubgroupOf A) p ≠ ⊥) :
    qCoreOf B p ≤ A := by
  classical
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let PFA : Subgroup G := pPrimeCoreOfFitting A p
  let K : Subgroup G := pResidualOf S p
  let J : Subgroup G := ⨆ q : {q : ℕ // q.Prime ∧ q ≠ p}, qCoreOf A q.1
  let : Fact p.Prime := ⟨hp⟩
  have hcentKR : Centralizes K (qCoreOf B p) :=
    pResidualOf_S_centralizes_qCoreOf_B_local hsimple A hA S hSF hSsub hCS hSB p hp hpF
  have hRcK : qCoreOf B p ≤ Subgroup.centralizer ((K : Subgroup G) : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact ((Subgroup.mem_centralizer_iff.mp (hcentKR hk)) r hr).symm
  have hEres : E ≤ K :=
    componentLayer_le_pResidualOf_local A S
      (fstar_componentLayer_le_selfCentralizingSubnormal A S hSF hSsub hCS) p hp
  by_cases hPFAbot : PFA = ⊥
  · have hJbot : J = ⊥ := by
      have hJlePFA : J ≤ PFA := by
        have hEq : pResidualOf (fittingSubgroupOf A) p = J := by
          simpa [J] using pResidualOf_fitting_eq_iSup_qCoreOf_of_ne_local A p hp
        rw [← hEq]
        exact pResidualOf_fitting_le_pPrimeCore_local A p hp
      exact le_bot_iff.mp (hJlePFA.trans (le_of_eq hPFAbot))
    have hResS_ne : K ≠ ⊥ := by
      intro hKbot
      have hRes_le : pResidualOf (generalizedFittingSubgroupOf A) p ≤ ⊥ := by
        calc
          pResidualOf (generalizedFittingSubgroupOf A) p ≤ K ⊔ J :=
            pResidualOf_generalizedFitting_le_generation_local A S hSF hSsub hCS p hp
          _ = ⊥ := by rw [hKbot, hJbot]; simp
      exact hRes (le_bot_iff.mp hRes_le)
    have hRSbot : pResidualOf (F ⊓ S) p = ⊥ := by
      have hRSle : pResidualOf (F ⊓ S) p ≤ PFA :=
        pResidualOf_le_pPrimeCore_of_le_fitting_local A (F ⊓ S) p hp inf_le_left
      exact le_bot_iff.mp (hRSle.trans (le_of_eq hPFAbot))
    have hEne : E ≠ ⊥ := by
      intro hEbot
      have hREbot : pResidualOf E p = ⊥ := by
        apply le_bot_iff.mp
        calc
          pResidualOf E p ≤ E := pResidualOf_le E p
          _ = ⊥ := hEbot
      have hKle : K ≤ ⊥ := by
        calc
          K ≤ pResidualOf (F ⊓ S) p ⊔ pResidualOf E p :=
            pResidualOf_S_le_sup_local A S hSF hSsub hCS p hp
          _ = ⊥ := by rw [hRSbot, hREbot]; simp
      exact hResS_ne (le_bot_iff.mp hKle)
    have hEleA : E ≤ A :=
      (le_sup_right : E ≤ generalizedFittingSubgroupOf A).trans
        (fstar_generalizedFittingSubgroupOf_le A)
    have hEnormal : IsNormalIn E A := fstar_componentLayerOf_isNormalIn A
    have hRcE : qCoreOf B p ≤ Subgroup.centralizer (E : Set G) :=
      hRcK.trans (Subgroup.centralizer_le (show (E : Set G) ⊆ (K : Set G) from hEres))
    exact hRcE.trans (centralizer_normal_le_A hsimple A hA hEleA hEnormal hEne)
  · let Z : Subgroup G := (Subgroup.center (↥PFA)).map PFA.subtype
    have hPFA_le_F : PFA ≤ F := by
      dsimp [PFA, pPrimeCoreOfFitting, F]
      exact Subgroup.map_subtype_le (H := fittingSubgroupOf A) (pPrimeCore p (↥(fittingSubgroupOf A)))
    have hZlePFA : Z ≤ PFA := Subgroup.map_subtype_le (H := PFA) (Subgroup.center (↥PFA))
    have hZleA : Z ≤ A :=
      hZlePFA.trans (hPFA_le_F.trans (le_sup_left.trans (fstar_generalizedFittingSubgroupOf_le A)))
    have hPFAnil : Group.IsNilpotent (↥PFA) := by
      have e : pPrimeCore p (↥F) ≃* ↥PFA :=
        Subgroup.equivMapOfInjective (pPrimeCore p (↥F)) F.subtype F.subtype_injective
      let : Group.IsNilpotent (↥F) := fittingSubgroupOf_isNilpotent A
      have : Group.IsNilpotent (pPrimeCore p (↥F)) := by
        infer_instance
      exact Group.nilpotent_of_mulEquiv e
    have hZne : Z ≠ ⊥ := by
      have : Nontrivial (↥PFA) :=
        (Subgroup.nontrivial_iff_ne_bot (H := PFA)).mpr hPFAbot
      have hCne : (Subgroup.center (↥PFA)) ≠ ⊥ :=
        Group.IsNilpotent.center_ne_bot (G := ↥PFA)
      intro hZbot
      have hCbot : (Subgroup.center (↥PFA)) = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center (↥PFA))
          (f := PFA.subtype) PFA.subtype_injective).1 hZbot
      exact hCne hCbot
    have hPFAnormA : IsNormalIn PFA A := by
      simpa [PFA, pPrimeCoreOfFitting, F] using
        (fstar_characteristic_subgroupOf_map_normal_in (F := F)
          (K := pPrimeCore p (↥F)) (pPrimeCore_characteristic (p := p))
          (fittingSubgroupOf_isNormalIn A))
    have hZnormal : IsNormalIn Z A := by
      simpa [Z] using
        (fstar_characteristic_subgroupOf_map_normal_in (F := PFA)
          (K := Subgroup.center (↥PFA)) (by infer_instance) hPFAnormA)
    have hZleK : Z ≤ K := by
      intro z hz
      have hzS : z ∈ S :=
        center_pPrimeCore_fitting_le_selfCentralizingSubnormal_local A S hSF hSsub hCS p hp hz
      have hzPFA : z ∈ PFA := hZlePFA hz
      have hzcop : Nat.Coprime p (orderOf z) := by
        dsimp [PFA, pPrimeCoreOfFitting] at hzPFA
        exact orderOf_coprime_of_mem_pPrimeCore_map_local (H := F) (p := p) hzPFA
      exact fstar_mem_pResidualOf_of_order_coprime S p hp hzS hzcop
    have hRcZ : qCoreOf B p ≤ Subgroup.centralizer (Z : Set G) :=
      hRcK.trans (Subgroup.centralizer_le (show (Z : Set G) ⊆ (K : Set G) from hZleK))
    exact hRcZ.trans (centralizer_normal_le_A hsimple A hA hZleA hZnormal hZne)

set_option maxHeartbeats 1600000 in
/-- The Thompson assembly for the second conjunct, once `O_p(B) ≤ A` is
known: `O_p(B)` centralizes `O_{p'}(F(A))` by the coprime subnormal
self-centralizing lemma, then the generation lemma finishes the residual. -/
private theorem commutator_qCoreOf_B_pResidualOf_generalizedFitting_of_le_A_local
    {G : Type u} [Group G] [Finite G]
    (A S B : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (hSB : S ≤ B)
    (p : ℕ) (hp : p.Prime) (hpF : p ∈ primesOfOrder (fittingSubgroupOf A))
    (hRleA : qCoreOf B p ≤ A)
    (hcentKR : Centralizes (pResidualOf S p) (qCoreOf B p)) :
    ⁅qCoreOf B p, pResidualOf (generalizedFittingSubgroupOf A) p⁆ = ⊥ := by
  classical
  let F : Subgroup G := fittingSubgroupOf A
  let PFA : Subgroup G := pPrimeCoreOfFitting A p
  let PS : Subgroup G := (pPrimeCore p (↥(F ⊓ S))).map (F ⊓ S).subtype
  let : Fact p.Prime := ⟨hp⟩
  have hRcK : qCoreOf B p ≤ Subgroup.centralizer ((pResidualOf S p : Subgroup G) : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact ((Subgroup.mem_centralizer_iff.mp (hcentKR hk)) r hr).symm
  have hFnil : Group.IsNilpotent F := fittingSubgroupOf_isNilpotent A
  have hPFAnormA : IsNormalIn PFA A := by
    simpa [PFA, pPrimeCoreOfFitting, F] using
      (fstar_characteristic_subgroupOf_map_normal_in (F := F)
        (K := pPrimeCore p (↥F)) (pPrimeCore_characteristic (p := p))
        (fittingSubgroupOf_isNormalIn A))
  have hPK : qCoreOf B p ≤ Subgroup.normalizer (PFA : Set G) :=
    hRleA.trans (le_normalizer_of_isNormalIn hPFAnormA)
  have hPS_le_PFA : PS ≤ PFA := by
    intro x hx
    have hxFS : x ∈ F ⊓ S :=
      Subgroup.map_subtype_le (H := F ⊓ S) (pPrimeCore p (↥(F ⊓ S))) hx
    have hxF : x ∈ F := hxFS.1
    have hxcop : Nat.Coprime p (orderOf x) :=
      orderOf_coprime_of_mem_pPrimeCore_map_local (H := F ⊓ S) (p := p) hx
    have hxPFA : x ∈ (pPrimeCore p (↥F)).map F.subtype :=
      element_mem_pPrimeCore_of_order_coprime_of_nilpotent_local (H := F) (p := p)
        hFnil hxF hxcop
    simpa [PFA, pPrimeCoreOfFitting, F] using hxPFA
  have hPFAnil : Group.IsNilpotent PFA := by
    have e : pPrimeCore p (↥F) ≃* ↥PFA :=
      Subgroup.equivMapOfInjective (pPrimeCore p (↥F)) F.subtype F.subtype_injective
    let : Group.IsNilpotent (↥F) := hFnil
    have : Group.IsNilpotent (pPrimeCore p (↥F)) := by
      infer_instance
    exact Group.nilpotent_of_mulEquiv e
  have hPS_sub : (PS.subgroupOf PFA).IsSubnormal :=
    isSubnormal_of_nilpotent hPFAnil PS hPS_le_PFA
  have hPS_le_K : PS ≤ pResidualOf S p := by
    intro x hx
    have hxS : x ∈ S :=
      (Subgroup.map_subtype_le (H := F ⊓ S) (pPrimeCore p (↥(F ⊓ S))) hx).2
    have hxcop : Nat.Coprime p (orderOf x) :=
      orderOf_coprime_of_mem_pPrimeCore_map_local (H := F ⊓ S) (p := p) hx
    exact fstar_mem_pResidualOf_of_order_coprime S p hp hxS hxcop
  have hRcPS : qCoreOf B p ≤ Subgroup.centralizer (PS : Set G) :=
    hRcK.trans (Subgroup.centralizer_le (show (PS : Set G) ⊆ (pResidualOf S p : Set G) from hPS_le_K))
  have hself : PFA ⊓ Subgroup.centralizer (PS : Set G) ≤ PS := by
    simpa [PFA, PS, pPrimeCoreOfFitting, F] using
      (pPrimeCore_fitting_centralizer_le_fitting_pPrimeCore_local A S hSF hSsub hCS p hp)
  have hcop : Nat.Coprime (Nat.card (qCoreOf B p)) (Nat.card PFA) := by
    have hcardPFA : Nat.card PFA = Nat.card (pPrimeCore p (↥F)) := by
      dsimp [PFA, pPrimeCoreOfFitting, F]
      exact Subgroup.card_map_of_injective (fittingSubgroupOf A).subtype_injective
    have hcopP : Nat.Coprime p (Nat.card PFA) := by
      rw [hcardPFA]
      exact pPrimeCore_coprime_card (p := p) (G := ↥F)
    rcases (IsPGroup.iff_card (p := p) (G := qCoreOf B p)).mp (qCoreOf_isPGroup B p) with
      ⟨n, hn⟩
    rw [hn]
    exact hcopP.pow_left n
  have hsolv : Group.IsSolvable PFA := by
    let : Group.IsNilpotent PFA := hPFAnil
    infer_instance
  have hcentPFA : qCoreOf B p ≤ Subgroup.centralizer (PFA : Set G) :=
    centralizes_of_subnormal_selfCentralizing_coprime_local (qCoreOf B p) PFA PS
      hPK hPS_le_PFA hPS_sub hRcPS hself hcop hsolv
  have hJlePFA :
      (⨆ q : {q : ℕ // q.Prime ∧ q ≠ p}, qCoreOf A q.1) ≤ PFA := by
    have hEq : pResidualOf (fittingSubgroupOf A) p =
        (⨆ q : {q : ℕ // q.Prime ∧ q ≠ p}, qCoreOf A q.1) := by
      simpa [F] using pResidualOf_fitting_eq_iSup_qCoreOf_of_ne_local A p hp
    rw [← hEq]
    simpa [PFA, pPrimeCoreOfFitting, F] using pResidualOf_fitting_le_pPrimeCore_local A p hp
  have hgen0 : pResidualOf (generalizedFittingSubgroupOf A) p ≤
      pResidualOf S p ⊔ (⨆ q : {q : ℕ // q.Prime ∧ q ≠ p}, qCoreOf A q.1) :=
    pResidualOf_generalizedFitting_le_generation_local A S hSF hSsub hCS p hp
  have hgen : pResidualOf (generalizedFittingSubgroupOf A) p ≤ pResidualOf S p ⊔ PFA :=
    hgen0.trans (sup_le_sup_left hJlePFA (pResidualOf S p))
  have hRcSup : qCoreOf B p ≤ Subgroup.centralizer
      ((pResidualOf S p ⊔ PFA : Subgroup G) : Set G) :=
    le_centralizer_of_centralizes_sup_local (qCoreOf B p) (pResidualOf S p) PFA hRcK hcentPFA
  have hRcRes : qCoreOf B p ≤ Subgroup.centralizer
      ((pResidualOf (generalizedFittingSubgroupOf A) p : Subgroup G) : Set G) :=
    hRcSup.trans (Subgroup.centralizer_le
      (show (pResidualOf (generalizedFittingSubgroupOf A) p : Set G) ⊆
        (pResidualOf S p ⊔ PFA : Subgroup G) from hgen))
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer
    (H₁ := qCoreOf B p)
    (H₂ := pResidualOf (generalizedFittingSubgroupOf A) p)).mpr hRcRes

set_option maxHeartbeats 1200000 in
public theorem bender1970_1_7_residual_commutator_assembly
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B) :
    (∀ q : ℕ, q.Prime → q ∉ primesOfOrder (fittingSubgroupOf A) →
      qCoreOf B q ⊓ A = ⊥) ∧
    (∀ p : ℕ, p.Prime → p ∈ primesOfOrder (fittingSubgroupOf A) →
      ⁅qCoreOf B p, pResidualOf (generalizedFittingSubgroupOf A) p⁆ = ⊥) := by
  constructor
  · intro q hq hqnot
    exact qCoreOf_B_inf_A_eq_bot_of_not_mem_primes_local A S B hSF hSsub hCS hSB q hq hqnot
  · intro p hp hpF
    classical
    have hRleA_if : pResidualOf (generalizedFittingSubgroupOf A) p ≠ ⊥ → qCoreOf B p ≤ A := by
      intro hResNe
      exact qCoreOf_B_le_A_of_pResidual_ne_bot_local hsimple A hA S hSF hSsub hCS hSB
        p hp hpF hResNe
    have hResCases : pResidualOf (generalizedFittingSubgroupOf A) p = ⊥ ∨
        pResidualOf (generalizedFittingSubgroupOf A) p ≠ ⊥ := Classical.em _
    rcases hResCases with hResBot | hResNe
    · simpa [hResBot]
    · have hRleA : qCoreOf B p ≤ A := hRleA_if hResNe
      have hcentKR : Centralizes (pResidualOf S p) (qCoreOf B p) :=
        pResidualOf_S_centralizes_qCoreOf_B_local hsimple A hA S hSF hSsub hCS hSB p hp hpF
      exact commutator_qCoreOf_B_pResidualOf_generalizedFitting_of_le_A_local
        A S B hSF hSsub hCS hSB p hp hpF hRleA hcentKR

/-- Bender [1], Statement 1.7(i): `O_q(B) ∩ A = 1` for primes outside
`π(F(A))`. -/
public theorem bender1970_1_7_i_oddCoreDisjoint
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B) :
    ∀ q : ℕ, q.Prime → q ∉ primesOfOrder (fittingSubgroupOf A) →
      qCoreOf B q ⊓ A = ⊥ := by
  exact (bender1970_1_7_residual_commutator_assembly
    hsimple A hA S hSF hSsub hCS hSB).1

end CFSG.GorensteinWalter
