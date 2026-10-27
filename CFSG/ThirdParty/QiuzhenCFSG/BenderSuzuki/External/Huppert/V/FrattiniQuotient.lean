module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.Semidirect

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v
/--
The upper quotient over a maximal proper invariant normal subgroup is the
elementary-abelian chief layer in Huppert V.8.13 step (3a).
-/
public theorem hkt_maximal_invariant_quotient_exists_isElementaryAbelian
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hN_ne_top : N ≠ ⊤)
    (hNmax :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        N ≤ K → K ≠ ⊤ → K = N)
    (hquot_nil : Group.IsNilpotent (Q ⧸ N)) :
    ∃ r : ℕ, Nat.Prime r ∧ IsElementaryAbelian r (Q ⧸ N) := by
  let ψ : MulAut (Q ⧸ N) := invariantQuotientAut φ N hNφ
  let M : Subgroup (Q ⧸ N) := ⊤
  haveI : M.Normal := by
    dsimp [M]
    infer_instance
  have hMinv : IsInvariant (Subgroup.zpowers ψ) (Q ⧸ N) M := by
    refine ⟨?_⟩
    intro a x
    simp [M]
  have hM_ne_bot : M ≠ ⊥ := by
    haveI : Nontrivial (Q ⧸ N) := (QuotientGroup.nontrivial_iff (N := N)).2 hN_ne_top
    simp [M]
  have hMmin :
      ∀ K : Subgroup (Q ⧸ N), K.Normal →
        IsInvariant (Subgroup.zpowers ψ) (Q ⧸ N) K →
          K ≠ ⊥ → K ≤ M → K = M := by
    intro K hKnormal hKinv hK_ne_bot _hKM
    have hKtop : K = ⊤ :=
      hkt_quotient_no_proper_nontrivial_invariant_normal
        φ N hNφ hNmax K hKnormal (by simpa [ψ] using hKinv) hK_ne_bot
    simpa [M] using hKtop
  haveI : Group.IsNilpotent (Q ⧸ N) := hquot_nil
  have hM_nil : Group.IsNilpotent M := by
    exact Group.nilpotent_of_mulEquiv
      (G := Q ⧸ N) (G' := M)
      (Subgroup.topEquiv.symm : (Q ⧸ N) ≃* M)
  obtain ⟨r, hr_prime, hM_elem⟩ :=
    hkt_minimal_invariant_nilpotent_exists_isElementaryAbelian
      ψ M hMinv hM_ne_bot hMmin hM_nil
  exact ⟨r, hr_prime, by simpa [M] using hkt_isElementaryAbelian_of_top hM_elem⟩

/-- A group that embeds in a nilpotent group is nilpotent.  This is the
subgroup-of-nilpotent fact packaged for non-subtype embeddings. -/
public theorem hkt_nilpotent_of_injective_to_nilpotent
    {G H : Type u} [Group G] [Group H] [Group.IsNilpotent H]
    (f : G →* H) (hf : Function.Injective f) :
    Group.IsNilpotent G := by
  let e : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict ⟨?_, ?_⟩
  · exact Group.nilpotent_of_mulEquiv (G := f.range) (G' := G) e.symm
  · intro x y hxy
    exact hf (congrArg Subtype.val hxy)
  · exact f.rangeRestrict_surjective

/--
Huppert III.2.5(c) in the form needed in V.8.13 step (3a): if the two
quotients by normal subgroups are nilpotent and their kernels intersect
trivially, then the diagonal map into the product of the quotients embeds the
ambient group in a nilpotent group.
-/
public theorem hkt_nilpotent_of_quotient_product_injective
    {G : Type u} [Group G] (K L : Subgroup G) [K.Normal] [L.Normal]
    (hK : Group.IsNilpotent (G ⧸ K))
    (hL : Group.IsNilpotent (G ⧸ L))
    (hKL : K ⊓ L = ⊥) :
    Group.IsNilpotent G := by
  let qK : G →* G ⧸ K := QuotientGroup.mk' K
  let qL : G →* G ⧸ L := QuotientGroup.mk' L
  let f : G →* (G ⧸ K) × (G ⧸ L) := qK.prod qL
  haveI : Group.IsNilpotent (G ⧸ K) := hK
  haveI : Group.IsNilpotent (G ⧸ L) := hL
  have hfker : f.ker = ⊥ := by
    rw [MonoidHom.ker_prod, QuotientGroup.ker_mk', QuotientGroup.ker_mk', hKL]
  exact hkt_nilpotent_of_injective_to_nilpotent f ((MonoidHom.ker_eq_bot_iff f).1 hfker)

/--
Huppert V.8.13 step (3a), lower layer: the maximal proper invariant normal
subgroup `N` is a `q`-group.  If two different primes occurred in the
nilpotent subgroup `N`, their characteristic Sylow subgroups would map to two
proper invariant normal subgroups of `Q` with trivial intersection.  The
minimal-counterexample quotient hypothesis would make both quotients
nilpotent, and the diagonal embedding into their product would make `Q`
nilpotent, a contradiction.
-/
public theorem hkt_maximal_lower_nilpotent_exists_isPGroup
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (N : Subgroup Q) [N.Normal]
    (hNinv : IsInvariant (Subgroup.zpowers φ) Q N)
    (hN_ne_bot : N ≠ ⊥) (hN_ne_top : N ≠ ⊤)
    (hN_nil : Group.IsNilpotent N)
    (hproper_invariant_quotient_nil :
      ∀ K : Subgroup Q, [K.Normal] → K ≠ ⊥ → K ≠ ⊤ →
        (∀ q : Q, q ∈ K ↔ φ q ∈ K) → Group.IsNilpotent (Q ⧸ K))
    (hnon_nil : ¬ Group.IsNilpotent Q) :
    ∃ q : ℕ, Nat.Prime q ∧ IsPGroup q N := by
  classical
  have hcardN_ne_one : Nat.card N ≠ 1 := by
    have : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot (H := N)).2 hN_ne_bot
    exact ne_of_gt this
  obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card N) hcardN_ne_one
  letI : Fact r.Prime := ⟨hr_prime⟩
  refine ⟨r, hr_prime, ?_⟩
  have hcardN_power : Nat.card N = r ^ (Nat.card N).primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := N)).ne'
    intro s hs_prime hs_dvd
    by_contra hs_ne_r
    letI : Fact s.Prime := ⟨hs_prime⟩
    let R : Sylow r N := default
    let S : Sylow s N := default
    have hR_ne_bot : (R : Subgroup N) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (G := N) (p := r) R hr_dvd
    have hS_ne_bot : (S : Subgroup N) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (G := N) (p := s) S hs_dvd
    have hR_normal_N : (R : Subgroup N).Normal :=
      Group.IsNilpotent.sylow_normal (G := N) hN_nil r R
    have hS_normal_N : (S : Subgroup N).Normal :=
      Group.IsNilpotent.sylow_normal (G := N) hN_nil s S
    have hR_char : (R : Subgroup N).Characteristic :=
      Sylow.characteristic_of_normal (G := N) (p := r) R hR_normal_N
    have hS_char : (S : Subgroup N).Characteristic :=
      Sylow.characteristic_of_normal (G := N) (p := s) S hS_normal_N
    let Ramb : Subgroup Q := (R : Subgroup N).map N.subtype
    let Samb : Subgroup Q := (S : Subgroup N).map N.subtype
    have hRamb_normal : Ramb.Normal := by
      haveI : (R : Subgroup N).Characteristic := hR_char
      simpa [Ramb] using (inferInstance : Ramb.Normal)
    have hSamb_normal : Samb.Normal := by
      haveI : (S : Subgroup N).Characteristic := hS_char
      simpa [Samb] using (inferInstance : Samb.Normal)
    have hRamb_inv : IsInvariant (Subgroup.zpowers φ) Q Ramb := by
      haveI : IsInvariant (Subgroup.zpowers φ) Q N := hNinv
      have hR_inv_N : IsInvariant (Subgroup.zpowers φ) N (R : Subgroup N) := by
        haveI : (R : Subgroup N).Characteristic := hR_char
        simpa using isInvariant_of_characteristic (A := Subgroup.zpowers φ) (G := N)
          (R : Subgroup N)
      haveI : IsInvariant (Subgroup.zpowers φ) N (R : Subgroup N) := hR_inv_N
      simpa [Ramb] using
        isInvariant_map_subtype (A := Subgroup.zpowers φ) (G := Q) N (R : Subgroup N)
    have hSamb_inv : IsInvariant (Subgroup.zpowers φ) Q Samb := by
      haveI : IsInvariant (Subgroup.zpowers φ) Q N := hNinv
      have hS_inv_N : IsInvariant (Subgroup.zpowers φ) N (S : Subgroup N) := by
        haveI : (S : Subgroup N).Characteristic := hS_char
        simpa using isInvariant_of_characteristic (A := Subgroup.zpowers φ) (G := N)
          (S : Subgroup N)
      haveI : IsInvariant (Subgroup.zpowers φ) N (S : Subgroup N) := hS_inv_N
      simpa [Samb] using
        isInvariant_map_subtype (A := Subgroup.zpowers φ) (G := Q) N (S : Subgroup N)
    have hRamb_ne_bot : Ramb ≠ ⊥ := by
      intro hbot
      exact hR_ne_bot
        ((Subgroup.map_eq_bot_iff_of_injective (H := (R : Subgroup N)) (f := N.subtype)
          N.subtype_injective).1 (by simpa [Ramb] using hbot))
    have hSamb_ne_bot : Samb ≠ ⊥ := by
      intro hbot
      exact hS_ne_bot
        ((Subgroup.map_eq_bot_iff_of_injective (H := (S : Subgroup N)) (f := N.subtype)
          N.subtype_injective).1 (by simpa [Samb] using hbot))
    have hRamb_le_N : Ramb ≤ N := by
      simpa [Ramb] using Subgroup.map_subtype_le (H := N) (K := (R : Subgroup N))
    have hSamb_le_N : Samb ≤ N := by
      simpa [Samb] using Subgroup.map_subtype_le (H := N) (K := (S : Subgroup N))
    have hRamb_ne_top : Ramb ≠ ⊤ := by
      intro htop
      have htop_le_N : (⊤ : Subgroup Q) ≤ N := by
        simpa [htop] using hRamb_le_N
      exact hN_ne_top (top_le_iff.mp htop_le_N)
    have hSamb_ne_top : Samb ≠ ⊤ := by
      intro htop
      have htop_le_N : (⊤ : Subgroup Q) ≤ N := by
        simpa [htop] using hSamb_le_N
      exact hN_ne_top (top_le_iff.mp htop_le_N)
    have hRambφ : ∀ q : Q, q ∈ Ramb ↔ φ q ∈ Ramb :=
      hkt_zpowers_invariant_generator φ Ramb
    have hSambφ : ∀ q : Q, q ∈ Samb ↔ φ q ∈ Samb :=
      hkt_zpowers_invariant_generator φ Samb
    have hRquot_nil : Group.IsNilpotent (Q ⧸ Ramb) := by
      letI : Ramb.Normal := hRamb_normal
      exact hproper_invariant_quotient_nil Ramb hRamb_ne_bot hRamb_ne_top hRambφ
    have hSquot_nil : Group.IsNilpotent (Q ⧸ Samb) := by
      letI : Samb.Normal := hSamb_normal
      exact hproper_invariant_quotient_nil Samb hSamb_ne_bot hSamb_ne_top hSambφ
    have hRamb_p : IsPGroup r Ramb := by
      simpa [Ramb] using R.isPGroup'.map N.subtype
    have hSamb_p : IsPGroup s Samb := by
      simpa [Samb] using S.isPGroup'.map N.subtype
    have hrs : r ≠ s := by
      intro hrs
      exact hs_ne_r hrs.symm
    have hcop : Nat.Coprime (Nat.card Ramb) (Nat.card Samb) :=
      IsPGroup.coprime_card_of_ne r s hrs Ramb Samb hRamb_p hSamb_p
    have hRS_bot : Ramb ⊓ Samb = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    haveI : Ramb.Normal := hRamb_normal
    haveI : Samb.Normal := hSamb_normal
    exact hnon_nil
      (hkt_nilpotent_of_quotient_product_injective Ramb Samb hRquot_nil hSquot_nil hRS_bot)
  exact IsPGroup.of_card (p := r) (G := N) hcardN_power

/--
If the lower normal subgroup and the upper quotient in Huppert V.8.13 step
(3a) are `p`-groups for the same prime, then the ambient group is itself a
`p`-group and hence nilpotent.  In the nonnilpotent branch this rules out the
possibility that the lower and upper elementary layers have the same prime.
-/
public theorem hkt_false_of_same_prime_lower_and_quotient_pgroups
    {Q : Type u} [Group Q] [Finite Q] {r : ℕ} [Fact r.Prime]
    (N : Subgroup Q) [N.Normal]
    (hnon_nil : ¬ Group.IsNilpotent Q)
    (hN_p : IsPGroup r N)
    [IsElementaryAbelian r (Q ⧸ N)] :
    False := by
  have hquot_p : IsPGroup r (Q ⧸ N) :=
    IsElementaryAbelian.isPGroup r (Q ⧸ N)
  have hQ_p : IsPGroup r Q :=
    hkt_isPGroup_of_normal_quotient N hN_p hquot_p
  exact hnon_nil hQ_p.isNilpotent

/--
Frattini facts for the lower subgroup in Huppert V.8.13 step (3a).
For a maximal proper invariant normal subgroup `N` that is already known to be
a `q`-group, the Frattini subgroup maps to a proper invariant normal subgroup
of the ambient group, and the Frattini quotient is elementary abelian.  The
remaining source step is to prove this Frattini image is actually trivial.
-/
public theorem huppertV813_lower_frattini_ambient_facts
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (N : Subgroup Q) [N.Normal]
    (hNinv : IsInvariant (Subgroup.zpowers φ) Q N)
    (_hN_ne_bot : N ≠ ⊥) (hN_ne_top : N ≠ ⊤)
    {q : ℕ} [Fact q.Prime] (hN_p : IsPGroup q N) :
    let Φ : Subgroup N := frattini N
    let Φamb : Subgroup Q := Φ.map N.subtype
    Φamb.Normal ∧
      IsInvariant (Subgroup.zpowers φ) Q Φamb ∧
      Φamb ≤ N ∧
      IsPGroup q Φamb ∧
      IsElementaryAbelian q (N ⧸ Φ) ∧
      (Φ ≠ ⊥ → Φamb ≠ ⊥) ∧
      Φamb ≠ ⊤ := by
  classical
  let Φ : Subgroup N := frattini N
  let Φamb : Subgroup Q := Φ.map N.subtype
  have hΦ_char : Φ.Characteristic := by
    simpa [Φ] using (frattini_characteristic (G := N))
  have hΦamb_normal : Φamb.Normal := by
    haveI : Φ.Characteristic := hΦ_char
    simpa [Φamb] using (hkt_map_characteristic_of_normal_normal (Q := Q) N Φ)
  have hΦamb_invariant : IsInvariant (Subgroup.zpowers φ) Q Φamb := by
    haveI : IsInvariant (Subgroup.zpowers φ) Q N := hNinv
    have hΦ_invariant_N : IsInvariant (Subgroup.zpowers φ) N Φ := by
      haveI : Φ.Characteristic := hΦ_char
      simpa [Φ] using
        isInvariant_of_characteristic (A := Subgroup.zpowers φ) (G := N) Φ
    haveI : IsInvariant (Subgroup.zpowers φ) N Φ := hΦ_invariant_N
    simpa [Φamb] using
      isInvariant_map_subtype (A := Subgroup.zpowers φ) (G := Q) N Φ
  have hΦamb_le_N : Φamb ≤ N := by
    simpa [Φamb] using Subgroup.map_subtype_le (H := N) (K := Φ)
  have hΦamb_p : IsPGroup q Φamb := by
    letI : Fact (IsPGroup q N) := ⟨hN_p⟩
    have hΦ_p : IsPGroup q Φ := hN_p.to_subgroup Φ
    simpa [Φamb] using hΦ_p.map N.subtype
  have hquot_elem : IsElementaryAbelian q (N ⧸ Φ) := by
    letI : Fact (IsPGroup q N) := ⟨hN_p⟩
    simpa [Φ] using isElementaryAbelian_quotient_frattini (R := N) (p := q)
  have hΦamb_ne_bot_of_Φ : Φ ≠ ⊥ → Φamb ≠ ⊥ := by
    intro hΦ_ne_bot hΦamb_bot
    exact hΦ_ne_bot
      ((Subgroup.map_eq_bot_iff_of_injective (H := Φ) (f := N.subtype)
        N.subtype_injective).1 (by simpa [Φamb] using hΦamb_bot))
  have hΦamb_ne_top : Φamb ≠ ⊤ := by
    intro htop
    have htop_le_N : (⊤ : Subgroup Q) ≤ N := by
      simpa [htop] using hΦamb_le_N
    exact hN_ne_top (top_le_iff.mp htop_le_N)
  exact
    ⟨hΦamb_normal, hΦamb_invariant, hΦamb_le_N, hΦamb_p, hquot_elem,
      hΦamb_ne_bot_of_Φ, hΦamb_ne_top⟩

/--
If the ambient image of `frattini N` is trivial, then the Frattini subgroup of
`N` itself is trivial.  This is the injectivity half of the lower-layer
Frattini reduction in Huppert V.8.13 step (3a).
-/
public theorem hkt_lower_frattini_eq_bot_of_ambient_eq_bot
    {Q : Type u} [Group Q] (N : Subgroup Q)
    (hΦamb :
      (frattini N).map N.subtype = (⊥ : Subgroup Q)) :
    frattini N = ⊥ := by
  exact
    (Subgroup.map_eq_bot_iff_of_injective
      (H := frattini N) (f := N.subtype) N.subtype_injective).1 hΦamb

/--
Once the lower Frattini image has been killed, the nilpotent lower `p`-group
is elementary abelian.  The still-hard source step is proving that ambient
Frattini image is trivial.
-/
public theorem hkt_lower_isElementaryAbelian_of_frattini_ambient_eq_bot
    {Q : Type u} [Group Q] [Finite Q] (N : Subgroup Q)
    {p : ℕ} [Fact p.Prime] (hN_p : IsPGroup p N)
    (hΦamb :
      (frattini N).map N.subtype = (⊥ : Subgroup Q)) :
    IsElementaryAbelian p N := by
  letI : Fact (IsPGroup p N) := ⟨hN_p⟩
  exact
    (frattini_eq_bot_iff_isElementaryAbelian (R := N) (p := p)).1
      (hkt_lower_frattini_eq_bot_of_ambient_eq_bot N hΦamb)

/--
Huppert III.3.7 in the narrow form needed in V.8.13: if a normal subgroup
`K` lies in the Frattini subgroup and the quotient by `K` is nilpotent, then
the quotient by the Frattini subgroup is nilpotent.  This is just nilpotence
descending through the third isomorphism theorem.
-/
public theorem hkt_nilpotent_quotient_frattini_of_quotient_le_frattini
    {G : Type u} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    (hK_le_frattini : K ≤ frattini G)
    (hKquot_nil : Group.IsNilpotent (G ⧸ K)) :
    Group.IsNilpotent (G ⧸ frattini G) := by
  haveI : Group.IsNilpotent (G ⧸ K) := hKquot_nil
  haveI : (frattini G).Normal := by infer_instance
  let e : (G ⧸ K) ⧸ (frattini G).map (QuotientGroup.mk' K) ≃* G ⧸ frattini G :=
    QuotientGroup.quotientQuotientEquivQuotient (N := K) (M := frattini G)
      hK_le_frattini
  exact Group.nilpotent_of_mulEquiv
    (G := (G ⧸ K) ⧸ (frattini G).map (QuotientGroup.mk' K))
    (G' := G ⧸ frattini G) e

/-- A maximal subgroup containing the kernel maps to a maximal subgroup under
a surjective homomorphism. -/
public theorem hkt_isCoatom_map_of_surjective_of_ker_le
    {G H : Type u} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) {M : Subgroup G}
    (hker : f.ker ≤ M) (hM : IsCoatom M) :
    IsCoatom (M.map f) := by
  refine ⟨?_, ?_⟩
  · intro htop
    apply hM.1
    have hmap : M.map f = (⊤ : Subgroup G).map f := by
      simpa [Subgroup.map_top_of_surjective f hf] using htop
    exact Subgroup.map_injective_of_ker_le (f := f) (H := M) (K := ⊤)
      hker le_top hmap
  · intro K hMK
    have hcomap_eq : K.comap f = ⊤ := by
      have hM_lt_comap : M < K.comap f := by
        refine lt_of_le_of_ne ?_ ?_
        · intro x hxM
          exact hMK.le (Subgroup.mem_map_of_mem f hxM)
        · intro hEq
          have hK_le_Mmap : K ≤ M.map f := by
            intro y hyK
            rcases hf y with ⟨x, rfl⟩
            have hx_comap : x ∈ K.comap f := hyK
            have hxM : x ∈ M := by simpa [hEq] using hx_comap
            exact Subgroup.mem_map_of_mem f hxM
          exact hMK.ne (le_antisymm hMK.le hK_le_Mmap)
      exact hM.2 (K.comap f) hM_lt_comap
    apply top_unique
    intro y _hy
    rcases hf y with ⟨x, rfl⟩
    change x ∈ K.comap f
    rw [hcomap_eq]
    simp

/--
Huppert III.3.7 / Gaschütz lifting in finite-group form: nilpotence of
`G/Φ(G)` lifts to nilpotence of `G`.  We prove it through Mathlib's finite
nilpotence criterion: every maximal subgroup contains `Φ(G)`, so normality of
its image in the nilpotent Frattini quotient pulls back to normality of the
maximal subgroup.
-/
public theorem hkt_nilpotent_of_quotient_frattini_nilpotent
    {G : Type u} [Group G] [Finite G]
    (hquot : Group.IsNilpotent (G ⧸ frattini G)) :
    Group.IsNilpotent G := by
  classical
  have hmax_normal : ∀ H : Subgroup G, IsCoatom H → H.Normal := by
    intro H hH
    have hΦ_le_H : frattini G ≤ H := frattini_le_coatom hH
    let q : G →* G ⧸ frattini G := QuotientGroup.mk' (frattini G)
    let Hbar : Subgroup (G ⧸ frattini G) := H.map q
    have : Group.IsNilpotent (G ⧸ frattini G) := hquot
    have hHbar_coatom : IsCoatom Hbar := by
      exact hkt_isCoatom_map_of_surjective_of_ker_le q
        (QuotientGroup.mk'_surjective (frattini G))
        (by simpa [q] using hΦ_le_H) hH
    have hHbar_normal : Hbar.Normal := by
      exact Subgroup.NormalizerCondition.normal_of_coatom Hbar
        (Group.normalizerCondition_of_isNilpotent (G := G ⧸ frattini G)) hHbar_coatom
    have hcomap_Hbar : Hbar.comap q = H := by
      simp [Hbar, q, QuotientGroup.comap_map_mk', sup_eq_right.mpr hΦ_le_H]
    have hcomap_normal : (Hbar.comap q).Normal := hHbar_normal.comap q
    simpa [hcomap_Hbar] using hcomap_normal
  exact ((Group.isNilpotent_of_finite_tfae (G := G)).out 3 1).mp hmax_normal

/--
Huppert III.3.3(b), in the exact ambient-image form needed here.  If `N` is
normal in a finite group `G`, then the image of `Φ(N)` in `G` lies in `Φ(G)`.
-/
public theorem hkt_frattini_map_subtype_le_frattini_of_normal
    {G : Type u} [Group G] [Finite G] (N : Subgroup G) [N.Normal] :
    (frattini N).map N.subtype ≤ frattini G := by
  classical
  let Φ : Subgroup N := frattini N
  let Φamb : Subgroup G := Φ.map N.subtype
  have hΦ_char : Φ.Characteristic := by
    simpa [Φ] using (frattini_characteristic (G := N))
  haveI : Φ.Normal := by
    haveI : Φ.Characteristic := hΦ_char
    infer_instance
  have hΦamb_normal : Φamb.Normal := by
    haveI : Φ.Characteristic := hΦ_char
    simpa [Φamb] using hkt_map_characteristic_of_normal_normal (Q := G) N Φ
  intro x hx
  change x ∈ Φamb at hx
  rcases hx with ⟨y, hyΦ, rfl⟩
  rw [frattini, Order.radical]
  rw [Subgroup.mem_iInf]
  intro M
  rw [Subgroup.mem_iInf]
  intro hM
  change IsCoatom M at hM
  by_contra hy_not_M
  have hMΦ_top : M ⊔ Φamb = ⊤ := by
    have hM_lt : M < M ⊔ Φamb := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro hsup_eq
      have hyM : (y : G) ∈ M := by
        rw [hsup_eq]
        exact (le_sup_right : Φamb ≤ M ⊔ Φamb) ⟨y, hyΦ, rfl⟩
      exact hy_not_M hyM
    exact hM.2 (M ⊔ Φamb) hM_lt
  have hsub_sup : M.subgroupOf N ⊔ Φ = ⊤ := by
    haveI : Φamb.Normal := hΦamb_normal
    apply eq_top_iff.mpr
    intro n _hn
    have hn_sup : (n : G) ∈ M ⊔ Φamb := by
      simp [hMΦ_top]
    rcases (Subgroup.mem_sup_of_normal_right (s := M) (t := Φamb) (x := (n : G))).1
        hn_sup with ⟨m, hmM, z, hzΦamb, hmz⟩
    rcases hzΦamb with ⟨zN, hzΦ, rfl⟩
    have hmN : m ∈ N := by
      have hm_eq : m = (n : G) * (zN : G)⁻¹ := by
        calc
          m = (m * (zN : G)) * (zN : G)⁻¹ := by simp
          _ = (n : G) * (zN : G)⁻¹ := by
              exact congrArg (fun a : G => a * (zN : G)⁻¹) (by simpa using hmz)
      rw [hm_eq]
      exact N.mul_mem n.2 (N.inv_mem zN.2)
    refine (Subgroup.mem_sup_of_normal_right
      (s := M.subgroupOf N) (t := Φ) (x := n)).2 ?_
    refine ⟨⟨m, hmN⟩, hmM, zN, hzΦ, ?_⟩
    exact Subtype.ext hmz
  have hMsub_top : M.subgroupOf N = ⊤ :=
    frattini_nongenerating (G := N) (K := M.subgroupOf N) (by simpa [Φ] using hsub_sup)
  have hyM : (y : G) ∈ M := by
    have : y ∈ M.subgroupOf N := by simp [hMsub_top]
    exact this
  exact hy_not_M hyM

/--
If the lower Frattini image in Huppert V.8.13 were nontrivial, induction gives
nilpotence of the quotient by that image.  Since the image lies in `Φ(Q)`,
nilpotence descends to `Q/Φ(Q)` and then lifts back to `Q`, contradicting the
minimal nonnilpotent choice.
-/
public theorem hkt_maximal_lower_frattini_ambient_eq_bot
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (N : Subgroup Q) [N.Normal]
    (hproper_invariant_quotient_nil :
      ∀ K : Subgroup Q, [K.Normal] → K ≠ ⊥ → K ≠ ⊤ →
        (∀ q : Q, q ∈ K ↔ φ q ∈ K) → Group.IsNilpotent (Q ⧸ K))
    (hnon_nil : ¬ Group.IsNilpotent Q)
    (hΦ_normal : ((frattini N).map N.subtype).Normal)
    (hΦ_invariant :
      IsInvariant (Subgroup.zpowers φ) Q ((frattini N).map N.subtype))
    (hΦ_ne_top : (frattini N).map N.subtype ≠ (⊤ : Subgroup Q)) :
    (frattini N).map N.subtype = (⊥ : Subgroup Q) := by
  by_contra hΦ_ne_bot
  let Φamb : Subgroup Q := (frattini N).map N.subtype
  haveI : Φamb.Normal := by simpa [Φamb] using hΦ_normal
  have hΦφ : ∀ q : Q, q ∈ Φamb ↔ φ q ∈ Φamb :=
    hkt_zpowers_invariant_generator φ Φamb
  have hquotΦ_nil : Group.IsNilpotent (Q ⧸ Φamb) :=
    hproper_invariant_quotient_nil Φamb (by simpa [Φamb] using hΦ_ne_bot)
      (by simpa [Φamb] using hΦ_ne_top) hΦφ
  have hΦ_le_frattini : Φamb ≤ frattini Q := by
    simpa [Φamb] using hkt_frattini_map_subtype_le_frattini_of_normal N
  have hquot_frattini_nil : Group.IsNilpotent (Q ⧸ frattini Q) :=
    hkt_nilpotent_quotient_frattini_of_quotient_le_frattini
      Φamb hΦ_le_frattini hquotΦ_nil
  exact hnon_nil (hkt_nilpotent_of_quotient_frattini_nilpotent hquot_frattini_nil)

/--
In the solvable maximal-branch setup of Huppert V.8.13, the lower elementary
abelian normal subgroup is self-centralizing.  Indeed its centralizer is a
normal invariant overgroup of `N`; maximality forces it to be either `N` or
`Q`, and the latter would put `N` in the center of `Q`.
-/
public theorem hkt_centralizer_lower_eq_self_of_maximal_elementary_branch
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {s : ℕ}
    (N : Subgroup Q) [N.Normal]
    (hNinv : IsInvariant (Subgroup.zpowers φ) Q N)
    (hN_ne_bot : N ≠ ⊥) (_hN_ne_top : N ≠ ⊤)
    (hNmax :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        N ≤ K → K ≠ ⊤ → K = N)
    (hcenter_bot : Subgroup.center Q = ⊥)
    (hN_elem : IsElementaryAbelian s N) :
    Subgroup.centralizer (N : Set Q) = N := by
  classical
  let C : Subgroup Q := Subgroup.centralizer (N : Set Q)
  have hN_le_C : N ≤ C := by
    letI : IsMulCommutative N := hN_elem.toIsMulCommutative
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simpa using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := N)).comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hC_normal : C.Normal := by
    simpa [C] using (inferInstance : (Subgroup.centralizer (N : Set Q)).Normal)
  have hC_invariant : IsInvariant (Subgroup.zpowers φ) Q C := by
    have hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N :=
      hkt_zpowers_invariant_generator φ N
    have hCφ : ∀ q : Q, q ∈ C ↔ φ q ∈ C := by
      intro x
      constructor
      · intro hx
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro n hn
        have hpre : φ.symm n ∈ N :=
          (hNφ (φ.symm n)).mpr (by simpa using hn)
        simpa using congrArg φ (hx (φ.symm n) hpre)
      · intro hx
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro n hn
        have hφn : φ n ∈ N := (hNφ n).mp hn
        simpa using congrArg φ.symm (hx (φ n) hφn)
    exact hkt_zpowers_invariant_of_generator φ C hCφ
  by_cases hCtop : C = ⊤
  · have hN_le_center : N ≤ Subgroup.center Q := by
      intro n hn
      rw [Subgroup.mem_center_iff]
      intro q
      have hqC : q ∈ C := by simp [hCtop]
      exact (Subgroup.mem_centralizer_iff.mp hqC n hn).symm
    have hN_le_bot : N ≤ (⊥ : Subgroup Q) := by
      simpa [hcenter_bot] using hN_le_center
    have hNbot : N = ⊥ := le_bot_iff.mp hN_le_bot
    exact False.elim (hN_ne_bot hNbot)
  · exact hNmax C hC_normal hC_invariant hN_le_C hCtop

/--
The lower elementary layer inherits the HKT fixed-point calculation: if its
elementary prime differs from the automorphism prime, then the cyclic group
generated by the restricted automorphism has trivial fixed-point subgroup.
-/
public theorem hkt_lower_fixedPointSubgroup_zpowers_eq_bot_of_distinct_prime
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p s : ℕ}
    [Fact p.Prime] [Fact s.Prime]
    (N : Subgroup Q)
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [IsElementaryAbelian s N]
    (hsp : s ≠ p)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1) :
    fixedPointSubgroup (↥(Subgroup.zpowers (invariantSubgroupAut φ N hNφ))) N = ⊥ := by
  exact hkt_fixedPointSubgroup_zpowers_eq_bot_of_distinct_elementary_prime_product
    (ψ := invariantSubgroupAut φ N hNφ) hsp
    (hkt_product_identity_of_invariant_subgroup φ N hNφ hprod)

/-- The restricted automorphism has period dividing the ambient HKT period. -/
public theorem hkt_invariant_subgroup_orderOf_dvd_prime_period
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    (N : Subgroup Q)
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hperiod : (fun q : Q => φ q)^[p] = id) :
    orderOf (invariantSubgroupAut φ N hNφ) ∣ p := by
  let ψ : MulAut N := invariantSubgroupAut φ N hNφ
  have hψp : ψ ^ p = 1 := by
    ext x
    calc
      (((ψ ^ p) x : N) : Q)
          = (((fun x : N => ψ x)^[p] x : N) : Q) := by
              rw [hkt_mulAut_pow_apply_iterate ψ p x]
      _ = (fun q : Q => φ q)^[p] (x : Q) := by
              exact invariantSubgroupAut_iterate_coe φ N hNφ p x
      _ = (x : Q) := by
              simpa using congrFun hperiod (x : Q)
  exact orderOf_dvd_of_pow_eq_one hψp

/--
If the lower elementary prime is different from the HKT period prime, then the
restricted automorphism has exact order `p`.
-/
public theorem hkt_lower_orderOf_eq_prime_of_distinct_prime
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p s : ℕ}
    [Fact p.Prime] [Fact s.Prime]
    (N : Subgroup Q)
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [Nontrivial N] [IsElementaryAbelian s N]
    (hsp : s ≠ p)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1) :
    orderOf (invariantSubgroupAut φ N hNφ) = p := by
  let ψ : MulAut N := invariantSubgroupAut φ N hNφ
  have hψ_dvd_p : orderOf ψ ∣ p :=
    hkt_invariant_subgroup_orderOf_dvd_prime_period φ N hNφ hperiod
  have hfix_bot : fixedPointSubgroup (↥(Subgroup.zpowers ψ)) N = ⊥ := by
    simpa [ψ] using
      hkt_lower_fixedPointSubgroup_zpowers_eq_bot_of_distinct_prime
        φ N hNφ hsp hprod
  have hψ_ne_one : ψ ≠ 1 := by
    intro hψone
    have hfix_top : fixedPointSubgroup (↥(Subgroup.zpowers ψ)) N = ⊤ := by
      rw [hψone]
      ext x
      simp [fixedPointSubgroup, FixedPoints.mem_subgroup]
    have htop_bot : (⊤ : Subgroup N) = ⊥ := by
      rw [← hfix_top, hfix_bot]
    exact (top_ne_bot : (⊤ : Subgroup N) ≠ ⊥) htop_bot
  rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd (orderOf ψ) hψ_dvd_p with
    horder_one | horder_p
  · exact False.elim <| hψ_ne_one (orderOf_eq_one_iff.mp horder_one)
  · exact horder_p

/--
Lower-layer analogue of the quotient action step used in Huppert V.8.13:
when `s ≠ p`, the restricted automorphism is fixed-point-free and has exact
prime order.
-/
public theorem huppertV813_lower_distinct_prime_regular_action
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p s : ℕ}
    [Fact p.Prime] [Fact s.Prime]
    (N : Subgroup Q)
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [Nontrivial N] [IsElementaryAbelian s N]
    (hsp : s ≠ p)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1) :
    fixedPointSubgroup (↥(Subgroup.zpowers (invariantSubgroupAut φ N hNφ))) N = ⊥ ∧
      orderOf (invariantSubgroupAut φ N hNφ) = p ∧
        Nat.card (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) = p ∧
          IsCyclic (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) ∧
            IsPGroup p (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) ∧
              ActsRegularly (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) N := by
  have hfix :
      fixedPointSubgroup (↥(Subgroup.zpowers (invariantSubgroupAut φ N hNφ))) N = ⊥ :=
    hkt_lower_fixedPointSubgroup_zpowers_eq_bot_of_distinct_prime
      φ N hNφ hsp hprod
  have horder : orderOf (invariantSubgroupAut φ N hNφ) = p :=
    hkt_lower_orderOf_eq_prime_of_distinct_prime φ N hNφ hsp hperiod hprod
  have hcard : Nat.card (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) = p :=
    natCard_zpowers_eq_prime_of_orderOf_eq (invariantSubgroupAut φ N hNφ) horder
  have hcyc : IsCyclic (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) :=
    isCyclic_zpowers (invariantSubgroupAut φ N hNφ)
  have hpgroup : IsPGroup p (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) :=
    isPGroup_zpowers_of_orderOf_eq_prime (invariantSubgroupAut φ N hNφ) horder
  have hregular :
      ActsRegularly (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) N :=
    hkt_actsRegularly_of_zpowers_prime_order_fixedPointSubgroup_eq_bot
      (invariantSubgroupAut φ N hNφ) hcard hfix
  exact ⟨hfix, horder, hcard, hcyc, hpgroup, hregular⟩

/--
Once Huppert V.8.13 (3b)'s `M(Q)` calculation has forced the quotient
elementary prime to be the HKT period prime and the quotient is known cyclic,
the elementary-cardinality package reduces the quotient order to `p`.
-/
public theorem hkt_quotient_card_eq_period_prime_of_same_prime_cyclic
    {Q : Type u} [Group Q] [Finite Q] {p r : ℕ}
    (N : Subgroup Q) [N.Normal]
    (hrp : r = p)
    (hquot_card_arith :
      ∃ n : ℕ,
        Nat.card (Q ⧸ N) = r ^ n ∧ n ≠ 0 ∧
          (∀ s : ℕ, Nat.Prime s → s ∣ Nat.card (Q ⧸ N) → s = r) ∧
            (IsCyclic (Q ⧸ N) → Nat.card (Q ⧸ N) = r))
    (hquot_cyclic : IsCyclic (Q ⧸ N)) :
    Nat.card (Q ⧸ N) = p := by
  rcases hquot_card_arith with ⟨_n, _hcard, _hn, _hprime_div, hcyc_card⟩
  simpa [hrp] using hcyc_card hquot_cyclic

/-- A cyclic quotient is generated by the image of one lifted element. -/
public theorem hkt_exists_zpowers_sup_top_of_cyclic_quotient
    {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal]
    (hcyc : IsCyclic (Q ⧸ N)) :
    ∃ a : Q, N ⊔ Subgroup.zpowers a = ⊤ := by
  classical
  let q : Q →* Q ⧸ N := QuotientGroup.mk' N
  obtain ⟨x, hx_top⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := Q ⧸ N)).1 hcyc
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective N x
  let H : Subgroup Q := N ⊔ Subgroup.zpowers a
  have hmap_top : H.map q = ⊤ := by
    apply eq_top_iff.2
    intro y _hy
    have hyzpow : y ∈ Subgroup.zpowers x := by
      simp [hx_top]
    rcases Subgroup.mem_zpowers_iff.mp hyzpow with ⟨n, rfl⟩
    have hxpow_eq : q (a ^ n) = x ^ n := by
      calc
        q (a ^ n) = q a ^ n := by simp [q]
        _ = x ^ n := by rw [ha]
    rw [← hxpow_eq]
    exact Subgroup.mem_map_of_mem q (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers a n))
  refine ⟨a, ?_⟩
  calc
    H = H ⊔ q.ker := by
      symm
      apply sup_eq_left.2
      simp [H, q, QuotientGroup.ker_mk']
    _ = Subgroup.comap q (H.map q) := by
      simpa using (Subgroup.comap_map_eq (f := q) (H := H)).symm
    _ = ⊤ := by simp [hmap_top]

/-- If the induced quotient automorphism fixes every coset, then a lift is
fixed modulo the lower subgroup. -/
public theorem hkt_quotient_fixed_top_forces_lift_div_mem
    {Q : Type u} [Group Q] (φ : MulAut Q)
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hfixed_top :
      fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊤)
    (a : Q) :
    φ a * a⁻¹ ∈ N := by
  have hfixed_a :
      ψ (QuotientGroup.mk' N a) = QuotientGroup.mk' N a := by
    have hmem :
        QuotientGroup.mk' N a ∈
          fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) := by
      simp [hfixed_top]
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hmem
    simpa [MulAut.smul_def] using hmem ⟨ψ, Subgroup.mem_zpowers ψ⟩
  have hfixed_hkt :
      invariantQuotientAut φ N hNφ (QuotientGroup.mk' N a) =
        QuotientGroup.mk' N a := by
    simpa [hψ] using hfixed_a
  have hquot_eq :
      QuotientGroup.mk' N (φ a) = QuotientGroup.mk' N a := by
    change QuotientGroup.mk' N (φ a) = QuotientGroup.mk' N a at hfixed_hkt
    exact hfixed_hkt
  simpa [div_eq_mul_inv] using
    (QuotientGroup.eq_iff_div_mem (N := N) (x := φ a) (y := a)).1 hquot_eq

/-- If a normal abelian subgroup together with one element generates a
center-free group, conjugation by that element is fixed-point-free on the
normal subgroup. -/
public theorem hkt_conjNormal_fixedPointSubgroup_eq_bot_of_sup_zpowers_center
    {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal]
    [IsMulCommutative N] (a : Q)
    (hsup : N ⊔ Subgroup.zpowers a = ⊤)
    (hcenter_bot : Subgroup.center Q = ⊥) :
    fixedPointSubgroup (↥(Subgroup.zpowers (MulAut.conjNormal (H := N) a))) N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxfix :
      (MulAut.conjNormal (H := N) a) x = x := by
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx
    exact hx ⟨MulAut.conjNormal (H := N) a, Subgroup.mem_zpowers _⟩
  have hcomm_a : Commute a (x : Q) := by
    have hxconj : a * (x : Q) * a⁻¹ = x := by
      simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using congrArg Subtype.val hxfix
    have hmul := congrArg (fun t : Q => t * a) hxconj
    change a * (x : Q) = (x : Q) * a
    simpa [mul_assoc] using hmul
  have hx_center : (x : Q) ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy_sup : y ∈ N ⊔ Subgroup.zpowers a := by
      simp [hsup]
    rcases (Subgroup.mem_sup_of_normal_left
        (x := y) (s := N) (t := Subgroup.zpowers a)).1 hy_sup with
      ⟨n, hnN, z, hz, rfl⟩
    have hn_comm : n * (x : Q) = (x : Q) * n := by
      simpa using congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := N)).comm ⟨n, hnN⟩ x)
    have hz_comm : z * (x : Q) = (x : Q) * z := by
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨m, rfl⟩
      exact (hcomm_a.zpow_left m).eq
    calc
      (n * z) * (x : Q) = n * (z * (x : Q)) := by simp [mul_assoc]
      _ = n * ((x : Q) * z) := by rw [hz_comm]
      _ = (n * (x : Q)) * z := by simp [mul_assoc]
      _ = ((x : Q) * n) * z := by rw [hn_comm]
      _ = (x : Q) * (n * z) := by simp [mul_assoc]
  have hx_bot : (x : Q) ∈ (⊥ : Subgroup Q) := by
    simpa [hcenter_bot] using hx_center
  apply Subtype.ext
  simpa using (Subgroup.mem_bot.mp hx_bot)

/-- If the quotient lift is fixed modulo `N`, then the restricted HKT
automorphism commutes with conjugation by that lift on the abelian lower layer.
-/
public theorem hkt_invariantSubgroupAut_commute_conjNormal_of_lift_fixed_mod
    {Q : Type u} [Group Q] (φ : MulAut Q)
    (N : Subgroup Q) [N.Normal] [IsMulCommutative N]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (a : Q) (ha_mod_N : φ a * a⁻¹ ∈ N) :
    invariantSubgroupAut φ N hNφ * MulAut.conjNormal (H := N) a =
      MulAut.conjNormal (H := N) a * invariantSubgroupAut φ N hNφ := by
  let α : MulAut N := invariantSubgroupAut φ N hNφ
  let β : MulAut N := MulAut.conjNormal (H := N) a
  change α * β = β * α
  ext x
  let c : Q := φ a * a⁻¹
  have hcN : c ∈ N := by simpa [c] using ha_mod_N
  have hφxN : φ (x : Q) ∈ N := (hNφ (x : Q)).mp x.2
  let y : Q := a * φ (x : Q) * a⁻¹
  have hyN : y ∈ N := by
    simpa [y] using (inferInstance : N.Normal).conj_mem (φ (x : Q)) hφxN a
  have hcy : c * y = y * c := by
    simpa [c, y] using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := N)).comm ⟨c, hcN⟩ ⟨y, hyN⟩)
  have hα_coe (z : N) : ((α z : N) : Q) = φ (z : Q) := by
    simpa [α] using invariantSubgroupAut_apply_coe φ N hNφ z
  have hβ_coe (z : N) : ((β z : N) : Q) = a * (z : Q) * a⁻¹ := by
    simp [β, MulAut.conjNormal_apply]
  have hφa : φ a = c * a := by
    simp [c, mul_assoc]
  have hleft :
      (((α * β) x : N) : Q) = φ (a * (x : Q) * a⁻¹) := by
    calc
      (((α * β) x : N) : Q)
          = φ (((β x : N) : Q)) := by
            simpa using hα_coe (β x)
      _ = φ (a * (x : Q) * a⁻¹) := by
            rw [hβ_coe x]
  have hφ_conj :
      φ (a * (x : Q) * a⁻¹) = c * y * c⁻¹ := by
    calc
      φ (a * (x : Q) * a⁻¹)
          = φ a * φ (x : Q) * (φ a)⁻¹ := by
            simp [map_mul, mul_assoc]
      _ = c * y * c⁻¹ := by
            rw [hφa]
            simp [y, mul_inv_rev, mul_assoc]
  have hright :
      (((β * α) x : N) : Q) = y := by
    calc
      (((β * α) x : N) : Q)
          = a * (((α x : N) : Q)) * a⁻¹ := by
            simpa using hβ_coe (α x)
      _ = y := by
            rw [hα_coe x]
  calc
    (((α * β) x : N) : Q)
        = φ (a * (x : Q) * a⁻¹) := hleft
    _ = c * y * c⁻¹ := hφ_conj
    _ = y := by
          calc
            c * y * c⁻¹ = y * c * c⁻¹ := by rw [hcy]
            _ = y := by simp [mul_assoc]
    _ = (((β * α) x : N) : Q) := hright.symm

/-- Coercion formula for powers of conjugation by a normalizing element. -/
public theorem hkt_conjNormal_pow_apply_coe
    {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal]
    (a : Q) :
    ∀ n (x : N),
      ((((MulAut.conjNormal (H := N) a) ^ n) x : N) : Q) =
        a ^ n * (x : Q) * (a ^ n)⁻¹ := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      calc
        ((((MulAut.conjNormal (H := N) a) ^ (n + 1)) x : N) : Q)
            = a * ((((MulAut.conjNormal (H := N) a) ^ n) x : N) : Q) * a⁻¹ := by
              simp [pow_succ', MulAut.conjNormal_apply, mul_assoc]
        _ = a * (a ^ n * (x : Q) * (a ^ n)⁻¹) * a⁻¹ := by
              rw [ih x]
        _ = a ^ (n + 1) * (x : Q) * (a ^ (n + 1))⁻¹ := by
              simp [pow_succ', mul_inv_rev, mul_assoc]

/-- If `aN` has `p`-th power trivial in the quotient, then conjugation by `a`
has `p`-th power trivial on an abelian normal subgroup `N`. -/
public theorem hkt_conjNormal_pow_eq_one_of_lift_pow_mem
    {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal] [IsMulCommutative N]
    (a : Q) {p : ℕ} (hapN : a ^ p ∈ N) :
    (MulAut.conjNormal (H := N) a) ^ p = 1 := by
  ext x
  have hpow :
      ((((MulAut.conjNormal (H := N) a) ^ p) x : N) : Q) =
        a ^ p * (x : Q) * (a ^ p)⁻¹ :=
    hkt_conjNormal_pow_apply_coe N a p x
  have hcomm : a ^ p * (x : Q) = (x : Q) * a ^ p := by
    simpa using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := N)).comm ⟨a ^ p, hapN⟩ x)
  calc
    ((((MulAut.conjNormal (H := N) a) ^ p) x : N) : Q)
        = a ^ p * (x : Q) * (a ^ p)⁻¹ := hpow
    _ = (x : Q) := by
          calc
            a ^ p * (x : Q) * (a ^ p)⁻¹ =
                (x : Q) * a ^ p * (a ^ p)⁻¹ := by rw [hcomm]
            _ = (x : Q) := by simp [mul_assoc]

/-- `MulAut.conjNormal` is a monoid hom, so integer powers of a lift induce
the corresponding integer powers of the conjugation automorphism. -/
public theorem hkt_conjNormal_zpow_eq
    {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal] (a : Q) (n : ℤ) :
    MulAut.conjNormal (H := N) (a ^ n) =
      (MulAut.conjNormal (H := N) a) ^ n := by
  exact (MulAut.conjNormal (H := N)).map_zpow a n

/-- If a lift is fixed modulo `N` by `φ`, then every integer power of the lift
is also fixed modulo `N`. -/
public theorem hkt_lift_zpow_mod_mem
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q) [N.Normal]
    (a : Q) (n : ℤ) (ha_mod_N : φ a * a⁻¹ ∈ N) :
    φ (a ^ n) * (a ^ n)⁻¹ ∈ N := by
  have hquot_a :
      QuotientGroup.mk' N (φ a) = QuotientGroup.mk' N a := by
    change (φ a : Q ⧸ N) = (a : Q ⧸ N)
    rw [QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv] using ha_mod_N
  have hquot :
      QuotientGroup.mk' N (φ (a ^ n)) = QuotientGroup.mk' N (a ^ n) := by
    calc
      QuotientGroup.mk' N (φ (a ^ n)) =
          QuotientGroup.mk' N ((φ a) ^ n) := by
        rw [map_zpow]
      _ = (QuotientGroup.mk' N (φ a)) ^ n := by
        rw [map_zpow]
      _ = (QuotientGroup.mk' N a) ^ n := by
        rw [hquot_a]
      _ = QuotientGroup.mk' N (a ^ n) := by
        rw [map_zpow]
  have hdiv : φ (a ^ n) / (a ^ n) ∈ N := by
    rw [← QuotientGroup.eq_iff_div_mem]
    exact hquot
  simpa [div_eq_mul_inv] using hdiv

/-- If the order of an automorphism divides the prime `p`, then the cyclic
subgroup it generates is a finite `p`-group. -/
public theorem hkt_zpowers_isPGroup_of_orderOf_dvd_prime
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (ψ : MulAut G) (hψ_dvd : orderOf ψ ∣ p) :
    IsPGroup p (Subgroup.zpowers ψ) := by
  have hcard_dvd : Nat.card (Subgroup.zpowers ψ) ∣ p := by
    simpa [Nat.card_zpowers] using hψ_dvd
  rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd
      (Nat.card (Subgroup.zpowers ψ)) hcard_dvd with hcard_one | hcard_p
  · exact IsPGroup.of_card (p := p) (G := Subgroup.zpowers ψ) (n := 0) (by
      simp [hcard_one])
  · exact IsPGroup.of_card (p := p) (G := Subgroup.zpowers ψ) (n := 1) (by
      simp [hcard_p])

/-- Same-characteristic fixed-point extraction for the quotient layer.  When
the quotient elementary prime equals the automorphism prime, the cyclic group
generated by the induced quotient automorphism is a `p`-group acting on a
nontrivial finite `p`-group, so its fixed-point subgroup is nontrivial. -/
public theorem hkt_same_prime_quotient_fixedPointSubgroup_ne_bot
    {Q : Type u} [Group Q] [Finite Q] {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime]
    (N : Subgroup Q) [N.Normal]
    [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (ψ : MulAut (Q ⧸ N))
    (hrp : r = p)
    (hψ_pgroup : IsPGroup p (Subgroup.zpowers ψ)) :
    fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) ≠ ⊥ := by
  have hquot_p_r : IsPGroup r (Q ⧸ N) :=
    IsElementaryAbelian.isPGroup r (Q ⧸ N)
  have hquot_p : IsPGroup p (Q ⧸ N) := by
    simpa [hrp] using hquot_p_r
  have hp_dvd_card : p ∣ Nat.card (Q ⧸ N) := by
    obtain ⟨n, hnpos, hcard⟩ :=
      (IsPGroup.nontrivial_iff_card (p := p) (G := Q ⧸ N) (hG := hquot_p)).mp
        (inferInstance : Nontrivial (Q ⧸ N))
    rw [hcard]
    exact dvd_pow_self p (ne_of_gt hnpos)
  have hone_fixed :
      (1 : Q ⧸ N) ∈ MulAction.fixedPoints (Subgroup.zpowers ψ) (Q ⧸ N) := by
    simp [MulAction.mem_fixedPoints]
  obtain ⟨x, hx_fixed, hx_ne_one_left⟩ :=
    hψ_pgroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := Q ⧸ N) hp_dvd_card hone_fixed
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ?_
  refine ⟨⟨x, ?_⟩, ?_⟩
  · simpa [fixedPointSubgroup, FixedPoints.mem_subgroup] using
      MulAction.mem_fixedPoints.mp hx_fixed
  · intro hx_one
    exact hx_ne_one_left (by
      simpa using (congrArg Subtype.val hx_one).symm)

/-- Fixed points of a commutative operator group are invariant under that same
operator group. -/
public theorem hkt_fixedPointSubgroup_invariant_of_commutative_operators
    {A G : Type u} [Group A] [Group G] [MulDistribMulAction A G]
    [IsMulCommutative A] :
    IsInvariant A G (fixedPointSubgroup A G) := by
  refine ⟨?_⟩
  intro a x
  constructor
  · intro hx
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx ⊢
    intro b
    calc
      b • (a • x) = a • (b • x) := by
        rw [← mul_smul, ← mul_smul, (IsMulCommutative.is_comm (M := A)).comm b a]
      _ = a • x := by rw [hx b]
  · intro hx
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx ⊢
    intro b
    have hx' := hx b
    have hcalc : a • (b • x) = a • x := by
      calc
        a • (b • x) = b • (a • x) := by
          rw [← mul_smul, ← mul_smul, (IsMulCommutative.is_comm (M := A)).comm a b]
        _ = a • x := hx'
    exact (MulAction.injective a) hcalc

/-- In the maximal quotient chief layer, a nontrivial fixed-point subgroup for
the induced cyclic automorphism must be the whole quotient. -/
public theorem hkt_quotient_fixedPointSubgroup_eq_top_of_ne_bot
    {Q : Type u} [Group Q] (φ : MulAut Q)
    (N : Subgroup Q) [N.Normal]
    [IsMulCommutative (Q ⧸ N)]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hNmax :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        N ≤ K → K ≠ ⊤ → K = N)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hfixed_ne_bot :
      fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) ≠ ⊥) :
    fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊤ := by
  let C : Subgroup (Q ⧸ N) := fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N)
  have hC_normal : C.Normal := by
    exact Subgroup.normal_of_isMulCommutative C
  have hC_invariant_ψ :
      IsInvariant (Subgroup.zpowers ψ) (Q ⧸ N) C := by
    haveI : IsMulCommutative (Subgroup.zpowers ψ) :=
      Subgroup.zpowers_isMulCommutative ψ
    simpa [C] using
      hkt_fixedPointSubgroup_invariant_of_commutative_operators
        (A := Subgroup.zpowers ψ) (G := Q ⧸ N)
  have hC_invariant_hkt :
      IsInvariant (Subgroup.zpowers (invariantQuotientAut φ N hNφ)) (Q ⧸ N) C := by
    subst hψ
    exact hC_invariant_ψ
  exact
    hkt_quotient_no_proper_nontrivial_invariant_normal
      φ N hNφ hNmax C hC_normal hC_invariant_hkt hfixed_ne_bot

/-- If every quotient element is fixed by the induced cyclic automorphism,
then the maximal quotient chief layer is cyclic. -/
public theorem hkt_quotient_isCyclic_of_fixedPointSubgroup_eq_top
    {Q : Type u} [Group Q] (φ : MulAut Q)
    (N : Subgroup Q) [N.Normal]
    [Nontrivial (Q ⧸ N)] [IsMulCommutative (Q ⧸ N)]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hNmax :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        N ≤ K → K ≠ ⊤ → K = N)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hfixed_top :
      fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊤) :
    IsCyclic (Q ⧸ N) := by
  classical
  obtain ⟨x, hx_ne_one⟩ := exists_ne (1 : Q ⧸ N)
  let L : Subgroup (Q ⧸ N) := Subgroup.zpowers x
  have hL_normal : L.Normal := by
    exact Subgroup.normal_of_isMulCommutative L
  have hLφψ : ∀ y : Q ⧸ N, y ∈ L ↔ ψ y ∈ L := by
    intro y
    have hy_fixed : ψ y = y := by
      have hy_mem :
          y ∈ fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) := by
        simp [hfixed_top]
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hy_mem
      simpa [MulAut.smul_def] using hy_mem ⟨ψ, Subgroup.mem_zpowers ψ⟩
    simp [hy_fixed]
  have hL_invariant_ψ :
      IsInvariant (Subgroup.zpowers ψ) (Q ⧸ N) L :=
    hkt_zpowers_invariant_of_generator ψ L hLφψ
  have hL_invariant_hkt :
      IsInvariant (Subgroup.zpowers (invariantQuotientAut φ N hNφ)) (Q ⧸ N) L := by
    subst hψ
    exact hL_invariant_ψ
  have hL_ne_bot : L ≠ ⊥ := by
    intro hLbot
    have hx_mem : x ∈ L := Subgroup.mem_zpowers x
    have hx_bot : x ∈ (⊥ : Subgroup (Q ⧸ N)) := by
      simpa [hLbot] using hx_mem
    exact hx_ne_one (Subgroup.mem_bot.mp hx_bot)
  have hL_top : L = ⊤ :=
    hkt_quotient_no_proper_nontrivial_invariant_normal
      φ N hNφ hNmax L hL_normal hL_invariant_hkt hL_ne_bot
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨x, hL_top⟩

/-- If every ambient element induces the trivial conjugation automorphism on
the normal lower layer, then the whole group centralizes that layer.  This is
the final formal bridge after Huppert's `M(Q)` calculation has proved that the
quotient conjugation action is trivial. -/
public theorem hkt_centralizer_eq_top_of_conjNormal_trivial
    {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal]
    (htriv : ∀ q : Q, MulAut.conjNormal (H := N) q = 1) :
    Subgroup.centralizer (N : Set Q) = ⊤ := by
  apply eq_top_iff.mpr
  intro q _hq
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hfix :
      (MulAut.conjNormal (H := N) q) ⟨n, hn⟩ = ⟨n, hn⟩ := by
    rw [htriv q]
    rfl
  have hconj : q * n * q⁻¹ = n := by
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using congrArg Subtype.val hfix
  have hmul := congrArg (fun t : Q => t * q) hconj
  simpa [mul_assoc] using hmul.symm

/-- Elements of an abelian normal subgroup act trivially by conjugation on
that subgroup.  This is the kernel calculation needed to factor the ambient
conjugation action through `Q ⧸ N`. -/
public theorem hkt_conjNormal_eq_one_of_mem_of_comm
    {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal]
    [IsMulCommutative N] {n : Q} (hn : n ∈ N) :
    MulAut.conjNormal (H := N) n = 1 := by
  ext x
  have hcomm :
      n * (x : Q) = (x : Q) * n := by
    simpa using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := N)).comm ⟨n, hn⟩ x)
  calc
    ((MulAut.conjNormal (H := N) n x : N) : Q)
        = n * (x : Q) * n⁻¹ := by
          simp [MulAut.conjNormal_apply]
    _ = (x : Q) * n * n⁻¹ := by rw [hcomm]
    _ = ((1 : MulAut N) x : N) := by simp [mul_assoc]

/-- The conjugation action of `Q` on an abelian normal subgroup `N` factors
through `Q ⧸ N`. -/
@[expose] public def quotientConjNormal
    {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal]
    [IsMulCommutative N] :
    Q ⧸ N →* MulAut N :=
  QuotientGroup.lift N (MulAut.conjNormal (H := N)) (by
    intro n hn
    exact hkt_conjNormal_eq_one_of_mem_of_comm N hn)

public theorem quotientConjNormal_mk'
    {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal]
    [IsMulCommutative N] (q : Q) :
    quotientConjNormal N (QuotientGroup.mk' N q) =
      MulAut.conjNormal (H := N) q := by
  rfl

/-- The ambient period of `φ` restricts to the same period on any invariant
subgroup. -/
public theorem invariantSubgroupAut_pow_eq_one_of_period
    {Q : Type u} [Group Q] (φ : MulAut Q) {p : ℕ}
    (N : Subgroup Q) (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hperiod : (fun q : Q => φ q)^[p] = id) :
    (invariantSubgroupAut φ N hNφ) ^ p = 1 := by
  apply hkt_mulAut_pow_eq_one_of_function_period
  funext n
  apply Subtype.ext
  have hn := congrFun hperiod (n : Q)
  simpa [invariantSubgroupAut_iterate_coe φ N hNφ p n] using hn

/-- Compatibility between the quotient action induced by `φ` and the
conjugation action on the lower normal layer.  Acting on the quotient by
`φ^k` conjugates the quotient-conjugation representation by the restricted
automorphism on `N`. -/
public theorem quotientConjNormal_invariant_npow_conj
    {Q : Type u} [Group Q] (φ : MulAut Q)
    (N : Subgroup Q) [N.Normal] [IsMulCommutative N]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N) (k : ℕ) :
    (quotientConjNormal N).comp
        (((invariantQuotientAut φ N hNφ) ^ k).toMonoidHom) =
      (MulAut.conj ((invariantSubgroupAut φ N hNφ) ^ k)).toMonoidHom.comp
        (quotientConjNormal N) := by
  apply MonoidHom.ext
  intro x
  ext n
  rcases QuotientGroup.mk'_surjective N x with ⟨q, rfl⟩
  let α : MulAut N := invariantSubgroupAut φ N hNφ
  let β : MulAut (Q ⧸ N) := invariantQuotientAut φ N hNφ
  let δ : MulAut Q := φ ^ k
  have hαcoe : ∀ m : N, (((α ^ k) m : N) : Q) = δ (m : Q) := by
    intro m
    calc
      (((α ^ k) m : N) : Q)
          = (((fun m : N => α m)^[k] m : N) : Q) := by
              rw [hkt_mulAut_pow_apply_iterate]
      _ = (fun q : Q => φ q)^[k] (m : Q) := by
              simpa [α] using invariantSubgroupAut_iterate_coe φ N hNφ k m
      _ = δ (m : Q) := by
              simpa [δ] using (hkt_mulAut_pow_apply_iterate φ k (m : Q)).symm
  have hαinv : ∀ m : N, δ (((α ^ k)⁻¹ m : N) : Q) = (m : Q) := by
    intro m
    have hm := hαcoe (((α ^ k)⁻¹) m)
    simpa using hm.symm
  have hβmk :
      (β ^ k) (QuotientGroup.mk' N q) = QuotientGroup.mk' N (δ q) := by
    calc
      (β ^ k) (QuotientGroup.mk' N q)
          = (fun x : Q ⧸ N => β x)^[k] (QuotientGroup.mk' N q) := by
              rw [hkt_mulAut_pow_apply_iterate]
      _ = QuotientGroup.mk' N ((fun q : Q => φ q)^[k] q) := by
              simpa [β] using invariantQuotientAut_iterate_mk' φ N hNφ k q
      _ = QuotientGroup.mk' N (δ q) := by
              simpa [δ] using congrArg (QuotientGroup.mk' N)
                (hkt_mulAut_pow_apply_iterate φ k q).symm
  calc
    ((quotientConjNormal N (((invariantQuotientAut φ N hNφ) ^ k)
        (QuotientGroup.mk' N q)) n : N) : Q)
        = ((MulAut.conjNormal (H := N) (δ q) n : N) : Q) := by
            rw [show ((invariantQuotientAut φ N hNφ) ^ k)
                (QuotientGroup.mk' N q) = QuotientGroup.mk' N (δ q) by
                  simpa [β] using hβmk]
            rw [quotientConjNormal_mk']
    _ = δ q * (n : Q) * (δ q)⁻¹ := by
            simp [MulAut.conjNormal_apply]
    _ = δ (q * (((α ^ k)⁻¹ n : N) : Q) * q⁻¹) := by
            have hn : (n : Q) = δ (((α ^ k)⁻¹ n : N) : Q) := (hαinv n).symm
            simp [map_mul, hn, mul_assoc]
    _ = (((α ^ k)
          (MulAut.conjNormal (H := N) q (((α ^ k)⁻¹) n)) : N) : Q) := by
            rw [hαcoe]
            simp [MulAut.conjNormal_apply]
    _ = ((((MulAut.conj (α ^ k))
          (quotientConjNormal N (QuotientGroup.mk' N q))) n : N) : Q) := by
            rw [quotientConjNormal_mk']
            rfl

/-- `ZMod p` form of the quotient/lower-layer action compatibility needed by
`SemidirectProduct.lift`. -/
public theorem quotientConjNormal_zmod_compat
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    [Fact p.Prime]
    (N : Subgroup Q) [N.Normal] [IsMulCommutative N]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hcard : Nat.card (Subgroup.zpowers ψ) = p)
    (g : Multiplicative (ZMod p)) :
    (quotientConjNormal N).comp
        ((zmodZPowersMulAutHom ψ hcard g).toMonoidHom) =
      (MulAut.conj
          (zmodPeriodMulAutHom
            (invariantSubgroupAut φ N hNφ)
            (invariantSubgroupAut_pow_eq_one_of_period φ N hNφ hperiod) g)).toMonoidHom.comp
        (quotientConjNormal N) := by
  classical
  subst hψ
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  obtain ⟨i, hg⟩ :
      ∃ i : ℕ, g = Multiplicative.ofAdd ((i : ℕ) : ZMod p) := by
    let z : ZMod p := Multiplicative.toAdd g
    have hgz : g = Multiplicative.ofAdd z := by
      cases g
      rfl
    rcases ZMod.natCast_zmod_surjective z with ⟨i, hi⟩
    exact ⟨i, by rw [hgz, ← hi]⟩
  rw [hg]
  let α : MulAut N := invariantSubgroupAut φ N hNφ
  let β : MulAut (Q ⧸ N) := invariantQuotientAut φ N hNφ
  let hαp : α ^ p = 1 := by
    simpa [α] using invariantSubgroupAut_pow_eq_one_of_period φ N hNφ hperiod
  have hquot :
      zmodZPowersMulAutHom β hcard (Multiplicative.ofAdd ((i : ℕ) : ZMod p)) =
        β ^ i := by
    simpa [β] using
      zmodZPowersMulAutHom_apply_ofAdd_intCast
        (invariantQuotientAut φ N hNφ) hcard (i : ℤ)
  have hlower :
      zmodPeriodMulAutHom α hαp (Multiplicative.ofAdd ((i : ℕ) : ZMod p)) =
        α ^ i := by
    simpa [α, hαp] using
      zmodPeriodMulAutHom_apply_ofAdd_intCast
        (invariantSubgroupAut φ N hNφ)
        (invariantSubgroupAut_pow_eq_one_of_period φ N hNφ hperiod)
        (i : ℤ)
  rw [hquot, hlower]
  exact quotientConjNormal_invariant_npow_conj φ N hNφ i

/-- The semidirect-product action on the lower layer used in Huppert's
Frobenius double-count: the quotient kernel acts by quotient conjugation, and
the cyclic complement acts by the restricted HKT automorphism. -/
@[expose]
public noncomputable def huppertMQSemidirectMulAutHom
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    [Fact p.Prime]
    (N : Subgroup Q) [N.Normal] [IsMulCommutative N]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hcard : Nat.card (Subgroup.zpowers ψ) = p) :
    (Q ⧸ N) ⋊[zmodZPowersMulAutHom ψ hcard] Multiplicative (ZMod p) →*
      MulAut N :=
  SemidirectProduct.lift
    (quotientConjNormal N)
    (zmodPeriodMulAutHom
      (invariantSubgroupAut φ N hNφ)
      (invariantSubgroupAut_pow_eq_one_of_period φ N hNφ hperiod))
    (quotientConjNormal_zmod_compat φ N hNφ hperiod ψ hψ hcard)

public theorem huppertMQSemidirectMulAutHom_inl
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    [Fact p.Prime]
    (N : Subgroup Q) [N.Normal] [IsMulCommutative N]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hcard : Nat.card (Subgroup.zpowers ψ) = p)
    (x : Q ⧸ N) :
    huppertMQSemidirectMulAutHom φ N hNφ hperiod ψ hψ hcard
        (SemidirectProduct.inl
          (φ := zmodZPowersMulAutHom ψ hcard) x) =
      quotientConjNormal N x := by
  simp [huppertMQSemidirectMulAutHom]

public theorem huppertMQSemidirectMulAutHom_inr
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    [Fact p.Prime]
    (N : Subgroup Q) [N.Normal] [IsMulCommutative N]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hcard : Nat.card (Subgroup.zpowers ψ) = p)
    (g : Multiplicative (ZMod p)) :
    huppertMQSemidirectMulAutHom φ N hNφ hperiod ψ hψ hcard
        (SemidirectProduct.inr
          (φ := zmodZPowersMulAutHom ψ hcard) g) =
      zmodPeriodMulAutHom
        (invariantSubgroupAut φ N hNφ)
        (invariantSubgroupAut_pow_eq_one_of_period φ N hNφ hperiod) g := by
  simp [huppertMQSemidirectMulAutHom]

public theorem semidirectRangeInl_card_ofHom
    {A B : Type*} [Group A] [Finite A] [Group B] (τ : B →* MulAut A) :
    Nat.card
      (MonoidHom.range
        (SemidirectProduct.inl :
          A →* A ⋊[τ] B)) =
      Nat.card A := by
  classical
  let e : A ≃ MonoidHom.range
      (SemidirectProduct.inl : A →* A ⋊[τ] B) :=
    { toFun := fun a =>
        ⟨SemidirectProduct.inl (φ := τ) a, ⟨a, rfl⟩⟩
      invFun := fun x => (x : A ⋊[τ] B).left
      left_inv := by
        intro a
        simp
      right_inv := by
        intro x
        rcases x.property with ⟨a, ha⟩
        apply Subtype.ext
        change
          SemidirectProduct.inl (φ := τ) ((x : A ⋊[τ] B).left) = (x : A ⋊[τ] B)
        rw [← ha]
        simp }
  exact Nat.card_congr e.symm

/-- Transport regularity from the prime cyclic subgroup generated by `ψ` to
the concrete `ZMod p` action used in the semidirect product. -/
public theorem actsRegularly_zmod_of_zpowers
    {A : Type u} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (ψ : MulAut A)
    (hcard : Nat.card (Subgroup.zpowers ψ) = p)
    (hregular : ActsRegularly (Subgroup.zpowers ψ) A) :
    letI : MulDistribMulAction (Multiplicative (ZMod p)) A :=
      MulDistribMulAction.compHom A (zmodZPowersMulAutHom ψ hcard)
    ActsRegularly (Multiplicative (ZMod p)) A := by
  classical
  letI : MulDistribMulAction (Multiplicative (ZMod p)) A :=
    MulDistribMulAction.compHom A (zmodZPowersMulAutHom ψ hcard)
  intro g hg
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  let e : Multiplicative (ZMod p) ≃* Subgroup.zpowers ψ :=
    zmodZPowersMulEquiv ψ hcard
  let a : Subgroup.zpowers ψ := e g
  have ha_ne : a ≠ 1 := by
    intro ha
    apply hg
    exact e.injective (by simpa [a] using ha)
  have hx_all :
      x ∈ fixedPointSubgroup (↥(Subgroup.zpowers a)) A := by
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro b
    rcases Subgroup.mem_zpowers_iff.mp b.property with ⟨k, hk⟩
    let z : Subgroup.zpowers g := ⟨g ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩⟩
    have hxz : z • x = x := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx
      exact hx z
    have hmap :
        zmodZPowersMulAutHom ψ hcard (z : Multiplicative (ZMod p)) =
          (b : Subgroup.zpowers ψ) := by
      change
        ((Subgroup.zpowers ψ).subtype.comp e.toMonoidHom) (g ^ k) =
          (b : Subgroup.zpowers ψ)
      rw [map_zpow]
      simpa [a] using congrArg (fun t : Subgroup.zpowers ψ => (t : MulAut A)) hk
    change ((b : Subgroup.zpowers ψ) : MulAut A) x = x
    have hxz' :
        zmodZPowersMulAutHom ψ hcard (z : Multiplicative (ZMod p)) x = x := by
      change zmodZPowersMulAutHom ψ hcard (z : Multiplicative (ZMod p)) x = x at hxz
      exact hxz
    rw [hmap] at hxz'
    simpa using hxz'
  have hx_bot : x ∈ (⊥ : Subgroup A) := by
    simpa [hregular a ha_ne] using hx_all
  simpa using hx_bot

/-- The Huppert norm/product `M_Q(n)` attached to the quotient conjugation
action on the lower abelian layer. -/
@[expose]
public noncomputable def huppertMQ
    {Q : Type u} [Group Q] [Finite Q] (N : Subgroup Q) [N.Normal]
    [IsMulCommutative N] (n : N) : N := by
  classical
  letI : CommGroup N := IsMulCommutative.instCommGroup
  letI : Fintype (Q ⧸ N) := Fintype.ofFinite _
  exact ∏ x : Q ⧸ N, quotientConjNormal N x n

/-- The kernel subgroup-sum in the semidirect representation is exactly the
additive form of Huppert's product `M_Q(n)`. -/
public theorem huppertMQSemidirect_kernel_subgroupSum_eq_huppertMQ
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p s : ℕ}
    [Fact p.Prime] [Fact s.Prime]
    (N : Subgroup Q) [N.Normal] [IsMulCommutative N]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hN_elem : IsElementaryAbelian s N)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hcard : Nat.card (Subgroup.zpowers ψ) = p)
    (n : N) :
    letI : CommGroup N := IsMulCommutative.instCommGroup
    let SD : Type u :=
      (Q ⧸ N) ⋊[zmodZPowersMulAutHom ψ hcard] Multiplicative (ZMod p)
    letI : Finite SD :=
      Finite.of_equiv ((Q ⧸ N) × Multiplicative (ZMod p))
        (SemidirectProduct.equivProd
          (φ := zmodZPowersMulAutHom ψ hcard)).symm
    letI : MulDistribMulAction SD N :=
      MulDistribMulAction.compHom N
        (huppertMQSemidirectMulAutHom φ N hNφ hperiod ψ hψ hcard)
    let K : Subgroup SD :=
      MonoidHom.range
        (SemidirectProduct.inl :
          Q ⧸ N →* SD)
    subgroupSum
        (Theory.Representation.ofElementaryAbelianAction (A := SD) (G := N) (p := s))
        K (Additive.ofMul n) =
      Additive.ofMul (huppertMQ N n) := by
  classical
  letI : CommGroup N := IsMulCommutative.instCommGroup
  letI : Fintype (Q ⧸ N) := Fintype.ofFinite _
  letI : MulDistribMulAction (Multiplicative (ZMod p)) (Q ⧸ N) :=
    MulDistribMulAction.compHom (Q ⧸ N) (zmodZPowersMulAutHom ψ hcard)
  let SD : Type u :=
    (Q ⧸ N) ⋊[zmodZPowersMulAutHom ψ hcard] Multiplicative (ZMod p)
  letI : Finite SD :=
    Finite.of_equiv ((Q ⧸ N) × Multiplicative (ZMod p))
      (SemidirectProduct.equivProd
        (φ := zmodZPowersMulAutHom ψ hcard)).symm
  letI : MulDistribMulAction SD N :=
    MulDistribMulAction.compHom N
      (huppertMQSemidirectMulAutHom φ N hNφ hperiod ψ hψ hcard)
  let K : Subgroup SD :=
    MonoidHom.range
      (SemidirectProduct.inl :
        Q ⧸ N →* SD)
  letI : Fintype K := Fintype.ofFinite K
  let ρ : Representation (ZMod s) SD (Additive N) :=
    Theory.Representation.ofElementaryAbelianAction (A := SD) (G := N) (p := s)
  let e : Q ⧸ N ≃ K :=
    { toFun := fun x =>
        ⟨SemidirectProduct.inl (φ := zmodZPowersMulAutHom ψ hcard) x, ⟨x, rfl⟩⟩
      invFun := fun x => (x : SD).left
      left_inv := by
        intro x
        simp
      right_inv := by
        intro x
        rcases x.property with ⟨a, ha⟩
        apply Subtype.ext
        change
          SemidirectProduct.inl (φ := zmodZPowersMulAutHom ψ hcard) ((x : SD).left) =
            (x : SD)
        rw [← ha]
        rfl }
  have hsum :
      (∑ k : K, ρ k (Additive.ofMul n)) =
        ∑ x : Q ⧸ N, ρ (e x) (Additive.ofMul n) := by
    exact
      (Fintype.sum_equiv e
        (fun x : Q ⧸ N => ρ (e x) (Additive.ofMul n))
        (fun k : K => ρ k (Additive.ofMul n))
        (by intro x; rfl)).symm
  have hsummand (x : Q ⧸ N) :
      ρ (e x) (Additive.ofMul n) =
        Additive.ofMul (quotientConjNormal N x n) := by
    dsimp [ρ, e]
    rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
    change
      Additive.ofMul
          ((huppertMQSemidirectMulAutHom φ N hNφ hperiod ψ hψ hcard)
            (SemidirectProduct.inl
              (φ := zmodZPowersMulAutHom ψ hcard) x) n) =
        Additive.ofMul (quotientConjNormal N x n)
    rw [huppertMQSemidirectMulAutHom_inl]
  calc
    subgroupSum ρ K (Additive.ofMul n)
        = ∑ k : K, ρ k (Additive.ofMul n) := by
            simpa [ρ, K] using subgroupSum_eq_sum ρ K (Additive.ofMul n)
    _ = ∑ x : Q ⧸ N, ρ (e x) (Additive.ofMul n) := hsum
    _ = ∑ x : Q ⧸ N, Additive.ofMul (quotientConjNormal N x n) := by
            exact Finset.sum_congr rfl (by intro x _hx; exact hsummand x)
    _ = Additive.ofMul (huppertMQ N n) := by
            simp [huppertMQ]

public theorem huppertMQSemidirect_kernel_card
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (N : Subgroup Q) [N.Normal]
    (ψ : MulAut (Q ⧸ N))
    (hcard : Nat.card (Subgroup.zpowers ψ) = p) :
    let SD : Type u :=
      (Q ⧸ N) ⋊[zmodZPowersMulAutHom ψ hcard] Multiplicative (ZMod p)
    letI : Finite SD :=
      Finite.of_equiv ((Q ⧸ N) × Multiplicative (ZMod p))
        (SemidirectProduct.equivProd
          (φ := zmodZPowersMulAutHom ψ hcard)).symm
    let K : Subgroup SD :=
      MonoidHom.range
        (SemidirectProduct.inl :
          Q ⧸ N →* SD)
    Nat.card K = Nat.card (Q ⧸ N) := by
  classical
  letI : Fintype (Q ⧸ N) := Fintype.ofFinite _
  letI : MulDistribMulAction (Multiplicative (ZMod p)) (Q ⧸ N) :=
    MulDistribMulAction.compHom (Q ⧸ N) (zmodZPowersMulAutHom ψ hcard)
  let SD : Type u :=
    (Q ⧸ N) ⋊[zmodZPowersMulAutHom ψ hcard] Multiplicative (ZMod p)
  letI : Finite SD :=
    Finite.of_equiv ((Q ⧸ N) × Multiplicative (ZMod p))
      (SemidirectProduct.equivProd
        (φ := zmodZPowersMulAutHom ψ hcard)).symm
  let K : Subgroup SD :=
    MonoidHom.range
      (SemidirectProduct.inl :
        Q ⧸ N →* SD)
  change Nat.card K = Nat.card (Q ⧸ N)
  exact semidirectRangeInl_card_ofHom (zmodZPowersMulAutHom ψ hcard)

public theorem huppertMQSemidirect_isFrobenius
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (N : Subgroup Q) [N.Normal] [Nontrivial (Q ⧸ N)]
    (ψ : MulAut (Q ⧸ N))
    (hcard : Nat.card (Subgroup.zpowers ψ) = p)
    (hregular : ActsRegularly (Subgroup.zpowers ψ) (Q ⧸ N)) :
    letI : MulDistribMulAction (Multiplicative (ZMod p)) (Q ⧸ N) :=
      MulDistribMulAction.compHom (Q ⧸ N) (zmodZPowersMulAutHom ψ hcard)
    let SD : Type u :=
      (Q ⧸ N) ⋊[zmodZPowersMulAutHom ψ hcard] Multiplicative (ZMod p)
    letI : Finite SD :=
      Finite.of_equiv ((Q ⧸ N) × Multiplicative (ZMod p))
        (SemidirectProduct.equivProd
          (φ := zmodZPowersMulAutHom ψ hcard)).symm
    let K : Subgroup SD :=
      MonoidHom.range
        (SemidirectProduct.inl :
          Q ⧸ N →* SD)
    let R : Subgroup SD :=
      MonoidHom.range
        (SemidirectProduct.inr :
          Multiplicative (ZMod p) →* SD)
    IsFrobeniusGroupWithKernelComplement K R := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  haveI : Nontrivial (Multiplicative (ZMod p)) := by infer_instance
  letI : MulDistribMulAction (Multiplicative (ZMod p)) (Q ⧸ N) :=
    MulDistribMulAction.compHom (Q ⧸ N) (zmodZPowersMulAutHom ψ hcard)
  let SD : Type u :=
    (Q ⧸ N) ⋊[zmodZPowersMulAutHom ψ hcard] Multiplicative (ZMod p)
  letI : Finite SD :=
    Finite.of_equiv ((Q ⧸ N) × Multiplicative (ZMod p))
      (SemidirectProduct.equivProd
        (φ := zmodZPowersMulAutHom ψ hcard)).symm
  let K : Subgroup SD :=
    MonoidHom.range
      (SemidirectProduct.inl :
        Q ⧸ N →* SD)
  let R : Subgroup SD :=
    MonoidHom.range
      (SemidirectProduct.inr :
        Multiplicative (ZMod p) →* SD)
  have hregular_zmod :
      ActsRegularly (Multiplicative (ZMod p)) (Q ⧸ N) :=
    actsRegularly_zmod_of_zpowers ψ hcard hregular
  have htoMulAut :
      MulDistribMulAction.toMulAut (Multiplicative (ZMod p)) (Q ⧸ N) =
        zmodZPowersMulAutHom ψ hcard := by
    ext g x
    rfl
  change IsFrobeniusGroupWithKernelComplement K R
  have hfrob :=
    hkt_regularSemidirect_isFrobenius
      (A := Q ⧸ N) (B := Multiplicative (ZMod p)) hregular_zmod
  rw [htoMulAut] at hfrob
  simpa [K, R, SD] using hfrob

public theorem hkt_sum_range_ofMul_eq_ofMul_prod
    {G : Type u} [CommGroup G] (f : ℕ → G) :
    ∀ n : ℕ,
      (∑ i ∈ Finset.range n, Additive.ofMul (f i)) =
        Additive.ofMul (∏ i ∈ Finset.range n, f i) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.prod_range_succ, ih]
      rfl

public theorem hkt_prod_range_eq_list_range_prod
    {G : Type u} [CommMonoid G] (f : ℕ → G) :
    ∀ n : ℕ,
      (∏ i ∈ Finset.range n, f i) = ((List.range n).map f).prod := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (∏ i ∈ Finset.range (n + 1), f i)
            = (∏ i ∈ Finset.range n, f i) * f n := by
                rw [Finset.prod_range_succ]
        _ = ((List.range n).map f).prod * f n := by rw [ih]
        _ = ((List.range (n + 1)).map f).prod := by
                rw [List.prod_range_succ]

public theorem zmodPeriod_sum_eq_zero_of_product_identity
    {G : Type u} [Group G] [Finite G] {p s : ℕ}
    [Fact p.Prime] [Fact s.Prime]
    (hG_elem : IsElementaryAbelian s G)
    (α : MulAut G)
    (hαp : α ^ p = 1)
    (hprod :
      ∀ g : G,
        ((List.range p).map (fun k ↦ (fun x : G => α x)^[k] g)).prod = 1)
    (g : G) :
    letI : CommGroup G := IsMulCommutative.instCommGroup
    letI : MulDistribMulAction (Multiplicative (ZMod p)) G :=
      MulDistribMulAction.compHom G (zmodPeriodMulAutHom α hαp)
    ∑ z : Multiplicative (ZMod p),
      (Theory.Representation.ofElementaryAbelianAction
        (A := Multiplicative (ZMod p)) (G := G) (p := s))
          z (Additive.ofMul g) = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  letI : CommGroup G := IsMulCommutative.instCommGroup
  letI : MulDistribMulAction (Multiplicative (ZMod p)) G :=
    MulDistribMulAction.compHom G (zmodPeriodMulAutHom α hαp)
  let ρ : Representation (ZMod s) (Multiplicative (ZMod p)) (Additive G) :=
    Theory.Representation.ofElementaryAbelianAction
      (A := Multiplicative (ZMod p)) (G := G) (p := s)
  let e : Fin p ≃ Multiplicative (ZMod p) :=
    (ZMod.finEquiv p).toEquiv.trans Multiplicative.ofAdd
  have hsum_fin :
      (∑ z : Multiplicative (ZMod p), ρ z (Additive.ofMul g)) =
        ∑ i : Fin p, ρ (e i) (Additive.ofMul g) := by
    exact
      (Fintype.sum_equiv e
        (fun i : Fin p => ρ (e i) (Additive.ofMul g))
        (fun z : Multiplicative (ZMod p) => ρ z (Additive.ofMul g))
        (by intro i; rfl)).symm
  have hfin_apply :
      (∑ i : Fin p, ρ (e i) (Additive.ofMul g)) =
        ∑ i : Fin p, Additive.ofMul ((α ^ (i : ℕ)) g) := by
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp [ρ, e]
    rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
    change
      Additive.ofMul
          ((zmodPeriodMulAutHom α hαp
            (Multiplicative.ofAdd ((ZMod.finEquiv p) i))) g) =
        Additive.ofMul ((α ^ (i : ℕ)) g)
    have happly :
        zmodPeriodMulAutHom α hαp
            (Multiplicative.ofAdd ((ZMod.finEquiv p) i)) =
          α ^ (i : ℕ) := by
      have hfin_eq : (ZMod.finEquiv p) i = ((i : ℕ) : ZMod p) := by
        have hfin_val : ((ZMod.finEquiv p) i).val = (i : ℕ) := by
          cases p with
          | zero =>
              exact (NeZero.ne 0 rfl).elim
          | succ n =>
              rfl
        rw [← ZMod.natCast_zmod_val ((ZMod.finEquiv p) i), hfin_val]
      rw [hfin_eq]
      simpa using
        zmodPeriodMulAutHom_apply_ofAdd_intCast α hαp ((i : ℕ) : ℤ)
    rw [happly]
  have hrange :
      (∑ i : Fin p, Additive.ofMul ((α ^ (i : ℕ)) g)) =
        ∑ i ∈ Finset.range p, Additive.ofMul ((α ^ i) g) := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => Additive.ofMul ((α ^ i) g)) p)
  have hprod_fin :
      (∏ i ∈ Finset.range p, (α ^ i) g) = 1 := by
    calc
      (∏ i ∈ Finset.range p, (α ^ i) g)
          = ((List.range p).map (fun i => (α ^ i) g)).prod := by
              exact hkt_prod_range_eq_list_range_prod (fun i => (α ^ i) g) p
      _ = ((List.range p).map (fun i ↦ (fun x : G => α x)^[i] g)).prod := by
              apply congrArg List.prod
              exact List.map_congr_left fun i _hi =>
                hkt_mulAut_pow_apply_iterate α i g
      _ = 1 := hprod g
  calc
    (∑ z : Multiplicative (ZMod p), ρ z (Additive.ofMul g))
        = ∑ i : Fin p, ρ (e i) (Additive.ofMul g) := hsum_fin
    _ = ∑ i : Fin p, Additive.ofMul ((α ^ (i : ℕ)) g) := hfin_apply
    _ = ∑ i ∈ Finset.range p, Additive.ofMul ((α ^ i) g) := hrange
    _ = Additive.ofMul (∏ i ∈ Finset.range p, (α ^ i) g) := by
          exact hkt_sum_range_ofMul_eq_ofMul_prod (fun i => (α ^ i) g) p
    _ = 0 := by
          simp [hprod_fin]

public theorem huppertMQSemidirect_complement_subgroupSum_eq_zero
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p s : ℕ}
    [Fact p.Prime] [Fact s.Prime]
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (N : Subgroup Q) [N.Normal] [IsMulCommutative N]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hN_elem : IsElementaryAbelian s N)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hcard : Nat.card (Subgroup.zpowers ψ) = p)
    (n : N) :
    letI : CommGroup N := IsMulCommutative.instCommGroup
    let SD : Type u :=
      (Q ⧸ N) ⋊[zmodZPowersMulAutHom ψ hcard] Multiplicative (ZMod p)
    letI : Finite SD :=
      Finite.of_equiv ((Q ⧸ N) × Multiplicative (ZMod p))
        (SemidirectProduct.equivProd
          (φ := zmodZPowersMulAutHom ψ hcard)).symm
    letI : MulDistribMulAction SD N :=
      MulDistribMulAction.compHom N
        (huppertMQSemidirectMulAutHom φ N hNφ hperiod ψ hψ hcard)
    let R : Subgroup SD :=
      MonoidHom.range
        (SemidirectProduct.inr :
          Multiplicative (ZMod p) →* SD)
    subgroupSum
        (Theory.Representation.ofElementaryAbelianAction (A := SD) (G := N) (p := s))
        R (Additive.ofMul n) =
      0 := by
  classical
  letI : CommGroup N := IsMulCommutative.instCommGroup
  letI : Fintype (Q ⧸ N) := Fintype.ofFinite _
  letI : MulDistribMulAction (Multiplicative (ZMod p)) (Q ⧸ N) :=
    MulDistribMulAction.compHom (Q ⧸ N) (zmodZPowersMulAutHom ψ hcard)
  let SD : Type u :=
    (Q ⧸ N) ⋊[zmodZPowersMulAutHom ψ hcard] Multiplicative (ZMod p)
  letI : Finite SD :=
    Finite.of_equiv ((Q ⧸ N) × Multiplicative (ZMod p))
      (SemidirectProduct.equivProd
        (φ := zmodZPowersMulAutHom ψ hcard)).symm
  letI : MulDistribMulAction SD N :=
    MulDistribMulAction.compHom N
      (huppertMQSemidirectMulAutHom φ N hNφ hperiod ψ hψ hcard)
  let R : Subgroup SD :=
    MonoidHom.range
      (SemidirectProduct.inr :
        Multiplicative (ZMod p) →* SD)
  letI : Fintype R := Fintype.ofFinite R
  let ρ : Representation (ZMod s) SD (Additive N) :=
    Theory.Representation.ofElementaryAbelianAction (A := SD) (G := N) (p := s)
  let e : Multiplicative (ZMod p) ≃ R :=
    { toFun := fun g =>
        ⟨SemidirectProduct.inr (φ := zmodZPowersMulAutHom ψ hcard) g, ⟨g, rfl⟩⟩
      invFun := fun x => (x : SD).right
      left_inv := by
        intro g
        simp
      right_inv := by
        intro x
        rcases x.property with ⟨g, hg⟩
        apply Subtype.ext
        change
          SemidirectProduct.inr (φ := zmodZPowersMulAutHom ψ hcard) ((x : SD).right) =
            (x : SD)
        rw [← hg]
        rfl }
  let α : MulAut N := invariantSubgroupAut φ N hNφ
  let hαp : α ^ p = 1 :=
    invariantSubgroupAut_pow_eq_one_of_period φ N hNφ hperiod
  letI : MulDistribMulAction (Multiplicative (ZMod p)) N :=
    MulDistribMulAction.compHom N (zmodPeriodMulAutHom α hαp)
  have hprodN :
      ∀ n : N,
        ((List.range p).map (fun k ↦ (fun x : N => α x)^[k] n)).prod = 1 := by
    simpa [α] using hkt_product_identity_of_invariant_subgroup φ N hNφ hprod
  have hsum :
      (∑ r : R, ρ r (Additive.ofMul n)) =
        ∑ g : Multiplicative (ZMod p), ρ (e g) (Additive.ofMul n) := by
    exact
      (Fintype.sum_equiv e
        (fun g : Multiplicative (ZMod p) => ρ (e g) (Additive.ofMul n))
        (fun r : R => ρ r (Additive.ofMul n))
        (by intro g; rfl)).symm
  have hsummand (g : Multiplicative (ZMod p)) :
      ρ (e g) (Additive.ofMul n) =
        Additive.ofMul ((zmodPeriodMulAutHom α hαp g) n) := by
    dsimp [ρ, e, α, hαp]
    rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
    change
      Additive.ofMul
          ((huppertMQSemidirectMulAutHom φ N hNφ hperiod ψ hψ hcard)
            (SemidirectProduct.inr
              (φ := zmodZPowersMulAutHom ψ hcard) g) n) =
        Additive.ofMul
          ((zmodPeriodMulAutHom
            (invariantSubgroupAut φ N hNφ)
            (invariantSubgroupAut_pow_eq_one_of_period φ N hNφ hperiod) g) n)
    rw [huppertMQSemidirectMulAutHom_inr]
  calc
    subgroupSum ρ R (Additive.ofMul n)
        = ∑ r : R, ρ r (Additive.ofMul n) := by
            simpa [ρ, R] using subgroupSum_eq_sum ρ R (Additive.ofMul n)
    _ = ∑ g : Multiplicative (ZMod p), ρ (e g) (Additive.ofMul n) := hsum
    _ = ∑ g : Multiplicative (ZMod p),
          Additive.ofMul ((zmodPeriodMulAutHom α hαp g) n) := by
            exact Finset.sum_congr rfl (by intro g _hg; exact hsummand g)
    _ = 0 := by
            have hzero :=
              zmodPeriod_sum_eq_zero_of_product_identity
                hN_elem α hαp hprodN n
            simp_rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul] at hzero
            have hsmul (g : Multiplicative (ZMod p)) :
                g • n = (zmodPeriodMulAutHom α hαp g) n := by
              rfl
            simpa only [hsmul] using hzero

/-- The quotient-conjugation norm is invariant under the quotient action.
This is the formal reindexing part of Huppert's `M(Q)` calculation. -/
public theorem huppertMQ_quotientConjNormal
    {Q : Type u} [Group Q] [Finite Q] (N : Subgroup Q) [N.Normal]
    [IsMulCommutative N] (x : Q ⧸ N) (n : N) :
    huppertMQ N (quotientConjNormal N x n) = huppertMQ N n := by
  classical
  letI : CommGroup N := IsMulCommutative.instCommGroup
  unfold huppertMQ
  letI : Fintype (Q ⧸ N) := Fintype.ofFinite _
  have hcomp : ∀ y : Q ⧸ N,
      quotientConjNormal N y (quotientConjNormal N x n) =
        quotientConjNormal N (y * x) n := by
    intro y
    calc
      quotientConjNormal N y (quotientConjNormal N x n)
          = (quotientConjNormal N y * quotientConjNormal N x) n := rfl
      _ = quotientConjNormal N (y * x) n := by
          rw [map_mul]
  calc
    (∏ y : Q ⧸ N,
        quotientConjNormal N y (quotientConjNormal N x n))
        = ∏ y : Q ⧸ N, quotientConjNormal N (y * x) n := by
          exact Fintype.prod_congr _ _ hcomp
    _ = ∏ y : Q ⧸ N, quotientConjNormal N y n := by
          simpa using
            (Fintype.prod_equiv (Equiv.mulRight x)
              (fun y : Q ⧸ N => quotientConjNormal N (y * x) n)
              (fun y : Q ⧸ N => quotientConjNormal N y n)
              (by intro y; rfl))

/-- Multiplicative `M_Q` is the additive representation norm for the
elementary-abelian quotient-conjugation action. -/
public theorem huppertMQ_eq_representation_norm
    {Q : Type u} [Group Q] [Finite Q] {s : ℕ} [Fact s.Prime]
    (N : Subgroup Q) [N.Normal] [IsMulCommutative N]
    (hN_elem : IsElementaryAbelian s N) (n : N) :
    letI : CommGroup N := IsMulCommutative.instCommGroup
    letI : Fintype (Q ⧸ N) := Fintype.ofFinite _
    letI : MulDistribMulAction (Q ⧸ N) N :=
      MulDistribMulAction.compHom N (quotientConjNormal N)
    Additive.ofMul (huppertMQ N n) =
      (Theory.Representation.ofElementaryAbelianAction (A := Q ⧸ N) (G := N) (p := s)).norm
        (Additive.ofMul n) := by
  classical
  letI : CommGroup N := IsMulCommutative.instCommGroup
  letI : Fintype (Q ⧸ N) := Fintype.ofFinite _
  letI : MulDistribMulAction (Q ⧸ N) N :=
    MulDistribMulAction.compHom N (quotientConjNormal N)
  unfold huppertMQ
  rw [Representation.norm]
  rw [LinearMap.sum_apply]
  simp_rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
  change
    (∑ i : Q ⧸ N, Additive.ofMul (((quotientConjNormal N) i) n)) =
      ∑ x : Q ⧸ N, Additive.ofMul (((quotientConjNormal N) x) n)
  rfl

/-- If Huppert's double count evaluates the norm as
`M_Q(n)=n^|Q/N|`, then the quotient conjugation action is trivial when the
lower and quotient elementary primes are distinct.  This keeps the source
double-count input separate from the elementary cancellation argument. -/
public theorem quotientConjNormal_trivial_of_huppertMQ_eval
    {Q : Type u} [Group Q] [Finite Q] {r s : ℕ}
    [Fact r.Prime] [Fact s.Prime]
    (N : Subgroup Q) [N.Normal]
    [IsMulCommutative N] [IsElementaryAbelian r (Q ⧸ N)]
    (hN_elem : IsElementaryAbelian s N)
    (hs_ne_r : s ≠ r)
    (hmq_eval : ∀ n : N, huppertMQ N n = n ^ Nat.card (Q ⧸ N)) :
    ∀ x : Q ⧸ N, quotientConjNormal N x = 1 := by
  classical
  letI : CommGroup N := IsMulCommutative.instCommGroup
  intro x
  ext n
  let m := Nat.card (Q ⧸ N)
  have hpow_eq :
      (quotientConjNormal N x n) ^ m = n ^ m := by
    calc
      (quotientConjNormal N x n) ^ m
          = huppertMQ N (quotientConjNormal N x n) := by
              simpa [m] using (hmq_eval (quotientConjNormal N x n)).symm
      _ = huppertMQ N n := huppertMQ_quotientConjNormal N x n
      _ = n ^ m := by
              simpa [m] using hmq_eval n
  let y : N := quotientConjNormal N x n * n⁻¹
  have hy_pow_m : y ^ m = 1 := by
    dsimp [y]
    simp [mul_pow, hpow_eq]
  have hy_pow_s : y ^ s = 1 := by
    simpa using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p s N) y)
  have hquot_p : IsPGroup r (Q ⧸ N) := IsElementaryAbelian.isPGroup r (Q ⧸ N)
  obtain ⟨k, hcard⟩ := hquot_p.exists_card_eq
  have hcop : Nat.Coprime s m := by
    dsimp [m]
    rw [hcard]
    simpa using
      (Nat.coprime_pow_primes 1 k
        (Fact.out : Nat.Prime s) (Fact.out : Nat.Prime r) hs_ne_r)
  have horder_m : orderOf y ∣ m := orderOf_dvd_of_pow_eq_one hy_pow_m
  have horder_s : orderOf y ∣ s := orderOf_dvd_of_pow_eq_one hy_pow_s
  have horder_one : orderOf y = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horder_s horder_m
  have hy_one : y = 1 := orderOf_eq_one_iff.mp horder_one
  have hmul := congrArg (fun t : N => t * n) hy_one
  simpa [y, mul_assoc] using hmul

end External
end CFSG.BenderSuzuki
