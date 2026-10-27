module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.theorem_7_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.corollary_9_2

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert IV basic group-theoretic helpers

Small reusable facts shared by several Huppert IV arguments.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v

/-- A subgroup is normal inside its own ambient normalizer. -/
public theorem hkt_subgroupOf_normalizer_normal
    {Q : Type u} [Group Q] (U : Subgroup Q) :
    (U.subgroupOf (Subgroup.normalizer (U : Set Q))).Normal := by
  let N : Subgroup Q := Subgroup.normalizer (U : Set Q)
  have hU_le_N : U ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := U))
  simpa [N] using
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := U) (K := N) hU_le_N).2
      (le_rfl : N ≤ Subgroup.normalizer (U : Set Q))

/-- A finite p-group has the trivial normal p-complement. -/
public theorem hkt_hasNormalPComplement_of_isPGroup
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hQp : IsPGroup p Q) :
    HasNormalPComplement p Q := by
  refine ⟨⊥, inferInstance, by simp, ?_⟩
  exact hQp.of_equiv (QuotientGroup.quotientBot (G := Q)).symm

public instance hkt_normal_subgroupOf_centralizer_normalizer
    {Q : Type u} [Group Q] (U : Subgroup Q) :
    ((Subgroup.centralizer (U : Set Q)).subgroupOf
      (Subgroup.normalizer (U : Set Q))).Normal := by
  rw [← U.normalizerMonoidHom_ker]
  infer_instance
/--
Frobenius IV.5.8(b), local algebraic bridge: if the normalizer of a `p`-
subgroup has a normal `p`-complement, then the normalizer-centralizer quotient
is a `p`-group.  The proof is the textbook line `[U,K] ≤ U ∩ K = 1`: the
normal complement `K` is normalized by `N_G(U)` and has order prime to `p`,
while `U` is a `p`-group inside the normalizer.
-/
public theorem hkt_normalizer_quotient_centralizer_isPGroup_of_hasNormalPComplement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (U : Subgroup Q) (hUp : IsPGroup q U)
    (hcomp : HasNormalPComplement q (↥(Subgroup.normalizer (U : Set Q)))) :
    IsPGroup q
      ((Subgroup.normalizer (U : Set Q)) ⧸
        ((Subgroup.centralizer (U : Set Q)).subgroupOf
          (Subgroup.normalizer (U : Set Q)))) := by
  classical
  let N : Subgroup Q := Subgroup.normalizer (U : Set Q)
  have hU_le_N : U ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := U))
  let UN : Subgroup N := U.subgroupOf N
  let C : Subgroup N := (Subgroup.centralizer (U : Set Q)).subgroupOf N
  let : C.Normal := by
    simpa [C, N] using
      (inferInstance :
        ((Subgroup.centralizer (U : Set Q)).subgroupOf
          (Subgroup.normalizer (U : Set Q))).Normal)
  rcases hcomp with ⟨K, hKnorm, hKcop, hquotp⟩
  have hUNnorm : UN.Normal := by
    simpa [UN, N] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer (H := U) (K := N) hU_le_N).2
        (le_rfl : N ≤ Subgroup.normalizer (U : Set Q))
  have hUNp : IsPGroup q UN := by
    simpa [UN] using
      hUp.of_equiv
        ((Subgroup.subgroupOfEquivOfLe (H := U) (K := N) hU_le_N).symm)
  have hinf_bot : UN ⊓ K = ⊥ := by
    rcases hUNp.exists_card_eq with ⟨n, hn⟩
    have hcop : Nat.Coprime (Nat.card UN) (Nat.card K) := by
      rw [hn]
      exact hKcop.pow_left n
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hcomm_bot : ⁅UN, K⁆ = ⊥ := by
    have hleft : ⁅UN, K⁆ ≤ UN := by
      let : UN.Normal := hUNnorm
      exact Subgroup.commutator_le_left (H₁ := UN) (H₂ := K)
    have hright : ⁅UN, K⁆ ≤ K := by
      let : K.Normal := hKnorm
      exact Subgroup.commutator_le_right (H₁ := UN) (H₂ := K)
    apply eq_bot_iff.mpr
    intro x hx
    have hxinf : x ∈ UN ⊓ K := ⟨hleft hx, hright hx⟩
    simpa [hinf_bot] using hxinf
  have hK_le_centUN : K ≤ Subgroup.centralizer (UN : Set N) := by
    have hcomm_K_UN : ⁅K, UN⁆ = ⊥ := by
      simpa [Subgroup.commutator_comm] using hcomm_bot
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := UN)).1
      hcomm_K_UN
  have hK_le_C : K ≤ C := by
    intro k hk
    change ((k : N) : Q) ∈ Subgroup.centralizer (U : Set Q)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    let uN : N := ⟨u, hU_le_N hu⟩
    have huN : uN ∈ UN := by
      change (uN : Q) ∈ U
      exact hu
    have hcommN : uN * (k : N) = (k : N) * uN :=
      (Subgroup.mem_centralizer_iff.mp (hK_le_centUN hk)) uN huN
    exact congrArg Subtype.val hcommN
  have hK_le_ker : K ≤ (QuotientGroup.mk' C).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (N := C) (x := x)).2 (hK_le_C hx)
  let ψ : N ⧸ K →* N ⧸ C :=
    QuotientGroup.lift K (QuotientGroup.mk' C) hK_le_ker
  have hψsurj : Function.Surjective ψ :=
    QuotientGroup.lift_surjective_of_surjective
      (N := K) (φ := QuotientGroup.mk' C)
      (QuotientGroup.mk'_surjective C) hK_le_ker
  exact hquotp.of_surjective ψ hψsurj

/-- Normalizing a subgroup normalizes the ambient image of any characteristic
subgroup of it. -/
public theorem hkt_normalizer_le_normalizer_map_subtype_of_characteristic
    {Q : Type u} [Group Q] (H : Subgroup Q) (K : Subgroup H)
    [K.Characteristic] :
    Subgroup.normalizer (H : Set Q) ≤
      Subgroup.normalizer (((K : Subgroup H).map H.subtype : Subgroup Q) : Set Q) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem ((K : Subgroup H).map H.subtype)
    (Subgroup.normalizer (H : Set Q)) ?_
  intro g x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set Q) := ⟨g, g.property⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxComap :
      xH ∈ Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K := by
    rw [hfix]
    exact hxK
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := hxComap
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩


/-- Inside the fixed Sylow subgroup, a proper subgroup has larger `q`-part in
its normalizer.  This is the numerical form of the normalizer condition used
in Huppert IV.6.2(b). -/
public theorem hkt_factorization_lt_normalizerIn_sylow_of_lt_sylow
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) {U : Subgroup Q} (hUS : U < (S : Subgroup Q)) :
    Nat.factorization (Nat.card U) q <
      Nat.factorization
        (Nat.card
          (Subgroup.normalizer
            ((U.subgroupOf (S : Subgroup Q)) : Set (S : Subgroup Q)))) q := by
  classical
  let K : Subgroup (S : Subgroup Q) := U.subgroupOf (S : Subgroup Q)
  have hKlt : K < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hKtop
    have hS_le_U : (S : Subgroup Q) ≤ U := by
      intro x hxS
      let xS : (S : Subgroup Q) := ⟨x, hxS⟩
      have hxK : xS ∈ K := by
        simp [hKtop]
      simpa [K, xS, Subgroup.mem_subgroupOf] using hxK
    exact (not_le_of_gt hUS) hS_le_U
  have hlt :=
    section8_factorization_lt_normalizer_of_lt_top_in_pgroup
      (S := (S : Subgroup Q)) (p := q)
      (hS := by simpa using S.isPGroup') (K := K) hKlt
  have hcardK : Nat.card K = Nat.card U :=
    natCard_subgroupOf_eq U (S : Subgroup Q) hUS.le
  simpa [K, hcardK] using hlt

/-- The normalizer of `U` inside the fixed Sylow subgroup maps into the ambient
normalizer of `U`. -/
public theorem sylow_subgroupOf_normalizer_map_le_normalizer
    {Q : Type u} [Group Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) {U : Subgroup Q} (hUS : U ≤ (S : Subgroup Q)) :
    (Subgroup.normalizer
        ((U.subgroupOf (S : Subgroup Q)) : Set (S : Subgroup Q))).map
      (S : Subgroup Q).subtype ≤ Subgroup.normalizer (U : Set Q) := by
  classical
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨n, hn, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hzU
    let zS : (S : Subgroup Q) := ⟨z, hUS hzU⟩
    have hzK : zS ∈ U.subgroupOf (S : Subgroup Q) := by
      simpa [zS, Subgroup.mem_subgroupOf] using hzU
    have hconjK :=
      (Subgroup.mem_normalizer_iff.mp hn zS).1 hzK
    simpa [zS, Subgroup.mem_subgroupOf] using hconjK
  · intro hzU
    have hzS : z ∈ (S : Subgroup Q) := by
      have hconjS : (n : Q) * z * (n : Q)⁻¹ ∈ (S : Subgroup Q) := hUS hzU
      have hback : (n : Q)⁻¹ * ((n : Q) * z * (n : Q)⁻¹) * (n : Q) ∈
          (S : Subgroup Q) := by
        exact (S : Subgroup Q).mul_mem
          ((S : Subgroup Q).mul_mem ((S : Subgroup Q).inv_mem n.property) hconjS)
          n.property
      simpa [mul_assoc] using hback
    let zS : (S : Subgroup Q) := ⟨z, hzS⟩
    have hzConjK : n * zS * n⁻¹ ∈ U.subgroupOf (S : Subgroup Q) := by
      simpa [zS, Subgroup.mem_subgroupOf] using hzU
    have hconjK :=
      (Subgroup.mem_normalizer_iff.mp hn zS).2 hzConjK
    simpa [zS, Subgroup.mem_subgroupOf] using hconjK

/-- If `U` is a proper subgroup of the fixed Sylow subgroup, then the ambient
normalizer of `U` has strictly larger `q`-part than `U` itself. -/
public theorem hkt_factorization_lt_ambient_normalizer_of_lt_sylow
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) {U : Subgroup Q} (hUS : U < (S : Subgroup Q)) :
    Nat.factorization (Nat.card U) q <
      Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q := by
  classical
  let K : Subgroup (S : Subgroup Q) := U.subgroupOf (S : Subgroup Q)
  let NS : Subgroup (S : Subgroup Q) := Subgroup.normalizer (K : Set (S : Subgroup Q))
  have hlt_internal :
      Nat.factorization (Nat.card U) q < Nat.factorization (Nat.card NS) q := by
    simpa [K, NS] using
      hkt_factorization_lt_normalizerIn_sylow_of_lt_sylow (S := S) hUS
  have hmap_card : Nat.card (NS.map (S : Subgroup Q).subtype) = Nat.card NS := by
    simpa [NS] using
      Subgroup.card_map_of_injective (K := NS) (f := (S : Subgroup Q).subtype)
        (S : Subgroup Q).subtype_injective
  have hmap_le :
      NS.map (S : Subgroup Q).subtype ≤ Subgroup.normalizer (U : Set Q) := by
    simpa [K, NS] using
      sylow_subgroupOf_normalizer_map_le_normalizer (S := S) (U := U) hUS.le
  have hle_ambient :
      Nat.factorization (Nat.card NS) q ≤
        Nat.factorization (Nat.card (Subgroup.normalizer (U : Set Q))) q := by
    rw [← hmap_card]
    exact Nat.factorization_le_factorization_of_dvd_right
      (Subgroup.card_dvd_of_le hmap_le) Nat.card_pos.ne' Nat.card_pos.ne'
  exact lt_of_lt_of_le hlt_internal hle_ambient


/-- If a subgroup of a quotient is nontrivial, then its full preimage is
strictly larger than the quotient kernel. -/
public theorem hkt_quotient_comap_card_gt_of_ne_bot
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (L : Subgroup (G ⧸ H)) (hL_ne_bot : L ≠ ⊥) :
    let K : Subgroup G := L.comap (QuotientGroup.mk' H)
    Nat.card H < Nat.card K := by
  classical
  intro K
  have hL_nontrivial : Nontrivial L :=
    (Subgroup.nontrivial_iff_ne_bot (H := L)).2 hL_ne_bot
  have hLcard : 1 < Nat.card L :=
    Finite.one_lt_card_iff_nontrivial.mpr hL_nontrivial
  have hK_card : Nat.card K = Nat.card H * Nat.card L := by
    change Nat.card (QuotientGroup.mk ⁻¹' (L : Set (G ⧸ H))) =
      Nat.card H * Nat.card L
    rw [← Nat.card_prod]
    exact Nat.card_congr
      (QuotientGroup.preimageMkEquivSubgroupProdSet H (L : Set (G ⧸ H)))
  calc
    Nat.card H < Nat.card H * Nat.card L :=
      lt_mul_of_one_lt_right Nat.card_pos hLcard
    _ = Nat.card K := hK_card.symm

/-- The preimage of `J(G/H)` is strictly larger than `H` when `G/H` is
nontrivial.  This is the counting half of the `J(P/U)` candidate in Huppert
IV.6.2(b). -/
public theorem hkt_thompson_quotient_comap_card_gt
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (hH_lt : Nat.card H < Nat.card G) :
    let Jbar : Subgroup (G ⧸ H) := thompsonSubgroup (G := G ⧸ H) ⊤
    let K : Subgroup G := Jbar.comap (QuotientGroup.mk' H)
    Nat.card H < Nat.card K := by
  classical
  intro Jbar K
  have hquot_nontrivial : Nontrivial (G ⧸ H) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have hHtop : H = ⊤ := QuotientGroup.subgroup_eq_top_of_subsingleton H hsub
    have hcardH : Nat.card H = Nat.card G := by
      rw [hHtop, Subgroup.card_top]
    rw [hcardH] at hH_lt
    exact (lt_irrefl (Nat.card G)) hH_lt
  have : Nontrivial (G ⧸ H) := hquot_nontrivial
  have hJ_ne_bot : Jbar ≠ ⊥ := by
    simpa [Jbar] using
      (section8_thompsonSubgroup_ne_bot_of_ne_bot
        (G := G ⧸ H) (S := (⊤ : Subgroup (G ⧸ H)))
        (top_ne_bot : (⊤ : Subgroup (G ⧸ H)) ≠ ⊥))
  exact hkt_quotient_comap_card_gt_of_ne_bot H Jbar hJ_ne_bot
/-- In a finite `p`-group, the preimage of the center of a nontrivial quotient
is strictly larger than the quotient kernel.  This is the formal counting step
behind Huppert IV.6.2(b)'s use of `Z(P/U)`. -/
public theorem hkt_center_quotient_comap_card_gt
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) [H.Normal] (hGp : IsPGroup p G)
    (hH_lt : Nat.card H < Nat.card G) :
    let Zbar : Subgroup (G ⧸ H) := Subgroup.center (G ⧸ H)
    let K : Subgroup G := Zbar.comap (QuotientGroup.mk' H)
    Nat.card H < Nat.card K := by
  classical
  intro Zbar K
  have hquot_nontrivial : Nontrivial (G ⧸ H) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have hHtop : H = ⊤ := QuotientGroup.subgroup_eq_top_of_subsingleton H hsub
    have hcardH : Nat.card H = Nat.card G := by
      rw [hHtop, Subgroup.card_top]
    rw [hcardH] at hH_lt
    exact (lt_irrefl (Nat.card G)) hH_lt
  have hquotp : IsPGroup p (G ⧸ H) := hGp.to_quotient H
  have : Nontrivial (G ⧸ H) := hquot_nontrivial
  have hZ_nontrivial : Nontrivial Zbar := by
    simpa [Zbar] using IsPGroup.center_nontrivial (p := p) hquotp
  have hZcard : 1 < Nat.card Zbar :=
    Finite.one_lt_card_iff_nontrivial.mpr hZ_nontrivial
  have hK_card : Nat.card K = Nat.card H * Nat.card Zbar := by
    change Nat.card (QuotientGroup.mk ⁻¹' (Zbar : Set (G ⧸ H))) =
      Nat.card H * Nat.card Zbar
    rw [← Nat.card_prod]
    exact Nat.card_congr
      (QuotientGroup.preimageMkEquivSubgroupProdSet H (Zbar : Set (G ⧸ H)))
  calc
    Nat.card H < Nat.card H * Nat.card Zbar :=
      lt_mul_of_one_lt_right Nat.card_pos hZcard
    _ = Nat.card K := hK_card.symm


/--
Huppert I.14.9(b), quaternion case, in relation form.  If `G` is generated
by a cyclic subgroup `<a>` of order `2 * k` and an element `b` satisfying
`a^z b = b a^{-z}` and `b^2 = a^k`, with the expected two-coset normal form,
then the resulting group is Mathlib's generalized quaternion group.
-/
public theorem huppert_I_14_9_generalizedQuaternion_mulEquiv_of_relations
    {G : Type u} [Group G] [Finite G] {k : ℕ} [NeZero k]
    (a b : G)
    (ha_order : orderOf a = 2 * k)
    (hconj : ∀ z : ℤ, a ^ z * b = b * a ^ (-z))
    (hb_mul_self : b * b = a ^ (k : ℤ))
    (hcover : ∀ g : G, ∃ i : ZMod (2 * k),
      g = a ^ (i.val : ℤ) ∨ g = b * a ^ (i.val : ℤ))
    (hcard : Nat.card G = 4 * k) :
    Nonempty (G ≃* QuaternionGroup k) := by
  classical
  have hpow_eq_of_eq_zmod :
      ∀ {r s : ℤ}, (r : ZMod (2 * k)) = (s : ZMod (2 * k)) → a ^ r = a ^ s := by
    intro r s hrs
    exact (zpow_eq_zpow_iff_modEq (x := a)).2 (by
      simpa [ha_order] using (ZMod.intCast_eq_intCast_iff r s (2 * k)).mp hrs)
  have hpow_add_val : ∀ i j : ZMod (2 * k),
      a ^ (((i + j).val : ℕ) : ℤ) = a ^ ((i.val : ℤ) + (j.val : ℤ)) := by
    intro i j
    apply hpow_eq_of_eq_zmod
    simp
  have hpow_sub_val : ∀ i j : ZMod (2 * k),
      a ^ (((j - i).val : ℕ) : ℤ) = a ^ ((j.val : ℤ) - (i.val : ℤ)) := by
    intro i j
    apply hpow_eq_of_eq_zmod
    simp
  have hpow_quaternion_twist_val : ∀ i j : ZMod (2 * k),
      a ^ ((((k : ZMod (2 * k)) + j - i).val : ℕ) : ℤ) =
        a ^ ((k : ℤ) + (j.val : ℤ) - (i.val : ℤ)) := by
    intro i j
    apply hpow_eq_of_eq_zmod
    simp
  let f : QuaternionGroup k →* G :=
    { toFun := fun q =>
        match q with
        | QuaternionGroup.a i => a ^ (i.val : ℤ)
        | QuaternionGroup.xa i => b * a ^ (i.val : ℤ)
      map_one' := by
        change a ^ (((0 : ZMod (2 * k)).val : ℕ) : ℤ) = 1
        simp
      map_mul' := by
        intro x y
        cases x with
        | a i =>
            cases y with
            | a j =>
                change a ^ (((i + j).val : ℕ) : ℤ) =
                  a ^ (i.val : ℤ) * a ^ (j.val : ℤ)
                calc
                  a ^ (((i + j).val : ℕ) : ℤ) = a ^ ((i.val : ℤ) + (j.val : ℤ)) :=
                    hpow_add_val i j
                  _ = a ^ (i.val : ℤ) * a ^ (j.val : ℤ) := by rw [zpow_add]
            | xa j =>
                change b * a ^ (((j - i).val : ℕ) : ℤ) =
                  a ^ (i.val : ℤ) * (b * a ^ (j.val : ℤ))
                calc
                  b * a ^ (((j - i).val : ℕ) : ℤ) =
                      b * a ^ ((j.val : ℤ) - (i.val : ℤ)) := by
                    rw [hpow_sub_val i j]
                  _ = b * a ^ (-(i.val : ℤ) + (j.val : ℤ)) := by ring_nf
                  _ = b * (a ^ (-(i.val : ℤ)) * a ^ (j.val : ℤ)) := by rw [zpow_add]
                  _ = (b * a ^ (-(i.val : ℤ))) * a ^ (j.val : ℤ) := by
                    group
                  _ = (a ^ (i.val : ℤ) * b) * a ^ (j.val : ℤ) := by
                    rw [← hconj (i.val : ℤ)]
                  _ = a ^ (i.val : ℤ) * (b * a ^ (j.val : ℤ)) := by
                    group
        | xa i =>
            cases y with
            | a j =>
                change b * a ^ (((i + j).val : ℕ) : ℤ) =
                  (b * a ^ (i.val : ℤ)) * a ^ (j.val : ℤ)
                calc
                  b * a ^ (((i + j).val : ℕ) : ℤ) =
                      b * a ^ ((i.val : ℤ) + (j.val : ℤ)) := by
                    rw [hpow_add_val i j]
                  _ = (b * a ^ (i.val : ℤ)) * a ^ (j.val : ℤ) := by
                    rw [zpow_add]
                    group
            | xa j =>
                change a ^ ((((k : ZMod (2 * k)) + j - i).val : ℕ) : ℤ) =
                  (b * a ^ (i.val : ℤ)) * (b * a ^ (j.val : ℤ))
                calc
                  a ^ ((((k : ZMod (2 * k)) + j - i).val : ℕ) : ℤ) =
                      a ^ ((k : ℤ) + (j.val : ℤ) - (i.val : ℤ)) :=
                    hpow_quaternion_twist_val i j
                  _ = a ^ ((k : ℤ) + (-(i.val : ℤ) + (j.val : ℤ))) := by ring_nf
                  _ = a ^ (k : ℤ) * (a ^ (-(i.val : ℤ)) * a ^ (j.val : ℤ)) := by
                    rw [zpow_add, zpow_add]
                  _ = (b * b) * (a ^ (-(i.val : ℤ)) * a ^ (j.val : ℤ)) := by
                    rw [hb_mul_self]
                  _ = (b * (a ^ (i.val : ℤ) * b)) * a ^ (j.val : ℤ) := by
                    rw [hconj (i.val : ℤ)]
                    group
                  _ = (b * a ^ (i.val : ℤ)) * (b * a ^ (j.val : ℤ)) := by
                    group }
  have hf_surj : Function.Surjective f := by
    intro g
    rcases hcover g with ⟨i, hgi | hgi⟩
    · exact ⟨QuaternionGroup.a i, hgi.symm⟩
    · exact ⟨QuaternionGroup.xa i, hgi.symm⟩
  have hf_bij : Function.Bijective f :=
    hf_surj.bijective_of_nat_card_le (by
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card, hcard])
  exact ⟨(MulEquiv.ofBijective f hf_bij).symm⟩
/-- Conjugation is inversion in the noncyclic cyclic-index-two case of Huppert I.14.9. -/
private theorem huppert_I_14_9_conj_inverts_of_cyclic_index_two
    {G : Type u} [Group G] [Finite G] {k : ℕ} [NeZero k]
    (A : Subgroup G) [A.Normal] (a b : G)
    (hA_eq : Subgroup.zpowers a = A)
    (hA_index : A.index = 2)
    (ha_order : orderOf a = 2 * k)
    (hb_not_mem : b ∉ A)
    (hunique_order_two : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y)
    (hnot_cyclic : ¬ IsCyclic G)
    (hcard : Nat.card G = 4 * k)
    (hGp : IsPGroup 2 G) :
    ∀ z : ℤ, a ^ z * b = b * a ^ (-z) := by
  have hcoverA : ∀ g : G, g ∈ A ∨ b⁻¹ * g ∈ A := by
    intro g
    by_cases hgA : g ∈ A
    · exact Or.inl hgA
    · have hiff := A.mul_mem_iff_of_index_two (by simpa using hA_index) (a := b⁻¹) (b := g)
      have hb_inv_not : b⁻¹ ∉ A := by
        intro hb_inv
        exact hb_not_mem (by simpa using A.inv_mem hb_inv)
      exact Or.inr (hiff.mpr (Iff.intro (fun hb => False.elim (hb_inv_not hb)) (fun hg => False.elim (hgA hg))))
  have hcover : ∀ g : G, ∃ i : ZMod (2 * k),
      g = a ^ (i.val : ℤ) ∨ g = b * a ^ (i.val : ℤ) := by
    intro g
    rcases hcoverA g with hgA | hbgA
    · rw [← hA_eq] at hgA
      rcases Subgroup.mem_zpowers_iff.mp hgA with ⟨z, hz⟩
      refine ⟨(z : ZMod (2 * k)), Or.inl ?_⟩
      calc
        g = a ^ z := hz.symm
        _ = a ^ (((z : ZMod (2 * k)).val : ℕ) : ℤ) := by
          apply (zpow_eq_zpow_iff_modEq (x := a)).2
          simpa [ha_order] using
            (ZMod.intCast_eq_intCast_iff z (((z : ZMod (2 * k)).val : ℕ) : ℤ) (2 * k)).mp (by simp)
    · rw [← hA_eq] at hbgA
      rcases Subgroup.mem_zpowers_iff.mp hbgA with ⟨z, hz⟩
      refine ⟨(z : ZMod (2 * k)), Or.inr ?_⟩
      calc
        g = b * (b⁻¹ * g) := by group
        _ = b * a ^ z := by rw [hz]
        _ = b * a ^ (((z : ZMod (2 * k)).val : ℕ) : ℤ) := by
          congr 1
          apply (zpow_eq_zpow_iff_modEq (x := a)).2
          simpa [ha_order] using
            (ZMod.intCast_eq_intCast_iff z (((z : ZMod (2 * k)).val : ℕ) : ℤ) (2 * k)).mp (by simp)
  have hb_sq_mem : b * b ∈ A := by
    simpa [pow_two] using A.sq_mem_of_index_two hA_index b
  have hb_sq_in_zpowers : b * b ∈ Subgroup.zpowers a := by
    simpa [hA_eq] using hb_sq_mem
  have ha_k_order_two : orderOf (a ^ (k : ℤ)) = 2 := by
    have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    have hnat : orderOf (a ^ k) = 2 := by
      rw [orderOf_pow, ha_order]
      rw [Nat.gcd_mul_left_left]
      rw [Nat.mul_comm 2 k]
      exact Nat.mul_div_right 2 hkpos
    simpa [zpow_natCast] using hnat
  have hA_card : Nat.card A = 2 * k := by
    have hmul : Nat.card A * A.index = Nat.card G := A.card_mul_index
    have hmul' : Nat.card A * 2 = 4 * k := by
      simpa [hA_index, hcard] using hmul
    have htarget : (2 * k) * 2 = 4 * k := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (hmul'.trans htarget.symm)
  have ha_k_mem_A : a ^ (k : ℤ) ∈ A := by
    rw [← hA_eq]
    exact Subgroup.zpow_mem_zpowers a (k : ℤ)
  have houtside_sq_ne_one : ∀ x : G, x ∉ A → x * x ≠ 1 := by
    intro x hxA hsq
    have hx_ne_one : x ≠ 1 := by
      intro hx
      exact hxA (by simp [hx])
    have hx_order : orderOf x = 2 := by
      have hpow : x ^ 2 = 1 := by simpa [pow_two] using hsq
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact False.elim (hx_ne_one (orderOf_eq_one_iff.mp h))
      · exact h
    have hx_eq_ak := hunique_order_two x (a ^ (k : ℤ)) hx_order ha_k_order_two
    exact hxA (by simpa [hx_eq_ak] using ha_k_mem_A)
  have hright_not_mem_A : ∀ z : ℤ, a ^ z * b ∉ A := by
    intro z hzA
    have haz : a ^ z ∈ A := by
      rw [← hA_eq]
      exact Subgroup.zpow_mem_zpowers a z
    have hbA : b ∈ A := by
      have hmul : (a ^ z)⁻¹ * (a ^ z * b) ∈ A := A.mul_mem (A.inv_mem haz) hzA
      simpa [mul_assoc] using hmul
    exact hb_not_mem hbA
  have hright_sq_ne_one : ∀ z : ℤ, (a ^ z * b) * (a ^ z * b) ≠ 1 := by
    intro z
    exact houtside_sq_ne_one (a ^ z * b) (hright_not_mem_A z)
  have hb_sq_ne_one : b * b ≠ 1 := by
    simpa using hright_sq_ne_one 0
  have ha_mem_A : a ∈ A := by
    rw [← hA_eq]
    exact Subgroup.mem_zpowers a
  have hbab_mem_A : b * a * b⁻¹ ∈ A := by
    exact (inferInstance : A.Normal).conj_mem a ha_mem_A b
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp (by
    simpa [hA_eq] using hbab_mem_A : b * a * b⁻¹ ∈ Subgroup.zpowers a)
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hb_sq_in_zpowers
  have hconj_a_zpow : ∀ z : ℤ, b * a ^ z * b⁻¹ = a ^ (r * z) := by
    intro z
    calc
      b * a ^ z * b⁻¹ = (b * a * b⁻¹) ^ z := (conj_zpow (a := b) (b := a) (i := z)).symm
      _ = (a ^ r) ^ z := by rw [hr]
      _ = a ^ (r * z) := by rw [zpow_mul]
  have hr_square_one : a ^ (r * r) = a := by
    calc
      a ^ (r * r) = b * a ^ r * b⁻¹ := (hconj_a_zpow r).symm
      _ = b * (b * a * b⁻¹) * b⁻¹ := by rw [hr]
      _ = (b * b) * a * (b * b)⁻¹ := by group
      _ = a := by
        rw [← hs]
        group
  have hs_fixed_by_r : a ^ (r * s) = a ^ s := by
    calc
      a ^ (r * s) = b * a ^ s * b⁻¹ := (hconj_a_zpow s).symm
      _ = b * (b * b) * b⁻¹ := by rw [hs]
      _ = b * b := by group
      _ = a ^ s := hs.symm
  have hAp : IsPGroup 2 A := hGp.to_subgroup A
  obtain ⟨M, hA_card_pow⟩ := hAp.exists_card_eq
  have ha_order_pow : orderOf a = 2 ^ M := by
    calc
      orderOf a = 2 * k := ha_order
      _ = Nat.card A := hA_card.symm
      _ = 2 ^ M := hA_card_pow
  have hright_square_formula : ∀ z : ℤ,
      (a ^ z * b) * (a ^ z * b) = a ^ ((1 + r) * z + s) := by
    intro z
    calc
      (a ^ z * b) * (a ^ z * b) =
          a ^ z * (b * a ^ z * b⁻¹) * (b * b) := by group
      _ = a ^ z * a ^ (r * z) * a ^ s := by rw [hconj_a_zpow z, ← hs]
      _ = a ^ (z + r * z) * a ^ s := by rw [← zpow_add]
      _ = a ^ ((1 + r) * z + s) := by
        rw [← zpow_add]
        ring_nf
  have hright_square_mod_ne_zero :
      ∀ z : ℤ, ¬ (((1 + r) * z + s) ≡ 0 [ZMOD (orderOf a : ℤ)]) := by
    intro z hz
    exact hright_sq_ne_one z (by
      rw [hright_square_formula z]
      have hpow0 : a ^ ((1 + r) * z + s) = a ^ (0 : ℤ) :=
        (zpow_eq_zpow_iff_modEq (x := a)).2 (by simpa using hz)
      simpa using hpow0)
  have hr_square_mod : r * r ≡ 1 [ZMOD (orderOf a : ℤ)] := by
    exact (zpow_eq_zpow_iff_modEq (x := a)).1 (by simpa using hr_square_one)
  have hs_fixed_mod : r * s ≡ s [ZMOD (orderOf a : ℤ)] := by
    exact (zpow_eq_zpow_iff_modEq (x := a)).1 hs_fixed_by_r
  have hflip_mod : r ≡ -1 [ZMOD (orderOf a : ℤ)] := by
    have horder_pow_int : (orderOf a : ℤ) = (2 : ℤ) ^ M := by
      exact_mod_cast ha_order_pow
    have hbad :
        ¬ ∃ z : ℤ, ((1 + r) * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
      rintro ⟨z, hz⟩
      exact hright_square_mod_ne_zero z (by
        simpa [horder_pow_int] using hz)
    by_contra hr_not_flip
    suffices hcycle : IsCyclic G from hnot_cyclic hcycle
    have hnonflip_forces_cyclic :
        (¬ r ≡ -1 [ZMOD (orderOf a : ℤ)]) → IsCyclic G := by
      intro hr_not_flip'
      have hcore :
          IsCyclic G ∨
            ∃ z : ℤ, ((1 + r) * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
        have hcentralizes_zpowers_of_r_one :
            r ≡ 1 [ZMOD (orderOf a : ℤ)] →
              ∀ z : ℤ, b * a ^ z * b⁻¹ = a ^ z := by
          intro hr_one z
          calc
            b * a ^ z * b⁻¹ = a ^ (r * z) := hconj_a_zpow z
            _ = a ^ ((1 : ℤ) * z) := by
              apply (zpow_eq_zpow_iff_modEq (x := a)).2
              exact hr_one.mul_right z
            _ = a ^ z := by ring_nf
        have hcyclic_of_zpowers_le_b :
            Subgroup.zpowers a ≤ Subgroup.zpowers b → IsCyclic G := by
          intro hA_le_b
          have htop : Subgroup.zpowers b = ⊤ := by
            apply le_antisymm le_top
            intro g hg
            rcases hcover g with ⟨i, hgi | hgi⟩
            · rw [hgi]
              exact hA_le_b (Subgroup.zpow_mem_zpowers a (i.val : ℤ))
            · rw [hgi]
              exact Subgroup.mul_mem _ (Subgroup.mem_zpowers b)
                (hA_le_b (Subgroup.zpow_mem_zpowers a (i.val : ℤ)))
          exact (isCyclic_iff_exists_zpowers_eq_top).2 ⟨b, htop⟩
        have hcyclic_of_a_mem_zpowers_b :
            a ∈ Subgroup.zpowers b → IsCyclic G := by
          intro ha_b
          exact hcyclic_of_zpowers_le_b (Subgroup.zpowers_le_of_mem ha_b)
        have ha_mem_zpowers_b_of_a_mem_zpowers_as :
            a ∈ Subgroup.zpowers (a ^ s) → a ∈ Subgroup.zpowers b := by
          intro ha_mem_as
          rcases Subgroup.mem_zpowers_iff.mp ha_mem_as with ⟨t, ht⟩
          rw [← ht]
          have hb2 : b * b ∈ Subgroup.zpowers b := by
            exact Subgroup.mul_mem _ (Subgroup.mem_zpowers b) (Subgroup.mem_zpowers b)
          have has_mem : a ^ s ∈ Subgroup.zpowers b := by
            simpa [hs] using hb2
          exact Subgroup.zpow_mem _ has_mem t
        have hcyclic_of_r_one :
            r ≡ 1 [ZMOD (orderOf a : ℤ)] → IsCyclic G := by
          intro hr_one
          have hs_unit_mod_order : s.gcd (orderOf a : ℤ) = 1 := by
            by_contra hs_not_unit
            have hsol_two : ∃ z : ℤ,
                (2 * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
              have hM_pos : 0 < M := by
                by_contra hM_not
                have hM0 : M = 0 := Nat.eq_zero_of_not_pos hM_not
                have horder_one : orderOf a = 1 := by
                  simp [ha_order_pow, hM0]
                have hk_zero : k = 0 := by omega
                exact (NeZero.ne k) hk_zero
              have hs_even : Even s := by
                by_contra hs_odd
                have hs_odd' : Odd s := Int.not_even_iff_odd.mp hs_odd
                have hs_nat_odd : Odd s.natAbs := hs_odd'.natAbs
                have hs_nat_coprime : Nat.Coprime s.natAbs (2 ^ M) := by
                  exact (Nat.prime_two.coprime_pow_of_not_dvd (m := M))
                    (by
                      intro htwo
                      exact Nat.not_even_iff_odd.mpr hs_nat_odd (even_iff_two_dvd.mpr htwo))
                have hs_gcd_one_nat : Nat.gcd s.natAbs (2 ^ M) = 1 :=
                  hs_nat_coprime.gcd_eq_one
                have hs_gcd_one : s.gcd (orderOf a : ℤ) = 1 := by
                  rw [horder_pow_int]
                  exact_mod_cast hs_gcd_one_nat
                exact hs_not_unit hs_gcd_one
              refine ⟨-(s / 2), ?_⟩
              have hcalc : 2 * (-(s / 2)) + s = 0 := by
                have hs2 : 2 * (s / 2) = s := Int.two_mul_ediv_two_of_even hs_even
                omega
              rw [hcalc]
            rcases hsol_two with ⟨z, hz⟩
            exact hbad ⟨z, by
              have hcoeff : (1 + r) * z + s ≡ 2 * z + s [ZMOD ((2 : ℤ) ^ M)] := by
                have hr_one_pow : r ≡ 1 [ZMOD ((2 : ℤ) ^ M)] := by
                  simpa [horder_pow_int] using hr_one
                exact (hr_one_pow.add_left 1).mul_right z |>.add_right s
              exact hcoeff.trans hz⟩
          have ha_mem_as : a ∈ Subgroup.zpowers (a ^ s) := by
            exact (mem_zpowers_zpow_iff (g := a) (k := s)).2 (by
              simpa using hs_unit_mod_order)
          exact hcyclic_of_a_mem_zpowers_b
            (ha_mem_zpowers_b_of_a_mem_zpowers_as ha_mem_as)
        have hlinear_solution_of_nontrivial_root (hM_ge_three : 3 ≤ M) :
            (r ≡ 1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] ∨
                r ≡ -1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)]) →
              ∃ z : ℤ, ((1 + r) * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
          intro hr_mid
          have hlinear_of_gcd_dvd :
              ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ) ∣ s →
                ∃ z : ℤ, ((1 + r) * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
            intro hdiv
            rcases hdiv with ⟨t, ht⟩
            refine ⟨-(Int.gcdA (1 + r) ((2 : ℤ) ^ M)) * t, ?_⟩
            rw [Int.modEq_zero_iff_dvd]
            refine ⟨Int.gcdB (1 + r) ((2 : ℤ) ^ M) * t, ?_⟩
            have hbez : (((1 + r).gcd ((2 : ℤ) ^ M) : ℕ) : ℤ) =
                (1 + r) * Int.gcdA (1 + r) ((2 : ℤ) ^ M) +
                  ((2 : ℤ) ^ M) * Int.gcdB (1 + r) ((2 : ℤ) ^ M) :=
              Int.gcd_eq_gcd_ab (1 + r) ((2 : ℤ) ^ M)
            calc
              (1 + r) * (-(Int.gcdA (1 + r) ((2 : ℤ) ^ M)) * t) + s =
                  -((1 + r) * Int.gcdA (1 + r) ((2 : ℤ) ^ M) * t) + s := by ring
              _ = -((1 + r) * Int.gcdA (1 + r) ((2 : ℤ) ^ M) * t) +
                    (((1 + r).gcd ((2 : ℤ) ^ M) : ℕ) : ℤ) * t := by rw [ht]
              _ = ((2 : ℤ) ^ M) * (Int.gcdB (1 + r) ((2 : ℤ) ^ M) * t) := by
                rw [hbez]
                ring
          have hs_fixed_pow : r * s ≡ s [ZMOD ((2 : ℤ) ^ M)] := by
            simpa [horder_pow_int] using hs_fixed_mod
          have hsub_fixed : (r - 1) * s ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
            have hdiff : r * s - s ≡ s - s [ZMOD ((2 : ℤ) ^ M)] := hs_fixed_pow.sub Int.ModEq.rfl
            simpa [sub_mul, one_mul] using hdiff
          apply hlinear_of_gcd_dvd
          rcases hr_mid with hr_mid_pos | hr_mid_neg
          · have hs_even : (2 : ℤ) ∣ s := by
              have hM_pos : 0 < M := by
                by_contra hM_not
                have hM0 : M = 0 := Nat.eq_zero_of_not_pos hM_not
                have horder_one : orderOf a = 1 := by
                  simp [ha_order_pow, hM0]
                have hk_zero : k = 0 := by omega
                exact (NeZero.ne k) hk_zero
              have hpow_sub_ne_zero : ((2 : ℤ) ^ (M - 1)) ≠ 0 := by
                exact pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
              have hsub_coeff : r - 1 ≡ (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
                have h := hr_mid_pos.sub (Int.ModEq.refl (1 : ℤ))
                convert h using 1
                ring
              have hpow_s_zero : ((2 : ℤ) ^ (M - 1)) * s ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
                exact (hsub_coeff.mul_right s).symm.trans hsub_fixed
              have hdiv_pow : (2 : ℤ) ^ M ∣ ((2 : ℤ) ^ (M - 1)) * s := by
                exact Int.modEq_zero_iff_dvd.mp hpow_s_zero
              have hM_eq : M = (M - 1) + 1 := by omega
              have hdiv_pow' : (2 : ℤ) ^ (M - 1) * 2 ∣ (2 : ℤ) ^ (M - 1) * s := by
                rw [hM_eq, pow_succ] at hdiv_pow
                simpa [mul_assoc, mul_comm, mul_left_comm] using hdiv_pow
              exact (mul_dvd_mul_iff_left hpow_sub_ne_zero).mp hdiv_pow'
            have hdiv : ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ) ∣ 2 := by
              let g : ℤ := ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ)
              change g ∣ (2 : ℤ)
              have hg_left : g ∣ 1 + r := by
                dsimp [g]
                exact Int.gcd_dvd_left (1 + r) ((2 : ℤ) ^ M)
              have hg_right : g ∣ (2 : ℤ) ^ M := by
                dsimp [g]
                exact Int.gcd_dvd_right (1 + r) ((2 : ℤ) ^ M)
              have hcoeff :
                  1 + r ≡ 2 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
                have h := hr_mid_pos.add_left (1 : ℤ)
                convert h using 1
                ring
              have hdiff_dvd :
                  (2 : ℤ) ^ M ∣
                    (1 + r) - (2 + (2 : ℤ) ^ (M - 1)) := by
                apply Int.modEq_zero_iff_dvd.mp
                have h := hcoeff.sub (Int.ModEq.refl (2 + (2 : ℤ) ^ (M - 1)))
                simpa using h
              have hg_diff :
                  g ∣ (1 + r) - (2 + (2 : ℤ) ^ (M - 1)) :=
                hg_right.trans hdiff_dvd
              have hg_coeff : g ∣ 2 + (2 : ℤ) ^ (M - 1) := by
                have hsub :
                    g ∣ (1 + r) - ((1 + r) - (2 + (2 : ℤ) ^ (M - 1))) :=
                  dvd_sub hg_left hg_diff
                convert hsub using 1
                ring
              have hM1 : M - 1 = (M - 2) + 1 := by omega
              have hc_eq :
                  2 + (2 : ℤ) ^ (M - 1) =
                    2 * (1 + (2 : ℤ) ^ (M - 2)) := by
                rw [hM1, pow_succ]
                ring
              have hp_mul :
                  (2 : ℤ) ^ M * (2 : ℤ) ^ (M - 3) =
                    2 * ((2 : ℤ) ^ (M - 2)) ^ 2 := by
                calc
                  (2 : ℤ) ^ M * (2 : ℤ) ^ (M - 3)
                      = (2 : ℤ) ^ (M + (M - 3)) := by rw [← pow_add]
                  _ = (2 : ℤ) ^ (((M - 2) + (M - 2)) + 1) := by
                    congr 1
                    omega
                  _ = (2 : ℤ) ^ ((M - 2) + (M - 2)) * 2 := by
                    rw [pow_succ]
                  _ = ((2 : ℤ) ^ (M - 2) * (2 : ℤ) ^ (M - 2)) * 2 := by
                    rw [pow_add]
                  _ = 2 * ((2 : ℤ) ^ (M - 2)) ^ 2 := by
                    ring
              have hcomb :
                  (2 + (2 : ℤ) ^ (M - 1)) * (1 - (2 : ℤ) ^ (M - 2)) +
                      (2 : ℤ) ^ M * (2 : ℤ) ^ (M - 3) = 2 := by
                rw [hc_eq, hp_mul]
                ring
              have hg_comb :
                  g ∣
                    (2 + (2 : ℤ) ^ (M - 1)) * (1 - (2 : ℤ) ^ (M - 2)) +
                      (2 : ℤ) ^ M * (2 : ℤ) ^ (M - 3) := by
                exact dvd_add
                  (dvd_mul_of_dvd_left hg_coeff _)
                  (dvd_mul_of_dvd_left hg_right _)
              simpa [hcomb] using hg_comb
            exact hdiv.trans hs_even
          · have hpow_dvd_s : (2 : ℤ) ^ (M - 1) ∣ s := by
              have htwo_ne_zero : (2 : ℤ) ≠ 0 := by norm_num
              have hsub_coeff :
                  r - 1 ≡ (2 : ℤ) ^ (M - 1) - 2 [ZMOD ((2 : ℤ) ^ M)] := by
                have h := hr_mid_neg.sub (Int.ModEq.refl (1 : ℤ))
                convert h using 1
                ring
              have hcoeff_s_zero :
                  ((2 : ℤ) ^ (M - 1) - 2) * s ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
                exact (hsub_coeff.mul_right s).symm.trans hsub_fixed
              have hdiv_pow :
                  (2 : ℤ) ^ M ∣ (((2 : ℤ) ^ (M - 1) - 2) * s) := by
                exact Int.modEq_zero_iff_dvd.mp hcoeff_s_zero
              have hcoeff_eq :
                  (2 : ℤ) ^ (M - 1) - 2 =
                    2 * ((2 : ℤ) ^ (M - 2) - 1) := by
                have hM1 : M - 1 = (M - 2) + 1 := by omega
                rw [hM1, pow_succ]
                ring
              have hpow_eq :
                  (2 : ℤ) ^ M = 2 * (2 : ℤ) ^ (M - 1) := by
                have hM : M = (M - 1) + 1 := by omega
                rw [hM, pow_succ]
                simp [mul_comm]
              have hdiv_cancel :
                  (2 : ℤ) ^ (M - 1) ∣ ((2 : ℤ) ^ (M - 2) - 1) * s := by
                have hdiv' :
                    2 * (2 : ℤ) ^ (M - 1) ∣
                      2 * (((2 : ℤ) ^ (M - 2) - 1) * s) := by
                  simpa [hpow_eq, hcoeff_eq, mul_assoc, mul_comm, mul_left_comm] using hdiv_pow
                exact (mul_dvd_mul_iff_left htwo_ne_zero).mp hdiv'
              rcases hdiv_cancel with ⟨t, ht⟩
              have hpow_mul :
                  (2 : ℤ) ^ (M - 1) * (2 : ℤ) ^ (M - 3) =
                    ((2 : ℤ) ^ (M - 2)) ^ 2 := by
                calc
                  (2 : ℤ) ^ (M - 1) * (2 : ℤ) ^ (M - 3)
                      = (2 : ℤ) ^ ((M - 1) + (M - 3)) := by rw [← pow_add]
                  _ = (2 : ℤ) ^ ((M - 2) + (M - 2)) := by
                    congr 1
                    omega
                  _ = (2 : ℤ) ^ (M - 2) * (2 : ℤ) ^ (M - 2) := by rw [pow_add]
                  _ = ((2 : ℤ) ^ (M - 2)) ^ 2 := by ring
              have hbez :
                  ((2 : ℤ) ^ (M - 2) - 1) * (-((2 : ℤ) ^ (M - 2) + 1)) +
                    (2 : ℤ) ^ (M - 1) * (2 : ℤ) ^ (M - 3) = 1 := by
                rw [hpow_mul]
                ring
              refine ⟨t * (-((2 : ℤ) ^ (M - 2) + 1)) + (2 : ℤ) ^ (M - 3) * s, ?_⟩
              calc
                s = 1 * s := by ring
                _ = (((2 : ℤ) ^ (M - 2) - 1) * (-((2 : ℤ) ^ (M - 2) + 1)) +
                      (2 : ℤ) ^ (M - 1) * (2 : ℤ) ^ (M - 3)) * s := by
                  rw [hbez]
                _ = (((2 : ℤ) ^ (M - 2) - 1) * s) *
                        (-((2 : ℤ) ^ (M - 2) + 1)) +
                      (2 : ℤ) ^ (M - 1) * ((2 : ℤ) ^ (M - 3) * s) := by
                  ring
                _ = ((2 : ℤ) ^ (M - 1) * t) *
                        (-((2 : ℤ) ^ (M - 2) + 1)) +
                      (2 : ℤ) ^ (M - 1) * ((2 : ℤ) ^ (M - 3) * s) := by
                  rw [ht]
                _ = (2 : ℤ) ^ (M - 1) *
                    (t * (-((2 : ℤ) ^ (M - 2) + 1)) + (2 : ℤ) ^ (M - 3) * s) := by
                  ring
            have hdiv : ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ) ∣ (2 : ℤ) ^ (M - 1) := by
              let g : ℤ := ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ)
              change g ∣ (2 : ℤ) ^ (M - 1)
              have hg_left : g ∣ 1 + r := by
                dsimp [g]
                exact Int.gcd_dvd_left (1 + r) ((2 : ℤ) ^ M)
              have hg_right : g ∣ (2 : ℤ) ^ M := by
                dsimp [g]
                exact Int.gcd_dvd_right (1 + r) ((2 : ℤ) ^ M)
              have hcoeff :
                  1 + r ≡ (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
                have h := hr_mid_neg.add_left (1 : ℤ)
                convert h using 1
                ring
              have hdiff_dvd :
                  (2 : ℤ) ^ M ∣ (1 + r) - (2 : ℤ) ^ (M - 1) := by
                apply Int.modEq_zero_iff_dvd.mp
                have h := hcoeff.sub (Int.ModEq.refl ((2 : ℤ) ^ (M - 1)))
                simpa using h
              have hg_diff :
                  g ∣ (1 + r) - (2 : ℤ) ^ (M - 1) :=
                hg_right.trans hdiff_dvd
              have hsub :
                  g ∣ (1 + r) - ((1 + r) - (2 : ℤ) ^ (M - 1)) :=
                dvd_sub hg_left hg_diff
              convert hsub using 1
              ring
            exact hdiv.trans hpow_dvd_s
        have hroot_split :
            r ≡ 1 [ZMOD (orderOf a : ℤ)] ∨
              r ≡ -1 [ZMOD (orderOf a : ℤ)] ∨
                (3 ≤ M ∧
                  (r ≡ 1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] ∨
                    r ≡ -1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)])) := by
          have hmodEq_of_dvd_sub {m x y : ℤ} (h : m ∣ x - y) :
              x ≡ y [ZMOD m] := by
            have hz : x - y ≡ 0 [ZMOD m] := Int.modEq_zero_iff_dvd.mpr h
            have h' := hz.add_right y
            convert h' using 1 <;> ring
          have hpow_dvd_consec :
              ∀ {n : ℕ} {x : ℤ}, (2 : ℤ) ^ n ∣ x * (x + 1) →
                (2 : ℤ) ^ n ∣ x ∨ (2 : ℤ) ^ n ∣ x + 1 := by
            intro n x hx
            have hprime2 : Prime (2 : ℤ) := by exact Int.prime_two
            by_cases hx2 : (2 : ℤ) ∣ x
            · left
              have hnot : ¬ (2 : ℤ) ∣ x + 1 := by
                intro hx1
                have htwo_one : (2 : ℤ) ∣ 1 := by
                  have h := dvd_sub hx1 hx2
                  simpa only [add_sub_cancel_left] using h
                norm_num at htwo_one
              have hcop2 : IsCoprime (2 : ℤ) (x + 1) :=
                (hprime2.coprime_iff_not_dvd).mpr hnot
              exact hcop2.pow_left.dvd_of_dvd_mul_right hx
            · right
              have hcop2 : IsCoprime (2 : ℤ) x :=
                (hprime2.coprime_iff_not_dvd).mpr hx2
              exact hcop2.pow_left.dvd_of_dvd_mul_left hx
          have hr_square_pow : r * r ≡ 1 [ZMOD ((2 : ℤ) ^ M)] := by
            simpa [horder_pow_int] using hr_square_mod
          have hsq_dvd : (2 : ℤ) ^ M ∣ r * r - 1 := by
            apply Int.modEq_zero_iff_dvd.mp
            have h := hr_square_pow.sub (Int.ModEq.refl (1 : ℤ))
            simpa using h
          have hprod_dvd : (2 : ℤ) ^ M ∣ (r - 1) * (r + 1) := by
            convert hsq_dvd using 1
            ring
          by_cases hM0 : M = 0
          · left
            subst M
            rw [horder_pow_int]
            norm_num [Int.ModEq]
          have hM_pos : 0 < M := Nat.pos_of_ne_zero hM0
          have htwo_dvd_pow : (2 : ℤ) ∣ (2 : ℤ) ^ M := by
            have hM_eq : M = (M - 1) + 1 := by omega
            rw [hM_eq, pow_succ]
            exact dvd_mul_left _ _
          have htwo_dvd_sq : (2 : ℤ) ∣ r * r - 1 :=
            htwo_dvd_pow.trans hsq_dvd
          have hodd_r : Odd r := by
            rcases Int.even_or_odd r with hr_even | hr_odd
            · have htwo_rr : (2 : ℤ) ∣ r * r := dvd_mul_of_dvd_left (by rw[← even_iff_two_dvd]; exact hr_even) r
              have htwo_one : (2 : ℤ) ∣ 1 := by
                have h := dvd_sub htwo_rr htwo_dvd_sq
                simpa only [sub_sub_cancel] using h
              norm_num at htwo_one
            · exact hr_odd
          rcases hodd_r with ⟨t, ht⟩
          by_cases hM_ge_three : 3 ≤ M
          · have hM_eq2 : M = (M - 2) + 2 := by omega
            have hpow_rewrite :
                (2 : ℤ) ^ M = 4 * (2 : ℤ) ^ (M - 2) := by
              rw [hM_eq2, pow_add]
              norm_num [pow_two]
              ring
            have hprod_rewrite :
                (r - 1) * (r + 1) = 4 * (t * (t + 1)) := by
              rw [ht]
              ring
            have htprod_dvd : (2 : ℤ) ^ (M - 2) ∣ t * (t + 1) := by
              have h4 :
                  4 * (2 : ℤ) ^ (M - 2) ∣ 4 * (t * (t + 1)) := by
                simpa [hpow_rewrite, hprod_rewrite] using hprod_dvd
              exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4
            have hM_eq1 : M = (M - 1) + 1 := by omega
            have hpowM :
                (2 : ℤ) ^ M = (2 : ℤ) ^ (M - 1) * 2 := by
              rw [hM_eq1, pow_succ]
              simp
            have hlift_minus :
                (2 : ℤ) ^ (M - 1) ∣ r - 1 →
                  r ≡ 1 [ZMOD ((2 : ℤ) ^ M)] ∨
                  r ≡ 1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
              intro hp
              rcases hp with ⟨q, hq⟩
              rcases Int.even_or_odd q with ⟨u, hu⟩ | ⟨u, hu⟩
              · left
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                calc
                  r - 1 = (2 : ℤ) ^ (M - 1) * q := hq
                  _ = (2 : ℤ) ^ (M - 1) * (2 * u) := by rw [hu]; ring
                  _ = (2 : ℤ) ^ M * u := by rw [hpowM]; ring
              · right
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                calc
                  r - (1 + (2 : ℤ) ^ (M - 1))
                      = (r - 1) - (2 : ℤ) ^ (M - 1) := by ring
                  _ = (2 : ℤ) ^ (M - 1) * q - (2 : ℤ) ^ (M - 1) := by rw [hq]
                  _ = (2 : ℤ) ^ (M - 1) * (2 * u + 1) -
                        (2 : ℤ) ^ (M - 1) := by rw [hu]
                  _ = (2 : ℤ) ^ M * u := by rw [hpowM]; ring

            have hlift_plus :
                (2 : ℤ) ^ (M - 1) ∣ r + 1 →
                  r ≡ -1 [ZMOD ((2 : ℤ) ^ M)] ∨
                  r ≡ -1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
              intro hp
              rcases hp with ⟨q, hq⟩
              rcases Int.even_or_odd q with ⟨u, hu⟩ | ⟨u, hu⟩
              · left
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                calc
                  r - (-1 : ℤ) = r + 1 := by ring
                  _ = (2 : ℤ) ^ (M - 1) * q := hq
                  _ = (2 : ℤ) ^ (M - 1) * (2 * u) := by rw [hu]; ring
                  _ = (2 : ℤ) ^ M * u := by rw [hpowM]; ring
              · right
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                calc
                  r - (-1 + (2 : ℤ) ^ (M - 1))
                      = (r + 1) - (2 : ℤ) ^ (M - 1) := by ring
                  _ = (2 : ℤ) ^ (M - 1) * q - (2 : ℤ) ^ (M - 1) := by rw [hq]
                  _ = (2 : ℤ) ^ (M - 1) * (2 * u + 1) -
                        (2 : ℤ) ^ (M - 1) := by rw [hu]
                  _ = (2 : ℤ) ^ M * u := by rw [hpowM]; ring
            rcases hpow_dvd_consec htprod_dvd with ht_dvd | ht1_dvd
            · have hp : (2 : ℤ) ^ (M - 1) ∣ r - 1 := by
                have hM1 : M - 1 = (M - 2) + 1 := by omega
                have hmul : (2 : ℤ) * (2 : ℤ) ^ (M - 2) ∣ 2 * t :=
                  mul_dvd_mul_left (2 : ℤ) ht_dvd
                rw [ht]
                simpa [hM1, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul
              rcases hlift_minus hp with h1 | hmid
              · left
                simpa [horder_pow_int] using h1
              · right
                right
                exact ⟨hM_ge_three, Or.inl hmid⟩
            · have hp : (2 : ℤ) ^ (M - 1) ∣ r + 1 := by
                have hM1 : M - 1 = (M - 2) + 1 := by omega
                have hmul :
                    (2 : ℤ) * (2 : ℤ) ^ (M - 2) ∣ 2 * (t + 1) :=
                  mul_dvd_mul_left (2 : ℤ) ht1_dvd
                rw [ht, show 2 * t + 1 + 1 = 2 * (t + 1) by ring]
                simpa [hM1, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul
              rcases hlift_plus hp with hneg | hmid
              · right
                left
                simpa [horder_pow_int] using hneg
              · right
                right
                exact ⟨hM_ge_three, Or.inr hmid⟩
          · have hM_le_two : M ≤ 2 := by omega
            interval_cases M
            · -- M = 1
              left
              rw [horder_pow_int]
              norm_num
              apply hmodEq_of_dvd_sub
              refine ⟨t, ?_⟩
              rw [ht]
              ring
            · -- M = 2
              rcases Int.even_or_odd t with ⟨u, hu⟩ | ⟨u, hu⟩
              · left
                rw [horder_pow_int]
                norm_num
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                rw [ht, hu]
                ring
              · right
                left
                rw [horder_pow_int]
                norm_num
                apply hmodEq_of_dvd_sub
                refine ⟨u + 1, ?_⟩
                rw [ht, hu]
                ring
        rcases hroot_split with hr_one | hr_neg | hmid
        · exact Or.inl (hcyclic_of_r_one hr_one)
        · exact False.elim (hr_not_flip' hr_neg)
        · rcases hmid with ⟨hM_ge_three, hr_mid_pos | hr_mid_neg⟩
          · exact Or.inr (hlinear_solution_of_nontrivial_root hM_ge_three (Or.inl hr_mid_pos))
          · exact Or.inr (hlinear_solution_of_nontrivial_root hM_ge_three (Or.inr hr_mid_neg))
      rcases hcore with hcycle | hex
      · exact hcycle
      · exact False.elim (hbad hex)
    exact hnonflip_forces_cyclic hr_not_flip
  have hconj_a_inv_zpow : ∀ z : ℤ, b * a ^ z * b⁻¹ = a ^ (-z) := by
    intro z
    calc
      b * a ^ z * b⁻¹ = a ^ (r * z) := hconj_a_zpow z
      _ = a ^ ((-1 : ℤ) * z) := by
        apply (zpow_eq_zpow_iff_modEq (x := a)).2
        exact hflip_mod.mul_right z
      _ = a ^ (-z) := by ring_nf
  have hconj : ∀ z : ℤ, a ^ z * b = b * a ^ (-z) := by
    intro z
    have hz : b * a ^ (-z) * b⁻¹ = a ^ z := by
      simpa using hconj_a_inv_zpow (-z)
    calc
      a ^ z * b = (b * a ^ (-z) * b⁻¹) * b := by rw [hz]
      _ = b * a ^ (-z) := by group
  exact hconj
/--
Huppert I.14.9(b), quaternion case from a cyclic normal subgroup of index `2`.
The proof constructs the actual equivalence with Mathlib's `QuaternionGroup` by
reducing to the presentation relations.
-/
public theorem huppert_I_14_9_generalizedQuaternion_mulEquiv_of_cyclic_index_two
    {G : Type u} [Group G] [Finite G] {k : ℕ} [NeZero k]
    (A : Subgroup G) [A.Normal] (a b : G)
    (hA_eq : Subgroup.zpowers a = A)
    (hA_index : A.index = 2)
    (ha_order : orderOf a = 2 * k)
    (hb_not_mem : b ∉ A)
    (hunique_order_two : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y)
    (hnot_cyclic : ¬ IsCyclic G)
    (hcard : Nat.card G = 4 * k)
    (hGp : IsPGroup 2 G) :
    Nonempty (G ≃* QuaternionGroup k) := by
  classical
  have hcoverA : ∀ g : G, g ∈ A ∨ b⁻¹ * g ∈ A := by
    intro g
    by_cases hgA : g ∈ A
    · exact Or.inl hgA
    · have hiff := A.mul_mem_iff_of_index_two (by simpa using hA_index) (a := b⁻¹) (b := g)
      have hb_inv_not : b⁻¹ ∉ A := by
        intro hb_inv
        exact hb_not_mem (by simpa using A.inv_mem hb_inv)
      exact Or.inr (hiff.mpr (Iff.intro (fun hb => False.elim (hb_inv_not hb)) (fun hg => False.elim (hgA hg))))
  have hcover : ∀ g : G, ∃ i : ZMod (2 * k),
      g = a ^ (i.val : ℤ) ∨ g = b * a ^ (i.val : ℤ) := by
    intro g
    rcases hcoverA g with hgA | hbgA
    · rw [← hA_eq] at hgA
      rcases Subgroup.mem_zpowers_iff.mp hgA with ⟨z, hz⟩
      refine ⟨(z : ZMod (2 * k)), Or.inl ?_⟩
      calc
        g = a ^ z := hz.symm
        _ = a ^ (((z : ZMod (2 * k)).val : ℕ) : ℤ) := by
          apply (zpow_eq_zpow_iff_modEq (x := a)).2
          simpa [ha_order] using
            (ZMod.intCast_eq_intCast_iff z (((z : ZMod (2 * k)).val : ℕ) : ℤ) (2 * k)).mp (by simp)
    · rw [← hA_eq] at hbgA
      rcases Subgroup.mem_zpowers_iff.mp hbgA with ⟨z, hz⟩
      refine ⟨(z : ZMod (2 * k)), Or.inr ?_⟩
      calc
        g = b * (b⁻¹ * g) := by group
        _ = b * a ^ z := by rw [hz]
        _ = b * a ^ (((z : ZMod (2 * k)).val : ℕ) : ℤ) := by
          congr 1
          apply (zpow_eq_zpow_iff_modEq (x := a)).2
          simpa [ha_order] using
            (ZMod.intCast_eq_intCast_iff z (((z : ZMod (2 * k)).val : ℕ) : ℤ) (2 * k)).mp (by simp)
  have hb_sq_mem : b * b ∈ A := by
    simpa [pow_two] using A.sq_mem_of_index_two hA_index b
  have hb_sq_in_zpowers : b * b ∈ Subgroup.zpowers a := by
    simpa [hA_eq] using hb_sq_mem
  have ha_k_order_two : orderOf (a ^ (k : ℤ)) = 2 := by
    have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    have hnat : orderOf (a ^ k) = 2 := by
      rw [orderOf_pow, ha_order]
      rw [Nat.gcd_mul_left_left]
      rw [Nat.mul_comm 2 k]
      exact Nat.mul_div_right 2 hkpos
    simpa [zpow_natCast] using hnat
  have hA_card : Nat.card A = 2 * k := by
    have hmul : Nat.card A * A.index = Nat.card G := A.card_mul_index
    have hmul' : Nat.card A * 2 = 4 * k := by
      simpa [hA_index, hcard] using hmul
    have htarget : (2 * k) * 2 = 4 * k := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (hmul'.trans htarget.symm)
  have ha_k_mem_A : a ^ (k : ℤ) ∈ A := by
    rw [← hA_eq]
    exact Subgroup.zpow_mem_zpowers a (k : ℤ)
  have houtside_sq_ne_one : ∀ x : G, x ∉ A → x * x ≠ 1 := by
    intro x hxA hsq
    have hx_ne_one : x ≠ 1 := by
      intro hx
      exact hxA (by simp [hx])
    have hx_order : orderOf x = 2 := by
      have hpow : x ^ 2 = 1 := by simpa [pow_two] using hsq
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact False.elim (hx_ne_one (orderOf_eq_one_iff.mp h))
      · exact h
    have hx_eq_ak := hunique_order_two x (a ^ (k : ℤ)) hx_order ha_k_order_two
    exact hxA (by simpa [hx_eq_ak] using ha_k_mem_A)
  have hright_not_mem_A : ∀ z : ℤ, a ^ z * b ∉ A := by
    intro z hzA
    have haz : a ^ z ∈ A := by
      rw [← hA_eq]
      exact Subgroup.zpow_mem_zpowers a z
    have hbA : b ∈ A := by
      have hmul : (a ^ z)⁻¹ * (a ^ z * b) ∈ A := A.mul_mem (A.inv_mem haz) hzA
      simpa [mul_assoc] using hmul
    exact hb_not_mem hbA
  have hright_sq_ne_one : ∀ z : ℤ, (a ^ z * b) * (a ^ z * b) ≠ 1 := by
    intro z
    exact houtside_sq_ne_one (a ^ z * b) (hright_not_mem_A z)
  have hb_sq_ne_one : b * b ≠ 1 := by
    simpa using hright_sq_ne_one 0
  have ha_mem_A : a ∈ A := by
    rw [← hA_eq]
    exact Subgroup.mem_zpowers a
  have hbab_mem_A : b * a * b⁻¹ ∈ A := by
    exact (inferInstance : A.Normal).conj_mem a ha_mem_A b
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp (by
    simpa [hA_eq] using hbab_mem_A : b * a * b⁻¹ ∈ Subgroup.zpowers a)
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hb_sq_in_zpowers
  have hconj_a_zpow : ∀ z : ℤ, b * a ^ z * b⁻¹ = a ^ (r * z) := by
    intro z
    calc
      b * a ^ z * b⁻¹ = (b * a * b⁻¹) ^ z := (conj_zpow (a := b) (b := a) (i := z)).symm
      _ = (a ^ r) ^ z := by rw [hr]
      _ = a ^ (r * z) := by rw [zpow_mul]
  have hr_square_one : a ^ (r * r) = a := by
    calc
      a ^ (r * r) = b * a ^ r * b⁻¹ := (hconj_a_zpow r).symm
      _ = b * (b * a * b⁻¹) * b⁻¹ := by rw [hr]
      _ = (b * b) * a * (b * b)⁻¹ := by group
      _ = a := by
        rw [← hs]
        group
  have hs_fixed_by_r : a ^ (r * s) = a ^ s := by
    calc
      a ^ (r * s) = b * a ^ s * b⁻¹ := (hconj_a_zpow s).symm
      _ = b * (b * b) * b⁻¹ := by rw [hs]
      _ = b * b := by group
      _ = a ^ s := hs.symm
  have hAp : IsPGroup 2 A := hGp.to_subgroup A
  obtain ⟨M, hA_card_pow⟩ := hAp.exists_card_eq
  have ha_order_pow : orderOf a = 2 ^ M := by
    calc
      orderOf a = 2 * k := ha_order
      _ = Nat.card A := hA_card.symm
      _ = 2 ^ M := hA_card_pow
  have hright_square_formula : ∀ z : ℤ,
      (a ^ z * b) * (a ^ z * b) = a ^ ((1 + r) * z + s) := by
    intro z
    calc
      (a ^ z * b) * (a ^ z * b) =
          a ^ z * (b * a ^ z * b⁻¹) * (b * b) := by group
      _ = a ^ z * a ^ (r * z) * a ^ s := by rw [hconj_a_zpow z, ← hs]
      _ = a ^ (z + r * z) * a ^ s := by rw [← zpow_add]
      _ = a ^ ((1 + r) * z + s) := by
        rw [← zpow_add]
        ring_nf
  have hright_square_mod_ne_zero :
      ∀ z : ℤ, ¬ (((1 + r) * z + s) ≡ 0 [ZMOD (orderOf a : ℤ)]) := by
    intro z hz
    exact hright_sq_ne_one z (by
      rw [hright_square_formula z]
      have hpow0 : a ^ ((1 + r) * z + s) = a ^ (0 : ℤ) :=
        (zpow_eq_zpow_iff_modEq (x := a)).2 (by simpa using hz)
      simpa using hpow0)
  have hr_square_mod : r * r ≡ 1 [ZMOD (orderOf a : ℤ)] := by
    exact (zpow_eq_zpow_iff_modEq (x := a)).1 (by simpa using hr_square_one)
  have hs_fixed_mod : r * s ≡ s [ZMOD (orderOf a : ℤ)] := by
    exact (zpow_eq_zpow_iff_modEq (x := a)).1 hs_fixed_by_r
  have hflip_mod : r ≡ -1 [ZMOD (orderOf a : ℤ)] := by
    have horder_pow_int : (orderOf a : ℤ) = (2 : ℤ) ^ M := by
      exact_mod_cast ha_order_pow
    have hbad :
        ¬ ∃ z : ℤ, ((1 + r) * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
      rintro ⟨z, hz⟩
      exact hright_square_mod_ne_zero z (by
        simpa [horder_pow_int] using hz)
    by_contra hr_not_flip
    suffices hcycle : IsCyclic G from hnot_cyclic hcycle
    have hnonflip_forces_cyclic :
        (¬ r ≡ -1 [ZMOD (orderOf a : ℤ)]) → IsCyclic G := by
      intro hr_not_flip'
      have hcore :
          IsCyclic G ∨
            ∃ z : ℤ, ((1 + r) * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
        have hcentralizes_zpowers_of_r_one :
            r ≡ 1 [ZMOD (orderOf a : ℤ)] →
              ∀ z : ℤ, b * a ^ z * b⁻¹ = a ^ z := by
          intro hr_one z
          calc
            b * a ^ z * b⁻¹ = a ^ (r * z) := hconj_a_zpow z
            _ = a ^ ((1 : ℤ) * z) := by
              apply (zpow_eq_zpow_iff_modEq (x := a)).2
              exact hr_one.mul_right z
            _ = a ^ z := by ring_nf
        have hcyclic_of_zpowers_le_b :
            Subgroup.zpowers a ≤ Subgroup.zpowers b → IsCyclic G := by
          intro hA_le_b
          have htop : Subgroup.zpowers b = ⊤ := by
            apply le_antisymm le_top
            intro g hg
            rcases hcover g with ⟨i, hgi | hgi⟩
            · rw [hgi]
              exact hA_le_b (Subgroup.zpow_mem_zpowers a (i.val : ℤ))
            · rw [hgi]
              exact Subgroup.mul_mem _ (Subgroup.mem_zpowers b)
                (hA_le_b (Subgroup.zpow_mem_zpowers a (i.val : ℤ)))
          exact (isCyclic_iff_exists_zpowers_eq_top).2 ⟨b, htop⟩
        have hcyclic_of_a_mem_zpowers_b :
            a ∈ Subgroup.zpowers b → IsCyclic G := by
          intro ha_b
          exact hcyclic_of_zpowers_le_b (Subgroup.zpowers_le_of_mem ha_b)
        have ha_mem_zpowers_b_of_a_mem_zpowers_as :
            a ∈ Subgroup.zpowers (a ^ s) → a ∈ Subgroup.zpowers b := by
          intro ha_mem_as
          rcases Subgroup.mem_zpowers_iff.mp ha_mem_as with ⟨t, ht⟩
          rw [← ht]
          have hb2 : b * b ∈ Subgroup.zpowers b := by
            exact Subgroup.mul_mem _ (Subgroup.mem_zpowers b) (Subgroup.mem_zpowers b)
          have has_mem : a ^ s ∈ Subgroup.zpowers b := by
            simpa [hs] using hb2
          exact Subgroup.zpow_mem _ has_mem t
        have hcyclic_of_r_one :
            r ≡ 1 [ZMOD (orderOf a : ℤ)] → IsCyclic G := by
          intro hr_one
          have hs_unit_mod_order : s.gcd (orderOf a : ℤ) = 1 := by
            by_contra hs_not_unit
            have hsol_two : ∃ z : ℤ,
                (2 * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
              have hM_pos : 0 < M := by
                by_contra hM_not
                have hM0 : M = 0 := Nat.eq_zero_of_not_pos hM_not
                have horder_one : orderOf a = 1 := by
                  simp [ha_order_pow, hM0]
                have hk_zero : k = 0 := by omega
                exact (NeZero.ne k) hk_zero
              have hs_even : Even s := by
                by_contra hs_odd
                have hs_odd' : Odd s := Int.not_even_iff_odd.mp hs_odd
                have hs_nat_odd : Odd s.natAbs := hs_odd'.natAbs
                have hs_nat_coprime : Nat.Coprime s.natAbs (2 ^ M) := by
                  exact (Nat.prime_two.coprime_pow_of_not_dvd (m := M))
                    (by
                      intro htwo
                      exact Nat.not_even_iff_odd.mpr hs_nat_odd (even_iff_two_dvd.mpr htwo))
                have hs_gcd_one_nat : Nat.gcd s.natAbs (2 ^ M) = 1 :=
                  hs_nat_coprime.gcd_eq_one
                have hs_gcd_one : s.gcd (orderOf a : ℤ) = 1 := by
                  rw [horder_pow_int]
                  exact_mod_cast hs_gcd_one_nat
                exact hs_not_unit hs_gcd_one
              refine ⟨-(s / 2), ?_⟩
              have hcalc : 2 * (-(s / 2)) + s = 0 := by
                have hs2 : 2 * (s / 2) = s := Int.two_mul_ediv_two_of_even hs_even
                omega
              rw [hcalc]
            rcases hsol_two with ⟨z, hz⟩
            exact hbad ⟨z, by
              have hcoeff : (1 + r) * z + s ≡ 2 * z + s [ZMOD ((2 : ℤ) ^ M)] := by
                have hr_one_pow : r ≡ 1 [ZMOD ((2 : ℤ) ^ M)] := by
                  simpa [horder_pow_int] using hr_one
                exact (hr_one_pow.add_left 1).mul_right z |>.add_right s
              exact hcoeff.trans hz⟩
          have ha_mem_as : a ∈ Subgroup.zpowers (a ^ s) := by
            exact (mem_zpowers_zpow_iff (g := a) (k := s)).2 (by
              simpa using hs_unit_mod_order)
          exact hcyclic_of_a_mem_zpowers_b
            (ha_mem_zpowers_b_of_a_mem_zpowers_as ha_mem_as)
        have hlinear_solution_of_nontrivial_root (hM_ge_three : 3 ≤ M) :
            (r ≡ 1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] ∨
                r ≡ -1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)]) →
              ∃ z : ℤ, ((1 + r) * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
          intro hr_mid
          have hlinear_of_gcd_dvd :
              ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ) ∣ s →
                ∃ z : ℤ, ((1 + r) * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
            intro hdiv
            rcases hdiv with ⟨t, ht⟩
            refine ⟨-(Int.gcdA (1 + r) ((2 : ℤ) ^ M)) * t, ?_⟩
            rw [Int.modEq_zero_iff_dvd]
            refine ⟨Int.gcdB (1 + r) ((2 : ℤ) ^ M) * t, ?_⟩
            have hbez : (((1 + r).gcd ((2 : ℤ) ^ M) : ℕ) : ℤ) =
                (1 + r) * Int.gcdA (1 + r) ((2 : ℤ) ^ M) +
                  ((2 : ℤ) ^ M) * Int.gcdB (1 + r) ((2 : ℤ) ^ M) :=
              Int.gcd_eq_gcd_ab (1 + r) ((2 : ℤ) ^ M)
            calc
              (1 + r) * (-(Int.gcdA (1 + r) ((2 : ℤ) ^ M)) * t) + s =
                  -((1 + r) * Int.gcdA (1 + r) ((2 : ℤ) ^ M) * t) + s := by ring
              _ = -((1 + r) * Int.gcdA (1 + r) ((2 : ℤ) ^ M) * t) +
                    (((1 + r).gcd ((2 : ℤ) ^ M) : ℕ) : ℤ) * t := by rw [ht]
              _ = ((2 : ℤ) ^ M) * (Int.gcdB (1 + r) ((2 : ℤ) ^ M) * t) := by
                rw [hbez]
                ring
          have hs_fixed_pow : r * s ≡ s [ZMOD ((2 : ℤ) ^ M)] := by
            simpa [horder_pow_int] using hs_fixed_mod
          have hsub_fixed : (r - 1) * s ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
            have hdiff : r * s - s ≡ s - s [ZMOD ((2 : ℤ) ^ M)] := hs_fixed_pow.sub Int.ModEq.rfl
            simpa [sub_mul, one_mul] using hdiff
          apply hlinear_of_gcd_dvd
          rcases hr_mid with hr_mid_pos | hr_mid_neg
          · have hs_even : (2 : ℤ) ∣ s := by
              have hM_pos : 0 < M := by
                by_contra hM_not
                have hM0 : M = 0 := Nat.eq_zero_of_not_pos hM_not
                have horder_one : orderOf a = 1 := by
                  simp [ha_order_pow, hM0]
                have hk_zero : k = 0 := by omega
                exact (NeZero.ne k) hk_zero
              have hpow_sub_ne_zero : ((2 : ℤ) ^ (M - 1)) ≠ 0 := by
                exact pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
              have hsub_coeff : r - 1 ≡ (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
                have h := hr_mid_pos.sub (Int.ModEq.refl (1 : ℤ))
                convert h using 1
                ring
              have hpow_s_zero : ((2 : ℤ) ^ (M - 1)) * s ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
                exact (hsub_coeff.mul_right s).symm.trans hsub_fixed
              have hdiv_pow : (2 : ℤ) ^ M ∣ ((2 : ℤ) ^ (M - 1)) * s := by
                exact Int.modEq_zero_iff_dvd.mp hpow_s_zero
              have hM_eq : M = (M - 1) + 1 := by omega
              have hdiv_pow' : (2 : ℤ) ^ (M - 1) * 2 ∣ (2 : ℤ) ^ (M - 1) * s := by
                rw [hM_eq, pow_succ] at hdiv_pow
                simpa [mul_assoc, mul_comm, mul_left_comm] using hdiv_pow
              exact (mul_dvd_mul_iff_left hpow_sub_ne_zero).mp hdiv_pow'
            have hdiv : ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ) ∣ 2 := by
              let g : ℤ := ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ)
              change g ∣ (2 : ℤ)
              have hg_left : g ∣ 1 + r := by
                dsimp [g]
                exact Int.gcd_dvd_left (1 + r) ((2 : ℤ) ^ M)
              have hg_right : g ∣ (2 : ℤ) ^ M := by
                dsimp [g]
                exact Int.gcd_dvd_right (1 + r) ((2 : ℤ) ^ M)
              have hcoeff :
                  1 + r ≡ 2 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
                have h := hr_mid_pos.add_left (1 : ℤ)
                convert h using 1
                ring
              have hdiff_dvd :
                  (2 : ℤ) ^ M ∣
                    (1 + r) - (2 + (2 : ℤ) ^ (M - 1)) := by
                apply Int.modEq_zero_iff_dvd.mp
                have h := hcoeff.sub (Int.ModEq.refl (2 + (2 : ℤ) ^ (M - 1)))
                simpa using h
              have hg_diff :
                  g ∣ (1 + r) - (2 + (2 : ℤ) ^ (M - 1)) :=
                hg_right.trans hdiff_dvd
              have hg_coeff : g ∣ 2 + (2 : ℤ) ^ (M - 1) := by
                have hsub :
                    g ∣ (1 + r) - ((1 + r) - (2 + (2 : ℤ) ^ (M - 1))) :=
                  dvd_sub hg_left hg_diff
                convert hsub using 1
                ring
              have hM1 : M - 1 = (M - 2) + 1 := by omega
              have hc_eq :
                  2 + (2 : ℤ) ^ (M - 1) =
                    2 * (1 + (2 : ℤ) ^ (M - 2)) := by
                rw [hM1, pow_succ]
                ring
              have hp_mul :
                  (2 : ℤ) ^ M * (2 : ℤ) ^ (M - 3) =
                    2 * ((2 : ℤ) ^ (M - 2)) ^ 2 := by
                calc
                  (2 : ℤ) ^ M * (2 : ℤ) ^ (M - 3)
                      = (2 : ℤ) ^ (M + (M - 3)) := by rw [← pow_add]
                  _ = (2 : ℤ) ^ (((M - 2) + (M - 2)) + 1) := by
                    congr 1
                    omega
                  _ = (2 : ℤ) ^ ((M - 2) + (M - 2)) * 2 := by
                    rw [pow_succ]
                  _ = ((2 : ℤ) ^ (M - 2) * (2 : ℤ) ^ (M - 2)) * 2 := by
                    rw [pow_add]
                  _ = 2 * ((2 : ℤ) ^ (M - 2)) ^ 2 := by
                    ring
              have hcomb :
                  (2 + (2 : ℤ) ^ (M - 1)) * (1 - (2 : ℤ) ^ (M - 2)) +
                      (2 : ℤ) ^ M * (2 : ℤ) ^ (M - 3) = 2 := by
                rw [hc_eq, hp_mul]
                ring
              have hg_comb :
                  g ∣
                    (2 + (2 : ℤ) ^ (M - 1)) * (1 - (2 : ℤ) ^ (M - 2)) +
                      (2 : ℤ) ^ M * (2 : ℤ) ^ (M - 3) := by
                exact dvd_add
                  (dvd_mul_of_dvd_left hg_coeff _)
                  (dvd_mul_of_dvd_left hg_right _)
              simpa [hcomb] using hg_comb
            exact hdiv.trans hs_even
          · have hpow_dvd_s : (2 : ℤ) ^ (M - 1) ∣ s := by
              have htwo_ne_zero : (2 : ℤ) ≠ 0 := by norm_num
              have hsub_coeff :
                  r - 1 ≡ (2 : ℤ) ^ (M - 1) - 2 [ZMOD ((2 : ℤ) ^ M)] := by
                have h := hr_mid_neg.sub (Int.ModEq.refl (1 : ℤ))
                convert h using 1
                ring
              have hcoeff_s_zero :
                  ((2 : ℤ) ^ (M - 1) - 2) * s ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
                exact (hsub_coeff.mul_right s).symm.trans hsub_fixed
              have hdiv_pow :
                  (2 : ℤ) ^ M ∣ (((2 : ℤ) ^ (M - 1) - 2) * s) := by
                exact Int.modEq_zero_iff_dvd.mp hcoeff_s_zero
              have hcoeff_eq :
                  (2 : ℤ) ^ (M - 1) - 2 =
                    2 * ((2 : ℤ) ^ (M - 2) - 1) := by
                have hM1 : M - 1 = (M - 2) + 1 := by omega
                rw [hM1, pow_succ]
                ring
              have hpow_eq :
                  (2 : ℤ) ^ M = 2 * (2 : ℤ) ^ (M - 1) := by
                have hM : M = (M - 1) + 1 := by omega
                rw [hM, pow_succ]
                simp [mul_comm]
              have hdiv_cancel :
                  (2 : ℤ) ^ (M - 1) ∣ ((2 : ℤ) ^ (M - 2) - 1) * s := by
                have hdiv' :
                    2 * (2 : ℤ) ^ (M - 1) ∣
                      2 * (((2 : ℤ) ^ (M - 2) - 1) * s) := by
                  simpa [hpow_eq, hcoeff_eq, mul_assoc, mul_comm, mul_left_comm] using hdiv_pow
                exact (mul_dvd_mul_iff_left htwo_ne_zero).mp hdiv'
              rcases hdiv_cancel with ⟨t, ht⟩
              have hpow_mul :
                  (2 : ℤ) ^ (M - 1) * (2 : ℤ) ^ (M - 3) =
                    ((2 : ℤ) ^ (M - 2)) ^ 2 := by
                calc
                  (2 : ℤ) ^ (M - 1) * (2 : ℤ) ^ (M - 3)
                      = (2 : ℤ) ^ ((M - 1) + (M - 3)) := by rw [← pow_add]
                  _ = (2 : ℤ) ^ ((M - 2) + (M - 2)) := by
                    congr 1
                    omega
                  _ = (2 : ℤ) ^ (M - 2) * (2 : ℤ) ^ (M - 2) := by rw [pow_add]
                  _ = ((2 : ℤ) ^ (M - 2)) ^ 2 := by ring
              have hbez :
                  ((2 : ℤ) ^ (M - 2) - 1) * (-((2 : ℤ) ^ (M - 2) + 1)) +
                    (2 : ℤ) ^ (M - 1) * (2 : ℤ) ^ (M - 3) = 1 := by
                rw [hpow_mul]
                ring
              refine ⟨t * (-((2 : ℤ) ^ (M - 2) + 1)) + (2 : ℤ) ^ (M - 3) * s, ?_⟩
              calc
                s = 1 * s := by ring
                _ = (((2 : ℤ) ^ (M - 2) - 1) * (-((2 : ℤ) ^ (M - 2) + 1)) +
                      (2 : ℤ) ^ (M - 1) * (2 : ℤ) ^ (M - 3)) * s := by
                  rw [hbez]
                _ = (((2 : ℤ) ^ (M - 2) - 1) * s) *
                        (-((2 : ℤ) ^ (M - 2) + 1)) +
                      (2 : ℤ) ^ (M - 1) * ((2 : ℤ) ^ (M - 3) * s) := by
                  ring
                _ = ((2 : ℤ) ^ (M - 1) * t) *
                        (-((2 : ℤ) ^ (M - 2) + 1)) +
                      (2 : ℤ) ^ (M - 1) * ((2 : ℤ) ^ (M - 3) * s) := by
                  rw [ht]
                _ = (2 : ℤ) ^ (M - 1) *
                    (t * (-((2 : ℤ) ^ (M - 2) + 1)) + (2 : ℤ) ^ (M - 3) * s) := by
                  ring
            have hdiv : ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ) ∣ (2 : ℤ) ^ (M - 1) := by
              let g : ℤ := ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ)
              change g ∣ (2 : ℤ) ^ (M - 1)
              have hg_left : g ∣ 1 + r := by
                dsimp [g]
                exact Int.gcd_dvd_left (1 + r) ((2 : ℤ) ^ M)
              have hg_right : g ∣ (2 : ℤ) ^ M := by
                dsimp [g]
                exact Int.gcd_dvd_right (1 + r) ((2 : ℤ) ^ M)
              have hcoeff :
                  1 + r ≡ (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
                have h := hr_mid_neg.add_left (1 : ℤ)
                convert h using 1
                ring
              have hdiff_dvd :
                  (2 : ℤ) ^ M ∣ (1 + r) - (2 : ℤ) ^ (M - 1) := by
                apply Int.modEq_zero_iff_dvd.mp
                have h := hcoeff.sub (Int.ModEq.refl ((2 : ℤ) ^ (M - 1)))
                simpa using h
              have hg_diff :
                  g ∣ (1 + r) - (2 : ℤ) ^ (M - 1) :=
                hg_right.trans hdiff_dvd
              have hsub :
                  g ∣ (1 + r) - ((1 + r) - (2 : ℤ) ^ (M - 1)) :=
                dvd_sub hg_left hg_diff
              convert hsub using 1
              ring
            exact hdiv.trans hpow_dvd_s
        have hroot_split :
            r ≡ 1 [ZMOD (orderOf a : ℤ)] ∨
              r ≡ -1 [ZMOD (orderOf a : ℤ)] ∨
                (3 ≤ M ∧
                  (r ≡ 1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] ∨
                    r ≡ -1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)])) := by
          have hmodEq_of_dvd_sub {m x y : ℤ} (h : m ∣ x - y) :
              x ≡ y [ZMOD m] := by
            have hz : x - y ≡ 0 [ZMOD m] := Int.modEq_zero_iff_dvd.mpr h
            have h' := hz.add_right y
            convert h' using 1 <;> ring
          have hpow_dvd_consec :
              ∀ {n : ℕ} {x : ℤ}, (2 : ℤ) ^ n ∣ x * (x + 1) →
                (2 : ℤ) ^ n ∣ x ∨ (2 : ℤ) ^ n ∣ x + 1 := by
            intro n x hx
            have hprime2 : Prime (2 : ℤ) := by exact Int.prime_two
            by_cases hx2 : (2 : ℤ) ∣ x
            · left
              have hnot : ¬ (2 : ℤ) ∣ x + 1 := by
                intro hx1
                have htwo_one : (2 : ℤ) ∣ 1 := by
                  have h := dvd_sub hx1 hx2
                  simpa only [add_sub_cancel_left] using h
                norm_num at htwo_one
              have hcop2 : IsCoprime (2 : ℤ) (x + 1) :=
                (hprime2.coprime_iff_not_dvd).mpr hnot
              exact hcop2.pow_left.dvd_of_dvd_mul_right hx
            · right
              have hcop2 : IsCoprime (2 : ℤ) x :=
                (hprime2.coprime_iff_not_dvd).mpr hx2
              exact hcop2.pow_left.dvd_of_dvd_mul_left hx
          have hr_square_pow : r * r ≡ 1 [ZMOD ((2 : ℤ) ^ M)] := by
            simpa [horder_pow_int] using hr_square_mod
          have hsq_dvd : (2 : ℤ) ^ M ∣ r * r - 1 := by
            apply Int.modEq_zero_iff_dvd.mp
            have h := hr_square_pow.sub (Int.ModEq.refl (1 : ℤ))
            simpa using h
          have hprod_dvd : (2 : ℤ) ^ M ∣ (r - 1) * (r + 1) := by
            convert hsq_dvd using 1
            ring
          by_cases hM0 : M = 0
          · left
            subst M
            rw [horder_pow_int]
            norm_num [Int.ModEq]
          have hM_pos : 0 < M := Nat.pos_of_ne_zero hM0
          have htwo_dvd_pow : (2 : ℤ) ∣ (2 : ℤ) ^ M := by
            have hM_eq : M = (M - 1) + 1 := by omega
            rw [hM_eq, pow_succ]
            exact dvd_mul_left _ _
          have htwo_dvd_sq : (2 : ℤ) ∣ r * r - 1 :=
            htwo_dvd_pow.trans hsq_dvd
          have hodd_r : Odd r := by
            rcases Int.even_or_odd r with hr_even | hr_odd
            · have htwo_rr : (2 : ℤ) ∣ r * r := dvd_mul_of_dvd_left (by rw[← even_iff_two_dvd]; exact hr_even) r
              have htwo_one : (2 : ℤ) ∣ 1 := by
                have h := dvd_sub htwo_rr htwo_dvd_sq
                simpa only [sub_sub_cancel] using h
              norm_num at htwo_one
            · exact hr_odd
          rcases hodd_r with ⟨t, ht⟩
          by_cases hM_ge_three : 3 ≤ M
          · have hM_eq2 : M = (M - 2) + 2 := by omega
            have hpow_rewrite :
                (2 : ℤ) ^ M = 4 * (2 : ℤ) ^ (M - 2) := by
              rw [hM_eq2, pow_add]
              norm_num [pow_two]
              ring
            have hprod_rewrite :
                (r - 1) * (r + 1) = 4 * (t * (t + 1)) := by
              rw [ht]
              ring
            have htprod_dvd : (2 : ℤ) ^ (M - 2) ∣ t * (t + 1) := by
              have h4 :
                  4 * (2 : ℤ) ^ (M - 2) ∣ 4 * (t * (t + 1)) := by
                simpa [hpow_rewrite, hprod_rewrite] using hprod_dvd
              exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4
            have hM_eq1 : M = (M - 1) + 1 := by omega
            have hpowM :
                (2 : ℤ) ^ M = (2 : ℤ) ^ (M - 1) * 2 := by
              rw [hM_eq1, pow_succ]
              simp
            have hlift_minus :
                (2 : ℤ) ^ (M - 1) ∣ r - 1 →
                  r ≡ 1 [ZMOD ((2 : ℤ) ^ M)] ∨
                  r ≡ 1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
              intro hp
              rcases hp with ⟨q, hq⟩
              rcases Int.even_or_odd q with ⟨u, hu⟩ | ⟨u, hu⟩
              · left
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                calc
                  r - 1 = (2 : ℤ) ^ (M - 1) * q := hq
                  _ = (2 : ℤ) ^ (M - 1) * (2 * u) := by rw [hu]; ring
                  _ = (2 : ℤ) ^ M * u := by rw [hpowM]; ring
              · right
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                calc
                  r - (1 + (2 : ℤ) ^ (M - 1))
                      = (r - 1) - (2 : ℤ) ^ (M - 1) := by ring
                  _ = (2 : ℤ) ^ (M - 1) * q - (2 : ℤ) ^ (M - 1) := by rw [hq]
                  _ = (2 : ℤ) ^ (M - 1) * (2 * u + 1) -
                        (2 : ℤ) ^ (M - 1) := by rw [hu]
                  _ = (2 : ℤ) ^ M * u := by rw [hpowM]; ring

            have hlift_plus :
                (2 : ℤ) ^ (M - 1) ∣ r + 1 →
                  r ≡ -1 [ZMOD ((2 : ℤ) ^ M)] ∨
                  r ≡ -1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
              intro hp
              rcases hp with ⟨q, hq⟩
              rcases Int.even_or_odd q with ⟨u, hu⟩ | ⟨u, hu⟩
              · left
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                calc
                  r - (-1 : ℤ) = r + 1 := by ring
                  _ = (2 : ℤ) ^ (M - 1) * q := hq
                  _ = (2 : ℤ) ^ (M - 1) * (2 * u) := by rw [hu]; ring
                  _ = (2 : ℤ) ^ M * u := by rw [hpowM]; ring
              · right
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                calc
                  r - (-1 + (2 : ℤ) ^ (M - 1))
                      = (r + 1) - (2 : ℤ) ^ (M - 1) := by ring
                  _ = (2 : ℤ) ^ (M - 1) * q - (2 : ℤ) ^ (M - 1) := by rw [hq]
                  _ = (2 : ℤ) ^ (M - 1) * (2 * u + 1) -
                        (2 : ℤ) ^ (M - 1) := by rw [hu]
                  _ = (2 : ℤ) ^ M * u := by rw [hpowM]; ring
            rcases hpow_dvd_consec htprod_dvd with ht_dvd | ht1_dvd
            · have hp : (2 : ℤ) ^ (M - 1) ∣ r - 1 := by
                have hM1 : M - 1 = (M - 2) + 1 := by omega
                have hmul : (2 : ℤ) * (2 : ℤ) ^ (M - 2) ∣ 2 * t :=
                  mul_dvd_mul_left (2 : ℤ) ht_dvd
                rw [ht]
                simpa [hM1, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul
              rcases hlift_minus hp with h1 | hmid
              · left
                simpa [horder_pow_int] using h1
              · right
                right
                exact ⟨hM_ge_three, Or.inl hmid⟩
            · have hp : (2 : ℤ) ^ (M - 1) ∣ r + 1 := by
                have hM1 : M - 1 = (M - 2) + 1 := by omega
                have hmul :
                    (2 : ℤ) * (2 : ℤ) ^ (M - 2) ∣ 2 * (t + 1) :=
                  mul_dvd_mul_left (2 : ℤ) ht1_dvd
                rw [ht, show 2 * t + 1 + 1 = 2 * (t + 1) by ring]
                simpa [hM1, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul
              rcases hlift_plus hp with hneg | hmid
              · right
                left
                simpa [horder_pow_int] using hneg
              · right
                right
                exact ⟨hM_ge_three, Or.inr hmid⟩
          · have hM_le_two : M ≤ 2 := by omega
            interval_cases M
            · -- M = 1
              left
              rw [horder_pow_int]
              norm_num
              apply hmodEq_of_dvd_sub
              refine ⟨t, ?_⟩
              rw [ht]
              ring
            · -- M = 2
              rcases Int.even_or_odd t with ⟨u, hu⟩ | ⟨u, hu⟩
              · left
                rw [horder_pow_int]
                norm_num
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                rw [ht, hu]
                ring
              · right
                left
                rw [horder_pow_int]
                norm_num
                apply hmodEq_of_dvd_sub
                refine ⟨u + 1, ?_⟩
                rw [ht, hu]
                ring
        rcases hroot_split with hr_one | hr_neg | hmid
        · exact Or.inl (hcyclic_of_r_one hr_one)
        · exact False.elim (hr_not_flip' hr_neg)
        · rcases hmid with ⟨hM_ge_three, hr_mid_pos | hr_mid_neg⟩
          · exact Or.inr (hlinear_solution_of_nontrivial_root hM_ge_three (Or.inl hr_mid_pos))
          · exact Or.inr (hlinear_solution_of_nontrivial_root hM_ge_three (Or.inr hr_mid_neg))
      rcases hcore with hcycle | hex
      · exact hcycle
      · exact False.elim (hbad hex)
    exact hnonflip_forces_cyclic hr_not_flip
  have hconj_a_inv_zpow : ∀ z : ℤ, b * a ^ z * b⁻¹ = a ^ (-z) := by
    intro z
    calc
      b * a ^ z * b⁻¹ = a ^ (r * z) := hconj_a_zpow z
      _ = a ^ ((-1 : ℤ) * z) := by
        apply (zpow_eq_zpow_iff_modEq (x := a)).2
        exact hflip_mod.mul_right z
      _ = a ^ (-z) := by ring_nf
  have hconj : ∀ z : ℤ, a ^ z * b = b * a ^ (-z) := by
    intro z
    have hz : b * a ^ (-z) * b⁻¹ = a ^ z := by
      simpa using hconj_a_inv_zpow (-z)
    calc
      a ^ z * b = (b * a ^ (-z) * b⁻¹) * b := by rw [hz]
      _ = b * a ^ (-z) := by group
  have hb_sq_order_two : orderOf (b * b) = 2 := by
    have hs_neg : a ^ s = a ^ (-s) := by
      calc
        a ^ s = a ^ (r * s) := hs_fixed_by_r.symm
        _ = b * a ^ s * b⁻¹ := (hconj_a_zpow s).symm
        _ = a ^ (-s) := hconj_a_inv_zpow s
    have hs_sq_one : a ^ s * a ^ s = 1 := by
      calc
        a ^ s * a ^ s = a ^ s * a ^ (-s) := by rw [hs_neg]
        _ = 1 := by simp
    have hsq_one : (b * b) * (b * b) = 1 := by
      calc
        (b * b) * (b * b) = a ^ s * a ^ s := by rw [hs]
        _ = 1 := hs_sq_one
    have hpow : (b * b) ^ 2 = 1 := by simpa [pow_two] using hsq_one
    have hdvd : orderOf (b * b) ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
    have hne_order_one : orderOf (b * b) ≠ 1 := by
      intro horder
      exact hb_sq_ne_one (orderOf_eq_one_iff.mp horder)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact False.elim (hne_order_one h)
    · exact h
  have hb_mul_self : b * b = a ^ (k : ℤ) :=
    hunique_order_two (b * b) (a ^ (k : ℤ)) hb_sq_order_two ha_k_order_two
  exact huppert_I_14_9_generalizedQuaternion_mulEquiv_of_relations
    a b ha_order hconj hb_mul_self hcover hcard

/-- Under the unique-involution hypothesis, every abelian subgroup of `G` is cyclic. -/
public theorem huppert_III_7_6b_isCyclic_of_isMulCommutative_unique_order_two
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G)
    (hunique_order_two : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y)
    (A : Subgroup G) (hAcomm : IsMulCommutative A) :
    IsCyclic A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsMulCommutative A := hAcomm
  have hAp : IsPGroup 2 A := hGp.to_subgroup A
  have : Fact (IsPGroup 2 A) := ⟨hAp⟩
  let Ω : Subgroup A := omega₁ (G := A) (p := 2)
  have hΩelem : IsElementaryAbelian 2 Ω := by
    simpa [Ω] using IsElementaryAbelian.omega₁_of_isMulCommutative (p := 2) (G := A)
  have : IsElementaryAbelian 2 Ω := hΩelem
  have hΩ_card_le_two : Nat.card Ω ≤ 2 := by
    classical
    let f : Ω → Bool := fun x => decide (x = 1)
    have hf_inj : Function.Injective f := by
      intro x y hxy
      by_cases hx1 : x = 1
      · have hy1 : y = 1 := by
          by_contra hy1
          simp [f, hx1, hy1] at hxy
        simp [hx1, hy1]
      · have hy1 : y ≠ 1 := by
          intro hy1
          simp [f, hx1, hy1] at hxy
        apply Subtype.ext
        apply Subtype.ext
        have hxpow : x ^ (2 : ℕ) = 1 := by
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 Ω) x
        have hypow : y ^ (2 : ℕ) = 1 := by
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 Ω) y
        have hxord : orderOf ((x : Ω) : A) = 2 := by
          refine (orderOf_eq_prime_iff (x := ((x : Ω) : A)) (p := 2)).2 ⟨?_, ?_⟩
          · simpa using congrArg Subtype.val hxpow
          · intro hxA1
            exact hx1 (Subtype.ext hxA1)
        have hyord : orderOf ((y : Ω) : A) = 2 := by
          refine (orderOf_eq_prime_iff (x := ((y : Ω) : A)) (p := 2)).2 ⟨?_, ?_⟩
          · simpa using congrArg Subtype.val hypow
          · intro hyA1
            exact hy1 (Subtype.ext hyA1)
        have hxordG : orderOf (((x : Ω) : A) : G) = 2 := by
          simpa [Subgroup.orderOf_coe] using hxord
        have hyordG : orderOf (((y : Ω) : A) : G) = 2 := by
          simpa [Subgroup.orderOf_coe] using hyord
        exact hunique_order_two (((x : Ω) : A) : G) (((y : Ω) : A) : G) hxordG hyordG
    have hcard_le : Nat.card Ω ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf_inj
    simpa using hcard_le
  have hquot_card_le_two : Nat.card (A ⧸ frattini A) ≤ 2 := by
    have hΩ_card_eq_quot : Nat.card Ω = Nat.card (A ⧸ frattini A) := by
      simpa [Ω] using
        section9_c92_omega1_card_eq_card_quotient_frattini_of_commutative (p := 2) A
    simpa [hΩ_card_eq_quot] using hΩ_card_le_two
  have hquot_elem : IsElementaryAbelian 2 (A ⧸ frattini A) := by
    exact isElementaryAbelian_quotient_frattini (R := A) (p := 2)
  have : IsElementaryAbelian 2 (A ⧸ frattini A) := hquot_elem
  have hquot_rank_le_one : generatorRank (A ⧸ frattini A) ≤ 1 := by
    have hquot_card_eq : Nat.card (A ⧸ frattini A) = 2 ^ generatorRank (A ⧸ frattini A) := by
      simpa using elementaryAbelian_card_eq_pow_generatorRank (p := 2) (A ⧸ frattini A)
    by_contra hle
    have htwo_le : 2 ≤ generatorRank (A ⧸ frattini A) :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)
    have hpow_ge : 2 ^ 2 ≤ 2 ^ generatorRank (A ⧸ frattini A) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) htwo_le
    have hpow_le_two : 2 ^ generatorRank (A ⧸ frattini A) ≤ 2 := by
      simpa [hquot_card_eq] using hquot_card_le_two
    have : 4 ≤ 2 := by
      simpa using hpow_ge.trans hpow_le_two
    omega
  have hrank_le_one : generatorRank A ≤ 1 :=
    (generatorRank_le_generatorRank_quotient_frattini (p := 2) A).trans hquot_rank_le_one
  exact isCyclic_of_generatorRank_le_one (G := A) hrank_le_one
/-- Abelian branch of Huppert III.7.5: a noncyclic abelian normal `2`-subgroup
contains a normal elementary abelian subgroup of order `4`. -/
private theorem huppert_III_7_5b_abelian_branch
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G) (N : Subgroup G)
    (hNnorm : N.Normal) (hNcomm : IsMulCommutative N)
    (hN_noncyclic : ¬ IsCyclic N) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ N ∧ Nat.card K = 2 ^ 2 ∧ IsElementaryAbelian 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 G) := ⟨hGp⟩
  have hNp : IsPGroup 2 N := hGp.to_subgroup N
  have : Fact (IsPGroup 2 N) := ⟨hNp⟩
  let : IsMulCommutative N := hNcomm
  let ΩN : Subgroup N := omega₁ (G := N) (p := 2)
  have hΩN_elem : IsElementaryAbelian 2 ΩN := by
    simpa [ΩN] using IsElementaryAbelian.omega₁_of_isMulCommutative (p := 2) (G := N)
  have : IsElementaryAbelian 2 ΩN := hΩN_elem
  have hN_rank_ge_two : 2 ≤ generatorRank N := by
    by_contra hlt
    have hle : generatorRank N ≤ 1 := by omega
    exact hN_noncyclic (isCyclic_of_generatorRank_le_one (G := N) hle)
  have hquot_rank_ge_two : 2 ≤ generatorRank (N ⧸ frattini N) :=
    hN_rank_ge_two.trans (generatorRank_le_generatorRank_quotient_frattini (p := 2) N)
  have hΩN_card_eq : Nat.card ΩN = Nat.card (N ⧸ frattini N) := by
    simpa [ΩN] using
      section9_c92_omega1_card_eq_card_quotient_frattini_of_commutative (p := 2) N
  have hΩN_card_ge : 2 ^ 2 ≤ Nat.card ΩN := by
    have hquot_elem : IsElementaryAbelian 2 (N ⧸ frattini N) :=
      isElementaryAbelian_quotient_frattini (R := N) (p := 2)
    let : IsElementaryAbelian 2 (N ⧸ frattini N) := hquot_elem
    have hpow_le : 2 ^ 2 ≤ 2 ^ generatorRank (N ⧸ frattini N) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hquot_rank_ge_two
    have hcard_ge : 2 ^ generatorRank (N ⧸ frattini N) ≤ Nat.card (N ⧸ frattini N) :=
      section9_c92_elementaryAbelian_card_ge_pow_generatorRank (p := 2) (N ⧸ frattini N)
    simpa [hΩN_card_eq] using hpow_le.trans hcard_ge
  let Ω : Subgroup G := ΩN.map N.subtype
  have hΩ_normal : Ω.Normal := by
    let : N.Normal := hNnorm
    let : ΩN.Characteristic := by
      simpa [ΩN] using (omega₁_characteristic (G := N) (p := 2))
    simpa [Ω] using (inferInstance : (ΩN.map N.subtype).Normal)
  have hΩ_le_N : Ω ≤ N := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hΩ_card_eq : Nat.card Ω = Nat.card ΩN :=
    Subgroup.card_map_of_injective (K := ΩN) (f := N.subtype) N.subtype_injective
  have hΩp : IsPGroup 2 Ω := hGp.to_subgroup Ω
  obtain ⟨m, hmΩ⟩ := hΩp.exists_card_eq
  have hm_ge_two : 2 ≤ m := by
    have hpow : 2 ^ 2 ≤ 2 ^ m := by
      calc
        2 ^ 2 ≤ Nat.card ΩN := hΩN_card_ge
        _ = Nat.card Ω := hΩ_card_eq.symm
        _ = 2 ^ m := hmΩ
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  obtain ⟨K, hK_normal, hK_le_Ω, hKcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := G) (p := 2)
      (N := Ω) hΩ_normal hmΩ 2 hm_ge_two
  have hK_le_N : K ≤ N := hK_le_Ω.trans hΩ_le_N
  have hKpow : ∀ x : K, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    change ((x : G) ^ 2 = 1)
    have hxΩ : (x : G) ∈ Ω := hK_le_Ω x.property
    rcases Subgroup.mem_map.mp hxΩ with ⟨y, hyΩN, hyx⟩
    have hypow : (⟨y, hyΩN⟩ : ΩN) ^ 2 = 1 := by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 ΩN) ⟨y, hyΩN⟩
    have hy_pow_G : ((y : N) : G) ^ 2 = 1 := by
      simpa using congrArg (fun z : ΩN => (((z : ΩN) : N) : G)) hypow
    simpa [← hyx] using hy_pow_G
  exact ⟨K, hK_normal, hK_le_N, hKcard,
    isElementaryAbelian_of_card_eq_p_sq_of_forall_pow_eq_one (S := K) (p := 2) hKcard hKpow⟩

/-- The cyclic quotient branch in Huppert III.7.5(b).  If `N/Z` is cyclic for a
central subgroup `Z ≤ N`, then `N/Z(N)` is cyclic, hence `N` is abelian. -/
private theorem huppert_III_7_5b_cyclic_quotient_branch
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G) (N Z : Subgroup G)
    (hNnorm : N.Normal) (hN_noncyclic : ¬ IsCyclic N)
    (hZnorm : Z.Normal) (hZ_le_center : Z ≤ Subgroup.center G)
    (hNbar_cyclic : IsCyclic (N.map (QuotientGroup.mk' Z))) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ N ∧ Nat.card K = 2 ^ 2 ∧ IsElementaryAbelian 2 K := by
  classical
  have : Z.Normal := hZnorm
  let q : G →* G ⧸ Z := QuotientGroup.mk' Z
  let Nbar : Subgroup (G ⧸ Z) := N.map q
  let qN : N →* Nbar := q.subgroupMap N
  have hqN_surj : Function.Surjective qN := MonoidHom.subgroupMap_surjective q N
  have hqN_range_cyclic : IsCyclic qN.range := by
    let : IsCyclic Nbar := by simpa [Nbar, q] using hNbar_cyclic
    exact Subgroup.isCyclic_of_le le_top
  have hquot_ker_cyclic : IsCyclic (N ⧸ qN.ker) :=
    (MulEquiv.isCyclic (QuotientGroup.quotientKerEquivRange qN)).2 hqN_range_cyclic
  have hker_le_centerN : qN.ker ≤ Subgroup.center N := by
    intro z hz
    have hzq : q ((z : N) : G) = 1 := by
      have hzqN : qN z = 1 := MonoidHom.mem_ker.mp hz
      exact congrArg Subtype.val hzqN
    have hzZ : ((z : N) : G) ∈ Z :=
      (QuotientGroup.eq_one_iff (N := Z) (x := ((z : N) : G))).1 (by simpa [q] using hzq)
    have hzcenter : ((z : N) : G) ∈ Subgroup.center G := hZ_le_center hzZ
    rw [Subgroup.mem_center_iff]
    intro n
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp hzcenter) (n : G)
  let π : N ⧸ qN.ker →* N ⧸ Subgroup.center N :=
    QuotientGroup.map qN.ker (Subgroup.center N) (MonoidHom.id N) (by simpa using hker_le_centerN)
  have hπ_surj : Function.Surjective π := by
    intro y
    refine Quotient.inductionOn' y ?_
    intro n
    exact ⟨(QuotientGroup.mk' qN.ker n), rfl⟩
  have hcenter_quot_cyclic : IsCyclic (N ⧸ Subgroup.center N) := by
    let : IsCyclic (N ⧸ qN.ker) := hquot_ker_cyclic
    exact isCyclic_of_surjective π hπ_surj
  have hNcomm : IsMulCommutative N := lemma_4_1 (G := N) hcenter_quot_cyclic
  exact huppert_III_7_5b_abelian_branch (G := G) hGp N hNnorm hNcomm hN_noncyclic
/-- In a finite `p`-group, a subgroup of prime index is maximal and normal. -/
private theorem huppert_III_7_5b_covby_top_of_index_eq_prime
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (h : IsPGroup p G) {H : Subgroup G} (h_idx : H.index = p) :
    CovBy H ⊤ ∧ H.Normal := by
  have hp : p.Prime := Fact.out
  have (a b : Prop) : a ∧ b ↔ a ∧ (a → b) := by tauto
  rw [this]
  constructor
  · refine ⟨Ne.lt_top (fun htop => ?_), fun K hHK hKtop => ?_⟩
    · have hp_one : p = 1 := by
        simpa [htop] using h_idx.symm
      exact hp.ne_one hp_one
    · have hrel := Subgroup.relIndex_mul_index hHK.le
      have hprime : (H.relIndex K * K.index).Prime := by rwa [hrel, h_idx]
      rcases Nat.prime_mul_iff.mp hprime with ⟨_, hindex_one⟩ | ⟨_, hrel_one⟩
      · rw [Subgroup.index_eq_one] at hindex_one
        simp [hindex_one] at hKtop
      · rw [Subgroup.relIndex_eq_one] at hrel_one
        exact hHK.not_ge hrel_one
  · intro hmax
    simp only [covBy_top_iff] at hmax
    have hnil : Group.IsNilpotent G := IsPGroup.isNilpotent (p := p) h
    exact Subgroup.NormalizerCondition.normal_of_coatom H
      (Group.normalizerCondition_of_isNilpotent (G := G)) hmax

/-- In a finite `2`-group, any subgroup whose index divides `2` contains the Frattini subgroup. -/
private theorem huppert_III_7_5b_frattini_le_of_index_dvd_two
    {G : Type u} [Group G] [Finite G] (hGp : IsPGroup 2 G)
    {H : Subgroup G} (hidx : H.index ∣ 2) :
    frattini G ≤ H := by
  have hidx_ne_zero : H.index ≠ 0 := by
    intro hzero
    simp [hzero] at hidx
  have hidx_cases : H.index = 1 ∨ H.index = 2 := by
    have hle : H.index ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hidx
    omega
  rcases hidx_cases with hidx_one | hidx_two
  · have htop : H = ⊤ := (Subgroup.index_eq_one).1 hidx_one
    intro x hx
    simp [htop]
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcov :=
      huppert_III_7_5b_covby_top_of_index_eq_prime (p := 2) (G := G) hGp hidx_two
    exact frattini_le_coatom (by simpa [covBy_top_iff] using hcov.1)
/-- The final order-eight branch in Huppert III.7.5(b).  This is the point where
Huppert uses the Frattini condition: a noncommutative lifted subgroup of order
`8` cannot force every normal subgroup of order `4` to be cyclic. -/
private theorem huppert_III_7_5b_noncomm_order_eight_branch
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G) (M N : Subgroup G)
    (hMnorm : M.Normal) (hM_le_N : M ≤ N) (hM_le_phi : M ≤ frattini G)
    (hMcard : Nat.card M = 2 ^ 3) (hMnoncomm : ¬ IsMulCommutative M) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ N ∧ Nat.card K = 2 ^ 2 ∧ IsElementaryAbelian 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 G) := ⟨hGp⟩
  obtain ⟨L, hL_normal, hL_le_M, hL_card⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := G) (p := 2)
      (N := M) hMnorm hMcard 2 (by norm_num : 2 ≤ 3)
  by_cases hL_elem : IsElementaryAbelian 2 L
  · exact ⟨L, hL_normal, hL_le_M.trans hM_le_N, hL_card, hL_elem⟩
  · have hL_comm : IsMulCommutative L :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := L) hL_card
    have hL_cyclic : IsCyclic L := by
      by_contra hL_not_cyclic
      have hL_exp : Monoid.exponent L = 2 :=
        (not_isCyclic_iff_exponent_eq_prime (p := 2) Nat.prime_two hL_card).1
          hL_not_cyclic
      have hL_elem' : IsElementaryAbelian 2 L :=
        { toIsMulCommutative := hL_comm
          exponent_dvd_p := by simp [hL_exp] }
      exact hL_elem hL_elem'
    let : L.Normal := hL_normal
    let : IsCyclic L := hL_cyclic
    let φ : G →* MulAut L := MulAut.conjNormal (H := L)
    have hAutL_card : Nat.card (MulAut L) = 2 := by
      rw [IsCyclic.card_mulAut, hL_card,
        Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 2)]
      norm_num
    have hker_index_dvd_two : φ.ker.index ∣ 2 := by
      rw [Subgroup.index_ker]
      simpa [hAutL_card] using (Subgroup.card_subgroup_dvd_card φ.range)
    have hPhi_le_ker : frattini G ≤ φ.ker :=
      huppert_III_7_5b_frattini_le_of_index_dvd_two (G := G) hGp hker_index_dvd_two
    have hM_le_ker : M ≤ φ.ker := hM_le_phi.trans hPhi_le_ker
    let LM : Subgroup M := L.subgroupOf M
    have hLM_le_center : LM ≤ Subgroup.center M := by
      intro l hl
      rw [Subgroup.mem_center_iff]
      intro m
      apply Subtype.ext
      have hlL : ((l : M) : G) ∈ L := by
        simpa [LM, Subgroup.mem_subgroupOf] using hl
      have hmker : (m : G) ∈ φ.ker := hM_le_ker m.property
      have hfix :
          MulAut.conjNormal (H := L) (m : G) ⟨((l : M) : G), hlL⟩ =
            ⟨((l : M) : G), hlL⟩ := by
        have hφm : φ (m : G) = 1 := MonoidHom.mem_ker.mp hmker
        simp [φ, hφm]
      have hconj : (m : G) * ((l : M) : G) * (m : G)⁻¹ = ((l : M) : G) := by
        simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using congrArg Subtype.val hfix
      have hcommG : (m : G) * ((l : M) : G) = ((l : M) : G) * (m : G) := by
        calc
          (m : G) * ((l : M) : G) =
              ((m : G) * ((l : M) : G) * (m : G)⁻¹) * (m : G) := by
                simp [mul_assoc]
          _ = ((l : M) : G) * (m : G) := by rw [hconj]
      simpa using hcommG
    have : LM.Normal := by
      simpa [LM] using (inferInstance : (L.subgroupOf M).Normal)
    have hLM_card_eq : Nat.card LM = Nat.card L := by
      simpa [LM] using Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL_le_M).toEquiv
    have hLM_card : Nat.card LM = 2 ^ 2 := hLM_card_eq.trans hL_card
    have hM_quot_LM_card : Nat.card (M ⧸ LM) = 2 := by
      have hmul := (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := LM)).symm
      rw [hLM_card, hMcard] at hmul
      have hmul' : Nat.card (M ⧸ LM) * (2 ^ 2) = 2 * (2 ^ 2) := by
        norm_num at hmul ⊢
        exact hmul
      exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2 ^ 2) hmul'
    have hM_quot_LM_cyclic : IsCyclic (M ⧸ LM) :=
      isCyclic_of_prime_card (α := M ⧸ LM) (p := 2) (by simpa using hM_quot_LM_card)
    let π : M ⧸ LM →* M ⧸ Subgroup.center M :=
      QuotientGroup.map LM (Subgroup.center M) (MonoidHom.id M) (by simpa using hLM_le_center)
    have hπ_surj : Function.Surjective π := by
      intro y
      refine Quotient.inductionOn' y ?_
      intro m
      exact ⟨QuotientGroup.mk' LM m, rfl⟩
    have hcenter_quot_cyclic : IsCyclic (M ⧸ Subgroup.center M) := by
      let : IsCyclic (M ⧸ LM) := hM_quot_LM_cyclic
      exact isCyclic_of_surjective π hπ_surj
    have hM_comm : IsMulCommutative M := lemma_4_1 (G := M) hcenter_quot_cyclic
    exact False.elim (hMnoncomm hM_comm)

/-- Huppert III.7.5(b), for a normal noncyclic subgroup contained in the Frattini subgroup. -/
private theorem huppert_III_7_5b_exists_normal_elementaryAbelian_order_four_of_noncyclic_frattini_aux
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G) (N : Subgroup G)
    (hNnorm : N.Normal) (hN_le_phi : N ≤ frattini G)
    (hN_noncyclic : ¬ IsCyclic N) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ N ∧ Nat.card K = 2 ^ 2 ∧ IsElementaryAbelian 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let rec aux {S : Type u} [Group S] [Finite S] [Fact (IsPGroup 2 S)]
      (N : Subgroup S) (hNnorm : N.Normal) (hN_le_phi : N ≤ frattini S)
      (hN_noncyclic : ¬ IsCyclic N) :
      ∃ K : Subgroup S, K.Normal ∧ K ≤ N ∧ Nat.card K = 2 ^ 2 ∧ IsElementaryAbelian 2 K := by
    have hSp : IsPGroup 2 S := Fact.out
    let : N.Normal := hNnorm
    have hN_nontrivial : Nontrivial N := Nontrivial.of_not_isCyclic hN_noncyclic
    have hN_ne_bot : N ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot N).1 hN_nontrivial
    obtain ⟨Z, hZ_normal, hZ_le_N, hZ_card, hZ_le_center⟩ :=
      exists_central_normal_subgroup_card_eq_prime_of_nontrivial_normal
        (G := S) (p := 2) N hN_ne_bot
    let : Z.Normal := hZ_normal
    let q : S →* S ⧸ Z := QuotientGroup.mk' Z
    let Nbar : Subgroup (S ⧸ Z) := N.map q
    have hNbar_normal : Nbar.Normal := by
      simpa [Nbar, q] using (QuotientGroup.map_normal Z N)
    let : Nbar.Normal := hNbar_normal
    have hNbar_le_phi : Nbar ≤ frattini (S ⧸ Z) := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨n, hnN, rfl⟩
      have hphi_le_comap : frattini S ≤ (frattini (S ⧸ Z)).comap q :=
        frattini_le_comap_frattini_of_surjective (G := S) (H := S ⧸ Z) (φ := q)
          (QuotientGroup.mk'_surjective Z)
      exact hphi_le_comap (hN_le_phi hnN)
    by_cases hNbar_cyclic : IsCyclic Nbar
    · exact
        huppert_III_7_5b_cyclic_quotient_branch (G := S) hSp N Z hNnorm hN_noncyclic
          hZ_normal hZ_le_center (by simpa [Nbar, q] using hNbar_cyclic)
    · have hQ_card : Nat.card S = Nat.card (S ⧸ Z) * 2 := by
        calc
          Nat.card S = Nat.card (S ⧸ Z) * Nat.card Z := by
            simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := S) (s := Z))
          _ = Nat.card (S ⧸ Z) * 2 := by rw [hZ_card]
      have hQ_lt : Nat.card (S ⧸ Z) < Nat.card S := by
        rw [hQ_card]
        have hlt := Nat.mul_lt_mul_of_pos_left (by decide : 1 < 2)
          (Nat.card_pos (α := S ⧸ Z))
        rw [mul_one] at hlt
        exact hlt
      have hQp : IsPGroup 2 (S ⧸ Z) := hSp.to_quotient Z
      let : Fact (IsPGroup 2 (S ⧸ Z)) := ⟨hQp⟩
      obtain ⟨Kbar, hKbar_normal, hKbar_le_Nbar, hKbar_card, hKbar_elem⟩ :=
        aux (S := S ⧸ Z) Nbar hNbar_normal hNbar_le_phi hNbar_cyclic
      let : Kbar.Normal := hKbar_normal
      let M : Subgroup S := Kbar.comap q
      have hM_normal : M.Normal := by
        simpa [M, q] using (inferInstance : (Kbar.comap (QuotientGroup.mk' Z)).Normal)
      let : M.Normal := hM_normal
      have hker_le_N : q.ker ≤ N := by
        simpa [q, QuotientGroup.ker_mk'] using hZ_le_N
      have hNbar_comap_eq : Nbar.comap q = N := by
        simpa [Nbar] using (Subgroup.comap_map_eq_self (f := q) (H := N) hker_le_N)
      have hM_le_N : M ≤ N := by
        have hcomap_le : Kbar.comap q ≤ Nbar.comap q := Subgroup.comap_mono hKbar_le_Nbar
        simpa [M, hNbar_comap_eq] using hcomap_le
      have hM_le_phi : M ≤ frattini S := hM_le_N.trans hN_le_phi
      have hM_card : Nat.card M = 2 ^ 3 := by
        have hcardQuotM : Nat.card (M ⧸ q.ker.subgroupOf M) = Nat.card Kbar := by
          simpa [M] using
            (card_quotient_subgroupOf_comap_eq (f := q) (hf := QuotientGroup.mk'_surjective Z)
              (H := Kbar))
        have hcardKerSub : Nat.card (q.ker.subgroupOf M) = Nat.card Z := by
          have hcardKerSub' : Nat.card (q.ker.subgroupOf M) = Nat.card q.ker := by
            exact Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (Subgroup.ker_le_comap (f := q) (H := Kbar))).toEquiv
          rw [hcardKerSub']
          simp [q, QuotientGroup.ker_mk']
        calc
          Nat.card M = Nat.card (M ⧸ q.ker.subgroupOf M) * Nat.card (q.ker.subgroupOf M) := by
            simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := q.ker.subgroupOf M))
          _ = 2 ^ 2 * 2 := by rw [hcardQuotM, hcardKerSub, hKbar_card, hZ_card]
          _ = 2 ^ 3 := by ring_nf
      have hM_noncyclic : ¬ IsCyclic M := by
        intro hMcyclic
        have hMmap_cyclic : IsCyclic (M.map q) := by
          let : IsCyclic M := hMcyclic
          exact isCyclic_of_surjective (q.subgroupMap M) (MonoidHom.subgroupMap_surjective q M)
        have hMmap_eq : M.map q = Kbar := by
          simpa [M] using
            (Subgroup.map_comap_eq_self_of_surjective (f := q) (h := QuotientGroup.mk'_surjective Z)
              Kbar)
        have hKbar_cyclic : IsCyclic Kbar := by
          rw [← hMmap_eq]
          exact hMmap_cyclic
        have : IsElementaryAbelian 2 Kbar := hKbar_elem
        exact (IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) (A := Kbar) hKbar_card)
          hKbar_cyclic
      by_cases hMcomm : IsMulCommutative M
      · obtain ⟨K, hK_normal, hK_le_M, hK_card, hK_elem⟩ :=
          huppert_III_7_5b_abelian_branch (G := S) hSp M hM_normal hMcomm hM_noncyclic
        exact ⟨K, hK_normal, hK_le_M.trans hM_le_N, hK_card, hK_elem⟩
      · exact
          huppert_III_7_5b_noncomm_order_eight_branch (G := S) hSp M N hM_normal hM_le_N
            hM_le_phi hM_card hMcomm
  termination_by Nat.card S
  decreasing_by
    exact hQ_lt
  have : Fact (IsPGroup 2 G) := ⟨hGp⟩
  exact aux (S := G) N hNnorm hN_le_phi hN_noncyclic

/-- Huppert III.7.5(b), in the only form needed for III.7.6(b). -/
private theorem huppert_III_7_5b_exists_normal_elementaryAbelian_order_four_of_noncyclic_frattini
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G) (hPhi_noncyclic : ¬ IsCyclic (frattini G)) :
    ∃ K : Subgroup G,
      K.Normal ∧ K ≤ frattini G ∧ Nat.card K = 2 ^ 2 ∧ IsElementaryAbelian 2 K := by
  classical
  exact
    huppert_III_7_5b_exists_normal_elementaryAbelian_order_four_of_noncyclic_frattini_aux
      (G := G) hGp (frattini G) inferInstance le_rfl hPhi_noncyclic

/-- Huppert III.7.5(b), in the only form needed for III.7.6(b). -/
private theorem huppert_III_7_6b_frattini_isCyclic_of_unique_order_two
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G)
    (hunique_order_two : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y) :
    IsCyclic (frattini G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hPhi_noncyclic
  obtain ⟨K, _hK_normal, _hK_le_phi, hKcard, hKelem⟩ :=
    huppert_III_7_5b_exists_normal_elementaryAbelian_order_four_of_noncyclic_frattini
      (G := G) hGp hPhi_noncyclic
  have : IsElementaryAbelian 2 K := hKelem
  have hK_cyclic : IsCyclic K :=
    huppert_III_7_6b_isCyclic_of_isMulCommutative_unique_order_two
      (G := G) hGp hunique_order_two K hKelem.toIsMulCommutative
  exact (IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) (A := K) hKcard) hK_cyclic
/-- The final maximal-abelian-normal step in Huppert III.7.6(b). -/
private theorem huppert_III_7_6b_index_eq_two_of_maximal_normal_abelian
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G)
    (hnot_cyclic : ¬ IsCyclic G)
    (hunique_order_two : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y)
    (A : Subgroup G)
    (hPhi_le_A : frattini G ≤ A)
    (hAnorm : A.Normal)
    (hAcomm : IsMulCommutative A)
    (hAmax : ∀ B : Subgroup G, B.Normal → IsMulCommutative B → A ≤ B → B = A) :
    A.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 G) := ⟨hGp⟩
  let : A.Normal := hAnorm
  have hA_cyclic : IsCyclic A :=
    huppert_III_7_6b_isCyclic_of_isMulCommutative_unique_order_two
      (G := G) hGp hunique_order_two A hAcomm
  have hAcent_le : Subgroup.centralizer (A : Set G) ≤ A :=
    maximal_normal_abelian_selfCentralizing_local (G := G) (p := 2)
      A hAnorm hAcomm hAmax
  have hA_le_cent : A ≤ Subgroup.centralizer (A : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hAcomm
  have hAcent_eq : Subgroup.centralizer (A : Set G) = A :=
    le_antisymm hAcent_le hA_le_cent
  have hquot_elem : IsElementaryAbelian 2 (G ⧸ A) := by
    refine
      { toIsMulCommutative := ?_
        exponent_dvd_p := ?_ }
    · have hcomm_le : _root_.commutator G ≤ A :=
        (commutator_le_frattini_of_isPGroup (R := G) (p := 2)).trans hPhi_le_A
      exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := A)).2 hcomm_le
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro x
      refine QuotientGroup.induction_on x ?_
      intro g
      have hgpow : g ^ 2 ∈ A :=
        hPhi_le_A (pth_power_mem_frattini_of_isPGroup (R := G) (p := 2) g)
      exact (QuotientGroup.eq_one_iff (N := A) (x := g ^ 2)).2 (by simpa using hgpow)
  let : IsElementaryAbelian 2 (G ⧸ A) := hquot_elem
  by_cases hquot_cyclic : IsCyclic (G ⧸ A)
  · have hquot_not_subsingleton : ¬ Subsingleton (G ⧸ A) := by
      intro hsub
      have hAtop : A = ⊤ := (QuotientGroup.subsingleton_iff (N := A)).1 hsub
      have htop_cyclic : IsCyclic (⊤ : Subgroup G) := by
        rw [← hAtop]
        exact hA_cyclic
      exact hnot_cyclic ((Subgroup.topEquiv (G := G)).isCyclic.mp htop_cyclic)
    have hcard_dvd_two : Nat.card (G ⧸ A) ∣ 2 := by
      simpa [hquot_cyclic.exponent_eq_card] using
        (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ A))
    have hcard_ne_one : Nat.card (G ⧸ A) ≠ 1 := by
      intro hcard_one
      have hsub : Subsingleton (G ⧸ A) := (Nat.card_eq_one_iff_unique.mp hcard_one).1
      exact hquot_not_subsingleton hsub
    have hcard_eq_two : Nat.card (G ⧸ A) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hcard_dvd_two with h | h
      · exact False.elim (hcard_ne_one h)
      · exact h
    simpa [Subgroup.index_eq_card] using hcard_eq_two
  · have hquot_not_subsingleton : ¬ Subsingleton (G ⧸ A) := by
      intro hsub
      have hAtop : A = ⊤ := (QuotientGroup.subsingleton_iff (N := A)).1 hsub
      have htop_cyclic : IsCyclic (⊤ : Subgroup G) := by
        rw [← hAtop]
        exact hA_cyclic
      exact hnot_cyclic ((Subgroup.topEquiv (G := G)).isCyclic.mp htop_cyclic)
    obtain ⟨aA, haA_top⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := A)).1 hA_cyclic
    let a : G := (aA : G)
    have ha_zpowers : Subgroup.zpowers a = A := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_zpowers_iff.mp hx with ⟨z, hz⟩
        rw [← hz]
        exact A.zpow_mem aA.property z
      · intro hxA
        have hxA_top : (⟨x, hxA⟩ : A) ∈ (⊤ : Subgroup A) := by simp
        have hxA_zpow : (⟨x, hxA⟩ : A) ∈ Subgroup.zpowers aA := by
          rw [haA_top]
          exact hxA_top
        rcases Subgroup.mem_zpowers_iff.mp hxA_zpow with ⟨z, hz⟩
        refine Subgroup.mem_zpowers_iff.mpr ⟨z, ?_⟩
        exact Subtype.ext_iff.mp hz
    have hA_ne_bot : A ≠ ⊥ := by
      intro hAbot
      have hAtop : A = ⊤ := by
        apply eq_top_iff.2
        intro g _hg
        apply hAcent_le
        rw [Subgroup.mem_centralizer_iff]
        intro x hxA
        have hx_one : x = 1 := by
          have hxbot : x ∈ (⊥ : Subgroup G) := by simpa [hAbot] using hxA
          simpa using hxbot
        simp [hx_one]
      have htop_cyclic : IsCyclic (⊤ : Subgroup G) := by
        rw [← hAtop]
        exact hA_cyclic
      exact hnot_cyclic ((Subgroup.topEquiv (G := G)).isCyclic.mp htop_cyclic)
    have hA_card_ne_one : Nat.card A ≠ 1 := by
      intro hcard_one
      exact hA_ne_bot (Subgroup.card_eq_one.mp hcard_one)
    have hAp : IsPGroup 2 A := hGp.to_subgroup A
    obtain ⟨nA, hA_card_pow⟩ := hAp.exists_card_eq
    have hnA_ne_zero : nA ≠ 0 := by
      intro hnA0
      exact hA_card_ne_one (by simpa [hnA0] using hA_card_pow)
    let k : ℕ := 2 ^ (nA - 1)
    have : NeZero k := ⟨pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)⟩
    have hA_card_two_mul : Nat.card A = 2 * k := by
      have hnA : nA = (nA - 1) + 1 := by omega
      calc
        Nat.card A = 2 ^ nA := hA_card_pow
        _ = 2 ^ ((nA - 1) + 1) := congrArg (fun m : ℕ => 2 ^ m) hnA
        _ = 2 ^ (nA - 1) * 2 := by rw [pow_succ]
        _ = k * 2 := by rfl
        _ = 2 * k := by ring
    have ha_order_G : orderOf a = 2 * k := by
      calc
        orderOf a = Nat.card (Subgroup.zpowers a) := (Nat.card_zpowers a).symm
        _ = Nat.card A := by rw [ha_zpowers]
        _ = 2 * k := hA_card_two_mul
    let π : G →* G ⧸ A := QuotientGroup.mk' A
    have hinverts_of_quot_order_two :
        ∀ q : G ⧸ A, orderOf q = 2 → ∀ b : G, π b = q →
          ∀ z : ℤ, a ^ z * b = b * a ^ (-z) := by
      intro q hq_order b hbq
      let Bbar : Subgroup (G ⧸ A) := Subgroup.zpowers q
      let B : Subgroup G := Bbar.comap π
      have hBbar_normal : Bbar.Normal := by
        let : IsMulCommutative (G ⧸ A) := hquot_elem.toIsMulCommutative
        infer_instance
      have hB_normal : B.Normal := by
        dsimp [B]
        exact hBbar_normal.comap π
      let : B.Normal := hB_normal
      have hA_le_B : A ≤ B := by
        intro g hgA
        change π g ∈ Bbar
        have hπg : π g = 1 := (QuotientGroup.eq_one_iff (N := A) (x := g)).2 hgA
        simp [Bbar, hπg]
      let A_B : Subgroup B := A.subgroupOf B
      have hA_B_normal : A_B.Normal := by
        dsimp [A_B]
        exact Subgroup.Normal.subgroupOf hAnorm B
      let : A_B.Normal := hA_B_normal
      let aB : B := ⟨a, hA_le_B (by rw [← ha_zpowers]; exact Subgroup.mem_zpowers a)⟩
      have hA_B_eq : Subgroup.zpowers aB = A_B := by
        ext x
        constructor
        · intro hx
          rcases Subgroup.mem_zpowers_iff.mp hx with ⟨z, hz⟩
          change ((x : B) : G) ∈ A
          rw [← ha_zpowers]
          refine Subgroup.mem_zpowers_iff.mpr ⟨z, ?_⟩
          exact congrArg (fun y : B => (y : G)) hz
        · intro hxA
          change ((x : B) : G) ∈ A at hxA
          rw [← ha_zpowers] at hxA
          rcases Subgroup.mem_zpowers_iff.mp hxA with ⟨z, hz⟩
          refine Subgroup.mem_zpowers_iff.mpr ⟨z, ?_⟩
          apply Subtype.ext
          exact hz
      have hBbar_card : Nat.card Bbar = 2 := by
        simpa [Bbar, Nat.card_zpowers] using hq_order
      have hker_sub_eq : π.ker.subgroupOf B = A_B := by
        ext x
        change ((x : B) : G) ∈ π.ker ↔ ((x : B) : G) ∈ A
        simp [π]
      have hA_B_index : A_B.index = 2 := by
        calc
          A_B.index = Nat.card (B ⧸ A_B) := Subgroup.index_eq_card A_B
          _ = Nat.card (B ⧸ π.ker.subgroupOf B) := by rw [hker_sub_eq]
          _ = Nat.card Bbar := card_quotient_subgroupOf_comap_eq (f := π)
              (hf := QuotientGroup.mk'_surjective A) (H := Bbar)
          _ = 2 := hBbar_card
      have hq_ne_one : q ≠ 1 := by
        intro hq1
        have : orderOf q = 1 := orderOf_eq_one_iff.mpr hq1
        omega
      have hb_not_A : b ∉ A := by
        intro hbA
        have hb_one : π b = 1 := (QuotientGroup.eq_one_iff (N := A) (x := b)).2 hbA
        rw [hbq] at hb_one
        exact hq_ne_one hb_one
      have hbB : b ∈ B := by
        change π b ∈ Bbar
        rw [hbq]
        exact Subgroup.mem_zpowers q
      let bB : B := ⟨b, hbB⟩
      have hbB_not_A_B : bB ∉ A_B := by
        intro hbA
        exact hb_not_A hbA
      have hA_B_card : Nat.card A_B = Nat.card A := natCard_subgroupOf_eq A B hA_le_B
      have hB_card : Nat.card B = 4 * k := by
        calc
          Nat.card B = Nat.card A_B * A_B.index := (Subgroup.card_mul_index A_B).symm
          _ = Nat.card A * 2 := by rw [hA_B_card, hA_B_index]
          _ = (2 * k) * 2 := by rw [hA_card_two_mul]
          _ = 4 * k := by ring
      have haB_order : orderOf aB = 2 * k := by
        simpa [aB, a, Subgroup.orderOf_coe] using ha_order_G
      have hB_not_cyclic : ¬ IsCyclic B := by
        intro hBcyclic
        have hBcomm : IsMulCommutative B := by
          let : IsCyclic B := hBcyclic
          let : CommGroup B := hBcyclic.commGroup
          infer_instance
        have hB_eq_A : B = A := hAmax B hB_normal hBcomm hA_le_B
        have hA_B_top : A_B = ⊤ := by
          apply eq_top_iff.2
          intro x _hx
          change ((x : B) : G) ∈ A
          rw [← hB_eq_A]
          exact x.property
        have hindex_one : A_B.index = 1 := by
          rw [hA_B_top]
          simp
        have : (2 : ℕ) = 1 := hA_B_index.symm.trans hindex_one
        norm_num at this
      have hunique_B : ∀ x y : B, orderOf x = 2 → orderOf y = 2 → x = y := by
        intro x y hx hy
        apply Subtype.ext
        exact hunique_order_two (x : G) (y : G)
          (by simpa [Subgroup.orderOf_coe] using hx)
          (by simpa [Subgroup.orderOf_coe] using hy)
      have hBinv :=
        huppert_I_14_9_conj_inverts_of_cyclic_index_two
          (G := B) (k := k) A_B aB bB hA_B_eq hA_B_index haB_order
          hbB_not_A_B hunique_B hB_not_cyclic hB_card (hGp.to_subgroup B)
      intro z
      have hz := congrArg (fun x : B => (x : G)) (hBinv z)
      simpa [aB, bB, a] using hz
    have hquot_has_nonone : ∃ x : G ⧸ A, x ≠ 1 := by
      by_contra hnone
      push Not at hnone
      have hsub : Subsingleton (G ⧸ A) := ⟨fun x y => by rw [hnone x, hnone y]⟩
      exact hquot_not_subsingleton hsub
    obtain ⟨x, hx_ne_one⟩ := hquot_has_nonone
    have hx_pow : x ^ (2 : ℕ) = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ A)) x
    have hx_order : orderOf x = 2 :=
      (orderOf_eq_prime_iff (x := x) (p := 2)).2 ⟨hx_pow, hx_ne_one⟩
    have hx_zpowers_ne_top : Subgroup.zpowers x ≠ (⊤ : Subgroup (G ⧸ A)) := by
      intro hx_top
      exact hquot_cyclic ((isCyclic_iff_exists_zpowers_eq_top (α := G ⧸ A)).2 ⟨x, hx_top⟩)
    have hquot_has_y : ∃ y : G ⧸ A, y ∉ Subgroup.zpowers x := by
      by_contra hyall_not
      push Not at hyall_not
      exact hx_zpowers_ne_top ((Subgroup.eq_top_iff' (H := Subgroup.zpowers x)).2 hyall_not)
    obtain ⟨y, hy_not_zpowers⟩ := hquot_has_y
    have hy_ne_one : y ≠ 1 := by
      intro hy_one
      exact hy_not_zpowers (by simp [hy_one])
    have hy_pow : y ^ (2 : ℕ) = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ A)) y
    have hy_order : orderOf y = 2 :=
      (orderOf_eq_prime_iff (x := y) (p := 2)).2 ⟨hy_pow, hy_ne_one⟩
    obtain ⟨b, hbq⟩ := QuotientGroup.mk'_surjective A x
    obtain ⟨c, hcq⟩ := QuotientGroup.mk'_surjective A y
    have hbinv : ∀ z : ℤ, a ^ z * b = b * a ^ (-z) :=
      hinverts_of_quot_order_two x hx_order b hbq
    have hcinv : ∀ z : ℤ, a ^ z * c = c * a ^ (-z) :=
      hinverts_of_quot_order_two y hy_order c hcq
    have hbc_cent : b * c ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hgA
      rw [← ha_zpowers] at hgA
      rcases Subgroup.mem_zpowers_iff.mp hgA with ⟨z, hz⟩
      rw [← hz]
      calc
        a ^ z * (b * c) = (a ^ z * b) * c := by group
        _ = (b * a ^ (-z)) * c := by rw [hbinv z]
        _ = b * (a ^ (-z) * c) := by group
        _ = b * (c * a ^ z) := by
          have hc := hcinv (-z)
          simpa using hc
        _ = (b * c) * a ^ z := by group
    have hbcA : b * c ∈ A := hAcent_le hbc_cent
    have hxy_one : x * y = 1 := by
      have hmk_one : π (b * c) = 1 := (QuotientGroup.eq_one_iff (N := A) (x := b * c)).2 hbcA
      calc
        x * y = π b * π c := by rw [hbq, hcq]
        _ = π (b * c) := by simp [π]
        _ = 1 := hmk_one
    have hy_eq_inv : y = x⁻¹ := by
      calc
        y = 1 * y := by simp
        _ = (x⁻¹ * x) * y := by simp
        _ = x⁻¹ * (x * y) := by group
        _ = x⁻¹ := by rw [hxy_one]; simp
    have hx_inv_mem : x⁻¹ ∈ Subgroup.zpowers x :=
      (Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x)
    exact False.elim (hy_not_zpowers (by rw [hy_eq_inv]; exact hx_inv_mem))

/--
Huppert III.7.6(b), specialized to the use in III.8.2: a noncyclic finite
`2`-group whose abelian normal subgroups are forced cyclic by the unique
involution hypothesis has a cyclic normal subgroup of index `2`.
-/

public theorem huppert_III_7_6b_cyclic_normal_index_two_of_unique_order_two
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G)
    (hnot_cyclic : ¬ IsCyclic G)
    (hunique_order_two : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y) :
    ∃ A : Subgroup G, ∃ a : G,
      A.Normal ∧ Subgroup.zpowers a = A ∧ A.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 G) := ⟨hGp⟩
  have hPhi_cyclic : IsCyclic (frattini G) :=
    huppert_III_7_6b_frattini_isCyclic_of_unique_order_two
      (G := G) hGp hunique_order_two
  let : CommGroup (frattini G) := hPhi_cyclic.commGroup
  have hPhi_comm : IsMulCommutative (frattini G) := inferInstance
  have hPhi_norm : (frattini G).Normal := by infer_instance
  obtain ⟨A, hPhi_le_A, hAnorm, hAcomm, hAmax⟩ :=
    exists_maximal_normal_abelian_subgroup_containing (G := G)
      (frattini G) hPhi_norm hPhi_comm
  have hA_cyclic : IsCyclic A :=
    huppert_III_7_6b_isCyclic_of_isMulCommutative_unique_order_two
      (G := G) hGp hunique_order_two A hAcomm
  obtain ⟨aA, haA_top⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := A)).1 hA_cyclic
  refine ⟨A, (aA : G), hAnorm, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      rcases Subgroup.mem_zpowers_iff.mp hx with ⟨z, hz⟩
      rw [← hz]
      exact A.zpow_mem aA.property z
    · intro hxA
      have hxA_top : (⟨x, hxA⟩ : A) ∈ (⊤ : Subgroup A) := by simp
      have hxA_zpow : (⟨x, hxA⟩ : A) ∈ Subgroup.zpowers aA := by
        rw [haA_top]
        exact hxA_top
      rcases Subgroup.mem_zpowers_iff.mp hxA_zpow with ⟨z, hz⟩
      refine Subgroup.mem_zpowers_iff.mpr ⟨z, ?_⟩
      exact Subtype.ext_iff.mp hz
  · exact
      huppert_III_7_6b_index_eq_two_of_maximal_normal_abelian
        (G := G) hGp hnot_cyclic hunique_order_two A hPhi_le_A hAnorm hAcomm hAmax
/--
Huppert III.8.2.  If a finite `p`-group has exactly one subgroup of order
`p`, then it is cyclic for odd `p`; for `p = 2` it is cyclic or a generalized
quaternion group.  The quaternion alternative is written directly as an
isomorphism to Mathlib's `QuaternionGroup (2 ^ (n - 2))`, whose order is
`2 ^ n` for `3 <= n`.
-/
public theorem huppert_III_8_2_pgroup_unique_order_prime_subgroup
    {G : Type u} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p)
    (hGp : IsPGroup p G)
    (hunique : ∃ U : Subgroup G, Nat.card U = p ∧
      ∀ V : Subgroup G, Nat.card V = p → V = U) :
    (p ≠ 2 → IsCyclic G) ∧
      (p = 2 →
        IsCyclic G ∨
          ∃ n : ℕ, 3 ≤ n ∧ Nonempty (G ≃* QuaternionGroup (2 ^ (n - 2)))) := by
  classical
  constructor
  · intro hp2
    by_contra hG_not_cyclic
    have : Fact p.Prime := ⟨hp⟩
    have : Fact (IsPGroup p G) := ⟨hGp⟩
    rcases lemma_4_5_a (R := G) (p := p) hp2 hG_not_cyclic with
      ⟨S, hS_normal, hS_card, hS_elem⟩
    let : S.Normal := hS_normal
    let : IsElementaryAbelian p S := hS_elem
    have hp_pos : 0 < p := hp.pos
    have hp_one_lt : 1 < p := hp.one_lt
    have hp_le_p2 : p ^ 1 ≤ p ^ 2 := by
      exact Nat.pow_le_pow_right (Nat.succ_le_of_lt hp_pos) (by decide : 1 ≤ 2)
    obtain ⟨B, hB_card⟩ :=
      Sylow.exists_subgroup_card_pow_prime_of_le_card (G := S) (n := 1) (p := p) hp
        (IsElementaryAbelian.isPGroup p S) (by simpa [hS_card, pow_one] using hp_le_p2)
    obtain ⟨C, hBC⟩ := IsElementaryAbelian.exists_isCompl (p := p) S B
    have hB_ne_top : B ≠ ⊤ := by
      intro hBtop
      have : p = p ^ 2 := by
        calc
          p = Nat.card B := (by simpa [pow_one] using hB_card.symm)
          _ = Nat.card (⊤ : Subgroup S) := by rw [hBtop]
          _ = Nat.card S := Subgroup.card_top
          _ = p ^ 2 := hS_card
      have : p ^ 1 = p ^ 2 := by simpa [pow_one] using this
      exact (by decide : (1:ℕ) ≠ 2) (Nat.pow_right_injective hp_one_lt this)
    have hC_ne_bot : C ≠ ⊥ := by
      intro hCbot
      have hBtop : B = ⊤ := by
        rcases hBC with ⟨_hdis, hcodis⟩
        simpa [hCbot] using hcodis
      exact hB_ne_top hBtop
    have hB_ne_C : B ≠ C := by
      intro hBCeq
      have hBbot : B = ⊥ := by
        rcases hBC with ⟨hdis, _hcodis⟩
        have : B ⊓ B = ⊥ := by simpa [hBCeq] using (disjoint_iff.mp hdis)
        simpa using this
      have : p = 1 := by
        calc
          p = Nat.card B := (by simpa [pow_one] using hB_card.symm)
          _ = Nat.card (⊥ : Subgroup S) := by rw [hBbot]
          _ = 1 := Subgroup.card_bot
      exact hp.ne_one this
    have hC_card : Nat.card C = p := by
      have hCp : IsPGroup p C := IsPGroup.to_subgroup (IsElementaryAbelian.isPGroup p S) C
      rcases hCp.exists_card_eq with ⟨n, hn⟩
      have hC_dvd_S : Nat.card C ∣ Nat.card S := Subgroup.card_subgroup_dvd_card C
      have hn_le_two : n ≤ 2 := by
        have hpow_dvd : p ^ n ∣ p ^ 2 := by
          simpa [hn, hS_card] using hC_dvd_S
        exact (Nat.pow_dvd_pow_iff_le_right hp_one_lt).mp hpow_dvd
      have hn_ne_zero : n ≠ 0 := by
        intro hn0
        have hCbot : C = ⊥ := by
          rw [← Subgroup.card_eq_one]
          simp [hn, hn0]
        exact hC_ne_bot hCbot
      have hn_ne_two : n ≠ 2 := by
        intro hn2
        have hCtop : C = ⊤ := by
          apply (Subgroup.card_eq_iff_eq_top (H := C)).1
          calc
            Nat.card C = p ^ n := hn
            _ = p ^ 2 := by rw [hn2]
            _ = Nat.card S := hS_card.symm
        have hBbot : B = ⊥ := by
          rcases hBC with ⟨hdis, _hcodis⟩
          have hleft : B ⊓ C = B := by simp [hCtop]
          calc
            B = B ⊓ C := hleft.symm
            _ = ⊥ := (disjoint_iff.mp hdis)
        have : p = 1 := by
          calc
            p = Nat.card B := (by simpa [pow_one] using hB_card.symm)
            _ = Nat.card (⊥ : Subgroup S) := by rw [hBbot]
            _ = 1 := Subgroup.card_bot
        exact hp.ne_one this
      have hn1 : n = 1 := by omega
      simpa [hn1, pow_one] using hn
    let BG : Subgroup G := B.map S.subtype
    let CG : Subgroup G := C.map S.subtype
    have hBG_card : Nat.card BG = p := by
      calc
        Nat.card BG = Nat.card B := by
          exact Subgroup.card_map_of_injective (K := B) (f := S.subtype) S.subtype_injective
        _ = p := by simpa [pow_one] using hB_card
    have hCG_card : Nat.card CG = p := by
      calc
        Nat.card CG = Nat.card C := by
          exact Subgroup.card_map_of_injective (K := C) (f := S.subtype) S.subtype_injective
        _ = p := hC_card
    rcases hunique with ⟨U, _hU_card, hU_unique⟩
    have hBG_eq : BG = U := hU_unique BG hBG_card
    have hCG_eq : CG = U := hU_unique CG hCG_card
    have hBCeq : B = C := by
      have hmap_eq : B.map S.subtype = C.map S.subtype := by
        simp [BG, CG, hBG_eq, hCG_eq]
      exact (Subgroup.map_injective (f := S.subtype) S.subtype_injective) hmap_eq
    exact hB_ne_C hBCeq
  · intro hp_eq_two
    subst p
    by_cases hG_cyclic : IsCyclic G
    · exact Or.inl hG_cyclic
    · right
      rcases hunique with ⟨U, hU_card, hU_unique⟩
      have hzpowers_eq_unique_of_order_two :
          ∀ x : G, orderOf x = 2 → Subgroup.zpowers x = U := by
        intro x hx
        apply hU_unique
        rw [Nat.card_zpowers, hx]
      have hinvolution_eq_of_order_two :
          ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y := by
        intro x y hx hy
        have hx_mem_y : x ∈ Subgroup.zpowers y := by
          rw [hzpowers_eq_unique_of_order_two y hy]
          rw [← hzpowers_eq_unique_of_order_two x hx]
          exact Subgroup.mem_zpowers x
        rcases Subgroup.mem_zpowers_iff.mp hx_mem_y with ⟨m, hm⟩
        have hy_sq : y ^ (2 : ℤ) = 1 := by
          exact (orderOf_dvd_iff_zpow_eq_one (x := y) (i := (2 : ℤ))).1
            (by rw [hy]; exact dvd_rfl)
        rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
        · have hx_one : x = 1 := by
            calc
              x = y ^ m := hm.symm
              _ = y ^ (2 * k : ℤ) := by rw [hk]; ring_nf
              _ = (y ^ (2 : ℤ)) ^ k := by rw [zpow_mul]
              _ = 1 := by simp [hy_sq]
          have hx_ne_one : x ≠ 1 := by
            intro hx1
            have : orderOf x = 1 := by simp [hx1]
            omega
          exact False.elim (hx_ne_one hx_one)
        · calc
            x = y ^ m := hm.symm
            _ = y ^ (2 * k + 1 : ℤ) := by rw [hk]
            _ = y ^ (2 * k : ℤ) * y := by
              rw [show (2 * k + 1 : ℤ) = 2 * k + (1 : ℤ) by ring]
              rw [zpow_add]
              norm_num
            _ = y := by
              rw [show y ^ (2 * k : ℤ) = 1 by
                rw [show (2 * k : ℤ) = (2 : ℤ) * k by norm_num]
                rw [zpow_mul, hy_sq]
                simp]
              simp
      have hU_ne_bot : U ≠ ⊥ := by
        intro hUbot
        have hcard : (2 : ℕ) = 1 := by
          calc
            (2 : ℕ) = Nat.card U := hU_card.symm
            _ = Nat.card (⊥ : Subgroup G) := by rw [hUbot]
            _ = 1 := Subgroup.card_bot
        norm_num at hcard
      have hU_center : U ≤ Subgroup.center G := by
        intro z hz
        rw [Subgroup.mem_center_iff]
        intro g
        by_cases hz_one : z = 1
        · simp [hz_one]
        · have hz_order : orderOf z = 2 := by
            have hzdvd : orderOf z ∣ Nat.card U := by
              exact U.orderOf_dvd_natCard hz
            have hz_order_ne_one : orderOf z ≠ 1 := by
              intro h
              exact hz_one (orderOf_eq_one_iff.mp h)
            rw [hU_card] at hzdvd
            rcases (Nat.dvd_prime Nat.prime_two).mp hzdvd with h | h
            · exact False.elim (hz_order_ne_one h)
            · exact h
          have hconj_order : orderOf (g * z * g⁻¹) = 2 := by
            rw [← hz_order]
            exact (SemiconjBy.orderOf_eq g (x := z) (y := g * z * g⁻¹) (by
              dsimp [SemiconjBy]
              group)).symm
          have hsame := hinvolution_eq_of_order_two (g * z * g⁻¹) z hconj_order hz_order
          have hcomm_conj : g * z * g⁻¹ * g = z * g := by
            rw [hsame]
          simpa [mul_assoc] using hcomm_conj
      rcases hGp.exists_card_eq with ⟨n, hG_card⟩
      have hn_ne_zero : n ≠ 0 := by
        intro hn0
        have hG_card_one : Nat.card G = 1 := by
          simpa [hn0] using hG_card
        have hsub : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hG_card_one).1
        exact hG_cyclic (@isCyclic_of_subsingleton G _ hsub)
      have hn_ne_one : n ≠ 1 := by
        intro hn1
        have hG_card_two : Nat.card G = 2 := by
          simpa [hn1] using hG_card
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact hG_cyclic (isCyclic_of_prime_card (α := G) hG_card_two)
      have hn_ne_two : n ≠ 2 := by
        intro hn2
        have hG_card_four : Nat.card G = 2 ^ 2 := by
          simpa [hn2] using hG_card
        let : CommGroup G := IsPGroup.commGroupOfCardEqPrimeSq (G := G) (p := 2) hG_card_four
        have hU_ne_top : U ≠ ⊤ := by
          intro hU_top
          have hG_card_two : Nat.card G = 2 := by
            calc
              Nat.card G = Nat.card (⊤ : Subgroup G) := (Subgroup.card_top (G := G)).symm
              _ = Nat.card U := by rw [hU_top]
              _ = 2 := hU_card
          have : (2 : ℕ) ^ 2 = 2 := by rw [← hG_card_four, hG_card_two]
          norm_num at this
        have hU_index_two : U.index = 2 := by
          have hmul : Nat.card U * U.index = Nat.card G := U.card_mul_index
          have hmul' : 2 * U.index = 4 := by
            simpa [hU_card] using hmul.trans hG_card_four
          omega
        have : U.Normal := Subgroup.normal_of_index_eq_two hU_index_two
        have hquot_card_two : Nat.card (G ⧸ U) = 2 := by
          have hmul : Nat.card G = Nat.card (G ⧸ U) * Nat.card U :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup U
          have hmul' : Nat.card (G ⧸ U) * 2 = 4 := by
            rw [hG_card_four] at hmul
            simpa [hU_card] using hmul.symm
          omega
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨gbar, hgbar⟩ := (isCyclic_of_prime_card (α := G ⧸ U) hquot_card_two)
        rcases QuotientGroup.mk'_surjective U gbar with ⟨g, rfl⟩
        have hg_not_mem : g ∉ U := by
          intro hgU
          have hmk_one : QuotientGroup.mk g = (1 : G ⧸ U) := (QuotientGroup.eq_one_iff (N := U) (x := g)).2 hgU
          have hgen_one : ∀ x : G ⧸ U, x = 1 := by
            intro x
            have hx : (1 : G ⧸ U) = x := by
              simpa [hmk_one] using hgbar x
            exact hx.symm
          have hquot_subsingleton : Subsingleton (G ⧸ U) :=
            ⟨fun a b => by rw [hgen_one a, hgen_one b]⟩
          have hquot_card_one : Nat.card (G ⧸ U) = 1 :=
            Nat.card_eq_one_iff_unique.mpr ⟨hquot_subsingleton, ⟨1⟩⟩
          have : (2 : ℕ) = 1 := hquot_card_two.symm.trans hquot_card_one
          norm_num at this
        have hg_sq_mem : g ^ 2 ∈ U := U.sq_mem_of_index_two hU_index_two g
        have hg_sq_order : orderOf (g ^ 2) = 2 := by
          have hgsq_ne_one : g ^ 2 ≠ 1 := by
            intro hgsq
            have hg_order_dvd_two : orderOf g ∣ 2 := by
              exact orderOf_dvd_of_pow_eq_one hgsq
            rcases (Nat.dvd_prime Nat.prime_two).mp hg_order_dvd_two with hgord_one | hgord_two
            · exact hg_not_mem (by simp [orderOf_eq_one_iff.mp hgord_one])
            · exact hg_not_mem (by
                have : Subgroup.zpowers g = U := hzpowers_eq_unique_of_order_two g hgord_two
                rw [← this]
                exact Subgroup.mem_zpowers g)
          have hgsq_order_dvd : orderOf (g ^ 2) ∣ Nat.card U := U.orderOf_dvd_natCard hg_sq_mem
          have hgsq_order_ne_one : orderOf (g ^ 2) ≠ 1 := by
            intro h
            exact hgsq_ne_one (orderOf_eq_one_iff.mp h)
          rw [hU_card] at hgsq_order_dvd
          rcases (Nat.dvd_prime Nat.prime_two).mp hgsq_order_dvd with h | h
          · exact False.elim (hgsq_order_ne_one h)
          · exact h
        have hU_le_zpowers_g : U ≤ Subgroup.zpowers g := by
          intro u hu
          by_cases hu_one : (u : G) = 1
          · simp [hu_one]
          · have hu_order : orderOf (u : G) = 2 := by
              have hudvd : orderOf (u : G) ∣ Nat.card U := U.orderOf_dvd_natCard hu
              have hune : orderOf (u : G) ≠ 1 := by
                intro h
                exact hu_one (orderOf_eq_one_iff.mp h)
              rw [hU_card] at hudvd
              rcases (Nat.dvd_prime Nat.prime_two).mp hudvd with h | h
              · exact False.elim (hune h)
              · exact h
            have hu_eq_gsq := hinvolution_eq_of_order_two u (g ^ 2) hu_order hg_sq_order
            rw [hu_eq_gsq]
            exact Subgroup.npow_mem_zpowers g 2
        have htop_le_zpowers_g : (⊤ : Subgroup G) ≤ Subgroup.zpowers g := by
          intro x hx
          have hxquot : QuotientGroup.mk x ∈ Subgroup.zpowers (QuotientGroup.mk g : G ⧸ U) := hgbar (QuotientGroup.mk x)
          rcases Subgroup.mem_zpowers_iff.mp hxquot with ⟨m, hm⟩
          let q : G →* G ⧸ U := QuotientGroup.mk' U
          have hm' : q (g ^ m) = q x := by
            simpa [q, map_zpow] using hm
          have hmk : q (x * (g ^ m)⁻¹) = (1 : G ⧸ U) := by
            rw [map_mul, map_inv, hm']
            simp
          have hxmemU : x * (g ^ m)⁻¹ ∈ U :=
            (QuotientGroup.eq_one_iff (N := U) (x := x * (g ^ m)⁻¹)).1 hmk
          have hxmem : x * (g ^ m)⁻¹ ∈ Subgroup.zpowers g := hU_le_zpowers_g hxmemU
          have hgmem : g ^ m ∈ Subgroup.zpowers g := Subgroup.zpow_mem_zpowers g m
          have hmul : (x * (g ^ m)⁻¹) * g ^ m ∈ Subgroup.zpowers g := Subgroup.mul_mem _ hxmem hgmem
          simpa [mul_assoc] using hmul
        have hztop : Subgroup.zpowers g = ⊤ := le_antisymm le_top htop_le_zpowers_g
        exact hG_cyclic ((isCyclic_iff_exists_zpowers_eq_top).2 ⟨g, hztop⟩)
      have hn_ge_three : 3 ≤ n := by omega
      rcases huppert_III_7_6b_cyclic_normal_index_two_of_unique_order_two
          (G := G) hGp hG_cyclic hinvolution_eq_of_order_two with
        ⟨A, a, hA_normal, hA_eq, hA_index⟩
      let : A.Normal := hA_normal
      rcases (Subgroup.index_eq_two_iff_exists_notMem_and (H := A)).mp hA_index with
        ⟨b, hb_not_mem, _⟩
      have hA_card : Nat.card A = 2 * 2 ^ (n - 2) := by
        have hmul : Nat.card A * A.index = Nat.card G := A.card_mul_index
        have hmul' : Nat.card A * 2 = 2 ^ n := by
          simpa [hA_index, hG_card] using hmul
        have htarget : (2 * 2 ^ (n - 2)) * 2 = 2 ^ n := by
          have hn : n = (n - 2) + 2 := by omega
          rw [hn, pow_add]
          norm_num [pow_two]
          ring
        exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (hmul'.trans htarget.symm)
      have ha_order : orderOf a = 2 * 2 ^ (n - 2) := by
        calc
          orderOf a = Nat.card (Subgroup.zpowers a) := (Nat.card_zpowers a).symm
          _ = Nat.card A := by rw [hA_eq]
          _ = 2 * 2 ^ (n - 2) := hA_card
      have : NeZero (2 ^ (n - 2)) := ⟨pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)⟩
      have hG_card_quaternion : Nat.card G = 4 * 2 ^ (n - 2) := by
        rw [hG_card]
        have hn : n = (n - 2) + 2 := by omega
        rw [hn, pow_add]
        norm_num [pow_two]
        ring
      exact ⟨n, hn_ge_three,
        huppert_I_14_9_generalizedQuaternion_mulEquiv_of_cyclic_index_two
          (G := G) (k := 2 ^ (n - 2)) A a b hA_eq hA_index ha_order hb_not_mem
          hinvolution_eq_of_order_two hG_cyclic hG_card_quaternion hGp⟩


end External
end CFSG.BenderSuzuki
