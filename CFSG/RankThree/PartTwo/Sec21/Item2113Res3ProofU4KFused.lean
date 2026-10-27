module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofU4
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofU4KDefs
public import CFSG.RankThree.PartTwo.Sec21.Item221ResProofU4
import CFSG.RankThree.PartTwo.Sec21.Item222ProofParts
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def Item2115U4UniqueE81 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (L ≃* projSU 4 2 n)) →
    Nat.card A = 3 ^ 4 → Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)) →
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) →
    ∀ B : Subgroup G, B ≤ Subgroup.normalizer (A : Set G) → CFSG.Assembly.IsElemAbelian 3 B →
      Nat.card B = 3 ^ 4 → B = A

namespace Item2113Res3Proof

open Subgroup
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (torusSU torusSU_le_unitarySU)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G] [Finite G]

theorem nonempty_u4OddCtx_of_pair {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {n : ℕ} (hn1 : 1 < n) (hno : Odd n)
    (eL : L ≃* projSU 4 2 n) (h81 : Nat.card A = 3 ^ 4)
    (hS4 : Nonempty (starOf A L ≃* Equiv.Perm (Fin 4))) :
    Nonempty (U4OddLines.U4OddCtx G L A c n (GaloisField 2 (2 * n))) := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ centralizer ({c} : Set G) := Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have := isSimpleGroup_projSU (m := 4) (n := n) le_rfl (by omega)
  have : IsSimpleGroup L := eL.isSimpleGroup
  obtain ⟨a, b, hab⟩ := Item222Proof.exists_not_commute_of_isPerfect hLp
  have hcL : c ∉ L := Item222Proof.not_mem_of_isSimpleGroup ⟨a, b, hab⟩ hc1 hLC
  obtain ⟨e⟩ := hS4
  have hAL := Item222Proof.card_inf_eq_of_star_four hAe h81 hcA hcL hLc e
  have hZL : center L = ⊥ := Item223KFactsProof.center_eq_bot_of_mulEquiv_projSU (by omega) eL hab
  exact Item221ResProof.nonempty_u4OddCtx hn1 hno eL hZL hAe h81 hcA hcL hLC hAL

theorem exists_mul_zpow_of_mem_normalizer (h45 : Sec4.Item4_5) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {n : ℕ} (hn1 : 1 < n) (eL : L ≃* projSU 4 2 n)
    {f : ℕ} {K : Type} [Field K] (C : U4OddLines.U4OddCtx G L A c f K) {x : G}
    (hx : x ∈ normalizer ((zpowers c : Subgroup G) : Set G)) (hx3 : x ^ 3 = 1) :
    ∃ y ∈ L, y ^ 3 = 1 ∧ ∃ k : ℤ, x = y * c ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG := hpair.standing.toTheoremFourHyp
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hAF.2.1 B hB hAB).le⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ centralizer ({c} : Set G) := Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have := isSimpleGroup_projSU (m := 4) (n := n) le_rfl (by omega)
  have : IsSimpleGroup L := eL.isSimpleGroup
  obtain ⟨a, b, hab⟩ := Item222Proof.exists_not_commute_of_isPerfect hLp
  have hZL : center L = ⊥ := Item223KFactsProof.center_eq_bot_of_mulEquiv_projSU (by omega) eL hab
  have hθ : aschbacherSolvableCore 3 L = ⊥ := by
    obtain ⟨hTs, -⟩ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 L) with h | h
    · exact h
    · exfalso
      rw [h] at hTs
      have hsol : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.topEquiv (G := L)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := L)).symm.injective
      exact Group.IsPerfect.not_isSolvable L hsol
  let eθ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 2 n :=
    ((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot).trans eL
  have hcomL : ∀ l ∈ L, l * c = c * l := fun l hl => mem_centralizer_singleton_iff.mp (hLC hl)
  have hQ3 : IsPGroup 3 (zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    change (x ^ i) ^ 3 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have hQC := Sec11.le_centralizer_of_le_normalizer_zpowers hco hQ3 (zpowers_le.mpr hx)
  have hxc : x * c = c * x := mem_centralizer_singleton_iff.mp (hQC (mem_zpowers x))
  have hxN : x ∈ normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 hG hc3 hc1 hQ3 hQC L hLc
      (mem_zpowers x)
  have hout := Item223PrintProof.not_inducesOuterTheta_of_mem_thetaComponentsAt hG hc3 hc1 hLc
    (by omega) eθ hxc hx3
  obtain ⟨y, hyL, hy⟩ := Item223PrintProof.exists_conj_eq_of_not_inducesOuterTheta hθ hxN hout
  set z := y⁻¹ * x with hz
  have hzL : ∀ l ∈ L, z * l = l * z := by
    intro l hl
    have h1 := hy l hl
    calc z * l = y⁻¹ * (x * l * x⁻¹) * x := by rw [hz]; group
      _ = y⁻¹ * (y * l * y⁻¹) * x := by rw [h1]
      _ = l * z := by rw [hz]; group
  have hxyz : x = y * z := by rw [hz]; group
  have hyz : Commute y z := (hzL y hyL).symm
  have h33 : y ^ 3 * z ^ 3 = 1 := by rw [← hyz.mul_pow, ← hxyz, hx3]
  have hy3 : y ^ 3 = 1 := by
    have h2 : y ^ 3 = (z ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h33
    apply Item223PrintProof.eq_one_of_forall_conj_eq hZL (L.pow_mem hyL 3)
    intro l hl
    have hz3 : z ^ 3 * l = l * z ^ 3 := (Commute.pow_left (hzL l hl : Commute z l) 3).eq
    rw [h2, inv_inv]
    calc (z ^ 3)⁻¹ * l * z ^ 3 = (z ^ 3)⁻¹ * (z ^ 3 * l) := by rw [hz3]; group
      _ = l := by group
  have hz3 : z ^ 3 = 1 := by rw [hy3, one_mul] at h33; exact h33
  have hzc : z * c = c * z := by
    have hyc : y⁻¹ * c = c * y⁻¹ := hcomL _ (L.inv_mem hyL)
    calc z * c = y⁻¹ * (x * c) := by rw [hz]; group
      _ = y⁻¹ * (c * x) := by rw [hxc]
      _ = (y⁻¹ * c) * x := by group
      _ = (c * y⁻¹) * x := by rw [hyc]
      _ = c * z := by rw [hz]; group
  have hzA : z ∈ A := by
    refine Sec4.mem_of_maximal_of_commute hAmax hz3 fun a ha => ?_
    obtain ⟨d, i, rfl⟩ := C.decomp ha
    have h1 : C.theta d * z = z * C.theta d := (hzL _ (C.theta_mem_L d)).symm
    have h2 : c ^ i * z = z * c ^ i := (Commute.zpow_left (hzc.symm : Commute c z) i).eq
    calc C.theta d * c ^ i * z = C.theta d * (c ^ i * z) := by group
      _ = C.theta d * (z * c ^ i) := by rw [h2]
      _ = (C.theta d * z) * c ^ i := by group
      _ = (z * C.theta d) * c ^ i := by rw [h1]
      _ = z * (C.theta d * c ^ i) := by group
  obtain ⟨d, k, hdk⟩ := C.decomp hzA
  have hθd : C.theta d = 1 := by
    apply Item223PrintProof.eq_one_of_forall_conj_eq hZL (C.theta_mem_L d)
    intro l hl
    have he : C.theta d = z * (c ^ k)⁻¹ := by rw [hdk]; group
    have h1 : z * l = l * z := hzL l hl
    have h2 : c ^ k * l = l * c ^ k :=
      (Commute.zpow_left ((hcomL l hl).symm : Commute c l) k).eq
    rw [he]
    calc z * (c ^ k)⁻¹ * l * (z * (c ^ k)⁻¹)⁻¹ = z * ((c ^ k)⁻¹ * (l * c ^ k)) * z⁻¹ := by group
      _ = z * ((c ^ k)⁻¹ * (c ^ k * l)) * z⁻¹ := by rw [h2]
      _ = z * l * z⁻¹ := by group
      _ = l * z * z⁻¹ := by rw [h1]
      _ = l := by group
  refine ⟨y, hyL, hy3, k, ?_⟩
  rw [hxyz, hdk, hθd, one_mul]

theorem item2115U4FusedA_of (h45 : Sec4.Item4_5) (hK3 : Item2115U4KConjTorus) :
    Item2115U4FusedA := by
  intro G _ _ A E U c L hpair ⟨n, hn1, hno, ⟨eL⟩⟩ h81 hS4 _ x hx hx3
  obtain ⟨C⟩ := nonempty_u4OddCtx_of_pair hpair hn1 hno eL h81 hS4
  obtain ⟨y, hyL, hy3, k, rfl⟩ := exists_mul_zpow_of_mem_normalizer h45 hpair hn1 eL C hx hx3
  set g := C.ψ.symm ⟨y, hyL⟩ with hg
  have hgy : C.phi g = y := by rw [U4OddLines.U4OddCtx.coe_phi, hg, MulEquiv.apply_symm_apply]
  have hg3 : (g : GL (Fin 4) (GaloisField 2 (2 * n))) ^ 3 = 1 := by
    have h1 : g ^ 3 = 1 := C.phi_injective (by rw [map_pow, hgy, hy3, map_one])
    have h2 := congrArg (fun w : unitarySU 2 n (GaloisField 2 (2 * n)) 4 =>
      (w : GL (Fin 4) (GaloisField 2 (2 * n)))) h1
    simpa using h2
  obtain ⟨u, huU, hut⟩ := hK3 n (GaloisField 2 (2 * n)) C.hU C.hf2 C.hpq g g.2 hg3
  set u' : unitarySU 2 n (GaloisField 2 (2 * n)) 4 := ⟨u, huU⟩ with hu'
  have h1 : C.phi u' * y * (C.phi u')⁻¹ ∈ A := by
    rw [← hgy, ← map_inv, ← map_mul, ← map_mul]
    exact (C.hψ _).mpr hut
  have h2 : C.phi u' * c ^ k * (C.phi u')⁻¹ = c ^ k := C.conj_zpow_c (C.phi_mem_L _) k
  refine ⟨C.phi u', C.phi_mem_L _, ?_⟩
  have e : C.phi u' * (y * c ^ k) * (C.phi u')⁻¹ =
      (C.phi u' * y * (C.phi u')⁻¹) * (C.phi u' * c ^ k * (C.phi u')⁻¹) := by group
  rw [e, h2]
  exact A.mul_mem h1 (A.zpow_mem C.hcA k)

theorem conj_mem_torusSU_of_mem_normalizer {A L : Subgroup G} {c : G} {f : ℕ} {K : Type}
    [Field K] (C : U4OddLines.U4OddCtx G L A c f K) {g : unitarySU 2 f K 4}
    (hg : C.phi g ∈ normalizer (A : Set G)) {t : GL (Fin 4) K} (ht : t ∈ torusSU 3 4 K) :
    (g : GL (Fin 4) K) * t * (g : GL (Fin 4) K)⁻¹ ∈ torusSU 3 4 K := by
  have htU := torusSU_le_unitarySU C.hU C.hpq ht
  have h1 : C.phi g * C.phi ⟨t, htU⟩ * (C.phi g)⁻¹ ∈ A :=
    (mem_normalizer_iff.mp hg _).1 ((C.hψ ⟨t, htU⟩).mpr ht)
  rw [← map_inv, ← map_mul, ← map_mul] at h1
  exact (C.hψ _).mp h1

theorem item2115U4UniqueE81_of (h45 : Sec4.Item4_5) (hK2 : Item2115U4KTorusE27) :
    Item2115U4UniqueE81 := by
  intro G _ _ A E U c L hpair ⟨n, hn1, hno, ⟨eL⟩⟩ h81 hS4 hW B hBW hBe hB81
  obtain ⟨C⟩ := nonempty_u4OddCtx_of_pair hpair hn1 hno eL h81 hS4
  set K := GaloisField 2 (2 * n)
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hco : orderOf c = 3 := orderOf_eq_prime (hAe.2 c C.hcA) (fun h => C.hcL (h ▸ L.one_mem))
  have hdec : ∀ b ∈ B, ∃ y ∈ L, ∃ k : ℤ, b = y * c ^ k := fun b hb => by
    obtain ⟨y, hyL, -, k, hk⟩ :=
      exists_mul_zpow_of_mem_normalizer h45 hpair hn1 eL C (hW (hBW hb)) (hBe.2 b hb)
    exact ⟨y, hyL, k, hk⟩
  have hBc : ∀ b ∈ B, ∀ i : ℤ, c ^ i * b = b * c ^ i := by
    intro b hb i
    obtain ⟨y, hyL, k, rfl⟩ := hdec b hb
    have h1 : c ^ i * y = y * c ^ i := by
      have h := C.conj_zpow_c hyL i
      calc c ^ i * y = (y * c ^ i * y⁻¹) * y := by rw [h]
        _ = y * c ^ i := by group
    calc c ^ i * (y * c ^ k) = (c ^ i * y) * c ^ k := by group
      _ = (y * c ^ i) * c ^ k := by rw [h1]
      _ = y * c ^ k * c ^ i := by rw [mul_assoc, mul_assoc, ← zpow_add, ← zpow_add, add_comm]
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let B' : Subgroup G :=
    { carrier := {g | ∃ b ∈ B, ∃ i : ℤ, g = b * c ^ i}
      mul_mem' := by
        rintro _ _ ⟨x, hx, i, rfl⟩ ⟨y, hy, j, rfl⟩
        refine ⟨x * y, B.mul_mem hx hy, i + j, ?_⟩
        rw [zpow_add]
        calc x * c ^ i * (y * c ^ j) = x * (c ^ i * y) * c ^ j := by group
          _ = x * (y * c ^ i) * c ^ j := by rw [hBc y hy i]
          _ = x * y * (c ^ i * c ^ j) := by group
      one_mem' := ⟨1, B.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, i, rfl⟩
        refine ⟨x⁻¹, B.inv_mem hx, -i, ?_⟩
        rw [mul_inv_rev, ← zpow_neg, hBc x⁻¹ (B.inv_mem hx) (-i)] }
  have hB'comm : ∀ g ∈ B', ∀ h ∈ B', g * h = h * g := by
    rintro _ ⟨x, hx, i, rfl⟩ _ ⟨y, hy, j, rfl⟩
    calc x * c ^ i * (y * c ^ j) = x * (c ^ i * y) * c ^ j := by group
      _ = x * (y * c ^ i) * c ^ j := by rw [hBc y hy i]
      _ = (x * y) * (c ^ i * c ^ j) := by group
      _ = (y * x) * (c ^ j * c ^ i) := by
          rw [hBcomm x hx y hy, ← zpow_add, ← zpow_add, add_comm]
      _ = y * (x * c ^ j) * c ^ i := by group
      _ = y * (c ^ j * x) * c ^ i := by rw [hBc x hx j]
      _ = y * c ^ j * (x * c ^ i) := by group
  have hB'3 : ∀ g ∈ B', g ^ 3 = 1 := by
    rintro _ ⟨x, hx, i, rfl⟩
    have hcx : Commute x (c ^ i) := (hBc x hx i).symm
    rw [hcx.mul_pow, hBe.2 x hx, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hAe.2 c C.hcA, one_zpow]
  have hB'N : B' ≤ normalizer (A : Set G) := by
    rintro _ ⟨x, hx, i, rfl⟩
    exact mul_mem (hBW hx) (zpow_mem (le_normalizer C.hcA) i)
  set F : Subgroup G := B' ⊓ L
  have hdec' : ∀ b : B, ∃ y : F, ∃ k : ℤ, (b : G) = (y : G) * c ^ k := by
    intro b
    obtain ⟨y, hyL, k, hk⟩ := hdec b b.2
    refine ⟨⟨y, ⟨b, b.2, -k, ?_⟩, hyL⟩, k, hk⟩
    rw [hk]
    group
  choose yb kb hkb using hdec'
  have hinj : Function.Injective fun b : B =>
      (yb b, (⟨c ^ kb b, zpow_mem_zpowers c (kb b)⟩ : zpowers c)) := by
    intro b b' h
    simp only [Prod.mk.injEq] at h
    have h2 : c ^ kb b = c ^ kb b' := congrArg Subtype.val h.2
    apply Subtype.ext
    rw [hkb b, hkb b', h.1, h2]
  have hF27 : 3 ^ 3 ≤ Nat.card F := by
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, Nat.card_zpowers, hco, hB81] at h1
    omega
  set F₀ : Subgroup (GL (Fin 4) K) := (F.comap C.phi).map (unitarySU 2 n K 4).subtype with hF₀
  have hFr : F ≤ C.phi.range := fun x hx =>
    ⟨C.ψ.symm ⟨x, hx.2⟩, by rw [U4OddLines.U4OddCtx.coe_phi, MulEquiv.apply_symm_apply]⟩
  have hF₀card : Nat.card F₀ = Nat.card F := by
    rw [hF₀, card_map_of_injective (unitarySU 2 n K 4).subtype_injective,
      ← card_map_of_injective C.phi_injective, map_comap_eq_self hFr]
  have hF₀mem : ∀ w ∈ F₀, ∃ g : unitarySU 2 n K 4, C.phi g ∈ F ∧ (g : GL (Fin 4) K) = w :=
    fun w hw => by
      obtain ⟨g, hg, rfl⟩ := mem_map.mp hw
      exact ⟨g, hg, rfl⟩
  have hF₀e : IsElemAbelian 3 F₀ := by
    refine ⟨⟨⟨fun w w' => Subtype.ext ?_⟩⟩, fun w hw => ?_⟩
    · obtain ⟨g, hg, hgw⟩ := hF₀mem w w.2
      obtain ⟨g', hg', hgw'⟩ := hF₀mem w' w'.2
      have h1 : g * g' = g' * g := C.phi_injective (by
        rw [map_mul, map_mul]
        exact hB'comm _ hg.1 _ hg'.1)
      change (w : GL (Fin 4) K) * w' = w' * w
      rw [← hgw, ← hgw']
      exact congrArg Subtype.val h1
    · obtain ⟨g, hg, rfl⟩ := hF₀mem w hw
      have h1 : g ^ 3 = 1 := C.phi_injective (by rw [map_pow, map_one]; exact hB'3 _ hg.1)
      exact congrArg Subtype.val h1
  have hF₀N : F₀ ≤ normalizer (torusSU 3 4 K : Set (GL (Fin 4) K)) := by
    intro w hw
    obtain ⟨g, hg, rfl⟩ := hF₀mem w hw
    have hgN : C.phi g ∈ normalizer (A : Set G) := hB'N hg.1
    have hgN' : C.phi g⁻¹ ∈ normalizer (A : Set G) := by rw [map_inv]; exact inv_mem hgN
    rw [mem_normalizer_iff]
    intro t
    refine ⟨fun ht => conj_mem_torusSU_of_mem_normalizer C hgN ht, fun ht => ?_⟩
    have h1 := conj_mem_torusSU_of_mem_normalizer C hgN' ht
    have e : ((g⁻¹ : unitarySU 2 n K 4) : GL (Fin 4) K) *
        ((g : GL (Fin 4) K) * t * (g : GL (Fin 4) K)⁻¹) *
        ((g⁻¹ : unitarySU 2 n K 4) : GL (Fin 4) K)⁻¹ = t := by
      rw [InvMemClass.coe_inv]
      group
    rwa [e] at h1
  have hF₀T := hK2 n K C.hU C.hf2 C.hpq F₀ (map_subtype_le _) hF₀e (hF₀card ▸ hF27) hF₀N
  have hFA : F ≤ A := by
    intro x hx
    obtain ⟨g, hg⟩ := hFr hx
    have hgF : (g : GL (Fin 4) K) ∈ F₀ := mem_map.mpr ⟨g, by rw [mem_comap, hg]; exact hx, rfl⟩
    rw [← hg]
    exact (C.hψ g).mpr (hF₀T hgF)
  have hBA : B ≤ A := by
    intro b hb
    have hb' : b = (yb ⟨b, hb⟩ : G) * c ^ kb ⟨b, hb⟩ := hkb ⟨b, hb⟩
    rw [hb']
    exact A.mul_mem (hFA (yb ⟨b, hb⟩).2) (A.zpow_mem C.hcA _)
  exact Subgroup.eq_of_le_of_card_ge hBA (by rw [hB81, h81])

omit [Finite G] in
theorem isElemAbelian_map_conj {A : Subgroup G} (hAe : IsElemAbelian 3 A) (g : G) :
    IsElemAbelian 3 (A.map (MulAut.conj g).toMonoidHom) := CFSG.Open.IsElemAbelian.map hAe _

theorem item2115U4Thompson_of_unique (hU : Item2115U4UniqueE81) : Item2115U4Thompson := by
  intro G _ _ A E U c L hpair hU4 h81 hS4 hW
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  set W := normalizer (A : Set G) with hWdef
  have hAW : A ≤ W := le_normalizer
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  obtain ⟨Q, hQ⟩ := (hA3.comap_subtype (K := W)).exists_le_sylow
  set P : Subgroup G := (Q : Subgroup W).map W.subtype with hP
  have hAP : A ≤ P := fun a ha =>
    mem_map.mpr ⟨⟨a, hAW ha⟩, hQ (mem_subgroupOf.mpr ha), rfl⟩
  have hPW : P ≤ W := map_subtype_le _
  have huniq : ∀ B : Subgroup G, B ≤ P → IsElemAbelian 3 B → Nat.card B = 3 ^ 4 → B = A :=
    fun B hB hBe hB81 => hU G A E U c L hpair hU4 h81 hS4 hW B (hB.trans hPW) hBe hB81
  have hNP : normalizer (P : Set G) ≤ W := by
    intro g hg
    have hle : A.map (MulAut.conj g).toMonoidHom ≤ P := by
      rintro _ ⟨b, hb, rfl⟩
      exact (mem_normalizer_iff.mp hg b).mp (hAP hb)
    have heq := huniq _ hle (isElemAbelian_map_conj hAe g)
      (by rw [card_map_of_injective (MulAut.conj g).injective, h81])
    apply mem_normalizer_fintype
    intro a ha
    rw [← heq]
    exact mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨S, hS⟩ := isSylow_of_normalizer_le ⟨Q, rfl⟩ hNP
  have hPH : P ≤ normalizer ((zpowers c : Subgroup G) : Set G) := hPW.trans hW
  refine ⟨P, hAP, ⟨S.subtype (hS ▸ hPH), ?_⟩, huniq⟩
  rw [Sylow.coe_subtype, subgroupOf_map_subtype, hS, inf_of_le_left hPH]

theorem item2115U4Fusion_of_unique (hF1 : Item2115U4FusedA) (hU : Item2115U4UniqueE81) :
    Item2115U4Fusion :=
  item2115U4Fusion_of hF1 (item2115U4Thompson_of_unique hU)

theorem item2115U4Fusion_of_kfacts (h45 : Sec4.Item4_5) (hK2 : Item2115U4KTorusE27)
    (hK3 : Item2115U4KConjTorus) : Item2115U4Fusion :=
  item2115U4Fusion_of_unique (item2115U4FusedA_of h45 hK3) (item2115U4UniqueE81_of h45 hK2)

end Item2113Res3Proof

end CFSG.RankThree.PartTwo.Sec21
