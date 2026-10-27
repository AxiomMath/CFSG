module

public import CFSG.RankThree.PartOne.TCX.Ree.WeylNeg
public import CFSG.RankThree.PartOne.TCX.Ree.Setup
public import CFSG.RankThree.PartOne.TCX.ParabolicConj

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.TCX
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Stab

variable {L : Type} [Field L]

theorem mem_rootCharStabilizer_of_commute {g : ModGL ReeTag.F4.tag L}
    {w : WeylGroup ReeTag.F4.tag} (hg : PermAct g w) (a : Fin ReeTag.F4.tag.rank → Lˣ)
    (h : g * rootDiagUnit ReeTag.F4.tag a = rootDiagUnit ReeTag.F4.tag a * g) :
    w ∈ rootCharStabilizer a := by
  intro v
  refine rootChar_smul_eq_of_forall_isRoot (fun γ hγ => ?_) v
  set d := rootDiagUnit ReeTag.F4.tag a with hd
  have e1 := rootDiagUnit_conj_pinnedX a hγ (1 : L)
  have e2 := rootDiagUnit_conj_pinnedX a (IsRoot.smul hγ w) (1 : L)
  have e3 : g * (d * pinnedX ReeTag.F4.tag L γ 1 * d⁻¹) * g⁻¹ =
      d * (g * pinnedX ReeTag.F4.tag L γ 1 * g⁻¹) * d⁻¹ := by
    calc g * (d * pinnedX ReeTag.F4.tag L γ 1 * d⁻¹) * g⁻¹
        = (g * d) * pinnedX ReeTag.F4.tag L γ 1 * (g * d)⁻¹ := by group
      _ = (d * g) * pinnedX ReeTag.F4.tag L γ 1 * (d * g)⁻¹ := by rw [h]
      _ = d * (g * pinnedX ReeTag.F4.tag L γ 1 * g⁻¹) * d⁻¹ := by group
  rw [e1, hg γ hγ, hg γ hγ 1, e2] at e3
  have e4 := pinnedX_injective ReeTag.F4.tag L (w • γ) e3
  have e5 : (rootChar a γ : L) = (rootChar a (w • γ) : L) := by simpa using e4
  exact (Units.ext e5).symm

end Stab

section Diag

theorem diag_mem_adjointGroup_F4 {K : Type} [Field K]
    (a : Fin ReeTag.F4.tag.rank → Kˣ) :
    rootDiagUnit ReeTag.F4.tag a ∈ adjointGroup ReeTag.F4.tag K := by
  obtain ⟨B, hB, -⟩ := (G2_F4_root_character_diagonals_inner Tag.F4 (Or.inr rfl) K).1
  obtain ⟨-, -, h, -⟩ := (G2_F4_root_character_diagonals_inner Tag.F4 (Or.inr rfl) K).2 B hB a
  exact h

end Diag

section Normalizer

theorem normalizer_map_of_injective {G H : Type*} [Group G] [Group H] (φ : G →* H)
    {x : G} {S : Subgroup G} (hxS : x ∈ Subgroup.normalizer (S : Set G)) :
    φ x ∈ Subgroup.normalizer ((S.map φ : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hxS ⊢
  intro h
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨x * s * x⁻¹, (hxS s).1 hs, by simp [map_mul]⟩
  · rintro ⟨s, hs, hsh⟩
    refine ⟨x⁻¹ * s * x, (hxS (x⁻¹ * s * x)).2 (by simpa [mul_assoc] using hs), ?_⟩
    rw [map_mul, map_mul, map_inv, hsh]
    group

end Normalizer

section Regular

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] [IsAlgClosed L] [IsAlgClosure K L]
  (D : ReeFrameData K L a)

omit [CharP L 2] [IsAlgClosed L] [IsAlgClosure K L] in
theorem fext_fext_eq_entrywise {u : ModGL ReeTag.F4.tag L} (hu : u ∈ adjointGroup ReeTag.F4.tag L) :
    Fext D.F (Fext D.F u) = Units.map (entrywiseHom D.Frq) u := by
  rw [Fext_of_mem D.F hu, Fext_of_mem D.F (D.F ⟨_, hu⟩).2]
  exact D.sq ⟨_, hu⟩

omit [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L] in
theorem regular_centralizer_torus {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hord : orderOf (rootDiagUnit ReeTag.F4.tag b) = p)
    (hker : rootCharKernel b = ∅) {u : ModGL ReeTag.F4.tag L}
    (hu : u ∈ adjointGroup ReeTag.F4.tag L)
    (hcomm : u * rootDiagUnit ReeTag.F4.tag b = rootDiagUnit ReeTag.F4.tag b * u) :
    u ∈ torusGroup ReeTag.F4.tag L := by
  have hbp := pow_eq_one_of_orderOf_rootDiagUnit hord
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hord
  have hstab := rootCharStabilizer_subset_closure hp (not_dvd_card_weylGroup_F4 hp hp3) hbp hb1
  have hS : ∀ α ∈ (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)), IsRoot ReeTag.F4.tag α :=
    fun α h => h.elim
  have hSn : ∀ α ∈ (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)),
      -α ∈ (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := fun α h => h.elim
  have hker' : rootCharKernel b ⊆ (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := by rw [hker]
  have hmem := mem_torus_mul_rootSpan_of_commute_of_stab hstab hS hSn hker' hu hcomm
  obtain ⟨t, ht, q, hq, hu'⟩ := Set.mem_mul.1 hmem
  have hspan : rootSpan ReeTag.F4.tag L (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) = ⊥ := by
    simp [rootSpan]
  have hq1 : q = 1 := by
    have h : q ∈ (⊥ : Subgroup (ModGL ReeTag.F4.tag L)) := by
      rw [← hspan]
      exact hq
    exact Subgroup.mem_bot.1 h
  rw [← hu', hq1, mul_one]
  exact ht

omit [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L] in
theorem regular_comm {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {g₀ : ModGL ReeTag.F4.tag L}
    (hg₀C : g₀ ∈ adjointGroup ReeTag.F4.tag L) {x c : ReeTag.F4.reeGamma K a}
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hord : orderOf (rootDiagUnit ReeTag.F4.tag b) = p)
    (hb : rootDiagUnit ReeTag.F4.tag b = g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀)
    (hker : rootCharKernel b = ∅) :
    ∀ y ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      ∀ z ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)), y * z = z * y := by
  have hψ : ∀ y ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      g₀⁻¹ * thetaGamma L a (c * y * c⁻¹) * g₀ ∈ torusGroup ReeTag.F4.tag L := by
    intro y hy
    refine regular_centralizer_torus hp hp3 hord hker
      (mul_mem (mul_mem (inv_mem hg₀C) (thetaGamma_mem_adjointGroup L _)) hg₀C) ?_
    rw [hb]
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    have h1 : (c * y * c⁻¹) * (c * x * c⁻¹) = (c * x * c⁻¹) * (c * y * c⁻¹) := by
      calc (c * y * c⁻¹) * (c * x * c⁻¹) = c * (y * x) * c⁻¹ := by group
        _ = c * (x * y) * c⁻¹ := by rw [hyx]
        _ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    have h2 : thetaGamma L a (c * y * c⁻¹) * thetaGamma L a (c * x * c⁻¹) =
        thetaGamma L a (c * x * c⁻¹) * thetaGamma L a (c * y * c⁻¹) := by
      rw [← map_mul, ← map_mul, h1]
    calc g₀⁻¹ * thetaGamma L a (c * y * c⁻¹) * g₀ * (g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀)
        = g₀⁻¹ * (thetaGamma L a (c * y * c⁻¹) * thetaGamma L a (c * x * c⁻¹)) * g₀ := by group
      _ = g₀⁻¹ * (thetaGamma L a (c * x * c⁻¹) * thetaGamma L a (c * y * c⁻¹)) * g₀ := by
        rw [h2]
      _ = g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ *
          (g₀⁻¹ * thetaGamma L a (c * y * c⁻¹) * g₀) := by group
  intro y hy z hz
  have h1 := KE.torusGroup_comm (hψ y hy) (hψ z hz)
  have h3 : g₀⁻¹ * (thetaGamma L a (c * y * c⁻¹) * thetaGamma L a (c * z * c⁻¹)) * g₀ =
      g₀⁻¹ * (thetaGamma L a (c * z * c⁻¹) * thetaGamma L a (c * y * c⁻¹)) * g₀ := by
    calc g₀⁻¹ * (thetaGamma L a (c * y * c⁻¹) * thetaGamma L a (c * z * c⁻¹)) * g₀
        = g₀⁻¹ * thetaGamma L a (c * y * c⁻¹) * g₀ *
          (g₀⁻¹ * thetaGamma L a (c * z * c⁻¹) * g₀) := by group
      _ = g₀⁻¹ * thetaGamma L a (c * z * c⁻¹) * g₀ *
          (g₀⁻¹ * thetaGamma L a (c * y * c⁻¹) * g₀) := h1
      _ = g₀⁻¹ * (thetaGamma L a (c * z * c⁻¹) * thetaGamma L a (c * y * c⁻¹)) * g₀ := by group
  have h2 : thetaGamma L a (c * y * c⁻¹) * thetaGamma L a (c * z * c⁻¹) =
      thetaGamma L a (c * z * c⁻¹) * thetaGamma L a (c * y * c⁻¹) :=
    mul_left_cancel (mul_right_cancel h3)
  have h4 : thetaGamma L a (c * (y * z) * c⁻¹) = thetaGamma L a (c * (z * y) * c⁻¹) := by
    have e1 : c * (y * z) * c⁻¹ = (c * y * c⁻¹) * (c * z * c⁻¹) := by group
    have e2 : c * (z * y) * c⁻¹ = (c * z * c⁻¹) * (c * y * c⁻¹) := by group
    calc thetaGamma L a (c * (y * z) * c⁻¹)
        = thetaGamma L a (c * y * c⁻¹) * thetaGamma L a (c * z * c⁻¹) := by
          rw [e1]; exact map_mul _ _ _
      _ = thetaGamma L a (c * z * c⁻¹) * thetaGamma L a (c * y * c⁻¹) := h2
      _ = thetaGamma L a (c * (z * y) * c⁻¹) := by
          rw [e2]; exact (map_mul _ _ _).symm
  exact mul_left_cancel (mul_right_cancel (thetaGamma_injective L h4))

omit [IsAlgClosure K L] in
theorem regular_no_normalized (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {g₀ N : ModGL ReeTag.F4.tag L}
    (hg₀C : g₀ ∈ adjointGroup ReeTag.F4.tag L) (hNC : N ∈ adjointGroup ReeTag.F4.tag L)
    (hFg : Fext D.F g₀ = g₀ * N) {w : WeylGroup ReeTag.F4.tag} (hNperm : PermAct N w)
    (hneg : NegAct (w * ReeTag.F4.weylPerm w)) {x c : ReeTag.F4.reeGamma K a}
    (hx : orderOf x = p) {b : Fin ReeTag.F4.tag.rank → Lˣ}
    (hord : orderOf (rootDiagUnit ReeTag.F4.tag b) = p)
    (hb : rootDiagUnit ReeTag.F4.tag b = g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀)
    (hker : rootCharKernel b = ∅) {S : Subgroup (ReeTag.F4.reeGamma K a)} (hS : S ≠ ⊥)
    (hS2 : IsPGroup 2 S) (hxS : x ∈ Subgroup.normalizer (S : Set (ReeTag.F4.reeGamma K a))) :
    False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hp3 : 3 < p := by omega
  set φ := RF4.reeGammaToAdjoint (K := K) a with hφ
  have hφinj : Function.Injective φ := RF4.reeGammaToAdjoint_injective a
  have hxo : orderOf (φ x) = p := by rw [orderOf_injective φ hφinj, hx]
  have hSφ : S.map φ ≠ ⊥ := fun h => hS ((Subgroup.map_eq_bot_iff_of_injective S hφinj).1 h)
  obtain ⟨z, hz, hzo⟩ := exists_centralizer_elt_orderOf_of_normalizes (τ := ReeTag.F4.tag)
    (r := 2) (fun a => diag_mem_adjointGroup_F4 a) hp (by omega) hxo hSφ (hS2.map φ)
    (normalizer_map_of_injective φ hxS)
  have hzx : z * φ x = φ x * z := Subgroup.mem_centralizer_singleton_iff.1 hz
  set zA : adjointGroup ReeTag.F4.tag K := φ c * z * (φ c)⁻¹ with hzA
  have hzAo : orderOf zA = Nat.card K - 1 := by
    have h := (MulAut.conj (φ c)).orderOf_eq z
    rw [MulAut.conj_apply] at h
    rw [hzA, h, hzo]
  have hcommA : zA * φ (c * x * c⁻¹) = φ (c * x * c⁻¹) * zA := by
    rw [hzA, map_mul, map_mul, map_inv]
    calc φ c * z * (φ c)⁻¹ * (φ c * φ x * (φ c)⁻¹) = φ c * (z * φ x) * (φ c)⁻¹ := by group
      _ = φ c * (φ x * z) * (φ c)⁻¹ := by rw [hzx]
      _ = φ c * φ x * (φ c)⁻¹ * (φ c * z * (φ c)⁻¹) := by group
  set ι := adjointBaseChangeHom ReeTag.F4.tag (algebraMap K L) with hι
  have hιinj : Function.Injective ι := adjointBaseChangeHom_injective _ _
  set g₀A : adjointGroup ReeTag.F4.tag L := ⟨g₀, hg₀C⟩ with hg₀A
  set ζA : adjointGroup ReeTag.F4.tag L := g₀A⁻¹ * ι zA * g₀A with hζA
  have hζ : (ζA : ModGL ReeTag.F4.tag L) = g₀⁻¹ * (ι zA : ModGL ReeTag.F4.tag L) * g₀ := rfl
  have hζo : orderOf ζA = Nat.card K - 1 := by
    have h := (MulAut.conj g₀A⁻¹).orderOf_eq (ι zA)
    rw [MulAut.conj_apply, inv_inv] at h
    rw [hζA, h, orderOf_injective ι hιinj zA, hzAo]
  have hθx : thetaGamma L a (c * x * c⁻¹) = (ι (φ (c * x * c⁻¹)) : ModGL ReeTag.F4.tag L) :=
    thetaGamma_eq_adjoint L _
  have hcommL : ζA * (g₀A⁻¹ * ι (φ (c * x * c⁻¹)) * g₀A) =
      (g₀A⁻¹ * ι (φ (c * x * c⁻¹)) * g₀A) * ζA := by
    have h1 : ι zA * ι (φ (c * x * c⁻¹)) = ι (φ (c * x * c⁻¹)) * ι zA := by
      rw [← map_mul, ← map_mul, hcommA]
    calc ζA * (g₀A⁻¹ * ι (φ (c * x * c⁻¹)) * g₀A)
        = g₀A⁻¹ * (ι zA * ι (φ (c * x * c⁻¹))) * g₀A := by rw [hζA]; group
      _ = g₀A⁻¹ * (ι (φ (c * x * c⁻¹)) * ι zA) * g₀A := by rw [h1]
      _ = (g₀A⁻¹ * ι (φ (c * x * c⁻¹)) * g₀A) * ζA := by rw [hζA]; group
  have hζcomm : (ζA : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag b =
      rootDiagUnit ReeTag.F4.tag b * (ζA : ModGL ReeTag.F4.tag L) := by
    rw [hb, hθx]
    exact congrArg Subtype.val hcommL
  have hζT : (ζA : ModGL ReeTag.F4.tag L) ∈ torusGroup ReeTag.F4.tag L :=
    regular_centralizer_torus hp hp3 hord hker ζA.2 hζcomm
  obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hζT
  have hordζ : orderOf (rootDiagUnit ReeTag.F4.tag a') = Nat.card K - 1 := by
    rw [← ha', Subgroup.orderOf_coe, hζo]
  have ha'ord : orderOf a' = Nat.card K - 1 := by
    rw [← hordζ]
    exact (orderOf_injective (rootDiagUnitHom ReeTag.F4.tag L) rootDiagUnit_injective a').symm
  have hpowa : a' ^ (Nat.card K - 1) = 1 := by
    rw [← ha'ord]
    exact pow_orderOf_eq_one a'
  have hpowj : ∀ j, a' j ^ (Nat.card K - 1) = 1 := fun j => congrFun hpowa j
  have hQpos : 1 ≤ Nat.card K := Nat.card_pos
  have hpowcard : ∀ t : K, t ^ Nat.card K = t := fun t => by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card t
  have hfixι : ∀ t : K, D.Frq (algebraMap K L t) = algebraMap K L ((RingHom.id K) t) := fun t => by
    rw [D.Frq_pow, ← map_pow, hpowcard t]
    rfl
  have hFrz : Units.map (entrywiseHom D.Frq) (ι zA : ModGL ReeTag.F4.tag L) =
      (ι zA : ModGL ReeTag.F4.tag L) := by
    show Units.map (entrywiseHom D.Frq)
        (baseChangeGL (algebraMap K L) (zA : ModGL ReeTag.F4.tag K)) =
      baseChangeGL (algebraMap K L) (zA : ModGL ReeTag.F4.tag K)
    rw [entrywise_baseChangeGL_comm (algebraMap K L) D.Frq (RingHom.id K) hfixι]
    congr 1
    exact Units.ext (entrywise_id _)
  have hFrg : Units.map (entrywiseHom D.Frq) g₀ = g₀ * N * Fext D.F N := by
    rw [← fext_fext_eq_entrywise D hg₀C, hFg, Fext_mul D.F hg₀C hNC, hFg]
  set N₂ : ModGL ReeTag.F4.tag L := N * Fext D.F N with hN₂
  have hFrζ : Units.map (entrywiseHom D.Frq) (ζA : ModGL ReeTag.F4.tag L) =
      N₂⁻¹ * (ζA : ModGL ReeTag.F4.tag L) * N₂ := by
    rw [hζ, map_mul, map_mul, map_inv, hFrz, hFrg, hN₂]
    group
  have hFrfix : Units.map (entrywiseHom D.Frq) (rootDiagUnit ReeTag.F4.tag a') =
      rootDiagUnit ReeTag.F4.tag a' := by
    have h1 : Units.map (entrywiseHom D.Frq) (rootDiagUnit ReeTag.F4.tag a') =
        rootDiagUnit ReeTag.F4.tag (fun i => Units.map D.Frq.toMonoidHom (a' i)) :=
      Units.ext (entrywise_rootDiag D.Frq a')
    rw [h1]
    congr 1
    funext j
    apply Units.ext
    change D.Frq (a' j : L) = (a' j : L)
    rw [D.Frq_pow]
    have h2 : (a' j) ^ Nat.card K = a' j := by
      rw [show Nat.card K = (Nat.card K - 1) + 1 by omega, pow_succ, hpowj j, one_mul]
    simpa using congrArg Units.val h2
  have hcomm₂ : N₂ * rootDiagUnit ReeTag.F4.tag a' = rootDiagUnit ReeTag.F4.tag a' * N₂ := by
    have h1 : N₂⁻¹ * rootDiagUnit ReeTag.F4.tag a' * N₂ = rootDiagUnit ReeTag.F4.tag a' := by
      have h := hFrζ
      rw [ha', hFrfix] at h
      exact h.symm
    calc N₂ * rootDiagUnit ReeTag.F4.tag a'
        = N₂ * (N₂⁻¹ * rootDiagUnit ReeTag.F4.tag a' * N₂) := by rw [h1]
      _ = rootDiagUnit ReeTag.F4.tag a' * N₂ := by group
  have hperm₂ : PermAct N₂ (w * ReeTag.F4.weylPerm w) :=
    hNperm.mul (permAct_fext D.isFrob hNC hNperm)
  have hstabw := mem_rootCharStabilizer_of_commute hperm₂ a' hcomm₂
  have hodd : Odd (Nat.card K - 1) := by
    rw [hK, Nat.odd_iff]
    have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
    omega
  have ha1 : a' = 1 := eq_one_of_stab_negAct hstabw hneg hodd hpowj
  have hζ1 : ζA = 1 := by
    apply Subtype.ext
    rw [ha', ha1, rootDiagUnit_one]
    rfl
  rw [hζ1, orderOf_one] at hζo
  have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hK] at hζo
  omega

end Regular

end CFSG.RankThree.PartOne.TCX.Ree
