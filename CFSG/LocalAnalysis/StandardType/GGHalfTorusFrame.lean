module

public import CFSG.LocalAnalysis.StandardType.GGHalfStageADefs
public import CFSG.LocalAnalysis.StandardType.GGHalfFrame
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockCentral

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

theorem exists_inner_action_of_odd_order {G : Type} [Group G] {X : Subgroup G} {d : ℕ}
    (hd : 3 ≤ d) (φ : SpecialLinearGroup (Fin d) F2 →* G) (hφ : φ.range = X)
    (hinj : Function.Injective φ) {b : G} (hb : b ∈ Subgroup.normalizer (X : Set G))
    (hodd : Odd (orderOf b)) :
    ∃ a : SpecialLinearGroup (Fin d) F2, ∀ l ∈ X, b * l * b⁻¹ = φ a * l * (φ a)⁻¹ := by
  let e : ↥X ≃* SpecialLinearGroup (Fin d) F2 :=
    (MulEquiv.subgroupCongr hφ).symm.trans (MonoidHom.ofInjective hinj).symm
  have hsup : b ∈ X ⊔ Subgroup.centralizer (X : Set G) :=
    sup_centralizer_of_odd_order hd e hb hodd
  have hCX : Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G)
  rw [sup_comm] at hsup
  change b ∈ (↑(Subgroup.centralizer (X : Set G) ⊔ X) : Set G) at hsup
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.centralizer (X : Set G)) X hCX]
    at hsup
  rw [Set.mem_mul] at hsup
  obtain ⟨z, hz, k, hk, hzk⟩ := hsup
  rw [← hφ] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨a, ?_⟩
  intro l hl
  have hφa : φ a ∈ X := by rw [← hφ]; exact ⟨a, rfl⟩
  have hm : φ a * l * (φ a)⁻¹ ∈ X := X.mul_mem (X.mul_mem hφa hl) (X.inv_mem hφa)
  have hz_comm : z * (φ a * l * (φ a)⁻¹) = (φ a * l * (φ a)⁻¹) * z :=
    (Subgroup.mem_centralizer_iff.1 hz _ hm).symm
  have hb_eq : b = z * φ a := by rw [← hzk, ← ha]
  calc b * l * b⁻¹ = z * (φ a * l * (φ a)⁻¹) * z⁻¹ := by rw [hb_eq]; group
    _ = (φ a * l * (φ a)⁻¹) * z * z⁻¹ := by rw [hz_comm]
    _ = φ a * l * (φ a)⁻¹ := by group

private theorem inv_conj_eq {G : Type} [Group G] {X : Subgroup G} {b A : G}
    (hA : A ∈ X) (hAc : ∀ l ∈ X, A * l * A⁻¹ = b * l * b⁻¹) :
    ∀ l ∈ X, A⁻¹ * l * A = b⁻¹ * l * b := by
  intro l hl
  have hm : A⁻¹ * l * A ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hA) hl) hA
  have h := hAc (A⁻¹ * l * A) hm
  rw [show A * (A⁻¹ * l * A) * A⁻¹ = l from by group] at h
  have hb : b⁻¹ * l * b = A⁻¹ * l * A := by
    conv_lhs => rw [h]
    group
  exact hb.symm

private theorem pow_three_mem_centralizer {G : Type} [Group G] {X : Subgroup G} {b A : G}
    (hA : A ∈ X) (hAc : ∀ l ∈ X, A * l * A⁻¹ = b * l * b⁻¹) (hb3 : b ^ 3 = 1) :
    A ^ 3 ∈ Subgroup.centralizer (X : Set G) := by
  have hz : A⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : (A⁻¹ * b) * l * (A⁻¹ * b)⁻¹ = l := by
      calc (A⁻¹ * b) * l * (A⁻¹ * b)⁻¹
          = A⁻¹ * (b * l * b⁻¹) * A := by group
        _ = A⁻¹ * (A * l * A⁻¹) * A := by rw [← hAc l hl]
        _ = l := by group
    have hcl : (A⁻¹ * b) * l = l * (A⁻¹ * b) := by
      calc (A⁻¹ * b) * l = (A⁻¹ * b) * l * (A⁻¹ * b)⁻¹ * (A⁻¹ * b) := by group
        _ = l * (A⁻¹ * b) := by rw [h1]
    exact hcl.symm
  have hAz : A * (A⁻¹ * b) = (A⁻¹ * b) * A := Subgroup.mem_centralizer_iff.1 hz A hA
  have hcomm : Commute A (A⁻¹ * b) := hAz
  have hb_eq : A * (A⁻¹ * b) = b := by group
  have h1 : A ^ 3 * (A⁻¹ * b) ^ 3 = 1 := by
    rw [← hcomm.mul_pow, hb_eq, hb3]
  have h2 : A ^ 3 = ((A⁻¹ * b) ^ 3)⁻¹ := by
    calc A ^ 3 = A ^ 3 * (A⁻¹ * b) ^ 3 * ((A⁻¹ * b) ^ 3)⁻¹ := by group
      _ = 1 * ((A⁻¹ * b) ^ 3)⁻¹ := by rw [h1]
      _ = ((A⁻¹ * b) ^ 3)⁻¹ := by group
  rw [h2]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hz 3)

private theorem commutator_mem_centralizer {G : Type} [Group G] {X : Subgroup G} {b b' A A' : G}
    (hA : A ∈ X) (hA' : A' ∈ X)
    (hAc : ∀ l ∈ X, A * l * A⁻¹ = b * l * b⁻¹)
    (hA'c : ∀ l ∈ X, A' * l * A'⁻¹ = b' * l * b'⁻¹)
    (hbb' : b * b' = b' * b) :
    A * A' * A⁻¹ * A'⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hm : A'⁻¹ * l * A' ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hA') hl) hA'
  have hn : A⁻¹ * (A'⁻¹ * l * A') * A ∈ X :=
    X.mul_mem (X.mul_mem (X.inv_mem hA) hm) hA
  have hp : A' * (A⁻¹ * (A'⁻¹ * l * A') * A) * A'⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem hA' hn) (X.inv_mem hA')
  have hconj : A * A' * A⁻¹ * A'⁻¹ * l * (A * A' * A⁻¹ * A'⁻¹)⁻¹ = l := by
    calc A * A' * A⁻¹ * A'⁻¹ * l * (A * A' * A⁻¹ * A'⁻¹)⁻¹
        = A * (A' * (A⁻¹ * (A'⁻¹ * l * A') * A) * A'⁻¹) * A⁻¹ := by group
      _ = b * (A' * (A⁻¹ * (A'⁻¹ * l * A') * A) * A'⁻¹) * b⁻¹ := hAc _ hp
      _ = b * (b' * (A⁻¹ * (A'⁻¹ * l * A') * A) * b'⁻¹) * b⁻¹ := by rw [hA'c _ hn]
      _ = b * (b' * (b⁻¹ * (A'⁻¹ * l * A') * b) * b'⁻¹) * b⁻¹ := by
            rw [inv_conj_eq hA hAc _ hm]
      _ = b * (b' * (b⁻¹ * (b'⁻¹ * l * b') * b) * b'⁻¹) * b⁻¹ := by
            rw [inv_conj_eq hA' hA'c l hl]
      _ = l := by
        have h2 : b'⁻¹ * b⁻¹ = b⁻¹ * b'⁻¹ := by
          rw [← _root_.mul_inv_rev b b', hbb', _root_.mul_inv_rev b' b]
        calc b * (b' * (b⁻¹ * (b'⁻¹ * l * b') * b) * b'⁻¹) * b⁻¹
            = (b * b') * ((b⁻¹ * (b'⁻¹ * l * b') * b) * (b'⁻¹ * b⁻¹)) := by group
          _ = b' * (b * (b⁻¹ * (b'⁻¹ * l * b') * b) * b⁻¹) * b'⁻¹ := by
                rw [hbb', h2]; group
          _ = l := by group
  have hcl : A * A' * A⁻¹ * A'⁻¹ * l = l * (A * A' * A⁻¹ * A'⁻¹) := by
    calc A * A' * A⁻¹ * A'⁻¹ * l
        = A * A' * A⁻¹ * A'⁻¹ * l * (A * A' * A⁻¹ * A'⁻¹)⁻¹ *
            (A * A' * A⁻¹ * A'⁻¹) := by group
      _ = l * (A * A' * A⁻¹ * A'⁻¹) := by rw [hconj]
  exact hcl.symm

theorem exists_conj_torus_of_actions {G : Type} [Group G] {X : Subgroup G} {N : ℕ}
    (hN : 5 ≤ N + 1) (φ : SpecialLinearGroup (Fin (N + 1)) F2 →* G) (hφ : φ.range = X)
    (hinj : Function.Injective φ) {S : Set G}
    (hnorm : ∀ b ∈ S, b ∈ Subgroup.normalizer (X : Set G))
    (hcomm : ∀ b ∈ S, ∀ b' ∈ S, b * b' = b' * b) (hS3 : ∀ b ∈ S, b ^ 3 = 1) :
    ∃ A : SpecialLinearGroup (Fin (N + 1)) F2, ∀ b ∈ S, ∃ t ∈ halfTorus N,
      ∀ l ∈ X, b * l * b⁻¹ = φ (A * t * A⁻¹) * l * (φ (A * t * A⁻¹))⁻¹ := by
  have hodd : ∀ b ∈ S, Odd (orderOf b) := by
    intro b hb
    have hdvd : orderOf b ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (hS3 b hb)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;> rw [h] <;> norm_num
  have hex : ∀ b : ↥S, ∃ a : SpecialLinearGroup (Fin (N + 1)) F2,
      ∀ l ∈ X, (b : G) * l * (b : G)⁻¹ = φ a * l * (φ a)⁻¹ :=
    fun b => exists_inner_action_of_odd_order (by omega) φ hφ hinj (hnorm b b.2) (hodd b b.2)
  choose a ha using hex
  let Tset : Set (SpecialLinearGroup (Fin (N + 1)) F2) := {x | ∃ b : ↥S, a b = x}
  have hφmem : ∀ t : SpecialLinearGroup (Fin (N + 1)) F2, φ t ∈ X := by
    intro t; rw [← hφ]; exact ⟨t, rfl⟩
  have hT3 : ∀ x ∈ Tset, x ^ 3 = 1 := by
    rintro x ⟨b, rfl⟩
    apply eq_one_of_commute_range hinj
    intro t
    rw [map_pow]
    have hAc : ∀ l ∈ X, φ (a b) * l * (φ (a b))⁻¹ = (b : G) * l * (b : G)⁻¹ :=
      fun l hl => (ha b l hl).symm
    have hcent : (φ (a b)) ^ 3 ∈ Subgroup.centralizer (X : Set G) :=
      pow_three_mem_centralizer (hφmem _) hAc (hS3 b b.2)
    exact (Subgroup.mem_centralizer_iff.1 hcent (φ t) (hφmem t)).symm
  have hTc : ∀ x ∈ Tset, ∀ y ∈ Tset, x * y = y * x := by
    rintro x ⟨b, rfl⟩ y ⟨b', rfl⟩
    have hAc : ∀ l ∈ X, φ (a b) * l * (φ (a b))⁻¹ = (b : G) * l * (b : G)⁻¹ :=
      fun l hl => (ha b l hl).symm
    have hA'c : ∀ l ∈ X, φ (a b') * l * (φ (a b'))⁻¹ = (b' : G) * l * (b' : G)⁻¹ :=
      fun l hl => (ha b' l hl).symm
    have hcent := commutator_mem_centralizer (hφmem _) (hφmem _) hAc hA'c
      (hcomm b b.2 b' b'.2)
    have hw : a b * a b' * (a b)⁻¹ * (a b')⁻¹ = 1 := by
      apply eq_one_of_commute_range hinj
      intro t
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact (Subgroup.mem_centralizer_iff.1 hcent (φ t) (hφmem t)).symm
    have hw' : (a b * a b') * (a b' * a b)⁻¹ = 1 := by
      rw [_root_.mul_inv_rev]
      simpa only [mul_assoc] using hw
    exact mul_inv_eq_one.mp hw'
  obtain ⟨A, hA⟩ := exists_conj_into_halfTorus (n := N) Tset hTc hT3
  refine ⟨A, ?_⟩
  intro b hb
  refine ⟨A⁻¹ * a ⟨b, hb⟩ * A, hA (a ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩, ?_⟩
  intro l hl
  rw [show A * (A⁻¹ * a ⟨b, hb⟩ * A) * A⁻¹ = a ⟨b, hb⟩ from by group]
  exact ha ⟨b, hb⟩ l hl

end CFSG.StandardType.GGHalf

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

theorem ggHalf_torusFrame {G : Type} [Group G] [Finite G] {B Bs X : Subgroup G} {p : ℕ}
    (hp : p = 3) (hB : GGBstar p B Bs) {N : ℕ} (hN : 5 ≤ N + 1)
    (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (φ : SpecialLinearGroup (Fin (N + 1)) F2 →* G) (hφ : φ.range = X)
    (hinj : Function.Injective φ) :
    ∃ A : SpecialLinearGroup (Fin (N + 1)) F2,
      GGHalfTorusFrame Bs X (halfTorus N) (φ.comp (MulAut.conj A).toMonoidHom) := by
  subst hp
  have hcomm : ∀ b ∈ Bs, ∀ b' ∈ Bs, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (hB.2.1.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  obtain ⟨A, hA⟩ := exists_conj_torus_of_actions hN φ hφ hinj (S := (Bs : Set G))
    (fun b hb => hnorm hb) hcomm hB.2.1.2
  refine ⟨A, ?_⟩
  set ψ : SpecialLinearGroup (Fin (N + 1)) F2 →* G := φ.comp (MulAut.conj A).toMonoidHom with hψ
  have hψrange : ψ.range = X := by
    rw [hψ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj A).surjective,
      ← MonoidHom.range_eq_map]
    exact hφ
  have hact : ∀ b ∈ Bs, ∃ t ∈ halfTorus N, ∀ l ∈ X, b * l * b⁻¹ = ψ t * l * (ψ t)⁻¹ := by
    intro b hb
    obtain ⟨t, ht, h⟩ := hA b hb
    exact ⟨t, ht, h⟩
  refine ⟨hψrange, hinj.comp (MulAut.conj A).injective, ?_, hact⟩
  rintro _ ⟨t, ht, rfl⟩
  refine hB.2.2.2 _ ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨t', ht', h⟩ := hact b hb
    have hmem : ψ t ∈ X := by
      rw [← hψrange]
      exact ⟨t, rfl⟩
    have hconj : b * ψ t * b⁻¹ = ψ t := by
      rw [h _ hmem, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [halfTorus_comm ht' ht, mul_assoc, mul_inv_cancel, mul_one]
    calc b * ψ t = b * ψ t * b⁻¹ * b := by group
      _ = ψ t * b := by rw [hconj]
  · rw [← map_pow, halfTorus_pow_three ht, map_one]

end CFSG.StandardType

end
