module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.RankThree.PartTwo.KFacts.KS14MultCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped commutatorElement

theorem not_dvd_card_ker_of_isPerfect_of_isCyclic_sylow {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Group.IsPerfect X] (f : X →* Y) (hker : f.ker ≤ Subgroup.center X) {q : ℕ}
    (hq : q.Prime) (hY : ∀ Q : Sylow q Y, IsCyclic Q) : ¬ q ∣ Nat.card f.ker := by
  intro hqZ
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨⟨z, hzZ⟩, hz⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) q hqZ
  have hzo : orderOf z = q := by rw [← hz, Subgroup.orderOf_mk]
  obtain ⟨P, hzP⟩ : ∃ P : Sylow q X, z ∈ (P : Subgroup X) := by
    have hpg : IsPGroup q (Subgroup.zpowers z) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hzo, pow_one]
    obtain ⟨P, hP⟩ := hpg.exists_le_sylow
    exact ⟨P, hP (Subgroup.mem_zpowers z)⟩
  have hPcomm : ∀ a b : (P : Subgroup X), a * b = b * a := by
    set g : (P : Subgroup X) →* Y := f.comp (P : Subgroup X).subtype with hg
    have hR : IsPGroup q g.range :=
      (P.isPGroup').of_surjective g.rangeRestrict g.rangeRestrict_surjective
    obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
    have hQ := hY Q
    have hcyc : IsCyclic g.range :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hRQ).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hRQ).surjective
    have hker' : g.rangeRestrict.ker ≤ Subgroup.center (P : Subgroup X) := by
      intro a ha
      rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hg, MonoidHom.comp_apply,
        Subgroup.coe_subtype] at ha
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hker ha) b)
    exact (g.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center hker').is_comm.comm
  have hpow := CFSG.RankThree.PartTwo.KFacts.KS14.pow_index_eq_one_of_isPerfect
    (P : Subgroup X) hPcomm (hker hzZ)
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  rw [hzo] at hdvd
  exact P.not_dvd_index hdvd

theorem exists_perfect_pair_of_surjective_prod {Q A B : Type*} [Group Q] [Group A] [Group B]
    (hQ : Group.IsPerfect Q) (f : Q →* A × B) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center Q) :
    ∃ H₁ H₂ : Subgroup Q, ⁅H₁, H₁⁆ = H₁ ∧ ⁅H₂, H₂⁆ = H₂ ∧
      (∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) ∧ H₁ ⊔ H₂ = ⊤ ∧
      (∀ x ∈ H₁, (f x).2 = 1) ∧ (∀ y ∈ H₂, (f y).1 = 1) ∧
      (∀ a : A, ∃ x ∈ H₁, (f x).1 = a) ∧ (∀ b : B, ∃ y ∈ H₂, (f y).2 = b) := by
  haveI : Group.IsPerfect Q := hQ
  classical
  let p : Q →* A := (MonoidHom.fst A B).comp f
  let q : Q →* B := (MonoidHom.snd A B).comp f
  let N₁ : Subgroup Q := q.ker
  let N₂ : Subgroup Q := p.ker
  let Z : Subgroup Q := f.ker
  let H₁ : Subgroup Q := ⁅N₁, N₁⁆
  let H₂ : Subgroup Q := ⁅N₂, N₂⁆
  have hp : Function.Surjective p := by
    intro a
    obtain ⟨x, hx⟩ := hf (a, 1)
    exact ⟨x, by simp [p, hx]⟩
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨x, hx⟩ := hf (1, b)
    exact ⟨x, by simp [q, hx]⟩
  have hAperf : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := p) hp
  have hBperf : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := q) hq
  haveI := hAperf
  haveI := hBperf
  have hZ_center : Z ≤ Subgroup.center Q := hker
  have hmapN₁ : Subgroup.map p N₁ = ⊤ := by
    rw [eq_top_iff]
    intro a _
    rw [Subgroup.mem_map]
    obtain ⟨x, hx⟩ := hf (a, 1)
    exact ⟨x, by simpa [N₁, q, hx], by simpa [p, hx]⟩
  have hmapN₂ : Subgroup.map q N₂ = ⊤ := by
    rw [eq_top_iff]
    intro b _
    rw [Subgroup.mem_map]
    obtain ⟨x, hx⟩ := hf (1, b)
    exact ⟨x, by simpa [N₂, p, hx], by simpa [q, hx]⟩
  have hmapH₁ : Subgroup.map p H₁ = ⊤ := by
    rw [Subgroup.map_commutator, hmapN₁, ← commutator_def]
    exact hAperf.commutator_eq_top
  have hmapH₂ : Subgroup.map q H₂ = ⊤ := by
    rw [Subgroup.map_commutator, hmapN₂, ← commutator_def]
    exact hBperf.commutator_eq_top
  have hH₁_le_N₁ : H₁ ≤ N₁ :=
    Subgroup.commutator_le_left (G := Q) (H₁ := N₁) (H₂ := N₁)
  have hH₂_le_N₂ : H₂ ≤ N₂ :=
    Subgroup.commutator_le_left (G := Q) (H₁ := N₂) (H₂ := N₂)
  have hZ_le_N₁ : Z ≤ N₁ := by
    intro x hx
    have hx1 : f x = 1 := hx
    simpa [N₁, q, hx1]
  have hZ_le_N₂ : Z ≤ N₂ := by
    intro x hx
    have hx1 : f x = 1 := hx
    simpa [N₂, p, hx1]
  have hN₁_le : N₁ ≤ H₁ ⊔ Z := by
    intro x hx
    have hxmem : p x ∈ Subgroup.map p H₁ := by
      rw [hmapH₁]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_map] at hxmem
    obtain ⟨h, hhH, hph⟩ := hxmem
    have hhN : h ∈ N₁ := hH₁_le_N₁ hhH
    have hxq : q x = 1 := hx
    have hhq : q h = 1 := hhN
    have hzh : x * h⁻¹ ∈ Z := by
      change f (x * h⁻¹) = 1
      rw [map_mul, map_inv, show f x = (p x, q x) from rfl,
        show f h = (p h, q h) from rfl, hph, hxq, hhq]
      simp
    have hx_eq : x = (x * h⁻¹) * h := by simp
    rw [hx_eq]
    exact (H₁ ⊔ Z).mul_mem (Subgroup.mem_sup_right hzh) (Subgroup.mem_sup_left hhH)
  have hN₁_eq : N₁ = H₁ ⊔ Z := le_antisymm hN₁_le (sup_le hH₁_le_N₁ hZ_le_N₁)
  have hN₂_le : N₂ ≤ H₂ ⊔ Z := by
    intro x hx
    have hxmem : q x ∈ Subgroup.map q H₂ := by
      rw [hmapH₂]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_map] at hxmem
    obtain ⟨h, hhH, hqh⟩ := hxmem
    have hhN : h ∈ N₂ := hH₂_le_N₂ hhH
    have hxp : p x = 1 := hx
    have hhp : p h = 1 := hhN
    have hzh : x * h⁻¹ ∈ Z := by
      change f (x * h⁻¹) = 1
      rw [map_mul, map_inv, show f x = (p x, q x) from rfl,
        show f h = (p h, q h) from rfl, hxp, hhp, hqh]
      simp
    have hx_eq : x = (x * h⁻¹) * h := by simp
    rw [hx_eq]
    exact (H₂ ⊔ Z).mul_mem (Subgroup.mem_sup_right hzh) (Subgroup.mem_sup_left hhH)
  have hN₂_eq : N₂ = H₂ ⊔ Z := le_antisymm hN₂_le (sup_le hH₂_le_N₂ hZ_le_N₂)
  have hN₁N₂_center : ⁅N₁, N₂⁆ ≤ Subgroup.center Q := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine hZ_center ?_
    change f ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    have hx2 : (f x).2 = 1 := by simpa [N₁, q] using hx
    have hy1 : (f y).1 = 1 := by simpa [N₂, p] using hy
    have hfx : f x = ((f x).1, 1) := Prod.ext rfl hx2
    have hfy : f y = (1, (f y).2) := Prod.ext hy1 rfl
    rw [hfx, hfy]
    ext <;> simp [commutatorElement_def]
  have hrot1 : ⁅⁅N₁, N₂⁆, N₁⁆ = ⊥ := by
    rw [← le_bot_iff]
    calc ⁅⁅N₁, N₂⁆, N₁⁆ ≤ ⁅Subgroup.center Q, N₁⁆ :=
          Subgroup.commutator_mono hN₁N₂_center le_rfl
      _ = ⊥ := Subgroup.commutator_center_left N₁
  have hrot2 : ⁅⁅N₂, N₁⁆, N₁⁆ = ⊥ := by
    rw [Subgroup.commutator_comm N₂ N₁]
    exact hrot1
  have hH₁N₂ : ⁅H₁, N₂⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hrot1 hrot2
  have hrot3 : ⁅⁅N₂, N₁⁆, N₂⁆ = ⊥ := by
    rw [← le_bot_iff]
    have hc : ⁅N₂, N₁⁆ ≤ Subgroup.center Q := by
      rw [Subgroup.commutator_comm]
      exact hN₁N₂_center
    calc ⁅⁅N₂, N₁⁆, N₂⁆ ≤ ⁅Subgroup.center Q, N₂⁆ :=
          Subgroup.commutator_mono hc le_rfl
      _ = ⊥ := Subgroup.commutator_center_left N₂
  have hrot4 : ⁅⁅N₁, N₂⁆, N₂⁆ = ⊥ := by
    rw [Subgroup.commutator_comm N₁ N₂]
    exact hrot3
  have hH₂N₁ : ⁅H₂, N₁⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hrot3 hrot4
  have hcommH₁N₂ : ∀ x ∈ H₁, ∀ y ∈ N₂, x * y = y * x := by
    intro x hx y hy
    have hle : H₁ ≤ Subgroup.centralizer (N₂ : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hH₁N₂
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm
  have hZN₂ : ⁅Z, N₂⁆ = ⊥ := by
    rw [← le_bot_iff]
    calc ⁅Z, N₂⁆ ≤ ⁅Subgroup.center Q, (⊤ : Subgroup Q)⁆ :=
          Subgroup.commutator_mono hZ_center le_top
      _ = ⊥ := Subgroup.commutator_center_left ⊤
  have hN₁N₂_bot : ⁅N₁, N₂⁆ = ⊥ := by
    rw [hN₁_eq, Subgroup.commutator_sup_right, hH₁N₂, hZN₂]
    simp
  have hbot1 : ⁅H₁, Z⁆ = ⊥ := by
    rw [← le_bot_iff]
    calc ⁅H₁, Z⁆ ≤ ⁅(⊤ : Subgroup Q), Subgroup.center Q⁆ :=
          Subgroup.commutator_mono le_top hZ_center
      _ = ⊥ := Subgroup.commutator_center_right ⊤
  have hbot2 : ⁅Z, H₁⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hbot1
  have hbot3 : ⁅Z, Z⁆ = ⊥ := by
    rw [← le_bot_iff]
    calc ⁅Z, Z⁆ ≤ ⁅Subgroup.center Q, (⊤ : Subgroup Q)⁆ :=
          Subgroup.commutator_mono hZ_center le_top
      _ = ⊥ := Subgroup.commutator_center_left ⊤
  have hH₁_perf : ⁅H₁, H₁⁆ = H₁ := by
    have hlow : ⁅H₁, H₁⁆ ≤ H₁ :=
      (Subgroup.commutator_mono hH₁_le_N₁ hH₁_le_N₁).trans (le_of_eq rfl)
    have hhigh : H₁ ≤ ⁅H₁, H₁⁆ := by
      have hsup1 : H₁ = (⁅H₁ ⊔ Z, H₁ ⊔ Z⁆ : Subgroup Q) := by rw [← hN₁_eq]
      have hsup2 : (⁅H₁ ⊔ Z, H₁ ⊔ Z⁆ : Subgroup Q) = ⁅H₁, H₁⁆ := by
        rw [Subgroup.commutator_sup_right, Subgroup.commutator_sup_left,
          Subgroup.commutator_sup_left, hbot1, hbot2, hbot3]
        simp
      exact hsup1.le.trans (le_of_eq hsup2)
    exact le_antisymm hlow hhigh
  have hbot1' : ⁅H₂, Z⁆ = ⊥ := by
    rw [← le_bot_iff]
    calc ⁅H₂, Z⁆ ≤ ⁅(⊤ : Subgroup Q), Subgroup.center Q⁆ :=
          Subgroup.commutator_mono le_top hZ_center
      _ = ⊥ := Subgroup.commutator_center_right ⊤
  have hbot2' : ⁅Z, H₂⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hbot1'
  have hH₂_perf : ⁅H₂, H₂⁆ = H₂ := by
    have hlow : ⁅H₂, H₂⁆ ≤ H₂ :=
      (Subgroup.commutator_mono hH₂_le_N₂ hH₂_le_N₂).trans (le_of_eq rfl)
    have hhigh : H₂ ≤ ⁅H₂, H₂⁆ := by
      have hsup1 : H₂ = (⁅H₂ ⊔ Z, H₂ ⊔ Z⁆ : Subgroup Q) := by rw [← hN₂_eq]
      have hsup2 : (⁅H₂ ⊔ Z, H₂ ⊔ Z⁆ : Subgroup Q) = ⁅H₂, H₂⁆ := by
        rw [Subgroup.commutator_sup_right, Subgroup.commutator_sup_left,
          Subgroup.commutator_sup_left, hbot1', hbot2', hbot3]
        simp
      exact hsup1.le.trans (le_of_eq hsup2)
    exact le_antisymm hlow hhigh
  have hH₁H₂_bot : ⁅H₁, H₂⁆ = ⊥ := by
    rw [← le_bot_iff]
    calc ⁅H₁, H₂⁆ ≤ ⁅N₁, N₂⁆ := Subgroup.commutator_mono hH₁_le_N₁ hH₂_le_N₂
      _ = ⊥ := hN₁N₂_bot
  have hcommH₁H₂ : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x := by
    intro x hx y hy
    have hbot : ⁅x, y⁆ = 1 := by
      have hle : ⁅H₁, H₂⁆ ≤ ⊥ := hH₁H₂_bot ▸ le_rfl
      exact Subgroup.mem_bot.mp (Subgroup.commutator_le.mp hle x hx y hy)
    exact commutatorElement_eq_one_iff_mul_comm.mp hbot
  have hNsup : N₁ ⊔ N₂ = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨x, hx⟩ := hf ((f z).1, 1)
    obtain ⟨y, hy⟩ := hf (1, (f z).2)
    have hxN₁ : x ∈ N₁ := by simpa [N₁, q, hx]
    have hyN₂ : y ∈ N₂ := by simpa [N₂, p, hy]
    have hxy : f (x * y) = f z := by
      rw [map_mul, hx, hy]
      exact Prod.ext (mul_one _) (one_mul _)
    have hzZ : z * (x * y)⁻¹ ∈ Z := by
      change f (z * (x * y)⁻¹) = 1
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hz_eq : z = (z * (x * y)⁻¹) * (x * y) := by group
    rw [hz_eq]
    exact (N₁ ⊔ N₂).mul_mem (Subgroup.mem_sup_left (hZ_le_N₁ hzZ))
      (Subgroup.mul_mem_sup hxN₁ hyN₂)
  have hHsup : H₁ ⊔ H₂ = ⊤ := by
    have hN₂N₁_bot : ⁅N₂, N₁⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hN₁N₂_bot
    have hmain : (⁅N₁ ⊔ N₂, N₁ ⊔ N₂⁆ : Subgroup Q) = H₁ ⊔ H₂ := by
      rw [Subgroup.commutator_sup_right, Subgroup.commutator_sup_left,
        Subgroup.commutator_sup_left, hN₁N₂_bot, hN₂N₁_bot]
      simp only [sup_bot_eq, bot_sup_eq]
      rfl
    have htop : (⁅N₁ ⊔ N₂, N₁ ⊔ N₂⁆ : Subgroup Q) = ⁅(⊤ : Subgroup Q), ⊤⁆ := by
      rw [hNsup]
    rw [← hmain, htop, ← commutator_def]
    exact hQ.commutator_eq_top
  refine ⟨H₁, H₂, hH₁_perf, hH₂_perf, hcommH₁H₂, hHsup, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hH₁_le_N₁ hx
  · intro y hy
    exact hH₂_le_N₂ hy
  · intro a
    have hmem : a ∈ Subgroup.map p H₁ := by
      rw [hmapH₁]
      exact Subgroup.mem_top a
    rw [Subgroup.mem_map] at hmem
    obtain ⟨x, hxH, hpx⟩ := hmem
    exact ⟨x, hxH, hpx⟩
  · intro b
    have hmem : b ∈ Subgroup.map q H₂ := by
      rw [hmapH₂]
      exact Subgroup.mem_top b
    rw [Subgroup.mem_map] at hmem
    obtain ⟨y, hyH, hqy⟩ := hmem
    exact ⟨y, hyH, hqy⟩

private lemma exists_mul_of_mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {z : G} (hz : z ∈ H ⊔ K) :
    ∃ x ∈ H, ∃ y ∈ K, z = x * y := by
  let S : Subgroup G :=
    { carrier := {z | ∃ x ∈ H, ∃ y ∈ K, z = x * y}
      mul_mem' := by
        rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
        refine ⟨x * x', H.mul_mem hx hx', y * y', K.mul_mem hy hy', ?_⟩
        have hyx : y * x' = x' * y := (hcomm x' hx' y hy).symm
        calc x * y * (x' * y') = x * (y * x') * y' := by group
          _ = x * (x' * y) * y' := by rw [hyx]
          _ = x * x' * (y * y') := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        refine ⟨x⁻¹, H.inv_mem hx, y⁻¹, K.inv_mem hy, ?_⟩
        calc (x * y)⁻¹ = (y * x)⁻¹ := by rw [hcomm x hx y hy]
          _ = x⁻¹ * y⁻¹ := by rw [mul_inv_rev] }
  have hH : H ≤ S := fun x hx => ⟨x, hx, 1, K.one_mem, by simp⟩
  have hK : K ≤ S := fun y hy => ⟨1, H.one_mem, y, hy, by simp⟩
  exact (sup_le hH hK) hz

theorem not_dvd_card_ker_of_isPerfect_prod {Q A B : Type*} [Group Q] [Finite Q] [Group A]
    [Group B] (hQ : Group.IsPerfect Q) (f : Q →* A × B) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center Q) {q : ℕ} (hq : q.Prime)
    (hA : ∀ P : Sylow q A, IsCyclic P) (hB : ∀ P : Sylow q B, IsCyclic P) :
    ¬ q ∣ Nat.card f.ker := by
  obtain ⟨H₁, H₂, hH₁, hH₂, hcomm, hsup, hf₂, hf₁, hsurjA, hsurjB⟩ :=
    exists_perfect_pair_of_surjective_prod hQ f hf hker
  classical
  let g₁ : ↥H₁ →* A := (MonoidHom.fst A B).comp (f.comp H₁.subtype)
  let g₂ : ↥H₂ →* B := (MonoidHom.snd A B).comp (f.comp H₂.subtype)
  have hg₁ : Function.Surjective g₁ := by
    intro a
    obtain ⟨x, hxH, hx⟩ := hsurjA a
    exact ⟨⟨x, hxH⟩, hx⟩
  have hg₂ : Function.Surjective g₂ := by
    intro b
    obtain ⟨y, hyH, hy⟩ := hsurjB b
    exact ⟨⟨y, hyH⟩, hy⟩
  have hker₁ : g₁.ker ≤ Subgroup.center ↥H₁ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : (f (x : Q)).1 = 1 := by simpa [g₁] using MonoidHom.mem_ker.mp hx
    have hx2 : (f (x : Q)).2 = 1 := hf₂ (x : Q) x.2
    have hxZ : (x : Q) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      exact Prod.ext hx1 hx2
    have hxc : (x : Q) ∈ Subgroup.center Q := hker hxZ
    exact Subtype.ext (by simpa using Subgroup.mem_center_iff.mp hxc (y : Q))
  have hker₂ : g₂.ker ≤ Subgroup.center ↥H₂ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : (f (x : Q)).1 = 1 := hf₁ (x : Q) x.2
    have hx2 : (f (x : Q)).2 = 1 := by simpa [g₂] using MonoidHom.mem_ker.mp hx
    have hxZ : (x : Q) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      exact Prod.ext hx1 hx2
    have hxc : (x : Q) ∈ Subgroup.center Q := hker hxZ
    exact Subtype.ext (by simpa using Subgroup.mem_center_iff.mp hxc (y : Q))
  haveI : Finite ↥H₁ := Subtype.finite
  haveI : Finite ↥H₂ := Subtype.finite
  haveI : Group.IsPerfect ↥H₁ := Subgroup.isPerfect_iff.mpr hH₁
  haveI : Group.IsPerfect ↥H₂ := Subgroup.isPerfect_iff.mpr hH₂
  have hnd₁ : ¬ q ∣ Nat.card g₁.ker :=
    not_dvd_card_ker_of_isPerfect_of_isCyclic_sylow g₁ hker₁ hq hA
  have hnd₂ : ¬ q ∣ Nat.card g₂.ker :=
    not_dvd_card_ker_of_isPerfect_of_isCyclic_sylow g₂ hker₂ hq hB
  let φ : ↥g₁.ker × ↥g₂.ker →* Q :=
    { toFun := fun p => ((p.1 : ↥H₁) : Q) * ((p.2 : ↥H₂) : Q)
      map_one' := by simp
      map_mul' := by
        intro p r
        have hcb : ((r.1 : ↥H₁) : Q) * ((p.2 : ↥H₂) : Q)
            = ((p.2 : ↥H₂) : Q) * ((r.1 : ↥H₁) : Q) :=
          hcomm ((r.1 : ↥H₁) : Q) (r.1 : ↥H₁).2 ((p.2 : ↥H₂) : Q) (p.2 : ↥H₂).2
        show (((p.1 : ↥H₁) : Q) * ((r.1 : ↥H₁) : Q))
            * (((p.2 : ↥H₂) : Q) * ((r.2 : ↥H₂) : Q))
          = (((p.1 : ↥H₁) : Q) * ((p.2 : ↥H₂) : Q))
            * (((r.1 : ↥H₁) : Q) * ((r.2 : ↥H₂) : Q))
        calc (((p.1 : ↥H₁) : Q) * ((r.1 : ↥H₁) : Q))
              * (((p.2 : ↥H₂) : Q) * ((r.2 : ↥H₂) : Q))
            = ((p.1 : ↥H₁) : Q)
              * (((r.1 : ↥H₁) : Q) * (((p.2 : ↥H₂) : Q) * ((r.2 : ↥H₂) : Q))) := by
                group
          _ = ((p.1 : ↥H₁) : Q)
              * ((((r.1 : ↥H₁) : Q) * ((p.2 : ↥H₂) : Q)) * ((r.2 : ↥H₂) : Q)) := by
                group
          _ = ((p.1 : ↥H₁) : Q)
              * ((((p.2 : ↥H₂) : Q) * ((r.1 : ↥H₁) : Q)) * ((r.2 : ↥H₂) : Q)) := by
                rw [hcb]
          _ = (((p.1 : ↥H₁) : Q) * ((p.2 : ↥H₂) : Q))
              * (((r.1 : ↥H₁) : Q) * ((r.2 : ↥H₂) : Q)) := by
                group }
  have hrange : φ.range = f.ker := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      have h1 : f ((p.1 : ↥H₁) : Q) = 1 := by
        ext
        · simpa [g₁] using MonoidHom.mem_ker.mp p.1.2
        · exact hf₂ ((p.1 : ↥H₁) : Q) (p.1 : ↥H₁).2
      have h2 : f ((p.2 : ↥H₂) : Q) = 1 := by
        ext
        · exact hf₁ ((p.2 : ↥H₂) : Q) (p.2 : ↥H₂).2
        · simpa [g₂] using MonoidHom.mem_ker.mp p.2.2
      rw [MonoidHom.mem_ker]
      show f (((p.1 : ↥H₁) : Q) * ((p.2 : ↥H₂) : Q)) = 1
      rw [map_mul, h1, h2, mul_one]
    · intro hz
      have hzsup : z ∈ H₁ ⊔ H₂ := by rw [hsup]; exact Subgroup.mem_top z
      obtain ⟨x, hxH, y, hyH, hxy⟩ := exists_mul_of_mem_sup_of_commute hcomm hzsup
      have hfx1 : (f x).1 = 1 := by
        have h : f x * f y = 1 := by
          have hz1 : f z = 1 := hz
          rwa [hxy, map_mul] at hz1
        have hy1 : (f y).1 = 1 := hf₁ y hyH
        have := congrArg Prod.fst h
        simpa [hy1] using this
      have hfy2 : (f y).2 = 1 := by
        have h : f x * f y = 1 := by
          have hz1 : f z = 1 := hz
          rwa [hxy, map_mul] at hz1
        have hx2 : (f x).2 = 1 := hf₂ x hxH
        have := congrArg Prod.snd h
        simpa [hx2] using this
      have hxg₁ : (⟨x, hxH⟩ : ↥H₁) ∈ g₁.ker := by
        rw [MonoidHom.mem_ker]
        simpa [g₁] using hfx1
      have hyg₂ : (⟨y, hyH⟩ : ↥H₂) ∈ g₂.ker := by
        rw [MonoidHom.mem_ker]
        simpa [g₂] using hfy2
      rw [MonoidHom.mem_range]
      refine ⟨(⟨⟨x, hxH⟩, hxg₁⟩, ⟨⟨y, hyH⟩, hyg₂⟩), ?_⟩
      show ((⟨x, hxH⟩ : ↥H₁) : Q) * ((⟨y, hyH⟩ : ↥H₂) : Q) = z
      rw [hxy]
  have hdvd : Nat.card φ.range ∣ Nat.card g₁.ker * Nat.card g₂.ker := by
    rw [← Nat.card_prod]
    exact Subgroup.card_range_dvd φ
  have hnd : ¬ q ∣ Nat.card g₁.ker * Nat.card g₂.ker := by
    rintro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · exact hnd₁ h
    · exact hnd₂ h
  intro hqker
  rw [← hrange] at hqker
  exact hnd (dvd_trans hqker hdvd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
