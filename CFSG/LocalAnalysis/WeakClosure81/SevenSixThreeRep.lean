module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeGrpTwo
public import CFSG.LocalAnalysis.UniquenessCase.UCK41

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open CFSG.RankThree.FFModules (fixSub mem_fixSub)
open CFSG.LocalAnalysis.UniquenessCase.UCK (iSup_fixSub_hyperplane_eq_top hyperplaneSet)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

@[expose] def traceSpace (ρ : Representation (ZMod 2) G W) (u : G) : Submodule (ZMod 2) W :=
  LinearMap.range (ρ u - 1)

theorem mem_traceSpace {ρ : Representation (ZMod 2) G W} {u : G} {w : W} :
    w ∈ traceSpace ρ u ↔ ∃ v : W, ρ u v - v = w := by
  simp [traceSpace, LinearMap.mem_range]

private lemma s763R_mul_eq_mul_inv {u y : G} (hu : u * u = 1) (h : u * y * u⁻¹ = y⁻¹) :
    y * u = u * y⁻¹ := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have h1 : u * (u * y * u⁻¹) = u * y⁻¹ := by rw [h]
  have h2 : u * (u * y * u⁻¹) = y * u := by
    calc u * (u * y * u⁻¹) = (u * u) * (y * u⁻¹) := by simp only [mul_assoc]
      _ = y * u := by rw [hu, one_mul, huinv]
  exact h2.symm.trans h1

theorem inverted_card_le_of_representation (ρ : Representation (ZMod 2) G W) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup G} {u : G} (hS : ∀ s ∈ S, s ^ p = 1)
    (hu : u * u = 1) (hinv : ∀ s ∈ S, u * s * u⁻¹ = s⁻¹) (hne : traceSpace ρ u ≠ ⊥)
    (hTI : ∀ y ∈ S, traceSpace ρ u ⊓ (traceSpace ρ u).map (ρ y) ≠ ⊥ → y * u = u * y) :
    Nat.card S ≤ p := by
  have hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    have h1 : u * (s * t) * u⁻¹ = (s * t)⁻¹ := hinv (s * t) (S.mul_mem hs ht)
    have h2 : u * (s * t) * u⁻¹ = s⁻¹ * t⁻¹ := by
      rw [← MulAut.conj_apply u (s * t), map_mul, MulAut.conj_apply u s,
        MulAut.conj_apply u t, hinv s hs, hinv t ht]
    have h3 : (s * t)⁻¹ = (t * s)⁻¹ := by rw [← h1, h2, mul_inv_rev]
    exact inv_injective h3
  have hScomm : IsMulCommutative ↥S :=
    ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  by_cases hSb : S = ⊥
  · rw [hSb, Subgroup.card_eq_one.mpr rfl]
    exact hp.one_le
  · have hA : CFSG.Open.IsElemAbelian p S := ⟨hScomm, hS⟩
    have hgen := iSup_fixSub_hyperplane_eq_top ρ hp hp2 hA hSb
    let f : W →ₗ[ZMod 2] W := ρ u - 1
    have hT : traceSpace ρ u =
        ⨆ B : hyperplaneSet p S, Submodule.map f (fixSub ρ (B : Subgroup G)) := by
      have h1 : traceSpace ρ u = Submodule.map f (⊤ : Submodule (ZMod 2) W) := by
        rw [traceSpace]
        exact LinearMap.range_eq_map (ρ u - 1)
      rw [h1, ← hgen, Submodule.map_iSup]
    have hne' : (⨆ B : hyperplaneSet p S,
        Submodule.map f (fixSub ρ (B : Subgroup G))) ≠ ⊥ := by
      rwa [← hT]
    obtain ⟨B, hBne⟩ : ∃ B : hyperplaneSet p S,
        Submodule.map f (fixSub ρ (B : Subgroup G)) ≠ ⊥ := by
      by_contra h
      exact hne' (iSup_eq_bot.mpr fun B => by
        by_contra hB
        exact h ⟨B, hB⟩)
    have hTB_le : Submodule.map f (fixSub ρ (B : Subgroup G)) ≤ traceSpace ρ u := by
      rw [hT]
      exact le_iSup (fun B : hyperplaneSet p S =>
        Submodule.map f (fixSub ρ (B : Subgroup G))) B
    have hfix : ∀ y ∈ (B : Subgroup G),
        ∀ t ∈ Submodule.map f (fixSub ρ (B : Subgroup G)), ρ y t = t := by
      intro y hy t ht
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp ht
      have hyu : y * u = u * y⁻¹ := s763R_mul_eq_mul_inv hu (hinv y (B.2.1 hy))
      have h1 : ρ y (ρ u w) = ρ u w := by
        have hw' : ρ y⁻¹ w = w := (mem_fixSub.mp hw) y⁻¹ ((B : Subgroup G).inv_mem hy)
        rw [← Module.End.mul_apply, ← map_mul, hyu, map_mul, Module.End.mul_apply, hw']
      have h2 : ρ y w = w := (mem_fixSub.mp hw) y hy
      change ρ y ((ρ u - 1) w) = (ρ u - 1) w
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, h1, h2]
    have hy1 : ∀ y ∈ (B : Subgroup G), y = 1 := by
      intro y hy
      obtain ⟨t, ht, ht0⟩ := (Submodule.ne_bot_iff _).mp hBne
      have hmem : t ∈ traceSpace ρ u ⊓ (traceSpace ρ u).map (ρ y) :=
        ⟨hTB_le ht, Submodule.mem_map.mpr ⟨t, hTB_le ht, hfix y hy t ht⟩⟩
      have hneT : traceSpace ρ u ⊓ (traceSpace ρ u).map (ρ y) ≠ ⊥ :=
        (Submodule.ne_bot_iff _).mpr ⟨t, hmem, ht0⟩
      have hyu : y * u = u * y := hTI y (B.2.1 hy) hneT
      have huinv : y = y⁻¹ := by
        have h : u * y = u * y⁻¹ :=
          hyu.symm.trans (s763R_mul_eq_mul_inv hu (hinv y (B.2.1 hy)))
        exact mul_left_cancel h
      have hyy : y * y = 1 := by
        have h := congrArg (fun z => y * z) huinv
        simpa using h
      obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
      have hpow : y ^ (2 * m + 1) = 1 := by
        rw [← hm]
        exact hS y (B.2.1 hy)
      have hy' : y ^ (2 * m + 1) = y := by
        calc y ^ (2 * m + 1) = y ^ (2 * m) * y := pow_succ y (2 * m)
          _ = (y ^ 2) ^ m * y := by rw [pow_mul]
          _ = y := by rw [show y ^ 2 = y * y from sq y, hyy, one_pow, one_mul]
      rw [hy'] at hpow
      exact hpow
    have hBbot : (B : Subgroup G) = ⊥ :=
      le_antisymm (fun y hy => Subgroup.mem_bot.mpr (hy1 y hy)) bot_le
    have hcard : Nat.card S = p := by
      have h := Subgroup.relIndex_mul_card (H := (B : Subgroup G)) (K := S)
      rw [B.2.2, inf_eq_left.mpr B.2.1, hBbot] at h
      rw [Subgroup.card_eq_one.mpr rfl, mul_one] at h
      exact h.symm
    exact hcard.le

theorem central_card_le_of_representation (ρ : Representation (ZMod 2) G W) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Q S : Subgroup G} {u : G} (hSQ : S ≤ Q)
    (hS : ∀ s ∈ S, s ^ p = 1) (hcent : ∀ s ∈ S, ∀ x ∈ Q, s * x = x * s)
    (hSu : ∀ s ∈ S, u * s = s * u) (hfaith : ∀ s ∈ S, ρ s = 1 → s = 1)
    (hirr : ∀ W' : Submodule (ZMod 2) W, (∀ x ∈ Q, ∀ w ∈ W', ρ x w ∈ W') →
      (∀ w ∈ W', ρ u w ∈ W') → W' = ⊥ ∨ W' = ⊤)
    (hW : Nontrivial W) : Nat.card S ≤ p := by
  have hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    exact hcent s hs t (hSQ ht)
  have hScomm : IsMulCommutative ↥S :=
    ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  by_cases hSb : S = ⊥
  · rw [hSb, Subgroup.card_eq_one.mpr rfl]
    exact hp.one_le
  · have hA : CFSG.Open.IsElemAbelian p S := ⟨hScomm, hS⟩
    have hgen := iSup_fixSub_hyperplane_eq_top ρ hp hp2 hA hSb
    have hbt : (⊥ : Submodule (ZMod 2) W) ≠ ⊤ := by
      intro h
      obtain ⟨x, y, hxy⟩ := hW.exists_pair_ne
      have hx : x ∈ (⊥ : Submodule (ZMod 2) W) := by rw [h]; exact Submodule.mem_top
      have hy : y ∈ (⊥ : Submodule (ZMod 2) W) := by rw [h]; exact Submodule.mem_top
      rw [Submodule.mem_bot] at hx hy
      exact hxy (hx.trans hy.symm)
    have hex : ∃ B : hyperplaneSet p S, fixSub ρ (B : Subgroup G) ≠ ⊥ := by
      by_contra h
      have h' : ∀ B : hyperplaneSet p S, fixSub ρ (B : Subgroup G) = ⊥ := by
        intro B
        by_contra hB
        exact h ⟨B, hB⟩
      have hbot : (⨆ B : hyperplaneSet p S, fixSub ρ (B : Subgroup G)) = ⊥ :=
        iSup_eq_bot.mpr h'
      rw [hgen] at hbot
      exact hbt hbot.symm
    obtain ⟨B, hBne⟩ := hex
    have hInvQ : ∀ x ∈ Q, ∀ w ∈ fixSub ρ (B : Subgroup G),
        ρ x w ∈ fixSub ρ (B : Subgroup G) := by
      intro x hx w hw
      rw [mem_fixSub] at hw ⊢
      intro b hb
      rw [← Module.End.mul_apply, ← map_mul, hcent b (B.2.1 hb) x hx, map_mul,
        Module.End.mul_apply, hw b hb]
    have hInvu : ∀ w ∈ fixSub ρ (B : Subgroup G),
        ρ u w ∈ fixSub ρ (B : Subgroup G) := by
      intro w hw
      rw [mem_fixSub] at hw ⊢
      intro b hb
      rw [← Module.End.mul_apply, ← map_mul, (hSu b (B.2.1 hb)).symm, map_mul,
        Module.End.mul_apply, hw b hb]
    rcases hirr (fixSub ρ (B : Subgroup G)) hInvQ hInvu with hbot | htop
    · exact absurd hbot hBne
    · have hb1 : ∀ b ∈ (B : Subgroup G), b = 1 := by
        intro b hb
        refine hfaith b (B.2.1 hb) (LinearMap.ext fun w => ?_)
        have hw : w ∈ fixSub ρ (B : Subgroup G) := by
          rw [htop]
          exact Submodule.mem_top
        simpa using (mem_fixSub.mp hw) b hb
      have hBbot : (B : Subgroup G) = ⊥ :=
        le_antisymm (fun y hy => Subgroup.mem_bot.mpr (hb1 y hy)) bot_le
      have hcard : Nat.card S = p := by
        have h := Subgroup.relIndex_mul_card (H := (B : Subgroup G)) (K := S)
        rw [B.2.2, inf_eq_left.mpr B.2.1, hBbot] at h
        rw [Subgroup.card_eq_one.mpr rfl, mul_one] at h
        exact h.symm
      exact hcard.le

theorem PInvol.card_main_of_faithful (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {p : ℕ} {Q : Subgroup G} {u : G} (h : PInvol p Q u)
    (hQ : Q ≠ ⊥)
    (hirr : ∀ W' : Submodule (ZMod 2) W, (∀ x ∈ Q, ∀ w ∈ W', ρ x w ∈ W') →
      (∀ w ∈ W', ρ u w ∈ W') → W' = ⊥ ∨ W' = ⊤)
    (hW : Nontrivial W)
    (hTI : ∀ y ∈ Q, traceSpace ρ u ⊓ (traceSpace ρ u).map (ρ y) ≠ ⊥ → y * u = u * y) :
    Nat.card Q = p ∨ (Nat.card Q = p ^ 3 ∧ ∃ x ∈ Q, ∃ y ∈ Q, ⁅x, y⁆ ≠ 1) := by
  have hne : traceSpace ρ u ≠ ⊥ := by
    intro hbot
    have hzero : ρ u - 1 = 0 := by
      rw [traceSpace] at hbot
      exact LinearMap.range_eq_bot.mp hbot
    have hu1 : ρ u = 1 := sub_eq_zero.mp hzero
    have hu : u = 1 := hρ (by rw [hu1, map_one])
    have hQle : Q ≤ ⊥ := by
      have hc := h.le_commutator
      rw [hu, Subgroup.zpowers_eq_bot.mpr rfl, Subgroup.commutator_bot_right] at hc
      exact hc
    exact hQ (le_antisymm hQle bot_le)
  refine PInvol.card_main h hQ ?_ ?_
  · intro S hSQ hinv
    exact inverted_card_le_of_representation ρ h.prime h.odd
      (fun s hs => h.exp s (hSQ hs)) h.sq_eq_one hinv hne
      (fun y hy hyT => hTI y (hSQ hy) hyT)
  · intro S hSQ hcent hSu
    exact central_card_le_of_representation ρ h.prime h.odd hSQ
      (fun s hs => h.exp s (hSQ hs)) hcent hSu
      (fun s hs hs1 => hρ (by rw [hs1, map_one])) hirr hW

end CFSG.LocalAnalysis.WeakClosure81
