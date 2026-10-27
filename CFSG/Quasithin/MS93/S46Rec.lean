module

public import CFSG.Quasithin.MS93.S4AFSec
public import CFSG.Quasithin.MS93.ML3RecBridge
public import CFSG.Quasithin.MS93.M16Dual
public import CFSG.Quasithin.MS93.ML3Aut

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

section Roots

variable {F : Type} [Field F]

private theorem conj_mem_sup {A B : Subgroup (SL3 F)} {x : SL3 F}
    (hA : ∀ a ∈ A, x * a * x⁻¹ ∈ A ⊔ B) (hB : ∀ b ∈ B, x * b * x⁻¹ ∈ A ⊔ B) {g : SL3 F}
    (hg : g ∈ A ⊔ B) : x * g * x⁻¹ ∈ A ⊔ B := by
  have h : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj x).toMonoidHom :=
    sup_le (fun a ha => by simpa using hA a ha) (fun b hb => by simpa using hB b hb)
  simpa using h hg

private theorem conj_eq_commutator_mul (h g : SL3 F) : h * g * h⁻¹ = ⁅h, g⁆ * g := by
  rw [commutatorElement_def]
  group

theorem rootElt12_conj_mem_qPt (c : F) {g : SL3 F} (hg : g ∈ (qPt : Subgroup (SL3 F))) :
    rootElt 1 2 c * g * (rootElt 1 2 c)⁻¹ ∈ (qPt : Subgroup (SL3 F)) := by
  unfold qPt at hg ⊢
  refine conj_mem_sup (fun a ha => ?_) (fun b hb => ?_) hg
  · obtain ⟨a, rfl⟩ := mem_rootGroup.mp ha
    rw [conj_eq_commutator_mul, ← commutatorElement_inv,
      rootElt_commutator (i := 0) (j := 1) (l := 2) (by decide) (by decide) (by decide)]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _
      (Subgroup.mem_sup_right (rootElt_mem_rootGroup 0 2 _)))
      (Subgroup.mem_sup_left (rootElt_mem_rootGroup 0 1 a))
  · obtain ⟨b, rfl⟩ := mem_rootGroup.mp hb
    rw [(rootElt_commute (i := 1) (j := 2) (k := 0) (l := 2) (by decide) (by decide) c b).eq,
      mul_inv_cancel_right]
    exact Subgroup.mem_sup_right (rootElt_mem_rootGroup 0 2 b)

theorem rootElt21_conj_mem_qPt (c : F) {g : SL3 F} (hg : g ∈ (qPt : Subgroup (SL3 F))) :
    rootElt 2 1 c * g * (rootElt 2 1 c)⁻¹ ∈ (qPt : Subgroup (SL3 F)) := by
  unfold qPt at hg ⊢
  refine conj_mem_sup (fun a ha => ?_) (fun b hb => ?_) hg
  · obtain ⟨a, rfl⟩ := mem_rootGroup.mp ha
    rw [(rootElt_commute (i := 2) (j := 1) (k := 0) (l := 1) (by decide) (by decide) c a).eq,
      mul_inv_cancel_right]
    exact Subgroup.mem_sup_left (rootElt_mem_rootGroup 0 1 a)
  · obtain ⟨b, rfl⟩ := mem_rootGroup.mp hb
    rw [conj_eq_commutator_mul, ← commutatorElement_inv,
      rootElt_commutator (i := 0) (j := 2) (l := 1) (by decide) (by decide) (by decide)]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _
      (Subgroup.mem_sup_left (rootElt_mem_rootGroup 0 1 _)))
      (Subgroup.mem_sup_right (rootElt_mem_rootGroup 0 2 b))

theorem tor_conj_mem_qPt (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) {g : SL3 F}
    (hg : g ∈ (qPt : Subgroup (SL3 F))) :
    M16.tor a b ha hb * g * (M16.tor a b ha hb)⁻¹ ∈ (qPt : Subgroup (SL3 F)) := by
  unfold qPt at hg ⊢
  refine conj_mem_sup (fun x hx => ?_) (fun x hx => ?_) hg
  · obtain ⟨c, rfl⟩ := mem_rootGroup.mp hx
    rw [M16.tor_conj_rootElt]
    exact Subgroup.mem_sup_left (rootElt_mem_rootGroup _ _ _)
  · obtain ⟨c, rfl⟩ := mem_rootGroup.mp hx
    rw [M16.tor_conj_rootElt]
    exact Subgroup.mem_sup_right (rootElt_mem_rootGroup _ _ _)

theorem commutator_qPt_rootElt12 (a b c : F) :
    ⁅rootElt 0 1 a * rootElt 0 2 b, rootElt 1 2 c⁆ = rootElt 0 2 (a * c) := by
  have hBC : rootElt 0 2 b * rootElt 1 2 c = rootElt 1 2 c * rootElt 0 2 b :=
    (rootElt_commute (i := 0) (j := 2) (k := 1) (l := 2) (by decide) (by decide) b c).eq
  rw [← rootElt_commutator (i := 0) (j := 1) (l := 2) (by decide) (by decide) (by decide)]
  simp only [commutatorElement_def]
  calc rootElt 0 1 a * rootElt 0 2 b * rootElt 1 2 c * (rootElt 0 1 a * rootElt 0 2 b)⁻¹ *
        (rootElt 1 2 c)⁻¹ = rootElt 0 1 a * (rootElt 0 2 b * rootElt 1 2 c) *
        (rootElt 0 2 b)⁻¹ * (rootElt 0 1 a)⁻¹ * (rootElt 1 2 c)⁻¹ := by group
    _ = rootElt 0 1 a * rootElt 1 2 c * (rootElt 0 1 a)⁻¹ * (rootElt 1 2 c)⁻¹ := by
        rw [hBC]
        group

theorem commutator_qPt_rootElt21 (a b c : F) :
    ⁅rootElt 0 1 a * rootElt 0 2 b, rootElt 2 1 c⁆ = rootElt 0 1 (b * c) := by
  have hAD : Commute (rootElt 0 1 a)⁻¹ (rootElt 2 1 c) :=
    (rootElt_commute (i := 0) (j := 1) (k := 2) (l := 1) (by decide) (by decide) a c).inv_left
  have hBD : ⁅rootElt 0 2 b, rootElt 2 1 c⁆ = rootElt 0 1 (b * c) :=
    rootElt_commutator (i := 0) (j := 2) (l := 1) (by decide) (by decide) (by decide) b c
  have hAE : rootElt 0 1 a * rootElt 0 1 (b * c) = rootElt 0 1 (b * c) * rootElt 0 1 a := by
    rw [← rootElt_add, ← rootElt_add, add_comm]
  calc ⁅rootElt 0 1 a * rootElt 0 2 b, rootElt 2 1 c⁆ =
        rootElt 0 1 a * ⁅rootElt 0 2 b, rootElt 2 1 c⁆ *
          (rootElt 2 1 c * (rootElt 0 1 a)⁻¹ * (rootElt 2 1 c)⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = rootElt 0 1 a * rootElt 0 1 (b * c) * (rootElt 0 1 a)⁻¹ := by
        rw [hBD, ← hAD.eq, mul_inv_cancel_right]
    _ = rootElt 0 1 (b * c) := by rw [hAE, mul_inv_cancel_right]

end Roots

section Mod

variable {F : Type} [Field F] {X : Type} [CommGroup X] (ρ : SL3 F →* MulAut X)

private def stabX (x : X) : Subgroup (SL3 F) where
  carrier := {g | ρ g x = x}
  mul_mem' := fun {g h} hg hh => by
    change ρ (g * h) x = x
    rw [M16.rho_mul, hh, hg]
  one_mem' := by
    change ρ 1 x = x
    rw [map_one, MulAut.one_apply]
  inv_mem' := fun {g} hg => by
    change ρ g⁻¹ x = x
    have h := M16.rho_inv_rho ρ g x
    rwa [show ρ g x = x from hg] at h

private theorem mem_stabX {x : X} {g : SL3 F} : g ∈ stabX ρ x ↔ ρ g x = x := Iff.rfl

theorem rho_mem_commV_map {A : Subgroup (SL3 F)} {x : SL3 F} (hx : ∀ g ∈ A, x * g * x⁻¹ ∈ A)
    {r : X} (hr : r ∈ commV (A.map ρ)) : ρ x r ∈ commV (A.map ρ) := by
  induction hr using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨_, ⟨g, hg, rfl⟩, v, rfl⟩ := hc
    have e : ρ (x * g * x⁻¹) (ρ x v) * (ρ x v)⁻¹ = ρ x (ρ g v * v⁻¹) := by
      rw [M16.rho_mul, M16.rho_mul, M16.rho_inv_rho, map_mul, map_inv]
    rw [← e]
    exact Subgroup.subset_closure ⟨_, ⟨_, hx g hg, rfl⟩, _, rfl⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem ptLevi_fix_of_card [Finite F] [Finite X]
    (hR : Nat.card (commV ((qPt : Subgroup (SL3 F)).map ρ)) ≤ Nat.card F)
    (hfixR : ∀ s ∈ (qPt : Subgroup (SL3 F)), ∀ r ∈ commV ((qPt : Subgroup (SL3 F)).map ρ),
      ρ s r = r)
    {w : X} (hw : w ∈ commV ((qPt : Subgroup (SL3 F)).map ρ)) {g : SL3 F}
    (hg : g ∈ (ptLevi : Subgroup (SL3 F))) : ρ g w = w := by
  set R := commV ((qPt : Subgroup (SL3 F)).map ρ) with hRdef
  have hle : (ptLevi : Subgroup (SL3 F)) ≤ stabX ρ w := by
    unfold ptLevi
    refine sup_le (sup_le (sup_le (fun x hx => ?_) (fun x hx => ?_)) ?_) ?_
    · exact hfixR x (Subgroup.mem_sup_left hx) w hw
    · exact hfixR x (Subgroup.mem_sup_right hx) w hw
    · rintro _ ⟨c, rfl⟩
      refine M16.rootElt_apply_eq_of_card_le ρ R hR
        (fun c r hr => rho_mem_commV_map ρ (fun g hg => rootElt12_conj_mem_qPt c hg) hr)
        (fun c c' hc hc' => ?_) c hw
      set t := c' * c⁻¹ with ht
      have htc : t * c = c' := by rw [ht, mul_assoc, inv_mul_cancel₀ hc, mul_one]
      refine ⟨M16.tor t 1 (mul_ne_zero hc' (inv_ne_zero hc)) one_ne_zero, ?_,
        fun r hr => rho_mem_commV_map ρ (fun g hg => tor_conj_mem_qPt _ _ _ _ hg) hr⟩
      rw [M16.tor_conj_rootElt]
      simp [htc]
    · rintro _ ⟨c, rfl⟩
      refine M16.rootElt_apply_eq_of_card_le ρ R hR
        (fun c r hr => rho_mem_commV_map ρ (fun g hg => rootElt21_conj_mem_qPt c hg) hr)
        (fun c c' hc hc' => ?_) c hw
      set t := c * c'⁻¹ with ht
      have htc : t⁻¹ * c = c' := by
        rw [ht, mul_inv, inv_inv, mul_comm c⁻¹ c', mul_assoc, inv_mul_cancel₀ hc, mul_one]
      refine ⟨M16.tor t 1 (mul_ne_zero hc (inv_ne_zero hc')) one_ne_zero, ?_,
        fun r hr => rho_mem_commV_map ρ (fun g hg => tor_conj_mem_qPt _ _ _ _ hg) hr⟩
      rw [M16.tor_conj_rootElt]
      simp [htc]
  exact hle hg

omit [Field F] in
private theorem commutator_mem_of_mem {G : Type*} [Group G] {H : Subgroup G} {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) : ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

omit [CommGroup X] in
private theorem cyc2_conj (i j : Fin 3) (c : F) :
    (cyc * cyc) * rootElt i j c * (cyc * cyc)⁻¹ = rootElt (i + 1 + 1) (j + 1 + 1) c := by
  rw [show (cyc * cyc) * rootElt i j c * (cyc * cyc)⁻¹ =
    cyc * (cyc * rootElt i j c * cyc⁻¹) * cyc⁻¹ by group, cyc_conj_rootElt, cyc_conj_rootElt]

theorem eq_one_of_lnLevi_fix [Finite F] [CharP F 2] [Finite X]
    (hR : Nat.card (commV ((qPt : Subgroup (SL3 F)).map ρ)) ≤ Nat.card F)
    (hCP : commV ρ.range ⊓ fixV ρ.range = ⊥) {v : X} (hv : v ∈ commV ρ.range)
    (hfix : ∀ g ∈ (lnLevi : Subgroup (SL3 F)), ρ g v = v) : v = 1 := by
  by_contra hv1
  set g₀ : SL3 F := cyc * cyc with hg₀
  set u := ρ g₀⁻¹ v with hu
  have hconj : ∀ x : SL3 F, g₀ * x * g₀⁻¹ ∈ (lnLevi : Subgroup (SL3 F)) → x ∈ stabX ρ u := by
    intro x hx
    have h1 := hfix _ hx
    rw [M16.rho_mul, M16.rho_mul] at h1
    change ρ x u = u
    calc ρ x u = ρ g₀⁻¹ (ρ g₀ (ρ x u)) := (M16.rho_inv_rho ρ g₀ _).symm
      _ = ρ g₀⁻¹ v := by rw [hu, h1]
  have h12 : ∀ c : F, rootElt 1 2 c ∈ stabX ρ u := fun c => hconj _ (by
    rw [hg₀, cyc2_conj]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (Subgroup.mem_sup_left (rootElt_mem_rootGroup 0 1 c))))
  have h21 : ∀ c : F, rootElt 2 1 c ∈ stabX ρ u := fun c => hconj _ (by
    rw [hg₀, cyc2_conj]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (Subgroup.mem_sup_right (rootElt_mem_rootGroup 1 0 c))))
  have h10 : ∀ c : F, rootElt 1 0 c ∈ stabX ρ u := fun c => hconj _ (by
    rw [hg₀, cyc2_conj]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (rootElt_mem_rootGroup 0 2 c)))
  have h20 : ∀ c : F, rootElt 2 0 c ∈ stabX ρ u := fun c => hconj _ (by
    rw [hg₀, cyc2_conj]
    exact Subgroup.mem_sup_right (rootElt_mem_rootGroup 1 2 c))
  have hfree : ∀ s ∈ (qPt : Subgroup (SL3 F)), ρ s u = u → s = 1 := by
    intro s hs hsu
    by_contra hs1
    obtain ⟨a, b, rfl⟩ := M16.mem_qPt_iff'.mp hs
    have hsSt : rootElt 0 1 a * rootElt 0 2 b ∈ stabX ρ u := hsu
    have hX02 : (∀ d : F, rootElt 0 2 d ∈ stabX ρ u) → ∀ d : F, rootElt 0 1 d ∈ stabX ρ u := by
      intro h d
      have h1 := commutator_mem_of_mem (Subgroup.mul_mem _
        (show rootElt 0 1 (0 : F) ∈ stabX ρ u by rw [rootElt_zero]; exact Subgroup.one_mem _)
        (h 1)) (h21 d)
      rwa [commutator_qPt_rootElt21, one_mul] at h1
    have hX01 : (∀ d : F, rootElt 0 1 d ∈ stabX ρ u) → ∀ d : F, rootElt 0 2 d ∈ stabX ρ u := by
      intro h d
      have h1 := commutator_mem_of_mem (Subgroup.mul_mem _ (h 1)
        (show rootElt 0 2 (0 : F) ∈ stabX ρ u by rw [rootElt_zero]; exact Subgroup.one_mem _))
        (h12 d)
      rwa [commutator_qPt_rootElt12, one_mul] at h1
    have hboth : (∀ d : F, rootElt 0 1 d ∈ stabX ρ u) ∧ ∀ d : F, rootElt 0 2 d ∈ stabX ρ u := by
      by_cases ha : a = 0
      · have hb : b ≠ 0 := by
          rintro rfl
          apply hs1
          rw [ha, rootElt_zero, rootElt_zero, one_mul]
        have h01 : ∀ d : F, rootElt 0 1 d ∈ stabX ρ u := by
          intro d
          have h1 := commutator_mem_of_mem hsSt (h21 (b⁻¹ * d))
          rwa [commutator_qPt_rootElt21, ← mul_assoc, mul_inv_cancel₀ hb, one_mul] at h1
        exact ⟨h01, hX01 h01⟩
      · have h02 : ∀ d : F, rootElt 0 2 d ∈ stabX ρ u := by
          intro d
          have h1 := commutator_mem_of_mem hsSt (h12 (a⁻¹ * d))
          rwa [commutator_qPt_rootElt12, ← mul_assoc, mul_inv_cancel₀ ha, one_mul] at h1
        exact ⟨hX02 h02, h02⟩
    have htop : stabX ρ u = ⊤ := by
      refine eq_top_of_rootElt_mem fun i j c hij => ?_
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hboth.1 c
      · exact hboth.2 c
      · exact h10 c
      · exact absurd rfl hij
      · exact h12 c
      · exact h20 c
      · exact h21 c
      · exact absurd rfl hij
    have hall : ∀ g : SL3 F, ρ g u = u := fun g => (mem_stabX ρ).mp (htop ▸ Subgroup.mem_top g)
    have hvu : v = u := by
      calc v = ρ g₀ u := (M16.rho_rho_inv ρ g₀ v).symm
        _ = u := hall g₀
    apply hv1
    have hvfix : v ∈ fixV ρ.range := by
      rintro _ ⟨g, rfl⟩
      rw [hvu]
      exact hall g
    have hmem : v ∈ commV ρ.range ⊓ fixV ρ.range := ⟨hv, hvfix⟩
    rwa [hCP, Subgroup.mem_bot] at hmem
  let f : ↥(qPt : Subgroup (SL3 F)) → ↥(commV ((qPt : Subgroup (SL3 F)).map ρ)) := fun s =>
    ⟨ρ s u * u⁻¹, Subgroup.subset_closure ⟨ρ s, ⟨s, s.2, rfl⟩, u, rfl⟩⟩
  have hf : Function.Injective f := by
    intro s s' h
    have h1 : ρ s u = ρ s' u := mul_right_cancel (congrArg Subtype.val h)
    have h2 : ρ ((s' : SL3 F)⁻¹ * s) u = u := by rw [M16.rho_mul, h1, M16.rho_inv_rho]
    have h3 := hfree _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ s'.2) s.2) h2
    rw [inv_mul_eq_one] at h3
    exact Subtype.ext h3.symm
  have hcard := (Nat.card_le_card_of_injective f hf).trans hR
  rw [card_qPt] at hcard
  have h2 : 1 < Nat.card F := Finite.one_lt_card
  have h3 : Nat.card F * Nat.card F ≤ Nat.card F * 1 := by rw [mul_one, ← sq]; exact hcard
  have h4 := Nat.le_of_mul_le_mul_left h3 (by omega)
  omega

end Mod

section Layer

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}

omit [Fintype F] [CharP F 2] in
theorem map_transposeInv_qPt_eq :
    (qPt : Subgroup (SL3 F)).map transposeInv = rootGroup 1 0 ⊔ rootGroup 2 0 := by
  rw [qPt, Subgroup.map_sup, M16.map_transposeInv_rootGroup, M16.map_transposeInv_rootGroup]

theorem exists_dual_layer (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Fintype.card F = 2 ^ n) {K Q U Z0 Z N T Y : Subgroup 𝔾} [Finite ↥K]
    {ψ : ↥K →* ↥(StatedSL 3 F)} (hψ : Function.Surjective ψ)
    (hU : IsSumOfNaturalModulesVia K U ⊥ ψ false 1)
    (hQ : ∀ k : ↥K, toSL3 ψ k = 1 ↔ (k : 𝔾) ∈ Q)
    (hZ : Z = U ⊔ Z0) (hZ0 : Z0 ≤ Subgroup.centralizer (K : Set 𝔾))
    (hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)) (hZN : Z ≤ N) (hNK : N ≤ K)
    (hNN : ⁅N, N⁆ ≤ Z) (hNQ : ⁅N, Q⁆ ≤ Z) (hN2 : ∀ x ∈ N, x ^ 2 ∈ Z)
    (hQT : Q ≤ T) (hTK : T ≤ K)
    (hT : (T.subgroupOf K).map (toSL3 ψ) = rootGroup 1 0 ⊔ rootGroup 2 0)
    (hZY : Z ≤ Y) (hYK : Y ≤ K) (hYZ : Z.relIndex Y ≤ Fintype.card F) (hYT : ⁅Y, T⁆ ≤ Z)
    (hNTY : ⁅N, T⁆ ≤ Y) (hNTZ : ¬ ⁅N, T⁆ ≤ Z) :
    ∃ N₀ : Subgroup 𝔾, N₀ ≤ N ∧ ¬ N₀ ≤ Z ∧ IsSumOfNaturalModulesVia K N₀ Z ψ true 1 := by
  have : Finite ↥N := Finite.of_injective _ (Subgroup.inclusion_injective hNK)
  have : Finite ↥Y := Finite.of_injective _ (Subgroup.inclusion_injective hYK)
  have hKZ0 : K ≤ Subgroup.normalizer (Z0 : Set 𝔾) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hc : ∀ y ∈ Z0, k * y * k⁻¹ = y := fun y hy => by
      rw [Subgroup.mem_centralizer_iff.mp (hZ0 hy) k hk, mul_inv_cancel_right]
    constructor
    · intro hz
      rw [hc z hz]
      exact hz
    · intro hz
      have hcomm : k * (k * z * k⁻¹) = k * z * k⁻¹ * k :=
        Subgroup.mem_centralizer_iff.mp (hZ0 hz) k hk
      have h3 : k * (k * z * k⁻¹) = k * z := by rw [hcomm]; group
      have h4 : k * z * k⁻¹ = z := mul_left_cancel h3
      exact h4 ▸ hz
  have hKZ : K ≤ Subgroup.normalizer (Z : Set 𝔾) := by
    rw [hZ]
    exact CFSG.LieType.Steinberg.le_normalizer_sup hU.1 hKZ0
  have hNc : ∀ v ∈ N, ∀ w ∈ N, ⁅v, w⁆ ∈ Z := fun v hv w hw =>
    hNN (Subgroup.commutator_mem_commutator hv hw)
  have hker : ∀ l : ↥K, ψ l = 1 → ∀ v ∈ N, v⁻¹ * ((l : 𝔾) * v * (l : 𝔾)⁻¹) ∈ Z := by
    intro l hl v hv
    have hlQ : (l : 𝔾) ∈ Q := (hQ l).mp (by simp [toSL3, hl])
    have h1 := hNQ (Subgroup.commutator_mem_commutator (N.inv_mem hv) hlQ)
    rw [commutatorElement_def, inv_inv] at h1
    simpa [mul_assoc] using h1
  obtain ⟨X, _, π, ρ, hπs, hπk, hπρ⟩ := ML3.exists_quotient_action hψ hKN hZN hKZ hNc hker
  have : Finite X := Finite.of_surjective π hπs
  have hX2 : ∀ x : X, x ^ 2 = 1 := by
    intro x
    obtain ⟨v, rfl⟩ := hπs x
    rw [← map_pow]
    refine (hπk _).mpr ?_
    rw [Subgroup.coe_pow]
    exact hN2 v v.2
  have hπeq : ∀ v v' : ↥N, π v = π v' ↔ (v : 𝔾)⁻¹ * v' ∈ Z := fun v v' => by
    have := hπk (v⁻¹ * v')
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    simpa using this
  set ρ' : SL3 F →* MulAut X := ρ.comp transposeInv with hρ'def
  have hρ' : ∀ g : SL3 F, ρ' (transposeInv g) = ρ g := fun g => by
    rw [hρ'def, MonoidHom.comp_apply, transposeInv_transposeInv]
  set ρK : ↥K →* MulAut X := ρ.comp (toSL3 ψ) with hρKdef
  have hρK : ∀ (k : ↥K) (v : ↥N), ρK k (π v) = π (conjOn hKN k v) := hπρ
  have hqPt : (qPt : Subgroup (SL3 F)).map ρ' = (T.subgroupOf K).map ρK := by
    rw [hρ'def, hρKdef, ← Subgroup.map_map, ← Subgroup.map_map, map_transposeInv_qPt_eq, hT]
  set R := commV ((qPt : Subgroup (SL3 F)).map ρ') with hRdef
  have hpreR : S4A.F.pre π R = ⁅N, T⁆ ⊔ Z := by
    rw [hRdef, hqPt]
    exact S4A.F.pre_commV hρK hπk hZN hπs hTK
  have hcomm : Nat.card R ≤ Nat.card F := by
    rw [← S4A.F.card_pre hπk hZN hπs R, hpreR, Nat.card_eq_fintype_card]
    refine le_trans (Subgroup.relIndex_le_of_le_right (sup_le hNTY hZY) ?_) hYZ
    exact Subgroup.index_ne_zero_of_finite
  have hfixR : ∀ s ∈ (qPt : Subgroup (SL3 F)), ∀ r ∈ R, ρ' s r = r := by
    intro s hs r hr
    obtain ⟨v, rfl⟩ := hπs r
    have hvY : (v : 𝔾) ∈ Y := by
      have h1 : (v : 𝔾) ∈ S4A.F.pre π R := S4A.F.mem_pre.mpr ⟨v.2, hr⟩
      rw [hpreR] at h1
      exact sup_le hNTY hZY h1
    have hs' : transposeInv s ∈ (T.subgroupOf K).map (toSL3 ψ) := by
      rw [hT, ← map_transposeInv_qPt_eq]
      exact ⟨s, hs, rfl⟩
    obtain ⟨t, htT, ht⟩ := hs'
    have e : ρ' s = ρ (toSL3 ψ t) := by rw [ht]; rfl
    rw [e, hπρ, eq_comm, hπeq]
    have h1 := hYT (Subgroup.commutator_mem_commutator (Y.inv_mem hvY)
      (Subgroup.mem_subgroupOf.mp htT))
    rw [commutatorElement_def, inv_inv] at h1
    simpa [coe_conjOn_apply, mul_assoc] using h1
  obtain ⟨n₁, hn₁, t₁, ht₁, hnt⟩ : ∃ n₁ ∈ N, ∃ t₁ ∈ T, ⁅n₁, t₁⁆ ∉ Z := by
    by_contra h
    push Not at h
    exact hNTZ (Subgroup.commutator_le.mpr h)
  set w := ⁅n₁, t₁⁆ with hwdef
  have hwN : w ∈ N := S4A.F.commutatorElement_mem_V hKN hn₁ (hTK ht₁)
  have hwR : π ⟨w, hwN⟩ ∈ R := by
    have h1 : w ∈ S4A.F.pre π R := by
      rw [hpreR]
      exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hn₁ ht₁)
    obtain ⟨_, h2⟩ := S4A.F.mem_pre.mp h1
    exact h2
  have hw1 : π ⟨w, hwN⟩ ≠ 1 := fun h => hnt ((hπk _).mp h)
  have hnt' : ∃ g x, ρ' g x ≠ x := by
    by_contra h
    push Not at h
    apply hw1
    have hle : R ≤ ⊥ := by
      rw [hRdef, commV, Subgroup.closure_le]
      rintro _ ⟨_, ⟨g, -, rfl⟩, x, rfl⟩
      rw [h g x, mul_inv_cancel]
      exact Subgroup.one_mem _
    exact Subgroup.mem_bot.mp (hle hwR)
  have hB : (qPt : Subgroup (SL3 F)) ≠ ⊥ := by
    intro h
    have h1 : rootElt 0 1 (1 : F) ∈ (qPt : Subgroup (SL3 F)) :=
      Subgroup.mem_sup_left (rootElt_mem_rootGroup 0 1 1)
    rw [h, Subgroup.mem_bot, rootElt_eq_one_iff (by decide)] at h1
    exact one_ne_zero h1
  have hB2 : ∀ b ∈ (qPt : Subgroup (SL3 F)), b ^ 2 = 1 := fun b hb => by
    rw [sq]
    exact ML3.qPt_elemAb.2 b hb
  have hqB : Nat.card F ≤ Nat.card (qPt : Subgroup (SL3 F)) := by
    rw [card_qPt]
    exact Nat.le_self_pow two_ne_zero _
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨hCP, -, -⟩ := S4A.F.dualOff_decomp h14 hSQ hsq hF' hX2 ρ' hnt' hB hB2
    ML3.qPt_elemAb.1 hqB hcomm
  set N₀ := Subgroup.closure {u | ∃ l : ↥K, (l : 𝔾) * w * (l : 𝔾)⁻¹ = u} ⊔ Z with hN₀def
  have hwN₀ : w ∈ N₀ := Subgroup.mem_sup_left (Subgroup.subset_closure ⟨1, by simp⟩)
  have hN₀N : N₀ ≤ N := by
    refine sup_le ?_ hZN
    rw [Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hKN l.2) w).mp hwN
  have hKN₀ : K ≤ Subgroup.normalizer (N₀ : Set 𝔾) := by
    refine CFSG.LieType.Steinberg.le_normalizer_sup ?_ hKZ
    refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun k hk => ?_
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    exact ⟨⟨k, hk⟩ * l, by simp [mul_assoc]⟩
  have hwC : π ⟨w, hwN⟩ ∈ commV ρ'.range :=
    G6.commV_mono (Subgroup.map_le_range ρ' _) hwR
  have hN₀C : N₀ ≤ S4A.F.pre π (commV ρ'.range) := by
    refine sup_le ?_ (S4A.F.le_pre hπk hZN _)
    rw [Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    have hlw : (l : 𝔾) * w * (l : 𝔾)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hKN l.2) w).mp hwN
    refine S4A.F.mem_pre.mpr ⟨hlw, ?_⟩
    have e : π ⟨(l : 𝔾) * w * (l : 𝔾)⁻¹, hlw⟩ = ρ' (transposeInv (toSL3 ψ l)) (π ⟨w, hwN⟩) := by
      rw [hρ', hπρ]
      rfl
    rw [e]
    exact commV_inv ρ' _ hwC
  have hmemT : ∀ l : ↥K, transposeInv (toSL3 ψ l) ∈ rootGroup 0 1 → (l : 𝔾) ∈ T := by
    intro l hl
    have h1 : toSL3 ψ l ∈ (T.subgroupOf K).map (toSL3 ψ) := by
      rw [hT, ← transposeInv_transposeInv (toSL3 ψ l)]
      refine Subgroup.mem_sup_left ?_
      rw [← M16.map_transposeInv_rootGroup]
      exact ⟨_, hl, rfl⟩
    obtain ⟨t, htT, ht⟩ := h1
    have h2 : (((t⁻¹ * l : ↥K)) : 𝔾) ∈ Q := (hQ _).mp (by rw [map_mul, map_inv, ht,
      inv_mul_cancel])
    have h3 : (l : 𝔾) = t * ((t⁻¹ * l : ↥K) : 𝔾) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [h3]
    exact T.mul_mem (Subgroup.mem_subgroupOf.mp htT) (hQT h2)
  refine ⟨N₀, hN₀N, fun h => hnt (h hwN₀), ?_⟩
  refine isSumOfNaturalModulesVia_dual_of_vecStab hψ hKN₀ le_sup_right hKZ
    (fun v hv w hw => hNc v (hN₀N hv) w (hN₀N hw)) (fun l hl v hv => hker l hl v (hN₀N hv))
    hwN₀ hnt ?_ ?_ ?_ rfl
  ·
    intro l hl
    have h1 := ptLevi_fix_of_card ρ' hcomm hfixR hwR hl
    rw [hρ', hπρ, eq_comm, hπeq] at h1
    simpa [coe_conjOn_apply] using h1
  ·
    intro l l' hl hl' v hv
    have hlT := hmemT l hl
    have hl'T := hmemT l' hl'
    have hy : (l : 𝔾) * v * (l : 𝔾)⁻¹ * v⁻¹ ∈ Y := by
      have h1 : ⁅(l : 𝔾), v⁆ ∈ ⁅N, T⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hlT (hN₀N hv)
      rw [commutatorElement_def] at h1
      exact hNTY h1
    have h2 := hYT (Subgroup.commutator_mem_commutator (Y.inv_mem hy) hl'T)
    rw [commutatorElement_def, inv_inv] at h2
    simpa [mul_assoc] using h2
  ·
    intro v hv hfixv
    obtain ⟨hvN, hvC⟩ := S4A.F.mem_pre.mp (hN₀C hv)
    have hfix' : ∀ g ∈ (lnLevi : Subgroup (SL3 F)), ρ' g (π ⟨v, hvN⟩) = π ⟨v, hvN⟩ := by
      intro g hg
      obtain ⟨l, hl⟩ := toSL3_surjective hψ (transposeInv g)
      have h1 := hfixv l (by rw [hl, transposeInv_transposeInv]; exact hg)
      have e : ρ' g = ρ (toSL3 ψ l) := by rw [hl]; rfl
      rw [e, hπρ, eq_comm, hπeq]
      simpa [coe_conjOn_apply] using h1
    exact (hπk _).mp (eq_one_of_lnLevi_fix ρ' hcomm hCP hvC hfix')

end Layer

end CFSG.Quasithin.MS93.S46
