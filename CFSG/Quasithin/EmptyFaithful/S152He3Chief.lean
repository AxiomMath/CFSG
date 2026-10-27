module

public import CFSG.Quasithin.Vol2.Ch3zStep
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X1
open scoped commutatorElement

section Abstract

variable {Ω Γ : Type*} [Group Ω] [Group Γ]

theorem map_eq_one_of_normal_two152 {X : Subgroup Γ} {X' : Subgroup Ω} (ψ : ↥X →* Ω)
    (hψ : ∀ g, ψ g ∈ X') (hsurj : ∀ x ∈ X', ∃ g, ψ g = x)
    (hO2 : ∀ Q : Subgroup Ω, Q ≤ X' → (Q.subgroupOf X').Normal → IsPGroup 2 Q → Q = ⊥)
    {P : Subgroup Γ} (hPn : ∀ g ∈ X, ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hP2 : IsPGroup 2 P)
    {g : ↥X} (hg : (g : Γ) ∈ P) : ψ g = 1 := by
  set Q : Subgroup Ω := (P.subgroupOf X).map ψ with hQ
  have hQX : Q ≤ X' := by
    rintro _ ⟨p, -, rfl⟩
    exact hψ p
  have hQn : (Q.subgroupOf X').Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQX]
    rintro _ k ⟨p, hp, rfl⟩ hk
    obtain ⟨h, rfl⟩ := hsurj k hk
    refine ⟨h * p * h⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact Subgroup.mem_subgroupOf.mpr (by
      simpa using hPn h h.2 p (Subgroup.mem_subgroupOf.mp hp))
  have hQ2 : IsPGroup 2 Q := by
    rintro ⟨_, ⟨p, hp, rfl⟩⟩
    obtain ⟨k, hk⟩ := hP2 ⟨(p : Γ), hp⟩
    refine ⟨k, Subtype.ext ?_⟩
    have : p ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    simp [← map_pow, this]
  have hbot := hO2 Q hQX hQn hQ2
  have : ψ g ∈ Q := ⟨g, hg, rfl⟩
  rw [hbot] at this
  exact Subgroup.mem_bot.mp this

theorem eq_bot_of_two_pow152 {X' K' : Subgroup Ω}
    (hO2 : ∀ Q : Subgroup Ω, Q ≤ X' → (Q.subgroupOf X').Normal → IsPGroup 2 Q → Q = ⊥)
    (h2pow : ∀ x ∈ X', ∃ m : ℕ, x ^ 2 ^ m ∈ K') (hK : ∀ k ∈ K', k = 1) : X' = ⊥ := by
  refine hO2 X' le_rfl ?_ ?_
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · intro x
    obtain ⟨m, hm⟩ := h2pow x x.2
    exact ⟨m, Subtype.ext (hK _ hm)⟩

theorem eq_one_of_commute_of_two_pow152 {X' K' : Subgroup Ω}
    (hO2 : ∀ Q : Subgroup Ω, Q ≤ X' → (Q.subgroupOf X').Normal → IsPGroup 2 Q → Q = ⊥)
    (hn : ∀ x ∈ X', ∀ k ∈ K', x * k * x⁻¹ ∈ K')
    (h2pow : ∀ x ∈ X', ∃ m : ℕ, x ^ 2 ^ m ∈ K')
    (hZ : ∀ k ∈ K', (∀ k' ∈ K', k * k' = k' * k) → k = 1) :
    ∀ x ∈ X', (∀ k ∈ K', x * k = k * x) → x = 1 := by
  set D : Subgroup Ω := X' ⊓ Subgroup.centralizer (K' : Set Ω) with hD
  have hDX : D ≤ X' := inf_le_left
  have hDn : (D.subgroupOf X').Normal := by
    rw [Subgroup.normal_subgroupOf_iff hDX]
    intro d x hd hx
    refine ⟨X'.mul_mem (X'.mul_mem hx hd.1) (X'.inv_mem hx), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro k hk
    have h1 := hn x⁻¹ (X'.inv_mem hx) k hk
    have h2 := Subgroup.mem_centralizer_iff.mp hd.2 _ h1
    rw [inv_inv] at h2
    calc k * (x * d * x⁻¹) = x * ((x⁻¹ * k * x) * d) * x⁻¹ := by group
      _ = x * (d * (x⁻¹ * k * x)) * x⁻¹ := by rw [h2]
      _ = (x * d * x⁻¹) * k := by group
  have hD2 : IsPGroup 2 D := by
    intro d
    obtain ⟨m, hm⟩ := h2pow d (hDX d.2)
    have hdm : (d : Ω) ^ 2 ^ m ∈ D := D.pow_mem d.2 _
    have h1 : (d : Ω) ^ 2 ^ m = 1 :=
      hZ _ hm fun k' hk' => (Subgroup.mem_centralizer_iff.mp hdm.2 k' hk').symm
    exact ⟨m, Subtype.ext h1⟩
  have hbot := hO2 D hDX hDn hD2
  intro x hx hc
  have : x ∈ D := ⟨hx, Subgroup.mem_centralizer_iff.mpr fun k hk => (hc k hk).symm⟩
  rw [hbot] at this
  exact Subgroup.mem_bot.mp this

end Abstract

section Chief

variable {Γ : Type} [Group Γ]

theorem isElemAbelian_chiefMod [Finite Γ] {X Q L N : Subgroup Γ} (hstep : IsChiefStep X Q L N)
    (hQX : Q ≤ X) (hQ2 : IsPGroup 2 Q) : IsElemAbelian 2 (Ch3z.chiefMod L N) := by
  classical
  have hXL : X ≤ Subgroup.normalizer (L : Set Γ) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hNQ : N ≤ Q := hstep.1.1
  have hNL : N ≤ Subgroup.normalizer (L : Set Γ) := (hNQ.trans hQX).trans hXL
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 ↥(Ch3z.chiefMod L N) := by
    intro m
    obtain ⟨n, rfl⟩ := Ch3z.chiefIota_surjective hNL m
    obtain ⟨k, hk⟩ := hQ2 ⟨(n : Γ), hNQ n.2⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : n ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hnt : Nontrivial ↥(Ch3z.chiefMod L N) := by
    obtain ⟨n, hnN, hnL⟩ := Set.exists_of_ssubset (SetLike.coe_ssubset_coe.mpr hstep.2.2.1)
    refine nontrivial_of_ne (Ch3z.chiefIota hNL ⟨n, hnN⟩) 1 ?_
    intro h
    exact hnL ((Ch3z.chiefIota_eq_one_iff hNL ⟨n, hnN⟩).1 h)
  have hZinv : ∀ x ∈ Ch3z.chiefAut X L N, ∀ w ∈ Subgroup.center ↥(Ch3z.chiefMod L N),
      x w ∈ Subgroup.center ↥(Ch3z.chiefMod L N) := by
    intro x _ w hw
    rw [Subgroup.mem_center_iff] at hw ⊢
    intro g
    have h2 := congrArg x (hw (x.symm g))
    simpa [map_mul] using h2
  have hZtop : Subgroup.center ↥(Ch3z.chiefMod L N) = ⊤ := by
    rcases Ch3z.chiefMod_irr hstep hQX _ hZinv with h | h
    · exfalso
      have := hpg.center_nontrivial
      obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥(Ch3z.chiefMod L N)))
      apply hz
      have hz2 : (z : ↥(Ch3z.chiefMod L N)) ∈ (⊥ : Subgroup ↥(Ch3z.chiefMod L N)) := by
        rw [← h]
        exact z.2
      exact Subtype.ext (Subgroup.mem_bot.mp hz2)
    · exact h
  have hcomm : ∀ a b : ↥(Ch3z.chiefMod L N), a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.center ↥(Ch3z.chiefMod L N) := by
      rw [hZtop]
      exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm
  let S : Subgroup ↥(Ch3z.chiefMod L N) :=
    { carrier := {m | m * m = 1}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        have ha' : a * a = 1 := ha
        have hb' : b * b = 1 := hb
        show a * b * (a * b) = 1
        calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
          _ = a * (a * b) * b := by rw [← hcomm a b]
          _ = (a * a) * (b * b) := by simp only [mul_assoc]
          _ = 1 := by rw [ha', hb', one_mul]
      inv_mem' := fun {a} ha => by
        have ha' : a * a = 1 := ha
        show a⁻¹ * a⁻¹ = 1
        rw [← mul_inv_rev, ha', inv_one] }
  have hSinv : ∀ x ∈ Ch3z.chiefAut X L N, ∀ w ∈ S, x w ∈ S := by
    intro x _ w hw
    have hw' : w * w = 1 := hw
    show x w * x w = 1
    rw [← map_mul, hw', map_one]
  have hS : ∀ m : ↥(Ch3z.chiefMod L N), m * m = 1 := by
    rcases Ch3z.chiefMod_irr hstep hQX S hSinv with h | h
    · exfalso
      have h2 : 2 ∣ Nat.card ↥(Ch3z.chiefMod L N) := by
        rcases hpg.card_eq_or_dvd with h1 | h1
        · exact absurd h1 (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne'
        · exact h1
      obtain ⟨m, hm⟩ := exists_prime_orderOf_dvd_card' 2 h2
      have hm1 : m ∈ S := by
        show m * m = 1
        rw [← sq]
        simpa [hm] using pow_orderOf_eq_one m
      rw [h, Subgroup.mem_bot] at hm1
      rw [hm1, orderOf_one] at hm
      omega
    · intro m
      have : m ∈ S := by rw [h]; exact Subgroup.mem_top m
      exact this
  rw [F7.isElemAbelian_iff]
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · exact congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
  · have := congrArg Subtype.val (hS ⟨x, hx⟩)
    simpa [sq] using this

variable {X L N : Subgroup Γ}

theorem commutator_mem_of_chiefPsi_eq_one (hXL : X ≤ Subgroup.normalizer (L : Set Γ))
    (hXN : X ≤ Subgroup.normalizer (N : Set Γ)) (hNL : N ≤ Subgroup.normalizer (L : Set Γ))
    {e : ↥X} (he1 : Ch3z.chiefPsi hXL hXN e = 1) {n : Γ} (hn : n ∈ N) : ⁅n, (e : Γ)⁆ ∈ L := by
  have hen : (e : Γ) * n * (e : Γ)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hXN e.2) n).mp hn
  have h1 := Ch3z.chiefPsi_iota hXL hXN hNL e ⟨n, hn⟩ hen
  rw [he1, MulAut.one_apply] at h1
  have h2 : Ch3z.chiefIota hNL ⟨(e : Γ) * n * (e : Γ)⁻¹ * n⁻¹, N.mul_mem hen (N.inv_mem hn)⟩ = 1 := by
    have : (⟨(e : Γ) * n * (e : Γ)⁻¹ * n⁻¹, N.mul_mem hen (N.inv_mem hn)⟩ : ↥N) =
        ⟨(e : Γ) * n * (e : Γ)⁻¹, hen⟩ * ⟨n, hn⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, ← h1, mul_inv_cancel]
  have h3 := (Ch3z.chiefIota_eq_one_iff hNL _).1 h2
  have : ⁅n, (e : Γ)⁆ = ((e : Γ) * n * (e : Γ)⁻¹ * n⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [this]
  exact L.inv_mem h3

theorem index_fixV_zpowers_chiefPsi_lt [Finite Γ] {E : Subgroup Γ}
    (hXL : X ≤ Subgroup.normalizer (L : Set Γ)) (hXN : X ≤ Subgroup.normalizer (N : Set Γ))
    (hNL : N ≤ Subgroup.normalizer (L : Set Γ)) (hLN : L ≤ N) (hEX : E ≤ X)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) {e : ↥X} (he : (e : Γ) ∈ E)
    (hlt : Nat.card ↥(⁅N, E⁆ ⊔ L) < 8 * Nat.card L) :
    (@fixV ↥(Ch3z.chiefMod L N) (Ch3z.chiefCG hE)
      (Subgroup.zpowers (Ch3z.chiefPsi hXL hXN e))).index < 8 := by
  classical
  let _ : CommGroup ↥(Ch3z.chiefMod L N) := Ch3z.chiefCG hE
  set t : MulAut ↥(Ch3z.chiefMod L N) := Ch3z.chiefPsi hXL hXN e with ht
  let f : ↥(Ch3z.chiefMod L N) →* ↥(Ch3z.chiefMod L N) :=
    MonoidHom.mk' (fun w => t w * w⁻¹) (fun a b => by
      rw [map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _)
  have hker : f.ker = fixV (Subgroup.zpowers t) := by
    ext w
    rw [MonoidHom.mem_ker, mem_fixV_zpowers]
    show t w * w⁻¹ = 1 ↔ t w = w
    exact mul_inv_eq_one
  have hidx : (fixV (Subgroup.zpowers t)).index = Nat.card f.range := by
    rw [← hker]
    exact Subgroup.index_ker f
  set Cm : Subgroup Γ := ⁅N, E⁆ ⊔ L with hCm
  have hCmN : Cm ≤ N := by
    refine sup_le (Subgroup.commutator_le.mpr fun n hn e' he' => ?_) hLN
    have h1 : (e' : Γ) * n⁻¹ * (e' : Γ)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hXN (hEX he')) n⁻¹).mp (N.inv_mem hn)
    have : ⁅n, e'⁆ = n * (e' * n⁻¹ * e'⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact N.mul_mem hn h1
  set Cbar : Subgroup ↥(Ch3z.chiefMod L N) :=
    (Cm.subgroupOf N).map (Ch3z.chiefIota hNL) with hCbar
  have hrange : f.range ≤ Cbar := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨n, rfl⟩ := Ch3z.chiefIota_surjective hNL w
    have hen : (e : Γ) * n * (e : Γ)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hXN e.2) n).mp n.2
    have h1 := Ch3z.chiefPsi_iota hXL hXN hNL e n hen
    refine ⟨⟨(e : Γ) * n * (e : Γ)⁻¹ * (n : Γ)⁻¹, N.mul_mem hen (N.inv_mem n.2)⟩, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      have hc : (e : Γ) * n * (e : Γ)⁻¹ * (n : Γ)⁻¹ = ⁅(n : Γ), (e : Γ)⁆⁻¹ := by
        rw [commutatorElement_inv, commutatorElement_def]
      show (e : Γ) * n * (e : Γ)⁻¹ * (n : Γ)⁻¹ ∈ Cm
      rw [hc]
      exact Cm.inv_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator n.2 he))
    · show Ch3z.chiefIota hNL _ = f (Ch3z.chiefIota hNL n)
      have : (⟨(e : Γ) * n * (e : Γ)⁻¹ * (n : Γ)⁻¹, N.mul_mem hen (N.inv_mem n.2)⟩ : ↥N) =
          ⟨(e : Γ) * n * (e : Γ)⁻¹, hen⟩ * n⁻¹ := rfl
      rw [this, map_mul, map_inv]
      show _ = t (Ch3z.chiefIota hNL n) * (Ch3z.chiefIota hNL n)⁻¹
      rw [ht, h1]
  have hcard : Nat.card Cbar * Nat.card L = Nat.card Cm := by
    set C' : Subgroup ↥N := Cm.subgroupOf N with hC'
    set g : ↥C' →* ↥(Ch3z.chiefMod L N) := (Ch3z.chiefIota hNL).comp C'.subtype with hg
    have h1 := Subgroup.index_mul_card g.ker
    rw [Subgroup.index_ker] at h1
    have hrange' : g.range = Cbar := by
      rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
    have hker' : Nat.card g.ker = Nat.card L := by
      refine Nat.card_eq_of_bijective
        (fun c => ⟨(((c : ↥C') : ↥N) : Γ), (Ch3z.chiefIota_eq_one_iff hNL _).1 c.2⟩) ⟨?_, ?_⟩
      · intro c d hcd
        have := congrArg Subtype.val hcd
        exact Subtype.ext (Subtype.ext (Subtype.ext this))
      · rintro ⟨l, hl⟩
        refine ⟨⟨⟨⟨l, hLN hl⟩, ?_⟩, ?_⟩, rfl⟩
        · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hl)
        · exact (Ch3z.chiefIota_eq_one_iff hNL _).2 hl
    have hC'card : Nat.card C' = Nat.card Cm :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCmN).toEquiv
    rw [hrange', hker', hC'card] at h1
    exact h1
  rw [hidx]
  have h2 : Nat.card f.range ≤ Nat.card Cbar := Subgroup.card_le_of_le hrange
  have h3 : Nat.card Cbar < 8 := by
    have : Nat.card Cbar * Nat.card L < 8 * Nat.card L := hcard ▸ hlt
    exact Nat.lt_of_mul_lt_mul_right this
  omega

end Chief

end CFSG.Quasithin
