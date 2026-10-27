module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

namespace LRed5

open Equiv Equiv.Perm

@[expose] def c3 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def d3 : Equiv.Perm (Fin 6) := (Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 3 4 * Equiv.swap 4 5)

theorem c3_mem : c3 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem d3_mem : d3 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem classify3 : ∀ γ : Equiv.Perm (Fin 6), Equiv.Perm.sign γ = 1 → γ ≠ 1 → γ ^ 3 = 1 →
    (∃ δ : Equiv.Perm (Fin 6), Equiv.Perm.sign δ = 1 ∧ γ = δ * c3 * δ⁻¹) ∨
    (∃ δ : Equiv.Perm (Fin 6), Equiv.Perm.sign δ = 1 ∧ γ = δ * d3 * δ⁻¹) := by
  decide +kernel


section Alt

variable {V : Type} [CommGroup V]

@[expose] def HasFixSec (U Z : Subgroup V) (g : MulAut V) : Prop :=
  ∃ u ∈ U, u ∉ Z ∧ g u * u⁻¹ ∈ Z

theorem HasFixSec.conj {U Z : Subgroup V} {s : MulAut V} (hU : ∀ u ∈ U, s u ∈ U)
    (hZ : ∀ z ∈ Z, s z ∈ Z) (hZ' : ∀ z ∈ Z, s⁻¹ z ∈ Z) {g : MulAut V} (h : HasFixSec U Z g) :
    HasFixSec U Z (s * g * s⁻¹) := by
  obtain ⟨u, hu, huZ, hg⟩ := h
  refine ⟨s u, hU u hu, fun hsu => huZ ?_, ?_⟩
  · simpa using hZ' _ hsu
  · have : (s * g * s⁻¹) (s u) * (s u)⁻¹ = s (g u * u⁻¹) := by
      simp [MulAut.mul_apply, map_mul, map_inv]
    rw [this]
    exact hZ _ hg

theorem hasFixSec_conj_iff {U Z : Subgroup V} {s : MulAut V} (hU : ∀ u ∈ U, s u ∈ U)
    (hU' : ∀ u ∈ U, s⁻¹ u ∈ U) (hZ : ∀ z ∈ Z, s z ∈ Z) (hZ' : ∀ z ∈ Z, s⁻¹ z ∈ Z) {g : MulAut V} :
    HasFixSec U Z (s * g * s⁻¹) ↔ HasFixSec U Z g := by
  refine ⟨fun h => ?_, HasFixSec.conj hU hZ hZ'⟩
  have := HasFixSec.conj (s := s⁻¹) hU' hZ' (by simpa using hZ) h
  simpa [mul_assoc] using this

theorem allOnes_mul_self : G6.allOnes 6 * G6.allOnes 6 = 1 := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  apply Multiplicative.toAdd.injective
  funext i
  simp [G6.allOnes, h11]

theorem mem_ker6 {m : G6.PermMod 6} :
    m ∈ (Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6) ↔ m = 1 ∨ m = G6.allOnes 6 := by
  have hsq : G6.allOnes 6 * G6.allOnes 6 = 1 := allOnes_mul_self
  have hmem : G6.allOnes 6 ∈ G6.coreMod 6 := by
    rw [G6.mem_coreMod]
    decide
  have hinv : (G6.allOnes 6)⁻¹ = G6.allOnes 6 := inv_eq_of_mul_eq_one_right hsq
  have hz : ∀ k : ℤ, G6.allOnes 6 ^ k = 1 ∨ G6.allOnes 6 ^ k = G6.allOnes 6 := by
    intro k
    induction k using Int.induction_on with
    | zero => left; simp
    | succ i ih =>
      rw [zpow_add_one]
      rcases ih with h | h
      · right; rw [h, one_mul]
      · left; rw [h, hsq]
    | pred i ih =>
      have e : G6.allOnes 6 ^ (-(i : ℤ) - 1) = G6.allOnes 6 ^ (-(i : ℤ)) * G6.allOnes 6 := by
        rw [zpow_sub_one]
        exact congrArg (fun x => G6.allOnes 6 ^ (-(i : ℤ)) * x) hinv
      rw [e]
      rcases ih with h | h
      · right; rw [h, one_mul]
      · left; rw [h, hsq]
  constructor
  · rintro ⟨hm, -⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
    exact hz k
  · rintro (rfl | rfl)
    · exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    · exact ⟨Subgroup.mem_zpowers _, hmem⟩

@[expose] def altFix' (γ : Equiv.Perm (Fin 6)) : Prop :=
  ∃ m : G6.PermMod 6, (∑ i, Multiplicative.toAdd m i = 0) ∧ ¬ (m = 1 ∨ m = G6.allOnes 6) ∧
    (G6.permAct 6 γ m * m⁻¹ = 1 ∨ G6.permAct 6 γ m * m⁻¹ = G6.allOnes 6)

theorem altFix'_c3 : altFix' c3 := by
  unfold altFix'
  decide +kernel

theorem not_altFix'_d3 : ¬ altFix' d3 := by
  unfold altFix'
  decide +kernel

theorem aux_quot {G : Type*} [CommGroup G] (a x m : G) (ha : a * a = 1) :
    (x⁻¹ * m = 1 ∨ x⁻¹ * m = a) ↔ (x * m⁻¹ = 1 ∨ x * m⁻¹ = a) := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have key : ∀ b : G, x⁻¹ * m = b ↔ x * m⁻¹ = b⁻¹ := by
    intro b
    constructor
    · intro h
      rw [← h, mul_inv_rev, inv_inv, mul_comm]
    · intro h
      have := congrArg (fun y => y⁻¹) h
      simp only [mul_inv_rev, inv_inv] at this
      rw [mul_comm] at this
      simpa using this
  rw [key 1, key a, hinv, inv_one]

theorem mk_eq_iff6 (x m : ↥(G6.coreMod 6)) :
    (QuotientGroup.mk x :
        ↥(G6.coreMod 6) ⧸ (Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6)) =
      QuotientGroup.mk m ↔
      ((x : G6.PermMod 6) * (m : G6.PermMod 6)⁻¹ = 1 ∨
        (x : G6.PermMod 6) * (m : G6.PermMod 6)⁻¹ = G6.allOnes 6) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_ker6]
  exact aux_quot (G6.allOnes 6) (x : G6.PermMod 6) (m : G6.PermMod 6) allOnes_mul_self

theorem hasFixSec_iff {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(alternatingGroup (Fin 6)) →* ↥L} (hπ : (FFModel.altDn 6).RealizesVia L U Z π)
    (γ : ↥(alternatingGroup (Fin 6))) :
    HasFixSec U Z ((π γ : ↥L) : MulAut V) ↔ altFix' (γ : Equiv.Perm (Fin 6)) := by
  obtain ⟨-, -, -, hLU, hLZ, hsec, -, β, hβs, hβk, hβe⟩ := hπ
  constructor
  · rintro ⟨u, hu, huZ, hg⟩
    have hu' : ((π γ : ↥L) : MulAut V) u ∈ U := hLU (π γ) u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, hu⟩)
    have hβ1 : β ⟨u, hu⟩ ≠ 1 := fun h => huZ ((hβk ⟨u, hu⟩).1 h)
    have hm' : (FFModel.altDn 6).act γ (m : (FFModel.altDn 6).Amb) ∈ (FFModel.altDn 6).sec :=
      hsec γ m m.2
    have h1 : β ⟨((π γ : ↥L) : MulAut V) u, hu'⟩ =
        QuotientGroup.mk ⟨(FFModel.altDn 6).act γ (m : (FFModel.altDn 6).Amb), hm'⟩ :=
      hβe γ ⟨u, hu⟩ m hu' hm' hm.symm
    have h2 : β ⟨((π γ : ↥L) : MulAut V) u, hu'⟩ = β ⟨u, hu⟩ := by
      have h3 : β (⟨((π γ : ↥L) : MulAut V) u, hu'⟩ * ⟨u, hu⟩⁻¹) = 1 :=
        (hβk _).2 (by simpa using hg)
      rw [map_mul, map_inv, mul_inv_eq_one] at h3
      exact h3
    rw [h1, ← hm] at h2
    let m₀ : ↥(G6.coreMod 6) := m
    refine ⟨(m₀ : G6.PermMod 6), G6.mem_coreMod.1 m₀.2, fun h => hβ1 ?_, ?_⟩
    · rw [← hm]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (mem_ker6.2 h))
    · exact (mk_eq_iff6 ⟨_, hm'⟩ m₀).1 h2
  · rintro ⟨m, hsum, hker, hfix⟩
    let m' : ↥(FFModel.altDn 6).sec := ⟨m, G6.mem_coreMod.2 hsum⟩
    obtain ⟨u₁, hu₁⟩ := hβs (QuotientGroup.mk m')
    have hu₁' : ((π γ : ↥L) : MulAut V) (u₁ : V) ∈ U := hLU (π γ) _ u₁.2
    have hm' : (FFModel.altDn 6).act γ (m' : (FFModel.altDn 6).Amb) ∈ (FFModel.altDn 6).sec :=
      hsec γ m' m'.2
    have h1 : β ⟨((π γ : ↥L) : MulAut V) (u₁ : V), hu₁'⟩ =
        QuotientGroup.mk ⟨(FFModel.altDn 6).act γ (m' : (FFModel.altDn 6).Amb), hm'⟩ :=
      hβe γ u₁ m' hu₁' hm' hu₁
    have h2 : (QuotientGroup.mk ⟨(FFModel.altDn 6).act γ (m' : (FFModel.altDn 6).Amb), hm'⟩ :
        ↥(FFModel.altDn 6).sec ⧸ (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec) =
        QuotientGroup.mk m' := (mk_eq_iff6 ⟨_, hm'⟩ m').2 hfix
    refine ⟨(u₁ : V), u₁.2, fun hZ => hker ?_, ?_⟩
    · have : β u₁ = 1 := (hβk u₁).2 hZ
      rw [hu₁] at this
      have := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff m').1 this)
      exact mem_ker6.1 this
    · have h3 : β (⟨((π γ : ↥L) : MulAut V) (u₁ : V), hu₁'⟩ * u₁⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, h2, ← hu₁, mul_inv_cancel]
      exact by simpa using (hβk _).1 h3

@[expose] def ConjTo (c : Equiv.Perm (Fin 6)) (γ : ↥(alternatingGroup (Fin 6))) : Prop :=
  ∃ δ : ↥(alternatingGroup (Fin 6)),
    (γ : Equiv.Perm (Fin 6)) = (δ : Equiv.Perm (Fin 6)) * c * (δ : Equiv.Perm (Fin 6))⁻¹

theorem classify3' (γ : ↥(alternatingGroup (Fin 6))) (h1 : γ ≠ 1) (h3 : γ ^ 3 = 1) :
    ConjTo c3 γ ∨ ConjTo d3 γ := by
  have hs : Equiv.Perm.sign (γ : Equiv.Perm (Fin 6)) = 1 := Equiv.Perm.mem_alternatingGroup.1 γ.2
  have h1' : (γ : Equiv.Perm (Fin 6)) ≠ 1 := fun h => h1 (Subtype.ext h)
  have h3' : (γ : Equiv.Perm (Fin 6)) ^ 3 = 1 := by simpa using congrArg Subtype.val h3
  rcases classify3 γ hs h1' h3' with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
  · exact Or.inl ⟨⟨δ, Equiv.Perm.mem_alternatingGroup.2 hδ⟩, h⟩
  · exact Or.inr ⟨⟨δ, Equiv.Perm.mem_alternatingGroup.2 hδ⟩, h⟩

theorem hasFixSec_conj_of_mem {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (hLU : ∀ h : ↥L, ∀ u ∈ U, (h : MulAut V) u ∈ U) (hLZ : ∀ h : ↥L, ∀ z ∈ Z, (h : MulAut V) z ∈ Z)
    (g : ↥L) (x : MulAut V) :
    HasFixSec U Z ((g : MulAut V) * x * (g : MulAut V)⁻¹) ↔ HasFixSec U Z x := by
  refine hasFixSec_conj_iff (hLU g) (fun u hu => ?_) (hLZ g) (fun z hz => ?_)
  · simpa using hLU g⁻¹ u hu
  · simpa using hLZ g⁻¹ z hz

theorem alt6_false {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(alternatingGroup (Fin 6)) →* ↥L} (hπ : (FFModel.altDn 6).RealizesVia L U Z π)
    (hinj : Function.Injective π) {s : MulAut V} (hU : ∀ u ∈ U, s u ∈ U)
    (hU' : ∀ u ∈ U, s⁻¹ u ∈ U) (hZ : ∀ z ∈ Z, s z ∈ Z) (hZ' : ∀ z ∈ Z, s⁻¹ z ∈ Z)
    (hL : ∀ l ∈ L, s * l * s⁻¹ ∈ L) {y : MulAut V} (hyL : y ∈ L) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hfuse : ∀ g ∈ L, s * y * s⁻¹ ≠ g * y * g⁻¹) : False := by
  classical
  have hLU := hπ.2.2.2.1
  have hLZ := hπ.2.2.2.2.1
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(alternatingGroup (Fin 6)), π γ = ⟨y, hyL⟩ := hπ.1 ⟨y, hyL⟩
  have hy' : s * y * s⁻¹ ∈ L := hL y hyL
  obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥(alternatingGroup (Fin 6)), π γ' = ⟨s * y * s⁻¹, hy'⟩ :=
    hπ.1 ⟨s * y * s⁻¹, hy'⟩
  have hγv : ((π γ : ↥L) : MulAut V) = y := congrArg Subtype.val hγ
  have hγ'v : ((π γ' : ↥L) : MulAut V) = s * y * s⁻¹ := congrArg Subtype.val hγ'
  have hγ3 : γ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact Subtype.ext (by simp [hγv, hy3])
  have hγ1 : γ ≠ 1 := fun h => hy1 (by rw [← hγv, h, map_one]; rfl)
  have hγ'3 : γ' ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact Subtype.ext (by simp [hγ'v, conj_pow, hy3])
  have hγ'1 : γ' ≠ 1 := fun h => hy1 (by
    have h1 : s * y * s⁻¹ = 1 := by rw [← hγ'v, h, map_one]; rfl
    simpa using h1)
  have hC : ∀ δ : ↥(alternatingGroup (Fin 6)), ∀ c : Equiv.Perm (Fin 6),
      ∀ hc : c ∈ alternatingGroup (Fin 6), ∀ x : ↥(alternatingGroup (Fin 6)),
        (x : Equiv.Perm (Fin 6)) = (δ : Equiv.Perm (Fin 6)) * c * (δ : Equiv.Perm (Fin 6))⁻¹ →
        (HasFixSec U Z ((π x : ↥L) : MulAut V) ↔ altFix' c) := by
    intro δ c hc x hx
    have hx' : x = δ * ⟨c, hc⟩ * δ⁻¹ := Subtype.ext (by simpa using hx)
    rw [hx', map_mul, map_mul, map_inv]
    have := hasFixSec_conj_of_mem hLU hLZ (π δ) ((π ⟨c, hc⟩ : ↥L) : MulAut V)
    rw [show ((π δ : ↥L) : MulAut V) * ((π ⟨c, hc⟩ : ↥L) : MulAut V) * ((π δ : ↥L) : MulAut V)⁻¹ =
      ((π δ * π ⟨c, hc⟩ * (π δ)⁻¹ : ↥L) : MulAut V) from rfl] at this
    rw [this]
    exact hasFixSec_iff hπ ⟨c, hc⟩
  have hinvs : HasFixSec U Z ((π γ' : ↥L) : MulAut V) ↔ HasFixSec U Z ((π γ : ↥L) : MulAut V) := by
    rw [hγ'v, hγv]
    exact hasFixSec_conj_iff hU hU' hZ hZ'
  have hc3 : c3 ∈ alternatingGroup (Fin 6) := c3_mem
  have hd3 : d3 ∈ alternatingGroup (Fin 6) := d3_mem
  have key : ∀ (c : Equiv.Perm (Fin 6)), c ∈ alternatingGroup (Fin 6) → ConjTo c γ → ConjTo c γ' → False := by
    intro c hc ⟨δ₁, h₁⟩ ⟨δ₂, h₂⟩
    apply hfuse ((π (δ₂ * δ₁⁻¹) : ↥L) : MulAut V) (π (δ₂ * δ₁⁻¹)).2
    have h12 : γ' = (δ₂ * δ₁⁻¹) * γ * (δ₂ * δ₁⁻¹)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, h₁, h₂]
      group
    rw [← hγ'v, h12, map_mul, map_mul, map_inv, ← hγv]
    rfl
  rcases classify3' γ hγ1 hγ3 with hγC | hγD <;> rcases classify3' γ' hγ'1 hγ'3 with hγ'C | hγ'D
  · exact key c3 hc3 hγC hγ'C
  ·
    obtain ⟨δ, hδ⟩ := hγC
    obtain ⟨δ', hδ'⟩ := hγ'D
    have e1 := (hC δ c3 hc3 γ hδ).2 altFix'_c3
    have e2 := (hC δ' d3 hd3 γ' hδ').1 (hinvs.2 e1)
    exact not_altFix'_d3 e2
  · obtain ⟨δ, hδ⟩ := hγD
    obtain ⟨δ', hδ'⟩ := hγ'C
    have e1 := (hC δ' c3 hc3 γ' hδ').2 altFix'_c3
    have e2 := (hC δ d3 hd3 γ hδ).1 (hinvs.1 e1)
    exact not_altFix'_d3 e2
  · exact key d3 hd3 hγD hγ'D

end Alt

end LRed5

end CFSG.Quasithin
