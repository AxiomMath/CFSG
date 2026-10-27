module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab
public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open Equiv CFSG.Quasithin.F53Mod CFSG.Quasithin.F53
open scoped Pointwise
open Multiplicative

private theorem D0fin_fix_all : ∀ q : Fin 5, (∀ d ∈ D0fin, d q = q) → q = 4 := by
  decide +kernel

theorem exists_conj_D0 (P : Subgroup (Perm (Fin 5))) (hP : Nat.card P = 8) :
    ∃ g : Perm (Fin 5), ∀ x : Perm (Fin 5), x ∈ P ↔ g⁻¹ * x * g ∈ D0fin := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP2, hPs, -⟩ := sylow_of_card_eight P hP
  obtain ⟨hD2, hDs, -⟩ := sylow_of_card_eight D0 D0_card
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) (hD2.toSylow hDs) (hP2.toSylow hPs)
  refine ⟨g, fun x => ?_⟩
  have hPeq : x ∈ P ↔ ∃ y ∈ D0fin, g * y * g⁻¹ = x := by
    have h1 : P = MulAut.conj g • D0 := by
      have := congrArg (fun Q : Sylow 2 (Perm (Fin 5)) => (Q : Subgroup (Perm (Fin 5)))) hg
      simpa [Sylow.coe_subgroup_smul] using this.symm
    rw [h1, Subgroup.mem_smul_pointwise_iff_exists]
    simp [MulAut.conj_apply, D0]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hPeq.mp hx
    have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [this]
    exact hy
  · intro hx
    exact hPeq.mpr ⟨g⁻¹ * x * g, hx, by group⟩

private theorem sign_conj (g y : Perm (Fin 5)) : Perm.sign (g⁻¹ * y * g) = Perm.sign y := by
  rw [map_mul, map_mul, map_inv]
  exact (mul_comm _ _).trans (mul_inv_cancel_left _ _)

private theorem D0_inf_all : ∀ z : Perm (Fin 5),
    (z ∈ D0fin ∧ Perm.sign z = 1) ↔ (Perm.sign z = 1 ∧ z * z = 1 ∧ z 4 = 4) := by
  decide +kernel

theorem mem_inf_alt_iff_of_card_eight {P : Subgroup (Perm (Fin 5))} (hP : Nat.card P = 8)
    {p₀ : Fin 5} (hp : ∀ σ ∈ P, σ p₀ = p₀) (y : Perm (Fin 5)) :
    y ∈ P ⊓ alternatingGroup (Fin 5) ↔ (Perm.sign y = 1 ∧ y * y = 1 ∧ y p₀ = p₀) := by
  obtain ⟨g, hg⟩ := exists_conj_D0 P hP
  have hq : g⁻¹ p₀ = 4 := by
    apply D0fin_fix_all
    intro d hd
    have hmem : g * d * g⁻¹ ∈ P := by
      refine (hg _).mpr ?_
      have : g⁻¹ * (g * d * g⁻¹) * g = d := by group
      rw [this]
      exact hd
    have h1 := hp _ hmem
    apply g.injective
    simpa [Perm.mul_apply] using h1
  have hp4 : p₀ = g 4 := by
    rw [← hq]
    simp
  subst hp4
  have hs := sign_conj g y
  have hsq : g⁻¹ * y * g * (g⁻¹ * y * g) = 1 ↔ y * y = 1 := by
    constructor
    · intro e
      calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = 1 := by rw [e]; group
    · intro e
      calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
        _ = 1 := by rw [e]; group
  have hz4 : (g⁻¹ * y * g) 4 = 4 ↔ y (g 4) = g 4 := by
    rw [show (g⁻¹ * y * g) 4 = g⁻¹ (y (g 4)) by simp [Perm.mul_apply], Perm.inv_eq_iff_eq]
  rw [Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup, hg y]
  constructor
  · rintro ⟨hz, hs1⟩
    obtain ⟨-, h2, h3⟩ := (D0_inf_all _).mp ⟨hz, by rw [hs]; exact hs1⟩
    exact ⟨hs1, hsq.mp h2, hz4.mp h3⟩
  · rintro ⟨hs1, h2, h3⟩
    obtain ⟨hz, -⟩ := (D0_inf_all (g⁻¹ * y * g)).mpr ⟨by rw [hs]; exact hs1, hsq.mpr h2,
      hz4.mpr h3⟩
    exact ⟨hz, hs1⟩

private theorem fix_point_of_natAct_fix_all : ∀ p : Fin 5, ∀ c : Fin 4 → ZMod 2, c ≠ 0 →
    (∀ y : Perm (Fin 5), Perm.sign y = 1 → y * y = 1 → y p = p → CFSG.Quasithin.F53Mod.natAct y c = c) →
    ∀ τ : Perm (Fin 5), CFSG.Quasithin.F53Mod.natAct τ c = c → τ p = p := by
  decide +kernel

theorem fix_point_of_natAct_fix {p₀ : Fin 5} {c : Fin 4 → ZMod 2} (hc : c ≠ 0)
    (hcT : ∀ y : Perm (Fin 5), Perm.sign y = 1 → y * y = 1 → y p₀ = p₀ → CFSG.Quasithin.F53Mod.natAct y c = c)
    {τ : Perm (Fin 5)} (hτ : CFSG.Quasithin.F53Mod.natAct τ c = c) : τ p₀ = p₀ :=
  fix_point_of_natAct_fix_all p₀ c hc hcT τ hτ

private def dAset (c : Fin 4 → ZMod 2) : Finset (Fin 4 → ZMod 2) :=
  insert 0 (D0fin.image fun d => CFSG.Quasithin.F53Mod.natAct d c) ∪ D0fin.image fun d => c + CFSG.Quasithin.F53Mod.natAct d c

private theorem dAset_card_all : ∀ c : Fin 4 → ZMod 2,
    (∃ v ∈ D0fin, Perm.sign v = 1 ∧ CFSG.Quasithin.F53Mod.natAct v c ≠ c) → 5 ≤ (dAset c).card := by
  decide +kernel

private theorem act_mul_apply' (σ τ : Perm (Fin 5)) (x : nat.W) :
    nat.act (σ * τ) x = nat.act σ (nat.act τ x) := by
  rw [map_mul]
  rfl

private theorem act_one_apply' (x : nat.W) : nat.act 1 x = x := by
  rw [map_one]
  rfl

private theorem act_conj_apply' (g d : Perm (Fin 5)) (x : nat.W) :
    nat.act g (nat.act d x) = nat.act (g * d * g⁻¹) (nat.act g x) := by
  rw [← act_mul_apply' (g * d * g⁻¹) g x, show g * d * g⁻¹ * g = g * d by group,
    act_mul_apply']

private theorem dAset_le_card (S : Subgroup nat.W) {c : Fin 4 → ZMod 2}
    (hc : (ofAdd c : nat.W) ∈ S)
    (hD : ∀ d ∈ D0fin, ∀ x ∈ S, nat.act d x ∈ S) :
    (dAset c).card ≤ Nat.card S := by
  have hmem : ∀ a ∈ dAset c, (ofAdd a : nat.W) ∈ S := by
    intro a ha
    unfold dAset at ha
    rw [Finset.mem_union, Finset.mem_insert, Finset.mem_image, Finset.mem_image] at ha
    rcases ha with (rfl | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩
    · exact S.one_mem
    · exact hD d hd _ hc
    · exact S.mul_mem hc (hD d hd _ hc)
  have hinj : Function.Injective
      (fun a : {x // x ∈ dAset c} => (⟨(ofAdd a.1 : nat.W), hmem a.1 a.2⟩ : S)) := by
    intro a b h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (ofAdd.injective h')
  have hc' := Nat.card_le_card_of_injective _ hinj
  simpa [Nat.card_eq_fintype_card] using hc'

theorem le_fixW_of_invariant_card_le_four {P : Subgroup (Perm (Fin 5))} (hP : Nat.card P = 8)
    {Y : Subgroup nat.W} (hY : ∀ σ ∈ P, ∀ y ∈ Y, nat.act σ y ∈ Y) (h4 : Nat.card Y ≤ 4) :
    Y ≤ fixW nat (P ⊓ alternatingGroup (Fin 5)) := by
  intro y hy
  rw [mem_fixW]
  intro τ hτ
  rw [Subgroup.mem_inf] at hτ
  obtain ⟨g, hg⟩ := exists_conj_D0 P hP
  let S : Subgroup nat.W := Y.comap (nat.act g).toMonoidHom
  have hS : ∀ x, x ∈ S ↔ nat.act g x ∈ Y := fun x => Iff.rfl
  have hSD : ∀ d ∈ D0fin, ∀ x ∈ S, nat.act d x ∈ S := by
    intro d hd x hx
    rw [hS, act_conj_apply']
    refine hY _ ((hg _).mpr ?_) _ ((hS x).mp hx)
    have : g⁻¹ * (g * d * g⁻¹) * g = d := by group
    rw [this]
    exact hd
  have hcard : Nat.card S ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun s : S => (⟨nat.act g s.1, s.2⟩ : Y)) ?_) h4
    intro a b hab
    have h1 : nat.act g a.1 = nat.act g b.1 := congrArg Subtype.val hab
    exact Subtype.ext ((nat.act g).injective h1)
  obtain ⟨w, hwdef⟩ : ∃ w : nat.W, w = nat.act g⁻¹ y := ⟨_, rfl⟩
  have hgw : nat.act g w = y := by
    rw [hwdef, ← act_mul_apply', mul_inv_cancel, act_one_apply']
  have hwS : w ∈ S := by
    rw [hS, hgw]
    exact hy
  obtain ⟨v, hvdef⟩ : ∃ v : Perm (Fin 5), v = g⁻¹ * τ * g := ⟨_, rfl⟩
  have hτv : τ = g * v * g⁻¹ := by rw [hvdef]; group
  have hvD : v ∈ D0fin := by
    rw [hvdef]
    exact (hg τ).mp hτ.1
  have hvs : Perm.sign v = 1 := by
    rw [hvdef, sign_conj]
    exact Equiv.Perm.mem_alternatingGroup.mp hτ.2
  have hvw : nat.act v w = w := by
    by_contra hne
    have hne' : CFSG.Quasithin.F53Mod.natAct v (toAdd w : Fin 4 → ZMod 2) ≠ (toAdd w : Fin 4 → ZMod 2) := by
      intro h
      apply hne
      exact congrArg ofAdd h
    have h5 := dAset_card_all (toAdd w : Fin 4 → ZMod 2) ⟨v, hvD, hvs, hne'⟩
    have hc : (ofAdd (toAdd w : Fin 4 → ZMod 2) : nat.W) ∈ S := hwS
    have := dAset_le_card S hc hSD
    omega
  rw [hτv, ← hgw, ← act_conj_apply', hvw]

end CFSG.Quasithin.Kleidman.F53Hss36

end
