module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SecMod
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sec8_exists_comm_section {R P I N : Subgroup G} {x : G} (hsec : SecHyp R P I)
    (hxP : ∀ y ∈ P, x * y * x⁻¹ ∈ P)
    (hxR : ∀ ρ ∈ R, ρ * x * ρ⁻¹ * x⁻¹ ∈ N) (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I) :
    ∃ U : Subgroup G, I ≤ U ∧ U ≤ P ∧ (∀ ρ ∈ R, conjSubgroup ρ U = U) ∧
      (∀ w ∈ P, ⁅x, w⁆ ∈ U) ∧ (∀ y ∈ U, ∃ w ∈ P, y * ⁅x, w⁆⁻¹ ∈ I) := by
  obtain ⟨M, iMo, iAct, κ, hκ⟩ := exists_sectionModule hsec
  have hcP : ∀ w ∈ P, ⁅x, w⁆ ∈ P := fun w hw => by
    rw [commutatorElement_def]
    exact P.mul_mem (hxP w hw) (P.inv_mem hw)
  have hconj : ∀ u v : ↥P, κ (u * v * u⁻¹) = κ v := by
    intro u v
    rw [hκ.eq_iff]
    have e : ((u * v * u⁻¹ : ↥P) : G) * ((v : ↥P) : G)⁻¹ = ⁅(u : G), (v : G)⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def] <;> group
    rw [e]
    exact hsec.comm u u.2 v v.2
  have hκI : ∀ i : ↥P, (i : G) ∈ I → κ i = 1 := fun i hi => (hκ.ker i).mpr hi
  have hκabs : ∀ i j a : ↥P, (i : G) ∈ I → (j : G) ∈ I → κ (i * a * j) = κ a := by
    intro i j a hi hj
    rw [map_mul, map_mul, hκI i hi, hκI j hj, one_mul, mul_one]
  obtain ⟨f, hf⟩ : ∃ f : ↥P → M, ∀ w : ↥P,
      f w = Multiplicative.toAdd (κ ⟨⁅x, (w : G)⁆, hcP (w : G) w.2⟩) :=
    ⟨fun w => Multiplicative.toAdd (κ ⟨⁅x, (w : G)⁆, hcP (w : G) w.2⟩), fun w => rfl⟩
  have hf_mul : ∀ w₁ w₂ : ↥P, f (w₁ * w₂) = f w₁ + f w₂ := by
    intro w₁ w₂
    have e : (⟨⁅x, ((w₁ * w₂ : ↥P) : G)⁆, hcP _ (w₁ * w₂).2⟩ : ↥P) =
        (⟨⁅x, (w₁ : G)⁆, hcP _ w₁.2⟩ : ↥P) *
          (w₁ * (⟨⁅x, (w₂ : G)⁆, hcP _ w₂.2⟩ : ↥P) * w₁⁻¹) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [hf (w₁ * w₂), hf w₁, hf w₂, e, map_mul, toAdd_mul, hconj]
  have hequiv : ∀ (r : ↥R) (w : ↥P),
      r • f w = f ⟨(r : G) * (w : G) * (r : G)⁻¹, hsec.normP r r.2 (w : G) w.2⟩ := by
    intro r w
    have hcR : (r : G) * ⁅x, (w : G)⁆ * (r : G)⁻¹ ∈ P :=
      hsec.normP r r.2 _ (hcP (w : G) w.2)
    have hw' : (r : G) * (w : G) * (r : G)⁻¹ ∈ P := hsec.normP r r.2 _ w.2
    have hcN : (r : G) * x * (r : G)⁻¹ * x⁻¹ ∈ N := hxR r r.2
    have hi1 : ⁅(r : G) * x * (r : G)⁻¹ * x⁻¹, ⁅x, (r : G) * (w : G) * (r : G)⁻¹⁆⁆ ∈ I :=
      hN _ hcN _ (hcP _ hw')
    have hi2 : ⁅(r : G) * x * (r : G)⁻¹ * x⁻¹, (r : G) * (w : G) * (r : G)⁻¹⁆ ∈ I :=
      hN _ hcN _ hw'
    have hact := hκ.act r ⟨⁅x, (w : G)⁆, hcP (w : G) w.2⟩
      ⟨(r : G) * ⁅x, (w : G)⁆ * (r : G)⁻¹, hcR⟩ rfl
    have hact' : Multiplicative.toAdd (κ ⟨(r : G) * ⁅x, (w : G)⁆ * (r : G)⁻¹, hcR⟩) =
        r • Multiplicative.toAdd (κ ⟨⁅x, (w : G)⁆, hcP (w : G) w.2⟩) := by
      rw [hact, toAdd_ofAdd]
    have e : (⟨(r : G) * ⁅x, (w : G)⁆ * (r : G)⁻¹, hcR⟩ : ↥P) =
        (⟨⁅(r : G) * x * (r : G)⁻¹ * x⁻¹, ⁅x, (r : G) * (w : G) * (r : G)⁻¹⁆⁆, hsec.le hi1⟩ :
          ↥P) *
          (⟨⁅x, (r : G) * (w : G) * (r : G)⁻¹⁆, hcP _ hw'⟩ : ↥P) *
          (⟨⁅(r : G) * x * (r : G)⁻¹ * x⁻¹, (r : G) * (w : G) * (r : G)⁻¹⁆, hsec.le hi2⟩ :
            ↥P) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group
    have key : κ ⟨(r : G) * ⁅x, (w : G)⁆ * (r : G)⁻¹, hcR⟩ =
        κ ⟨⁅x, (r : G) * (w : G) * (r : G)⁻¹⁆, hcP _ hw'⟩ := by
      rw [e]
      exact hκabs ⟨_, hsec.le hi1⟩ ⟨_, hsec.le hi2⟩ _ hi1 hi2
    rw [hf w, hf, ← hact', key]
  obtain ⟨W, hW⟩ : ∃ W : AddSubgroup M, ∀ a : M, a ∈ W ↔ ∃ w : ↥P, f w = a :=
    ⟨{ carrier := {a | ∃ w : ↥P, f w = a}
       add_mem' := by
         rintro _ _ ⟨w₁, rfl⟩ ⟨w₂, rfl⟩
         exact ⟨w₁ * w₂, hf_mul w₁ w₂⟩
       zero_mem' := ⟨1, ((congrArg f (mul_one (1 : ↥P))).symm.trans (hf_mul 1 1)).trans
         (hκ.two (f 1))⟩
       neg_mem' := by
         rintro _ ⟨w, rfl⟩
         exact ⟨w, (neg_eq_iff_add_eq_zero.mpr (hκ.two (f w))).symm⟩ }, fun a => Iff.rfl⟩
  have hWinv : ∀ r : ↥R, W.map (DistribSMul.toAddMonoidHom M r) = W := by
    intro r
    ext a
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨w, rfl⟩ := (hW b).mp hb
      show r • f w ∈ W
      rw [hequiv r w]
      exact (hW _).mpr ⟨_, rfl⟩
    · intro ha
      obtain ⟨w, rfl⟩ := (hW a).mp ha
      refine ⟨r⁻¹ • f w, (hW _).mpr ⟨_, (hequiv r⁻¹ w).symm⟩, ?_⟩
      show r • r⁻¹ • f w = f w
      rw [smul_inv_smul]
  obtain ⟨U, hIU, hUP, hUW⟩ := exists_secSub_eq hsec.le hκ W
  refine ⟨U, hIU, hUP, ?_, ?_, ?_⟩
  · intro ρ hρ
    refine (conjSubgroup_eq_self_iff_secSub hsec hκ ⟨ρ, hρ⟩ hIU hUP).mpr ?_
    rw [hUW]
    exact hWinv ⟨ρ, hρ⟩
  · intro w hw
    have hmem : Multiplicative.toAdd (κ ⟨⁅x, w⁆, hcP w hw⟩) ∈ secSub κ U := by
      rw [hUW]
      exact (hW _).mpr ⟨⟨w, hw⟩, hf ⟨w, hw⟩⟩
    exact (toAdd_mem_secSub_iff hκ hIU ⟨⁅x, w⁆, hcP w hw⟩).mp hmem
  · intro y hy
    have hyP : y ∈ P := hUP hy
    have hmem : Multiplicative.toAdd (κ ⟨y, hyP⟩) ∈ secSub κ U :=
      (toAdd_mem_secSub_iff hκ hIU ⟨y, hyP⟩).mpr hy
    rw [hUW, hW] at hmem
    obtain ⟨w, hw⟩ := hmem
    rw [hf] at hw
    have h1 : κ ⟨⁅x, (w : G)⁆, hcP (w : G) w.2⟩ = κ ⟨y, hyP⟩ :=
      Multiplicative.toAdd.injective hw
    have h2 : ⁅x, (w : G)⁆ * y⁻¹ ∈ I := (hκ.eq_iff _ _).mp h1
    refine ⟨(w : G), w.2, ?_⟩
    have h3 := I.inv_mem h2
    rwa [mul_inv_rev, inv_inv] at h3

end

section

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

variable {G : Type} [Group G] [Finite G]

theorem sec8_card_le_of_comm_section {R P I U T Z : Subgroup G} {Mo : Type} [AddCommGroup Mo]
    [DistribMulAction ↥R Mo] {κ : ↥P →* Multiplicative Mo}
    (hκ : IsSecMod R P I Mo κ) (hIU : I ≤ U) (hUP : U ≤ P) (hZI : Z ≤ I) (hTP : T ≤ P)
    (hZT : Z ≤ T) (hUT : ∀ y ∈ U, ∃ w ∈ T, y * w⁻¹ ∈ I) :
    Nat.card ↥U * Nat.card ↥Z ≤ Nat.card ↥T * Nat.card ↥I := by
  haveI : Finite Mo := hκ.finite
  have hle : secSub κ U ≤ secSub κ T := by
    intro a ha
    obtain ⟨y, hyU, hya⟩ := mem_secSub.mp ha
    obtain ⟨w, hwT, hyw⟩ := hUT (y : G) hyU
    exact mem_secSub.mpr ⟨⟨w, hTP hwT⟩, hwT,
      ((hκ.eq_iff y ⟨w, hTP hwT⟩).mpr hyw).symm.trans hya⟩
  have hsec : Nat.card ↥(secSub κ U) ≤ Nat.card ↥(secSub κ T) :=
    AddSubgroup.card_le_of_le hle
  have hT : Nat.card ↥(secSub κ T) * Nat.card ↥(T ⊓ I) = Nat.card ↥T := by
    have hker : κ.ker = I.subgroupOf P := by
      ext x
      rw [MonoidHom.mem_ker, hκ.ker, Subgroup.mem_subgroupOf]
    have h1 : Nat.card ↥(secSub κ T) = Nat.card ↥((T.subgroupOf P).map κ) :=
      Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd (fun a => Iff.rfl))
    have h2 := card_inf_mul_card_map hTP κ hker
    rw [h1, mul_comm]
    exact h2
  have hU : Nat.card ↥(secSub κ U) * Nat.card ↥I = Nat.card ↥U :=
    natCard_secSub_mul (hIU.trans hUP) hκ hIU hUP
  have hZle : Nat.card ↥Z ≤ Nat.card ↥(T ⊓ I) :=
    Subgroup.card_le_of_le (le_inf hZT hZI)
  calc Nat.card ↥U * Nat.card ↥Z
      = (Nat.card ↥(secSub κ U) * Nat.card ↥I) * Nat.card ↥Z := by rw [hU]
    _ ≤ (Nat.card ↥(secSub κ T) * Nat.card ↥I) * Nat.card ↥(T ⊓ I) :=
        Nat.mul_le_mul (Nat.mul_le_mul hsec le_rfl) hZle
    _ = (Nat.card ↥(secSub κ T) * Nat.card ↥(T ⊓ I)) * Nat.card ↥I := by ring
    _ = Nat.card ↥T * Nat.card ↥I := by rw [hT]

end

end CFSG.RankThree.GF2n.Stroth80
