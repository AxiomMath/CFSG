module

public import CFSG.Quasithin.Background.GoldschmidtE23Comp
public import CFSG.Quasithin.Background.GoldschmidtE23Fam
public import CFSG.Quasithin.Background.GoldschmidtE23SymFin2
public import CFSG.Quasithin.Background.GoldschmidtE23SymSpec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique G6 Equiv

namespace GE23

theorem arith_offender {ι : Type*} (s : Finset ι) (a c : ι → ℕ) (hapos : ∀ i ∈ s, 0 < a i)
    (hc : ∀ i ∈ s, 0 < c i) (hle : ∀ i ∈ s, a i * c i ≤ 16) {b f v : ℕ} (hf : 0 < f)
    (hb : b ≤ ∏ i ∈ s, a i) (hP : v * ∏ i ∈ s, c i = f * 16 ^ s.card) :
    b * f ≤ v ∧ (b * f = v → b = ∏ i ∈ s, a i ∧ ∀ i ∈ s, a i * c i = 16) := by
  have hcpos : 0 < ∏ i ∈ s, c i := Finset.prod_pos hc
  have hprod : (∏ i ∈ s, a i) * ∏ i ∈ s, c i = ∏ i ∈ s, (a i * c i) :=
    (Finset.prod_mul_distrib).symm
  have hle' : ∏ i ∈ s, (a i * c i) ≤ 16 ^ s.card := by
    calc ∏ i ∈ s, (a i * c i) ≤ ∏ _i ∈ s, 16 := Finset.prod_le_prod hle
      _ = 16 ^ s.card := Finset.prod_const _
  have h1 : b * f * ∏ i ∈ s, c i ≤ v * ∏ i ∈ s, c i := by
    calc b * f * ∏ i ∈ s, c i ≤ (∏ i ∈ s, a i) * f * ∏ i ∈ s, c i :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb)
      _ = f * ∏ i ∈ s, (a i * c i) := by rw [← hprod]; ring
      _ ≤ f * 16 ^ s.card := Nat.mul_le_mul_left _ hle'
      _ = v * ∏ i ∈ s, c i := hP.symm
  refine ⟨Nat.le_of_mul_le_mul_right h1 hcpos, fun heq => ?_⟩
  subst heq
  have h2 : f * ∏ i ∈ s, (a i * c i) = f * 16 ^ s.card := by
    refine le_antisymm (Nat.mul_le_mul_left _ hle') ?_
    calc f * 16 ^ s.card = b * f * ∏ i ∈ s, c i := hP.symm
      _ ≤ (∏ i ∈ s, a i) * f * ∏ i ∈ s, c i :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb)
      _ = f * ∏ i ∈ s, (a i * c i) := by rw [← hprod]; ring
  have h3 : ∏ i ∈ s, (a i * c i) = 16 ^ s.card := Nat.eq_of_mul_eq_mul_left hf h2
  have h4 : ∀ i ∈ s, a i * c i = 16 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi, hne⟩ := hcon
    have hlt : a i * c i < 16 := lt_of_le_of_ne (hle i hi) hne
    have : ∏ i ∈ s, (a i * c i) < ∏ _i ∈ s, 16 :=
      Finset.prod_lt_prod₀ (fun j hj => Nat.mul_pos (hapos j hj) (hc j hj)) hle ⟨i, hi, hlt⟩
    rw [Finset.prod_const, h3] at this
    exact lt_irrefl _ this
  refine ⟨?_, h4⟩
  have h5 : (∏ i ∈ s, a i) * f * ∏ i ∈ s, c i = b * f * ∏ i ∈ s, c i := by
    calc (∏ i ∈ s, a i) * f * ∏ i ∈ s, c i = f * ∏ i ∈ s, (a i * c i) := by
          rw [← hprod]; ring
      _ = f * 16 ^ s.card := by rw [h3]
      _ = b * f * ∏ i ∈ s, c i := hP.symm
  have h6 : b * (f * ∏ i ∈ s, c i) = (∏ i ∈ s, a i) * (f * ∏ i ∈ s, c i) := by
    rw [← mul_assoc, ← mul_assoc]
    exact h5.symm
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hf hcpos) h6

theorem eq_of_coreAct_eq {σ τ : Perm (Fin 5)}
    (h : ∀ u : ↥(coreMod 5), coreAct 5 σ u = coreAct 5 τ u) : σ = τ := by
  have h2 : τ⁻¹ * σ = 1 := by
    refine eq_one_of_coreAct_trivial _ fun u => ?_
    rw [map_mul, MulAut.mul_apply, h u, map_inv]
    exact MulAut.inv_apply_self _ _ _
  exact (inv_mul_eq_one.1 h2).symm

section Restr

variable {V : Type} [CommGroup V]

@[expose] def restrPerm (β : ↥(coreMod 5) →* V) (B : Subgroup (MulAut V)) :
    Subgroup (Perm (Fin 5)) where
  carrier := {σ | ∃ b ∈ B, ∀ u : ↥(coreMod 5), b (β u) = β (coreAct 5 σ u)}
  one_mem' := ⟨1, B.one_mem, fun u => by simp⟩
  mul_mem' := by
    rintro σ₁ σ₂ ⟨b₁, hb₁, h₁⟩ ⟨b₂, hb₂, h₂⟩
    refine ⟨b₁ * b₂, B.mul_mem hb₁ hb₂, fun u => ?_⟩
    rw [MulAut.mul_apply, h₂ u, h₁ (coreAct 5 σ₂ u), map_mul, MulAut.mul_apply]
  inv_mem' := by
    rintro σ ⟨b, hb, h⟩
    refine ⟨b⁻¹, B.inv_mem hb, fun u => ?_⟩
    have h1 : b (β (coreAct 5 σ⁻¹ u)) = β u := by
      rw [h, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    calc b⁻¹ (β u) = b⁻¹ (b (β (coreAct 5 σ⁻¹ u))) := by rw [h1]
      _ = β (coreAct 5 σ⁻¹ u) := by simp

variable {β : ↥(coreMod 5) →* V} {B : Subgroup (MulAut V)}

variable {H D : Subgroup (MulAut V)} {ψ : Perm (Fin 5) →* MulAut V}

theorem SymSpec.mem_restrPerm_of_act (h : SymSpec H D ψ β) {b : MulAut V} (hb : b ∈ B)
    {σ : Perm (Fin 5)} (hbσ : ∀ w ∈ commV H, b w = ψ σ w) : σ ∈ restrPerm β B :=
  ⟨b, hb, fun u => by rw [hbσ _ (h.β_mem u), h.equiv]⟩

theorem SymSpec.restrPerm_comm (h : SymSpec H D ψ β) (hB : IsElemAbelian2 B) {σ τ : Perm (Fin 5)}
    (hσ : σ ∈ restrPerm β B) (hτ : τ ∈ restrPerm β B) : σ * τ = τ * σ := by
  obtain ⟨b₁, hb₁, h₁⟩ := hσ
  obtain ⟨b₂, hb₂, h₂⟩ := hτ
  refine eq_of_coreAct_eq fun u => h.β_inj ?_
  have e1 : β (coreAct 5 (σ * τ) u) = b₁ (b₂ (β u)) := by
    rw [map_mul, MulAut.mul_apply, ← h₁, h₂]
  have e2 : β (coreAct 5 (τ * σ) u) = b₂ (b₁ (β u)) := by
    rw [map_mul, MulAut.mul_apply, ← h₂, h₁]
  rw [e1, e2]
  have := hB.1 b₁ hb₁ b₂ hb₂
  exact congrArg (fun x : MulAut V => x (β u)) this

theorem SymSpec.restrPerm_sq (h : SymSpec H D ψ β) (hB : IsElemAbelian2 B) {σ : Perm (Fin 5)}
    (hσ : σ ∈ restrPerm β B) : σ * σ = 1 := by
  obtain ⟨b, hb, hbσ⟩ := hσ
  refine eq_of_coreAct_eq fun u => h.β_inj ?_
  have e1 : β (coreAct 5 (σ * σ) u) = b (b (β u)) := by
    rw [map_mul, MulAut.mul_apply, hbσ u, hbσ (coreAct 5 σ u)]
  rw [e1, map_one, MulAut.one_apply]
  have := hB.2 b hb
  have h2 : b * b = 1 := by rw [← pow_two]; exact this
  exact congrArg (fun x : MulAut V => x (β u)) h2

end Restr

section Fam

variable {V : Type} [CommGroup V] [Finite V]

structure SymFam (I : Finset (Subgroup (MulAut V)))
    (ψ : Subgroup (MulAut V) → Perm (Fin 5) →* MulAut V)
    (β : Subgroup (MulAut V) → ↥(coreMod 5) →* V) : Prop where
  spec : ∀ H ∈ I, SymSpec H (d8.map (ψ H)) (ψ H) (β H)
  hcomm : ∀ H ∈ I, ∀ H' ∈ I, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a
  hind : ∀ H ∈ I, H ⊓ ⨆ H' ∈ I, ⨆ (_ : H' ≠ H), H' = ⊥
  hother : ∀ H ∈ I, ∀ H' ∈ I, H' ≠ H → ∀ y ∈ H', ∀ u ∈ commV H, y u = u
  hind0 : ∀ H ∈ I, commV H ⊓ ⨆ H' ∈ I, ⨆ (_ : H' ≠ H), commV H' = ⊥
  hsplit : ∀ v : V, ∃ w ∈ ⨆ H ∈ I, commV H, ∃ c ∈ fixV (⨆ H ∈ I, H), v = w * c

namespace SymFam

variable {I : Finset (Subgroup (MulAut V))} {ψ : Subgroup (MulAut V) → Perm (Fin 5) →* MulAut V}
  {β : Subgroup (MulAut V) → ↥(coreMod 5) →* V} (hF : SymFam I ψ β)

include hF

omit [Finite V] in
theorem hstab : ∀ H ∈ I, ∀ y ∈ H, ∀ u ∈ commV H, y u ∈ commV H :=
  fun H hH _ hy _ hu => (hF.spec H hH).stab hy hu

omit [Finite V] in
theorem d8_le {H : Subgroup (MulAut V)} (hH : H ∈ I) : d8.map (ψ H) ≤ H :=
  (hF.spec H hH).D_le

omit [Finite V] in
theorem map_le {H : Subgroup (MulAut V)} (hH : H ∈ I) (R : Subgroup (Perm (Fin 5))) :
    R.map (ψ H) ≤ H := by
  rintro x ⟨σ, -, rfl⟩
  exact (hF.spec H hH).ψ_mem σ

omit [Finite V] in
theorem card_iSup (A : Subgroup (MulAut V) → Subgroup (MulAut V)) (hA : ∀ H ∈ I, A H ≤ H) :
    Nat.card ↥(⨆ H ∈ I, A H) = ∏ H ∈ I, Nat.card ↥(A H) := by
  classical
  refine card_iSup_of_indep I A (fun i hi j hj hij a ha b hb =>
    hF.hcomm i hi j hj hij a (hA i hi ha) b (hA j hj hb)) (fun i hi => le_bot_iff.1 ?_)
  calc A i ⊓ ⨆ j ∈ I, ⨆ (_ : j ≠ i), A j ≤ i ⊓ ⨆ j ∈ I, ⨆ (_ : j ≠ i), j :=
      inf_le_inf (hA i hi) (iSup₂_mono fun j hj => iSup_mono fun _ => hA j hj)
    _ = ⊥ := hF.hind i hi

theorem card_fixV_single {H₀ : Subgroup (MulAut V)} (hH₀ : H₀ ∈ I) {A : Subgroup (MulAut V)}
    (hA : A ≤ H₀) :
    Nat.card V * Nat.card ↥(commV H₀ ⊓ fixV A) = Nat.card ↥(fixV A) * 16 := by
  classical
  have hAI : A ≤ ⨆ H ∈ I, H := hA.trans (le_iSup₂_of_le (f := fun H (_ : H ∈ I) => H) H₀ hH₀ le_rfl)
  have h := card_fixV_prod hF.hother hF.hstab hF.hind0 hF.hsplit hAI
  have hothers : ∀ H ∈ I.erase H₀, commV H ⊓ fixV A = commV H := by
    intro H hH
    have hne : H ≠ H₀ := (Finset.mem_erase.1 hH).1
    have hHI : H ∈ I := (Finset.mem_erase.1 hH).2
    refine inf_eq_left.2 fun u hu a ha => ?_
    exact hF.hother H hHI H₀ hH₀ (Ne.symm hne) a (hA ha) u hu
  rw [← Finset.mul_prod_erase I (fun H => Nat.card ↥(commV H ⊓ fixV A)) hH₀,
    ← Finset.mul_prod_erase I (fun H => Nat.card ↥(commV H)) hH₀,
    Finset.prod_congr rfl fun H hH => by rw [hothers H hH]] at h
  have hP : 0 < ∏ H ∈ I.erase H₀, Nat.card ↥(commV H) :=
    Finset.prod_pos fun H _ => Nat.card_pos
  have h2 : Nat.card V * Nat.card ↥(commV H₀ ⊓ fixV A) * ∏ H ∈ I.erase H₀, Nat.card ↥(commV H) =
      Nat.card ↥(fixV A) * 16 * ∏ H ∈ I.erase H₀, Nat.card ↥(commV H) := by
    rw [mul_assoc, h, (hF.spec H₀ hH₀).card_commV, mul_assoc]
  exact Nat.eq_of_mul_eq_mul_right hP h2

theorem key {B : Subgroup (MulAut V)} (hBD : B ≤ ⨆ H ∈ I, d8.map (ψ H)) (hB : IsElemAbelian2 B) :
    Nat.card ↥B * Nat.card ↥(fixV B) ≤ Nat.card V ∧
      (Nat.card ↥B * Nat.card ↥(fixV B) = Nat.card V →
        B = ⨆ H ∈ I, (restrPerm (β H) B).map (ψ H) ∧
        ∀ H ∈ I, restrPerm (β H) B ≤ e4 ∧
          Nat.card ↥(restrPerm (β H) B) * Nat.card ↥(fixΔ (restrPerm (β H) B)) = 16) := by
  classical
  have hBI : B ≤ ⨆ H ∈ I, H := hBD.trans (iSup₂_mono fun H hH => hF.d8_le hH)
  have hres : ∀ H ∈ I, ∀ b ∈ B, ∃ σ ∈ d8,
      ∀ u : ↥(coreMod 5), b (β H u) = β H (coreAct 5 σ u) := by
    intro H hH b hb
    obtain ⟨a, ha, hba⟩ := exists_restr hF.hother hF.hstab (A := fun H => d8.map (ψ H))
      (fun H hH => hF.d8_le hH) (hBD hb) hH
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 ha
    refine ⟨σ, hσ, fun u => ?_⟩
    rw [hba _ ((hF.spec H hH).β_mem u), (hF.spec H hH).equiv]
  have hR8 : ∀ H ∈ I, restrPerm (β H) B ≤ d8 := by
    intro H hH σ hσ
    obtain ⟨b, hb, hbσ⟩ := hσ
    obtain ⟨τ, hτ, hbτ⟩ := hres H hH b hb
    have : σ = τ :=
      eq_of_coreAct_eq fun u => (hF.spec H hH).β_inj ((hbσ u).symm.trans (hbτ u))
    rw [this]
    exact hτ
  have hcomm5 : ∀ H ∈ I, ∀ a ∈ restrPerm (β H) B, ∀ b ∈ restrPerm (β H) B, a * b = b * a :=
    fun H hH a ha b hb => (hF.spec H hH).restrPerm_comm hB ha hb
  have hsq5 : ∀ H ∈ I, ∀ a ∈ restrPerm (β H) B, a * a = 1 :=
    fun H hH a ha => (hF.spec H hH).restrPerm_sq hB ha
  have hcls := fun H (hH : H ∈ I) => classify_sub (hR8 H hH) (hcomm5 H hH) (hsq5 H hH)
  let A : Subgroup (MulAut V) → Subgroup (MulAut V) := fun H => (restrPerm (β H) B).map (ψ H)
  have hAH : ∀ H ∈ I, A H ≤ H := fun H hH => hF.map_le hH _
  have hBA : B ≤ ⨆ H ∈ I, A H := by
    intro b hb
    refine mem_iSup_of_restr hF.hcomm hF.hother hF.hstab hF.hsplit hAH (hBI hb) fun H hH => ?_
    obtain ⟨σ, -, hσ⟩ := hres H hH b hb
    refine ⟨ψ H σ, Subgroup.mem_map_of_mem _ ⟨b, hb, hσ⟩, fun w hw => ?_⟩
    obtain ⟨u, rfl⟩ := (hF.spec H hH).exists_β hw
    rw [hσ u, (hF.spec H hH).equiv]
  have hcardA : ∀ H ∈ I, Nat.card ↥(A H) = Nat.card ↥(restrPerm (β H) B) := fun H hH =>
    Subgroup.card_map_of_injective (hF.spec H hH).ψ_inj
  have hBle : Nat.card ↥B ≤ ∏ H ∈ I, Nat.card ↥(restrPerm (β H) B) := by
    calc Nat.card ↥B ≤ Nat.card ↥(⨆ H ∈ I, A H) := Subgroup.card_le_of_le hBA
      _ = ∏ H ∈ I, Nat.card ↥(A H) := hF.card_iSup A hAH
      _ = ∏ H ∈ I, Nat.card ↥(restrPerm (β H) B) := Finset.prod_congr rfl hcardA
  have hfixc : ∀ H ∈ I, Nat.card ↥(commV H ⊓ fixV B) =
      Nat.card ↥(fixΔ (restrPerm (β H) B)) := by
    intro H hH
    have hS := hF.spec H hH
    have : commV H ⊓ fixV B = (fixΔ (restrPerm (β H) B)).map (β H) := by
      ext v
      constructor
      · rintro ⟨hv, hvB⟩
        obtain ⟨u, rfl⟩ := hS.exists_β hv
        refine ⟨u, fun σ hσ => ?_, rfl⟩
        obtain ⟨b, hb, hbσ⟩ := hσ
        apply hS.β_inj
        rw [← hbσ u]
        exact hvB b hb
      · rintro ⟨u, hu, rfl⟩
        refine ⟨hS.β_mem u, fun b hb => ?_⟩
        obtain ⟨σ, -, hσ⟩ := hres H hH b hb
        rw [hσ u, hu σ ⟨b, hb, hσ⟩]
    rw [this]
    exact Subgroup.card_map_of_injective hS.β_inj
  have hprod := card_fixV_prod hF.hother hF.hstab hF.hind0 hF.hsplit hBI
  have hP : Nat.card V * ∏ H ∈ I, Nat.card ↥(fixΔ (restrPerm (β H) B)) =
      Nat.card ↥(fixV B) * 16 ^ I.card := by
    have e1 : ∏ H ∈ I, Nat.card ↥(commV H ⊓ fixV B) =
        ∏ H ∈ I, Nat.card ↥(fixΔ (restrPerm (β H) B)) := Finset.prod_congr rfl hfixc
    have e2 : ∏ H ∈ I, Nat.card ↥(commV H) = 16 ^ I.card := by
      rw [Finset.prod_congr rfl (fun H hH => (hF.spec H hH).card_commV), Finset.prod_const]
    rw [e1, e2] at hprod
    exact hprod
  have hfpos : 0 < Nat.card ↥(fixV B) := Nat.card_pos
  have hfin := arith_offender I (fun H => Nat.card ↥(restrPerm (β H) B))
    (fun H => Nat.card ↥(fixΔ (restrPerm (β H) B))) (fun H _ => Nat.card_pos)
    (fun H _ => Nat.card_pos) (fun H hH => (hcls H hH).1) hfpos hBle hP
  refine ⟨hfin.1, fun heq => ?_⟩
  obtain ⟨hcard, hall⟩ := hfin.2 heq
  refine ⟨?_, fun H hH => ⟨(hcls H hH).2 (hall H hH), hall H hH⟩⟩
  refine Subgroup.eq_of_le_of_card_ge hBA ?_
  rw [hF.card_iSup A hAH, Finset.prod_congr rfl hcardA, ← hcard]

theorem card_E :
    Nat.card ↥(⨆ H ∈ I, e4.map (ψ H)) * Nat.card ↥(fixV (⨆ H ∈ I, e4.map (ψ H))) =
      Nat.card V := by
  classical
  have hA : ∀ H ∈ I, e4.map (ψ H) ≤ H := fun H hH => hF.map_le hH _
  have hEI : (⨆ H ∈ I, e4.map (ψ H)) ≤ ⨆ H ∈ I, H := iSup₂_mono hA
  have hEcard : Nat.card ↥(⨆ H ∈ I, e4.map (ψ H)) = 4 ^ I.card := by
    rw [hF.card_iSup _ hA, Finset.prod_congr rfl (fun H hH => by
      rw [Subgroup.card_map_of_injective (hF.spec H hH).ψ_inj, card_e4]), Finset.prod_const]
  have hfixE : ∀ H ∈ I, commV H ⊓ fixV (⨆ H' ∈ I, e4.map (ψ H')) =
      commV H ⊓ fixV (e4.map (ψ H)) := by
    intro H hH
    refine le_antisymm (inf_le_inf_left _ (B1.fixV_le_fixV
      (le_iSup₂_of_le (f := fun H' (_ : H' ∈ I) => e4.map (ψ H')) H hH le_rfl))) ?_
    rintro v ⟨hv, hfv⟩
    refine ⟨hv, fun x hx => ?_⟩
    have : (⨆ H' ∈ I, e4.map (ψ H')) ≤ MulAction.stabilizer (MulAut V) v := by
      refine iSup₂_le fun H' hH' y hy => ?_
      rw [MulAction.mem_stabilizer_iff]
      by_cases hHH : H' = H
      · subst hHH
        exact hfv y hy
      · exact hF.hother H hH H' hH' hHH y (hA H' hH' hy) v hv
    exact this hx
  have hcardc : ∀ H ∈ I, Nat.card ↥(commV H ⊓ fixV (⨆ H' ∈ I, e4.map (ψ H'))) = 4 := by
    intro H hH
    rw [hfixE H hH, (hF.spec H hH).card_fix_map, card_fixΔ_e4]
  have hprod := card_fixV_prod hF.hother hF.hstab hF.hind0 hF.hsplit hEI
  rw [Finset.prod_congr rfl hcardc,
    Finset.prod_congr rfl (fun H hH => (hF.spec H hH).card_commV)] at hprod
  simp only [Finset.prod_const] at hprod
  have h16 : (16 : ℕ) ^ I.card = 4 ^ I.card * 4 ^ I.card := by
    rw [← mul_pow]
    norm_num
  rw [hEcard]
  have hpos : 0 < 4 ^ I.card := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc 4 ^ I.card * Nat.card ↥(fixV (⨆ H ∈ I, e4.map (ψ H))) * 4 ^ I.card =
        Nat.card ↥(fixV (⨆ H ∈ I, e4.map (ψ H))) * (4 ^ I.card * 4 ^ I.card) := by ring
    _ = Nat.card ↥(fixV (⨆ H ∈ I, e4.map (ψ H))) * 16 ^ I.card := by rw [h16]
    _ = Nat.card V * 4 ^ I.card := hprod.symm

omit [Finite V] in
theorem inf_E_le {H : Subgroup (MulAut V)} (hH : H ∈ I) :
    (⨆ H' ∈ I, e4.map (ψ H')) ⊓ H ≤ e4.map (ψ H) := by
  rintro x ⟨hxE, hxH⟩
  obtain ⟨a, ha, hxa⟩ := exists_restr hF.hother hF.hstab (A := fun H' => e4.map (ψ H'))
    (fun H' hH' => hF.map_le hH' _) hxE hH
  have : x = a := (hF.spec H hH).eq_of_act hxH (hF.map_le hH _ ha) hxa
  rw [this]
  exact ha

end SymFam

end Fam

end GE23

end CFSG.Quasithin
