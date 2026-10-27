module

public import CFSG.Quasithin.MS93.FFStatement
public import CFSG.Quasithin.Background.SmithB42HatA6Off

public section

namespace CFSG.Quasithin.MS93.S36E

open CFSG.Quasithin CFSG.QuasithinUnique

section Alt6

@[expose] def x4 : ↥(alternatingGroup (Fin 6)) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem x4_sq_ne_one : x4 ^ 2 ≠ 1 := by
  intro h
  have := congrArg (fun σ : ↥(alternatingGroup (Fin 6)) => (σ : Equiv.Perm (Fin 6)) 0) h
  revert this
  decide

theorem x4_pow_four : x4 ^ 4 = 1 := by
  apply Subtype.ext
  show (x4 : Equiv.Perm (Fin 6)) ^ 4 = 1
  decide

theorem not_elemAbelian_eight_alt6 {A : Subgroup ↥(alternatingGroup (Fin 6))}
    (hA : ∀ a ∈ A, a ^ 2 = 1) (hcard : Nat.card A = 8) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := fun a => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hA a a.2)⟩
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [H13.card_alternatingGroup_fin 6 (by norm_num)]
    decide
  have hidx : A.index = 45 := by
    have h := A.card_mul_index
    rw [hcard, h360] at h
    omega
  set P : Sylow 2 ↥(alternatingGroup (Fin 6)) := hA2.toSylow (by rw [hidx]; decide) with hP
  have hPA : (P : Subgroup ↥(alternatingGroup (Fin 6))) = A := rfl
  have hx : IsPGroup 2 ↥(Subgroup.zpowers x4) := by
    rintro ⟨y, n, rfl⟩
    refine ⟨2, Subtype.ext ?_⟩
    show (x4 ^ n) ^ 2 ^ 2 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show ((2 ^ 2 : ℕ) : ℤ) = 4 by norm_num,
      show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, x4_pow_four, one_zpow]
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(alternatingGroup (Fin 6)) Q P
  have hxQ : x4 ∈ (Q : Subgroup ↥(alternatingGroup (Fin 6))) := hQ (Subgroup.mem_zpowers x4)
  have hmem : g * x4 * g⁻¹ ∈ A := by
    rw [← hPA, ← hg]
    exact ⟨x4, hxQ, rfl⟩
  have h1 := hA _ hmem
  apply x4_sq_ne_one
  have e : (g * x4 * g⁻¹) ^ 2 = g * x4 ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
  rw [e] at h1
  have := congrArg (fun y => g⁻¹ * y * g) h1
  simpa [mul_assoc] using this

end Alt6

section Hat

variable {S : Type} [CommGroup S] [Finite S]

theorem false_of_hat (hS2 : ∀ s : S, s ^ 2 = 1) {X K E : Subgroup (MulAut S)}
    (hXK : X ≤ Subgroup.normalizer (K : Set (MulAut S))) (hEX : E ≤ X) (hE : IsElemAbelian2 E)
    (hcount : 2 * Nat.card S ≤ Nat.card E * Nat.card (fixV E)) (hE8 : Nat.card E ≤ 8)
    (hhat : FFCaseHatA6 K) : False := by
  obtain ⟨-, ⟨hq, hZ, ⟨e⟩⟩, hcardS, hirr⟩ := hhat
  have hperf : Group.IsPerfect ↥K := hq.1
  obtain ⟨z, hcen, h3, hfp⟩ := HatA6.exists_center_fpf hS2 hcardS hperf hZ e
  have hz1 : (z : MulAut S) ≠ 1 := by
    intro h1
    have hall : ∀ v : S, v = 1 := fun v => hfp v (by rw [h1]; rfl)
    have : Nat.card S = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    rw [hcardS] at this
    norm_num at this
  have hcomm : ∀ b ∈ E, b * (z : MulAut S) = (z : MulAut S) * b := by
    intro b hb
    rcases HatA6.conj_z_cases hcen h3 hz1 (hXK (hEX hb)) with h | h
    · exact h
    · exfalso
      have htz : ∀ v, b ((z : MulAut S) v) = (z : MulAut S) ((z : MulAut S) (b v)) := fun v =>
        congrArg (fun y : MulAut S => y v) h
      have hsq := HatA6.card_sq_le_of_semilinear hfp htz (U := ⊤) (fun _ _ => Subgroup.mem_top _)
      rw [Subgroup.card_top, hcardS] at hsq
      have hle : fixV E ≤ (⊤ : Subgroup S) ⊓ fixV (Subgroup.zpowers b) := by
        intro v hv
        refine ⟨Subgroup.mem_top v, fun y hy => ?_⟩
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact hv _ (E.zpow_mem hb n)
      have h1 := Subgroup.card_le_of_le hle
      have h8 : Nat.card ↥((⊤ : Subgroup S) ⊓ fixV (Subgroup.zpowers b)) ≤ 8 := by
        by_contra hlt
        push Not at hlt
        have : 9 ^ 2 ≤ Nat.card ↥((⊤ : Subgroup S) ⊓ fixV (Subgroup.zpowers b)) ^ 2 :=
          Nat.pow_le_pow_left hlt 2
        omega
      rw [hcardS] at hcount
      have := Nat.mul_le_mul hE8 (h1.trans h8)
      omega
  have hEK : E ≤ K := by
    intro b hb
    refine HatA6.mem_of_normalizes hS2 hcardS hperf hZ e
      (fun J hJ => ?_) (fun l => ?_) (fun k hk => ?_)
    · rcases hirr.2 J (fun a l hl => hJ a a.2 l hl) bot_le le_top with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact (Subgroup.mem_normalizer_iff.1 (hXK (hEX hb)) l)
    · rw [hcen] at hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      have hc : Commute b (z : MulAut S) := hcomm b hb
      simpa using (hc.zpow_right n).eq
  have hzC : ∀ s ∈ fixV E, (z : MulAut S) s ∈ fixV E := by
    intro s hs b hb
    have h1 := congrArg (fun y : MulAut S => y s) (hcomm b hb)
    simp only [MulAut.mul_apply] at h1
    rw [h1, hs b hb]
  have hmod := H13.card_mod_three_of_sub h3 hzC (fun s _ hs => hfp s hs)
  have hdvd : Nat.card (fixV E) ∣ 64 := by
    rw [← show Nat.card S = 64 by rw [hcardS]; norm_num]
    exact Subgroup.card_subgroup_dvd_card _
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot, one_mul] at hcount
    have := Subgroup.card_le_card_group (fixV (⊥ : Subgroup (MulAut S)))
    omega
  have hfix64 : Nat.card (fixV E) ≠ 64 := by
    intro h64
    have htop : fixV E = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h64, hcardS]; norm_num)
    apply hE1
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    exact MulEquiv.ext fun s => (show s ∈ fixV E from htop ▸ Subgroup.mem_top s) b hb
  have hcardE : Nat.card E = 8 := by
    rcases H13.card_cases_of_dvd hdvd hmod with h | h | h | h
    · rw [h, hcardS] at hcount; omega
    · rw [h, hcardS] at hcount; omega
    · rw [h, hcardS] at hcount; omega
    · exact absurd h hfix64
  set f : ↥K →* ↥(alternatingGroup (Fin 6)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)) with hf
  have hfi : ∀ a ∈ E.subgroupOf K, f a = 1 → a = 1 := by
    intro a ha h1
    have hz : a ∈ Subgroup.center ↥K := by
      have : (QuotientGroup.mk' (Subgroup.center ↥K)) a = 1 :=
        e.injective (by rw [map_one]; exact h1)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have ha2 : a ^ 2 = 1 := Subtype.ext (hE.2 _ (Subgroup.mem_subgroupOf.1 ha))
    have ha3 : a ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(Subgroup.center ↥K)) (x := ⟨a, hz⟩)
      rw [hZ] at this
      exact congrArg Subtype.val this
    have : a = a ^ 3 * (a ^ 2)⁻¹ := by group
    rw [this, ha2, ha3, inv_one, one_mul]
  set f' : ↥(E.subgroupOf K) →* ↥(alternatingGroup (Fin 6)) := f.comp (E.subgroupOf K).subtype
  have hinj : Function.Injective f' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    exact Subgroup.mem_bot.2 (Subtype.ext (hfi a a.2 ha))
  apply not_elemAbelian_eight_alt6 (A := f'.range)
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, show a ^ 2 = 1 from Subtype.ext (Subtype.ext
      (hE.2 _ (Subgroup.mem_subgroupOf.1 a.2))), map_one]
  · rw [← hcardE, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv

end Hat

end CFSG.Quasithin.MS93.S36E
