module

public import CFSG.Milestones.ASVolI.A3Aut.Core

public section

namespace CFSG.ASVolI

open scoped Pointwise

section Core2

variable {A : Type} [Group A] [Finite A]

theorem burnsideAut_exists_complement {p : ℕ} [Fact p.Prime] {E Y : Subgroup A} (hEY : E ≤ Y)
    (hYE : Y ≤ Subgroup.normalizer (E : Set A)) (hE : IsPGroup p E) (hp : ¬ p ∣ E.relIndex Y) :
    ∃ C : Subgroup A, C ≤ Y ∧ E ⊓ C = ⊥ ∧ E ⊔ C = Y := by
  set N : Subgroup ↥Y := E.subgroupOf Y with hN
  haveI hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hEY).2 hYE
  have hNcard : Nat.card ↥N = Nat.card ↥E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv
  have hcop : Nat.Coprime (Nat.card ↥N) N.index := by
    rw [hNcard]
    obtain ⟨k, hk⟩ := hE.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hp)
  obtain ⟨C', hC'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨C'.map Y.subtype, Subgroup.map_subtype_le C', ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxE, ⟨c, hc, rfl⟩⟩
    have hcN : c ∈ N := Subgroup.mem_subgroupOf.2 hxE
    have : c ∈ N ⊓ C' := ⟨hcN, hc⟩
    rw [hC'.disjoint.eq_bot, Subgroup.mem_bot] at this
    rw [this]
    rfl
  · apply le_antisymm (sup_le hEY (Subgroup.map_subtype_le C'))
    intro y hy
    obtain ⟨⟨n, c⟩, hnc⟩ := hC'.2 ⟨y, hy⟩
    have hval : (n : ↥Y) * (c : ↥Y) = ⟨y, hy⟩ := hnc
    have hy' : y = ((n : ↥Y) : A) * ((c : ↥Y) : A) := by
      have := congrArg Subtype.val hval
      simpa using this.symm
    rw [hy']
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 n.2) ⟨c, c.2, rfl⟩

theorem burnsideAut_le_conj_complement {E Y C X : Subgroup A}
    (hYE : Y ≤ Subgroup.normalizer (E : Set A)) (hE : IsPGroup 2 E) (hCY : C ≤ Y)
    (hEC : E ⊓ C = ⊥) (hECY : E ⊔ C = Y) (hXY : X ≤ Y) (hXodd : Odd (Nat.card X)) :
    ∃ e ∈ E, X ≤ C.map (MulAut.conj e).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C₁ : Subgroup A := (E ⊔ X) ⊓ C with hC₁
  have hEY : E ≤ Y := hECY ▸ le_sup_left
  have hXE : X ≤ Subgroup.normalizer (E : Set A) := hXY.trans hYE
  have hCE : C ≤ Subgroup.normalizer (E : Set A) := hCY.trans hYE
  have hC₁E : C₁ ≤ Subgroup.normalizer (E : Set A) := inf_le_right.trans hCE
  have hsup : E ⊔ C₁ = E ⊔ X := by
    refine le_antisymm (sup_le le_sup_left inf_le_left) (sup_le le_sup_left ?_)
    intro x hx
    have hxY : x ∈ E ⊔ C := hECY ▸ hXY hx
    obtain ⟨e, he, c, hc, rfl⟩ := (burnsideAut_mem_sup_iff hCE).1 hxY
    have hcC₁ : c ∈ C₁ := by
      refine ⟨?_, hc⟩
      have : c = e⁻¹ * (e * c) := by group
      rw [this]
      exact (E ⊔ X).mul_mem (Subgroup.mem_sup_left (E.inv_mem he)) (Subgroup.mem_sup_right hx)
    exact Subgroup.mul_mem_sup he hcC₁
  have hdisjC₁ : Disjoint E C₁ := by
    rw [disjoint_iff, eq_bot_iff]
    intro x ⟨hxE, hxC₁⟩
    have : x ∈ E ⊓ C := ⟨hxE, hxC₁.2⟩
    rwa [hEC] at this
  have hdisjX : Disjoint E X := burnsideAut_disjoint_of_odd hE hXodd
  have hXp : ¬ 2 ∣ Nat.card X := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hXodd
  obtain ⟨e, he, hC₁e⟩ := burnsideAut_conj_of_complements (p := 2) hXE hC₁E hE hXp hdisjX hdisjC₁
    hsup
  refine ⟨e, he, ?_⟩
  rw [← hC₁e]
  exact Subgroup.map_mono inf_le_right

theorem burnsideAut_case5_core2 {Lb I J Φ Sb Bb : Subgroup A}
    (hSbLb : Sb ≤ Lb) (hLbI : Lb ≤ I) (hIJ : I ≤ J)
    (hΦI : Φ ≤ Subgroup.normalizer (I : Set A)) (hIΦ : I ⊓ Φ = ⊥)
    (hΦJ : Φ ≤ Subgroup.normalizer (J : Set A))
    (hΦS : Φ ≤ Subgroup.normalizer (Sb : Set A)) (hΦodd : Odd (Nat.card Φ))
    (hSb2 : IsPGroup 2 Sb) (hSbI : ¬ 2 ∣ Sb.relIndex (I ⊓ Subgroup.normalizer (Sb : Set A)))
    (hBΦ : Bb ≤ I ⊔ Φ) (hBS : Bb ≤ Subgroup.normalizer (Sb : Set A))
    (hBodd : Odd (Nat.card Bb)) :
    ∃ χ ∈ (I ⊔ Φ) ⊓ Subgroup.normalizer (Sb : Set A), ∃ F H : Subgroup A,
      F ≤ Φ.map (MulAut.conj χ).toMonoidHom ∧ Nat.card F ∣ Nat.card Bb ∧
      F ≤ Subgroup.normalizer (Sb : Set A) ∧ F ≤ Subgroup.normalizer (H : Set A) ∧
      CFSG.Quasithin.A315.IsCartan 2 Sb ((F ⊔ Bb ⊔ Lb) ⊓ J) H ∧
      F ⊔ Bb ⊔ Lb = H ⊔ Bb ⊔ Lb ∧ Bb ≤ F ⊔ H ∧
      ∀ x ∈ F, ∃ b ∈ Bb, x * b⁻¹ ∈ I := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSbI' : Sb ≤ I := hSbLb.trans hLbI
  have hIΦ' : ∀ {φ : A}, φ ∈ Φ → φ ∈ I → φ = 1 := fun {φ} hφ hφI => by
    have : φ ∈ I ⊓ Φ := ⟨hφI, hφ⟩
    rw [hIΦ] at this
    exact this
  have hIΦn : I ⊔ Φ ≤ Subgroup.normalizer (I : Set A) := sup_le Subgroup.le_normalizer hΦI
  set Y : Subgroup A := (I ⊔ Φ) ⊓ Subgroup.normalizer (Sb : Set A) with hY
  have hSbY : Sb ≤ Y := le_inf (hSbI'.trans le_sup_left) Subgroup.le_normalizer
  have hYN : Y ≤ Subgroup.normalizer (Sb : Set A) := inf_le_right
  have hΦY : Φ ≤ Y := le_inf le_sup_right hΦS
  have hBY : Bb ≤ Y := le_inf hBΦ hBS
  set NI : Subgroup A := I ⊓ Subgroup.normalizer (Sb : Set A) with hNI
  have hΦNI : Φ ≤ Subgroup.normalizer (NI : Set A) :=
    (le_inf hΦI (hΦS.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hNIY : NI ≤ Y := le_inf (inf_le_left.trans le_sup_left) inf_le_right
  have hYeq : Y = NI ⊔ Φ := by
    refine le_antisymm ?_ (sup_le hNIY hΦY)
    rintro y ⟨hyIΦ, hyN⟩
    obtain ⟨i, hi, φ, hφ, rfl⟩ := (burnsideAut_mem_sup_iff hΦI).1 hyIΦ
    have hiN : i ∈ Subgroup.normalizer (Sb : Set A) := by
      have : i = (i * φ) * φ⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hyN (Subgroup.inv_mem _ (hΦS hφ))
    exact Subgroup.mul_mem_sup ⟨hi, hiN⟩ hφ
  have hNIΦ : NI ⊓ Φ = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hx1, hx2⟩
    exact hIΦ' hx2 hx1.1
  have hcardY : Nat.card Y = Nat.card NI * Nat.card Φ := by
    rw [hYeq]
    exact burnsideAut_card_sup_of_le_normalizer hΦNI hNIΦ
  have hidxY : ¬ 2 ∣ Sb.relIndex Y := by
    have hSbNI : Sb ≤ NI := le_inf hSbI' Subgroup.le_normalizer
    have h1 := Subgroup.relIndex_mul_relIndex Sb NI Y hSbNI hNIY
    have h2 : NI.relIndex Y * Nat.card ↥(NI ⊓ Y) = Nat.card Y := Subgroup.relIndex_mul_card NI Y
    rw [inf_eq_left.2 hNIY, hcardY, mul_comm] at h2
    have hpos : 0 < Nat.card NI := Nat.card_pos
    have h3 : NI.relIndex Y = Nat.card Φ := Nat.eq_of_mul_eq_mul_left hpos (by rw [h2])
    rw [← h1, h3, Nat.Prime.dvd_mul Nat.prime_two]
    rintro (h | h)
    · exact hSbI h
    · exact (Nat.not_even_iff_odd.2 hΦodd) (even_iff_two_dvd.2 h)
  obtain ⟨C₀, hC₀Y, hC₀d, hC₀s⟩ := burnsideAut_exists_complement (p := 2) hSbY hYN hSb2 hidxY
  have hmapY : ∀ {e : A}, e ∈ Sb → Y.map (MulAut.conj e).toMonoidHom = Y := fun he =>
    burnsideAut_map_conj_self (hSbY he)
  have hmapSb : ∀ {e : A}, e ∈ Sb → Sb.map (MulAut.conj e).toMonoidHom = Sb := fun he =>
    burnsideAut_map_conj_self he
  have hconjC : ∀ {e : A} {C : Subgroup A}, e ∈ Sb → C ≤ Y → Sb ⊓ C = ⊥ → Sb ⊔ C = Y →
      C.map (MulAut.conj e).toMonoidHom ≤ Y ∧ Sb ⊓ C.map (MulAut.conj e).toMonoidHom = ⊥ ∧
        Sb ⊔ C.map (MulAut.conj e).toMonoidHom = Y := by
    intro e C he hCY hd hs
    have hinj : Function.Injective (MulAut.conj e).toMonoidHom := (MulAut.conj e).injective
    refine ⟨(hmapY he) ▸ Subgroup.map_mono hCY, ?_, ?_⟩
    · rw [← hmapSb he, ← Subgroup.map_inf _ _ _ hinj, hd, Subgroup.map_bot]
    · rw [← hmapSb he, ← Subgroup.map_sup, hs, hmapY he]
  obtain ⟨e₁, he₁, hΦC₁⟩ := burnsideAut_le_conj_complement hYN hSb2 hC₀Y hC₀d hC₀s hΦY hΦodd
  set C₁ : Subgroup A := C₀.map (MulAut.conj e₁).toMonoidHom with hC₁
  obtain ⟨hC₁Y, hC₁d, hC₁s⟩ := hconjC he₁ hC₀Y hC₀d hC₀s
  obtain ⟨e₂, he₂, hBC⟩ := burnsideAut_le_conj_complement hYN hSb2 hC₁Y hC₁d hC₁s hBY hBodd
  set C : Subgroup A := C₁.map (MulAut.conj e₂).toMonoidHom with hC
  obtain ⟨hCY, hCd, hCs⟩ := hconjC he₂ hC₁Y hC₁d hC₁s
  set Φ' : Subgroup A := Φ.map (MulAut.conj e₂).toMonoidHom with hΦ'
  have hΦ'C : Φ' ≤ C := Subgroup.map_mono hΦC₁
  set H₀ : Subgroup A := C ⊓ I with hH₀
  have he₂I : e₂ ∈ I := hSbI' he₂
  have he₂N : e₂ ∈ Subgroup.normalizer (Sb : Set A) := Subgroup.le_normalizer he₂
  have hΦ'I : Φ' ≤ Subgroup.normalizer (I : Set A) :=
    burnsideAut_map_conj_le_normalizer (Subgroup.le_normalizer he₂I) hΦI
  have hIΦ'' : I ⊓ Φ' = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxI, hxΦ⟩
    have h1 : e₂⁻¹ * x * e₂ ∈ Φ := burnsideAut_mem_map_conj.1 hxΦ
    have h2 : e₂⁻¹ * x * e₂ ∈ I := I.mul_mem (I.mul_mem (I.inv_mem he₂I) hxI) he₂I
    have h3 := hIΦ' h1 h2
    have : x = e₂ * (e₂⁻¹ * x * e₂) * e₂⁻¹ := by group
    rw [Subgroup.mem_bot, this, h3]
    group
  have hΦ'J : Φ' ≤ Subgroup.normalizer (J : Set A) :=
    burnsideAut_map_conj_le_normalizer (Subgroup.le_normalizer (hIJ he₂I)) hΦJ
  have hΦ'S : Φ' ≤ Subgroup.normalizer (Sb : Set A) :=
    burnsideAut_map_conj_le_normalizer he₂N hΦS
  have hCN : C ≤ Subgroup.normalizer (Sb : Set A) := hCY.trans hYN
  have hCodd : Odd (Nat.card C) := by
    have h1 : Nat.card Y = Nat.card Sb * Nat.card C := by
      rw [← hCs]
      exact burnsideAut_card_sup_of_le_normalizer hCN hCd
    have h2 : Sb.relIndex Y * Nat.card ↥(Sb ⊓ Y) = Nat.card Y := Subgroup.relIndex_mul_card Sb Y
    rw [inf_eq_left.2 hSbY, h1, mul_comm] at h2
    have hpos : 0 < Nat.card Sb := Nat.card_pos
    have h3 : Sb.relIndex Y = Nat.card C := Nat.eq_of_mul_eq_mul_left hpos h2
    rw [← h3, ← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hidxY
  have hNS : I ⊓ Subgroup.normalizer (Sb : Set A) = Sb ⊔ H₀ := by
    refine le_antisymm ?_ (sup_le (le_inf hSbI' Subgroup.le_normalizer)
      (le_inf inf_le_right (inf_le_left.trans hCN)))
    intro x hx
    have hxY : x ∈ Sb ⊔ C := hCs ▸ hNIY hx
    obtain ⟨s, hs, c, hc, rfl⟩ := (burnsideAut_mem_sup_iff hCN).1 hxY
    have hcI : c ∈ I := by
      have : c = s⁻¹ * (s * c) := by group
      rw [this]
      exact I.mul_mem (I.inv_mem (hSbI' hs)) hx.1
    exact Subgroup.mul_mem_sup hs ⟨hc, hcI⟩
  have hH₀I : H₀ ≤ I := inf_le_right
  have hH₀S : H₀ ≤ Subgroup.normalizer (Sb : Set A) := inf_le_left.trans hCN
  have hH₀odd : Odd (Nat.card H₀) := Odd.of_dvd_nat hCodd (Subgroup.card_dvd_of_le inf_le_left)
  have hΦ'H₀ : Φ' ≤ Subgroup.normalizer (H₀ : Set A) :=
    (le_inf (hΦ'C.trans Subgroup.le_normalizer) hΦ'I).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hIΦ_le : I ⊔ Φ ≤ I ⊔ Φ' := by
    refine sup_le le_sup_left ?_
    intro φ hφ
    have h1 : e₂ * φ * e₂⁻¹ ∈ Φ' := ⟨φ, hφ, rfl⟩
    have : φ = e₂⁻¹ * (e₂ * φ * e₂⁻¹) * e₂ := by group
    rw [this]
    exact (I ⊔ Φ').mul_mem ((I ⊔ Φ').mul_mem (Subgroup.mem_sup_left (I.inv_mem he₂I))
      (Subgroup.mem_sup_right h1)) (Subgroup.mem_sup_left he₂I)
  have hB : Bb ≤ H₀ ⊔ Φ' := by
    intro b hb
    obtain ⟨i, hi, φ, hφ, rfl⟩ := (burnsideAut_mem_sup_iff hΦ'I).1 (hIΦ_le (hBΦ hb))
    have hiC : i ∈ C := by
      have : i = (i * φ) * φ⁻¹ := by group
      rw [this]
      exact C.mul_mem (hBC hb) (C.inv_mem (hΦ'C hφ))
    exact Subgroup.mul_mem_sup ⟨hiC, hi⟩ hφ
  obtain ⟨F, H, hF, hrest⟩ := burnsideAut_case5_core_aux hSbLb hLbI hIJ hΦ'I hIΦ'' hΦ'J hΦ'S hNS
    hH₀I hH₀S hH₀odd hΦ'H₀ hSb2 hB hBodd
  exact ⟨e₂, hSbY he₂, F, H, hF, hrest⟩

end Core2

end CFSG.ASVolI
