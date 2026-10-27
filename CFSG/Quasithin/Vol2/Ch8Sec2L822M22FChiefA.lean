module

public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.H13.M22F

section Abstract

variable {A : Type} [CommGroup A]

@[expose] def NormalA_m22f (σ : A →* A) (S : Subgroup A) : Prop := ∀ x ∈ S, σ x ∈ S

@[expose] def ChiefStepA_m22f (σ : A →* A) (L N : Subgroup A) : Prop :=
  NormalA_m22f σ N ∧ NormalA_m22f σ L ∧ L < N ∧ ∀ K : Subgroup A, NormalA_m22f σ K → L ≤ K → K ≤ N → K = L ∨ K = N

@[expose] def CentralA_m22f (σ : A →* A) (L N : Subgroup A) : Prop := ∀ x ∈ N, σ x * x⁻¹ ∈ L

inductive ChiefA_m22f (σ : A →* A) : Subgroup A → ℕ → Prop
  | bot : ChiefA_m22f σ ⊥ 0
  | central {N L : Subgroup A} {n : ℕ} :
      ChiefStepA_m22f σ L N → CentralA_m22f σ L N → ChiefA_m22f σ L n → ChiefA_m22f σ N n
  | noncentral {N L : Subgroup A} {n : ℕ} :
      ChiefStepA_m22f σ L N → ¬ CentralA_m22f σ L N → ChiefA_m22f σ L n → ChiefA_m22f σ N (n + 1)

@[expose] def psiA_m22f (σ : A →* A) : A →* A :=
  MonoidHom.mk' (fun x => σ x * x⁻¹) (fun a b => by
    simp only [map_mul, mul_inv]
    ac_rfl)

theorem psiA_apply_m22f (σ : A →* A) (x : A) : psiA_m22f σ x = σ x * x⁻¹ := rfl

@[expose] def imgA_m22f (σ : A →* A) (N : Subgroup A) : Subgroup A :=
  ((psiA_m22f σ).comp N.subtype).range

@[expose] def kerA_m22f (σ : A →* A) (N : Subgroup A) : Subgroup N :=
  ((psiA_m22f σ).comp N.subtype).ker

theorem card_imgA_mul_kerA_m22f [Finite A] (σ : A →* A) (N : Subgroup A) :
    Nat.card (imgA_m22f σ N) * Nat.card (kerA_m22f σ N) = Nat.card N := by
  rw [mul_comm]
  exact Subgroup.card_ker_mul_card_range ((psiA_m22f σ).comp N.subtype)

theorem imgA_mono_m22f (σ : A →* A) {L N : Subgroup A} (h : L ≤ N) : imgA_m22f σ L ≤ imgA_m22f σ N := by
  rintro w ⟨⟨x, hx⟩, rfl⟩
  exact ⟨⟨x, h hx⟩, rfl⟩

theorem imgA_eq_of_central_m22f {σ : A →* A} (h3 : ∀ a : A, σ (σ (σ a)) = a) (hexp : ∀ a : A, a ^ 2 = 1)
    {L N : Subgroup A} (hLN : L ≤ N) (hL : NormalA_m22f σ L) (hc : CentralA_m22f σ L N) :
    imgA_m22f σ N = imgA_m22f σ L := by
  refine le_antisymm ?_ (imgA_mono_m22f σ hLN)
  intro w hw
  obtain ⟨⟨x, hx⟩, rfl⟩ := MonoidHom.mem_range.mp hw
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : A, ℓ = σ x * x⁻¹ := ⟨_, rfl⟩
  have hℓL : ℓ ∈ L := by rw [hℓdef]; exact hc x hx
  have hℓ' : σ ℓ ∈ L := hL ℓ hℓL
  have hσx : σ x = ℓ * x := by rw [hℓdef]; group
  have hl2 : ℓ * ℓ = 1 := by simpa [sq] using hexp ℓ
  have hx2 : x * x = 1 := by simpa [sq] using hexp x
  have h1 : σ (σ x) = σ ℓ * (ℓ * x) := by rw [hσx, map_mul, hσx]
  have hcx : x * σ x * σ (σ x) = x * σ ℓ := by
    rw [h1, hσx]
    calc x * (ℓ * x) * (σ ℓ * (ℓ * x)) = (x * x) * (ℓ * ℓ) * (x * σ ℓ) := by ac_rfl
      _ = x * σ ℓ := by rw [hx2, hl2, one_mul, one_mul]
  have hσc : σ (x * σ x * σ (σ x)) = x * σ x * σ (σ x) := by
    simp only [map_mul]
    rw [h3 x]
    ac_rfl
  have hψc : psiA_m22f σ (x * σ ℓ) = 1 := by
    rw [psiA_apply_m22f, ← hcx, hσc, mul_inv_cancel]
  have hψx : psiA_m22f σ x = ℓ := hℓdef.symm
  refine MonoidHom.mem_range.mpr ⟨⟨(σ ℓ)⁻¹, L.inv_mem hℓ'⟩, ?_⟩
  show psiA_m22f σ (σ ℓ)⁻¹ = psiA_m22f σ x
  have hx_eq : x = (x * σ ℓ) * (σ ℓ)⁻¹ := by group
  rw [hx_eq, map_mul, hψc, one_mul]

theorem card_le_four_mul_of_noncentral_m22f [Finite A] {σ : A →* A} (h3 : ∀ a : A, σ (σ (σ a)) = a)
    (hexp : ∀ a : A, a ^ 2 = 1) {L N : Subgroup A} (hstep : ChiefStepA_m22f σ L N)
    (hnc : ¬ CentralA_m22f σ L N) : Nat.card N ≤ 4 * Nat.card L := by
  obtain ⟨hN, hL, hLN, hmax⟩ := hstep
  have hLN' : L ≤ N := hLN.le
  set C : Subgroup A := L.comap (psiA_m22f σ) ⊓ N with hCdef
  have hCN : C ≤ N := inf_le_right
  have hLC : L ≤ C := by
    intro l hl
    refine ⟨Subgroup.mem_comap.mpr ?_, hLN' hl⟩
    rw [psiA_apply_m22f]
    exact L.mul_mem (hL l hl) (L.inv_mem hl)
  have hCnorm : NormalA_m22f σ C := by
    rintro x ⟨hxL, hxN⟩
    refine ⟨Subgroup.mem_comap.mpr ?_, hN x hxN⟩
    have hxL' : psiA_m22f σ x ∈ L := Subgroup.mem_comap.mp hxL
    rw [psiA_apply_m22f] at hxL'
    rw [psiA_apply_m22f]
    have e : σ (σ x) * (σ x)⁻¹ = σ (σ x * x⁻¹) := by rw [map_mul, map_inv]
    rw [e]
    exact hL _ hxL'
  have hCeq : C = L := by
    rcases hmax C hCnorm hLC hCN with h | h
    · exact h
    · exfalso
      apply hnc
      intro x hx
      have hxC : x ∈ C := by rw [h]; exact hx
      exact Subgroup.mem_comap.mp hxC.1
  have hF2 : ∀ x ∈ N, x * σ x * σ (σ x) ∈ L := by
    intro x hx
    have hcN : x * σ x * σ (σ x) ∈ N :=
      N.mul_mem (N.mul_mem hx (hN x hx)) (hN _ (hN x hx))
    have hσc : σ (x * σ x * σ (σ x)) = x * σ x * σ (σ x) := by
      simp only [map_mul]
      rw [h3 x]
      ac_rfl
    have hψ : psiA_m22f σ (x * σ x * σ (σ x)) = 1 := by
      rw [psiA_apply_m22f, hσc, mul_inv_cancel]
    have hmemC : x * σ x * σ (σ x) ∈ C := by
      refine ⟨Subgroup.mem_comap.mpr ?_, hcN⟩
      rw [hψ]
      exact L.one_mem
    rw [hCeq] at hmemC
    exact hmemC
  obtain ⟨v, hvN, hvL⟩ := SetLike.exists_of_lt hLN
  set w : A := σ v with hwdef
  have hwN : w ∈ N := hN v hvN
  set S : Subgroup A := (L ⊔ Subgroup.zpowers v) ⊔ Subgroup.zpowers w with hSdef
  have hLS : L ≤ S := fun l hl => Subgroup.mem_sup_left (Subgroup.mem_sup_left hl)
  have hvS : v ∈ S := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  have hwS : w ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hw2S : σ w ∈ S := by
    have e : σ w = (v * w)⁻¹ * (v * w * σ w) := (inv_mul_cancel_left (v * w) (σ w)).symm
    rw [e]
    refine S.mul_mem (S.inv_mem (S.mul_mem hvS hwS)) (hLS ?_)
    exact hF2 v hvN
  have hSσ : NormalA_m22f σ S := by
    have hle : S ≤ S.comap σ := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro l hl
        exact Subgroup.mem_comap.mpr (hLS (hL l hl))
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_comap.mpr hwS
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_comap.mpr hw2S
    intro x hx
    exact Subgroup.mem_comap.mp (hle hx)
  have hSN : S ≤ N :=
    sup_le (sup_le hLN' (Subgroup.zpowers_le.mpr hvN)) (Subgroup.zpowers_le.mpr hwN)
  have hSne : S ≠ L := fun h => hvL (h ▸ hvS)
  have hSeq : S = N := (hmax S hSσ hLS hSN).resolve_left hSne
  have hsurj : Function.Surjective (fun p : ↥L × ↥(Subgroup.zpowers v) × ↥(Subgroup.zpowers w) =>
      (⟨p.1.1 * p.2.1.1 * p.2.2.1, N.mul_mem (N.mul_mem (hLN' p.1.2)
        (Subgroup.zpowers_le.mpr hvN p.2.1.2)) (Subgroup.zpowers_le.mpr hwN p.2.2.2)⟩ : ↥N)) := by
    intro x
    have hxS : (x : A) ∈ S := by rw [hSeq]; exact x.2
    obtain ⟨p, hp, q, hq, hpq⟩ := Subgroup.mem_sup.mp hxS
    obtain ⟨l, hl, r, hr, hlr⟩ := Subgroup.mem_sup.mp hp
    refine ⟨(⟨l, hl⟩, ⟨r, hr⟩, ⟨q, hq⟩), ?_⟩
    apply Subtype.ext
    show l * r * q = (x : A)
    rw [hlr]
    exact hpq
  have hcardle : Nat.card N ≤ Nat.card (↥L × ↥(Subgroup.zpowers v) × ↥(Subgroup.zpowers w)) :=
    Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_prod] at hcardle
  have hv2 : Nat.card (Subgroup.zpowers v) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (hexp v)
  have hw2 : Nat.card (Subgroup.zpowers w) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (hexp w)
  calc Nat.card N ≤ Nat.card L * (Nat.card (Subgroup.zpowers v) * Nat.card (Subgroup.zpowers w)) := hcardle
    _ ≤ Nat.card L * (2 * 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hv2 hw2)
    _ = 4 * Nat.card L := by ring

theorem card_imgA_le_four_mul_m22f [Finite A] {σ : A →* A} (h3 : ∀ a : A, σ (σ (σ a)) = a)
    (hexp : ∀ a : A, a ^ 2 = 1) {L N : Subgroup A} (hstep : ChiefStepA_m22f σ L N)
    (hnc : ¬ CentralA_m22f σ L N) : Nat.card (imgA_m22f σ N) ≤ 4 * Nat.card (imgA_m22f σ L) := by
  have eN := card_imgA_mul_kerA_m22f σ N
  have eL := card_imgA_mul_kerA_m22f σ L
  have hcard := card_le_four_mul_of_noncentral_m22f h3 hexp hstep hnc
  have hLN : L ≤ N := hstep.2.2.1.le
  have hmap : ∀ x : kerA_m22f σ L, (⟨x.1.1, hLN x.1.2⟩ : ↥N) ∈ kerA_m22f σ N := by
    intro x
    have hx : psiA_m22f σ x.1.1 = 1 := MonoidHom.mem_ker.mp x.2
    exact MonoidHom.mem_ker.mpr hx
  have hkle : Nat.card (kerA_m22f σ L) ≤ Nat.card (kerA_m22f σ N) := by
    refine Nat.card_le_card_of_injective
      (fun x : kerA_m22f σ L => (⟨⟨x.1.1, hLN x.1.2⟩, hmap x⟩ : ↥(kerA_m22f σ N))) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(kerA_m22f σ N) => z.1.1) hab
  have hpos : 0 < Nat.card (kerA_m22f σ N) := Nat.card_pos
  have key : Nat.card (imgA_m22f σ N) * Nat.card (kerA_m22f σ N) ≤
      (4 * Nat.card (imgA_m22f σ L)) * Nat.card (kerA_m22f σ N) := by
    calc Nat.card (imgA_m22f σ N) * Nat.card (kerA_m22f σ N) = Nat.card N := eN
      _ ≤ 4 * Nat.card L := hcard
      _ = 4 * (Nat.card (imgA_m22f σ L) * Nat.card (kerA_m22f σ L)) := by rw [eL]
      _ = (4 * Nat.card (imgA_m22f σ L)) * Nat.card (kerA_m22f σ L) := by ring
      _ ≤ (4 * Nat.card (imgA_m22f σ L)) * Nat.card (kerA_m22f σ N) := Nat.mul_le_mul_left _ hkle
  exact Nat.le_of_mul_le_mul_right key hpos

theorem card_imgA_le_pow_of_chief_m22f [Finite A] {σ : A →* A} (h3 : ∀ a : A, σ (σ (σ a)) = a)
    (hexp : ∀ a : A, a ^ 2 = 1) {N : Subgroup A} {k : ℕ} (h : ChiefA_m22f σ N k) :
    Nat.card (imgA_m22f σ N) ≤ 4 ^ k := by
  induction h with
  | bot =>
    have h1 := card_imgA_mul_kerA_m22f σ (⊥ : Subgroup A)
    rw [Subgroup.card_bot] at h1
    have hd : Nat.card (imgA_m22f σ ⊥) ∣ 1 := Dvd.intro _ h1
    simpa using Nat.le_of_dvd one_pos hd
  | central hstep hc _ ih =>
    rw [imgA_eq_of_central_m22f h3 hexp hstep.2.2.1.le hstep.2.1 hc]
    exact ih
  | noncentral hstep hnc _ ih =>
    have h4 := card_imgA_le_four_mul_m22f h3 hexp hstep hnc
    rw [pow_succ]
    linarith [h4, ih]

end Abstract

end CFSG.Quasithin.H13.M22F
