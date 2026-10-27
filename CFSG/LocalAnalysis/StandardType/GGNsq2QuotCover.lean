module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotAut
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.CoprimeKernel

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

@[expose] def Datum.fL (hD : Datum p N f L Bs Z) : ↥L →* ↥(img N f L) :=
  (f.comp (Subgroup.inclusion hD.LN)).codRestrict (img N f L)
    (fun l => mem_img.2 ⟨Subgroup.inclusion hD.LN l, l.2, rfl⟩)

theorem Datum.fL_surjective (hD : Datum p N f L Bs Z) : Function.Surjective hD.fL := by
  intro y
  obtain ⟨u, hu, hy⟩ := mem_img.1 y.2
  exact ⟨⟨(u : G), hu⟩, Subtype.ext hy⟩

theorem Datum.fL_eq_one_iff (hD : Datum p N f L Bs Z) (l : ↥L) : hD.fL l = 1 ↔ (l : G) ∈ Z := by
  constructor
  · intro h
    have h1 : f ⟨(l : G), hD.LN l.2⟩ = 1 := congrArg Subtype.val h
    exact (hD.mem_ker_iff _).1 h1
  · intro h
    apply Subtype.ext
    exact (hD.mem_ker_iff ⟨(l : G), hD.LN l.2⟩).2 h

theorem Datum.mem_center_of_mem (hD : Datum p N f L Bs Z) {l : ↥L} (hl : (l : G) ∈ Z) :
    l ∈ Subgroup.center ↥L := by
  rw [Subgroup.mem_center_iff]
  intro l'
  exact Subtype.ext (hD.Zcent _ hl _ l'.2)

variable {R : Type} [Group R]

theorem Datum.exists_eta (hD : Datum p N f L Bs Z) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) :
    ∃ η : ↥(img N f L) →* R, ∀ l : ↥L, η (hD.fL l) = θ (QuotientGroup.mk l) := by
  let g : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hker : hD.fL.ker ≤ g.ker := by
    intro l hl
    have hlZ : (l : G) ∈ Z := (hD.fL_eq_one_iff l).1 hl
    have hc : l ∈ Subgroup.center ↥L := hD.mem_center_of_mem hlZ
    rw [MonoidHom.mem_ker]
    change θ (QuotientGroup.mk l) = 1
    rw [(QuotientGroup.eq_one_iff l).2 hc, map_one]
  refine ⟨hD.fL.liftOfSurjective hD.fL_surjective ⟨g, hker⟩, fun l => ?_⟩
  exact MonoidHom.liftOfRightInverse_comp_apply hD.fL (Function.surjInv hD.fL_surjective)
    (Function.rightInverse_surjInv hD.fL_surjective) ⟨g, hker⟩ l

theorem Datum.eta_surjective (hD : Datum p N f L Bs Z) {θ : ↥L ⧸ Subgroup.center ↥L ≃* R}
    {η : ↥(img N f L) →* R} (hη : ∀ l : ↥L, η (hD.fL l) = θ (QuotientGroup.mk l)) :
    Function.Surjective η := by
  intro r
  obtain ⟨c, rfl⟩ := θ.surjective r
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨hD.fL l, hη l⟩

theorem Datum.eta_ker_le_center (hD : Datum p N f L Bs Z) {θ : ↥L ⧸ Subgroup.center ↥L ≃* R}
    {η : ↥(img N f L) →* R} (hη : ∀ l : ↥L, η (hD.fL l) = θ (QuotientGroup.mk l)) :
    η.ker ≤ Subgroup.center ↥(img N f L) := by
  intro y hy
  obtain ⟨l, rfl⟩ := hD.fL_surjective y
  rw [MonoidHom.mem_ker, hη l] at hy
  have hl : l ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff l).1 (θ.map_eq_one_iff.1 hy)
  rw [Subgroup.mem_center_iff] at hl ⊢
  intro y'
  obtain ⟨l', rfl⟩ := hD.fL_surjective y'
  rw [← map_mul, ← map_mul, hl l']

theorem Datum.eta_ker_coprime_four [Finite Q] (hD : Datum p N f L Bs Z)
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {η : ↥(img N f L) →* R}
    (hη : ∀ l : ↥L, η (hD.fL l) = θ (QuotientGroup.mk l))
    (hmax : ∀ l : ↥L, l ∈ Subgroup.center ↥L → (∃ k : ℕ, l ^ (2 ^ k) = 1) → (l : G) ∈ Z) :
    Nat.Coprime (Nat.card η.ker) 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : ¬ 2 ∣ Nat.card η.ker := by
    intro h2
    obtain ⟨y, hy2⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hy1 : (y : ↥(img N f L)) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one y
      rw [hy2] at h
      exact congrArg Subtype.val h
    obtain ⟨l, hl⟩ := hD.fL_surjective (y : ↥(img N f L))
    have hyker : η (y : ↥(img N f L)) = 1 := y.2
    rw [← hl, hη l] at hyker
    have hc : l ∈ Subgroup.center ↥L :=
      (QuotientGroup.eq_one_iff l).1 (θ.map_eq_one_iff.1 hyker)
    have hl2 : hD.fL (l ^ 2) = 1 := by rw [map_pow, hl]; exact hy1
    have hl2Z : ((l ^ 2 : ↥L) : G) ∈ Z := (hD.fL_eq_one_iff _).1 hl2
    obtain ⟨j, hj⟩ := hD.Z2 _ hl2Z
    have hlj : l ^ (2 ^ (j + 1)) = 1 := by
      apply Subtype.ext
      have h1 : ((l ^ 2 : ↥L) : G) ^ (2 ^ j) = 1 := hj
      have h2 : ((l : ↥L) : G) ^ (2 ^ (j + 1)) = 1 := by
        have : ((l : ↥L) : G) ^ (2 * 2 ^ j) = 1 := by
          rw [pow_mul]
          simpa using h1
        simpa [pow_succ, mul_comm] using this
      simpa using h2
    have hlZ : (l : G) ∈ Z := hmax l hc ⟨j + 1, hlj⟩
    have hy : (y : ↥(img N f L)) = 1 := by rw [← hl]; exact (hD.fL_eq_one_iff l).2 hlZ
    have hy' : y = 1 := Subtype.ext hy
    rw [hy', orderOf_one] at hy2
    omega
  have hcop : Nat.Coprime 2 (Nat.card η.ker) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnd
  have h4 : Nat.Coprime (2 ^ 2) (Nat.card η.ker) := Nat.Coprime.pow_left 2 hcop
  exact (Nat.coprime_comm.1 (by simpa using h4))

theorem Datum.eta_induces (hD : Datum p N f L Bs Z) {θ : ↥L ⧸ Subgroup.center ↥L ≃* R}
    {η : ↥(img N f L) →* R} (hη : ∀ l : ↥L, η (hD.fL l) = θ (QuotientGroup.mk l))
    (hBsL : Bs ≤ Subgroup.normalizer (L : Set G)) {b : G} (hb : b ∈ Bs) {φ : MulAut R}
    (hInd : LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∀ y y' : ↥(img N f L),
      (y' : Q) = (f ⟨b, hD.BsN hb⟩)⁻¹ * (y : Q) * f ⟨b, hD.BsN hb⟩ → φ (η y) = η y' := by
  intro y y' hyy
  obtain ⟨l, rfl⟩ := hD.fL_surjective y
  obtain ⟨l', rfl⟩ := hD.fL_surjective y'
  have hbL : ∀ h ∈ L, b⁻¹ * h * b ∈ L := fun h hh => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hBsL hb)) h).1 hh
    simpa using this
  let lb : ↥L := ⟨b⁻¹ * (l : G) * b, hbL _ l.2⟩
  have h1 : f ⟨(l' : G), hD.LN l'.2⟩ =
      (f ⟨b, hD.BsN hb⟩)⁻¹ * f ⟨(l : G), hD.LN l.2⟩ * f ⟨b, hD.BsN hb⟩ := hyy
  have h2 : f ⟨(lb : G), hD.LN lb.2⟩ =
      (f ⟨b, hD.BsN hb⟩)⁻¹ * f ⟨(l : G), hD.LN l.2⟩ * f ⟨b, hD.BsN hb⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext rfl)
  have hker : (⟨(l' : G), hD.LN l'.2⟩ : ↥N)⁻¹ * ⟨(lb : G), hD.LN lb.2⟩ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, h2, inv_mul_cancel]
  have hZ : ((l'⁻¹ * lb : ↥L) : G) ∈ Z := by
    have h := (hD.mem_ker_iff _).1 hker
    simpa using h
  have hc : l'⁻¹ * lb ∈ Subgroup.center ↥L := hD.mem_center_of_mem hZ
  have hmk : (QuotientGroup.mk l' : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk lb :=
    (QuotientGroup.eq).2 hc
  rw [hη l, hη l', hmk]
  exact hInd l lb rfl

end NsQuot

end CFSG.StandardType

end
