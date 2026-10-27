module

public import CFSG.Quasithin.Background.C116Three.L3Defs
import CFSG.Quasithin.EmptyFaithful.S1422Center
public import CFSG.Quasithin.EmptyFaithful.R3c23Core
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

theorem PairData.symm' {G₁ G₂ : Subgroup (MulAut V)} {W₁ W₂ C : Subgroup V}
    (P : PairData G₁ G₂ W₁ W₂ C) : PairData G₂ G₁ W₂ W₁ C where
  comm a ha b hb := (P.comm b hb a ha).symm
  inf_eq_bot := by rw [inf_comm]; exact P.inf_eq_bot
  sup_eq_top := by rw [sup_comm]; exact P.sup_eq_top
  inf_eq := by rw [inf_comm]; exact P.inf_eq
  fix_C g hg c hc := P.fix_C g (by rw [sup_comm]; exact hg) c hc
  inv₁ := P.inv₂
  inv₂ := P.inv₁
  triv₁ := P.triv₂
  triv₂ := P.triv₁

variable [Finite V]

theorem card_sup_mul_inf_of_comm {P : Type} [Group P] [Finite P] {H K : Subgroup P}
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K :=
  CFSG.Quasithin.card_sup_mul_card_inf_of_le_centralizer
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (hc x hx y hy).symm)

theorem card_sup_mul_inf_V (H K : Subgroup V) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K :=
  card_sup_mul_inf_of_comm fun x _ y _ => mul_comm x y

theorem le_projSub_sup {G₁ G₂ A : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hAG : A ≤ G₁ ⊔ G₂) :
    A ≤ R3c23.projSub G₁ G₂ A hcomm ⊔
      R3c23.projSub G₂ G₁ A (fun b hb a ha => (hcomm a ha b hb).symm) := by
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := R3c23.exists_decomp hcomm (hAG ha)
  refine Subgroup.mul_mem_sup (R3c23.mem_projSub.mpr ⟨hx, y, hy, ha⟩)
    (R3c23.mem_projSub.mpr ⟨hy, x, hx, ?_⟩)
  rw [← hcomm x hx y hy]
  exact ha

theorem card_sup_projSub {G₁ G₂ A : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hbot : G₁ ⊓ G₂ = ⊥) :
    Nat.card ↥(R3c23.projSub G₁ G₂ A hcomm ⊔
      R3c23.projSub G₂ G₁ A (fun b hb a ha => (hcomm a ha b hb).symm)) =
      Nat.card ↥(R3c23.projSub G₁ G₂ A hcomm) *
        Nat.card ↥(R3c23.projSub G₂ G₁ A (fun b hb a ha => (hcomm a ha b hb).symm)) := by
  have hle₁ := R3c23.projSub_le (G := G₁) (H := G₂) (A := A) hcomm
  have hle₂ := R3c23.projSub_le (G := G₂) (H := G₁) (A := A)
    (fun b hb a ha => (hcomm a ha b hb).symm)
  have hinf : R3c23.projSub G₁ G₂ A hcomm ⊓
      R3c23.projSub G₂ G₁ A (fun b hb a ha => (hcomm a ha b hb).symm) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf hle₁ hle₂).trans hbot.le)
  have h := card_sup_mul_inf_of_comm (H := R3c23.projSub G₁ G₂ A hcomm)
    (K := R3c23.projSub G₂ G₁ A (fun b hb a ha => (hcomm a ha b hb).symm))
    (fun x hx y hy => hcomm x (hle₁ hx) y (hle₂ hy))
  rw [hinf, Subgroup.card_bot, mul_one] at h
  exact h

theorem card_fixV_le {G₁ G₂ : Subgroup (MulAut V)} {W₁ W₂ C : Subgroup V}
    (P : PairData G₁ G₂ W₁ W₂ C) {A : Subgroup (MulAut V)} (hAG : A ≤ G₁ ⊔ G₂) :
    Nat.card ↥(fixV A) * Nat.card ↥C ≤ Nat.card ↥(fixV A ⊓ W₁) * Nat.card ↥(fixMod A W₂ C) := by
  have hYW : fixMod A W₂ C ⊓ W₁ = C := by
    apply le_antisymm
    · intro v hv
      rw [← P.inf_eq]
      exact ⟨hv.2, R3c23.fixMod_le hv.1⟩
    · exact le_inf (R3c23.le_fixMod P.le₂ fun b hb c hc => P.fix_C b (hAG hb) c hc) P.le₁
  have hF : fixV A ≤ fixMod A W₂ C ⊔ W₁ := by
    calc fixV A ≤ fixMod A W₁ C ⊔ fixMod A W₂ C := R3c23.fixV_le_sup_fixMod P hAG
      _ ≤ W₁ ⊔ fixMod A W₂ C := sup_le_sup_right R3c23.fixMod_le _
      _ = fixMod A W₂ C ⊔ W₁ := sup_comm _ _
  have hle : Nat.card ↥(fixV A ⊔ W₁) ≤ Nat.card ↥(fixMod A W₂ C ⊔ W₁) :=
    Subgroup.card_le_of_le (sup_le hF le_sup_right)
  have h1 := card_sup_mul_inf_V (fixV A) W₁
  have h2 := card_sup_mul_inf_V (fixMod A W₂ C) W₁
  rw [hYW] at h2
  have hpos : 0 < Nat.card W₁ := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card (fixV A) * Nat.card C * Nat.card W₁
      = Nat.card ↥(fixV A ⊔ W₁) * Nat.card ↥(fixV A ⊓ W₁) * Nat.card C := by rw [h1]; ring
    _ ≤ Nat.card ↥(fixMod A W₂ C ⊔ W₁) * Nat.card ↥(fixV A ⊓ W₁) * Nat.card C :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
    _ = Nat.card ↥(fixV A ⊓ W₁) * (Nat.card ↥(fixMod A W₂ C ⊔ W₁) * Nat.card C) := by ring
    _ = Nat.card ↥(fixV A ⊓ W₁) * (Nat.card (fixMod A W₂ C) * Nat.card W₁) := by rw [h2]
    _ = Nat.card ↥(fixV A ⊓ W₁) * Nat.card (fixMod A W₂ C) * Nat.card W₁ := by ring

theorem card_projSub_dichotomy {G₁ G₂ A : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hbot : G₁ ⊓ G₂ = ⊥) (hAG : A ≤ G₁ ⊔ G₂) :
    Nat.card A = Nat.card ↥(R3c23.projSub G₁ G₂ A hcomm) *
        Nat.card ↥(R3c23.projSub G₂ G₁ A fun b hb a ha => (hcomm a ha b hb).symm) ∨
      2 * Nat.card A ≤ Nat.card ↥(R3c23.projSub G₁ G₂ A hcomm) *
        Nat.card ↥(R3c23.projSub G₂ G₁ A fun b hb a ha => (hcomm a ha b hb).symm) := by
  have hdvd : Nat.card A ∣ Nat.card ↥(R3c23.projSub G₁ G₂ A hcomm ⊔
      R3c23.projSub G₂ G₁ A (fun b hb a ha => (hcomm a ha b hb).symm)) :=
    Subgroup.card_dvd_of_le (le_projSub_sup hcomm hAG)
  rw [card_sup_projSub hcomm hbot] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hp1 : 0 < Nat.card ↥(R3c23.projSub G₁ G₂ A hcomm) := Nat.card_pos
  have hp2 : 0 < Nat.card ↥(R3c23.projSub G₂ G₁ A (fun b hb a ha => (hcomm a ha b hb).symm)) :=
    Nat.card_pos
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · exfalso
      rw [mul_zero] at hk
      exact (Nat.mul_pos hp1 hp2).ne' hk
    · left
      rw [mul_one] at hk
      exact hk.symm
  · right
    rw [hk]
    exact (Nat.mul_le_mul_right (Nat.card ↥A) hk2).trans (le_of_eq (mul_comm _ _))

theorem card_fixV_direct {G₁ G₂ : Subgroup (MulAut V)} {W₁ W₂ C : Subgroup V}
    (P : PairData G₁ G₂ W₁ W₂ C) {A : Subgroup (MulAut V)} (hAG : A ≤ G₁ ⊔ G₂)
    (hdir : Nat.card A = Nat.card ↥(R3c23.projSub G₁ G₂ A P.comm) *
        Nat.card ↥(R3c23.projSub G₂ G₁ A fun b hb a ha => (P.comm a ha b hb).symm)) :
    Nat.card ↥(fixV A) * Nat.card ↥C ≤ Nat.card ↥(fixV A ⊓ W₁) * Nat.card ↥(fixV A ⊓ W₂) := by
  have hsup := card_sup_projSub (A := A) P.comm P.inf_eq_bot
  have hle₁ := R3c23.projSub_le (G := G₁) (H := G₂) (A := A) P.comm
  have hle₂ := R3c23.projSub_le (G := G₂) (H := G₁) (A := A)
    (fun b hb a ha => (P.comm a ha b hb).symm)
  have heq : A = R3c23.projSub G₁ G₂ A P.comm ⊔
      R3c23.projSub G₂ G₁ A (fun b hb a ha => (P.comm a ha b hb).symm) :=
    Subgroup.eq_of_le_of_card_ge (le_projSub_sup P.comm hAG) (le_of_eq (hsup.trans hdir.symm))
  have hA₁ : R3c23.projSub G₁ G₂ A P.comm ≤ A := le_sup_left.trans heq.symm.le
  have hA₂ : R3c23.projSub G₂ G₁ A (fun b hb a ha => (P.comm a ha b hb).symm) ≤ A :=
    le_sup_right.trans heq.symm.le
  have hF : fixV A ≤ (fixV A ⊓ W₁) ⊔ (fixV A ⊓ W₂) := by
    intro v hv
    have hv' : v ∈ W₁ ⊔ W₂ := by rw [P.sup_eq_top]; exact Subgroup.mem_top v
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.mp hv'
    have hfix : ∀ a ∈ A, a (w₁ * w₂) = w₁ * w₂ := fun a ha => mem_fixV.mp hv a ha
    have hxw₁ : ∀ x ∈ R3c23.projSub G₁ G₂ A P.comm, x w₁ = w₁ := by
      intro x hxA
      have h := hfix x (hA₁ hxA)
      rw [map_mul, P.triv₂ x (hle₁ hxA) w₂ hw₂] at h
      exact mul_right_cancel h
    have hyw₂ : ∀ y ∈ R3c23.projSub G₂ G₁ A (fun b hb a ha => (P.comm a ha b hb).symm),
        y w₂ = w₂ := by
      intro y hyA
      have h := hfix y (hA₂ hyA)
      rw [map_mul, P.triv₁ y (hle₂ hyA) w₁ hw₁] at h
      exact mul_left_cancel h
    have hw1 : w₁ ∈ fixV A := mem_fixV.mpr fun a ha => by
      obtain ⟨x, hxG, y, hyG, rfl⟩ := R3c23.exists_decomp P.comm (hAG ha)
      have hxA : x ∈ R3c23.projSub G₁ G₂ A P.comm := R3c23.mem_projSub.mpr ⟨hxG, y, hyG, ha⟩
      rw [MulAut.mul_apply, P.triv₁ y hyG w₁ hw₁]
      exact hxw₁ x hxA
    have hw2 : w₂ ∈ fixV A := mem_fixV.mpr fun a ha => by
      obtain ⟨x, hxG, y, hyG, rfl⟩ := R3c23.exists_decomp P.comm (hAG ha)
      have hyA : y ∈ R3c23.projSub G₂ G₁ A (fun b hb a ha => (P.comm a ha b hb).symm) :=
        R3c23.mem_projSub.mpr ⟨hyG, x, hxG, by rw [← P.comm x hxG y hyG]; exact ha⟩
      rw [MulAut.mul_apply, hyw₂ y hyA, P.triv₂ x hxG w₂ hw₂]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hw1, hw₁⟩) (Subgroup.mem_inf.mpr ⟨hw2, hw₂⟩)
  have hYW : (fixV A ⊓ W₁) ⊓ (fixV A ⊓ W₂) = C := by
    apply le_antisymm
    · intro v hv
      rw [← P.inf_eq]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hv.1).2, (Subgroup.mem_inf.mp hv.2).2⟩
    · intro c hc
      have hfc : c ∈ fixV A := mem_fixV.mpr fun a ha => P.fix_C a (hAG ha) c hc
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_inf.mpr ⟨hfc, P.le₁ hc⟩, Subgroup.mem_inf.mpr ⟨hfc, P.le₂ hc⟩⟩
  have h1 := card_sup_mul_inf_V (fixV A ⊓ W₁) (fixV A ⊓ W₂)
  rw [hYW] at h1
  have hle : Nat.card ↥(fixV A) ≤ Nat.card ↥((fixV A ⊓ W₁) ⊔ (fixV A ⊓ W₂)) :=
    Subgroup.card_le_of_le hF
  rw [← h1]
  exact Nat.mul_le_mul_right _ hle

theorem fixV_inf_projSub {G₁ G₂ : Subgroup (MulAut V)} {W₁ W₂ C : Subgroup V}
    (P : PairData G₁ G₂ W₁ W₂ C) {A : Subgroup (MulAut V)} (hAG : A ≤ G₁ ⊔ G₂) :
    fixV A ⊓ W₁ = fixV (R3c23.projSub G₁ G₂ A P.comm) ⊓ W₁ := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvA, hvW⟩ := Subgroup.mem_inf.mp hv
    refine Subgroup.mem_inf.mpr ⟨mem_fixV.mpr fun x hx => ?_, hvW⟩
    obtain ⟨hxG, y, hyG, hxy⟩ := R3c23.mem_projSub.mp hx
    have h1 := mem_fixV.mp hvA (x * y) hxy
    rw [MulAut.mul_apply, P.triv₁ y hyG v hvW] at h1
    exact h1
  · intro hv
    obtain ⟨hvA, hvW⟩ := Subgroup.mem_inf.mp hv
    refine Subgroup.mem_inf.mpr ⟨mem_fixV.mpr fun a ha => ?_, hvW⟩
    obtain ⟨x, hxG, y, hyG, rfl⟩ := R3c23.exists_decomp P.comm (hAG ha)
    have hxA : x ∈ R3c23.projSub G₁ G₂ A P.comm := R3c23.mem_projSub.mpr ⟨hxG, y, hyG, ha⟩
    rw [MulAut.mul_apply, P.triv₁ y hyG v hvW]
    exact mem_fixV.mp hvA x hxA

theorem nat_tight_aux {x y w₁ w₂ : ℕ} (hx : x ≤ w₁) (hy : y ≤ w₂) (h : w₁ * w₂ ≤ x * y)
    (h1 : 0 < w₁) (h2 : 0 < w₂) : x = w₁ := by
  by_contra hne
  have hlt : x < w₁ := lt_of_le_of_ne hx hne
  have h3 : x * y < w₁ * w₂ := by
    calc x * y ≤ x * w₂ := Nat.mul_le_mul_left x hy
      _ < w₁ * w₂ := Nat.mul_lt_mul_of_pos_right hlt h2
  omega

theorem offender_arith {a a₁ a₂ f c v w₁ w₂ z₁ z₂ y₁ y₂ : ℕ}
    (hc : 0 < c) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hVC : v * c = w₁ * w₂) (hcard : v ≤ a * f)
    (hE3 : f * c ≤ z₁ * y₂) (hE4 : f * c ≤ z₂ * y₁)
    (hdir : a = a₁ * a₂ → f * c ≤ z₁ * z₂) (hdich : a = a₁ * a₂ ∨ 2 * a ≤ a₁ * a₂)
    (hN1₁ : a₁ * z₁ ≤ w₁) (hN2₁ : a₁ ^ 2 * z₁ * y₁ ≤ w₁ ^ 2)
    (hN1₂ : a₂ * z₂ ≤ w₂) (hN2₂ : a₂ ^ 2 * z₂ * y₂ ≤ w₂ ^ 2) :
    a₁ * z₁ = w₁ := by
  have hX : w₁ * w₂ ≤ a * (f * c) := by
    calc w₁ * w₂ = v * c := hVC.symm
      _ ≤ (a * f) * c := Nat.mul_le_mul_right c hcard
      _ = a * (f * c) := Nat.mul_assoc a f c
  rcases hdich with hd | hd
  ·
    have h5 := hdir hd
    have h6 : w₁ * w₂ ≤ (a₁ * z₁) * (a₂ * z₂) := by
      calc w₁ * w₂ ≤ a * (f * c) := hX
        _ ≤ a * (z₁ * z₂) := Nat.mul_le_mul_left a h5
        _ = (a₁ * a₂) * (z₁ * z₂) := by rw [hd]
        _ = (a₁ * z₁) * (a₂ * z₂) := by ring
    exact nat_tight_aux hN1₁ hN1₂ h6 hw₁ hw₂
  ·
    exfalso
    have h1 : w₁ * w₂ ≤ a * (z₁ * y₂) := hX.trans (Nat.mul_le_mul_left a hE3)
    have h2 : w₁ * w₂ ≤ a * (z₂ * y₁) := hX.trans (Nat.mul_le_mul_left a hE4)
    have h3 : (w₁ * w₂) * (w₁ * w₂) ≤ (a * (z₁ * y₂)) * (a * (z₂ * y₁)) := Nat.mul_le_mul h1 h2
    have h4 : (2 * a) * (2 * a) ≤ (a₁ * a₂) * (a₁ * a₂) := Nat.mul_le_mul hd hd
    have h5 : 4 * ((w₁ * w₂) * (w₁ * w₂)) ≤ ((a₁ * a₂) * (a₁ * a₂)) * (z₁ * y₁ * (z₂ * y₂)) := by
      calc 4 * ((w₁ * w₂) * (w₁ * w₂)) ≤ 4 * ((a * (z₁ * y₂)) * (a * (z₂ * y₁))) :=
            Nat.mul_le_mul_left 4 h3
        _ = ((2 * a) * (2 * a)) * (z₁ * y₁ * (z₂ * y₂)) := by ring
        _ ≤ ((a₁ * a₂) * (a₁ * a₂)) * (z₁ * y₁ * (z₂ * y₂)) :=
            Nat.mul_le_mul_right _ h4
    have h6 : ((a₁ * a₂) * (a₁ * a₂)) * (z₁ * y₁ * (z₂ * y₂)) ≤ (w₁ ^ 2) * (w₂ ^ 2) := by
      calc ((a₁ * a₂) * (a₁ * a₂)) * (z₁ * y₁ * (z₂ * y₂))
          = (a₁ ^ 2 * z₁ * y₁) * (a₂ ^ 2 * z₂ * y₂) := by ring
        _ ≤ (w₁ ^ 2) * (w₂ ^ 2) := Nat.mul_le_mul hN2₁ hN2₂
    have h7 : 4 * ((w₁ * w₂) * (w₁ * w₂)) ≤ (w₁ * w₂) * (w₁ * w₂) := by
      calc 4 * ((w₁ * w₂) * (w₁ * w₂)) ≤ (w₁ ^ 2) * (w₂ ^ 2) := h5.trans h6
        _ = (w₁ * w₂) * (w₁ * w₂) := by ring
    have hpos : 0 < (w₁ * w₂) * (w₁ * w₂) := Nat.mul_pos (Nat.mul_pos hw₁ hw₂) (Nat.mul_pos hw₁ hw₂)
    omega

theorem offender_tight {G₁ G₂ : Subgroup (MulAut V)} {W₁ W₂ C : Subgroup V}
    (P : PairData G₁ G₂ W₁ W₂ C) (b₁ : Bounds G₁ W₁ C) (b₂ : Bounds G₂ W₂ C)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G₁ ⊔ G₂) (hAel : IsElemAbelian2 A)
    (hcard : Nat.card V ≤ Nat.card A * Nat.card ↥(fixV A)) :
    Nat.card ↥(R3c23.projSub G₁ G₂ A P.comm) * Nat.card ↥(fixV (R3c23.projSub G₁ G₂ A P.comm) ⊓ W₁) =
      Nat.card W₁ := by
  have P' := PairData.symm' P
  have hAG' : A ≤ G₂ ⊔ G₁ := hAG.trans (sup_comm G₁ G₂).le
  have hbot' : G₂ ⊓ G₁ = ⊥ := by rw [inf_comm]; exact P.inf_eq_bot
  have hA₁el : IsElemAbelian2 (R3c23.projSub G₁ G₂ A P.comm) :=
    R3c23.isElemAbelian2_projSub P.comm P.inf_eq_bot hAel
  have hA₂el : IsElemAbelian2 (R3c23.projSub G₂ G₁ A P'.comm) :=
    R3c23.isElemAbelian2_projSub P'.comm hbot' hAel
  obtain ⟨hB₁, hB₁'⟩ := b₁ _ (R3c23.projSub_le P.comm) hA₁el
  obtain ⟨hB₂, hB₂'⟩ := b₂ _ (R3c23.projSub_le P'.comm) hA₂el
  have hF₁ := fixV_inf_projSub P hAG
  have hF₂ := fixV_inf_projSub P' hAG'
  have hY₁ : fixMod A W₁ C = fixMod (R3c23.projSub G₁ G₂ A P.comm) W₁ C :=
    R3c23.fixMod_projSub P.comm hAG P.triv₁
  have hY₂ : fixMod A W₂ C = fixMod (R3c23.projSub G₂ G₁ A P'.comm) W₂ C :=
    R3c23.fixMod_projSub P'.comm hAG' P'.triv₁
  have hE3 := card_fixV_le P hAG
  have hE4 := card_fixV_le P' hAG'
  rw [hF₁, hY₂] at hE3
  rw [hF₂, hY₁] at hE4
  have hVC : Nat.card V * Nat.card ↥C = Nat.card W₁ * Nat.card W₂ := by
    have h := card_sup_mul_card_inf W₁ W₂
    rw [P.sup_eq_top, P.inf_eq, Subgroup.card_top] at h
    exact h
  have hdich : Nat.card A = Nat.card ↥(R3c23.projSub G₁ G₂ A P.comm) *
        Nat.card ↥(R3c23.projSub G₂ G₁ A P'.comm) ∨
      2 * Nat.card A ≤ Nat.card ↥(R3c23.projSub G₁ G₂ A P.comm) *
        Nat.card ↥(R3c23.projSub G₂ G₁ A P'.comm) :=
    card_projSub_dichotomy P.comm P.inf_eq_bot hAG
  have hdir : Nat.card A = Nat.card ↥(R3c23.projSub G₁ G₂ A P.comm) *
        Nat.card ↥(R3c23.projSub G₂ G₁ A P'.comm) →
      Nat.card ↥(fixV A) * Nat.card ↥C ≤
        Nat.card ↥(fixV (R3c23.projSub G₁ G₂ A P.comm) ⊓ W₁) *
          Nat.card ↥(fixV (R3c23.projSub G₂ G₁ A P'.comm) ⊓ W₂) := by
    intro hd
    have h := card_fixV_direct P hAG hd
    rwa [hF₁, hF₂] at h
  exact offender_arith Nat.card_pos (Nat.card_pos) (Nat.card_pos) hVC hcard hE3 hE4 hdir hdich
    hB₁ hB₁' hB₂ hB₂'

end CFSG.Quasithin.C116Three
