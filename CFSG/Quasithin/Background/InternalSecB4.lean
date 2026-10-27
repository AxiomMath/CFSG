module

public import CFSG.Quasithin.Background.InternalSecBasic
public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.InternalSecIrr
public import CFSG.Quasithin.Background.InternalSecTwo

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.QuasithinUnique.Bridge

namespace QSec

variable {V : Type} [CommGroup V] {X K : Subgroup (MulAut V)} {C : Subgroup V}
  (h : QSec X K C)

include h

theorem stabX : X ≤ stabSub ⊤ ⊓ stabSub C := fun _ hx => ⟨mem_stabSub_top _, h.stab hx⟩

theorem stabKC : K ≤ stabSub C := fun _ hk => h.stab (h.le hk)

theorem stabK : K ≤ stabSub ⊤ ⊓ stabSub C := fun _ hk => h.stabX (h.le hk)

theorem commute_of_mem_centSec {x : MulAut V} (hx : x ∈ X) (hxs : x ∈ centSec ⊤ C) :
    ∀ k ∈ K, x * k = k * x := by
  intro k hk
  have hc : x * k * x⁻¹ * k⁻¹ ∈ K := K.mul_mem (h.normal x hx k hk) (K.inv_mem hk)
  have hcs : x * k * x⁻¹ * k⁻¹ ∈ centSec ⊤ C := by
    have h1 : k * x⁻¹ * k⁻¹ ∈ centSec ⊤ C :=
      SecHyp.conj_mem_centSec (h.stabK hk) ((centSec ⊤ C).inv_mem hxs)
    have e : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
    rw [e]
    exact (centSec ⊤ C).mul_mem hxs h1
  have h1 : x * k * x⁻¹ * k⁻¹ ∈ K ⊓ centSec ⊤ C := ⟨hc, hcs⟩
  rw [h.faithful, Subgroup.mem_bot] at h1
  calc x * k = (x * k * x⁻¹ * k⁻¹) * (k * x) := by group
    _ = k * x := by rw [h1, one_mul]

theorem inf_centSec_eq_bot : X ⊓ centSec ⊤ C = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxs⟩
  have hcomm := h.commute_of_mem_centSec hx hxs
  have hfixgen : ∀ k ∈ K, ∀ v : V, x (k v * v⁻¹) = k v * v⁻¹ := by
    intro k hk v
    set c := x v * v⁻¹ with hc
    have hcC : c ∈ C := hxs.2 v trivial
    have hkc : k c = c := h.fix hcC k hk
    have hxv : x v = c * v := by rw [hc, inv_mul_cancel_right]
    have hxk : x (k v) = k (x v) := by
      have := congrArg (fun φ : MulAut V => φ v) (hcomm k hk)
      simpa [MulAut.mul_apply] using this
    rw [map_mul, map_inv, hxk, hxv, map_mul, hkc, ← div_eq_mul_inv, ← div_eq_mul_inv,
      mul_div_mul_left_eq_div]
  let D : Subgroup V :=
    { carrier := {v | x v = v}
      one_mem' := map_one x
      mul_mem' := fun {a b} ha hb => by
        show x (a * b) = a * b
        rw [map_mul, show x a = a from ha, show x b = b from hb]
      inv_mem' := fun {a} ha => by
        show x a⁻¹ = a⁻¹
        rw [map_inv, show x a = a from ha] }
  have hD : commV K ≤ D := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨k, hk, v, rfl⟩
    exact hfixgen k hk v
  rw [h.comm] at hD
  rw [Subgroup.mem_bot]
  ext v
  exact hD (Subgroup.mem_top v)

theorem le_autSec : autSec K ⊤ C ≤ autSec X ⊤ C := autSec_mono h.le ⊤ C

theorem normal_autSec :
    ∀ y ∈ autSec X ⊤ C, ∀ l ∈ autSec K ⊤ C, y * l * y⁻¹ ∈ autSec K ⊤ C := by
  intro y hy l hl
  obtain ⟨g, hgX, rfl⟩ := (mem_autSec_iff_secHom h.stabX).1 hy
  obtain ⟨k, hkK, rfl⟩ := (mem_autSec_iff_secHom h.stabK).1 hl
  rw [← map_inv, ← map_mul, ← map_mul]
  exact secHom_mem_autSec h.stabK (g := g * k * g⁻¹) (h.normal _ hgX _ hkK)

theorem two_autSec : ∀ y ∈ autSec X ⊤ C, ∃ e : ℕ, y ^ 2 ^ e ∈ autSec K ⊤ C := by
  intro y hy
  obtain ⟨g, hgX, rfl⟩ := (mem_autSec_iff_secHom h.stabX).1 hy
  obtain ⟨e, he⟩ := h.two _ hgX
  refine ⟨e, ?_⟩
  rw [← map_pow]
  exact secHom_mem_autSec h.stabK (g := g ^ 2 ^ e) he

theorem isQuasisimple_autSec : CFSG.IsQuasisimple ↥(autSec K ⊤ C) :=
  B5.isQuasisimple_autSec (le_stabSub_top K) h.stabKC h.faithful h.quasi

theorem isIrrSec_autSec : XMod.IsIrrSec ↥(autSec K ⊤ C) (⊥ : Subgroup (Sec ⊤ C)) ⊤ :=
  B5.isIrrSec_autSec h.lt (fun J hJ hCJ _ => h.irr J hCJ hJ) (le_stabSub_top K) h.stabKC

theorem exists_noncomm_autSec : ∃ a b : ↥(autSec K ⊤ C), a * b ≠ b * a :=
  exists_noncomm_of_isQuasisimple h.isQuasisimple_autSec

theorem pCoreOf_autSec_eq_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1) :
    pCoreOf 2 (autSec X ⊤ C) = ⊥ := by
  have hq := B1Red.isQuasisimple_to_open h.isQuasisimple_autSec
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (autSec X ⊤ C)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (autSec X ⊤ C)
  have hQle : pCoreOf 2 (autSec X ⊤ C) ≤ autSec X ⊤ C :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hnot : ¬ autSec K ⊤ C ≤ pCoreOf 2 (autSec X ⊤ C) := by
    intro hle
    have hnil := (hQ2.to_le hle).isNilpotent
    have : Group.IsPerfect ↥(autSec K ⊤ C) := ⟨hq.1⟩
    have : Nontrivial ↥(autSec K ⊤ C) :=
      CFSG.ComponentClassification.Quasisimple.nontrivial hq
    exact Group.IsPerfect.not_isNilpotent ↥(autSec K ⊤ C) hnil
  have hcomm := B1Red.commute_of_normal_not_le hq
    (fun n hn l hl => h.normal_autSec n (hQle hn) l hl)
    (fun l hl n hn => B1Red.conj_mem_pCoreOf (h.le_autSec hl) hn) hnot
  have hodd : Odd (Nat.card ↥(XMod.eqvAut ↥(autSec K ⊤ C) (Sec (⊤ : Subgroup V) C))) :=
    odd_card_eqvAut_of_irr (sec_sq_eq_one hV ⊤ C) h.isIrrSec_autSec h.exists_noncomm_autSec
  rw [eq_bot_iff]
  intro q hq'
  have hqe : q ∈ XMod.eqvAut ↥(autSec K ⊤ C) (Sec (⊤ : Subgroup V) C) := by
    intro a p
    exact congrArg (fun f : MulAut (Sec (⊤ : Subgroup V) C) => f p) (hcomm q hq' a a.2)
  obtain ⟨k, hk⟩ := hQ2 ⟨q, hq'⟩
  have hk' : (⟨q, hqe⟩ : ↥(XMod.eqvAut ↥(autSec K ⊤ C) (Sec (⊤ : Subgroup V) C))) ^ (2 ^ k) =
      1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k)
      (Nat.card ↥(XMod.eqvAut ↥(autSec K ⊤ C) (Sec (⊤ : Subgroup V) C))) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hord := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
    (orderOf_dvd_natCard _)
  exact Subgroup.mem_bot.2 (congrArg Subtype.val (orderOf_eq_one_iff.1 hord))

theorem genFitting_autSec [Finite V] (hV : ∀ v : V, v ^ 2 = 1) :
    quasithinGenFitting (autSec X ⊤ C) = autSec K ⊤ C :=
  quasithinGenFitting_eq_of_two_pow h.le_autSec h.normal_autSec
    (B1Red.isQuasisimple_to_open h.isQuasisimple_autSec) h.two_autSec (h.pCoreOf_autSec_eq_bot hV)

theorem sqtkGroup [Finite V] (hS : SQTKGroup ↥K) : SQTKGroup ↥X :=
  sqtkGroup_of_two_pow h.le h.normal h.two hS

theorem sqtkGroup_autSec [Finite V] (hS : SQTKGroup ↥K) : SQTKGroup ↥(autSec X ⊤ C) :=
  B5.sqtk_autSec (le_stabSub_top X) h.stab h.inf_centSec_eq_bot (h.sqtkGroup hS)

theorem b4Hyp [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hS : SQTKGroup ↥K) :
    B4Hyp (autSec X ⊤ C) (autSec K ⊤ C) :=
  ⟨h.sqtkGroup_autSec hS, (h.genFitting_autSec hV).symm, h.isQuasisimple_autSec,
    h.isIrrSec_autSec⟩

end QSec

end CFSG.Quasithin.InternalSec
