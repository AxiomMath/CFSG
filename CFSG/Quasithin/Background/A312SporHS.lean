
module

public import CFSG.Quasithin.Background.A312SporHSBase
import all CFSG.Quasithin.Background.A312SporHSBase

public import CFSG.Quasithin.Background.A312SporShapes
public import CFSG.Quasithin.Background.A312SporHSInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.Quasithin.Background.A312SporHSKInputs
import Certificates.Kernel.HSA312.Y1
import Certificates.Kernel.HSA312.Y2
public import CFSG.Blueprint.NativeSporadic
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS

public section

namespace CFSG.Quasithin.A312S

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.Sporadic.SmallF2 CFSG.Quasithin.A312S.HS
open CFSG.Sporadic.HS.Native (hsData)
open Matrix

section HS

theorem hs_V1 :
    IsZ4StarExtra2 ↥(Subgroup.closure {x | x ∈ hsZ4Elt :: hsEElts}) ∧
      Nat.card (Subgroup.closure {x | x ∈ hsZ4Elt :: hsEElts}) = 64 :=
  ⟨(Certificates.certificate4102.2.2.2.2.1).1,
    (Certificates.certificate4102.2.2.2.2.1).2.1⟩

theorem hs_O2Y1 :
    CFSG.Open.pCoreOf 2 (hsCtx.Y 1) = Subgroup.closure {x | x ∈ hsZ4Elt :: hsEElts} :=
  (Certificates.certificate4102.2.2.2.2.1).2.2

theorem hsE2_size :
    hsE2.toArray.size = 4 := by
  rw [List.size_toArray]
  exact (Certificates.certificate4102.2.2.2.2.2).1

theorem hs_e8 :
    E8Basis hsV ∧ ∀ l < 4, ∀ i : Fin 3,
      hsLetter l * hsV i * (hsLetter l)⁻¹ = e8Elt hsV fun r => hsMat l r i :=
  ⟨(Certificates.certificate4102.2.2.2.2.2).2.1,
    (Certificates.certificate4102.2.2.2.2.2).2.2.1⟩

theorem hsLetter_mem
    {l : ℕ} (hl : l < 4) :
    hsLetter l ∈ hsCtx.Y 2 := by
  have h1 := evalElt_getD_mem_closure hsE2.toArray (l := l) (by rw [hsE2_size]; exact hl)
  rw [LatCtx.toList_toArray_set] at h1
  exact h1

theorem hs_Y2_le_norm :
    hsCtx.Y 2 ≤ e8Norm hs_e8.1 := by
  rw [LatCtx.Y, Subgroup.closure_le]
  intro x hx
  have hx' : x ∈ hsE2 := hx
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hx'
  have hl4 : l < 4 := by
    have := hsE2_size
    rw [List.size_toArray] at this
    omega
  have hlet : hsE2[l] = hsLetter l := by
    rw [hsLetter, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hl]
    rfl
  have hm := mem_e8Norm hs_e8.1 (hsMat l) (hs_e8.2 l hl4)
  rw [← hlet] at hm
  exact hm

noncomputable def hsPsi :
    ↥(hsCtx.Y 2) →* SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (e8SL hs_e8.1).comp (Subgroup.inclusion hs_Y2_le_norm)

theorem hsPsi_letter
    {l : ℕ} (hl : l < 4) :
    hsPsi ⟨hsLetter l, hsLetter_mem hl⟩ = hsSL l :=
  e8SL_eq hs_e8.1 _ (hsSL l) (hs_e8.2 l hl)

theorem hsPsi_surjective :
    Function.Surjective hsPsi := by
  have h3 : hsSL 0 * hsSL 2 * hsSL 3 ∈ hsPsi.range :=
    ⟨⟨hsLetter 0, hsLetter_mem (by norm_num)⟩ * ⟨hsLetter 2, hsLetter_mem (by norm_num)⟩ *
      ⟨hsLetter 3, hsLetter_mem (by norm_num)⟩, by
      rw [map_mul, map_mul, hsPsi_letter (l := 0) (by norm_num),
        hsPsi_letter (l := 2) (by norm_num), hsPsi_letter (l := 3) (by norm_num)]⟩
  have h4 : hsSL 0 * hsSL 1 ∈ hsPsi.range :=
    ⟨⟨hsLetter 0, hsLetter_mem (by norm_num)⟩ * ⟨hsLetter 1, hsLetter_mem (by norm_num)⟩, by
      rw [map_mul, hsPsi_letter (l := 0) (by norm_num), hsPsi_letter (l := 1) (by norm_num)]⟩
  have h7 : hsSL 3 ∈ hsPsi.range := ⟨_, hsPsi_letter (l := 3) (by norm_num)⟩
  have o3 : orderOf (hsSL 0 * hsSL 2 * hsSL 3) = 3 := by
    apply orderOf_eq_prime (hp := ⟨Nat.prime_three⟩)
    · exact Subtype.ext (show (hsMat 0 * hsMat 2 * hsMat 3) ^ 3 = 1 by decide +kernel)
    · intro h
      have h' : hsMat 0 * hsMat 2 * hsMat 3 = 1 := congrArg Subtype.val h
      revert h'
      decide +kernel
  have o4 : orderOf (hsSL 0 * hsSL 1) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := hsSL 0 * hsSL 1)
      (hp := ⟨Nat.prime_two⟩) ?_ ?_
    · rw [h]
      norm_num
    · intro h
      have h' : (hsMat 0 * hsMat 1) ^ 2 ^ 1 = 1 := congrArg Subtype.val h
      revert h'
      decide +kernel
    · exact Subtype.ext (show (hsMat 0 * hsMat 1) ^ 2 ^ (1 + 1) = 1 by decide +kernel)
  have o7 : orderOf (hsSL 3) = 7 := by
    apply orderOf_eq_prime (hp := ⟨by norm_num⟩)
    · exact Subtype.ext (show hsMat 3 ^ 7 = 1 by decide +kernel)
    · intro h
      have h' : hsMat 3 = 1 := congrArg Subtype.val h
      revert h'
      decide +kernel
  exact MonoidHom.range_eq_top.mp (eq_top_of_orders_sl32 h3 h4 h7 o3 o4 o7)

theorem hsPsi_ker_card :
    Nat.card hsPsi.ker = 64 := by
  have h1 := card_eq_card_ker_mul_card_range hsPsi
  rw [MonoidHom.range_eq_top.mpr hsPsi_surjective, Subgroup.card_top,
    CFSG.QuasithinUnique.Vol2Native.A312L.Seven.card_slThree, hs_member_card 2 (by norm_num)] at h1
  have h2 : (#[1, 15, 21, 3, 3] : Array ℕ)[2]! * 512 = 64 * 168 := rfl
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm

end HS

end CFSG.Quasithin.A312S
