module

public import CFSG.Quasithin.Background.C126A5Lift1
public import CFSG.Quasithin.Background.B6Sections

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem mem_O2_of_odd {H : Subgroup G} {x : G} (hx : x ∈ H) (ho : Odd (orderOf x)) :
    x ∈ twoResidual H := by
  obtain ⟨b, hb⟩ := twoResidual_isTwoQuotient H x hx
  exact B6.mem_of_pow_mem_of_coprime hb (Nat.Coprime.pow_right b (Odd.coprime_two_right ho))

namespace Lift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : Setting H T M V Y hV}
  {d : Data H T V Y hV}

structure XData (s : Setting H T M V Y hV) (d : Data H T V Y hV) (x : G) : Prop where
  mem : x ∈ Y
  ord : orderOf x = 3
  mem_L : cv hV x ∈ d.L
  th_eq : d.th (cv hV x) = cyc3 d.π

@[expose] def Khat (s : Setting H T M V Y hV) (d : Data H T V Y hV) (x : G) : Subgroup G :=
  conjClosure (Subgroup.zpowers x) (A₁ s d)

namespace XData

variable {x : G} (hx : XData s d x)

include hx

theorem x_mem_A₁ : x ∈ A₁ s d := Y_le_A₁ (s := s) (d := d) hx.mem

theorem zpowers_le_A₁ : Subgroup.zpowers x ≤ A₁ s d := by
  rw [Subgroup.zpowers_le]; exact hx.x_mem_A₁

theorem zpowers_le_Khat : Subgroup.zpowers x ≤ Khat s d x := le_conjClosure _ _

theorem Khat_le_A₁ : Khat s d x ≤ A₁ s d :=
  conjClosure_le fun _ ha _ hz => (A₁ s d).mul_mem ((A₁ s d).mul_mem ha (hx.zpowers_le_A₁ hz))
    ((A₁ s d).inv_mem ha)

theorem A₁_le_normalizer_Khat : A₁ s d ≤ Subgroup.normalizer (Khat s d x : Set G) :=
  le_normalizer_conjClosure _ _

theorem Khat_le_H : Khat s d x ≤ H := hx.Khat_le_A₁.trans A₁_le_H

theorem Y_le_Khat : Y ≤ Khat s d x := by
  set Y₀ := conjClosure (Subgroup.zpowers x) Y with hY₀
  have hxY : Subgroup.zpowers x ≤ Y := by rw [Subgroup.zpowers_le]; exact hx.mem
  have hY₀Y : Y₀ ≤ Y := conjClosure_le fun y hy z hz => Y.mul_mem (Y.mul_mem hy (hxY hz))
    (Y.inv_mem hy)
  have hnY : Y ≤ Subgroup.normalizer (Y₀ : Set G) := le_normalizer_conjClosure _ _
  have hsup : (Y ⊓ pCoreOf 2 H) ⊔ Y₀ = Y := by
    apply le_antisymm (sup_le inf_le_left hY₀Y)
    calc Y = (Y ⊓ pCoreOf 2 H) ⊔ Subgroup.zpowers x := s.Y_eq_sup hx.mem hx.ord
      _ ≤ (Y ⊓ pCoreOf 2 H) ⊔ Y₀ := sup_le_sup_left (le_conjClosure _ _) _
  have h2 := isTwoQuotient_of_sup_eq ((pCoreOf_isPGroup 2 H).to_le inf_le_right) hnY hsup
  have : twoResidual Y ≤ Y₀ := twoResidual_le_of_isTwoQuotient hY₀Y hnY h2
  rw [s.Y_res] at this
  exact this.trans (conjClosure_mono le_rfl (Y_le_A₁ (s := s) (d := d)))

theorem Khat_le_twoResidual : Khat s d x ≤ twoResidual H := by
  have hxK : x ∈ twoResidual H :=
    mem_O2_of_odd (s.Y_le hx.mem) (by rw [hx.ord]; decide)
  refine conjClosure_le fun a ha z hz => ?_
  have hzK : z ∈ twoResidual H := by
    have : Subgroup.zpowers x ≤ twoResidual H := by rw [Subgroup.zpowers_le]; exact hxK
    exact this hz
  exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_twoResidual H (A₁_le_H ha)) z).1 hzK

theorem Khat_inf_C (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    Khat s d x ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H :=
  fun _ hk => hRad ⟨hx.Khat_le_twoResidual hk.1, hk.2⟩

end XData

end Lift

end CFSG.Quasithin.C126.A5
