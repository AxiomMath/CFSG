module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Shift
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P512Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan512c (F : FanTree Γ G) (h510 : Fan510 F) (h511 : Fan511 F) (h53a : Fan53a F)
    (h53b : Fan53b F) (h57b : Fan57bT F) : Fan512c F := by
  intro h40 T hT z hz hz1 a b tL tR hfix hEven
  obtain ⟨-, huniv⟩ := P512.coreSat2 h510 h511 h40 hT hz hz1
  obtain ⟨hba, hrl⟩ := huniv a b tL tR hfix
  obtain ⟨k, hk⟩ := hEven
  have hr1 : 1 ≤ tR - b := (h53a h40 T.line z a b tL tR hz hfix).1
  have hshift : P55.IsShift T.line (T.τ ^ (k + 1)) (2 * (k + 1)) := fun i =>
    T.zpow_smul_vert (k + 1) i
  have hz'' : T.τ ^ (k + 1) * z * (T.τ ^ (k + 1))⁻¹ ∈ T.line.ZZ := P55.IsShift.zz hshift hz
  have hfix'' := P55.IsShift.isCoreFix hshift hfix
  have hC1 : T.line.IsCoreCFix z a b tL tR := ⟨hfix.fix, h53b h40 T.line z a b hz hfix.core⟩
  have hC2 := P55.IsShift.isCoreCFix F hshift hC1
  have hperfect : T.line.InPerfectPos z (T.τ ^ (k + 1) * z * (T.τ ^ (k + 1))⁻¹) a b tL tR
      (a + 2 * (k + 1)) (b + 2 * (k + 1)) (tL + 2 * (k + 1)) (tR + 2 * (k + 1)) :=
    ⟨hC1, hC2, by omega, by omega⟩
  have := h57b h40 T z _ a b tL tR _ _ _ _ hz hz'' hfix hfix'' hperfect
  omega

end CFSG.Quasithin.Fan86
