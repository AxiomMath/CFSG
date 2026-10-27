module

public import Certificates.Data.ParrottPSp43
public import CFSG.Permutation.FinPack64

public section

namespace CFSG.RankThree.GF2n.Parrott.Pack45

open Equiv
open CFSG.KS.PCnt (pkw)
open CFSG.Permutation.FinPack64
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (x45 y45 f45)

theorem h45 : 45 ≤ 64 := by norm_num

@[expose] def cOne : ℕ :=
  1324506994726093842395220415202184825539067753363340944416092930018803878078455872
@[expose] def cT : ℕ :=
  1323551936092835221201048465889197193977640368861089134228055773665926500247408768
@[expose] def cU : ℕ :=
  783879938608084924469995659485639463910692570296370511312628825440072340993220672
@[expose] def cA1 : ℕ :=
  1189076732329508598327988703204730138703200508813159819035034594213892255295247104
@[expose] def cB1 : ℕ :=
  1046075522681691933087663707505977654605449983831461126909635701422581463639700352
@[expose] def cA2 : ℕ :=
  1052915510873207803926639565884906434767584352412826349907141705890539040397341056
@[expose] def cB2 : ℕ :=
  1076941463407737486198316390409044046335591186426649479655389057703412767623500288
@[expose] def cS1 : ℕ :=
  902942574704215725468559849436512372713305672823258992364072685183662857512558656
@[expose] def cS2 : ℕ :=
  722241093118414939743940992217888438543664053386887216045509032374718440309792832
@[expose] def cA1i : ℕ :=
  1187702040393188206060602032131195841961931570882087115188228558643680050966479424
@[expose] def cB1i : ℕ :=
  1047913269703547726517080933023748512979978151342702349835017093958444049048593088
@[expose] def cS1i : ℕ :=
  482746987804245472910489973232273122682909771666394254779653738631762881073127488
@[expose] def cS2i : ℕ :=
  1023374043922254390677793904347844717922205475483344855444109560715400336146178112

@[expose] def cY : ℕ :=
  369320570347332080866071694897057006364230807052024500897345987209471738623205414
@[expose] def cF : ℕ :=
  903855130118820968380953642477467841243549792412070468675806884038879808943034496
@[expose] def cV : ℕ :=
  904766766555602278478877746400819273629311449916827138567766512658224394595213376

theorem pk_one : pkw 6 (1 : Perm (Fin 45)) = cOne := by decide +kernel
theorem pk_t : pkw 6 t = cT := by decide +kernel
theorem pk_u : pkw 6 u = cU := by decide +kernel
theorem pk_a1 : pkw 6 alpha1 = cA1 := by decide +kernel
theorem pk_b1 : pkw 6 beta1 = cB1 := by decide +kernel
theorem pk_a2 : pkw 6 alpha2 = cA2 := by decide +kernel
theorem pk_b2 : pkw 6 beta2 = cB2 := by decide +kernel
theorem pk_s1 : pkw 6 sigma1 = cS1 := by decide +kernel
theorem pk_s2 : pkw 6 sigma2 = cS2 := by decide +kernel
theorem pk_a1i : pkw 6 alpha1⁻¹ = cA1i := by decide +kernel
theorem pk_b1i : pkw 6 beta1⁻¹ = cB1i := by decide +kernel
theorem pk_s1i : pkw 6 sigma1⁻¹ = cS1i := by decide +kernel
theorem pk_s2i : pkw 6 sigma2⁻¹ = cS2i := by decide +kernel
theorem pk_x : pkw 6 x45 = cT := pk_t
theorem pk_y : pkw 6 y45 = cY := by decide +kernel
theorem pk_f : pkw 6 f45 = cF := by decide +kernel
theorem pk_v : pkw 6 v = cV := by decide +kernel

@[expose] def q0w (p : Fin 5 → Fin 2) : Perm (Fin 45) :=
  alpha1 ^ (p 0 : ℕ) * beta1 ^ (p 1 : ℕ) * alpha2 ^ (p 2 : ℕ) * beta2 ^ (p 3 : ℕ) * t ^ (p 4 : ℕ)

@[expose] def s0w (p : Fin 4 → Fin 2) : Perm (Fin 45) :=
  t ^ (p 0 : ℕ) * u ^ (p 1 : ℕ) * (alpha1 * alpha2) ^ (p 2 : ℕ) * (beta1 * beta2) ^ (p 3 : ℕ)

@[expose] noncomputable def q0K (b0 b1 b2 b3 b4 : ℕ) : ℕ :=
  mulW 45 (mulW 45 (mulW 45 (mulW 45 (selK b0 cOne cA1) (selK b1 cOne cB1)) (selK b2 cOne cA2))
    (selK b3 cOne cB2)) (selK b4 cOne cT)

@[expose] noncomputable def s0K (b0 b1 b2 b3 : ℕ) : ℕ :=
  mulW 45 (mulW 45 (mulW 45 (selK b0 cOne cT) (selK b1 cOne cU))
    (selK b2 cOne (mulW 45 cA1 cA2))) (selK b3 cOne (mulW 45 cB1 cB2))

theorem pk_q0 (p : Fin 5 → Fin 2) : pkw 6 (q0w p) = q0K (p 0) (p 1) (p 2) (p 3) (p 4) :=
  pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_pow pk_one pk_a1 _) (pk_pow pk_one pk_b1 _))
    (pk_pow pk_one pk_a2 _)) (pk_pow pk_one pk_b2 _)) (pk_pow pk_one pk_t _)

theorem pk_s0 (p : Fin 4 → Fin 2) : pkw 6 (s0w p) = s0K (p 0) (p 1) (p 2) (p 3) :=
  pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_pow pk_one pk_t _) (pk_pow pk_one pk_u _))
    (pk_pow pk_one (pk_mul h45 pk_a1 pk_a2) _)) (pk_pow pk_one (pk_mul h45 pk_b1 pk_b2) _)

end CFSG.RankThree.GF2n.Parrott.Pack45
