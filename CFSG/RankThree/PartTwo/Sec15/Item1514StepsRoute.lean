module

public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1518
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1519
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1521
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1522
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17

@[expose] noncomputable def Step1515R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step1515 A (lB A) c L

@[expose] noncomputable def Step1516R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step1516 A (lB A) c L

@[expose] noncomputable def Step1517R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step1517 A (lB A) c L

@[expose] noncomputable def Step1518R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step1518 A (lB A) c L

@[expose] noncomputable def Step1519R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step1519 A (lB A) c L

@[expose] noncomputable def Step1520R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step1520 A (lB A) c L

@[expose] noncomputable def Step1521R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step1521 A (lB A) c L

@[expose] noncomputable def Step1522R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step1522 A (lB A) c L

@[expose] noncomputable def Item1511R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item1511 A (lB A) c L

@[expose] noncomputable def Item1512R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item1512 A (lB A) L

@[expose] noncomputable def Item1513R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item1513 A (lB A) c L

@[expose] noncomputable def Item1513S17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1513 A (lB A) c L

@[expose] noncomputable def Item156R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item156 A (lB A)

@[expose] noncomputable def Item14_24R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item14_24 A (lB A) c L

@[expose] noncomputable def Claim153NormalR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Claim153Normal A (lB A)

theorem step1515R_of
    (h131 : Item131) (h137 : Item137) (hcl : Claim1515M12)
    (h1511 : Item1511R) (h1512 : Item1512R) (h1513 : Item1513R) (h156 : Item156R)
    (hA7T : Step1515A7Trans) (hA7O : Step1515A7Omega) (hM22 : Step1515M22)
    (hLA7 : Step1515LA7) (hHJL : Step1515HJList) (hHJ : Step1515HJ) : Step1515R :=
  fun G _ _ A c L h => rank3II_15_15_of h h131 h137 hcl (h1511 G A c L h) (h1512 G A c L h)
    (h1513 G A c L h) (h156 G A c L h) hA7T hA7O hM22 hLA7 hHJL hHJ

theorem step1516R_of (h153 : Item153MainR) (hobs : Claim153ObsR) (h149 : Sec16.Item149S14)
    (h1411 : Item1411_1R) (hloc : Claim1411LocalR) : Step1516R :=
  fun G _ _ A c L h => rank3II_15_16_of h (h153 G A c L h) (hobs G A c L h)
    (h149 G A c L h.toSec14Std) (h1411 G A c L h) (hloc G A c L h)

theorem step1517R_of (hY0 : Step1517Y0) (hcon : Step1517Con) (hsimp : Step1517Simple) :
    Step1517R :=
  fun _ _ _ _ _ _ h => rank3II_15_17_of h hY0 hcon hsimp

theorem step1519R_of (h1518 : Step1518R) (hsmall : Step1519Small) (hP : Step1519P)
    (hcent : Step1519Cent) : Step1519R :=
  fun G _ _ A c L h => rank3II_15_19_of h (h1518 G A c L h) hsmall hP hcent

theorem step1520R_of (h1423 : Item14_23R) (hcore : Step1520Core) (hcomm : Step1520Comm) :
    Step1520R :=
  fun G _ _ A c L h => rank3II_15_20_of h (h1423 G A c L h) hcore hcomm

theorem step1521R_of (h1520 : Step1520R) (hU : Step1521U) (hnorm : Claim153NormalR)
    (hgen : Step1521Gen) : Step1521R :=
  fun G _ _ A c L h => rank3II_15_21_of h (h1520 G A c L h) hU (hnorm G A c L h) hgen

theorem step1522R_of (h1424 : Item14_24R) (h153 : Item153MainR) (h1517 : Step1517R)
    (hhyp : Step1522Hyp) (hconj : Step1522Conj) : Step1522R :=
  fun G _ _ A c L h => rank3II_15_22_of h (h1424 G A c L h) (h153 G A c L h)
    (h1517 G A c L h) hhyp hconj

theorem item1514R_of (h1515 : Step1515R) (h1519 : Step1519R) (h1521 : Step1521R)
    (h1522 : Step1522R) : Item1514R :=
  fun G _ _ A c L h => rank3II_15_14_of_steps (h1515 G A c L h) (h1519 G A c L h)
    (h1521 G A c L h) (h1522 G A c L h)

end CFSG.RankThree.PartTwo.Sec15
