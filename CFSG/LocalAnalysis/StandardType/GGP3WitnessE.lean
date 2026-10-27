module

public import CFSG.LocalAnalysis.StandardType.GGP3Witness

public section

namespace CFSG.StandardType

private def p3e_E6Rcodes : List ℕ :=
  [7755367, 7755383, 7759479, 7825015, 8873591, 7759735, 7825271, 8873847, 7829367, 8877943,
   8943479, 7829383, 8877959, 8943495, 8947591, 8947847, 7759736, 7825272, 8873848, 7829368,
   8877944, 8943480, 7829624, 8878200, 8943736, 8947832, 7829384, 8877960, 8943496, 8947592,
   7829640, 8878216, 8943752, 7833736, 8882312, 7899272, 9996424, 9013384, 10061960, 8951944,
   9017480, 10066056, 8948104, 8952200, 9017736, 10066312, 8947864, 8951960, 9017496, 10066072,
   8952216, 9017752, 10066328, 9021848, 10070424, 10135960, 8947849, 8948105, 8952201, 9017737,
   10066313, 8952217, 9017753, 10066329, 9021849, 10070425, 10135961, 9022105, 10070681, 10136217,
   10140313, 10140329]

private def p3e_E6R : List (List ℤ) := p3e_E6Rcodes.map (ggLWdecode 6)

private theorem p3e_E6R_closed : ggLWclosed (ggLWmatC (CartanMatrix.E 6)) 6 p3e_E6R = true := by
  decide +kernel

private def p3e_E7Rcodes : List ℕ :=
  [124077414, 124077415, 124077671, 124081767, 124147303, 125195879, 141973095, 124081783,
   124147319, 125195895, 141973111, 124151415, 125199991, 141977207, 125265527, 142042743,
   143091319, 124151671, 125200247, 141977463, 125265783, 142042999, 143091575, 125269879,
   142047095, 143095671, 143161207, 125269895, 142047111, 143095687, 143161223, 143165319,
   143165575, 124151672, 125200248, 141977464, 125265784, 142043000, 143091576, 125269880,
   142047096, 143095672, 143161208, 125270136, 142047352, 143095928, 143161464, 143165560,
   125269896, 142047112, 143095688, 143161224, 143165320, 125270152, 142047368, 143095944,
   143161480, 125274248, 142051464, 143100040, 125339784, 142117000, 126388360, 159942792,
   144214152, 160991368, 143231112, 144279688, 161056904, 143169672, 143235208, 144283784,
   161061000, 143165832, 143169928, 143235464, 144284040, 161061256, 143165592, 143169688,
   143235224, 144283800, 161061016, 143169944, 143235480, 144284056, 161061272, 143239576,
   144288152, 161065368, 144353688, 161130904, 162179480, 143165577, 143165833, 143169929,
   143235465, 144284041, 161061257, 143169945, 143235481, 144284057, 161061273, 143239577,
   144288153, 161065369, 144353689, 161130905, 162179481, 143239833, 144288409, 161065625,
   144353945, 161131161, 162179737, 144358041, 161135257, 162183833, 162249369, 144358057,
   161135273, 162183849, 162249385, 162253481, 162253737, 162253738]

private def p3e_E7R : List (List ℤ) := p3e_E7Rcodes.map (ggLWdecode 7)

private theorem p3e_E7R_closed : ggLWclosed (ggLWmatC (CartanMatrix.E 7)) 7 p3e_E7R = true := by
  decide +kernel

private def p3e_E8Rcodes : List ℕ :=
  [1698899030, 1967334486, 1984111702, 1985160278, 1985225814, 1985229910, 1985230166, 1985229926,
   1985230182, 1985234278, 1985299814, 1986348390, 2003125606, 2271561062, 1985230167, 1985230183,
   1985234279, 1985299815, 1986348391, 2003125607, 2271561063, 1985234535, 1985300071, 1986348647,
   2003125863, 2271561319, 1985304167, 1986352743, 2003129959, 2271565415, 1986418279, 2003195495,
   2271630951, 2004244071, 2272679527, 2289456743, 1985304183, 1986352759, 2003129975, 2271565431,
   1986418295, 2003195511, 2271630967, 2004244087, 2272679543, 2289456759, 1986422391, 2003199607,
   2271635063, 2004248183, 2272683639, 2289460855, 2004313719, 2272749175, 2289526391, 2290574967,
   1986422647, 2003199863, 2271635319, 2004248439, 2272683895, 2289461111, 2004313975, 2272749431,
   2289526647, 2290575223, 2004318071, 2272753527, 2289530743, 2290579319, 2290644855, 2004318087,
   2272753543, 2289530759, 2290579335, 2290644871, 2290648967, 2290649223, 1986422648, 2003199864,
   2271635320, 2004248440, 2272683896, 2289461112, 2004313976, 2272749432, 2289526648, 2290575224,
   2004318072, 2272753528, 2289530744, 2290579320, 2290644856, 2004318328, 2272753784, 2289531000,
   2290579576, 2290645112, 2290649208, 2004318088, 2272753544, 2289530760, 2290579336, 2290644872,
   2290648968, 2004318344, 2272753800, 2289531016, 2290579592, 2290645128, 2004322440, 2272757896,
   2289535112, 2290583688, 2004387976, 2272823432, 2289600648, 2005436552, 2273872008, 2022213768,
   2559084680, 2307426440, 2575861896, 2291697800, 2308475016, 2576910472, 2290714760, 2291763336,
   2308540552, 2576976008, 2290653320, 2290718856, 2291767432, 2308544648, 2576980104, 2290649480,
   2290653576, 2290719112, 2291767688, 2308544904, 2576980360, 2290649240, 2290653336, 2290718872,
   2291767448, 2308544664, 2576980120, 2290653592, 2290719128, 2291767704, 2308544920, 2576980376,
   2290723224, 2291771800, 2308549016, 2576984472, 2291837336, 2308614552, 2577050008, 2309663128,
   2578098584, 2594875800, 2290649225, 2290649481, 2290653577, 2290719113, 2291767689, 2308544905,
   2576980361, 2290653593, 2290719129, 2291767705, 2308544921, 2576980377, 2290723225, 2291771801,
   2308549017, 2576984473, 2291837337, 2308614553, 2577050009, 2309663129, 2578098585, 2594875801,
   2290723481, 2291772057, 2308549273, 2576984729, 2291837593, 2308614809, 2577050265, 2309663385,
   2578098841, 2594876057, 2291841689, 2308618905, 2577054361, 2309667481, 2578102937, 2594880153,
   2309733017, 2578168473, 2594945689, 2595994265, 2291841705, 2308618921, 2577054377, 2309667497,
   2578102953, 2594880169, 2309733033, 2578168489, 2594945705, 2595994281, 2309737129, 2578172585,
   2594949801, 2595998377, 2596063913, 2309737385, 2578172841, 2594950057, 2595998633, 2596064169,
   2596068265, 2596068281, 2309737386, 2578172842, 2594950058, 2595998634, 2596064170, 2596068266,
   2596068522, 2596068282, 2596068538, 2596072634, 2596138170, 2597186746, 2613963962, 2882399418]

private def p3e_E8R : List (List ℤ) := p3e_E8Rcodes.map (ggLWdecode 8)

private theorem p3e_E8R_closed : ggLWclosed (ggLWmatC (CartanMatrix.E 8)) 8 p3e_E8R = true := by
  decide +kernel

private theorem p3e_cell_E6_k2 :
    ggLWtest3 (ggLWmat (ggAttachCartan (CartanMatrix.E 6) (2 : Fin 6))) 6 p3e_E6R
      [2, 3, 0, 2, 6, 4, 5, 3, 4, 2,
       3, 1, 3, 2, 4, 3, 5, 4, 6, 2,
       0, 3, 2, 6] 6 1 = true := by
  decide +kernel

private theorem p3e_cell_E6_k4 :
    ggLWtest3 (ggLWmat (ggAttachCartan (CartanMatrix.E 6) (4 : Fin 6))) 6 p3e_E6R
      [4, 5, 3, 4, 6, 2, 3, 4, 1, 3,
       2, 0, 2, 3, 1, 4, 3, 2, 6, 4,
       3, 5, 4, 6] 6 1 = true := by
  decide +kernel

private theorem p3e_cell_E6_k3 :
    ggLWtest3 (ggLWmat (ggAttachCartan (CartanMatrix.E 6) (3 : Fin 6))) 6 p3e_E6R
      [3, 4, 2, 3, 6, 5, 4, 3, 1, 3,
       4, 5, 6, 3, 2, 4, 3, 6] 6 0 = true := by
  decide +kernel

private theorem p3e_cell_E7_k2 :
    ggLWtest3 (ggLWmat (ggAttachCartan (CartanMatrix.E 7) (2 : Fin 7))) 7 p3e_E7R
      [2, 3, 0, 2, 7, 4, 5, 3, 4, 2,
       3, 1, 3, 2, 4, 3, 5, 4, 7, 2,
       0, 3, 2, 7] 7 1 = true := by
  decide +kernel

private theorem p3e_cell_E7_k5 :
    ggLWtest3 (ggLWmat (ggAttachCartan (CartanMatrix.E 7) (5 : Fin 7))) 7 p3e_E7R
      [5, 6, 4, 5, 7, 3, 4, 5, 2, 3,
       4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
       2, 5, 4, 3, 7, 5, 4, 6, 5, 7] 7 1 = true := by
  decide +kernel

private theorem p3e_cell_E7_k3 :
    ggLWtest3 (ggLWmat (ggAttachCartan (CartanMatrix.E 7) (3 : Fin 7))) 7 p3e_E7R
      [3, 4, 2, 3, 7, 5, 4, 3, 1, 3,
       4, 5, 7, 3, 2, 4, 3, 7] 7 0 = true := by
  decide +kernel

private theorem p3e_cell_E7_k1 :
    ggLWtest3 (ggLWmat (ggAttachCartan (CartanMatrix.E 7) (1 : Fin 7))) 7 p3e_E7R
      [1, 3, 4, 2, 3, 1, 7, 5, 6, 4,
       5, 3, 4, 1, 3, 2, 0, 2, 3, 1,
       4, 3, 5, 4, 6, 5, 7, 1, 3, 2,
       4, 3, 1, 7] 7 0 = true := by
  decide +kernel

private theorem p3e_cell_E8_k2 :
    ggLWtest3 (ggLWmat (ggAttachCartan (CartanMatrix.E 8) (2 : Fin 8))) 8 p3e_E8R
      [2, 3, 0, 2, 8, 4, 5, 3, 4, 2,
       3, 1, 3, 2, 4, 3, 5, 4, 8, 2,
       0, 3, 2, 8] 8 1 = true := by
  decide +kernel

private theorem p3e_cell_E8_k0 :
    ggLWtest3 (ggLWmat (ggAttachCartan (CartanMatrix.E 8) (0 : Fin 8))) 8 p3e_E8R
      [0, 2, 3, 4, 1, 3, 2, 0, 8, 5,
       6, 7, 4, 5, 6, 3, 4, 5, 2, 3,
       4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
       2, 5, 4, 3, 6, 5, 4, 7, 6, 5,
       8, 0, 2, 3, 1, 4, 3, 2, 0, 8] 8 4 = true := by
  decide +kernel

private theorem p3e_cell_E8_k6 :
    ggLWtest3 (ggLWmat (ggAttachCartan (CartanMatrix.E 8) (6 : Fin 8))) 8 p3e_E8R
      [6, 7, 5, 6, 8, 4, 5, 6, 3, 4,
       5, 2, 3, 4, 1, 3, 2, 0, 2, 3,
       1, 4, 3, 2, 5, 4, 3, 6, 5, 4,
       8, 6, 5, 7, 6, 8] 8 1 = true := by
  decide +kernel

private theorem p3e_cell_E8_k3 :
    ggLWtest3 (ggLWmat (ggAttachCartan (CartanMatrix.E 8) (3 : Fin 8))) 8 p3e_E8R
      [3, 4, 1, 3, 8, 5, 4, 3, 2, 3,
       4, 5, 8, 3, 1, 4, 3, 8] 8 0 = true := by
  decide +kernel

private theorem p3e_cell_E8_k1 :
    ggLWtest3 (ggLWmat (ggAttachCartan (CartanMatrix.E 8) (1 : Fin 8))) 8 p3e_E8R
      [1, 3, 4, 2, 3, 1, 8, 5, 6, 4,
       5, 3, 4, 1, 3, 2, 0, 2, 3, 1,
       4, 3, 5, 4, 6, 5, 8, 1, 3, 2,
       4, 3, 1, 8] 8 0 = true := by
  decide +kernel

theorem ggInvTest3_E6_cell {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {c : Λ} (e : Fin 6 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j)
    (hc : c = e 2 ∨ c = e 3 ∨ c = e 4) : GGInvTest3 (ggAttachCartan C c) := by
  rcases hc with hc | hc | hc
  · exact ggInvTest3_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggInvTest3_of_data (CartanMatrix.E 6) 2 p3e_E6R
        [2, 3, 0, 2, 6, 4, 5, 3, 4, 2,
         3, 1, 3, 2, 4, 3, 5, 4, 6, 2,
         0, 3, 2, 6] 6 1 p3e_E6R_closed p3e_cell_E6_k2)
  · exact ggInvTest3_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggInvTest3_of_data (CartanMatrix.E 6) 3 p3e_E6R
        [3, 4, 2, 3, 6, 5, 4, 3, 1, 3,
         4, 5, 6, 3, 2, 4, 3, 6] 6 0 p3e_E6R_closed p3e_cell_E6_k3)
  · exact ggInvTest3_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggInvTest3_of_data (CartanMatrix.E 6) 4 p3e_E6R
        [4, 5, 3, 4, 6, 2, 3, 4, 1, 3,
         2, 0, 2, 3, 1, 4, 3, 2, 6, 4,
         3, 5, 4, 6] 6 1 p3e_E6R_closed p3e_cell_E6_k4)

theorem ggInvTest3_E7_cell {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {c : Λ} (e : Fin 7 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j)
    (hc : c = e 2 ∨ c = e 3 ∨ c = e 5) : GGInvTest3 (ggAttachCartan C c) := by
  rcases hc with hc | hc | hc
  · exact ggInvTest3_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggInvTest3_of_data (CartanMatrix.E 7) 2 p3e_E7R
        [2, 3, 0, 2, 7, 4, 5, 3, 4, 2,
         3, 1, 3, 2, 4, 3, 5, 4, 7, 2,
         0, 3, 2, 7] 7 1 p3e_E7R_closed p3e_cell_E7_k2)
  · exact ggInvTest3_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggInvTest3_of_data (CartanMatrix.E 7) 3 p3e_E7R
        [3, 4, 2, 3, 7, 5, 4, 3, 1, 3,
         4, 5, 7, 3, 2, 4, 3, 7] 7 0 p3e_E7R_closed p3e_cell_E7_k3)
  · exact ggInvTest3_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggInvTest3_of_data (CartanMatrix.E 7) 5 p3e_E7R
        [5, 6, 4, 5, 7, 3, 4, 5, 2, 3,
         4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
         2, 5, 4, 3, 7, 5, 4, 6, 5, 7] 7 1 p3e_E7R_closed p3e_cell_E7_k5)

theorem ggInvTest3_E7_cell_one {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {b : Λ} (e : Fin 7 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j) (hb : b = e 1) :
    GGInvTest3 (ggAttachCartan C b) := by
  exact ggInvTest3_of_equiv e (ggAttachCartan_map_equiv e hC hb)
    (ggInvTest3_of_data (CartanMatrix.E 7) 1 p3e_E7R
      [1, 3, 4, 2, 3, 1, 7, 5, 6, 4,
       5, 3, 4, 1, 3, 2, 0, 2, 3, 1,
       4, 3, 5, 4, 6, 5, 7, 1, 3, 2,
       4, 3, 1, 7] 7 0 p3e_E7R_closed p3e_cell_E7_k1)

theorem ggInvTest3_E8_cell {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {c : Λ} (e : Fin 8 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j)
    (hc : c = e 2 ∨ c = e 3 ∨ c = e 6) : GGInvTest3 (ggAttachCartan C c) := by
  rcases hc with hc | hc | hc
  · exact ggInvTest3_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggInvTest3_of_data (CartanMatrix.E 8) 2 p3e_E8R
        [2, 3, 0, 2, 8, 4, 5, 3, 4, 2,
         3, 1, 3, 2, 4, 3, 5, 4, 8, 2,
         0, 3, 2, 8] 8 1 p3e_E8R_closed p3e_cell_E8_k2)
  · exact ggInvTest3_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggInvTest3_of_data (CartanMatrix.E 8) 3 p3e_E8R
        [3, 4, 1, 3, 8, 5, 4, 3, 2, 3,
         4, 5, 8, 3, 1, 4, 3, 8] 8 0 p3e_E8R_closed p3e_cell_E8_k3)
  · exact ggInvTest3_of_equiv e (ggAttachCartan_map_equiv e hC hc)
      (ggInvTest3_of_data (CartanMatrix.E 8) 6 p3e_E8R
        [6, 7, 5, 6, 8, 4, 5, 6, 3, 4,
         5, 2, 3, 4, 1, 3, 2, 0, 2, 3,
         1, 4, 3, 2, 5, 4, 3, 6, 5, 4,
         8, 6, 5, 7, 6, 8] 8 1 p3e_E8R_closed p3e_cell_E8_k6)

theorem ggInvTest3_E8_cell_one {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {b : Λ} (e : Fin 8 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j)
    (hb : b = e 0 ∨ b = e 1) : GGInvTest3 (ggAttachCartan C b) := by
  rcases hb with hb | hb
  · exact ggInvTest3_of_equiv e (ggAttachCartan_map_equiv e hC hb)
      (ggInvTest3_of_data (CartanMatrix.E 8) 0 p3e_E8R
        [0, 2, 3, 4, 1, 3, 2, 0, 8, 5,
         6, 7, 4, 5, 6, 3, 4, 5, 2, 3,
         4, 1, 3, 2, 0, 2, 3, 1, 4, 3,
         2, 5, 4, 3, 6, 5, 4, 7, 6, 5,
         8, 0, 2, 3, 1, 4, 3, 2, 0, 8] 8 4 p3e_E8R_closed p3e_cell_E8_k0)
  · exact ggInvTest3_of_equiv e (ggAttachCartan_map_equiv e hC hb)
      (ggInvTest3_of_data (CartanMatrix.E 8) 1 p3e_E8R
        [1, 3, 4, 2, 3, 1, 8, 5, 6, 4,
         5, 3, 4, 1, 3, 2, 0, 2, 3, 1,
         4, 3, 5, 4, 6, 5, 8, 1, 3, 2,
         4, 3, 1, 8] 8 0 p3e_E8R_closed p3e_cell_E8_k1)

end CFSG.StandardType
