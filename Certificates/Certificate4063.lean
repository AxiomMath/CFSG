module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23BaseInputs
import Certificates.Kernel.LocalQT.Word.C4063

public section

namespace Certificates

open CFSG.KD.LQT.C4063 CFSG.KC.LQT.W in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.G3 CFSG.QuasithinUnique.A5.G3.M23 in
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat in
theorem certificate4063 : (tGens = [evalW natGens [0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0],
         evalW natGens [0,1,1,0,1,0,1,1,0,1,1,0,1,0,1,1,0],
         evalW natGens [0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,1,0,1,0],
         evalW natGens [1,1,1,0,1,0,1,1,1,0,1,0,1,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,0]] ∧ mGens1 = [evalW natGens [1,1,0,1,0,1,0,1,1,1,0,1],
         evalW natGens [0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,0,1]] ∧ mGens2 = [evalW natGens [1,1,1,0,1,0,1,1,1,0,1],
         evalW natGens [0,1,0,1,0,1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1]]) :=
  ⟨words_sound _ _ _ hA hT kT, words_sound _ _ _ hA h1 k1, words_sound _ _ _ hA h2 k2⟩

end Certificates
