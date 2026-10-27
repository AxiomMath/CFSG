module

public import Certificates.Data.G23RecogWordsInputs

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.CosetTable

@[expose] def g23H5 : List (List (Fin (subsetOf 6 [0, 1, 2, 3, 4]).length × Bool)) :=
  restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) g23WordsH

end CFSG.GH74.QTGen4.Recog.G23
