module

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def sixTabDigit (t i : Nat) : Nat := (t >>> (4 * i)) &&& 15

@[expose] def sixTabImg (t off h : Nat) : Nat :=
  (((h >>> 0) &&& 1) <<< sixTabDigit t off) |||
  (((h >>> 1) &&& 1) <<< sixTabDigit t (off + 1)) |||
  (((h >>> 2) &&& 1) <<< sixTabDigit t (off + 2)) |||
  (((h >>> 3) &&& 1) <<< sixTabDigit t (off + 3)) |||
  (((h >>> 4) &&& 1) <<< sixTabDigit t (off + 4)) |||
  (((h >>> 5) &&& 1) <<< sixTabDigit t (off + 5))

@[expose] def sixTabLo (t : Nat) : Nat :=
  (List.range 64).foldl (fun acc h => acc ||| (sixTabImg t 0 h <<< (12 * h))) 0

@[expose] def sixTabHi (t : Nat) : Nat :=
  (List.range 64).foldl (fun acc h => acc ||| (sixTabImg t 6 h <<< (12 * h))) 0

@[expose] def sixTabAct (t m : Nat) : Nat :=
  ((sixTabLo t >>> (12 * (m &&& 63))) &&& 4095) |||
    ((sixTabHi t >>> (12 * ((m >>> 6) &&& 63))) &&& 4095)

@[expose] def sixTabComp (a b : Nat) : Nat :=
  (sixTabDigit a (sixTabDigit b 0)) ||| (sixTabDigit a (sixTabDigit b 1) <<< 4) |||
  (sixTabDigit a (sixTabDigit b 2) <<< 8) ||| (sixTabDigit a (sixTabDigit b 3) <<< 12) |||
  (sixTabDigit a (sixTabDigit b 4) <<< 16) ||| (sixTabDigit a (sixTabDigit b 5) <<< 20) |||
  (sixTabDigit a (sixTabDigit b 6) <<< 24) ||| (sixTabDigit a (sixTabDigit b 7) <<< 28) |||
  (sixTabDigit a (sixTabDigit b 8) <<< 32) ||| (sixTabDigit a (sixTabDigit b 9) <<< 36) |||
  (sixTabDigit a (sixTabDigit b 10) <<< 40) ||| (sixTabDigit a (sixTabDigit b 11) <<< 44)

@[expose] def sixEvenW (n : Nat) : Bool :=
  ((n ^^^ (n >>> 1) ^^^ (n >>> 2) ^^^ (n >>> 3) ^^^ (n >>> 4) ^^^ (n >>> 5)) &&& 1) == 0

@[expose] def sixVecs : List Nat :=
  (List.range 4096).filter fun m => sixEvenW (m &&& 63) && sixEvenW (m >>> 6)

@[expose] def sixKMem (K : Bool) (d : Nat) : Bool := d == 0 || (K && d == 4095)

@[expose] def sixFixes (K : Bool) (t m : Nat) : Bool := sixKMem K (sixTabAct t m ^^^ m)

@[expose] def sixProf (K : Bool) (t : Nat) : Nat :=
  sixVecs.foldl (fun acc m => if sixFixes K t m then acc ||| (1 <<< m) else acc) 0

@[expose] def sixFull : Nat := sixVecs.foldl (fun acc m => acc ||| (1 <<< m)) 0

@[expose] def sixInvTabs : List Nat := [
  1255026489771, 1327757694891, 2281792047771, 3659624130171, 4541180963211, 5781859170411,
  17881332549306, 17945507358906, 20088376359606, 21029576944056, 22003745195961, 23313127085751,
  35395989904266, 36580295797671, 38505481218921, 38570156403606, 39926848191336, 40695161588601,
  53137899042666, 53886076762281, 55250818546296, 55323550726791, 57264841602711, 58416934926726,
  70527985871226, 71825285154726, 72775292918376, 73744679413911, 75871447381641, 75935620229016,
  88039124007066, 89267719607976, 90177464199801, 91539187017606, 92509329590631, 92574005762166,
  113840982602016, 113905406116371, 114875801223696, 115012700222721, 116168312762901,
  116172344337216, 117066230411346, 117138709828116, 117199110018096, 117203131384101,
  130333908664851, 130398332203296, 132399766975056, 132605879001876, 133756963927056,
  133765518348801, 134590204428306, 134731884737856, 134787750957621, 134796308251731,
  147865425163536, 148002330329601, 148896471855636, 149102576018256, 151369265975856,
  151369516658706, 152194199605536, 152263407501891, 152400052761621, 152400306378036,
  165715043758656, 165719065240341, 166810761843216, 166819320181761, 167926364909586,
  167926615577136, 170108493246756, 170113020200211, 170116793975376, 170117047603266,
  188461173973776, 188465195070021, 188525850145281, 188534404305936, 188606631457296,
  188606884089906, 188662749021456, 188667277619796, 188671056937251, 188671307621121,
  200629101269556, 200701574788176, 200761975001106, 200766000268611, 201660142196016,
  201801823633941, 201857696870466, 201866251096356, 202767441462291, 202836642378021,
  202973295759936, 202973545447506, 204124630286931, 204129164280096, 204132935808276,
  204133185492021, 204953847411201, 204957870465876, 205018523575056, 205027077735681,
  205099306853121, 205099557519651, 205155424424961, 205159951049541, 205163730374706
]

@[expose] def sixIdx (t : Nat) : Nat := sixInvTabs.findIdx (· == t)

@[expose] def sixInvProf (K : Bool) : List Nat := sixInvTabs.map (sixProf K)

@[expose] def sixProfOf (K : Bool) (t : Nat) : Nat := (sixInvProf K).getD (sixIdx t) 0

@[expose] def sixComm (a b : Nat) : Bool := sixTabComp a b == sixTabComp b a

@[expose] def sixInvAdj : List Nat :=
  sixInvTabs.map fun a => (List.range 111).foldl (fun acc k =>
    if sixComm a (sixInvTabs.getD k 0) then acc ||| (1 <<< k) else acc) 0

@[expose] def sixChk1 (K : Bool) : Bool :=
  (List.range 111).all fun i => (sixInvProf K).getD i 0 != sixFull

@[expose] def sixChk2 (K : Bool) : Bool :=
  (List.range 111).all fun i => (List.range 111).all fun j =>
    i == j || !(sixInvAdj.getD i 0).testBit j ||
      (let a := sixInvTabs.getD i 0
       let b := sixInvTabs.getD j 0
       (sixInvProf K).getD i 0 != (sixInvProf K).getD j 0 ||
         (sixInvProf K).getD j 0 != sixProfOf K (sixTabComp a b))

@[expose] def sixChk3 (K : Bool) : Bool :=
  (List.range 111).all fun i => (List.range 111).all fun j =>
    i == j || !(sixInvAdj.getD i 0).testBit j ||
    (List.range 111).all fun k =>
      k == i || k == j || !(sixInvAdj.getD i 0).testBit k || !(sixInvAdj.getD j 0).testBit k ||
        (let a := sixInvTabs.getD i 0
         let b := sixInvTabs.getD j 0
         let c := sixInvTabs.getD k 0
         sixTabComp a b == c ||
           (let pa := (sixInvProf K).getD i 0
            let pb := (sixInvProf K).getD j 0
            let pc := (sixInvProf K).getD k 0
            let pab := sixProfOf K (sixTabComp a b)
            let pac := sixProfOf K (sixTabComp a c)
            let pbc := sixProfOf K (sixTabComp b c)
            let e := pa &&& pb &&& pc
            (pa &&& pb) != e || (pa &&& pc) != e || (pb &&& pc) != e || (pa &&& pbc) != e ||
              (pb &&& pac) != e || (pc &&& pab) != e || (pab &&& pac) != e))

@[expose] def sixChk4 : Bool :=
  (List.range 111).all fun i => (List.range 111).all fun j =>
    i == j || !(sixInvAdj.getD i 0).testBit j ||
    (List.range 111).all fun k =>
      k == i || k == j || !(sixInvAdj.getD i 0).testBit k || !(sixInvAdj.getD j 0).testBit k ||
        (let a := sixInvTabs.getD i 0
         let b := sixInvTabs.getD j 0
         let c := sixInvTabs.getD k 0
         sixTabComp a b == c ||
           (let ab := sixTabComp a b
            let n := (sixInvAdj.getD i 0) &&& (sixInvAdj.getD j 0) &&& (sixInvAdj.getD k 0)
            (List.range 111).all fun l =>
              !n.testBit l ||
                (let d := sixInvTabs.getD l 0
                 d == a || d == b || d == c || d == ab || d == sixTabComp a c ||
                   d == sixTabComp b c || d == sixTabComp ab c)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
