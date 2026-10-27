module

public import CFSG.Quasithin.Vol2.KGFactC31HeData
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.C31Insp
public import CFSG.Quasithin.Vol2.KGFactC31Cover
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.SectionRank.QTK.Insp443.He

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Quasithin.KGC31.He

@[expose] def x7W : List ℤ := decodeW "bababababbaba2a22221b121bbb122121b121b1bb1221bb122212222221b\
  b12221222212222121221212212bbbababbababbababbbbbbbbababbabbbbabbbabbbbaba2abbba222ababba222121212\
  a2a2a2a2121b121bbbabbabbba222a2aba22abbabbbbababbabbbbaba2ababba22a2abbba22222aba21221b1ba2a2221b\
  ababababbaba2a22221bbb12221b1bb122121b12122221221212222221bb122212222222212122122212222221212abbb\
  b1b121221212121ba222ababba222abbb122121222222121222212221222222121222221bb1bbb122122212122"

@[expose] def c7W : List ℤ := decodeW "2121b12221b1ba2abbbbb1221bb12221b1bb122212222221bb1221212222\
  1221b12212121baba222aba22a2abbbbbb12121212221222babbababbababbbbabbbbabbba22abbbbbbabbba22abba22a\
  2aba2ababba222aba2abbbb1b1212212121212"

@[expose] def l7GenW : List (List ℤ) := [x7W, c7W ++ x7W ++ invW c7W]

@[expose] def l7Der : List (List ℤ) := decodeWs "a21121b aba22122aaa2abbaa"

@[expose] def l7S : Array (Array ℕ) :=
  l7Der.foldl (fun S w => S.push (wordA 8330 S (S.map (invCand 8330)) w)) (l7GenW.map wA).toArray

@[expose] def l7Wd : Array (List ℤ) :=
  (List.replicate l7GenW.length ([] : List ℤ) ++ l7Der).toArray

@[expose] def l7B : Vector (Fin 8330) 2 := #v[0, 1]

end CFSG.SectionRank.QTK.Insp443.He

end
