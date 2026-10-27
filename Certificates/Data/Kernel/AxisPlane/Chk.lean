module

public import Certificates.Data.Kernel.AxisPlane.Plane

public section

namespace CFSG.KC.AxisPlane

structure PlanesChk (opss rls : List (List Nat)) (Ls Qs : List Nat) (Rss : List (List Nat))
    (lams sizes : List Nat) : Prop where
  len_Rss : Rss.length = opss.length
  ops_ok : ∀ g < opss.length, opsOK (opss.getD g []) (rls.getD g []) = true
  inv : ∀ g < opss.length, ∀ b < Ls.length, invK (opss.getD g []) (Ls.getD b 0) = true
  img_len : ∀ g < opss.length, (Rss.getD g []).length = Qs.length
  img : ∀ g < opss.length, ∀ j < Qs.length,
    imgEqK (opss.getD g []) (Qs.getD j 0) ((Rss.getD g []).getD j 0) = true
  gen : genK Qs Rss = true
  cov : covK Ls Qs = true
  seeds : seedsK Ls Qs lams = true
  d0 : d0K Qs lams = true
  qs_pos : 0 < Qs.length
  lams_lt : lams.length < 2 ^ Ls.length
  len_sizes : sizes.length = lams.length
  cnt : ∀ r < lams.length, cntK Ls (r + 1) (sizes.getD r 0) = true

end CFSG.KC.AxisPlane

end
