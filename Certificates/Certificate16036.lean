module

public import CFSG.Monster.B.E6.StdF4RadicalLeviInputs

public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4Radical
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension

namespace CertificateChecks.Batch16036

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4Radical
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension

private theorem isRoot_levRoot_0 : (List.range 10).all (fun c => (List.range 72).any fun l =>
      List.ofFn (e6Certificate.root l) == List.ofFn (levRoot c)) = true := by
  decide +kernel

private theorem levRoot_one_1 : (List.range 10).all (fun c => levRoot c 1 == 0) = true := by
  decide +kernel

private theorem levAddCheck_2 : (List.range 10).all (fun c => (List.range 21).all fun k =>
    if levAdd c k < 21 then List.ofFn (rr (levAdd c k)) == List.ofFn (levRoot c + rr k)
    else (List.range 21).all fun l => List.ofFn (rr l) != List.ofFn (levRoot c + rr k)) = true := by
  decide +kernel

private theorem leviQCheck_3 : (List.range 6).all (fun k => (List.range 15).all fun i =>
    inQMask (nfWM (leviConjW k (orbIdx i)))) = true := by
  decide +kernel

private theorem leviTCheck_4 :
    (List.range 6).all (fun k => nfWM (leviConjW k [20]) == nfWM [20]) = true := by
  decide +kernel

private theorem centerCheck_5 : (List.range 6).all (fun k => (List.range 7).all fun i =>
    if hk : k < 6 then if hi : i < 7 then
      nfWM (leviConjW k (orbIdx (zIdx i))) == nfWM (zWordOf (centerCols ⟨k, hk⟩ ⟨i, hi⟩))
    else false else false) = true := by
  decide +kernel

private theorem levPairCheck_6 : (List.range 4).all (fun p =>
    let a := levRoot (2 * p + 2); let b := levRoot (2 * p + 3)
    (List.range 72).all (fun l => List.ofFn (e6Certificate.root l) != List.ofFn (a + b)) &&
      List.ofFn a != List.ofFn b && List.ofFn a != List.ofFn (-b)) = true := by
  decide +kernel

private theorem levRhoCheck_7 : (List.range 10).all (fun c =>
    List.ofFn (rho (levRoot c)) == List.ofFn (levRoot ([0, 1, 3, 2, 5, 4, 7, 6, 9, 8].getD c 0)))
    = true := by
  decide +kernel

private theorem height_levRoot_pos_8 :
    [0, 2, 3, 6, 7].all (fun c => decide (0 < height (levRoot c))) = true := by
  decide +kernel

private theorem height_levRoot_neg_9 :
    [1, 4, 5, 8, 9].all (fun c => decide (height (levRoot c) < 0)) = true := by
  decide +kernel

end CertificateChecks.Batch16036

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4Radical
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension in
theorem certificate16036 : (
    (List.range 10).all (fun c => (List.range 72).any fun l =>
        List.ofFn (e6Certificate.root l) == List.ofFn (levRoot c)) = true
  ) ∧ (
    (List.range 10).all (fun c => levRoot c 1 == 0) = true
  ) ∧ (
    (List.range 10).all (fun c => (List.range 21).all fun k =>
      if levAdd c k < 21 then List.ofFn (rr (levAdd c k)) == List.ofFn (levRoot c + rr k)
      else (List.range 21).all fun l => List.ofFn (rr l) != List.ofFn (levRoot c + rr k)) = true
  ) ∧ (
    (List.range 6).all (fun k => (List.range 15).all fun i =>
      inQMask (nfWM (leviConjW k (orbIdx i)))) = true
  ) ∧ (
    (List.range 6).all (fun k => nfWM (leviConjW k [20]) == nfWM [20]) = true
  ) ∧ (
    (List.range 6).all (fun k => (List.range 7).all fun i =>
      if hk : k < 6 then if hi : i < 7 then
        nfWM (leviConjW k (orbIdx (zIdx i))) == nfWM (zWordOf (centerCols ⟨k, hk⟩ ⟨i, hi⟩))
      else false else false) = true
  ) ∧ (
    (List.range 4).all (fun p =>
      let a := levRoot (2 * p + 2); let b := levRoot (2 * p + 3)
      (List.range 72).all (fun l => List.ofFn (e6Certificate.root l) != List.ofFn (a + b)) &&
        List.ofFn a != List.ofFn b && List.ofFn a != List.ofFn (-b)) = true
  ) ∧ (
    (List.range 10).all (fun c =>
      List.ofFn (rho (levRoot c)) ==
        List.ofFn (levRoot ([0, 1, 3, 2, 5, 4, 7, 6, 9, 8].getD c 0))) = true
  ) ∧ (
    [0, 2, 3, 6, 7].all (fun c => decide (0 < height (levRoot c))) = true
  ) ∧ (
    [1, 4, 5, 8, 9].all (fun c => decide (height (levRoot c) < 0)) = true
  ) := by
  exact ⟨CertificateChecks.Batch16036.isRoot_levRoot_0, CertificateChecks.Batch16036.levRoot_one_1, CertificateChecks.Batch16036.levAddCheck_2,
    CertificateChecks.Batch16036.leviQCheck_3, CertificateChecks.Batch16036.leviTCheck_4, CertificateChecks.Batch16036.centerCheck_5,
    CertificateChecks.Batch16036.levPairCheck_6, CertificateChecks.Batch16036.levRhoCheck_7, CertificateChecks.Batch16036.height_levRoot_pos_8,
    CertificateChecks.Batch16036.height_levRoot_neg_9⟩

end Certificates
