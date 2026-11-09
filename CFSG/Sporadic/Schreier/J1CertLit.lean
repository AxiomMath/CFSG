module

public import CFSG.Sporadic.Schreier.J1CertTypes
import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

namespace CFSG.Sporadic.Schreier

open CFSG.Monster.B.Mathieu

set_option maxHeartbeats 2000000 in
#kc_repo #kc_json_eval CFSG.Sporadic.Schreier
  "CFSG/Sporadic/Schreier/Data/j1-cert-lit.json" 1796505 13257893504543277780
  (j1G0 : List ℕ)
  (j1G1 : List ℕ)
  (j1S0 : List ℕ)
  (j1S1 : List ℕ)
  (j1S2 : List ℕ)
  (j1S3 : List ℕ)
  (j1VecsLit : List (List ℕ))
  (j1Y0G0 : List ℕ)
  (j1Y0G1 : List ℕ)
  (j1Y0G2 : List ℕ)
  (j1Y0N0R : List ℕ)
  (j1Y0N0G0 : List ℕ)
  (j1Y0N0G1 : List ℕ)
  (j1Y0N0G2 : List ℕ)
  (j1Y0N0S0 : List ℕ)
  (j1Y0N0S1 : List ℕ)
  (j1Y0N0S2 : List ℕ)
  (j1Y0N0S3 : List ℕ)
  (j1Y0N0S4 : List ℕ)
  (j1Y0N0S5 : List ℕ)
  (j1Y0N1R : List ℕ)
  (j1Y0N1G0 : List ℕ)
  (j1Y0N1G1 : List ℕ)
  (j1Y0N1G2 : List ℕ)
  (j1Y0N1S0 : List ℕ)
  (j1Y0N1S1 : List ℕ)
  (j1Y0N1S2 : List ℕ)
  (j1Y0N1S3 : List ℕ)
  (j1Y0N1S4 : List ℕ)
  (j1Y0N1S5 : List ℕ)
  (j1Y0N2R : List ℕ)
  (j1Y0N2G0 : List ℕ)
  (j1Y0N2G1 : List ℕ)
  (j1Y0N2G2 : List ℕ)
  (j1Y0N2S0 : List ℕ)
  (j1Y0N2S1 : List ℕ)
  (j1Y0N2S2 : List ℕ)
  (j1Y0N2S3 : List ℕ)
  (j1Y0N2S4 : List ℕ)
  (j1Y0N2S5 : List ℕ)
  (j1Y0N3R : List ℕ)
  (j1Y0N3G0 : List ℕ)
  (j1Y0N3G1 : List ℕ)
  (j1Y0N3G2 : List ℕ)
  (j1Y0N3S0 : List ℕ)
  (j1Y0N3S1 : List ℕ)
  (j1Y0N3S2 : List ℕ)
  (j1Y0N3S3 : List ℕ)
  (j1Y0N3S4 : List ℕ)
  (j1Y0N4R : List ℕ)
  (j1Y0N4G0 : List ℕ)
  (j1Y0N4G1 : List ℕ)
  (j1Y0N4G2 : List ℕ)
  (j1Y0N4S0 : List ℕ)
  (j1Y0N4S1 : List ℕ)
  (j1Y0N4S2 : List ℕ)
  (j1Y0N4S3 : List ℕ)
  (j1Y0N4S4 : List ℕ)
  (j1Y0N4S5 : List ℕ)
  (j1Y0N5R : List ℕ)
  (j1Y0N5G0 : List ℕ)
  (j1Y0N5G1 : List ℕ)
  (j1Y0N5G2 : List ℕ)
  (j1Y0N5S0 : List ℕ)
  (j1Y0N5S1 : List ℕ)
  (j1Y0N5S2 : List ℕ)
  (j1Y0N5S3 : List ℕ)
  (j1Y0N5S4 : List ℕ)
  (j1Y0N5S5 : List ℕ)
  (j1Y0N6R : List ℕ)
  (j1Y0N6G0 : List ℕ)
  (j1Y0N6G1 : List ℕ)
  (j1Y0N6G2 : List ℕ)
  (j1Y0N6S0 : List ℕ)
  (j1Y0N6S1 : List ℕ)
  (j1Y0N6S2 : List ℕ)
  (j1Y0N6S3 : List ℕ)
  (j1Y0N6S4 : List ℕ)
  (j1Y1G0 : List ℕ)
  (j1Y1N0R : List ℕ)
  (j1Y1N0G0 : List ℕ)
  (j1Y1N0G1 : List ℕ)
  (j1Y1N0G2 : List ℕ)
  (j1Y1N0S0 : List ℕ)
  (j1Y1N0S1 : List ℕ)
  (j1Y1N0S2 : List ℕ)
  (j1Y1N0S3 : List ℕ)
  (j1Y1N0S4 : List ℕ)
  (j1Y1N0S5 : List ℕ)
  (j1Y2G0 : List ℕ)
  (j1Y2N0R : List ℕ)
  (j1Y2N0G0 : List ℕ)
  (j1Y2N0G1 : List ℕ)
  (j1Y2N0S0 : List ℕ)
  (j1Y2N0S1 : List ℕ)
  (j1Y2N0S2 : List ℕ)
  (j1Y2N0S3 : List ℕ)
  (j1Y2N0S4 : List ℕ)
  (j1Y3G0 : List ℕ)
  (j1Y3N0R : List ℕ)
  (j1Y3N0G0 : List ℕ)
  (j1Y3N0G1 : List ℕ)
  (j1Y3N0S0 : List ℕ)
  (j1Y3N0S1 : List ℕ)
  (j1Y3N0S2 : List ℕ)
  (j1Y3N0S3 : List ℕ)
  (j1Y3N0S4 : List ℕ)
  (j1Y4G0 : List ℕ)
  (j1Y4N0R : List ℕ)
  (j1Y4N0G0 : List ℕ)
  (j1Y4N0G1 : List ℕ)
  (j1Y4N0S0 : List ℕ)
  (j1Y4N0S1 : List ℕ)
  (j1Y4N0S2 : List ℕ)
  (j1Y4N0S3 : List ℕ)
  (j1Y5G0 : List ℕ)
  (j1Y5N0R : List ℕ)
  (j1Y5N0G0 : List ℕ)
  (j1Y5N0G1 : List ℕ)
  (j1Y5N0S0 : List ℕ)
  (j1Y5N0S1 : List ℕ)
  (j1Y5N0S2 : List ℕ)
  (j1Y5N0S3 : List ℕ)

@[expose] def j1Chain : ChainRecord :=
  ⟨3080, [j1G0, j1G1],
    [0, 1, 2],
    [j1S0, j1S1, j1S2, j1S3],
    [[1, -2, -2, 1, 2, 2, 1, 2],
      [-3, -3, -3, 1, -2, 1, -2, -2, 1, -2, 1, -2, 1, -2, -2, 1, -2, 1, -2, -2, 1, -2, 1, 2, 1,
      2, 1, 2,
  2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1]]⟩

@[expose] def j1Y0N0C : List (List ℤ) :=
  [[-2, -2, -2, 2, -1, 1, 2, -1, -2, -1, -2, 1], [-1, -2, -2, 1, -1, -2, -2, -1, 2, 2, 2, -2],
    [-2, 2, 1, 1, 2, -1, 2, -2, 1, -1, -1, 2]]

@[expose] def j1Y0N0Chain : ChainRecord :=
  ⟨3080, [j1Y0N0G0, j1Y0N0G1, j1Y0N0G2],
    [0, 1, 2],
    [j1Y0N0S0, j1Y0N0S1, j1Y0N0S2, j1Y0N0S3, j1Y0N0S4, j1Y0N0S5],
    [[2, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 2], [1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1],
      [-5, -5, 4, 4, 5]]⟩

@[expose] def j1Y0N0 : NormalGenRecord :=
  ⟨j1Y0N0R, j1Y0N0C, j1Y0N0Chain⟩

@[expose] def j1Y0N1C : List (List ℤ) :=
  [[-1, 2, 1, -1, 2, -2, 2, -2, -2, -1, 2, -2], [2, -2, 1, 2, -2, 2, -2, 2, 1, 1, -2, -2],
    [-1, -2, -1, 1, 2, 2, 1, 1, -1, 1, 1, -1]]

@[expose] def j1Y0N1Chain : ChainRecord :=
  ⟨3080, [j1Y0N1G0, j1Y0N1G1, j1Y0N1G2],
    [0, 1, 2],
    [j1Y0N1S0, j1Y0N1S1, j1Y0N1S2, j1Y0N1S3, j1Y0N1S4, j1Y0N1S5],
    [[1, 2, 1, 3, 2, 1, 2, 1, 3, 2], [2, 1, 2, 1, 3, 2, 1, 2, 1, 3], [-5, -5, 4, 4, 5]]⟩

@[expose] def j1Y0N1 : NormalGenRecord :=
  ⟨j1Y0N1R, j1Y0N1C, j1Y0N1Chain⟩

@[expose] def j1Y0N2C : List (List ℤ) :=
  [[1, 2, -1, 1, -1, -2, 2, 2, 2, 2, -1, -1], [-2, 1, 2, -2, -1, 2, -2, -2, -1, 2, -2, 1],
    [1, -2, -1, 2, 2, 1, 1, 2, -2, -1, 1, 2]]

@[expose] def j1Y0N2Chain : ChainRecord :=
  ⟨3080, [j1Y0N2G0, j1Y0N2G1, j1Y0N2G2],
    [0, 1, 2],
    [j1Y0N2S0, j1Y0N2S1, j1Y0N2S2, j1Y0N2S3, j1Y0N2S4, j1Y0N2S5],
    [[2, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1], [1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3], [-4, -4, 5, 4]]⟩

@[expose] def j1Y0N2 : NormalGenRecord :=
  ⟨j1Y0N2R, j1Y0N2C, j1Y0N2Chain⟩

@[expose] def j1Y0N3C : List (List ℤ) :=
  [[2, -2, -1, 2, 2, 1, 2, 2, -1, -1, 2, -1], [1, 2, -1, -2, 1, 1, 1, -2, -1, -1, 2, 2],
    [2, -2, -2, -1, -1, 2, -2, 2, 2, -1, 1, 2]]

@[expose] def j1Y0N3Chain : ChainRecord :=
  ⟨3080, [j1Y0N3G0, j1Y0N3G1, j1Y0N3G2],
    [0, 1, 2],
    [j1Y0N3S0, j1Y0N3S1, j1Y0N3S2, j1Y0N3S3, j1Y0N3S4],
    [[2, 1, 3, 2, 1, 2, 3, 2, 1], [-4, -4, -4, -4, -4, 3, 2, 1, 3, 2, 3, 2, 3, 2]]⟩

@[expose] def j1Y0N3 : NormalGenRecord :=
  ⟨j1Y0N3R, j1Y0N3C, j1Y0N3Chain⟩

@[expose] def j1Y0N4C : List (List ℤ) :=
  [[1, 1, 2, -2, 1, -1, 1, -1, -1, -1, -1, -1], [-2, -1, -2, 2, 2, 2, 2, -2, 1, -2, 2, -2],
    [-2, -2, 2, 2, 2, -1, 1, 2, 2, -1, 2, -2]]

@[expose] def j1Y0N4Chain : ChainRecord :=
  ⟨3080, [j1Y0N4G0, j1Y0N4G1, j1Y0N4G2],
    [0, 1, 2],
    [j1Y0N4S0, j1Y0N4S1, j1Y0N4S2, j1Y0N4S3, j1Y0N4S4, j1Y0N4S5],
    [[3, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1], [2, 1, 3, 2, 3, 1, 3, 1, 3, 2, 1, 2, 1],
      [-5, -4, -5, 4, 5, 4, 4]]⟩

@[expose] def j1Y0N4 : NormalGenRecord :=
  ⟨j1Y0N4R, j1Y0N4C, j1Y0N4Chain⟩

@[expose] def j1Y0N5C : List (List ℤ) :=
  [[1, 2, -2, 2, 1, 2, -2, -2, 2, 2, 1, 2], [2, -1, -1, -1, 1, -1, -2, 2, -2, 2, 2, -2],
    [1, -1, -1, 1, 1, 1, -1, -1, -1, 2, -2, 2]]

@[expose] def j1Y0N5Chain : ChainRecord :=
  ⟨3080, [j1Y0N5G0, j1Y0N5G1, j1Y0N5G2],
    [0, 1, 2],
    [j1Y0N5S0, j1Y0N5S1, j1Y0N5S2, j1Y0N5S3, j1Y0N5S4, j1Y0N5S5],
    [[1, 2, 3, 1, 3, 1, 2, 1, 3, 2], [1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2], [5, 5, 4]]⟩

@[expose] def j1Y0N5 : NormalGenRecord :=
  ⟨j1Y0N5R, j1Y0N5C, j1Y0N5Chain⟩

@[expose] def j1Y0N6C : List (List ℤ) :=
  [[2, -2, 2, -1, 2, -1, 2, 2, 2, 1, -1, -2], [-1, -1, 2, 1, -2, -2, 2, 2, -2, -1, 2, 2],
    [2, -1, -1, -1, -2, 1, -2, 1, 2, -1, 2, 1]]

@[expose] def j1Y0N6Chain : ChainRecord :=
  ⟨3080, [j1Y0N6G0, j1Y0N6G1, j1Y0N6G2],
    [0, 1, 2],
    [j1Y0N6S0, j1Y0N6S1, j1Y0N6S2, j1Y0N6S3, j1Y0N6S4],
    [[2, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1],
      [-4, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, 1, 2, 1, 2, 3, 1, 2, 3, 2,
      3, 1,
  3, 1, 3]]⟩

@[expose] def j1Y0N6 : NormalGenRecord :=
  ⟨j1Y0N6R, j1Y0N6C, j1Y0N6Chain⟩

@[expose] def j1Y0 : SylowRecord :=
  ⟨2, [j1Y0G0, j1Y0G1, j1Y0G2],
    [j1Y0N0, j1Y0N1, j1Y0N2, j1Y0N3, j1Y0N4, j1Y0N5, j1Y0N6]⟩

@[expose] def j1Y1N0C : List (List ℤ) :=
  [[1, -1, 2, 2, -1, -1, 1, -1, 1, -1, 1, -2], [-2, 2, 2, 1, 2, -1, 2, 1, 1, 1, -1, 2],
    [-2, 2, -2, -1, 2, -2, -2, -1, 2, 2, -1, 1]]

@[expose] def j1Y1N0Chain : ChainRecord :=
  ⟨3080, [j1Y1N0G0, j1Y1N0G1, j1Y1N0G2],
    [0, 1, 2],
    [j1Y1N0S0, j1Y1N0S1, j1Y1N0S2, j1Y1N0S3, j1Y1N0S4, j1Y1N0S5],
    [[-1, -1, -2, 1, 2, 1, 1], [-2, -2, -3, 1, 3, 2, 2], [-5, 4, 5, 4]]⟩

@[expose] def j1Y1N0 : NormalGenRecord :=
  ⟨j1Y1N0R, j1Y1N0C, j1Y1N0Chain⟩

@[expose] def j1Y1 : SylowRecord :=
  ⟨3, [j1Y1G0],
    [j1Y1N0]⟩

@[expose] def j1Y2N0C : List (List ℤ) :=
  [[-1, 1, -2, 1, 2, -1, -2, 2, -2, 2, 2, -2], [1, -2, 2, -1, 2, -2, -2, 1, -1, -2, 2, 1]]

@[expose] def j1Y2N0Chain : ChainRecord :=
  ⟨3080, [j1Y2N0G0, j1Y2N0G1],
    [0, 1, 2],
    [j1Y2N0S0, j1Y2N0S1, j1Y2N0S2, j1Y2N0S3, j1Y2N0S4],
    [[-1, -2, -1, -1, -1, -2, 1, 1, 2, 2, 2, 1, 1],
      [-1, -2, -2, -1, -2, -2, -1, 2, 2, 1, 1, 2, 1, 2], [-3, -3, -4, 3, 4, 4, 3]]⟩

@[expose] def j1Y2N0 : NormalGenRecord :=
  ⟨j1Y2N0R, j1Y2N0C, j1Y2N0Chain⟩

@[expose] def j1Y2 : SylowRecord :=
  ⟨5, [j1Y2G0],
    [j1Y2N0]⟩

@[expose] def j1Y3N0C : List (List ℤ) :=
  [[-2, -1, -2, -1, -1, -2, 1, 2, 2, 2, 2, -1], [-1, 1, -1, 1, -1, -1, -1, 1, 2, -1, -2, -2]]

@[expose] def j1Y3N0Chain : ChainRecord :=
  ⟨3080, [j1Y3N0G0, j1Y3N0G1],
    [0, 1, 2],
    [j1Y3N0S0, j1Y3N0S1, j1Y3N0S2, j1Y3N0S3, j1Y3N0S4],
    [[-1, -2, -2, -2, -1, 2, 1, 1, 1, 1, 1], [-1, -2, -1, -2, -1, -2, 1, 1, 1, 1, 1, 2],
      [-4, -3, -4, 3, 4, 3, 3]]⟩

@[expose] def j1Y3N0 : NormalGenRecord :=
  ⟨j1Y3N0R, j1Y3N0C, j1Y3N0Chain⟩

@[expose] def j1Y3 : SylowRecord :=
  ⟨7, [j1Y3G0],
    [j1Y3N0]⟩

@[expose] def j1Y4N0C : List (List ℤ) :=
  [[2, -2, -2, 1, -2, 1, 1, 2, 2, 2, 1, 1], [1, -2, 2, -2, -1, -2, 1, 1, 2, 2, 1, -1]]

@[expose] def j1Y4N0Chain : ChainRecord :=
  ⟨3080, [j1Y4N0G0, j1Y4N0G1],
    [0, 1, 2],
    [j1Y4N0S0, j1Y4N0S1, j1Y4N0S2, j1Y4N0S3],
    [[-1, -1, -1, -1, -2, 1, 2, 2, 2, 1, 1], [-3, -2, -1, 2, 1, 2, 2, 1, 1, 1]]⟩

@[expose] def j1Y4N0 : NormalGenRecord :=
  ⟨j1Y4N0R, j1Y4N0C, j1Y4N0Chain⟩

@[expose] def j1Y4 : SylowRecord :=
  ⟨11, [j1Y4G0],
    [j1Y4N0]⟩

@[expose] def j1Y5N0C : List (List ℤ) :=
  [[-2, 2, -1, -1, 1, 2, -2, 1, 1, -1, -1, 1], [-1, -1, -2, -2, -2, 2, -1, -2, -1, 2, -1, 1]]

@[expose] def j1Y5N0Chain : ChainRecord :=
  ⟨3080, [j1Y5N0G0, j1Y5N0G1],
    [0, 1, 2],
    [j1Y5N0S0, j1Y5N0S1, j1Y5N0S2, j1Y5N0S3],
    [[-2, -2, 1, 2, 2, 2], [-3, -1, -2, -1, -2, -1, -1, 2, 2, 1, 2, 1, 2]]⟩

@[expose] def j1Y5N0 : NormalGenRecord :=
  ⟨j1Y5N0R, j1Y5N0C, j1Y5N0Chain⟩

@[expose] def j1Y5 : SylowRecord :=
  ⟨19, [j1Y5G0],
    [j1Y5N0]⟩

@[expose] def j1CertLit : J1CertificateFile :=
  ⟨1, "J1", 11, 7, j1VecsLit,
    [0, 1, 2, 3, 4, 5, 6], j1Chain,
    [j1Y0, j1Y1, j1Y2, j1Y3, j1Y4, j1Y5]⟩

end CFSG.Sporadic.Schreier

end
