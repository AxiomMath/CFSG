module

public import Certificates.Certificate3178

public section

namespace CFSG.Monster.B.GSide

open SimpleGraph

theorem codeAdj_σ_w : codeGraph.Adj 6144 6175 :=
  Certificates.certificate3178.1

theorem codeAdj_w_q₁ : codeGraph.Adj 6175 24606 :=
  Certificates.certificate3178.2.1

theorem codeAdj_q₁_σ : codeGraph.Adj 24606 6144 :=
  Certificates.certificate3178.2.2.1

theorem codeAdj_w_q₂ : codeGraph.Adj 6175 2652785 :=
  Certificates.certificate3178.2.2.2.1

theorem codeAdj_q₂_σ : codeGraph.Adj 2652785 6144 :=
  Certificates.certificate3178.2.2.2.2.1

theorem not_adj_q₁_q₂ : ¬ codeGraph.Adj 24606 2652785 :=
  Certificates.certificate3178.2.2.2.2.2

@[expose] def bridgeWalk : codeGraph.Walk 6144 6144 :=
  .cons codeAdj_q₁_σ.symm (.cons codeAdj_w_q₁.symm (.cons codeAdj_w_q₂ (.cons codeAdj_q₂_σ .nil)))

end CFSG.Monster.B.GSide
