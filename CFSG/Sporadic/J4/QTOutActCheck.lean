module

public import CFSG.Sporadic.J4.QTOutActNative
public meta import CFSG.Sporadic.J4.QTOutActNative
public import CFSG.Sporadic.J4.QTCheck
public import CFSG.Sporadic.J4.QTRankCheck
public import Certificates.Certificate4018

public section

namespace CFSG.Sporadic.J4.QT

theorem orbits_shape :
    orbits.length = 2 ∧ (orbits.getD 0 (0, [], [])).1 = 1 ∧
    (orbits.getD 1 (0, [], [])).1 = 3 :=
  Certificates.certificate4018.1

theorem o1_len : o1.length = 276 ∧ o1.Nodup :=
  Certificates.certificate4018.2.1

theorem o2_len : o2.length = 1771 ∧ o2.Nodup :=
  Certificates.certificate4018.2.2.1

theorem o_lt : ∀ c ∈ o1 ++ o2, c < 2 ^ 11 ∧ c ≠ 0 :=
  Certificates.certificate4018.2.2.2.1

theorem o_cover : ∀ c < 2 ^ 11, c ≠ 0 → c ∈ o1 ∨ c ∈ o2 :=
  Certificates.certificate4018.2.2.2.2.1

theorem o_disj : ∀ c ∈ o1, c ∉ o2 :=
  Certificates.certificate4018.2.2.2.2.2.1

theorem o_roots : 1 ∈ o1 ∧ 3 ∈ o2 :=
  Certificates.certificate4018.2.2.2.2.2.2.1

theorem o_closed :
    (∀ c ∈ o1, ∀ ℓ ∈ letters, act ℓ c ∈ o1) ∧ ∀ c ∈ o2, ∀ ℓ ∈ letters, act ℓ c ∈ o2 :=
  Certificates.certificate4018.2.2.2.2.2.2.2.1

theorem tp_period : ∀ c < 2 ^ 11, actT (tp 23) c = c :=
  Certificates.certificate4018.2.2.2.2.2.2.2.2.1

theorem tp_ok : ∀ n < 23, lenOK (tp n) = true :=
  Certificates.certificate4018.2.2.2.2.2.2.2.2.2.1

theorem kcomb_kinv :
    ∀ c < 2 ^ 11, kcomb (kinv.getD c 0) = c ∧ kinv.getD c 0 < 2 ^ 11 :=
  Certificates.certificate4018.2.2.2.2.2.2.2.2.2.2.1

theorem hWord_letters : ∀ ℓ ∈ hWord, ℓ ∈ letters :=
  Certificates.certificate4018.2.2.2.2.2.2.2.2.2.2.2.1

theorem surv_all :
    ∀ s < 23, s ≠ 0 → ∀ w ∈ o1, survOK s w = true → survIn s w = true :=
  Certificates.certificate4018.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.J4.QT
