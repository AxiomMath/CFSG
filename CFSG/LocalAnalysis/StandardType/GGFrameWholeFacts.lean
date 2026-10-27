module

public import Certificates.Certificate709590
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType.FrameRoute

theorem frameWhole_facts {n N d : ℕ}
    (h : (n = 6 ∧ N = 36 ∧ d = 20) ∨ (n = 7 ∧ N = 63 ∧ d = 32) ∨ (n = 8 ∧ N = 120 ∧ d = 56)) :
    (feT n).ncard = N ∧ (∀ r ∈ feT n, {t | t ∈ feT n ∧ r * t ≠ t * r}.ncard = d) ∧
      ∀ r ∈ feT n, ∀ t ∈ feT n,
        Relation.ReflTransGen (fun a b => a ∈ feT n ∧ b ∈ feT n ∧ a * b ≠ b * a) r t :=
  Certificates.certificate709590 h

end CFSG.StandardType.FrameRoute

end
