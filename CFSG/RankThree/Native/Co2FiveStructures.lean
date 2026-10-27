module

public import CFSG.RankThree.Native.Co2FiveDefs
public import CFSG.RankThree.Native.Co2FiveCheckInputs
public import CFSG.Sporadic.Co2Cert.Cert

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert

structure Co2FiveStructures : Prop where
  q_le_P : co2FiveQ ≤ co2P
  q_sylow : ∃ S : Sylow 5 co2P, (S : Subgroup co2P) = co2FiveQ.subgroupOf co2P
  card_Q : Nat.card co2FiveQ = 125
  exponent_Q : Monoid.exponent co2FiveQ = 5
  lines : {H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} =
      Set.range (fun j : Fin 31 => Subgroup.zpowers (co2FiveLine j)) ∧
    Function.Injective (fun j : Fin 31 => Subgroup.zpowers (co2FiveLine j))
  transporter : ∀ j : Fin 31, co2FiveTransporter j ∈ co2P ∧
    co2FiveTransporter j * co2FiveLine (co2FiveRepLine (co2FiveRecordOf j)) *
      (co2FiveTransporter j)⁻¹ = co2FiveLine j
  c0_eq : co2FiveC0 = Subgroup.centralizer {co2FiveLine 0} ⊓ co2P
  card_C0 : Nat.card co2FiveC0 = 3000
  a_le_C0 : co2FiveA ≤ co2FiveC0
  a_normal : (co2FiveA.subgroupOf co2FiveC0).Normal
  centA_eq : Subgroup.centralizer (co2FiveA : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC0 =
    Subgroup.zpowers (co2FiveLine 0)
  c1_eq : co2FiveC1 = Subgroup.centralizer {co2FiveLine 1} ⊓ co2P
  card_C1 : Nat.card co2FiveC1 = 600
  d_simple : IsSimpleGroup co2FiveD
  d_nonabelian : ∃ g ∈ co2FiveD, ∃ h ∈ co2FiveD, g * h ≠ h * g
  card_D : Nat.card co2FiveD = 60
  centD_eq : Subgroup.centralizer (co2FiveD : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC1 =
    Subgroup.zpowers (co2FiveLine 1)
  line_rep : ∀ j : Fin 31, Rep 2300 (co2FiveLineArr j) (co2FiveLine j)
  q_enum : ∀ x, x ∈ co2FiveQ ↔ ∃ i < co2FiveQCert.pts.size, permOfArr 2300 co2FiveQCert.pts[i]! = x
  q_rep : ∀ i < co2FiveQCert.pts.size,
    Rep 2300 co2FiveQCert.pts[i]! (permOfArr 2300 co2FiveQCert.pts[i]!)
  c0_enum : ∀ x, x ∈ co2FiveC0 ↔
    ∃ i < co2FiveC0Cert.pts.size, permOfArr 2300 co2FiveC0Cert.pts[i]! = x
  c0_rep : ∀ i < co2FiveC0Cert.pts.size,
    Rep 2300 co2FiveC0Cert.pts[i]! (permOfArr 2300 co2FiveC0Cert.pts[i]!)

end CFSG.RankThree.Native

end
