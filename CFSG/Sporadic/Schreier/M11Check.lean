module

public import CFSG.Sporadic.Schreier.M11Data
public meta import CFSG.Sporadic.Schreier.M11Data
public import Certificates.Certificate2191

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu

theorem m11Certificate_check :
    m11Certificate.check = true ∧ m11Certificate.orderCertificate = 7920 :=
  Certificates.certificate2191.1

theorem m11_counts :
    orderIs m11gA 2 = true ∧ orderIs m11gB 4 = true ∧ orderIs (m11gA * m11gB) 11 = true ∧
      orderIs (m11gA * m11gB * m11gA⁻¹ * m11gB⁻¹) 6 = true ∧
      (m11Elements.filter (orderIs · 2)).length = 165 ∧
      (m11Elements.filter (orderIs · 4)).length = 990 ∧
      ((m11Elements.filter (orderIs · 2) ×ˢ m11Elements.filter (orderIs · 4)).filter
        fun q => orderIs (q.1 * q.2) 11 && orderIs (q.1 * q.2 * q.1⁻¹ * q.2⁻¹) 6).length =
        15840 :=
  Certificates.certificate2191.2

end CFSG.Sporadic.Schreier
