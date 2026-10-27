module

public import CFSG.Quasithin.Vol2.F134M12Inputs
public import CFSG.Quasithin.Recognition.CertPermList
public import CFSG.Quasithin.Vol2.F134Basic

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.F134 CFSG.Quasithin.M12Amal CFSG.Quasithin.P134 Equiv

namespace CertificateChecks.Batch17019

open CFSG CFSG.Quasithin CFSG.Quasithin.F134 CFSG.Quasithin.M12Amal CFSG.Quasithin.P134 Equiv

private theorem m12ATab_one_0 : List.range 12 ∈ m12ATab := by
  decide +kernel

private theorem m12BTab_one_1 : List.range 12 ∈ m12BTab := by
  decide +kernel

private theorem m12ATab_closed_2 : ∀ l ∈ m12ATab, ∀ k ∈ [0, 1, 2, 3], compL l (genTab.getD k []) ∈ m12ATab := by
  decide +kernel

private theorem m12BTab_closed_3 : ∀ l ∈ m12BTab, ∀ k ∈ [0, 1, 2, 4], compL l (genTab.getD k []) ∈ m12BTab := by
  decide +kernel

private theorem m12ATab_length_4 : m12ATab.length = 192 := by
  decide +kernel

private theorem m12BTab_length_5 : m12BTab.length = 192 := by
  decide +kernel

end CertificateChecks.Batch17019

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.F134 CFSG.Quasithin.M12Amal CFSG.Quasithin.P134 Equiv in
theorem certificate17019 : (
 List.range 12 ∈ m12ATab 
)
    ∧ (
 List.range 12 ∈ m12BTab 
)
    ∧ (

    ∀ l ∈ m12ATab, ∀ k ∈ [0, 1, 2, 3], compL l (genTab.getD k []) ∈ m12ATab 
)
    ∧ (

    ∀ l ∈ m12BTab, ∀ k ∈ [0, 1, 2, 4], compL l (genTab.getD k []) ∈ m12BTab 
)
    ∧ (
 m12ATab.length = 192 
)
    ∧ (
 m12BTab.length = 192 
) := by
  exact ⟨@CertificateChecks.Batch17019.m12ATab_one_0, @CertificateChecks.Batch17019.m12BTab_one_1, @CertificateChecks.Batch17019.m12ATab_closed_2, @CertificateChecks.Batch17019.m12BTab_closed_3, @CertificateChecks.Batch17019.m12ATab_length_4, @CertificateChecks.Batch17019.m12BTab_length_5⟩

end Certificates
