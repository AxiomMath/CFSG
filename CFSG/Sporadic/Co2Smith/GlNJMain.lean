module

public import CFSG.Sporadic.Co2Smith.GlNJG6
public import CFSG.Sporadic.Co2Smith.GlWMain
public import CFSG.Sporadic.Co2Smith.GlNJG5

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.RankThree.Co2 CFSG.Certificates

theorem smithNJChart :
    SmithNJChart := by
  intro G _ _ z _ hG φ _
  have hz : orderOf z = 2 := hG.orderOf_eq
  have hφz := φ_zH hz φ
  obtain ⟨L, hL, s, hs4, hLs⟩ := exists_NJComp_QKs φ hz hφz
  rcases hs4 with rfl | rfl | rfl | rfl
  · exact ⟨chartOf φ hz hφz hL hLs (fun _ h1 h2 => LK_inf_Jc h1 h2)
      (fun _ hσ => exists_LK_piK hσ),
      isNJChart_chartOf φ hz hφz hL hLs _ _ (fun _ h1 h2 => LK_inf_Cz_le h1 h2)⟩
  · exact (not_comp_fusion φ hz hφz hL (Or.inl rfl) hLs).elim
  · exact ⟨chartOf φ hz hφz hL hLs (fun _ h1 h2 => LKt_inf_Jc h1 h2)
      (fun _ hσ => exists_LKt_piK hσ),
      isNJChart_chartOf φ hz hφz hL hLs _ _ (fun _ h1 h2 => LKt_inf_Cz_le h1 h2)⟩
  · exact (not_comp_fusion φ hz hφz hL (Or.inr rfl) hLs).elim

theorem smithC0Input :
    SmithC0Input C0c α3c :=
  smithC0Input_of_NJChart smithNJChart

end CFSG.Sporadic.Co2Smith
