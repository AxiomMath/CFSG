module

public import CFSG.Quasithin.Vol2.Ch11SecGTCase1
public import CFSG.Quasithin.Vol2.Ch11SecGTCase2
public import CFSG.Quasithin.Vol2.Ch11SecGFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem mQuot_anti_right {G : Type} [Group G] [Finite G] {V U U' : Subgroup G} (hV : IsPGroup 2 V)
    (hUU' : U ≤ U') : E3.mQuot V U' ≤ E3.mQuot V U := by
  have hdvd : U'.relIndex V ∣ U.relIndex V := Subgroup.relIndex_dvd_of_le_left V hUU'
  rw [E3.relIndex_eq_two_pow hV U, E3.relIndex_eq_two_pow hV U'] at hdvd
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd

theorem factTransv11_5_8_of (hInv : FactL2pInvol) (hMod5 : FactL2pListMod5)
    (hShape : FactCase1Shape) : FactTransv11_5_8 := by
  intro G _ _ H K T L₁ Y A _ hKH hHK hT hKT hKK hlist hcase hL _ hL4 hcl _ hHY hY hCL hAH hA hAO
    hm
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL4
  obtain ⟨a, haA, haO⟩ := IsConcreteLE.not_le_iff_exists.mp hAO
  have ha : a ∈ H := hAH haA
  obtain ⟨n, hn⟩ := hA ⟨a, haA⟩
  have han : a ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hm' : E3.mQuot Y (Y ⊓ Subgroup.centralizer ({a} : Set G)) ≤ 1 := by
    refine le_trans (mQuot_anti_right (F7.isPGroup_of_isElemAbelian hY) ?_) hm
    exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  obtain ⟨y₀, hy₀, htr⟩ := exists_transv_of_mQuot hY (hHY ha) hm'
  have ha2 := sq_mem_centralizer_of_transv hY hy₀ htr
  rcases hcase with h1 | ⟨p, hp, hp11, hPSL⟩
  · exact haO (mem_pCoreOf_of_case1 hKH hHK hT hKT hKK hL hF e hcl hHY hY hCL ha han hy₀ htr ha2
      (case1Struct_of_fact hShape hlist h1))
  · have hp17 : p ≠ 17 := by
      intro h17
      have h5 := hMod5 _ p hp hp11 hPSL hlist
      subst h17
      omega
    exact haO (mem_pCoreOf_of_case2 hInv hKH hHK hT hKT hKK hL hF e hcl hHY hY hCL ha han hy₀ htr
      ha2 hp hp11 hp17 hPSL)

end CFSG.Quasithin.Vol2.Ch11.SecG
