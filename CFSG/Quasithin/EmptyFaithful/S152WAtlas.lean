module

public import CFSG.Quasithin.EmptyFaithful.S152WRank2
public import CFSG.Quasithin.EmptyFaithful.S152WMathieu
public import CFSG.Quasithin.EmptyFaithful.S152WJ2
public import CFSG.Quasithin.EmptyFaithful.S152WHS
public import CFSG.Quasithin.EmptyFaithful.S152WHe
public import CFSG.Quasithin.EmptyFaithful.S152WRu

public section

namespace CFSG.Quasithin

open CFSG.Blueprint S152W

theorem sporadicInvolutionAtlas_of_certificates :
    SporadicInvolutionAtlas := by
  intro s hs Γ _ _ hΓ
  obtain ⟨e⟩ := hΓ
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact atlas_statement_of_clauses (AtlasClauses.of_equiv e atlasClauses_M11)
  · exact atlas_statement_of_clauses (AtlasClauses.of_equiv e atlasClauses_M12)
  · exact atlas_statement_of_clauses (AtlasClauses.of_equiv e atlasClauses_M22)
  · exact atlas_statement_of_clauses (AtlasClauses.of_equiv e atlasClauses_M23)
  · exact atlas_statement_of_clauses (AtlasClauses.of_equiv e atlasClauses_M24)
  · exact atlas_statement_of_clauses (AtlasClauses.of_equiv e atlasClauses_J2)
  · exact atlas_statement_of_clauses (AtlasClauses.of_equiv e atlasClauses_HS)
  · exact atlas_statement_of_clauses (atlasClauses_He e)
  · exact atlas_statement_of_clauses (AtlasClauses.of_equiv e atlasClauses_Ru)

theorem sporadicInvolution3Rank_of_certificates :
    SporadicInvolution3Rank :=
  sporadicInvolution3Rank_of_atlas sporadicInvolutionAtlas_of_certificates

end CFSG.Quasithin
