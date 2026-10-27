module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImagesQuotient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

universe u

theorem properStrongEmbeddingCommutingImages
    (G : Type u) [Group G] [Finite G] : ProperStrongEmbeddingCommutingImages G := by
  intro K _ hrank M hM a b haM haorder hbM hborder
  exact properCommutingImages_quotient_involutions_commute_of_twoRank M
    (native_strong_embedding_of_order_conditions hM) hrank a b haM haorder hbM hborder

end CFSG.ShultStronglyClosedTI
