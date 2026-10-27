module
public import CFSG.Sporadic.HNSchreier.IncludeGiantArchive
public meta import CFSG.Sporadic.HNSchreier.IncludeGiantArchive

public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace CFSG.Sporadic.HNSchreier.Native

@[expose] noncomputable def archiveGiantBytes (_ : Unit := ()) : KernelBytes := giant_archive%

theorem archiveGiantBytes_bytes :
    (archiveKernelBytes ()).bytes = (archiveGiantBytes ()).bytes := giant_archive_eq%

theorem archiveGiantBytes_toByteArray :
    (archiveKernelBytes ()).toByteArray = (archiveGiantBytes ()).toByteArray := by
  unfold KernelBytes.toByteArray
  rw [archiveGiantBytes_bytes]

end CFSG.Sporadic.HNSchreier.Native
