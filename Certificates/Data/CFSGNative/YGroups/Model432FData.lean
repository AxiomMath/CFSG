module

public import Certificates.Data.CFSGNative.YGroups.ExactData

public section

namespace CFSG.YGroups.ModelNative

@[expose] def y432FPermText : String := y432PermText

@[expose] def y432FChainText : String := include_str "../../../../CFSG/YGroups/Data/y432F-chain.txt"

@[expose] def y432CChainText : String := include_str "../../../../CFSG/YGroups/Data/y432C-chain.txt"

end CFSG.YGroups.ModelNative
