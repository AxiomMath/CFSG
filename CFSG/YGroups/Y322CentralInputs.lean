module

public import CFSG.YGroups.Exact.Y322Inputs
public import Certificates.Data.CFSGNative.YGroups.Y322CentralData

@[expose] public section

namespace CFSG.YGroups


def y322WordF1 : List ℕ := (List.replicate 9 [0, 1, 2, 3, 4, 5, 6]).flatten

def y322WordF2 : List ℕ := (List.replicate 9 [0, 1, 2, 3, 6, 7, 4]).flatten

def y322HSubArrays : Array (Array ℕ) := y322Arrays.extract 0 7

def y322HActArrays : Array (Array ℕ) := ModelNative.parsePerms ModelNative.y322HPermText

end CFSG.YGroups
