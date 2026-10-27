module

public import CFSG.Monster.VisCert.CyclicSpanVis

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisCert

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible

@[expose] def pAImage : List ℕ :=
  [3, 4, 20, 0, 1, 13, 18, 11, 19, 16, 23, 7, 14, 5, 12, 22, 9, 21, 6, 8, 2, 17, 15, 10]

@[expose] def pBImage : List ℕ :=
  [3, 9, 6, 18, 4, 5, 13, 22, 8, 14, 10, 23, 15, 2, 1, 20, 16, 7, 0, 11, 12, 21, 17, 19]

@[expose] def pA : Equiv.Perm (Fin 24) where
  toFun := ![3, 4, 20, 0, 1, 13, 18, 11, 19, 16, 23, 7, 14, 5, 12, 22, 9, 21, 6, 8, 2, 17, 15, 10]
  invFun := ![3, 4, 20, 0, 1, 13, 18, 11, 19, 16, 23, 7, 14, 5, 12, 22, 9, 21, 6, 8, 2, 17, 15, 10]
  left_inv := by decide
  right_inv := by decide

@[expose] def pB : Equiv.Perm (Fin 24) where
  toFun := ![3, 9, 6, 18, 4, 5, 13, 22, 8, 14, 10, 23, 15, 2, 1, 20, 16, 7, 0, 11, 12, 21, 17, 19]
  invFun := ![18, 14, 13, 0, 4, 5, 2, 17, 8, 1, 10, 19, 20, 6, 9, 12, 16, 22, 3, 23, 15, 21, 7, 11]
  left_inv := by decide
  right_inv := by decide

theorem pA_image : ∀ i : Fin 24, (pA i : ℕ) = pAImage.getD i 0 := by decide +kernel

theorem pB_image : ∀ i : Fin 24, (pB i : ℕ) = pBImage.getD i 0 := by decide +kernel

private theorem pA_basis : ∀ i, B i ∘ ⇑pA ∈ C := by decide +kernel

private theorem pA_basis' : ∀ i, B i ∘ ⇑pA⁻¹ ∈ C := by decide +kernel

private theorem pB_basis : ∀ i, B i ∘ ⇑pB ∈ C := by decide +kernel

private theorem pB_basis' : ∀ i, B i ∘ ⇑pB⁻¹ ∈ C := by decide +kernel

theorem pA_mem : pA ∈ AutPerm := mem_AutPerm_of_basis pA_basis pA_basis'

theorem pB_mem : pB ∈ AutPerm := mem_AutPerm_of_basis pB_basis pB_basis'

@[expose] def pAAut : AutPerm := ⟨pA, pA_mem⟩

@[expose] def pBAut : AutPerm := ⟨pB, pB_mem⟩

@[expose] def frameGen (j : Fin 15) : latticeO :=
  if (j : ℕ) = 0 then xiO else if (j : ℕ) = 1 then PO pAAut else if (j : ℕ) = 2 then PO pBAut
  else gO (bC ⟨j - 3, by omega⟩)

abbrev GLV : Type := LinearMap.GeneralLinearGroup (ZMod 2) L2

@[expose] def kGen (j : Fin 15) : GLV := modTwoUnit (frameGen j)

@[expose] def Hvis : Subgroup GLV := (PvisLat.map modTwoHom).unop

@[expose] def Kvis : Subgroup GLV := Subgroup.closure (Set.range kGen)

@[expose] def Nvis : Subgroup GLV := Subgroup.closure (kGen '' {j | 1 ≤ (j : ℕ)})

@[expose] def Evis : Subgroup GLV := Subgroup.closure (kGen '' {j | 3 ≤ (j : ℕ)})

@[expose] def frameDelta : Set L2 :=
  {v | v ≠ 0 ∧ qL v = 0 ∧ ¬∃ u ∈ minVecs, classOf u = v}

@[expose] def frameMatrices : Array (Array ℕ) :=
  #[#[4096, 65536, 524288, 4194304, 8388608, 13230080, 121, 185, 314, 570, 1084, 2108, 4097, 8254,
      16446, 32830, 65538, 131133, 262205, 524292, 1048635, 2097211, 4194312, 8388624],
    #[13407452, 12978240, 8496943, 4793655, 571, 12721280, 8055318, 922424, 5209100, 8496896,
      14674188, 16194068, 32768, 65536, 13230080, 4096, 8192, 5976064, 11243520, 11911168, 8388608,
      16400384, 7163904, 1048576],
    #[615966, 8761827, 10016997, 1, 3567567, 2253033, 8761697, 10016929, 1523551, 8815265,
      11568225, 3956639, 32768, 1048576, 262144, 11243520, 65536, 131072, 5976064, 524288, 7163904,
      2097152, 7770112, 8388608],
    #[1, 122882, 581636, 4251656, 8445968, 13172768, 49279, 41151, 256, 512, 1024, 2048, 4097,
      8254, 16446, 32830, 65598, 131073, 262145, 524350, 1048577, 2097153, 4194366, 8388670],
    #[122881, 2, 651268, 4321288, 8515600, 13111328, 64, 128, 258367, 389695, 1024, 2048, 4157,
      8194, 16386, 32770, 65538, 131133, 262205, 524349, 1048578, 2097154, 4194365, 8388669],
    #[581633, 651266, 4, 4780040, 8974352, 12652576, 64, 128, 256, 512, 1635391, 2684991, 4155,
      8196, 16388, 32772, 65595, 131076, 262148, 524292, 1048635, 2097211, 4194363, 8388667],
    #[4251649, 4321282, 4780036, 8, 12644368, 8982560, 1818751, 2990271, 1818943, 2990655, 1819711,
      2992191, 4151, 8200, 16392, 32776, 65591, 131080, 262152, 524343, 1048584, 2097160, 4194312,
      8388663],
    #[8445953, 8515586, 8974340, 12644360, 16, 4788256, 3485823, 1986751, 2842943, 3486271,
      1987647, 2844735, 4143, 8208, 16400, 32784, 65583, 131088, 262160, 524335, 1048592, 2097168,
      4194351, 8388624],
    #[13172737, 13111298, 12652548, 8982536, 4788240, 32, 3027071, 3363007, 3363135, 1925695,
      1926207, 3029055, 4127, 8224, 16416, 32800, 65567, 131104, 262176, 524319, 1048608, 2097184,
      4194335, 8388639],
    #[49214, 2, 4, 1818679, 3485743, 3026975, 64, 651392, 5312768, 12182016, 4854784, 12978176,
      4160, 8256, 16511, 32895, 65600, 131136, 262208, 524352, 1048640, 2097216, 4194368, 8388672],
    #[41022, 2, 4, 2990135, 1986607, 3362847, 651328, 128, 15728896, 6361600, 9430016, 4986880,
      4224, 8383, 16512, 32959, 65664, 131200, 262272, 524416, 1048704, 2097280, 4194432, 8388736],
    #[1, 258109, 4, 1818679, 2842671, 3362847, 5312576, 15728768, 256, 582144, 4793344, 9013248,
      4352, 8448, 16640, 33024, 65792, 131328, 262463, 524544, 1048832, 2097408, 4194560, 8388864],
    #[1, 389181, 4, 2990135, 3485743, 1925151, 12181568, 6361216, 581888, 512, 12608512, 4802560,
      4608, 8704, 16896, 33280, 66048, 131647, 262656, 524800, 1049088, 2097664, 4194816, 8389120],
    #[1, 2, 1634363, 1818679, 1986607, 1925151, 4853824, 9429120, 4792576, 12608000, 1024, 124928,
      5120, 9216, 17408, 33792, 66560, 132096, 263168, 525312, 1049600, 2098239, 4195328, 8389632],
    #[1, 2, 2682939, 2990135, 2842671, 3026975, 12976192, 4984960, 9011456, 4801024, 123904, 2048,
      6144, 10240, 18432, 34816, 67584, 133120, 264192, 526336, 1050687, 2099200, 4196352, 8390656]]

@[expose] def frameSeedVec : ℕ := 63

@[expose] def fusionDeltaCount : ℕ := 8292375

@[expose] def fusionOrbitReps : Array ℕ := #[63, 61440, 13135901, 267519, 798985, 14989736]

@[expose] def fusionOrbitSizes : Array ℕ := #[1, 3542, 1457280, 48576, 2637824, 4145152]

@[expose] def ambientWords : Array (List ℕ) :=
  #[[0], [0, 1, 0], [0, 1, 0, 1, 0], [0, 1, 0, 2, 0], [0, 2, 0, 1, 0]]

structure FusionWitness where
  src : ℕ
  dst : ℕ
  v : ℕ
  w : ℕ
  srcWord : List ℕ
  dstWord : List ℕ

@[expose] def fusionWitnesses : Array (Array FusionWitness) :=
  #[#[⟨0, 1, 63, 61440, [], []⟩,
      ⟨1, 2, 13135872, 13135901, [1], []⟩,
      ⟨2, 3, 320767, 267519, [1], []⟩,
      ⟨2, 4, 5095733, 798985, [2], []⟩,
      ⟨5, 4, 8901309, 8790672, [1, 7, 2, 1], [3, 1, 10, 2]⟩],
    #[⟨0, 2, 63, 13135901, [], []⟩,
      ⟨1, 3, 13135872, 267519, [1], []⟩,
      ⟨1, 5, 12521472, 14989736, [2], []⟩,
      ⟨1, 2, 61440, 13139997, [], [3, 4]⟩,
      ⟨2, 4, 5095733, 1437159, [2], [1, 10, 12, 13]⟩],
    #[⟨0, 3, 63, 267519, [], []⟩,
      ⟨1, 2, 61503, 13135901, [3], []⟩,
      ⟨2, 3, 320767, 13111325, [1], [1, 4]⟩,
      ⟨4, 5, 4130364, 2440599, [1, 11, 2, 1], [13]⟩,
      ⟨2, 4, 7172405, 906703, [2, 12], [1, 2, 3, 5, 2, 14]⟩],
    #[⟨0, 4, 63, 798985, [], []⟩,
      ⟨2, 1, 36898, 61440, [3], []⟩,
      ⟨2, 4, 36893, 835849, [3, 9, 14], [3, 5]⟩,
      ⟨3, 4, 3126510, 1569078, [2, 1, 2, 2], [3, 6]⟩,
      ⟨2, 5, 12035327, 250367, [4, 11, 1], [3, 11, 2, 6]⟩],
    #[⟨0, 5, 63, 14989736, [], []⟩,
      ⟨1, 2, 61503, 13135901, [3], []⟩,
      ⟨1, 5, 61440, 2935221, [], [9, 10, 11, 1]⟩,
      ⟨1, 4, 13135872, 1437159, [1], [1, 10, 12, 13]⟩,
      ⟨3, 5, 5659336, 5218775, [2, 2, 7, 9], [9, 14]⟩]]

theorem frameGen_mem_PvisLat (j : Fin 15) : frameGen j ∈ PvisLat := by
  unfold frameGen
  split_ifs
  · exact xiO_mem_PvisLat
  · exact PO_mem_PvisLat pAAut
  · exact PO_mem_PvisLat pBAut
  · exact gO_mem_PvisLat _

theorem mem_Hvis {u : GLV} : u ∈ Hvis ↔ ∃ g ∈ PvisLat, modTwoUnit g = u := by
  rw [Hvis, Subgroup.mem_unop, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, h⟩
    exact ⟨g, hg, MulOpposite.op_injective h⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem modTwoUnit_mem_Hvis {g : latticeO} (hg : g ∈ PvisLat) : modTwoUnit g ∈ Hvis :=
  mem_Hvis.2 ⟨g, hg, rfl⟩

theorem kGen_mem_Hvis (j : Fin 15) : kGen j ∈ Hvis := modTwoUnit_mem_Hvis (frameGen_mem_PvisLat j)

theorem Kvis_le_Hvis : Kvis ≤ Hvis :=
  (Subgroup.closure_le _).2 (Set.range_subset_iff.2 kGen_mem_Hvis)

theorem Nvis_le_Kvis : Nvis ≤ Kvis :=
  Subgroup.closure_mono (Set.image_subset_range _ _)

theorem Evis_le_Nvis : Evis ≤ Nvis :=
  Subgroup.closure_mono (Set.image_mono fun j (hj : 3 ≤ (j : ℕ)) => (by omega : 1 ≤ (j : ℕ)))

theorem Nvis_le_Hvis : Nvis ≤ Hvis := Nvis_le_Kvis.trans Kvis_le_Hvis

theorem Evis_le_Hvis : Evis ≤ Hvis := Evis_le_Nvis.trans Nvis_le_Hvis

theorem kGen_smul (j : Fin 15) (x : L2) : kGen j • x = modTwoEnd (frameGen j) x := rfl

end CFSG.Monster.VisCert
