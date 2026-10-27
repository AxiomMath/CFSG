module

public import CFSG.Quasithin.EmptyFaithful.S151S8C2B
public import CFSG.Quasithin.EmptyFaithful.S151S7A
public import CFSG.Quasithin.EmptyFaithful.S151S8C2A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Input15122ThreeDLocS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), SporadicSix ↥L → IsPGroup 2 ↥S →
    S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
    ∀ z ∈ centerOf (S ⊓ L), ¬ L ≤ Subgroup.centralizer ({z} : Set G) →
      ∃ P : Subgroup G, P ≤ L ∧ S ⊓ L ≤ P ∧ S ≤ Subgroup.normalizer (P : Set G) ∧
        ¬ P ≤ Subgroup.centralizer ({z} : Set G) ∧ CharTwo P ∧
        IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
        oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P

end CFSG.Quasithin

namespace CFSG.Quasithin.S151S8C2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normal_pCoreOf {L : Subgroup G} (hLn : L.Normal) : (pCoreOf 2 L).Normal := by
  have h1 : Subgroup.normalizer (L : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hLn
  have h2 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  rw [h1] at h2
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h2)

section Quotient

variable {Gb : Type} [Group Gb] [Finite Gb]

omit [Finite G] [Finite Gb] in
theorem isSylowTwoOf_map' {B L : Subgroup G} (hB : IsSylowTwoOf B L) (π : G →* Gb) :
    IsSylowTwoOf (B.map π) (L.map π) := by
  refine ⟨Subgroup.map_mono hB.1, hB.2.1.map π, ?_⟩
  have hρ := restrictTo_surjective π L
  have heq : (B.subgroupOf L).map (restrictTo π L) = (B.map π).subgroupOf (L.map π) := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨b, hb, hby⟩
      refine ⟨⟨b, hB.1 hb⟩, hb, Subtype.ext hby⟩
  have h1 : ((B.map π).subgroupOf (L.map π)).index ∣ (B.subgroupOf L).index := by
    rw [← heq]
    exact Subgroup.index_map_dvd _ hρ
  exact fun hd => hB.2.2 (hd.trans h1)

omit [Finite G] [Finite Gb] in
theorem le_centralizer_of_map {L : Subgroup G} (hperf : Group.IsPerfect ↥L)
    (hpc : CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L) (π : G →* Gb)
    (hρker : (restrictTo π L).ker = CFSG.pCore 2 ↥L) {z₀ : G} (hz₀ : z₀ ∈ L)
    (hcen : L.map π ≤ Subgroup.centralizer ({π z₀} : Set Gb)) :
    L ≤ Subgroup.centralizer ({z₀} : Set G) := by
  have hker : (restrictTo π L).ker ≤ Subgroup.center ↥L := hρker ▸ hpc
  let z : ↥L := ⟨z₀, hz₀⟩
  let κf : ↥L → ↥L := fun l => l * z * l⁻¹ * z⁻¹
  have hκmem : ∀ l, κf l ∈ (restrictTo π L).ker := by
    intro l
    refine MonoidHom.mem_ker.mpr (Subtype.ext ?_)
    have h1 : π (l : G) * π z₀ = π z₀ * π (l : G) :=
      (Subgroup.mem_centralizer_iff.mp (hcen ⟨l, l.2, rfl⟩) (π z₀) rfl).symm
    show π ((l : G) * z₀ * (l : G)⁻¹ * z₀⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group
  have hκcen : ∀ l, κf l ∈ Subgroup.center ↥L := fun l => hker (hκmem l)
  let κ : ↥L →* ↥L := MonoidHom.mk' κf (by
    intro a b
    have h1 : κf (a * b) = (a * κf b * a⁻¹) * κf a := by
      simp only [κf]; group
    have h2 : a * κf b * a⁻¹ = κf b := by
      rw [Subgroup.mem_center_iff.mp (hκcen b) a]; group
    rw [h1, h2]
    exact Subgroup.mem_center_iff.mp (hκcen a) (κf b))
  intro l hl
  have h1 := S151S7.hom_into_ker_trivial_of_perfect hperf (restrictTo π L) hker κ hκmem ⟨l, hl⟩
  have h2 : (l : G) * z₀ * (l : G)⁻¹ * z₀⁻¹ = 1 := congrArg Subtype.val h1
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  rw [Set.mem_singleton_iff] at hh
  subst hh
  calc h * l = (l * h * l⁻¹ * h⁻¹) * (h * l) := by rw [h2, one_mul]
    _ = l * h := by group

end Quotient

theorem locN_of_simple_normal (hS : Input15122ThreeDLocS) {L S : Subgroup G} (hLn : L.Normal)
    (hsix : SporadicSix (↥L ⧸ CFSG.pCore 2 ↥L)) (hperf : Group.IsPerfect ↥L)
    (hpc : CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L)
    (hS2 : IsPGroup 2 ↥S) (hSyl : IsSylowTwoOf (S ⊓ L) L)
    (hnc : ¬ L ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G)) :
    ∃ P : Subgroup G, P ≤ L ∧ S ⊓ L ≤ P ∧ S ≤ Subgroup.normalizer (P : Set G) ∧
      ¬ P ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) ∧ CharTwo P ∧
      IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
      oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P := by
  have hZn : (pCoreOf 2 L).Normal := normal_pCoreOf hLn
  let π : G →* G ⧸ pCoreOf 2 L := QuotientGroup.mk' (pCoreOf 2 L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = pCoreOf 2 L := QuotientGroup.ker_mk' _
  have hK : IsPGroup 2 ↥π.ker := by
    rw [hker]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hZL : pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hZS : pCoreOf 2 L ≤ S ⊓ L := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hSyl
  have : Finite (G ⧸ pCoreOf 2 L) := Finite.of_surjective π hπ
  have hmapinf : S.map π ⊓ L.map π ≤ (S ⊓ L).map π := by
    rintro _ ⟨⟨s, hs, rfl⟩, ⟨l, hl, hls⟩⟩
    have hkerm : l⁻¹ * s ∈ π.ker :=
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hls, inv_mul_cancel])
    have hkerL : l⁻¹ * s ∈ L := hZL (hker ▸ hkerm)
    refine ⟨s, ⟨hs, ?_⟩, rfl⟩
    have := L.mul_mem hl hkerL
    simpa using this
  have hSL : (S ⊓ L).map π = S.map π ⊓ L.map π := le_antisymm (Subgroup.map_inf_le _ _ _) hmapinf
  have hρker : (restrictTo π L).ker = CFSG.pCore 2 ↥L := by
    rw [← pCoreOf_subgroupOf L]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact hker.le (MonoidHom.mem_ker.mpr (congrArg Subtype.val h))
    · intro h
      exact Subtype.ext (MonoidHom.mem_ker.mp (hker.ge h))
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(L.map π) :=
    (QuotientGroup.quotientMulEquivOfEq hρker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (restrictTo π L) (restrictTo_surjective π L))
  have hsix' : SporadicSix ↥(L.map π) := zb_sporadicSix_congr e hsix
  have hLbn : (L.map π).Normal := hLn.map π hπ
  have hSN' : S.map π ≤ Subgroup.normalizer ((L.map π : Subgroup (G ⧸ pCoreOf 2 L)) : Set _) := by
    intro x _
    rw [Subgroup.normalizer_eq_top_iff.mpr hLbn]
    exact Subgroup.mem_top x
  have hSyl' : IsSylowTwoOf (S.map π ⊓ L.map π) (L.map π) := by
    rw [← hSL]
    exact isSylowTwoOf_map' hSyl π
  obtain ⟨z₀, hz₀, hLz₀⟩ : ∃ z ∈ centerOf (S ⊓ L), ¬ L ≤ Subgroup.centralizer ({z} : Set G) := by
    by_contra hcon
    apply hnc
    intro l hl
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    by_contra hne
    exact hcon ⟨z, hz, fun hLC => hne (Subgroup.mem_centralizer_iff.mp (hLC hl) z rfl)⟩
  have hz₀SL : z₀ ∈ S ⊓ L := hz₀.1
  have hzb : π z₀ ∈ centerOf (S.map π ⊓ L.map π) := by
    have h1 : π z₀ ∈ (S ⊓ L).map π := Subgroup.mem_map_of_mem π hz₀SL
    rw [hSL] at h1
    refine ⟨h1, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [← hSL] at hh
    obtain ⟨b, hb, rfl⟩ := hh
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hz₀.2 b hb]
  have hLzb : ¬ L.map π ≤ Subgroup.centralizer ({π z₀} : Set (G ⧸ pCoreOf 2 L)) :=
    fun hcen => hLz₀ (le_centralizer_of_map hperf hpc π hρker hz₀SL.2 hcen)
  obtain ⟨Pb, hPbL, hSPb, hSNb, hPbz, hchar, hmin, hnum, hoP⟩ :=
    hS (G ⧸ pCoreOf 2 L) (L.map π) (S.map π) hsix' (hS2.map π) hSN' hSyl' (π z₀) hzb hLzb
  rw [← hSL] at hSPb hoP
  set P : Subgroup G := Pb.comap π with hPdef
  have hPmap : P.map π = Pb := Subgroup.map_comap_eq_self_of_surjective hπ Pb
  have hZP : pCoreOf 2 L ≤ P := by
    intro x hx
    exact Subgroup.mem_comap.mpr (by rw [MonoidHom.mem_ker.mp (hker.ge hx)]; exact Pb.one_mem)
  have hPL : P ≤ L := by
    intro x hx
    obtain ⟨l, hl, hlx⟩ := hPbL (Subgroup.mem_comap.mp hx)
    have hkerm : l⁻¹ * x ∈ π.ker :=
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hlx, inv_mul_cancel])
    have := L.mul_mem hl (hZL (hker ▸ hkerm))
    simpa using this
  have hSLP : S ⊓ L ≤ P := fun x hx => Subgroup.mem_comap.mpr (hSPb (Subgroup.mem_map_of_mem π hx))
  have hSsupP : (P ⊔ S).map π = Pb ⊔ S.map π := by rw [Subgroup.map_sup, hPmap]
  refine ⟨P, hPL, hSLP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro s hs
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    have h1 : π s ∈ Subgroup.normalizer (Pb : Set (G ⧸ pCoreOf 2 L)) := hSNb ⟨s, hs, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp h1 (π p)).mp (Subgroup.mem_comap.mp hp)
    exact Subgroup.mem_comap.mpr (by simpa using this)
  ·
    intro hPC
    obtain ⟨pb, hpb, hpz⟩ : ∃ pb ∈ Pb, ¬ pb ∈ Subgroup.centralizer ({π z₀} : Set (G ⧸ pCoreOf 2 L)) := by
      by_contra hcon
      exact hPbz fun x hx => by
        by_contra hx'
        exact hcon ⟨x, hx, hx'⟩
    obtain ⟨p, rfl⟩ := hπ pb
    have hpP : p ∈ P := Subgroup.mem_comap.mpr hpb
    have h1 := Subgroup.mem_centralizer_iff.mp (hPC hpP) z₀ hz₀
    exact hpz (Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rw [← map_mul, ← map_mul, h1])
  ·
    refine charTwo_of_map π hK ?_
    rwa [hPmap]
  ·
    refine isMinParabolicOf_of_map π hK ?_
    rw [hSsupP]
    exact hmin
  ·
    refine numC126_of_map π hK ?_
    rw [hSsupP]
    exact hnum
  ·
    have hOP : oPrimeResidualOf 3 P ≤ P := (Subgroup.closure_le P).mpr fun x hx => hx.1
    refine le_antisymm (sup_le hOP hSLP) fun p hp => ?_
    have hO : (oPrimeResidualOf 3 P ⊔ (S ⊓ L)).map π = Pb := by
      calc (oPrimeResidualOf 3 P ⊔ (S ⊓ L)).map π
          = (oPrimeResidualOf 3 P).map π ⊔ (S ⊓ L).map π := Subgroup.map_sup _ _ _
        _ = oPrimeResidualOf 3 (P.map π) ⊔ (S ⊓ L).map π := by rw [map_oPrimeResidualOf π hK P]
        _ = oPrimeResidualOf 3 Pb ⊔ (S ⊓ L).map π := by rw [hPmap]
        _ = Pb := hoP
    have hpb : π p ∈ (oPrimeResidualOf 3 P ⊔ (S ⊓ L)).map π := hO ▸ Subgroup.mem_comap.mp hp
    have h1 : p ∈ ((oPrimeResidualOf 3 P ⊔ (S ⊓ L)).map π).comap π := Subgroup.mem_comap.mpr hpb
    rw [Subgroup.comap_map_eq] at h1
    have hk : π.ker ≤ oPrimeResidualOf 3 P ⊔ (S ⊓ L) := hker.le.trans (hZS.trans le_sup_right)
    exact (sup_le le_rfl hk) h1

end CFSG.Quasithin.S151S8C2
